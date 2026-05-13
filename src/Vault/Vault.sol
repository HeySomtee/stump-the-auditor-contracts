// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20} from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import {IERC20Metadata} from "@openzeppelin/contracts/token/ERC20/extensions/IERC20Metadata.sol";
import {SafeERC20} from "@openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol";
import {Ownable2Step, Ownable} from "@openzeppelin/contracts/access/Ownable2Step.sol";
import {ReentrancyGuard} from "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import {Pausable} from "@openzeppelin/contracts/utils/Pausable.sol";
import {Math} from "@openzeppelin/contracts/utils/math/Math.sol";

import {IVault} from "../interfaces/IVault.sol";

/// @title Multi-asset vault with fee accrual and withdrawal timelocks
///
/// @notice Accounting model — read this before attempting to modify anything:
///
///   Unit conventions:
///     - WAD (1e18): internal denominator for all multi-asset accounting. Token balances are normalized to WAD on entry,
///       denormalized on exit.
///     - BPS (10_000): fee rate configuration (performance + management).
///     - PPS_SCALE = WAD * VSO: internal precision unit for the per-share price calculation.
///
///   Active vs. pending capital:
///     - `totalManagedWad` tracks all capital ever deposited + yield reported, minus what has been released.
///     - `totalPendingWithdrawWad` is the frozen WAD claim on capital held for timelocked withdrawals.
///     - `_activeManagedWad() = totalManagedWad - totalPendingWithdrawWad` is the base used for per-share price (PPS).
///       This carve-out prevents `requestWithdraw` from ever lifting PPS and masquerading as yield.
///     - `shareAssetOf[user]` binds user shares to the asset first deposited for that share account. Users may not
///       deposit one whitelisted asset and redeem a different whitelisted asset from the shared pool.
///
///   Fee schedule — `_accrueFees()` runs on every state-mutating entry point:
///     1. Time passes -> management fee minted to fee recipient (dilution-based, uses `_effectiveTotalShares`).
///     2. Current PPS recomputed (only `reportYield` actually lifts it; deposit/withdraw are construction-preserving).
///     3. If PPS > high-water-mark PPS, performance fee minted on the lift × active shares.
///     4. Pending withdrawals are fixed claims and do not participate in future yield or performance fees.
///
///   Pause matrix: deposit + requestWithdraw blocked; claimWithdraw + cancelWithdraw always available; reportYield is
///   owner-only and also blocked while paused.
contract Vault is IVault, Ownable2Step, ReentrancyGuard, Pausable {
    using SafeERC20 for IERC20;

    uint256 public constant WAD = 1e18;
    uint256 public constant BPS = 10_000;
    uint256 public constant MAX_MANAGEMENT_FEE_BPS = 500;
    uint256 public constant MAX_PERFORMANCE_FEE_BPS = 3_000;
    uint256 public constant MAX_TIMELOCK_BLOCKS = 7 days / 12;
    uint256 public constant MIN_INITIAL_DEPOSIT = 1e18;
    uint256 public constant VIRTUAL_SHARES_OFFSET = 1e3;
    uint256 public constant SECONDS_PER_YEAR = 365 days;

    uint256 private constant PPS_SCALE = WAD * VIRTUAL_SHARES_OFFSET;

    struct AssetConfig {
        bool enabled;
        uint8 decimals;
        uint256 totalHeld;
    }

    mapping(address => AssetConfig) public assetConfig;
    address[] public assetList;
    mapping(address => uint256) private _userShares;
    mapping(address => uint256) private _unboundFeeShares;
    mapping(address => address) public shareAssetOf;
    mapping(address => uint256) public sharesByAsset;
    uint256 public totalShares;
    uint256 public totalManagedWad;
    mapping(address => WithdrawRequest) public pendingWithdraw;
    mapping(address => uint256) public reservedForWithdraw;

    uint256 public performanceFeeBps;
    uint256 public managementFeeBps;
    uint256 public lastFeeAccrual;
    uint256 public highWaterMarkPPS;
    address public feeRecipient;

    uint256 public timelockBlocks;

    uint256 internal totalPendingWithdrawWad;
    mapping(address => uint256) private _assetIndexPlusOne;
    address[] private _pendingUsers;
    mapping(address => uint256) private _pendingUserIndexPlusOne;

    /// @notice Sets the initial fee recipient and fee parameters.
    /// @param feeRecipient_ The address that receives fee shares.
    /// @param performanceFeeBps_ The initial performance fee, in basis points.
    /// @param managementFeeBps_ The initial annualized management fee, in basis points.
    /// @param timelockBlocks_ The initial withdrawal timelock, in blocks.
    constructor(address feeRecipient_, uint256 performanceFeeBps_, uint256 managementFeeBps_, uint256 timelockBlocks_)
        Ownable(msg.sender)
    {
        if (feeRecipient_ == address(0)) revert ZeroAddress();
        if (performanceFeeBps_ > MAX_PERFORMANCE_FEE_BPS) {
            revert FeeTooHigh(performanceFeeBps_, MAX_PERFORMANCE_FEE_BPS);
        }
        if (managementFeeBps_ > MAX_MANAGEMENT_FEE_BPS) {
            revert FeeTooHigh(managementFeeBps_, MAX_MANAGEMENT_FEE_BPS);
        }
        if (timelockBlocks_ > MAX_TIMELOCK_BLOCKS) revert TimelockTooLong(timelockBlocks_, MAX_TIMELOCK_BLOCKS);

        feeRecipient = feeRecipient_;
        performanceFeeBps = performanceFeeBps_;
        managementFeeBps = managementFeeBps_;
        timelockBlocks = timelockBlocks_;
        lastFeeAccrual = block.timestamp;
    }

    /// @notice Deposits a whitelisted asset and mints vault shares to the receiver.
    /// @dev Share minting rounds down in favor of the vault. The first deposit must clear the minimum seed threshold.
    /// @param asset The whitelisted asset to deposit.
    /// @param amount The token-native amount to deposit.
    /// @param receiver The account that receives the newly minted shares.
    /// @return sharesMinted The number of shares minted to `receiver`.
    function deposit(address asset, uint256 amount, address receiver)
        external
        nonReentrant
        whenNotPaused
        returns (uint256 sharesMinted)
    {
        if (amount == 0) revert ZeroAmount();
        if (receiver == address(0)) revert ZeroAddress();
        if (receiver != msg.sender && shareAssetOf[receiver] == address(0)) {
            revert UnauthorizedReceiverBinding(receiver);
        }

        AssetConfig storage config = _requireWhitelistedAsset(asset);
        _accrueFees(asset);
        _setOrCheckShareAsset(receiver, asset);

        bool initializingSupply = totalShares == 0;

        uint256 amountWad = _toWad(amount, config.decimals);
        if (amountWad == 0) revert ZeroAmount();
        if (initializingSupply && amountWad < MIN_INITIAL_DEPOSIT) {
            revert InitialDepositTooSmall(amountWad, MIN_INITIAL_DEPOSIT);
        }

        uint256 activeManagedWad = _activeManagedWad();
        sharesMinted = _computeShares(amountWad, totalShares, activeManagedWad);
        if (sharesMinted == 0) revert ZeroAmount();

        IERC20 assetToken = IERC20(asset);
        uint256 balanceBefore = assetToken.balanceOf(address(this));
        assetToken.safeTransferFrom(msg.sender, address(this), amount);
        uint256 balanceAfter = assetToken.balanceOf(address(this));
        uint256 received = balanceAfter - balanceBefore;
        if (received != amount) revert UnsupportedToken(asset);

        totalManagedWad += amountWad;
        totalShares += sharesMinted;
        _userShares[receiver] += sharesMinted;
        sharesByAsset[asset] += sharesMinted;
        config.totalHeld = balanceAfter;

        if (initializingSupply && highWaterMarkPPS == 0) {
            highWaterMarkPPS = WAD;
        }

        emit Deposited(msg.sender, asset, received, sharesMinted, receiver);
    }

    /// @notice Burns shares into a timelocked withdrawal claim denominated in a chosen asset.
    /// @dev The request freezes the caller's share count and initial WAD claim. While active capital still exists,
    ///      future `reportYield` calls accrue only to active shares; the pending claim stays fixed in the requested
    ///      settlement asset so yield reporting never needs to iterate or re-reserve every pending withdrawal.
    /// @param shares The number of shares to burn into the request.
    /// @param asset The whitelisted asset to be received on claim.
    /// @return unlockBlock The first block at which the withdrawal may be claimed.
    function requestWithdraw(uint256 shares, address asset)
        external
        nonReentrant
        whenNotPaused
        returns (uint64 unlockBlock)
    {
        if (shares == 0) revert ZeroAmount();
        AssetConfig storage config = _requireWhitelistedAsset(asset);
        _accrueFees(asset);
        _materializeUnboundFeeShares(msg.sender, asset);
        _requireShareAsset(msg.sender, asset);

        WithdrawRequest storage existingRequest = pendingWithdraw[msg.sender];
        if (existingRequest.shares != 0) revert PendingWithdrawExists(msg.sender);

        uint256 availableShares = _userShares[msg.sender];
        if (shares > availableShares) revert InsufficientShares(shares, availableShares);

        uint256 wadOwed = _computeAssets(shares, totalShares, _activeManagedWad());
        uint256 reservedAmount = _fromWad(wadOwed, config.decimals);
        if (wadOwed != 0 && reservedAmount == 0) revert ZeroAmount();
        uint256 effectiveWadOwed = _toWad(reservedAmount, config.decimals);
        uint256 availableLiquidity = _syncTrackedHoldings(asset, config);
        uint256 alreadyReserved = reservedForWithdraw[asset];
        uint256 unreservedLiquidity = availableLiquidity > alreadyReserved ? availableLiquidity - alreadyReserved : 0;
        if (reservedAmount > unreservedLiquidity) {
            revert InsufficientAssetLiquidity(asset, reservedAmount, unreservedLiquidity);
        }

        _userShares[msg.sender] = availableShares - shares;
        totalShares -= shares;
        sharesByAsset[asset] -= shares;
        totalPendingWithdrawWad += effectiveWadOwed;
        reservedForWithdraw[asset] = alreadyReserved + reservedAmount;

        unlockBlock = uint64(block.number + timelockBlocks);
        pendingWithdraw[msg.sender] = WithdrawRequest({
            shares: shares,
            wadOwed: effectiveWadOwed,
            reservedAmount: reservedAmount,
            asset: asset,
            unlockBlock: unlockBlock,
            claimed: false
        });
        _addPendingUser(msg.sender);

        emit WithdrawRequested(msg.sender, shares, effectiveWadOwed, asset, unlockBlock);
    }

    /// @notice Claims an unlocked withdrawal request in the asset chosen at request time.
    /// @return amountOut The token-native amount transferred to the caller.
    function claimWithdraw() external nonReentrant returns (uint256 amountOut) {
        WithdrawRequest memory request = pendingWithdraw[msg.sender];
        if (request.shares == 0) revert NoPendingWithdraw(msg.sender);
        if (block.number < request.unlockBlock) revert TimelockActive(request.unlockBlock, uint64(block.number));
        _accrueFees(address(0));

        AssetConfig storage config = assetConfig[request.asset];
        uint256 availableLiquidity = _syncTrackedHoldings(request.asset, config);
        amountOut = request.reservedAmount;
        uint256 settledWad = request.wadOwed;
        if (block.number > request.unlockBlock) {
            uint256 repricedWad = _computeAssets(request.shares, totalShares + request.shares, totalManagedWad);
            amountOut = _fromWad(repricedWad, config.decimals);
            settledWad = _toWad(amountOut, config.decimals);
        }
        if (amountOut > availableLiquidity) {
            revert InsufficientAssetLiquidity(request.asset, amountOut, availableLiquidity);
        }

        totalManagedWad -= settledWad;
        totalPendingWithdrawWad -= request.wadOwed;
        reservedForWithdraw[request.asset] -= request.reservedAmount;
        config.totalHeld = availableLiquidity - amountOut;

        _removePendingUser(msg.sender);
        delete pendingWithdraw[msg.sender];
        if (_userShares[msg.sender] == 0) delete shareAssetOf[msg.sender];

        IERC20(request.asset).safeTransfer(msg.sender, amountOut);

        emit WithdrawClaimed(msg.sender, request.asset, amountOut);
    }

    /// @notice Cancels a pending withdrawal and restores the original burned shares.
    /// @dev Cancels are only allowed before the request becomes claimable to avoid post-unlock optionality.
    ///      The restored share count is repriced from the fixed pending WAD claim at the current active PPS.
    function cancelWithdraw() external nonReentrant {
        WithdrawRequest memory request = pendingWithdraw[msg.sender];
        if (request.shares == 0) revert NoPendingWithdraw(msg.sender);
        if (block.number >= request.unlockBlock) revert TimelockActive(request.unlockBlock, uint64(block.number));

        _accrueFees(address(0));

        uint256 activeManagedWad = _activeManagedWad();
        uint256 newShares = totalShares == 0 && activeManagedWad == 0
            ? request.shares
            : _computeShares(request.wadOwed, totalShares, activeManagedWad);
        if (newShares == 0 && request.wadOwed != 0) revert ZeroAmount();

        totalPendingWithdrawWad -= request.wadOwed;
        reservedForWithdraw[request.asset] -= request.reservedAmount;
        _userShares[msg.sender] += newShares;
        totalShares += newShares;
        sharesByAsset[request.asset] += newShares;

        _removePendingUser(msg.sender);
        delete pendingWithdraw[msg.sender];

        emit WithdrawCancelled(msg.sender, newShares);
    }

    /// @notice Returns the total managed assets tracked by the vault, in WAD.
    /// @return assetsWad The vault's total managed assets, including pending withdrawal liabilities.
    function totalAssets() external view returns (uint256 assetsWad) {
        return totalManagedWad;
    }

    /// @notice Returns the user's raw shares plus any unbound fee shares owed to that address.
    /// @param user The account to inspect.
    /// @return shares The account's observable share balance.
    function userShares(address user) public view returns (uint256 shares) {
        return _userShares[user] + _unboundFeeShares[user];
    }

    /// @notice Returns unbound fee shares currently owed to the active fee recipient.
    /// @return shares The active fee recipient's asset-agnostic fee shares.
    function feeRecipientShares() external view returns (uint256 shares) {
        return _unboundFeeShares[feeRecipient];
    }

    /// @notice Converts a WAD-denominated asset amount into shares at the post-fee ratio.
    /// @param amountWad The WAD-denominated asset amount.
    /// @return shares The number of shares that amount would mint.
    function convertToShares(uint256 amountWad) external view returns (uint256 shares) {
        if (amountWad == 0) return 0;

        (uint256 activeManagedWad, uint256 effectiveTotalShares,,,) = _pendingFees();
        return _computeShares(amountWad, effectiveTotalShares, activeManagedWad);
    }

    /// @notice Converts shares into WAD-denominated assets at the post-fee ratio.
    /// @param shares The number of shares to convert.
    /// @return amountWad The WAD-denominated asset value for those shares.
    function convertToAssets(uint256 shares) external view returns (uint256 amountWad) {
        if (shares == 0) return 0;

        (uint256 activeManagedWad, uint256 effectiveTotalShares,,,) = _pendingFees();
        return _computeAssets(shares, effectiveTotalShares, activeManagedWad);
    }

    /// @notice Quotes a deposit using the post-fee share ratio.
    /// @param asset The whitelisted asset to quote.
    /// @param amount The token-native deposit amount.
    /// @return shares The number of shares that deposit would mint.
    function previewDeposit(address asset, uint256 amount) external view returns (uint256 shares) {
        if (amount == 0) return 0;

        AssetConfig storage config = _requireWhitelistedAsset(asset);
        uint256 amountWad = _toWad(amount, config.decimals);
        (uint256 activeManagedWad, uint256 effectiveTotalShares,,,) = _pendingFees();
        return _computeShares(amountWad, effectiveTotalShares, activeManagedWad);
    }

    /// @notice Quotes the WAD-denominated assets owed for a withdrawal request using the post-fee ratio.
    /// @param shares The number of shares to burn.
    /// @return amountWad The WAD-denominated asset value the request would lock in.
    function previewWithdraw(uint256 shares) external view returns (uint256 amountWad) {
        if (shares == 0) return 0;

        (uint256 activeManagedWad, uint256 effectiveTotalShares,,,) = _pendingFees();
        return _computeAssets(shares, effectiveTotalShares, activeManagedWad);
    }

    /// @notice Returns the currently whitelisted asset list.
    /// @return assets The whitelisted assets.
    function getAssetList() external view returns (address[] memory assets) {
        return assetList;
    }

    /// @notice Returns the caller-facing pending withdrawal record for a user.
    /// @param user The user to inspect.
    /// @return request The stored pending withdrawal request.
    function getPendingWithdraw(address user) external view returns (WithdrawRequest memory request) {
        return pendingWithdraw[user];
    }

    /// @notice Whitelists an asset for future deposits and withdrawals.
    /// @param asset The ERC20 asset to whitelist.
    function addAsset(address asset) external onlyOwner {
        _accrueFees(address(0));

        if (asset == address(0)) revert ZeroAddress();
        if (assetConfig[asset].enabled) revert AssetAlreadyWhitelisted(asset);

        AssetConfig storage config = assetConfig[asset];
        uint8 decimals = IERC20Metadata(asset).decimals();
        if (decimals > 36) revert UnsupportedToken(asset);

        config.enabled = true;
        config.decimals = decimals;

        assetList.push(asset);
        _assetIndexPlusOne[asset] = assetList.length;

        emit AssetAdded(asset, config.decimals);
    }

    /// @notice Removes an asset from the whitelist after all tracked liquidity has been drained.
    /// @param asset The whitelisted asset to remove.
    function removeAsset(address asset) external onlyOwner {
        _accrueFees(address(0));

        AssetConfig storage config = _requireWhitelistedAsset(asset);
        uint256 outstandingShares = sharesByAsset[asset];
        if (outstandingShares != 0 || reservedForWithdraw[asset] != 0) {
            revert AssetHasOutstandingShares(asset, outstandingShares);
        }
        uint256 held = _syncTrackedHoldings(asset, config);
        if (held != 0) revert AssetStillHeld(asset, held);

        config.enabled = false;
        _removeAssetFromList(asset);

        emit AssetRemoved(asset);
    }

    /// @notice Sets the performance fee that applies to PPS gains above the high water mark.
    /// @param bps The new performance fee, in basis points.
    function setPerformanceFee(uint256 bps) external onlyOwner {
        _accrueFees(address(0));

        if (bps > MAX_PERFORMANCE_FEE_BPS) revert FeeTooHigh(bps, MAX_PERFORMANCE_FEE_BPS);
        performanceFeeBps = bps;

        emit FeeParamsUpdated(performanceFeeBps, managementFeeBps);
    }

    /// @notice Sets the annualized management fee.
    /// @param bps The new management fee, in basis points.
    function setManagementFee(uint256 bps) external onlyOwner {
        _accrueFees(address(0));

        if (bps > MAX_MANAGEMENT_FEE_BPS) revert FeeTooHigh(bps, MAX_MANAGEMENT_FEE_BPS);
        managementFeeBps = bps;

        emit FeeParamsUpdated(performanceFeeBps, managementFeeBps);
    }

    /// @notice Sets the withdrawal timelock.
    /// @param blocks_ The new timelock, in blocks.
    function setTimelockBlocks(uint256 blocks_) external onlyOwner {
        _accrueFees(address(0));

        if (blocks_ > MAX_TIMELOCK_BLOCKS) revert TimelockTooLong(blocks_, MAX_TIMELOCK_BLOCKS);
        timelockBlocks = blocks_;

        emit TimelockUpdated(blocks_);
    }

    /// @notice Sets the address that receives newly minted fee shares.
    /// @dev Existing fee shares remain at the previous recipient address. Rotations only affect future accrual.
    /// @param recipient The new fee recipient.
    function setFeeRecipient(address recipient) external onlyOwner {
        _accrueFees(address(0));

        if (recipient == address(0)) revert ZeroAddress();
        feeRecipient = recipient;

        emit FeeRecipientUpdated(recipient);
    }

    /// @notice Pulls whitelisted strategy profits into the vault and adds them to managed assets.
    /// @dev Pull-based accounting keeps managed assets aligned with live balances. Realized profit belongs to active
    ///      shares only; pending withdrawal liabilities are fixed at request time and do not receive future yield.
    /// @param asset The whitelisted asset being realized as profit.
    /// @param amount The token-native profit amount to pull from the owner.
    function reportYield(address asset, uint256 amount) external onlyOwner {
        _accrueFees(asset);

        if (amount == 0) revert ZeroAmount();
        uint256 activeManagedWad = _activeManagedWad();
        if (totalShares == 0 || activeManagedWad == 0) revert NoActiveShares();

        AssetConfig storage config = _requireWhitelistedAsset(asset);
        IERC20 assetToken = IERC20(asset);
        uint256 balanceBefore = assetToken.balanceOf(address(this));
        assetToken.safeTransferFrom(msg.sender, address(this), amount);
        uint256 balanceAfter = assetToken.balanceOf(address(this));
        uint256 received = balanceAfter - balanceBefore;
        if (received != amount) revert UnsupportedToken(asset);

        uint256 amountWad = _toWad(received, config.decimals);
        if (amountWad == 0) revert ZeroAmount();

        totalManagedWad += amountWad;
        config.totalHeld = balanceAfter;

        emit YieldReported(asset, received, totalManagedWad);
    }

    /// @notice Accrues any pending management and performance fees.
    function accrueFees() external {
        _accrueFees(address(0));
    }

    /// @notice Pauses new exposure-creating entry points.
    function pause() external onlyOwner {
        _accrueFees(address(0));
        _pause();
    }

    /// @notice Unpauses new exposure-creating entry points.
    function unpause() external onlyOwner {
        _accrueFees(address(0));
        _unpause();
    }

    /// @notice Accrues management fees first, then performance fees against active-PPS gains over the high water mark.
    /// @dev PPS is measured against active managed assets only, excluding timelocked withdrawal liabilities, so deposits,
    ///      cancellations, and claim finalization preserve PPS up to round-down dust instead of appearing as new profit.
    ///      Pending withdrawals are fixed claims, leaving this path to price only active managed assets.
    function _accrueFees(address) internal {
        uint256 currentTime = block.timestamp;
        if (totalShares == 0) {
            lastFeeAccrual = currentTime;
            if (totalPendingWithdrawWad == 0 && totalManagedWad == 0) {
                highWaterMarkPPS = 0;
            }
            return;
        }

        (,, uint256 mgmtFeeShares, uint256 perfFeeShares, uint256 newHighWaterMarkPPS) = _pendingFees();
        uint256 feeShares = mgmtFeeShares + perfFeeShares;

        if (feeShares != 0) {
            // Fee shares are asset-agnostic until the recipient chooses a settlement asset on requestWithdraw().
            _unboundFeeShares[feeRecipient] += feeShares;
            totalShares += feeShares;
        }
        if (newHighWaterMarkPPS > highWaterMarkPPS) {
            highWaterMarkPPS = newHighWaterMarkPPS;
        }

        lastFeeAccrual = currentTime;

        if (mgmtFeeShares != 0 || perfFeeShares != 0) {
            emit FeesAccrued(mgmtFeeShares, perfFeeShares, highWaterMarkPPS);
        }
    }

    /// @notice Computes the fees that would accrue if `_accrueFees()` ran at the current timestamp.
    /// @return activeManagedWad The managed assets that still back active shares.
    /// @return effectiveTotalShares The share supply after simulated fee minting.
    /// @return mgmtFeeShares The management fee shares that would mint.
    /// @return perfFeeShares The performance fee shares that would mint.
    /// @return newHighWaterMarkPPS The high water mark that would be stored.
    function _pendingFees()
        internal
        view
        returns (
            uint256 activeManagedWad,
            uint256 effectiveTotalShares,
            uint256 mgmtFeeShares,
            uint256 perfFeeShares,
            uint256 newHighWaterMarkPPS
        )
    {
        activeManagedWad = _activeManagedWad();
        effectiveTotalShares = totalShares;
        newHighWaterMarkPPS = highWaterMarkPPS;

        if (effectiveTotalShares == 0) return (activeManagedWad, effectiveTotalShares, 0, 0, newHighWaterMarkPPS);

        uint256 dt = block.timestamp - lastFeeAccrual;
        uint256 profitShareSupply = effectiveTotalShares;
        if (dt != 0 && managementFeeBps != 0) {
            mgmtFeeShares =
                Math.mulDiv(effectiveTotalShares, managementFeeBps * dt, BPS * SECONDS_PER_YEAR, Math.Rounding.Floor);
            effectiveTotalShares += mgmtFeeShares;
        }

        (, uint256 profitWad) = _profitAboveHighWaterMarkWad(activeManagedWad, profitShareSupply, newHighWaterMarkPPS);
        if (profitWad != 0) {
            uint256 perfFeeWad = Math.mulDiv(profitWad, performanceFeeBps, BPS, Math.Rounding.Floor);
            perfFeeShares = _computeFeeShares(perfFeeWad, effectiveTotalShares, activeManagedWad);
            effectiveTotalShares += perfFeeShares;
            newHighWaterMarkPPS = _currentPPS(activeManagedWad, effectiveTotalShares);
        }
    }

    /// @notice Returns the gross WAD profit above a reference high-water-mark PPS.
    /// @param managedWad The managed assets backing the active pool.
    /// @param shareSupply The active share supply.
    /// @param referencePPS The PPS threshold that profit must exceed.
    /// @return currentPPS The current active PPS before any new performance-fee shares mint.
    /// @return profitWad The WAD profit that sits above `referencePPS`.
    function _profitAboveHighWaterMarkWad(uint256 managedWad, uint256 shareSupply, uint256 referencePPS)
        internal
        pure
        returns (uint256 currentPPS, uint256 profitWad)
    {
        currentPPS = _currentPPS(managedWad, shareSupply);
        if (currentPPS <= referencePPS) return (currentPPS, 0);

        profitWad = Math.mulDiv(currentPPS - referencePPS, shareSupply, PPS_SCALE, Math.Rounding.Floor);
    }

    /// @notice Converts a token-native amount into WAD.
    /// @param amount The token-native amount.
    /// @param decimals The token decimals.
    /// @return wadAmount The WAD-denominated amount.
    function _toWad(uint256 amount, uint8 decimals) internal pure returns (uint256 wadAmount) {
        if (decimals == 18) return amount;
        if (decimals < 18) {
            return Math.mulDiv(amount, 10 ** (18 - decimals), 1, Math.Rounding.Floor);
        }
        return Math.mulDiv(amount, 1, 10 ** (decimals - 18), Math.Rounding.Floor);
    }

    /// @notice Converts a WAD amount into token-native units.
    /// @param wadAmount The WAD-denominated amount.
    /// @param decimals The token decimals.
    /// @return amount The token-native amount.
    function _fromWad(uint256 wadAmount, uint8 decimals) internal pure returns (uint256 amount) {
        return _fromWad(wadAmount, decimals, Math.Rounding.Floor);
    }

    function _fromWad(uint256 wadAmount, uint8 decimals, Math.Rounding rounding)
        internal
        pure
        returns (uint256 amount)
    {
        if (decimals == 18) return wadAmount;
        if (decimals < 18) {
            return Math.mulDiv(wadAmount, 1, 10 ** (18 - decimals), rounding);
        }
        return Math.mulDiv(wadAmount, 10 ** (decimals - 18), 1, rounding);
    }

    /// @notice Computes shares for a WAD deposit amount under the virtual-offset share model.
    /// @param amountWad The WAD amount to convert.
    /// @param shareSupply The share supply to use for the conversion.
    /// @param managedWad The managed assets backing those shares.
    /// @return shares The computed share amount, rounded down.
    function _computeShares(uint256 amountWad, uint256 shareSupply, uint256 managedWad)
        internal
        pure
        returns (uint256 shares)
    {
        return Math.mulDiv(amountWad, shareSupply + VIRTUAL_SHARES_OFFSET, managedWad + 1, Math.Rounding.Floor);
    }

    function _computeFeeShares(uint256 feeWad, uint256 shareSupply, uint256 managedWad)
        internal
        pure
        returns (uint256 shares)
    {
        return Math.mulDiv(feeWad, shareSupply + VIRTUAL_SHARES_OFFSET, managedWad + 1 - feeWad, Math.Rounding.Floor);
    }

    /// @notice Computes WAD-denominated assets for a share amount under the virtual-offset share model.
    /// @param shares The share amount to convert.
    /// @param shareSupply The share supply to use for the conversion.
    /// @param managedWad The managed assets backing those shares.
    /// @return amountWad The computed WAD amount, rounded down.
    function _computeAssets(uint256 shares, uint256 shareSupply, uint256 managedWad)
        internal
        pure
        returns (uint256 amountWad)
    {
        return Math.mulDiv(shares, managedWad + 1, shareSupply + VIRTUAL_SHARES_OFFSET, Math.Rounding.Floor);
    }

    /// @notice Returns the WAD-scaled assets-per-normalized-share value used by the high water mark.
    /// @param managedWad The managed assets backing active shares.
    /// @param shareSupply The active share supply.
    /// @return pps The current PPS value scaled by `WAD`.
    function _currentPPS(uint256 managedWad, uint256 shareSupply) internal pure returns (uint256 pps) {
        return Math.mulDiv(managedWad + 1, PPS_SCALE, shareSupply + VIRTUAL_SHARES_OFFSET, Math.Rounding.Floor);
    }

    /// @notice Returns the managed assets that still back active shares after excluding pending withdrawals.
    /// @return activeManagedWad The managed WAD available to active shares.
    function _activeManagedWad() internal view returns (uint256 activeManagedWad) {
        return totalManagedWad - totalPendingWithdrawWad;
    }

    /// @notice Returns and stores the live on-chain token balance for an asset.
    /// @param asset The asset to sync.
    /// @param config The storage slot for the asset configuration.
    /// @return held The liquidity available to the vault for that asset.
    function _syncTrackedHoldings(address asset, AssetConfig storage config) internal returns (uint256 held) {
        held = IERC20(asset).balanceOf(address(this));
        config.totalHeld = held;
    }

    /// @notice Returns a whitelisted asset configuration or reverts.
    /// @param asset The asset to validate.
    /// @return config The storage slot for that asset.
    function _requireWhitelistedAsset(address asset) internal view returns (AssetConfig storage config) {
        config = assetConfig[asset];
        if (!config.enabled) revert AssetNotWhitelisted(asset);
    }

    function _setOrCheckShareAsset(address user, address asset) internal {
        address existingAsset = shareAssetOf[user];
        if (existingAsset == address(0)) {
            shareAssetOf[user] = asset;
            return;
        }
        if (existingAsset != asset) revert ShareAssetMismatch(user, existingAsset, asset);
    }

    function _requireShareAsset(address user, address asset) internal view {
        address expectedAsset = shareAssetOf[user];
        if (expectedAsset == address(0)) return;
        if (expectedAsset != asset) revert ShareAssetMismatch(user, expectedAsset, asset);
    }

    function _materializeUnboundFeeShares(address user, address asset) internal {
        uint256 shares = _unboundFeeShares[user];
        if (shares == 0) return;

        _setOrCheckShareAsset(user, asset);
        delete _unboundFeeShares[user];
        _userShares[user] += shares;
        sharesByAsset[asset] += shares;
    }

    /// @notice Removes an asset from `assetList` in O(1) time via swap-and-pop.
    /// @param asset The asset to remove.
    function _removeAssetFromList(address asset) internal {
        uint256 indexPlusOne = _assetIndexPlusOne[asset];
        uint256 index = indexPlusOne - 1;
        uint256 lastIndex = assetList.length - 1;

        if (index != lastIndex) {
            address movedAsset = assetList[lastIndex];
            assetList[index] = movedAsset;
            _assetIndexPlusOne[movedAsset] = index + 1;
        }

        assetList.pop();
        delete _assetIndexPlusOne[asset];
    }

    /// @notice Adds a user to the enumerable pending-withdraw set.
    /// @param user The account with a live pending withdrawal.
    function _addPendingUser(address user) internal {
        if (_pendingUserIndexPlusOne[user] != 0) return;

        _pendingUsers.push(user);
        _pendingUserIndexPlusOne[user] = _pendingUsers.length;
    }

    /// @notice Removes a user from the enumerable pending-withdraw set.
    /// @param user The account whose pending withdrawal is being cleared.
    function _removePendingUser(address user) internal {
        uint256 indexPlusOne = _pendingUserIndexPlusOne[user];
        if (indexPlusOne == 0) return;

        uint256 index = indexPlusOne - 1;
        uint256 lastIndex = _pendingUsers.length - 1;

        if (index != lastIndex) {
            address movedUser = _pendingUsers[lastIndex];
            _pendingUsers[index] = movedUser;
            _pendingUserIndexPlusOne[movedUser] = index + 1;
        }

        _pendingUsers.pop();
        delete _pendingUserIndexPlusOne[user];
    }
}
