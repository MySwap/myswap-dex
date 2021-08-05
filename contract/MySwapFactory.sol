pragma solidity >=0.5.0;

interface IMySwapFactory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);
    function feeToSetter() external view returns (address);
    function migrator() external view returns (address);

    function getPair(address tokenA, address tokenB) external view returns (address pair);
    function allPairs(uint) external view returns (address pair);
    function allPairsLength() external view returns (uint);

    function createPair(address tokenA, address tokenB) external returns (address pair);

    function setFeeTo(address) external;
    function setFeeToSetter(address) external;
    function setMigrator(address) external;
    function pairCodeHash() external pure returns (bytes32);
}

pragma solidity ^0.6.0;


interface IERC20 {
    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}


pragma solidity ^0.6.0;

/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}

pragma solidity >=0.5.0;

interface IERC20MySwap {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);
    function symbol() external pure returns (string memory);
    function decimals() external pure returns (uint8);
    function totalSupply() external view returns (uint);
    function balanceOf(address owner) external view returns (uint);
    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);
    function transfer(address to, uint value) external returns (bool);
    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);
    function PERMIT_TYPEHASH() external pure returns (bytes32);
    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;
}

pragma solidity =0.6.12;


contract MySwapERC20 is IERC20MySwap {
    using SafeMath for uint256;

    string public constant override name = "MySwap LP Token";
    string public override symbol = "MLP";
    uint8 public constant override decimals = 18;
    uint256 public override totalSupply;
    mapping(address => uint256) public override balanceOf;
    mapping(address => mapping(address => uint256)) public override allowance;

    bytes32 public override DOMAIN_SEPARATOR;
    /// @notice The EIP-712 typehash for the contract's domain
    // keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");
    bytes32
        public constant
        override PERMIT_TYPEHASH = 0x6e71edae12b1b97f4d1f60370fef10105fa2faae0126114a169c64845d6126c9;

    mapping(address => uint256) public override nonces;

    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );
    event Transfer(address indexed from, address indexed to, uint256 value);

    constructor() public {
        uint256 chainId;
        // solium-disable-next-line
        assembly {
            chainId := chainid()
        }
        //EIP712Domain
        DOMAIN_SEPARATOR = keccak256(
            abi.encode(
                keccak256(
                    "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"
                ),
                keccak256(bytes(name)),
                keccak256(bytes("1")),
                chainId,
                address(this)
            )
        );
    }

    function _mint(address to, uint256 value) internal {
        totalSupply = totalSupply.add(value);
        balanceOf[to] = balanceOf[to].add(value);
        emit Transfer(address(0), to, value);
    }

    function _burn(address from, uint256 value) internal {
        balanceOf[from] = balanceOf[from].sub(value);
        totalSupply = totalSupply.sub(value);
        emit Transfer(from, address(0), value);
    }

    function _approve(
        address owner,
        address spender,
        uint256 value
    ) private {
        allowance[owner][spender] = value;
        emit Approval(owner, spender, value);
    }

    function _transfer(
        address from,
        address to,
        uint256 value
    ) private {
        balanceOf[from] = balanceOf[from].sub(value);
        balanceOf[to] = balanceOf[to].add(value);
        emit Transfer(from, to, value);
    }

    function approve(address spender, uint256 value)
        external
        override
        returns (bool)
    {
        _approve(msg.sender, spender, value);
        return true;
    }

    function transfer(address to, uint256 value)
        external
        override
        returns (bool)
    {
        _transfer(msg.sender, to, value);
        return true;
    }

    function transferFrom(
        address from,
        address to,
        uint256 value
    ) external override returns (bool) {
        if (allowance[from][msg.sender] != uint256(-1)) {
            allowance[from][msg.sender] = allowance[from][msg.sender].sub(
                value
            );
        }
        _transfer(from, to, value);
        return true;
    }

    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external override {
        require(deadline >= block.timestamp, "MySwap: EXPIRED");
        bytes32 digest = keccak256(
            abi.encodePacked(
                "\x19\x01",
                DOMAIN_SEPARATOR,
                keccak256(
                    abi.encode(
                        PERMIT_TYPEHASH,
                        owner,
                        spender,
                        value,
                        nonces[owner]++,
                        deadline
                    )
                )
            )
        );
        address recoveredAddress = ecrecover(digest, v, r, s);
        require(
            recoveredAddress != address(0) && recoveredAddress == owner,
            "MySwap: INVALID_SIGNATURE"
        );
        _approve(owner, spender, value);
    }
}

pragma solidity =0.6.12;


library Math {
    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a >= b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow, so we distribute
        return (a / 2) + (b / 2) + ((a % 2 + b % 2) / 2);
    }
    // babylonian method (https://en.wikipedia.org/wiki/Methods_of_computing_square_roots#Babylonian_method)
    function sqrt(uint y) internal pure returns (uint z) {
        if (y > 3) {
            z = y;
            uint x = y / 2 + 1;
            while (x < z) {
                z = x;
                x = (y / x + x) / 2;
            }
        } else if (y != 0) {
            z = 1;
        }
    }
}

pragma solidity =0.6.12;


library UQ112x112 {
    uint224 constant Q112 = 2**112;

    // encode a uint112 as a UQ112x112
    function encode(uint112 y) internal pure returns (uint224 z) {
        z = uint224(y) * Q112; // never overflows
    }

    // divide a UQ112x112 by a uint112, returning a UQ112x112
    function uqdiv(uint224 x, uint112 y) internal pure returns (uint224 z) {
        z = x / uint224(y);
    }
}

pragma solidity >=0.5.0;

interface IMySwapPair {
    event Mint(address indexed sender, uint256 amount0, uint256 amount1);
    event Burn(
        address indexed sender,
        uint256 amount0,
        uint256 amount1,
        address indexed to
    );
    event Swap(
        address indexed sender,
        uint256 amount0In,
        uint256 amount1In,
        uint256 amount0Out,
        uint256 amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint256);

    function factory() external pure returns (address);

    function token0() external pure returns (address);

    function token1() external pure returns (address);

    function getReserves()
        external
        view
        returns (
            uint112 reserve0,
            uint112 reserve1,
            uint32 blockTimestampLast
        );

    function price0CumulativeLast() external view returns (uint256);

    function price1CumulativeLast() external view returns (uint256);

    function kLast() external view returns (uint256);

    function mint(address to) external returns (uint256 liquidity);

    function burn(address to)
        external
        returns (uint256 amount0, uint256 amount1);

    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external;

    function skim(address to) external;

    function sync() external;

    function fee() external view returns (uint8);

    function feeTo() external view returns (address);

    function getFeeTo() external view returns (address);

    function creator() external view returns (address);

    function birthday() external view returns (uint256);

    function rootKmul() external view returns (uint8);

    function initialize(address, address) external;

    function setFeeTo(address) external;

    function setrootKmul(uint8) external;

    function setFee(uint8) external;

    function getDeposited()
        external
        view
        returns (uint256 _deposited0, uint256 _deposited1);

    function getDummy()
        external
        view
        returns (uint256 _dummy0, uint256 _dummy1);

    function balanceOfIndex(uint8 tokenIndex)
        external
        view
        returns (uint256 balance);
}

pragma solidity >=0.5.0;

interface IMySwapCallee {
    function myswapCall(address sender, uint amount0, uint amount1, bytes calldata data) external;
}

pragma solidity =0.6.12;


interface IMigrator {
    function desiredLiquidity() external view returns (uint256);
}

interface IMySwapHook {
    function swapHook(
        address sender,
        uint256 amount0Out,
        uint256 amount1Out,
        address to
    ) external;
}

interface IVault {
    function totalSupply() external view returns (uint256);

    function balanceOf(address owner) external view returns (uint256);

    function deposit(uint256) external;

    function withdraw(uint256) external;

    function balance() external view returns (uint256);
}


contract MySwapPair is MySwapERC20 {
    using SafeMath for uint256;
    using UQ112x112 for uint224;

    uint256 public constant MINIMUM_LIQUIDITY = 10**3;
    bytes4 private constant SELECTOR = bytes4(keccak256(bytes('transfer(address,uint256)')));

    address public factory;
    address[2] private tokens;


    address[2] public vaults;
    uint16[2] public redepositRatios;
    uint256[2] public depositeds;
    uint112[2] public dummys;
    address public feeTo;
    address public creator;
    address public swapHookAddress;
    uint112[2] private reserves; // uses single storage slot, accessible via getReserves
    uint32 private blockTimestampLast; // uses single storage slot, accessible via getReserves

    uint256 public birthday;
    uint256[2] private priceCumulativeLasts;
    uint256 public kLast; // reserve0 * reserve1, as of immediately after the most recent liquidity event
    uint8 public rootKmul = 0; // mint liquidity equivalent to 1/6th of the growth in sqrt(k)
    uint8 public fee = 2;
    uint256 private unlocked = 1;
	
    event Mint(address indexed sender, uint256 amount0, uint256 amount1);
    event Burn(address indexed sender, uint256 amount0, uint256 amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint256 amount0In,
        uint256 amount1In,
        uint256 amount0Out,
        uint256 amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);
    event DepositedUpdated(uint256 deposited0, uint256 deposited1);
    event VaultUpdated(uint8 tokenIndex, address indexed vault);
    event RedepositRatioUpdated(uint8 tokenIndex, uint16 ratio);
    event DummyMint(uint256 amount0, uint256 amount1);
    event DummyBurn(uint256 amount0, uint256 amount1);
    event FeeToUpdated(address indexed feeTo);
    event RootKmulUpdated(uint8 rootKmul);
    event SwapHookUpdated(address swapHookAddress);
    event FeeUpdated(uint8 fee);
	
    modifier lock() {
        require(unlocked == 1, 'MySwap: LOCKED');
        unlocked = 0;
        _;
        unlocked = 1;
    }
    modifier onlyFeeToSetter() {
        require(msg.sender == IMySwapFactory(factory).feeToSetter(), 'MySwap: FORBIDDEN');
        _;
    }
    function token0() public view returns (address) {
        return tokens[0];
    }
    function token1() public view returns (address) {
        return tokens[1];
    }
    function price0CumulativeLast() public view returns (uint256) {
        return priceCumulativeLasts[0];
    }
    function price1CumulativeLast() public view returns (uint256) {
        return priceCumulativeLasts[1];
    }
    function getReserves()
        public
        view
        returns (
            uint112 _reserve0,
            uint112 _reserve1,
            uint32 _blockTimestampLast
        )
    {
        _reserve0 = reserves[0];
        _reserve1 = reserves[1];
        _blockTimestampLast = blockTimestampLast;
    }

    function getDeposited() public view returns (uint256, uint256) {
        return (depositeds[0], depositeds[1]);
    }
    function getDummy() public view returns (uint256, uint256) {
        return (dummys[0], dummys[1]);
    }
    function _safeTransfer(
        uint8 tokenIndex,
        address to,
        uint256 value
    ) private {
        uint256 balance = IERC20(tokens[tokenIndex]).balanceOf(address(this));
        bool success;
        bytes memory data;
        if (balance < value) {
            _withdrawAll(tokenIndex);
            (success, data) = tokens[tokenIndex].call(abi.encodeWithSelector(SELECTOR, to, value));
            if (redepositRatios[tokenIndex] > 0) {
                _redeposit(tokenIndex);
            }
        } else {
            (success, data) = tokens[tokenIndex].call(abi.encodeWithSelector(SELECTOR, to, value));
        }
        require(success && (data.length == 0 || abi.decode(data, (bool))), 'MySwap: TRANSFER_FAILED');
    }

    constructor() public {
        factory = msg.sender;
        birthday = block.timestamp;
    }

    function initialize(address _token0, address _token1) external {
        require(msg.sender == factory, 'MySwap: FORBIDDEN'); // sufficient check
        tokens[0] = _token0;
        tokens[1] = _token1;
        symbol = string(abi.encodePacked('MLP:', IERC20MySwap(_token0).symbol(), '-', IERC20MySwap(_token1).symbol()));
    }

    function setFeeTo(address _feeTo) external onlyFeeToSetter {
        feeTo = _feeTo;
        emit FeeToUpdated(_feeTo);
    }

    function setRootKmul(uint8 _rootKmul) external onlyFeeToSetter {
        rootKmul = _rootKmul;
        emit RootKmulUpdated(_rootKmul);
    }

    function setFee(uint8 _fee) external onlyFeeToSetter {
        fee = _fee;
        emit FeeUpdated(fee);
    }

    function setSwapHook(address _swapHookAddress) external onlyFeeToSetter {
        swapHookAddress = _swapHookAddress;
        emit SwapHookUpdated(swapHookAddress);
    }

    function getFeeTo() public view returns (address) {
        if (feeTo != address(0)) {
            return feeTo;
        } else {
            return IMySwapFactory(factory).feeTo();
        }
    }

    function _update(
        uint256 balance0,
        uint256 balance1,
        uint112 _reserve0,
        uint112 _reserve1
    ) private {
        require(balance0 <= uint112(-1) && balance1 <= uint112(-1), 'MySwap: OVERFLOW');
        uint32 blockTimestamp = uint32(block.timestamp % 2**32);
        uint32 timeElapsed = blockTimestamp - blockTimestampLast; // overflow is desired
        if (timeElapsed > 0 && _reserve0 != 0 && _reserve1 != 0) {
            // * never overflows, and + overflow is desired
            priceCumulativeLasts[0] += uint256(UQ112x112.encode(_reserve1).uqdiv(_reserve0)) * timeElapsed;
            priceCumulativeLasts[1] += uint256(UQ112x112.encode(_reserve0).uqdiv(_reserve1)) * timeElapsed;
        }
        reserves[0] = uint112(balance0);
        reserves[1] = uint112(balance1);
        blockTimestampLast = blockTimestamp;
        emit Sync(reserves[0], reserves[1]);
    }

    function _mintFee(uint112 _reserve0, uint112 _reserve1) private {
        uint256 _kLast = kLast; // gas savings
        if (_kLast != 0) {
            uint256 rootK = Math.sqrt(uint256(_reserve0).mul(_reserve1));
            uint256 rootKLast = Math.sqrt(_kLast);
            if (rootK > rootKLast) {
                uint256 numerator = totalSupply.mul(rootK.sub(rootKLast));
                uint256 denominator = rootK.mul(rootKmul).add(rootKLast);
                uint256 liquidity = numerator / denominator;
                if (liquidity > 0) _mint(getFeeTo(), liquidity);
            }
        }
    }

    function mint(address to) external lock returns (uint256 liquidity) {
        (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
        uint256 balance0 = balanceOfIndex(0);
        uint256 balance1 = balanceOfIndex(1);
        uint256 amount0 = balance0.sub(_reserve0);
        uint256 amount1 = balance1.sub(_reserve1);
        _reserve0 -= dummys[0];
        _reserve1 -= dummys[1];

        _mintFee(_reserve0, _reserve1);
        uint256 _totalSupply = totalSupply; // gas savings, must be defined here since totalSupply can update in _mintFee
        if (_totalSupply == 0) {
            address migrator = IMySwapFactory(factory).migrator();
            if (msg.sender == migrator) {
                liquidity = IMigrator(migrator).desiredLiquidity();
                require(liquidity > 0 && liquidity != uint256(-1), 'Bad desired liquidity');
            } else {
                require(migrator == address(0), 'Must not have migrator');
                liquidity = Math.sqrt(amount0.mul(amount1)).sub(MINIMUM_LIQUIDITY);
                _mint(address(0), MINIMUM_LIQUIDITY); // permanently lock the first MINIMUM_LIQUIDITY tokens
            }
            creator = to; // set creator
        } else {
            liquidity = Math.min(amount0.mul(_totalSupply) / _reserve0, amount1.mul(_totalSupply) / _reserve1);
        }
        require(liquidity > 0, 'MySwap: INSUFFICIENT_LIQUIDITY_MINTED');
        _mint(to, liquidity);
        _reserve0 += dummys[0];
        _reserve1 += dummys[1];

        _update(balance0, balance1, _reserve0, _reserve1);
        kLast = uint256(reserves[0] - dummys[0]).mul(reserves[1] - dummys[1]); // reserve0 and reserve1 are up-to-date
        emit Mint(msg.sender, amount0, amount1);
    }

    function burn(address to) external lock returns (uint256 amount0, uint256 amount1) {
        (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
        uint256 balance0 = balanceOfIndex(0).sub(dummys[0]);
        uint256 balance1 = balanceOfIndex(1).sub(dummys[1]);
        uint256 liquidity = balanceOf[address(this)];

        _mintFee(_reserve0 - dummys[0], _reserve1 - dummys[1]);
        uint256 _totalSupply = totalSupply; // gas savings, must be defined here since totalSupply can update in _mintFee
        amount0 = liquidity.mul(balance0) / _totalSupply; // using balances ensures pro-rata distribution
        amount1 = liquidity.mul(balance1) / _totalSupply; // using balances ensures pro-rata distribution
        require(amount0 > 0 && amount1 > 0, 'MySwap: INSUFFICIENT_LIQUIDITY_BURNED');
        _burn(address(this), liquidity);
        _safeTransfer(0, to, amount0);
        _safeTransfer(1, to, amount1);
        balance0 = balanceOfIndex(0);
        balance1 = balanceOfIndex(1);

        _update(balance0, balance1, _reserve0, _reserve1);
        kLast = uint256(reserves[0] - dummys[0]).mul(reserves[1] - dummys[1]); // reserve0 and reserve1 are up-to-date
        emit Burn(msg.sender, amount0, amount1, to);
    }

    function dummyMint(uint256 amount0, uint256 amount1) external onlyFeeToSetter lock {
        (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
        dummys[0] += uint112(amount0);
        dummys[1] += uint112(amount1);
        _update(balanceOfIndex(0), balanceOfIndex(1), _reserve0, _reserve1);
        emit DummyMint(amount0, amount1);
    }

    function dummyBurn(uint256 amount0, uint256 amount1) external onlyFeeToSetter lock {
        (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
        dummys[0] -= uint112(amount0);
        dummys[1] -= uint112(amount1);
        _update(balanceOfIndex(0), balanceOfIndex(1), _reserve0, _reserve1);
        emit DummyBurn(amount0, amount1);
    }

    function swap(
        uint256 amount0Out,
        uint256 amount1Out,
        address to,
        bytes calldata data
    ) external lock {
        //确认amount0Out和amount1Out都大于0
        require(amount0Out > 0 || amount1Out > 0, 'MySwap: INSUFFICIENT_OUTPUT_AMOUNT');
        (uint112 _reserve0, uint112 _reserve1, ) = getReserves(); // gas savings
        require(amount0Out < _reserve0 && amount1Out < _reserve1, 'MySwap: INSUFFICIENT_LIQUIDITY');

        uint256 balance0;
        uint256 balance1;
        {
            // scope for _token{0,1}, avoids stack too deep errors
            address _token0 = tokens[0];
            address _token1 = tokens[1];
            require(to != _token0 && to != _token1, 'MySwap: INVALID_TO');
            if (amount0Out > 0) _safeTransfer(0, to, amount0Out); // optimistically transfer tokens
            if (amount1Out > 0) _safeTransfer(1, to, amount1Out); // optimistically transfer tokens
            if (data.length > 0) IMySwapCallee(to).myswapCall(msg.sender, amount0Out, amount1Out, data);
            if (swapHookAddress != address(0))
                IMySwapHook(swapHookAddress).swapHook(msg.sender, amount0Out, amount1Out, to);
            balance0 = balanceOfIndex(0);
            balance1 = balanceOfIndex(1);
        }
        uint256 amount0In = balance0 > _reserve0 - amount0Out ? balance0 - (_reserve0 - amount0Out) : 0;
        uint256 amount1In = balance1 > _reserve1 - amount1Out ? balance1 - (_reserve1 - amount1Out) : 0;
        require(amount0In > 0 || amount1In > 0, 'MySwap: INSUFFICIENT_INPUT_AMOUNT');
        {
            // scope for reserve{0,1}Adjusted, avoids stack too deep errors
            uint256 balance0Adjusted = balance0.mul(1000).sub(amount0In.mul(fee));
            uint256 balance1Adjusted = balance1.mul(1000).sub(amount1In.mul(fee));
            require(
                balance0Adjusted.mul(balance1Adjusted) >= uint256(_reserve0).mul(_reserve1).mul(1000**2),
                'MySwap: K'
            );
        }

        _update(balance0, balance1, _reserve0, _reserve1);
        emit Swap(msg.sender, amount0In, amount1In, amount0Out, amount1Out, to);
    }

    function skim(address to) external lock {
        _safeTransfer(0, to, balanceOfIndex(0).sub(reserves[0]));
        _safeTransfer(1, to, balanceOfIndex(1).sub(reserves[1]));
    }

    function sync() external lock {
        _update(balanceOfIndex(0), balanceOfIndex(1), reserves[0], reserves[1]);
    }

    function balanceOfIndex(uint8 tokenIndex) public view returns (uint256 balance) {
        balance = IERC20(tokens[tokenIndex]).balanceOf(address(this)).add(depositeds[tokenIndex]).add(
            dummys[tokenIndex]
        );
    }

    function approveByIndex(uint8 tokenIndex) public onlyFeeToSetter {
        IERC20(tokens[tokenIndex]).approve(vaults[tokenIndex], uint256(-1));
    }

    function unApproveByIndex(uint8 tokenIndex) public onlyFeeToSetter {
        IERC20(tokens[tokenIndex]).approve(vaults[tokenIndex], 0);
    }

    function setVaults(uint8 tokenIndex, address vault) public onlyFeeToSetter {
        vaults[tokenIndex] = vault;
        approveByIndex(tokenIndex);
        emit VaultUpdated(tokenIndex, vault);
    }

    function _deposit(uint8 tokenIndex, uint256 amount) internal {
        require(amount > 0, 'deposit amount must be greater than 0');
        depositeds[tokenIndex] = depositeds[tokenIndex].add(amount);
        IVault(vaults[tokenIndex]).deposit(amount);
        emit DepositedUpdated(depositeds[0], depositeds[1]);
    }

    function depositSome(uint8 tokenIndex, uint256 amount) external onlyFeeToSetter {
        _deposit(tokenIndex, amount);
    }

    function depositAll(uint8 tokenIndex) external onlyFeeToSetter {
        _deposit(tokenIndex, IERC20(tokens[tokenIndex]).balanceOf(address(this)));
    }

    function _redeposit(uint8 tokenIndex) internal {
        uint256 amount = IERC20(tokens[tokenIndex]).balanceOf(address(this)).mul(redepositRatios[tokenIndex]).div(1000);
        _deposit(tokenIndex, amount);
    }

    function setRedepositRatio(uint8 tokenIndex, uint16 _redpositRatio) external onlyFeeToSetter {
        require(_redpositRatio <= 1000, 'ratio too large');
        redepositRatios[tokenIndex] = _redpositRatio;
        emit RedepositRatioUpdated(tokenIndex, _redpositRatio);
    }

    function _withdraw(uint8 tokenIndex, uint256 amount) internal {
        require(amount > 0, 'withdraw amount must be greater than 0');
        uint256 before = IERC20(tokens[tokenIndex]).balanceOf(address(this));
        IVault(vaults[tokenIndex]).withdraw(amount);
        uint256 received = IERC20(tokens[tokenIndex]).balanceOf(address(this)).sub(before);
        if (received <= depositeds[tokenIndex]) {
            depositeds[tokenIndex] -= received;
        } else {
            uint256 reward = received.sub(depositeds[tokenIndex]);
            depositeds[tokenIndex] = 0;
            _safeTransfer(tokenIndex, getFeeTo(), reward);
        }

        emit DepositedUpdated(depositeds[0], depositeds[1]);
    }

    function _withdrawAll(uint8 tokenIndex) internal {
        _withdraw(tokenIndex, IERC20(vaults[tokenIndex]).balanceOf(address(this)));
    }

    function withdraw(uint8 tokenIndex, uint256 amount) external onlyFeeToSetter {
        _withdraw(tokenIndex, amount);
    }

    function withdrawAll(uint8 tokenIndex) external onlyFeeToSetter {
        _withdrawAll(tokenIndex);
    }
}

pragma solidity =0.6.12;

contract MySwapFactory is IMySwapFactory {
    address public override feeTo;
    address public override feeToSetter;
    address public override migrator;
    mapping(address => mapping(address => address)) public override getPair;
    address[] public override allPairs;

    event PairCreated(
        address indexed token0,
        address indexed token1,
        address pair,
        uint256
    );

    constructor() public {
        feeToSetter = msg.sender;
        feeTo = msg.sender;
    }

    function allPairsLength() external override view returns (uint256) {
        return allPairs.length;
    }

    function pairCodeHash() external override pure returns (bytes32) {
        return keccak256(type(MySwapPair).creationCode);
    }

    function createPair(address tokenA, address tokenB)
        external
        override
        returns (address pair)
    {
        require(tokenA != tokenB, "MySwap: IDENTICAL_ADDRESSES");
        (address token0, address token1) = tokenA < tokenB
            ? (tokenA, tokenB)
            : (tokenB, tokenA);
        require(token0 != address(0), "MySwap: ZERO_ADDRESS");
        require(getPair[token0][token1] == address(0), "MySwap: PAIR_EXISTS"); // single check is sufficient
        bytes memory bytecode = type(MySwapPair).creationCode;
        bytes32 salt = keccak256(abi.encodePacked(token0, token1));
        //solium-disable-next-line
        assembly {
            pair := create2(0, add(bytecode, 32), mload(bytecode), salt)
        }
        MySwapPair(pair).initialize(token0, token1);
        getPair[token0][token1] = pair;
        getPair[token1][token0] = pair; // populate mapping in the reverse direction
        allPairs.push(pair);
        emit PairCreated(token0, token1, pair, allPairs.length);
    }

    modifier onlyFeeToSetter() {
        require(msg.sender == feeToSetter, "MySwap: FORBIDDEN");
        _;
    }

    function setFeeTo(address _feeTo) external override onlyFeeToSetter {
        feeTo = _feeTo;
    }

    function setMigrator(address _migrator) external override onlyFeeToSetter {
        migrator = _migrator;
    }

    function setFeeToSetter(address _feeToSetter)
        external
        override
        onlyFeeToSetter
    {
        feeToSetter = _feeToSetter;
    }
}