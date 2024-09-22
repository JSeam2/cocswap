// SPDX-License-Identifier: AGPL-3.0
pragma solidity ^0.8.26;

error Initialized();
error NotInitialized();
error VerificationFailed();
error InvalidShares();
error InvalidReserve0();
error InvalidReserve1();
error InvalidAmounts();

contract COCSwap {
    IERC20 public immutable token0;
    IERC20 public immutable token1;
    Halo2Verifier public immutable verifier;

    uint256 public reserve0;
    uint256 public reserve1;

    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;

    constructor(address _token0, address _token1, address _verifier) {
        token0 = IERC20(_token0);
        token1 = IERC20(_token1);
        verifier = Halo2Verifier(_verifier);
    }

    function _mint(address _to, uint256 _amount) private {
        balanceOf[_to] += _amount;
        totalSupply += _amount;
    }

    function _burn(address _from, uint256 _amount) private {
        balanceOf[_from] -= _amount;
        totalSupply -= _amount;
    }

    function _update(uint256 _reserve0, uint256 _reserve1) private {
        reserve0 = _reserve0;
        reserve1 = _reserve1;
    }

    function swap(
        address tokenIn,
        uint256 amountIn,
        bytes calldata proof,
        uint256[] calldata instances
    ) external returns (uint256 amountOut) {
        require(
            tokenIn == address(token0) || tokenIn == address(token1),
            "Invalid token"
        );
        require(amountIn > 0, "Amount in = 0");

        bool isToken0 = tokenIn == address(token0);
        (IERC20 tokenInContract, IERC20 tokenOutContract) = isToken0
            ? (token0, token1)
            : (token1, token0);

        // omitted declaration cuz of stack too deep error
        // uint256 a0 = instances[0];
        // uint256 b0 = instances[1];
        // We don't need these value
        // uint256 delta_a = instances[2];
        // uint256 delta_b = instances[3];
        // uint256 c = instances[4];
        uint256 new_a = instances[5];
        uint256 new_b = instances[6];

        if (instances[0] != reserve0) {
            revert InvalidReserve0();
        }

        if (instances[1] != reserve1) {
            revert InvalidReserve1();
        }

        if (verifier.verifyProof(proof, instances)) {
            // Calculate amountOut based on the new state
            amountOut = isToken0
                ? (instances[1] - new_b)
                : (instances[0] - new_a);

            // Transfer tokens
            tokenInContract.transferFrom(msg.sender, address(this), amountIn);
            tokenOutContract.transfer(msg.sender, amountOut);

            // Update reserves
            _update(
                token0.balanceOf(address(this)),
                token1.balanceOf(address(this))
            );
        } else {
            revert VerificationFailed();
        }

        require(amountOut > 0, "Insufficient output amount");
    }

    function addLiquidityInit(
        uint256 _amount0,
        uint256 _amount1
    ) external returns (uint256 shares) {
        if (totalSupply == 0) {
            // initialization

            // TODO: we assume constant product in this case for the purpose of the hackathon
            // This can also be generalized
            token0.transferFrom(msg.sender, address(this), _amount0);
            token1.transferFrom(msg.sender, address(this), _amount1);

            shares = _sqrt(_amount0 * _amount1);

            _mint(msg.sender, shares);

            _update(
                token0.balanceOf(address(this)),
                token1.balanceOf(address(this))
            );
        } else {
            revert Initialized();
        }
    }

    function addLiquidity(
        uint256 _amount0,
        uint256 _amount1,
        bytes calldata proof,
        uint256[] calldata instances
    ) external returns (uint256 shares) {
        token0.transferFrom(msg.sender, address(this), _amount0);
        token1.transferFrom(msg.sender, address(this), _amount1);

        uint256 a0 = instances[0];
        uint256 b0 = instances[1];
        // We don't need these values for now
        // uint256 delta_a = instances[2];
        // uint256 delta_b = instances[3];
        // uint256 c = instances[4];
        uint256 new_a = instances[5];
        uint256 new_b = instances[6];

        if (a0 != reserve0) {
            revert InvalidReserve0();
        }

        if (b0 != reserve1) {
            revert InvalidReserve1();
        }

        if (totalSupply > 0) {
            // after initialization

            // TODO: Generalize this further, these values can be provided via instances
            if (verifier.verifyProof(proof, instances)) {
                shares = _min(
                    (new_a * totalSupply) / reserve0,
                    (new_b * totalSupply) / reserve1
                );
            } else {
                revert VerificationFailed();
            }
        } else {
            revert NotInitialized();
        }

        if (shares > 0) {
            _mint(msg.sender, shares);
        } else {
            revert InvalidShares();
        }

        _update(
            token0.balanceOf(address(this)),
            token1.balanceOf(address(this))
        );
    }

    function removeLiquidity(
        uint256 _shares,
        uint256[] calldata instances
    ) external returns (uint256 amount0, uint256 amount1) {
        require(_shares > 0, "Invalid shares amount");

        uint256 a0 = instances[0];
        uint256 b0 = instances[1];
        // uint256 delta_a = instances[2];
        // uint256 delta_b = instances[3];
        // We don't need these values for now
        // uint256 c = instances[4];
        uint256 new_a = instances[5];
        uint256 new_b = instances[6];

        if (a0 != reserve0) {
            revert InvalidReserve0();
        }

        if (b0 != reserve1) {
            revert InvalidReserve1();
        }

        // Calculate the amounts to return based on the new state
        amount0 = (a0 * _shares) / totalSupply;
        amount1 = (b0 * _shares) / totalSupply;

        // Burn the shares
        _burn(msg.sender, _shares);

        // Transfer tokens to the user
        token0.transfer(msg.sender, amount0);
        token1.transfer(msg.sender, amount1);

        // Update the reserves
        _update(new_a, new_b);

        if (amount0 == 0 && amount1 == 0) {
            revert InvalidAmounts();
        }
    }

    function _sqrt(uint256 y) private pure returns (uint256 z) {
        if (y > 3) {
            z = y;
            uint256 x = y / 2 + 1;
            while (x < z) {
                z = x;
                x = (y / x + x) / 2;
            }
        } else if (y != 0) {
            z = 1;
        }
    }

    function _min(uint256 x, uint256 y) private pure returns (uint256) {
        return x <= y ? x : y;
    }
}

interface IERC20 {
    function totalSupply() external view returns (uint256);
    function balanceOf(address account) external view returns (uint256);
    function transfer(
        address recipient,
        uint256 amount
    ) external returns (bool);
    function allowance(
        address owner,
        address spender
    ) external view returns (uint256);
    function approve(address spender, uint256 amount) external returns (bool);
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);
}

interface Halo2Verifier {
    function verifyProof(
        bytes calldata proof,
        uint256[] calldata instances
    ) external returns (bool);
}
