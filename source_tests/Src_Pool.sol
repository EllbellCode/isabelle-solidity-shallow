// SPDX-License-Identifier: AGPL-3.0-only
// Flattened from Certora's examples (DEFI/LiquidityPool/contracts: IERC20.sol, IFlashLoanReceiver.sol, ERC20.sol, Pool.sol @279e553),
// imports removed and the files concatenated in dependency order; the only addition are the three `@custom:assume norevert` lines (a comment for solc)
// that say the asset and the flash loan receiver answer every call they are made (stage B, baseline/SOLIDITY_UPDATE_EXTASSUME.md).
pragma solidity >=0.8.0;

// ---- IERC20.sol ----
interface S_IERC20 {
    function totalSupply() external view returns (uint256);

    /// @custom:assume norevert
    function balanceOf(address account) external view returns (uint256);

    function transfer(address recipient, uint256 amount) external returns (bool);

    function allowance(address owner, address spender) external view returns (uint256);

    function approve(address spender, uint256 amount) external returns (bool);

    /// @custom:assume norevert
    function transferFrom(
        address sender,
        address recipient,
        uint256 amount
    ) external returns (bool);

}

// ---- IFlashLoanReceiver.sol ----
interface S_IFlashLoanReceiver {
  /// @custom:assume norevert
  function executeOperation(uint256 amount,uint256 premium,address initiator) external returns (bool);
}

// ---- ERC20.sol ----
abstract contract S_ERC20 is S_IERC20{

    uint256 private _totalSupply;
    mapping(address => uint256) private _balanceOf;
    mapping(address => mapping(address => uint256)) private _allowance;
    function totalSupply() public view override returns (uint256) {
    return _totalSupply;
    }
    function balanceOf(address account) public view override returns (uint256) {
    return _balanceOf[account];
    }
    function allowance(address owner, address spender)
    public view virtual override returns (uint256)
  {
    return _allowance[owner][spender];
  }

    function approve(address spender, uint256 amount) override external returns (bool) {
        _allowance[msg.sender][spender] = amount;
        return true;
    }

    function transfer(address recipient, uint256 amount) override external returns (bool) {
        _balanceOf[msg.sender] -= amount;
        _balanceOf[recipient] += amount;
        
        return true;
    }

    function transferFrom(address from,address recipient,uint256 amount) 
    override external returns (bool) {
        if (_allowance[from][msg.sender] != type(uint256).max) {
            _allowance[from][msg.sender] -= amount;}
        _balanceOf[from] -= amount;
        _balanceOf[recipient] += amount;

        return true;
    }

    function _mint(address recipient, uint256 amount) internal {
        _totalSupply += amount;
        _balanceOf[recipient] += amount;
 
    }

    function _burn(address user, uint256 amount) internal {
        _totalSupply -= amount;
        _balanceOf[user] -= amount;
    }
     
}

// ---- Pool.sol ----
contract S_Pool is S_ERC20 {

  uint256 private constant _NOT_ENTERED = 1;
  uint256 private constant _ENTERED = 2;

  uint256 private _status;
  modifier nonReentrant() {
        // On the first call to nonReentrant, _notEntered will be true
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;

        _;

        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }

  S_IERC20 public asset;   
  uint256 private constant feePrecision = 10000; 
  //feeRate is up to 1%, so less than 100 as it is divided by feePrecision
  uint256 public feeRate; 
  uint256 public depositedAmount = 0;

  function sharesToAmount(uint256 shares) public view virtual returns (uint256) {
     return shares * depositedAmount / totalSupply();  
  }


  function amountToShares(uint256 amount) public view virtual returns (uint256) { 
      return amount * totalSupply() / depositedAmount;   
  }

  function deposit(uint256 amount) public nonReentrant() returns(uint256 shares) {
      if (totalSupply()==0 || depositedAmount == 0){
          shares = amount;
      }
      else{
        shares = amountToShares(amount);
        require (shares != 0);
      }
      asset.transferFrom(msg.sender,address(this),amount);
      depositedAmount = depositedAmount + amount;
      _mint(msg.sender,shares);
    }


  function withdraw(uint256 shares) public nonReentrant() returns (uint256 amountOut)  {
    uint256 poolBalance = asset.balanceOf(address(this));
    require (poolBalance != 0);
    amountOut = sharesToAmount(shares);
    require (amountOut != 0);
   	_burn(msg.sender,shares);
		asset.transferFrom(address(this),msg.sender,amountOut);
    depositedAmount = depositedAmount - amountOut;
    }

    
  function flashLoan(address receiverAddress, uint256 amount) nonReentrant() public {          
    uint256 totalPremium = calcPremium(amount);
    require (totalPremium != 0);
    uint256 amountPlusPremium = amount + totalPremium;
    asset.transferFrom(address(this),msg.sender,amount);
    depositedAmount = depositedAmount - amount;
    require(S_IFlashLoanReceiver(receiverAddress).executeOperation(amount,totalPremium,msg.sender),'P_INVALID_FLASH_LOAN_EXECUTOR_RETURN');
    asset.transferFrom(msg.sender,address(this),amountPlusPremium);
    depositedAmount = depositedAmount + amountPlusPremium;
  }

  function calcPremium(uint256 amount) public view returns (uint256){
    return ((amount*feeRate)/feePrecision);
  }

  function assetBalance() public view returns (uint256) {
    return asset.balanceOf(address(this));
  }
}

