// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// As Ext.sol, with assumptions on what the view functions (and, stage B', two state-changing functions: grow, approve) of the callee answer (@custom:assume, see baseline/SOLIDITY_UPDATE_EXTASSUME.md).
// Calls to another contract through an interface. The callee is not part of the model: the harness stands in for it with a contract whose
// answers are a fixed function of the call counter, the function and the arguments (see conf.py, "stand-in callee").
interface S_IToken {
    /// @custom:assume norevert
    /// @custom:assume max 1000000
    function balanceOf(address a) external view returns (uint256);
    function transfer(address to, uint256 v) external returns (bool);
    function transferFrom(address f, address t, uint256 v) external returns (bool);
    /// @custom:assume constant
    /// @custom:assume norevert
    function decimals() external view returns (uint8);
    function ping() external;
    /// @custom:assume norevert
    /// @custom:assume min 3
    /// @custom:assume max 9
    function grow(uint256 k) external returns (uint256);
    /// @custom:assume norevert
    function approve(address s, uint256 v) external returns (bool);
    /// @custom:assume norevert
    function owner() external view returns (address);
    /// @custom:assume norevert
    function flag(uint256 x) external view returns (bool);
    /// @custom:assume min 10
    /// @custom:assume max 20
    function quota(uint256 k) external view returns (uint256);
}

contract S_ExtAssume {
    S_IToken public token;
    uint256 public last;
    uint256 public total;
    bool public okFlag;
    address public who;
    mapping(address => uint256) public seen;

    constructor(S_IToken t) { token = t; }

    function setToken(S_IToken t) external { token = t; }
    function bal(address a) external { last = token.balanceOf(a); }
    function bal2(address a) external { last = token.balanceOf(a) + token.balanceOf(address(this)); }
    function send(address to, uint256 v) external { require(token.transfer(to, v)); total += v; }
    function pull(uint256 v) external { bool ok = token.transferFrom(msg.sender, address(this), v); okFlag = ok; if (ok) { total += v; } }
    function dec() external { last = token.decimals(); }
    function pg() external { token.ping(); }
    function gr(uint256 k) external { last = token.grow(k); }
    function ap(address s, uint256 v) external { okFlag = token.approve(s, v); }
    function qt(uint256 k) external { last = token.quota(k); }
    function own() external { who = token.owner(); }
    function fl(uint256 x) external { okFlag = token.flag(x); }
    function twice(address a) external { uint256 b1 = token.balanceOf(a); token.ping(); uint256 b2 = token.balanceOf(a); last = b1 == b2 ? 1 : 2; }
    function viaConv(address t, address a) external { last = S_IToken(t).balanceOf(a); }
    function remember(address a) external { seen[a] = token.balanceOf(a); }
    function guarded(address a, uint256 min) external { require(token.balanceOf(a) >= min, "low"); total += 1; }
}
