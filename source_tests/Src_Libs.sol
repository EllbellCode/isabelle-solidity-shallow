// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Internal library functions called through `using L for T` and as `L.f(...)`, with require messages, unchecked blocks, early
// returns (guard clauses), overloading, calls between library functions and narrow types, in the style of SafeMath.
library S_SafeMath {
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");
        return c;
    }
    function sub(uint256 a, uint256 b) internal pure returns (uint256) { return sub(a, b, "SafeMath: subtraction overflow"); }
    function sub(uint256 a, uint256 b, string memory message) internal pure returns (uint256) {
        require(b <= a, message);
        return a - b;
    }
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) { return 0; }
        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");
        return c;
    }
    function div(uint256 a, uint256 b) internal pure returns (uint256) { require(b > 0, "SafeMath: division by zero"); return a / b; }
    function min(uint256 a, uint256 b) internal pure returns (uint256) { if (a < b) { return a; } return b; }
    function wrappingAdd(uint256 a, uint256 b) internal pure returns (uint256) { unchecked { return a + b; } }
    function mulDiv(uint256 a, uint256 b, uint256 c) internal pure returns (uint256) { return div(mul(a, b), c); }
}

library S_Small {
    function inc(uint8 a) internal pure returns (uint8) { return a + 1; }
    function isZero(uint256 a) internal pure returns (bool) { return a == 0; }
}

contract S_Libs {
    using S_SafeMath for uint256;
    using S_Small for uint8;
    using S_Small for uint256;

    uint256 public x;
    uint8 public small;
    bool public flag;
    mapping(address => uint256) public bal;

    function guard(uint256 p) internal returns (uint256) {
        if (p > 10) { return 1; }
        x += 1;
        if (p == 3) { return 2; }
        return 3;
    }
    function early(uint256 p) internal { if (p == 0) { return; } x += p; }

    function t1(uint256 p) external { x = x.add(p); }
    function t2(uint256 p) external { x = S_SafeMath.sub(x, p); }
    function t3(uint256 p) external { x = x.sub(p, "custom"); }
    function t4(uint256 p) external { x = x.mul(p); }
    function t5(uint256 p) external { x = x.div(p); }
    function t6(uint256 p) external { x = x.min(p); }
    function t7(uint256 p) external { x = x.wrappingAdd(p); }
    function t8(uint256 a, uint256 b) external { x = x.mulDiv(a, b); }
    function t9(uint8 p) external { small = p.inc(); }
    function t10(uint256 p) external { flag = p.isZero(); }
    function t11(uint256 p) external { bal[msg.sender] = bal[msg.sender].add(p).mul(2); }
    function t12(uint256 p) external { x = guard(p); }
    function t13(uint256 p) external { early(p); }
}
