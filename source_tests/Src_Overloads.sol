// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Overloaded functions: told apart by their parameter types (internal and public), an override of one overload in a derived contract,
// calls resolved by the types of the arguments.
abstract contract S_Base {
    uint256 public total;
    uint256 public last;
    bool public flag;

    function _put(uint256 a) internal { total += a; last = 1; }
    function _put(uint256 a, bool f) internal { total += a; flag = f; last = 2; }
    function _put(address to, uint256 a) internal virtual { total += a; last = 3; if (to == msg.sender) { flag = true; } }

    function put(uint256 a) public { _put(a); }
    function put(uint256 a, bool f) public { _put(a, f); }
    function put(address to, uint256 a) public { _put(to, a); }
    function noArgs() public { _put(1); }
}

contract S_Over is S_Base {
    function _put(address to, uint256 a) internal override { total += 2 * a; last = 4; if (to == msg.sender) { flag = false; } }
    function twice(uint256 a) public { _put(a); _put(a, true); }
}

// The overloads are declared in different classes of the hierarchy.
abstract contract S_OvA {
    uint256 public x;
    function set(uint256 a) public virtual { x = a; }
    function _bump(uint256 a) internal virtual { x += a; }
}

contract S_OvB is S_OvA {
    function set(uint256 a, uint256 b) public { x = a + b; _bump(a, b); }
    function _bump(uint256 a, uint256 b) internal { x += a * b; }
    function again(uint256 a) public { _bump(a); set(a); set(a, 1); }
}
