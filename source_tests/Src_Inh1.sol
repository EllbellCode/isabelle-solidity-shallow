// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Inheritance, single chain: initialiser and constructor order, base constructor arguments, virtual dispatch of an
// internal function, super calls, inherited modifiers and public functions. Digits of `log` record the order of execution.
abstract contract S_A {
    uint256 a = 5;
    address owner;
    uint256 log;
    constructor(uint256 x) { a = a + x; owner = msg.sender; log = log * 10 + 1; }
    modifier onlyOwner() { require(msg.sender == owner); _; }
    function f() public virtual { log = log * 10 + 4; }
    function g() internal virtual { log = log * 10 + 5; }
    function callG() public { g(); }
    function setA(uint256 v) public onlyOwner { a = v; }
}

abstract contract S_B is S_A {
    uint256 b = a + 10;                       // initialiser that reads a base variable
    constructor(uint256 y) S_A(y + 1) { b = b + y; log = log * 10 + 2; }
    function f() public virtual override { super.f(); log = log * 10 + 6; }
    function g() internal virtual override { log = log * 10 + 7; }
}

contract S_C is S_B {
    uint256 c;
    constructor() payable S_B(5) { c = a + b; log = log * 10 + 3; }
    function f() public override { super.f(); log = log * 10 + 8; }
    function h(uint256 d) public onlyOwner { c += d; a = a + 1; }
}
