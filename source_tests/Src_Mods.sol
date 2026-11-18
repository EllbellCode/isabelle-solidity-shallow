// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Modifiers (inlined by transpile.py): placement of `_`, arguments, locals, nesting, repeated `_`, constructors.
contract S_Mods {
    address owner;
    uint256 x;
    uint256 y;
    uint256 counter;
    bool locked;

    modifier onlyOwner() { require(msg.sender == owner); _; }
    modifier atLeast(uint256 v) { require(x >= v); _; }
    modifier bump() { counter++; _; counter += 10; }
    modifier noReentry() { require(!locked); locked = true; _; locked = false; }
    modifier twice() { _; _; }
    modifier withLocal(uint256 a) { uint256 t = a + 1; x = t; _; y = t; }
    modifier branch(bool b) { if (b) { _; } else { y = 99; } }
    modifier loopy(uint256 n) { for (uint256 i = 0; i < n; i++) { _; } }
    modifier setC() { counter = 5; _; }
    modifier useArg(uint256 v) { y = v; _; }
    modifier needValue(uint256 m) { require(msg.value >= m); _; }
    modifier init() { y = 7; _; y += 1; }

    constructor() payable init { owner = msg.sender; x = y; }

    function setX(uint256 v) public onlyOwner { x = v; }
    function f(uint256 v) public atLeast(v) bump { y = v; }
    function g() public onlyOwner noReentry bump { x += 1; }
    function dbl() public twice { x += 1; }
    function wl(uint256 v) public withLocal(v) { x = x + 100; }
    function shadow(uint256 t) public withLocal(t) { y = y + t; }
    function br(uint256 v) public branch(v > 3) { x = v; }
    function loopLp(uint256 n) public loopy(n) { x += 1; }
    // when are modifier arguments evaluated: at entry of the function, or when the modifier is entered?
    function ord() public setC useArg(counter) { }
    function ord2() public useArg(counter) setC { }
    function paid(uint256 v) public payable needValue(v) { x = msg.value; }
    function nested(uint256 v) public onlyOwner atLeast(v) branch(v < 50) bump { y = v; }
}
