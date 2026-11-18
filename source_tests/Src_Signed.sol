// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Signed integers (int / int256), two's complement: order, checked and unchecked arithmetic, truncating division and remainder,
// negation, conversions, constant folding.  Grid mode of conf.py: 0, +-1, +-2, +-3, max, min, min + 1, +-2^128.
contract S_Signed {
    int256 r;
    int256 r2;
    uint256 u;
    bool b;
    mapping(address => int256) m;

    // checked arithmetic
    function add(int256 x, int256 y) public { r = x + y; }
    function sub(int256 x, int256 y) public { r = x - y; }
    function mul(int256 x, int256 y) public { r = x * y; }
    function dv(int256 x, int256 y) public { r = x / y; }               // truncates toward zero; min / -1 overflows
    function md(int256 x, int256 y) public { r = x % y; }               // the sign of the dividend; min % -1 == 0
    function neg(int256 x) public { r = -x; }                           // -min overflows
    // wrapping arithmetic
    function uadd(int256 x, int256 y) public { unchecked { r = x + y; } }
    function usub(int256 x, int256 y) public { unchecked { r = x - y; } }
    function umul(int256 x, int256 y) public { unchecked { r = x * y; } }
    function udv(int256 x, int256 y) public { unchecked { r = x / y; } } // min / -1 wraps to min, a zero divisor still reverts
    function umd(int256 x, int256 y) public { unchecked { r = x % y; } }
    function uneg(int256 x) public { unchecked { r = -x; } }
    // order
    function lt(int256 x, int256 y) public { b = x < y; }
    function gt(int256 x, int256 y) public { b = x > y; }
    function le(int256 x, int256 y) public { b = x <= y; }
    function ge(int256 x, int256 y) public { b = x >= y; }
    function eq(int256 x, int256 y) public { b = x == y; }
    function ne(int256 x, int256 y) public { b = x != y; }
    function ltZero(int256 x) public { b = x < 0; }
    function geMinusOne(int256 x) public { b = x >= -1; }
    // literals and constants
    function addLit(int256 x) public { r = x + 1; }
    function subLit(int256 x) public { r = x - 5; }
    function mulNeg(int256 x) public { r = x * -1; }
    function divNeg(int256 x) public { r = x / -1; }
    function divLit(int256 x) public { r = x / 3; }
    function mdLit(int256 x) public { r = x % -3; }
    function folded(int256 x) public { r = x + (2 - 5); }                // the constant is -3
    function foldedDiff() public { r = 2 - 5 + 10; }                     // intermediate -3
    function minLit() public { r = -57896044618658097711785492504343953926634992332820282019728792003956564819968; }
    function bigLit() public { r = 57896044618658097711785492504343953926634992332820282019728792003956564819967; }
    // compound assignment and increments, applied to a non-zero state (r starts at 0, which would hide signedness)
    function addEq(int256 x, int256 y) public { r = x; r += y; }
    function subEq(int256 x, int256 y) public { r = x; r -= y; }
    function mulEq(int256 x, int256 y) public { r = x; r *= y; }
    function dvEq(int256 x, int256 y) public { r = x; r /= y; }
    function mdEq(int256 x, int256 y) public { r = x; r %= y; }
    function incFrom(int256 x) public { r = x; r++; }
    function decFrom(int256 x) public { r = x; r--; }
    function setR(int256 x) public { r = x; }
    // conversions between int256 and uint256 (same bits)
    function toU(int256 x) public { u = uint256(x); }
    function fromU(uint256 x) public { r = int256(x); }
    function roundTrip(int256 x) public { r = int256(uint256(x)); }
    function absLike(int256 x) public { if (x < 0) { r = -x; } else { r = x; } }
    // mappings and locals
    function setM(address who, int256 v) public { m[who] = v; }
    function addM(address who, int256 v) public { m[who] += v; }
    function local(int256 x, int256 y) public {
        int256 t = x;
        t = t - y;
        r2 = t * 2;
    }
    function loopS(uint8 n) public {
        int256 s = 0;
        for (int256 i = -3; i < int256(uint256(n)); i++) { s += i; }
        r = s;
    }
}
