// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Narrow unsigned integers (uint8 ... uint248): arithmetic checked and unchecked at the width of the type, conversions,
// mixed widths, argument range checks of the ABI decoder.  Grid mode of conf.py (edges of each range and values just outside it).
contract S_Widths {
    uint8 a8;
    uint64 a64;
    uint128 a128;
    uint192 a192;
    uint248 a248;
    uint256 a256;
    bool b;
    mapping(address => uint8) m8;
    mapping(uint8 => uint64) k8;

    constructor(uint8 init) { a8 = init; }

    // checked arithmetic at the width of the type
    function add8(uint8 x, uint8 y) public { a8 = x + y; }
    function sub8(uint8 x, uint8 y) public { a8 = x - y; }
    function mul8(uint8 x, uint8 y) public { a8 = x * y; }
    function add64(uint64 x, uint64 y) public { a64 = x + y; }
    function sub64(uint64 x, uint64 y) public { a64 = x - y; }
    function mul64(uint64 x, uint64 y) public { a64 = x * y; }
    function add128(uint128 x, uint128 y) public { a128 = x + y; }
    function mul128(uint128 x, uint128 y) public { a128 = x * y; }
    function mul192(uint192 x, uint192 y) public { a192 = x * y; }      // the product can leave 256 bits
    function add248(uint248 x, uint248 y) public { a248 = x + y; }
    function mul248(uint248 x, uint248 y) public { a248 = x * y; }
    // wrapping arithmetic
    function uadd8(uint8 x, uint8 y) public { unchecked { a8 = x + y; } }
    function usub8(uint8 x, uint8 y) public { unchecked { a8 = x - y; } }
    function umul8(uint8 x, uint8 y) public { unchecked { a8 = x * y; } }
    function uadd64(uint64 x, uint64 y) public { unchecked { a64 = x + y; } }
    function usub64(uint64 x, uint64 y) public { unchecked { a64 = x - y; } }
    function umul64(uint64 x, uint64 y) public { unchecked { a64 = x * y; } }
    function umul128(uint128 x, uint128 y) public { unchecked { a128 = x * y; } }
    function umul192(uint192 x, uint192 y) public { unchecked { a192 = x * y; } }
    function usub248(uint248 x, uint248 y) public { unchecked { a248 = x - y; } }
    function uadd248(uint248 x, uint248 y) public { unchecked { a248 = x + y; } }
    // the arithmetic happens in the type of the expression, not of the target
    function wide(uint8 x, uint8 y) public { a256 = x + y; }              // overflows at 8 bits even though the target is wide
    function wideConv(uint8 x, uint8 y) public { a256 = uint256(x) + y; } // widening first: no overflow
    function mixed(uint8 x, uint64 y) public { a64 = x + y; }
    function mixed2(uint64 x, uint128 y) public { a128 = x * y; }
    function mixedSub(uint8 x, uint128 y) public { a128 = y - x; }
    function lit8(uint8 x) public { a8 = x + 200; }
    function lit8m(uint8 x) public { a8 = x * 3; }
    // division and remainder
    function dv8(uint8 x, uint8 y) public { a8 = x / y; }
    function md8(uint8 x, uint8 y) public { a8 = x % y; }
    function dv128(uint128 x, uint128 y) public { a128 = x / y; }
    // compound assignment and increments on narrow state and locals
    function inc8() public { a8++; }
    function dec8() public { a8--; }
    function addEq8(uint8 x) public { a8 += x; }
    function subEq8(uint8 x) public { a8 -= x; }
    function mulEq64(uint64 x) public { a64 *= x; }
    function uinc8() public { unchecked { a8++; } }
    function udec8() public { unchecked { a8--; } }
    function local8(uint8 x, uint8 y) public {
        uint8 t = x;
        t += y;
        a8 = t;
    }
    // explicit conversions
    function down8(uint256 x) public { a8 = uint8(x); }                  // truncates
    function down64(uint128 x) public { a64 = uint64(x); }
    function down192(uint256 x) public { a192 = uint192(x); }
    function up(uint8 x) public { a256 = uint256(x); }
    function upd(uint8 x) public { a64 = uint64(x) * 1000000000000; }
    function chain(uint256 x) public { a128 = uint128(uint8(x)) + 1; }
    // comparison across widths
    function lt8(uint8 x, uint8 y) public { b = x < y; }
    function ge8(uint8 x, uint8 y) public { b = x >= y; }
    function eqMixed(uint8 x, uint64 y) public { b = x == y; }
    function ltMixed(uint8 x, uint256 y) public { b = x < y; }
    // mappings with narrow keys or values
    function setM(address who, uint8 v) public { m8[who] = v; }
    function addM(address who, uint8 v) public { m8[who] += v; }
    function setK(uint8 k, uint64 v) public { k8[k] = v; }
    function addK(uint8 k, uint64 v) public { k8[k] += v; }
    // narrow loop counter
    function loop8(uint8 n) public {
        uint8 s = 0;
        for (uint8 i = 0; i < n; i++) { s += i; }
        a8 = s;
    }
    // argument range check happens even when the argument is not used
    function unused(uint8 x) public { a256 = 1; }
    function unusedPay(uint8 x) public payable { a256 = 2; }
}
