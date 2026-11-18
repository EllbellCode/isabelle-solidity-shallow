// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Bitwise operators, shifts and exponentiation on unsigned and signed integers, narrow types (truncation of `~` and `<<`), checked and
// unchecked `**`, shift amounts of 256 and more, and the compound forms.
contract S_Bits {
    uint256 public x;
    uint8 public small;
    uint128 public mid;
    int256 public s;

    function b1(uint256 a, uint256 b) external { x = a & b; }
    function b2(uint256 a, uint256 b) external { x = a | b; }
    function b3(uint256 a, uint256 b) external { x = a ^ b; }
    function b4(uint256 a) external { x = ~a; }
    function b5(uint256 a, uint256 n) external { x = a << n; }
    function b6(uint256 a, uint256 n) external { x = a >> n; }
    function b7(int256 a, uint256 n) external { s = a >> n; }
    function b8(int256 a, int256 b) external { s = a & b; }
    function b9(int256 a) external { s = ~a; }
    function b10(int256 a, uint256 n) external { s = a << n; }
    function n1(uint8 a) external { small = ~a; }
    function n2(uint8 a, uint256 n) external { small = a << n; }
    function n3(uint8 a, uint8 b) external { small = a ^ b; }
    function n4(uint128 a, uint256 n) external { mid = a << n; }
    function n5(uint8 a, uint256 n) external { small = a >> n; }
    function e1(uint256 a, uint256 b) external { x = a ** b; }
    function e2(uint8 a, uint8 b) external { small = a ** b; }
    function e3(uint256 a, uint256 b) external { unchecked { x = a ** b; } }
    function e4(uint8 a, uint8 b) external { unchecked { small = a ** b; } }
    function e5(uint256 b) external { x = 10 ** b; }
    function e6() external { x = 2 ** 255; }
    function c1(uint256 a) external { x &= a; }
    function c2(uint256 a) external { x |= a; }
    function c3(uint256 a) external { x ^= a; }
    function c4(uint256 n) external { x <<= n; }
    function c5(uint256 n) external { x >>= n; }
    function c7(uint8 a) external { small ^= a; small <<= 1; }
    function k1() external { x = type(uint256).max ^ (1 << 255); }
    function k2(uint256 a) external { x = (a & 0xff) << 8 | (a >> 8) & 0xff; }
}
