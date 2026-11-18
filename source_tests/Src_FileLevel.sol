// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

uint256 constant LIMIT = 100;
uint8 constant SMALL = 7;
bytes32 constant TAG = keccak256("tag");

function twice(uint256 x) pure returns (uint256) {
    return x * 2;
}

function clamp(uint256 x, uint256 hi) pure returns (uint256) {
    if (x > hi) { return hi; }
    return x;
}

function plusSmall(uint256 x) pure returns (uint256) {
    return twice(x) + SMALL;
}

contract S_FileLevel {
    uint256 public total;
    uint8 public narrow;
    bytes32 public seen;

    function add(uint256 v) external {
        require(v <= LIMIT, "too big");
        total += v + SMALL;
    }

    function dbl(uint256 v) external { total = twice(v); }
    function cl(uint256 v, uint256 hi) external { total = clamp(v, hi); }
    function ps(uint256 v) external { total = plusSmall(v); }
    function nar(uint8 v) external { narrow = v + SMALL; }
    function tag() external { seen = TAG; }
}

contract S_Other {
    uint256 public x;
    function f(uint256 v) external { x = clamp(v, LIMIT); }
}
