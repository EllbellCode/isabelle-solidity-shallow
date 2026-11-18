// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// break, continue and do-while, in all loop forms, nested, with state changes and reverts
contract S_Jumps {
    uint256 public total;
    uint256 public count;
    uint256 public last;
    mapping(address => uint256) public seen;

    function sumUntil(uint256 n, uint256 stop) external {
        require(n < 12);
        uint256 i = 0;
        while (i < n) {
            if (i == stop) { break; }
            total += i;
            i++;
        }
        last = i;
    }

    function skipEven(uint256 n) external {
        require(n < 12);
        for (uint256 i = 0; i < n; i++) {
            if (i % 2 == 0) { continue; }
            total += i;
            count++;
        }
    }

    function both(uint256 n, uint256 skip, uint256 stop) external {
        require(n < 12);
        for (uint256 i = 0; i < n; i++) {
            if (i == skip) { continue; }
            if (i == stop) { break; }
            total += 3;
            count += i;
        }
    }

    function doOnce(uint256 n) external {
        require(n < 12);
        uint256 i = n;
        do {
            total += 1;
            i++;
        } while (i < n);
        last = i;
    }

    function doCount(uint256 n) external {
        require(n < 12);
        uint256 i = 0;
        do {
            i += 2;
            total += i;
        } while (i < n);
        last = i;
    }

    function doJumps(uint256 n, uint256 skip, uint256 stop) external {
        require(n < 12);
        uint256 i = 0;
        do {
            i++;
            if (i == skip) { continue; }
            if (i == stop) { break; }
            count += i;
        } while (i < n);
        last = i;
    }

    function nested(uint256 a, uint256 b, uint256 stop) external {
        require(a < 6 && b < 6);
        for (uint256 i = 0; i < a; i++) {
            for (uint256 j = 0; j < b; j++) {
                if (j == stop) { break; }
                total += 1;
            }
            if (i == 2) { continue; }
            count += 10;
        }
    }

    function revertInLoop(uint256 n) external {
        require(n < 12);
        uint256 i = 0;
        while (true) {
            i++;
            if (i > n) { break; }
            require(i != 7, "seven");
            seen[msg.sender] += i;
        }
    }

    function afterBreak(uint256 n) external {
        uint256 i = 0;
        while (i < 10) {
            i++;
            { if (i >= n) { break; } }
            unchecked { total += i; }
            count += 1;
        }
    }
}
