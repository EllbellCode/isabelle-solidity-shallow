// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// A constructor and state-variable initialisers that call internal methods (with arguments and return values), as the ERC20
// constructors of OpenZeppelin-style contracts do (`_mint`, `_setOwner`).
contract S_CtorCalls {
    address public owner;
    uint256 public total;
    uint256 public base = scale(3);
    mapping(address => uint256) public bal;

    function setOwner(address o) internal { owner = o; }
    function scale(uint256 v) internal pure returns (uint256) { return v * 10; }
    function mint(address to, uint256 v) internal { total += v; bal[to] += v; }
    function checked(uint256 v) internal returns (uint256) { require(v < 1000); return v; }

    constructor(uint256 supply, address first) {
        setOwner(msg.sender);
        mint(msg.sender, scale(supply));
        mint(first, checked(supply));
    }

    function again(uint256 v) external { mint(msg.sender, v); }
    function transferOwner(address o) external { require(msg.sender == owner); setOwner(o); }
}
