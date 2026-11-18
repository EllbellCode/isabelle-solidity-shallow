// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// keccak256 with abi.encode / abi.encodePacked / a byte string. The model's hash is an injective function, not Keccak, so the
// harness compares which of the observed bytes32 cells are equal (and which are zero), not their values.
contract S_Hash {
    bytes32 public h1;
    bytes32 public h2;
    bytes32 public h3;
    bytes32 public hs;
    bytes32 public hs2;
    bytes32 public hs3;
    bytes32 public hl;
    bytes32 public hl2;
    mapping(address => bytes32) public commitment;
    mapping(bytes32 => bool) public seen;
    mapping(bytes32 => uint256) public count;
    uint256 public n;
    // a 32-byte literal: solc abbreviates the type string of a number this long
    bytes32 constant TYPEHASH = 0x7c7c6cdb67a18743f49ec6fa9b35f50d52ed05cbed4cc592e13b44501c1a2267;

    // order and arity matter
    function enc2(uint256 a, uint256 b) external { h1 = keccak256(abi.encode(a, b)); h2 = keccak256(abi.encode(b, a)); }
    function enc1(uint256 a) external { h3 = keccak256(abi.encode(a)); }
    function enc3(uint256 a, uint256 b, uint256 c) external { h1 = keccak256(abi.encode(a, b, c)); h2 = keccak256(abi.encode(a, b)); }
    // packed of word-sized values coincides with abi.encode (32-byte words)
    function packed(uint256 a, uint256 b) external { h1 = keccak256(abi.encodePacked(a, b)); h2 = keccak256(abi.encode(a, b)); }
    function mixed(address who, bool flag, uint256 v) external { h1 = keccak256(abi.encode(who, flag, v)); h2 = keccak256(abi.encode(msg.sender, flag, v)); }
    function narrow(uint8 a, uint8 b) external { h1 = keccak256(abi.encodePacked(a, b)); h2 = keccak256(abi.encode(a, b)); h3 = keccak256(abi.encodePacked(b, a)); }
    function viaSender(uint256 v) external { h3 = keccak256(abi.encodePacked(msg.sender, v)); }
    // byte strings: hashed directly, packed alone, and encoded
    function str(string memory s) external { hs = keccak256(bytes(s)); hs2 = keccak256(abi.encodePacked(s)); hs3 = keccak256(abi.encode(s)); }
    function bytesArg(bytes memory b) external { hs = keccak256(b); hs3 = keccak256(abi.encode(b, b)); }
    function strPlus(string memory s, uint256 k) external { hs2 = keccak256(abi.encodePacked(s, k)); hs3 = keccak256(abi.encode(s, k)); }
    function two(string memory a, string memory b) external { hs = keccak256(abi.encode(a, b)); hs2 = keccak256(abi.encode(b, a)); }
    // literals
    function lit() external { hl = keccak256("abc"); hl2 = keccak256(abi.encodePacked("abc")); }
    function litOther() external { hl2 = keccak256("abd"); }
    function litEq() external { require(hl == keccak256(bytes("abc"))); n += 1; }
    // equality of hashes drives control flow
    function same(uint256 a, uint256 b) external { require(keccak256(abi.encode(a)) == keccak256(abi.encode(b))); n += 1; }
    function differ(uint256 a, uint256 b) external { require(keccak256(abi.encode(a, 1)) != keccak256(abi.encode(b, 1))); n += 1; }
    function sameStr(string memory a, string memory b) external { require(keccak256(bytes(a)) == keccak256(bytes(b))); n += 1; }
    function typed(uint256 a) external { h3 = keccak256(abi.encode(TYPEHASH, a)); h2 = TYPEHASH; }
    function typedEq(uint256 a) external { require(h3 == keccak256(abi.encode(TYPEHASH, a))); n += 1; }
    // commit / reveal
    function commit(uint256 secret) external { commitment[msg.sender] = keccak256(abi.encodePacked(secret, msg.sender)); }
    function reveal(uint256 secret) external { require(commitment[msg.sender] == keccak256(abi.encodePacked(secret, msg.sender))); n += 1; commitment[msg.sender] = bytes32(0); }
    // hashes as keys
    function mark(uint256 a) external { seen[keccak256(abi.encode(a))] = true; }
    function check(uint256 b) external { require(seen[keccak256(abi.encode(b))]); n += 1; }
    function bump(string memory k) external { count[keccak256(bytes(k))] += 1; }
    function need(string memory k, uint256 atLeast) external { require(count[keccak256(bytes(k))] >= atLeast); n += 1; }
}
