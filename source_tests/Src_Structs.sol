// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Structs in storage: a struct variable, a mapping to structs (default values of untouched entries), a nested struct, a mapping inside a
// struct, narrow and packed fields, storage pointers (also to nested structs and to entries of a mapping inside a struct), copies
// between storage places, fields as keys and in conditions.
struct Pos { address owner; uint256 amount; bool open; }

contract S_Structs {
    struct Inner { uint256 a; uint8 b; bool flag; }
    struct Outer { uint256 id; Inner inner; mapping(address => uint256) m; uint8 small; }

    Pos public p;
    mapping(uint256 => Pos) public book;
    Outer public o;
    mapping(address => Outer) public users;
    mapping(uint256 => uint256) public byAmount;
    uint256 public n;

    function f1(uint256 k) external { book[k].amount += 5; book[k].open = true; }
    function f2(uint256 k) external { Pos storage q = book[k]; q.owner = msg.sender; q.amount = q.amount + 1; }
    function f3() external { o.inner.a = 7; o.inner.b = 3; o.m[msg.sender] = 9; users[msg.sender].inner.a += 1; }
    function f4(uint256 k) external { n = book[k].amount; }
    function f5(uint256 k, uint256 j) external { book[k] = book[j]; }
    function f6() external { p.owner = msg.sender; p.amount = 100; p.open = !p.open; }
    function f7() external { Inner storage i = o.inner; i.a = 11; i.b += 1; i.flag = true; }
    function f8(address a) external { Outer storage u = users[a]; u.id = 5; u.m[msg.sender] += 2; u.small = 200; }
    function f9() external { o.small += 100; }
    function f10(uint256 k) external { require(book[k].open); book[k].open = false; }
    function f11(uint256 k) external { byAmount[book[k].amount] = k; }
    function f12(uint256 k) external { n = book[k].open ? book[k].amount : 1; }
    function f13(address a) external { users[a].inner = o.inner; }
    function f14(uint256 k) external { Pos storage q = book[k]; Pos storage r = book[k + 1]; r.amount = q.amount; q.amount = 0; }
}
