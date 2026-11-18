// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Arrays in storage: dynamic and fixed, of numbers, addresses, bools and bytes32, nested, in mappings and in structs; index, push, pop,
// length, delete, compound assignment, storage pointers. An index out of range and a pop of an empty array revert.
contract S_Arrays {
    uint256[] public xs;
    uint256[3] public fixedXs;
    address[] public owners;
    bool[] public flags;
    bytes32[] public hashes;
    uint8[] public small;
    uint256[][] public grid;
    uint256[2][] public pairs;
    mapping(address => uint256[]) public byUser;
    struct Item { uint256 id; uint256[] tags; }
    Item[] public items;
    uint256 public total;

    function push(uint256 v) external { xs.push(v); }
    function pushEmpty() external { xs.push(); }
    function pop() external { xs.pop(); }
    function len() external { total = xs.length; }
    function set(uint256 i, uint256 v) external { xs[i] = v; }
    function add(uint256 i, uint256 v) external { xs[i] += v; }
    function get(uint256 i) external { total = xs[i]; }
    function sum() external { uint256 s = 0; for (uint256 i = 0; i < xs.length; i++) { s += xs[i]; } total = s; }
    function clear() external { delete xs; }
    function clearAt(uint256 i) external { delete xs[i]; }
    function setFixed(uint256 i, uint256 v) external { fixedXs[i] = v; }
    function fixedLen() external { total = fixedXs.length; }
    function clearFixed() external { delete fixedXs; }
    function addOwner(address a) external { owners.push(a); }
    function isOwner(address a) external { bool found = false; for (uint256 i = 0; i < owners.length; i++) { if (owners[i] == a) { found = true; } } require(found); total += 1; }
    function pushFlag(bool b) external { flags.push(b); }
    function toggle(uint256 i) external { flags[i] = !flags[i]; }
    function pushHash(bytes32 h) external { hashes.push(h); }
    function pushSmall(uint8 v) external { small.push(v); }
    function addSmall(uint256 i, uint8 v) external { small[i] += v; }
    function pushRow() external { grid.push(); }
    function pushCell(uint256 r, uint256 v) external { grid[r].push(v); }
    function setCell(uint256 r, uint256 c, uint256 v) external { grid[r][c] = v; }
    function rowLen(uint256 r) external { total = grid[r].length; }
    function popCell(uint256 r) external { grid[r].pop(); }
    function pushPair() external { pairs.push(); }
    function setPair(uint256 i, uint256 j, uint256 v) external { pairs[i][j] = v; }
    function userPush(uint256 v) external { byUser[msg.sender].push(v); }
    function userGet(address a, uint256 i) external { total = byUser[a][i]; }
    function userLen(address a) external { total = byUser[a].length; }
    function userPop() external { byUser[msg.sender].pop(); }
    function newItem(uint256 id) external { items.push(); items[items.length - 1].id = id; }
    function tag(uint256 i, uint256 t) external { items[i].tags.push(t); }
    function tagLen(uint256 i) external { total = items[i].tags.length; }
    function dropItem(uint256 i) external { delete items[i]; }
    function viaPointer(uint256 r, uint256 v) external { uint256[] storage row = grid[r]; row[0] = v; total = row.length; }
}
