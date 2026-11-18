// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// A modifier of a base constructor that a derived class overrides (Solidity resolves modifiers virtually, also those of constructors):
// the constructor of Ra runs with the modifier of Rb (Rc) or of Rq. The class that overrides the modifier gives the body for Ra's constructor.
abstract contract S_Ra {
    uint256 public a;
    uint256 public marker;
    uint256 public ini = 4;
    modifier guard(uint256 v) virtual { uint256 t = v + 1; marker = t; _; }
    constructor(uint256 x) guard(x) { a = x + ini; }
    function bump() public guard(1) { a += 1; }
}

abstract contract S_Rb is S_Ra {
    modifier guard(uint256 v) virtual override { uint256 t = v + 20; marker = t; _; }
}

contract S_Rc is S_Rb {
    uint256 public c;
    constructor() S_Ra(3) { c = marker; }
    function more() public { c += marker; }
}

contract S_Rq is S_Rb {
    modifier guard(uint256 v) override { marker = v * 100; _; }
    constructor() S_Ra(2) { }
}
