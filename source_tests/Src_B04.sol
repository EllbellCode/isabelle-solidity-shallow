// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// Benchmark 1, entry 04: an explicit base call A.f() skips the override in B; the call of hook() inside A.f is still dispatched to the most derived class.
contract S_EA {
    uint256 public log;
    function f() internal virtual { log = log * 10 + 1; hook(); }
    function hook() internal virtual { log = log * 10 + 5; }
}

contract S_EB is S_EA {
    function f() internal virtual override { log = log * 10 + 2; }
}

contract S_EC is S_EB {
    function viaA() public { S_EA.f(); log = log * 10 + 3; }
    function viaB() public { S_EB.f(); log = log * 10 + 4; }
    function hook() internal override { log = log * 10 + 7; }
}
