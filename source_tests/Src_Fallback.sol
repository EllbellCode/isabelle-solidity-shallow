// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

// fallback(): reached by a call whose selector matches no function (and by an empty call if there is no receive()).
contract S_Fb {
    uint256 public hits;
    uint256 public last;
    fallback() external payable { hits += 1; last = msg.value; }
    function set(uint256 v) public { last = v; }
}

// both: an empty call reaches receive(), an unknown selector the fallback
contract S_Fr {
    uint256 public hits;
    uint256 public last;
    receive() external payable { last = 1; }
    fallback() external { hits += 1; last = 2; }
    function set(uint256 v) public { last = v; }
}

abstract contract S_FbBase {
    uint256 public hits;
    fallback() external virtual payable { hits += 1; }
}

contract S_FbDerived is S_FbBase {
    uint256 public extra;
    fallback() external override payable { hits += 10; extra += 1; }
    function bump() public { extra += 5; }
}
