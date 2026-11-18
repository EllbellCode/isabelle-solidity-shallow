// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

enum Level { Low, Mid, High }
type Price is uint256;
type Tag is bytes32;

contract S_Enums {
    enum State { Idle, Running, Done, Failed }

    State public state;
    Level public level;
    mapping(address => State) public stateOf;
    mapping(State => uint256) public counts;
    Price public price;
    Tag public tag;
    uint256 public steps;

    struct Job { State st; Level lv; uint256 n; }
    Job public job;

    function start() external {
        require(state == State.Idle, "not idle");
        state = State.Running;
        stateOf[msg.sender] = State.Running;
        counts[State.Running] += 1;
    }

    function finish(bool ok) external {
        require(state == State.Running);
        state = ok ? State.Done : State.Failed;
        counts[state] += 1;
    }

    function setLevel(Level l) external {
        level = l;
        if (l == Level.High) { steps += 10; } else if (l >= Level.Mid) { steps += 5; }
    }

    function setState(State s) external { state = s; stateOf[msg.sender] = s; }

    function fromNumber(uint256 x) external { state = State(x); }

    function toNumber() external { steps = uint256(state) * 100 + uint8(level); }

    function levelFromNumber(uint8 x) external { level = Level(x); job.lv = level; job.st = State.Done; job.n = x; }

    function setPrice(uint256 p) external { price = Price.wrap(p); }
    function bump() external { price = Price.wrap(Price.unwrap(price) + 1); }
    function setTag(bytes32 t) external { tag = Tag.wrap(t); }
    function tagIs(bytes32 t) external { require(Tag.unwrap(tag) == t); steps += 1; }

    function reset() external {
        delete state;
        steps = 0;
        job.st = State.Idle;
    }
}
