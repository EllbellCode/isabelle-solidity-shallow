# Secure Smart Contracts with Isabelle/Solidity

This is a shallow embedding of [Solidity 0.8](https://docs.soliditylang.org/en/v0.8.0/) in [Isabelle/HOL](https://isabelle.in.tum.de/).

## Content

Isabelle/Solidity consists of the following theories:

- `Utils.thy`: A set of general functions and lemmas independent of Solidity.
- `State_Monad.thy`: A formalizaton of a state monad with exceptions and non-termination. It provides also a new mode sm for the partial function package.
- `Memory.thy`: A formalization of the Solidity memory model.
- `Stores.thy`: Integration of SMAC into Isabelle/Solidity.
- `State.thy`: A formalization of the Solidity storage model consisting of definitions for storage, memory, calldata, and stack. In addition it contains several useful functions for the different types of stores such as functions to read data structures from one store to another.
- `Solidity.thy`: A formalization of Solidity expressions and statements in terms of our state monad.
- `Contract.thy`: An Isabelle/ML implementation of two new commands: `contract` and `invariant` to support the specification of Solidity contracts and verification of invariants in Isabelle.
- `WP.thy`: A weakest precondition calculus and corresponding verification condition generator for our Solidity monads.
- `Mcalc.thy`: A formalisation of SMAC and corresponding soundness proof.
- `MTests.thy`: Examples for memory array verification.
- `Solidity_Main.thy`: Main entry point
- `Unit_tests.thy`: A test suite to validate conformance of the semantics to the original Solidity documentation. The test cases were executed using the [Remix IDE](https://remix.ethereum.org/).
- `Bank.thy`: Formalization of a banking contract.
- `Token.thy`: A formalization of a simple banking contract and verification of a key invariant using Isabelle/Solidity.
- `Casino.thy`: A formalization of a casino contract and verification of a key invariant using Isabelle/Solidity.
- `Voting.thy`: A formalization of a delegated voting contract and verification of a key invariant using Isabelle/Solidity.
- `SimpleAuction.thy`: A formalization of a simple auction contract.
- `Aliasing.thy`: The running example discussed in the paper.
- `ArrayBuilder.thy`: Verification of a contract using memory arrays/
- `document.pdf`: A pdf document containing all the formalizations.

## Prerequisites

The formalization requires [Isabelle 2025-2](https://isabelle.in.tum.de/).
Please follow the instructions on the Isabelle home page for your operating system.

In the following, we assume that the ``isabelle`` tool is available on the command line.
This might require to add the Isabelle binary directory to the ``PATH`` environment variable of your system.

## Using the Formalization

The formalization can be loaded into Isabelle/jEdit by executing 

```sh
isabelle jedit Solidity_Main.thy
```

on the command line. Alternatively, you can start Isabelle/jEdit by 
clicking on the Isabelle icon and loading the theory 
[Solidity_Main.thy](./Solidity_Main.thy) manually. 

To use a command line build that also generates a PDF document,
first add ``path/to/solidity`` to your Isabelle roots file which is
a file called ``ROOTS`` in your Isabelle home directory.
Then, the build can be started by executing:

```sh
isabelle build -D .
```
