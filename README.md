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
- `Inheritance.ML`, `Inheritance_Bank.thy`, `Inheritance_Constructors.thy`, `Inheritance_Abstract.thy`: Inheritance for the `contract` and `verification` commands, with examples (see below).
- `document.pdf`: A pdf document containing all the formalizations.

## Inheritance

A contract can inherit from other contracts, as in Solidity:

```isabelle
contract Bank2 is Bank                      (* several bases: is A, B ("arg") *)
  for ...                                   (* own state variables *)
constructor
where "..."
cfunction f external where "..." ,          (* overrides f if a base has one *)
cfunction g abstract                        (* declared, not implemented *)
```

* **State and constructors.** The state variables of the bases come first (each once, most base-like first). The constructors run in
  this order: the parameters of all base constructors are bound (the nearest base first, so that the arguments given for a base may use the
  parameters of a nearer one), then the constructor bodies of the bases, most base-like first, then the body of the derived contract.
  Arguments for a base constructor are written in the inheritance list: `contract D is B ("<monadic expression>")`.
* **Methods.** An inherited method is an alias of the base's method, applied to the dispatcher of the derived contract composed with an
  injection of the base's calls. Calls are therefore virtual: a call of `f` in a base reaches the override in the derived contract.
  The linearisation is Solidity's (C3, the right-most base is the most derived); a method defined in unrelated bases has to be overridden.
* **`super`.** `icall super_f` in a method of the derived contract runs the definition of `f` of the nearest base; a base's own
  `super_f` reaches the next definition after it in the linearisation of the contract at hand. Only internal methods can be reached
  (the transpiler uses an internal twin `f__int` of a public function).
* **Abstract methods.** `cfunction f abstract` has no body (calling it reverts); a contract that inherits it should implement it.
* **Facts.** A derived contract notes `<base>_const` for every base (the base's locale holds in the derived contract's locale for a
  constant external function), needed to use the invariant rules of a base: `wprules: base.invI[OF base_const]`. This also works for
  bases that hash (`keccak256` is a parameter of the locale, injective by assumption) and for bases with an `assuming` clause, provided
  the derived contract assumes the same locale. (`contract C` itself notes a global `C_const` for the callee-free case.)

### Verification

`verification inv [m1 (pre, post) and m2 ...] for "D"` with the invariant `base.inv` of a base (`inv` alone is found in the locales of the bases).
The methods are listed only to give them pairs; a method that is not listed is verified like one that is listed without a pair:

* the obligation of an *inherited* method is that of the base and is proved automatically (from the facts `<base>_external.<m>_vc` that the
  `verification` of the base leaves);
* the pairs `(pre, post)` of the base are the defaults for the inherited methods (and for the hidden methods of super calls);
* an override without its own pair has to meet the base's pair (its obligation is the base's, to be proved by the user);
* an override with its own pair also gets the goal that its condition implies the base's (`vcond` of the derived contract for the method
  implies `base.vcond` for the base's method), so that the base's proofs about calls of the method remain valid;
* the user proves the constructor and the methods that are new or overridden.

**An invariant of its own.** A derived contract can also verify an invariant that its base never verified (about its own state
variables, say; a contract has one `verification`, so this is instead of the base's invariant). The obligations of the base cannot be
reused then. For an inherited method `verification` tries the proof of a method that leaves the invariant alone (unfold the alias and
the base's definition, weakest precondition, simplify the storage updates); what it proves is not shown as a goal. It does not prove
methods that call other methods and methods that change what the invariant looks at: they stay goals, as do the constructor and the new
and overridden methods (`Inheritance_Invariants.thy`).

### Limits

A derived contract that inherits from a base with an `assuming` clause has to assume the same locale (otherwise: "does not hold in this contract"); memory parameters (arrays, structs) of a base constructor are
not supported (strings and bytes are value parameters and work). The facts `vcond` are also available by name: `vcond_constructor` and `vcond_<method>` (the numbers `vcond(i)` depend on the position of the method, hidden methods of super calls included).

The implementation is in `Inheritance.ML`; examples and tests are in `Inheritance_Bank.thy`, `Inheritance_Constructors.thy` and
`Inheritance_Abstract.thy`, `Inheritance_Callee.thy` (bases that hash or assume a locale), `Inheritance_Invariants.thy` (invariants of derived contracts), `Inheritance_Errors.thy` (what is refused).

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
