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

## Extensions for generated code

`Solidity_Ext.thy` adds what the transpiler (`transpile.py`, in the transpiler repository) needs beyond the core theories: `address.balance`, `tx.origin` and
block constants as unconstrained values, the non-payable check `value_guard`, checked and wrapping arithmetic on narrow `uintN` and on signed `int256`
(`below_monad`, `sless_monad`, `sdiv_safe_monad`, `smod_monad`, ...), division and modulo with a zero-divisor revert, `pop` and `delete` of arrays,
and the monotonicity and `wp` rules for all of them. `Solidity_Main` does not import it: the rules it adds are not in the environment of hand-written
proofs unless they import `Solidity_Ext`. Generated theories import `Solidity.Solidity_Main` and `Solidity.Solidity_Ext`.

## Contracts as Solidity source text

The command `solidity` takes Solidity source text and creates its contracts like the `contract` command does:

```isabelle
solidity \<open>
contract Bank {
    mapping(address => uint) balances;

    function deposit() external payable { balances[msg.sender] += msg.value; }
    function reset() internal { balances[msg.sender] = 0; }
    function withdraw() external {
        uint bal = balances[msg.sender];
        reset();
        payable(msg.sender).transfer(bal);
    }
}
\<close>
```

The text is read by `Solidity_Source.ML` (lexer, parser, type-directed elaborator) into the data of the `contract` command: state variables,
constructor and methods with their bodies as monadic terms, `contract D is B (args)` for inheritance. The rules of the translation are those
of the transpiler `transpile.py` of the surrounding project (which gets the types from `solc`); `source_diff/diff.py` there compares the two
term by term on a corpus of Solidity files, and the theories `source_tests/Src_*.thy` do so inside this session, against reference
specifications (the output of the transpiler, committed with the tests, so that `solc` is not needed to check them).
The `invariant` and `verification` commands work on the result unchanged.

**Supported.** The types `uint8` ... `uint256` (the range is kept as in `Solidity_Ext`, "Narrow unsigned integers"), `int256` (two's
complement, signed operators), `address` (payable), `bool`, `bytesN`, `string`, `bytes`, mappings, structs, arrays (`push`, `pop`, `.length`,
`delete`, storage pointers), contract and interface types (a value is the address). State variables with an initial value, `constant`,
`immutable`; constructor and functions (`external`/`public`, `internal`/`private`, `payable`, `view`/`pure`, `virtual`/`override`),
`receive` and `fallback`; parameters, locals, return values (tail `return`, guard clauses, named results) and internal calls with arguments;
the operators `+ - * / % ** & | ^ ~ << >> && || ! ?:` and comparisons (checked as in Solidity 0.8, `unchecked { }` for wrapping),
assignments (also as values), `++`, `--`, `delete`; `if`, `while`, `for`, `do`-`while`, `break`, `continue` (flags that are locals of the function:
`_brk<k>`, `_cnt<k>`, `_first<k>`, so that the loop is still one `while_monad`); enums (a `uint8` that stays below the number of members: `E.A` is
the number, `E(x)` reverts unless `x` is below it, so does an external argument; enums at file or contract level) and user-defined value types
(`type T is uint256`, `T.wrap`/`T.unwrap` are the identity); constants and functions outside of any contract (copied into each contract that mentions
them, a free function becomes an internal function); `require`/`assert`/`revert` (a message is a string literal or a
variable that holds one), `emit` (arguments are evaluated), `address.transfer` and the pattern `(bool ok, ) = a.call{value: v}(""); ...;
require(ok);`; `msg.sender`, `msg.value`, `block.timestamp`, `block.number`, `block.chainid`, `tx.origin`, `address(x).balance`, `this`,
`type(T).max`/`min`, `type(I).interfaceId`, number literals with units (`1 ether`); `keccak256` (of a byte string, of `abi.encode`/
`abi.encodePacked` of several values) and `ecrecover`.

**Inheritance.** Bases, base-constructor arguments (in the `is` list or the modifier list of the constructor, also for indirect bases), `super`,
explicit base calls `A.f()`, abstract contracts and functions, overloaded functions (named after their parameter types), virtual modifiers
(a derived class that overrides a modifier gives its constructor body for the base), modifiers of bases, library functions
(`using L for T`, `L.f(x)`: internal ones are copied into the contract as `L__f`), interfaces.

**Calls to other contracts.** `t.f(args)` on a value of contract or interface type is a call to code that is not modelled, as for the
transpiler (`Solidity_Ext`, "Calls to other contracts"); the natspec lines `/// @custom:assume norevert|constant|min N|max N|nocallback` on the
called function become the assumptions of a generated locale `<C>_Callee` that the contract imports.

**Modifiers.** `modifier m(uint k) { require(...); _; ... }` is inserted at every use, as `transpile.py --inherit` does (the parameters and
variables of the modifier get unique names `_m<k>_<name>`). With `declare [[solidity_modifier_abbreviations = true]]` each use is a locale
abbreviation `mod_<Class>_<name>` instead (`mod_Vault_onlyOwner (body)`): the elaborated definitions are the same terms, so proofs are
unchanged, but they print short.

**What it creates.** For every contract the command writes, as a message of the command (the output panel of the IDE, the place where `value`
or `thm` write), the text of the `contract` command that it hands to the framework: the state variables with their types, the constructor and
each method with its body as a monadic term, in the form that `transpile.py` writes. That is the contract under the hood; pasting it into a
theory gives the same contract. `declare [[solidity_show = false]]` switches the message off.

**Options.** `[[solidity_value_guard]]` (default true): a function or constructor that is not payable starts with `value_guard` (Solidity
reverts when `msg.value > 0`; needs `Solidity_Ext`); the hand-written specifications do not have it, set it to false to get their terms.
`[[solidity_abbreviations]]` (default false): `abbreviation balances \<equiv> STR ''balances''` for the state variables, as in the hand-written
specifications. `[[solidity_modifier_abbreviations]]` (default false), see above.

**Refused** (with line and column): the narrow signed types, `new`, inline assembly, tuple declarations other than the call pattern above, events with non-trivial arguments are evaluated but not logged, structs and
arrays in memory or as parameters, `abi.encodeWithSelector` and the other `abi` functions, `this.f()`, call options other than `value`,
library functions that are not internal, `import` (put the contracts in one text), `try`/`catch`, multiple return values, `bytes` `.length`/index and
`string.concat` (the framework has no operation on the length of a byte string). The semantics are the framework's. What is still missing needs a
change of the framework (a new kind of value or a new operation with its proof rules), not of the command; see the list in the project notes.

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
* **Initialisers.** A constructor may have an `initialiser` (between its parameters and `where`): the state variable initialisers of the legacy
  pipeline of solc, which runs the initialisers of the whole hierarchy before the first constructor. With initialisers in the hierarchy the
  order is: the initialisers of all the contracts (most base-like first), then the parameters of the base constructors are bound, then the
  bodies as above. An initialiser that reads what a base constructor writes sees the initial value, as in Solidity's default pipeline. Without
  an `initialiser` anywhere nothing changes: a class at a time, which is the order of the via-IR pipeline (put its initialisers in the body of
  the constructor). Example and test: `Inheritance_Constructors.thy`.
* **Replacing the constructor of a base.** Solidity resolves the modifiers of a constructor virtually: if a derived contract overrides a modifier
  that the constructor of a base uses, that constructor runs with the new modifier. The derived contract gives the body for it: in its
  `constructor` (after the `initialiser`, before `where`) `replacing B "<body>"`; a contract derived from it takes the replacement too, unless it
  replaces the body again. The parameters of B's constructor are bound as before. Test: `Inheritance_Constructors.thy`.
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
variables, say; this is a further `verification` of the derived contract, see below). The obligations of the base cannot be
reused then. For an inherited method `verification` tries the proof of a method that leaves the invariant alone (unfold the alias and
the base's definition, weakest precondition, simplify the storage updates, and for methods that update maps the typing of the maps taken
apart); what it proves is not shown as a goal. Methods that change what the invariant looks at stay goals, as do the constructor and the
new and overridden methods (`Inheritance_Invariants.thy`).

**Inherited methods that call internal methods.** Inside a `verification` an internal method without a pair is known only as "anything",
so an inherited method that calls one cannot be proved from the base alone. With `declare [[verification_frame_calls = true]]` (off by
default: it changes the conditions `vcond` and the goals of such verifications) the verification of an invariant that the base did not
verify gives the internal methods that the inherited methods call (directly or through each other) the pair "if the invariant holds before
the call it holds after". The obligation of such a method is the one of a method that leaves the invariant alone (proved automatically when
it does, a goal for the user when it does not, and then the verification cannot be completed unless the method really preserves the
invariant), and the inherited methods that call them are proved by stepping over the calls with the pair (`wp_call_inv` in `WP.thy`): the
invariant has to hold before each call (it is found from the premises), the rest of the body starts in a state where it holds. A further
derived contract that verifies the same invariant takes over the pairs. A pair the user gives for such a method is kept. Test:
`Inheritance_Calls.thy`.

**Methods that call methods, and revert conditions.** The condition `vcond` of a verification carries, for every method with a pair, its
postcondition and, if the pair has a revert condition `rv`, also "does not revert if `rv` is false" and "reverts if `rv` is true". What a caller
knows about a call of an internal method is therefore exactly its pair, and a caller's own revert condition can be exact in both directions.
`verification` generates for every internal method with a pair, a precondition and a revert condition a rule `wpc_<method>`
(with the suffix of the verification, like `vcond_<m>`): after `vcg_all` has stopped at `wp (call M_m ..)`, `rule_tac call=call in wpc_<method>` steps over
the call; the goals that remain are the precondition, what follows from the postcondition when the call does not revert, and what follows when it does.
(The rule is not a `wprule`: its conclusion would unify with any `wp` goal.) A pair of an inherited internal method has to say what the method leaves
alone (a frame condition), because the derived contract has variables the base does not know. Test: `Verification_Calls.thy`.

**Several verifications of one contract.** A contract can verify several invariants, one `verification` each. The first keeps the names
`vcond`, `vcond_<m>`, `<c>_external`; a further one adds `_<name of the verification>` to them (`vcond_owner_typed_v`). A derived contract that
verifies an invariant which one of the verifications of its base verified reuses the proofs of that verification. A pair (`pre`, `post`, `rv`)
may use the invariant of another verification as its precondition: the derived `ERC20` example (`gen_inherit/ERC20_Split_Gen.thy` in the
transpiler repository) proves the postconditions and revert conditions of `mint` and `burn` for a precondition that is the invariant
`owner_typed` of the derived contract, verified by a second `verification`. `invariant` and `verification` may be written in a later theory than
the `contract` command.

### Limits

A derived contract that inherits from a base with an `assuming` clause has to assume the same locale (otherwise: "does not hold in this contract"); memory parameters (arrays, structs) of a base constructor are
not supported (strings and bytes are value parameters and work). The facts `vcond` are also available by name: `vcond_constructor` and `vcond_<method>` (the numbers `vcond(i)` depend on the position of the method, hidden methods of super calls included).

The implementation is in `Inheritance.ML`; examples and tests are in `Inheritance_Bank.thy`, `Inheritance_Constructors.thy` and
`Inheritance_Abstract.thy`, `Inheritance_Callee.thy` (bases that hash or assume a locale), `Inheritance_Invariants.thy` (invariants of derived contracts), `Inheritance_Calls.thy` (inherited methods that call internal methods), `Inheritance_Errors.thy` (what is refused).

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
