theory Solidity_Source_Tests
  imports Bank Solidity_Ext
begin

section \<open>The command \<open>solidity\<close>: contracts written as Solidity source text\<close>

text \<open>
  Bank as Solidity text. The elaborated definitions are compared, as terms, with those of the hand-written contract \<open>Bank\<close>
  (\<open>Bank.thy\<close>), after renaming the constants of the one locale to those of the other.
\<close>

text \<open>
  The hand-written specifications do not check \<open>msg.value\<close> in functions that are not payable, the command does by default (\<open>value_guard\<close>, as Solidity does):
  to compare with them the check is switched off.
\<close>

declare [[solidity_value_guard = false]]

solidity \<open>
contract SBank {
    mapping(address => uint) balances;

    function deposit() external payable {
        balances[msg.sender] += msg.value;
    }

    function reset() internal {
        balances[msg.sender] = 0;
    }

    function withdraw() external {
        uint bal = balances[msg.sender];
        reset();
        payable(msg.sender).transfer(bal);
    }
}
\<close>

declare [[solidity_value_guard = true]]

ML \<open>
  structure Source_Equiv =
  struct
    fun rename (gen, hand) =
      let
        val rn = fn s => if String.isPrefix gen s then hand ^ unprefix gen s else s
        fun typ (Type (c, Ts)) = Type (rn c, map typ Ts)
          | typ T = T
        fun trm (Const (c, T)) = Const (rn c, typ T)
          | trm (Free (x, T)) = Free (x, typ T)
          | trm (Var (x, T)) = Var (x, typ T)
          | trm (Abs (x, T, b)) = Abs (x, typ T, trm b)
          | trm (t $ u) = trm t $ trm u
          | trm t = t
      in trm end

    (*`decl T x` is by definition `init (default T) x`: unfold it, so that the surface choice between the two does not count*)
    fun norm thy =
      Raw_Simplifier.rewrite_term thy
        (map (Local_Defs.meta_rewrite_rule (Proof_Context.init_global thy))
          (@{thm decl_def} :: @{thm comp_def} :: @{thms default.simps})) []

    (*the definition theorems of the methods of two contracts (locale prefixes), compared as terms*)
    fun compare thy (gen, hand) names =
      let
        val ren = rename (gen, hand)
        fun get pre n = Global_Theory.get_thm thy (pre ^ "." ^ n ^ "_def") |> Thm.prop_of
        fun one n = (n, norm thy (get hand n) aconv norm thy (ren (get gen n)), get hand n, ren (get gen n))
      in map one names end

    fun check thy pair names =
      let val bad = filter_out (fn (_, ok, _, _) => ok) (compare thy pair names)
      in
        if null bad then ()
        else error ("different from the hand-written definition: " ^ commas (map #1 bad) ^ "\n" ^
                    cat_lines (map (fn (n, _, a, b) => n ^ "\n  hand-written: " ^ Syntax.string_of_term_global thy a ^ "\n  from source:  " ^ Syntax.string_of_term_global thy b) bad))
      end
  end
\<close>

ML \<open>
  Source_Equiv.check \<^theory> ("Solidity_Source_Tests.sBank", "Bank.bank") ["constructor", "deposit", "reset", "withdraw"]
\<close>

subsection \<open>Refusals and error messages\<close>

text \<open>
  What the command does not support is refused with a message and the position in the text (line and column), and nothing is created.
\<close>

ML \<open>
  fun failure thy text =
    let
      val trs = Outer_Syntax.parse_text thy (K thy) Position.start text
      val result = Exn.capture (fn () => fold (Toplevel.command_exception false) trs (Toplevel.make_state (SOME thy))) ()
    in (case result of Exn.Res _ => NONE | Exn.Exn e => SOME (Runtime.exn_message e)) end;

  fun expect_failure thy text fragment =
    (case failure thy text of
       NONE => error ("expected an error containing: " ^ fragment)
     | SOME msg => if String.isSubstring fragment msg then () else error ("wrong error: " ^ msg ^ "\nexpected: " ^ fragment));

  fun refused src fragment = expect_failure \<^theory> ("solidity \<open>" ^ src ^ "\<close>") fragment;

  val _ = refused "contract A { uint x; function f() external { break; } }" "break outside of a loop";
  val _ = refused "contract A { uint x; function f() external { while (x < 3) { x++; } continue; } }" "continue outside of a loop";
  val _ = refused "contract A { enum E { P, Q } uint x; function f() external { x = E.R; } }" "the enum has no member";
  val _ = refused "contract A { enum E { P, Q } function f(int a) external { E e = E(a); } }" "a conversion of a signed integer to an enum";
  val _ = refused "contract A { int8 x; }" "the narrow signed integer types are not supported";
  val _ = refused "contract A { uint x; function f() external { y = 1; } }" "unknown name \"y\"";
  val _ = refused "contract A { uint x; function f() external { x = 1 } }" "expected \";\", found \"}\"";
  val _ = refused "contract A { mapping(address => uint) m; function f() external { m = 1; } }" "the mapping \"m\" is assigned without an index";
  val _ = refused "contract A { uint x; function f() external { uint x = 1; } }" "shadows a state variable";
  val _ = refused "contract A { uint x; function f() external m { x = 1; } }" "unknown modifier \"m\"";
  val _ = refused "contract A { uint x; modifier m(uint k) { _; } function f() external m { x = 1; } }" "takes 1 argument";
  val _ = refused "contract A { uint x; function f() external { _; } }" "only valid in a modifier";
  val _ = refused "contract A { uint x; modifier m() { _; } modifier m() { _; } function f() external m { x = 1; } }" "is declared twice";
  val _ = refused "contract A { uint x; function f() external { x = new A(); } }" "new is not supported";
  val _ = refused "contract A { uint x; function f() external { require(x > 0, x + 1); } }" "only a string literal";
  val _ = refused "contract A { uint x; function f() external { (uint a, uint b) = (1, 2); } }" "a tuple declaration is not supported";
  val _ = refused "contract A { uint x; function f() external { assembly { x := 1 } } }" "inline assembly is not supported";
  val _ = refused "contract A { uint x; function f() public { f(); } }" "recursive internal calls";
\<close>

end
