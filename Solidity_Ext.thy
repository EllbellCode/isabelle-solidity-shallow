theory Solidity_Ext
  imports Solidity_Main
begin

text \<open>
  Extensions needed by the transpiler (\<open>transpile.py\<close>) and the SmartBugs benchmark: constructs of Solidity that the core theories do not express.
  Each is used by generated theories only when the Solidity source needs it. This theory is not imported by \<open>Solidity_Main\<close>: the rules it adds
  (\<open>wprules\<close>, \<open>wpsimps\<close>, monotonicity rules) are not in the environment of hand-written proofs and of the framework's own theories unless they import it.
  Generated theories import \<open>Solidity.Solidity_Ext\<close> besides \<open>Solidity.Solidity_Main\<close>.
\<close>

section \<open>Ether balance of an address: \<open>addr.balance\<close>\<close>

text \<open>
  The framework keeps balances as naturals (\<open>Balances s a\<close>) and has no expression for reading them.
  Modelling assumption inherited from the framework: balances are never reduced modulo 2^256 (the
  total supply of ether is far below 2^256), so \<open>word_of_nat\<close> does not wrap in any reachable state.
\<close>

definition balance_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "balance_monad am =
    do {
      a \<leftarrow> am;
      av \<leftarrow> readValue a;
      ad \<leftarrow> readAddress av;
      s \<leftarrow> get;
      return (kdSint (word_of_nat (Balances s ad)))
    }"

lemma wp_balance_monad[wprules]:
  assumes "wp am
     (\<lambda>a. wp (readValue a \<bind>
               (\<lambda>av. readAddress av \<bind>
                      (\<lambda>ad. get \<bind>
                             (\<lambda>s. return (kdSint (word_of_nat (Balances s ad)))))))
            P E)
     E s"
  shows "wp (balance_monad am) P E s"
  unfolding balance_monad_def apply (rule wprules)+ by (rule assms)


section \<open>Weakest-precondition rules for the new constructs\<close>

lemma (in Contract) wp_this_monad[wprules]:
  assumes "P (kdAddress this) s"
  shows "wp this_monad P E s"
  unfolding this_monad_def address_monad_def using assms by (simp add: wprules)

lemma wp_readValue_plain[wprules]:
  assumes "P v s"
  shows "wp (readValue (rvalue.Value v)) P E s"
  unfolding wp_def readValue.simps by (simp add: execute_return assms)

section \<open>Word arithmetic helpers (as naturals)\<close>

lemma unat_add_imp:
  assumes "unat (x::256 word) + unat y < 2^256"
    shows "unat (x + y) = unat x + unat y"
  using assms Word.unat_add_lem[where ?'a=256, of x y] by simp

lemma unat_sub_imp:
  assumes "(y::256 word) \<le> x"
    shows "unat (x - y) = unat x - unat y"
  using assms Word.unat_sub[where ?'a=256, of y x] by simp

text \<open>Moving v from one balance to another conserves the sum of the balances (as naturals).\<close>
lemma word_transfer_conserves:
  fixes si sib v :: "256 word"
  assumes "v \<le> si" and "unat sib + unat v < 2^256"
    shows "unat (si - v) + unat (sib + v) = unat si + unat sib"
proof -
  have "unat v \<le> unat si" using assms(1) by (simp add: word_le_nat_alt)
  then show ?thesis using unat_sub_imp[OF assms(1)] unat_add_imp[OF assms(2)] by simp
qed

section \<open>Transaction origin: \<open>tx.origin\<close>\<close>

text \<open>
  The framework has no notion of the account that started the transaction. \<open>tx_origin\<close> is a fixed
  but unspecified address (Hilbert's \<open>undefined\<close>): nothing relates it to \<open>msg_sender\<close>, so every
  proof that mentions it holds for every possible origin (sound, conservative). A kill witness must
  state which relation between origin and sender it needs (e.g. \<open>msg_sender \<noteq> tx_origin\<close>, the phishing case).
\<close>

definition tx_origin::"'a::address" where
  "tx_origin = undefined"

definition tx_origin_monad::"('a::address) expression_monad" where
  "tx_origin_monad = address_monad tx_origin"

lemma wp_tx_origin_monad[wprules]:
  assumes "P (kdAddress tx_origin) s"
  shows "wp tx_origin_monad P E s"
  unfolding tx_origin_monad_def address_monad_def using assms by (simp add: wprules)

section \<open>Address equality in guards\<close>

lemma kdequals_addr_dest:
  assumes "kdequals (rvalue.Value (Address a)) (rvalue.Value (Address b)) = Some y"
      and "kdequals y (rvalue.Value (Bool True)) = Some (rvalue.Value (Bool True))"
    shows "a = b"
  using assms by (auto simp: kdequals_def)

section \<open>Concrete environments for kill witnesses\<close>

text \<open>
  The framework's \<open>external\<close> is a locale parameter constrained only by monotonicity. A witness fixes one
  environment; these lemmas show the environments used are legitimate (monotone), so the witness is not
  vacuous.
\<close>

lemma environment_does_nothing_mono:
  "mono_sm (\<lambda>c::'d \<Rightarrow> ('a::address expression_monad). (return Empty :: 'a expression_monad))"
  by (simp add: mono)

section \<open>Destructors for guards (as in the framework's Casino example, here for all contracts)\<close>

lemma kdequals_true_dest:
  assumes "kdequals a b = Some (rvalue.Value (Bool True))"
  shows "a = b"
  using assms
  apply (cases a; simp add: kdequals_def)
  apply (cases b; simp add: kdequals_def)
  by (case_tac x4; case_tac x4a; simp add: kdequals_def split: if_split_asm)

lemma kdnot_dest:
  assumes "kdnot ya = Some (rvalue.Value (Bool True))"
  shows "ya = rvalue.Value (Bool False)"
  using assms apply (cases ya; simp add: kdnot_def)
  by (case_tac x4; simp add: vtnot_def)

lemma kdless_false_dest:
  assumes "kdless (rvalue.Value (Uint x)) (rvalue.Value (Uint y)) = Some (rvalue.Value (Bool False))"
  shows "\<not> x < y"
  using assms by (simp add: kdless_def vtless_def)

lemma kdless_true_dest:
  assumes "kdless (rvalue.Value (Uint x)) (rvalue.Value (Uint y)) = Some (rvalue.Value (Bool True))"
  shows "x < y"
  using assms by (simp add: kdless_def vtless_def)

section \<open>The callvalue guard of non-payable entry points\<close>

text \<open>
  transpile.py starts every non-payable external/public function and constructor with
  @{text "value_guard"} = @{text "assert_monad (equals_monad value_monad (sint_monad 0))"} (Solidity reverts when ether is sent to
  such a function; the framework's \<open>init_balance_np\<close> ignores msg.value). This rule decomposes the guard in
  one step: it passes when \<open>msg_value = 0\<close> and raises \<open>Err\<close> otherwise. Declared after the framework's rules,
  so \<open>vcg\<close> tries it before the generic \<open>wp_assert_monad\<close>.
\<close>

definition (in Method) value_guard :: "('a::address) expression_monad" where
  "value_guard = assert_monad (equals_monad value_monad (sint_monad 0))"

text \<open>
  A constant of its own (not just the term it abbreviates), so that this rule is the only one that applies:
  with the plain term, the framework's generic \<open>wp_assert_monad\<close> is tried first and the guard is
  expanded into its \<open>kdequals\<close> bookkeeping.
\<close>

lemma (in Method) wp_value_guard[wprules]:
  assumes "msg_value = 0 \<Longrightarrow> P Empty s" and "msg_value \<noteq> 0 \<Longrightarrow> E Err s"
  shows "wp value_guard P E s"
  unfolding value_guard_def
  apply vcg
  using assms by (auto simp add: kdequals_def kdSint_def kdbool_def wp_def execute_simps)


text \<open>
  For concrete executions (kill witnesses): the guard evaluated, stated for \<open>sint_monad\<close> (the unfolding of
  \<open>value_monad\<close> in a contract locale), so that it can be passed to \<open>simp\<close> as an instance
  \<open>execute_sint_guard_normal[OF assms]\<close> without rewriting the locale parameter \<open>msg_value\<close> itself.
\<close>

lemma execute_sint_guard_normal:
  assumes "mv = 0"
  shows "execute (assert_monad (equals_monad (sint_monad mv) (sint_monad (0::256 word)))) (s::('a::address) state) = Normal (Empty, s)"
  using assms
  by (simp add: assert_monad_def cond_monad_def equals_monad_def sint_monad_def true_monad_def lift_op_monad_def
      kdequals_def kdSint_def kdbool_def bool_monad_def false_monad_def lift_value_binary.simps vtequals.simps
      bind_def option_def return_def throw_def execute_simps)

lemma execute_sint_guard_exception:
  assumes "mv \<noteq> 0"
  shows "execute (assert_monad (equals_monad (sint_monad mv) (sint_monad (0::256 word)))) (s::('a::address) state) = Exception (Err, s)"
  using assms
  by (simp add: assert_monad_def cond_monad_def equals_monad_def sint_monad_def true_monad_def lift_op_monad_def
      kdequals_def kdSint_def kdbool_def bool_monad_def false_monad_def lift_value_binary.simps vtequals.simps
      bind_def option_def return_def throw_def execute_simps)


text \<open>The same two facts for the form the guard has after \<open>sint_monad_def\<close> has been unfolded.\<close>

lemma create_sint_monad: "create (\<lambda>s. Normal (rvalue.Value (Uint mv), s)) = sint_monad mv"
  by (simp add: sint_monad_def kdSint_def return_def comp_def)

lemma execute_guard_unfolded_normal:
  assumes "mv = 0"
  shows "execute (assert_monad (equals_monad (create (\<lambda>s. Normal (rvalue.Value (Uint mv), s)))
                                          (create (\<lambda>s. Normal (rvalue.Value (Uint (0::256 word)), s))))) (s::('a::address) state)
         = Normal (Empty, s)"
  unfolding create_sint_monad using execute_sint_guard_normal[OF assms, of s] .

lemma execute_guard_unfolded_exception:
  assumes "mv \<noteq> 0"
  shows "execute (assert_monad (equals_monad (create (\<lambda>s. Normal (rvalue.Value (Uint mv), s)))
                                          (create (\<lambda>s. Normal (rvalue.Value (Uint (0::256 word)), s))))) (s::('a::address) state)
         = Exception (Err, s)"
  unfolding create_sint_monad using execute_sint_guard_exception[OF assms, of s] .


section \<open>Division: \<open>x / y\<close>\<close>

text \<open>
  The framework has no division. This is unsigned division on the 256-bit word, built exactly like \<open>mod_monad\<close>
  (\<open>lift_int_binary\<close>), so it rounds toward zero. Solidity reverts (Panic 0x12) on a zero divisor, also inside \<open>unchecked\<close>,
  whereas the word operation returns 0; transpile.py therefore emits a division only behind an explicit zero test
  (\<open>cond_monad (equals_monad y (sint_monad 0)) (assert_monad false_monad) (div_monad x y)\<close>), as it does for \<open>%\<close>.
\<close>

definition vtdiv where
  "vtdiv = lift_int_binary (div)"

definition kddiv where
  "kddiv = lift_value_binary vtdiv"

definition div_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "div_monad = lift_op_monad kddiv"

lemma wp_div_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kddiv a rv)) \<bind> return)) P E) E s"
  shows "wp (div_monad lm rm) P E s"
  unfolding div_monad_def using assms by (rule wp_lift_op_monad)


section \<open>Narrow unsigned integers: \<open>uint8\<close> ... \<open>uint248\<close>\<close>

text \<open>
  The framework has one integer type, the 256-bit word. A value of type \<open>uintN\<close> (N < 256) is represented as the word
  with the same value, and the range \<open>0 \<le> v < 2^N\<close> is kept by the translation instead of by the type:
  \<^item> a checked \<open>+\<close>, \<open>*\<close> is the 256-bit checked operation followed by \<open>below_monad\<close> with bound \<open>2^N\<close>. This is exact: for N < 256 the
    sum of two N-bit values cannot overflow 256 bits, and where the product can, the 256-bit check reverts, as would the N-bit check;
  \<^item> a checked \<open>-\<close> needs nothing (the result is at most the left operand);
  \<^item> an unchecked operation (and an explicit conversion to a narrower type) is the 256-bit wrapping operation followed by \<open>mod 2^N\<close>
    (\<open>mod_monad\<close>), exact because \<open>2^N\<close> divides \<open>2^256\<close>;
  \<^item> an argument of an external function is checked on entry (Solidity's ABI decoder reverts on a value outside the range).
  \<open>below_monad x b\<close> is \<open>x\<close> if \<open>x < b\<close> and raises \<open>Err\<close> otherwise.
\<close>

definition vtbelow::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtbelow l r = (case (l, r) of (Uint x, Uint b) \<Rightarrow> (if x < b then Some (Uint x) else None) | _ \<Rightarrow> None)"

definition kdbelow where
  "kdbelow = lift_value_binary vtbelow"

definition below_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "below_monad = lift_op_monad kdbelow"

lemma wp_below_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdbelow a rv)) \<bind> return)) P E) E s"
  shows "wp (below_monad lm rm) P E s"
  unfolding below_monad_def using assms by (rule wp_lift_op_monad)

lemma kdbelow_Uint:
  "kdbelow (rvalue.Value (Uint x)) (rvalue.Value (Uint b)) = (if x < b then Some (rvalue.Value (Uint x)) else None)"
  by (simp add: kdbelow_def vtbelow_def)


section \<open>Signed integers: \<open>int256\<close>\<close>

text \<open>
  An \<open>int256\<close> is the 256-bit word read in two's complement (\<open>sint\<close>), so storage, equality, the wrapping operations of \<open>unchecked\<close> code and
  the conversions to and from \<open>uint256\<close> are the framework's own. What differs from the unsigned operations is the order and the checked
  operations, defined here on top of \<open>sint\<close>:
  \<^item> \<open>x < y\<close> compares \<open>sint x\<close> and \<open>sint y\<close>;
  \<^item> a checked \<open>+\<close>, \<open>-\<close>, \<open>*\<close> reverts when the exact result is outside \<open>[-2^255, 2^255)\<close>;
  \<^item> \<open>/\<close> rounds toward zero (not toward minus infinity as HOL's \<open>div\<close> on \<open>int\<close>); checked, it reverts on \<open>type(int256).min / -1\<close>,
    whose result \<open>2^255\<close> is out of range; unchecked, that case wraps to \<open>type(int256).min\<close>;
  \<^item> \<open>%\<close> takes the sign of the dividend (\<open>-7 % 2 = -1\<close>, \<open>7 % -2 = 1\<close>) and never overflows;
  \<^item> a zero divisor reverts for both; as for the unsigned operations transpile.py emits that test explicitly.
\<close>

definition sint_ok::"int \<Rightarrow> bool" where
  "sint_ok z = (-(2^255) \<le> z \<and> z < 2^255)"

definition stdiv::"int \<Rightarrow> int \<Rightarrow> int" where
  "stdiv a b = sgn a * sgn b * (\<bar>a\<bar> div \<bar>b\<bar>)"

definition stmod::"int \<Rightarrow> int \<Rightarrow> int" where
  "stmod a b = sgn a * (\<bar>a\<bar> mod \<bar>b\<bar>)"

definition vtsless::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtsless l r = (case (l, r) of (Uint x, Uint y) \<Rightarrow> Some (Bool (sint x < sint y)) | _ \<Rightarrow> None)"

definition vtsplus_safe::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtsplus_safe l r = (case (l, r) of (Uint x, Uint y) \<Rightarrow>
     (if sint_ok (sint x + sint y) then Some (Uint (x + y)) else None) | _ \<Rightarrow> None)"

definition vtsminus_safe::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtsminus_safe l r = (case (l, r) of (Uint x, Uint y) \<Rightarrow>
     (if sint_ok (sint x - sint y) then Some (Uint (x - y)) else None) | _ \<Rightarrow> None)"

definition vtsmult_safe::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtsmult_safe l r = (case (l, r) of (Uint x, Uint y) \<Rightarrow>
     (if sint_ok (sint x * sint y) then Some (Uint (x * y)) else None) | _ \<Rightarrow> None)"

definition vtsdiv::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtsdiv l r = (case (l, r) of (Uint x, Uint y) \<Rightarrow> Some (Uint (word_of_int (stdiv (sint x) (sint y)))) | _ \<Rightarrow> None)"

definition vtsdiv_safe::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtsdiv_safe l r = (case (l, r) of (Uint x, Uint y) \<Rightarrow>
     (if sint_ok (stdiv (sint x) (sint y)) then Some (Uint (word_of_int (stdiv (sint x) (sint y)))) else None) | _ \<Rightarrow> None)"

definition vtsmod::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtsmod l r = (case (l, r) of (Uint x, Uint y) \<Rightarrow> Some (Uint (word_of_int (stmod (sint x) (sint y)))) | _ \<Rightarrow> None)"

definition kdsless where "kdsless = lift_value_binary vtsless"
definition kdsplus_safe where "kdsplus_safe = lift_value_binary vtsplus_safe"
definition kdsminus_safe where "kdsminus_safe = lift_value_binary vtsminus_safe"
definition kdsmult_safe where "kdsmult_safe = lift_value_binary vtsmult_safe"
definition kdsdiv where "kdsdiv = lift_value_binary vtsdiv"
definition kdsdiv_safe where "kdsdiv_safe = lift_value_binary vtsdiv_safe"
definition kdsmod where "kdsmod = lift_value_binary vtsmod"

definition sless_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "sless_monad = lift_op_monad kdsless"

lemma wp_sless_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdsless a rv)) \<bind> return)) P E) E s"
  shows "wp (sless_monad lm rm) P E s"
  unfolding sless_monad_def using assms by (rule wp_lift_op_monad)

definition splus_safe_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "splus_safe_monad = lift_op_monad kdsplus_safe"

lemma wp_splus_safe_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdsplus_safe a rv)) \<bind> return)) P E) E s"
  shows "wp (splus_safe_monad lm rm) P E s"
  unfolding splus_safe_monad_def using assms by (rule wp_lift_op_monad)

definition sminus_safe_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "sminus_safe_monad = lift_op_monad kdsminus_safe"

lemma wp_sminus_safe_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdsminus_safe a rv)) \<bind> return)) P E) E s"
  shows "wp (sminus_safe_monad lm rm) P E s"
  unfolding sminus_safe_monad_def using assms by (rule wp_lift_op_monad)

definition smult_safe_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "smult_safe_monad = lift_op_monad kdsmult_safe"

lemma wp_smult_safe_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdsmult_safe a rv)) \<bind> return)) P E) E s"
  shows "wp (smult_safe_monad lm rm) P E s"
  unfolding smult_safe_monad_def using assms by (rule wp_lift_op_monad)

definition sdiv_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "sdiv_monad = lift_op_monad kdsdiv"

lemma wp_sdiv_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdsdiv a rv)) \<bind> return)) P E) E s"
  shows "wp (sdiv_monad lm rm) P E s"
  unfolding sdiv_monad_def using assms by (rule wp_lift_op_monad)

definition sdiv_safe_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "sdiv_safe_monad = lift_op_monad kdsdiv_safe"

lemma wp_sdiv_safe_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdsdiv_safe a rv)) \<bind> return)) P E) E s"
  shows "wp (sdiv_safe_monad lm rm) P E s"
  unfolding sdiv_safe_monad_def using assms by (rule wp_lift_op_monad)

definition smod_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "smod_monad = lift_op_monad kdsmod"

lemma wp_smod_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdsmod a rv)) \<bind> return)) P E) E s"
  shows "wp (smod_monad lm rm) P E s"
  unfolding smod_monad_def using assms by (rule wp_lift_op_monad)

text \<open>Sanity checks of the definitions against Solidity's documented results.\<close>

lemma stdiv_examples: "stdiv (-7) 2 = -3" "stdiv 7 (-2) = -3" "stdiv (-7) (-2) = 3" "stdiv 7 2 = 3"
  by (simp_all add: stdiv_def)

lemma stmod_examples: "stmod (-7) 2 = -1" "stmod 7 (-2) = 1" "stmod (-7) (-2) = -1" "stmod 7 2 = 1"
  by (simp_all add: stmod_def)

lemma stdiv_min_overflows: "\<not> sint_ok (stdiv (-(2^255)) (-1))"
  by (simp add: stdiv_def sint_ok_def)

lemma stmod_min_minus_one: "stmod (-(2^255)) (-1) = 0"
  by (simp add: stmod_def)

lemma stdiv_stmod: "b \<noteq> 0 \<Longrightarrow> stdiv a b * b + stmod a b = a"
proof -
  assume "b \<noteq> 0"
  have "sgn a * sgn b * (\<bar>a\<bar> div \<bar>b\<bar>) * b + sgn a * (\<bar>a\<bar> mod \<bar>b\<bar>) = sgn a * ((\<bar>a\<bar> div \<bar>b\<bar>) * (sgn b * b) + \<bar>a\<bar> mod \<bar>b\<bar>)"
    by (simp add: algebra_simps)
  also have "sgn b * b = \<bar>b\<bar>" by (simp add: abs_sgn)
  also have "(\<bar>a\<bar> div \<bar>b\<bar>) * \<bar>b\<bar> + \<bar>a\<bar> mod \<bar>b\<bar> = \<bar>a\<bar>" by (simp add: algebra_simps)
  finally show ?thesis unfolding stdiv_def stmod_def by (simp add: abs_sgn mult.commute)
qed

lemma vtsplus_safe_Uint:
  "vtsplus_safe (Uint x) (Uint y) = (if sint_ok (sint x + sint y) then Some (Uint (x + y)) else None)"
  by (simp add: vtsplus_safe_def)


section \<open>Proof support for the signed operators\<close>

text \<open>
  As for the framework's own checked operators (\<open>WP.thy\<close>): a rule that evaluates the lifted operation on two values when its
  side condition holds (\<open>wpsimps\<close>), and the destruction rule that turns a successful result into the side condition (\<open>wpdrules\<close>).
\<close>

lemma kdsless[wpsimps]:
  "kdsless (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Bool (sint l < sint r)))"
  by (simp add: kdsless_def vtsless_def)

lemma kdsplus_safe[wpsimps]:
  assumes "sint_ok (sint l + sint r)"
  shows "kdsplus_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (l + r)))"
  unfolding kdsplus_safe_def using assms by (simp add: vtsplus_safe_def)

lemma kdsplus_safe_dest[wpdrules]:
  assumes "kdsplus_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some ya"
  shows "sint_ok (sint l + sint r) \<and> ya = rvalue.Value (Uint (l + r))"
  using assms unfolding kdsplus_safe_def by (simp split: if_split_asm add: vtsplus_safe_def)

lemma kdsminus_safe[wpsimps]:
  assumes "sint_ok (sint l - sint r)"
  shows "kdsminus_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (l - r)))"
  unfolding kdsminus_safe_def using assms by (simp add: vtsminus_safe_def)

lemma kdsminus_safe_dest[wpdrules]:
  assumes "kdsminus_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some ya"
  shows "sint_ok (sint l - sint r) \<and> ya = rvalue.Value (Uint (l - r))"
  using assms unfolding kdsminus_safe_def by (simp split: if_split_asm add: vtsminus_safe_def)

lemma kdsmult_safe[wpsimps]:
  assumes "sint_ok (sint l * sint r)"
  shows "kdsmult_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (l * r)))"
  unfolding kdsmult_safe_def using assms by (simp add: vtsmult_safe_def)

lemma kdsmult_safe_dest[wpdrules]:
  assumes "kdsmult_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some ya"
  shows "sint_ok (sint l * sint r) \<and> ya = rvalue.Value (Uint (l * r))"
  using assms unfolding kdsmult_safe_def by (simp split: if_split_asm add: vtsmult_safe_def)

lemma kdsdiv[wpsimps]:
  "kdsdiv (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (word_of_int (stdiv (sint l) (sint r)))))"
  by (simp add: kdsdiv_def vtsdiv_def)

lemma kdsdiv_safe[wpsimps]:
  assumes "sint_ok (stdiv (sint l) (sint r))"
  shows "kdsdiv_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (word_of_int (stdiv (sint l) (sint r)))))"
  unfolding kdsdiv_safe_def using assms by (simp add: vtsdiv_safe_def)

lemma kdsdiv_safe_dest[wpdrules]:
  assumes "kdsdiv_safe (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some ya"
  shows "sint_ok (stdiv (sint l) (sint r)) \<and> ya = rvalue.Value (Uint (word_of_int (stdiv (sint l) (sint r))))"
  using assms unfolding kdsdiv_safe_def by (simp split: if_split_asm add: vtsdiv_safe_def)

lemma kdsmod[wpsimps]:
  "kdsmod (rvalue.Value (Uint l)) (rvalue.Value (Uint r)) = Some (rvalue.Value (Uint (word_of_int (stmod (sint l) (sint r)))))"
  by (simp add: kdsmod_def vtsmod_def)

text \<open>Addition of two words never adds more than the sum of the two numbers (a wrap-around only lowers it).\<close>

lemma unat_add_le:
  fixes x y :: "256 word"
  shows "unat (x + y) \<le> unat x + unat y"
  by (simp add: unat_word_ariths(1) mod_less_eq_dividend)


section \<open>Arguments of internal calls\<close>

text \<open>
  The framework's methods take their parameters as plain HOL values. \<open>transpile.py\<close> evaluates the arguments of an internal call, and
  reads each one as such a value with \<open>readSint\<close>, \<open>readAddress\<close> (both in the framework) or \<open>readBool\<close> (here, same shape).
\<close>

fun readBytes:: "('a::address) valtype \<Rightarrow> ((string, ex, ('a::address) state) state_monad)" where
  "readBytes (Bytes x) = return x"
| "readBytes _ = throw Err"

fun readBool:: "('a::address) valtype \<Rightarrow> ((bool, ex, ('a::address) state) state_monad)" where
  "readBool (Bool x) = return x"
| "readBool _ = throw Err"

section \<open>Monotonicity of the operators (needed when an operand contains an internal call)\<close>

text \<open>
  The \<open>contract\<close> command proves every method monotone in the dispatcher \<open>call\<close> (it defines the dispatcher as a least fixed point). Until now the
  operands of the operators never contained a call, so those proofs were trivial; with \<open>x = f(a) + g(b)\<close> the operand monads depend on
  \<open>call\<close>. The framework proves this for \<open>equals_monad\<close> only (\<open>lift_op_monad_mono\<close>); the same one-line proof works for every operator
  defined with \<open>lift_op_monad\<close>, and the corresponding facts for the unary operator, \<open>require\<close>/\<open>assert\<close> and the assignments.
\<close>

lemma mono_sm_const: "mono_sm (\<lambda>_. m)"
  by (simp add: monotoneI sm_ordI)

lemma lift_unary_monad_mono:
  assumes "mono_sm A"
  shows "mono_sm (\<lambda>f. lift_unary_monad op (A f))"
  unfolding lift_unary_monad_def by (rule bind_mono[OF assms]) (simp add: mono_sm_const)

lemma not_monad_mono[mono]: "mono_sm A \<Longrightarrow> mono_sm (\<lambda>f. not_monad (A f))"
  unfolding not_monad_def by (rule lift_unary_monad_mono)

lemma less_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. less_monad (A f) (B f))"
  unfolding less_monad_def by (rule lift_op_monad_mono)
lemma and_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. and_monad (A f) (B f))"
  unfolding and_monad_def by (rule lift_op_monad_mono)
lemma or_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. or_monad (A f) (B f))"
  unfolding or_monad_def by (rule lift_op_monad_mono)
lemma plus_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. plus_monad (A f) (B f))"
  unfolding plus_monad_def by (rule lift_op_monad_mono)
lemma plus_monad_safe_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. plus_monad_safe (A f) (B f))"
  unfolding plus_monad_safe_def by (rule lift_op_monad_mono)
lemma minus_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. minus_monad (A f) (B f))"
  unfolding minus_monad_def by (rule lift_op_monad_mono)
lemma minus_monad_safe_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. minus_monad_safe (A f) (B f))"
  unfolding minus_monad_safe_def by (rule lift_op_monad_mono)
lemma mult_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. mult_monad (A f) (B f))"
  unfolding mult_monad_def by (rule lift_op_monad_mono)
lemma mult_monad_safe_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. mult_monad_safe (A f) (B f))"
  unfolding mult_monad_safe_def by (rule lift_op_monad_mono)
lemma mod_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. mod_monad (A f) (B f))"
  unfolding mod_monad_def by (rule lift_op_monad_mono)

lemma div_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. div_monad (A f) (B f))"
  unfolding div_monad_def by (rule lift_op_monad_mono)
lemma below_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. below_monad (A f) (B f))"
  unfolding below_monad_def by (rule lift_op_monad_mono)
lemma sless_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. sless_monad (A f) (B f))"
  unfolding sless_monad_def by (rule lift_op_monad_mono)
lemma splus_safe_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. splus_safe_monad (A f) (B f))"
  unfolding splus_safe_monad_def by (rule lift_op_monad_mono)
lemma sminus_safe_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. sminus_safe_monad (A f) (B f))"
  unfolding sminus_safe_monad_def by (rule lift_op_monad_mono)
lemma smult_safe_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. smult_safe_monad (A f) (B f))"
  unfolding smult_safe_monad_def by (rule lift_op_monad_mono)
lemma sdiv_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. sdiv_monad (A f) (B f))"
  unfolding sdiv_monad_def by (rule lift_op_monad_mono)
lemma sdiv_safe_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. sdiv_safe_monad (A f) (B f))"
  unfolding sdiv_safe_monad_def by (rule lift_op_monad_mono)
lemma smod_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. smod_monad (A f) (B f))"
  unfolding smod_monad_def by (rule lift_op_monad_mono)

lemma assert_monad_mono[mono]: "mono_sm A \<Longrightarrow> mono_sm (\<lambda>f. assert_monad (A f))"
  unfolding assert_monad_def by (rule cond_mono) (simp_all add: mono_sm_const)

lemma lfold_cons_mono[mono]:
  assumes "mono_sm A" and "mono_sm (\<lambda>f. lfold (ms f))"
  shows "mono_sm (\<lambda>f. lfold (A f # ms f))"
  unfolding lfold.simps
  by (rule bind_mono[OF assms(1)], rule bind_mono, simp add: mono_sm_const, rule bind_mono[OF assms(2)], simp add: mono_sm_const)

lemma (in Contract) storeLookup_mono[mono]:
  assumes "mono_sm (\<lambda>f. lfold (es f))"
  shows "mono_sm (\<lambda>f. storeLookup i (es f))"
  unfolding storeLookup_def by (rule bind_mono[OF assms]) (simp add: mono_sm_const)

lemma (in Contract) stackLookup_mono[mono]:
  assumes "mono_sm (\<lambda>f. lfold (es f))"
  shows "mono_sm (\<lambda>f. stackLookup i (es f))"
  unfolding stackLookup_def by (rule bind_mono[OF assms]) (simp add: mono_sm_const)

lemma (in Contract) assign_stack_monad_mono[mono]:
  assumes "mono_sm M" and "mono_sm (\<lambda>f. lfold (es f))"
  shows "mono_sm (\<lambda>f. assign_stack_monad i (es f) (M f))"
  unfolding assign_stack_monad_def
  by (rule bind_mono[OF assms(1)], rule bind_mono[OF assms(2)], simp add: mono_sm_const)

lemma (in Contract) assign_storage_monad_mono[mono]:
  assumes "mono_sm M" and "mono_sm (\<lambda>f. lfold (es f))"
  shows "mono_sm (\<lambda>f. assign_storage_monad i (es f) (M f))"
  unfolding assign_storage_monad_def
  by (rule bind_mono[OF assms(1)], rule bind_mono[OF assms(2)], simp add: mono_sm_const)

lemma (in External) transfer_monad_mono2[mono]:
  assumes "mono_sm A" and "mono_sm B"
  shows "mono_sm (\<lambda>f. transfer_monad f (A f) (B f))"
  unfolding transfer_monad_def by (auto intro!: mono assms)

section \<open>Bitwise operations, shifts and exponentiation\<close>

text \<open>
  On the 256-bit word these are the word operations (\<open>AND\<close>, \<open>OR\<close>, \<open>XOR\<close>, \<open>NOT\<close>, \<open>push_bit\<close>, \<open>drop_bit\<close>, \<open>signed_drop_bit\<close>), as on the EVM.
  A shift by 256 bits or more gives 0 (or, for the arithmetic shift of a negative number, \<open>-1\<close>); it is guarded, so that an enormous shift
  amount is not evaluated. A narrow type (\<open>uintN\<close>, N < 256) is the word with the same value: \<open>&\<close>, \<open>|\<close>, \<open>^\<close> and \<open>>>\<close> keep a value in range,
  while \<open>~\<close> and \<open><<\<close> are followed by \<open>mod 2^N\<close> by transpile.py (Solidity truncates to the type).
  Exponentiation \<open>x ** y\<close> of unsigned numbers: the checked form reverts when the result does not fit (an exponent of 256 or more
  overflows for every base of at least 2), the unchecked form wraps around (square-and-multiply, so a huge exponent is cheap).
\<close>

unbundle bit_operations_syntax

definition word_shl::"256 word \<Rightarrow> 256 word \<Rightarrow> 256 word" where
  "word_shl a b = (if unat b < 256 then push_bit (unat b) a else 0)"

definition word_shr::"256 word \<Rightarrow> 256 word \<Rightarrow> 256 word" where
  "word_shr a b = (if unat b < 256 then drop_bit (unat b) a else 0)"

definition word_sar::"256 word \<Rightarrow> 256 word \<Rightarrow> 256 word" where
  "word_sar a b = (if unat b < 256 then signed_drop_bit (unat b) a else (if sint a < 0 then -1 else 0))"

fun wpow::"256 word \<Rightarrow> nat \<Rightarrow> 256 word" where
  "wpow a n = (if n = 0 then 1 else (let h = wpow (a * a) (n div 2) in if odd n then a * h else h))"

definition vtbitand where "vtbitand = lift_int_binary (AND)"
definition vtbitor where "vtbitor = lift_int_binary (OR)"
definition vtbitxor where "vtbitxor = lift_int_binary (XOR)"
definition vtshl where "vtshl = lift_int_binary word_shl"
definition vtshr where "vtshr = lift_int_binary word_shr"
definition vtsar where "vtsar = lift_int_binary word_sar"
definition vtexp_wrap where "vtexp_wrap = (\<lambda>l r. case (l, r) of (Uint a, Uint b) \<Rightarrow> Some (Uint (wpow a (unat b))) | _ \<Rightarrow> None)"

definition vtexp_safe::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtexp_safe l r = (case (l, r) of (Uint a, Uint b) \<Rightarrow>
      (if unat a \<le> 1 then Some (Uint (wpow a (unat b)))
       else if unat b \<ge> 256 then None
       else (let p = unat a ^ unat b in if p < 2^256 then Some (Uint (word_of_nat p)) else None))
    | _ \<Rightarrow> None)"

definition vtbitnot::"('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtbitnot v = (case v of Uint x \<Rightarrow> Some (Uint (NOT x)) | _ \<Rightarrow> None)"

definition kdbitand where "kdbitand = lift_value_binary vtbitand"
definition kdbitor where "kdbitor = lift_value_binary vtbitor"
definition kdbitxor where "kdbitxor = lift_value_binary vtbitxor"
definition kdshl where "kdshl = lift_value_binary vtshl"
definition kdshr where "kdshr = lift_value_binary vtshr"
definition kdsar where "kdsar = lift_value_binary vtsar"
definition kdexp_wrap where "kdexp_wrap = lift_value_binary vtexp_wrap"
definition kdexp_safe where "kdexp_safe = lift_value_binary vtexp_safe"
definition kdbitnot where "kdbitnot = lift_value_unary vtbitnot"

definition bitand_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "bitand_monad = lift_op_monad kdbitand"
definition bitor_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "bitor_monad = lift_op_monad kdbitor"
definition bitxor_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "bitxor_monad = lift_op_monad kdbitxor"
definition shl_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "shl_monad = lift_op_monad kdshl"
definition shr_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "shr_monad = lift_op_monad kdshr"
definition sar_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "sar_monad = lift_op_monad kdsar"
definition exp_wrap_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "exp_wrap_monad = lift_op_monad kdexp_wrap"
definition exp_safe_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "exp_safe_monad = lift_op_monad kdexp_safe"
definition bitnot_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "bitnot_monad = lift_unary_monad kdbitnot"

lemma wp_bitand_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdbitand a rv)) \<bind> return)) P E) E s"
  shows "wp (bitand_monad lm rm) P E s"
  unfolding bitand_monad_def using assms by (rule wp_lift_op_monad)
lemma wp_bitor_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdbitor a rv)) \<bind> return)) P E) E s"
  shows "wp (bitor_monad lm rm) P E s"
  unfolding bitor_monad_def using assms by (rule wp_lift_op_monad)
lemma wp_bitxor_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdbitxor a rv)) \<bind> return)) P E) E s"
  shows "wp (bitxor_monad lm rm) P E s"
  unfolding bitxor_monad_def using assms by (rule wp_lift_op_monad)
lemma wp_shl_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdshl a rv)) \<bind> return)) P E) E s"
  shows "wp (shl_monad lm rm) P E s"
  unfolding shl_monad_def using assms by (rule wp_lift_op_monad)
lemma wp_shr_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdshr a rv)) \<bind> return)) P E) E s"
  shows "wp (shr_monad lm rm) P E s"
  unfolding shr_monad_def using assms by (rule wp_lift_op_monad)
lemma wp_sar_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdsar a rv)) \<bind> return)) P E) E s"
  shows "wp (sar_monad lm rm) P E s"
  unfolding sar_monad_def using assms by (rule wp_lift_op_monad)
lemma wp_exp_wrap_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdexp_wrap a rv)) \<bind> return)) P E) E s"
  shows "wp (exp_wrap_monad lm rm) P E s"
  unfolding exp_wrap_monad_def using assms by (rule wp_lift_op_monad)
lemma wp_exp_safe_monad[wprules]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdexp_safe a rv)) \<bind> return)) P E) E s"
  shows "wp (exp_safe_monad lm rm) P E s"
  unfolding exp_safe_monad_def using assms by (rule wp_lift_op_monad)

lemma bitand_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. bitand_monad (A f) (B f))"
  unfolding bitand_monad_def by (rule lift_op_monad_mono)
lemma bitor_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. bitor_monad (A f) (B f))"
  unfolding bitor_monad_def by (rule lift_op_monad_mono)
lemma bitxor_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. bitxor_monad (A f) (B f))"
  unfolding bitxor_monad_def by (rule lift_op_monad_mono)
lemma shl_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. shl_monad (A f) (B f))"
  unfolding shl_monad_def by (rule lift_op_monad_mono)
lemma shr_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. shr_monad (A f) (B f))"
  unfolding shr_monad_def by (rule lift_op_monad_mono)
lemma sar_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. sar_monad (A f) (B f))"
  unfolding sar_monad_def by (rule lift_op_monad_mono)
lemma exp_wrap_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. exp_wrap_monad (A f) (B f))"
  unfolding exp_wrap_monad_def by (rule lift_op_monad_mono)
lemma exp_safe_monad_mono[mono]: "\<lbrakk>mono_sm A; mono_sm B\<rbrakk> \<Longrightarrow> mono_sm (\<lambda>f. exp_safe_monad (A f) (B f))"
  unfolding exp_safe_monad_def by (rule lift_op_monad_mono)
lemma bitnot_monad_mono[mono]: "mono_sm A \<Longrightarrow> mono_sm (\<lambda>f. bitnot_monad (A f))"
  unfolding bitnot_monad_def by (rule lift_unary_monad_mono)

lemma wpow_examples:
  "wpow 2 10 = 1024" "wpow 3 0 = 1" "wpow 0 0 = 1" "wpow 0 5 = 0" "wpow 2 256 = 0" "wpow 2 255 = 2^255"
  by eval+


section \<open>Block number and chain id\<close>

text \<open>
  Like \<open>tx.origin\<close>, these are fixed but unspecified values (Hilbert's \<open>undefined\<close>): nothing relates them to the rest of the model, so a
  proof that mentions them holds for every block number and every chain. (The framework has \<open>block.timestamp\<close> only.)
  A contract that reads them cannot be run against the EVM by the conformance harness (it has no value for them), as for \<open>tx.origin\<close>.
\<close>

definition block_number::"256 word" where "block_number = undefined"
definition chain_id::"256 word" where "chain_id = undefined"

definition block_number_monad::"('a::address) expression_monad" where "block_number_monad = sint_monad block_number"
definition chain_id_monad::"('a::address) expression_monad" where "chain_id_monad = sint_monad chain_id"

lemma wp_block_number_monad[wprules]:
  assumes "P (kdSint block_number) s"
  shows "wp block_number_monad P E s"
  unfolding block_number_monad_def sint_monad_def using assms by (simp add: wprules)

lemma wp_chain_id_monad[wprules]:
  assumes "P (kdSint chain_id) s"
  shows "wp chain_id_monad P E s"
  unfolding chain_id_monad_def sint_monad_def using assms by (simp add: wprules)

section \<open>Signature recovery\<close>

text \<open>
  \<open>ecrecover(hash, v, r, s)\<close> is an unspecified function of its four arguments. It is a parameter of the framework's \<open>Keccak256\<close>
  locale (the third, next to \<open>keccak256\<close> and \<open>encodeABI\<close>; a local patch of \<open>Solidity.thy\<close>), and nothing is assumed about
  it: a proof about a contract that recovers a signer holds for every assignment of signers to signatures, including the zero address
  that the EVM returns for an invalid signature. The arguments are evaluated left to right and packed into a list as for
  \<open>encodeABI\<close>. The conformance harness instantiates the parameter with the values of the precompile on the signatures it generates.
\<close>

context Keccak256
begin

definition ecrecover_monad ::
  "('a::address) expression_monad \<Rightarrow> 'a expression_monad \<Rightarrow> 'a expression_monad \<Rightarrow> 'a expression_monad \<Rightarrow> 'a expression_monad" where
  "ecrecover_monad h v r s =
    do {
      xs \<leftarrow> mfold [h, v, r, s];
      address_monad (ecrecover xs)
    }"

lemma wp_ecrecover_monad[wprules]:
  assumes "wp (mfold [h, v, r, s]) (\<lambda>xs. wp (address_monad (ecrecover xs)) P E) E st"
  shows "wp (ecrecover_monad h v r s) P E st"
  unfolding ecrecover_monad_def using assms by (rule wprules)+

end

section \<open>Hashing and recovery: monotonicity for arguments that contain calls\<close>

text \<open>
  The \<open>contract\<close> command proves every method monotone in the dispatcher (see "Monotonicity" above). The framework has no rule for
  \<open>keccak256_monad\<close>, \<open>encodeABI_monad\<close> (or the list fold \<open>mfold\<close> they use), nor for \<open>ecrecover_monad\<close>, so a hash or a signature recovery
  whose arguments call an internal function (\<open>keccak256(abi.encodePacked("\\x19\\x01", DOMAIN_SEPARATOR(), ...))\<close>) could not be defined.
\<close>

lemma mfold_nil_mono[mono]: "mono_sm (\<lambda>f. mfold [])"
  unfolding mfold.simps by (simp add: mono_sm_const)

lemma mfold_cons_mono[mono]:
  assumes "mono_sm A" and "mono_sm (\<lambda>f. mfold (ms f))"
  shows "mono_sm (\<lambda>f. mfold (A f # ms f))"
  unfolding mfold.simps
  by (rule bind_mono[OF assms(1)], rule bind_mono[OF assms(2)], simp add: mono_sm_const)

context Keccak256
begin

lemma keccak256_monad_mono[mono]: "mono_sm A \<Longrightarrow> mono_sm (\<lambda>f. keccak256_monad (A f))"
  unfolding keccak256_monad_def by (rule bind_mono, assumption) (simp add: mono_sm_const)

lemma encodeABI_monad_mono[mono]: "mono_sm (\<lambda>f. mfold (ms f)) \<Longrightarrow> mono_sm (\<lambda>f. encodeABI_monad (ms f))"
  unfolding encodeABI_monad_def by (rule bind_mono, assumption) (simp add: mono_sm_const)

lemma ecrecover_monad_mono[mono]:
  assumes "mono_sm A" and "mono_sm B" and "mono_sm C" and "mono_sm D"
  shows "mono_sm (\<lambda>f. ecrecover_monad (A f) (B f) (C f) (D f))"
proof -
  have "mono_sm (\<lambda>f. mfold [A f, B f, C f, D f])" by (intro mfold_cons_mono mfold_nil_mono assms)
  then show ?thesis unfolding ecrecover_monad_def by (rule bind_mono) (simp add: mono_sm_const)
qed

end

section \<open>Arrays in storage: \<open>pop\<close> and \<open>delete\<close>\<close>

text \<open>
  The framework has \<open>storeArrayLength\<close> (\<open>a.length\<close>), \<open>allocate\<close> (the first half of \<open>a.push(x)\<close>: a default element is appended, the
  value is then assigned to the new last element) and indexed lookup and assignment (a path of indices; out of range is an error, as the
  panic of Solidity). It has no \<open>a.pop()\<close> and no way to reset a whole array or struct (\<open>delete a\<close>, \<open>delete s\<close>).
  \<open>pop_monad\<close> removes the last element and fails on an empty array; \<open>delete_monad\<close> replaces the value at a path by the default value
  of its type (\<open>sdefault T\<close>, given by the caller): the empty list for a dynamic array, the default elements for a fixed one.
\<close>

fun pop_data :: "'v storage_data \<Rightarrow> 'v storage_data option" where
  "pop_data (storage_data.Array xs) = (if xs = [] then None else Some (storage_data.Array (butlast xs)))"
| "pop_data _ = None"

context Contract
begin

definition pop_monad :: "id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> 'a expression_monad" where
  "pop_monad i es =
    do {
      is \<leftarrow> lfold es;
      ar \<leftarrow> option Err (\<lambda>s. slookup is (state.Storage s this i) \<bind> pop_data);
      storage_update_monad [] is (K ar) i
    }"

definition delete_monad :: "id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> 'a valtype storage_data \<Rightarrow> 'a expression_monad" where
  "delete_monad i es d =
    do {
      is \<leftarrow> lfold es;
      storage_update_monad [] is (K d) i
    }"

lemma wp_pop_monad[wprules]:
  assumes "wp (lfold es)
     (\<lambda>a. wp (option Err (\<lambda>s. slookup a (state.Storage s this i) \<bind> pop_data) \<bind>
              (\<lambda>ar. storage_update_monad [] a (K ar) i))
           P E)
     E s"
  shows "wp (pop_monad i es) P E s"
  unfolding pop_monad_def apply vcg using assms by simp

lemma wp_delete_monad[wprules]:
  assumes "wp (lfold es) (\<lambda>a. wp (storage_update_monad [] a (K d) i) P E) E s"
  shows "wp (delete_monad i es d) P E s"
  unfolding delete_monad_def apply vcg using assms by simp

text \<open>Monotonicity when an index expression calls an internal function (see "Monotonicity of the operators").\<close>

lemma pop_monad_mono[mono]:
  assumes "mono_sm (\<lambda>f. lfold (es f))"
  shows "mono_sm (\<lambda>f. pop_monad i (es f))"
  unfolding pop_monad_def by (rule bind_mono[OF assms]) (simp add: mono_sm_const)

lemma delete_monad_mono[mono]:
  assumes "mono_sm (\<lambda>f. lfold (es f))"
  shows "mono_sm (\<lambda>f. delete_monad i (es f) d)"
  unfolding delete_monad_def by (rule bind_mono[OF assms]) (simp add: mono_sm_const)

lemma storeArrayLength_mono[mono]:
  assumes "mono_sm (\<lambda>f. lfold (es f))"
  shows "mono_sm (\<lambda>f. storeArrayLength i (es f))"
  unfolding storeArrayLength_def by (rule bind_mono[OF assms]) (simp add: mono_sm_const)

lemma allocate_mono[mono]:
  assumes "mono_sm (\<lambda>f. lfold (es f))"
  shows "mono_sm (\<lambda>f. allocate i (es f) d)"
  unfolding allocate_def by (rule bind_mono[OF assms]) (simp add: mono_sm_const)

end

section \<open>Calls to other contracts (a callee that is not modelled)\<close>

text \<open>
  A call \<open>t.f(args)\<close> on a value of contract or interface type runs code that the model does not contain. Two things are therefore left
  unspecified, as two further parameters of the framework's \<open>Keccak256\<close> locale (framework patch 5, next to \<open>ecrecover\<close>):
  \<^item> \<open>ext_isc a\<close>: does the address hold code? Solidity reverts a call to an address without code.
  \<^item> \<open>ext_result ep st bal a f vs\<close>: the answer of the callee at address \<open>a\<close> to the function with signature \<open>f\<close> and the argument values \<open>vs\<close>,
    \<open>None\<close> if it reverts. It may depend on the storage \<open>st\<close> and the balances \<open>bal\<close> of the caller (a callee can read them) and on \<open>ep\<close>, the
    number of state-changing calls to callees made so far: \<open>transpile.py\<close> adds a counter \<open>ghost_ext_epoch\<close> to the contract, increased by every
    call that is not \<open>view\<close> or \<open>pure\<close>, so that a callee whose own state changed can answer differently to the same question.
  A state-changing call also hands control to an arbitrary party after the counter is increased (the framework's \<open>transfer_monad\<close> of the value 0,
  i.e. \<open>ecall (external call)\<close>: the callee may re-enter any external function); a \<open>view\<close> call cannot (it is a static call).
  Nothing is assumed about either parameter, so a proof holds for every callee. A call with several return values, a payable call
  and \<open>delegatecall\<close> are not expressed.
\<close>

fun read_values :: "('a::address) rvalue list \<Rightarrow> ((('a::address) valtype list), ex, ('a::address) state) state_monad" where
  "read_values [] = return []"
| "read_values (x # xs) = do { v \<leftarrow> readValue x; vs \<leftarrow> read_values xs; return (v # vs) }"

context Keccak256
begin

definition ext_code_monad :: "('a::address) rvalue \<Rightarrow> 'a expression_monad" where
  "ext_code_monad t =
    do {
      v \<leftarrow> readValue t;
      a \<leftarrow> readAddress v;
      assert Err (\<lambda>_. ext_isc a);
      return Empty
    }"

definition ext_result_monad ::
  "string \<Rightarrow> ('a::address) rvalue \<Rightarrow> 'a rvalue \<Rightarrow> 'a rvalue list \<Rightarrow> (('a valtype), ex, 'a state) state_monad" where
  "ext_result_monad f ep t args =
    do {
      epv \<leftarrow> readValue ep;
      e \<leftarrow> readSint epv;
      tv \<leftarrow> readValue t;
      a \<leftarrow> readAddress tv;
      vs \<leftarrow> read_values args;
      s \<leftarrow> get;
      (case ext_result e (state.Storage s) (Balances s) a f vs of None \<Rightarrow> throw Err | Some v \<Rightarrow> return v)
    }"

text \<open>
  The answer, checked to have the shape of the declared return type (the ABI decoder reverts on anything else). The three conversions are
  constants of their own with a weakest-precondition rule that splits on the shape, so that \<open>vcg\<close> needs no case analysis.
\<close>

definition ext_as_word :: "('a::address) valtype \<Rightarrow> 'a expression_monad" where
  "ext_as_word v = (case v of Uint w \<Rightarrow> sint_monad w | _ \<Rightarrow> throw Err)"

definition ext_as_flag :: "('a::address) valtype \<Rightarrow> 'a expression_monad" where
  "ext_as_flag v = (case v of Bool b \<Rightarrow> bool_monad b | _ \<Rightarrow> throw Err)"

definition ext_as_addr :: "('a::address) valtype \<Rightarrow> 'a expression_monad" where
  "ext_as_addr v = (case v of Address a \<Rightarrow> address_monad a | _ \<Rightarrow> throw Err)"

lemma wp_ext_as_word[wprules]:
  assumes "\<And>w. v = Uint w \<Longrightarrow> P (kdSint w) s" and "(\<forall>w. v \<noteq> Uint w) \<Longrightarrow> E Err s"
  shows "wp (ext_as_word v) P E s"
  using assms unfolding ext_as_word_def sint_monad_def by (cases v) (simp_all add: wprules)

lemma wp_ext_as_flag[wprules]:
  assumes "\<And>b. v = Bool b \<Longrightarrow> P (kdbool b) s" and "(\<forall>b. v \<noteq> Bool b) \<Longrightarrow> E Err s"
  shows "wp (ext_as_flag v) P E s"
  using assms unfolding ext_as_flag_def bool_monad_def by (cases v) (simp_all add: wprules)

lemma wp_ext_as_addr[wprules]:
  assumes "\<And>a. v = Address a \<Longrightarrow> P (kdAddress a) s" and "(\<forall>a. v \<noteq> Address a) \<Longrightarrow> E Err s"
  shows "wp (ext_as_addr v) P E s"
  using assms unfolding ext_as_addr_def address_monad_def by (cases v) (simp_all add: wprules)

definition ext_word_monad :: "string \<Rightarrow> ('a::address) rvalue \<Rightarrow> 'a rvalue \<Rightarrow> 'a rvalue list \<Rightarrow> 'a expression_monad" where
  "ext_word_monad f ep t args = do { v \<leftarrow> ext_result_monad f ep t args; ext_as_word v }"

definition ext_flag_monad :: "string \<Rightarrow> ('a::address) rvalue \<Rightarrow> 'a rvalue \<Rightarrow> 'a rvalue list \<Rightarrow> 'a expression_monad" where
  "ext_flag_monad f ep t args = do { v \<leftarrow> ext_result_monad f ep t args; ext_as_flag v }"

definition ext_addr_monad :: "string \<Rightarrow> ('a::address) rvalue \<Rightarrow> 'a rvalue \<Rightarrow> 'a rvalue list \<Rightarrow> 'a expression_monad" where
  "ext_addr_monad f ep t args = do { v \<leftarrow> ext_result_monad f ep t args; ext_as_addr v }"

definition ext_unit_monad :: "string \<Rightarrow> ('a::address) rvalue \<Rightarrow> 'a rvalue \<Rightarrow> 'a rvalue list \<Rightarrow> 'a expression_monad" where
  "ext_unit_monad f ep t args = do { _ \<leftarrow> ext_result_monad f ep t args; return Empty }"

text \<open>
  The monads do not depend on the dispatcher, so they are monotone in it (the \<open>contract\<close> command needs this); the weakest-precondition
  rules unfold the definition and leave the steps to the existing rules.
\<close>

lemma ext_code_monad_mono[mono]: "mono_sm (\<lambda>f. ext_code_monad t)" by (rule mono_sm_const)
lemma ext_word_monad_mono[mono]: "mono_sm (\<lambda>f. ext_word_monad n ep t args)" by (rule mono_sm_const)
lemma ext_flag_monad_mono[mono]: "mono_sm (\<lambda>f. ext_flag_monad n ep t args)" by (rule mono_sm_const)
lemma ext_addr_monad_mono[mono]: "mono_sm (\<lambda>f. ext_addr_monad n ep t args)" by (rule mono_sm_const)
lemma ext_unit_monad_mono[mono]: "mono_sm (\<lambda>f. ext_unit_monad n ep t args)" by (rule mono_sm_const)

lemma wp_ext_code_monad[wprules]:
  assumes "wp (readValue t \<bind> (\<lambda>v. readAddress v \<bind> (\<lambda>a. assert Err (\<lambda>_. ext_isc a) \<bind> (\<lambda>_. return Empty)))) P E s"
  shows "wp (ext_code_monad t) P E s"
  unfolding ext_code_monad_def using assms .

lemma wp_ext_result_monad[wprules]:
  assumes "wp (readValue ep \<bind> (\<lambda>epv. readSint epv \<bind> (\<lambda>e. readValue t \<bind> (\<lambda>tv. readAddress tv \<bind> (\<lambda>a.
              read_values args \<bind> (\<lambda>vs. get \<bind> (\<lambda>s. (case ext_result e (state.Storage s) (Balances s) a f vs of
                None \<Rightarrow> throw Err | Some v \<Rightarrow> return v)))))))) P E s"
  shows "wp (ext_result_monad f ep t args) P E s"
  unfolding ext_result_monad_def using assms .

lemma wp_ext_word_monad[wprules]:
  assumes "wp (ext_result_monad f ep t args) (\<lambda>v. wp (ext_as_word v) P E) E s"
  shows "wp (ext_word_monad f ep t args) P E s"
  unfolding ext_word_monad_def apply (rule wprules) by (rule assms)

lemma wp_ext_flag_monad[wprules]:
  assumes "wp (ext_result_monad f ep t args) (\<lambda>v. wp (ext_as_flag v) P E) E s"
  shows "wp (ext_flag_monad f ep t args) P E s"
  unfolding ext_flag_monad_def apply (rule wprules) by (rule assms)

lemma wp_ext_addr_monad[wprules]:
  assumes "wp (ext_result_monad f ep t args) (\<lambda>v. wp (ext_as_addr v) P E) E s"
  shows "wp (ext_addr_monad f ep t args) P E s"
  unfolding ext_addr_monad_def apply (rule wprules) by (rule assms)

lemma wp_ext_unit_monad[wprules]:
  assumes "wp (ext_result_monad f ep t args) (\<lambda>_. wp (return Empty) P E) E s"
  shows "wp (ext_unit_monad f ep t args) P E s"
  unfolding ext_unit_monad_def apply (rule wprules) by (rule assms)

end

end
