theory Inheritance_Reuse
  imports Solidity_Main
begin

section \<open>Inheritance: reuse of the proofs of a base whose pair has a compound revert condition\<close>

text \<open>
  A derived contract that verifies the invariant of its base takes the obligations of the inherited methods from the base. The hypothesis
  on the dispatcher is translated along the injection and simplified; with a revert condition such as the one of an ERC20 transfer (an
  address is zero, or a value is excessive, written with absorbed disjuncts) the simplifier leaves a goal that is literally one conjunct of a
  premise, and the automatic proof used to fail with "Tactic failed" for the inherited method.
\<close>

contract Bs
  for "STR ''x''": "SType.TValue TSint"

constructor
where
  "skip_monad"

cfunction mv external
param "STR ''t''" : "SType.TValue TAddress"
and "STR ''v''" : "SType.TValue TSint"
where
  "do {
     cond_monad (equals_monad (stackLookup (STR ''t'') []) (address_monad null)) (assert_monad false_monad) skip_monad;
     cond_monad (equals_monad (stackLookup (STR ''v'') []) (sint_monad 5)) (assert_monad false_monad) skip_monad
   }"

contract Dv is Bs

constructor
where
  "skip_monad"

cfunction other external
where
  "skip_monad"

invariant bs_ok e where "True" for "Bs"

lemma (in bs) bs_okI2:
  assumes "\<exists>v. fst e STR ''x'' = storage_data.Value (Uint v)"
  shows "bs_ok e"
  using assms by (blast intro: bs_okI)

declare (in bs) bs_okI[wprules del]
declare (in bs) bs_okI2[wprules]

abbreviation (in bs) lp2 where "lp2 _ _ st \<equiv> inv_state bs_ok st"
abbreviation (in Solidity) sp2 where "sp2 (t::'a) (v::256 word) st rr st' \<equiv> True"
abbreviation (in Solidity) rv2 where
  "rv2 (t::'a) (v::256 word) st \<equiv> t = null \<or> (t = null \<and> v = 7) \<or> (t \<noteq> null \<and> v = 5)"

verification bs_v:
  bs_ok
  mv (lp2, sp2, rv2)
  for "Bs"
  apply (all \<open>unfold constructor_def mv_def\<close>)
  apply (all \<open>(erule post_exc_const, erule_tac post_wp)\<close>)
  apply (all \<open>unfold inv_state_def\<close>)
  apply (all \<open>vcg_all wprules: bs_okI2 wperules: bs_okE\<close>)
  apply (all \<open>(clarsimp simp: wpsimps dest!: wpdrules)?\<close>)
  apply (all \<open>(vcg_all wprules: bs_okI2 wperules: bs_okE)?\<close>)
  apply (all \<open>(clarsimp simp: wpsimps dest!: wpdrules)?\<close>)
  apply (all \<open>(solves \<open>clarsimp simp: kdequals_def kdnot_def kdless_def vtless_def lift_value_binary.simps vtequals.simps vtnot_def\<close>)?\<close>)
  apply (all \<open>(solves \<open>clarsimp simp: word_gt_0\<close>)?\<close>)
  done

abbreviation (in dv) lp2 where "lp2 _ _ st \<equiv> inv_state bs.bs_ok st"

verification dv_v:
  bs.bs_ok
  for "Dv"
  apply (all \<open>(unfold constructor_def other_def)?\<close>)
  apply (all \<open>(erule post_exc_const, erule_tac post_wp)?\<close>)
  apply (all \<open>(unfold inv_state_def)?\<close>)
  apply (all \<open>(vcg_all wprules: bs.bs_okI2[OF bs_const] wperules: bs.bs_okE[OF bs_const])?\<close>)
  apply (all \<open>(clarsimp simp: wpsimps dest!: wpdrules)?\<close>)
  done

end
