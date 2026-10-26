theory Inheritance_Bank
  imports Bank
begin

section \<open>Inheritance: derived banking contracts\<close>

text \<open>
  A contract can inherit from others: \<open>contract D is B1, B2\<close>. The methods of the bases are inherited (as aliases of the
  base's methods, so that calls resolve to the most derived definition), the state variables of the bases come first,
  the constructors of the bases run before the one of the derived contract, and \<open>verification\<close> reuses the proofs
  of the bases: the obligations for an inherited method are those of the base and are proved automatically.
\<close>

subsection \<open>A derived contract that adds a method\<close>

contract Bank2 is Bank

constructor
where
  "\<langle>skip\<rangle>"

cfunction noop external
where
  "\<langle>skip\<rangle>"

text \<open>
  \<open>deposit\<close>, \<open>withdraw\<close> and \<open>reset\<close> are inherited: their obligations (and the pair of \<open>reset\<close>) come from the
  verification of \<open>Bank\<close>. Only the constructor and the new method remain.
\<close>

verification sum_bal_bank2:
  sum_bal  (*the invariant of Bank, found in the locale of the base; the others below write bank.sum_bal*)
  deposit and
  withdraw and
  reset and
  noop
  for "Bank2"
proof -
  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (constructor call) s r \<Longrightarrow> post s r (K (K (inv_state bank.sum_bal))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: bank.sum_balI[OF bank_const] | auto)+

  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (noop call) s r \<Longrightarrow> inv_state bank.sum_bal s \<Longrightarrow> post s r (K (K (inv_state bank.sum_bal))) (K True)"
    unfolding noop_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by vcg
qed

subsection \<open>Overriding a method\<close>

text \<open>
  \<open>Bank3\<close> overrides \<open>reset\<close>. Calls of \<open>reset\<close> in the inherited \<open>withdraw\<close> reach the override. Without a pair of its own the
  override has to meet the pair of \<open>Bank\<close>, so \<open>withdraw\<close> (and \<open>deposit\<close>) are still proved automatically.
\<close>

contract Bank3 is Bank

constructor
where
  "\<langle>skip\<rangle>"

cfunction reset
where
  "do {
    balances [\<langle>sender\<rangle>] ::=\<^sub>s \<langle>sint\<rangle> 0;
    \<langle>skip\<rangle>
  }"

verification sum_bal_bank3:
  bank.sum_bal
  deposit and
  withdraw and
  reset
  for "Bank3"
proof -
  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (constructor call) s r \<Longrightarrow> post s r (K (K (inv_state bank.sum_bal))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: bank.sum_balI[OF bank_const] | auto)+

  show "\<And>call. effect (reset call) s r \<Longrightarrow>
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> True \<Longrightarrow> post s r reset_post (K True)"
    unfolding reset_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply vcg
    by auto
qed

subsection \<open>Overriding with a stronger postcondition\<close>

text \<open>
  An override may state a pair of its own. The base's proofs about calls of the method (here the proof for \<open>withdraw\<close>, which uses
  the pair \<open>reset_post\<close> of \<open>reset\<close>) stay valid only if the new condition implies the old one: this is an additional goal.
\<close>

definition(in Solidity) reset_post2 where
"reset_post2 start_state return_value end_state \<equiv>
  reset_post start_state return_value end_state \<and> Balances end_state this = Balances start_state this"

contract Bank4 is Bank

constructor
where
  "\<langle>skip\<rangle>"

cfunction reset
where
  "do {
    balances [\<langle>sender\<rangle>] ::=\<^sub>s \<langle>sint\<rangle> 0;
    \<langle>skip\<rangle>
  }"

verification sum_bal_bank4:
  bank.sum_bal
  deposit and
  withdraw and
  reset (true_pre, reset_post2)
  for "Bank4"
proof -
  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (constructor call) s r \<Longrightarrow> post s r (K (K (inv_state bank.sum_bal))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: bank.sum_balI[OF bank_const] | auto)+

  show "\<And>call. effect (reset call) s r \<Longrightarrow>
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> True \<Longrightarrow> post s r reset_post2 (K True)"
    unfolding reset_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def reset_post2_def
    apply vcg
    by auto

  (*the new condition of reset implies the condition of the base*)
  show "vcond bank4.Reset_m s r \<Longrightarrow> bank.vcond msg_sender this bank.Reset_m s r"
    by (cases r) (auto simp add: vcond_reset bank.vcond_reset[OF bank_const] post_def reset_post2_def)
qed

subsection \<open>\<open>super\<close>\<close>

text \<open>\<open>icall super_reset\<close> runs the definition of \<open>reset\<close> in \<open>Bank\<close>.\<close>

contract Bank9 is Bank

constructor
where
  "\<langle>skip\<rangle>"

cfunction reset
where
  "icall super_reset"

verification sum_bal_bank9:
  bank.sum_bal
  deposit and
  withdraw and
  reset
  for "Bank9"
proof -
  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (constructor call) s r \<Longrightarrow> post s r (K (K (inv_state bank.sum_bal))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: bank.sum_balI[OF bank_const] | auto)+

  show "\<And>call. effect (reset call) s r \<Longrightarrow>
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> True \<Longrightarrow> post s r reset_post (K True)"
    unfolding reset_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def icall_def
    apply vcg
    apply (rule_tac c=call and x=Super_reset_m and P'=reset_post in wp_post)
    using vcond_super_reset apply simp apply blast
    apply vcg
    done
qed

subsection \<open>Several bases (a diamond)\<close>

text \<open>\<open>Bank8\<close> inherits from \<open>Bank2\<close> (new method \<open>noop\<close>) and \<open>Bank3\<close> (overrides \<open>reset\<close>), which both inherit from \<open>Bank\<close>.\<close>

contract Bank8 is Bank2, Bank3

constructor
where
  "\<langle>skip\<rangle>"

verification sum_bal_bank8:
  bank.sum_bal
  deposit and
  withdraw and
  reset and
  noop
  for "Bank8"
proof -
  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (constructor call) s r \<Longrightarrow> post s r (K (K (inv_state bank.sum_bal))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: bank.sum_balI[OF bank_const] | auto)+
qed

end
