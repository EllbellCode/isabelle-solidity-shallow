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

text \<open>
  \<open>Bank2\<close> adds \<open>resetTwice\<close>, which calls the inherited internal method \<open>reset\<close> twice, and \<open>noop\<close>. The proof for \<open>resetTwice\<close> uses
  the pair of \<open>reset\<close> (\<open>reset_post\<close>, from the verification of \<open>Bank\<close>) and a lemma that \<open>reset_post\<close> preserves the sum of the balances.
\<close>

context Solidity
begin

lemma reset_pres:
  fixes mp :: "'a::address valtype \<Rightarrow> 'a valtype storage_data" and s s' :: "'a state"
  assumes "SUMM (state.Storage s this) \<le> Balances s this"
      and "state.Storage s this balances = storage_data.Map mp"
      and "\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si)"
      and "reset_post s r s'"
    shows "\<exists>mp'. state.Storage s' this balances = storage_data.Map mp'
             \<and> (\<forall>y. \<exists>si. mp' y = storage_data.Value (Uint si)) \<and> SUMM (state.Storage s' this) \<le> Balances s' this"
proof -
  from assms(3) obtain y where y: "mp (Address msg_sender) = storage_data.Value (Uint y)" by (rule bal_msg_sender)
  from assms(4) assms(2,3) obtain mp' where
      m': "state.Storage s' this balances = storage_data.Map mp'" "mp' (Address msg_sender) = storage_data.Value (Uint 0)"
          "\<And>x. x \<noteq> msg_sender \<Longrightarrow> mp' (Address x) = mp (Address x)" "\<forall>y. \<exists>si. mp' y = storage_data.Value (Uint si)"
      and bs: "Balances s = Balances s'"
    by auto
  have a1: "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (mp (Address ad))))) \<le> Balances s' this"
    using assms(1,2) bs by simp
  have "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (mp' (Address ad))))) \<le> Balances s' this - unat y"
    by (rule sum_leq_sender[where mp = mp and mp' = mp' and sa = s' and s = s and y = y]) (use a1 y m'(2) bs m'(3) in auto)
  then have "SUMM (state.Storage s' this) \<le> Balances s' this" using m'(1) by simp
  with m' show ?thesis by blast
qed

end

contract Bank2 is Bank

constructor
where
  "\<langle>skip\<rangle>"

cfunction resetTwice external
where
  "do {
    icall reset;
    icall reset
  }" ,

cfunction noop external
where
  "\<langle>skip\<rangle>"

text \<open>
  \<open>deposit\<close>, \<open>withdraw\<close> and \<open>reset\<close> are inherited: their obligations (and the pair of \<open>reset\<close>) come from the
  verification of \<open>Bank\<close>. Only the constructor and the new methods remain. The methods need not be listed: a method that is not
  mentioned is verified like one that is listed without a pair of its own (a listed method is only needed to give it a pair).
\<close>

verification sum_bal_bank2:
  sum_bal  (*the invariant of Bank, found in the locale of the base; the others below write bank.sum_bal*)
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
       effect (resetTwice call) s r \<Longrightarrow> inv_state bank.sum_bal s \<Longrightarrow> post s r (K (K (inv_state bank.sum_bal))) (K True)"
    unfolding resetTwice_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def icall_def
    apply vcg
    apply (rule_tac c=call and x=Reset_m and P'=reset_post in wp_post)
    using vcond_reset apply simp apply blast
    apply vcg
    apply (rule_tac c=call and x=Reset_m and P'=reset_post in wp_post)
    using vcond_reset apply simp apply blast
    apply vcg
    apply (elim conjE exE)
    subgoal premises p for call sa saa
    proof -
      obtain mp where m: "state.Storage s this balances = storage_data.Map mp"
          "\<forall>y. \<exists>si. mp y = storage_data.Value (Uint si)"
          "(\<Sum>ad\<in>UNIV. unat (valtype.uint (storage_data.vt (mp (Address ad))))) \<le> Balances saa this"
        using p(2) by (rule bank.sum_balE[OF bank_const]) auto
      have b0: "Balances s this = Balances saa this" using p(3) by simp
      have a0: "SUMM (state.Storage s this) \<le> Balances s this" using m(1,3) b0 by simp
      have r1: "reset_post s Empty sa" using p(3,4,5) by simp
      obtain mp1 where m1: "state.Storage sa this balances = storage_data.Map mp1"
          "\<forall>y. \<exists>si. mp1 y = storage_data.Value (Uint si)" "SUMM (state.Storage sa this) \<le> Balances sa this"
        using reset_pres[OF a0 m(1,2) r1] by auto
      have r2: "reset_post sa Empty saa" using p(5,6) by simp
      obtain mp2 where m2: "state.Storage saa this balances = storage_data.Map mp2"
          "\<forall>y. \<exists>si. mp2 y = storage_data.Value (Uint si)" "SUMM (state.Storage saa this) \<le> Balances saa this"
        using reset_pres[OF m1(3,1,2) r2] by auto
      show ?thesis
        by (rule bank.sum_balI[OF bank_const, where mp = mp2]) (use m2 in auto)
    qed
    apply simp_all
    done

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

cfunction withdraw external
where
  "do {
    bal :: TSint;
    bal [] ::= balances ~\<^sub>s [\<langle>sender\<rangle>];
    icall reset;
    \<langle>transfer\<rangle> \<langle>sender\<rangle> (bal ~ [])
  }"

verification sum_bal_bank3:
  bank.sum_bal
  deposit and
  withdraw and
  reset (true_pre, reset_post)
  for "Bank3"
proof -
  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (constructor call) s r \<Longrightarrow> post s r (K (K (inv_state bank.sum_bal))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: bank.sum_balI[OF bank_const] | auto)+

  show
    d: "\<And>call.
      (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)
        \<Longrightarrow> effect (withdraw call) s r
        \<Longrightarrow> inv_state bank.sum_bal s
        \<Longrightarrow> post s r (K (K (inv_state bank.sum_bal))) (K True)"
    unfolding withdraw_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def icall_def
    apply (case_tac "msg_sender = this")
     apply (vcg wperules: bank.sum_balE[OF bank_const])
     apply (rule_tac s = msg_sender in subst,assumption)
     apply (vcg wperules: bank.sum_balE[OF bank_const])
    (* Apply precondition for internal method call *)
           apply (subgoal_tac "(\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)")
            apply (rule_tac c=call and x=Reset_m and P'=reset_post in wp_post)
    using vcond_reset apply simp apply blast
    (* End: Apply precondition for internal method call *)
             apply (vcg wperules: bank.sum_balE[OF bank_const])
             apply (rule_tac s=msg_sender in subst, assumption)
             apply (vcg wperules: bank.sum_balE[OF bank_const])
             apply (auto simp add:wpsimps)
      apply (vcg wperules: bank.sum_balE[OF bank_const])
         apply (auto simp add:wpsimps)
      apply (rule bal_msg_sender, assumption)
      apply (vcg wperules: bank.sum_balE[OF bank_const])
         apply (rule_tac mp = mp' in bank.sum_balI[OF bank_const])
          apply (auto simp add:wpsimps intro: sum_leq_this)
       apply (vcg wperules: bank.sum_balE[OF bank_const])
       apply (rule_tac mp = mpa in bank.sum_balI[OF bank_const])
        apply (vcg wperules: bank.sum_balE[OF bank_const])
    (* Apply precondition for internal method call *)
        apply (subgoal_tac "(\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r)")
         apply (rule_tac c=call and x=Reset_m and P'=reset_post in wp_post)
    using vcond_reset apply simp apply blast
    (* End: Apply precondition for internal method call *)
          apply (vcg wperules: bank.sum_balE[OF bank_const])
          apply (auto simp add:wpsimps)
     apply (vcg wperules: bank.sum_balE[OF bank_const])
        apply (auto simp add:wpsimps)
     apply (rule bal_msg_sender, assumption)
     apply (vcg wperules: bank.sum_balE[OF bank_const])
        apply (rule_tac mp = mp' in bank.sum_balI[OF bank_const])
         apply (auto simp add:wpsimps intro: sum_leq_sender)
      defer
      apply (vcg wperules: bank.sum_balE[OF bank_const])
    apply (rule_tac mp = mpa in bank.sum_balI[OF bank_const])
     apply (vcg wperules: bank.sum_balE[OF bank_const])
    done
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
  resetTwice and
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
