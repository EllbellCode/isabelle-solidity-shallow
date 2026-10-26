theory Inheritance_Abstract
  imports Solidity_Main
begin

abbreviation(in Solidity) tp where "tp (_::'a state) \<equiv> True"
abbreviation(in Solidity) tq where
  "tq start_state return_value end_state \<equiv> state.Storage end_state this (STR ''x'') = storage_data.Value (Uint 0)"

section \<open>Inheritance: abstract methods\<close>

text \<open>
  An abstract method (\<open>cfunction reset abstract\<close>) has no body. The pair declared for it in the verification of the base is the
  specification every implementation has to meet; methods of the base that call it are proved against that specification.
  A derived contract implements the method and proves only that implementation.
\<close>

text \<open>An abstract contract: reset has no body; twice calls it twice.\<close>

contract Res
  for "STR ''x''": "SType.TValue TSint"

constructor
where
  "\<langle>skip\<rangle>"

cfunction reset abstract ,

cfunction twice external
where
  "do {
    icall reset;
    icall reset
  }"

invariant triv sb where
  "True"
  for "Res"

verification triv_v:
  triv
  twice and
  reset (tp, tq)
  for "Res"
proof -
  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (constructor call) s r \<Longrightarrow> post s r (K (K (inv_state triv))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: trivI | auto)+

  show "\<And>call. effect (reset call) s r \<Longrightarrow>
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> True \<Longrightarrow> post s r tq (K True)"
    unfolding reset_def
    apply (erule post_exc_true, erule_tac post_wp)
    by vcg

  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (twice call) s r \<Longrightarrow> inv_state triv s \<Longrightarrow> post s r (K (K (inv_state triv))) (K True)"
    unfolding twice_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def icall_def
    apply vcg
    apply (rule_tac c=call and x=Reset_m and P'=tq in wp_post)
    using vcond(2) apply simp apply blast
    apply vcg
    apply (rule_tac c=call and x=Reset_m and P'=tq in wp_post)
    using vcond(2) apply simp apply blast
    apply vcg
    done
qed



text \<open>An implementation: it must meet the pair declared for the abstract method; the method that calls it is proved by the base.\<close>

contract Impl is Res

constructor
where
  "\<langle>skip\<rangle>"

cfunction reset
where
  "STR ''x'' [] ::=\<^sub>s \<langle>sint\<rangle> 0"

verification triv_i:
  res.triv
  twice and
  reset
  for "Impl"
proof -
  show "\<And>call.
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow>
       effect (constructor call) s r \<Longrightarrow> post s r (K (K (inv_state res.triv))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: res.trivI[OF res_const] | auto)+

  show "\<And>call. effect (reset call) s r \<Longrightarrow>
       (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> True \<Longrightarrow> post s r tq (K True)"
    unfolding reset_def
    apply (erule post_exc_true, erule_tac post_wp)
    by vcg
qed

end
