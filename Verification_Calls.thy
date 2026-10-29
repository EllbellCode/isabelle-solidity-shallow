theory Verification_Calls
  imports Solidity_Main
begin

section \<open>Verifying a method that calls another: the rule \<open>wpc_<method>\<close>\<close>

text \<open>
  A method that calls an internal method with a pair \<open>(pre, post, rv)\<close> is verified through the pair: the hypothesis on the dispatcher (which every
  verification has) gives what is known about the call, and \<open>verification\<close> turns it into the rule \<open>wpc_<method>\<close>. After \<open>vcg_all\<close> has stopped at
  \<open>wp (call M_m ..)\<close>, \<open>rule_tac call=call in wpc_<method>\<close> steps over it: three goals remain, the precondition, what follows from the postcondition
  when the call does not revert, and what follows when it does. The revert condition of the caller (exact, in both directions) can then use the one of the callee.
\<close>

abbreviation "cx \<equiv> STR ''cx''"

contract CcA
  for cx: "SType.TValue TSint"

constructor
where
  "cx [] ::=\<^sub>s \<langle>sint\<rangle> 0"

cfunction setOne
where
  "cx [] ::=\<^sub>s \<langle>sint\<rangle> 1" ,

cfunction run external
where
  "icall setOne"

invariant cc_ok cc where "\<exists>n. fst cc cx = storage_data.Value (Uint n)" for "CcA"

abbreviation (in Solidity) pre_one where "pre_one s \<equiv> \<exists>n. state.Storage s this cx = storage_data.Value (Uint n)"
abbreviation (in Solidity) sp_one where "sp_one st rr st' \<equiv> state.Storage st' this cx = storage_data.Value (Uint 1)"
abbreviation (in Solidity) rv_one where "rv_one st \<equiv> False"
abbreviation (in Solidity) pre_run where "pre_run st \<equiv> True"
abbreviation (in Solidity) sp_run where "sp_run st rr st' \<equiv> state.Storage st' this cx = storage_data.Value (Uint 1)"
abbreviation (in Solidity) rv_run where "rv_run st \<equiv> False"

verification cc_ok_v:
  cc_ok
  setOne (pre_one, sp_one, rv_one) and
  run (pre_run, sp_run, rv_run)
  for "CcA"
  apply (all \<open>unfold constructor_def setOne_def run_def icall_def\<close>)
  apply (all \<open>(erule post_exc_const, erule_tac post_wp)\<close>)
  apply (all \<open>(unfold inv_state_def)?\<close>)
  apply (all \<open>(vcg_all wprules: cc_okI wperules: cc_okE)?\<close>)
  apply (all \<open>(rule_tac call=call in wpc_setOne)?\<close>)
  apply (all \<open>(clarsimp simp: wpsimps dest!: wpdrules)?\<close>)
  apply (all \<open>(vcg_all wprules: cc_okI wperules: cc_okE)?\<close>)
  apply (all \<open>(clarsimp simp: wpsimps dest!: wpdrules)?\<close>)
  apply (all \<open>(auto dest: sym simp: storage_update_def)?\<close>)
  done

end
