theory Inheritance_Invariants
  imports Solidity_Main
begin

section \<open>Inheritance: invariants of derived contracts\<close>

text \<open>
  A derived contract can verify the invariant of its base: the obligations of the inherited methods are those of the base (see
  \<open>Inheritance_Bank\<close>). It can also verify an invariant of its own, for example one about its own state variables. The base
  never verified that invariant, so there is nothing to reuse. For an inherited method \<open>verification\<close> then tries the usual proof of
  a method that leaves the invariant alone: unfold the method, compute the weakest precondition, simplify the updates of the storage.
  It succeeds for a method that does not call other methods and does not touch what the invariant looks at (or leaves it as the
  invariant demands). What it does not prove remains a goal, like the constructor and the new methods. The methods need not be listed
  in \<open>verification\<close>.
\<close>

abbreviation "count \<equiv> STR ''count''"
abbreviation "cap \<equiv> STR ''cap''"

contract Counter
  for count: "SType.TValue TSint"

constructor
where
  "count [] ::=\<^sub>s \<langle>sint\<rangle> 0"

cfunction inc external
where
  "count [] ::=\<^sub>s count ~\<^sub>s [] \<langle>+\<rangle> \<langle>sint\<rangle> 1" ,

cfunction clear external
where
  "count [] ::=\<^sub>s \<langle>sint\<rangle> 0"

invariant count_val cv where
    "\<exists>v. fst cv count = storage_data.Value (Uint v)"
  for "Counter"

verification count_val_v:
  count_val
  inc and
  clear
  for "Counter"
proof -
  show "\<And>call. (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> effect (constructor call) s r \<Longrightarrow>
        post s r (K (K (inv_state count_val))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: count_valI | auto simp: storage_update_def | (drule sym, simp))+

  show "\<And>call. effect (inc call) s r \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> inv_state count_val s \<Longrightarrow>
        post s r (K (K (inv_state count_val))) (K True)"
    unfolding inc_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: count_valI | auto simp: storage_update_def | (drule sym, simp))+

  show "\<And>call. effect (clear call) s r \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> inv_state count_val s \<Longrightarrow>
        post s r (K (K (inv_state count_val))) (K True)"
    unfolding clear_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: count_valI | auto simp: storage_update_def | (drule sym, simp))+
qed

subsection \<open>Several verifications of one contract\<close>

text \<open>
  A contract can verify several invariants, one \<open>verification\<close> each. The first keeps the names \<open>vcond\<close>, \<open>vcond_<m>\<close>; a further one adds
  \<open>_<name of the verification>\<close> to them (here \<open>vcond_count_any_v\<close>). A derived contract that verifies an invariant that one of the
  verifications of its base verified reuses the proofs of that verification.
\<close>

invariant count_any ca where
    "True"
  for "Counter"

verification count_any_v:
  count_any
  inc and
  clear
  for "Counter"
proof -
  show "\<And>call. (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond_count_any_v x h r) \<Longrightarrow> effect (constructor call) s r \<Longrightarrow>
        post s r (K (K (inv_state count_any))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: count_anyI | auto simp: storage_update_def | (drule sym, simp))+

  show "\<And>call. effect (inc call) s r \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond_count_any_v x h r) \<Longrightarrow> inv_state count_any s \<Longrightarrow>
        post s r (K (K (inv_state count_any))) (K True)"
    unfolding inc_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: count_anyI | auto simp: storage_update_def | (drule sym, simp))+

  show "\<And>call. effect (clear call) s r \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond_count_any_v x h r) \<Longrightarrow> inv_state count_any s \<Longrightarrow>
        post s r (K (K (inv_state count_any))) (K True)"
    unfolding clear_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: count_anyI | auto simp: storage_update_def | (drule sym, simp))+
qed

subsection \<open>An invariant on the state of the derived contract\<close>

text \<open>
  \<open>Capped\<close> adds \<open>cap\<close>, which is at least 10 and only grows. \<open>inc\<close> and \<open>clear\<close> are inherited and do not touch \<open>cap\<close>: they are
  proved automatically. Only the constructor and \<open>raise\<close> remain.
\<close>

contract Capped is Counter
  for cap: "SType.TValue TSint"

constructor
where
  "cap [] ::=\<^sub>s \<langle>sint\<rangle> 10"

cfunction raise external
where
  "cap [] ::=\<^sub>s cap ~\<^sub>s [] \<langle>+\<rangle> \<langle>sint\<rangle> 1"

invariant cap_big cb where
    "\<exists>v. 10 \<le> unat v \<and> fst cb cap = storage_data.Value (Uint v)"
  for "Capped"

verification cap_big_v:
  cap_big
  for "Capped"
proof -
  show "\<And>call. (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> effect (constructor call) s r \<Longrightarrow>
        post s r (K (K (inv_state cap_big))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: cap_bigI | auto simp: storage_update_def | (drule sym, simp))+

  show "\<And>call. effect (raise call) s r \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> inv_state cap_big s \<Longrightarrow>
        post s r (K (K (inv_state cap_big))) (K True)"
    unfolding raise_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply (vcg wprules: cap_bigI)
    apply (auto simp: storage_update_def)
     apply (simp add: unat_word_ariths mod_less)
    apply (drule sym, simp)
    done
qed

text \<open>
  \<open>Twin\<close> verifies \<open>count_any\<close> too: \<open>inc\<close> and \<open>clear\<close> come from the second verification of \<open>Counter\<close> (the first one verified another invariant);
  the constructor and the new method \<open>noop\<close> are left.
\<close>

contract Twin is Counter

constructor
where
  "\<langle>skip\<rangle>"

cfunction noop external
where
  "\<langle>skip\<rangle>"

verification twin_any:
  counter.count_any
  for "Twin"
proof -
  show "\<And>call. (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> effect (constructor call) s r \<Longrightarrow>
        post s r (K (K (inv_state counter.count_any))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: counter.count_anyI[OF counter_const] | auto simp: storage_update_def | (drule sym, simp))+

  show "\<And>call. effect (noop call) s r \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> inv_state counter.count_any s \<Longrightarrow>
        post s r (K (K (inv_state counter.count_any))) (K True)"
    unfolding noop_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    apply (vcg_all wprules: counter.count_anyI[OF counter_const] wperules: counter.count_anyE[OF counter_const])
    apply (all \<open>(auto simp: storage_update_def)?\<close>)
    done
qed

subsection \<open>A stronger invariant: overriding what would break it\<close>

text \<open>
  \<open>Frozen\<close> keeps \<open>count\<close> at 0, a stronger invariant than the base's. \<open>inc\<close> would break it, so \<open>Frozen\<close> overrides \<open>inc\<close> (that is a goal);
  \<open>clear\<close> sets \<open>count\<close> to 0 and is proved automatically.
\<close>

contract Frozen is Counter

constructor
where
  "\<langle>skip\<rangle>"

cfunction inc external
where
  "\<langle>skip\<rangle>"

invariant count_zero cz where
    "fst cz count = storage_data.Value (Uint 0)"
  for "Frozen"

verification count_zero_v:
  count_zero
  for "Frozen"
proof -
  show "\<And>call. (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> effect (constructor call) s r \<Longrightarrow>
        post s r (K (K (inv_state count_zero))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: count_zeroI | auto simp: storage_update_def | (drule sym, simp))+

  show "\<And>call. effect (inc call) s r \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> inv_state count_zero s \<Longrightarrow>
        post s r (K (K (inv_state count_zero))) (K True)"
    unfolding inc_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by vcg
qed

subsection \<open>Inherited methods that update mappings\<close>

text \<open>
  The invariant types all state variables of the contract, so an inherited method that writes into a mapping has to be shown to keep the mapping
  typed. \<open>verification\<close> proves this itself (a second strategy after the one for methods that leave the state alone): the typing of the mappings is
  taken apart into functions (\<open>typed_map1\<close>, \<open>typed_map2\<close> in \<open>WP.thy\<close>), the updates are simplified, and the introduction rule of the invariant is
  applied with the updated functions as witnesses. \<open>Tagged\<close> inherits \<open>put\<close> (writes one entry of \<open>stock\<close>) and \<open>copy\<close> (reads one entry and writes
  another); the invariant is about the new variable \<open>tag\<close>. Only the constructor and \<open>retag\<close> remain.
\<close>

abbreviation "stock \<equiv> STR ''stock''"
abbreviation "tag \<equiv> STR ''tag''"

contract Ledger
  for stock: "SType.TMap (SType.TValue TAddress) (SType.TValue TSint)"

constructor
where
  "\<langle>skip\<rangle>"

cfunction put external
param "STR ''who''" : "SType.TValue TAddress"
and "STR ''amount''" : "SType.TValue TSint"
where
  "assign_storage_monad stock [stackLookup (STR ''who'') []] (stackLookup (STR ''amount'') [])" ,

cfunction copy external
param "STR ''from''" : "SType.TValue TAddress"
and "STR ''to''" : "SType.TValue TAddress"
where
  "assign_storage_monad stock [stackLookup (STR ''to'') []] (stock ~\<^sub>s [stackLookup (STR ''from'') []])"

contract Tagged is Ledger
  for tag: "SType.TValue TSint"

constructor
where
  "tag [] ::=\<^sub>s \<langle>sint\<rangle> 1"

cfunction retag external
where
  "tag [] ::=\<^sub>s tag ~\<^sub>s [] \<langle>+\<rangle> \<langle>sint\<rangle> 1"

invariant tag_set ts where
    "\<exists>v. fst ts tag = storage_data.Value (Uint v)"
  for "Tagged"

verification tag_set_v:
  tag_set
  for "Tagged"
proof -
  show "\<And>call. (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> effect (constructor call) s r \<Longrightarrow>
        post s r (K (K (inv_state tag_set))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: tag_setI | auto simp: storage_update_def | (drule sym, simp))+

  show "\<And>call. effect (retag call) s r \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> inv_state tag_set s \<Longrightarrow>
        post s r (K (K (inv_state tag_set))) (K True)"
    unfolding retag_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: tag_setI | auto simp: storage_update_def | (drule sym, simp))+
qed

subsection \<open>Overriding a method whose pair mentions \<open>msg_value\<close>\<close>

text \<open>
  The condition of a verification depends on the variables of the contract that the pairs mention, so its parameters are not always the same.
  An override whose pair differs from the base's has to imply the base's: this goal is built with the parameters of the base's condition
  (this test would fail if they were assumed to be \<open>msg_sender\<close> and \<open>this\<close>). The base's postcondition is about the final state only, the
  override's relates the initial and the final state and says more.
\<close>

abbreviation "ovx \<equiv> STR ''x''"
abbreviation "ovy \<equiv> STR ''y''"

abbreviation "ovd \<equiv> STR ''done''"

contract OvA
  for ovx: "SType.TValue TSint"
  and ovd: "SType.TValue TBool"

constructor
where
  "\<langle>skip\<rangle>"

cfunction h external
param "STR ''v''" : "SType.TValue TSint"
where
  "ovx [] ::=\<^sub>s stackLookup (STR ''v'') []"

contract OvB is OvA
  for ovy: "SType.TValue TSint"

constructor
where
  "\<langle>skip\<rangle>"

cfunction h external
param "STR ''v''" : "SType.TValue TSint"
where
  "do { ovx [] ::=\<^sub>s stackLookup (STR ''v'') []; ovy [] ::=\<^sub>s \<langle>sint\<rangle> 2 }"

invariant ov_ok t where "True" for "OvA"

abbreviation (in Solidity) ov_pre_g where "ov_pre_g _ \<equiv> True"
abbreviation (in Solidity) ov_sp_g_a where "ov_sp_g_a s r s' \<equiv> state.Storage s' this STR ''x'' = storage_data.Value (Uint 1)"
abbreviation (in Solidity) ov_sp_g_b where "ov_sp_g_b s r s' \<equiv> ov_sp_g_a s r s' \<and> state.Storage s' this STR ''y'' = storage_data.Value (Uint 2)"
abbreviation (in Solidity) ov_rv_g where "ov_rv_g s \<equiv> False"
abbreviation (in Solidity) ov_pre_h where "ov_pre_h _ _ \<equiv> True"
abbreviation (in Solidity) ov_sp_h_a where "ov_sp_h_a v st rr st' \<equiv> state.Storage st' this STR ''x'' = storage_data.Value (Uint v)"
abbreviation (in Solidity) ov_sp_h_b where "ov_sp_h_b v st rr st' \<equiv> ov_sp_h_a v st rr st' \<and> state.Storage st' this STR ''y'' = storage_data.Value (Uint 2)"
abbreviation (in Solidity) ov_rv_h where "ov_rv_h v s \<equiv> msg_value < 0"

verification ov_ok_a:
  ov_ok
  h (ov_pre_h, ov_sp_h_a, ov_rv_h)
  for "OvA"
  apply (all \<open>unfold constructor_def h_def\<close>)
  apply (all \<open>(erule post_exc_const, erule_tac post_wp)\<close>)
  apply (all \<open>unfold inv_state_def\<close>)
  apply (all \<open>vcg_all wprules: ov_okI wperules: ov_okE\<close>)
  apply (all \<open>(clarsimp simp: wpsimps dest!: wpdrules)?\<close>)
  apply (all \<open>(vcg_all wprules: ov_okI wperules: ov_okE)?\<close>)
  apply (all \<open>(clarsimp simp: wpsimps dest!: wpdrules)?\<close>)
  apply (all \<open>(auto dest: sym simp: storage_update_def kdequals_def word_gt_0 unat_eq_zero not_less_zero)?\<close>)
  done

verification ov_ok_b:
  ovA.ov_ok
  h (ov_pre_h, ov_sp_h_b, ov_rv_h)
  for "OvB"
  apply -
  apply (all \<open>(unfold constructor_def h_def)?\<close>)
  apply (all \<open>(erule post_exc_const, erule_tac post_wp)?\<close>)
  apply (all \<open>(unfold inv_state_def)?\<close>)
  apply (all \<open>(vcg_all wprules: ovA.ov_okI[OF ovA_const] wperules: ovA.ov_okE[OF ovA_const])?\<close>)
  apply (all \<open>(clarsimp simp: wpsimps dest!: wpdrules)?\<close>)
  apply (all \<open>(vcg_all wprules: ovA.ov_okI[OF ovA_const] wperules: ovA.ov_okE[OF ovA_const])?\<close>)
  apply (all \<open>(clarsimp simp: wpsimps dest!: wpdrules)?\<close>)
  apply (all \<open>(auto dest: sym simp: storage_update_def kdequals_def word_gt_0 unat_eq_zero not_less_zero vcond_h ovA.vcond_h[OF ovA_const])?\<close>)
  done

end
