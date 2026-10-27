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

end
