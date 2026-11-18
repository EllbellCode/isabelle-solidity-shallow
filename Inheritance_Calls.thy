theory Inheritance_Calls
  imports Solidity_Main
begin

section \<open>Inheritance: inherited methods that call internal methods\<close>

text \<open>
  A derived contract can verify an invariant its base never verified. Inherited methods that leave the invariant alone are proved
  automatically (see \<open>Inheritance_Invariants\<close>). An inherited method that calls an internal method cannot be proved that way: inside
  \<open>verification\<close> an internal method without a pair is known only as "anything", so the call could break the invariant.

  With \<open>declare [[verification_frame_calls = true]]\<close> the verification of an invariant that the base did not verify assumes, for the internal methods that
  the inherited methods call (directly or through other internal methods), the pair "if the invariant holds before the call it holds
  after". Their obligation is the usual one for a method that leaves the invariant alone (proved automatically when it does; it stays a goal
  when it does not), and the inherited methods that call them are proved by stepping over the calls with that pair. The option is off by
  default: it changes the conditions of such verifications.
\<close>

abbreviation "cla \<equiv> STR ''cla''"
abbreviation "clb \<equiv> STR ''clb''"

contract ClBase
  for cla: "SType.TValue TSint"

constructor
where
  "cla [] ::=\<^sub>s \<langle>sint\<rangle> 0"

cfunction cl_step
param "STR ''k''" : "SType.TValue TSint"
where
  "cla [] ::=\<^sub>s cla ~\<^sub>s [] \<langle>+\<rangle> stackLookup (STR ''k'') []" ,

cfunction cl_two
where
  "do {
    icall (cl_step 5);
    icall (cl_step 7)
  }" ,

cfunction cl_run external
where
  "do {
    icall cl_two;
    cla [] ::=\<^sub>s \<langle>sint\<rangle> 1;
    icall cl_two
  }" ,

cfunction cl_idle external
where
  "\<langle>skip\<rangle>"

ML \<open>
  (*run the commands in the text on the current theory; the message of the error, or NONE if they succeed*)
  fun failure thy text =
    let
      val trs = Outer_Syntax.parse_text thy (K thy) Position.start text
      val result = Exn.capture (fn () => fold (Toplevel.command_exception false) trs (Toplevel.make_state (SOME thy))) ()
    in (case result of Exn.Res _ => NONE | Exn.Exn e => SOME (Runtime.exn_message e)) end;

  fun expect_failure thy text fragment =
    (case failure thy text of
       NONE => error ("expected an error containing: " ^ fragment)
     | SOME msg => if String.isSubstring fragment msg then () else error ("wrong error: " ^ msg ^ "\nexpected: " ^ fragment));
\<close>

subsection \<open>A chain of calls, with a parameter\<close>

text \<open>
  \<open>ClDer\<close> adds \<open>clb\<close> and the invariant that \<open>clb\<close> holds a number. \<open>cl_run\<close> calls \<open>cl_two\<close> twice, which calls \<open>cl_step\<close> twice (with an argument);
  all three internal methods are inherited and write only \<open>cla\<close>. With the option set, \<open>cl_step\<close> and \<open>cl_two\<close> get the pair and are proved,
  and so is \<open>cl_run\<close>: only the constructor and the new method \<open>cl_setb\<close> remain.
\<close>

contract ClDer is ClBase
  for clb: "SType.TValue TSint"

constructor
where
  "clb [] ::=\<^sub>s \<langle>sint\<rangle> 5"

cfunction cl_setb external
where
  "clb [] ::=\<^sub>s \<langle>sint\<rangle> 6"

invariant cl_typed ct where
    "\<exists>v. fst ct clb = storage_data.Value (Uint v)"
  for "ClDer"

(*without the option the caller is a goal of the user*)
ML \<open>
  val thy = \<^theory>;
  val _ = expect_failure thy "verification cl_typed_off: cl_typed for \"ClDer\" done" "cl_run";
\<close>

declare [[verification_frame_calls = true]]

verification cl_typed_v:
  cl_typed
  for "ClDer"
proof -
  show "\<And>call. (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> effect (constructor call) s r \<Longrightarrow>
        post s r (K (K (inv_state cl_typed))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: cl_typedI | auto simp: storage_update_def | (drule sym, simp))+

  show "\<And>call. effect (cl_setb call) s r \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> inv_state cl_typed s \<Longrightarrow>
        post s r (K (K (inv_state cl_typed))) (K True)"
    unfolding cl_setb_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: cl_typedI | auto simp: storage_update_def | (drule sym, simp))+
qed

subsection \<open>A further derived contract reuses the pairs\<close>

text \<open>
  \<open>ClDer2\<close> verifies the same invariant: the obligations of all inherited methods, the internal ones included, come from the verification of
  \<open>ClDer\<close> (whose conditions have the pairs, and so do ours).
\<close>

contract ClDer2 is ClDer

constructor
where
  "\<langle>skip\<rangle>"

cfunction cl_noop external
where
  "\<langle>skip\<rangle>"

verification cl_typed_v2:
  clDer.cl_typed
  for "ClDer2"
proof -
  show "\<And>call. (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> effect (constructor call) s r \<Longrightarrow>
        post s r (K (K (inv_state clDer.cl_typed))) (K True)"
    unfolding constructor_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by (vcg wprules: clDer.cl_typedI[OF clDer_const] | auto simp: storage_update_def | (drule sym, simp))+

  show "\<And>call. effect (cl_noop call) s r \<Longrightarrow> (\<And>x h r. effect (call x) h r \<Longrightarrow> vcond x h r) \<Longrightarrow> inv_state clDer.cl_typed s \<Longrightarrow>
        post s r (K (K (inv_state clDer.cl_typed))) (K True)"
    unfolding cl_noop_def
    apply (erule post_exc_true, erule_tac post_wp)
    unfolding inv_state_def
    by vcg
qed

subsection \<open>Controls\<close>

text \<open>
  The pair is only assumed: its obligation is proved for the callee. \<open>ClZero\<close> verifies "\<open>cla\<close> is 0", which \<open>cl_step\<close> breaks. The caller
  \<open>cl_run\<close> is proved from the pair, but the obligation of \<open>cl_step\<close> stays a goal and cannot be proved: the verification does not finish.
\<close>

ML \<open>
  val thy = \<^theory>;
  val _ = expect_failure thy
    "contract ClZero is ClBase constructor where \"\<langle>skip\<rangle>\" cfunction cl_zz external where \"\<langle>skip\<rangle>\" \
    \invariant cl_zero z where \"fst z cla = storage_data.Value (Uint 0)\" for \"ClZero\" \
    \verification cl_zero_v: cl_zero for \"ClZero\" by (simp add: inv_state_def)"
    "cl_step";
  val _ = expect_failure thy
    "contract ClZero2 is ClBase constructor where \"\<langle>skip\<rangle>\" cfunction cl_zz2 external where \"\<langle>skip\<rangle>\" \
    \invariant cl_zero2 z where \"fst z cla = storage_data.Value (Uint 0)\" for \"ClZero2\" \
    \verification cl_zero2_v: cl_zero2 for \"ClZero2\" by (simp add: inv_state_def)"
    "Failed to apply initial proof method";
\<close>

end
