theory Inheritance_Errors
  imports Solidity_Main
begin

section \<open>Inheritance: what is refused\<close>

text \<open>
  Each of the following commands is run and has to fail with the message shown (the check is on the message).
\<close>

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

contract E1
  for "STR ''x''": "SType.TValue TSint"

constructor
where
  "\<langle>skip\<rangle>"

cfunction f external
where
  "\<langle>skip\<rangle>"

contract E2
  for "STR ''y''": "SType.TValue TSint"

constructor
where
  "\<langle>skip\<rangle>"

cfunction f external
where
  "\<langle>skip\<rangle>"

ML \<open>
  val thy = \<^theory>;
  (*a base that does not exist*)
  val _ = expect_failure thy
    "contract E3 is NoSuchContract constructor where \"\<langle>skip\<rangle>\" cfunction g external where \"\<langle>skip\<rangle>\"" "unknown base contract";
  (*the same method in two unrelated bases has to be overridden*)
  val _ = expect_failure thy
    "contract E4 is E1, E2 constructor where \"\<langle>skip\<rangle>\" cfunction g external where \"\<langle>skip\<rangle>\"" "defined in unrelated bases";
  (*... and then it is accepted*)
  val _ = (case failure thy
    "contract E5 is E1, E2 constructor where \"\<langle>skip\<rangle>\" cfunction f external where \"\<langle>skip\<rangle>\"" of
      NONE => () | SOME msg => error ("override of f was refused: " ^ msg));
\<close>

section \<open>A base that assumes a locale\<close>

locale Callee = Keccak256 +
  assumes callee_ok: "ext_isc a \<Longrightarrow> \<exists>b. ext_result ep st bal a ''f()'' vs = Some (Bool b)"

contract E6 assuming Callee
  for "STR ''x''": "SType.TValue TSint"

constructor
where
  "\<langle>skip\<rangle>"

cfunction f external
where
  "\<langle>skip\<rangle>"

ML \<open>
  (*a derived contract has to assume what the base assumes*)
  val _ = expect_failure \<^theory>
    "contract E7 is E6 constructor where \"\<langle>skip\<rangle>\" cfunction g external where \"\<langle>skip\<rangle>\""
    "does not hold in this contract";
  (*... and then it is accepted*)
  val _ = (case failure \<^theory>
    "contract E7 is E6 assuming Callee constructor where \"\<langle>skip\<rangle>\" cfunction g external where \"\<langle>skip\<rangle>\"" of
      NONE => () | SOME msg => error ("a derived contract with the same assumption was refused: " ^ msg));
\<close>

section \<open>Memory parameters of a base constructor\<close>

contract E8
  for "STR ''x''": "SType.TValue TSint"

constructor
  memory "STR ''m''": "SType.DArray (SType.TValue TSint)"
where
  "\<langle>skip\<rangle>"

cfunction f external
where
  "\<langle>skip\<rangle>"

ML \<open>
  val _ = expect_failure \<^theory>
    "contract E9 is E8 (\"\<langle>skip\<rangle>\") constructor where \"\<langle>skip\<rangle>\" cfunction g external where \"\<langle>skip\<rangle>\""
    "memory parameters of a constructor are not";
\<close>

end
