theory Inheritance_Constructors
  imports Solidity_Main
begin

section \<open>Inheritance: constructors\<close>

text \<open>
  The constructors of a hierarchy run in one frame: first the parameters of all base constructors are bound (nearest base first, the
  arguments are those written in the inheritance lists), then the bodies run, the most base-like first, and last the body of the
  derived contract. The tests below check the definitions that the \<open>contract\<close> command generates.
\<close>

abbreviation "va \<equiv> STR ''a''"
abbreviation "vb \<equiv> STR ''b''"
abbreviation "vc \<equiv> STR ''c''"

contract CA
  for va: "SType.TValue TSint"

constructor
param "STR ''x''": "SType.TValue TSint"
where
  "va [] ::=\<^sub>s stackLookup (STR ''x'') []"

cfunction fa external
where
  "\<langle>skip\<rangle>"

(*The argument for CA is computed from the parameter of CB*)
contract CB is CA ("stackLookup (STR ''y'') []")
  for vb: "SType.TValue TSint"

constructor
param "STR ''y''": "SType.TValue TSint"
where
  "vb [] ::=\<^sub>s va ~\<^sub>s [] \<langle>+\<rangle> \<langle>sint\<rangle> 1"

(*... and the argument for CB is a constant: CC's constructor has no parameters*)
contract CC is CB ("\<langle>sint\<rangle> 7")
  for vc: "SType.TValue TSint"

constructor
where
  "vc [] ::=\<^sub>s vb ~\<^sub>s [] \<langle>+\<rangle> \<langle>sint\<rangle> 1"

cfunction fc external
where
  "\<langle>skip\<rangle>"

ML \<open>
  fun definition_text thy name =
    XML.content_of (YXML.parse_body (Syntax.string_of_term_global thy (Thm.prop_of (Global_Theory.get_thm thy name))));

  (*start positions of the occurrences of a text; an occurrence followed by one of the characters in `not_before` does not count*)
  fun positions txt sub not_before =
    let
      val n = size sub
      fun go i acc =
        if i + n > size txt then rev acc
        else if String.substring (txt, i, n) = sub
                andalso not (i + n < size txt andalso exists_string (fn c => c = String.substring (txt, i + n, 1)) not_before)
        then go (i + 1) (i :: acc)
        else go (i + 1) acc
    in go 0 [] end;

  fun check what ok = if ok then () else error ("Inheritance_Constructors: " ^ what);
  fun increasing (x :: y :: zs) = x < y andalso increasing (y :: zs) | increasing _ = true;
  fun first txt sub = (case positions txt sub "" of p :: _ => p | [] => error ("Inheritance_Constructors: missing " ^ sub ^ " in\n" ^ txt));
\<close>

ML \<open>
  val txt = definition_text \<^theory> "Inheritance_Constructors.cC.constructor_def";
  (*the parameters are bound first (CC's argument 7 for y, then CB's argument y for x), then the bodies run: a, b, c*)
  val _ = check "parameters before bodies in CC" (increasing (map (first txt) ["''y''", "''x''"]));
  val _ = check "bodies in the order a, b, c"
    (increasing (map (first txt) ["assign_storage_monad ?this va", "assign_storage_monad ?this vb", "assign_storage_monad ?this vc"]));
\<close>

section \<open>A diamond\<close>

contract DBase
  for va: "SType.TValue TSint"

constructor
where
  "va [] ::=\<^sub>s va ~\<^sub>s [] \<langle>*\<rangle> \<langle>sint\<rangle> 10 \<langle>+\<rangle> \<langle>sint\<rangle> 1"

cfunction dbase external
where
  "\<langle>skip\<rangle>"

contract DL is DBase
  for vb: "SType.TValue TSint"

constructor
where
  "va [] ::=\<^sub>s va ~\<^sub>s [] \<langle>*\<rangle> \<langle>sint\<rangle> 10 \<langle>+\<rangle> \<langle>sint\<rangle> 2"

cfunction dl external
where
  "\<langle>skip\<rangle>"

contract DR is DBase
  for vc: "SType.TValue TSint"

constructor
where
  "va [] ::=\<^sub>s va ~\<^sub>s [] \<langle>*\<rangle> \<langle>sint\<rangle> 10 \<langle>+\<rangle> \<langle>sint\<rangle> 3"

cfunction dr external
where
  "\<langle>skip\<rangle>"

contract DD is DBase, DL, DR

constructor
where
  "va [] ::=\<^sub>s va ~\<^sub>s [] \<langle>*\<rangle> \<langle>sint\<rangle> 10 \<langle>+\<rangle> \<langle>sint\<rangle> 4"

cfunction dd external
where
  "\<langle>skip\<rangle>"

text \<open>
  \<open>DD\<close> lists its bases from the most base-like (as Solidity does), so the constructors run \<open>DBase\<close>, \<open>DL\<close>, \<open>DR\<close>, \<open>DD\<close>: the
  constructor of \<open>DBase\<close> appears once, and the digits are appended in this order.
\<close>

ML \<open>
  val txt = definition_text \<^theory> "Inheritance_Constructors.dD.constructor_def";
  (*the bodies of the four constructors add the digits 1 (DBase), 2 (DL), 3 (DR), 4 (DD) in this order, DBase's once*)
  val digits = map (fn d => positions txt ("\<langle>+\<rangle> \<langle>sint\<rangle> " ^ d) "0123456789") ["1", "2", "3", "4"];
  val _ = check "each constructor body once" (forall (fn ps => length ps = 1) digits);
  val _ = check "DBase, DL, DR, DD" (increasing (map hd digits));
\<close>

end
