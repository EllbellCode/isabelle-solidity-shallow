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

section \<open>Initialisers\<close>

text \<open>
  The legacy pipeline of solc runs the state variable initialisers of the whole hierarchy before the first constructor. A contract states
  them as an \<open>initialiser\<close> of its constructor: the initialisers of all the contracts run first, the most base-like first, then the arguments
  of the base constructors are evaluated, then the constructors run. (The via-IR pipeline runs a class at a time; its initialisers are
  part of the body of the constructor.) An initialiser may read what a base constructor writes later: it sees the initial value.
\<close>

abbreviation "vp \<equiv> STR ''p''"
abbreviation "vq \<equiv> STR ''q''"
abbreviation "vr \<equiv> STR ''r''"

contract IA
  for vp: "SType.TValue TSint"
  and vq: "SType.TValue TSint"

constructor
param "STR ''x''": "SType.TValue TSint"
initialiser
  "vq [] ::=\<^sub>s \<langle>sint\<rangle> 100"
where
  "vp [] ::=\<^sub>s stackLookup (STR ''x'') []"

cfunction ia external
where
  "\<langle>skip\<rangle>"

contract IB is IA ("\<langle>sint\<rangle> 5")
  for vr: "SType.TValue TSint"

constructor
initialiser
  "vr [] ::=\<^sub>s vp ~\<^sub>s [] \<langle>+\<rangle> \<langle>sint\<rangle> 200"
where
  "vq [] ::=\<^sub>s vq ~\<^sub>s [] \<langle>+\<rangle> \<langle>sint\<rangle> 300"

cfunction ib external
where
  "\<langle>skip\<rangle>"

ML \<open>
  val txt_a = definition_text \<^theory> "Inheritance_Constructors.iA.constructor_def";
  val _ = check "IA: its initialiser before its constructor body"
    (increasing [first txt_a "100", first txt_a "stackLookup"]);

  val txt_b = definition_text \<^theory> "Inheritance_Constructors.iB.constructor_def";
  (*the initialisers (IA's, then IB's), then the argument for IA's parameter, then the bodies (IA's, then IB's)*)
  val _ = check "IB: initialisers, argument, bodies"
    (increasing [first txt_b "100", first txt_b "200", first txt_b "''x''", first txt_b "300"]);
  val _ = check "IB: each part once" (forall (fn d => length (positions txt_b d "0123456789") = 1) ["100", "200", "300"]);
\<close>

section \<open>A derived contract replaces the constructor of a base\<close>

text \<open>
  Solidity resolves the modifiers of a constructor virtually: the constructor of a base that uses a modifier which a derived contract overrides
  runs with the new modifier. The derived contract gives the body for it, \<open>replacing B "..."\<close>; a contract derived from it takes the replacement
  too, unless it replaces the body again.
\<close>

abbreviation "vs \<equiv> STR ''s''"
abbreviation "vk \<equiv> STR ''t''"

contract RA
  for vs: "SType.TValue TSint"

constructor
where
  "vs [] ::=\<^sub>s \<langle>sint\<rangle> 7"

cfunction ra external
where
  "\<langle>skip\<rangle>"

contract RB is RA
  for vk: "SType.TValue TSint"

constructor
replacing RA
  "vs [] ::=\<^sub>s \<langle>sint\<rangle> 8"
where
  "vk [] ::=\<^sub>s \<langle>sint\<rangle> 9"

cfunction rb external
where
  "\<langle>skip\<rangle>"

contract RC is RB

constructor
where
  "\<langle>skip\<rangle>"

cfunction rc external
where
  "\<langle>skip\<rangle>"

contract RD is RC

constructor
replacing RA
  "vs [] ::=\<^sub>s \<langle>sint\<rangle> 11"
where
  "\<langle>skip\<rangle>"

cfunction rd external
where
  "\<langle>skip\<rangle>"

ML \<open>
  fun numbers txt = map (fn n => (n, length (positions txt ("\<langle>sint\<rangle> " ^ n) "0123456789"))) ["7", "8", "9", "11"];
  val _ = check "RA keeps its own body" (numbers (definition_text \<^theory> "Inheritance_Constructors.rA.constructor_def") = [("7", 1), ("8", 0), ("9", 0), ("11", 0)]);
  val _ = check "RB runs the replacement" (numbers (definition_text \<^theory> "Inheritance_Constructors.rB.constructor_def") = [("7", 0), ("8", 1), ("9", 1), ("11", 0)]);
  val _ = check "RC takes RB's replacement" (numbers (definition_text \<^theory> "Inheritance_Constructors.rC.constructor_def") = [("7", 0), ("8", 1), ("9", 1), ("11", 0)]);
  val _ = check "RD replaces it again" (numbers (definition_text \<^theory> "Inheritance_Constructors.rD.constructor_def") = [("7", 0), ("8", 0), ("9", 1), ("11", 1)]);
\<close>

end
