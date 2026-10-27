(*  Title:      Inheritance.ML

    Inheritance for the commands `contract` and `verification`:

      contract D is B1 ("arg"), B2 ... for ...

    A contract inherits the methods of its bases as aliases: the method of the base that defines it, applied to the dispatcher of the
    derived contract composed with an injection of the base's calls (a case over the base's datatype). The proofs about the bases are
    reused by `verification` (see the README, section Inheritance).

    The functions are used by Specification.ML (contract-time) and Verification.ML (verification-time).
*)

signature SOLIDITY_INHERITANCE =
sig
  (* theory data *)
  val ilookupN: theory -> string -> (string list * (string * string) list) option
  val abstract_of: theory -> string -> string list
  val own_methods_of: theory -> string -> string list

  (* names *)
  val super_src: string -> string option
  val c3_lin: theory -> string list -> string list
  val pred_args: theory -> string -> string -> string
  val local_instance: Proof.context -> string -> thm
  val plain: string -> string

  (* contract-time *)
  type prepared =
    {parent_args: (string * string list) list,   (* direct bases (lower case) with the argument texts given for their constructors *)
     ancestors: string list,                     (* all bases, nearest first *)
     base_members: (term * term) list,           (* state variables of the bases *)
     inherited_def: (string * string) list,      (* inherited method, base that defines it (hidden methods of super calls included) *)
     unimplemented: string list,                 (* abstract methods without an implementation *)
     alias_methods: ((((((binding * (bool * bool)) * ((term * term) list)) * ((term * term) list)) * ((term * term) list)) * string)) list}
  val prepare: theory ->
    {dname: string, name_lc: string, parents: (string * string list) list, abstract_names: string list, own_names: string list,
     ctor_arity: int} -> prepared
  val constructor_body: theory -> prepared -> {own_params: (string * string) list, own_init: string, own_body: string, body: string} -> string
  val register_instances: prepared -> local_theory -> local_theory
  val register: string -> prepared -> {own_params: (string * string) list, own_init: string, own_body: string} -> theory -> theory
  val note_const: string -> theory -> theory

  (* verification-time *)
  val pairs_and_overrides: theory -> string -> term ->
    (string * ((string * string) * string option) list) list ->
    (string * ((string * string) * string option) list) list * (string * string) list
  val read_invariant: Proof.context -> theory -> string -> typ -> string -> term
  val verified_with: theory -> string -> term -> bool
  val record_pairs: string -> term -> (string * ((string * string) * string option) list) list -> theory -> theory
  val user_goals: (term * term list) list -> bool list -> (term * term list) list list list ->
    (term * term list) list list -> (term * term list) list list
  val override_goals: Proof.context -> Solidity_Data.data -> term -> (string * string) list -> (term * term list) list list
  val discharge:
    {lthy: Proof.context, pi: morphism, data: Solidity_Data.data, ct: typ, vcond: term, vcond_thms: thm list, lems: (term * term list) list list list} ->
    (string * string) list -> thm list -> thm list list option list
  val frame_proofs:
    {lthy: Proof.context, pi: morphism, data: Solidity_Data.data, lems: (term * term list) list list list} ->
    (string * string) list -> thm list list option list
  val assemble: int -> (thm list -> thm list list option list) -> (term * term list) list list list -> thm list list -> thm list list
end

structure Solidity_Inheritance: SOLIDITY_INHERITANCE =
struct

open Solidity_Util
open Solidity_Data

(** theory data **)

(* contract (lower case name) |-> direct bases in declaration order, inherited methods with the contract that defines each *)
structure InheritN = Theory_Data
(
  type T = (string list * (string * string) list) Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

(* contract |-> constructor: parameters (name, type; as text), the body of this contract only, and the bases with the argument texts
   given to their constructors *)
structure CtorN = Theory_Data
(
  type T = ((string * string) list * string * (string * string list) list) Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

(* contract |-> its initialiser (the text of the `initialiser` clause of its constructor, "skip_monad" if there is none) *)
structure InitN = Theory_Data
(
  type T = string Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

(* contract |-> methods declared abstract (without body) and not implemented *)
structure AbstractN = Theory_Data
(
  type T = string list Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

(* contract |-> (pre, post[, revert]) pairs of its verifications, by invariant: a derived contract takes them as defaults for its
   inherited methods *)
structure VerifN = Theory_Data
(
  type T = (term * (string * (((string * string) * string option) list)) list) list Symtab.table
  val empty = Symtab.empty
  val merge = Symtab.merge (K true)
)

val ilookupN = Symtab.lookup o InheritN.get
val clookupN = Symtab.lookup o CtorN.get
fun abstract_of thy c = these (Symtab.lookup (AbstractN.get thy) c)

(* methods a contract defines itself (not inherited) *)
fun own_methods_of thy c =
  (case (mlookupN thy c, ilookupN thy c) of
     (SOME d, SOME (_, inh)) => filter_out (fn m => member (op =) (map fst inh) m) (map fst (#methods d))
   | (SOME d, NONE) => map fst (#methods d)
   | _ => [])


(** names **)

(* A hidden method `super_m` (`<x>_super_m` for a base x) runs the definition of m in the next base: the name it stands for *)
fun super_src n =
  if String.isPrefix "super_" n then SOME (String.extract (n, 6, NONE))
  else
    (case Substring.position "_super_" (Substring.full n) of
       (_, post) => if Substring.isEmpty post then NONE else SOME (Substring.string (Substring.triml 7 post)))

(* C3 linearisation, as Solidity does it: the bases of a contract are listed from the most base-like to the most derived, so the list
   is reversed; the result starts with the most derived contract *)
fun c3_lin thy parents =
  let
    fun parents_of c = (case ilookupN thy c of SOME (ps, _) => ps | NONE => [])
    fun merge seqs0 =
      let val seqs = filter_out null seqs0 in
        if null seqs then []
        else
          (case get_first (fn s => let val h = hd s in
                                     if forall (fn t => not (member (op =) (tl t) h)) seqs then SOME h else NONE end) seqs of
             NONE => error "inconsistent linearisation of the base contracts"
           | SOME h => h :: merge (map (fn s => if hd s = h then tl s else s) seqs))
      end
    fun lin c = c :: merge (map lin (rev (parents_of c)) @ [rev (parents_of c)])
  in merge (map lin (rev parents) @ [rev parents]) end

(* The arguments of the locale predicate of a contract, as a term string (the predicate takes only the parameters that the contract uses).
   The environment is the constant one: keccak256 is `id`, the timestamp is `ts`, the external function is `disp`. A contract whose
   predicate depends on the unspecified functions of the framework (hashing, ecrecover, calls to other contracts) has no such instance. *)
fun pred_args thy loc disp =
  let
    val (l, _) = Logic.dest_equals (Thm.prop_of (Global_Theory.get_thm thy (loc ^ "_def")))
    fun arg (Var ((a, _), _)) =
          if member (op =) ["encodeABI", "ecrecover", "ext_isc", "ext_result"] a then
            error ("Inheritance: the locale " ^ quote loc ^ " depends on the unspecified parameter " ^ quote a ^
              " (assuming clause, calls to other contracts, hashing of several values or ecrecover); not supported yet")
          else (case a of "keccak256" => "id" | "timestamp" => "ts" | "external" => disp | n => n)
      | arg _ = error "Unexpected locale predicate"
  in space_implode " " (map arg (snd (strip_comb l))) end

(* source text of a term as parsed (markup removed, one line) *)
fun plain s =
  XML.content_of (YXML.parse_body s)
  |> String.explode |> map (fn c => if c = #"\n" then #" " else c) |> filter Char.isPrint |> String.implode

(* The arguments of the locale predicate of a contract in the context of a derived contract (the parameters are fixed there under the same
   names), as a term string; the external function is replaced by `disp`. *)
fun local_pred_args thy loc disp =
  let
    val (l, _) = Logic.dest_equals (Thm.prop_of (Global_Theory.get_thm thy (loc ^ "_def")))
    fun arg (Var ((a, _), _)) = if a = "external" then disp else a
      | arg _ = error "Unexpected locale predicate"
  in space_implode " " (map arg (snd (strip_comb l))) end

(* The instance of the locale of a base in the locale of a derived contract: the base's predicate for the parameters of the derived contract
   and a constant external function, Z kw ts (\<lambda>_. X). The derived contract's own locale has everything the predicate asks for, except
   that its assumption on the external function is one of the derived contract's: the constant function satisfies the assumption of the base.
   The derived contract has to assume what the base assumes (the callee locale, if any). Works for bases that hash, call other contracts or
   have an `assuming` clause, which have no instance for a constant environment. *)
fun local_instance ctxt loc =
  let
    val thy = Proof_Context.theory_of ctxt
    val def = Global_Theory.get_thm thy (loc ^ "_def")
    val sol_gen = Global_Theory.get_thm thy "Contract.sol_gen"
    val goal = Syntax.read_term ctxt (loc ^ " " ^ local_pred_args thy loc "(\<lambda>_. X)") |> Syntax.check_term ctxt |> HOLogic.mk_Trueprop
    (*the method unfold_locales, as a tactic: it also uses the assumptions of the locale that the context belongs to*)
    fun intro context =
      Context_Tactic.NO_CONTEXT_TACTIC context
        (Method.evaluate (Method.Source (Token.make_src ("unfold_locales", Position.none) [])) context [])
      THEN ALLGOALS (Method.assm_tac context)
    val sol_here =
      Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (Syntax.read_term ctxt "Solidity keccak256 timestamp external" |> Syntax.check_term ctxt))
        (fn {context, ...} => intro context)
    val sol_const = sol_gen OF [sol_here]
    fun tac context =
      Local_Defs.unfold_tac context [def]
      THEN REPEAT (resolve_tac context [@{thm conjI}] 1)
      THEN ALLGOALS (TRY o resolve_tac context [sol_const])          (*the part about the external function and the hash*)
      THEN (fn st => if Thm.nprems_of st = 0 then Seq.single st else intro context st)   (*the callee locale, if the base has one*)
    fun why () =
      (case Seq.pull (tac ctxt (Goal.init (Thm.cterm_of ctxt goal))) of
         SOME (st, _) => "unproved: " ^ Thm.string_of_thm ctxt st
       | NONE => "no proof")
  in
    Goal.prove ctxt ["X"] [] goal (fn {context, ...} => tac context)
      handle ERROR msg =>
        error ("Inheritance: the locale of the base " ^ quote loc ^ " does not hold in this contract (a base's assumptions on the callee have to be assumed here too): "
               ^ msg ^ "; " ^ why ())
  end

(* the unconditional instance of a contract's locale: the locale predicate for a constant environment (id for keccak256) *)
fun const_instance ctxt thy loc =
  let
    val def = Global_Theory.get_thm thy (loc ^ "_def")
    val sol_const = Global_Theory.get_thm thy "Contract.sol_const"
    val goal = Syntax.read_term ctxt (loc ^ " " ^ pred_args thy loc "(\<lambda>_. X)") |> Syntax.check_term ctxt |> HOLogic.mk_Trueprop
  in
    Goal.prove ctxt ["ts", "X"] [] goal (fn {context, ...} => Local_Defs.unfold_tac context [def] THEN resolve_tac context [sol_const] 1)
  end


(** contract-time **)

type prepared =
  {parent_args: (string * string list) list,
   ancestors: string list,
   base_members: (term * term) list,
   inherited_def: (string * string) list,
   unimplemented: string list,
   alias_methods: ((((((binding * (bool * bool)) * ((term * term) list)) * ((term * term) list)) * ((term * term) list)) * string)) list}

fun prepare thy {dname, name_lc, parents, abstract_names, own_names, ctor_arity} : prepared =
  let
    val parent_args = map (fn (p, args) => (decapitalizeFirst p, map plain args)) parents
    val parent_names = map fst parent_args
    val _ = List.app (fn p => if is_some (mlookupN thy p) then () else error ("unknown base contract " ^ p)) parent_names
    val ancestors = c3_lin thy parent_names
    fun data_of a = the (mlookupN thy a)
    fun parents_of a = (case ilookupN thy a of SOME (ps, _) => ps | NONE => [])
    fun is_ancestor y x = member (op =) (c3_lin thy (parents_of x)) y

    (* state variables: those of the bases, the most base-like first, each once *)
    val base_members =
      fold (fn a => fn acc => acc @ filter_out (fn (n, _) => exists (fn (n', _) => n aconv n') acc) (#members (data_of a))) (rev ancestors) []

    (* The methods of the bases that this contract does not override, with the base that defines each. A concrete definition is
       preferred to an abstract declaration; several definitions in unrelated bases have to be overridden. *)
    val all_names =
      fold (fn a => fn acc => acc @ filter_out (fn n => member (op =) acc n orelse is_some (super_src n)) (map fst (#methods (data_of a))))
        (rev ancestors) []
    fun definers m = filter (fn a => member (op =) (own_methods_of thy a) m) ancestors
    fun is_abstract_in a m = member (op =) (abstract_of thy a) m
    fun concrete_definers m = (case filter_out (fn a => is_abstract_in a m) (definers m) of [] => definers m | ds => ds)
    fun definer m =
      (case concrete_definers m of
         [] => error ("no base defines " ^ m)
       | z :: others =>
           if forall (fn y => is_ancestor y z) others then z
           else error ("the method " ^ m ^ " is defined in unrelated bases; override it in " ^ dname))
    val inherited = map_filter (fn m => if member (op =) own_names m then NONE else SOME (m, definer m)) all_names
    val unimplemented = abstract_names @ map fst (filter (fn (m, z) => is_abstract_in z m) inherited)

    (* Super calls. For a method this contract defines and some base defines too, the hidden internal method super_m runs the definition
       of the nearest such base; for each base x that has such a hidden method itself, x_super_m runs the next definition of m after x in
       the linearisation of this contract (the methods of x that call super.m reach it through the injection). *)
    fun nonexternal z m = not (#external (lookup_safe (#methods (data_of z)) m))
    val own_hidden =
      map_filter (fn m =>
        (case concrete_definers m of
           [] => NONE
         | z :: _ => if nonexternal z m then SOME ("super_" ^ m, z) else NONE)) own_names
    val inherited_hidden =
      maps (fn x =>
        let
          val hidden = filter (fn n => String.isPrefix "super_" n) (map fst (#methods (data_of x)))
          val after = tl (snd (chop_prefix (fn a => a <> x) ancestors))
        in
          map_filter (fn h =>
            let val m = the (super_src h)
            in (case filter (fn y => member (op =) (own_methods_of thy y) m andalso not (is_abstract_in y m)) after of
                  [] => NONE
                | y :: _ => SOME (x ^ "_" ^ h, y)) end) hidden
        end) ancestors
    val inherited_def = inherited @ inherited_hidden @ own_hidden

    (* The alias of a method of the base z: that method applied to the dispatcher composed with the injection and, for the base's
       external function, to a function that ignores its argument and returns this contract's external function applied to the dispatcher. *)
    fun mk_alias (zname, zd) bind (md: mdata) =
      let
        val ddt = name_lc
        val bdt = zname
        (* the constructor of the base is never called through the dispatcher: its arguments are dropped and this contract's constructor
           gets arbitrary ones (the verification conditions of the two constructors do not depend on them) *)
        val base_ctor_arity = length (#parlist (#constructor zd) @ #memlist (#constructor zd))
        val ctor_case =
          bdt ^ "." ^ mk_dt_con_name con_name ^ String.concat (map (fn i => " ca" ^ string_of_int i) (0 upto base_ctor_arity - 1)) ^
          " \<Rightarrow> " ^ ddt ^ "." ^ mk_dt_con_name con_name ^ String.concat (replicate ctor_arity " undefined")
        (* a hidden method of the base becomes the hidden method of this contract for that base *)
        fun target m = if String.isPrefix "super_" m then zname ^ "_" ^ m else m
        fun method_case (m, mmd: mdata) =
          let val ps = String.concat (map (fn i => " cm" ^ string_of_int i) (0 upto length (#parlist mmd @ #memlist mmd @ #cdlist mmd) - 1))
          in bdt ^ "." ^ mk_dt_con_name m ^ ps ^ " \<Rightarrow> " ^ ddt ^ "." ^ mk_dt_con_name (target m) ^ ps end
        val injection = "(\<lambda>x. call (case x of " ^ space_implode " | " (ctor_case :: map method_case (#methods zd)) ^ "))"
        val (head, args) = strip_comb (fst (Logic.dest_equals (Thm.concl_of (#def md))))
        val cname = (case head of Const (c, _) => c | _ => error "inherited method: unexpected definition")
        fun arg_text t =
          let val n = (case t of Var ((n, _), _) => n | Free (n, _) => n | _ => error "inherited method: unexpected argument")
          in if n = "external" then "(\<lambda>cb. external call)" else n end
        val nps = length (#parlist md @ #memlist md @ #cdlist md)
        val body = "ALIAS " ^ space_implode " " (cname :: map arg_text args @ [injection] @ map (fn i => "par__" ^ string_of_int i) (0 upto nps - 1))
        fun mk_pars off pl = map (fn (((_, _), st), i) => (Free ("par__" ^ string_of_int i, dummyT), st)) (pl ~~ (off upto off + length pl - 1))
        val parl = mk_pars 0 (#parlist md)
        val meml = mk_pars (length (#parlist md)) (#memlist md)
        val cdl = mk_pars (length (#parlist md) + length (#memlist md)) (#cdlist md)
      in
        (((((bind, (#external md, #payable md)), parl), meml), cdl), body)
      end
    fun src_of m = the_default m (super_src m)
    fun alias_of (m, z) = mk_alias (z, data_of z) (Binding.name m) (lookup_safe (#methods (data_of z)) (src_of m))
    (* a method can only call a method defined before it: the aliases come first, then the hidden methods, then the own methods *)
    val (hidden_def, plain_def) = List.partition (fn (m, _) => is_some (super_src m)) inherited_def
  in
    {parent_args = parent_args, ancestors = ancestors, base_members = base_members, inherited_def = inherited_def,
     unimplemented = unimplemented, alias_methods = map alias_of plain_def @ map alias_of hidden_def}
  end

(* The constructor of a derived contract: the parameters of the constructors of all bases are bound first, the nearest base first (the
   arguments given for a base may use the parameters of a nearer one); then the bodies of the bases run, the most base-like first; then
   the body of this contract. An empty body (the transpiler writes skip_monad) adds nothing to the sequence.

   A contract may have an `initialiser` (the state variable initialisers of the legacy pipeline of solc): the initialisers of all the
   contracts of the hierarchy run first, the most base-like first, then the arguments of the base constructors are evaluated, then the
   constructors run as above. Without an initialiser anywhere the sequence is the one above. (The via-IR pipeline runs a class at a time:
   its initialisers belong to the body of its constructor.) *)
fun constructor_body thy ({parent_args, ancestors, ...}: prepared) {own_params = _, own_init, own_body, body} =
  let
    fun given r = (case r of SOME [] => NONE | _ => r)
    fun ctor_args x =
      (case given (AList.lookup (op =) parent_args x) of
         SOME a => SOME a
       | NONE => get_first (fn y => (case clookupN thy y of SOME (_, _, ps) => given (AList.lookup (op =) ps x) | NONE => NONE)) ancestors)
    fun block x =
      (case clookupN thy x of
         NONE => ([], [])
       | SOME (params, ctor_body, _) =>
           let
             (* no class of the hierarchy gives the arguments: a base that is still abstract, their value is unspecified *)
             val args = the_default (map (K "undefined") params) (ctor_args x)
             val _ = if length params = length args then ()
                     else error ("the constructor of " ^ x ^ " takes " ^ string_of_int (length params) ^ " argument(s)")
             fun value_type ty =
               if String.isPrefix "SType.TValue " ty then String.extract (ty, 13, NONE)
               else error "only value parameters of a base constructor are supported (memory parameters of a constructor are not)"
             fun decl ((pname, ptype), arg) =
               "decl " ^ value_type ptype ^ " (" ^ pname ^ "); assign_stack_monad (" ^ pname ^ ") [] (" ^ arg ^ ")"
           in (map decl (params ~~ args), [ctor_body]) end)
    fun is_skip t = (plain t = "skip_monad" orelse plain t = "\<langle>skip\<rangle>")
    val inits = filter_out is_skip (map_filter (Symtab.lookup (InitN.get thy)) (rev ancestors) @ [own_init])
    val parts =
      inits @ maps (fst o block) ancestors @ filter_out is_skip (maps (snd o block) (rev ancestors)) @ (if is_skip own_body then [] else [own_body])
  in
    if null ancestors andalso null inits then body
    else if null parts then own_body
    else "do { " ^ space_implode "; " parts ^ " }"
  end

(* The definitions of the base methods behind the aliases, unconditionally, for the monotonicity proofs and the final tactic of
   `verification`: they hold in the locale of the derived contract (instance of each base's locale there). Also noted as <base>_const,
   the instance for use with the invariant rules of the base (wprules: base.invI[OF base_const]). *)
fun register_instances ({inherited_def, ...}: prepared) lthy =
  let
    val thy = Proof_Context.theory_of lthy
    fun for_base z lthy =
      let
        val zd = the (mlookupN thy z)
        val inst = local_instance lthy (#locale zd)
        fun def_of (md: mdata) =
          (case head_of (fst (Logic.dest_equals (Thm.concl_of (#def md)))) of
             Const (c, _) => Global_Theory.get_thm thy (c ^ "_def")
           | _ => error "inherited method: unexpected definition")
        val unfoldings =
          map (fn (m, _) => def_of (lookup_safe (#methods zd) (the_default m (super_src m))) OF [inst])
            (filter (fn (_, z') => z' = z) inherited_def)
      in
        lthy
        |> Local_Theory.note ((Binding.name (z ^ "_const"), []), [inst]) |> snd
        |> Local_Theory.note ((Binding.name (z ^ "_unfoldings"), [Attrib.internal \<^here> (K (Named_Theorems.add "Contract.alias_defs"))]), unfoldings) |> snd
      end
  in fold for_base (distinct (op =) (map snd inherited_def)) lthy end

(* the data a derived contract leaves for the contracts and verifications that build on it *)
fun register name_lc ({parent_args, inherited_def, unimplemented, ...}: prepared) {own_params, own_init, own_body} thy =
  thy
  |> CtorN.map (Symtab.update (name_lc, (own_params, own_body, parent_args)))
  |> InitN.map (Symtab.update (name_lc, own_init))
  |> AbstractN.map (Symtab.update (name_lc, unimplemented))
  |> (if null parent_args then I else InheritN.map (Symtab.update (name_lc, (map fst parent_args, inherited_def))))

(* the fact <c>_const: the contract's locale holds for a constant external function (not for a contract that depends on the unspecified
   functions of the framework); needed to use the contract's invariant rules from a derived contract *)
fun note_const lc thy =
  (let
     val th = const_instance (Proof_Context.init_global thy) thy lc
   in Global_Theory.store_thm (Binding.name (lc ^ "_const"), th) thy |> snd end)
  handle ERROR _ => thy


(** verification-time **)

(* The (pre, post[, revert]) pairs of a derived contract: the ones given, with the pairs of the base for the methods without any (and for
   the hidden methods of super calls); and the overrides whose pairs differ from the base's, for which the base's condition has to follow. *)
fun pairs_and_overrides thy name_lc invariant prepost =
  let
    val (parents, inherited_def) = the_default ([], []) (ilookupN thy name_lc)
    val ancestors = if null parents then [] else c3_lin thy parents
    fun pairs_of x m =
      (case find_first (fn (inv, _) => inv aconv invariant) (these (Symtab.lookup (VerifN.get thy) x)) of
         SOME (_, pp) => AList.lookup (op =) pp m
       | NONE => NONE)
    fun texts ps = map (fn ((a, b), _) => (plain a, plain b)) ps
    val hidden = filter (fn h => is_some (super_src h) andalso not (exists (fn (n, _) => n = h) prepost)) (map fst inherited_def)
    fun default m = get_first (fn x => (case pairs_of x m of SOME ps => if null ps then NONE else SOME ps | NONE => NONE)) ancestors
    fun fill (name, ps) =
      let val src = the_default name (super_src name)
      in
        if null ps andalso exists (fn x => member (op =) (map fst (#methods (the (mlookupN thy x)))) src) ancestors
        then (name, these (default src))
        else (name, ps)
      end
    val prepost = map fill (prepost @ map (fn h => (h, [])) hidden)
    fun overrides z =
      map_filter (fn (c, ps) =>
        if member (op =) (map fst (#methods (the (mlookupN thy z)))) c andalso not (null ps)
           andalso (case pairs_of z c of SOME zp => texts ps <> texts zp | NONE => false)
        then SOME (z, c) else NONE) prepost
  in (prepost, maps overrides (distinct (op =) (map snd inherited_def))) end

(* The invariant named in a verification of a derived contract: a name that the contract's locale does not know is looked up in the
   locales of the bases, nearest first (so `triv` stands for `res.triv`). *)
fun read_invariant lthy thy name_lc tp text =
  let
    val inv = readAs lthy tp text
    fun unresolved t = (case t of Free _ => true | _ => false)
    val ancestors = (case ilookupN thy name_lc of SOME (parents, _) => c3_lin thy parents | NONE => [])
    val name = plain text
    fun qualified a =
      if String.isSubstring " " name then NONE
      else SOME (readAs lthy tp (#locale (the (mlookupN thy a)) ^ "." ^ name)) handle ERROR _ => NONE
  in
    if not (unresolved inv) then inv
    else (case get_first (fn t => if unresolved t then NONE else SOME t) (map_filter qualified ancestors) of SOME t => t | NONE => inv)
  end

(* did the contract (lower case name) have a verification of this invariant? Only then are the obligations of its methods available to the
   contracts that inherit them. *)
fun verified_with thy x invariant =
  exists (fn (inv, _) => inv aconv invariant) (these (Symtab.lookup (VerifN.get thy) x))

fun record_pairs name_lc invariant prepost =
  VerifN.map (Symtab.map_default (name_lc, []) (cons (invariant, prepost)))

(* The goals the user has to prove: the constructor, the methods that are not inherited, and the implication for each override. *)
fun user_goals lem is_inh lems ovr_goals =
  lem :: flat (map2 (fn inhd => fn groups => if inhd then [] else groups) is_inh lems) @ ovr_goals

(* For an override with its own pairs: this contract's condition for the method implies the condition of the base that defines it. *)
fun override_goals lthy (data: data) vcond ovr =
  let
    val thy = Proof_Context.theory_of lthy
    fun goal (z, m) =
      let
        val zd = the (mlookupN thy z)
        val vdef = Global_Theory.get_thm thy (#locale zd ^ ".vcond_def")
        val base_vcond = map_types Logic.unvarifyT_global (head_of (fst (Logic.dest_equals (Thm.concl_of vdef))))
        val msg_sender = Syntax.read_term lthy "msg_sender"
        val this = Syntax.read_term lthy "this"
        val md = lookup_safe (#methods data) m
        val bmd = lookup_safe (#methods zd) m
        val frees = map (fst #> Free) (#parlist md @ #memlist md @ #cdlist md)
        val prem = HOLogic.mk_Trueprop (vcond $ list_comb (instantiate_b_a2 (#dt_const md), frees) $ s $ r)
        val concl = HOLogic.mk_Trueprop (list_comb (base_vcond, [msg_sender, this, list_comb (instantiate_b_a2 (#dt_const bmd), frees), s, r]))
      in [(fold_rev Logic.all frees (Logic.mk_implies (prem, concl)), [])] end
  in map goal ovr end

(* The obligations of an inherited method are discharged by those of the base that defines it (the facts <base>_external.<m>_vc): this
   contract's external function composed with the injection is the base's external function, and the hypothesis on the dispatcher is
   translated along the injection. `impls` are the proved implications of the overrides. *)
fun discharge {lthy, pi, data, ct, vcond, vcond_thms, lems} inherited_defs impls =
  let
    val thy = Proof_Context.theory_of lthy
    val vcond_thms = map (Morphism.thm pi) vcond_thms
    fun for_base bname (mname, md: mdata) groups =
      let
        val bd = the (mlookupN thy bname)
        val bext = bname ^ "_external"
        val be_def = Proof_Context.get_thm lthy (bext ^ "_def")
        val bax_def = Proof_Context.get_thm lthy (bext ^ "_axioms_def")
        val b_const = local_instance lthy (#locale bd)
        val vcond_base = map (fn th => th OF [b_const]) (Proof_Context.get_thms lthy (#locale bd ^ ".vcond"))
        val case_rules =
          Proof_Context.get_thms lthy (fst (dest_Type (#dt_type bd)) ^ ".case") @ Proof_Context.get_thms lthy (fst (dest_Type ct) ^ ".case")
        val pnames = map (fst #> fst) (#parlist md @ #memlist md @ #cdlist md)
        val k = length groups
        val alias_def = Morphism.thm pi (#def md)
        fun prove_group (i, group) =
          let
            val sname = the_default mname (super_src mname)
            val vc = Proof_Context.get_thm lthy (bext ^ "." ^ (if k = 1 then sname ^ "_vc" else sname ^ "_vc" ^ string_of_int (i + 1)))
            fun tac {context, prems, params, ...} =
              let
                val effect_prem = nth prems 0
                val hyp = nth prems 1
                val effect_prem' = Local_Defs.unfold context [alias_def] effect_prem
                val call_t = Thm.term_of (snd (hd params))
                (* the hypothesis on the dispatcher as an object-level statement *)
                val hyp_goal =
                  HOLogic.mk_Trueprop
                    (HOLogic.mk_all ("x", ct, HOLogic.mk_all ("h", stateT, HOLogic.mk_all ("r", rT,
                      HOLogic.mk_imp (effect $ (call_t $ Free ("x", ct)) $ Free ("h", stateT) $ Free ("r", rT),
                                      vcond $ Free ("x", ct) $ Free ("h", stateT) $ Free ("r", rT))))))
                val hyp_obj =
                  Goal.prove context [] [] hyp_goal
                    (fn {context = c1, ...} =>
                       resolve_tac c1 [@{thm allI}] 1 THEN resolve_tac c1 [@{thm allI}] 1 THEN resolve_tac c1 [@{thm allI}] 1
                       THEN resolve_tac c1 [@{thm impI}] 1 THEN resolve_tac c1 [hyp] 1 THEN assume_tac c1 1)
                val external_inv = Proof_Context.get_thm context "external_inv" OF [hyp_obj]
                (* the base's external assumption for this contract's external function *)
                val base_external_goal =
                  Syntax.parse_term context (bext ^ " " ^ local_pred_args thy bext "(\<lambda>cb. external callx)")
                  |> map_aterms (fn Free ("callx", _) => call_t | t => t)
                  |> Syntax.check_term context |> HOLogic.mk_Trueprop
                val base_external =
                  Goal.prove context [] [] base_external_goal
                    (fn {context = c2, ...} =>
                       Local_Defs.unfold_tac c2 [be_def, bax_def]
                       THEN resolve_tac c2 [@{thm conjI}] 1
                       THEN resolve_tac c2 [b_const] 1
                       THEN resolve_tac c2 [@{thm allI}] 1 THEN resolve_tac c2 [@{thm allI}] 1 THEN resolve_tac c2 [@{thm impI}] 1
                       THEN resolve_tac c2 [external_inv] 1)
                (* the base's hypothesis on the dispatcher, from ours, by cases over the base's calls *)
                fun hyp_tac i =
                  Subgoal.FOCUS_PREMS (fn {context = c3, prems = p3, params = pr3, ...} =>
                    let
                      val e = hd p3
                      val e' = Thm.equal_elim (Drule.beta_eta_conversion (Thm.cprop_of e)) e
                      val v = hyp OF [e']
                    in
                      Induct_Tacs.case_tac c3 (fst (hd pr3)) [] NONE 1
                      THEN ALLGOALS (cut_facts_tac [v] THEN'
                        ((asm_full_simp_tac (c3 addsimps case_rules) THEN' resolve_tac c3 impls THEN' assume_tac c3)
                         ORELSE' asm_full_simp_tac (c3 addsimps (vcond_thms @ vcond_base @ case_rules))))
                    end) context i
              in
                resolve_tac context [vc] 1
                THEN resolve_tac context [base_external] 1
                THEN resolve_tac context [effect_prem'] 1
                THEN hyp_tac 1
                THEN ALLGOALS (resolve_tac context (drop 2 prems))
              end
          in [Goal.prove lthy ("s" :: "r" :: pnames) [] (fst (hd group)) (fn {context, ...} => Subgoal.FOCUS_PREMS tac context 1)] end
      in map_index prove_group groups end
  in
    map2 (fn (m, md) => fn groups =>
            (case AList.lookup (op =) inherited_defs m of
               SOME bname => SOME (for_base bname (m, md) groups)
             | NONE => NONE))
      (#methods data) lems
  end

(* An inherited method of a base that did not verify this invariant (a derived contract's own invariant, for instance on its own state
   variables): the proof of a method that leaves the invariant alone is tried -- unfold the alias and the definition in the base, weakest
   precondition, then simplify the updates of the storage. It succeeds when the method does not call other methods (their obligations
   would need the pairs of those methods) and does not change what the invariant looks at. What it does not prove stays a goal for the user. *)
fun frame_proofs {lthy, pi, data, lems} foreign_defs =
  let
    val thy = Proof_Context.theory_of lthy
    val timeout = Time.fromSeconds 30
    fun for_method (mname, md: mdata) groups =
      (case AList.lookup (op =) foreign_defs mname of
         NONE => NONE
       | SOME bname =>
           let
             val bd = the (mlookupN thy bname)
             val b_const = local_instance lthy (#locale bd)
             val base_def = Global_Theory.get_thm thy (#locale bd ^ "." ^ mname ^ "_def") OF [b_const]
             val alias_def = Morphism.thm pi (#def md)
             val pnames = map (fst #> fst) (#parlist md @ #memlist md @ #cdlist md)
             val get = Proof_Context.get_thm lthy
             fun isar ctxt txt =
               Context_Tactic.NO_CONTEXT_TACTIC ctxt (Method.evaluate (fst (Method.read_closure_input ctxt (Input.string txt))) ctxt [])
             fun tac ctxt =
               Local_Defs.unfold_tac ctxt [alias_def, base_def]
               THEN eresolve_tac ctxt [get "post_exc_true"] 1
               THEN eresolve_tac ctxt [get "post_wp"] 1
               THEN Local_Defs.unfold_tac ctxt [get "inv_state_def"]
               THEN Context_Tactic.NO_CONTEXT_TACTIC ctxt
                      (Method.evaluate (Method.Source (Token.make_src ("vcg", Position.none) [])) ctxt [])
               THEN isar ctxt "auto simp: storage_update_def"
               THEN TRY (isar ctxt "drule sym, simp")
             fun prove (group: (term * term list) list) =
               (case Exn.capture (Timeout.apply timeout (fn () =>
                   Goal.prove lthy ("s" :: "r" :: pnames) [] (fst (hd group)) (fn {context, ...} => tac context))) () of
                  Exn.Res th => SOME th
                | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else NONE)
             val proofs = map prove groups
           in
             if forall is_some proofs then SOME (map (fn p => [the p]) proofs) else NONE
           end)
  in map2 (fn (m, md) => fn groups => for_method (m, md) groups) (#methods data) lems end

(* All rules the final theorem needs, in the order of the facts: the constructor, then the groups of each method; those of the inherited
   methods come from `discharge_with` (it needs the implications of the overrides, the last `n_ovr` of the user's rules). *)
fun assemble n_ovr discharge_with lems user_rules0 =
  let
    val user_rules = take (length user_rules0 - n_ovr) user_rules0
    val impls = flat (drop (length user_rules0 - n_ovr) user_rules0)
    fun go [] _ = []
      | go ((auto, groups) :: rest) us =
          (case auto of
             SOME rs => rs @ go rest us
           | NONE => let val n = length groups in take n us @ go rest (drop n us) end)
  in hd user_rules :: go (discharge_with impls ~~ lems) (tl user_rules) end

end
