theory Solidity_Source_Diff
  imports Solidity_Main Solidity_Ext
begin

section \<open>Testing the command \<open>solidity\<close> against reference specifications\<close>

text \<open>
  A test theory contains reference specifications (the contract commands that \<open>transpile.py --inherit\<close> writes for a Solidity file, each in a theory of its own)
  and the Solidity source with every contract renamed \<open>S_<name>\<close>. \<open>Source_Diff.check\<close> creates the contracts of the source with the command and compares, class by class,
  the definition theorems of the constructor and of the methods with those of the reference, as terms. Any difference is an error.
\<close>

ML \<open>
structure Source_Diff =
struct
  (*the numeric suffix of the copy of an overloaded library function is an id of solc's tree: not comparable*)
  fun norm_id s =
    if not (String.isSubstring "__" s) then s
    else
      let
        fun go [] = []
          | go (#"_" :: c :: r) = if Char.isDigit c then #"_" :: #"N" :: go (drop_digits r) else #"_" :: go (c :: r)
          | go (c :: r) = c :: go r
        and drop_digits r = (case r of c :: r' => if Char.isDigit c then drop_digits r' else r | [] => [])
      in String.implode (go (String.explode s)) end

  fun rename (gen, hand) =
    let
      fun fix_hidden s =
        if String.isSubstring "__s_" s then
          let
            val (pre, rest) = Substring.position "__s_" (Substring.full s)
            val r = Substring.string (Substring.triml 4 rest)
          in Substring.string pre ^ "__" ^ String.map Char.toLower (String.substring (r, 0, 1)) ^ String.extract (r, 1, NONE) end
        else s
      fun fix_lib s =
        let val parts = String.fields (fn c => c = #".") s val l = List.last parts in
          if String.isPrefix "S_" l then String.concatWith "." (take (length parts - 1) parts @ [String.extract (l, 2, NONE)]) else s
        end
      val rn = fn s => norm_id (fix_lib (fix_hidden (if String.isPrefix gen s then hand ^ unprefix gen s else s)))
      fun typ (Type (c, Ts)) = Type (rn c, map typ Ts)
        | typ T = T
      fun trm (Const (c, T)) = Const (rn c, typ T)
        | trm (Free (x, T)) = Free (x, typ T)
        | trm (Var (x, T)) = Var (x, typ T)
        | trm (Abs (x, T, b)) = Abs (x, typ T, trm b)
        | trm (t $ u) = trm t $ trm u
        | trm t = t
    in trm end

  (*`decl T x` is by definition `init (default T) x`*)
  fun norm thy =
    Raw_Simplifier.rewrite_term thy
      (map (Local_Defs.meta_rewrite_rule (Proof_Context.init_global thy))
        (@{thm decl_def} :: @{thm comp_def} :: @{thms default.simps})) []

  fun run_text thy text =
    let
      val trs = Outer_Syntax.parse_text thy (K thy) Position.start text
    in Toplevel.theory_of (fold (Toplevel.command_exception false) trs (Toplevel.make_state (SOME thy))) end

  fun lc s = String.map Char.toLower (String.substring (s, 0, 1)) ^ String.extract (s, 1, NONE)

  (*options: configuration options set before the command; classes: (reference theory, [(contract, [constructor and method names])])*)
  fun check thy options file classes =
    let
      val text = File.read (Path.append (Resources.master_directory thy) (Path.basic file))
      val me = Context.theory_name {long = false} thy
      val thy' = run_text thy (implode (map (fn o_ => "declare [[" ^ o_ ^ "]]\n") options) ^ "solidity \<open>" ^ text ^ "\<close>")
      fun get th n m = Global_Theory.get_thm th (n ^ "." ^ m ^ "_def") |> Thm.prop_of
      fun get_alt th n m =
        (get th n m handle ERROR _ =>
           (get th n ("S_" ^ m) handle ERROR _ =>
              let
                val pre = n ^ "."
                val names = Facts.fold_static (fn (nm, _) => if String.isPrefix pre nm andalso String.isSuffix "_def" nm then cons nm else I) (Global_Theory.facts_of th) []
                fun base nm = norm_id (let val b = String.substring (nm, size pre, size nm - size pre - 4) in if String.isPrefix "S_" b then String.extract (b, 2, NONE) else b end)
              in
                (case filter (fn nm => base nm = norm_id m) names of
                   [nm] => Thm.prop_of (Global_Theory.get_thm th nm)
                 | _ => error ("no definition " ^ m))
              end))
      fun one gen_thy (cname, ms) =
        let
          val mine = me ^ "." ^ lc ("S_" ^ cname)
          val gen = gen_thy ^ "." ^ lc cname
          val ren = rename (mine, gen)
          fun cmp m =
            let
              val a = norm thy' (rename ("\<^none>", "") (get thy' gen m))
              val b = norm thy' (ren (get_alt thy' mine m))
            in if a aconv b then NONE else SOME (cname ^ "." ^ m) end
        in map_filter cmp ms end
      val bad = maps (fn (g, cs) => maps (one g) cs) classes
    in
      if null bad then () else error ("different from the reference: " ^ commas bad)
    end
end
\<close>

end
