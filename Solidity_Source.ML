(*  Title:      Solidity_Source.ML

    A front end for Solidity source text: the command

      solidity <open> contract Bank { mapping(address => uint) balances; function deposit() external payable { ... } } <close>

    reads the contracts in the text (a lexer, a recursive-descent parser and an elaborator, in this order) and creates them like the
    `contract` command does: the result of the elaboration is the data of that command (state variables, constructor, methods, with
    the bodies as text of monadic terms that the command then reads). The rules of the translation are those of the transpiler
    (transpile.py, which gets the types from solc); `source_diff/diff.py` compares the two term by term.

    The semantics are the framework's. Anything outside the supported subset is refused with a message and the position.
*)

signature SOLIDITY_SOURCE =
sig
  type method = {name: string, external: bool, payable: bool, params: (string * string) list, body: string}
  type contract =
    {name: string,
     parents: (string * string list) list,
     variables: (string * string) list,
     payable: bool,
     params: (string * string) list,
     init: string,
     repl: (string * string) list,
     body: string,
     methods: method list,
     pre: string,                      (*commands to run before the contract is created (the locale of the assumptions on callees)*)
     assuming: string option}
  val value_guard: bool Config.T
  val abbreviations: bool Config.T
  val modifier_abbreviations: bool Config.T
  val show_output: bool Config.T
  val show: contract -> string
  val read: Proof.context -> string -> contract list
end

structure Solidity_Source: SOLIDITY_SOURCE =
struct

type method = {name: string, external: bool, payable: bool, params: (string * string) list, body: string}

type contract =
  {name: string,
   parents: (string * string list) list,
   variables: (string * string) list,
   payable: bool,
   params: (string * string) list,
   init: string,
   repl: (string * string) list,
   body: string,
   methods: method list,
   pre: string,
   assuming: string option}

(*[[solidity_value_guard]]: a function or constructor that is not payable starts with `value_guard` (Solidity reverts when msg.value > 0)*)
val value_guard = Attrib.setup_config_bool \<^binding>\<open>solidity_value_guard\<close> (K true)

(*[[solidity_abbreviations]]: `abbreviation balances \<equiv> STR ''balances''` for the state variables of a contract, as in hand-written specifications*)
val abbreviations = Attrib.setup_config_bool \<^binding>\<open>solidity_abbreviations\<close> (K false)

(*[[solidity_modifier_abbreviations]]: every use of a modifier is a locale abbreviation (`mod_onlyOwner (body)`) instead of the inlined text: the elaborated
  definitions are the same terms, but they print short*)
val modifier_abbreviations = Attrib.setup_config_bool \<^binding>\<open>solidity_modifier_abbreviations\<close> (K false)

(*[[solidity_show]]: the command writes, as a message of the command (the output panel of the IDE), what each contract is under the hood: the text of the
  `contract` command that creates it (its state variables, constructor and methods with the bodies as monadic terms)*)
val show_output = Attrib.setup_config_bool \<^binding>\<open>solidity_show\<close> (K true)

(*the text of the `contract` command for a contract, in the form that transpile.py writes*)
fun show (c: contract) : string =
  let
    fun q s = "\"" ^ s ^ "\""
    val name_of = (fn n => if member (op =) ["contract", "constructor", "cfunction", "external", "memory", "param", "calldata", "payable", "assuming", "is",
                                            "abstract", "initialiser", "replacing", "verification", "invariant", "for", "and", "where", "record", "begin",
                                            "end", "fun", "lemma", "theorem", "definition", "datatype", "type", "section", "text", "ML", "in", "imports",
                                            "keywords", "theory", "context", "locale"] n then q n else n)
    val head =
      "contract " ^ #name c
      ^ (if null (#parents c) then ""
         else " is " ^ space_implode ", " (map (fn (p, args) => p ^ (if null args then "" else " (" ^ space_implode ", " (map q args) ^ ")")) (#parents c)))
      ^ (case #assuming c of SOME l => " assuming " ^ l | NONE => "")
    val vars = map_index (fn (i, (n, st)) => "  " ^ (if i = 0 then "for " else "and ") ^ q n ^ " : " ^ q st) (#variables c)
    fun params ps = map_index (fn (i, (n, st)) => (if i = 0 then "param " else "and ") ^ q n ^ " : " ^ q st) ps
    val ctor =
      ["constructor" ^ (if #payable c then " payable" else "")] @ params (#params c)
      @ (if #init c = "" orelse #init c = "skip_monad" then [] else ["initialiser", "  " ^ q (#init c)])
      @ map_index (fn (i, (x, txt)) => (if i = 0 then "replacing " else "and ") ^ x ^ "\n  " ^ q txt) (#repl c)
      @ ["where", "  " ^ q (#body c)]
    fun meth (i, (m: method)) =
      ["", "cfunction " ^ name_of (#name m) ^ (if #external m then " external" else "") ^ (if #payable m then " payable" else "")]
      @ params (#params m) @ ["where", "  " ^ q (#body m) ^ (if i < length (#methods c) - 1 then " ," else "")]
  in
    cat_lines ([head] @ vars @ [""] @ ctor @ maps meth (map_index I (#methods c)))
  end

(** errors **)

exception Err of int * string   (*offset, message*)

fun err pos msg = raise Err (pos, msg)

fun position_of text pos =
  let
    val n = Int.min (pos, String.size text)
    fun go i line col = if i >= n then (line, col) else if String.sub (text, i) = #"\n" then go (i + 1) (line + 1) 1 else go (i + 1) line (col + 1)
    val (line, col) = go 0 1 1
  in "line " ^ string_of_int line ^ ", column " ^ string_of_int col end

(** lexer **)

datatype tok = Id of string | Num of string | Str of string | HexStr of string | Sym of string | Doc of string | Eof

type token = tok * int

fun is_alpha c = Char.isAlpha c orelse c = #"_" orelse c = #"$"
fun is_alnum c = Char.isAlphaNum c orelse c = #"_" orelse c = #"$"

val symbols3 = ["<<=", ">>=", "**="]
val symbols2 = ["=>", "==", "!=", "<=", ">=", "&&", "||", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "++", "--", "<<", ">>", "**"]

fun drop_while_ws cs = (case cs of c :: r => if c = #" " orelse c = #"\t" then drop_while_ws r else cs | [] => [])

fun lex text : token list =
  let
    val n = String.size text
    fun at i = if i < n then String.sub (text, i) else #"\000"
    fun sub i j = String.substring (text, i, j - i)
    fun skip_comment i =
      if i >= n then err i "unterminated comment"
      else if at i = #"*" andalso at (i + 1) = #"/" then i + 2 else skip_comment (i + 1)
    fun line_comment i = if i >= n orelse at i = #"\n" then i else line_comment (i + 1)
    fun scan_while p i = if i < n andalso p (at i) then scan_while p (i + 1) else i
    fun skip_pragma i = if i >= n then n else if at i = #";" then i + 1 else skip_pragma (i + 1)
    fun go i acc =
      if i >= n then rev ((Eof, n) :: acc)
      else
        let val c = at i in
          if Char.isSpace c then go (i + 1) acc
          else if c = #"/" andalso at (i + 1) = #"/" andalso at (i + 2) = #"/" then
            let val j = line_comment i in go j ((Doc (sub (i + 3) j), i) :: acc) end
          else if c = #"/" andalso at (i + 1) = #"/" then go (line_comment i) acc
          else if c = #"/" andalso at (i + 1) = #"*" andalso at (i + 2) = #"*" andalso at (i + 3) <> #"/" then
            let
              val j = skip_comment (i + 3)
              val inner = sub (i + 3) (j - 2)
              val lines = map (fn l => let val l' = String.implode (drop_while_ws (String.explode l)) in if String.isPrefix "*" l' then String.extract (l', 1, NONE) else l' end) (String.fields (fn c => c = #"\n") inner)
            in go j ((Doc (space_implode "\n" lines), i) :: acc) end
          else if c = #"/" andalso at (i + 1) = #"*" then go (skip_comment (i + 2)) acc
          else if is_alpha c then
            let val j = scan_while is_alnum i val s = sub i j in
              if s = "pragma" then go (skip_pragma j) acc
              else if (s = "hex" orelse s = "unicode") andalso at j = #"\"" then
                let
                  fun close k = if k >= n then err i "unterminated string" else if at k = #"\"" then k else close (k + 1)
                  val k = close (j + 1)
                in go (k + 1) (((if s = "hex" then HexStr (sub (j + 1) k) else Str (sub (j + 1) k)), i) :: acc) end
              else go j ((Id s, i) :: acc)
            end
          else if Char.isDigit c orelse (c = #"." andalso Char.isDigit (at (i + 1))) then
            let
              val j =
                if c = #"0" andalso (at (i + 1) = #"x" orelse at (i + 1) = #"X")
                then scan_while (fn d => Char.isHexDigit d orelse d = #"_") (i + 2)
                else
                  let
                    val a = scan_while (fn d => Char.isDigit d orelse d = #"_") i
                    val b = if at a = #"." andalso Char.isDigit (at (a + 1)) then scan_while (fn d => Char.isDigit d orelse d = #"_") (a + 1) else a
                  in
                    if (at b = #"e" orelse at b = #"E") andalso (Char.isDigit (at (b + 1)) orelse ((at (b + 1) = #"-" orelse at (b + 1) = #"+") andalso Char.isDigit (at (b + 2))))
                    then scan_while Char.isDigit (b + 2) else b
                  end
            in go j ((Num (sub i j), i) :: acc) end
          else if c = #"\"" orelse c = #"'" then
            let
              fun close j = if j >= n then err i "unterminated string" else if at j = #"\\" then close (j + 2) else if at j = c then j else close (j + 1)
              val j = close (i + 1)
            in go (j + 1) ((Str (sub (i + 1) j), i) :: acc) end
          else
            let
              val s3 = if i + 3 <= n then sub i (i + 3) else ""
              val s2 = if i + 2 <= n then sub i (i + 2) else ""
            in
              if member (op =) symbols3 s3 then go (i + 3) ((Sym s3, i) :: acc)
              else if member (op =) symbols2 s2 then go (i + 2) ((Sym s2, i) :: acc)
              else if String.isSubstring (String.str c) "{}()[];,.=+-*/%<>!?:&|^~" then go (i + 1) ((Sym (String.str c), i) :: acc)
              else err i ("unexpected character " ^ quote (String.str c))
            end
        end
  in go 0 [] end

(** syntax tree **)

datatype ty =
    TyInt of bool * int            (*signed, bits*)
  | TyAddr of bool                 (*payable*)
  | TyBool
  | TyBytesN of int
  | TyBytes
  | TyString
  | TyMapping of ty * ty
  | TyUser of string               (*a struct, enum, contract, interface or library*)
  | TyArray of ty * IntInf.int option
  | TyConst of IntInf.int          (*the type of a constant integer expression (only during elaboration)*)
  | TyStrLit of string             (*a string literal (only during elaboration)*)

datatype expr =
    ENum of string
  | EStr of string
  | EHex of string
  | EBool of bool
  | EId of string * int
  | EType of ty * int              (*an elementary type name used as a value: uint8(x), type(uint8)*)
  | EMember of expr * string * int
  | EIndex of expr * expr * int
  | ECall of expr * expr list * int
  | EBin of string * expr * expr * int
  | EUn of string * expr * int     (*! - ~ ++ -- (prefix), ++post --post, delete*)
  | ECond of expr * expr * expr * int
  | EAssign of string * expr * expr * int
  | ETuple of expr list * int
  | ECallOpts of expr * (string * expr) list * int   (*f{value: v}*)

datatype stmt =
    SDecl of ty * string * string * expr option * int   (*type, name, data location, initial value*)
  | SExpr of expr * int
  | SIf of expr * stmt * stmt option
  | SWhile of expr * stmt
  | SDoWhile of stmt * expr
  | SBreak of int
  | SContinue of int
  | SFor of stmt option * expr option * expr option * stmt
  | SBlock of stmt list
  | SUnchecked of stmt list
  | SReturn of expr option * int
  | SEmit of expr * int
  | SRevert of expr option * int
  | SPlaceholder of int
  | SUnsupported of string * int
  | SLowCall of string * expr * expr * int          (*(bool ok, ) = a.call{value: v}("")*)
  | SReturnValue of expr           (*synthetic: the value of the function, last element of its do-block*)
  | SReturnVar of string           (*synthetic: a named return variable, read at the end*)
  | SEval of expr                  (*synthetic: the value of a `return` expression, dropped*)

type invocation = string * expr list * int

type param = {ty: ty, name: string, loc: string, bound: int}    (*bound > 0: a parameter of an enum type with that many members*)

type func =
  {name: string, kind: string, params: param list, returns: param list, vis: string, mut: string, virt: bool, over: bool,
   mods: invocation list, body: stmt list option, pos: int, doc: string}

type moddef = {name: string, params: param list, virt: bool, over: bool, body: stmt list, pos: int}

type vardef = {ty: ty, name: string, vis: string, const: bool, immutable: bool, init: expr option, pos: int}

type cdef =
  {name: string, kind: string, abstract: bool, parents: (string * expr list) list, vars: vardef list, funcs: func list,
   modifiers: moddef list, structs: (string * (ty * string) list) list, enums: (string * string list) list,
   using: (string * ty option) list, events: string list, errors: string list, pos: int}

(** parser **)

fun elementary_type s =
  let
    fun num_after p = if String.isPrefix p s then Int.fromString (String.extract (s, size p, NONE)) else NONE
    fun all_digits t = size t > 0 andalso forall Char.isDigit (String.explode t)
  in
    if s = "address" then SOME (TyAddr false)
    else if s = "bool" then SOME TyBool
    else if s = "string" then SOME TyString
    else if s = "bytes" then SOME TyBytes
    else if s = "uint" then SOME (TyInt (false, 256))
    else if s = "int" then SOME (TyInt (true, 256))
    else if String.isPrefix "uint" s andalso all_digits (String.extract (s, 4, NONE)) then
      (case num_after "uint" of SOME w => if w >= 8 andalso w <= 256 andalso w mod 8 = 0 then SOME (TyInt (false, w)) else NONE | NONE => NONE)
    else if String.isPrefix "int" s andalso all_digits (String.extract (s, 3, NONE)) then
      (case num_after "int" of SOME w => if w >= 8 andalso w <= 256 andalso w mod 8 = 0 then SOME (TyInt (true, w)) else NONE | NONE => NONE)
    else if String.isPrefix "bytes" s andalso all_digits (String.extract (s, 5, NONE)) then
      (case num_after "bytes" of SOME w => if w >= 1 andalso w <= 32 then SOME (TyBytesN w) else NONE | NONE => NONE)
    else NONE
  end

val units =
  [("wei", 1), ("gwei", 1000000000), ("ether", 1000000000000000000), ("seconds", 1), ("minutes", 60), ("hours", 3600),
   ("days", 86400), ("weeks", 604800)]

val file_structs : (string * (ty * string) list) list Unsynchronized.ref = Unsynchronized.ref []

(*Constants and functions that are declared outside of any contract are copied into every contract that mentions them (a free function becomes an
  internal function of the contract), in front of its own members, as `transpile.py` does with the tree of solc*)
fun inline_file_level (toks: token list) : token list =
  let
    fun first_real ts = (case ts of (Doc _, _) :: r => first_real r | t :: _ => SOME (#1 t) | [] => NONE)
    fun take_item ts =
      let
        fun go depth acc ts =
          (case ts of
             [] => (rev acc, [])
           | (t as (Sym "{", _)) :: r => go (depth + 1) (t :: acc) r
           | (t as (Sym "}", _)) :: r => if depth <= 1 then (rev (t :: acc), r) else go (depth - 1) (t :: acc) r
           | (t as (Sym ";", _)) :: r => if depth = 0 then (rev (t :: acc), r) else go depth (t :: acc) r
           | t :: r => go depth (t :: acc) r)
      in go 0 [] ts end
    fun items ts = if null ts then [] else let val (i, r) = take_item ts in i :: items r end
    val its = items toks
    val kw = ["contract", "interface", "library", "abstract", "pragma", "import", "enum", "struct", "type", "using", "function"]
    fun is_contract it = (case first_real it of SOME (Id s) => member (op =) ["contract", "interface", "library", "abstract"] s | _ => false)
    fun real it = filter (fn (Doc _, _) => false | _ => true) it
    fun is_free_fn it = (first_real it = SOME (Id "function"))
    fun is_free_const it =
      (case first_real it of
         SOME (Id s) => not (member (op =) kw s) andalso exists (fn (Id "constant", _) => true | _ => false) it andalso not (exists (fn (Sym "{", _) => true | _ => false) it)
       | _ => false)
    val members = filter (fn it => is_free_fn it orelse is_free_const it) its
    (*the name that a member declares*)
    fun declared it =
      let
        val r = map #1 (real it)
        fun fn_name (Id "function" :: Id n :: _) = SOME n
          | fn_name _ = NONE
        fun const_name ts =
          (case ts of
             Id n :: Sym "=" :: _ => SOME n
           | _ :: r => const_name r
           | [] => NONE)
      in if is_free_fn it then fn_name r else const_name r end
    fun ids it = map_filter (fn (Id s, _) => SOME s | _ => NONE) it
    fun add_internal it =
      (*after the parameter list of a free function: internal*)
      let
        fun go depth acc ts =
          (case ts of
             [] => rev acc
           | (t as (Sym "(", p)) :: r => go (depth + 1) (t :: acc) r
           | (t as (Sym ")", p)) :: r =>
               if depth = 1 then rev acc @ [t, (Id "internal", p)] @ r else go (depth - 1) (t :: acc) r
           | t :: r => go depth (t :: acc) r)
        val (before, from_paren) = chop_prefix (fn (Sym "(", _) => false | _ => true) it
      in before @ go 0 [] from_paren end
    and chop_prefix f xs = (case xs of x :: r => if f x then (case chop_prefix f r of (a, b) => (x :: a, b)) else ([], xs) | [] => ([], []))
    fun with_members it =
      let
        fun needed names todo =
          (case todo of
             [] => names
           | m :: r =>
               let
                 val used = ids it @ (if member (op =) names m then [] else ids m)
                 val _ = used
               in needed names r end)
        (*the members mentioned by the contract, and by the members that it needs*)
        fun closure (got: token list list) (mentioned: string list) =
          let
            val new = filter (fn m => not (member (op =) got m) andalso (case declared m of SOME n => member (op =) mentioned n | NONE => false)) members
          in if null new then got else closure (got @ new) (mentioned @ maps ids new) end
        val got = closure [] (ids it)
        val ordered = filter (fn m => member (op =) got m) members
        val ins = maps (fn m => if is_free_fn m then add_internal m else m) ordered
        val (head, rest) = chop_prefix (fn (Sym "{", _) => false | _ => true) it
      in (case rest of b :: r => head @ [b] @ ins @ r | [] => it) end
  in
    maps (fn it => if is_contract it then with_members it else if member (op =) members it then [] else it) its
  end

fun parse (toks00: token list) : cdef list =
  let
    val toks0 = inline_file_level toks00
    val _ = file_structs := []
    (*the doc comments in front of each token are kept apart (natspec of functions)*)
    val (toks, docs) =
      let
        fun go [] _ acc = rev acc
          | go ((Doc d, _) :: r) pending acc = go r (pending @ [d]) acc
          | go ((tk, p) :: r) pending acc = go r [] (((tk, p), space_implode "\n" pending) :: acc)
      in ListPair.unzip (go toks0 [] []) end
    (*enums and user-defined value types are found in a first pass over the tokens: an enum is a uint8 that stays below the number of its members, a user-defined
      value type is its underlying type (wrap and unwrap are the identity)*)
    val enum_tbl : (string * string list) list =
      let
        fun members ((Id m, _) :: (Sym ",", _) :: r) = m :: members r
          | members ((Id m, _) :: r) = [m]
          | members _ = []
        fun scan ((Id "enum", _) :: (Id n, _) :: (Sym "{", _) :: r) = (n, members r) :: scan r
          | scan (_ :: r) = scan r
          | scan [] = []
      in scan toks0 |> map (fn (n, ms) => (n, ms)) end
    val udvt_tbl : (string * ty) list =
      let
        fun scan ((Id "type", _) :: (Id n, _) :: (Id "is", _) :: (Id u, _) :: r) =
              (case elementary_type u of SOME ty => (n, ty) :: scan r | NONE => scan r)
          | scan (_ :: r) = scan r
          | scan [] = []
      in scan toks0 end
    val last_enum : int Unsynchronized.ref = Unsynchronized.ref 0
    fun enum_of_name n = AList.lookup (op =) enum_tbl n
    fun tail_name e = (case e of EId (n, _) => SOME n | EMember (_, n, _) => SOME n | _ => NONE)
    val doc_arr = Vector.fromList docs
    fun doc_at i = if i < Vector.length doc_arr then Vector.sub (doc_arr, i) else ""
    val arr = Vector.fromList toks
    val pos_ref = Unsynchronized.ref 0
    fun peek () = Vector.sub (arr, Int.min (!pos_ref, Vector.length arr - 1))
    fun cur () = fst (peek ())
    fun cur_pos () = snd (peek ())
    fun nth_tok k = fst (Vector.sub (arr, Int.min (!pos_ref + k, Vector.length arr - 1)))
    fun advance () = pos_ref := !pos_ref + 1
    fun cur_doc () = doc_at (!pos_ref)
    fun show t = (case t of Id s => s | Num s => s | Str s => quote s | HexStr s => "hex" ^ quote s | Sym s => s | Doc _ => "a comment" | Eof => "end of the text")
    fun fail msg = err (cur_pos ()) msg
    fun expect s = if cur () = Sym s then advance () else fail ("expected " ^ quote s ^ ", found " ^ quote (show (cur ())))
    fun accept s = if cur () = Sym s then (advance (); true) else false
    fun accept_id s = if cur () = Id s then (advance (); true) else false
    fun expect_id s = if cur () = Id s then advance () else fail ("expected " ^ quote s ^ ", found " ^ quote (show (cur ())))
    fun ident () = (case cur () of Id s => (advance (); s) | t => fail ("expected a name, found " ^ quote (show t)))
    fun is_one_of l t = (case t of Id s => member (op =) l s | _ => false)

    fun list_until close item =
      if accept close then []
      else
        let fun more acc = if accept "," then more (item () :: acc) else (expect close; rev acc)
        in more [item ()] end

    (* types *)
    fun parse_type () =
      let
        val _ = last_enum := 0
        val base =
          (case cur () of
             Id "mapping" =>
               let
                 val _ = advance ()
                 val _ = expect "("
                 val k = parse_type ()
                 val _ = (case cur () of Id _ => advance () | _ => ())           (*a name of the key: mapping(address account => uint)*)
                 val _ = expect "=>"
                 val v = parse_type ()
                 val _ = (case cur () of Id _ => advance () | _ => ())
                 val _ = expect ")"
               in TyMapping (k, v) end
           | Id "function" => fail "function types are not supported"
           | Id s =>
               (case elementary_type s of
                  SOME t =>
                    (advance ();
                     if t = TyAddr false andalso cur () = Id "payable" then (advance (); TyAddr true) else t)
                | NONE =>
                    if s = "uint" orelse String.isPrefix "uint" s orelse String.isPrefix "int" s orelse String.isPrefix "bytes" s
                       andalso size s > 5 andalso forall Char.isDigit (String.explode (String.extract (s, 5, NONE)))
                    then (advance (); TyUser s)   (*not a valid elementary type name: treated as a user type, which is refused later*)
                    else
                      let
                        val _ = advance ()
                        fun dotted n = if cur () = Sym "." andalso (case nth_tok 1 of Id _ => true | _ => false) then (advance (); dotted (n ^ "." ^ ident ())) else n
                        val full = dotted s
                        val short = (case rev (String.fields (fn c => c = #".") full) of x :: _ => x | [] => full)
                      in
                        (case (AList.lookup (op =) udvt_tbl short, enum_of_name short) of
                           (SOME u, _) => u
                         | (NONE, SOME ms) => (last_enum := length ms; TyInt (false, 8))
                         | _ => TyUser full)
                      end)
           | t => fail ("expected a type, found " ^ quote (show t)))
        fun arrays t =
          if cur () = Sym "[" then
            (case nth_tok 1 of
               Sym "]" => (advance (); advance (); arrays (TyArray (t, NONE)))
             | Num s => if nth_tok 2 = Sym "]" then (advance (); advance (); advance (); arrays (TyArray (t, SOME (the (IntInf.fromString s))))) else fail "an array length must be a number literal"
             | _ => fail "expected an array length or ]")
          else t
        fun arrays' t = if cur () = Sym "[" then (last_enum := 0; arrays t) else t
      in arrays' base end

    fun location () = (case cur () of Id s => if member (op =) ["memory", "storage", "calldata"] s then (advance (); s) else "" | _ => "")

    (* expressions *)
    fun unit_of s = AList.lookup (op =) units s

    fun expression () = parse_assign ()
    and parse_assign () =
      let val l = parse_cond () in
        (case cur () of
           Sym s =>
             if member (op =) ["=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>=", "**="] s
             then let val p = cur_pos () val _ = advance () val r = parse_assign () in EAssign (s, l, r, p) end
             else l
         | _ => l)
      end
    and parse_cond () =
      let val c = parse_level 0 in
        if cur () = Sym "?" then
          let val p = cur_pos () val _ = advance () val a = parse_assign () val _ = expect ":" val b = parse_assign () in ECond (c, a, b, p) end
        else c
      end
    and parse_level k =
      let
        val levels = [["||"], ["&&"], ["==", "!="], ["<", ">", "<=", ">="], ["|"], ["^"], ["&"], ["<<", ">>"], ["+", "-"], ["*", "/", "%"]]
      in
        if k >= length levels then parse_pow ()
        else
          let
            val ops = nth levels k
            fun loop l =
              (case cur () of
                 Sym s => if member (op =) ops s then let val p = cur_pos () val _ = advance () val r = parse_level (k + 1) in loop (EBin (s, l, r, p)) end else l
               | _ => l)
          in loop (parse_level (k + 1)) end
      end
    and parse_pow () =
      let val l = parse_unary () in
        if cur () = Sym "**" then let val p = cur_pos () val _ = advance () val r = parse_pow () in EBin ("**", l, r, p) end else l
      end
    and parse_unary () =
      let val p = cur_pos () in
        (case cur () of
           Sym "!" => (advance (); EUn ("!", parse_unary (), p))
         | Sym "-" => (advance (); EUn ("-", parse_unary (), p))
         | Sym "~" => (advance (); EUn ("~", parse_unary (), p))
         | Sym "++" => (advance (); EUn ("++", parse_unary (), p))
         | Sym "--" => (advance (); EUn ("--", parse_unary (), p))
         | Id "delete" => (advance (); EUn ("delete", parse_unary (), p))
         | _ => parse_postfix (parse_primary ()))
      end
    and parse_primary () =
      let val p = cur_pos () in
        (case cur () of
           Num s =>
             (advance ();
              (case cur () of
                 Id u =>
                   (case unit_of u of
                      SOME m => (advance (); EBin ("*", ENum s, ENum (string_of_int m), p))
                    | NONE => ENum s)
               | _ => ENum s))
         | Str s => (advance (); EStr s)
         | HexStr s => (advance (); EHex s)
         | Id "true" => (advance (); EBool true)
         | Id "false" => (advance (); EBool false)
         | Id "new" => fail "new is not supported"
         | Id s =>
             (case elementary_type s of
                SOME t =>
                  (advance ();
                   if t = TyAddr false andalso cur () = Id "payable" then (advance (); EType (TyAddr true, p)) else EType (t, p))
              | NONE => (advance (); EId (s, p)))
         | Sym "(" =>
             let
               val _ = advance ()
               val es = list_until ")" expression
             in ETuple (es, p) end
         | t => fail ("expected an expression, found " ^ quote (show t)))
      end
    and parse_postfix e =
      (case cur () of
         Sym "." =>
           let val p = cur_pos () val _ = advance () val m = ident () in
             (case Option.mapPartial enum_of_name (tail_name e) of
                SOME ms =>
                  (case find_index (fn x => x = m) ms of
                     ~1 => err p ("the enum has no member " ^ quote m)
                   | i => parse_postfix (ENum (string_of_int i)))
              | NONE => parse_postfix (EMember (e, m, p)))
           end
       | Sym "[" =>
           let val p = cur_pos () val _ = advance () val i = expression () val _ = expect "]" in parse_postfix (EIndex (e, i, p)) end
       | Sym "(" =>
           let
             val p = cur_pos () val _ = advance () val args = list_until ")" expression
             fun is_udvt n = AList.defined (op =) udvt_tbl n
           in
             (case (e, args) of
                (EMember (EId (x, _), w, _), [a]) =>
                  if (w = "wrap" orelse w = "unwrap") andalso is_udvt x then parse_postfix a else parse_postfix (ECall (e, args, p))
              | (_, [a]) =>
                  (case Option.mapPartial enum_of_name (tail_name e) of
                     SOME ms => parse_postfix (ECall (EId ("$enum", p), [ENum (string_of_int (length ms)), a], p))
                   | NONE => parse_postfix (ECall (e, args, p)))
              | _ => parse_postfix (ECall (e, args, p)))
           end
       | Sym "{" =>
           (case e of
              EMember (_, "call", _) =>
                let
                  val p = cur_pos ()
                  val _ = advance ()
                  fun opt () = let val n = ident () val _ = expect ":" val v = expression () in (n, v) end
                  val opts = list_until "}" opt
                in parse_postfix (ECallOpts (e, opts, p)) end
            | _ => fail "call options are not supported")
       | Sym "++" => let val p = cur_pos () val _ = advance () in parse_postfix (EUn ("++post", e, p)) end
       | Sym "--" => let val p = cur_pos () val _ = advance () in parse_postfix (EUn ("--post", e, p)) end
       | _ => e)

    (* statements *)
    fun is_decl_start () =
      let
        val save = !pos_ref
        val r =
          (case cur () of
             Id s =>
               if member (op =) ["return", "if", "for", "while", "emit", "revert", "delete", "unchecked", "do", "break", "continue", "new", "require", "assert", "type"] s then false
               else
                 (let val _ = parse_type () in (case cur () of Id _ => true | _ => false) end handle Err _ => false)
           | _ => false)
        val _ = pos_ref := save
      in r end

    fun var_decl () =
      let
        val p = cur_pos ()
        val t = parse_type ()
        val loc = location ()
        val n = ident ()
        val init = if accept "=" then SOME (expression ()) else NONE
      in SDecl (t, n, loc, init, p) end

    fun statement () =
      let val p = cur_pos () in
        (case cur () of
           Sym "{" => let val _ = advance () in SBlock (block_rest ()) end
         | Id "if" =>
             let
               val _ = advance ()
               val _ = expect "("
               val c = expression ()
               val _ = expect ")"
               val t = statement ()
               val f = if accept_id "else" then SOME (statement ()) else NONE
             in SIf (c, t, f) end
         | Id "while" =>
             let val _ = advance () val _ = expect "(" val c = expression () val _ = expect ")" in SWhile (c, statement ()) end
         | Id "do" =>
             let
               val _ = advance ()
               val b = statement ()
               val _ = if accept_id "while" then () else fail "expected \"while\" after the body of do"
               val _ = expect "("
               val c = expression ()
               val _ = expect ")"
               val _ = expect ";"
             in SDoWhile (b, c) end
         | Id "for" =>
             let
               val _ = advance ()
               val _ = expect "("
               val init = if cur () = Sym ";" then NONE else SOME (simple ())
               val _ = expect ";"
               val cond = if cur () = Sym ";" then NONE else SOME (expression ())
               val _ = expect ";"
               val step = if cur () = Sym ")" then NONE else SOME (expression ())
               val _ = expect ")"
             in SFor (init, cond, step, statement ()) end
         | Id "return" =>
             let val _ = advance () in
               if cur () = Sym ";" then (advance (); SReturn (NONE, p))
               else let val e = expression () val _ = expect ";" in SReturn (SOME e, p) end
             end
         | Id "unchecked" => let val _ = advance () val _ = expect "{" in SUnchecked (block_rest ()) end
         | Id "emit" => let val _ = advance () val e = expression () val _ = expect ";" in SEmit (e, p) end
         | Id "revert" =>
             let val _ = advance () in
               if cur () = Sym "(" then (pos_ref := !pos_ref - 1; let val s = simple () val _ = expect ";" in s end)
               else if cur () = Sym ";" then (advance (); SRevert (NONE, p))
               else let val e = expression () val _ = expect ";" in SRevert (SOME e, p) end
             end
         | Sym "(" =>
             (case (nth_tok 1, nth_tok 2, nth_tok 3, nth_tok 4) of
                (Id "bool", Id ok, Sym ",", Sym ")") =>
                  let
                    val _ = advance () val _ = advance () val _ = advance () val _ = advance () val _ = advance ()
                    val _ = expect "="
                    val e = expression ()
                    val _ = expect ";"
                  in
                    (case e of
                       ECall (ECallOpts (EMember (a, "call", _), [("value", v)], _), [EStr ""], _) => SLowCall (ok, a, v, p)
                     | _ => err p "this tuple declaration is not supported (only (bool ok, ) = a.call{value: v}(\"\") is)")
                  end
              | _ =>
                 let
                   (*a tuple declaration (T a, U b) = e; is parsed, and refused where it is used*)
                   val save = !pos_ref
                   val decl =
                     (let
                        val _ = advance ()
                        fun slot () = if cur () = Sym "," orelse cur () = Sym ")" then () else (ignore (parse_type ()); ignore (location ()); ignore (ident ()))
                        fun slots () = (slot (); if accept "," then slots () else expect ")")
                        val _ = slots ()
                      in cur () = Sym "=" end handle Err _ => false)
                 in
                   if decl then
                     let val _ = advance () val _ = expression () val _ = expect ";" in SUnsupported ("a tuple declaration", p) end
                   else (pos_ref := save; let val s = simple () val _ = expect ";" in s end)
                 end)
         | Id "assembly" =>
             let
               val _ = advance ()
               val _ = (case cur () of Str _ => advance () | _ => ())
               val _ = if cur () = Sym "(" then (advance (); ignore (list_until ")" expression)) else ()
               val _ = expect "{"
               fun skip depth = (case cur () of
                                   Sym "{" => (advance (); skip (depth + 1))
                                 | Sym "}" => (advance (); if depth = 0 then () else skip (depth - 1))
                                 | Eof => fail "unterminated assembly block"
                                 | _ => (advance (); skip depth))
               val _ = skip 0
             in SUnsupported ("inline assembly", p) end
         | Id "break" => (advance (); expect ";"; SBreak p)
         | Id "continue" => (advance (); expect ";"; SContinue p)
         | Id "_" => let val _ = advance () val _ = expect ";" in SPlaceholder p end
         | _ => let val s = simple () val _ = expect ";" in s end)
      end
    and simple () =
      let val p = cur_pos () in
        if is_decl_start () then var_decl ()
        else SExpr (expression (), p)
      end
    and block_rest () = if accept "}" then [] else let val s = statement () in s :: block_rest () end

    (* declarations *)
    fun parameter () =
      let
        val t = parse_type ()
        val bound = !last_enum
        val loc = location ()
        val n = (case cur () of Id s => if is_one_of ["indexed", "anonymous"] (cur ()) then (advance (); (case cur () of Id s2 => (advance (); s2) | _ => "")) else (advance (); s) | _ => "")
      in {ty = t, name = n, loc = loc, bound = bound} end

    fun parameters () = let val _ = expect "(" in list_until ")" parameter end

    (*the attributes of a function: visibility, mutability, virtual, override, modifier invocations*)
    fun attributes () =
      let
        fun go (vis, mut, virt, over, mods, rets) =
          (case cur () of
             Id s =>
               if member (op =) ["external", "public", "internal", "private"] s then (advance (); go (s, mut, virt, over, mods, rets))
               else if member (op =) ["payable", "view", "pure"] s then (advance (); go (vis, s, virt, over, mods, rets))
               else if s = "virtual" then (advance (); go (vis, mut, true, over, mods, rets))
               else if s = "override" then
                 (advance ();
                  if cur () = Sym "(" then (advance (); ignore (list_until ")" ident)) else ();
                  go (vis, mut, virt, true, mods, rets))
               else if s = "returns" then (advance (); let val r = parameters () in go (vis, mut, virt, over, mods, r) end)
               else
                 let
                   val p = cur_pos ()
                   val _ = advance ()
                   val args = if accept "(" then list_until ")" expression else []
                 in go (vis, mut, virt, over, mods @ [(s, args, p)], rets) end
           | _ => (vis, mut, virt, over, mods, rets))
      in go ("", "", false, false, [], []) end

    fun function_body () = if accept ";" then NONE else let val _ = expect "{" in SOME (block_rest ()) end

    fun contract_def () =
      let
        val p0 = cur_pos ()
        val abstract = accept_id "abstract"
        val kind = (case cur () of Id s => if member (op =) ["contract", "interface", "library"] s then (advance (); s) else fail ("expected `contract`, found " ^ quote s) | t => fail ("expected `contract`, found " ^ quote (show t)))
        val name = ident ()
        val parents =
          if accept_id "is" then
            let
              fun base () =
                let
                  val b = ident ()
                  val b = if cur () = Sym "." then (advance (); b ^ "." ^ ident ()) else b
                  val args = if accept "(" then list_until ")" expression else []
                in (b, args) end
              fun more acc = if accept "," then more (base () :: acc) else rev acc
            in more [base ()] end
          else []
        val _ = expect "{"
        val vars = Unsynchronized.ref []
        val funcs = Unsynchronized.ref []
        val mods = Unsynchronized.ref []
        val structs = Unsynchronized.ref []
        val enums = Unsynchronized.ref []
        val usings = Unsynchronized.ref []
        val events = Unsynchronized.ref []
        val errors = Unsynchronized.ref []
        fun special_fn p doc s =
          let
            val _ = advance ()
            val params = parameters ()
            val (vis, mut, virt, over, ms, rets) = attributes ()
            val body = function_body ()
          in funcs := !funcs @ [{name = s, kind = s, params = params, returns = rets, vis = vis, mut = mut, virt = virt, over = over, mods = ms, body = body, pos = p, doc = doc}] end
        fun member_decl () =
          let val p = cur_pos () val doc = cur_doc () in
            (case cur () of
               Id "function" =>
                 let
                   val _ = advance ()
                   val fname = ident ()
                   val params = parameters ()
                   val (vis, mut, virt, over, ms, rets) = attributes ()
                   val body = function_body ()
                 in funcs := !funcs @ [{name = fname, kind = "function", params = params, returns = rets, vis = vis, mut = mut, virt = virt, over = over, mods = ms, body = body, pos = p, doc = doc}] end
             | Id "constructor" =>
                 let
                   val _ = advance ()
                   val params = parameters ()
                   val (vis, mut, virt, over, ms, rets) = attributes ()
                   val body = function_body ()
                 in funcs := !funcs @ [{name = "constructor", kind = "constructor", params = params, returns = [], vis = vis, mut = mut, virt = virt, over = over, mods = ms, body = body, pos = p, doc = doc}] end
             | Id "receive" => special_fn p doc "receive"
             | Id "fallback" => special_fn p doc "fallback"
             | Id "modifier" =>
                 let
                   val _ = advance ()
                   val mname = ident ()
                   val params = if cur () = Sym "(" then parameters () else []
                   val virt = Unsynchronized.ref false
                   val over = Unsynchronized.ref false
                   fun attrs () =
                     if accept_id "virtual" then (virt := true; attrs ())
                     else if accept_id "override" then ((if cur () = Sym "(" then (advance (); ignore (list_until ")" ident)) else ()); over := true; attrs ())
                     else ()
                   val _ = attrs ()
                   val _ = expect "{"
                   val body = block_rest ()
                 in mods := !mods @ [{name = mname, params = params, virt = !virt, over = !over, body = body, pos = p}] end
             | Id "event" =>
                 let val _ = advance () val n = ident () val _ = parameters () val _ = accept_id "anonymous" val _ = expect ";" in events := !events @ [n] end
             | Id "error" =>
                 let val _ = advance () val n = ident () val _ = parameters () val _ = expect ";" in errors := !errors @ [n] end
             | Id "struct" =>
                 let
                   val _ = advance ()
                   val n = ident ()
                   val _ = expect "{"
                   fun fields () =
                     if accept "}" then []
                     else let val t = parse_type () val fn_ = ident () val _ = expect ";" in (t, fn_) :: fields () end
                 in structs := !structs @ [(n, fields ())] end
             | Id "enum" =>
                 let
                   val _ = advance ()
                   val n = ident ()
                   val _ = expect "{"
                   val vs = list_until "}" ident
                 in enums := !enums @ [(n, vs)] end
             | Id "using" =>
                 let
                   val _ = advance ()
                   val lib = ident ()
                   val _ = expect_id "for"
                   val t = if accept "*" then NONE else SOME (parse_type ())
                   val _ = expect ";"
                 in usings := !usings @ [(lib, t)] end
             | Id "type" => (advance (); ignore (ident ()); expect_id "is"; advance (); expect ";")      (*a user-defined value type: see udvt_tbl*)
             | _ =>
                 let
                   val t = parse_type ()
                   fun attrs (vis, const, imm) =
                     (case cur () of
                        Id s =>
                          if member (op =) ["public", "private", "internal"] s then (advance (); attrs (s, const, imm))
                          else if s = "constant" then (advance (); attrs (vis, true, imm))
                          else if s = "immutable" then (advance (); attrs (vis, const, true))
                          else if s = "override" then (advance (); (if cur () = Sym "(" then (advance (); ignore (list_until ")" ident)) else ()); attrs (vis, const, imm))
                          else (vis, const, imm)
                      | _ => (vis, const, imm))
                   val (vis, const, imm) = attrs ("", false, false)
                   val n = ident ()
                   val init = if accept "=" then SOME (expression ()) else NONE
                   val _ = expect ";"
                 in vars := !vars @ [{ty = t, name = n, vis = vis, const = const, immutable = imm, init = init, pos = p}] end)
          end
        fun members () = if accept "}" then () else (member_decl (); members ())
        val _ = members ()
      in
        {name = name, kind = kind, abstract = abstract, parents = parents, vars = !vars, funcs = !funcs, modifiers = !mods,
         structs = !structs, enums = !enums, using = !usings, events = !events, errors = !errors, pos = p0}
      end

    fun contracts () =
      (case cur () of
         Eof => []
       | Id "import" => fail "import is not supported (put the contracts in one text)"
       | Id "enum" =>
           let val _ = advance () val _ = ident () val _ = expect "{" val _ = list_until "}" ident in contracts () end
       | Id "type" =>
           let val _ = advance () val _ = ident () val _ = expect_id "is" val _ = advance () val _ = expect ";" in contracts () end
       | Id "struct" =>
           let
             val _ = advance ()
             val n = ident ()
             val _ = expect "{"
             fun fields () =
               if accept "}" then []
               else let val t = parse_type () val fn_ = ident () val _ = expect ";" in (t, fn_) :: fields () end
             val fs = fields ()
           in (file_structs := !file_structs @ [(n, fs)]; contracts ()) end
       | Id s =>
           if member (op =) ["contract", "interface", "library", "abstract"] s then let val c = contract_def () in c :: contracts () end
           else fail ("expected `contract`, found " ^ quote s)
       | t => fail ("expected `contract`, found " ^ quote (show t)))
  in contracts () end

(** elaboration: the text of the monadic terms **)

fun str_name n = "STR ''" ^ n ^ "''"

fun two_pow n = IntInf.pow (2, n)

fun isa_ident name =
  let val n = String.translate (fn c => if c = #"$" then "S_" else String.str c) name
  in if String.isPrefix "_" n then "u" ^ n else n end

(*the commands and keywords of Isabelle/Solidity cannot be method names unless quoted*)
val isabelle_keywords =
  ["contract", "constructor", "cfunction", "external", "memory", "param", "calldata", "payable", "assuming", "is", "abstract",
   "initialiser", "replacing", "verification", "invariant", "for", "and", "where", "record", "begin", "end", "fun", "lemma", "theorem",
   "definition", "datatype", "type", "section", "text", "ML", "in", "imports", "keywords", "theory", "context", "locale"]

fun cf_name n = if member (op =) isabelle_keywords n then "\"" ^ n ^ "\"" else n

(*the text of a number: exact value or NONE (fractions that are not integers)*)
fun parse_number s : IntInf.int option =
  let
    val s' = String.translate (fn c => if c = #"_" then "" else String.str c) s
  in
    if String.isPrefix "0x" s' orelse String.isPrefix "0X" s' then
      let
        fun hv c = if Char.isDigit c then Char.ord c - Char.ord #"0" else Char.ord (Char.toLower c) - Char.ord #"a" + 10
      in SOME (fold (fn c => fn acc => acc * 16 + IntInf.fromInt (hv c)) (String.explode (String.extract (s', 2, NONE))) 0) end
    else
      let
        val (mant, ex) =
          (case String.fields (fn c => c = #"e" orelse c = #"E") s' of
             [m] => (m, 0)
           | [m, e] => (m, the_default 0 (Int.fromString (if String.isPrefix "+" e then String.extract (e, 1, NONE) else e)))
           | _ => ("", 0))
        val (ip, fp) = (case String.fields (fn c => c = #".") mant of [a] => (a, "") | [a, b] => (a, b) | _ => ("", ""))
        val digits = ip ^ fp
        val scale = ex - size fp
      in
        if digits = "" orelse not (forall Char.isDigit (String.explode digits)) orelse abs scale > 400 then NONE
        else
          let val m = the (IntInf.fromString digits) in
            if scale >= 0 then SOME (m * IntInf.pow (10, scale))
            else let val d = IntInf.pow (10, ~scale) in if m mod d = 0 then SOME (m div d) else NONE end
          end
      end
  end


(*Keccak-256, for the selectors of functions (type(I).interfaceId)*)
structure Keccak =
struct
  val rc = map (fn h => Word64.fromLargeInt (the (parse_number h)))
    ["0x0000000000000001", "0x0000000000008082", "0x800000000000808A", "0x8000000080008000", "0x000000000000808B", "0x0000000080000001",
     "0x8000000080008081", "0x8000000000008009", "0x000000000000008A", "0x0000000000000088", "0x0000000080008009", "0x000000008000000A",
     "0x000000008000808B", "0x800000000000008B", "0x8000000000008089", "0x8000000000008003", "0x8000000000008002", "0x8000000000000080",
     "0x000000000000800A", "0x800000008000000A", "0x8000000080008081", "0x8000000000008080", "0x0000000080000001", "0x8000000080008008"]
  val rot = [0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14]
  fun rol (w, n) = if n = 0 then w else Word64.orb (Word64.<< (w, Word.fromInt n), Word64.>> (w, Word.fromInt (64 - n)))

  fun round (a: Word64.word Array.array, r) =
    let
      val c = Array.tabulate (5, fn x => Word64.xorb (Word64.xorb (Word64.xorb (Array.sub (a, x), Array.sub (a, x + 5)), Word64.xorb (Array.sub (a, x + 10), Array.sub (a, x + 15))), Array.sub (a, x + 20)))
      val _ = List.app (fn x =>
                let val d = Word64.xorb (Array.sub (c, (x + 4) mod 5), rol (Array.sub (c, (x + 1) mod 5), 1))
                in List.app (fn y => Array.update (a, x + 5 * y, Word64.xorb (Array.sub (a, x + 5 * y), d))) [0, 1, 2, 3, 4] end) [0, 1, 2, 3, 4]
      val b = Array.array (25, Word64.fromInt 0)
      val _ = List.app (fn x => List.app (fn y =>
                Array.update (b, y + 5 * ((2 * x + 3 * y) mod 5), rol (Array.sub (a, x + 5 * y), nth rot (x + 5 * y)))) [0, 1, 2, 3, 4]) [0, 1, 2, 3, 4]
      val _ = List.app (fn x => List.app (fn y =>
                Array.update (a, x + 5 * y, Word64.xorb (Array.sub (b, x + 5 * y),
                  Word64.andb (Word64.notb (Array.sub (b, (x + 1) mod 5 + 5 * y)), Array.sub (b, (x + 2) mod 5 + 5 * y))))) [0, 1, 2, 3, 4]) [0, 1, 2, 3, 4]
    in Array.update (a, 0, Word64.xorb (Array.sub (a, 0), nth rc r)) end

  (*the 32 bytes of the hash of a list of bytes*)
  fun hash (bytes: int list) : int list =
    let
      val rate = 136
      val padlen = rate - (length bytes mod rate)
      val padded = bytes @ (if padlen = 1 then [0x81] else [0x01] @ replicate (padlen - 2) 0 @ [0x80])
      val a = Array.array (25, Word64.fromInt 0)
      fun absorb [] = ()
        | absorb bs =
            let
              val (blk, rest) = (take rate bs, drop rate bs)
              val _ = List.app (fn i =>
                        let
                          val lane = fold (fn k => fn acc => Word64.orb (acc, Word64.<< (Word64.fromInt (nth blk (8 * i + k)), Word.fromInt (8 * k)))) (0 upto 7) (Word64.fromInt 0)
                        in Array.update (a, i, Word64.xorb (Array.sub (a, i), lane)) end) (0 upto (rate div 8 - 1))
              val _ = List.app (fn r => round (a, r)) (0 upto 23)
            in absorb rest end
      val _ = absorb padded
    in maps (fn i => map (fn k => Word64.toInt (Word64.andb (Word64.>> (Array.sub (a, i), Word.fromInt (8 * k)), Word64.fromInt 255))) (0 upto 7)) [0, 1, 2, 3] end
end

(*the ABI type name of a parameter in the signature of a function*)
fun abi_type is_contract t =
  (case t of
     TyInt (false, w) => "uint" ^ string_of_int w | TyInt (true, w) => "int" ^ string_of_int w | TyAddr _ => "address" | TyBool => "bool"
   | TyBytesN n => "bytes" ^ string_of_int n | TyString => "string" | TyBytes => "bytes"
   | TyUser n => if is_contract n then "address" else "?" | _ => "?")

fun selector is_contract (name: string) (params: ty list) : IntInf.int =
  let
    val sg = name ^ "(" ^ space_implode "," (map (abi_type is_contract) params) ^ ")"
    val h = Keccak.hash (map Char.ord (String.explode sg))
  in fold (fn b => fn acc => acc * 256 + IntInf.fromInt b) (take 4 h) 0 end

fun xor_int (a: IntInf.int, b: IntInf.int) : IntInf.int =
  let
    fun go x y k = if x = 0 andalso y = 0 then 0 else (if (x mod 2) <> (y mod 2) then k else 0) + go (x div 2) (y div 2) (k * 2)
  in go a b 1 end

fun const_text v = if v >= 0 then "(sint_monad " ^ IntInf.toString v ^ ")" else "(sint_monad (- " ^ IntInf.toString (~v) ^ "))"

fun bytes_text (bs: int list) =
  "(bytes_monad2 [" ^ space_implode ", " (map (fn b => "CHR 0x" ^ (if b < 16 then "0" else "") ^ (String.map Char.toUpper (Int.fmt StringCvt.HEX b))) bs) ^ "])"

fun unescape s =
  let
    fun hex2 c = if Char.isDigit c then Char.ord c - Char.ord #"0" else Char.ord (Char.toLower c) - Char.ord #"a" + 10
    fun go [] = []
      | go (#"\\" :: #"n" :: r) = 10 :: go r
      | go (#"\\" :: #"t" :: r) = 9 :: go r
      | go (#"\\" :: #"r" :: r) = 13 :: go r
      | go (#"\\" :: #"x" :: a :: b :: r) = (hex2 a * 16 + hex2 b) :: go r
      | go (#"\\" :: c :: r) = Char.ord c :: go r
      | go (c :: r) = Char.ord c :: go r
  in go (String.explode s) end

fun hex_bytes s =
  let
    fun hv c = if Char.isDigit c then Char.ord c - Char.ord #"0" else Char.ord (Char.toLower c) - Char.ord #"a" + 10
    fun go (a :: b :: r) = (hv a * 16 + hv b) :: go r
      | go _ = []
  in go (String.explode (String.translate (fn c => if c = #"_" then "" else String.str c) s)) end

(*in the definition of a modifier abbreviation the do-notation does not work (it needs the monad syntax of the context): explicit binds*)
val explicit_bind = Unsynchronized.ref false

fun do_block parts =
  if not (!explicit_bind) then "(do {\n      " ^ space_implode ";\n      " parts ^ "\n    })"
  else
    let
      fun binder p =
        (case String.fields (fn c => c = #" ") p of
           x :: "<-" :: _ => if x <> "" andalso Char.isAlpha (String.sub (x, 0)) then SOME (x, String.extract (p, size x + 4, NONE)) else NONE
         | _ => NONE)
      fun go [] = "skip_monad"
        | go [last] = last
        | go (p :: rest) =
            (case binder p of
               SOME (x, m) => "(bind (" ^ m ^ ") (\<lambda>" ^ x ^ ". " ^ go rest ^ "))"
             | NONE => "(bind (" ^ p ^ ") (\<lambda>_. " ^ go rest ^ "))")
    in "(" ^ go parts ^ ")" end

fun join_do parts =
  (case parts of
     [] => "skip_monad"
   | [p] => "(" ^ p ^ ")"
   | _ => do_block parts)



(*a state variable's or function's data*)
type fsig = {name: string, external: bool, params: param list, returns: param list, mut: string, pos: int, body: stmt list, mods: invocation list}

(*a function of another contract that is called: signature, parameter and result types, assumptions of its natspec*)
type ext_sig = {sg: string, params: string list, ret: string option, view: bool, assume: string list list, nocallback: bool}

type env =
  {cname: string,
   state: (string * ty) list,
   consts: (string * (expr * ty)) list,
   locals: (string * ty) list Unsynchronized.ref,     (*emitted name -> type; one set per function, no block scoping, as in the transpiler*)
   rename: (string * string) list,
   placeholder: string option,
   counter: int Unsynchronized.ref,
   mods: (string * moddef) list,
   funcs: (string * fsig) list,                       (*the functions that can be called by name*)
   alias: (string * string) list,                     (*public function -> its internal twin*)
   value_ret: string list,                            (*functions whose value is used by a caller*)
   unchecked: bool Unsynchronized.ref,
   uses: string list Unsynchronized.ref,
   guard: bool,
   locs: (string * string) list Unsynchronized.ref,   (*emitted name of a local -> its data location (memory, calldata)*)
   home: string Unsynchronized.ref,                   (*the class that declares the function being translated (for super)*)
   classes: string list,                              (*the contracts of the source text*)
   mod_abbrevs: (string * string) list Unsynchronized.ref,   (*the abbreviations of modifiers: name, command (when [[solidity_modifier_abbreviations]])*)
   mod_class: string -> string,                       (*the class that declares the (most derived) modifier of this name*)
   mod_abbrev_on: bool,
   ext_sigs: ext_sig list Unsynchronized.ref,         (*the functions of other contracts that are called*)
   find_callee: string -> string -> ty list -> int -> func,   (*contract, function, argument types -> the declaration*)
   lib_ctx: string option,                            (*the library whose function is being translated*)
   usings: (string * ty option) list Unsynchronized.ref,   (*using L for T of the contract that declares the function being translated*)
   lib_fn: string -> string -> ty list -> int -> string * fsig,   (*library, function, argument types -> the copy in the contract*)
   libs: string list,                                 (*the libraries of the text*)
   lib_fns: string -> string list,                    (*the functions of a library*)
   interface_ids: string -> IntInf.int option,        (*the ERC-165 id of an interface (xor of the selectors of its functions)*)
   super_of: string -> string -> (string * fsig) option,   (*home class, function -> the next implementation before the class*)
   base_of: string -> string -> (string * fsig) option}    (*class A, function -> the implementation that A.f() runs*)

fun use (env: env) name = (#uses env) := name :: !(#uses env)

fun with_rename (env: env) rename placeholder : env =
  {cname = #cname env, state = #state env, consts = #consts env, locals = #locals env, rename = rename, placeholder = placeholder,
   counter = #counter env, mods = #mods env, funcs = #funcs env, alias = #alias env, value_ret = #value_ret env,
   unchecked = #unchecked env, uses = #uses env, guard = #guard env, locs = #locs env, home = #home env, classes = #classes env,
   mod_abbrevs = #mod_abbrevs env, mod_class = #mod_class env, mod_abbrev_on = #mod_abbrev_on env,
   ext_sigs = #ext_sigs env, find_callee = #find_callee env, lib_ctx = #lib_ctx env, usings = #usings env, lib_fn = #lib_fn env, libs = #libs env, lib_fns = #lib_fns env,
   interface_ids = #interface_ids env, super_of = #super_of env, base_of = #base_of env}

fun emitted (env: env) n = the_default n (AList.lookup (op =) (#rename env) n)
fun local_ty (env: env) n = AList.lookup (op =) (!(#locals env)) n
fun add_local (env: env) n t = (#locals env) := (n, t) :: !(#locals env)

(*the types of Solidity in the framework*)
(*the structs of the source text (declared in contracts or at file level): name -> fields*)
val struct_table : (string * (ty * string) list) list Unsynchronized.ref = Unsynchronized.ref []

(*the contracts and interfaces of the text (a value of such a type is the address of the contract)*)
val contract_kinds : (string * string) list Unsynchronized.ref = Unsynchronized.ref []
fun is_contract_type n = (case AList.lookup (op =) (!contract_kinds) (String.map I n) of SOME k => k = "contract" orelse k = "interface" | NONE => false)

(*overloaded functions: source name -> [(name in the model, parameter types)]; the name in the model is made of the parameter types*)
val overload_table : (string * (string * ty list) list) list Unsynchronized.ref = Unsynchronized.ref []

fun last_component n = (case String.fields (fn c => c = #".") n of [] => n | l => List.last l)

fun vtype p t =
  (case t of
     TyInt (true, w) => if w = 256 then "TSint" else err p "the narrow signed integer types are not supported"
   | TyInt (false, _) => "TSint"
   | TyAddr _ => "TAddress"
   | TyBool => "TBool"
   | TyBytesN n => "(TBytes " ^ string_of_int n ^ ")"
   | TyBytes => "(TBytes 0)"
   | TyString => "(TBytes 0)"
   | TyUser n => if is_contract_type (last_component n) then "TAddress" else err p "this type is not a value type"
   | _ => err p "this type is not a value type")

fun stype p t = stype' p [] t

and stype' p seen t =
  (case t of
     TyMapping (k, v) =>
       let
         val _ = (case k of
                    TyInt _ => () | TyAddr _ => () | TyBool => () | TyBytesN _ => () | TyString => () | TyBytes => ()
                  | _ => err p "a mapping key type that is not elementary is not supported")
       in "SType.TMap (" ^ stype' p seen k ^ ") (" ^ stype' p seen v ^ ")" end
   | TyArray (b, NONE) => "SType.DArray (" ^ stype' p seen b ^ ")"
   | TyArray (b, SOME n) => "SType.TArray " ^ IntInf.toString n ^ " (" ^ stype' p seen b ^ ")"
   | TyUser n =>
       if is_contract_type (last_component n) then "SType.TValue TAddress" else
       (case AList.lookup (op =) (!struct_table) (last_component n) of
          SOME fields =>
            if member (op =) seen (last_component n) then err p "a recursive struct"
            else "SType.TEnum [" ^ space_implode ", " (map (fn (ft, _) => stype' p (last_component n :: seen) ft) fields) ^ "]"
        | NONE => err p ("the type " ^ quote n ^ " is not supported yet (enums and contract types)"))
   | _ => "SType.TValue " ^ vtype p t)

(*how well an argument of type `a` fits a parameter of type `p`: SOME 0 exact, SOME n an implicit conversion, NONE does not fit*)
fun fit a p =
  (case (a, p) of
     (TyConst _, TyInt _) => SOME 1
   | (TyConst _, TyBytesN _) => SOME 3
   | (TyInt (s1, w1), TyInt (s2, w2)) => if s1 = s2 andalso w1 = w2 then SOME 0 else if s1 = s2 andalso w1 < w2 then SOME 2 else NONE
   | (TyAddr b1, TyAddr b2) => if b1 = b2 then SOME 0 else if b1 andalso not b2 then SOME 1 else NONE
   | (TyStrLit _, TyString) => SOME 1
   | (TyStrLit _, TyBytes) => SOME 1
   | (TyStrLit _, TyBytesN _) => SOME 2
   | (TyUser x, TyUser y) => if x = y then SOME 0 else NONE
   | _ => if a = p then SOME 0 else NONE)

(*the overload that a call with these argument types runs*)
fun resolve_overload p f (cands: (string * ty list) list) (atys: ty list) : string =
  let
    val viable =
      map_filter (fn (en, ptys) =>
        if length ptys <> length atys then NONE
        else
          let val scores = map2 fit atys ptys
          in if exists is_none scores then NONE else SOME (en, fold (fn s => fn acc => acc + the s) scores 0) end) cands
  in
    (case sort (fn ((_, a), (_, b)) => int_ord (a, b)) viable of
       [] => err p ("no overload of " ^ quote f ^ " fits the arguments")
     | [(en, _)] => en
     | (en, a) :: (_, b) :: _ => if a < b then en else err p ("the call of the overloaded function " ^ quote f ^ " is ambiguous"))
  end

(*does a type contain a mapping (delete leaves mappings alone)?*)
fun holds_mapping t =
  (case t of
     TyMapping _ => true
   | TyArray (b, _) => holds_mapping b
   | TyUser n => (case AList.lookup (op =) (!struct_table) (last_component n) of SOME fs => exists (fn (ft, _) => holds_mapping ft) fs | NONE => false)
   | _ => false)

fun is_struct n = is_some (AList.lookup (op =) (!struct_table) (last_component n))

fun member_index p n f =
  (case AList.lookup (op =) (!struct_table) (last_component n) of
     SOME fs =>
       (case find_index (fn (_, fname) => fname = f) fs of
          ~1 => err p ("the struct " ^ quote n ^ " has no member " ^ quote f)
        | i => (i, #1 (nth fs i)))
   | NONE => err p ("member access on something that is not a struct"))

fun is_signed t = (case t of TyInt (true, _) => true | _ => false)
fun uwidth t = (case t of TyInt (false, w) => SOME w | _ => NONE)
fun type_name t =
  (case t of
     TyBytesN n => SOME ("bytes" ^ string_of_int n)
   | _ => NONE)

(*is a type a value of 256 bits: a word*)
fun is_int t = (case t of TyInt _ => true | TyConst _ => true | _ => false)

(*the exact value of a constant integer expression*)
fun cval (env: env) e : IntInf.int option =
  let
    fun both f a b = (case (cval env a, cval env b) of (SOME x, SOME y) => f (x, y) | _ => NONE)
  in
    (case e of
       ENum s => parse_number s
     | ETuple ([a], _) => cval env a
     | EUn ("-", a, _) => Option.map (fn v => ~v) (cval env a)
     | EBin ("+", a, b, _) => both (fn (x, y) => SOME (x + y)) a b
     | EBin ("-", a, b, _) => both (fn (x, y) => SOME (x - y)) a b
     | EBin ("*", a, b, _) => both (fn (x, y) => SOME (x * y)) a b
     | EBin ("/", a, b, _) => both (fn (x, y) => if y = 0 orelse x mod y <> 0 then NONE else SOME (IntInf.quot (x, y))) a b
     | EBin ("%", a, b, _) =>
         both (fn (x, y) => if y = 0 then NONE else let val r = IntInf.rem (x, y) in SOME r end) a b
     | EBin ("**", a, b, _) => both (fn (x, y) => if y < 0 orelse y > 4096 then NONE else SOME (IntInf.pow (x, IntInf.toInt y))) a b
     | _ => NONE)
  end

(*no calls (and no assignments) inside: reordering or duplicating the evaluation is harmless*)
fun pure e =
  (case e of
     ENum _ => true | EStr _ => true | EHex _ => true | EBool _ => true | EId _ => true | EType _ => true
   | EMember (a, _, _) => pure a
   | EIndex (a, b, _) => pure a andalso pure b
   | ECall (EId ("keccak256", _), args, _) => forall pure args
   | ECall (EMember (EId ("abi", _), m, _), args, _) => (m = "encode" orelse m = "encodePacked") andalso forall pure args
   | ECall (EType _, args, _) => forall pure args
   | ECall (EId ("address", _), args, _) => forall pure args
   | ECall (EId ("payable", _), args, _) => forall pure args
   | ECall _ => false
   | EBin (_, a, b, _) => pure a andalso pure b
   | EUn (opr, a, _) => not (member (op =) ["++", "--", "++post", "--post", "delete"] opr) andalso pure a
   | ECond (a, b, c, _) => pure a andalso pure b andalso pure c
   | EAssign _ => false
   | ETuple (es, _) => forall pure es
   | ECallOpts _ => false)

fun epos e =
  (case e of
     ENum _ => 0 | EStr _ => 0 | EHex _ => 0 | EBool _ => 0
   | EId (_, p) => p | EType (_, p) => p | EMember (_, _, p) => p | EIndex (_, _, p) => p | ECall (_, _, p) => p
   | EBin (_, _, _, p) => p | EUn (_, _, p) => p | ECond (_, _, _, p) => p | EAssign (_, _, _, p) => p | ETuple (_, p) => p
   | ECallOpts (_, _, p) => p)

fun default_text p t =
  (case t of
     TyInt _ => "(sint_monad 0)"
   | TyBool => "false_monad"
   | TyAddr _ => "null_monad"
   | TyBytesN n => bytes_text (replicate n 0)
   | TyBytes => "(bytes_monad2 [])"
   | TyString => "(bytes_monad2 [])"
   | _ => err p "delete of a value of this type is not supported")

(*the common type of the operands of an arithmetic operation*)
fun common p a b =
  (case (a, b) of
     (TyConst _, TyConst _) => TyInt (false, 256)
   | (TyConst _, _) => b
   | (_, TyConst _) => a
   | (TyInt (s1, w1), TyInt (s2, w2)) =>
       if s1 = s2 then TyInt (s1, Int.max (w1, w2)) else err p "an operation on a signed and an unsigned integer"
   | _ => err p "arithmetic on operands that are not integers")

fun declared_names ss =
  let
    fun one s =
      (case s of
         SDecl (_, n, _, _, _) => [n]
       | SIf (_, a, b) => one a @ (case b of NONE => [] | SOME b => one b)
       | SWhile (_, b) => one b
       | SDoWhile (b, _) => one b
       | SFor (i, _, _, b) => (case i of NONE => [] | SOME i => one i) @ one b
       | SBlock ss => maps one ss
       | SUnchecked ss => maps one ss
       | _ => [])
  in maps one ss end

(*Solidity does not specify the order of evaluation of the operands, so an expression whose operands interfere through state is
  refused (the transpiler does the same): the effects of an expression, as (reads, writes) of names of state variables*)
fun effects (env: env) (bodies: string -> (stmt list * expr list) option) e =
  let
    val state_names = map fst (#state env)
    fun root x = (case x of EId (n, _) => SOME n | EIndex (a, _, _) => root_of a | EMember (a, _, _) => root_of a | _ => NONE)
    and root_of x = root x
    fun ex_e seen x : string list * string list =
      let
        fun both xs = fold (fn (r, w) => fn (r0, w0) => (r @ r0, w @ w0)) (map (ex_e seen) xs) ([], [])
      in
        (case x of
           EId (n, _) => if member (op =) state_names n andalso not (is_some (local_ty env (emitted env n))) then ([n], []) else ([], [])
         | EMember (a, "balance", _) => let val (r, w) = ex_e seen a in ("@balance" :: r, w) end
         | EMember (a, _, _) => ex_e seen a
         | EIndex (a, b, _) => both [a, b]
         | EAssign (_, l, r, _) =>
             let val (r1, w1) = both [l, r]
                 val w2 = (case root l of SOME n => if member (op =) state_names n then [n] else [] | NONE => ["*"])
             in (r1, w2 @ w1) end
         | EUn (opr, a, _) =>
             let val (r, w) = ex_e seen a in
               if member (op =) ["++", "--", "++post", "--post", "delete"] opr
               then (r, (case root a of SOME n => if member (op =) state_names n then [n] else [] | NONE => ["*"]) @ w)
               else (r, w)
             end
         | EBin (_, a, b, _) => both [a, b]
         | ECond (a, b, c, _) => both [a, b, c]
         | ETuple (es, _) => both es
         | ECall (EMember (a, m, _), args, _) =>
             let val (r, w) = both (a :: args) in
               if member (op =) ["transfer", "send", "call", "delegatecall", "staticcall"] m then (r, "*" :: w) else (r, w)
             end
         | ECall (EId (f, _), args, _) =>
             let val (r, w) = both args in
               if member (op =) seen f then (r, w)
               else (case bodies f of
                       SOME (stmts, extra) =>
                         let val (r2, w2) = fold (fn s => fn (r0, w0) => let val (a, b) = stmt_effects (f :: seen) s in (a @ r0, b @ w0) end) stmts ([], [])
                             val (r3, w3) = both' (f :: seen) extra
                         in (r @ r2 @ r3, w @ w2 @ w3) end
                     | NONE => (r, w))
             end
         | ECall (a, args, _) => both (a :: args)
         | _ => ([], []))
      end
    and both' seen xs = fold (fn x => fn (r0, w0) => let val (r, w) = ex_e seen x in (r @ r0, w @ w0) end) xs ([], [])
    and stmt_effects seen s =
      (case s of
         SDecl (_, _, _, i, _) => (case i of SOME e => ex_e seen e | NONE => ([], []))
       | SExpr (e, _) => ex_e seen e
       | SIf (c, a, b) => both' seen ([c] @ []) |> (fn (r, w) => let val (r1, w1) = stmt_effects seen a val (r2, w2) = (case b of SOME b => stmt_effects seen b | NONE => ([], [])) in (r @ r1 @ r2, w @ w1 @ w2) end)
       | SWhile (c, b) => let val (r, w) = ex_e seen c val (r1, w1) = stmt_effects seen b in (r @ r1, w @ w1) end
       | SDoWhile (b, c) => let val (r, w) = ex_e seen c val (r1, w1) = stmt_effects seen b in (r @ r1, w @ w1) end
       | SFor (i, c, st, b) =>
           let
             val (r0, w0) = (case i of SOME i => stmt_effects seen i | NONE => ([], []))
             val (r1, w1) = both' seen (the_list c @ the_list st)
             val (r2, w2) = stmt_effects seen b
           in (r0 @ r1 @ r2, w0 @ w1 @ w2) end
       | SBlock ss => fold (fn s => fn (r0, w0) => let val (a, b) = stmt_effects seen s in (a @ r0, b @ w0) end) ss ([], [])
       | SUnchecked ss => fold (fn s => fn (r0, w0) => let val (a, b) = stmt_effects seen s in (a @ r0, b @ w0) end) ss ([], [])
       | SReturn (SOME e, _) => ex_e seen e
       | SEmit (e, _) => ex_e seen e
       | _ => ([], []))
  in ex_e [] e end

fun conflicts (ra, wa) (rb, wb) =
  let
    fun inter a b = exists (fn x => member (op =) b x) a
    fun nonempty l = not (null l)
  in
    (member (op =) rb "@any" andalso nonempty wa) orelse (member (op =) ra "@any" andalso nonempty wb)
    orelse (member (op =) wa "*" andalso nonempty (rb @ wb)) orelse (member (op =) wb "*" andalso nonempty (ra @ wa))
    orelse inter wa (rb @ wb) orelse inter wb ra
  end

(*the expressions whose operands are evaluated in an order that is not specified*)
fun check_order (env: env) bodies e =
  let
    fun eff x = effects env bodies x
    fun check p kids =
      let val es = map eff kids in
        List.app (fn (i, ei) => List.app (fn (j, ej) => if i <> j andalso not (null (snd ei)) andalso conflicts ei ej then
          err p "an expression whose operands' evaluation order matters (one writes state that another reads or writes; Solidity does not specify the order)" else ()) (tag_list 0 es)) (tag_list 0 es)
      end
    and tag_list _ [] = []
      | tag_list i (x :: xs) = (i, x) :: tag_list (i + 1) xs
    fun walk x =
      (case x of
         EBin (opr, a, b, p) => (if opr = "&&" orelse opr = "||" then () else check p [a, b]; walk a; walk b)
       | ECall (f, args, p) => ((if length args > 1 then check p args else ()); walk f; List.app walk args)
       | EIndex (a, b, p) => (check p [a, b]; walk a; walk b)
       | EAssign (opr, l, r, p) =>
           ((case l of
               EIndex (_, i, _) => if opr = "=" then check p [r, i] else check p [r, l]
             | _ => if opr = "=" then () else check p [r, l]);
            walk l; walk r)
       | EMember (a, _, _) => walk a
       | EUn (_, a, _) => walk a
       | ECond (a, b, c, _) => (walk a; walk b; walk c)
       | ETuple (es, _) => List.app walk es
       | _ => ())
  in walk e end

fun has_return ss =
  exists (fn s =>
    (case s of
       SReturn _ => true
     | SIf (_, a, b) => has_return [a] orelse (case b of SOME b => has_return [b] | NONE => false)
     | SWhile (_, b) => has_return [b]
     | SDoWhile (b, _) => has_return [b]
     | SFor (_, _, _, b) => has_return [b]
     | SBlock ss => has_return ss
     | SUnchecked ss => has_return ss
     | _ => false)) ss

(*all expressions of a statement list*)
fun exprs_of ss =
  maps (fn s =>
    (case s of
       SDecl (_, _, _, i, _) => the_list i
     | SExpr (e, _) => [e]
     | SIf (c, a, b) => c :: exprs_of [a] @ (case b of SOME b => exprs_of [b] | NONE => [])
     | SWhile (c, b) => c :: exprs_of [b]
     | SDoWhile (b, c) => c :: exprs_of [b]
     | SFor (i, c, st, b) => (case i of SOME i => exprs_of [i] | NONE => []) @ the_list c @ the_list st @ exprs_of [b]
     | SBlock b => exprs_of b
     | SUnchecked b => exprs_of b
     | SReturn (e, _) => the_list e
     | SEmit (e, _) => [e]
     | SRevert (e, _) => the_list e
     | _ => [])) ss

(*how many calls to other contracts have been translated (also those of functions that are omitted: they make the contract keep the epoch counter)*)
val ext_call_count : int Unsynchronized.ref = Unsynchronized.ref 0

(*loops with flags (break, continue, do-while): how many in the current function (numbers the flag variables), and the (break flag, continue flag) of the loop being translated*)
val loop_k : int Unsynchronized.ref = Unsynchronized.ref 0
val jump : (string option * string option) option Unsynchronized.ref = Unsynchronized.ref NONE

(*the jumps of a statement that belong to the loop around it (a nested loop owns its own)*)
fun jumps_of s : string list =
  (case s of
     SBreak _ => ["break"]
   | SContinue _ => ["continue"]
   | SIf (_, a, b) => jumps_of a @ (case b of SOME b => jumps_of b | NONE => [])
   | SBlock ss => maps jumps_of ss
   | SUnchecked ss => maps jumps_of ss
   | _ => [])

val current_fn : string Unsynchronized.ref = Unsynchronized.ref ""

val known_classes : string list Unsynchronized.ref = Unsynchronized.ref []

(*all identifiers; with `members`, the function of a call super.f() or A.f() counts as referenced*)
fun idents_gen members e =
  let val rec_ = idents_gen members in
    (case e of
       EId (n, _) => [n]
     | EMember (EId (a, _), m, _) => if members andalso (a = "super" orelse member (op =) (!known_classes) a) then [a, m] else [a]
     | EMember (a, _, _) => rec_ a
     | EIndex (a, b, _) => rec_ a @ rec_ b
     | ECall (f, args, _) => rec_ f @ maps rec_ args
     | EBin (_, a, b, _) => rec_ a @ rec_ b
     | EUn (_, a, _) => rec_ a
     | ECond (a, b, c, _) => rec_ a @ rec_ b @ rec_ c
     | EAssign (_, a, b, _) => rec_ a @ rec_ b
     | ETuple (es, _) => maps rec_ es
     | _ => [])
  end

fun idents_of_expr e = idents_gen true e
fun idents_plain e = idents_gen false e


(** calls to other contracts **)

(*the name of a type in the signature of a function that is called: uintN, int256, bool, address (also contracts)*)
fun ext_tname p t =
  (case t of
     TyInt (false, w) => "uint" ^ string_of_int w
   | TyInt (true, 256) => "int256"
   | TyBool => "bool"
   | TyAddr _ => "address"
   | TyUser n => if is_contract_type (last_component n) then "address" else err p "an external call with a parameter or result that is not an elementary value"
   | _ => err p "an external call with a parameter or result of this type is not supported")

fun ext_ty_of s =
  if s = "bool" then TyBool else if s = "address" then TyAddr false else if s = "int256" then TyInt (true, 256)
  else TyInt (false, the (Int.fromString (String.extract (s, 4, NONE))))

fun words_of s = String.tokens Char.isSpace s

(*the clauses of the lines `@custom:assume <clause>` of the natspec of a called function*)
fun assume_lines doc =
  map_filter (fn line =>
    let val (pre, rest) = Substring.position "@custom:assume" (Substring.full line) in
      if Substring.isEmpty rest then NONE
      else SOME (filter (fn w => w <> "*/") (words_of (Substring.string (Substring.triml (size "@custom:assume") rest))))
    end) (String.fields (fn c => c = #"\n") doc)

fun ext_nocallback doc = exists (fn ws => ws = ["nocallback"]) (assume_lines doc)

fun assume_bounds clauses rty =
  let
    val w = (case rty of TyInt (false, w) => SOME w | _ => NONE)
    val lo = fold (fn c => fn m => (case c of ["min", n] => Int.max (m, 0) |> (fn _ => IntInf.max (m, the (parse_number n))) | _ => m)) clauses (0: IntInf.int)
    val cap = (case w of SOME w => two_pow w - 1 | NONE => (0: IntInf.int))
    val hi = fold (fn c => fn m => (case c of ["max", n] => IntInf.min (m, the (parse_number n)) | _ => m)) clauses cap
  in (lo, hi) end

fun ext_assumptions p sg (rty: ty option) doc : string list list =
  let
    val found =
      fold (fn ws => fn acc =>
        (case ws of
           [] => err p ("an empty @custom:assume on " ^ quote sg)
         | ["nocallback"] => acc
         | [k] => if k = "norevert" orelse k = "constant" then (if member (op =) acc [k] then acc else acc @ [[k]]) else err p ("unknown assumption " ^ quote ("@custom:assume " ^ k) ^ " on " ^ quote sg)
         | [k, n] =>
             if (k = "min" orelse k = "max") andalso is_some (parse_number n) andalso (String.isPrefix "0x" n orelse forall Char.isDigit (String.explode n))
             then (let val c = [k, IntInf.toString (the (parse_number n))] in if member (op =) acc c then acc else acc @ [c] end)
             else err p ("unknown assumption " ^ quote ("@custom:assume " ^ space_implode " " ws) ^ " on " ^ quote sg)
         | _ => err p ("unknown assumption " ^ quote ("@custom:assume " ^ space_implode " " ws) ^ " on " ^ quote sg))) (assume_lines doc) []
  in
    if null found then []
    else
      let
        val rt = (case rty of NONE => err p ("an assumption on " ^ quote sg ^ ", which returns nothing") | SOME t => t)
        val _ = if exists (fn c => hd c = "min" orelse hd c = "max") found andalso (case rt of TyInt (false, _) => false | _ => true)
                then err p ("a min/max assumption on " ^ quote sg ^ ", whose result is not an unsigned integer") else ()
        val (lo, hi) = assume_bounds found rt
        val _ = if lo > hi then err p ("contradictory assumptions on " ^ quote sg ^ ": min " ^ IntInf.toString lo ^ " > max " ^ IntInf.toString hi) else ()
      in found end
  end

(*the bodies that a call of f runs, for the effects: its statements and those of its modifiers, and the arguments of the modifiers*)
fun bodies_of (env: env) f =
  (case AList.lookup (op =) (#funcs env) f of
     NONE => NONE
   | SOME (fs: fsig) =>
       let
         val modbodies = maps (fn (m, _, _) => (case AList.lookup (op =) (#mods env) m of SOME (md: moddef) => #body md | NONE => [])) (#mods fs)
         val args = maps (fn (_, a, _) => a) (#mods fs)
       in SOME (#body fs @ modbodies, args) end)

fun trivially_safe (env: env) e =
  (case e of
     ENum _ => true | EStr _ => true | EHex _ => true | EBool _ => true
   | EId (n, _) =>
       is_some (local_ty env (emitted env n)) orelse is_some (AList.lookup (op =) (#consts env) n) orelse n = "this"
       orelse (case AList.lookup (op =) (#state env) n of SOME (TyMapping _) => false | SOME _ => true | NONE => false)
   | EMember (EId (a, _), m, _) => member (op =) [("msg", "sender"), ("msg", "value"), ("block", "timestamp")] (a, m)
   | ETuple ([a], _) => trivially_safe env a
   | ECall (EType _, args, _) => forall (trivially_safe env) args
   | _ => false)

(*the model has a single exception without data: a message is a string literal, or a variable that holds one (anything else could itself revert)*)
fun message_check env p msgs =
  List.app (fn m => (case m of EStr _ => () | EId _ => if trivially_safe env m then () else err p "this message of require/revert is not supported"
                              | _ => err p "only a string literal (or a variable that holds one) is supported as the message of require and revert")) msgs

fun has_call (env: env) s =
  let
    fun in_expr e =
      (case e of
         ECall (EId (f, _), args, _) => is_some (AList.lookup (op =) (#funcs env) f) orelse exists in_expr args
       | ECall (a, args, _) => in_expr a orelse exists in_expr args
       | EMember (a, _, _) => in_expr a
       | EIndex (a, b, _) => in_expr a orelse in_expr b
       | EBin (_, a, b, _) => in_expr a orelse in_expr b
       | EUn (_, a, _) => in_expr a
       | ECond (a, b, c, _) => in_expr a orelse in_expr b orelse in_expr c
       | EAssign (_, a, b, _) => in_expr a orelse in_expr b
       | ETuple (es, _) => exists in_expr es
       | _ => false)
    fun in_stmt s =
      (case s of
         SDecl (_, _, _, i, _) => (case i of SOME e => in_expr e | NONE => false)
       | SExpr (e, _) => in_expr e
       | SIf (c, a, b) => in_expr c orelse in_stmt a orelse (case b of SOME b => in_stmt b | NONE => false)
       | SWhile (c, b) => in_expr c orelse in_stmt b
       | SDoWhile (b, c) => in_expr c orelse in_stmt b
       | SFor (i, c, st, b) => (case i of SOME i => in_stmt i | NONE => false) orelse (case c of SOME c => in_expr c | NONE => false) orelse (case st of SOME x => in_expr x | NONE => false) orelse in_stmt b
       | SBlock ss => exists in_stmt ss
       | SUnchecked ss => exists in_stmt ss
       | SReturn (SOME e, _) => in_expr e
       | SEmit (e, _) => in_expr e
       | _ => false)
  in in_stmt s end

fun reader_of p t =
  (case t of
     TyBool => "readBool"
   | TyAddr _ => "readAddress"
   | TyBytesN _ => "readBytes"
   | TyBytes => "readBytes"
   | TyString => "readBytes"
   | TyInt _ => "readSint"
   | _ => err p "a parameter of this type in an internal call is not supported")

fun narrow (env: env) text t op0 =
  (case uwidth t of
     NONE => text
   | SOME w =>
       if w = 256 then text
       else
         (use env "narrow";
          if !(#unchecked env) then "(mod_monad " ^ text ^ " (sint_monad " ^ IntInf.toString (two_pow w) ^ "))"
          else if op0 = "-" then text
          else "(below_monad " ^ text ^ " (sint_monad " ^ IntInf.toString (two_pow w) ^ "))"))

fun arith (env: env) op0 signed =
  if signed andalso not (!(#unchecked env)) then
    (use env "signed"; (case op0 of "+" => "splus_safe_monad" | "-" => "sminus_safe_monad" | _ => "smult_safe_monad"))
  else
    let val name = (case op0 of "+" => "plus_monad" | "-" => "minus_monad" | _ => "mult_monad")
    in if !(#unchecked env) then name else name ^ "_safe" end

fun ex (env: env) (e: expr) : string * ty =
  (case cval env e of
     SOME v =>
       (if v < ~(two_pow 255) orelse v >= two_pow 256 then err (epos e) "a constant outside the range of a word" else ();
        (const_text v, TyConst v))
   | NONE => ex' env e)

and ex' env e =
  (case e of
     ENum _ => err (epos e) "this number literal is not an integer"
   | EBool b => ((if b then "true_monad" else "false_monad"), TyBool)
   | EStr s => (bytes_text (unescape s), TyStrLit s)
   | EHex s => (bytes_text (hex_bytes s), TyStrLit s)
   | ETuple ([a], _) => ex env a
   | ETuple (_, p) => err p "tuples are not supported"
   | EType (_, p) => err p "a type is not a value"
   | EId (n, p) => ident env n p
   | EMember (a, m, p) => member_expr env a m p
   | EIndex (_, _, p) => let val (kind, name, idx, t) = path env e in (lookup_text p kind name idx t, t) end
   | ECall _ => call env e false
   | ECond (c, a, b, p) =>
       let
         val (ct, _) = ex env c
         val (at, aty) = ex env a
         val (bt, bty) = ex env b
         val t = (case (aty, bty) of (TyInt _, _) => common p aty bty | (TyConst _, TyInt _) => common p aty bty | (TyConst _, TyConst _) => TyInt (false, 256) | _ => aty)
       in ("(cond_monad " ^ ct ^ " " ^ at ^ " " ^ bt ^ ")", t) end
   | EAssign (_, l, _, p) =>
       if not (pure l) then err p "an assignment used as a value whose target contains a call"
       else (case e of EAssign (opr, l, r, p) =>
                let val (lt, lty) = ex env l in (do_block [assign env (opr, l, r, p), lt], lty) end
              | _ => err p "assignment")
   | EUn (opr, a, p) => unary env opr a p
   | EBin (opr, l, r, p) => binop env opr l r p)

and ident env n p =
  let val n' = emitted env n in
    (case local_ty env n' of
       SOME t => ("(stackLookup (" ^ str_name n' ^ ") [])", t)
     | NONE =>
         (case AList.lookup (op =) (#consts env) n of
            SOME (init, t) => let val (txt, _) = ex_as env init t in (txt, t) end
          | NONE =>
              (case AList.lookup (op =) (#state env) n of
                 SOME (TyMapping _) => err p ("the mapping " ^ quote n ^ " is used without an index")
               | SOME t => ("(storeLookup (" ^ str_name n ^ ") [])", t)
               | NONE =>
                   if n = "this" then ("this_monad", TyAddr false)
                   else err p ("unknown name " ^ quote n))))
  end

and member_expr env a m p =
  (case (a, m) of
     (EId ("msg", _), "sender") => ("sender_monad", TyAddr true)
   | (EId ("msg", _), "value") => ("value_monad", TyInt (false, 256))
   | (EId ("block", _), "timestamp") => ("block_timestamp_monad", TyInt (false, 256))
   | (EId ("tx", _), "origin") => (use env "origin"; ("tx_origin_monad", TyAddr false))
   | (EId ("block", _), "number") => (use env "env"; ("block_number_monad", TyInt (false, 256)))
   | (EId ("block", _), "chainid") => (use env "env"; ("chain_id_monad", TyInt (false, 256)))
   | (ECall (EId ("type", _), [EId (i, _)], _), "interfaceId") =>
       (case #interface_ids env i of
          SOME v => (let val bs = [IntInf.toInt (v div 16777216 mod 256), IntInf.toInt (v div 65536 mod 256), IntInf.toInt (v div 256 mod 256), IntInf.toInt (v mod 256)]
                     in (bytes_text bs, TyBytesN 4) end)
        | NONE => err p "type(...).interfaceId of something that is not an interface")
   | (ECall (EId ("type", _), [EType (t, _)], _), _) =>
       if m <> "max" andalso m <> "min" then err p ("the member " ^ quote m ^ " of type(...) is not supported")
       else
       (case t of
          TyInt (false, w) => (const_text (if m = "max" then two_pow w - 1 else 0), t)
        | TyInt (true, 256) =>
            let val v = if m = "max" then two_pow 255 - 1 else ~(two_pow 255) in (const_text v, t) end
        | _ => err p ("type(...)." ^ m ^ " of this type is not supported"))
   | (_, "balance") =>
       let val (ta, tyA) = ex env a in
         (case tyA of
            TyAddr _ => (use env "balance"; ("(balance_monad " ^ ta ^ ")", TyInt (false, 256)))
          | _ => err p "balance of something that is not an address")
       end
   | _ =>
       (case a of
          EId _ => path_member env a m p
        | EIndex _ => path_member env a m p
        | EMember _ => path_member env a m p
        | _ => err p ("the member " ^ quote m ^ " is not supported yet")))

(*a member of a struct place, or the length of an array place*)
and path_member env a m p : string * ty =
  let val (kind, name, idx, bty) = path env a in
    (case bty of
       TyUser n =>
         let val (i, fty) = member_index p n m
         in (lookup_text p kind name (idx @ ["(sint_monad " ^ string_of_int i ^ ")"]) fty, fty) end
     | TyArray (_, _) =>
         if m = "length" then
           ((if kind = "storage" then "(storeArrayLength (" else "(arrayLength (") ^ str_name name ^ ") [" ^ space_implode ", " idx ^ "])", TyInt (false, 256))
         else err p ("the member " ^ quote m ^ " of an array is not supported")
     | _ => err p ("the member " ^ quote m ^ " is not supported yet"))
  end

(*a variable and its indices: storage or stack, the name, the index texts, the type of the place*)
and path env e : string * string * string list * ty =
  (case e of
     EId (n, p) =>
       let val n' = emitted env n in
         (case local_ty env n' of
            SOME t => ("stack", n', [], t)
          | NONE =>
              (case AList.lookup (op =) (#state env) n of
                 SOME t => ("storage", n, [], t)
               | NONE => err p ("unknown name " ^ quote n)))
       end
   | EIndex (b, i, p) =>
       let val (kind, name, idx, bty) = path env b in
         (case bty of
            TyMapping (kt, vt) => let val (it, _) = ex_as env i kt in (kind, name, idx @ [it], vt) end
          | TyArray (et, _) => let val (it, _) = ex env i in (kind, name, idx @ [it], et) end
          | _ => err p "indexing something that is not a mapping or an array")
       end
   | EMember (b, f, p) =>
       let val (kind, name, idx, bty) = path env b in
         (case bty of
            TyUser n => let val (i, fty) = member_index p n f in (kind, name, idx @ ["(sint_monad " ^ string_of_int i ^ ")"], fty) end
          | _ => err p ("the member " ^ quote f ^ " of something that is not a struct"))
       end
   | ETuple ([a], _) => path env a
   | _ => err (epos e) "this is not a variable")

and lookup_text p kind name idx t =
  (case t of
     TyMapping _ => err p ("the mapping " ^ quote name ^ " is used without an index")
   | _ =>
       (if kind = "storage" then "(storeLookup (" else "(stackLookup (") ^ str_name name ^ ") [" ^ space_implode ", " idx ^ "])")

(*the expression where a value of type t is expected: a constant converted implicitly to bytesN is the N bytes of its big-endian value*)
and ex_as env e t : string * ty =
  (case (t, ex env e) of
     (TyBytesN n, (_, TyConst v)) =>
       if v < 0 orelse v >= IntInf.pow (256, n) then err (epos e) ("a constant that does not fit bytes" ^ string_of_int n)
       else
         let
           fun bytes_of v k = if k = 0 then [] else bytes_of (v div 256) (k - 1) @ [IntInf.toInt (v mod 256)]
         in (bytes_text (bytes_of v n), t) end
   | (_, r) => r)

and unary env opr a p =
  (case opr of
     "!" => let val (t, _) = ex env a in ("(not_monad " ^ t ^ ")", TyBool) end
   | "-" =>
       let val (t, ty) = ex env a in
         (case ty of
            TyInt (true, _) =>
              if !(#unchecked env) then ("(minus_monad (sint_monad 0) " ^ t ^ ")", ty)
              else (use env "signed"; ("(sminus_safe_monad (sint_monad 0) " ^ t ^ ")", ty))
          | _ => err p "unary minus on an unsigned integer")
       end
   | "~" =>
       let
         val (t, ty) = ex env a
         val _ = use env "bits"
         val text = "(bitnot_monad " ^ t ^ ")"
       in
         (case uwidth ty of
            SOME w => if w < 256 then ("(mod_monad " ^ text ^ " (sint_monad " ^ IntInf.toString (two_pow w) ^ "))", ty) else (text, ty)
          | NONE => (text, ty))
       end
   | "++" => incdec env a "+=" true p
   | "--" => incdec env a "-=" true p
   | "++post" => incdec env a "+=" false p
   | "--post" => incdec env a "-=" false p
   | _ => err p "this operator is not supported in an expression")

and incdec env sub opr prefix p =
  if not (pure sub) then err p "'++' or '--' used as a value on a target that contains a call"
  else
    let
      val asg = assign env (opr, sub, ENum "1", p)
      val (st, sty) = ex env sub
    in
      if prefix then (do_block [asg, st], sty)
      else (do_block ["old <- " ^ st, asg, "(return old)"], sty)
    end

and bound env l r build p =
  let val (lt, _) = ex env l val (rt, _) = ex env r
  in do_block ["lv <- " ^ lt, "rv <- " ^ rt, build "(return lv)" "(return rv)"] end

and divmod env opr a b signed =
  let
    val name =
      if signed then (use env "signed"; if opr = "%" then "smod_monad" else if !(#unchecked env) then "sdiv_monad" else "sdiv_safe_monad")
      else if opr = "%" then "mod_monad" else (use env "div"; "div_monad")
  in "(cond_monad (equals_monad " ^ b ^ " (sint_monad 0)) (assert_monad false_monad) (" ^ name ^ " " ^ a ^ " " ^ b ^ "))" end

and bit_op env opr a b tres sg p =
  let
    val _ = use env "bits"
    val w = uwidth tres
  in
    (case opr of
       "&" => "(bitand_monad " ^ a ^ " " ^ b ^ ")"
     | "|" => "(bitor_monad " ^ a ^ " " ^ b ^ ")"
     | "^" => "(bitxor_monad " ^ a ^ " " ^ b ^ ")"
     | ">>" => "(" ^ (if sg then "sar_monad" else "shr_monad") ^ " " ^ a ^ " " ^ b ^ ")"
     | "<<" =>
         let val text = "(shl_monad " ^ a ^ " " ^ b ^ ")" in
           (case w of SOME w => if w < 256 then "(mod_monad " ^ text ^ " (sint_monad " ^ IntInf.toString (two_pow w) ^ "))" else text | NONE => text)
         end
     | "**" =>
         if sg then err p "exponentiation of a signed integer"
         else narrow env ("(" ^ (if !(#unchecked env) then "exp_wrap_monad" else "exp_safe_monad") ^ " " ^ a ^ " " ^ b ^ ")") tres "*"
     | _ => err p ("the operator " ^ quote opr ^ " is not supported yet"))
  end

and binop env opr l r p =
  let
    val (lt, lty) = ex env l
    val (rt, rty) = ex env r
  in
    if member (op =) ["&", "|", "^", "<<", ">>", "**"] opr then
      let val tres = (case lty of TyConst _ => (case rty of TyInt _ => rty | _ => TyInt (false, 256)) | _ => lty)
      in (bit_op env opr lt rt tres (is_signed lty) p, tres) end
    else if opr = "&&" then ("(cond_monad " ^ lt ^ " " ^ rt ^ " false_monad)", TyBool)
    else if opr = "||" then ("(cond_monad " ^ lt ^ " true_monad " ^ rt ^ ")", TyBool)
    else if member (op =) ["+", "-", "*"] opr then
      let
        val tres = common p lty rty
        val sg = is_signed tres
        val text = "(" ^ arith env opr sg ^ " " ^ lt ^ " " ^ rt ^ ")"
      in (narrow env text tres opr, tres) end
    else if member (op =) ["/", "%"] opr then
      let
        val tres = common p lty rty
        val sg = is_signed tres
      in
        if not (pure r) then (bound env l r (fn a => fn b => divmod env opr a b sg) p, tres)
        else (divmod env opr lt rt sg, tres)
      end
    else
      let
        val sg = is_signed lty orelse is_signed rty
        val less = if sg then (use env "signed"; "sless_monad") else "less_monad"
        val (lt', _) = ex_as env l rty
        val (rt', _) = ex_as env r lty
        fun build a b =
          (case opr of
             ">" => "(" ^ less ^ " " ^ b ^ " " ^ a ^ ")"
           | "<=" => "(not_monad (" ^ less ^ " " ^ b ^ " " ^ a ^ "))"
           | _ => "(not_monad (" ^ less ^ " " ^ a ^ " " ^ b ^ "))")
      in
        (case opr of
           "==" => ("(equals_monad " ^ lt' ^ " " ^ rt' ^ ")", TyBool)
         | "!=" => ("(not_monad (equals_monad " ^ lt' ^ " " ^ rt' ^ "))", TyBool)
         | "<" => ("(" ^ less ^ " " ^ lt' ^ " " ^ rt' ^ ")", TyBool)
         | ">" => if pure l andalso pure r then (build lt' rt', TyBool) else (bound env l r build p, TyBool)
         | "<=" => if pure l andalso pure r then (build lt' rt', TyBool) else (bound env l r build p, TyBool)
         | ">=" => if pure l andalso pure r then (build lt' rt', TyBool) else (bound env l r build p, TyBool)
         | _ => err p ("the operator " ^ quote opr ^ " is not supported yet"))
      end
  end

(*calls: conversions, require/assert/revert, internal calls, transfer*)
and call env e discard : string * ty =
  (case e of
     ECall (EType (t, _), [a], p) => conv env t a p
   | ECall (EId ("payable", _), [a], p) => let val (txt, _) = ex env a in (txt, TyAddr true) end
   | ECall (EId ("$enum", _), [ENum n, a], p) =>
       let
         val (ta, tya) = ex env a
         val _ =
           (case tya of
              TyInt (true, _) => err p "a conversion of a signed integer to an enum is not supported"
            | TyInt _ => ()
            | TyConst v => if v < 0 then err p "a negative number converted to an enum" else ()
            | _ => err p "a conversion to an enum from something that is not an unsigned integer")
         val _ = use env "narrow"
       in ("(below_monad " ^ ta ^ " (sint_monad " ^ n ^ "))", TyInt (false, 8)) end
   | ECall (EId ("keccak256", _), args, p) => keccak env args p
   | ECall (EId ("ecrecover", _), args, p) =>
       if length args <> 4 then err p "ecrecover takes four arguments"
       else
         (use env "ecrecover";
          ("(ecrecover_monad " ^ space_implode " " (map_index (fn (i, a) => fst (if i <> 1 then ex_as env a (TyBytesN 32) else ex env a)) args) ^ ")", TyAddr false))
   | ECall (EId ("require", _), c :: msgs, p) => (message_check env p msgs; let val (ct, _) = ex env c in ("(assert_monad " ^ ct ^ ")", TyBool) end)
   | ECall (EId ("assert", _), [c], p) => let val (ct, _) = ex env c in ("(assert_monad " ^ ct ^ ")", TyBool) end
   | ECall (EId ("revert", _), msgs, p) => (message_check env p msgs; ("(assert_monad false_monad)", TyBool))
   | ECall (EMember (EId ("super", _), f0, fp), args, p) =>
       let val f = resolve_name env f0 args p in
       (case #super_of env (!(#home env)) f of
          SOME (_, fs) => internal_call_to env ("super_" ^ the_default (isa_ident f) (AList.lookup (op =) (#alias env) f)) fs args p discard false
        | NONE => err fp ("super." ^ f ^ "() without an implementation"))
       end
   | ECall (EMember (EId (a, _), f0, fp), args, p) =>
       if member (op =) (#classes env) a then
         let val f = resolve_name env f0 args p in
         (case #base_of env a f of
            SOME (_, fs) =>
              if a = !(#home env) then err p (a ^ "." ^ f ^ "() in " ^ a ^ " itself")
              else internal_call_to env ("base__" ^ String.map Char.toLower (String.substring (a, 0, 1)) ^ String.extract (a, 1, NONE) ^ "__" ^ the_default (isa_ident (#name fs)) (AList.lookup (op =) (#alias env) (#name fs))) fs args p discard false
          | NONE => err fp (a ^ "." ^ f ^ "() without an implementation"))
         end
       else call_member env e discard
   | ECall (EId (n, _), [a], p) =>
       if is_contract_type (last_component n) andalso not (AList.defined (op =) (#funcs env) n) then
         let val (ta, tya) = ex env a in
           (case tya of
              TyAddr _ => (ta, TyUser n)
            | TyUser _ => (ta, TyUser n)
            | TyConst 0 => ("null_monad", TyUser n)
            | _ => err p ("a conversion to the contract type " ^ quote n ^ " from something that is not an address"))
         end
       else call_plain env e discard
   | ECall _ => call_plain env e discard
   | _ => err (epos e) "not a call")

and call_plain env e discard : string * ty =
  (case e of
     ECall (EId (f0, fp), args, p) =>
       if is_some (#lib_ctx env) andalso member (op =) (#lib_fns env (the (#lib_ctx env))) f0 then
         let
           val l = the (#lib_ctx env)
           val (en, fs) = #lib_fn env l f0 (map (fn a => snd (ex env a)) args) p
         in internal_call_to env en fs args p discard false end
       else
       let val f = resolve_name env f0 args p in
       (case AList.lookup (op =) (#funcs env) f of
          SOME fs => internal_call_to env (the_default (isa_ident (#name fs)) (AList.lookup (op =) (#alias env) f)) fs args p discard true
        | NONE => err fp ("unknown function " ^ quote f0))
       end
   | ECall (EMember _, _, _) => call_member env e discard
   | ECall (_, _, p) => err p "this form of call is not supported yet")

and delete_composite env p kind name idx tt =
  (if kind <> "storage" then err p "delete through a storage pointer" else ();
   if holds_mapping tt then err p "delete of an array or struct that contains a mapping (Solidity leaves the mapping as it is)" else ();
   use env "arrays";
   "delete_monad (" ^ str_name name ^ ") [" ^ space_implode ", " idx ^ "] (sdefault (" ^ stype p tt ^ "))")

(*a.push(x), a.push(), a.pop() on a dynamic storage array*)
and push_pop env a m args p discard : string * ty =
  let
    val (kind, name, idx, tt) = path env a
    val _ = if kind <> "storage" then err p (m ^ " through a storage pointer") else ()
    val elem = (case tt of TyArray (b, NONE) => b | _ => err p (m ^ " on something that is not a dynamic array"))
    val _ = if not (pure a) then err p (m ^ " on a place that contains a call") else ()
    val _ = use env "arrays"
    val lst = space_implode ", " idx
  in
    if m = "pop" then
      (if not (null args) then err p "pop with an argument" else ();
       ("(pop_monad (" ^ str_name name ^ ") [" ^ lst ^ "])", TyBool))
    else
      let
        val _ = if not discard then err p "the result of push is used" else ()
        val default = "(allocate (" ^ str_name name ^ ") [" ^ lst ^ "] (sdefault (" ^ stype p elem ^ ")))"
      in
        (case args of
           [] => (default, TyBool)
         | [v] =>
             let
               val _ = (case elem of TyInt _ => () | TyAddr _ => () | TyBool => () | TyBytesN _ => () | _ => err p "push of a value that is not an elementary number, address, bool or bytesN")
               val (vt, _) = ex_as env v elem
               val last = space_implode ", " (idx @ ["(minus_monad (return n) (sint_monad 1))"])
             in
               (do_block ["v <- " ^ vt, default, "n <- (storeArrayLength (" ^ str_name name ^ ") [" ^ lst ^ "])",
                          "assign_storage_monad (" ^ str_name name ^ ") [" ^ last ^ "] (return v)"], TyBool)
             end
         | _ => err p "push arity")
      end
  end

and resolve_name env f args p =
  (case AList.lookup (op =) (!overload_table) f of
     SOME cands => resolve_overload p f cands (map (fn a => snd (ex env a)) args)
   | NONE => f)

and call_member env e discard : string * ty =
  (case e of
     ECall (EMember (a, m, _), args, p) =>
       if (m = "push" orelse m = "pop") andalso (case a of EId _ => true | EIndex _ => true | EMember _ => true | _ => false)
       then push_pop env a m args p discard
       else call_member2 env e discard
   | _ => call_member2 env e discard)

and call_member2 env e discard : string * ty =
  (case e of
     ECall (EMember (recv, f0, fp), args, p) =>
       let
         val direct = (case recv of EId (l, _) => if member (op =) (#libs env) l andalso member (op =) (#lib_fns env l) f0 then SOME l else NONE | _ => NONE)
       in
         (case direct of
            SOME l =>
              let val (en, fs) = #lib_fn env l f0 (map (fn a => snd (ex env a)) args) p
              in internal_call_to env en fs args p discard false end
          | NONE =>
              (case using_target env recv f0 args p of
                 SOME (en, fs) => internal_call_to env en fs (recv :: args) p discard false
               | NONE => call_member3 env e discard))
       end
   | _ => call_member3 env e discard)

(*the library function that `recv.f(args)` runs through a `using L for T` directive*)
and using_target env recv f args p : (string * fsig) option =
  let
    val by_name = filter (fn (l, _) => member (op =) (#lib_fns env l) f) (!(#usings env))
  in
    if null by_name then NONE
    else
      let
        val rty = snd (ex env recv)
        val atys = rty :: map (fn a => snd (ex env a)) args
        fun applies (_, tyopt) = (case tyopt of NONE => true | SOME ty => is_some (fit rty ty))
      in
        (case filter applies by_name of
           [] => NONE
         | (l, _) :: _ => SOME (#lib_fn env l f atys p))
      end
  end

and call_member3 env e discard : string * ty =
  (case e of
     ECall (EMember (recv, f0, fp), args, p) =>
       let
         fun plain r = (case r of EId (n, _) => not (member (op =) ["abi", "msg", "block", "tx", "super"] n) | EIndex _ => true | EMember _ => true | ECall _ => true | ETuple _ => true | _ => false)
         val rty = if plain recv then SOME (snd (ex env recv)) else NONE
       in
         (case rty of
            SOME (TyUser c) => if is_contract_type (last_component c) then ext_call env recv (last_component c) f0 args p else call_member4 env e discard
          | _ => call_member4 env e discard)
       end
   | _ => call_member4 env e discard)

(*`t.f(a1, ..., an)` on a value of contract or interface type: a call to code that is not modelled (Solidity_Ext, "Calls to other contracts")*)
and ext_call env recv c f args p : string * ty =
  let
    fun unwrap r = (case r of ETuple ([x], _) => unwrap x | ECall (EId (n, _), [x], _) => if is_contract_type (last_component n) then unwrap x else r | ECall (EType _, [x], _) => unwrap x | _ => r)
    val _ = (case unwrap recv of EId ("this", _) => err p "an external call on `this` (the contract's own code would run, with itself as msg.sender)" | _ => ())
    val atys = map (fn a => snd (ex env a)) args
    val callee = #find_callee env c f atys p
    val _ = if length args <> length (#params callee) then err p "an external call with the wrong number of arguments" else ()
    val ptypes = map (fn (pr: param) => ext_tname p (#ty pr)) (#params callee)
    val _ = if length (#returns callee) > 1 then err p "an external call that returns several values" else ()
    val rty = (case #returns callee of [r] => SOME (#ty r) | _ => NONE)
    val rtype = Option.map (ext_tname p) rty
    val view = (#mut callee = "view" orelse #mut callee = "pure")
    val sg = f ^ "(" ^ space_implode "," ptypes ^ ")"
    val rty' = Option.map ext_ty_of rtype
    val assume = ext_assumptions p sg rty' (#doc callee)
    val nocb = (not view) andalso ext_nocallback (#doc callee)
    val _ = if not (exists (fn (s: ext_sig) => #sg s = sg) (!(#ext_sigs env)))
            then (#ext_sigs env) := !(#ext_sigs env) @ [{sg = sg, params = ptypes, ret = rtype, view = view, assume = assume, nocallback = nocb}] else ()
    val _ = use env "ext"
    val _ = ext_call_count := !ext_call_count + 1
    val ghost = "(" ^ str_name "ghost_ext_epoch" ^ ")"
    val steps0 = ["t <- " ^ fst (ex env recv)]
    val steps1 = map_index (fn (i, a) => "a" ^ string_of_int i ^ " <- " ^ fst (ex env a)) args
    val argl = "[" ^ space_implode ", " (map (fn i => "a" ^ string_of_int i) (0 upto (length ptypes - 1))) ^ "]"
    val steps2 = ["ext_code_monad t"]
    val steps3 =
      if view then []
      else
        ["assign_storage_monad " ^ ghost ^ " [] (plus_monad (storeLookup " ^ ghost ^ " []) (sint_monad 1))"]
        @ (if nocb then [] else ["transfer_monad (return t) (sint_monad 0)"])
    val kind = (case rtype of NONE => "unit" | SOME "bool" => "flag" | SOME "address" => "addr" | SOME _ => "word")
    val steps4 = ["ep <- storeLookup " ^ ghost ^ " []", "ext_" ^ kind ^ "_monad ''" ^ sg ^ "'' ep t " ^ argl]
    val text = do_block (steps0 @ steps1 @ steps2 @ steps3 @ steps4)
    val text' =
      (case rty' of
         SOME (TyInt (false, w)) => if w < 256 then (use env "narrow"; "(below_monad " ^ text ^ " (sint_monad " ^ IntInf.toString (two_pow w) ^ "))") else text
       | _ => text)
  in (text', (case rty' of SOME t => t | NONE => TyBool)) end

and call_member4 env e discard : string * ty =
  (case e of
     ECall (EMember (a, "transfer", _), [v], p) =>
       let
         val (ta, tya) = ex env a
         val _ = (case tya of TyAddr _ => () | _ => err p "transfer on a receiver that is not an address")
         val (tv, _) = ex env v
       in ("(transfer_monad " ^ ta ^ " " ^ tv ^ ")", TyBool) end
   | ECall (_, _, p) => err p "this form of call is not supported yet"
   | _ => err (epos e) "not a call")

(*keccak256(b), keccak256(abi.encode(a, ...)), keccak256(abi.encodePacked(a, ...)): see the transpiler for what the model can express*)
and keccak env args p : string * ty =
  let
    fun kind_of x ty =
      (case ty of
         TyString => "dyn" | TyBytes => "dyn" | TyStrLit _ => "dyn"
       | TyInt _ => "static" | TyConst _ => "static" | TyAddr _ => "static" | TyBool => "static" | TyBytesN _ => "static"
       | _ => err (epos x) "a hashed value of this type is not supported")
    fun tstr_of x ty =
      let
        fun with_loc base =
          (case x of
             EId (n, _) =>
               let val n' = emitted env n in
                 (case AList.lookup (op =) (!(#locs env)) n' of
                    SOME "" => base
                  | SOME l => base ^ " " ^ l
                  | NONE => if AList.defined (op =) (#state env) n then base ^ " storage ref" else base)
               end
           | _ => err (epos x) ("the type of this " ^ base ^ " expression is not known here"))
      in
        (case ty of
           TyInt (false, w) => "uint" ^ string_of_int w | TyInt (true, w) => "int" ^ string_of_int w | TyAddr _ => "address" | TyBool => "bool"
         | TyBytesN n => "bytes" ^ string_of_int n | TyString => with_loc "string" | TyBytes => with_loc "bytes"
         | TyStrLit _ =>
             let
               val bs = (case x of EHex h => hex_bytes h | EStr s => unescape s | _ => [])
               fun hex2 b = (if b < 16 then "0" else "") ^ String.map Char.toLower (Int.fmt StringCvt.HEX b)
             in
               if forall (fn b => b >= 32 andalso b < 127) bs then "literal_string \"" ^ String.implode (map Char.chr bs) ^ "\""
               else "literal_string hex\"" ^ implode (map hex2 bs) ^ "\""
             end
         | TyConst _ => "int_const"
         | _ => "?")
      end
  in
    (case args of
       [ECall (EMember (EId ("abi", _), m, _), xs, pa)] =>
         let
           val _ = if m <> "encode" andalso m <> "encodePacked" then err pa ("abi." ^ m ^ " is not supported") else ()
           val typed = map (fn x => (x, snd (ex env x))) xs
           val kinds = map (fn (x, ty) => kind_of x ty) typed
           val ndyn = length (filter (fn k => k = "dyn") kinds)
         in
           if m = "encodePacked" andalso ndyn > 1 then err pa "abi.encodePacked with more than one dynamically sized argument (ambiguous: not injective)"
           else if m = "encodePacked" andalso length xs = 1 andalso ndyn = 1 then ("(keccak256_monad " ^ fst (ex env (hd xs)) ^ ")", TyBytesN 32)
           else
             let
               val parts = map (fn x => fst (ex env x)) xs
               val sig_kinds =
                 map (fn ((x, ty), k) =>
                        if k = "dyn" then "d"
                        else (case ty of
                                TyAddr _ => "a"
                              | TyBytesN n => if n < 32 then "b" ^ string_of_int n else "w"
                              | _ => "w")) (typed ~~ kinds)
               val sg0 = space_implode "," sig_kinds
               val word_types = ["uint256", "int256", "bytes32"]
               val sg =
                 if m = "encodePacked" andalso not (forall (fn (x, ty) => member (op =) word_types (case ty of TyInt (false, 256) => "uint256" | TyInt (true, 256) => "int256" | TyBytesN 32 => "bytes32" | _ => "-")) typed)
                 then
                   (if exists (fn (_, ty) => (case ty of TyConst _ => true | _ => false)) typed
                    then err pa "abi.encodePacked of a number literal (its width is the smallest type that holds it)" else ();
                    "P:" ^ space_implode "," (map (fn (x, ty) => tstr_of x ty) typed))
                 else sg0
               val sigtext = bytes_text (map Char.ord (String.explode sg))
             in ("(keccak256_monad (encodeABI_monad [" ^ space_implode ", " (sigtext :: parts) ^ "]))", TyBytesN 32) end
         end
     | [a] =>
         let val (ta, tya) = ex env a in
           (case kind_of a tya of
              "dyn" => ("(keccak256_monad " ^ ta ^ ")", TyBytesN 32)
            | _ => err p "keccak256 of something that is not a byte string")
         end
     | _ => err p "keccak256 takes one argument")
  end

and conv env t a p : string * ty =
  let val (ta, tya) = ex env a in
    (case t of
       TyAddr _ =>
         (case (tya, a) of
            (TyConst 0, _) => ("null_monad", t)
          | (_, EId ("this", _)) => ("this_monad", t)
          | (TyAddr _, _) => (ta, t)
          | _ => err p "this conversion to address is not supported")
     | TyBytesN n =>
         (case tya of
            TyConst 0 => (bytes_text (replicate n 0), t)
          | TyBytesN _ => err p "a conversion between bytesN types is not supported"
          | _ => err p "this conversion to bytesN is not supported")
     | TyString => (case tya of TyString => (ta, t) | TyBytes => (ta, t) | TyStrLit _ => (ta, t) | _ => err p "this conversion to string is not supported")
     | TyBytes => (case tya of TyString => (ta, t) | TyBytes => (ta, t) | TyStrLit _ => (ta, t) | _ => err p "this conversion to bytes is not supported")
     | TyInt (false, tw) =>
         (case tya of
            TyInt (false, sw) =>
              if tw >= sw then (ta, t) else (use env "narrow"; ("(mod_monad " ^ ta ^ " (sint_monad " ^ IntInf.toString (two_pow tw) ^ "))", t))
          | TyConst _ => (ta, t)
          | TyInt (true, 256) => if tw = 256 then (ta, t) else err p "this integer conversion is not supported"
          | _ => err p "this conversion to an integer type is not supported")
     | TyInt (true, 256) =>
         (case tya of
            TyConst _ => (ta, t)
          | TyInt (_, 256) => (ta, t)
          | _ => err p "this conversion to int is not supported")
     | _ => err p "this type conversion is not supported")
  end

and internal_call_to env target (fs: fsig) args p discard check_value : string * ty =
  let
    val params = #params fs
    val f = #name fs
    val _ = if length args <> length params then err p ("the function " ^ quote f ^ " takes " ^ string_of_int (length params) ^ " argument(s)") else ()
    val rty = (case #returns fs of [r] => #ty r | [] => TyBool | _ => TyBool)
    val _ = if check_value andalso not (null (#returns fs)) andalso not discard andalso not (member (op =) (#value_ret env) f)
            then err p ("the value of the call of " ^ quote f ^ " is used, but the function is not marked as returning it") else ()
    val _ = if length (#returns fs) > 1 andalso not discard then err p ("the function " ^ quote f ^ " returns several values and the value is used") else ()
  in
    if null args then ("(icall " ^ target ^ ")", rty)
    else
      let
        val steps =
          maps (fn (i, (pr: param, a)) =>
                  let
                    val (at, _) = ex_as env a (#ty pr)
                    val si = string_of_int i
                  in
                    ["a" ^ si ^ " <- " ^ at, "b" ^ si ^ " <- readValue a" ^ si, "w" ^ si ^ " <- " ^ reader_of p (#ty pr) ^ " b" ^ si]
                  end)
            (tag_from 0 (params ~~ args))
        val ws = space_implode " " (map (fn i => "w" ^ string_of_int i) (0 upto (length args - 1)))
        val _ = if exists (fn (pr: param) => (case #ty pr of TyBool => true | _ => false)) params then use env "readbool" else ()
        val _ = if exists (fn (pr: param) => (case #ty pr of TyBytesN _ => true | TyBytes => true | TyString => true | _ => false)) params then use env "readbytes" else ()
      in (do_block (steps @ ["(icall (" ^ target ^ " " ^ ws ^ "))"]), rty) end
  end

and tag_from _ [] = []
  | tag_from i (x :: xs) = (i, x) :: tag_from (i + 1) xs

(*assignment: the text of the monad*)
and assign env (op0, target, value, p) : string =
  let
    val (kind, name, idx, tt) = path env target
    val _ = (case tt of TyMapping _ => err p ("the mapping " ^ quote name ^ " is assigned without an index") | _ => ())
    val rhs =
      if op0 = "=" then fst (ex_as env value tt)
      else
        let
          val opr = String.substring (op0, 0, size op0 - 1)
          val (lt, lty) = ex env target
          val (vt, vty) = ex env value
          val _ = if not (pure target) then err p "a compound assignment with a call in the target" else ()
        in
          if member (op =) ["&", "|", "^", "<<", ">>"] opr then bit_op env opr lt vt tt (is_signed tt) p
          else if member (op =) ["/", "%"] opr then
            (if not (pure value) then err p ("the operator " ^ quote op0 ^ " with a divisor that contains calls") else ();
             divmod env opr lt vt (is_signed tt))
          else if opr = "**" then bit_op env opr lt vt tt (is_signed tt) p
          else narrow env ("(" ^ arith env opr (is_signed tt) ^ " " ^ lt ^ " " ^ vt ^ ")") tt opr
        end
  in assign_text kind name idx rhs end

and assign_text kind name idx rhs =
  (if kind = "storage" then "assign_storage_monad (" else "assign_stack_monad (") ^ str_name name ^ ") [" ^ space_implode ", " idx ^ "] " ^ rhs

and stmt env s : string list =
  (case s of
     SDecl (t, n, loc, init, p) =>
     if loc = "storage" then
       let
         val n' = emitted env n
         val is_comp = (case t of TyArray _ => true | TyUser u => is_struct u | _ => false)
         val _ = if not is_comp then err p ("local " ^ quote n ^ " is a storage pointer to something that is not a struct or an array") else ()
         val _ = if AList.defined (op =) (#state env) n orelse AList.defined (op =) (#consts env) n then err p ("the local " ^ quote n ^ " shadows a state variable") else ()
         val _ = if is_some (local_ty env n') then err p ("the name " ^ quote n ^ " is declared twice") else ()
         val init_e = (case init of SOME e => e | NONE => err p "a storage pointer without a value")
         val _ = (case init_e of EId _ => () | EIndex _ => () | EMember _ => () | _ => err p "a storage pointer that is not initialised with a storage place")
         val d = "sdecl (" ^ stype p t ^ ") (" ^ str_name n' ^ ")"
         val _ = add_local env n' t
         val _ = (#locs env) := (n', "storage") :: !(#locs env)
       in [d, "assign_stack_monad (" ^ str_name n' ^ ") [] " ^ fst (ex env init_e)] end
     else
       let
         val n' = emitted env n
         val _ = (case t of TyMapping _ => err p "a local mapping is not supported" | _ => ())
         val vt = vtype p t
         val _ = if AList.defined (op =) (#state env) n orelse AList.defined (op =) (#consts env) n then err p ("the local " ^ quote n ^ " shadows a state variable") else ()
         val _ = if is_some (local_ty env n') then err p ("the name " ^ quote n ^ " is declared twice") else ()
         val d = "decl " ^ vt ^ " (" ^ str_name n' ^ ")"
         val _ = add_local env n' t
         val _ = (#locs env) := (n', loc) :: !(#locs env)
         val a = (case init of NONE => [] | SOME e => ["assign_stack_monad (" ^ str_name n' ^ ") [] " ^ fst (ex_as env e t)])
       in d :: a end
   | SExpr (e, p) =>
       (case e of
          EAssign (opr, l, r, pp) => [assign env (opr, l, r, pp)]
        | EUn ("delete", a, pp) =>
            let val (kind, name, idx, tt) = path env a in
              (case tt of
                 TyArray _ => [delete_composite env pp kind name idx tt]
               | TyUser u => if is_struct u then [delete_composite env pp kind name idx tt] else err pp "delete of a value of this type is not supported"
               | _ => [assign_text kind name idx (default_text pp tt)])
            end
        | EUn (opr, a, pp) =>
            if member (op =) ["++", "++post"] opr then [assign env ("+=", a, ENum "1", pp)]
            else if member (op =) ["--", "--post"] opr then [assign env ("-=", a, ENum "1", pp)]
            else err p "this expression statement is not supported"
        | ECall _ => [fst (call env e true)]
        | _ => err p "this expression statement is not supported")
   | SIf (c, a, b) =>
       let val (ct, _) = ex env c in
         ["(cond_monad " ^ ct ^ " " ^ block_of env a ^ " " ^ (case b of NONE => "skip_monad" | SOME b => block_of env b) ^ ")"]
       end
   | SWhile (c, b) =>
       if has_call env s then err (epos c) "a loop that contains an internal call"
       else if not (null (jumps_of b)) then flagged_loop env s
       else let val (ct, _) = ex env c in ["(while_monad " ^ ct ^ " " ^ block_of env b ^ ")"] end
   | SFor (i, c, st, b) =>
       if has_call env s then err (case c of SOME c => epos c | NONE => 0) "a loop that contains an internal call"
       else if not (null (jumps_of b)) then flagged_loop env s
       else
         let
           val ipart = (case i of NONE => [] | SOME i => stmt env i)
           val body = block_of env b
           val spart = (case st of NONE => [] | SOME e => stmt env (SExpr (e, epos e)))
           val body' = if null spart then body else do_block (body :: spart)
           val ct = (case c of NONE => "true_monad" | SOME c => fst (ex env c))
         in ipart @ ["(while_monad " ^ ct ^ " " ^ body' ^ ")"] end
   | SBreak p =>
       (case !jump of
          SOME (SOME f, _) => ["assign_stack_monad (" ^ str_name f ^ ") [] true_monad"]
        | _ => err p "break outside of a loop")
   | SContinue p =>
       (case !jump of
          SOME (_, SOME f) => ["assign_stack_monad (" ^ str_name f ^ ") [] true_monad"]
        | _ => err p "continue outside of a loop")
   | SDoWhile (b, c) =>
       if has_call env s then err (epos c) "a loop that contains an internal call" else flagged_loop env s
   | SBlock ss => [block env ss]
   | SUnchecked ss =>
       let
         val old = !(#unchecked env)
         val _ = (#unchecked env) := true
         val text = block env ss
         val _ = (#unchecked env) := old
       in [text] end
   | SEmit (e, p) =>
       (case e of
          ECall (_, args, _) =>
            let val parts = map_filter (fn a => if trivially_safe env a then NONE else SOME (fst (ex env a))) args
            in if null parts then ["skip_monad"] else parts end
        | _ => err p "emit of something that is not an event")
   | SRevert (_, _) => ["(assert_monad false_monad)"]
   | SPlaceholder p => (case #placeholder env of SOME text => [text] | NONE => err p "the placeholder `_` is only valid in a modifier")
   | SReturn (_, p) => err p "a return statement that is not at the end of the function"
   | SUnsupported (what, p) => err p (what ^ " is not supported")
   | SLowCall (_, _, _, p) => err p "the result of a low-level call has to be checked by require(ok) (and nothing else may use it)"
   | SReturnValue e => [fst (ex env e)]
   | SReturnVar n => ["stackLookup (" ^ str_name n ^ ") []"]
   | SEval e => if trivially_safe env e then ["skip_monad"] else [fst (ex env e)])

(*a loop with `break`, `continue` or `do ... while`: flags (locals of the function) carry the jumps, exactly as `transpile.py` does*)
and flagged_loop env s : string list =
  let
    val (body, init, cond, step, dowhile) =
      (case s of
         SWhile (c, b) => (b, [], SOME c, NONE, false)
       | SDoWhile (b, c) => (b, [], SOME c, NONE, true)
       | SFor (i, c, st, b) => (b, (case i of NONE => [] | SOME i => [i]), c, st, false)
       | _ => raise Fail "flagged_loop")
    val js = jumps_of body
    val _ = loop_k := !loop_k + 1
    val k = string_of_int (!loop_k)
    val brk = if member (op =) js "break" then SOME ("_brk" ^ k) else NONE
    val cnt = if member (op =) js "continue" then SOME ("_cnt" ^ k) else NONE
    val first = if dowhile then SOME ("_first" ^ k) else NONE
    fun flag_decl n init =
      let val _ = add_local env n TyBool in ["decl TBool (" ^ str_name n ^ ")", "assign_stack_monad (" ^ str_name n ^ ") [] " ^ init] end
    fun look n = "(stackLookup (" ^ str_name n ^ ") [])"
    val init_text = maps (fn i => stmt env i) init
    val flags1 = (case brk of SOME n => flag_decl n "false_monad" | NONE => []) @ (case first of SOME n => flag_decl n "true_monad" | NONE => [])
    val c0 = (case cond of SOME c => fst (ex env c) | NONE => "true_monad")
    val c1 = (case brk of SOME n => "(cond_monad " ^ look n ^ " false_monad " ^ c0 ^ ")" | NONE => c0)
    val c2 = (case first of SOME n => "(cond_monad " ^ look n ^ " true_monad " ^ c1 ^ ")" | NONE => c1)
    val old = !jump
    val _ = jump := SOME (brk, cnt)
    val body_res =
      Exn.capture (fn () =>
        (case first of SOME n => ["assign_stack_monad (" ^ str_name n ^ ") [] false_monad"] | NONE => [])
        @ (case cnt of SOME n => flag_decl n "false_monad" | NONE => [])
        @ [block_of env body]
        @ (case step of
             NONE => []
           | SOME e =>
               let val st = do_block (stmt env (SExpr (e, epos e)))
               in [(case brk of SOME n => "(cond_monad " ^ look n ^ " skip_monad " ^ st ^ ")" | NONE => st)] end)) ()
    val _ = jump := old
    val body_parts = Exn.release body_res
  in init_text @ flags1 @ ["(while_monad " ^ c2 ^ " " ^ do_block body_parts ^ ")"] end

(*run the rest of a block only when no break and no continue has happened in this iteration*)
and guard_jump rest =
  (case !jump of
     SOME (brk, cnt) =>
       let
         fun wrap f r = (case f of SOME n => "(cond_monad (stackLookup (" ^ str_name n ^ ") []) skip_monad " ^ r ^ ")" | NONE => r)
       in wrap brk (wrap cnt rest) end
   | NONE => rest)

and block env ss = join_do (stmts_text env ss)

(*statements in order; `(bool ok, ) = a.call{value: v}(""); ...; require(ok);` is the transfer of a with a callback, placed where the call is*)
and stmts_text env ss =
  (case ss of
     [] => []
   | SLowCall (ok, a, v, p) :: rest =>
       let
         fun mentions s = member (op =) (maps idents_plain (exprs_of [s])) ok
         val j = find_index mentions rest
         val _ = if j < 0 then err p "the result of a low-level call is never checked" else ()
         val between = take j rest
         val _ = if has_return between then err p "a return between a low-level call and the require that checks it" else ()
         val chk = nth rest j
         val _ = (case chk of
                    SExpr (ECall (EId ("require", _), EId (n, _) :: msgs, _), _) =>
                      if n = ok andalso forall (fn EStr _ => true | _ => false) msgs then () else err p "the result of a low-level call has to be checked by require(ok) (and nothing else may use it)"
                  | _ => err p "the result of a low-level call has to be checked by require(ok) (and nothing else may use it)")
         val (ta, _) = ex env a
         val (tv, _) = ex env v
       in ("(transfer_monad " ^ ta ^ " " ^ tv ^ ")") :: stmts_text env between @ stmts_text env (drop (j + 1) rest) end
   | s :: rest =>
       let val here = stmt env s in
         if is_some (!jump) andalso not (null rest) andalso not (null (jumps_of s)) then here @ [guard_jump (block env rest)]
         else here @ stmts_text env rest
       end)

and block_of env s = (case s of SBlock ss => block env ss | _ => block env [s])

(*one invocation of a modifier around `inner`, the translated rest of the function: the body of the modifier with `_` replaced by it.
  The parameters and variables of the modifier live in the same stack frame as those of the function, so they get unique names
  (_m<k>_<name>); the locals of the function are hidden meanwhile; the arguments are evaluated once, in the scope of the function.*)
and apply_modifier env (name, args, p) inner =
  (case AList.lookup (op =) (#mods env) name of
     NONE => err p ("unknown modifier " ^ quote name ^ " (base constructors in the modifier list are not supported yet)")
   | SOME (md: moddef) =>
       let
         val _ = if length args <> length (#params md) then err p ("the modifier " ^ quote name ^ " takes " ^ string_of_int (length (#params md)) ^ " argument(s)") else ()
         val _ = #counter env := !(#counter env) + 1
         val k = !(#counter env)
         val arg_texts = map (fn (pr: param, a) => fst (ex_as env a (#ty pr))) (#params md ~~ args)
         val ren0 = map (fn (pr: param) => (#name pr, "_m" ^ string_of_int k ^ "_" ^ #name pr)) (#params md)
         val ren = fold (fn n => fn r => if AList.defined (op =) r n then r else (n, "_m" ^ string_of_int k ^ "_" ^ n) :: r) (declared_names (#body md)) ren0
         (*the do-block of the modifier around `placeholder`, given the texts of the arguments*)
         fun build arg_texts placeholder =
           let
             val outer_locals = !(#locals env)
             val outer_unchecked = !(#unchecked env)
             val env1 = with_rename env ren (SOME placeholder)
             val _ = (#locals env) := []
             val _ = (#unchecked env) := false
             val param_parts =
               maps (fn (pr: param, a) =>
                       let val en = the (AList.lookup (op =) ren (#name pr)) in
                         (add_local env en (#ty pr);
                          ["decl " ^ vtype p (#ty pr) ^ " (" ^ str_name en ^ ")", "assign_stack_monad (" ^ str_name en ^ ") [] " ^ a])
                       end)
                 (#params md ~~ arg_texts)
             val parts = param_parts @ [block env1 (#body md)]
             val _ = (#locals env) := outer_locals
             val _ = (#unchecked env) := outer_unchecked
           in do_block parts end
       in
         if not (#mod_abbrev_on env) then build arg_texts inner
         else
           let
             val needs_k = not (null (#params md)) orelse not (null (declared_names (#body md)))
             val abbr = "mod_" ^ #mod_class env name ^ "_" ^ name ^ (if needs_k then "_" ^ string_of_int k else "")
             val formals = map (fn i => "a" ^ string_of_int i) (0 upto (length args - 1))
             val _ =
               if AList.defined (op =) (!(#mod_abbrevs env)) abbr then ()
               else
                 let
                   val _ = explicit_bind := true
                   val def_res = Exn.capture (fn () => build formals "r") ()
                   val _ = explicit_bind := false
                   val def = Exn.release def_res
                 in (#mod_abbrevs env) := !(#mod_abbrevs env) @
                      [(abbr, "context Solidity\nbegin\nabbreviation " ^ abbr ^ " :: \"" ^ space_implode " \<Rightarrow> " (map (fn _ => "('a::address) expression_monad") (formals @ ["r"]) @ ["('a::address) expression_monad"]) ^ "\" where\n  \"" ^ abbr ^ " " ^ space_implode " " (formals @ ["r"]) ^ " \<equiv> " ^ def ^ "\"\nend\n")] end
             (*the arguments are evaluated where the modifier is entered, as in the inlined text*)
             val use_text = "(" ^ abbr ^ " " ^ space_implode " " (map (fn a => "(" ^ a ^ ")") arg_texts @ ["(" ^ inner ^ ")"]) ^ ")"
           in use_text end
       end)

and with_modifiers env (mods: invocation list) text = fold (fn inv => fn t => apply_modifier env inv t) (rev mods) text

(** returns **)

fun stmts_of b = (case b of SBlock ss => ss | _ => [b])

fun always_returns ss =
  (case rev ss of
     [] => false
   | last :: _ =>
       (case last of
          SReturn _ => true
        | SBlock b => always_returns b
        | SUnchecked b => always_returns b
        | SIf (_, a, SOME b) => always_returns (stmts_of a) andalso always_returns (stmts_of b)
        | _ => false))

(*early returns as guard clauses become tail returns: `if (c) { ...; return e; } rest` is `if (c) { ...; return e; } else { rest }` (and
  symmetrically); the statements after an `if` whose branches both return are dropped*)
fun lift_returns ss =
  let
    fun go i [] = NONE
      | go i (s :: rest) =
          (case s of
             SIf (c, a, b) =>
               if null rest then go (i + 1) rest
               else
                 let
                   val tl = stmts_of a
                   val fl = (case b of SOME b => stmts_of b | NONE => [])
                   val rt = always_returns tl
                   val rf = is_some b andalso always_returns fl
                 in
                   if rt andalso rf then SOME (i, s)
                   else if rt then SOME (i, SIf (c, a, SOME (SBlock (lift_returns (fl @ rest)))))
                   else if rf then SOME (i, SIf (c, SBlock (lift_returns (tl @ rest)), b))
                   else go (i + 1) rest
                 end
           | _ => go (i + 1) rest)
    fun inner ss' =
      map (fn s => (case s of SBlock b => SBlock (lift_returns b) | SUnchecked b => SUnchecked (lift_returns b) | _ => s)) ss'
  in
    (case go 0 (inner ss) of
       SOME (i, s) => take i (inner ss) @ [s]
     | NONE => inner ss)
  end

(*the value of a function that is used: every path ends in the value, the value of the do-block*)
fun value_returns p ss (rps: param list) =
  let
    fun always ss' =
      (case rev ss' of
         [] => false
       | last :: _ =>
           (case last of
              SReturn (SOME _, _) => true
            | SBlock b => always b
            | SUnchecked b => always b
            | SIf (_, a, SOME b) => always (stmts_of a) andalso always (stmts_of b)
            | _ => false))
    fun conv ss' =
      (case rev ss' of
         [] => []
       | last :: restr =>
           let val rest = rev restr in
             (case last of
                SReturn (SOME e, _) => rest @ [SReturnValue e]
              | SBlock b => rest @ [SBlock (conv b)]
              | SUnchecked b => rest @ [SUnchecked (conv b)]
              | SIf (c, a, SOME b) => rest @ [SIf (c, SBlock (conv (stmts_of a)), SOME (SBlock (conv (stmts_of b))))]
              | _ => ss')
           end)
  in
    if length rps <> 1 then err p "a function with several return values whose value is used"
    else if always ss then conv ss
    else (case #name (hd rps) of
            "" => err p "a function whose value is used does not return on every path"
          | n => ss @ [SReturnVar n])
  end

(*`return e;` in tail position (the last statement, also in the branches of a last `if`) is its evaluation*)
fun tail_returns ss =
  (case rev ss of
     [] => []
   | last :: restr =>
       let val rest = rev restr in
         (case last of
            SReturn (NONE, _) => rest
          | SReturn (SOME (ETuple ([e], _)), _) => rest @ [SEval e]
          | SReturn (SOME (ETuple (es, _)), _) => rest @ map SEval es
          | SReturn (SOME e, _) => rest @ [SEval e]
          | SBlock b => rest @ [SBlock (tail_returns b)]
          | SUnchecked b => rest @ [SUnchecked (tail_returns b)]
          | SIf (c, a, b) =>
              let fun branch x = SBlock (tail_returns (stmts_of x))
              in rest @ [SIf (c, branch a, Option.map branch b)] end
          | _ => ss)
       end)

(*the names of the functions called with a used value, and all identifiers*)
(*all calls with a flag that says whether the value of the call is discarded (a call that is a statement of its own)*)
fun calls_expr e disc : (expr * bool) list =
  (case e of
     ECall (f, args, _) => (e, disc) :: calls_expr f false @ maps (fn a => calls_expr a false) args
   | EMember (a, _, _) => calls_expr a false
   | EIndex (a, b, _) => calls_expr a false @ calls_expr b false
   | EBin (_, a, b, _) => calls_expr a false @ calls_expr b false
   | EUn (_, a, _) => calls_expr a false
   | ECond (a, b, c, _) => calls_expr a false @ calls_expr b false @ calls_expr c false
   | EAssign (_, a, b, _) => calls_expr a false @ calls_expr b false
   | ETuple (es, _) => maps (fn x => calls_expr x false) es
   | _ => [])

fun calls_stmts ss : (expr * bool) list =
  maps (fn s =>
    (case s of
       SExpr (e, _) => calls_expr e true
     | SDecl (_, _, _, i, _) => maps (fn e => calls_expr e false) (the_list i)
     | SIf (c, a, b) => calls_expr c false @ calls_stmts [a] @ (case b of SOME b => calls_stmts [b] | NONE => [])
     | SWhile (c, b) => calls_expr c false @ calls_stmts [b]
     | SDoWhile (b, c) => calls_expr c false @ calls_stmts [b]
     | SFor (i, c, st, b) => (case i of SOME i => calls_stmts [i] | NONE => []) @ maps (fn e => calls_expr e false) (the_list c) @ maps (fn e => calls_expr e true) (the_list st) @ calls_stmts [b]
     | SBlock b => calls_stmts b
     | SUnchecked b => calls_stmts b
     | SReturn (e, _) => maps (fn e => calls_expr e false) (the_list e)
     | SEmit (e, _) => calls_expr e false
     | SRevert (e, _) => maps (fn e => calls_expr e false) (the_list e)
     | _ => [])) ss

fun value_call (e, disc) =
  (case e of
     ECall (EId (f, _), _, _) => if disc then NONE else SOME f
   | ECall (EMember (EId (a, _), f, _), _, _) => if disc orelse a = "super" orelse member (op =) (!known_classes) a then NONE else SOME f
   | ECall (EMember (_, f, _), _, _) => if disc then NONE else SOME f
   | _ => NONE)

fun value_calls_stmts ss = map_filter value_call (calls_stmts ss)

fun value_calls_expr e = map_filter value_call (calls_expr e false)

fun param_guards p (ps: param list) =
  map_filter (fn (pr: param) =>
    let fun guard bound = SOME ("assert_monad (less_monad (stackLookup (" ^ str_name (#name pr) ^ ") []) (sint_monad " ^ bound ^ "))")
    in
      if #bound pr > 0 then guard (string_of_int (#bound pr))
      else (case uwidth (#ty pr) of SOME w => if w < 256 then guard (IntInf.toString (two_pow w)) else NONE | NONE => NONE)
    end) ps

fun with_guards guards body =
  if null guards then body
  else
    let val parts = guards @ (if body = "skip_monad" then [] else [body])
    in if length parts = 1 then "(" ^ hd parts ^ ")" else do_block parts end

fun guarded body =
  if body = "skip_monad" then "(value_guard)" else do_block ["value_guard", body]

(*the body of a function (the constructor is handled by the caller)*)
fun func_body env bodies (f: func) value_return : string =
  let
    val p = #pos f
    val _ = (#locals env) := map (fn (pr: param) => (#name pr, #ty pr)) (#params f)
    val _ = (#locs env) := map (fn (pr: param) => (#name pr, #loc pr)) (#params f)
    val stmts0 = (case #body f of SOME b => b | NONE => [])
    val _ = List.app (check_order env bodies) (exprs_of stmts0)
    val _ = List.app (fn (m, args, _) =>
              (List.app (check_order env bodies) args;
               case AList.lookup (op =) (#mods env) m of SOME (md: moddef) => List.app (check_order env bodies) (exprs_of (#body md)) | NONE => ())) (#mods f)
    val stmts1 = if has_return stmts0 then lift_returns stmts0 else stmts0
    val rps = #returns f
    val (decls, stmts2) =
      if not (null rps) then
        let
          val decls =
            map_filter (fn (pr: param) =>
              let val vt = vtype p (#ty pr) in
                if #name pr = "" then NONE
                else
                  (if AList.defined (op =) (#state env) (#name pr) orelse AList.defined (op =) (#consts env) (#name pr) then err p ("the return variable " ^ quote (#name pr) ^ " shadows a state variable") else ();
                   if is_some (local_ty env (#name pr)) then err p ("the return variable " ^ quote (#name pr) ^ " redeclares a parameter") else ();
                   add_local env (#name pr) (#ty pr);
                   SOME ("decl " ^ vt ^ " (" ^ str_name (#name pr) ^ ")"))
              end) rps
          val _ = List.app (fn (pr: param) => ignore (vtype p (#ty pr))) rps
          val ss = if value_return then value_returns p stmts1 rps else tail_returns stmts1
          val _ = if has_return ss then err p ("the function " ^ quote (#name f) ^ " has a return statement that is not at the end") else ()
        in (decls, ss) end
      else if has_return stmts1 then
        let val ss = tail_returns stmts1
        in (if has_return ss then err p ("the function " ^ quote (#name f) ^ " has a return statement that is not at the end") else ();
            ([], ss)) end
      else ([], stmts1)
    val text0 = block env stmts2
    val text1 = if null decls then text0 else do_block (decls @ [text0])
    val _ = if value_return andalso not (null (#mods f)) then err p ("the function " ^ quote (#name f) ^ " has modifiers and its value is used") else ()
    val text2 = if value_return then do_block ["skip_monad", text1] else text1
  in with_modifiers env (#mods f) text2 end

(** classes **)

fun c3_lin (cdefs: cdef list) name =
  let
    fun find n = find_first (fn (d: cdef) => #name d = n) cdefs
    fun parents_of n = (case find n of SOME d => map fst (#parents d) | NONE => [])
    fun merge seqs0 =
      let val seqs = filter_out null seqs0 in
        if null seqs then []
        else
          (case get_first (fn s => let val h = hd s in if forall (fn t => not (member (op =) (tl t) h)) seqs then SOME h else NONE end) seqs of
             NONE => error "inconsistent linearisation of the base contracts"
           | SOME h => h :: merge (map (fn s => if hd s = h then tl s else s) seqs))
      end
    fun lin c = c :: merge (map lin (rev (parents_of c)) @ [rev (parents_of c)])
  in lin name end

val needs =
  [("narrow", "below_monad"), ("signed", "sless_monad"), ("div", "div_monad"), ("bits", "bitand_monad"), ("origin", "tx_origin_monad"),
   ("env", "block_number_monad"), ("balance", "balance_monad"), ("readbool", "readBool"), ("readbytes", "readBytes"), ("guard", "value_guard")]

fun check_uses ctxt uses =
  let
    val consts = map fst (#constants (Consts.dest (Sign.consts_of (Proof_Context.theory_of ctxt))))
    fun declared c = exists (fn n => Long_Name.base_name n = c) consts
  in
    List.app (fn u =>
      (case AList.lookup (op =) needs u of
         SOME c =>
           if declared c then ()
           else error ("This Solidity source needs the theory Solidity.Solidity_Ext (the constant " ^ c ^ "): add it to the imports of the theory")
       | NONE => ())) (distinct (op =) uses)
  end

(*overloaded functions get a name made of their parameter types (the decision is made for each hierarchy; here for the whole text)*)
fun rename_overloads (cdefs: cdef list) : cdef list =
  let
    fun find n = find_first (fn (d: cdef) => #name d = n) cdefs
    fun is_contract_name n = is_some (find (last_component n))
    fun tag_of ty =
      (case ty of
         TyUser n => if is_contract_name n then "contract_" ^ last_component n else last_component n
       | _ => abi_type is_contract_name ty)
    fun tag (ptys: ty list) = if null ptys then "none" else space_implode "_" (map tag_of ptys)
    fun sigs_of (f: func) = map #ty (#params f)
    val over =
      distinct (op =)
        (maps (fn (d: cdef) =>
                 if #kind d = "library" then [] else
                 let
                   val lin = map_filter find (c3_lin cdefs (#name d))
                   val fs = maps (fn (x: cdef) => filter (fn (f: func) => #kind f = "function") (#funcs x)) lin
                   val names = distinct (op =) (map #name fs)
                 in filter (fn n => length (distinct (op =) (map sigs_of (filter (fn (f: func) => #name f = n) fs))) > 1) names end) cdefs)
    val table =
      map (fn n =>
        let
          val all = maps (fn (d: cdef) => if #kind d = "library" then [] else map sigs_of (filter (fn (f: func) => #kind f = "function" andalso #name f = n) (#funcs d))) cdefs
        in (n, map (fn sg => (n ^ "__" ^ tag sg, sg)) (distinct (op =) all)) end) over
    val _ = overload_table := table
    fun new_name (f: func) =
      if #kind f <> "function" then #name f
      else
        (case AList.lookup (op =) table (#name f) of
           SOME cands =>
             (case find_first (fn (_, sg) => sg = sigs_of f) cands of SOME (en, _) => en | NONE => #name f)
         | NONE => #name f)
  in
    map (fn (d: cdef) => if #kind d = "library" then d else {name = #name d, kind = #kind d, abstract = #abstract d, parents = #parents d, vars = #vars d,
          funcs = map (fn (f: func) => {name = new_name f, kind = #kind f, params = #params f, returns = #returns f, vis = #vis f, mut = #mut f, virt = #virt f,
                                       over = #over f, mods = #mods f, body = #body f, pos = #pos f, doc = #doc f}) (#funcs d),
          modifiers = #modifiers d, structs = #structs d, enums = #enums d, using = #using d, events = #events d, errors = #errors d, pos = #pos d}) cdefs
  end

fun expand_names ids = maps (fn n => (case AList.lookup (op =) (!overload_table) n of SOME cs => map fst cs | NONE => [n])) ids

fun is_base_of_other_in (cdefs: cdef list) n =
  exists (fn (d: cdef) => d <> d andalso false) cdefs orelse
  exists (fn (d: cdef) => #name d <> n andalso member (op =) (c3_lin cdefs (#name d)) n) cdefs

fun lc_first s = String.map Char.toLower (String.substring (s, 0, 1)) ^ String.extract (s, 1, NONE)

fun elab_class ctxt (cdefs: cdef list) (c: cdef) (is_base_of_other: bool) : contract * ext_sig list * (string * string) list * bool =
  let
    fun find n = find_first (fn (d: cdef) => #name d = n) cdefs
    fun is_real n = (case find n of SOME d => #kind d = "contract" | NONE => false)
    val lin = c3_lin cdefs (#name c)                                     (*most derived first*)
    val base_first = rev (filter is_real lin)                           (*the real contracts of the hierarchy, this one last*)
    val ancestors = filter (fn n => n <> #name c) base_first
    val anc_defs = map_filter find ancestors
    val all_defs = map_filter find base_first
    fun index n = the_default 0 (find_index (fn x => x = n) base_first |> (fn i => if i < 0 then NONE else SOME i))
    val own_vars = filter_out (fn (v: vardef) => #const v) (#vars c)
    val state0 = map (fn (v: vardef) => (#name v, #ty v)) (maps (fn (d: cdef) => filter_out (fn (v: vardef) => #const v) (#vars d)) all_defs)
    val consts = map (fn (v: vardef) => (#name v, (the (#init v), #ty v))) (filter (fn (v: vardef) => #const v andalso is_some (#init v)) (maps #vars all_defs))
    (*modifiers are virtual: every invocation runs the most derived definition of the name*)
    val _ = List.app (fn (d: cdef) => ignore (fold (fn (m: moddef) => fn seen => if member (op =) seen (#name m) then err (#pos m) ("the modifier " ^ quote (#name m) ^ " is declared twice") else #name m :: seen) (#modifiers d) [])) all_defs
    val modvers = maps (fn (d: cdef) => map (fn (m: moddef) => (#name m, (#name d, m))) (#modifiers d)) all_defs
    val mod_names = distinct (op =) (map fst modvers)
    val mod_final = map (fn n => (n, List.last (map snd (filter (fn (n', _) => n' = n) modvers)))) mod_names     (*name -> (class, definition)*)
    val mods = map (fn (n, (_, m)) => (n, m)) mod_final
    val mod_home = map (fn (n, (cl, _)) => (n, cl)) mod_final
    (*the class whose command contains a function: where it is declared, or the class that declares an overriding modifier it uses*)
    fun mod_origin (f: func) (d: cdef) =
      fold (fn (m, _, _) => fn home =>
              (case AList.lookup (op =) mod_home m of SOME hc => if index hc > index home then hc else home | NONE => home)) (#mods f) (#name d)
    (*the functions of the hierarchy: versions base first*)
    val fn_versions = maps (fn (d: cdef) => map (fn (f: func) => ((#kind f, #name f), (d, f))) (filter (fn (f: func) => #kind f <> "constructor") (#funcs d))) all_defs
    val keys = distinct (op =) (map fst fn_versions)
    fun versions key = map snd (filter (fn (k, _) => k = key) fn_versions)
    fun impls key = filter (fn (_, f) => is_some (#body f)) (versions key)
    fun param_sig (f: func) = map (fn (pr: param) => pr) (#params f) |> map #ty
    (*per function: the final implementation (or the last declaration if there is none) and the class that holds it*)
    val finals =
      map (fn key =>
        (case impls key of
           [] => let val (d, f) = List.last (versions key) in (key, (d, f, #name d)) end
         | is => let val (d, f) = List.last is in (key, (d, f, mod_origin f d)) end)) keys
    val own = filter (fn (_, (_, _, origin)) => origin = #name c) finals
    val callable = map_filter (fn ((kind, n), (d, f, _)) => if kind = "function" then SOME (n, (d, f)) else NONE) finals
    fun fsig_of (f: func) : fsig =
      {name = #name f, external = #vis f = "public" orelse #vis f = "external" orelse #vis f = "", params = #params f, returns = #returns f,
       mut = #mut f, pos = #pos f, body = the_default [] (#body f), mods = #mods f}
    (*the classes that have this one among their bases: the functions that some of them override count as overridden*)
    val descendants = filter (fn (d: cdef) => #kind d = "contract" andalso member (op =) (c3_lin cdefs (#name d)) (#name c)) cdefs
    (*what the hierarchies that this class belongs to call by name (the calls of unrelated contracts of the text do not count)*)
    val hier_names = distinct (op =) (maps (fn (d: cdef) => c3_lin cdefs (#name d)) descendants)
    val hier_defs = filter (fn (d: cdef) => member (op =) hier_names (#name d) orelse #kind d = "library") cdefs
    val referenced =
      distinct (op =) (expand_names
        (maps (fn (d: cdef) =>
                 maps (fn (f: func) => maps idents_of_expr (exprs_of (the_default [] (#body f))) @ maps (fn (_, a, _) => maps idents_of_expr a) (#mods f)) (#funcs d)
                 @ maps (fn (m: moddef) => maps idents_of_expr (exprs_of (#body m))) (#modifiers d)
                 @ maps (fn (v: vardef) => maps idents_of_expr (the_list (#init v))) (#vars d)) hier_defs))
    val value_used =
      distinct (op =) (expand_names
        (maps (fn (d: cdef) =>
                 maps (fn (f: func) => value_calls_stmts (the_default [] (#body f)) @ maps (fn (_, a, _) => maps value_calls_expr a) (#mods f)) (#funcs d)
                 @ maps (fn (m: moddef) => value_calls_stmts (#body m)) (#modifiers d)
                 @ maps (fn (v: vardef) => maps value_calls_expr (the_list (#init v))) (#vars d)) hier_defs))
    (*super.f() and A.f(): the implementations they reach*)
    fun super_of home fname =
      let
        val j = index home
        val cands = filter (fn (d: cdef) => index (#name d) < j) all_defs |> rev
      in
        get_first (fn (d: cdef) => (case find_first (fn (f: func) => #kind f = "function" andalso #name f = fname andalso is_some (#body f)) (#funcs d) of
                                      SOME f => SOME (#name d, fsig_of f) | NONE => NONE)) cands
      end
    fun base_of a fname =
      let val alin = filter is_real (c3_lin cdefs a) in
        get_first (fn n => (case find n of
                              SOME (d: cdef) =>
                                (case find_first (fn (f: func) => #kind f = "function" andalso #name f = fname andalso is_some (#body f)) (#funcs d) of
                                   SOME f => SOME (n, fsig_of f) | NONE => NONE)
                            | NONE => NONE)) alin
      end
    (*the targets whose value is used by a super call or a call A.f()*)
    fun super_target_in (d: cdef) fname =
      let
        val order = rev (filter is_real (c3_lin cdefs (#name d)))
        val earlier = rev (take (Int.max (find_index (fn n => n = #name d) order, 0)) order)
      in
        get_first (fn n => (case find n of
                              SOME (x: cdef) => (case find_first (fn (f: func) => #kind f = "function" andalso #name f = fname andalso is_some (#body f)) (#funcs x) of
                                                   SOME _ => SOME (n, fname) | NONE => NONE)
                            | NONE => NONE)) earlier
      end
    val special_targets =
      maps (fn (d: cdef) =>
        map_filter (fn (e, disc) =>
          (case e of
             ECall (EMember (EId ("super", _), f, _), _, _) => if disc then NONE else super_target_in d f
           | ECall (EMember (EId (a, _), f, _), _, _) => if disc orelse not (is_real a) then NONE else Option.map (fn (cl, _) => (cl, f)) (base_of a f)
           | _ => NONE))
          (maps (fn (f: func) => calls_stmts (the_default [] (#body f))) (#funcs d)))
        cdefs
    val defined_in_several =
      distinct (op =)
        (maps (fn (d: cdef) =>
                 let
                   val fs = maps (fn n => (case find n of SOME (x: cdef) => filter (fn (f: func) => #kind f = "function") (#funcs x) | NONE => [])) (filter is_real (c3_lin cdefs (#name d)))
                   val names = map #name fs
                 in filter (fn n => length (filter (fn m => m = n) names) > 1) (distinct (op =) names) end) descendants)
    val omitted =
      map_filter (fn (_, (_, f, _)) =>
        if #kind f = "function" andalso (#mut f = "view" orelse #mut f = "pure") andalso not (null (#returns f))
           andalso not (member (op =) referenced (#name f)) andalso not (member (op =) defined_in_several (#name f)) then SOME (#name f) else NONE) own
    val funcs0 = filter (fn (_, (_, f, _)) => not (#kind f = "function" andalso member (op =) omitted (#name f))) own
    val alias =
      map_filter (fn (n, (_, f)) => if #vis f = "public" andalso member (op =) referenced n then SOME (n, isa_ident n ^ "__int") else NONE) callable
    val twins =
      map_filter (fn (_, (d, f, o)) =>
        if #vis f = "public" andalso #kind f = "function" andalso member (op =) referenced (#name f)
        then SOME (d, {name = #name f ^ "__int", kind = "function", params = #params f, returns = #returns f, vis = "internal", mut = "nonpayable", virt = false, over = false,
                       mods = #mods f, body = #body f, pos = #pos f, doc = #doc f}: func)
        else NONE) funcs0
    val funcs_all = map (fn (_, (d, f, _)) => (d, f)) funcs0 @ twins
    val funcs_sigs = map (fn (n, (_, f)) => (n, fsig_of f)) callable @ map (fn (_, (f: func)) => (#name f, fsig_of f)) twins
    val value_ret =
      filter (fn n => (case AList.lookup (op =) callable n of SOME (_, f) => not (null (#returns f)) | NONE => false)) value_used
    val ctor = find_first (fn (f: func) => #kind f = "constructor") (#funcs c)
    fun is_interface n = (case find n of SOME d => #kind d = "interface" | NONE => false)
    val real_class_names = map #name (filter (fn (d: cdef) => #kind d = "contract") cdefs)
    fun is_contract_name n = member (op =) (map #name cdefs) (last_component n)
    fun interface_id n =
      (case find n of
         SOME d =>
           if #kind d <> "interface" then NONE
           else SOME (fold (fn (f: func) => fn acc => xor_int (acc, selector is_contract_name (#name f) (map #ty (#params f)))) (filter (fn (f: func) => #kind f = "function") (#funcs d)) 0)
       | NONE => NONE)
    (*libraries: the internal functions that are called are copied into the contract as <Lib>__<f>*)
    val lib_names = map #name (filter (fn (d: cdef) => #kind d = "library") cdefs)
    fun lib_funcs l = (case find l of SOME d => filter (fn (f: func) => #kind f = "function") (#funcs d) | NONE => [])
    fun lib_fns l = distinct (op =) (map #name (lib_funcs l))
    val done_libs : method list Unsynchronized.ref = Unsynchronized.ref []
    val started_libs : string list Unsynchronized.ref = Unsynchronized.ref []
    val lib_fn_ref : (string -> string -> ty list -> int -> string * fsig) Unsynchronized.ref = Unsynchronized.ref (fn _ => fn _ => fn _ => fn _ => raise Fail "lib")
    val shared_uses : string list Unsynchronized.ref = Unsynchronized.ref []
    (*the copy of a library function is named after the library; the first copy of a name gets the plain name, the others a number*)
    val lib_assigned : (string * int * string) list Unsynchronized.ref = Unsynchronized.ref []
    fun lib_ename l (f: func) k =
      (case find_first (fn (l', k', _) => l' = l andalso k' = k) (!lib_assigned) of
         SOME (_, _, en) => en
       | NONE =>
           let
             val taken = filter (fn (l', _, en) => l' = l andalso String.isPrefix (l ^ "__" ^ #name f) en) (!lib_assigned)
             val en = if null taken then l ^ "__" ^ #name f else l ^ "__" ^ #name f ^ "_" ^ string_of_int (k + 1)
             val _ = lib_assigned := (l, k, en) :: !lib_assigned
           in en end)
    val lib_value_ret = []: string list
    val counter = Unsynchronized.ref 0
    val ext_sigs_ref : ext_sig list Unsynchronized.ref = Unsynchronized.ref []
    val mod_abbrevs_ref : (string * string) list Unsynchronized.ref = Unsynchronized.ref []
    fun find_callee cname f atys p =
      let
        val lin_c = filter (fn n => is_some (find n)) (c3_lin cdefs cname)
        val fs = maps (fn n => (case find n of SOME (d: cdef) => filter (fn (g: func) => #kind g = "function" andalso #name g = f) (#funcs d) | NONE => [])) lin_c
        val fs' = filter (fn (g: func) => length (#params g) = length atys) fs
      in
        (case fs' of
           [] => err p ("the contract " ^ quote cname ^ " has no function " ^ quote f ^ " with " ^ string_of_int (length atys) ^ " argument(s)")
         | [g] => g
         | _ =>
             (case find_first (fn (g: func) => forall (fn (a, (pr: param)) => is_some (fit a (#ty pr))) (atys ~~ #params g)) fs' of
                SOME g => g
              | NONE => hd fs'))
      end
    fun mk_env state consts mods funcs alias value_ret lib_ctx home ctr : env =
      {cname = #name c, state = state, consts = consts, locals = Unsynchronized.ref [], rename = [], placeholder = NONE, counter = ctr, mods = mods,
       funcs = funcs, alias = alias, value_ret = value_ret, unchecked = Unsynchronized.ref false, uses = shared_uses,
       guard = Config.get ctxt value_guard, locs = Unsynchronized.ref [], home = Unsynchronized.ref home, classes = real_class_names,
       mod_abbrevs = mod_abbrevs_ref, mod_class = (fn n => the_default "" (AList.lookup (op =) mod_home n)), mod_abbrev_on = Config.get ctxt modifier_abbreviations,
       ext_sigs = ext_sigs_ref, find_callee = find_callee, lib_ctx = lib_ctx, usings = Unsynchronized.ref (#using c), lib_fn = (fn l => fn f => fn a => fn p => !lib_fn_ref l f a p), libs = lib_names, lib_fns = lib_fns,
       interface_ids = interface_id, super_of = super_of, base_of = base_of}
    val env : env = mk_env state0 consts mods funcs_sigs alias (value_ret @ lib_value_ret) NONE (#name c) counter
    val _ = lib_fn_ref :=
      (fn l => fn f => fn atys => fn p =>
        let
          val cands = lib_funcs l
          val same = filter (fn (_, (g: func)) => #name g = f) (map_index I cands)
          val _ = if null same then err p ("the library " ^ quote l ^ " has no function " ^ quote f) else ()
          val (k, g) =
            (case same of
               [one] => one
             | _ =>
                 let val kk = resolve_overload p f (map (fn (k, (g: func)) => (string_of_int k, map #ty (#params g))) same) atys
                 in the (find_first (fn (k, _) => string_of_int k = kk) same) end)
          val en = lib_ename l g k
          val sg : fsig = {name = en, external = false, params = #params g, returns = #returns g, mut = #mut g, pos = #pos g, body = the_default [] (#body g), mods = #mods g}
          val _ =
            if member (op =) (!started_libs) en then ()
            else
              let
                val _ = started_libs := en :: !started_libs
                val _ = if #vis g <> "internal" andalso #vis g <> "private" then err (#pos g) ("library function " ^ quote (l ^ "." ^ f) ^ " that is " ^ #vis g ^ " (only internal library functions are inlined)") else ()
                val _ = if is_none (#body g) then err (#pos g) ("library function " ^ quote (l ^ "." ^ f) ^ " without body") else ()
                val _ = List.app (fn (pr: param) => (case #ty pr of TyInt _ => () | TyAddr _ => () | TyBool => () | TyBytesN _ => () | TyString => () | TyBytes => ()
                                                       | TyUser n => if is_contract_type (last_component n) then () else err (#pos g) "a library function with a storage or non-elementary parameter"
                                                       | _ => err (#pos g) "a library function with a storage or non-elementary parameter")) (#params g)
                val env_l = mk_env [] [] [] [] [] (value_ret @ lib_value_ret) (SOME l) l (Unsynchronized.ref 0)
                val copy = {name = en, kind = "function", params = #params g, returns = #returns g, vis = "internal", mut = #mut g, virt = false, over = false,
                            mods = #mods g, body = #body g, pos = #pos g, doc = ""}: func
                val vr = member (op =) value_used (#name g) andalso not (null (#returns g))
                val body = (func_body env_l (bodies_of env_l) copy vr) handle Err (ps, m) => raise Err (ps, m ^ " (in the library function " ^ l ^ "." ^ f ^ ", requested by " ^ !current_fn ^ ")")
              in
                done_libs := !done_libs @ [{name = en, external = false, payable = false,
                                            params = map (fn (pr: param) => (str_name (#name pr), stype (#pos g) (#ty pr))) (#params g), body = body}]
              end
        in (en, sg) end)
    val bodies = bodies_of env
    fun callees (f: func) =
      let
        val ids = maps idents_plain (exprs_of (the_default [] (#body f)))
          @ maps (fn (m, args, _) => maps idents_plain args @ (case AList.lookup (op =) mods m of SOME (md: moddef) => maps idents_plain (exprs_of (#body md)) | NONE => [])) (#mods f)
        (*an overloaded name stands for all its versions: a call of another version of the function itself is no recursion*)
        val names =
          maps (fn n =>
                  (case AList.lookup (op =) (!overload_table) n of
                     SOME cs => filter (fn en => en <> #name f) (map fst cs)
                   | NONE => [n])) ids
        val names = map (fn n => the_default n (AList.lookup (op =) alias n)) names
      in sort_strings (distinct (op =) (filter (fn n => exists (fn (_, (g: func)) => #name g = n) funcs_all) names)) end
    fun by_name n = the (find_first (fn (_, (g: func)) => #name g = n) funcs_all)
    fun visit (df as (_, (f: func))) (done, stack) =
      if member (op =) (map (fn (_, (g: func)) => #name g) done) (#name f) then (done, stack)
      else if member (op =) stack (#name f) then err (#pos f) ("recursive internal calls through " ^ quote (#name f) ^ " (a method must be defined before it is called)")
      else
        let val (done', _) = fold (fn n => fn st => visit (by_name n) st) (callees f) (done, #name f :: stack)
        in (done' @ [df], stack) end
    val (ordered, _) = fold visit funcs_all ([], [])
    fun method_of (d: cdef, f: func) : method =
      let
        val p = #pos f
        val ext = #vis f = "public" orelse #vis f = "external" orelse (#kind f <> "function")
        val payable = #mut f = "payable"
        val base_name = if String.isSuffix "__int" (#name f) then String.substring (#name f, 0, size (#name f) - 5) else #name f
        val vr = (member (op =) value_ret (#name f) orelse member (op =) value_ret base_name orelse member (op =) special_targets (#name d, base_name))
                 andalso not (null (#returns f))
        val _ = counter := 0
        val _ = loop_k := 0
        val _ = jump := NONE
        val _ = current_fn := #name d ^ "." ^ #name f
        val _ = (#usings env) := #using d
        val _ = (#home env) := #name d
        val _ = if #kind f = "fallback" andalso (not (null (#params f))) then err p "a fallback function with calldata is not supported" else ()
        val body0 = if is_none (#body f) then "ABSTRACT" else func_body env bodies f vr
        val body1 = if ext andalso is_some (#body f) then with_guards (param_guards p (#params f)) body0 else body0
        val body2 = if ext andalso not payable andalso #guard env andalso is_some (#body f) then (use env "guard"; guarded body1) else body1
      in
        {name = if #kind f = "function" then isa_ident (#name f) else #kind f, external = ext, payable = payable,
         params = map (fn (pr: param) => (str_name (#name pr), stype p (#ty pr))) (#params f), body = body2}
      end
    val own_methods = map method_of ordered
    (*the library functions that the inherited functions use are copied into this class too (the view of a class contains the functions of its bases)*)
    val _ =
      List.app (fn (_, (d: cdef, f: func, origin)) =>
        if origin = #name c orelse #kind f <> "function" orelse is_none (#body f)
           orelse ((#mut f = "view" orelse #mut f = "pure") andalso not (null (#returns f)) andalso not (member (op =) referenced (#name f)) andalso not (member (op =) defined_in_several (#name f)))
        then ()
        else
          (counter := 0; loop_k := 0; jump := NONE; current_fn := #name d ^ "." ^ #name f ^ " (inherited)"; (#usings env) := #using d; (#home env) := #name d;
           ignore (func_body env bodies f (member (op =) value_ret (#name f) andalso not (null (#returns f)))))) finals
    (*the functions that are omitted are not translated, but a call to another contract in one of them still makes the contract declare the epoch counter*)
    val ghost_before = !ext_call_count
    val saved_sigs = !ext_sigs_ref
    val _ =
      List.app (fn (_, (d: cdef, f: func, _)) =>
        if #kind f = "function" andalso is_some (#body f) andalso (#mut f = "view" orelse #mut f = "pure") andalso not (null (#returns f))
           andalso not (member (op =) referenced (#name f)) andalso not (member (op =) defined_in_several (#name f))
        then
          (counter := 0; loop_k := 0; jump := NONE; (#usings env) := #using d; (#home env) := #name d;
           ignore (Exn.capture (fn () => func_body env bodies f false) ()))
        else ()) finals
    val omitted_ext = !ext_call_count > ghost_before
    val _ = ext_sigs_ref := saved_sigs
    val methods = !done_libs @ own_methods
    (*the constructor: its modifier list holds modifiers and arguments for base constructors*)
    val ctor_inv = (case ctor of SOME f => #mods f | NONE => [])
    val real_inv = filter (fn (m, _, _) => not (is_real m) andalso not (is_interface m)) ctor_inv
    val base_inv = filter (fn (m, _, _) => is_real m) ctor_inv
    (*the position of this class in the linearisation of the last contract of the text that is built on it (as in the hierarchy of the transpiler)*)
    val k_index =
      let
        val leaves = filter (fn (d: cdef) => not (is_base_of_other_in cdefs (#name d))) descendants
        val leaf = (case leaves of [] => #name c | _ => #name (List.last leaves))
        val order = rev (filter is_real (c3_lin cdefs leaf))
      in (case find_index (fn n => n = #name c) order of ~1 => length ancestors | i => i) end
    val ctor_params0 = (case ctor of SOME f => #params f | NONE => [])
    fun ctor_renaming (f: func) k =
      map (fn (pr: param) => (#name pr, "_i" ^ string_of_int k ^ "_" ^ #name pr)) (#params f)
      @ map (fn n => (n, "_i" ^ string_of_int k ^ "_" ^ n)) (distinct (op =) (declared_names (the_default [] (#body f))))
      |> (fn l => fold (fn (a, b) => fn acc => if AList.defined (op =) acc a then acc else acc @ [(a, b)]) l [])
    val ctor_ren = if is_base_of_other andalso is_some ctor then ctor_renaming (the ctor) k_index else []
    val env_c = with_rename env ctor_ren NONE
    fun cname n = the_default n (AList.lookup (op =) ctor_ren n)
    val _ = (#locals env) := map (fn (pr: param) => (cname (#name pr), #ty pr)) ctor_params0
    (*the direct bases in the order of the list, each with its arguments; a base that only gets arguments in the modifier list of the constructor is listed too*)
    val direct = filter (fn (b, _) => is_real b) (#parents c)
    val order0 = map fst direct
    val specs0 = map (fn (b, args) => (b, args)) direct
    val (order, specs) =
      fold (fn (m, args, p) => fn (order, specs) =>
        if member (op =) order m then
          (case AList.lookup (op =) specs m of
             SOME (_ :: _) => if null args then (order, specs) else err p "base constructor arguments given twice"
           | _ => (order, AList.update (op =) (m, args) specs))
        else
          let
            val lin_z = filter is_real (c3_lin cdefs m)
            val inheriting = map_index (fn (k, b) => (k, member (op =) (filter is_real (c3_lin cdefs b)) m)) order |> filter snd |> map fst
            val ancestors_of_z = map_index (fn (k, b) => (k, member (op =) lin_z b)) order |> filter snd |> map fst
            val _ = if null inheriting orelse (not (null ancestors_of_z) andalso List.last (sort int_ord ancestors_of_z) >= hd (sort int_ord inheriting))
                    then err p "a base constructor called in a modifier list for a contract that is not a base, or whose position cannot be listed" else ()
            val at = hd (sort int_ord inheriting)
          in (take at order @ [m] @ drop at order, AList.update (op =) (m, args) specs @ [] ) end) base_inv (order0, specs0)
    val parents =
      map (fn b =>
        let
          val args = the_default [] (AList.lookup (op =) specs b)
          val bparams = (case find b of SOME d => (case find_first (fn (f: func) => #kind f = "constructor") (#funcs d) of SOME f => #params f | NONE => []) | NONE => [])
          val _ = if not (null args) andalso length args <> length bparams then err (#pos c) ("a base constructor call of " ^ quote b ^ " with the wrong number of arguments") else ()
        in (b, map (fn a => fst (ex env_c a)) args) end) order
    val init_parts =
      map_filter (fn (v: vardef) =>
        (case #init v of
           NONE => NONE
         | SOME e =>
             (check_order env bodies e;
              SOME ("assign_storage_monad (" ^ str_name (#name v) ^ ") [] " ^ fst (ex_as env e (#ty v)))))) own_vars
    val ctor_offset_of =
      (fn (d: cdef) =>
         let val anc = filter (fn n => n <> #name d) (rev (filter is_real (c3_lin cdefs (#name d)))) in
           fold (fn n => fn acc => acc + (case find n of SOME x => (case find_first (fn (f: func) => #kind f = "constructor") (#funcs x) of
                                                                      SOME f => length (filter (fn (m, _, _) => not (is_real m) andalso not (is_interface m)) (#mods f)) | NONE => 0)
                                                    | NONE => 0)) anc 0
         end)
    fun ctor_text_of (d: cdef) (f: func) env' =
      let
        val _ = counter := ctor_offset_of d
        val _ = loop_k := 0
        val _ = jump := NONE
        val stmts0 = the_default [] (#body f)
        val _ = List.app (check_order env' bodies) (exprs_of stmts0)
        val text = with_modifiers env' (filter (fn (m, _, _) => not (is_real m) andalso not (is_interface m)) (#mods f)) (block env' stmts0)
      in if text = "skip_monad" then [] else [text] end
    val _ = (#home env) := #name c
    val ctor_body = (case ctor of NONE => [] | SOME f => ctor_text_of c f env_c)
    val flat = null (filter is_real (map fst (#parents c))) andalso null order andalso not is_base_of_other
    val ctor_parts = if flat then init_parts @ ctor_body else ctor_body
    val cbody0 = (case ctor_parts of [] => "skip_monad" | [p] => if String.isPrefix "(" p then p else "(" ^ p ^ ")" | ps => do_block ps)
    val cpay = (case ctor of SOME f => #mut f = "payable" | NONE => false)
    val cbody1 = (case ctor of SOME f => if is_base_of_other then cbody0 else with_guards (param_guards (#pos f) ctor_params0) cbody0 | NONE => cbody0)
    val cbody2 = if not cpay andalso not is_base_of_other andalso #guard env then (use env "guard"; guarded cbody1) else cbody1
    val init_text = if flat then "skip_monad" else (case init_parts of [] => "skip_monad" | [p] => p | ps => do_block ps)
    (*a constructor of a base that uses a modifier this class overrides runs with the new modifier: this class gives its body*)
    val repl =
      map_filter (fn (x: cdef) =>
        (case find_first (fn (f: func) => #kind f = "constructor") (#funcs x) of
           NONE => NONE
         | SOME xf =>
             if exists (fn (m, _, _) => (case AList.lookup (op =) mod_home m of SOME hc => hc = #name c andalso index hc > index (#name x) | NONE => false)) (#mods xf)
             then
               let
                 val xren = ctor_renaming xf (index (#name x))
                 val env_x = with_rename env xren NONE
                 val _ = (#locals env_x) := map (fn (pr: param) => (the_default (#name pr) (AList.lookup (op =) xren (#name pr)), #ty pr)) (#params xf)
                 val parts = ctor_text_of x xf env_x
                 val txt = (case parts of [] => "skip_monad" | [p] => p | ps => do_block ps)
               in SOME (#name x, if length parts = 1 andalso not (String.isPrefix "(" txt) then "(" ^ txt ^ ")" else txt) end
             else NONE)) anc_defs
    val variables =
      (case own_vars of
         [] => if null order andalso null (filter is_real (map fst (#parents c))) then [("STR ''_no_state''", "SType.TValue TBool")] else []
       | _ => map (fn (v: vardef) => (str_name (#name v), stype (#pos v) (#ty v))) own_vars)
    val _ = check_uses ctxt (!shared_uses)
  in
    ({name = #name c, parents = parents, variables = variables, payable = cpay,
      params = map (fn (pr: param) => (str_name (cname (#name pr)), stype (#pos c) (#ty pr))) ctor_params0,
      init = init_text, repl = repl, body = cbody2, methods = methods, pre = "", assuming = NONE}: contract, !ext_sigs_ref, !mod_abbrevs_ref, omitted_ext)
  end

(*The locale `<name>_Callee` with the assumptions on the callees (a predicate `<name>_callee_assm` of `ext_isc` and `ext_result`), a witness that shows that they can
  all hold at once, and the two satisfiability lemmas; the contract imports it (`contract C assuming <name>_Callee`), so every theorem about the contract carries them.*)
fun callee_block name (sigs: ext_sig list) : (string * string) option =
  let
    val sigs = filter (fn (s: ext_sig) => not (null (#assume s))) sigs
  in
    if null sigs then NONE
    else
      let
        val pred = name ^ "_callee_assm" and loc = name ^ "_Callee" and wit = name ^ "_callee_wit"
        val res_t = "256 word \<Rightarrow> ('a, 'a valtype) storage \<Rightarrow> 'a balances \<Rightarrow> 'a \<Rightarrow> string \<Rightarrow> 'a valtype list \<Rightarrow> 'a valtype option"
        val al = "\<forall>ep st bal a vs. isc a \<longrightarrow> "
        fun replace_first s a b =
          let val (pre, rest) = Substring.position a (Substring.full s)
          in if Substring.isEmpty rest then s else Substring.string pre ^ b ^ Substring.string (Substring.triml (size a) rest) end
        fun clause_parts (s: ext_sig) =
          let
            val sg = #sg s
            val rt = the (#ret s)
            val call = "r ep st bal a ''" ^ sg ^ "'' vs"
            val call_e = replace_first call "r " "ext_result "
            val w = (case ext_ty_of rt of TyInt (false, w) => SOME w | _ => NONE)
            val (shape, var) = if rt = "bool" then ("Bool b", "b") else if rt = "address" then ("Address x", "x") else ("Uint w", "w")
            val fn_ = hd (String.fields (fn c => c = #"(") sg)
          in
            map (fn c =>
              let
                val k = hd c
                val fact = "callee_" ^ fn_ ^ "_" ^ k ^ (if k = "norevert" orelse k = "constant" then "" else "_" ^ nth c 1)
              in
                if k = "norevert" then
                  let val rng = (case w of SOME w => if w < 256 then " \<and> unat w < " ^ IntInf.toString (two_pow w) else "" | NONE => "")
                  in ("(" ^ al ^ "(\<exists>" ^ var ^ ". " ^ call ^ " = Some (" ^ shape ^ ")" ^ rng ^ "))",
                      (fact, "ext_isc a \<Longrightarrow> \<exists>" ^ var ^ ". " ^ call_e ^ " = Some (" ^ shape ^ ")" ^ rng)) end
                else if k = "constant" then
                  ("(\<forall>ep ep' st st' bal bal' a vs. isc a \<longrightarrow> r ep st bal a ''" ^ sg ^ "'' vs = r ep' st' bal' a ''" ^ sg ^ "'' vs)",
                   (fact, "ext_isc a \<Longrightarrow> ext_result ep st bal a ''" ^ sg ^ "'' vs = ext_result ep' st' bal' a ''" ^ sg ^ "'' vs"))
                else
                  let val rel = if k = "min" then nth c 1 ^ " \<le> unat w" else "unat w \<le> " ^ nth c 1
                  in ("(" ^ replace_first al "vs." "vs w." ^ call ^ " = Some (Uint w) \<longrightarrow> " ^ rel ^ ")",
                      (fact, call_e ^ " = Some (Uint w) \<Longrightarrow> ext_isc a \<Longrightarrow> " ^ rel)) end
              end) (#assume s)
          end
        val all = maps clause_parts sigs
        val parts = map fst all
        val facts = map snd all
        fun witval (s: ext_sig) =
          let val rt = the (#ret s) in
            if rt = "bool" then "Some (Bool False)" else if rt = "address" then "Some (Address null)"
            else "Some (Uint " ^ IntInf.toString (fst (assume_bounds (#assume s) (ext_ty_of rt))) ^ ")"
          end
        val body = fold (fn s => fn acc => "(if f = ''" ^ #sg s ^ "'' then " ^ witval s ^ " else " ^ acc ^ ")") (rev sigs) "None"
        val summary = space_implode "; " (map (fn (s: ext_sig) => #sg s ^ ": " ^ space_implode ", " (map (space_implode " ") (#assume s))) sigs)
        val res_t_wit = replace_first res_t "('a," "('a::address,"
        val lines =
          ["definition " ^ pred ^ " :: \"('a::address \<Rightarrow> bool) \<Rightarrow> (" ^ res_t ^ ") \<Rightarrow> bool\" where",
           "  \"" ^ pred ^ " isc r \<equiv>",
           "    " ^ space_implode "\n    \<and> " parts ^ "\"",
           "",
           "definition " ^ wit ^ " :: \"" ^ res_t_wit ^ "\" where",
           "  \"" ^ wit ^ " ep st bal a f vs = " ^ body ^ "\"",
           "",
           "locale " ^ loc ^ " = Keccak256 +",
           "  assumes callee_assumptions: \"" ^ pred ^ " ext_isc ext_result\"",
           ""]
          @ maps (fn (f, tt) => ["lemma (in " ^ loc ^ ") " ^ f ^ ": \"" ^ tt ^ "\"", "  using callee_assumptions unfolding " ^ pred ^ "_def by fastforce", ""]) facts
          @ ["lemma " ^ pred ^ "_sat: \"" ^ pred ^ " (\<lambda>_. True) " ^ wit ^ "\"", "  unfolding " ^ pred ^ "_def " ^ wit ^ "_def by auto", "",
             "lemma " ^ loc ^ "_sat: \"" ^ loc ^ " id (\<lambda>_. True) " ^ wit ^ "\"",
             "  unfolding " ^ loc ^ "_def " ^ loc ^ "_axioms_def Keccak256_def using " ^ pred ^ "_sat by simp", ""]
      in SOME (cat_lines lines, loc) end
  end

fun read_unlocked ctxt text =
  let
    val cdefs0 = parse (lex text)
    val _ = struct_table := !file_structs @ maps #structs cdefs0
    val cdefs = rename_overloads cdefs0
    val _ = known_classes := map #name cdefs
    val _ = contract_kinds := map (fn (d: cdef) => (#name d, #kind d)) cdefs
    fun is_base_of_other (c: cdef) = exists (fn (d: cdef) => member (op =) (tl (c3_lin cdefs (#name d))) (#name c)) cdefs
    val real = filter (fn (d: cdef) => #kind d = "contract" andalso (not (#abstract d) orelse is_base_of_other d)) cdefs
    val elaborated = map (fn c => (c, elab_class ctxt cdefs c (is_base_of_other c))) real
    val names = map (fn (c: cdef, _) => #name c) elaborated
    (*the classes that are related by inheritance form a hierarchy: it shares the ghost variable of the calls to other contracts and the locale of the assumptions*)
    fun related a b = member (op =) (c3_lin cdefs a) b orelse member (op =) (c3_lin cdefs b) a
    val comps =
      fold (fn n => fn comps =>
        let val (hit, rest) = List.partition (fn comp => exists (related n) comp) comps
        in rest @ [n :: flat hit] end) names []
    fun comp_of n = the (find_first (fn comp => member (op =) comp n) comps)
    val declared = Unsynchronized.ref ([]: string list)       (*the hierarchies whose ghost variable is declared*)
    val callee_done = Unsynchronized.ref ([]: string list)
    val emitted_abbrs = Unsynchronized.ref ([]: string list)
    fun finish ((d: cdef, (k: contract, sigs: ext_sig list, abbrs: (string * string) list, omitted_ext: bool))) : contract =
      let
        (*the abbreviations of modifiers that no earlier class has defined*)
        val new_abbrs = filter (fn (n, _) => not (member (op =) (!emitted_abbrs) n)) abbrs
        val _ = emitted_abbrs := !emitted_abbrs @ map fst new_abbrs
        val k = {name = #name k, parents = #parents k, variables = #variables k, payable = #payable k, params = #params k, init = #init k, repl = #repl k,
                 body = #body k, methods = #methods k, pre = cat_lines (map snd new_abbrs), assuming = #assuming k}: contract
        val comp = comp_of (#name d)
        val key = hd (sort_strings comp)
        val k =
          if (null sigs andalso not omitted_ext) orelse member (op =) (!declared) key then k
          else
            (declared := key :: !declared;
             {name = #name k, parents = #parents k,
              variables = (case #variables k of [("STR ''_no_state''", _)] => [] | vs => vs) @ [(str_name "ghost_ext_epoch", "SType.TValue TSint")],
              payable = #payable k, params = #params k, init = #init k, repl = #repl k, body = #body k, methods = #methods k, pre = #pre k, assuming = #assuming k})
        val comp_sigs =
      fold (fn (s: ext_sig) => fn acc => if exists (fn (x: ext_sig) => #sg x = #sg s) acc then acc else acc @ [s])
        (maps (fn (d': cdef, (_, ss, _, _)) => if member (op =) comp (#name d') then ss else []) elaborated) []
        val leaf = List.last (filter (fn n => member (op =) comp n) names)
      in
        (case callee_block leaf comp_sigs of
           NONE => k
         | SOME (text, loc) =>
             let val first = not (member (op =) (!callee_done) key)
                 val _ = if first then callee_done := key :: !callee_done else ()
             in
               {name = #name k, parents = #parents k, variables = #variables k, payable = #payable k, params = #params k, init = #init k, repl = #repl k,
                body = #body k, methods = #methods k, pre = #pre k ^ (if first then "\n" ^ text else ""), assuming = SOME loc}
             end)
      end
  in map finish elaborated end
  handle Err (pos, msg) => error ("Solidity source, " ^ position_of text pos ^ ": " ^ msg)


(*the elaboration keeps its tables in global references (struct_table, known_classes, ...): theories are processed in parallel, so one text at a time*)
val read_lock = Thread.Mutex.mutex ()
fun read ctxt text = Multithreading.synchronized "Solidity_Source.read" read_lock (fn () => read_unlocked ctxt text)

end
