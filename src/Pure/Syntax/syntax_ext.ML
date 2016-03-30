(*  Title:      Pure/Syntax/syntax_ext.ML
    Author:     Markus Wenzel and Carsten Clasohm, TU Muenchen

Syntax extension.
*)

signature SYNTAX_EXT =
sig
  val dddot_indexname: indexname
  datatype mfix = Mfix of Symbol_Pos.T list * typ * string * int list * int * Position.T
  val typ_to_nonterm: typ -> string
  datatype xsymb =
    Delim of string |
    Argument of string * int |
    Space of string |
    Bg of int | Brk of int | En
  datatype xprod = XProd of string * xsymb list * string * int
  val chain_pri: int
  val delims_of: xprod list -> string list list
  datatype syn_ext =
    Syn_Ext of {
      xprods: xprod list,
      consts: (string * string) list,
      parse_ast_translation: (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list,
      parse_rules: (Ast.ast * Ast.ast) list,
      parse_translation: (string * ((Proof.context -> term list -> term) * stamp)) list,
      print_translation: (string * ((Proof.context -> typ -> term list -> term) * stamp)) list,
      print_rules: (Ast.ast * Ast.ast) list,
      print_ast_translation: (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list}
  val mfix_args: Symbol_Pos.T list -> int
  val mixfix_args: Input.source -> int
  val escape: string -> string
  val syn_ext': string list -> mfix list ->
    (string * string) list -> (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list *
    (string * ((Proof.context -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> typ -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list ->
    (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext: mfix list -> (string * string) list ->
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list *
    (string * ((Proof.context -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> typ -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list ->
    (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext_rules: (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext_trfuns:
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list *
    (string * ((Proof.context -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> typ -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list -> syn_ext
  val stamp_trfun: stamp -> string * 'a -> string * ('a * stamp)
  val mk_trfun: string * 'a -> string * ('a * stamp)
  val eq_trfun: ('a * stamp) * ('a * stamp) -> bool
end;

structure Syntax_Ext: SYNTAX_EXT =
struct


(** misc definitions **)

val dddot_indexname = ("dddot", 0);


(** datatype xprod **)

(*Delim s: delimiter s
  Argument (s, p): nonterminal s requiring priority >= p, or valued token
  Space s: some white space for printing
  Bg, Brk, En: blocks and breaks for pretty printing*)

datatype xsymb =
  Delim of string |
  Argument of string * int |
  Space of string |
  Bg of int | Brk of int | En;

fun is_delim (Delim _) = true
  | is_delim _ = false;

fun is_terminal (Delim _) = true
  | is_terminal (Argument (s, _)) = Lexicon.is_terminal s
  | is_terminal _ = false;

fun is_argument (Argument _) = true
  | is_argument _ = false;

fun is_index (Argument ("index", _)) = true
  | is_index _ = false;

val index = Argument ("index", 1000);


(*XProd (lhs, syms, c, p):
    lhs: name of nonterminal on the lhs of the production
    syms: list of symbols on the rhs of the production
    c: head of parse tree
    p: priority of this production*)

datatype xprod = XProd of string * xsymb list * string * int;

val chain_pri = ~1;   (*dummy for chain productions*)

fun delims_of xprods =
  fold (fn XProd (_, xsymbs, _, _) =>
    fold (fn Delim s => insert (op =) s | _ => I) xsymbs) xprods []
  |> map Symbol.explode;



(** datatype mfix **)

(*Mfix (sy, ty, c, ps, p, pos):
    sy: rhs of production as symbolic text
    ty: type description of production
    c: head of parse tree
    ps: priorities of arguments in sy
    p: priority of production
    pos: source position*)

datatype mfix = Mfix of Symbol_Pos.T list * typ * string * int list * int * Position.T;


(* typ_to_nonterm *)

fun typ_to_nt _ (Type (c, _)) = c
  | typ_to_nt default _ = default;

(*get nonterminal for rhs*)
val typ_to_nonterm = typ_to_nt "any";

(*get nonterminal for lhs*)
val typ_to_nonterm1 = typ_to_nt "logic";


(* read mixfix annotations *)

local

open Basic_Symbol_Pos;

fun scan_one pred = Scan.one (pred o Symbol_Pos.symbol);
fun scan_many pred = Scan.many (pred o Symbol_Pos.symbol);
fun scan_many1 pred = Scan.many1 (pred o Symbol_Pos.symbol);

val is_meta = member (op =) ["(", ")", "/", "_", "\<index>"];

val scan_delim_char =
  $$ "'" |-- scan_one ((not o Symbol.is_blank) andf Symbol.not_eof) ||
  scan_one ((not o is_meta) andf (not o Symbol.is_blank) andf Symbol.not_eof);

fun read_int ["0", "0"] = ~1
  | read_int cs = #1 (Library.read_int cs);

val scan_sym =
  $$ "_" >> K (Argument ("", 0)) ||
  $$ "\<index>" >> K index ||
  $$ "(" |-- scan_many Symbol.is_digit >> (Bg o read_int o map Symbol_Pos.symbol) ||
  $$ ")" >> K En ||
  $$ "/" -- $$ "/" >> K (Brk ~1) ||
  $$ "/" |-- scan_many Symbol.is_blank >> (Brk o length) ||
  scan_many1 Symbol.is_blank >> (Space o Symbol_Pos.content) ||
  Scan.repeat1 scan_delim_char >> (Delim o Symbol_Pos.content);

val scan_symb =
  Symbol_Pos.scan_pos -- scan_sym >> (SOME o swap) ||
  $$ "'" -- scan_one Symbol.is_blank >> K NONE;

val scan_symbs = Scan.repeat scan_symb --| Scan.ahead (~$$ "'");

in

val read_mfix = map_filter I o the o Scan.read Symbol_Pos.stopper scan_symbs;

val mfix_args = length o filter (is_argument o #1) o read_mfix;
val mixfix_args = mfix_args o Input.source_explode;

val escape = implode o map (fn s => if is_meta s then "'" ^ s else s) o Symbol.explode;

end;


(* mfix_to_xprod *)

fun mfix_to_xprod logical_types (Mfix (sy, typ, const, pris, pri, pos)) =
  let
    fun err_in_mixfix msg = error (msg ^ " in mixfix annotation" ^ Position.here pos);

    fun check_blocks [] pending bad = pending @ bad
      | check_blocks ((Bg _, pos) :: rest) pending bad = check_blocks rest (pos :: pending) bad
      | check_blocks ((En, pos) :: rest) [] bad = check_blocks rest [] (pos :: bad)
      | check_blocks ((En, _) :: rest) (_ :: pending) bad = check_blocks rest pending bad
      | check_blocks (_ :: rest) pending bad = check_blocks rest pending bad;

    fun add_args [] ty [] = ([], typ_to_nonterm1 ty)
      | add_args [] _ _ = err_in_mixfix "Too many precedences"
      | add_args ((sym as (Argument ("index", _), _)) :: syms) ty ps =
          add_args syms ty ps |>> cons sym
      | add_args ((Argument _, pos) :: syms) (Type ("fun", [ty, tys])) [] =
          add_args syms tys [] |>> cons (Argument (typ_to_nonterm ty, 0), pos)
      | add_args ((Argument _, pos) :: syms) (Type ("fun", [ty, tys])) (p :: ps) =
          add_args syms tys ps |>> cons (Argument (typ_to_nonterm ty, p), pos)
      | add_args ((Argument _, _) :: _) _ _ =
          err_in_mixfix "More arguments than in corresponding type"
      | add_args (sym :: syms) ty ps = add_args syms ty ps |>> cons sym;

    fun logical_args (a as (Argument (s, p))) =
          if s <> "prop" andalso member (op =) logical_types s then Argument ("logic", p) else a
      | logical_args a = a;

    fun rem_pri (Argument (s, _)) = Argument (s, chain_pri)
      | rem_pri sym = sym;


    val raw_symbs = read_mfix sy;

    val indexes = filter (is_index o #1) raw_symbs;
    val _ =
      if length indexes <= 1 then ()
      else error ("More than one index argument" ^ Position.here_list (map #2 indexes));

    val args = map_filter (fn (arg as Argument _, _) => SOME arg | _ => NONE) raw_symbs;
    val (const', typ', syntax_consts, parse_rules) =
      if not (exists is_index args) then (const, typ, NONE, NONE)
      else
        let
          val indexed_const =
            if const <> "" then const ^ "_indexed"
            else err_in_mixfix "Missing constant name for indexed syntax";
          val rangeT = Term.range_type typ handle Match =>
            err_in_mixfix "Missing structure argument for indexed syntax";

          val xs = map Ast.Variable (Name.invent Name.context "xa" (length args - 1));
          val (xs1, xs2) = chop (find_index is_index args) xs;
          val i = Ast.Variable "i";
          val lhs =
            Ast.mk_appl (Ast.Constant indexed_const)
              (xs1 @ [Ast.mk_appl (Ast.Constant "_index") [i]] @ xs2);
          val rhs = Ast.mk_appl (Ast.Constant const) (i :: xs);
        in (indexed_const, rangeT, SOME (indexed_const, const), SOME (lhs, rhs)) end;

    val (symbs, lhs) = add_args raw_symbs typ' pris;

    val copy_prod =
      (lhs = "prop" orelse lhs = "logic")
        andalso const <> ""
        andalso not (null symbs)
        andalso not (exists (is_delim o #1) symbs);
    val lhs' =
      if copy_prod orelse lhs = "prop" andalso map #1 symbs = [Argument ("prop'", 0)] then lhs
      else if lhs = "prop" then "prop'"
      else if member (op =) logical_types lhs then "logic"
      else lhs;
    val symbs' = map (apfst logical_args) symbs;

    val _ =
      (pri :: pris) |> List.app (fn p =>
        if p >= 0 andalso p <= 1000 then ()
        else err_in_mixfix ("Precedence " ^ string_of_int p ^ " out of range"));
    val _ =
      (case check_blocks symbs' [] [] of
        [] => ()
      | bad => error ("Unbalanced block parentheses" ^ Position.here_list bad));

    val xprod = XProd (lhs', map #1 symbs', const', pri);
    val xprod' =
      if Lexicon.is_terminal lhs' then
        err_in_mixfix ("Illegal use of terminal " ^ quote lhs' ^ " as nonterminal")
      else if const <> "" then xprod
      else if length (filter (is_argument o #1) symbs') <> 1 then
        err_in_mixfix "Copy production must have exactly one argument"
      else if exists (is_terminal o #1) symbs' then xprod
      else XProd (lhs', map (rem_pri o #1) symbs', "", chain_pri);

  in (xprod', syntax_consts, parse_rules) end;



(** datatype syn_ext **)

datatype syn_ext =
  Syn_Ext of {
    xprods: xprod list,
    consts: (string * string) list,
    parse_ast_translation: (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list,
    parse_rules: (Ast.ast * Ast.ast) list,
    parse_translation: (string * ((Proof.context -> term list -> term) * stamp)) list,
    print_translation: (string * ((Proof.context -> typ -> term list -> term) * stamp)) list,
    print_rules: (Ast.ast * Ast.ast) list,
    print_ast_translation: (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list};


(* syn_ext *)

fun syn_ext' logical_types mfixes consts trfuns (parse_rules, print_rules) =
  let
    val (parse_ast_translation, parse_translation, print_translation,
      print_ast_translation) = trfuns;

    val xprod_results = map (mfix_to_xprod logical_types) mfixes;
    val xprods = map #1 xprod_results;
    val consts' = map_filter #2 xprod_results;
    val parse_rules' = rev (map_filter #3 xprod_results);
    val mfix_consts = map (fn Mfix x => (#3 x, "")) mfixes @ map (fn XProd x => (#3 x, "")) xprods;
  in
    Syn_Ext {
      xprods = xprods,
      consts = mfix_consts @ consts' @ consts,
      parse_ast_translation = parse_ast_translation,
      parse_rules = parse_rules' @ parse_rules,
      parse_translation = parse_translation,
      print_translation = print_translation,
      print_rules = map swap parse_rules' @ print_rules,
      print_ast_translation = print_ast_translation}
  end;


val syn_ext = syn_ext' [];

fun syn_ext_rules rules = syn_ext [] [] ([], [], [], []) rules;
fun syn_ext_trfuns trfuns = syn_ext [] [] trfuns ([], []);

fun stamp_trfun s (c, f) = (c, (f, s));
fun mk_trfun tr = stamp_trfun (stamp ()) tr;
fun eq_trfun ((_, s1: stamp), (_, s2)) = s1 = s2;

end;
