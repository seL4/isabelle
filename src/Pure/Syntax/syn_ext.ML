(*  Title:      Pure/Syntax/syn_ext.ML
    ID:         $Id$
    Author:     Markus Wenzel and Carsten Clasohm, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Syntax extension (internal interface).
*)

signature SYN_EXT0 =
sig
  val dddot_indexname: indexname
  val constrainC: string
  val typeT: typ
  val max_pri: int
end;

signature SYN_EXT =
sig
  include SYN_EXT0
  val logic: string
  val args: string
  val cargs: string
  val any: string
  val sprop: string
  val typ_to_nonterm: typ -> string
  datatype xsymb =
    Delim of string |
    Argument of string * int |
    Space of string |
    Bg of int | Brk of int | En
  datatype xprod = XProd of string * xsymb list * string * int
  val chain_pri: int
  val delims_of: xprod list -> string list list
  datatype mfix = Mfix of string * typ * string * int list * int
  datatype syn_ext =
    SynExt of {
      xprods: xprod list,
      consts: string list,
      prmodes: string list,
      parse_ast_translation: (string * (Ast.ast list -> Ast.ast)) list,
      parse_rules: (Ast.ast * Ast.ast) list,
      parse_translation: (string * (term list -> term)) list,
      print_translation: (string * (bool -> typ -> term list -> term)) list,
      print_rules: (Ast.ast * Ast.ast) list,
      print_ast_translation: (string * (Ast.ast list -> Ast.ast)) list,
      token_translation: (string * string * (string -> string * real)) list}
  val mfix_args: string -> int
  val escape_mfix: string -> string
  val syn_ext': bool -> (string -> bool) -> mfix list ->
    string list -> (string * (Ast.ast list -> Ast.ast)) list *
    (string * (term list -> term)) list *
    (string * (bool -> typ -> term list -> term)) list * (string * (Ast.ast list -> Ast.ast)) list
    -> (string * string * (string -> string * real)) list
    -> (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext: mfix list -> string list ->
    (string * (Ast.ast list -> Ast.ast)) list * (string * (term list -> term)) list *
    (string * (bool -> typ -> term list -> term)) list * (string * (Ast.ast list -> Ast.ast)) list
    -> (string * string * (string -> string * real)) list
    -> (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext_const_names: string list -> syn_ext
  val syn_ext_rules: (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext_trfuns:
    (string * (Ast.ast list -> Ast.ast)) list *
    (string * (term list -> term)) list *
    (string * (bool -> typ -> term list -> term)) list *
    (string * (Ast.ast list -> Ast.ast)) list -> syn_ext
  val syn_ext_tokentrfuns: (string * string * (string -> string * real)) list -> syn_ext
  val pure_ext: syn_ext
end;

structure SynExt : SYN_EXT =
struct


(** misc definitions **)

val dddot_indexname = ("dddot", 0);
val constrainC = "_constrain";


(* syntactic categories *)

val logic = "logic";
val logicT = Type (logic, []);

val args = "args";
val cargs = "cargs";

val typeT = Type ("type", []);

val sprop = "#prop";
val spropT = Type (sprop, []);

val any = "any";
val anyT = Type (any, []);



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

val max_pri = 1000;   (*maximum legal priority*)
val chain_pri = ~1;   (*dummy for chain productions*)


(* delims_of *)

fun delims_of xprods =
  let
    fun del_of (Delim s) = Some s
      | del_of _ = None;

    fun dels_of (XProd (_, xsymbs, _, _)) =
      mapfilter del_of xsymbs;
  in
    map Symbol.explode (distinct (flat (map dels_of xprods)))
  end;



(** datatype mfix **)

(*Mfix (sy, ty, c, ps, p):
    sy: rhs of production as symbolic string
    ty: type description of production
    c: head of parse tree
    ps: priorities of arguments in sy
    p: priority of production*)

datatype mfix = Mfix of string * typ * string * int list * int;

fun err_in_mfix msg (Mfix (sy, _, const, _, _)) =
  error ((if msg = "" then "" else msg ^ "\n") ^
    "in mixfix annotation " ^ quote sy ^ " for " ^ quote const);


(* typ_to_nonterm *)

fun typ_to_nt _ (Type (c, _)) = c
  | typ_to_nt default _ = default;

(*get nonterminal for rhs*)
val typ_to_nonterm = typ_to_nt any;

(*get nonterminal for lhs*)
val typ_to_nonterm1 = typ_to_nt logic;


(* read_mixfix *)

local
  fun is_meta c = c mem ["(", ")", "/", "_", "\\<index>"];

  val scan_delim_char =
    $$ "'" |-- Scan.one ((not o Symbol.is_blank) andf Symbol.not_eof) ||
    Scan.one ((not o is_meta) andf (not o Symbol.is_blank) andf Symbol.not_eof);

  fun read_int ["0", "0"] = ~1
    | read_int cs = #1 (Library.read_int cs);

  val scan_sym =
    $$ "_" >> K (Argument ("", 0)) ||
    $$ "\\<index>" >> K index ||
    $$ "(" |-- Scan.any Symbol.is_digit >> (Bg o read_int) ||
    $$ ")" >> K En ||
    $$ "/" -- $$ "/" >> K (Brk ~1) ||
    $$ "/" |-- Scan.any Symbol.is_blank >> (Brk o length) ||
    Scan.any1 Symbol.is_blank >> (Space o implode) ||
    Scan.repeat1 scan_delim_char >> (Delim o implode);

  val scan_symb =
    scan_sym >> Some ||
    $$ "'" -- Scan.one Symbol.is_blank >> K None;

  val scan_symbs = Scan.repeat scan_symb --| Scan.ahead (Scan.one (not_equal "'"));
  val read_symbs = mapfilter I o the o Scan.read Symbol.stopper scan_symbs;

  fun unique_index xsymbs =
    if length (filter is_index xsymbs) <= 1 then xsymbs
    else error "Duplicate index arguments (\\<index>)";
in
  val read_mixfix = unique_index o read_symbs o Symbol.explode;
  val mfix_args = length o filter is_argument o read_mixfix;
  val escape_mfix = implode o map (fn s => if is_meta s then "'" ^ s else s) o Symbol.explode;
end;


(* mfix_to_xprod *)

fun mfix_to_xprod convert is_logtype (mfix as Mfix (sy, typ, const, pris, pri)) =
  let
    fun check_pri p =
      if p >= 0 andalso p <= max_pri then ()
      else err_in_mfix ("Precedence out of range: " ^ string_of_int p) mfix;

    fun blocks_ok [] 0 = true
      | blocks_ok [] _ = false
      | blocks_ok (Bg _ :: syms) n = blocks_ok syms (n + 1)
      | blocks_ok (En :: _) 0 = false
      | blocks_ok (En :: syms) n = blocks_ok syms (n - 1)
      | blocks_ok (_ :: syms) n = blocks_ok syms n;

    fun check_blocks syms =
      if blocks_ok syms 0 then ()
      else err_in_mfix "Unbalanced block parentheses" mfix;


    val cons_fst = apfst o cons;

    fun add_args [] ty [] = ([], typ_to_nonterm1 ty)
      | add_args [] _ _ = err_in_mfix "Too many precedences" mfix
      | add_args ((arg as Argument ("index", _)) :: syms) ty ps =
          cons_fst arg (add_args syms ty ps)
      | add_args (Argument _ :: syms) (Type ("fun", [ty, tys])) [] =
          cons_fst (Argument (typ_to_nonterm ty, 0)) (add_args syms tys [])
      | add_args (Argument _ :: syms) (Type ("fun", [ty, tys])) (p :: ps) =
          cons_fst (Argument (typ_to_nonterm ty, p)) (add_args syms tys ps)
      | add_args (Argument _ :: _) _ _ =
          err_in_mfix "More arguments than in corresponding type" mfix
      | add_args (sym :: syms) ty ps = cons_fst sym (add_args syms ty ps);

    fun rem_pri (Argument (s, _)) = Argument (s, chain_pri)
      | rem_pri sym = sym;

    fun logify_types copy_prod (a as (Argument (s, p))) =
          if s <> "prop" andalso is_logtype s then Argument (logic, p) else a
      | logify_types _ a = a;


    val raw_symbs = read_mixfix sy handle ERROR => err_in_mfix "" mfix;
    val args = filter (fn Argument _ => true | _ => false) raw_symbs;
    val (const', typ', parse_rules) =
      if not (exists is_index args) then (const, typ, [])
      else
        let
          val indexed_const = if const <> "" then "_indexed_" ^ const
            else err_in_mfix "Missing constant name for indexed syntax" mfix;
          val rangeT = Term.range_type typ handle Match =>
            err_in_mfix "Missing structure argument for indexed syntax" mfix;

          val xs = map Ast.Variable (Term.invent_names [] "xa" (length args - 1));
          val (xs1, xs2) = Library.splitAt (Library.find_index is_index args, xs);
          val i = Ast.Variable "i";
          val lhs = Ast.mk_appl (Ast.Constant indexed_const)
            (xs1 @ [Ast.mk_appl (Ast.Constant "_index") [i]] @ xs2);
          val rhs = Ast.mk_appl (Ast.Constant const) (i :: xs);
        in (indexed_const, rangeT, [(lhs, rhs)]) end;

    val (symbs, lhs) = add_args raw_symbs typ' pris;

    val copy_prod =
      lhs mem ["prop", "logic"]
        andalso const <> ""
        andalso not (null symbs)
        andalso not (exists is_delim symbs);
    val lhs' =
      if convert andalso not copy_prod then
       (if lhs = "prop" then sprop else if is_logtype lhs then logic else lhs)
      else lhs;
    val symbs' = map (logify_types copy_prod) symbs;
    val xprod = XProd (lhs', symbs', const', pri);

    val _ = (seq check_pri pris; check_pri pri; check_blocks symbs');
    val xprod' =
      if Lexicon.is_terminal lhs' then err_in_mfix ("Illegal lhs: " ^ lhs') mfix
      else if const <> "" then xprod
      else if length (filter is_argument symbs') <> 1 then
        err_in_mfix "Copy production must have exactly one argument" mfix
      else if exists is_terminal symbs' then xprod
      else XProd (lhs', map rem_pri symbs', "", chain_pri);

  in (xprod', parse_rules) end;



(** datatype syn_ext **)

datatype syn_ext =
  SynExt of {
    xprods: xprod list,
    consts: string list,
    prmodes: string list,
    parse_ast_translation: (string * (Ast.ast list -> Ast.ast)) list,
    parse_rules: (Ast.ast * Ast.ast) list,
    parse_translation: (string * (term list -> term)) list,
    print_translation: (string * (bool -> typ -> term list -> term)) list,
    print_rules: (Ast.ast * Ast.ast) list,
    print_ast_translation: (string * (Ast.ast list -> Ast.ast)) list,
    token_translation: (string * string * (string -> string * real)) list}


(* syn_ext *)

fun syn_ext' convert is_logtype mfixes consts trfuns tokentrfuns (parse_rules, print_rules) =
  let
    val (parse_ast_translation, parse_translation, print_translation,
      print_ast_translation) = trfuns;

    val (xprods, parse_rules') = map (mfix_to_xprod convert is_logtype) mfixes
      |> split_list |> apsnd (rev o flat);
    val mfix_consts = distinct (map (fn Mfix x => #3 x) mfixes @ map (fn XProd x => #3 x) xprods);
  in
    SynExt {
      xprods = xprods,
      consts = consts union_string mfix_consts,
      prmodes = distinct (map (fn (m, _, _) => m) tokentrfuns),
      parse_ast_translation = parse_ast_translation,
      parse_rules = parse_rules' @ parse_rules,
      parse_translation = parse_translation,
      print_translation = print_translation,
      print_rules = map swap parse_rules' @ print_rules,
      print_ast_translation = print_ast_translation,
      token_translation = tokentrfuns}
  end;


val syn_ext = syn_ext' true (K false);

fun syn_ext_const_names cs = syn_ext [] cs ([], [], [], []) [] ([], []);
fun syn_ext_rules rules = syn_ext [] [] ([], [], [], []) [] rules;
fun syn_ext_trfuns trfuns = syn_ext [] [] trfuns [] ([], []);
fun syn_ext_tokentrfuns trfuns = syn_ext [] [] ([], [], [], []) trfuns ([], []);


(* pure_ext *)

val pure_ext = syn_ext' false (K false)
  [Mfix ("_", spropT --> propT, "", [0], 0),
   Mfix ("_", logicT --> anyT, "", [0], 0),
   Mfix ("_", spropT --> anyT, "", [0], 0),
   Mfix ("'(_')", logicT --> logicT, "", [0], max_pri),
   Mfix ("'(_')", spropT --> spropT, "", [0], max_pri),
   Mfix ("_::_",  [logicT, typeT] ---> logicT, "_constrain", [4, 0], 3),
   Mfix ("_::_",  [spropT, typeT] ---> spropT, "_constrain", [4, 0], 3)]
  []
  ([], [], [], [])
  []
  ([], []);

end;
