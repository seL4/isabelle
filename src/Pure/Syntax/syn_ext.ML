(*  Title:      Pure/Syntax/syn_ext.ML
    ID:         $Id$
    Author:     Markus Wenzel and Carsten Clasohm, TU Muenchen

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
      logtypes: string list,
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
  val mk_syn_ext: bool -> string list -> mfix list ->
    string list -> (string * (Ast.ast list -> Ast.ast)) list *
    (string * (term list -> term)) list *
    (string * (bool -> typ -> term list -> term)) list * (string * (Ast.ast list -> Ast.ast)) list
    -> (string * string * (string -> string * real)) list
    -> (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext: string list -> mfix list -> string list ->
    (string * (Ast.ast list -> Ast.ast)) list * (string * (term list -> term)) list *
    (string * (bool -> typ -> term list -> term)) list * (string * (Ast.ast list -> Ast.ast)) list
    -> (string * string * (string -> string * real)) list
    -> (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext_logtypes: string list -> syn_ext
  val syn_ext_const_names: string list -> string list -> syn_ext
  val syn_ext_rules: string list -> (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val fix_tr': (term list -> term) -> bool -> typ -> term list -> term
  val syn_ext_trfuns: string list ->
    (string * (Ast.ast list -> Ast.ast)) list * (string * (term list -> term)) list *
    (string * (term list -> term)) list * (string * (Ast.ast list -> Ast.ast)) list
    -> syn_ext
  val syn_ext_trfunsT: string list ->
    (string * (bool -> typ -> term list -> term)) list -> syn_ext
  val syn_ext_tokentrfuns: string list
    -> (string * string * (string -> string * real)) list -> syn_ext
  val pure_ext: syn_ext
end;

structure SynExt : SYN_EXT =
struct


(** misc definitions **)

val dddot_indexname = (Lexicon.binding "dddot", 0);
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


(* typ_to_nonterm *)

fun typ_to_nt _ (Type (c, _)) = c
  | typ_to_nt default _ = default;

(*get nonterminal for rhs*)
val typ_to_nonterm = typ_to_nt any;

(*get nonterminal for lhs*)
val typ_to_nonterm1 = typ_to_nt logic;


(* read_mixfix, mfix_args *)

local
  fun is_meta c = c mem ["(", ")", "/", "_"];

  val scan_delim_char =
    $$ "'" |-- Scan.one ((not o Symbol.is_blank) andf Symbol.not_eof) ||
    Scan.one ((not o is_meta) andf (not o Symbol.is_blank) andf Symbol.not_eof);

  val scan_sym =
    $$ "_" >> K (Argument ("", 0)) ||
    $$ "(" |-- Scan.any Symbol.is_digit >> (Bg o #1 o Term.read_int) ||
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
in
  val read_mixfix = read_symbs o Symbol.explode;
end;

fun mfix_args sy =
  foldl (fn (i, Argument _) => i + 1 | (i, _) => i) (0, read_mixfix sy);


(* mfix_to_xprod *)

fun mfix_to_xprod convert logtypes (Mfix (sy, typ, const, pris, pri)) =
  let
    fun err msg =
      (if msg = "" then () else error_msg msg;
        error ("in mixfix annotation " ^ quote sy ^ " for " ^ quote const));

    fun check_pri p =
      if p >= 0 andalso p <= max_pri then ()
      else err ("Precedence out of range: " ^ string_of_int p);

    fun blocks_ok [] 0 = true
      | blocks_ok [] _ = false
      | blocks_ok (Bg _ :: syms) n = blocks_ok syms (n + 1)
      | blocks_ok (En :: _) 0 = false
      | blocks_ok (En :: syms) n = blocks_ok syms (n - 1)
      | blocks_ok (_ :: syms) n = blocks_ok syms n;

    fun check_blocks syms =
      if blocks_ok syms 0 then ()
      else err "Unbalanced block parentheses";


    val cons_fst = apfst o cons;

    fun add_args [] ty [] = ([], typ_to_nonterm1 ty)
      | add_args [] _ _ = err "Too many precedences"
      | add_args (Argument _ :: syms) (Type ("fun", [ty, tys])) [] =
          cons_fst (Argument (typ_to_nonterm ty, 0)) (add_args syms tys [])
      | add_args (Argument _ :: syms) (Type ("fun", [ty, tys])) (p :: ps) =
          cons_fst (Argument (typ_to_nonterm ty, p)) (add_args syms tys ps)
      | add_args (Argument _ :: _) _ _ =
          err "More arguments than in corresponding type"
      | add_args (sym :: syms) ty ps = cons_fst sym (add_args syms ty ps);


    fun is_arg (Argument _) = true
      | is_arg _ = false;

    fun is_term (Delim _) = true
      | is_term (Argument (s, _)) = Lexicon.is_terminal s
      | is_term _ = false;

    fun rem_pri (Argument (s, _)) = Argument (s, chain_pri)
      | rem_pri sym = sym;

    fun is_delim (Delim _) = true
      | is_delim _ = false;

    fun logify_types copy_prod (a as (Argument (s, p))) =
          if s mem logtypes then Argument (logic, p) else a
      | logify_types _ a = a;


    val raw_symbs = read_mixfix sy handle ERROR => err "";
    val (symbs, lhs) = add_args raw_symbs typ pris;
    val copy_prod =
      lhs mem ["prop", "logic"]
        andalso const <> ""
        andalso not (null symbs)
        andalso not (exists is_delim symbs);
    val lhs' =
      if convert andalso not copy_prod then
       (if lhs mem logtypes then logic
        else if lhs = "prop" then sprop else lhs)
      else lhs;
    val symbs' = map (logify_types copy_prod) symbs;
    val xprod = XProd (lhs', symbs', const, pri);
  in
    seq check_pri pris;
    check_pri pri;
    check_blocks symbs';

    if Lexicon.is_terminal lhs' then err ("Illegal lhs: " ^ lhs')
    else if const <> "" then xprod
    else if length (filter is_arg symbs') <> 1 then
      err "Copy production must have exactly one argument"
    else if exists is_term symbs' then xprod
    else XProd (lhs', map rem_pri symbs', "", chain_pri)
  end;


(** datatype syn_ext **)

datatype syn_ext =
  SynExt of {
    logtypes: string list,
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

fun mk_syn_ext convert logtypes mfixes consts trfuns tokentrfuns rules =
  let
    val (parse_ast_translation, parse_translation, print_translation,
      print_ast_translation) = trfuns;
    val (parse_rules, print_rules) = rules;
    val logtypes' = logtypes \ "prop";

    val mfix_consts = distinct (map (fn (Mfix (_, _, c, _, _)) => c) mfixes);
    val xprods = map (mfix_to_xprod convert logtypes') mfixes;
  in
    SynExt {
      logtypes = logtypes',
      xprods = xprods,
      consts = filter Lexicon.is_xid (consts union mfix_consts),
      prmodes = distinct (map (fn (m, _, _) => m) tokentrfuns),
      parse_ast_translation = parse_ast_translation,
      parse_rules = parse_rules,
      parse_translation = parse_translation,
      print_translation = print_translation,
      print_rules = print_rules,
      print_ast_translation = print_ast_translation,
      token_translation = tokentrfuns}
  end;


val syn_ext = mk_syn_ext true;

fun syn_ext_logtypes logtypes =
  syn_ext logtypes [] [] ([], [], [], []) [] ([], []);

fun syn_ext_const_names logtypes cs =
  syn_ext logtypes [] cs ([], [], [], []) [] ([], []);

fun syn_ext_rules logtypes rules =
  syn_ext logtypes [] [] ([], [], [], []) [] rules;

fun fix_tr' f _ _ ts = f ts;

fun syn_ext_trfuns logtypes (atrs, trs, tr's, atr's) =
  syn_ext logtypes [] [] (atrs, trs, map (apsnd fix_tr') tr's, atr's) [] ([], []);

fun syn_ext_trfunsT logtypes tr's =
  syn_ext logtypes [] [] ([], [], tr's, []) [] ([], []);

fun syn_ext_tokentrfuns logtypes tokentrfuns =
  syn_ext logtypes [] [] ([], [], [], []) tokentrfuns ([], []);


(* pure_ext *)

val pure_ext = mk_syn_ext false []
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
