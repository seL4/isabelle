(*  Title:      Pure/Syntax/syn_ext.ML
    ID:         $Id$
    Author:     Markus Wenzel and Carsten Clasohm, TU Muenchen

Syntax extension (internal interface).
*)

signature SYN_EXT0 =
  sig
  val typeT: typ
  val constrainC: string
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
  val max_pri: int
  val chain_pri: int
  val delims_of: xprod list -> string list
  datatype mfix = Mfix of string * typ * string * int list * int
  datatype syn_ext =
    SynExt of {
      logtypes: string list,
      xprods: xprod list,
      consts: string list,
      parse_ast_translation: (string * (Ast.ast list -> Ast.ast)) list,
      parse_rules: (Ast.ast * Ast.ast) list,
      parse_translation: (string * (term list -> term)) list,
      print_translation: (string * (typ -> term list -> term)) list,
      print_rules: (Ast.ast * Ast.ast) list,
      print_ast_translation: (string * (Ast.ast list -> Ast.ast)) list}
  val mk_syn_ext: bool -> string list -> mfix list ->
    string list -> (string * (Ast.ast list -> Ast.ast)) list *
    (string * (term list -> term)) list *
    (string * (typ -> term list -> term)) list * (string * (Ast.ast list -> Ast.ast)) list
    -> (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext: string list -> mfix list -> string list ->
    (string * (Ast.ast list -> Ast.ast)) list * (string * (term list -> term)) list *
    (string * (typ -> term list -> term)) list * (string * (Ast.ast list -> Ast.ast)) list
    -> (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext_logtypes: string list -> syn_ext
  val syn_ext_const_names: string list -> string list -> syn_ext
  val syn_ext_rules: string list -> (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val fix_tr': (term list -> term) -> typ -> term list -> term
  val syn_ext_trfuns: string list ->
    (string * (Ast.ast list -> Ast.ast)) list * (string * (term list -> term)) list *
    (string * (term list -> term)) list * (string * (Ast.ast list -> Ast.ast)) list
    -> syn_ext
  val syn_ext_trfunsT: string list -> (string * (typ -> term list -> term)) list -> syn_ext
  val pure_ext: syn_ext
  end;

structure SynExt : SYN_EXT =
struct

open Lexicon Ast;

(** misc definitions **)

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


(* constants *)

val constrainC = "_constrain";



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
    distinct (flat (map dels_of xprods))
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


(* mfix_to_xprod *)

fun mfix_to_xprod convert logtypes (Mfix (sy, typ, const, pris, pri)) =
  let
    fun err msg =
      (writeln ("Error in mixfix annotation " ^ quote sy ^ " for " ^ quote const);
        error msg);
    fun post_err () = error ("The error(s) above occurred in mixfix annotation " ^
      quote sy ^ " for " ^ quote const);

    fun check_pri p =
      if p >= 0 andalso p <= max_pri then ()
      else err ("precedence out of range: " ^ string_of_int p);

    fun blocks_ok [] 0 = true
      | blocks_ok [] _ = false
      | blocks_ok (Bg _ :: syms) n = blocks_ok syms (n + 1)
      | blocks_ok (En :: _) 0 = false
      | blocks_ok (En :: syms) n = blocks_ok syms (n - 1)
      | blocks_ok (_ :: syms) n = blocks_ok syms n;

    fun check_blocks syms =
      if blocks_ok syms 0 then ()
      else err "unbalanced block parentheses";


    local
      fun is_meta c = c mem ["(", ")", "/", "_"];

      fun scan_delim_char ("'" :: c :: cs) =
            if is_blank c then raise LEXICAL_ERROR else (c, cs)
        | scan_delim_char ["'"] = err "trailing escape character"
        | scan_delim_char (chs as c :: cs) =
            if is_blank c orelse is_meta c then raise LEXICAL_ERROR else (c, cs)
        | scan_delim_char [] = raise LEXICAL_ERROR;

      val scan_sym =
        $$ "_" >> K (Argument ("", 0)) ||
        $$ "(" -- scan_int >> (Bg o #2) ||
        $$ ")" >> K En ||
        $$ "/" -- $$ "/" >> K (Brk ~1) ||
        $$ "/" -- scan_any is_blank >> (Brk o length o #2) ||
        scan_any1 is_blank >> (Space o implode) ||
        repeat1 scan_delim_char >> (Delim o implode);

      val scan_symb =
        scan_sym >> Some ||
        $$ "'" -- scan_one is_blank >> K None;
    in
      val scan_symbs = mapfilter I o #1 o repeat scan_symb;
    end;


    val cons_fst = apfst o cons;

    fun add_args [] ty [] = ([], typ_to_nonterm1 ty)
      | add_args [] _ _ = err "too many precedences"
      | add_args (Argument _ :: syms) (Type ("fun", [ty, tys])) [] =
          cons_fst (Argument (typ_to_nonterm ty, 0)) (add_args syms tys [])
      | add_args (Argument _ :: syms) (Type ("fun", [ty, tys])) (p :: ps) =
          cons_fst (Argument (typ_to_nonterm ty, p)) (add_args syms tys ps)
      | add_args (Argument _ :: _) _ _ =
          err "more arguments than in corresponding type"
      | add_args (sym :: syms) ty ps = cons_fst sym (add_args syms ty ps);


    fun is_arg (Argument _) = true
      | is_arg _ = false;

    fun is_term (Delim _) = true
      | is_term (Argument (s, _)) = is_terminal s
      | is_term _ = false;

    fun rem_pri (Argument (s, _)) = Argument (s, chain_pri)
      | rem_pri sym = sym;

    fun is_delim (Delim _) = true
      | is_delim _ = false;

    (*replace logical types on rhs by "logic"*)
    fun unify_logtypes copy_prod (a as (Argument (s, p))) =
          if s mem logtypes then Argument (logic, p)
          else a
      | unify_logtypes _ a = a;


    val sy_chars =
      SymbolFont.read_charnames (explode sy) handle ERROR => post_err ();
    val raw_symbs = scan_symbs sy_chars;
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
    val symbs' = map (unify_logtypes copy_prod) symbs;
    val xprod = XProd (lhs', symbs', const, pri);
  in
    seq check_pri pris;
    check_pri pri;
    check_blocks symbs';

    if is_terminal lhs' then err ("illegal lhs: " ^ lhs')
    else if const <> "" then xprod
    else if length (filter is_arg symbs') <> 1 then
      err "copy production must have exactly one argument"
    else if exists is_term symbs' then xprod
    else XProd (lhs', map rem_pri symbs', "", chain_pri)
  end;


(** datatype syn_ext **)

datatype syn_ext =
  SynExt of {
    logtypes: string list,
    xprods: xprod list,
    consts: string list,
    parse_ast_translation: (string * (Ast.ast list -> Ast.ast)) list,
    parse_rules: (Ast.ast * Ast.ast) list,
    parse_translation: (string * (term list -> term)) list,
    print_translation: (string * (typ -> term list -> term)) list,
    print_rules: (Ast.ast * Ast.ast) list,
    print_ast_translation: (string * (Ast.ast list -> Ast.ast)) list};


(* syn_ext *)

fun mk_syn_ext convert logtypes mfixes consts trfuns rules =
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
      consts = filter is_xid (consts union mfix_consts),
      parse_ast_translation = parse_ast_translation,
      parse_rules = parse_rules,
      parse_translation = parse_translation,
      print_translation = print_translation,
      print_rules = print_rules,
      print_ast_translation = print_ast_translation}
  end;


val syn_ext = mk_syn_ext true;

fun syn_ext_logtypes logtypes =
  syn_ext logtypes [] [] ([], [], [], []) ([], []);

fun syn_ext_const_names logtypes cs =
  syn_ext logtypes [] cs ([], [], [], []) ([], []);

fun syn_ext_rules logtypes rules =
  syn_ext logtypes [] [] ([], [], [], []) rules;

fun fix_tr' f _ args = f args;

fun syn_ext_trfuns logtypes (atrs, trs, tr's, atr's) =
  syn_ext logtypes [] [] (atrs, trs, map (apsnd fix_tr') tr's, atr's) ([], []);

fun syn_ext_trfunsT logtypes tr's =
  syn_ext logtypes [] [] ([], [], tr's, []) ([], []);


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
  ([], []);

end;
