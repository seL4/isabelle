(*  Title:      Pure/Syntax/syn_ext.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

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
  structure Ast: AST
  local open Ast in
    val logic: string
    val args: string
    val idT: typ
    val varT: typ
    val tfreeT: typ
    val tvarT: typ
    val applC: string
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
        roots: string list,
        xprods: xprod list,
        consts: string list,
        parse_ast_translation: (string * (ast list -> ast)) list,
        parse_rules: (ast * ast) list,
        parse_translation: (string * (term list -> term)) list,
        print_translation: (string * (term list -> term)) list,
        print_rules: (ast * ast) list,
        print_ast_translation: (string * (ast list -> ast)) list}
    val syn_ext: string list -> mfix list -> string list ->
      (string * (ast list -> ast)) list * (string * (term list -> term)) list *
      (string * (term list -> term)) list * (string * (ast list -> ast)) list
      -> (ast * ast) list * (ast * ast) list -> syn_ext
    val syn_ext_rules: (ast * ast) list * (ast * ast) list -> syn_ext
    val syn_ext_roots: string list -> syn_ext
  end
end;

functor SynExtFun(structure Lexicon: LEXICON and Ast: AST): SYN_EXT =
struct

structure Ast = Ast;
open Lexicon Ast;


(** misc definitions **)

(* syntactic categories *)

val logic = "logic";
val logicT = Type (logic, []);

val logic1 = "logic1";
val logic1T = Type (logic1, []);

val args = "args";
val argsT = Type (args, []);

val funT = Type ("fun", []);

val typeT = Type ("type", []);


(* terminals *)

val idT = Type (id, []);
val varT = Type (var, []);
val tfreeT = Type (tfree, []);
val tvarT = Type (tvar, []);


(* constants *)

val applC = "_appl";
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

fun typ_to_nonterm (Type (c, _)) = c
  | typ_to_nonterm _ = logic;

fun typ_to_nonterm1 (Type (c, _)) = c
  | typ_to_nonterm1 _ = logic1;


(* mfix_to_xprod *)

fun mfix_to_xprod (Mfix (sy, typ, const, pris, pri)) =
  let
    fun err msg =
      (writeln ("Error in mixfix annotation " ^ quote sy ^ " for " ^ quote const);
        error msg);

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


    fun is_meta c = c mem ["(", ")", "/", "_"];

    fun scan_delim_char ("'" :: c :: cs) =
          if is_blank c then err "illegal spaces in delimiter" else (c, cs)
      | scan_delim_char ["'"] = err "trailing escape character"
      | scan_delim_char (chs as c :: cs) =
          if is_blank c orelse is_meta c then raise LEXICAL_ERROR else (c, cs)
      | scan_delim_char [] = raise LEXICAL_ERROR;

    val scan_symb =
      $$ "_" >> K (Argument ("", 0)) ||
      $$ "(" -- scan_int >> (Bg o #2) ||
      $$ ")" >> K En ||
      $$ "/" -- $$ "/" >> K (Brk ~1) ||
      $$ "/" -- scan_any is_blank >> (Brk o length o #2) ||
      scan_any1 is_blank >> (Space o implode) ||
      repeat1 scan_delim_char >> (Delim o implode);


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


    val (raw_symbs, _) = repeat scan_symb (explode sy);
    val (symbs, lhs) = add_args raw_symbs typ pris;
    val xprod = XProd (lhs, symbs, const, pri);
  in
    seq check_pri pris;
    check_pri pri;
    check_blocks symbs;

    if is_terminal lhs then err ("illegal lhs: " ^ lhs)
    else if const <> "" then xprod
    else if length (filter is_arg symbs) <> 1 then
      err "copy production must have exactly one argument"
    else if exists is_term symbs then xprod
    else XProd (lhs, map rem_pri symbs, "", chain_pri)
  end;



(** datatype syn_ext **)

datatype syn_ext =
  SynExt of {
    roots: string list,
    xprods: xprod list,
    consts: string list,
    parse_ast_translation: (string * (ast list -> ast)) list,
    parse_rules: (ast * ast) list,
    parse_translation: (string * (term list -> term)) list,
    print_translation: (string * (term list -> term)) list,
    print_rules: (ast * ast) list,
    print_ast_translation: (string * (ast list -> ast)) list};


(* syn_ext *)

fun syn_ext roots mfixes consts trfuns rules =
  let
    fun descend (from, to) = Mfix ("_", to --> from, "", [0], 0);

    fun parents T = Mfix ("'(_')", T --> T, "", [0], max_pri);

    fun mkappl T =
      Mfix ("(1_/(1'(_')))", [funT, argsT] ---> T, applC, [max_pri, 0], max_pri);

    fun mkid T = Mfix ("_", idT --> T, "", [], max_pri);

    fun mkvar T = Mfix ("_", varT --> T, "", [], max_pri);

    fun constrain T =
      Mfix ("_::_", [T, typeT] ---> T, constrainC, [max_pri, 0], max_pri - 1);


    val (parse_ast_translation, parse_translation, print_translation,
      print_ast_translation) = trfuns;
    val (parse_rules, print_rules) = rules;

    val Troots = map (apr (Type, [])) roots;
    val Troots' = Troots \\ [typeT, propT, logicT];
    val mfixes' = mfixes @ map parents (Troots \ logicT) @ map mkappl Troots' @
      map mkid Troots' @ map mkvar Troots' @ map constrain Troots' @
      map (apl (logicT, descend)) (Troots \\ [typeT, logicT]) @
      map (apr (descend, logic1T)) Troots';
    val mfix_consts =
      distinct (filter is_xid (map (fn (Mfix (_, _, c, _, _)) => c) mfixes'));
  in
    SynExt {
      roots = roots,
      xprods = map mfix_to_xprod mfixes',
      consts = consts union mfix_consts,
      parse_ast_translation = parse_ast_translation,
      parse_rules = parse_rules,
      parse_translation = parse_translation,
      print_translation = print_translation,
      print_rules = print_rules,
      print_ast_translation = print_ast_translation}
  end;


(* syn_ext_rules, syn_ext_roots *)

fun syn_ext_rules rules =
  syn_ext [] [] [] ([], [], [], []) rules;

fun syn_ext_roots roots =
  syn_ext roots [] [] ([], [], [], []) ([], []);


end;

