(*  Title:      Pure/Syntax/extension.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

External grammar definition (internal interface).

TODO:
  Ext of {roots, mfix, extra_consts} * {.._translation} * {.._rules}
  remove synrules
  extend_xgram: move '.. \\ roots1' to Syntax.extend_tables
*)

signature EXTENSION0 =
sig
  val typeT: typ
  val constrainC: string
end;

signature EXTENSION =
sig
  include EXTENSION0
  structure XGram: XGRAM
  local open XGram XGram.Ast in
    datatype mfix = Mfix of string * typ * string * int list * int
    datatype ext =
      Ext of {
        roots: string list,
        mfix: mfix list,
        extra_consts: string list,
        parse_ast_translation: (string * (ast list -> ast)) list,
        parse_translation: (string * (term list -> term)) list,
        print_translation: (string * (term list -> term)) list,
        print_ast_translation: (string * (ast list -> ast)) list}
    datatype synrules =
      SynRules of {
        parse_rules: (ast * ast) list,
        print_rules: (ast * ast) list}
    val logic: string
    val args: string
    val idT: typ
    val varT: typ
    val tfreeT: typ
    val tvarT: typ
    val typ_to_nonterm: typ -> string
    val applC: string
    val empty_synrules: synrules
    val empty_xgram: xgram
    val extend_xgram: xgram -> (ext * synrules) -> xgram
    val mk_xgram: (ext * synrules) -> xgram
  end
end;

functor ExtensionFun(structure XGram: XGRAM and Lexicon: LEXICON): EXTENSION =
struct

structure XGram = XGram;
open XGram XGram.Ast Lexicon;


(** datatype ext **)

(*Mfix (sy, ty, c, ps, p):
    sy: rhs of production as symbolic string
    ty: type description of production
    c: head of parse tree
    ps: priorities of arguments in sy
    p: priority of production*)

datatype mfix = Mfix of string * typ * string * int list * int;

datatype ext =
  Ext of {
    roots: string list,
    mfix: mfix list,
    extra_consts: string list,
    parse_ast_translation: (string * (ast list -> ast)) list,
    parse_translation: (string * (term list -> term)) list,
    print_translation: (string * (term list -> term)) list,
    print_ast_translation: (string * (ast list -> ast)) list};

datatype synrules =
  SynRules of {
    parse_rules: (ast * ast) list,
    print_rules: (ast * ast) list};


(* empty_synrules *)

val empty_synrules = SynRules {parse_rules = [], print_rules = []};


(* empty_xgram *)

val empty_xgram =
  XGram {
    roots = [], prods = [], consts = [],
    parse_ast_translation = [],
    parse_rules = [],
    parse_translation = [],
    print_translation = [],
    print_rules = [],
    print_ast_translation = []};


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


(* typ_to_nonterm *)

fun typ_to_nonterm (Type (c, _)) = c
  | typ_to_nonterm _ = logic;

fun typ_to_nonterm1 (Type (c, _)) = c
  | typ_to_nonterm1 _ = logic1;



(** mfix_to_prod **)

fun mfix_to_prod (Mfix (sy, typ, const, pris, pri)) =
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
      $$ "_" >> K (Nonterminal ("", 0)) ||
      $$ "(" -- scan_int >> (Bg o #2) ||
      $$ ")" >> K En ||
      $$ "/" -- $$ "/" >> K (Brk ~1) ||
      $$ "/" -- scan_any is_blank >> (Brk o length o #2) ||
      scan_any1 is_blank >> (Space o implode) ||
      repeat1 scan_delim_char >> (Terminal o implode);


    val cons_fst = apfst o cons;

    fun add_args [] ty [] = ([], typ_to_nonterm1 ty)
      | add_args [] _ _ = err "too many precedences"
      | add_args (Nonterminal _ :: syms) (Type ("fun", [ty, tys])) [] =
          cons_fst (Nonterminal (typ_to_nonterm ty, 0)) (add_args syms tys [])
      | add_args (Nonterminal _ :: syms) (Type ("fun", [ty, tys])) (p :: ps) =
          cons_fst (Nonterminal (typ_to_nonterm ty, p)) (add_args syms tys ps)
      | add_args (Nonterminal _ :: _) _ _ =
          err "more arguments than in corresponding type"
      | add_args (sym :: syms) ty ps = cons_fst sym (add_args syms ty ps);


    fun is_arg (Nonterminal _) = true
      | is_arg _ = false;

    fun is_term (Terminal _) = true
      | is_term (Nonterminal (s, _)) = is_terminal s
      | is_term _ = false;

    fun rem_pri (Nonterminal (s, _)) = Nonterminal (s, chain_pri)
      | rem_pri sym = sym;


    val (raw_symbs, _) = repeat scan_symb (explode sy);
    val (symbs, lhs) = add_args raw_symbs typ pris;
    val prod = Prod (lhs, symbs, const, pri);
  in
    seq check_pri pris;
    check_pri pri;
    check_blocks symbs;
    if is_terminal lhs then err ("illegal lhs: " ^ lhs) else ();

    if const <> "" then prod
    else if length (filter is_arg symbs) <> 1 then
      err "copy production must have exactly one argument"
    else if exists is_term symbs then prod
    else Prod (lhs, map rem_pri symbs, "", chain_pri)
  end;



(** extend_xgram **)

fun extend_xgram (XGram xgram) (Ext ext, SynRules rules) =
  let
    fun descend (from, to) = Mfix ("_", to --> from, "", [0], 0);

    fun parents T = Mfix ("(1'(_'))", T --> T, "", [0], max_pri);

    fun mkappl T =
      Mfix ("_/(1'(_'))", [funT, argsT] ---> T, applC, [max_pri, 0], max_pri);

    fun mkid T = Mfix ("_", idT --> T, "", [], max_pri);

    fun mkvar T = Mfix ("_", varT --> T, "", [], max_pri);

    fun constrain T =
      Mfix ("_::_", [T, typeT] ---> T, constrainC, [max_pri, 0], max_pri - 1);


    val {roots = roots1, prods, consts,
      parse_ast_translation = parse_ast_translation1,
      parse_rules = parse_rules1,
      parse_translation = parse_translation1,
      print_translation = print_translation1,
      print_rules = print_rules1,
      print_ast_translation = print_ast_translation1} = xgram;

    val {roots = roots2, mfix, extra_consts,
      parse_ast_translation = parse_ast_translation2,
      parse_translation = parse_translation2,
      print_translation = print_translation2,
      print_ast_translation = print_ast_translation2} = ext;

    val {parse_rules = parse_rules2, print_rules = print_rules2} = rules;

    val Troots = map (apr (Type, [])) (roots2 \\ roots1);
    val Troots' = Troots \\ [typeT, propT, logicT];
    val mfix' = mfix @ map parents (Troots \ logicT) @ map mkappl Troots' @
      map mkid Troots' @ map mkvar Troots' @ map constrain Troots' @
      map (apl (logicT, descend)) (Troots \\ [typeT, logicT]) @
      map (apr (descend, logic1T)) Troots';
    val mfix_consts =
      distinct (filter is_xid (map (fn (Mfix (_, _, c, _, _)) => c) mfix'));
  in
    XGram {
      roots = distinct (roots1 @ roots2),
      prods = prods @ map mfix_to_prod mfix',
      consts = extra_consts union (mfix_consts union consts),
      parse_ast_translation = parse_ast_translation1 @ parse_ast_translation2,
      parse_rules = parse_rules1 @ parse_rules2,
      parse_translation = parse_translation1 @ parse_translation2,
      print_translation = print_translation1 @ print_translation2,
      print_rules = print_rules1 @ print_rules2,
      print_ast_translation = print_ast_translation1 @ print_ast_translation2}
  end;


(* mk_xgram *)

val mk_xgram = extend_xgram empty_xgram;


end;

