(*  Title:      Pure/Syntax/extension
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Syntax definition (internal interface)
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
        parse_preproc: (ast -> ast) option,
        parse_postproc: (ast -> ast) option,
        parse_translation: (string * (term list -> term)) list,
        print_translation: (string * (term list -> term)) list,
        print_preproc: (ast -> ast) option,
        print_postproc: (ast -> ast) option,
        print_ast_translation: (string * (ast list -> ast)) list}
    datatype synrules =
      SynRules of {
        parse_rules: (ast * ast) list,
        print_rules: (ast * ast) list}
    val max_pri: int
    val logic: string
    val id: string
    val idT: typ
    val var: string
    val varT: typ
    val tfree: string
    val tfreeT: typ
    val tvar: string
    val tvarT: typ
    val typ_to_nt: typ -> string
    val applC: string
    val args: string
    val empty_synrules: synrules
    val empty: string xgram
    val extend: string xgram -> (ext * synrules) -> string xgram
  end
end;

functor ExtensionFun(XGram: XGRAM): EXTENSION =
struct

structure XGram = XGram;
open XGram XGram.Ast;


(** datatype ext **)

(* Mfix (sy, ty, c, pl, p):
    sy: production as symbolic string
    ty: type description of production
    c: corresponding Isabelle Const
    pl: priorities of nonterminals in sy
    p: priority of production
*)

datatype mfix = Mfix of string * typ * string * int list * int;

datatype ext =
  Ext of {
    roots: string list,
    mfix: mfix list,
    extra_consts: string list,
    parse_ast_translation: (string * (ast list -> ast)) list,
    parse_preproc: (ast -> ast) option,
    parse_postproc: (ast -> ast) option,
    parse_translation: (string * (term list -> term)) list,
    print_translation: (string * (term list -> term)) list,
    print_preproc: (ast -> ast) option,
    print_postproc: (ast -> ast) option,
    print_ast_translation: (string * (ast list -> ast)) list};

datatype synrules =
  SynRules of {
    parse_rules: (ast * ast) list,
    print_rules: (ast * ast) list};


(* empty_synrules *)

val empty_synrules = SynRules {parse_rules = [], print_rules = []};


(* empty xgram *)

val empty =
  XGram {
    roots = [], prods = [], consts = [],
    parse_ast_translation = [],
    parse_preproc = None,
    parse_rules = [],
    parse_postproc = None,
    parse_translation = [],
    print_translation = [],
    print_preproc = None,
    print_rules = [],
    print_postproc = None,
    print_ast_translation = []};



(** syntactic constants etc. **)

val max_pri = 1000;   (*maximum legal priority*)

val logic = "logic";
val logicT = Type (logic, []);

val logic1 = "logic1";
val logic1T = Type (logic1, []);

val funT = Type ("fun", []);


(* terminals *)

val id = "id";
val idT = Type (id, []);

val var = "var";
val varT = Type (var, []);

val tfree = "tfree";
val tfreeT = Type (tfree, []);

val tvar = "tvar";
val tvarT = Type (tvar, []);

val terminalTs = [idT, varT, tfreeT, tvarT];


val args = "args";
val argsT = Type (args, []);

val typeT = Type ("type", []);

val applC = "_appl";
val constrainC = "_constrain";


fun typ_to_nt (Type (c, _)) = c
  | typ_to_nt _ = logic;



(** extend xgram **)    (* FIXME clean *)

fun nonts syn = foldl (fn (i, "_") => i + 1 | (i, _) => i) (0, explode syn);

val meta_chs = ["(", ")", "/", "_"];

fun mk_term(pref, []) = (pref, [])
  | mk_term(pref, "'"::c::cl) = mk_term(pref^c, cl)
  | mk_term(pref, l as c::cl) = if is_blank(c) orelse c mem meta_chs
        then (pref, l) else mk_term(pref^c, cl);

fun mk_space(sp, []) = (sp, []) |
    mk_space(sp, cl as c::cl') =
      if is_blank(c) then mk_space(sp^c, cl') else (sp, cl);

exception ARG_EXN;
exception BLOCK_EXN;

fun mk_syntax([], ar, _, b, sy) = if b=0 then (sy, ar) else raise BLOCK_EXN
  | mk_syntax("_"::cs, Type("fun", [ar, ar']), [], b, sy) =
        mk_syntax(cs, ar', [], b, sy@[Nonterminal(typ_to_nt ar, 0)])
  | mk_syntax("_"::cs, Type("fun", [ar, ar']), p::pl, b, sy) =
        mk_syntax(cs, ar', pl, b, sy@[Nonterminal(typ_to_nt ar, p)])
  | mk_syntax("_"::cs, _, _, _, _) = raise ARG_EXN
  | mk_syntax("("::cs, ar, pl, b, sy) = let val (i, cs') = scan_int cs
        in mk_syntax(cs', ar, pl, b+1, sy@[Bg(i)]) end
  | mk_syntax(")"::cs, ar, pl, b, sy) =
        if b>0 then mk_syntax(cs, ar, pl, b-1, sy@[En]) else raise BLOCK_EXN
  | mk_syntax("/"::cs, ar, pl, b, sy) = let val (sp, cs') = take_prefix is_blank cs
        in mk_syntax(cs', ar, pl, b, sy@[Brk(length sp)]) end
  | mk_syntax(c::cs, ar, pl, b, sy) =
        let val (term, rest) =
           if is_blank(c)
           then let val (sp, cs') = mk_space(c, cs) in (Space(sp), cs') end
           else let val (tk, cs') = mk_term("", c::cs) in(Terminal(tk), cs') end
        in mk_syntax(rest, ar, pl, b, sy@[term]) end;

fun pri_test1 p = if 0 <= p andalso p <= max_pri then ()
        else error("Priority out of range: " ^ string_of_int p)
fun pri_test(pl, p) = (pri_test1 p; seq pri_test1 pl);

fun mk_prod2(sy, T, opn, pl, p) =
let val (syn, T') = mk_syntax(explode sy, T, pl, 0, []) handle
        ARG_EXN =>
        error("More arguments in "^sy^" than in corresponding type") |
        BLOCK_EXN => error("Unbalanced block parantheses in "^sy);
    val nt = case T' of Type(c, _) => c | _ => logic1;
in Prod(nt, syn, opn, p) end;

fun mk_prod1(sy, T, opn, pl, p) = (pri_test(pl, p); mk_prod2(sy, T, opn, pl, p));


fun terminal1(T as Type("fun", _)) = hd(binder_types T) mem terminalTs
  | terminal1 _ = false;

fun mk_prod(Mfix(sy, T, "", pl, p)) = if nonts sy <> 1
        then error"Copy op must have exactly one argument" else
        if filter_out is_blank (explode sy) = ["_"] andalso
           not(terminal1 T)
        then mk_prod2(sy, T, "", [copy_pri], copy_pri)
        else mk_prod1(sy, T, "", pl, p)
  | mk_prod(Mfix(sy, T, const, pl, p)) = mk_prod1(sy, T, const, pl, p)



fun extend (XGram xgram) (Ext ext, SynRules rules) =
  let
    infix oo;

    fun None oo None = None
      | (Some f) oo None = Some f
      | None oo (Some g) = Some g
      | (Some f) oo (Some g) = Some (f o g);

    fun descend (from, to) = Mfix ("_", to --> from, "", [0], 0);

    fun parents T = Mfix ("(1'(_'))", T --> T, "", [0], max_pri);

    fun mkappl T =
      Mfix ("_(1'(_'))", [funT, argsT] ---> T, applC, [max_pri, 0], max_pri);

    fun mkid T = Mfix ("_", idT --> T, "", [], max_pri);

    fun mkvar T = Mfix ("_", varT --> T, "", [], max_pri);

    fun constrain T =
      Mfix ("_::_", [T, typeT]--->T, constrainC, [max_pri, 0], max_pri - 1);


    val {roots = roots1, prods, consts,
      parse_ast_translation = parse_ast_translation1,
      parse_preproc = parse_preproc1,
      parse_rules = parse_rules1,
      parse_postproc = parse_postproc1,
      parse_translation = parse_translation1,
      print_translation = print_translation1,
      print_preproc = print_preproc1,
      print_rules = print_rules1,
      print_postproc = print_postproc1,
      print_ast_translation = print_ast_translation1} = xgram;

    val {roots = roots2, mfix, extra_consts,
      parse_ast_translation = parse_ast_translation2,
      parse_preproc = parse_preproc2,
      parse_postproc = parse_postproc2,
      parse_translation = parse_translation2,
      print_translation = print_translation2,
      print_preproc = print_preproc2,
      print_postproc = print_postproc2,
      print_ast_translation = print_ast_translation2} = ext;

    val {parse_rules = parse_rules2, print_rules = print_rules2} = rules;

    val Troots = map (apr (Type, [])) (roots2 \\ roots1);
    val Troots' = Troots \\ [typeT, propT, logicT];
    val mfix' = mfix @ map parents (Troots \ logicT) @ map mkappl Troots' @
      map mkid Troots' @ map mkvar Troots' @ map constrain Troots' @
      map (apl (logicT, descend)) (Troots \\ [typeT, logicT]) @
      map (apr (descend, logic1T)) Troots';
  in
    XGram {
      roots = distinct (roots1 @ roots2),
(*      roots = roots1 union roots2,  *)    (* FIXME remove *)
      prods = prods @ map mk_prod mfix',
      consts = consts union extra_consts,
      parse_ast_translation = parse_ast_translation1 @ parse_ast_translation2,
      parse_preproc = parse_preproc1 oo parse_preproc2,
      parse_rules = parse_rules1 @ parse_rules2,
      parse_postproc = parse_postproc2 oo parse_postproc1,
      parse_translation = parse_translation1 @ parse_translation2,
      print_translation = print_translation1 @ print_translation2,
      print_preproc = print_preproc1 oo print_preproc2,
      print_rules = print_rules1 @ print_rules2,
      print_postproc = print_postproc2 oo print_postproc1,
      print_ast_translation = print_ast_translation1 @ print_ast_translation2}
  end;


end;

