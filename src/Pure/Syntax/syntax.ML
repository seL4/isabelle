(*  Title:      Pure/Syntax/syntax.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Root of Isabelle's syntax module.

TODO:
  extend_tables (requires extend_gram) (roots!)
  replace add_synrules by extend_tables
  extend, merge: make roots handling more robust
  extend: read_typ (incl check) as arg, remove def_sort
  extend: use extend_tables
*)

signature SYNTAX =
sig
  include AST0
  include LEXICON0
  include EXTENSION0
  include TYPE_EXT0
  include SEXTENSION1
  include PRINTER0
  type syntax
  val type_syn: syntax
  val extend: syntax * (indexname -> sort) -> string list * string list * sext
    -> syntax
  val merge: syntax * syntax -> syntax
  val print_gram: syntax -> unit
  val print_trans: syntax -> unit
  val print_syntax: syntax -> unit
  val test_read: syntax -> string -> string -> unit
  val read: syntax -> typ -> string -> term
  val pretty_term: syntax -> term -> Pretty.T
  val pretty_typ: syntax -> typ -> Pretty.T
  val string_of_term: syntax -> term -> string
  val string_of_typ: syntax -> typ -> string
end;

functor SyntaxFun(structure Symtab: SYMTAB and TypeExt: TYPE_EXT
  and Parser: PARSER and SExtension: SEXTENSION and Printer: PRINTER
  sharing TypeExt.Extension = SExtension.Extension
  and Parser.XGram = TypeExt.Extension.XGram = Printer.XGram
  and Parser.XGram.Ast = Parser.ParseTree.Ast): SYNTAX =
struct

structure Extension = TypeExt.Extension;
structure XGram = Extension.XGram;
structure Lexicon = Parser.ParseTree.Lexicon;
open Lexicon Parser Parser.ParseTree Extension TypeExt SExtension Printer
  XGram XGram.Ast;


fun lookup tab a = Symtab.lookup (tab, a);



(** datatype syntax **)

datatype tables =
  Tabs of {
    lexicon: lexicon,
    roots: string list,
    gram: gram,
    consts: string list,
    parse_ast_trtab: (ast list -> ast) Symtab.table,
    parse_ruletab: (ast * ast) list Symtab.table,
    parse_trtab: (term list -> term) Symtab.table,
    print_trtab: (term list -> term) Symtab.table,
    print_ruletab: (ast * ast) list Symtab.table,
    prtab: prtab};

datatype gramgraph =
  EmptyGG |
  ExtGG of gramgraph ref * (ext * synrules) |
  MergeGG of gramgraph ref * gramgraph ref;

datatype syntax = Syntax of gramgraph ref * tables;



(*** compile syntax ***)

(* translation funs *)

fun extend_trtab tab trfuns name =
  Symtab.balance (Symtab.st_of_alist (trfuns, tab)) handle Symtab.DUPLICATE s
    => error ("More than one " ^ name ^ " for " ^ quote s);

val mk_trtab = extend_trtab Symtab.null;


(* translation rules *)

fun mk_ruletab rules =
  let
    fun add_rule (r, tab) =
      let val a = head_of_rule r;
      in
        (case lookup tab a of
          None => Symtab.update ((a, [r]), tab)
        | Some rs => Symtab.update ((a, r :: rs), tab))
      end;
  in
    Symtab.balance (foldr add_rule (rules, Symtab.null))
  end;

fun extend_ruletab tab rules =
  mk_ruletab (flat (map #2 (Symtab.alist_of tab)) @ rules);


(* mk_tables *)

fun mk_tables (XGram xgram) =
  let
    val {roots, prods, consts, parse_ast_translation, parse_rules,
      parse_translation, print_translation, print_rules,
      print_ast_translation} = xgram;
  in
    Tabs {
      lexicon = mk_lexicon (literals_of prods),
      roots = roots,
      gram = mk_gram roots prods,
      consts = consts,
      parse_ast_trtab = mk_trtab parse_ast_translation "parse ast translation",
      parse_ruletab = mk_ruletab parse_rules,
      parse_trtab = mk_trtab parse_translation "parse translation",
      print_trtab = mk_trtab print_translation "print translation",
      print_ruletab = mk_ruletab print_rules,
      prtab = mk_prtab prods print_ast_translation}
  end;


(* add_synrules *)

fun add_synrules (Tabs tabs) (SynRules rules) =
  let
    val {lexicon, roots, gram, consts, parse_ast_trtab, parse_ruletab,
      parse_trtab, print_trtab, print_ruletab, prtab} = tabs;
    val {parse_rules, print_rules} = rules;
  in
    Tabs {
      lexicon = lexicon, roots = roots, gram = gram, consts = consts,
      parse_ast_trtab = parse_ast_trtab,
      parse_ruletab = extend_ruletab parse_ruletab parse_rules,
      parse_trtab = parse_trtab,
      print_trtab = print_trtab,
      print_ruletab = extend_ruletab print_ruletab print_rules,
      prtab = prtab}
  end;


(* ggr_to_xgram *)

fun ggr_to_xgram ggr =
  let
    fun flatGG ggr (xg, v) =
      if ggr mem v then (xg, v) else flatGG' ggr (xg, ggr :: v)
    and flatGG' (ref EmptyGG) xgv = xgv
      | flatGG' (ref (ExtGG (ggr, ext))) xgv =
          let
            val (xg', v') = flatGG ggr xgv;
          in
            (extend_xgram xg' ext, v')
          end
      | flatGG' (ref (MergeGG (ggr1, ggr2))) xgv =
          flatGG ggr1 (flatGG ggr2 xgv);
  in
    #1 (flatGG ggr (empty_xgram, []))
  end;


(* make_syntax *)

fun make_syntax ggr = Syntax (ggr, mk_tables (ggr_to_xgram ggr));



(*** inspect syntax ***)

fun xgram_of (Syntax (ggr, _)) = ggr_to_xgram ggr;

fun string_of_big_list name prts =
  Pretty.string_of (Pretty.blk (2,
    separate Pretty.fbrk (Pretty.str name :: prts)));

fun string_of_strings name strs =
  Pretty.string_of (Pretty.blk (2,
    separate (Pretty.brk 1)
      (map Pretty.str (name :: map quote (sort_strings strs)))));


(* print_gram *)

fun prt_gram (XGram {roots, prods, ...}) =
  let
    fun pretty_name name = [Pretty.str (name ^ " ="), Pretty.brk 1];

    fun pretty_xsymbs (Terminal s :: xs) =
          Pretty.str (quote s) :: Pretty.brk 1 :: pretty_xsymbs xs
      | pretty_xsymbs (Nonterminal (s, p) :: xs) =
          (if is_terminal s then Pretty.str s
          else Pretty.str (s ^ "[" ^ string_of_int p ^ "]"))
            :: Pretty.brk 1 :: pretty_xsymbs xs
      | pretty_xsymbs (_ :: xs) = pretty_xsymbs xs
      | pretty_xsymbs [] = [];

    fun pretty_const "" = [Pretty.brk 1]
      | pretty_const c = [Pretty.str (" => " ^ quote c), Pretty.brk 1];

    fun pretty_pri p = [Pretty.str ("(" ^ string_of_int p ^ ")")];

    fun pretty_prod (Prod (name, xsymbs, const, pri)) =
      Pretty.blk (2, pretty_name name @ pretty_xsymbs xsymbs @
        pretty_const const @ pretty_pri pri);
  in
    writeln (string_of_strings "lexicon:" (literals_of prods));
    writeln (Pretty.string_of (Pretty.blk (2,
      separate (Pretty.brk 1) (map Pretty.str ("roots:" :: roots)))));
    writeln (string_of_big_list "prods:" (map pretty_prod prods))
  end;

val print_gram = prt_gram o xgram_of;


(* print_trans *)

fun prt_trans (XGram xgram) =
  let
    fun string_of_trs name trs = string_of_strings name (map fst trs);

    fun string_of_rules name rules =
      string_of_big_list name (map pretty_rule rules);

    val {consts, parse_ast_translation, parse_rules, parse_translation,
      print_translation, print_rules, print_ast_translation, ...} = xgram;
  in
    writeln (string_of_strings "consts:" consts);
    writeln (string_of_trs "parse_ast_translation:" parse_ast_translation);
    writeln (string_of_rules "parse_rules:" parse_rules);
    writeln (string_of_trs "parse_translation:" parse_translation);
    writeln (string_of_trs "print_translation:" print_translation);
    writeln (string_of_rules "print_rules:" print_rules);
    writeln (string_of_trs "print_ast_translation:" print_ast_translation)
  end;

val print_trans = prt_trans o xgram_of;


(* print_syntax *)

fun print_syntax syn =
  let
    val xgram = xgram_of syn;
  in
    prt_gram xgram; prt_trans xgram
  end;



(*** parsing and printing ***)

(* mk_get_rules *)

fun mk_get_rules ruletab =
  let
    fun get_rules a =
      (case lookup ruletab a of
        Some rules => rules
      | None => []);
  in
    if Symtab.is_null ruletab then None else Some get_rules
  end;


(* read_ast *)

fun read_ast (Syntax (_, tabs)) xids root str =
  let
    val Tabs {lexicon, gram, parse_ast_trtab, ...} = tabs;
  in
    pt_to_ast (lookup parse_ast_trtab)
      (parse gram root (tokenize lexicon xids str))
  end;



(** test_read **)

fun test_read (Syntax (_, tabs)) root str =
  let
    val Tabs {lexicon, gram, parse_ast_trtab, parse_ruletab, ...} = tabs;

    val toks = tokenize lexicon false str;
    val _ = writeln ("tokens: " ^ space_implode " " (map display_token toks));

    val pt = parse gram root toks;
    val raw_ast = pt_to_ast (K None) pt;
    val _ = writeln ("raw: " ^ str_of_ast raw_ast);

    val pre_ast = pt_to_ast (lookup parse_ast_trtab) pt;
    val _ = normalize true true (mk_get_rules parse_ruletab) pre_ast;
  in () end;



(** read **)

fun read (syn as Syntax (_, tabs)) ty str =
  let
    val Tabs {parse_ruletab, parse_trtab, ...} = tabs;
    val ast = read_ast syn false (typ_to_nonterm ty) str;
  in
    ast_to_term (lookup parse_trtab)
      (normalize_ast (mk_get_rules parse_ruletab) ast)
  end;



(** read_rule **)

fun read_rule syn (xrule as ((_, lhs_src), (_, rhs_src))) =
  let
    val Syntax (_, Tabs {consts, ...}) = syn;

    fun constantify (ast as Constant _) = ast
      | constantify (ast as Variable x) =
          if x mem consts then Constant x else ast
      | constantify (Appl asts) = Appl (map constantify asts);

    fun read_pat (root, str) =
      constantify (read_ast syn true root str)
        handle ERROR => error ("The error above occurred in " ^ quote str);

    val rule as (lhs, rhs) = (pairself read_pat) xrule;
  in
    (case rule_error rule of
      Some msg =>
        error ("Error in syntax translation rule: " ^ msg ^
          "\nexternal: " ^ quote lhs_src ^ "  ->  " ^ quote rhs_src ^
          "\ninternal: " ^ str_of_ast lhs ^ "  ->  " ^ str_of_ast rhs)
    | None => rule)
  end;



(** read_xrules **)

fun read_xrules syn xrules =
  let
    fun right_rule (xpat1 |-> xpat2) = Some (xpat1, xpat2)
      | right_rule (xpat1 <-| xpat2) = None
      | right_rule (xpat1 <-> xpat2) = Some (xpat1, xpat2);

    fun left_rule (xpat1 |-> xpat2) = None
      | left_rule (xpat1 <-| xpat2) = Some (xpat2, xpat1)
      | left_rule (xpat1 <-> xpat2) = Some (xpat2, xpat1);
  in
    (map (read_rule syn) (mapfilter right_rule xrules),
     map (read_rule syn) (mapfilter left_rule xrules))
  end;



(** pretty terms or typs **)

fun pretty_t t_to_ast pretty_t (syn as Syntax (_, tabs)) t =
  let
    val Tabs {print_trtab, print_ruletab, prtab, ...} = tabs;
    val ast = t_to_ast (lookup print_trtab) t;
  in
    pretty_t prtab (normalize_ast (mk_get_rules print_ruletab) ast)
  end;

val pretty_term = pretty_t term_to_ast pretty_term_ast;

val pretty_typ = pretty_t typ_to_ast pretty_typ_ast;

fun string_of_term syn t = Pretty.string_of (pretty_term syn t);

fun string_of_typ syn ty = Pretty.string_of (pretty_typ syn ty);



(*** build syntax ***)

(* type_syn *)

val type_syn = make_syntax (ref (ExtGG (ref EmptyGG, (type_ext, empty_synrules))));


(** extend **)

fun extend (old_syn as Syntax (ggr, _), def_sort) (roots, xconsts, sext) =
  let
    fun read_typ s = typ_of_term def_sort (read old_syn typeT s);
    val ext = ext_of_sext roots xconsts read_typ sext;

    val (tmp_syn as Syntax (_, tmp_tabs)) =
      make_syntax (ref (ExtGG (ggr, (ext, empty_synrules))));

    val (parse_rules, print_rules) = read_xrules tmp_syn (xrules_of sext);
    val rules =
      SynRules {
        parse_rules = parse_rules,
        print_rules = print_rules};
  in
    Syntax (ref (ExtGG (ggr, (ext, rules))), add_synrules tmp_tabs rules)
  end;


(* merge *)

fun merge (Syntax (ggr1, _), Syntax (ggr2, _)) =
  make_syntax (ref (MergeGG (ggr1, ggr2)));


end;

