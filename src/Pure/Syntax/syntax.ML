(*  Title:      Pure/Syntax/syntax
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
*)

signature SYNTAX =
sig
  (* FIXME include AST0 (?) *)
  include LEXICON0
  include EXTENSION0
  include TYPE_EXT0
  include SEXTENSION1
  include PRINTER0
  structure Extension: EXTENSION
  structure Pretty: PRETTY
  local open Extension.XGram Extension.XGram.Ast in
    type syntax
    val print_gram: syntax -> unit
    val print_trans: syntax -> unit
    val print_syntax: syntax -> unit
    val read_ast: syntax -> string * string -> ast
    val read: syntax -> typ -> string -> term
    val pretty_term: syntax -> term -> Pretty.T
    val pretty_typ: syntax -> typ -> Pretty.T
    val string_of_term: syntax -> term -> string
    val string_of_typ: syntax -> typ -> string
    val type_syn: syntax
    val extend: syntax * (indexname -> sort) -> string list * string list * sext
      -> syntax
    val merge: syntax * syntax -> syntax
  end
end;

functor SyntaxFun(structure Symtab: SYMTAB and TypeExt: TYPE_EXT
  and Parser: PARSER and SExtension: SEXTENSION and Printer: PRINTER
  sharing TypeExt.Extension.XGram = Parser.XGram = Printer.XGram
  and TypeExt.Extension = SExtension.Extension
  and Parser.ParseTree.Ast = Parser.XGram.Ast)(*: SYNTAX *) = (* FIXME *)
struct

structure Extension = TypeExt.Extension;
structure XGram = Extension.XGram;
structure Lexicon = Parser.ParseTree.Lexicon;
open Lexicon Extension TypeExt SExtension Printer XGram XGram.Ast;


fun lookup tab a = Symtab.lookup (tab, a);



(** datatype syntax **)

datatype tables =
  Tab of {
    gram: Parser.Gram,
    lexicon: Lexicon,
    const_tab: unit Symtab.table,
    parse_ast_trtab: (ast list -> ast) Symtab.table,
    parse_preproc: ast -> ast,
    parse_ruletab: (ast * ast) list Symtab.table,
    parse_postproc: ast -> ast,
    parse_trtab: (term list -> term) Symtab.table,
    print_trtab: (term list -> term) Symtab.table,
    print_preproc: ast -> ast,
    print_ruletab: (ast * ast) list Symtab.table,
    print_postproc: ast -> ast,
    print_tab: Printer.tab};

datatype gramgraph =
  EmptyGG |
  ExtGG of gramgraph ref * (ext * synrules) |
  MergeGG of gramgraph ref * gramgraph ref;

datatype syntax = Syntax of gramgraph ref * tables;



(*** compile syntax ***)

(* ggr_to_xgram *)

fun ggr_to_xgram ggr =
  let
    fun flatGG ggr (xg, v) =
      if ggr mem v then (xg, v) else flatGG' ggr (xg, ggr :: v)
    and flatGG' (ref EmptyGG) xgv = xgv
      | flatGG' (ref (ExtGG (ggr, ext))) xgv =
          let
            val (xg', v') = flatGG ggr xgv
          in
            (Extension.extend xg' ext, v')
          end
      | flatGG' (ref (MergeGG (ggr1, ggr2))) xgv =
          flatGG ggr1 (flatGG ggr2 xgv);
  in
    fst (flatGG ggr (Extension.empty, []))
  end;


(* mk_ruletab *)

fun mk_ruletab rules =
  let
    fun add_rule (r, tab) =
      let
        val a = head_of_rule r
      in
        case lookup tab a of
          None => Symtab.update ((a, [r]), tab)
        | Some rs => Symtab.update ((a, r :: rs), tab)
      end;
  in
    Symtab.balance (foldr add_rule (rules, Symtab.null))
  end;


(* make_syntax *)

fun make_syntax ggr =
  let
    fun mk_const_tab cs =
      Symtab.balance
        (Symtab.st_of_alist ((map (fn c => (c, ())) cs), Symtab.null));

    fun mk_trtab alst name =
      Symtab.balance (Symtab.st_of_alist (alst, Symtab.null))
        handle Symtab.DUPLICATE s => error ("More than one " ^ name ^ " for " ^ quote s);

    fun mk_proc (Some f) = f
      | mk_proc None = I;

    fun all_strings (opl: string prod list): string list =
        flat (map (fn Prod (_, syn, _, _) => terminals syn) opl);

    fun str_to_tok (opl: string prod list, lex: Lexicon): Token prod list =
      map
        (fn Prod (t, syn, s, pa) =>
          Prod (t, translate (hd o tokenize lex) syn, s, pa))
        opl;

    fun xgram_to_tables (XGram xgram) =
      let
        val {roots, prods, consts, parse_ast_translation, parse_preproc, parse_rules,
          parse_postproc, parse_translation, print_translation, print_preproc,
          print_rules, print_postproc, print_ast_translation} = xgram;
        val lexicon = mk_lexicon (all_strings prods);
      in
        Tab {
          gram = Parser.compile_xgram (roots, str_to_tok (prods, lexicon)),
          lexicon = lexicon,
          const_tab = mk_const_tab consts,
          parse_ast_trtab = mk_trtab parse_ast_translation "parse ast translation",
          parse_preproc = mk_proc parse_preproc,
          parse_ruletab = mk_ruletab parse_rules,
          parse_postproc = mk_proc parse_postproc,
          parse_trtab = mk_trtab parse_translation "parse translation",
          print_trtab = mk_trtab print_translation "print translation",
          print_preproc = mk_proc print_preproc,
          print_ruletab = mk_ruletab print_rules,
          print_postproc = mk_proc print_postproc,
          print_tab = mk_print_tab prods
            (mk_trtab print_ast_translation "print ast translation")}
      end;
  in
    Syntax (ggr, xgram_to_tables (ggr_to_xgram ggr))
  end;


(* add_synrules *)

fun add_synrules (Tab tabs) (SynRules rules) =
  let
    val {gram, lexicon, const_tab, parse_ast_trtab, parse_preproc, parse_ruletab,
      parse_postproc, parse_trtab, print_trtab, print_preproc, print_ruletab,
      print_postproc, print_tab} = tabs;
    val {parse_rules, print_rules} = rules;
    val parse_rs = flat (map snd (Symtab.alist_of parse_ruletab)) @ parse_rules;
    val print_rs = flat (map snd (Symtab.alist_of print_ruletab)) @ print_rules;
  in
    Tab {
      gram = gram, lexicon = lexicon, const_tab = const_tab,
      parse_ast_trtab = parse_ast_trtab,
      parse_preproc = parse_preproc,
      parse_ruletab = mk_ruletab parse_rs,
      parse_postproc = parse_postproc,
      parse_trtab = parse_trtab,
      print_trtab = print_trtab,
      print_preproc = print_preproc,
      print_ruletab = mk_ruletab print_rs,
      print_postproc = print_postproc,
      print_tab = print_tab}
  end;



(*** inspect syntax ***)

(* print_syntax_old *) (* FIXME remove *)

fun print_syntax_old (Syntax (_, Tab {gram, lexicon, ...})) =
  Parser.print_gram (gram, lexicon);



fun xgram_of (Syntax (ggr, _)) = ggr_to_xgram ggr;

fun string_of_big_list name prts =
  Pretty.string_of (Pretty.blk (2,
    separate Pretty.fbrk (Pretty.str name :: prts)));


(* print_gram *)    (* FIXME check *)

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
    writeln (Pretty.string_of (Pretty.blk (2,
      separate (Pretty.brk 1) (map Pretty.str ("roots:" :: roots)))));
    writeln (string_of_big_list "prods:" (map pretty_prod prods))
  end;


val print_gram = prt_gram o xgram_of;


(* print_trans *)   (* FIXME check *)

fun prt_trans (XGram xgram) =
  let
    fun string_of_strings name strs =
      Pretty.string_of (Pretty.blk (2,
        separate (Pretty.brk 1) (map Pretty.str (name :: map quote strs))));

    fun string_of_trs name trs = string_of_strings name (map fst trs);

    fun string_of_proc name proc =
      Pretty.string_of (Pretty.blk (2, [Pretty.str name, Pretty.brk 1,
        Pretty.str (if is_none proc then "None" else "Some fn")]));

    fun string_of_rules name rules =
      string_of_big_list name (map pretty_rule rules);


    val {consts, parse_ast_translation, parse_preproc, parse_rules,
      parse_postproc, parse_translation, print_translation, print_preproc,
      print_rules, print_postproc, print_ast_translation, ...} = xgram;
  in
    writeln (string_of_strings "consts:" consts);
    writeln (string_of_trs "parse_ast_translation:" parse_ast_translation);
    writeln (string_of_proc "parse_preproc:" parse_preproc);
    writeln (string_of_rules "parse_rules:" parse_rules);
    writeln (string_of_proc "parse_postproc:" parse_postproc);
    writeln (string_of_trs "parse_translation:" parse_translation);
    writeln (string_of_trs "print_translation:" print_translation);
    writeln (string_of_proc "print_preproc:" print_preproc);
    writeln (string_of_rules "print_rules:" print_rules);
    writeln (string_of_proc "print_postproc:" print_postproc);
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

(* read_ast *)

fun read_ast syn (root, s) =
  let
    val Syntax (_, Tab {gram, lexicon, parse_ast_trtab, ...}) = syn;
    val root = if Parser.parsable (gram, root) then root else error ("Unparsable root " ^ root) (* Extension.logic *);    (* FIXME *)
    fun syn_err toks =
      error ("Syntax error at\n" ^ space_implode " " (map token_to_string toks));
  in
    Parser.ParseTree.pt_to_ast (lookup parse_ast_trtab)
      (Parser.parse (gram, root, tokenize lexicon s))
        handle Parser.SYNTAX_ERR toks => syn_err toks
  end;


(* norm_ast *)

fun norm_ast ruletab ast =
  let
    fun get_rules a =
      (case lookup ruletab a of
        Some rules => rules
      | None => []);
  in
    normalize (if Symtab.is_null ruletab then None else Some get_rules) ast
  end;



(** read **)

fun read (syn as Syntax (_, Tab tabs)) ty s =
  let
    val {parse_preproc, parse_ruletab, parse_postproc, parse_trtab, ...} = tabs;
    val ast = read_ast syn (typ_to_nt ty, s);
  in
    ast_to_term (lookup parse_trtab)
      (parse_postproc (norm_ast parse_ruletab (parse_preproc ast)))
  end;



(** pprint_ast **)

val pprint_ast = Pretty.pprint o pretty_ast;



(** pretty term, typ **)

fun pretty_t t_to_ast pretty_t (syn as Syntax (_, Tab tabs)) t =
  let
    val {print_trtab, print_preproc, print_ruletab, print_postproc, print_tab, ...} = tabs;
    val ast = t_to_ast (lookup print_trtab) t;
  in
    pretty_t print_tab
      (print_postproc (norm_ast print_ruletab (print_preproc ast)))
  end;

val pretty_term = pretty_t term_to_ast pretty_term_ast;

val pretty_typ = pretty_t typ_to_ast pretty_typ_ast;

fun string_of_term syn t = Pretty.string_of (pretty_term syn t);

fun string_of_typ syn ty = Pretty.string_of (pretty_typ syn ty);



(*** build syntax ***)

(* type_syn *)

val type_syn = make_syntax (ref (ExtGG (ref EmptyGG, (type_ext, empty_synrules))));


(* extend *)  (* FIXME check *)

fun extend (old_syn as Syntax (ggr, _), def_sort) (roots, xconsts, sext) =
  let
    fun read_typ s = typ_of_term def_sort (read old_syn typeT s);
    val ext = ext_of_sext roots xconsts read_typ sext;

    fun right_rule (xpat1 |-> xpat2) = Some (xpat1, xpat2)
      | right_rule (xpat1 <-| xpat2) = None
      | right_rule (xpat1 <-> xpat2) = Some (xpat1, xpat2);

    fun left_rule (xpat1 |-> xpat2) = None
      | left_rule (xpat1 <-| xpat2) = Some (xpat2, xpat1)
      | left_rule (xpat1 <-> xpat2) = Some (xpat2, xpat1);

    val (tmp_syn as Syntax (_, tmp_tabs)) =
      make_syntax (ref (ExtGG (ggr, (ext, empty_synrules))));
    val Syntax (_, Tab {const_tab, ...}) = tmp_syn;

    fun constantify (ast as (Constant _)) = ast
      | constantify (ast as (Variable x)) =
          if is_some (lookup const_tab x) then Constant x else ast
      | constantify (Appl asts) = Appl (map constantify asts);

    fun read_pat (r_s as (root, s)) =
      constantify ((read_ast tmp_syn r_s)
        handle ERROR => error ("The error above occurred in " ^ quote s));

    fun read_rule (xrule as ((_, lhs_src), (_, rhs_src))) =
      let
        val rule as (lhs, rhs) = (pairself read_pat) xrule;
      in
        case rule_error rule of
          Some msg =>
            error ("Error in syntax translation rule: " ^ msg ^
              "\nexternal: " ^ quote lhs_src ^ "  ->  " ^ quote rhs_src ^
              "\ninternal: " ^ str_of_ast lhs ^ "  ->  " ^ str_of_ast rhs)
        | None => rule
      end;

    val xrules = xrules_of sext;
    val new_rules =
      SynRules {
        parse_rules = map read_rule (mapfilter right_rule xrules),
        print_rules = map read_rule (mapfilter left_rule xrules)};
  in
    Syntax (ref (ExtGG (ggr, (ext, new_rules))), add_synrules tmp_tabs new_rules)
  end;


(* merge *)

fun merge (Syntax (ggr1, _), Syntax (ggr2, _)) =
  make_syntax (ref (MergeGG (ggr1, ggr2)));


end;

