(*  Title:      Pure/Syntax/syntax.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Root of Isabelle's syntax module.
*)

signature BASIC_SYNTAX =
sig
  include AST0
  include SYN_TRANS0
  include MIXFIX0
  include PRINTER0
end;

signature SYNTAX =
sig
  include AST1
  include LEXICON0
  include SYN_EXT0
  include TYPE_EXT0
  include SYN_TRANS1
  include MIXFIX1
  include PRINTER0
  val extend_trtab: string -> (string * ('a * stamp)) list ->
    ('a * stamp) Symtab.table -> ('a * stamp) Symtab.table
  val merge_trtabs: string -> ('a * stamp) Symtab.table -> ('a * stamp) Symtab.table ->
    ('a * stamp) Symtab.table
  val merge_tr'tabs: ('a * stamp) list Symtab.table -> ('a * stamp) list Symtab.table
    -> ('a * stamp) list Symtab.table
  val extend_tr'tab: (string * ('a * stamp)) list ->
    ('a * stamp) list Symtab.table -> ('a * stamp) list Symtab.table
  datatype 'a trrule =
    ParseRule of 'a * 'a |
    PrintRule of 'a * 'a |
    ParsePrintRule of 'a * 'a
  type syntax
  val eq_syntax: syntax * syntax -> bool
  val is_keyword: syntax -> string -> bool
  val default_mode: string * bool
  val extend_type_gram: (string * int * mixfix) list -> syntax -> syntax
  val extend_const_gram: (string -> bool) ->
    string * bool -> (string * typ * mixfix) list -> syntax -> syntax
  val extend_consts: string list -> syntax -> syntax
  val extend_trfuns:
    (string * ((ast list -> ast) * stamp)) list *
    (string * ((term list -> term) * stamp)) list *
    (string * ((bool -> typ -> term list -> term) * stamp)) list *
    (string * ((ast list -> ast) * stamp)) list -> syntax -> syntax
  val extend_advanced_trfuns:
    (string * ((Context.generic -> ast list -> ast) * stamp)) list *
    (string * ((Context.generic -> term list -> term) * stamp)) list *
    (string * ((Context.generic -> bool -> typ -> term list -> term) * stamp)) list *
    (string * ((Context.generic -> ast list -> ast) * stamp)) list -> syntax -> syntax
  val extend_tokentrfuns: (string * string * (string -> string * real)) list -> syntax -> syntax
  val extend_trrules_i: ast trrule list -> syntax -> syntax
  val extend_trrules: Context.generic -> (string -> bool) -> syntax ->
    (string * string) trrule list -> syntax -> syntax
  val remove_const_gram: (string -> bool) ->
    string * bool -> (string * typ * mixfix) list -> syntax -> syntax
  val map_trrule: ('a -> 'b) -> 'a trrule -> 'b trrule
  val merge_syntaxes: syntax -> syntax -> syntax
  val basic_syn: syntax
  val basic_nonterms: string list
  val appl_syntax: (string * string * mixfix) list
  val applC_syntax: (string * string * mixfix) list
  val print_gram: syntax -> unit
  val print_trans: syntax -> unit
  val print_syntax: syntax -> unit
  val read: Context.generic -> (string -> bool) -> syntax -> typ -> string -> term list
  val read_typ: Context.generic -> syntax -> ((indexname * sort) list -> indexname -> sort) ->
    (sort -> sort) -> string -> typ
  val read_sort: Context.generic -> syntax -> string -> sort
  val pretty_term: Context.generic -> syntax -> bool -> term -> Pretty.T
  val pretty_typ: Context.generic -> syntax -> typ -> Pretty.T
  val pretty_sort: Context.generic -> syntax -> sort -> Pretty.T
  val ambiguity_level: int ref
  val ambiguity_is_error: bool ref
end;

structure Syntax: SYNTAX =
struct

(** tables of translation functions **)

(* parse (ast) translations *)

fun lookup_tr tab c = Option.map fst (Symtab.lookup tab c);

fun err_dup_trfuns name cs =
  error ("More than one " ^ name ^ " for " ^ commas_quote cs);

fun extend_trtab name trfuns tab = Symtab.extend (tab, trfuns)
  handle Symtab.DUPS cs => err_dup_trfuns name cs;

fun remove_trtab trfuns = fold (Symtab.remove SynExt.eq_trfun) trfuns;

fun merge_trtabs name tab1 tab2 = Symtab.merge SynExt.eq_trfun (tab1, tab2)
  handle Symtab.DUPS cs => err_dup_trfuns name cs;


(* print (ast) translations *)

fun lookup_tr' tab c = map fst (Symtab.lookup_list tab c);
fun extend_tr'tab trfuns = fold_rev Symtab.update_list trfuns;
fun remove_tr'tab trfuns = fold (Symtab.remove_list SynExt.eq_trfun) trfuns;
fun merge_tr'tabs tab1 tab2 = Symtab.merge_list SynExt.eq_trfun (tab1, tab2);



(** tables of token translation functions **)

fun lookup_tokentr tabs modes =
  let val trs = gen_distinct (eq_fst (op =))
    (List.concat (map (these o AList.lookup (op =) tabs) (modes @ [""])))
  in fn c => Option.map fst (AList.lookup (op =) trs c) end;

fun merge_tokentrtabs tabs1 tabs2 =
  let
    fun eq_tr ((c1, (_, s1)), (c2, (_, s2))) = c1 = c2 andalso s1 = s2;

    fun name (s, _) = implode (tl (Symbol.explode s));

    fun merge mode =
      let
        val trs1 = these (AList.lookup (op =) tabs1 mode);
        val trs2 = these (AList.lookup (op =) tabs2 mode);
        val trs = gen_distinct eq_tr (trs1 @ trs2);
      in
        (case duplicates (eq_fst (op =)) trs of
          [] => (mode, trs)
        | dups => error ("More than one token translation function in mode " ^
            quote mode ^ " for " ^ commas_quote (map name dups)))
      end;
  in
    map merge (gen_distinct (op =) (map fst (tabs1 @ tabs2)))
  end;

fun extend_tokentrtab tokentrs tabs =
  let
    fun ins_tokentr (m, c, f) =
      AList.default (op =) (m, [])
      #> AList.map_entry (op =) m (cons ("_" ^ c, (f, stamp ())));
  in merge_tokentrtabs tabs (fold ins_tokentr tokentrs []) end;



(** tables of translation rules **)

type ruletab = (Ast.ast * Ast.ast) list Symtab.table;

fun dest_ruletab tab = List.concat (map snd (Symtab.dest tab));


(* empty, extend, merge ruletabs *)

val extend_ruletab = fold_rev (fn r => Symtab.update_list (Ast.head_of_rule r, r));
val remove_ruletab = fold (fn r => Symtab.remove_list (op =) (Ast.head_of_rule r, r));
fun merge_ruletabs tab1 tab2 = Symtab.merge_list (op =) (tab1, tab2);



(** datatype syntax **)

datatype syntax =
  Syntax of {
    input: SynExt.xprod list,
    lexicon: Scan.lexicon,
    gram: Parser.gram,
    consts: string list,
    prmodes: string list,
    parse_ast_trtab: ((Context.generic -> Ast.ast list -> Ast.ast) * stamp) Symtab.table,
    parse_ruletab: ruletab,
    parse_trtab: ((Context.generic -> term list -> term) * stamp) Symtab.table,
    print_trtab: ((Context.generic -> bool -> typ -> term list -> term) * stamp) list Symtab.table,
    print_ruletab: ruletab,
    print_ast_trtab: ((Context.generic -> Ast.ast list -> Ast.ast) * stamp) list Symtab.table,
    tokentrtab: (string * (string * ((string -> string * real) * stamp)) list) list,
    prtabs: Printer.prtabs} * stamp;

fun eq_syntax (Syntax (_, s1), Syntax (_, s2)) = s1 = s2;

fun is_keyword (Syntax ({lexicon, ...}, _)) = Scan.is_literal lexicon o Symbol.explode;

val default_mode = ("", true);


(* empty_syntax *)

val empty_syntax = Syntax
  ({input = [],
    lexicon = Scan.empty_lexicon,
    gram = Parser.empty_gram,
    consts = [],
    prmodes = [],
    parse_ast_trtab = Symtab.empty,
    parse_ruletab = Symtab.empty,
    parse_trtab = Symtab.empty,
    print_trtab = Symtab.empty,
    print_ruletab = Symtab.empty,
    print_ast_trtab = Symtab.empty,
    tokentrtab = [],
    prtabs = Printer.empty_prtabs}, stamp ());


(* extend_syntax *)

fun extend_syntax (mode, inout) syn_ext (Syntax (tabs, _)) =
  let
    val {input, lexicon, gram, consts = consts1, prmodes = prmodes1,
      parse_ast_trtab, parse_ruletab, parse_trtab, print_trtab, print_ruletab,
      print_ast_trtab, tokentrtab, prtabs} = tabs;
    val SynExt.SynExt {xprods, consts = consts2, prmodes = prmodes2,
      parse_ast_translation, parse_rules, parse_translation, print_translation, print_rules,
      print_ast_translation, token_translation} = syn_ext;
  in
    Syntax
    ({input = if inout then xprods @ input else input,
      lexicon = if inout then Scan.extend_lexicon lexicon (SynExt.delims_of xprods) else lexicon,
      gram = if inout then Parser.extend_gram gram xprods else gram,
      consts = Library.merge (op =) (consts1, consts2),
      prmodes = insert (op =) mode (Library.merge (op =) (prmodes1, prmodes2)),
      parse_ast_trtab =
        extend_trtab "parse ast translation" parse_ast_translation parse_ast_trtab,
      parse_ruletab = extend_ruletab parse_rules parse_ruletab,
      parse_trtab = extend_trtab "parse translation" parse_translation parse_trtab,
      print_trtab = extend_tr'tab print_translation print_trtab,
      print_ruletab = extend_ruletab print_rules print_ruletab,
      print_ast_trtab = extend_tr'tab print_ast_translation print_ast_trtab,
      tokentrtab = extend_tokentrtab token_translation tokentrtab,
      prtabs = Printer.extend_prtabs mode xprods prtabs}, stamp ())
  end;


(* remove_syntax *)

fun remove_syntax (mode, inout) syn_ext (Syntax (tabs, _)) =
  let
    val SynExt.SynExt {xprods, consts = _, prmodes = _,
      parse_ast_translation, parse_rules, parse_translation, print_translation, print_rules,
      print_ast_translation, token_translation = _} = syn_ext;
    val {input, lexicon, gram, consts, prmodes,
      parse_ast_trtab, parse_ruletab, parse_trtab, print_trtab, print_ruletab,
      print_ast_trtab, tokentrtab, prtabs} = tabs;
    val input' = if inout then fold (remove (op =)) xprods input else input;
  in
    Syntax
    ({input = input',
      lexicon = if inout then Scan.make_lexicon (SynExt.delims_of input') else lexicon,
      gram = if inout then Parser.make_gram input' else gram,
      consts = consts,
      prmodes = prmodes,
      parse_ast_trtab = remove_trtab parse_ast_translation parse_ast_trtab,
      parse_ruletab = remove_ruletab parse_rules parse_ruletab,
      parse_trtab = remove_trtab parse_translation parse_trtab,
      print_trtab = remove_tr'tab print_translation print_trtab,
      print_ruletab = remove_ruletab print_rules print_ruletab,
      print_ast_trtab = remove_tr'tab print_ast_translation print_ast_trtab,
      tokentrtab = tokentrtab,
      prtabs = Printer.remove_prtabs mode xprods prtabs}, stamp ())
  end;


(* merge_syntaxes *)

fun merge_syntaxes (Syntax (tabs1, _)) (Syntax (tabs2, _)) =
  let
    val {input = input1, lexicon = lexicon1, gram = gram1, consts = consts1,
      prmodes = prmodes1, parse_ast_trtab = parse_ast_trtab1,
      parse_ruletab = parse_ruletab1, parse_trtab = parse_trtab1,
      print_trtab = print_trtab1, print_ruletab = print_ruletab1,
      print_ast_trtab = print_ast_trtab1, tokentrtab = tokentrtab1, prtabs = prtabs1} = tabs1;

    val {input = input2, lexicon = lexicon2, gram = gram2, consts = consts2,
      prmodes = prmodes2, parse_ast_trtab = parse_ast_trtab2,
      parse_ruletab = parse_ruletab2, parse_trtab = parse_trtab2,
      print_trtab = print_trtab2, print_ruletab = print_ruletab2,
      print_ast_trtab = print_ast_trtab2, tokentrtab = tokentrtab2, prtabs = prtabs2} = tabs2;
  in
    Syntax
    ({input = Library.merge (op =) (input1, input2),
      lexicon = Scan.merge_lexicons lexicon1 lexicon2,
      gram = Parser.merge_grams gram1 gram2,
      consts = sort_distinct string_ord (consts1 @ consts2),
      prmodes = Library.merge (op =) (prmodes1, prmodes2),
      parse_ast_trtab =
        merge_trtabs "parse ast translation" parse_ast_trtab1 parse_ast_trtab2,
      parse_ruletab = merge_ruletabs parse_ruletab1 parse_ruletab2,
      parse_trtab = merge_trtabs "parse translation" parse_trtab1 parse_trtab2,
      print_trtab = merge_tr'tabs print_trtab1 print_trtab2,
      print_ruletab = merge_ruletabs print_ruletab1 print_ruletab2,
      print_ast_trtab = merge_tr'tabs print_ast_trtab1 print_ast_trtab2,
      tokentrtab = merge_tokentrtabs tokentrtab1 tokentrtab2,
      prtabs = Printer.merge_prtabs prtabs1 prtabs2}, stamp ())
  end;


(* basic syntax *)

val basic_syn =
  empty_syntax
  |> extend_syntax default_mode TypeExt.type_ext
  |> extend_syntax default_mode SynExt.pure_ext;

val basic_nonterms =
  (Lexicon.terminals @ [SynExt.logic, "type", "types", "sort", "classes",
    SynExt.args, SynExt.cargs, "pttrn", "pttrns", "idt", "idts", "aprop",
    "asms", SynExt.any, SynExt.sprop, "num_const", "index", "struct"]);

val appl_syntax =
 [("_appl", "[('b => 'a), args] => logic", Mixfix.Mixfix ("(1_/(1'(_')))", [1000, 0], 1000)),
  ("_appl", "[('b => 'a), args] => aprop", Mixfix.Mixfix ("(1_/(1'(_')))", [1000, 0], 1000))];

val applC_syntax =
 [("",       "'a => cargs",                  Mixfix.Delimfix "_"),
  ("_cargs", "['a, cargs] => cargs",         Mixfix.Mixfix ("_/ _", [1000, 1000], 1000)),
  ("_applC", "[('b => 'a), cargs] => logic", Mixfix.Mixfix ("(1_/ _)", [1000, 1000], 999)),
  ("_applC", "[('b => 'a), cargs] => aprop", Mixfix.Mixfix ("(1_/ _)", [1000, 1000], 999))];



(** print syntax **)

local

fun pretty_strs_qs name strs =
  Pretty.strs (name :: map Library.quote (sort_strings strs));

fun pretty_gram (Syntax (tabs, _)) =
  let
    val {lexicon, prmodes, gram, prtabs, ...} = tabs;
    val prmodes' = sort_strings (filter_out (equal "") prmodes);
  in
    [pretty_strs_qs "lexicon:" (Scan.dest_lexicon lexicon),
      Pretty.big_list "prods:" (Parser.pretty_gram gram),
      pretty_strs_qs "print modes:" prmodes']
  end;

fun pretty_trans (Syntax (tabs, _)) =
  let
    fun pretty_trtab name tab =
      pretty_strs_qs name (Symtab.keys tab);

    fun pretty_ruletab name tab =
      Pretty.big_list name (map Ast.pretty_rule (dest_ruletab tab));

    fun pretty_tokentr (mode, trs) = Pretty.strs (Library.quote mode ^ ":" :: map fst trs);

    val {consts, parse_ast_trtab, parse_ruletab, parse_trtab, print_trtab,
      print_ruletab, print_ast_trtab, tokentrtab, ...} = tabs;
  in
    [pretty_strs_qs "consts:" consts,
      pretty_trtab "parse_ast_translation:" parse_ast_trtab,
      pretty_ruletab "parse_rules:" parse_ruletab,
      pretty_trtab "parse_translation:" parse_trtab,
      pretty_trtab "print_translation:" print_trtab,
      pretty_ruletab "print_rules:" print_ruletab,
      pretty_trtab "print_ast_translation:" print_ast_trtab,
      Pretty.big_list "token_translation:" (map pretty_tokentr tokentrtab)]
  end;

in

fun print_gram syn = Pretty.writeln (Pretty.chunks (pretty_gram syn));
fun print_trans syn = Pretty.writeln (Pretty.chunks (pretty_trans syn));
fun print_syntax syn = Pretty.writeln (Pretty.chunks (pretty_gram syn @ pretty_trans syn));

end;



(** read **)

(* read_ast *)

val ambiguity_level = ref 1;
val ambiguity_is_error = ref false

fun read_asts context is_logtype (Syntax (tabs, _)) xids root str =
  let
    val {lexicon, gram, parse_ast_trtab, ...} = tabs;
    val root' = if root <> "prop" andalso is_logtype root then SynExt.logic else root;
    val chars = Symbol.explode str;
    val pts = Parser.parse gram root' (Lexicon.tokenize lexicon xids chars);

    fun show_pt pt =
      Pretty.string_of (Ast.pretty_ast (hd (SynTrans.pts_to_asts context (K NONE) [pt])));
  in
    conditional (length pts > ! ambiguity_level) (fn () =>
      if ! ambiguity_is_error then error ("Ambiguous input " ^ quote str)
      else (warning ("Ambiguous input " ^ quote str ^ "\n" ^
          "produces " ^ string_of_int (length pts) ^ " parse trees.");
         List.app (warning o show_pt) pts));
    SynTrans.pts_to_asts context (lookup_tr parse_ast_trtab) pts
  end;


(* read *)

fun read context is_logtype (syn as Syntax (tabs, _)) ty str =
  let
    val {parse_ruletab, parse_trtab, ...} = tabs;
    val asts = read_asts context is_logtype syn false (SynExt.typ_to_nonterm ty) str;
  in
    SynTrans.asts_to_terms context (lookup_tr parse_trtab)
      (map (Ast.normalize_ast (Symtab.lookup_list parse_ruletab)) asts)
  end;


(* read types *)

fun read_typ context syn get_sort map_sort str =
  (case read context (K false) syn SynExt.typeT str of
    [t] => TypeExt.typ_of_term (get_sort (TypeExt.raw_term_sorts t)) map_sort t
  | _ => error "read_typ: ambiguous syntax");


(* read sorts *)

fun read_sort context syn str =
  (case read context (K false) syn TypeExt.sortT str of
    [t] => TypeExt.sort_of_term t
  | _ => error "read_sort: ambiguous syntax");



(** prepare translation rules **)

datatype 'a trrule =
  ParseRule of 'a * 'a |
  PrintRule of 'a * 'a |
  ParsePrintRule of 'a * 'a;

fun map_trrule f (ParseRule (x, y)) = ParseRule (f x, f y)
  | map_trrule f (PrintRule (x, y)) = PrintRule (f x, f y)
  | map_trrule f (ParsePrintRule (x, y)) = ParsePrintRule (f x, f y);

fun parse_rule (ParseRule pats) = SOME pats
  | parse_rule (PrintRule _) = NONE
  | parse_rule (ParsePrintRule pats) = SOME pats;

fun print_rule (ParseRule _) = NONE
  | print_rule (PrintRule pats) = SOME (swap pats)
  | print_rule (ParsePrintRule pats) = SOME (swap pats);


fun check_rule (rule as (lhs, rhs)) =
  (case Ast.rule_error rule of
    SOME msg =>
      error ("Error in syntax translation rule: " ^ msg ^ "\n" ^
        Ast.str_of_ast lhs ^ "  ->  " ^ Ast.str_of_ast rhs)
  | NONE => rule);


fun read_pattern context is_logtype syn (root, str) =
  let
    val Syntax ({consts, ...}, _) = syn;

    fun constify (ast as Ast.Constant _) = ast
      | constify (ast as Ast.Variable x) =
          if x mem consts orelse NameSpace.is_qualified x then Ast.Constant x
          else ast
      | constify (Ast.Appl asts) = Ast.Appl (map constify asts);
  in
    (case read_asts context is_logtype syn true root str of
      [ast] => constify ast
    | _ => error ("Syntactically ambiguous input: " ^ quote str))
  end handle ERROR msg =>
    cat_error msg ("The error(s) above occurred in translation pattern " ^
      quote str);


fun prep_rules rd_pat raw_rules =
  let val rules = map (map_trrule rd_pat) raw_rules in
    (map check_rule (List.mapPartial parse_rule rules),
      map check_rule (List.mapPartial print_rule rules))
  end



(** pretty terms, typs, sorts **)

fun pretty_t t_to_ast prt_t context (syn as Syntax (tabs, _)) curried t =
  let
    val {print_trtab, print_ruletab, print_ast_trtab, tokentrtab, prtabs, ...} = tabs;
    val ast = t_to_ast context (lookup_tr' print_trtab) t;
  in
    prt_t context curried prtabs (lookup_tr' print_ast_trtab)
      (lookup_tokentr tokentrtab (! print_mode))
      (Ast.normalize_ast (Symtab.lookup_list print_ruletab) ast)
  end;

val pretty_term = pretty_t Printer.term_to_ast Printer.pretty_term_ast;
fun pretty_typ context syn = pretty_t Printer.typ_to_ast Printer.pretty_typ_ast context syn false;
fun pretty_sort context syn = pretty_t Printer.sort_to_ast Printer.pretty_typ_ast context syn false;



(** extend syntax **)

fun ext_syntax' f is_logtype prmode decls = extend_syntax prmode (f is_logtype decls);
fun ext_syntax f = ext_syntax' (K f) (K false) default_mode;

val extend_type_gram       = ext_syntax Mixfix.syn_ext_types;
val extend_const_gram      = ext_syntax' Mixfix.syn_ext_consts;
val extend_consts          = ext_syntax SynExt.syn_ext_const_names;
val extend_trfuns          = ext_syntax SynExt.syn_ext_trfuns;
val extend_advanced_trfuns = ext_syntax SynExt.syn_ext_advanced_trfuns;
val extend_tokentrfuns     = ext_syntax SynExt.syn_ext_tokentrfuns;
val extend_trrules_i       = ext_syntax SynExt.syn_ext_rules o prep_rules I;

fun extend_trrules context is_logtype syn rules =
  ext_syntax' (K SynExt.syn_ext_rules) (K false) default_mode
    (prep_rules (read_pattern context is_logtype syn) rules);

fun remove_const_gram is_logtype prmode decls =
  remove_syntax prmode (Mixfix.syn_ext_consts is_logtype decls);



(*export parts of internal Syntax structures*)
open Lexicon SynExt Ast Parser TypeExt SynTrans Mixfix Printer;

end;

structure BasicSyntax: BASIC_SYNTAX = Syntax;
open BasicSyntax;
