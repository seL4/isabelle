(*  Title:      Pure/Syntax/syntax.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

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
  include TOKEN_TRANS0
  include AST1
  include LEXICON0
  include SYN_EXT0
  include TYPE_EXT0
  include SYN_TRANS1
  include MIXFIX1
  include PRINTER0
  val extend_trtab: ('a * stamp) Symtab.table -> (string * 'a) list -> string
    -> ('a * stamp) Symtab.table
  val merge_trtabs: ('a * stamp) Symtab.table -> ('a * stamp) Symtab.table -> string
    -> ('a * stamp) Symtab.table
  val merge_tr'tabs: ('a * stamp) list Symtab.table -> ('a * stamp) list Symtab.table
    -> ('a * stamp) list Symtab.table
  val extend_tr'tab: ('a * stamp) list Symtab.table -> (string * 'a) list
    -> ('a * stamp) list Symtab.table
  datatype 'a trrule =
    ParseRule of 'a * 'a |
    PrintRule of 'a * 'a |
    ParsePrintRule of 'a * 'a
  type syntax
  val is_keyword: syntax -> string -> bool
  val extend_type_gram: (string * int * mixfix) list -> syntax -> syntax
  val extend_const_gram: (string -> bool) ->
    string * bool -> (string * typ * mixfix) list -> syntax -> syntax
  val extend_consts: string list -> syntax -> syntax
  val extend_trfuns:
    (string * (ast list -> ast)) list *
    (string * (term list -> term)) list *
    (string * (bool -> typ -> term list -> term)) list *
    (string * (ast list -> ast)) list -> syntax -> syntax
  val extend_tokentrfuns:
    (string * string * (string -> string * real)) list -> syntax -> syntax
  val extend_trrules_i: ast trrule list -> syntax -> syntax
  val extend_trrules: (string -> bool) -> syntax ->
    (string * string) trrule list -> syntax -> syntax
  val map_trrule: ('a -> 'b) -> 'a trrule -> 'b trrule
  val default_mode: string * bool
  val merge_syntaxes: syntax -> syntax -> syntax
  val type_syn: syntax
  val pure_syn: syntax
  val print_gram: syntax -> unit
  val print_trans: syntax -> unit
  val print_syntax: syntax -> unit
  val read: (string -> bool) -> syntax -> typ -> string -> term list
  val read_typ: syntax -> ((indexname * sort) list -> indexname -> sort) -> (sort -> sort) ->
    string -> typ
  val read_sort: syntax -> string -> sort
  val pretty_term: syntax -> bool -> term -> Pretty.T
  val pretty_typ: syntax -> typ -> Pretty.T
  val pretty_sort: syntax -> sort -> Pretty.T
  val simple_pprint_typ: typ -> pprint_args -> unit
  val ambiguity_level: int ref
  val ambiguity_is_error: bool ref
end;

structure Syntax: SYNTAX =
struct

val ambiguity_is_error = ref false

(** tables of translation functions **)

fun mk_trfun (c, f) = (c, (f, stamp ()));
fun eq_trfuns ((_, s1:stamp), (_, s2)) = s1 = s2;


(* parse (ast) translations *)

fun lookup_tr tab c = apsome fst (Symtab.lookup (tab, c));

fun err_dup_trfuns name cs =
  error ("More than one " ^ name ^ " for " ^ commas_quote cs);

fun extend_trtab tab trfuns name =
  Symtab.extend (tab, map mk_trfun trfuns)
    handle Symtab.DUPS cs => err_dup_trfuns name cs;

fun merge_trtabs tab1 tab2 name =
  Symtab.merge eq_snd (tab1, tab2)
    handle Symtab.DUPS cs => err_dup_trfuns name cs;


(* print (ast) translations *)

fun lookup_tr' tab c = map fst (Symtab.lookup_multi (tab, c));
fun extend_tr'tab tab trfuns = foldr Symtab.update_multi (map mk_trfun trfuns, tab);
fun merge_tr'tabs tab1 tab2 = Symtab.merge_multi' eq_trfuns (tab1, tab2);



(** tables of token translation functions **)

fun lookup_tokentr tabs modes =
  let val trs = gen_distinct eq_fst (flat (map (assocs tabs) (modes @ [""])))
  in fn c => apsome fst (assoc (trs, c)) end;

fun merge_tokentrtabs tabs1 tabs2 =
  let
    fun eq_tr ((c1, (_, s1)), (c2, (_, s2))) = c1 = c2 andalso s1 = s2;

    fun name (s, _) = implode (tl (Symbol.explode s));

    fun merge mode =
      let
        val trs1 = assocs tabs1 mode;
        val trs2 = assocs tabs2 mode;
        val trs = gen_distinct eq_tr (trs1 @ trs2);
      in
        (case gen_duplicates eq_fst trs of
          [] => (mode, trs)
        | dups => error ("More than one token translation function in mode " ^
            quote mode ^ " for " ^ commas_quote (map name dups)))
      end;
  in
    map merge (distinct (map fst (tabs1 @ tabs2)))
  end;

fun extend_tokentrtab tabs tokentrs =
  let
    fun ins_tokentr (ts, (m, c, f)) =
      overwrite (ts, (m, ("_" ^ c, (f, stamp ())) :: assocs ts m));
  in
    merge_tokentrtabs tabs (foldl ins_tokentr ([], tokentrs))
  end;



(** tables of translation rules **)

type ruletab = (Ast.ast * Ast.ast) list Symtab.table;

fun dest_ruletab tab = flat (map snd (Symtab.dest tab));
fun lookup_ruletab tab a = Symtab.lookup_multi (tab, a);


(* empty, extend, merge ruletabs *)

fun extend_ruletab tab rules =
  foldr Symtab.update_multi (map (fn r => (Ast.head_of_rule r, r)) rules, tab);

fun merge_ruletabs tab1 tab2 = Symtab.merge_multi' (op =) (tab1, tab2);



(** datatype syntax **)

datatype syntax =
  Syntax of {
    lexicon: Scan.lexicon,
    gram: Parser.gram,
    consts: string list,
    prmodes: string list,
    parse_ast_trtab: ((Ast.ast list -> Ast.ast) * stamp) Symtab.table,
    parse_ruletab: ruletab,
    parse_trtab: ((term list -> term) * stamp) Symtab.table,
    print_trtab: ((bool -> typ -> term list -> term) * stamp) list Symtab.table,
    print_ruletab: ruletab,
    print_ast_trtab: ((Ast.ast list -> Ast.ast) * stamp) list Symtab.table,
    tokentrtab: (string * (string * ((string -> string * real) * stamp)) list) list,
    prtabs: Printer.prtabs}

fun is_keyword (Syntax {lexicon, ...}) = Scan.is_literal lexicon o Symbol.explode;


(* empty_syntax *)

val empty_syntax =
  Syntax {
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
    prtabs = Printer.empty_prtabs}


(* extend_syntax *)

fun extend_syntax (mode, inout) syn_ext (Syntax tabs) =
  let
    val {lexicon, gram, consts = consts1, prmodes = prmodes1,
      parse_ast_trtab, parse_ruletab, parse_trtab, print_trtab, print_ruletab,
      print_ast_trtab, tokentrtab, prtabs} = tabs;
    val SynExt.SynExt {xprods, consts = consts2, prmodes = prmodes2,
      parse_ast_translation, parse_rules, parse_translation, print_translation, print_rules,
      print_ast_translation, token_translation} = syn_ext;
  in
    Syntax {
      lexicon = if inout then Scan.extend_lexicon lexicon (SynExt.delims_of xprods) else lexicon,
      gram = if inout then Parser.extend_gram gram xprods else gram,
      consts = consts2 @ consts1,
      prmodes = (mode ins_string prmodes2) union_string prmodes1,
      parse_ast_trtab =
        extend_trtab parse_ast_trtab parse_ast_translation "parse ast translation",
      parse_ruletab = extend_ruletab parse_ruletab parse_rules,
      parse_trtab = extend_trtab parse_trtab parse_translation "parse translation",
      print_trtab = extend_tr'tab print_trtab print_translation,
      print_ruletab = extend_ruletab print_ruletab print_rules,
      print_ast_trtab = extend_tr'tab print_ast_trtab print_ast_translation,
      tokentrtab = extend_tokentrtab tokentrtab token_translation,
      prtabs = Printer.extend_prtabs prtabs mode xprods}
  end;

val default_mode = ("", true);


(* merge_syntaxes *)

fun merge_syntaxes (Syntax tabs1) (Syntax tabs2) =
  let
    val {lexicon = lexicon1, gram = gram1, consts = consts1, prmodes = prmodes1,
      parse_ast_trtab = parse_ast_trtab1, parse_ruletab = parse_ruletab1,
      parse_trtab = parse_trtab1, print_trtab = print_trtab1,
      print_ruletab = print_ruletab1, print_ast_trtab = print_ast_trtab1,
      tokentrtab = tokentrtab1, prtabs = prtabs1} = tabs1;

    val {lexicon = lexicon2, gram = gram2, consts = consts2, prmodes = prmodes2,
      parse_ast_trtab = parse_ast_trtab2, parse_ruletab = parse_ruletab2,
      parse_trtab = parse_trtab2, print_trtab = print_trtab2,
      print_ruletab = print_ruletab2, print_ast_trtab = print_ast_trtab2,
      tokentrtab = tokentrtab2, prtabs = prtabs2} = tabs2;
  in
    Syntax {
      lexicon = Scan.merge_lexicons lexicon1 lexicon2,
      gram = Parser.merge_grams gram1 gram2,
      consts = unique_strings (sort_strings (consts1 @ consts2)),
      prmodes = merge_lists prmodes1 prmodes2,
      parse_ast_trtab =
        merge_trtabs parse_ast_trtab1 parse_ast_trtab2 "parse ast translation",
      parse_ruletab = merge_ruletabs parse_ruletab1 parse_ruletab2,
      parse_trtab = merge_trtabs parse_trtab1 parse_trtab2 "parse translation",
      print_trtab = merge_tr'tabs print_trtab1 print_trtab2,
      print_ruletab = merge_ruletabs print_ruletab1 print_ruletab2,
      print_ast_trtab = merge_tr'tabs print_ast_trtab1 print_ast_trtab2,
      tokentrtab = merge_tokentrtabs tokentrtab1 tokentrtab2,
      prtabs = Printer.merge_prtabs prtabs1 prtabs2}
  end;


(* type_syn *)

val type_syn = empty_syntax |> extend_syntax default_mode TypeExt.type_ext;
val pure_syn = type_syn |> extend_syntax default_mode SynExt.pure_ext;



(** inspect syntax **)

fun pretty_strs_qs name strs =
  Pretty.strs (name :: map Library.quote (sort_strings strs));


(* print_gram *)

fun print_gram (Syntax tabs) =
  let
    val {lexicon, prmodes, gram, prtabs, ...} = tabs;
    val prmodes' = sort_strings (filter_out (equal "") prmodes);
  in
    [pretty_strs_qs "lexicon:" (Scan.dest_lexicon lexicon),
      Pretty.big_list "prods:" (Parser.pretty_gram gram),
      pretty_strs_qs "print modes:" prmodes']
    |> Pretty.chunks |> Pretty.writeln
  end;


(* print_trans *)

fun print_trans (Syntax tabs) =
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
    |> Pretty.chunks |> Pretty.writeln
  end;


(* print_syntax *)

fun print_syntax syn = (print_gram syn; print_trans syn);



(** read **)

(* read_ast *)

val ambiguity_level = ref 1;

fun read_asts is_logtype (Syntax tabs) xids root str =
  let
    val {lexicon, gram, parse_ast_trtab, ...} = tabs;
    val root' = if root <> "prop" andalso is_logtype root then SynExt.logic else root;
    val chars = Symbol.explode str;
    val pts = Parser.parse gram root' (Lexicon.tokenize lexicon xids chars);

    fun show_pt pt =
      warning (Pretty.string_of (Ast.pretty_ast (hd (SynTrans.pts_to_asts (K None) [pt]))));
  in
    if length pts > ! ambiguity_level then
        if ! ambiguity_is_error then
            error ("Ambiguous input " ^ quote str)
        else
            (warning ("Ambiguous input " ^ quote str);
             warning "produces the following parse trees:";
             seq show_pt pts)
    else ();
    SynTrans.pts_to_asts (lookup_tr parse_ast_trtab) pts
  end;


(* read *)

fun read is_logtype (syn as Syntax tabs) ty str =
  let
    val {parse_ruletab, parse_trtab, ...} = tabs;
    val asts = read_asts is_logtype syn false (SynExt.typ_to_nonterm ty) str;
  in
    SynTrans.asts_to_terms (lookup_tr parse_trtab)
      (map (Ast.normalize_ast (lookup_ruletab parse_ruletab)) asts)
  end;


(* read types *)

fun read_typ syn get_sort map_sort str =
  (case read (K false) syn SynExt.typeT str of
    [t] => TypeExt.typ_of_term (get_sort (TypeExt.raw_term_sorts t)) map_sort t
  | _ => error "read_typ: ambiguous syntax");


(* read sorts *)

fun read_sort syn str =
  (case read (K false) syn TypeExt.sortT str of
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

fun parse_rule (ParseRule pats) = Some pats
  | parse_rule (PrintRule _) = None
  | parse_rule (ParsePrintRule pats) = Some pats;

fun print_rule (ParseRule _) = None
  | print_rule (PrintRule pats) = Some (swap pats)
  | print_rule (ParsePrintRule pats) = Some (swap pats);


fun check_rule (rule as (lhs, rhs)) =
  (case Ast.rule_error rule of
    Some msg =>
      error ("Error in syntax translation rule: " ^ msg ^ "\n" ^
        Ast.str_of_ast lhs ^ "  ->  " ^ Ast.str_of_ast rhs)
  | None => rule);


fun read_pattern is_logtype syn (root, str) =
  let
    val Syntax {consts, ...} = syn;

    fun constify (ast as Ast.Constant _) = ast
      | constify (ast as Ast.Variable x) =
          if x mem consts orelse NameSpace.is_qualified x then Ast.Constant x
          else ast
      | constify (Ast.Appl asts) = Ast.Appl (map constify asts);
  in
    (case read_asts is_logtype syn true root str of
      [ast] => constify ast
    | _ => error ("Syntactically ambiguous input: " ^ quote str))
  end handle ERROR =>
    error ("The error(s) above occurred in translation pattern " ^
      quote str);


fun prep_rules rd_pat raw_rules =
  let val rules = map (map_trrule rd_pat) raw_rules in
    (map check_rule (mapfilter parse_rule rules),
      map check_rule (mapfilter print_rule rules))
  end



(** pretty terms, typs, sorts **)

fun pretty_t t_to_ast prt_t (syn as Syntax tabs) curried t =
  let
    val {print_trtab, print_ruletab, print_ast_trtab, tokentrtab, prtabs, ...} = tabs;
    val ast = t_to_ast (lookup_tr' print_trtab) t;
  in
    prt_t curried prtabs (lookup_tr' print_ast_trtab)
      (lookup_tokentr tokentrtab (! print_mode))
      (Ast.normalize_ast (lookup_ruletab print_ruletab) ast)
  end;

val pretty_term = pretty_t Printer.term_to_ast Printer.pretty_term_ast;
fun pretty_typ syn = pretty_t Printer.typ_to_ast Printer.pretty_typ_ast syn false;
fun pretty_sort syn = pretty_t Printer.sort_to_ast Printer.pretty_typ_ast syn false;

val simple_pprint_typ = Pretty.pprint o Pretty.quote o (pretty_typ type_syn);



(** extend syntax **)

fun ext_syntax' f is_logtype prmode decls = extend_syntax prmode (f is_logtype decls);
fun ext_syntax f = ext_syntax' (K f) (K false) default_mode;

val extend_type_gram   = ext_syntax Mixfix.syn_ext_types;
val extend_const_gram  = ext_syntax' Mixfix.syn_ext_consts;
val extend_consts      = ext_syntax SynExt.syn_ext_const_names;
val extend_trfuns      = ext_syntax SynExt.syn_ext_trfuns;
val extend_tokentrfuns = ext_syntax SynExt.syn_ext_tokentrfuns;
val extend_trrules_i   = ext_syntax SynExt.syn_ext_rules o prep_rules I;

fun extend_trrules is_logtype syn rules =
  ext_syntax' (K SynExt.syn_ext_rules) (K false) default_mode
    (prep_rules (read_pattern is_logtype syn) rules);



(** export parts of internal Syntax structures **)

open TokenTrans Lexicon SynExt Ast Parser TypeExt SynTrans Mixfix Printer;


end;


structure BasicSyntax: BASIC_SYNTAX = Syntax;
open BasicSyntax;
