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
  datatype 'a trrule =
    ParseRule of 'a * 'a |
    PrintRule of 'a * 'a |
    ParsePrintRule of 'a * 'a
  type syntax
  val extend_log_types: syntax -> string list -> syntax
  val extend_type_gram: syntax -> (string * int * mixfix) list -> syntax
  val extend_const_gram: syntax -> string * bool -> (string * typ * mixfix) list -> syntax
  val extend_consts: syntax -> string list -> syntax
  val extend_trfuns: syntax ->
    (string * (ast list -> ast)) list *
    (string * (term list -> term)) list *
    (string * (term list -> term)) list *
    (string * (ast list -> ast)) list -> syntax
  val extend_trfunsT: syntax -> (string * (typ -> term list -> term)) list -> syntax
  val extend_tokentrfuns: syntax -> (string * string * (string -> string * int)) list -> syntax
  val extend_trrules: syntax -> (string * string) trrule list -> syntax
  val extend_trrules_i: syntax -> ast trrule list -> syntax
  val merge_syntaxes: syntax -> syntax -> syntax
  val type_syn: syntax
  val pure_syn: syntax
  val print_gram: syntax -> unit
  val print_trans: syntax -> unit
  val print_syntax: syntax -> unit
  val test_read: syntax -> string -> string -> unit
  val read: syntax -> typ -> string -> term list
  val read_typ: syntax -> ((indexname * sort) list -> indexname -> sort) -> string -> typ
  val simple_read_typ: string -> typ
  val pretty_term: syntax -> bool -> term -> Pretty.T
  val pretty_typ: syntax -> typ -> Pretty.T
  val pretty_sort: syntax -> sort -> Pretty.T
  val simple_str_of_sort: sort -> string
  val simple_string_of_typ: typ -> string
  val simple_pprint_typ: typ -> pprint_args -> unit
  val ambiguity_level: int ref
end;

structure Syntax : SYNTAX =
struct

open Lexicon SynExt Ast Parser TypeExt SynTrans Mixfix Printer;


(** tables of translation functions **)

(*does not subsume typed print translations*)
type 'a trtab = (('a list -> 'a) * stamp) Symtab.table;

val dest_trtab = Symtab.dest;

fun lookup_trtab tab c =
  apsome fst (Symtab.lookup (tab, c));


(* empty, extend, merge trtabs *)

fun err_dup_trfuns name cs =
  error ("More than one " ^ name ^ " for " ^ commas_quote cs);

val empty_trtab = Symtab.null;

fun extend_trtab tab trfuns name =
  Symtab.extend_new (tab, map (fn (c, f) => (c, (f, stamp ()))) trfuns)
    handle Symtab.DUPS cs => err_dup_trfuns name cs;

fun merge_trtabs tab1 tab2 name =
  Symtab.merge eq_snd (tab1, tab2)
    handle Symtab.DUPS cs => err_dup_trfuns name cs;



(** tables of token translation functions **)

fun lookup_tokentr tabs modes =
  let val trs = gen_distinct eq_fst (flat (map (assocs tabs) (modes @ [""])))
  in fn c => apsome fst (assoc (trs, c)) end;

fun merge_tokentrtabs tabs1 tabs2 =
  let
    fun eq_tr ((c1, (_, s1)), (c2, (_, s2))) = c1 = c2 andalso s1 = s2;

    fun name (s, _) = implode (tl (explode s));

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

type ruletab = (ast * ast) list Symtab.table;

fun dest_ruletab tab = flat (map snd (Symtab.dest tab));


(* lookup_ruletab *)

fun lookup_ruletab tab =
  if Symtab.is_null tab then None
  else Some (fn a => Symtab.lookup_multi (tab, a));


(* empty, extend, merge ruletabs *)

val empty_ruletab = Symtab.null;

fun extend_ruletab tab rules =
  generic_extend (op =) Symtab.dest_multi Symtab.make_multi tab
    (map (fn r => (head_of_rule r, r)) (distinct rules));

fun merge_ruletabs tab1 tab2 =
  generic_merge (op =) Symtab.dest_multi Symtab.make_multi tab1 tab2;



(** datatype syntax **)

datatype syntax =
  Syntax of {
    lexicon: lexicon,
    logtypes: string list,
    gram: gram,
    consts: string list,
    prmodes: string list,
    parse_ast_trtab: ast trtab,
    parse_ruletab: ruletab,
    parse_trtab: term trtab,
    print_trtab: ((typ -> term list -> term) * stamp) Symtab.table,
    print_ruletab: ruletab,
    print_ast_trtab: ast trtab,
    tokentrtab: (string * (string * ((string -> string * int) * stamp)) list) list,
    prtabs: prtabs}


(* empty_syntax *)

val empty_syntax =
  Syntax {
    lexicon = empty_lexicon,
    logtypes = [],
    gram = empty_gram,
    consts = [],
    prmodes = [],
    parse_ast_trtab = empty_trtab,
    parse_ruletab = empty_ruletab,
    parse_trtab = empty_trtab,
    print_trtab = empty_trtab,
    print_ruletab = empty_ruletab,
    print_ast_trtab = empty_trtab,
    tokentrtab = [],
    prtabs = empty_prtabs}


(* extend_syntax *)

fun extend_syntax (mode, inout) (Syntax tabs) syn_ext =
  let
    val {lexicon, logtypes = logtypes1, gram, consts = consts1, prmodes = prmodes1,
      parse_ast_trtab, parse_ruletab, parse_trtab, print_trtab, print_ruletab,
      print_ast_trtab, tokentrtab, prtabs} = tabs;
    val SynExt {logtypes = logtypes2, xprods, consts = consts2, prmodes = prmodes2,
      parse_ast_translation, parse_rules, parse_translation, print_translation, print_rules,
      print_ast_translation, token_translation} = syn_ext;
  in
    Syntax {
      lexicon = if inout then extend_lexicon lexicon (delims_of xprods) else lexicon,
      logtypes = extend_list logtypes1 logtypes2,
      gram = if inout then extend_gram gram xprods else gram,
      consts = consts2 union consts1,
      prmodes = (mode ins prmodes2) union prmodes1,
      parse_ast_trtab =
        extend_trtab parse_ast_trtab parse_ast_translation "parse ast translation",
      parse_ruletab = extend_ruletab parse_ruletab parse_rules,
      parse_trtab = extend_trtab parse_trtab parse_translation "parse translation",
      print_trtab = extend_trtab print_trtab print_translation "print translation",
      print_ruletab = extend_ruletab print_ruletab print_rules,
      print_ast_trtab =
        extend_trtab print_ast_trtab print_ast_translation "print ast translation",
      tokentrtab = extend_tokentrtab tokentrtab token_translation,
      prtabs = extend_prtabs prtabs mode xprods}
  end;


(* merge_syntaxes *)

fun merge_syntaxes (Syntax tabs1) (Syntax tabs2) =
  let
    val {lexicon = lexicon1, logtypes = logtypes1, gram = gram1, consts = consts1,
      prmodes = prmodes1, parse_ast_trtab = parse_ast_trtab1, parse_ruletab = parse_ruletab1,
      parse_trtab = parse_trtab1, print_trtab = print_trtab1,
      print_ruletab = print_ruletab1, print_ast_trtab = print_ast_trtab1,
      tokentrtab = tokentrtab1, prtabs = prtabs1} = tabs1;

    val {lexicon = lexicon2, logtypes = logtypes2, gram = gram2, consts = consts2,
      prmodes = prmodes2, parse_ast_trtab = parse_ast_trtab2, parse_ruletab = parse_ruletab2,
      parse_trtab = parse_trtab2, print_trtab = print_trtab2,
      print_ruletab = print_ruletab2, print_ast_trtab = print_ast_trtab2,
      tokentrtab = tokentrtab2, prtabs = prtabs2} = tabs2;
  in
    Syntax {
      lexicon = merge_lexicons lexicon1 lexicon2,
      logtypes = merge_lists logtypes1 logtypes2,
      gram = merge_grams gram1 gram2,
      consts = merge_lists consts1 consts2,
      prmodes = merge_lists prmodes1 prmodes2,
      parse_ast_trtab =
        merge_trtabs parse_ast_trtab1 parse_ast_trtab2 "parse ast translation",
      parse_ruletab = merge_ruletabs parse_ruletab1 parse_ruletab2,
      parse_trtab = merge_trtabs parse_trtab1 parse_trtab2 "parse translation",
      print_trtab = merge_trtabs print_trtab1 print_trtab2 "print translation",
      print_ruletab = merge_ruletabs print_ruletab1 print_ruletab2,
      print_ast_trtab =
        merge_trtabs print_ast_trtab1 print_ast_trtab2 "print ast translation",
      tokentrtab = merge_tokentrtabs tokentrtab1 tokentrtab2,
      prtabs = merge_prtabs prtabs1 prtabs2}
  end;


(* type_syn *)

val type_syn =
  extend_syntax ("", true) empty_syntax type_ext;

val pure_syn = extend_syntax ("", true) type_syn pure_ext;


(** inspect syntax **)

fun pretty_strs_qs name strs =
  Pretty.strs (name :: map quote (sort_strings strs));


(* print_gram *)

fun print_gram (Syntax tabs) =
  let
    val {lexicon, logtypes, prmodes, gram, prtabs, ...} = tabs;
    val prmodes' = sort_strings (filter_out (equal "") prmodes);
  in
    Pretty.writeln (pretty_strs_qs "lexicon:" (dest_lexicon lexicon));
    Pretty.writeln (Pretty.strs ("logtypes:" :: logtypes));
    Pretty.writeln (Pretty.big_list "prods:" (pretty_gram gram));
    Pretty.writeln (pretty_strs_qs "print modes:" prmodes')
  end;


(* print_trans *)

fun print_trans (Syntax tabs) =
  let
    fun pretty_trtab name tab =
      pretty_strs_qs name (map fst (dest_trtab tab));

    fun pretty_ruletab name tab =
      Pretty.big_list name (map pretty_rule (dest_ruletab tab));

    val {consts, parse_ast_trtab, parse_ruletab, parse_trtab, print_trtab,
      print_ruletab, print_ast_trtab, ...} = tabs;
  in
    Pretty.writeln (pretty_strs_qs "consts:" consts);
    Pretty.writeln (pretty_trtab "parse_ast_translation:" parse_ast_trtab);
    Pretty.writeln (pretty_ruletab "parse_rules:" parse_ruletab);
    Pretty.writeln (pretty_trtab "parse_translation:" parse_trtab);
    Pretty.writeln (pretty_trtab "print_translation:" print_trtab);
    Pretty.writeln (pretty_ruletab "print_rules:" print_ruletab);
    Pretty.writeln (pretty_trtab "print_ast_translation:" print_ast_trtab)
  end;


(* print_syntax *)

fun print_syntax syn = (print_gram syn; print_trans syn);



(** read **)

(* test_read *)

fun test_read (Syntax tabs) root str =
  let
    val {lexicon, gram, parse_ast_trtab, parse_ruletab, ...} = tabs;

    val chars = SymbolFont.read_charnames (explode str);
    val toks = tokenize lexicon false chars;
    val _ = writeln ("tokens: " ^ space_implode " " (map display_token toks));

    fun show_pt pt =
      let
        val raw_ast = pt_to_ast (K None) pt;
        val _ = writeln ("raw: " ^ str_of_ast raw_ast);
        val pre_ast = pt_to_ast (lookup_trtab parse_ast_trtab) pt;
        val _ = normalize true true (lookup_ruletab parse_ruletab) pre_ast;
      in () end;
  in
    seq show_pt (parse gram root toks)
  end;


(* read_ast *)

val ambiguity_level = ref 1;

fun read_asts (Syntax tabs) xids root str =
  let
    val {lexicon, gram, parse_ast_trtab, logtypes, ...} = tabs;
    val root' = if root mem logtypes then logic else root;
    val chars = SymbolFont.read_charnames (explode str);
    val pts = parse gram root' (tokenize lexicon xids chars);

    fun show_pt pt =
      warning (Pretty.string_of (pretty_ast (pt_to_ast (K None) pt)));
  in
    if length pts > ! ambiguity_level then
      (warning ("Ambiguous input " ^ quote str);
       warning "produces the following parse trees:";
       seq show_pt pts)
    else ();
    map (pt_to_ast (lookup_trtab parse_ast_trtab)) pts
  end;


(* read *)

fun read (syn as Syntax tabs) ty str =
  let
    val {parse_ruletab, parse_trtab, ...} = tabs;
    val asts = read_asts syn false (typ_to_nonterm ty) str;
  in
    map (ast_to_term (lookup_trtab parse_trtab))
      (map (normalize_ast (lookup_ruletab parse_ruletab)) asts)
  end;


(* read types *)

fun read_typ syn get_sort str =
  (case read syn typeT str of
    [t] => typ_of_term (get_sort (raw_term_sorts t)) t
  | _ => error "read_typ: ambiguous type syntax");

fun simple_read_typ str =
  let fun get_sort env xi = if_none (assoc (env, xi)) [] in
    read_typ type_syn get_sort str
  end;



(** prepare translation rules **)

datatype 'a trrule =
  ParseRule of 'a * 'a |
  PrintRule of 'a * 'a |
  ParsePrintRule of 'a * 'a;

fun map_rule f (ParseRule (x, y)) = ParseRule (f x, f y)
  | map_rule f (PrintRule (x, y)) = PrintRule (f x, f y)
  | map_rule f (ParsePrintRule (x, y)) = ParsePrintRule (f x, f y);

fun parse_rule (ParseRule pats) = Some pats
  | parse_rule (PrintRule _) = None
  | parse_rule (ParsePrintRule pats) = Some pats;

fun print_rule (ParseRule _) = None
  | print_rule (PrintRule pats) = Some (swap pats)
  | print_rule (ParsePrintRule pats) = Some (swap pats);


fun check_rule (rule as (lhs, rhs)) =
  (case rule_error rule of
    Some msg =>
      error ("Error in syntax translation rule: " ^ msg ^ "\n" ^
        str_of_ast lhs ^ "  ->  " ^ str_of_ast rhs)
  | None => rule);


fun read_pattern syn (root, str) =
  let
    val Syntax {consts, ...} = syn;

    fun constify (ast as Constant _) = ast
      | constify (ast as Variable x) =
          if x mem consts then Constant x else ast
      | constify (Appl asts) = Appl (map constify asts);
  in
    (case read_asts syn true root str of
      [ast] => constify ast
    | _ => error ("Syntactically ambiguous input: " ^ quote str))
  end handle ERROR =>
    error ("The error(s) above occurred in translation pattern " ^
      quote str);


fun prep_rules rd_pat raw_rules =
  let val rules = map (map_rule rd_pat) raw_rules in
    (map check_rule (mapfilter parse_rule rules),
      map check_rule (mapfilter print_rule rules))
  end



(** pretty terms, typs, sorts **)

fun pretty_t t_to_ast prt_t (syn as Syntax tabs) curried t =
  let
    val {print_trtab, print_ruletab, print_ast_trtab, tokentrtab, prtabs, ...} = tabs;
    val ast = t_to_ast (lookup_trtab print_trtab) t;
  in
    prt_t curried prtabs (lookup_trtab print_ast_trtab)
      (lookup_tokentr tokentrtab (! print_mode))
      (normalize_ast (lookup_ruletab print_ruletab) ast)
  end;

val pretty_term = pretty_t term_to_ast pretty_term_ast;
fun pretty_typ syn = pretty_t typ_to_ast pretty_typ_ast syn false;
fun pretty_sort syn = pretty_t sort_to_ast pretty_typ_ast syn false;

val simple_str_of_sort = Pretty.str_of o pretty_sort type_syn;
val simple_string_of_typ = Pretty.string_of o (pretty_typ type_syn);
val simple_pprint_typ = Pretty.pprint o Pretty.quote o (pretty_typ type_syn);



(** extend syntax (external interfaces) **)

fun ext_syntax mk_syn_ext prmode (syn as Syntax {logtypes, ...}) decls =
  extend_syntax prmode syn (mk_syn_ext logtypes decls);


fun extend_log_types syn logtypes =
  extend_syntax ("", true) syn (syn_ext_logtypes logtypes);

val extend_type_gram = ext_syntax syn_ext_types ("", true);

fun extend_const_gram syn prmode = ext_syntax syn_ext_consts prmode syn;

val extend_consts = ext_syntax syn_ext_const_names ("", true);

val extend_trfuns = ext_syntax syn_ext_trfuns ("", true);

val extend_trfunsT = ext_syntax syn_ext_trfunsT ("", true);

val extend_tokentrfuns = ext_syntax syn_ext_tokentrfuns ("", true);

fun extend_trrules syn rules =
  ext_syntax syn_ext_rules ("", true) syn (prep_rules (read_pattern syn) rules);

fun extend_trrules_i syn rules =
  ext_syntax syn_ext_rules ("", true) syn (prep_rules I rules);


end;
