(*  Title:      Pure/Syntax/syntax.ML
    ID:         $Id$
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Root of Isabelle's syntax module.
*)

signature BASIC_SYNTAX =
sig
  include AST0
  include SEXTENSION0
(*  include MIXFIX0   *)   (* FIXME *)
  include PRINTER0
end;

signature SYNTAX =
sig
  include AST1
  include LEXICON0
  include SYN_EXT0
  include TYPE_EXT0
  include SEXTENSION1
  include PRINTER0
  sharing type ast = Parser.SynExt.Ast.ast
  structure Mixfix: MIXFIX
  local open Mixfix in    (* FIXME *)
    type syntax
    val extend_log_types: syntax -> string list -> syntax
    val extend_type_gram: syntax -> (string * int * mixfix) list -> syntax
    val extend_const_gram: syntax -> (string * typ * mixfix) list -> syntax
    val extend_consts: syntax -> string list -> syntax
    val extend_trfuns: syntax ->
      (string * (ast list -> ast)) list *
      (string * (term list -> term)) list *
      (string * (term list -> term)) list *
      (string * (ast list -> ast)) list -> syntax
    val extend_trrules: syntax -> xrule list -> syntax
  end  (* FIXME *)
    val extend: syntax -> (string -> typ) -> string list * string list * sext
      -> syntax     (* FIXME *)
    val merge_syntaxes: syntax -> syntax -> syntax
    val type_syn: syntax
    val print_gram: syntax -> unit
    val print_trans: syntax -> unit
    val print_syntax: syntax -> unit
    val test_read: syntax -> string -> string -> unit
    val read: syntax -> typ -> string -> term
    val read_typ: syntax -> (indexname -> sort) -> string -> typ
    val simple_read_typ: string -> typ
    val pretty_term: syntax -> term -> Pretty.T
    val pretty_typ: syntax -> typ -> Pretty.T
    val string_of_term: syntax -> term -> string
    val string_of_typ: syntax -> typ -> string
    val simple_string_of_typ: typ -> string
    val simple_pprint_typ: typ -> pprint_args -> unit

end;

functor SyntaxFun(structure Symtab: SYMTAB and TypeExt: TYPE_EXT
  and SExtension: SEXTENSION and Mixfix: MIXFIX and Printer: PRINTER
  sharing Mixfix.SynExt = SExtension.Parser.SynExt = TypeExt.SynExt = Printer.SynExt)
  : SYNTAX =
struct

structure SynExt = TypeExt.SynExt;
structure Parser = SExtension.Parser;
structure Lexicon = Parser.Lexicon;
structure Mixfix = Mixfix;
open Lexicon SynExt SynExt.Ast Parser TypeExt SExtension Printer;


(** tables of translation functions **)

(*the ref serves as unique id*)
type 'a trtab = (('a list -> 'a) * unit ref) Symtab.table;

val dest_trtab = Symtab.dest;

fun lookup_trtab tab c =
  apsome fst (Symtab.lookup (tab, c));


(* empty, extend, merge trtabs *)

fun err_dup_trfuns name cs =
  error ("More than one " ^ name ^ " for " ^ commas_quote cs);

val empty_trtab = Symtab.null;

fun extend_trtab tab trfuns name =
  Symtab.extend_new (tab, map (fn (c, f) => (c, (f, ref ()))) trfuns)
    handle Symtab.DUPS cs => err_dup_trfuns name cs;

fun merge_trtabs tab1 tab2 name =
  Symtab.merge eq_snd (tab1, tab2)
    handle Symtab.DUPS cs => err_dup_trfuns name cs;



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
    roots: string list,
    gram: gram,
    consts: string list,
    parse_ast_trtab: ast trtab,
    parse_ruletab: ruletab,
    parse_trtab: term trtab,
    print_trtab: term trtab,
    print_ruletab: ruletab,
    print_ast_trtab: ast trtab,
    prtab: prtab};


(* empty_syntax *)

val empty_syntax =
  Syntax {
    lexicon = empty_lexicon,
    roots = [],
    gram = empty_gram,
    consts = [],
    parse_ast_trtab = empty_trtab,
    parse_ruletab = empty_ruletab,
    parse_trtab = empty_trtab,
    print_trtab = empty_trtab,
    print_ruletab = empty_ruletab,
    print_ast_trtab = empty_trtab,
    prtab = empty_prtab};


(* extend_syntax *)

fun extend_syntax (Syntax tabs) syn_ext =
  let
    val {lexicon, roots = roots1, gram, consts = consts1, parse_ast_trtab,
      parse_ruletab, parse_trtab, print_trtab, print_ruletab, print_ast_trtab,
      prtab} = tabs;
    val SynExt {roots = roots2, xprods, consts = consts2, parse_ast_translation,
      parse_rules, parse_translation, print_translation, print_rules,
      print_ast_translation} = syn_ext;
  in
    Syntax {
      lexicon = extend_lexicon lexicon (delims_of xprods),
      roots = extend_list roots1 roots2,
      gram = extend_gram gram roots2 xprods,
      consts = consts2 union consts1,
      parse_ast_trtab =
        extend_trtab parse_ast_trtab parse_ast_translation "parse ast translation",
      parse_ruletab = extend_ruletab parse_ruletab parse_rules,
      parse_trtab = extend_trtab parse_trtab parse_translation "parse translation",
      print_trtab = extend_trtab print_trtab print_translation "print translation",
      print_ruletab = extend_ruletab print_ruletab print_rules,
      print_ast_trtab =
        extend_trtab print_ast_trtab print_ast_translation "print ast translation",
      prtab = extend_prtab prtab xprods}
  end;


(* merge_syntaxes *)

fun merge_syntaxes (Syntax tabs1) (Syntax tabs2) =
  let
    val {lexicon = lexicon1, roots = roots1, gram = gram1, consts = consts1,
      parse_ast_trtab = parse_ast_trtab1, parse_ruletab = parse_ruletab1,
      parse_trtab = parse_trtab1, print_trtab = print_trtab1,
      print_ruletab = print_ruletab1, print_ast_trtab = print_ast_trtab1,
      prtab = prtab1} = tabs1;

    val {lexicon = lexicon2, roots = roots2, gram = gram2, consts = consts2,
      parse_ast_trtab = parse_ast_trtab2, parse_ruletab = parse_ruletab2,
      parse_trtab = parse_trtab2, print_trtab = print_trtab2,
      print_ruletab = print_ruletab2, print_ast_trtab = print_ast_trtab2,
      prtab = prtab2} = tabs2;
  in
    Syntax {
      lexicon = merge_lexicons lexicon1 lexicon2,
      roots = merge_lists roots1 roots2,
      gram = merge_grams gram1 gram2,
      consts = merge_lists consts1 consts2,
      parse_ast_trtab =
        merge_trtabs parse_ast_trtab1 parse_ast_trtab2 "parse ast translation",
      parse_ruletab = merge_ruletabs parse_ruletab1 parse_ruletab2,
      parse_trtab = merge_trtabs parse_trtab1 parse_trtab2 "parse translation",
      print_trtab = merge_trtabs print_trtab1 print_trtab2 "print translation",
      print_ruletab = merge_ruletabs print_ruletab1 print_ruletab2,
      print_ast_trtab =
        merge_trtabs print_ast_trtab1 print_ast_trtab2 "print ast translation",
      prtab = merge_prtabs prtab1 prtab2}
  end;


(* type_syn *)

val type_syn = extend_syntax empty_syntax type_ext;



(** inspect syntax **)

fun pretty_strs_qs name strs =
  Pretty.strs (name :: map quote (sort_strings strs));


(* print_gram *)

fun print_gram (Syntax tabs) =
  let
    val {lexicon, roots, gram, ...} = tabs;
  in
    Pretty.writeln (pretty_strs_qs "lexicon:" (dest_lexicon lexicon));
    Pretty.writeln (Pretty.strs ("roots:" :: roots));
    Pretty.writeln (Pretty.big_list "prods:" (pretty_gram gram))
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

    val toks = tokenize lexicon false str;
    val _ = writeln ("tokens: " ^ space_implode " " (map display_token toks))

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

fun read_ast (Syntax tabs) xids root str =
  let
    val {lexicon, gram, parse_ast_trtab, ...} = tabs;
    val pts = parse gram root (tokenize lexicon xids str);

    fun show_pt pt =
      writeln (str_of_ast (pt_to_ast (K None) pt));
  in
    (case pts of
      [pt] => pt_to_ast (lookup_trtab parse_ast_trtab) pt
    | _ =>
      (writeln ("Ambiguous input " ^ quote str);
       writeln "produces the following parse trees:"; seq show_pt pts;
       error "Please disambiguate the grammar or your input."))
  end;


(* read *)

fun read (syn as Syntax tabs) ty str =
  let
    val {parse_ruletab, parse_trtab, ...} = tabs;
    val ast = read_ast syn false (typ_to_nonterm ty) str;
  in
    ast_to_term (lookup_trtab parse_trtab)
      (normalize_ast (lookup_ruletab parse_ruletab) ast)
  end;


(* read types *)

fun read_typ syn def_sort str =
  typ_of_term def_sort (read syn typeT str);

fun simple_read_typ str = read_typ type_syn (K []) str;


(* read rules *)

fun read_rule syn (xrule as ((_, lhs_src), (_, rhs_src))) =
  let
    val Syntax {consts, ...} = syn;

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

fun pretty_t t_to_ast pretty_t (syn as Syntax tabs) t =
  let
    val {print_trtab, print_ruletab, print_ast_trtab, prtab, ...} = tabs;
    val ast = t_to_ast (lookup_trtab print_trtab) t;
  in
    pretty_t prtab (lookup_trtab print_ast_trtab)
      (normalize_ast (lookup_ruletab print_ruletab) ast)
  end;

val pretty_term = pretty_t term_to_ast pretty_term_ast;
val pretty_typ = pretty_t typ_to_ast pretty_typ_ast;

fun string_of_term syn t = Pretty.string_of (pretty_term syn t);
fun string_of_typ syn ty = Pretty.string_of (pretty_typ syn ty);

val simple_string_of_typ = string_of_typ type_syn;
val simple_pprint_typ = Pretty.pprint o Pretty.quote o (pretty_typ type_syn);



(** extend syntax (external interfaces) **)

(* FIXME -> syn_ext.ML *)
fun syn_ext_const_names roots cs =
  syn_ext roots [] [] cs ([], [], [], []) ([], []);

(* FIXME -> syn_ext.ML *)
fun syn_ext_trfuns roots trfuns =
  syn_ext roots [] [] [] trfuns ([], []);


fun ext_syntax mk_syn_ext (syn as Syntax {roots, ...}) decls =
  extend_syntax syn (mk_syn_ext roots decls);


fun extend_log_types (syn as Syntax {roots, ...}) all_roots =
  extend_syntax syn (syn_ext_roots all_roots (all_roots \\ roots));

val extend_type_gram = ext_syntax Mixfix.syn_ext_types;

val extend_const_gram = ext_syntax Mixfix.syn_ext_consts;

val extend_consts = ext_syntax syn_ext_const_names;

val extend_trfuns = ext_syntax syn_ext_trfuns;

fun extend_trrules syn xrules =
  ext_syntax syn_ext_rules syn (read_xrules syn xrules);


(* extend *)    (* FIXME remove *)

fun extend syn0 read_ty (all_roots, xconsts, sext) =
  let
    val Syntax {roots, ...} = syn0;

    val syn1 = extend_syntax syn0
      (syn_ext_of_sext all_roots (all_roots \\ roots) xconsts read_ty sext);

    val syn2 = extend_syntax syn1
      (syn_ext_rules all_roots (read_xrules syn1 (xrules_of sext)));
  in syn2 end;


end;

