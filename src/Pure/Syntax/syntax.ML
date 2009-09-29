(*  Title:      Pure/Syntax/syntax.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Standard Isabelle syntax, based on arbitrary context-free grammars
(specified by mixfix declarations).
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
  type syntax
  val eq_syntax: syntax * syntax -> bool
  val is_keyword: syntax -> string -> bool
  type mode
  val mode_default: mode
  val mode_input: mode
  val merge_syntaxes: syntax -> syntax -> syntax
  val basic_syn: syntax
  val basic_nonterms: string list
  val print_gram: syntax -> unit
  val print_trans: syntax -> unit
  val print_syntax: syntax -> unit
  val guess_infix: syntax -> string -> mixfix option
  val read_token: string -> Symbol_Pos.T list * Position.T
  val ambiguity_is_error: bool Unsynchronized.ref
  val ambiguity_level: int Unsynchronized.ref
  val ambiguity_limit: int Unsynchronized.ref
  val standard_parse_term: Pretty.pp -> (term -> string option) ->
    (((string * int) * sort) list -> string * int -> Term.sort) ->
    (string -> bool * string) -> (string -> string option) ->
    (typ -> typ) -> (sort -> sort) -> Proof.context ->
    (string -> bool) -> syntax -> typ -> Symbol_Pos.T list * Position.T -> term
  val standard_parse_typ: Proof.context -> syntax ->
    ((indexname * sort) list -> indexname -> sort) -> (sort -> sort) ->
    Symbol_Pos.T list * Position.T -> typ
  val standard_parse_sort: Proof.context -> syntax -> (sort -> sort) ->
    Symbol_Pos.T list * Position.T -> sort
  datatype 'a trrule =
    ParseRule of 'a * 'a |
    PrintRule of 'a * 'a |
    ParsePrintRule of 'a * 'a
  val map_trrule: ('a -> 'b) -> 'a trrule -> 'b trrule
  val standard_unparse_term: (string -> xstring) ->
    Proof.context -> syntax -> bool -> term -> Pretty.T
  val standard_unparse_typ: Proof.context -> syntax -> typ -> Pretty.T
  val standard_unparse_sort: Proof.context -> syntax -> sort -> Pretty.T
  val update_type_gram: (string * int * mixfix) list -> syntax -> syntax
  val update_consts: string list -> syntax -> syntax
  val update_trfuns:
    (string * ((ast list -> ast) * stamp)) list *
    (string * ((term list -> term) * stamp)) list *
    (string * ((bool -> typ -> term list -> term) * stamp)) list *
    (string * ((ast list -> ast) * stamp)) list -> syntax -> syntax
  val update_advanced_trfuns:
    (string * ((Proof.context -> ast list -> ast) * stamp)) list *
    (string * ((Proof.context -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> bool -> typ -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> ast list -> ast) * stamp)) list -> syntax -> syntax
  val extend_tokentrfuns: (string * string * (Proof.context -> string -> Pretty.T)) list ->
    syntax -> syntax
  val update_const_gram: (string -> bool) ->
    mode -> (string * typ * mixfix) list -> syntax -> syntax
  val remove_const_gram: (string -> bool) ->
    mode -> (string * typ * mixfix) list -> syntax -> syntax
  val update_trrules: Proof.context -> (string -> bool) -> syntax ->
    (string * string) trrule list -> syntax -> syntax
  val remove_trrules: Proof.context -> (string -> bool) -> syntax ->
    (string * string) trrule list -> syntax -> syntax
  val update_trrules_i: ast trrule list -> syntax -> syntax
  val remove_trrules_i: ast trrule list -> syntax -> syntax
  val parse_token: Markup.T -> string -> Symbol_Pos.T list * Position.T
  val parse_sort: Proof.context -> string -> sort
  val parse_typ: Proof.context -> string -> typ
  val parse_term: Proof.context -> string -> term
  val parse_prop: Proof.context -> string -> term
  val unparse_sort: Proof.context -> sort -> Pretty.T
  val unparse_classrel: Proof.context -> class list -> Pretty.T
  val unparse_arity: Proof.context -> arity -> Pretty.T
  val unparse_typ: Proof.context -> typ -> Pretty.T
  val unparse_term: Proof.context -> term -> Pretty.T
  val install_operations:
   {parse_sort: Proof.context -> string -> sort,
    parse_typ: Proof.context -> string -> typ,
    parse_term: Proof.context -> string -> term,
    parse_prop: Proof.context -> string -> term,
    unparse_sort: Proof.context -> sort -> Pretty.T,
    unparse_typ: Proof.context -> typ -> Pretty.T,
    unparse_term: Proof.context -> term -> Pretty.T} -> unit
  val print_checks: Proof.context -> unit
  val add_typ_check: int -> string ->
    (typ list -> Proof.context -> (typ list * Proof.context) option) ->
    Context.generic -> Context.generic
  val add_term_check: int -> string ->
    (term list -> Proof.context -> (term list * Proof.context) option) ->
    Context.generic -> Context.generic
  val add_typ_uncheck: int -> string ->
    (typ list -> Proof.context -> (typ list * Proof.context) option) ->
    Context.generic -> Context.generic
  val add_term_uncheck: int -> string ->
    (term list -> Proof.context -> (term list * Proof.context) option) ->
    Context.generic -> Context.generic
  val check_sort: Proof.context -> sort -> sort
  val check_typ: Proof.context -> typ -> typ
  val check_term: Proof.context -> term -> term
  val check_prop: Proof.context -> term -> term
  val check_typs: Proof.context -> typ list -> typ list
  val check_terms: Proof.context -> term list -> term list
  val check_props: Proof.context -> term list -> term list
  val uncheck_sort: Proof.context -> sort -> sort
  val uncheck_arity: Proof.context -> arity -> arity
  val uncheck_classrel: Proof.context -> class list -> class list
  val uncheck_typs: Proof.context -> typ list -> typ list
  val uncheck_terms: Proof.context -> term list -> term list
  val read_sort: Proof.context -> string -> sort
  val read_typ: Proof.context -> string -> typ
  val read_term: Proof.context -> string -> term
  val read_prop: Proof.context -> string -> term
  val read_terms: Proof.context -> string list -> term list
  val read_props: Proof.context -> string list -> term list
  val read_sort_global: theory -> string -> sort
  val read_typ_global: theory -> string -> typ
  val read_term_global: theory -> string -> term
  val read_prop_global: theory -> string -> term
  val pretty_term: Proof.context -> term -> Pretty.T
  val pretty_typ: Proof.context -> typ -> Pretty.T
  val pretty_sort: Proof.context -> sort -> Pretty.T
  val pretty_classrel: Proof.context -> class list -> Pretty.T
  val pretty_arity: Proof.context -> arity -> Pretty.T
  val string_of_term: Proof.context -> term -> string
  val string_of_typ: Proof.context -> typ -> string
  val string_of_sort: Proof.context -> sort -> string
  val string_of_classrel: Proof.context -> class list -> string
  val string_of_arity: Proof.context -> arity -> string
  val is_pretty_global: Proof.context -> bool
  val set_pretty_global: bool -> Proof.context -> Proof.context
  val init_pretty_global: theory -> Proof.context
  val pretty_term_global: theory -> term -> Pretty.T
  val pretty_typ_global: theory -> typ -> Pretty.T
  val pretty_sort_global: theory -> sort -> Pretty.T
  val string_of_term_global: theory -> term -> string
  val string_of_typ_global: theory -> typ -> string
  val string_of_sort_global: theory -> sort -> string
  val pp: Proof.context -> Pretty.pp
  val pp_global: theory -> Pretty.pp
end;

structure Syntax: SYNTAX =
struct

(** tables of translation functions **)

(* parse (ast) translations *)

fun lookup_tr tab c = Option.map fst (Symtab.lookup tab c);

fun err_dup_trfun name c =
  error ("More than one " ^ name ^ " for " ^ quote c);

fun remove_trtab trfuns = fold (Symtab.remove SynExt.eq_trfun) trfuns;

fun update_trtab name trfuns tab = fold Symtab.update_new trfuns (remove_trtab trfuns tab)
  handle Symtab.DUP c => err_dup_trfun name c;

fun merge_trtabs name tab1 tab2 = Symtab.merge SynExt.eq_trfun (tab1, tab2)
  handle Symtab.DUP c => err_dup_trfun name c;


(* print (ast) translations *)

fun lookup_tr' tab c = map fst (Symtab.lookup_list tab c);
fun update_tr'tab trfuns = fold_rev (Symtab.update_list SynExt.eq_trfun) trfuns;
fun remove_tr'tab trfuns = fold (Symtab.remove_list SynExt.eq_trfun) trfuns;
fun merge_tr'tabs tab1 tab2 = Symtab.merge_list SynExt.eq_trfun (tab1, tab2);



(** tables of token translation functions **)

fun lookup_tokentr tabs modes =
  let val trs = distinct (eq_fst (op =)) (maps (these o AList.lookup (op =) tabs) (modes @ [""]))
  in fn c => Option.map fst (AList.lookup (op =) trs c) end;

fun merge_tokentrtabs tabs1 tabs2 =
  let
    fun eq_tr ((c1, (_, s1)), (c2, (_, s2))) = c1 = c2 andalso s1 = s2;

    fun name (s, _) = implode (tl (Symbol.explode s));

    fun merge mode =
      let
        val trs1 = these (AList.lookup (op =) tabs1 mode);
        val trs2 = these (AList.lookup (op =) tabs2 mode);
        val trs = distinct eq_tr (trs1 @ trs2);
      in
        (case duplicates (eq_fst (op =)) trs of
          [] => (mode, trs)
        | dups => error ("More than one token translation function in mode " ^
            quote mode ^ " for " ^ commas_quote (map name dups)))
      end;
  in map merge (distinct (op =) (map fst (tabs1 @ tabs2))) end;

fun extend_tokentrtab tokentrs tabs =
  let
    fun ins_tokentr (m, c, f) =
      AList.default (op =) (m, [])
      #> AList.map_entry (op =) m (cons ("_" ^ c, (f, stamp ())));
  in merge_tokentrtabs tabs (fold ins_tokentr tokentrs []) end;



(** tables of translation rules **)

type ruletab = (Ast.ast * Ast.ast) list Symtab.table;

fun dest_ruletab tab = maps snd (Symtab.dest tab);


(* empty, update, merge ruletabs *)

val update_ruletab = fold_rev (fn r => Symtab.update_list (op =) (Ast.head_of_rule r, r));
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
    parse_ast_trtab: ((Proof.context -> Ast.ast list -> Ast.ast) * stamp) Symtab.table,
    parse_ruletab: ruletab,
    parse_trtab: ((Proof.context -> term list -> term) * stamp) Symtab.table,
    print_trtab: ((Proof.context -> bool -> typ -> term list -> term) * stamp) list Symtab.table,
    print_ruletab: ruletab,
    print_ast_trtab: ((Proof.context -> Ast.ast list -> Ast.ast) * stamp) list Symtab.table,
    tokentrtab: (string * (string * ((Proof.context -> string -> Pretty.T) * stamp)) list) list,
    prtabs: Printer.prtabs} * stamp;

fun eq_syntax (Syntax (_, s1), Syntax (_, s2)) = s1 = s2;

fun is_keyword (Syntax ({lexicon, ...}, _)) = Scan.is_literal lexicon o Symbol.explode;

type mode = string * bool;
val mode_default = ("", true);
val mode_input = (PrintMode.input, true);


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


(* update_syntax *)

fun update_syntax (mode, inout) syn_ext (Syntax (tabs, _)) =
  let
    val {input, lexicon, gram, consts = consts1, prmodes = prmodes1,
      parse_ast_trtab, parse_ruletab, parse_trtab, print_trtab, print_ruletab,
      print_ast_trtab, tokentrtab, prtabs} = tabs;
    val SynExt.SynExt {xprods, consts = consts2, prmodes = prmodes2,
      parse_ast_translation, parse_rules, parse_translation, print_translation, print_rules,
      print_ast_translation, token_translation} = syn_ext;
    val input' = if inout then fold (insert (op =)) xprods input else input;
    val changed = length input <> length input';
    fun if_inout xs = if inout then xs else [];
  in
    Syntax
    ({input = input',
      lexicon =
        if changed then fold Scan.extend_lexicon (SynExt.delims_of xprods) lexicon else lexicon,
      gram = if changed then Parser.extend_gram gram xprods else gram,
      consts = Library.merge (op =) (consts1, filter_out Long_Name.is_qualified consts2),
      prmodes = insert (op =) mode (Library.merge (op =) (prmodes1, prmodes2)),
      parse_ast_trtab =
        update_trtab "parse ast translation" (if_inout parse_ast_translation) parse_ast_trtab,
      parse_ruletab = update_ruletab (if_inout parse_rules) parse_ruletab,
      parse_trtab = update_trtab "parse translation" (if_inout parse_translation) parse_trtab,
      print_trtab = update_tr'tab print_translation print_trtab,
      print_ruletab = update_ruletab print_rules print_ruletab,
      print_ast_trtab = update_tr'tab print_ast_translation print_ast_trtab,
      tokentrtab = extend_tokentrtab token_translation tokentrtab,
      prtabs = Printer.update_prtabs mode xprods prtabs}, stamp ())
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
    val input' = if inout then subtract (op =) xprods input else input;
    val changed = length input <> length input';
    fun if_inout xs = if inout then xs else [];
  in
    Syntax
    ({input = input',
      lexicon = if changed then Scan.make_lexicon (SynExt.delims_of input') else lexicon,
      gram = if changed then Parser.make_gram input' else gram,
      consts = consts,
      prmodes = prmodes,
      parse_ast_trtab = remove_trtab (if_inout parse_ast_translation) parse_ast_trtab,
      parse_ruletab = remove_ruletab (if_inout parse_rules) parse_ruletab,
      parse_trtab = remove_trtab (if_inout parse_translation) parse_trtab,
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
      lexicon = Scan.merge_lexicons (lexicon1, lexicon2),
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
  |> update_syntax mode_default TypeExt.type_ext
  |> update_syntax mode_default SynExt.pure_ext;

val basic_nonterms =
  (Lexicon.terminals @ [SynExt.logic, "type", "types", "sort", "classes",
    SynExt.args, SynExt.cargs, "pttrn", "pttrns", "idt", "idts", "aprop",
    "asms", SynExt.any, SynExt.sprop, "num_const", "float_const",
    "index", "struct"]);



(** print syntax **)

local

fun pretty_strs_qs name strs =
  Pretty.strs (name :: map quote (sort_strings strs));

fun pretty_gram (Syntax (tabs, _)) =
  let
    val {lexicon, prmodes, gram, prtabs, ...} = tabs;
    val prmodes' = sort_strings (filter_out (fn s => s = "") prmodes);
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

    fun pretty_tokentr (mode, trs) = Pretty.strs (quote mode ^ ":" :: map fst trs);

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


(* reconstructing infixes -- educated guessing *)

fun guess_infix (Syntax ({gram, ...}, _)) c =
  (case Parser.guess_infix_lr gram c of
    SOME (s, l, r, j) => SOME
     (if l then Mixfix.InfixlName (s, j)
      else if r then Mixfix.InfixrName (s, j)
      else Mixfix.InfixName (s, j))
  | NONE => NONE);



(** read **)

(* read token -- with optional YXML encoding of position *)

fun read_token str =
  let val (text, pos) =
    (case YXML.parse str handle Fail msg => error msg of
      XML.Elem ("token", props, [XML.Text text]) => (text, Position.of_properties props)
    | XML.Elem ("token", props, []) => ("", Position.of_properties props)
    | XML.Text text => (text, Position.none)
    | _ => (str, Position.none))
  in (Symbol_Pos.explode (text, pos), pos) end;


(* read_ast *)

val ambiguity_is_error = Unsynchronized.ref false;
val ambiguity_level = Unsynchronized.ref 1;
val ambiguity_limit = Unsynchronized.ref 10;

fun ambiguity_msg pos = "Parse error: ambiguous syntax" ^ Position.str_of pos;

fun read_asts ctxt is_logtype (Syntax (tabs, _)) xids root (syms, pos) =
  let
    val {lexicon, gram, parse_ast_trtab, ...} = tabs;
    val toks = Lexicon.tokenize lexicon xids syms;
    val _ = List.app Lexicon.report_token toks;

    val root' = if root <> "prop" andalso is_logtype root then SynExt.logic else root;
    val pts = Parser.parse gram root' (filter Lexicon.is_proper toks);
    val len = length pts;

    val limit = ! ambiguity_limit;
    fun show_pt pt =
      Pretty.string_of (Ast.pretty_ast (hd (SynTrans.pts_to_asts ctxt (K NONE) [pt])));
  in
    if len <= ! ambiguity_level then ()
    else if ! ambiguity_is_error then error (ambiguity_msg pos)
    else
      (warning (cat_lines
        (("Ambiguous input " ^ Position.str_of pos ^
          "\nproduces " ^ string_of_int len ^ " parse trees" ^
          (if len <= limit then "" else " (" ^ string_of_int limit ^ " displayed)") ^ ":") ::
          map show_pt (Library.take (limit, pts)))));
    SynTrans.pts_to_asts ctxt (lookup_tr parse_ast_trtab) pts
  end;


(* read *)

fun read ctxt is_logtype (syn as Syntax (tabs, _)) ty inp =
  let
    val {parse_ruletab, parse_trtab, ...} = tabs;
    val asts = read_asts ctxt is_logtype syn false (SynExt.typ_to_nonterm ty) inp;
  in
    SynTrans.asts_to_terms ctxt (lookup_tr parse_trtab)
      (map (Ast.normalize_ast (Symtab.lookup_list parse_ruletab)) asts)
  end;


(* read terms *)

(*brute-force disambiguation via type-inference*)
fun disambig _ _ [t] = t
  | disambig pp check ts =
      let
        val level = ! ambiguity_level;
        val limit = ! ambiguity_limit;

        val ambiguity = length ts;
        fun ambig_msg () =
          if ambiguity > 1 andalso ambiguity <= level then
            "Got more than one parse tree.\n\
            \Retry with smaller Syntax.ambiguity_level for more information."
          else "";

        val errs = map check ts;
        val results = map_filter (fn (t, NONE) => SOME t | _ => NONE) (ts ~~ errs);
        val len = length results;
      in
        if null results then cat_error (ambig_msg ()) (cat_lines (map_filter I errs))
        else if len = 1 then
          (if ambiguity > level then
            warning "Fortunately, only one parse tree is type correct.\n\
              \You may still want to disambiguate your grammar or your input."
          else (); hd results)
        else cat_error (ambig_msg ()) (cat_lines
          (("Ambiguous input, " ^ string_of_int len ^ " terms are type correct" ^
            (if len <= limit then "" else " (" ^ string_of_int limit ^ " displayed)") ^ ":") ::
            map (Pretty.string_of_term pp) (Library.take (limit, results))))
      end;

fun standard_parse_term pp check get_sort map_const map_free map_type map_sort
    ctxt is_logtype syn ty (syms, pos) =
  read ctxt is_logtype syn ty (syms, pos)
  |> map (TypeExt.decode_term get_sort map_const map_free map_type map_sort)
  |> disambig (Printer.pp_show_brackets pp) check;


(* read types *)

fun standard_parse_typ ctxt syn get_sort map_sort (syms, pos) =
  (case read ctxt (K false) syn SynExt.typeT (syms, pos) of
    [t] => TypeExt.typ_of_term (get_sort (TypeExt.term_sorts map_sort t)) map_sort t
  | _ => error (ambiguity_msg pos));


(* read sorts *)

fun standard_parse_sort ctxt syn map_sort (syms, pos) =
  (case read ctxt (K false) syn TypeExt.sortT (syms, pos) of
    [t] => TypeExt.sort_of_term map_sort t
  | _ => error (ambiguity_msg pos));



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


local

fun check_rule (rule as (lhs, rhs)) =
  (case Ast.rule_error rule of
    SOME msg =>
      error ("Error in syntax translation rule: " ^ msg ^ "\n" ^
        Ast.str_of_ast lhs ^ "  ->  " ^ Ast.str_of_ast rhs)
  | NONE => rule);

fun read_pattern ctxt is_logtype syn (root, str) =
  let
    val Syntax ({consts, ...}, _) = syn;

    fun constify (ast as Ast.Constant _) = ast
      | constify (ast as Ast.Variable x) =
          if member (op =) consts x orelse Long_Name.is_qualified x then Ast.Constant x
          else ast
      | constify (Ast.Appl asts) = Ast.Appl (map constify asts);

    val (syms, pos) = read_token str;
  in
    (case read_asts ctxt is_logtype syn true root (syms, pos) of
      [ast] => constify ast
    | _ => error (ambiguity_msg pos))
  end;

fun prep_rules rd_pat raw_rules =
  let val rules = map (map_trrule rd_pat) raw_rules in
    (map check_rule (map_filter parse_rule rules),
      map check_rule (map_filter print_rule rules))
  end

in

val cert_rules = prep_rules I;

fun read_rules ctxt is_logtype syn =
  prep_rules (read_pattern ctxt is_logtype syn);

end;



(** unparse terms, typs, sorts **)

local

fun unparse_t t_to_ast prt_t markup ctxt (syn as Syntax (tabs, _)) curried t =
  let
    val {print_trtab, print_ruletab, print_ast_trtab, tokentrtab, prtabs, ...} = tabs;
    val ast = t_to_ast ctxt (lookup_tr' print_trtab) t;
  in
    Pretty.markup markup (prt_t ctxt curried prtabs (lookup_tr' print_ast_trtab)
      (lookup_tokentr tokentrtab (print_mode_value ()))
      (Ast.normalize_ast (Symtab.lookup_list print_ruletab) ast))
  end;

in

fun standard_unparse_term extern =
  unparse_t Printer.term_to_ast (Printer.pretty_term_ast extern) Markup.term;

fun standard_unparse_typ ctxt syn =
  unparse_t Printer.typ_to_ast Printer.pretty_typ_ast Markup.typ ctxt syn false;

fun standard_unparse_sort ctxt syn =
  unparse_t Printer.sort_to_ast Printer.pretty_typ_ast Markup.sort ctxt syn false;

end;



(** modify syntax **)

fun ext_syntax f decls = update_syntax mode_default (f decls);

val update_type_gram       = ext_syntax Mixfix.syn_ext_types;
val update_consts          = ext_syntax SynExt.syn_ext_const_names;
val update_trfuns          = ext_syntax SynExt.syn_ext_trfuns;
val update_advanced_trfuns = ext_syntax SynExt.syn_ext_advanced_trfuns;
val extend_tokentrfuns     = ext_syntax SynExt.syn_ext_tokentrfuns;

fun update_const_gram is_logtype prmode decls =
  update_syntax prmode (Mixfix.syn_ext_consts is_logtype decls);

fun remove_const_gram is_logtype prmode decls =
  remove_syntax prmode (Mixfix.syn_ext_consts is_logtype decls);

fun update_trrules ctxt is_logtype syn =
  ext_syntax SynExt.syn_ext_rules o read_rules ctxt is_logtype syn;

fun remove_trrules ctxt is_logtype syn =
  remove_syntax mode_default o SynExt.syn_ext_rules o read_rules ctxt is_logtype syn;

val update_trrules_i = ext_syntax SynExt.syn_ext_rules o cert_rules;
val remove_trrules_i = remove_syntax mode_default o SynExt.syn_ext_rules o cert_rules;



(** inner syntax operations **)

(* (un)parsing *)

fun parse_token markup str =
  let
    val (syms, pos) = read_token str;
    val _ = Position.report markup pos;
  in (syms, pos) end;

local
  type operations =
   {parse_sort: Proof.context -> string -> sort,
    parse_typ: Proof.context -> string -> typ,
    parse_term: Proof.context -> string -> term,
    parse_prop: Proof.context -> string -> term,
    unparse_sort: Proof.context -> sort -> Pretty.T,
    unparse_typ: Proof.context -> typ -> Pretty.T,
    unparse_term: Proof.context -> term -> Pretty.T};

  val operations = Unsynchronized.ref (NONE: operations option);

  fun operation which ctxt x =
    (case ! operations of
      NONE => error "Inner syntax operations not yet installed"
    | SOME ops => which ops ctxt x);
in

val parse_sort = operation #parse_sort;
val parse_typ = operation #parse_typ;
val parse_term = operation #parse_term;
val parse_prop = operation #parse_prop;
val unparse_sort = operation #unparse_sort;
val unparse_typ = operation #unparse_typ;
val unparse_term = operation #unparse_term;

fun install_operations ops = CRITICAL (fn () =>
  if is_some (! operations) then error "Inner syntax operations already installed"
  else operations := SOME ops);

end;


(* context-sensitive (un)checking *)

local

type key = int * bool;
type 'a check = 'a list -> Proof.context -> ('a list * Proof.context) option;

structure Checks = GenericDataFun
(
  type T =
    ((key * ((string * typ check) * stamp) list) list *
     (key * ((string * term check) * stamp) list) list);
  val empty = ([], []);
  val extend = I;
  fun merge _ ((typ_checks1, term_checks1), (typ_checks2, term_checks2)) : T =
    (AList.join (op =) (K (Library.merge (eq_snd (op =)))) (typ_checks1, typ_checks2),
     AList.join (op =) (K (Library.merge (eq_snd (op =)))) (term_checks1, term_checks2));
);

fun gen_add which (key: key) name f =
  Checks.map (which (AList.map_default op = (key, []) (cons ((name, f), stamp ()))));

fun check_stage fs = perhaps_loop (perhaps_apply (map uncurry fs));

fun gen_check which uncheck ctxt0 xs0 =
  let
    val funs = which (Checks.get (Context.Proof ctxt0))
      |> map_filter (fn ((i, u), fs) => if uncheck = u then SOME (i, map (snd o fst) fs) else NONE)
      |> Library.sort (int_ord o pairself fst) |> map snd
      |> not uncheck ? map rev;
    val check_all = perhaps_apply (map check_stage funs);
  in #1 (perhaps check_all (xs0, ctxt0)) end;

fun map_sort f S =
  (case f (TFree ("", S)) of
    TFree ("", S') => S'
  | _ => raise TYPE ("map_sort", [TFree ("", S)], []));

in

fun print_checks ctxt =
  let
    fun split_checks checks =
      List.partition (fn ((_, un), _) => not un) checks
      |> pairself (map (fn ((i, _), fs) => (i, map (fst o fst) fs))
          #> sort (int_ord o pairself fst));
    fun pretty_checks kind checks =
      checks |> map (fn (i, names) => Pretty.block
        [Pretty.str (kind ^ " (stage " ^ signed_string_of_int i ^ "):"),
          Pretty.brk 1, Pretty.strs names]);

    val (typs, terms) = Checks.get (Context.Proof ctxt);
    val (typ_checks, typ_unchecks) = split_checks typs;
    val (term_checks, term_unchecks) = split_checks terms;
  in
    pretty_checks "typ_checks" typ_checks @
    pretty_checks "term_checks" term_checks @
    pretty_checks "typ_unchecks" typ_unchecks @
    pretty_checks "term_unchecks" term_unchecks
  end |> Pretty.chunks |> Pretty.writeln;

fun add_typ_check stage = gen_add apfst (stage, false);
fun add_term_check stage = gen_add apsnd (stage, false);
fun add_typ_uncheck stage = gen_add apfst (stage, true);
fun add_term_uncheck stage = gen_add apsnd (stage, true);

val check_typs = gen_check fst false;
val check_terms = gen_check snd false;
fun check_props ctxt = map (TypeExt.type_constraint propT) #> check_terms ctxt;

val check_typ = singleton o check_typs;
val check_term = singleton o check_terms;
val check_prop = singleton o check_props;
val check_sort = map_sort o check_typ;

val uncheck_typs = gen_check fst true;
val uncheck_terms = gen_check snd true;
val uncheck_sort = map_sort o singleton o uncheck_typs;

end;


(* derived operations for classrel and arity *)

val uncheck_classrel = map o singleton o uncheck_sort;

fun unparse_classrel ctxt cs = Pretty.block (flat
  (separate [Pretty.str " <", Pretty.brk 1] (map (single o unparse_sort ctxt o single) cs)));

fun uncheck_arity ctxt (a, Ss, S) =
  let
    val T = Type (a, replicate (length Ss) dummyT);
    val a' =
      (case singleton (uncheck_typs ctxt) T of
        Type (a', _) => a'
      | T => raise TYPE ("uncheck_arity", [T], []));
    val Ss' = map (uncheck_sort ctxt) Ss;
    val S' = uncheck_sort ctxt S;
  in (a', Ss', S') end;

fun unparse_arity ctxt (a, Ss, S) =
  let
    val prtT = unparse_typ ctxt (Type (a, []));
    val dom =
      if null Ss then []
      else [Pretty.list "(" ")" (map (unparse_sort ctxt) Ss), Pretty.brk 1];
  in Pretty.block ([prtT, Pretty.str " ::", Pretty.brk 1] @ dom @ [unparse_sort ctxt S]) end;


(* read = parse + check *)

fun read_sort ctxt = parse_sort ctxt #> check_sort ctxt;
fun read_typ ctxt = parse_typ ctxt #> singleton (check_typs ctxt);

fun read_terms ctxt = map (parse_term ctxt) #> check_terms ctxt;
fun read_props ctxt = map (parse_prop ctxt) #> check_props ctxt;

val read_term = singleton o read_terms;
val read_prop = singleton o read_props;

val read_sort_global = read_sort o ProofContext.init;
val read_typ_global = read_typ o ProofContext.init;
val read_term_global = read_term o ProofContext.init;
val read_prop_global = read_prop o ProofContext.init;


(* pretty = uncheck + unparse *)

fun pretty_term ctxt = singleton (uncheck_terms ctxt) #> unparse_term ctxt;
fun pretty_typ ctxt = singleton (uncheck_typs ctxt) #> unparse_typ ctxt;
fun pretty_sort ctxt = uncheck_sort ctxt #> unparse_sort ctxt;
fun pretty_classrel ctxt = uncheck_classrel ctxt #> unparse_classrel ctxt;
fun pretty_arity ctxt = uncheck_arity ctxt #> unparse_arity ctxt;

val string_of_term = Pretty.string_of oo pretty_term;
val string_of_typ = Pretty.string_of oo pretty_typ;
val string_of_sort = Pretty.string_of oo pretty_sort;
val string_of_classrel = Pretty.string_of oo pretty_classrel;
val string_of_arity = Pretty.string_of oo pretty_arity;


(* global pretty printing *)

structure PrettyGlobal = ProofDataFun(type T = bool fun init _ = false);
val is_pretty_global = PrettyGlobal.get;
val set_pretty_global = PrettyGlobal.put;
val init_pretty_global = set_pretty_global true o ProofContext.init;

val pretty_term_global = pretty_term o init_pretty_global;
val pretty_typ_global = pretty_typ o init_pretty_global;
val pretty_sort_global = pretty_sort o init_pretty_global;

val string_of_term_global = string_of_term o init_pretty_global;
val string_of_typ_global = string_of_typ o init_pretty_global;
val string_of_sort_global = string_of_sort o init_pretty_global;


(* pp operations -- deferred evaluation *)

fun pp ctxt = Pretty.pp
 (fn x => pretty_term ctxt x,
  fn x => pretty_typ ctxt x,
  fn x => pretty_sort ctxt x,
  fn x => pretty_classrel ctxt x,
  fn x => pretty_arity ctxt x);

fun pp_global thy = Pretty.pp
 (fn x => pretty_term_global thy x,
  fn x => pretty_typ_global thy x,
  fn x => pretty_sort_global thy x,
  fn x => pretty_classrel (init_pretty_global thy) x,
  fn x => pretty_arity (init_pretty_global thy) x);


(*export parts of internal Syntax structures*)
open Lexicon SynExt Ast Parser TypeExt SynTrans Mixfix Printer;

end;

structure BasicSyntax: BASIC_SYNTAX = Syntax;
open BasicSyntax;

forget_structure "Ast";
forget_structure "SynExt";
forget_structure "Parser";
forget_structure "TypeExt";
forget_structure "SynTrans";
forget_structure "Mixfix";
forget_structure "Printer";
