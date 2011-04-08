(*  Title:      Pure/Syntax/syntax.ML
    Author:     Tobias Nipkow and Markus Wenzel, TU Muenchen

Standard Isabelle syntax, based on arbitrary context-free grammars
(specified by mixfix declarations).
*)

signature SYNTAX =
sig
  val max_pri: int
  val const: string -> term
  val free: string -> term
  val var: indexname -> term
  val root: string Config.T
  val positions_raw: Config.raw
  val positions: bool Config.T
  val ambiguity_enabled: bool Config.T
  val ambiguity_level_raw: Config.raw
  val ambiguity_level: int Config.T
  val ambiguity_limit: int Config.T
  val read_token: string -> Symbol_Pos.T list * Position.T
  val parse_token: Proof.context -> Markup.T -> string -> Symbol_Pos.T list * Position.T
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
  type syntax
  val eq_syntax: syntax * syntax -> bool
  val is_const: syntax -> string -> bool
  val is_keyword: syntax -> string -> bool
  val tokenize: syntax -> bool -> Symbol_Pos.T list -> Lexicon.token list
  val parse: Proof.context -> syntax -> string -> Lexicon.token list -> Parser.parsetree list
  val parse_ast_translation: syntax -> string -> (Proof.context -> Ast.ast list -> Ast.ast) option
  val parse_rules: syntax -> string -> (Ast.ast * Ast.ast) list
  val parse_translation: syntax -> string -> (Proof.context -> term list -> term) option
  val print_translation: syntax -> string ->
    Proof.context -> typ -> term list -> term  (*exception Match*)
  val print_rules: syntax -> string -> (Ast.ast * Ast.ast) list
  val print_ast_translation: syntax -> string ->
    Proof.context -> Ast.ast list -> Ast.ast  (*exception Match*)
  val prtabs: syntax -> Printer.prtabs
  type mode
  val mode_default: mode
  val mode_input: mode
  val empty_syntax: syntax
  val merge_syntaxes: syntax -> syntax -> syntax
  val token_markers: string list
  val basic_nonterms: string list
  val print_gram: syntax -> unit
  val print_trans: syntax -> unit
  val print_syntax: syntax -> unit
  val guess_infix: syntax -> string -> mixfix option
  datatype 'a trrule =
    Parse_Rule of 'a * 'a |
    Print_Rule of 'a * 'a |
    Parse_Print_Rule of 'a * 'a
  val map_trrule: ('a -> 'b) -> 'a trrule -> 'b trrule
  val update_trfuns:
    (string * ((Ast.ast list -> Ast.ast) * stamp)) list *
    (string * ((term list -> term) * stamp)) list *
    (string * ((typ -> term list -> term) * stamp)) list *
    (string * ((Ast.ast list -> Ast.ast) * stamp)) list -> syntax -> syntax
  val update_advanced_trfuns:
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list *
    (string * ((Proof.context -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> typ -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list -> syntax -> syntax
  val update_type_gram: bool -> mode -> (string * typ * mixfix) list -> syntax -> syntax
  val update_const_gram: bool -> (string -> bool) ->
    mode -> (string * typ * mixfix) list -> syntax -> syntax
  val update_trrules: Ast.ast trrule list -> syntax -> syntax
  val remove_trrules: Ast.ast trrule list -> syntax -> syntax
end;

structure Syntax: SYNTAX =
struct

val max_pri = Syntax_Ext.max_pri;

val const = Lexicon.const;
val free = Lexicon.free;
val var = Lexicon.var;



(** inner syntax operations **)

(* configuration options *)

val root = Config.string (Config.declare "syntax_root" (K (Config.String "any")));

val positions_raw = Config.declare "syntax_positions" (fn _ => Config.Bool true);
val positions = Config.bool positions_raw;

val ambiguity_enabled =
  Config.bool (Config.declare "syntax_ambiguity_enabled" (fn _ => Config.Bool true));

val ambiguity_level_raw = Config.declare "syntax_ambiguity_level" (fn _ => Config.Int 1);
val ambiguity_level = Config.int ambiguity_level_raw;

val ambiguity_limit =
  Config.int (Config.declare "syntax_ambiguity_limit" (fn _ => Config.Int 10));


(* read token -- with optional YXML encoding of position *)

fun read_token str =
  let
    val tree = YXML.parse str handle Fail msg => error msg;
    val text = XML.content_of [tree];
    val pos =
      (case tree of
        XML.Elem ((name, props), _) =>
          if name = Markup.tokenN then Position.of_properties props
          else Position.none
      | XML.Text _ => Position.none);
  in (Symbol_Pos.explode (text, pos), pos) end;


(* (un)parsing *)

fun parse_token ctxt markup str =
  let
    val (syms, pos) = read_token str;
    val _ = Context_Position.report ctxt pos markup;
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

val operations: operations Single_Assignment.var = Single_Assignment.var "Syntax.operations";

fun operation which ctxt x =
  (case Single_Assignment.peek operations of
    NONE => raise Fail "Inner syntax operations not installed"
  | SOME ops => which ops ctxt x);

in

val parse_sort = operation #parse_sort;
val parse_typ = operation #parse_typ;
val parse_term = operation #parse_term;
val parse_prop = operation #parse_prop;
val unparse_sort = operation #unparse_sort;
val unparse_typ = operation #unparse_typ;
val unparse_term = operation #unparse_term;

fun install_operations ops = Single_Assignment.assign operations ops;

end;


(* context-sensitive (un)checking *)

local

type key = int * bool;
type 'a check = 'a list -> Proof.context -> ('a list * Proof.context) option;

structure Checks = Generic_Data
(
  type T =
    ((key * ((string * typ check) * stamp) list) list *
     (key * ((string * term check) * stamp) list) list);
  val empty = ([], []);
  val extend = I;
  fun merge ((typ_checks1, term_checks1), (typ_checks2, term_checks2)) : T =
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
fun check_props ctxt = map (Type.constraint propT) #> check_terms ctxt;

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

val read_sort_global = read_sort o ProofContext.init_global;
val read_typ_global = read_typ o ProofContext.init_global;
val read_term_global = read_term o ProofContext.init_global;
val read_prop_global = read_prop o ProofContext.init_global;


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

val pretty_global = Config.bool (Config.declare "Syntax.pretty_global" (K (Config.Bool false)));
fun is_pretty_global ctxt = Config.get ctxt pretty_global;
val set_pretty_global = Config.put pretty_global;
val init_pretty_global = set_pretty_global true o ProofContext.init_global;

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



(** tables of translation functions **)

(* parse (ast) translations *)

fun err_dup_trfun name c =
  error ("More than one " ^ name ^ " for " ^ quote c);

fun lookup_tr tab c = Option.map fst (Symtab.lookup tab c);

fun remove_trtab trfuns = fold (Symtab.remove Syntax_Ext.eq_trfun) trfuns;

fun update_trtab name trfuns tab = fold Symtab.update_new trfuns (remove_trtab trfuns tab)
  handle Symtab.DUP c => err_dup_trfun name c;

fun merge_trtabs name tab1 tab2 = Symtab.merge Syntax_Ext.eq_trfun (tab1, tab2)
  handle Symtab.DUP c => err_dup_trfun name c;


(* print (ast) translations *)

fun apply_tr' tab c ctxt T args =
  let
    val fns = map fst (Symtab.lookup_list tab c);
    fun app_first [] = raise Match
      | app_first (f :: fs) = f ctxt T args handle Match => app_first fs;
  in app_first fns end;

fun apply_ast_tr' tab c ctxt args =
  let
    val fns = map fst (Symtab.lookup_list tab c);
    fun app_first [] = raise Match
      | app_first (f :: fs) = f ctxt args handle Match => app_first fs;
  in app_first fns end;

fun update_tr'tab trfuns = fold_rev (Symtab.update_list Syntax_Ext.eq_trfun) trfuns;
fun remove_tr'tab trfuns = fold (Symtab.remove_list Syntax_Ext.eq_trfun) trfuns;
fun merge_tr'tabs tab1 tab2 = Symtab.merge_list Syntax_Ext.eq_trfun (tab1, tab2);



(** tables of translation rules **)

type ruletab = (Ast.ast * Ast.ast) list Symtab.table;

fun dest_ruletab tab = maps snd (Symtab.dest tab);

val update_ruletab = fold_rev (fn r => Symtab.update_list (op =) (Ast.head_of_rule r, r));
val remove_ruletab = fold (fn r => Symtab.remove_list (op =) (Ast.head_of_rule r, r));
fun merge_ruletabs tab1 tab2 = Symtab.merge_list (op =) (tab1, tab2);



(** datatype syntax **)

datatype syntax =
  Syntax of {
    input: Syntax_Ext.xprod list,
    lexicon: Scan.lexicon,
    gram: Parser.gram,
    consts: string list,
    prmodes: string list,
    parse_ast_trtab: ((Proof.context -> Ast.ast list -> Ast.ast) * stamp) Symtab.table,
    parse_ruletab: ruletab,
    parse_trtab: ((Proof.context -> term list -> term) * stamp) Symtab.table,
    print_trtab: ((Proof.context -> typ -> term list -> term) * stamp) list Symtab.table,
    print_ruletab: ruletab,
    print_ast_trtab: ((Proof.context -> Ast.ast list -> Ast.ast) * stamp) list Symtab.table,
    prtabs: Printer.prtabs} * stamp;

fun eq_syntax (Syntax (_, s1), Syntax (_, s2)) = s1 = s2;

fun is_const (Syntax ({consts, ...}, _)) c = member (op =) consts c;
fun is_keyword (Syntax ({lexicon, ...}, _)) = Scan.is_literal lexicon o Symbol.explode;
fun tokenize (Syntax ({lexicon, ...}, _)) = Lexicon.tokenize lexicon;
fun parse ctxt (Syntax ({gram, ...}, _)) = Parser.parse ctxt gram;

fun parse_ast_translation (Syntax ({parse_ast_trtab, ...}, _)) = lookup_tr parse_ast_trtab;
fun parse_translation (Syntax ({parse_trtab, ...}, _)) = lookup_tr parse_trtab;
fun parse_rules (Syntax ({parse_ruletab, ...}, _)) = Symtab.lookup_list parse_ruletab;
fun print_translation (Syntax ({print_trtab, ...}, _)) = apply_tr' print_trtab;
fun print_rules (Syntax ({print_ruletab, ...}, _)) = Symtab.lookup_list print_ruletab;
fun print_ast_translation (Syntax ({print_ast_trtab, ...}, _)) = apply_ast_tr' print_ast_trtab;

fun prtabs (Syntax ({prtabs, ...}, _)) = prtabs;

type mode = string * bool;
val mode_default = ("", true);
val mode_input = (Print_Mode.input, true);


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
    prtabs = Printer.empty_prtabs}, stamp ());


(* update_syntax *)

fun update_syntax (mode, inout) syn_ext (Syntax (tabs, _)) =
  let
    val {input, lexicon, gram, consts = consts1, prmodes, parse_ast_trtab, parse_ruletab,
      parse_trtab, print_trtab, print_ruletab, print_ast_trtab, prtabs} = tabs;
    val Syntax_Ext.Syn_Ext {xprods, consts = consts2, parse_ast_translation,
      parse_rules, parse_translation, print_translation, print_rules,
      print_ast_translation} = syn_ext;
    val new_xprods =
      if inout then distinct (op =) (filter_out (member (op =) input) xprods) else [];
    fun if_inout xs = if inout then xs else [];
  in
    Syntax
    ({input = new_xprods @ input,
      lexicon = fold Scan.extend_lexicon (Syntax_Ext.delims_of new_xprods) lexicon,
      gram = Parser.extend_gram new_xprods gram,
      consts = Library.merge (op =) (consts1, filter_out Lexicon.is_marked consts2),
      prmodes = insert (op =) mode prmodes,
      parse_ast_trtab =
        update_trtab "parse ast translation" (if_inout parse_ast_translation) parse_ast_trtab,
      parse_ruletab = update_ruletab (if_inout parse_rules) parse_ruletab,
      parse_trtab = update_trtab "parse translation" (if_inout parse_translation) parse_trtab,
      print_trtab = update_tr'tab print_translation print_trtab,
      print_ruletab = update_ruletab print_rules print_ruletab,
      print_ast_trtab = update_tr'tab print_ast_translation print_ast_trtab,
      prtabs = Printer.update_prtabs mode xprods prtabs}, stamp ())
  end;


(* remove_syntax *)

fun remove_syntax (mode, inout) syn_ext (Syntax (tabs, _)) =
  let
    val Syntax_Ext.Syn_Ext {xprods, consts = _, parse_ast_translation, parse_rules,
      parse_translation, print_translation, print_rules, print_ast_translation} = syn_ext;
    val {input, lexicon, gram, consts, prmodes, parse_ast_trtab, parse_ruletab,
      parse_trtab, print_trtab, print_ruletab, print_ast_trtab, prtabs} = tabs;
    val input' = if inout then subtract (op =) xprods input else input;
    val changed = length input <> length input';
    fun if_inout xs = if inout then xs else [];
  in
    Syntax
    ({input = input',
      lexicon = if changed then Scan.make_lexicon (Syntax_Ext.delims_of input') else lexicon,
      gram = if changed then Parser.extend_gram input' Parser.empty_gram else gram,
      consts = consts,
      prmodes = prmodes,
      parse_ast_trtab = remove_trtab (if_inout parse_ast_translation) parse_ast_trtab,
      parse_ruletab = remove_ruletab (if_inout parse_rules) parse_ruletab,
      parse_trtab = remove_trtab (if_inout parse_translation) parse_trtab,
      print_trtab = remove_tr'tab print_translation print_trtab,
      print_ruletab = remove_ruletab print_rules print_ruletab,
      print_ast_trtab = remove_tr'tab print_ast_translation print_ast_trtab,
      prtabs = Printer.remove_prtabs mode xprods prtabs}, stamp ())
  end;


(* merge_syntaxes *)

fun merge_syntaxes (Syntax (tabs1, _)) (Syntax (tabs2, _)) =
  let
    val {input = input1, lexicon = lexicon1, gram = gram1, consts = consts1,
      prmodes = prmodes1, parse_ast_trtab = parse_ast_trtab1, parse_ruletab = parse_ruletab1,
      parse_trtab = parse_trtab1, print_trtab = print_trtab1, print_ruletab = print_ruletab1,
      print_ast_trtab = print_ast_trtab1, prtabs = prtabs1} = tabs1;

    val {input = input2, lexicon = lexicon2, gram = gram2, consts = consts2,
      prmodes = prmodes2, parse_ast_trtab = parse_ast_trtab2, parse_ruletab = parse_ruletab2,
      parse_trtab = parse_trtab2, print_trtab = print_trtab2, print_ruletab = print_ruletab2,
      print_ast_trtab = print_ast_trtab2, prtabs = prtabs2} = tabs2;
  in
    Syntax
    ({input = Library.merge (op =) (input1, input2),
      lexicon = Scan.merge_lexicons (lexicon1, lexicon2),
      gram = Parser.merge_gram (gram1, gram2),
      consts = sort_distinct string_ord (consts1 @ consts2),
      prmodes = Library.merge (op =) (prmodes1, prmodes2),
      parse_ast_trtab =
        merge_trtabs "parse ast translation" parse_ast_trtab1 parse_ast_trtab2,
      parse_ruletab = merge_ruletabs parse_ruletab1 parse_ruletab2,
      parse_trtab = merge_trtabs "parse translation" parse_trtab1 parse_trtab2,
      print_trtab = merge_tr'tabs print_trtab1 print_trtab2,
      print_ruletab = merge_ruletabs print_ruletab1 print_ruletab2,
      print_ast_trtab = merge_tr'tabs print_ast_trtab1 print_ast_trtab2,
      prtabs = Printer.merge_prtabs prtabs1 prtabs2}, stamp ())
  end;


(* basic syntax *)

val token_markers =
  ["_tfree", "_tvar", "_free", "_bound", "_var", "_numeral", "_inner_string"];

val basic_nonterms =
  (Lexicon.terminals @ ["logic", "type", "types", "sort", "classes",
    "args", "cargs", "pttrn", "pttrns", "idt", "idts", "aprop", "asms",
    "any", "prop'", "num_const", "float_const", "index", "struct",
    "id_position", "longid_position", "type_name", "class_name"]);



(** print syntax **)

local

fun pretty_strs_qs name strs =
  Pretty.strs (name :: map quote (sort_strings strs));

fun pretty_gram (Syntax (tabs, _)) =
  let
    val {lexicon, prmodes, gram, ...} = tabs;
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

    val {consts, parse_ast_trtab, parse_ruletab, parse_trtab, print_trtab,
      print_ruletab, print_ast_trtab, ...} = tabs;
  in
    [pretty_strs_qs "consts:" consts,
      pretty_trtab "parse_ast_translation:" parse_ast_trtab,
      pretty_ruletab "parse_rules:" parse_ruletab,
      pretty_trtab "parse_translation:" parse_trtab,
      pretty_trtab "print_translation:" print_trtab,
      pretty_ruletab "print_rules:" print_ruletab,
      pretty_trtab "print_ast_translation:" print_ast_trtab]
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
     (if l then Mixfix.Infixl (s, j)
      else if r then Mixfix.Infixr (s, j)
      else Mixfix.Infix (s, j))
  | NONE => NONE);



(** prepare translation rules **)

(* rules *)

datatype 'a trrule =
  Parse_Rule of 'a * 'a |
  Print_Rule of 'a * 'a |
  Parse_Print_Rule of 'a * 'a;

fun map_trrule f (Parse_Rule (x, y)) = Parse_Rule (f x, f y)
  | map_trrule f (Print_Rule (x, y)) = Print_Rule (f x, f y)
  | map_trrule f (Parse_Print_Rule (x, y)) = Parse_Print_Rule (f x, f y);

fun parse_rule (Parse_Rule pats) = SOME pats
  | parse_rule (Print_Rule _) = NONE
  | parse_rule (Parse_Print_Rule pats) = SOME pats;

fun print_rule (Parse_Rule _) = NONE
  | print_rule (Print_Rule pats) = SOME (swap pats)
  | print_rule (Parse_Print_Rule pats) = SOME (swap pats);


(* check_rules *)

local

fun check_rule rule =
  (case Ast.rule_error rule of
    SOME msg =>
      error ("Error in syntax translation rule: " ^ msg ^ "\n" ^
        Pretty.string_of (Ast.pretty_rule rule))
  | NONE => rule);

in

fun check_rules rules =
 (map check_rule (map_filter parse_rule rules),
  map check_rule (map_filter print_rule rules));

end;



(** modify syntax **)

fun ext_syntax f decls = update_syntax mode_default (f decls);

val update_trfuns = ext_syntax Syntax_Ext.syn_ext_trfuns;
val update_advanced_trfuns = ext_syntax Syntax_Ext.syn_ext_advanced_trfuns;

fun update_type_gram add prmode decls =
  (if add then update_syntax else remove_syntax) prmode (Mixfix.syn_ext_types decls);

fun update_const_gram add is_logtype prmode decls =
  (if add then update_syntax else remove_syntax) prmode (Mixfix.syn_ext_consts is_logtype decls);

val update_trrules = ext_syntax Syntax_Ext.syn_ext_rules o check_rules;
val remove_trrules = remove_syntax mode_default o Syntax_Ext.syn_ext_rules o check_rules;

end;

