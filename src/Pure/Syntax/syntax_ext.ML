(*  Title:      Pure/Syntax/syntax_ext.ML
    Author:     Makarius

Syntax extension as internal record.
*)

signature SYNTAX_EXT =
sig
  datatype mfix = Mfix of Symbol_Pos.T list * typ * string * int list * int * Position.T
  type block =
    {markup: Markup.T list, open_block: bool, consistent: bool, unbreakable: bool, indent: int}
  val block_indent: int -> block
  datatype xsymb =
    Delim of string |
    Argument of string * int |
    Space of string |
    Bg of block |
    Brk of int |
    En
  datatype xprod = XProd of string * xsymb list * string * int
  val chain_pri: int
  val delims_of: xprod list -> Symbol.symbol list list
  datatype syn_ext =
    Syn_Ext of {
      xprods: xprod list,
      consts: (string * string list) list,
      parse_ast_translation: (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list,
      parse_rules: (Ast.ast * Ast.ast) list,
      parse_translation: (string * ((Proof.context -> term list -> term) * stamp)) list,
      print_translation: (string * ((Proof.context -> typ -> term list -> term) * stamp)) list,
      print_rules: (Ast.ast * Ast.ast) list,
      print_ast_translation: (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list}
  val block_annotation: int -> Markup.T -> string -> string
  val mfix_name: Proof.context -> Symbol_Pos.T list -> string
  val mfix_args: Proof.context -> Symbol_Pos.T list -> int
  val mixfix_args: Proof.context -> Input.source -> int
  val escape: string -> string
  val syn_ext: Proof.context -> string list -> mfix list ->
    (string * string list) list -> (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list *
    (string * ((Proof.context -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> typ -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list ->
    (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext_consts: Proof.context -> (string * string list) list -> syn_ext
  val syn_ext_rules: Proof.context -> (Ast.ast * Ast.ast) list * (Ast.ast * Ast.ast) list -> syn_ext
  val syn_ext_trfuns: Proof.context ->
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list *
    (string * ((Proof.context -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> typ -> term list -> term) * stamp)) list *
    (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list -> syn_ext
  val stamp_trfun: stamp -> string * 'a -> string * ('a * stamp)
  val mk_trfun: string * 'a -> string * ('a * stamp)
  val eq_trfun: ('a * stamp) * ('a * stamp) -> bool
end;

structure Syntax_Ext: SYNTAX_EXT =
struct

(** datatype xprod **)

(*Delim s: delimiter s
  Argument (s, p): nonterminal s requiring priority >= p, or valued token
  Space s: some white space for printing
  Bg, Brk, En: blocks and breaks for pretty printing*)

type block =
  {markup: Markup.T list, open_block: bool, consistent: bool, unbreakable: bool, indent: int};

fun block_indent indent : block =
  {markup = [], open_block = false, consistent = false, unbreakable = false, indent = indent};

datatype xsymb =
  Delim of string |
  Argument of string * int |
  Space of string |
  Bg of block |
  Brk of int |
  En;

fun is_delim (Delim _) = true
  | is_delim _ = false;

fun is_terminal (Delim _) = true
  | is_terminal (Argument (s, _)) = Lexicon.is_terminal s
  | is_terminal _ = false;

fun is_argument (Argument _) = true
  | is_argument _ = false;

fun is_index (Argument ("index", _)) = true
  | is_index _ = false;

val index = Argument ("index", 1000);


(*XProd (lhs, syms, c, p):
    lhs: name of nonterminal on the lhs of the production
    syms: list of symbols on the rhs of the production
    c: head of parse tree
    p: priority of this production*)

datatype xprod = XProd of string * xsymb list * string * int;

val chain_pri = ~1;   (*dummy for chain productions*)

fun delims_of xprods =
  fold (fn XProd (_, xsymbs, _, _) =>
    fold (fn Delim s => insert (op =) s | _ => I) xsymbs) xprods []
  |> map Symbol.explode;



(** datatype mfix **)

(*Mfix (sy, ty, c, ps, p, pos):
    sy: rhs of production as symbolic text
    ty: type description of production
    c: head of parse tree
    ps: priorities of arguments in sy
    p: priority of production
    pos: source position*)

datatype mfix = Mfix of Symbol_Pos.T list * typ * string * int list * int * Position.T;


(* properties *)

fun block_annotation indent notation_markup notation_name =
  let
    val (elem, props) = notation_markup |> notation_name <> "" ? Markup.name notation_name;
    val kind = Properties.get props Markup.kindN;
    val name = Properties.get props Markup.nameN;
    val s1 = if indent = 0 then [] else ["indent=" ^ Value.print_int indent];
    val s2 =
      if elem = Markup.notationN then
        [Properties.print_eq (elem, cartouche (implode_space (the_list kind @ the_list name)))]
      else raise Fail ("Bad markup element for notatio: " ^ quote elem)
  in cartouche (implode_space (s1 @ s2)) end;

fun show_names names =
  commas_quote (map (fn (name, pos) => Markup.markup (Position.markup pos) name) names);

local

open Basic_Symbol_Pos;

val err_prefix = "Error in mixfix block properties: ";
val !!! = Symbol_Pos.!!! (fn () => err_prefix ^ "atom expected (identifier, numeral, cartouche)");

val scan_atom =
  Symbol_Pos.scan_ident ||
  ($$$ "-" @@@ (Symbol_Pos.scan_float || Symbol_Pos.scan_nat)) ||
  Symbol_Pos.scan_float || Symbol_Pos.scan_nat ||
  Symbol_Pos.scan_cartouche_content err_prefix;

val scan_blanks = Scan.many (Symbol.is_blank o Symbol_Pos.symbol);
val scan_item =
  scan_blanks |-- scan_atom --| scan_blanks
    >> (fn ss => (Symbol_Pos.content ss, #1 (Symbol_Pos.range ss)));

val scan_prop = scan_item -- Scan.option ($$ "=" |-- !!! scan_item);

fun get_property default0 default1 parse name props =
  (case find_first (fn ((a, _), _) => a = name) props of
    NONE => default0
  | SOME (_, NONE) => default1
  | SOME ((_, pos1), SOME (b, pos2)) =>
      (parse (b, pos2) handle Fail msg =>
        error (msg ^ " for property " ^ quote name ^ Position.here_list [pos1, pos2])));

fun parse_notation ctxt (s, pos) =
  let
    val (kind, name) =
      (case Symbol.explode_words s of
        [] => ("", "")
      | a :: bs => (a, space_implode " " bs));
    val markup =
      (case try (fn () => Markup_Kind.check_notation ctxt (kind, Position.none)) () of
        SOME m => m
      | NONE =>
          error ("Bad notation kind " ^ quote kind ^ Position.here pos ^
            ", expected: " ^ commas_quote (Markup_Kind.get_notation_kinds ctxt)));
  in markup |> Markup.properties (Markup.name_proper name) end;

in

fun read_properties ss =
  let
    val props =
      (case Scan.error (Scan.finite Symbol_Pos.stopper (Scan.repeat scan_prop)) ss of
        (props, []) => props
      | (_, (_, pos) :: _) => error (err_prefix ^ "bad input" ^ Position.here pos));
    fun ok (_, bs) = length bs <= 1;
    val _ =
      (case AList.group (eq_fst op =) props |> filter_out ok of
        [] => ()
      | dups => error ("Duplicate properties: " ^ show_names (map #1 dups)));
  in props end;

val get_string = get_property "" "" #1;
val get_bool = get_property false true (Value.parse_bool o #1);
val get_nat = get_property 0 1 (Value.parse_nat o #1);

fun get_notation_markup ctxt =
  get_property NONE (SOME Markup.notation0) (SOME o parse_notation ctxt) Markup.notationN;

end;


(* read mixfix annotations *)

local

val markup_block_begin = Markup_Kind.setup_expression (Binding.make ("mixfix_block_begin", \<^here>));
val markup_block_end = Markup_Kind.setup_expression (Binding.make ("mixfix_block_end", \<^here>));
val markup_delimiter = Markup_Kind.setup_expression (Binding.make ("mixfix_delimiter", \<^here>));
val markup_argument = Markup_Kind.setup_expression (Binding.make ("mixfix_argument", \<^here>));
val markup_space = Markup_Kind.setup_expression (Binding.make ("mixfix_space", \<^here>));
val markup_break = Markup_Kind.setup_expression (Binding.make ("mixfix_break", \<^here>));

open Basic_Symbol_Pos;

val err_prefix = "Error in mixfix annotation: ";

fun scan_one pred = Scan.one (pred o Symbol_Pos.symbol);
fun scan_many pred = Scan.many (pred o Symbol_Pos.symbol);
fun scan_many1 pred = Scan.many1 (pred o Symbol_Pos.symbol);

fun reports_of_block pos = [(pos, markup_block_begin), (pos, Markup.keyword3)];

fun reports_of (xsym, pos) =
  (case xsym of
    Delim _ => [(pos, markup_delimiter), (pos, Markup.literal)]
  | Argument _ => [(pos, markup_argument)]
  | Space _ => [(pos, markup_space)]
  | Bg _ => reports_of_block pos
  | Brk _ => [(pos, markup_break), (pos, Markup.keyword3)]
  | En => [(pos, markup_block_end), (pos, Markup.keyword3)]);

fun reports_text_of (Delim s, pos) =
      if Position.is_reported pos andalso exists Symbol.is_utf8 (Symbol.explode s) then
        [((pos, Markup.bad ()),
          "Mixfix delimiter contains raw Unicode -- this is non-portable and unreliable")]
      else []
  | reports_text_of _ = [];

fun read_block_properties ctxt ss =
  let
    val props = read_properties ss;

    val more_markups = the_list (get_notation_markup ctxt props);

    val markup_name = get_string Markup.markupN props;
    val markup_props = props |> map_filter (fn (a, opt_b) =>
      if member (op =) Markup.block_properties (#1 a) then NONE
      else SOME (a, the_default ("true", Position.none) opt_b));
    val markups =
      if markup_name <> "" then [(markup_name, map (apply2 #1) markup_props)]
      else if null markup_props then []
      else error ("Markup name required for block properties: " ^ show_names (map #1 markup_props));

    val block: block =
     {markup = more_markups @ markups,
      open_block = get_bool Markup.open_blockN props,
      consistent = get_bool Markup.consistentN props,
      unbreakable = get_bool Markup.unbreakableN props,
      indent = get_nat Markup.indentN props};
  in Bg block end
  handle ERROR msg =>
    let
      val reported_texts =
        reports_of_block (#1 (Symbol_Pos.range ss))
        |> map (fn (p, m) => Markup.markup_report (Position.reported_text p m ""))
    in error (msg ^ implode reported_texts) end;

val read_block_indent =
  Bg o block_indent o #1 o Library.read_int o map Symbol_Pos.symbol;

val is_meta = member (op =) ["'", "(", ")", "/", "_", "\<index>", Symbol.open_, Symbol.close];

val scan_delim =
  scan_one Symbol.is_control ::: Symbol_Pos.scan_cartouche "Mixfix error: " ||
  $$ "'" |-- scan_one ((not o Symbol.is_blank) andf Symbol.not_eof) >> single ||
  scan_one ((not o is_meta) andf (not o Symbol.is_blank) andf Symbol.not_eof) >> single;

fun scan_symbs ctxt =
  let
    val scan_sym =
      $$ "_" >> K (Argument ("", 0)) ||
      $$ "\<index>" >> K index ||
      $$ "(" |--
       (Symbol_Pos.scan_cartouche_content err_prefix >> read_block_properties ctxt ||
        scan_many Symbol.is_digit >> read_block_indent) ||
      $$ ")" >> K En ||
      $$ "/" -- $$ "/" >> K (Brk ~1) ||
      $$ "/" |-- scan_many Symbol.is_space >> (Brk o length) ||
      scan_many1 Symbol.is_space >> (Space o Symbol_Pos.content) ||
      Scan.repeat1 scan_delim >> (Delim o Symbol_Pos.content o flat);

    val scan_symb =
      Scan.trace scan_sym >> (fn (syms, trace) => SOME (syms, #1 (Symbol_Pos.range trace))) ||
      $$ "'" -- scan_one Symbol.is_space >> K NONE;
  in Scan.repeat scan_symb --| Scan.ahead (~$$ "'") end;

in

fun read_mfix ctxt ss =
  let
    val xsymbs =
      (case Scan.error (Scan.finite Symbol_Pos.stopper (scan_symbs ctxt)) ss of
        (res, []) => map_filter I res
      | (_, (_, pos) :: _) => error (err_prefix ^ "bad input" ^ Position.here pos));
    val _ = Context_Position.reports ctxt (maps reports_of xsymbs);
    val _ = Context_Position.reports_text ctxt (maps reports_text_of xsymbs);
  in xsymbs end;

val read_mfix0 = read_mfix o Context_Position.set_visible false;

fun mfix_name ctxt =
  read_mfix0 ctxt #> map_filter (fn (Delim s, _) => SOME s | _ => NONE) #> space_implode " ";

fun mfix_args ctxt ss =
  Integer.build (read_mfix0 ctxt ss |> fold (fn (xsymb, _) => is_argument xsymb ? Integer.add 1));

fun mixfix_args ctxt = mfix_args ctxt o Input.source_explode;

val escape = implode o map (fn s => if is_meta s then "'" ^ s else s) o Symbol.explode;

end;


(* mfix_to_xprod *)

fun mfix_to_xprod ctxt logical_types (Mfix (sy, typ, const, pris, pri, pos)) =
  let
    val nonterm_for_lhs = the_default "logic" o try dest_Type_name;
    val nonterm_for_rhs = the_default "any" o try dest_Type_name;

    val _ = Context_Position.report ctxt pos Markup.language_mixfix;
    val symbs0 = read_mfix ctxt sy;

    fun err_in_mixfix msg = error (msg ^ " in mixfix annotation" ^ Position.here pos);

    fun check_blocks [] pending bad = pending @ bad
      | check_blocks ((Bg _, pos) :: rest) pending bad = check_blocks rest (pos :: pending) bad
      | check_blocks ((En, pos) :: rest) [] bad = check_blocks rest [] (pos :: bad)
      | check_blocks ((En, _) :: rest) (_ :: pending) bad = check_blocks rest pending bad
      | check_blocks (_ :: rest) pending bad = check_blocks rest pending bad;

    fun add_args [] ty [] = ([], nonterm_for_lhs ty)
      | add_args [] _ _ = err_in_mixfix "Too many precedences"
      | add_args ((sym as (Argument ("index", _), _)) :: syms) ty ps =
          add_args syms ty ps |>> cons sym
      | add_args ((Argument _, pos) :: syms) (Type ("fun", [ty, tys])) [] =
          add_args syms tys [] |>> cons (Argument (nonterm_for_rhs ty, 0), pos)
      | add_args ((Argument _, pos) :: syms) (Type ("fun", [ty, tys])) (p :: ps) =
          add_args syms tys ps |>> cons (Argument (nonterm_for_rhs ty, p), pos)
      | add_args ((Argument _, _) :: _) _ _ =
          err_in_mixfix "More arguments than in corresponding type"
      | add_args (sym :: syms) ty ps = add_args syms ty ps |>> cons sym;

    fun logical_args (a as (Argument (s, p))) =
          if s <> "prop" andalso member (op =) logical_types s then Argument ("logic", p) else a
      | logical_args a = a;

    fun rem_pri (Argument (s, _)) = Argument (s, chain_pri)
      | rem_pri sym = sym;

    val indexes = filter (is_index o #1) symbs0;
    val _ =
      if length indexes <= 1 then ()
      else error ("More than one index argument" ^ Position.here_list (map #2 indexes));

    val args = map_filter (fn (arg as Argument _, _) => SOME arg | _ => NONE) symbs0;
    val (const', typ', syntax_consts, parse_rules) =
      if not (exists is_index args) then (const, typ, NONE, NONE)
      else
        let
          val indexed_const =
            if const <> "" then const ^ "_indexed"
            else err_in_mixfix "Missing constant name for indexed syntax";
          val rangeT = Term.range_type typ handle Match =>
            err_in_mixfix "Missing structure argument for indexed syntax";

          val xs = map Ast.Variable (Name.invent Name.context "xa" (length args - 1));
          val (xs1, xs2) = chop (find_index is_index args) xs;
          val i = Ast.Variable "i";
          val lhs =
            Ast.mk_appl (Ast.Constant indexed_const)
              (xs1 @ [Ast.mk_appl (Ast.Constant "_index") [i]] @ xs2);
          val rhs = Ast.mk_appl (Ast.Constant const) (i :: xs);
        in (indexed_const, rangeT, SOME (indexed_const, [const]), SOME (lhs, rhs)) end;

    val (symbs1, lhs) = add_args symbs0 typ' pris;

    val copy_prod =
      (lhs = "prop" orelse lhs = "logic")
        andalso const <> ""
        andalso not (null symbs1)
        andalso not (exists (is_delim o #1) symbs1);
    val lhs' =
      if copy_prod orelse lhs = "prop" andalso map #1 symbs1 = [Argument ("prop'", 0)] then lhs
      else if lhs = "prop" then "prop'"
      else if member (op =) logical_types lhs then "logic"
      else lhs;
    val symbs2 = map (apfst logical_args) symbs1;

    val _ =
      (pri :: pris) |> List.app (fn p =>
        if p >= 0 andalso p <= 1000 then ()
        else err_in_mixfix ("Precedence " ^ string_of_int p ^ " out of range"));
    val _ =
      (case check_blocks symbs2 [] [] of
        [] => ()
      | bad => error ("Unbalanced block parentheses" ^ Position.here_list bad));

    val xprod = XProd (lhs', map #1 symbs2, const', pri);
    val xprod' =
      if Lexicon.is_terminal lhs' then
        err_in_mixfix ("Illegal use of terminal " ^ quote lhs' ^ " as nonterminal")
      else if const <> "" then xprod
      else if length (filter (is_argument o #1) symbs2) <> 1 then
        err_in_mixfix "Copy production must have exactly one argument"
      else if exists (is_terminal o #1) symbs2 then xprod
      else XProd (lhs', map (rem_pri o #1) symbs2, "", chain_pri);

  in (xprod', syntax_consts, parse_rules) end;



(** datatype syn_ext **)

datatype syn_ext =
  Syn_Ext of {
    xprods: xprod list,
    consts: (string * string list) list,
    parse_ast_translation: (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list,
    parse_rules: (Ast.ast * Ast.ast) list,
    parse_translation: (string * ((Proof.context -> term list -> term) * stamp)) list,
    print_translation: (string * ((Proof.context -> typ -> term list -> term) * stamp)) list,
    print_rules: (Ast.ast * Ast.ast) list,
    print_ast_translation: (string * ((Proof.context -> Ast.ast list -> Ast.ast) * stamp)) list};


(* syn_ext *)

fun syn_ext ctxt logical_types mfixes consts trfuns (parse_rules, print_rules) =
  let
    val (parse_ast_translation, parse_translation, print_translation,
      print_ast_translation) = trfuns;

    val xprod_results = map (mfix_to_xprod ctxt logical_types) mfixes;
    val xprods = map #1 xprod_results;
    val consts' = map_filter #2 xprod_results;
    val parse_rules' = rev (map_filter #3 xprod_results);
    val mfix_consts = map (fn Mfix x => (#3 x, [])) mfixes @ map (fn XProd x => (#3 x, [])) xprods;
  in
    Syn_Ext {
      xprods = xprods,
      consts = mfix_consts @ consts' @ consts,
      parse_ast_translation = parse_ast_translation,
      parse_rules = parse_rules' @ parse_rules,
      parse_translation = parse_translation,
      print_translation = print_translation,
      print_rules = map swap parse_rules' @ print_rules,
      print_ast_translation = print_ast_translation}
  end;


fun syn_ext_consts ctxt consts = syn_ext ctxt [] [] consts ([], [], [], []) ([], []);
fun syn_ext_rules ctxt rules = syn_ext ctxt [] [] [] ([], [], [], []) rules;
fun syn_ext_trfuns ctxt trfuns = syn_ext ctxt [] [] [] trfuns ([], []);

fun stamp_trfun s (c, f) = (c, (f, s));
fun mk_trfun tr = stamp_trfun (stamp ()) tr;
fun eq_trfun ((_, s1: stamp), (_, s2)) = s1 = s2;

end;
