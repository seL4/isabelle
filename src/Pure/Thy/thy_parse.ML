(*  Title:      Pure/Thy/thy_parse.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The parser for theory files.
*)

infix 5 -- --$$ $$-- ^^;
infix 3 >>;
infix 0 ||;

signature THY_PARSE =
  sig
  type token
  val !! : ('a -> 'b * 'c) -> 'a -> 'b * 'c
  val >> : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c
  val || : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
  val -- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
  val ^^ : ('a -> string * 'b) * ('b -> string * 'c) -> 'a -> string * 'c
  val $$ : string -> token list -> string * token list
  val $$-- : string * (token list -> 'b * 'c) -> token list -> 'b * 'c
  val --$$ : ('a -> 'b * token list) * string -> 'a -> 'b * token list
  val ident: token list -> string * token list
  val long_ident: token list -> string * token list
  val long_id: token list -> string * token list
  val type_var: token list -> string * token list
  val type_args: token list -> string list * token list
  val nat: token list -> string * token list
  val string: token list -> string * token list
  val verbatim: token list -> string * token list
  val empty: 'a -> 'b list * 'a
  val optional: ('a -> 'b * 'a) -> 'b -> 'a -> 'b * 'a
  val repeat: ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val repeat1: ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val enum: string -> (token list -> 'a * token list)
    -> token list -> 'a list * token list
  val enum1: string -> (token list -> 'a * token list)
    -> token list -> 'a list * token list
  val list: (token list -> 'a * token list)
    -> token list -> 'a list * token list
  val list1: (token list -> 'a * token list)
    -> token list -> 'a list * token list
  val name: token list -> string * token list
  val sort: token list -> string * token list
  val opt_infix: token list -> string * token list
  val opt_mixfix: token list -> string * token list
  val opt_witness: token list -> string * token list
  type syntax
  val make_syntax: string list ->
    (string * (token list -> (string * string) * token list)) list -> syntax
  val parse_thy: syntax -> string -> string -> string
  val section: string -> string -> (token list -> string * token list)
    -> (string * (token list -> (string * string) * token list))
  val axm_section: string -> string
    -> (token list -> (string * string list) * token list)
    -> (string * (token list -> (string * string) * token list))
  val pure_keywords: string list
  val pure_sections:
    (string * (token list -> (string * string) * token list)) list
  (*items for building strings*)
  val cat: string -> string -> string
  val parens: string -> string
  val brackets: string -> string
  val mk_list: string list -> string
  val mk_big_list: string list -> string
  val mk_pair: string * string -> string
  val mk_triple: string * string * string -> string
  val strip_quotes: string -> string
  end;


structure ThyParse : THY_PARSE=
struct

open ThyScan;


(** parser toolbox **)

type token = token_kind * string * int;


(* errors *)

exception SYNTAX_ERROR of string * string * int;

fun syn_err s1 s2 n = raise SYNTAX_ERROR (s1, s2, n);

fun eof_err () = error "Unexpected end-of-file";

(*Similar to Prolog's cut: reports any syntax error instead of backtracking
  through a superior || *)
fun !! parse toks = parse toks
  handle SYNTAX_ERROR (s1, s2, n) => error ("Syntax error on line " ^
    string_of_int n ^ ": " ^ s1 ^ " expected and " ^ s2 ^ " was found");


(* parser combinators *)

fun (parse >> f) toks = apfst f (parse toks);

fun (parse1 || parse2) toks =
  parse1 toks handle SYNTAX_ERROR _ => parse2 toks;

fun (parse1 -- parse2) toks =
  let
    val (x, toks') = parse1 toks;
    val (y, toks'') = parse2 toks';
  in
    ((x, y), toks'')
  end;

fun (parse1 ^^ parse2) = parse1 -- parse2 >> op ^;


(* generic parsers *)

fun $$ a ((k, b, n) :: toks) =
      if k = Keyword andalso a = b then (a, toks)
      else syn_err (quote a) (quote b) n
  | $$ _ [] = eof_err ();

fun (a $$-- parse) = $$ a -- parse >> #2;

fun (parse --$$ a) = parse -- $$ a >> #1;


fun kind k1 ((k2, s, n) :: toks) =
      if k1 = k2 then (s, toks)
      else syn_err (name_of_kind k1) (quote s) n
  | kind _ [] = eof_err ();

val ident = kind Ident;
val long_ident = kind LongIdent;
val long_id = ident || long_ident;
val type_var = kind TypeVar >> quote;
val nat = kind Nat;
val string = kind String;
val verbatim = kind Verbatim;
val eof = kind EOF;

fun empty toks = ([], toks);

fun optional parse def = parse || empty >> K def;

fun repeat parse toks = (parse -- repeat parse >> op :: || empty) toks;
fun repeat1 parse = parse -- repeat parse >> op ::;

fun enum1 sep parse = parse -- repeat (sep $$-- parse) >> op ::;
fun enum sep parse = enum1 sep parse || empty;

fun list  parse = enum  "," parse;
fun list1 parse = enum1 "," parse;


(** theory parsers **)

(* misc utilities *)

fun cat s1 s2 = s1 ^ " " ^ s2;

val parens = enclose "(" ")";
val brackets = enclose "[" "]";

val mk_list = brackets o commas;
val mk_big_list = brackets o space_implode ",\n ";

fun mk_pair (x, y) = parens (commas [x, y]);
fun mk_triple (x, y, z) = parens (commas [x, y, z]);
fun mk_triple1 ((x, y), z) = mk_triple (x, y, z);
fun mk_triple2 (x, (y, z)) = mk_triple (x, y, z);

fun split_decls l = flat (map (fn (xs, y) => map (rpair y) xs) l);

fun strip_quotes str =
  implode (tl (take (size str - 1, explode str)));


(* names *)

val name = ident >> quote || string;
val names = list name;
val names1 = list1 name;
val name_list = names >> mk_list;
val name_list1 = names1 >> mk_list;


(* classes *)

val subclass = name -- optional ("<" $$-- !! name_list1) "[]";

val class_decls = repeat1 (subclass >> mk_pair) >> mk_big_list;


(* arities *)

val sort =
  name >> brackets ||
  "{" $$-- name_list --$$ "}";

val sort_list1 = list1 sort >> mk_list;


val arity = optional ("(" $$-- !! (sort_list1 --$$")")) "[]" -- sort;

val arity_decls = repeat1 (names1 --$$ "::" -- !! arity)
  >> (mk_big_list o map mk_triple2 o split_decls);


(* mixfix annotations *)

val infxl =
  "infixl" $$-- !! (nat >> cat "Infixl" || string -- nat >> (cat "InfixlName" o mk_pair));
val infxr =
  "infixr" $$-- !! (nat >> cat "Infixr" || string -- nat >> (cat "InfixrName" o mk_pair));

val binder = "binder" $$--
  !! (string -- (("[" $$-- nat --$$ "]") -- nat || nat >> (fn n => (n, n))))
    >> (cat "Binder" o mk_triple2);

val opt_pris = optional ("[" $$-- !! (list nat --$$ "]")) [] >> mk_list;

val mixfix = string -- !! (opt_pris -- optional nat "max_pri")
  >> (cat "Mixfix" o mk_triple2);

fun opt_syn fx = optional ("(" $$-- fx --$$ ")") "NoSyn";

val opt_infix = opt_syn (infxl || infxr);
val opt_mixfix = opt_syn (mixfix || infxl || infxr || binder);


(* types *)

(*Parse an identifier, but only if it is not followed by "::", "=" or ",";
  the exclusion of a postfix comma can be controlled to allow expressions
  like "(id, id)" but disallow ones like "'a => id id,id :: ..."*)
fun ident_no_colon _ [] = eof_err()
  | ident_no_colon allow_comma ((Ident, s, n) :: (rest as (Keyword, s2, n2) ::
                                toks)) =
      if s2 = "::" orelse s2 = "=" orelse (not allow_comma andalso s2 = ",")
      then syn_err (name_of_kind Ident) (quote s2) n2
      else (s, rest)
  | ident_no_colon _ ((Ident, s, n) :: toks) = (s, toks)
  | ident_no_colon _ ((k, s, n) :: _) =
      syn_err (name_of_kind Ident) (quote s) n;

(*Type used in types, consts and syntax sections*)
fun const_type allow_comma toks =
  let val simple_type =
        (ident ||
         kind TypeVar -- optional ("::" $$-- ident >> cat "::") "" >>
           (fn (tv, cl) => cat tv cl)) --
           repeat (ident_no_colon allow_comma) >>
           (fn (args, ts) => cat args (space_implode " " ts)) ||
         ("(" $$-- (list1 (const_type true)) --$$ ")" >> (parens o commas)) --
           repeat1 (ident_no_colon allow_comma) >>
           (fn (args, ts) => cat args (space_implode " " ts));

      val appl_param =
        simple_type || "(" $$-- const_type true --$$ ")" >> parens || 
        "[" $$-- (list1 (const_type true)) --$$ "]" --$$ "=>" --
          const_type allow_comma >>
          (fn (src, dest) => mk_list src ^ " => " ^ dest);
  in ("[" $$-- (list1 (const_type true)) --$$ "]" --$$ "=>" --
        const_type allow_comma >>
        (fn (src, dest) => mk_list src ^ " => " ^ dest) ||
      repeat1 (appl_param --$$ "=>") -- const_type allow_comma >>
        (fn (src, dest) => space_implode " => " (src@[dest])) ||
      simple_type ||
      "(" $$-- const_type true --$$ ")" >> parens) toks
  end;

fun mk_old_type_decl ((ts, n), syn) =
  map (fn t => (mk_triple (t, n, syn), false)) ts;

fun mk_type_decl (((xs, t), None), syn) =
      [(mk_triple (t, string_of_int (length xs), syn), false)]
  | mk_type_decl (((xs, t), Some rhs), syn) =
      [(parens (commas [t, mk_list xs, rhs, syn]), true)];

fun mk_type_decls tys =
  "|> add_types\n" ^ mk_big_list (keyfilter tys false) ^ "\n\n\
  \|> add_tyabbrs\n" ^ mk_big_list (keyfilter tys true);


val old_type_decl = names1 -- nat -- opt_infix >> mk_old_type_decl;

val type_args =
  type_var >> (fn x => [x]) ||
  "(" $$-- !! (list1 type_var --$$ ")") ||
  empty >> K [];

val type_decl = type_args -- name --
  optional ("=" $$-- (string || (const_type false >> quote)) >> Some) None
  -- opt_infix >> mk_type_decl;

val type_decls =
  repeat1 (old_type_decl || type_decl) >> (mk_type_decls o flat);


(* consts *)

val const_decls =
  repeat1
    (names1 --$$ "::" -- !! ((string || const_type false >> quote) -- opt_mixfix))
  >> (mk_big_list o map mk_triple2 o split_decls);

val opt_mode =
  optional
    ("(" $$-- !! (name -- optional ($$ "output" >> K "false") "true" --$$ ")"))
    ("\"\"", "true")
  >> mk_pair;

val syntax_decls = opt_mode -- const_decls >> (fn (mode, txt) => mode ^ "\n" ^ txt);


(* translations *)

val trans_pat =
  optional ("(" $$-- !! (name --$$ ")")) "\"logic\"" -- string >> mk_pair;

val trans_arrow =
  $$ "=>" >> K "Syntax.|-> " ||
  $$ "<=" >> K "Syntax.<-| " ||
  $$ "==" >> K "Syntax.<-> ";

val trans_line =
  trans_pat -- !! (trans_arrow -- trans_pat)
    >> (fn (left, (arr, right)) => arr ^ mk_pair (left, right));

val trans_decls = repeat1 trans_line >> mk_big_list;


(* ML translations *)

val trfun_defs =
  " val parse_ast_translation = [];\n\
  \ val parse_translation = [];\n\
  \ val print_translation = [];\n\
  \ val print_ast_translation = [];";

val trfun_args =
  "(parse_ast_translation, parse_translation, \
  \print_translation, print_ast_translation)";

fun mk_mltrans txt =
  "let\n"
  ^ trfun_defs ^ "\n"
  ^ txt ^ "\n\
  \in\n\
  \ " ^ trfun_args ^ "\n\
  \end";

val mltrans = verbatim >> mk_mltrans;


(* axioms *)

val mk_axms = mk_big_list o map (mk_pair o apfst quote);

fun mk_axiom_decls axms = (mk_axms axms, map fst axms);

val axiom_decls = repeat1 (ident -- !! string) >> mk_axiom_decls;


(* combined consts and axioms *)

fun mk_constaxiom_decls x =
  let
    val (axms_defs, axms_names) =
      mk_axiom_decls (map (fn ((id, _), def) => (id ^ "_def", def)) x);
  in ((mk_big_list o map mk_triple2 o map (apfst quote o fst)) x ^
       "\n\n|> add_defs\n" ^ axms_defs, axms_names)
  end;

val constaxiom_decls =
  repeat1 (ident --$$ "::" -- !!
           ((string || const_type false >> quote) -- opt_mixfix) -- !!
           string) >> mk_constaxiom_decls;


(* axclass *)

fun mk_axclass_decl ((c, cs), axms) =
  (mk_pair (c, cs) ^ "\n" ^ mk_axms axms,
    (strip_quotes c ^ "I") :: map fst axms);

val axclass_decl = subclass -- repeat (ident -- !! string) >> mk_axclass_decl;


(* instance *)

fun mk_witness (axths, opt_tac) =
  mk_list (keyfilter axths false) ^ "\n" ^
  mk_list (keyfilter axths true) ^ "\n" ^
  opt_tac;

val axm_or_thm =
  string >> rpair false ||
  long_id >> rpair true;


val opt_witness =
  optional ("(" $$-- list1 axm_or_thm --$$ ")") [] --
  optional (verbatim >> (parens o cat "Some" o parens)) "None"
  >> mk_witness;

val instance_decl =
  (name --$$ "<" -- name >> (pair "|> AxClass.add_inst_subclass" o mk_pair) ||
    name --$$ "::" -- arity >> (pair "|> AxClass.add_inst_arity" o mk_triple2))
  -- opt_witness
  >> (fn ((x, y), z) => (cat_lines [x, y, z]));



(** theory syntax **)

type syntax =
  lexicon * (token list -> (string * string) * token list) Symtab.table;

fun make_syntax keywords sects =
  (make_lexicon (map fst sects @ keywords),
    Symtab.make sects handle Symtab.DUPS dups =>
      error ("Duplicate sections in theory file syntax: " ^ commas_quote dups));


(* header *)

fun mk_header (thy_name, bases) =
  (thy_name, "mk_base " ^ mk_list bases ^ " " ^ quote thy_name);

val base =
  ident >> (cat "Thy" o quote) ||
  string >> cat "File";

val header = ident --$$ "=" -- enum1 "+" base >> mk_header;


(* extension *)

fun mk_extension (txts, mltxt) =
  let
    val cat_sects = space_implode "\n\n" o filter_out (equal "");
    val (extxts, postxts) = split_list txts;
  in
    (cat_sects extxts, cat_sects postxts, mltxt)
  end;

fun sect tab ((Keyword, s, n) :: toks) =
      (case Symtab.lookup (tab, s) of
        Some parse => !! parse toks
      | None => syn_err "section" s n)
  | sect _ ((_, s, n) :: _) = syn_err "section" s n
  | sect _ [] = eof_err ();

fun extension sectab = "+" $$-- !! (repeat (sect sectab) --$$ "end") --
  optional ("ML" $$-- verbatim) "" >> mk_extension;


(* theory definition *)

fun mk_structure tname ((thy_name, old_thys), opt_txts) =
  if thy_name <> tname then
    error ("Filename \"" ^ tname ^ ".thy\" and theory name "
      ^ quote thy_name ^ " are different")
  else
    (case opt_txts of
      Some (extxt, postxt, mltxt) =>
        "val thy = " ^ old_thys ^ " true;\n\n\
        \structure " ^ thy_name ^ " =\n\
        \struct\n\
        \\n\
        \local\n"
        ^ trfun_defs ^ "\n\
        \in\n\
        \\n"
        ^ mltxt ^ "\n\
        \\n\
        \val thy = thy\n\
        \\n\
        \|> add_trfuns\n"
        ^ trfun_args ^ "\n\
        \\n"
        ^ extxt ^ "\n\
        \\n\
        \|> add_thyname " ^ quote thy_name ^ ";\n\
        \\n\
        \val _ = store_theory (thy, " ^ quote thy_name ^ ");\n\
        \\n\
        \\n"
        ^ postxt ^ "\n\
        \\n\
        \end;\n\
        \end;\n\
        \\n\
        \open " ^ thy_name ^ ";\n\
        \\n"
    | None =>
        "val thy = " ^ old_thys ^ " false;\n\
        \\n\
        \structure " ^ thy_name ^ " =\n\
        \struct\n\
        \\n\
        \val thy = thy\n\
        \\n\
        \val _ = store_theory (thy, " ^ quote thy_name ^ ");\n\
        \\n\
        \end;\n\
        \\n\
        \open " ^ thy_name ^ ";\n\
        \\n");


fun theory_defn sectab tname =
  header -- optional (extension sectab >> Some) None -- eof
  >> (mk_structure tname o #1);

fun parse_thy (lex, sectab) tname str =
  #1 (!! (theory_defn sectab tname) (tokenize lex str));


(* standard sections *)

fun mk_val ax = "val " ^ ax ^ " = get_axiom thy " ^ quote ax ^ ";";
val mk_vals = cat_lines o map mk_val;

fun mk_axm_sect "" (txt, axs) = (txt, mk_vals axs)
  | mk_axm_sect pretxt (txt, axs) = (pretxt ^ "\n" ^ txt, mk_vals axs);

fun axm_section name pretxt parse =
  (name, parse >> mk_axm_sect pretxt);

fun section name pretxt parse =
  axm_section name pretxt (parse >> rpair []);


val pure_keywords =
 ["end", "ML", "mixfix", "infixr", "infixl", "binder", "output", "=",
  "+", ",", "<", "{", "}", "(", ")", "[", "]", "::", "==", "=>", "<="];

val pure_sections =
 [section "oracle" "|> set_oracle" (name >> strip_quotes),
  section "classes" "|> add_classes" class_decls,
  section "default" "|> add_defsort" sort,
  section "types" "" type_decls,
  section "arities" "|> add_arities" arity_decls,
  section "consts" "|> add_consts" const_decls,
  section "syntax" "|> add_modesyntax" syntax_decls,
  section "translations" "|> add_trrules" trans_decls,
  section "MLtrans" "|> add_trfuns" mltrans,
  section "MLtext" "" verbatim,
  axm_section "rules" "|> add_axioms" axiom_decls,
  axm_section "defs" "|> add_defs" axiom_decls,
  axm_section "constdefs" "|> add_consts" constaxiom_decls,
  axm_section "axclass" "|> AxClass.add_axclass" axclass_decl,
  section "instance" "" instance_decl];

end;
