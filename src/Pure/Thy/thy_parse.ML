(*  Title:      Pure/Thy/thy_parse.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

The parser for theory files.

TODO:
  remove quote in syn_err (?)
  check: names vs names1
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
  type syntax
  val make_syntax: string list ->
    (string * (token list -> (string * string) * token list)) list -> syntax
  val parse_thy: syntax -> string -> string
  val section: string -> string -> (token list -> string * token list)
    -> (string * (token list -> (string * string) * token list))
  val axm_section: string -> string
    -> (token list -> (string * string list) * token list)
    -> (string * (token list -> (string * string) * token list))
  val pure_keywords: string list
  val pure_sections:
    (string * (token list -> (string * string) * token list)) list
  val pure_syntax: syntax
end;

functor ThyParseFun(structure Symtab: SYMTAB and ThyScan: THY_SCAN)(*: THY_PARSE *) = (* FIXME *)
struct

open ThyScan;


(** parser toolbox **)

type token = token_kind * string * int;


(* errors *)

exception SYNTAX_ERROR of string * string * int;

fun syn_err s1 s2 n = raise SYNTAX_ERROR (s1, s2, n);

fun eof_err () = error "Unexpected end-of-file";

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

val list = enum ",";
val list1 = enum1 ",";



(** theory parsers **)

(* misc utilities *)

fun cat s1 s2 = s1 ^ " " ^ s2;

val pars = parents "(" ")";
val brackets = parents "[" "]";

val mk_list = brackets o commas;
val mk_big_list = brackets o space_implode ",\n ";

fun mk_pair (x, y) = pars (commas [x, y]);
fun mk_triple (x, y, z) = pars (commas [x, y, z]);
fun mk_triple1 ((x, y), z) = mk_triple (x, y, z);
fun mk_triple2 (x, (y, z)) = mk_triple (x, y, z);

val split_decls = flat o map (fn (xs, y) => map (rpair y) xs);

fun strip_quotes str =
  implode (tl (take (size str - 1, explode str)));


(* names *)

val name = ident >> quote || string;
val names = list name;
val names1 = list1 name;
val name_list = names >> mk_list;
val name_list1 = names1 >> mk_list;


(* classes *)

fun mk_subclass (c, cs) = mk_triple ("[]", c, cs);

val subclass = name -- optional ("<" $$-- !! name_list1) "[]";

val class_decls = repeat1 (subclass >> mk_subclass) >> mk_big_list;


(* arities *)

val sort =
  name >> brackets ||
  "{" $$-- name_list --$$ "}";

val sort_list1 = list1 sort >> mk_list;


val arity = optional ("(" $$-- !! (sort_list1 --$$")")) "[]" -- sort;

val arity_decls = repeat1 (names1 --$$ "::" -- !! arity)
  >> (mk_big_list o map mk_triple2 o split_decls);


(* mixfix annotations *)

val infxl = "infixl" $$-- !! nat >> cat "Infixl";
val infxr = "infixr" $$-- !! nat >> cat "Infixr";

val binder = "binder" $$-- !! (string -- nat) >> (cat "Binder" o mk_pair);

val opt_pris = optional ("[" $$-- !! (list nat --$$ "]")) [] >> mk_list;

val mixfix = string -- !! (opt_pris -- optional nat "max_pri")
  >> (cat "Mixfix" o mk_triple2);

fun opt_syn fx =
  "(" $$-- fx --$$ ")" ||
  empty >> K "NoSyn";

val opt_infix = opt_syn (infxl || infxr);
val opt_mixfix = opt_syn (mixfix || infxl || infxr || binder);


(* types *)

fun mk_old_type_decl ((ts, n), syn) =
  map (fn t => (mk_triple (t, n, syn), false)) ts;

fun mk_type_decl (((xs, t), None), syn) =
      [(mk_triple (t, string_of_int (length xs), syn), false)]
  | mk_type_decl (((xs, t), Some rhs), syn) =
      [(pars (commas [t, mk_list xs, rhs, syn]), true)];

fun mk_type_decls tys =
  "also add_types\n" ^ mk_big_list (keyfilter tys false) ^ "\n\n\
  \also add_tyabbrs\n" ^ mk_big_list (keyfilter tys true);


val old_type_decl = names -- nat -- opt_infix >> mk_old_type_decl;

val type_args =
  type_var >> (fn x => [x]) ||
  "(" $$-- !! (list1 type_var --$$ ")") ||
  empty >> K [];

val type_decl = type_args -- name -- optional ("=" $$-- !! string >> Some) None
  -- opt_infix >> mk_type_decl;

val type_decls = repeat1 (old_type_decl || type_decl)
  >> (rpair "" o mk_type_decls o flat);


(* consts *)

val const_decls = repeat1 (names1 --$$ "::" -- !! (string -- opt_mixfix))
  >> (mk_big_list o map mk_triple2 o split_decls);


(* translations *)

val trans_pat =
  optional ("(" $$-- !! (name --$$ ")")) "\"logic\"" -- string >> mk_pair;

val trans_arrow =
  $$ "=>" >> K " |-> " ||
  $$ "<=" >> K " <-| " ||
  $$ "==" >> K " <-> ";

val trans_decls = repeat1 (trans_pat ^^ !! (trans_arrow ^^ trans_pat))
  >> mk_big_list;


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


(* axclass *)

fun mk_axclass_decl ((c, cs), axms) =
  (mk_pair (c, cs) ^ "\n" ^ mk_axms axms,
    (strip_quotes c ^ "I") :: map fst axms);

val axclass_decl = subclass -- repeat (ident -- !! string) >> mk_axclass_decl;


(* instance *)

fun mk_instance_decl ((((t, ss), c), axths), opt_tac) =
  mk_triple (t, ss, c) ^ "\n" ^
  mk_list (keyfilter axths false) ^ "\n" ^
  mk_list (keyfilter axths true) ^ "\n" ^
  opt_tac;

val axm_or_thm =
  string >> rpair false ||
  long_id >> rpair true;

val instance_decl =
  name --$$ "::" -- optional ("(" $$-- sort_list1 --$$")") "[]" -- name --
  optional ("(" $$-- list1 axm_or_thm --$$ ")") [] --
  optional (verbatim >> (pars o cat "Some" o pars)) "None"
  >> mk_instance_decl;



(** theory syntax **)

type syntax =
  lexicon * (token list -> (string * string) * token list) Symtab.table;

fun make_syntax keywords sects =
  (make_lexicon keywords, Symtab.make sects handle Symtab.DUPS names
    => error ("Duplicate sections in thy syntax: " ^ commas_quote names));


(* header *)

fun mk_header (thy_name, bases) =
  (thy_name, "(base_on " ^ mk_list bases ^ " " ^ quote thy_name ^ ")");

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

fun mk_structure ((thy_name, old_thys), Some (extxt, postxt, mltxt)) =
      "structure " ^ thy_name ^ " =\n\
      \struct\n\
      \\n\
      \local\n"              ^ " open Mixfix;\n"  (* FIXME tmp *)
      ^ trfun_defs ^ "\n\
      \in\n\
      \\n"
      ^ mltxt ^ "\n\
      \\n\
      \val thy = " ^ old_thys ^ "\n\n\
      \also add_trfuns\n"
      ^ trfun_args ^ "\n\
      \\n"
      ^ extxt ^ "\n\
      \\n\
      \also add_thyname " ^ quote thy_name ^ ";\n\
      \\n\
      \\n"
      ^ postxt ^ "\n\
      \\n\
      \end;\n\
      \end;\n"
  | mk_structure ((thy_name, old_thys), None) =
      "structure " ^ thy_name ^ " =\n\
      \struct\n\
      \\n\
      \val thy = " ^ old_thys ^ ";\n\
      \\n\
      \end;\n";

fun theory_defn sectab =
  header -- optional (extension sectab >> Some) None -- eof
  >> (mk_structure o #1);

fun parse_thy (lex, sectab) str =
  #1 (!! (theory_defn sectab) (tokenize lex str));


(* standard sections *)

fun mk_val ax = "val " ^ ax ^ " = get_axiom thy " ^ quote ax ^ ";";

fun mk_axm_sect pretxt (txt, axs) =
  (pretxt ^ "\n" ^ txt, cat_lines (map mk_val axs));

fun axm_section name pretxt parse =
  (name, parse >> mk_axm_sect pretxt);

fun section name pretxt parse =
  axm_section name pretxt (parse >> rpair []);


val pure_keywords =
 ["classes", "default", "types", "arities", "consts", "syntax",
  "translations", "MLtrans", "MLtext", "rules", "defns", "axclass",
  "instance", "end", "ML", "mixfix", "infixr", "infixl", "binder", "=", "+",
  ",", "<", "{", "}", "(", ")", "[", "]", "::", "==", "=>", "<="];

val pure_sections =
 [section "classes" "also add_classes" class_decls,
  section "default" "also add_defsort" sort,
  ("types", type_decls),
  section "arities" "also add_arities" arity_decls,
  section "consts" "also add_consts" const_decls,
  section "syntax" "also add_syntax" const_decls,
  section "translations" "also add_trrules" trans_decls,
  section "MLtrans" "also add_trfuns" mltrans,
  ("MLtext", verbatim >> rpair ""),
  axm_section "rules" "also add_axioms" axiom_decls,
  axm_section "defns" "also add_defns" axiom_decls,
  axm_section "axclass" "also add_axclass" axclass_decl,
  section "instance" "also add_instance" instance_decl];


(* FIXME -> thy_read.ML *)
val pure_syntax = make_syntax pure_keywords pure_sections;

end;

