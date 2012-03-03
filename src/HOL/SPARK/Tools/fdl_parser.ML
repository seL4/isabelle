(*  Title:      HOL/SPARK/Tools/fdl_parser.ML
    Author:     Stefan Berghofer
    Copyright:  secunet Security Networks AG

Parser for fdl files.
*)

signature FDL_PARSER =
sig
  datatype expr =
      Ident of string
    | Number of int
    | Quantifier of string * string list * string * expr
    | Funct of string * expr list
    | Element of expr * expr list
    | Update of expr * expr list * expr
    | Record of string * (string * expr) list
    | Array of string * expr option *
        ((expr * expr option) list list * expr) list;

  datatype fdl_type =
      Basic_Type of string
    | Enum_Type of string list
    | Array_Type of string list * string
    | Record_Type of (string list * string) list
    | Pending_Type;

  datatype fdl_rule =
      Inference_Rule of expr list * expr
    | Substitution_Rule of expr list * expr * expr;

  type rules =
    ((string * int) * fdl_rule) list *
    (string * (expr * (string * string) list) list) list;

  type vcs = (string * (string *
    ((string * expr) list * (string * expr) list)) list) list;

  type 'a tab = 'a Symtab.table * (string * 'a) list;

  val lookup: 'a tab -> string -> 'a option;
  val update: string * 'a -> 'a tab -> 'a tab;
  val items: 'a tab -> (string * 'a) list;

  type decls =
    {types: fdl_type tab,
     vars: string tab,
     consts: string tab,
     funs: (string list * string) tab};

  val parse_vcs: (Fdl_Lexer.chars -> 'a * Fdl_Lexer.chars) -> Position.T ->
    string -> 'a * ((string * string) * vcs);

  val parse_declarations:  Position.T -> string -> (string * string) * decls;

  val parse_rules: Position.T -> string -> rules;
end;

structure Fdl_Parser: FDL_PARSER =
struct

(** error handling **)

fun beginning n cs =
  let val dots = if length cs > n then " ..." else "";
  in
    space_implode " " (take n cs) ^ dots
  end;

fun !!! scan =
  let
    fun get_pos [] = " (past end-of-file!)"
      | get_pos (tok :: _) = Fdl_Lexer.pos_of tok;

    fun err (syms, msg) = fn () =>
      "Syntax error" ^ get_pos syms ^ " at " ^
        beginning 10 (map Fdl_Lexer.unparse syms) ^
        (case msg of NONE => "" | SOME m => "\n" ^ m () ^ " expected");
  in Scan.!! err scan end;

fun parse_all p =
  Scan.repeat (Scan.unless (Scan.one Fdl_Lexer.is_eof) (!!! p));


(** parsers **)

fun group s p = p || Scan.fail_with (K (fn () => s));

fun $$$ s = group s
  (Scan.one (fn t => Fdl_Lexer.kind_of t = Fdl_Lexer.Keyword andalso
     Fdl_Lexer.content_of t = s) >> K s);

val identifier = group "identifier"
  (Scan.one (fn t => Fdl_Lexer.kind_of t = Fdl_Lexer.Ident) >>
     Fdl_Lexer.content_of);

val long_identifier = group "long identifier"
  (Scan.one (fn t => Fdl_Lexer.kind_of t = Fdl_Lexer.Long_Ident) >>
     Fdl_Lexer.content_of);

fun the_identifier s = group s
  (Scan.one (fn t => Fdl_Lexer.kind_of t = Fdl_Lexer.Ident andalso
     Fdl_Lexer.content_of t = s) >> K s);

fun prfx_identifier g s = group g
  (Scan.one (fn t => Fdl_Lexer.kind_of t = Fdl_Lexer.Ident andalso
     can (unprefix s) (Fdl_Lexer.content_of t)) >>
     (unprefix s o Fdl_Lexer.content_of));

val mk_identifier = prfx_identifier "identifier \"mk__...\"" "mk__";
val hyp_identifier = prfx_identifier "hypothesis identifer" "H";
val concl_identifier = prfx_identifier "conclusion identifier" "C";

val number = group "number"
  (Scan.one (fn t => Fdl_Lexer.kind_of t = Fdl_Lexer.Number) >>
     (the o Int.fromString o Fdl_Lexer.content_of));

val traceability = group "traceability information"
  (Scan.one (fn t => Fdl_Lexer.kind_of t = Fdl_Lexer.Traceability) >>
     Fdl_Lexer.content_of);

fun enum1 sep scan = scan ::: Scan.repeat ($$$ sep |-- !!! scan);
fun enum sep scan = enum1 sep scan || Scan.succeed [];

fun list1 scan = enum1 "," scan;
fun list scan = enum "," scan;


(* expressions, see section 4.4 of SPARK Proof Manual *)

datatype expr =
    Ident of string
  | Number of int
  | Quantifier of string * string list * string * expr
  | Funct of string * expr list
  | Element of expr * expr list
  | Update of expr * expr list * expr
  | Record of string * (string * expr) list
  | Array of string * expr option *
      ((expr * expr option) list list * expr) list;

fun unop (f, x) = Funct (f, [x]);

fun binop p q = p :|-- (fn x => Scan.optional
  (q -- !!! p >> (fn (f, y) => Funct (f, [x, y]))) x);

(* left-associative *)
fun binops opp argp =
  argp -- Scan.repeat (opp -- !!! argp) >> (fn (x, fys) =>
    fold (fn (f, y) => fn x => Funct (f, [x, y])) fys x);

(* right-associative *)
fun binops' f p = enum1 f p >> foldr1 (fn (x, y) => Funct (f, [x, y]));

val multiplying_operator = $$$ "*" || $$$ "/" || $$$ "div" || $$$ "mod";

val adding_operator = $$$ "+" || $$$ "-";

val relational_operator =
     $$$ "=" || $$$ "<>"
  || $$$ "<" || $$$ ">"
  || $$$ "<="|| $$$ ">=";

val quantification_kind = $$$ "for_all" || $$$ "for_some";

val quantification_generator =
  list1 identifier --| $$$ ":" -- identifier;

fun expression xs = group "expression"
  (binop disjunction ($$$ "->" || $$$ "<->")) xs

and disjunction xs = binops' "or" conjunction xs

and conjunction xs = binops' "and" negation xs

and negation xs =
  (   $$$ "not" -- !!! relation >> unop
   || relation) xs

and relation xs = binop sum relational_operator xs

and sum xs = binops adding_operator term xs

and term xs = binops multiplying_operator factor xs

and factor xs =
  (   $$$ "+" |-- !!! primary
   || $$$ "-" -- !!! primary >> unop
   || binop primary ($$$ "**")) xs

and primary xs = group "primary"
  (   number >> Number
   || $$$ "(" |-- !!! (expression --| $$$ ")")
   || quantified_expression
   || function_designator
   || identifier >> Ident) xs

and quantified_expression xs = (quantification_kind --
  !!! ($$$ "(" |-- quantification_generator --|  $$$ "," --
    expression --| $$$ ")") >> (fn (q, ((xs, T), e)) =>
      Quantifier (q, xs, T, e))) xs

and function_designator xs =
  (   mk_identifier --| $$$ "(" :|--
        (fn s => record_args s || array_args s) --| $$$ ")"
   || $$$ "element" |-- !!! ($$$ "(" |-- expression --| $$$ "," --| $$$ "[" --
        list1 expression --| $$$ "]" --| $$$ ")") >> Element
   || $$$ "update" |-- !!! ($$$ "(" |-- expression --| $$$ "," --| $$$ "[" --
        list1 expression --| $$$ "]" --| $$$ "," -- expression --| $$$ ")") >>
          (fn ((A, xs), x) => Update (A, xs, x))
   || identifier --| $$$ "(" -- !!! (list1 expression --| $$$ ")") >> Funct) xs

and record_args s xs =
  (list1 (identifier --| $$$ ":=" -- !!! expression) >> (pair s #> Record)) xs

and array_args s xs =
  (   expression -- Scan.optional ($$$ "," |-- !!! array_associations) [] >>
        (fn (default, assocs) => Array (s, SOME default, assocs))
   || array_associations >> (fn assocs => Array (s, NONE, assocs))) xs

and array_associations xs =
  (list1 (enum1 "&" ($$$ "[" |--
     !!! (list1 (expression -- Scan.option ($$$ ".." |-- !!! expression)) --|
       $$$ "]")) --| $$$ ":=" -- expression)) xs;


(* verification conditions *)

type vcs = (string * (string *
  ((string * expr) list * (string * expr) list)) list) list;

val vc =
  identifier --| $$$ "." -- !!!
    (   $$$ "***" |-- !!! (the_identifier "true" --| $$$ ".") >>
          (Ident #> pair "1" #> single #> pair [])
     || $$$ "!!!" |-- !!! (the_identifier "false" --| $$$ ".") >>
          (Ident #> pair "1" #> single #> pair [])
     || Scan.repeat1 (hyp_identifier --
          !!! ($$$ ":" |-- expression --| $$$ ".")) --| $$$ "->" --
        Scan.repeat1 (concl_identifier --
          !!! ($$$ ":" |-- expression --| $$$ ".")));

val subprogram_kind = $$$ "function" || $$$ "procedure";

val vcs =
  subprogram_kind -- (long_identifier || identifier) --
  parse_all (traceability -- !!! (Scan.repeat1 vc));

fun parse_vcs header pos s =
  s |>
  Fdl_Lexer.tokenize header Fdl_Lexer.c_comment pos ||>
  filter Fdl_Lexer.is_proper ||>
  Scan.finite Fdl_Lexer.stopper (Scan.error (!!! vcs)) ||>
  fst;


(* fdl declarations, see section 4.3 of SPARK Proof Manual *)

datatype fdl_type =
    Basic_Type of string
  | Enum_Type of string list
  | Array_Type of string list * string
  | Record_Type of (string list * string) list
  | Pending_Type;

(* also store items in a list to preserve order *)
type 'a tab = 'a Symtab.table * (string * 'a) list;

fun lookup ((tab, _) : 'a tab) = Symtab.lookup tab;
fun update decl (tab, items) = (Symtab.update_new decl tab, decl :: items);
fun items ((_, items) : 'a tab) = rev items;

type decls =
  {types: fdl_type tab,
   vars: string tab,
   consts: string tab,
   funs: (string list * string) tab};

val empty_decls : decls =
  {types = (Symtab.empty, []), vars = (Symtab.empty, []),
   consts = (Symtab.empty, []), funs = (Symtab.empty, [])};

fun add_type_decl decl {types, vars, consts, funs} =
  {types = update decl types,
   vars = vars, consts = consts, funs = funs}
  handle Symtab.DUP s => error ("Duplicate type " ^ s);

fun add_var_decl (vs, ty) {types, vars, consts, funs} =
  {types = types,
   vars = fold (update o rpair ty) vs vars,
   consts = consts, funs = funs}
  handle Symtab.DUP s => error ("Duplicate variable " ^ s);

fun add_const_decl decl {types, vars, consts, funs} =
  {types = types, vars = vars,
   consts = update decl consts,
   funs = funs}
  handle Symtab.DUP s => error ("Duplicate constant " ^ s);

fun add_fun_decl decl {types, vars, consts, funs} =
  {types = types, vars = vars, consts = consts,
   funs = update decl funs}
  handle Symtab.DUP s => error ("Duplicate function " ^ s);

fun type_decl x = ($$$ "type" |-- !!! (identifier --| $$$ "=" --
  (   identifier >> Basic_Type
   || $$$ "(" |-- !!! (list1 identifier --| $$$ ")") >> Enum_Type
   || $$$ "array" |-- !!! ($$$ "[" |-- list1 identifier --| $$$ "]" --|
        $$$ "of" -- identifier) >> Array_Type
   || $$$ "record" |-- !!! (enum1 ";"
        (list1 identifier -- !!! ($$$ ":" |-- identifier)) --|
           $$$ "end") >> Record_Type
   || $$$ "pending" >> K Pending_Type)) >> add_type_decl) x;

fun const_decl x = ($$$ "const" |-- !!! (identifier --| $$$ ":" -- identifier --|
  $$$ "=" --| $$$ "pending") >> add_const_decl) x;

fun var_decl x = ($$$ "var" |-- !!! (list1 identifier --| $$$ ":" -- identifier) >>
  add_var_decl) x;

fun fun_decl x = ($$$ "function" |-- !!! (identifier --
  (Scan.optional ($$$ "(" |-- !!! (list1 identifier --| $$$ ")")) [] --|
   $$$ ":" -- identifier)) >> add_fun_decl) x;

fun declarations x =
 ($$$ "title" |-- subprogram_kind -- identifier --| $$$ ";" --
  (Scan.repeat ((type_decl || const_decl || var_decl || fun_decl) --|
     !!! ($$$ ";")) >> (fn ds => fold I ds empty_decls)) --|
  $$$ "end" --| $$$ ";") x;

fun parse_declarations pos s =
  s |>
  Fdl_Lexer.tokenize (Scan.succeed ()) Fdl_Lexer.curly_comment pos |>
  snd |> filter Fdl_Lexer.is_proper |>
  Scan.finite Fdl_Lexer.stopper (Scan.error (!!! declarations)) |>
  fst;


(* rules, see section 5 of SPADE Proof Checker Rules Manual *)

datatype fdl_rule =
    Inference_Rule of expr list * expr
  | Substitution_Rule of expr list * expr * expr;

type rules =
  ((string * int) * fdl_rule) list *
  (string * (expr * (string * string) list) list) list;

val condition_list = $$$ "[" |-- list expression --| $$$ "]";
val if_condition_list = $$$ "if" |-- !!! condition_list;

val rule =
  identifier -- !!! ($$$ "(" |-- number --| $$$ ")" --| $$$ ":" --
  (expression :|-- (fn e =>
        $$$ "may_be_deduced" >> K (Inference_Rule ([], e))
     || $$$ "may_be_deduced_from" |--
          !!! condition_list >> (Inference_Rule o rpair e)
     || $$$ "may_be_replaced_by" |-- !!! (expression --
          Scan.optional if_condition_list []) >> (fn (e', cs) =>
            Substitution_Rule (cs, e, e'))
     || $$$ "&" |-- !!! (expression --| $$$ "are_interchangeable" --
          Scan.optional if_condition_list []) >> (fn (e', cs) =>
            Substitution_Rule (cs, e, e')))) --| $$$ ".") >>
    (fn (id, (n, rl)) => ((id, n), rl));

val rule_family = 
  $$$ "rule_family" |-- identifier --| $$$ ":" --
  enum1 "&" (expression -- !!! ($$$ "requires" |-- $$$ "[" |--
    list (identifier -- !!! ($$$ ":" |-- identifier)) --| $$$ "]")) --|
  $$$ ".";

val rules =
  parse_all (rule >> (apfst o cons) || rule_family >> (apsnd o cons)) >>
  (fn rls => fold_rev I rls ([], []));

fun parse_rules pos s =
  s |>
  Fdl_Lexer.tokenize (Scan.succeed ())
    (Fdl_Lexer.c_comment || Fdl_Lexer.percent_comment) pos |>
  snd |> filter Fdl_Lexer.is_proper |>
  Scan.finite Fdl_Lexer.stopper (Scan.error (!!! rules)) |>
  fst;

end;
