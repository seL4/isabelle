(*  Title:      Pure/Isar/spec_parse.ML
    ID:         $Id$
    Author:     Makarius

Parsers for complex specifications.
*)

signature SPEC_PARSE =
sig
  type token
  val attrib: OuterLex.token list -> Attrib.src * token list
  val attribs: token list -> Attrib.src list * token list
  val opt_attribs: token list -> Attrib.src list * token list
  val thm_name: string -> token list -> (bstring * Attrib.src list) * token list
  val opt_thm_name: string -> token list -> (bstring * Attrib.src list) * token list
  val spec: token list -> ((bstring * Attrib.src list) * string list) * token list
  val named_spec: token list -> ((bstring * Attrib.src list) * string list) * token list
  val spec_name: token list -> ((bstring * string) * Attrib.src list) * token list
  val spec_opt_name: token list -> ((bstring * string) * Attrib.src list) * token list
  val xthm: token list -> (Facts.ref * Attrib.src list) * token list
  val xthms1: token list -> (Facts.ref * Attrib.src list) list * token list
  val name_facts: token list ->
    ((bstring * Attrib.src list) * (Facts.ref * Attrib.src list) list) list * token list
  val locale_mixfix: token list -> mixfix * token list
  val locale_fixes: token list -> (string * string option * mixfix) list * token list
  val locale_insts: token list ->
    (string option list * ((bstring * Attrib.src list) * string) list) * token list
  val class_expr: token list -> string list * token list
  val locale_expr: token list -> Locale.expr * token list
  val locale_keyword: token list -> string * token list
  val locale_element: token list -> Element.context Locale.element * token list
  val context_element: token list -> Element.context * token list
  val statement: token list ->
    ((bstring * Attrib.src list) * (string * string list) list) list * token list
  val general_statement: token list ->
    (Element.context Locale.element list * Element.statement) * OuterLex.token list
  val statement_keyword: token list -> string * token list
  val specification: token list ->
    (string *
      (((bstring * Attrib.src list) * string list) list * (string * string option) list)) list *
    token list
end;

structure SpecParse: SPEC_PARSE =
struct

structure P = OuterParse;
type token = P.token;


(* theorem specifications *)

val attrib = P.position ((P.keyword_ident_or_symbolic || P.xname) -- P.!!! Args.parse) >> Args.src;
val attribs = P.$$$ "[" |-- P.list attrib --| P.$$$ "]";
val opt_attribs = Scan.optional attribs [];

fun thm_name s = P.name -- opt_attribs --| P.$$$ s;
fun opt_thm_name s =
  Scan.optional ((P.name -- opt_attribs || attribs >> pair "") --| P.$$$ s) ("", []);

val spec = opt_thm_name ":" -- Scan.repeat1 P.prop;
val named_spec = thm_name ":" -- Scan.repeat1 P.prop;

val spec_name = thm_name ":" -- P.prop >> (fn ((x, y), z) => ((x, z), y));
val spec_opt_name = opt_thm_name ":" -- P.prop >> (fn ((x, y), z) => ((x, z), y));

val xthm =
  P.$$$ "[" |-- attribs --| P.$$$ "]" >> pair (Facts.named "") ||
  (P.alt_string >> Facts.Fact ||
    P.position P.xname -- Scan.option Attrib.thm_sel >> Facts.Named) -- opt_attribs;

val xthms1 = Scan.repeat1 xthm;

val name_facts = P.and_list1 (opt_thm_name "=" -- xthms1);


(* locale and context elements *)

val locale_mixfix = P.$$$ "(" -- P.$$$ "structure" -- P.!!! (P.$$$ ")") >> K Structure || P.mixfix;

val locale_fixes =
  P.and_list1 (P.name -- Scan.option (P.$$$ "::" |-- P.typ) -- locale_mixfix
    >> (single o P.triple1) ||
  P.params >> map Syntax.no_syn) >> flat;

val locale_insts =
  Scan.optional (P.$$$ "[" |-- P.!!! (Scan.repeat1 (P.maybe P.term) --| P.$$$ "]")) []
  -- Scan.optional (P.$$$ "where" |-- P.and_list1 (opt_thm_name ":" -- P.prop)) [];

local

val loc_keyword = P.$$$ "fixes" || P.$$$ "constrains" || P.$$$ "assumes" ||
   P.$$$ "defines" || P.$$$ "notes" || P.$$$ "includes";

val loc_element =
  P.$$$ "fixes" |-- P.!!! locale_fixes >> Element.Fixes ||
  P.$$$ "constrains" |-- P.!!! (P.and_list1 (P.name -- (P.$$$ "::" |-- P.typ)))
    >> Element.Constrains ||
  P.$$$ "assumes" |-- P.!!! (P.and_list1 (opt_thm_name ":" -- Scan.repeat1 P.propp))
    >> Element.Assumes ||
  P.$$$ "defines" |-- P.!!! (P.and_list1 (opt_thm_name ":" -- P.propp))
    >> Element.Defines ||
  P.$$$ "notes" |-- P.!!! (P.and_list1 (opt_thm_name "=" -- xthms1))
    >> (curry Element.Notes "");

fun plus1_unless test scan =
  scan ::: Scan.repeat (P.$$$ "+" |-- Scan.unless test (P.!!! scan));

val rename = P.name -- Scan.option P.mixfix;

in

val class_expr = plus1_unless loc_keyword P.xname;

val locale_expr =
  let
    fun expr2 x = (P.xname >> Locale.Locale || P.$$$ "(" |-- P.!!! (expr0 --| P.$$$ ")")) x
    and expr1 x = (expr2 -- Scan.repeat1 (P.maybe rename) >> Locale.Rename || expr2) x
    and expr0 x = (plus1_unless loc_keyword expr1 >> (fn [e] => e | es => Locale.Merge es)) x;
  in expr0 end;

val locale_keyword = loc_keyword;

val locale_element = P.group "locale element"
  (loc_element >> Locale.Elem || P.$$$ "includes" |-- P.!!! locale_expr >> Locale.Expr);

val context_element = P.group "context element" loc_element;

end;


(* statements *)

val statement = P.and_list1 (opt_thm_name ":" -- Scan.repeat1 P.propp);

val obtain_case =
  P.parname -- (Scan.optional (P.simple_fixes --| P.$$$ "where") [] --
    (P.and_list1 (Scan.repeat1 P.prop) >> flat));

val general_statement =
  statement >> (fn x => ([], Element.Shows x)) ||
  Scan.repeat locale_element --
   (P.$$$ "obtains" |-- P.!!! (P.enum1 "|" obtain_case) >> Element.Obtains ||
    P.$$$ "shows" |-- P.!!! statement >> Element.Shows);

val statement_keyword = P.$$$ "obtains" || P.$$$ "shows";


(* specifications *)

val specification = P.enum1 "|" (P.parname -- (P.and_list1 spec -- P.for_simple_fixes));

end;
