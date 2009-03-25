(*  Title:      Pure/Isar/spec_parse.ML
    Author:     Makarius

Parsers for complex specifications.
*)

signature SPEC_PARSE =
sig
  val attrib: Attrib.src parser
  val attribs: Attrib.src list parser
  val opt_attribs: Attrib.src list parser
  val thm_name: string -> Attrib.binding parser
  val opt_thm_name: string -> Attrib.binding parser
  val spec: (Attrib.binding * string) parser
  val specs: (Attrib.binding * string list) parser
  val alt_specs: (Attrib.binding * string) list parser
  val where_alt_specs: (Attrib.binding * string) list parser
  val xthm: (Facts.ref * Attrib.src list) parser
  val xthms1: (Facts.ref * Attrib.src list) list parser
  val name_facts: (Attrib.binding * (Facts.ref * Attrib.src list) list) list parser
  val locale_mixfix: mixfix parser
  val locale_fixes: (binding * string option * mixfix) list parser
  val locale_insts: (string option list * (Attrib.binding * string) list) parser
  val class_expr: string list parser
  val locale_expression: Expression.expression parser
  val locale_keyword: string parser
  val context_element: Element.context parser
  val statement: (Attrib.binding * (string * string list) list) list parser
  val general_statement: (Element.context list * Element.statement) parser
  val statement_keyword: string parser
end;

structure SpecParse: SPEC_PARSE =
struct

structure P = OuterParse;


(* theorem specifications *)

val attrib = P.position ((P.keyword_ident_or_symbolic || P.xname) -- P.!!! Args.parse) >> Args.src;
val attribs = P.$$$ "[" |-- P.list attrib --| P.$$$ "]";
val opt_attribs = Scan.optional attribs [];

fun thm_name s = P.binding -- opt_attribs --| P.$$$ s;

fun opt_thm_name s =
  Scan.optional ((P.binding -- opt_attribs || attribs >> pair Binding.empty) --| P.$$$ s)
    Attrib.empty_binding;

val spec = opt_thm_name ":" -- P.prop;
val specs = opt_thm_name ":" -- Scan.repeat1 P.prop;

val alt_specs =
  P.enum1 "|" (spec --| Scan.option (Scan.ahead (P.name || P.$$$ "[") -- P.!!! (P.$$$ "|")));

val where_alt_specs = P.where_ |-- P.!!! alt_specs;

val xthm =
  P.$$$ "[" |-- attribs --| P.$$$ "]" >> pair (Facts.named "") ||
  (P.alt_string >> Facts.Fact ||
    P.position P.xname -- Scan.option Attrib.thm_sel >> Facts.Named) -- opt_attribs;

val xthms1 = Scan.repeat1 xthm;

val name_facts = P.and_list1 (opt_thm_name "=" -- xthms1);


(* locale and context elements *)

val locale_mixfix = P.$$$ "(" -- P.$$$ "structure" -- P.!!! (P.$$$ ")") >> K Structure || P.mixfix;

val locale_fixes =
  P.and_list1 (P.binding -- Scan.option (P.$$$ "::" |-- P.typ) -- locale_mixfix
    >> (single o P.triple1) ||
  P.params >> map Syntax.no_syn) >> flat;

val locale_insts =
  Scan.optional (P.$$$ "[" |-- P.!!! (Scan.repeat1 (P.maybe P.term) --| P.$$$ "]")) []
  -- Scan.optional (P.$$$ "where" |-- P.and_list1 (opt_thm_name ":" -- P.prop)) [];

local

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

val prefix = P.name -- Scan.optional (P.$$$ "!" >> K true) false --| P.$$$ ":";
val named = P.name -- (P.$$$ "=" |-- P.term);
val position = P.maybe P.term;
val instance = P.$$$ "where" |-- P.and_list1 named >> Expression.Named ||
  Scan.repeat1 position >> Expression.Positional;

in

val locale_keyword = P.$$$ "fixes" || P.$$$ "constrains" || P.$$$ "assumes" ||
   P.$$$ "defines" || P.$$$ "notes";

val class_expr = plus1_unless locale_keyword P.xname;

val locale_expression =
  let
    val expr2 = P.xname;
    val expr1 = Scan.optional prefix ("", false) -- expr2 --
      Scan.optional instance (Expression.Named []) >> (fn ((p, l), i) => (l, (p, i)));
    val expr0 = plus1_unless locale_keyword expr1;
  in expr0 -- Scan.optional (P.$$$ "for" |-- P.!!! locale_fixes) [] end;

val context_element = P.group "context element" loc_element;

end;


(* statements *)

val statement = P.and_list1 (opt_thm_name ":" -- Scan.repeat1 P.propp);

val obtain_case =
  P.parbinding -- (Scan.optional (P.simple_fixes --| P.$$$ "where") [] --
    (P.and_list1 (Scan.repeat1 P.prop) >> flat));

val general_statement =
  statement >> (fn x => ([], Element.Shows x)) ||
  Scan.repeat context_element --
   (P.$$$ "obtains" |-- P.!!! (P.enum1 "|" obtain_case) >> Element.Obtains ||
    P.$$$ "shows" |-- P.!!! statement >> Element.Shows);

val statement_keyword = P.$$$ "obtains" || P.$$$ "shows";

end;
