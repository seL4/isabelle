(*  Title:      Pure/Isar/rule_cases.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Manage local contexts of rules.
*)

signature RULE_CASES =
sig
  type T (* = (string * typ) list * term list *)
  val name: string list -> thm -> thm
  val case_names: string list -> 'a attribute
  val get: thm -> string list
  val add: thm -> thm * string list
  val none: thm -> thm * string list
  val make: bool -> thm -> string list -> (string * T) list
  val rename_params: string list list -> thm -> thm
  val params: string list list -> 'a attribute
end;

structure RuleCases: RULE_CASES =
struct


(* local contexts *)

type T = (string * typ) list * term list;
val casesN = "cases";


(* case names *)

fun name names thm =
  thm
  |> Drule.untag_rule casesN
  |> Drule.tag_rule (casesN, names);

fun case_names ss = Drule.rule_attribute (K (name ss));

fun get thm = Library.assocs (Thm.tags_of_thm thm) casesN;
fun add thm = (thm, get thm);
fun none thm = (thm, []);


(* prepare cases *)

fun prep_case open_parms thm name i =
  let
    val (_, _, Bi, _) = Thm.dest_state (thm, i)
      handle THM _ => raise THM ("More cases than premises in rule", 0, [thm]);
    val rev_params = map (if open_parms then I else apfst Syntax.internal)
      (rename_wrt_term Bi (Logic.strip_params Bi));
    val rev_frees = map Free rev_params;
    val props = map (fn t => Term.subst_bounds (rev_frees, t)) (Logic.strip_assums_hyp Bi);
  in (name, (rev rev_params, props)) end;

fun make open_parms thm names =
  #1 (foldr (fn (name, (cases, i)) => (prep_case open_parms thm name i :: cases, i - 1))
    (Library.drop (length names - Thm.nprems_of thm, names), ([], Thm.nprems_of thm)));


(* params *)

fun rename_params xss thm =
  #1 (foldl (fn ((th, i), xs) => (Thm.rename_params_rule (xs, i) th, i + 1)) ((thm, 1), xss))
  |> name (get thm);

fun params xss = Drule.rule_attribute (K (rename_params xss));


end;
