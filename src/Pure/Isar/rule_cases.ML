(*  Title:      Pure/Isar/rule_cases.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Manage local contexts of rules.
*)

signature RULE_CASES =
sig
  val consumes: int -> 'a attribute
  val consumes_default: int -> 'a attribute
  val name: string list -> thm -> thm
  val case_names: string list -> 'a attribute
  val get: thm -> string list * int
  val add: thm -> thm * (string list * int)
  val save: thm -> thm -> thm
  type T
  val make: bool -> thm -> string list -> (string * T) list
  val make_raw: bool -> thm -> string list -> (string * T) list
  val rename_params: string list list -> thm -> thm
  val params: string list list -> 'a attribute
end;

structure RuleCases: RULE_CASES =
struct

(* names *)

val consumes_tagN = "consumes";
val cases_tagN = "cases";
val case_conclN = "case";


(* number of consumed facts *)

fun lookup_consumes thm = Library.assoc (Thm.tags_of_thm thm, consumes_tagN);

fun get_consumes thm =
  let fun err () = raise THM ("Malformed 'consumes' tag of theorem", 0, [thm]) in
    (case lookup_consumes thm of
      None => 0
    | Some [s] => (case Syntax.read_nat s of Some n => n | _ => err ())
    | _ => err ())
  end;

fun put_consumes n = Drule.tag_rule (consumes_tagN, [Library.string_of_int n]);
val save_consumes = put_consumes o get_consumes;

fun consumes n x = Drule.rule_attribute (K (put_consumes n)) x;
fun consumes_default n x = if Library.is_some (lookup_consumes (#2 x)) then x else consumes n x;


(* case names *)

fun name names thm =
  thm
  |> Drule.untag_rule cases_tagN
  |> Drule.tag_rule (cases_tagN, names);

fun get_case_names thm = Library.assocs (Thm.tags_of_thm thm) cases_tagN;
val save_case_names = name o get_case_names;

fun case_names ss = Drule.rule_attribute (K (name ss));


(* access hints *)

fun get thm = (get_case_names thm, get_consumes thm);
fun add thm = (thm, get thm);

fun save thm = save_case_names thm o save_consumes thm;


(* prepare cases *)

type T = {fixes: (string * typ) list, assumes: term list, binds: (indexname * term option) list};

local

fun prep_case raw open_parms thm name i =
  let
    val (_, _, Bi, _) = Thm.dest_state (thm, i)
      handle THM _ => raise THM ("More cases than premises in rule", 0, [thm]);
    val xs = map (if open_parms then I else apfst Syntax.internal) (Logic.strip_params Bi);
    val asms = map (curry Term.list_abs xs) (Logic.strip_assums_hyp Bi);
    val concl = Term.list_abs (xs, Logic.strip_assums_concl Bi);
    val bind = ((case_conclN, 0), Some (if raw then concl else AutoBind.drop_judgment concl));
  in (name, {fixes = xs, assumes = asms, binds = [bind]}) end;

fun gen_make raw open_parms raw_thm names =
  let val thm = Tactic.norm_hhf raw_thm in
    #1 (foldr (fn (name, (cases, i)) => (prep_case raw open_parms thm name i :: cases, i - 1))
      (Library.drop (length names - Thm.nprems_of thm, names), ([], Thm.nprems_of thm)))
  end;

in

fun make x = gen_make false x;
fun make_raw x = gen_make true x;

end;


(* params *)

fun rename_params xss thm =
  #1 (foldl (fn ((th, i), xs) => (Thm.rename_params_rule (xs, i) th, i + 1)) ((thm, 1), xss))
  |> save thm;

fun params xss = Drule.rule_attribute (K (rename_params xss));


end;
