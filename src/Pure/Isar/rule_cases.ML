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
  val save: thm -> thm -> thm
  val get: thm -> string list * int
  val add: thm -> thm * (string list * int)
  type T
  val empty: T
  val make: bool -> term option -> Sign.sg * term -> string list -> (string * T) list
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

fun lookup_consumes thm =
  let fun err () = raise THM ("Malformed 'consumes' tag of theorem", 0, [thm]) in
    (case Library.assoc (Thm.tags_of_thm thm, consumes_tagN) of
      None => None
    | Some [s] => (case Syntax.read_nat s of Some n => Some n | _ => err ())
    | _ => err ())
  end;

fun put_consumes None th = th
  | put_consumes (Some n) th = th
      |> Drule.untag_rule consumes_tagN
      |> Drule.tag_rule (consumes_tagN, [Library.string_of_int n]);

val save_consumes = put_consumes o lookup_consumes;

fun consumes n x = Drule.rule_attribute (K (put_consumes (Some n))) x;
fun consumes_default n x = if Library.is_some (lookup_consumes (#2 x)) then x else consumes n x;


(* case names *)

fun put_case_names None thm = thm
  | put_case_names (Some names) thm =
      thm
      |> Drule.untag_rule cases_tagN
      |> Drule.tag_rule (cases_tagN, names);

fun lookup_case_names thm = Library.assoc (Thm.tags_of_thm thm, cases_tagN);

val save_case_names = put_case_names o lookup_case_names;
val name = put_case_names o Some;
fun case_names ss = Drule.rule_attribute (K (name ss));


(* access hints *)

fun save thm = save_case_names thm o save_consumes thm;

fun get thm =
  let
    val n = if_none (lookup_consumes thm) 0;
    val ss =
      (case lookup_case_names thm of
        None => map Library.string_of_int (1 upto (Thm.nprems_of thm - n))
      | Some ss => ss);
  in (ss, n) end;

fun add thm = (thm, get thm);


(* prepare cases *)

type T =
 {fixes: (string * typ) list,
  assumes: (string * term list) list,
  binds: (indexname * term option) list};

val hypsN = "hyps";
val premsN = "prems";

val empty = {fixes = [], assumes = [], binds = []};

fun prep_case is_open split sg prop name i =
  let
    val Bi = Drule.norm_hhf sg (hd (#1 (Logic.strip_prems (i, [], Logic.skip_flexpairs prop))));
    val xs = map (if is_open then I else apfst Syntax.internal) (Logic.strip_params Bi);
    val asms = map (curry Term.list_abs xs) (Logic.strip_assums_hyp Bi);
    val named_asms =
      (case split of None => [("", asms)]
      | Some t =>
          let val h = length (Logic.strip_assums_hyp
            (hd (#1 (Logic.strip_prems (i, [], Logic.skip_flexpairs t)))))
          in [(hypsN, Library.take (h, asms)), (premsN, Library.drop (h, asms))] end);
    val concl = Term.list_abs (xs, Logic.strip_assums_concl Bi);
    val bind = ((case_conclN, 0), Some (ObjectLogic.drop_judgment sg concl));
  in (name, {fixes = xs, assumes = named_asms, binds = [bind]}) end;

fun make is_open split (sg, prop) names =
  let val nprems = Logic.count_prems (Logic.skip_flexpairs prop, 0) in
    foldr (fn (name, (cases, i)) => (prep_case is_open split sg prop name i :: cases, i - 1))
      (Library.drop (length names - nprems, names), ([], length names)) |> #1
  end;


(* params *)

fun rename_params xss thm = foldln Thm.rename_params_rule xss thm
  |> save thm;

fun params xss = Drule.rule_attribute (K (rename_params xss));

end;
