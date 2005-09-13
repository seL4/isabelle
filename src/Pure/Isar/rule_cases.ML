(*  Title:      Pure/Isar/rule_cases.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

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
  val make: bool -> term option -> theory * term -> string list -> (string * T option) list
  val simple: bool -> theory * term -> string -> string * T option
  val rename_params: string list list -> thm -> thm
  val params: string list list -> 'a attribute
  type tactic
  val NO_CASES: Tactical.tactic -> tactic
end;

structure RuleCases: RULE_CASES =
struct

(* names *)

val consumes_tagN = "consumes";
val cases_tagN = "cases";
val case_conclN = "case";
val case_hypsN = "hyps";
val case_premsN = "prems";


(* number of consumed facts *)

fun lookup_consumes thm =
  let fun err () = raise THM ("Malformed 'consumes' tag of theorem", 0, [thm]) in
    (case AList.lookup (op =) (Thm.tags_of_thm thm) (consumes_tagN) of
      NONE => NONE
    | SOME [s] => (case Syntax.read_nat s of SOME n => SOME n | _ => err ())
    | _ => err ())
  end;

fun put_consumes NONE th = th
  | put_consumes (SOME n) th = th
      |> Drule.untag_rule consumes_tagN
      |> Drule.tag_rule (consumes_tagN, [Library.string_of_int n]);

val save_consumes = put_consumes o lookup_consumes;

fun consumes n x = Drule.rule_attribute (K (put_consumes (SOME n))) x;
fun consumes_default n x =
  if Library.is_some (lookup_consumes (#2 x)) then x else consumes n x;


(* case names *)

fun put_case_names NONE thm = thm
  | put_case_names (SOME names) thm =
      thm
      |> Drule.untag_rule cases_tagN
      |> Drule.tag_rule (cases_tagN, names);

fun lookup_case_names thm = AList.lookup (op =) (Thm.tags_of_thm thm) cases_tagN;

val save_case_names = put_case_names o lookup_case_names;
val name = put_case_names o SOME;
fun case_names ss = Drule.rule_attribute (K (name ss));


(* access hints *)

fun save thm = save_case_names thm o save_consumes thm;

fun get thm =
  let
    val n = if_none (lookup_consumes thm) 0;
    val ss =
      (case lookup_case_names thm of
        NONE => map Library.string_of_int (1 upto (Thm.nprems_of thm - n))
      | SOME ss => ss);
  in (ss, n) end;

fun add thm = (thm, get thm);


(* prepare cases *)

type T =
 {fixes: (string * typ) list,
  assumes: (string * term list) list,
  binds: (indexname * term option) list};

fun unskolem x =
  (case try Syntax.dest_skolem x of SOME x' => x' | NONE => x);

fun prep_case is_open thy (split, raw_prop) name =
  let
    val prop = Drule.norm_hhf thy raw_prop;

    val xs = map (apfst unskolem) (Logic.strip_params prop);
    val rename = if is_open then I else map (apfst Syntax.internal);
    val named_xs =
      (case split of
        NONE => rename xs
      | SOME t =>
          let val (us, vs) = splitAt (length (Logic.strip_params t), xs)
          in rename us @ vs end);

    val asms = map (curry Term.list_abs named_xs) (Logic.strip_assums_hyp prop);
    val named_asms =
      (case split of
        NONE => [("", asms)]
      | SOME t =>
          let val (hyps, prems) = splitAt (length (Logic.strip_assums_hyp t), asms)
          in [(case_hypsN, hyps), (case_premsN, prems)] end);

    val concl = Term.list_abs (named_xs, Logic.strip_assums_concl prop);
    val bind = ((case_conclN, 0), SOME (ObjectLogic.drop_judgment thy concl));
  in (name, SOME {fixes = named_xs, assumes = named_asms, binds = [bind]}) end;

fun make is_open split (thy, prop) names =
  let
    val nprems = Logic.count_prems (prop, 0);
    fun add_case name (cases, i) =
      ((case try (fn () =>
          (Option.map (curry Logic.nth_prem i) split, Logic.nth_prem (i, prop))) () of
        NONE => (name, NONE)
      | SOME sp => prep_case is_open thy sp name) :: cases, i - 1);
  in
    fold_rev add_case (Library.drop (length names - nprems, names)) ([], length names)
    |> #1
  end;

fun simple is_open (thy, prop) = prep_case is_open thy (NONE, prop);


(* params *)

fun rename_params xss thm = foldln Thm.rename_params_rule xss thm
  |> save thm;

fun params xss = Drule.rule_attribute (K (rename_params xss));


(* tactics with cases *)

type tactic = thm -> (thm * (string * T option) list) Seq.seq;

fun NO_CASES tac = Seq.map (rpair []) o tac;

end;

val NO_CASES = RuleCases.NO_CASES;
