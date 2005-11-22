(*  Title:      Pure/Isar/rule_cases.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Annotations and local contexts of rules.
*)

infix 1 THEN_ALL_NEW_CASES;

signature BASIC_RULE_CASES =
sig
  type cases
  type cases_tactic
  val CASES: cases -> tactic -> cases_tactic
  val NO_CASES: tactic -> cases_tactic
  val SUBGOAL_CASES: ((term * int) -> cases_tactic) -> int -> cases_tactic
  val THEN_ALL_NEW_CASES: (int -> cases_tactic) * (int -> tactic) -> int -> cases_tactic
end

signature RULE_CASES =
sig
  include BASIC_RULE_CASES
  type T
  val consume: thm list -> ('a * int) * thm -> (('a * (int * thm list)) * thm) Seq.seq
  val consumes: int -> 'a attribute
  val consumes_default: int -> 'a attribute
  val name: string list -> thm -> thm
  val case_names: string list -> 'a attribute
  val case_conclusion: string -> (string * string) list -> 'a attribute
  val case_conclusion_binops: string -> string list -> 'a attribute
  val save: thm -> thm -> thm
  val get: thm -> (string * (string * string) list) list * int
  val strip_params: term -> (string * typ) list
  val make: bool -> term option -> theory * term ->
    (string * (string * string) list) list -> cases
  val simple: bool -> theory * term -> string -> string * T option
  val rename_params: string list list -> thm -> thm
  val params: string list list -> 'a attribute
end;

structure RuleCases: RULE_CASES =
struct

(** tactics with cases **)

type T =
 {fixes: (string * typ) list,
  assumes: (string * term list) list,
  binds: (indexname * term option) list};

type cases = (string * T option) list;
type cases_tactic = thm -> (cases * thm) Seq.seq;

fun CASES cases tac st = Seq.map (pair cases) (tac st);
fun NO_CASES tac = CASES [] tac;

fun SUBGOAL_CASES tac i st =
  (case try Logic.nth_prem (i, Thm.prop_of st) of
    SOME goal => tac (goal, i) st
  | NONE => Seq.empty);

fun (tac1 THEN_ALL_NEW_CASES tac2) i st =
  st |> tac1 i |> Seq.maps (fn (cases, st') =>
    Seq.map (pair cases) (Seq.INTERVAL tac2 i (i + nprems_of st' - nprems_of st) st'));



(** consume facts **)

fun consume facts ((x, n), th) =
  Drule.multi_resolves (Library.take (n, facts)) [th]
  |> Seq.map (pair (x, (n - length facts, Library.drop (n, facts))));

val consumes_tagN = "consumes";

fun lookup_consumes th =
  let fun err () = raise THM ("Malformed 'consumes' tag of theorem", 0, [th]) in
    (case AList.lookup (op =) (Thm.tags_of_thm th) (consumes_tagN) of
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



(** case names **)

val cases_tagN = "cases";

fun add_case_names NONE = I
  | add_case_names (SOME names) =
      Drule.untag_rule cases_tagN
      #> Drule.tag_rule (cases_tagN, names);

fun lookup_case_names th = AList.lookup (op =) (Thm.tags_of_thm th) cases_tagN;

val save_case_names = add_case_names o lookup_case_names;
val name = add_case_names o SOME;
fun case_names ss = Drule.rule_attribute (K (name ss));



(** case conclusions **)

(* term positions *)

fun term_at pos tm =
  let
    fun at [] t = t
      | at ("0" :: ps) (t $ _) = at ps t
      | at ("1" :: ps) (_ $ u) = at ps u
      | at _ _ = raise TERM ("Bad term position: " ^ pos, [tm]);
  in at (explode pos) tm end;

fun binop_positions [] = []
  | binop_positions [x] = [(x, "")]
  | binop_positions xs =
      let
        fun pos i = replicate_string i "1";
        val k = length xs - 1;
      in xs ~~ (map (suffix "01" o pos) (0 upto k - 1) @ [pos k]) end;


(* conclusion tags *)

val case_concl_tagN = "case_conclusion";

fun is_case_concl name ((a, b :: _): tag) = (a = case_concl_tagN andalso b = name)
  | is_case_concl _ _ = false;

fun add_case_concl (name, cs) = Drule.map_tags (fn tags =>
  filter_out (is_case_concl name) tags @ [(case_concl_tagN, name :: cs)]);

fun lookup_case_concl th name =
  find_first (is_case_concl name) (Thm.tags_of_thm th) |> Option.map (tl o snd);

fun get_case_concls th name =
  let
    fun concls (x :: pos :: cs) = (x, pos) :: concls cs
      | concls [] = []
      | concls [x] = error ("No position for conclusion " ^ quote x ^ " of case " ^ quote name);
  in concls (these (lookup_case_concl th name)) end;

fun save_case_concls th =
  let val concls = Thm.tags_of_thm th |> List.mapPartial
    (fn (a, b :: bs) =>
      if a = case_concl_tagN then SOME (b, bs) else NONE
    | _ => NONE)
  in fold add_case_concl concls end;

fun case_conclusion name concls = Drule.rule_attribute (fn _ =>
  add_case_concl (name, List.concat (map (fn (a, b) => [a, b]) concls)));

fun case_conclusion_binops name xs = case_conclusion name (binop_positions xs);



(** case declarations **)

(* access hints *)

fun save th = save_consumes th #> save_case_names th #> save_case_concls th;

fun get th =
  let
    val n = the_default 0 (lookup_consumes th);
    val cases =
      (case lookup_case_names th of
        NONE => map (rpair [] o Library.string_of_int) (1 upto (Thm.nprems_of th - n))
      | SOME names => map (fn name => (name, get_case_concls th name)) names);
  in (cases, n) end;


(* extract cases *)

val case_conclN = "case";
val case_hypsN = "hyps";
val case_premsN = "prems";

val strip_params = map (apfst Syntax.deskolem) o Logic.strip_params;

fun extract_case is_open thy (split, raw_prop) name concls =
  let
    val prop = Drule.norm_hhf thy raw_prop;

    val xs = strip_params prop;
    val rename = if is_open then I else map (apfst Syntax.internal);
    val fixes =
      (case split of
        NONE => rename xs
      | SOME t =>
          let val (us, vs) = splitAt (length (Logic.strip_params t), xs)
          in rename us @ vs end);
    fun abs_fixes t = Term.list_abs (fixes, t);

    val asms = map abs_fixes (Logic.strip_assums_hyp prop);
    val assumes =
      (case split of
        NONE => [("", asms)]
      | SOME t =>
          let val (hyps, prems) = splitAt (length (Logic.strip_assums_hyp t), asms)
          in [(case_hypsN, hyps), (case_premsN, prems)] end);

    val concl = ObjectLogic.drop_judgment thy (Logic.strip_assums_concl prop);
    fun bind (x, pos) = ((x, 0), SOME (abs_fixes (term_at pos concl)));
    val binds = bind (case_conclN, "") :: map bind concls;
  in {fixes = fixes, assumes = assumes, binds = binds} end;

fun make is_open split (thy, prop) cases =
  let
    val n = length cases;
    val nprems = Logic.count_prems (prop, 0);
    fun add_case (name, concls) (cs, i) =
      ((case try (fn () =>
          (Option.map (curry Logic.nth_prem i) split, Logic.nth_prem (i, prop))) () of
        NONE => (name, NONE)
      | SOME sp => (name, SOME (extract_case is_open thy sp name concls))) :: cs, i - 1);
  in fold_rev add_case (Library.drop (n - nprems, cases)) ([], n) |> #1 end;

fun simple is_open (thy, prop) name =
  (name, SOME (extract_case is_open thy (NONE, prop) name []));


(* params *)

fun rename_params xss th =
  th
  |> fold_index (fn (i, xs) => Thm.rename_params_rule (xs, i + 1)) xss
  |> save th;

fun params xss = Drule.rule_attribute (K (rename_params xss));

end;

structure BasicRuleCases: BASIC_RULE_CASES = RuleCases;
open BasicRuleCases;
