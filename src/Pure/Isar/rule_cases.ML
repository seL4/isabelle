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
  val consume: thm list -> thm list -> ('a * int) * thm ->
    (('a * (int * thm list)) * thm) Seq.seq
  val add_consumes: int -> thm -> thm
  val consumes: int -> 'a attribute
  val consumes_default: int -> 'a attribute
  val name: string list -> thm -> thm
  val case_names: string list -> 'a attribute
  val case_conclusion: string * string list -> 'a attribute
  val save: thm -> thm -> thm
  val get: thm -> (string * string list) list * int
  val strip_params: term -> (string * typ) list
  val make: bool -> term option -> theory * term -> (string * string list) list -> cases
  val simple: theory * term -> string -> cases
  val rename_params: string list list -> thm -> thm
  val params: string list list -> 'a attribute
  val mutual_rule: thm list -> (int list * thm) option
  val strict_mutual_rule: thm list -> int list * thm
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
    CASES cases (Seq.INTERVAL tac2 i (i + nprems_of st' - nprems_of st)) st');



(** consume facts **)

local

fun unfold_prems n defs th =
  if null defs then th
  else Drule.fconv_rule (Drule.goals_conv (fn i => i <= n) (Tactic.rewrite true defs)) th;

fun unfold_prems_concls defs th =
  if null defs orelse not (can Logic.dest_conjunction (Thm.concl_of th)) then th
  else
    Drule.fconv_rule
      (Drule.concl_conv ~1 (Drule.conjunction_conv ~1
        (K (Drule.prems_conv ~1 (K (Tactic.rewrite true defs)))))) th;

in

fun consume defs facts ((xx, n), th) =
  let val m = Int.min (length facts, n) in
    th
    |> unfold_prems n defs
    |> unfold_prems_concls defs
    |> Drule.multi_resolve (Library.take (m, facts))
    |> Seq.map (pair (xx, (n - m, Library.drop (m, facts))))
  end;

end;

val consumes_tagN = "consumes";

fun lookup_consumes th =
  let fun err () = raise THM ("Malformed 'consumes' tag of theorem", 0, [th]) in
    (case AList.lookup (op =) (Thm.tags_of_thm th) (consumes_tagN) of
      NONE => NONE
    | SOME [s] => (case Syntax.read_nat s of SOME n => SOME n | _ => err ())
    | _ => err ())
  end;

fun get_consumes th = the_default 0 (lookup_consumes th);

fun put_consumes NONE th = th
  | put_consumes (SOME n) th = th
      |> Drule.untag_rule consumes_tagN
      |> Drule.tag_rule (consumes_tagN, [Library.string_of_int n]);

fun add_consumes k th = put_consumes (SOME (k + get_consumes th)) th;

val save_consumes = put_consumes o lookup_consumes;

fun consumes n x = Drule.rule_attribute (K (put_consumes (SOME n))) x;
fun consumes_default n x =
  if Library.is_some (lookup_consumes (#2 x)) then x else consumes n x;



(** case names **)

val case_names_tagN = "case_names";

fun add_case_names NONE = I
  | add_case_names (SOME names) =
      Drule.untag_rule case_names_tagN
      #> Drule.tag_rule (case_names_tagN, names);

fun lookup_case_names th = AList.lookup (op =) (Thm.tags_of_thm th) case_names_tagN;

val save_case_names = add_case_names o lookup_case_names;
val name = add_case_names o SOME;
fun case_names ss = Drule.rule_attribute (K (name ss));



(** case conclusions **)

val case_concl_tagN = "case_conclusion";

fun is_case_concl name ((a, b :: _): tag) = (a = case_concl_tagN andalso b = name)
  | is_case_concl _ _ = false;

fun add_case_concl (name, cs) = Drule.map_tags (fn tags =>
  filter_out (is_case_concl name) tags @ [(case_concl_tagN, name :: cs)]);

fun get_case_concls th name =
  (case find_first (is_case_concl name) (Thm.tags_of_thm th) of
    SOME (_, _ :: cs) => cs
  | _ => []);

fun save_case_concls th =
  let val concls = Thm.tags_of_thm th |> List.mapPartial
    (fn (a, b :: cs) =>
      if a = case_concl_tagN then SOME (b, cs) else NONE
    | _ => NONE)
  in fold add_case_concl concls end;

fun case_conclusion concl = Drule.rule_attribute (fn _ => add_case_concl concl);



(** case declarations **)

(* access hints *)

fun save th = save_consumes th #> save_case_names th #> save_case_concls th;

fun get th =
  let
    val n = get_consumes th;
    val cases =
      (case lookup_case_names th of
        NONE => map (rpair [] o Library.string_of_int) (1 upto (Thm.nprems_of th - n))
      | SOME names => map (fn name => (name, get_case_concls th name)) names);
  in (cases, n) end;


(* extract cases *)

val case_conclN = "case";
val case_hypsN = "hyps";
val case_premsN = "prems";

val strip_params = map (apfst (perhaps (try Syntax.dest_skolem))) o Logic.strip_params;

local

fun dest_binops cs tm =
  let
    val n = length cs;
    fun dest 0 _ = []
      | dest 1 t = [t]
      | dest k (_ $ t $ u) = t :: dest (k - 1) u
      | dest _ _ = raise TERM ("Expected " ^ string_of_int n ^ " binop arguments", [tm]);
  in cs ~~ dest n tm end;

fun extract_cases is_open thy (split, raw_prop) name concls =
  let
    fun extract prop idx =
      let
        val xs = strip_params prop;
        val rename = if is_open then I else map (apfst Syntax.internal);
        val fixes =
          (case split of
            NONE => rename xs
          | SOME t =>
              let val (us, vs) = splitAt (length (Logic.strip_params t), xs)
              in rename us @ vs end);
        fun abs_fixes t = Term.list_abs (fixes, t);
        val dest_conjuncts = map abs_fixes o List.concat o map Logic.dest_conjunctions;

        val asms = Logic.strip_assums_hyp prop;
        val assumes =
          (case split of
            NONE => [("", dest_conjuncts asms)]
          | SOME t =>
              let val (hyps, prems) = splitAt (length (Logic.strip_assums_hyp t), asms) in
               [(case_hypsN, dest_conjuncts hyps),
                (case_premsN, dest_conjuncts prems)]
              end);

        val concl = ObjectLogic.drop_judgment thy (Logic.strip_assums_concl prop);
        val binds = (case_conclN, concl) :: dest_binops concls concl
          |> map (fn (x, t) => ((x, 0), SOME (abs_fixes t)));
      in (name ^ idx, SOME {fixes = fixes, assumes = assumes, binds = binds}) end;
  in
    (case Logic.dest_conjunctions (Drule.norm_hhf thy raw_prop) of
      [prop] => [extract prop ""]
    | props => map2 extract props (map string_of_int (1 upto length props)))
  end;

in

fun make is_open split (thy, prop) cases =
  let
    val n = length cases;
    val nprems = Logic.count_prems (prop, 0);
    fun add_case (name, concls) (cs, i) =
      ((case try (fn () =>
          (Option.map (curry Logic.nth_prem i) split, Logic.nth_prem (i, prop))) () of
        NONE => [(name, NONE)]
      | SOME sp => extract_cases is_open thy sp name concls) @ cs, i - 1);
  in fold_rev add_case (Library.drop (n - nprems, cases)) ([], n) |> #1 end;

fun simple (thy, prop) name =
  extract_cases true thy (NONE, prop) name [];

end;


(* params *)

fun rename_params xss th =
  th
  |> fold_index (fn (i, xs) => Thm.rename_params_rule (xs, i + 1)) xss
  |> save th;

fun params xss = Drule.rule_attribute (K (rename_params xss));



(** mutual_rule **)

local

fun equal_cterms ts us =
  list_ord (Term.fast_term_ord o pairself Thm.term_of) (ts, us) = EQUAL;

fun prep_rule th =
  let
    val n = get_consumes th;
    val th' = Drule.freeze_all (Thm.permute_prems 0 n th);
    val prems = Library.take (Thm.nprems_of th' - n, Drule.cprems_of th');
    val th'' = Drule.implies_elim_list th' (map Thm.assume prems);
  in (prems, (n, th'')) end;

in

fun mutual_rule [] = NONE
  | mutual_rule [th] = SOME ([0], th)
  | mutual_rule raw_rules =
      let
        val rules as (prems, _) :: _ = map prep_rule raw_rules;
        val (ns, ths) = split_list (map #2 rules);
      in
        if not (forall (equal_cterms prems o #1) rules) then NONE
        else
          SOME (ns,
            ths
            |> foldr1 (uncurry Drule.conj_intr)
            |> Drule.implies_intr_list prems
            |> Drule.standard'
            |> save (hd raw_rules)
            |> put_consumes (SOME 0))
      end;

end;

fun strict_mutual_rule ths =
  (case mutual_rule ths of
    NONE => error "Failed to join given rules into one mutual rule"
  | SOME res => res);

end;

structure BasicRuleCases: BASIC_RULE_CASES = RuleCases;
open BasicRuleCases;
