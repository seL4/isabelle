(*  Title:      Pure/Isar/rule_cases.ML
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
  datatype T = Case of
   {fixes: (string * typ) list,
    assumes: (string * term list) list,
    binds: (indexname * term option) list,
    cases: (string * T) list}
  val strip_params: term -> (string * typ) list
  val make_common: bool -> theory * term -> (string * string list) list -> cases
  val make_nested: bool -> term -> theory * term -> (string * string list) list -> cases
  val apply: term list -> T -> T
  val consume: thm list -> thm list -> ('a * int) * thm ->
    (('a * (int * thm list)) * thm) Seq.seq
  val add_consumes: int -> thm -> thm
  val get_consumes: thm -> int
  val consumes: int -> attribute
  val consumes_default: int -> attribute
  val name: string list -> thm -> thm
  val case_names: string list -> attribute
  val case_conclusion: string * string list -> attribute
  val is_inner_rule: thm -> bool
  val inner_rule: attribute
  val save: thm -> thm -> thm
  val get: thm -> (string * string list) list * int
  val rename_params: string list list -> thm -> thm
  val params: string list list -> attribute
  val mutual_rule: Proof.context -> thm list -> (int list * thm) option
  val strict_mutual_rule: Proof.context -> thm list -> int list * thm
end;

structure Rule_Cases: RULE_CASES =
struct

(** cases **)

datatype T = Case of
 {fixes: (string * typ) list,
  assumes: (string * term list) list,
  binds: (indexname * term option) list,
  cases: (string * T) list};

type cases = (string * T option) list;

val case_conclN = "case";
val case_hypsN = "hyps";
val case_premsN = "prems";

val strip_params = map (apfst (perhaps (try Name.dest_skolem))) o Logic.strip_params;

local

fun abs xs t = Term.list_abs (xs, t);
fun app us t = Term.betapplys (t, us);

fun dest_binops cs tm =
  let
    val n = length cs;
    fun dest 0 _ = []
      | dest 1 t = [t]
      | dest k (_ $ t $ u) = t :: dest (k - 1) u
      | dest _ _ = raise TERM ("Expected " ^ string_of_int n ^ " binop arguments", [tm]);
  in cs ~~ dest n tm end;

fun extract_fixes NONE prop = (strip_params prop, [])
  | extract_fixes (SOME outline) prop =
      chop (length (Logic.strip_params outline)) (strip_params prop);

fun extract_assumes _ NONE prop = ([("", Logic.strip_assums_hyp prop)], [])
  | extract_assumes qual (SOME outline) prop =
      let val (hyps, prems) =
        chop (length (Logic.strip_assums_hyp outline)) (Logic.strip_assums_hyp prop)
      in ([(qual case_hypsN, hyps)], [(qual case_premsN, prems)]) end;

fun extract_case is_open thy (case_outline, raw_prop) name concls =
  let
    val rename = if is_open then I else apfst (Name.internal o Name.clean);

    val props = Logic.dest_conjunctions (Drule.norm_hhf thy raw_prop);
    val len = length props;
    val nested = is_some case_outline andalso len > 1;

    fun extract prop =
      let
        val (fixes1, fixes2) = extract_fixes case_outline prop
          |> apfst (map rename);
        val abs_fixes = abs (fixes1 @ fixes2);
        fun abs_fixes1 t =
          if not nested then abs_fixes t
          else abs fixes1 (app (map (Term.dummy_pattern o #2) fixes2) (abs fixes2 t));

        val (assumes1, assumes2) = extract_assumes (Long_Name.qualify name) case_outline prop
          |> pairself (map (apsnd (maps Logic.dest_conjunctions)));

        val concl = ObjectLogic.drop_judgment thy (Logic.strip_assums_concl prop);
        val binds =
          (case_conclN, concl) :: dest_binops concls concl
          |> map (fn (x, t) => ((x, 0), SOME (abs_fixes t)));
      in
       ((fixes1, map (apsnd (map abs_fixes1)) assumes1),
        ((fixes2, map (apsnd (map abs_fixes)) assumes2), binds))
      end;

    val cases = map extract props;

    fun common_case ((fixes1, assumes1), ((fixes2, assumes2), binds)) =
      Case {fixes = fixes1 @ fixes2, assumes = assumes1 @ assumes2, binds = binds, cases = []};
    fun inner_case (_, ((fixes2, assumes2), binds)) =
      Case {fixes = fixes2, assumes = assumes2, binds = binds, cases = []};
    fun nested_case ((fixes1, assumes1), _) =
      Case {fixes = fixes1, assumes = assumes1, binds = [],
        cases = map string_of_int (1 upto len) ~~ map inner_case cases};
  in
    if len = 0 then NONE
    else if len = 1 then SOME (common_case (hd cases))
    else if is_none case_outline orelse length (distinct (op =) (map fst cases)) > 1 then NONE
    else SOME (nested_case (hd cases))
  end;

fun make is_open rule_struct (thy, prop) cases =
  let
    val n = length cases;
    val nprems = Logic.count_prems prop;
    fun add_case (name, concls) (cs, i) =
      ((case try (fn () =>
          (Option.map (curry Logic.nth_prem i) rule_struct, Logic.nth_prem (i, prop))) () of
        NONE => (name, NONE)
      | SOME p => (name, extract_case is_open thy p name concls)) :: cs, i - 1);
  in fold_rev add_case ((uncurry drop) (n - nprems, cases)) ([], n) |> #1 end;

in

fun make_common is_open = make is_open NONE;
fun make_nested is_open rule_struct = make is_open (SOME rule_struct);

fun apply args =
  let
    fun appl (Case {fixes, assumes, binds, cases}) =
      let
        val assumes' = map (apsnd (map (app args))) assumes;
        val binds' = map (apsnd (Option.map (app args))) binds;
        val cases' = map (apsnd appl) cases;
      in Case {fixes = fixes, assumes = assumes', binds = binds', cases = cases'} end;
  in appl end;

end;



(** tactics with cases **)

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
  else Conv.fconv_rule (Conv.prems_conv n (MetaSimplifier.rewrite true defs)) th;

fun unfold_prems_concls defs th =
  if null defs orelse not (can Logic.dest_conjunction (Thm.concl_of th)) then th
  else
    Conv.fconv_rule
      (Conv.concl_conv ~1 (Conjunction.convs
        (Conv.prems_conv ~1 (MetaSimplifier.rewrite true defs)))) th;

in

fun consume defs facts ((xx, n), th) =
  let val m = Int.min (length facts, n) in
    th
    |> unfold_prems n defs
    |> unfold_prems_concls defs
    |> Drule.multi_resolve ((uncurry take) (m, facts))
    |> Seq.map (pair (xx, (n - m, (uncurry drop) (m, facts))))
  end;

end;

val consumes_tagN = "consumes";

fun lookup_consumes th =
  (case AList.lookup (op =) (Thm.get_tags th) consumes_tagN of
    NONE => NONE
  | SOME s =>
      (case Lexicon.read_nat s of SOME n => SOME n
      | _ => raise THM ("Malformed 'consumes' tag of theorem", 0, [th])));

fun get_consumes th = the_default 0 (lookup_consumes th);

fun put_consumes NONE th = th
  | put_consumes (SOME n) th = th
      |> Thm.untag_rule consumes_tagN
      |> Thm.tag_rule (consumes_tagN, string_of_int (if n < 0 then Thm.nprems_of th + n else n));

fun add_consumes k th = put_consumes (SOME (k + get_consumes th)) th;

val save_consumes = put_consumes o lookup_consumes;

fun consumes n = Thm.rule_attribute (K (put_consumes (SOME n)));

fun consumes_default n x =
  if is_some (lookup_consumes (#2 x)) then x else consumes n x;



(** case names **)

val implode_args = space_implode ";";
val explode_args = space_explode ";";

val case_names_tagN = "case_names";

fun add_case_names NONE = I
  | add_case_names (SOME names) =
      Thm.untag_rule case_names_tagN
      #> Thm.tag_rule (case_names_tagN, implode_args names);

fun lookup_case_names th =
  AList.lookup (op =) (Thm.get_tags th) case_names_tagN
  |> Option.map explode_args;

val save_case_names = add_case_names o lookup_case_names;
val name = add_case_names o SOME;
fun case_names ss = Thm.rule_attribute (K (name ss));



(** case conclusions **)

val case_concl_tagN = "case_conclusion";

fun get_case_concl name (a, b) =
  if a = case_concl_tagN then
    (case explode_args b of c :: cs => if c = name then SOME cs else NONE)
  else NONE;

fun add_case_concl (name, cs) = Thm.map_tags (fn tags =>
  filter_out (is_some o get_case_concl name) tags @
    [(case_concl_tagN, implode_args (name :: cs))]);

fun get_case_concls th name =
  these (get_first (get_case_concl name) (Thm.get_tags th));

fun save_case_concls th =
  let val concls = Thm.get_tags th |> map_filter
    (fn (a, b) =>
      if a = case_concl_tagN then (case explode_args b of c :: cs => SOME (c, cs) | _ => NONE)
      else NONE)
  in fold add_case_concl concls end;

fun case_conclusion concl = Thm.rule_attribute (K (add_case_concl concl));



(** inner rule **)

val inner_rule_tagN = "inner_rule";

fun is_inner_rule th =
  AList.defined (op =) (Thm.get_tags th) inner_rule_tagN;

fun put_inner_rule inner =
  Thm.untag_rule inner_rule_tagN
  #> inner ? Thm.tag_rule (inner_rule_tagN, "");

val save_inner_rule = put_inner_rule o is_inner_rule;

val inner_rule = Thm.rule_attribute (K (put_inner_rule true));



(** case declarations **)

(* access hints *)

fun save th =
  save_consumes th #>
  save_case_names th #>
  save_case_concls th #>
  save_inner_rule th;

fun get th =
  let
    val n = get_consumes th;
    val cases =
      (case lookup_case_names th of
        NONE => map (rpair [] o Library.string_of_int) (1 upto (Thm.nprems_of th - n))
      | SOME names => map (fn name => (name, get_case_concls th name)) names);
  in (cases, n) end;


(* params *)

fun rename_params xss th =
  th
  |> fold_index (fn (i, xs) => Thm.rename_params_rule (xs, i + 1)) xss
  |> save th;

fun params xss = Thm.rule_attribute (K (rename_params xss));



(** mutual_rule **)

local

fun equal_cterms ts us =
  is_equal (list_ord (TermOrd.fast_term_ord o pairself Thm.term_of) (ts, us));

fun prep_rule n th =
  let
    val th' = Thm.permute_prems 0 n th;
    val prems = (uncurry take) (Thm.nprems_of th' - n, Drule.cprems_of th');
    val th'' = Drule.implies_elim_list th' (map Thm.assume prems);
  in (prems, (n, th'')) end;

in

fun mutual_rule _ [] = NONE
  | mutual_rule _ [th] = SOME ([0], th)
  | mutual_rule ctxt (ths as th :: _) =
      let
        val ((_, ths'), ctxt') = Variable.import true ths ctxt;
        val rules as (prems, _) :: _ = map (prep_rule (get_consumes th)) ths';
        val (ns, rls) = split_list (map #2 rules);
      in
        if not (forall (equal_cterms prems o #1) rules) then NONE
        else
          SOME (ns,
            rls
            |> Conjunction.intr_balanced
            |> Drule.implies_intr_list prems
            |> singleton (Variable.export ctxt' ctxt)
            |> save th
            |> put_consumes (SOME 0))
      end;

end;

fun strict_mutual_rule ctxt ths =
  (case mutual_rule ctxt ths of
    NONE => error "Failed to join given rules into one mutual rule"
  | SOME res => res);

end;

structure Basic_Rule_Cases: BASIC_RULE_CASES = Rule_Cases;
open Basic_Rule_Cases;
