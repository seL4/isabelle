(*  Title:      HOL/Hoare/hoare_tac.ML
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Author:     Walter Guttmann (extension to total-correctness proofs)

Derivation of the proof rules and, most importantly, the VCG tactic.
*)

signature HOARE_TAC =
sig
  val hoare_rule_tac: Proof.context -> term list * thm -> (int -> tactic) -> bool ->
    int -> tactic
  val hoare_tac: Proof.context -> (int -> tactic) -> int -> tactic
  val hoare_tc_tac: Proof.context -> (int -> tactic) -> int -> tactic
end;

structure Hoare_Tac: HOARE_TAC =
struct

(*** The tactics ***)

(*****************************************************************************)
(** The function Mset makes the theorem                                     **)
(** "?Mset <= {(x1,...,xn). ?P (x1,...,xn)} ==> ?Mset <= {s. ?P s}",        **)
(** where (x1,...,xn) are the variables of the particular program we are    **)
(** working on at the moment of the call                                    **)
(*****************************************************************************)

local

(** maps (%x1 ... xn. t) to [x1,...,xn] **)
fun abs2list (Const (\<^const_name>\<open>case_prod\<close>, _) $ Abs (x, T, t)) = Free (x, T) :: abs2list t
  | abs2list (Abs (x, T, _)) = [Free (x, T)]
  | abs2list _ = [];

(** maps {(x1,...,xn). t} to [x1,...,xn] **)
fun mk_vars (Const (\<^const_name>\<open>Collect\<close>,_) $ T) = abs2list T
  | mk_vars _ = [];

(** abstraction of body over a tuple formed from a list of free variables.
Types are also built **)
fun mk_abstupleC [] body = absfree ("x", HOLogic.unitT) body
  | mk_abstupleC [v] body = absfree (dest_Free v) body
  | mk_abstupleC (v :: w) body =
      let
        val (x, T) = dest_Free v;
        val z = mk_abstupleC w body;
        val T2 =
          (case z of
            Abs (_, T, _) => T
          | Const (_, Type (_, [_, Type (_, [T, _])])) $ _ => T);
      in
        Const (\<^const_name>\<open>case_prod\<close>,
            (T --> T2 --> HOLogic.boolT) --> HOLogic.mk_prodT (T, T2) --> HOLogic.boolT) $
          absfree (x, T) z
      end;

(** maps [x1,...,xn] to (x1,...,xn) and types**)
fun mk_bodyC [] = HOLogic.unit
  | mk_bodyC [x] = x
  | mk_bodyC (x :: xs) =
      let
        val (_, T) = dest_Free x;
        val z = mk_bodyC xs;
        val T2 =
          (case z of
            Free (_, T) => T
          | Const (\<^const_name>\<open>Pair\<close>, Type ("fun", [_, Type ("fun", [_, T])])) $ _ $ _ => T);
     in Const (\<^const_name>\<open>Pair\<close>, [T, T2] ---> HOLogic.mk_prodT (T, T2)) $ x $ z end;

(** maps a subgoal of the form:
    VARS x1 ... xn {._.} _ {._.} or to [x1,...,xn]
**)
fun get_vars c =
  let
    val d = Logic.strip_assums_concl c;
    val Const _ $ pre $ _ $ _ = HOLogic.dest_Trueprop d;
  in mk_vars pre end;

fun mk_CollectC tm =
  let val Type ("fun",[t,_]) = fastype_of tm;
  in HOLogic.Collect_const t $ tm end;

fun inclt ty = Const (\<^const_name>\<open>Orderings.less_eq\<close>, [ty,ty] ---> HOLogic.boolT);

in

fun Mset ctxt prop =
  let
    val [(Mset, _), (P, _)] = Variable.variant_frees ctxt [] [("Mset", ()), ("P", ())];

    val vars = get_vars prop;
    val varsT = fastype_of (mk_bodyC vars);
    val big_Collect =
      mk_CollectC (mk_abstupleC vars (Free (P, varsT --> HOLogic.boolT) $ mk_bodyC vars));
    val small_Collect =
      mk_CollectC (Abs ("x", varsT, Free (P, varsT --> HOLogic.boolT) $ Bound 0));

    val MsetT = fastype_of big_Collect;
    fun Mset_incl t = HOLogic.mk_Trueprop (inclt MsetT $ Free (Mset, MsetT) $ t);
    val impl = Logic.mk_implies (Mset_incl big_Collect, Mset_incl small_Collect);
    val th = Goal.prove ctxt [Mset, P] [] impl (fn _ => blast_tac ctxt 1);
 in (vars, th) end;

end;


(*****************************************************************************)
(** Simplifying:                                                            **)
(** Some useful lemmata, lists and simplification tactics to control which  **)
(** theorems are used to simplify at each moment, so that the original      **)
(** input does not suffer any unexpected transformation                     **)
(*****************************************************************************)

(**Simp_tacs**)

fun before_set2pred_simp_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps [Collect_conj_eq RS sym, @{thm Compl_Collect}]);

fun split_simp_tac ctxt =
  simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm split_conv}]);

(*****************************************************************************)
(** set_to_pred_tac transforms sets inclusion into predicates implication,  **)
(** maintaining the original variable names.                                **)
(** Ex. "{x. x=0} <= {x. x <= 1}" -set2pred-> "x=0 --> x <= 1"              **)
(** Subgoals containing intersections (A Int B) or complement sets (-A)     **)
(** are first simplified by "before_set2pred_simp_tac", that returns only   **)
(** subgoals of the form "{x. P x} <= {x. Q x}", which are easily           **)
(** transformed.                                                            **)
(** This transformation may solve very easy subgoals due to a ligth         **)
(** simplification done by (split_all_tac)                                  **)
(*****************************************************************************)

fun set_to_pred_tac ctxt var_names = SUBGOAL (fn (_, i) =>
  before_set2pred_simp_tac ctxt i THEN_MAYBE
  EVERY [
    resolve_tac ctxt [subsetI] i,
    resolve_tac ctxt [CollectI] i,
    dresolve_tac ctxt [CollectD] i,
    TRY (split_all_tac ctxt i) THEN_MAYBE
     (rename_tac var_names i THEN
      full_simp_tac (put_simpset HOL_basic_ss ctxt addsimps [@{thm split_conv}]) i)]);

(*******************************************************************************)
(** basic_simp_tac is called to simplify all verification conditions. It does **)
(** a light simplification by applying "mem_Collect_eq", then it calls        **)
(** max_simp_tac, which solves subgoals of the form "A <= A",                 **)
(** and transforms any other into predicates, applying then                   **)
(** the tactic chosen by the user, which may solve the subgoal completely.    **)
(*******************************************************************************)

fun max_simp_tac ctxt var_names tac =
  FIRST' [resolve_tac ctxt [subset_refl],
    set_to_pred_tac ctxt var_names THEN_MAYBE' tac];

fun basic_simp_tac ctxt var_names tac =
  simp_tac
    (put_simpset HOL_basic_ss ctxt
      addsimps [mem_Collect_eq, @{thm split_conv}] addsimprocs [Record.simproc])
  THEN_MAYBE' max_simp_tac ctxt var_names tac;


(** hoare_rule_tac **)

fun hoare_rule_tac ctxt (vars, Mlem) tac =
  let
    val get_thms = Proof_Context.get_thms ctxt;
    val var_names = map (fst o dest_Free) vars;
    fun wlp_tac i =
      resolve_tac ctxt (get_thms \<^named_theorems>\<open>SeqRule\<close>) i THEN rule_tac false (i + 1)
    and rule_tac pre_cond i st = st |> (*abstraction over st prevents looping*)
      ((wlp_tac i THEN rule_tac pre_cond i)
        ORELSE
        (FIRST [
          resolve_tac ctxt (get_thms \<^named_theorems>\<open>SkipRule\<close>) i,
          resolve_tac ctxt (get_thms \<^named_theorems>\<open>AbortRule\<close>) i,
          EVERY [
            resolve_tac ctxt (get_thms \<^named_theorems>\<open>BasicRule\<close>) i,
            resolve_tac ctxt [Mlem] i,
            split_simp_tac ctxt i],
          EVERY [
            resolve_tac ctxt (get_thms \<^named_theorems>\<open>CondRule\<close>) i,
            rule_tac false (i + 2),
            rule_tac false (i + 1)],
          EVERY [
            resolve_tac ctxt (get_thms \<^named_theorems>\<open>WhileRule\<close>) i,
            basic_simp_tac ctxt var_names tac (i + 2),
            rule_tac true (i + 1)]]
         THEN (
           if pre_cond then basic_simp_tac ctxt var_names tac i
           else resolve_tac ctxt [subset_refl] i)));
  in rule_tac end;


(** tac is the tactic the user chooses to solve or simplify **)
(** the final verification conditions                       **)

fun hoare_tac ctxt tac = SUBGOAL (fn (goal, i) =>
  SELECT_GOAL (hoare_rule_tac ctxt (Mset ctxt goal) tac true 1) i);


(* total correctness rules *)

fun hoare_tc_rule_tac ctxt (vars, Mlem) tac =
  let
    val get_thms = Proof_Context.get_thms ctxt;
    val var_names = map (fst o dest_Free) vars;
    fun wlp_tac i =
      resolve_tac ctxt (get_thms \<^named_theorems>\<open>SeqRuleTC\<close>) i THEN rule_tac false (i + 1)
    and rule_tac pre_cond i st = st |> (*abstraction over st prevents looping*)
      ((wlp_tac i THEN rule_tac pre_cond i)
        ORELSE
        (FIRST [
          resolve_tac ctxt (get_thms \<^named_theorems>\<open>SkipRuleTC\<close>) i,
          EVERY [
            resolve_tac ctxt (get_thms \<^named_theorems>\<open>BasicRuleTC\<close>) i,
            resolve_tac ctxt [Mlem] i,
            split_simp_tac ctxt i],
          EVERY [
            resolve_tac ctxt (get_thms \<^named_theorems>\<open>CondRuleTC\<close>) i,
            rule_tac false (i + 2),
            rule_tac false (i + 1)],
          EVERY [
            resolve_tac ctxt (get_thms \<^named_theorems>\<open>WhileRuleTC\<close>) i,
            basic_simp_tac ctxt var_names tac (i + 2),
            rule_tac true (i + 1)]]
         THEN (
           if pre_cond then basic_simp_tac ctxt var_names tac i
           else resolve_tac ctxt [subset_refl] i)));
  in rule_tac end;


fun hoare_tc_tac ctxt tac = SUBGOAL (fn (goal, i) =>
  SELECT_GOAL (hoare_tc_rule_tac ctxt (Mset ctxt goal) tac true 1) i);

end;
