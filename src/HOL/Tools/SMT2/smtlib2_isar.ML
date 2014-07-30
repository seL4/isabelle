(*  Title:      HOL/Tools/SMT2/smtlib2_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Mathias Fleury, ENS Rennes

General tools for Isar proof reconstruction.
*)

signature SMTLIB2_ISAR =
sig
  val simplify_bool: term -> term
  val unlift_term: term list -> term -> term
  val postprocess_step_conclusion: term -> theory -> thm list -> term list -> term
  val normalizing_prems : Proof.context -> term -> (string * string list) list
  val distinguish_conjecture_and_hypothesis : ''a list -> ''b -> ''b -> ''b list ->
    (''a * 'c) list -> 'c list -> 'c -> 'c -> ATP_Problem.atp_formula_role * 'c
  val unskolemize_names: term -> term
end;

structure SMTLIB2_Isar: SMTLIB2_ISAR =
struct

open ATP_Problem
open ATP_Util

fun simplify_bool ((all as Const (@{const_name All}, _)) $ Abs (s, T, t)) =
    let val t' = simplify_bool t in
      if loose_bvar1 (t', 0) then all $ Abs (s, T, t') else t'
    end
  | simplify_bool (@{const Not} $ t) = s_not (simplify_bool t)
  | simplify_bool (@{const conj} $ t $ u) = s_conj (simplify_bool t, simplify_bool u)
  | simplify_bool (@{const disj} $ t $ u) = s_disj (simplify_bool t, simplify_bool u)
  | simplify_bool (@{const implies} $ t $ u) = s_imp (simplify_bool t, simplify_bool u)
  | simplify_bool (@{const HOL.eq (bool)} $ t $ u) = s_iff (simplify_bool t, simplify_bool u)
  | simplify_bool (t as Const (@{const_name HOL.eq}, _) $ u $ v) =
    if u aconv v then @{const True} else t
  | simplify_bool (t $ u) = simplify_bool t $ simplify_bool u
  | simplify_bool (Abs (s, T, t)) = Abs (s, T, simplify_bool t)
  | simplify_bool t = t

fun strip_alls (Const (@{const_name All}, _) $ Abs (s, T, body)) = strip_alls body |>> cons (s, T)
  | strip_alls t = ([], t)

fun push_skolem_all_under_iff t =
  (case strip_alls t of
    (qs as _ :: _,
     (t0 as Const (@{const_name HOL.eq}, _)) $ (t1 as Const (@{const_name Ex}, _) $ _) $ t2) =>
    t0 $ HOLogic.list_all (qs, t1) $ HOLogic.list_all (qs, t2)
  | _ => t)

fun unlift_term ll_defs =
  let
    val lifted = map (ATP_Util.extract_lambda_def dest_Free o ATP_Util.hol_open_form I) ll_defs

    fun un_free (t as Free (s, _)) =
       (case AList.lookup (op =) lifted s of
         SOME t => un_term t
       | NONE => t)
     | un_free t = t
    and un_term t = map_aterms un_free t
  in un_term end

(* It is not entirely clear why this should be necessary, especially for abstractions variables. *)
val unskolemize_names =
  Term.map_abs_vars (perhaps (try Name.dest_skolem))
  #> Term.map_aterms (perhaps (try (fn Free (s, T) => Free (Name.dest_skolem s, T))))

fun postprocess_step_conclusion concl thy rewrite_rules ll_defs =
  concl
  |> Raw_Simplifier.rewrite_term thy rewrite_rules []
  |> Object_Logic.atomize_term thy
  |> simplify_bool
  |> not (null ll_defs) ? unlift_term ll_defs
  |> unskolemize_names
  |> push_skolem_all_under_iff
  |> HOLogic.mk_Trueprop
  |> unskolemize_names

fun normalizing_prems ctxt concl0 =
  SMT2_Normalize.case_bool_entry :: SMT2_Normalize.special_quant_table @
  SMT2_Normalize.abs_min_max_table
  |> map_filter (fn (c, th) =>
    if exists_Const (curry (op =) c o fst) concl0 then
      let val s = short_thm_name ctxt th in SOME (s, [s]) end
    else
      NONE)

fun distinguish_conjecture_and_hypothesis ss id conjecture_id prem_ids fact_helper_ts hyp_ts concl_t
    t =
  (case ss of
    [s] => (Axiom, the (AList.lookup (op =) fact_helper_ts s))
  | _ =>
    if id = conjecture_id then
      (Conjecture, concl_t)
    else
      (Hypothesis,
       (case find_index (curry (op =) id) prem_ids of
         ~1 => t
       | i => nth hyp_ts i)))

end;
