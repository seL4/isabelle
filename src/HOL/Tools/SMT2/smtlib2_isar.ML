(*  Title:      HOL/Tools/SMT2/smtlib2_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Author:     Mathias Fleury, ENS Rennes

General tools for Isar proof reconstruction.
*)

signature SMTLIB2_ISAR =
sig
  val unlift_term: term list -> term -> term
  val postprocess_step_conclusion: theory -> thm list -> term list -> term -> term
  val normalizing_prems : Proof.context -> term -> (string * string list) list
  val distinguish_conjecture_and_hypothesis : ''a list -> ''b -> ''b -> ''b list ->
    (''a * 'c) list -> 'c list -> 'c -> (ATP_Problem.atp_formula_role * 'c) option
  val unskolemize_names: term -> term
end;

structure SMTLIB2_Isar: SMTLIB2_ISAR =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof_Reconstruct

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

fun postprocess_step_conclusion thy rewrite_rules ll_defs =
  Raw_Simplifier.rewrite_term thy rewrite_rules []
  #> Object_Logic.atomize_term thy
  #> not (null ll_defs) ? unlift_term ll_defs
  #> simplify_bool
  #> unskolemize_names
  #> HOLogic.mk_Trueprop

fun normalizing_prems ctxt concl0 =
  SMT2_Normalize.case_bool_entry :: SMT2_Normalize.special_quant_table @
  SMT2_Normalize.abs_min_max_table
  |> map_filter (fn (c, th) =>
    if exists_Const (curry (op =) c o fst) concl0 then
      let val s = short_thm_name ctxt th in SOME (s, [s]) end
    else
      NONE)

fun distinguish_conjecture_and_hypothesis ss id conjecture_id prem_ids fact_helper_ts hyp_ts
    concl_t =
  (case ss of
    [s] => SOME (Axiom, the (AList.lookup (op =) fact_helper_ts s))
  | _ =>
    if id = conjecture_id then
      SOME (Conjecture, concl_t)
    else
     (case find_index (curry (op =) id) prem_ids of
       ~1 => NONE (* lambda-lifting definition *)
     | i => SOME (Hypothesis, nth hyp_ts i)))

end;
