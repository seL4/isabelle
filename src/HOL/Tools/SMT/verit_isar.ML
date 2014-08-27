(*  Title:      HOL/Tools/SMT/verit_isar.ML
    Author:     Mathias Fleury, TU Muenchen
    Author:     Jasmin Blanchette, TU Muenchen

VeriT proofs as generic ATP proofs for Isar proof reconstruction.
*)

signature VERIT_ISAR =
sig
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step
  val atp_proof_of_veriT_proof: Proof.context -> term list -> thm list -> term list -> term ->
    (string * term) list -> int list -> int -> (int * string) list -> VeriT_Proof.veriT_step list ->
    (term, string) ATP_Proof.atp_step list
end;

structure VeriT_Isar: VERIT_ISAR =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Proof_Reconstruct
open SMTLIB_Isar
open VeriT_Proof

fun atp_proof_of_veriT_proof ctxt ll_defs rewrite_rules hyp_ts concl_t fact_helper_ts prem_ids
    conjecture_id fact_helper_ids proof =
  let
    fun steps_of (VeriT_Proof.VeriT_Step {id, rule, prems, concl, ...}) =
      let
        val concl' = postprocess_step_conclusion ctxt rewrite_rules ll_defs concl
        fun standard_step role = ((id, []), role, concl', rule, map (rpair []) prems)
      in
        if rule = veriT_input_rule then
          let val ss = the_list (AList.lookup (op =) fact_helper_ids (the (Int.fromString id))) in
            (case distinguish_conjecture_and_hypothesis ss (the (Int.fromString id))
                conjecture_id prem_ids fact_helper_ts hyp_ts concl_t of
              NONE => []
            | SOME (role0, concl00) =>
              let
                val name0 = (id ^ "a", ss)
                val concl0 = unskolemize_names ctxt concl00
              in
                [(name0, role0, concl0, rule, []),
                 ((id, []), Plain, concl', veriT_rewrite_rule,
                  name0 :: normalizing_prems ctxt concl0)]
              end)
          end
        else if rule = veriT_tmp_ite_elim_rule then
          [standard_step Lemma]
        else
          [standard_step Plain]
      end
  in
    maps steps_of proof
  end

end;
