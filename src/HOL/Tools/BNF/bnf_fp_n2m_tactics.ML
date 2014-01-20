(*  Title:      HOL/Tools/BNF/bnf_fp_n2m_tactics.ML
    Author:     Dmitriy Traytel, TU Muenchen
    Copyright   2013

Tactics for mutualization of nested (co)datatypes.
*)

signature BNF_FP_N2M_TACTICS =
sig
  val mk_rel_xtor_co_induct_tactic: BNF_FP_Util.fp_kind -> thm list -> thm list -> thm list ->
    {prems: thm list, context: Proof.context} -> tactic
end;

structure BNF_FP_N2M_Tactics : BNF_FP_N2M_TACTICS =
struct

open BNF_Util
open BNF_FP_Util

fun mk_rel_xtor_co_induct_tactic fp co_inducts rel_defs rel_monos
  {context = ctxt, prems = raw_C_IHs} =
  let
    val unfolds = map (fn def => unfold_thms ctxt (id_apply :: no_reflexive [def])) rel_defs;
    val folded_C_IHs = map (fn thm => thm RS @{thm spec2} RS mp) raw_C_IHs;
    val C_IHs = map2 (curry op |>) folded_C_IHs unfolds;
    val C_IH_monos =
      map3 (fn C_IH => fn mono => fn unfold =>
        (mono RSN (2, @{thm rev_predicate2D}), C_IH)
        |> fp = Greatest_FP ? swap
        |> op RS
        |> unfold)
      folded_C_IHs rel_monos unfolds;
  in
    HEADGOAL (CONJ_WRAP_GEN' (rtac @{thm context_conjI})
      (fn thm => rtac thm THEN_ALL_NEW (rotate_tac ~1 THEN'
         REPEAT_ALL_NEW (FIRST' [eresolve_tac C_IHs, eresolve_tac C_IH_monos,
           rtac @{thm order_refl}, atac, resolve_tac co_inducts])))
    co_inducts)
  end;

end;
