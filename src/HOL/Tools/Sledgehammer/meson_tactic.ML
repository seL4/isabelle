(*  Title:      HOL/Tools/Sledgehammer/meson_tactic.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory

MESON general tactic and proof method.
*)

signature MESON_TACTIC =
sig
  val expand_defs_tac : thm -> tactic
  val meson_general_tac : Proof.context -> thm list -> int -> tactic
  val setup: theory -> theory
end;

structure Meson_Tactic : MESON_TACTIC =
struct

open Clausifier

(*Expand all new definitions of abstraction or Skolem functions in a proof state.*)
fun is_absko (Const (@{const_name "=="}, _) $ Free (a, _) $ _) =
    String.isPrefix skolem_prefix a
  | is_absko _ = false;

fun is_okdef xs (Const (@{const_name "=="}, _) $ t $ _) =   (*Definition of Free, not in certain terms*)
      is_Free t andalso not (member (op aconv) xs t)
  | is_okdef _ _ = false

(*This function tries to cope with open locales, which introduce hypotheses of the form
  Free == t, conjecture clauses, which introduce various hypotheses, and also definitions
  of sko_ functions. *)
fun expand_defs_tac st0 st =
  let val hyps0 = #hyps (rep_thm st0)
      val hyps = #hyps (crep_thm st)
      val newhyps = filter_out (member (op aconv) hyps0 o Thm.term_of) hyps
      val defs = filter (is_absko o Thm.term_of) newhyps
      val remaining_hyps = filter_out (member (op aconv) (map Thm.term_of defs))
                                      (map Thm.term_of hyps)
      val fixed = OldTerm.term_frees (concl_of st) @
                  fold (union (op aconv)) (map OldTerm.term_frees remaining_hyps) []
  in Seq.of_list [Local_Defs.expand (filter (is_okdef fixed o Thm.term_of) defs) st] end;

fun meson_general_tac ctxt ths i st0 =
  let
    val thy = ProofContext.theory_of ctxt
    val ctxt0 = Classical.put_claset HOL_cs ctxt
  in (Meson.meson_tac ctxt0 (maps (cnf_axiom thy) ths) i THEN expand_defs_tac st0) st0 end;

val setup =
  Method.setup @{binding meson} (Attrib.thms >> (fn ths => fn ctxt =>
    SIMPLE_METHOD' (CHANGED_PROP o meson_general_tac ctxt ths)))
    "MESON resolution proof procedure";

end;
