(*  Title:      HOL/Tools/Sledgehammer/meson_tactic.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

MESON general tactic and proof method.
*)

signature MESON_TACTIC =
sig
  val meson_general_tac : Proof.context -> thm list -> int -> tactic
  val setup: theory -> theory
end;

structure Meson_Tactic : MESON_TACTIC =
struct

fun meson_general_tac ctxt ths =
  let
    val thy = ProofContext.theory_of ctxt
    val ctxt0 = Classical.put_claset HOL_cs ctxt
  in Meson.meson_tac ctxt0 (maps (Clausifier.cnf_axiom thy false) ths) end

val setup =
  Method.setup @{binding meson} (Attrib.thms >> (fn ths => fn ctxt =>
    SIMPLE_METHOD' (CHANGED_PROP o meson_general_tac ctxt ths)))
    "MESON resolution proof procedure";

end;
