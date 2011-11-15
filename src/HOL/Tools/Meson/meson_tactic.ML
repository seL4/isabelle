(*  Title:      HOL/Tools/Meson/meson_tactic.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

The "meson" proof method for HOL.
*)

signature MESON_TACTIC =
sig
  val meson_general_tac : Proof.context -> thm list -> int -> tactic
  val setup: theory -> theory
end;

structure Meson_Tactic : MESON_TACTIC =
struct

open Meson_Clausify

fun meson_general_tac ctxt ths =
  let val ctxt' = put_claset HOL_cs ctxt
  in Meson.meson_tac ctxt' (maps (snd o cnf_axiom ctxt' false true 0) ths) end

val setup =
  Method.setup @{binding meson} (Attrib.thms >> (fn ths => fn ctxt =>
     SIMPLE_METHOD' (CHANGED_PROP o meson_general_tac ctxt ths)))
     "MESON resolution proof procedure"

end;
