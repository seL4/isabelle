(*  Title:      HOL/Tools/Meson/meson_tactic.ML
    Author:     Jia Meng, Cambridge University Computer Laboratory and NICTA
    Author:     Jasmin Blanchette, TU Muenchen

The "meson" proof method for HOL.
*)

signature MESON_TACTIC =
sig
  val meson_general_tac : Proof.context -> thm list -> int -> tactic
end;

structure Meson_Tactic : MESON_TACTIC =
struct

fun meson_general_tac ctxt ths =
  let val ctxt' = put_claset HOL_cs ctxt
  in
    Meson.meson_tac ctxt' (maps (snd o Meson_Clausify.cnf_axiom Meson.simp_options_all_true ctxt'
      false true 0) ths)
  end

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>meson\<close> (Attrib.thms >> (fn ths => fn ctxt =>
      SIMPLE_METHOD' (CHANGED_PROP o meson_general_tac ctxt ths)))
      "MESON resolution proof procedure")

end;
