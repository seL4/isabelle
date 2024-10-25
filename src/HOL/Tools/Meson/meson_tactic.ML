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
      {new_skolem = false, combs = true, refl = true} 0) ths)
  end

(* This is part of a workaround to avoid freezing schematic variables in \<^text>\<open>using\<close> facts. See
   \<^file>\<open>~~/src/HOL/Tools/Metis/metis_tactic.ML\<close> for details. *)
val has_tvar = exists_type (exists_subtype (fn TVar _ => true | _ => false)) o Thm.prop_of

val _ =
  Theory.setup
    (Method.setup \<^binding>\<open>meson\<close> (Attrib.thms >> (fn ths => fn ctxt0 =>
      CONTEXT_METHOD (fn facts => fn (ctxt, st) =>
        let val (schem_facts, nonschem_facts) = List.partition has_tvar facts in
          st
          |> HEADGOAL (Method.insert_tac ctxt nonschem_facts THEN'
            CHANGED_PROP o meson_general_tac ctxt0 (schem_facts @ ths))
          |> TACTIC_CONTEXT ctxt
        end)))
      "MESON resolution proof procedure")

end;
