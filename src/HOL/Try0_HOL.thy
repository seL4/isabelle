(* Title:      HOL/Try0_HOL.thy
   Author:     Jasmin Blanchette, LMU Muenchen
   Author:     Martin Desharnais, LMU Muenchen
   Author:     Fabian Huch, TU Muenchen
*)
theory Try0_HOL
  imports Try0 Presburger
begin

ML \<open>
signature TRY0_HOL =
sig
  val silence_methods : Proof.context -> Proof.context
end

structure Try0_HOL : TRY0_HOL = struct

(* Makes reconstructor tools as silent as possible. The "set_visible" calls suppresses "Unification
   bound exceeded" warnings and the like. *)
fun silence_methods ctxt =
  ctxt
  |> Config.put Metis_Tactic.verbose false
  |> Simplifier_Trace.disable
  |> Context_Position.set_visible false
  |> Config.put Unify.unify_trace false
  |> Config.put Argo_Tactic.trace "none"

end
\<close>

setup \<open>
  let
    open Try0_Util

    (* name * (run_if_auto_try * (all_goals * tags)) *)
    val raw_named_methods =
      [("auto", (true, (true, full_attrs))),
       ("blast", (true, (false, clas_attrs))),
       ("metis", (true, (false, Direct_Args))),
       ("argo", (true, (false, Direct_Args))),
       ("linarith", (true, (false, No_Args))),
       ("presburger", (true, (false, No_Args))),
       ("algebra", (true, (false, No_Args))),
       ("fast", (false, (false, clas_attrs))),
       ("fastforce", (false, (false, full_attrs))),
       ("force", (false, (false, full_attrs))),
       ("meson", (false, (false, Direct_Args))),
       ("satx", (false, (false, No_Args))),
       ("order", (true, (false, No_Args)))]
  in
    Context.theory_map (raw_named_methods
      |> fold (fn (name, (run_if_auto_try, (all_goals, tags))) =>
        Try0.register_proof_method name {run_if_auto_try = run_if_auto_try}
          (apply_raw_named_method name all_goals tags Try0_HOL.silence_methods)))
  end
\<close>

declare [[try0_schedule = "
  satx metis
  order presburger linarith algebra argo
  simp auto blast fast fastforce force meson
"]]

end