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

local

open Try0_Util

(* name * (run_if_auto_try * (all_goals * tags)) *)
val raw_named_methods =
  [("auto", (true, (true, full_attrs))),
   ("blast", (true, (false, clas_attrs))),
   ("metis", (true, (false, metis_attrs))),
   ("argo", (true, (false, no_attrs))),
   ("linarith", (true, (false, no_attrs))),
   ("presburger", (true, (false, no_attrs))),
   ("algebra", (true, (false, no_attrs))),
   ("fast", (false, (false, clas_attrs))),
   ("fastforce", (false, (false, full_attrs))),
   ("force", (false, (false, full_attrs))),
   ("meson", (false, (false, metis_attrs))),
   ("satx", (false, (false, no_attrs))),
   ("order", (true, (false, no_attrs)))]

in

val () = raw_named_methods
  |> List.app (fn (name, (run_if_auto_try, (all_goals, tags))) =>
    let
      val meth : Try0.proof_method =
        Try0_Util.apply_raw_named_method name all_goals tags silence_methods
    in
      Try0.register_proof_method name {run_if_auto_try = run_if_auto_try} meth
      handle Symtab.DUP _ => ()
    end)

end

end
\<close>

declare [[try0_schedule = "
  satx metis
  order presburger linarith algebra argo
  simp auto blast fast fastforce force meson
"]]

end