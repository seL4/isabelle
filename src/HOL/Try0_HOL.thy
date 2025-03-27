(* Title:      HOL/Try0_HOL.thy
   Author:     Jasmin Blanchette, LMU Muenchen
   Author:     Martin Desharnais, LMU Muenchen
   Author:     Fabian Huch, TU Muenchen
*)
theory Try0_HOL
  imports Try0 Presburger
begin


ML_file \<open>Tools/try0_util.ML\<close>

ML \<open>
val _ =
  Try.tool_setup
   {name = "try0", weight = 30, auto_option = \<^system_option>\<open>auto_methods\<close>,
    body = fn auto => fst o Try0.generic_try0 (if auto then Try0.Auto_Try else Try0.Try) NONE []}
\<close>

ML \<open>
local

val full_attrs = [(Try0.Simp, "simp"), (Try0.Intro, "intro"), (Try0.Elim, "elim"), (Try0.Dest, "dest")]
val clas_attrs = [(Try0.Intro, "intro"), (Try0.Elim, "elim"), (Try0.Dest, "dest")]
val simp_attrs = [(Try0.Simp, "add")]
val metis_attrs = [(Try0.Simp, ""), (Try0.Intro, ""), (Try0.Elim, ""), (Try0.Dest, "")]
val no_attrs = []

(* name * (run_if_auto_try * (all_goals * tags)) *)
val raw_named_methods =
  [("simp", (true, (false, simp_attrs))),
   ("auto", (true, (true, full_attrs))),
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
    let val meth : Try0.proof_method = Try0_Util.apply_raw_named_method name all_goals tags in
      Try0.register_proof_method name {run_if_auto_try = run_if_auto_try} meth
      handle Symtab.DUP _ => ()
    end)

end
\<close>

end