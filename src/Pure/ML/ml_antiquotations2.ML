(*  Title:      Pure/ML/ml_antiquotations2.ML
    Author:     Makarius

Miscellaneous ML antiquotations: part 2.
*)

structure ML_Antiquotations2: sig end =
struct

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>method\<close>
    (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, (name, pos)) =>
      ML_Syntax.print_string (Method.check_name ctxt (name, pos)))) #>

  ML_Antiquotation.inline_embedded \<^binding>\<open>locale\<close>
   (Args.context -- Scan.lift Args.embedded_position >> (fn (ctxt, (name, pos)) =>
      Locale.check (Proof_Context.theory_of ctxt) (name, pos)
      |> ML_Syntax.print_string)));

end;
