(*  Title:      Pure/ML/ml_antiquotations2.ML
    Author:     Makarius

Miscellaneous ML antiquotations: part 2.
*)

structure ML_Antiquotations2: sig end =
struct

val _ = Theory.setup
 (ML_Antiquotation.inline_embedded \<^binding>\<open>method\<close>
    (Args.context -- Scan.lift Args.embedded_position >>
      (ML_Syntax.print_string o uncurry Method.check_name)) #>

  ML_Antiquotation.inline_embedded \<^binding>\<open>locale\<close>
   (Args.theory -- Scan.lift Args.embedded_position >>
      (ML_Syntax.print_string o uncurry Locale.check)));

end;
