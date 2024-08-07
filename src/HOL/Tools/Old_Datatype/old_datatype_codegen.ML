(*  Title:      HOL/Tools/Old_Datatype/old_datatype_codegen.ML
    Author:     Stefan Berghofer and Florian Haftmann, TU Muenchen

Code generator facilities for inductive datatypes.
*)

signature OLD_DATATYPE_CODEGEN =
sig
end;

structure Old_Datatype_Codegen : OLD_DATATYPE_CODEGEN =
struct

fun add_code_for_datatype fcT_name thy =
  let
    val ctxt = Proof_Context.init_global thy
    val SOME {ctrs, injects, distincts, case_thms, ...} = Ctr_Sugar.ctr_sugar_of ctxt fcT_name
    val As = dest_Type_args (body_type (fastype_of (hd ctrs)))
  in
    Ctr_Sugar_Code.add_ctr_code fcT_name As (map dest_Const ctrs) injects distincts case_thms thy
  end;

val _ = Theory.setup (Old_Datatype_Data.interpretation (K (fold add_code_for_datatype)));

end;
