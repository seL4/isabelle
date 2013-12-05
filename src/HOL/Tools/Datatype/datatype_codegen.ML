(*  Title:      HOL/Tools/Datatype/datatype_codegen.ML
    Author:     Stefan Berghofer and Florian Haftmann, TU Muenchen

Code generator facilities for inductive datatypes.
*)

signature DATATYPE_CODEGEN =
sig
end;

structure Datatype_Codegen : DATATYPE_CODEGEN =
struct

fun add_code_for_datatype fcT_name thy =
  let
    val (As', ctr_specs) = Datatype_Data.the_spec thy fcT_name;
    val {inject = inject_thms, distinct = distinct_thms, case_rewrites = case_thms, ...} =
      Datatype_Data.the_info thy fcT_name;

    val As = map TFree As';
    val fcT = Type (fcT_name, As);
    val ctrs = map (fn (c, arg_Ts) => (c, arg_Ts ---> fcT)) ctr_specs;
  in
    Ctr_Sugar_Code.add_ctr_code fcT_name As ctrs inject_thms distinct_thms case_thms thy
  end;

val _ = Theory.setup (Datatype_Data.interpretation (K (fold add_code_for_datatype)));

end;
