(*  Title:      Pure/ML-Systems/ml_name_space_polyml.ML
    Author:     Makarius

Name space for Poly/ML.
*)

structure ML_Name_Space =
struct
  open PolyML.NameSpace;
  type T = nameSpace;
  val global = PolyML.globalNameSpace;
  val forget_global_structure = PolyML.Compiler.forgetStructure;
end;
