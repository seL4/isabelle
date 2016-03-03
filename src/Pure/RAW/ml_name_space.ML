(*  Title:      Pure/RAW/ml_name_space.ML
    Author:     Makarius

Name space for Poly/ML.
*)

structure ML_Name_Space =
struct
  open PolyML.NameSpace;

  type T = PolyML.NameSpace.nameSpace;
  val global = PolyML.globalNameSpace;
  val forget_global_structure = PolyML.Compiler.forgetStructure;

  type valueVal = Values.value;
  fun displayVal (x, depth, space) = Values.printWithType (x, depth, SOME space);
  fun displayTypeExpression (x, depth, space) = Values.printType (x, depth, SOME space);

  type typeVal = TypeConstrs.typeConstr;
  fun displayType (x, depth, space) = TypeConstrs.print (x, depth, SOME space);

  type fixityVal = Infixes.fixity;
  fun displayFix (_: string, x) = Infixes.print x;

  type structureVal = Structures.structureVal;
  fun displayStruct (x, depth, space) = Structures.print (x, depth, SOME space);

  type signatureVal = Signatures.signatureVal;
  fun displaySig (x, depth, space) = Signatures.print (x, depth, SOME space);

  type functorVal = Functors.functorVal;
  fun displayFunct (x, depth, space) = Functors.print (x, depth, SOME space);
end;
