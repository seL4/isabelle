(*  Title:      Pure/ML/ml_name_space.ML
    Author:     Makarius

Name space for Poly/ML.
*)

structure ML_Name_Space =
struct
  val critical_structures = ["CInterface", "Foreign", "RunCall", "RuntimeCalls", "Signal"];

  open PolyML.NameSpace;

  type T = PolyML.NameSpace.nameSpace;
  val global = PolyML.globalNameSpace;

  type valueVal = Values.value;
  fun displayVal (x, depth, space) = Values.printWithType (x, depth, SOME space);
  fun displayTypeExpression (x, depth, space) = Values.printType (x, depth, SOME space);
  val initial_val = List.filter (fn (a, _) => a <> "use" andalso a <> "exit") (#allVal global ());
  val forget_val = PolyML.Compiler.forgetValue;

  type typeVal = TypeConstrs.typeConstr;
  fun displayType (x, depth, space) = TypeConstrs.print (x, depth, SOME space);
  val initial_type = #allType global ();
  val forget_type = PolyML.Compiler.forgetType;

  type fixityVal = Infixes.fixity;
  fun displayFix (_: string, x) = Infixes.print x;
  val initial_fixity = #allFix global ();

  type structureVal = Structures.structureVal;
  fun displayStruct (x, depth, space) = Structures.print (x, depth, SOME space);
  val initial_structure =
    List.filter (fn (a, _) => not (List.exists (fn b => a = b) critical_structures))
      (#allStruct global ());
  val forget_structure = PolyML.Compiler.forgetStructure;

  type signatureVal = Signatures.signatureVal;
  fun displaySig (x, depth, space) = Signatures.print (x, depth, SOME space);
  val initial_signature = #allSig global ();

  type functorVal = Functors.functorVal;
  fun displayFunct (x, depth, space) = Functors.print (x, depth, SOME space);
  val initial_functor = #allFunct global ();
end;
