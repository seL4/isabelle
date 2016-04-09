(*  Title:      Pure/ML/ml_name_space.ML
    Author:     Makarius

ML name space, with initial entries for strict Standard ML.
*)

structure ML_Name_Space =
struct
  open PolyML.NameSpace;

  type T = PolyML.NameSpace.nameSpace;

  val global = PolyML.globalNameSpace;
  fun global_values values : T =
   {lookupVal = #lookupVal global,
    lookupType = #lookupType global,
    lookupStruct = #lookupStruct global,
    lookupFix = #lookupFix global,
    lookupSig = #lookupSig global,
    lookupFunct = #lookupFunct global,
    enterVal =
      fn (x, value) =>
        (case List.find (fn (y, _) => x = y) values of
          SOME (_, x') => #enterVal global (x', value)
        | NONE => ()),
    enterType = fn _ => (),
    enterFix = fn _ => (),
    enterStruct = fn _ => (),
    enterSig = fn _ => (),
    enterFunct = fn _ => (),
    allVal = #allVal global,
    allType = #allType global,
    allFix = #allFix global,
    allStruct = #allStruct global,
    allSig = #allSig global,
    allFunct = #allFunct global};

  type valueVal = Values.value;
  fun displayVal (x, depth, space) = Values.printWithType (x, depth, SOME space);
  fun displayTypeExpression (x, depth, space) = Values.printType (x, depth, SOME space);
  val forget_val = PolyML.Compiler.forgetValue;

  type typeVal = TypeConstrs.typeConstr;
  fun displayType (x, depth, space) = TypeConstrs.print (x, depth, SOME space);
  val forget_type = PolyML.Compiler.forgetType;

  type fixityVal = Infixes.fixity;
  fun displayFix (_: string, x) = Infixes.print x;

  type structureVal = Structures.structureVal;
  fun displayStruct (x, depth, space) = Structures.print (x, depth, SOME space);
  val forget_structure = PolyML.Compiler.forgetStructure;

  type signatureVal = Signatures.signatureVal;
  fun displaySig (x, depth, space) = Signatures.print (x, depth, SOME space);

  type functorVal = Functors.functorVal;
  fun displayFunct (x, depth, space) = Functors.print (x, depth, SOME space);


  (* bootstrap environment *)

  val bootstrap_values =
    ["use", "exit", "ML_file", "ML_system_pretty", "ML_system_pp", "ML_system_overload",
      "chapter", "section", "subsection", "subsubsection", "paragraph", "subparagraph"];
  val hidden_structures = ["CInterface", "Foreign", "RunCall", "RuntimeCalls", "Signal"];
  val bootstrap_structures =
    ["Exn", "Basic_Exn", "Thread_Data", "Thread_Position", "ML_Recursive", "PolyML"] @
      hidden_structures;
  val bootstrap_signatures =
    ["EXN", "BASIC_EXN", "THREAD_DATA", "THREAD_POSITION", "ML_RECURSIVE"];


  (* Standard ML environment *)

  val sml_val =
    List.filter (fn (a, _) => List.all (fn b => a <> b) bootstrap_values) (#allVal global ());
  val sml_type = #allType global ();
  val sml_fixity = #allFix global ();
  val sml_structure =
    List.filter (fn (a, _) => List.all (fn b => a <> b) bootstrap_structures) (#allStruct global ());
  val sml_signature =
    List.filter (fn (a, _) => List.all (fn b => a <> b) bootstrap_signatures) (#allSig global ());
  val sml_functor = #allFunct global ();
end;
