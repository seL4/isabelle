(*  Title:      Pure/pure.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Setup the actual Pure and CPure theories.
*)

local
  val common_setup =
    ObjectLogic.setup @
    Locale.setup @
    ProofContext.setup @
    Method.setup @
    Attrib.setup;
in
  structure Pure =
  struct
    val thy =
      PureThy.begin_theory "Pure" [ProtoPure.thy]
      |> Theory.add_syntax Syntax.pure_appl_syntax
      |> Theory.apply common_setup
      |> PureThy.end_theory;
  end;

  structure CPure =
  struct
    val thy =
      PureThy.begin_theory "CPure" [ProtoPure.thy]
      |> Theory.add_syntax Syntax.pure_applC_syntax
      |> Theory.apply common_setup
      |> Theory.copy
      |> PureThy.end_theory;
  end;
end;

ThyInfo.loaded_thys :=
  (Symtab.make (map ThyInfo.mk_info
    [("ProtoPure", ["Pure", "CPure"], [], ProtoPure.thy),
     ("Pure", [], ["ProtoPure"], Pure.thy),
     ("CPure", [], ["ProtoPure"], CPure.thy)]));
