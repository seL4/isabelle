(*  Title:      Pure/pure.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Final setup of the Pure theories.
*)

local
  val common_setup =
    ObjectLogic.setup @
    Locale.setup @
    HTML.setup @
    ProofContext.setup @
    Method.setup @
    Attrib.setup @
    AxClass.setup @
    BrowserInfo.setup @
    Isamode.setup @
    ProofGeneral.setup;
in
  structure Pure =
  struct
    val thy =
      PureThy.begin_theory "Pure" [ProtoPure.thy]
      |> Theory.add_syntax Syntax.pure_appl_syntax
      |> Library.apply common_setup
      |> PureThy.end_theory;
  end;

  structure CPure =
  struct
    val thy =
      PureThy.begin_theory "CPure" [ProtoPure.thy]
      |> Theory.add_syntax Syntax.pure_applC_syntax
      |> Library.apply common_setup
      |> Theory.copy
      |> PureThy.end_theory;
  end;
end;

ThyInfo.register_theory ProtoPure.thy;
ThyInfo.register_theory Pure.thy;
ThyInfo.register_theory CPure.thy;
