(*  Title:      Pure/pure.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Final setup of the Pure theories.
*)

local
  val common_setup =
    Locale.setup @
    HTML.setup @
    ObjectLogic.setup @
    ProofContext.setup @
    Attrib.setup @
    InductAttrib.setup @
    Method.setup @
    Calculation.setup @
    SkipProof.setup @
    AxClass.setup @
    Latex.setup @
    Present.setup @
    Isamode.setup @
    ProofGeneral.setup @
    Codegen.setup;
in
  structure Pure =
  struct
    val thy =
      PureThy.begin_theory Sign.PureN [ProtoPure.thy]
      |> Theory.add_syntax Syntax.pure_appl_syntax
      |> Library.apply common_setup
      |> PureThy.end_theory;
  end;

  structure CPure =
  struct
    val thy =
      PureThy.begin_theory Sign.CPureN [ProtoPure.thy]
      |> Theory.add_syntax Syntax.pure_applC_syntax
      |> Library.apply common_setup
      |> Theory.copy
      |> PureThy.end_theory;
  end;
end;

ThyInfo.register_theory ProtoPure.thy;
ThyInfo.register_theory Pure.thy;
ThyInfo.register_theory CPure.thy;
