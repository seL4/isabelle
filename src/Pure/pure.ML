(*  Title:      Pure/pure.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Setup the actual Pure and CPure theories.
*)

structure Pure =
struct
  val thy =
    PureThy.begin_theory "Pure" [ProtoPure.thy]
    |> Theory.add_syntax Syntax.pure_appl_syntax
    |> PureThy.end_theory;
end;

structure CPure =
struct
  val thy =
    PureThy.begin_theory "CPure" [ProtoPure.thy]
    |> Theory.add_syntax Syntax.pure_applC_syntax
    |> PureThy.end_theory;
end;

ThyInfo.loaded_thys :=
  (Symtab.make (map ThyInfo.mk_info
    [("ProtoPure", ["Pure", "CPure"], [], ProtoPure.thy),
     ("Pure", [], ["ProtoPure"], Pure.thy),
     ("CPure", [], ["ProtoPure"], CPure.thy)]));
