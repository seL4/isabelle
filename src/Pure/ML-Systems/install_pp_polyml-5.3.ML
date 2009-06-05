(*  Title:      Pure/ML-Systems/install_pp_polyml-5.3.ML

Extra toplevel pretty-printing for Poly/ML 5.3.
*)

PolyML.addPrettyPrinter (fn depth => fn pretty => fn x =>
  (case Future.peek x of
    NONE => PolyML.PrettyString "<future>"
  | SOME (Exn.Exn _) => PolyML.PrettyString "<failed>"
  | SOME (Exn.Result y) => pretty (y, depth)));

PolyML.addPrettyPrinter (fn depth => fn pretty => fn x =>
  (case Lazy.peek x of
    NONE => PolyML.PrettyString "<lazy>"
  | SOME (Exn.Exn _) => PolyML.PrettyString "<failed>"
  | SOME (Exn.Result y) => pretty (y, depth)));

