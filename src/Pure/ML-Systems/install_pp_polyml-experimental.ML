(*  Title:      Pure/ML-Systems/install_pp_polyml-experimental.ML

Extra toplevel pretty-printing for Poly/ML 5.3 (SVN experimental).
*)

addPrettyPrinter (fn depth => fn pretty => fn x =>
  (case Future.peek x of
    NONE => PrettyString "<future>"
  | SOME (Exn.Exn _) => PrettyString "<failed>"
  | SOME (Exn.Result y) => pretty (y, depth)));

addPrettyPrinter (fn depth => fn pretty => fn x =>
  (case Lazy.peek x of
    NONE => PrettyString "<lazy>"
  | SOME (Exn.Exn _) => PrettyString "<failed>"
  | SOME (Exn.Result y) => pretty (y, depth)));

