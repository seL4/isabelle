(*  Title:      Pure/ML-Systems/install_pp_polyml-experimental.ML

Extra toplevel pretty-printing for Poly/ML; experimental version for
Poly/ML 5.3.
*)

local

fun pretty_future depth (pretty: 'a * int -> pretty) (x: 'a future) =
  (case Future.peek x of
    NONE => PrettyString "<future>"
  | SOME (Exn.Exn _) => PrettyString "<failed>"
  | SOME (Exn.Result y) => pretty (y, depth));

fun pretty_lazy depth (pretty: 'a * int -> pretty) (x: 'a lazy) =
  (case Lazy.peek x of
    NONE => PrettyString "<lazy>"
  | SOME (Exn.Exn _) => PrettyString "<failed>"
  | SOME (Exn.Result y) => pretty (y, depth));

in

val _ = addPrettyPrinter pretty_future;
val _ = addPrettyPrinter pretty_lazy;

end;

