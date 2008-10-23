(*  Title:      Pure/ML-Systems/install_pp_polyml.ML
    ID:         $Id$

Extra toplevel pretty-printing for Poly/ML.
*)

install_pp (fn (str, _, _, _) => fn depth => fn (print: 'a * int -> unit) => fn (x: 'a Future.T) =>
  (case Future.peek x of
    NONE => str "<future>"
  | SOME (Exn.Exn _) => str "<failed>"
  | SOME (Exn.Result y) => print (y, depth)));

install_pp (fn (str, _, _, _) => fn depth => fn (print: 'a * int -> unit) => fn (x: 'a Susp.T) =>
  (case Susp.peek x of
    NONE => str "<delayed>"
  | SOME (Exn.Exn _) => str "<failed>"
  | SOME (Exn.Result y) => print (y, depth)));

