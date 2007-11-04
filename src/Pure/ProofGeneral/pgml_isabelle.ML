(*  Title:      Pure/ProofGeneral/pgml_isabelle.ML
    ID:         $Id$
    Author:     David Aspinall

PGML print mode for common Isabelle markup.
*)

signature PGML_ISABELLE =
sig
  val pgml_mode: ('a -> 'b) -> 'a -> 'b
end

structure PgmlIsabelle : PGML_ISABELLE =
struct

(** print mode **)

val pgmlN = "PGML";
fun pgml_mode f x = PrintMode.with_modes [pgmlN] f x;

val _ = Output.add_mode pgmlN Output.default_output Output.default_escape;
val _ = Markup.add_mode pgmlN (fn markup as (name, _) => ("", ""));

end;
