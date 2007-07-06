(*  Title:      Pure/ProofGeneral/pgip_types.ML
    ID:         $Id$
    Author:     David Aspinall

PGIP abstraction: marshalling between PGML and Isabelle types
*)

signature PGML_ISABELLE =
sig
(*    val pgml_of_prettyT : Pretty.T -> Pgml.pgmlterm *)
end

structure PgmlIsabelle : PGML_ISABELLE =
struct
   open Pgml;
   open Pretty;

(*   fun pgml_of_prettyT1 (Block(ts,ind,length)) =
       Box {orient = SOME HVOrient, indent = SOME ind, content = map pgml_of_prettyT1 ts}

     | pgml_of_prettyT1 (String (str,len)) = Atoms { kind = NONE, content = [Str str] }  
					    (* TODO: should unquote symbols *)

     | pgml_of_prettyT1 (Break (flag,ind)) = Pgml.Break { mandatory = SOME flag, indent = SOME ind }

   val pgml_of_prettyT = pgml_of_prettyT1 o dest_prettyT;
*)
end
