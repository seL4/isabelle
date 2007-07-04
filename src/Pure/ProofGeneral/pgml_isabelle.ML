(*  Title:      Pure/ProofGeneral/pgip_types.ML
    ID:         $Id$
    Author:     David Aspinall

PGIP abstraction: marshalling between PGML and Isabelle types
*)

signature PGML_ISABELLE =
sig
    val pgml_of_prettyT : PrettyExt.prettyT -> Pgml.pgmlterm
end

structure PgmlIsabelle : PGML_ISABELLE =
struct
   open Pgml;
   open PrettyExt;

   fun pgml_of_prettyT (Block(ts,ind,length)) =
       Box {orient = SOME HVOrient, indent = SOME ind, content = map pgml_of_prettyT ts}

     | pgml_of_prettyT (String (str,len)) = Atoms { kind = NONE, content = [Str str] }  
					    (* TODO: should unquote symbols *)

     | pgml_of_prettyT (Break (flag,ind)) = Pgml.Break { mandatory = SOME flag, indent = SOME ind }
end
