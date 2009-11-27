(*  Title:      HOL/Tools/datatype.ML
    Author:     Stefan Berghofer, TU Muenchen

Datatype package interface for Isabelle/HOL.
*)

signature DATATYPE =
sig
  include DATATYPE_DATA
  include DATATYPE_REP_PROOFS
end;

structure Datatype =
struct

open Datatype_Data;
open DatatypeRepProofs;

end;
