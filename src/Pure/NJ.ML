(*  Title:      Pure/NJ
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Compatibility file for Standard ML of New Jersey.
*)


(*Determine if we are running under 0.93 or a newer version of SML/NJ
  This is based on the variable "version" defined in 0.93's System structure
  which is no longer present in 1.09.*)

local val version = ""; open System in
  val smlversion = if version <> "" then 93 else 109
end;

use (if smlversion = 93 then "NJ093.ML" else "NJ1xx.ML");


(** Other functions which are not specific to 0.93 or 1.xx*)

(*Dummy version of the Poly/ML function*)
fun commit() = ();
