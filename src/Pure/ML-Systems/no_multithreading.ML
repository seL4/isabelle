(*  Title:      Pure/ML-Systems/no_multithreading.ML
    ID:         $Id$
    Author:     Makarius

Compatibility file for ML systems without multithreading.
*)

(* critical section *)

fun CRITICAL e = e ();
