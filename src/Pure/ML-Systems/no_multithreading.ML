(*  Title:      Pure/ML-Systems/no_multithreading.ML
    ID:         $Id$
    Author:     Makarius

Compatibility file for ML systems without multithreading.
*)

(*default number of worker threads*)
val multithreading = ref (NONE: int option);

(*critical section*)
fun self_critical () = false;
fun CRITICAL e = e ();
