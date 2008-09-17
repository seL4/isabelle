(*  Title:      HOL/Modelcheck/ROOT.ML
    ID:         $Id$
    Author:     Olaf Mueller and Tobias Hamberger and Robert Sandner, TU Muenchen

Basic Modelchecker examples.
*)

time_use_thy "CTL";


(* Einhoven model checker *)

(*check if user has pmu installed*)
fun eindhoven_enabled () = getenv "EINDHOVEN_HOME" <> "";
fun if_eindhoven_enabled f x = if eindhoven_enabled () then f x else ();

time_use_thy "EindhovenSyn";
if_eindhoven_enabled time_use_thy "EindhovenExample";


(* Mucke -- mu-calculus model checker from Karlsruhe *)

time_use_thy "MuckeSyn";

(*check if user has mucke installed*)
fun mucke_enabled () = getenv "MUCKE_HOME" <> "";
fun if_mucke_enabled f x = if mucke_enabled () then f x else ();

if_mucke_enabled time_use_thy "MuckeExample1";
if_mucke_enabled time_use_thy "MuckeExample2";
