(*  Title:      HOL/Modelcheck/ROOT.ML
    ID:         $Id$
    Author:     Olaf Mueller and Tobias Hamberger and Robert Sandner, TU Muenchen

Basic Modelchecker examples.
*)


(* Mucke -- mu-calculus model checker from Karlsruhe *)

time_use "mucke_oracle.ML";
time_use_thy "MuckeSyn";

if_mucke_enabled time_use_thy "MuckeExample1";
if_mucke_enabled time_use_thy "MuckeExample2";


(* Einhoven model checker *)

time_use_thy "CTL";
time_use_thy "EindhovenSyn";

if_eindhoven_enabled time_use_thy "EindhovenExample";
