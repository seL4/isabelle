(*  Title:      HOL/Modelcheck/ROOT.ML
    ID:         $Id$
    Author:     Olaf Mueller and Tobias Hamberger and Robert Sandner, TU Muenchen

Basic Modelchecker examples.
*)


(* Mucke -- mu-calculus model checker from Karlsruhe *)

use "mucke_oracle.ML";
use_thy "MuckeSyn";

if_mucke_enabled use_thy "MuckeExample1";
if_mucke_enabled use_thy "MuckeExample2";


(* Einhoven model checker *)

use_thy "CTL";
use_thy "EindhovenSyn";

if_eindhoven_enabled use_thy "EindhovenExample";
