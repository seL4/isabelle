(*  Title:      HOL/Lex/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

HOL_build_completed;    (*Make examples fail if HOL did*)

use_thy"AutoChopper";
use_thy"AutoChopper1";
use_thy"AutoMaxChop";
(* Do not swap the next two use_thy's.
   There is some interference, probably via claset() or simpset().
   Or via ML-bound names of axioms that are overwritten?
*)
use_thy"RegSet_of_nat_DA";
use_thy"RegExp2NAe";
use_thy"Scanner";
