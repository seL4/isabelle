(*  Title:      CCL/ROOT
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Adds Classical Computational Logic to a database containing First-Order Logic.
*)

val banner = "Classical Computational Logic (in FOL)";

(* Higher-Order Set Theory Extension to FOL *)
(*      used as basis for CCL               *)

use_thy "set";
use     "subset.ML";
use     "equalities.ML";
use     "mono.ML";
use_thy "lfp";
use_thy "gfp";

(* CCL - a computational logic for an untyped functional language *)
(*                       with evaluation to weak head-normal form *)

use_thy "ccl";
use_thy "terms";
use_thy "types";
use     "coinduction.ML";
use_thy "hered";

use_thy "trancl";
use_thy "wf";
use     "genrec.ML";
use     "typecheck.ML";
use     "eval.ML";
use_thy "fix";

val CCL_build_completed = ();   (*indicate successful build*)
