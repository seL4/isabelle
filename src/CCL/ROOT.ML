(*  Title:      CCL/ROOT
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Adds Classical Computational Logic to a database containing First-Order Logic.
*)

val banner = "Classical Computational Logic (in FOL)";
writeln banner;

print_depth 1;
set eta_contract;

(* Higher-Order Set Theory Extension to FOL *)
(*      used as basis for CCL               *)

use_thy "Set";
use     "subset.ML";
use     "equalities.ML";
use     "mono.ML";
use_thy "Lfp";
use_thy "Gfp";

(* CCL - a computational logic for an untyped functional language *)
(*                       with evaluation to weak head-normal form *)

use_thy "CCL";
use_thy "Term";
use_thy "Type";
use     "coinduction.ML";
use_thy "Hered";

use_thy "Trancl";
use_thy "Wfd";
use     "genrec.ML";
use     "typecheck.ML";
use     "eval.ML";
use_thy "Fix";

print_depth 8;
