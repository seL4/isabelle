(*  Title:      CCL/ROOT.ML
    ID:         $Id$
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Classical Computational Logic based on First-Order Logic.
*)

val banner = "Classical Computational Logic (in FOL)";
writeln banner;

set eta_contract;

(* CCL - a computational logic for an untyped functional language *)
(*                       with evaluation to weak head-normal form *)

use_thy "CCL";
use_thy "Hered";
use_thy "Wfd";
use_thy "Fix";
