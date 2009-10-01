(*  Title:      CCL/ROOT.ML
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Classical Computational Logic based on First-Order Logic.

A computational logic for an untyped functional language with
evaluation to weak head-normal form.
*)

Unsynchronized.set eta_contract;

use_thys ["Wfd", "Fix"];
