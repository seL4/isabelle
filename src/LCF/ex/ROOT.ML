(*  Title:      LCF/ex/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1991  University of Cambridge

Some examples from Lawrence Paulson's book Logic and Computation.
*)

writeln"Root file for LCF examples";
LCF_build_completed;    (*Cause examples to fail if LCF did*)

set proof_timing;

use_thy "Ex1";
use_thy "Ex2";
use_thy "Ex3";
use_thy "Ex4";
