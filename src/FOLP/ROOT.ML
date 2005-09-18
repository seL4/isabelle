(*  Title:      FOLP/ROOT.ML
    ID:         $Id$
    Author:     martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Modifed version of Lawrence Paulson's FOL that contains proof terms.

Presence of unknown proof term means that matching does not behave as expected.
*)

val banner = "First-Order Logic with Natural Deduction with Proof Terms";
writeln banner;

use_thy "FOLP";
