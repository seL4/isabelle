(*  Title:      HOL/Induct/Multiset0.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

This theory merely proves that the representation of multisets is nonempty.
*)

Goal "(%x.0) : {f. finite {x. 0 < f x}}";
by (Simp_tac 1);
qed "multiset_witness";
