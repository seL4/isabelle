(*  Title:      ZF/UNITY/ROOT.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

ZF/UNITY proofs.
*)

use_thys [
  (*Simple examples: no composition*)
  "Mutex",

  (*Basic meta-theory*)
  "Guar",

  (*Prefix relation; the Allocator example*)
  "Distributor", "Merge", "ClientImpl", "AllocImpl"
];
