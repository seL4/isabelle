(*  Title:      ZF/UNITY/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Root file for ZF/UNITY proofs.
*)

add_path "../Induct";  (*for Multisets*)

(*Simple examples: no composition*)
time_use_thy"Mutex";

(*Basic meta-theory*)
time_use_thy "Guar";

(* Prefix relation; the Allocator example *)
time_use_thy "Distributor";
time_use_thy "Merge";
time_use_thy "ClientImpl";
time_use_thy "AllocImpl";
