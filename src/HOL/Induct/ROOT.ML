(*  Title:      HOL/Induct/ROOT
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1997  University of Cambridge

Exampled of Inductive Definitions
*)

HOL_build_completed;    (*Make examples fail if HOL did*)

writeln"Root file for HOL/Induct";
set proof_timing;
time_use_thy "Perm";
time_use_thy "Comb";
time_use_thy "Mutil";
time_use_thy "Acc";
time_use_thy "PropLog";
time_use_thy "SList";
time_use_thy "LFilter";
time_use_thy "Term";
time_use_thy "Simult";
time_use_thy "Exp";
