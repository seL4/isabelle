(*  Title: 	HOL/MiniML/ROOT.ML
    ID:         $Id$
    Author: 	Tobias Nipkow
    Copyright   1995 TUM

Type inference for let-free MiniML
*)

HOL_build_completed;	(*Make examples fail if HOL did*)

writeln"Root file for HOL/MiniML";
Unify.trace_bound := 20;

AddSEs [less_SucE];

time_use_thy "I";
