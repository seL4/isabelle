(*  Title:      HOL/W0/ROOT.ML
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TUM

Type inference for let-free MiniML
*)

writeln"Root file for HOL/W0";

Unify.trace_bound := 20;

AddSEs [less_SucE];

time_use_thy "I";
