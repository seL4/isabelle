(*  Title:      Admin/Benchmarks/HOL-datatype/ROOT.ML
    ID:         $Id$

Some rather large datatype examples (from John Harrison).
*)

val tests = ["Brackin", "Instructions", "SML", "Verilog"];

set Toplevel.trace;

warning "\nset quick_and_dirty\n"; set quick_and_dirty;
seq time_use_thy tests;

warning "\nreset quick_and_dirty\n"; reset quick_and_dirty;
seq remove_thy tests;
seq time_use_thy tests;
