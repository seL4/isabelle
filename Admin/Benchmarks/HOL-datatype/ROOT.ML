(*  Title:      Admin/Benchmarks/HOL-datatype/ROOT.ML
    ID:         $Id$

Some rather large datatype examples (from John Harrison).
*)

val tests = ["Brackin", "Instructions", "SML", "Verilog"];

set timing;

warning "\nset quick_and_dirty\n"; set quick_and_dirty;
List.app time_use_thy tests;

warning "\nreset quick_and_dirty\n"; reset quick_and_dirty;
List.app remove_thy tests;
List.app time_use_thy tests;
