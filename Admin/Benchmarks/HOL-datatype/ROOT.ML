(*  Title:      Admin/Benchmarks/HOL-datatype/ROOT.ML

Some rather large datatype examples (from John Harrison).
*)

val tests = ["Brackin", "Instructions", "SML", "Verilog"];

Unsynchronized.set timing;

warning "\nset quick_and_dirty\n"; Unsynchronized.set quick_and_dirty;
use_thys tests;

warning "\nreset quick_and_dirty\n"; Unsynchronized.reset quick_and_dirty;
List.app Thy_Info.remove_thy tests;
use_thys tests;
