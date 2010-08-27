(*  Title:      Admin/Benchmarks/HOL-datatype/ROOT.ML

Some rather large datatype examples (from John Harrison).
*)

val tests = ["Brackin", "Instructions", "SML", "Verilog"];

timing := true;

warning "\nset quick_and_dirty\n"; quick_and_dirty := true;
use_thys tests;

warning "\nreset quick_and_dirty\n"; quick_and_dirty := false;
List.app Thy_Info.remove_thy tests;
use_thys tests;
