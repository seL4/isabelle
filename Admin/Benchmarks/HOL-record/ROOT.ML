(*  Title:      Admin/Benchmarks/HOL-record/ROOT.ML

Some benchmark on large record.
*)

val tests = ["RecordBenchmark"];

timing := true;

warning "\nset quick_and_dirty\n"; quick_and_dirty := true;
use_thys tests;

warning "\nreset quick_and_dirty\n"; quick_and_dirty := false;
use_thys tests;
