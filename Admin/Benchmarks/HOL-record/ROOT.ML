(*  Title:      Admin/Benchmarks/HOL-record/ROOT.ML

Some benchmark on large record
*)

val tests = ["RecordBenchmark"];

Unsynchronized.set timing;

warning "\nset quick_and_dirty\n"; Unsynchronized.set quick_and_dirty;
List.app time_use_thy tests;

warning "\nreset quick_and_dirty\n"; Unsynchronized.reset quick_and_dirty;
List.app time_use_thy tests;
