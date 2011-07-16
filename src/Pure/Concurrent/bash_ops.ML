(*  Title:      Pure/Concurrent/bash_ops.ML
    Author:     Makarius

Derived operations for bash_process.
*)

fun bash_output s =
  let val {output, rc, ...} = bash_process s
  in (output, rc) end;

fun bash s =
  (case bash_output s of
    ("", rc) => rc
  | (out, rc) => (writeln (perhaps (try (unsuffix "\n")) out); rc));

