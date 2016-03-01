(*  Title:      Pure/RAW/use_context.ML
    Author:     Makarius

Common context for "use" operations (compiler invocation).
*)

type use_context =
 {name_space: ML_Name_Space.T,
  str_of_pos: int -> string -> string,
  print: string -> unit,
  error: string -> unit};

val boot_context: use_context =
 {name_space = ML_Name_Space.global,
  str_of_pos = fn line => fn file => " (line " ^ Int.toString line ^ " of \"" ^ file ^ "\")",
  print = fn s => (TextIO.output (TextIO.stdOut, s ^ "\n"); TextIO.flushOut TextIO.stdOut),
  error = fn s => raise Fail s};
