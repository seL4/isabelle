(*  Title:      Pure/System/bash.ML
    Author:     Makarius

GNU bash processes, with propagation of interrupts -- POSIX version.
*)

signature BASH =
sig
  val string: string -> string
  val strings: string list -> string
  val process: string -> {out: string, err: string, rc: int}
end;

structure Bash: BASH =
struct

val string = Bash_Syntax.string;
val strings = Bash_Syntax.strings;

fun process script =
  Scala.function_thread "bash_process"
    ("export ISABELLE_TMP=" ^ string (getenv "ISABELLE_TMP") ^ "\n" ^ script)
  |> YXML.parse_body
  |>
    let open XML.Decode in
      variant
       [fn ([], []) => raise Exn.Interrupt,
        fn ([], a) => error (YXML.string_of_body a),
        fn ([a], c) =>
          let
            val rc = int_atom a;
            val (out, err) = pair I I c |> apply2 YXML.string_of_body;
          in {out = out, err = err, rc = rc} end]
    end;

end;
