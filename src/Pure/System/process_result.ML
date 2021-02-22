(*  Title:      Pure/System/process_result.scala
    Author:     Makarius

Result of system process.
*)

signature PROCESS_RESULT =
sig
  type T
  val make:
   {rc: int,
    out_lines: string list,
    err_lines: string list,
    timing: Timing.timing} -> T
  val rc: T -> int
  val out_lines: T -> string list
  val err_lines: T -> string list
  val timing: T -> Timing.timing
  val out: T -> string
  val err: T -> string
  val ok: T -> bool
  val interrupted: T -> bool
  val check_rc: (int -> bool) -> T -> T
  val check: T -> T
end;

structure Process_Result: PROCESS_RESULT =
struct

abstype T =
  Process_Result of
   {rc: int,
    out_lines: string list,
    err_lines: string list,
    timing: Timing.timing}
with

val make = Process_Result;
fun rep (Process_Result args) = args;

val rc = #rc o rep;
val out_lines = #out_lines o rep;
val err_lines = #err_lines o rep;
val timing = #timing o rep;

val out = trim_line o cat_lines o out_lines;
val err = trim_line o cat_lines o err_lines;

fun ok result = rc result = 0;
fun interrupted result = rc result = Exn.interrupt_return_code;

fun check_rc pred result =
  if pred (rc result) then result
  else if interrupted result then raise Exn.Interrupt
  else error (err result);

val check = check_rc (fn rc => rc = 0);

end;

end;
