(*  Title:      Pure/ML/exn_debugger.ML
    Author:     Makarius

Detailed exception trace via ML debugger.
*)

signature EXN_DEBUGGER =
sig
  val capture_exception_trace: (unit -> 'a) -> (string * ML_Debugger.location) list * 'a Exn.result
end;

structure Exn_Debugger: EXN_DEBUGGER =
struct

(* thread data *)

local
  val tag = Universal.tag () : ((string * ML_Debugger.location) * exn) list option Universal.tag;
in

fun start_trace () = Thread.setLocal (tag, SOME []);

fun update_trace entry exn =
  (case Thread.getLocal tag of
    SOME (SOME trace) => Thread.setLocal (tag, SOME ((entry, exn) :: trace))
  | _ => ());

fun stop_trace () =
  let
    val trace = (case Thread.getLocal tag of SOME (SOME trace) => trace | _ => []);
    val _ = Thread.setLocal (tag, NONE);
  in trace end;

val _ = ML_Debugger.on_exit_exception (SOME update_trace);

end;


(* capture exception trace *)

local
  fun eq_exn exns =
    op = (apply2 General.exnName exns) andalso op = (apply2 Exn_Output.position exns);
in

fun capture_exception_trace e =
  uninterruptible (fn restore_attributes => fn () =>
    let
      val _ = start_trace ();
      val result = Exn.interruptible_capture (restore_attributes e) ();
      val trace = stop_trace ();
      val trace' =
        (case result of
          Exn.Res _ => []
        | Exn.Exn exn =>
            trace
            |> map_filter (fn (entry, e) => if eq_exn (exn, e) then SOME entry else NONE)
            |> rev);
    in (trace', result) end) ();

end;

end;
