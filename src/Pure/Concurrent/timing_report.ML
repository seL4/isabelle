(*  Title:      Pure/Isar/timing_report.ML
    Author:     Thomas Sewell, Data61

Timing reports for long running tasks.
*)

signature TIMING_REPORT = sig
  type timer
  (* start/finish timing of tracked tasks *)
  val start: Position.T -> timer
  val finish: timer -> Timing.timing

  (* start logging: supply session name *)
  val start_logging: string -> unit
  val shutdown: unit -> unit
end

structure Timing_Report : TIMING_REPORT = struct

datatype active_timer = Active of Timing.start * Position.T
    * (int * bool) Synchronized.var

datatype timer = Timer of active_timer | Start of Timing.start

(* the timing output file, interval and callback, if activated *)
val timing_task = Synchronized.var "timing report generator"
    (NONE : (TextIO.outstream * Time.time * Event_Timer.request list) option)

(* new task timers. O(1) operations only *)
val new_timers = Synchronized.var "timers for timing reports"
    ([] : active_timer list)

(* task timers that have survived one round, accessed only by report thread *)
val inner_timers = Synchronized.var "timers for timing reports (internal use)"
    ([] : active_timer list)

fun bump (Active (_, _, v)) = Synchronized.change_result v
    (fn (bump_count, running) => (bump_count, (bump_count + 1, running)))

fun send_msg outfile msg
    = (TextIO.output (outfile, msg ^ "\n"); TextIO.flushOut outfile)

fun long_msg outfile (Active (start_time, pos, _))
    = send_msg outfile ("Long running task ("
        ^ Timing.message (Timing.result start_time)
        ^ ", at " ^ (Position.here pos) ^ ")")

fun bump_msg outfile timer = let
    val bump_count = bump timer
  in
    if bump_count >= 3 then (long_msg outfile timer; true) else false
  end

fun is_live (Active (_, _, v)) = Synchronized.value v |> snd

fun filter_timers () = let
    val new = Synchronized.change_result new_timers (fn ts => (ts, []))
    val filt_new = filter is_live new
  in
    Synchronized.change inner_timers (fn ts => filt_new @ filter is_live ts);
    length filt_new
  end

fun bump_msg_timers outfile = Synchronized.value inner_timers
    |> filter (bump_msg outfile)

fun pos_list_msg () = let
    val ps = Synchronized.value inner_timers
      |> map (fn (Active (_, pos, _)) => pos)
    val n = length ps
    fun opt_s NONE = "" | opt_s (SOME s) = s
    val lim = 10
    val files = map (Position.file_of #> opt_s) (take lim ps)
        |> map (Path.explode #> Path.file_name)
        |> sort_distinct fast_string_ord
  in "Running tasks: roughly " ^ string_of_int n ^ " running"
    ^ (if n = 0 then "." else " in ")
    ^ commas files ^ (if n > lim then ", etc" else "")
  end

fun report () = case Synchronized.value timing_task of
  SOME (file, _, _) => let
    (* task timers are added to the outer queue quickly. Filtering out all the
       finished tasks might take a while, leading to a stale picture. Running
       through the outer queue again brings us more up to date. *)
    val _ = filter_timers ()
    val _ = filter_timers ()
    val time = Time.now ()
    val _ = send_msg file ("Timing report at " ^ Time.toString time);
    val long = bump_msg_timers file;
  in
    if null long then send_msg file "  - no long-running tasks."
    else ();
    send_msg file (pos_list_msg ())
  end
  | NONE => ()

fun start pos = case Synchronized.value timing_task of
  SOME _ => let
    val nm = "timing report at " ^ Position.here pos
    val var = Synchronized.var nm (0, true)
    val timer = Active (Timing.start (), pos, var)
  in
    Synchronized.change new_timers (fn timers => timer :: timers);
    Timer timer
  end
  | NONE => Start (Timing.start ())

fun deactivate (Active (_, _, v)) = Synchronized.change v
        (fn (bump_count, _) => (bump_count, false))

fun active_result_time (Active (start_time, _, _)) = Timing.result start_time

fun finish (Timer active) = (deactivate active; active_result_time active)
  | finish (Start start) = Timing.result start

fun spawn f = case Synchronized.value timing_task of
  NONE => ()
  | SOME (_, intvl, _) => let
    val r = Event_Timer.request {physical=false} (intvl + Time.now ()) f
    val extras = Synchronized.change_result timing_task
        (fn NONE => ([r], NONE)
            | SOME (out, i, tasks) => (tasks, SOME (out, i, [r])))
  in app (Event_Timer.cancel #> ignore) extras end

fun timing_report_task () = let
    fun inner () = (report (); spawn timing_report_task)
  in
    Future.fork inner; ()
  end

fun log_path fname = let
    val isabelle_output = getenv "ISABELLE_OUTPUT"
    val log_base =
        if isabelle_output = ""
        then Path.append (Path.explode (getenv "ISABELLE_HEAPS"))
                         (Path.make [getenv "ML_IDENTIFIER"])
        else Path.explode isabelle_output
  in Path.append log_base (Path.make ["log", fname]) end

fun open_outfile session_name = let
    val fname = session_name ^ "_times.txt"
    val p_fname = log_path fname
    val out = TextIO.openOut (Path.implode p_fname)
    val _ = send_msg out ("Timing log for session " ^ session_name);
  in out end

(* FIXME: the canonical way to check ISABELLE_HEAPS and ISABELLE_TIMING_LOG
   would be in Scala, but that requires more engineering. *)
fun start_logging session_name = case Time.fromString (getenv "ISABELLE_TIMING_LOG") of
  NONE => ()
  | SOME intvl => let
    val out = open_outfile session_name
    val succ = Synchronized.change_result timing_task
        (fn NONE => (true, SOME (out, intvl, [])) | SOME v => (false, SOME v))
  in if succ then timing_report_task ()
    else error "repeat attempt to start time logging" end

fun shutdown () = let
    val v = Synchronized.change_result timing_task (fn v => (v, NONE))
  in case v of NONE => ()
    | SOME (out, _, tasks) =>
        (app (Event_Timer.cancel #> ignore) tasks;
            send_msg out "Timing log ends.";
            TextIO.closeOut out)
  end

end

