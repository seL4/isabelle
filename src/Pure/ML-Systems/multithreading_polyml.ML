(*  Title:      Pure/ML-Systems/multithreading_polyml.ML
    Author:     Makarius

Multithreading in Poly/ML 5.2.1 or later (cf. polyml/basis/Thread.sml).
*)

signature MULTITHREADING_POLYML =
sig
  val interruptible: ('a -> 'b) -> 'a -> 'b
  val uninterruptible: ((('c -> 'd) -> 'c -> 'd) -> 'a -> 'b) -> 'a -> 'b
  val system_out: string -> string * int
  structure TimeLimit: TIME_LIMIT
end;

signature BASIC_MULTITHREADING =
sig
  include BASIC_MULTITHREADING
  include MULTITHREADING_POLYML
end;

signature MULTITHREADING =
sig
  include MULTITHREADING
  include MULTITHREADING_POLYML
end;

structure Multithreading: MULTITHREADING =
struct

(* options *)

val available = true;

val max_threads = Unsynchronized.ref 0;

val tested_platform =
  let val ml_platform = getenv "ML_PLATFORM"
  in String.isSuffix "linux" ml_platform orelse String.isSuffix "darwin" ml_platform end;

fun max_threads_value () =
  let val m = ! max_threads in
    if m > 0 then m
    else if not tested_platform then 1
    else Int.min (Int.max (Thread.numProcessors (), 1), 4)
  end;

fun enabled () = max_threads_value () > 1;


(* misc utils *)

fun show "" = "" | show name = " " ^ name;
fun show' "" = "" | show' name = " [" ^ name ^ "]";

fun read_file name =
  let val is = TextIO.openIn name
  in Exn.release (Exn.capture TextIO.inputAll is before TextIO.closeIn is) end;

fun write_file name txt =
  let val os = TextIO.openOut name
  in Exn.release (Exn.capture TextIO.output (os, txt) before TextIO.closeOut os) end;


(* thread attributes *)

val no_interrupts =
  [Thread.EnableBroadcastInterrupt false, Thread.InterruptState Thread.InterruptDefer];

val public_interrupts =
  [Thread.EnableBroadcastInterrupt true, Thread.InterruptState Thread.InterruptAsynchOnce];

val private_interrupts =
  [Thread.EnableBroadcastInterrupt false, Thread.InterruptState Thread.InterruptAsynchOnce];

val sync_interrupts = map
  (fn x as Thread.InterruptState Thread.InterruptDefer => x
    | Thread.InterruptState _ => Thread.InterruptState Thread.InterruptSynch
    | x => x);

val safe_interrupts = map
  (fn Thread.InterruptState Thread.InterruptAsynch =>
      Thread.InterruptState Thread.InterruptAsynchOnce
    | x => x);

fun with_attributes new_atts e =
  let
    val orig_atts = safe_interrupts (Thread.getAttributes ());
    val result = Exn.capture (fn () =>
      (Thread.setAttributes (safe_interrupts new_atts); e orig_atts)) ();
    val _ = Thread.setAttributes orig_atts;
  in Exn.release result end;


(* portable wrappers *)

fun interruptible f x = with_attributes public_interrupts (fn _ => f x);

fun uninterruptible f x =
  with_attributes no_interrupts (fn atts =>
    f (fn g => fn y => with_attributes atts (fn _ => g y)) x);


(* synchronous wait *)

fun sync_wait opt_atts time cond lock =
  with_attributes
    (sync_interrupts (case opt_atts of SOME atts => atts | NONE => Thread.getAttributes ()))
    (fn _ =>
      (case time of
        SOME t => Exn.Result (ConditionVar.waitUntil (cond, lock, t))
      | NONE => (ConditionVar.wait (cond, lock); Exn.Result true))
      handle exn => Exn.Exn exn);


(* tracing *)

val trace = Unsynchronized.ref 0;

fun tracing level msg =
  if level > ! trace then ()
  else uninterruptible (fn _ => fn () =>
    (TextIO.output (TextIO.stdErr, (">>> " ^ msg () ^ "\n")); TextIO.flushOut TextIO.stdErr)
      handle _ (*sic*) => ()) ();

fun tracing_time detailed time =
  tracing
   (if not detailed then 5
    else if Time.>= (time, Time.fromMilliseconds 1000) then 1
    else if Time.>= (time, Time.fromMilliseconds 100) then 2
    else if Time.>= (time, Time.fromMilliseconds 10) then 3
    else if Time.>= (time, Time.fromMilliseconds 1) then 4 else 5);

fun real_time f x =
  let
    val timer = Timer.startRealTimer ();
    val () = f x;
    val time = Timer.checkRealTimer timer;
  in time end;


(* execution with time limit *)

structure TimeLimit =
struct

exception TimeOut;

fun timeLimit time f x = uninterruptible (fn restore_attributes => fn () =>
  let
    val worker = Thread.self ();
    val timeout = Unsynchronized.ref false;
    val watchdog = Thread.fork (fn () =>
      (OS.Process.sleep time; timeout := true; Thread.interrupt worker), []);

    val result = Exn.capture (restore_attributes f) x;
    val was_timeout = (case result of Exn.Exn Exn.Interrupt => ! timeout | _ => false);

    val _ = Thread.interrupt watchdog handle Thread _ => ();
  in if was_timeout then raise TimeOut else Exn.release result end) ();

end;


(* system shell processes, with propagation of interrupts *)

fun system_out script = with_attributes no_interrupts (fn orig_atts =>
  let
    val script_name = OS.FileSys.tmpName ();
    val _ = write_file script_name script;

    val pid_name = OS.FileSys.tmpName ();
    val output_name = OS.FileSys.tmpName ();

    (*result state*)
    datatype result = Wait | Signal | Result of int;
    val result = Unsynchronized.ref Wait;
    val lock = Mutex.mutex ();
    val cond = ConditionVar.conditionVar ();
    fun set_result res =
      (Mutex.lock lock; result := res; ConditionVar.signal cond; Mutex.unlock lock);

    val _ = Mutex.lock lock;

    (*system thread*)
    val system_thread = Thread.fork (fn () =>
      let
        val status =
          OS.Process.system ("perl -w \"$ISABELLE_HOME/lib/scripts/system.pl\" group " ^
            script_name ^ " " ^ pid_name ^ " " ^ output_name);
        val res =
          (case Posix.Process.fromStatus status of
            Posix.Process.W_EXITED => Result 0
          | Posix.Process.W_EXITSTATUS 0wx82 => Signal
          | Posix.Process.W_EXITSTATUS w => Result (Word8.toInt w)
          | Posix.Process.W_SIGNALED s =>
              if s = Posix.Signal.int then Signal
              else Result (256 + LargeWord.toInt (Posix.Signal.toWord s))
          | Posix.Process.W_STOPPED s => Result (512 + LargeWord.toInt (Posix.Signal.toWord s)));
      in set_result res end handle _ (*sic*) => set_result (Result 2), []);

    (*main thread -- proxy for interrupts*)
    fun kill n =
      (case Int.fromString (read_file pid_name) of
        SOME pid =>
          Posix.Process.kill
            (Posix.Process.K_GROUP (Posix.Process.wordToPid (LargeWord.fromInt pid)),
              Posix.Signal.int)
      | NONE => ())
      handle OS.SysErr _ => () | IO.Io _ =>
        (OS.Process.sleep (Time.fromMilliseconds 100); if n > 0 then kill (n - 1) else ());

    val _ =
      while ! result = Wait do
        let val res =
          sync_wait (SOME orig_atts)
            (SOME (Time.+ (Time.now (), Time.fromMilliseconds 100))) cond lock
        in case res of Exn.Exn Exn.Interrupt => kill 10 | _ => () end;

    (*cleanup*)
    val output = read_file output_name handle IO.Io _ => "";
    val _ = OS.FileSys.remove script_name handle OS.SysErr _ => ();
    val _ = OS.FileSys.remove pid_name handle OS.SysErr _ => ();
    val _ = OS.FileSys.remove output_name handle OS.SysErr _ => ();
    val _ = Thread.interrupt system_thread handle Thread _ => ();
    val rc = (case ! result of Signal => raise Exn.Interrupt | Result rc => rc);
  in (output, rc) end);


(* critical section -- may be nested within the same thread *)

local

val critical_lock = Mutex.mutex ();
val critical_thread = Unsynchronized.ref (NONE: Thread.thread option);
val critical_name = Unsynchronized.ref "";

in

fun self_critical () =
  (case ! critical_thread of
    NONE => false
  | SOME t => Thread.equal (t, Thread.self ()));

fun NAMED_CRITICAL name e =
  if self_critical () then e ()
  else
    Exn.release (uninterruptible (fn restore_attributes => fn () =>
      let
        val name' = ! critical_name;
        val _ =
          if Mutex.trylock critical_lock then ()
          else
            let
              val _ = tracing 5 (fn () => "CRITICAL" ^ show name ^ show' name' ^ ": waiting");
              val time = real_time Mutex.lock critical_lock;
              val _ = tracing_time true time (fn () =>
                "CRITICAL" ^ show name ^ show' name' ^ ": passed after " ^ Time.toString time);
            in () end;
        val _ = critical_thread := SOME (Thread.self ());
        val _ = critical_name := name;
        val result = Exn.capture (restore_attributes e) ();
        val _ = critical_name := "";
        val _ = critical_thread := NONE;
        val _ = Mutex.unlock critical_lock;
      in result end) ());

fun CRITICAL e = NAMED_CRITICAL "" e;

end;


(* serial numbers *)

local

val serial_lock = Mutex.mutex ();
val serial_count = Unsynchronized.ref 0;

in

val serial = uninterruptible (fn _ => fn () =>
  let
    val _ = Mutex.lock serial_lock;
    val _ = serial_count := ! serial_count + 1;
    val res = ! serial_count;
    val _ = Mutex.unlock serial_lock;
  in res end);

end;

end;

structure Basic_Multithreading: BASIC_MULTITHREADING = Multithreading;
open Basic_Multithreading;
