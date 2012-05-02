(*  Title:      HOL/Mirabelle/Tools/mirabelle.ML
    Author:     Jasmin Blanchette and Sascha Boehme, TU Munich
*)

signature MIRABELLE =
sig
  (*configuration*)
  val logfile : string Config.T
  val timeout : int Config.T
  val start_line : int Config.T
  val end_line : int Config.T

  (*core*)
  type init_action = int -> theory -> theory
  type done_args = {last: Toplevel.state, log: string -> unit}
  type done_action = int -> done_args -> unit
  type run_args = {pre: Proof.state, post: Toplevel.state option,
    timeout: Time.time, log: string -> unit, pos: Position.T, name: string}
  type run_action = int -> run_args -> unit
  type action = init_action * run_action * done_action
  val catch : (int -> string) -> run_action -> run_action
  val catch_result : (int -> string) -> 'a -> (int -> run_args -> 'a) ->
    int -> run_args -> 'a
  val register : action -> theory -> theory
  val step_hook : Toplevel.transition -> Toplevel.state -> Toplevel.state ->
    unit

  (*utility functions*)
  val can_apply : Time.time -> (Proof.context -> int -> tactic) ->
    Proof.state -> bool
  val theorems_in_proof_term : thm -> thm list
  val theorems_of_sucessful_proof : Toplevel.state option -> thm list
  val get_setting : (string * string) list -> string * string -> string
  val get_int_setting : (string * string) list -> string * int -> int
  val cpu_time : ('a -> 'b) -> 'a -> 'b * int
end



structure Mirabelle : MIRABELLE =
struct

(* Mirabelle configuration *)

val logfile = Attrib.setup_config_string @{binding mirabelle_logfile} (K "")
val timeout = Attrib.setup_config_int @{binding mirabelle_timeout} (K 30)
val start_line = Attrib.setup_config_int @{binding mirabelle_start_line} (K 0)
val end_line = Attrib.setup_config_int @{binding mirabelle_end_line} (K ~1)


(* Mirabelle core *)

type init_action = int -> theory -> theory
type done_args = {last: Toplevel.state, log: string -> unit}
type done_action = int -> done_args -> unit
type run_args = {pre: Proof.state, post: Toplevel.state option,
  timeout: Time.time, log: string -> unit, pos: Position.T, name: string}
type run_action = int -> run_args -> unit
type action = init_action * run_action * done_action

structure Actions = Theory_Data
(
  type T = (int * run_action * done_action) list
  val empty = []
  val extend = I
  fun merge data = Library.merge (K true) data  (* FIXME potential data loss because of (K true) *)
)


fun log_exn log tag id e = log (tag id ^ "exception:\n" ^ General.exnMessage e)

fun catch tag f id (st as {log, ...}: run_args) = (f id st; ())
  handle exn =>
    if Exn.is_interrupt exn then reraise exn else (log_exn log tag id exn; ())

fun catch_result tag d f id (st as {log, ...}: run_args) = f id st
  handle exn =>
    if Exn.is_interrupt exn then reraise exn else (log_exn log tag id exn; d)

fun register (init, run, done) thy =
  let val id = length (Actions.get thy) + 1
  in
    thy
    |> init id
    |> Actions.map (cons (id, run, done))
  end

local

fun log thy s =
  let fun append_to n = if n = "" then K () else File.append (Path.explode n)
  in append_to (Config.get_global thy logfile) (s ^ "\n") end
  (* FIXME: with multithreading and parallel proofs enabled, we might need to
     encapsulate this inside a critical section *)

fun log_sep thy = log thy "------------------"

fun apply_actions thy pos name info (pre, post, time) actions =
  let
    fun apply f = f {pre=pre, post=post, timeout=time, log=log thy, pos=pos, name=name}
    fun run (id, run, _) = (apply (run id); log_sep thy)
  in (log thy info; log_sep thy; List.app run actions) end

fun in_range _ _ NONE = true
  | in_range l r (SOME i) = (l <= i andalso (r < 0 orelse i <= r))

fun only_within_range thy pos f x =
  let val l = Config.get_global thy start_line and r = Config.get_global thy end_line
  in if in_range l r (Position.line_of pos) then f x else () end

in

fun run_actions tr pre post =
  let
    val thy = Proof.theory_of pre
    val pos = Toplevel.pos_of tr
    val name = Toplevel.name_of tr
    val st = (pre, post, Time.fromSeconds (Config.get_global thy timeout))

    val str0 = string_of_int o the_default 0
    val loc = str0 (Position.line_of pos) ^ ":" ^ str0 (Position.offset_of pos)
    val info = "\n\nat " ^ loc ^ " (" ^ name ^ "):"
  in
    only_within_range thy pos (apply_actions thy pos name info st) (Actions.get thy)
  end

fun done_actions st =
  let
    val thy = Toplevel.theory_of st
    val _ = log thy "\n\n";
  in
    thy
    |> Actions.get
    |> List.app (fn (id, _, done) => done id {last=st, log=log thy})
  end

end

val whitelist = ["apply", "by", "proof"]

fun step_hook tr pre post =
 (* FIXME: might require wrapping into "interruptible" *)
  if can (Proof.assert_backward o Toplevel.proof_of) pre andalso
     member (op =) whitelist (Toplevel.name_of tr)
  then run_actions tr (Toplevel.proof_of pre) (SOME post)
  else if not (Toplevel.is_toplevel pre) andalso Toplevel.is_toplevel post
  then done_actions pre
  else ()   (* FIXME: add theory_hook here *)



(* Mirabelle utility functions *)

fun can_apply time tac st =
  let
    val {context = ctxt, facts, goal} = Proof.goal st
    val full_tac = HEADGOAL (Method.insert_tac facts THEN' tac ctxt)
  in
    (case try (TimeLimit.timeLimit time (Seq.pull o full_tac)) goal of
      SOME (SOME _) => true
    | _ => false)
  end

local

fun fold_body_thms f =
  let
    fun app n (PBody {thms, ...}) = thms |> fold (fn (i, (name, prop, body)) =>
      fn (x, seen) =>
        if Inttab.defined seen i then (x, seen)
        else
          let
            val body' = Future.join body
            val (x', seen') = app (n + (if name = "" then 0 else 1)) body'
              (x, Inttab.update (i, ()) seen)
        in (x' |> n = 0 ? f (name, prop, body'), seen') end)
  in fn bodies => fn x => #1 (fold (app 0) bodies (x, Inttab.empty)) end

in

fun theorems_in_proof_term thm =
  let
    val all_thms = Global_Theory.all_thms_of (Thm.theory_of_thm thm)
    fun collect (s, _, _) = if s <> "" then insert (op =) s else I
    fun member_of xs (x, y) = if member (op =) xs x then SOME y else NONE
    fun resolve_thms names = map_filter (member_of names) all_thms
  in
    resolve_thms (fold_body_thms collect [Thm.proof_body_of thm] [])
  end

end

fun theorems_of_sucessful_proof state =
  (case state of
    NONE => []
  | SOME st =>
      if not (Toplevel.is_proof st) then []
      else theorems_in_proof_term (#goal (Proof.goal (Toplevel.proof_of st))))

fun get_setting settings (key, default) =
  the_default default (AList.lookup (op =) settings key)

fun get_int_setting settings (key, default) =
  (case Option.map Int.fromString (AList.lookup (op =) settings key) of
    SOME (SOME i) => i
  | SOME NONE => error ("bad option: " ^ key)
  | NONE => default)

fun cpu_time f x =
  let val ({cpu, ...}, y) = Timing.timing f x
  in (y, Time.toMilliseconds cpu) end

end
