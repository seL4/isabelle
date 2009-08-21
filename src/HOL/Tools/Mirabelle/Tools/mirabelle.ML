(* Title:  mirabelle.ML
   Author: Jasmin Blanchette and Sascha Boehme
*)

signature MIRABELLE =
sig
  type action
  val register : string * action -> theory -> theory

  val timeout : int Config.T
  val verbose : bool Config.T
  val start_line : int Config.T
  val end_line : int Config.T
  val set_logfile : string -> theory -> theory

  val goal_thm_of : Proof.state -> thm
  val can_apply : (Proof.context -> int -> tactic) -> Proof.state -> bool
  val theorems_in_proof_term : Thm.thm -> Thm.thm list
  val theorems_of_sucessful_proof : Toplevel.state option -> Thm.thm list
  val get_setting : (string * string) list -> string * string -> string
  val get_int_setting : (string * string) list -> string * int -> int
end



signature MIRABELLE_EXT =
sig
  include MIRABELLE
  val setup : theory -> theory
  val step_hook : Toplevel.transition -> Toplevel.state -> Toplevel.state ->
    unit
end



structure Mirabelle : MIRABELLE_EXT =
struct

(* Mirabelle core *)

type action = {pre: Proof.state, post: Toplevel.state option} -> string option

structure Actions = TheoryDataFun
(
  type T = action Symtab.table
  val empty = Symtab.empty
  val copy = I
  val extend = I
  fun merge _ = Symtab.merge (K true)
)

val register = Actions.map o Symtab.update_new

val (logfile, setup1) = Attrib.config_string "mirabelle_logfile" ""
val (timeout, setup2) = Attrib.config_int "mirabelle_timeout" 30
val (verbose, setup3) = Attrib.config_bool "mirabelle_verbose" true
val (start_line, setup4) = Attrib.config_int "mirabelle_start_line" 0
val (end_line, setup5) = Attrib.config_int "mirabelle_end_line" ~1

val setup = setup1 #> setup2 #> setup3 #> setup4 #> setup5

fun set_logfile name =
  let val _ = File.write (Path.explode name) ""   (* erase file content *)
  in Config.put_thy logfile name end

local

fun log thy s =
  let fun append_to n = if n = "" then K () else File.append (Path.explode n)
  in append_to (Config.get_thy thy logfile) (s ^ "\n") end
  (* FIXME: with multithreading and parallel proofs enabled, we might need to
     encapsulate this inside a critical section *)

fun verbose_msg verbose msg = if verbose then SOME msg else NONE

fun with_time_limit (verb, secs) f x = TimeLimit.timeLimit secs f x
  handle TimeLimit.TimeOut => verbose_msg verb "time out"
       | ERROR msg => verbose_msg verb ("error: " ^ msg)

fun capture_exns verb f x =
  (case try f x of NONE => verbose_msg verb "exception" | SOME msg => msg)

fun apply_action (c as (verb, _)) st (name, action) =
  Option.map (pair name) (capture_exns verb (with_time_limit c action) st)

fun in_range _ _ NONE = true
  | in_range l r (SOME i) = (l <= i andalso (r < 0 orelse i <= r))

fun only_within_range thy pos f x =
  let val l = Config.get_thy thy start_line and r = Config.get_thy thy end_line
  in if in_range l r (Position.line_of pos) then f x else [] end

fun pretty_print verbose pos name msgs =
  let
    val file = the_default "unknown file" (Position.file_of pos)

    val str0 = string_of_int o the_default 0
    val loc = str0 (Position.line_of pos) ^ ":" ^ str0 (Position.column_of pos)

    val full_loc = if verbose then file ^ ":" ^ loc else "at " ^ loc
    val head = full_loc ^ " (" ^ name ^ "):"

    fun pretty_msg (name, msg) = Pretty.block (map Pretty.str [name, ": ", msg])
  in
    Pretty.string_of (Pretty.big_list head (map pretty_msg msgs))
  end

in

fun basic_hook tr pre post =
  let
    val thy = Proof.theory_of pre
    val pos = Toplevel.pos_of tr
    val name = Toplevel.name_of tr
    val verb = Config.get_thy thy verbose
    val secs = Time.fromSeconds (Config.get_thy thy timeout)
    val st = {pre=pre, post=post}
  in
    Actions.get thy
    |> Symtab.dest
    |> only_within_range thy pos (map_filter (apply_action (verb, secs) st))
    |> (fn [] => () | msgs => log thy (pretty_print verb pos name msgs))
  end

end

fun step_hook tr pre post =
 (* FIXME: might require wrapping into "interruptible" *)
  if can (Proof.assert_backward o Toplevel.proof_of) pre andalso
     not (member (op =) ["disable_pr", "enable_pr"] (Toplevel.name_of tr))
  then basic_hook tr (Toplevel.proof_of pre) (SOME post)
  else ()   (* FIXME: add theory_hook here *)



(* Mirabelle utility functions *)

val goal_thm_of = snd o snd o Proof.get_goal

fun can_apply tac st =
  let val (ctxt, (facts, goal)) = Proof.get_goal st
  in
    (case Seq.pull (HEADGOAL (Method.insert_tac facts THEN' tac ctxt) goal) of
      SOME (thm, _) => true
    | NONE => false)
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
    val all_thms = PureThy.all_thms_of (Thm.theory_of_thm thm)
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
      else theorems_in_proof_term (goal_thm_of (Toplevel.proof_of st)))

fun get_setting settings (key, default) =
  the_default default (AList.lookup (op =) settings key)

fun get_int_setting settings (key, default) =
  (case Option.map Int.fromString (AList.lookup (op =) settings key) of
    SOME (SOME i) => i
  | SOME NONE => error ("bad option: " ^ key)
  | NONE => default)

end
