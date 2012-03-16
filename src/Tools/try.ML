(*  Title:      Tools/try.ML
    Author:     Jasmin Blanchette, TU Muenchen

Manager for tools that should be tried on conjectures.
*)

signature TRY =
sig
  type tool =
    string * (int * bool Unsynchronized.ref
              * (bool -> Proof.state -> bool * (string * Proof.state)))

  val tryN : string
  val auto_time_limit: real Unsynchronized.ref

  val serial_commas : string -> string list -> string list
  val subgoal_count : Proof.state -> int
  val register_tool : tool -> theory -> theory
  val get_tools : theory -> tool list
  val try_tools : Proof.state -> (string * string) option
end;

structure Try : TRY =
struct

type tool =
  string * (int * bool Unsynchronized.ref
            * (bool -> Proof.state -> bool * (string * Proof.state)))

val tryN = "try"


(* preferences *)

val auto_time_limit = Unsynchronized.ref 4.0

val auto_try_time_limitN = "auto-try-time-limit"
val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
    (Preferences.real_pref auto_time_limit
      auto_try_time_limitN "Time limit for automatically tried tools (in seconds).")


(* helpers *)

fun serial_commas _ [] = ["??"]
  | serial_commas _ [s] = [s]
  | serial_commas conj [s1, s2] = [s1, conj, s2]
  | serial_commas conj [s1, s2, s3] = [s1 ^ ",", s2 ^ ",", conj, s3]
  | serial_commas conj (s :: ss) = s ^ "," :: serial_commas conj ss

val subgoal_count = Logic.count_prems o prop_of o #goal o Proof.goal


(* configuration *)

fun tool_ord ((name1, (weight1, _, _)), (name2, (weight2, _, _))) =
  prod_ord int_ord string_ord ((weight1, name1), (weight2, name2))

structure Data = Theory_Data
(
  type T = tool list
  val empty = []
  val extend = I
  fun merge data : T = Ord_List.merge tool_ord data
)

val get_tools = Data.get

val register_tool = Data.map o Ord_List.insert tool_ord

(* try command *)

fun try_tools state =
  if subgoal_count state = 0 then
    (Output.urgent_message "No subgoal!"; NONE)
  else
    get_tools (Proof.theory_of state)
    |> tap (fn tools =>
               "Trying " ^ space_implode " "
                    (serial_commas "and" (map (quote o fst) tools)) ^ "..."
               |> Output.urgent_message)
    |> Par_List.get_some
           (fn (name, (_, _, tool)) =>
               case try (tool false) state of
                 SOME (true, (outcome_code, _)) => SOME (name, outcome_code)
               | _ => NONE)
    |> tap (fn NONE => Output.urgent_message "Tried in vain." | _ => ())

val _ =
  Outer_Syntax.improper_command @{command_spec "try"}
    "try a combination of automatic proving and disproving tools"
    (Scan.succeed (Toplevel.keep (ignore o try_tools o Toplevel.proof_of)))


(* automatic try *)

fun auto_try state =
  get_tools (Proof.theory_of state)
  |> map_filter (fn (_, (_, auto, tool)) => if !auto then SOME tool else NONE)
  |> Par_List.get_some (fn tool =>
                           case try (tool true) state of
                             SOME (true, (_, state)) => SOME state
                           | _ => NONE)
  |> the_default state

(* Too large values are understood as milliseconds, ensuring compatibility with
   old setting files. No users can possibly in their right mind want the user
   interface to block for more than 100 seconds. *)
fun smart_seconds r =
  seconds (if r >= 100.0 then
             (legacy_feature (quote auto_try_time_limitN ^
                " expressed in milliseconds -- use seconds instead"); 0.001 * r)
           else
             r)

val _ = Context.>> (Specification.add_theorem_hook (fn interact => fn state =>
  if interact andalso not (!Toplevel.quiet) andalso !auto_time_limit > 0.0 then
    TimeLimit.timeLimit (smart_seconds (!auto_time_limit)) auto_try state
    handle TimeLimit.TimeOut => state
  else
    state))

end;
