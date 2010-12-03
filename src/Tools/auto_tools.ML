(*  Title:      Tools/auto_tools.ML
    Author:     Jasmin Blanchette, TU Muenchen

Manager for tools that should be run automatically on newly entered conjectures.
*)

signature AUTO_TOOLS =
sig
  val time_limit: real Unsynchronized.ref

  val register_tool :
    bool Unsynchronized.ref * (Proof.state -> bool * Proof.state) -> theory
    -> theory
end;

structure Auto_Tools : AUTO_TOOLS =
struct

(* preferences *)

val time_limit = Unsynchronized.ref 4.0

val auto_tools_time_limitN = "auto-tools-time-limit"
val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
    (Preferences.real_pref time_limit
      auto_tools_time_limitN "Time limit for automatic tools (in seconds).")


(* configuration *)

structure Data = Theory_Data
(
  type T = (bool Unsynchronized.ref * (Proof.state -> bool * Proof.state)) list
  val empty = []
  val extend = I
  fun merge data : T = AList.merge (op =) (K true) data
)

val register_tool = Data.map o AList.update (op =)


(* automatic testing *)

fun run_tools tools state =
  tools |> map_filter (fn (auto, tool) => if !auto then SOME tool else NONE)
        |> Par_List.get_some (fn tool =>
                                 case try tool state of
                                   SOME (true, state) => SOME state
                                 | _ => NONE)
        |> the_default state

(* Too large values are understood as milliseconds, ensuring compatibility with
   old setting files. No users can possibly in their right mind want the user
   interface to block for more than 100 seconds. *)
fun smart_seconds r =
  seconds (if r >= 100.0 then
             (legacy_feature (quote auto_tools_time_limitN ^
                " expressed in milliseconds -- use seconds instead"); 0.001 * r)
           else
             r)

val _ = Context.>> (Specification.add_theorem_hook (fn interact => fn state =>
  if interact andalso not (!Toplevel.quiet) andalso !time_limit > 0.0 then
    TimeLimit.timeLimit (smart_seconds (!time_limit))
        (run_tools (Data.get (Proof.theory_of state))) state
    handle TimeLimit.TimeOut => state
  else
    state))

end;
