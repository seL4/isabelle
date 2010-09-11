(*  Title:      Tools/auto_tools.ML
    Author:     Jasmin Blanchette, TU Muenchen

Manager for tools that should be run automatically on newly entered conjectures.
*)

signature AUTO_TOOLS =
sig
  val time_limit: int Unsynchronized.ref

  val register_tool :
    string * (Proof.state -> bool * Proof.state) -> theory -> theory
end;

structure Auto_Tools : AUTO_TOOLS =
struct

(* preferences *)

val time_limit = Unsynchronized.ref 2500

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
    (Preferences.nat_pref time_limit
      "auto-tools-time-limit"
      "Time limit for automatic tools (in milliseconds).")


(* configuration *)

structure Data = Theory_Data
(
  type T = (string * (Proof.state -> bool * Proof.state)) list
  val empty = []
  val extend = I
  fun merge data : T = AList.merge (op =) (K true) data
)

val register_tool = Data.map o AList.update (op =)


(* automatic testing *)

val _ = Context.>> (Specification.add_theorem_hook (fn interact => fn state =>
  case !time_limit of
    0 => state
  | ms =>
    TimeLimit.timeLimit (Time.fromMilliseconds ms)
        (fn () =>
            if interact andalso not (!Toplevel.quiet) then
              fold_rev (fn (_, tool) => fn (true, state) => (true, state)
                                         | (false, state) => tool state)
                   (Data.get (Proof.theory_of state)) (false, state) |> snd
            else
              state) ()
    handle TimeLimit.TimeOut => state))

end;
