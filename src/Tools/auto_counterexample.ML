(*  Title:      Tools/auto_counterexample.ML
    Author:     Jasmin Blanchette, TU Muenchen

Counterexample Search Unit (do not abbreviate!).
*)

signature AUTO_COUNTEREXAMPLE =
sig
  val time_limit: int Unsynchronized.ref

  val register_tool :
    string * (Proof.state -> bool * Proof.state) -> theory -> theory
end;

structure Auto_Counterexample : AUTO_COUNTEREXAMPLE =
struct

(* preferences *)

val time_limit = Unsynchronized.ref 2500

val _ =
  ProofGeneralPgip.add_preference Preferences.category_tracing
    (Preferences.nat_pref time_limit
      "auto-counterexample-time-limit"
      "Time limit for automatic counterexample search (in milliseconds).")


(* configuration *)

structure Data = TheoryDataFun(
  type T = (string * (Proof.state -> bool * Proof.state)) list
  val empty = []
  val copy = I
  val extend = I
  fun merge _ (tools1, tools2) = AList.merge (op =) (K true) (tools1, tools2)
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
    handle TimeLimit.TimeOut =>
           (warning "Automatic counterexample search timed out."; state)))

end;
