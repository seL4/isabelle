(*  Title:      Pure/Isar/experiment.ML
    Author:     Makarius

Target for specification experiments that are mostly private.
*)

signature EXPERIMENT =
sig
  val experiment: Element.context_i list -> theory -> Binding.scope * local_theory
  val experiment_cmd: Element.context list -> theory -> Binding.scope * local_theory
end;

structure Experiment: EXPERIMENT =
struct

fun gen_experiment add_locale elems thy =
  let
    val (_, lthy) = thy
      |> add_locale (Binding.name ("experiment" ^ serial_string ())) Binding.empty ([], []) elems;
    val (scope, naming) =
      Name_Space.new_scope (Proof_Context.naming_of (Local_Theory.target_of lthy));
    val naming' = naming |> Name_Space.private scope;
    val lthy' = lthy |> Local_Theory.map_contexts (K (Proof_Context.map_naming (K naming')));
  in (scope, lthy') end;

val experiment = gen_experiment Expression.add_locale;
val experiment_cmd = gen_experiment Expression.add_locale_cmd;

end;
