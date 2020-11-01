(*  Title:      Pure/Isar/experiment.ML
    Author:     Makarius

Target for specification experiments that are mostly private.
*)

signature EXPERIMENT =
sig
  val is_experiment: theory -> string -> bool
  val experiment: Element.context_i list -> theory -> Binding.scope * local_theory
  val experiment_cmd: Element.context list -> theory -> Binding.scope * local_theory
end;

structure Experiment: EXPERIMENT =
struct

structure Data = Theory_Data
(
  type T = Symtab.set;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (K true);
);

fun is_experiment thy name = Symtab.defined (Data.get thy) name;

fun gen_experiment add_locale elems thy =
  let
    val experiment_name = Binding.name ("experiment" ^ serial_string ()) |> Binding.concealed;
    val lthy =
      thy
      |> add_locale experiment_name Binding.empty [] ([], []) elems
      |-> (Local_Theory.background_theory o Data.map o Symtab.insert_set);
    val (scope, naming) =
      Name_Space.new_scope (Proof_Context.naming_of (Local_Theory.target_of lthy));
    val naming' = naming |> Name_Space.private_scope scope;
    val lthy' = lthy
      |> Local_Theory.map_contexts (K (Proof_Context.map_naming (K naming')))
      |> Local_Theory.map_background_naming Name_Space.concealed;
  in (scope, lthy') end;

val experiment = gen_experiment Expression.add_locale;
val experiment_cmd = gen_experiment Expression.add_locale_cmd;

end;
