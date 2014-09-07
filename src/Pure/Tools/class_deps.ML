(*  Title:      Pure/Tools/class_deps.ML
    Author:     Florian Haftmann, TU Muenchen

Visualization of class dependencies.
*)

signature CLASS_DEPS =
sig
  val class_deps: Toplevel.transition -> Toplevel.transition
end;

structure Class_deps: CLASS_DEPS =
struct

val class_deps = Toplevel.unknown_theory o Toplevel.keep (fn state =>
  let
    val ctxt = Toplevel.context_of state;
    val {classes = (space, algebra), ...} = Type.rep_tsig (Proof_Context.tsig_of ctxt);
    val classes = Sorts.classes_of algebra;
    fun entry (c, (i, (_, cs))) =
      (i, {name = Name_Space.extern ctxt space c, ID = c, parents = Graph.Keys.dest cs,
            dir = "", unfold = true, path = "", content = []});
    val gr =
      Graph.fold (cons o entry) classes []
      |> sort (int_ord o pairself #1) |> map #2;
  in Graph_Display.display_graph gr end);

val _ =
  Outer_Syntax.improper_command @{command_spec "class_deps"} "visualize class dependencies"
    (Scan.succeed class_deps);

end;
