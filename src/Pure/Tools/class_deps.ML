(*  Title:      Pure/Tools/class_deps.ML
    Author:     Florian Haftmann, TU Muenchen

Visualization of class dependencies.
*)

signature CLASS_DEPS =
sig
  val class_deps: Proof.context -> sort -> sort option -> unit
  val class_deps_cmd: Proof.context -> string -> string option -> unit
end;

structure Class_Deps: CLASS_DEPS =
struct

fun gen_visualize prep_sort ctxt raw_super raw_sub =
  let
    val thy = Proof_Context.theory_of ctxt;
    val super = prep_sort ctxt raw_super;
    val sub = Option.map (prep_sort ctxt) raw_sub;
    val {classes = (space, original_algebra), ...} = Type.rep_tsig (Proof_Context.tsig_of ctxt);
    fun le_super class = Sorts.sort_le original_algebra ([class], super);
    val sub_le =
      (case sub of
        NONE => K true
      | SOME sub => fn class => Sorts.sort_le original_algebra (sub, [class]));
    val (_, algebra) =
      Sorts.subalgebra (Context.pretty ctxt)
        (le_super andf sub_le) (K NONE) original_algebra;
    fun pretty_body_of c = if Class.is_class thy c then Class.pretty_body thy c else [];
  in
    Sorts.classes_of algebra
    |> Graph.dest
    |> map (fn ((c, _), ds) =>
        ((c, Graph_Display.content_node (Name_Space.extern ctxt space c) (pretty_body_of c)), ds))
    |> Graph_Display.display_graph
  end;

val class_deps = gen_visualize (Type.cert_sort o Proof_Context.tsig_of);
val class_deps_cmd = gen_visualize Syntax.read_sort;

val _ =
  Outer_Syntax.command @{command_spec "class_deps"} "visualize class dependencies"
    ((Scan.optional Parse.sort "{}" -- Scan.option Parse.sort) >> (fn (super, sub) =>
      (Toplevel.unknown_theory o
       Toplevel.keep (fn st => class_deps_cmd (Toplevel.context_of st) super sub))));

end;
