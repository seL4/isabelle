(*  Title:      Pure/Tools/class_deps.ML
    Author:     Florian Haftmann, TU Muenchen

Visualization of class dependencies.
*)

signature CLASS_DEPS =
sig
  val visualize: Proof.context -> sort -> sort option -> unit
  val visualize_cmd: Proof.context -> string -> string option -> unit
end;

structure Class_deps: CLASS_DEPS =
struct

fun gen_visualize prep_sort ctxt raw_super raw_sub =
  let
    val super = prep_sort ctxt raw_super;
    val sub = Option.map (prep_sort ctxt) raw_sub;
    val {classes = (space, original_algebra), ...} = Type.rep_tsig (Proof_Context.tsig_of ctxt);
    fun le_super class = Sorts.sort_le original_algebra ([class], super);
    val sub_le = case sub of
      NONE => K true |
      SOME sub => fn class => Sorts.sort_le original_algebra (sub, [class]);
    val (_, algebra) = Sorts.subalgebra (Context.pretty ctxt)
      (le_super andf sub_le) (K NONE) original_algebra;
    val classes = Sorts.classes_of algebra;
    fun entry (c, (i, (_, cs))) =
      (i, {name = Name_Space.extern ctxt space c, ID = c, parents = Graph.Keys.dest cs,
            dir = "", unfold = true, path = "", content = []});
    val gr =
      Graph.fold (cons o entry) classes []
      |> sort (int_ord o apply2 #1) |> map #2;
  in Graph_Display.display_graph gr end;

val visualize = gen_visualize (Type.cert_sort o Proof_Context.tsig_of);
val visualize_cmd = gen_visualize Syntax.read_sort;

val _ =
  Outer_Syntax.command @{command_spec "class_deps"} "visualize class dependencies"
    ((Scan.optional Parse.sort "{}" -- Scan.option Parse.sort) >> (fn (raw_super, raw_sub) =>
      ((Toplevel.unknown_theory oo Toplevel.keep) (fn st => visualize_cmd (Toplevel.context_of st) raw_super raw_sub))));

end;
