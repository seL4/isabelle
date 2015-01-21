(*  Title:      Pure/Tools/class_deps.ML
    Author:     Florian Haftmann, TU Muenchen

Visualization of class dependencies.
*)

signature CLASS_DEPS =
sig
  val inlined_class_specs: bool Config.T
  val class_deps: Proof.context -> sort -> sort option -> unit
  val class_deps_cmd: Proof.context -> string -> string option -> unit
end;

structure Class_Deps: CLASS_DEPS =
struct

val inlined_class_specs = Attrib.setup_config_bool @{binding "inlined_class_specs"} (K false);

val stringify = XML.content_of o YXML.parse_body o Pretty.string_of;

fun gen_class_deps prep_sort ctxt raw_super raw_sub =
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
    val inlined = Config.get ctxt inlined_class_specs;
    fun label_for c =
      if inlined
      then (stringify o Pretty.block o op @) (Class.pretty_specification thy c)
      else Name_Space.extern ctxt space c;
    fun tooltip_for c =
      if inlined
      then []
      else
        let
          val pretty_spec = Class.pretty_specification thy c
        in
          if (null o snd) pretty_spec
          then []
          else [(Pretty.block o op @) pretty_spec]
        end;
    fun node c = Graph_Display.content_node (label_for c) (tooltip_for c);
  in
    Sorts.classes_of algebra
    |> Graph.dest
    |> map (fn ((c, _), ds) => ((c, node c), ds))
    |> Graph_Display.display_graph
  end;

val class_deps = gen_class_deps (Type.cert_sort o Proof_Context.tsig_of);
val class_deps_cmd = gen_class_deps Syntax.read_sort;

val _ =
  Outer_Syntax.command @{command_spec "class_deps"} "visualize class dependencies"
    ((Scan.optional Parse.sort "{}" -- Scan.option Parse.sort) >> (fn (super, sub) =>
      (Toplevel.unknown_theory o
       Toplevel.keep (fn st => class_deps_cmd (Toplevel.context_of st) super sub))));

end;
