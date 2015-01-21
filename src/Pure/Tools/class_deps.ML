(*  Title:      Pure/Tools/class_deps.ML
    Author:     Florian Haftmann, TU Muenchen

Visualization of class dependencies.
*)

signature CLASS_DEPS =
sig
  val inlined_class_specs: bool Config.T
  val class_deps: Proof.context -> sort list option -> sort list option -> unit
  val class_deps_cmd: Proof.context -> string list option -> string list option -> unit
end;

structure Class_Deps: CLASS_DEPS =
struct

val inlined_class_specs = Attrib.setup_config_bool @{binding "inlined_class_specs"} (K false);

val stringify = XML.content_of o YXML.parse_body o Pretty.string_of;

fun gen_class_deps prep_sort ctxt raw_subs raw_supers =
  let
    val thy = Proof_Context.theory_of ctxt;
    val some_subs = (Option.map o map) (prep_sort ctxt) raw_subs;
    val some_supers = (Option.map o map) (prep_sort ctxt) raw_supers;
    val {classes = (space, original_algebra), ...} = Type.rep_tsig (Proof_Context.tsig_of ctxt);
    val sort_le = curry (Sorts.sort_le original_algebra);
    val le_sub = case some_subs of
      SOME subs => (fn class => exists (sort_le [class]) subs)
    | NONE => K true;
    val super_le = case some_supers of
      SOME supers => (fn class => exists (fn super => sort_le super [class]) supers)
    | NONE => K true
    val (_, algebra) =
      Sorts.subalgebra (Context.pretty ctxt)
        (le_sub andf super_le) (K NONE) original_algebra;
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

val parse_sort_list = (Parse.sort >> single)
  || (@{keyword "("} |-- Parse.enum "|" Parse.sort --| @{keyword ")"});

val _ =
  Outer_Syntax.command @{command_spec "class_deps"} "visualize class dependencies"
    ((Scan.option parse_sort_list -- Scan.option parse_sort_list) >> (fn (super, sub) =>
      (Toplevel.unknown_theory o
       Toplevel.keep (fn st => class_deps_cmd (Toplevel.context_of st) super sub))));

end;
