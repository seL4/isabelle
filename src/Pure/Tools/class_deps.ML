(*  Title:      Pure/Tools/class_deps.ML
    Author:     Florian Haftmann, TU Muenchen

Visualization of class dependencies.
*)

signature CLASS_DEPS =
sig
  val class_deps: Proof.context -> sort list option -> sort list option -> unit
  val class_deps_cmd: Proof.context -> string list option -> string list option -> unit
end;

structure Class_Deps: CLASS_DEPS =
struct

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
    fun node c =
      Graph_Display.content_node (Name_Space.extern ctxt space c)
        (Class.pretty_specification thy c);
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
  Outer_Syntax.command @{command_keyword class_deps} "visualize class dependencies"
    ((Scan.option parse_sort_list -- Scan.option parse_sort_list) >> (fn (super, sub) =>
      (Toplevel.unknown_theory o
       Toplevel.keep (fn st => class_deps_cmd (Toplevel.context_of st) super sub))));

end;
