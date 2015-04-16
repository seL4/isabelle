(*  Title:      Pure/Tools/class_deps.ML
    Author:     Florian Haftmann, TU Muenchen

Visualization of class dependencies.
*)

signature CLASS_DEPS =
sig
  val class_deps: Proof.context -> sort list option * sort list option -> unit
  val class_deps_cmd: Proof.context -> string list option * string list option -> unit
end;

structure Class_Deps: CLASS_DEPS =
struct

fun gen_class_deps prep_sort ctxt raw_bounds =
  let
    val (upper, lower) = apply2 ((Option.map o map) (prep_sort ctxt)) raw_bounds;
    val {classes = (space, algebra), ...} = Type.rep_tsig (Proof_Context.tsig_of ctxt);
    val sort_le = curry (Sorts.sort_le algebra);
    val restrict =
      (case upper of
        SOME bs => (fn c => exists (fn b => sort_le [c] b) bs)
      | NONE => K true) andf
      (case lower of
        SOME bs => (fn c => exists (fn b => sort_le b [c]) bs)
      | NONE => K true);
    fun node c =
      Graph_Display.content_node (Name_Space.extern ctxt space c)
        (Class.pretty_specification (Proof_Context.theory_of ctxt) c);
  in
    Sorts.subalgebra (Context.pretty ctxt) restrict (K NONE) algebra
    |> #2 |> Sorts.classes_of |> Graph.dest
    |> map (fn ((c, _), ds) => ((c, node c), ds))
    |> Graph_Display.display_graph
  end;

val class_deps = gen_class_deps (Type.cert_sort o Proof_Context.tsig_of);
val class_deps_cmd = gen_class_deps Syntax.read_sort;

val parse_sort_list =
  Parse.sort >> single ||
  (@{keyword "("} |-- Parse.enum "|" Parse.sort --| @{keyword ")"});

val _ =
  Outer_Syntax.command @{command_keyword class_deps} "visualize class dependencies"
    ((Scan.option parse_sort_list -- Scan.option parse_sort_list) >> (fn bounds =>
      (Toplevel.unknown_theory o
       Toplevel.keep (fn st => class_deps_cmd (Toplevel.context_of st) bounds))));

end;
