(*  Title:      Pure/Tools/thy_deps.ML
    Author:     Makarius

Visualization of theory dependencies.
*)

signature THY_DEPS =
sig
  val thy_deps: theory -> theory list option * theory list option -> Graph_Display.entry list
  val thy_deps_cmd: theory -> string list option * string list option -> unit
end;

structure Thy_Deps: THY_DEPS =
struct

fun gen_thy_deps _ thy0 (NONE, NONE) =
      let
        val parent_session = Session.get_name ();
        val parent_loaded = is_some o Thy_Info.lookup_theory;
      in Present.session_graph parent_session parent_loaded thy0 end
  | gen_thy_deps prep_thy thy0 bounds =
      let
        val (upper, lower) = apply2 ((Option.map o map) (prep_thy thy0)) bounds;
        val rel = Theory.subthy o swap;
        val pred =
          (case upper of
            SOME Bs => (fn thy => exists (fn B => rel (thy, B)) Bs)
          | NONE => K true) andf
          (case lower of
            SOME Bs => (fn thy => exists (fn B => rel (B, thy)) Bs)
          | NONE => K true);
        fun node thy =
          ((Context.theory_name thy, Graph_Display.content_node (Context.theory_name thy) []),
            map Context.theory_name (filter pred (Theory.parents_of thy)));
      in Theory.nodes_of thy0 |> filter pred |> map node end;

val thy_deps = gen_thy_deps (K I);
val thy_deps_cmd = Graph_Display.display_graph oo gen_thy_deps Context.get_theory;

val theory_bounds =
  Parse.theory_xname >> single ||
  (@{keyword "("} |-- Parse.enum "|" Parse.theory_xname --| @{keyword ")"});

val _ =
  Outer_Syntax.command @{command_keyword thy_deps} "visualize theory dependencies"
    (Scan.option theory_bounds -- Scan.option theory_bounds >>
      (fn args => Toplevel.keep (fn st => thy_deps_cmd (Toplevel.theory_of st) args)));

end;
