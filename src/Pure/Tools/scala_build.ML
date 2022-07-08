(*  Title:      Pure/Tools/scala_build.ML
    Author:     Makarius

Build and export Isabelle/Scala/Java modules.
*)

signature SCALA_BUILD =
sig
  val scala_build_component: Proof.context -> Input.source -> unit
  val scala_build_directory: Proof.context -> Input.source -> unit
end

structure Scala_Build: SCALA_BUILD =
struct

fun scala_build component ctxt dir =
  let
    val path = Resources.check_dir ctxt NONE dir;
    val [jar_name, jar_bytes, output] =
      \<^scala>\<open>scala_build\<close>
        [Bytes.string (Value.print_bool component), Bytes.string (Path.implode path)];
    val _ = writeln (Bytes.content output);
  in
    Export.export (Proof_Context.theory_of ctxt)
      (Path.explode_binding0 (Bytes.content jar_name))
      (Bytes.contents_blob jar_bytes)
  end;

val scala_build_component = scala_build true;
val scala_build_directory = scala_build false;

end;
