(*  Title:      Pure/Tools/scala_build.ML
    Author:     Makarius

Build and export Isabelle/Scala/Java modules.
*)

signature SCALA_BUILD =
sig
  val scala_build: Proof.context -> Path.T -> unit
end

structure Scala_Build: SCALA_BUILD =
struct

fun scala_build ctxt dir =
  let
    val [jar_name, jar_bytes, output] =
      \<^scala>\<open>scala_build\<close> [Bytes.string (Isabelle_System.absolute_path dir)];
    val _ = writeln (Bytes.content output);
  in
    Export.export (Proof_Context.theory_of ctxt)
      (Path.explode_binding0 (Bytes.content jar_name))
      (Bytes.contents_blob jar_bytes)
  end;

end;
