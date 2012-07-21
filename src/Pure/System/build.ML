(*  Title:      Pure/System/build.ML
    Author:     Makarius

Build Isabelle sessions.
*)

signature BUILD =
sig
  val build: string -> unit
end;

structure Build: BUILD =
struct

fun build args_file =
  let
    val (build_images, (parent, (name, theories))) =
      File.read (Path.explode args_file) |> YXML.parse_body |>
        let open XML.Decode in pair bool (pair string (pair string (list string))) end;

    val _ = Session.init false parent name;  (* FIXME reset!? *)
    val _ = Thy_Info.use_thys theories;
    val _ = Session.finish ();

    val _ = if build_images then () else quit ();
  in () end
  handle exn => (Output.error_msg (ML_Compiler.exn_message exn); exit 1);

end;
