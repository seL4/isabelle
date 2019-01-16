(*  Title:      Pure/Thy/sessions.ML
    Author:     Makarius

Support for session ROOT syntax.
*)

signature SESSIONS =
sig
  val root_name: string
  val theory_name: string
  val command_parser: (Toplevel.transition -> Toplevel.transition) parser
end;

structure Sessions: SESSIONS =
struct

val root_name = "ROOT";
val theory_name = "Pure.Sessions";

local

val global =
  Parse.$$$ "(" -- Parse.!!! (Parse.$$$ "global" -- Parse.$$$ ")") >> K true || Scan.succeed false;

val theory_entry = Parse.theory_name --| global;

val theories =
  Parse.$$$ "theories" |-- Parse.!!! (Scan.optional Parse.options [] -- Scan.repeat1 theory_entry);

val in_path =
  Parse.$$$ "(" |-- Parse.!!! (Parse.$$$ "in" |-- Parse.position Parse.path --| Parse.$$$ ")");

val document_files =
  Parse.$$$ "document_files" |--
    Parse.!!! (Scan.optional in_path ("document", Position.none)
      -- Scan.repeat1 (Parse.position Parse.path));

val prune =
  Scan.optional (Parse.$$$ "[" |-- Parse.!!! (Parse.nat --| Parse.$$$ "]")) 0;

val export_files =
  Parse.$$$ "export_files" |--
    Parse.!!!
      (Scan.optional in_path ("export", Position.none) -- prune -- Scan.repeat1 Parse.embedded);

in

val command_parser =
  Parse.session_name --
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.name --| Parse.$$$ ")")) [] --
  Scan.optional (Parse.$$$ "in" |-- Parse.!!! (Parse.position Parse.path)) (".", Position.none) --
  (Parse.$$$ "=" |--
    Parse.!!! (Scan.option (Parse.session_name --| Parse.!!! (Parse.$$$ "+")) --
      Scan.optional (Parse.$$$ "description" |-- Parse.!!! (Parse.input Parse.text)) Input.empty --
      Scan.optional (Parse.$$$ "options" |-- Parse.!!! Parse.options) [] --
      Scan.optional (Parse.$$$ "sessions" |--
        Parse.!!! (Scan.repeat1 Parse.session_name)) [] --
      Scan.repeat theories --
      Scan.repeat document_files --
      Scan.repeat export_files))
  >> (fn ((((session, _), _), dir),
          (((((((parent, descr), options), sessions), theories), document_files), export_files))) =>
    Toplevel.keep (fn state =>
      let
        val ctxt = Toplevel.context_of state;
        val thy = Toplevel.theory_of state;
        val session_dir = Resources.check_dir ctxt (Resources.master_directory thy) dir;

        val _ =
          (the_list parent @ sessions) |> List.app (fn arg =>
            ignore (Resources.check_session ctxt arg)
              handle ERROR msg => Output.error_message msg);

        val _ =
          Context_Position.report ctxt
            (Position.range_position (Symbol_Pos.range (Input.source_explode descr)))
            Markup.comment;

        val _ =
          (options @ maps #1 theories) |> List.app (fn (x, y) =>
            ignore (Completion.check_option_value ctxt x y (Options.default ()))
              handle ERROR msg => Output.error_message msg);

        val _ =
          maps #2 theories |> List.app (fn (s, pos) =>
            let
              val {node_name, theory_name, ...} =
                Resources.import_name session session_dir s
                  handle ERROR msg => error (msg ^ Position.here pos);
              val theory_path = the_default node_name (Resources.known_theory theory_name);
              val _ = Resources.check_file ctxt Path.current (Path.implode theory_path, pos);
            in () end);

        val _ =
          document_files |> List.app (fn (doc_dir, doc_files) =>
            let
              val dir = Resources.check_dir ctxt session_dir doc_dir;
              val _ = List.app (ignore o Resources.check_file ctxt dir) doc_files;
            in () end);

        val _ =
          export_files |> List.app (fn ((export_dir, _), _) =>
            ignore (Resources.check_path ctxt session_dir export_dir));
      in () end));

end;

end;
