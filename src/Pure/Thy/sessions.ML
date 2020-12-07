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

val theory_entry = Parse.input Parse.theory_name --| Parse.opt_keyword "global";

val theories =
  Parse.$$$ "theories" |-- Parse.!!! (Scan.optional Parse.options [] -- Scan.repeat1 theory_entry);

val in_path =
  Parse.$$$ "(" |-- Parse.!!! (Parse.$$$ "in" |-- Parse.path_input --| Parse.$$$ ")");

val document_theories =
  Parse.$$$ "document_theories" |-- Scan.repeat1 (Parse.input Parse.theory_name);

val document_files =
  Parse.$$$ "document_files" |--
    Parse.!!! (Scan.optional in_path (Input.string "document") -- Scan.repeat1 Parse.path_input);

val prune =
  Scan.optional (Parse.$$$ "[" |-- Parse.!!! (Parse.nat --| Parse.$$$ "]")) 0;

val export_files =
  Parse.$$$ "export_files" |--
    Parse.!!! (Scan.optional in_path (Input.string "export") -- prune -- Scan.repeat1 Parse.embedded);

fun path_source source path =
  Input.source (Input.is_delimited source) (Path.implode path) (Input.range_of source);

in

val command_parser =
  Parse.session_name --
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.name --| Parse.$$$ ")")) [] --
  Scan.optional (Parse.$$$ "in" |-- Parse.!!! Parse.path_input) (Input.string ".") --
  (Parse.$$$ "=" |--
    Parse.!!! (Scan.option (Parse.session_name --| Parse.!!! (Parse.$$$ "+")) --
      Scan.optional (Parse.$$$ "description" |-- Parse.!!! (Parse.input Parse.text)) Input.empty --
      Scan.optional (Parse.$$$ "options" |-- Parse.!!! Parse.options) [] --
      Scan.optional (Parse.$$$ "sessions" |--
        Parse.!!! (Scan.repeat1 Parse.session_name)) [] --
      Scan.optional (Parse.$$$ "directories" |-- Parse.!!! (Scan.repeat1 Parse.path_input)) [] --
      Scan.repeat theories --
      Scan.optional document_theories [] --
      Scan.repeat document_files --
      Scan.repeat export_files))
  >> (fn (((((session, _), _), dir),
          (((((((((parent, descr), options), sessions), directories), theories),
            document_theories), document_files), export_files)))) =>
    Toplevel.keep (fn state =>
      let
        val ctxt = Toplevel.context_of state;
        val session_dir = Resources.check_dir ctxt NONE dir;

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

        fun check_thy source =
          ignore (Resources.check_file ctxt (SOME Path.current) source)
            handle ERROR msg => Output.error_message msg;

        val _ =
          maps #2 theories |> List.app (fn source =>
            let
              val s = Input.string_of source;
              val pos = Input.pos_of source;
              val {node_name, theory_name, ...} =
                Resources.import_name session session_dir s
                  handle ERROR msg => error (msg ^ Position.here pos);
              val thy_path = the_default node_name (Resources.find_theory_file theory_name);
            in check_thy (path_source source thy_path) end);

        val _ =
          directories |> List.app (ignore o Resources.check_dir ctxt (SOME session_dir));

        val _ =
          document_theories |> List.app (fn source =>
            let
              val thy = Input.string_of source;
              val pos = Input.pos_of source;
            in
              (case Resources.find_theory_file thy of
                NONE => Output.error_message ("Unknown theory " ^ quote thy ^ Position.here pos)
              | SOME path => check_thy (path_source source path))
            end);

        val _ =
          document_files |> List.app (fn (doc_dir, doc_files) =>
            let
              val dir = Resources.check_dir ctxt (SOME session_dir) doc_dir;
              val _ = List.app (ignore o Resources.check_file ctxt (SOME dir)) doc_files;
            in () end);

        val _ =
          export_files |> List.app (fn ((export_dir, _), _) =>
            ignore (Resources.check_path ctxt (SOME session_dir) export_dir));
      in () end));

end;

end;
