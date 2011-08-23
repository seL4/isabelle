(*  Title:      Pure/PIDE/isar_document.ML
    Author:     Makarius

Protocol message formats for interactive Isar documents.
*)

structure Isar_Document: sig end =
struct

val _ =
  Isabelle_Process.add_command "Isar_Document.define_command"
    (fn [id, text] => Document.change_state (Document.define_command (Document.parse_id id) text));

val _ =
  Isabelle_Process.add_command "Isar_Document.edit_version"
    (fn [old_id_string, new_id_string, edits_yxml] => Document.change_state (fn state =>
      let
        val old_id = Document.parse_id old_id_string;
        val new_id = Document.parse_id new_id_string;
        val edits =
          YXML.parse_body edits_yxml |>
            let open XML.Decode in
              list (pair string
                (variant
                 [fn ([], []) => Document.Clear,
                  fn ([], a) => Document.Edits (list (pair (option int) (option int)) a),
                  fn ([], a) =>
                    Document.Header
                      (Exn.Res (triple string (list string) (list (pair string bool)) a)),
                  fn ([a], []) => Document.Header (Exn.Exn (ERROR a)),
                  fn (a, []) => Document.Perspective (map int_atom a)]))
            end;

      val running = Document.cancel_execution state;
      val (updates, state') = Document.edit old_id new_id edits state;
      val _ = Future.join_tasks running;
      val _ = Document.join_commands state';
      val _ =
        Output.status (Markup.markup (Markup.assign new_id)
          (implode (map (Markup.markup_only o Markup.edit) updates)));
      val state'' = Document.execute new_id state';
    in state'' end));

val _ =
  Isabelle_Process.add_command "Isar_Document.invoke_scala"
    (fn [id, tag, res] => Invoke_Scala.fulfill_method id tag res);

end;

