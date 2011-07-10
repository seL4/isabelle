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
    (fn [old_id_string, new_id_string, edits_yxml, headers_yxml] => Document.change_state (fn state =>
      let
        val old_id = Document.parse_id old_id_string;
        val new_id = Document.parse_id new_id_string;
        val edits = YXML.parse_body edits_yxml |>
          let open XML_Data.Dest
          in list (pair string (option (list (pair (option int) (option int))))) end;
        val headers = YXML.parse_body headers_yxml |>
          let open XML_Data.Dest
          in list (pair string (triple string (list string) (list string))) end;

      val await_cancellation = Document.cancel_execution state;
      val (updates, state') = Document.edit old_id new_id edits headers state;
      val _ = await_cancellation ();
      val _ =
        Output.status (Markup.markup (Markup.assign new_id)
          (implode (map (Markup.markup_only o Markup.edit) updates)));
      val state'' = Document.execute new_id state';
    in state'' end));

end;

