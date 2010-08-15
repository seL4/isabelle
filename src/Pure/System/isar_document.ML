(*  Title:      Pure/System/isar_document.ML
    Author:     Makarius

Protocol commands for interactive Isar documents.
*)

structure Isar_Document: sig end =
struct

val global_state = Synchronized.var "Isar_Document" Document.init_state;
val change_state = Synchronized.change global_state;

val _ =
  Isabelle_Process.add_command "Isar_Document.define_command"
    (fn [id, text] => change_state (Document.define_command (Document.parse_id id) text));

val _ =
  Isabelle_Process.add_command "Isar_Document.edit_version"
    (fn [old_id_string, new_id_string, edits_yxml] => change_state (fn state =>
      let
        val old_id = Document.parse_id old_id_string;
        val new_id = Document.parse_id new_id_string;
        val edits =
          XML_Data.dest_list (XML_Data.dest_pair XML_Data.dest_string
            (XML_Data.dest_option (XML_Data.dest_list
                (XML_Data.dest_pair XML_Data.dest_int
                  (XML_Data.dest_option XML_Data.dest_int))))) (YXML.parse_body edits_yxml);

      val (updates, state') = Document.edit old_id new_id edits state;
      val _ =
        implode (map (fn (id, exec_id) => Markup.markup (Markup.edit id exec_id) "") updates)
        |> Markup.markup (Markup.assign new_id)
        |> Output.status;
      val state'' = Document.execute new_id state';
    in state'' end));

end;

