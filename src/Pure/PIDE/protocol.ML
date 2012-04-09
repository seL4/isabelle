(*  Title:      Pure/PIDE/protocol.ML
    Author:     Makarius

Protocol message formats for interactive proof documents.
*)

structure Protocol: sig end =
struct

val _ =
  Isabelle_Process.protocol_command "Document.define_command"
    (fn [id, name, text] =>
      Document.change_state (Document.define_command (Document.parse_id id) name text));

val _ =
  Isabelle_Process.protocol_command "Document.discontinue_execution"
    (fn [] => Document.discontinue_execution (Document.state ()));

val _ =
  Isabelle_Process.protocol_command "Document.cancel_execution"
    (fn [] => Document.cancel_execution (Document.state ()));

val _ =
  Isabelle_Process.protocol_command "Document.update"
    (fn [old_id_string, new_id_string, edits_yxml] => Document.change_state (fn state =>
      let
        val _ = Document.cancel_execution state;

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
                    let
                      val ((((master, name), imports), keywords), uses) =
                        pair (pair (pair (pair string string) (list string))
                          (list (pair string (option (pair string (list string))))))
                          (list (pair string bool)) a;
                      val res =
                        Exn.capture (fn () =>
                          (master, Thy_Header.make name imports keywords
                            (map (apfst Path.explode) uses))) ();
                    in Document.Header res end,
                  fn ([a], []) => Document.Header (Exn.Exn (ERROR a)),
                  fn (a, []) => Document.Perspective (map int_atom a)]))
            end;

        val (assignment, state1) = Document.update old_id new_id edits state;
        val _ =
          Output.protocol_message Isabelle_Markup.assign_execs
            ((new_id, assignment) |>
              let open XML.Encode
              in pair int (list (pair int (option int))) end
              |> YXML.string_of_body);
        val state2 = Document.execute new_id state1;
      in state2 end));

val _ =
  Isabelle_Process.protocol_command "Document.remove_versions"
    (fn [versions_yxml] => Document.change_state (fn state =>
      let
        val versions =
          YXML.parse_body versions_yxml |>
            let open XML.Decode in list int end;
        val state1 = Document.remove_versions versions state;
        val _ = Output.protocol_message Isabelle_Markup.removed_versions versions_yxml;
      in state1 end));

val _ =
  Isabelle_Process.protocol_command "Document.invoke_scala"
    (fn [id, tag, res] => Invoke_Scala.fulfill_method id tag res);

end;

