(*  Title:      Pure/PIDE/protocol.ML
    Author:     Makarius

Protocol message formats for interactive proof documents.
*)

structure Protocol: sig end =
struct

val _ =
  Isabelle_Process.add_command "Document.define_command"
    (fn [id, name, text] =>
      Document.change_state (Document.define_command (Document.parse_id id) name text));

val _ =
  Isabelle_Process.add_command "Document.cancel_execution"
    (fn [] => ignore (Document.cancel_execution (Document.state ())));

val _ =
  Isabelle_Process.add_command "Document.update_perspective"
    (fn [old_id_string, new_id_string, name, ids_yxml] => Document.change_state (fn state =>
      let
        val old_id = Document.parse_id old_id_string;
        val new_id = Document.parse_id new_id_string;
        val ids = YXML.parse_body ids_yxml
          |> let open XML.Decode in list int end;

        val _ = Future.join_tasks (Document.cancel_execution state);
      in
        state
        |> Document.update_perspective old_id new_id name ids
        |> Document.execute new_id
      end));

val _ =
  Isabelle_Process.add_command "Document.update"
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
                      (Exn.Res
                        (triple (pair string string) (list string) (list (pair string bool)) a)),
                  fn ([a], []) => Document.Header (Exn.Exn (ERROR a)),
                  fn (a, []) => Document.Perspective (map int_atom a)]))
            end;

        val running = Document.cancel_execution state;
        val (assignment, state1) = Document.update old_id new_id edits state;
        val _ = Future.join_tasks running;
        val _ =
          Output.raw_message Isabelle_Markup.assign_execs
            ((new_id, assignment) |>
              let open XML.Encode
              in pair int (pair (list (pair int (option int))) (list (pair string (option int)))) end
              |> YXML.string_of_body);
        val state2 = Document.execute new_id state1;
      in state2 end));

val _ =
  Isabelle_Process.add_command "Document.remove_versions"
    (fn [versions_yxml] => Document.change_state (fn state =>
      let
        val versions =
          YXML.parse_body versions_yxml |>
            let open XML.Decode in list int end;
        val state1 = Document.remove_versions versions state;
        val _ = Output.raw_message Isabelle_Markup.removed_versions versions_yxml;
      in state1 end));

val _ =
  Isabelle_Process.add_command "Document.invoke_scala"
    (fn [id, tag, res] => Invoke_Scala.fulfill_method id tag res);

end;

