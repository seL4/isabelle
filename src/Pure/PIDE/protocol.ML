(*  Title:      Pure/PIDE/protocol.ML
    Author:     Makarius

Protocol message formats for interactive proof documents.
*)

structure Protocol: sig end =
struct

val _ =
  Protocol_Command.define "Prover.echo"
    (fn args => List.app writeln args);

val _ =
  Protocol_Command.define "Prover.stop"
    (fn rc :: msgs =>
      (List.app Output.system_message msgs;
       raise Protocol_Command.STOP (Value.parse_int rc)));

val _ =
  Protocol_Command.define_bytes "Prover.options"
    (fn [options_yxml] =>
      (Options.set_default (Options.decode (YXML.parse_body_bytes options_yxml));
       Isabelle_Process.init_options_interactive ()));

val _ =
  Protocol_Command.define_bytes "Prover.init_session"
    (fn [yxml] => Resources.init_session_yxml yxml);

val _ =
  Protocol_Command.define "Document.define_blob"
    (fn [digest, content] => Document.change_state (Document.define_blob digest content));

fun decode_command id name parents_xml blobs_xml toks_xml sources : Document.command =
  let
    open XML.Decode;
    val parents = list string parents_xml;
    val (blobs_digests, blobs_index) =
      blobs_xml |>
        let
          val message = YXML.string_of_body o Protocol_Message.command_positions id;
          val blob =
            triple string string (option string)
            #> (fn (a, b, c) => {file_node = a, src_path = Path.explode b, digest = c});
        in
          pair
            (list (variant
             [fn ([], a) => Exn.Res (blob a),
              fn ([], a) => Exn.Exn (ERROR (message a))]))
            int
        end;
    val toks = list (pair int int) toks_xml;
  in
   {command_id = Document_ID.parse id,
    name = name,
    parents = parents,
    blobs_digests = blobs_digests,
    blobs_index = blobs_index,
    tokens = toks ~~ sources}
  end;

fun commands_accepted ids =
  Output.protocol_message Markup.commands_accepted [[XML.Text (space_implode "," ids)]];

val _ =
  Protocol_Command.define "Document.define_command"
    (fn id :: name :: parents :: blobs :: toks :: sources =>
      let
        val command =
          decode_command id name (YXML.parse_body parents) (YXML.parse_body blobs)
            (YXML.parse_body toks) sources;
        val _ = Document.change_state (Document.define_command command);
      in commands_accepted [id] end);

val _ =
  Protocol_Command.define "Document.define_commands"
    (fn args =>
      let
        fun decode arg =
          let
            open XML.Decode;
            val (id, (name, (parents_xml, (blobs_xml, (toks_xml, sources))))) =
              pair string (pair string (pair I (pair I (pair I (list string)))))
                (YXML.parse_body arg);
          in decode_command id name parents_xml blobs_xml toks_xml sources end;

        val commands = map decode args;
        val _ = Document.change_state (fold Document.define_command commands);
      in commands_accepted (map (Value.print_int o #command_id) commands) end);

val _ =
  Protocol_Command.define "Document.discontinue_execution"
    (fn [] => Execution.discontinue ());

val _ =
  Protocol_Command.define "Document.cancel_exec"
    (fn [exec_id] => Execution.cancel (Document_ID.parse exec_id));

val _ =
  Protocol_Command.define_bytes "Document.update"
    (Future.task_context "Document.update" (Future.new_group NONE)
      (fn old_id_bytes :: new_id_bytes :: consolidate_yxml :: edits_yxml =>
        Document.change_state (fn state =>
          let
            val old_id = Document_ID.parse (Bytes.content old_id_bytes);
            val new_id = Document_ID.parse (Bytes.content new_id_bytes);
            val consolidate =
              YXML.parse_body_bytes consolidate_yxml |>
                let open XML.Decode in list string end;
            val edits =
              edits_yxml |> map (YXML.parse_body_bytes #>
                let open XML.Decode in
                  pair string
                    (variant
                     [fn ([], a) => Document.Edits (list (pair (option int) (option int)) a),
                      fn ([], a) =>
                        let
                          val (master, (name, (imports, (keywords, errors)))) =
                            pair string (pair string (pair (list string)
                              (pair (list (pair string (pair string (list string))))
                                (list YXML.string_of_body)))) a;
                          val imports' = map (rpair Position.none) imports;
                          val keywords' =
                            map (fn (x, y) => ((x, Position.none), Keyword.command_spec y)) keywords;
                          val header = Thy_Header.make (name, Position.none) imports' keywords';
                        in Document.Deps {master = master, header = header, errors = errors} end,
                      fn (a :: b, c) =>
                        Document.Perspective (bool_atom a, map int_atom b,
                          list (pair int (pair string (list string))) c)])
                end);

            val _ = Execution.discontinue ();

            val (edited, removed, assign_update, state') =
              Document.update old_id new_id edits consolidate state;
            val _ =
              (singleton o Future.forks)
               {name = "Document.update/remove", group = NONE,
                deps = Execution.snapshot removed,
                pri = Task_Queue.urgent_pri + 2, interrupts = false}
               (fn () => (Execution.purge removed; List.app Isabelle_Process.reset_tracing removed));

            val _ =
              Output.protocol_message Markup.assign_update
                [(new_id, edited, assign_update) |>
                  let
                    open XML.Encode;
                    fun encode_upd (a, bs) =
                      string (space_implode "," (map Value.print_int (a :: bs)));
                  in triple int (list string) (list encode_upd) end];
          in Document.start_execution state' end)));

val _ =
  Protocol_Command.define_bytes "Document.remove_versions"
    (fn [versions_yxml] => Document.change_state (fn state =>
      let
        val versions =
          YXML.parse_body_bytes versions_yxml |>
            let open XML.Decode in list int end;
        val state1 = Document.remove_versions versions state;
        val _ = Output.protocol_message Markup.removed_versions [Bytes.contents_blob versions_yxml];
      in state1 end));

val _ =
  Protocol_Command.define "Document.dialog_result"
    (fn [serial, result] =>
      (case Exn.capture_body (fn () => Active.dialog_result (Value.parse_int serial) result) of
        Exn.Res () => ()
      | Exn.Exn exn => if Exn.is_interrupt exn then () (*sic!*) else Exn.reraise exn));

val _ =
  Protocol_Command.define "ML_Heap.full_gc"
    (fn [] => ML_Heap.full_gc ());

val _ =
  Protocol_Command.define "ML_Heap.share_common_data"
    (fn [] => ML_Heap.share_common_data ());

end;
