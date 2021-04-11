(*  Title:      Pure/Tools/build.ML
    Author:     Makarius

Build Isabelle sessions.
*)

structure Build: sig end =
struct

(* session timing *)

fun session_timing f x =
  let
    val start = Timing.start ();
    val y = f x;
    val timing = Timing.result start;

    val threads = string_of_int (Multithreading.max_threads ());
    val props = [("threads", threads)] @ Markup.timing_properties timing;
    val _ = Output.protocol_message (Markup.session_timing :: props) [];
  in y end;


(* build theories *)

fun build_theories qualifier (options, thys) =
  let
    val condition = space_explode "," (Options.string options "condition");
    val conds = filter_out (can getenv_strict) condition;
  in
    if null conds then
      (Options.set_default options;
        Isabelle_Process.init_options ();
        Future.fork I;
        (Thy_Info.use_theories options qualifier
        |>
          (case Options.string options "profiling" of
            "" => I
          | "time" => profile_time
          | "allocations" => profile_allocations
          | bad => error ("Bad profiling option: " ^ quote bad))
        |> Unsynchronized.setmp print_mode
            (space_explode "," (Options.string options "print_mode") @ print_mode_value ())) thys)
    else
      Output.physical_stderr ("Skipping theories " ^ commas_quote (map #1 thys) ^
        " (undefined " ^ commas conds ^ ")\n")
  end;


(* build session *)

val _ =
  Protocol_Command.define "build_session"
    (fn [resources_yxml, args_yxml] =>
        let
          val _ = Resources.init_session_yxml resources_yxml;
          val (session_name, theories) =
            YXML.parse_body args_yxml |>
              let
                open XML.Decode;
                val position = Position.of_properties o properties;
              in pair string (list (pair Options.decode (list (pair string position)))) end;

          val _ = Session.init session_name;

          fun build () =
            let
              val res1 =
                theories |>
                  (List.app (build_theories session_name)
                    |> session_timing
                    |> Exn.capture);
              val res2 = Exn.capture Session.finish ();

              val _ = Resources.finish_session_base ();
              val _ = Par_Exn.release_all [res1, res2];
              val _ =
                if session_name = Context.PureN
                then Theory.install_pure (Thy_Info.get_theory Context.PureN) else ();
            in () end;

          fun exec e =
            if can Theory.get_pure () then
              Isabelle_Thread.fork
                {name = "build_session", stack_limit = Isabelle_Thread.stack_limit (),
                  interrupts = false} e
              |> ignore
            else e ();
        in
          exec (fn () =>
            (Future.interruptible_task (fn () => (build (); (0, []))) () handle exn =>
              ((1, Runtime.exn_message_list exn) handle _ (*sic!*) => (2, ["CRASHED"])))
          |> let open XML.Encode in pair int (list string) end
          |> single
          |> Output.protocol_message Markup.build_session_finished)
        end
      | _ => raise Match);

end;
