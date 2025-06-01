(*  Title:      Pure/Build/build.ML
    Author:     Makarius

Build Isabelle sessions.
*)

signature BUILD =
sig
  type hook = string -> (theory * Document_Output.segment list) list -> unit
  val add_hook: hook -> unit
end;

structure Build: BUILD =
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

type hook = string -> (theory * Document_Output.segment list) list -> unit;

local
  val hooks = Synchronized.var "Build.hooks" ([]: hook list);
in

fun add_hook hook = Synchronized.change hooks (cons hook);

fun apply_hooks qualifier loaded_theories =
  Synchronized.value hooks
  |> List.app (fn hook => hook qualifier loaded_theories);

end;


fun build_theories qualifier (options, thys) =
  let
    val _ = ML_Profiling.check_mode (Options.string options "profiling");
    val condition = space_explode "," (Options.string options "condition");
    val conds = filter_out (can getenv_strict) condition;
    val loaded_theories =
      if null conds then
        (Options.set_default options;
          Isabelle_Process.init_options ();
          Future.fork I;
          (Thy_Info.use_theories options qualifier
          |> Unsynchronized.setmp print_mode
              (space_explode "," (Options.string options "print_mode") @ print_mode_value ())) thys)
      else
       (Output.physical_stderr ("Skipping theories " ^ commas_quote (map #1 thys) ^
          " (undefined " ^ commas conds ^ ")\n"); [])
  in loaded_theories end;


(* build session *)

val _ =
  Protocol_Command.define_bytes "build_session"
    (fn [resources_yxml, args_yxml] =>
        let
          val _ = Resources.init_session_yxml resources_yxml;
          val (session_name, theories) =
            YXML.parse_body_bytes args_yxml |>
              let
                open XML.Decode;
                val position = Position.of_properties o properties;
              in pair string (list (pair Options.decode (list (pair string position)))) end;

          val _ = Session.init session_name;

          fun build () =
            let
              val res =
                theories |>
                  (maps (build_theories session_name)
                    |> session_timing
                    |> Exn.capture);
              val res1 =
                (case res of
                  Exn.Res loaded_theories =>
                    Exn.capture (apply_hooks session_name) loaded_theories
                | Exn.Exn exn => Exn.Exn exn);
              val res2 = Exn.capture_body Session.finish;

              val _ = Resources.finish_session_base ();
              val _ = Par_Exn.release_all [res1, res2];
              val _ =
                if session_name = Context.PureN
                then Theory.install_pure (Thy_Info.get_theory Context.PureN) else ();
            in () end;

          fun exec e =
            if can Theory.get_pure () then
              Isabelle_Thread.fork (Isabelle_Thread.params "build_session") e
              |> ignore
            else e ();
        in
          exec (fn () =>
            (case Exn.capture_body (Future.interruptible_task build) of
              Exn.Res () => (0, [])
            | Exn.Exn exn =>
                (case Exn.capture Runtime.exn_message_list exn of
                  Exn.Res errs => (1, errs)
                | Exn.Exn _ (*sic!*) => (2, ["CRASHED"])))
          |> let open XML.Encode in pair int (list string) end
          |> single
          |> Output.protocol_message Markup.build_session_finished)
        end
      | _ => raise Match);

end;
