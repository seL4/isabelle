(*  Title:      Pure/Tools/build.ML
    Author:     Makarius

Build Isabelle sessions.
*)

structure Build: sig end =
struct

(* command timings *)

type timings = ((string * Time.time) Inttab.table) Symtab.table;  (*file -> offset -> name, time*)

val empty_timings: timings = Symtab.empty;

fun update_timings props =
  (case Markup.parse_command_timing_properties props of
    SOME ({file, offset, name}, time) =>
      Symtab.map_default (file, Inttab.empty)
        (Inttab.map_default (offset, (name, time)) (fn (_, t) => (name, t + time)))
  | NONE => I);

fun approximative_id name pos =
  (case (Position.file_of pos, Position.offset_of pos) of
    (SOME file, SOME offset) =>
      if name = "" then NONE else SOME {file = file, offset = offset, name = name}
  | _ => NONE);

fun get_timings timings tr =
  (case approximative_id (Toplevel.name_of tr) (Toplevel.pos_of tr) of
    SOME {file, offset, name} =>
      (case Symtab.lookup timings file of
        SOME offsets =>
          (case Inttab.lookup offsets offset of
            SOME (name', time) => if name = name' then SOME time else NONE
          | NONE => NONE)
      | NONE => NONE)
  | NONE => NONE)
  |> the_default Time.zeroTime;


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

fun build_theories symbols last_timing qualifier master_dir (options, thys) =
  let
    val context =
      {options = options, symbols = symbols, last_timing = last_timing};
    val condition = space_explode "," (Options.string options "condition");
    val conds = filter_out (can getenv_strict) condition;
  in
    if null conds then
      (Options.set_default options;
        Isabelle_Process.init_options ();
        Future.fork I;
        (Thy_Info.use_theories context qualifier master_dir
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
  Isabelle_Process.protocol_command "build_session"
    (fn [args_yxml] =>
        let
          val (symbol_codes, (command_timings, (verbose, (browser_info,
            (documents, (parent_name, (chapter, (session_name, (master_dir,
            (theories, (session_positions, (session_directories, (session_chapters,
            (doc_names, (global_theories, (loaded_theories, bibtex_entries)))))))))))))))) =
            YXML.parse_body args_yxml |>
              let
                open XML.Decode;
                val position = Position.of_properties o properties;
                val path = Path.explode o string;
              in
                pair (list (pair string int)) (pair (list properties) (pair bool (pair path
                  (pair (list string) (pair string (pair string (pair string
                    (pair path
                      (pair (((list (pair Options.decode (list (pair string position))))))
                        (pair (list (pair string properties))
                          (pair (list (pair string string))
                            (pair (list (pair string string)) (pair (list string)
                              (pair (list (pair string string)) (pair (list string)
                                (list (pair string (list string))))))))))))))))))
              end;

          val symbols = HTML.make_symbols symbol_codes;

          fun build () =
            let
              val _ =
                Resources.init_session
                  {session_positions = session_positions,
                   session_directories = session_directories,
                   session_chapters = session_chapters,
                   bibtex_entries = bibtex_entries,
                   docs = doc_names,
                   global_theories = global_theories,
                   loaded_theories = loaded_theories};

              val _ =
                Session.init
                  symbols
                  (Options.default_bool "browser_info")
                  browser_info
                  documents
                  parent_name
                  (chapter, session_name)
                  verbose;

              val last_timing = get_timings (fold update_timings command_timings empty_timings);

              val res1 =
                theories |>
                  (List.app (build_theories symbols last_timing session_name master_dir)
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
          |> Output.protocol_message Markup.build_session_finished)
        end
      | _ => raise Match);

end;
