(*  Title:      Pure/ProofGeneral/proof_general_emacs.ML
    Author:     David Aspinall and Markus Wenzel

Isabelle/Isar configuration for Emacs Proof General.
See also http://proofgeneral.inf.ed.ac.uk
*)

signature PROOF_GENERAL =
sig
  val test_markupN: string
  val sendback: string -> Pretty.T list -> unit
  val init: bool -> unit
  structure ThyLoad: sig val add_path: string -> unit end
end;

structure ProofGeneral: PROOF_GENERAL =
struct


(* print modes *)

val thm_depsN = "thm_deps";                (*meta-information about theorem deps*)
val test_markupN = "test_markup";          (*XML markup for everything*)

fun special ch = chr 1 ^ ch;


(* render markup *)

local

fun render_trees ts = fold render_tree ts
and render_tree (XML.Text s) = Buffer.add s
  | render_tree (XML.Elem ((name, props), ts)) =
      let
        val (bg1, en1) =
          if name <> Isabelle_Markup.promptN andalso print_mode_active test_markupN
          then XML.output_markup (name, props)
          else Markup.no_output;
        val (bg2, en2) =
          if null ts then Markup.no_output
          else if name = Isabelle_Markup.stateN then (special "O" ^ "\n", "\n" ^ special "P")
          else if name = Isabelle_Markup.sendbackN then (special "W", special "X")
          else if name = Isabelle_Markup.hiliteN then (special "0", special "1")
          else if name = Isabelle_Markup.tfreeN then (special "C", special "A")
          else if name = Isabelle_Markup.tvarN then (special "D", special "A")
          else if name = Isabelle_Markup.freeN then (special "E", special "A")
          else if name = Isabelle_Markup.boundN then (special "F", special "A")
          else if name = Isabelle_Markup.varN then (special "G", special "A")
          else if name = Isabelle_Markup.skolemN then (special "H", special "A")
          else
            (case Isabelle_Markup.get_entity_kind (name, props) of
              SOME kind =>
                if kind = Isabelle_Markup.classN then (special "B", special "A")
                else Markup.no_output
            | NONE => Markup.no_output);
      in
        Buffer.add bg1 #>
        Buffer.add bg2 #>
        render_trees ts #>
        Buffer.add en2 #>
        Buffer.add en1
      end;

in

fun render text =
  Buffer.content (render_trees (YXML.parse_body text) Buffer.empty);

end;


(* messages *)

fun message bg en prfx text =
  (case render text of
    "" => ()
  | s => Output.physical_writeln (enclose bg en (prefix_lines prfx s)));

fun setup_messages () =
 (Output.Private_Hooks.writeln_fn := message "" "" "";
  Output.Private_Hooks.status_fn := (fn _ => ());
  Output.Private_Hooks.report_fn := (fn _ => ());
  Output.Private_Hooks.urgent_message_fn := message (special "I") (special "J") "";
  Output.Private_Hooks.tracing_fn := message (special "I" ^ special "V") (special "J") "";
  Output.Private_Hooks.warning_fn := message (special "K") (special "L") "### ";
  Output.Private_Hooks.error_fn := (fn (_, s) => message (special "M") (special "N") "*** " s);
  Output.Private_Hooks.prompt_fn := (fn s => Output.physical_stdout (render s ^ special "S")));

fun panic s =
  (message (special "M") (special "N") "!!! " ("## SYSTEM EXIT ##\n" ^ s); exit 1);


(* notification *)

val emacs_notify = message (special "I") (special "J") "";

fun tell_clear_goals () =
  emacs_notify "Proof General, please clear the goals buffer.";

fun tell_clear_response () =
  emacs_notify "Proof General, please clear the response buffer.";

fun tell_file_loaded path =
  emacs_notify ("Proof General, this file is loaded: " ^ quote (File.platform_path path));

fun tell_file_retracted path =
  emacs_notify ("Proof General, you can unlock the file " ^ quote (File.platform_path path));

fun sendback heading prts =
  Pretty.writeln (Pretty.big_list heading [Pretty.markup Isabelle_Markup.sendback prts]);


(* theory loader actions *)

local

fun trace_action action name =
  if action = Thy_Info.Update then
    List.app tell_file_loaded (Thy_Info.loaded_files name)
  else if action = Thy_Info.Remove then
    List.app tell_file_retracted (Thy_Info.loaded_files name)
  else ();

in
  fun setup_thy_loader () = Thy_Info.add_hook trace_action;
  fun sync_thy_loader () = List.app (trace_action Thy_Info.Update) (Thy_Info.get_names ());
end;


(* get informed about files *)

(*liberal low-level version*)
val thy_name = perhaps (try (unsuffix ".thy")) o List.last o space_explode "/";

val inform_file_retracted = Thy_Info.kill_thy o thy_name;

fun inform_file_processed file =
  let
    val name = thy_name file;
    val _ = name = "" andalso error ("Bad file name: " ^ quote file);
    val _ =
      Thy_Info.register_thy (Toplevel.end_theory Position.none (Isar.state ()))
        handle ERROR msg =>
          (warning (cat_lines ["Failed to register theory: " ^ quote name, msg]);
            tell_file_retracted (Thy_Load.thy_path (Path.basic name)))
    val _ = Isar.init ();
  in () end;


(* restart top-level loop (keeps most state information) *)

val welcome = Output.urgent_message o Session.welcome;

fun restart () =
 (sync_thy_loader ();
  tell_clear_goals ();
  tell_clear_response ();
  Isar.init ();
  welcome ());


(* theorem dependency output *)

local

val spaces_quote = space_implode " " o map quote;

fun thm_deps_message (thms, deps) =
  emacs_notify ("Proof General, theorem dependencies of " ^ thms ^ " are " ^ deps);

in

fun setup_present_hook () = Toplevel.add_hook (fn _ => fn state => fn state' =>
  if print_mode_active thm_depsN andalso
    can Toplevel.theory_of state andalso Toplevel.is_theory state'
  then
    let val (names, deps) =
      ProofGeneralPgip.new_thms_deps (Toplevel.theory_of state) (Toplevel.theory_of state')
    in
      if null names orelse null deps then ()
      else thm_deps_message (spaces_quote names, spaces_quote deps)
    end
  else ());

end;


(* additional outer syntax for Isar *)

val _ =
  Outer_Syntax.improper_command "ProofGeneral.pr" "print state (internal)" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.keep (fn state =>
      if Toplevel.is_toplevel state orelse Toplevel.is_theory state then tell_clear_goals ()
      else (Toplevel.quiet := false; Toplevel.print_state true state))));

val _ = (*undo without output -- historical*)
  Outer_Syntax.improper_command "ProofGeneral.undo" "(internal)" Keyword.control
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative (fn () => Isar.undo 1)));

val _ =
  Outer_Syntax.improper_command "ProofGeneral.restart" "(internal)" Keyword.control
    (Parse.opt_unit >> (Toplevel.no_timing oo K (Toplevel.imperative restart)));

val _ =
  Outer_Syntax.improper_command "ProofGeneral.kill_proof" "(internal)" Keyword.control
    (Scan.succeed (Toplevel.no_timing o
      Toplevel.imperative (fn () => (Isar.kill_proof (); tell_clear_goals ()))));

val _ =
  Outer_Syntax.improper_command "ProofGeneral.inform_file_processed" "(internal)" Keyword.control
    (Parse.name >> (fn file =>
      Toplevel.no_timing o Toplevel.imperative (fn () => inform_file_processed file)));

val _ =
  Outer_Syntax.improper_command "ProofGeneral.inform_file_retracted" "(internal)" Keyword.control
    (Parse.name >> (Toplevel.no_timing oo
      (fn file => Toplevel.imperative (fn () => inform_file_retracted file))));


(* init *)

val initialized = Unsynchronized.ref false;

fun init false = panic "No Proof General interface support for Isabelle/classic mode."
  | init true =
      (if ! initialized then ()
       else
        (Output.add_mode Symbol.xsymbolsN Symbol.output Output.default_escape;
         Output.add_mode ProofGeneralPgip.proof_general_emacsN
          Output.default_output Output.default_escape;
         Markup.add_mode ProofGeneralPgip.proof_general_emacsN YXML.output_markup;
         setup_messages ();
         ProofGeneralPgip.pgip_channel_emacs (! Output.Private_Hooks.urgent_message_fn);
         setup_thy_loader ();
         setup_present_hook ();
         initialized := true);
       sync_thy_loader ();
       Unsynchronized.change print_mode (update (op =) ProofGeneralPgip.proof_general_emacsN);
       Secure.PG_setup ();
       Isar.toplevel_loop TextIO.stdIn
        {init = true, welcome = true, sync = true, secure = Secure.is_secure ()});


(* fake old ThyLoad -- with new semantics *)

structure ThyLoad =
struct
  val add_path = Thy_Load.set_master_path o Path.explode;
end;

end;
