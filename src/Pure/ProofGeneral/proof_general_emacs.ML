(*  Title:      Pure/ProofGeneral/proof_general_emacs.ML
    Author:     David Aspinall and Markus Wenzel

Isabelle/Isar configuration for Emacs Proof General.
See also http://proofgeneral.inf.ed.ac.uk
*)

signature PROOF_GENERAL =
sig
  val test_markupN: string
  val init: bool -> unit
  val init_outer_syntax: unit -> unit
  val sendback: string -> Pretty.T list -> unit
end;

structure ProofGeneral: PROOF_GENERAL =
struct


(* print modes *)

val proof_generalN = "ProofGeneralEmacs";  (*token markup (colouring vars, etc.)*)
val thm_depsN = "thm_deps";                (*meta-information about theorem deps*)
val test_markupN = "test_markup";          (*XML markup for everything*)

fun special ch = Symbol.SOH ^ ch;


(* render markup *)

local

fun render_trees ts = fold render_tree ts
and render_tree (XML.Text s) = Buffer.add s
  | render_tree (XML.Elem (name, props, ts)) =
      let
        val (bg1, en1) =
          if name <> Markup.promptN andalso print_mode_active test_markupN
          then XML.output_markup (name, props)
          else Markup.no_output;
        val (bg2, en2) =
          if null ts then Markup.no_output
          else if name = Markup.stateN then (special "O" ^ "\n", "\n" ^ special "P")
          else if name = Markup.sendbackN then (special "W", special "X")
          else if name = Markup.hiliteN then (special "0", special "1")
          else if name = Markup.tclassN then (special "B", special "A")
          else if name = Markup.tfreeN then (special "C", special "A")
          else if name = Markup.tvarN then (special "D", special "A")
          else if name = Markup.freeN then (special "E", special "A")
          else if name = Markup.boundN then (special "F", special "A")
          else if name = Markup.varN then (special "G", special "A")
          else if name = Markup.skolemN then (special "H", special "A")
          else Markup.no_output;
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
  | s => Output.writeln_default (enclose bg en (prefix_lines prfx s)));

fun setup_messages () =
 (Output.writeln_fn := message "" "" "";
  Output.status_fn := (fn _ => ());
  Output.priority_fn := message (special "I") (special "J") "";
  Output.tracing_fn := message (special "I" ^ special "V") (special "J") "";
  Output.debug_fn := message (special "K") (special "L") "+++ ";
  Output.warning_fn := message (special "K") (special "L") "### ";
  Output.error_fn := message (special "M") (special "N") "*** ";
  Output.prompt_fn := (fn s => Output.std_output (render s ^ special "S")));

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
  Pretty.writeln (Pretty.big_list heading [Pretty.markup Markup.sendback prts]);


(* theory loader actions *)

local

fun trace_action action name =
  if action = ThyInfo.Update then
    List.app tell_file_loaded (ThyInfo.loaded_files name)
  else if action = ThyInfo.Outdate orelse action = ThyInfo.Remove then
    List.app tell_file_retracted (ThyInfo.loaded_files name)
  else ();

in
  fun setup_thy_loader () = ThyInfo.add_hook trace_action;
  fun sync_thy_loader () = List.app (trace_action ThyInfo.Update) (ThyInfo.get_names ());
end;


(* get informed about files *)

(*liberal low-level version*)
val thy_name = perhaps (try (unsuffix ".thy")) o List.last o space_explode "/";

val inform_file_retracted = ThyInfo.if_known_thy ThyInfo.remove_thy o thy_name;

fun inform_file_processed file =
  let
    val name = thy_name file;
    val _ = name = "" andalso error ("Bad file name: " ^ quote file);
    val _ =
      if ThyInfo.check_known_thy name then
        (Isar.>> (Toplevel.commit_exit Position.none);
            ThyInfo.touch_child_thys name; ThyInfo.register_thy name)
          handle ERROR msg =>
            (warning (cat_lines ["Failed to register theory: " ^ quote name, msg]);
              tell_file_retracted (ThyLoad.thy_path name))
      else ();
    val _ = Isar.init ();
  in () end;


(* restart top-level loop (keeps most state information) *)

val welcome = priority o Session.welcome;

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

local structure P = OuterParse and K = OuterKeyword in

fun prP () =
  OuterSyntax.improper_command "ProofGeneral.pr" "print state (internal)" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.keep (fn state =>
      if Toplevel.is_toplevel state orelse Toplevel.is_theory state then tell_clear_goals ()
      else (Toplevel.quiet := false; Toplevel.print_state true state))));

fun undoP () = (*undo without output -- historical*)
  OuterSyntax.improper_command "ProofGeneral.undo" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative (fn () => Isar.undo 1)));

fun restartP () =
  OuterSyntax.improper_command "ProofGeneral.restart" "(internal)" K.control
    (P.opt_unit >> (Toplevel.no_timing oo K (Toplevel.imperative restart)));

fun kill_proofP () =
  OuterSyntax.improper_command "ProofGeneral.kill_proof" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o
      Toplevel.imperative (fn () => (Isar.kill_proof (); tell_clear_goals ()))));

fun inform_file_processedP () =
  OuterSyntax.improper_command "ProofGeneral.inform_file_processed" "(internal)" K.control
    (P.name >> (fn file =>
      Toplevel.no_timing o Toplevel.imperative (fn () => inform_file_processed file)));

fun inform_file_retractedP () =
  OuterSyntax.improper_command "ProofGeneral.inform_file_retracted" "(internal)" K.control
    (P.name >> (Toplevel.no_timing oo
      (fn file => Toplevel.imperative (fn () => inform_file_retracted file))));

fun process_pgipP () =
  OuterSyntax.improper_command "ProofGeneral.process_pgip" "(internal)" K.control
    (P.text >> (Toplevel.no_timing oo
      (fn txt => Toplevel.imperative (fn () => ProofGeneralPgip.process_pgip txt))));

fun init_outer_syntax () = List.app (fn f => f ())
  [prP, undoP, restartP, kill_proofP, inform_file_processedP,
    inform_file_retractedP, process_pgipP];

end;


(* init *)

val initialized = Unsynchronized.ref false;

fun init false = panic "No Proof General interface support for Isabelle/classic mode."
  | init true =
      (! initialized orelse
        (Output.no_warnings_CRITICAL init_outer_syntax ();
          Output.add_mode Symbol.xsymbolsN Symbol.output Output.default_escape;
          Output.add_mode proof_generalN Output.default_output Output.default_escape;
          Markup.add_mode proof_generalN YXML.output_markup;
          setup_messages ();
          ProofGeneralPgip.init_pgip_channel (! Output.priority_fn);
          setup_thy_loader ();
          setup_present_hook ();
          Unsynchronized.set initialized);
        sync_thy_loader ();
       Unsynchronized.change print_mode (update (op =) proof_generalN);
       Isar.toplevel_loop {init = true, welcome = true, sync = true, secure = Secure.is_secure ()});

end;
