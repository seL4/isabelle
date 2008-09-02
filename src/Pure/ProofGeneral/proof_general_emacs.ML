(*  Title:      Pure/ProofGeneral/proof_general_emacs.ML
    ID:         $Id$
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
val pgasciiN = "PGASCII";                  (*plain 7-bit ASCII communication*)
val thm_depsN = "thm_deps";                (*meta-information about theorem deps*)
val test_markupN = "test_markup";          (*XML markup for everything*)

val _ = Markup.add_mode test_markupN (fn (name, props) =>
  if name = Markup.promptN then ("", "") else XML.output_markup (name, props));

fun special oct =
  if print_mode_active pgasciiN then Symbol.SOH ^ chr (ord (oct_char oct) - 167)
  else oct_char oct;


(* text output: print modes for xsymbol *)

local

fun xsym_output "\\" = "\\\\"
  | xsym_output s = if Symbol.is_raw s then Symbol.decode_raw s else s;

fun xsymbols_output s =
  if print_mode_active Symbol.xsymbolsN andalso exists_string (equal "\\") s then
    let val syms = Symbol.explode s
    in (implode (map xsym_output syms), Symbol.length syms) end
  else Output.default_output s;

in

fun setup_xsymbols_output () =
  Output.add_mode Symbol.xsymbolsN xsymbols_output Symbol.encode_raw;

end;


(* common markup *)

val _ = Markup.add_mode proof_generalN (fn (name, props) =>
  let
    val (bg1, en1) =
      if name = Markup.stateN then (special "366" ^ "\n", "\n" ^ special "367")
      else if name = Markup.sendbackN then (special "376", special "377")
      else if name = Markup.hiliteN then (special "327", special "330")
      else if name = Markup.tclassN then (special "351", special "350")
      else if name = Markup.tfreeN then (special "352", special "350")
      else if name = Markup.tvarN then (special "353", special "350")
      else if name = Markup.freeN then (special "354", special "350")
      else if name = Markup.boundN then (special "355", special "350")
      else if name = Markup.varN then (special "356", special "350")
      else if name = Markup.skolemN then (special "357", special "350")
      else ("", "");
    val (bg2, en2) =
      if name <> Markup.promptN andalso print_mode_active test_markupN
      then XML.output_markup (name, props)
      else ("", "");
  in (bg1 ^ bg2, en2 ^ en1) end);


(* messages and notification *)

fun decorate bg en prfx =
  Output.writeln_default o enclose bg en o prefix_lines prfx;

fun setup_messages () =
 (Output.writeln_fn := Output.writeln_default;
  Output.status_fn := (fn "" => () | s => ! Output.priority_fn s);
  Output.priority_fn := (fn s => decorate (special "360") (special "361") "" s);
  Output.tracing_fn := (fn s => decorate (special "360" ^ special "375") (special "361") "" s);
  Output.debug_fn := (fn s => decorate (special "362") (special "363") "+++ " s);
  Output.warning_fn := (fn s => decorate (special "362") (special "363") "### " s);
  Output.error_fn := (fn s => decorate (special "364") (special "365") "*** " s);
  Output.prompt_fn := (fn s => Output.std_output (s ^ special "372")));

fun panic s =
  (decorate (special "364") (special "365") "!!! " ("## SYSTEM EXIT ##\n" ^ s); exit 1);

fun emacs_notify s = decorate (special "360") (special "361") "" s;

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
        (Isar.>> Toplevel.commit_exit; ThyInfo.touch_child_thys name; ThyInfo.register_thy name)
          handle ERROR msg =>
            (warning (cat_lines ["Failed to register theory: " ^ quote name, msg]);
              tell_file_retracted (ThyLoad.thy_path name))
      else ();
    val _ = Isar.init_point ();
  in () end;


(* restart top-level loop (keeps most state information) *)

val welcome = priority o Session.welcome;

fun restart () =
 (sync_thy_loader ();
  tell_clear_goals ();
  tell_clear_response ();
  Isar.init_point ();
  welcome ());


(* theorem dependency output *)

local

val spaces_quote = space_implode " " o map quote;

fun thm_deps_message (thms, deps) =
  emacs_notify ("Proof General, theorem dependencies of " ^ thms ^ " are " ^ deps);

in

fun setup_present_hook () = Toplevel.add_hook (fn _ => fn state => fn (state', opt_err) =>
  if print_mode_active thm_depsN andalso Toplevel.is_theory state' andalso is_none opt_err then
    let val (names, deps) = ProofGeneralPgip.new_thms_deps state state' in
      if null names orelse null deps then ()
      else thm_deps_message (spaces_quote names, spaces_quote deps)
    end
  else ());

end;


(* additional outer syntax for Isar *)

local structure P = OuterParse and K = OuterKeyword in

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
  [undoP, restartP, kill_proofP, inform_file_processedP, inform_file_retractedP, process_pgipP];

end;


(* init *)

val initialized = ref false;

fun init false = panic "No Proof General interface support for Isabelle/classic mode."
  | init true =
      (! initialized orelse
        (Output.no_warnings init_outer_syntax ();
          setup_xsymbols_output ();
          setup_messages ();
          ProofGeneralPgip.init_pgip_channel (! Output.priority_fn);
          setup_thy_loader ();
          setup_present_hook ();
          set initialized);
        sync_thy_loader ();
       change print_mode (update (op =) proof_generalN);
       Isar.toplevel_loop {init = true, welcome = true, sync = true, secure = Secure.is_secure ()});

end;
