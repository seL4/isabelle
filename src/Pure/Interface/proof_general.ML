(*  Title:      Pure/Interface/proof_general.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Configuration for Proof General (see http://www.dcs.ed.ac.uk/home/proofgen/).
*)

signature PROOF_GENERAL =
sig
  val setup: (theory -> theory) list
  val update_thy_only: string -> unit
  val try_update_thy_only: string -> unit
  val inform_file_processed: string -> unit
  val inform_file_retracted: string -> unit
  val thms_containing: xstring list -> unit
  val help: unit -> unit
  val show_context: unit -> theory
  val kill_goal: unit -> unit
  val repeat_undo: int -> unit
  val isa_restart: unit -> unit
  val init: bool -> unit
  val write_keywords: unit -> unit
end;

structure ProofGeneral: PROOF_GENERAL =
struct

(** compile-time theory setup **)

(* token translations *)

val proof_generalN = "ProofGeneral";

local

val end_tag = oct_char "350";
val tclass_tag = oct_char "351";
val tfree_tag = oct_char "352";
val tvar_tag = oct_char "353";
val free_tag = oct_char "354";
val bound_tag = oct_char "355";
val var_tag = oct_char "356";
val skolem_tag = oct_char "357";

fun tagit p x = (p ^ x ^ end_tag, real (Symbol.length (Symbol.explode x)));

fun unless_skolem tag x =
  (case try Syntax.dest_skolem x of
    None => tagit tag x
  | Some x' => tagit skolem_tag x');

in

val proof_general_trans =
 Syntax.tokentrans_mode proof_generalN
  [("class", tagit tclass_tag),
   ("tfree", tagit tfree_tag),
   ("tvar", tagit tvar_tag),
   ("free", unless_skolem free_tag),
   ("bound", tagit bound_tag),
   ("var", unless_skolem var_tag)];

end;


(* setup *)

val setup = [Theory.add_tokentrfuns proof_general_trans];



(** run-time operations **)

(* symbol output *)

fun xsymbols_output s =
  if not (exists_string (equal "\\") s) then (s, real (size s))
  else
    let val syms = Symbol.explode s
    in (implode (map (fn "\\" => "\\\\" | c => c) syms), real (Symbol.length syms)) end;

fun setup_xsymbols_output () = Symbol.add_mode "xsymbols" xsymbols_output;


(* messages *)

val plain_output = Library.std_output o suffix "\n";

fun decorate_lines bg en "" = plain_output o enclose bg en
  | decorate_lines bg en prfx = plain_output o enclose bg en o prefix_lines prfx;

fun setup_messages () =
 (priority_fn := decorate_lines (oct_char "360") (oct_char "361") "";
  warning_fn := (decorate_lines (oct_char "362") (oct_char "363") "### ");
  error_fn := (decorate_lines (oct_char "364") (oct_char "365") "*** "));


(* notification *)

fun tell_clear_goals () = priority "Proof General, please clear the goals buffer.";
fun tell_clear_response () = priority "Proof General, please clear the response buffer.";
fun tell_file msg path = priority ("Proof General, " ^ msg ^ " " ^ quote (File.sysify_path path));


(* theory / proof state output *)

fun setup_state () =
 (current_goals_markers :=
    let
      val begin_state = oct_char "366";
      val end_state= oct_char "367";
    in (begin_state, end_state, "") end;
  Toplevel.prompt_state_fn := (suffix (oct_char "372") o Toplevel.prompt_state_default));


(* theory loader actions *)

local

fun add_master_files name files =
  let val masters = [ThyLoad.thy_path name, ThyLoad.ml_path name]
  in masters @ gen_rems (op = o pairself Path.base) (files, masters) end;

fun trace_action action name =
  if action = ThyInfo.Update then
    seq (tell_file "this file is loaded:") (ThyInfo.loaded_files name)
  else if action = ThyInfo.Outdate orelse action = ThyInfo.Remove then
    seq (tell_file "you can unlock the file") (add_master_files name (ThyInfo.loaded_files name))
  else ();

in
  fun setup_thy_loader () = ThyInfo.add_hook trace_action;
end;


(* prepare theory context *)

val thy_name = Path.pack o Path.drop_ext o Path.base o Path.unpack;
val update_thy_only = setmp Thm.trace_simp false ThyInfo.update_thy_only;

fun which_context () =
  (case Context.get_context () of
    Some thy => "  Using current (dynamic!) one: " ^
      (case try PureThy.get_name thy of Some name => quote name | None => "<unnamed>")
  | None => "");

fun try_update_thy_only file =
  ThyLoad.cond_add_path (Path.dir (Path.unpack file)) (fn () =>
    let val name = thy_name file in
      if is_some (ThyLoad.check_file (ThyLoad.thy_path name)) then update_thy_only name
      else warning ("Unkown theory context of ML file." ^ which_context ())
    end) ();


(* get informed about files *)

val touch_child_thys = ThyInfo.if_known_thy ThyInfo.touch_child_thys;

val inform_file_processed = touch_child_thys o thy_name;
val inform_file_retracted = touch_child_thys o thy_name;

fun proper_inform_file_processed file state =
  let val name = thy_name file in
    touch_child_thys name;
    if not (Toplevel.is_toplevel state) then
      warning ("Not at toplevel -- cannot register theory " ^ quote name)
    else Library.transform_error ThyInfo.pretend_use_thy_only name handle ERROR_MESSAGE msg =>
      (warning msg; warning ("Failed to register theory " ^ quote name))
  end;


(* misc commands for ProofGeneral/isa *)

fun thms_containing cs = ThmDatabase.print_thms_containing (the_context ()) cs;

val welcome = priority o Session.welcome;
val help = welcome;
val show_context = Context.the_context;

fun kill_goal () = (Goals.reset_goals (); tell_clear_goals ());

fun no_print_goals f = setmp print_current_goals_fn (fn _ => fn _ => fn _ => ()) f;

fun repeat_undo 0 = ()
  | repeat_undo 1 = undo ()
  | repeat_undo n = (no_print_goals undo (); repeat_undo (n - 1));


(* re-init process (an approximation) *)

local

fun restart isar =
 (if isar then tell_clear_goals () else kill_goal ();
  tell_clear_response ();
  welcome ());

fun restart_loader () =
  (ThyInfo.touch_all_thys (); ThyLoad.reset_path ());

in

fun isa_start () = restart false;
fun isa_restart () = (restart_loader (); restart false);
fun isar_restart () = (restart_loader (); restart true; raise Toplevel.RESTART);

end;


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val old_undoP = (*same name for compatibility with PG/Isabelle99*)
  OuterSyntax.improper_command "undo" "undo last command (no output)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.undo));

val undoP =
  OuterSyntax.improper_command "ProofGeneral.undo" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.undo));

val context_thy_onlyP =
  OuterSyntax.improper_command "ProofGeneral.context_thy_only" "(internal)" K.control
    (P.name >> (Toplevel.no_timing oo IsarThy.init_context update_thy_only));

val try_context_thy_onlyP =
  OuterSyntax.improper_command "ProofGeneral.try_context_thy_only" "(internal)" K.control
    (P.name >> (Toplevel.no_timing oo
      (Toplevel.imperative (K ()) oo IsarThy.init_context try_update_thy_only)));

val restartP =
  OuterSyntax.improper_command "ProofGeneral.restart" "(internal)" K.control
    (P.opt_unit >> (Toplevel.no_timing oo K (Toplevel.imperative isar_restart)));

val kill_proofP =
  OuterSyntax.improper_command "ProofGeneral.kill_proof" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.kill_proof_notify tell_clear_goals));

val inform_file_processedP =
  OuterSyntax.improper_command "ProofGeneral.inform_file_processed" "(internal)" K.control
    (P.name >> (Toplevel.no_timing oo
      (fn name => Toplevel.keep (proper_inform_file_processed name))));

val inform_file_retractedP =
  OuterSyntax.improper_command "ProofGeneral.inform_file_retracted" "(internal)" K.control
    (P.name >> (Toplevel.no_timing oo
      (fn name => Toplevel.imperative (fn () => inform_file_retracted name))));

fun init_outer_syntax () = OuterSyntax.add_parsers
 [old_undoP, undoP, restartP, kill_proofP, context_thy_onlyP, try_context_thy_onlyP,
  inform_file_processedP, inform_file_retractedP];

end;


(* init *)

fun init isar =
 (if isar then setmp warning_fn (K ()) init_outer_syntax () else ();
  setup_xsymbols_output ();
  setup_messages ();
  setup_state ();
  setup_thy_loader ();
  print_mode := [proof_generalN];
  set quick_and_dirty;
  ThmDeps.enable ();
  if isar then ml_prompts "ML> " "ML# "
  else ml_prompts ("> " ^ oct_char "372") ("- " ^ oct_char "373");
  welcome ();
  if isar then Isar.sync_main () else isa_start ());



(** generate keyword classification file **)

local

val regexp_meta = explode ".*+?[]^$";
val regexp_quote = implode o map (fn c => if c mem regexp_meta then "\\\\" ^ c else c) o explode;

fun defconst name strs =
  "\n(defconst isar-keywords-" ^ name ^
  "\n  '(" ^ space_implode "\n    " (map (quote o regexp_quote) strs) ^ "))\n";

fun make_elisp_commands commands kind =
  defconst kind (mapfilter (fn (c, _, k, _) => if k = kind then Some c else None) commands);

fun make_elisp_syntax (keywords, commands) =
  ";;\n\
  \;; Keyword classification tables for Isabelle/Isar.\n\
  \;; This file generated by Isabelle -- DO NOT EDIT!\n\
  \;;\n\
  \;; $" ^ "Id$\n\
  \;;\n" ^
  defconst "major" (map #1 commands) ^
  defconst "minor" (filter Syntax.is_identifier keywords) ^
  implode (map (make_elisp_commands commands) OuterSyntax.Keyword.kinds) ^
  "\n(provide 'isar-keywords)\n";

val keywords_file = "isar-keywords.el";

in

fun write_keywords () =
  (init_outer_syntax ();
    File.write (Path.unpack keywords_file)
      (make_elisp_syntax (OuterSyntax.dest_keywords (), OuterSyntax.dest_parsers ())));

end;


end;
