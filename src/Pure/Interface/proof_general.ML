(*  Title:      Pure/Interface/proof_general.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Configuration for Proof General of LFCS Edinburgh.
*)

signature PROOF_GENERAL =
sig
  val setup: (theory -> theory) list
  val thms_containing: xstring list -> unit
  val help: unit -> unit
  val show_context: unit -> theory
  val kill_goal: unit -> unit
  val repeat_undo: int -> unit
  val isa_restart: unit -> unit
  val inform_file_processed: string -> unit
  val inform_file_retracted: string -> unit
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

fun tagit p x = (p ^ x ^ end_tag, real (size x));

fun free_or_skolem x =
  (case try Syntax.dest_skolem x of
    None => tagit free_tag x
  | Some x' => tagit skolem_tag x');

in

val proof_general_trans =
 Syntax.tokentrans_mode proof_generalN
  [("class", tagit tclass_tag),
   ("tfree", tagit tfree_tag),
   ("tvar", tagit tvar_tag),
   ("free", free_or_skolem),
   ("bound", tagit bound_tag),
   ("var", tagit var_tag)];

end;


(* setup *)

val setup = [Theory.add_tokentrfuns proof_general_trans];



(** run-time operations **)

(* messages *)

val plain_output = std_output o suffix "\n";
fun plain_writeln x = Library.setmp writeln_fn plain_output x;

fun decorate_lines bg en "" = plain_output o enclose bg en
  | decorate_lines bg en prfx = plain_output o enclose bg en o prefix_lines prfx;

fun setup_messages () =
 (writeln_fn := (decorate_lines (oct_char "360") (oct_char "361") "");
  warning_fn := (decorate_lines (oct_char "362") (oct_char "363") "### ");
  error_fn := (decorate_lines (oct_char "364") (oct_char "365") "*** "));


(* notification *)

fun tell_clear_goals () = writeln "Proof General, please clear the goals buffer.";
fun tell_clear_response () = writeln "Proof General, please clear the response buffer.";
fun tell_file msg path = writeln ("Proof General, " ^ msg ^ " " ^ quote (File.sysify_path path));


(* theory / proof state output *)

fun print_current_goals n max th = plain_writeln (Goals.print_current_goals_default n max) th;

fun setup_state isar =
  (current_goals_markers :=
    let
      val begin_state = oct_char "366";
      val end_state= oct_char "367";
      val begin_goal = oct_char "370";
    in (begin_state, end_state, begin_goal) end;
  if isar then
   (Toplevel.print_state_fn := plain_writeln Toplevel.print_state_default;
    Toplevel.prompt_state_fn := (suffix (oct_char "372") o Toplevel.prompt_state_default))
  else ();
  Goals.print_current_goals_fn := print_current_goals);  (*isar: avoids verbose responses*)


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


(* get informed about files *)

val thy_name = Path.pack o Path.drop_ext o Path.base o Path.unpack;

(* FIXME improve, e.g. do something like pretend_use_thy *)
fun inform_file_processed file =
  ThyInfo.if_known_thy ThyInfo.touch_child_thys (thy_name file);

fun inform_file_retracted file =
  ThyInfo.if_known_thy ThyInfo.touch_child_thys (thy_name file);


(* misc commands for ProofGeneral/isa *)

fun thms_containing cs = ThmDatabase.print_thms_containing (the_context ()) cs;

val help = writeln o Session.welcome;
val show_context = Context.the_context;

fun kill_goal () = (Goals.reset_goals (); tell_clear_goals ());

fun no_print_goals f = setmp print_current_goals_fn (fn _ => fn _ => fn _ => ()) f;

fun repeat_undo 0 = ()
  | repeat_undo 1 = undo ()
  | repeat_undo n = (no_print_goals undo (); repeat_undo (n - 1));


(* re-init process (an approximation) *)

local

fun restart isar =
 (ThyInfo.touch_all_thys ();
  if isar then () else (ml_prompts ("> " ^ oct_char "372") ("- " ^ oct_char "373"); kill_goal ());
  tell_clear_response ();
  writeln (Session.welcome ()));

in

fun isa_restart () = restart false;
fun isar_restart () = (restart true; raise Toplevel.RESTART);

end;


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val restartP =
  OuterSyntax.improper_command "ProofGeneral.restart" "(internal)" K.control
    (P.opt_unit >> K (Toplevel.imperative isar_restart));

val kill_proofP =
  OuterSyntax.improper_command "ProofGeneral.kill_proof" "(internal)" K.control
    (Scan.succeed (IsarCmd.kill_proof_notify tell_clear_goals));

val inform_file_processedP =
  OuterSyntax.improper_command "ProofGeneral.inform_file_processed" "(internal)" K.control
    (P.name >> (fn name => Toplevel.imperative (fn () => inform_file_processed name)));

val inform_file_retractedP =
  OuterSyntax.improper_command "ProofGeneral.inform_file_retracted" "(internal)" K.control
    (P.name >> (fn name => Toplevel.imperative (fn () => inform_file_retracted name)));

fun init_outer_syntax () =
  OuterSyntax.add_parsers [restartP, kill_proofP, inform_file_processedP, inform_file_retractedP];

end;


(* init *)

fun init isar =
 (setup_messages ();
  setup_state isar;
  setup_thy_loader ();
  print_mode := [proof_generalN];
  set quick_and_dirty;
  if isar then init_outer_syntax () else ();
  if isar then Isar.sync_main () else isa_restart ());



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
