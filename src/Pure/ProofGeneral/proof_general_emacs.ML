(*  Title:      Pure/ProofGeneral/proof_general_emacs.ML
    ID:         $Id$
    Author:     David Aspinall and Markus Wenzel

Isabelle/Isar configuration for Emacs Proof General.
See http://proofgeneral.inf.ed.ac.uk
*)

signature PROOF_GENERAL =
sig
  val init: bool -> unit
  val sendback: string -> Pretty.T list -> unit
  val write_keywords: string -> unit
end;

structure ProofGeneral: PROOF_GENERAL =
struct


(* print modes *)

val proof_generalN = "ProofGeneralEmacs";  (*token markup (colouring vars, etc.)*)
val pgasciiN = "PGASCII";                  (*plain 7-bit ASCII communication*)
val thm_depsN = "thm_deps";                (*meta-information about theorem deps*)

fun special oct =
  if print_mode_active pgasciiN then chr 1 ^ chr (ord (oct_char oct) - 167)
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


(* token translations *)

local

fun end_tag () = special "350";
val class_tag = ("class", fn () => special "351");
val tfree_tag = ("tfree", fn () => special "352");
val tvar_tag = ("tvar", fn () => special "353");
val free_tag = ("free", fn () => special "354");
val bound_tag = ("bound", fn () => special "355");
val var_tag = ("var", fn () => special "356");
val skolem_tag = ("skolem", fn () => special "357");

fun xml_atom kind x = XML.element "atom" [("kind", kind)] [XML.text x];

fun tagit (kind, bg_tag) x =
  (bg_tag () ^ x ^ end_tag (), Symbol.length (Symbol.explode x));

fun free_or_skolem x =
  (case try Name.dest_skolem x of
    NONE => tagit free_tag x
  | SOME x' => tagit skolem_tag x');

fun var_or_skolem s =
  (case Lexicon.read_variable s of
    SOME (x, i) =>
      (case try Name.dest_skolem x of
        NONE => tagit var_tag s
      | SOME x' => tagit skolem_tag
          (setmp show_question_marks true Term.string_of_vname (x', i)))
  | NONE => tagit var_tag s);

val proof_general_trans =
 Syntax.tokentrans_mode proof_generalN
  [("class", tagit class_tag),
   ("tfree", tagit tfree_tag),
   ("tvar", tagit tvar_tag),
   ("free", free_or_skolem),
   ("bound", tagit bound_tag),
   ("var", var_or_skolem)];

in

val _ = Context.add_setup (Sign.add_tokentrfuns proof_general_trans);

end;


(* common markup *)

fun proof_general_markup (name, props) =
  (if name = Markup.promptN then ("", special "372")
    else if name = Markup.stateN then (special "366" ^ "\n", "\n" ^ special "367")
    else if name = Markup.sendbackN then (special "376", special "377")
    else if name = Markup.hiliteN then (special "327", special "330")
    else ("", ""))
  |> (name <> Markup.promptN andalso print_mode_active "test_markup") ?
    (fn (bg, en) =>
      (bg ^ enclose "<" ">" (space_implode " " (name :: map XML.attribute props)),
        enclose "</" ">" name ^ en));

val _ = Markup.add_mode proof_generalN proof_general_markup;


(* messages and notification *)

fun decorate bg en prfx =
  Output.writeln_default o enclose bg en o prefix_lines prfx;

fun setup_messages () =
 (Output.writeln_fn := Output.writeln_default;
  Output.priority_fn := (fn s => decorate (special "360") (special "361") "" s);
  Output.tracing_fn := (fn s => decorate (special "360" ^ special "375") (special "361") "" s);
  Output.debug_fn := (fn s => decorate (special "362") (special "363") "+++ " s);
  Output.warning_fn := (fn s => decorate (special "362") (special "363") "### " s);
  Output.error_fn := (fn s => decorate (special "364") (special "365") "*** " s));

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
  fun sync_thy_loader () = List.app (trace_action ThyInfo.Update) (ThyInfo.names ());
end;


(* get informed about files *)

val thy_name = Path.implode o #1 o Path.split_ext o Path.base o Path.explode;

val inform_file_retracted = ThyInfo.if_known_thy ThyInfo.remove_thy o thy_name;
val inform_file_processed = ThyInfo.if_known_thy ThyInfo.touch_child_thys o thy_name;

fun proper_inform_file_processed file () =
  let val name = thy_name file in
    if ThyInfo.known_thy name then
     (ThyInfo.touch_child_thys name;
      ThyInfo.register_thy name handle ERROR msg =>
       (warning (cat_lines [msg, "Failed to register theory: " ^ quote name]);
        tell_file_retracted (Path.base (Path.explode file))))
    else raise Toplevel.UNDEF
  end;

fun vacuous_inform_file_processed file () =
 (warning ("No theory " ^ quote (thy_name file));
  tell_file_retracted (Path.base (Path.explode file)));


(* restart top-level loop (keeps most state information) *)

val welcome = priority o Session.welcome;

fun restart () =
 (sync_thy_loader ();
  tell_clear_goals ();
  tell_clear_response ();
  welcome ();
  raise Toplevel.RESTART);


(* theorem dependency output *)

local

val spaces_quote = space_implode " " o map quote;

fun thm_deps_message (thms, deps) =
  emacs_notify ("Proof General, theorem dependencies of " ^ thms ^ " are " ^ deps);

fun tell_thm_deps ths =
  if print_mode_active thm_depsN then
    let
      val names = map PureThy.get_name_hint (filter PureThy.has_name_hint ths);
      val deps = Symtab.keys (fold Proofterm.thms_of_proof'
				   (map Thm.proof_of ths) Symtab.empty);
    in
      if null names orelse null deps then ()
      else thm_deps_message (spaces_quote names, spaces_quote deps)
    end
  else ();

in

fun setup_present_hook () =
  Present.add_hook (fn _ => fn res => tell_thm_deps (maps #2 res));

end;


(* additional outer syntax for Isar *)

local structure P = OuterParse and K = OuterKeyword in

fun undoP () = (*undo without output*)
  OuterSyntax.improper_command "ProofGeneral.undo" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.undo));

fun restartP () =
  OuterSyntax.improper_command "ProofGeneral.restart" "(internal)" K.control
    (P.opt_unit >> (Toplevel.no_timing oo K (Toplevel.imperative restart)));

fun kill_proofP () =
  OuterSyntax.improper_command "ProofGeneral.kill_proof" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.kill_proof_notify tell_clear_goals));

fun inform_file_processedP () =
  OuterSyntax.improper_command "ProofGeneral.inform_file_processed" "(internal)" K.control
    (P.name >> (fn file => Toplevel.no_timing o
      Toplevel.init_empty (vacuous_inform_file_processed file) o
      Toplevel.kill o
      Toplevel.init_empty (proper_inform_file_processed file)));

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
       change print_mode (cons proof_generalN o remove (op =) proof_generalN);
       Isar.sync_main ());



(** generate elisp file for keyword classification **)

local

val regexp_meta = member (op =) (explode ".*+?[]^$");
val regexp_quote = translate_string (fn c => if regexp_meta c then "\\\\" ^ c else c);

fun defconst name strs =
  "\n(defconst isar-keywords-" ^ name ^
  "\n  '(" ^ space_implode "\n    " (map (quote o regexp_quote) strs) ^ "))\n";

fun make_elisp_commands commands kind = defconst kind
  (commands |> map_filter (fn (c, _, k, _) => if k = kind then SOME c else NONE));

fun make_elisp_syntax (keywords, commands) =
  ";;\n\
  \;; Keyword classification tables for Isabelle/Isar.\n\
  \;; This file was generated by " ^ Session.name () ^ " -- DO NOT EDIT!\n\
  \;;\n\
  \;; $" ^ "Id$\n\
  \;;\n" ^
  defconst "major" (map #1 commands) ^
  defconst "minor" (filter Syntax.is_identifier keywords) ^
  implode (map (make_elisp_commands commands) OuterKeyword.kinds) ^
  "\n(provide 'isar-keywords)\n";

in

fun write_keywords s =
 (init_outer_syntax ();
  File.write (Path.explode ("isar-keywords" ^ (if s = "" then "" else "-" ^ s) ^ ".el"))
    (make_elisp_syntax (OuterSyntax.dest_keywords (), OuterSyntax.dest_parsers ())));

end;

end;
