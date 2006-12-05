(*  Title:      Pure/ProofGeneral/proof_general_emacs.ML
    ID:         $Id$
    Author:     David Aspinall and Markus Wenzel

Isabelle/Isar configuration for Emacs Proof General.
See http://proofgeneral.inf.ed.ac.uk
*)

signature PROOF_GENERAL =
sig
  val init: bool -> unit
  val init_pgip: bool -> unit	        (* for compatibility; always fails *)
  val write_keywords: string -> unit
end;

structure ProofGeneral: PROOF_GENERAL =
struct

structure P = OuterParse;

(* print modes *)

val proof_generalN = "ProofGeneralEmacs";  (*token markup (colouring vars, etc.)*)
val pgasciiN = "PGASCII";                  (*plain 7-bit ASCII communication*)
val xsymbolsN = Symbol.xsymbolsN;          (*X-Symbol symbols*)
val thm_depsN = "thm_deps";                (*meta-information about theorem deps*)

fun special oct =
  if Output.has_mode pgasciiN then chr 1 ^ chr (ord (oct_char oct) - 167)
  else oct_char oct;


(* text output: print modes for xsymbol *)

local

fun xsym_output "\\" = "\\\\"
  | xsym_output s = if Symbol.is_raw s then Symbol.decode_raw s else s;

fun xsymbols_output s =
  if Output.has_mode xsymbolsN andalso exists_string (equal "\\") s then
    let val syms = Symbol.explode s
    in (implode (map xsym_output syms), real (Symbol.length syms)) end
  else Symbol.default_output s;

in

fun setup_xsymbols_output () =
  Output.add_mode xsymbolsN
    (xsymbols_output, K xsymbols_output, Symbol.default_indent, Symbol.encode_raw);

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
    (bg_tag () ^ x ^ end_tag (), real (Symbol.length (Symbol.explode x)));

fun free_or_skolem x =
  (case try Name.dest_skolem x of
    NONE => tagit free_tag x
  | SOME x' => tagit skolem_tag x');

fun var_or_skolem s =
  (case Syntax.read_variable s of
    SOME (x, i) =>
      (case try Name.dest_skolem x of
        NONE => tagit var_tag s
      | SOME x' => tagit skolem_tag
          (setmp show_question_marks true Syntax.string_of_vname (x', i)))
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

val _ = Context.add_setup (Theory.add_tokentrfuns proof_general_trans);

end;


(* messages and notification *)

fun decorate bg en prfx =
  writeln_default o enclose bg en o prefix_lines prfx;

fun setup_messages () =
 (writeln_fn := (fn s => decorate "" "" "" s);
  priority_fn := (fn s => decorate (special "360") (special "361") "" s);
  tracing_fn := (fn s => decorate (special "360" ^ special "375") (special "361") "" s);
  info_fn := (fn s => decorate (special "362") (special "363") "+++ " s);
  debug_fn := (fn s => decorate (special "362") (special "363") "+++ " s);
  warning_fn := (fn s => decorate (special "362") (special "363") "### " s);
  error_fn := (fn s => decorate (special "364") (special "365") "*** " s);
  panic_fn := (fn s => decorate (special "364") (special "365") "!!! " s));


fun emacs_notify s = decorate (special "360") (special "361") "" s;

fun tell_clear_goals () =
    emacs_notify "Proof General, please clear the goals buffer.";

fun tell_clear_response () =
    emacs_notify "Proof General, please clear the response buffer.";

fun tell_file_loaded path =
    emacs_notify ("Proof General, this file is loaded: " ^ 
		  quote (File.platform_path path));

fun tell_file_retracted path =
    emacs_notify ("Proof General, you can unlock the file " 
		  ^ quote (File.platform_path path));


(* theory / proof state output *)

local

fun tmp_markers f =
  setmp Display.current_goals_markers (special "366", special "367", "") f ();

fun print_current_goals n m st =
    tmp_markers (fn () => Display.print_current_goals_default n m st);

fun print_state b st =
    tmp_markers (fn () => Toplevel.print_state_default b st);

in

fun setup_state () =
  (Display.print_current_goals_fn := print_current_goals;
   Toplevel.print_state_fn := print_state;
   Toplevel.prompt_state_fn := (fn s => suffix (special "372")
     (Toplevel.prompt_state_default s)));

end;


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


(* prepare theory context *)

val thy_name = Path.pack o #1 o Path.split_ext o Path.base o Path.unpack;

(* FIXME general treatment of tracing*)
val update_thy_only = setmp MetaSimplifier.trace_simp false ThyInfo.update_thy_only;

fun dynamic_context () =
  (case Context.get_context () of
    SOME thy => "  Using current (dynamic!) one: " ^ quote (Context.theory_name thy)
  | NONE => "");

fun try_update_thy_only file =
  ThyLoad.cond_add_path (Path.dir (Path.unpack file)) (fn () =>
    let val name = thy_name file in
      if is_some (ThyLoad.check_file NONE (ThyLoad.thy_path name))
      then update_thy_only name
      else warning ("Unkown theory context of ML file." ^ dynamic_context ())
    end) ();


(* get informed about files *)

val inform_file_retracted = ThyInfo.if_known_thy ThyInfo.remove_thy o thy_name;
val inform_file_processed = ThyInfo.if_known_thy ThyInfo.touch_child_thys o thy_name;
val openfile_retract = Output.no_warnings (ThyInfo.if_known_thy ThyInfo.remove_thy) o thy_name;

fun proper_inform_file_processed file state =
  let val name = thy_name file in
    if Toplevel.is_toplevel state andalso ThyInfo.known_thy name then
     (ThyInfo.touch_child_thys name;
      ThyInfo.pretend_use_thy_only name handle ERROR msg =>
       (warning msg; warning ("Failed to register theory: " ^ quote name);
        tell_file_retracted (Path.base (Path.unpack file))))
    else raise Toplevel.UNDEF
  end;

fun vacuous_inform_file_processed file state =
 (warning ("No theory " ^ quote (thy_name file));
  tell_file_retracted (Path.base (Path.unpack file)));


(* restart top-level loop (keeps most state information) *)

val welcome = priority o Session.welcome;

fun restart () =
    (sync_thy_loader ();
     tell_clear_goals ();
     tell_clear_response ();
     welcome ();
     raise Toplevel.RESTART)


(* theorem dependency output *)

local

val spaces_quote = space_implode " " o map quote;

fun thm_deps_message (thms, deps) =
    emacs_notify ("Proof General, theorem dependencies of " ^ thms ^ " are " ^ deps);

(* FIXME: check this uses non-transitive closure function here *)
fun tell_thm_deps ths = conditional (Output.has_mode thm_depsN) (fn () =>
  let
    val names = filter_out (equal "") (map PureThy.get_name_hint ths);
    val deps = filter_out (equal "")
      (Symtab.keys (fold Proofterm.thms_of_proof
        (map Thm.proof_of ths) Symtab.empty));
  in
    if null names orelse null deps then ()
    else thm_deps_message (spaces_quote names, spaces_quote deps)
  end);

in

fun setup_present_hook () =
  Present.add_hook (fn _ => fn res => tell_thm_deps (maps #2 res));

end;


(* additional outer syntax for Isar *)

local structure P = OuterParse and K = OuterKeyword in

val undoP = (*undo without output*)
  OuterSyntax.improper_command "ProofGeneral.undo" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.undo));

val redoP = (*redo without output*)
  OuterSyntax.improper_command "ProofGeneral.redo" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.redo));

val context_thy_onlyP =
  OuterSyntax.improper_command "ProofGeneral.context_thy_only" "(internal)" K.control
    (P.name >> (Toplevel.no_timing oo IsarCmd.init_context update_thy_only));

val try_context_thy_onlyP =
  OuterSyntax.improper_command "ProofGeneral.try_context_thy_only" "(internal)" K.control
    (P.name >> (Toplevel.no_timing oo
      (Toplevel.imperative (K ()) oo IsarCmd.init_context try_update_thy_only)));

val restartP =
  OuterSyntax.improper_command "ProofGeneral.restart" "(internal)" K.control
    (P.opt_unit >> (Toplevel.no_timing oo K (Toplevel.imperative restart)));

val kill_proofP =
  OuterSyntax.improper_command "ProofGeneral.kill_proof" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.kill_proof_notify tell_clear_goals));

val inform_file_processedP =
  OuterSyntax.improper_command "ProofGeneral.inform_file_processed" "(internal)" K.control
    (P.name >> (fn file => Toplevel.no_timing o
      Toplevel.keep (vacuous_inform_file_processed file) o
      Toplevel.kill o
      Toplevel.keep (proper_inform_file_processed file)));

val inform_file_retractedP =
  OuterSyntax.improper_command "ProofGeneral.inform_file_retracted" "(internal)" K.control
    (P.name >> (Toplevel.no_timing oo
      (fn file => Toplevel.imperative (fn () => inform_file_retracted file))));

val process_pgipP =
  OuterSyntax.improper_command "ProofGeneral.process_pgip" "(internal)" K.control
    (P.text >> (Toplevel.no_timing oo
      (fn txt => Toplevel.imperative (fn () => ProofGeneralPgip.process_pgip txt))));

fun init_outer_syntax () = OuterSyntax.add_parsers
 [undoP, redoP, restartP, kill_proofP, context_thy_onlyP, try_context_thy_onlyP,
  inform_file_processedP, inform_file_retractedP, process_pgipP];

end;


(* init *)

val initialized = ref false;

fun set_prompts () = ml_prompts "ML> " "ML# "

fun init_setup () =
  (conditional (not (! initialized)) (fn () =>
   (setmp warning_fn (K ()) init_outer_syntax ();
    setup_xsymbols_output ();
    setup_messages ();
    ProofGeneralPgip.init_pgip_channel (!priority_fn);
    setup_state ();
    setup_thy_loader ();
    setup_present_hook ();
    set initialized; ()));
  sync_thy_loader ();
  change print_mode (cons proof_generalN o remove (op =) proof_generalN);
  set_prompts ())

fun init true = (init_setup ();
		 Isar.sync_main ())
  | init false = Output.panic "Interface support no longer available for Isabelle/classic mode."

fun init_pgip false = init true
  | init_pgip true = Output.panic "No PGIP here, please use ProofGeneralPgip.init_pgip (update your isabelle-process script)."




(** generate elisp file for keyword classification **)

local

val regexp_meta = member (op =) (explode ".*+?[]^$");
val regexp_quote =
  implode o map (fn c => if regexp_meta c then "\\\\" ^ c else c) o explode;

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
  defconst "minor" (List.filter Syntax.is_identifier keywords) ^
  implode (map (make_elisp_commands commands) OuterKeyword.kinds) ^
  "\n(provide 'isar-keywords)\n";

in

fun write_keywords s =
 (init_outer_syntax ();
  File.write (Path.unpack ("isar-keywords" ^ (if s = "" then "" else "-" ^ s) ^".el"))
    (make_elisp_syntax (OuterSyntax.dest_keywords (), OuterSyntax.dest_parsers ())));

end;


end;
