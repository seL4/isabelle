(*  Title:      Pure/proof_general.ML
    ID:         $Id$
    Author:     David Aspinall and Markus Wenzel
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Isabelle configuration for Proof General (see http://proofgeneral.inf.ed.ac.uk).
*)

signature PROOF_GENERAL =
sig
  val setup: (theory -> theory) list
  val update_thy_only: string -> unit
  val try_update_thy_only: string -> unit
  val inform_file_retracted: string -> unit
  val inform_file_processed: string -> unit
  val options: (string * (string * (string * (unit -> string) * (string -> unit)))) list ref
  val process_pgip: string -> unit
  val thms_containing: string list -> unit
  val help: unit -> unit
  val show_context: unit -> theory
  val kill_goal: unit -> unit
  val repeat_undo: int -> unit
  val isa_restart: unit -> unit
  val full_proofs: bool -> unit
  val init: bool -> unit
  val write_keywords: string -> unit
end;

structure ProofGeneral: PROOF_GENERAL =
struct

(* print modes *)

val proof_generalN = "ProofGeneral";
val xsymbolsN = "xsymbols";
val thm_depsN = "thm_deps";

val pgml_version_supported = "1.0";
val pgmlN = "PGML";
fun pgml () = pgmlN mem_string ! print_mode;


(* text output *)

local

fun xsymbols_output s =
  if xsymbolsN mem_string ! print_mode andalso exists_string (equal "\\") s then
    let val syms = Symbol.explode s
    in (implode (map (fn "\\" => "\\\\" | c => c) syms), real (Symbol.length syms)) end
  else (s, real (size s));

fun pgml_output (s, len) =
  if pgml () then (XML.text s, len)
  else (s, len);

in

fun setup_xsymbols_output () =
  Symbol.add_mode proof_generalN (pgml_output o xsymbols_output, Symbol.default_indent);

end;


(* token translations *)

local

val end_tag = oct_char "350";
val class_tag = ("class", oct_char "351");
val tfree_tag = ("tfree", oct_char "352");
val tvar_tag = ("tvar", oct_char "353");
val free_tag = ("free", oct_char "354");
val bound_tag = ("bound", oct_char "355");
val var_tag = ("var", oct_char "356");
val skolem_tag = ("skolem", oct_char "357");

fun xml_atom kind x = XML.element "atom" [("kind", kind)] [XML.text x];

fun tagit (kind, bg_tag) x =
  (if pgml () then xml_atom kind x else bg_tag ^ x ^ end_tag,
    real (Symbol.length (Symbol.explode x)));

fun free_or_skolem x =
  (case try Syntax.dest_skolem x of
    None => tagit free_tag x
  | Some x' => tagit skolem_tag x');

fun var_or_skolem s =
  (case Syntax.read_var s of
    Var ((x, i), _) =>
      (case try Syntax.dest_skolem x of
        None => tagit var_tag s
      | Some x' => tagit skolem_tag (Syntax.string_of_vname (x', i)))
  | _ => tagit var_tag s);

val proof_general_trans =
 Syntax.tokentrans_mode proof_generalN
  [("class", tagit class_tag),
   ("tfree", tagit tfree_tag),
   ("tvar", tagit tvar_tag),
   ("free", free_or_skolem),
   ("bound", tagit bound_tag),
   ("var", var_or_skolem)];

in val setup = [Theory.add_tokentrfuns proof_general_trans] end;


(* messages and notification *)

local

fun decorated_output bg en prfx =
  writeln_default o enclose bg en o prefix_lines prfx;

fun message kind bg en prfx s =
  if pgml () then writeln_default (XML.element kind [] [prefix_lines prfx s])
  else decorated_output bg en prfx s;

in

val notify = message "notify" (oct_char "360") (oct_char "361") "";

fun setup_messages () =
 (writeln_fn := message "output" "" "" "";
  priority_fn := message "information" (oct_char "360") (oct_char "361") "";
  tracing_fn := message "tracing" (oct_char "360" ^ oct_char "375") (oct_char "361") "";
  warning_fn := message "warning" (oct_char "362") (oct_char "363") "### ";
  error_fn := message "error" (oct_char "364") (oct_char "365") "*** ");

fun tell_clear_goals () = notify "Proof General, please clear the goals buffer.";
fun tell_clear_response () = notify "Proof General, please clear the response buffer.";
fun tell_file msg path = notify ("Proof General, " ^ msg ^ " " ^ quote (File.sysify_path path));

end;


(* theory / proof state output *)

local

fun tmp_markers f =
  setmp Display.current_goals_markers (oct_char "366", oct_char "367", "") f ();

fun statedisplay prts =
  writeln_default (XML.element "statedisplay" [] [Pretty.string_of (Pretty.chunks prts)]);

fun print_current_goals n m st =
  if pgml () then statedisplay (Display.pretty_current_goals n m st)
  else tmp_markers (fn () => Display.print_current_goals_default n m st);

fun print_state b st =
  if pgml () then statedisplay (Toplevel.pretty_state b st)
  else tmp_markers (fn () => Toplevel.print_state_default b st);

in

fun setup_state () =
 (Display.print_current_goals_fn := print_current_goals;
  Toplevel.print_state_fn := print_state;
  Toplevel.prompt_state_fn := (suffix (oct_char "372") o Toplevel.prompt_state_default));

end;


(* theorem dependency output *)

local

val spaces_quote = space_implode " " o map quote;

fun tell_thm_deps ths =
  conditional (thm_depsN mem_string ! print_mode) (fn () =>
    let
      val names = map Thm.name_of_thm ths \ "";
      val deps = Symtab.keys (foldl (uncurry Proofterm.thms_of_proof)
          (Symtab.empty, map Thm.proof_of ths)) \ "";
    in
      if null names orelse null deps then ()
      else notify ("Proof General, theorem dependencies of " ^ spaces_quote names ^ " are "
        ^ spaces_quote deps)
    end);

in

fun setup_present_hook () =
  Present.add_hook (fn _ => fn res => tell_thm_deps (flat (map #2 res)));

end;


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
  fun sync_thy_loader () = seq (trace_action ThyInfo.Update) (ThyInfo.names ());
end;


(* prepare theory context *)

val thy_name = Path.pack o Path.drop_ext o Path.base o Path.unpack;
val update_thy_only = setmp MetaSimplifier.trace_simp false ThyInfo.update_thy_only;

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

val inform_file_retracted = ThyInfo.if_known_thy ThyInfo.remove_thy o thy_name;
val inform_file_processed = ThyInfo.if_known_thy ThyInfo.touch_child_thys o thy_name;

fun proper_inform_file_processed file state =
  let val name = thy_name file in
    ThyInfo.if_known_thy ThyInfo.touch_child_thys name;
    if not (Toplevel.is_toplevel state) then
      warning ("Not at toplevel -- cannot register theory " ^ quote name)
    else Library.transform_error ThyInfo.pretend_use_thy_only name handle ERROR_MESSAGE msg =>
      (warning msg; warning ("Failed to register theory " ^ quote name))
  end;


(* options *)

fun nat_option r = ("nat",
  (fn () => string_of_int (!r)),
  (fn s => (case Syntax.read_nat s of
       None => error "nat_option: illegal value"
     | Some i => r := i)));

fun bool_option r = ("boolean",
  (fn () => Bool.toString (!r)),
  (fn "false" => r := false | "true" => r := true
    | _ => error "bool_option: illegal value"));

val proof_option = ("boolean",
  (fn () => Bool.toString (!proofs >= 2)),
  (fn "false" => proofs := 1 | "true" => proofs := 2
    | _ => error "proof_option: illegal value"));

val thm_deps_option = ("boolean",
  (fn () => Bool.toString ("thm_deps" mem !print_mode)),
  (fn "false" => print_mode := Library.gen_rems (op =) (!print_mode, ["thm_deps"])
    | "true" => print_mode := (["thm_deps"] @ !print_mode)
    | _ => error "thm_deps_option: illegal value"));

val print_depth_option = ("nat",
  (fn () => "10"),
  (fn s => (case Syntax.read_nat s of
       None => error "print_depth_option: illegal value"
     | Some i => print_depth i)));

val options = ref
  [("show-types", ("Whether to show types in Isabelle.",
      bool_option show_types)),
   ("show-sorts", ("Whether to show sorts in Isabelle.",
      bool_option show_sorts)),
   ("show-structs", ("Whether to show implicit structures in Isabelle.",
      bool_option show_structs)),
   ("show-consts", ("Whether to show types of consts in Isabelle goals.",
      bool_option show_consts)),
   ("long-names", ("Whether to show fully qualified names in Isabelle.",
      bool_option long_names)),
   ("show-brackets", ("Whether to show full bracketing in Isabelle.",
      bool_option show_brackets)),
   ("eta-contract", ("Whether to print terms eta-contracted in Isabelle.",
      bool_option Syntax.eta_contract)),
   ("trace-simplifier", ("Whether to trace the Simplifier in Isabelle.",
      bool_option trace_simp)),
   ("trace-rules", ("Whether to trace the standard rules in Isabelle.",
      bool_option trace_rules)),
   ("quick-and-dirty", ("Whether to take a few short cuts occasionally.",
      bool_option quick_and_dirty)),
   ("full-proofs", ("Whether to record full proof objects internally.",
      proof_option)),
   ("trace-unification", ("Whether to output error diagnostics during unification.",
      bool_option Pattern.trace_unify_fail)),
   ("show-main-goal", ("Whether to show main goal.",
      bool_option Proof.show_main_goal)),
   ("global-timing", ("Whether to enable timing in Isabelle.",
      bool_option Library.timing)),
   ("theorem-dependencies", ("Whether to track theorem dependencies within Proof General.",
      thm_deps_option)),
   ("goals-limit", ("Setting for maximum number of goals printed in Isabelle.",
      nat_option goals_limit)),
   ("prems-limit", ("Setting for maximum number of premises printed in Isabelle/Isar.",
      nat_option ProofContext.prems_limit)),
   ("print-depth", ("Setting for the ML print depth in Isabelle.",
      print_depth_option))];


(* sending PGIP commands to the interface *)

fun issue_pgip pgips = notify (XML.element "pgip" [] pgips);

fun usespgml () = 
  issue_pgip [XML.element "usespgml" [("version", pgml_version_supported)] []];

(*NB: the default returned here is actually the current value, so
  repeated uses of <askprefs> will not work correctly*)
fun show_options () = issue_pgip (map 
  (fn (name, (descr, (ty, get, _))) => (XML.element "oldhaspref"
    [("type", ty), ("descr", descr), ("default", get ())] [name])) (!options));

fun set_option name value = (case assoc (!options, name) of
      None => warning ("Unknown option: " ^ quote name)
    | Some (_, (_, _, set)) => set value);

fun get_option name = (case assoc (!options, name) of
      None => warning ("Unknown option: " ^ quote name)
    | Some (_, (_, get, _)) => 
	issue_pgip [XML.element "prefval" [("name", name)] [get ()]]);


(* processing PGIP commands from the interface *)

(*FIXME: matching on attributes is a bit too strict here*)

fun process_pgip_element pgip = (case pgip of
      XML.Elem ("askpgml", _, []) => usespgml ()
    | XML.Elem ("askprefs", _, [])  => show_options ()
    | XML.Elem ("getpref", [("name", name)], []) => get_option name
    | XML.Elem ("setpref", [("name", name)], [XML.Text value]) =>
        set_option name value
    | XML.Elem (e, _, _) => warning ("Unrecognized PGIP command: " ^ e)
    | XML.Text t => warning ("Unrecognized PGIP command:\n" ^ t));

fun process_pgip s = (case XML.tree_of_string s of
    XML.Elem ("pgip", _, pgips) => seq process_pgip_element pgips
  | _ => warning ("Invalid PGIP packet received\n" ^ s));


(* misc commands for ProofGeneral/isa *)

fun thms_containing ss =
  ProofContext.print_thms_containing (ProofContext.init (the_context ())) None ss;

val welcome = priority o Session.welcome;
val help = welcome;
val show_context = Context.the_context;

fun kill_goal () = (Goals.reset_goals (); tell_clear_goals ());

fun no_print_goals f = setmp Display.print_current_goals_fn (fn _ => fn _ => fn _ => ()) f;

fun repeat_undo 0 = ()
  | repeat_undo 1 = undo ()
  | repeat_undo n = (no_print_goals undo (); repeat_undo (n - 1));


(* restart top-level loop (keeps most state information) *)

local

fun restart isar =
 (if isar then tell_clear_goals () else kill_goal ();
  tell_clear_response ();
  welcome ());

in

fun isa_restart () = restart false;
fun isar_restart () = (sync_thy_loader (); restart true; raise Toplevel.RESTART);

end;


fun full_proofs true = proofs := 2
  | full_proofs false = proofs := 1;


(* outer syntax *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

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
 [undoP, restartP, kill_proofP, context_thy_onlyP, try_context_thy_onlyP,
  inform_file_processedP, inform_file_retractedP];

end;


(* init *)

val initialized = ref false;

fun init isar =
 (conditional (not (! initialized)) (fn () =>
   (if isar then setmp warning_fn (K ()) init_outer_syntax () else ();
    setup_xsymbols_output ();
    setup_messages ();
    setup_state ();
    setup_thy_loader ();
    setup_present_hook ();
    set initialized; ()));
  sync_thy_loader ();
  print_mode := proof_generalN :: (! print_mode \ proof_generalN);
  set quick_and_dirty;
  ThmDeps.enable ();
  if isar then ml_prompts "ML> " "ML# "
  else ml_prompts ("> " ^ oct_char "372") ("- " ^ oct_char "373");
  if isar then (welcome (); Isar.sync_main ()) else isa_restart ());



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
  \;; This file was generated by " ^ Session.name () ^ " -- DO NOT EDIT!\n\
  \;;\n\
  \;; $" ^ "Id$\n\
  \;;\n" ^
  defconst "major" (map #1 commands) ^
  defconst "minor" (filter Syntax.is_ascii_identifier keywords) ^
  implode (map (make_elisp_commands commands) OuterSyntax.Keyword.kinds) ^
  "\n(provide 'isar-keywords)\n";

in

fun write_keywords s =
  (init_outer_syntax ();
    File.write (Path.unpack ("isar-keywords" ^ (if s = "" then "" else "-" ^ s) ^".el"))
      (make_elisp_syntax (OuterSyntax.dest_keywords (), OuterSyntax.dest_parsers ())));

end;


end;

(*a hack for Proof General 3.2 to avoid problems with escapes in ML commands*)
infix \\\\ val op \\\\ = op \\;
