(*  Title:      Pure/proof_general.ML
    ID:         $Id$
    Author:     David Aspinall and Markus Wenzel

Isabelle configuration for Proof General (see
http://proofgeneral.inf.ed.ac.uk).  Also includes experimental support
for PGIP control language for Isabelle/Isar (PGIP 2.X).
*)

signature PROOF_GENERAL =
sig
  val update_thy_only: string -> unit
  val try_update_thy_only: string -> unit
  val inform_file_retracted: string -> unit
  val inform_file_processed: string -> unit
  val preferences:
      (string *
        (string *
         (string *
          (string * (string * (unit -> string)) *
           (string -> unit)))) list) list ref
  val process_pgip: string -> unit
  val thms_containing: string list -> unit
  val help: unit -> unit
  val show_context: unit -> theory
  val kill_goal: unit -> unit
  val repeat_undo: int -> unit
  val isa_restart: unit -> unit
  val full_proofs: bool -> unit
  val isarcmd: string -> unit
  val init: bool -> unit
  val init_pgip: bool -> unit
  val write_keywords: string -> unit
  val xmls_of_str: string -> string list   (*temp for testing parser*)
end;

structure ProofGeneral: PROOF_GENERAL =
struct

structure P = OuterParse;


(* PGIP messaging mode (independent of PGML output) *)

val pgip_active = ref false;
val pgip_emacs_compatibility_flag = ref false;

fun pgip () = (! pgip_active);
fun pgip_emacs_compatibility () = (! pgip_emacs_compatibility_flag);


(* print modes *)

val proof_generalN = "ProofGeneral";  (*token markup (colouring vars, etc.)*)
val pgasciiN = "PGASCII";             (*plain 7-bit ASCII communication*)
val xsymbolsN = Symbol.xsymbolsN;     (*X-Symbol symbols*)
val pgmlN = "PGML";                   (*XML escapes and PGML symbol elements*)
val pgmlatomsN = "PGMLatoms";         (*variable kind decorations*)
val thm_depsN = "thm_deps";           (*meta-information about theorem deps*)

fun pgml () = Output.has_mode pgmlN;

fun special oct =
  if Output.has_mode pgasciiN then chr 1 ^ chr (ord (oct_char oct) - 167)
  else oct_char oct;


(* text output: print modes for xsymbol and PGML *)

local

fun xsym_output "\\" = "\\\\"
  | xsym_output s = if Symbol.is_raw s then Symbol.decode_raw s else s;

fun xsymbols_output s =
  if Output.has_mode xsymbolsN andalso exists_string (equal "\\") s then
    let val syms = Symbol.explode s
    in (implode (map xsym_output syms), real (Symbol.length syms)) end
  else Symbol.default_output s;

fun pgml_sym s =
  (case Symbol.decode s of
    (*NB: an alternative here would be to output the default print mode alternative
      in the element content, but unfortunately print modes are not that fine grained.*)
    Symbol.Char s => XML.text s
  | Symbol.Sym sn => XML.element "sym" [("name", sn)] [XML.text s]
  | Symbol.Ctrl sn => XML.element "ctrl" [("name", sn)] [XML.text s] (* FIXME: no such PGML! *)
  | Symbol.Raw s => s);

fun pgml_output str =
  let val syms = Symbol.explode str
  in (implode (map pgml_sym syms), real (Symbol.length syms)) end;

in

fun setup_xsymbols_output () =
  Output.add_mode xsymbolsN
    (xsymbols_output, Symbol.default_indent, Symbol.encode_raw);

fun setup_pgml_output () =
  Output.add_mode pgmlN
    (pgml_output, Symbol.default_indent, Symbol.encode_raw);

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
 (if Output.has_mode pgmlatomsN then xml_atom kind x
  else bg_tag () ^ x ^ end_tag (), real (Symbol.length (Symbol.explode x)));

fun free_or_skolem x =
  (case try Syntax.dest_skolem x of
    NONE => tagit free_tag x
  | SOME x' => tagit skolem_tag x');

fun var_or_skolem s =
  (case Syntax.read_variable s of
    SOME (x, i) =>
      (case try Syntax.dest_skolem x of
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

val _ = Context.add_setup [Theory.add_tokentrfuns proof_general_trans];

end;


(* assembling PGIP packets *)

val pgip_refid  = ref NONE: string option ref;
val pgip_refseq = ref NONE: string option ref;

local
  val pgip_class  = "pg"
  val pgip_tag = "Isabelle/Isar"
  val pgip_id = ref ""
  val pgip_seq = ref 0
  fun pgip_serial () = inc pgip_seq

  fun assemble_pgips pgips =
    XML.element
      "pgip"
      ([("tag",    pgip_tag),
        ("class",  pgip_class),
        ("seq",    string_of_int (pgip_serial())),
        ("id",     !pgip_id)] @
       if_none (Option.map (single o (pair "destid")) (! pgip_refid)) [] @
       (* destid=refid since Isabelle only communicates back to sender,
          so we may omit refid from attributes.
       if_none (Option.map (single o (pair "refid"))  (! pgip_refid)) [] @
       *)
       if_none (Option.map (single o (pair "refseq")) (! pgip_refseq)) [])
      pgips;

in

fun init_pgip_session_id () =
    pgip_id := getenv "HOSTNAME" ^ "/" ^ getenv "USER" ^ "/" ^
               getenv "ISABELLE_PID" ^ "/" ^ Time.toString (Time.now ())


fun matching_pgip_id id = (id = !pgip_id)

fun decorated_output bg en prfx =
  writeln_default o enclose bg en o prefix_lines prfx;

(* FIXME: see Rev 1.48 [PG CVS] for cleaner version of this which can be used
   for PG 4.0 which processes PGIP without needing special chars *)
fun issue_pgips ps =
  if pgip_emacs_compatibility() then
    decorated_output (*add urgent message annotation*)
      (special "360") (special "361") ""
      (assemble_pgips ps)
  else
    writeln_default (assemble_pgips ps);

fun assemble_pgip resp attrs s = assemble_pgips [XML.element resp attrs [s]];
fun assemble_pgipe resp attrs = assemble_pgips [XML.element resp attrs []];

(* FIXME: need to add stuff to gather PGIPs here *)
fun issue_pgip resp attrs txt =
  if pgip_emacs_compatibility () then
    decorated_output (*add urgent message annotation*)
      (special "360") (special "361") ""
      (assemble_pgip resp attrs txt)
  else
    writeln_default (assemble_pgip resp attrs txt);

(* FIXME: temporarily to support PG 3.4 *)
fun issue_pgip_maybe_decorated bg en resp attrs s =
  if pgip_emacs_compatibility () then
    (*in PGIP mode, but using escape characters as well*)
    writeln_default (enclose bg en (assemble_pgip resp attrs s))
  else
    issue_pgip resp attrs s;

fun issue_pgipe resp attrs = writeln_default (assemble_pgipe resp attrs);

end;


(* messages and notification *)

local
  val delay_msgs = ref false;   (*true: accumulate messages*)
  val delayed_msgs = ref [];
in

fun message resp attrs bg en prfx s =
  if pgip () then
   (if (! delay_msgs) then
      delayed_msgs := (resp, attrs, prefix_lines prfx s) :: ! delayed_msgs (*NB: no decs*)
    else
      issue_pgip_maybe_decorated bg en resp attrs
        (XML.element "pgmltext" [] [prefix_lines prfx s]))
  else decorated_output bg en prfx s;

fun start_delay_msgs () = (set delay_msgs; delayed_msgs := []);

fun end_delayed_msgs () = (reset delay_msgs;
  (! delayed_msgs) |> map (fn (resp, attrs, s) =>
    XML.element resp attrs [XML.element "pgmltext" [] [s]]));

end;

local
  val display_area = ("area", "display");
  val message_area = ("area", "message");
  val internal_category = ("messagecategory", "internal");
  val info_category = ("messagecategory", "information");
  val tracing_category = ("messagecategory", "tracing");
  val urgent_indication = ("urgent", "y");
  val nonfatal = ("fatality", "nonfatal");
  val fatal = ("fatality", "fatal");
  val panic = ("fatality", "panic");

  val thyname_attr = pair "thyname";
  val url_attr = pair "url";
  fun localfile_url_attr path = url_attr ("file:///" ^ path);
in

fun setup_messages () =
 (writeln_fn := (fn s => message "normalresponse" [message_area] "" "" "" s);
  priority_fn := (fn s => message "normalresponse" [message_area, urgent_indication]
    (special "360") (special "361") "" s);
  tracing_fn := (fn s => message "normalresponse"  [message_area, tracing_category]
    (special "360" ^ special "375") (special "361") "" s);
  info_fn := (fn s => message "normalresponse" [message_area, info_category]
    (special "362") (special "363") "+++ " s);
  debug_fn := (fn s => message "normalresponse" [message_area, internal_category]
    (special "362") (special "363") "+++ " s);
  warning_fn := (fn s => message "errorresponse" [nonfatal]
    (special "362") (special "363") "### " s);
  error_fn := (fn s => message "errorresponse" [fatal]
    (special "364") (special "365") "*** " s);
  panic_fn := (fn s => message "errorresponse" [panic]
    (special "364") (special "365") "!!! " s));


(* accumulate printed output in a single PGIP response (inside <pgmltext>) *)

fun with_displaywrap (elt, attrs) dispfn =
  let
    val lines = ref ([]: string list);
    fun wlgrablines s = lines := s :: ! lines;
  in
    setmp writeln_fn wlgrablines dispfn ();
    (* IMPORTANT FIXME: XML.element here too inefficient, should use stream output *)
    issue_pgip elt attrs (XML.element "pgmltext" [] (! lines))
  end;

fun emacs_notify s = decorated_output (special "360") (special "361") "" s;

fun tell_clear_goals () =
  if pgip () then
    issue_pgipe "cleardisplay" [display_area]
  else
    emacs_notify "Proof General, please clear the goals buffer.";

fun tell_clear_response () =
  if pgip () then
    issue_pgipe "cleardisplay" [message_area]
  else
    emacs_notify "Proof General, please clear the response buffer.";

fun tell_file_loaded path =
  if pgip () then
    issue_pgipe "informfileloaded"
      [localfile_url_attr  (XML.text (File.platform_path path))]
  else
    emacs_notify ("Proof General, this file is loaded: " ^ quote (File.platform_path path));

fun tell_file_retracted path =
  if pgip() then
    issue_pgipe "informfileretracted"
      [localfile_url_attr  (XML.text (File.platform_path path))]
  else
    emacs_notify ("Proof General, you can unlock the file " ^ quote (File.platform_path path));


(* theory / proof state output *)

local

fun tmp_markers f =
  setmp Display.current_goals_markers (special "366", special "367", "") f ();

fun statedisplay prts =
  issue_pgip "proofstate" []
    (XML.element "pgml" []
      [XML.element "statedisplay" [] [Pretty.output (Pretty.chunks prts)]]);

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
   (* FIXME: check next octal char won't appear in pgip? *)
   Toplevel.prompt_state_fn := (fn s => suffix (special "372")
     (Toplevel.prompt_state_default s)));

end;

end;


(* misc commands for ProofGeneral/isa *)

fun thms_containing ss =
  FindTheorems.print_theorems (ProofContext.init (the_context ())) NONE NONE
    (map (fn s => (true, FindTheorems.Pattern s)) ss);

val welcome = priority o Session.welcome;
val help = welcome;
val show_context = Context.the_context;

fun kill_goal () = (Goals.reset_goals (); tell_clear_goals ());

fun no_print_goals f = setmp Display.print_current_goals_fn (fn _ => fn _ => fn _ => ()) f;

fun repeat_undo 0 = ()
  | repeat_undo 1 = undo ()
  | repeat_undo n = (no_print_goals undo (); repeat_undo (n - 1));


(* theory loader actions *)

local

fun add_master_files name files =
  let val masters = [ThyLoad.thy_path name, ThyLoad.ml_path name]
  in masters @ gen_rems (op = o pairself Path.base) (files, masters) end;

fun trace_action action name =
  if action = ThyInfo.Update then
    List.app tell_file_loaded (ThyInfo.loaded_files name)
  else if action = ThyInfo.Outdate orelse action = ThyInfo.Remove then
    List.app tell_file_retracted (add_master_files name (ThyInfo.loaded_files name))
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
      transform_error ThyInfo.pretend_use_thy_only name handle ERROR_MESSAGE msg =>
       (warning msg; warning ("Failed to register theory: " ^ quote name);
        tell_file_retracted (Path.base (Path.unpack file))))
    else raise Toplevel.UNDEF
  end;

fun vacuous_inform_file_processed file state =
 (warning ("No theory " ^ quote (thy_name file));
  tell_file_retracted (Path.base (Path.unpack file)));


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


(* theorem dependency output *)

local

val spaces_quote = space_implode " " o map quote;

(* FIXME: investigate why dependencies at the moment include themselves! *)
fun thm_deps_message (thms, deps) =
  if pgip() then
    issue_pgips
      [XML.element
        "metainforesponse"  (* FIXME: get thy name from info here? *)
        [("infotype", "isabelle_theorem_dependencies")]
        [XML.element "value" [("name", "thms")] [XML.text thms],
         XML.element "value" [("name", "deps")] [XML.text deps]]]
  else emacs_notify ("Proof General, theorem dependencies of " ^ thms ^ " are " ^ deps);

fun tell_thm_deps ths = conditional (Output.has_mode thm_depsN) (fn () =>
  let
    val names = filter_out (equal "") (map Thm.name_of_thm ths);
    val deps = filter_out (equal "")
      (Symtab.keys (fold Proofterm.thms_of_proof
        (map Thm.proof_of ths) Symtab.empty));
  in
    if null names orelse null deps then ()
    else thm_deps_message (spaces_quote names, spaces_quote deps)
  end);

in

fun setup_present_hook () =
  Present.add_hook (fn _ => fn res => tell_thm_deps (List.concat (map #2 res)));

end;



(** preferences **)

local

val pgipnat = XML.element "pgipint" [("min", "0")] [];
fun pgipnatmax max = XML.element "pgipint" [("min", "0"), ("max", string_of_int max)] [];
val pgipbool = XML.element "pgipbool" [] [];

fun with_default f = (f (), f);

in

fun nat_option r = (pgipnat,
  with_default (fn () => string_of_int (! r)),
  (fn s => (case Syntax.read_nat s of
      NONE => error ("nat_option: illegal value: " ^ s)
    | SOME i => r := i)));

fun bool_option r = (pgipbool,
  with_default (fn () => Bool.toString (! r)),
  (fn "false" => r := false | "true" => r := true
    | x => error ("bool_option: illegal value: " ^ x)));

val proof_option = (pgipbool,
  with_default (fn () => Bool.toString (! proofs >= 2)),
  (fn "false" => proofs := 1 | "true" => proofs := 2
    | x => error ("proof_option: illegal value: " ^ x)));

val thm_deps_option = (pgipbool,
  with_default (fn () => Bool.toString (Output.has_mode thm_depsN)),
  (fn "false" => change print_mode (remove (op =) thm_depsN)
    | "true" => change print_mode (insert (op =) thm_depsN)
    | x => error ("thm_deps_option: illegal value: " ^ x)));

local
  val pg_print_depth_val = ref 10;
  fun pg_print_depth n = (print_depth n; pg_print_depth_val := n)
in

val print_depth_option = (pgipnat,
  with_default (fn () => string_of_int (! pg_print_depth_val)),
  (fn s => (case Syntax.read_nat s of
      NONE => error ("print_depth_option: illegal value: " ^ s)
    | SOME i => pg_print_depth i)));
end;

val preferences = ref
  [("Display",
    [("show-types",
      ("Include types in display of Isabelle terms",
       bool_option show_types)),
     ("show-sorts",
      ("Include sorts in display of Isabelle terms",
       bool_option show_sorts)),
     ("show-consts",
      ("Show types of consts in Isabelle goal display",
       bool_option show_consts)),
     ("long-names",
      ("Show fully qualified names in Isabelle terms",
       bool_option long_names)),
     ("show-brackets",
      ("Show full bracketing in Isabelle terms",
       bool_option show_brackets)),
     ("show-main-goal",
      ("Show main goal in proof state display",
       bool_option Proof.show_main_goal)),
     ("show-sort-hypotheses",
      ("Include sort hypotheses in display of Isabelle theorems",
       bool_option show_hyps)),
     ("eta-contract",
      ("Print terms eta-contracted",
       bool_option Syntax.eta_contract))]),
   ("Advanced Display",
    [("goals-limit",
      ("Setting for maximum number of goals printed",
       nat_option goals_limit)),
     ("prems-limit",
      ("Setting for maximum number of premises printed",
       nat_option ProofContext.prems_limit)),
     ("print-depth",
      ("Setting for the ML print depth",
       print_depth_option)),
     ("show-question-marks",
      ("Show leading question mark of variable name",
       bool_option show_question_marks))]),
   ("Tracing",
    [("trace-simplifier",
      ("Trace simplification rules.",
       bool_option trace_simp)),
     ("trace-simplifier-depth",
      ("Trace simplifier depth limit.",
       nat_option trace_simp_depth_limit)),
     ("trace-rules",
      ("Trace application of the standard rules",
       bool_option trace_rules)),
     ("trace-unification",
      ("Output error diagnostics during unification",
       bool_option Pattern.trace_unify_fail)),
     ("global-timing",
      ("Whether to enable timing in Isabelle.",
       bool_option Output.timing))]),
   ("Proof",
    [("quick-and-dirty",
      ("Take a few short cuts",
       bool_option quick_and_dirty)),
     ("full-proofs",
      ("Record full proof objects internally",
       proof_option)),
     ("theorem-dependencies",
       ("Track theorem dependencies within Proof General",
        thm_deps_option)),
     ("skip-proofs",
      ("Ignore proof scripts (interactive-only)",
       bool_option Toplevel.skip_proofs))])
   ];
end;


(* Configuration: GUI config, proverinfo messages *)

local
    val config_file = "~~/lib/ProofGeneral/pgip_isar.xml"
    val name_attr = pair "name"
    val version_attr = pair "version"
    val isabelle_www = "http://isabelle.in.tum.de/"
in
fun send_pgip_config () =
    let
        val path = Path.unpack config_file
        val exists = File.exists path
        val proverinfo =
            XML.element "proverinfo"
              [("name",Session.name()), ("version", version),
               ("url", isabelle_www), ("filenameextns", ".thy;")]
            [XML.element "welcomemsg" [] [XML.text (Session.welcome())],
             XML.element "helpdoc"
         (* NB: would be nice to generate/display docs from isatool
          doc, but that program may not be running on same machine;
          front end should be responsible for launching viewer, etc. *)
                      [("name", "Isabelle/HOL Tutorial"),
                       ("descr", "A Gentle Introduction to Isabelle/HOL"),
                       ("url",  "http://isabelle.in.tum.de/dist/Isabelle2004/doc/tutorial.pdf")]
              []]
    in
        if exists then
            (issue_pgips [proverinfo]; issue_pgips [File.read path])
        else panic ("PGIP configuration file " ^ config_file ^ " not found")
    end;
end


(* Reveal some information about prover state *)
fun send_informguise (openfile, opentheory, openproofpos) =
    let val guisefile =
            case openfile of SOME f => [XML.element "guisefile"
                                                    [("url",Url.pack (Url.File (Path.unpack f)))] []]
                           | _ => []
        val guisetheory =
            case opentheory of SOME t => [XML.element "guisetheory" [("thyname", t)] []]
                             | _ => []
        val guiseproof =
            case openproofpos of SOME i => [XML.element "guiseproof" [("proofpos", string_of_int i)] []]
                               | _ => []
    in
        issue_pgips [XML.element "informguise" [] (guisefile @ guisetheory @ guiseproof)]
    end


(* PGIP identifier tables (prover objects). [incomplete] *)

local
    val objtype_thy  = "theory"
    val objtype_thm  = "theorem"
    val objtype_term = "term"
    val objtype_type = "type"

    fun xml_idtable ty ctx ids =
        let
            fun ctx_attr (SOME c)= [("context", c)]
              | ctx_attr NONE    = []
            fun xmlid x = XML.element "identifier" [] [XML.text x];
        in
            XML.element "idtable" (("objtype", ty)::ctx_attr ctx)
                                  (map xmlid ids)
        end
in

fun setids t = issue_pgip "setids" [] t
fun addids t = issue_pgip "addids" [] t
fun delids t = issue_pgip "delids" [] t

fun delallids ty = setids (xml_idtable ty NONE [])

fun send_thy_idtable ctx thys = setids (xml_idtable objtype_thy ctx thys)
fun clear_thy_idtable () = delallids objtype_thy

fun send_thm_idtable ctx thy =
    addids (xml_idtable objtype_thm ctx (map fst (PureThy.thms_of thy)));

fun clear_thm_idtable () = delallids objtype_thm

(* fun send_type_idtable thy = TODO, it's a bit low-level messy
   & maybe not so useful anyway *)

end

(* Response to interface queries about known objects *)

local
 val topthy = Toplevel.theory_of o Toplevel.get_state
 fun pthm thy name = print_thm (get_thm thy (Name name))

 fun idvalue tp nm = ("idvalue",[("objtype",tp),("name",nm)])
in
(* FIXME: add askids for "file" here, which returns single theory with same name *)
fun askids (NONE, SOME "theory")  = send_thy_idtable NONE (ThyInfo.names())
  | askids (NONE, NONE) =  send_thy_idtable NONE (ThyInfo.names())
                           (* only theories known in top context *)
  | askids (SOME thy, SOME "theory") = send_thy_idtable (SOME thy) (ThyInfo.get_preds thy)
  | askids (SOME thy, SOME "theorem") = send_thm_idtable (SOME thy) (ThyInfo.get_theory thy)
  | askids (SOME thy, NONE) = (send_thy_idtable (SOME thy) (ThyInfo.get_preds thy);
                               send_thm_idtable (SOME thy) (ThyInfo.get_theory thy))
  | askids (_, SOME ot) = error ("No objects of type "^(quote ot)^" are available here.")

fun showid (_,        "theory", n) =
    with_displaywrap (idvalue "theory" n) (fn ()=>(print_theory (ThyInfo.get_theory n)))
  | showid (SOME thy, "theorem", t) =
    with_displaywrap (idvalue "theorem" t) (fn ()=>(pthm (ThyInfo.get_theory thy) t))
  | showid (NONE,     "theorem", t) =
    with_displaywrap (idvalue "theorem" t) (fn ()=>pthm (topthy()) t)
  | showid (_, ot, _) = error ("Cannot show objects of type "^ot)

end


(** Parsing proof scripts without execution **)

(* Notes.
   This is quite tricky, because 1) we need to put back whitespace which
   was removed during parsing so we can provide markup around commands;
   2) parsing is intertwined with execution in Isar so we have to repeat
   the parsing to extract interesting parts of commands.  The trace of
   tokens parsed which is now recorded in each transition (added by
   Markus June '04) helps do this, but the mechanism is still a bad mess.

   If we had proper parse trees it would be easy, although having a
   fixed type of trees might be tricky with Isar's extensible parser.

   Probably the best solution is to produce the meta-information at
   the same time as the parse, for each command, e.g. by recording a
   list of (name,objtype) pairs which record the bindings created by
   a command.  This would require changing the interfaces in
   outer_syntax.ML (or providing new ones),

    datatype metainfo = Binding of string * string  (* name, objtype *)

    val command_withmetainfo: string -> string -> string ->
      (token list ->
       ((Toplevel.transition -> Toplevel.transition) * metainfo list) *
       token list) -> parser

   We'd also like to render terms as they appear in output, but this
   will be difficult because inner syntax is extensible and we don't
   have the correct syntax to hand when just doing outer parsing
   without execution.  A reasonable approximation could
   perhaps be obtained by using the syntax of the current context.
   However, this would mean more mess trying to pick out terms,
   so at this stage a more serious change to the Isar functions
   seems necessary.
*)

local
    fun markup_text str elt = [XML.element elt [] [XML.text str]]
    fun markup_text_attrs str elt attrs = [XML.element elt attrs [XML.text str]]
    fun empty elt = [XML.element elt [] []]

    fun whitespace str = XML.element "whitespace" [] [XML.text str]

    (* an extra token is needed to terminate the command *)
    val sync = OuterSyntax.scan "\\<^sync>";

    fun named_item_elt_with nameattr toks str elt nameP objtyp =
        let
            val name = (fst (nameP (toks@sync)))
                        handle _ => (error ("Error occurred in name parser for " ^ elt ^
                                            "(objtype: " ^ objtyp ^ ")");
                                     "")

        in
            [XML.element elt
                         ((if name="" then [] else [(nameattr, name)])@
                          (if objtyp="" then [] else [("objtype", objtyp)]))
                         ([XML.text str])]
        end

    val named_item_elt = named_item_elt_with "name"
    val thmnamed_item_elt = named_item_elt_with "thmname"

    fun parse_warning msg = warning ("script->PGIP markup parser: " ^ msg)

    (* FIXME: allow dynamic extensions to language here: we need a hook in
       outer_syntax.ML to reset this table. *)

    val keywords_classification_table = ref (NONE: string Symtab.table option)

    fun get_keywords_classification_table () =
        case (!keywords_classification_table) of
          SOME t => t
        | NONE => (let
                     val tab = fold (fn (c, _, k, _) => Symtab.update (c, k))
                                    (OuterSyntax.dest_parsers ()) Symtab.empty;
                   in (keywords_classification_table := SOME tab; tab) end)



    fun xmls_of_thy_begin (name,toks,str) = (* see isar_syn.ML/theoryP *)
        let
            val ((thyname,imports,files),_) = ThyHeader.args (toks@sync)
        in
            markup_text_attrs str "opentheory"
                              ([("thyname",thyname)] @
                               (if imports=[] then [] else
                                [("parentnames", (space_implode ";" imports) ^ ";")]))
        end

    fun xmls_of_thy_decl (name,toks,str) = (* see isar_syn.ML/thy_decl cases  *)
        let
            (* NB: PGIP only deals with single name bindings at the moment;
               potentially we could markup grouped definitions several times but
               that might suggest the wrong structure to the editor?
               Better alternative would be to put naming closer around text,
               but to do that we'd be much better off modifying the real parser
               instead of reconstructing it here. *)

            val plain_items = (* no names, unimportant names, or too difficult *)
                ["defaultsort","arities","judgement","finalconsts",
                 "syntax", "nonterminals", "translations",
                 "global", "local", "hide",
                 "ML_setup", "setup", "method_setup",
                 "parse_ast_translation", "parse_translation", "print_translation",
                 "typed_print_translation", "print_ast_translation", "token_translation",
                 "oracle",
                 "declare"]

            val plain_item   = markup_text str "theoryitem"
            val comment_item = markup_text str "litcomment"
            val named_item   = named_item_elt toks str "theoryitem"

            val opt_overloaded = P.opt_keyword "overloaded";

            val thmnameP = (* see isar_syn.ML/theoremsP *)
                let
                    val name_facts = P.and_list1 ((P.opt_thm_name "=" --| P.xthms1) >> #1)
                    val theoremsP = P.opt_locale_target |-- name_facts >> (fn [] => "" | x::_ => x)
                in
                    theoremsP
                end
        in
            (* TODO: ideally we would like to render terms properly, just as they are
               in output. This implies using PGML for symbols and variables/atoms.
               BUT it's rather tricky without having the correct concrete syntax to hand,
               and even if we did, we'd have to mess around here a whole lot more first
               to pick out the terms from the syntax. *)

            if (name mem plain_items) then plain_item
            else case name of
                     "text"      => comment_item
                   | "text_raw"  => comment_item
                   | "typedecl"  => named_item (P.type_args |-- P.name) "type"
                   | "types"     => named_item (P.type_args |-- P.name) "type"
                   | "classes"   => named_item P.name "class"
                   | "classrel"  => named_item P.name "class"
                   | "consts"    => named_item (P.const >> #1) "term"
                   | "axioms"    => named_item (P.spec_name >> (#1 o #1)) "theorem"
                   | "defs"      => named_item (opt_overloaded |-- P.spec_name >> (#1 o #1)) "theorem"
                   | "constdefs" => named_item P.name (* FIXME: heavily simplified/wrong *) "term"
                   | "theorems"  => named_item thmnameP "thmset"
                   | "lemmas"    => named_item thmnameP "thmset"
                   | "oracle"    => named_item P.name "oracle"
                   | "locale"    => named_item ((P.opt_keyword "open" >> not) |-- P.name) "locale"
                   | _ => (parse_warning ("Unrecognized thy-decl command: " ^ name); plain_item)
        end

    fun xmls_of_thy_goal (name,toks,str) =
        let
            (* see isar_syn.ML/gen_theorem *)
         val statement = P.and_list1 (P.opt_thm_name ":" -- Scan.repeat1 P.propp);
         val general_statement =
            statement >> pair [] || Scan.repeat P.locale_elem_or_expr -- (P.$$$ "shows" |-- statement);

            val gen_theoremP =
                P.opt_locale_target -- Scan.optional (P.opt_thm_name ":" --|
                 Scan.ahead (P.locale_keyword || P.$$$ "shows")) ("", []) --
                                 general_statement >> (fn ((locale, a), (elems, concl)) =>
                                                         fst a) (* a : (bstring * Args.src list) *)

            val nameP = P.opt_locale_target |-- (Scan.optional ((P.opt_thm_name ":") >> #1) "")
            (* TODO: add preference values for attributes
               val prefval = XML.element "prefval" [("name","thm-kind"),("value",name)]
            *)
        in
            (thmnamed_item_elt toks str "opengoal" nameP "") @
            (empty "openblock")
        end

    fun xmls_of_qed (name,markup) =
        let val qedmarkup  =
                (case name of
                     "sorry" => markup "postponegoal"
                   | "oops"  => markup "giveupgoal"
                   | "done"  => markup "closegoal"
                   | "by"    => markup "closegoal"  (* nested or toplevel *)
                   | "qed"   => markup "closegoal"  (* nested or toplevel *)
                   | "."     => markup "closegoal"  (* nested or toplevel *)
                   | ".."    => markup "closegoal"  (* nested or toplevel *)
                   | other => (* default to closegoal: may be wrong for extns *)
                                  (parse_warning
                                       ("Unrecognized qed command: " ^ quote other);
                                       markup "closegoal"))
        in qedmarkup @ (empty "closeblock") end

    fun xmls_of_kind kind (name,toks,str) =
    let val markup = markup_text str in
    case kind of
      "control"        => markup "badcmd"
    | "diag"           => markup "spuriouscmd"
    (* theory/files *)
    | "theory-begin"   => xmls_of_thy_begin (name,toks,str)
    | "theory-decl"    => xmls_of_thy_decl (name,toks,str)
    | "theory-heading" => markup "litcomment"
    | "theory-script"  => markup "theorystep"
    | "theory-end"     => markup "closetheory"
    (* proof control *)
    | "theory-goal"    => xmls_of_thy_goal (name,toks,str)
    | "proof-heading"  => markup "litcomment"
    | "proof-goal"     => (markup "opengoal") @ (empty "openblock")  (* nested proof: have, show, ... *)
    | "proof-block"    => markup "proofstep" (* context-shift: proof, next; really "newgoal" *)
    | "proof-open"     => (empty "openblock") @ (markup "proofstep")
    | "proof-close"    => (markup "proofstep") @ (empty "closeblock")
    | "proof-script"   => markup "proofstep"
    | "proof-chain"    => markup "proofstep"
    | "proof-decl"     => markup "proofstep"
    | "proof-asm"      => markup "proofstep"
    | "proof-asm-goal" => (markup "opengoal") @ (empty "openblock")  (* nested proof: obtain *)
    | "qed"            => xmls_of_qed (name,markup)
    | "qed-block"      => xmls_of_qed (name,markup)
    | "qed-global"     => xmls_of_qed (name,markup)
    | other => (* default for anything else is "spuriouscmd", ignored for undo. *)
      (parse_warning ("Internal inconsistency, unrecognized keyword kind: " ^ quote other);
       markup "spuriouscmd")
    end
in

fun xmls_of_transition (name,str,toks) =
   let
     val classification = Symtab.lookup (get_keywords_classification_table ()) name
   in case classification of
          SOME k => (xmls_of_kind k (name,toks,str))
        | NONE => (* an uncategorized keyword ignored for undo (maybe wrong) *)
          (parse_warning ("Uncategorized command found: " ^ name ^ " -- using spuriouscmd");
           markup_text str "spuriouscmd")
   end

fun markup_toks [] _ = []
  | markup_toks toks x = markup_text (implode (map OuterLex.unparse toks)) x

fun markup_comment_whs [] = []
  | markup_comment_whs (toks as t::ts) = (* this would be a lot neater if we could match on toks! *)
    let
        val (prewhs,rest) = take_prefix (OuterLex.is_kind OuterLex.Space) toks
    in
        if (prewhs <> []) then
            whitespace (implode (map OuterLex.unparse prewhs))
            :: (markup_comment_whs rest)
        else
            (markup_text (OuterLex.unparse t) "comment") @
            (markup_comment_whs ts)
    end

fun xmls_pre_cmd [] = ([],[])
  | xmls_pre_cmd toks =
    let
        (* an extra token is needed to terminate the command *)
        val sync = OuterSyntax.scan "\\<^sync>";
        val spaceP = Scan.bulk (Scan.one (fn t =>not (OuterLex.is_proper t)) >> OuterLex.val_of) >> implode
        val text_with_whs =
            ((spaceP || Scan.succeed "") --
             (P.short_ident || P.long_ident || P.sym_ident || P.string || P.number || P.verbatim) >> op^)
             -- (spaceP || Scan.succeed "") >> op^
        val (prewhs,rest1) = take_prefix (not o OuterLex.is_proper) (toks@sync)
        (* NB: this collapses  litcomment,(litcomment|whitespace)* to a single litcomment *)
        val (_,rest2) = (Scan.bulk (P.$$$ "--" |-- text_with_whs) >> implode || Scan.succeed "") rest1
        val (postwhs,rest3) = take_prefix (not o OuterLex.is_proper) rest2
    in
        ((markup_comment_whs prewhs) @
         (if (length rest2 = length rest1)  then []
          else markup_text (implode
                                (map OuterLex.unparse (Library.take (length rest1 - length rest2, rest1))))
               "litcomment") @
         (markup_comment_whs postwhs),
         Library.take (length rest3 - 1,rest3))
    end

fun xmls_of_impropers toks =
    let
        val (xmls,rest) = xmls_pre_cmd toks
    in
        xmls @ (markup_toks rest "unparseable")
    end

fun markup_unparseable str = markup_text str "unparseable"

end


local
    (* we have to weave together the whitespace/comments with proper tokens
       to reconstruct the input. *)
    (* TODO: see if duplicating isar_output/parse_thy can help here *)

    fun match_tokens ([],us,vs) = (rev vs,us)  (* used, unused *)
      | match_tokens (t::ts,w::ws,vs) =
        if (t = w) then match_tokens (ts,ws,w::vs)
        else match_tokens (t::ts,ws,w::vs)
      | match_tokens _ = error ("match_tokens: mismatched input parse")
in
    fun xmls_of_str str =
    let
       (* parsing:   See outer_syntax.ML/toplevel_source *)
       fun parse_loop ([],[],xmls) = xmls
         | parse_loop ([],itoks,xmls) = xmls @ (xmls_of_impropers itoks)
         | parse_loop ((nm,toks,_)::trs,itoks,xmls) =
           let
               (* first proper token after whitespace/litcomment/whitespace is command *)
               val (xmls_pre_cmd,cmditoks') = xmls_pre_cmd itoks
               val (cmdtok,itoks') = case cmditoks' of x::xs => (x,xs)
                                                     | _ => error("proof_general/parse_loop impossible")
               val (utoks,itoks'') = match_tokens (toks,itoks',[])
               (* FIXME: should take trailing [w/s+] semicolon too in utoks *)

               val str = implode (map OuterLex.unparse (cmdtok::utoks))

               val xmls_tr  = xmls_of_transition (nm,str,toks)
           in
               parse_loop(trs,itoks'',xmls @ xmls_pre_cmd @ xmls_tr)
           end
    in
        (let val toks = OuterSyntax.scan str
         in
             parse_loop (OuterSyntax.read toks, toks, [])
         end)
           handle _ => markup_unparseable str
    end


fun parsescript str attrs =
    let
        val _ = start_delay_msgs ()  (* accumulate error messages to put inside parseresult *)
        val xmls = xmls_of_str str
        val errs = end_delayed_msgs ()
     in
        issue_pgips [XML.element "parseresult" attrs (errs@xmls)]
    end
end



(**** PGIP:  Isabelle -> Interface ****)

val isabelle_pgml_version_supported = "1.0";
val isabelle_pgip_version_supported = "2.0"

(* TODO: would be cleaner to define a datatype here for the accepted elements,
   and mapping functions to/from strings.  At the moment this list must
   coincide with the strings in the function process_pgip_element. *)
val isabelle_acceptedpgipelems =
    ["askpgip","askpgml","askprefs","getpref","setpref",
     "proverinit","proverexit","startquiet","stopquiet",
     "pgmlsymbolson", "pgmlsymbolsoff",
     "dostep", "undostep", "redostep", "abortgoal", "forget", "restoregoal",
     "askids", "showid", "askguise",
     "parsescript",
     "showproofstate", "showctxt", "searchtheorems", "setlinewidth", "viewdoc",
     "doitem", "undoitem", "redoitem", "abortheory",
     "retracttheory", "loadfile", "openfile", "closefile",
     "abortfile", "changecwd", "systemcmd"];

fun usespgip () =
    issue_pgip
        "usespgip"
        [("version", isabelle_pgip_version_supported)]
        (XML.element "acceptedpgipelems" []
                     (map (fn s=>XML.element "pgipelem"
                                             [] (* if threads: possibility to add async here *)
                                             [s])
                          isabelle_acceptedpgipelems))

fun usespgml () =
    issue_pgipe "usespgml" [("version", isabelle_pgml_version_supported)]

fun hasprefs () =
    List.app (fn (prefcat, prefs) =>
            issue_pgips [XML.element "hasprefs" [("prefcategory",prefcat)]
                 (map (fn (name, (descr, (ty, (default,_),_))) =>
                       XML.element "haspref" [("name", name),
                                              ("descr", descr),
                                              ("default", default)]
                       [ty]) prefs)]) (!preferences)

fun allprefs () = Library.foldl (op @) ([], map snd (!preferences))

fun setpref name value =
    (case AList.lookup (op =) (allprefs ()) name of
         NONE => warning ("Unknown pref: " ^ quote name)
       | SOME (_, (_, _, set)) => set value);

fun getpref name =
    (case AList.lookup (op =) (allprefs ()) name of
         NONE => warning ("Unknown pref: " ^ quote name)
       | SOME (_, (_, (_,get), _)) =>
           issue_pgip "prefval" [("name", name)] (get ()));



(**** PGIP:  Interface -> Isabelle/Isar ****)

exception PGIP of string;
exception PGIP_QUIT;


(* Sending commands to Isar *)

fun isarcmd s =
    s |> OuterSyntax.scan |> OuterSyntax.read
      |> map (Toplevel.position (Position.name "PGIP message") o #3) |> Toplevel.>>>;

fun xmltext ((XML.Text text)::ts) = text ^ (xmltext ts)
  | xmltext [] = ""
  | xmltext _ = raise PGIP "Expected text (PCDATA/CDATA)"

fun isarscript xmls = isarcmd (xmltext xmls)   (* send a script command *)


(* load an arbitrary file (must be .thy or .ML) *)

fun use_thy_or_ml_file file =
    let
        val (path,extn) = Path.split_ext (Path.unpack file)
    in
        case extn of
            "" => isarcmd ("use_thy " ^ (quote (Path.pack path)))
          | "thy" => isarcmd ("use_thy " ^ (quote (Path.pack path)))
          | "ML" => isarcmd ("use " ^ quote file)
          | other => error ("Don't know how to read a file with extension " ^ other)
    end


(* Proof control commands *)

local
  fun xmlattro attr attrs = AList.lookup (op =) attrs attr

  fun xmlattr attr attrs =
      (case xmlattro attr attrs of
           SOME value => value
         | NONE => raise PGIP ("Missing attribute: " ^ attr))

  val thyname_attro = xmlattro "thyname"
  val thyname_attr = xmlattr "thyname"
  val objtype_attro = xmlattro "objtype"
  val objtype_attr = xmlattr "objtype"
  val name_attr = xmlattr "name"
  val dirname_attr = xmlattr "dir"
  fun comment x = "(* " ^ x ^ " *)"

  fun localfile_of_url url = (* only handle file:/// or file://localhost/ *)
      case Url.unpack url of
          (Url.File path) => File.platform_path path
        | _ => error ("Cannot access non-local URL " ^ url)

  val fileurl_of = localfile_of_url o (xmlattr "url")

  val topthy = Toplevel.theory_of o Toplevel.get_state
  val topthy_name = Context.theory_name o topthy

  val currently_open_file = ref (NONE : string option)

  (* Path management: we allow theory files to have dependencies
     in their own directory, but when we change directory for a new
     file we remove the path.  Leaving it there can cause confusion
     with difference in batch mode.a  NB: PGIP does not assume
     that the prover has a load path. *)
  local
      val current_working_dir = ref (NONE : string option)
  in
      fun changecwd dir =
          (case (!current_working_dir) of
               NONE => ()
             | SOME dir => ThyLoad.del_path dir;
           ThyLoad.add_path dir;
           current_working_dir := SOME dir)
  end

  val topnode = Toplevel.node_of o Toplevel.get_state
  fun topproofpos () = (case topnode() of Toplevel.Proof ph => SOME(ProofHistory.position ph)
                                        | _ => NONE) handle Toplevel.UNDEF => NONE
in

fun process_pgip_element pgipxml = (case pgipxml of
  (XML.Text t) => warning ("Ignored text in PGIP packet: \n" ^ t)
| (xml as (XML.Elem (elem, attrs, data))) =>
  (case elem of
       (* protocol config *)
       "askpgip"        => (pgip_emacs_compatibility_flag:=false; (* PG>=3.6 or other PGIP interface *)
                            usespgip (); send_pgip_config ())
     | "askpgml"        => usespgml ()
     (* proverconfig *)
     | "askprefs"       => hasprefs ()
     | "getpref"        => getpref (name_attr attrs)
     | "setpref"        => setpref (name_attr attrs) (xmltext data)
     (* provercontrol *)
     | "proverinit"     => isar_restart ()
     | "proverexit"     => isarcmd "quit"
     | "startquiet"     => isarcmd "disable_pr"
     | "stopquiet"      => isarcmd "enable_pr"
     | "pgmlsymbolson"   => change print_mode (insert (op =) Symbol.xsymbolsN)
     | "pgmlsymbolsoff"  => change print_mode (remove (op =) Symbol.xsymbolsN)
     (* properproofcmd: proper commands which belong in script *)
     (* FIXME: next ten are by Eclipse interface, can be removed in favour of dostep *)
     (* NB: Isar doesn't make lemma name of goal accessible during proof *)
     | "opengoal"       => isarscript data
     | "proofstep"      => isarscript data
     | "closegoal"      => isarscript data
     | "giveupgoal"     => isarscript data
     | "postponegoal"   => isarscript data
     | "comment"        => isarscript data  (* NB: should be ignored, but process anyway *)
     | "whitespace"     => isarscript data  (* NB: should be ignored, but process anyway *)
     | "litcomment"     => isarscript data
     | "spuriouscmd"    => isarscript data
     | "badcmd"         => isarscript data
     (* improperproofcmd: improper commands which *do not* belong in script *)
     | "dostep"         => isarscript data
     | "undostep"       => isarcmd "undos_proof 1"
     | "redostep"       => isarcmd "redo"
     | "abortgoal"      => isarcmd "ProofGeneral.kill_proof"
     | "forget"         => error "Not implemented"
     | "restoregoal"    => error "Not implemented"  (* could just treat as forget? *)
     (* proofctxt: improper commands *)
     | "askids"         => askids (thyname_attro attrs, objtype_attro attrs)
     | "showid"         => showid (thyname_attro attrs, objtype_attr attrs, name_attr attrs)
     | "askguise"       => send_informguise (!currently_open_file,
                                             SOME (topthy_name()) handle Toplevel.UNDEF => NONE,
                                             topproofpos())
     | "parsescript"    => parsescript (xmltext data) attrs (* just pass back attrs unchanged *)
     | "showproofstate" => isarcmd "pr"
     | "showctxt"       => isarcmd "print_theory"   (* more useful than print_context *)
     | "searchtheorems" => isarcmd ("thms_containing " ^ xmltext data)
     | "setlinewidth"   => isarcmd ("pretty_setmargin " ^ xmltext data)
     | "viewdoc"        => isarcmd ("print_" ^ xmltext data) (* FIXME: isatool doc? *)
     (* properfilecmd: proper theory-level script commands *)
     (* FIXME: next three are sent by Eclipse, can be removed in favour of doitem *)
     | "opentheory"     => isarscript data
     | "theoryitem"     => isarscript data
     | "closetheory"    => let
                              val thyname = topthy_name()
                           in (isarscript data;
                               writeln ("Theory " ^ quote thyname ^ " completed."))
                           end
     (* improperfilecmd: theory-level commands not in script *)
     | "doitem"         => isarscript data
     | "undoitem"       => isarcmd "ProofGeneral.undo"
     | "redoitem"       => isarcmd "ProofGeneral.redo"
     | "aborttheory"    => isarcmd ("init_toplevel")
     | "retracttheory"  => isarcmd ("kill_thy " ^ quote (thyname_attr attrs))
     | "loadfile"       => use_thy_or_ml_file (fileurl_of attrs)
     | "openfile"       => (openfile_retract (fileurl_of attrs);
                            currently_open_file := SOME (fileurl_of attrs))
     | "closefile"      => (case !currently_open_file of
                                SOME f => (inform_file_processed f;
                                           currently_open_file := NONE)
                              | NONE => raise PGIP ("closefile when no file is open!"))
     | "abortfile"      => (currently_open_file := NONE) (* perhaps error for no file open *)
     | "changecwd"      => changecwd (dirname_attr attrs)
     | "systemcmd"      => isarscript data
     (* unofficial command for debugging *)
     | "quitpgip" => raise PGIP_QUIT
     | _ => raise PGIP ("Unrecognized PGIP element: " ^ elem)))

fun process_pgip_tree xml =
    (pgip_refid := NONE;
     pgip_refseq := NONE;
     (case xml of
          XML.Elem ("pgip", attrs, pgips) =>
          (let
               val class = xmlattr "class" attrs
               val dest  = xmlattro "destid" attrs
               val _ = (pgip_refid :=  xmlattro "id" attrs;
                        pgip_refseq := xmlattro "seq" attrs)
           in
               (* We respond to broadcast messages to provers, or
                  messages intended uniquely for us.  Silently ignore rest. *)
               case dest of
                   NONE => if (class = "pa") then
                               (List.app process_pgip_element pgips; true)
                           else false
                 | SOME id => if (matching_pgip_id id) then
                                  (List.app process_pgip_element pgips; true)
                              else false
           end)
        | _ => raise PGIP "Invalid PGIP packet received")
     handle (PGIP msg) =>
            (error (msg ^ "\nPGIP error occured in XML text below:\n" ^
                    (XML.string_of_tree xml))))

val process_pgip = K () o process_pgip_tree o XML.tree_of_string

end


(* PGIP loop: process PGIP input only *)

local

exception XML_PARSE

fun loop ready src =
    let
        val _ = if ready then (issue_pgipe "ready" []) else ()
        val pgipo = (Source.get_single src)
                        handle e => raise XML_PARSE
    in
        case pgipo of
             NONE  => ()
           | SOME (pgip,src') =>
             let
                 val ready' = (process_pgip_tree pgip) handle e => (handler (e,SOME src'); true)
             in
                 loop ready' src'
             end
    end handle e => handler (e,SOME src)  (* i.e. error in ready/XML parse *)

and handler (e,srco) =
    case (e,srco) of
        (XML_PARSE,SOME src) =>
        panic "Invalid XML input, aborting" (* NB: loop OK for tty, but want exit on EOF *)
      | (PGIP_QUIT,_) => ()
      | (ERROR,SOME src) => loop true src (* message already given *)
      | (Interrupt,SOME src) => (!error_fn "Interrupt during PGIP processing"; loop true src)
      | (Toplevel.UNDEF,SOME src) => (error "No working context defined"; loop true src) (* usually *)
      | (e,SOME src) => (error (Toplevel.exn_message e); loop true src)
      | (_,NONE) => ()
in
  (* NB: simple tty for now; later might read from other tty-style sources (e.g. sockets). *)

  val xmlP = XML.scan_comment_whspc |-- XML.parse_elem >> single

  val tty_src = Source.set_prompt "" (Source.source Symbol.stopper xmlP NONE Source.tty)

  fun pgip_toplevel x = loop true x
end


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
      (fn txt => Toplevel.imperative (fn () => process_pgip txt))));

fun init_outer_syntax () = OuterSyntax.add_parsers
 [undoP, redoP, restartP, kill_proofP, context_thy_onlyP, try_context_thy_onlyP,
  inform_file_processedP, inform_file_retractedP, process_pgipP];

end;


(* init *)

val initialized = ref false;

fun set_prompts true _ = ml_prompts "ML> " "ML# "
  | set_prompts false true = ml_prompts "PGIP-ML>" "PGIP-ML# "
  | set_prompts false false = ml_prompts ("> " ^ special "372") ("- " ^ special "373");

fun init_setup isar pgip =
  (conditional (not (! initialized)) (fn () =>
   (if isar then setmp warning_fn (K ()) init_outer_syntax () else ();
    setup_xsymbols_output ();
    setup_pgml_output ();
    setup_messages ();
    setup_state ();
    setup_thy_loader ();
    setup_present_hook ();
    set initialized; ()));
  sync_thy_loader ();
  change print_mode (cons proof_generalN o remove (op =) proof_generalN);
  if pgip then
      (init_pgip_session_id();
       change print_mode (append [pgmlN, pgmlatomsN] o fold (remove (op =)) [pgmlN, pgmlatomsN]))
  else
    pgip_emacs_compatibility_flag := true;  (* assume this for PG <3.6 compatibility *)
  set quick_and_dirty;
  ThmDeps.enable ();
  set_prompts isar pgip;
  pgip_active := pgip);

fun init isar =
 (init_setup isar false;
  if isar then Isar.sync_main () else isa_restart ());

fun init_pgip false = panic "PGIP not supported for Isabelle/classic mode."
  | init_pgip true = (init_setup true true; pgip_toplevel tty_src);



(** generate elisp file for keyword classification **)

local

val regexp_meta = explode ".*+?[]^$";
val regexp_quote =
  implode o map (fn c => if c mem_string regexp_meta then "\\\\" ^ c else c) o explode;

fun defconst name strs =
  "\n(defconst isar-keywords-" ^ name ^
  "\n  '(" ^ space_implode "\n    " (map (quote o regexp_quote) strs) ^ "))\n";

fun make_elisp_commands commands kind = defconst kind
  (commands |> List.mapPartial (fn (c, _, k, _) => if k = kind then SOME c else NONE));

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
