(*  Title:      Pure/proof_general.ML
    ID:         $Id$
    Author:     David Aspinall and Markus Wenzel

Isabelle configuration for Proof General (see http://proofgeneral.inf.ed.ac.uk)
Includes support for PGIP control language for Isabelle/Isar.

===========================================================================
NOTE: With this version you will lose support for the Isabelle
preferences menu in the currently released version of Proof General (3.5).
No other changes should be visible in the Emacs interface.

If the loss of preferences is a serious problem, please use a "sticky"
check-out of the previous version of this file, version 1.27.

A version of Emacs Proof General which supports the new PGIP format for
preferences will be available shortly.  
===========================================================================

STATUS: this version is an experimental version that supports PGIP 2.X.

*)

signature PROOF_GENERAL =
sig
  val setup: (theory -> theory) list
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
end;

structure ProofGeneral : PROOF_GENERAL =
struct

structure P = OuterParse

(* PGIP messaging mode (independent of PGML output) *)

val pgip_active = ref false;
val pgip_emacs_compatibility_flag = ref false;

fun pgip () = (!pgip_active);
fun pgip_emacs_compatibility () = (!pgip_emacs_compatibility_flag);


(* print modes *)

val proof_generalN = "ProofGeneral"; (* token markup (colouring vars, etc.) *)
val xsymbolsN = Symbol.xsymbolsN;    (* XSymbols symbols *)
val pgmlN = "PGML";		     (* XML escapes and PGML symbol elements *)
val pgmlatomsN = "PGMLatoms";	     (* variable kind decorations *)
val thm_depsN = "thm_deps";	     (* meta-information about theorem deps *)

fun pgml () = pgmlN mem_string ! print_mode;

(* text output: print modes for xsymbol and PGML *)

local

fun xsym_output "\\" = "\\\\"
  | xsym_output s = if Symbol.is_raw s then Symbol.decode_raw s else s;

fun xsymbols_output s =
  if xsymbolsN mem_string ! print_mode andalso exists_string (equal "\\") s then
    let val syms = Symbol.explode s
    in (implode (map xsym_output syms), real (Symbol.length syms)) end
  else Symbol.default_output s;

fun pgml_sym s =
  (case Symbol.decode s of
    Symbol.Char "\\" => "\\\\"
  | Symbol.Char s => XML.text s
  | Symbol.Sym s => XML.element "sym" [("name", s)] []
  | Symbol.Ctrl s => XML.element "ctrl" [("name", s)] []
  | Symbol.Raw s => s);

fun pgml_output str =
  let val syms = Symbol.explode str
  in (implode (map pgml_sym syms), real (Symbol.length syms)) end;

in 

fun setup_xsymbols_output () = 
    Output.add_mode 
	xsymbolsN 
	(xsymbols_output, Symbol.default_indent, Symbol.encode_raw);

fun setup_pgml_output () = 
    Output.add_mode 
	pgmlN
	(pgml_output, Symbol.default_indent, Symbol.encode_raw);

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
    (if Output.has_mode pgmlatomsN then 
	 xml_atom kind x
     else bg_tag ^ x ^ end_tag, 
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


(* assembling PGIP packets *)

val pgip_refseq = ref None : string option ref
val pgip_refid = ref None : string option ref

local
    val myseq_no = ref 1;      (* PGIP packet counter *)

    val pgip_class  = "pg"
    val pgip_origin = "Isabelle/Isar"
    val pgip_id = (getenv "HOSTNAME") ^ "/" ^ (getenv "USER") ^ "/" ^ 
		   (Time.toString(Time.now()))
	          (* FIXME: PPID is empty for me: any way to get process ID? *)

    fun assemble_pgips pgips = 
	XML.element 
	     "pgip" 
	     ([("class",  pgip_class),
	       ("origin", pgip_origin),
	       ("id",     pgip_id)] @
	      (if_none (apsome (single o (pair "refseq")) (!pgip_refseq)) []) @
	      (if_none (apsome (single o (pair "refid")) (!pgip_refid)) []) @
	      [("seq",  string_of_int (Library.inc myseq_no))])
	     pgips
in

 fun decorated_output bg en prfx = 
    writeln_default o enclose bg en o prefix_lines prfx;

 (* FIXME: see Rev 1.48 [PG CVS] for cleaner version of this which can be used
    for PG 4.0 which processes PGIP without needing special chars. *)
 fun issue_pgips ps = 
     if pgip_emacs_compatibility() then
	 decorated_output (* add urgent message annotation *)
	     (oct_char "360") (oct_char "361") "" 
	     (assemble_pgips ps)
     else 
	 writeln_default (assemble_pgips ps)

 fun assemble_pgip resp attrs s = assemble_pgips [XML.element resp attrs [s]]
				  
 fun assemble_pgipe resp attrs = assemble_pgips [XML.element resp attrs []]

 (* FIXME: need to add stuff to gather PGIPs here *)
 fun issue_pgip resp attrs = writeln_default o (assemble_pgip resp attrs)

(*  FIXME: temporarily to support PG 3.4.  *)
 fun issue_pgip_maybe_decorated bg en resp attrs s = 
     if pgip_emacs_compatibility() then
      (*  in PGIP mode, but using escape characters as well.  *)
	writeln_default (enclose bg en (assemble_pgip resp attrs s))
     else 
	issue_pgip resp attrs s
	
 fun issue_pgipe resp attrs = writeln_default (assemble_pgipe resp attrs)

end

(* messages and notification *)

fun message resp attrs bg en prfx s =
  if pgip() then 
      issue_pgip_maybe_decorated bg en resp attrs (prefix_lines prfx s)
  else 
      decorated_output bg en prfx s;


local
    val display_area = ("area", "display")
    val message_area = ("area", "message")
    val tracing_category = ("category", "tracing")
    val urgent_indication = ("urgent", "y")
    val nonfatal = ("fatality", "nonfatal")
    val fatal = ("fatality", "fatal")
    val panic = ("fatality", "panic")

    val thyname_attr = pair "thyname"
    val url_attr = pair "url"
    fun localfile_url_attr path = url_attr ("file:///" ^ path)
in			   

fun setup_messages () =
 (writeln_fn  := message "normalresponse" [message_area] "" "" "";

  priority_fn := message "normalresponse" [message_area, urgent_indication]
			 (oct_char "360") (oct_char "361") "";

  tracing_fn := message "normalresponse"  [message_area, tracing_category]
			(oct_char "360" ^ oct_char "375") (oct_char "361") "";

  warning_fn := message "errorresponse"    [nonfatal]
			(oct_char "362") (oct_char "363") "### ";

  error_fn := message "errorresponse" [fatal]
		      (oct_char "364") (oct_char "365") "*** ";

  panic_fn := message "errorresponse" [panic]
		      (oct_char "364") (oct_char "365") "!!! ")


(* accumulate printed output in a single PGIP response *)

fun with_displaywrap (elt,attrs) dispfn =
    let 
	val lines = ref ([] : string list);
	fun wlgrablines s = (lines:= (s :: (!lines)))
    in 
	(setmp writeln_fn wlgrablines dispfn ();
	 (* FIXME: cat_lines here inefficient, should use stream output *)
         issue_pgip elt attrs (cat_lines (!lines)))
    end

val emacs_notify = decorated_output (oct_char "360") (oct_char "361") "";
    
fun tell_clear_goals () = 
    if pgip() then
	issue_pgipe "cleardisplay" [display_area]
    else 
	emacs_notify "Proof General, please clear the goals buffer.";

fun tell_clear_response () = 
    if pgip() then
	issue_pgipe "cleardisplay" [message_area]
    else 
	emacs_notify "Proof General, please clear the response buffer.";

fun tell_file_loaded path = 
    if pgip() then
	issue_pgipe "informtheoryloaded"  (* FIXME: get thy name from info here? *)
		    [thyname_attr        (XML.text (File.sysify_path path)),
		     localfile_url_attr  (XML.text (File.sysify_path path))]
    else 
	emacs_notify ("Proof General, this file is loaded: " 
		      ^ quote (File.sysify_path path));

fun tell_file_retracted path = 
    if pgip() then
	issue_pgipe "informtheoryretracted"  (* FIXME: get thy name from info here? *)
		    [thyname_attr        (XML.text (File.sysify_path path)),
		     localfile_url_attr  (XML.text (File.sysify_path path))]
    else 
	emacs_notify ("Proof General, you can unlock the file " 
		      ^ quote (File.sysify_path path));


(* theory / proof state output *)

local

    fun tmp_markers f =	setmp Display.current_goals_markers 
			      (oct_char "366", oct_char "367", "") f ()

    fun statedisplay prts =
	issue_pgip "proofstate" []
		   (XML.element "pgml" []
				[XML.element "statedisplay" 
					     [] 
					     [Output.output (* FIXME: needed? *)
						  (Pretty.output
						       (Pretty.chunks prts))]])

    fun print_current_goals n m st =
	if pgml () then statedisplay (Display.pretty_current_goals n m st)
	else tmp_markers (fn () => Display.print_current_goals_default n m st)
	     
    fun print_state b st =
	if pgml () then statedisplay (Toplevel.pretty_state b st)
	else tmp_markers (fn () => Toplevel.print_state_default b st)
in

 fun setup_state () =
     (Display.print_current_goals_fn := print_current_goals;
      Toplevel.print_state_fn := print_state;
      (* FIXME: check next octal char won't appear in pgip? *)
      Toplevel.prompt_state_fn := (suffix (oct_char "372") o  
				   Toplevel.prompt_state_default));
end

end

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


(* theory loader actions *)

local

fun add_master_files name files =
  let val masters = [ThyLoad.thy_path name, ThyLoad.ml_path name]
  in masters @ gen_rems (op = o pairself Path.base) (files, masters) end;

fun trace_action action name =
  if action = ThyInfo.Update then
    seq tell_file_loaded (ThyInfo.loaded_files name)
  else if action = ThyInfo.Outdate orelse action = ThyInfo.Remove then
    seq tell_file_retracted (add_master_files name (ThyInfo.loaded_files name))
  else ();

in
  fun setup_thy_loader () = ThyInfo.add_hook trace_action;
  fun sync_thy_loader () = seq (trace_action ThyInfo.Update) (ThyInfo.names ());
end;


(* prepare theory context *)

val thy_name = Path.pack o #1 o Path.split_ext o Path.base o Path.unpack;
val update_thy_only = setmp MetaSimplifier.trace_simp 
			    false ThyInfo.update_thy_only;

fun which_context () =
  (case Context.get_context () of
    Some thy => "  Using current (dynamic!) one: " ^
      (case try PureThy.get_name thy of Some name => quote name | None => "<unnamed>")
  | None => "");

fun try_update_thy_only file =
  ThyLoad.cond_add_path (Path.dir (Path.unpack file)) (fn () =>
    let val name = thy_name file in
      if is_some (ThyLoad.check_file (ThyLoad.thy_path name)) 
      then update_thy_only name
      else warning ("Unkown theory context of ML file." ^ which_context ())
    end) ();


(* get informed about files *)

val inform_file_retracted = 
    ThyInfo.if_known_thy ThyInfo.remove_thy o thy_name;
val inform_file_processed = 
    ThyInfo.if_known_thy ThyInfo.touch_child_thys o thy_name;

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

fun thm_deps_message (thms, deps) = 
    if pgip() then
	issue_pgips 
	    [XML.element
		 "metainforesponse"  (* FIXME: get thy name from info here? *)
		 [("infotype", "isabelle_theorem_dependencies")]
		 [XML.element "value" [("name", "thms")] [XML.text thms],
		  XML.element "value" [("name", "deps")] [XML.text deps]]]
    else emacs_notify 
	     ("Proof General, theorem dependencies of " 
	      ^ thms ^ " are " ^ deps)


fun tell_thm_deps ths =
  conditional (thm_depsN mem_string ! print_mode) (fn () =>
    let
      val names = map Thm.name_of_thm ths \ "";
      val deps = Symtab.keys (foldl (uncurry Proofterm.thms_of_proof)
				    (Symtab.empty, map Thm.proof_of ths)) \ "";
    in
      if null names orelse null deps then ()
      else thm_deps_message (spaces_quote names, spaces_quote deps)
    end);

in

fun setup_present_hook () =
  Present.add_hook (fn _ => fn res => tell_thm_deps (flat (map #2 res)));

end;


(*** Preferences ***)

local
val pgipnat        = XML.element "pgipint" [("min", "0")] [] 
fun pgipnatmax max = XML.element "pgipint" [("min", "0"), 
					    ("max", string_of_int max)] []
val pgipbool       = XML.element "pgipbool" [] []

fun withdefault f = (f(), f)
in

fun nat_option r = (pgipnat,
  withdefault (fn () => string_of_int (!r)),
  (fn s => (case Syntax.read_nat s of
       None => error "nat_option: illegal value"
     | Some i => r := i)));

fun bool_option r = (pgipbool,
  withdefault (fn () => Bool.toString (!r)),
  (fn "false" => r := false | "true" => r := true
    | _ => error "bool_option: illegal value"));

val proof_option = (pgipbool,
  withdefault (fn () => Bool.toString (!proofs >= 2)),
  (fn "false" => proofs := 1 | "true" => proofs := 2
    | _ => error "proof_option: illegal value"));

val thm_deps_option = (pgipbool,
  withdefault (fn () => Bool.toString (Output.has_mode "thm_deps")),
  (fn "false" => print_mode := ((!print_mode) \ "thm_deps")
    | "true" => print_mode := ("thm_deps" ins (!print_mode))
    | _ => error "thm_deps_option: illegal value"));

local 
    val pg_print_depth_val = ref 10
    fun pg_print_depth n = (print_depth n; pg_print_depth_val := n)
in
val print_depth_option = (pgipnat,
  withdefault (fn () => string_of_int (!pg_print_depth_val)),
  (fn s => (case Syntax.read_nat s of
       None => error "print_depth_option: illegal value"
     | Some i => pg_print_depth i)))
end

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
      ("Show fully qualified names in Isabelle terms", bool_option long_names)),
     ("show-brackets", 
      ("Show full bracketing in Isabelle terms",
       bool_option show_brackets)),
     ("show-main-goal", 
      ("Show main goal in proof state display", bool_option Proof.show_main_goal)),
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
       print_depth_option))]),
   ("Tracing",
    [("trace-simplifier", 
      ("Trace simplification rules.",
       bool_option trace_simp)),
     ("trace-rules", ("Trace application of the standard rules",
		      bool_option trace_rules)),
     ("trace-unification", 
      ("Output error diagnostics during unification",
       bool_option Pattern.trace_unify_fail)),
     ("global-timing", 
      ("Whether to enable timing in Isabelle.",
       bool_option Output.timing))]),
   ("Proof", 
    [("quick-and-dirty", 
      ("Take a few (interactive-only) short cuts",
       bool_option quick_and_dirty)),
     ("full-proofs", 
      ("Record full proof objects internally",
       proof_option)),
     ("theorem-dependencies", 
       ("Track theorem dependencies within Proof General",
	thm_deps_option))])
   ];
end

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
	       ("url", isabelle_www)]
	    [XML.element "welcomemsg" [] [XML.text (Session.welcome())],
	     XML.element "helpdoc" 
         (* NB: would be nice to generate/display docs from isatool
          doc, but that program may not be running on same machine;
          front end should be responsible for launching viewer, etc. *)
		      [("name", "Isabelle/HOL Tutorial"),
		       ("descr", "A Gentle Introduction to Isabelle/HOL"), 
		       ("url",  "http://isabelle.in.tum.de/dist/Isabelle2003/doc/tutorial.pdf")]
	      []]
    in
	if exists then
	    (issue_pgips [proverinfo]; issue_pgips [File.read path])
	else panic ("PGIP configuration file " ^ config_file ^ " not found")
    end;
end


(* PGIP identifier tables (prover objects). [incomplete] *)

local
    val objtype_thy  = "theory"
    val objtype_thm  = "theorem"
    val objtype_term = "term"
    val objtype_type = "type"
		       
    fun xml_idtable ty ctx ids = 
	let
            fun ctx_attr (Some c)= [("context", c)]
              | ctx_attr None    = []
	    fun xmlid x = XML.element "identifier" [] [XML.text x];
	in 
	    XML.element "idtable" (("objtype", ty)::ctx_attr ctx)
	                          (map xmlid ids)
	end
in

fun setids t = issue_pgip "setids" [] t
fun addids t = issue_pgip "addids" [] t
fun delids t = issue_pgip "delids" [] t

fun delallids ty = setids (xml_idtable ty None [])

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
 val pthm = print_thm oo get_thm

 fun idvalue tp nm = ("idvalue",[("objtype",tp),("name",nm)])
in
fun askids (None, Some "theory")  = send_thy_idtable None (ThyInfo.names())
  | askids (None, None) =  send_thy_idtable None (ThyInfo.names())
                           (* only theories known in top context *)
  | askids (Some thy, Some "theory") = send_thy_idtable (Some thy) (ThyInfo.get_preds thy)
  | askids (Some thy, Some "theorem") = send_thm_idtable (Some thy) (ThyInfo.get_theory thy)
  | askids (Some thy, None) = (send_thy_idtable (Some thy) (ThyInfo.get_preds thy);
                               send_thm_idtable (Some thy) (ThyInfo.get_theory thy)) 
  | askids (_, Some ot) = error ("No objects of type "^(quote ot)^" are available here.")

fun showid (_,        "theory", n) = 
    with_displaywrap (idvalue "theory" n) (fn ()=>(print_theory (ThyInfo.get_theory n)))
  | showid (Some thy, "theorem", t) = 
    with_displaywrap (idvalue "theorem" t) (fn ()=>(pthm (ThyInfo.get_theory thy) t))
  | showid (None,     "theorem", t) = 
    with_displaywrap (idvalue "theorem" t) (fn ()=>pthm (topthy()) t)
  | showid (_, ot, _) = error ("Cannot show objects of type "^ot)

end
	 
(** Parsing proof scripts without execution **)

local
    fun markup_text str elt = [XML.element elt [] [XML.text str]]
    fun markup_text_attrs str elt attrs = [XML.element elt attrs [XML.text str]]
    fun empty elt = [XML.element elt [] []]

    fun named_item_elt toks str elt nameP objtyp = 
	let 
	    val name = (fst (nameP toks))
			handle _ => (error ("Error occurred in name parser for " ^ elt);
				     "")
				     
	in 
	    [XML.element elt 
			 ((if name="" then [] else [("name", name)])@
			  (if objtyp="" then [] else [("objtype", objtyp)]))
			 ([XML.text str])]
	end

    fun parse_warning msg = warning ("script->PGIP markup parser: " ^ msg)

    (* FIXME: allow dynamic extensions to language here: we need a hook in
       outer_syntax.ML to reset this table. *)

    val keywords_classification_table = ref (None:(string Symtab.table) option)

    fun get_keywords_classification_table () = 
	case (!keywords_classification_table) of
	    Some t => t
	  | None => (let
			 val tab = foldl (fn (tab,(c,_,k,_))=>Symtab.update((c,k),tab)) 
					 (Symtab.empty,OuterSyntax.dest_parsers())
		     in (keywords_classification_table := Some tab; tab) end)


		    
    fun xmls_of_thy_begin (name,toks,str) = (* see isar_syn.ML/theoryP *)
	let 
	    val ((thyname,imports,files),_) = ThyHeader.args toks
	in 
	    markup_text_attrs str "opentheory" [("thyname",thyname)]
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
		    val theoremsP = P.locale_target |-- name_facts >> (fn [] => "" | x::_ => x)
		in 
		    theoremsP
		end
	in 
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
		   | "defs"	 => named_item (opt_overloaded |-- P.spec_name >> (#1 o #1)) "theorem"
		   | "constdefs" => named_item P.name (* FIXME: heavily simplified/wrong *) "term"
		   | "theorems"  => named_item thmnameP "thmset"
		   | "lemmas"    => named_item thmnameP "thmset"
		   | "oracle"    => named_item P.name "oracle"
		   | "locale"	 => named_item ((P.opt_keyword "open" >> not) |-- P.name) "locale"
		   | _ => (parse_warning ("Unrecognized thy-decl command: " ^ name); plain_item)
	end

    fun xmls_of_thy_goal (name,toks,str) = 
	let 
	    val nameP = P.locale_target |-- ((P.opt_thm_name ":") >> #1)
	    (* TODO: add preference values for attributes 
	       val prefval = XML.element "prefval" [("name","thm-kind"),("value",name)]
	    *)
	in 
	    named_item_elt toks str "opengoal" nameP ""
	end

    fun xmls_of_qed (name,markup) = case name of
      "sorry"         => markup "giveupgoal"
    | "oops"          => markup "postponegoal"
    | "done"          => markup "closegoal" 
    | "by"            => markup "closegoal"  (* nested or toplevel *)
    | "qed"           => markup "closegoal"  (* nested or toplevel *)
    | "."	      => markup "closegoal"  (* nested or toplevel *)
    | ".."	      => markup "closegoal"  (* nested or toplevel *)
    | other => (* default to closegoal: may be wrong for extns *)
      (parse_warning ("Unrecognized qed command: " ^ quote other); markup "closegoal")

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
    (* proof control *)
    | "theory-goal"    => xmls_of_thy_goal (name,toks,str)
    | "proof-heading"  => markup "litcomment"
    | "proof-goal"     => markup "opengoal"  (* nested proof: have, show, ... *)
    | "proof-block"    => markup "proofstep" (* context-shift: proof, next; really "newgoal" *)
    | "proof-open"     => (empty "openblock") @ (markup "proofstep")
    | "proof-close"    => (markup "proofstep") @ (empty "closeblock")
    | "proof-script"   => markup "proofstep"
    | "proof-chain"    => markup "proofstep"
    | "proof-decl"     => markup "proofstep"
    | "proof-asm"      => markup "proofstep"
    | "proof-asm-goal" => markup "proofstep"
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
       val classification = Symtab.lookup (get_keywords_classification_table(),name)
   in case classification of
	  Some k => (xmls_of_kind k (name,toks,str))
	| None => (* an uncategorized keyword ignored for undo (maybe wrong) *)
	  (parse_warning ("Uncategorized command found: " ^ name ^ " -- using spuriouscmd");
	   markup_text str "spuriouscmd")
   end 

fun xmls_of_impropers [] = []
  | xmls_of_impropers toks = 
    let 
	val (whs,rest) = take_prefix (not o OuterLex.is_proper) toks
	fun markup [] _ = []
	  | markup toks x = markup_text (implode (map OuterLex.unparse toks)) x
    in
	(markup whs "comment") @ (markup rest "unparseable")
    end
    
end


local
    (* we have to weave together the whitespace/comments with proper tokens 
       to reconstruct the input. *)

    fun match_tokens ([],us,vs) = (rev vs,us)  (* used, unused *)
      | match_tokens (t::ts,w::ws,vs) = 
	if (t = w) then match_tokens (ts,ws,w::vs)
	else match_tokens (t::ts,ws,w::vs)
      | match_tokens _ = error ("match_tokens: mismatched input parse")
in
    fun xmls_of_str str =
    let 
       val toks = OuterSyntax.scan str

       (* parsing:   See outer_syntax.ML/toplevel_source *)
    
       fun parse_loop ([],[],xmls) = xmls
	 | parse_loop ([],itoks,xmls) = xmls @ (xmls_of_impropers itoks)
	 | parse_loop ((nm,toks,_)::trs,itoks,xmls) =
	   let 
	       (* first proper token is command, except FIXME for -- *)
	       val (prewhs,cmditoks') = take_prefix (not o OuterLex.is_proper) itoks
	       val (cmdtok,itoks') = case cmditoks' of x::xs => (x,xs)
						  | _ => error("proof_general/parse_loop impossible") 
	       val (utoks,itoks'') = match_tokens (toks,itoks',[])
               (* FIXME: should take trailing [w/s+] semicolon too in utoks *)

	       val str = implode (map OuterLex.unparse (cmdtok::utoks))

	       val xmls_whs = xmls_of_impropers prewhs 
	       val xmls_tr  = xmls_of_transition (nm,str,toks)
	   in
	       parse_loop(trs,itoks'',xmls @ xmls_whs @ xmls_tr)
	   end
    in
	(* FIXME: put errors/warnings inside the parse result *)
	parse_loop (OuterSyntax.read toks, toks, [])
    end


fun parsescript str = 
    issue_pgips [XML.element "parseresult" [] (xmls_of_str str)]

end



(**** PGIP:  Isabelle -> Interface ****)

val isabelle_pgml_version_supported = "1.0"; 
val isabelle_pgip_version_supported = "2.0"

fun usespgip () = 
    issue_pgipe "usespgip" [("version", isabelle_pgip_version_supported)];

fun usespgml () = 
    issue_pgipe "usespgml" [("version", isabelle_pgml_version_supported)];

fun hasprefs () = 
    seq (fn (prefcat, prefs) =>
	    issue_pgips [XML.element "hasprefs" [("prefcategory",prefcat)]
		 (map (fn (name, (descr, (ty, (default,_),_))) => 
		       XML.element "haspref" [("name", name), 
					      ("descr", descr), 
					      ("default", default)]
		       [ty]) prefs)]) (!preferences);

fun allprefs () = foldl (op @) ([], map snd (!preferences))
	
fun setpref name value = 
    (case assoc (allprefs(), name) of
	 None => warning ("Unknown pref: " ^ quote name)
       | Some (_, (_, _, set)) => set value);

fun getpref name = 
    (case assoc (allprefs(), name) of
	 None => warning ("Unknown pref: " ^ quote name)
       | Some (_, (_, (_,get), _)) => 
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


(* load an arbitrary (.thy or .ML) file *)

fun use_thy_or_ml_file file = 
    let
	val (path,extn) = Path.split_ext (Path.unpack file)
    in
	case extn of
	    "" => isarcmd ("use_thy " ^ (quote (Path.pack path)))
	  | "thy" => isarcmd ("use_thy " ^ (quote (Path.pack path)))
	  | "ML" => isarcmd ("use " ^ quote file)
	  (* instead of error we could guess theory? *)
	  | other => error ("Don't know how to read a file with extension " ^ other)
    end  


local
  (* Proof control commands *)

  fun xmlattro attrs attr = assoc(attrs,attr)

  fun xmlattr attrs attr = 
      (case xmlattro attrs attr of 
	   Some value => value 
	 | None => raise PGIP ("Missing attribute: " ^ attr))

  val thyname_attr = "thyname"
  val objtype_attr = "objtype"
  val name_attr = "name"
  val dirname_attr = "dir"
  fun comment x = "(* " ^ x ^ " *)"

  (* parse URLs like "file://host/name.thy" *)
  (* FIXME: instead of this, extend code in General/url.ML & use that. *)
  fun decode_url url = 
      (let 
	  val sep = find_index_eq ":" (explode url)
 	  val proto = String.substring(url,0,sep)
	  val hostsep = find_index_eq "/" (drop (sep+3,explode url))
	  val host = String.substring(url,sep+3,hostsep-sep+4)
	  val doc = if (size url >= sep+hostsep+3) then
			String.substring(url,sep+hostsep+4,size url-hostsep-sep-4) 
		    else ""
      in 
	  (proto,host,doc)
      end) handle Subscript => error ("Badly formed URL " ^ url)
 
  fun localfile_of_url url =
      let
	  val (proto,host,name) = decode_url url
      in
	  if (proto = "file" andalso 
	      (host = "" orelse 
	       host = "localhost" orelse 
	       host = (getenv "HOSTNAME")))
	     then name
	  else error ("Cannot access non-local URL " ^ url)
      end

  fun fileurl_of attrs = localfile_of_url (xmlattr attrs "url")

  val topthy = Toplevel.theory_of o Toplevel.get_state
  val topthy_name = PureThy.get_name o topthy

  val currently_open_file = ref (None : string option)

in

fun process_pgip_element pgipxml = (case pgipxml of 
  (XML.Text t) => warning ("Ignored text in PGIP packet: \n" ^ t)
| (XML.Elem (xml as (elem, attrs, data))) => 
  (case elem of
       (* protocol config *)
       "askpgip"  	=> (usespgip (); send_pgip_config ())
     | "askpgml"  	=> usespgml ()
     (* proverconfig *)
     | "askprefs" 	=> hasprefs ()
     | "getpref"  	=> getpref (xmlattr attrs name_attr)
     | "setpref"  	=> setpref (xmlattr attrs name_attr) (xmltext data)
     (* provercontrol *)
     | "proverinit" 	=> isar_restart ()
     | "proverexit" 	=> isarcmd "quit"
     | "startquiet" 	=> isarcmd "disable_pr"
     | "stopquiet"  	=> isarcmd "enable_pr"
     | "pgmlsymbolson"   => (print_mode := (["xsymbols", "symbols"] @ ! print_mode))
     | "pgmlsymbolsoff"  => (print_mode := (Library.gen_rems 
						(op =) 
						(! print_mode, ["xsymbols", "symbols"])))
     (* properproofcmd: proper commands which belong in script *)
     | "opengoal"       => isarscript data
     | "proofstep"      => isarscript data
     | "closegoal"      => isarscript data
     | "giveupgoal"     => isarscript data
     | "postponegoal"   => isarscript data
     | "comment"	=> isarscript data
     | "litcomment"     => isarscript data
     | "spuriouscmd"    => isarscript data
     | "badcmd"		=> isarscript data
     (* improperproofcmd: improper commands which *do not* belong in script *)
     | "undostep"       => isarcmd "ProofGeneral.undo"
     | "abortgoal"      => isarcmd "ProofGeneral.kill_proof"  
     | "forget"         => error "Not implemented" 
     | "restoregoal"    => error "Not implemented"  (* could just treat as forget? *)
     (* proofctxt: improper commands *)
     | "askids"         => askids (xmlattro attrs thyname_attr, 
				   xmlattro attrs objtype_attr)
     | "showid"	        => showid (xmlattro attrs thyname_attr, 
				   xmlattr attrs objtype_attr,
		     		   xmlattr attrs name_attr)
     | "parsescript"    => parsescript (xmltext data)
     | "showproofstate" => isarcmd "pr"
     | "showctxt"       => isarcmd "print_theory"   (* more useful than print_context *)
     | "searchtheorems" => isarcmd ("thms_containing " ^ (xmltext data))
     | "setlinewidth"   => isarcmd ("pretty_setmargin " ^ (xmltext data))
     | "viewdoc"	=> isarcmd ("print_" ^ (xmltext data)) (* FIXME: isatool doc? *)
     (* properfilecmd: proper theory-level script commands *)
     | "opentheory"     => isarscript data
     | "theoryitem"     => isarscript data
     | "closetheory"    => (isarscript data;
			    writeln ("Theory "^(topthy_name())^" completed."))
     (* improperfilecmd: theory-level commands not in script *)
     | "aborttheory"    => isarcmd ("init_toplevel")
     | "retracttheory"  => isarcmd ("kill_thy " ^
				    (quote (xmlattr attrs thyname_attr)))
     | "loadfile"       => use_thy_or_ml_file    (fileurl_of attrs)
     | "openfile"       => (inform_file_retracted (fileurl_of attrs);
			    currently_open_file := Some (fileurl_of attrs))
     | "closefile"      => (case !currently_open_file of 
				Some f => (inform_file_processed f;
					   currently_open_file := None)
			      | None => raise PGIP ("closefile when no file is open!"))
     | "abortfile"      => (currently_open_file := None) (* perhaps error for no file open *)
     | "changecwd"      => ThyLoad.add_path (xmlattr attrs dirname_attr)
     (* unofficial command for debugging *)
     | "quitpgip" => raise PGIP_QUIT  
     | _ => raise PGIP ("Unrecognized PGIP element: " ^ elem)))

fun process_pgip_tree s = 
    (pgip_refseq := None; 
     pgip_refid := None;
     (case s of
	  XML.Elem ("pgip", attrs, pgips) => 
	  (let 
	       val class = xmlattr attrs "class"
	       val _ = (pgip_refseq := xmlattro attrs "seq";
			pgip_refid :=  xmlattro attrs "id")
	   in  
	       if (class = "pa") then
		   seq process_pgip_element pgips
	       else 
		   raise PGIP "PGIP packet for me should have class=\"pa\""
	   end)
	| _ => raise PGIP "Invalid PGIP packet received") 
     handle (PGIP msg) => 
	    (error (msg ^ "\nPGIP error occured in XML text below:\n" ^ 
		    (XML.string_of_tree s))))

(* for export to Emacs *)
(* val process_pgip = process_pgip_tree o XML.tree_of_string; *)
(* FIXME: for temporary compatibility with PG 3.4, we engage special characters
   during output *)
fun process_pgip s = 
    (pgip_emacs_compatibility_flag := true;
     process_pgip_tree (XML.tree_of_string s);
     pgip_emacs_compatibility_flag := false)
end




(* PGIP loop: process PGIP input only *)

local  

exception XML_PARSE

fun loop src : unit =
    let 
	val _ = issue_pgipe "ready" []
	val pgipo = (Source.get_single src) 
			handle e => raise XML_PARSE
    in
	case pgipo of  
	     None  => ()
	   | Some (pgip,src') =>  
	     ((process_pgip_tree pgip); loop src') handle e => handler (e,Some src')
    end handle e => handler (e,Some src)  (* i.e. error in ready/XML parse *)

and handler (e,srco) = 
    case (e,srco) of
        (XML_PARSE,Some src) => 
	(* (!error_fn "Invalid XML input, aborting"; ()) NB: loop OK for tty, but want exit on EOF *)
         panic "Invalid XML input, aborting"
      | (PGIP_QUIT,_) => ()
      | (ERROR,Some src) => loop src (* message already given *)
      | (Interrupt,Some src) => (!error_fn "Interrupt during PGIP processing"; loop src)
      | (Toplevel.UNDEF,Some src) => (error "No working context defined"; loop src) (* usually *)
      | (e,Some src) => (error (Toplevel.exn_message e); loop src)
      | (_,None) => ()
in
  (* NB: simple tty for now; later might read from other tty-style sources (e.g. sockets). *)

  val xmlP = XML.scan_comment_whspc |-- XML.parse_elem >> single

  val tty_src = Source.set_prompt "" (Source.source Symbol.stopper xmlP None Source.tty)

  val pgip_toplevel =  loop 
end


(* additional outer syntax for Isar *)

local structure P = OuterParse and K = OuterSyntax.Keyword in

val undoP = (* undo without output *)
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
 [undoP, restartP, kill_proofP, context_thy_onlyP, try_context_thy_onlyP,
  inform_file_processedP, inform_file_retractedP, process_pgipP];

end;


(* init *)

val initialized = ref false;

fun set_prompts true _ = ml_prompts "ML> " "ML# " 
  | set_prompts false true = ml_prompts "PGIP-ML>" "PGIP-ML# "
  | set_prompts false false = 
    ml_prompts ("> " ^ oct_char "372") ("- " ^ oct_char "373");

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
  print_mode := proof_generalN :: (! print_mode \ proof_generalN);
  if pgip then 
      print_mode := pgmlN :: (pgmlatomsN :: (! print_mode \ pgmlN \ pgmlatomsN)) 
    else ();
  set quick_and_dirty;
  ThmDeps.enable ();
  set_prompts isar pgip;
  pgip_active := pgip)

fun init isar = 
    (init_setup isar false;
     if isar then ((* da: this welcome is problematic: clashes with welcome
		      issued for PG anyway. 
		      welcome (); *)
		    Isar.sync_main ()) else isa_restart ());

fun init_pgip false = panic "Sorry, PGIP not supported for Isabelle/classic mode."
  | init_pgip true = (init_setup true true; pgip_toplevel tty_src);



(** generate keyword classification elisp file **)

local

val regexp_meta = explode ".*+?[]^$";
val regexp_quote = 
    implode o map  (fn c => if c mem regexp_meta then "\\\\" ^ c else c)
    o explode;

fun defconst name strs =
  "\n(defconst isar-keywords-" ^ name ^
  "\n  '(" ^ space_implode "\n    " (map (quote o regexp_quote) strs) ^ "))\n";

fun make_elisp_commands commands kind =
  defconst kind (mapfilter 
		     (fn (c, _, k, _) => if k = kind then Some c else None) 
		     commands);

fun make_elisp_syntax (keywords, commands) =
  ";;\n\
  \;; Keyword classification tables for Isabelle/Isar.\n\
  \;; This file was generated by " ^ Session.name () ^ " -- DO NOT EDIT!\n\
  \;;\n\
  \;; $" ^ "Id$\n\
  \;;\n" ^
  defconst "major" (map #1 commands) ^
  defconst "minor" (filter Syntax.is_identifier keywords) ^
  implode (map (make_elisp_commands commands) OuterSyntax.Keyword.kinds) ^
  "\n(provide 'isar-keywords)\n";

in

fun write_keywords s =
  (init_outer_syntax ();
    File.write (Path.unpack ("isar-keywords" ^ (if s = "" then "" else "-" ^ s) ^".el"))
      (make_elisp_syntax (OuterSyntax.dest_keywords (), 
			  OuterSyntax.dest_parsers ())));

end;

end
