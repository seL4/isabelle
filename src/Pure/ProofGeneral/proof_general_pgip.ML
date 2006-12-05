(*  Title:      Pure/ProofGeneral/proof_general_pgip.ML
    ID:         $Id$
    Author:     David Aspinall and Markus Wenzel

Isabelle configuration for Proof General using PGIP protocol.
See http://proofgeneral.inf.ed.ac.uk/kit  
*)


signature PROOF_GENERAL_PGIP =
sig
  val init_pgip: bool -> unit		  (* main PGIP loop with true; fail with false *)

  (* These two are just to support the semi-PGIP Emacs mode *)
  val init_pgip_channel: (string -> unit) -> unit 
  val process_pgip: string -> unit     
end

structure ProofGeneralPgip : PROOF_GENERAL_PGIP  =
struct

structure P = OuterParse;

open Pgip;

(* print modes *)

val proof_generalN = "ProofGeneral";  (*token markup (colouring vars, etc.)*)
val xsymbolsN = Symbol.xsymbolsN;     (*X-Symbol symbols*)
val pgmlN = "PGML";                   (*XML escapes and PGML symbol elements*)
val pgmlatomsN = "PGMLatoms";         (*variable kind decorations*)
val thm_depsN = "thm_deps";           (*meta-information about theorem deps*)


(* text output: print modes for xsymbol and PGML *)

local

fun xsym_output "\\" = "\\\\"
  | xsym_output s = if Symbol.is_raw s then Symbol.decode_raw s else s;

fun xsymbols_output s =
  if Output.has_mode xsymbolsN andalso exists_string (equal "\\") s then
    let val syms = Symbol.explode s
    in (implode (map xsym_output syms), real (Symbol.length syms)) end
  else Symbol.default_output s;

(* XML immediately rendered pretty printer. Take care not to double escape *)
fun pgml_sym s =
  (case Symbol.decode s of
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
    (xsymbols_output, K xsymbols_output, Symbol.default_indent, Symbol.encode_raw);

fun setup_pgml_output () =
  Output.add_mode pgmlN
    (pgml_output, K pgml_output, Symbol.default_indent, Symbol.encode_raw);

end;


(* token translations *)

local

val class_tag = "class"
val tfree_tag = "tfree"
val tvar_tag = "tvar"
val free_tag = "free"
val bound_tag = "bound"
val var_tag = "var"
val skolem_tag = "skolem"

fun xml_atom kind x = XML.element "atom" [("kind", kind)] [XML.text x];

fun tagit kind x = 
 (xml_atom kind x, real (Symbol.length (Symbol.explode x)));

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


(** assembling and issuing PGIP packets **)

val pgip_refid  = ref NONE: string option ref;
val pgip_refseq = ref NONE: int option ref;

local
  val pgip_class  = "pg"
  val pgip_tag = "Isabelle/Isar"
  val pgip_id = ref ""
  val pgip_seq = ref 0
  fun pgip_serial () = inc pgip_seq

  fun assemble_pgips pgips =
    Pgip { tag = SOME pgip_tag, 
	   class = pgip_class,
	   seq = pgip_serial(),
	   id = !pgip_id,
	   destid = !pgip_refid,
	   (* destid=refid since Isabelle only communicates back to sender *)
	   refid  = !pgip_refid,
	   refseq = !pgip_refseq,
	   content = pgips }
in

fun init_pgip_session_id () =
    pgip_id := getenv "HOSTNAME" ^ "/" ^ getenv "USER" ^ "/" ^
               getenv "ISABELLE_PID" ^ "/" ^ Time.toString (Time.now ())

fun matching_pgip_id id = (id = !pgip_id)

val output_xml_fn = ref writeln_default  
fun output_xml s = (!output_xml_fn) (XML.string_of_tree s);  (* TODO: string buffer *)

fun issue_pgip_rawtext str = 
    output_xml (PgipOutput.output (assemble_pgips [XML.Rawtext str]))

fun issue_pgips pgipops =
    output_xml (PgipOutput.output (assemble_pgips (map PgipOutput.output pgipops)));

fun issue_pgip pgipop =
    output_xml (PgipOutput.output (assemble_pgips [PgipOutput.output pgipop]));

end;


(** messages and notification **)

local
    val delay_msgs = ref false   (*true: accumulate messages*)
    val delayed_msgs = ref []

    fun queue_or_issue pgip =
	if (! delay_msgs) then
	    delayed_msgs := pgip :: ! delayed_msgs
	else issue_pgip pgip
in
    fun normalmsg area cat urgent prfx s = 
	let 
	    val content = 
		(* NB: prefixing is obsolete, but let's keep it for a while for familiarity *)
		    XML.Elem("pgmltext",[],[XML.Rawtext (prefix_lines prfx s)])
	    val pgip = Normalresponse {area=area,messagecategory=cat,
				       urgent=urgent,content=[content] }
	in
	    queue_or_issue pgip
	end

    fun errormsg fatality prfx s =
	let
	    (* FIXME: need a way of passing in locations *)
              val content =
		  XML.Elem("pgmltext",[],[XML.Rawtext (prefix_lines prfx s)])
	      val pgip = Errorresponse {area=NONE,fatality=fatality,
					content=[content], location=NONE}
	in 
	    queue_or_issue pgip
	end

    fun start_delay_msgs () = (set delay_msgs; delayed_msgs := [])
    fun end_delayed_msgs () = (reset delay_msgs; ! delayed_msgs)
end;

(* NB: all of the standard error/message functions now expect already-escaped text.
   FIXME: this may cause us problems now we're generating trees; on the other
   hand the output functions were tuned some time ago, so it ought to be 
   enough to use Rawtext always above. *)

fun setup_messages () =
 (writeln_fn := (fn s => normalmsg Message Normal false "" s);
  priority_fn := (fn s => normalmsg Message Normal true "" s);
  tracing_fn := (fn s => normalmsg  Message Tracing false "" s);
  info_fn := (fn s => normalmsg Message Information false "+++ " s);
  debug_fn := (fn s => normalmsg Message Internal false "+++ " s);
  warning_fn := (fn s => errormsg Nonfatal "### " s);
  error_fn := (fn s => errormsg Fatal "*** " s);
  panic_fn := (fn s => errormsg Panic "!!! " s))

(* immediate messages *)

fun tell_clear_goals ()      = issue_pgip (Cleardisplay {area=Display})
fun tell_clear_response ()   = issue_pgip (Cleardisplay {area=Message})
fun tell_file_loaded path    = issue_pgip (Informfileloaded {url=PgipTypes.pgipurl_of_path path})
fun tell_file_retracted path = issue_pgip (Informfileretracted {url=PgipTypes.pgipurl_of_path path})



(** theory / proof state output **)

local

fun statedisplay prts =
    let
	val display = Pretty.output (Pretty.chunks prts)
	val statedisplay = XML.Elem("statedisplay",[], [XML.Rawtext display])
    in
	issue_pgip (Proofstate {pgml=[XML.Elem("pgml",[],[statedisplay])]})
    end

fun print_current_goals n m st =
  statedisplay (Display.pretty_current_goals n m st)

fun print_state b st =
  statedisplay (Toplevel.pretty_state b st)

in

fun setup_state () =
  (Display.print_current_goals_fn := print_current_goals;
   Toplevel.print_state_fn := print_state);
      (*    Toplevel.prompt_state_fn := (fn s => suffix (special "372")
					(Toplevel.prompt_state_default s))); *)

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
    let 
	val valuethms = XML.Elem("value",[("name", "thms")],[XML.Text thms])
	val valuedeps = XML.Elem("value",[("name", "deps")],[XML.Text deps])
    in
	issue_pgip (Metainforesponse {attrs=[("infotype", "isabelle_theorem_dependencies")],
				      content=[valuethms,valuedeps]})
    end

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

(** lexicalstructure element with keywords (PGIP version of elisp keywords file) **)

fun lexicalstructure_keywords () = 
    let val commands = OuterSyntax.dest_keywords ()
	fun category_of k = if (k mem commands) then "major" else "minor"
         (* NB: we might filter to only include words like elisp case (OuterSyntax.is_keyword). *)
    	fun keyword_elt (keyword,help,kind,_) = 
  	    XML.Elem("keyword", [("word", keyword), ("category", category_of kind)],
	  	     [XML.Elem("shorthelp", [], [XML.Text help])])
        in 	    	    
            (* Also, note we don't call init_outer_syntax here to add interface commands,
            but they should never appear in scripts anyway so it shouldn't matter *)
            Lexicalstructure {content = map keyword_elt (OuterSyntax.dest_parsers()) }
        end

(* TODO: we can issue a lexicalstructure/keyword when the syntax gets extended dynamically;
   hooks needed in outer_syntax.ML to do that. *)


(* Configuration: GUI config, proverinfo messages *)

local
    val isabellewww = "http://isabelle.in.tum.de/"
    val staticconfig = "~~/lib/ProofGeneral/pgip_isar.xml"
    fun orenv v d = case (getenv v) of "" => d  | s => s
    fun config_file()  = orenv "ISABELLE_PGIPCONFIG" staticconfig
    fun isabelle_www() = orenv "ISABELLE_HOMEPAGE" isabellewww
in
fun send_pgip_config () =
    let
        val path = Path.unpack (config_file())
        val exists = File.exists path

	val wwwpage = 
	    (Url.unpack (isabelle_www()))
	    handle _ => 
		   (Output.panic 
			("Error in URL in environment variable ISABELLE_HOMEPAGE.");
			Url.unpack isabellewww)
		     
	val proverinfo =
            Proverinfo { name = "Isabelle",
			 version = version,
			 instance = Session.name(), 
			 descr = "The Isabelle/Isar theorem prover",
			 url = wwwpage,
			 filenameextns = ".thy;" }
    in
        if exists then
            (issue_pgip proverinfo; 
	     issue_pgip_rawtext (File.read path);
	     issue_pgip (lexicalstructure_keywords()))
        else Output.panic ("PGIP configuration file \"" ^ config_file() ^ "\" not found")
    end;
end


(* PGIP identifier tables (prover objects). [incomplete] *)

local
    (* TODO: objtypes should be in pgip_types.ML *)
    val objtype_thy  = "theory"
    val objtype_thm  = "theorem"
    val objtype_term = "term"
    val objtype_type = "type"

    fun xml_idtable ty ctx ids =
        PgipOutput.output (Idtable {objtype=ty,context=ctx,ids=ids})
in

fun setids t = issue_pgip (Setids {idtables = [t]})
fun addids t = issue_pgip (Addids {idtables = [t]})
fun delids t = issue_pgip (Delids {idtables = [t]})

fun delallids ty = setids (xml_idtable ty NONE [])

fun send_thy_idtable ctx thys = setids (xml_idtable objtype_thy ctx thys)
fun clear_thy_idtable () = delallids objtype_thy

fun send_thm_idtable ctx thy =
    addids (xml_idtable objtype_thm ctx (map fst (PureThy.thms_of thy)));

fun clear_thm_idtable () = delallids objtype_thm

(* fun send_type_idtable thy = TODO, it's a bit low-level messy
   & maybe not so useful anyway *)

end


(* Sending commands to Isar *)

fun isarcmd s =
    s |> OuterSyntax.scan |> OuterSyntax.read
      |> map (Toplevel.position (Position.name "PGIP message") o #3) |> Toplevel.>>>;

(* how TODO: apply a command given a transition function, e.g. IsarCmd.undo *)

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


(**** PGIP actions ****)


(* Responses to each of the PGIP input commands. 
   These are programmed uniformly for extensibility. *)

fun askpgip vs = 
    issue_pgip
        (Usespgip { version = PgipIsabelle.isabelle_pgip_version_supported,
		    pgipelems = PgipIsabelle.accepted_inputs })

fun askpgml vs = 
    issue_pgip
	(Usespgml { version = PgipIsabelle.isabelle_pgml_version_supported })

fun askprefs vs =
    let 
	fun preference_of {name, descr, default, pgiptype, get, set } = 
	    { name = name, descr = SOME descr, default = SOME default, 
	      pgiptype = pgiptype }
    in
	List.app (fn (prefcat, prefs) =>
		     issue_pgip (Hasprefs {prefcategory=SOME prefcat, 
					   prefs=map preference_of prefs}))
                 Preferences.preferences
    end 

fun askconfig vs = () (* TODO: add config response *)

local
    fun lookuppref pref = 
	case AList.lookup (op =) 
			  (map (fn p => (#name p,p))
			       (maps snd Preferences.preferences)) pref of
	    NONE => error ("Unknown prover preference: " ^ quote pref)
	  | SOME p => p
in
fun setpref vs = 
    let 
	val name = #name vs
	val value = #value vs
	val set = #set (lookuppref name)
    in
	set value
    end

fun getpref vs =
    let 
	val name = #name vs
	val get = #get (lookuppref name)
    in 
        issue_pgip (Prefval {name=name, value=get ()})
    end
end

fun proverinit vs = restart ()

fun proverexit vs = isarcmd "quit"

fun startquiet vs = isarcmd "disable_pr"

fun stopquiet vs = isarcmd "enable_pr"

fun pgmlsymbolson vs = 
    change print_mode (fn mode =>
			  remove (op =) Symbol.xsymbolsN mode @ [Symbol.xsymbolsN])

fun pgmlsymbolsoff vs =
    change print_mode (remove (op =) Symbol.xsymbolsN)

fun dostep vs = 
    let 
	val text = #text vs
    in 
	isarcmd text
    end

fun undostep vs =
    let 
	val times = #times vs
    in 
	isarcmd ("undos_proof " ^ (Int.toString times))
    end

fun redostep vs = isarcmd "redo"
    
fun abortgoal vs = isarcmd "ProofGeneral.kill_proof" 


fun askids vs = 
    let
	val thyname = #thyname vs
	val objtype = #objtype vs
    in 
	(* TODO: add askids for "file" here, which returns single theory with same name *)
	case (thyname,objtype) of 
           (* only theories known in top context *)
	   (NONE, NONE) =>  send_thy_idtable NONE (ThyInfo.names())
	 | (NONE, SOME "theory")  => send_thy_idtable NONE (ThyInfo.names())
	 | (SOME thy, SOME "theory") => send_thy_idtable (SOME thy) (ThyInfo.get_preds thy)
	 | (SOME thy, SOME "theorem") => send_thm_idtable (SOME thy) (ThyInfo.get_theory thy)
	 | (SOME thy, NONE) => (send_thy_idtable (SOME thy) (ThyInfo.get_preds thy);
                               send_thm_idtable (SOME thy) (ThyInfo.get_theory thy))
	 | (_, SOME ot) => error ("No objects of type "^(quote ot)^" are available here.")
    end

local
  (* accumulate printed output in a single PGIP response (inside <pgmltext>) *)
  fun with_displaywrap pgipfn dispfn =
      let
	  val lines = ref ([]: string list);
	  fun wlgrablines s = lines := s :: ! lines;
      in
	  setmp writeln_fn wlgrablines dispfn ();
	  issue_pgip (pgipfn (!lines))
      end;
in
fun showid vs = 
    let
	val thyname = #thyname vs
	val objtype = #objtype vs
	val name = #objtype vs
	val topthy = Toplevel.theory_of o Toplevel.get_state

	fun idvalue objtype name strings =
	    Idvalue { name=name, objtype=objtype,
		      text=[XML.Elem("pgmltext",[],map XML.Text strings)] }

	fun pthm thy name = print_thm (get_thm thy (Name name))
    in 
	case (thyname, objtype) of 
	    (_,"theory") =>
	    with_displaywrap (idvalue "theory" name) 
			     (fn ()=>(print_theory (ThyInfo.get_theory name)))
	  | (SOME thy, "theorem") =>
	    with_displaywrap (idvalue "theorem" name) 
			     (fn ()=>(pthm (ThyInfo.get_theory thy) name))
	  | (NONE, "theorem") =>
	    with_displaywrap (idvalue "theorem" name) 
			     (fn ()=>pthm (topthy()) name)
	  | (_, ot) => error ("Cannot show objects of type "^ot)
    end

(* The file which is currently being processed interactively.  
   In the pre-PGIP code, this was informed to Isabelle and the theory loader
   on completion, but that allows for circularity in case we read
   ourselves.  So PGIP opens the filename at the start of a script.
   We ought to prevent problems by modifying the theory loader to know
   about this special status, but for now we just keep a local reference. 
*) 

val currently_open_file = ref (NONE : pgipurl option)

fun askguise vs = 
    (* The "guise" is the PGIP abstraction of the prover's state.
       The <informguise> message is merely used for consistency checking. *)
    let 
	val openfile = !currently_open_file

	val topthy = Toplevel.theory_of o Toplevel.get_state
	val topthy_name = Context.theory_name o topthy

	val opentheory = SOME (topthy_name()) handle Toplevel.UNDEF => NONE

	fun topproofpos () = try Toplevel.proof_position_of (Isar.state ());
	val openproofpos = topproofpos()
    in
        issue_pgip (Informguise { file = openfile,
				  theory = opentheory,
				  (* would be nice to get thm name... *)
				  theorem = NONE,
				  proofpos = openproofpos })
    end

fun parsescript vs =
    let
	val text = #text vs
	val systemdata = #systemdata vs      
	val location = #location vs   (* TODO: extract position *)

        val _ = start_delay_msgs ()  (* gather parsing messages *)
        val xmls = PgipParser.xmls_of_str text
        val errs = end_delayed_msgs ()

	val sysattrs = PgipTypes.opt_attr "systemdata" systemdata
	val locattrs = PgipTypes.attrs_of_location location
     in
        issue_pgip (Parseresult { attrs= sysattrs@locattrs,
				  content = (map PgipOutput.output errs)@xmls })
    end

fun showproofstate vs = isarcmd "pr"

fun showctxt vs = isarcmd "print_theory"   (* more useful than print_context *)

fun searchtheorems vs =
    let 
	val arg = #arg vs
    in
	isarcmd ("thms_containing " ^ arg)
    end

fun setlinewidth vs = 
    let 
	val width = #width vs
    in
	isarcmd ("pretty_setmargin " ^ (Int.toString width)) (* FIXME: conversion back/forth! *)
    end

fun viewdoc vs =
    let 
	val arg = #arg vs
    in 
	isarcmd ("print_" ^ arg)   (* FIXME: isatool doc?.  Return URLs, maybe? *)
    end

fun doitem vs =
    let
	val text = #text vs
    in
	isarcmd text
    end

fun undoitem vs =
    isarcmd "ProofGeneral.undo"

fun redoitem vs =
    isarcmd "ProofGeneral.redo"

fun aborttheory vs = 
    isarcmd "init_toplevel"

fun retracttheory vs =
    let 
	val thyname = #thyname vs
    in
	isarcmd ("kill_thy " ^ quote thyname)
    end

fun loadfile vs = 
    let 
	val url = #url vs
    in 
	case !currently_open_file of
            SOME f => raise PGIP ("<loadfile> when a file is open!")
          | NONE => use_thy_or_ml_file (File.platform_path url)
    end

fun openfile vs =
  let 
      val url = #url vs
  in
      case !currently_open_file of
          SOME f => raise PGIP ("<openfile> when a file is already open! ")
        | NONE => (openfile_retract (File.platform_path url);
		   currently_open_file := SOME url) (*(File.platform_path url))*)
  end

fun closefile vs =
    case !currently_open_file of
        SOME f => (proper_inform_file_processed (File.platform_path f) 
						(Isar.state());
                   currently_open_file := NONE)
      | NONE => raise PGIP ("<closefile> when no file is open!")

fun abortfile vs =
    case !currently_open_file of
        SOME f => (isarcmd "init_toplevel";
		   currently_open_file := NONE)
      | NONE => raise PGIP ("<abortfile> when no file is open!")

fun retractfile vs = 
    let 
	val url = #url vs
    in
	case !currently_open_file of
            SOME f => raise PGIP ("<retractfile> when a file is open!")
          | NONE => inform_file_retracted (File.platform_path url)
    end

(* Path management: we allow theory files to have dependencies in
   their own directory, but when we change directory for a new file we
   remove the path.  Leaving it there can cause confusion with
   difference in batch mode.
   NB: PGIP does not assume that the prover has a load path. 
*)

local
    val current_working_dir = ref (NONE : string option)
in
fun changecwd vs = 
    let 
	val url = #url vs
	val newdir = File.platform_path url
    in
        (case (!current_working_dir) of
             NONE => ()
           | SOME dir => ThyLoad.del_path dir;
         ThyLoad.add_path newdir;
         current_working_dir := SOME newdir)
    end
end


fun systemcmd vs =
  let 
      val arg = #arg vs
  in
      isarcmd arg
  end

exception PGIP_QUIT;
fun quitpgip vs = raise PGIP_QUIT

fun process_input inp = case inp of
     Pgip.Askpgip vs         => askpgip vs
   | Pgip.Askpgml vs         => askpgml vs
   | Pgip.Askprefs vs        => askprefs vs 
   | Pgip.Askconfig vs       => askconfig vs
   | Pgip.Getpref vs         => getpref vs
   | Pgip.Setpref vs         => setpref vs
   | Pgip.Proverinit vs      => proverinit vs
   | Pgip.Proverexit vs      => proverexit vs
   | Pgip.Startquiet vs      => startquiet vs
   | Pgip.Stopquiet vs       => stopquiet vs
   | Pgip.Pgmlsymbolson vs   => pgmlsymbolson vs
   | Pgip.Pgmlsymbolsoff vs  => pgmlsymbolsoff vs
   | Pgip.Dostep vs          => dostep vs
   | Pgip.Undostep vs        => undostep vs
   | Pgip.Redostep vs        => redostep vs
   | Pgip.Forget vs	     => (error "<forget> not implemented")
   | Pgip.Restoregoal vs     => (error "<restoregoal> not implemented")
   | Pgip.Abortgoal vs       => abortgoal vs
   | Pgip.Askids vs          => askids vs
   | Pgip.Showid vs          => showid vs
   | Pgip.Askguise vs	     => askguise vs
   | Pgip.Parsescript vs     => parsescript vs
   | Pgip.Showproofstate vs  => showproofstate vs
   | Pgip.Showctxt vs        => showctxt vs
   | Pgip.Searchtheorems vs  => searchtheorems vs
   | Pgip.Setlinewidth vs    => setlinewidth vs
   | Pgip.Viewdoc vs         => viewdoc vs
   | Pgip.Doitem vs          => doitem vs
   | Pgip.Undoitem vs        => undoitem vs
   | Pgip.Redoitem vs        => redoitem vs
   | Pgip.Aborttheory vs     => aborttheory vs
   | Pgip.Retracttheory vs   => retracttheory vs
   | Pgip.Loadfile vs	     => loadfile vs
   | Pgip.Openfile vs	     => openfile vs
   | Pgip.Closefile vs	     => closefile vs
   | Pgip.Abortfile vs	     => abortfile vs
   | Pgip.Retractfile vs     => retractfile vs
   | Pgip.Changecwd vs	     => changecwd vs
   | Pgip.Systemcmd vs	     => systemcmd vs
   | Pgip.Quitpgip vs        => quitpgip vs


fun process_pgip_element pgipxml = 
    case pgipxml of
	(xml as (XML.Elem elem)) =>
	(case Pgip.input elem of
	     NONE => warning ("Unrecognized PGIP command, ignored: \n" ^
			      (XML.string_of_tree xml))
	   | SOME inp => (process_input inp)) (* errors later; packet discarded *)
      | (XML.Text t) => ignored_text_warning t
      |	(XML.Rawtext t) => ignored_text_warning t
and ignored_text_warning t =
    if (size (Symbol.strip_blanks t) > 0) then
	   warning ("Ignored text in PGIP packet: \n" ^ t)
    else ()

fun process_pgip_tree xml =
    (pgip_refid := NONE;
     pgip_refseq := NONE;
     (case xml of
          XML.Elem ("pgip", attrs, pgips) =>
          (let
               val class = PgipTypes.get_attr "class" attrs
               val dest  = PgipTypes.get_attr_opt "destid" attrs
               val _ = (pgip_refid :=  PgipTypes.get_attr_opt "id" attrs)
	       val _ = (pgip_refseq := Option.join 
					   (Option.map Int.fromString
						  (PgipTypes.get_attr_opt "seq" attrs)))
               (* Respond to prover broadcasts, or messages for us. Ignore rest *)
	       val processit = 
		   case dest of
                       NONE =>    class = "pa"
		     | SOME id => matching_pgip_id id
           in
               if processit then 
		   (List.app process_pgip_element pgips; true) 
	       else false
           end)
        | _ => raise PGIP "Invalid PGIP packet received")
     handle PGIP msg =>
            (Output.error_msg ((msg ^ "\nPGIP error occured in XML text below:\n") ^
			       (XML.string_of_tree xml));
	     true))

(* External input *)

val process_pgip_plain = K () o process_pgip_tree o XML.tree_of_string

end


(* PGIP loop: process PGIP input only *)

local

exception XML_PARSE

fun loop ready src =
    let
        val _ = if ready then issue_pgip (Ready ()) else ()
        val pgipo = (Source.get_single src)
                        handle e => raise XML_PARSE
    in
        case pgipo of
             NONE  => ()
           | SOME (pgip,src') =>
             let
                 val ready' = (process_pgip_tree pgip) 
				handle e => (handler (e,SOME src'); true)
             in
                 loop ready' src'
             end
    end handle e => handler (e,SOME src)  (* error in XML parse or Ready issue *)

and handler (e,srco) =
    case (e,srco) of
        (XML_PARSE,SOME src) =>
        Output.panic "Invalid XML input, aborting"
      | (PGIP_QUIT,_) => ()
      | (Interrupt,SOME src) => 
	(Output.error_msg "Interrupt during PGIP processing"; loop true src)
      | (Toplevel.UNDEF,SOME src) => 
	(Output.error_msg "No working context defined"; loop true src)
      | (e,SOME src) => 
	(Output.error_msg (Toplevel.exn_message e); loop true src)
      | (_,NONE) => ()
in
  (* TODO: add socket interface *)

  val xmlP = XML.scan_comment_whspc |-- XML.parse_elem >> single

  val tty_src = Source.set_prompt "" (Source.source Symbol.stopper xmlP NONE Source.tty)

  fun pgip_toplevel x = loop true x
end


(* additional outer syntax for Isar *)  
(* da: TODO: perhaps we can drop this superfluous syntax now??
   Seems cleaner to support the operations directly above in the PGIP actions.
 *)

local structure P = OuterParse and K = OuterKeyword in

val undoP = (*undo without output*)
  OuterSyntax.improper_command "ProofGeneral.undo" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.undo));

val redoP = (*redo without output*)
  OuterSyntax.improper_command "ProofGeneral.redo" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.redo));

(* da: what were these context commands ones for? *)
val context_thy_onlyP =
  OuterSyntax.improper_command "ProofGeneral.context_thy_only" "(internal)" K.control
    (P.name >> (Toplevel.no_timing oo IsarCmd.init_context update_thy_only));

val try_context_thy_onlyP =
  OuterSyntax.improper_command "ProofGeneral.try_context_thy_only" "(internal)" K.control
    (P.name >> (Toplevel.no_timing oo
      (Toplevel.imperative (K ()) oo IsarCmd.init_context try_update_thy_only)));

(* ProofGeneral.kill_proof still used above *)
val kill_proofP =
  OuterSyntax.improper_command "ProofGeneral.kill_proof" "(internal)" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.kill_proof_notify tell_clear_goals));

(* FIXME: Not quite same as commands used above *)
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

(* This one can actually be used for Daniel's interface scripting idea: generically!! *)
val process_pgipP =
  OuterSyntax.improper_command "ProofGeneral.process_pgip" "(internal)" K.control
    (P.text >> (Toplevel.no_timing oo
      (fn txt => Toplevel.imperative (fn () => process_pgip_plain txt))));

fun init_outer_syntax () = OuterSyntax.add_parsers
 [undoP, redoP, kill_proofP, context_thy_onlyP, try_context_thy_onlyP,
  inform_file_processedP, inform_file_retractedP, process_pgipP];

end;


(* init *)

val initialized = ref false;

(* ML top level only for testing, entered on <quitpgip> *)
fun set_prompts () = ml_prompts "ML> " "ML# ";

fun init_setup () =
  (conditional (not (! initialized)) (fn () =>
   (setmp warning_fn (K ()) init_outer_syntax ();
    setup_xsymbols_output ();
    setup_pgml_output ();
    setup_messages ();
    setup_state ();
    setup_thy_loader ();
    setup_present_hook ();
    init_pgip_session_id ();
    welcome ();
    set initialized; ()));
  sync_thy_loader ();
  change print_mode (cons proof_generalN o remove (op =) proof_generalN);
  change print_mode (append [pgmlN, pgmlatomsN] o subtract (op =) [pgmlN, pgmlatomsN]);
  set_prompts ());

fun init_pgip false = Output.panic "PGIP not supported for Isabelle/classic mode."
  | init_pgip true = (init_setup (); pgip_toplevel tty_src);



(** Out-of-loop PGIP commands (for Emacs hybrid mode) **)

local
    val pgip_output_channel = ref writeln_default
in

(* Set recipient for PGIP results *)
fun init_pgip_channel writefn =
    (init_pgip_session_id();  
     pgip_output_channel := writefn)				  

(* Process a PGIP command. 
   This works for preferences but not generally guaranteed 
   because we haven't done full setup here (e.g., no pgml mode)  *)
fun process_pgip str =
     setmp output_xml_fn (!pgip_output_channel) process_pgip_plain str

end

end;

