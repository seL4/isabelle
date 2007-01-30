(*  Title:      Pure/ProofGeneral/proof_general_pgip.ML
    ID:         $Id$
    Author:     David Aspinall and Markus Wenzel

Isabelle configuration for Proof General using PGIP protocol.
See http://proofgeneral.inf.ed.ac.uk/kit
*)

signature PROOF_GENERAL_PGIP =
sig
  val init_pgip: bool -> unit             (* main PGIP loop with true; fail with false *)

  (* These two are just to support the semi-PGIP Emacs mode *)
  val init_pgip_channel: (string -> unit) -> unit
  val process_pgip: string -> unit

  (* Yet more message functions... *)
  val nonfatal_error : string -> unit     (* recoverable error *)
  val log_msg : string -> unit	          (* for internal log messages *)
  val error_with_pos : PgipTypes.fatality -> Position.T -> string -> unit

  val get_currently_open_file : unit -> Path.T option  (* interface focus *)
end

structure ProofGeneralPgip : PROOF_GENERAL_PGIP  =
struct

open Pgip;


(* print modes *)

val proof_generalN = "ProofGeneral";  (*token markup (colouring vars, etc.)*)
val pgmlN = "PGML";                   (*XML escapes and PGML symbol elements*)
val pgmlatomsN = "PGMLatoms";         (*variable kind decorations*)
val thm_depsN = "thm_deps";           (*meta-information about theorem deps*)


(* text output: print modes for xsymbol and PGML *)

local

fun xsym_output "\\" = "\\\\"
  | xsym_output s = if Symbol.is_raw s then Symbol.decode_raw s else s;

fun xsymbols_output s =
  if Output.has_mode Symbol.xsymbolsN andalso exists_string (equal "\\") s then
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
  Output.add_mode Symbol.xsymbolsN
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
        if ! delay_msgs then
            delayed_msgs := pgip :: ! delayed_msgs
        else issue_pgip pgip
in
    (* Normal responses are messages for the user *)
    fun normalmsg area cat urgent s =
        let
            val content = XML.Elem("pgmltext",[],[XML.Rawtext s])
            val pgip = Normalresponse {area=area,messagecategory=cat,
                                       urgent=urgent,content=[content] }
        in
            queue_or_issue pgip
        end

    (* Error responses are error messages for the user, or system-level messages *)
    fun errormsg fatality s =
        let
              val content = XML.Elem("pgmltext",[],[XML.Rawtext s])
              val pgip = Errorresponse {area=NONE,fatality=fatality,
                                        content=[content],
                                        location=NONE}
        in
            queue_or_issue pgip
        end

    (* Error responses with useful locations *)
    fun error_with_pos fatality pos s =
        let
              val content = XML.Elem("pgmltext",[],[XML.Rawtext s])
              val pgip = Errorresponse {area=NONE,fatality=fatality,
                                        content=[content],
                                        location=SOME (PgipIsabelle.location_of_position pos)}
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
(* NB 2: all of standard functions print strings terminated with new lines, but we don't
   add new lines explicitly in PGIP: they are left implicit.  It means that PGIP messages 
   can't be written without newlines. *)

fun setup_messages () =
 (writeln_fn := (fn s => normalmsg Message Normal false s);
  priority_fn := (fn s => normalmsg Message Normal true s);
  tracing_fn := (fn s => normalmsg  Message Tracing false s);
  info_fn := (fn s => errormsg Info s);
  warning_fn := (fn s => errormsg Warning s);
  error_fn := (fn s => errormsg Fatal s);
  panic_fn := (fn s => errormsg Panic s);
  debug_fn := (fn s => errormsg Debug s));

fun nonfatal_error s = errormsg Nonfatal s;
fun log_msg s = errormsg Log s;


(* immediate messages *)

fun tell_clear_goals ()      = issue_pgip (Cleardisplay {area=Display})
fun tell_clear_response ()   = issue_pgip (Cleardisplay {area=Message})

fun tell_file_loaded completed path   = 
    issue_pgip (Informfileloaded {url=PgipTypes.pgipurl_of_path path,
				  completed=completed})
fun tell_file_outdated completed path   = 
    issue_pgip (Informfileoutdated {url=PgipTypes.pgipurl_of_path path,
				    completed=completed})
fun tell_file_retracted completed path = 
    issue_pgip (Informfileretracted {url=PgipTypes.pgipurl_of_path path,
				     completed=completed})



(** theory / proof state output **)

local

fun statedisplay prts =
    let 
        val display = Pretty.output (Pretty.chunks prts)
        (* TODO: add extra PGML markup for allow proof state navigation *)
        val statedisplay = XML.Elem("statedisplay",[], [XML.Rawtext display])
    in
        issue_pgip (Proofstate {pgml=[XML.Elem("pgml",[],[statedisplay])]})
    end

fun print_current_goals n m st =
  case (Display.pretty_current_goals n m st) of 
   [] => tell_clear_goals()
 | prts => statedisplay prts

fun print_state b st =
  case (Toplevel.pretty_state b st) of 
   [] => tell_clear_goals() 
  | prts => statedisplay prts

in

fun setup_state () =
  (Display.print_current_goals_fn := print_current_goals;
   Toplevel.print_state_fn := print_state);

end;


(* theory loader actions *)

local
  (* da: TODO: PGIP has a completed flag so the prover can indicate to the 
     interface which files are busy performing a particular action. 
     To make use of this we need to adjust the hook in thy_info.ML
     (may actually be difficult to tell the interface *which* action is in 
      progress, but we could add a generic "Lock" action which uses
      informfileloaded: the broker/UI should not infer too much from incomplete
      operations).
   *)     
fun trace_action action name =
  if action = ThyInfo.Update then
    List.app (tell_file_loaded true) (ThyInfo.loaded_files name) 
  else if action = ThyInfo.Outdate then
    List.app (tell_file_outdated true) (ThyInfo.loaded_files name)
  else if action = ThyInfo.Remove then
      List.app (tell_file_retracted true) (ThyInfo.loaded_files name) 
  else ()


in
  fun setup_thy_loader () = ThyInfo.add_hook trace_action;
  fun sync_thy_loader () = List.app (trace_action ThyInfo.Update) (ThyInfo.names ());
end;


(* get informed about files *)

val thy_name = Path.implode o #1 o Path.split_ext o Path.base;

val inform_file_retracted = ThyInfo.if_known_thy ThyInfo.remove_thy o thy_name;
val inform_file_processed = ThyInfo.if_known_thy ThyInfo.touch_child_thys o thy_name;

fun proper_inform_file_processed path state =
  let val name = thy_name path in
    if Toplevel.is_toplevel state andalso ThyInfo.known_thy name then
     (ThyInfo.touch_child_thys name;
      ThyInfo.pretend_use_thy_only name handle ERROR msg =>
       (warning msg; warning ("Failed to register theory: " ^ quote name);
        tell_file_retracted true (Path.base path)))
    else raise Toplevel.UNDEF
  end;


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
fun tell_thm_deps ths =
  if Output.has_mode thm_depsN then
    let
      val names = filter_out (equal "") (map PureThy.get_name_hint ths); (* da: HAS THIS NOW BECOME "??.unknown"? *)
      val deps = filter_out (equal "")
        (Symtab.keys (fold Proofterm.thms_of_proof
          (map Thm.proof_of ths) Symtab.empty));
    in
      if null names orelse null deps then ()
      else thm_deps_message (spaces_quote names, spaces_quote deps)
    end
  else ();

in

fun setup_present_hook () =
  Present.add_hook (fn _ => fn res => tell_thm_deps (maps #2 res));

end;

(** lexicalstructure element with keywords (PGIP version of elisp keywords file) **)

fun lexicalstructure_keywords () =
    let val commands = OuterSyntax.dest_keywords ()
        fun category_of k = if k mem commands then "major" else "minor"
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
    fun orenv v d = case getenv v of "" => d  | s => s
    fun config_file()  = orenv "ISABELLE_PGIPCONFIG" staticconfig
    fun isabelle_www() = orenv "ISABELLE_HOMEPAGE" isabellewww
in
fun send_pgip_config () =
    let
        val path = Path.explode (config_file())
        val ex = File.exists path

        val wwwpage =
            (Url.explode (isabelle_www()))
            handle ERROR _ =>
                   (Output.panic
                        ("Error in URL in environment variable ISABELLE_HOMEPAGE.");
                        Url.explode isabellewww)

        val proverinfo =
            Proverinfo { name = "Isabelle",
                         version = version,
                         instance = Session.name(),
                         descr = "The Isabelle/Isar theorem prover",
                         url = wwwpage,
                         filenameextns = ".thy;" }
    in
        if ex then
            (issue_pgip proverinfo;
             issue_pgip_rawtext (File.read path);
             issue_pgip (lexicalstructure_keywords()))
        else Output.panic ("PGIP configuration file \"" ^ config_file() ^ "\" not found")
    end;
end


(* Preferences: tweak for PGIP interfaces *)

val preferences = ref Preferences.preferences;

fun setup_preferences_tweak() =
    preferences :=
     (* PGIP uses markup for distinguishing variable types *)
     (!preferences |> Preferences.set_default ("show-question-marks","false")
	           |> Preferences.remove "show-question-marks");
		 


(* Sending commands to Isar *)

fun isarcmd s =
    s |> OuterSyntax.scan |> OuterSyntax.read
      (*|> map (Toplevel.position (Position.name "PGIP message") o #3)*)
      |> map #3
      |> Toplevel.>>>;

(* TODO:
    - apply a command given a transition function, e.g. IsarCmd.undo.
    - fix position from path of currently open file [line numbers risk garbling though].
*)

(* load an arbitrary file (must be .thy or .ML) *)

fun use_thy_or_ml_file file =
    let
        val (path,extn) = Path.split_ext (Path.explode file)
    in
        case extn of
            "" => isarcmd ("use_thy " ^ quote (Path.implode path))
          | "thy" => isarcmd ("use_thy " ^ quote (Path.implode path))
          | "ML" => isarcmd ("use " ^ quote file)
          | other => error ("Don't know how to read a file with extension " ^ quote other)
    end


(******* PGIP actions *******)


(* Responses to each of the PGIP input commands.
   These are programmed uniformly for extensibility. *)

fun askpgip (Askpgip vs) =
    issue_pgip
        (Usespgip { version = PgipIsabelle.isabelle_pgip_version_supported,
                    pgipelems = PgipIsabelle.accepted_inputs })

fun askpgml (Askpgml vs) =
    issue_pgip
        (Usespgml { version = PgipIsabelle.isabelle_pgml_version_supported })

fun askprefs (Askprefs vs) =
    let
        fun preference_of {name, descr, default, pgiptype, get, set } =
            { name = name, descr = SOME descr, default = SOME default,
              pgiptype = pgiptype }
    in
        List.app (fn (prefcat, prefs) =>
                     issue_pgip (Hasprefs {prefcategory=SOME prefcat,
                                           prefs=map preference_of prefs}))
                 (!preferences)
    end

fun askconfig (Askconfig vs) = () (* TODO: add config response *)

local
    fun lookuppref pref =
        case AList.lookup (op =)
                          (map (fn p => (#name p,p))
                               (maps snd (!preferences))) pref of
            NONE => error ("Unknown prover preference: " ^ quote pref)
          | SOME p => p
in
fun setpref (Setpref vs) =
    let
        val name = #name vs
        val value = #value vs
        val set = #set (lookuppref name)
    in
        set value
    end

fun getpref (Getpref vs) =
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

fun dostep (Dostep vs) =
    let
        val text = #text vs
    in
        isarcmd text
    end

fun undostep (Undostep vs) =
    let
        val times = #times vs
    in
        isarcmd ("undos_proof " ^ Int.toString times)
    end

fun redostep vs = isarcmd "redo"

fun abortgoal vs = isarcmd "kill" (* was: ProofGeneral.kill_proof *)


(*** PGIP identifier tables ***)

(* TODO: these ones should be triggered by hooks after a 
   declaration addition/removal, to be sent automatically. *)

fun addids t  = issue_pgip (Addids {idtables = [t]})
fun delids t  = issue_pgip (Delids {idtables = [t]})

fun askids (Askids vs) =
    let
        val url = #url vs            (* ask for identifiers within a file *)
        val thyname = #thyname vs    (* ask for identifiers within a theory *)
        val objtype = #objtype vs    (* ask for identifiers of a particular type *)

        fun idtable ty ctx ids = {objtype=ty,context=ctx,ids=ids}

	fun setids t  = issue_pgip (Setids {idtables = [t]})

        val thms_of_thy = map fst o PureThy.thms_of o ThyInfo.get_theory
    in
(*      case (url_attr,thyname,objtype) of
            (NONE,NONE,NONE) =>
*)          (* top-level: return *)

        (* TODO: add askids for "file" here, which returns single theory with same name *)
        (* FIXME: objtypes on both sides *)
        case (thyname,objtype) of
           (* only files known in top context *)
           (NONE, NONE)               => setids (idtable ObjFile NONE (ThyInfo.names())) (*FIXME: uris?*)
         | (NONE, SOME ObjFile)        => setids (idtable ObjFile NONE (ThyInfo.names())) (* ditto *)
         | (SOME fi, SOME ObjFile)     => setids (idtable ObjTheory (SOME fi) [fi]) (* FIXME: lookup file *)
         | (NONE, SOME ObjTheory)      => setids (idtable ObjTheory NONE (ThyInfo.names()))
         | (SOME thy, SOME ObjTheory)  => setids (idtable ObjTheory (SOME thy) (ThyInfo.get_succs thy))
         | (SOME thy, SOME ObjTheorem) => setids (idtable ObjTheorem (SOME thy) (thms_of_thy thy))
         (* next case is both of above.  FIXME: cleanup this *)
         | (SOME thy, NONE) => (setids (idtable ObjTheory (SOME thy) (ThyInfo.get_preds thy));
                                setids (idtable ObjTheorem (SOME thy) (thms_of_thy thy)))
         | (_, SOME ot) => error ("No objects of type "^(PgipTypes.name_of_objtype ot)^" are available here.")
    end

fun askrefs (Askrefs vs) =
    let
        val url = #url vs            (* ask for references of a file (i.e. immediate pre-requisites) *)
        val thyname = #thyname vs    (* ask for references of a theory (other theories) *)
        val objtype = #objtype vs    (* ask for references of a particular type... *)
        val name = #name vs          (*   ... with this name *)

        fun idtable ty ctx ids = {objtype=ty,context=ctx,ids=ids}

        val thms_of_thy = map fst o PureThy.thms_of o ThyInfo.get_theory

	val thy_name = Path.implode o #1 o Path.split_ext o Path.base

	fun filerefs f = 
	    let val thy = thy_name f
		val (_,filerefs) = OuterSyntax.deps_thy thy true f (* (Path.unpack f); *)
	    in 
		issue_pgip (Setrefs {url=url, thyname=NONE, objtype=SOME PgipTypes.ObjFile,
				     name=NONE, idtables=[], fileurls=filerefs})
	    end

	fun thyrefs thy = 
	    let val ml_path = ThyLoad.ml_path thy
		val (thyrefs,_) = OuterSyntax.deps_thy thy true ml_path (* (Path.unpack f); *)
	    in 
		issue_pgip (Setrefs {url=url, thyname=thyname, objtype=SOME PgipTypes.ObjTheory,
				     name=NONE, idtables=[{context=NONE, objtype=PgipTypes.ObjTheory,
							   ids=thyrefs}], fileurls=[]})
	    end

	fun thmrefs thmname = 
	    let
		(* TODO: interim: this is probably not right.  
		   What we want is mapping onto simple PGIP name/context model. *)
		val ctx = Toplevel.context_of (Toplevel.get_state()) (* NB: raises UNDEF *)
		val thy = Context.theory_of_proof ctx
		val ths = [PureThy.get_thm thy (PureThy.Name thmname)]
		val deps = filter_out (equal "")
				      (Symtab.keys (fold Proofterm.thms_of_proof
							 (map Thm.proof_of ths) Symtab.empty))
	    in
		if null deps then ()
		else issue_pgip (Setrefs {url=url, thyname=thyname, name=name,
					  objtype=SOME PgipTypes.ObjTheorem,
					  idtables=[{context=NONE, objtype=PgipTypes.ObjTheorem,
						     ids=deps}], fileurls=[]})
	    end 
    in
        case (url,thyname,objtype,name) of
	    (SOME file, NONE, _, _)  => filerefs file           
	  | (_,SOME thy,_,_)         => thyrefs thy
	  | (_,_,SOME PgipTypes.ObjTheorem,SOME thmname) => thmrefs thmname
          | _  => error ("Unimplemented/invalid case of <askrefs>")
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
fun showid (Showid vs) =
    let
        val thyname = #thyname vs
        val objtype = #objtype vs
        val name = #name vs
        val topthy = Toplevel.theory_of o Toplevel.get_state

        fun idvalue objtype name strings =
            Idvalue { name=name, objtype=objtype,
                      text=[XML.Elem("pgmltext",[],map XML.Text strings)] }

        fun pthm thy name = print_thm (get_thm thy (Name name))
    in
        case (thyname, objtype) of
            (_,ObjTheory) =>
            with_displaywrap (idvalue ObjTheory name)
                             (fn ()=>(print_theory (ThyInfo.get_theory name)))
          | (SOME thy, ObjTheorem) =>
            with_displaywrap (idvalue ObjTheorem name)
                             (fn ()=>(pthm (ThyInfo.get_theory thy) name))
          | (NONE, ObjTheorem) =>
            with_displaywrap (idvalue ObjTheorem name)
                             (fn ()=>pthm (topthy()) name)
          | (_, ot) => error ("Cannot show objects of type "^(PgipTypes.name_of_objtype ot))
    end

(*** Inspecting state ***)

(* The file which is currently being processed interactively.
   In the pre-PGIP code, this was informed to Isabelle and the theory loader
   on completion, but that allows for circularity in case we read
   ourselves.  So PGIP opens the filename at the start of a script.
   We ought to prevent problems by modifying the theory loader to know
   about this special status, but for now we just keep a local reference.
*)

val currently_open_file = ref (NONE : pgipurl option)

fun get_currently_open_file () = ! currently_open_file;

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

fun parsescript (Parsescript vs) =
    let
        val text = #text vs
        val systemdata = #systemdata vs
        val location = #location vs   (* TODO: extract position *)

        val _ = start_delay_msgs ()   (* gather parsing errs/warns *)
        val doc = PgipParser.pgip_parser text
        val errs = end_delayed_msgs ()

        val sysattrs = PgipTypes.opt_attr "systemdata" systemdata
        val locattrs = PgipTypes.attrs_of_location location
     in
        issue_pgip (Parseresult { attrs= sysattrs@locattrs,
                                  doc = doc,
                                  errs = map PgipOutput.output errs })
    end

fun showproofstate vs = isarcmd "pr"

fun showctxt vs = isarcmd "print_context"

fun searchtheorems (Searchtheorems vs) =
    let
        val arg = #arg vs
    in
        isarcmd ("find_theorems " ^ arg)
    end

fun setlinewidth (Setlinewidth vs) =
    let
        val width = #width vs
    in
        isarcmd ("pretty_setmargin " ^ Int.toString width) (* FIXME: conversion back/forth! *)
    end

fun viewdoc (Viewdoc vs) =
    let
        val arg = #arg vs
    in
        isarcmd ("print_" ^ arg)   (* FIXME: isatool doc?.  Return URLs, maybe? *)
    end

(*** Theory ***)

fun doitem (Doitem vs) =
    let
        val text = #text vs
    in
        isarcmd text
    end

fun undoitem vs =
    isarcmd "undo"

fun redoitem vs =
    isarcmd "redo"

fun aborttheory vs =
    isarcmd "kill"  (* was: "init_toplevel" *)

fun retracttheory (Retracttheory vs) =
    let
        val thyname = #thyname vs
    in
        isarcmd ("kill_thy " ^ quote thyname)
    end


(*** Files ***)

(* Path management: we allow theory files to have dependencies in
   their own directory, but when we change directory for a new file we
   remove the path.  Leaving it there can cause confusion with
   difference in batch mode.
   NB: PGIP does not assume that the prover has a load path.
*)

local
    val current_working_dir = ref (NONE : string option)
in
fun changecwd_dir newdirpath =
   let
       val newdir = File.platform_path newdirpath
   in
       (case (!current_working_dir) of
            NONE => ()
          | SOME dir => ThyLoad.del_path dir;
        ThyLoad.add_path newdir;
        current_working_dir := SOME newdir)
   end
end

fun changecwd (Changecwd vs) =
    let
        val url = #url vs
        val newdir = PgipTypes.path_of_pgipurl url
    in
        changecwd_dir url
    end

fun openfile (Openfile vs) =
  let
      val url = #url vs
      val filepath = PgipTypes.path_of_pgipurl url
      val filedir = Path.dir filepath
      val thy_name = Path.implode o #1 o Path.split_ext o Path.base
      val openfile_retract = Output.no_warnings (ThyInfo.if_known_thy ThyInfo.remove_thy) o thy_name;
  in
      case !currently_open_file of
          SOME f => raise PGIP ("<openfile> when a file is already open!\nCurrently open file: " ^
				PgipTypes.string_of_pgipurl url)
        | NONE => (openfile_retract filepath;
                   changecwd_dir filedir;
		   priority ("Working in file: " ^ PgipTypes.string_of_pgipurl url);
                   currently_open_file := SOME url)
  end

fun closefile vs =
    case !currently_open_file of
        SOME f => (proper_inform_file_processed f (Isar.state());
		   priority ("Finished working in file: " ^ PgipTypes.string_of_pgipurl f);
                   currently_open_file := NONE)
      | NONE => raise PGIP ("<closefile> when no file is open!")

fun loadfile (Loadfile vs) =
    let
        val url = #url vs
    in
        (* da: this doesn't seem to cause a problem, batch loading uses
           a different state context.  Of course confusion is still possible,
           e.g. file loaded depends on open file which is not yet saved. *)
        (* case !currently_open_file of
            SOME f => raise PGIP ("<loadfile> when a file is open!\nCurrently open file: " ^
				  PgipTypes.string_of_pgipurl url)
          | NONE => *)
	use_thy_or_ml_file (File.platform_path url)
    end

fun abortfile vs =
    case !currently_open_file of
        SOME f => (isarcmd "init_toplevel";
		   priority ("Aborted working in file: " ^ 
			     PgipTypes.string_of_pgipurl f);
                   currently_open_file := NONE)
      | NONE => raise PGIP ("<abortfile> when no file is open!")

fun retractfile (Retractfile vs) =
    let
        val url = #url vs
    in
        case !currently_open_file of
            SOME f => raise PGIP ("<retractfile> when a file is open!")
          | NONE => (priority ("Retracting file: " ^ PgipTypes.string_of_pgipurl url);
		     (* TODO: next should be in thy loader, here just for testing *)
		     let 
			 val name = thy_name url
		     in List.app (tell_file_retracted false) (ThyInfo.loaded_files name) end;
		     inform_file_retracted url)
    end


(*** System ***)

fun systemcmd (Systemcmd vs) =
  let
      val arg = #arg vs
  in
      isarcmd arg
  end

exception PGIP_QUIT;
fun quitpgip vs = raise PGIP_QUIT

fun process_input inp = case inp
 of Pgip.Askpgip _          => askpgip inp
  | Pgip.Askpgml _          => askpgml inp
  | Pgip.Askprefs _         => askprefs inp
  | Pgip.Askconfig _        => askconfig inp
  | Pgip.Getpref _          => getpref inp
  | Pgip.Setpref _          => setpref inp
  | Pgip.Proverinit _       => proverinit inp
  | Pgip.Proverexit _       => proverexit inp
  | Pgip.Startquiet _       => startquiet inp
  | Pgip.Stopquiet _        => stopquiet inp
  | Pgip.Pgmlsymbolson _    => pgmlsymbolson inp
  | Pgip.Pgmlsymbolsoff _   => pgmlsymbolsoff inp
  | Pgip.Dostep _           => dostep inp
  | Pgip.Undostep _         => undostep inp
  | Pgip.Redostep _         => redostep inp
  | Pgip.Forget _           => error "<forget> not implemented"
  | Pgip.Restoregoal _      => error "<restoregoal> not implemented"
  | Pgip.Abortgoal _        => abortgoal inp
  | Pgip.Askids _           => askids inp
  | Pgip.Askrefs _          => askrefs inp
  | Pgip.Showid _           => showid inp
  | Pgip.Askguise _         => askguise inp
  | Pgip.Parsescript _      => parsescript inp
  | Pgip.Showproofstate _   => showproofstate inp
  | Pgip.Showctxt _         => showctxt inp
  | Pgip.Searchtheorems _   => searchtheorems inp
  | Pgip.Setlinewidth _     => setlinewidth inp
  | Pgip.Viewdoc _          => viewdoc inp
  | Pgip.Doitem _           => doitem inp
  | Pgip.Undoitem _         => undoitem inp
  | Pgip.Redoitem _         => redoitem inp
  | Pgip.Aborttheory _      => aborttheory inp
  | Pgip.Retracttheory _    => retracttheory inp
  | Pgip.Loadfile _         => loadfile inp
  | Pgip.Openfile _         => openfile inp
  | Pgip.Closefile _        => closefile inp
  | Pgip.Abortfile _        => abortfile inp
  | Pgip.Retractfile _      => retractfile inp
  | Pgip.Changecwd _        => changecwd inp
  | Pgip.Systemcmd _        => systemcmd inp
  | Pgip.Quitpgip _         => quitpgip inp


fun process_pgip_element pgipxml =
    case pgipxml of
        xml as (XML.Elem elem) =>
        (case Pgip.input elem of
             NONE => warning ("Unrecognized PGIP command, ignored: \n" ^
                              (XML.string_of_tree xml))
           | SOME inp => (process_input inp)) (* errors later; packet discarded *)
      | XML.Text t => ignored_text_warning t
      | XML.Rawtext t => ignored_text_warning t
and ignored_text_warning t =
    if size (Symbol.strip_blanks t) > 0 then
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
               val seq = PgipTypes.read_pgipnat (PgipTypes.get_attr "seq" attrs)
               (* Respond to prover broadcasts, or messages for us. Ignore rest *)
               val processit =
                   case dest of
                       NONE =>    class = "pa"
                     | SOME id => matching_pgip_id id
           in if processit then
                  (pgip_refid :=  PgipTypes.get_attr_opt "id" attrs;
                   pgip_refseq := SOME seq;
                   List.app process_pgip_element pgips;
                   (* return true to indicate <ready/> *)
                   true)
              else
                  (* no response to ignored messages. *)
                  false
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
        val pgipo =
          (case try Source.get_single src of
            SOME pgipo => pgipo
          | NONE => raise XML_PARSE)
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


local
(* Extra command for embedding prover-control inside document (obscure/debug usage). *)

val process_pgipP =
  OuterSyntax.improper_command "ProofGeneral.process_pgip" "(internal)" OuterKeyword.control
    (OuterParse.text >> (Toplevel.no_timing oo
      (fn txt => Toplevel.imperative (fn () => process_pgip_plain txt))));

in

 fun init_outer_syntax () = OuterSyntax.add_parsers [process_pgipP];

end



(* init *)

val initialized = ref false;

fun init_pgip false =
      Output.panic "No Proof General interface support for Isabelle/classic mode."
  | init_pgip true =
      (! initialized orelse
        (setmp warning_fn (K ()) init_outer_syntax ();
          PgipParser.init ();
	  setup_preferences_tweak ();
          setup_xsymbols_output ();
          setup_pgml_output ();
          setup_messages ();
          setup_state ();
          setup_thy_loader ();
          setup_present_hook ();
          init_pgip_session_id ();
          welcome ();
          set initialized);
        sync_thy_loader ();
       change print_mode (cons proof_generalN o remove (op =) proof_generalN);
       change print_mode (append [pgmlN, pgmlatomsN] o subtract (op =) [pgmlN, pgmlatomsN]);
       pgip_toplevel tty_src);



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

