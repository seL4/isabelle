(*  Title:      Pure/ProofGeneral/proof_general_pgip.ML
    Author:     David Aspinall and Markus Wenzel

Isabelle configuration for Proof General using PGIP protocol.
See http://proofgeneral.inf.ed.ac.uk/kit
*)

signature PROOF_GENERAL_PGIP =
sig
  val proof_general_emacsN: string

  val new_thms_deps: theory -> theory -> string list * string list
  val init_pgip: bool -> unit             (* main PGIP loop with true; fail with false *)

  val pgip_channel_emacs: (string -> unit) -> unit

  (* More message functions... *)
  val nonfatal_error : string -> unit     (* recoverable (batch) error: carry on scripting *)
  val log_msg : string -> unit            (* for internal log messages *)
  val error_with_pos : PgipTypes.displayarea -> PgipTypes.fatality -> Position.T -> string -> unit

  val get_currently_open_file : unit -> Path.T option  (* interface focus *)
  val add_preference: string -> Preferences.preference -> unit
end

structure ProofGeneralPgip : PROOF_GENERAL_PGIP =
struct

open Pgip;


(** print mode **)

val proof_general_emacsN = "ProofGeneralEmacs";
val proof_generalN = "ProofGeneral";
val pgmlsymbols_flag = Unsynchronized.ref true;


(* assembling and issuing PGIP packets *)

val pgip_refid = Unsynchronized.ref NONE: string option Unsynchronized.ref;
val pgip_refseq = Unsynchronized.ref NONE: int option Unsynchronized.ref;

local
  val pgip_class  = "pg"
  val pgip_tag = "Isabelle/Isar"
  val pgip_id = Unsynchronized.ref ""
  val pgip_seq = Unsynchronized.ref 0
  fun pgip_serial () = Unsynchronized.inc pgip_seq

  fun assemble_pgips pgips =
    Pgip { tag = SOME pgip_tag,
           class = pgip_class,
           seq = pgip_serial (),
           id = ! pgip_id,
           destid = ! pgip_refid,
           (* destid=refid since Isabelle only communicates back to sender *)
           refid = ! pgip_refid,
           refseq = ! pgip_refseq,
           content = pgips }
in

fun init_pgip_session_id () =
    pgip_id := getenv "HOSTNAME" ^ "/" ^ getenv "USER" ^ "/" ^
               getenv "ISABELLE_PID" ^ "/" ^ Time.toString (Time.now ())

fun matching_pgip_id id = (id = ! pgip_id)

val output_xml_fn = Unsynchronized.ref Output.physical_writeln
fun output_xml s = ! output_xml_fn (XML.string_of s);

val output_pgips = XML.string_of o PgipOutput.output o assemble_pgips o map PgipOutput.output;

val output_pgmlterm = XML.string_of o Pgml.pgmlterm_to_xml;
val output_pgmltext = XML.string_of o Pgml.pgml_to_xml;


fun issue_pgip_rawtext str =
  output_xml (PgipOutput.output (assemble_pgips (YXML.parse_body str)));

fun issue_pgip pgipop =
  output_xml (PgipOutput.output (assemble_pgips [PgipOutput.output pgipop]));

end;



(** messages and notification **)

(* PGML terms *)

local

fun pgml_sym s =
  if ! pgmlsymbols_flag then
    (case Symbol.decode s of
      Symbol.Sym name => Pgml.Sym {name = name, content = s}
    | _ => Pgml.Str s)
  else Pgml.Str s;

val pgml_syms = map pgml_sym o Symbol.explode;

val token_markups =
 [Isabelle_Markup.tfreeN, Isabelle_Markup.tvarN, Isabelle_Markup.freeN,
  Isabelle_Markup.boundN, Isabelle_Markup.varN, Isabelle_Markup.skolemN];

fun get_int props name =
  (case Properties.get props name of NONE => NONE | SOME s => Int.fromString s);

in

fun pgml_terms (XML.Elem ((name, atts), body)) =
      if member (op =) token_markups name then
        let val content = pgml_syms (XML.content_of body)
        in [Pgml.Atoms {kind = SOME name, content = content}] end
      else
        let val content = maps pgml_terms body in
          if name = Isabelle_Markup.blockN then
            [Pgml.Box {orient = NONE,
              indent = get_int atts Isabelle_Markup.indentN, content = content}]
          else if name = Isabelle_Markup.breakN then
            [Pgml.Break {mandatory = NONE, indent = get_int atts Isabelle_Markup.widthN}]
          else content
        end
  | pgml_terms (XML.Text text) = map (Pgml.Raw o Pgml.atom_to_xml) (pgml_syms text);

end;


(* messages *)

fun pgml area content =
  Pgml.Pgml {version = NONE, systemid = NONE, area = SOME area, content = content};

fun message_content default_area s =
  let
    val body = YXML.parse_body s;
    val area =
      (case body of
        [XML.Elem ((name, _), _)] =>
          if name = Isabelle_Markup.stateN then PgipTypes.Display else default_area
      | _ => default_area);
  in Pgml.pgml_to_xml (pgml area (maps pgml_terms body)) end;


fun normalmsg area s = issue_pgip
  (Normalresponse {content = [message_content area s]});

fun errormsg area fatality s = issue_pgip
  (Errorresponse {fatality = fatality, location = NONE, content = [message_content area s]});

(*error responses with useful locations*)
fun error_with_pos area fatality pos s = issue_pgip
  (Errorresponse {
    fatality = fatality,
    location = SOME (PgipIsabelle.location_of_position pos),
    content = [message_content area s]});

fun panic s = (errormsg Message Panic ("## SYSTEM EXIT ##\n" ^ s); exit 1);
fun nonfatal_error s = errormsg Message Nonfatal s;
fun log_msg s = errormsg Message Log s;

(* NB: all of standard functions print strings terminated with new lines, but we don't
   add new lines explicitly in PGIP: they are left implicit.  It means that PGIP messages
   can't be written without newlines. *)
fun setup_messages () =
 (Output.Private_Hooks.writeln_fn := (fn s => normalmsg Message s);
  Output.Private_Hooks.status_fn := (fn _ => ());
  Output.Private_Hooks.report_fn := (fn _ => ());
  Output.Private_Hooks.urgent_message_fn := (fn s => normalmsg Status s);
  Output.Private_Hooks.tracing_fn := (fn s => normalmsg Tracing s);
  Output.Private_Hooks.warning_fn := (fn s => errormsg Message Warning s);
  Output.Private_Hooks.error_fn := (fn (_, s) => errormsg Message Fatal s));


(* immediate messages *)

fun tell_clear_goals () =
    issue_pgip (Normalresponse { content = [Pgml.pgml_to_xml (pgml Display [])] })
fun tell_clear_response () =
    issue_pgip (Normalresponse { content = [Pgml.pgml_to_xml (pgml Message [])] })

fun tell_file_loaded completed path   =
    issue_pgip (Informfileloaded {url=PgipTypes.pgipurl_of_path path,
                                  completed=completed})
fun tell_file_outdated completed path   =
    issue_pgip (Informfileoutdated {url=PgipTypes.pgipurl_of_path path,
                                    completed=completed})
fun tell_file_retracted completed path =
    issue_pgip (Informfileretracted {url=PgipTypes.pgipurl_of_path path,
                                     completed=completed})


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
  if action = Thy_Info.Update then
    List.app (tell_file_loaded true) (Thy_Info.loaded_files name)
  else if action = Thy_Info.Remove then
      List.app (tell_file_retracted true) (Thy_Info.loaded_files name)
  else ()


in
  fun setup_thy_loader () = Thy_Info.add_hook trace_action;
  fun sync_thy_loader () = List.app (trace_action Thy_Info.Update) (Thy_Info.get_names ());
end;


(* get informed about files *)

val thy_name = Path.implode o #1 o Path.split_ext o Path.base;

val inform_file_retracted = Thy_Info.kill_thy o thy_name;

fun inform_file_processed path state =
  let val name = thy_name path in
    if Toplevel.is_toplevel state then
      Thy_Info.register_thy (Toplevel.end_theory Position.none state)
        handle ERROR msg =>
          (warning (cat_lines [msg, "Failed to register theory: " ^ quote name]);
            tell_file_retracted true (Path.base path))
    else raise Toplevel.UNDEF
  end;


(* restart top-level loop (keeps most state information) *)

val welcome = Output.urgent_message o Session.welcome;

fun restart () =
    (sync_thy_loader ();
     tell_clear_goals ();
     tell_clear_response ();
     Isar.init ();
     welcome ());


(* theorem dependencies *)

local

fun add_proof_body (PBody {thms, ...}) =
  thms |> fold (fn (_, (name, _, _)) => name <> "" ? Symtab.update (name, ()));

fun add_thm th =
  (case Thm.proof_body_of th of 
    PBody {proof = PThm (_, ((name, _, _), body)), ...} =>
      if Thm.has_name_hint th andalso Thm.get_name_hint th = name
      then add_proof_body (Future.join body)
      else I
  | body => add_proof_body body);

in

fun thms_deps ths =
  let
    (* FIXME proper derivation names!? *)
    val names = map Thm.get_name_hint (filter Thm.has_name_hint ths);
    val deps = Symtab.keys (fold add_thm ths Symtab.empty);
  in (names, deps) end;

fun new_thms_deps thy thy' =
  let
    val prev_facts = Global_Theory.facts_of thy;
    val facts = Global_Theory.facts_of thy';
  in thms_deps (maps #2 (Facts.dest_static [prev_facts] facts)) end;

end;


(* theorem dependeny output *)

val show_theorem_dependencies = Unsynchronized.ref false;

local

val spaces_quote = space_implode " " o map quote;

fun thm_deps_message (thms, deps) =
  let
    val valuethms = XML.Elem (("value", [("name", "thms")]), [XML.Text thms]);
    val valuedeps = XML.Elem (("value", [("name", "deps")]), [XML.Text deps]);
  in
    issue_pgip (Metainforesponse
      {attrs = [("infotype", "isabelle_theorem_dependencies")],
       content = [valuethms, valuedeps]})
  end;

in

fun setup_present_hook () = Toplevel.add_hook (fn _ => fn state => fn state' =>
  if ! show_theorem_dependencies andalso
    can Toplevel.theory_of state andalso Toplevel.is_theory state'
  then
    let val (names, deps) = new_thms_deps (Toplevel.theory_of state) (Toplevel.theory_of state') in
      if null names orelse null deps then ()
      else thm_deps_message (spaces_quote names, spaces_quote deps)
    end
  else ());

end;


(** lexicalstructure element with keywords (PGIP version of elisp keywords file) **)

fun lexicalstructure_keywords () =
    let val (keywords, commands) = Keyword.dest ()
        fun keyword_elt kind keyword =
            XML.Elem (("keyword", [("word", keyword), ("category", kind)]), [])
        in
            Lexicalstructure
              {content = map (keyword_elt "minor") keywords @ map (keyword_elt "major") commands}
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
                   (panic ("Error in URL in environment variable ISABELLE_HOMEPAGE.");
                        Url.explode isabellewww)

        val proverinfo =
            Proverinfo { name = "Isabelle",
                         version = Distribution.version,
                         instance = Session.name(),
                         descr = "The Isabelle/Isar theorem prover",
                         url = wwwpage,
                         filenameextns = ".thy;" }
    in
        if ex then
            (issue_pgip proverinfo;
             issue_pgip_rawtext (File.read path);
             issue_pgip (lexicalstructure_keywords()))
        else panic ("PGIP configuration file \"" ^ config_file() ^ "\" not found")
    end;
end


(* Preferences: tweak for PGIP interfaces *)

val preferences = Unsynchronized.ref Preferences.pure_preferences;

fun add_preference cat pref =
  CRITICAL (fn () => Unsynchronized.change preferences (Preferences.add cat pref));

fun setup_preferences_tweak () =
  CRITICAL (fn () => Unsynchronized.change preferences
   (Preferences.set_default ("show-question-marks", "false") #>
    Preferences.remove "show-question-marks" #>   (* we use markup, not ?s *)
    Preferences.remove "theorem-dependencies" #>  (* set internally *)
    Preferences.remove "full-proofs"));           (* set internally *)



(* Sending commands to Isar *)

fun isarcmd s = Isar.>>> (Outer_Syntax.parse Position.none s);

(* TODO:
    - apply a command given a transition function;
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

fun askpgip (Askpgip _) =
    (issue_pgip
         (Usespgip { version = PgipIsabelle.isabelle_pgip_version_supported,
                     pgipelems = PgipIsabelle.accepted_inputs });
     send_pgip_config())

fun askpgml (Askpgml _) =
    issue_pgip
        (Usespgml { version = PgipIsabelle.isabelle_pgml_version_supported })

fun askprefs (Askprefs _) =
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

fun askconfig (Askconfig _) = () (* TODO: add config response *)

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

fun proverinit _ = restart ()

fun proverexit _ = isarcmd "quit"

fun set_proverflag_quiet b =
    isarcmd (if b then "disable_pr" else "enable_pr")

fun set_proverflag_pgmlsymbols b =
    (pgmlsymbols_flag := b;
      NAMED_CRITICAL "print_mode" (fn () =>
        Unsynchronized.change print_mode
            (fn mode =>
                remove (op =) Symbol.xsymbolsN mode @ (if b then [Symbol.xsymbolsN] else []))))

fun set_proverflag_thmdeps b =
    (show_theorem_dependencies := b;
     Proofterm.proofs := (if b then 1 else 2))

fun setproverflag (Setproverflag vs) =
    let
        val flagname = #flagname vs
        val value = #value vs
    in
        (case flagname of
             "quiet"            => set_proverflag_quiet value
           | "pgmlsymbols"      => set_proverflag_pgmlsymbols value
           | "metainfo:thmdeps" => set_proverflag_thmdeps value
           | _ => log_msg ("Unrecognised prover control flag: " ^
                           (quote flagname) ^ " ignored."))
    end


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
        isarcmd ("undos_proof " ^ string_of_int times)
    end

fun redostep _ = raise Fail "redo unavailable"

fun abortgoal _ = isarcmd "kill" (* was: ProofGeneral.kill_proof *)


(*** PGIP identifier tables ***)

(* TODO: these ones should be triggered by hooks after a
   declaration addition/removal, to be sent automatically. *)

fun addids t  = issue_pgip (Addids {idtables = [t]})
fun delids t  = issue_pgip (Delids {idtables = [t]})


local

fun theory_facts thy =
  (map Global_Theory.facts_of (Theory.parents_of thy), Global_Theory.facts_of thy);

fun thms_of_thy name =
  let val thy = Thy_Info.get_theory name
  in map fst (theory_facts thy |-> Facts.extern_static (Proof_Context.init_global thy)) end;

fun qualified_thms_of_thy name =
  map fst (theory_facts (Thy_Info.get_theory name) |-> Facts.dest_static);

in

fun askids (Askids vs) =
    let
        val url = #url vs            (* ask for identifiers within a file *)
        val thyname = #thyname vs    (* ask for identifiers within a theory *)
        val objtype = #objtype vs    (* ask for identifiers of a particular type *)

        fun idtable ty ctx ids = {objtype=ty,context=ctx,ids=ids}

        fun setids t = issue_pgip (Setids {idtables = [t]})

        (* fake one-level nested "subtheories" by picking apart names. *)
        val immed_thms_of_thy = filter_out Long_Name.is_qualified o thms_of_thy
        fun thy_prefix s = case Long_Name.explode s of
                                    x::_::_ => SOME x  (* String.find? *)
                                  | _ => NONE
        fun subthys_of_thy s =
            List.foldl  (fn (NONE,xs) => xs | (SOME x,xs) => insert op= x xs) []
                   (map thy_prefix (thms_of_thy s))
        fun subthms_of_thy thy =
            (case thy_prefix thy of
                 NONE => immed_thms_of_thy thy
               | SOME prf => filter (String.isPrefix (unprefix (prf ^ Long_Name.separator) thy))
                                    (thms_of_thy prf))
    in
        case (thyname,objtype) of
           (NONE, NONE) =>
           setids (idtable ObjFile NONE (Thy_Info.get_names())) (*FIXME: uris*)
         | (NONE, SOME ObjFile) =>
           setids (idtable ObjFile NONE (Thy_Info.get_names())) (*FIXME: uris*)
         | (SOME fi, SOME ObjFile) =>
           setids (idtable ObjTheory (SOME fi) [fi])       (* TODO: check exists *)
         | (NONE, SOME ObjTheory) =>
           setids (idtable ObjTheory NONE (Thy_Info.get_names()))
         | (SOME thy, SOME ObjTheory) =>
           setids (idtable ObjTheory (SOME thy) (subthys_of_thy thy))
         | (SOME thy, SOME ObjTheorem) =>
           setids (idtable ObjTheorem (SOME thy) (subthms_of_thy thy))
         | (NONE, SOME ObjTheorem) =>
           (* A large query, but not unreasonable. ~5000 results for HOL.*)
           (* Several setids should be allowed, but Eclipse code is currently broken:
              List.app (fn thy => setids (idtable ObjTheorem (SOME thy) (subthms_of_thy thy)))
                         (Thy_Info.get_names()) *)
           setids (idtable ObjTheorem NONE (* this one gives ~7000 for HOL *)
                           (maps qualified_thms_of_thy (Thy_Info.get_names())))
         | _ => warning ("askids: ignored argument combination")
    end

end;

fun askrefs (Askrefs vs) =
    let
        val url = #url vs            (* ask for references of a file (i.e. immediate pre-requisites) *)
        val thyname = #thyname vs    (* ask for references of a theory (other theories) *)
        val objtype = #objtype vs    (* ask for references of a particular type... *)
        val name = #name vs          (*   ... with this name *)

        fun idtable ty ctx ids = {objtype=ty,context=ctx,ids=ids}

        val thy_name = Path.implode o #1 o Path.split_ext o Path.base

        fun filerefs f =
            let val thy = thy_name f
                val filerefs = map #1 (#uses (Thy_Load.check_thy (Path.dir f) thy))
            in
                issue_pgip (Setrefs {url=url, thyname=NONE, objtype=SOME PgipTypes.ObjFile,
                                     name=NONE, idtables=[], fileurls=filerefs})
            end

        fun thyrefs thy =
            let val thyrefs = #imports (Thy_Load.check_thy Path.current thy)
            in
                issue_pgip (Setrefs {url=url, thyname=thyname, objtype=SOME PgipTypes.ObjTheory,
                                     name=NONE, idtables=[{context=NONE, objtype=PgipTypes.ObjTheory,
                                                           ids=thyrefs}], fileurls=[]})
            end

        fun thmrefs thmname =
            let
                (* TODO: interim: this is probably not right.
                   What we want is mapping onto simple PGIP name/context model. *)
                val ctx = Toplevel.context_of (Isar.state ()) (* NB: raises UNDEF *)
                val thy = Proof_Context.theory_of ctx
                val ths = [Global_Theory.get_thm thy thmname]
                val deps = #2 (thms_deps ths);
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



fun showid (Showid vs) =
    let
        val thyname = #thyname vs
        val objtype = #objtype vs
        val name = #name vs

        val topthy = Toplevel.theory_of o Isar.state

        fun splitthy id =
            let val comps = Long_Name.explode id
            in case comps of
                   (thy::(rest as _::_)) => (Thy_Info.get_theory thy, Long_Name.implode rest)
                 | [plainid] => (topthy(),plainid)
                 | _ => raise Toplevel.UNDEF (* assert false *)
            end


        fun idvalue strings =
            issue_pgip (Idvalue { thyname=thyname, objtype=objtype, name=name,
                                  text=[XML.Elem (("pgml", []), maps YXML.parse_body strings)] })

        fun strings_of_thm (thy, name) =
          map (Display.string_of_thm_global thy) (Global_Theory.get_thms thy name)

        val string_of_thy = Pretty.string_of o Proof_Display.pretty_full_theory false
    in
        case (thyname, objtype) of
            (_, ObjTheory) => idvalue [string_of_thy (Thy_Info.get_theory name)]
          | (SOME thy, ObjTheorem) => idvalue (strings_of_thm (Thy_Info.get_theory thy, name))
          | (NONE, ObjTheorem) => idvalue (strings_of_thm (splitthy name))
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

val currently_open_file = Unsynchronized.ref (NONE : pgipurl option)

fun get_currently_open_file () = ! currently_open_file;

fun askguise _ =
    (* The "guise" is the PGIP abstraction of the prover's state.
       The <informguise> message is merely used for consistency checking. *)
    let
        val openfile = !currently_open_file

        val topthy = Toplevel.theory_of o Isar.state
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

        val doc = PgipParser.pgip_parser Position.none text

        val sysattrs = PgipTypes.opt_attr "systemdata" systemdata
        val locattrs = PgipTypes.attrs_of_location location
     in
        issue_pgip (Parseresult { attrs= sysattrs@locattrs,
                                  doc = doc,
                                  errs = [] })
    end

fun showproofstate _ = isarcmd "pr"

fun showctxt _ = isarcmd "print_context"

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
        isarcmd ("pretty_setmargin " ^ string_of_int width) (* FIXME: conversion back/forth! *)
    end

fun viewdoc (Viewdoc vs) =
    let
        val arg = #arg vs
    in
        isarcmd ("print_" ^ arg)   (* FIXME: isabelle doc?.  Return URLs, maybe? *)
    end

(*** Theory ***)

fun doitem (Doitem vs) =
    let
        val text = #text vs
    in
        isarcmd text
    end

fun undoitem _ =
    isarcmd "undo"

fun redoitem _ =
    isarcmd "redo"

fun aborttheory _ =
    isarcmd "kill"  (* was: "init_toplevel" *)

fun retracttheory (Retracttheory vs) =
    let
        val thyname = #thyname vs
    in
        isarcmd ("kill_thy " ^ quote thyname)
    end


(*** Files ***)

fun changecwd (Changecwd {url, ...}) =
  Thy_Load.set_master_path (PgipTypes.path_of_pgipurl url)

fun openfile (Openfile vs) =
  let
      val url = #url vs
      val filepath = PgipTypes.path_of_pgipurl url
      val filedir = Path.dir filepath
      val thy_name = Path.implode o #1 o Path.split_ext o Path.base
      val openfile_retract = Thy_Info.kill_thy o thy_name;
  in
      case !currently_open_file of
          SOME f => raise PGIP ("<openfile> when a file is already open!\nCurrently open file: " ^
                                PgipTypes.string_of_pgipurl url)
        | NONE => (openfile_retract filepath;
                   Thy_Load.set_master_path filedir;
                   Output.urgent_message ("Working in file: " ^ PgipTypes.string_of_pgipurl url);
                   currently_open_file := SOME url)
  end

fun closefile _ =
    case !currently_open_file of
        SOME f => (inform_file_processed f (Isar.state ());
                   Output.urgent_message
                    ("Finished working in file: " ^ PgipTypes.string_of_pgipurl f);
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

fun abortfile _ =
    case !currently_open_file of
        SOME f => (isarcmd "init_toplevel";
                   Output.urgent_message ("Aborted working in file: " ^
                             PgipTypes.string_of_pgipurl f);
                   currently_open_file := NONE)
      | NONE => raise PGIP ("<abortfile> when no file is open!")

fun retractfile (Retractfile vs) =
    let
        val url = #url vs
    in
        case !currently_open_file of
            SOME f => raise PGIP ("<retractfile> when a file is open!")
          | NONE => (Output.urgent_message ("Retracting file: " ^ PgipTypes.string_of_pgipurl url);
                     (* TODO: next should be in thy loader, here just for testing *)
                     let
                         val name = thy_name url
                     in List.app (tell_file_retracted false) (Thy_Info.loaded_files name) end;
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
fun quitpgip _ = raise PGIP_QUIT

fun process_input inp = case inp
 of Pgip.Askpgip _          => askpgip inp
  | Pgip.Askpgml _          => askpgml inp
  | Pgip.Askprefs _         => askprefs inp
  | Pgip.Askconfig _        => askconfig inp
  | Pgip.Getpref _          => getpref inp
  | Pgip.Setpref _          => setpref inp
  | Pgip.Proverinit _       => proverinit inp
  | Pgip.Proverexit _       => proverexit inp
  | Pgip.Setproverflag _    => setproverflag inp
  | Pgip.Dostep _           => dostep inp
  | Pgip.Undostep _         => undostep inp
  | Pgip.Redostep _         => redostep inp
  | Pgip.Forget _           => error "<forget> not implemented by Isabelle"
  | Pgip.Restoregoal _      => error "<restoregoal> not implemented by Isabelle"
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
                              (XML.string_of xml))
           | SOME inp => (process_input inp)) (* errors later; packet discarded *)
      | XML.Text t => ignored_text_warning t
and ignored_text_warning t =
    if size (Symbol.strip_blanks t) > 0 then
           warning ("Ignored text in PGIP packet: \n" ^ t)
    else ()

fun process_pgip_tree xml =
    (pgip_refid := NONE;
     pgip_refseq := NONE;
     (case xml of
          XML.Elem (("pgip", attrs), pgips) =>
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
            (Output.error_msg ((msg ^ "\nPGIP error occurred in XML text below:\n") ^
                               (XML.string_of xml));
             true))

(* External input *)

val process_pgip_plain = K () o process_pgip_tree o XML.parse

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
                                handle PGIP_QUIT => raise PGIP_QUIT
                                     | e => (handler (e,SOME src'); true)
             in
                 loop ready' src'
             end
    end handle e => handler (e,SOME src)  (* error in XML parse or Ready issue *)

and handler (e,srco) =
    if Exn.is_interrupt e andalso is_some srco then
        (Output.error_msg "Interrupt during PGIP processing"; loop true (the srco))
    else
        case (e,srco) of
            (XML_PARSE,SOME src) =>
            panic "Invalid XML input, aborting" (* TODO: attempt recovery  *)
          | (Toplevel.UNDEF,SOME src) =>
            (Output.error_msg "No working context defined"; loop true src)
          | (e,SOME src) =>
            (Output.error_msg (ML_Compiler.exn_message e); loop true src)
          | (PGIP_QUIT,_) => ()
          | (_,NONE) => ()
in
  (* TODO: add socket interface *)

  val xmlP = XML.parse_comments |-- XML.parse_element >> single

  val tty_src =
    Source.set_prompt "" (Source.source Symbol.stopper xmlP NONE (Source.tty TextIO.stdIn))

  fun pgip_toplevel x = loop true x
end


(* init *)

val initialized = Unsynchronized.ref false;

fun init_pgip false = panic "No Proof General interface support for Isabelle/classic mode."
  | init_pgip true =
      (if ! initialized then ()
       else
        (setup_preferences_tweak ();
         Output.add_mode proof_generalN Output.default_output Output.default_escape;
         Markup.add_mode proof_generalN YXML.output_markup;
         setup_messages ();
         setup_thy_loader ();
         setup_present_hook ();
         init_pgip_session_id ();
         welcome ();
         initialized := true);
       sync_thy_loader ();
       Unsynchronized.change print_mode (update (op =) proof_generalN);
       pgip_toplevel tty_src);



(** Out-of-loop PGIP commands (for Emacs hybrid mode) **)

local
    val pgip_output_channel = Unsynchronized.ref Output.physical_writeln
in

(* Set recipient for PGIP results *)
fun pgip_channel_emacs writefn =
    (init_pgip_session_id();
     pgip_output_channel := writefn)

(* Process a PGIP command.
   This works for preferences but not generally guaranteed
   because we haven't done full setup here (e.g., no pgml mode)  *)
fun process_pgip_emacs str =
     Unsynchronized.setmp output_xml_fn (!pgip_output_channel) process_pgip_plain str

end


(* Extra command for embedding prover-control inside document (obscure/debug usage). *)

val _ =
  Outer_Syntax.improper_command ("ProofGeneral.process_pgip", Keyword.control) "(internal)"
    (Parse.text >> (Toplevel.no_timing oo
      (fn txt => Toplevel.imperative (fn () =>
        if print_mode_active proof_general_emacsN
        then process_pgip_emacs txt
        else process_pgip_plain txt))));

end;
