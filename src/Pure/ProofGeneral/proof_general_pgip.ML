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

  (* More message functions... *)
  val nonfatal_error : string -> unit     (* recoverable (batch) error: carry on scripting *)
  val log_msg : string -> unit            (* for internal log messages *)
  val error_with_pos : PgipTypes.displayarea -> PgipTypes.fatality -> Position.T -> string -> unit

  val get_currently_open_file : unit -> Path.T option  (* interface focus *)
end

structure ProofGeneralPgip : PROOF_GENERAL_PGIP  =
struct

open Pgip;


(** print mode **)

val proof_generalN = "ProofGeneral";
val pgmlsymbols_flag = ref true;


(* symbol output *)

local

fun xsym_output "\\" = "\\\\"
  | xsym_output s = if Symbol.is_raw s then Symbol.decode_raw s else s;

fun pgml_sym s =
  (case Symbol.decode s of
    Symbol.Char s => XML.text s
  | Symbol.Sym sn => 
    let val ascii = implode (map xsym_output (Symbol.explode s))
    in if !pgmlsymbols_flag then XML.element "sym" [("name", sn)] [XML.text ascii]
       else  ascii end
  | Symbol.Ctrl sn => XML.element "ctrl" [("name", sn)] [XML.text sn] (* FIXME: no such PGML *)
  | Symbol.Raw raw => raw);

fun pgml_output str =
  let val syms = Symbol.explode str
  in (implode (map pgml_sym syms), Symbol.length syms) end;

in

fun setup_proofgeneral_output () =
  Output.add_mode proof_generalN pgml_output Symbol.encode_raw;

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
  (xml_atom kind x, Symbol.length (Symbol.explode x));

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

val _ = Context.add_setup (Theory.add_tokentrfuns proof_general_trans);

end;


(* assembling and issuing PGIP packets *)

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

val output_xml_fn = ref Output.writeln_default
fun output_xml s = (!output_xml_fn) (XML.string_of_tree s);  (* TODO: string buffer *)

val output_pgips =
  XML.string_of_tree o PgipOutput.output o assemble_pgips o map PgipOutput.output;

val output_pgmlterm = 
  XML.string_of_tree o Pgml.pgmlterm_to_xml;

val output_pgmltext = 
  XML.string_of_tree o Pgml.pgml_to_xml;


fun issue_pgip_rawtext str =
    output_xml (PgipOutput.output (assemble_pgips [XML.Output str]))

fun issue_pgips pgipops =
    output_xml (PgipOutput.output (assemble_pgips (map PgipOutput.output pgipops)));

fun issue_pgip pgipop =
    output_xml (PgipOutput.output (assemble_pgips [PgipOutput.output pgipop]));

end;


fun pgml area terms = Pgml.Pgml { version=NONE,systemid=NONE,
                                  area=SOME area, content=terms }

(** messages and notification **)

local
    val delay_msgs = ref false   (*true: accumulate messages*)
    val delayed_msgs = ref []

    fun queue_or_issue pgip =
        if ! delay_msgs then
            delayed_msgs := pgip :: ! delayed_msgs
        else issue_pgip pgip

    fun wrap_pgml area s = 
        if String.isPrefix "<pgml" s then  
            XML.Output s  (* already pgml outermost *)
        else 
            Pgml.pgml_to_xml (pgml area [Pgml.Raw (XML.Output s)]) (* mixed *)

in
    fun normalmsg area s =
        let
            val content = wrap_pgml area s
            val pgip = Normalresponse { content=[content] }
        in
            queue_or_issue pgip
        end

    fun errormsg area fatality s =
        let
            val content = wrap_pgml area s
            val pgip = Errorresponse { fatality=fatality,
                                       location=NONE,
                                       content=[content] }
        in
            queue_or_issue pgip
        end

    (* Error responses with useful locations *)
    fun error_with_pos area fatality pos s =
        let
              val content = wrap_pgml area s
              val pgip = Errorresponse { fatality=fatality,
                                         location=SOME (PgipIsabelle.location_of_position pos),
                                         content=[content] }
        in
            queue_or_issue pgip
        end

    fun start_delay_msgs () = (set delay_msgs; delayed_msgs := [])
    fun end_delayed_msgs () = (reset delay_msgs; ! delayed_msgs)
end;

(* NB: all of the standard error/message functions now expect already-escaped text.
   FIXME: this may cause us problems now we're generating trees; on the other
   hand the output functions were tuned some time ago, so it ought to be
   enough to use XML.Output always above. *)
(* NB 2: all of standard functions print strings terminated with new lines, but we don't
   add new lines explicitly in PGIP: they are left implicit.  It means that PGIP messages
   can't be written without newlines. *)

fun setup_messages () =
 (Output.writeln_fn := (fn s => normalmsg Message s);
  Output.priority_fn := (fn s => normalmsg Status s);
  Output.tracing_fn := (fn s => normalmsg  Tracing s);
  Output.warning_fn := (fn s => errormsg Message Warning s);
  Output.error_fn := (fn s => errormsg Message Fatal s);
  Output.debug_fn := (fn s => errormsg Message Debug s));

fun panic s = (errormsg Message Panic ("## SYSTEM EXIT ##\n" ^ s); exit 1);
fun nonfatal_error s = errormsg Message Nonfatal s;
fun log_msg s = errormsg Message Log s;


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


(* common markup *)

local

val no_text = chr 0;

val pgmlterms_no_text= [Pgml.Raw (XML.Output no_text)]

fun split_markup text =
  (case space_explode no_text text of
    [bg, en] => (bg, en)
  | _ => (error ("Internal error: failed to split XML markup:\n" ^ text); ("", "")));


fun block_markup markup =
    let 
      val pgml = Pgml.Box { orient = NONE, 
                            indent = Markup.get_int markup Markup.indentN,
                            content = pgmlterms_no_text }
    in split_markup (output_pgmlterm pgml) end;

fun break_markup markup =
    let 
      val pgml = Pgml.Break { mandatory = NONE,
                              indent = Markup.get_int markup Markup.widthN }
    in (output_pgmlterm pgml, "") end;

fun fbreak_markup markup =
    let 
      val pgml = Pgml.Break { mandatory = SOME true, indent = NONE }
    in (output_pgmlterm pgml, "") end;

val state_markup =
    split_markup (output_pgmltext (pgml PgipTypes.Display pgmlterms_no_text))

fun proof_general_markup (markup as (name, _)) =
        if name = Markup.blockN    then block_markup markup
   else if name = Markup.breakN    then break_markup markup
   else if name = Markup.fbreakN   then fbreak_markup markup
(* else if name = Markup.classN    then class_markup markup
   else if name = Markup.tyconN    then tycon_markup markup
   else if name = Markup.constN    then const_markup markup
   else if name = Markup.axiomN    then axiom_markup markup
   else if name = Markup.sortN     then sort_markup markup
   else if name = Markup.typN      then typ_markup markup
   else if name = Markup.termN     then term_markup markup
   else if name = Markup.keywordN  then keyword_markup markup
   else if name = Markup.commandN  then command_markup markup 
   else if name = Markup.promptN   then prompt_markup markup *)
   else if name = Markup.stateN    then state_markup
(* else if name = Markup.subgoalN  then subgoal_markup () *)
   else ("", "");

in

val _ = Markup.add_mode proof_generalN proof_general_markup;

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
      ThyInfo.register_thy name handle ERROR msg =>
       (warning (cat_lines [msg, "Failed to register theory: " ^ quote name]);
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

val show_theorem_dependencies = ref false;

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

fun tell_thm_deps ths =
  if !show_theorem_dependencies then
      let
        val names = map PureThy.get_name_hint (filter PureThy.has_name_hint ths);
        val deps = (Symtab.keys (fold Proofterm.thms_of_proof'
                                        (map Thm.proof_of ths) Symtab.empty))
      in
          if null names orelse null deps then ()
          else thm_deps_message (spaces_quote names, spaces_quote deps)
      end
  else ()

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
                   (panic ("Error in URL in environment variable ISABELLE_HOMEPAGE.");
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
        else panic ("PGIP configuration file \"" ^ config_file() ^ "\" not found")
    end;
end


(* Preferences: tweak for PGIP interfaces *)

val preferences = ref Preferences.preferences;

fun setup_preferences_tweak() =
    preferences :=
     (!preferences |> Preferences.set_default ("show-question-marks","false")
                   |> Preferences.remove "show-question-marks"    (* we use markup, not ?s *)
                   |> Preferences.remove "theorem-dependencies"   (* set internally *)
                   |> Preferences.remove "full-proofs")           (* set internally *)



(* Sending commands to Isar *)

fun isarcmd s =
    s |> OuterSyntax.scan |> OuterSyntax.read
      (*|> map (Toplevel.position Position.none o #3)*)
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
     change print_mode 
            (fn mode =>
                remove (op =) Symbol.xsymbolsN mode @ (if b then [Symbol.xsymbolsN] else [])))

fun set_proverflag_thmdeps b =
    (show_theorem_dependencies := b;
     proofs := (if b then 1 else 2))

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
        isarcmd ("undos_proof " ^ Int.toString times)
    end

fun redostep _ = isarcmd "redo"

fun abortgoal _ = isarcmd "kill" (* was: ProofGeneral.kill_proof *)


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

        fun setids t = issue_pgip (Setids {idtables = [t]})

        (* fake one-level nested "subtheories" by picking apart names. *)
        val thms_of_thy =
            map fst o NameSpace.extern_table o PureThy.theorems_of o ThyInfo.get_theory
        val immed_thms_of_thy = filter_out NameSpace.is_qualified o thms_of_thy
        fun thy_prefix s = case space_explode NameSpace.separator s of
                                    x::_::_ => SOME x  (* String.find? *)
                                  | _ => NONE
        fun subthys_of_thy s =
            List.foldl  (fn (NONE,xs) => xs | (SOME x,xs) => insert op= x xs) []
                   (map thy_prefix (thms_of_thy s))
        fun subthms_of_thy thy =
            (case thy_prefix thy of
                 NONE => immed_thms_of_thy thy
               | SOME prf => filter (String.isPrefix (unprefix (prf ^ NameSpace.separator) thy))
                                    (thms_of_thy prf))
       val qualified_thms_of_thy = (* for global query with single response *)
            (map fst) o NameSpace.dest_table o PureThy.theorems_of o ThyInfo.get_theory; 
(* da: this version is equivalent to my previous, but splits up theorem sets with names
   that I can't get to access later with get_thm.  Anyway, would rather use sets.
   Is above right way to get qualified names in that case?  Filtering required again?
            map PureThy.get_name_hint o filter PureThy.has_name_hint o
              map snd o PureThy.thms_of o ThyInfo.get_theory; *)
    in 
        case (thyname,objtype) of
           (NONE, NONE) =>
           setids (idtable ObjFile NONE (ThyInfo.names())) (*FIXME: uris*)
         | (NONE, SOME ObjFile) =>
           setids (idtable ObjFile NONE (ThyInfo.names())) (*FIXME: uris*)
         | (SOME fi, SOME ObjFile) =>
           setids (idtable ObjTheory (SOME fi) [fi])       (* TODO: check exists *)
         | (NONE, SOME ObjTheory) =>
           setids (idtable ObjTheory NONE (ThyInfo.names()))
         | (SOME thy, SOME ObjTheory) =>
           setids (idtable ObjTheory (SOME thy) (subthys_of_thy thy))
         | (SOME thy, SOME ObjTheorem) =>
           setids (idtable ObjTheorem (SOME thy) (subthms_of_thy thy))
         | (NONE, SOME ObjTheorem) =>
           (* A large query, but not unreasonable. ~5000 results for HOL.*)
           (* Several setids should be allowed, but Eclipse code is currently broken:
              List.app (fn thy => setids (idtable ObjTheorem (SOME thy) (subthms_of_thy thy)))
                         (ThyInfo.names()) *)
           setids (idtable ObjTheorem NONE (* this one gives ~7000 for HOL *)
                           (maps qualified_thms_of_thy (ThyInfo.names())))
         | _ => warning ("askids: ignored argument combination")
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
                val filerefs = #uses (ThyLoad.deps_thy (Path.dir f) thy)
            in
                issue_pgip (Setrefs {url=url, thyname=NONE, objtype=SOME PgipTypes.ObjFile,
                                     name=NONE, idtables=[], fileurls=filerefs})
            end

        fun thyrefs thy =
            let val thyrefs = #imports (ThyLoad.deps_thy Path.current thy)
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



fun showid (Showid vs) =
    let
        val thyname = #thyname vs
        val objtype = #objtype vs
        val name = #name vs

        val topthy = Toplevel.theory_of o Toplevel.get_state

        fun splitthy id =
            let val comps = NameSpace.explode id
            in case comps of
                   (thy::(rest as _::_)) => (ThyInfo.get_theory thy, space_implode "." rest)
                 | [plainid] => (topthy(),plainid)
                 | _ => raise Toplevel.UNDEF (* assert false *)
            end 
                                            

        fun idvalue strings =
            issue_pgip (Idvalue { thyname=thyname, objtype=objtype, name=name, 
                                  text=[XML.Elem("pgml",[],
                                                 map XML.Output strings)] })

        fun string_of_thm th = Output.output
                               (Pretty.string_of
                                   (Display.pretty_thm_aux
                                        (Sign.pp (Thm.theory_of_thm th))
                                        false (* quote *)
                                        false (* show hyps *)
                                        [] (* asms *)
                                        th))

        fun strings_of_thm (thy, name) = map string_of_thm (get_thms thy (Name name))

        val string_of_thy = Output.output o
                                Pretty.string_of o (ProofDisplay.pretty_full_theory false)
    in
        case (thyname, objtype) of
            (_,ObjTheory) => idvalue [string_of_thy (ThyInfo.get_theory name)]
          | (SOME thy, ObjTheorem) => idvalue (strings_of_thm (ThyInfo.get_theory thy, name))
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

val currently_open_file = ref (NONE : pgipurl option)

fun get_currently_open_file () = ! currently_open_file;

fun askguise _ =
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
        val doc = OldPgipParser.pgip_parser text
		  (* not yet working: PgipParser.pgip_parser Position.none text  *)
        val errs = end_delayed_msgs ()

        val sysattrs = PgipTypes.opt_attr "systemdata" systemdata
        val locattrs = PgipTypes.attrs_of_location location
     in
        issue_pgip (Parseresult { attrs= sysattrs@locattrs,
                                  doc = doc,
                                  errs = map PgipOutput.output errs })
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

fun closefile _ =
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

fun abortfile _ =
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
                              (XML.string_of_tree xml))
           | SOME inp => (process_input inp)) (* errors later; packet discarded *)
      | XML.Text t => ignored_text_warning t
      | XML.Output t => ignored_text_warning t
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
    case (e,srco) of
        (XML_PARSE,SOME src) =>
        panic "Invalid XML input, aborting" (* TODO: attempt recovery  *)
      | (Interrupt,SOME src) =>
        (Output.error_msg "Interrupt during PGIP processing"; loop true src)
      | (Toplevel.UNDEF,SOME src) =>
        (Output.error_msg "No working context defined"; loop true src)
      | (e,SOME src) =>
        (Output.error_msg (Toplevel.exn_message e); loop true src)
      | (PGIP_QUIT,_) => ()
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

fun init_pgip false = panic "No Proof General interface support for Isabelle/classic mode."
  | init_pgip true =
      (! initialized orelse
        (Output.no_warnings init_outer_syntax ();
          OldPgipParser.init ();
          setup_preferences_tweak ();
          setup_proofgeneral_output ();
          setup_messages ();
          setup_thy_loader ();
          setup_present_hook ();
          init_pgip_session_id ();
          welcome ();
          set initialized);
        sync_thy_loader ();
       change print_mode (cons proof_generalN o remove (op =) proof_generalN);
       pgip_toplevel tty_src);



(** Out-of-loop PGIP commands (for Emacs hybrid mode) **)

local
    val pgip_output_channel = ref Output.writeln_default
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
