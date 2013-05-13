(*  Title:      Pure/ProofGeneral/proof_general_pgip.ML
    Author:     David Aspinall and Markus Wenzel

Isabelle configuration for Proof General using PGIP protocol.
See http://proofgeneral.inf.ed.ac.uk/kit
*)

signature PROOF_GENERAL_PGIP =
sig
  val proof_general_emacsN: string

  val new_thms_deps: theory -> theory -> string list * string list

  val add_preference: string -> Preferences.preference -> unit
end

structure ProofGeneralPgip : PROOF_GENERAL_PGIP =
struct

open PgipTypes;
open PgipMarkup;
open PgipInput;
open PgipOutput;


(** print mode **)

val proof_general_emacsN = "ProofGeneralEmacs";


(* assembling and issuing PGIP packets *)

val pgip_refid = Unsynchronized.ref NONE: string option Unsynchronized.ref;
val pgip_refseq = Unsynchronized.ref NONE: int option Unsynchronized.ref;

local
  val pgip_class  = "pg"
  val pgip_tag = "Isabelle/Isar"
  val pgip_id = "dummy"
  val pgip_seq = Unsynchronized.ref 0
  fun pgip_serial () = Unsynchronized.inc pgip_seq

  fun assemble_pgips pgips =
    Pgip { tag = SOME pgip_tag,
           class = pgip_class,
           seq = pgip_serial (),
           id = pgip_id,
           destid = ! pgip_refid,
           (* destid=refid since Isabelle only communicates back to sender *)
           refid = ! pgip_refid,
           refseq = ! pgip_refseq,
           content = pgips }
in

fun matching_pgip_id id = (id = pgip_id)

val output_pgips = XML.string_of o PgipOutput.output o assemble_pgips o map PgipOutput.output;

end;



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


(* Preferences: tweak for PGIP interfaces *)

val preferences = Unsynchronized.ref Preferences.pure_preferences;

fun add_preference cat pref =
  CRITICAL (fn () => Unsynchronized.change preferences (Preferences.add cat pref));

fun set_preference pref value =
  (case AList.lookup (op =) (map (fn p => (#name p, p)) (maps snd (! preferences))) pref of
    SOME {set, ...} => set value
  | NONE => error ("Unknown prover preference: " ^ quote pref));


(** PGIP/Emacs rudiments **)

local

fun invalid_pgip () = raise PGIP "Invalid PGIP packet received";

fun output_emacs pgips = Output.urgent_message (output_pgips pgips);

fun process_element_emacs (XML.Elem (("askprefs", _), _)) =
      let
        fun preference_of {name, descr, default, pgiptype, get = _, set = _} =
          {name = name, descr = SOME descr, default = SOME default, pgiptype = pgiptype};
      in
        ! preferences |> List.app (fn (prefcat, prefs) =>
            output_emacs [Hasprefs {prefcategory = SOME prefcat, prefs = map preference_of prefs}])
      end
  | process_element_emacs (XML.Elem (("setpref", attrs), data)) =
      let
        val name =
          (case Properties.get attrs "name" of
            SOME name => name
          | NONE => invalid_pgip ());
        val value = XML.content_of data;
      in set_preference name value end
  | process_element_emacs _ = invalid_pgip ();

in

fun process_pgip_emacs str =
  let
    val _ = pgip_refid := NONE;
    val _ = pgip_refseq := NONE;
  in
    (case XML.parse str of
      XML.Elem (("pgip", attrs), pgips) =>
        let
          val class = PgipTypes.get_attr "class" attrs;
          val dest = PgipTypes.get_attr_opt "destid" attrs;
          val seq = PgipTypes.read_pgipnat (PgipTypes.get_attr "seq" attrs);
          val processit =
            (case dest of
              NONE => class = "pa"
            | SOME id => matching_pgip_id id);
         in
           if processit then
            (pgip_refid := PgipTypes.get_attr_opt "id" attrs;
             pgip_refseq := SOME seq;
             List.app process_element_emacs pgips)
           else ()
         end
    | _ => invalid_pgip ())
  end handle PGIP msg => error (msg ^ "\n" ^ str);

val _ =
  Outer_Syntax.improper_command
    (("ProofGeneral.process_pgip", Keyword.control), Position.none) "(internal)"
    (Parse.text >> (fn str => Toplevel.imperative (fn () => process_pgip_emacs str)));

end;

end;
