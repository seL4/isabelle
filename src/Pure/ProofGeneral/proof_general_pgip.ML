(*  Title:      Pure/ProofGeneral/proof_general_pgip.ML
    Author:     David Aspinall and Markus Wenzel

Isabelle configuration for Proof General using PGIP protocol.
See http://proofgeneral.inf.ed.ac.uk/kit
*)

signature PROOF_GENERAL_PGIP =
sig
  val add_preference: string -> Preferences.preference -> unit
end

structure ProofGeneralPgip : PROOF_GENERAL_PGIP =
struct

(* assembling and issuing PGIP packets *)

val pgip_refid = Unsynchronized.ref NONE: string option Unsynchronized.ref;
val pgip_refseq = Unsynchronized.ref NONE: int option Unsynchronized.ref;

local
  val pgip_class  = "pg"
  val pgip_tag = "Isabelle/Isar"
  val pgip_id = "dummy"
  val pgip_seq = Unsynchronized.ref 0
  fun pgip_serial () = Unsynchronized.inc pgip_seq

  fun assemble_pgip content =
    XML.Elem(("pgip",
             [("tag", pgip_tag), ("id", pgip_id)] @
             PgipTypes.opt_attr "destid" (! pgip_refid) @
             [("class", pgip_class)] @
             PgipTypes.opt_attr "refid" (! pgip_refid) @
             PgipTypes.opt_attr_map string_of_int "refseq" (! pgip_refseq) @
             [("seq", string_of_int (pgip_serial ()))]),
             content)
in

fun matching_pgip_id id = (id = pgip_id)

fun output_pgip content = Output.urgent_message (XML.string_of (assemble_pgip content));

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

fun invalid_pgip () = raise PgipTypes.PGIP "Invalid PGIP packet received";

fun haspref ({name, descr, default, pgiptype, ...}: Preferences.preference) =
  XML.Elem (("haspref", [("name", name), ("descr", descr), ("default", default)]),
    [PgipTypes.pgiptype_to_xml pgiptype]);

fun process_element_emacs (XML.Elem (("askprefs", _), _)) =
      ! preferences |> List.app (fn (category, prefs) =>
          output_pgip [XML.Elem (("hasprefs", [("prefcategory", category)]), map haspref prefs)])
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
  end handle PgipTypes.PGIP msg => error (msg ^ "\n" ^ str);

val _ =
  Outer_Syntax.improper_command
    (("ProofGeneral.process_pgip", Keyword.control), Position.none) "(internal)"
    (Parse.text >> (fn str => Toplevel.imperative (fn () => process_pgip_emacs str)));

end;

end;
