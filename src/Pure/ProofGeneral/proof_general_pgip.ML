(*  Title:      Pure/ProofGeneral/proof_general_pgip.ML
    Author:     David Aspinall and Markus Wenzel

Rudiments of PGIP for ProofGeneral preferences.
*)

signature PROOF_GENERAL_PGIP =
sig
  val add_preference: string -> Preferences.preference -> unit
end

structure ProofGeneralPgip : PROOF_GENERAL_PGIP =
struct

(* output PGIP packets *)

val pgip_id = "dummy";
val pgip_serial = Synchronized.counter ();

fun output_pgip refid refseq content =
  XML.Elem (("pgip",
    PgipTypes.attr "tag" "Isabelle/Isar" @
    PgipTypes.attr "id" pgip_id @
    PgipTypes.opt_attr "destid" refid @
    PgipTypes.attr "class" "pg" @
    PgipTypes.opt_attr "refid" refid @
    PgipTypes.attr "refseq" refseq @
    PgipTypes.attr "seq" (string_of_int (pgip_serial ()))), content)
  |> XML.string_of
  |> Output.urgent_message;


(* preferences *)

val preferences = Unsynchronized.ref Preferences.pure_preferences;

fun add_preference cat pref =
  CRITICAL (fn () => Unsynchronized.change preferences (Preferences.add cat pref));

fun set_preference pref value =
  (case AList.lookup (op =) (map (fn p => (#name p, p)) (maps snd (! preferences))) pref of
    SOME {set, ...} => set value
  | NONE => error ("Unknown prover preference: " ^ quote pref));


(* process_pgip *)

local

fun invalid_pgip () = raise PgipTypes.PGIP "Invalid PGIP packet received";

fun haspref ({name, descr, default, pgiptype, ...}: Preferences.preference) =
  XML.Elem (("haspref", [("name", name), ("descr", descr), ("default", default)]),
    [PgipTypes.pgiptype_to_xml pgiptype]);

fun process_element refid refseq (XML.Elem (("askprefs", _), _)) =
      ! preferences |> List.app (fn (category, prefs) =>
          output_pgip refid refseq
            [XML.Elem (("hasprefs", [("prefcategory", category)]), map haspref prefs)])
  | process_element _ _ (XML.Elem (("setpref", attrs), data)) =
      let
        val name =
          (case Properties.get attrs "name" of
            SOME name => name
          | NONE => invalid_pgip ());
        val value = XML.content_of data;
      in set_preference name value end
  | process_element _ _ _ = invalid_pgip ();

fun process_pgip str =
  (case XML.parse str of
    XML.Elem (("pgip", attrs), pgips) =>
      let
        val class = PgipTypes.get_attr attrs "class";
        val dest = Properties.get attrs "destid";
        val refid = Properties.get attrs "id";
        val refseq = PgipTypes.get_attr attrs "seq";
        val processit =
          (case dest of
            NONE => class = "pa"
          | SOME id => id = pgip_id);
       in if processit then List.app (process_element refid refseq) pgips else () end
  | _ => invalid_pgip ())
  handle PgipTypes.PGIP msg => error (msg ^ "\n" ^ str);

in

val _ =
  Outer_Syntax.improper_command
    (("ProofGeneral.process_pgip", Keyword.control), Position.none) "(internal)"
    (Parse.text >> (fn str => Toplevel.imperative (fn () => process_pgip str)));

end;

end;
