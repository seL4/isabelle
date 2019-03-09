(*  Title:      Pure/Thy/document_marker.ML
    Author:     Makarius

Document markers: declarations on the presentation context.
*)

signature DOCUMENT_MARKER =
sig
  type marker = Proof.context -> Proof.context
  val setup: binding -> 'a context_parser -> ('a -> marker) -> theory -> theory
  val evaluate: Input.source -> marker
end;

structure Document_Marker: DOCUMENT_MARKER =
struct

(* theory data *)

type marker = Proof.context -> Proof.context;

structure Markers = Theory_Data
(
  type T = (Token.src -> Proof.context -> Proof.context) Name_Space.table;
  val empty : T = Name_Space.empty_table "document_marker";
  val extend = I;
  val merge = Name_Space.merge_tables;
);

val get_markers = Markers.get o Proof_Context.theory_of;

fun check ctxt = Name_Space.check (Context.Proof ctxt) (get_markers ctxt);

fun setup name scan body thy =
  let
    fun marker src ctxt =
      let val (x, ctxt') = Token.syntax scan src ctxt
      in body x ctxt' end;
  in thy |> Markers.map (Name_Space.define (Context.Theory thy) true (name, marker) #> #2) end;


(* evaluate inner syntax *)

val parse_marker = Parse.token Parse.liberal_name ::: Parse.!!! Parse.args;

fun evaluate input ctxt =
  let
    val pos = Input.pos_of input;
    val _ = Context_Position.report ctxt pos Markup.language_document_marker;

    val syms = Input.source_explode input;
    val markers =
      (case Token.read_body (Thy_Header.get_keywords' ctxt) (Parse.list parse_marker) syms of
        SOME res => res
      | NONE => error ("Bad input" ^ Position.here pos));
  in fold (fn src => #2 (check ctxt (Token.name_of_src src)) src) markers ctxt end;


(* concrete markers *)

val _ =
  Theory.setup
    (setup (Binding.make ("tag", \<^here>)) (Scan.lift Parse.name) Document_Source.update_tags);

end;
