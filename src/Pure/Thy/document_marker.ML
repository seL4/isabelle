(*  Title:      Pure/Thy/document_marker.ML
    Author:     Makarius

Document markers: declarations on the presentation context.
*)

signature DOCUMENT_MARKER =
sig
  type marker = Proof.context -> Proof.context
  val setup: binding -> 'a context_parser -> ('a -> marker) -> theory -> theory
  val setup0: binding -> 'a parser -> ('a -> marker) -> theory -> theory
  val evaluate: Input.source -> marker
  val legacy_tag: string -> Input.source
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

fun setup0 name scan = setup name (Scan.lift scan);


(* evaluate inner syntax *)

val parse_marker = Parse.token Parse.liberal_name ::: Parse.!!! Parse.args;

fun evaluate input ctxt =
  let
    val body =
      Input.source_explode input
      |> drop_prefix (fn (s, _) => s = Symbol.marker)
      |> Symbol_Pos.cartouche_content;
    val markers =
      (case Token.read_body (Thy_Header.get_keywords' ctxt) (Parse.list parse_marker) body of
        SOME res => res
      | NONE => error ("Bad input" ^ Position.here (Input.pos_of input)));
  in fold (fn src => #2 (check ctxt (Token.name_of_src src)) src) markers ctxt end;


(* concrete markers *)

fun meta_data markup arg ctxt =
  (Context_Position.report_text ctxt (Position.thread_data ()) markup arg; ctxt);

val _ =
  Theory.setup
    (setup0 (Binding.make ("tag", \<^here>)) Parse.name Document_Source.update_tags #>
     setup0 (Binding.make ("title", \<^here>)) Parse.embedded (meta_data Markup.meta_title) #>
     setup0 (Binding.make ("creator", \<^here>)) Parse.embedded (meta_data Markup.meta_creator) #>
     setup0 (Binding.make ("contributor", \<^here>)) Parse.embedded (meta_data Markup.meta_contributor) #>
     setup0 (Binding.make ("date", \<^here>)) Parse.embedded (meta_data Markup.meta_date) #>
     setup0 (Binding.make ("description", \<^here>)) (Parse.input Parse.embedded)
      (fn source => fn ctxt =>
        let
          val (arg, pos) = Input.source_content source;
          val _ = Context_Position.report ctxt pos Markup.words;
        in meta_data Markup.meta_description arg ctxt end));

fun legacy_tag name =
  Input.string (cartouche ("tag " ^ Symbol_Pos.quote_string_qq name));

end;
