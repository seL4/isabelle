(*  Title:      Pure/Thy/document_marker.ML
    Author:     Makarius

Document markers: declarations on the presentation context.
*)

signature DOCUMENT_MARKER =
sig
  type marker = Proof.context -> Proof.context
  val check: Proof.context -> string * Position.T -> string * (Token.src -> marker)
  val setup: binding -> 'a context_parser -> ('a -> marker) -> theory -> theory
  val setup0: binding -> 'a parser -> ('a -> marker) -> theory -> theory
  val evaluate: string -> Input.source -> marker
  val command_name: Proof.context -> string
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

val config_command_name = Config.declare_string ("command_name", \<^here>) (K "");
val command_name = Config.apply config_command_name;

val parse_marker = Parse.token Parse.liberal_name ::: Parse.!!! Parse.args;

fun evaluate cmd_name input ctxt =
  let
    val syms = Input.source_explode input
      |> drop_prefix (fn (s, _) => s = Symbol.marker);
    val pos = #1 (Symbol_Pos.range syms);

    val _ = Context_Position.reports ctxt (map (pair pos) (Comment.kind_markups Comment.Marker));

    val body = Symbol_Pos.cartouche_content syms;
    val markers =
      (case Token.read_body (Thy_Header.get_keywords' ctxt) (Parse.list parse_marker) body of
        SOME res => res
      | NONE => error ("Bad input" ^ Position.here pos));
  in
    ctxt
    |> Config.put config_command_name cmd_name
    |> fold (fn src => #2 (check ctxt (Token.name_of_src src)) src) markers
    |> Config.put config_command_name (command_name ctxt)
  end;


(* tag with scope *)

val parse_tag =
  Scan.state :|-- (fn context =>
    let
      val ctxt = Context.proof_of context;
      val scope0 =
        if Keyword.is_theory_goal (Thy_Header.get_keywords' ctxt) (command_name ctxt)
        then Document_Source.Command
        else Document_Source.Proof;
      val tag = Scan.optional Document_Source.tag_scope scope0 -- Document_Source.tag_name >> swap;
    in Scan.lift (Parse.position tag) end);

fun update_tags (tag as (name, _), pos) ctxt =
 (Context_Position.report ctxt pos (Markup.document_tag name);
  Document_Source.update_tags tag ctxt);


(* concrete markers *)

fun meta_data markup arg ctxt =
  (Context_Position.report_text ctxt (Position.thread_data ()) markup arg; ctxt);

val _ =
  Theory.setup
    (setup (Binding.make ("tag", \<^here>)) parse_tag update_tags #>
     setup0 (Binding.make ("title", \<^here>)) Parse.embedded (meta_data Markup.meta_title) #>
     setup0 (Binding.make ("creator", \<^here>)) Parse.embedded (meta_data Markup.meta_creator) #>
     setup0 (Binding.make ("contributor", \<^here>)) Parse.embedded (meta_data Markup.meta_contributor) #>
     setup0 (Binding.make ("date", \<^here>)) Parse.embedded (meta_data Markup.meta_date) #>
     setup0 (Binding.make ("license", \<^here>)) Parse.embedded (meta_data Markup.meta_license) #>
     setup0 (Binding.make ("description", \<^here>)) (Parse.input Parse.embedded)
      (fn source => fn ctxt =>
        let
          val (arg, pos) = Input.source_content source;
          val _ = Context_Position.report ctxt pos Markup.words;
        in meta_data Markup.meta_description arg ctxt end));

fun legacy_tag name =
  Input.string (cartouche ("tag (proof) " ^ Symbol_Pos.quote_string_qq name));

end;
