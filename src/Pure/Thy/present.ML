(*  Title:      Pure/Thy/present.ML
    Author:     Makarius

Theory presentation: HTML and LaTeX documents.
*)

signature PRESENT =
sig
  val document_html_name: theory -> Path.binding
  val document_tex_name: theory -> Path.binding
  val html_name: theory -> Path.T
  val export_html: theory -> Command_Span.span list -> unit
end;

structure Present: PRESENT =
struct

(** artefact names **)

fun document_name ext thy =
  Path.explode_binding0 ("document/" ^ Context.theory_name thy ^ "." ^ ext);

val document_html_name = document_name "html";
val document_tex_name = document_name "tex";

fun html_name thy = Path.basic (Context.theory_name thy ^ ".html");


(* theory as HTML *)

local

fun get_session_chapter thy =
  let
    val session = Resources.theory_qualifier (Context.theory_long_name thy);
    val chapter = Resources.session_chapter session;
  in (session, chapter) end;

fun theory_link thy thy' =
  let
    val ((session, chapter), (session', chapter')) = apply2 get_session_chapter (thy, thy');
    val link = html_name thy';
  in
    if session = session' then SOME link
    else if chapter = chapter' then SOME (Path.parent + Path.basic session + link)
    else if chapter = Context.PureN then NONE
    else SOME (Path.parent + Path.parent + Path.basic chapter + Path.basic session + link)
  end;

fun theory_document symbols A Bs body =
  HTML.begin_document symbols ("Theory " ^ A) ^ "\n" ^
  HTML.command symbols "theory" ^ " " ^ HTML.name symbols A ^ "<br/>\n" ^
  HTML.keyword symbols "imports" ^ " " ^
    space_implode " " (map (uncurry HTML.href_opt_path o apsnd (HTML.name symbols)) Bs) ^
  "<br/>\n\n</div>\n<div class=\"source\">\n<pre class=\"source\">" ::
  body @ ["</pre>\n", HTML.end_document];

in

fun export_html thy spans =
  let
    val name = Context.theory_name thy;
    val parents =
      Theory.parents_of thy |> map (fn thy' =>
        (Option.map Url.File (theory_link thy thy'), Context.theory_name thy'));

    val symbols = Resources.html_symbols ();
    val keywords = Thy_Header.get_keywords thy;
    val body = map (HTML.present_span symbols keywords) spans;
    val html = XML.blob (theory_document symbols name parents body);
  in Export.export thy (document_html_name thy) html end

end;

end;
