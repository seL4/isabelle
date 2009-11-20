(*  Title:      xhtml.ML
    Author:     Timothy Bourke, NICTA

Rudimentary XHTML construction.
*)
signature XHTML =
sig
  type attribute
  type common_atts = { id : string option,
                       class : string option };
  val noid : common_atts;
  val id : string -> common_atts;
  val class : string -> common_atts;

  type tag

  val doctype_xhtml1_0_strict: string;

  val att: string -> string -> attribute
  val bool_att: string * bool -> attribute list

  val tag: string -> attribute list -> tag list -> tag
  val tag': string -> common_atts -> tag list -> tag
  val text: string -> tag
  val raw_text: string -> tag

  val add_attributes: attribute list -> tag -> tag
  val append: tag -> tag list -> tag

  val show: tag -> string list

  val write: (string -> unit) -> tag -> unit
  val write_open: (string -> unit) -> tag -> unit
  val write_close: (string -> unit) -> tag -> unit

  val html: { lang : string } -> tag list -> tag
  val head: { title : string, stylesheet_href : string } -> tag list -> tag
  val body: common_atts -> tag list -> tag
  val divele: common_atts -> tag list -> tag
  val span: common_atts * string -> tag
  val span': common_atts -> tag list -> tag

  val pre: common_atts -> string -> tag

  val table: common_atts -> tag list -> tag
  val thead: common_atts -> tag list -> tag
  val tbody: common_atts -> tag list -> tag
  val tr: tag list -> tag
  val th: common_atts * string -> tag
  val th': common_atts -> tag list -> tag
  val td: common_atts * string -> tag
  val td': common_atts -> tag list -> tag
  val td'': common_atts * { colspan : int option, rowspan : int option }
           -> tag list -> tag

  val p: common_atts * string -> tag
  val p': common_atts * tag list -> tag
  val h: common_atts * int * string -> tag
  val strong: string -> tag
  val em: string -> tag
  val a: { href : string, text : string } -> tag

  val ul: common_atts * tag list -> tag
  val ol: common_atts * tag list -> tag
  val dl: common_atts * (string * tag) list -> tag

  val alternate_class: { class0 : string, class1 : string }
                      -> tag list -> tag list

  val form: common_atts * { method : string, action : string }
            -> tag list -> tag

  datatype input_type =
      TextInput of { value: string option, maxlength: int option }
    | Password of int option
    | Checkbox of { checked : bool, value : string option }
    | Radio of { checked : bool, value : string option }
    | Submit
    | Reset
    | Hidden
    | Image of { src : string, alt : string }
    | File of { accept : string }
    | Button;

  val input: common_atts * { name : string, itype : input_type } -> tag
  val select: common_atts * { name : string, value : string option }
              -> string list -> tag
  val label: common_atts * { for: string } * string -> tag

  val reset_button: common_atts -> tag
  val submit_button: common_atts -> tag

  datatype event =
    (* global *)
      OnClick
    | OnDblClick
    | OnMouseDown
    | OnMouseUp
    | OnMouseOver
    | OnMouseMove
    | OnMouseOut
    | OnKeyPress
    | OnKeyDown
    | OnKeyUp
      (* anchor/label/input/select/textarea/button/area *)
    | OnFocus
    | OnBlur
      (* form *)
    | OnSubmit
    | OnReset
      (* input/textarea *)
    | OnSelect
      (* input/select/textarea *)
    | OnChange
      (* body *)
    | OnLoad
    | OnUnload;

  val script: common_atts * { script_type: string, src: string } -> tag
  val add_script: event * string -> tag -> tag
end;

structure Xhtml : XHTML =
struct

type attribute = string * string;
type common_atts = {
    id : string option,
    class : string option
  };
val noid = { id = NONE, class = NONE };
fun id s = { id = SOME s, class = NONE };
fun class s = { id = NONE, class = SOME s };

fun from_common { id = NONE,   class = NONE } = []
  | from_common { id = SOME i, class = NONE } = [("id", i)]
  | from_common { id = NONE,   class = SOME c } = [("class", c)]
  | from_common { id = SOME i, class = SOME c } = [("id", i), ("class", c)];

val update_atts =
  AList.join (op = : string * string -> bool) (fn _ => snd);

datatype tag = Tag of (string * attribute list * tag list)
             | Text of string
             | RawText of string;

fun is_text (Tag _) = false
  | is_text (Text _) = true
  | is_text (RawText _) = true;

fun is_tag (Tag _) = true
  | is_tag (Text _) = false
  | is_tag (RawText _) = false;

val att = pair;

fun bool_att (nm, true) = [(nm, nm)]
  | bool_att (nm, false) = [];

fun tag name atts inner = Tag (name, atts, inner);
fun tag' name common_atts inner = Tag (name, from_common common_atts, inner);
fun text t = Text t;
fun raw_text t = RawText t;

fun add_attributes atts' (Tag (nm, atts, inner)) =
      Tag (nm, update_atts (atts, atts'), inner)
  | add_attributes _ t = t;

fun append (Tag (nm, atts, inner)) inner' = Tag (nm, atts, inner @ inner')
  | append _ _ = raise Fail "cannot append to a text element";

fun show_att (n, v) = concat [" ", n, "=\"", XML.text v, "\""];

fun show_text (Text t) = XML.text t
  | show_text (RawText t) = t
  | show_text _ = raise Fail "Bad call to show_text.";

fun show (Text t) = [XML.text t]
  | show (RawText t) = [t]
  | show (Tag (nm, atts, inner)) =
  (["<", nm] @ map show_att atts
   @
   (if length inner = 0
    then ["/>"]
    else List.concat (
      [[">"]]
      @
      map show inner
      @
      [["</", nm, ">"]]
  )));

fun write pr =
  let
    fun f (Text t) = (pr o XML.text) t
      | f (RawText t) = pr t
      | f (Tag (nm, atts, inner)) = (
          pr "<";
          pr nm;
          app (pr o show_att) atts;
          if length inner = 0
          then pr "/>"
          else (
            pr ">";
            app f inner;
            pr ("</" ^ nm ^ ">")
          ))
  in f end;

(* Print all opening tags down into the tree until a branch of degree > 1 is
   found, in which case print everything before the last tag, which is then
   opened. *)
fun write_open pr =
  let
    fun f (Text t) = (pr o XML.text) t
      | f (RawText t) = pr t
      | f (Tag (nm, atts, [])) =
          (pr "<"; pr nm; app (pr o show_att) atts; pr ">")
      | f (Tag (nm, atts, xs)) =
           (pr "<"; pr nm; app (pr o show_att) atts; pr ">";
            (case take_suffix is_text xs of
               ([], _) => ()
             | (b, _) =>
                 let val (xs, x) = split_last b;
                 in app (write pr) xs; f x end));
  in f end;

(* Print matching closing tags for write_open. *)
fun write_close pr =
  let
    fun close nm = pr ("</" ^ nm ^ ">");
    val pr_text = app (pr o show_text);

    fun f (Text t) = ()
      | f (RawText t) = ()
      | f (Tag (nm, _, [])) = close nm
      | f (Tag (nm, _, xs)) =
           (case take_suffix is_text xs of
              ([], text) => pr_text text
            | (b, text) =>
                let val (xs, x) = split_last b;
                in f x; close nm; pr_text text end);
  in f end;

fun html { lang } tags = Tag ("html",
                              [("xmlns", "http://www.w3.org/1999/xhtml"),
                               ("xml:lang", lang)],
                              tags);

fun head { title, stylesheet_href } inner = let
    val link =
      Tag ("link",
        [("rel", "stylesheet"),
         ("type", "text/css"),
         ("href", stylesheet_href)], []);
    val title = Tag ("title", [], [Text title]);
    val charset = Tag ("meta",
        [("http-equiv", "Content-type"),
         ("content", "text/html; charset=UTF-8")], []);
  in Tag ("head", [], link::title::charset::inner) end;

fun body common_atts tags = Tag ("body", from_common common_atts, tags);

fun divele common_atts tags = Tag ("div", from_common common_atts, tags);
fun span (common_atts, t) = Tag ("span", from_common common_atts, [Text t]);
fun span' common_atts tags = Tag ("span", from_common common_atts, tags);

fun pre common_atts rt = Tag ("pre", from_common common_atts, [RawText rt]);

fun ostr_att (nm, NONE) = []
  | ostr_att (nm, SOME s) = [(nm, s)];
val oint_att = ostr_att o apsnd (Option.map Int.toString);

val table = tag' "table";
val thead = tag' "thead";
val tbody = tag' "tbody";
val tr = tag "tr" [];
fun th (common_atts, t) = Tag ("th", from_common common_atts, [Text t]);
fun th' common_atts tags = Tag ("th", from_common common_atts, tags);
fun td (common_atts, t) = Tag ("td", from_common common_atts, [Text t]);
fun td' common_atts tags = Tag ("td", from_common common_atts, tags);
fun td'' (common_atts, { colspan, rowspan }) tags =
  Tag ("td",
    from_common common_atts
    @ oint_att ("colspan", colspan)
    @ oint_att ("rowspan", rowspan),
    tags);

fun p (common_atts, t) = Tag ("p", from_common common_atts, [Text t]);
fun p' (common_atts, tags) = Tag ("p", from_common common_atts, tags);

fun h (common_atts, i, text) =
  Tag ("h" ^ Int.toString i, from_common common_atts, [Text text]);

fun strong t = Tag ("strong", [], [Text t]);
fun em t = Tag ("em", [], [Text t]);
fun a { href, text } = Tag ("a", [("href", href)], [Text text]);

fun to_li tag = Tag ("li", [], [tag]);
fun ul (common_atts, lis) = Tag ("ul", from_common common_atts, map to_li lis);
fun ol (common_atts, lis) = Tag ("ol", from_common common_atts, map to_li lis);

fun to_dtdd (nm, tag) = [Tag ("dt", [], [Text nm]),
                         Tag ("dd", [], [tag])];
fun dl (common_atts, dtdds) =
  Tag ("dl", from_common common_atts, (List.concat o map to_dtdd) dtdds);
            
fun alternate_class { class0, class1 } rows = let
    fun f ((true, xs), x) = (false, add_attributes [("class", class0)] x :: xs)
      | f ((false, xs), x) = (true, add_attributes [("class", class1)] x :: xs);
  in Library.foldl f ((true, []), rows) |> snd |> rev end;

fun form (common_atts as { id, ... }, { method, action }) tags =
  Tag ("form",
    [("method", method),
     ("action", action)]
    @ from_common common_atts, tags);

datatype input_type =
    TextInput of { value: string option, maxlength: int option }
  | Password of int option
  | Checkbox of { checked : bool, value : string option }
  | Radio of { checked : bool, value : string option }
  | Submit
  | Reset
  | Hidden
  | Image of { src : string, alt : string }
  | File of { accept : string }
  | Button;

fun from_checked { checked = false, value = NONE }   = []
  | from_checked { checked = true,  value = NONE }   = [("checked", "checked")]
  | from_checked { checked = false, value = SOME v } = [("value", v)]
  | from_checked { checked = true,  value = SOME v } =
      [("checked", "checked"), ("value", v)];

fun input_atts (TextInput { value, maxlength }) =
      ("type", "text")
       :: ostr_att ("value", value)
        @ oint_att ("maxlength", maxlength)
  | input_atts (Password NONE) = [("type", "password")]
  | input_atts (Password (SOME i)) =
      [("type", "password"), ("maxlength", Int.toString i)]
  | input_atts (Checkbox checked) =
      ("type", "checkbox") :: from_checked checked
  | input_atts (Radio checked) = ("type", "radio") :: from_checked checked
  | input_atts Submit = [("type", "submit")]
  | input_atts Reset = [("type", "reset")]
  | input_atts Hidden = [("type", "hidden")]
  | input_atts (Image { src, alt }) =
      [("type", "image"), ("src", src), ("alt", alt)]
  | input_atts (File { accept }) = [("type", "file"), ("accept", accept)]
  | input_atts Button = [("type", "button")];

fun input (common_atts, { name, itype }) =
  Tag ("input",
       input_atts itype @ [("name", name)] @ from_common common_atts,
       []);

fun reset_button common_atts =
  Tag ("input", input_atts Reset @ from_common common_atts, []);

fun submit_button common_atts =
  Tag ("input", input_atts Submit @ from_common common_atts, []);


fun select (common_atts, { name, value }) options =
  let
    fun is_selected t =
      (case value of
         NONE => []
       | SOME s => if t = s then bool_att ("selected", true) else []);
    fun to_option t = Tag ("option", is_selected t, [Text t]);
  in
    Tag ("select",
      ("name", name) :: from_common common_atts,
      map to_option options)
  end;

fun label (common_atts, { for }, text) =
  Tag ("label", ("for", for) :: from_common common_atts, [Text text]);

datatype event =
    OnClick
  | OnDblClick
  | OnMouseDown
  | OnMouseUp
  | OnMouseOver
  | OnMouseMove
  | OnMouseOut
  | OnKeyPress
  | OnKeyDown
  | OnKeyUp
  | OnFocus
  | OnBlur
  | OnSubmit
  | OnReset
  | OnSelect
  | OnChange
  | OnLoad
  | OnUnload;

fun event_to_str OnClick = "onclick"
  | event_to_str OnDblClick = "ondblclick"
  | event_to_str OnMouseDown = "onmousedown"
  | event_to_str OnMouseUp = "onmouseup"
  | event_to_str OnMouseOver = "onmouseover"
  | event_to_str OnMouseMove = "onmousemove"
  | event_to_str OnMouseOut = "onmouseout"
  | event_to_str OnKeyPress = "onkeypress"
  | event_to_str OnKeyDown = "onkeydown"
  | event_to_str OnKeyUp = "onkeyup"
  | event_to_str OnFocus = "onfocus"
  | event_to_str OnBlur = "onblur"
  | event_to_str OnSubmit = "onsubmit"
  | event_to_str OnReset = "onreset"
  | event_to_str OnSelect = "onselect"
  | event_to_str OnChange = "onchange"
  | event_to_str OnLoad = "onload"
  | event_to_str OnUnload = "onunload";

fun script (common_atts, {script_type, src}) =
  Tag ("script",
    ("type", script_type)
    :: ("src", src)
    :: from_common common_atts, [text ""]);

fun add_script (evty, script) (Tag (name, atts, inner))
      = Tag (name, AList.update (op =) (event_to_str evty, script) atts, inner)
  | add_script _ t = t;


val doctype_xhtml1_0_strict =
  "<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Strict//EN\" \
  \\"http://www.w3.org/TR/xhtml1/DTD/xhtml1-strict.dtd\">\n";

end;

