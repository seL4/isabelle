datatype token =
  Identifier of string |
  Special_Identifier of string |
  Text of string |
  Anot of string |
  Symbol of string |
  EOF;

fun is_identifier (Identifier _) = true
  | is_identifier (Special_Identifier _ ) = true
  | is_identifier _ = false;
  
fun is_text (Text _) = true
  | is_text _ = false;

fun is_anot (Anot _) = true
  | is_anot _ = false;

fun is_symbol (Symbol _) = true
  | is_symbol _ = false;

fun is_ str = (fn s => s = Symbol str);


local (* copied from antiquote-setup... *)
fun translate f = Symbol.explode #> map f #> implode;

fun clean_name "\<dots>" = "dots"
  | clean_name ".." = "ddot"
  | clean_name "." = "dot"
  | clean_name "_" = "underscore"
  | clean_name "{" = "braceleft"
  | clean_name "}" = "braceright"
  | clean_name s = s |> translate (fn "_" => "-" | "\<dash>" => "-" | c => c);

fun no_check _ _ = true;

fun false_check _ _ = false;

fun thy_check intern defined ctxt =
  let val thy = ProofContext.theory_of ctxt
  in defined thy o intern thy end;

fun check_tool name =
  File.exists (Path.append (Path.explode "~~/lib/Tools") (Path.basic name));

val arg = enclose "{" "}";

val markup_table =
(*  [(kind, (markup, check, style))*)
  Symtab.make [
  ("syntax", ("", no_check, true)),
  ("command", ("isacommand", K (is_some o OuterKeyword.command_keyword), true)),
  ("keyword", ("isakeyword", K OuterKeyword.is_keyword, true)),
  ("element", ("isakeyword", K OuterKeyword.is_keyword, true)),
  ("method", ("", thy_check Method.intern Method.defined, true)),
  ("attribute", ("", thy_check Attrib.intern Attrib.defined, true)),
  ("fact", ("", no_check, true)),
  ("variable", ("", no_check, true)),
  ("case", ("", no_check, true)),
  ("antiquotation", ("", K ThyOutput.defined_command, true)),
  ("antiquotation option", ("", K ThyOutput.defined_option, true)), (* kann mein scanner nicht erkennen *)
  ("setting", ("isatt", (fn _ => fn name => is_some (OS.Process.getEnv name)), true)),
  ("inference", ("", no_check, true)),
  ("executable", ("isatt", no_check, true)),
  ("tool", ("isatt", K check_tool, true)),
  ("file", ("isatt", K (File.exists o Path.explode), true)),
  ("theory", ("", K ThyInfo.known_thy, true)) 
  ];

in

fun decode_link ctxt (kind,index,logic,name) =
  let
  val (markup, check, style) = case Symtab.lookup markup_table kind of
    SOME x => x
  | NONE => ("", false_check, false);
  val hyper_name =
    "{" ^ Long_Name.append kind (Long_Name.append logic (clean_name name)) ^ "}";
  val hyper =
    enclose ("\\hyperlink" ^ hyper_name ^ "{") "}" #>
    index = "def" ? enclose ("\\hypertarget" ^ hyper_name ^ "{") "}";
  val idx =
    if index = "" then ""
    else "\\index" ^ index ^ arg logic ^ arg kind ^ arg name;
  in
  if check ctxt name then
    (idx ^
    (Output.output name
      |> (if markup = "" then I else enclose ("\\" ^ markup ^ "{") "}")
      |> (if ! ThyOutput.quotes then quote else I)
      |> (if ! ThyOutput.display then enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
	  else hyper o enclose "\\mbox{\\isa{" "}}")), style)
  else ("Bad " ^ kind ^ " " ^ name, false)
  end;
end;

val blanks =
  Scan.many Symbol.is_blank >> implode;

val scan_symbol =
  $$ ";" || $$ ":"|| $$ "("|| $$ ")"|| $$ "+"|| $$ "|"|| $$ "*"|| $$ "?"|| $$ "\\";

(* escaped version *)
val scan_link = (* @{kind{_def|_ref (logic) name} *)
  let
    fun pseudo_antiquote inner_scan = ($$ "@" ^^ $$ "{") |-- inner_scan --| (blanks -- $$ "}");
    fun parens scan = $$ "(" |-- scan --| $$ ")";
    fun opt_quotes scan = $$ "'" |-- scan --| $$ "'" || scan;
    val letters = Scan.many Symbol.is_letter >> implode;
    val kind_name = letters;
    val opt_kind_type = Scan.optional (
      $$ "_" |-- (Scan.this_string "def" || Scan.this_string "ref")) "";
    val logic_name = letters;
    val escaped_singlequote = $$ "\\" |-- $$ "'";
    val text = Scan.repeat (Scan.one Symbol.is_letter || escaped_singlequote) >> implode;
  in
   pseudo_antiquote (
    kind_name -- opt_kind_type --
    (blanks |-- Scan.optional ( parens logic_name ) "") --
    (blanks |-- opt_quotes text) )
    >> (fn (((kind,index),logic),name) => (kind, index, logic, name))
end;

(* escaped version *)
fun scan_identifier ctxt = 
  let fun is_identifier_start s =
    Symbol.is_letter s orelse
    s = "_"
  fun is_identifier_rest s =
    Symbol.is_letter s orelse
    Symbol.is_digit s orelse
    s = "_" orelse
    s = "."
  in
  (Scan.one is_identifier_start :::
    Scan.repeat (Scan.one is_identifier_rest || ($$ "\\" |-- $$ "'"))
  ) >> (Identifier o enclose "\\isa{" "}" o Output.output o implode) ||
  scan_link >> (decode_link ctxt) >>
    (fn (txt, style) =>
	if style then Special_Identifier(txt)
	else Identifier(txt))
end;

fun scan_anot ctxt =
  let val scan_anot =
    Scan.many (fn s =>
      s <> "\n" andalso
      s <> "\t" andalso
      s <> "]" andalso
      Symbol.is_regular s) >> implode
  in
  $$ "[" |-- scan_link --| $$ "]" >> (fst o (decode_link ctxt)) ||
  $$ "[" |-- scan_anot --| $$ "]" >> Output.output
end;

(* escaped version *)
fun scan_text ctxt =
  let
    val text_sq =
      Scan.repeat (
        Scan.one (fn s =>
	  s <> "\n" andalso
	  s <> "\t" andalso
	  s <> "'" andalso
	  s <> "\\" andalso
	  Symbol.is_regular s) ||
	($$ "\\" |-- $$ "'")
      ) >> implode
  fun quoted scan = $$ "'" |-- scan --| $$ "'";
  in
  quoted scan_link >> (fst o (decode_link ctxt)) ||
  quoted text_sq >> (enclose "\\isa{" "}" o Output.output)
end;

fun scan_rail ctxt =
  Scan.repeat ( blanks |-- (
    scan_identifier ctxt ||
    scan_anot ctxt >> Anot ||
    scan_text ctxt >> Text ||
    scan_symbol >> Symbol)
  ) --| blanks;

fun lex_rail txt ctxt = (* Symbol_Pos fuer spaeter durchgereicht *)
  Symbol.scanner "Malformed rail-declaration" (scan_rail ctxt) (map fst (Symbol_Pos.explode txt));

val lex = lex_rail;

datatype id_kind = UNKNOWN | TOKEN | TERM | NTERM;

datatype id_type =
  Id of string * id_kind |
  Null_Id;

datatype body_kind =
  CAT | BAR | PLUS |
  CR | EMPTY | ANNOTE | IDENT | STRING |
  Null_Kind;

datatype body_type =	
  Body of body_kind * string * string * id_type * body_type list |
  Body_Pos of body_kind * string * string * id_type * body_type list * int * int |
  Empty_Body |
  Null_Body;

datatype rule = 
  Rule of id_type * body_type;

fun new_id id kind = Id (id, kind);

fun is_empty (Body(kind,_,_,_,_)) = kind = EMPTY;

fun new_body (kind, Null_Body, Null_Body) = Body (kind, "", "", Null_Id, [])
  | new_body (kind, body1, body2) = Body (kind, "", "", Null_Id, body1 :: [body2]);

fun is_kind_of kind (Body(bodyKind,_,_,_,_)) = kind = bodyKind
  | is_kind_of _ _ = false;

fun add_list (Body(kind, text, annot, id, bodies), body) =
  Body(kind, text, annot, id, bodies @ [body]);

fun cat_body_lists (Body(kind, text, annot, id, bodies1), Body(_,_,_,_, bodies2)) = 
      Body(kind, text, annot, id, bodies1 @ bodies2);

fun add_body (kind, body1 as Body(kind1,_,_,_,_), body2 as Body(kind2,_,_,_,_)) =
  if kind = kind1 andalso kind <> BAR then
    if kind = kind2 then
      cat_body_lists(body1, body2)
    else (* kind <> kind2 *)
      add_list(body1, body2)
  else (* kind <> kind1 orelse kind = BAR *)
    if kind = kind2 then
      cat_body_lists(add_list(new_body(kind,Null_Body,Null_Body), body1), body2)
    else (* kind <> kind2 *)
      add_list(add_list(new_body(kind,Null_Body,Null_Body), body1), body2);

fun rev_body (body as Body (kind, text, annot, id, [])) = body
  | rev_body (Body (CAT, text, annot, id, bodies)) =
      Body(CAT, text, annot, id, map rev_body (rev bodies))
  | rev_body (Body (kind, text, annot, id, bodies)) =
      Body(kind, text, annot, id, map rev_body bodies)
  | rev_body body = body;

fun set_body_text text (Body(k,_,a,i,b)) = Body(k,text,a,i,b);
fun set_body_anot anot (Body(k,t,_,i,b)) = Body(k,t,anot,i,b);
fun set_body_ident id (Body(k,t,a,_,b)) = Body(k,t,a, new_id id TOKEN,b);
fun set_body_special_ident id (Body(k,t,a,_,b)) = Body(k,t,a, new_id id TERM,b);


fun mk_eof _ = EOF;
fun is_eof s = s = EOF;
val stopper = Scan.stopper mk_eof is_eof;

(* TODO: change this, so the next or next two tokens are printed *)
fun lex_err msg (cs, _) = "rail grammar error: " ^ msg cs;
fun !!! msg scan = Scan.!! (lex_err (K msg)) scan;
fun $$$ tok = Scan.one (is_ tok);


local
fun new_bar_body([], body2) = body2
  | new_bar_body(body1::bodies, body2) =
      add_body(BAR, body1, new_bar_body(bodies, body2));

fun new_cat_body(body::[]) = body
  | new_cat_body(body1::bodies) = add_body(CAT, body1, new_cat_body(bodies));

fun new_annote_body (Anot anot) =
  set_body_text anot (new_body(ANNOTE, Empty_Body, Empty_Body));

fun new_text_annote_body (Text text, Anot anot) =
  set_body_anot anot (set_body_text text (new_body(STRING, Empty_Body, Empty_Body)));

fun new_ident_body (Identifier ident, Anot anot) =
      set_body_anot anot (set_body_ident ident (new_body(IDENT, Empty_Body, Empty_Body)))
  | new_ident_body (Special_Identifier ident, Anot anot) =
      set_body_anot anot (set_body_special_ident ident (new_body(IDENT, Empty_Body, Empty_Body)));

val new_empty_body = new_body(EMPTY, Null_Body, Null_Body);
in

fun parse_body x =
  (
  Scan.repeat1 (parse_body0 --| $$$ "|") -- !!! "body0 expected" (parse_body0) >>
    new_bar_body ||
  parse_body0
  ) x
and parse_body0 x =
  (
  Scan.one is_anot -- !!! "body1 expected" (parse_body1) >>
    (fn (anot, body) => add_body(CAT, new_annote_body(anot), body))  ||
  parse_body1
  ) x
and parse_body1 x =
  (
  parse_body2 -- ($$$ "*" |-- !!! "body4e expected" (parse_body4e)) >>
    (fn (body1, body2) =>
      if is_empty body2 then
	add_body(PLUS, new_empty_body, rev_body body1)
      else
	add_body(BAR, new_empty_body, add_body (PLUS, body1, rev_body body2)) ) ||
  parse_body2 -- ($$$ "+" |-- !!! "body4e expected" (parse_body4e)) >> 
    (fn (body1, body2) => new_body (PLUS, body1, rev_body body2) ) ||
  parse_body2e
  ) x
and parse_body2e x =
  (
  parse_body2 ||
  (fn toks => (new_empty_body, toks))
  ) x
and parse_body2 x =
  (
  Scan.repeat1 (parse_body3) >> new_cat_body
  ) x
and parse_body3 x =
  (
  parse_body4 --| $$$ "?" >> (fn body => new_body (BAR, new_empty_body, body) ) ||
  parse_body4
  ) x
and parse_body4e x =
  (
  parse_body4 ||
  (fn toks => (new_empty_body, toks))
  ) x
and parse_body4 x =
  (
  $$$ "(" |-- !!! "body0 or ')' expected" (parse_body --| $$$ ")") ||
  Scan.one is_text -- (Scan.optional (Scan.one is_anot) (Anot(""))) >>
    (fn (text, anot) => new_text_annote_body (text,anot)) ||    
  Scan.one is_identifier -- (Scan.optional (Scan.one is_anot) (Anot(""))) >>
    (fn (id, anot) => new_ident_body (id,anot)) ||
  $$$ "\\" >> (fn _ => new_body (CR, Null_Body, Null_Body))
  ) x;
end;

fun new_named_rule (Identifier name, body) = Rule(Id(name, UNKNOWN), body)
  | new_named_rule (Special_Identifier name, body) = Rule(Id(name, UNKNOWN), body);
fun new_anonym_rule body = Rule(Null_Id, body);

val parse_rule =
  (Scan.one (is_identifier) -- ($$$ ":" |-- !!! "body expected" (parse_body)) ) >>
    new_named_rule ||
  parse_body >> new_anonym_rule;

val parse_rules =
  Scan.repeat ( parse_rule --| $$$ ";") @@@ Scan.single parse_rule;

fun parse_rail s =
  Scan.read stopper parse_rules s;

val parse = parse_rail;

fun getystart (Body_Pos(_,_,_,_,_,ystart,_)) = ystart;
fun getynext (Body_Pos(_,_,_,_,_,_,ynext)) = ynext;

fun position_body (body as Body(kind, text, annot, id, bodies), ystart) =
  let fun max (x,y) = if x > y then x else y
    fun set_body_position (Body(kind, text, annot, id, bodies), ystart, ynext) =
	  Body_Pos(kind, text, annot, id, bodies, ystart, ynext)
    fun pos_bodies_cat ([],_,ynext,liste) = (liste, ynext)
      | pos_bodies_cat (x::xs, ystart, ynext, liste) =
	  if is_kind_of CR x then
	      (case set_body_position(x, ystart, ynext+1) of
		body as Body_Pos(_,_,_,_,_,_,ynext1) =>
		  pos_bodies_cat(xs, ynext1, max(ynext,ynext1), liste@[body])
	      )
	  else
	      (case position_body(x, ystart) of
		body as Body_Pos(_,_,_,_,_,_,ynext1) =>
		  pos_bodies_cat(xs, ystart, max(ynext,ynext1), liste@[body])
	      )
    fun pos_bodies_bar_plus ([],_,ynext,liste) = (liste, ynext)
      | pos_bodies_bar_plus (x::xs, ystart, ynext, liste) =
	  (case position_body(x, ystart) of
	    body as Body_Pos(_,_,_,_,_,_,ynext1) =>
	      pos_bodies_bar_plus(xs, ynext1, max(ynext,ynext1), liste@[body])
	  )
  in
  (case kind of
    CAT => (case pos_bodies_cat(bodies,ystart,ystart+1,[]) of
	      (bodiesPos, ynext) =>
		Body_Pos(kind, text, annot, id, bodiesPos, ystart, ynext))
  | BAR => (case pos_bodies_bar_plus(bodies,ystart,ystart+1,[]) of
	      (bodiesPos, ynext) =>
		Body_Pos(kind, text, annot, id, bodiesPos, ystart, ynext))
  | PLUS => (case pos_bodies_bar_plus(bodies,ystart,ystart+1,[]) of
	      (bodiesPos, ynext) =>
		Body_Pos(kind, text, annot, id, bodiesPos, ystart, ynext))
  | CR => set_body_position(body, ystart, ystart+3)
  | EMPTY => set_body_position(body, ystart, ystart+1)
  | ANNOTE => set_body_position(body, ystart, ystart+1)
  | IDENT => set_body_position(body, ystart, ystart+1)
  | STRING => set_body_position(body, ystart, ystart+1)
  )
  end;

fun format_body (Body_Pos(EMPTY,_,_,_,_,_,_), _) = ""
  | format_body (Body_Pos(CAT,_,_,_,bodies,_,_), cent) =
    let fun format_bodies([]) = ""
	  | format_bodies(x::xs) = format_body (x, "") ^ format_bodies(xs)
    in
      format_bodies(bodies)
    end
  | format_body (Body_Pos(BAR,_,_,_,bodies,_,_),cent) = 
    let fun format_bodies([]) = "\\rail@endbar\n"
	  | format_bodies(x::xs) =
	      "\\rail@nextbar{" ^ string_of_int(getystart(x)) ^"}\n" ^
	      format_body(x, "") ^ format_bodies(xs)
    in
      "\\rail@bar\n" ^ format_body(hd(bodies), "") ^ format_bodies(tl(bodies))
    end
  | format_body (Body_Pos(PLUS,_,_,_,x::y::xs,_,_),cent) =
      "\\rail@plus\n" ^ format_body(x, cent) ^
      "\\rail@nextplus{" ^ string_of_int(getystart(y)) ^ "}\n" ^
      format_body(y, "c") ^
      "\\rail@endplus\n"
  | format_body (Body_Pos(ANNOTE,text,_,_,_,_,_),cent) =
      "\\rail@annote[" ^ text ^ "]\n"
  | format_body (Body_Pos(IDENT,_,annot,Id(name,TERM),_,_,_),cent) =
      "\\rail@" ^ cent ^ "token{" ^ name ^ "}" ^ "[" ^ annot ^ "]\n"
  | format_body (Body_Pos(IDENT,_,annot,Id(name,_),_,_,_),cent) =
      "\\rail@" ^ cent ^ "nont{" ^ name ^ "}" ^ "[" ^ annot ^ "]\n"
  | format_body (Body_Pos(CR,_,_,_,_,_,ynext),cent) =
      "\\rail@cr{" ^ string_of_int(ynext) ^ "}\n"
  | format_body (Body_Pos(STRING,text,annot,_,_,_,_),cent) =
      "\\rail@" ^ cent ^ "term{" ^ text ^ "}[" ^ annot ^ "]\n"
  | format_body _ =
      "\\rail@unknown\n";

fun out_body (Id(name,_), body) =
  let val bodyPos as Body_Pos(_,_,_,_,_,_,ynext) = position_body(body,0)
  in
    "\\rail@begin{" ^ string_of_int(ynext) ^ "}{" ^ name ^ "}\n" ^
    format_body(bodyPos,"") ^
    "\\rail@end\n"
  end
  | out_body (Null_Id, body) = out_body (Id("", UNKNOWN), body);

fun out_rule (Rule(id, body)) =
  if is_empty body then ""
  else out_body (id, body);

fun out_rules ([]) = ""
  | out_rules (rule::rules) = out_rule rule ^ out_rules rules;

val output_no_rules =
  "\\rail@begin{1}{}\n" ^
  "\\rail@setbox{\\bfseries ???}\n" ^
  "\\rail@oval\n" ^
  "\\rail@end\n";


fun print (SOME rules) =
    "\\begin{railoutput}\n" ^
    out_rules rules ^
    "\\end{railoutput}\n"
  | print (NONE) =
    "\\begin{railoutput}\n" ^
    output_no_rules ^
    "\\end{railoutput}\n";

fun process txt ctxt =
  lex txt ctxt
  |> parse
  |> print;

val _ = ThyOutput.antiquotation "rail" (Scan.lift ( OuterParse.position Args.name ))
  (fn {context = ctxt,...} => fn txt => process txt ctxt);
