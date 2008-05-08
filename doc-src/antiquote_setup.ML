(*  Title:      Doc/antiquote_setup.ML
    ID:         $Id$
    Author:     Makarius

Auxiliary antiquotations for the Isabelle manuals.
*)

structure AntiquoteSetup: sig end =
struct

structure O = ThyOutput;


(* misc utils *)

val clean_string = translate_string
  (fn "_" => "\\_"
    | ">" => "$>$"
    | "#" => "\\#"
    | "{" => "\\{"
    | "}" => "\\}"
    | c => c);

val str_of_source = space_implode " " o map Args.string_of o #2 o #1 o Args.dest_src;

fun tweak_line s =
  if ! O.display then s else Symbol.strip_blanks s;

val pretty_text = Pretty.chunks o map Pretty.str o map tweak_line o Library.split_lines;

fun pretty_term ctxt t = Syntax.pretty_term (Variable.auto_fixes t ctxt) t;
fun pretty_thm ctxt = pretty_term ctxt o Thm.full_prop_of;


(* verbatim text *)

val verbatim = space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|";

val _ = O.add_commands
 [("verbatim", O.args (Scan.lift Args.name) (fn _ => fn _ =>
      split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n"))];


(* ML text *)

local

fun ml_val (txt1, "") = "fn _ => (" ^ txt1 ^ ");"
  | ml_val (txt1, txt2) = "fn _ => (" ^ txt1 ^ ": " ^ txt2 ^ ");";

fun ml_type (txt1, "") = "val _ = NONE : (" ^ txt1 ^ ") option;"
  | ml_type (txt1, txt2) = "val _ = [NONE : (" ^ txt1 ^ ") option, NONE : (" ^ txt2 ^ ") option];";

fun ml_exn (txt1, "") = "fn _ => (" ^ txt1 ^ ": exn);"
  | ml_exn (txt1, txt2) = "fn _ => (" ^ txt1 ^ ": " ^ txt2 ^ " -> exn);";

fun ml_structure (txt, _) = "functor DUMMY_FUNCTOR() = struct structure DUMMY = " ^ txt ^ " end;"

fun ml_functor _ = "val _ = ();";  (*no check!*)

fun index_ml kind ml src ctxt (txt1, txt2) =
  let
    val txt = if txt2 = "" then txt1 else
      if kind = "type" then txt1 ^ " = " ^ txt2
      else if kind = "exception" then txt1 ^ " of " ^ txt2
      else txt1 ^ ": " ^ txt2;
    val txt' = if kind = "" then txt else kind ^ " " ^ txt;
    val _ = writeln (ml (txt1, txt2));
    val _ = ML_Context.eval_in (SOME (Context.Proof ctxt)) false Position.none (ml (txt1, txt2));
  in
    "\\indexml" ^ kind ^ enclose "{" "}" (clean_string txt1) ^
    ((if ! O.source then str_of_source src else txt')
    |> (if ! O.quotes then quote else I)
    |> (if ! O.display then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
        else split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n"))
  end;

fun output_ml ctxt src =
  if ! O.display then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
  else
    split_lines
    #> map (space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|")
    #> space_implode "\\isasep\\isanewline%\n";

fun ml_args x = O.args (Scan.lift (Args.name -- Scan.optional (Args.colon |-- Args.name) "")) x;

in

val _ = O.add_commands
 [("index_ML", ml_args (index_ml "" ml_val)),
  ("index_ML_type", ml_args (index_ml "type" ml_type)),
  ("index_ML_exn", ml_args (index_ml "exception" ml_exn)),
  ("index_ML_structure", ml_args (index_ml "structure" ml_structure)),
  ("index_ML_functor", ml_args (index_ml "functor" ml_functor)),
  ("ML_functor", O.args (Scan.lift Args.name) output_ml),
  ("ML_text", O.args (Scan.lift Args.name) output_ml)];

end;


(* theorems with names *)

local

fun output_named_thms src ctxt xs =
  map (apfst (pretty_thm ctxt)) xs        (*always pretty in order to exhibit errors!*)
  |> (if ! O.quotes then map (apfst Pretty.quote) else I)
  |> (if ! O.display then
    map (fn (p, name) =>
      Output.output (Pretty.string_of (Pretty.indent (! O.indent) p)) ^
      "\\rulename{" ^ Output.output (Pretty.str_of (pretty_text name)) ^ "}")
    #> space_implode "\\par\\smallskip%\n"
    #> enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
  else
    map (fn (p, name) =>
      Output.output (Pretty.str_of p) ^
      "\\rulename{" ^ Output.output (Pretty.str_of (pretty_text name)) ^ "}")
    #> space_implode "\\par\\smallskip%\n"
    #> enclose "\\isa{" "}");

in

val _ = O.add_commands
 [("named_thms", O.args (Scan.repeat (Attrib.thm --
      Scan.lift (Args.parens Args.name))) output_named_thms)];

end;


(* theory files *)

val _ = O.add_commands
 [("thy_file", O.args (Scan.lift Args.name) (O.output (fn _ => fn name =>
      (ThyLoad.check_thy Path.current name; Pretty.str name))))];


(* Isar entities (with index) *)

local

val arg = enclose "{" "}" o clean_string;

fun output_entity markup index kind ctxt (logic, name) =
  (case index of
    NONE => ""
  | SOME is_def =>
      "\\index" ^ (if is_def then "def" else "ref") ^ arg logic ^ arg kind ^ arg name)
  ^
  (Output.output name
    |> (if markup = "" then I else enclose ("\\" ^ markup ^ "{") "}")
    |> (if ! O.quotes then quote else I)
    |> (if ! O.display then enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
        else enclose "\\mbox{\\isa{" "}}"));

fun entity markup index kind =
  O.args (Scan.lift (Scan.optional (Args.parens Args.name) "" -- Args.name))
    (K (output_entity markup index kind));
    
fun entity_antiqs markup kind =
 [(kind, entity markup NONE kind),
  (kind ^ "_def", entity markup (SOME true) kind), 
  (kind ^ "_ref", entity markup (SOME false) kind)];

in

val _ = O.add_commands
 (entity_antiqs "" "syntax" @
  entity_antiqs "isacommand" "command" @
  entity_antiqs "isakeyword" "keyword" @
  entity_antiqs "isakeyword" "element" @
  entity_antiqs "" "method" @
  entity_antiqs "" "attribute" @
  entity_antiqs "" "fact" @
  entity_antiqs "" "variable" @
  entity_antiqs "" "case" @
  entity_antiqs "" "antiquotation");

end;

end;
