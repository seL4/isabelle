(*  Title:      Doc/antiquote_setup.ML
    Author:     Makarius

Auxiliary antiquotations for the Isabelle manuals.
*)

structure AntiquoteSetup: sig end =
struct

(* misc utils *)

fun translate f = Symbol.explode #> map f #> implode;

val clean_string = translate
  (fn "_" => "\\_"
    | "#" => "\\#"
    | "<" => "$<$"
    | ">" => "$>$"
    | "{" => "\\{"
    | "|" => "$\\mid$"
    | "}" => "\\}"
    | "\\<dash>" => "-"
    | c => c);

fun clean_name "\\<dots>" = "dots"
  | clean_name ".." = "ddot"
  | clean_name "." = "dot"
  | clean_name "_" = "underscore"
  | clean_name "{" = "braceleft"
  | clean_name "}" = "braceright"
  | clean_name s = s |> translate (fn "_" => "-" | "\\<dash>" => "-" | c => c);


(* verbatim text *)

val verbatim = space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|";

val _ = ThyOutput.antiquotation "verbatim" (fn _ => fn _ =>
  Scan.lift Args.name >> (split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n"));


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
    val _ = ML_Context.eval_in (SOME ctxt) false Position.none (ml (txt1, txt2));
    val kind' = if kind = "" then "ML" else "ML " ^ kind;
  in
    "\\indexdef{}{" ^ kind' ^ "}{" ^ clean_string txt1 ^ "}" ^
    (txt'
    |> (if ! ThyOutput.quotes then quote else I)
    |> (if ! ThyOutput.display then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
        else split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n"))
  end;

fun output_ml ctxt src =
  if ! ThyOutput.display then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
  else
    split_lines
    #> map (space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|")
    #> space_implode "\\isasep\\isanewline%\n";

fun ml_args x = ThyOutput.args (Scan.lift (Args.name -- Scan.optional (Args.colon |-- Args.name) "")) x;

in

val _ = ThyOutput.add_commands
 [("index_ML", ml_args (index_ml "" ml_val)),
  ("index_ML_type", ml_args (index_ml "type" ml_type)),
  ("index_ML_exn", ml_args (index_ml "exception" ml_exn)),
  ("index_ML_structure", ml_args (index_ml "structure" ml_structure)),
  ("index_ML_functor", ml_args (index_ml "functor" ml_functor)),
  ("ML_functor", ThyOutput.args (Scan.lift Args.name) output_ml),
  ("ML_text", ThyOutput.args (Scan.lift Args.name) output_ml)];

end;


(* theorems with names *)

local

fun output_named_thms src ctxt xs =
  map (apfst (ThyOutput.pretty_thm ctxt)) xs        (*always pretty in order to exhibit errors!*)
  |> (if ! ThyOutput.quotes then map (apfst Pretty.quote) else I)
  |> (if ! ThyOutput.display then
    map (fn (p, name) =>
      Output.output (Pretty.string_of (Pretty.indent (! ThyOutput.indent) p)) ^
      "\\rulename{" ^ Output.output (Pretty.str_of (ThyOutput.pretty_text name)) ^ "}")
    #> space_implode "\\par\\smallskip%\n"
    #> enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
  else
    map (fn (p, name) =>
      Output.output (Pretty.str_of p) ^
      "\\rulename{" ^ Output.output (Pretty.str_of (ThyOutput.pretty_text name)) ^ "}")
    #> space_implode "\\par\\smallskip%\n"
    #> enclose "\\isa{" "}");

in

val _ = ThyOutput.add_commands
 [("named_thms", ThyOutput.args (Scan.repeat (Attrib.thm --
      Scan.lift (Args.parens Args.name))) output_named_thms)];

end;


(* theory files *)

val _ = ThyOutput.add_commands
 [("thy_file", ThyOutput.args (Scan.lift Args.name) (ThyOutput.output (fn _ => fn name =>
      (ThyLoad.check_thy Path.current name; Pretty.str name))))];


(* Isabelle entities (with index) *)

local

fun no_check _ _ = true;

fun thy_check intern defined ctxt =
  let val thy = ProofContext.theory_of ctxt
  in defined thy o intern thy end;

fun check_tool name =
  File.exists (Path.append (Path.explode "~~/lib/Tools") (Path.basic name));

val arg = enclose "{" "}" o clean_string;

fun output_entity check markup index kind ctxt (logic, name) =
  let
    val hyper_name = "{" ^ Long_Name.append kind (Long_Name.append logic (clean_name name)) ^ "}";
    val hyper =
      enclose ("\\hyperlink" ^ hyper_name ^ "{") "}" #>
      index = SOME true ? enclose ("\\hypertarget" ^ hyper_name ^ "{") "}";
    val idx =
      (case index of
        NONE => ""
      | SOME is_def =>
          "\\index" ^ (if is_def then "def" else "ref") ^ arg logic ^ arg kind ^ arg name);
  in
    if check ctxt name then
      idx ^
      (Output.output name
        |> (if markup = "" then I else enclose ("\\" ^ markup ^ "{") "}")
        |> (if ! ThyOutput.quotes then quote else I)
        |> (if ! ThyOutput.display then enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
            else hyper o enclose "\\mbox{\\isa{" "}}"))
    else error ("Bad " ^ kind ^ " " ^ quote name)
  end;

fun entity check markup index kind =
  ThyOutput.args (Scan.lift (Scan.optional (Args.parens Args.name) "" -- Args.name))
    (K (output_entity check markup index kind));

fun entity_antiqs check markup kind =
 [(kind, entity check markup NONE kind),
  (kind ^ "_def", entity check markup (SOME true) kind),
  (kind ^ "_ref", entity check markup (SOME false) kind)];

in

val _ = ThyOutput.add_commands
 (entity_antiqs no_check "" "syntax" @
  entity_antiqs (K (is_some o OuterKeyword.command_keyword)) "isacommand" "command" @
  entity_antiqs (K OuterKeyword.is_keyword) "isakeyword" "keyword" @
  entity_antiqs (K OuterKeyword.is_keyword) "isakeyword" "element" @
  entity_antiqs (thy_check Method.intern Method.defined) "" "method" @
  entity_antiqs (thy_check Attrib.intern Attrib.defined) "" "attribute" @
  entity_antiqs no_check "" "fact" @
  entity_antiqs no_check "" "variable" @
  entity_antiqs no_check "" "case" @
  entity_antiqs (K ThyOutput.defined_command) "" "antiquotation" @
  entity_antiqs (fn _ => fn name => is_some (OS.Process.getEnv name)) "isatt" "setting" @
  entity_antiqs no_check "" "inference" @
  entity_antiqs no_check "isatt" "executable" @
  entity_antiqs (K check_tool) "isatt" "tool" @
  entity_antiqs (K (File.exists o Path.explode)) "isatt" "file" @
  entity_antiqs (K ThyInfo.known_thy) "" "theory");

end;

end;
