(*  Title:      doc-src/antiquote_setup.ML
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

val _ = ThyOutput.antiquotation "verbatim" (Scan.lift Args.name)
  (K (split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n"));


(* ML text *)

local

fun ml_val (txt1, "") = "fn _ => (" ^ txt1 ^ ");"
  | ml_val (txt1, txt2) = "fn _ => (" ^ txt1 ^ ": " ^ txt2 ^ ");";

fun ml_type (txt1, "") = "val _ = NONE : (" ^ txt1 ^ ") option;"
  | ml_type (txt1, txt2) = "val _ = [NONE : (" ^ txt1 ^ ") option, NONE : (" ^ txt2 ^ ") option];";

fun ml_exn (txt1, "") = "fn _ => (" ^ txt1 ^ ": exn);"
  | ml_exn (txt1, txt2) = "fn _ => (" ^ txt1 ^ ": " ^ txt2 ^ " -> exn);";

fun ml_structure (txt, _) = "functor XXX() = struct structure XX = " ^ txt ^ " end;";

fun ml_functor _ = "";  (*no check!*)

fun index_ml name kind ml = ThyOutput.antiquotation name
  (Scan.lift (Args.name -- Scan.optional (Args.colon |-- Args.name) ""))
  (fn {context = ctxt, ...} => fn (txt1, txt2) =>
    let
      val txt =
        if txt2 = "" then txt1
        else if kind = "type" then txt1 ^ " = " ^ txt2
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
    end);

in

val _ = index_ml "index_ML" "" ml_val;
val _ = index_ml "index_ML_type" "type" ml_type;
val _ = index_ml "index_ML_exn" "exception" ml_exn;
val _ = index_ml "index_ML_structure" "structure" ml_structure;
val _ = index_ml "index_ML_functor" "functor" ml_functor;

end;


(* named theorems *)

val _ = ThyOutput.antiquotation "named_thms"
  (Scan.repeat (Attrib.thm -- Scan.lift (Args.parens Args.name)))
  (fn {context = ctxt, ...} =>
    map (apfst (ThyOutput.pretty_thm ctxt))
    #> (if ! ThyOutput.quotes then map (apfst Pretty.quote) else I)
    #> (if ! ThyOutput.display
        then
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
          #> enclose "\\isa{" "}"));


(* theory file *)

val _ = ThyOutput.antiquotation "thy_file" (Scan.lift Args.name)
  (fn _ => fn name => (ThyLoad.check_thy Path.current name; ThyOutput.output [Pretty.str name]));


(* Isabelle/Isar entities (with index) *)

local

fun no_check _ _ = true;

fun thy_check intern defined ctxt =
  let val thy = ProofContext.theory_of ctxt
  in defined thy o intern thy end;

fun check_tool name =
  File.exists (Path.append (Path.explode "~~/lib/Tools") (Path.basic name));

val arg = enclose "{" "}" o clean_string;

fun entity check markup kind index =
  ThyOutput.antiquotation
    (case index of NONE => kind | SOME true => kind ^ "_def" | SOME false => kind ^ "_ref")
    (Scan.lift (Scan.optional (Args.parens Args.name) "" -- Args.name))
    (fn {context = ctxt, ...} => fn (logic, name) =>
      let
        val hyper_name =
          "{" ^ Long_Name.append kind (Long_Name.append logic (clean_name name)) ^ "}";
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
      end);

fun entity_antiqs check markup kind =
 [(entity check markup kind NONE),
  (entity check markup kind (SOME true)),
  (entity check markup kind (SOME false))];

in

val _ = entity_antiqs no_check "" "syntax";
val _ = entity_antiqs (K (is_some o OuterKeyword.command_keyword)) "isacommand" "command";
val _ = entity_antiqs (K OuterKeyword.is_keyword) "isakeyword" "keyword";
val _ = entity_antiqs (K OuterKeyword.is_keyword) "isakeyword" "element";
val _ = entity_antiqs (thy_check Method.intern Method.defined) "" "method";
val _ = entity_antiqs (thy_check Attrib.intern Attrib.defined) "" "attribute";
val _ = entity_antiqs no_check "" "fact";
val _ = entity_antiqs no_check "" "variable";
val _ = entity_antiqs no_check "" "case";
val _ = entity_antiqs (K ThyOutput.defined_command) "" "antiquotation";
val _ = entity_antiqs (fn _ => fn name => is_some (OS.Process.getEnv name)) "isatt" "setting";
val _ = entity_antiqs no_check "" "inference";
val _ = entity_antiqs no_check "isatt" "executable";
val _ = entity_antiqs (K check_tool) "isatt" "tool";
val _ = entity_antiqs (K (File.exists o Path.explode)) "isatt" "file";
val _ = entity_antiqs (K ThyInfo.known_thy) "" "theory";

end;

end;
