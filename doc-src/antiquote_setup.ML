(*  Title:      doc-src/antiquote_setup.ML
    Author:     Makarius

Auxiliary antiquotations for the Isabelle manuals.
*)

signature ANTIQUOTE_SETUP =
sig
  val setup: theory -> theory
end;

structure Antiquote_Setup: ANTIQUOTE_SETUP =
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
    | "\<hyphen>" => "-"
    | c => c);

fun clean_name "\<dots>" = "dots"
  | clean_name ".." = "ddot"
  | clean_name "." = "dot"
  | clean_name "_" = "underscore"
  | clean_name "{" = "braceleft"
  | clean_name "}" = "braceright"
  | clean_name s = s |> translate (fn "_" => "-" | "\<hyphen>" => "-" | c => c);


(* verbatim text *)

val verbatim = space_implode "\\verb,|," o map (enclose "\\verb|" "|") o space_explode "|";

val verbatim_setup =
  Thy_Output.antiquotation @{binding verbatim} (Scan.lift Args.name)
    (K (split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n"));


(* ML text *)

local

fun ml_val (txt1, "") = "fn _ => (" ^ txt1 ^ ");"
  | ml_val (txt1, txt2) = "fn _ => (" ^ txt1 ^ " : " ^ txt2 ^ ");";

fun ml_op (txt1, "") = "fn _ => (op " ^ txt1 ^ ");"
  | ml_op (txt1, txt2) = "fn _ => (op " ^ txt1 ^ " : " ^ txt2 ^ ");";

fun ml_type (txt1, "") = "val _ = NONE : (" ^ txt1 ^ ") option;"
  | ml_type (txt1, txt2) = "val _ = [NONE : (" ^ txt1 ^ ") option, NONE : (" ^ txt2 ^ ") option];";

fun ml_exn (txt1, "") = "fn _ => (" ^ txt1 ^ " : exn);"
  | ml_exn (txt1, txt2) = "fn _ => (" ^ txt1 ^ " : " ^ txt2 ^ " -> exn);";

fun ml_structure (txt, _) = "functor XXX() = struct structure XX = " ^ txt ^ " end;";

fun ml_functor (txt, _) = "ML_Env.check_functor " ^ ML_Syntax.print_string txt;

val is_name = ML_Lex.kind_of #> (fn kind => kind = ML_Lex.Ident orelse kind = ML_Lex.LongIdent);

fun ml_name txt =
  (case filter is_name (ML_Lex.tokenize txt) of
    toks as [_] => ML_Lex.flatten toks
  | _ => error ("Single ML name expected in input: " ^ quote txt));

fun index_ml name kind ml = Thy_Output.antiquotation name
  (Scan.lift (Args.name -- Scan.optional (Args.colon |-- Args.name) ""))
  (fn {context = ctxt, ...} => fn (txt1, txt2) =>
    let
      val txt =
        if txt2 = "" then txt1
        else if kind = "type" then txt1 ^ " = " ^ txt2
        else if kind = "exception" then txt1 ^ " of " ^ txt2
        else if Lexicon.is_identifier (Long_Name.base_name (ml_name txt1))
        then txt1 ^ ": " ^ txt2
        else txt1 ^ " : " ^ txt2;
      val txt' = if kind = "" then txt else kind ^ " " ^ txt;
      val _ = ML_Context.eval_text_in (SOME ctxt) false Position.none (ml (txt1, txt2));  (* ML_Lex.read (!?) *)
      val kind' = if kind = "" then "ML" else "ML " ^ kind;
    in
      "\\indexdef{}{" ^ kind' ^ "}{" ^ clean_string (ml_name txt1) ^ "}" ^
      (txt'
      |> (if Config.get ctxt Thy_Output.quotes then quote else I)
      |> (if Config.get ctxt Thy_Output.display then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
          else split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n"))
    end);

in

val index_ml_setup =
  index_ml @{binding index_ML} "" ml_val #>
  index_ml @{binding index_ML_op} "infix" ml_op #>
  index_ml @{binding index_ML_type} "type" ml_type #>
  index_ml @{binding index_ML_exn} "exception" ml_exn #>
  index_ml @{binding index_ML_structure} "structure" ml_structure #>
  index_ml @{binding index_ML_functor} "functor" ml_functor;

end;


(* named theorems *)

val named_thms_setup =
  Thy_Output.antiquotation @{binding named_thms}
    (Scan.repeat (Attrib.thm -- Scan.lift (Args.parens Args.name)))
    (fn {context = ctxt, ...} =>
      map (apfst (Thy_Output.pretty_thm ctxt))
      #> (if Config.get ctxt Thy_Output.quotes then map (apfst Pretty.quote) else I)
      #> (if Config.get ctxt Thy_Output.display
          then
            map (fn (p, name) =>
              Output.output (Pretty.string_of (Pretty.indent (Config.get ctxt Thy_Output.indent) p)) ^
              "\\rulename{" ^ Output.output (Pretty.str_of (Thy_Output.pretty_text ctxt name)) ^ "}")
            #> space_implode "\\par\\smallskip%\n"
            #> enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
          else
            map (fn (p, name) =>
              Output.output (Pretty.str_of p) ^
              "\\rulename{" ^ Output.output (Pretty.str_of (Thy_Output.pretty_text ctxt name)) ^ "}")
            #> space_implode "\\par\\smallskip%\n"
            #> enclose "\\isa{" "}"));


(* theory file *)

val thy_file_setup =
  Thy_Output.antiquotation @{binding thy_file} (Scan.lift Args.name)
    (fn {context = ctxt, ...} =>
      fn name => (Thy_Load.check_thy Path.current name; Thy_Output.output ctxt [Pretty.str name]));


(* Isabelle/Isar entities (with index) *)

local

fun no_check _ _ = true;

fun thy_check intern defined ctxt =
  let val thy = Proof_Context.theory_of ctxt
  in defined thy o intern thy end;

fun check_tool name =
  File.exists (Path.append (Path.explode "~~/lib/Tools") (Path.basic name));

val arg = enclose "{" "}" o clean_string;

fun entity check markup kind index =
  Thy_Output.antiquotation
    (Binding.name (translate (fn " " => "_" | c => c) kind ^
      (case index of NONE => "" | SOME true => "_def" | SOME false => "_ref")))
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
            |> (if Config.get ctxt Thy_Output.quotes then quote else I)
            |> (if Config.get ctxt Thy_Output.display
                then enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
                else hyper o enclose "\\mbox{\\isa{" "}}"))
        else error ("Bad " ^ kind ^ " " ^ quote name)
      end);

fun entity_antiqs check markup kind =
  entity check markup kind NONE #>
  entity check markup kind (SOME true) #>
  entity check markup kind (SOME false);

in

val entity_setup =
  entity_antiqs no_check "" "syntax" #>
  entity_antiqs (K (is_some o Keyword.command_keyword)) "isacommand" "command" #>
  entity_antiqs (K Keyword.is_keyword) "isakeyword" "keyword" #>
  entity_antiqs (K Keyword.is_keyword) "isakeyword" "element" #>
  entity_antiqs (thy_check Method.intern Method.defined) "" "method" #>
  entity_antiqs (thy_check Attrib.intern Attrib.defined) "" "attribute" #>
  entity_antiqs no_check "" "fact" #>
  entity_antiqs no_check "" "variable" #>
  entity_antiqs no_check "" "case" #>
  entity_antiqs (thy_check Thy_Output.intern_command Thy_Output.defined_command)
    "" "antiquotation" #>
  entity_antiqs (thy_check Thy_Output.intern_option Thy_Output.defined_option)
    "" "antiquotation option" #>
  entity_antiqs (fn _ => fn name => is_some (OS.Process.getEnv name)) "isatt" "setting" #>
  entity_antiqs no_check "" "inference" #>
  entity_antiqs no_check "isatt" "executable" #>
  entity_antiqs (K check_tool) "isatt" "tool" #>
  entity_antiqs (thy_check ML_Context.intern_antiq ML_Context.defined_antiq)
    "" Isabelle_Markup.ML_antiquotationN;

end;


(* theory setup *)

val setup =
  verbatim_setup #>
  index_ml_setup #>
  named_thms_setup #>
  thy_file_setup #>
  entity_setup;

end;
