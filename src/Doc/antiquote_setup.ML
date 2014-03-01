(*  Title:      Doc/antiquote_setup.ML
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
    | "$" => "\\$"
    | "%" => "\\%"
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

val ml_toks = ML_Lex.read Position.none;

fun ml_val (toks1, []) = ml_toks "fn _ => (" @ toks1 @ ml_toks ");"
  | ml_val (toks1, toks2) = ml_toks "fn _ => (" @ toks1 @ ml_toks " : " @ toks2 @ ml_toks ");";

fun ml_op (toks1, []) = ml_toks "fn _ => (op " @ toks1 @ ml_toks ");"
  | ml_op (toks1, toks2) = ml_toks "fn _ => (op " @ toks1 @ ml_toks " : " @ toks2 @ ml_toks ");";

fun ml_type (toks1, []) = ml_toks "val _ = NONE : (" @ toks1 @ ml_toks ") option;"
  | ml_type (toks1, toks2) =
      ml_toks "val _ = [NONE : (" @ toks1 @ ml_toks ") option, NONE : (" @
        toks2 @ ml_toks ") option];";

fun ml_exn (toks1, []) = ml_toks "fn _ => (" @ toks1 @ ml_toks " : exn);"
  | ml_exn (toks1, toks2) =
      ml_toks "fn _ => (" @ toks1 @ ml_toks " : " @ toks2 @ ml_toks " -> exn);";

fun ml_structure (toks, _) =
  ml_toks "functor XXX() = struct structure XX = " @ toks @ ml_toks " end;";

fun ml_functor (Antiquote.Text tok :: _, _) =
      ml_toks "ML_Env.check_functor " @ ml_toks (ML_Syntax.print_string (ML_Lex.content_of tok))
  | ml_functor _ = raise Fail "Bad ML functor specification";

val is_name = ML_Lex.kind_of #> (fn kind => kind = ML_Lex.Ident orelse kind = ML_Lex.LongIdent);

fun ml_name txt =
  (case filter is_name (ML_Lex.tokenize txt) of
    toks as [_] => ML_Lex.flatten toks
  | _ => error ("Single ML name expected in input: " ^ quote txt));

fun prep_ml source =
  (#1 (Symbol_Pos.source_content source), ML_Lex.read_source source);

fun index_ml name kind ml = Thy_Output.antiquotation name
  (Scan.lift (Args.name_source_position -- Scan.option (Args.colon |-- Args.name_source_position)))
  (fn {context = ctxt, ...} => fn (source1, opt_source2) =>
    let
      val (txt1, toks1) = prep_ml source1;
      val (txt2, toks2) =
        (case opt_source2 of
          SOME source => prep_ml source
        | NONE => ("", []));

      val txt =
        if txt2 = "" then txt1
        else if kind = "type" then txt1 ^ " = " ^ txt2
        else if kind = "exception" then txt1 ^ " of " ^ txt2
        else if Symbol_Pos.is_identifier (Long_Name.base_name (ml_name txt1))
        then txt1 ^ ": " ^ txt2
        else txt1 ^ " : " ^ txt2;
      val txt' = if kind = "" then txt else kind ^ " " ^ txt;

      val _ = ML_Context.eval_in (SOME ctxt) false (#pos source1) (ml (toks1, toks2));
      val kind' = if kind = "" then "ML" else "ML " ^ kind;
    in
      "\\indexdef{}{" ^ kind' ^ "}{" ^ clean_string (ml_name txt1) ^ "}" ^
      (txt'
      |> (if Config.get ctxt Thy_Output.quotes then quote else I)
      |> (if Config.get ctxt Thy_Output.display
          then enclose "\\begin{verbatim}\n" "\n\\end{verbatim}"
          else split_lines #> map verbatim #> space_implode "\\isasep\\isanewline%\n"))
    end);

in

val index_ml_setup =
  index_ml @{binding index_ML} "" ml_val #>
  index_ml @{binding index_ML_op} "infix" ml_op #>
  index_ml @{binding index_ML_type} "type" ml_type #>
  index_ml @{binding index_ML_exn} "exception" ml_exn #>
  index_ml @{binding index_ML_struct} "structure" ml_structure #>
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

fun command_check (name, pos) =
  is_some (Keyword.command_keyword name) andalso
    let
      val markup =
        Outer_Syntax.scan Position.none name
        |> maps (Outer_Syntax.command_reports (#2 (Outer_Syntax.get_syntax ())))
        |> map (snd o fst);
      val _ = List.app (Position.report pos) markup;
    in true end;

fun check_tool (name, pos) =
  let
    fun tool dir =
      let val path = Path.append dir (Path.basic name)
      in if File.exists path then SOME path else NONE end;
  in
    (case get_first tool (Path.split (getenv "ISABELLE_TOOLS")) of
      NONE => false
    | SOME path => (Position.report pos (Markup.path (Path.implode path)); true))
  end;

val arg = enclose "{" "}" o clean_string;

fun entity check markup kind index =
  Thy_Output.antiquotation
    (Binding.name (translate (fn " " => "_" | c => c) kind ^
      (case index of NONE => "" | SOME true => "_def" | SOME false => "_ref")))
    (Scan.lift (Scan.optional (Args.parens Args.name) "" -- Parse.position Args.name))
    (fn {context = ctxt, ...} => fn (logic, (name, pos)) =>
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
        if check ctxt (name, pos) then
          idx ^
          (Output.output name
            |> (if markup = "" then I else enclose ("\\" ^ markup ^ "{") "}")
            |> (if Config.get ctxt Thy_Output.quotes then quote else I)
            |> (if Config.get ctxt Thy_Output.display
                then enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
                else hyper o enclose "\\mbox{\\isa{" "}}"))
        else error ("Bad " ^ kind ^ " " ^ quote name ^ Position.here pos)
      end);

fun entity_antiqs check markup kind =
  entity check markup kind NONE #>
  entity check markup kind (SOME true) #>
  entity check markup kind (SOME false);

in

val entity_setup =
  entity_antiqs no_check "" "syntax" #>
  entity_antiqs (K command_check) "isacommand" "command" #>
  entity_antiqs (K (Keyword.is_keyword o #1)) "isakeyword" "keyword" #>
  entity_antiqs (K (Keyword.is_keyword o #1)) "isakeyword" "element" #>
  entity_antiqs (can o Method.check_name) "" "method" #>
  entity_antiqs (can o Attrib.check o Proof_Context.theory_of) "" "attribute" #>
  entity_antiqs no_check "" "fact" #>
  entity_antiqs no_check "" "variable" #>
  entity_antiqs no_check "" "case" #>
  entity_antiqs (can o Thy_Output.check_command) "" "antiquotation" #>
  entity_antiqs (can o Thy_Output.check_option) "" "antiquotation option" #>
  entity_antiqs no_check "isatt" "setting" #>
  entity_antiqs no_check "isatt" "system option" #>
  entity_antiqs no_check "" "inference" #>
  entity_antiqs no_check "isatt" "executable" #>
  entity_antiqs (K check_tool) "isatool" "tool" #>
  entity_antiqs (can o ML_Context.check_antiq) "" Markup.ML_antiquotationN;

end;


(* theory setup *)

val setup =
  verbatim_setup #>
  index_ml_setup #>
  named_thms_setup #>
  thy_file_setup #>
  entity_setup;

end;
