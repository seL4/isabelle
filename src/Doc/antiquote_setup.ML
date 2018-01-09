(*  Title:      Doc/antiquote_setup.ML
    Author:     Makarius

Auxiliary antiquotations for the Isabelle manuals.
*)

structure Antiquote_Setup: sig end =
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


(* ML text *)

local

fun ml_val (toks1, []) = ML_Lex.read "fn _ => (" @ toks1 @ ML_Lex.read ");"
  | ml_val (toks1, toks2) =
      ML_Lex.read "fn _ => (" @ toks1 @ ML_Lex.read " : " @ toks2 @ ML_Lex.read ");";

fun ml_op (toks1, []) = ML_Lex.read "fn _ => (op " @ toks1 @ ML_Lex.read ");"
  | ml_op (toks1, toks2) =
      ML_Lex.read "fn _ => (op " @ toks1 @ ML_Lex.read " : " @ toks2 @ ML_Lex.read ");";

fun ml_type (toks1, []) = ML_Lex.read "val _ = NONE : (" @ toks1 @ ML_Lex.read ") option;"
  | ml_type (toks1, toks2) =
      ML_Lex.read "val _ = [NONE : (" @ toks1 @ ML_Lex.read ") option, NONE : (" @
        toks2 @ ML_Lex.read ") option];";

fun ml_exception (toks1, []) = ML_Lex.read "fn _ => (" @ toks1 @ ML_Lex.read " : exn);"
  | ml_exception (toks1, toks2) =
      ML_Lex.read "fn _ => (" @ toks1 @ ML_Lex.read " : " @ toks2 @ ML_Lex.read " -> exn);";

fun ml_structure (toks, _) =
  ML_Lex.read "functor XXX() = struct structure XX = " @ toks @ ML_Lex.read " end;";

fun ml_functor (Antiquote.Text tok :: _, _) =
      ML_Lex.read "ML_Env.check_functor " @
      ML_Lex.read (ML_Syntax.print_string (ML_Lex.content_of tok))
  | ml_functor _ = raise Fail "Bad ML functor specification";

val is_name =
  ML_Lex.kind_of #> (fn kind => kind = ML_Lex.Ident orelse kind = ML_Lex.Long_Ident);

fun ml_name txt =
  (case filter is_name (ML_Lex.tokenize txt) of
    toks as [_] => ML_Lex.flatten toks
  | _ => error ("Single ML name expected in input: " ^ quote txt));

fun prep_ml source =
  (Input.source_content source, ML_Lex.read_source false source);

fun index_ml name kind ml = Document_Antiquotation.setup name
  (Scan.lift (Args.text_input -- Scan.option (Args.colon |-- Args.text_input)))
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

      val pos = Input.pos_of source1;
      val _ =
        ML_Context.eval_in (SOME ctxt) ML_Compiler.flags pos (ml (toks1, toks2))
          handle ERROR msg => error (msg ^ Position.here pos);
      val kind' = if kind = "" then "ML" else "ML " ^ kind;
    in
      "\\indexdef{}{" ^ kind' ^ "}{" ^ clean_string (ml_name txt1) ^ "}" ^
      (Thy_Output.verbatim_text ctxt txt')
    end);

in

val _ =
  Theory.setup
   (index_ml @{binding index_ML} "" ml_val #>
    index_ml @{binding index_ML_op} "infix" ml_op #>
    index_ml @{binding index_ML_type} "type" ml_type #>
    index_ml @{binding index_ML_exception} "exception" ml_exception #>
    index_ml @{binding index_ML_structure} "structure" ml_structure #>
    index_ml @{binding index_ML_functor} "functor" ml_functor);

end;


(* named theorems *)

val _ =
  Theory.setup (Document_Antiquotation.setup @{binding named_thms}
    (Scan.repeat (Attrib.thm -- Scan.lift (Args.parens Args.name)))
    (fn {context = ctxt, ...} =>
      map (apfst (Thy_Output.pretty_thm ctxt))
      #> (if Config.get ctxt Document_Antiquotation.thy_output_quotes
          then map (apfst Pretty.quote) else I)
      #> (if Config.get ctxt Document_Antiquotation.thy_output_display
          then
            map (fn (p, name) =>
              Output.output
                (Thy_Output.string_of_margin ctxt
                  (Pretty.indent (Config.get ctxt Document_Antiquotation.thy_output_indent) p)) ^
              "\\rulename{" ^
              Output.output (Pretty.unformatted_string_of (Thy_Output.pretty_text ctxt name)) ^ "}")
            #> space_implode "\\par\\smallskip%\n"
            #> Latex.environment "isabelle"
          else
            map (fn (p, name) =>
              Output.output (Pretty.unformatted_string_of p) ^
              "\\rulename{" ^
              Output.output (Pretty.unformatted_string_of (Thy_Output.pretty_text ctxt name)) ^ "}")
            #> space_implode "\\par\\smallskip%\n"
            #> enclose "\\isa{" "}")));


(* Isabelle/Isar entities (with index) *)

local

fun no_check (_: Proof.context) (name, _: Position.T) = name;

fun check_keyword ctxt (name, pos) =
  if Keyword.is_keyword (Thy_Header.get_keywords' ctxt) name then name
  else error ("Bad outer syntax keyword " ^ quote name ^ Position.here pos);

fun check_system_option ctxt (name, pos) =
  (Context_Position.report ctxt pos (Options.default_markup (name, pos)); true)
    handle ERROR _ => false;

val arg = enclose "{" "}" o clean_string;

fun entity check markup binding index =
  Document_Antiquotation.setup
    (binding |> Binding.map_name (fn name => name ^
      (case index of NONE => "" | SOME true => "_def" | SOME false => "_ref")))
    (Scan.lift (Scan.optional (Args.parens Args.name) "" -- Parse.position Args.name))
    (fn {context = ctxt, ...} => fn (logic, (name, pos)) =>
      let
        val kind = translate (fn "_" => " " | c => c) (Binding.name_of binding);
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
        val _ =
          if Context_Position.is_reported ctxt pos then ignore (check ctxt (name, pos)) else ();
      in
        idx ^
        (Output.output name
          |> (if markup = "" then I else enclose ("\\" ^ markup ^ "{") "}")
          |> hyper o enclose "\\mbox{\\isa{" "}}")
      end);

fun entity_antiqs check markup kind =
  entity check markup kind NONE #>
  entity check markup kind (SOME true) #>
  entity check markup kind (SOME false);

in

val _ =
  Theory.setup
   (entity_antiqs no_check "" @{binding syntax} #>
    entity_antiqs Outer_Syntax.check_command "isacommand" @{binding command} #>
    entity_antiqs check_keyword "isakeyword" @{binding keyword} #>
    entity_antiqs check_keyword "isakeyword" @{binding element} #>
    entity_antiqs Method.check_name "" @{binding method} #>
    entity_antiqs Attrib.check_name "" @{binding attribute} #>
    entity_antiqs no_check "" @{binding fact} #>
    entity_antiqs no_check "" @{binding variable} #>
    entity_antiqs no_check "" @{binding case} #>
    entity_antiqs Document_Antiquotation.check "" @{binding antiquotation} #>
    entity_antiqs Document_Antiquotation.check_option "" @{binding antiquotation_option} #>
    entity_antiqs no_check "isasystem" @{binding setting} #>
    entity_antiqs check_system_option "isasystem" @{binding system_option} #>
    entity_antiqs no_check "" @{binding inference} #>
    entity_antiqs no_check "isasystem" @{binding executable} #>
    entity_antiqs no_check "isatool" @{binding tool} #>
    entity_antiqs ML_Context.check_antiquotation "" @{binding ML_antiquotation} #>
    entity_antiqs (K JEdit.check_action) "isasystem" @{binding action});

end;

end;
