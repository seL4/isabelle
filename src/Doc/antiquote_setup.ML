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
  (#1 (Input.source_content source), ML_Lex.read_source source);

fun index_ml name kind ml = Thy_Output.antiquotation_raw name
  (Scan.lift (Args.text_input -- Scan.option (Args.colon |-- Args.text_input)))
  (fn ctxt => fn (source1, opt_source2) =>
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
      Latex.block
       [Latex.string ("\\indexdef{}{" ^ kind' ^ "}{" ^ clean_string (ml_name txt1) ^ "}"),
        Thy_Output.verbatim ctxt txt']
    end);

in

val _ =
  Theory.setup
   (index_ml \<^binding>\<open>index_ML\<close> "" ml_val #>
    index_ml \<^binding>\<open>index_ML_op\<close> "infix" ml_op #>
    index_ml \<^binding>\<open>index_ML_type\<close> "type" ml_type #>
    index_ml \<^binding>\<open>index_ML_exception\<close> "exception" ml_exception #>
    index_ml \<^binding>\<open>index_ML_structure\<close> "structure" ml_structure #>
    index_ml \<^binding>\<open>index_ML_functor\<close> "functor" ml_functor);

end;


(* named theorems *)

val _ =
  Theory.setup (Thy_Output.antiquotation_raw \<^binding>\<open>named_thms\<close>
    (Scan.repeat (Attrib.thm -- Scan.lift (Args.parens Args.name)))
    (fn ctxt =>
      map (fn (thm, name) =>
        Output.output
          (Document_Antiquotation.format ctxt
            (Document_Antiquotation.delimit ctxt (Thy_Output.pretty_thm ctxt thm))) ^
        enclose "\\rulename{" "}" (Output.output name))
      #> space_implode "\\par\\smallskip%\n"
      #> Latex.string #> single
      #> Thy_Output.isabelle ctxt));


(* Isabelle/Isar entities (with index) *)

local

fun no_check (_: Proof.context) (name, _: Position.T) = name;

fun check_keyword ctxt (name, pos) =
  if Keyword.is_keyword (Thy_Header.get_keywords' ctxt) name then name
  else error ("Bad outer syntax keyword " ^ quote name ^ Position.here pos);

fun check_system_option ctxt arg =
  (Completion.check_option (Options.default ()) ctxt arg; true)
    handle ERROR _ => false;

val arg = enclose "{" "}" o clean_string;

fun entity check markup binding index =
  Thy_Output.antiquotation_raw
    (binding |> Binding.map_name (fn name => name ^
      (case index of NONE => "" | SOME true => "_def" | SOME false => "_ref")))
    (Scan.lift (Scan.optional (Args.parens Args.name) "" -- Args.name_position))
    (fn ctxt => fn (logic, (name, pos)) =>
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
        val latex =
          idx ^
          (Output.output name
            |> (if markup = "" then I else enclose ("\\" ^ markup ^ "{") "}")
            |> hyper o enclose "\\mbox{\\isa{" "}}");
      in Latex.string latex end);

fun entity_antiqs check markup kind =
  entity check markup kind NONE #>
  entity check markup kind (SOME true) #>
  entity check markup kind (SOME false);

in

val _ =
  Theory.setup
   (entity_antiqs no_check "" \<^binding>\<open>syntax\<close> #>
    entity_antiqs Outer_Syntax.check_command "isacommand" \<^binding>\<open>command\<close> #>
    entity_antiqs check_keyword "isakeyword" \<^binding>\<open>keyword\<close> #>
    entity_antiqs check_keyword "isakeyword" \<^binding>\<open>element\<close> #>
    entity_antiqs Method.check_name "" \<^binding>\<open>method\<close> #>
    entity_antiqs Attrib.check_name "" \<^binding>\<open>attribute\<close> #>
    entity_antiqs no_check "" \<^binding>\<open>fact\<close> #>
    entity_antiqs no_check "" \<^binding>\<open>variable\<close> #>
    entity_antiqs no_check "" \<^binding>\<open>case\<close> #>
    entity_antiqs Document_Antiquotation.check "" \<^binding>\<open>antiquotation\<close> #>
    entity_antiqs Document_Antiquotation.check_option "" \<^binding>\<open>antiquotation_option\<close> #>
    entity_antiqs Document_Marker.check "" \<^binding>\<open>document_marker\<close> #>
    entity_antiqs no_check "isasystem" \<^binding>\<open>setting\<close> #>
    entity_antiqs check_system_option "isasystem" \<^binding>\<open>system_option\<close> #>
    entity_antiqs no_check "" \<^binding>\<open>inference\<close> #>
    entity_antiqs no_check "isasystem" \<^binding>\<open>executable\<close> #>
    entity_antiqs Isabelle_Tool.check "isatool" \<^binding>\<open>tool\<close> #>
    entity_antiqs ML_Context.check_antiquotation "" \<^binding>\<open>ML_antiquotation\<close> #>
    entity_antiqs (K JEdit.check_action) "isasystem" \<^binding>\<open>action\<close>);

end;


(* show symbols *)

val _ =
  Theory.setup (Thy_Output.antiquotation_raw \<^binding>\<open>show_symbols\<close> (Scan.succeed ())
    (fn _ => fn _ =>
      let
        val symbol_name =
          unprefix "\\newcommand{\\isasym"
          #> raw_explode
          #> take_prefix Symbol.is_ascii_letter
          #> implode;

        val symbols =
          File.read \<^file>\<open>~~/lib/texinputs/isabellesym.sty\<close>
          |> split_lines
          |> map_filter (fn line =>
            (case try symbol_name line of
              NONE => NONE
            | SOME "" => NONE
            | SOME name => SOME ("\\verb,\\" ^ "<" ^ name ^ ">, & {\\isasym" ^ name ^ "}")));

        val eol = "\\\\\n";
        fun table (a :: b :: rest) = a ^ " & " ^ b ^ eol :: table rest
          | table [a] = [a ^ eol]
          | table [] = [];
      in
        Latex.string
          ("\\begin{supertabular}{ll@{\\qquad}ll}\n" ^ implode (table symbols) ^
           "\\end{supertabular}\n")
      end))

end;
