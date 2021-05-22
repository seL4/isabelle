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

fun test_val (ml1, []) = ML_Lex.read "fn _ => (" @ ml1 @ ML_Lex.read ");"
  | test_val (ml1, ml2) = ML_Lex.read "fn _ => (" @ ml1 @ ML_Lex.read " : " @ ml2 @ ML_Lex.read ");";

fun test_op (ml1, ml2) = test_val (ML_Lex.read "op " @ ml1, ml2);

fun test_type (ml1, []) = ML_Lex.read "val _ = NONE : (" @ ml1 @ ML_Lex.read ") option;"
  | test_type (ml1, ml2) =
      ML_Lex.read "val _ = [NONE : (" @ ml1 @ ML_Lex.read ") option, NONE : (" @
      ml2 @ ML_Lex.read ") option];";

fun text_exn (ml1, []) = ML_Lex.read "fn _ => (" @ ml1 @ ML_Lex.read " : exn);"
  | text_exn (ml1, ml2) =
      ML_Lex.read "fn _ => (" @ ml1 @ ML_Lex.read " : " @ ml2 @ ML_Lex.read " -> exn);";

fun test_struct (ml, _) =
  ML_Lex.read "functor XXX() = struct structure XX = " @ ml @ ML_Lex.read " end;";

fun test_functor (Antiquote.Text tok :: _, _) =
      ML_Lex.read "ML_Env.check_functor " @
      ML_Lex.read (ML_Syntax.print_string (ML_Lex.content_of tok))
  | test_functor _ = raise Fail "Bad ML functor specification";

val is_name =
  ML_Lex.kind_of #> (fn kind => kind = ML_Lex.Ident orelse kind = ML_Lex.Long_Ident);

fun is_ml_identifier ants =
  forall Antiquote.is_text ants andalso
    (case filter is_name (map (Antiquote.the_text "") ants) of
      toks as [_] => Symbol_Pos.is_identifier (Long_Name.base_name (ML_Lex.flatten toks))
    | _ => false);

val parse_ml = Args.text_input -- Scan.optional (Args.colon |-- Args.text_input) Input.empty;
val parse_type = Args.text_input -- Scan.optional (Args.$$$ "=" |-- Args.text_input) Input.empty;
val parse_exn = Args.text_input -- Scan.optional (Args.$$$ "of" |-- Args.text_input) Input.empty;
val parse_struct = Args.text_input >> rpair Input.empty;

fun antiquotation_ml parse test kind show_kind binding index =
  Document_Output.antiquotation_raw binding (Scan.lift parse)
    (fn ctxt => fn (source1, source2) =>
      let
        val (ml1, ml2) = apply2 ML_Lex.read_source (source1, source2);
        val pos = Input.pos_of source1;
        val _ =
          ML_Context.eval_in (SOME ctxt) ML_Compiler.flags pos (test (ml1, ml2))
            handle ERROR msg => error (msg ^ Position.here pos);

        val (txt1, txt2) = apply2 (#1 o Input.source_content) (source1, source2);
        val sep = if kind = "type" then "=" else if kind = "exception" then "of" else ":";
        val txt =
          if txt2 = "" then txt1
          else if sep = ":" andalso is_ml_identifier ml1 then txt1 ^ ": " ^ txt2
          else txt1 ^ " " ^ sep ^ " " ^ txt2;

        val main_text =
          Document_Output.verbatim ctxt
            (if kind = "" orelse not show_kind then txt else kind ^ " " ^ txt);

        val index_text =
          index |> Option.map (fn def =>
            let
              val ctxt' = Config.put Document_Antiquotation.thy_output_display false ctxt;
              val kind' = if kind = "" then " (ML)" else " (ML " ^ kind ^ ")";
              val txt' = Latex.block [Document_Output.verbatim ctxt' txt1, Latex.string kind'];
              val like = Document_Antiquotation.approx_content ctxt source1;
            in Latex.index_entry {items = [{text = txt', like = like}], def = def} end);
      in Latex.block (the_list index_text @ [main_text]) end);

fun antiquotation_ml' parse test kind binding =
  antiquotation_ml parse test kind true binding (SOME true);

in

val _ =
  Theory.setup
   (antiquotation_ml' parse_ml test_val "" \<^binding>\<open>define_ML\<close> #>
    antiquotation_ml' parse_ml test_op "infix" \<^binding>\<open>define_ML_infix\<close> #>
    antiquotation_ml' parse_type test_type "type" \<^binding>\<open>define_ML_type\<close> #>
    antiquotation_ml' parse_exn text_exn "exception" \<^binding>\<open>define_ML_exception\<close> #>
    antiquotation_ml' parse_struct test_struct "structure" \<^binding>\<open>define_ML_structure\<close> #>
    antiquotation_ml' parse_struct test_functor "functor" \<^binding>\<open>define_ML_functor\<close>);

end;


(* named theorems *)

val _ =
  Theory.setup (Document_Output.antiquotation_raw \<^binding>\<open>named_thms\<close>
    (Scan.repeat (Attrib.thm -- Scan.lift (Args.parens Args.name)))
    (fn ctxt =>
      map (fn (thm, name) =>
        Output.output
          (Document_Antiquotation.format ctxt
            (Document_Antiquotation.delimit ctxt (Document_Output.pretty_thm ctxt thm))) ^
        enclose "\\rulename{" "}" (Output.output name))
      #> space_implode "\\par\\smallskip%\n"
      #> Latex.string #> single
      #> Document_Output.isabelle ctxt));


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
  Document_Output.antiquotation_raw
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
  Theory.setup (Document_Output.antiquotation_raw \<^binding>\<open>show_symbols\<close> (Scan.succeed ())
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
