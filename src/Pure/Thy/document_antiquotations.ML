(*  Title:      Pure/Thy/document_antiquotations.ML
    Author:     Makarius

Miscellaneous document antiquotations.
*)

structure Document_Antiquotations: sig end =
struct

(* basic entities *)

local

type style = term -> term;

fun pretty_term_style ctxt (style: style, t) =
  Document_Output.pretty_term ctxt (style t);

fun pretty_thms_style ctxt (style: style, ths) =
  map (fn th => Document_Output.pretty_term ctxt (style (Thm.full_prop_of th))) ths;

fun pretty_term_typ ctxt (style: style, t) =
  let val t' = style t
  in Document_Output.pretty_term ctxt (Type.constraint (Term.fastype_of t') t') end;

fun pretty_term_typeof ctxt (style: style, t) =
  Syntax.pretty_typ ctxt (Term.fastype_of (style t));

fun pretty_const ctxt c =
  let
    val t = Const (c, Consts.type_scheme (Proof_Context.consts_of ctxt) c)
      handle TYPE (msg, _, _) => error msg;
    val (t', _) = yield_singleton (Variable.import_terms true) t ctxt;
  in Document_Output.pretty_term ctxt t' end;

fun pretty_abbrev ctxt s =
  let
    val t = Syntax.read_term (Proof_Context.set_mode Proof_Context.mode_abbrev ctxt) s;
    fun err () = error ("Abbreviated constant expected: " ^ Syntax.string_of_term ctxt t);
    val (head, args) = Term.strip_comb t;
    val (c, T) = Term.dest_Const head handle TERM _ => err ();
    val (U, u) = Consts.the_abbreviation (Proof_Context.consts_of ctxt) c
      handle TYPE _ => err ();
    val t' = Term.betapplys (Envir.expand_atom T (U, u), args);
    val eq = Logic.mk_equals (t, t');
    val ctxt' = Proof_Context.augment eq ctxt;
  in Proof_Context.pretty_term_abbrev ctxt' eq end;

fun pretty_locale ctxt (name, pos) =
  let val thy = Proof_Context.theory_of ctxt
  in Pretty.str (Locale.extern thy (Locale.check thy (name, pos))) end;

fun pretty_class ctxt s =
  Pretty.str (Proof_Context.extern_class ctxt (Proof_Context.read_class ctxt s));

fun pretty_type ctxt s =
  let val Type (name, _) = Proof_Context.read_type_name {proper = true, strict = false} ctxt s
  in Pretty.str (Proof_Context.extern_type ctxt name) end;

fun pretty_prf full ctxt = Proof_Syntax.pretty_standard_proof_of ctxt full;

fun pretty_theory ctxt (name, pos) =
  (Theory.check {long = true} ctxt (name, pos); Pretty.str name);

val basic_entity = Document_Output.antiquotation_pretty_source_embedded;

fun basic_entities name scan pretty =
  Document_Antiquotation.setup name scan
    (fn {context = ctxt, source = src, argument = xs} =>
      Document_Output.pretty_items_source ctxt {embedded = false} src (map (pretty ctxt) xs));

val _ = Theory.setup
 (basic_entity \<^binding>\<open>prop\<close> (Term_Style.parse -- Args.prop) pretty_term_style #>
  basic_entity \<^binding>\<open>term\<close> (Term_Style.parse -- Args.term) pretty_term_style #>
  basic_entity \<^binding>\<open>term_type\<close> (Term_Style.parse -- Args.term) pretty_term_typ #>
  basic_entity \<^binding>\<open>typeof\<close> (Term_Style.parse -- Args.term) pretty_term_typeof #>
  basic_entity \<^binding>\<open>const\<close> (Args.const {proper = true, strict = false}) pretty_const #>
  basic_entity \<^binding>\<open>abbrev\<close> (Scan.lift Args.embedded_inner_syntax) pretty_abbrev #>
  basic_entity \<^binding>\<open>typ\<close> Args.typ_abbrev Syntax.pretty_typ #>
  basic_entity \<^binding>\<open>locale\<close> (Scan.lift Args.embedded_position) pretty_locale #>
  basic_entity \<^binding>\<open>class\<close> (Scan.lift Args.embedded_inner_syntax) pretty_class #>
  basic_entity \<^binding>\<open>type\<close> (Scan.lift Args.embedded_inner_syntax) pretty_type #>
  basic_entity \<^binding>\<open>theory\<close> (Scan.lift Args.embedded_position) pretty_theory #>
  basic_entities \<^binding>\<open>prf\<close> Attrib.thms (pretty_prf false) #>
  basic_entities \<^binding>\<open>full_prf\<close> Attrib.thms (pretty_prf true) #>
  Document_Antiquotation.setup \<^binding>\<open>thm\<close> (Term_Style.parse -- Attrib.thms)
    (fn {context = ctxt, source = src, argument = arg} =>
      Document_Output.pretty_items_source ctxt {embedded = false} src (pretty_thms_style ctxt arg)));

in end;


(* Markdown errors *)

local

fun markdown_error binding =
  Document_Antiquotation.setup binding (Scan.succeed ())
    (fn {source = src, ...} =>
      error ("Bad Markdown structure: illegal " ^ quote (Binding.name_of binding) ^
        Position.here (Position.no_range_position (#1 (Token.range_of src)))))

val _ =
  Theory.setup
   (markdown_error \<^binding>\<open>item\<close> #>
    markdown_error \<^binding>\<open>enum\<close> #>
    markdown_error \<^binding>\<open>descr\<close>);

in end;


(* control spacing *)

val _ =
  Theory.setup
   (Document_Output.antiquotation_raw \<^binding>\<open>noindent\<close> (Scan.succeed ())
      (fn _ => fn () => Latex.string "\\noindent") #>
    Document_Output.antiquotation_raw \<^binding>\<open>smallskip\<close> (Scan.succeed ())
      (fn _ => fn () => Latex.string "\\smallskip") #>
    Document_Output.antiquotation_raw \<^binding>\<open>medskip\<close> (Scan.succeed ())
      (fn _ => fn () => Latex.string "\\medskip") #>
    Document_Output.antiquotation_raw \<^binding>\<open>bigskip\<close> (Scan.succeed ())
      (fn _ => fn () => Latex.string "\\bigskip"));


(* nested document text *)

local

fun nested_antiquotation name s1 s2 =
  Document_Output.antiquotation_raw_embedded name (Scan.lift Args.cartouche_input)
    (fn ctxt => fn txt =>
      (Context_Position.reports ctxt (Document_Output.document_reports txt);
        Latex.enclose_block s1 s2 (Document_Output.output_document ctxt {markdown = false} txt)));

val _ =
  Theory.setup
   (nested_antiquotation \<^binding>\<open>footnote\<close> "\\footnote{" "}" #>
    nested_antiquotation \<^binding>\<open>emph\<close> "\\emph{" "}" #>
    nested_antiquotation \<^binding>\<open>bold\<close> "\\textbf{" "}");

in end;


(* index entries *)

local

val index_like = Parse.$$$ "(" |-- Parse.!!! (Parse.$$$ "is" |-- Args.name --| Parse.$$$ ")");
val index_args = Parse.enum1 "!" (Args.embedded_input -- Scan.option index_like);

fun output_text ctxt = Latex.block o Document_Output.output_document ctxt {markdown = false};

fun index binding def =
  Document_Output.antiquotation_raw binding (Scan.lift index_args)
    (fn ctxt => fn args =>
      let
        val _ = Context_Position.reports ctxt (maps (Document_Output.document_reports o #1) args);
        fun make_item (txt, opt_like) =
          let
            val text = output_text ctxt txt;
            val like =
              (case opt_like of
                SOME s => s
              | NONE => Document_Antiquotation.approx_content ctxt (Input.string_of txt));
            val _ =
              if is_none opt_like andalso Context_Position.is_visible ctxt then
                writeln ("(" ^ Markup.markup Markup.keyword2 "is" ^ " " ^ quote like ^ ")" ^
                  Position.here (Input.pos_of txt))
              else ();
          in {text = text, like = like} end;
      in Latex.index_entry {items = map make_item args, def = def} end);

val _ = Theory.setup (index \<^binding>\<open>index_ref\<close> false #> index \<^binding>\<open>index_def\<close> true);

in end;


(* quasi-formal text (unchecked) *)

local

fun report_text ctxt text =
  let val pos = Input.pos_of text in
    Context_Position.reports ctxt
      [(pos, Markup.language_text (Input.is_delimited text)),
       (pos, Markup.raw_text)]
  end;

fun prepare_text ctxt =
  Input.source_content #> #1 #> Document_Antiquotation.prepare_lines ctxt;

fun text_antiquotation name =
  Document_Output.antiquotation_raw_embedded name (Scan.lift Args.text_input)
    (fn ctxt => fn text =>
      let
        val _ = report_text ctxt text;
      in
        prepare_text ctxt text
        |> Document_Output.output_source ctxt
        |> Document_Output.isabelle ctxt
      end);

val theory_text_antiquotation =
  Document_Output.antiquotation_raw_embedded \<^binding>\<open>theory_text\<close> (Scan.lift Args.text_input)
    (fn ctxt => fn text =>
      let
        val keywords = Thy_Header.get_keywords' ctxt;

        val _ = report_text ctxt text;
        val _ =
          Input.source_explode text
          |> Token.tokenize keywords {strict = true}
          |> maps (Token.reports keywords)
          |> Context_Position.reports_text ctxt;
      in
        prepare_text ctxt text
        |> Token.explode0 keywords
        |> maps (Document_Output.output_token ctxt)
        |> Document_Output.isabelle ctxt
      end);

val _ =
  Theory.setup
   (text_antiquotation \<^binding>\<open>text\<close> #>
    text_antiquotation \<^binding>\<open>cartouche\<close> #>
    theory_text_antiquotation);

in end;


(* goal state *)

local

fun goal_state name main =
  Document_Output.antiquotation_pretty name (Scan.succeed ())
    (fn ctxt => fn () =>
      Goal_Display.pretty_goal
        (Config.put Goal_Display.show_main_goal main ctxt)
        (#goal (Proof.goal (Toplevel.proof_of (Toplevel.presentation_state ctxt)))));

val _ = Theory.setup
 (goal_state \<^binding>\<open>goals\<close> true #>
  goal_state \<^binding>\<open>subgoals\<close> false);

in end;


(* embedded lemma *)

val _ = Theory.setup
  (Document_Antiquotation.setup \<^binding>\<open>lemma\<close>
    (Scan.lift (Scan.ahead Parse.not_eof) -- Args.prop --
      Scan.lift (Parse.position (Parse.reserved "by") -- Method.parse -- Scan.option Method.parse))
    (fn {context = ctxt, source = src, argument = ((prop_tok, prop), (((_, by_pos), m1), m2))} =>
      let
        val reports =
          (by_pos, Markup.keyword1 |> Markup.keyword_properties) ::
            maps Method.reports_of (m1 :: the_list m2);
        val _ = Context_Position.reports ctxt reports;

        (* FIXME check proof!? *)
        val _ = ctxt
          |> Proof.theorem NONE (K I) [[(prop, [])]]
          |> Proof.global_terminal_proof (m1, m2);
      in
        Document_Output.pretty_source ctxt {embedded = false}
          [hd src, prop_tok] (Document_Output.pretty_term ctxt prop)
      end));


(* verbatim text *)

val _ = Theory.setup
  (Document_Output.antiquotation_verbatim_embedded \<^binding>\<open>verbatim\<close> (Scan.lift Args.text_input)
    (fn ctxt => fn text =>
      let
        val pos = Input.pos_of text;
        val _ =
          Context_Position.reports ctxt
            [(pos, Markup.language_verbatim (Input.is_delimited text)),
             (pos, Markup.raw_text)];
      in #1 (Input.source_content text) end));


(* bash functions *)

val _ = Theory.setup
  (Document_Output.antiquotation_verbatim_embedded \<^binding>\<open>bash_function\<close>
    (Scan.lift Args.embedded_position) Isabelle_System.check_bash_function);


(* system options *)

val _ = Theory.setup
  (Document_Output.antiquotation_verbatim_embedded \<^binding>\<open>system_option\<close>
    (Scan.lift Args.embedded_position)
    (fn ctxt => fn (name, pos) =>
      let val _ = Completion.check_option (Options.default ()) ctxt (name, pos);
      in name end));


(* ML text *)

local

fun test_val (ml1, []) = ML_Lex.read "fn _ => (" @ ml1 @ ML_Lex.read ");"
  | test_val (ml1, ml2) = ML_Lex.read "fn _ => (" @ ml1 @ ML_Lex.read " : " @ ml2 @ ML_Lex.read ");";

fun test_op (ml1, ml2) = test_val (ML_Lex.read "op " @ ml1, ml2);

fun test_type (ml1, []) = ML_Lex.read "val _ = NONE : (" @ ml1 @ ML_Lex.read ") option;"
  | test_type (ml1, ml2) =
      ML_Lex.read "val _ = [NONE : (" @ ml1 @ ML_Lex.read ") option, NONE : (" @
      ml2 @ ML_Lex.read ") option];";

fun test_exn (ml1, []) = ML_Lex.read "fn _ => (" @ ml1 @ ML_Lex.read " : exn);"
  | test_exn (ml1, ml2) =
      ML_Lex.read "fn _ => (" @ ml1 @ ML_Lex.read " : " @ ml2 @ ML_Lex.read " -> exn);";

fun test_struct (ml, _) =
  ML_Lex.read "functor XXX() = struct structure XX = " @ ml @ ML_Lex.read " end;";

fun test_functor (Antiquote.Text tok :: _, _) =
      ML_Lex.read "ML_Env.check_functor " @
      ML_Lex.read (ML_Syntax.print_string (ML_Lex.content_of tok))
  | test_functor _ = raise Fail "Bad ML functor specification";

val parse_ml0 = Args.text_input >> (fn source => ("", (source, Input.empty)));

val parse_ml =
  Args.text_input -- Scan.optional (Args.colon |-- Args.text_input) Input.empty >> pair "";

val parse_exn =
  Args.text_input -- Scan.optional (Args.$$$ "of" |-- Args.text_input) Input.empty >> pair "";

val parse_type =
  (Parse.type_args >> (fn [] => "" | [a] => a ^ " " | bs => enclose "(" ") " (commas bs))) --
    (Args.text_input -- Scan.optional (Args.$$$ "=" |-- Args.text_input) Input.empty);

fun eval ctxt pos ml =
  ML_Context.eval_in (SOME ctxt) ML_Compiler.flags pos ml
    handle ERROR msg => error (msg ^ Position.here pos);

fun make_text sep sources =
  let
    val (txt1, txt2) = apply2 (#1 o Input.source_content) sources;
    val is_ident =
      (case try List.last (Symbol.explode txt1) of
        NONE => false
      | SOME s => Symbol.is_ascii_letdig s);
    val txt =
      if txt2 = "" then txt1
      else if sep = ":" andalso is_ident then txt1 ^ ": " ^ txt2
      else txt1 ^ " " ^ sep ^ " " ^ txt2
  in (txt, txt1) end;

fun antiquotation_ml parse test kind show_kind binding index =
  Document_Output.antiquotation_raw binding (Scan.lift parse)
    (fn ctxt => fn (txt0, sources) =>
      let
        val (ml1, ml2) = apply2 ML_Lex.read_source sources;
        val ml0 = ML_Lex.read_source (Input.string txt0);
        val _ = test (ml0 @ ml1, ml2) |> eval ctxt (Input.pos_of (#1 sources));

        val sep = if kind = "type" then "=" else if kind = "exception" then "of" else ":";
        val (txt, idx) = make_text sep sources;

        val main_text =
          Document_Output.verbatim ctxt
            ((if kind = "" orelse not show_kind then "" else kind ^ " ") ^ txt0 ^ txt);

        val index_text =
          index |> Option.map (fn def =>
            let
              val ctxt' = Config.put Document_Antiquotation.thy_output_display false ctxt;
              val kind' = if kind = "" then " (ML)" else " (ML " ^ kind ^ ")";
              val txt' = Latex.block [Document_Output.verbatim ctxt' idx, Latex.string kind'];
              val like = Document_Antiquotation.approx_content ctxt' idx;
            in Latex.index_entry {items = [{text = txt', like = like}], def = def} end);
      in Latex.block (the_list index_text @ [main_text]) end);

fun antiquotation_ml0 test kind =
  antiquotation_ml parse_ml0 test kind false;

fun antiquotation_ml1 parse test kind binding =
  antiquotation_ml parse test kind true binding (SOME true);

in

val _ =
  Theory.setup
   (Latex.index_variants (antiquotation_ml0 test_val "") \<^binding>\<open>ML\<close> #>
    Latex.index_variants (antiquotation_ml0 test_op "infix") \<^binding>\<open>ML_infix\<close> #>
    Latex.index_variants (antiquotation_ml0 test_type "type") \<^binding>\<open>ML_type\<close> #>
    Latex.index_variants (antiquotation_ml0 test_struct "structure") \<^binding>\<open>ML_structure\<close> #>
    Latex.index_variants (antiquotation_ml0 test_functor "functor") \<^binding>\<open>ML_functor\<close> #>
    antiquotation_ml0 (K []) "text" \<^binding>\<open>ML_text\<close> NONE #>
    antiquotation_ml1 parse_ml test_val "" \<^binding>\<open>define_ML\<close> #>
    antiquotation_ml1 parse_ml test_op "infix" \<^binding>\<open>define_ML_infix\<close> #>
    antiquotation_ml1 parse_type test_type "type" \<^binding>\<open>define_ML_type\<close> #>
    antiquotation_ml1 parse_exn test_exn "exception" \<^binding>\<open>define_ML_exception\<close> #>
    antiquotation_ml1 parse_ml0 test_struct "structure" \<^binding>\<open>define_ML_structure\<close> #>
    antiquotation_ml1 parse_ml0 test_functor "functor" \<^binding>\<open>define_ML_functor\<close>);

end;


(* URLs *)

val escape_url =
  translate_string (fn c => if c = "%" orelse c = "#" orelse c = "^" then "\\" ^ c else c);

val _ = Theory.setup
  (Document_Output.antiquotation_raw_embedded \<^binding>\<open>url\<close> (Scan.lift Args.embedded_input)
    (fn ctxt => fn source =>
      let
        val url = Input.string_of source;
        val pos = Input.pos_of source;
        val delimited = Input.is_delimited source;
        val _ =
          Context_Position.reports ctxt
            [(pos, Markup.language_url delimited), (pos, Markup.url url)];
      in Latex.enclose_block "\\url{" "}" [Latex.string (escape_url url)] end));


(* formal entities *)

local

fun entity_antiquotation name check bg en =
  Document_Output.antiquotation_raw name (Scan.lift Args.name_position)
    (fn ctxt => fn (name, pos) =>
      let val _ = check ctxt (name, pos)
      in Latex.enclose_block bg en [Latex.string (Output.output name)] end);

val _ =
  Theory.setup
   (entity_antiquotation \<^binding>\<open>command\<close> Outer_Syntax.check_command "\\isacommand{" "}" #>
    entity_antiquotation \<^binding>\<open>method\<close> Method.check_name "\\isa{" "}" #>
    entity_antiquotation \<^binding>\<open>attribute\<close> Attrib.check_name "\\isa{" "}");

in end;

end;
