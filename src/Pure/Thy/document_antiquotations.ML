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
  Thy_Output.pretty_term ctxt (style t);

fun pretty_thms_style ctxt (style: style, ths) =
  map (fn th => Thy_Output.pretty_term ctxt (style (Thm.full_prop_of th))) ths;

fun pretty_term_typ ctxt (style: style, t) =
  let val t' = style t
  in Thy_Output.pretty_term ctxt (Type.constraint (Term.fastype_of t') t') end;

fun pretty_term_typeof ctxt (style: style, t) =
  Syntax.pretty_typ ctxt (Term.fastype_of (style t));

fun pretty_const ctxt c =
  let
    val t = Const (c, Consts.type_scheme (Proof_Context.consts_of ctxt) c)
      handle TYPE (msg, _, _) => error msg;
    val (t', _) = yield_singleton (Variable.import_terms true) t ctxt;
  in Thy_Output.pretty_term ctxt t' end;

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

val basic_entity = Thy_Output.antiquotation_pretty_source_embedded;

fun basic_entities name scan pretty =
  Document_Antiquotation.setup name scan
    (fn {context = ctxt, source = src, argument = xs} =>
      Thy_Output.pretty_items_source ctxt {embedded = false} src (map (pretty ctxt) xs));

in

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
      Thy_Output.pretty_items_source ctxt {embedded = false} src (pretty_thms_style ctxt arg)));

end;


(* Markdown errors *)

local

fun markdown_error binding =
  Document_Antiquotation.setup binding (Scan.succeed ())
    (fn {source = src, ...} =>
      error ("Bad Markdown structure: illegal " ^ quote (Binding.name_of binding) ^
        Position.here (Position.no_range_position (#1 (Token.range_of src)))))

in

val _ =
  Theory.setup
   (markdown_error \<^binding>\<open>item\<close> #>
    markdown_error \<^binding>\<open>enum\<close> #>
    markdown_error \<^binding>\<open>descr\<close>);

end;


(* control spacing *)

val _ =
  Theory.setup
   (Thy_Output.antiquotation_raw \<^binding>\<open>noindent\<close> (Scan.succeed ())
      (fn _ => fn () => Latex.string "\\noindent") #>
    Thy_Output.antiquotation_raw \<^binding>\<open>smallskip\<close> (Scan.succeed ())
      (fn _ => fn () => Latex.string "\\smallskip") #>
    Thy_Output.antiquotation_raw \<^binding>\<open>medskip\<close> (Scan.succeed ())
      (fn _ => fn () => Latex.string "\\medskip") #>
    Thy_Output.antiquotation_raw \<^binding>\<open>bigskip\<close> (Scan.succeed ())
      (fn _ => fn () => Latex.string "\\bigskip"));


(* control style *)

local

fun control_antiquotation name s1 s2 =
  Thy_Output.antiquotation_raw_embedded name (Scan.lift Args.cartouche_input)
    (fn ctxt => Latex.enclose_block s1 s2 o Thy_Output.output_document ctxt {markdown = false});

in

val _ =
  Theory.setup
   (control_antiquotation \<^binding>\<open>footnote\<close> "\\footnote{" "}" #>
    control_antiquotation \<^binding>\<open>emph\<close> "\\emph{" "}" #>
    control_antiquotation \<^binding>\<open>bold\<close> "\\textbf{" "}");

end;


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
  Thy_Output.antiquotation_raw_embedded name (Scan.lift Args.text_input)
    (fn ctxt => fn text =>
      let
        val _ = report_text ctxt text;
      in
        prepare_text ctxt text
        |> Thy_Output.output_source ctxt
        |> Thy_Output.isabelle ctxt
      end);

val theory_text_antiquotation =
  Thy_Output.antiquotation_raw_embedded \<^binding>\<open>theory_text\<close> (Scan.lift Args.text_input)
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
        |> maps (Thy_Output.output_token ctxt)
        |> Thy_Output.isabelle ctxt
      end);

in

val _ =
  Theory.setup
   (text_antiquotation \<^binding>\<open>text\<close> #>
    text_antiquotation \<^binding>\<open>cartouche\<close> #>
    theory_text_antiquotation);

end;




(* goal state *)

local

fun goal_state name main =
  Thy_Output.antiquotation_pretty name (Scan.succeed ())
    (fn ctxt => fn () =>
      Goal_Display.pretty_goal
        (Config.put Goal_Display.show_main_goal main ctxt)
        (#goal (Proof.goal (Toplevel.proof_of (Toplevel.presentation_state ctxt)))));

in

val _ = Theory.setup
 (goal_state \<^binding>\<open>goals\<close> true #>
  goal_state \<^binding>\<open>subgoals\<close> false);

end;


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
        Thy_Output.pretty_source ctxt {embedded = false}
          [hd src, prop_tok] (Thy_Output.pretty_term ctxt prop)
      end));


(* verbatim text *)

val _ = Theory.setup
  (Thy_Output.antiquotation_verbatim_embedded \<^binding>\<open>verbatim\<close> (Scan.lift Args.text_input)
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
  (Thy_Output.antiquotation_verbatim_embedded \<^binding>\<open>bash_function\<close>
    (Scan.lift Args.embedded_position) Isabelle_System.check_bash_function);


(* system options *)

val _ = Theory.setup
  (Thy_Output.antiquotation_verbatim_embedded \<^binding>\<open>system_option\<close>
    (Scan.lift Args.embedded_position)
    (fn ctxt => fn (name, pos) =>
      let val _ = Completion.check_option (Options.default ()) ctxt (name, pos);
      in name end));


(* ML text *)

local

fun ml_text name ml =
  Thy_Output.antiquotation_verbatim_embedded name (Scan.lift Args.text_input)
    (fn ctxt => fn text =>
      let val _ = ML_Context.eval_in (SOME ctxt) ML_Compiler.flags (Input.pos_of text) (ml text)
      in #1 (Input.source_content text) end);

fun ml_enclose bg en source =
  ML_Lex.read bg @ ML_Lex.read_source source @ ML_Lex.read en;

in

val _ = Theory.setup
 (ml_text \<^binding>\<open>ML\<close> (ml_enclose "fn _ => (" ");") #>
  ml_text \<^binding>\<open>ML_op\<close> (ml_enclose "fn _ => (op " ");") #>
  ml_text \<^binding>\<open>ML_type\<close> (ml_enclose "val _ = NONE : (" ") option;") #>
  ml_text \<^binding>\<open>ML_structure\<close>
    (ml_enclose "functor XXX() = struct structure XX = " " end;") #>

  ml_text \<^binding>\<open>ML_functor\<close>   (* FIXME formal treatment of functor name (!?) *)
    (fn source =>
      ML_Lex.read ("ML_Env.check_functor " ^
        ML_Syntax.print_string (#1 (Input.source_content source)))) #>

  ml_text \<^binding>\<open>ML_text\<close> (K []));

end;


(* URLs *)

val escape_url =
  translate_string (fn c => if c = "%" orelse c = "#" orelse c = "^" then "\\" ^ c else c);

val _ = Theory.setup
  (Thy_Output.antiquotation_raw_embedded \<^binding>\<open>url\<close> (Scan.lift Args.embedded_input)
    (fn ctxt => fn source =>
      let
        val url = Input.string_of source;
        val pos = Input.pos_of source;
        val delimited = Input.is_delimited source;
        val _ =
          Context_Position.reports ctxt
            [(pos, Markup.language_path delimited), (pos, Markup.url url)];
      in Latex.enclose_block "\\url{" "}" [Latex.string (escape_url url)] end));


(* formal entities *)

local

fun entity_antiquotation name check bg en =
  Thy_Output.antiquotation_raw name (Scan.lift Args.name_position)
    (fn ctxt => fn (name, pos) =>
      let val _ = check ctxt (name, pos)
      in Latex.enclose_block bg en [Latex.string (Output.output name)] end);

in

val _ =
  Theory.setup
   (entity_antiquotation \<^binding>\<open>command\<close> Outer_Syntax.check_command "\\isacommand{" "}" #>
    entity_antiquotation \<^binding>\<open>method\<close> Method.check_name "\\isa{" "}" #>
    entity_antiquotation \<^binding>\<open>attribute\<close> Attrib.check_name "\\isa{" "}");

end;

end;
