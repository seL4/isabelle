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

fun index_ml name kind ml = Thy_Output.antiquotation name
  (Scan.lift (Args.text_source_position -- Scan.option (Args.colon |-- Args.text_source_position)))
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
  Theory.setup (Thy_Output.antiquotation @{binding named_thms}
    (Scan.repeat (Attrib.thm -- Scan.lift (Args.parens Args.name)))
    (fn {context = ctxt, ...} =>
      map (apfst (Thy_Output.pretty_thm ctxt))
      #> (if Config.get ctxt Thy_Output.quotes then map (apfst Pretty.quote) else I)
      #> (if Config.get ctxt Thy_Output.display
          then
            map (fn (p, name) =>
              Output.output
                (Thy_Output.string_of_margin ctxt
                  (Pretty.indent (Config.get ctxt Thy_Output.indent) p)) ^
              "\\rulename{" ^ Output.output (Pretty.str_of (Thy_Output.pretty_text ctxt name)) ^ "}")
            #> space_implode "\\par\\smallskip%\n"
            #> enclose "\\begin{isabelle}%\n" "%\n\\end{isabelle}"
          else
            map (fn (p, name) =>
              Output.output (Pretty.str_of p) ^
              "\\rulename{" ^ Output.output (Pretty.str_of (Thy_Output.pretty_text ctxt name)) ^ "}")
            #> space_implode "\\par\\smallskip%\n"
            #> enclose "\\isa{" "}")));


(* theory file *)

val _ =
  Theory.setup (Thy_Output.antiquotation @{binding thy_file} (Scan.lift Args.name)
    (fn {context = ctxt, ...} =>
      fn name => (Resources.check_thy Path.current name; Thy_Output.output ctxt [Pretty.str name])));


(* Isabelle/jEdit elements *)

local

fun parse_named a (XML.Elem ((b, props), _)) =
      (case Properties.get props "NAME" of
        SOME name => if a = b then [name] else []
      | NONE => [])
  | parse_named _ _ = [];

val isabelle_jedit_actions =
  (case XML.parse (File.read @{path "~~/src/Tools/jEdit/src/actions.xml"}) of
    XML.Elem (("ACTIONS", _), body) => maps (parse_named "ACTION") body
  | _ => []);

val isabelle_jedit_dockables =
  (case XML.parse (File.read @{path "~~/src/Tools/jEdit/src/dockables.xml"}) of
    XML.Elem (("DOCKABLES", _), body) => maps (parse_named "DOCKABLE") body
  | _ => []);

val jedit_actions =
  Lazy.lazy (fn () =>
    (case Isabelle_System.bash_output
      "unzip -p \"$JEDIT_HOME/dist/jedit.jar\" org/gjt/sp/jedit/actions.xml" of
      (txt, 0) =>
        (case XML.parse txt of
          XML.Elem (("ACTIONS", _), body) => maps (parse_named "ACTION") body
        | _ => [])
    | (_, rc) => error ("Cannot unzip jedit.jar\nreturn code = " ^ string_of_int rc)));

in

fun is_action a =
  member (op =) isabelle_jedit_actions a orelse
  member (op =) isabelle_jedit_dockables a orelse
  member (op =) (Lazy.force jedit_actions) a;

end;


(* Isabelle/Isar entities (with index) *)

local

fun no_check _ _ = true;

fun is_keyword ctxt (name, _) =
  Keyword.is_keyword (Thy_Header.get_keywords' ctxt) name;

fun check_command ctxt (name, pos) =
  let
    val thy = Proof_Context.theory_of ctxt;
    val keywords = Thy_Header.get_keywords thy;
  in
    Keyword.is_command keywords name andalso
      let
        val markup =
          Token.explode keywords Position.none name
          |> maps (Outer_Syntax.command_reports thy)
          |> map (snd o fst);
        val _ = Context_Position.reports ctxt (map (pair pos) markup);
      in true end
  end;

fun check_system_option ctxt (name, pos) =
  (Context_Position.report ctxt pos (Options.default_markup (name, pos)); true)
    handle ERROR _ => false;

fun check_tool ctxt (name, pos) =
  let
    fun tool dir =
      let val path = Path.append dir (Path.basic name)
      in if File.exists path then SOME path else NONE end;
  in
    (case get_first tool (Path.split (getenv "ISABELLE_TOOLS")) of
      NONE => false
    | SOME path => (Context_Position.report ctxt pos (Markup.path (Path.implode path)); true))
  end;

val arg = enclose "{" "}" o clean_string;

fun entity check markup binding index =
  Thy_Output.antiquotation
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

val _ =
  Theory.setup
   (entity_antiqs no_check "" @{binding syntax} #>
    entity_antiqs check_command "isacommand" @{binding command} #>
    entity_antiqs is_keyword "isakeyword" @{binding keyword} #>
    entity_antiqs is_keyword "isakeyword" @{binding element} #>
    entity_antiqs (can o Method.check_name) "" @{binding method} #>
    entity_antiqs (can o Attrib.check_name) "" @{binding attribute} #>
    entity_antiqs no_check "" @{binding fact} #>
    entity_antiqs no_check "" @{binding variable} #>
    entity_antiqs no_check "" @{binding case} #>
    entity_antiqs (can o Thy_Output.check_command) "" @{binding antiquotation} #>
    entity_antiqs (can o Thy_Output.check_option) "" @{binding antiquotation_option} #>
    entity_antiqs no_check "isasystem" @{binding setting} #>
    entity_antiqs check_system_option "isasystem" @{binding system_option} #>
    entity_antiqs no_check "" @{binding inference} #>
    entity_antiqs no_check "isasystem" @{binding executable} #>
    entity_antiqs check_tool "isatool" @{binding tool} #>
    entity_antiqs (can o ML_Context.check_antiquotation) "" @{binding ML_antiquotation} #>
    entity_antiqs (K (is_action o #1)) "isasystem" @{binding action});

end;

end;
