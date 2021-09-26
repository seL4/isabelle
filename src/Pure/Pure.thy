(*  Title:      Pure/Pure.thy
    Author:     Makarius

The Pure theory, with definitions of Isar commands and some lemmas.
*)

theory Pure
keywords
    "!!" "!" "+" ":" ";" "<" "<=" "==" "=>" "?" "[" "\<comment>" "\<equiv>" "\<leftharpoondown>" "\<rightharpoonup>" "\<rightleftharpoons>"
    "\<subseteq>" "]" "binder" "in" "infix" "infixl" "infixr" "is" "open" "output"
    "overloaded" "pervasive" "premises" "structure" "unchecked"
  and "private" "qualified" :: before_command
  and "assumes" "constrains" "defines" "fixes" "for" "if" "includes" "notes" "rewrites"
    "obtains" "shows" "when" "where" "|" :: quasi_command
  and "text" "txt" :: document_body
  and "text_raw" :: document_raw
  and "default_sort" :: thy_decl
  and "typedecl" "nonterminal" "judgment" "consts" "syntax" "no_syntax" "translations"
    "no_translations" "type_notation" "no_type_notation" "notation" "no_notation" "alias"
    "type_alias" "declare" "hide_class" "hide_type" "hide_const" "hide_fact" :: thy_decl
  and "type_synonym" "definition" "abbreviation" "lemmas" :: thy_defn
  and "axiomatization" :: thy_stmt
  and "external_file" "bibtex_file" "ROOTS_file" :: thy_load
  and "generate_file" :: thy_decl
  and "export_generated_files" :: diag
  and "compile_generated_files" :: diag and "external_files" "export_files" "export_prefix"
  and "ML_file" "ML_file_debug" "ML_file_no_debug" :: thy_load % "ML"
  and "SML_file" "SML_file_debug" "SML_file_no_debug" :: thy_load % "ML"
  and "SML_import" "SML_export" "ML_export" :: thy_decl % "ML"
  and "ML_prf" :: prf_decl % "proof"  (* FIXME % "ML" ?? *)
  and "ML_val" "ML_command" :: diag % "ML"
  and "simproc_setup" :: thy_decl % "ML"
  and "setup" "local_setup" "attribute_setup" "method_setup"
    "declaration" "syntax_declaration"
    "parse_ast_translation" "parse_translation" "print_translation"
    "typed_print_translation" "print_ast_translation" "oracle" :: thy_decl % "ML"
  and "bundle" :: thy_decl_block
  and "unbundle" :: thy_decl
  and "include" "including" :: prf_decl
  and "print_bundles" :: diag
  and "context" "locale" "experiment" :: thy_decl_block
  and "interpret" :: prf_goal % "proof"
  and "interpretation" "global_interpretation" "sublocale" :: thy_goal
  and "class" :: thy_decl_block
  and "subclass" :: thy_goal
  and "instantiation" :: thy_decl_block
  and "instance" :: thy_goal
  and "overloading" :: thy_decl_block
  and "opening" :: quasi_command
  and "code_datatype" :: thy_decl
  and "theorem" "lemma" "corollary" "proposition" :: thy_goal_stmt
  and "schematic_goal" :: thy_goal_stmt
  and "notepad" :: thy_decl_block
  and "have" :: prf_goal % "proof"
  and "hence" :: prf_goal % "proof"
  and "show" :: prf_asm_goal % "proof"
  and "thus" :: prf_asm_goal % "proof"
  and "then" "from" "with" :: prf_chain % "proof"
  and "note" :: prf_decl % "proof"
  and "supply" :: prf_script % "proof"
  and "using" "unfolding" :: prf_decl % "proof"
  and "fix" "assume" "presume" "define" :: prf_asm % "proof"
  and "consider" :: prf_goal % "proof"
  and "obtain" :: prf_asm_goal % "proof"
  and "let" "write" :: prf_decl % "proof"
  and "case" :: prf_asm % "proof"
  and "{" :: prf_open % "proof"
  and "}" :: prf_close % "proof"
  and "next" :: next_block % "proof"
  and "qed" :: qed_block % "proof"
  and "by" ".." "." "sorry" "\<proof>" :: "qed" % "proof"
  and "done" :: "qed_script" % "proof"
  and "oops" :: qed_global % "proof"
  and "defer" "prefer" "apply" :: prf_script % "proof"
  and "apply_end" :: prf_script % "proof"
  and "subgoal" :: prf_script_goal % "proof"
  and "proof" :: prf_block % "proof"
  and "also" "moreover" :: prf_decl % "proof"
  and "finally" "ultimately" :: prf_chain % "proof"
  and "back" :: prf_script % "proof"
  and "help" "print_commands" "print_options" "print_context" "print_theory"
    "print_definitions" "print_syntax" "print_abbrevs" "print_defn_rules"
    "print_theorems" "print_locales" "print_classes" "print_locale"
    "print_interps" "print_attributes"
    "print_simpset" "print_rules" "print_trans_rules" "print_methods"
    "print_antiquotations" "print_ML_antiquotations" "thy_deps"
    "locale_deps" "class_deps" "thm_deps" "thm_oracles" "print_term_bindings"
    "print_facts" "print_cases" "print_statement" "thm" "prf" "full_prf"
    "prop" "term" "typ" "print_codesetup" "unused_thms" :: diag
  and "print_state" :: diag
  and "welcome" :: diag
  and "end" :: thy_end
  and "realizers" :: thy_decl
  and "realizability" :: thy_decl
  and "extract_type" "extract" :: thy_decl
  and "find_theorems" "find_consts" :: diag
  and "named_theorems" :: thy_decl
abbrevs "\\tag" = "\<^marker>\<open>tag \<close>"
  and "===>" = "===>"  (*prevent replacement of very long arrows*)
  and "--->" = "\<midarrow>\<rightarrow>"
  and "hence" "thus" "default_sort" "simproc_setup" "apply_end" "realizers" "realizability" = ""
  and "hence" = "then have"
  and "thus" = "then show"
begin

section \<open>Isar commands\<close>

subsection \<open>Other files\<close>

ML \<open>
local
  val _ =
    Outer_Syntax.command \<^command_keyword>\<open>external_file\<close> "formal dependency on external file"
      (Resources.provide_parse_file >> (fn get_file => Toplevel.theory (#2 o get_file)));

  val _ =
    Outer_Syntax.command \<^command_keyword>\<open>bibtex_file\<close> "check bibtex database file in Prover IDE"
      (Resources.provide_parse_file >> (fn get_file =>
        Toplevel.theory (fn thy =>
          let
            val ({lines, pos, ...}, thy') = get_file thy;
            val _ = Bibtex.check_database_output pos (cat_lines lines);
          in thy' end)));

  val _ =
    Outer_Syntax.command \<^command_keyword>\<open>ROOTS_file\<close> "session ROOTS file"
      (Resources.provide_parse_file >> (fn get_file =>
        Toplevel.theory (fn thy =>
          let
            val ({src_path, lines, pos = pos0, ...}, thy') = get_file thy;
            val ctxt = Proof_Context.init_global thy';
            val dir = Path.dir (Path.expand (Resources.master_directory thy' + src_path));
            val _ =
              (lines, pos0) |-> fold (fn line => fn pos1 =>
                let
                  val pos2 = Position.symbol_explode line pos1;
                  val range = Position.range (pos1, pos2);
                  val source = Input.source true line range;
                  val _ =
                    if line = "" then ()
                    else if String.isPrefix "#" line then
                      Context_Position.report ctxt (#1 range) Markup.comment
                    else
                      (ignore (Resources.check_session_dir ctxt (SOME dir) source)
                        handle ERROR msg => Output.error_message msg);
                in pos2 |> Position.symbol "\n" end);
          in thy' end)));

  val _ =
    Outer_Syntax.local_theory \<^command_keyword>\<open>generate_file\<close>
      "generate source file, with antiquotations"
      (Parse.path_binding -- (\<^keyword>\<open>=\<close> |-- Parse.embedded_input)
        >> Generated_Files.generate_file_cmd);


  val files_in_theory =
    (Parse.underscore >> K [] || Scan.repeat1 Parse.path_binding) --
      Scan.option (\<^keyword>\<open>(\<close> |-- Parse.!!! (\<^keyword>\<open>in\<close> |-- Parse.theory_name --| \<^keyword>\<open>)\<close>));

  val _ =
    Outer_Syntax.command \<^command_keyword>\<open>export_generated_files\<close>
      "export generated files from given theories"
      (Parse.and_list1 files_in_theory >> (fn args =>
        Toplevel.keep (fn st =>
          Generated_Files.export_generated_files_cmd (Toplevel.context_of st) args)));


  val base_dir =
    Scan.optional (\<^keyword>\<open>(\<close> |--
      Parse.!!! (\<^keyword>\<open>in\<close> |-- Parse.path_input --| \<^keyword>\<open>)\<close>)) (Input.string "");

  val external_files = Scan.repeat1 Parse.path_input -- base_dir;

  val exe = Parse.reserved "exe" >> K true || Parse.reserved "executable" >> K false;
  val executable = \<^keyword>\<open>(\<close> |-- Parse.!!! (exe --| \<^keyword>\<open>)\<close>) >> SOME || Scan.succeed NONE;

  val export_files = Scan.repeat1 Parse.path_binding -- executable;

  val _ =
    Outer_Syntax.command \<^command_keyword>\<open>compile_generated_files\<close>
      "compile generated files and export results"
      (Parse.and_list files_in_theory --
        Scan.optional (\<^keyword>\<open>external_files\<close> |-- Parse.!!! (Parse.and_list1 external_files)) [] --
        Scan.optional (\<^keyword>\<open>export_files\<close> |-- Parse.!!! (Parse.and_list1 export_files)) [] --
        Scan.optional (\<^keyword>\<open>export_prefix\<close> |-- Parse.path_binding) ("", Position.none) --
        (Parse.where_ |-- Parse.!!! Parse.ML_source)
        >> (fn ((((args, external), export), export_prefix), source) =>
          Toplevel.keep (fn st =>
            Generated_Files.compile_generated_files_cmd
              (Toplevel.context_of st) args external export export_prefix source)));

in end\<close>

external_file "ROOT0.ML"
external_file "ROOT.ML"


subsection \<open>Embedded ML text\<close>

ML \<open>
local

val semi = Scan.option \<^keyword>\<open>;\<close>;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>ML_file\<close> "read and evaluate Isabelle/ML file"
    (Resources.parse_file --| semi >> ML_File.ML NONE);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>ML_file_debug\<close>
    "read and evaluate Isabelle/ML file (with debugger information)"
    (Resources.parse_file --| semi >> ML_File.ML (SOME true));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>ML_file_no_debug\<close>
    "read and evaluate Isabelle/ML file (no debugger information)"
    (Resources.parse_file --| semi >> ML_File.ML (SOME false));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>SML_file\<close> "read and evaluate Standard ML file"
    (Resources.parse_file --| semi >> ML_File.SML NONE);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>SML_file_debug\<close>
    "read and evaluate Standard ML file (with debugger information)"
    (Resources.parse_file --| semi >> ML_File.SML (SOME true));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>SML_file_no_debug\<close>
    "read and evaluate Standard ML file (no debugger information)"
    (Resources.parse_file --| semi >> ML_File.SML (SOME false));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>SML_export\<close> "evaluate SML within Isabelle/ML environment"
    (Parse.ML_source >> (fn source =>
      let
        val flags: ML_Compiler.flags =
          {environment = ML_Env.SML_export, redirect = false, verbose = true,
            debug = NONE, writeln = writeln, warning = warning};
      in
        Toplevel.theory
          (Context.theory_map (ML_Context.exec (fn () => ML_Context.eval_source flags source)))
      end));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>SML_import\<close> "evaluate Isabelle/ML within SML environment"
    (Parse.ML_source >> (fn source =>
      let
        val flags: ML_Compiler.flags =
          {environment = ML_Env.SML_import, redirect = false, verbose = true,
            debug = NONE, writeln = writeln, warning = warning};
      in
        Toplevel.generic_theory
          (ML_Context.exec (fn () => ML_Context.eval_source flags source) #>
            Local_Theory.propagate_ml_env)
      end));

val _ =
  Outer_Syntax.command ("ML_export", \<^here>)
    "ML text within theory or local theory, and export to bootstrap environment"
    (Parse.ML_source >> (fn source =>
      Toplevel.generic_theory (fn context =>
        context
        |> Config.put_generic ML_Env.ML_environment ML_Env.Isabelle
        |> Config.put_generic ML_Env.ML_write_global true
        |> ML_Context.exec (fn () =>
            ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source)
        |> Config.restore_generic ML_Env.ML_write_global context
        |> Config.restore_generic ML_Env.ML_environment context
        |> Local_Theory.propagate_ml_env)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>ML_prf\<close> "ML text within proof"
    (Parse.ML_source >> (fn source =>
      Toplevel.proof (Proof.map_context (Context.proof_map
        (ML_Context.exec (fn () =>
            ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source))) #>
          Proof.propagate_ml_env)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>ML_val\<close> "diagnostic ML text"
    (Parse.ML_source >> Isar_Cmd.ml_diag true);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>ML_command\<close> "diagnostic ML text (silent)"
    (Parse.ML_source >> Isar_Cmd.ml_diag false);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>setup\<close> "ML setup for global theory"
    (Parse.ML_source >> (Toplevel.theory o Isar_Cmd.setup));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>local_setup\<close> "ML setup for local theory"
    (Parse.ML_source >> Isar_Cmd.local_setup);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>oracle\<close> "declare oracle"
    (Parse.range Parse.name -- Parse.!!! (\<^keyword>\<open>=\<close> |-- Parse.ML_source) >>
      (fn (x, y) => Toplevel.theory (Isar_Cmd.oracle x y)));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>attribute_setup\<close> "define attribute in ML"
    (Parse.name_position --
        Parse.!!! (\<^keyword>\<open>=\<close> |-- Parse.ML_source -- Scan.optional Parse.text "")
      >> (fn (name, (txt, cmt)) => Attrib.attribute_setup name txt cmt));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>method_setup\<close> "define proof method in ML"
    (Parse.name_position --
        Parse.!!! (\<^keyword>\<open>=\<close> |-- Parse.ML_source -- Scan.optional Parse.text "")
      >> (fn (name, (txt, cmt)) => Method.method_setup name txt cmt));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>declaration\<close> "generic ML declaration"
    (Parse.opt_keyword "pervasive" -- Parse.ML_source
      >> (fn (pervasive, txt) => Isar_Cmd.declaration {syntax = false, pervasive = pervasive} txt));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>syntax_declaration\<close> "generic ML syntax declaration"
    (Parse.opt_keyword "pervasive" -- Parse.ML_source
      >> (fn (pervasive, txt) => Isar_Cmd.declaration {syntax = true, pervasive = pervasive} txt));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>simproc_setup\<close> "define simproc in ML"
    (Parse.name_position --
      (\<^keyword>\<open>(\<close> |-- Parse.enum1 "|" Parse.term --| \<^keyword>\<open>)\<close> --| \<^keyword>\<open>=\<close>) --
      Parse.ML_source >> (fn ((a, b), c) => Isar_Cmd.simproc_setup a b c));

in end\<close>


subsection \<open>Theory commands\<close>

subsubsection \<open>Sorts and types\<close>

ML \<open>
local

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>default_sort\<close>
    "declare default sort for explicit type variables"
    (Parse.sort >> (fn s => fn lthy => Local_Theory.set_defsort (Syntax.read_sort lthy s) lthy));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>typedecl\<close> "type declaration"
    (Parse.type_args -- Parse.binding -- Parse.opt_mixfix
      >> (fn ((args, a), mx) =>
          Typedecl.typedecl {final = true} (a, map (rpair dummyS) args, mx) #> snd));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>type_synonym\<close> "declare type abbreviation"
    (Parse.type_args -- Parse.binding --
      (\<^keyword>\<open>=\<close> |-- Parse.!!! (Parse.typ -- Parse.opt_mixfix'))
      >> (fn ((args, a), (rhs, mx)) => snd o Typedecl.abbrev_cmd (a, args, mx) rhs));

in end\<close>


subsubsection \<open>Consts\<close>

ML \<open>
local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>judgment\<close> "declare object-logic judgment"
    (Parse.const_binding >> (Toplevel.theory o Object_Logic.add_judgment_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>consts\<close> "declare constants"
    (Scan.repeat1 Parse.const_binding >> (Toplevel.theory o Sign.add_consts_cmd));

in end\<close>


subsubsection \<open>Syntax and translations\<close>

ML \<open>
local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>nonterminal\<close>
    "declare syntactic type constructors (grammar nonterminal symbols)"
    (Parse.and_list1 Parse.binding >> (Toplevel.theory o Sign.add_nonterminals_global));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>syntax\<close> "add raw syntax clauses"
    (Parse.syntax_mode -- Scan.repeat1 Parse.const_decl
      >> uncurry (Local_Theory.syntax_cmd true));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>no_syntax\<close> "delete raw syntax clauses"
    (Parse.syntax_mode -- Scan.repeat1 Parse.const_decl
      >> uncurry (Local_Theory.syntax_cmd false));

val trans_pat =
  Scan.optional
    (\<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.inner_syntax Parse.name --| \<^keyword>\<open>)\<close>)) "logic"
    -- Parse.inner_syntax Parse.string;

fun trans_arrow toks =
  ((\<^keyword>\<open>\<rightharpoonup>\<close> || \<^keyword>\<open>=>\<close>) >> K Syntax.Parse_Rule ||
    (\<^keyword>\<open>\<leftharpoondown>\<close> || \<^keyword>\<open><=\<close>) >> K Syntax.Print_Rule ||
    (\<^keyword>\<open>\<rightleftharpoons>\<close> || \<^keyword>\<open>==\<close>) >> K Syntax.Parse_Print_Rule) toks;

val trans_line =
  trans_pat -- Parse.!!! (trans_arrow -- trans_pat)
    >> (fn (left, (arr, right)) => arr (left, right));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>translations\<close> "add syntax translation rules"
    (Scan.repeat1 trans_line >> (Toplevel.theory o Isar_Cmd.translations));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>no_translations\<close> "delete syntax translation rules"
    (Scan.repeat1 trans_line >> (Toplevel.theory o Isar_Cmd.no_translations));

in end\<close>


subsubsection \<open>Translation functions\<close>

ML \<open>
local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>parse_ast_translation\<close>
    "install parse ast translation functions"
    (Parse.ML_source >> (Toplevel.theory o Isar_Cmd.parse_ast_translation));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>parse_translation\<close>
    "install parse translation functions"
    (Parse.ML_source >> (Toplevel.theory o Isar_Cmd.parse_translation));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_translation\<close>
    "install print translation functions"
    (Parse.ML_source >> (Toplevel.theory o Isar_Cmd.print_translation));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>typed_print_translation\<close>
    "install typed print translation functions"
    (Parse.ML_source >> (Toplevel.theory o Isar_Cmd.typed_print_translation));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_ast_translation\<close>
    "install print ast translation functions"
    (Parse.ML_source >> (Toplevel.theory o Isar_Cmd.print_ast_translation));

in end\<close>


subsubsection \<open>Specifications\<close>

ML \<open>
local

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>definition\<close> "constant definition"
    (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes >> (fn (((decl, spec), prems), params) =>
        #2 oo Specification.definition_cmd decl params prems spec));

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>abbreviation\<close> "constant abbreviation"
    (Parse.syntax_mode -- Scan.option Parse_Spec.constdecl -- Parse.prop -- Parse.for_fixes
      >> (fn (((mode, decl), spec), params) => Specification.abbreviation_cmd mode decl params spec));

val axiomatization =
  Parse.and_list1 (Parse_Spec.thm_name ":" -- Parse.prop) --
  Parse_Spec.if_assumes -- Parse.for_fixes >> (fn ((a, b), c) => (c, b, a));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>axiomatization\<close> "axiomatic constant specification"
    (Scan.optional Parse.vars [] --
      Scan.optional (Parse.where_ |-- Parse.!!! axiomatization) ([], [], [])
      >> (fn (a, (b, c, d)) => Toplevel.theory (#2 o Specification.axiomatization_cmd a b c d)));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>alias\<close> "name-space alias for constant"
    (Parse.binding -- (Parse.!!! \<^keyword>\<open>=\<close> |-- Parse.name_position)
      >> Specification.alias_cmd);

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>type_alias\<close> "name-space alias for type constructor"
    (Parse.binding -- (Parse.!!! \<^keyword>\<open>=\<close> |-- Parse.name_position)
      >> Specification.type_alias_cmd);

in end\<close>


subsubsection \<open>Notation\<close>

ML \<open>
local

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>type_notation\<close>
    "add concrete syntax for type constructors"
    (Parse.syntax_mode -- Parse.and_list1 (Parse.type_const -- Parse.mixfix)
      >> (fn (mode, args) => Local_Theory.type_notation_cmd true mode args));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>no_type_notation\<close>
    "delete concrete syntax for type constructors"
    (Parse.syntax_mode -- Parse.and_list1 (Parse.type_const -- Parse.mixfix)
      >> (fn (mode, args) => Local_Theory.type_notation_cmd false mode args));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>notation\<close>
    "add concrete syntax for constants / fixed variables"
    (Parse.syntax_mode -- Parse.and_list1 (Parse.const -- Parse.mixfix)
      >> (fn (mode, args) => Local_Theory.notation_cmd true mode args));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>no_notation\<close>
    "delete concrete syntax for constants / fixed variables"
    (Parse.syntax_mode -- Parse.and_list1 (Parse.const -- Parse.mixfix)
      >> (fn (mode, args) => Local_Theory.notation_cmd false mode args));

in end\<close>


subsubsection \<open>Theorems\<close>

ML \<open>
local

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun theorem spec schematic descr =
  Outer_Syntax.local_theory_to_proof' spec ("state " ^ descr)
    ((long_statement || short_statement) >> (fn (long, binding, includes, elems, concl) =>
      ((if schematic then Specification.schematic_theorem_cmd else Specification.theorem_cmd)
        long Thm.theoremK NONE (K I) binding includes elems concl)));

val _ = theorem \<^command_keyword>\<open>theorem\<close> false "theorem";
val _ = theorem \<^command_keyword>\<open>lemma\<close> false "lemma";
val _ = theorem \<^command_keyword>\<open>corollary\<close> false "corollary";
val _ = theorem \<^command_keyword>\<open>proposition\<close> false "proposition";
val _ = theorem \<^command_keyword>\<open>schematic_goal\<close> true "schematic goal";

in end\<close>

ML \<open>
local

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>lemmas\<close> "define theorems"
    (Parse_Spec.name_facts -- Parse.for_fixes >>
      (fn (facts, fixes) => #2 oo Specification.theorems_cmd Thm.theoremK facts fixes));

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>declare\<close> "declare theorems"
    (Parse.and_list1 Parse.thms1 -- Parse.for_fixes
      >> (fn (facts, fixes) =>
          #2 oo Specification.theorems_cmd "" [(Binding.empty_atts, flat facts)] fixes));

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>named_theorems\<close>
    "declare named collection of theorems"
    (Parse.and_list1 (Parse.binding -- Scan.optional Parse.text "") >>
      fold (fn (b, descr) => snd o Named_Theorems.declare b descr));

in end\<close>


subsubsection \<open>Hide names\<close>

ML \<open>
local

fun hide_names command_keyword what hide parse prep =
  Outer_Syntax.command command_keyword ("hide " ^ what ^ " from name space")
    ((Parse.opt_keyword "open" >> not) -- Scan.repeat1 parse >> (fn (fully, args) =>
      (Toplevel.theory (fn thy =>
        let val ctxt = Proof_Context.init_global thy
        in fold (hide fully o prep ctxt) args thy end))));

val _ =
  hide_names \<^command_keyword>\<open>hide_class\<close> "classes" Sign.hide_class Parse.class
    Proof_Context.read_class;

val _ =
  hide_names \<^command_keyword>\<open>hide_type\<close> "types" Sign.hide_type Parse.type_const
    ((#1 o dest_Type) oo Proof_Context.read_type_name {proper = true, strict = false});

val _ =
  hide_names \<^command_keyword>\<open>hide_const\<close> "consts" Sign.hide_const Parse.const
    ((#1 o dest_Const) oo Proof_Context.read_const {proper = true, strict = false});

val _ =
  hide_names \<^command_keyword>\<open>hide_fact\<close> "facts" Global_Theory.hide_fact
    Parse.name_position (Global_Theory.check_fact o Proof_Context.theory_of);

in end\<close>


subsection \<open>Bundled declarations\<close>

ML \<open>
local

val _ =
  Outer_Syntax.maybe_begin_local_theory \<^command_keyword>\<open>bundle\<close>
    "define bundle of declarations"
    ((Parse.binding --| \<^keyword>\<open>=\<close>) -- Parse.thms1 -- Parse.for_fixes
      >> (uncurry Bundle.bundle_cmd))
    (Parse.binding --| Parse.begin >> Bundle.init);

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>unbundle\<close>
    "activate declarations from bundle in local theory"
    (Scan.repeat1 Parse.name_position >> Bundle.unbundle_cmd);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>include\<close>
    "activate declarations from bundle in proof body"
    (Scan.repeat1 Parse.name_position >> (Toplevel.proof o Bundle.include_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>including\<close>
    "activate declarations from bundle in goal refinement"
    (Scan.repeat1 Parse.name_position >> (Toplevel.proof o Bundle.including_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_bundles\<close>
    "print bundles of declarations"
    (Parse.opt_bang >> (fn b => Toplevel.keep (Bundle.print_bundles b o Toplevel.context_of)));

in end\<close>


subsection \<open>Local theory specifications\<close>

subsubsection \<open>Specification context\<close>

ML \<open>
local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>context\<close> "begin local theory context"
    (((Parse.name_position -- Scan.optional Parse_Spec.opening [])
        >> (fn (name, incls) => Toplevel.begin_main_target true (Target_Context.context_begin_named_cmd incls name)) ||
      Scan.optional Parse_Spec.includes [] -- Scan.repeat Parse_Spec.context_element
        >> (fn (incls, elems) => Toplevel.begin_nested_target (Target_Context.context_begin_nested_cmd incls elems)))
      --| Parse.begin);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>end\<close> "end context"
    (Scan.succeed
      (Toplevel.exit o Toplevel.end_main_target o Toplevel.end_nested_target o
        Toplevel.end_proof (K Proof.end_notepad)));

in end\<close>


subsubsection \<open>Locales and interpretation\<close>

ML \<open>
local

val locale_context_elements =
  Scan.repeat1 Parse_Spec.context_element;

val locale_val =
  ((Parse_Spec.locale_expression -- Scan.optional Parse_Spec.opening [])
    || Parse_Spec.opening >> pair ([], []))
  -- Scan.optional (\<^keyword>\<open>+\<close> |-- Parse.!!! locale_context_elements) []
  || locale_context_elements >> pair (([], []), []);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>locale\<close> "define named specification context"
    (Parse.binding --
      Scan.optional (\<^keyword>\<open>=\<close> |-- Parse.!!! locale_val) ((([], []), []), []) -- Parse.opt_begin
      >> (fn ((name, ((expr, includes), elems)), begin) =>
          Toplevel.begin_main_target begin
            (Expression.add_locale_cmd name Binding.empty includes expr elems #> snd)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>experiment\<close> "open private specification context"
    (Scan.repeat Parse_Spec.context_element --| Parse.begin
      >> (fn elems =>
          Toplevel.begin_main_target true (Experiment.experiment_cmd elems #> snd)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>interpret\<close>
    "prove interpretation of locale expression in proof context"
    (Parse.!!! Parse_Spec.locale_expression >> (fn expr =>
      Toplevel.proof (Interpretation.interpret_cmd expr)));

val interpretation_args_with_defs =
  Parse.!!! Parse_Spec.locale_expression --
    (Scan.optional (\<^keyword>\<open>defines\<close> |-- Parse.and_list1 (Parse_Spec.opt_thm_name ":"
      -- ((Parse.binding -- Parse.opt_mixfix') --| \<^keyword>\<open>=\<close> -- Parse.term))) ([]));

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>global_interpretation\<close>
    "prove interpretation of locale expression into global theory"
    (interpretation_args_with_defs >> (fn (expr, defs) =>
      Interpretation.global_interpretation_cmd expr defs));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>sublocale\<close>
    "prove sublocale relation between a locale and a locale expression"
    ((Parse.name_position --| (\<^keyword>\<open>\<subseteq>\<close> || \<^keyword>\<open><\<close>) --
      interpretation_args_with_defs >> (fn (loc, (expr, defs)) =>
        Toplevel.theory_to_proof (Interpretation.global_sublocale_cmd loc expr defs)))
    || interpretation_args_with_defs >> (fn (expr, defs) =>
        Toplevel.local_theory_to_proof NONE NONE (Interpretation.sublocale_cmd expr defs)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>interpretation\<close>
    "prove interpretation of locale expression in local theory or into global theory"
    (Parse.!!! Parse_Spec.locale_expression >> (fn expr =>
      Toplevel.local_theory_to_proof NONE NONE
        (Interpretation.isar_interpretation_cmd expr)));

in end\<close>


subsubsection \<open>Type classes\<close>

ML \<open>
local

val class_context_elements =
  Scan.repeat1 Parse_Spec.context_element;

val class_val =
  ((Parse_Spec.class_expression -- Scan.optional Parse_Spec.opening [])
    || Parse_Spec.opening >> pair [])
  -- Scan.optional (\<^keyword>\<open>+\<close> |-- Parse.!!! class_context_elements) [] ||
  class_context_elements >> pair ([], []);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>class\<close> "define type class"
   (Parse.binding -- Scan.optional (\<^keyword>\<open>=\<close> |-- class_val) (([], []), []) -- Parse.opt_begin
    >> (fn ((name, ((supclasses, includes), elems)), begin) =>
        Toplevel.begin_main_target begin
          (Class_Declaration.class_cmd name includes supclasses elems #> snd)));

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>subclass\<close> "prove a subclass relation"
    (Parse.class >> Class_Declaration.subclass_cmd);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>instantiation\<close> "instantiate and prove type arity"
   (Parse.multi_arity --| Parse.begin
     >> (fn arities => Toplevel.begin_main_target true (Class.instantiation_cmd arities)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>instance\<close> "prove type arity or subclass relation"
  ((Parse.class --
    ((\<^keyword>\<open>\<subseteq>\<close> || \<^keyword>\<open><\<close>) |-- Parse.!!! Parse.class) >> Class.classrel_cmd ||
    Parse.multi_arity >> Class.instance_arity_cmd) >> Toplevel.theory_to_proof ||
    Scan.succeed (Toplevel.local_theory_to_proof NONE NONE (Class.instantiation_instance I)));

in end\<close>


subsubsection \<open>Arbitrary overloading\<close>

ML \<open>
local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>overloading\<close> "overloaded definitions"
   (Scan.repeat1 (Parse.name --| (\<^keyword>\<open>==\<close> || \<^keyword>\<open>\<equiv>\<close>) -- Parse.term --
      Scan.optional (\<^keyword>\<open>(\<close> |-- (\<^keyword>\<open>unchecked\<close> >> K false) --| \<^keyword>\<open>)\<close>) true
      >> Scan.triple1) --| Parse.begin
   >> (fn operations => Toplevel.begin_main_target true (Overloading.overloading_cmd operations)));

in end\<close>


subsection \<open>Proof commands\<close>

ML \<open>
local

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>notepad\<close> "begin proof context"
    (Parse.begin >> K Proof.begin_notepad);

in end\<close>


subsubsection \<open>Statements\<close>

ML \<open>
local

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.cond_statement -- Parse.for_fixes
    >> (fn ((shows, (strict, assumes)), fixes) => (strict, fixes, assumes, shows));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>have\<close> "state local goal"
    (structured_statement >> (fn (a, b, c, d) =>
      Toplevel.proof' (fn int => Proof.have_cmd a NONE (K I) b c d int #> #2)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>show\<close> "state local goal, to refine pending subgoals"
    (structured_statement >> (fn (a, b, c, d) =>
      Toplevel.proof' (fn int => Proof.show_cmd a NONE (K I) b c d int #> #2)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>hence\<close> "old-style alias of \"then have\""
    (structured_statement >> (fn (a, b, c, d) =>
      Toplevel.proof' (fn int => Proof.chain #> Proof.have_cmd a NONE (K I) b c d int #> #2)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>thus\<close> "old-style alias of  \"then show\""
    (structured_statement >> (fn (a, b, c, d) =>
      Toplevel.proof' (fn int => Proof.chain #> Proof.show_cmd a NONE (K I) b c d int #> #2)));

in end\<close>


subsubsection \<open>Local facts\<close>

ML \<open>
local

val facts = Parse.and_list1 Parse.thms1;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>then\<close> "forward chaining"
    (Scan.succeed (Toplevel.proof Proof.chain));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>from\<close> "forward chaining from given facts"
    (facts >> (Toplevel.proof o Proof.from_thmss_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>with\<close> "forward chaining from given and current facts"
    (facts >> (Toplevel.proof o Proof.with_thmss_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>note\<close> "define facts"
    (Parse_Spec.name_facts >> (Toplevel.proof o Proof.note_thmss_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>supply\<close> "define facts during goal refinement (unstructured)"
    (Parse_Spec.name_facts >> (Toplevel.proof o Proof.supply_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>using\<close> "augment goal facts"
    (facts >> (Toplevel.proof o Proof.using_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>unfolding\<close> "unfold definitions in goal and facts"
    (facts >> (Toplevel.proof o Proof.unfolding_cmd));

in end\<close>


subsubsection \<open>Proof context\<close>

ML \<open>
local

val structured_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement' -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) => (fixes, assumes, shows));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>fix\<close> "fix local variables (Skolem constants)"
    (Parse.vars >> (Toplevel.proof o Proof.fix_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>assume\<close> "assume propositions"
    (structured_statement >> (fn (a, b, c) => Toplevel.proof (Proof.assume_cmd a b c)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>presume\<close> "assume propositions, to be established later"
    (structured_statement >> (fn (a, b, c) => Toplevel.proof (Proof.presume_cmd a b c)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>define\<close> "local definition (non-polymorphic)"
    ((Parse.vars --| Parse.where_) -- Parse_Spec.statement -- Parse.for_fixes
      >> (fn ((a, b), c) => Toplevel.proof (Proof.define_cmd a c b)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>consider\<close> "state cases rule"
    (Parse_Spec.obtains >> (Toplevel.proof' o Obtain.consider_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>obtain\<close> "generalized elimination"
    (Parse.parbinding -- Scan.optional (Parse.vars --| Parse.where_) [] -- structured_statement
      >> (fn ((a, b), (c, d, e)) => Toplevel.proof' (Obtain.obtain_cmd a b c d e)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>let\<close> "bind text variables"
    (Parse.and_list1 (Parse.and_list1 Parse.term -- (\<^keyword>\<open>=\<close> |-- Parse.term))
      >> (Toplevel.proof o Proof.let_bind_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>write\<close> "add concrete syntax for constants / fixed variables"
    (Parse.syntax_mode -- Parse.and_list1 (Parse.const -- Parse.mixfix)
    >> (fn (mode, args) => Toplevel.proof (Proof.write_cmd mode args)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>case\<close> "invoke local context"
    (Parse_Spec.opt_thm_name ":" --
      (\<^keyword>\<open>(\<close> |-- Parse.!!! (Parse.name_position -- Scan.repeat (Parse.maybe Parse.binding)
          --| \<^keyword>\<open>)\<close>) ||
        Parse.name_position >> rpair []) >> (Toplevel.proof o Proof.case_cmd));

in end\<close>


subsubsection \<open>Proof structure\<close>

ML \<open>
local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>{\<close> "begin explicit proof block"
    (Scan.succeed (Toplevel.proof Proof.begin_block));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>}\<close> "end explicit proof block"
    (Scan.succeed (Toplevel.proof Proof.end_block));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>next\<close> "enter next proof block"
    (Scan.succeed (Toplevel.proof Proof.next_block));

in end\<close>


subsubsection \<open>End proof\<close>

ML \<open>
local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>qed\<close> "conclude proof"
    (Scan.option Method.parse >> (fn m =>
     (Option.map Method.report m;
      Isar_Cmd.qed m)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>by\<close> "terminal backward proof"
    (Method.parse -- Scan.option Method.parse >> (fn (m1, m2) =>
     (Method.report m1;
      Option.map Method.report m2;
      Isar_Cmd.terminal_proof (m1, m2))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>..\<close> "default proof"
    (Scan.succeed Isar_Cmd.default_proof);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>.\<close> "immediate proof"
    (Scan.succeed Isar_Cmd.immediate_proof);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>done\<close> "done proof"
    (Scan.succeed Isar_Cmd.done_proof);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>sorry\<close> "skip proof (quick-and-dirty mode only!)"
    (Scan.succeed Isar_Cmd.skip_proof);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>\<proof>\<close> "dummy proof (quick-and-dirty mode only!)"
    (Scan.succeed Isar_Cmd.skip_proof);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>oops\<close> "forget proof"
    (Scan.succeed Toplevel.forget_proof);

in end\<close>


subsubsection \<open>Proof steps\<close>

ML \<open>
local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>defer\<close> "shuffle internal proof state"
    (Scan.optional Parse.nat 1 >> (Toplevel.proof o Proof.defer));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>prefer\<close> "shuffle internal proof state"
    (Parse.nat >> (Toplevel.proof o Proof.prefer));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply\<close> "initial goal refinement step (unstructured)"
    (Method.parse >> (fn m => (Method.report m; Toplevel.proofs (Proof.apply m))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply_end\<close> "terminal goal refinement step (unstructured)"
    (Method.parse >> (fn m => (Method.report m; Toplevel.proofs (Proof.apply_end m))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>proof\<close> "backward proof step"
    (Scan.option Method.parse >> (fn m =>
      (Option.map Method.report m;
       Toplevel.proof (fn state =>
         let
          val state' = state |> Proof.proof m |> Seq.the_result "";
          val _ =
            Output.information
              (Proof_Context.print_cases_proof (Proof.context_of state) (Proof.context_of state'));
        in state' end))))

in end\<close>


subsubsection \<open>Subgoal focus\<close>

ML \<open>
local

val opt_fact_binding =
  Scan.optional (Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty)
    Binding.empty_atts;

val for_params =
  Scan.optional
    (\<^keyword>\<open>for\<close> |--
      Parse.!!! ((Scan.option Parse.dots >> is_some) --
        (Scan.repeat1 (Parse.maybe_position Parse.name_position))))
    (false, []);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>subgoal\<close>
    "focus on first subgoal within backward refinement"
    (opt_fact_binding -- (Scan.option (\<^keyword>\<open>premises\<close> |-- Parse.!!! opt_fact_binding)) --
      for_params >> (fn ((a, b), c) =>
        Toplevel.proofs (Seq.make_results o Seq.single o #2 o Subgoal.subgoal_cmd a b c)));

in end\<close>


subsubsection \<open>Calculation\<close>

ML \<open>
local

val calculation_args =
  Scan.option (\<^keyword>\<open>(\<close> |-- Parse.!!! ((Parse.thms1 --| \<^keyword>\<open>)\<close>)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>also\<close> "combine calculation and current facts"
    (calculation_args >> (Toplevel.proofs' o Calculation.also_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>finally\<close>
    "combine calculation and current facts, exhibit result"
    (calculation_args >> (Toplevel.proofs' o Calculation.finally_cmd));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>moreover\<close> "augment calculation by current facts"
    (Scan.succeed (Toplevel.proof' Calculation.moreover));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>ultimately\<close>
    "augment calculation by current facts, exhibit result"
    (Scan.succeed (Toplevel.proof' Calculation.ultimately));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_trans_rules\<close> "print transitivity rules"
    (Scan.succeed (Toplevel.keep (Calculation.print_rules o Toplevel.context_of)));

in end\<close>


subsubsection \<open>Proof navigation\<close>

ML \<open>
local

fun report_back () =
  Output.report [Markup.markup (Markup.bad ()) "Explicit backtracking"];

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>back\<close> "explicit backtracking of proof command"
    (Scan.succeed
     (Toplevel.actual_proof (fn prf => (report_back (); Proof_Node.back prf)) o
      Toplevel.skip_proof report_back));

in end\<close>


subsection \<open>Diagnostic commands (for interactive mode only)\<close>

ML \<open>
local

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>help\<close>
    "retrieve outer syntax commands according to name patterns"
    (Scan.repeat Parse.name >>
      (fn pats => Toplevel.keep (fn st => Outer_Syntax.help (Toplevel.theory_of st) pats)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_commands\<close> "print outer syntax commands"
    (Scan.succeed (Toplevel.keep (Outer_Syntax.print_commands o Toplevel.theory_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_options\<close> "print configuration options"
    (Parse.opt_bang >> (fn b => Toplevel.keep (Attrib.print_options b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_context\<close>
    "print context of local theory target"
    (Scan.succeed (Toplevel.keep (Pretty.writeln_chunks o Toplevel.pretty_context)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_theory\<close>
    "print logical theory contents"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (Pretty.writeln o Proof_Display.pretty_theory b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_definitions\<close>
    "print dependencies of definitional theory content"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (Pretty.writeln o Proof_Display.pretty_definitions b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_syntax\<close>
    "print inner syntax of context"
    (Scan.succeed (Toplevel.keep (Proof_Context.print_syntax o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_defn_rules\<close>
    "print definitional rewrite rules of context"
    (Scan.succeed (Toplevel.keep (Local_Defs.print_rules o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_abbrevs\<close>
    "print constant abbreviations of context"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (Proof_Context.print_abbrevs b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_theorems\<close>
    "print theorems of local theory or proof context"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (Pretty.writeln o Pretty.chunks o Isar_Cmd.pretty_theorems b)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_locales\<close>
    "print locales of this theory"
    (Parse.opt_bang >> (fn verbose =>
      Toplevel.keep (fn state =>
        let val thy = Toplevel.theory_of state
        in Pretty.writeln (Locale.pretty_locales thy verbose) end)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_classes\<close>
    "print classes of this theory"
    (Scan.succeed (Toplevel.keep (Class.print_classes o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_locale\<close>
    "print locale of this theory"
    (Parse.opt_bang -- Parse.name_position >> (fn (show_facts, raw_name) =>
      Toplevel.keep (fn state =>
        let
          val thy = Toplevel.theory_of state;
          val name = Locale.check thy raw_name;
        in Pretty.writeln (Locale.pretty_locale thy show_facts name) end)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_interps\<close>
    "print interpretations of locale for this theory or proof context"
    (Parse.name_position >> (fn raw_name =>
      Toplevel.keep (fn state =>
        let
          val ctxt = Toplevel.context_of state;
          val thy = Toplevel.theory_of state;
          val name = Locale.check thy raw_name;
        in Pretty.writeln (Locale.pretty_registrations ctxt name) end)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_attributes\<close>
    "print attributes of this theory"
    (Parse.opt_bang >> (fn b => Toplevel.keep (Attrib.print_attributes b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_simpset\<close>
    "print context of Simplifier"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (Pretty.writeln o Simplifier.pretty_simpset b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_rules\<close> "print intro/elim rules"
    (Scan.succeed (Toplevel.keep (Context_Rules.print_rules o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_methods\<close> "print methods of this theory"
    (Parse.opt_bang >> (fn b => Toplevel.keep (Method.print_methods b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_antiquotations\<close>
    "print document antiquotations"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (Document_Antiquotation.print_antiquotations b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_ML_antiquotations\<close>
    "print ML antiquotations"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (ML_Context.print_antiquotations b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>locale_deps\<close> "visualize locale dependencies"
    (Scan.succeed
      (Toplevel.keep (Toplevel.theory_of #> (fn thy =>
        Locale.pretty_locale_deps thy
        |> map (fn {name, parents, body} =>
          ((name, Graph_Display.content_node (Locale.extern thy name) [body]), parents))
        |> Graph_Display.display_graph_old))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_term_bindings\<close>
    "print term bindings of proof context"
    (Scan.succeed
      (Toplevel.keep
        (Pretty.writeln_chunks o Proof_Context.pretty_term_bindings o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_facts\<close> "print facts of proof context"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (Proof_Context.print_local_facts b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_cases\<close> "print cases of proof context"
    (Scan.succeed
      (Toplevel.keep (Pretty.writeln_chunks o Proof_Context.pretty_cases o Toplevel.context_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_statement\<close>
    "print theorems as long statements"
    (opt_modes -- Parse.thms1 >> Isar_Cmd.print_stmts);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>thm\<close> "print theorems"
    (opt_modes -- Parse.thms1 >> Isar_Cmd.print_thms);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>prf\<close> "print proof terms of theorems"
    (opt_modes -- Scan.option Parse.thms1 >> Isar_Cmd.print_prfs false);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>full_prf\<close> "print full proof terms of theorems"
    (opt_modes -- Scan.option Parse.thms1 >> Isar_Cmd.print_prfs true);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>prop\<close> "read and print proposition"
    (opt_modes -- Parse.term >> Isar_Cmd.print_prop);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>term\<close> "read and print term"
    (opt_modes -- Parse.term >> Isar_Cmd.print_term);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>typ\<close> "read and print type"
    (opt_modes -- (Parse.typ -- Scan.option (\<^keyword>\<open>::\<close> |-- Parse.!!! Parse.sort))
      >> Isar_Cmd.print_type);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_codesetup\<close> "print code generator setup"
    (Scan.succeed (Toplevel.keep (Code.print_codesetup o Toplevel.theory_of)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_state\<close>
    "print current proof state (if present)"
    (opt_modes >> (fn modes =>
      Toplevel.keep (Print_Mode.with_modes modes (Output.state o Toplevel.string_of_state))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>welcome\<close> "print welcome message"
    (Scan.succeed (Toplevel.keep (fn _ => writeln (Session.welcome ()))));

in end\<close>


subsection \<open>Dependencies\<close>

ML \<open>
local

val theory_bounds =
  Parse.theory_name >> single ||
  (\<^keyword>\<open>(\<close> |-- Parse.enum "|" Parse.theory_name --| \<^keyword>\<open>)\<close>);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>thy_deps\<close> "visualize theory dependencies"
    (Scan.option theory_bounds -- Scan.option theory_bounds >>
      (fn args => Toplevel.keep (fn st => Thy_Deps.thy_deps_cmd (Toplevel.context_of st) args)));


val class_bounds =
  Parse.sort >> single ||
  (\<^keyword>\<open>(\<close> |-- Parse.enum "|" Parse.sort --| \<^keyword>\<open>)\<close>);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>class_deps\<close> "visualize class dependencies"
    (Scan.option class_bounds -- Scan.option class_bounds >> (fn args =>
      Toplevel.keep (fn st => Class_Deps.class_deps_cmd (Toplevel.context_of st) args)));


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>thm_deps\<close>
    "print theorem dependencies (immediate non-transitive)"
    (Parse.thms1 >> (fn args =>
      Toplevel.keep (fn st =>
        let
          val thy = Toplevel.theory_of st;
          val ctxt = Toplevel.context_of st;
        in Pretty.writeln (Thm_Deps.pretty_thm_deps thy (Attrib.eval_thms ctxt args)) end)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>thm_oracles\<close>
    "print all oracles used in theorems (full graph of transitive dependencies)"
    (Parse.thms1 >> (fn args =>
      Toplevel.keep (fn st =>
        let
          val ctxt = Toplevel.context_of st;
          val thms = Attrib.eval_thms ctxt args;
        in Pretty.writeln (Thm_Deps.pretty_thm_oracles ctxt thms) end)));

val thy_names = Scan.repeat1 (Scan.unless Parse.minus Parse.theory_name);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>unused_thms\<close> "find unused theorems"
    (Scan.option ((thy_names --| Parse.minus) -- Scan.option thy_names) >> (fn opt_range =>
        Toplevel.keep (fn st =>
          let
            val thy = Toplevel.theory_of st;
            val ctxt = Toplevel.context_of st;
            fun pretty_thm (a, th) = Proof_Context.pretty_fact ctxt (a, [th]);
            val check = Theory.check {long = false} ctxt;
          in
            Thm_Deps.unused_thms_cmd
              (case opt_range of
                NONE => (Theory.parents_of thy, [thy])
              | SOME (xs, NONE) => (map check xs, [thy])
              | SOME (xs, SOME ys) => (map check xs, map check ys))
            |> map pretty_thm |> Pretty.writeln_chunks
          end)));

in end\<close>


subsubsection \<open>Find consts and theorems\<close>

ML \<open>
local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>find_consts\<close>
    "find constants by name / type patterns"
    (Find_Consts.query_parser >> (fn spec =>
      Toplevel.keep (fn st =>
        Pretty.writeln (Find_Consts.pretty_consts (Toplevel.context_of st) spec))));

val options =
  Scan.optional
    (Parse.$$$ "(" |--
      Parse.!!! (Scan.option Parse.nat --
        Scan.optional (Parse.reserved "with_dups" >> K false) true --| Parse.$$$ ")"))
    (NONE, true);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>find_theorems\<close>
    "find theorems meeting specified criteria"
    (options -- Find_Theorems.query_parser >> (fn ((opt_lim, rem_dups), spec) =>
      Toplevel.keep (fn st =>
        Pretty.writeln
          (Find_Theorems.pretty_theorems (Find_Theorems.proof_state st) opt_lim rem_dups spec))));

in end\<close>


subsection \<open>Code generation\<close>

ML \<open>
local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>code_datatype\<close>
    "define set of code datatype constructors"
    (Scan.repeat1 Parse.term >> (Toplevel.theory o Code.declare_datatype_cmd));

in end\<close>


subsection \<open>Extraction of programs from proofs\<close>

ML \<open>
local

val parse_vars = Scan.optional (Parse.$$$ "(" |-- Parse.list1 Parse.name --| Parse.$$$ ")") [];

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>realizers\<close>
    "specify realizers for primitive axioms / theorems, together with correctness proof"
    (Scan.repeat1 (Parse.name -- parse_vars --| Parse.$$$ ":" -- Parse.string -- Parse.string) >>
     (fn xs => Toplevel.theory (fn thy => Extraction.add_realizers
       (map (fn (((a, vs), s1), s2) => (Global_Theory.get_thm thy a, (vs, s1, s2))) xs) thy)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>realizability\<close>
    "add equations characterizing realizability"
    (Scan.repeat1 Parse.string >> (Toplevel.theory o Extraction.add_realizes_eqns));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>extract_type\<close>
    "add equations characterizing type of extracted program"
    (Scan.repeat1 Parse.string >> (Toplevel.theory o Extraction.add_typeof_eqns));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>extract\<close> "extract terms from proofs"
    (Scan.repeat1 (Parse.name -- parse_vars) >> (fn xs => Toplevel.theory (fn thy =>
      Extraction.extract (map (apfst (Global_Theory.get_thm thy)) xs) thy)));

in end\<close>


section \<open>Auxiliary lemmas\<close>

subsection \<open>Meta-level connectives in assumptions\<close>

lemma meta_mp:
  assumes "PROP P \<Longrightarrow> PROP Q" and "PROP P"
  shows "PROP Q"
    by (rule \<open>PROP P \<Longrightarrow> PROP Q\<close> [OF \<open>PROP P\<close>])

lemmas meta_impE = meta_mp [elim_format]

lemma meta_spec:
  assumes "\<And>x. PROP P x"
  shows "PROP P x"
    by (rule \<open>\<And>x. PROP P x\<close>)

lemmas meta_allE = meta_spec [elim_format]

lemma swap_params:
  "(\<And>x y. PROP P x y) \<equiv> (\<And>y x. PROP P x y)" ..

lemma equal_allI:
  \<open>(\<And>x. PROP P x) \<equiv> (\<And>x. PROP Q x)\<close> if \<open>\<And>x. PROP P x \<equiv> PROP Q x\<close>
  by (simp only: that)


subsection \<open>Meta-level conjunction\<close>

lemma all_conjunction:
  "(\<And>x. PROP A x &&& PROP B x) \<equiv> ((\<And>x. PROP A x) &&& (\<And>x. PROP B x))"
proof
  assume conj: "\<And>x. PROP A x &&& PROP B x"
  show "(\<And>x. PROP A x) &&& (\<And>x. PROP B x)"
  proof -
    fix x
    from conj show "PROP A x" by (rule conjunctionD1)
    from conj show "PROP B x" by (rule conjunctionD2)
  qed
next
  assume conj: "(\<And>x. PROP A x) &&& (\<And>x. PROP B x)"
  fix x
  show "PROP A x &&& PROP B x"
  proof -
    show "PROP A x" by (rule conj [THEN conjunctionD1, rule_format])
    show "PROP B x" by (rule conj [THEN conjunctionD2, rule_format])
  qed
qed

lemma imp_conjunction:
  "(PROP A \<Longrightarrow> PROP B &&& PROP C) \<equiv> ((PROP A \<Longrightarrow> PROP B) &&& (PROP A \<Longrightarrow> PROP C))"
proof
  assume conj: "PROP A \<Longrightarrow> PROP B &&& PROP C"
  show "(PROP A \<Longrightarrow> PROP B) &&& (PROP A \<Longrightarrow> PROP C)"
  proof -
    assume "PROP A"
    from conj [OF \<open>PROP A\<close>] show "PROP B" by (rule conjunctionD1)
    from conj [OF \<open>PROP A\<close>] show "PROP C" by (rule conjunctionD2)
  qed
next
  assume conj: "(PROP A \<Longrightarrow> PROP B) &&& (PROP A \<Longrightarrow> PROP C)"
  assume "PROP A"
  show "PROP B &&& PROP C"
  proof -
    from \<open>PROP A\<close> show "PROP B" by (rule conj [THEN conjunctionD1])
    from \<open>PROP A\<close> show "PROP C" by (rule conj [THEN conjunctionD2])
  qed
qed

lemma conjunction_imp:
  "(PROP A &&& PROP B \<Longrightarrow> PROP C) \<equiv> (PROP A \<Longrightarrow> PROP B \<Longrightarrow> PROP C)"
proof
  assume r: "PROP A &&& PROP B \<Longrightarrow> PROP C"
  assume ab: "PROP A" "PROP B"
  show "PROP C"
  proof (rule r)
    from ab show "PROP A &&& PROP B" .
  qed
next
  assume r: "PROP A \<Longrightarrow> PROP B \<Longrightarrow> PROP C"
  assume conj: "PROP A &&& PROP B"
  show "PROP C"
  proof (rule r)
    from conj show "PROP A" by (rule conjunctionD1)
    from conj show "PROP B" by (rule conjunctionD2)
  qed
qed

declare [[ML_write_global = false]]

end
