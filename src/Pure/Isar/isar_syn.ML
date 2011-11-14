(*  Title:      Pure/Isar/isar_syn.ML
    Author:     Markus Wenzel, TU Muenchen

Isar/Pure outer syntax.
*)

structure Isar_Syn: sig end =
struct

(** keywords **)

(*keep keywords consistent with the parsers, otherwise be prepared for
  unexpected errors*)

val _ = List.app Keyword.keyword
 ["!!", "!", "%", "(", ")", "+", ",", "--", ":", "::", ";", "<", "<=",
  "=", "==", "=>", "?", "[", "\\<equiv>", "\\<leftharpoondown>",
  "\\<rightharpoonup>", "\\<rightleftharpoons>", "\\<subseteq>", "]",
  "advanced", "and", "assumes", "attach", "begin", "binder",
  "constrains", "defines", "fixes", "for", "identifier", "if",
  "imports", "in", "infix", "infixl", "infixr", "is",
  "notes", "obtains", "open", "output", "overloaded", "pervasive",
  "shows", "structure", "unchecked", "uses", "where", "|"];



(** init and exit **)

val _ =
  Outer_Syntax.command "theory" "begin theory" (Keyword.tag_theory Keyword.thy_begin)
    (Thy_Header.args >> (fn (name, imports, uses) =>
      Toplevel.print o
        Toplevel.init_theory
          (fn () =>
            Thy_Info.toplevel_begin_theory (Thy_Load.get_master_path ())
              name imports (map (apfst Path.explode) uses))));

val _ =
  Outer_Syntax.command "end" "end (local) theory" (Keyword.tag_theory Keyword.thy_end)
    (Scan.succeed
      (Toplevel.exit o Toplevel.end_local_theory o Toplevel.end_proof (K Proof.end_notepad)));



(** markup commands **)

val _ = Outer_Syntax.markup_command Thy_Output.Markup "header" "theory header" Keyword.diag
  (Parse.doc_source >> Isar_Cmd.header_markup);

val _ = Outer_Syntax.markup_command Thy_Output.Markup "chapter" "chapter heading"
  Keyword.thy_heading (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ = Outer_Syntax.markup_command Thy_Output.Markup "section" "section heading"
  Keyword.thy_heading (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ = Outer_Syntax.markup_command Thy_Output.Markup "subsection" "subsection heading"
  Keyword.thy_heading (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.Markup "subsubsection" "subsubsection heading"
  Keyword.thy_heading (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ = Outer_Syntax.markup_command Thy_Output.MarkupEnv "text" "formal comment (theory)"
  Keyword.thy_decl (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ = Outer_Syntax.markup_command Thy_Output.Verbatim "text_raw" "raw document preparation text"
  Keyword.thy_decl (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ = Outer_Syntax.markup_command Thy_Output.Markup "sect" "formal comment (proof)"
  (Keyword.tag_proof Keyword.prf_heading) (Parse.doc_source >> Isar_Cmd.proof_markup);

val _ = Outer_Syntax.markup_command Thy_Output.Markup "subsect" "formal comment (proof)"
  (Keyword.tag_proof Keyword.prf_heading) (Parse.doc_source >> Isar_Cmd.proof_markup);

val _ = Outer_Syntax.markup_command Thy_Output.Markup "subsubsect" "formal comment (proof)"
  (Keyword.tag_proof Keyword.prf_heading) (Parse.doc_source >> Isar_Cmd.proof_markup);

val _ = Outer_Syntax.markup_command Thy_Output.MarkupEnv "txt" "formal comment (proof)"
  (Keyword.tag_proof Keyword.prf_decl) (Parse.doc_source >> Isar_Cmd.proof_markup);

val _ = Outer_Syntax.markup_command Thy_Output.Verbatim "txt_raw"
  "raw document preparation text (proof)" (Keyword.tag_proof Keyword.prf_decl)
  (Parse.doc_source >> Isar_Cmd.proof_markup);



(** theory commands **)

(* classes and sorts *)

val _ =
  Outer_Syntax.command "classes" "declare type classes" Keyword.thy_decl
    (Scan.repeat1 (Parse.binding -- Scan.optional ((Parse.$$$ "\\<subseteq>" || Parse.$$$ "<") |--
        Parse.!!! (Parse.list1 Parse.xname)) [])
      >> (Toplevel.theory o fold AxClass.axiomatize_class_cmd));

val _ =
  Outer_Syntax.command "classrel" "state inclusion of type classes (axiomatic!)" Keyword.thy_decl
    (Parse.and_list1 (Parse.xname -- ((Parse.$$$ "\\<subseteq>" || Parse.$$$ "<")
        |-- Parse.!!! Parse.xname))
    >> (Toplevel.theory o AxClass.axiomatize_classrel_cmd));

val _ =
  Outer_Syntax.local_theory "default_sort" "declare default sort for explicit type variables"
    Keyword.thy_decl
    (Parse.sort >> (fn s => fn lthy => Local_Theory.set_defsort (Syntax.read_sort lthy s) lthy));


(* types *)

val _ =
  Outer_Syntax.local_theory "typedecl" "type declaration" Keyword.thy_decl
    (Parse.type_args -- Parse.binding -- Parse.opt_mixfix
      >> (fn ((args, a), mx) => Typedecl.typedecl (a, map (rpair dummyS) args, mx) #> snd));

val type_abbrev =
  Parse.type_args -- Parse.binding --
    (Parse.$$$ "=" |-- Parse.!!! (Parse.typ -- Parse.opt_mixfix'));

val _ =
  Outer_Syntax.local_theory "type_synonym" "declare type abbreviation" Keyword.thy_decl
    (type_abbrev >> (fn ((args, a), (rhs, mx)) => snd o Typedecl.abbrev_cmd (a, args, mx) rhs));

val _ =
  Outer_Syntax.command "nonterminal"
    "declare syntactic type constructors (grammar nonterminal symbols)" Keyword.thy_decl
    (Parse.and_list1 Parse.binding >> (Toplevel.theory o Sign.add_nonterminals_global));

val _ =
  Outer_Syntax.command "arities" "state type arities (axiomatic!)" Keyword.thy_decl
    (Scan.repeat1 Parse.arity >> (Toplevel.theory o fold AxClass.axiomatize_arity_cmd));


(* consts and syntax *)

val _ =
  Outer_Syntax.command "judgment" "declare object-logic judgment" Keyword.thy_decl
    (Parse.const_binding >> (Toplevel.theory o Object_Logic.add_judgment_cmd));

val _ =
  Outer_Syntax.command "consts" "declare constants" Keyword.thy_decl
    (Scan.repeat1 Parse.const_binding >> (Toplevel.theory o Sign.add_consts));

val opt_overloaded = Parse.opt_keyword "overloaded";

val _ =
  Outer_Syntax.command "finalconsts" "declare constants as final" Keyword.thy_decl
    (opt_overloaded -- Scan.repeat1 Parse.term >> (uncurry (Toplevel.theory oo Theory.add_finals)));

val mode_spec =
  (Parse.$$$ "output" >> K ("", false)) ||
    Parse.name -- Scan.optional (Parse.$$$ "output" >> K false) true;

val opt_mode =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (mode_spec --| Parse.$$$ ")")) Syntax.mode_default;

val _ =
  Outer_Syntax.command "syntax" "declare syntactic constants" Keyword.thy_decl
    (opt_mode -- Scan.repeat1 Parse.const_decl >> (Toplevel.theory o uncurry Sign.add_modesyntax));

val _ =
  Outer_Syntax.command "no_syntax" "delete syntax declarations" Keyword.thy_decl
    (opt_mode -- Scan.repeat1 Parse.const_decl >> (Toplevel.theory o uncurry Sign.del_modesyntax));


(* translations *)

val trans_pat =
  Scan.optional
    (Parse.$$$ "(" |-- Parse.!!! (Parse.xname --| Parse.$$$ ")")) "logic"
    -- Parse.inner_syntax Parse.string;

fun trans_arrow toks =
  ((Parse.$$$ "\\<rightharpoonup>" || Parse.$$$ "=>") >> K Syntax.Parse_Rule ||
    (Parse.$$$ "\\<leftharpoondown>" || Parse.$$$ "<=") >> K Syntax.Print_Rule ||
    (Parse.$$$ "\\<rightleftharpoons>" || Parse.$$$ "==") >> K Syntax.Parse_Print_Rule) toks;

val trans_line =
  trans_pat -- Parse.!!! (trans_arrow -- trans_pat)
    >> (fn (left, (arr, right)) => arr (left, right));

val _ =
  Outer_Syntax.command "translations" "declare syntax translation rules" Keyword.thy_decl
    (Scan.repeat1 trans_line >> (Toplevel.theory o Isar_Cmd.translations));

val _ =
  Outer_Syntax.command "no_translations" "remove syntax translation rules" Keyword.thy_decl
    (Scan.repeat1 trans_line >> (Toplevel.theory o Isar_Cmd.no_translations));


(* axioms and definitions *)

val _ =
  Outer_Syntax.command "axioms" "state arbitrary propositions (axiomatic!)" Keyword.thy_decl
    (Scan.repeat1 Parse_Spec.spec >>
      (fn spec => Toplevel.theory (fn thy =>
        (legacy_feature "Old 'axioms' command -- use 'axiomatization' instead";
          Isar_Cmd.add_axioms spec thy))));

val opt_unchecked_overloaded =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!!
    (((Parse.$$$ "unchecked" >> K true) -- Scan.optional (Parse.$$$ "overloaded" >> K true) false ||
      Parse.$$$ "overloaded" >> K (false, true)) --| Parse.$$$ ")")) (false, false);

val _ =
  Outer_Syntax.command "defs" "define constants" Keyword.thy_decl
    (opt_unchecked_overloaded --
      Scan.repeat1 (Parse_Spec.thm_name ":" -- Parse.prop >> (fn ((x, y), z) => ((x, z), y)))
      >> (Toplevel.theory o Isar_Cmd.add_defs));


(* constant definitions and abbreviations *)

val _ =
  Outer_Syntax.local_theory' "definition" "constant definition" Keyword.thy_decl
    (Parse_Spec.constdef >> (fn args => #2 oo Specification.definition_cmd args));

val _ =
  Outer_Syntax.local_theory' "abbreviation" "constant abbreviation" Keyword.thy_decl
    (opt_mode -- (Scan.option Parse_Spec.constdecl -- Parse.prop)
      >> (fn (mode, args) => Specification.abbreviation_cmd mode args));

val _ =
  Outer_Syntax.local_theory "type_notation" "add concrete syntax for type constructors"
    Keyword.thy_decl
    (opt_mode -- Parse.and_list1 (Parse.type_const -- Parse.mixfix)
      >> (fn (mode, args) => Specification.type_notation_cmd true mode args));

val _ =
  Outer_Syntax.local_theory "no_type_notation" "delete concrete syntax for type constructors"
    Keyword.thy_decl
    (opt_mode -- Parse.and_list1 (Parse.type_const -- Parse.mixfix)
      >> (fn (mode, args) => Specification.type_notation_cmd false mode args));

val _ =
  Outer_Syntax.local_theory "notation" "add concrete syntax for constants / fixed variables"
    Keyword.thy_decl
    (opt_mode -- Parse.and_list1 (Parse.const -- Parse_Spec.locale_mixfix)
      >> (fn (mode, args) => Specification.notation_cmd true mode args));

val _ =
  Outer_Syntax.local_theory "no_notation" "delete concrete syntax for constants / fixed variables"
    Keyword.thy_decl
    (opt_mode -- Parse.and_list1 (Parse.const -- Parse_Spec.locale_mixfix)
      >> (fn (mode, args) => Specification.notation_cmd false mode args));


(* constant specifications *)

val _ =
  Outer_Syntax.command "axiomatization" "axiomatic constant specification" Keyword.thy_decl
    (Scan.optional Parse.fixes [] --
      Scan.optional (Parse.where_ |-- Parse.!!! (Parse.and_list1 Parse_Spec.specs)) []
      >> (fn (x, y) => Toplevel.theory (#2 o Specification.axiomatization_cmd x y)));


(* theorems *)

fun theorems kind =
  Parse_Spec.name_facts >> (fn args => #2 oo Specification.theorems_cmd kind args);

val _ =
  Outer_Syntax.local_theory' "theorems" "define theorems" Keyword.thy_decl (theorems Thm.theoremK);

val _ =
  Outer_Syntax.local_theory' "lemmas" "define lemmas" Keyword.thy_decl (theorems Thm.lemmaK);

val _ =
  Outer_Syntax.local_theory' "declare" "declare theorems" Keyword.thy_decl
    (Parse.and_list1 Parse_Spec.xthms1
      >> (fn args => #2 oo Specification.theorems_cmd "" [(Attrib.empty_binding, flat args)]));


(* name space entry path *)

fun hide_names name hide what =
  Outer_Syntax.command name ("hide " ^ what ^ " from name space") Keyword.thy_decl
    ((Parse.opt_keyword "open" >> not) -- Scan.repeat1 Parse.xname >>
      (Toplevel.theory o uncurry hide));

val _ = hide_names "hide_class" Isar_Cmd.hide_class "classes";
val _ = hide_names "hide_type" Isar_Cmd.hide_type "types";
val _ = hide_names "hide_const" Isar_Cmd.hide_const "constants";
val _ = hide_names "hide_fact" Isar_Cmd.hide_fact "facts";


(* use ML text *)

val _ =
  Outer_Syntax.command "use" "ML text from file" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.path >> (fn path => Toplevel.generic_theory (Thy_Load.exec_ml path)));

val _ =
  Outer_Syntax.command "ML" "ML text within theory or local theory"
    (Keyword.tag_ml Keyword.thy_decl)
    (Parse.ML_source >> (fn (txt, pos) =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () => ML_Context.eval_text true pos txt) #>
          Local_Theory.propagate_ml_env)));

val _ =
  Outer_Syntax.command "ML_prf" "ML text within proof" (Keyword.tag_proof Keyword.prf_decl)
    (Parse.ML_source >> (fn (txt, pos) =>
      Toplevel.proof (Proof.map_context (Context.proof_map
        (ML_Context.exec (fn () => ML_Context.eval_text true pos txt))) #> Proof.propagate_ml_env)));

val _ =
  Outer_Syntax.command "ML_val" "diagnostic ML text" (Keyword.tag_ml Keyword.diag)
    (Parse.ML_source >> Isar_Cmd.ml_diag true);

val _ =
  Outer_Syntax.command "ML_command" "diagnostic ML text (silent)" (Keyword.tag_ml Keyword.diag)
    (Parse.ML_source >> (Toplevel.no_timing oo Isar_Cmd.ml_diag false));

val _ =
  Outer_Syntax.command "setup" "ML theory setup" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.ML_source >> (Toplevel.theory o Isar_Cmd.global_setup));

val _ =
  Outer_Syntax.local_theory "local_setup" "ML local theory setup" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.ML_source >> Isar_Cmd.local_setup);

val _ =
  Outer_Syntax.command "attribute_setup" "define attribute in ML" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.position Parse.name --
        Parse.!!! (Parse.$$$ "=" |-- Parse.ML_source -- Scan.optional Parse.text "")
      >> (fn (name, (txt, cmt)) => Toplevel.theory (Attrib.attribute_setup name txt cmt)));

val _ =
  Outer_Syntax.command "method_setup" "define proof method in ML" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.position Parse.name --
        Parse.!!! (Parse.$$$ "=" |-- Parse.ML_source -- Scan.optional Parse.text "")
      >> (fn (name, (txt, cmt)) => Toplevel.theory (Method.method_setup name txt cmt)));

val _ =
  Outer_Syntax.local_theory "declaration" "generic ML declaration"
    (Keyword.tag_ml Keyword.thy_decl)
    (Parse.opt_keyword "pervasive" -- Parse.ML_source
      >> (fn (pervasive, txt) => Isar_Cmd.declaration {syntax = false, pervasive = pervasive} txt));

val _ =
  Outer_Syntax.local_theory "syntax_declaration" "generic ML declaration"
    (Keyword.tag_ml Keyword.thy_decl)
    (Parse.opt_keyword "pervasive" -- Parse.ML_source
      >> (fn (pervasive, txt) => Isar_Cmd.declaration {syntax = true, pervasive = pervasive} txt));

val _ =
  Outer_Syntax.local_theory "simproc_setup" "define simproc in ML" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.position Parse.name --
      (Parse.$$$ "(" |-- Parse.enum1 "|" Parse.term --| Parse.$$$ ")" --| Parse.$$$ "=") --
      Parse.ML_source -- Scan.optional (Parse.$$$ "identifier" |-- Scan.repeat1 Parse.xname) []
    >> (fn (((a, b), c), d) => Isar_Cmd.simproc_setup a b c d));


(* translation functions *)

val trfun = Parse.opt_keyword "advanced" -- Parse.ML_source;

val _ =
  Outer_Syntax.command "parse_ast_translation" "install parse ast translation functions"
    (Keyword.tag_ml Keyword.thy_decl)
    (trfun >> (Toplevel.theory o Isar_Cmd.parse_ast_translation));

val _ =
  Outer_Syntax.command "parse_translation" "install parse translation functions"
    (Keyword.tag_ml Keyword.thy_decl)
    (trfun >> (Toplevel.theory o Isar_Cmd.parse_translation));

val _ =
  Outer_Syntax.command "print_translation" "install print translation functions"
    (Keyword.tag_ml Keyword.thy_decl)
    (trfun >> (Toplevel.theory o Isar_Cmd.print_translation));

val _ =
  Outer_Syntax.command "typed_print_translation" "install typed print translation functions"
    (Keyword.tag_ml Keyword.thy_decl)
    (trfun >> (Toplevel.theory o Isar_Cmd.typed_print_translation));

val _ =
  Outer_Syntax.command "print_ast_translation" "install print ast translation functions"
    (Keyword.tag_ml Keyword.thy_decl)
    (trfun >> (Toplevel.theory o Isar_Cmd.print_ast_translation));


(* oracles *)

val _ =
  Outer_Syntax.command "oracle" "declare oracle" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.position Parse.name -- (Parse.$$$ "=" |-- Parse.ML_source) >>
      (fn (x, y) => Toplevel.theory (Isar_Cmd.oracle x y)));


(* local theories *)

val _ =
  Outer_Syntax.command "context" "enter local theory context" Keyword.thy_decl
    (Parse.position Parse.name --| Parse.begin >> (fn name =>
      Toplevel.print o Toplevel.begin_local_theory true (Named_Target.context_cmd name)));


(* locales *)

val locale_val =
  Parse_Spec.locale_expression false --
    Scan.optional (Parse.$$$ "+" |-- Parse.!!! (Scan.repeat1 Parse_Spec.context_element)) [] ||
  Scan.repeat1 Parse_Spec.context_element >> pair ([], []);

val _ =
  Outer_Syntax.command "locale" "define named proof context" Keyword.thy_decl
    (Parse.binding --
      Scan.optional (Parse.$$$ "=" |-- Parse.!!! locale_val) (([], []), []) -- Parse.opt_begin
      >> (fn ((name, (expr, elems)), begin) =>
          (begin ? Toplevel.print) o Toplevel.begin_local_theory begin
            (Expression.add_locale_cmd I name Binding.empty expr elems #> snd)));

fun parse_interpretation_arguments mandatory =
  Parse.!!! (Parse_Spec.locale_expression mandatory) --
    Scan.optional
      (Parse.where_ |-- Parse.and_list1 (Parse_Spec.opt_thm_name ":" -- Parse.prop)) [];

val _ =
  Outer_Syntax.command "sublocale"
    "prove sublocale relation between a locale and a locale expression" Keyword.thy_goal
    (Parse.xname --| (Parse.$$$ "\\<subseteq>" || Parse.$$$ "<") --
      parse_interpretation_arguments false
      >> (fn (loc, (expr, equations)) =>
          Toplevel.print o Toplevel.theory_to_proof (Expression.sublocale_cmd I loc expr equations)));

val _ =
  Outer_Syntax.command "interpretation"
    "prove interpretation of locale expression in theory" Keyword.thy_goal
    (parse_interpretation_arguments true
      >> (fn (expr, equations) => Toplevel.print o
          Toplevel.theory_to_proof (Expression.interpretation_cmd expr equations)));

val _ =
  Outer_Syntax.command "interpret"
    "prove interpretation of locale expression in proof context"
    (Keyword.tag_proof Keyword.prf_goal)
    (parse_interpretation_arguments true
      >> (fn (expr, equations) => Toplevel.print o
          Toplevel.proof' (Expression.interpret_cmd expr equations)));


(* classes *)

val class_val =
  Parse_Spec.class_expr --
    Scan.optional (Parse.$$$ "+" |-- Parse.!!! (Scan.repeat1 Parse_Spec.context_element)) [] ||
  Scan.repeat1 Parse_Spec.context_element >> pair [];

val _ =
  Outer_Syntax.command "class" "define type class" Keyword.thy_decl
   (Parse.binding -- Scan.optional (Parse.$$$ "=" |-- class_val) ([], []) -- Parse.opt_begin
    >> (fn ((name, (supclasses, elems)), begin) =>
        (begin ? Toplevel.print) o Toplevel.begin_local_theory begin
          (Class_Declaration.class_cmd I name supclasses elems #> snd)));

val _ =
  Outer_Syntax.local_theory_to_proof "subclass" "prove a subclass relation" Keyword.thy_goal
    (Parse.xname >> Class_Declaration.subclass_cmd I);

val _ =
  Outer_Syntax.command "instantiation" "instantiate and prove type arity" Keyword.thy_decl
   (Parse.multi_arity --| Parse.begin
     >> (fn arities => Toplevel.print o
         Toplevel.begin_local_theory true (Class.instantiation_cmd arities)));

val _ =
  Outer_Syntax.command "instance" "prove type arity or subclass relation" Keyword.thy_goal
  ((Parse.xname -- ((Parse.$$$ "\\<subseteq>" || Parse.$$$ "<") |-- Parse.!!! Parse.xname)
        >> Class.classrel_cmd ||
    Parse.multi_arity >> Class.instance_arity_cmd)
    >> (Toplevel.print oo Toplevel.theory_to_proof) ||
    Scan.succeed
      (Toplevel.print o Toplevel.local_theory_to_proof NONE (Class.instantiation_instance I)));


(* arbitrary overloading *)

val _ =
  Outer_Syntax.command "overloading" "overloaded definitions" Keyword.thy_decl
   (Scan.repeat1 (Parse.name --| (Parse.$$$ "\\<equiv>" || Parse.$$$ "==") -- Parse.term --
      Scan.optional (Parse.$$$ "(" |-- (Parse.$$$ "unchecked" >> K false) --| Parse.$$$ ")") true
      >> Parse.triple1) --| Parse.begin
   >> (fn operations => Toplevel.print o
         Toplevel.begin_local_theory true (Overloading.overloading_cmd operations)));


(* code generation *)

val _ =
  Outer_Syntax.command "code_datatype" "define set of code datatype constructors" Keyword.thy_decl
    (Scan.repeat1 Parse.term >> (Toplevel.theory o Code.add_datatype_cmd));



(** proof commands **)

(* statements *)

fun gen_theorem schematic kind =
  Outer_Syntax.local_theory_to_proof'
    (if schematic then "schematic_" ^ kind else kind)
    ("state " ^ (if schematic then "schematic " ^ kind else kind))
    (if schematic then Keyword.thy_schematic_goal else Keyword.thy_goal)
    (Scan.optional (Parse_Spec.opt_thm_name ":" --|
      Scan.ahead (Parse_Spec.locale_keyword || Parse_Spec.statement_keyword)) Attrib.empty_binding --
      Parse_Spec.general_statement >> (fn (a, (elems, concl)) =>
        ((if schematic then Specification.schematic_theorem_cmd else Specification.theorem_cmd)
          kind NONE (K I) a elems concl)));

val _ = gen_theorem false Thm.theoremK;
val _ = gen_theorem false Thm.lemmaK;
val _ = gen_theorem false Thm.corollaryK;
val _ = gen_theorem true Thm.theoremK;
val _ = gen_theorem true Thm.lemmaK;
val _ = gen_theorem true Thm.corollaryK;

val _ =
  Outer_Syntax.local_theory_to_proof "notepad"
    "Isar proof state as formal notepad, without any result" Keyword.thy_decl
    (Parse.begin >> K Proof.begin_notepad);

val _ =
  Outer_Syntax.command "have" "state local goal"
    (Keyword.tag_proof Keyword.prf_goal)
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o Isar_Cmd.have));

val _ =
  Outer_Syntax.command "hence" "abbreviates \"then have\""
    (Keyword.tag_proof Keyword.prf_goal)
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o Isar_Cmd.hence));

val _ =
  Outer_Syntax.command "show" "state local goal, solving current obligation"
    (Keyword.tag_proof Keyword.prf_asm_goal)
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o Isar_Cmd.show));

val _ =
  Outer_Syntax.command "thus" "abbreviates \"then show\""
    (Keyword.tag_proof Keyword.prf_asm_goal)
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o Isar_Cmd.thus));


(* facts *)

val facts = Parse.and_list1 Parse_Spec.xthms1;

val _ =
  Outer_Syntax.command "then" "forward chaining"
    (Keyword.tag_proof Keyword.prf_chain)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.chain));

val _ =
  Outer_Syntax.command "from" "forward chaining from given facts"
    (Keyword.tag_proof Keyword.prf_chain)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.from_thmss_cmd)));

val _ =
  Outer_Syntax.command "with" "forward chaining from given and current facts"
    (Keyword.tag_proof Keyword.prf_chain)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.with_thmss_cmd)));

val _ =
  Outer_Syntax.command "note" "define facts"
    (Keyword.tag_proof Keyword.prf_decl)
    (Parse_Spec.name_facts >> (Toplevel.print oo (Toplevel.proof o Proof.note_thmss_cmd)));

val _ =
  Outer_Syntax.command "using" "augment goal facts"
    (Keyword.tag_proof Keyword.prf_decl)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.using_cmd)));

val _ =
  Outer_Syntax.command "unfolding" "unfold definitions in goal and facts"
    (Keyword.tag_proof Keyword.prf_decl)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.unfolding_cmd)));


(* proof context *)

val _ =
  Outer_Syntax.command "fix" "fix local variables (Skolem constants)"
    (Keyword.tag_proof Keyword.prf_asm)
    (Parse.fixes >> (Toplevel.print oo (Toplevel.proof o Proof.fix_cmd)));

val _ =
  Outer_Syntax.command "assume" "assume propositions"
    (Keyword.tag_proof Keyword.prf_asm)
    (Parse_Spec.statement >> (Toplevel.print oo (Toplevel.proof o Proof.assume_cmd)));

val _ =
  Outer_Syntax.command "presume" "assume propositions, to be established later"
    (Keyword.tag_proof Keyword.prf_asm)
    (Parse_Spec.statement >> (Toplevel.print oo (Toplevel.proof o Proof.presume_cmd)));

val _ =
  Outer_Syntax.command "def" "local definition"
    (Keyword.tag_proof Keyword.prf_asm)
    (Parse.and_list1
      (Parse_Spec.opt_thm_name ":" --
        ((Parse.binding -- Parse.opt_mixfix) --
          ((Parse.$$$ "\\<equiv>" || Parse.$$$ "==") |-- Parse.!!! Parse.termp)))
    >> (Toplevel.print oo (Toplevel.proof o Proof.def_cmd)));

val _ =
  Outer_Syntax.command "obtain" "generalized existence"
    (Keyword.tag_proof Keyword.prf_asm_goal)
    (Parse.parname -- Scan.optional (Parse.fixes --| Parse.where_) [] -- Parse_Spec.statement
      >> (fn ((x, y), z) => Toplevel.print o Toplevel.proof' (Obtain.obtain_cmd x y z)));

val _ =
  Outer_Syntax.command "guess" "wild guessing (unstructured)"
    (Keyword.tag_proof Keyword.prf_asm_goal)
    (Scan.optional Parse.fixes [] >> (Toplevel.print oo (Toplevel.proof' o Obtain.guess_cmd)));

val _ =
  Outer_Syntax.command "let" "bind text variables"
    (Keyword.tag_proof Keyword.prf_decl)
    (Parse.and_list1 (Parse.and_list1 Parse.term -- (Parse.$$$ "=" |-- Parse.term))
      >> (Toplevel.print oo (Toplevel.proof o Proof.let_bind_cmd)));

val _ =
  Outer_Syntax.command "write" "add concrete syntax for constants / fixed variables"
    (Keyword.tag_proof Keyword.prf_decl)
    (opt_mode -- Parse.and_list1 (Parse.const -- Parse_Spec.locale_mixfix)
    >> (fn (mode, args) => Toplevel.print o Toplevel.proof (Proof.write_cmd mode args)));

val case_spec =
  (Parse.$$$ "(" |--
    Parse.!!! (Parse.xname -- Scan.repeat1 (Parse.maybe Parse.binding) --| Parse.$$$ ")") ||
    Parse.xname >> rpair []) -- Parse_Spec.opt_attribs >> Parse.triple1;

val _ =
  Outer_Syntax.command "case" "invoke local context"
    (Keyword.tag_proof Keyword.prf_asm)
    (case_spec >> (Toplevel.print oo (Toplevel.proof o Proof.invoke_case_cmd)));


(* proof structure *)

val _ =
  Outer_Syntax.command "{" "begin explicit proof block"
    (Keyword.tag_proof Keyword.prf_open)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.begin_block));

val _ =
  Outer_Syntax.command "}" "end explicit proof block"
    (Keyword.tag_proof Keyword.prf_close)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.end_block));

val _ =
  Outer_Syntax.command "next" "enter next proof block"
    (Keyword.tag_proof Keyword.prf_block)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.next_block));


(* end proof *)

val _ =
  Outer_Syntax.command "qed" "conclude (sub-)proof"
    (Keyword.tag_proof Keyword.qed_block)
    (Scan.option Method.parse >> Isar_Cmd.qed);

val _ =
  Outer_Syntax.command "by" "terminal backward proof"
    (Keyword.tag_proof Keyword.qed)
    (Method.parse -- Scan.option Method.parse >> Isar_Cmd.terminal_proof);

val _ =
  Outer_Syntax.command ".." "default proof"
    (Keyword.tag_proof Keyword.qed)
    (Scan.succeed Isar_Cmd.default_proof);

val _ =
  Outer_Syntax.command "." "immediate proof"
    (Keyword.tag_proof Keyword.qed)
    (Scan.succeed Isar_Cmd.immediate_proof);

val _ =
  Outer_Syntax.command "done" "done proof"
    (Keyword.tag_proof Keyword.qed)
    (Scan.succeed Isar_Cmd.done_proof);

val _ =
  Outer_Syntax.command "sorry" "skip proof (quick-and-dirty mode only!)"
    (Keyword.tag_proof Keyword.qed)
    (Scan.succeed Isar_Cmd.skip_proof);

val _ =
  Outer_Syntax.command "oops" "forget proof"
    (Keyword.tag_proof Keyword.qed_global)
    (Scan.succeed Toplevel.forget_proof);


(* proof steps *)

val _ =
  Outer_Syntax.command "defer" "shuffle internal proof state"
    (Keyword.tag_proof Keyword.prf_script)
    (Scan.option Parse.nat >> (Toplevel.print oo (Toplevel.proofs o Proof.defer)));

val _ =
  Outer_Syntax.command "prefer" "shuffle internal proof state"
    (Keyword.tag_proof Keyword.prf_script)
    (Parse.nat >> (Toplevel.print oo (Toplevel.proofs o Proof.prefer)));

val _ =
  Outer_Syntax.command "apply" "initial refinement step (unstructured)"
    (Keyword.tag_proof Keyword.prf_script)
    (Method.parse >> (Toplevel.print oo (Toplevel.proofs o Proof.apply)));

val _ =
  Outer_Syntax.command "apply_end" "terminal refinement (unstructured)"
    (Keyword.tag_proof Keyword.prf_script)
    (Method.parse >> (Toplevel.print oo (Toplevel.proofs o Proof.apply_end)));

val _ =
  Outer_Syntax.command "proof" "backward proof"
    (Keyword.tag_proof Keyword.prf_block)
    (Scan.option Method.parse >> (fn m => Toplevel.print o
      Toplevel.actual_proof (Proof_Node.applys (Proof.proof m)) o
      Toplevel.skip_proof (fn i => i + 1)));


(* calculational proof commands *)

val calc_args =
  Scan.option (Parse.$$$ "(" |-- Parse.!!! ((Parse_Spec.xthms1 --| Parse.$$$ ")")));

val _ =
  Outer_Syntax.command "also" "combine calculation and current facts"
    (Keyword.tag_proof Keyword.prf_decl)
    (calc_args >> (Toplevel.proofs' o Calculation.also_cmd));

val _ =
  Outer_Syntax.command "finally" "combine calculation and current facts, exhibit result"
    (Keyword.tag_proof Keyword.prf_chain)
    (calc_args >> (Toplevel.proofs' o Calculation.finally_cmd));

val _ =
  Outer_Syntax.command "moreover" "augment calculation by current facts"
    (Keyword.tag_proof Keyword.prf_decl)
    (Scan.succeed (Toplevel.proof' Calculation.moreover));

val _ =
  Outer_Syntax.command "ultimately" "augment calculation by current facts, exhibit result"
    (Keyword.tag_proof Keyword.prf_chain)
    (Scan.succeed (Toplevel.proof' Calculation.ultimately));


(* proof navigation *)

val _ =
  Outer_Syntax.command "back" "backtracking of proof command"
    (Keyword.tag_proof Keyword.prf_script)
    (Scan.succeed (Toplevel.print o Toplevel.actual_proof Proof_Node.back o Toplevel.skip_proof I));


(* nested commands *)

val props_text =
  Scan.optional Parse.properties [] -- Parse.position Parse.string
  >> (fn (props, (str, pos)) =>
      (Position.of_properties (Position.default_properties pos props), str));

val _ =
  Outer_Syntax.improper_command "Isabelle.command" "nested Isabelle command" Keyword.control
    (props_text :|-- (fn (pos, str) =>
      (case Outer_Syntax.parse pos str of
        [tr] => Scan.succeed (K tr)
      | _ => Scan.fail_with (K (fn () => "exactly one command expected")))
      handle ERROR msg => Scan.fail_with (K (fn () => msg))));



(** diagnostic commands (for interactive mode only) **)

val opt_modes =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.xname --| Parse.$$$ ")")) [];

val opt_bang = Scan.optional (Parse.$$$ "!" >> K true) false;

val _ =
  Outer_Syntax.improper_command "pretty_setmargin" "change default margin for pretty printing"
    Keyword.diag (Parse.nat >>
      (fn n => Toplevel.no_timing o Toplevel.imperative (fn () => Pretty.margin_default := n)));

val _ =
  Outer_Syntax.improper_command "help" "print outer syntax commands" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative Outer_Syntax.print_outer_syntax));

val _ =
  Outer_Syntax.improper_command "print_commands" "print outer syntax commands" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative Outer_Syntax.print_outer_syntax));

val _ =
  Outer_Syntax.improper_command "print_configs" "print configuration options" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_configs));

val _ =
  Outer_Syntax.improper_command "print_context" "print theory context name" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_context));

val _ =
  Outer_Syntax.improper_command "print_theory" "print logical theory contents (verbose!)"
    Keyword.diag (opt_bang >> (Toplevel.no_timing oo Isar_Cmd.print_theory));

val _ =
  Outer_Syntax.improper_command "print_syntax" "print inner syntax of context (verbose!)"
    Keyword.diag (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_syntax));

val _ =
  Outer_Syntax.improper_command "print_abbrevs" "print constant abbreviation of context"
    Keyword.diag (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_abbrevs));

val _ =
  Outer_Syntax.improper_command "print_theorems"
      "print theorems of local theory or proof context" Keyword.diag
    (opt_bang >> (Toplevel.no_timing oo Isar_Cmd.print_theorems));

val _ =
  Outer_Syntax.improper_command "print_locales" "print locales of this theory" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_locales));

val _ =
  Outer_Syntax.improper_command "print_classes" "print classes of this theory" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_theory o
      Toplevel.keep (Class.print_classes o Toplevel.context_of)));

val _ =
  Outer_Syntax.improper_command "print_locale" "print locale of this theory" Keyword.diag
    (opt_bang -- Parse.xname >> (Toplevel.no_timing oo Isar_Cmd.print_locale));

val _ =
  Outer_Syntax.improper_command "print_interps"
    "print interpretations of locale for this theory or proof context" Keyword.diag
    (Parse.xname >> (Toplevel.no_timing oo Isar_Cmd.print_registrations));

val _ =
  Outer_Syntax.improper_command "print_dependencies"
    "print dependencies of locale expression" Keyword.diag
    (opt_bang -- Parse_Spec.locale_expression true >>
      (Toplevel.no_timing oo Isar_Cmd.print_dependencies));

val _ =
  Outer_Syntax.improper_command "print_attributes" "print attributes of this theory" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_attributes));

val _ =
  Outer_Syntax.improper_command "print_simpset" "print context of Simplifier" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_simpset));

val _ =
  Outer_Syntax.improper_command "print_rules" "print intro/elim rules" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_rules));

val _ =
  Outer_Syntax.improper_command "print_trans_rules" "print transitivity rules" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_trans_rules));

val _ =
  Outer_Syntax.improper_command "print_methods" "print methods of this theory" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_methods));

val _ =
  Outer_Syntax.improper_command "print_antiquotations" "print antiquotations (global)" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_antiquotations));

val _ =
  Outer_Syntax.improper_command "thy_deps" "visualize theory dependencies"
    Keyword.diag (Scan.succeed (Toplevel.no_timing o Isar_Cmd.thy_deps));

val _ =
  Outer_Syntax.improper_command "class_deps" "visualize class dependencies"
    Keyword.diag (Scan.succeed (Toplevel.no_timing o Isar_Cmd.class_deps));

val _ =
  Outer_Syntax.improper_command "thm_deps" "visualize theorem dependencies"
    Keyword.diag (Parse_Spec.xthms1 >> (Toplevel.no_timing oo Isar_Cmd.thm_deps));

val _ =
  Outer_Syntax.improper_command "print_binds" "print term bindings of proof context" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_binds));

val _ =
  Outer_Syntax.improper_command "print_facts" "print facts of proof context" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_facts));

val _ =
  Outer_Syntax.improper_command "print_cases" "print cases of proof context" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_cases));

val _ =
  Outer_Syntax.improper_command "print_statement" "print theorems as long statements" Keyword.diag
    (opt_modes -- Parse_Spec.xthms1 >> (Toplevel.no_timing oo Isar_Cmd.print_stmts));

val _ =
  Outer_Syntax.improper_command "thm" "print theorems" Keyword.diag
    (opt_modes -- Parse_Spec.xthms1 >> (Toplevel.no_timing oo Isar_Cmd.print_thms));

val _ =
  Outer_Syntax.improper_command "prf" "print proof terms of theorems" Keyword.diag
    (opt_modes -- Scan.option Parse_Spec.xthms1
      >> (Toplevel.no_timing oo Isar_Cmd.print_prfs false));

val _ =
  Outer_Syntax.improper_command "full_prf" "print full proof terms of theorems" Keyword.diag
    (opt_modes -- Scan.option Parse_Spec.xthms1 >> (Toplevel.no_timing oo Isar_Cmd.print_prfs true));

val _ =
  Outer_Syntax.improper_command "prop" "read and print proposition" Keyword.diag
    (opt_modes -- Parse.term >> (Toplevel.no_timing oo Isar_Cmd.print_prop));

val _ =
  Outer_Syntax.improper_command "term" "read and print term" Keyword.diag
    (opt_modes -- Parse.term >> (Toplevel.no_timing oo Isar_Cmd.print_term));

val _ =
  Outer_Syntax.improper_command "typ" "read and print type" Keyword.diag
    (opt_modes -- Parse.typ >> (Toplevel.no_timing oo Isar_Cmd.print_type));

val _ =
  Outer_Syntax.improper_command "print_codesetup" "print code generator setup" Keyword.diag
    (Scan.succeed
      (Toplevel.no_timing o Toplevel.unknown_theory o Toplevel.keep
        (Code.print_codesetup o Toplevel.theory_of)));

val _ =
  Outer_Syntax.improper_command "unused_thms" "find unused theorems" Keyword.diag
    (Scan.option ((Scan.repeat1 (Scan.unless Parse.minus Parse.name) --| Parse.minus) --
       Scan.option (Scan.repeat1 (Scan.unless Parse.minus Parse.name))) >>
         (Toplevel.no_timing oo Isar_Cmd.unused_thms));



(** system commands (for interactive mode only) **)

val _ =
  Outer_Syntax.improper_command "cd" "change current working directory" Keyword.control
    (Parse.path >> (fn path => Toplevel.no_timing o Toplevel.imperative (fn () => File.cd path)));

val _ =
  Outer_Syntax.improper_command "pwd" "print current working directory" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o
      Toplevel.imperative (fn () => writeln (Path.print (File.pwd ())))));

val _ =
  Outer_Syntax.improper_command "use_thy" "use theory file" Keyword.control
    (Parse.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => Thy_Info.use_thy name)));

val _ =
  Outer_Syntax.improper_command "remove_thy" "remove theory from loader database" Keyword.control
    (Parse.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => Thy_Info.remove_thy name)));

val _ =
  Outer_Syntax.improper_command "kill_thy" "kill theory -- try to remove from loader database"
    Keyword.control (Parse.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => Thy_Info.kill_thy name)));

val _ =
  Outer_Syntax.improper_command "display_drafts" "display raw source files with symbols"
    Keyword.diag (Scan.repeat1 Parse.path >> (Toplevel.no_timing oo Isar_Cmd.display_drafts));

val _ =
  Outer_Syntax.improper_command "print_drafts" "print raw source files with symbols"
    Keyword.diag (Scan.repeat1 Parse.path >> (Toplevel.no_timing oo Isar_Cmd.print_drafts));

val _ =  (* FIXME tty only *)
  Outer_Syntax.improper_command "pr" "print current proof state (if present)" Keyword.diag
    (opt_modes -- Scan.option Parse.nat >> (fn (modes, limit) =>
      Toplevel.no_timing o Toplevel.keep (fn state =>
       (case limit of NONE => () | SOME n => Goal_Display.goals_limit_default := n;
        Toplevel.quiet := false;
        Print_Mode.with_modes modes (Toplevel.print_state true) state))));

val _ =
  Outer_Syntax.improper_command "disable_pr" "disable printing of toplevel state" Keyword.control
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative (fn () => Toplevel.quiet := true)));

val _ =
  Outer_Syntax.improper_command "enable_pr" "enable printing of toplevel state" Keyword.control
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative (fn () => Toplevel.quiet := false)));

val _ =
  Outer_Syntax.improper_command "commit" "commit current session to ML database" Keyword.control
    (Parse.opt_unit >> K (Toplevel.no_timing o Toplevel.imperative Secure.commit));

val _ =
  Outer_Syntax.improper_command "quit" "quit Isabelle" Keyword.control
    (Parse.opt_unit >> (Toplevel.no_timing oo K (Toplevel.imperative quit)));

val _ =
  Outer_Syntax.improper_command "exit" "exit Isar loop" Keyword.control
    (Scan.succeed
      (Toplevel.no_timing o Toplevel.keep (fn state =>
        (Context.set_thread_data (try Toplevel.generic_theory_of state);
          raise Runtime.TERMINATE))));

end;

