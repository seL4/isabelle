(*  Title:      Pure/Isar/isar_syn.ML
    Author:     Markus Wenzel, TU Muenchen

Isar/Pure outer syntax.
*)

structure IsarSyn: sig end =
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
  OuterSyntax.command "theory" "begin theory" (Keyword.tag_theory Keyword.thy_begin)
    (Thy_Header.args >> (Toplevel.print oo IsarCmd.init_theory));

val _ =
  OuterSyntax.command "end" "end (local) theory" (Keyword.tag_theory Keyword.thy_end)
    (Scan.succeed (Toplevel.exit o Toplevel.end_local_theory));



(** markup commands **)

val _ = OuterSyntax.markup_command ThyOutput.Markup "header" "theory header" Keyword.diag
  (Parse.doc_source >> IsarCmd.header_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "chapter" "chapter heading"
  Keyword.thy_heading (Parse.opt_target -- Parse.doc_source >> IsarCmd.local_theory_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "section" "section heading"
  Keyword.thy_heading (Parse.opt_target -- Parse.doc_source >> IsarCmd.local_theory_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "subsection" "subsection heading"
  Keyword.thy_heading (Parse.opt_target -- Parse.doc_source >> IsarCmd.local_theory_markup);

val _ =
  OuterSyntax.markup_command ThyOutput.Markup "subsubsection" "subsubsection heading"
  Keyword.thy_heading (Parse.opt_target -- Parse.doc_source >> IsarCmd.local_theory_markup);

val _ = OuterSyntax.markup_command ThyOutput.MarkupEnv "text" "formal comment (theory)"
  Keyword.thy_decl (Parse.opt_target -- Parse.doc_source >> IsarCmd.local_theory_markup);

val _ = OuterSyntax.markup_command ThyOutput.Verbatim "text_raw" "raw document preparation text"
  Keyword.thy_decl (Parse.opt_target -- Parse.doc_source >> IsarCmd.local_theory_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "sect" "formal comment (proof)"
  (Keyword.tag_proof Keyword.prf_heading) (Parse.doc_source >> IsarCmd.proof_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "subsect" "formal comment (proof)"
  (Keyword.tag_proof Keyword.prf_heading) (Parse.doc_source >> IsarCmd.proof_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "subsubsect" "formal comment (proof)"
  (Keyword.tag_proof Keyword.prf_heading) (Parse.doc_source >> IsarCmd.proof_markup);

val _ = OuterSyntax.markup_command ThyOutput.MarkupEnv "txt" "formal comment (proof)"
  (Keyword.tag_proof Keyword.prf_decl) (Parse.doc_source >> IsarCmd.proof_markup);

val _ = OuterSyntax.markup_command ThyOutput.Verbatim "txt_raw"
  "raw document preparation text (proof)" (Keyword.tag_proof Keyword.prf_decl)
  (Parse.doc_source >> IsarCmd.proof_markup);



(** theory commands **)

(* classes and sorts *)

val _ =
  OuterSyntax.command "classes" "declare type classes" Keyword.thy_decl
    (Scan.repeat1 (Parse.binding -- Scan.optional ((Parse.$$$ "\\<subseteq>" || Parse.$$$ "<") |--
        Parse.!!! (Parse.list1 Parse.xname)) [])
      >> (Toplevel.theory o fold AxClass.axiomatize_class_cmd));

val _ =
  OuterSyntax.command "classrel" "state inclusion of type classes (axiomatic!)" Keyword.thy_decl
    (Parse.and_list1 (Parse.xname -- ((Parse.$$$ "\\<subseteq>" || Parse.$$$ "<")
        |-- Parse.!!! Parse.xname))
    >> (Toplevel.theory o AxClass.axiomatize_classrel_cmd));

val _ =
  OuterSyntax.local_theory "default_sort" "declare default sort for explicit type variables"
    Keyword.thy_decl
    (Parse.sort >> (fn s => fn lthy => Local_Theory.set_defsort (Syntax.read_sort lthy s) lthy));


(* types *)

val _ =
  OuterSyntax.local_theory "typedecl" "type declaration" Keyword.thy_decl
    (Parse.type_args -- Parse.binding -- Parse.opt_mixfix
      >> (fn ((args, a), mx) => Typedecl.typedecl (a, map (rpair dummyS) args, mx) #> snd));

val _ =
  OuterSyntax.local_theory "types" "declare type abbreviations" Keyword.thy_decl
    (Scan.repeat1
      (Parse.type_args -- Parse.binding --
        (Parse.$$$ "=" |-- Parse.!!! (Parse.typ -- Parse.opt_mixfix')))
      >> (fold (fn ((args, a), (rhs, mx)) => snd o Typedecl.abbrev_cmd (a, args, mx) rhs)));

val _ =
  OuterSyntax.command "nonterminals" "declare types treated as grammar nonterminal symbols"
    Keyword.thy_decl (Scan.repeat1 Parse.binding >> (Toplevel.theory o Sign.add_nonterminals));

val _ =
  OuterSyntax.command "arities" "state type arities (axiomatic!)" Keyword.thy_decl
    (Scan.repeat1 Parse.arity >> (Toplevel.theory o fold AxClass.axiomatize_arity_cmd));


(* consts and syntax *)

val _ =
  OuterSyntax.command "judgment" "declare object-logic judgment" Keyword.thy_decl
    (Parse.const_binding >> (Toplevel.theory o Object_Logic.add_judgment_cmd));

val _ =
  OuterSyntax.command "consts" "declare constants" Keyword.thy_decl
    (Scan.repeat1 Parse.const_binding >> (Toplevel.theory o Sign.add_consts));

val opt_overloaded = Parse.opt_keyword "overloaded";

val _ =
  OuterSyntax.command "finalconsts" "declare constants as final" Keyword.thy_decl
    (opt_overloaded -- Scan.repeat1 Parse.term >> (uncurry (Toplevel.theory oo Theory.add_finals)));

val mode_spec =
  (Parse.$$$ "output" >> K ("", false)) ||
    Parse.name -- Scan.optional (Parse.$$$ "output" >> K false) true;

val opt_mode =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (mode_spec --| Parse.$$$ ")")) Syntax.mode_default;

val _ =
  OuterSyntax.command "syntax" "declare syntactic constants" Keyword.thy_decl
    (opt_mode -- Scan.repeat1 Parse.const >> (Toplevel.theory o uncurry Sign.add_modesyntax));

val _ =
  OuterSyntax.command "no_syntax" "delete syntax declarations" Keyword.thy_decl
    (opt_mode -- Scan.repeat1 Parse.const >> (Toplevel.theory o uncurry Sign.del_modesyntax));


(* translations *)

val trans_pat =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Parse.xname --| Parse.$$$ ")")) "logic"
    -- Parse.string;

fun trans_arrow toks =
  ((Parse.$$$ "\\<rightharpoonup>" || Parse.$$$ "=>") >> K Syntax.ParseRule ||
    (Parse.$$$ "\\<leftharpoondown>" || Parse.$$$ "<=") >> K Syntax.PrintRule ||
    (Parse.$$$ "\\<rightleftharpoons>" || Parse.$$$ "==") >> K Syntax.ParsePrintRule) toks;

val trans_line =
  trans_pat -- Parse.!!! (trans_arrow -- trans_pat)
    >> (fn (left, (arr, right)) => arr (left, right));

val _ =
  OuterSyntax.command "translations" "declare syntax translation rules" Keyword.thy_decl
    (Scan.repeat1 trans_line >> (Toplevel.theory o Sign.add_trrules));

val _ =
  OuterSyntax.command "no_translations" "remove syntax translation rules" Keyword.thy_decl
    (Scan.repeat1 trans_line >> (Toplevel.theory o Sign.del_trrules));


(* axioms and definitions *)

val _ =
  OuterSyntax.command "axioms" "state arbitrary propositions (axiomatic!)" Keyword.thy_decl
    (Scan.repeat1 SpecParse.spec >>
      (Toplevel.theory o
        (IsarCmd.add_axioms o
          tap (fn _ => legacy_feature "Old 'axioms' command -- use 'axiomatization' instead"))));

val opt_unchecked_overloaded =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!!
    (((Parse.$$$ "unchecked" >> K true) -- Scan.optional (Parse.$$$ "overloaded" >> K true) false ||
      Parse.$$$ "overloaded" >> K (false, true)) --| Parse.$$$ ")")) (false, false);

val _ =
  OuterSyntax.command "defs" "define constants" Keyword.thy_decl
    (opt_unchecked_overloaded --
      Scan.repeat1 (SpecParse.thm_name ":" -- Parse.prop >> (fn ((x, y), z) => ((x, z), y)))
      >> (Toplevel.theory o IsarCmd.add_defs));


(* old constdefs *)

val old_constdecl =
  Parse.binding --| Parse.where_ >> (fn x => (x, NONE, NoSyn)) ||
  Parse.binding -- (Parse.$$$ "::" |-- Parse.!!! Parse.typ >> SOME) -- Parse.opt_mixfix'
    --| Scan.option Parse.where_ >> Parse.triple1 ||
  Parse.binding -- (Parse.mixfix >> pair NONE) --| Scan.option Parse.where_ >> Parse.triple2;

val old_constdef = Scan.option old_constdecl -- (SpecParse.opt_thm_name ":" -- Parse.prop);

val structs =
  Scan.optional ((Parse.$$$ "(" -- Parse.$$$ "structure")
    |-- Parse.!!! (Parse.simple_fixes --| Parse.$$$ ")")) [];

val _ =
  OuterSyntax.command "constdefs" "old-style constant definition" Keyword.thy_decl
    (structs -- Scan.repeat1 old_constdef >> (Toplevel.theory o Constdefs.add_constdefs));


(* constant definitions and abbreviations *)

val _ =
  OuterSyntax.local_theory "definition" "constant definition" Keyword.thy_decl
    (SpecParse.constdef >> (fn args => #2 o Specification.definition_cmd args));

val _ =
  OuterSyntax.local_theory "abbreviation" "constant abbreviation" Keyword.thy_decl
    (opt_mode -- (Scan.option SpecParse.constdecl -- Parse.prop)
      >> (fn (mode, args) => Specification.abbreviation_cmd mode args));

val _ =
  OuterSyntax.local_theory "type_notation" "add concrete syntax for type constructors"
    Keyword.thy_decl
    (opt_mode -- Parse.and_list1 (Parse.xname -- Parse.mixfix)
      >> (fn (mode, args) => Specification.type_notation_cmd true mode args));

val _ =
  OuterSyntax.local_theory "no_type_notation" "delete concrete syntax for type constructors"
    Keyword.thy_decl
    (opt_mode -- Parse.and_list1 (Parse.xname -- Parse.mixfix)
      >> (fn (mode, args) => Specification.type_notation_cmd false mode args));

val _ =
  OuterSyntax.local_theory "notation" "add concrete syntax for constants / fixed variables"
    Keyword.thy_decl
    (opt_mode -- Parse.and_list1 (Parse.xname -- SpecParse.locale_mixfix)
      >> (fn (mode, args) => Specification.notation_cmd true mode args));

val _ =
  OuterSyntax.local_theory "no_notation" "delete concrete syntax for constants / fixed variables"
    Keyword.thy_decl
    (opt_mode -- Parse.and_list1 (Parse.xname -- SpecParse.locale_mixfix)
      >> (fn (mode, args) => Specification.notation_cmd false mode args));


(* constant specifications *)

val _ =
  OuterSyntax.command "axiomatization" "axiomatic constant specification" Keyword.thy_decl
    (Scan.optional Parse.fixes [] --
      Scan.optional (Parse.where_ |-- Parse.!!! (Parse.and_list1 SpecParse.specs)) []
      >> (fn (x, y) => Toplevel.theory (#2 o Specification.axiomatization_cmd x y)));


(* theorems *)

fun theorems kind =
  SpecParse.name_facts >> (fn args => #2 o Specification.theorems_cmd kind args);

val _ =
  OuterSyntax.local_theory "theorems" "define theorems" Keyword.thy_decl (theorems Thm.theoremK);

val _ =
  OuterSyntax.local_theory "lemmas" "define lemmas" Keyword.thy_decl (theorems Thm.lemmaK);

val _ =
  OuterSyntax.local_theory "declare" "declare theorems" Keyword.thy_decl
    (Parse.and_list1 SpecParse.xthms1
      >> (fn args => #2 o Specification.theorems_cmd "" [(Attrib.empty_binding, flat args)]));


(* name space entry path *)

val _ =
  OuterSyntax.command "global" "disable prefixing of theory name" Keyword.thy_decl
    (Scan.succeed (Toplevel.theory Sign.root_path));

val _ =
  OuterSyntax.command "local" "enable prefixing of theory name" Keyword.thy_decl
    (Scan.succeed (Toplevel.theory Sign.local_path));

fun hide_names name hide what =
  OuterSyntax.command name ("hide " ^ what ^ " from name space") Keyword.thy_decl
    ((Parse.opt_keyword "open" >> not) -- Scan.repeat1 Parse.xname >>
      (Toplevel.theory o uncurry hide));

val _ = hide_names "hide_class" IsarCmd.hide_class "classes";
val _ = hide_names "hide_type" IsarCmd.hide_type "types";
val _ = hide_names "hide_const" IsarCmd.hide_const "constants";
val _ = hide_names "hide_fact" IsarCmd.hide_fact "facts";


(* use ML text *)

fun propagate_env (context as Context.Proof lthy) =
      Context.Proof (Local_Theory.map_contexts (ML_Env.inherit context) lthy)
  | propagate_env context = context;

fun propagate_env_prf prf = Proof.map_contexts
  (Context.proof_map (ML_Env.inherit (Context.Proof (Proof.context_of prf)))) prf;

val _ =
  OuterSyntax.command "use" "ML text from file" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.path >>
      (fn path => Toplevel.generic_theory (ThyInfo.exec_file false path #> propagate_env)));

val _ =
  OuterSyntax.command "ML" "ML text within theory or local theory"
    (Keyword.tag_ml Keyword.thy_decl)
    (Parse.ML_source >> (fn (txt, pos) =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () => ML_Context.eval true pos txt) #> propagate_env)));

val _ =
  OuterSyntax.command "ML_prf" "ML text within proof" (Keyword.tag_proof Keyword.prf_decl)
    (Parse.ML_source >> (fn (txt, pos) =>
      Toplevel.proof (Proof.map_context (Context.proof_map
        (ML_Context.exec (fn () => ML_Context.eval true pos txt))) #> propagate_env_prf)));

val _ =
  OuterSyntax.command "ML_val" "diagnostic ML text" (Keyword.tag_ml Keyword.diag)
    (Parse.ML_source >> IsarCmd.ml_diag true);

val _ =
  OuterSyntax.command "ML_command" "diagnostic ML text (silent)" (Keyword.tag_ml Keyword.diag)
    (Parse.ML_source >> (Toplevel.no_timing oo IsarCmd.ml_diag false));

val _ =
  OuterSyntax.command "setup" "ML theory setup" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.ML_source >> (Toplevel.theory o IsarCmd.global_setup));

val _ =
  OuterSyntax.local_theory "local_setup" "ML local theory setup" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.ML_source >> IsarCmd.local_setup);

val _ =
  OuterSyntax.command "attribute_setup" "define attribute in ML" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.position Parse.name -- Parse.!!! (Parse.$$$ "=" |-- Parse.ML_source -- Parse.text)
      >> (fn (name, (txt, cmt)) => Toplevel.theory (Attrib.attribute_setup name txt cmt)));

val _ =
  OuterSyntax.command "method_setup" "define proof method in ML" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.position Parse.name -- Parse.!!! (Parse.$$$ "=" |-- Parse.ML_source -- Parse.text)
      >> (fn (name, (txt, cmt)) => Toplevel.theory (Method.method_setup name txt cmt)));

val _ =
  OuterSyntax.local_theory "declaration" "generic ML declaration" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.opt_keyword "pervasive" -- Parse.ML_source >> uncurry IsarCmd.declaration);

val _ =
  OuterSyntax.local_theory "simproc_setup" "define simproc in ML" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.name --
      (Parse.$$$ "(" |-- Parse.enum1 "|" Parse.term --| Parse.$$$ ")" --| Parse.$$$ "=") --
      Parse.ML_source -- Scan.optional (Parse.$$$ "identifier" |-- Scan.repeat1 Parse.xname) []
    >> (fn (((a, b), c), d) => IsarCmd.simproc_setup a b c d));


(* translation functions *)

val trfun = Parse.opt_keyword "advanced" -- Parse.ML_source;

val _ =
  OuterSyntax.command "parse_ast_translation" "install parse ast translation functions"
    (Keyword.tag_ml Keyword.thy_decl)
    (trfun >> (Toplevel.theory o IsarCmd.parse_ast_translation));

val _ =
  OuterSyntax.command "parse_translation" "install parse translation functions"
    (Keyword.tag_ml Keyword.thy_decl)
    (trfun >> (Toplevel.theory o IsarCmd.parse_translation));

val _ =
  OuterSyntax.command "print_translation" "install print translation functions"
    (Keyword.tag_ml Keyword.thy_decl)
    (trfun >> (Toplevel.theory o IsarCmd.print_translation));

val _ =
  OuterSyntax.command "typed_print_translation" "install typed print translation functions"
    (Keyword.tag_ml Keyword.thy_decl)
    (trfun >> (Toplevel.theory o IsarCmd.typed_print_translation));

val _ =
  OuterSyntax.command "print_ast_translation" "install print ast translation functions"
    (Keyword.tag_ml Keyword.thy_decl)
    (trfun >> (Toplevel.theory o IsarCmd.print_ast_translation));


(* oracles *)

val _ =
  OuterSyntax.command "oracle" "declare oracle" (Keyword.tag_ml Keyword.thy_decl)
    (Parse.position Parse.name -- (Parse.$$$ "=" |-- Parse.ML_source) >>
      (fn (x, y) => Toplevel.theory (IsarCmd.oracle x y)));


(* local theories *)

val _ =
  OuterSyntax.command "context" "enter local theory context" Keyword.thy_decl
    (Parse.name --| Parse.begin >> (fn name =>
      Toplevel.print o Toplevel.begin_local_theory true (Theory_Target.context_cmd name)));


(* locales *)

val locale_val =
  SpecParse.locale_expression false --
    Scan.optional (Parse.$$$ "+" |-- Parse.!!! (Scan.repeat1 SpecParse.context_element)) [] ||
  Scan.repeat1 SpecParse.context_element >> pair ([], []);

val _ =
  OuterSyntax.command "locale" "define named proof context" Keyword.thy_decl
    (Parse.binding --
      Scan.optional (Parse.$$$ "=" |-- Parse.!!! locale_val) (([], []), []) -- Parse.opt_begin
      >> (fn ((name, (expr, elems)), begin) =>
          (begin ? Toplevel.print) o Toplevel.begin_local_theory begin
            (Expression.add_locale_cmd name Binding.empty expr elems #> snd)));

val _ =
  OuterSyntax.command "sublocale"
    "prove sublocale relation between a locale and a locale expression" Keyword.thy_goal
    (Parse.xname --| (Parse.$$$ "\\<subseteq>" || Parse.$$$ "<") --
      Parse.!!! (SpecParse.locale_expression false)
      >> (fn (loc, expr) =>
          Toplevel.print o Toplevel.theory_to_proof (Expression.sublocale_cmd loc expr)));

val _ =
  OuterSyntax.command "interpretation"
    "prove interpretation of locale expression in theory" Keyword.thy_goal
    (Parse.!!! (SpecParse.locale_expression true) --
      Scan.optional (Parse.where_ |-- Parse.and_list1 (SpecParse.opt_thm_name ":" -- Parse.prop)) []
      >> (fn (expr, equations) => Toplevel.print o
          Toplevel.theory_to_proof (Expression.interpretation_cmd expr equations)));

val _ =
  OuterSyntax.command "interpret"
    "prove interpretation of locale expression in proof context"
    (Keyword.tag_proof Keyword.prf_goal)
    (Parse.!!! (SpecParse.locale_expression true)
      >> (fn expr => Toplevel.print o Toplevel.proof' (Expression.interpret_cmd expr)));


(* classes *)

val class_val =
  SpecParse.class_expr --
    Scan.optional (Parse.$$$ "+" |-- Parse.!!! (Scan.repeat1 SpecParse.context_element)) [] ||
  Scan.repeat1 SpecParse.context_element >> pair [];

val _ =
  OuterSyntax.command "class" "define type class" Keyword.thy_decl
   (Parse.binding -- Scan.optional (Parse.$$$ "=" |-- class_val) ([], []) -- Parse.opt_begin
    >> (fn ((name, (supclasses, elems)), begin) =>
        (begin ? Toplevel.print) o Toplevel.begin_local_theory begin
          (Class.class_cmd name supclasses elems #> snd)));

val _ =
  OuterSyntax.local_theory_to_proof "subclass" "prove a subclass relation" Keyword.thy_goal
    (Parse.xname >> Class.subclass_cmd);

val _ =
  OuterSyntax.command "instantiation" "instantiate and prove type arity" Keyword.thy_decl
   (Parse.multi_arity --| Parse.begin
     >> (fn arities => Toplevel.print o
         Toplevel.begin_local_theory true (Theory_Target.instantiation_cmd arities)));

val _ =
  OuterSyntax.command "instance" "prove type arity or subclass relation" Keyword.thy_goal
  ((Parse.xname -- ((Parse.$$$ "\\<subseteq>" || Parse.$$$ "<") |-- Parse.!!! Parse.xname)
        >> Class.classrel_cmd ||
    Parse.multi_arity >> Class.instance_arity_cmd)
    >> (Toplevel.print oo Toplevel.theory_to_proof) ||
    Scan.succeed
      (Toplevel.print o Toplevel.local_theory_to_proof NONE (Class.instantiation_instance I)));


(* arbitrary overloading *)

val _ =
  OuterSyntax.command "overloading" "overloaded definitions" Keyword.thy_decl
   (Scan.repeat1 (Parse.name --| (Parse.$$$ "\\<equiv>" || Parse.$$$ "==") -- Parse.term --
      Scan.optional (Parse.$$$ "(" |-- (Parse.$$$ "unchecked" >> K false) --| Parse.$$$ ")") true
      >> Parse.triple1) --| Parse.begin
   >> (fn operations => Toplevel.print o
         Toplevel.begin_local_theory true (Theory_Target.overloading_cmd operations)));


(* code generation *)

val _ =
  OuterSyntax.command "code_datatype" "define set of code datatype constructors" Keyword.thy_decl
    (Scan.repeat1 Parse.term >> (Toplevel.theory o Code.add_datatype_cmd));



(** proof commands **)

(* statements *)

fun gen_theorem schematic kind =
  OuterSyntax.local_theory_to_proof'
    (if schematic then "schematic_" ^ kind else kind)
    ("state " ^ (if schematic then "schematic " ^ kind else kind))
    (if schematic then Keyword.thy_schematic_goal else Keyword.thy_goal)
    (Scan.optional (SpecParse.opt_thm_name ":" --|
      Scan.ahead (SpecParse.locale_keyword || SpecParse.statement_keyword)) Attrib.empty_binding --
      SpecParse.general_statement >> (fn (a, (elems, concl)) =>
        ((if schematic then Specification.schematic_theorem_cmd else Specification.theorem_cmd)
          kind NONE (K I) a elems concl)));

val _ = gen_theorem false Thm.theoremK;
val _ = gen_theorem false Thm.lemmaK;
val _ = gen_theorem false Thm.corollaryK;
val _ = gen_theorem true Thm.theoremK;
val _ = gen_theorem true Thm.lemmaK;
val _ = gen_theorem true Thm.corollaryK;

val _ =
  OuterSyntax.local_theory_to_proof "example_proof"
    "example proof body, without any result" Keyword.thy_schematic_goal
    (Scan.succeed
      (Specification.schematic_theorem_cmd "" NONE (K I)
        Attrib.empty_binding [] (Element.Shows []) false #> Proof.enter_forward));

val _ =
  OuterSyntax.command "have" "state local goal"
    (Keyword.tag_proof Keyword.prf_goal)
    (SpecParse.statement >> ((Toplevel.print oo Toplevel.proof') o IsarCmd.have));

val _ =
  OuterSyntax.command "hence" "abbreviates \"then have\""
    (Keyword.tag_proof Keyword.prf_goal)
    (SpecParse.statement >> ((Toplevel.print oo Toplevel.proof') o IsarCmd.hence));

val _ =
  OuterSyntax.command "show" "state local goal, solving current obligation"
    (Keyword.tag_proof Keyword.prf_asm_goal)
    (SpecParse.statement >> ((Toplevel.print oo Toplevel.proof') o IsarCmd.show));

val _ =
  OuterSyntax.command "thus" "abbreviates \"then show\""
    (Keyword.tag_proof Keyword.prf_asm_goal)
    (SpecParse.statement >> ((Toplevel.print oo Toplevel.proof') o IsarCmd.thus));


(* facts *)

val facts = Parse.and_list1 SpecParse.xthms1;

val _ =
  OuterSyntax.command "then" "forward chaining"
    (Keyword.tag_proof Keyword.prf_chain)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.chain));

val _ =
  OuterSyntax.command "from" "forward chaining from given facts"
    (Keyword.tag_proof Keyword.prf_chain)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.from_thmss_cmd)));

val _ =
  OuterSyntax.command "with" "forward chaining from given and current facts"
    (Keyword.tag_proof Keyword.prf_chain)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.with_thmss_cmd)));

val _ =
  OuterSyntax.command "note" "define facts"
    (Keyword.tag_proof Keyword.prf_decl)
    (SpecParse.name_facts >> (Toplevel.print oo (Toplevel.proof o Proof.note_thmss_cmd)));

val _ =
  OuterSyntax.command "using" "augment goal facts"
    (Keyword.tag_proof Keyword.prf_decl)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.using_cmd)));

val _ =
  OuterSyntax.command "unfolding" "unfold definitions in goal and facts"
    (Keyword.tag_proof Keyword.prf_decl)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.unfolding_cmd)));


(* proof context *)

val _ =
  OuterSyntax.command "fix" "fix local variables (Skolem constants)"
    (Keyword.tag_proof Keyword.prf_asm)
    (Parse.fixes >> (Toplevel.print oo (Toplevel.proof o Proof.fix_cmd)));

val _ =
  OuterSyntax.command "assume" "assume propositions"
    (Keyword.tag_proof Keyword.prf_asm)
    (SpecParse.statement >> (Toplevel.print oo (Toplevel.proof o Proof.assume_cmd)));

val _ =
  OuterSyntax.command "presume" "assume propositions, to be established later"
    (Keyword.tag_proof Keyword.prf_asm)
    (SpecParse.statement >> (Toplevel.print oo (Toplevel.proof o Proof.presume_cmd)));

val _ =
  OuterSyntax.command "def" "local definition"
    (Keyword.tag_proof Keyword.prf_asm)
    (Parse.and_list1
      (SpecParse.opt_thm_name ":" --
        ((Parse.binding -- Parse.opt_mixfix) --
          ((Parse.$$$ "\\<equiv>" || Parse.$$$ "==") |-- Parse.!!! Parse.termp)))
    >> (Toplevel.print oo (Toplevel.proof o Proof.def_cmd)));

val _ =
  OuterSyntax.command "obtain" "generalized existence"
    (Keyword.tag_proof Keyword.prf_asm_goal)
    (Parse.parname -- Scan.optional (Parse.fixes --| Parse.where_) [] -- SpecParse.statement
      >> (fn ((x, y), z) => Toplevel.print o Toplevel.proof' (Obtain.obtain_cmd x y z)));

val _ =
  OuterSyntax.command "guess" "wild guessing (unstructured)"
    (Keyword.tag_proof Keyword.prf_asm_goal)
    (Scan.optional Parse.fixes [] >> (Toplevel.print oo (Toplevel.proof' o Obtain.guess_cmd)));

val _ =
  OuterSyntax.command "let" "bind text variables"
    (Keyword.tag_proof Keyword.prf_decl)
    (Parse.and_list1 (Parse.and_list1 Parse.term -- (Parse.$$$ "=" |-- Parse.term))
      >> (Toplevel.print oo (Toplevel.proof o Proof.let_bind_cmd)));

val _ =
  OuterSyntax.command "write" "add concrete syntax for constants / fixed variables"
    (Keyword.tag_proof Keyword.prf_decl)
    (opt_mode -- Parse.and_list1 (Parse.xname -- SpecParse.locale_mixfix)
    >> (fn (mode, args) => Toplevel.print o Toplevel.proof (Proof.write_cmd mode args)));

val case_spec =
  (Parse.$$$ "(" |--
    Parse.!!! (Parse.xname -- Scan.repeat1 (Parse.maybe Parse.name) --| Parse.$$$ ")") ||
    Parse.xname >> rpair []) -- SpecParse.opt_attribs >> Parse.triple1;

val _ =
  OuterSyntax.command "case" "invoke local context"
    (Keyword.tag_proof Keyword.prf_asm)
    (case_spec >> (Toplevel.print oo (Toplevel.proof o Proof.invoke_case_cmd)));


(* proof structure *)

val _ =
  OuterSyntax.command "{" "begin explicit proof block"
    (Keyword.tag_proof Keyword.prf_open)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.begin_block));

val _ =
  OuterSyntax.command "}" "end explicit proof block"
    (Keyword.tag_proof Keyword.prf_close)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.end_block));

val _ =
  OuterSyntax.command "next" "enter next proof block"
    (Keyword.tag_proof Keyword.prf_block)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.next_block));


(* end proof *)

val _ =
  OuterSyntax.command "qed" "conclude (sub-)proof"
    (Keyword.tag_proof Keyword.qed_block)
    (Scan.option Method.parse >> IsarCmd.qed);

val _ =
  OuterSyntax.command "by" "terminal backward proof"
    (Keyword.tag_proof Keyword.qed)
    (Method.parse -- Scan.option Method.parse >> IsarCmd.terminal_proof);

val _ =
  OuterSyntax.command ".." "default proof"
    (Keyword.tag_proof Keyword.qed)
    (Scan.succeed IsarCmd.default_proof);

val _ =
  OuterSyntax.command "." "immediate proof"
    (Keyword.tag_proof Keyword.qed)
    (Scan.succeed IsarCmd.immediate_proof);

val _ =
  OuterSyntax.command "done" "done proof"
    (Keyword.tag_proof Keyword.qed)
    (Scan.succeed IsarCmd.done_proof);

val _ =
  OuterSyntax.command "sorry" "skip proof (quick-and-dirty mode only!)"
    (Keyword.tag_proof Keyword.qed)
    (Scan.succeed IsarCmd.skip_proof);

val _ =
  OuterSyntax.command "oops" "forget proof"
    (Keyword.tag_proof Keyword.qed_global)
    (Scan.succeed Toplevel.forget_proof);


(* proof steps *)

val _ =
  OuterSyntax.command "defer" "shuffle internal proof state"
    (Keyword.tag_proof Keyword.prf_script)
    (Scan.option Parse.nat >> (Toplevel.print oo (Toplevel.proofs o Proof.defer)));

val _ =
  OuterSyntax.command "prefer" "shuffle internal proof state"
    (Keyword.tag_proof Keyword.prf_script)
    (Parse.nat >> (Toplevel.print oo (Toplevel.proofs o Proof.prefer)));

val _ =
  OuterSyntax.command "apply" "initial refinement step (unstructured)"
    (Keyword.tag_proof Keyword.prf_script)
    (Method.parse >> (Toplevel.print oo (Toplevel.proofs o Proof.apply)));

val _ =
  OuterSyntax.command "apply_end" "terminal refinement (unstructured)"
    (Keyword.tag_proof Keyword.prf_script)
    (Method.parse >> (Toplevel.print oo (Toplevel.proofs o Proof.apply_end)));

val _ =
  OuterSyntax.command "proof" "backward proof"
    (Keyword.tag_proof Keyword.prf_block)
    (Scan.option Method.parse >> (fn m => Toplevel.print o
      Toplevel.actual_proof (Proof_Node.applys (Proof.proof m)) o
      Toplevel.skip_proof (fn i => i + 1)));


(* calculational proof commands *)

val calc_args =
  Scan.option (Parse.$$$ "(" |-- Parse.!!! ((SpecParse.xthms1 --| Parse.$$$ ")")));

val _ =
  OuterSyntax.command "also" "combine calculation and current facts"
    (Keyword.tag_proof Keyword.prf_decl)
    (calc_args >> (Toplevel.proofs' o Calculation.also_cmd));

val _ =
  OuterSyntax.command "finally" "combine calculation and current facts, exhibit result"
    (Keyword.tag_proof Keyword.prf_chain)
    (calc_args >> (Toplevel.proofs' o Calculation.finally_cmd));

val _ =
  OuterSyntax.command "moreover" "augment calculation by current facts"
    (Keyword.tag_proof Keyword.prf_decl)
    (Scan.succeed (Toplevel.proof' Calculation.moreover));

val _ =
  OuterSyntax.command "ultimately" "augment calculation by current facts, exhibit result"
    (Keyword.tag_proof Keyword.prf_chain)
    (Scan.succeed (Toplevel.proof' Calculation.ultimately));


(* proof navigation *)

val _ =
  OuterSyntax.command "back" "backtracking of proof command"
    (Keyword.tag_proof Keyword.prf_script)
    (Scan.succeed (Toplevel.print o Toplevel.actual_proof Proof_Node.back o Toplevel.skip_proof I));


(* nested commands *)

val props_text =
  Scan.optional Parse_Value.properties [] -- Parse.position Parse.string
  >> (fn (props, (str, pos)) =>
      (Position.of_properties (Position.default_properties pos props), str));

val _ =
  OuterSyntax.improper_command "Isabelle.command" "nested Isabelle command" Keyword.control
    (props_text :|-- (fn (pos, str) =>
      (case OuterSyntax.parse pos str of
        [tr] => Scan.succeed (K tr)
      | _ => Scan.fail_with (K "exactly one command expected"))
      handle ERROR msg => Scan.fail_with (K msg)));



(** diagnostic commands (for interactive mode only) **)

val opt_modes =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.xname --| Parse.$$$ ")")) [];

val opt_bang = Scan.optional (Parse.$$$ "!" >> K true) false;

val _ =
  OuterSyntax.improper_command "pretty_setmargin" "change default margin for pretty printing"
    Keyword.diag (Parse.nat >> (Toplevel.no_timing oo IsarCmd.pretty_setmargin));

val _ =
  OuterSyntax.improper_command "help" "print outer syntax commands" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative OuterSyntax.print_outer_syntax));

val _ =
  OuterSyntax.improper_command "print_commands" "print outer syntax commands" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative OuterSyntax.print_outer_syntax));

val _ =
  OuterSyntax.improper_command "print_configs" "print configuration options" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_configs));

val _ =
  OuterSyntax.improper_command "print_context" "print theory context name" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_context));

val _ =
  OuterSyntax.improper_command "print_theory" "print logical theory contents (verbose!)"
    Keyword.diag (opt_bang >> (Toplevel.no_timing oo IsarCmd.print_theory));

val _ =
  OuterSyntax.improper_command "print_syntax" "print inner syntax of context (verbose!)"
    Keyword.diag (Scan.succeed (Toplevel.no_timing o IsarCmd.print_syntax));

val _ =
  OuterSyntax.improper_command "print_abbrevs" "print constant abbreviation of context"
    Keyword.diag (Scan.succeed (Toplevel.no_timing o IsarCmd.print_abbrevs));

val _ =
  OuterSyntax.improper_command "print_theorems"
      "print theorems of local theory or proof context" Keyword.diag
    (opt_bang >> (Toplevel.no_timing oo IsarCmd.print_theorems));

val _ =
  OuterSyntax.improper_command "print_locales" "print locales of this theory" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_locales));

val _ =
  OuterSyntax.improper_command "print_classes" "print classes of this theory" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_theory
      o Toplevel.keep (Class.print_classes o Toplevel.theory_of)));

val _ =
  OuterSyntax.improper_command "print_locale" "print locale of this theory" Keyword.diag
    (opt_bang -- Parse.xname >> (Toplevel.no_timing oo IsarCmd.print_locale));

val _ =
  OuterSyntax.improper_command "print_interps"
    "print interpretations of locale for this theory" Keyword.diag
    (Parse.xname >> (Toplevel.no_timing oo IsarCmd.print_registrations));

val _ =
  OuterSyntax.improper_command "print_attributes" "print attributes of this theory" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_attributes));

val _ =
  OuterSyntax.improper_command "print_simpset" "print context of Simplifier" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_simpset));

val _ =
  OuterSyntax.improper_command "print_rules" "print intro/elim rules" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_rules));

val _ =
  OuterSyntax.improper_command "print_trans_rules" "print transitivity rules" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_trans_rules));

val _ =
  OuterSyntax.improper_command "print_methods" "print methods of this theory" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_methods));

val _ =
  OuterSyntax.improper_command "print_antiquotations" "print antiquotations (global)" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_antiquotations));

val _ =
  OuterSyntax.improper_command "thy_deps" "visualize theory dependencies"
    Keyword.diag (Scan.succeed (Toplevel.no_timing o IsarCmd.thy_deps));

val _ =
  OuterSyntax.improper_command "class_deps" "visualize class dependencies"
    Keyword.diag (Scan.succeed (Toplevel.no_timing o IsarCmd.class_deps));

val _ =
  OuterSyntax.improper_command "thm_deps" "visualize theorem dependencies"
    Keyword.diag (SpecParse.xthms1 >> (Toplevel.no_timing oo IsarCmd.thm_deps));

val _ =
  OuterSyntax.improper_command "print_binds" "print term bindings of proof context" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_binds));

val _ =
  OuterSyntax.improper_command "print_facts" "print facts of proof context" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_facts));

val _ =
  OuterSyntax.improper_command "print_cases" "print cases of proof context" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_cases));

val _ =
  OuterSyntax.improper_command "print_statement" "print theorems as long statements" Keyword.diag
    (opt_modes -- SpecParse.xthms1 >> (Toplevel.no_timing oo IsarCmd.print_stmts));

val _ =
  OuterSyntax.improper_command "thm" "print theorems" Keyword.diag
    (opt_modes -- SpecParse.xthms1 >> (Toplevel.no_timing oo IsarCmd.print_thms));

val _ =
  OuterSyntax.improper_command "prf" "print proof terms of theorems" Keyword.diag
    (opt_modes -- Scan.option SpecParse.xthms1
      >> (Toplevel.no_timing oo IsarCmd.print_prfs false));

val _ =
  OuterSyntax.improper_command "full_prf" "print full proof terms of theorems" Keyword.diag
    (opt_modes -- Scan.option SpecParse.xthms1 >> (Toplevel.no_timing oo IsarCmd.print_prfs true));

val _ =
  OuterSyntax.improper_command "prop" "read and print proposition" Keyword.diag
    (opt_modes -- Parse.term >> (Toplevel.no_timing oo IsarCmd.print_prop));

val _ =
  OuterSyntax.improper_command "term" "read and print term" Keyword.diag
    (opt_modes -- Parse.term >> (Toplevel.no_timing oo IsarCmd.print_term));

val _ =
  OuterSyntax.improper_command "typ" "read and print type" Keyword.diag
    (opt_modes -- Parse.typ >> (Toplevel.no_timing oo IsarCmd.print_type));

val _ =
  OuterSyntax.improper_command "print_codesetup" "print code generator setup" Keyword.diag
    (Scan.succeed
      (Toplevel.no_timing o Toplevel.unknown_theory o Toplevel.keep
        (Code.print_codesetup o Toplevel.theory_of)));

val _ =
  OuterSyntax.improper_command "unused_thms" "find unused theorems" Keyword.diag
    (Scan.option ((Scan.repeat1 (Scan.unless Parse.minus Parse.name) --| Parse.minus) --
       Scan.option (Scan.repeat1 (Scan.unless Parse.minus Parse.name))) >>
         (Toplevel.no_timing oo IsarCmd.unused_thms));



(** system commands (for interactive mode only) **)

val _ =
  OuterSyntax.improper_command "cd" "change current working directory" Keyword.diag
    (Parse.path >> (Toplevel.no_timing oo IsarCmd.cd));

val _ =
  OuterSyntax.improper_command "pwd" "print current working directory" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.pwd));

val _ =
  OuterSyntax.improper_command "use_thy" "use theory file" Keyword.diag
    (Parse.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => ThyInfo.use_thy name)));

val _ =
  OuterSyntax.improper_command "touch_thy" "outdate theory, including descendants" Keyword.diag
    (Parse.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => ThyInfo.touch_thy name)));

val _ =
  OuterSyntax.improper_command "remove_thy" "remove theory from loader database" Keyword.diag
    (Parse.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => ThyInfo.remove_thy name)));

val _ =
  OuterSyntax.improper_command "kill_thy" "kill theory -- try to remove from loader database"
    Keyword.diag (Parse.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => ThyInfo.kill_thy name)));

val _ =
  OuterSyntax.improper_command "display_drafts" "display raw source files with symbols"
    Keyword.diag (Scan.repeat1 Parse.path >> (Toplevel.no_timing oo IsarCmd.display_drafts));

val _ =
  OuterSyntax.improper_command "print_drafts" "print raw source files with symbols"
    Keyword.diag (Scan.repeat1 Parse.path >> (Toplevel.no_timing oo IsarCmd.print_drafts));

val opt_limits =
  Scan.option Parse.nat -- Scan.option (Parse.$$$ "," |-- Parse.!!! Parse.nat);

val _ =
  OuterSyntax.improper_command "pr" "print current proof state (if present)" Keyword.diag
    (opt_modes -- opt_limits >> (Toplevel.no_timing oo IsarCmd.pr));

val _ =
  OuterSyntax.improper_command "disable_pr" "disable printing of toplevel state" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.disable_pr));

val _ =
  OuterSyntax.improper_command "enable_pr" "enable printing of toplevel state" Keyword.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.enable_pr));

val _ =
  OuterSyntax.improper_command "commit" "commit current session to ML database" Keyword.diag
    (Parse.opt_unit >> K (Toplevel.no_timing o Toplevel.imperative Secure.commit));

val _ =
  OuterSyntax.improper_command "quit" "quit Isabelle" Keyword.control
    (Parse.opt_unit >> (Toplevel.no_timing oo K IsarCmd.quit));

val _ =
  OuterSyntax.improper_command "exit" "exit Isar loop" Keyword.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.exit));

end;

