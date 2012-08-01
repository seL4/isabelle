(*  Title:      Pure/Isar/isar_syn.ML
    Author:     Markus Wenzel, TU Muenchen

Isar/Pure outer syntax.
*)

structure Isar_Syn: sig end =
struct

(** markup commands **)

val _ =
  Outer_Syntax.markup_command Thy_Output.Markup
    ("header", Keyword.diag) "theory header"
    (Parse.doc_source >> Isar_Cmd.header_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.Markup
    ("chapter", Keyword.thy_heading1) "chapter heading"
    (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.Markup
    ("section", Keyword.thy_heading2) "section heading"
    (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.Markup
    ("subsection", Keyword.thy_heading3) "subsection heading"
    (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.Markup
    ("subsubsection", Keyword.thy_heading4) "subsubsection heading"
    (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.MarkupEnv
    ("text", Keyword.thy_decl) "formal comment (theory)"
    (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.Verbatim
    ("text_raw", Keyword.thy_decl) "raw document preparation text"
    (Parse.opt_target -- Parse.doc_source >> Isar_Cmd.local_theory_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.Markup
    ("sect", Keyword.tag_proof Keyword.prf_heading2) "formal comment (proof)"
    (Parse.doc_source >> Isar_Cmd.proof_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.Markup
    ("subsect", Keyword.tag_proof Keyword.prf_heading3) "formal comment (proof)"
    (Parse.doc_source >> Isar_Cmd.proof_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.Markup
    ("subsubsect", Keyword.tag_proof Keyword.prf_heading4) "formal comment (proof)"
    (Parse.doc_source >> Isar_Cmd.proof_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.MarkupEnv
    ("txt", Keyword.tag_proof Keyword.prf_decl) "formal comment (proof)"
    (Parse.doc_source >> Isar_Cmd.proof_markup);

val _ =
  Outer_Syntax.markup_command Thy_Output.Verbatim
    ("txt_raw", Keyword.tag_proof Keyword.prf_decl) "raw document preparation text (proof)"
    (Parse.doc_source >> Isar_Cmd.proof_markup);



(** theory commands **)

(* classes and sorts *)

val _ =
  Outer_Syntax.command ("classes", Keyword.thy_decl) "declare type classes"
    (Scan.repeat1 (Parse.binding -- Scan.optional ((Parse.$$$ "\<subseteq>" || Parse.$$$ "<") |--
        Parse.!!! (Parse.list1 Parse.class)) [])
      >> (Toplevel.theory o fold AxClass.axiomatize_class_cmd));

val _ =
  Outer_Syntax.command ("classrel", Keyword.thy_decl) "state inclusion of type classes (axiomatic!)"
    (Parse.and_list1 (Parse.class -- ((Parse.$$$ "\<subseteq>" || Parse.$$$ "<")
        |-- Parse.!!! Parse.class))
    >> (Toplevel.theory o AxClass.axiomatize_classrel_cmd));

val _ =
  Outer_Syntax.local_theory ("default_sort", Keyword.thy_decl)
    "declare default sort for explicit type variables"
    (Parse.sort >> (fn s => fn lthy => Local_Theory.set_defsort (Syntax.read_sort lthy s) lthy));


(* types *)

val _ =
  Outer_Syntax.local_theory ("typedecl", Keyword.thy_decl) "type declaration"
    (Parse.type_args -- Parse.binding -- Parse.opt_mixfix
      >> (fn ((args, a), mx) => Typedecl.typedecl (a, map (rpair dummyS) args, mx) #> snd));

val _ =
  Outer_Syntax.local_theory ("type_synonym", Keyword.thy_decl) "declare type abbreviation"
    (Parse.type_args -- Parse.binding --
      (Parse.$$$ "=" |-- Parse.!!! (Parse.typ -- Parse.opt_mixfix'))
      >> (fn ((args, a), (rhs, mx)) => snd o Typedecl.abbrev_cmd (a, args, mx) rhs));

val _ =
  Outer_Syntax.command ("nonterminal", Keyword.thy_decl)
    "declare syntactic type constructors (grammar nonterminal symbols)"
    (Parse.and_list1 Parse.binding >> (Toplevel.theory o Sign.add_nonterminals_global));

val _ =
  Outer_Syntax.command ("arities", Keyword.thy_decl) "state type arities (axiomatic!)"
    (Scan.repeat1 Parse.arity >> (Toplevel.theory o fold AxClass.axiomatize_arity_cmd));


(* consts and syntax *)

val _ =
  Outer_Syntax.command ("judgment", Keyword.thy_decl) "declare object-logic judgment"
    (Parse.const_binding >> (Toplevel.theory o Object_Logic.add_judgment_cmd));

val _ =
  Outer_Syntax.command ("consts", Keyword.thy_decl) "declare constants"
    (Scan.repeat1 Parse.const_binding >> (Toplevel.theory o Sign.add_consts));

val mode_spec =
  (Parse.$$$ "output" >> K ("", false)) ||
    Parse.name -- Scan.optional (Parse.$$$ "output" >> K false) true;

val opt_mode =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!! (mode_spec --| Parse.$$$ ")")) Syntax.mode_default;

val _ =
  Outer_Syntax.command ("syntax", Keyword.thy_decl) "declare syntactic constants"
    (opt_mode -- Scan.repeat1 Parse.const_decl >> (Toplevel.theory o uncurry Sign.add_modesyntax));

val _ =
  Outer_Syntax.command ("no_syntax", Keyword.thy_decl) "delete syntax declarations"
    (opt_mode -- Scan.repeat1 Parse.const_decl >> (Toplevel.theory o uncurry Sign.del_modesyntax));


(* translations *)

val trans_pat =
  Scan.optional
    (Parse.$$$ "(" |-- Parse.!!! (Parse.xname --| Parse.$$$ ")")) "logic"
    -- Parse.inner_syntax Parse.string;

fun trans_arrow toks =
  ((Parse.$$$ "\<rightharpoonup>" || Parse.$$$ "=>") >> K Syntax.Parse_Rule ||
    (Parse.$$$ "\<leftharpoondown>" || Parse.$$$ "<=") >> K Syntax.Print_Rule ||
    (Parse.$$$ "\<rightleftharpoons>" || Parse.$$$ "==") >> K Syntax.Parse_Print_Rule) toks;

val trans_line =
  trans_pat -- Parse.!!! (trans_arrow -- trans_pat)
    >> (fn (left, (arr, right)) => arr (left, right));

val _ =
  Outer_Syntax.command ("translations", Keyword.thy_decl) "declare syntax translation rules"
    (Scan.repeat1 trans_line >> (Toplevel.theory o Isar_Cmd.translations));

val _ =
  Outer_Syntax.command ("no_translations", Keyword.thy_decl) "remove syntax translation rules"
    (Scan.repeat1 trans_line >> (Toplevel.theory o Isar_Cmd.no_translations));


(* axioms and definitions *)

val _ =
  Outer_Syntax.command ("axioms", Keyword.thy_decl) "state arbitrary propositions (axiomatic!)"
    (Scan.repeat1 Parse_Spec.spec >>
      (fn spec => Toplevel.theory (fn thy =>
        (legacy_feature "Old 'axioms' command -- use 'axiomatization' instead";
          Isar_Cmd.add_axioms spec thy))));

val opt_unchecked_overloaded =
  Scan.optional (Parse.$$$ "(" |-- Parse.!!!
    (((Parse.$$$ "unchecked" >> K true) -- Scan.optional (Parse.$$$ "overloaded" >> K true) false ||
      Parse.$$$ "overloaded" >> K (false, true)) --| Parse.$$$ ")")) (false, false);

val _ =
  Outer_Syntax.command ("defs", Keyword.thy_decl) "define constants"
    (opt_unchecked_overloaded --
      Scan.repeat1 (Parse_Spec.thm_name ":" -- Parse.prop >> (fn ((x, y), z) => ((x, z), y)))
      >> (Toplevel.theory o Isar_Cmd.add_defs));


(* constant definitions and abbreviations *)

val _ =
  Outer_Syntax.local_theory' ("definition", Keyword.thy_decl) "constant definition"
    (Parse_Spec.constdef >> (fn args => #2 oo Specification.definition_cmd args));

val _ =
  Outer_Syntax.local_theory' ("abbreviation", Keyword.thy_decl) "constant abbreviation"
    (opt_mode -- (Scan.option Parse_Spec.constdecl -- Parse.prop)
      >> (fn (mode, args) => Specification.abbreviation_cmd mode args));

val _ =
  Outer_Syntax.local_theory ("type_notation", Keyword.thy_decl)
    "add concrete syntax for type constructors"
    (opt_mode -- Parse.and_list1 (Parse.type_const -- Parse.mixfix)
      >> (fn (mode, args) => Specification.type_notation_cmd true mode args));

val _ =
  Outer_Syntax.local_theory ("no_type_notation", Keyword.thy_decl)
    "delete concrete syntax for type constructors"
    (opt_mode -- Parse.and_list1 (Parse.type_const -- Parse.mixfix)
      >> (fn (mode, args) => Specification.type_notation_cmd false mode args));

val _ =
  Outer_Syntax.local_theory ("notation", Keyword.thy_decl)
    "add concrete syntax for constants / fixed variables"
    (opt_mode -- Parse.and_list1 (Parse.const -- Parse_Spec.locale_mixfix)
      >> (fn (mode, args) => Specification.notation_cmd true mode args));

val _ =
  Outer_Syntax.local_theory ("no_notation", Keyword.thy_decl)
    "delete concrete syntax for constants / fixed variables"
    (opt_mode -- Parse.and_list1 (Parse.const -- Parse_Spec.locale_mixfix)
      >> (fn (mode, args) => Specification.notation_cmd false mode args));


(* constant specifications *)

val _ =
  Outer_Syntax.command ("axiomatization", Keyword.thy_decl) "axiomatic constant specification"
    (Scan.optional Parse.fixes [] --
      Scan.optional (Parse.where_ |-- Parse.!!! (Parse.and_list1 Parse_Spec.specs)) []
      >> (fn (x, y) => Toplevel.theory (#2 o Specification.axiomatization_cmd x y)));


(* theorems *)

fun theorems kind =
  Parse_Spec.name_facts -- Parse.for_fixes
    >> (fn (facts, fixes) => #2 oo Specification.theorems_cmd kind facts fixes);

val _ =
  Outer_Syntax.local_theory' ("theorems", Keyword.thy_decl) "define theorems"
    (theorems Thm.theoremK);

val _ =
  Outer_Syntax.local_theory' ("lemmas", Keyword.thy_decl) "define lemmas" (theorems Thm.lemmaK);

val _ =
  Outer_Syntax.local_theory' ("declare", Keyword.thy_decl) "declare theorems"
    (Parse.and_list1 Parse_Spec.xthms1 -- Parse.for_fixes
      >> (fn (facts, fixes) =>
          #2 oo Specification.theorems_cmd "" [(Attrib.empty_binding, flat facts)] fixes));


(* name space entry path *)

fun hide_names name hide what =
  Outer_Syntax.command (name, Keyword.thy_decl) ("hide " ^ what ^ " from name space")
    ((Parse.opt_keyword "open" >> not) -- Scan.repeat1 Parse.xname >>
      (Toplevel.theory o uncurry hide));

val _ = hide_names "hide_class" Isar_Cmd.hide_class "classes";
val _ = hide_names "hide_type" Isar_Cmd.hide_type "types";
val _ = hide_names "hide_const" Isar_Cmd.hide_const "constants";
val _ = hide_names "hide_fact" Isar_Cmd.hide_fact "facts";


(* use ML text *)

val _ =
  Outer_Syntax.command ("use", Keyword.tag_ml Keyword.thy_decl) "ML text from file"
    (Parse.path >> (fn path => Toplevel.generic_theory (Thy_Load.exec_ml path)));

val _ =
  Outer_Syntax.command ("ML", Keyword.tag_ml Keyword.thy_decl)
    "ML text within theory or local theory"
    (Parse.ML_source >> (fn (txt, pos) =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () => ML_Context.eval_text true pos txt) #>
          Local_Theory.propagate_ml_env)));

val _ =
  Outer_Syntax.command ("ML_prf", Keyword.tag_proof Keyword.prf_decl) "ML text within proof"
    (Parse.ML_source >> (fn (txt, pos) =>
      Toplevel.proof (Proof.map_context (Context.proof_map
        (ML_Context.exec (fn () => ML_Context.eval_text true pos txt))) #> Proof.propagate_ml_env)));

val _ =
  Outer_Syntax.command ("ML_val", Keyword.tag_ml Keyword.diag) "diagnostic ML text"
    (Parse.ML_source >> Isar_Cmd.ml_diag true);

val _ =
  Outer_Syntax.command ("ML_command", Keyword.tag_ml Keyword.diag) "diagnostic ML text (silent)"
    (Parse.ML_source >> (Toplevel.no_timing oo Isar_Cmd.ml_diag false));

val _ =
  Outer_Syntax.command ("setup", Keyword.tag_ml Keyword.thy_decl) "ML theory setup"
    (Parse.ML_source >> (Toplevel.theory o Isar_Cmd.global_setup));

val _ =
  Outer_Syntax.local_theory ("local_setup", Keyword.tag_ml Keyword.thy_decl) "ML local theory setup"
    (Parse.ML_source >> Isar_Cmd.local_setup);

val _ =
  Outer_Syntax.command ("attribute_setup", Keyword.tag_ml Keyword.thy_decl) "define attribute in ML"
    (Parse.position Parse.name --
        Parse.!!! (Parse.$$$ "=" |-- Parse.ML_source -- Scan.optional Parse.text "")
      >> (fn (name, (txt, cmt)) => Toplevel.theory (Attrib.attribute_setup name txt cmt)));

val _ =
  Outer_Syntax.command ("method_setup", Keyword.tag_ml Keyword.thy_decl) "define proof method in ML"
    (Parse.position Parse.name --
        Parse.!!! (Parse.$$$ "=" |-- Parse.ML_source -- Scan.optional Parse.text "")
      >> (fn (name, (txt, cmt)) => Toplevel.theory (Method.method_setup name txt cmt)));

val _ =
  Outer_Syntax.local_theory ("declaration", Keyword.tag_ml Keyword.thy_decl)
    "generic ML declaration"
    (Parse.opt_keyword "pervasive" -- Parse.ML_source
      >> (fn (pervasive, txt) => Isar_Cmd.declaration {syntax = false, pervasive = pervasive} txt));

val _ =
  Outer_Syntax.local_theory ("syntax_declaration", Keyword.tag_ml Keyword.thy_decl)
    "generic ML declaration"
    (Parse.opt_keyword "pervasive" -- Parse.ML_source
      >> (fn (pervasive, txt) => Isar_Cmd.declaration {syntax = true, pervasive = pervasive} txt));

val _ =
  Outer_Syntax.local_theory ("simproc_setup", Keyword.tag_ml Keyword.thy_decl)
    "define simproc in ML"
    (Parse.position Parse.name --
      (Parse.$$$ "(" |-- Parse.enum1 "|" Parse.term --| Parse.$$$ ")" --| Parse.$$$ "=") --
      Parse.ML_source -- Scan.optional (Parse.$$$ "identifier" |-- Scan.repeat1 Parse.xname) []
    >> (fn (((a, b), c), d) => Isar_Cmd.simproc_setup a b c d));


(* translation functions *)

val trfun = Parse.opt_keyword "advanced" -- Parse.ML_source;

val _ =
  Outer_Syntax.command ("parse_ast_translation", Keyword.tag_ml Keyword.thy_decl)
    "install parse ast translation functions"
    (trfun >> (Toplevel.theory o Isar_Cmd.parse_ast_translation));

val _ =
  Outer_Syntax.command ("parse_translation", Keyword.tag_ml Keyword.thy_decl)
    "install parse translation functions"
    (trfun >> (Toplevel.theory o Isar_Cmd.parse_translation));

val _ =
  Outer_Syntax.command ("print_translation", Keyword.tag_ml Keyword.thy_decl)
    "install print translation functions"
    (trfun >> (Toplevel.theory o Isar_Cmd.print_translation));

val _ =
  Outer_Syntax.command ("typed_print_translation", Keyword.tag_ml Keyword.thy_decl)
    "install typed print translation functions"
    (trfun >> (Toplevel.theory o Isar_Cmd.typed_print_translation));

val _ =
  Outer_Syntax.command ("print_ast_translation", Keyword.tag_ml Keyword.thy_decl)
    "install print ast translation functions"
    (trfun >> (Toplevel.theory o Isar_Cmd.print_ast_translation));


(* oracles *)

val _ =
  Outer_Syntax.command ("oracle", Keyword.tag_ml Keyword.thy_decl) "declare oracle"
    (Parse.position Parse.name -- (Parse.$$$ "=" |-- Parse.ML_source) >>
      (fn (x, y) => Toplevel.theory (Isar_Cmd.oracle x y)));


(* bundled declarations *)

val _ =
  Outer_Syntax.local_theory ("bundle", Keyword.thy_decl) "define bundle of declarations"
    ((Parse.binding --| Parse.$$$ "=") -- Parse_Spec.xthms1 -- Parse.for_fixes
      >> (uncurry Bundle.bundle_cmd));

val _ =
  Outer_Syntax.command ("include", Keyword.prf_decl)
    "include declarations from bundle in proof body"
    (Scan.repeat1 (Parse.position Parse.xname)
      >> (Toplevel.print oo (Toplevel.proof o Bundle.include_cmd)));

val _ =
  Outer_Syntax.command ("including", Keyword.prf_decl)
    "include declarations from bundle in goal refinement"
    (Scan.repeat1 (Parse.position Parse.xname)
      >> (Toplevel.print oo (Toplevel.proof o Bundle.including_cmd)));

val _ =
  Outer_Syntax.improper_command ("print_bundles", Keyword.diag) "print bundles of declarations"
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_context o
      Toplevel.keep (Bundle.print_bundles o Toplevel.context_of)));


(* local theories *)

val _ =
  Outer_Syntax.command ("context", Keyword.thy_decl) "begin local theory context"
    ((Parse.position Parse.xname >> (fn name =>
        Toplevel.print o Toplevel.begin_local_theory true (Named_Target.context_cmd name)) ||
      Scan.optional Parse_Spec.includes [] -- Scan.repeat Parse_Spec.context_element
        >> (fn (incls, elems) => Toplevel.open_target (Bundle.context_cmd incls elems)))
      --| Parse.begin);


(* locales *)

val locale_val =
  Parse_Spec.locale_expression false --
    Scan.optional (Parse.$$$ "+" |-- Parse.!!! (Scan.repeat1 Parse_Spec.context_element)) [] ||
  Scan.repeat1 Parse_Spec.context_element >> pair ([], []);

val _ =
  Outer_Syntax.command ("locale", Keyword.thy_decl) "define named proof context"
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
  Outer_Syntax.command ("sublocale", Keyword.thy_schematic_goal)
    "prove sublocale relation between a locale and a locale expression"
    (Parse.position Parse.xname --| (Parse.$$$ "\<subseteq>" || Parse.$$$ "<") --
      parse_interpretation_arguments false
      >> (fn (loc, (expr, equations)) =>
          Toplevel.print o Toplevel.theory_to_proof (Expression.sublocale_cmd I loc expr equations)));

val _ =
  Outer_Syntax.command ("interpretation", Keyword.thy_schematic_goal)
    "prove interpretation of locale expression in theory"
    (parse_interpretation_arguments true
      >> (fn (expr, equations) => Toplevel.print o
          Toplevel.theory_to_proof (Expression.interpretation_cmd expr equations)));

val _ =
  Outer_Syntax.command ("interpret", Keyword.tag_proof Keyword.prf_goal)
    "prove interpretation of locale expression in proof context"
    (parse_interpretation_arguments true
      >> (fn (expr, equations) => Toplevel.print o
          Toplevel.proof' (Expression.interpret_cmd expr equations)));


(* classes *)

val class_val =
  Parse_Spec.class_expression --
    Scan.optional (Parse.$$$ "+" |-- Parse.!!! (Scan.repeat1 Parse_Spec.context_element)) [] ||
  Scan.repeat1 Parse_Spec.context_element >> pair [];

val _ =
  Outer_Syntax.command ("class", Keyword.thy_decl) "define type class"
   (Parse.binding -- Scan.optional (Parse.$$$ "=" |-- class_val) ([], []) -- Parse.opt_begin
    >> (fn ((name, (supclasses, elems)), begin) =>
        (begin ? Toplevel.print) o Toplevel.begin_local_theory begin
          (Class_Declaration.class_cmd I name supclasses elems #> snd)));

val _ =
  Outer_Syntax.local_theory_to_proof ("subclass", Keyword.thy_goal) "prove a subclass relation"
    (Parse.class >> Class_Declaration.subclass_cmd I);

val _ =
  Outer_Syntax.command ("instantiation", Keyword.thy_decl) "instantiate and prove type arity"
   (Parse.multi_arity --| Parse.begin
     >> (fn arities => Toplevel.print o
         Toplevel.begin_local_theory true (Class.instantiation_cmd arities)));

val _ =
  Outer_Syntax.command ("instance", Keyword.thy_goal) "prove type arity or subclass relation"
  ((Parse.class --
    ((Parse.$$$ "\<subseteq>" || Parse.$$$ "<") |-- Parse.!!! Parse.class) >> Class.classrel_cmd ||
    Parse.multi_arity >> Class.instance_arity_cmd)
    >> (Toplevel.print oo Toplevel.theory_to_proof) ||
    Scan.succeed
      (Toplevel.print o Toplevel.local_theory_to_proof NONE (Class.instantiation_instance I)));


(* arbitrary overloading *)

val _ =
  Outer_Syntax.command ("overloading", Keyword.thy_decl) "overloaded definitions"
   (Scan.repeat1 (Parse.name --| (Parse.$$$ "\<equiv>" || Parse.$$$ "==") -- Parse.term --
      Scan.optional (Parse.$$$ "(" |-- (Parse.$$$ "unchecked" >> K false) --| Parse.$$$ ")") true
      >> Parse.triple1) --| Parse.begin
   >> (fn operations => Toplevel.print o
         Toplevel.begin_local_theory true (Overloading.overloading_cmd operations)));


(* code generation *)

val _ =
  Outer_Syntax.command ("code_datatype", Keyword.thy_decl)
    "define set of code datatype constructors"
    (Scan.repeat1 Parse.term >> (Toplevel.theory o Code.add_datatype_cmd));



(** proof commands **)

(* statements *)

fun gen_theorem schematic kind =
  Outer_Syntax.local_theory_to_proof'
    (if schematic then ("schematic_" ^ kind, Keyword.thy_schematic_goal)
     else (kind, Keyword.thy_goal))
    ("state " ^ (if schematic then "schematic " ^ kind else kind))
    (Scan.optional (Parse_Spec.opt_thm_name ":" --|
      Scan.ahead (Parse_Spec.includes >> K "" ||
        Parse_Spec.locale_keyword || Parse_Spec.statement_keyword)) Attrib.empty_binding --
      Scan.optional Parse_Spec.includes [] --
      Parse_Spec.general_statement >> (fn ((a, includes), (elems, concl)) =>
        ((if schematic then Specification.schematic_theorem_cmd else Specification.theorem_cmd)
          kind NONE (K I) a includes elems concl)));

val _ = gen_theorem false Thm.theoremK;
val _ = gen_theorem false Thm.lemmaK;
val _ = gen_theorem false Thm.corollaryK;
val _ = gen_theorem true Thm.theoremK;
val _ = gen_theorem true Thm.lemmaK;
val _ = gen_theorem true Thm.corollaryK;

val _ =
  Outer_Syntax.local_theory_to_proof ("notepad", Keyword.thy_decl) "begin proof context"
    (Parse.begin >> K Proof.begin_notepad);

val _ =
  Outer_Syntax.command ("have", Keyword.tag_proof Keyword.prf_goal) "state local goal"
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o Isar_Cmd.have));

val _ =
  Outer_Syntax.command ("hence", Keyword.tag_proof Keyword.prf_goal) "abbreviates \"then have\""
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o Isar_Cmd.hence));

val _ =
  Outer_Syntax.command ("show", Keyword.tag_proof Keyword.prf_asm_goal)
    "state local goal, solving current obligation"
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o Isar_Cmd.show));

val _ =
  Outer_Syntax.command ("thus", Keyword.tag_proof Keyword.prf_asm_goal) "abbreviates \"then show\""
    (Parse_Spec.statement >> ((Toplevel.print oo Toplevel.proof') o Isar_Cmd.thus));


(* facts *)

val facts = Parse.and_list1 Parse_Spec.xthms1;

val _ =
  Outer_Syntax.command ("then", Keyword.tag_proof Keyword.prf_chain) "forward chaining"
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.chain));

val _ =
  Outer_Syntax.command ("from", Keyword.tag_proof Keyword.prf_chain)
    "forward chaining from given facts"
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.from_thmss_cmd)));

val _ =
  Outer_Syntax.command ("with", Keyword.tag_proof Keyword.prf_chain)
    "forward chaining from given and current facts"
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.with_thmss_cmd)));

val _ =
  Outer_Syntax.command ("note", Keyword.tag_proof Keyword.prf_decl) "define facts"
    (Parse_Spec.name_facts >> (Toplevel.print oo (Toplevel.proof o Proof.note_thmss_cmd)));

val _ =
  Outer_Syntax.command ("using", Keyword.tag_proof Keyword.prf_decl) "augment goal facts"
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.using_cmd)));

val _ =
  Outer_Syntax.command ("unfolding", Keyword.tag_proof Keyword.prf_decl)
    "unfold definitions in goal and facts"
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.unfolding_cmd)));


(* proof context *)

val _ =
  Outer_Syntax.command ("fix", Keyword.tag_proof Keyword.prf_asm)
    "fix local variables (Skolem constants)"
    (Parse.fixes >> (Toplevel.print oo (Toplevel.proof o Proof.fix_cmd)));

val _ =
  Outer_Syntax.command ("assume", Keyword.tag_proof Keyword.prf_asm) "assume propositions"
    (Parse_Spec.statement >> (Toplevel.print oo (Toplevel.proof o Proof.assume_cmd)));

val _ =
  Outer_Syntax.command ("presume", Keyword.tag_proof Keyword.prf_asm)
    "assume propositions, to be established later"
    (Parse_Spec.statement >> (Toplevel.print oo (Toplevel.proof o Proof.presume_cmd)));

val _ =
  Outer_Syntax.command ("def", Keyword.tag_proof Keyword.prf_asm) "local definition"
    (Parse.and_list1
      (Parse_Spec.opt_thm_name ":" --
        ((Parse.binding -- Parse.opt_mixfix) --
          ((Parse.$$$ "\<equiv>" || Parse.$$$ "==") |-- Parse.!!! Parse.termp)))
    >> (Toplevel.print oo (Toplevel.proof o Proof.def_cmd)));

val _ =
  Outer_Syntax.command ("obtain", Keyword.tag_proof Keyword.prf_asm_goal)
    "generalized elimination"
    (Parse.parname -- Scan.optional (Parse.fixes --| Parse.where_) [] -- Parse_Spec.statement
      >> (fn ((x, y), z) => Toplevel.print o Toplevel.proof' (Obtain.obtain_cmd x y z)));

val _ =
  Outer_Syntax.command ("guess", Keyword.tag_proof Keyword.prf_asm_goal)
    "wild guessing (unstructured)"
    (Scan.optional Parse.fixes [] >> (Toplevel.print oo (Toplevel.proof' o Obtain.guess_cmd)));

val _ =
  Outer_Syntax.command ("let", Keyword.tag_proof Keyword.prf_decl) "bind text variables"
    (Parse.and_list1 (Parse.and_list1 Parse.term -- (Parse.$$$ "=" |-- Parse.term))
      >> (Toplevel.print oo (Toplevel.proof o Proof.let_bind_cmd)));

val _ =
  Outer_Syntax.command ("write", Keyword.tag_proof Keyword.prf_decl)
    "add concrete syntax for constants / fixed variables"
    (opt_mode -- Parse.and_list1 (Parse.const -- Parse_Spec.locale_mixfix)
    >> (fn (mode, args) => Toplevel.print o Toplevel.proof (Proof.write_cmd mode args)));

val case_spec =
  (Parse.$$$ "(" |--
    Parse.!!! (Parse.xname -- Scan.repeat1 (Parse.maybe Parse.binding) --| Parse.$$$ ")") ||
    Parse.xname >> rpair []) -- Parse_Spec.opt_attribs >> Parse.triple1;

val _ =
  Outer_Syntax.command ("case", Keyword.tag_proof Keyword.prf_asm) "invoke local context"
    (case_spec >> (Toplevel.print oo (Toplevel.proof o Proof.invoke_case_cmd)));


(* proof structure *)

val _ =
  Outer_Syntax.command ("{", Keyword.tag_proof Keyword.prf_open) "begin explicit proof block"
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.begin_block));

val _ =
  Outer_Syntax.command ("}", Keyword.tag_proof Keyword.prf_close) "end explicit proof block"
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.end_block));

val _ =
  Outer_Syntax.command ("next", Keyword.tag_proof Keyword.prf_block) "enter next proof block"
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.next_block));


(* end proof *)

val _ =
  Outer_Syntax.command ("qed", Keyword.tag_proof Keyword.qed_block) "conclude (sub-)proof"
    (Scan.option Method.parse >> Isar_Cmd.qed);

val _ =
  Outer_Syntax.command ("by", Keyword.tag_proof Keyword.qed) "terminal backward proof"
    (Method.parse -- Scan.option Method.parse >> Isar_Cmd.terminal_proof);

val _ =
  Outer_Syntax.command ("..", Keyword.tag_proof Keyword.qed) "default proof"
    (Scan.succeed Isar_Cmd.default_proof);

val _ =
  Outer_Syntax.command (".", Keyword.tag_proof Keyword.qed) "immediate proof"
    (Scan.succeed Isar_Cmd.immediate_proof);

val _ =
  Outer_Syntax.command ("done", Keyword.tag_proof Keyword.qed) "done proof"
    (Scan.succeed Isar_Cmd.done_proof);

val _ =
  Outer_Syntax.command ("sorry", Keyword.tag_proof Keyword.qed)
    "skip proof (quick-and-dirty mode only!)"
    (Scan.succeed Isar_Cmd.skip_proof);

val _ =
  Outer_Syntax.command ("oops", Keyword.tag_proof Keyword.qed_global) "forget proof"
    (Scan.succeed Toplevel.forget_proof);


(* proof steps *)

val _ =
  Outer_Syntax.command ("defer", Keyword.tag_proof Keyword.prf_script)
    "shuffle internal proof state"
    (Scan.option Parse.nat >> (Toplevel.print oo (Toplevel.proofs o Proof.defer)));

val _ =
  Outer_Syntax.command ("prefer", Keyword.tag_proof Keyword.prf_script)
    "shuffle internal proof state"
    (Parse.nat >> (Toplevel.print oo (Toplevel.proofs o Proof.prefer)));

val _ =
  Outer_Syntax.command ("apply", Keyword.tag_proof Keyword.prf_script)
    "initial refinement step (unstructured)"
    (Method.parse >> (Toplevel.print oo (Toplevel.proofs o Proof.apply)));

val _ =
  Outer_Syntax.command ("apply_end", Keyword.tag_proof Keyword.prf_script)
    "terminal refinement (unstructured)"
    (Method.parse >> (Toplevel.print oo (Toplevel.proofs o Proof.apply_end)));

val _ =
  Outer_Syntax.command ("proof", Keyword.tag_proof Keyword.prf_block) "backward proof"
    (Scan.option Method.parse >> (fn m => Toplevel.print o
      Toplevel.actual_proof (Proof_Node.applys (Proof.proof m)) o
      Toplevel.skip_proof (fn i => i + 1)));


(* calculational proof commands *)

val calc_args =
  Scan.option (Parse.$$$ "(" |-- Parse.!!! ((Parse_Spec.xthms1 --| Parse.$$$ ")")));

val _ =
  Outer_Syntax.command ("also", Keyword.tag_proof Keyword.prf_decl)
    "combine calculation and current facts"
    (calc_args >> (Toplevel.proofs' o Calculation.also_cmd));

val _ =
  Outer_Syntax.command ("finally", Keyword.tag_proof Keyword.prf_chain)
    "combine calculation and current facts, exhibit result"
    (calc_args >> (Toplevel.proofs' o Calculation.finally_cmd));

val _ =
  Outer_Syntax.command ("moreover", Keyword.tag_proof Keyword.prf_decl)
    "augment calculation by current facts"
    (Scan.succeed (Toplevel.proof' Calculation.moreover));

val _ =
  Outer_Syntax.command ("ultimately", Keyword.tag_proof Keyword.prf_chain)
    "augment calculation by current facts, exhibit result"
    (Scan.succeed (Toplevel.proof' Calculation.ultimately));


(* proof navigation *)

val _ =
  Outer_Syntax.command ("back", Keyword.tag_proof Keyword.prf_script)
    "backtracking of proof command"
    (Scan.succeed (Toplevel.print o Toplevel.actual_proof Proof_Node.back o Toplevel.skip_proof I));


(* nested commands *)

val props_text =
  Scan.optional Parse.properties [] -- Parse.position Parse.string
  >> (fn (props, (str, pos)) =>
      (Position.of_properties (Position.default_properties pos props), str));

val _ =
  Outer_Syntax.improper_command ("Isabelle.command", Keyword.control) "nested Isabelle command"
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
  Outer_Syntax.improper_command ("pretty_setmargin", Keyword.diag)
    "change default margin for pretty printing"
    (Parse.nat >>
      (fn n => Toplevel.no_timing o Toplevel.imperative (fn () => Pretty.margin_default := n)));

val _ =
  Outer_Syntax.improper_command ("help", Keyword.diag) "print outer syntax commands"
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative Outer_Syntax.print_outer_syntax));

val _ =
  Outer_Syntax.improper_command ("print_commands", Keyword.diag) "print outer syntax commands"
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative Outer_Syntax.print_outer_syntax));

val _ =
  Outer_Syntax.improper_command ("print_configs", Keyword.diag) "print configuration options"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_configs));

val _ =
  Outer_Syntax.improper_command ("print_context", Keyword.diag) "print theory context name"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_context));

val _ =
  Outer_Syntax.improper_command ("print_theory", Keyword.diag)
    "print logical theory contents (verbose!)"
    (opt_bang >> (Toplevel.no_timing oo Isar_Cmd.print_theory));

val _ =
  Outer_Syntax.improper_command ("print_syntax", Keyword.diag)
    "print inner syntax of context (verbose!)"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_syntax));

val _ =
  Outer_Syntax.improper_command ("print_abbrevs", Keyword.diag)
    "print constant abbreviation of context"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_abbrevs));

val _ =
  Outer_Syntax.improper_command ("print_theorems", Keyword.diag)
    "print theorems of local theory or proof context"
    (opt_bang >> (Toplevel.no_timing oo Isar_Cmd.print_theorems));

val _ =
  Outer_Syntax.improper_command ("print_locales", Keyword.diag)
    "print locales of this theory"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_locales));

val _ =
  Outer_Syntax.improper_command ("print_classes", Keyword.diag) "print classes of this theory"
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_theory o
      Toplevel.keep (Class.print_classes o Toplevel.context_of)));

val _ =
  Outer_Syntax.improper_command ("print_locale", Keyword.diag) "print locale of this theory"
    (opt_bang -- Parse.position Parse.xname >> (Toplevel.no_timing oo Isar_Cmd.print_locale));

val _ =
  Outer_Syntax.improper_command ("print_interps", Keyword.diag)
    "print interpretations of locale for this theory or proof context"
    (Parse.position Parse.xname >> (Toplevel.no_timing oo Isar_Cmd.print_registrations));

val _ =
  Outer_Syntax.improper_command ("print_dependencies", Keyword.diag)
    "print dependencies of locale expression"
    (opt_bang -- Parse_Spec.locale_expression true >>
      (Toplevel.no_timing oo Isar_Cmd.print_dependencies));

val _ =
  Outer_Syntax.improper_command ("print_attributes", Keyword.diag)
    "print attributes of this theory"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_attributes));

val _ =
  Outer_Syntax.improper_command ("print_simpset", Keyword.diag)
    "print context of Simplifier"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_simpset));

val _ =
  Outer_Syntax.improper_command ("print_rules", Keyword.diag) "print intro/elim rules"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_rules));

val _ =
  Outer_Syntax.improper_command ("print_trans_rules", Keyword.diag) "print transitivity rules"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_trans_rules));

val _ =
  Outer_Syntax.improper_command ("print_methods", Keyword.diag) "print methods of this theory"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_methods));

val _ =
  Outer_Syntax.improper_command ("print_antiquotations", Keyword.diag)
    "print antiquotations (global)"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_antiquotations));

val _ =
  Outer_Syntax.improper_command ("thy_deps", Keyword.diag) "visualize theory dependencies"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.thy_deps));

val _ =
  Outer_Syntax.improper_command ("class_deps", Keyword.diag) "visualize class dependencies"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.class_deps));

val _ =
  Outer_Syntax.improper_command ("thm_deps", Keyword.diag) "visualize theorem dependencies"
    (Parse_Spec.xthms1 >> (Toplevel.no_timing oo Isar_Cmd.thm_deps));

val _ =
  Outer_Syntax.improper_command ("print_binds", Keyword.diag) "print term bindings of proof context"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_binds));

val _ =
  Outer_Syntax.improper_command ("print_facts", Keyword.diag) "print facts of proof context"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_facts));

val _ =
  Outer_Syntax.improper_command ("print_cases", Keyword.diag) "print cases of proof context"
    (Scan.succeed (Toplevel.no_timing o Isar_Cmd.print_cases));

val _ =
  Outer_Syntax.improper_command ("print_statement", Keyword.diag)
    "print theorems as long statements"
    (opt_modes -- Parse_Spec.xthms1 >> (Toplevel.no_timing oo Isar_Cmd.print_stmts));

val _ =
  Outer_Syntax.improper_command ("thm", Keyword.diag) "print theorems"
    (opt_modes -- Parse_Spec.xthms1 >> (Toplevel.no_timing oo Isar_Cmd.print_thms));

val _ =
  Outer_Syntax.improper_command ("prf", Keyword.diag) "print proof terms of theorems"
    (opt_modes -- Scan.option Parse_Spec.xthms1
      >> (Toplevel.no_timing oo Isar_Cmd.print_prfs false));

val _ =
  Outer_Syntax.improper_command ("full_prf", Keyword.diag) "print full proof terms of theorems"
    (opt_modes -- Scan.option Parse_Spec.xthms1 >> (Toplevel.no_timing oo Isar_Cmd.print_prfs true));

val _ =
  Outer_Syntax.improper_command ("prop", Keyword.diag) "read and print proposition"
    (opt_modes -- Parse.term >> (Toplevel.no_timing oo Isar_Cmd.print_prop));

val _ =
  Outer_Syntax.improper_command ("term", Keyword.diag) "read and print term"
    (opt_modes -- Parse.term >> (Toplevel.no_timing oo Isar_Cmd.print_term));

val _ =
  Outer_Syntax.improper_command ("typ", Keyword.diag) "read and print type"
    (opt_modes -- Parse.typ >> (Toplevel.no_timing oo Isar_Cmd.print_type));

val _ =
  Outer_Syntax.improper_command ("print_codesetup", Keyword.diag) "print code generator setup"
    (Scan.succeed
      (Toplevel.no_timing o Toplevel.unknown_theory o Toplevel.keep
        (Code.print_codesetup o Toplevel.theory_of)));

val _ =
  Outer_Syntax.improper_command ("unused_thms", Keyword.diag) "find unused theorems"
    (Scan.option ((Scan.repeat1 (Scan.unless Parse.minus Parse.name) --| Parse.minus) --
       Scan.option (Scan.repeat1 (Scan.unless Parse.minus Parse.name))) >>
         (Toplevel.no_timing oo Isar_Cmd.unused_thms));



(** system commands (for interactive mode only) **)

val _ =
  Outer_Syntax.improper_command ("cd", Keyword.control) "change current working directory"
    (Parse.path >> (fn path => Toplevel.no_timing o Toplevel.imperative (fn () => File.cd path)));

val _ =
  Outer_Syntax.improper_command ("pwd", Keyword.diag) "print current working directory"
    (Scan.succeed (Toplevel.no_timing o
      Toplevel.imperative (fn () => writeln (Path.print (File.pwd ())))));

val _ =
  Outer_Syntax.improper_command ("use_thy", Keyword.control) "use theory file"
    (Parse.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => Thy_Info.use_thy name)));

val _ =
  Outer_Syntax.improper_command ("remove_thy", Keyword.control) "remove theory from loader database"
    (Parse.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => Thy_Info.remove_thy name)));

val _ =
  Outer_Syntax.improper_command ("kill_thy", Keyword.control)
    "kill theory -- try to remove from loader database"
    (Parse.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => Thy_Info.kill_thy name)));

val _ =
  Outer_Syntax.improper_command ("display_drafts", Keyword.diag)
    "display raw source files with symbols"
    (Scan.repeat1 Parse.path >> (Toplevel.no_timing oo Isar_Cmd.display_drafts));

val _ =
  Outer_Syntax.improper_command ("print_drafts", Keyword.diag)
    "print raw source files with symbols"
    (Scan.repeat1 Parse.path >> (Toplevel.no_timing oo Isar_Cmd.print_drafts));

val _ =  (* FIXME tty only *)
  Outer_Syntax.improper_command ("pr", Keyword.diag) "print current proof state (if present)"
    (opt_modes -- Scan.option Parse.nat >> (fn (modes, limit) =>
      Toplevel.no_timing o Toplevel.keep (fn state =>
       (case limit of NONE => () | SOME n => Goal_Display.goals_limit_default := n;
        Toplevel.quiet := false;
        Print_Mode.with_modes modes (Toplevel.print_state true) state))));

val _ =
  Outer_Syntax.improper_command ("disable_pr", Keyword.control)
    "disable printing of toplevel state"
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative (fn () => Toplevel.quiet := true)));

val _ =
  Outer_Syntax.improper_command ("enable_pr", Keyword.control)
    "enable printing of toplevel state"
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative (fn () => Toplevel.quiet := false)));

val _ =
  Outer_Syntax.improper_command ("commit", Keyword.control)
    "commit current session to ML database"
    (Parse.opt_unit >> K (Toplevel.no_timing o Toplevel.imperative Secure.commit));

val _ =
  Outer_Syntax.improper_command ("quit", Keyword.control) "quit Isabelle"
    (Parse.opt_unit >> (Toplevel.no_timing oo K (Toplevel.imperative quit)));

val _ =
  Outer_Syntax.improper_command ("exit", Keyword.control) "exit Isar loop"
    (Scan.succeed
      (Toplevel.no_timing o Toplevel.keep (fn state =>
        (Context.set_thread_data (try Toplevel.generic_theory_of state);
          raise Runtime.TERMINATE))));



(** end **)

val _ =
  Outer_Syntax.command ("end", Keyword.tag_theory Keyword.thy_end) "end context"
    (Scan.succeed
      (Toplevel.exit o Toplevel.end_local_theory o Toplevel.close_target o
        Toplevel.end_proof (K Proof.end_notepad)));

end;

