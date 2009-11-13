(*  Title:      Pure/Isar/isar_syn.ML
    Author:     Markus Wenzel, TU Muenchen

Isar/Pure outer syntax.
*)

structure IsarSyn: sig end =
struct

structure P = OuterParse and K = OuterKeyword;


(** keywords **)

(*keep keywords consistent with the parsers, otherwise be prepared for
  unexpected errors*)

val _ = List.app OuterKeyword.keyword
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
  OuterSyntax.command "theory" "begin theory" (K.tag_theory K.thy_begin)
    (Thy_Header.args >> (Toplevel.print oo IsarCmd.init_theory));

val _ =
  OuterSyntax.command "end" "end (local) theory" (K.tag_theory K.thy_end)
    (Scan.succeed (Toplevel.exit o Toplevel.end_local_theory));



(** markup commands **)

val _ = OuterSyntax.markup_command ThyOutput.Markup "header" "theory header" K.diag
  (P.doc_source >> IsarCmd.header_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "chapter" "chapter heading"
  K.thy_heading (P.opt_target -- P.doc_source >> IsarCmd.local_theory_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "section" "section heading"
  K.thy_heading (P.opt_target -- P.doc_source >> IsarCmd.local_theory_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "subsection" "subsection heading"
  K.thy_heading (P.opt_target -- P.doc_source >> IsarCmd.local_theory_markup);

val _ =
  OuterSyntax.markup_command ThyOutput.Markup "subsubsection" "subsubsection heading"
  K.thy_heading (P.opt_target -- P.doc_source >> IsarCmd.local_theory_markup);

val _ = OuterSyntax.markup_command ThyOutput.MarkupEnv "text" "formal comment (theory)"
  K.thy_decl (P.opt_target -- P.doc_source >> IsarCmd.local_theory_markup);

val _ = OuterSyntax.markup_command ThyOutput.Verbatim "text_raw" "raw document preparation text"
  K.thy_decl (P.opt_target -- P.doc_source >> IsarCmd.local_theory_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "sect" "formal comment (proof)"
  (K.tag_proof K.prf_heading) (P.doc_source >> IsarCmd.proof_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "subsect" "formal comment (proof)"
  (K.tag_proof K.prf_heading) (P.doc_source >> IsarCmd.proof_markup);

val _ = OuterSyntax.markup_command ThyOutput.Markup "subsubsect" "formal comment (proof)"
  (K.tag_proof K.prf_heading) (P.doc_source >> IsarCmd.proof_markup);

val _ = OuterSyntax.markup_command ThyOutput.MarkupEnv "txt" "formal comment (proof)"
  (K.tag_proof K.prf_decl) (P.doc_source >> IsarCmd.proof_markup);

val _ = OuterSyntax.markup_command ThyOutput.Verbatim "txt_raw"
  "raw document preparation text (proof)" (K.tag_proof K.prf_decl)
  (P.doc_source >> IsarCmd.proof_markup);



(** theory commands **)

(* classes and sorts *)

val _ =
  OuterSyntax.command "classes" "declare type classes" K.thy_decl
    (Scan.repeat1 (P.binding -- Scan.optional ((P.$$$ "\\<subseteq>" || P.$$$ "<") |--
        P.!!! (P.list1 P.xname)) []) >> (Toplevel.theory o fold AxClass.axiomatize_class_cmd));

val _ =
  OuterSyntax.command "classrel" "state inclusion of type classes (axiomatic!)" K.thy_decl
    (P.and_list1 (P.xname -- ((P.$$$ "\\<subseteq>" || P.$$$ "<") |-- P.!!! P.xname))
    >> (Toplevel.theory o AxClass.axiomatize_classrel_cmd));

val _ =
  OuterSyntax.command "defaultsort" "declare default sort" K.thy_decl
    (P.sort >> (Toplevel.theory o Sign.add_defsort));

val _ =
  OuterSyntax.command "axclass" "define axiomatic type class" K.thy_decl
    (P.binding -- Scan.optional ((P.$$$ "\\<subseteq>" || P.$$$ "<") |--
        P.!!! (P.list1 P.xname)) []
        -- Scan.repeat (SpecParse.thm_name ":" -- (P.prop >> single))
      >> (fn (x, y) => Toplevel.theory (snd o Class.axclass_cmd x y)));


(* types *)

val _ =
  OuterSyntax.command "typedecl" "type declaration" K.thy_decl
    (P.type_args -- P.binding -- P.opt_infix >> (fn ((args, a), mx) =>
      Toplevel.theory (ObjectLogic.typedecl (a, args, mx) #> snd)));

val _ =
  OuterSyntax.command "types" "declare type abbreviations" K.thy_decl
    (Scan.repeat1
      (P.type_args -- P.binding -- (P.$$$ "=" |-- P.!!! (P.typ -- P.opt_infix')))
      >> (Toplevel.theory o Sign.add_tyabbrs o
        map (fn ((args, a), (T, mx)) => (a, args, T, mx))));

val _ =
  OuterSyntax.command "nonterminals" "declare types treated as grammar nonterminal symbols"
    K.thy_decl (Scan.repeat1 P.binding >> (Toplevel.theory o Sign.add_nonterminals));

val _ =
  OuterSyntax.command "arities" "state type arities (axiomatic!)" K.thy_decl
    (Scan.repeat1 P.arity >> (Toplevel.theory o fold AxClass.axiomatize_arity_cmd));


(* consts and syntax *)

val _ =
  OuterSyntax.command "judgment" "declare object-logic judgment" K.thy_decl
    (P.const_binding >> (Toplevel.theory o ObjectLogic.add_judgment_cmd));

val _ =
  OuterSyntax.command "consts" "declare constants" K.thy_decl
    (Scan.repeat1 P.const_binding >> (Toplevel.theory o Sign.add_consts));

val opt_overloaded = P.opt_keyword "overloaded";

val _ =
  OuterSyntax.command "finalconsts" "declare constants as final" K.thy_decl
    (opt_overloaded -- Scan.repeat1 P.term >> (uncurry (Toplevel.theory oo Theory.add_finals)));

val mode_spec =
  (P.$$$ "output" >> K ("", false)) || P.name -- Scan.optional (P.$$$ "output" >> K false) true;

val opt_mode =
  Scan.optional (P.$$$ "(" |-- P.!!! (mode_spec --| P.$$$ ")")) Syntax.mode_default;

val _ =
  OuterSyntax.command "syntax" "declare syntactic constants" K.thy_decl
    (opt_mode -- Scan.repeat1 P.const >> (Toplevel.theory o uncurry Sign.add_modesyntax));

val _ =
  OuterSyntax.command "no_syntax" "delete syntax declarations" K.thy_decl
    (opt_mode -- Scan.repeat1 P.const >> (Toplevel.theory o uncurry Sign.del_modesyntax));


(* translations *)

val trans_pat =
  Scan.optional (P.$$$ "(" |-- P.!!! (P.xname --| P.$$$ ")")) "logic" -- P.string;

fun trans_arrow toks =
  ((P.$$$ "\\<rightharpoonup>" || P.$$$ "=>") >> K Syntax.ParseRule ||
    (P.$$$ "\\<leftharpoondown>" || P.$$$ "<=") >> K Syntax.PrintRule ||
    (P.$$$ "\\<rightleftharpoons>" || P.$$$ "==") >> K Syntax.ParsePrintRule) toks;

val trans_line =
  trans_pat -- P.!!! (trans_arrow -- trans_pat)
    >> (fn (left, (arr, right)) => arr (left, right));

val _ =
  OuterSyntax.command "translations" "declare syntax translation rules" K.thy_decl
    (Scan.repeat1 trans_line >> (Toplevel.theory o Sign.add_trrules));

val _ =
  OuterSyntax.command "no_translations" "remove syntax translation rules" K.thy_decl
    (Scan.repeat1 trans_line >> (Toplevel.theory o Sign.del_trrules));


(* axioms and definitions *)

val named_spec = SpecParse.thm_name ":" -- P.prop >> (fn ((x, y), z) => ((x, z), y));

val _ =
  OuterSyntax.command "axioms" "state arbitrary propositions (axiomatic!)" K.thy_decl
    (Scan.repeat1 named_spec >> (Toplevel.theory o IsarCmd.add_axioms));

val opt_unchecked_overloaded =
  Scan.optional (P.$$$ "(" |-- P.!!!
    (((P.$$$ "unchecked" >> K true) -- Scan.optional (P.$$$ "overloaded" >> K true) false ||
      P.$$$ "overloaded" >> K (false, true)) --| P.$$$ ")")) (false, false);

val _ =
  OuterSyntax.command "defs" "define constants" K.thy_decl
    (opt_unchecked_overloaded -- Scan.repeat1 named_spec
      >> (Toplevel.theory o IsarCmd.add_defs));


(* old constdefs *)

val old_constdecl =
  P.binding --| P.where_ >> (fn x => (x, NONE, NoSyn)) ||
  P.binding -- (P.$$$ "::" |-- P.!!! P.typ >> SOME) -- P.opt_mixfix'
    --| Scan.option P.where_ >> P.triple1 ||
  P.binding -- (P.mixfix >> pair NONE) --| Scan.option P.where_ >> P.triple2;

val old_constdef = Scan.option old_constdecl -- (SpecParse.opt_thm_name ":" -- P.prop);

val structs =
  Scan.optional ((P.$$$ "(" -- P.$$$ "structure") |-- P.!!! (P.simple_fixes --| P.$$$ ")")) [];

val _ =
  OuterSyntax.command "constdefs" "old-style constant definition" K.thy_decl
    (structs -- Scan.repeat1 old_constdef >> (Toplevel.theory o Constdefs.add_constdefs));


(* constant definitions and abbreviations *)

val _ =
  OuterSyntax.local_theory "definition" "constant definition" K.thy_decl
    (SpecParse.constdef >> (fn args => #2 o Specification.definition_cmd args));

val _ =
  OuterSyntax.local_theory "abbreviation" "constant abbreviation" K.thy_decl
    (opt_mode -- (Scan.option SpecParse.constdecl -- P.prop)
    >> (fn (mode, args) => Specification.abbreviation_cmd mode args));

val _ =
  OuterSyntax.local_theory "notation" "add notation for constants / fixed variables" K.thy_decl
    (opt_mode -- P.and_list1 (P.xname -- SpecParse.locale_mixfix)
    >> (fn (mode, args) => Specification.notation_cmd true mode args));

val _ =
  OuterSyntax.local_theory "no_notation" "delete notation for constants / fixed variables" K.thy_decl
    (opt_mode -- P.and_list1 (P.xname -- SpecParse.locale_mixfix)
    >> (fn (mode, args) => Specification.notation_cmd false mode args));


(* constant specifications *)

val _ =
  OuterSyntax.command "axiomatization" "axiomatic constant specification" K.thy_decl
    (Scan.optional P.fixes [] --
      Scan.optional (P.where_ |-- P.!!! (P.and_list1 SpecParse.specs)) []
    >> (fn (x, y) => Toplevel.theory (#2 o Specification.axiomatization_cmd x y)));


(* theorems *)

fun theorems kind =
  SpecParse.name_facts >> (fn args => #2 o Specification.theorems_cmd kind args);

val _ =
  OuterSyntax.local_theory "theorems" "define theorems" K.thy_decl (theorems Thm.theoremK);

val _ =
  OuterSyntax.local_theory "lemmas" "define lemmas" K.thy_decl (theorems Thm.lemmaK);

val _ =
  OuterSyntax.local_theory "declare" "declare theorems" K.thy_decl
    (P.and_list1 SpecParse.xthms1
      >> (fn args => #2 o Specification.theorems_cmd "" [(Attrib.empty_binding, flat args)]));


(* name space entry path *)

val _ =
  OuterSyntax.command "global" "disable prefixing of theory name" K.thy_decl
    (Scan.succeed (Toplevel.theory Sign.root_path));

val _ =
  OuterSyntax.command "local" "enable prefixing of theory name" K.thy_decl
    (Scan.succeed (Toplevel.theory Sign.local_path));

val _ =
  OuterSyntax.command "hide" "hide names from given name space" K.thy_decl
    ((P.opt_keyword "open" >> not) -- (P.name -- Scan.repeat1 P.xname) >>
      (Toplevel.theory o uncurry IsarCmd.hide_names));


(* use ML text *)

fun propagate_env (context as Context.Proof lthy) =
      Context.Proof (Local_Theory.map_contexts (ML_Env.inherit context) lthy)
  | propagate_env context = context;

fun propagate_env_prf prf = Proof.map_contexts
  (Context.proof_map (ML_Env.inherit (Context.Proof (Proof.context_of prf)))) prf;

val _ =
  OuterSyntax.command "use" "ML text from file" (K.tag_ml K.thy_decl)
    (P.path >> (fn path => Toplevel.generic_theory (ThyInfo.exec_file false path #> propagate_env)));

val _ =
  OuterSyntax.command "ML" "ML text within theory or local theory" (K.tag_ml K.thy_decl)
    (P.ML_source >> (fn (txt, pos) =>
      Toplevel.generic_theory
        (ML_Context.exec (fn () => ML_Context.eval true pos txt) #> propagate_env)));

val _ =
  OuterSyntax.command "ML_prf" "ML text within proof" (K.tag_proof K.prf_decl)
    (P.ML_source >> (fn (txt, pos) =>
      Toplevel.proof (Proof.map_context (Context.proof_map
        (ML_Context.exec (fn () => ML_Context.eval true pos txt))) #> propagate_env_prf)));

val _ =
  OuterSyntax.command "ML_val" "diagnostic ML text" (K.tag_ml K.diag)
    (P.ML_source >> IsarCmd.ml_diag true);

val _ =
  OuterSyntax.command "ML_command" "diagnostic ML text (silent)" (K.tag_ml K.diag)
    (P.ML_source >> (Toplevel.no_timing oo IsarCmd.ml_diag false));

val _ =
  OuterSyntax.command "setup" "ML theory setup" (K.tag_ml K.thy_decl)
    (P.ML_source >> (Toplevel.theory o IsarCmd.global_setup));

val _ =
  OuterSyntax.local_theory "local_setup" "ML local theory setup" (K.tag_ml K.thy_decl)
    (P.ML_source >> IsarCmd.local_setup);

val _ =
  OuterSyntax.command "attribute_setup" "define attribute in ML" (K.tag_ml K.thy_decl)
    (P.position P.name -- P.!!! (P.$$$ "=" |-- P.ML_source -- P.text)
    >> (fn (name, (txt, cmt)) => Toplevel.theory (Attrib.attribute_setup name txt cmt)));

val _ =
  OuterSyntax.command "method_setup" "define proof method in ML" (K.tag_ml K.thy_decl)
    (P.position P.name -- P.!!! (P.$$$ "=" |-- P.ML_source -- P.text)
    >> (fn (name, (txt, cmt)) => Toplevel.theory (Method.method_setup name txt cmt)));

val _ =
  OuterSyntax.local_theory "declaration" "generic ML declaration" (K.tag_ml K.thy_decl)
    (P.opt_keyword "pervasive" -- P.ML_source >> uncurry IsarCmd.declaration);

val _ =
  OuterSyntax.local_theory "simproc_setup" "define simproc in ML" (K.tag_ml K.thy_decl)
    (P.name -- (P.$$$ "(" |-- P.enum1 "|" P.term --| P.$$$ ")" --| P.$$$ "=") --
      P.ML_source -- Scan.optional (P.$$$ "identifier" |-- Scan.repeat1 P.xname) []
    >> (fn (((a, b), c), d) => IsarCmd.simproc_setup a b c d));


(* translation functions *)

val trfun = P.opt_keyword "advanced" -- P.ML_source;

val _ =
  OuterSyntax.command "parse_ast_translation" "install parse ast translation functions"
    (K.tag_ml K.thy_decl)
    (trfun >> (Toplevel.theory o IsarCmd.parse_ast_translation));

val _ =
  OuterSyntax.command "parse_translation" "install parse translation functions"
    (K.tag_ml K.thy_decl)
    (trfun >> (Toplevel.theory o IsarCmd.parse_translation));

val _ =
  OuterSyntax.command "print_translation" "install print translation functions"
    (K.tag_ml K.thy_decl)
    (trfun >> (Toplevel.theory o IsarCmd.print_translation));

val _ =
  OuterSyntax.command "typed_print_translation" "install typed print translation functions"
    (K.tag_ml K.thy_decl)
    (trfun >> (Toplevel.theory o IsarCmd.typed_print_translation));

val _ =
  OuterSyntax.command "print_ast_translation" "install print ast translation functions"
    (K.tag_ml K.thy_decl)
    (trfun >> (Toplevel.theory o IsarCmd.print_ast_translation));


(* oracles *)

val _ =
  OuterSyntax.command "oracle" "declare oracle" (K.tag_ml K.thy_decl)
    (P.position P.name -- (P.$$$ "=" |-- P.ML_source) >>
      (fn (x, y) => Toplevel.theory (IsarCmd.oracle x y)));


(* local theories *)

val _ =
  OuterSyntax.command "context" "enter local theory context" K.thy_decl
    (P.name --| P.begin >> (fn name =>
      Toplevel.print o Toplevel.begin_local_theory true (Theory_Target.context name)));


(* locales *)

val locale_val =
  SpecParse.locale_expression false --
    Scan.optional (P.$$$ "+" |-- P.!!! (Scan.repeat1 SpecParse.context_element)) [] ||
  Scan.repeat1 SpecParse.context_element >> pair ([], []);

val _ =
  OuterSyntax.command "locale" "define named proof context" K.thy_decl
    (P.binding -- Scan.optional (P.$$$ "=" |-- P.!!! locale_val) (([], []), []) -- P.opt_begin
      >> (fn ((name, (expr, elems)), begin) =>
          (begin ? Toplevel.print) o Toplevel.begin_local_theory begin
            (Expression.add_locale_cmd name Binding.empty expr elems #> snd)));

val _ =
  OuterSyntax.command "sublocale"
    "prove sublocale relation between a locale and a locale expression" K.thy_goal
    (P.xname --| (P.$$$ "\\<subseteq>" || P.$$$ "<") -- P.!!! (SpecParse.locale_expression false)
      >> (fn (loc, expr) =>
          Toplevel.print o Toplevel.theory_to_proof (Expression.sublocale_cmd loc expr)));

val _ =
  OuterSyntax.command "interpretation"
    "prove interpretation of locale expression in theory" K.thy_goal
    (P.!!! (SpecParse.locale_expression true) --
      Scan.optional (P.where_ |-- P.and_list1 (SpecParse.opt_thm_name ":" -- P.prop)) []
      >> (fn (expr, equations) => Toplevel.print o
          Toplevel.theory_to_proof (Expression.interpretation_cmd expr equations)));

val _ =
  OuterSyntax.command "interpret"
    "prove interpretation of locale expression in proof context"
    (K.tag_proof K.prf_goal)
    (P.!!! (SpecParse.locale_expression true)
      >> (fn expr => Toplevel.print o Toplevel.proof' (Expression.interpret_cmd expr)));


(* classes *)

val class_val =
  SpecParse.class_expr --
    Scan.optional (P.$$$ "+" |-- P.!!! (Scan.repeat1 SpecParse.context_element)) [] ||
  Scan.repeat1 SpecParse.context_element >> pair [];

val _ =
  OuterSyntax.command "class" "define type class" K.thy_decl
   (P.binding -- Scan.optional (P.$$$ "=" |-- class_val) ([], []) -- P.opt_begin
    >> (fn ((name, (supclasses, elems)), begin) =>
        (begin ? Toplevel.print) o Toplevel.begin_local_theory begin
          (Class.class_cmd name supclasses elems #> snd)));

val _ =
  OuterSyntax.local_theory_to_proof "subclass" "prove a subclass relation" K.thy_goal
    (P.xname >> Class.subclass_cmd);

val _ =
  OuterSyntax.command "instantiation" "instantiate and prove type arity" K.thy_decl
   (P.multi_arity --| P.begin
     >> (fn arities => Toplevel.print o
         Toplevel.begin_local_theory true (Theory_Target.instantiation_cmd arities)));

val _ =
  OuterSyntax.command "instance" "prove type arity or subclass relation" K.thy_goal
  ((P.xname -- ((P.$$$ "\\<subseteq>" || P.$$$ "<") |-- P.!!! P.xname) >> Class.classrel_cmd ||
    P.multi_arity >> Class.instance_arity_cmd)
    >> (Toplevel.print oo Toplevel.theory_to_proof)
  || Scan.succeed (Toplevel.print o Toplevel.local_theory_to_proof NONE (Class.instantiation_instance I)));


(* arbitrary overloading *)

val _ =
  OuterSyntax.command "overloading" "overloaded definitions" K.thy_decl
   (Scan.repeat1 (P.name --| (P.$$$ "\\<equiv>" || P.$$$ "==") -- P.term --
      Scan.optional (P.$$$ "(" |-- (P.$$$ "unchecked" >> K false) --| P.$$$ ")") true
      >> P.triple1) --| P.begin
   >> (fn operations => Toplevel.print o
         Toplevel.begin_local_theory true (Theory_Target.overloading_cmd operations)));


(* code generation *)

val _ =
  OuterSyntax.command "code_datatype" "define set of code datatype constructors" K.thy_decl
    (Scan.repeat1 P.term >> (Toplevel.theory o Code.add_datatype_cmd));



(** proof commands **)

(* statements *)

fun gen_theorem kind =
  OuterSyntax.local_theory_to_proof' kind ("state " ^ kind) K.thy_goal
    (Scan.optional (SpecParse.opt_thm_name ":" --|
      Scan.ahead (SpecParse.locale_keyword || SpecParse.statement_keyword)) Attrib.empty_binding --
      SpecParse.general_statement >> (fn (a, (elems, concl)) =>
        (Specification.theorem_cmd kind NONE (K I) a elems concl)));

val _ = gen_theorem Thm.theoremK;
val _ = gen_theorem Thm.lemmaK;
val _ = gen_theorem Thm.corollaryK;

val _ =
  OuterSyntax.command "have" "state local goal"
    (K.tag_proof K.prf_goal)
    (SpecParse.statement >> ((Toplevel.print oo Toplevel.proof') o IsarCmd.have));

val _ =
  OuterSyntax.command "hence" "abbreviates \"then have\""
    (K.tag_proof K.prf_goal)
    (SpecParse.statement >> ((Toplevel.print oo Toplevel.proof') o IsarCmd.hence));

val _ =
  OuterSyntax.command "show" "state local goal, solving current obligation"
    (K.tag_proof K.prf_asm_goal)
    (SpecParse.statement >> ((Toplevel.print oo Toplevel.proof') o IsarCmd.show));

val _ =
  OuterSyntax.command "thus" "abbreviates \"then show\""
    (K.tag_proof K.prf_asm_goal)
    (SpecParse.statement >> ((Toplevel.print oo Toplevel.proof') o IsarCmd.thus));


(* facts *)

val facts = P.and_list1 SpecParse.xthms1;

val _ =
  OuterSyntax.command "then" "forward chaining"
    (K.tag_proof K.prf_chain)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.chain));

val _ =
  OuterSyntax.command "from" "forward chaining from given facts"
    (K.tag_proof K.prf_chain)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.from_thmss)));

val _ =
  OuterSyntax.command "with" "forward chaining from given and current facts"
    (K.tag_proof K.prf_chain)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.with_thmss)));

val _ =
  OuterSyntax.command "note" "define facts"
    (K.tag_proof K.prf_decl)
    (SpecParse.name_facts >> (Toplevel.print oo (Toplevel.proof o Proof.note_thmss)));

val _ =
  OuterSyntax.command "using" "augment goal facts"
    (K.tag_proof K.prf_decl)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.using)));

val _ =
  OuterSyntax.command "unfolding" "unfold definitions in goal and facts"
    (K.tag_proof K.prf_decl)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.unfolding)));


(* proof context *)

val _ =
  OuterSyntax.command "fix" "fix local variables (Skolem constants)"
    (K.tag_proof K.prf_asm)
    (P.fixes >> (Toplevel.print oo (Toplevel.proof o Proof.fix)));

val _ =
  OuterSyntax.command "assume" "assume propositions"
    (K.tag_proof K.prf_asm)
    (SpecParse.statement >> (Toplevel.print oo (Toplevel.proof o Proof.assume)));

val _ =
  OuterSyntax.command "presume" "assume propositions, to be established later"
    (K.tag_proof K.prf_asm)
    (SpecParse.statement >> (Toplevel.print oo (Toplevel.proof o Proof.presume)));

val _ =
  OuterSyntax.command "def" "local definition"
    (K.tag_proof K.prf_asm)
    (P.and_list1
      (SpecParse.opt_thm_name ":" --
        ((P.binding -- P.opt_mixfix) -- ((P.$$$ "\\<equiv>" || P.$$$ "==") |-- P.!!! P.termp)))
    >> (Toplevel.print oo (Toplevel.proof o Proof.def)));

val _ =
  OuterSyntax.command "obtain" "generalized existence"
    (K.tag_proof K.prf_asm_goal)
    (P.parname -- Scan.optional (P.fixes --| P.where_) [] -- SpecParse.statement
      >> (fn ((x, y), z) => Toplevel.print o Toplevel.proof' (Obtain.obtain x y z)));

val _ =
  OuterSyntax.command "guess" "wild guessing (unstructured)"
    (K.tag_proof K.prf_asm_goal)
    (Scan.optional P.fixes [] >> (Toplevel.print oo (Toplevel.proof' o Obtain.guess)));

val _ =
  OuterSyntax.command "let" "bind text variables"
    (K.tag_proof K.prf_decl)
    (P.and_list1 (P.and_list1 P.term -- (P.$$$ "=" |-- P.term))
      >> (Toplevel.print oo (Toplevel.proof o Proof.let_bind)));

val case_spec =
  (P.$$$ "(" |-- P.!!! (P.xname -- Scan.repeat1 (P.maybe P.name) --| P.$$$ ")") ||
    P.xname >> rpair []) -- SpecParse.opt_attribs >> P.triple1;

val _ =
  OuterSyntax.command "case" "invoke local context"
    (K.tag_proof K.prf_asm)
    (case_spec >> (Toplevel.print oo (Toplevel.proof o Proof.invoke_case)));


(* proof structure *)

val _ =
  OuterSyntax.command "{" "begin explicit proof block"
    (K.tag_proof K.prf_open)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.begin_block));

val _ =
  OuterSyntax.command "}" "end explicit proof block"
    (K.tag_proof K.prf_close)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.end_block));

val _ =
  OuterSyntax.command "next" "enter next proof block"
    (K.tag_proof K.prf_block)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.next_block));


(* end proof *)

val _ =
  OuterSyntax.command "qed" "conclude (sub-)proof"
    (K.tag_proof K.qed_block)
    (Scan.option Method.parse >> IsarCmd.qed);

val _ =
  OuterSyntax.command "by" "terminal backward proof"
    (K.tag_proof K.qed)
    (Method.parse -- Scan.option Method.parse >> IsarCmd.terminal_proof);

val _ =
  OuterSyntax.command ".." "default proof"
    (K.tag_proof K.qed)
    (Scan.succeed IsarCmd.default_proof);

val _ =
  OuterSyntax.command "." "immediate proof"
    (K.tag_proof K.qed)
    (Scan.succeed IsarCmd.immediate_proof);

val _ =
  OuterSyntax.command "done" "done proof"
    (K.tag_proof K.qed)
    (Scan.succeed IsarCmd.done_proof);

val _ =
  OuterSyntax.command "sorry" "skip proof (quick-and-dirty mode only!)"
    (K.tag_proof K.qed)
    (Scan.succeed IsarCmd.skip_proof);

val _ =
  OuterSyntax.command "oops" "forget proof"
    (K.tag_proof K.qed_global)
    (Scan.succeed Toplevel.forget_proof);


(* proof steps *)

val _ =
  OuterSyntax.command "defer" "shuffle internal proof state"
    (K.tag_proof K.prf_script)
    (Scan.option P.nat >> (Toplevel.print oo (Toplevel.proofs o Proof.defer)));

val _ =
  OuterSyntax.command "prefer" "shuffle internal proof state"
    (K.tag_proof K.prf_script)
    (P.nat >> (Toplevel.print oo (Toplevel.proofs o Proof.prefer)));

val _ =
  OuterSyntax.command "apply" "initial refinement step (unstructured)"
    (K.tag_proof K.prf_script)
    (Method.parse >> (Toplevel.print oo (Toplevel.proofs o Proof.apply)));

val _ =
  OuterSyntax.command "apply_end" "terminal refinement (unstructured)"
    (K.tag_proof K.prf_script)
    (Method.parse >> (Toplevel.print oo (Toplevel.proofs o Proof.apply_end)));

val _ =
  OuterSyntax.command "proof" "backward proof"
    (K.tag_proof K.prf_block)
    (Scan.option Method.parse >> (fn m => Toplevel.print o
      Toplevel.actual_proof (Proof_Node.applys (Proof.proof m)) o
      Toplevel.skip_proof (fn i => i + 1)));


(* calculational proof commands *)

val calc_args =
  Scan.option (P.$$$ "(" |-- P.!!! ((SpecParse.xthms1 --| P.$$$ ")")));

val _ =
  OuterSyntax.command "also" "combine calculation and current facts"
    (K.tag_proof K.prf_decl)
    (calc_args >> (Toplevel.proofs' o Calculation.also));

val _ =
  OuterSyntax.command "finally" "combine calculation and current facts, exhibit result"
    (K.tag_proof K.prf_chain)
    (calc_args >> (Toplevel.proofs' o Calculation.finally));

val _ =
  OuterSyntax.command "moreover" "augment calculation by current facts"
    (K.tag_proof K.prf_decl)
    (Scan.succeed (Toplevel.proof' Calculation.moreover));

val _ =
  OuterSyntax.command "ultimately" "augment calculation by current facts, exhibit result"
    (K.tag_proof K.prf_chain)
    (Scan.succeed (Toplevel.proof' Calculation.ultimately));


(* proof navigation *)

val _ =
  OuterSyntax.command "back" "backtracking of proof command"
    (K.tag_proof K.prf_script)
    (Scan.succeed (Toplevel.print o Toplevel.actual_proof Proof_Node.back o Toplevel.skip_proof I));


(* nested commands *)

val props_text =
  Scan.optional ValueParse.properties [] -- P.position P.string >> (fn (props, (str, pos)) =>
    (Position.of_properties (Position.default_properties pos props), str));

val _ =
  OuterSyntax.improper_command "Isabelle.command" "nested Isabelle command" K.control
    (props_text :|-- (fn (pos, str) =>
      (case OuterSyntax.parse pos str of
        [tr] => Scan.succeed (K tr)
      | _ => Scan.fail_with (K "exactly one command expected"))
      handle ERROR msg => Scan.fail_with (K msg)));



(** diagnostic commands (for interactive mode only) **)

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];
val opt_bang = Scan.optional (P.$$$ "!" >> K true) false;

val _ =
  OuterSyntax.improper_command "pretty_setmargin" "change default margin for pretty printing"
    K.diag (P.nat >> (Toplevel.no_timing oo IsarCmd.pretty_setmargin));

val _ =
  OuterSyntax.improper_command "help" "print outer syntax commands" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative OuterSyntax.print_outer_syntax));

val _ =
  OuterSyntax.improper_command "print_commands" "print outer syntax commands" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.imperative OuterSyntax.print_outer_syntax));

val _ =
  OuterSyntax.improper_command "print_configs" "print configuration options" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_configs));

val _ =
  OuterSyntax.improper_command "print_context" "print theory context name" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_context));

val _ =
  OuterSyntax.improper_command "print_theory" "print logical theory contents (verbose!)" K.diag
    (opt_bang >> (Toplevel.no_timing oo IsarCmd.print_theory));

val _ =
  OuterSyntax.improper_command "print_syntax" "print inner syntax of context (verbose!)" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_syntax));

val _ =
  OuterSyntax.improper_command "print_abbrevs" "print constant abbreviation of context" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_abbrevs));

val _ =
  OuterSyntax.improper_command "print_theorems"
      "print theorems of local theory or proof context" K.diag
    (opt_bang >> (Toplevel.no_timing oo IsarCmd.print_theorems));

val _ =
  OuterSyntax.improper_command "print_locales" "print locales of this theory" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_locales));

val _ =
  OuterSyntax.improper_command "print_classes" "print classes of this theory" K.diag
    (Scan.succeed (Toplevel.no_timing o Toplevel.unknown_theory
      o Toplevel.keep (Class.print_classes o Toplevel.theory_of)));

val _ =
  OuterSyntax.improper_command "print_locale" "print locale of this theory" K.diag
    (opt_bang -- P.xname >> (Toplevel.no_timing oo IsarCmd.print_locale));

val _ =
  OuterSyntax.improper_command "print_interps"
    "print interpretations of locale for this theory" K.diag
    (P.xname >> (Toplevel.no_timing oo IsarCmd.print_registrations));

val _ =
  OuterSyntax.improper_command "print_attributes" "print attributes of this theory" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_attributes));

val _ =
  OuterSyntax.improper_command "print_simpset" "print context of Simplifier" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_simpset));

val _ =
  OuterSyntax.improper_command "print_rules" "print intro/elim rules" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_rules));

val _ =
  OuterSyntax.improper_command "print_trans_rules" "print transitivity rules" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_trans_rules));

val _ =
  OuterSyntax.improper_command "print_methods" "print methods of this theory" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_methods));

val _ =
  OuterSyntax.improper_command "print_antiquotations" "print antiquotations (global)" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_antiquotations));

val _ =
  OuterSyntax.improper_command "thy_deps" "visualize theory dependencies"
    K.diag (Scan.succeed (Toplevel.no_timing o IsarCmd.thy_deps));

val _ =
  OuterSyntax.improper_command "class_deps" "visualize class dependencies"
    K.diag (Scan.succeed (Toplevel.no_timing o IsarCmd.class_deps));

val _ =
  OuterSyntax.improper_command "thm_deps" "visualize theorem dependencies"
    K.diag (SpecParse.xthms1 >> (Toplevel.no_timing oo IsarCmd.thm_deps));

val _ =
  OuterSyntax.improper_command "print_binds" "print term bindings of proof context" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_binds));

val _ =
  OuterSyntax.improper_command "print_facts" "print facts of proof context" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_facts));

val _ =
  OuterSyntax.improper_command "print_cases" "print cases of proof context" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_cases));

val _ =
  OuterSyntax.improper_command "print_statement" "print theorems as long statements" K.diag
    (opt_modes -- SpecParse.xthms1 >> (Toplevel.no_timing oo IsarCmd.print_stmts));

val _ =
  OuterSyntax.improper_command "thm" "print theorems" K.diag
    (opt_modes -- SpecParse.xthms1 >> (Toplevel.no_timing oo IsarCmd.print_thms));

val _ =
  OuterSyntax.improper_command "prf" "print proof terms of theorems" K.diag
    (opt_modes -- Scan.option SpecParse.xthms1
      >> (Toplevel.no_timing oo IsarCmd.print_prfs false));

val _ =
  OuterSyntax.improper_command "full_prf" "print full proof terms of theorems" K.diag
    (opt_modes -- Scan.option SpecParse.xthms1 >> (Toplevel.no_timing oo IsarCmd.print_prfs true));

val _ =
  OuterSyntax.improper_command "prop" "read and print proposition" K.diag
    (opt_modes -- P.term >> (Toplevel.no_timing oo IsarCmd.print_prop));

val _ =
  OuterSyntax.improper_command "term" "read and print term" K.diag
    (opt_modes -- P.term >> (Toplevel.no_timing oo IsarCmd.print_term));

val _ =
  OuterSyntax.improper_command "typ" "read and print type" K.diag
    (opt_modes -- P.typ >> (Toplevel.no_timing oo IsarCmd.print_type));

val _ =
  OuterSyntax.improper_command "print_codesetup" "print code generator setup" K.diag
    (Scan.succeed
      (Toplevel.no_timing o Toplevel.unknown_theory o Toplevel.keep
        (Code.print_codesetup o Toplevel.theory_of)));

val _ =
  OuterSyntax.improper_command "unused_thms" "find unused theorems" K.diag
    (Scan.option ((Scan.repeat1 (Scan.unless P.minus P.name) --| P.minus) --
       Scan.option (Scan.repeat1 (Scan.unless P.minus P.name))) >>
         (Toplevel.no_timing oo IsarCmd.unused_thms));



(** system commands (for interactive mode only) **)

val _ =
  OuterSyntax.improper_command "cd" "change current working directory" K.diag
    (P.path >> (Toplevel.no_timing oo IsarCmd.cd));

val _ =
  OuterSyntax.improper_command "pwd" "print current working directory" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.pwd));

val _ =
  OuterSyntax.improper_command "use_thy" "use theory file" K.diag
    (P.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => ThyInfo.use_thy name)));

val _ =
  OuterSyntax.improper_command "touch_thy" "outdate theory, including descendants" K.diag
    (P.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => ThyInfo.touch_thy name)));

val _ =
  OuterSyntax.improper_command "remove_thy" "remove theory from loader database" K.diag
    (P.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => ThyInfo.remove_thy name)));

val _ =
  OuterSyntax.improper_command "kill_thy" "kill theory -- try to remove from loader database"
    K.diag (P.name >> (fn name =>
      Toplevel.no_timing o Toplevel.imperative (fn () => ThyInfo.kill_thy name)));

val _ =
  OuterSyntax.improper_command "display_drafts" "display raw source files with symbols"
    K.diag (Scan.repeat1 P.path >> (Toplevel.no_timing oo IsarCmd.display_drafts));

val _ =
  OuterSyntax.improper_command "print_drafts" "print raw source files with symbols"
    K.diag (Scan.repeat1 P.path >> (Toplevel.no_timing oo IsarCmd.print_drafts));

val opt_limits =
  Scan.option P.nat -- Scan.option (P.$$$ "," |-- P.!!! P.nat);

val _ =
  OuterSyntax.improper_command "pr" "print current proof state (if present)" K.diag
    (opt_modes -- opt_limits >> (Toplevel.no_timing oo IsarCmd.pr));

val _ =
  OuterSyntax.improper_command "disable_pr" "disable printing of toplevel state" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.disable_pr));

val _ =
  OuterSyntax.improper_command "enable_pr" "enable printing of toplevel state" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.enable_pr));

val _ =
  OuterSyntax.improper_command "commit" "commit current session to ML database" K.diag
    (P.opt_unit >> K (Toplevel.no_timing o Toplevel.imperative Secure.commit));

val _ =
  OuterSyntax.improper_command "quit" "quit Isabelle" K.control
    (P.opt_unit >> (Toplevel.no_timing oo K IsarCmd.quit));

val _ =
  OuterSyntax.improper_command "exit" "exit Isar loop" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.exit));

end;

