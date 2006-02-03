(*  Title:      Pure/Isar/isar_syn.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar/Pure outer syntax.
*)

structure IsarSyn: sig end =
struct

structure P = OuterParse and K = OuterKeyword;


(** init and exit **)

val theoryP =
  OuterSyntax.command "theory" "begin theory" (K.tag_theory K.thy_begin)
    (ThyHeader.args >> (Toplevel.print oo IsarThy.theory));

val end_excursionP =
  OuterSyntax.command "end" "end current excursion" (K.tag_theory K.thy_end)
    (Scan.succeed (Toplevel.print o Toplevel.exit));

val contextP =
  OuterSyntax.improper_command "context" "switch theory context" (K.tag_theory K.thy_switch)
    (P.name >> (Toplevel.print oo IsarThy.context));



(** markup commands **)

val headerP = OuterSyntax.markup_command IsarOutput.Markup "header" "theory header" K.diag
  (P.position P.text >> IsarCmd.add_header);

val chapterP = OuterSyntax.markup_command IsarOutput.Markup "chapter" "chapter heading"
  K.thy_heading (P.opt_locale_target -- P.position P.text >> IsarCmd.add_chapter);

val sectionP = OuterSyntax.markup_command IsarOutput.Markup "section" "section heading"
  K.thy_heading (P.opt_locale_target -- P.position P.text >> IsarCmd.add_section);

val subsectionP = OuterSyntax.markup_command IsarOutput.Markup "subsection" "subsection heading"
  K.thy_heading (P.opt_locale_target -- P.position P.text >> IsarCmd.add_subsection);

val subsubsectionP =
  OuterSyntax.markup_command IsarOutput.Markup "subsubsection" "subsubsection heading"
  K.thy_heading (P.opt_locale_target -- P.position P.text >> IsarCmd.add_subsubsection);

val textP = OuterSyntax.markup_command IsarOutput.MarkupEnv "text" "formal comment (theory)"
  K.thy_decl (P.opt_locale_target -- P.position P.text >> IsarCmd.add_text);

val text_rawP = OuterSyntax.markup_command IsarOutput.Verbatim "text_raw"
  "raw document preparation text"
  K.thy_decl (P.position P.text >> IsarCmd.add_text_raw);

val sectP = OuterSyntax.markup_command IsarOutput.Markup "sect" "formal comment (proof)"
  (K.tag_proof K.prf_heading) (P.position P.text >> IsarCmd.add_sect);

val subsectP = OuterSyntax.markup_command IsarOutput.Markup "subsect" "formal comment (proof)"
  (K.tag_proof K.prf_heading) (P.position P.text >> IsarCmd.add_subsect);

val subsubsectP = OuterSyntax.markup_command IsarOutput.Markup "subsubsect"
  "formal comment (proof)" (K.tag_proof K.prf_heading)
  (P.position P.text >> IsarCmd.add_subsubsect);

val txtP = OuterSyntax.markup_command IsarOutput.MarkupEnv "txt" "formal comment (proof)"
  (K.tag_proof K.prf_decl) (P.position P.text >> IsarCmd.add_txt);

val txt_rawP = OuterSyntax.markup_command IsarOutput.Verbatim "txt_raw"
  "raw document preparation text (proof)" (K.tag_proof K.prf_decl)
  (P.position P.text >> IsarCmd.add_txt_raw);



(** theory sections **)

(* classes and sorts *)

val classesP =
  OuterSyntax.command "classes" "declare type classes" K.thy_decl
    (Scan.repeat1 (P.name -- Scan.optional ((P.$$$ "\\<subseteq>" || P.$$$ "<") |--
        P.!!! (P.list1 P.xname)) []) >> (Toplevel.theory o Theory.add_classes));

val classrelP =
  OuterSyntax.command "classrel" "state inclusion of type classes (axiomatic!)" K.thy_decl
    (P.and_list1 (P.xname -- ((P.$$$ "\\<subseteq>" || P.$$$ "<") |-- P.!!! P.xname))
    >> (Toplevel.theory o Theory.add_classrel));

val defaultsortP =
  OuterSyntax.command "defaultsort" "declare default sort" K.thy_decl
    (P.sort >> (Toplevel.theory o Theory.add_defsort));


(* types *)

val typedeclP =
  OuterSyntax.command "typedecl" "type declaration" K.thy_decl
    (P.type_args -- P.name -- P.opt_infix >> (fn ((args, a), mx) =>
      Toplevel.theory (Theory.add_typedecls [(a, args, mx)])));

val typeabbrP =
  OuterSyntax.command "types" "declare type abbreviations" K.thy_decl
    (Scan.repeat1
      (P.type_args -- P.name -- (P.$$$ "=" |-- P.!!! (P.typ -- P.opt_infix')))
      >> (Toplevel.theory o Theory.add_tyabbrs o
        map (fn ((args, a), (T, mx)) => (a, args, T, mx))));

val nontermP =
  OuterSyntax.command "nonterminals" "declare types treated as grammar nonterminal symbols"
    K.thy_decl (Scan.repeat1 P.name >> (Toplevel.theory o Theory.add_nonterminals));

val aritiesP =
  OuterSyntax.command "arities" "state type arities (axiomatic!)" K.thy_decl
    (Scan.repeat1 (P.xname -- (P.$$$ "::" |-- P.!!! P.arity) >> P.triple2)
      >> (Toplevel.theory o Theory.add_arities));


(* consts and syntax *)

val judgmentP =
  OuterSyntax.command "judgment" "declare object-logic judgment" K.thy_decl
    (P.const >> (Toplevel.theory o ObjectLogic.add_judgment));

val constsP =
  OuterSyntax.command "consts" "declare constants" K.thy_decl
    (Scan.repeat1 P.const >> (Toplevel.theory o Theory.add_consts));

val opt_overloaded = P.opt_keyword "overloaded";

val finalconstsP =
  OuterSyntax.command "finalconsts" "declare constants as final" K.thy_decl
    (opt_overloaded -- Scan.repeat1 P.term >> (uncurry (Toplevel.theory oo Theory.add_finals)));

val mode_spec =
  (P.$$$ "output" >> K ("", false)) || P.name -- Scan.optional (P.$$$ "output" >> K false) true;

val opt_mode =
  Scan.optional (P.$$$ "(" |-- P.!!! (mode_spec --| P.$$$ ")")) Syntax.default_mode;

val syntaxP =
  OuterSyntax.command "syntax" "declare syntactic constants" K.thy_decl
    (opt_mode -- Scan.repeat1 P.const >> (Toplevel.theory o uncurry Theory.add_modesyntax));

val no_syntaxP =
  OuterSyntax.command "no_syntax" "delete syntax declarations" K.thy_decl
    (opt_mode -- Scan.repeat1 P.const >> (Toplevel.theory o uncurry Theory.del_modesyntax));


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

val translationsP =
  OuterSyntax.command "translations" "declare syntax translation rules" K.thy_decl
    (Scan.repeat1 trans_line >> (Toplevel.theory o Theory.add_trrules));


(* axioms and definitions *)

val axiomsP =
  OuterSyntax.command "axioms" "state arbitrary propositions (axiomatic!)" K.thy_decl
    (Scan.repeat1 P.spec_name >> (Toplevel.theory o IsarThy.add_axioms));

val defsP =
  OuterSyntax.command "defs" "define constants" K.thy_decl
    (opt_overloaded -- Scan.repeat1 P.spec_name >> (Toplevel.theory o IsarThy.add_defs));


(* constant definitions *)

val structs =
  Scan.optional ((P.$$$ "(" -- P.$$$ "structure") |-- P.!!! (P.simple_fixes --| P.$$$ ")")) [];

val constdecl =
  (P.name --| P.$$$ "where") >> (fn x => (x, NONE, NoSyn)) ||
    P.name -- (P.$$$ "::" |-- P.!!! P.typ >> SOME) -- P.opt_mixfix' >> P.triple1 ||
    P.name -- (P.mixfix >> pair NONE) >> P.triple2;
val constdef = Scan.option constdecl -- (P.opt_thm_name ":" -- P.prop);

val constdefsP =
  OuterSyntax.command "constdefs" "old-style constant definitions" K.thy_decl
    (structs -- Scan.repeat1 constdef >> (Toplevel.theory o Constdefs.add_constdefs));

val definitionP =
  OuterSyntax.command "definition" "standard constant definition" K.thy_decl
    (P.opt_locale_target -- Scan.repeat1 constdef
    >> (fn (x, y) => Toplevel.theory_context (#2 o Specification.definition x y)));


(* constant specifications *)

val axiomatizationP =
  OuterSyntax.command "axiomatization" "axiomatic constant specification" K.thy_decl
    (P.opt_locale_target --
      Scan.optional P.fixes [] --
      Scan.optional (P.$$$ "where" |-- P.!!! (P.and_list1 P.spec)) []
    >> (fn ((x, y), z) => Toplevel.theory_context (#2 o Specification.axiomatization x y z)));


(* theorems *)

fun theorems kind = P.opt_locale_target -- P.name_facts
  >> (Toplevel.theory_context o uncurry (IsarThy.smart_theorems kind));

val theoremsP =
  OuterSyntax.command "theorems" "define theorems" K.thy_decl (theorems PureThy.theoremK);

val lemmasP =
  OuterSyntax.command "lemmas" "define lemmas" K.thy_decl (theorems PureThy.lemmaK);

val declareP =
  OuterSyntax.command "declare" "declare theorems (improper)" K.thy_script
    (P.opt_locale_target -- (P.and_list1 P.xthms1 >> List.concat)
      >> (Toplevel.theory_context o uncurry IsarThy.declare_theorems));


(* name space entry path *)

val globalP =
  OuterSyntax.command "global" "disable prefixing of theory name" K.thy_decl
    (Scan.succeed (Toplevel.theory Sign.root_path));

val localP =
  OuterSyntax.command "local" "enable prefixing of theory name" K.thy_decl
    (Scan.succeed (Toplevel.theory Sign.local_path));

val hideP =
  OuterSyntax.command "hide" "hide names from given name space" K.thy_decl
    ((P.opt_keyword "open" >> not) -- (P.name -- Scan.repeat1 P.xname) >>
      (Toplevel.theory o uncurry Sign.hide_names));


(* use ML text *)

val useP =
  OuterSyntax.command "use" "eval ML text from file" (K.tag_ml K.diag)
    (P.path >> (Toplevel.no_timing oo IsarCmd.use));

val mlP =
  OuterSyntax.command "ML" "eval ML text (diagnostic)" (K.tag_ml K.diag)
    (P.text >> IsarCmd.use_mltext true);

val ml_commandP =
  OuterSyntax.command "ML_command" "eval ML text" (K.tag_ml K.diag)
    (P.text >> (Toplevel.no_timing oo IsarCmd.use_mltext false));

val ml_setupP =
  OuterSyntax.command "ML_setup" "eval ML text (may change theory)" (K.tag_ml K.thy_decl)
    (P.text >> IsarCmd.use_mltext_theory);

val setupP =
  OuterSyntax.command "setup" "apply ML theory setup" (K.tag_ml K.thy_decl)
    (Scan.option P.text >> (Toplevel.theory o PureThy.generic_setup));

val method_setupP =
  OuterSyntax.command "method_setup" "define proof method in ML" (K.tag_ml K.thy_decl)
    (((P.name -- P.!!! (P.$$$ "=" |-- P.text -- P.text) >> P.triple2))
      >> (Toplevel.theory o Method.method_setup));


(* translation functions *)

val trfun = P.opt_keyword "advanced" -- P.text;

val parse_ast_translationP =
  OuterSyntax.command "parse_ast_translation" "install parse ast translation functions"
    (K.tag_ml K.thy_decl)
    (trfun >> (Toplevel.theory o Sign.parse_ast_translation));

val parse_translationP =
  OuterSyntax.command "parse_translation" "install parse translation functions"
    (K.tag_ml K.thy_decl)
    (trfun >> (Toplevel.theory o Sign.parse_translation));

val print_translationP =
  OuterSyntax.command "print_translation" "install print translation functions"
    (K.tag_ml K.thy_decl)
    (trfun >> (Toplevel.theory o Sign.print_translation));

val typed_print_translationP =
  OuterSyntax.command "typed_print_translation" "install typed print translation functions"
    (K.tag_ml K.thy_decl)
    (trfun >> (Toplevel.theory o Sign.typed_print_translation));

val print_ast_translationP =
  OuterSyntax.command "print_ast_translation" "install print ast translation functions"
    (K.tag_ml K.thy_decl)
    (trfun >> (Toplevel.theory o Sign.print_ast_translation));

val token_translationP =
  OuterSyntax.command "token_translation" "install token translation functions"
    (K.tag_ml K.thy_decl)
    (P.text >> (Toplevel.theory o Sign.token_translation));


(* oracles *)

val oracleP =
  OuterSyntax.command "oracle" "declare oracle" (K.tag_ml K.thy_decl)
    (P.name -- (P.$$$ "(" |-- P.text --| P.$$$ ")" --| P.$$$ "=")
      -- P.text >> (Toplevel.theory o PureThy.add_oracle o P.triple1));


(* locales *)

val locale_val =
  (P.locale_expr --
    Scan.optional (P.$$$ "+" |-- P.!!! (Scan.repeat1 P.context_element)) [] ||
  Scan.repeat1 P.context_element >> pair Locale.empty);

val localeP =
  OuterSyntax.command "locale" "define named proof context" K.thy_decl
    ((P.opt_keyword "open" >> not) -- P.name
        -- Scan.optional (P.$$$ "=" |-- P.!!! locale_val) (Locale.empty, [])
      >> (Toplevel.theory_context o (fn ((is_open, name), (expr, elems)) =>
          Locale.add_locale is_open name expr elems)));

val opt_inst =
  Scan.optional (P.$$$ "[" |-- P.!!! (Scan.repeat1 (P.maybe P.term) --| P.$$$ "]")) [];

val interpretationP =
  OuterSyntax.command "interpretation"
    "prove and register interpretation of locale expression in theory or locale" K.thy_goal
    (P.xname --| (P.$$$ "\\<subseteq>" || P.$$$ "<") -- P.!!! P.locale_expr
      >> (Toplevel.print oo (Toplevel.theory_to_proof o Locale.interpretation_in_locale)) ||
     P.opt_thm_name ":" -- P.locale_expr -- opt_inst >> (fn ((x, y), z) =>
      Toplevel.print o Toplevel.theory_to_proof (Locale.interpretation x y z)));

val interpretP =
  OuterSyntax.command "interpret"
    "prove and register interpretation of locale expression in proof context"
    (K.tag_proof K.prf_goal)
    (P.opt_thm_name ":" -- P.locale_expr -- opt_inst >> (fn ((x, y), z) =>
      Toplevel.print o Toplevel.proof' (Locale.interpret x y z)));



(** proof commands **)

(* statements *)

fun gen_theorem kind =
  OuterSyntax.command kind ("state " ^ kind) K.thy_goal
    (P.opt_locale_target -- Scan.optional (P.opt_thm_name ":" --|
      Scan.ahead (P.locale_keyword || P.statement_keyword)) ("", []) --
      P.general_statement >> (fn ((x, y), (z, w)) =>
      (Toplevel.print o Toplevel.theory_to_proof (Locale.smart_theorem kind x y z w))));

val theoremP = gen_theorem PureThy.theoremK;
val lemmaP = gen_theorem PureThy.lemmaK;
val corollaryP = gen_theorem PureThy.corollaryK;

val haveP =
  OuterSyntax.command "have" "state local goal"
    (K.tag_proof K.prf_goal)
    (P.statement >> ((Toplevel.print oo Toplevel.proof') o IsarThy.have));

val henceP =
  OuterSyntax.command "hence" "abbreviates \"then have\""
    (K.tag_proof K.prf_goal)
    (P.statement >> ((Toplevel.print oo Toplevel.proof') o IsarThy.hence));

val showP =
  OuterSyntax.command "show" "state local goal, solving current obligation"
    (K.tag_proof K.prf_goal)
    (P.statement >> ((Toplevel.print oo Toplevel.proof') o IsarThy.show));

val thusP =
  OuterSyntax.command "thus" "abbreviates \"then show\""
    (K.tag_proof K.prf_goal)
    (P.statement >> ((Toplevel.print oo Toplevel.proof') o IsarThy.thus));


(* facts *)

val facts = P.and_list1 P.xthms1;

val thenP =
  OuterSyntax.command "then" "forward chaining"
    (K.tag_proof K.prf_chain)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.chain));

val fromP =
  OuterSyntax.command "from" "forward chaining from given facts"
    (K.tag_proof K.prf_chain)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.from_thmss)));

val withP =
  OuterSyntax.command "with" "forward chaining from given and current facts"
    (K.tag_proof K.prf_chain)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.with_thmss)));

val noteP =
  OuterSyntax.command "note" "define facts"
    (K.tag_proof K.prf_decl)
    (P.name_facts >> (Toplevel.print oo (Toplevel.proof o Proof.note_thmss)));

val usingP =
  OuterSyntax.command "using" "augment goal facts"
    (K.tag_proof K.prf_decl)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.using)));

val unfoldingP =
  OuterSyntax.command "unfolding" "unfold definitions in goal and facts"
    (K.tag_proof K.prf_decl)
    (facts >> (Toplevel.print oo (Toplevel.proof o Proof.unfolding)));


(* proof context *)

val fixP =
  OuterSyntax.command "fix" "fix local variables (Skolem constants)"
    (K.tag_proof K.prf_asm)
    (P.simple_fixes >> (Toplevel.print oo (Toplevel.proof o Proof.fix)));

val assumeP =
  OuterSyntax.command "assume" "assume propositions"
    (K.tag_proof K.prf_asm)
    (P.statement >> (Toplevel.print oo (Toplevel.proof o Proof.assume)));

val presumeP =
  OuterSyntax.command "presume" "assume propositions, to be established later"
    (K.tag_proof K.prf_asm)
    (P.statement >> (Toplevel.print oo (Toplevel.proof o Proof.presume)));

val defP =
  OuterSyntax.command "def" "local definition"
    (K.tag_proof K.prf_asm)
    (P.and_list1
      (P.opt_thm_name ":" -- (P.name -- ((P.$$$ "\\<equiv>" || P.$$$ "==") |-- P.!!! P.termp)))
    >> (Toplevel.print oo (Toplevel.proof o Proof.def)));

val obtainP =
  OuterSyntax.command "obtain" "generalized existence"
    (K.tag_proof K.prf_asm_goal)
    (P.parname -- Scan.optional (P.simple_fixes --| P.$$$ "where") [] -- P.statement
      >> (fn ((x, y), z) => Toplevel.print o Toplevel.proof' (Obtain.obtain x y z)));

val guessP =
  OuterSyntax.command "guess" "wild guessing (unstructured)"
    (K.tag_proof K.prf_asm_goal)
    (Scan.optional P.simple_fixes [] >> (Toplevel.print oo (Toplevel.proof' o Obtain.guess)));

val letP =
  OuterSyntax.command "let" "bind text variables"
    (K.tag_proof K.prf_decl)
    (P.and_list1 (P.enum1 "and" P.term -- (P.$$$ "=" |-- P.term))
      >> (Toplevel.print oo (Toplevel.proof o Proof.let_bind)));

val case_spec =
  (P.$$$ "(" |-- P.!!! (P.xname -- Scan.repeat1 (P.maybe P.name) --| P.$$$ ")") ||
    P.xname >> rpair []) -- P.opt_attribs >> P.triple1;

val caseP =
  OuterSyntax.command "case" "invoke local context"
    (K.tag_proof K.prf_asm)
    (case_spec >> (Toplevel.print oo (Toplevel.proof o Proof.invoke_case)));


(* proof structure *)

val beginP =
  OuterSyntax.command "{" "begin explicit proof block"
    (K.tag_proof K.prf_open)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.begin_block));

val endP =
  OuterSyntax.command "}" "end explicit proof block"
    (K.tag_proof K.prf_close)
    (Scan.succeed (Toplevel.print o Toplevel.proofs Proof.end_block));

val nextP =
  OuterSyntax.command "next" "enter next proof block"
    (K.tag_proof K.prf_block)
    (Scan.succeed (Toplevel.print o Toplevel.proof Proof.next_block));


(* end proof *)

val qedP =
  OuterSyntax.command "qed" "conclude (sub-)proof"
    (K.tag_proof K.qed_block)
    (Scan.option P.method >> (Toplevel.print3 oo IsarThy.qed));

val terminal_proofP =
  OuterSyntax.command "by" "terminal backward proof"
    (K.tag_proof K.qed)
    (P.method -- Scan.option P.method >> (Toplevel.print3 oo IsarThy.terminal_proof));

val default_proofP =
  OuterSyntax.command ".." "default proof"
    (K.tag_proof K.qed)
    (Scan.succeed (Toplevel.print3 o IsarThy.default_proof));

val immediate_proofP =
  OuterSyntax.command "." "immediate proof"
    (K.tag_proof K.qed)
    (Scan.succeed (Toplevel.print3 o IsarThy.immediate_proof));

val done_proofP =
  OuterSyntax.command "done" "done proof"
    (K.tag_proof K.qed)
    (Scan.succeed (Toplevel.print3 o IsarThy.done_proof));

val skip_proofP =
  OuterSyntax.improper_command "sorry" "skip proof (quick-and-dirty mode only!)"
    (K.tag_proof K.qed)
    (Scan.succeed (Toplevel.print3 o IsarThy.skip_proof));

val forget_proofP =
  OuterSyntax.command "oops" "forget proof"
    (K.tag_proof K.qed_global)
    (Scan.succeed Toplevel.forget_proof);


(* proof steps *)

val deferP =
  OuterSyntax.command "defer" "shuffle internal proof state"
    (K.tag_proof K.prf_script)
    (Scan.option P.nat >> (Toplevel.print oo (Toplevel.proofs o Proof.defer)));

val preferP =
  OuterSyntax.command "prefer" "shuffle internal proof state"
    (K.tag_proof K.prf_script)
    (P.nat >> (Toplevel.print oo (Toplevel.proofs o Proof.prefer)));

val applyP =
  OuterSyntax.command "apply" "initial refinement step (unstructured)"
    (K.tag_proof K.prf_script)
    (P.method >> (Toplevel.print oo (Toplevel.proofs o Proof.apply)));

val apply_endP =
  OuterSyntax.command "apply_end" "terminal refinement (unstructured)"
    (K.tag_proof K.prf_script)
    (P.method >> (Toplevel.print oo (Toplevel.proofs o Proof.apply_end)));

val proofP =
  OuterSyntax.command "proof" "backward proof"
    (K.tag_proof K.prf_block)
    (Scan.option P.method >> (fn m => Toplevel.print o
      Toplevel.actual_proof (ProofHistory.applys (Proof.proof m)) o
      Toplevel.skip_proof (History.apply (fn i => i + 1))));


(* calculational proof commands *)

val calc_args =
  Scan.option (P.$$$ "(" |-- P.!!! ((P.xthms1 --| P.$$$ ")")));

val alsoP =
  OuterSyntax.command "also" "combine calculation and current facts"
    (K.tag_proof K.prf_decl)
    (calc_args >> (Toplevel.proofs' o Calculation.also));

val finallyP =
  OuterSyntax.command "finally" "combine calculation and current facts, exhibit result"
    (K.tag_proof K.prf_chain)
    (calc_args >> (Toplevel.proofs' o Calculation.finally));

val moreoverP =
  OuterSyntax.command "moreover" "augment calculation by current facts"
    (K.tag_proof K.prf_decl)
    (Scan.succeed (Toplevel.proof' Calculation.moreover));

val ultimatelyP =
  OuterSyntax.command "ultimately" "augment calculation by current facts, exhibit result"
    (K.tag_proof K.prf_chain)
    (Scan.succeed (Toplevel.proof' Calculation.ultimately));


(* proof navigation *)

val backP =
  OuterSyntax.command "back" "backtracking of proof command"
    (K.tag_proof K.prf_script)
    (Scan.succeed (Toplevel.print o IsarCmd.back));


(* history *)

val cannot_undoP =
  OuterSyntax.improper_command "cannot_undo" "report 'cannot undo' error message" K.control
    (P.name >> (Toplevel.no_timing oo IsarCmd.cannot_undo));

val clear_undosP =
  OuterSyntax.improper_command "clear_undos" "clear theory-level undo information" K.control
    (P.nat >> (Toplevel.no_timing oo IsarCmd.clear_undos_theory));

val redoP =
  OuterSyntax.improper_command "redo" "redo last command" K.control
    (Scan.succeed (Toplevel.no_timing o Toplevel.print o IsarCmd.redo));

val undos_proofP =
  OuterSyntax.improper_command "undos_proof" "undo last proof commands" K.control
    (P.nat >> ((Toplevel.no_timing o Toplevel.print) oo IsarCmd.undos_proof));

val undoP =
  OuterSyntax.improper_command "undo" "undo last command" K.control
    (Scan.succeed ((Toplevel.no_timing o Toplevel.print) o IsarCmd.undo));

val killP =
  OuterSyntax.improper_command "kill" "kill current history node" K.control
    (Scan.succeed ((Toplevel.no_timing o Toplevel.print) o IsarCmd.kill));



(** diagnostic commands (for interactive mode only) **)

val opt_modes = Scan.optional (P.$$$ "(" |-- P.!!! (Scan.repeat1 P.xname --| P.$$$ ")")) [];


val pretty_setmarginP =
  OuterSyntax.improper_command "pretty_setmargin" "change default margin for pretty printing"
    K.diag (P.nat >> (Toplevel.no_timing oo IsarCmd.pretty_setmargin));

val print_commandsP =
  OuterSyntax.improper_command "print_commands" "print outer syntax (global)" K.diag
    (Scan.succeed (Toplevel.no_timing o OuterSyntax.print_commands));

val print_contextP =
  OuterSyntax.improper_command "print_context" "print theory context name" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_context));

val print_theoryP =
  OuterSyntax.improper_command "print_theory" "print logical theory contents (verbose!)" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_theory));

val print_syntaxP =
  OuterSyntax.improper_command "print_syntax" "print inner syntax of theory (verbose!)" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_syntax));

val print_theoremsP =
  OuterSyntax.improper_command "print_theorems"
      "print theorems of local theory or proof context" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_theorems));

val print_localesP =
  OuterSyntax.improper_command "print_locales" "print locales of this theory" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_locales));

val print_localeP =
  OuterSyntax.improper_command "print_locale" "print locale expression in this theory" K.diag
    (Scan.optional (P.$$$ "!" >> K true) false -- locale_val
      >> (Toplevel.no_timing oo IsarCmd.print_locale));

val print_registrationsP =
  OuterSyntax.improper_command "print_interps"
    "print interpretations of named locale" K.diag
    (Scan.optional (P.$$$ "!" >> K true) false -- P.xname
      >> (Toplevel.no_timing oo uncurry IsarCmd.print_registrations));

val print_attributesP =
  OuterSyntax.improper_command "print_attributes" "print attributes of this theory" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_attributes));

val print_simpsetP =
  OuterSyntax.improper_command "print_simpset" "print context of Simplifier" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_simpset));

val print_rulesP =
  OuterSyntax.improper_command "print_rules" "print intro/elim rules" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_rules));

val print_induct_rulesP =
  OuterSyntax.improper_command "print_induct_rules" "print induction and cases rules" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_induct_rules));

val print_trans_rulesP =
  OuterSyntax.improper_command "print_trans_rules" "print transitivity rules" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_trans_rules));

val print_methodsP =
  OuterSyntax.improper_command "print_methods" "print methods of this theory" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_methods));

val print_antiquotationsP =
  OuterSyntax.improper_command "print_antiquotations" "print antiquotations (global)" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_antiquotations));

val thm_depsP =
  OuterSyntax.improper_command "thm_deps" "visualize theorem dependencies"
    K.diag (P.xthms1 >> (Toplevel.no_timing oo IsarCmd.thm_deps));

val criterion =
  P.reserved "name" |-- P.!!! (P.$$$ ":" |-- P.xname) >> FindTheorems.Name ||
  P.reserved "intro" >> K FindTheorems.Intro ||
  P.reserved "elim" >> K FindTheorems.Elim ||
  P.reserved "dest" >> K FindTheorems.Dest ||
  P.reserved "simp" |-- P.!!! (P.$$$ ":" |-- P.term) >> FindTheorems.Simp ||
  P.term >> FindTheorems.Pattern;

val find_theoremsP =
  OuterSyntax.improper_command "find_theorems"
    "print theorems meeting specified criteria" K.diag
    (Scan.option (P.$$$ "(" |-- P.!!! (P.nat --| P.$$$ ")")) --
     Scan.repeat (((Scan.option P.minus >> is_none) -- criterion))
      >> (Toplevel.no_timing oo IsarCmd.find_theorems));

val print_bindsP =
  OuterSyntax.improper_command "print_binds" "print term bindings of proof context" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_binds));

val print_lthmsP =
  OuterSyntax.improper_command "print_facts" "print facts of proof context" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_lthms));

val print_casesP =
  OuterSyntax.improper_command "print_cases" "print cases of proof context" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.print_cases));

val print_thmsP =
  OuterSyntax.improper_command "thm" "print theorems" K.diag
    (opt_modes -- P.xthms1 >> (Toplevel.no_timing oo IsarCmd.print_thms));

val print_prfsP =
  OuterSyntax.improper_command "prf" "print proof terms of theorems" K.diag
    (opt_modes -- Scan.option P.xthms1 >> (Toplevel.no_timing oo IsarCmd.print_prfs false));

val print_full_prfsP =
  OuterSyntax.improper_command "full_prf" "print full proof terms of theorems" K.diag
    (opt_modes -- Scan.option P.xthms1 >> (Toplevel.no_timing oo IsarCmd.print_prfs true));

val print_propP =
  OuterSyntax.improper_command "prop" "read and print proposition" K.diag
    (opt_modes -- P.term >> (Toplevel.no_timing oo IsarCmd.print_prop));

val print_termP =
  OuterSyntax.improper_command "term" "read and print term" K.diag
    (opt_modes -- P.term >> (Toplevel.no_timing oo IsarCmd.print_term));

val print_typeP =
  OuterSyntax.improper_command "typ" "read and print type" K.diag
    (opt_modes -- P.typ >> (Toplevel.no_timing oo IsarCmd.print_type));



(** system commands (for interactive mode only) **)

val cdP =
  OuterSyntax.improper_command "cd" "change current working directory" K.diag
    (P.path >> (Toplevel.no_timing oo IsarCmd.cd));

val pwdP =
  OuterSyntax.improper_command "pwd" "print current working directory" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.pwd));

val use_thyP =
  OuterSyntax.improper_command "use_thy" "use theory file" K.diag
    (P.name >> (Toplevel.no_timing oo IsarCmd.use_thy));

val use_thy_onlyP =
  OuterSyntax.improper_command "use_thy_only" "use theory file only, ignoring associated ML"
    K.diag (P.name >> (Toplevel.no_timing oo IsarCmd.use_thy_only));

val update_thyP =
  OuterSyntax.improper_command "update_thy" "update theory file" K.diag
    (P.name >> (Toplevel.no_timing oo IsarCmd.update_thy));

val update_thy_onlyP =
  OuterSyntax.improper_command "update_thy_only" "update theory file, ignoring associated ML"
    K.diag (P.name >> (Toplevel.no_timing oo IsarCmd.update_thy_only));

val touch_thyP =
  OuterSyntax.improper_command "touch_thy" "outdate theory, including descendants" K.diag
    (P.name >> (Toplevel.no_timing oo IsarCmd.touch_thy));

val touch_all_thysP =
  OuterSyntax.improper_command "touch_all_thys" "outdate all non-finished theories" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.touch_all_thys));

val touch_child_thysP =
  OuterSyntax.improper_command "touch_child_thys" "outdate child theories" K.diag
    (P.name >> (Toplevel.no_timing oo IsarCmd.touch_child_thys));

val remove_thyP =
  OuterSyntax.improper_command "remove_thy" "remove theory from loader database" K.diag
    (P.name >> (Toplevel.no_timing oo IsarCmd.remove_thy));

val kill_thyP =
  OuterSyntax.improper_command "kill_thy" "kill theory -- try to remove from loader database"
    K.diag (P.name >> (Toplevel.no_timing oo IsarCmd.kill_thy));

val display_draftsP =
  OuterSyntax.improper_command "display_drafts" "display raw source files with symbols"
    K.diag (Scan.repeat1 P.path >> (Toplevel.no_timing oo IsarCmd.display_drafts));

val print_draftsP =
  OuterSyntax.improper_command "print_drafts" "print raw source files with symbols"
    K.diag (Scan.repeat1 P.path >> (Toplevel.no_timing oo IsarCmd.print_drafts));

val opt_limits =
  Scan.option P.nat -- Scan.option (P.$$$ "," |-- P.!!! P.nat);

val prP =
  OuterSyntax.improper_command "pr" "print current proof state (if present)" K.diag
    (opt_modes -- opt_limits >> (Toplevel.no_timing oo IsarCmd.pr));

val disable_prP =
  OuterSyntax.improper_command "disable_pr" "disable printing of toplevel state" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.disable_pr));

val enable_prP =
  OuterSyntax.improper_command "enable_pr" "enable printing of toplevel state" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.enable_pr));

val commitP =
  OuterSyntax.improper_command "commit" "commit current session to ML database" K.diag
    (P.opt_unit >> (Toplevel.no_timing oo K IsarCmd.use_commit));

val quitP =
  OuterSyntax.improper_command "quit" "quit Isabelle" K.control
    (P.opt_unit >> (Toplevel.no_timing oo K IsarCmd.quit));

val exitP =
  OuterSyntax.improper_command "exit" "exit Isar loop" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.exit));

val init_toplevelP =
  OuterSyntax.improper_command "init_toplevel" "restart Isar toplevel loop" K.control
    (Scan.succeed (Toplevel.no_timing o IsarCmd.init_toplevel));

val welcomeP =
  OuterSyntax.improper_command "welcome" "print welcome message" K.diag
    (Scan.succeed (Toplevel.no_timing o IsarCmd.welcome));



(** the Pure outer syntax **)

(*keep keywords consistent with the parsers, including those in
  outer_parse.ML, otherwise be prepared for unexpected errors*)

val _ = OuterSyntax.add_keywords
 ["!", "!!", "%", "(", ")", "+", ",", "--", ":", "::", ";", "<", "<=",
  "=", "==", "=>", "?", "[", "]", "advanced", "and", "assumes",
  "begin", "binder", "concl", "constrains", "defines", "fixes",
  "imports", "in", "includes", "infix", "infixl", "infixr", "is",
  "notes", "obtains", "open", "output", "overloaded", "shows",
  "structure", "uses", "where", "|", "\\<equiv>",
  "\\<leftharpoondown>", "\\<rightharpoonup>",
  "\\<rightleftharpoons>", "\\<subseteq>"];

val _ = OuterSyntax.add_parsers [
  (*theory structure*)
  theoryP, end_excursionP, contextP,
  (*markup commands*)
  headerP, chapterP, sectionP, subsectionP, subsubsectionP, textP,
  text_rawP, sectP, subsectP, subsubsectP, txtP, txt_rawP,
  (*theory sections*)
  classesP, classrelP, defaultsortP, typedeclP, typeabbrP, nontermP,
  aritiesP, judgmentP, constsP, finalconstsP, syntaxP, no_syntaxP,
  translationsP, axiomsP, defsP, constdefsP, definitionP,
  axiomatizationP, theoremsP, lemmasP, declareP, globalP, localP,
  hideP, useP, mlP, ml_commandP, ml_setupP, setupP, method_setupP,
  parse_ast_translationP, parse_translationP, print_translationP,
  typed_print_translationP, print_ast_translationP,
  token_translationP, oracleP, localeP,
  (*proof commands*)
  theoremP, lemmaP, corollaryP, haveP, henceP, showP, thusP, fixP,
  assumeP, presumeP, defP, obtainP, guessP, letP, caseP, thenP, fromP,
  withP, noteP, usingP, unfoldingP, beginP, endP, nextP, qedP,
  terminal_proofP, default_proofP, immediate_proofP, done_proofP,
  skip_proofP, forget_proofP, deferP, preferP, applyP, apply_endP,
  proofP, alsoP, finallyP, moreoverP, ultimatelyP, backP,
  cannot_undoP, clear_undosP, redoP, undos_proofP, undoP, killP,
  interpretationP, interpretP,
  (*diagnostic commands*)
  pretty_setmarginP,
  print_commandsP, print_contextP, print_theoryP, print_syntaxP,
  print_theoremsP, print_localesP, print_localeP,
  print_registrationsP, print_attributesP, print_simpsetP,
  print_rulesP, print_induct_rulesP, print_trans_rulesP,
  print_methodsP, print_antiquotationsP, thm_depsP, find_theoremsP,
  print_bindsP, print_lthmsP, print_casesP, print_thmsP, print_prfsP,
  print_full_prfsP, print_propP, print_termP, print_typeP,
  (*system commands*)
  cdP, pwdP, use_thyP, use_thy_onlyP, update_thyP, update_thy_onlyP,
  touch_thyP, touch_all_thysP, touch_child_thysP, remove_thyP,
  kill_thyP, display_draftsP, print_draftsP, prP, disable_prP,
  enable_prP, commitP, quitP, exitP, init_toplevelP, welcomeP];

end;
