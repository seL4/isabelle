(*  Title:      Pure/Isar/isar_syn.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar/Pure outer syntax.
*)

signature ISAR_SYN =
sig
  val keywords: string list
  val parsers: OuterSyntax.parser list
end;

structure IsarSyn: ISAR_SYN =
struct

structure P = OuterParse and K = OuterSyntax.Keyword;


(** init and exit **)

val theoryP =
  OuterSyntax.command "theory" "begin theory" K.thy_begin
    (OuterSyntax.theory_header >> (Toplevel.print oo IsarThy.theory));

val end_excursionP =
  OuterSyntax.command "end" "end current excursion" K.thy_end
    (Scan.succeed (Toplevel.print o Toplevel.exit));

val kill_excursionP =
  OuterSyntax.improper_command "kill" "kill current excursion" K.control
    (Scan.succeed (Toplevel.print o Toplevel.kill));

val contextP =
  OuterSyntax.improper_command "context" "switch theory context" K.thy_switch
    (P.name >> (Toplevel.print oo IsarThy.context));



(** markup commands **)

val headerP = OuterSyntax.markup_command "header" "theory header" K.diag
  (P.comment >> IsarThy.add_header);

val chapterP = OuterSyntax.markup_command "chapter" "chapter heading" K.thy_heading
  (P.comment >> (Toplevel.theory o IsarThy.add_chapter));

val sectionP = OuterSyntax.markup_command "section" "section heading" K.thy_heading
  (P.comment >> (Toplevel.theory o IsarThy.add_section));

val subsectionP = OuterSyntax.markup_command "subsection" "subsection heading" K.thy_heading
  (P.comment >> (Toplevel.theory o IsarThy.add_subsection));

val subsubsectionP =
  OuterSyntax.markup_command "subsubsection" "subsubsection heading" K.thy_heading
    (P.comment >> (Toplevel.theory o IsarThy.add_subsubsection));

val textP = OuterSyntax.markup_command "text" "formal comment (theory)" K.thy_decl
  (P.comment >> (Toplevel.theory o IsarThy.add_text));

val text_rawP = OuterSyntax.verbatim_command "text_raw" "raw document preparation text"
  K.thy_decl (P.comment >> (Toplevel.theory o IsarThy.add_text_raw));


val sectP = OuterSyntax.markup_command "sect" "formal comment (proof)" K.prf_decl
  (P.comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.add_sect)));

val subsectP = OuterSyntax.markup_command "subsect" "formal comment (proof)" K.prf_decl
  (P.comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.add_subsect)));

val subsubsectP = OuterSyntax.markup_command "subsubsect" "formal comment (proof)" K.prf_decl
  (P.comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.add_subsubsect)));

val txtP = OuterSyntax.markup_command "txt" "formal comment (proof)" K.prf_decl
  (P.comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.add_txt)));

val txt_rawP = OuterSyntax.verbatim_command "txt_raw" "raw document preparation text (proof)"
  K.prf_decl (P.comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.add_txt_raw)));



(** theory sections **)

(* classes and sorts *)

val classesP =
  OuterSyntax.command "classes" "declare type classes" K.thy_decl
    (Scan.repeat1 (P.name -- Scan.optional (P.$$$ "<" |-- P.!!! (P.list1 P.xname)) [])
      -- P.marg_comment >> (Toplevel.theory o IsarThy.add_classes));

val classrelP =
  OuterSyntax.command "classrel" "state inclusion of type classes (axiomatic!)" K.thy_decl
    (P.xname -- (P.$$$ "<" |-- P.!!! P.xname) -- P.marg_comment
      >> (Toplevel.theory o IsarThy.add_classrel));

val defaultsortP =
  OuterSyntax.command "defaultsort" "declare default sort" K.thy_decl
    (P.sort -- P.marg_comment >> (Toplevel.theory o IsarThy.add_defsort));


(* types *)

val typedeclP =
  OuterSyntax.command "typedecl" "Pure type declaration" K.thy_decl
    (P.type_args -- P.name -- P.opt_infix -- P.marg_comment >> (fn (((args, a), mx), cmt) =>
      Toplevel.theory (IsarThy.add_typedecl ((a, args, mx), cmt))));

val typeabbrP =
  OuterSyntax.command "types" "declare type abbreviations" K.thy_decl
    (Scan.repeat1
      (P.type_args -- P.name -- (P.$$$ "=" |-- P.!!! (P.typ -- P.opt_infix)) -- P.marg_comment)
      >> (Toplevel.theory o IsarThy.add_tyabbrs o
        map (fn (((args, a), (T, mx)), cmt) => ((a, args, T, mx), cmt))));

val nontermP =
  OuterSyntax.command "nonterminals" "declare types treated as grammar nonterminal symbols"
    K.thy_decl (Scan.repeat1 (P.name -- P.marg_comment)
      >> (Toplevel.theory o IsarThy.add_nonterminals));

val aritiesP =
  OuterSyntax.command "arities" "state type arities (axiomatic!)" K.thy_decl
    (Scan.repeat1 ((P.xname -- (P.$$$ "::" |-- P.!!! P.arity) >> P.triple2) -- P.marg_comment)
      >> (Toplevel.theory o IsarThy.add_arities));


(* consts and syntax *)

val judgmentP =
  OuterSyntax.command "judgment" "declare object-logic judgment" K.thy_decl
    (P.const -- P.marg_comment >> (Toplevel.theory o IsarThy.add_judgment));

val constsP =
  OuterSyntax.command "consts" "declare constants" K.thy_decl
    (Scan.repeat1 (P.const -- P.marg_comment) >> (Toplevel.theory o IsarThy.add_consts));

val opt_mode =
  Scan.optional
    (P.$$$ "(" |-- P.!!! (P.name -- Scan.optional (P.$$$ "output" >> K false) true --| P.$$$ ")"))
    ("", true);

val syntaxP =
  OuterSyntax.command "syntax" "declare syntactic constants" K.thy_decl
    (opt_mode -- Scan.repeat1 (P.const -- P.marg_comment)
      >> (Toplevel.theory o uncurry IsarThy.add_modesyntax));


(* translations *)

val trans_pat =
  Scan.optional (P.$$$ "(" |-- P.!!! (P.xname --| P.$$$ ")")) "logic" -- P.string;

fun trans_arrow toks =
  (P.$$$ "=>" >> K Syntax.ParseRule ||
    P.$$$ "<=" >> K Syntax.PrintRule ||
    P.$$$ "==" >> K Syntax.ParsePrintRule) toks;

val trans_line =
  trans_pat -- P.!!! (trans_arrow -- trans_pat)
    >> (fn (left, (arr, right)) => arr (left, right));

val translationsP =
  OuterSyntax.command "translations" "declare syntax translation rules" K.thy_decl
    (Scan.repeat1 (trans_line -- P.marg_comment) >> (Toplevel.theory o IsarThy.add_trrules));


(* axioms and definitions *)

val axiomsP =
  OuterSyntax.command "axioms" "state arbitrary propositions (axiomatic!)" K.thy_decl
    (Scan.repeat1 (P.spec_name -- P.marg_comment) >> (Toplevel.theory o IsarThy.add_axioms));

val defsP =
  OuterSyntax.command "defs" "define constants" K.thy_decl
    (Scan.repeat1 (P.spec_name -- P.marg_comment) >> (Toplevel.theory o IsarThy.add_defs));

val constdefsP =
  OuterSyntax.command "constdefs" "declare and define constants" K.thy_decl
    (Scan.repeat1 ((P.const -- P.marg_comment) -- (P.term -- P.marg_comment))
      >> (Toplevel.theory o IsarThy.add_constdefs));


(* theorems *)

val facts = P.opt_thm_name "=" -- P.xthms1;

val theoremsP =
  OuterSyntax.command "theorems" "define theorems" K.thy_decl
    (facts -- P.marg_comment >> (Toplevel.theory o IsarThy.have_theorems));

val lemmasP =
  OuterSyntax.command "lemmas" "define lemmas" K.thy_decl
    (facts -- P.marg_comment >> (Toplevel.theory o IsarThy.have_lemmas));


(* name space entry path *)

val globalP =
  OuterSyntax.command "global" "disable prefixing of theory name" K.thy_decl
    (Scan.succeed (Toplevel.theory PureThy.global_path));

val localP =
  OuterSyntax.command "local" "enable prefixing of theory name" K.thy_decl
    (Scan.succeed (Toplevel.theory PureThy.local_path));


(* use ML text *)

val useP =
  OuterSyntax.command "use" "eval ML text from file" K.diag
    (P.name >> IsarCmd.use);

val mlP =
  OuterSyntax.command "ML" "eval ML text (diagnostic)" K.diag
    (P.text >> IsarCmd.use_mltext true);

val ml_commandP =
  OuterSyntax.command "ML_command" "eval ML text" K.diag
    (P.text >> IsarCmd.use_mltext false);

val ml_setupP =
  OuterSyntax.command "ML_setup" "eval ML text (may change theory)" K.thy_decl
    (P.text >> IsarCmd.use_mltext_theory);

val setupP =
  OuterSyntax.command "setup" "apply ML theory setup" K.thy_decl
    (P.text >> (Toplevel.theory o Context.use_setup));


(* translation functions *)

val parse_ast_translationP =
  OuterSyntax.command "parse_ast_translation" "install parse ast translation functions" K.thy_decl
    (P.text >> (Toplevel.theory o IsarThy.parse_ast_translation));

val parse_translationP =
  OuterSyntax.command "parse_translation" "install parse translation functions" K.thy_decl
    (P.text >> (Toplevel.theory o IsarThy.parse_translation));

val print_translationP =
  OuterSyntax.command "print_translation" "install print translation functions" K.thy_decl
    (P.text >> (Toplevel.theory o IsarThy.print_translation));

val typed_print_translationP =
  OuterSyntax.command "typed_print_translation" "install typed print translation functions"
    K.thy_decl (P.text >> (Toplevel.theory o IsarThy.typed_print_translation));

val print_ast_translationP =
  OuterSyntax.command "print_ast_translation" "install print ast translation functions" K.thy_decl
    (P.text >> (Toplevel.theory o IsarThy.print_ast_translation));

val token_translationP =
  OuterSyntax.command "token_translation" "install token translation functions" K.thy_decl
    (P.text >> (Toplevel.theory o IsarThy.token_translation));


(* oracles *)

val oracleP =
  OuterSyntax.command "oracle" "install oracle" K.thy_decl
    ((P.name --| P.$$$ "=") -- P.text -- P.marg_comment >> (Toplevel.theory o IsarThy.add_oracle));



(** proof commands **)

(* statements *)

fun statement f = (P.opt_thm_name ":" -- P.propp >> P.triple1) -- P.marg_comment >> f;

val theoremP =
  OuterSyntax.command "theorem" "state theorem" K.thy_goal
    (statement IsarThy.theorem >> (fn f => Toplevel.print o Toplevel.theory_to_proof f));

val lemmaP =
  OuterSyntax.command "lemma" "state lemma" K.thy_goal
    (statement IsarThy.lemma >> (fn f => Toplevel.print o Toplevel.theory_to_proof f));

val showP =
  OuterSyntax.command "show" "state local goal, solving current obligation" K.prf_goal
    (statement IsarThy.show >> (fn f => Toplevel.print o Toplevel.proof f));

val haveP =
  OuterSyntax.command "have" "state local goal" K.prf_goal
    (statement IsarThy.have >> (fn f => Toplevel.print o Toplevel.proof f));

val thusP =
  OuterSyntax.command "thus" "abbreviates \"then show\"" K.prf_goal
    (statement IsarThy.thus >> (fn f => Toplevel.print o Toplevel.proof f));

val henceP =
  OuterSyntax.command "hence" "abbreviates \"then have\"" K.prf_goal
    (statement IsarThy.hence >> (fn f => Toplevel.print o Toplevel.proof f));


(* facts *)

val thenP =
  OuterSyntax.command "then" "forward chaining" K.prf_chain
    (P.marg_comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.chain)));

val thenceP =
  OuterSyntax.command "thence" "forward chaining, including full export (EXPERIMENTAL!)" K.prf_chain
    (P.marg_comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.export_chain)));

val fromP =
  OuterSyntax.command "from" "forward chaining from given facts" K.prf_chain
    (P.xthms1 -- P.marg_comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.from_facts)));

val withP =
  OuterSyntax.command "with" "forward chaining from given and current facts" K.prf_chain
    (P.xthms1 -- P.marg_comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.with_facts)));

val noteP =
  OuterSyntax.command "note" "define facts" K.prf_decl
    (facts -- P.marg_comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.have_facts)));


(* proof context *)

val assumeP =
  OuterSyntax.command "assume" "assume propositions" K.prf_asm
    (P.and_list1 ((P.opt_thm_name ":" -- Scan.repeat1 P.propp >> P.triple1) -- P.marg_comment)
      >> (Toplevel.print oo (Toplevel.proof o IsarThy.assume)));

val presumeP =
  OuterSyntax.command "presume" "assume propositions, to be established later" K.prf_asm
    (P.and_list1 ((P.opt_thm_name ":" -- Scan.repeat1 P.propp >> P.triple1) -- P.marg_comment)
      >> (Toplevel.print oo (Toplevel.proof o IsarThy.presume)));

val defP =
  OuterSyntax.command "def" "local definition" K.prf_asm
    ((P.opt_thm_name ":" -- (P.name -- Scan.option (P.$$$ "::" |-- P.typ) --
      (P.$$$ "==" |-- P.termp)) >> P.triple1) -- P.marg_comment
      >> (Toplevel.print oo (Toplevel.proof o IsarThy.local_def)));

val fixP =
  OuterSyntax.command "fix" "fix variables (Skolem constants)" K.prf_asm
    (P.and_list1 (Scan.repeat1 P.name -- Scan.option (P.$$$ "::" |-- P.typ) -- P.marg_comment)
      >> (Toplevel.print oo (Toplevel.proof o IsarThy.fix)));

val letP =
  OuterSyntax.command "let" "bind text variables" K.prf_decl
    (P.and_list1 (P.enum1 "as" P.term -- (P.$$$ "=" |-- P.term) -- P.marg_comment)
      >> (Toplevel.print oo (Toplevel.proof o IsarThy.match_bind)));

val caseP =
  OuterSyntax.command "case" "invoke local context" K.prf_asm
    (P.xname -- P.marg_comment >> (Toplevel.print oo (Toplevel.proof o IsarThy.invoke_case)));


(* proof structure *)

val beginP =
  OuterSyntax.command "{{" "begin explicit proof block" K.prf_block
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.begin_block));

val endP =
  OuterSyntax.command "}}" "end explicit proof block" K.prf_block
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.end_block));

val nextP =
  OuterSyntax.command "next" "enter next proof block" K.prf_block
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.next_block));


(* end proof *)

val qedP =
  OuterSyntax.command "qed" "conclude (sub-)proof" K.qed_block
    (Scan.option (P.method -- P.interest) -- P.marg_comment >> IsarThy.qed);

val terminal_proofP =
  OuterSyntax.command "by" "terminal backward proof" K.qed
    (P.method -- P.interest -- Scan.option (P.method -- P.interest)
      -- P.marg_comment >> IsarThy.terminal_proof);

val immediate_proofP =
  OuterSyntax.command "." "immediate proof" K.qed
    (P.marg_comment >> IsarThy.immediate_proof);

val default_proofP =
  OuterSyntax.command ".." "default proof" K.qed
    (P.marg_comment >> IsarThy.default_proof);

val skip_proofP =
  OuterSyntax.improper_command "sorry" "skip proof (quick-and-dirty mode only!)" K.qed
    (P.marg_comment >> IsarThy.skip_proof);

val forget_proofP =
  OuterSyntax.improper_command "oops" "forget proof" K.qed_global
    (P.marg_comment >> IsarThy.forget_proof);



(* proof steps *)

val deferP =
  OuterSyntax.command "defer" "shuffle internal proof state"
    K.prf_script (Scan.option P.nat >> (Toplevel.print oo (Toplevel.proof o IsarThy.defer)));

val preferP =
  OuterSyntax.command "prefer" "shuffle internal proof state"
    K.prf_script (P.nat >> (Toplevel.print oo (Toplevel.proof o IsarThy.prefer)));

val applyP =
  OuterSyntax.command "apply" "initial refinement step (unstructured)"
    K.prf_script (P.method >> (Toplevel.print oo (Toplevel.proof o IsarThy.apply)));

val apply_endP =
  OuterSyntax.command "apply_end" "terminal refinement (unstructured)"
    K.prf_script (P.method >> (Toplevel.print oo (Toplevel.proof o IsarThy.apply_end)));

val proofP =
  OuterSyntax.command "proof" "backward proof" K.prf_block
    (P.interest -- Scan.option (P.method -- P.interest) -- P.marg_comment
      >> (Toplevel.print oo (Toplevel.proof o IsarThy.proof)));


(* calculational proof commands *)

val calc_args =
  Scan.option (P.$$$ "(" |-- P.!!! ((P.xthms1 --| P.$$$ ")") -- P.interest));

val alsoP =
  OuterSyntax.command "also" "intermediate calculational proof step" K.prf_decl
    (calc_args -- P.marg_comment >> IsarThy.also);

val finallyP =
  OuterSyntax.command "finally" "terminal calculational proof step" K.prf_chain
    (calc_args -- P.marg_comment >> IsarThy.finally);


(* proof navigation *)

val backP =
  OuterSyntax.command "back" "backtracking of proof command" K.prf_script
    (Scan.optional (P.$$$ "!" >> K true) false >>
      (Toplevel.print oo (Toplevel.proof o ProofHistory.back)));


(* history *)

val cannot_undoP =
  OuterSyntax.improper_command "cannot_undo" "report 'cannot undo' error message" K.control
    (P.name >> IsarCmd.cannot_undo);

val clear_undosP =
  OuterSyntax.improper_command "clear_undos" "clear theory-level undo information" K.control
    (P.nat >> IsarCmd.clear_undos_theory);

val redoP =
  OuterSyntax.improper_command "redo" "redo last command" K.control
    (Scan.succeed (Toplevel.print o IsarCmd.redo));

val undos_proofP =
  OuterSyntax.improper_command "undos_proof" "undo last proof commands" K.control
    (P.nat >> (Toplevel.print oo IsarCmd.undos_proof));

val kill_proofP =
  OuterSyntax.improper_command "kill_proof" "undo current proof" K.control
    (Scan.succeed IsarCmd.kill_proof);

val undoP =
  OuterSyntax.improper_command "undo" "undo last command" K.control
    (Scan.succeed IsarCmd.undo);



(** diagnostic commands (for interactive mode only) **)

val pretty_setmarginP =
  OuterSyntax.improper_command "pretty_setmargin" "change default margin for pretty printing"
    K.diag (P.nat >> IsarCmd.pretty_setmargin);

val print_commandsP =
  OuterSyntax.improper_command "help" "print outer syntax (global)" K.diag
    (Scan.succeed OuterSyntax.print_help);

val print_contextP =
  OuterSyntax.improper_command "print_context" "print theory context name" K.diag
    (Scan.succeed IsarCmd.print_context);

val print_theoryP =
  OuterSyntax.improper_command "print_theory" "print logical theory contents (verbose!)" K.diag
    (Scan.succeed IsarCmd.print_theory);

val print_syntaxP =
  OuterSyntax.improper_command "print_syntax" "print inner syntax of theory (verbose!)" K.diag
    (Scan.succeed IsarCmd.print_syntax);

val print_theoremsP =
  OuterSyntax.improper_command "print_theorems" "print theorems known in this theory" K.diag
    (Scan.succeed IsarCmd.print_theorems);

val print_attributesP =
  OuterSyntax.improper_command "print_attributes" "print attributes known in this theory" K.diag
    (Scan.succeed IsarCmd.print_attributes);

val print_methodsP =
  OuterSyntax.improper_command "print_methods" "print methods known in this theory" K.diag
    (Scan.succeed IsarCmd.print_methods);

val thms_containingP =
  OuterSyntax.improper_command "thms_containing" "print theorems containing all given constants"
    K.diag (Scan.repeat P.xname >> IsarCmd.print_thms_containing);

val print_bindsP =
  OuterSyntax.improper_command "print_binds" "print term bindings of proof context" K.diag
    (Scan.succeed IsarCmd.print_binds);

val print_lthmsP =
  OuterSyntax.improper_command "print_facts" "print facts of proof context" K.diag
    (Scan.succeed IsarCmd.print_lthms);

val print_casesP =
  OuterSyntax.improper_command "print_cases" "print cases of proof context" K.diag
    (Scan.succeed IsarCmd.print_cases);

val print_thmsP =
  OuterSyntax.improper_command "thm" "print theorems" K.diag (P.xthms1 >> IsarCmd.print_thms);

val print_propP =
  OuterSyntax.improper_command "prop" "read and print proposition" K.diag
    (P.term >> IsarCmd.print_prop);

val print_termP =
  OuterSyntax.improper_command "term" "read and print term" K.diag
    (P.term >> IsarCmd.print_term);

val print_typeP =
  OuterSyntax.improper_command "typ" "read and print type" K.diag
    (P.typ >> IsarCmd.print_type);



(** system commands (for interactive mode only) **)

val cdP =
  OuterSyntax.improper_command "cd" "change current working directory" K.control
    (P.name >> IsarCmd.cd);

val pwdP =
  OuterSyntax.improper_command "pwd" "print current working directory" K.diag
    (Scan.succeed IsarCmd.pwd);

val use_thyP =
  OuterSyntax.improper_command "use_thy" "use theory file" K.diag
    (P.name >> IsarCmd.use_thy);

val use_thy_onlyP =
  OuterSyntax.improper_command "use_thy_only" "use theory file only, ignoring associated ML"
    K.diag (P.name >> IsarCmd.use_thy_only);

val update_thyP =
  OuterSyntax.improper_command "update_thy" "update theory file" K.diag
    (P.name >> IsarCmd.update_thy);

val update_thy_onlyP =
  OuterSyntax.improper_command "update_thy_only" "update theory file, ignoring associated ML"
    K.diag (P.name >> IsarCmd.update_thy_only);

val touch_thyP =
  OuterSyntax.improper_command "touch_thy" "outdate theory, including descendants" K.diag
    (P.name >> IsarCmd.touch_thy);

val touch_all_thysP =
  OuterSyntax.improper_command "touch_all_thys" "outdate all non-finished theories" K.diag
    (Scan.succeed IsarCmd.touch_all_thys);

val touch_child_thysP =
  OuterSyntax.improper_command "touch_child_thys" "outdate child theories" K.diag
    (P.name >> IsarCmd.touch_child_thys);

val remove_thyP =
  OuterSyntax.improper_command "remove_thy" "remove theory from loader database" K.diag
    (P.name >> IsarCmd.remove_thy);

val kill_thyP =
  OuterSyntax.improper_command "kill_thy" "kill theory -- try to remove from loader database"
    K.diag (P.name >> IsarCmd.kill_thy);

val prP =
  OuterSyntax.improper_command "pr" "print current toplevel state" K.diag
    (Scan.succeed (Toplevel.print o Toplevel.imperative (fn () => Toplevel.quiet := false)));

val disable_prP =
  OuterSyntax.improper_command "disable_pr" "disable printing of toplevel state" K.diag
    (Scan.succeed (Toplevel.imperative (fn () => Toplevel.quiet := true)));

val enable_prP =
  OuterSyntax.improper_command "enable_pr" "enable printing of toplevel state" K.diag
    (Scan.succeed (Toplevel.imperative (fn () => Toplevel.quiet := false)));

val commitP =
  OuterSyntax.improper_command "commit" "commit current session to ML database" K.diag
    (P.opt_unit >> (K IsarCmd.use_commit));

val quitP =
  OuterSyntax.improper_command "quit" "quit Isabelle" K.control
    (P.opt_unit >> (K IsarCmd.quit));

val exitP =
  OuterSyntax.improper_command "exit" "exit Isar loop" K.control
    (Scan.succeed IsarCmd.exit);

val init_toplevelP =
  OuterSyntax.improper_command "init_toplevel" "restart Isar toplevel loop" K.control
    (Scan.succeed IsarCmd.init_toplevel);

val welcomeP =
  OuterSyntax.improper_command "welcome" "print welcome message" K.control
    (Scan.succeed IsarCmd.welcome);



(** the Pure outer syntax **)

(*keep keywords consistent with the parsers, including those in
  outer_parse.ML, otherwise be prepared for unexpected errors*)

val keywords =
 ["!", "!!", "%", "%%", "(", ")", "+", ",", "--", ":", "::", ";", "<",
  "<=", "=", "==", "=>", "?", "[", "]", "and", "as", "binder",
  "concl", "files", "in", "infixl", "infixr", "is", "output", "{",
  "|", "}"];

val parsers = [
  (*theory structure*)
  theoryP, end_excursionP, kill_excursionP, contextP,
  (*markup commands*)
  headerP, chapterP, sectionP, subsectionP, subsubsectionP, textP,
  text_rawP, sectP, subsectP, subsubsectP, txtP, txt_rawP,
  (*theory sections*)
  classesP, classrelP, defaultsortP, typedeclP, typeabbrP, nontermP,
  aritiesP, judgmentP, constsP, syntaxP, translationsP, axiomsP,
  defsP, constdefsP, theoremsP, lemmasP, globalP, localP, useP, mlP,
  ml_commandP, ml_setupP, setupP, parse_ast_translationP,
  parse_translationP, print_translationP, typed_print_translationP,
  print_ast_translationP, token_translationP, oracleP,
  (*proof commands*)
  theoremP, lemmaP, showP, haveP, thusP, henceP, assumeP, presumeP,
  defP, fixP, letP, caseP, thenP, thenceP, fromP, withP, noteP,
  beginP, endP, nextP, qedP, terminal_proofP, immediate_proofP,
  default_proofP, skip_proofP, forget_proofP, deferP, preferP, applyP,
  apply_endP, proofP, alsoP, finallyP, backP, cannot_undoP,
  clear_undosP, redoP, undos_proofP, kill_proofP, undoP,
  (*diagnostic commands*)
  pretty_setmarginP, print_commandsP, print_contextP, print_theoryP,
  print_syntaxP, print_theoremsP, print_attributesP, print_methodsP,
  thms_containingP, print_bindsP, print_lthmsP, print_casesP,
  print_thmsP, print_propP, print_termP, print_typeP,
  (*system commands*)
  cdP, pwdP, use_thyP, use_thy_onlyP, update_thyP, update_thy_onlyP,
  touch_thyP, touch_all_thysP, touch_child_thysP, remove_thyP,
  kill_thyP, prP, disable_prP, enable_prP, commitP, quitP, exitP,
  init_toplevelP, welcomeP];


end;


(*install the Pure outer syntax*)
OuterSyntax.add_keywords IsarSyn.keywords;
OuterSyntax.add_parsers IsarSyn.parsers;
