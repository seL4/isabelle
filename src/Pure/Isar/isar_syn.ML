(*  Title:      Pure/Isar/isar_syn.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Isar/Pure outer syntax.

TODO:
  - '--' (comment) option almost everywhere:
  - add_parsers: warn if command name coincides with other keyword (if
    not already present) (!?);
  - 'result' (interactive): print current result (?);
  - check evaluation of transformers (exns!);
  - 'thms': xthms1 (vs. 'thm' (!?));
*)

signature ISAR_SYN =
sig
  val keywords: string list
  val parsers: OuterSyntax.parser list
end;

structure IsarSyn: ISAR_SYN =
struct

open OuterParse;


(** init and exit **)

val theoryP =
  OuterSyntax.command "theory" "begin theory"
    (OuterSyntax.theory_header >> (Toplevel.print oo IsarThy.theory));

(*end current theory / sub-proof / excursion*)
val endP =
  OuterSyntax.command "end" "end current block / theory / excursion"
    (Scan.succeed (Toplevel.print o Toplevel.exit o Toplevel.proof IsarThy.end_block));

val contextP =
  OuterSyntax.improper_command "context" "switch theory context"
    (name >> (Toplevel.print oo IsarThy.context));

val update_contextP =
  OuterSyntax.improper_command "update_context" "switch theory context, forcing update"
    (name >> (Toplevel.print oo IsarThy.update_context));



(** theory sections **)

(* formal comments *)

val textP = OuterSyntax.command "text" "formal comments"
  (text >> (Toplevel.theory o IsarThy.add_text));

val titleP = OuterSyntax.command "title" "document title"
  ((text -- Scan.optional text "" -- Scan.optional text "")
    >> (fn ((x, y), z) => Toplevel.theory (IsarThy.add_title x y z)));

val chapterP = OuterSyntax.command "chapter" "chapter heading"
  (text >> (Toplevel.theory o IsarThy.add_chapter));

val sectionP = OuterSyntax.command "section" "section heading"
  (text >> (Toplevel.theory o IsarThy.add_section));

val subsectionP = OuterSyntax.command "subsection" "subsection heading"
  (text >> (Toplevel.theory o IsarThy.add_subsection));

val subsubsectionP = OuterSyntax.command "subsubsection" "subsubsection heading"
  (text >> (Toplevel.theory o IsarThy.add_subsubsection));


(* classes and sorts *)

val classesP =
  OuterSyntax.command "classes" "declare type classes"
    (Scan.repeat1 (name -- Scan.optional ($$$ "<" |-- !!! (list1 xname)) [])
      >> (Toplevel.theory o Theory.add_classes));

val classrelP =
  OuterSyntax.command "classrel" "state inclusion of type classes (axiomatic!)"
    (xname -- ($$$ "<" |-- !!! xname) >> (Toplevel.theory o Theory.add_classrel o single));

val defaultsortP =
  OuterSyntax.command "defaultsort" "declare default sort"
    (sort >> (Toplevel.theory o Theory.add_defsort));


(* types *)

val typedeclP =
  OuterSyntax.command "typedecl" "Pure type declaration"
    (type_args -- name -- opt_infix
      >> (fn ((args, a), mx) => Toplevel.theory (PureThy.add_typedecls [(a, args, mx)])));

val typeabbrP =
  OuterSyntax.command "types" "declare type abbreviations"
    (Scan.repeat1 (type_args -- name -- ($$$ "=" |-- !!! (typ -- opt_infix)))
      >> (Toplevel.theory o Theory.add_tyabbrs o
        map (fn ((args, a), (T, mx)) => (a, args, T, mx))));

val nontermP =
  OuterSyntax.command "nonterminals" "declare types treated as grammar nonterminal symbols"
    (Scan.repeat1 name >> (Toplevel.theory o Theory.add_nonterminals));

val aritiesP =
  OuterSyntax.command "arities" "state type arities (axiomatic!)"
    (Scan.repeat1 (xname -- ($$$ "::" |-- !!! arity) >> triple2)
      >> (Toplevel.theory o Theory.add_arities));


(* consts and syntax *)

val constsP =
  OuterSyntax.command "consts" "declare constants"
    (Scan.repeat1 const >> (Toplevel.theory o Theory.add_consts));

val opt_mode =
  Scan.optional
    ($$$ "(" |-- !!! (name -- Scan.optional ($$$ "output" >> K false) true --| $$$ ")"))
    ("", true);

val syntaxP =
  OuterSyntax.command "syntax" "declare syntactic constants"
    (opt_mode -- Scan.repeat1 const >> (Toplevel.theory o uncurry Theory.add_modesyntax));


(* translations *)

val trans_pat =
  Scan.optional ($$$ "(" |-- !!! (xname --| $$$ ")")) "logic" -- string;

fun trans_arrow toks =
  ($$$ "=>" >> K Syntax.ParseRule ||
    $$$ "<=" >> K Syntax.PrintRule ||
    $$$ "==" >> K Syntax.ParsePrintRule) toks;

val trans_line =
  trans_pat -- !!! (trans_arrow -- trans_pat)
    >> (fn (left, (arr, right)) => arr (left, right));

val translationsP =
  OuterSyntax.command "translations" "declare syntax translation rules"
    (Scan.repeat1 trans_line >> (Toplevel.theory o Theory.add_trrules));


(* axioms and definitions *)

val axiomsP =
  OuterSyntax.command "axioms" "state arbitrary propositions (axiomatic!)"
    (Scan.repeat1 spec_name >> (Toplevel.theory o IsarThy.add_axioms));

val defsP =
  OuterSyntax.command "defs" "define constants"
    (Scan.repeat1 spec_opt_name >> (Toplevel.theory o IsarThy.add_defs));

val constdefsP =
  OuterSyntax.command "constdefs" "declare and define constants"
    (Scan.repeat1 (const -- term) >> (Toplevel.theory o IsarThy.add_constdefs));


(* theorems *)

val facts = opt_thm_name "=" -- xthms1;

val theoremsP =
  OuterSyntax.command "theorems" "define theorems"
    (facts >> (Toplevel.theory o IsarThy.have_theorems));

val lemmasP =
  OuterSyntax.command "lemmas" "define lemmas"
    (facts >> (Toplevel.theory o IsarThy.have_lemmas));


(* name space entry path *)

val globalP =
  OuterSyntax.command "global" "disable prefixing of theory name"
    (Scan.succeed (Toplevel.theory PureThy.global_path));

val localP =
  OuterSyntax.command "local" "enable prefixing of theory name"
    (Scan.succeed (Toplevel.theory PureThy.local_path));

val pathP =
  OuterSyntax.command "path" "modify name-space entry path"
    (xname >> (Toplevel.theory o Theory.add_path));


(* use ML text *)

val useP =
  OuterSyntax.command "use" "eval ML text from file"
    (name >> IsarCmd.use);

val mlP =
  OuterSyntax.command "ML" "eval ML text"
    (text >> (fn txt => IsarCmd.use_mltext txt o IsarCmd.use_mltext_theory txt));

val setupP =
  OuterSyntax.command "setup" "apply ML theory transformer"
    (text >> (Toplevel.theory o IsarThy.use_setup));


(* translation functions *)

val parse_ast_translationP =
  OuterSyntax.command "parse_ast_translation" "install parse ast translation functions"
    (text >> (Toplevel.theory o IsarThy.parse_ast_translation));

val parse_translationP =
  OuterSyntax.command "parse_translation" "install parse translation functions"
    (text >> (Toplevel.theory o IsarThy.parse_translation));

val print_translationP =
  OuterSyntax.command "print_translation" "install print translation functions"
    (text >> (Toplevel.theory o IsarThy.print_translation));

val typed_print_translationP =
  OuterSyntax.command "typed_print_translation" "install typed print translation functions"
    (text >> (Toplevel.theory o IsarThy.typed_print_translation));

val print_ast_translationP =
  OuterSyntax.command "print_ast_translation" "install print ast translation functions"
    (text >> (Toplevel.theory o IsarThy.print_ast_translation));

val token_translationP =
  OuterSyntax.command "token_translation" "install token translation functions"
    (text >> (Toplevel.theory o IsarThy.token_translation));


(* oracles *)

val oracleP =
  OuterSyntax.command "oracle" "install oracle"
    (name -- text >> (Toplevel.theory o IsarThy.add_oracle));



(** proof commands **)

(* statements *)

val is_props = $$$ "(" |-- !!! (Scan.repeat1 ($$$ "is" |-- prop) --| $$$ ")");
val propp = prop -- Scan.optional is_props [];
fun statement f = opt_thm_name ":" -- propp >> (fn ((x, y), z) => f x y z);

val theoremP =
  OuterSyntax.command "theorem" "state theorem"
    (statement IsarThy.theorem >> (fn f => Toplevel.print o Toplevel.theory_to_proof f));

val lemmaP =
  OuterSyntax.command "lemma" "state lemma"
    (statement IsarThy.lemma >> (fn f => Toplevel.print o Toplevel.theory_to_proof f));

val showP =
  OuterSyntax.command "show" "state local goal, solving current obligation"
    (statement IsarThy.show >> (fn f => Toplevel.print o Toplevel.proof f));

val haveP =
  OuterSyntax.command "have" "state local goal"
    (statement IsarThy.have >> (fn f => Toplevel.print o Toplevel.proof f));


(* facts *)

val thenP =
  OuterSyntax.command "then" "forward chaining"
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.chain));

val fromP =
  OuterSyntax.command "from" "forward chaining from given facts"
    (xthms1 >> (fn x => Toplevel.print o Toplevel.proof (IsarThy.from_facts x)));

val factsP =
  OuterSyntax.command "note" "define facts"
    (facts >> (Toplevel.proof o IsarThy.have_facts));


(* proof context *)

val assumeP =
  OuterSyntax.command "assume" "assume propositions"
    (opt_thm_name ":" -- Scan.repeat1 propp >>
      (fn ((x, y), z) => Toplevel.print o Toplevel.proof (IsarThy.assume x y z)));

val fixP =
  OuterSyntax.command "fix" "fix variables (Skolem constants)"
    (Scan.repeat1 (name -- Scan.option ($$$ "::" |-- typ))
      >> (fn xs => Toplevel.print o Toplevel.proof (IsarThy.fix xs)));

val letP =
  OuterSyntax.command "let" "bind text variables"
    (and_list1 (enum1 "as" term -- ($$$ "=" |-- term))
      >> (fn bs => Toplevel.print o Toplevel.proof (IsarThy.match_bind bs)));


(* proof structure *)

val beginP =
  OuterSyntax.command "begin" "begin block"
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.begin_block));

val nextP =
  OuterSyntax.command "next" "enter next block"
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.next_block));


(* end proof *)

val kill_proofP =
  OuterSyntax.improper_command "kill" "abort current proof"
    (Scan.succeed (Toplevel.print o Toplevel.proof_to_theory IsarThy.kill_proof));

val qed_withP =
  OuterSyntax.improper_command "qed_with" "conclude proof, may patch name and attributes"
    (Scan.option name -- Scan.option attribs -- Scan.option method
      >> (uncurry IsarThy.global_qed_with));

val qedP =
  OuterSyntax.command "qed" "conclude (sub-)proof"
    (Scan.option method >> IsarThy.qed);

val terminal_proofP =
  OuterSyntax.command "by" "terminal backward proof"
    (method >> (Toplevel.print oo IsarThy.terminal_proof));

val immediate_proofP =
  OuterSyntax.command "." "immediate proof"
    (Scan.succeed (Toplevel.print o IsarThy.immediate_proof));

val default_proofP =
  OuterSyntax.command ".." "default proof"
    (Scan.succeed (Toplevel.print o IsarThy.default_proof));


(* proof steps *)

val refineP =
  OuterSyntax.improper_command "refine" "unstructured backward proof step, ignoring facts"
    (method >> (Toplevel.print oo (Toplevel.proof o IsarThy.tac)));

val then_refineP =
  OuterSyntax.improper_command "then_refine" "unstructured backward proof step, using facts"
    (method >> (Toplevel.print oo (Toplevel.proof o IsarThy.then_tac)));

val proofP =
  OuterSyntax.command "proof" "backward proof"
    (Scan.option method >> (Toplevel.print oo (Toplevel.proof o IsarThy.proof)));


(* proof history *)

val clear_undoP =
  OuterSyntax.improper_command "clear_undo" "clear proof command undo information"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.clear));

val undoP =
  OuterSyntax.improper_command "undo" "undo proof command"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.undo));

val redoP =
  OuterSyntax.improper_command "redo" "redo proof command"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.redo));

val undosP =
  OuterSyntax.improper_command "undos" "undo proof commands"
    (nat >> (fn n => Toplevel.print o Toplevel.proof (ProofHistory.undos n)));

val redosP =
  OuterSyntax.improper_command "redos" "redo proof commands"
    (nat >> (fn n => Toplevel.print o Toplevel.proof (ProofHistory.redos n)));

val backP =
  OuterSyntax.improper_command "back" "backtracking of proof command"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.back));

val prevP =
  OuterSyntax.improper_command "prev" "previous proof state"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.prev));

val upP =
  OuterSyntax.improper_command "up" "upper proof state"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.up));

val topP =
  OuterSyntax.improper_command "top" "to initial proof state"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.top));



(** diagnostic commands (for interactive mode only) **)

val print_commandsP =
  OuterSyntax.improper_command "help" "print outer syntax (global)"
    (Scan.succeed (Toplevel.imperative OuterSyntax.print_outer_syntax));

val print_theoryP =
  OuterSyntax.improper_command "print_theory" "print logical theory contents (verbose!)"
    (Scan.succeed IsarCmd.print_theory);

val print_syntaxP =
  OuterSyntax.improper_command "print_syntax" "print inner syntax of theory (verbose!)"
    (Scan.succeed IsarCmd.print_syntax);

val print_theoremsP =
  OuterSyntax.improper_command "print_theorems" "print theorems known in this theory"
    (Scan.succeed IsarCmd.print_theorems);

val print_attributesP =
  OuterSyntax.improper_command "print_attributes" "print attributes known in this theory"
    (Scan.succeed IsarCmd.print_attributes);

val print_methodsP =
  OuterSyntax.improper_command "print_methods" "print methods known in this theory"
    (Scan.succeed IsarCmd.print_methods);

val print_bindsP =
  OuterSyntax.improper_command "print_binds" "print term bindings of proof context"
    (Scan.succeed IsarCmd.print_binds);

val print_lthmsP =
  OuterSyntax.improper_command "print_facts" "print local theorems of proof context"
    (Scan.succeed IsarCmd.print_lthms);

val print_thmsP =
  OuterSyntax.improper_command "thm" "print theorems" (xthm >> IsarCmd.print_thms);

val print_propP =
  OuterSyntax.improper_command "prop" "read and print proposition"
    (term >> IsarCmd.print_prop);

val print_termP =
  OuterSyntax.improper_command "term" "read and print term"
    (term >> IsarCmd.print_term);

val print_typeP =
  OuterSyntax.improper_command "type" "read and print type"
    (typ >> IsarCmd.print_type);



(** system commands (for interactive mode only) **)

val cdP =
  OuterSyntax.improper_command "cd" "change current working directory"
    (name >> IsarCmd.cd);

val pwdP =
  OuterSyntax.improper_command "pwd" "print current working directory"
    (Scan.succeed IsarCmd.pwd);

val use_thyP =
  OuterSyntax.improper_command "use_thy" "use theory file"
    (name >> IsarCmd.use_thy);

val update_thyP =
  OuterSyntax.improper_command "update_thy" "update theory file"
    (name >> IsarCmd.update_thy);

val prP =
  OuterSyntax.improper_command "pr" "print current toplevel state"
    (Scan.succeed (Toplevel.print o Toplevel.imperative (K ())));


val opt_unit = Scan.optional ($$$ "(" -- $$$ ")" >> (K ())) ();

val commitP =
  OuterSyntax.improper_command "commit" "commit current session to ML database"
    (opt_unit >> (K IsarCmd.use_commit));

val quitP =
  OuterSyntax.improper_command "quit" "quit Isabelle"
    (opt_unit >> (K IsarCmd.quit));

val exitP =
  OuterSyntax.improper_command "exit" "exit Isar loop"
    (Scan.succeed IsarCmd.exit);

val restartP =
  OuterSyntax.improper_command "restart" "restart Isar loop"
    (Scan.succeed IsarCmd.restart);

val breakP =
  OuterSyntax.improper_command "break" "discontinue excursion (keep current state)"
    (Scan.succeed IsarCmd.break);



(** the Pure outer syntax **)

(*keep keywords consistent with the parsers, including those in
  outer_parse.ML, otherwise be prepared for unexpected errors*)

val keywords =
 ["(", ")", "*", "+", "--", ",", ":", "::", ";", "<", "<=", "=", "==", "=>",
  "?", "[", "]", "and", "as", "binder", "files", "infixl", "infixr", "is",
  "output", "{", "|", "}"];

val parsers = [
  (*theory structure*)
  theoryP, endP, contextP, update_contextP,
  (*theory sections*)
  textP, titleP, chapterP, sectionP, subsectionP, subsubsectionP,
  classesP, classrelP, defaultsortP, typedeclP, typeabbrP, nontermP,
  aritiesP, constsP, syntaxP, translationsP, axiomsP, defsP,
  constdefsP, theoremsP, lemmasP, globalP, localP, pathP, useP, mlP,
  setupP, parse_ast_translationP, parse_translationP,
  print_translationP, typed_print_translationP,
  print_ast_translationP, token_translationP, oracleP,
  (*proof commands*)
  theoremP, lemmaP, showP, haveP, assumeP, fixP, letP, thenP, fromP,
  factsP, beginP, nextP, kill_proofP, qed_withP, qedP,
  terminal_proofP, immediate_proofP, default_proofP, refineP,
  then_refineP, proofP, clear_undoP, undoP, redoP, undosP, redosP,
  backP, prevP, upP, topP,
  (*diagnostic commands*)
  print_commandsP, print_theoryP, print_syntaxP, print_attributesP,
  print_methodsP, print_theoremsP, print_bindsP, print_lthmsP,
  print_thmsP, print_propP, print_termP, print_typeP,
  (*system commands*)
  cdP, pwdP, use_thyP, update_thyP, prP, commitP, quitP, exitP,
  restartP, breakP];


end;


(*install the Pure outer syntax*)
OuterSyntax.add_keywords IsarSyn.keywords;
OuterSyntax.add_parsers IsarSyn.parsers;
