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
    (Scan.succeed (Toplevel.print o IsarCmd.kill_theory));

val contextP =
  OuterSyntax.improper_command "context" "switch theory context" K.thy_begin
    (P.name >> (Toplevel.print oo IsarThy.context));

val update_contextP =
  OuterSyntax.improper_command "update_context" "switch theory context, forcing update" K.thy_begin
    (P.name >> (Toplevel.print oo IsarThy.update_context));



(** formal comments **)

val txtP = OuterSyntax.command "txt" "formal comment (proof)" K.prf_decl
  (P.comment >> (Toplevel.proof o IsarThy.add_txt));

val textP = OuterSyntax.command "text" "formal comment (theory)" K.thy_decl
  (P.comment >> (Toplevel.theory o IsarThy.add_text));

val titleP = OuterSyntax.command "title" "document title" K.thy_heading
  ((P.comment -- Scan.optional P.comment Comment.none -- Scan.optional P.comment Comment.none)
    >> (fn ((x, y), z) => Toplevel.theory (IsarThy.add_title x y z)));

val chapterP = OuterSyntax.command "chapter" "chapter heading" K.thy_heading
  (P.comment >> (Toplevel.theory o IsarThy.add_chapter));

val sectionP = OuterSyntax.command "section" "section heading" K.thy_heading
  (P.comment >> (Toplevel.theory o IsarThy.add_section));

val subsectionP = OuterSyntax.command "subsection" "subsection heading" K.thy_heading
  (P.comment >> (Toplevel.theory o IsarThy.add_subsection));

val subsubsectionP = OuterSyntax.command "subsubsection" "subsubsection heading" K.thy_heading
  (P.comment >> (Toplevel.theory o IsarThy.add_subsubsection));



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
    (Scan.repeat1 (P.spec_opt_name -- P.marg_comment) >> (Toplevel.theory o IsarThy.add_defs));

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

val pathP =
  OuterSyntax.command "path" "modify name-space entry path" K.thy_decl
    (P.xname >> (Toplevel.theory o Theory.add_path));


(* use ML text *)

val useP =
  OuterSyntax.command "use" "eval ML text from file" K.diag
    (P.name >> IsarCmd.use);

val mlP =
  OuterSyntax.command "ML" "eval ML text" K.diag
    (P.text >> (fn txt => IsarCmd.use_mltext txt o IsarCmd.use_mltext_theory txt));

val setupP =
  OuterSyntax.command "setup" "apply ML theory transformer" K.thy_decl
    (P.text >> (Toplevel.theory o IsarThy.use_setup));


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
    (P.name -- P.text -- P.marg_comment >> (Toplevel.theory o IsarThy.add_oracle));



(** proof commands **)

(* statements *)

val is_props = P.$$$ "(" |-- P.!!! (Scan.repeat1 (P.$$$ "is" |-- P.prop) --| P.$$$ ")");
val propp = P.prop -- Scan.optional is_props [];
fun statement f = (P.opt_thm_name ":" -- propp >> P.triple1) -- P.marg_comment >> f;

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
    ((P.opt_thm_name ":" -- Scan.repeat1 propp >> P.triple1) -- P.marg_comment
      >> (Toplevel.print oo (Toplevel.proof o IsarThy.assume)));

val presumeP =
  OuterSyntax.command "presume" "assume propositions, to be established later" K.prf_asm
    ((P.opt_thm_name ":" -- Scan.repeat1 propp >> P.triple1) -- P.marg_comment
      >> (Toplevel.print oo (Toplevel.proof o IsarThy.presume)));

val fixP =
  OuterSyntax.command "fix" "fix variables (Skolem constants)" K.prf_asm
    (Scan.repeat1 (P.name -- Scan.option (P.$$$ "::" |-- P.typ)) -- P.marg_comment
      >> (Toplevel.print oo (Toplevel.proof o IsarThy.fix)));

val letP =
  OuterSyntax.command "let" "bind text variables" K.prf_decl
    (P.and_list1 (P.enum1 "as" P.term -- (P.$$$ "=" |-- P.term) -- P.marg_comment)
      >> (Toplevel.print oo (Toplevel.proof o IsarThy.match_bind)));


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

val qed_withP =
  OuterSyntax.improper_command "qed_with" "conclude proof, may patch name and attributes"
    K.qed_block
    (Scan.option P.name -- Scan.option P.attribs -- Scan.option (P.method -- P.interest)
      >> (uncurry IsarThy.global_qed_with));

val qedP =
  OuterSyntax.command "qed" "conclude (sub-)proof" K.qed_block
    (Scan.option (P.method -- P.interest) >> IsarThy.qed);

val terminal_proofP =
  OuterSyntax.command "by" "terminal backward proof" K.qed
    (P.method -- P.interest >> IsarThy.terminal_proof);

val immediate_proofP =
  OuterSyntax.command "." "immediate proof" K.qed
    (Scan.succeed IsarThy.immediate_proof);

val default_proofP =
  OuterSyntax.command ".." "default proof" K.qed
    (Scan.succeed IsarThy.default_proof);


(* proof steps *)

val applyP =
  OuterSyntax.improper_command "apply" "unstructured backward proof step, ignoring facts"
    K.prf_script (P.method >> (Toplevel.print oo (Toplevel.proof o IsarThy.tac)));

val then_applyP =
  OuterSyntax.improper_command "then_apply" "unstructured backward proof step, using facts"
    K.prf_script (P.method >> (Toplevel.print oo (Toplevel.proof o IsarThy.then_tac)));

val proofP =
  OuterSyntax.command "proof" "backward proof" K.prf_block
    (P.interest -- Scan.option (P.method -- P.interest)
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
  OuterSyntax.improper_command "back" "backtracking of proof command" K.prf_script
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.back));

val prevP =
  OuterSyntax.improper_command "prev" "previous proof state" K.control
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.prev));

val upP =
  OuterSyntax.improper_command "up" "upper proof state" K.control
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.up));

val topP =
  OuterSyntax.improper_command "top" "to initial proof state" K.control
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.top));


(* history *)

val cannot_undoP =
  OuterSyntax.improper_command "cannot_undo" "report 'cannot undo' error message" K.control
    (P.name >> (Toplevel.print oo IsarCmd.cannot_undo));

val clear_undoP =
  OuterSyntax.improper_command "clear_undo" "clear undo information" K.control
    (Scan.succeed (Toplevel.print o IsarCmd.clear_undo));

val redoP =
  OuterSyntax.improper_command "redo" "redo last command" K.control
    (Scan.succeed (Toplevel.print o IsarCmd.redo));

val undos_proofP =
  OuterSyntax.improper_command "undos_proof" "undo last proof commands" K.control
    (P.nat >> (Toplevel.print oo IsarCmd.undos_proof));

val kill_proofP =
  OuterSyntax.improper_command "kill_proof" "undo current proof" K.control
    (Scan.succeed (Toplevel.print o IsarCmd.kill_proof));

val undoP =
  OuterSyntax.improper_command "undo" "undo last command" K.control
    (Scan.succeed (Toplevel.print o IsarCmd.undo));



(** diagnostic commands (for interactive mode only) **)

val print_commandsP =
  OuterSyntax.improper_command "help" "print outer syntax (global)" K.diag
    (Scan.succeed (Toplevel.imperative OuterSyntax.print_outer_syntax));

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

val print_bindsP =
  OuterSyntax.improper_command "print_binds" "print term bindings of proof context" K.diag
    (Scan.succeed IsarCmd.print_binds);

val print_lthmsP =
  OuterSyntax.improper_command "print_facts" "print local theorems of proof context" K.diag
    (Scan.succeed IsarCmd.print_lthms);

val print_thmsP =
  OuterSyntax.improper_command "thm" "print theorems" K.diag (P.xthm >> IsarCmd.print_thms);

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
  OuterSyntax.improper_command "use_thy_only" "use theory file only, ignoring associated ML" K.diag
    (P.name >> IsarCmd.use_thy_only);

val update_thyP =
  OuterSyntax.improper_command "update_thy" "update theory file" K.diag
    (P.name >> IsarCmd.update_thy);

val prP =
  OuterSyntax.improper_command "pr" "print current toplevel state" K.diag
    (Scan.succeed (Toplevel.print o Toplevel.imperative (K ())));


val opt_unit = Scan.optional (P.$$$ "(" -- P.$$$ ")" >> (K ())) ();

val commitP =
  OuterSyntax.improper_command "commit" "commit current session to ML database" K.diag
    (opt_unit >> (K IsarCmd.use_commit));

val quitP =
  OuterSyntax.improper_command "quit" "quit Isabelle" K.control
    (opt_unit >> (K IsarCmd.quit));

val exitP =
  OuterSyntax.improper_command "exit" "exit Isar loop" K.control
    (Scan.succeed IsarCmd.exit);

val restartP =
  OuterSyntax.improper_command "restart" "restart Isar loop" K.control
    (Scan.succeed IsarCmd.restart);

val breakP =
  OuterSyntax.improper_command "break" "discontinue excursion (keep current state)" K.control
    (Scan.succeed IsarCmd.break);



(** the Pure outer syntax **)

(*keep keywords consistent with the parsers, including those in
  outer_parse.ML, otherwise be prepared for unexpected errors*)

val keywords =
 ["!", "%", "(", ")", "*", "+", ",", "--", ":", "::", ";", "<", "<=",
  "=", "==", "=>", "?", "[", "]", "and", "as", "binder", "files",
  "infixl", "infixr", "is", "output", "{", "|", "}"];

val parsers = [
  (*theory structure*)
  theoryP, end_excursionP, kill_excursionP, contextP, update_contextP,
  (*theory sections*)
  txtP, textP, titleP, chapterP, sectionP, subsectionP,
  subsubsectionP, classesP, classrelP, defaultsortP, typedeclP,
  typeabbrP, nontermP, aritiesP, constsP, syntaxP, translationsP,
  axiomsP, defsP, constdefsP, theoremsP, lemmasP, globalP, localP,
  pathP, useP, mlP, setupP, parse_ast_translationP,
  parse_translationP, print_translationP, typed_print_translationP,
  print_ast_translationP, token_translationP, oracleP,
  (*proof commands*)
  theoremP, lemmaP, showP, haveP, thusP, henceP, assumeP, presumeP,
  fixP, letP, thenP, fromP, withP, noteP, beginP, endP, nextP,
  qed_withP, qedP, terminal_proofP, immediate_proofP, default_proofP,
  applyP, then_applyP, proofP, alsoP, finallyP, backP, prevP, upP,
  topP, cannot_undoP, clear_undoP, redoP, undos_proofP, kill_proofP,
  undoP,
  (*diagnostic commands*)
  print_commandsP, print_theoryP, print_syntaxP, print_attributesP,
  print_methodsP, print_theoremsP, print_bindsP, print_lthmsP,
  print_thmsP, print_propP, print_termP, print_typeP,
  (*system commands*)
  cdP, pwdP, use_thyP, use_thy_onlyP, update_thyP, prP, commitP,
  quitP, exitP, restartP, breakP];


end;


(*install the Pure outer syntax*)
OuterSyntax.add_keywords IsarSyn.keywords;
OuterSyntax.add_parsers IsarSyn.parsers;
