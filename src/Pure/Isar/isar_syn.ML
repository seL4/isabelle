(*  Title:      Pure/Isar/isar_syn.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Pure outer syntax.

TODO:
  - constdefs;
  - axclass axioms: attribs;
  - instance: theory_to_proof (with special attribute to add result arity);
  - witness: eliminate (!);
  - result (interactive): print current result (?);
  - check evaluation of transformers (exns!);
  - 'result' command;
  - '--' (comment) option almost everywhere:
  - 'thm': xthms1;
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

val contextP =
  OuterSyntax.parser false "context" "switch theory context"
    (name >> (fn x => Toplevel.print o Toplevel.init_theory (IsarThy.the_theory x) (K ())));

val theoryP =
  OuterSyntax.parser false "theory" "begin theory"
    (name -- ($$$ "=" |-- !!! (enum "+" name --| (Scan.ahead eof || $$$ ":")))
      >> (fn x => Toplevel.print o
            Toplevel.init_theory (IsarThy.begin_theory x) IsarThy.end_theory));

(*end current theory / sub-proof / excursion*)
val endP =
  OuterSyntax.parser false "end" "end current theory / sub-proof / excursion"
    (Scan.succeed (Toplevel.print o Toplevel.exit o Toplevel.proof IsarThy.end_block));



(** theory sections **)

(* formal comments *)

val textP = OuterSyntax.parser false "text" "formal comments"
  (text >> (Toplevel.theory o IsarThy.add_text));

val chapterP = OuterSyntax.parser false "chapter" "chapter heading"
  (text >> (Toplevel.theory o IsarThy.add_chapter));

val sectionP = OuterSyntax.parser false "section" "section heading"
  (text >> (Toplevel.theory o IsarThy.add_section));

val subsectionP = OuterSyntax.parser false "subsection" "subsection heading"
  (text >> (Toplevel.theory o IsarThy.add_subsection));

val subsubsectionP = OuterSyntax.parser false "subsubsection" "subsubsection heading"
  (text >> (Toplevel.theory o IsarThy.add_subsubsection));


(* classes and sorts *)

val classesP =
  OuterSyntax.parser false "classes" "declare type classes"
    (Scan.repeat1 (name -- Scan.optional ($$$ "<" |-- !!! (list1 xname)) [])
      >> (Toplevel.theory o Theory.add_classes));

val classrelP =
  OuterSyntax.parser false "classrel" "state inclusion of type classes (axiomatic!)"
    (xname -- ($$$ "<" |-- !!! xname) >> (Toplevel.theory o Theory.add_classrel o single));

val defaultsortP =
  OuterSyntax.parser false "defaultsort" "declare default sort"
    (sort >> (Toplevel.theory o Theory.add_defsort));


(* types *)

val typedeclP =
  OuterSyntax.parser false "typedecl" "declare logical type"
    (type_args -- name -- opt_infix
      >> (fn ((args, a), mx) => Toplevel.theory (PureThy.add_typedecls [(a, args, mx)])));

val typeabbrP =
  OuterSyntax.parser false "types" "declare type abbreviations"
    (Scan.repeat1 (type_args -- name -- ($$$ "=" |-- !!! (typ -- opt_infix)))
      >> (Toplevel.theory o Theory.add_tyabbrs o
        map (fn ((args, a), (T, mx)) => (a, args, T, mx))));

val nontermP =
  OuterSyntax.parser false "nonterminals" "declare types treated as grammar nonterminal symbols"
    (Scan.repeat1 name >> (Toplevel.theory o Theory.add_nonterminals));

val aritiesP =
  OuterSyntax.parser false "arities" "state type arities (axiomatic!)"
    (Scan.repeat1 (xname -- ($$$ "::" |-- !!! arity) >> triple2)
      >> (Toplevel.theory o Theory.add_arities));


(* consts and syntax *)

val constsP =
  OuterSyntax.parser false "consts" "declare constants"
    (Scan.repeat1 const >> (Toplevel.theory o Theory.add_consts));

val opt_mode =
  Scan.optional
    ($$$ "(" |-- !!! (name -- Scan.optional ($$$ "output" >> K false) true --| $$$ ")"))
    ("", true);

val syntaxP =
  OuterSyntax.parser false "syntax" "declare syntactic constants"
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
  OuterSyntax.parser false "translations" "declare syntax translation rules"
    (Scan.repeat1 trans_line >> (Toplevel.theory o Theory.add_trrules));


(* axioms and definitions *)

val spec = thm_name ":" -- prop >> (fn ((x, y), z) => ((x, z), y));
val spec' = opt_thm_name ":" -- prop >> (fn ((x, y), z) => ((x, z), y));

val axiomsP =
  OuterSyntax.parser false "axioms" "state arbitrary propositions (axiomatic!)"
    (Scan.repeat1 spec >> (Toplevel.theory o IsarThy.add_axioms));

val defsP =
  OuterSyntax.parser false "defs" "define constants"
    (Scan.repeat1 spec' >> (Toplevel.theory o IsarThy.add_defs));


(* theorems *)

val facts = opt_thm_name "=" -- xthms1;

val theoremsP =
  OuterSyntax.parser false "theorems" "define theorems"
    (facts >> (Toplevel.theory o IsarThy.have_theorems));

val lemmasP =
  OuterSyntax.parser false "lemmas" "define lemmas"
    (facts >> (Toplevel.theory o IsarThy.have_lemmas));


(* axclass *)

val axclassP =
  OuterSyntax.parser false "axclass" "define axiomatic type class"
    (name -- Scan.optional ($$$ "<" |-- !!! (list1 xname)) [] -- Scan.repeat (spec >> fst)
      >> (Toplevel.theory o uncurry AxClass.add_axclass));


(* instance *)

val opt_witness =
  Scan.optional ($$$ "(" |-- !!! (list1 xname --| $$$ ")")) [];

val instanceP =
  OuterSyntax.parser false "instance" "prove type arity"
    ((xname -- ($$$ "<" |-- xname) >> AxClass.add_inst_subclass ||
      xname -- ($$$ "::" |-- arity) >> (AxClass.add_inst_arity o triple2))
    -- opt_witness >> (fn (f, x) => Toplevel.theory (f x [] None)));


(* name space entry path *)

val globalP =
  OuterSyntax.parser false "global" "disable prefixing of theory name"
    (Scan.succeed (Toplevel.theory PureThy.global_path));

val localP =
  OuterSyntax.parser false "local" "enable prefixing of theory name"
    (Scan.succeed (Toplevel.theory PureThy.local_path));

val pathP =
  OuterSyntax.parser false "path" "modify name-space entry path"
    (xname >> (Toplevel.theory o Theory.add_path));


(* use ML text *)

val useP =
  OuterSyntax.parser true "use" "eval ML text from file"
    (name >> IsarCmd.use);

val mlP =
  OuterSyntax.parser false "ML" "eval ML text"
    (text >> (fn txt => IsarCmd.use_mltext txt o IsarCmd.use_mltext_theory txt));

val setupP =
  OuterSyntax.parser false "setup" "apply ML theory transformer"
    (text >> (Toplevel.theory o IsarThy.use_setup));


(* translation functions *)

val parse_ast_translationP =
  OuterSyntax.parser false "parse_ast_translation" "install parse ast translation functions"
    (text >> (Toplevel.theory o IsarThy.parse_ast_translation));

val parse_translationP =
  OuterSyntax.parser false "parse_translation" "install parse translation functions"
    (text >> (Toplevel.theory o IsarThy.parse_translation));

val print_translationP =
  OuterSyntax.parser false "print_translation" "install print translation functions"
    (text >> (Toplevel.theory o IsarThy.print_translation));

val typed_print_translationP =
  OuterSyntax.parser false "typed_print_translation" "install typed print translation functions"
    (text >> (Toplevel.theory o IsarThy.typed_print_translation));

val print_ast_translationP =
  OuterSyntax.parser false "print_ast_translation" "install print ast translation functions"
    (text >> (Toplevel.theory o IsarThy.print_ast_translation));

val token_translationP =
  OuterSyntax.parser false "token_translation" "install token translation functions"
    (text >> (Toplevel.theory o IsarThy.token_translation));


(* oracles *)

val oracleP =
  OuterSyntax.parser false "oracle" "install oracle"
    (name -- text >> (Toplevel.theory o IsarThy.add_oracle));



(** proof commands **)

(* statements *)

val is_props = $$$ "(" |-- !!! (Scan.repeat1 ($$$ "is" |-- prop) --| $$$ ")");
val propp = prop -- Scan.optional is_props [];
fun statement f = opt_thm_name ":" -- propp >> (fn ((x, y), z) => f x y z);

val theoremP =
  OuterSyntax.parser false "theorem" "state theorem"
    (statement IsarThy.theorem >> (fn f => Toplevel.print o Toplevel.theory_to_proof f));

val lemmaP =
  OuterSyntax.parser false "lemma" "state lemma"
    (statement IsarThy.lemma >> (fn f => Toplevel.print o Toplevel.theory_to_proof f));

val showP =
  OuterSyntax.parser false "show" "state local goal, solving current obligation"
    (statement IsarThy.show >> (fn f => Toplevel.print o Toplevel.proof f));

val haveP =
  OuterSyntax.parser false "have" "state local goal"
    (statement IsarThy.have >> (fn f => Toplevel.print o Toplevel.proof f));


(* facts *)

val thenP =
  OuterSyntax.parser false "then" "forward chaining"
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.chain));

val fromP =
  OuterSyntax.parser false "from" "forward chaining from given facts"
    (xthms1 >> (fn x => Toplevel.print o Toplevel.proof (IsarThy.from_facts x)));

val factsP =
  OuterSyntax.parser false "note" "define facts"
    (facts >> (Toplevel.proof o IsarThy.have_facts));


(* proof context *)

val assumeP =
  OuterSyntax.parser false "assume" "assume propositions"
    (opt_thm_name ":" -- and_list1 propp >>
      (fn ((x, y), z) => Toplevel.print o Toplevel.proof (IsarThy.assume x y z)));

val fixP =
  OuterSyntax.parser false "fix" "fix variables (Skolem constants)"
    (and_list1 (name -- Scan.option ($$$ "::" |-- typ))
      >> (fn xs => Toplevel.print o Toplevel.proof (IsarThy.fix xs)));

val letP =
  OuterSyntax.parser false "let" "bind text variables"
    (and_list1 (enum1 "as" term -- ($$$ "=" |-- term))
      >> (fn bs => Toplevel.print o Toplevel.proof (IsarThy.match_bind bs)));


(* proof structure *)

val beginP =
  OuterSyntax.parser false "begin" "begin block"
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.begin_block));

val nextP =
  OuterSyntax.parser false "next" "enter next block"
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.next_block));


(* end proof *)

val qedP =
  OuterSyntax.parser false "qed" "conclude proof"
    (Scan.succeed (Toplevel.proof_to_theory IsarThy.qed));

val qed_withP =
  OuterSyntax.parser true "qed_with" "conclude proof, may patch name and attributes"
    (Scan.option name -- Scan.option attribs >> (Toplevel.proof_to_theory o IsarThy.qed_with));

val kill_proofP =
  OuterSyntax.parser true "kill" "abort current proof"
    (Scan.succeed (Toplevel.print o Toplevel.proof_to_theory IsarThy.kill_proof));


(* proof steps *)

fun gen_stepP meth int name cmt f =
  OuterSyntax.parser int name cmt
    (meth >> (fn txt => Toplevel.print o Toplevel.proof (f txt)));

val stepP = gen_stepP method;

val refineP = stepP true "refine" "unstructured backward proof step, ignoring facts" IsarThy.tac;
val then_refineP =
  stepP true "then_refine" "unstructured backward proof step, using facts" IsarThy.then_tac;


val proofP = gen_stepP (Scan.option method) false "proof" "backward proof" IsarThy.proof;
val terminal_proofP = stepP false "by" "terminal backward proof" IsarThy.terminal_proof;

val immediate_proofP =
  OuterSyntax.parser false "." "immediate proof"
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.immediate_proof));

val default_proofP =
  OuterSyntax.parser false ".." "default proof"
    (Scan.succeed (Toplevel.print o Toplevel.proof IsarThy.default_proof));


(* proof history *)

val clear_undoP =
  OuterSyntax.parser true "clear_undo" "clear proof command undo information"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.clear));

val undoP =
  OuterSyntax.parser true "undo" "undo proof command"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.undo));

val redoP =
  OuterSyntax.parser true "redo" "redo proof command"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.redo));

val undosP =
  OuterSyntax.parser true "undos" "undo proof commands"
    (nat >> (fn n => Toplevel.print o Toplevel.proof (ProofHistory.undos n)));

val redosP =
  OuterSyntax.parser true "redos" "redo proof commands"
    (nat >> (fn n => Toplevel.print o Toplevel.proof (ProofHistory.redos n)));

val backP =
  OuterSyntax.parser true "back" "backtracking of proof command"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.back));

val prevP =
  OuterSyntax.parser true "prev" "previous proof state"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.prev));

val upP =
  OuterSyntax.parser true "up" "upper proof state"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.up));

val topP =
  OuterSyntax.parser true "top" "to initial proof state"
    (Scan.succeed (Toplevel.print o Toplevel.proof ProofHistory.top));



(** diagnostic commands (for interactive mode only) **)

val print_commandsP =
  OuterSyntax.parser true "help" "print outer syntax (global)"
    (Scan.succeed (Toplevel.imperative OuterSyntax.print_outer_syntax));

val print_theoryP =
  OuterSyntax.parser true "print_theory" "print logical theory contents (verbose!)"
    (Scan.succeed IsarCmd.print_theory);

val print_syntaxP =
  OuterSyntax.parser true "print_syntax" "print inner syntax of theory (verbose!)"
    (Scan.succeed IsarCmd.print_syntax);

val print_theoremsP =
  OuterSyntax.parser true "print_theorems" "print theorems known in this theory"
    (Scan.succeed IsarCmd.print_theorems);

val print_attributesP =
  OuterSyntax.parser true "print_attributes" "print attributes known in this theory"
    (Scan.succeed IsarCmd.print_attributes);

val print_methodsP =
  OuterSyntax.parser true "print_methods" "print methods known in this theory"
    (Scan.succeed IsarCmd.print_methods);

val print_bindsP =
  OuterSyntax.parser true "print_binds" "print term bindings of proof context"
    (Scan.succeed IsarCmd.print_binds);

val print_lthmsP =
  OuterSyntax.parser true "print_facts" "print local theorems of proof context"
    (Scan.succeed IsarCmd.print_lthms);

val print_thmsP =
  OuterSyntax.parser true "thm" "print theorems" (xthm >> IsarCmd.print_thms);

val print_propP =
  OuterSyntax.parser true "prop" "read and print proposition"
    (term >> IsarCmd.print_prop);

val print_termP =
  OuterSyntax.parser true "term" "read and print term"
    (term >> IsarCmd.print_term);

val print_typeP =
  OuterSyntax.parser true "typ" "read and print type"
    (typ >> IsarCmd.print_type);



(** system commands (for interactive mode only) **)

val cdP =
  OuterSyntax.parser true "cd" "change current working directory"
    (name >> IsarCmd.cd);

val pwdP =
  OuterSyntax.parser true "pwd" "print current working directory"
    (Scan.succeed IsarCmd.pwd);

val use_thyP =
  OuterSyntax.parser true "use_thy" "use theory file"
    (name >> IsarCmd.use_thy);

val update_thyP =
  OuterSyntax.parser true "update_thy" "update theory file"
    (name >> IsarCmd.update_thy);

val prP =
  OuterSyntax.parser true "pr" "print current toplevel state"
    (Scan.succeed (Toplevel.print o Toplevel.imperative (K ())));


val opt_unit = Scan.optional ($$$ "(" -- $$$ ")" >> (K ())) ();

val commitP =
  OuterSyntax.parser true "commit" "commit current session to ML database"
    (opt_unit >> (K IsarCmd.use_commit));

val quitP =
  OuterSyntax.parser true "quit" "quit Isabelle"
    (opt_unit >> (K IsarCmd.quit));

val exitP =
  OuterSyntax.parser true "exit" "exit Isar loop"
    (Scan.succeed IsarCmd.exit);

val restartP =
  OuterSyntax.parser true "restart" "restart Isar loop"
    (Scan.succeed IsarCmd.restart);

val breakP =
  OuterSyntax.parser true "break" "discontinue excursion (keep current state)"
    (Scan.succeed IsarCmd.break);



(** the Pure outer syntax **)

(*keep keywords consistent with the parsers, including those in
  outer_parse.ML, otherwise be prepared for unexpected errors*)

val keywords =
 ["(", ")", "*", "+", "--", ",", ":", "::", ";", "<", "<=", "=", "==", "=>",
  "?", "[", "]", "and", "as", "binder", "infixl", "infixr", "is",
  "output", "{", "|", "}"];

val parsers = [
  (*theory structure*)
  contextP, theoryP, endP,
  (*theory sections*)
  textP, chapterP, sectionP, subsectionP, subsubsectionP, classesP,
  classrelP, defaultsortP, typedeclP, typeabbrP, nontermP, aritiesP,
  constsP, syntaxP, translationsP, axiomsP, defsP, theoremsP, lemmasP,
  axclassP, instanceP, globalP, localP, pathP, useP, mlP, setupP,
  parse_ast_translationP, parse_translationP, print_translationP,
  typed_print_translationP, print_ast_translationP,
  token_translationP, oracleP,
  (*proof commands*)
  theoremP, lemmaP, showP, haveP, assumeP, fixP, letP, thenP, fromP,
  factsP, beginP, nextP, qedP, qed_withP, kill_proofP, refineP,
  then_refineP, proofP, terminal_proofP, immediate_proofP,
  default_proofP, clear_undoP, undoP, redoP, undosP, redosP, backP,
  prevP, upP, topP,
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
