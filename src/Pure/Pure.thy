(*  Title:      Pure/Pure.thy
    Author:     Makarius

Final stage of bootstrapping Pure, based on implicit background theory.
*)

theory Pure
  keywords
    "!!" "!" "%" "(" ")" "+" "," "--" ":" "::" ";" "<" "<=" "=" "=="
    "=>" "?" "[" "\<equiv>" "\<leftharpoondown>" "\<rightharpoonup>"
    "\<rightleftharpoons>" "\<subseteq>" "]" "advanced" "and" "assumes"
    "attach" "begin" "binder" "constrains" "defines" "fixes" "for"
    "identifier" "if" "imports" "in" "includes" "infix" "infixl"
    "infixr" "is" "keywords" "notes" "obtains" "open" "output"
    "overloaded" "pervasive" "shows" "structure" "unchecked" "uses"
    "where" "|"
  and "header" :: diag
  and "chapter" :: thy_heading1
  and "section" :: thy_heading2
  and "subsection" :: thy_heading3
  and "subsubsection" :: thy_heading4
  and "text" "text_raw" :: thy_decl
  and "sect" :: prf_heading2 % "proof"
  and "subsect" :: prf_heading3 % "proof"
  and "subsubsect" :: prf_heading4 % "proof"
  and "txt" "txt_raw" :: prf_decl % "proof"
  and "classes" "classrel" "default_sort" "typedecl" "type_synonym"
    "nonterminal" "arities" "judgment" "consts" "syntax" "no_syntax"
    "translations" "no_translations" "axioms" "defs" "definition"
    "abbreviation" "type_notation" "no_type_notation" "notation"
    "no_notation" "axiomatization" "theorems" "lemmas" "declare"
    "hide_class" "hide_type" "hide_const" "hide_fact" :: thy_decl
  and "use" "ML" :: thy_decl % "ML"
  and "ML_prf" :: prf_decl % "proof"  (* FIXME % "ML" ?? *)
  and "ML_val" "ML_command" :: diag % "ML"
  and "setup" "local_setup" "attribute_setup" "method_setup"
    "declaration" "syntax_declaration" "simproc_setup"
    "parse_ast_translation" "parse_translation" "print_translation"
    "typed_print_translation" "print_ast_translation" "oracle" :: thy_decl % "ML"
  and "bundle" :: thy_decl
  and "include" "including" :: prf_decl
  and "print_bundles" :: diag
  and "context" "locale" :: thy_decl
  and "sublocale" "interpretation" :: thy_schematic_goal
  and "interpret" :: prf_goal % "proof"  (* FIXME schematic? *)
  and "class" :: thy_decl
  and "subclass" :: thy_goal
  and "instantiation" :: thy_decl
  and "instance" :: thy_goal
  and "overloading" :: thy_decl
  and "code_datatype" :: thy_decl
  and "theorem" "lemma" "corollary" :: thy_goal
  and "schematic_theorem" "schematic_lemma" "schematic_corollary" :: thy_schematic_goal
  and "notepad" :: thy_decl
  and "have" "hence" :: prf_goal % "proof"
  and "show" "thus" :: prf_asm_goal % "proof"
  and "then" "from" "with" :: prf_chain % "proof"
  and "note" "using" "unfolding" :: prf_decl % "proof"
  and "fix" "assume" "presume" "def" :: prf_asm % "proof"
  and "obtain" "guess" :: prf_asm_goal % "proof"
  and "let" "write" :: prf_decl % "proof"
  and "case" :: prf_asm % "proof"
  and "{" :: prf_open % "proof"
  and "}" :: prf_close % "proof"
  and "next" :: prf_block % "proof"
  and "qed" :: qed_block % "proof"
  and "by" ".." "." "done" "sorry" :: "qed" % "proof"
  and "oops" :: qed_global % "proof"
  and "defer" "prefer" "apply" "apply_end" :: prf_script % "proof"
  and "proof" :: prf_block % "proof"
  and "also" "moreover" :: prf_decl % "proof"
  and "finally" "ultimately" :: prf_chain % "proof"
  and "back" :: prf_script % "proof"
  and "Isabelle.command" :: control
  and "pretty_setmargin" "help" "print_commands" "print_configs"
    "print_context" "print_theory" "print_syntax" "print_abbrevs"
    "print_theorems" "print_locales" "print_classes" "print_locale"
    "print_interps" "print_dependencies" "print_attributes"
    "print_simpset" "print_rules" "print_trans_rules" "print_methods"
    "print_antiquotations" "thy_deps" "class_deps" "thm_deps"
    "print_binds" "print_facts" "print_cases" "print_statement" "thm"
    "prf" "full_prf" "prop" "term" "typ" "print_codesetup" "unused_thms"
    :: diag
  and "cd" :: control
  and "pwd" :: diag
  and "use_thy" "remove_thy" "kill_thy" :: control
  and "display_drafts" "print_drafts" "pr" :: diag
  and "disable_pr" "enable_pr" "commit" "quit" "exit" :: control
  and "welcome" :: diag
  and "init_toplevel" "linear_undo" "undo" "undos_proof" "cannot_undo" "kill" :: control
  and "end" :: thy_end % "theory"
  and "realizers" "realizability" "extract_type" "extract" :: thy_decl
  and "find_theorems" "find_consts" :: diag
begin

ML_file "Isar/isar_syn.ML"
ML_file "Tools/find_theorems.ML"
ML_file "Tools/find_consts.ML"


section {* Further content for the Pure theory *}

subsection {* Meta-level connectives in assumptions *}

lemma meta_mp:
  assumes "PROP P ==> PROP Q" and "PROP P"
  shows "PROP Q"
    by (rule `PROP P ==> PROP Q` [OF `PROP P`])

lemmas meta_impE = meta_mp [elim_format]

lemma meta_spec:
  assumes "!!x. PROP P x"
  shows "PROP P x"
    by (rule `!!x. PROP P x`)

lemmas meta_allE = meta_spec [elim_format]

lemma swap_params:
  "(!!x y. PROP P x y) == (!!y x. PROP P x y)" ..


subsection {* Meta-level conjunction *}

lemma all_conjunction:
  "(!!x. PROP A x &&& PROP B x) == ((!!x. PROP A x) &&& (!!x. PROP B x))"
proof
  assume conj: "!!x. PROP A x &&& PROP B x"
  show "(!!x. PROP A x) &&& (!!x. PROP B x)"
  proof -
    fix x
    from conj show "PROP A x" by (rule conjunctionD1)
    from conj show "PROP B x" by (rule conjunctionD2)
  qed
next
  assume conj: "(!!x. PROP A x) &&& (!!x. PROP B x)"
  fix x
  show "PROP A x &&& PROP B x"
  proof -
    show "PROP A x" by (rule conj [THEN conjunctionD1, rule_format])
    show "PROP B x" by (rule conj [THEN conjunctionD2, rule_format])
  qed
qed

lemma imp_conjunction:
  "(PROP A ==> PROP B &&& PROP C) == (PROP A ==> PROP B) &&& (PROP A ==> PROP C)"
proof
  assume conj: "PROP A ==> PROP B &&& PROP C"
  show "(PROP A ==> PROP B) &&& (PROP A ==> PROP C)"
  proof -
    assume "PROP A"
    from conj [OF `PROP A`] show "PROP B" by (rule conjunctionD1)
    from conj [OF `PROP A`] show "PROP C" by (rule conjunctionD2)
  qed
next
  assume conj: "(PROP A ==> PROP B) &&& (PROP A ==> PROP C)"
  assume "PROP A"
  show "PROP B &&& PROP C"
  proof -
    from `PROP A` show "PROP B" by (rule conj [THEN conjunctionD1])
    from `PROP A` show "PROP C" by (rule conj [THEN conjunctionD2])
  qed
qed

lemma conjunction_imp:
  "(PROP A &&& PROP B ==> PROP C) == (PROP A ==> PROP B ==> PROP C)"
proof
  assume r: "PROP A &&& PROP B ==> PROP C"
  assume ab: "PROP A" "PROP B"
  show "PROP C"
  proof (rule r)
    from ab show "PROP A &&& PROP B" .
  qed
next
  assume r: "PROP A ==> PROP B ==> PROP C"
  assume conj: "PROP A &&& PROP B"
  show "PROP C"
  proof (rule r)
    from conj show "PROP A" by (rule conjunctionD1)
    from conj show "PROP B" by (rule conjunctionD2)
  qed
qed

end

