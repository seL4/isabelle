theory Quick_Reference
imports Base Main
begin

chapter {* Isabelle/Isar quick reference \label{ap:refcard} *}

section {* Proof commands *}

subsection {* Primitives and basic syntax *}

text {*
  \begin{tabular}{ll}
    @{command "fix"}~@{text x} & augment context by @{text "\<And>x. \<box>"} \\
    @{command "assume"}~@{text "a: \<phi>"} & augment context by @{text "\<phi> \<Longrightarrow> \<box>"} \\
    @{command "then"} & indicate forward chaining of facts \\
    @{command "have"}~@{text "a: \<phi>"} & prove local result \\
    @{command "show"}~@{text "a: \<phi>"} & prove local result, refining some goal \\
    @{command "using"}~@{text a} & indicate use of additional facts \\
    @{command "unfolding"}~@{text a} & unfold definitional equations \\
    @{command "proof"}~@{text "m\<^sub>1"}~\dots~@{command "qed"}~@{text "m\<^sub>2"} & indicate proof structure and refinements \\
    @{command "{"}~@{text "\<dots>"}~@{command "}"} & indicate explicit blocks \\
    @{command "next"} & switch blocks \\
    @{command "note"}~@{text "a = b"} & reconsider facts \\
    @{command "let"}~@{text "p = t"} & abbreviate terms by higher-order matching \\
    @{command "write"}~@{text "c  (mx)"} & declare local mixfix syntax \\
  \end{tabular}

  \medskip

  \begin{tabular}{rcl}
    @{text "proof"} & = & @{text "prfx\<^sup>*"}~@{command "proof"}~@{text "method\<^sup>? stmt\<^sup>*"}~@{command "qed"}~@{text "method\<^sup>?"} \\
    & @{text "|"} & @{text "prfx\<^sup>*"}~@{command "done"} \\
    @{text prfx} & = & @{command "apply"}~@{text method} \\
    & @{text "|"} & @{command "using"}~@{text "facts"} \\
    & @{text "|"} & @{command "unfolding"}~@{text "facts"} \\
    @{text stmt} & = & @{command "{"}~@{text "stmt\<^sup>*"}~@{command "}"} \\
    & @{text "|"} & @{command "next"} \\
    & @{text "|"} & @{command "note"}~@{text "name = facts"} \\
    & @{text "|"} & @{command "let"}~@{text "term = term"} \\
    & @{text "|"} & @{command "write"}~@{text "name (mixfix)"} \\
    & @{text "|"} & @{command "fix"}~@{text "var\<^sup>+"} \\
    & @{text "|"} & @{command "assume"}~@{text "name: props"} \\
    & @{text "|"} & @{command "then"}@{text "\<^sup>?"}~@{text goal} \\
    @{text goal} & = & @{command "have"}~@{text "name: props proof"} \\
    & @{text "|"} & @{command "show"}~@{text "name: props proof"} \\
  \end{tabular}
*}


subsection {* Abbreviations and synonyms *}

text {*
  \begin{tabular}{rcl}
    @{command "by"}~@{text "m\<^sub>1 m\<^sub>2"} & @{text "\<equiv>"} &
      @{command "proof"}~@{text "m\<^sub>1"}~@{command "qed"}~@{text "m\<^sub>2"} \\
    @{command ".."} & @{text "\<equiv>"} & @{command "by"}~@{text rule} \\
    @{command "."} & @{text "\<equiv>"} & @{command "by"}~@{text this} \\
    @{command "hence"} & @{text "\<equiv>"} & @{command "then"}~@{command "have"} \\
    @{command "thus"} & @{text "\<equiv>"} & @{command "then"}~@{command "show"} \\
    @{command "from"}~@{text a} & @{text "\<equiv>"} & @{command "note"}~@{text a}~@{command "then"} \\
    @{command "with"}~@{text a} & @{text "\<equiv>"} & @{command "from"}~@{text "a \<AND> this"} \\
    @{command "from"}~@{text this} & @{text "\<equiv>"} & @{command "then"} \\
    @{command "from"}~@{text this}~@{command "have"} & @{text "\<equiv>"} & @{command "hence"} \\
    @{command "from"}~@{text this}~@{command "show"} & @{text "\<equiv>"} & @{command "thus"} \\
  \end{tabular}
*}


subsection {* Derived elements *}

text {*
  \begin{tabular}{rcl}
    @{command "also"}@{text "\<^sub>0"} & @{text "\<approx>"} &
      @{command "note"}~@{text "calculation = this"} \\
    @{command "also"}@{text "\<^sub>n\<^sub>+\<^sub>1"} & @{text "\<approx>"} &
      @{command "note"}~@{text "calculation = trans [OF calculation this]"} \\
    @{command "finally"} & @{text "\<approx>"} &
      @{command "also"}~@{command "from"}~@{text calculation} \\[0.5ex]
    @{command "moreover"} & @{text "\<approx>"} &
      @{command "note"}~@{text "calculation = calculation this"} \\
    @{command "ultimately"} & @{text "\<approx>"} &
      @{command "moreover"}~@{command "from"}~@{text calculation} \\[0.5ex]
    @{command "presume"}~@{text "a: \<phi>"} & @{text "\<approx>"} &
      @{command "assume"}~@{text "a: \<phi>"} \\
    @{command "def"}~@{text "a: x \<equiv> t"} & @{text "\<approx>"} &
      @{command "fix"}~@{text x}~@{command "assume"}~@{text "a: x \<equiv> t"} \\
    @{command "obtain"}~@{text "x \<WHERE> a: \<phi>"} & @{text "\<approx>"} &
      @{text "\<dots>"}~@{command "fix"}~@{text x}~@{command "assume"}~@{text "a: \<phi>"} \\
    @{command "case"}~@{text c} & @{text "\<approx>"} &
      @{command "fix"}~@{text x}~@{command "assume"}~@{text "c: \<phi>"} \\
    @{command "sorry"} & @{text "\<approx>"} &
      @{command "by"}~@{text cheating} \\
  \end{tabular}
*}


subsection {* Diagnostic commands *}

text {*
  \begin{tabular}{ll}
    @{command "pr"} & print current state \\
    @{command "thm"}~@{text a} & print fact \\
    @{command "prop"}~@{text \<phi>} & print proposition \\
    @{command "term"}~@{text t} & print term \\
    @{command "typ"}~@{text \<tau>} & print type \\
  \end{tabular}
*}


section {* Proof methods *}

text {*
  \begin{tabular}{ll}
    \multicolumn{2}{l}{\textbf{Single steps (forward-chaining facts)}} \\[0.5ex]
    @{method assumption} & apply some assumption \\
    @{method this} & apply current facts \\
    @{method rule}~@{text a} & apply some rule  \\
    @{method rule} & apply standard rule (default for @{command "proof"}) \\
    @{method contradiction} & apply @{text "\<not>"} elimination rule (any order) \\
    @{method cases}~@{text t} & case analysis (provides cases) \\
    @{method induct}~@{text x} & proof by induction (provides cases) \\[2ex]

    \multicolumn{2}{l}{\textbf{Repeated steps (inserting facts)}} \\[0.5ex]
    @{method "-"} & no rules \\
    @{method intro}~@{text a} & introduction rules \\
    @{method intro_classes} & class introduction rules \\
    @{method elim}~@{text a} & elimination rules \\
    @{method unfold}~@{text a} & definitional rewrite rules \\[2ex]

    \multicolumn{2}{l}{\textbf{Automated proof tools (inserting facts)}} \\[0.5ex]
    @{method iprover} & intuitionistic proof search \\
    @{method blast}, @{method fast} & Classical Reasoner \\
    @{method simp}, @{method simp_all} & Simplifier (+ Splitter) \\
    @{method auto}, @{method force} & Simplifier + Classical Reasoner \\
    @{method arith} & Arithmetic procedures \\
  \end{tabular}
*}


section {* Attributes *}

text {*
  \begin{tabular}{ll}
    \multicolumn{2}{l}{\textbf{Rules}} \\[0.5ex]
    @{attribute OF}~@{text a} & rule resolved with facts (skipping ``@{text _}'') \\
    @{attribute of}~@{text t} & rule instantiated with terms (skipping ``@{text _}'') \\
    @{attribute "where"}~@{text "x = t"} & rule instantiated with terms, by variable name \\
    @{attribute symmetric} & resolution with symmetry rule \\
    @{attribute THEN}~@{text b} & resolution with another rule \\
    @{attribute rule_format} & result put into standard rule format \\
    @{attribute elim_format} & destruct rule turned into elimination rule format \\[1ex]

    \multicolumn{2}{l}{\textbf{Declarations}} \\[0.5ex]
    @{attribute simp} & Simplifier rule \\
    @{attribute intro}, @{attribute elim}, @{attribute dest} & Pure or Classical Reasoner rule \\
    @{attribute iff} & Simplifier + Classical Reasoner rule \\
    @{attribute split} & case split rule \\
    @{attribute trans} & transitivity rule \\
    @{attribute sym} & symmetry rule \\
  \end{tabular}
*}


section {* Rule declarations and methods *}

text {*
  \begin{tabular}{l|lllll}
      & @{method rule} & @{method iprover} & @{method blast} & @{method simp} & @{method auto} \\
      &                &                   & @{method fast} & @{method simp_all} & @{method force} \\
    \hline
    @{attribute Pure.elim}@{text "!"} @{attribute Pure.intro}@{text "!"}
      & @{text "\<times>"}    & @{text "\<times>"} \\
    @{attribute Pure.elim} @{attribute Pure.intro}
      & @{text "\<times>"}    & @{text "\<times>"} \\
    @{attribute elim}@{text "!"} @{attribute intro}@{text "!"}
      & @{text "\<times>"}    &                    & @{text "\<times>"}          &                     & @{text "\<times>"} \\
    @{attribute elim} @{attribute intro}
      & @{text "\<times>"}    &                    & @{text "\<times>"}          &                     & @{text "\<times>"} \\
    @{attribute iff}
      & @{text "\<times>"}    &                    & @{text "\<times>"}          & @{text "\<times>"}         & @{text "\<times>"} \\
    @{attribute iff}@{text "?"}
      & @{text "\<times>"} \\
    @{attribute elim}@{text "?"} @{attribute intro}@{text "?"}
      & @{text "\<times>"} \\
    @{attribute simp}
      &                &                    &                      & @{text "\<times>"}         & @{text "\<times>"} \\
    @{attribute cong}
      &                &                    &                      & @{text "\<times>"}         & @{text "\<times>"} \\
    @{attribute split}
      &                &                    &                      & @{text "\<times>"}         & @{text "\<times>"} \\
  \end{tabular}
*}


section {* Emulating tactic scripts *}

subsection {* Commands *}

text {*
  \begin{tabular}{ll}
    @{command "apply"}~@{text m} & apply proof method at initial position \\
    @{command "apply_end"}~@{text m} & apply proof method near terminal position \\
    @{command "done"} & complete proof \\
    @{command "defer"}~@{text n} & move subgoal to end \\
    @{command "prefer"}~@{text n} & move subgoal to beginning \\
    @{command "back"} & backtrack last command \\
  \end{tabular}
*}


subsection {* Methods *}

text {*
  \begin{tabular}{ll}
    @{method rule_tac}~@{text insts} & resolution (with instantiation) \\
    @{method erule_tac}~@{text insts} & elim-resolution (with instantiation) \\
    @{method drule_tac}~@{text insts} & destruct-resolution (with instantiation) \\
    @{method frule_tac}~@{text insts} & forward-resolution (with instantiation) \\
    @{method cut_tac}~@{text insts} & insert facts (with instantiation) \\
    @{method thin_tac}~@{text \<phi>} & delete assumptions \\
    @{method subgoal_tac}~@{text \<phi>} & new claims \\
    @{method rename_tac}~@{text x} & rename innermost goal parameters \\
    @{method rotate_tac}~@{text n} & rotate assumptions of goal \\
    @{method tactic}~@{text "text"} & arbitrary ML tactic \\
    @{method case_tac}~@{text t} & exhaustion (datatypes) \\
    @{method induct_tac}~@{text x} & induction (datatypes) \\
    @{method ind_cases}~@{text t} & exhaustion + simplification (inductive predicates) \\
  \end{tabular}
*}

end
