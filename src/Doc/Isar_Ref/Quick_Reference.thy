(*:maxLineLen=78:*)

theory Quick_Reference
imports Base Main
begin

chapter \<open>Isabelle/Isar quick reference \label{ap:refcard}\<close>

section \<open>Proof commands\<close>

subsection \<open>Primitives and basic syntax\<close>

text \<open>
  \begin{tabular}{ll}
    @{command "fix"}~\<open>x\<close> & augment context by \<open>\<And>x. \<box>\<close> \\
    @{command "assume"}~\<open>a: \<phi>\<close> & augment context by \<open>\<phi> \<Longrightarrow> \<box>\<close> \\
    @{command "then"} & indicate forward chaining of facts \\
    @{command "have"}~\<open>a: \<phi>\<close> & prove local result \\
    @{command "show"}~\<open>a: \<phi>\<close> & prove local result, refining some goal \\
    @{command "using"}~\<open>a\<close> & indicate use of additional facts \\
    @{command "unfolding"}~\<open>a\<close> & unfold definitional equations \\
    @{command "proof"}~\<open>m\<^sub>1\<close>~\dots~@{command "qed"}~\<open>m\<^sub>2\<close> & indicate proof structure and refinements \\
    @{command "{"}~\<open>\<dots>\<close>~@{command "}"} & indicate explicit blocks \\
    @{command "next"} & switch blocks \\
    @{command "note"}~\<open>a = b\<close> & reconsider facts \\
    @{command "let"}~\<open>p = t\<close> & abbreviate terms by higher-order matching \\
    @{command "write"}~\<open>c  (mx)\<close> & declare local mixfix syntax \\
  \end{tabular}

  \<^medskip>

  \begin{tabular}{rcl}
    \<open>proof\<close> & = & \<open>prfx\<^sup>*\<close>~@{command "proof"}~\<open>method\<^sup>? stmt\<^sup>*\<close>~@{command "qed"}~\<open>method\<^sup>?\<close> \\
    & \<open>|\<close> & \<open>prfx\<^sup>*\<close>~@{command "done"} \\
    \<open>prfx\<close> & = & @{command "apply"}~\<open>method\<close> \\
    & \<open>|\<close> & @{command "using"}~\<open>facts\<close> \\
    & \<open>|\<close> & @{command "unfolding"}~\<open>facts\<close> \\
    \<open>stmt\<close> & = & @{command "{"}~\<open>stmt\<^sup>*\<close>~@{command "}"} \\
    & \<open>|\<close> & @{command "next"} \\
    & \<open>|\<close> & @{command "note"}~\<open>name = facts\<close> \\
    & \<open>|\<close> & @{command "let"}~\<open>term = term\<close> \\
    & \<open>|\<close> & @{command "write"}~\<open>name (mixfix)\<close> \\
    & \<open>|\<close> & @{command "fix"}~\<open>var\<^sup>+\<close> \\
    & \<open>|\<close> & @{command "assume"}~\<open>name: props\<close> \\
    & \<open>|\<close> & @{command "then"}\<open>\<^sup>?\<close>~\<open>goal\<close> \\
    \<open>goal\<close> & = & @{command "have"}~\<open>name: props proof\<close> \\
    & \<open>|\<close> & @{command "show"}~\<open>name: props proof\<close> \\
  \end{tabular}
\<close>


subsection \<open>Abbreviations and synonyms\<close>

text \<open>
  \begin{tabular}{rcl}
    @{command "by"}~\<open>m\<^sub>1 m\<^sub>2\<close> & \<open>\<equiv>\<close> &
      @{command "proof"}~\<open>m\<^sub>1\<close>~@{command "qed"}~\<open>m\<^sub>2\<close> \\
    @{command ".."} & \<open>\<equiv>\<close> & @{command "by"}~\<open>standard\<close> \\
    @{command "."} & \<open>\<equiv>\<close> & @{command "by"}~\<open>this\<close> \\
    @{command "hence"} & \<open>\<equiv>\<close> & @{command "then"}~@{command "have"} \\
    @{command "thus"} & \<open>\<equiv>\<close> & @{command "then"}~@{command "show"} \\
    @{command "from"}~\<open>a\<close> & \<open>\<equiv>\<close> & @{command "note"}~\<open>a\<close>~@{command "then"} \\
    @{command "with"}~\<open>a\<close> & \<open>\<equiv>\<close> & @{command "from"}~\<open>a \<AND> this\<close> \\
    @{command "from"}~\<open>this\<close> & \<open>\<equiv>\<close> & @{command "then"} \\
    @{command "from"}~\<open>this\<close>~@{command "have"} & \<open>\<equiv>\<close> & @{command "hence"} \\
    @{command "from"}~\<open>this\<close>~@{command "show"} & \<open>\<equiv>\<close> & @{command "thus"} \\
  \end{tabular}
\<close>


subsection \<open>Derived elements\<close>

text \<open>
  \begin{tabular}{rcl}
    @{command "also"}\<open>\<^sub>0\<close> & \<open>\<approx>\<close> &
      @{command "note"}~\<open>calculation = this\<close> \\
    @{command "also"}\<open>\<^sub>n\<^sub>+\<^sub>1\<close> & \<open>\<approx>\<close> &
      @{command "note"}~\<open>calculation = trans [OF calculation this]\<close> \\
    @{command "finally"} & \<open>\<approx>\<close> &
      @{command "also"}~@{command "from"}~\<open>calculation\<close> \\[0.5ex]
    @{command "moreover"} & \<open>\<approx>\<close> &
      @{command "note"}~\<open>calculation = calculation this\<close> \\
    @{command "ultimately"} & \<open>\<approx>\<close> &
      @{command "moreover"}~@{command "from"}~\<open>calculation\<close> \\[0.5ex]
    @{command "presume"}~\<open>a: \<phi>\<close> & \<open>\<approx>\<close> &
      @{command "assume"}~\<open>a: \<phi>\<close> \\
    @{command "def"}~\<open>a: x \<equiv> t\<close> & \<open>\<approx>\<close> &
      @{command "fix"}~\<open>x\<close>~@{command "assume"}~\<open>a: x \<equiv> t\<close> \\
    @{command "obtain"}~\<open>x \<WHERE> a: \<phi>\<close> & \<open>\<approx>\<close> &
      \<open>\<dots>\<close>~@{command "fix"}~\<open>x\<close>~@{command "assume"}~\<open>a: \<phi>\<close> \\
    @{command "case"}~\<open>c\<close> & \<open>\<approx>\<close> &
      @{command "fix"}~\<open>x\<close>~@{command "assume"}~\<open>c: \<phi>\<close> \\
    @{command "sorry"} & \<open>\<approx>\<close> &
      @{command "by"}~\<open>cheating\<close> \\
  \end{tabular}
\<close>


subsection \<open>Diagnostic commands\<close>

text \<open>
  \begin{tabular}{ll}
    @{command "print_state"} & print proof state \\
    @{command "print_statement"} & print fact in long statement form \\
    @{command "thm"}~\<open>a\<close> & print fact \\
    @{command "prop"}~\<open>\<phi>\<close> & print proposition \\
    @{command "term"}~\<open>t\<close> & print term \\
    @{command "typ"}~\<open>\<tau>\<close> & print type \\
  \end{tabular}
\<close>


section \<open>Proof methods\<close>

text \<open>
  \begin{tabular}{ll}
    \multicolumn{2}{l}{\<^bold>\<open>Single steps (forward-chaining facts)\<close>} \\[0.5ex]
    @{method assumption} & apply some assumption \\
    @{method this} & apply current facts \\
    @{method rule}~\<open>a\<close> & apply some rule  \\
    @{method standard} & apply standard rule (default for @{command "proof"}) \\
    @{method contradiction} & apply \<open>\<not>\<close> elimination rule (any order) \\
    @{method cases}~\<open>t\<close> & case analysis (provides cases) \\
    @{method induct}~\<open>x\<close> & proof by induction (provides cases) \\[2ex]

    \multicolumn{2}{l}{\<^bold>\<open>Repeated steps (inserting facts)\<close>} \\[0.5ex]
    @{method "-"} & no rules \\
    @{method intro}~\<open>a\<close> & introduction rules \\
    @{method intro_classes} & class introduction rules \\
    @{method elim}~\<open>a\<close> & elimination rules \\
    @{method unfold}~\<open>a\<close> & definitional rewrite rules \\[2ex]

    \multicolumn{2}{l}{\<^bold>\<open>Automated proof tools (inserting facts)\<close>} \\[0.5ex]
    @{method iprover} & intuitionistic proof search \\
    @{method blast}, @{method fast} & Classical Reasoner \\
    @{method simp}, @{method simp_all} & Simplifier (+ Splitter) \\
    @{method auto}, @{method force} & Simplifier + Classical Reasoner \\
    @{method arith} & Arithmetic procedures \\
  \end{tabular}
\<close>


section \<open>Attributes\<close>

text \<open>
  \begin{tabular}{ll}
    \multicolumn{2}{l}{\<^bold>\<open>Rules\<close>} \\[0.5ex]
    @{attribute OF}~\<open>a\<close> & rule resolved with facts (skipping ``\<open>_\<close>'') \\
    @{attribute of}~\<open>t\<close> & rule instantiated with terms (skipping ``\<open>_\<close>'') \\
    @{attribute "where"}~\<open>x = t\<close> & rule instantiated with terms, by variable name \\
    @{attribute symmetric} & resolution with symmetry rule \\
    @{attribute THEN}~\<open>b\<close> & resolution with another rule \\
    @{attribute rule_format} & result put into standard rule format \\
    @{attribute elim_format} & destruct rule turned into elimination rule format \\[1ex]

    \multicolumn{2}{l}{\<^bold>\<open>Declarations\<close>} \\[0.5ex]
    @{attribute simp} & Simplifier rule \\
    @{attribute intro}, @{attribute elim}, @{attribute dest} & Pure or Classical Reasoner rule \\
    @{attribute iff} & Simplifier + Classical Reasoner rule \\
    @{attribute split} & case split rule \\
    @{attribute trans} & transitivity rule \\
    @{attribute sym} & symmetry rule \\
  \end{tabular}
\<close>


section \<open>Rule declarations and methods\<close>

text \<open>
  \begin{tabular}{l|lllll}
      & @{method rule} & @{method iprover} & @{method blast} & @{method simp} & @{method auto} \\
      &                &                   & @{method fast} & @{method simp_all} & @{method force} \\
    \hline
    @{attribute Pure.elim}\<open>!\<close> @{attribute Pure.intro}\<open>!\<close>
      & \<open>\<times>\<close>    & \<open>\<times>\<close> \\
    @{attribute Pure.elim} @{attribute Pure.intro}
      & \<open>\<times>\<close>    & \<open>\<times>\<close> \\
    @{attribute elim}\<open>!\<close> @{attribute intro}\<open>!\<close>
      & \<open>\<times>\<close>    &                    & \<open>\<times>\<close>          &                     & \<open>\<times>\<close> \\
    @{attribute elim} @{attribute intro}
      & \<open>\<times>\<close>    &                    & \<open>\<times>\<close>          &                     & \<open>\<times>\<close> \\
    @{attribute iff}
      & \<open>\<times>\<close>    &                    & \<open>\<times>\<close>          & \<open>\<times>\<close>         & \<open>\<times>\<close> \\
    @{attribute iff}\<open>?\<close>
      & \<open>\<times>\<close> \\
    @{attribute elim}\<open>?\<close> @{attribute intro}\<open>?\<close>
      & \<open>\<times>\<close> \\
    @{attribute simp}
      &                &                    &                      & \<open>\<times>\<close>         & \<open>\<times>\<close> \\
    @{attribute cong}
      &                &                    &                      & \<open>\<times>\<close>         & \<open>\<times>\<close> \\
    @{attribute split}
      &                &                    &                      & \<open>\<times>\<close>         & \<open>\<times>\<close> \\
  \end{tabular}
\<close>


section \<open>Emulating tactic scripts\<close>

subsection \<open>Commands\<close>

text \<open>
  \begin{tabular}{ll}
    @{command "apply"}~\<open>m\<close> & apply proof method at initial position \\
    @{command "apply_end"}~\<open>m\<close> & apply proof method near terminal position \\
    @{command "done"} & complete proof \\
    @{command "defer"}~\<open>n\<close> & move subgoal to end \\
    @{command "prefer"}~\<open>n\<close> & move subgoal to beginning \\
    @{command "back"} & backtrack last command \\
  \end{tabular}
\<close>


subsection \<open>Methods\<close>

text \<open>
  \begin{tabular}{ll}
    @{method rule_tac}~\<open>insts\<close> & resolution (with instantiation) \\
    @{method erule_tac}~\<open>insts\<close> & elim-resolution (with instantiation) \\
    @{method drule_tac}~\<open>insts\<close> & destruct-resolution (with instantiation) \\
    @{method frule_tac}~\<open>insts\<close> & forward-resolution (with instantiation) \\
    @{method cut_tac}~\<open>insts\<close> & insert facts (with instantiation) \\
    @{method thin_tac}~\<open>\<phi>\<close> & delete assumptions \\
    @{method subgoal_tac}~\<open>\<phi>\<close> & new claims \\
    @{method rename_tac}~\<open>x\<close> & rename innermost goal parameters \\
    @{method rotate_tac}~\<open>n\<close> & rotate assumptions of goal \\
    @{method tactic}~\<open>text\<close> & arbitrary ML tactic \\
    @{method case_tac}~\<open>t\<close> & exhaustion (datatypes) \\
    @{method induct_tac}~\<open>x\<close> & induction (datatypes) \\
    @{method ind_cases}~\<open>t\<close> & exhaustion + simplification (inductive predicates) \\
  \end{tabular}
\<close>

end
