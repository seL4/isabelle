(*:maxLineLen=78:*)

theory Quick_Reference
  imports Main Base
begin

chapter \<open>Isabelle/Isar quick reference \label{ap:refcard}\<close>

section \<open>Proof commands\<close>

subsection \<open>Main grammar \label{ap:main-grammar}\<close>

text \<open>
  \begin{tabular}{rcl}
    \<open>main\<close> & = & \<^theory_text>\<open>notepad begin "statement\<^sup>*" end\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>theorem name: props if name: props for vars "proof"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>theorem name:\<close> \\
    & & \quad\<^theory_text>\<open>fixes vars\<close> \\
    & & \quad\<^theory_text>\<open>assumes name: props\<close> \\
    & & \quad\<^theory_text>\<open>shows name: props "proof"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>theorem name:\<close> \\
    & & \quad\<^theory_text>\<open>fixes vars\<close> \\
    & & \quad\<^theory_text>\<open>assumes name: props\<close> \\
    & & \quad\<^theory_text>\<open>obtains (name) vars where props | \<dots> "proof"\<close> \\
    \<open>proof\<close> & = & \<^theory_text>\<open>"refinement\<^sup>*" proper_proof\<close> \\
    \<open>refinement\<close> & = &  \<^theory_text>\<open>apply method\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>supply name = thms\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>subgoal premises name for vars "proof"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>using thms\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>unfolding thms\<close> \\
    \<open>proper_proof\<close> & = & \<^theory_text>\<open>proof "method\<^sup>?" "statement\<^sup>*" qed "method\<^sup>?"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>done\<close> \\
    \<open>statement\<close> & = & \<^theory_text>\<open>{ "statement\<^sup>*" }\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>next\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>note name = thms\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>let "term" = "term"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>write name  (mixfix)\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>fix vars\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>assume name: props if props for vars\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>then"\<^sup>?" goal\<close> \\
    \<open>goal\<close> & = & \<^theory_text>\<open>have name: props if name: props for vars "proof"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>show name: props if name: props for vars "proof"\<close> \\
  \end{tabular}
\<close>


subsection \<open>Primitives\<close>

text \<open>
  \begin{tabular}{ll}
    \<^theory_text>\<open>fix x\<close> & augment context by \<open>\<And>x. \<box>\<close> \\
    \<^theory_text>\<open>assume a: A\<close> & augment context by \<open>A \<Longrightarrow> \<box>\<close> \\
    \<^theory_text>\<open>then\<close> & indicate forward chaining of facts \\
    \<^theory_text>\<open>have a: A\<close> & prove local result \\
    \<^theory_text>\<open>show a: A\<close> & prove local result, refining some goal \\
    \<^theory_text>\<open>using a\<close> & indicate use of additional facts \\
    \<^theory_text>\<open>unfolding a\<close> & unfold definitional equations \\
    \<^theory_text>\<open>proof m\<^sub>1 \<dots> qed m\<^sub>2\<close> & indicate proof structure and refinements \\
    \<^theory_text>\<open>{ \<dots> }\<close> & indicate explicit blocks \\
    \<^theory_text>\<open>next\<close> & switch proof blocks \\
    \<^theory_text>\<open>note a = b\<close> & reconsider and declare facts \\
    \<^theory_text>\<open>let p = t\<close> & abbreviate terms by higher-order matching \\
    \<^theory_text>\<open>write c  (mx)\<close> & declare local mixfix syntax \\
  \end{tabular}
\<close>


subsection \<open>Abbreviations and synonyms\<close>

text \<open>
  \begin{tabular}{rcl}
    \<^theory_text>\<open>by m\<^sub>1 m\<^sub>2\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>proof m\<^sub>1 qed m\<^sub>2\<close> \\
    \<^theory_text>\<open>..\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>by standard\<close> \\
    \<^theory_text>\<open>.\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>by this\<close> \\
    \<^theory_text>\<open>from a\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>note a then\<close> \\
    \<^theory_text>\<open>with a\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>from a and this\<close> \\
    \<^theory_text>\<open>from this\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>then\<close> \\
  \end{tabular}
\<close>


subsection \<open>Derived elements\<close>

text \<open>
  \begin{tabular}{rcl}
    \<^theory_text>\<open>also"\<^sub>0"\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>note calculation = this\<close> \\
    \<^theory_text>\<open>also"\<^sub>n\<^sub>+\<^sub>1"\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>note calculation = trans [OF calculation this]\<close> \\
    \<^theory_text>\<open>finally\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>also from calculation\<close> \\[0.5ex]
    \<^theory_text>\<open>moreover\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>note calculation = calculation this\<close> \\
    \<^theory_text>\<open>ultimately\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>moreover from calculation\<close> \\[0.5ex]
    \<^theory_text>\<open>presume a: A\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>assume a: A\<close> \\
    \<^theory_text>\<open>define x where "x = t"\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>fix x assume x_def: "x = t"\<close> \\
    \<^theory_text>\<open>consider x where A | \<dots>\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>have thesis\<close> \\
    & & \quad \<^theory_text>\<open>if "\<And>x. A \<Longrightarrow> thesis" and \<dots> for thesis\<close> \\
    \<^theory_text>\<open>obtain x where a: A \<proof>\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>consider x where A \<proof>\<close> \\
    & & \<^theory_text>\<open>fix x assume a: A\<close> \\
    \<^theory_text>\<open>case c\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>fix x assume c: A\<close> \\
    \<^theory_text>\<open>sorry\<close> & \<open>\<approx>\<close> & \<^theory_text>\<open>by cheating\<close> \\
  \end{tabular}
\<close>


subsection \<open>Diagnostic commands\<close>

text \<open>
  \begin{tabular}{ll}
    \<^theory_text>\<open>typ \<tau>\<close> & print type \\
    \<^theory_text>\<open>term t\<close> & print term \\
    \<^theory_text>\<open>prop \<phi>\<close> & print proposition \\
    \<^theory_text>\<open>thm a\<close> & print fact \\
    \<^theory_text>\<open>print_statement a\<close> & print fact in long statement form \\
  \end{tabular}
\<close>


section \<open>Proof methods\<close>

text \<open>
  \begin{tabular}{ll}
    \multicolumn{2}{l}{\<^bold>\<open>Single steps (forward-chaining facts)\<close>} \\[0.5ex]
    @{method assumption} & apply some goal assumption \\
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
    @{method intro_locales} & locale introduction rules (without body) \\
    @{method unfold_locales} & locale introduction rules (with body) \\
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


section \<open>Proof scripts\<close>

subsection \<open>Commands\<close>

text \<open>
  \begin{tabular}{ll}
    \<^theory_text>\<open>apply m\<close> & apply proof method during backwards refinement \\
    \<^theory_text>\<open>apply_end m\<close> & apply proof method (as if in terminal position) \\
    \<^theory_text>\<open>supply a\<close> & supply facts during backwards refinement \\
    \<^theory_text>\<open>subgoal\<close> & nested proof during backwards refinement \\
    \<^theory_text>\<open>defer n\<close> & move subgoal to end \\
    \<^theory_text>\<open>prefer n\<close> & move subgoal to start \\
    \<^theory_text>\<open>back\<close> & backtrack last command \\
    \<^theory_text>\<open>done\<close> & complete proof \\
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
