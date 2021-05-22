(*:maxLineLen=78:*)

theory Generic
imports Main Base
begin

chapter \<open>Generic tools and packages \label{ch:gen-tools}\<close>

section \<open>Configuration options \label{sec:config}\<close>

text \<open>
  Isabelle/Pure maintains a record of named configuration options within the
  theory or proof context, with values of type \<^ML_type>\<open>bool\<close>, \<^ML_type>\<open>int\<close>, \<^ML_type>\<open>real\<close>, or \<^ML_type>\<open>string\<close>. Tools may declare options in
  ML, and then refer to these values (relative to the context). Thus global
  reference variables are easily avoided. The user may change the value of a
  configuration option by means of an associated attribute of the same name.
  This form of context declaration works particularly well with commands such
  as @{command "declare"} or @{command "using"} like this:
\<close>

(*<*)experiment begin(*>*)
declare [[show_main_goal = false]]

notepad
begin
  note [[show_main_goal = true]]
end
(*<*)end(*>*)

text \<open>
  \begin{matharray}{rcll}
    @{command_def "print_options"} & : & \<open>context \<rightarrow>\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command print_options} ('!'?)
    ;
    @{syntax name} ('=' ('true' | 'false' | @{syntax int} | @{syntax float} | @{syntax name}))?
  \<close>

  \<^descr> @{command "print_options"} prints the available configuration options,
  with names, types, and current values; the ``\<open>!\<close>'' option indicates extra
  verbosity.
  
  \<^descr> \<open>name = value\<close> as an attribute expression modifies the named option, with
  the syntax of the value depending on the option's type. For \<^ML_type>\<open>bool\<close>
  the default value is \<open>true\<close>. Any attempt to change a global option in a
  local context is ignored.
\<close>


section \<open>Basic proof tools\<close>

subsection \<open>Miscellaneous methods and attributes \label{sec:misc-meth-att}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def unfold} & : & \<open>method\<close> \\
    @{method_def fold} & : & \<open>method\<close> \\
    @{method_def insert} & : & \<open>method\<close> \\[0.5ex]
    @{method_def erule}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def drule}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def frule}\<open>\<^sup>*\<close> & : & \<open>method\<close> \\
    @{method_def intro} & : & \<open>method\<close> \\
    @{method_def elim} & : & \<open>method\<close> \\
    @{method_def fail} & : & \<open>method\<close> \\
    @{method_def succeed} & : & \<open>method\<close> \\
    @{method_def sleep} & : & \<open>method\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@@{method fold} | @@{method unfold} | @@{method insert}) @{syntax thms}
    ;
    (@@{method erule} | @@{method drule} | @@{method frule})
      ('(' @{syntax nat} ')')? @{syntax thms}
    ;
    (@@{method intro} | @@{method elim}) @{syntax thms}?
    ;
    @@{method sleep} @{syntax real}
  \<close>

  \<^descr> @{method unfold}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> and @{method fold}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> expand (or
  fold back) the given definitions throughout all goals; any chained facts
  provided are inserted into the goal and subject to rewriting as well.

  Unfolding works in two stages: first, the given equations are used directly
  for rewriting; second, the equations are passed through the attribute
  @{attribute_ref abs_def} before rewriting --- to ensure that definitions are
  fully expanded, regardless of the actual parameters that are provided.

  \<^descr> @{method insert}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> inserts theorems as facts into all goals of
  the proof state. Note that current facts indicated for forward chaining are
  ignored.

  \<^descr> @{method erule}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close>, @{method drule}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close>, and @{method
  frule}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> are similar to the basic @{method rule} method (see
  \secref{sec:pure-meth-att}), but apply rules by elim-resolution,
  destruct-resolution, and forward-resolution, respectively @{cite
  "isabelle-implementation"}. The optional natural number argument (default 0)
  specifies additional assumption steps to be performed here.

  Note that these methods are improper ones, mainly serving for
  experimentation and tactic script emulation. Different modes of basic rule
  application are usually expressed in Isar at the proof language level,
  rather than via implicit proof state manipulations. For example, a proper
  single-step elimination would be done using the plain @{method rule} method,
  with forward chaining of current facts.

  \<^descr> @{method intro} and @{method elim} repeatedly refine some goal by intro-
  or elim-resolution, after having inserted any chained facts. Exactly the
  rules given as arguments are taken into account; this allows fine-tuned
  decomposition of a proof problem, in contrast to common automated tools.

  \<^descr> @{method fail} yields an empty result sequence; it is the identity of the
  ``\<open>|\<close>'' method combinator (cf.\ \secref{sec:proof-meth}).

  \<^descr> @{method succeed} yields a single (unchanged) result; it is the identity
  of the ``\<open>,\<close>'' method combinator (cf.\ \secref{sec:proof-meth}).

  \<^descr> @{method sleep}~\<open>s\<close> succeeds after a real-time delay of \<open>s\<close> seconds. This
  is occasionally useful for demonstration and testing purposes.


  \begin{matharray}{rcl}
    @{attribute_def tagged} & : & \<open>attribute\<close> \\
    @{attribute_def untagged} & : & \<open>attribute\<close> \\[0.5ex]
    @{attribute_def THEN} & : & \<open>attribute\<close> \\
    @{attribute_def unfolded} & : & \<open>attribute\<close> \\
    @{attribute_def folded} & : & \<open>attribute\<close> \\
    @{attribute_def abs_def} & : & \<open>attribute\<close> \\[0.5ex]
    @{attribute_def rotated} & : & \<open>attribute\<close> \\
    @{attribute_def (Pure) elim_format} & : & \<open>attribute\<close> \\
    @{attribute_def no_vars}\<open>\<^sup>*\<close> & : & \<open>attribute\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{attribute tagged} @{syntax name} @{syntax name}
    ;
    @@{attribute untagged} @{syntax name}
    ;
    @@{attribute THEN} ('[' @{syntax nat} ']')? @{syntax thm}
    ;
    (@@{attribute unfolded} | @@{attribute folded}) @{syntax thms}
    ;
    @@{attribute rotated} @{syntax int}?
  \<close>

  \<^descr> @{attribute tagged}~\<open>name value\<close> and @{attribute untagged}~\<open>name\<close> add and
  remove \<^emph>\<open>tags\<close> of some theorem. Tags may be any list of string pairs that
  serve as formal comment. The first string is considered the tag name, the
  second its value. Note that @{attribute untagged} removes any tags of the
  same name.

  \<^descr> @{attribute THEN}~\<open>a\<close> composes rules by resolution; it resolves with the
  first premise of \<open>a\<close> (an alternative position may be also specified). See
  also \<^ML_op>\<open>RS\<close> in @{cite "isabelle-implementation"}.
  
  \<^descr> @{attribute unfolded}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> and @{attribute folded}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close>
  expand and fold back again the given definitions throughout a rule.

  \<^descr> @{attribute abs_def} turns an equation of the form \<^prop>\<open>f x y \<equiv> t\<close>
  into \<^prop>\<open>f \<equiv> \<lambda>x y. t\<close>, which ensures that @{method simp} steps always
  expand it. This also works for object-logic equality.

  \<^descr> @{attribute rotated}~\<open>n\<close> rotate the premises of a theorem by \<open>n\<close> (default
  1).

  \<^descr> @{attribute (Pure) elim_format} turns a destruction rule into elimination
  rule format, by resolving with the rule \<^prop>\<open>PROP A \<Longrightarrow> (PROP A \<Longrightarrow> PROP B) \<Longrightarrow>
  PROP B\<close>.
  
  Note that the Classical Reasoner (\secref{sec:classical}) provides its own
  version of this operation.

  \<^descr> @{attribute no_vars} replaces schematic variables by free ones; this is
  mainly for tuning output of pretty printed theorems.
\<close>


subsection \<open>Low-level equational reasoning\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def subst} & : & \<open>method\<close> \\
    @{method_def hypsubst} & : & \<open>method\<close> \\
    @{method_def split} & : & \<open>method\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{method subst} ('(' 'asm' ')')? \<newline> ('(' (@{syntax nat}+) ')')? @{syntax thm}
    ;
    @@{method split} @{syntax thms}
  \<close>

  These methods provide low-level facilities for equational reasoning that are
  intended for specialized applications only. Normally, single step
  calculations would be performed in a structured text (see also
  \secref{sec:calculation}), while the Simplifier methods provide the
  canonical way for automated normalization (see \secref{sec:simplifier}).

  \<^descr> @{method subst}~\<open>eq\<close> performs a single substitution step using rule \<open>eq\<close>,
  which may be either a meta or object equality.

  \<^descr> @{method subst}~\<open>(asm) eq\<close> substitutes in an assumption.

  \<^descr> @{method subst}~\<open>(i \<dots> j) eq\<close> performs several substitutions in the
  conclusion. The numbers \<open>i\<close> to \<open>j\<close> indicate the positions to substitute at.
  Positions are ordered from the top of the term tree moving down from left to
  right. For example, in \<open>(a + b) + (c + d)\<close> there are three positions where
  commutativity of \<open>+\<close> is applicable: 1 refers to \<open>a + b\<close>, 2 to the whole
  term, and 3 to \<open>c + d\<close>.

  If the positions in the list \<open>(i \<dots> j)\<close> are non-overlapping (e.g.\ \<open>(2 3)\<close> in
  \<open>(a + b) + (c + d)\<close>) you may assume all substitutions are performed
  simultaneously. Otherwise the behaviour of \<open>subst\<close> is not specified.

  \<^descr> @{method subst}~\<open>(asm) (i \<dots> j) eq\<close> performs the substitutions in the
  assumptions. The positions refer to the assumptions in order from left to
  right. For example, given in a goal of the form \<open>P (a + b) \<Longrightarrow> P (c + d) \<Longrightarrow> \<dots>\<close>,
  position 1 of commutativity of \<open>+\<close> is the subterm \<open>a + b\<close> and position 2 is
  the subterm \<open>c + d\<close>.

  \<^descr> @{method hypsubst} performs substitution using some assumption; this only
  works for equations of the form \<open>x = t\<close> where \<open>x\<close> is a free or bound
  variable.

  \<^descr> @{method split}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> performs single-step case splitting using the
  given rules. Splitting is performed in the conclusion or some assumption of
  the subgoal, depending of the structure of the rule.
  
  Note that the @{method simp} method already involves repeated application of
  split rules as declared in the current context, using @{attribute split},
  for example.
\<close>


section \<open>The Simplifier \label{sec:simplifier}\<close>

text \<open>
  The Simplifier performs conditional and unconditional rewriting and uses
  contextual information: rule declarations in the background theory or local
  proof context are taken into account, as well as chained facts and subgoal
  premises (``local assumptions''). There are several general hooks that allow
  to modify the simplification strategy, or incorporate other proof tools that
  solve sub-problems, produce rewrite rules on demand etc.

  The rewriting strategy is always strictly bottom up, except for congruence
  rules, which are applied while descending into a term. Conditions in
  conditional rewrite rules are solved recursively before the rewrite rule is
  applied.

  The default Simplifier setup of major object logics (HOL, HOLCF, FOL, ZF)
  makes the Simplifier ready for immediate use, without engaging into the
  internal structures. Thus it serves as general-purpose proof tool with the
  main focus on equational reasoning, and a bit more than that.
\<close>


subsection \<open>Simplification methods \label{sec:simp-meth}\<close>

text \<open>
  \begin{tabular}{rcll}
    @{method_def simp} & : & \<open>method\<close> \\
    @{method_def simp_all} & : & \<open>method\<close> \\
    \<open>Pure.\<close>@{method_def (Pure) simp} & : & \<open>method\<close> \\
    \<open>Pure.\<close>@{method_def (Pure) simp_all} & : & \<open>method\<close> \\
    @{attribute_def simp_depth_limit} & : & \<open>attribute\<close> & default \<open>100\<close> \\
  \end{tabular}
  \<^medskip>

  \<^rail>\<open>
    (@@{method simp} | @@{method simp_all}) opt? (@{syntax simpmod} * )
    ;

    opt: '(' ('no_asm' | 'no_asm_simp' | 'no_asm_use' | 'asm_lr' ) ')'
    ;
    @{syntax_def simpmod}: ('add' | 'del' | 'flip' | 'only' |
      'split' (() | '!' | 'del') | 'cong' (() | 'add' | 'del'))
    ':' @{syntax thms}
  \<close>

  \<^descr> @{method simp} invokes the Simplifier on the first subgoal, after
  inserting chained facts as additional goal premises; further rule
  declarations may be included via \<open>(simp add: facts)\<close>. The proof method fails
  if the subgoal remains unchanged after simplification.

  Note that the original goal premises and chained facts are subject to
  simplification themselves, while declarations via \<open>add\<close>/\<open>del\<close> merely follow
  the policies of the object-logic to extract rewrite rules from theorems,
  without further simplification. This may lead to slightly different behavior
  in either case, which might be required precisely like that in some boundary
  situations to perform the intended simplification step!

  \<^medskip>
Modifier \<open>flip\<close> deletes the following theorems from the simpset and adds
their symmetric version (i.e.\ lhs and rhs exchanged). No warning is shown
if the original theorem was not present.

  \<^medskip>
  The \<open>only\<close> modifier first removes all other rewrite rules, looper tactics
  (including split rules), congruence rules, and then behaves like \<open>add\<close>.
  Implicit solvers remain, which means that trivial rules like reflexivity or
  introduction of \<open>True\<close> are available to solve the simplified subgoals, but
  also non-trivial tools like linear arithmetic in HOL. The latter may lead to
  some surprise of the meaning of ``only'' in Isabelle/HOL compared to
  English!

  \<^medskip>
  The \<open>split\<close> modifiers add or delete rules for the Splitter (see also
  \secref{sec:simp-strategies} on the looper). This works only if the
  Simplifier method has been properly setup to include the Splitter (all major
  object logics such HOL, HOLCF, FOL, ZF do this already).
  The \<open>!\<close> option causes the split rules to be used aggressively:
  after each application of a split rule in the conclusion, the \<open>safe\<close>
  tactic of the classical reasoner (see \secref{sec:classical:partial})
  is applied to the new goal. The net effect is that the goal is split into
  the different cases. This option can speed up simplification of goals
  with many nested conditional or case expressions significantly.

  There is also a separate @{method_ref split} method available for
  single-step case splitting. The effect of repeatedly applying \<open>(split thms)\<close>
  can be imitated by ``\<open>(simp only: split: thms)\<close>''.

  \<^medskip>
  The \<open>cong\<close> modifiers add or delete Simplifier congruence rules (see also
  \secref{sec:simp-rules}); the default is to add.

  \<^descr> @{method simp_all} is similar to @{method simp}, but acts on all goals,
  working backwards from the last to the first one as usual in Isabelle.\<^footnote>\<open>The
  order is irrelevant for goals without schematic variables, so simplification
  might actually be performed in parallel here.\<close>

  Chained facts are inserted into all subgoals, before the simplification
  process starts. Further rule declarations are the same as for @{method
  simp}.

  The proof method fails if all subgoals remain unchanged after
  simplification.

  \<^descr> @{attribute simp_depth_limit} limits the number of recursive invocations
  of the Simplifier during conditional rewriting.


  By default the Simplifier methods above take local assumptions fully into
  account, using equational assumptions in the subsequent normalization
  process, or simplifying assumptions themselves. Further options allow to
  fine-tune the behavior of the Simplifier in this respect, corresponding to a
  variety of ML tactics as follows.\<^footnote>\<open>Unlike the corresponding Isar proof
  methods, the ML tactics do not insist in changing the goal state.\<close>

  \begin{center}
  \small
  \begin{tabular}{|l|l|p{0.3\textwidth}|}
  \hline
  Isar method & ML tactic & behavior \\\hline

  \<open>(simp (no_asm))\<close> & \<^ML>\<open>simp_tac\<close> & assumptions are ignored completely
  \\\hline

  \<open>(simp (no_asm_simp))\<close> & \<^ML>\<open>asm_simp_tac\<close> & assumptions are used in the
  simplification of the conclusion but are not themselves simplified \\\hline

  \<open>(simp (no_asm_use))\<close> & \<^ML>\<open>full_simp_tac\<close> & assumptions are simplified but
  are not used in the simplification of each other or the conclusion \\\hline

  \<open>(simp)\<close> & \<^ML>\<open>asm_full_simp_tac\<close> & assumptions are used in the
  simplification of the conclusion and to simplify other assumptions \\\hline

  \<open>(simp (asm_lr))\<close> & \<^ML>\<open>asm_lr_simp_tac\<close> & compatibility mode: an
  assumption is only used for simplifying assumptions which are to the right
  of it \\\hline

  \end{tabular}
  \end{center}

  \<^medskip>
  In Isabelle/Pure, proof methods @{method (Pure) simp} and @{method (Pure)
  simp_all} only know about meta-equality \<open>\<equiv>\<close>. Any new object-logic needs to
  re-define these methods via \<^ML>\<open>Simplifier.method_setup\<close> in ML:
  Isabelle/FOL or Isabelle/HOL may serve as blue-prints.
\<close>


subsubsection \<open>Examples\<close>

text \<open>
  We consider basic algebraic simplifications in Isabelle/HOL. The rather
  trivial goal \<^prop>\<open>0 + (x + 0) = x + 0 + 0\<close> looks like a good candidate
  to be solved by a single call of @{method simp}:
\<close>

lemma "0 + (x + 0) = x + 0 + 0" apply simp? oops

text \<open>
  The above attempt \<^emph>\<open>fails\<close>, because \<^term>\<open>0\<close> and \<^term>\<open>(+)\<close> in the
  HOL library are declared as generic type class operations, without stating
  any algebraic laws yet. More specific types are required to get access to
  certain standard simplifications of the theory context, e.g.\ like this:\<close>

lemma fixes x :: nat shows "0 + (x + 0) = x + 0 + 0" by simp
lemma fixes x :: int shows "0 + (x + 0) = x + 0 + 0" by simp
lemma fixes x :: "'a :: monoid_add" shows "0 + (x + 0) = x + 0 + 0" by simp

text \<open>
  \<^medskip>
  In many cases, assumptions of a subgoal are also needed in the
  simplification process. For example:
\<close>

lemma fixes x :: nat shows "x = 0 \<Longrightarrow> x + x = 0" by simp
lemma fixes x :: nat assumes "x = 0" shows "x + x = 0" apply simp oops
lemma fixes x :: nat assumes "x = 0" shows "x + x = 0" using assms by simp

text \<open>
  As seen above, local assumptions that shall contribute to simplification
  need to be part of the subgoal already, or indicated explicitly for use by
  the subsequent method invocation. Both too little or too much information
  can make simplification fail, for different reasons.

  In the next example the malicious assumption \<^prop>\<open>\<And>x::nat. f x = g (f (g
  x))\<close> does not contribute to solve the problem, but makes the default
  @{method simp} method loop: the rewrite rule \<open>f ?x \<equiv> g (f (g ?x))\<close> extracted
  from the assumption does not terminate. The Simplifier notices certain
  simple forms of nontermination, but not this one. The problem can be solved
  nonetheless, by ignoring assumptions via special options as explained
  before:
\<close>

lemma "(\<And>x::nat. f x = g (f (g x))) \<Longrightarrow> f 0 = f 0 + 0"
  by (simp (no_asm))

text \<open>
  The latter form is typical for long unstructured proof scripts, where the
  control over the goal content is limited. In structured proofs it is usually
  better to avoid pushing too many facts into the goal state in the first
  place. Assumptions in the Isar proof context do not intrude the reasoning if
  not used explicitly. This is illustrated for a toplevel statement and a
  local proof body as follows:
\<close>

lemma
  assumes "\<And>x::nat. f x = g (f (g x))"
  shows "f 0 = f 0 + 0" by simp

notepad
begin
  assume "\<And>x::nat. f x = g (f (g x))"
  have "f 0 = f 0 + 0" by simp
end

text \<open>
  \<^medskip>
  Because assumptions may simplify each other, there can be very subtle cases
  of nontermination. For example, the regular @{method simp} method applied to
  \<^prop>\<open>P (f x) \<Longrightarrow> y = x \<Longrightarrow> f x = f y \<Longrightarrow> Q\<close> gives rise to the infinite
  reduction sequence
  \[
  \<open>P (f x)\<close> \stackrel{\<open>f x \<equiv> f y\<close>}{\longmapsto}
  \<open>P (f y)\<close> \stackrel{\<open>y \<equiv> x\<close>}{\longmapsto}
  \<open>P (f x)\<close> \stackrel{\<open>f x \<equiv> f y\<close>}{\longmapsto} \cdots
  \]
  whereas applying the same to \<^prop>\<open>y = x \<Longrightarrow> f x = f y \<Longrightarrow> P (f x) \<Longrightarrow> Q\<close>
  terminates (without solving the goal):
\<close>

lemma "y = x \<Longrightarrow> f x = f y \<Longrightarrow> P (f x) \<Longrightarrow> Q"
  apply simp
  oops

text \<open>
  See also \secref{sec:simp-trace} for options to enable Simplifier trace
  mode, which often helps to diagnose problems with rewrite systems.
\<close>


subsection \<open>Declaring rules \label{sec:simp-rules}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{attribute_def simp} & : & \<open>attribute\<close> \\
    @{attribute_def split} & : & \<open>attribute\<close> \\
    @{attribute_def cong} & : & \<open>attribute\<close> \\
    @{command_def "print_simpset"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@@{attribute simp} | @@{attribute cong}) (() | 'add' | 'del') |
    @@{attribute split} (() | '!' | 'del')
    ;
    @@{command print_simpset} ('!'?)
  \<close>

  \<^descr> @{attribute simp} declares rewrite rules, by adding or deleting them from
  the simpset within the theory or proof context. Rewrite rules are theorems
  expressing some form of equality, for example:

  \<open>Suc ?m + ?n = ?m + Suc ?n\<close> \\
  \<open>?P \<and> ?P \<longleftrightarrow> ?P\<close> \\
  \<open>?A \<union> ?B \<equiv> {x. x \<in> ?A \<or> x \<in> ?B}\<close>

  \<^medskip>
  Conditional rewrites such as \<open>?m < ?n \<Longrightarrow> ?m div ?n = 0\<close> are also permitted;
  the conditions can be arbitrary formulas.

  \<^medskip>
  Internally, all rewrite rules are translated into Pure equalities, theorems
  with conclusion \<open>lhs \<equiv> rhs\<close>. The simpset contains a function for extracting
  equalities from arbitrary theorems, which is usually installed when the
  object-logic is configured initially. For example, \<open>\<not> ?x \<in> {}\<close> could be
  turned into \<open>?x \<in> {} \<equiv> False\<close>. Theorems that are declared as @{attribute
  simp} and local assumptions within a goal are treated uniformly in this
  respect.

  The Simplifier accepts the following formats for the \<open>lhs\<close> term:

    \<^enum> First-order patterns, considering the sublanguage of application of
    constant operators to variable operands, without \<open>\<lambda>\<close>-abstractions or
    functional variables. For example:

    \<open>(?x + ?y) + ?z \<equiv> ?x + (?y + ?z)\<close> \\
    \<open>f (f ?x ?y) ?z \<equiv> f ?x (f ?y ?z)\<close>

    \<^enum> Higher-order patterns in the sense of @{cite "nipkow-patterns"}. These
    are terms in \<open>\<beta>\<close>-normal form (this will always be the case unless you have
    done something strange) where each occurrence of an unknown is of the form
    \<open>?F x\<^sub>1 \<dots> x\<^sub>n\<close>, where the \<open>x\<^sub>i\<close> are distinct bound variables.

    For example, \<open>(\<forall>x. ?P x \<and> ?Q x) \<equiv> (\<forall>x. ?P x) \<and> (\<forall>x. ?Q x)\<close> or its
    symmetric form, since the \<open>rhs\<close> is also a higher-order pattern.

    \<^enum> Physical first-order patterns over raw \<open>\<lambda>\<close>-term structure without
    \<open>\<alpha>\<beta>\<eta>\<close>-equality; abstractions and bound variables are treated like
    quasi-constant term material.

    For example, the rule \<open>?f ?x \<in> range ?f = True\<close> rewrites the term \<open>g a \<in>
    range g\<close> to \<open>True\<close>, but will fail to match \<open>g (h b) \<in> range (\<lambda>x. g (h
    x))\<close>. However, offending subterms (in our case \<open>?f ?x\<close>, which is not a
    pattern) can be replaced by adding new variables and conditions like this:
    \<open>?y = ?f ?x \<Longrightarrow> ?y \<in> range ?f = True\<close> is acceptable as a conditional rewrite
    rule of the second category since conditions can be arbitrary terms.

  \<^descr> @{attribute split} declares case split rules.

  \<^descr> @{attribute cong} declares congruence rules to the Simplifier context.

  Congruence rules are equalities of the form @{text [display]
  "\<dots> \<Longrightarrow> f ?x\<^sub>1 \<dots> ?x\<^sub>n = f ?y\<^sub>1 \<dots> ?y\<^sub>n"}

  This controls the simplification of the arguments of \<open>f\<close>. For example, some
  arguments can be simplified under additional assumptions:
  @{text [display]
    "?P\<^sub>1 \<longleftrightarrow> ?Q\<^sub>1 \<Longrightarrow>
    (?Q\<^sub>1 \<Longrightarrow> ?P\<^sub>2 \<longleftrightarrow> ?Q\<^sub>2) \<Longrightarrow>
    (?P\<^sub>1 \<longrightarrow> ?P\<^sub>2) \<longleftrightarrow> (?Q\<^sub>1 \<longrightarrow> ?Q\<^sub>2)"}

  Given this rule, the Simplifier assumes \<open>?Q\<^sub>1\<close> and extracts rewrite rules
  from it when simplifying \<open>?P\<^sub>2\<close>. Such local assumptions are effective for
  rewriting formulae such as \<open>x = 0 \<longrightarrow> y + x = y\<close>.

  %FIXME
  %The local assumptions are also provided as theorems to the solver;
  %see \secref{sec:simp-solver} below.

  \<^medskip>
  The following congruence rule for bounded quantifiers also supplies
  contextual information --- about the bound variable: @{text [display]
  "(?A = ?B) \<Longrightarrow>
    (\<And>x. x \<in> ?B \<Longrightarrow> ?P x \<longleftrightarrow> ?Q x) \<Longrightarrow>
    (\<forall>x \<in> ?A. ?P x) \<longleftrightarrow> (\<forall>x \<in> ?B. ?Q x)"}

  \<^medskip>
  This congruence rule for conditional expressions can supply contextual
  information for simplifying the arms: @{text [display]
  "?p = ?q \<Longrightarrow>
    (?q \<Longrightarrow> ?a = ?c) \<Longrightarrow>
    (\<not> ?q \<Longrightarrow> ?b = ?d) \<Longrightarrow>
    (if ?p then ?a else ?b) = (if ?q then ?c else ?d)"}

  A congruence rule can also \<^emph>\<open>prevent\<close> simplification of some arguments. Here
  is an alternative congruence rule for conditional expressions that conforms
  to non-strict functional evaluation: @{text [display]
  "?p = ?q \<Longrightarrow>
    (if ?p then ?a else ?b) = (if ?q then ?a else ?b)"}

  Only the first argument is simplified; the others remain unchanged. This can
  make simplification much faster, but may require an extra case split over
  the condition \<open>?q\<close> to prove the goal.

  \<^descr> @{command "print_simpset"} prints the collection of rules declared to the
  Simplifier, which is also known as ``simpset'' internally; the ``\<open>!\<close>''
  option indicates extra verbosity.

  The implicit simpset of the theory context is propagated monotonically
  through the theory hierarchy: forming a new theory, the union of the
  simpsets of its imports are taken as starting point. Also note that
  definitional packages like @{command "datatype"}, @{command "primrec"},
  @{command "fun"} routinely declare Simplifier rules to the target context,
  while plain @{command "definition"} is an exception in \<^emph>\<open>not\<close> declaring
  anything.

  \<^medskip>
  It is up the user to manipulate the current simpset further by explicitly
  adding or deleting theorems as simplification rules, or installing other
  tools via simplification procedures (\secref{sec:simproc}). Good simpsets
  are hard to design. Rules that obviously simplify, like \<open>?n + 0 \<equiv> ?n\<close> are
  good candidates for the implicit simpset, unless a special non-normalizing
  behavior of certain operations is intended. More specific rules (such as
  distributive laws, which duplicate subterms) should be added only for
  specific proof steps. Conversely, sometimes a rule needs to be deleted just
  for some part of a proof. The need of frequent additions or deletions may
  indicate a poorly designed simpset.

  \begin{warn}
  The union of simpsets from theory imports (as described above) is not always
  a good starting point for the new theory. If some ancestors have deleted
  simplification rules because they are no longer wanted, while others have
  left those rules in, then the union will contain the unwanted rules, and
  thus have to be deleted again in the theory body.
  \end{warn}
\<close>


subsection \<open>Ordered rewriting with permutative rules\<close>

text \<open>
  A rewrite rule is \<^emph>\<open>permutative\<close> if the left-hand side and right-hand side
  are the equal up to renaming of variables. The most common permutative rule
  is commutativity: \<open>?x + ?y = ?y + ?x\<close>. Other examples include \<open>(?x - ?y) -
  ?z = (?x - ?z) - ?y\<close> in arithmetic and \<open>insert ?x (insert ?y ?A) = insert ?y
  (insert ?x ?A)\<close> for sets. Such rules are common enough to merit special
  attention.

  Because ordinary rewriting loops given such rules, the Simplifier employs a
  special strategy, called \<^emph>\<open>ordered rewriting\<close>. Permutative rules are
  detected and only applied if the rewriting step decreases the redex wrt.\ a
  given term ordering. For example, commutativity rewrites \<open>b + a\<close> to \<open>a + b\<close>,
  but then stops, because the redex cannot be decreased further in the sense
  of the term ordering.

  The default is lexicographic ordering of term structure, but this could be
  also changed locally for special applications via @{define_ML
  Simplifier.set_term_ord} in Isabelle/ML.

  \<^medskip>
  Permutative rewrite rules are declared to the Simplifier just like other
  rewrite rules. Their special status is recognized automatically, and their
  application is guarded by the term ordering accordingly.
\<close>


subsubsection \<open>Rewriting with AC operators\<close>

text \<open>
  Ordered rewriting is particularly effective in the case of
  associative-commutative operators. (Associativity by itself is not
  permutative.) When dealing with an AC-operator \<open>f\<close>, keep the following
  points in mind:

    \<^item> The associative law must always be oriented from left to right, namely
    \<open>f (f x y) z = f x (f y z)\<close>. The opposite orientation, if used with
    commutativity, leads to looping in conjunction with the standard term
    order.

    \<^item> To complete your set of rewrite rules, you must add not just
    associativity (A) and commutativity (C) but also a derived rule
    \<^emph>\<open>left-commutativity\<close> (LC): \<open>f x (f y z) = f y (f x z)\<close>.

  Ordered rewriting with the combination of A, C, and LC sorts a term
  lexicographically --- the rewriting engine imitates bubble-sort.
\<close>

experiment
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infix "\<bullet>" 60)
  assumes assoc: "(x \<bullet> y) \<bullet> z = x \<bullet> (y \<bullet> z)"
  assumes commute: "x \<bullet> y = y \<bullet> x"
begin

lemma left_commute: "x \<bullet> (y \<bullet> z) = y \<bullet> (x \<bullet> z)"
proof -
  have "(x \<bullet> y) \<bullet> z = (y \<bullet> x) \<bullet> z" by (simp only: commute)
  then show ?thesis by (simp only: assoc)
qed

lemmas AC_rules = assoc commute left_commute

text \<open>
  Thus the Simplifier is able to establish equalities with arbitrary
  permutations of subterms, by normalizing to a common standard form. For
  example:
\<close>

lemma "(b \<bullet> c) \<bullet> a = xxx"
  apply (simp only: AC_rules)
  txt \<open>\<^subgoals>\<close>
  oops

lemma "(b \<bullet> c) \<bullet> a = a \<bullet> (b \<bullet> c)" by (simp only: AC_rules)
lemma "(b \<bullet> c) \<bullet> a = c \<bullet> (b \<bullet> a)" by (simp only: AC_rules)
lemma "(b \<bullet> c) \<bullet> a = (c \<bullet> b) \<bullet> a" by (simp only: AC_rules)

end

text \<open>
  Martin and Nipkow @{cite "martin-nipkow"} discuss the theory and give many
  examples; other algebraic structures are amenable to ordered rewriting, such
  as Boolean rings. The Boyer-Moore theorem prover @{cite bm88book} also
  employs ordered rewriting.
\<close>


subsubsection \<open>Re-orienting equalities\<close>

text \<open>Another application of ordered rewriting uses the derived rule
  @{thm [source] eq_commute}: @{thm [source = false] eq_commute} to
  reverse equations.

  This is occasionally useful to re-orient local assumptions according
  to the term ordering, when other built-in mechanisms of
  reorientation and mutual simplification fail to apply.\<close>


subsection \<open>Simplifier tracing and debugging \label{sec:simp-trace}\<close>

text \<open>
  \begin{tabular}{rcll}
    @{attribute_def simp_trace} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def simp_trace_depth_limit} & : & \<open>attribute\<close> & default \<open>1\<close> \\
    @{attribute_def simp_debug} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def simp_trace_new} & : & \<open>attribute\<close> \\
    @{attribute_def simp_break} & : & \<open>attribute\<close> \\
  \end{tabular}
  \<^medskip>

  \<^rail>\<open>
    @@{attribute simp_trace_new} ('interactive')? \<newline>
      ('mode' '=' ('full' | 'normal'))? \<newline>
      ('depth' '=' @{syntax nat})?
    ;

    @@{attribute simp_break} (@{syntax term}*)
  \<close>

  These attributes and configurations options control various aspects of
  Simplifier tracing and debugging.

  \<^descr> @{attribute simp_trace} makes the Simplifier output internal operations.
  This includes rewrite steps, but also bookkeeping like modifications of the
  simpset.

  \<^descr> @{attribute simp_trace_depth_limit} limits the effect of @{attribute
  simp_trace} to the given depth of recursive Simplifier invocations (when
  solving conditions of rewrite rules).

  \<^descr> @{attribute simp_debug} makes the Simplifier output some extra information
  about internal operations. This includes any attempted invocation of
  simplification procedures.

  \<^descr> @{attribute simp_trace_new} controls Simplifier tracing within
  Isabelle/PIDE applications, notably Isabelle/jEdit @{cite "isabelle-jedit"}.
  This provides a hierarchical representation of the rewriting steps performed
  by the Simplifier.

  Users can configure the behaviour by specifying breakpoints, verbosity and
  enabling or disabling the interactive mode. In normal verbosity (the
  default), only rule applications matching a breakpoint will be shown to the
  user. In full verbosity, all rule applications will be logged. Interactive
  mode interrupts the normal flow of the Simplifier and defers the decision
  how to continue to the user via some GUI dialog.

  \<^descr> @{attribute simp_break} declares term or theorem breakpoints for
  @{attribute simp_trace_new} as described above. Term breakpoints are
  patterns which are checked for matches on the redex of a rule application.
  Theorem breakpoints trigger when the corresponding theorem is applied in a
  rewrite step. For example:
\<close>

(*<*)experiment begin(*>*)
declare conjI [simp_break]
declare [[simp_break "?x \<and> ?y"]]
(*<*)end(*>*)


subsection \<open>Simplification procedures \label{sec:simproc}\<close>

text \<open>
  Simplification procedures are ML functions that produce proven rewrite rules
  on demand. They are associated with higher-order patterns that approximate
  the left-hand sides of equations. The Simplifier first matches the current
  redex against one of the LHS patterns; if this succeeds, the corresponding
  ML function is invoked, passing the Simplifier context and redex term. Thus
  rules may be specifically fashioned for particular situations, resulting in
  a more powerful mechanism than term rewriting by a fixed set of rules.

  Any successful result needs to be a (possibly conditional) rewrite rule \<open>t \<equiv>
  u\<close> that is applicable to the current redex. The rule will be applied just as
  any ordinary rewrite rule. It is expected to be already in \<^emph>\<open>internal form\<close>,
  bypassing the automatic preprocessing of object-level equivalences.

  \begin{matharray}{rcl}
    @{command_def "simproc_setup"} & : & \<open>local_theory \<rightarrow> local_theory\<close> \\
    simproc & : & \<open>attribute\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{command simproc_setup} @{syntax name} '(' (@{syntax term} + '|') ')' '='
      @{syntax text};

    @@{attribute simproc} (('add' ':')? | 'del' ':') (@{syntax name}+)
  \<close>

  \<^descr> @{command "simproc_setup"} defines a named simplification procedure that
  is invoked by the Simplifier whenever any of the given term patterns match
  the current redex. The implementation, which is provided as ML source text,
  needs to be of type
  \<^ML_type>\<open>morphism -> Proof.context -> cterm -> thm option\<close>, where the
  \<^ML_type>\<open>cterm\<close> represents the current redex \<open>r\<close> and the result is supposed
  to be some proven rewrite rule \<open>r \<equiv> r'\<close> (or a generalized version), or \<^ML>\<open>NONE\<close> to indicate failure. The \<^ML_type>\<open>Proof.context\<close> argument holds the
  full context of the current Simplifier invocation. The \<^ML_type>\<open>morphism\<close>
  informs about the difference of the original compilation context wrt.\ the
  one of the actual application later on.

  Morphisms are only relevant for simprocs that are defined within a local
  target context, e.g.\ in a locale.

  \<^descr> \<open>simproc add: name\<close> and \<open>simproc del: name\<close> add or delete named simprocs
  to the current Simplifier context. The default is to add a simproc. Note
  that @{command "simproc_setup"} already adds the new simproc to the
  subsequent context.
\<close>


subsubsection \<open>Example\<close>

text \<open>
  The following simplification procedure for @{thm [source = false,
  show_types] unit_eq} in HOL performs fine-grained control over rule
  application, beyond higher-order pattern matching. Declaring @{thm unit_eq}
  as @{attribute simp} directly would make the Simplifier loop! Note that a
  version of this simplification procedure is already active in Isabelle/HOL.
\<close>

(*<*)experiment begin(*>*)
simproc_setup unit ("x::unit") =
  \<open>fn _ => fn _ => fn ct =>
    if HOLogic.is_unit (Thm.term_of ct) then NONE
    else SOME (mk_meta_eq @{thm unit_eq})\<close>
(*<*)end(*>*)

text \<open>
  Since the Simplifier applies simplification procedures frequently, it is
  important to make the failure check in ML reasonably fast.\<close>


subsection \<open>Configurable Simplifier strategies \label{sec:simp-strategies}\<close>

text \<open>
  The core term-rewriting engine of the Simplifier is normally used in
  combination with some add-on components that modify the strategy and allow
  to integrate other non-Simplifier proof tools. These may be reconfigured in
  ML as explained below. Even if the default strategies of object-logics like
  Isabelle/HOL are used unchanged, it helps to understand how the standard
  Simplifier strategies work.\<close>


subsubsection \<open>The subgoaler\<close>

text \<open>
  \begin{mldecls}
  @{define_ML Simplifier.set_subgoaler: "(Proof.context -> int -> tactic) ->
  Proof.context -> Proof.context"} \\
  @{define_ML Simplifier.prems_of: "Proof.context -> thm list"} \\
  \end{mldecls}

  The subgoaler is the tactic used to solve subgoals arising out of
  conditional rewrite rules or congruence rules. The default should be
  simplification itself. In rare situations, this strategy may need to be
  changed. For example, if the premise of a conditional rule is an instance of
  its conclusion, as in \<open>Suc ?m < ?n \<Longrightarrow> ?m < ?n\<close>, the default strategy could
  loop. % FIXME !??

    \<^descr> \<^ML>\<open>Simplifier.set_subgoaler\<close>~\<open>tac ctxt\<close> sets the subgoaler of the
    context to \<open>tac\<close>. The tactic will be applied to the context of the running
    Simplifier instance.

    \<^descr> \<^ML>\<open>Simplifier.prems_of\<close>~\<open>ctxt\<close> retrieves the current set of premises
    from the context. This may be non-empty only if the Simplifier has been
    told to utilize local assumptions in the first place (cf.\ the options in
    \secref{sec:simp-meth}).

  As an example, consider the following alternative subgoaler:
\<close>

ML_val \<open>
  fun subgoaler_tac ctxt =
    assume_tac ctxt ORELSE'
    resolve_tac ctxt (Simplifier.prems_of ctxt) ORELSE'
    asm_simp_tac ctxt
\<close>

text \<open>
  This tactic first tries to solve the subgoal by assumption or by resolving
  with with one of the premises, calling simplification only if that fails.\<close>


subsubsection \<open>The solver\<close>

text \<open>
  \begin{mldecls}
  @{define_ML_type solver} \\
  @{define_ML Simplifier.mk_solver: "string ->
  (Proof.context -> int -> tactic) -> solver"} \\
  @{define_ML_infix setSolver: "Proof.context * solver -> Proof.context"} \\
  @{define_ML_infix addSolver: "Proof.context * solver -> Proof.context"} \\
  @{define_ML_infix setSSolver: "Proof.context * solver -> Proof.context"} \\
  @{define_ML_infix addSSolver: "Proof.context * solver -> Proof.context"} \\
  \end{mldecls}

  A solver is a tactic that attempts to solve a subgoal after simplification.
  Its core functionality is to prove trivial subgoals such as \<^prop>\<open>True\<close>
  and \<open>t = t\<close>, but object-logics might be more ambitious. For example,
  Isabelle/HOL performs a restricted version of linear arithmetic here.

  Solvers are packaged up in abstract type \<^ML_type>\<open>solver\<close>, with \<^ML>\<open>Simplifier.mk_solver\<close> as the only operation to create a solver.

  \<^medskip>
  Rewriting does not instantiate unknowns. For example, rewriting alone cannot
  prove \<open>a \<in> ?A\<close> since this requires instantiating \<open>?A\<close>. The solver, however,
  is an arbitrary tactic and may instantiate unknowns as it pleases. This is
  the only way the Simplifier can handle a conditional rewrite rule whose
  condition contains extra variables. When a simplification tactic is to be
  combined with other provers, especially with the Classical Reasoner, it is
  important whether it can be considered safe or not. For this reason a
  simpset contains two solvers: safe and unsafe.

  The standard simplification strategy solely uses the unsafe solver, which is
  appropriate in most cases. For special applications where the simplification
  process is not allowed to instantiate unknowns within the goal,
  simplification starts with the safe solver, but may still apply the ordinary
  unsafe one in nested simplifications for conditional rules or congruences.
  Note that in this way the overall tactic is not totally safe: it may
  instantiate unknowns that appear also in other subgoals.

  \<^descr> \<^ML>\<open>Simplifier.mk_solver\<close>~\<open>name tac\<close> turns \<open>tac\<close> into a solver; the
  \<open>name\<close> is only attached as a comment and has no further significance.

  \<^descr> \<open>ctxt setSSolver solver\<close> installs \<open>solver\<close> as the safe solver of \<open>ctxt\<close>.

  \<^descr> \<open>ctxt addSSolver solver\<close> adds \<open>solver\<close> as an additional safe solver; it
  will be tried after the solvers which had already been present in \<open>ctxt\<close>.

  \<^descr> \<open>ctxt setSolver solver\<close> installs \<open>solver\<close> as the unsafe solver of \<open>ctxt\<close>.

  \<^descr> \<open>ctxt addSolver solver\<close> adds \<open>solver\<close> as an additional unsafe solver; it
  will be tried after the solvers which had already been present in \<open>ctxt\<close>.


  \<^medskip>
  The solver tactic is invoked with the context of the running Simplifier.
  Further operations may be used to retrieve relevant information, such as the
  list of local Simplifier premises via \<^ML>\<open>Simplifier.prems_of\<close> --- this
  list may be non-empty only if the Simplifier runs in a mode that utilizes
  local assumptions (see also \secref{sec:simp-meth}). The solver is also
  presented the full goal including its assumptions in any case. Thus it can
  use these (e.g.\ by calling \<^ML>\<open>assume_tac\<close>), even if the Simplifier proper
  happens to ignore local premises at the moment.

  \<^medskip>
  As explained before, the subgoaler is also used to solve the premises of
  congruence rules. These are usually of the form \<open>s = ?x\<close>, where \<open>s\<close> needs to
  be simplified and \<open>?x\<close> needs to be instantiated with the result. Typically,
  the subgoaler will invoke the Simplifier at some point, which will
  eventually call the solver. For this reason, solver tactics must be prepared
  to solve goals of the form \<open>t = ?x\<close>, usually by reflexivity. In particular,
  reflexivity should be tried before any of the fancy automated proof tools.

  It may even happen that due to simplification the subgoal is no longer an
  equality. For example, \<open>False \<longleftrightarrow> ?Q\<close> could be rewritten to \<open>\<not> ?Q\<close>. To cover
  this case, the solver could try resolving with the theorem \<open>\<not> False\<close> of the
  object-logic.

  \<^medskip>
  \begin{warn}
  If a premise of a congruence rule cannot be proved, then the congruence is
  ignored. This should only happen if the rule is \<^emph>\<open>conditional\<close> --- that is,
  contains premises not of the form \<open>t = ?x\<close>. Otherwise it indicates that some
  congruence rule, or possibly the subgoaler or solver, is faulty.
  \end{warn}
\<close>


subsubsection \<open>The looper\<close>

text \<open>
  \begin{mldecls}
  @{define_ML_infix setloop: "Proof.context *
  (Proof.context -> int -> tactic) -> Proof.context"} \\
  @{define_ML_infix addloop: "Proof.context *
  (string * (Proof.context -> int -> tactic))
  -> Proof.context"} \\
  @{define_ML_infix delloop: "Proof.context * string -> Proof.context"} \\
  @{define_ML Splitter.add_split: "thm -> Proof.context -> Proof.context"} \\
  @{define_ML Splitter.add_split: "thm -> Proof.context -> Proof.context"} \\
  @{define_ML Splitter.add_split_bang: "
  thm -> Proof.context -> Proof.context"} \\
  @{define_ML Splitter.del_split: "thm -> Proof.context -> Proof.context"} \\
  \end{mldecls}

  The looper is a list of tactics that are applied after simplification, in
  case the solver failed to solve the simplified goal. If the looper succeeds,
  the simplification process is started all over again. Each of the subgoals
  generated by the looper is attacked in turn, in reverse order.

  A typical looper is \<^emph>\<open>case splitting\<close>: the expansion of a conditional.
  Another possibility is to apply an elimination rule on the assumptions. More
  adventurous loopers could start an induction.

    \<^descr> \<open>ctxt setloop tac\<close> installs \<open>tac\<close> as the only looper tactic of \<open>ctxt\<close>.

    \<^descr> \<open>ctxt addloop (name, tac)\<close> adds \<open>tac\<close> as an additional looper tactic
    with name \<open>name\<close>, which is significant for managing the collection of
    loopers. The tactic will be tried after the looper tactics that had
    already been present in \<open>ctxt\<close>.

    \<^descr> \<open>ctxt delloop name\<close> deletes the looper tactic that was associated with
    \<open>name\<close> from \<open>ctxt\<close>.

    \<^descr> \<^ML>\<open>Splitter.add_split\<close>~\<open>thm ctxt\<close> adds split tactic
    for \<open>thm\<close> as additional looper tactic of \<open>ctxt\<close>
    (overwriting previous split tactic for the same constant).

    \<^descr> \<^ML>\<open>Splitter.add_split_bang\<close>~\<open>thm ctxt\<close> adds aggressive
    (see \S\ref{sec:simp-meth})
    split tactic for \<open>thm\<close> as additional looper tactic of \<open>ctxt\<close>
    (overwriting previous split tactic for the same constant).

    \<^descr> \<^ML>\<open>Splitter.del_split\<close>~\<open>thm ctxt\<close> deletes the split tactic
    corresponding to \<open>thm\<close> from the looper tactics of \<open>ctxt\<close>.

  The splitter replaces applications of a given function; the right-hand side
  of the replacement can be anything. For example, here is a splitting rule
  for conditional expressions:

  @{text [display] "?P (if ?Q ?x ?y) \<longleftrightarrow> (?Q \<longrightarrow> ?P ?x) \<and> (\<not> ?Q \<longrightarrow> ?P ?y)"}

  Another example is the elimination operator for Cartesian products (which
  happens to be called \<^const>\<open>case_prod\<close> in Isabelle/HOL:

  @{text [display] "?P (case_prod ?f ?p) \<longleftrightarrow> (\<forall>a b. ?p = (a, b) \<longrightarrow> ?P (f a b))"}

  For technical reasons, there is a distinction between case splitting in the
  conclusion and in the premises of a subgoal. The former is done by \<^ML>\<open>Splitter.split_tac\<close> with rules like @{thm [source] if_split} or @{thm
  [source] option.split}, which do not split the subgoal, while the latter is
  done by \<^ML>\<open>Splitter.split_asm_tac\<close> with rules like @{thm [source]
  if_split_asm} or @{thm [source] option.split_asm}, which split the subgoal.
  The function \<^ML>\<open>Splitter.add_split\<close> automatically takes care of which
  tactic to call, analyzing the form of the rules given as argument; it is the
  same operation behind \<open>split\<close> attribute or method modifier syntax in the
  Isar source language.

  Case splits should be allowed only when necessary; they are expensive and
  hard to control. Case-splitting on if-expressions in the conclusion is
  usually beneficial, so it is enabled by default in Isabelle/HOL and
  Isabelle/FOL/ZF.

  \begin{warn}
  With \<^ML>\<open>Splitter.split_asm_tac\<close> as looper component, the Simplifier may
  split subgoals! This might cause unexpected problems in tactic expressions
  that silently assume 0 or 1 subgoals after simplification.
  \end{warn}
\<close>


subsection \<open>Forward simplification \label{sec:simp-forward}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{attribute_def simplified} & : & \<open>attribute\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{attribute simplified} opt? @{syntax thms}?
    ;

    opt: '(' ('no_asm' | 'no_asm_simp' | 'no_asm_use') ')'
  \<close>

  \<^descr> @{attribute simplified}~\<open>a\<^sub>1 \<dots> a\<^sub>n\<close> causes a theorem to be simplified,
  either by exactly the specified rules \<open>a\<^sub>1, \<dots>, a\<^sub>n\<close>, or the implicit
  Simplifier context if no arguments are given. The result is fully simplified
  by default, including assumptions and conclusion; the options \<open>no_asm\<close> etc.\
  tune the Simplifier in the same way as the for the \<open>simp\<close> method.

  Note that forward simplification restricts the Simplifier to its most basic
  operation of term rewriting; solver and looper tactics
  (\secref{sec:simp-strategies}) are \<^emph>\<open>not\<close> involved here. The @{attribute
  simplified} attribute should be only rarely required under normal
  circumstances.
\<close>


section \<open>The Classical Reasoner \label{sec:classical}\<close>

subsection \<open>Basic concepts\<close>

text \<open>Although Isabelle is generic, many users will be working in
  some extension of classical first-order logic.  Isabelle/ZF is built
  upon theory FOL, while Isabelle/HOL conceptually contains
  first-order logic as a fragment.  Theorem-proving in predicate logic
  is undecidable, but many automated strategies have been developed to
  assist in this task.

  Isabelle's classical reasoner is a generic package that accepts
  certain information about a logic and delivers a suite of automatic
  proof tools, based on rules that are classified and declared in the
  context.  These proof procedures are slow and simplistic compared
  with high-end automated theorem provers, but they can save
  considerable time and effort in practice.  They can prove theorems
  such as Pelletier's @{cite pelletier86} problems 40 and 41 in a few
  milliseconds (including full proof reconstruction):\<close>

lemma "(\<exists>y. \<forall>x. F x y \<longleftrightarrow> F x x) \<longrightarrow> \<not> (\<forall>x. \<exists>y. \<forall>z. F z y \<longleftrightarrow> \<not> F z x)"
  by blast

lemma "(\<forall>z. \<exists>y. \<forall>x. f x y \<longleftrightarrow> f x z \<and> \<not> f x x) \<longrightarrow> \<not> (\<exists>z. \<forall>x. f x z)"
  by blast

text \<open>The proof tools are generic.  They are not restricted to
  first-order logic, and have been heavily used in the development of
  the Isabelle/HOL library and applications.  The tactics can be
  traced, and their components can be called directly; in this manner,
  any proof can be viewed interactively.\<close>


subsubsection \<open>The sequent calculus\<close>

text \<open>Isabelle supports natural deduction, which is easy to use for
  interactive proof.  But natural deduction does not easily lend
  itself to automation, and has a bias towards intuitionism.  For
  certain proofs in classical logic, it can not be called natural.
  The \<^emph>\<open>sequent calculus\<close>, a generalization of natural deduction,
  is easier to automate.

  A \<^bold>\<open>sequent\<close> has the form \<open>\<Gamma> \<turnstile> \<Delta>\<close>, where \<open>\<Gamma>\<close>
  and \<open>\<Delta>\<close> are sets of formulae.\<^footnote>\<open>For first-order
  logic, sequents can equivalently be made from lists or multisets of
  formulae.\<close> The sequent \<open>P\<^sub>1, \<dots>, P\<^sub>m \<turnstile> Q\<^sub>1, \<dots>, Q\<^sub>n\<close> is
  \<^bold>\<open>valid\<close> if \<open>P\<^sub>1 \<and> \<dots> \<and> P\<^sub>m\<close> implies \<open>Q\<^sub>1 \<or> \<dots> \<or>
  Q\<^sub>n\<close>.  Thus \<open>P\<^sub>1, \<dots>, P\<^sub>m\<close> represent assumptions, each of which
  is true, while \<open>Q\<^sub>1, \<dots>, Q\<^sub>n\<close> represent alternative goals.  A
  sequent is \<^bold>\<open>basic\<close> if its left and right sides have a common
  formula, as in \<open>P, Q \<turnstile> Q, R\<close>; basic sequents are trivially
  valid.

  Sequent rules are classified as \<^bold>\<open>right\<close> or \<^bold>\<open>left\<close>,
  indicating which side of the \<open>\<turnstile>\<close> symbol they operate on.
  Rules that operate on the right side are analogous to natural
  deduction's introduction rules, and left rules are analogous to
  elimination rules.  The sequent calculus analogue of \<open>(\<longrightarrow>I)\<close>
  is the rule
  \[
  \infer[\<open>(\<longrightarrow>R)\<close>]{\<open>\<Gamma> \<turnstile> \<Delta>, P \<longrightarrow> Q\<close>}{\<open>P, \<Gamma> \<turnstile> \<Delta>, Q\<close>}
  \]
  Applying the rule backwards, this breaks down some implication on
  the right side of a sequent; \<open>\<Gamma>\<close> and \<open>\<Delta>\<close> stand for
  the sets of formulae that are unaffected by the inference.  The
  analogue of the pair \<open>(\<or>I1)\<close> and \<open>(\<or>I2)\<close> is the
  single rule
  \[
  \infer[\<open>(\<or>R)\<close>]{\<open>\<Gamma> \<turnstile> \<Delta>, P \<or> Q\<close>}{\<open>\<Gamma> \<turnstile> \<Delta>, P, Q\<close>}
  \]
  This breaks down some disjunction on the right side, replacing it by
  both disjuncts.  Thus, the sequent calculus is a kind of
  multiple-conclusion logic.

  To illustrate the use of multiple formulae on the right, let us
  prove the classical theorem \<open>(P \<longrightarrow> Q) \<or> (Q \<longrightarrow> P)\<close>.  Working
  backwards, we reduce this formula to a basic sequent:
  \[
  \infer[\<open>(\<or>R)\<close>]{\<open>\<turnstile> (P \<longrightarrow> Q) \<or> (Q \<longrightarrow> P)\<close>}
    {\infer[\<open>(\<longrightarrow>R)\<close>]{\<open>\<turnstile> (P \<longrightarrow> Q), (Q \<longrightarrow> P)\<close>}
      {\infer[\<open>(\<longrightarrow>R)\<close>]{\<open>P \<turnstile> Q, (Q \<longrightarrow> P)\<close>}
        {\<open>P, Q \<turnstile> Q, P\<close>}}}
  \]

  This example is typical of the sequent calculus: start with the
  desired theorem and apply rules backwards in a fairly arbitrary
  manner.  This yields a surprisingly effective proof procedure.
  Quantifiers add only few complications, since Isabelle handles
  parameters and schematic variables.  See @{cite \<open>Chapter 10\<close>
  "paulson-ml2"} for further discussion.\<close>


subsubsection \<open>Simulating sequents by natural deduction\<close>

text \<open>Isabelle can represent sequents directly, as in the
  object-logic LK.  But natural deduction is easier to work with, and
  most object-logics employ it.  Fortunately, we can simulate the
  sequent \<open>P\<^sub>1, \<dots>, P\<^sub>m \<turnstile> Q\<^sub>1, \<dots>, Q\<^sub>n\<close> by the Isabelle formula
  \<open>P\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> P\<^sub>m \<Longrightarrow> \<not> Q\<^sub>2 \<Longrightarrow> ... \<Longrightarrow> \<not> Q\<^sub>n \<Longrightarrow> Q\<^sub>1\<close> where the order of
  the assumptions and the choice of \<open>Q\<^sub>1\<close> are arbitrary.
  Elim-resolution plays a key role in simulating sequent proofs.

  We can easily handle reasoning on the left.  Elim-resolution with
  the rules \<open>(\<or>E)\<close>, \<open>(\<bottom>E)\<close> and \<open>(\<exists>E)\<close> achieves
  a similar effect as the corresponding sequent rules.  For the other
  connectives, we use sequent-style elimination rules instead of
  destruction rules such as \<open>(\<and>E1, 2)\<close> and \<open>(\<forall>E)\<close>.
  But note that the rule \<open>(\<not>L)\<close> has no effect under our
  representation of sequents!
  \[
  \infer[\<open>(\<not>L)\<close>]{\<open>\<not> P, \<Gamma> \<turnstile> \<Delta>\<close>}{\<open>\<Gamma> \<turnstile> \<Delta>, P\<close>}
  \]

  What about reasoning on the right?  Introduction rules can only
  affect the formula in the conclusion, namely \<open>Q\<^sub>1\<close>.  The
  other right-side formulae are represented as negated assumptions,
  \<open>\<not> Q\<^sub>2, \<dots>, \<not> Q\<^sub>n\<close>.  In order to operate on one of these, it
  must first be exchanged with \<open>Q\<^sub>1\<close>.  Elim-resolution with the
  \<open>swap\<close> rule has this effect: \<open>\<not> P \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> R\<close>

  To ensure that swaps occur only when necessary, each introduction
  rule is converted into a swapped form: it is resolved with the
  second premise of \<open>(swap)\<close>.  The swapped form of \<open>(\<and>I)\<close>, which might be called \<open>(\<not>\<and>E)\<close>, is
  @{text [display] "\<not> (P \<and> Q) \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> (\<not> R \<Longrightarrow> Q) \<Longrightarrow> R"}

  Similarly, the swapped form of \<open>(\<longrightarrow>I)\<close> is
  @{text [display] "\<not> (P \<longrightarrow> Q) \<Longrightarrow> (\<not> R \<Longrightarrow> P \<Longrightarrow> Q) \<Longrightarrow> R"}

  Swapped introduction rules are applied using elim-resolution, which
  deletes the negated formula.  Our representation of sequents also
  requires the use of ordinary introduction rules.  If we had no
  regard for readability of intermediate goal states, we could treat
  the right side more uniformly by representing sequents as @{text
  [display] "P\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> P\<^sub>m \<Longrightarrow> \<not> Q\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> \<not> Q\<^sub>n \<Longrightarrow> \<bottom>"}
\<close>


subsubsection \<open>Extra rules for the sequent calculus\<close>

text \<open>As mentioned, destruction rules such as \<open>(\<and>E1, 2)\<close> and
  \<open>(\<forall>E)\<close> must be replaced by sequent-style elimination rules.
  In addition, we need rules to embody the classical equivalence
  between \<open>P \<longrightarrow> Q\<close> and \<open>\<not> P \<or> Q\<close>.  The introduction
  rules \<open>(\<or>I1, 2)\<close> are replaced by a rule that simulates
  \<open>(\<or>R)\<close>: @{text [display] "(\<not> Q \<Longrightarrow> P) \<Longrightarrow> P \<or> Q"}

  The destruction rule \<open>(\<longrightarrow>E)\<close> is replaced by @{text [display]
  "(P \<longrightarrow> Q) \<Longrightarrow> (\<not> P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R"}

  Quantifier replication also requires special rules.  In classical
  logic, \<open>\<exists>x. P x\<close> is equivalent to \<open>\<not> (\<forall>x. \<not> P x)\<close>;
  the rules \<open>(\<exists>R)\<close> and \<open>(\<forall>L)\<close> are dual:
  \[
  \infer[\<open>(\<exists>R)\<close>]{\<open>\<Gamma> \<turnstile> \<Delta>, \<exists>x. P x\<close>}{\<open>\<Gamma> \<turnstile> \<Delta>, \<exists>x. P x, P t\<close>}
  \qquad
  \infer[\<open>(\<forall>L)\<close>]{\<open>\<forall>x. P x, \<Gamma> \<turnstile> \<Delta>\<close>}{\<open>P t, \<forall>x. P x, \<Gamma> \<turnstile> \<Delta>\<close>}
  \]
  Thus both kinds of quantifier may be replicated.  Theorems requiring
  multiple uses of a universal formula are easy to invent; consider
  @{text [display] "(\<forall>x. P x \<longrightarrow> P (f x)) \<and> P a \<longrightarrow> P (f\<^sup>n a)"} for any
  \<open>n > 1\<close>.  Natural examples of the multiple use of an
  existential formula are rare; a standard one is \<open>\<exists>x. \<forall>y. P x
  \<longrightarrow> P y\<close>.

  Forgoing quantifier replication loses completeness, but gains
  decidability, since the search space becomes finite.  Many useful
  theorems can be proved without replication, and the search generally
  delivers its verdict in a reasonable time.  To adopt this approach,
  represent the sequent rules \<open>(\<exists>R)\<close>, \<open>(\<exists>L)\<close> and
  \<open>(\<forall>R)\<close> by \<open>(\<exists>I)\<close>, \<open>(\<exists>E)\<close> and \<open>(\<forall>I)\<close>,
  respectively, and put \<open>(\<forall>E)\<close> into elimination form: @{text
  [display] "\<forall>x. P x \<Longrightarrow> (P t \<Longrightarrow> Q) \<Longrightarrow> Q"}

  Elim-resolution with this rule will delete the universal formula
  after a single use.  To replicate universal quantifiers, replace the
  rule by @{text [display] "\<forall>x. P x \<Longrightarrow> (P t \<Longrightarrow> \<forall>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q"}

  To replicate existential quantifiers, replace \<open>(\<exists>I)\<close> by
  @{text [display] "(\<not> (\<exists>x. P x) \<Longrightarrow> P t) \<Longrightarrow> \<exists>x. P x"}

  All introduction rules mentioned above are also useful in swapped
  form.

  Replication makes the search space infinite; we must apply the rules
  with care.  The classical reasoner distinguishes between safe and
  unsafe rules, applying the latter only when there is no alternative.
  Depth-first search may well go down a blind alley; best-first search
  is better behaved in an infinite search space.  However, quantifier
  replication is too expensive to prove any but the simplest theorems.
\<close>


subsection \<open>Rule declarations\<close>

text \<open>The proof tools of the Classical Reasoner depend on
  collections of rules declared in the context, which are classified
  as introduction, elimination or destruction and as \<^emph>\<open>safe\<close> or
  \<^emph>\<open>unsafe\<close>.  In general, safe rules can be attempted blindly,
  while unsafe rules must be used with care.  A safe rule must never
  reduce a provable goal to an unprovable set of subgoals.

  The rule \<open>P \<Longrightarrow> P \<or> Q\<close> is unsafe because it reduces \<open>P
  \<or> Q\<close> to \<open>P\<close>, which might turn out as premature choice of an
  unprovable subgoal.  Any rule whose premises contain new unknowns is
  unsafe. The elimination rule \<open>\<forall>x. P x \<Longrightarrow> (P t \<Longrightarrow> Q) \<Longrightarrow> Q\<close> is
  unsafe, since it is applied via elim-resolution, which discards the
  assumption \<open>\<forall>x. P x\<close> and replaces it by the weaker
  assumption \<open>P t\<close>.  The rule \<open>P t \<Longrightarrow> \<exists>x. P x\<close> is
  unsafe for similar reasons.  The quantifier duplication rule \<open>\<forall>x. P x \<Longrightarrow> (P t \<Longrightarrow> \<forall>x. P x \<Longrightarrow> Q) \<Longrightarrow> Q\<close> is unsafe in a different sense:
  since it keeps the assumption \<open>\<forall>x. P x\<close>, it is prone to
  looping.  In classical first-order logic, all rules are safe except
  those mentioned above.

  The safe~/ unsafe distinction is vague, and may be regarded merely
  as a way of giving some rules priority over others.  One could argue
  that \<open>(\<or>E)\<close> is unsafe, because repeated application of it
  could generate exponentially many subgoals.  Induction rules are
  unsafe because inductive proofs are difficult to set up
  automatically.  Any inference that instantiates an unknown
  in the proof state is unsafe --- thus matching must be used, rather than
  unification.  Even proof by assumption is unsafe if it instantiates
  unknowns shared with other subgoals.

  \begin{matharray}{rcl}
    @{command_def "print_claset"}\<open>\<^sup>*\<close> & : & \<open>context \<rightarrow>\<close> \\
    @{attribute_def intro} & : & \<open>attribute\<close> \\
    @{attribute_def elim} & : & \<open>attribute\<close> \\
    @{attribute_def dest} & : & \<open>attribute\<close> \\
    @{attribute_def rule} & : & \<open>attribute\<close> \\
    @{attribute_def iff} & : & \<open>attribute\<close> \\
    @{attribute_def swapped} & : & \<open>attribute\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@@{attribute intro} | @@{attribute elim} | @@{attribute dest}) ('!' | () | '?') @{syntax nat}?
    ;
    @@{attribute rule} 'del'
    ;
    @@{attribute iff} (((() | 'add') '?'?) | 'del')
  \<close>

  \<^descr> @{command "print_claset"} prints the collection of rules
  declared to the Classical Reasoner, i.e.\ the \<^ML_type>\<open>claset\<close>
  within the context.

  \<^descr> @{attribute intro}, @{attribute elim}, and @{attribute dest}
  declare introduction, elimination, and destruction rules,
  respectively.  By default, rules are considered as \<^emph>\<open>unsafe\<close>
  (i.e.\ not applied blindly without backtracking), while ``\<open>!\<close>'' classifies as \<^emph>\<open>safe\<close>.  Rule declarations marked by
  ``\<open>?\<close>'' coincide with those of Isabelle/Pure, cf.\
  \secref{sec:pure-meth-att} (i.e.\ are only applied in single steps
  of the @{method rule} method).  The optional natural number
  specifies an explicit weight argument, which is ignored by the
  automated reasoning tools, but determines the search order of single
  rule steps.

  Introduction rules are those that can be applied using ordinary
  resolution.  Their swapped forms are generated internally, which
  will be applied using elim-resolution.  Elimination rules are
  applied using elim-resolution.  Rules are sorted by the number of
  new subgoals they will yield; rules that generate the fewest
  subgoals will be tried first.  Otherwise, later declarations take
  precedence over earlier ones.

  Rules already present in the context with the same classification
  are ignored.  A warning is printed if the rule has already been
  added with some other classification, but the rule is added anyway
  as requested.

  \<^descr> @{attribute rule}~\<open>del\<close> deletes all occurrences of a
  rule from the classical context, regardless of its classification as
  introduction~/ elimination~/ destruction and safe~/ unsafe.

  \<^descr> @{attribute iff} declares logical equivalences to the
  Simplifier and the Classical reasoner at the same time.
  Non-conditional rules result in a safe introduction and elimination
  pair; conditional ones are considered unsafe.  Rules with negative
  conclusion are automatically inverted (using \<open>\<not>\<close>-elimination
  internally).

  The ``\<open>?\<close>'' version of @{attribute iff} declares rules to
  the Isabelle/Pure context only, and omits the Simplifier
  declaration.

  \<^descr> @{attribute swapped} turns an introduction rule into an
  elimination, by resolving with the classical swap principle \<open>\<not> P \<Longrightarrow> (\<not> R \<Longrightarrow> P) \<Longrightarrow> R\<close> in the second position.  This is mainly for
  illustrative purposes: the Classical Reasoner already swaps rules
  internally as explained above.
\<close>


subsection \<open>Structured methods\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def rule} & : & \<open>method\<close> \\
    @{method_def contradiction} & : & \<open>method\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{method rule} @{syntax thms}?
  \<close>

  \<^descr> @{method rule} as offered by the Classical Reasoner is a
  refinement over the Pure one (see \secref{sec:pure-meth-att}).  Both
  versions work the same, but the classical version observes the
  classical rule context in addition to that of Isabelle/Pure.

  Common object logics (HOL, ZF, etc.) declare a rich collection of
  classical rules (even if these would qualify as intuitionistic
  ones), but only few declarations to the rule context of
  Isabelle/Pure (\secref{sec:pure-meth-att}).

  \<^descr> @{method contradiction} solves some goal by contradiction,
  deriving any result from both \<open>\<not> A\<close> and \<open>A\<close>.  Chained
  facts, which are guaranteed to participate, may appear in either
  order.
\<close>


subsection \<open>Fully automated methods\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def blast} & : & \<open>method\<close> \\
    @{method_def auto} & : & \<open>method\<close> \\
    @{method_def force} & : & \<open>method\<close> \\
    @{method_def fast} & : & \<open>method\<close> \\
    @{method_def slow} & : & \<open>method\<close> \\
    @{method_def best} & : & \<open>method\<close> \\
    @{method_def fastforce} & : & \<open>method\<close> \\
    @{method_def slowsimp} & : & \<open>method\<close> \\
    @{method_def bestsimp} & : & \<open>method\<close> \\
    @{method_def deepen} & : & \<open>method\<close> \\
  \end{matharray}

  \<^rail>\<open>
    @@{method blast} @{syntax nat}? (@{syntax clamod} * )
    ;
    @@{method auto} (@{syntax nat} @{syntax nat})? (@{syntax clasimpmod} * )
    ;
    @@{method force} (@{syntax clasimpmod} * )
    ;
    (@@{method fast} | @@{method slow} | @@{method best}) (@{syntax clamod} * )
    ;
    (@@{method fastforce} | @@{method slowsimp} | @@{method bestsimp})
      (@{syntax clasimpmod} * )
    ;
    @@{method deepen} (@{syntax nat} ?) (@{syntax clamod} * )
    ;
    @{syntax_def clamod}:
      (('intro' | 'elim' | 'dest') ('!' | () | '?') | 'del') ':' @{syntax thms}
    ;
    @{syntax_def clasimpmod}: ('simp' (() | 'add' | 'del' | 'only') |
      'cong' (() | 'add' | 'del') |
      'split' (() | '!' | 'del') |
      'iff' (((() | 'add') '?'?) | 'del') |
      (('intro' | 'elim' | 'dest') ('!' | () | '?') | 'del')) ':' @{syntax thms}
  \<close>

  \<^descr> @{method blast} is a separate classical tableau prover that
  uses the same classical rule declarations as explained before.

  Proof search is coded directly in ML using special data structures.
  A successful proof is then reconstructed using regular Isabelle
  inferences.  It is faster and more powerful than the other classical
  reasoning tools, but has major limitations too.

    \<^item> It does not use the classical wrapper tacticals, such as the
    integration with the Simplifier of @{method fastforce}.

    \<^item> It does not perform higher-order unification, as needed by the
    rule @{thm [source=false] rangeI} in HOL.  There are often
    alternatives to such rules, for example @{thm [source=false]
    range_eqI}.

    \<^item> Function variables may only be applied to parameters of the
    subgoal.  (This restriction arises because the prover does not use
    higher-order unification.)  If other function variables are present
    then the prover will fail with the message
    @{verbatim [display] \<open>Function unknown's argument not a bound variable\<close>}

    \<^item> Its proof strategy is more general than @{method fast} but can
    be slower.  If @{method blast} fails or seems to be running forever,
    try @{method fast} and the other proof tools described below.

  The optional integer argument specifies a bound for the number of
  unsafe steps used in a proof.  By default, @{method blast} starts
  with a bound of 0 and increases it successively to 20.  In contrast,
  \<open>(blast lim)\<close> tries to prove the goal using a search bound
  of \<open>lim\<close>.  Sometimes a slow proof using @{method blast} can
  be made much faster by supplying the successful search bound to this
  proof method instead.

  \<^descr> @{method auto} combines classical reasoning with
  simplification.  It is intended for situations where there are a lot
  of mostly trivial subgoals; it proves all the easy ones, leaving the
  ones it cannot prove.  Occasionally, attempting to prove the hard
  ones may take a long time.

  The optional depth arguments in \<open>(auto m n)\<close> refer to its
  builtin classical reasoning procedures: \<open>m\<close> (default 4) is for
  @{method blast}, which is tried first, and \<open>n\<close> (default 2) is
  for a slower but more general alternative that also takes wrappers
  into account.

  \<^descr> @{method force} is intended to prove the first subgoal
  completely, using many fancy proof tools and performing a rather
  exhaustive search.  As a result, proof attempts may take rather long
  or diverge easily.

  \<^descr> @{method fast}, @{method best}, @{method slow} attempt to
  prove the first subgoal using sequent-style reasoning as explained
  before.  Unlike @{method blast}, they construct proofs directly in
  Isabelle.

  There is a difference in search strategy and back-tracking: @{method
  fast} uses depth-first search and @{method best} uses best-first
  search (guided by a heuristic function: normally the total size of
  the proof state).

  Method @{method slow} is like @{method fast}, but conducts a broader
  search: it may, when backtracking from a failed proof attempt, undo
  even the step of proving a subgoal by assumption.

  \<^descr> @{method fastforce}, @{method slowsimp}, @{method bestsimp}
  are like @{method fast}, @{method slow}, @{method best},
  respectively, but use the Simplifier as additional wrapper. The name
  @{method fastforce}, reflects the behaviour of this popular method
  better without requiring an understanding of its implementation.

  \<^descr> @{method deepen} works by exhaustive search up to a certain
  depth.  The start depth is 4 (unless specified explicitly), and the
  depth is increased iteratively up to 10.  Unsafe rules are modified
  to preserve the formula they act on, so that it be used repeatedly.
  This method can prove more goals than @{method fast}, but is much
  slower, for example if the assumptions have many universal
  quantifiers.


  Any of the above methods support additional modifiers of the context
  of classical (and simplifier) rules, but the ones related to the
  Simplifier are explicitly prefixed by \<open>simp\<close> here.  The
  semantics of these ad-hoc rule declarations is analogous to the
  attributes given before.  Facts provided by forward chaining are
  inserted into the goal before commencing proof search.
\<close>


subsection \<open>Partially automated methods\label{sec:classical:partial}\<close>

text \<open>These proof methods may help in situations when the
  fully-automated tools fail.  The result is a simpler subgoal that
  can be tackled by other means, such as by manual instantiation of
  quantifiers.

  \begin{matharray}{rcl}
    @{method_def safe} & : & \<open>method\<close> \\
    @{method_def clarify} & : & \<open>method\<close> \\
    @{method_def clarsimp} & : & \<open>method\<close> \\
  \end{matharray}

  \<^rail>\<open>
    (@@{method safe} | @@{method clarify}) (@{syntax clamod} * )
    ;
    @@{method clarsimp} (@{syntax clasimpmod} * )
  \<close>

  \<^descr> @{method safe} repeatedly performs safe steps on all subgoals.
  It is deterministic, with at most one outcome.

  \<^descr> @{method clarify} performs a series of safe steps without
  splitting subgoals; see also @{method clarify_step}.

  \<^descr> @{method clarsimp} acts like @{method clarify}, but also does
  simplification.  Note that if the Simplifier context includes a
  splitter for the premises, the subgoal may still be split.
\<close>


subsection \<open>Single-step tactics\<close>

text \<open>
  \begin{matharray}{rcl}
    @{method_def safe_step} & : & \<open>method\<close> \\
    @{method_def inst_step} & : & \<open>method\<close> \\
    @{method_def step} & : & \<open>method\<close> \\
    @{method_def slow_step} & : & \<open>method\<close> \\
    @{method_def clarify_step} & : &  \<open>method\<close> \\
  \end{matharray}

  These are the primitive tactics behind the automated proof methods
  of the Classical Reasoner.  By calling them yourself, you can
  execute these procedures one step at a time.

  \<^descr> @{method safe_step} performs a safe step on the first subgoal.
  The safe wrapper tacticals are applied to a tactic that may include
  proof by assumption or Modus Ponens (taking care not to instantiate
  unknowns), or substitution.

  \<^descr> @{method inst_step} is like @{method safe_step}, but allows
  unknowns to be instantiated.

  \<^descr> @{method step} is the basic step of the proof procedure, it
  operates on the first subgoal.  The unsafe wrapper tacticals are
  applied to a tactic that tries @{method safe}, @{method inst_step},
  or applies an unsafe rule from the context.

  \<^descr> @{method slow_step} resembles @{method step}, but allows
  backtracking between using safe rules with instantiation (@{method
  inst_step}) and using unsafe rules.  The resulting search space is
  larger.

  \<^descr> @{method clarify_step} performs a safe step on the first
  subgoal; no splitting step is applied.  For example, the subgoal
  \<open>A \<and> B\<close> is left as a conjunction.  Proof by assumption,
  Modus Ponens, etc., may be performed provided they do not
  instantiate unknowns.  Assumptions of the form \<open>x = t\<close> may
  be eliminated.  The safe wrapper tactical is applied.
\<close>


subsection \<open>Modifying the search step\<close>

text \<open>
  \begin{mldecls}
    @{define_ML_type wrapper = "(int -> tactic) -> (int -> tactic)"} \\[0.5ex]
    @{define_ML_infix addSWrapper: "Proof.context *
  (string * (Proof.context -> wrapper)) -> Proof.context"} \\
    @{define_ML_infix addSbefore: "Proof.context *
  (string * (Proof.context -> int -> tactic)) -> Proof.context"} \\
    @{define_ML_infix addSafter: "Proof.context *
  (string * (Proof.context -> int -> tactic)) -> Proof.context"} \\
    @{define_ML_infix delSWrapper: "Proof.context * string -> Proof.context"} \\[0.5ex]
    @{define_ML_infix addWrapper: "Proof.context *
  (string * (Proof.context -> wrapper)) -> Proof.context"} \\
    @{define_ML_infix addbefore: "Proof.context *
  (string * (Proof.context -> int -> tactic)) -> Proof.context"} \\
    @{define_ML_infix addafter: "Proof.context *
  (string * (Proof.context -> int -> tactic)) -> Proof.context"} \\
    @{define_ML_infix delWrapper: "Proof.context * string -> Proof.context"} \\[0.5ex]
    @{define_ML addSss: "Proof.context -> Proof.context"} \\
    @{define_ML addss: "Proof.context -> Proof.context"} \\
  \end{mldecls}

  The proof strategy of the Classical Reasoner is simple.  Perform as
  many safe inferences as possible; or else, apply certain safe rules,
  allowing instantiation of unknowns; or else, apply an unsafe rule.
  The tactics also eliminate assumptions of the form \<open>x = t\<close>
  by substitution if they have been set up to do so.  They may perform
  a form of Modus Ponens: if there are assumptions \<open>P \<longrightarrow> Q\<close> and
  \<open>P\<close>, then replace \<open>P \<longrightarrow> Q\<close> by \<open>Q\<close>.

  The classical reasoning tools --- except @{method blast} --- allow
  to modify this basic proof strategy by applying two lists of
  arbitrary \<^emph>\<open>wrapper tacticals\<close> to it.  The first wrapper list,
  which is considered to contain safe wrappers only, affects @{method
  safe_step} and all the tactics that call it.  The second one, which
  may contain unsafe wrappers, affects the unsafe parts of @{method
  step}, @{method slow_step}, and the tactics that call them.  A
  wrapper transforms each step of the search, for example by
  attempting other tactics before or after the original step tactic.
  All members of a wrapper list are applied in turn to the respective
  step tactic.

  Initially the two wrapper lists are empty, which means no
  modification of the step tactics. Safe and unsafe wrappers are added
  to the context with the functions given below, supplying them with
  wrapper names.  These names may be used to selectively delete
  wrappers.

  \<^descr> \<open>ctxt addSWrapper (name, wrapper)\<close> adds a new wrapper,
  which should yield a safe tactic, to modify the existing safe step
  tactic.

  \<^descr> \<open>ctxt addSbefore (name, tac)\<close> adds the given tactic as a
  safe wrapper, such that it is tried \<^emph>\<open>before\<close> each safe step of
  the search.

  \<^descr> \<open>ctxt addSafter (name, tac)\<close> adds the given tactic as a
  safe wrapper, such that it is tried when a safe step of the search
  would fail.

  \<^descr> \<open>ctxt delSWrapper name\<close> deletes the safe wrapper with
  the given name.

  \<^descr> \<open>ctxt addWrapper (name, wrapper)\<close> adds a new wrapper to
  modify the existing (unsafe) step tactic.

  \<^descr> \<open>ctxt addbefore (name, tac)\<close> adds the given tactic as an
  unsafe wrapper, such that it its result is concatenated
  \<^emph>\<open>before\<close> the result of each unsafe step.

  \<^descr> \<open>ctxt addafter (name, tac)\<close> adds the given tactic as an
  unsafe wrapper, such that it its result is concatenated \<^emph>\<open>after\<close>
  the result of each unsafe step.

  \<^descr> \<open>ctxt delWrapper name\<close> deletes the unsafe wrapper with
  the given name.

  \<^descr> \<open>addSss\<close> adds the simpset of the context to its
  classical set. The assumptions and goal will be simplified, in a
  rather safe way, after each safe step of the search.

  \<^descr> \<open>addss\<close> adds the simpset of the context to its
  classical set. The assumptions and goal will be simplified, before
  the each unsafe step of the search.
\<close>


section \<open>Object-logic setup \label{sec:object-logic}\<close>

text \<open>
  \begin{matharray}{rcl}
    @{command_def "judgment"} & : & \<open>theory \<rightarrow> theory\<close> \\
    @{method_def atomize} & : & \<open>method\<close> \\
    @{attribute_def atomize} & : & \<open>attribute\<close> \\
    @{attribute_def rule_format} & : & \<open>attribute\<close> \\
    @{attribute_def rulify} & : & \<open>attribute\<close> \\
  \end{matharray}

  The very starting point for any Isabelle object-logic is a ``truth
  judgment'' that links object-level statements to the meta-logic
  (with its minimal language of \<open>prop\<close> that covers universal
  quantification \<open>\<And>\<close> and implication \<open>\<Longrightarrow>\<close>).

  Common object-logics are sufficiently expressive to internalize rule
  statements over \<open>\<And>\<close> and \<open>\<Longrightarrow>\<close> within their own
  language.  This is useful in certain situations where a rule needs
  to be viewed as an atomic statement from the meta-level perspective,
  e.g.\ \<open>\<And>x. x \<in> A \<Longrightarrow> P x\<close> versus \<open>\<forall>x \<in> A. P x\<close>.

  From the following language elements, only the @{method atomize}
  method and @{attribute rule_format} attribute are occasionally
  required by end-users, the rest is for those who need to setup their
  own object-logic.  In the latter case existing formulations of
  Isabelle/FOL or Isabelle/HOL may be taken as realistic examples.

  Generic tools may refer to the information provided by object-logic
  declarations internally.

  \<^rail>\<open>
    @@{command judgment} @{syntax name} '::' @{syntax type} @{syntax mixfix}?
    ;
    @@{attribute atomize} ('(' 'full' ')')?
    ;
    @@{attribute rule_format} ('(' 'noasm' ')')?
  \<close>

  \<^descr> @{command "judgment"}~\<open>c :: \<sigma> (mx)\<close> declares constant
  \<open>c\<close> as the truth judgment of the current object-logic.  Its
  type \<open>\<sigma>\<close> should specify a coercion of the category of
  object-level propositions to \<open>prop\<close> of the Pure meta-logic;
  the mixfix annotation \<open>(mx)\<close> would typically just link the
  object language (internally of syntactic category \<open>logic\<close>)
  with that of \<open>prop\<close>.  Only one @{command "judgment"}
  declaration may be given in any theory development.
  
  \<^descr> @{method atomize} (as a method) rewrites any non-atomic
  premises of a sub-goal, using the meta-level equations declared via
  @{attribute atomize} (as an attribute) beforehand.  As a result,
  heavily nested goals become amenable to fundamental operations such
  as resolution (cf.\ the @{method (Pure) rule} method).  Giving the ``\<open>(full)\<close>'' option here means to turn the whole subgoal into an
  object-statement (if possible), including the outermost parameters
  and assumptions as well.

  A typical collection of @{attribute atomize} rules for a particular
  object-logic would provide an internalization for each of the
  connectives of \<open>\<And>\<close>, \<open>\<Longrightarrow>\<close>, and \<open>\<equiv>\<close>.
  Meta-level conjunction should be covered as well (this is
  particularly important for locales, see \secref{sec:locale}).

  \<^descr> @{attribute rule_format} rewrites a theorem by the equalities
  declared as @{attribute rulify} rules in the current object-logic.
  By default, the result is fully normalized, including assumptions
  and conclusions at any depth.  The \<open>(no_asm)\<close> option
  restricts the transformation to the conclusion of a rule.

  In common object-logics (HOL, FOL, ZF), the effect of @{attribute
  rule_format} is to replace (bounded) universal quantification
  (\<open>\<forall>\<close>) and implication (\<open>\<longrightarrow>\<close>) by the corresponding
  rule statements over \<open>\<And>\<close> and \<open>\<Longrightarrow>\<close>.
\<close>


section \<open>Tracing higher-order unification\<close>

text \<open>
  \begin{tabular}{rcll}
    @{attribute_def unify_trace_simp} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def unify_trace_types} & : & \<open>attribute\<close> & default \<open>false\<close> \\
    @{attribute_def unify_trace_bound} & : & \<open>attribute\<close> & default \<open>50\<close> \\
    @{attribute_def unify_search_bound} & : & \<open>attribute\<close> & default \<open>60\<close> \\
  \end{tabular}
  \<^medskip>

  Higher-order unification works well in most practical situations,
  but sometimes needs extra care to identify problems.  These tracing
  options may help.

  \<^descr> @{attribute unify_trace_simp} controls tracing of the
  simplification phase of higher-order unification.

  \<^descr> @{attribute unify_trace_types} controls warnings of
  incompleteness, when unification is not considering all possible
  instantiations of schematic type variables.

  \<^descr> @{attribute unify_trace_bound} determines the depth where
  unification starts to print tracing information once it reaches
  depth; 0 for full tracing.  At the default value, tracing
  information is almost never printed in practice.

  \<^descr> @{attribute unify_search_bound} prevents unification from
  searching past the given depth.  Because of this bound, higher-order
  unification cannot return an infinite sequence, though it can return
  an exponentially long one.  The search rarely approaches the default
  value in practice.  If the search is cut off, unification prints a
  warning ``Unification bound exceeded''.


  \begin{warn}
  Options for unification cannot be modified in a local context.  Only
  the global theory content is taken into account.
  \end{warn}
\<close>

end
