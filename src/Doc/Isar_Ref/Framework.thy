(*:maxLineLen=78:*)

theory Framework
  imports Main Base
begin

chapter \<open>The Isabelle/Isar Framework \label{ch:isar-framework}\<close>

text \<open>
  Isabelle/Isar @{cite "Wenzel:1999:TPHOL" and "Wenzel-PhD" and
  "Nipkow-TYPES02" and "Wiedijk:1999:Mizar" and "Wenzel-Paulson:2006" and
  "Wenzel:2006:Festschrift"} is a generic framework for developing formal
  mathematical documents with full proof checking. Definitions, statements and
  proofs are organized as theories. A collection of theories sources may be
  presented as a printed document; see also \chref{ch:document-prep}.

  The main concern of Isar is the design of a human-readable structured proof
  language, which is called the ``primary proof format'' in Isar terminology.
  Such a primary proof language is somewhere in the middle between the
  extremes of primitive proof objects and actual natural language.

  Thus Isar challenges the traditional way of recording informal proofs in
  mathematical prose, as well as the common tendency to see fully formal
  proofs directly as objects of some logical calculus (e.g.\ \<open>\<lambda>\<close>-terms in a
  version of type theory). Technically, Isar is an interpreter of a simple
  block-structured language for describing the data flow of local facts and
  goals, interspersed with occasional invocations of proof methods. Everything
  is reduced to logical inferences internally, but these steps are somewhat
  marginal compared to the overall bookkeeping of the interpretation process.
  Thanks to careful design of the syntax and semantics of Isar language
  elements, a formal record of Isar commands may later appear as an
  intelligible text to the human reader.

  The Isar proof language has emerged from careful analysis of some inherent
  virtues of the logical framework Isabelle/Pure @{cite "paulson-found" and
  "paulson700"}, notably composition of higher-order natural deduction rules,
  which is a generalization of Gentzen's original calculus @{cite
  "Gentzen:1935"}. The approach of generic inference systems in Pure is
  continued by Isar towards actual proof texts. See also
  \figref{fig:natural-deduction}

  \begin{figure}[htb]

  \begin{center}
  \begin{minipage}[t]{0.9\textwidth}

  \textbf{Inferences:}
  \begin{center}
  \begin{tabular}{l@ {\qquad}l}
  \infer{\<open>B\<close>}{\<open>A \<longrightarrow> B\<close> & \<open>A\<close>} &
  \infer{\<open>A \<longrightarrow> B\<close>}{\infer*{\<open>B\<close>}{\<open>[A]\<close>}} \\
  \end{tabular}
  \end{center}

  \textbf{Isabelle/Pure:}
  \begin{center}
  \begin{tabular}{l@ {\qquad}l}
  \<open>(A \<longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B\<close> &
  \<open>(A \<Longrightarrow> B) \<Longrightarrow> A \<longrightarrow> B\<close>
  \end{tabular}
  \end{center}

  \textbf{Isabelle/Isar:}
  \begin{center}
  \begin{minipage}[t]{0.4\textwidth}
  @{theory_text [display, indent = 2]
    \<open>have "A \<longrightarrow> B" \<proof>
also have A \<proof>
finally have B .\<close>}
  \end{minipage}
  \begin{minipage}[t]{0.4\textwidth}
  @{theory_text [display, indent = 2]
    \<open>have "A \<longrightarrow> B"
proof
  assume A
  then show B \<proof>
qed\<close>}
  \end{minipage}
  \end{center}

  \end{minipage}
  \end{center}

  \caption{Natural Deduction via inferences according to Gentzen, rules in
  Isabelle/Pure, and proofs in Isabelle/Isar}\label{fig:natural-deduction}

  \end{figure}

  \<^medskip>
  Concrete applications require another intermediate layer: an object-logic.
  Isabelle/HOL @{cite "isa-tutorial"} (simply-typed set-theory) is most
  commonly used; elementary examples are given in the directory
  \<^dir>\<open>~~/src/HOL/Isar_Examples\<close>. Some examples demonstrate how to start a fresh
  object-logic from Isabelle/Pure, and use Isar proofs from the very start,
  despite the lack of advanced proof tools at such an early stage (e.g.\ see
  \<^file>\<open>~~/src/HOL/Isar_Examples/Higher_Order_Logic.thy\<close>). Isabelle/FOL @{cite
  "isabelle-logics"} and Isabelle/ZF @{cite "isabelle-ZF"} also work, but are
  much less developed.

  In order to illustrate natural deduction in Isar, we shall subsequently
  refer to the background theory and library of Isabelle/HOL. This includes
  common notions of predicate logic, naive set-theory etc.\ using fairly
  standard mathematical notation. From the perspective of generic natural
  deduction there is nothing special about the logical connectives of HOL
  (\<open>\<and>\<close>, \<open>\<or>\<close>, \<open>\<forall>\<close>, \<open>\<exists>\<close>, etc.), only the resulting reasoning principles are
  relevant to the user. There are similar rules available for set-theory
  operators (\<open>\<inter>\<close>, \<open>\<union>\<close>, \<open>\<Inter>\<close>, \<open>\<Union>\<close>, etc.), or any other theory developed in the
  library (lattice theory, topology etc.).

  Subsequently we briefly review fragments of Isar proof texts corresponding
  directly to such general deduction schemes. The examples shall refer to
  set-theory, to minimize the danger of understanding connectives of predicate
  logic as something special.

  \<^medskip>
  The following deduction performs \<open>\<inter>\<close>-introduction, working forwards from
  assumptions towards the conclusion. We give both the Isar text, and depict
  the primitive rule involved, as determined by unification of fact and goal
  statements against rules that are declared in the library context.
\<close>

text_raw \<open>\medskip\begin{minipage}{0.6\textwidth}\<close>

(*<*)
notepad
begin
    fix x :: 'a and A B
(*>*)
    assume "x \<in> A" and "x \<in> B"
    then have "x \<in> A \<inter> B" ..
(*<*)
end
(*>*)

text_raw \<open>\end{minipage}\begin{minipage}{0.4\textwidth}\<close>

text \<open>
  \infer{\<open>x \<in> A \<inter> B\<close>}{\<open>x \<in> A\<close> & \<open>x \<in> B\<close>}
\<close>

text_raw \<open>\end{minipage}\<close>

text \<open>
  \<^medskip>
  Note that \<^theory_text>\<open>assume\<close> augments the proof context, \<^theory_text>\<open>then\<close> indicates that the
  current fact shall be used in the next step, and \<^theory_text>\<open>have\<close> states an
  intermediate goal. The two dots ``\<^theory_text>\<open>..\<close>'' refer to a complete proof of this
  claim, using the indicated facts and a canonical rule from the context. We
  could have been more explicit here by spelling out the final proof step via
  the \<^theory_text>\<open>by\<close> command:
\<close>

(*<*)
notepad
begin
    fix x :: 'a and A B
(*>*)
    assume "x \<in> A" and "x \<in> B"
    then have "x \<in> A \<inter> B" by (rule IntI)
(*<*)
end
(*>*)

text \<open>
  The format of the \<open>\<inter>\<close>-introduction rule represents the most basic inference,
  which proceeds from given premises to a conclusion, without any nested proof
  context involved.

  The next example performs backwards introduction of \<open>\<Inter>\<A>\<close>, the intersection
  of all sets within a given set. This requires a nested proof of set
  membership within a local context, where \<open>A\<close> is an arbitrary-but-fixed
  member of the collection:
\<close>

text_raw \<open>\medskip\begin{minipage}{0.6\textwidth}\<close>

(*<*)
notepad
begin
    fix x :: 'a and \<A>
(*>*)
    have "x \<in> \<Inter>\<A>"
    proof
      fix A
      assume "A \<in> \<A>"
      show "x \<in> A" \<proof>
    qed
(*<*)
end
(*>*)

text_raw \<open>\end{minipage}\begin{minipage}{0.4\textwidth}\<close>

text \<open>
  \infer{\<open>x \<in> \<Inter>\<A>\<close>}{\infer*{\<open>x \<in> A\<close>}{\<open>[A][A \<in> \<A>]\<close>}}
\<close>

text_raw \<open>\end{minipage}\<close>

text \<open>
  \<^medskip>
  This Isar reasoning pattern again refers to the primitive rule depicted
  above. The system determines it in the ``\<^theory_text>\<open>proof\<close>'' step, which could have
  been spelled out more explicitly as ``\<^theory_text>\<open>proof (rule InterI)\<close>''. Note that
  the rule involves both a local parameter \<open>A\<close> and an assumption \<open>A \<in> \<A>\<close> in
  the nested reasoning. Such compound rules typically demands a genuine
  subproof in Isar, working backwards rather than forwards as seen before. In
  the proof body we encounter the \<^theory_text>\<open>fix\<close>-\<^theory_text>\<open>assume\<close>-\<^theory_text>\<open>show\<close> outline of nested
  subproofs that is typical for Isar. The final \<^theory_text>\<open>show\<close> is like \<^theory_text>\<open>have\<close>
  followed by an additional refinement of the enclosing claim, using the rule
  derived from the proof body.

  \<^medskip>
  The next example involves \<open>\<Union>\<A>\<close>, which can be characterized as the set of
  all \<open>x\<close> such that \<open>\<exists>A. x \<in> A \<and> A \<in> \<A>\<close>. The elimination rule for \<open>x \<in> \<Union>\<A>\<close>
  does not mention \<open>\<exists>\<close> and \<open>\<and>\<close> at all, but admits to obtain directly a local
  \<open>A\<close> such that \<open>x \<in> A\<close> and \<open>A \<in> \<A>\<close> hold. This corresponds to the following
  Isar proof and inference rule, respectively:
\<close>

text_raw \<open>\medskip\begin{minipage}{0.6\textwidth}\<close>

(*<*)
notepad
begin
    fix x :: 'a and \<A> C
(*>*)
    assume "x \<in> \<Union>\<A>"
    then have C
    proof
      fix A
      assume "x \<in> A" and "A \<in> \<A>"
      show C \<proof>
    qed
(*<*)
end
(*>*)

text_raw \<open>\end{minipage}\begin{minipage}{0.4\textwidth}\<close>

text \<open>
  \infer{\<open>C\<close>}{\<open>x \<in> \<Union>\<A>\<close> & \infer*{\<open>C\<close>~}{\<open>[A][x \<in> A, A \<in> \<A>]\<close>}}
\<close>

text_raw \<open>\end{minipage}\<close>

text \<open>
  \<^medskip>
  Although the Isar proof follows the natural deduction rule closely, the text
  reads not as natural as anticipated. There is a double occurrence of an
  arbitrary conclusion \<open>C\<close>, which represents the final result, but is
  irrelevant for now. This issue arises for any elimination rule involving
  local parameters. Isar provides the derived language element \<^theory_text>\<open>obtain\<close>,
  which is able to perform the same elimination proof more conveniently:
\<close>

(*<*)
notepad
begin
    fix x :: 'a and \<A>
(*>*)
    assume "x \<in> \<Union>\<A>"
    then obtain A where "x \<in> A" and "A \<in> \<A>" ..
(*<*)
end
(*>*)

text \<open>
  Here we avoid to mention the final conclusion \<open>C\<close> and return to plain
  forward reasoning. The rule involved in the ``\<^theory_text>\<open>..\<close>'' proof is the same as
  before.
\<close>


section \<open>The Pure framework \label{sec:framework-pure}\<close>

text \<open>
  The Pure logic @{cite "paulson-found" and "paulson700"} is an intuitionistic
  fragment of higher-order logic @{cite "church40"}. In type-theoretic
  parlance, there are three levels of \<open>\<lambda>\<close>-calculus with corresponding arrows
  \<open>\<Rightarrow>\<close>/\<open>\<And>\<close>/\<open>\<Longrightarrow>\<close>:

  \<^medskip>
  \begin{tabular}{ll}
  \<open>\<alpha> \<Rightarrow> \<beta>\<close> & syntactic function space (terms depending on terms) \\
  \<open>\<And>x. B(x)\<close> & universal quantification (proofs depending on terms) \\
  \<open>A \<Longrightarrow> B\<close> & implication (proofs depending on proofs) \\
  \end{tabular}
  \<^medskip>

  Here only the types of syntactic terms, and the propositions of proof terms
  have been shown. The \<open>\<lambda>\<close>-structure of proofs can be recorded as an optional
  feature of the Pure inference kernel @{cite "Berghofer-Nipkow:2000:TPHOL"},
  but the formal system can never depend on them due to \<^emph>\<open>proof irrelevance\<close>.

  On top of this most primitive layer of proofs, Pure implements a generic
  calculus for nested natural deduction rules, similar to @{cite
  "Schroeder-Heister:1984"}. Here object-logic inferences are internalized as
  formulae over \<open>\<And>\<close> and \<open>\<Longrightarrow>\<close>. Combining such rule statements may involve
  higher-order unification @{cite "paulson-natural"}.
\<close>


subsection \<open>Primitive inferences\<close>

text \<open>
  Term syntax provides explicit notation for abstraction \<open>\<lambda>x :: \<alpha>. b(x)\<close> and
  application \<open>b a\<close>, while types are usually implicit thanks to
  type-inference; terms of type \<open>prop\<close> are called propositions. Logical
  statements are composed via \<open>\<And>x :: \<alpha>. B(x)\<close> and \<open>A \<Longrightarrow> B\<close>. Primitive reasoning
  operates on judgments of the form \<open>\<Gamma> \<turnstile> \<phi>\<close>, with standard introduction and
  elimination rules for \<open>\<And>\<close> and \<open>\<Longrightarrow>\<close> that refer to fixed parameters \<open>x\<^sub>1, \<dots>,
  x\<^sub>m\<close> and hypotheses \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close> from the context \<open>\<Gamma>\<close>; the corresponding
  proof terms are left implicit. The subsequent inference rules define \<open>\<Gamma> \<turnstile> \<phi>\<close>
  inductively, relative to a collection of axioms from the implicit background
  theory:

  \[
  \infer{\<open>\<turnstile> A\<close>}{\<open>A\<close> \mbox{~is axiom}}
  \qquad
  \infer{\<open>A \<turnstile> A\<close>}{}
  \]

  \[
  \infer{\<open>\<Gamma> \<turnstile> \<And>x. B(x)\<close>}{\<open>\<Gamma> \<turnstile> B(x)\<close> & \<open>x \<notin> \<Gamma>\<close>}
  \qquad
  \infer{\<open>\<Gamma> \<turnstile> B(a)\<close>}{\<open>\<Gamma> \<turnstile> \<And>x. B(x)\<close>}
  \]

  \[
  \infer{\<open>\<Gamma> - A \<turnstile> A \<Longrightarrow> B\<close>}{\<open>\<Gamma> \<turnstile> B\<close>}
  \qquad
  \infer{\<open>\<Gamma>\<^sub>1 \<union> \<Gamma>\<^sub>2 \<turnstile> B\<close>}{\<open>\<Gamma>\<^sub>1 \<turnstile> A \<Longrightarrow> B\<close> & \<open>\<Gamma>\<^sub>2 \<turnstile> A\<close>}
  \]

  Furthermore, Pure provides a built-in equality \<open>\<equiv> :: \<alpha> \<Rightarrow> \<alpha> \<Rightarrow> prop\<close> with
  axioms for reflexivity, substitution, extensionality, and \<open>\<alpha>\<beta>\<eta>\<close>-conversion
  on \<open>\<lambda>\<close>-terms.

  \<^medskip>

  An object-logic introduces another layer on top of Pure, e.g.\ with types
  \<open>i\<close> for individuals and \<open>o\<close> for propositions, term constants \<open>Trueprop :: o
  \<Rightarrow> prop\<close> as (implicit) derivability judgment and connectives like \<open>\<and> :: o \<Rightarrow> o
  \<Rightarrow> o\<close> or \<open>\<forall> :: (i \<Rightarrow> o) \<Rightarrow> o\<close>, and axioms for object-level rules such as
  \<open>conjI: A \<Longrightarrow> B \<Longrightarrow> A \<and> B\<close> or \<open>allI: (\<And>x. B x) \<Longrightarrow> \<forall>x. B x\<close>. Derived object rules
  are represented as theorems of Pure. After the initial object-logic setup,
  further axiomatizations are usually avoided: definitional principles are
  used instead (e.g.\ \<^theory_text>\<open>definition\<close>, \<^theory_text>\<open>inductive\<close>, \<^theory_text>\<open>fun\<close>, \<^theory_text>\<open>function\<close>).
\<close>


subsection \<open>Reasoning with rules \label{sec:framework-resolution}\<close>

text \<open>
  Primitive inferences mostly serve foundational purposes. The main reasoning
  mechanisms of Pure operate on nested natural deduction rules expressed as
  formulae, using \<open>\<And>\<close> to bind local parameters and \<open>\<Longrightarrow>\<close> to express entailment.
  Multiple parameters and premises are represented by repeating these
  connectives in a right-associative manner.

  Thanks to the Pure theorem @{prop "(A \<Longrightarrow> (\<And>x. B x)) \<equiv> (\<And>x. A \<Longrightarrow> B x)"} the
  connectives \<open>\<And>\<close> and \<open>\<Longrightarrow>\<close> commute. So we may assume w.l.o.g.\ that rule
  statements always observe the normal form where quantifiers are pulled in
  front of implications at each level of nesting. This means that any Pure
  proposition may be presented as a \<^emph>\<open>Hereditary Harrop Formula\<close> @{cite
  "Miller:1991"} which is of the form \<open>\<And>x\<^sub>1 \<dots> x\<^sub>m. H\<^sub>1 \<Longrightarrow> \<dots> H\<^sub>n \<Longrightarrow> A\<close> for \<open>m, n
  \<ge> 0\<close>, and \<open>A\<close> atomic, and \<open>H\<^sub>1, \<dots>, H\<^sub>n\<close> being recursively of the same
  format. Following the convention that outermost quantifiers are implicit,
  Horn clauses \<open>A\<^sub>1 \<Longrightarrow> \<dots> A\<^sub>n \<Longrightarrow> A\<close> are a special case of this.

  For example, the \<open>\<inter>\<close>-introduction rule encountered before is represented as
  a Pure theorem as follows:
  \[
  \<open>IntI:\<close>~@{prop "x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x \<in> A \<inter> B"}
  \]

  This is a plain Horn clause, since no further nesting on the left is
  involved. The general \<open>\<Inter>\<close>-introduction corresponds to a Hereditary Harrop
  Formula with one additional level of nesting:
  \[
  \<open>InterI:\<close>~@{prop "(\<And>A. A \<in> \<A> \<Longrightarrow> x \<in> A) \<Longrightarrow> x \<in> \<Inter>\<A>"}
  \]

  \<^medskip>
  Goals are also represented as rules: \<open>A\<^sub>1 \<Longrightarrow> \<dots> A\<^sub>n \<Longrightarrow> C\<close> states that the
  subgoals \<open>A\<^sub>1, \<dots>, A\<^sub>n\<close> entail the result \<open>C\<close>; for \<open>n = 0\<close> the goal is
  finished. To allow \<open>C\<close> being a rule statement itself, there is an internal
  protective marker \<open># :: prop \<Rightarrow> prop\<close>, which is defined as identity and
  hidden from the user. We initialize and finish goal states as follows:

  \[
  \begin{array}{c@ {\qquad}c}
  \infer[(@{inference_def init})]{\<open>C \<Longrightarrow> #C\<close>}{} &
  \infer[(@{inference_def finish})]{\<open>C\<close>}{\<open>#C\<close>}
  \end{array}
  \]

  Goal states are refined in intermediate proof steps until a finished form is
  achieved. Here the two main reasoning principles are @{inference
  resolution}, for back-chaining a rule against a subgoal (replacing it by
  zero or more subgoals), and @{inference assumption}, for solving a subgoal
  (finding a short-circuit with local assumptions). Below \<open>\<^vec>x\<close> stands
  for \<open>x\<^sub>1, \<dots>, x\<^sub>n\<close> (for \<open>n \<ge> 0\<close>).

  \[
  \infer[(@{inference_def resolution})]
  {\<open>(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> \<^vec>A (\<^vec>a \<^vec>x))\<vartheta> \<Longrightarrow> C\<vartheta>\<close>}
  {\begin{tabular}{rl}
    \<open>rule:\<close> &
    \<open>\<^vec>A \<^vec>a \<Longrightarrow> B \<^vec>a\<close> \\
    \<open>goal:\<close> &
    \<open>(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> B' \<^vec>x) \<Longrightarrow> C\<close> \\
    \<open>goal unifier:\<close> &
    \<open>(\<lambda>\<^vec>x. B (\<^vec>a \<^vec>x))\<vartheta> = B'\<vartheta>\<close> \\
   \end{tabular}}
  \]

  \<^medskip>

  \[
  \infer[(@{inference_def assumption})]{\<open>C\<vartheta>\<close>}
  {\begin{tabular}{rl}
    \<open>goal:\<close> &
    \<open>(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> A \<^vec>x) \<Longrightarrow> C\<close> \\
    \<open>assm unifier:\<close> & \<open>A\<vartheta> = H\<^sub>i\<vartheta>\<close>~~\mbox{for some~\<open>H\<^sub>i\<close>} \\
   \end{tabular}}
  \]

  The following trace illustrates goal-oriented reasoning in
  Isabelle/Pure:

  {\footnotesize
  \<^medskip>
  \begin{tabular}{r@ {\quad}l}
  \<open>(A \<and> B \<Longrightarrow> B \<and> A) \<Longrightarrow> #(A \<and> B \<Longrightarrow> B \<and> A)\<close> & \<open>(init)\<close> \\
  \<open>(A \<and> B \<Longrightarrow> B) \<Longrightarrow> (A \<and> B \<Longrightarrow> A) \<Longrightarrow> #\<dots>\<close> & \<open>(resolution B \<Longrightarrow> A \<Longrightarrow> B \<and> A)\<close> \\
  \<open>(A \<and> B \<Longrightarrow> A \<and> B) \<Longrightarrow> (A \<and> B \<Longrightarrow> A) \<Longrightarrow> #\<dots>\<close> & \<open>(resolution A \<and> B \<Longrightarrow> B)\<close> \\
  \<open>(A \<and> B \<Longrightarrow> A) \<Longrightarrow> #\<dots>\<close> & \<open>(assumption)\<close> \\
  \<open>(A \<and> B \<Longrightarrow> A \<and> B) \<Longrightarrow> #\<dots>\<close> & \<open>(resolution A \<and> B \<Longrightarrow> A)\<close> \\
  \<open>#\<dots>\<close> & \<open>(assumption)\<close> \\
  \<open>A \<and> B \<Longrightarrow> B \<and> A\<close> & \<open>(finish)\<close> \\
  \end{tabular}
  \<^medskip>
  }

  Compositions of @{inference assumption} after @{inference resolution} occurs
  quite often, typically in elimination steps. Traditional Isabelle tactics
  accommodate this by a combined @{inference_def elim_resolution} principle.
  In contrast, Isar uses a combined refinement rule as follows:\footnote{For
  simplicity and clarity, the presentation ignores \<^emph>\<open>weak premises\<close> as
  introduced via \<^theory_text>\<open>presume\<close> or \<^theory_text>\<open>show \<dots> when\<close>.}

  {\small
  \[
  \infer[(@{inference refinement})]
  {\<open>C\<vartheta>\<close>}
  {\begin{tabular}{rl}
    \<open>subgoal:\<close> &
    \<open>(\<And>\<^vec>x. \<^vec>H \<^vec>x \<Longrightarrow> B' \<^vec>x) \<Longrightarrow> C\<close> \\
    \<open>subproof:\<close> &
    \<open>\<^vec>G \<^vec>a \<Longrightarrow> B \<^vec>a\<close> \quad for schematic \<open>\<^vec>a\<close> \\
    \<open>concl unifier:\<close> &
    \<open>(\<lambda>\<^vec>x. B (\<^vec>a \<^vec>x))\<vartheta> = B'\<vartheta>\<close> \\
    \<open>assm unifiers:\<close> &
    \<open>(\<lambda>\<^vec>x. G\<^sub>j (\<^vec>a \<^vec>x))\<vartheta> = H\<^sub>i\<vartheta>\<close> \quad for each \<open>G\<^sub>j\<close> some \<open>H\<^sub>i\<close> \\
   \end{tabular}}
  \]}

  Here the \<open>subproof\<close> rule stems from the main \<^theory_text>\<open>fix\<close>-\<^theory_text>\<open>assume\<close>-\<^theory_text>\<open>show\<close>
  outline of Isar (cf.\ \secref{sec:framework-subproof}): each assumption
  indicated in the text results in a marked premise \<open>G\<close> above. Consequently,
  \<^theory_text>\<open>fix\<close>-\<^theory_text>\<open>assume\<close>-\<^theory_text>\<open>show\<close> enables to fit the result of a subproof quite
  robustly into a pending subgoal, while maintaining a good measure of
  flexibility: the subproof only needs to fit modulo unification, and its
  assumptions may be a proper subset of the subgoal premises (see
  \secref{sec:framework-subproof}).
\<close>


section \<open>The Isar proof language \label{sec:framework-isar}\<close>

text \<open>
  Structured proofs are presented as high-level expressions for composing
  entities of Pure (propositions, facts, and goals). The Isar proof language
  allows to organize reasoning within the underlying rule calculus of Pure,
  but Isar is not another logical calculus. Isar merely imposes certain
  structure and policies on Pure inferences. The main grammar of the Isar
  proof language is given in \figref{fig:isar-syntax}.

  \begin{figure}[htb]
  \begin{center}
  \begin{tabular}{rcl}
    \<open>main\<close> & \<open>=\<close> & \<^theory_text>\<open>notepad begin "statement\<^sup>*" end\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>theorem name: props if name: props for vars\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>theorem name:\<close> \\
    & & \quad\<^theory_text>\<open>fixes vars\<close> \\
    & & \quad\<^theory_text>\<open>assumes name: props\<close> \\
    & & \quad\<^theory_text>\<open>shows name: props "proof"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>theorem name:\<close> \\
    & & \quad\<^theory_text>\<open>fixes vars\<close> \\
    & & \quad\<^theory_text>\<open>assumes name: props\<close> \\
    & & \quad\<^theory_text>\<open>obtains (name) clause "\<^bold>|" \<dots> "proof"\<close> \\
    \<open>proof\<close> & \<open>=\<close> & \<^theory_text>\<open>"refinement\<^sup>* proper_proof"\<close> \\
    \<open>refinement\<close> & \<open>=\<close> &  \<^theory_text>\<open>apply method\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>supply name = thms\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>subgoal premises name for vars "proof"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>using thms\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>unfolding thms\<close> \\
    \<open>proper_proof\<close> & \<open>=\<close> & \<^theory_text>\<open>proof "method\<^sup>?" "statement\<^sup>*" qed "method\<^sup>?"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>by method method\<close>~~~\<open>|\<close>~~~\<^theory_text>\<open>..\<close>~~~\<open>|\<close>~~~\<^theory_text>\<open>.\<close>~~~\<open>|\<close>~~~\<^theory_text>\<open>sorry\<close>~~~\<open>|\<close>~~~\<^theory_text>\<open>done\<close> \\
    \<open>statement\<close> & \<open>=\<close> & \<^theory_text>\<open>{ "statement\<^sup>*" }\<close>~~~\<open>|\<close>~~~\<^theory_text>\<open>next\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>note name = thms\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>let "term" = "term"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>write name  (mixfix)\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>fix vars\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>assume name: props if props for vars\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>presume name: props if props for vars\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>define clause\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>case name: "case"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>then"\<^sup>?" goal\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>from thms goal\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>with thms goal\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>also\<close>~~~\<open>|\<close>~~~\<^theory_text>\<open>finally goal\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>moreover\<close>~~~\<open>|\<close>~~~\<^theory_text>\<open>ultimately goal\<close> \\
    \<open>goal\<close> & \<open>=\<close> & \<^theory_text>\<open>have name: props if name: props for vars "proof"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>show name: props if name: props for vars "proof"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>show name: props when name: props for vars "proof"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>consider (name) clause "\<^bold>|" \<dots> "proof"\<close> \\
    & \<open>|\<close> & \<^theory_text>\<open>obtain (name) clause "proof"\<close> \\
    \<open>clause\<close> & \<open>=\<close> & \<^theory_text>\<open>vars where name: props if props for vars\<close> \\
  \end{tabular}
  \end{center}
  \caption{Main grammar of the Isar proof language}\label{fig:isar-syntax}
  \end{figure}

  The construction of the Isar proof language proceeds in a bottom-up fashion,
  as an exercise in purity and minimalism. The grammar in
  \appref{ap:main-grammar} describes the primitive parts of the core language
  (category \<open>proof\<close>), which is embedded into the main outer theory syntax via
  elements that require a proof (e.g.\ \<^theory_text>\<open>theorem\<close>, \<^theory_text>\<open>lemma\<close>, \<^theory_text>\<open>function\<close>,
  \<^theory_text>\<open>termination\<close>).

  The syntax for terms and propositions is inherited from Pure (and the
  object-logic). A \<open>pattern\<close> is a \<open>term\<close> with schematic variables, to be bound
  by higher-order matching. Simultaneous propositions or facts may be
  separated by the \<^theory_text>\<open>and\<close> keyword.

  \<^medskip>
  Facts may be referenced by name or proposition. For example, the result of
  ``\<^theory_text>\<open>have a: A \<proof>\<close>'' becomes accessible both via the name \<open>a\<close> and the
  literal proposition \<open>\<open>A\<close>\<close>. Moreover, fact expressions may involve attributes
  that modify either the theorem or the background context. For example, the
  expression ``\<open>a [OF b]\<close>'' refers to the composition of two facts according
  to the @{inference resolution} inference of
  \secref{sec:framework-resolution}, while ``\<open>a [intro]\<close>'' declares a fact as
  introduction rule in the context.

  The special fact called ``@{fact this}'' always refers to the last result,
  as produced by \<^theory_text>\<open>note\<close>, \<^theory_text>\<open>assume\<close>, \<^theory_text>\<open>have\<close>, or \<^theory_text>\<open>show\<close>. Since \<^theory_text>\<open>note\<close> occurs
  frequently together with \<^theory_text>\<open>then\<close>, there are some abbreviations:

  \<^medskip>
  \begin{tabular}{rcl}
    \<^theory_text>\<open>from a\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>note a then\<close> \\
    \<^theory_text>\<open>with a\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>from a and this\<close> \\
  \end{tabular}
  \<^medskip>

  The \<open>method\<close> category is essentially a parameter of the Isar language and
  may be populated later. The command \<^theory_text>\<open>method_setup\<close> allows to define proof
  methods semantically in Isabelle/ML. The Eisbach language allows to define
  proof methods symbolically, as recursive expressions over existing methods
  @{cite "Matichuk-et-al:2014"}; see also \<^dir>\<open>~~/src/HOL/Eisbach\<close>.

  Methods use the facts indicated by \<^theory_text>\<open>then\<close> or \<^theory_text>\<open>using\<close>, and then operate on
  the goal state. Some basic methods are predefined in Pure: ``@{method "-"}''
  leaves the goal unchanged, ``@{method this}'' applies the facts as rules to
  the goal, ``@{method (Pure) "rule"}'' applies the facts to another rule and
  the result to the goal (both ``@{method this}'' and ``@{method (Pure)
  rule}'' refer to @{inference resolution} of
  \secref{sec:framework-resolution}). The secondary arguments to ``@{method
  (Pure) rule}'' may be specified explicitly as in ``\<open>(rule a)\<close>'', or picked
  from the context. In the latter case, the system first tries rules declared
  as @{attribute (Pure) elim} or @{attribute (Pure) dest}, followed by those
  declared as @{attribute (Pure) intro}.

  The default method for \<^theory_text>\<open>proof\<close> is ``@{method standard}'' (which subsumes
  @{method rule} with arguments picked from the context), for \<^theory_text>\<open>qed\<close> it is
  ``@{method "succeed"}''. Further abbreviations for terminal proof steps are
  ``\<^theory_text>\<open>by method\<^sub>1 method\<^sub>2\<close>'' for ``\<^theory_text>\<open>proof method\<^sub>1 qed method\<^sub>2\<close>'', and
  ``\<^theory_text>\<open>..\<close>'' for ``\<^theory_text>\<open>by standard\<close>, and ``\<^theory_text>\<open>.\<close>'' for ``\<^theory_text>\<open>by this\<close>''. The command
  ``\<^theory_text>\<open>unfolding facts\<close>'' operates directly on the goal by applying equalities.

  \<^medskip>
  Block structure can be indicated explicitly by ``\<^theory_text>\<open>{ \<dots> }\<close>'', although the
  body of a subproof ``\<^theory_text>\<open>proof \<dots> qed\<close>'' already provides implicit nesting. In
  both situations, \<^theory_text>\<open>next\<close> jumps into the next section of a block, i.e.\ it
  acts like closing an implicit block scope and opening another one. There is
  no direct connection to subgoals here!

  The commands \<^theory_text>\<open>fix\<close> and \<^theory_text>\<open>assume\<close> build up a local context (see
  \secref{sec:framework-context}), while \<^theory_text>\<open>show\<close> refines a pending subgoal by
  the rule resulting from a nested subproof (see
  \secref{sec:framework-subproof}). Further derived concepts will support
  calculational reasoning (see \secref{sec:framework-calc}).
\<close>


subsection \<open>Context elements \label{sec:framework-context}\<close>

text \<open>
  In judgments \<open>\<Gamma> \<turnstile> \<phi>\<close> of the primitive framework, \<open>\<Gamma>\<close> essentially acts like a
  proof context. Isar elaborates this idea towards a more advanced concept,
  with additional information for type-inference, term abbreviations, local
  facts, hypotheses etc.

  The element \<^theory_text>\<open>fix x :: \<alpha>\<close> declares a local parameter, i.e.\ an
  arbitrary-but-fixed entity of a given type; in results exported from the
  context, \<open>x\<close> may become anything. The \<^theory_text>\<open>assume \<guillemotleft>inference\<guillemotright>\<close> element provides
  a general interface to hypotheses: \<^theory_text>\<open>assume \<guillemotleft>inference\<guillemotright> A\<close> produces \<open>A \<turnstile> A\<close>
  locally, while the included inference tells how to discharge \<open>A\<close> from
  results \<open>A \<turnstile> B\<close> later on. There is no surface syntax for \<open>\<guillemotleft>inference\<guillemotright>\<close>,
  i.e.\ it may only occur internally when derived commands are defined in ML.

  The default inference for \<^theory_text>\<open>assume\<close> is @{inference export} as given below.
  The derived element \<^theory_text>\<open>define x where "x \<equiv> a"\<close> is defined as \<^theory_text>\<open>fix x assume
  \<guillemotleft>expand\<guillemotright> x \<equiv> a\<close>, with the subsequent inference @{inference expand}.

  \[
  \infer[(@{inference_def export})]{\<open>\<strut>\<Gamma> - A \<turnstile> A \<Longrightarrow> B\<close>}{\<open>\<strut>\<Gamma> \<turnstile> B\<close>}
  \qquad
  \infer[(@{inference_def expand})]{\<open>\<strut>\<Gamma> - (x \<equiv> a) \<turnstile> B a\<close>}{\<open>\<strut>\<Gamma> \<turnstile> B x\<close>}
  \]

  \<^medskip>
  The most interesting derived context element in Isar is \<^theory_text>\<open>obtain\<close> @{cite
  \<open>\S5.3\<close> "Wenzel-PhD"}, which supports generalized elimination steps in a
  purely forward manner. The \<^theory_text>\<open>obtain\<close> command takes a specification of
  parameters \<open>\<^vec>x\<close> and assumptions \<open>\<^vec>A\<close> to be added to the context,
  together with a proof of a case rule stating that this extension is
  conservative (i.e.\ may be removed from closed results later on):

  \<^medskip>
  \begin{tabular}{l}
  \<^theory_text>\<open>\<langle>facts\<rangle> obtain "\<^vec>x" where "\<^vec>A" "\<^vec>x" \<proof> \<equiv>\<close> \\[0.5ex]
  \quad \<^theory_text>\<open>have "case": "\<And>thesis. (\<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis) \<Longrightarrow> thesis"\<close> \\
  \quad \<^theory_text>\<open>proof -\<close> \\
  \qquad \<^theory_text>\<open>fix thesis\<close> \\
  \qquad \<^theory_text>\<open>assume [intro]: "\<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis"\<close> \\
  \qquad \<^theory_text>\<open>show thesis using \<langle>facts\<rangle> \<proof>\<close> \\
  \quad \<^theory_text>\<open>qed\<close> \\
  \quad \<^theory_text>\<open>fix "\<^vec>x" assume \<guillemotleft>elimination "case"\<guillemotright> "\<^vec>A \<^vec>x"\<close> \\
  \end{tabular}
  \<^medskip>

  \[
  \infer[(@{inference elimination})]{\<open>\<Gamma> \<turnstile> B\<close>}{
    \begin{tabular}{rl}
    \<open>case:\<close> &
    \<open>\<Gamma> \<turnstile> \<And>thesis. (\<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \\[0.2ex]
    \<open>result:\<close> &
    \<open>\<Gamma> \<union> \<^vec>A \<^vec>y \<turnstile> B\<close> \\[0.2ex]
    \end{tabular}}
  \]

  Here the name ``\<open>thesis\<close>'' is a specific convention for an
  arbitrary-but-fixed proposition; in the primitive natural deduction rules
  shown before we have occasionally used \<open>C\<close>. The whole statement of
  ``\<^theory_text>\<open>obtain x where A x\<close>'' can be read as a claim that \<open>A x\<close> may be assumed
  for some arbitrary-but-fixed \<open>x\<close>. Also note that ``\<^theory_text>\<open>obtain A and B\<close>''
  without parameters is similar to ``\<^theory_text>\<open>have A and B\<close>'', but the latter
  involves multiple subgoals that need to be proven separately.

  \<^medskip>
  The subsequent Isar proof texts explain all context elements introduced
  above using the formal proof language itself. After finishing a local proof
  within a block, the exported result is indicated via \<^theory_text>\<open>note\<close>.
\<close>

(*<*)
theorem True
proof
(*>*)
  text_raw \<open>\begin{minipage}[t]{0.45\textwidth}\<close>
  {
    fix x
    have "B x" \<proof>
  }
  note \<open>\<And>x. B x\<close>
  text_raw \<open>\end{minipage}\quad\begin{minipage}[t]{0.45\textwidth}\<close>(*<*)next(*>*)
  {
    assume A
    have B \<proof>
  }
  note \<open>A \<Longrightarrow> B\<close>
  text_raw \<open>\end{minipage}\\[3ex]\begin{minipage}[t]{0.45\textwidth}\<close>(*<*)next(*>*)
  {
    define x where "x \<equiv> a"
    have "B x" \<proof>
  }
  note \<open>B a\<close>
  text_raw \<open>\end{minipage}\quad\begin{minipage}[t]{0.45\textwidth}\<close>(*<*)next(*>*)
  {
    obtain x where "A x" \<proof>
    have B \<proof>
  }
  note \<open>B\<close>
  text_raw \<open>\end{minipage}\<close>
(*<*)
qed
(*>*)

text \<open>
  \<^bigskip>
  This explains the meaning of Isar context elements without, without goal
  states getting in the way.
\<close>


subsection \<open>Structured statements \label{sec:framework-stmt}\<close>

text \<open>
  The syntax of top-level theorem statements is defined as follows:

  \<^medskip>
  \begin{tabular}{rcl}
  \<open>statement\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>name: props and \<dots>\<close> \\
  & \<open>|\<close> & \<open>context\<^sup>* conclusion\<close> \\[0.5ex]

  \<open>context\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>fixes vars and \<dots>\<close> \\
  & \<open>|\<close> & \<^theory_text>\<open>assumes name: props and \<dots>\<close> \\

  \<open>conclusion\<close> & \<open>\<equiv>\<close> & \<^theory_text>\<open>shows name: props and \<dots>\<close> \\
  & \<open>|\<close> & \<^theory_text>\<open>obtains vars and \<dots> where name: props and \<dots>\<close> \\
  & & \quad \<open>\<BBAR> \<dots>\<close> \\
  \end{tabular}

  \<^medskip>
  A simple statement consists of named propositions. The full form admits
  local context elements followed by the actual conclusions, such as ``\<^theory_text>\<open>fixes
  x assumes A x shows B x\<close>''. The final result emerges as a Pure rule after
  discharging the context: @{prop "\<And>x. A x \<Longrightarrow> B x"}.

  The \<^theory_text>\<open>obtains\<close> variant is another abbreviation defined below; unlike
  \<^theory_text>\<open>obtain\<close> (cf.\ \secref{sec:framework-context}) there may be several
  ``cases'' separated by ``\<open>\<BBAR>\<close>'', each consisting of several parameters
  (\<open>vars\<close>) and several premises (\<open>props\<close>). This specifies multi-branch
  elimination rules.

  \<^medskip>
  \begin{tabular}{l}
  \<^theory_text>\<open>obtains "\<^vec>x" where "\<^vec>A" "\<^vec>x"  "\<BBAR>"  \<dots>  \<equiv>\<close> \\[0.5ex]
  \quad \<^theory_text>\<open>fixes thesis\<close> \\
  \quad \<^theory_text>\<open>assumes [intro]: "\<And>\<^vec>x. \<^vec>A \<^vec>x \<Longrightarrow> thesis"  and  \<dots>\<close> \\
  \quad \<^theory_text>\<open>shows thesis\<close> \\
  \end{tabular}
  \<^medskip>

  Presenting structured statements in such an ``open'' format usually
  simplifies the subsequent proof, because the outer structure of the problem
  is already laid out directly. E.g.\ consider the following canonical
  patterns for \<^theory_text>\<open>shows\<close> and \<^theory_text>\<open>obtains\<close>, respectively:
\<close>

text_raw \<open>\begin{minipage}{0.5\textwidth}\<close>

  theorem
    fixes x and y
    assumes "A x" and "B y"
    shows "C x y"
  proof -
    from \<open>A x\<close> and \<open>B y\<close>
    show "C x y" \<proof>
  qed

text_raw \<open>\end{minipage}\begin{minipage}{0.5\textwidth}\<close>

  theorem
    obtains x and y
    where "A x" and "B y"
  proof -
    have "A a" and "B b" \<proof>
    then show thesis ..
  qed

text_raw \<open>\end{minipage}\<close>

text \<open>
  \<^medskip>
  Here local facts \<open>\<open>A x\<close>\<close> and \<open>\<open>B y\<close>\<close> are referenced immediately; there is no
  need to decompose the logical rule structure again. In the second proof the
  final ``\<^theory_text>\<open>then show thesis ..\<close>'' involves the local rule case \<open>\<And>x y. A x \<Longrightarrow> B
  y \<Longrightarrow> thesis\<close> for the particular instance of terms \<open>a\<close> and \<open>b\<close> produced in the
  body.
\<close>


subsection \<open>Structured proof refinement \label{sec:framework-subproof}\<close>

text \<open>
  By breaking up the grammar for the Isar proof language, we may understand a
  proof text as a linear sequence of individual proof commands. These are
  interpreted as transitions of the Isar virtual machine (Isar/VM), which
  operates on a block-structured configuration in single steps. This allows
  users to write proof texts in an incremental manner, and inspect
  intermediate configurations for debugging.

  The basic idea is analogous to evaluating algebraic expressions on a stack
  machine: \<open>(a + b) \<cdot> c\<close> then corresponds to a sequence of single transitions
  for each symbol \<open>(, a, +, b, ), \<cdot>, c\<close>. In Isar the algebraic values are
  facts or goals, and the operations are inferences.

  \<^medskip>
  The Isar/VM state maintains a stack of nodes, each node contains the local
  proof context, the linguistic mode, and a pending goal (optional). The mode
  determines the type of transition that may be performed next, it essentially
  alternates between forward and backward reasoning, with an intermediate
  stage for chained facts (see \figref{fig:isar-vm}).

  \begin{figure}[htb]
  \begin{center}
  \includegraphics[width=0.8\textwidth]{isar-vm}
  \end{center}
  \caption{Isar/VM modes}\label{fig:isar-vm}
  \end{figure}

  For example, in \<open>state\<close> mode Isar acts like a mathematical scratch-pad,
  accepting declarations like \<^theory_text>\<open>fix\<close>, \<^theory_text>\<open>assume\<close>, and claims like \<^theory_text>\<open>have\<close>,
  \<^theory_text>\<open>show\<close>. A goal statement changes the mode to \<open>prove\<close>, which means that we
  may now refine the problem via \<^theory_text>\<open>unfolding\<close> or \<^theory_text>\<open>proof\<close>. Then we are again
  in \<open>state\<close> mode of a proof body, which may issue \<^theory_text>\<open>show\<close> statements to solve
  pending subgoals. A concluding \<^theory_text>\<open>qed\<close> will return to the original \<open>state\<close>
  mode one level upwards. The subsequent Isar/VM trace indicates block
  structure, linguistic mode, goal state, and inferences:
\<close>

text_raw \<open>\begingroup\footnotesize\<close>
(*<*)notepad begin
(*>*)
  text_raw \<open>\begin{minipage}[t]{0.18\textwidth}\<close>
  have "A \<longrightarrow> B"
  proof
    assume A
    show B
      \<proof>
  qed
  text_raw \<open>\end{minipage}\quad
\begin{minipage}[t]{0.06\textwidth}
\<open>begin\<close> \\
\\
\\
\<open>begin\<close> \\
\<open>end\<close> \\
\<open>end\<close> \\
\end{minipage}
\begin{minipage}[t]{0.08\textwidth}
\<open>prove\<close> \\
\<open>state\<close> \\
\<open>state\<close> \\
\<open>prove\<close> \\
\<open>state\<close> \\
\<open>state\<close> \\
\end{minipage}\begin{minipage}[t]{0.35\textwidth}
\<open>(A \<longrightarrow> B) \<Longrightarrow> #(A \<longrightarrow> B)\<close> \\
\<open>(A \<Longrightarrow> B) \<Longrightarrow> #(A \<longrightarrow> B)\<close> \\
\\
\\
\<open>#(A \<longrightarrow> B)\<close> \\
\<open>A \<longrightarrow> B\<close> \\
\end{minipage}\begin{minipage}[t]{0.4\textwidth}
\<open>(init)\<close> \\
\<open>(resolution impI)\<close> \\
\\
\\
\<open>(refinement #A \<Longrightarrow> B)\<close> \\
\<open>(finish)\<close> \\
\end{minipage}\<close>
(*<*)
end
(*>*)
text_raw \<open>\endgroup\<close>

text \<open>
  Here the @{inference refinement} inference from
  \secref{sec:framework-resolution} mediates composition of Isar subproofs
  nicely. Observe that this principle incorporates some degree of freedom in
  proof composition. In particular, the proof body allows parameters and
  assumptions to be re-ordered, or commuted according to Hereditary Harrop
  Form. Moreover, context elements that are not used in a subproof may be
  omitted altogether. For example:
\<close>

text_raw \<open>\begin{minipage}{0.5\textwidth}\<close>

(*<*)
notepad
begin
(*>*)
  have "\<And>x y. A x \<Longrightarrow> B y \<Longrightarrow> C x y"
  proof -
    fix x and y
    assume "A x" and "B y"
    show "C x y" \<proof>
  qed

text_raw \<open>\end{minipage}\begin{minipage}{0.5\textwidth}\<close>

(*<*)
next
(*>*)
  have "\<And>x y. A x \<Longrightarrow> B y \<Longrightarrow> C x y"
  proof -
    fix x assume "A x"
    fix y assume "B y"
    show "C x y" \<proof>
  qed

text_raw \<open>\end{minipage}\\[3ex]\begin{minipage}{0.5\textwidth}\<close>

(*<*)
next
(*>*)
  have "\<And>x y. A x \<Longrightarrow> B y \<Longrightarrow> C x y"
  proof -
    fix y assume "B y"
    fix x assume "A x"
    show "C x y" \<proof>
  qed

text_raw \<open>\end{minipage}\begin{minipage}{0.5\textwidth}\<close>
(*<*)
next
(*>*)
  have "\<And>x y. A x \<Longrightarrow> B y \<Longrightarrow> C x y"
  proof -
    fix y assume "B y"
    fix x
    show "C x y" \<proof>
  qed
(*<*)
end
(*>*)

text_raw \<open>\end{minipage}\<close>

text \<open>
  \<^medskip>
  Such fine-tuning of Isar text is practically important to improve
  readability. Contexts elements are rearranged according to the natural flow
  of reasoning in the body, while still observing the overall scoping rules.

  \<^medskip>
  This illustrates the basic idea of structured proof processing in Isar. The
  main mechanisms are based on natural deduction rule composition within the
  Pure framework. In particular, there are no direct operations on goal states
  within the proof body. Moreover, there is no hidden automated reasoning
  involved, just plain unification.
\<close>


subsection \<open>Calculational reasoning \label{sec:framework-calc}\<close>

text \<open>
  The existing Isar infrastructure is sufficiently flexible to support
  calculational reasoning (chains of transitivity steps) as derived concept.
  The generic proof elements introduced below depend on rules declared as
  @{attribute trans} in the context. It is left to the object-logic to provide
  a suitable rule collection for mixed relations of \<open>=\<close>, \<open><\<close>, \<open>\<le>\<close>, \<open>\<subset>\<close>, \<open>\<subseteq>\<close>
  etc. Due to the flexibility of rule composition
  (\secref{sec:framework-resolution}), substitution of equals by equals is
  covered as well, even substitution of inequalities involving monotonicity
  conditions; see also @{cite \<open>\S6\<close> "Wenzel-PhD"} and @{cite
  "Bauer-Wenzel:2001"}.

  The generic calculational mechanism is based on the observation that rules
  such as \<open>trans:\<close>~@{prop "x = y \<Longrightarrow> y = z \<Longrightarrow> x = z"} proceed from the premises
  towards the conclusion in a deterministic fashion. Thus we may reason in
  forward mode, feeding intermediate results into rules selected from the
  context. The course of reasoning is organized by maintaining a secondary
  fact called ``@{fact calculation}'', apart from the primary ``@{fact this}''
  already provided by the Isar primitives. In the definitions below,
  @{attribute OF} refers to @{inference resolution}
  (\secref{sec:framework-resolution}) with multiple rule arguments, and
  \<open>trans\<close> represents to a suitable rule from the context:

  \begin{matharray}{rcl}
    \<^theory_text>\<open>also"\<^sub>0"\<close> & \equiv & \<^theory_text>\<open>note calculation = this\<close> \\
    \<^theory_text>\<open>also"\<^sub>n\<^sub>+\<^sub>1"\<close> & \equiv & \<^theory_text>\<open>note calculation = trans [OF calculation this]\<close> \\[0.5ex]
    \<^theory_text>\<open>finally\<close> & \equiv & \<^theory_text>\<open>also from calculation\<close> \\
  \end{matharray}

  The start of a calculation is determined implicitly in the text: here
  \<^theory_text>\<open>also\<close> sets @{fact calculation} to the current result; any subsequent
  occurrence will update @{fact calculation} by combination with the next
  result and a transitivity rule. The calculational sequence is concluded via
  \<^theory_text>\<open>finally\<close>, where the final result is exposed for use in a concluding claim.

  Here is a canonical proof pattern, using \<^theory_text>\<open>have\<close> to establish the
  intermediate results:
\<close>

(*<*)
notepad
begin
  fix a b c d :: 'a
(*>*)
  have "a = b" \<proof>
  also have "\<dots> = c" \<proof>
  also have "\<dots> = d" \<proof>
  finally have "a = d" .
(*<*)
end
(*>*)

text \<open>
  The term ``\<open>\<dots>\<close>'' (literal ellipsis) is a special abbreviation provided by
  the Isabelle/Isar term syntax: it statically refers to the right-hand side
  argument of the previous statement given in the text. Thus it happens to
  coincide with relevant sub-expressions in the calculational chain, but the
  exact correspondence is dependent on the transitivity rules being involved.

  \<^medskip>
  Symmetry rules such as @{prop "x = y \<Longrightarrow> y = x"} are like transitivities with
  only one premise. Isar maintains a separate rule collection declared via the
  @{attribute sym} attribute, to be used in fact expressions ``\<open>a
  [symmetric]\<close>'', or single-step proofs ``\<^theory_text>\<open>assume "x = y" then have "y = x"
  ..\<close>''.
\<close>

end
