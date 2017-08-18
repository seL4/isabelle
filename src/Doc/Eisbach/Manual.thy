(*:maxLineLen=78:*)

theory Manual
imports Base "HOL-Eisbach.Eisbach_Tools"
begin

chapter \<open>The method command\<close>

text \<open>
  The @{command_def method} command provides the ability to write proof
  methods by combining existing ones with their usual syntax. Specifically it
  allows compound proof methods to be named, and to extend the name space of
  basic methods accordingly. Method definitions may abstract over parameters:
  terms, facts, or other methods.

  \<^medskip>
  The syntax diagram below refers to some syntactic categories that are
  further defined in @{cite "isabelle-isar-ref"}.

  @{rail \<open>
    @@{command method} name args @'=' method
    ;
    args: term_args? method_args? \<newline> fact_args? decl_args?
    ;
    term_args: @'for' @{syntax "fixes"}
    ;
    method_args: @'methods' (name+)
    ;
    fact_args: @'uses' (name+)
    ;
    decl_args: @'declares' (name+)
  \<close>}
\<close>


section \<open>Basic method definitions\<close>

text \<open>
  Consider the following proof that makes use of usual Isar method
  combinators.
\<close>

    lemma "P \<and> Q \<longrightarrow> P"
      by ((rule impI, (erule conjE)?) | assumption)+

text \<open>
  It is clear that this compound method will be applicable in more cases than
  this proof alone. With the @{command method} command we can define a proof
  method that makes the above functionality available generally.
\<close>

    method prop_solver\<^sub>1 =
      ((rule impI, (erule conjE)?) | assumption)+

    lemma "P \<and> Q \<and> R \<longrightarrow> P"
      by prop_solver\<^sub>1

text \<open>
  In this example, the facts \<open>impI\<close> and \<open>conjE\<close> are static. They are evaluated
  once when the method is defined and cannot be changed later. This makes the
  method stable in the sense of \<^emph>\<open>static scoping\<close>: naming another fact \<open>impI\<close>
  in a later context won't affect the behaviour of \<open>prop_solver\<^sub>1\<close>.
\<close>


section \<open>Term abstraction\<close>

text \<open>
  Methods can also abstract over terms using the @{keyword_def "for"} keyword,
  optionally providing type constraints. For instance, the following proof
  method \<open>intro_ex\<close> takes a term @{term y} of any type, which it uses to
  instantiate the @{term x}-variable of \<open>exI\<close> (existential introduction)
  before applying the result as a rule. The instantiation is performed here by
  Isar's @{attribute_ref "where"} attribute. If the current subgoal is to find
  a witness for the given predicate @{term Q}, then this has the effect of
  committing to @{term y}.
\<close>

    method intro_ex for Q :: "'a \<Rightarrow> bool" and y :: 'a =
      (rule exI ["where" P = Q and x = y])


text \<open>
  The term parameters @{term y} and @{term Q} can be used arbitrarily inside
  the method body, as part of attribute applications or arguments to other
  methods. The expression is type-checked as far as possible when the method
  is defined, however dynamic type errors can still occur when it is invoked
  (e.g.\ when terms are instantiated in a parameterized fact). Actual term
  arguments are supplied positionally, in the same order as in the method
  definition.
\<close>

    lemma "P a \<Longrightarrow> \<exists>x. P x"
      by (intro_ex P a)


section \<open>Fact abstraction\<close>

subsection \<open>Named theorems\<close>

text \<open>
  A \<^emph>\<open>named theorem\<close> is a fact whose contents are produced dynamically within
  the current proof context. The Isar command @{command_ref "named_theorems"}
  provides simple access to this concept: it declares a dynamic fact with
  corresponding \<^emph>\<open>attribute\<close> for managing this particular data slot in the
  context.
\<close>

    named_theorems intros

text \<open>
  So far \<open>intros\<close> refers to the empty fact. Using the Isar command
  @{command_ref "declare"} we may apply declaration attributes to the context.
  Below we declare both \<open>conjI\<close> and \<open>impI\<close> as \<open>intros\<close>, adding them to the
  named theorem slot.
\<close>

    declare conjI [intros] and impI [intros]

text \<open>
  We can refer to named theorems as dynamic facts within a particular proof
  context, which are evaluated whenever the method is invoked. Instead of
  having facts hard-coded into the method, as in \<open>prop_solver\<^sub>1\<close>, we can
  instead refer to these named theorems.
\<close>

    named_theorems elims
    declare conjE [elims]

    method prop_solver\<^sub>3 =
      ((rule intros, (erule elims)?) | assumption)+

    lemma "P \<and> Q \<longrightarrow> P"
      by prop_solver\<^sub>3

text \<open>
  Often these named theorems need to be augmented on the spot, when a method
  is invoked. The @{keyword_def "declares"} keyword in the signature of
  @{command method} adds the common method syntax \<open>method decl: facts\<close> for
  each named theorem \<open>decl\<close>.
\<close>

    method prop_solver\<^sub>4 declares intros elims =
      ((rule intros, (erule elims)?) | assumption)+

    lemma "P \<and> (P \<longrightarrow> Q) \<longrightarrow> Q \<and> P"
      by (prop_solver\<^sub>4 elims: impE intros: conjI)


subsection \<open>Simple fact abstraction\<close>

text \<open>
  The @{keyword "declares"} keyword requires that a corresponding dynamic fact
  has been declared with @{command_ref named_theorems}. This is useful for
  managing collections of facts which are to be augmented with declarations,
  but is overkill if we simply want to pass a fact to a method.

  We may use the @{keyword_def "uses"} keyword in the method header to provide
  a simple fact parameter. In contrast to @{keyword "declares"}, these facts
  are always implicitly empty unless augmented when the method is invoked.
\<close>

    method rule_twice uses my_rule =
      (rule my_rule, rule my_rule)

    lemma "P \<Longrightarrow> Q \<Longrightarrow> (P \<and> Q) \<and> Q"
      by (rule_twice my_rule: conjI)


section \<open>Higher-order methods\<close>

text \<open>
  The \<^emph>\<open>structured concatenation\<close> combinator ``\<open>method\<^sub>1 ; method\<^sub>2\<close>'' was
  introduced in Isabelle2015, motivated by development of Eisbach. It is
  similar to ``\<open>method\<^sub>1, method\<^sub>2\<close>'', but \<open>method\<^sub>2\<close> is invoked on on \<^emph>\<open>all\<close>
  subgoals that have newly emerged from \<open>method\<^sub>1\<close>. This is useful to handle
  cases where the number of subgoals produced by a method is determined
  dynamically at run-time.
\<close>

    method conj_with uses rule =
      (intro conjI ; intro rule)

    lemma
      assumes A: "P"
      shows "P \<and> P \<and> P"
      by (conj_with rule: A)

text \<open>
  Method definitions may take other methods as arguments, and thus implement
  method combinators with prefix syntax. For example, to more usefully exploit
  Isabelle's backtracking, the explicit requirement that a method solve all
  produced subgoals is frequently useful. This can easily be written as a
  \<^emph>\<open>higher-order method\<close> using ``\<open>;\<close>''. The @{keyword "methods"} keyword
  denotes method parameters that are other proof methods to be invoked by the
  method being defined.
\<close>

    method solve methods m = (m ; fail)

text \<open>
  Given some method-argument \<open>m\<close>, \<open>solve \<open>m\<close>\<close> applies the method \<open>m\<close> and then
  fails whenever \<open>m\<close> produces any new unsolved subgoals --- i.e. when \<open>m\<close>
  fails to completely discharge the goal it was applied to.
\<close>


section \<open>Example\<close>

text \<open>
  With these simple features we are ready to write our first non-trivial proof
  method. Returning to the first-order logic example, the following method
  definition applies various rules with their canonical methods.
\<close>

    named_theorems subst

    method prop_solver declares intros elims subst =
      (assumption |
        (rule intros) | erule elims |
        subst subst | subst (asm) subst |
        (erule notE ; solve \<open>prop_solver\<close>))+

text \<open>
  The only non-trivial part above is the final alternative \<open>(erule notE ;
  solve \<open>prop_solver\<close>)\<close>. Here, in the case that all other alternatives fail,
  the method takes one of the assumptions @{term "\<not> P"} of the current goal
  and eliminates it with the rule \<open>notE\<close>, causing the goal to be proved to
  become @{term P}. The method then recursively invokes itself on the
  remaining goals. The job of the recursive call is to demonstrate that there
  is a contradiction in the original assumptions (i.e.\ that @{term P} can be
  derived from them). Note this recursive invocation is applied with the
  @{method solve} method combinator to ensure that a contradiction will indeed
  be shown. In the case where a contradiction cannot be found, backtracking
  will occur and a different assumption @{term "\<not> Q"} will be chosen for
  elimination.

  Note that the recursive call to @{method prop_solver} does not have any
  parameters passed to it. Recall that fact parameters, e.g.\ \<open>intros\<close>,
  \<open>elims\<close>, and \<open>subst\<close>, are managed by declarations in the current proof
  context. They will therefore be passed to any recursive call to @{method
  prop_solver} and, more generally, any invocation of a method which declares
  these named theorems.

  \<^medskip>
  After declaring some standard rules to the context, the @{method
  prop_solver} becomes capable of solving non-trivial propositional
  tautologies.
\<close>

    lemmas [intros] =
      conjI  \<comment>  \<open>@{thm conjI}\<close>
      impI  \<comment>  \<open>@{thm impI}\<close>
      disjCI  \<comment>  \<open>@{thm disjCI}\<close>
      iffI  \<comment>  \<open>@{thm iffI}\<close>
      notI  \<comment>  \<open>@{thm notI}\<close>

    lemmas [elims] =
      impCE  \<comment>  \<open>@{thm impCE}\<close>
      conjE  \<comment>  \<open>@{thm conjE}\<close>
      disjE  \<comment>  \<open>@{thm disjE}\<close>

    lemma "(A \<or> B) \<and> (A \<longrightarrow> C) \<and> (B \<longrightarrow> C) \<longrightarrow> C"
      by prop_solver


chapter \<open>The match method \label{s:matching}\<close>

text \<open>
  So far we have seen methods defined as simple combinations of other methods.
  Some familiar programming language concepts have been introduced (i.e.\
  abstraction and recursion). The only control flow has been implicitly the
  result of backtracking. When designing more sophisticated proof methods this
  proves too restrictive and difficult to manage conceptually.

  To address this, we introduce the @{method_def match} method, which provides
  more direct access to the higher-order matching facility at the core of
  Isabelle. It is implemented as a separate proof method (in Isabelle/ML), and
  thus can be directly applied to proofs, however it is most useful when
  applied in the context of writing Eisbach method definitions.

  \<^medskip>
  The syntax diagram below refers to some syntactic categories that are
  further defined in @{cite "isabelle-isar-ref"}.

  @{rail \<open>
    @@{method match} kind @'in' (pattern '\<Rightarrow>' @{syntax text} + '\<bar>')
    ;
    kind:
      (@'conclusion' | @'premises' ('(' 'local' ')')? |
       '(' term ')' | @{syntax thms})
    ;
    pattern: fact_name? term args? \<newline> (@'for' fixes)?
    ;
    fact_name: @{syntax name} @{syntax attributes}? ':'
    ;
    args: '(' (('multi' | 'cut' nat?) + ',') ')'
  \<close>}

  Matching allows methods to introspect the goal state, and to implement more
  explicit control flow. In the basic case, a term or fact \<open>ts\<close> is given to
  match against as a \<^emph>\<open>match target\<close>, along with a collection of
  pattern-method pairs \<open>(p, m)\<close>: roughly speaking, when the pattern \<open>p\<close>
  matches any member of \<open>ts\<close>, the \<^emph>\<open>inner\<close> method \<open>m\<close> will be executed.
\<close>

    lemma
      assumes X:
        "Q \<longrightarrow> P"
        "Q"
      shows P
        by (match X in I: "Q \<longrightarrow> P" and I': "Q" \<Rightarrow> \<open>insert mp [OF I I']\<close>)

text \<open>
  In this example we have a structured Isar proof, with the named assumption
  \<open>X\<close> and a conclusion @{term "P"}. With the match method we can find the
  local facts @{term "Q \<longrightarrow> P"} and @{term "Q"}, binding them to separately as
  \<open>I\<close> and \<open>I'\<close>. We then specialize the modus-ponens rule @{thm mp [of Q P]} to
  these facts to solve the goal.
\<close>


section \<open>Subgoal focus\<close>

text\<open>
  In the previous example we were able to match against an assumption out of
  the Isar proof state. In general, however, proof subgoals can be
  \<^emph>\<open>unstructured\<close>, with goal parameters and premises arising from rule
  application. To address this, @{method match} uses \<^emph>\<open>subgoal focusing\<close> to
  produce structured goals out of unstructured ones. In place of fact or term,
  we may give the keyword @{keyword_def "premises"} as the match target. This
  causes a subgoal focus on the first subgoal, lifting local goal parameters
  to fixed term variables and premises into hypothetical theorems. The match
  is performed against these theorems, naming them and binding them as
  appropriate. Similarly giving the keyword @{keyword_def "conclusion"}
  matches against the conclusion of the first subgoal.

  An unstructured version of the previous example can then be similarly solved
  through focusing.
\<close>

    lemma "Q \<longrightarrow> P \<Longrightarrow> Q \<Longrightarrow> P"
      by (match premises in
                I: "Q \<longrightarrow> P" and I': "Q" \<Rightarrow> \<open>insert mp [OF I I']\<close>)

text \<open>
  Match variables may be specified by giving a list of @{keyword_ref
  "for"}-fixes after the pattern description. This marks those terms as bound
  variables, which may be used in the method body.
\<close>

    lemma "Q \<longrightarrow> P \<Longrightarrow> Q \<Longrightarrow> P"
      by (match premises in I: "Q \<longrightarrow> A" and I': "Q" for A \<Rightarrow>
            \<open>match conclusion in A \<Rightarrow> \<open>insert mp [OF I I']\<close>\<close>)

text \<open>
  In this example @{term A} is a match variable which is bound to @{term P}
  upon a successful match. The inner @{method match} then matches the
  now-bound @{term A} (bound to @{term P}) against the conclusion (also @{term
  P}), finally applying the specialized rule to solve the goal.

  Schematic terms like \<open>?P\<close> may also be used to specify match variables, but
  the result of the match is not bound, and thus cannot be used in the inner
  method body.

  \<^medskip>
  In the following example we extract the predicate of an existentially
  quantified conclusion in the current subgoal and search the current premises
  for a matching fact. If both matches are successful, we then instantiate the
  existential introduction rule with both the witness and predicate, solving
  with the matched premise.
\<close>

    method solve_ex =
      (match conclusion in "\<exists>x. Q x" for Q \<Rightarrow>
        \<open>match premises in U: "Q y" for y \<Rightarrow>
          \<open>rule exI [where P = Q and x = y, OF U]\<close>\<close>)

text \<open>
  The first @{method match} matches the pattern @{term "\<exists>x. Q x"} against the
  current conclusion, binding the term @{term "Q"} in the inner match. Next
  the pattern \<open>Q y\<close> is matched against all premises of the current subgoal. In
  this case @{term "Q"} is fixed and @{term "y"} may be instantiated. Once a
  match is found, the local fact \<open>U\<close> is bound to the matching premise and the
  variable @{term "y"} is bound to the matching witness. The existential
  introduction rule \<open>exI:\<close>~@{thm exI} is then instantiated with @{term "y"} as
  the witness and @{term "Q"} as the predicate, with its proof obligation
  solved by the local fact U (using the Isar attribute @{attribute OF}). The
  following example is a trivial use of this method.
\<close>

    lemma "halts p \<Longrightarrow> \<exists>x. halts x"
      by solve_ex


subsection \<open>Operating within a focus\<close>

text \<open>
  Subgoal focusing provides a structured form of a subgoal, allowing for more
  expressive introspection of the goal state. This requires some consideration
  in order to be used effectively. When the keyword @{keyword "premises"} is
  given as the match target, the premises of the subgoal are lifted into
  hypothetical theorems, which can be found and named via match patterns.
  Additionally these premises are stripped from the subgoal, leaving only the
  conclusion. This renders them inaccessible to standard proof methods which
  operate on the premises, such as @{method frule} or @{method erule}. Naive
  usage of these methods within a match will most likely not function as the
  method author intended.
\<close>

    method my_allE_bad for y :: 'a =
      (match premises in I: "\<forall>x :: 'a. ?Q x" \<Rightarrow>
        \<open>erule allE [where x = y]\<close>)

text \<open>
  Here we take a single parameter @{term y} and specialize the universal
  elimination rule (@{thm allE}) to it, then attempt to apply this specialized
  rule with @{method erule}. The method @{method erule} will attempt to unify
  with a universal quantifier in the premises that matches the type of @{term
  y}. Since @{keyword "premises"} causes a focus, however, there are no
  subgoal premises to be found and thus @{method my_allE_bad} will always
  fail. If focusing instead left the premises in place, using methods like
  @{method erule} would lead to unintended behaviour, specifically during
  backtracking. In our example, @{method erule} could choose an alternate
  premise while backtracking, while leaving \<open>I\<close> bound to the original match.
  In the case of more complex inner methods, where either \<open>I\<close> or bound terms
  are used, this would almost certainly not be the intended behaviour.

  An alternative implementation would be to specialize the elimination rule to
  the bound term and apply it directly.
\<close>

    method my_allE_almost for y :: 'a =
      (match premises in I: "\<forall>x :: 'a. ?Q x" \<Rightarrow>
        \<open>rule allE [where x = y, OF I]\<close>)

    lemma "\<forall>x. P x \<Longrightarrow> P y"
      by (my_allE_almost y)

text \<open>
  This method will insert a specialized duplicate of a universally quantified
  premise. Although this will successfully apply in the presence of such a
  premise, it is not likely the intended behaviour. Repeated application of
  this method will produce an infinite stream of duplicate specialized
  premises, due to the original premise never being removed. To address this,
  matched premises may be declared with the @{attribute thin} attribute. This
  will hide the premise from subsequent inner matches, and remove it from the
  list of premises when the inner method has finished and the subgoal is
  unfocused. It can be considered analogous to the existing \<open>thin_tac\<close>.

  To complete our example, the correct implementation of the method will
  @{attribute thin} the premise from the match and then apply it to the
  specialized elimination rule.\<close>

    method my_allE for y :: 'a =
      (match premises in I [thin]: "\<forall>x :: 'a. ?Q x" \<Rightarrow>
         \<open>rule allE [where x = y, OF I]\<close>)

    lemma "\<forall>x. P x \<Longrightarrow> \<forall>x. Q x \<Longrightarrow> P y \<and> Q y"
      by (my_allE y)+ (rule conjI)


subsubsection \<open>Inner focusing\<close>

text \<open>
  Premises are \<^emph>\<open>accumulated\<close> for the purposes of subgoal focusing. In
  contrast to using standard methods like @{method frule} within focused
  match, another @{method match} will have access to all the premises of the
  outer focus.
\<close>

    lemma "A \<Longrightarrow> B \<Longrightarrow> A \<and> B"
      by (match premises in H: A \<Rightarrow> \<open>intro conjI, rule H,
            match premises in H': B \<Rightarrow> \<open>rule H'\<close>\<close>)

text \<open>
  In this example, the inner @{method match} can find the focused premise
  @{term B}. In contrast, the @{method assumption} method would fail here due
  to @{term B} not being logically accessible.
\<close>

    lemma "A \<Longrightarrow> A \<and> (B \<longrightarrow> B)"
      by (match premises in H: A \<Rightarrow> \<open>intro conjI, rule H, rule impI,
            match premises (local) in A \<Rightarrow> \<open>fail\<close>
                                 \<bar> H': B \<Rightarrow> \<open>rule H'\<close>\<close>)

text \<open>
  In this example, the only premise that exists in the first focus is @{term
  "A"}. Prior to the inner match, the rule \<open>impI\<close> changes the goal @{term "B \<longrightarrow>
  B"} into @{term "B \<Longrightarrow> B"}. A standard premise match would also include @{term
  A} as an original premise of the outer match. The \<open>local\<close> argument limits
  the match to newly focused premises.
\<close>


section \<open>Attributes\<close>

text \<open>
  Attributes may throw errors when applied to a given fact. For example, rule
  instantiation will fail of there is a type mismatch or if a given variable
  doesn't exist. Within a match or a method definition, it isn't generally
  possible to guarantee that applied attributes won't fail. For example, in
  the following method there is no guarantee that the two provided facts will
  necessarily compose.
\<close>

    method my_compose uses rule1 rule2 =
      (rule rule1 [OF rule2])

text \<open>
  Some attributes (like @{attribute OF}) have been made partially
  Eisbach-aware. This means that they are able to form a closure despite not
  necessarily always being applicable. In the case of @{attribute OF}, it is
  up to the proof author to guard attribute application with an appropriate
  @{method match}, but there are still no static guarantees.

  In contrast to @{attribute OF}, the @{attribute "where"} and @{attribute of}
  attributes attempt to provide static guarantees that they will apply
  whenever possible.

  Within a match pattern for a fact, each outermost quantifier specifies the
  requirement that a matching fact must have a schematic variable at that
  point. This gives a corresponding name to this ``slot'' for the purposes of
  forming a static closure, allowing the @{attribute "where"} attribute to
  perform an instantiation at run-time.
\<close>

    lemma
      assumes A: "Q \<Longrightarrow> False"
      shows "\<not> Q"
      by (match intros in X: "\<And>P. (P \<Longrightarrow> False) \<Longrightarrow> \<not> P" \<Rightarrow>
            \<open>rule X [where P = Q, OF A]\<close>)

text \<open>
  Subgoal focusing converts the outermost quantifiers of premises into
  schematics when lifting them to hypothetical facts. This allows us to
  instantiate them with @{attribute "where"} when using an appropriate match
  pattern.
\<close>

    lemma "(\<And>x :: 'a. A x \<Longrightarrow> B x) \<Longrightarrow> A y \<Longrightarrow> B y"
      by (match premises in I: "\<And>x :: 'a. ?P x \<Longrightarrow> ?Q x" \<Rightarrow>
            \<open>rule I [where x = y]\<close>)

text \<open>
  The @{attribute of} attribute behaves similarly. It is worth noting,
  however, that the positional instantiation of @{attribute of} occurs against
  the position of the variables as they are declared \<^emph>\<open>in the match pattern\<close>.
\<close>

    lemma
      fixes A B and x :: 'a and y :: 'b
      assumes asm: "(\<And>x y. A y x \<Longrightarrow> B x y )"
      shows "A y x \<Longrightarrow> B x y"
      by (match asm in I: "\<And>(x :: 'a) (y :: 'b). ?P x y \<Longrightarrow> ?Q x y" \<Rightarrow>
            \<open>rule I [of x y]\<close>)

text \<open>
  In this example, the order of schematics in \<open>asm\<close> is actually \<open>?y ?x\<close>, but
  we instantiate our matched rule in the opposite order. This is because the
  effective rule @{term I} was bound from the match, which declared the @{typ
  'a} slot first and the @{typ 'b} slot second.

  To get the dynamic behaviour of @{attribute of} we can choose to invoke it
  \<^emph>\<open>unchecked\<close>. This avoids trying to do any type inference for the provided
  parameters, instead storing them as their most general type and doing type
  matching at run-time. This, like @{attribute OF}, will throw errors if the
  expected slots don't exist or there is a type mismatch.
\<close>

    lemma
      fixes A B and x :: 'a and y :: 'b
      assumes asm: "\<And>x y. A y x \<Longrightarrow> B x y"
      shows "A y x \<Longrightarrow> B x y"
      by (match asm in I: "PROP ?P" \<Rightarrow> \<open>rule I [of (unchecked) y x]\<close>)

text \<open>
  Attributes may be applied to matched facts directly as they are matched. Any
  declarations will therefore be applied in the context of the inner method,
  as well as any transformations to the rule.
\<close>

    lemma "(\<And>x :: 'a. A x \<Longrightarrow> B x) \<Longrightarrow> A y \<longrightarrow> B y"
      by (match premises in I [of y, intros]: "\<And>x :: 'a. ?P x \<Longrightarrow> ?Q x" \<Rightarrow>
            \<open>prop_solver\<close>)

text \<open>
  In this example, the pattern \<open>\<And>x :: 'a. ?P x \<Longrightarrow> ?Q x\<close> matches against the
  only premise, giving an appropriately typed slot for @{term y}. After the
  match, the resulting rule is instantiated to @{term y} and then declared as
  an @{attribute intros} rule. This is then picked up by @{method prop_solver}
  to solve the goal.
\<close>


section \<open>Multi-match \label{sec:multi}\<close>

text \<open>
  In all previous examples, @{method match} was only ever searching for a
  single rule or premise. Each local fact would therefore always have a length
  of exactly one. We may, however, wish to find \<^emph>\<open>all\<close> matching results. To
  achieve this, we can simply mark a given pattern with the \<open>(multi)\<close>
  argument.
\<close>

    lemma
      assumes asms: "A \<Longrightarrow> B"  "A \<Longrightarrow> D"
      shows "(A \<longrightarrow> B) \<and> (A \<longrightarrow> D)"
      apply (match asms in I [intros]: "?P \<Longrightarrow> ?Q"  \<Rightarrow> \<open>solves \<open>prop_solver\<close>\<close>)?
      apply (match asms in I [intros]: "?P \<Longrightarrow> ?Q" (multi) \<Rightarrow> \<open>prop_solver\<close>)
      done

text \<open>
  In the first @{method match}, without the \<open>(multi)\<close> argument, @{term I} is
  only ever be bound to one of the members of \<open>asms\<close>. This backtracks over
  both possibilities (see next section), however neither assumption in
  isolation is sufficient to solve to goal. The use of the @{method solves}
  combinator ensures that @{method prop_solver} has no effect on the goal when
  it doesn't solve it, and so the first match leaves the goal unchanged. In
  the second @{method match}, \<open>I\<close> is bound to all of \<open>asms\<close>, declaring both
  results as \<open>intros\<close>. With these rules @{method prop_solver} is capable of
  solving the goal.

  Using for-fixed variables in patterns imposes additional constraints on the
  results. In all previous examples, the choice of using \<open>?P\<close> or a for-fixed
  @{term P} only depended on whether or not @{term P} was mentioned in another
  pattern or the inner method. When using a multi-match, however, all
  for-fixed terms must agree in the results.
\<close>

    lemma
      assumes asms: "A \<Longrightarrow> B"  "A \<Longrightarrow> D"  "D \<Longrightarrow> B"
      shows "(A \<longrightarrow> B) \<and> (A \<longrightarrow> D)"
      apply (match asms in I [intros]: "?P \<Longrightarrow> Q" (multi) for Q \<Rightarrow>
              \<open>solves \<open>prop_solver\<close>\<close>)?
      apply (match asms in I [intros]: "P \<Longrightarrow> ?Q" (multi) for P \<Rightarrow>
              \<open>prop_solver\<close>)
      done

text \<open>
  Here we have two seemingly-equivalent applications of @{method match},
  however only the second one is capable of solving the goal. The first
  @{method match} selects the first and third members of \<open>asms\<close> (those that
  agree on their conclusion), which is not sufficient. The second @{method
  match} selects the first and second members of \<open>asms\<close> (those that agree on
  their assumption), which is enough for @{method prop_solver} to solve the
  goal.
\<close>


section \<open>Dummy patterns\<close>

text \<open>
  Dummy patterns may be given as placeholders for unique schematics in
  patterns. They implicitly receive all currently bound variables as
  arguments, and are coerced into the @{typ prop} type whenever possible. For
  example, the trivial dummy pattern \<open>_\<close> will match any proposition. In
  contrast, by default the pattern \<open>?P\<close> is considered to have type @{typ
  bool}. It will not bind anything with meta-logical connectives (e.g. \<open>_ \<Longrightarrow> _\<close>
  or \<open>_ &&& _\<close>).
\<close>

    lemma
      assumes asms: "A &&& B \<Longrightarrow> D"
      shows "(A \<and> B \<longrightarrow> D)"
      by (match asms in I: _ \<Rightarrow> \<open>prop_solver intros: I conjunctionI\<close>)


section \<open>Backtracking\<close>

text \<open>
  Patterns are considered top-down, executing the inner method \<open>m\<close> of the
  first pattern which is satisfied by the current match target. By default,
  matching performs extensive backtracking by attempting all valid variable
  and fact bindings according to the given pattern. In particular, all
  unifiers for a given pattern will be explored, as well as each matching
  fact. The inner method \<open>m\<close> will be re-executed for each different
  variable/fact binding during backtracking. A successful match is considered
  a cut-point for backtracking. Specifically, once a match is made no other
  pattern-method pairs will be considered.

  The method \<open>foo\<close> below fails for all goals that are conjunctions. Any such
  goal will match the first pattern, causing the second pattern (that would
  otherwise match all goals) to never be considered.
\<close>

    method foo =
      (match conclusion in "?P \<and> ?Q" \<Rightarrow> \<open>fail\<close> \<bar> "?R" \<Rightarrow> \<open>prop_solver\<close>)

text \<open>
  The failure of an inner method that is executed after a successful match
  will cause the entire match to fail. This distinction is important due to
  the pervasive use of backtracking. When a method is used in a combinator
  chain, its failure becomes significant because it signals previously applied
  methods to move to the next result. Therefore, it is necessary for @{method
  match} to not mask such failure. One can always rewrite a match using the
  combinators ``\<open>?\<close>'' and ``\<open>|\<close>'' to try subsequent patterns in the case of an
  inner-method failure. The following proof method, for example, always
  invokes @{method prop_solver} for all goals because its first alternative
  either never matches or (if it does match) always fails.
\<close>

    method foo\<^sub>1 =
      (match conclusion in "?P \<and> ?Q" \<Rightarrow> \<open>fail\<close>) |
      (match conclusion in "?R" \<Rightarrow> \<open>prop_solver\<close>)


subsection \<open>Cut\<close>

text \<open>
  Backtracking may be controlled more precisely by marking individual patterns
  as \<open>cut\<close>. This causes backtracking to not progress beyond this pattern: once
  a match is found no others will be considered.
\<close>

    method foo\<^sub>2 =
      (match premises in I: "P \<and> Q" (cut) and I': "P \<longrightarrow> ?U" for P Q \<Rightarrow>
        \<open>rule mp [OF I' I [THEN conjunct1]]\<close>)

text \<open>
  In this example, once a conjunction is found (@{term "P \<and> Q"}), all possible
  implications of @{term "P"} in the premises are considered, evaluating the
  inner @{method rule} with each consequent. No other conjunctions will be
  considered, with method failure occurring once all implications of the form
  \<open>P \<longrightarrow> ?U\<close> have been explored. Here the left-right processing of individual
  patterns is important, as all patterns after of the cut will maintain their
  usual backtracking behaviour.
\<close>

    lemma "A \<and> B \<Longrightarrow> A \<longrightarrow> D \<Longrightarrow> A \<longrightarrow> C \<Longrightarrow> C"
      by foo\<^sub>2

    lemma "C \<and> D \<Longrightarrow> A \<and> B \<Longrightarrow> A \<longrightarrow> C  \<Longrightarrow> C"
      by (foo\<^sub>2 | prop_solver)

text \<open>
  In this example, the first lemma is solved by \<open>foo\<^sub>2\<close>, by first picking
  @{term "A \<longrightarrow> D"} for \<open>I'\<close>, then backtracking and ultimately succeeding after
  picking @{term "A \<longrightarrow> C"}. In the second lemma, however, @{term "C \<and> D"} is
  matched first, the second pattern in the match cannot be found and so the
  method fails, falling through to @{method prop_solver}.

  More precise control is also possible by giving a positive number \<open>n\<close> as an
  argument to \<open>cut\<close>. This will limit the number of backtracking results of
  that match to be at most \<open>n\<close>. The match argument \<open>(cut 1)\<close> is the same as
  simply \<open>(cut)\<close>.
\<close>


subsection \<open>Multi-match revisited\<close>

text \<open>
  A multi-match will produce a sequence of potential bindings for for-fixed
  variables, where each binding environment is the result of matching against
  at least one element from the match target. For each environment, the match
  result will be all elements of the match target which agree with the pattern
  under that environment. This can result in unexpected behaviour when giving
  very general patterns.
\<close>

    lemma
      assumes asms: "\<And>x. A x \<and> B x"  "\<And>y. A y \<and> C y"  "\<And>z. B z \<and> C z"
      shows "A x \<and> C x"
      by (match asms in I: "\<And>x. P x \<and> ?Q x" (multi) for P \<Rightarrow>
         \<open>match (P) in "A" \<Rightarrow> \<open>fail\<close>
                       \<bar> _ \<Rightarrow> \<open>match I in "\<And>x. A x \<and> B x" \<Rightarrow> \<open>fail\<close>
                                                      \<bar> _ \<Rightarrow> \<open>rule I\<close>\<close>\<close>)

text \<open>
  Intuitively it seems like this proof should fail to check. The first match
  result, which binds @{term I} to the first two members of \<open>asms\<close>, fails the
  second inner match due to binding @{term P} to @{term A}. Backtracking then
  attempts to bind @{term I} to the third member of \<open>asms\<close>. This passes all
  inner matches, but fails when @{method rule} cannot successfully apply this
  to the current goal. After this, a valid match that is produced by the
  unifier is one which binds @{term P} to simply \<open>\<lambda>a. A ?x\<close>. The first inner
  match succeeds because \<open>\<lambda>a. A ?x\<close> does not match @{term A}. The next inner
  match succeeds because @{term I} has only been bound to the first member of
  \<open>asms\<close>. This is due to @{method match} considering \<open>\<lambda>a. A ?x\<close> and \<open>\<lambda>a. A ?y\<close>
  as distinct terms.

  The simplest way to address this is to explicitly disallow term bindings
  which we would consider invalid.
\<close>

    method abs_used for P =
      (match (P) in "\<lambda>a. ?P" \<Rightarrow> \<open>fail\<close> \<bar> _ \<Rightarrow> \<open>-\<close>)

text \<open>
  This method has no effect on the goal state, but instead serves as a filter
  on the environment produced from match.
\<close>


section \<open>Uncurrying\<close>

text \<open>
  The @{method match} method is not aware of the logical content of match
  targets. Each pattern is simply matched against the shallow structure of a
  fact or term. Most facts are in \<^emph>\<open>normal form\<close>, which curries premises via
  meta-implication \<open>_ \<Longrightarrow> _\<close>.
\<close>

    lemma
      assumes asms: "D \<Longrightarrow> B \<Longrightarrow> C"  "D \<Longrightarrow> A"
      shows "D \<Longrightarrow> B \<Longrightarrow> C \<and> A"
      by (match asms in H: "D \<Longrightarrow> _" (multi) \<Rightarrow> \<open>prop_solver elims: H\<close>)

text \<open>
  For the first member of \<open>asms\<close> the dummy pattern successfully matches
  against @{term "B \<Longrightarrow> C"} and so the proof is successful.
\<close>

    lemma
      assumes asms: "A \<Longrightarrow> B \<Longrightarrow> C"  "D \<Longrightarrow> C"
      shows "D \<or> (A \<and> B) \<Longrightarrow> C"
      apply (match asms in H: "_ \<Longrightarrow> C" (multi) \<Rightarrow> \<open>prop_solver elims: H\<close>)(*<*)?
      apply (prop_solver elims: asms)
      done(*>*)

text \<open>
  This proof will fail to solve the goal. Our match pattern will only match
  rules which have a single premise, and conclusion @{term C}, so the first
  member of \<open>asms\<close> is not bound and thus the proof fails. Matching a pattern
  of the form @{term "P \<Longrightarrow> Q"} against this fact will bind @{term "P"} to
  @{term "A"} and @{term Q} to @{term "B \<Longrightarrow> C"}. Our pattern, with a concrete
  @{term "C"} in the conclusion, will fail to match this fact.

  To express our desired match, we may \<^emph>\<open>uncurry\<close> our rules before matching
  against them. This forms a meta-conjunction of all premises in a fact, so
  that only one implication remains. For example the uncurried version of
  @{term "A \<Longrightarrow> B \<Longrightarrow> C"} is @{term "A &&& B \<Longrightarrow> C"}. This will now match our
  desired pattern \<open>_ \<Longrightarrow> C\<close>, and can be \<^emph>\<open>curried\<close> after the match to put it
  back into normal form.
\<close>

    lemma
      assumes asms: "A \<Longrightarrow> B \<Longrightarrow> C"  "D \<Longrightarrow> C"
      shows "D \<or> (A \<and> B) \<Longrightarrow> C"
      by (match asms [uncurry] in H [curry]: "_ \<Longrightarrow> C" (multi) \<Rightarrow>
          \<open>prop_solver elims: H\<close>)


section \<open>Reverse matching\<close>

text \<open>
  The @{method match} method only attempts to perform matching of the pattern
  against the match target. Specifically this means that it will not
  instantiate schematic terms in the match target.
\<close>

    lemma
      assumes asms: "\<And>x :: 'a. A x"
      shows "A y"
      apply (match asms in H: "A y" \<Rightarrow> \<open>rule H\<close>)?
      apply (match asms in H: P for P \<Rightarrow>
          \<open>match ("A y") in P \<Rightarrow> \<open>rule H\<close>\<close>)
      done

text \<open>
  In the first @{method match} we attempt to find a member of \<open>asms\<close> which
  matches our goal precisely. This fails due to no such member existing. The
  second match reverses the role of the fact in the match, by first giving a
  general pattern @{term P}. This bound pattern is then matched against @{term
  "A y"}. In this case, @{term P} is bound to \<open>A ?x\<close> and so it successfully
  matches.
\<close>


section \<open>Type matching\<close>

text \<open>
  The rule instantiation attributes @{attribute "where"} and @{attribute "of"}
  attempt to guarantee type-correctness wherever possible. This can require
  additional invocations of @{method match} in order to statically ensure that
  instantiation will succeed.
\<close>

    lemma
      assumes asms: "\<And>x :: 'a. A x"
      shows "A y"
      by (match asms in H: "\<And>z :: 'b. P z" for P \<Rightarrow>
          \<open>match (y) in "y :: 'b" for y \<Rightarrow> \<open>rule H [where z = y]\<close>\<close>)

text \<open>
  In this example the type \<open>'b\<close> is matched to \<open>'a\<close>, however statically they
  are formally distinct types. The first match binds \<open>'b\<close> while the inner
  match serves to coerce @{term y} into having the type \<open>'b\<close>. This allows the
  rule instantiation to successfully apply.
\<close>


chapter \<open>Method development\<close>

section \<open>Tracing methods\<close>

text \<open>
  Method tracing is supported by auxiliary print methods provided by @{theory
  Eisbach_Tools}. These include @{method print_fact}, @{method print_term} and
  @{method print_type}. Whenever a print method is evaluated it leaves the
  goal unchanged and writes its argument as tracing output.

  Print methods can be combined with the @{method fail} method to investigate
  the backtracking behaviour of a method.
\<close>

    lemma
      assumes asms: A B C D
      shows D
      apply (match asms in H: _ \<Rightarrow> \<open>print_fact H, fail\<close>)(*<*)?
      apply (simp add: asms)
      done(*>*)

text \<open>
  This proof will fail, but the tracing output will show the order that the
  assumptions are attempted.
\<close>


section \<open>Integrating with Isabelle/ML\<close>

subsubsection \<open>Attributes\<close>

text \<open>
  A custom rule attribute is a simple way to extend the functionality of
  Eisbach methods. The dummy rule attribute notation (\<open>[[ _ ]]\<close>) invokes the
  given attribute against a dummy fact and evaluates to the result of that
  attribute. When used as a match target, this can serve as an effective
  auxiliary function.
\<close>

    attribute_setup get_split_rule =
      \<open>Args.term >> (fn t =>
        Thm.rule_attribute [] (fn context => fn _ =>
          (case get_split_rule (Context.proof_of context) t of
            SOME thm => thm
          | NONE => Drule.dummy_thm)))\<close>

text \<open>
  In this example, the new attribute @{attribute get_split_rule} lifts the ML
  function of the same name into an attribute. When applied to a case
  distinction over a datatype, it retrieves its corresponding split rule.

  We can then integrate this intro a method that applies the split rule, first
  matching to ensure that fetching the rule was successful.
\<close>
(*<*)declare TrueI [intros](*>*)
    method splits =
      (match conclusion in "?P f" for f \<Rightarrow>
        \<open>match [[get_split_rule f]] in U: "(_ :: bool) = _" \<Rightarrow>
          \<open>rule U [THEN iffD2]\<close>\<close>)

    lemma "L \<noteq> [] \<Longrightarrow> case L of [] \<Rightarrow> False | _ \<Rightarrow> True"
      apply splits
      apply (prop_solver intros: allI)
      done

text \<open>
  Here the new @{method splits} method transforms the goal to use only logical
  connectives: @{term "L = [] \<longrightarrow> False \<and> (\<forall>x y. L = x # y \<longrightarrow> True)"}. This goal
  is then in a form solvable by @{method prop_solver} when given the universal
  quantifier introduction rule \<open>allI\<close>.
\<close>

end
