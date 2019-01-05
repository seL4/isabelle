(*<*)theory AB imports Main begin(*>*)

section\<open>Case Study: A Context Free Grammar\<close>

text\<open>\label{sec:CFG}
\index{grammars!defining inductively|(}%
Grammars are nothing but shorthands for inductive definitions of nonterminals
which represent sets of strings. For example, the production
$A \to B c$ is short for
\[ w \in B \Longrightarrow wc \in A \]
This section demonstrates this idea with an example
due to Hopcroft and Ullman, a grammar for generating all words with an
equal number of $a$'s and~$b$'s:
\begin{eqnarray}
S &\to& \epsilon \mid b A \mid a B \nonumber\\
A &\to& a S \mid b A A \nonumber\\
B &\to& b S \mid a B B \nonumber
\end{eqnarray}
At the end we say a few words about the relationship between
the original proof @{cite \<open>p.\ts81\<close> HopcroftUllman} and our formal version.

We start by fixing the alphabet, which consists only of \<^term>\<open>a\<close>'s
and~\<^term>\<open>b\<close>'s:
\<close>

datatype alfa = a | b

text\<open>\noindent
For convenience we include the following easy lemmas as simplification rules:
\<close>

lemma [simp]: "(x \<noteq> a) = (x = b) \<and> (x \<noteq> b) = (x = a)"
by (case_tac x, auto)

text\<open>\noindent
Words over this alphabet are of type \<^typ>\<open>alfa list\<close>, and
the three nonterminals are declared as sets of such words.
The productions above are recast as a \emph{mutual} inductive
definition\index{inductive definition!simultaneous}
of \<^term>\<open>S\<close>, \<^term>\<open>A\<close> and~\<^term>\<open>B\<close>:
\<close>

inductive_set
  S :: "alfa list set" and
  A :: "alfa list set" and
  B :: "alfa list set"
where
  "[] \<in> S"
| "w \<in> A \<Longrightarrow> b#w \<in> S"
| "w \<in> B \<Longrightarrow> a#w \<in> S"

| "w \<in> S        \<Longrightarrow> a#w   \<in> A"
| "\<lbrakk> v\<in>A; w\<in>A \<rbrakk> \<Longrightarrow> b#v@w \<in> A"

| "w \<in> S            \<Longrightarrow> b#w   \<in> B"
| "\<lbrakk> v \<in> B; w \<in> B \<rbrakk> \<Longrightarrow> a#v@w \<in> B"

text\<open>\noindent
First we show that all words in \<^term>\<open>S\<close> contain the same number of \<^term>\<open>a\<close>'s and \<^term>\<open>b\<close>'s. Since the definition of \<^term>\<open>S\<close> is by mutual
induction, so is the proof: we show at the same time that all words in
\<^term>\<open>A\<close> contain one more \<^term>\<open>a\<close> than \<^term>\<open>b\<close> and all words in \<^term>\<open>B\<close> contain one more \<^term>\<open>b\<close> than \<^term>\<open>a\<close>.
\<close>

lemma correctness:
  "(w \<in> S \<longrightarrow> size[x\<leftarrow>w. x=a] = size[x\<leftarrow>w. x=b])     \<and>
   (w \<in> A \<longrightarrow> size[x\<leftarrow>w. x=a] = size[x\<leftarrow>w. x=b] + 1) \<and>
   (w \<in> B \<longrightarrow> size[x\<leftarrow>w. x=b] = size[x\<leftarrow>w. x=a] + 1)"

txt\<open>\noindent
These propositions are expressed with the help of the predefined \<^term>\<open>filter\<close> function on lists, which has the convenient syntax \<open>[x\<leftarrow>xs. P
x]\<close>, the list of all elements \<^term>\<open>x\<close> in \<^term>\<open>xs\<close> such that \<^prop>\<open>P x\<close>
holds. Remember that on lists \<open>size\<close> and \<open>length\<close> are synonymous.

The proof itself is by rule induction and afterwards automatic:
\<close>

by (rule S_A_B.induct, auto)

text\<open>\noindent
This may seem surprising at first, and is indeed an indication of the power
of inductive definitions. But it is also quite straightforward. For example,
consider the production $A \to b A A$: if $v,w \in A$ and the elements of $A$
contain one more $a$ than~$b$'s, then $bvw$ must again contain one more $a$
than~$b$'s.

As usual, the correctness of syntactic descriptions is easy, but completeness
is hard: does \<^term>\<open>S\<close> contain \emph{all} words with an equal number of
\<^term>\<open>a\<close>'s and \<^term>\<open>b\<close>'s? It turns out that this proof requires the
following lemma: every string with two more \<^term>\<open>a\<close>'s than \<^term>\<open>b\<close>'s can be cut somewhere such that each half has one more \<^term>\<open>a\<close> than
\<^term>\<open>b\<close>. This is best seen by imagining counting the difference between the
number of \<^term>\<open>a\<close>'s and \<^term>\<open>b\<close>'s starting at the left end of the
word. We start with 0 and end (at the right end) with 2. Since each move to the
right increases or decreases the difference by 1, we must have passed through
1 on our way from 0 to 2. Formally, we appeal to the following discrete
intermediate value theorem @{thm[source]nat0_intermed_int_val}
@{thm[display,margin=60]nat0_intermed_int_val[no_vars]}
where \<^term>\<open>f\<close> is of type \<^typ>\<open>nat \<Rightarrow> int\<close>, \<^typ>\<open>int\<close> are the integers,
\<open>\<bar>.\<bar>\<close> is the absolute value function\footnote{See
Table~\ref{tab:ascii} in the Appendix for the correct \textsc{ascii}
syntax.}, and \<^term>\<open>1::int\<close> is the integer 1 (see \S\ref{sec:numbers}).

First we show that our specific function, the difference between the
numbers of \<^term>\<open>a\<close>'s and \<^term>\<open>b\<close>'s, does indeed only change by 1 in every
move to the right. At this point we also start generalizing from \<^term>\<open>a\<close>'s
and \<^term>\<open>b\<close>'s to an arbitrary property \<^term>\<open>P\<close>. Otherwise we would have
to prove the desired lemma twice, once as stated above and once with the
roles of \<^term>\<open>a\<close>'s and \<^term>\<open>b\<close>'s interchanged.
\<close>

lemma step1: "\<forall>i < size w.
  \<bar>(int(size[x\<leftarrow>take (i+1) w. P x])-int(size[x\<leftarrow>take (i+1) w. \<not>P x]))
   - (int(size[x\<leftarrow>take i w. P x])-int(size[x\<leftarrow>take i w. \<not>P x]))\<bar> \<le> 1"

txt\<open>\noindent
The lemma is a bit hard to read because of the coercion function
\<open>int :: nat \<Rightarrow> int\<close>. It is required because \<^term>\<open>size\<close> returns
a natural number, but subtraction on type~\<^typ>\<open>nat\<close> will do the wrong thing.
Function \<^term>\<open>take\<close> is predefined and \<^term>\<open>take i xs\<close> is the prefix of
length \<^term>\<open>i\<close> of \<^term>\<open>xs\<close>; below we also need \<^term>\<open>drop i xs\<close>, which
is what remains after that prefix has been dropped from \<^term>\<open>xs\<close>.

The proof is by induction on \<^term>\<open>w\<close>, with a trivial base case, and a not
so trivial induction step. Since it is essentially just arithmetic, we do not
discuss it.
\<close>

apply(induct_tac w)
apply(auto simp add: abs_if take_Cons split: nat.split)
done

text\<open>
Finally we come to the above-mentioned lemma about cutting in half a word with two more elements of one sort than of the other sort:
\<close>

lemma part1:
 "size[x\<leftarrow>w. P x] = size[x\<leftarrow>w. \<not>P x]+2 \<Longrightarrow>
  \<exists>i\<le>size w. size[x\<leftarrow>take i w. P x] = size[x\<leftarrow>take i w. \<not>P x]+1"

txt\<open>\noindent
This is proved by \<open>force\<close> with the help of the intermediate value theorem,
instantiated appropriately and with its first premise disposed of by lemma
@{thm[source]step1}:
\<close>

apply(insert nat0_intermed_int_val[OF step1, of "P" "w" "1"])
by force

text\<open>\noindent

Lemma @{thm[source]part1} tells us only about the prefix \<^term>\<open>take i w\<close>.
An easy lemma deals with the suffix \<^term>\<open>drop i w\<close>:
\<close>


lemma part2:
  "\<lbrakk>size[x\<leftarrow>take i w @ drop i w. P x] =
    size[x\<leftarrow>take i w @ drop i w. \<not>P x]+2;
    size[x\<leftarrow>take i w. P x] = size[x\<leftarrow>take i w. \<not>P x]+1\<rbrakk>
   \<Longrightarrow> size[x\<leftarrow>drop i w. P x] = size[x\<leftarrow>drop i w. \<not>P x]+1"
by(simp del: append_take_drop_id)

text\<open>\noindent
In the proof we have disabled the normally useful lemma
\begin{isabelle}
@{thm append_take_drop_id[no_vars]}
\rulename{append_take_drop_id}
\end{isabelle}
to allow the simplifier to apply the following lemma instead:
@{text[display]"[x\<in>xs@ys. P x] = [x\<in>xs. P x] @ [x\<in>ys. P x]"}

To dispose of trivial cases automatically, the rules of the inductive
definition are declared simplification rules:
\<close>

declare S_A_B.intros[simp]

text\<open>\noindent
This could have been done earlier but was not necessary so far.

The completeness theorem tells us that if a word has the same number of
\<^term>\<open>a\<close>'s and \<^term>\<open>b\<close>'s, then it is in \<^term>\<open>S\<close>, and similarly 
for \<^term>\<open>A\<close> and \<^term>\<open>B\<close>:
\<close>

theorem completeness:
  "(size[x\<leftarrow>w. x=a] = size[x\<leftarrow>w. x=b]     \<longrightarrow> w \<in> S) \<and>
   (size[x\<leftarrow>w. x=a] = size[x\<leftarrow>w. x=b] + 1 \<longrightarrow> w \<in> A) \<and>
   (size[x\<leftarrow>w. x=b] = size[x\<leftarrow>w. x=a] + 1 \<longrightarrow> w \<in> B)"

txt\<open>\noindent
The proof is by induction on \<^term>\<open>w\<close>. Structural induction would fail here
because, as we can see from the grammar, we need to make bigger steps than
merely appending a single letter at the front. Hence we induct on the length
of \<^term>\<open>w\<close>, using the induction rule @{thm[source]length_induct}:
\<close>

apply(induct_tac w rule: length_induct)
apply(rename_tac w)

txt\<open>\noindent
The \<open>rule\<close> parameter tells \<open>induct_tac\<close> explicitly which induction
rule to use. For details see \S\ref{sec:complete-ind} below.
In this case the result is that we may assume the lemma already
holds for all words shorter than \<^term>\<open>w\<close>. Because the induction step renames
the induction variable we rename it back to \<open>w\<close>.

The proof continues with a case distinction on \<^term>\<open>w\<close>,
on whether \<^term>\<open>w\<close> is empty or not.
\<close>

apply(case_tac w)
 apply(simp_all)
(*<*)apply(rename_tac x v)(*>*)

txt\<open>\noindent
Simplification disposes of the base case and leaves only a conjunction
of two step cases to be proved:
if \<^prop>\<open>w = a#v\<close> and @{prop[display]"size[x\<in>v. x=a] = size[x\<in>v. x=b]+2"} then
\<^prop>\<open>b#v \<in> A\<close>, and similarly for \<^prop>\<open>w = b#v\<close>.
We only consider the first case in detail.

After breaking the conjunction up into two cases, we can apply
@{thm[source]part1} to the assumption that \<^term>\<open>w\<close> contains two more \<^term>\<open>a\<close>'s than \<^term>\<open>b\<close>'s.
\<close>

apply(rule conjI)
 apply(clarify)
 apply(frule part1[of "\<lambda>x. x=a", simplified])
 apply(clarify)
txt\<open>\noindent
This yields an index \<^prop>\<open>i \<le> length v\<close> such that
@{prop[display]"length [x\<leftarrow>take i v . x = a] = length [x\<leftarrow>take i v . x = b] + 1"}
With the help of @{thm[source]part2} it follows that
@{prop[display]"length [x\<leftarrow>drop i v . x = a] = length [x\<leftarrow>drop i v . x = b] + 1"}
\<close>

 apply(drule part2[of "\<lambda>x. x=a", simplified])
  apply(assumption)

txt\<open>\noindent
Now it is time to decompose \<^term>\<open>v\<close> in the conclusion \<^prop>\<open>b#v \<in> A\<close>
into \<^term>\<open>take i v @ drop i v\<close>,
\<close>

 apply(rule_tac n1=i and t=v in subst[OF append_take_drop_id])

txt\<open>\noindent
(the variables \<^term>\<open>n1\<close> and \<^term>\<open>t\<close> are the result of composing the
theorems @{thm[source]subst} and @{thm[source]append_take_drop_id})
after which the appropriate rule of the grammar reduces the goal
to the two subgoals \<^prop>\<open>take i v \<in> A\<close> and \<^prop>\<open>drop i v \<in> A\<close>:
\<close>

 apply(rule S_A_B.intros)

txt\<open>
Both subgoals follow from the induction hypothesis because both \<^term>\<open>take i
v\<close> and \<^term>\<open>drop i v\<close> are shorter than \<^term>\<open>w\<close>:
\<close>

  apply(force simp add: min_less_iff_disj)
 apply(force split: nat_diff_split)

txt\<open>
The case \<^prop>\<open>w = b#v\<close> is proved analogously:
\<close>

apply(clarify)
apply(frule part1[of "\<lambda>x. x=b", simplified])
apply(clarify)
apply(drule part2[of "\<lambda>x. x=b", simplified])
 apply(assumption)
apply(rule_tac n1=i and t=v in subst[OF append_take_drop_id])
apply(rule S_A_B.intros)
 apply(force simp add: min_less_iff_disj)
by(force simp add: min_less_iff_disj split: nat_diff_split)

text\<open>
We conclude this section with a comparison of our proof with 
Hopcroft\index{Hopcroft, J. E.} and Ullman's\index{Ullman, J. D.}
@{cite \<open>p.\ts81\<close> HopcroftUllman}.
For a start, the textbook
grammar, for no good reason, excludes the empty word, thus complicating
matters just a little bit: they have 8 instead of our 7 productions.

More importantly, the proof itself is different: rather than
separating the two directions, they perform one induction on the
length of a word. This deprives them of the beauty of rule induction,
and in the easy direction (correctness) their reasoning is more
detailed than our \<open>auto\<close>. For the hard part (completeness), they
consider just one of the cases that our \<open>simp_all\<close> disposes of
automatically. Then they conclude the proof by saying about the
remaining cases: ``We do this in a manner similar to our method of
proof for part (1); this part is left to the reader''. But this is
precisely the part that requires the intermediate value theorem and
thus is not at all similar to the other cases (which are automatic in
Isabelle). The authors are at least cavalier about this point and may
even have overlooked the slight difficulty lurking in the omitted
cases.  Such errors are found in many pen-and-paper proofs when they
are scrutinized formally.%
\index{grammars!defining inductively|)}
\<close>

(*<*)end(*>*)
