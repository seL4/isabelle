(*<*)theory AB = Main:(*>*)

section{*Case Study: A Context Free Grammar*}

text{*\label{sec:CFG}
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
the original proof \cite[p.\ts81]{HopcroftUllman} and our formal version.

We start by fixing the alphabet, which consists only of @{term a}'s
and~@{term b}'s:
*}

datatype alfa = a | b;

text{*\noindent
For convenience we include the following easy lemmas as simplification rules:
*}

lemma [simp]: "(x \<noteq> a) = (x = b) \<and> (x \<noteq> b) = (x = a)";
by (case_tac x, auto)

text{*\noindent
Words over this alphabet are of type @{typ"alfa list"}, and
the three nonterminals are declared as sets of such words:
*}

consts S :: "alfa list set"
       A :: "alfa list set"
       B :: "alfa list set";

text{*\noindent
The productions above are recast as a \emph{mutual} inductive
definition\index{inductive definition!simultaneous}
of @{term S}, @{term A} and~@{term B}:
*}

inductive S A B
intros
  "[] \<in> S"
  "w \<in> A \<Longrightarrow> b#w \<in> S"
  "w \<in> B \<Longrightarrow> a#w \<in> S"

  "w \<in> S        \<Longrightarrow> a#w   \<in> A"
  "\<lbrakk> v\<in>A; w\<in>A \<rbrakk> \<Longrightarrow> b#v@w \<in> A"

  "w \<in> S            \<Longrightarrow> b#w   \<in> B"
  "\<lbrakk> v \<in> B; w \<in> B \<rbrakk> \<Longrightarrow> a#v@w \<in> B";

text{*\noindent
First we show that all words in @{term S} contain the same number of @{term
a}'s and @{term b}'s. Since the definition of @{term S} is by mutual
induction, so is the proof: we show at the same time that all words in
@{term A} contain one more @{term a} than @{term b} and all words in @{term
B} contains one more @{term b} than @{term a}.
*}

lemma correctness:
  "(w \<in> S \<longrightarrow> size[x\<in>w. x=a] = size[x\<in>w. x=b])     \<and>
   (w \<in> A \<longrightarrow> size[x\<in>w. x=a] = size[x\<in>w. x=b] + 1) \<and>
   (w \<in> B \<longrightarrow> size[x\<in>w. x=b] = size[x\<in>w. x=a] + 1)"

txt{*\noindent
These propositions are expressed with the help of the predefined @{term
filter} function on lists, which has the convenient syntax @{text"[x\<in>xs. P
x]"}, the list of all elements @{term x} in @{term xs} such that @{prop"P x"}
holds. Remember that on lists @{text size} and @{text length} are synonymous.

The proof itself is by rule induction and afterwards automatic:
*}

by (rule S_A_B.induct, auto)

text{*\noindent
This may seem surprising at first, and is indeed an indication of the power
of inductive definitions. But it is also quite straightforward. For example,
consider the production $A \to b A A$: if $v,w \in A$ and the elements of $A$
contain one more $a$ than~$b$'s, then $bvw$ must again contain one more $a$
than~$b$'s.

As usual, the correctness of syntactic descriptions is easy, but completeness
is hard: does @{term S} contain \emph{all} words with an equal number of
@{term a}'s and @{term b}'s? It turns out that this proof requires the
following lemma: every string with two more @{term a}'s than @{term
b}'s can be cut somewhere such that each half has one more @{term a} than
@{term b}. This is best seen by imagining counting the difference between the
number of @{term a}'s and @{term b}'s starting at the left end of the
word. We start with 0 and end (at the right end) with 2. Since each move to the
right increases or decreases the difference by 1, we must have passed through
1 on our way from 0 to 2. Formally, we appeal to the following discrete
intermediate value theorem @{thm[source]nat0_intermed_int_val}
@{thm[display]nat0_intermed_int_val[no_vars]}
where @{term f} is of type @{typ"nat \<Rightarrow> int"}, @{typ int} are the integers,
@{text"\<bar>.\<bar>"} is the absolute value function\footnote{See
Table~\ref{tab:ascii} in the Appendix for the correct \textsc{ascii}
syntax.}, and @{term"#1::int"} is the integer 1 (see \S\ref{sec:numbers}).

First we show that our specific function, the difference between the
numbers of @{term a}'s and @{term b}'s, does indeed only change by 1 in every
move to the right. At this point we also start generalizing from @{term a}'s
and @{term b}'s to an arbitrary property @{term P}. Otherwise we would have
to prove the desired lemma twice, once as stated above and once with the
roles of @{term a}'s and @{term b}'s interchanged.
*}

lemma step1: "\<forall>i < size w.
  \<bar>(int(size[x\<in>take (i+1) w. P x])-int(size[x\<in>take (i+1) w. \<not>P x]))
   - (int(size[x\<in>take i w. P x])-int(size[x\<in>take i w. \<not>P x]))\<bar> \<le> #1"

txt{*\noindent
The lemma is a bit hard to read because of the coercion function
@{text"int :: nat \<Rightarrow> int"}. It is required because @{term size} returns
a natural number, but subtraction on type~@{typ nat} will do the wrong thing.
Function @{term take} is predefined and @{term"take i xs"} is the prefix of
length @{term i} of @{term xs}; below we also need @{term"drop i xs"}, which
is what remains after that prefix has been dropped from @{term xs}.

The proof is by induction on @{term w}, with a trivial base case, and a not
so trivial induction step. Since it is essentially just arithmetic, we do not
discuss it.
*}

apply(induct w);
 apply(simp);
by(force simp add:zabs_def take_Cons split:nat.split if_splits); 

text{*
Finally we come to the above mentioned lemma about cutting in half a word with two
more elements of one sort than of the other sort:
*}

lemma part1:
 "size[x\<in>w. P x] = size[x\<in>w. \<not>P x]+2 \<Longrightarrow>
  \<exists>i\<le>size w. size[x\<in>take i w. P x] = size[x\<in>take i w. \<not>P x]+1";

txt{*\noindent
This is proved by @{text force} with the help of the intermediate value theorem,
instantiated appropriately and with its first premise disposed of by lemma
@{thm[source]step1}:
*}

apply(insert nat0_intermed_int_val[OF step1, of "P" "w" "#1"]);
by force;

text{*\noindent

Lemma @{thm[source]part1} tells us only about the prefix @{term"take i w"}.
An easy lemma deals with the suffix @{term"drop i w"}:
*}


lemma part2:
  "\<lbrakk>size[x\<in>take i w @ drop i w. P x] =
    size[x\<in>take i w @ drop i w. \<not>P x]+2;
    size[x\<in>take i w. P x] = size[x\<in>take i w. \<not>P x]+1\<rbrakk>
   \<Longrightarrow> size[x\<in>drop i w. P x] = size[x\<in>drop i w. \<not>P x]+1";
by(simp del:append_take_drop_id);

text{*\noindent
In the proof we have disabled the normally useful lemma
\begin{isabelle}
@{thm append_take_drop_id[no_vars]}
\rulename{append_take_drop_id}
\end{isabelle}
to allow the simplifier to apply the following lemma instead:
@{text[display]"[x\<in>xs@ys. P x] = [x\<in>xs. P x] @ [x\<in>ys. P x]"}

To dispose of trivial cases automatically, the rules of the inductive
definition are declared simplification rules:
*}

declare S_A_B.intros[simp];

text{*\noindent
This could have been done earlier but was not necessary so far.

The completeness theorem tells us that if a word has the same number of
@{term a}'s and @{term b}'s, then it is in @{term S}, and similarly 
for @{term A} and @{term B}:
*}

theorem completeness:
  "(size[x\<in>w. x=a] = size[x\<in>w. x=b]     \<longrightarrow> w \<in> S) \<and>
   (size[x\<in>w. x=a] = size[x\<in>w. x=b] + 1 \<longrightarrow> w \<in> A) \<and>
   (size[x\<in>w. x=b] = size[x\<in>w. x=a] + 1 \<longrightarrow> w \<in> B)";

txt{*\noindent
The proof is by induction on @{term w}. Structural induction would fail here
because, as we can see from the grammar, we need to make bigger steps than
merely appending a single letter at the front. Hence we induct on the length
of @{term w}, using the induction rule @{thm[source]length_induct}:
*}

apply(induct_tac w rule: length_induct);
(*<*)apply(rename_tac w)(*>*)

txt{*\noindent
The @{text rule} parameter tells @{text induct_tac} explicitly which induction
rule to use. For details see \S\ref{sec:complete-ind} below.
In this case the result is that we may assume the lemma already
holds for all words shorter than @{term w}.

The proof continues with a case distinction on @{term w},
i.e.\ if @{term w} is empty or not.
*}

apply(case_tac w);
 apply(simp_all);
(*<*)apply(rename_tac x v)(*>*)

txt{*\noindent
Simplification disposes of the base case and leaves only a conjunction
of two step cases to be proved:
if @{prop"w = a#v"} and @{prop[display]"size[x\<in>v. x=a] = size[x\<in>v. x=b]+2"} then
@{prop"b#v \<in> A"}, and similarly for @{prop"w = b#v"}.
We only consider the first case in detail.

After breaking the conjunction up into two cases, we can apply
@{thm[source]part1} to the assumption that @{term w} contains two more @{term
a}'s than @{term b}'s.
*}

apply(rule conjI)
 apply(clarify)
 apply(frule part1[of "\<lambda>x. x=a", simplified])
 apply(clarify)
txt{*\noindent
This yields an index @{prop"i \<le> length v"} such that
@{prop[display]"length [x\<in>take i v . x = a] = length [x\<in>take i v . x = b] + 1"}
With the help of @{thm[source]part2} it follows that
@{prop[display]"length [x\<in>drop i v . x = a] = length [x\<in>drop i v . x = b] + 1"}
*}

 apply(drule part2[of "\<lambda>x. x=a", simplified])
  apply(assumption)

txt{*\noindent
Now it is time to decompose @{term v} in the conclusion @{prop"b#v \<in> A"}
into @{term"take i v @ drop i v"},
*}

 apply(rule_tac n1=i and t=v in subst[OF append_take_drop_id])

txt{*\noindent
(the variables @{term n1} and @{term t} are the result of composing the
theorems @{thm[source]subst} and @{thm[source]append_take_drop_id})
after which the appropriate rule of the grammar reduces the goal
to the two subgoals @{prop"take i v \<in> A"} and @{prop"drop i v \<in> A"}:
*}

 apply(rule S_A_B.intros)

txt{*
Both subgoals follow from the induction hypothesis because both @{term"take i
v"} and @{term"drop i v"} are shorter than @{term w}:
*}

  apply(force simp add: min_less_iff_disj)
 apply(force split add: nat_diff_split)

txt{*
The case @{prop"w = b#v"} is proved analogously:
*}

apply(clarify)
apply(frule part1[of "\<lambda>x. x=b", simplified])
apply(clarify)
apply(drule part2[of "\<lambda>x. x=b", simplified])
 apply(assumption)
apply(rule_tac n1=i and t=v in subst[OF append_take_drop_id])
apply(rule S_A_B.intros)
 apply(force simp add:min_less_iff_disj)
by(force simp add:min_less_iff_disj split add: nat_diff_split)

text{*
We conclude this section with a comparison of our proof with 
Hopcroft and Ullman's \cite[p.\ts81]{HopcroftUllman}. For a start, the texbook
grammar, for no good reason, excludes the empty word, thus complicating
matters just a little bit: they have 8 instead of our 7 productions.

More importantly, the proof itself is different: rather than
separating the two directions, they perform one induction on the
length of a word. This deprives them of the beauty of rule induction,
and in the easy direction (correctness) their reasoning is more
detailed than our @{text auto}. For the hard part (completeness), they
consider just one of the cases that our @{text simp_all} disposes of
automatically. Then they conclude the proof by saying about the
remaining cases: ``We do this in a manner similar to our method of
proof for part (1); this part is left to the reader''. But this is
precisely the part that requires the intermediate value theorem and
thus is not at all similar to the other cases (which are automatic in
Isabelle). The authors are at least cavalier about this point and may
even have overlooked the slight difficulty lurking in the omitted
cases. This is not atypical for pen-and-paper proofs, once analysed in
detail.  *}

(*<*)end(*>*)
