(*  Title:      FOL/ex/Classical.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>Classical Predicate Calculus Problems\<close>

theory Classical
imports FOL
begin

lemma "(P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longrightarrow> Q) \<or> (P \<longrightarrow> R)"
  by blast


subsubsection \<open>If and only if\<close>

lemma "(P \<longleftrightarrow> Q) \<longleftrightarrow> (Q \<longleftrightarrow> P)"
  by blast

lemma "\<not> (P \<longleftrightarrow> \<not> P)"
  by blast


subsection \<open>Pelletier's examples\<close>

text \<open>
  Sample problems from

    \<^item> F. J. Pelletier,
    Seventy-Five Problems for Testing Automatic Theorem Provers,
    J. Automated Reasoning 2 (1986), 191-216.
    Errata, JAR 4 (1988), 236-236.

  The hardest problems -- judging by experience with several theorem
  provers, including matrix ones -- are 34 and 43.
\<close>

text\<open>1\<close>
lemma "(P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  by blast

text\<open>2\<close>
lemma "\<not> \<not> P \<longleftrightarrow> P"
  by blast

text\<open>3\<close>
lemma "\<not> (P \<longrightarrow> Q) \<longrightarrow> (Q \<longrightarrow> P)"
  by blast

text\<open>4\<close>
lemma "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  by blast

text\<open>5\<close>
lemma "((P \<or> Q) \<longrightarrow> (P \<or> R)) \<longrightarrow> (P \<or> (Q \<longrightarrow> R))"
  by blast

text\<open>6\<close>
lemma "P \<or> \<not> P"
  by blast

text\<open>7\<close>
lemma "P \<or> \<not> \<not> \<not> P"
  by blast

text\<open>8. Peirce's law\<close>
lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  by blast

text\<open>9\<close>
lemma "((P \<or> Q) \<and> (\<not> P \<or> Q) \<and> (P \<or> \<not> Q)) \<longrightarrow> \<not> (\<not> P \<or> \<not> Q)"
  by blast

text\<open>10\<close>
lemma "(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)"
  by blast

text\<open>11. Proved in each direction (incorrectly, says Pelletier!!)\<close>
lemma "P \<longleftrightarrow> P"
  by blast

text\<open>12. "Dijkstra's law"\<close>
lemma "((P \<longleftrightarrow> Q) \<longleftrightarrow> R) \<longleftrightarrow> (P \<longleftrightarrow> (Q \<longleftrightarrow> R))"
  by blast

text\<open>13. Distributive law\<close>
lemma "P \<or> (Q \<and> R) \<longleftrightarrow> (P \<or> Q) \<and> (P \<or> R)"
  by blast

text\<open>14\<close>
lemma "(P \<longleftrightarrow> Q) \<longleftrightarrow> ((Q \<or> \<not> P) \<and> (\<not> Q \<or> P))"
  by blast

text\<open>15\<close>
lemma "(P \<longrightarrow> Q) \<longleftrightarrow> (\<not> P \<or> Q)"
  by blast

text\<open>16\<close>
lemma "(P \<longrightarrow> Q) \<or> (Q \<longrightarrow> P)"
  by blast

text\<open>17\<close>
lemma "((P \<and> (Q \<longrightarrow> R)) \<longrightarrow> S) \<longleftrightarrow> ((\<not> P \<or> Q \<or> S) \<and> (\<not> P \<or> \<not> R \<or> S))"
  by blast


subsection \<open>Classical Logic: examples with quantifiers\<close>

lemma "(\<forall>x. P(x) \<and> Q(x)) \<longleftrightarrow> (\<forall>x. P(x)) \<and> (\<forall>x. Q(x))"
  by blast

lemma "(\<exists>x. P \<longrightarrow> Q(x)) \<longleftrightarrow> (P \<longrightarrow> (\<exists>x. Q(x)))"
  by blast

lemma "(\<exists>x. P(x) \<longrightarrow> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<longrightarrow> Q"
  by blast

lemma "(\<forall>x. P(x)) \<or> Q \<longleftrightarrow> (\<forall>x. P(x) \<or> Q)"
  by blast

text\<open>Discussed in Avron, Gentzen-Type Systems, Resolution and Tableaux,
  JAR 10 (265-281), 1993.  Proof is trivial!\<close>
lemma "\<not> ((\<exists>x. \<not> P(x)) \<and> ((\<exists>x. P(x)) \<or> (\<exists>x. P(x) \<and> Q(x))) \<and> \<not> (\<exists>x. P(x)))"
  by blast


subsection \<open>Problems requiring quantifier duplication\<close>

text\<open>Theorem B of Peter Andrews, Theorem Proving via General Matings,
  JACM 28 (1981).\<close>
lemma "(\<exists>x. \<forall>y. P(x) \<longleftrightarrow> P(y)) \<longrightarrow> ((\<exists>x. P(x)) \<longleftrightarrow> (\<forall>y. P(y)))"
  by blast

text\<open>Needs multiple instantiation of ALL.\<close>
lemma "(\<forall>x. P(x) \<longrightarrow> P(f(x))) \<and> P(d) \<longrightarrow> P(f(f(f(d))))"
  by blast

text\<open>Needs double instantiation of the quantifier\<close>
lemma "\<exists>x. P(x) \<longrightarrow> P(a) \<and> P(b)"
  by blast

lemma "\<exists>z. P(z) \<longrightarrow> (\<forall>x. P(x))"
  by blast

lemma "\<exists>x. (\<exists>y. P(y)) \<longrightarrow> P(x)"
  by blast

text\<open>V. Lifschitz, What Is the Inverse Method?, JAR 5 (1989), 1--23. NOT PROVED.\<close>
lemma
  "\<exists>x x'. \<forall>y. \<exists>z z'.
    (\<not> P(y,y) \<or> P(x,x) \<or> \<not> S(z,x)) \<and>
    (S(x,y) \<or> \<not> S(y,z) \<or> Q(z',z')) \<and>
    (Q(x',y) \<or> \<not> Q(y,z') \<or> S(x',x'))"
  oops


subsection \<open>Hard examples with quantifiers\<close>

text\<open>18\<close>
lemma "\<exists>y. \<forall>x. P(y) \<longrightarrow> P(x)"
  by blast

text\<open>19\<close>
lemma "\<exists>x. \<forall>y z. (P(y) \<longrightarrow> Q(z)) \<longrightarrow> (P(x) \<longrightarrow> Q(x))"
  by blast

text\<open>20\<close>
lemma "(\<forall>x y. \<exists>z. \<forall>w. (P(x) \<and> Q(y) \<longrightarrow> R(z) \<and> S(w)))
  \<longrightarrow> (\<exists>x y. P(x) \<and> Q(y)) \<longrightarrow> (\<exists>z. R(z))"
  by blast

text\<open>21\<close>
lemma "(\<exists>x. P \<longrightarrow> Q(x)) \<and> (\<exists>x. Q(x) \<longrightarrow> P) \<longrightarrow> (\<exists>x. P \<longleftrightarrow> Q(x))"
  by blast

text\<open>22\<close>
lemma "(\<forall>x. P \<longleftrightarrow> Q(x)) \<longrightarrow> (P \<longleftrightarrow> (\<forall>x. Q(x)))"
  by blast

text\<open>23\<close>
lemma "(\<forall>x. P \<or> Q(x)) \<longleftrightarrow> (P \<or> (\<forall>x. Q(x)))"
  by blast

text\<open>24\<close>
lemma
  "\<not> (\<exists>x. S(x) \<and> Q(x)) \<and> (\<forall>x. P(x) \<longrightarrow> Q(x) \<or> R(x)) \<and>
    (\<not> (\<exists>x. P(x)) \<longrightarrow> (\<exists>x. Q(x))) \<and> (\<forall>x. Q(x) \<or> R(x) \<longrightarrow> S(x))
    \<longrightarrow> (\<exists>x. P(x) \<and> R(x))"
  by blast

text\<open>25\<close>
lemma
  "(\<exists>x. P(x)) \<and>
    (\<forall>x. L(x) \<longrightarrow> \<not> (M(x) \<and> R(x))) \<and>
    (\<forall>x. P(x) \<longrightarrow> (M(x) \<and> L(x))) \<and>
    ((\<forall>x. P(x) \<longrightarrow> Q(x)) \<or> (\<exists>x. P(x) \<and> R(x)))
    \<longrightarrow> (\<exists>x. Q(x) \<and> P(x))"
  by blast

text\<open>26\<close>
lemma
  "((\<exists>x. p(x)) \<longleftrightarrow> (\<exists>x. q(x))) \<and>
    (\<forall>x. \<forall>y. p(x) \<and> q(y) \<longrightarrow> (r(x) \<longleftrightarrow> s(y)))
  \<longrightarrow> ((\<forall>x. p(x) \<longrightarrow> r(x)) \<longleftrightarrow> (\<forall>x. q(x) \<longrightarrow> s(x)))"
  by blast

text\<open>27\<close>
lemma
  "(\<exists>x. P(x) \<and> \<not> Q(x)) \<and>
    (\<forall>x. P(x) \<longrightarrow> R(x)) \<and>
    (\<forall>x. M(x) \<and> L(x) \<longrightarrow> P(x)) \<and>
    ((\<exists>x. R(x) \<and> \<not> Q(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> \<not> R(x)))
  \<longrightarrow> (\<forall>x. M(x) \<longrightarrow> \<not> L(x))"
  by blast

text\<open>28. AMENDED\<close>
lemma
  "(\<forall>x. P(x) \<longrightarrow> (\<forall>x. Q(x))) \<and>
    ((\<forall>x. Q(x) \<or> R(x)) \<longrightarrow> (\<exists>x. Q(x) \<and> S(x))) \<and>
    ((\<exists>x. S(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> M(x)))
  \<longrightarrow> (\<forall>x. P(x) \<and> L(x) \<longrightarrow> M(x))"
  by blast

text\<open>29. Essentially the same as Principia Mathematica *11.71\<close>
lemma
  "(\<exists>x. P(x)) \<and> (\<exists>y. Q(y))
    \<longrightarrow> ((\<forall>x. P(x) \<longrightarrow> R(x)) \<and> (\<forall>y. Q(y) \<longrightarrow> S(y)) \<longleftrightarrow>
      (\<forall>x y. P(x) \<and> Q(y) \<longrightarrow> R(x) \<and> S(y)))"
  by blast

text\<open>30\<close>
lemma
  "(\<forall>x. P(x) \<or> Q(x) \<longrightarrow> \<not> R(x)) \<and>
    (\<forall>x. (Q(x) \<longrightarrow> \<not> S(x)) \<longrightarrow> P(x) \<and> R(x))
    \<longrightarrow> (\<forall>x. S(x))"
  by blast

text\<open>31\<close>
lemma
  "\<not> (\<exists>x. P(x) \<and> (Q(x) \<or> R(x))) \<and>
    (\<exists>x. L(x) \<and> P(x)) \<and>
    (\<forall>x. \<not> R(x) \<longrightarrow> M(x))
  \<longrightarrow> (\<exists>x. L(x) \<and> M(x))"
  by blast

text\<open>32\<close>
lemma
  "(\<forall>x. P(x) \<and> (Q(x) \<or> R(x)) \<longrightarrow> S(x)) \<and>
    (\<forall>x. S(x) \<and> R(x) \<longrightarrow> L(x)) \<and>
    (\<forall>x. M(x) \<longrightarrow> R(x))
  \<longrightarrow> (\<forall>x. P(x) \<and> M(x) \<longrightarrow> L(x))"
  by blast

text\<open>33\<close>
lemma
  "(\<forall>x. P(a) \<and> (P(x) \<longrightarrow> P(b)) \<longrightarrow> P(c)) \<longleftrightarrow>
    (\<forall>x. (\<not> P(a) \<or> P(x) \<or> P(c)) \<and> (\<not> P(a) \<or> \<not> P(b) \<or> P(c)))"
  by blast

text\<open>34. AMENDED (TWICE!!). Andrews's challenge.\<close>
lemma
  "((\<exists>x. \<forall>y. p(x) \<longleftrightarrow> p(y)) \<longleftrightarrow> ((\<exists>x. q(x)) \<longleftrightarrow> (\<forall>y. p(y)))) \<longleftrightarrow>
    ((\<exists>x. \<forall>y. q(x) \<longleftrightarrow> q(y)) \<longleftrightarrow> ((\<exists>x. p(x)) \<longleftrightarrow> (\<forall>y. q(y))))"
  by blast

text\<open>35\<close>
lemma "\<exists>x y. P(x,y) \<longrightarrow> (\<forall>u v. P(u,v))"
  by blast

text\<open>36\<close>
lemma
  "(\<forall>x. \<exists>y. J(x,y)) \<and>
    (\<forall>x. \<exists>y. G(x,y)) \<and>
    (\<forall>x y. J(x,y) \<or> G(x,y) \<longrightarrow> (\<forall>z. J(y,z) \<or> G(y,z) \<longrightarrow> H(x,z)))
  \<longrightarrow> (\<forall>x. \<exists>y. H(x,y))"
  by blast

text\<open>37\<close>
lemma
  "(\<forall>z. \<exists>w. \<forall>x. \<exists>y.
    (P(x,z) \<longrightarrow> P(y,w)) \<and> P(y,z) \<and> (P(y,w) \<longrightarrow> (\<exists>u. Q(u,w)))) \<and>
    (\<forall>x z. \<not> P(x,z) \<longrightarrow> (\<exists>y. Q(y,z))) \<and>
    ((\<exists>x y. Q(x,y)) \<longrightarrow> (\<forall>x. R(x,x)))
  \<longrightarrow> (\<forall>x. \<exists>y. R(x,y))"
  by blast

text\<open>38\<close>
lemma
  "(\<forall>x. p(a) \<and> (p(x) \<longrightarrow> (\<exists>y. p(y) \<and> r(x,y))) \<longrightarrow>
    (\<exists>z. \<exists>w. p(z) \<and> r(x,w) \<and> r(w,z)))  \<longleftrightarrow>
    (\<forall>x. (\<not> p(a) \<or> p(x) \<or> (\<exists>z. \<exists>w. p(z) \<and> r(x,w) \<and> r(w,z))) \<and>
      (\<not> p(a) \<or> \<not> (\<exists>y. p(y) \<and> r(x,y)) \<or>
      (\<exists>z. \<exists>w. p(z) \<and> r(x,w) \<and> r(w,z))))"
  by blast

text\<open>39\<close>
lemma "\<not> (\<exists>x. \<forall>y. F(y,x) \<longleftrightarrow> \<not> F(y,y))"
  by blast

text\<open>40. AMENDED\<close>
lemma
  "(\<exists>y. \<forall>x. F(x,y) \<longleftrightarrow> F(x,x)) \<longrightarrow>
    \<not> (\<forall>x. \<exists>y. \<forall>z. F(z,y) \<longleftrightarrow> \<not> F(z,x))"
  by blast

text\<open>41\<close>
lemma
  "(\<forall>z. \<exists>y. \<forall>x. f(x,y) \<longleftrightarrow> f(x,z) \<and> \<not> f(x,x))
    \<longrightarrow> \<not> (\<exists>z. \<forall>x. f(x,z))"
  by blast

text\<open>42\<close>
lemma "\<not> (\<exists>y. \<forall>x. p(x,y) \<longleftrightarrow> \<not> (\<exists>z. p(x,z) \<and> p(z,x)))"
  by blast

text\<open>43\<close>
lemma
  "(\<forall>x. \<forall>y. q(x,y) \<longleftrightarrow> (\<forall>z. p(z,x) \<longleftrightarrow> p(z,y)))
    \<longrightarrow> (\<forall>x. \<forall>y. q(x,y) \<longleftrightarrow> q(y,x))"
  by blast

text \<open>
  Other proofs: Can use @{text auto}, which cheats by using rewriting!
  @{text Deepen_tac} alone requires 253 secs.  Or
  @{text \<open>by (mini_tac 1 THEN Deepen_tac 5 1)\<close>}.
\<close>

text\<open>44\<close>
lemma
  "(\<forall>x. f(x) \<longrightarrow> (\<exists>y. g(y) \<and> h(x,y) \<and> (\<exists>y. g(y) \<and> \<not> h(x,y)))) \<and>
    (\<exists>x. j(x) \<and> (\<forall>y. g(y) \<longrightarrow> h(x,y)))
  \<longrightarrow> (\<exists>x. j(x) \<and> \<not> f(x))"
  by blast

text\<open>45\<close>
lemma
  "(\<forall>x. f(x) \<and> (\<forall>y. g(y) \<and> h(x,y) \<longrightarrow> j(x,y))
      \<longrightarrow> (\<forall>y. g(y) \<and> h(x,y) \<longrightarrow> k(y))) \<and>
      \<not> (\<exists>y. l(y) \<and> k(y)) \<and>
      (\<exists>x. f(x) \<and> (\<forall>y. h(x,y) \<longrightarrow> l(y)) \<and> (\<forall>y. g(y) \<and> h(x,y) \<longrightarrow> j(x,y)))
      \<longrightarrow> (\<exists>x. f(x) \<and> \<not> (\<exists>y. g(y) \<and> h(x,y)))"
  by blast


text\<open>46\<close>
lemma
  "(\<forall>x. f(x) \<and> (\<forall>y. f(y) \<and> h(y,x) \<longrightarrow> g(y)) \<longrightarrow> g(x)) \<and>
      ((\<exists>x. f(x) \<and> \<not> g(x)) \<longrightarrow>
       (\<exists>x. f(x) \<and> \<not> g(x) \<and> (\<forall>y. f(y) \<and> \<not> g(y) \<longrightarrow> j(x,y)))) \<and>
      (\<forall>x y. f(x) \<and> f(y) \<and> h(x,y) \<longrightarrow> \<not> j(y,x))
      \<longrightarrow> (\<forall>x. f(x) \<longrightarrow> g(x))"
  by blast


subsection \<open>Problems (mainly) involving equality or functions\<close>

text\<open>48\<close>
lemma "(a = b \<or> c = d) \<and> (a = c \<or> b = d) \<longrightarrow> a = d \<or> b = c"
  by blast

text\<open>49. NOT PROVED AUTOMATICALLY. Hard because it involves substitution for
  Vars; the type constraint ensures that x,y,z have the same type as a,b,u.\<close>
lemma
  "(\<exists>x y::'a. \<forall>z. z = x \<or> z = y) \<and> P(a) \<and> P(b) \<and> a \<noteq> b \<longrightarrow> (\<forall>u::'a. P(u))"
  apply safe
  apply (rule_tac x = a in allE, assumption)
  apply (rule_tac x = b in allE, assumption)
  apply fast  -- \<open>blast's treatment of equality can't do it\<close>
  done

text\<open>50. (What has this to do with equality?)\<close>
lemma "(\<forall>x. P(a,x) \<or> (\<forall>y. P(x,y))) \<longrightarrow> (\<exists>x. \<forall>y. P(x,y))"
  by blast

text\<open>51\<close>
lemma
  "(\<exists>z w. \<forall>x y. P(x,y) \<longleftrightarrow> (x = z \<and> y = w)) \<longrightarrow>
    (\<exists>z. \<forall>x. \<exists>w. (\<forall>y. P(x,y) \<longleftrightarrow> y=w) \<longleftrightarrow> x = z)"
  by blast

text\<open>52\<close>
text\<open>Almost the same as 51.\<close>
lemma
  "(\<exists>z w. \<forall>x y. P(x,y) \<longleftrightarrow> (x = z \<and> y = w)) \<longrightarrow>
    (\<exists>w. \<forall>y. \<exists>z. (\<forall>x. P(x,y) \<longleftrightarrow> x = z) \<longleftrightarrow> y = w)"
  by blast

text\<open>55\<close>
text\<open>Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  fast DISCOVERS who killed Agatha.\<close>
schematic_goal
  "lives(agatha) \<and> lives(butler) \<and> lives(charles) \<and>
   (killed(agatha,agatha) \<or> killed(butler,agatha) \<or> killed(charles,agatha)) \<and>
   (\<forall>x y. killed(x,y) \<longrightarrow> hates(x,y) \<and> \<not> richer(x,y)) \<and>
   (\<forall>x. hates(agatha,x) \<longrightarrow> \<not> hates(charles,x)) \<and>
   (hates(agatha,agatha) \<and> hates(agatha,charles)) \<and>
   (\<forall>x. lives(x) \<and> \<not> richer(x,agatha) \<longrightarrow> hates(butler,x)) \<and>
   (\<forall>x. hates(agatha,x) \<longrightarrow> hates(butler,x)) \<and>
   (\<forall>x. \<not> hates(x,agatha) \<or> \<not> hates(x,butler) \<or> \<not> hates(x,charles)) \<longrightarrow>
    killed(?who,agatha)"
  by fast  -- \<open>MUCH faster than blast\<close>


text\<open>56\<close>
lemma "(\<forall>x. (\<exists>y. P(y) \<and> x = f(y)) \<longrightarrow> P(x)) \<longleftrightarrow> (\<forall>x. P(x) \<longrightarrow> P(f(x)))"
  by blast

text\<open>57\<close>
lemma
  "P(f(a,b), f(b,c)) \<and> P(f(b,c), f(a,c)) \<and>
    (\<forall>x y z. P(x,y) \<and> P(y,z) \<longrightarrow> P(x,z)) \<longrightarrow> P(f(a,b), f(a,c))"
  by blast

text\<open>58  NOT PROVED AUTOMATICALLY\<close>
lemma "(\<forall>x y. f(x) = g(y)) \<longrightarrow> (\<forall>x y. f(f(x)) = f(g(y)))"
  by (slow elim: subst_context)


text\<open>59\<close>
lemma "(\<forall>x. P(x) \<longleftrightarrow> \<not> P(f(x))) \<longrightarrow> (\<exists>x. P(x) \<and> \<not> P(f(x)))"
  by blast

text\<open>60\<close>
lemma "\<forall>x. P(x,f(x)) \<longleftrightarrow> (\<exists>y. (\<forall>z. P(z,y) \<longrightarrow> P(z,f(x))) \<and> P(x,y))"
  by blast

text\<open>62 as corrected in JAR 18 (1997), page 135\<close>
lemma
  "(\<forall>x. p(a) \<and> (p(x) \<longrightarrow> p(f(x))) \<longrightarrow> p(f(f(x)))) \<longleftrightarrow>
    (\<forall>x. (\<not> p(a) \<or> p(x) \<or> p(f(f(x)))) \<and>
      (\<not> p(a) \<or> \<not> p(f(x)) \<or> p(f(f(x)))))"
  by blast

text \<open>From Davis, Obvious Logical Inferences, IJCAI-81, 530-531
  fast indeed copes!\<close>
lemma
  "(\<forall>x. F(x) \<and> \<not> G(x) \<longrightarrow> (\<exists>y. H(x,y) \<and> J(y))) \<and>
    (\<exists>x. K(x) \<and> F(x) \<and> (\<forall>y. H(x,y) \<longrightarrow> K(y))) \<and>
    (\<forall>x. K(x) \<longrightarrow> \<not> G(x)) \<longrightarrow> (\<exists>x. K(x) \<and> J(x))"
  by fast

text \<open>From Rudnicki, Obvious Inferences, JAR 3 (1987), 383-393.
  It does seem obvious!\<close>
lemma
  "(\<forall>x. F(x) \<and> \<not> G(x) \<longrightarrow> (\<exists>y. H(x,y) \<and> J(y))) \<and>
    (\<exists>x. K(x) \<and> F(x) \<and> (\<forall>y. H(x,y) \<longrightarrow> K(y))) \<and>
    (\<forall>x. K(x) \<longrightarrow> \<not> G(x)) \<longrightarrow> (\<exists>x. K(x) \<longrightarrow> \<not> G(x))"
  by fast

text \<open>Halting problem: Formulation of Li Dafa (AAR Newsletter 27, Oct 1994.)
  author U. Egly.\<close>
lemma
  "((\<exists>x. A(x) \<and> (\<forall>y. C(y) \<longrightarrow> (\<forall>z. D(x,y,z)))) \<longrightarrow>
     (\<exists>w. C(w) \<and> (\<forall>y. C(y) \<longrightarrow> (\<forall>z. D(w,y,z)))))
    \<and>
    (\<forall>w. C(w) \<and> (\<forall>u. C(u) \<longrightarrow> (\<forall>v. D(w,u,v))) \<longrightarrow>
          (\<forall>y z.
              (C(y) \<and> P(y,z) \<longrightarrow> Q(w,y,z) \<and> OO(w,g)) \<and>
              (C(y) \<and> \<not> P(y,z) \<longrightarrow> Q(w,y,z) \<and> OO(w,b))))
    \<and>
    (\<forall>w. C(w) \<and>
      (\<forall>y z.
          (C(y) \<and> P(y,z) \<longrightarrow> Q(w,y,z) \<and> OO(w,g)) \<and>
          (C(y) \<and> \<not> P(y,z) \<longrightarrow> Q(w,y,z) \<and> OO(w,b))) \<longrightarrow>
      (\<exists>v. C(v) \<and>
            (\<forall>y. ((C(y) \<and> Q(w,y,y)) \<and> OO(w,g) \<longrightarrow> \<not> P(v,y)) \<and>
                    ((C(y) \<and> Q(w,y,y)) \<and> OO(w,b) \<longrightarrow> P(v,y) \<and> OO(v,b)))))
     \<longrightarrow> \<not> (\<exists>x. A(x) \<and> (\<forall>y. C(y) \<longrightarrow> (\<forall>z. D(x,y,z))))"
  by (blast 12)
    -- \<open>Needed because the search for depths below 12 is very slow.\<close>


text \<open>
  Halting problem II: credited to M. Bruschi by Li Dafa in JAR 18(1),
  p. 105.
\<close>
lemma
  "((\<exists>x. A(x) \<and> (\<forall>y. C(y) \<longrightarrow> (\<forall>z. D(x,y,z)))) \<longrightarrow>
     (\<exists>w. C(w) \<and> (\<forall>y. C(y) \<longrightarrow> (\<forall>z. D(w,y,z)))))
    \<and>
    (\<forall>w. C(w) \<and> (\<forall>u. C(u) \<longrightarrow> (\<forall>v. D(w,u,v))) \<longrightarrow>
          (\<forall>y z.
              (C(y) \<and> P(y,z) \<longrightarrow> Q(w,y,z) \<and> OO(w,g)) \<and>
              (C(y) \<and> \<not> P(y,z) \<longrightarrow> Q(w,y,z) \<and> OO(w,b))))
    \<and>
    ((\<exists>w. C(w) \<and> (\<forall>y. (C(y) \<and> P(y,y) \<longrightarrow> Q(w,y,y) \<and> OO(w,g)) \<and>
                           (C(y) \<and> \<not> P(y,y) \<longrightarrow> Q(w,y,y) \<and> OO(w,b))))
     \<longrightarrow>
     (\<exists>v. C(v) \<and> (\<forall>y. (C(y) \<and> P(y,y) \<longrightarrow> P(v,y) \<and> OO(v,g)) \<and>
                           (C(y) \<and> \<not> P(y,y) \<longrightarrow> P(v,y) \<and> OO(v,b)))))
    \<longrightarrow>
    ((\<exists>v. C(v) \<and> (\<forall>y. (C(y) \<and> P(y,y) \<longrightarrow> P(v,y) \<and> OO(v,g)) \<and>
                           (C(y) \<and> \<not> P(y,y) \<longrightarrow> P(v,y) \<and> OO(v,b))))
     \<longrightarrow>
     (\<exists>u. C(u) \<and> (\<forall>y. (C(y) \<and> P(y,y) \<longrightarrow> \<not> P(u,y)) \<and>
                           (C(y) \<and> \<not> P(y,y) \<longrightarrow> P(u,y) \<and> OO(u,b)))))
     \<longrightarrow> \<not> (\<exists>x. A(x) \<and> (\<forall>y. C(y) \<longrightarrow> (\<forall>z. D(x,y,z))))"
  by blast

text \<open>Challenge found on info-hol.\<close>
lemma "\<forall>x. \<exists>v w. \<forall>y z. P(x) \<and> Q(y) \<longrightarrow> (P(v) \<or> R(w)) \<and> (R(z) \<longrightarrow> Q(v))"
  by blast

text \<open>
  Attributed to Lewis Carroll by S. G. Pulman. The first or last assumption
  can be deleted.\<close>
lemma
  "(\<forall>x. honest(x) \<and> industrious(x) \<longrightarrow> healthy(x)) \<and>
    \<not> (\<exists>x. grocer(x) \<and> healthy(x)) \<and>
    (\<forall>x. industrious(x) \<and> grocer(x) \<longrightarrow> honest(x)) \<and>
    (\<forall>x. cyclist(x) \<longrightarrow> industrious(x)) \<and>
    (\<forall>x. \<not> healthy(x) \<and> cyclist(x) \<longrightarrow> \<not> honest(x))
    \<longrightarrow> (\<forall>x. grocer(x) \<longrightarrow> \<not> cyclist(x))"
  by blast


(*Runtimes for old versions of this file:
Thu Jul 23 1992: loaded in 467s using iffE [on SPARC2]
Mon Nov 14 1994: loaded in 144s [on SPARC10, with deepen_tac]
Wed Nov 16 1994: loaded in 138s [after addition of norm_term_skip]
Mon Nov 21 1994: loaded in 131s [DEPTH_FIRST suppressing repetitions]

Further runtimes on a Sun-4
Tue Mar  4 1997: loaded in 93s (version 94-7)
Tue Mar  4 1997: loaded in 89s
Thu Apr  3 1997: loaded in 44s--using mostly Blast_tac
Thu Apr  3 1997: loaded in 96s--addition of two Halting Probs
Thu Apr  3 1997: loaded in 98s--using lim-1 for all haz rules
Tue Dec  2 1997: loaded in 107s--added 46; new equalSubst
Fri Dec 12 1997: loaded in 91s--faster proof reconstruction
Thu Dec 18 1997: loaded in 94s--two new "obvious theorems" (??)
*)

end
