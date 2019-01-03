(*  Title:      FOL/ex/Classical.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section \<open>Classical Predicate Calculus Problems\<close>

theory Classical
imports FOL
begin

lemma \<open>(P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longrightarrow> Q) \<or> (P \<longrightarrow> R)\<close>
  by blast


subsubsection \<open>If and only if\<close>

lemma \<open>(P \<longleftrightarrow> Q) \<longleftrightarrow> (Q \<longleftrightarrow> P)\<close>
  by blast

lemma \<open>\<not> (P \<longleftrightarrow> \<not> P)\<close>
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
lemma \<open>(P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> \<not> P)\<close>
  by blast

text\<open>2\<close>
lemma \<open>\<not> \<not> P \<longleftrightarrow> P\<close>
  by blast

text\<open>3\<close>
lemma \<open>\<not> (P \<longrightarrow> Q) \<longrightarrow> (Q \<longrightarrow> P)\<close>
  by blast

text\<open>4\<close>
lemma \<open>(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)\<close>
  by blast

text\<open>5\<close>
lemma \<open>((P \<or> Q) \<longrightarrow> (P \<or> R)) \<longrightarrow> (P \<or> (Q \<longrightarrow> R))\<close>
  by blast

text\<open>6\<close>
lemma \<open>P \<or> \<not> P\<close>
  by blast

text\<open>7\<close>
lemma \<open>P \<or> \<not> \<not> \<not> P\<close>
  by blast

text\<open>8. Peirce's law\<close>
lemma \<open>((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P\<close>
  by blast

text\<open>9\<close>
lemma \<open>((P \<or> Q) \<and> (\<not> P \<or> Q) \<and> (P \<or> \<not> Q)) \<longrightarrow> \<not> (\<not> P \<or> \<not> Q)\<close>
  by blast

text\<open>10\<close>
lemma \<open>(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)\<close>
  by blast

text\<open>11. Proved in each direction (incorrectly, says Pelletier!!)\<close>
lemma \<open>P \<longleftrightarrow> P\<close>
  by blast

text\<open>12. "Dijkstra's law"\<close>
lemma \<open>((P \<longleftrightarrow> Q) \<longleftrightarrow> R) \<longleftrightarrow> (P \<longleftrightarrow> (Q \<longleftrightarrow> R))\<close>
  by blast

text\<open>13. Distributive law\<close>
lemma \<open>P \<or> (Q \<and> R) \<longleftrightarrow> (P \<or> Q) \<and> (P \<or> R)\<close>
  by blast

text\<open>14\<close>
lemma \<open>(P \<longleftrightarrow> Q) \<longleftrightarrow> ((Q \<or> \<not> P) \<and> (\<not> Q \<or> P))\<close>
  by blast

text\<open>15\<close>
lemma \<open>(P \<longrightarrow> Q) \<longleftrightarrow> (\<not> P \<or> Q)\<close>
  by blast

text\<open>16\<close>
lemma \<open>(P \<longrightarrow> Q) \<or> (Q \<longrightarrow> P)\<close>
  by blast

text\<open>17\<close>
lemma \<open>((P \<and> (Q \<longrightarrow> R)) \<longrightarrow> S) \<longleftrightarrow> ((\<not> P \<or> Q \<or> S) \<and> (\<not> P \<or> \<not> R \<or> S))\<close>
  by blast


subsection \<open>Classical Logic: examples with quantifiers\<close>

lemma \<open>(\<forall>x. P(x) \<and> Q(x)) \<longleftrightarrow> (\<forall>x. P(x)) \<and> (\<forall>x. Q(x))\<close>
  by blast

lemma \<open>(\<exists>x. P \<longrightarrow> Q(x)) \<longleftrightarrow> (P \<longrightarrow> (\<exists>x. Q(x)))\<close>
  by blast

lemma \<open>(\<exists>x. P(x) \<longrightarrow> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<longrightarrow> Q\<close>
  by blast

lemma \<open>(\<forall>x. P(x)) \<or> Q \<longleftrightarrow> (\<forall>x. P(x) \<or> Q)\<close>
  by blast

text\<open>Discussed in Avron, Gentzen-Type Systems, Resolution and Tableaux,
  JAR 10 (265-281), 1993.  Proof is trivial!\<close>
lemma \<open>\<not> ((\<exists>x. \<not> P(x)) \<and> ((\<exists>x. P(x)) \<or> (\<exists>x. P(x) \<and> Q(x))) \<and> \<not> (\<exists>x. P(x)))\<close>
  by blast


subsection \<open>Problems requiring quantifier duplication\<close>

text\<open>Theorem B of Peter Andrews, Theorem Proving via General Matings,
  JACM 28 (1981).\<close>
lemma \<open>(\<exists>x. \<forall>y. P(x) \<longleftrightarrow> P(y)) \<longrightarrow> ((\<exists>x. P(x)) \<longleftrightarrow> (\<forall>y. P(y)))\<close>
  by blast

text\<open>Needs multiple instantiation of ALL.\<close>
lemma \<open>(\<forall>x. P(x) \<longrightarrow> P(f(x))) \<and> P(d) \<longrightarrow> P(f(f(f(d))))\<close>
  by blast

text\<open>Needs double instantiation of the quantifier\<close>
lemma \<open>\<exists>x. P(x) \<longrightarrow> P(a) \<and> P(b)\<close>
  by blast

lemma \<open>\<exists>z. P(z) \<longrightarrow> (\<forall>x. P(x))\<close>
  by blast

lemma \<open>\<exists>x. (\<exists>y. P(y)) \<longrightarrow> P(x)\<close>
  by blast

text\<open>V. Lifschitz, What Is the Inverse Method?, JAR 5 (1989), 1--23. NOT PROVED.\<close>
lemma
  \<open>\<exists>x x'. \<forall>y. \<exists>z z'.
    (\<not> P(y,y) \<or> P(x,x) \<or> \<not> S(z,x)) \<and>
    (S(x,y) \<or> \<not> S(y,z) \<or> Q(z',z')) \<and>
    (Q(x',y) \<or> \<not> Q(y,z') \<or> S(x',x'))\<close>
  oops


subsection \<open>Hard examples with quantifiers\<close>

text\<open>18\<close>
lemma \<open>\<exists>y. \<forall>x. P(y) \<longrightarrow> P(x)\<close>
  by blast

text\<open>19\<close>
lemma \<open>\<exists>x. \<forall>y z. (P(y) \<longrightarrow> Q(z)) \<longrightarrow> (P(x) \<longrightarrow> Q(x))\<close>
  by blast

text\<open>20\<close>
lemma \<open>(\<forall>x y. \<exists>z. \<forall>w. (P(x) \<and> Q(y) \<longrightarrow> R(z) \<and> S(w)))
  \<longrightarrow> (\<exists>x y. P(x) \<and> Q(y)) \<longrightarrow> (\<exists>z. R(z))\<close>
  by blast

text\<open>21\<close>
lemma \<open>(\<exists>x. P \<longrightarrow> Q(x)) \<and> (\<exists>x. Q(x) \<longrightarrow> P) \<longrightarrow> (\<exists>x. P \<longleftrightarrow> Q(x))\<close>
  by blast

text\<open>22\<close>
lemma \<open>(\<forall>x. P \<longleftrightarrow> Q(x)) \<longrightarrow> (P \<longleftrightarrow> (\<forall>x. Q(x)))\<close>
  by blast

text\<open>23\<close>
lemma \<open>(\<forall>x. P \<or> Q(x)) \<longleftrightarrow> (P \<or> (\<forall>x. Q(x)))\<close>
  by blast

text\<open>24\<close>
lemma
  \<open>\<not> (\<exists>x. S(x) \<and> Q(x)) \<and> (\<forall>x. P(x) \<longrightarrow> Q(x) \<or> R(x)) \<and>
    (\<not> (\<exists>x. P(x)) \<longrightarrow> (\<exists>x. Q(x))) \<and> (\<forall>x. Q(x) \<or> R(x) \<longrightarrow> S(x))
    \<longrightarrow> (\<exists>x. P(x) \<and> R(x))\<close>
  by blast

text\<open>25\<close>
lemma
  \<open>(\<exists>x. P(x)) \<and>
    (\<forall>x. L(x) \<longrightarrow> \<not> (M(x) \<and> R(x))) \<and>
    (\<forall>x. P(x) \<longrightarrow> (M(x) \<and> L(x))) \<and>
    ((\<forall>x. P(x) \<longrightarrow> Q(x)) \<or> (\<exists>x. P(x) \<and> R(x)))
    \<longrightarrow> (\<exists>x. Q(x) \<and> P(x))\<close>
  by blast

text\<open>26\<close>
lemma
  \<open>((\<exists>x. p(x)) \<longleftrightarrow> (\<exists>x. q(x))) \<and>
    (\<forall>x. \<forall>y. p(x) \<and> q(y) \<longrightarrow> (r(x) \<longleftrightarrow> s(y)))
  \<longrightarrow> ((\<forall>x. p(x) \<longrightarrow> r(x)) \<longleftrightarrow> (\<forall>x. q(x) \<longrightarrow> s(x)))\<close>
  by blast

text\<open>27\<close>
lemma
  \<open>(\<exists>x. P(x) \<and> \<not> Q(x)) \<and>
    (\<forall>x. P(x) \<longrightarrow> R(x)) \<and>
    (\<forall>x. M(x) \<and> L(x) \<longrightarrow> P(x)) \<and>
    ((\<exists>x. R(x) \<and> \<not> Q(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> \<not> R(x)))
  \<longrightarrow> (\<forall>x. M(x) \<longrightarrow> \<not> L(x))\<close>
  by blast

text\<open>28. AMENDED\<close>
lemma
  \<open>(\<forall>x. P(x) \<longrightarrow> (\<forall>x. Q(x))) \<and>
    ((\<forall>x. Q(x) \<or> R(x)) \<longrightarrow> (\<exists>x. Q(x) \<and> S(x))) \<and>
    ((\<exists>x. S(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> M(x)))
  \<longrightarrow> (\<forall>x. P(x) \<and> L(x) \<longrightarrow> M(x))\<close>
  by blast

text\<open>29. Essentially the same as Principia Mathematica *11.71\<close>
lemma
  \<open>(\<exists>x. P(x)) \<and> (\<exists>y. Q(y))
    \<longrightarrow> ((\<forall>x. P(x) \<longrightarrow> R(x)) \<and> (\<forall>y. Q(y) \<longrightarrow> S(y)) \<longleftrightarrow>
      (\<forall>x y. P(x) \<and> Q(y) \<longrightarrow> R(x) \<and> S(y)))\<close>
  by blast

text\<open>30\<close>
lemma
  \<open>(\<forall>x. P(x) \<or> Q(x) \<longrightarrow> \<not> R(x)) \<and>
    (\<forall>x. (Q(x) \<longrightarrow> \<not> S(x)) \<longrightarrow> P(x) \<and> R(x))
    \<longrightarrow> (\<forall>x. S(x))\<close>
  by blast

text\<open>31\<close>
lemma
  \<open>\<not> (\<exists>x. P(x) \<and> (Q(x) \<or> R(x))) \<and>
    (\<exists>x. L(x) \<and> P(x)) \<and>
    (\<forall>x. \<not> R(x) \<longrightarrow> M(x))
  \<longrightarrow> (\<exists>x. L(x) \<and> M(x))\<close>
  by blast

text\<open>32\<close>
lemma
  \<open>(\<forall>x. P(x) \<and> (Q(x) \<or> R(x)) \<longrightarrow> S(x)) \<and>
    (\<forall>x. S(x) \<and> R(x) \<longrightarrow> L(x)) \<and>
    (\<forall>x. M(x) \<longrightarrow> R(x))
  \<longrightarrow> (\<forall>x. P(x) \<and> M(x) \<longrightarrow> L(x))\<close>
  by blast

text\<open>33\<close>
lemma
  \<open>(\<forall>x. P(a) \<and> (P(x) \<longrightarrow> P(b)) \<longrightarrow> P(c)) \<longleftrightarrow>
    (\<forall>x. (\<not> P(a) \<or> P(x) \<or> P(c)) \<and> (\<not> P(a) \<or> \<not> P(b) \<or> P(c)))\<close>
  by blast

text\<open>34. AMENDED (TWICE!!). Andrews's challenge.\<close>
lemma
  \<open>((\<exists>x. \<forall>y. p(x) \<longleftrightarrow> p(y)) \<longleftrightarrow> ((\<exists>x. q(x)) \<longleftrightarrow> (\<forall>y. p(y)))) \<longleftrightarrow>
    ((\<exists>x. \<forall>y. q(x) \<longleftrightarrow> q(y)) \<longleftrightarrow> ((\<exists>x. p(x)) \<longleftrightarrow> (\<forall>y. q(y))))\<close>
  by blast

text\<open>35\<close>
lemma \<open>\<exists>x y. P(x,y) \<longrightarrow> (\<forall>u v. P(u,v))\<close>
  by blast

text\<open>36\<close>
lemma
  \<open>(\<forall>x. \<exists>y. J(x,y)) \<and>
    (\<forall>x. \<exists>y. G(x,y)) \<and>
    (\<forall>x y. J(x,y) \<or> G(x,y) \<longrightarrow> (\<forall>z. J(y,z) \<or> G(y,z) \<longrightarrow> H(x,z)))
  \<longrightarrow> (\<forall>x. \<exists>y. H(x,y))\<close>
  by blast

text\<open>37\<close>
lemma
  \<open>(\<forall>z. \<exists>w. \<forall>x. \<exists>y.
    (P(x,z) \<longrightarrow> P(y,w)) \<and> P(y,z) \<and> (P(y,w) \<longrightarrow> (\<exists>u. Q(u,w)))) \<and>
    (\<forall>x z. \<not> P(x,z) \<longrightarrow> (\<exists>y. Q(y,z))) \<and>
    ((\<exists>x y. Q(x,y)) \<longrightarrow> (\<forall>x. R(x,x)))
  \<longrightarrow> (\<forall>x. \<exists>y. R(x,y))\<close>
  by blast

text\<open>38\<close>
lemma
  \<open>(\<forall>x. p(a) \<and> (p(x) \<longrightarrow> (\<exists>y. p(y) \<and> r(x,y))) \<longrightarrow>
    (\<exists>z. \<exists>w. p(z) \<and> r(x,w) \<and> r(w,z)))  \<longleftrightarrow>
    (\<forall>x. (\<not> p(a) \<or> p(x) \<or> (\<exists>z. \<exists>w. p(z) \<and> r(x,w) \<and> r(w,z))) \<and>
      (\<not> p(a) \<or> \<not> (\<exists>y. p(y) \<and> r(x,y)) \<or>
      (\<exists>z. \<exists>w. p(z) \<and> r(x,w) \<and> r(w,z))))\<close>
  by blast

text\<open>39\<close>
lemma \<open>\<not> (\<exists>x. \<forall>y. F(y,x) \<longleftrightarrow> \<not> F(y,y))\<close>
  by blast

text\<open>40. AMENDED\<close>
lemma
  \<open>(\<exists>y. \<forall>x. F(x,y) \<longleftrightarrow> F(x,x)) \<longrightarrow>
    \<not> (\<forall>x. \<exists>y. \<forall>z. F(z,y) \<longleftrightarrow> \<not> F(z,x))\<close>
  by blast

text\<open>41\<close>
lemma
  \<open>(\<forall>z. \<exists>y. \<forall>x. f(x,y) \<longleftrightarrow> f(x,z) \<and> \<not> f(x,x))
    \<longrightarrow> \<not> (\<exists>z. \<forall>x. f(x,z))\<close>
  by blast

text\<open>42\<close>
lemma \<open>\<not> (\<exists>y. \<forall>x. p(x,y) \<longleftrightarrow> \<not> (\<exists>z. p(x,z) \<and> p(z,x)))\<close>
  by blast

text\<open>43\<close>
lemma
  \<open>(\<forall>x. \<forall>y. q(x,y) \<longleftrightarrow> (\<forall>z. p(z,x) \<longleftrightarrow> p(z,y)))
    \<longrightarrow> (\<forall>x. \<forall>y. q(x,y) \<longleftrightarrow> q(y,x))\<close>
  by blast

text \<open>
  Other proofs: Can use \<open>auto\<close>, which cheats by using rewriting!
  \<open>Deepen_tac\<close> alone requires 253 secs.  Or
  \<open>by (mini_tac 1 THEN Deepen_tac 5 1)\<close>.
\<close>

text\<open>44\<close>
lemma
  \<open>(\<forall>x. f(x) \<longrightarrow> (\<exists>y. g(y) \<and> h(x,y) \<and> (\<exists>y. g(y) \<and> \<not> h(x,y)))) \<and>
    (\<exists>x. j(x) \<and> (\<forall>y. g(y) \<longrightarrow> h(x,y)))
  \<longrightarrow> (\<exists>x. j(x) \<and> \<not> f(x))\<close>
  by blast

text\<open>45\<close>
lemma
  \<open>(\<forall>x. f(x) \<and> (\<forall>y. g(y) \<and> h(x,y) \<longrightarrow> j(x,y))
      \<longrightarrow> (\<forall>y. g(y) \<and> h(x,y) \<longrightarrow> k(y))) \<and>
      \<not> (\<exists>y. l(y) \<and> k(y)) \<and>
      (\<exists>x. f(x) \<and> (\<forall>y. h(x,y) \<longrightarrow> l(y)) \<and> (\<forall>y. g(y) \<and> h(x,y) \<longrightarrow> j(x,y)))
      \<longrightarrow> (\<exists>x. f(x) \<and> \<not> (\<exists>y. g(y) \<and> h(x,y)))\<close>
  by blast


text\<open>46\<close>
lemma
  \<open>(\<forall>x. f(x) \<and> (\<forall>y. f(y) \<and> h(y,x) \<longrightarrow> g(y)) \<longrightarrow> g(x)) \<and>
      ((\<exists>x. f(x) \<and> \<not> g(x)) \<longrightarrow>
       (\<exists>x. f(x) \<and> \<not> g(x) \<and> (\<forall>y. f(y) \<and> \<not> g(y) \<longrightarrow> j(x,y)))) \<and>
      (\<forall>x y. f(x) \<and> f(y) \<and> h(x,y) \<longrightarrow> \<not> j(y,x))
      \<longrightarrow> (\<forall>x. f(x) \<longrightarrow> g(x))\<close>
  by blast


subsection \<open>Problems (mainly) involving equality or functions\<close>

text\<open>48\<close>
lemma \<open>(a = b \<or> c = d) \<and> (a = c \<or> b = d) \<longrightarrow> a = d \<or> b = c\<close>
  by blast

text\<open>49. NOT PROVED AUTOMATICALLY. Hard because it involves substitution for
  Vars; the type constraint ensures that x,y,z have the same type as a,b,u.\<close>
lemma
  \<open>(\<exists>x y::'a. \<forall>z. z = x \<or> z = y) \<and> P(a) \<and> P(b) \<and> a \<noteq> b \<longrightarrow> (\<forall>u::'a. P(u))\<close>
  apply safe
  apply (rule_tac x = \<open>a\<close> in allE, assumption)
  apply (rule_tac x = \<open>b\<close> in allE, assumption)
  apply fast  \<comment> \<open>blast's treatment of equality can't do it\<close>
  done

text\<open>50. (What has this to do with equality?)\<close>
lemma \<open>(\<forall>x. P(a,x) \<or> (\<forall>y. P(x,y))) \<longrightarrow> (\<exists>x. \<forall>y. P(x,y))\<close>
  by blast

text\<open>51\<close>
lemma
  \<open>(\<exists>z w. \<forall>x y. P(x,y) \<longleftrightarrow> (x = z \<and> y = w)) \<longrightarrow>
    (\<exists>z. \<forall>x. \<exists>w. (\<forall>y. P(x,y) \<longleftrightarrow> y=w) \<longleftrightarrow> x = z)\<close>
  by blast

text\<open>52\<close>
text\<open>Almost the same as 51.\<close>
lemma
  \<open>(\<exists>z w. \<forall>x y. P(x,y) \<longleftrightarrow> (x = z \<and> y = w)) \<longrightarrow>
    (\<exists>w. \<forall>y. \<exists>z. (\<forall>x. P(x,y) \<longleftrightarrow> x = z) \<longleftrightarrow> y = w)\<close>
  by blast

text\<open>55\<close>
text\<open>Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  fast DISCOVERS who killed Agatha.\<close>
schematic_goal
  \<open>lives(agatha) \<and> lives(butler) \<and> lives(charles) \<and>
   (killed(agatha,agatha) \<or> killed(butler,agatha) \<or> killed(charles,agatha)) \<and>
   (\<forall>x y. killed(x,y) \<longrightarrow> hates(x,y) \<and> \<not> richer(x,y)) \<and>
   (\<forall>x. hates(agatha,x) \<longrightarrow> \<not> hates(charles,x)) \<and>
   (hates(agatha,agatha) \<and> hates(agatha,charles)) \<and>
   (\<forall>x. lives(x) \<and> \<not> richer(x,agatha) \<longrightarrow> hates(butler,x)) \<and>
   (\<forall>x. hates(agatha,x) \<longrightarrow> hates(butler,x)) \<and>
   (\<forall>x. \<not> hates(x,agatha) \<or> \<not> hates(x,butler) \<or> \<not> hates(x,charles)) \<longrightarrow>
    killed(?who,agatha)\<close>
  by fast  \<comment> \<open>MUCH faster than blast\<close>


text\<open>56\<close>
lemma \<open>(\<forall>x. (\<exists>y. P(y) \<and> x = f(y)) \<longrightarrow> P(x)) \<longleftrightarrow> (\<forall>x. P(x) \<longrightarrow> P(f(x)))\<close>
  by blast

text\<open>57\<close>
lemma
  \<open>P(f(a,b), f(b,c)) \<and> P(f(b,c), f(a,c)) \<and>
    (\<forall>x y z. P(x,y) \<and> P(y,z) \<longrightarrow> P(x,z)) \<longrightarrow> P(f(a,b), f(a,c))\<close>
  by blast

text\<open>58  NOT PROVED AUTOMATICALLY\<close>
lemma \<open>(\<forall>x y. f(x) = g(y)) \<longrightarrow> (\<forall>x y. f(f(x)) = f(g(y)))\<close>
  by (slow elim: subst_context)


text\<open>59\<close>
lemma \<open>(\<forall>x. P(x) \<longleftrightarrow> \<not> P(f(x))) \<longrightarrow> (\<exists>x. P(x) \<and> \<not> P(f(x)))\<close>
  by blast

text\<open>60\<close>
lemma \<open>\<forall>x. P(x,f(x)) \<longleftrightarrow> (\<exists>y. (\<forall>z. P(z,y) \<longrightarrow> P(z,f(x))) \<and> P(x,y))\<close>
  by blast

text\<open>62 as corrected in JAR 18 (1997), page 135\<close>
lemma
  \<open>(\<forall>x. p(a) \<and> (p(x) \<longrightarrow> p(f(x))) \<longrightarrow> p(f(f(x)))) \<longleftrightarrow>
    (\<forall>x. (\<not> p(a) \<or> p(x) \<or> p(f(f(x)))) \<and>
      (\<not> p(a) \<or> \<not> p(f(x)) \<or> p(f(f(x)))))\<close>
  by blast

text \<open>From Davis, Obvious Logical Inferences, IJCAI-81, 530-531
  fast indeed copes!\<close>
lemma
  \<open>(\<forall>x. F(x) \<and> \<not> G(x) \<longrightarrow> (\<exists>y. H(x,y) \<and> J(y))) \<and>
    (\<exists>x. K(x) \<and> F(x) \<and> (\<forall>y. H(x,y) \<longrightarrow> K(y))) \<and>
    (\<forall>x. K(x) \<longrightarrow> \<not> G(x)) \<longrightarrow> (\<exists>x. K(x) \<and> J(x))\<close>
  by fast

text \<open>From Rudnicki, Obvious Inferences, JAR 3 (1987), 383-393.
  It does seem obvious!\<close>
lemma
  \<open>(\<forall>x. F(x) \<and> \<not> G(x) \<longrightarrow> (\<exists>y. H(x,y) \<and> J(y))) \<and>
    (\<exists>x. K(x) \<and> F(x) \<and> (\<forall>y. H(x,y) \<longrightarrow> K(y))) \<and>
    (\<forall>x. K(x) \<longrightarrow> \<not> G(x)) \<longrightarrow> (\<exists>x. K(x) \<longrightarrow> \<not> G(x))\<close>
  by fast

text \<open>Halting problem: Formulation of Li Dafa (AAR Newsletter 27, Oct 1994.)
  author U. Egly.\<close>
lemma
  \<open>((\<exists>x. A(x) \<and> (\<forall>y. C(y) \<longrightarrow> (\<forall>z. D(x,y,z)))) \<longrightarrow>
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
     \<longrightarrow> \<not> (\<exists>x. A(x) \<and> (\<forall>y. C(y) \<longrightarrow> (\<forall>z. D(x,y,z))))\<close>
  by (blast 12)
    \<comment> \<open>Needed because the search for depths below 12 is very slow.\<close>


text \<open>
  Halting problem II: credited to M. Bruschi by Li Dafa in JAR 18(1),
  p. 105.
\<close>
lemma
  \<open>((\<exists>x. A(x) \<and> (\<forall>y. C(y) \<longrightarrow> (\<forall>z. D(x,y,z)))) \<longrightarrow>
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
     \<longrightarrow> \<not> (\<exists>x. A(x) \<and> (\<forall>y. C(y) \<longrightarrow> (\<forall>z. D(x,y,z))))\<close>
  by blast

text \<open>Challenge found on info-hol.\<close>
lemma \<open>\<forall>x. \<exists>v w. \<forall>y z. P(x) \<and> Q(y) \<longrightarrow> (P(v) \<or> R(w)) \<and> (R(z) \<longrightarrow> Q(v))\<close>
  by blast

text \<open>
  Attributed to Lewis Carroll by S. G. Pulman. The first or last assumption
  can be deleted.\<close>
lemma
  \<open>(\<forall>x. honest(x) \<and> industrious(x) \<longrightarrow> healthy(x)) \<and>
    \<not> (\<exists>x. grocer(x) \<and> healthy(x)) \<and>
    (\<forall>x. industrious(x) \<and> grocer(x) \<longrightarrow> honest(x)) \<and>
    (\<forall>x. cyclist(x) \<longrightarrow> industrious(x)) \<and>
    (\<forall>x. \<not> healthy(x) \<and> cyclist(x) \<longrightarrow> \<not> honest(x))
    \<longrightarrow> (\<forall>x. grocer(x) \<longrightarrow> \<not> cyclist(x))\<close>
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
