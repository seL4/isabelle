(*  Title:      HOL/ex/Classical.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

section\<open>Classical Predicate Calculus Problems\<close>

theory Classical imports Main begin

subsection\<open>Traditional Classical Reasoner\<close>

text\<open>The machine "griffon" mentioned below is a 2.5GHz Power Mac G5.\<close>

text\<open>Taken from \<open>FOL/Classical.thy\<close>. When porting examples from
first-order logic, beware of the precedence of \<open>=\<close> versus \<open>\<leftrightarrow>\<close>.\<close>

lemma "(P \<longrightarrow> Q \<or> R) \<longrightarrow> (P\<longrightarrow>Q) \<or> (P\<longrightarrow>R)"
by blast

text\<open>If and only if\<close>

lemma "(P=Q) = (Q = (P::bool))"
by blast

lemma "\<not> (P = (\<not>P))"
by blast


text\<open>Sample problems from
  F. J. Pelletier,
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.

The hardest problems -- judging by experience with several theorem provers,
including matrix ones -- are 34 and 43.
\<close>

subsubsection\<open>Pelletier's examples\<close>

text\<open>1\<close>
lemma "(P\<longrightarrow>Q)  =  (\<not>Q \<longrightarrow> \<not>P)"
by blast

text\<open>2\<close>
lemma "(\<not> \<not> P) =  P"
by blast

text\<open>3\<close>
lemma "\<not>(P\<longrightarrow>Q) \<longrightarrow> (Q\<longrightarrow>P)"
by blast

text\<open>4\<close>
lemma "(\<not>P\<longrightarrow>Q)  =  (\<not>Q \<longrightarrow> P)"
by blast

text\<open>5\<close>
lemma "((P\<or>Q)\<longrightarrow>(P\<or>R)) \<longrightarrow> (P\<or>(Q\<longrightarrow>R))"
by blast

text\<open>6\<close>
lemma "P \<or> \<not> P"
by blast

text\<open>7\<close>
lemma "P \<or> \<not> \<not> \<not> P"
by blast

text\<open>8.  Peirce's law\<close>
lemma "((P\<longrightarrow>Q) \<longrightarrow> P)  \<longrightarrow>  P"
by blast

text\<open>9\<close>
lemma "((P\<or>Q) \<and> (\<not>P\<or>Q) \<and> (P\<or> \<not>Q)) \<longrightarrow> \<not> (\<not>P \<or> \<not>Q)"
by blast

text\<open>10\<close>
lemma "(Q\<longrightarrow>R) \<and> (R\<longrightarrow>P\<and>Q) \<and> (P\<longrightarrow>Q\<or>R) \<longrightarrow> (P=Q)"
by blast

text\<open>11.  Proved in each direction (incorrectly, says Pelletier!!)\<close>
lemma "P=(P::bool)"
by blast

text\<open>12.  "Dijkstra's law"\<close>
lemma "((P = Q) = R) = (P = (Q = R))"
by blast

text\<open>13.  Distributive law\<close>
lemma "(P \<or> (Q \<and> R)) = ((P \<or> Q) \<and> (P \<or> R))"
by blast

text\<open>14\<close>
lemma "(P = Q) = ((Q \<or> \<not>P) \<and> (\<not>Q\<or>P))"
by blast

text\<open>15\<close>
lemma "(P \<longrightarrow> Q) = (\<not>P \<or> Q)"
by blast

text\<open>16\<close>
lemma "(P\<longrightarrow>Q) \<or> (Q\<longrightarrow>P)"
by blast

text\<open>17\<close>
lemma "((P \<and> (Q\<longrightarrow>R))\<longrightarrow>S)  =  ((\<not>P \<or> Q \<or> S) \<and> (\<not>P \<or> \<not>R \<or> S))"
by blast

subsubsection\<open>Classical Logic: examples with quantifiers\<close>

lemma "(\<forall>x. P(x) \<and> Q(x)) = ((\<forall>x. P(x)) \<and> (\<forall>x. Q(x)))"
by blast

lemma "(\<exists>x. P\<longrightarrow>Q(x))  =  (P \<longrightarrow> (\<exists>x. Q(x)))"
by blast

lemma "(\<exists>x. P(x)\<longrightarrow>Q) = ((\<forall>x. P(x)) \<longrightarrow> Q)"
by blast

lemma "((\<forall>x. P(x)) \<or> Q)  =  (\<forall>x. P(x) \<or> Q)"
by blast

text\<open>From Wishnu Prasetya\<close>
lemma "(\<forall>x. Q(x) \<longrightarrow> R(x)) \<and> \<not>R(a) \<and> (\<forall>x. \<not>R(x) \<and> \<not>Q(x) \<longrightarrow> P(b) \<or> Q(b))
    \<longrightarrow> P(b) \<or> R(b)"
by blast


subsubsection\<open>Problems requiring quantifier duplication\<close>

text\<open>Theorem B of Peter Andrews, Theorem Proving via General Matings,
  JACM 28 (1981).\<close>
lemma "(\<exists>x. \<forall>y. P(x) = P(y)) \<longrightarrow> ((\<exists>x. P(x)) = (\<forall>y. P(y)))"
by blast

text\<open>Needs multiple instantiation of the quantifier.\<close>
lemma "(\<forall>x. P(x)\<longrightarrow>P(f(x)))  \<and>  P(d)\<longrightarrow>P(f(f(f(d))))"
by blast

text\<open>Needs double instantiation of the quantifier\<close>
lemma "\<exists>x. P(x) \<longrightarrow> P(a) \<and> P(b)"
by blast

lemma "\<exists>z. P(z) \<longrightarrow> (\<forall>x. P(x))"
by blast

lemma "\<exists>x. (\<exists>y. P(y)) \<longrightarrow> P(x)"
by blast

subsubsection\<open>Hard examples with quantifiers\<close>

text\<open>Problem 18\<close>
lemma "\<exists>y. \<forall>x. P(y)\<longrightarrow>P(x)"
by blast

text\<open>Problem 19\<close>
lemma "\<exists>x. \<forall>y z. (P(y)\<longrightarrow>Q(z)) \<longrightarrow> (P(x)\<longrightarrow>Q(x))"
by blast

text\<open>Problem 20\<close>
lemma "(\<forall>x y. \<exists>z. \<forall>w. (P(x)\<and>Q(y)\<longrightarrow>R(z)\<and>S(w)))
    \<longrightarrow> (\<exists>x y. P(x) \<and> Q(y)) \<longrightarrow> (\<exists>z. R(z))"
by blast

text\<open>Problem 21\<close>
lemma "(\<exists>x. P\<longrightarrow>Q(x)) \<and> (\<exists>x. Q(x)\<longrightarrow>P) \<longrightarrow> (\<exists>x. P=Q(x))"
by blast

text\<open>Problem 22\<close>
lemma "(\<forall>x. P = Q(x))  \<longrightarrow>  (P = (\<forall>x. Q(x)))"
by blast

text\<open>Problem 23\<close>
lemma "(\<forall>x. P \<or> Q(x))  =  (P \<or> (\<forall>x. Q(x)))"
by blast

text\<open>Problem 24\<close>
lemma "\<not>(\<exists>x. S(x)\<and>Q(x)) \<and> (\<forall>x. P(x) \<longrightarrow> Q(x)\<or>R(x)) \<and>
     (\<not>(\<exists>x. P(x)) \<longrightarrow> (\<exists>x. Q(x))) \<and> (\<forall>x. Q(x)\<or>R(x) \<longrightarrow> S(x))
    \<longrightarrow> (\<exists>x. P(x)\<and>R(x))"
by blast

text\<open>Problem 25\<close>
lemma "(\<exists>x. P(x)) \<and>
        (\<forall>x. L(x) \<longrightarrow> \<not> (M(x) \<and> R(x))) \<and>
        (\<forall>x. P(x) \<longrightarrow> (M(x) \<and> L(x))) \<and>
        ((\<forall>x. P(x)\<longrightarrow>Q(x)) \<or> (\<exists>x. P(x)\<and>R(x)))
    \<longrightarrow> (\<exists>x. Q(x)\<and>P(x))"
by blast

text\<open>Problem 26\<close>
lemma "((\<exists>x. p(x)) = (\<exists>x. q(x))) \<and>
      (\<forall>x. \<forall>y. p(x) \<and> q(y) \<longrightarrow> (r(x) = s(y)))
  \<longrightarrow> ((\<forall>x. p(x)\<longrightarrow>r(x)) = (\<forall>x. q(x)\<longrightarrow>s(x)))"
by blast

text\<open>Problem 27\<close>
lemma "(\<exists>x. P(x) \<and> \<not>Q(x)) \<and>
              (\<forall>x. P(x) \<longrightarrow> R(x)) \<and>
              (\<forall>x. M(x) \<and> L(x) \<longrightarrow> P(x)) \<and>
              ((\<exists>x. R(x) \<and> \<not> Q(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> \<not> R(x)))
          \<longrightarrow> (\<forall>x. M(x) \<longrightarrow> \<not>L(x))"
by blast

text\<open>Problem 28.  AMENDED\<close>
lemma "(\<forall>x. P(x) \<longrightarrow> (\<forall>x. Q(x))) \<and>
        ((\<forall>x. Q(x)\<or>R(x)) \<longrightarrow> (\<exists>x. Q(x)\<and>S(x))) \<and>
        ((\<exists>x. S(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> M(x)))
    \<longrightarrow> (\<forall>x. P(x) \<and> L(x) \<longrightarrow> M(x))"
by blast

text\<open>Problem 29.  Essentially the same as Principia Mathematica *11.71\<close>
lemma "(\<exists>x. F(x)) \<and> (\<exists>y. G(y))
    \<longrightarrow> ( ((\<forall>x. F(x)\<longrightarrow>H(x)) \<and> (\<forall>y. G(y)\<longrightarrow>J(y)))  =
          (\<forall>x y. F(x) \<and> G(y) \<longrightarrow> H(x) \<and> J(y)))"
by blast

text\<open>Problem 30\<close>
lemma "(\<forall>x. P(x) \<or> Q(x) \<longrightarrow> \<not> R(x)) \<and>
        (\<forall>x. (Q(x) \<longrightarrow> \<not> S(x)) \<longrightarrow> P(x) \<and> R(x))
    \<longrightarrow> (\<forall>x. S(x))"
by blast

text\<open>Problem 31\<close>
lemma "\<not>(\<exists>x. P(x) \<and> (Q(x) \<or> R(x))) \<and>
        (\<exists>x. L(x) \<and> P(x)) \<and>
        (\<forall>x. \<not> R(x) \<longrightarrow> M(x))
    \<longrightarrow> (\<exists>x. L(x) \<and> M(x))"
by blast

text\<open>Problem 32\<close>
lemma "(\<forall>x. P(x) \<and> (Q(x)\<or>R(x))\<longrightarrow>S(x)) \<and>
        (\<forall>x. S(x) \<and> R(x) \<longrightarrow> L(x)) \<and>
        (\<forall>x. M(x) \<longrightarrow> R(x))
    \<longrightarrow> (\<forall>x. P(x) \<and> M(x) \<longrightarrow> L(x))"
by blast

text\<open>Problem 33\<close>
lemma "(\<forall>x. P(a) \<and> (P(x)\<longrightarrow>P(b))\<longrightarrow>P(c))  =
     (\<forall>x. (\<not>P(a) \<or> P(x) \<or> P(c)) \<and> (\<not>P(a) \<or> \<not>P(b) \<or> P(c)))"
by blast

text\<open>Problem 34  AMENDED (TWICE!!)\<close>
text\<open>Andrews's challenge\<close>
lemma "((\<exists>x. \<forall>y. p(x) = p(y))  =
               ((\<exists>x. q(x)) = (\<forall>y. p(y))))   =
              ((\<exists>x. \<forall>y. q(x) = q(y))  =
               ((\<exists>x. p(x)) = (\<forall>y. q(y))))"
by blast

text\<open>Problem 35\<close>
lemma "\<exists>x y. P x y \<longrightarrow>  (\<forall>u v. P u v)"
by blast

text\<open>Problem 36\<close>
lemma "(\<forall>x. \<exists>y. J x y) \<and>
        (\<forall>x. \<exists>y. G x y) \<and>
        (\<forall>x y. J x y \<or> G x y \<longrightarrow>
        (\<forall>z. J y z \<or> G y z \<longrightarrow> H x z))
    \<longrightarrow> (\<forall>x. \<exists>y. H x y)"
by blast

text\<open>Problem 37\<close>
lemma "(\<forall>z. \<exists>w. \<forall>x. \<exists>y.
           (P x z \<longrightarrow>P y w) \<and> P y z \<and> (P y w \<longrightarrow> (\<exists>u. Q u w))) \<and>
        (\<forall>x z. \<not>(P x z) \<longrightarrow> (\<exists>y. Q y z)) \<and>
        ((\<exists>x y. Q x y) \<longrightarrow> (\<forall>x. R x x))
    \<longrightarrow> (\<forall>x. \<exists>y. R x y)"
by blast

text\<open>Problem 38\<close>
lemma "(\<forall>x. p(a) \<and> (p(x) \<longrightarrow> (\<exists>y. p(y) \<and> r x y)) \<longrightarrow>
           (\<exists>z. \<exists>w. p(z) \<and> r x w \<and> r w z))  =
     (\<forall>x. (\<not>p(a) \<or> p(x) \<or> (\<exists>z. \<exists>w. p(z) \<and> r x w \<and> r w z)) \<and>
           (\<not>p(a) \<or> \<not>(\<exists>y. p(y) \<and> r x y) \<or>
            (\<exists>z. \<exists>w. p(z) \<and> r x w \<and> r w z)))"
by blast (*beats fast!*)

text\<open>Problem 39\<close>
lemma "\<not> (\<exists>x. \<forall>y. F y x = (\<not> F y y))"
by blast

text\<open>Problem 40.  AMENDED\<close>
lemma "(\<exists>y. \<forall>x. F x y = F x x)
        \<longrightarrow>  \<not> (\<forall>x. \<exists>y. \<forall>z. F z y = (\<not> F z x))"
by blast

text\<open>Problem 41\<close>
lemma "(\<forall>z. \<exists>y. \<forall>x. f x y = (f x z \<and> \<not> f x x))
               \<longrightarrow> \<not> (\<exists>z. \<forall>x. f x z)"
by blast

text\<open>Problem 42\<close>
lemma "\<not> (\<exists>y. \<forall>x. p x y = (\<not> (\<exists>z. p x z \<and> p z x)))"
by blast

text\<open>Problem 43!!\<close>
lemma "(\<forall>x::'a. \<forall>y::'a. q x y = (\<forall>z. p z x \<longleftrightarrow> (p z y)))
  \<longrightarrow> (\<forall>x. (\<forall>y. q x y \<longleftrightarrow> (q y x)))"
by blast

text\<open>Problem 44\<close>
lemma "(\<forall>x. f(x) \<longrightarrow>
              (\<exists>y. g(y) \<and> h x y \<and> (\<exists>y. g(y) \<and> \<not> h x y)))  \<and>
              (\<exists>x. j(x) \<and> (\<forall>y. g(y) \<longrightarrow> h x y))
              \<longrightarrow> (\<exists>x. j(x) \<and> \<not>f(x))"
by blast

text\<open>Problem 45\<close>
lemma "(\<forall>x. f(x) \<and> (\<forall>y. g(y) \<and> h x y \<longrightarrow> j x y)
                      \<longrightarrow> (\<forall>y. g(y) \<and> h x y \<longrightarrow> k(y))) \<and>
     \<not> (\<exists>y. l(y) \<and> k(y)) \<and>
     (\<exists>x. f(x) \<and> (\<forall>y. h x y \<longrightarrow> l(y))
                \<and> (\<forall>y. g(y) \<and> h x y \<longrightarrow> j x y))
      \<longrightarrow> (\<exists>x. f(x) \<and> \<not> (\<exists>y. g(y) \<and> h x y))"
by blast


subsubsection\<open>Problems (mainly) involving equality or functions\<close>

text\<open>Problem 48\<close>
lemma "(a=b \<or> c=d) \<and> (a=c \<or> b=d) \<longrightarrow> a=d \<or> b=c"
by blast

text\<open>Problem 49  NOT PROVED AUTOMATICALLY.
     Hard because it involves substitution for Vars
  the type constraint ensures that x,y,z have the same type as a,b,u.\<close>
lemma "(\<exists>x y::'a. \<forall>z. z=x \<or> z=y) \<and> P(a) \<and> P(b) \<and> (\<not>a=b)
                \<longrightarrow> (\<forall>u::'a. P(u))"
by metis

text\<open>Problem 50.  (What has this to do with equality?)\<close>
lemma "(\<forall>x. P a x \<or> (\<forall>y. P x y)) \<longrightarrow> (\<exists>x. \<forall>y. P x y)"
by blast

text\<open>Problem 51\<close>
lemma "(\<exists>z w. \<forall>x y. P x y = (x=z \<and> y=w)) \<longrightarrow>
     (\<exists>z. \<forall>x. \<exists>w. (\<forall>y. P x y = (y=w)) = (x=z))"
by blast

text\<open>Problem 52. Almost the same as 51.\<close>
lemma "(\<exists>z w. \<forall>x y. P x y = (x=z \<and> y=w)) \<longrightarrow>
     (\<exists>w. \<forall>y. \<exists>z. (\<forall>x. P x y = (x=z)) = (y=w))"
by blast

text\<open>Problem 55\<close>

text\<open>Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  fast DISCOVERS who killed Agatha.\<close>
schematic_goal "lives(agatha) \<and> lives(butler) \<and> lives(charles) \<and>
   (killed agatha agatha \<or> killed butler agatha \<or> killed charles agatha) \<and>
   (\<forall>x y. killed x y \<longrightarrow> hates x y \<and> \<not>richer x y) \<and>
   (\<forall>x. hates agatha x \<longrightarrow> \<not>hates charles x) \<and>
   (hates agatha agatha \<and> hates agatha charles) \<and>
   (\<forall>x. lives(x) \<and> \<not>richer x agatha \<longrightarrow> hates butler x) \<and>
   (\<forall>x. hates agatha x \<longrightarrow> hates butler x) \<and>
   (\<forall>x. \<not>hates x agatha \<or> \<not>hates x butler \<or> \<not>hates x charles) \<longrightarrow>
    killed ?who agatha"
by fast

text\<open>Problem 56\<close>
lemma "(\<forall>x. (\<exists>y. P(y) \<and> x=f(y)) \<longrightarrow> P(x)) = (\<forall>x. P(x) \<longrightarrow> P(f(x)))"
by blast

text\<open>Problem 57\<close>
lemma "P (f a b) (f b c) \<and> P (f b c) (f a c) \<and>
     (\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z)    \<longrightarrow>   P (f a b) (f a c)"
by blast

text\<open>Problem 58  NOT PROVED AUTOMATICALLY\<close>
lemma "(\<forall>x y. f(x)=g(y)) \<longrightarrow> (\<forall>x y. f(f(x))=f(g(y)))"
by (fast intro: arg_cong [of concl: f])

text\<open>Problem 59\<close>
lemma "(\<forall>x. P(x) = (\<not>P(f(x)))) \<longrightarrow> (\<exists>x. P(x) \<and> \<not>P(f(x)))"
by blast

text\<open>Problem 60\<close>
lemma "\<forall>x. P x (f x) = (\<exists>y. (\<forall>z. P z y \<longrightarrow> P z (f x)) \<and> P x y)"
by blast

text\<open>Problem 62 as corrected in JAR 18 (1997), page 135\<close>
lemma "(\<forall>x. p a \<and> (p x \<longrightarrow> p(f x)) \<longrightarrow> p(f(f x)))  =
      (\<forall>x. (\<not> p a \<or> p x \<or> p(f(f x))) \<and>
              (\<not> p a \<or> \<not> p(f x) \<or> p(f(f x))))"
by blast

text\<open>From Davis, Obvious Logical Inferences, IJCAI-81, 530-531
  fast indeed copes!\<close>
lemma "(\<forall>x. F(x) \<and> \<not>G(x) \<longrightarrow> (\<exists>y. H(x,y) \<and> J(y))) \<and>
       (\<exists>x. K(x) \<and> F(x) \<and> (\<forall>y. H(x,y) \<longrightarrow> K(y))) \<and>
       (\<forall>x. K(x) \<longrightarrow> \<not>G(x))  \<longrightarrow>  (\<exists>x. K(x) \<and> J(x))"
by fast

text\<open>From Rudnicki, Obvious Inferences, JAR 3 (1987), 383-393.
  It does seem obvious!\<close>
lemma "(\<forall>x. F(x) \<and> \<not>G(x) \<longrightarrow> (\<exists>y. H(x,y) \<and> J(y))) \<and>
       (\<exists>x. K(x) \<and> F(x) \<and> (\<forall>y. H(x,y) \<longrightarrow> K(y)))  \<and>
       (\<forall>x. K(x) \<longrightarrow> \<not>G(x))   \<longrightarrow>   (\<exists>x. K(x) \<longrightarrow> \<not>G(x))"
by fast

text\<open>Attributed to Lewis Carroll by S. G. Pulman.  The first or last
assumption can be deleted.\<close>
lemma "(\<forall>x. honest(x) \<and> industrious(x) \<longrightarrow> healthy(x)) \<and>
      \<not> (\<exists>x. grocer(x) \<and> healthy(x)) \<and>
      (\<forall>x. industrious(x) \<and> grocer(x) \<longrightarrow> honest(x)) \<and>
      (\<forall>x. cyclist(x) \<longrightarrow> industrious(x)) \<and>
      (\<forall>x. \<not>healthy(x) \<and> cyclist(x) \<longrightarrow> \<not>honest(x))
      \<longrightarrow> (\<forall>x. grocer(x) \<longrightarrow> \<not>cyclist(x))"
by blast

lemma "(\<forall>x y. R(x,y) \<or> R(y,x)) \<and>
       (\<forall>x y. S(x,y) \<and> S(y,x) \<longrightarrow> x=y) \<and>
       (\<forall>x y. R(x,y) \<longrightarrow> S(x,y))    \<longrightarrow>   (\<forall>x y. S(x,y) \<longrightarrow> R(x,y))"
by blast


subsection\<open>Model Elimination Prover\<close>


text\<open>Trying out meson with arguments\<close>
lemma "x < y \<and> y < z \<longrightarrow> \<not> (z < (x::nat))"
by (meson order_less_irrefl order_less_trans)

text\<open>The "small example" from Bezem, Hendriks and de Nivelle,
Automatic Proof Construction in Type Theory Using Resolution,
JAR 29: 3-4 (2002), pages 253-275\<close>
lemma "(\<forall>x y z. R(x,y) \<and> R(y,z) \<longrightarrow> R(x,z)) \<and>
       (\<forall>x. \<exists>y. R(x,y)) \<longrightarrow>
       \<not> (\<forall>x. P x = (\<forall>y. R(x,y) \<longrightarrow> \<not> P y))"
by (tactic\<open>Meson.safe_best_meson_tac @{context} 1\<close>)
    \<comment> \<open>In contrast, \<open>meson\<close> is SLOW: 7.6s on griffon\<close>


subsubsection\<open>Pelletier's examples\<close>
text\<open>1\<close>
lemma "(P \<longrightarrow> Q)  =  (\<not>Q \<longrightarrow> \<not>P)"
by blast

text\<open>2\<close>
lemma "(\<not> \<not> P) =  P"
by blast

text\<open>3\<close>
lemma "\<not>(P\<longrightarrow>Q) \<longrightarrow> (Q\<longrightarrow>P)"
by blast

text\<open>4\<close>
lemma "(\<not>P\<longrightarrow>Q)  =  (\<not>Q \<longrightarrow> P)"
by blast

text\<open>5\<close>
lemma "((P\<or>Q)\<longrightarrow>(P\<or>R)) \<longrightarrow> (P\<or>(Q\<longrightarrow>R))"
by blast

text\<open>6\<close>
lemma "P \<or> \<not> P"
by blast

text\<open>7\<close>
lemma "P \<or> \<not> \<not> \<not> P"
by blast

text\<open>8.  Peirce's law\<close>
lemma "((P\<longrightarrow>Q) \<longrightarrow> P)  \<longrightarrow>  P"
by blast

text\<open>9\<close>
lemma "((P\<or>Q) \<and> (\<not>P\<or>Q) \<and> (P\<or> \<not>Q)) \<longrightarrow> \<not> (\<not>P \<or> \<not>Q)"
by blast

text\<open>10\<close>
lemma "(Q\<longrightarrow>R) \<and> (R\<longrightarrow>P\<and>Q) \<and> (P\<longrightarrow>Q\<or>R) \<longrightarrow> (P=Q)"
by blast

text\<open>11.  Proved in each direction (incorrectly, says Pelletier!!)\<close>
lemma "P=(P::bool)"
by blast

text\<open>12.  "Dijkstra's law"\<close>
lemma "((P = Q) = R) = (P = (Q = R))"
by blast

text\<open>13.  Distributive law\<close>
lemma "(P \<or> (Q \<and> R)) = ((P \<or> Q) \<and> (P \<or> R))"
by blast

text\<open>14\<close>
lemma "(P = Q) = ((Q \<or> \<not>P) \<and> (\<not>Q\<or>P))"
by blast

text\<open>15\<close>
lemma "(P \<longrightarrow> Q) = (\<not>P \<or> Q)"
by blast

text\<open>16\<close>
lemma "(P\<longrightarrow>Q) \<or> (Q\<longrightarrow>P)"
by blast

text\<open>17\<close>
lemma "((P \<and> (Q\<longrightarrow>R))\<longrightarrow>S)  =  ((\<not>P \<or> Q \<or> S) \<and> (\<not>P \<or> \<not>R \<or> S))"
by blast

subsubsection\<open>Classical Logic: examples with quantifiers\<close>

lemma "(\<forall>x. P x \<and> Q x) = ((\<forall>x. P x) \<and> (\<forall>x. Q x))"
by blast

lemma "(\<exists>x. P \<longrightarrow> Q x)  =  (P \<longrightarrow> (\<exists>x. Q x))"
by blast

lemma "(\<exists>x. P x \<longrightarrow> Q) = ((\<forall>x. P x) \<longrightarrow> Q)"
by blast

lemma "((\<forall>x. P x) \<or> Q)  =  (\<forall>x. P x \<or> Q)"
by blast

lemma "(\<forall>x. P x \<longrightarrow> P(f x))  \<and>  P d \<longrightarrow> P(f(f(f d)))"
by blast

text\<open>Needs double instantiation of EXISTS\<close>
lemma "\<exists>x. P x \<longrightarrow> P a \<and> P b"
by blast

lemma "\<exists>z. P z \<longrightarrow> (\<forall>x. P x)"
by blast

text\<open>From a paper by Claire Quigley\<close>
lemma "\<exists>y. ((P c \<and> Q y) \<or> (\<exists>z. \<not> Q z)) \<or> (\<exists>x. \<not> P x \<and> Q d)"
by fast

subsubsection\<open>Hard examples with quantifiers\<close>

text\<open>Problem 18\<close>
lemma "\<exists>y. \<forall>x. P y \<longrightarrow> P x"
by blast

text\<open>Problem 19\<close>
lemma "\<exists>x. \<forall>y z. (P y \<longrightarrow> Q z) \<longrightarrow> (P x \<longrightarrow> Q x)"
by blast

text\<open>Problem 20\<close>
lemma "(\<forall>x y. \<exists>z. \<forall>w. (P x \<and> Q y \<longrightarrow> R z \<and> S w))
    \<longrightarrow> (\<exists>x y. P x \<and> Q y) \<longrightarrow> (\<exists>z. R z)"
by blast

text\<open>Problem 21\<close>
lemma "(\<exists>x. P \<longrightarrow> Q x) \<and> (\<exists>x. Q x \<longrightarrow> P) \<longrightarrow> (\<exists>x. P=Q x)"
by blast

text\<open>Problem 22\<close>
lemma "(\<forall>x. P = Q x)  \<longrightarrow>  (P = (\<forall>x. Q x))"
by blast

text\<open>Problem 23\<close>
lemma "(\<forall>x. P \<or> Q x)  =  (P \<or> (\<forall>x. Q x))"
by blast

text\<open>Problem 24\<close>  (*The first goal clause is useless*)
lemma "\<not>(\<exists>x. S x \<and> Q x) \<and> (\<forall>x. P x \<longrightarrow> Q x \<or> R x) \<and>
      (\<not>(\<exists>x. P x) \<longrightarrow> (\<exists>x. Q x)) \<and> (\<forall>x. Q x \<or> R x \<longrightarrow> S x)
    \<longrightarrow> (\<exists>x. P x \<and> R x)"
by blast

text\<open>Problem 25\<close>
lemma "(\<exists>x. P x) \<and>
      (\<forall>x. L x \<longrightarrow> \<not> (M x \<and> R x)) \<and>
      (\<forall>x. P x \<longrightarrow> (M x \<and> L x)) \<and>
      ((\<forall>x. P x \<longrightarrow> Q x) \<or> (\<exists>x. P x \<and> R x))
    \<longrightarrow> (\<exists>x. Q x \<and> P x)"
by blast

text\<open>Problem 26; has 24 Horn clauses\<close>
lemma "((\<exists>x. p x) = (\<exists>x. q x)) \<and>
      (\<forall>x. \<forall>y. p x \<and> q y \<longrightarrow> (r x = s y))
  \<longrightarrow> ((\<forall>x. p x \<longrightarrow> r x) = (\<forall>x. q x \<longrightarrow> s x))"
by blast

text\<open>Problem 27; has 13 Horn clauses\<close>
lemma "(\<exists>x. P x \<and> \<not>Q x) \<and>
      (\<forall>x. P x \<longrightarrow> R x) \<and>
      (\<forall>x. M x \<and> L x \<longrightarrow> P x) \<and>
      ((\<exists>x. R x \<and> \<not> Q x) \<longrightarrow> (\<forall>x. L x \<longrightarrow> \<not> R x))
      \<longrightarrow> (\<forall>x. M x \<longrightarrow> \<not>L x)"
by blast

text\<open>Problem 28.  AMENDED; has 14 Horn clauses\<close>
lemma "(\<forall>x. P x \<longrightarrow> (\<forall>x. Q x)) \<and>
      ((\<forall>x. Q x \<or> R x) \<longrightarrow> (\<exists>x. Q x \<and> S x)) \<and>
      ((\<exists>x. S x) \<longrightarrow> (\<forall>x. L x \<longrightarrow> M x))
    \<longrightarrow> (\<forall>x. P x \<and> L x \<longrightarrow> M x)"
by blast

text\<open>Problem 29.  Essentially the same as Principia Mathematica *11.71.
      62 Horn clauses\<close>
lemma "(\<exists>x. F x) \<and> (\<exists>y. G y)
    \<longrightarrow> ( ((\<forall>x. F x \<longrightarrow> H x) \<and> (\<forall>y. G y \<longrightarrow> J y))  =
          (\<forall>x y. F x \<and> G y \<longrightarrow> H x \<and> J y))"
by blast


text\<open>Problem 30\<close>
lemma "(\<forall>x. P x \<or> Q x \<longrightarrow> \<not> R x) \<and> (\<forall>x. (Q x \<longrightarrow> \<not> S x) \<longrightarrow> P x \<and> R x)
       \<longrightarrow> (\<forall>x. S x)"
by blast

text\<open>Problem 31; has 10 Horn clauses; first negative clauses is useless\<close>
lemma "\<not>(\<exists>x. P x \<and> (Q x \<or> R x)) \<and>
      (\<exists>x. L x \<and> P x) \<and>
      (\<forall>x. \<not> R x \<longrightarrow> M x)
    \<longrightarrow> (\<exists>x. L x \<and> M x)"
by blast

text\<open>Problem 32\<close>
lemma "(\<forall>x. P x \<and> (Q x \<or> R x)\<longrightarrow>S x) \<and>
      (\<forall>x. S x \<and> R x \<longrightarrow> L x) \<and>
      (\<forall>x. M x \<longrightarrow> R x)
    \<longrightarrow> (\<forall>x. P x \<and> M x \<longrightarrow> L x)"
by blast

text\<open>Problem 33; has 55 Horn clauses\<close>
lemma "(\<forall>x. P a \<and> (P x \<longrightarrow> P b)\<longrightarrow>P c)  =
      (\<forall>x. (\<not>P a \<or> P x \<or> P c) \<and> (\<not>P a \<or> \<not>P b \<or> P c))"
by blast

text\<open>Problem 34: Andrews's challenge has 924 Horn clauses\<close>
lemma "((\<exists>x. \<forall>y. p x = p y)  = ((\<exists>x. q x) = (\<forall>y. p y)))     =
      ((\<exists>x. \<forall>y. q x = q y)  = ((\<exists>x. p x) = (\<forall>y. q y)))"
by blast

text\<open>Problem 35\<close>
lemma "\<exists>x y. P x y \<longrightarrow>  (\<forall>u v. P u v)"
by blast

text\<open>Problem 36; has 15 Horn clauses\<close>
lemma "(\<forall>x. \<exists>y. J x y) \<and> (\<forall>x. \<exists>y. G x y) \<and>
       (\<forall>x y. J x y \<or> G x y \<longrightarrow> (\<forall>z. J y z \<or> G y z \<longrightarrow> H x z))
       \<longrightarrow> (\<forall>x. \<exists>y. H x y)"
by blast

text\<open>Problem 37; has 10 Horn clauses\<close>
lemma "(\<forall>z. \<exists>w. \<forall>x. \<exists>y.
           (P x z \<longrightarrow> P y w) \<and> P y z \<and> (P y w \<longrightarrow> (\<exists>u. Q u w))) \<and>
      (\<forall>x z. \<not>P x z \<longrightarrow> (\<exists>y. Q y z)) \<and>
      ((\<exists>x y. Q x y) \<longrightarrow> (\<forall>x. R x x))
    \<longrightarrow> (\<forall>x. \<exists>y. R x y)"
by blast \<comment> \<open>causes unification tracing messages\<close>


text\<open>Problem 38\<close>  text\<open>Quite hard: 422 Horn clauses!!\<close>
lemma "(\<forall>x. p a \<and> (p x \<longrightarrow> (\<exists>y. p y \<and> r x y)) \<longrightarrow>
           (\<exists>z. \<exists>w. p z \<and> r x w \<and> r w z))  =
      (\<forall>x. (\<not>p a \<or> p x \<or> (\<exists>z. \<exists>w. p z \<and> r x w \<and> r w z)) \<and>
            (\<not>p a \<or> \<not>(\<exists>y. p y \<and> r x y) \<or>
             (\<exists>z. \<exists>w. p z \<and> r x w \<and> r w z)))"
by blast

text\<open>Problem 39\<close>
lemma "\<not> (\<exists>x. \<forall>y. F y x = (\<not>F y y))"
by blast

text\<open>Problem 40.  AMENDED\<close>
lemma "(\<exists>y. \<forall>x. F x y = F x x)
      \<longrightarrow>  \<not> (\<forall>x. \<exists>y. \<forall>z. F z y = (\<not>F z x))"
by blast

text\<open>Problem 41\<close>
lemma "(\<forall>z. (\<exists>y. (\<forall>x. f x y = (f x z \<and> \<not> f x x))))
      \<longrightarrow> \<not> (\<exists>z. \<forall>x. f x z)"
by blast

text\<open>Problem 42\<close>
lemma "\<not> (\<exists>y. \<forall>x. p x y = (\<not> (\<exists>z. p x z \<and> p z x)))"
by blast

text\<open>Problem 43  NOW PROVED AUTOMATICALLY!!\<close>
lemma "(\<forall>x. \<forall>y. q x y = (\<forall>z. p z x = (p z y::bool)))
      \<longrightarrow> (\<forall>x. (\<forall>y. q x y = (q y x::bool)))"
by blast

text\<open>Problem 44: 13 Horn clauses; 7-step proof\<close>
lemma "(\<forall>x. f x \<longrightarrow> (\<exists>y. g y \<and> h x y \<and> (\<exists>y. g y \<and> \<not> h x y)))  \<and>
       (\<exists>x. j x \<and> (\<forall>y. g y \<longrightarrow> h x y))
       \<longrightarrow> (\<exists>x. j x \<and> \<not>f x)"
by blast

text\<open>Problem 45; has 27 Horn clauses; 54-step proof\<close>
lemma "(\<forall>x. f x \<and> (\<forall>y. g y \<and> h x y \<longrightarrow> j x y)
            \<longrightarrow> (\<forall>y. g y \<and> h x y \<longrightarrow> k y)) \<and>
      \<not> (\<exists>y. l y \<and> k y) \<and>
      (\<exists>x. f x \<and> (\<forall>y. h x y \<longrightarrow> l y)
                \<and> (\<forall>y. g y \<and> h x y \<longrightarrow> j x y))
      \<longrightarrow> (\<exists>x. f x \<and> \<not> (\<exists>y. g y \<and> h x y))"
by blast

text\<open>Problem 46; has 26 Horn clauses; 21-step proof\<close>
lemma "(\<forall>x. f x \<and> (\<forall>y. f y \<and> h y x \<longrightarrow> g y) \<longrightarrow> g x) \<and>
       ((\<exists>x. f x \<and> \<not>g x) \<longrightarrow>
       (\<exists>x. f x \<and> \<not>g x \<and> (\<forall>y. f y \<and> \<not>g y \<longrightarrow> j x y))) \<and>
       (\<forall>x y. f x \<and> f y \<and> h x y \<longrightarrow> \<not>j y x)
       \<longrightarrow> (\<forall>x. f x \<longrightarrow> g x)"
by blast

text\<open>Problem 47.  Schubert's Steamroller.
      26 clauses; 63 Horn clauses.
      87094 inferences so far.  Searching to depth 36\<close>
lemma "(\<forall>x. wolf x \<longrightarrow> animal x) \<and> (\<exists>x. wolf x) \<and>
       (\<forall>x. fox x \<longrightarrow> animal x) \<and> (\<exists>x. fox x) \<and>
       (\<forall>x. bird x \<longrightarrow> animal x) \<and> (\<exists>x. bird x) \<and>
       (\<forall>x. caterpillar x \<longrightarrow> animal x) \<and> (\<exists>x. caterpillar x) \<and>
       (\<forall>x. snail x \<longrightarrow> animal x) \<and> (\<exists>x. snail x) \<and>
       (\<forall>x. grain x \<longrightarrow> plant x) \<and> (\<exists>x. grain x) \<and>
       (\<forall>x. animal x \<longrightarrow>
             ((\<forall>y. plant y \<longrightarrow> eats x y)  \<or> 
              (\<forall>y. animal y \<and> smaller_than y x \<and>
                    (\<exists>z. plant z \<and> eats y z) \<longrightarrow> eats x y))) \<and>
       (\<forall>x y. bird y \<and> (snail x \<or> caterpillar x) \<longrightarrow> smaller_than x y) \<and>
       (\<forall>x y. bird x \<and> fox y \<longrightarrow> smaller_than x y) \<and>
       (\<forall>x y. fox x \<and> wolf y \<longrightarrow> smaller_than x y) \<and>
       (\<forall>x y. wolf x \<and> (fox y \<or> grain y) \<longrightarrow> \<not>eats x y) \<and>
       (\<forall>x y. bird x \<and> caterpillar y \<longrightarrow> eats x y) \<and>
       (\<forall>x y. bird x \<and> snail y \<longrightarrow> \<not>eats x y) \<and>
       (\<forall>x. (caterpillar x \<or> snail x) \<longrightarrow> (\<exists>y. plant y \<and> eats x y))
       \<longrightarrow> (\<exists>x y. animal x \<and> animal y \<and> (\<exists>z. grain z \<and> eats y z \<and> eats x y))"
by (tactic\<open>Meson.safe_best_meson_tac @{context} 1\<close>)
    \<comment> \<open>Nearly twice as fast as \<open>meson\<close>,
        which performs iterative deepening rather than best-first search\<close>

text\<open>The Los problem. Circulated by John Harrison\<close>
lemma "(\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z) \<and>
       (\<forall>x y z. Q x y \<and> Q y z \<longrightarrow> Q x z) \<and>
       (\<forall>x y. P x y \<longrightarrow> P y x) \<and>
       (\<forall>x y. P x y \<or> Q x y)
       \<longrightarrow> (\<forall>x y. P x y) \<or> (\<forall>x y. Q x y)"
by meson

text\<open>A similar example, suggested by Johannes Schumann and
 credited to Pelletier\<close>
lemma "(\<forall>x y z. P x y \<longrightarrow> P y z \<longrightarrow> P x z) \<longrightarrow>
       (\<forall>x y z. Q x y \<longrightarrow> Q y z \<longrightarrow> Q x z) \<longrightarrow>
       (\<forall>x y. Q x y \<longrightarrow> Q y x) \<longrightarrow>  (\<forall>x y. P x y \<or> Q x y) \<longrightarrow>
       (\<forall>x y. P x y) \<or> (\<forall>x y. Q x y)"
by meson

text\<open>Problem 50.  What has this to do with equality?\<close>
lemma "(\<forall>x. P a x \<or> (\<forall>y. P x y)) \<longrightarrow> (\<exists>x. \<forall>y. P x y)"
by blast

text\<open>Problem 54: NOT PROVED\<close>
lemma "(\<forall>y::'a. \<exists>z. \<forall>x. F x z = (x=y)) \<longrightarrow>
      \<not> (\<exists>w. \<forall>x. F x w = (\<forall>u. F x u \<longrightarrow> (\<exists>y. F y u \<and> \<not> (\<exists>z. F z u \<and> F z y))))"
oops 


text\<open>Problem 55\<close>

text\<open>Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  \<open>meson\<close> cannot report who killed Agatha.\<close>
lemma "lives agatha \<and> lives butler \<and> lives charles \<and>
       (killed agatha agatha \<or> killed butler agatha \<or> killed charles agatha) \<and>
       (\<forall>x y. killed x y \<longrightarrow> hates x y \<and> \<not>richer x y) \<and>
       (\<forall>x. hates agatha x \<longrightarrow> \<not>hates charles x) \<and>
       (hates agatha agatha \<and> hates agatha charles) \<and>
       (\<forall>x. lives x \<and> \<not>richer x agatha \<longrightarrow> hates butler x) \<and>
       (\<forall>x. hates agatha x \<longrightarrow> hates butler x) \<and>
       (\<forall>x. \<not>hates x agatha \<or> \<not>hates x butler \<or> \<not>hates x charles) \<longrightarrow>
       (\<exists>x. killed x agatha)"
by meson

text\<open>Problem 57\<close>
lemma "P (f a b) (f b c) \<and> P (f b c) (f a c) \<and>
      (\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z)    \<longrightarrow>   P (f a b) (f a c)"
by blast

text\<open>Problem 58: Challenge found on info-hol\<close>
lemma "\<forall>P Q R x. \<exists>v w. \<forall>y z. P x \<and> Q y \<longrightarrow> (P v \<or> R w) \<and> (R z \<longrightarrow> Q v)"
by blast

text\<open>Problem 59\<close>
lemma "(\<forall>x. P x = (\<not>P(f x))) \<longrightarrow> (\<exists>x. P x \<and> \<not>P(f x))"
by blast

text\<open>Problem 60\<close>
lemma "\<forall>x. P x (f x) = (\<exists>y. (\<forall>z. P z y \<longrightarrow> P z (f x)) \<and> P x y)"
by blast

text\<open>Problem 62 as corrected in JAR 18 (1997), page 135\<close>
lemma "(\<forall>x. p a \<and> (p x \<longrightarrow> p(f x)) \<longrightarrow> p(f(f x)))  =
       (\<forall>x. (\<not> p a \<or> p x \<or> p(f(f x))) \<and>
            (\<not> p a \<or> \<not> p(f x) \<or> p(f(f x))))"
by blast

text\<open>Charles Morgan's problems\<close>
context
  fixes T i n
  assumes a: "\<forall>x y. T(i x(i y x))"
    and b: "\<forall>x y z. T(i (i x (i y z)) (i (i x y) (i x z)))"
    and c: "\<forall>x y. T(i (i (n x) (n y)) (i y x))"
    and c': "\<forall>x y. T(i (i y x) (i (n x) (n y)))"
    and d: "\<forall>x y. T(i x y) \<and> T x \<longrightarrow> T y"
begin

lemma "\<forall>x. T(i x x)"
  using a b d by blast

lemma "\<forall>x. T(i x (n(n x)))" \<comment> \<open>Problem 66\<close>
  using a b c d by metis

lemma "\<forall>x. T(i (n(n x)) x)" \<comment> \<open>Problem 67\<close>
  using a b c d by meson \<comment> \<open>4.9s on griffon. 51061 inferences, depth 21\<close>

lemma "\<forall>x. T(i x (n(n x)))" \<comment> \<open>Problem 68: not proved.  Listed as satisfiable in TPTP (LCL078-1)\<close>
  using a b c' d oops

end

text\<open>Problem 71, as found in TPTP (SYN007+1.005)\<close>
lemma "p1 = (p2 = (p3 = (p4 = (p5 = (p1 = (p2 = (p3 = (p4 = p5))))))))"
  by blast

end
