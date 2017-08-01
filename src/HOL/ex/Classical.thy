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

lemma "(P --> Q | R) --> (P-->Q) | (P-->R)"
by blast

text\<open>If and only if\<close>

lemma "(P=Q) = (Q = (P::bool))"
by blast

lemma "~ (P = (~P))"
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
lemma "(P-->Q)  =  (~Q --> ~P)"
by blast

text\<open>2\<close>
lemma "(~ ~ P) =  P"
by blast

text\<open>3\<close>
lemma "~(P-->Q) --> (Q-->P)"
by blast

text\<open>4\<close>
lemma "(~P-->Q)  =  (~Q --> P)"
by blast

text\<open>5\<close>
lemma "((P|Q)-->(P|R)) --> (P|(Q-->R))"
by blast

text\<open>6\<close>
lemma "P | ~ P"
by blast

text\<open>7\<close>
lemma "P | ~ ~ ~ P"
by blast

text\<open>8.  Peirce's law\<close>
lemma "((P-->Q) --> P)  -->  P"
by blast

text\<open>9\<close>
lemma "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)"
by blast

text\<open>10\<close>
lemma "(Q-->R) & (R-->P&Q) & (P-->Q|R) --> (P=Q)"
by blast

text\<open>11.  Proved in each direction (incorrectly, says Pelletier!!)\<close>
lemma "P=(P::bool)"
by blast

text\<open>12.  "Dijkstra's law"\<close>
lemma "((P = Q) = R) = (P = (Q = R))"
by blast

text\<open>13.  Distributive law\<close>
lemma "(P | (Q & R)) = ((P | Q) & (P | R))"
by blast

text\<open>14\<close>
lemma "(P = Q) = ((Q | ~P) & (~Q|P))"
by blast

text\<open>15\<close>
lemma "(P --> Q) = (~P | Q)"
by blast

text\<open>16\<close>
lemma "(P-->Q) | (Q-->P)"
by blast

text\<open>17\<close>
lemma "((P & (Q-->R))-->S)  =  ((~P | Q | S) & (~P | ~R | S))"
by blast

subsubsection\<open>Classical Logic: examples with quantifiers\<close>

lemma "(\<forall>x. P(x) & Q(x)) = ((\<forall>x. P(x)) & (\<forall>x. Q(x)))"
by blast

lemma "(\<exists>x. P-->Q(x))  =  (P --> (\<exists>x. Q(x)))"
by blast

lemma "(\<exists>x. P(x)-->Q) = ((\<forall>x. P(x)) --> Q)"
by blast

lemma "((\<forall>x. P(x)) | Q)  =  (\<forall>x. P(x) | Q)"
by blast

text\<open>From Wishnu Prasetya\<close>
lemma "(\<forall>s. q(s) --> r(s)) & ~r(s) & (\<forall>s. ~r(s) & ~q(s) --> p(t) | q(t))
    --> p(t) | r(t)"
by blast


subsubsection\<open>Problems requiring quantifier duplication\<close>

text\<open>Theorem B of Peter Andrews, Theorem Proving via General Matings,
  JACM 28 (1981).\<close>
lemma "(\<exists>x. \<forall>y. P(x) = P(y)) --> ((\<exists>x. P(x)) = (\<forall>y. P(y)))"
by blast

text\<open>Needs multiple instantiation of the quantifier.\<close>
lemma "(\<forall>x. P(x)-->P(f(x)))  &  P(d)-->P(f(f(f(d))))"
by blast

text\<open>Needs double instantiation of the quantifier\<close>
lemma "\<exists>x. P(x) --> P(a) & P(b)"
by blast

lemma "\<exists>z. P(z) --> (\<forall>x. P(x))"
by blast

lemma "\<exists>x. (\<exists>y. P(y)) --> P(x)"
by blast

subsubsection\<open>Hard examples with quantifiers\<close>

text\<open>Problem 18\<close>
lemma "\<exists>y. \<forall>x. P(y)-->P(x)"
by blast

text\<open>Problem 19\<close>
lemma "\<exists>x. \<forall>y z. (P(y)-->Q(z)) --> (P(x)-->Q(x))"
by blast

text\<open>Problem 20\<close>
lemma "(\<forall>x y. \<exists>z. \<forall>w. (P(x)&Q(y)-->R(z)&S(w)))
    --> (\<exists>x y. P(x) & Q(y)) --> (\<exists>z. R(z))"
by blast

text\<open>Problem 21\<close>
lemma "(\<exists>x. P-->Q(x)) & (\<exists>x. Q(x)-->P) --> (\<exists>x. P=Q(x))"
by blast

text\<open>Problem 22\<close>
lemma "(\<forall>x. P = Q(x))  -->  (P = (\<forall>x. Q(x)))"
by blast

text\<open>Problem 23\<close>
lemma "(\<forall>x. P | Q(x))  =  (P | (\<forall>x. Q(x)))"
by blast

text\<open>Problem 24\<close>
lemma "~(\<exists>x. S(x)&Q(x)) & (\<forall>x. P(x) --> Q(x)|R(x)) &
     (~(\<exists>x. P(x)) --> (\<exists>x. Q(x))) & (\<forall>x. Q(x)|R(x) --> S(x))
    --> (\<exists>x. P(x)&R(x))"
by blast

text\<open>Problem 25\<close>
lemma "(\<exists>x. P(x)) &
        (\<forall>x. L(x) --> ~ (M(x) & R(x))) &
        (\<forall>x. P(x) --> (M(x) & L(x))) &
        ((\<forall>x. P(x)-->Q(x)) | (\<exists>x. P(x)&R(x)))
    --> (\<exists>x. Q(x)&P(x))"
by blast

text\<open>Problem 26\<close>
lemma "((\<exists>x. p(x)) = (\<exists>x. q(x))) &
      (\<forall>x. \<forall>y. p(x) & q(y) --> (r(x) = s(y)))
  --> ((\<forall>x. p(x)-->r(x)) = (\<forall>x. q(x)-->s(x)))"
by blast

text\<open>Problem 27\<close>
lemma "(\<exists>x. P(x) & ~Q(x)) &
              (\<forall>x. P(x) --> R(x)) &
              (\<forall>x. M(x) & L(x) --> P(x)) &
              ((\<exists>x. R(x) & ~ Q(x)) --> (\<forall>x. L(x) --> ~ R(x)))
          --> (\<forall>x. M(x) --> ~L(x))"
by blast

text\<open>Problem 28.  AMENDED\<close>
lemma "(\<forall>x. P(x) --> (\<forall>x. Q(x))) &
        ((\<forall>x. Q(x)|R(x)) --> (\<exists>x. Q(x)&S(x))) &
        ((\<exists>x. S(x)) --> (\<forall>x. L(x) --> M(x)))
    --> (\<forall>x. P(x) & L(x) --> M(x))"
by blast

text\<open>Problem 29.  Essentially the same as Principia Mathematica *11.71\<close>
lemma "(\<exists>x. F(x)) & (\<exists>y. G(y))
    --> ( ((\<forall>x. F(x)-->H(x)) & (\<forall>y. G(y)-->J(y)))  =
          (\<forall>x y. F(x) & G(y) --> H(x) & J(y)))"
by blast

text\<open>Problem 30\<close>
lemma "(\<forall>x. P(x) | Q(x) --> ~ R(x)) &
        (\<forall>x. (Q(x) --> ~ S(x)) --> P(x) & R(x))
    --> (\<forall>x. S(x))"
by blast

text\<open>Problem 31\<close>
lemma "~(\<exists>x. P(x) & (Q(x) | R(x))) &
        (\<exists>x. L(x) & P(x)) &
        (\<forall>x. ~ R(x) --> M(x))
    --> (\<exists>x. L(x) & M(x))"
by blast

text\<open>Problem 32\<close>
lemma "(\<forall>x. P(x) & (Q(x)|R(x))-->S(x)) &
        (\<forall>x. S(x) & R(x) --> L(x)) &
        (\<forall>x. M(x) --> R(x))
    --> (\<forall>x. P(x) & M(x) --> L(x))"
by blast

text\<open>Problem 33\<close>
lemma "(\<forall>x. P(a) & (P(x)-->P(b))-->P(c))  =
     (\<forall>x. (~P(a) | P(x) | P(c)) & (~P(a) | ~P(b) | P(c)))"
by blast

text\<open>Problem 34  AMENDED (TWICE!!)\<close>
text\<open>Andrews's challenge\<close>
lemma "((\<exists>x. \<forall>y. p(x) = p(y))  =
               ((\<exists>x. q(x)) = (\<forall>y. p(y))))   =
              ((\<exists>x. \<forall>y. q(x) = q(y))  =
               ((\<exists>x. p(x)) = (\<forall>y. q(y))))"
by blast

text\<open>Problem 35\<close>
lemma "\<exists>x y. P x y -->  (\<forall>u v. P u v)"
by blast

text\<open>Problem 36\<close>
lemma "(\<forall>x. \<exists>y. J x y) &
        (\<forall>x. \<exists>y. G x y) &
        (\<forall>x y. J x y | G x y -->
        (\<forall>z. J y z | G y z --> H x z))
    --> (\<forall>x. \<exists>y. H x y)"
by blast

text\<open>Problem 37\<close>
lemma "(\<forall>z. \<exists>w. \<forall>x. \<exists>y.
           (P x z -->P y w) & P y z & (P y w --> (\<exists>u. Q u w))) &
        (\<forall>x z. ~(P x z) --> (\<exists>y. Q y z)) &
        ((\<exists>x y. Q x y) --> (\<forall>x. R x x))
    --> (\<forall>x. \<exists>y. R x y)"
by blast

text\<open>Problem 38\<close>
lemma "(\<forall>x. p(a) & (p(x) --> (\<exists>y. p(y) & r x y)) -->
           (\<exists>z. \<exists>w. p(z) & r x w & r w z))  =
     (\<forall>x. (~p(a) | p(x) | (\<exists>z. \<exists>w. p(z) & r x w & r w z)) &
           (~p(a) | ~(\<exists>y. p(y) & r x y) |
            (\<exists>z. \<exists>w. p(z) & r x w & r w z)))"
by blast (*beats fast!*)

text\<open>Problem 39\<close>
lemma "~ (\<exists>x. \<forall>y. F y x = (~ F y y))"
by blast

text\<open>Problem 40.  AMENDED\<close>
lemma "(\<exists>y. \<forall>x. F x y = F x x)
        -->  ~ (\<forall>x. \<exists>y. \<forall>z. F z y = (~ F z x))"
by blast

text\<open>Problem 41\<close>
lemma "(\<forall>z. \<exists>y. \<forall>x. f x y = (f x z & ~ f x x))
               --> ~ (\<exists>z. \<forall>x. f x z)"
by blast

text\<open>Problem 42\<close>
lemma "~ (\<exists>y. \<forall>x. p x y = (~ (\<exists>z. p x z & p z x)))"
by blast

text\<open>Problem 43!!\<close>
lemma "(\<forall>x::'a. \<forall>y::'a. q x y = (\<forall>z. p z x = (p z y::bool)))
  --> (\<forall>x. (\<forall>y. q x y = (q y x::bool)))"
by blast

text\<open>Problem 44\<close>
lemma "(\<forall>x. f(x) -->
              (\<exists>y. g(y) & h x y & (\<exists>y. g(y) & ~ h x y)))  &
              (\<exists>x. j(x) & (\<forall>y. g(y) --> h x y))
              --> (\<exists>x. j(x) & ~f(x))"
by blast

text\<open>Problem 45\<close>
lemma "(\<forall>x. f(x) & (\<forall>y. g(y) & h x y --> j x y)
                      --> (\<forall>y. g(y) & h x y --> k(y))) &
     ~ (\<exists>y. l(y) & k(y)) &
     (\<exists>x. f(x) & (\<forall>y. h x y --> l(y))
                & (\<forall>y. g(y) & h x y --> j x y))
      --> (\<exists>x. f(x) & ~ (\<exists>y. g(y) & h x y))"
by blast


subsubsection\<open>Problems (mainly) involving equality or functions\<close>

text\<open>Problem 48\<close>
lemma "(a=b | c=d) & (a=c | b=d) --> a=d | b=c"
by blast

text\<open>Problem 49  NOT PROVED AUTOMATICALLY.
     Hard because it involves substitution for Vars
  the type constraint ensures that x,y,z have the same type as a,b,u.\<close>
lemma "(\<exists>x y::'a. \<forall>z. z=x | z=y) & P(a) & P(b) & (~a=b)
                --> (\<forall>u::'a. P(u))"
by metis

text\<open>Problem 50.  (What has this to do with equality?)\<close>
lemma "(\<forall>x. P a x | (\<forall>y. P x y)) --> (\<exists>x. \<forall>y. P x y)"
by blast

text\<open>Problem 51\<close>
lemma "(\<exists>z w. \<forall>x y. P x y = (x=z & y=w)) -->
     (\<exists>z. \<forall>x. \<exists>w. (\<forall>y. P x y = (y=w)) = (x=z))"
by blast

text\<open>Problem 52. Almost the same as 51.\<close>
lemma "(\<exists>z w. \<forall>x y. P x y = (x=z & y=w)) -->
     (\<exists>w. \<forall>y. \<exists>z. (\<forall>x. P x y = (x=z)) = (y=w))"
by blast

text\<open>Problem 55\<close>

text\<open>Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  fast DISCOVERS who killed Agatha.\<close>
schematic_goal "lives(agatha) & lives(butler) & lives(charles) &
   (killed agatha agatha | killed butler agatha | killed charles agatha) &
   (\<forall>x y. killed x y --> hates x y & ~richer x y) &
   (\<forall>x. hates agatha x --> ~hates charles x) &
   (hates agatha agatha & hates agatha charles) &
   (\<forall>x. lives(x) & ~richer x agatha --> hates butler x) &
   (\<forall>x. hates agatha x --> hates butler x) &
   (\<forall>x. ~hates x agatha | ~hates x butler | ~hates x charles) -->
    killed ?who agatha"
by fast

text\<open>Problem 56\<close>
lemma "(\<forall>x. (\<exists>y. P(y) & x=f(y)) --> P(x)) = (\<forall>x. P(x) --> P(f(x)))"
by blast

text\<open>Problem 57\<close>
lemma "P (f a b) (f b c) & P (f b c) (f a c) &
     (\<forall>x y z. P x y & P y z --> P x z)    -->   P (f a b) (f a c)"
by blast

text\<open>Problem 58  NOT PROVED AUTOMATICALLY\<close>
lemma "(\<forall>x y. f(x)=g(y)) --> (\<forall>x y. f(f(x))=f(g(y)))"
by (fast intro: arg_cong [of concl: f])

text\<open>Problem 59\<close>
lemma "(\<forall>x. P(x) = (~P(f(x)))) --> (\<exists>x. P(x) & ~P(f(x)))"
by blast

text\<open>Problem 60\<close>
lemma "\<forall>x. P x (f x) = (\<exists>y. (\<forall>z. P z y --> P z (f x)) & P x y)"
by blast

text\<open>Problem 62 as corrected in JAR 18 (1997), page 135\<close>
lemma "(\<forall>x. p a & (p x --> p(f x)) --> p(f(f x)))  =
      (\<forall>x. (~ p a | p x | p(f(f x))) &
              (~ p a | ~ p(f x) | p(f(f x))))"
by blast

text\<open>From Davis, Obvious Logical Inferences, IJCAI-81, 530-531
  fast indeed copes!\<close>
lemma "(\<forall>x. F(x) & ~G(x) --> (\<exists>y. H(x,y) & J(y))) &
       (\<exists>x. K(x) & F(x) & (\<forall>y. H(x,y) --> K(y))) &
       (\<forall>x. K(x) --> ~G(x))  -->  (\<exists>x. K(x) & J(x))"
by fast

text\<open>From Rudnicki, Obvious Inferences, JAR 3 (1987), 383-393.
  It does seem obvious!\<close>
lemma "(\<forall>x. F(x) & ~G(x) --> (\<exists>y. H(x,y) & J(y))) &
       (\<exists>x. K(x) & F(x) & (\<forall>y. H(x,y) --> K(y)))  &
       (\<forall>x. K(x) --> ~G(x))   -->   (\<exists>x. K(x) --> ~G(x))"
by fast

text\<open>Attributed to Lewis Carroll by S. G. Pulman.  The first or last
assumption can be deleted.\<close>
lemma "(\<forall>x. honest(x) & industrious(x) --> healthy(x)) &
      ~ (\<exists>x. grocer(x) & healthy(x)) &
      (\<forall>x. industrious(x) & grocer(x) --> honest(x)) &
      (\<forall>x. cyclist(x) --> industrious(x)) &
      (\<forall>x. ~healthy(x) & cyclist(x) --> ~honest(x))
      --> (\<forall>x. grocer(x) --> ~cyclist(x))"
by blast

lemma "(\<forall>x y. R(x,y) | R(y,x)) &
       (\<forall>x y. S(x,y) & S(y,x) --> x=y) &
       (\<forall>x y. R(x,y) --> S(x,y))    -->   (\<forall>x y. S(x,y) --> R(x,y))"
by blast


subsection\<open>Model Elimination Prover\<close>


text\<open>Trying out meson with arguments\<close>
lemma "x < y & y < z --> ~ (z < (x::nat))"
by (meson order_less_irrefl order_less_trans)

text\<open>The "small example" from Bezem, Hendriks and de Nivelle,
Automatic Proof Construction in Type Theory Using Resolution,
JAR 29: 3-4 (2002), pages 253-275\<close>
lemma "(\<forall>x y z. R(x,y) & R(y,z) --> R(x,z)) &
       (\<forall>x. \<exists>y. R(x,y)) -->
       ~ (\<forall>x. P x = (\<forall>y. R(x,y) --> ~ P y))"
by (tactic\<open>Meson.safe_best_meson_tac @{context} 1\<close>)
    \<comment>\<open>In contrast, \<open>meson\<close> is SLOW: 7.6s on griffon\<close>


subsubsection\<open>Pelletier's examples\<close>
text\<open>1\<close>
lemma "(P --> Q)  =  (~Q --> ~P)"
by blast

text\<open>2\<close>
lemma "(~ ~ P) =  P"
by blast

text\<open>3\<close>
lemma "~(P-->Q) --> (Q-->P)"
by blast

text\<open>4\<close>
lemma "(~P-->Q)  =  (~Q --> P)"
by blast

text\<open>5\<close>
lemma "((P|Q)-->(P|R)) --> (P|(Q-->R))"
by blast

text\<open>6\<close>
lemma "P | ~ P"
by blast

text\<open>7\<close>
lemma "P | ~ ~ ~ P"
by blast

text\<open>8.  Peirce's law\<close>
lemma "((P-->Q) --> P)  -->  P"
by blast

text\<open>9\<close>
lemma "((P|Q) & (~P|Q) & (P| ~Q)) --> ~ (~P | ~Q)"
by blast

text\<open>10\<close>
lemma "(Q-->R) & (R-->P&Q) & (P-->Q|R) --> (P=Q)"
by blast

text\<open>11.  Proved in each direction (incorrectly, says Pelletier!!)\<close>
lemma "P=(P::bool)"
by blast

text\<open>12.  "Dijkstra's law"\<close>
lemma "((P = Q) = R) = (P = (Q = R))"
by blast

text\<open>13.  Distributive law\<close>
lemma "(P | (Q & R)) = ((P | Q) & (P | R))"
by blast

text\<open>14\<close>
lemma "(P = Q) = ((Q | ~P) & (~Q|P))"
by blast

text\<open>15\<close>
lemma "(P --> Q) = (~P | Q)"
by blast

text\<open>16\<close>
lemma "(P-->Q) | (Q-->P)"
by blast

text\<open>17\<close>
lemma "((P & (Q-->R))-->S)  =  ((~P | Q | S) & (~P | ~R | S))"
by blast

subsubsection\<open>Classical Logic: examples with quantifiers\<close>

lemma "(\<forall>x. P x & Q x) = ((\<forall>x. P x) & (\<forall>x. Q x))"
by blast

lemma "(\<exists>x. P --> Q x)  =  (P --> (\<exists>x. Q x))"
by blast

lemma "(\<exists>x. P x --> Q) = ((\<forall>x. P x) --> Q)"
by blast

lemma "((\<forall>x. P x) | Q)  =  (\<forall>x. P x | Q)"
by blast

lemma "(\<forall>x. P x --> P(f x))  &  P d --> P(f(f(f d)))"
by blast

text\<open>Needs double instantiation of EXISTS\<close>
lemma "\<exists>x. P x --> P a & P b"
by blast

lemma "\<exists>z. P z --> (\<forall>x. P x)"
by blast

text\<open>From a paper by Claire Quigley\<close>
lemma "\<exists>y. ((P c & Q y) | (\<exists>z. ~ Q z)) | (\<exists>x. ~ P x & Q d)"
by fast

subsubsection\<open>Hard examples with quantifiers\<close>

text\<open>Problem 18\<close>
lemma "\<exists>y. \<forall>x. P y --> P x"
by blast

text\<open>Problem 19\<close>
lemma "\<exists>x. \<forall>y z. (P y --> Q z) --> (P x --> Q x)"
by blast

text\<open>Problem 20\<close>
lemma "(\<forall>x y. \<exists>z. \<forall>w. (P x & Q y --> R z & S w))
    --> (\<exists>x y. P x & Q y) --> (\<exists>z. R z)"
by blast

text\<open>Problem 21\<close>
lemma "(\<exists>x. P --> Q x) & (\<exists>x. Q x --> P) --> (\<exists>x. P=Q x)"
by blast

text\<open>Problem 22\<close>
lemma "(\<forall>x. P = Q x)  -->  (P = (\<forall>x. Q x))"
by blast

text\<open>Problem 23\<close>
lemma "(\<forall>x. P | Q x)  =  (P | (\<forall>x. Q x))"
by blast

text\<open>Problem 24\<close>  (*The first goal clause is useless*)
lemma "~(\<exists>x. S x & Q x) & (\<forall>x. P x --> Q x | R x) &
      (~(\<exists>x. P x) --> (\<exists>x. Q x)) & (\<forall>x. Q x | R x --> S x)
    --> (\<exists>x. P x & R x)"
by blast

text\<open>Problem 25\<close>
lemma "(\<exists>x. P x) &
      (\<forall>x. L x --> ~ (M x & R x)) &
      (\<forall>x. P x --> (M x & L x)) &
      ((\<forall>x. P x --> Q x) | (\<exists>x. P x & R x))
    --> (\<exists>x. Q x & P x)"
by blast

text\<open>Problem 26; has 24 Horn clauses\<close>
lemma "((\<exists>x. p x) = (\<exists>x. q x)) &
      (\<forall>x. \<forall>y. p x & q y --> (r x = s y))
  --> ((\<forall>x. p x --> r x) = (\<forall>x. q x --> s x))"
by blast

text\<open>Problem 27; has 13 Horn clauses\<close>
lemma "(\<exists>x. P x & ~Q x) &
      (\<forall>x. P x --> R x) &
      (\<forall>x. M x & L x --> P x) &
      ((\<exists>x. R x & ~ Q x) --> (\<forall>x. L x --> ~ R x))
      --> (\<forall>x. M x --> ~L x)"
by blast

text\<open>Problem 28.  AMENDED; has 14 Horn clauses\<close>
lemma "(\<forall>x. P x --> (\<forall>x. Q x)) &
      ((\<forall>x. Q x | R x) --> (\<exists>x. Q x & S x)) &
      ((\<exists>x. S x) --> (\<forall>x. L x --> M x))
    --> (\<forall>x. P x & L x --> M x)"
by blast

text\<open>Problem 29.  Essentially the same as Principia Mathematica *11.71.
      62 Horn clauses\<close>
lemma "(\<exists>x. F x) & (\<exists>y. G y)
    --> ( ((\<forall>x. F x --> H x) & (\<forall>y. G y --> J y))  =
          (\<forall>x y. F x & G y --> H x & J y))"
by blast


text\<open>Problem 30\<close>
lemma "(\<forall>x. P x | Q x --> ~ R x) & (\<forall>x. (Q x --> ~ S x) --> P x & R x)
       --> (\<forall>x. S x)"
by blast

text\<open>Problem 31; has 10 Horn clauses; first negative clauses is useless\<close>
lemma "~(\<exists>x. P x & (Q x | R x)) &
      (\<exists>x. L x & P x) &
      (\<forall>x. ~ R x --> M x)
    --> (\<exists>x. L x & M x)"
by blast

text\<open>Problem 32\<close>
lemma "(\<forall>x. P x & (Q x | R x)-->S x) &
      (\<forall>x. S x & R x --> L x) &
      (\<forall>x. M x --> R x)
    --> (\<forall>x. P x & M x --> L x)"
by blast

text\<open>Problem 33; has 55 Horn clauses\<close>
lemma "(\<forall>x. P a & (P x --> P b)-->P c)  =
      (\<forall>x. (~P a | P x | P c) & (~P a | ~P b | P c))"
by blast

text\<open>Problem 34: Andrews's challenge has 924 Horn clauses\<close>
lemma "((\<exists>x. \<forall>y. p x = p y)  = ((\<exists>x. q x) = (\<forall>y. p y)))     =
      ((\<exists>x. \<forall>y. q x = q y)  = ((\<exists>x. p x) = (\<forall>y. q y)))"
by blast

text\<open>Problem 35\<close>
lemma "\<exists>x y. P x y -->  (\<forall>u v. P u v)"
by blast

text\<open>Problem 36; has 15 Horn clauses\<close>
lemma "(\<forall>x. \<exists>y. J x y) & (\<forall>x. \<exists>y. G x y) &
       (\<forall>x y. J x y | G x y --> (\<forall>z. J y z | G y z --> H x z))
       --> (\<forall>x. \<exists>y. H x y)"
by blast

text\<open>Problem 37; has 10 Horn clauses\<close>
lemma "(\<forall>z. \<exists>w. \<forall>x. \<exists>y.
           (P x z --> P y w) & P y z & (P y w --> (\<exists>u. Q u w))) &
      (\<forall>x z. ~P x z --> (\<exists>y. Q y z)) &
      ((\<exists>x y. Q x y) --> (\<forall>x. R x x))
    --> (\<forall>x. \<exists>y. R x y)"
by blast \<comment>\<open>causes unification tracing messages\<close>


text\<open>Problem 38\<close>  text\<open>Quite hard: 422 Horn clauses!!\<close>
lemma "(\<forall>x. p a & (p x --> (\<exists>y. p y & r x y)) -->
           (\<exists>z. \<exists>w. p z & r x w & r w z))  =
      (\<forall>x. (~p a | p x | (\<exists>z. \<exists>w. p z & r x w & r w z)) &
            (~p a | ~(\<exists>y. p y & r x y) |
             (\<exists>z. \<exists>w. p z & r x w & r w z)))"
by blast

text\<open>Problem 39\<close>
lemma "~ (\<exists>x. \<forall>y. F y x = (~F y y))"
by blast

text\<open>Problem 40.  AMENDED\<close>
lemma "(\<exists>y. \<forall>x. F x y = F x x)
      -->  ~ (\<forall>x. \<exists>y. \<forall>z. F z y = (~F z x))"
by blast

text\<open>Problem 41\<close>
lemma "(\<forall>z. (\<exists>y. (\<forall>x. f x y = (f x z & ~ f x x))))
      --> ~ (\<exists>z. \<forall>x. f x z)"
by blast

text\<open>Problem 42\<close>
lemma "~ (\<exists>y. \<forall>x. p x y = (~ (\<exists>z. p x z & p z x)))"
by blast

text\<open>Problem 43  NOW PROVED AUTOMATICALLY!!\<close>
lemma "(\<forall>x. \<forall>y. q x y = (\<forall>z. p z x = (p z y::bool)))
      --> (\<forall>x. (\<forall>y. q x y = (q y x::bool)))"
by blast

text\<open>Problem 44: 13 Horn clauses; 7-step proof\<close>
lemma "(\<forall>x. f x --> (\<exists>y. g y & h x y & (\<exists>y. g y & ~ h x y)))  &
       (\<exists>x. j x & (\<forall>y. g y --> h x y))
       --> (\<exists>x. j x & ~f x)"
by blast

text\<open>Problem 45; has 27 Horn clauses; 54-step proof\<close>
lemma "(\<forall>x. f x & (\<forall>y. g y & h x y --> j x y)
            --> (\<forall>y. g y & h x y --> k y)) &
      ~ (\<exists>y. l y & k y) &
      (\<exists>x. f x & (\<forall>y. h x y --> l y)
                & (\<forall>y. g y & h x y --> j x y))
      --> (\<exists>x. f x & ~ (\<exists>y. g y & h x y))"
by blast

text\<open>Problem 46; has 26 Horn clauses; 21-step proof\<close>
lemma "(\<forall>x. f x & (\<forall>y. f y & h y x --> g y) --> g x) &
       ((\<exists>x. f x & ~g x) -->
       (\<exists>x. f x & ~g x & (\<forall>y. f y & ~g y --> j x y))) &
       (\<forall>x y. f x & f y & h x y --> ~j y x)
       --> (\<forall>x. f x --> g x)"
by blast

text\<open>Problem 47.  Schubert's Steamroller.
      26 clauses; 63 Horn clauses.
      87094 inferences so far.  Searching to depth 36\<close>
lemma "(\<forall>x. wolf x \<longrightarrow> animal x) & (\<exists>x. wolf x) &
       (\<forall>x. fox x \<longrightarrow> animal x) & (\<exists>x. fox x) &
       (\<forall>x. bird x \<longrightarrow> animal x) & (\<exists>x. bird x) &
       (\<forall>x. caterpillar x \<longrightarrow> animal x) & (\<exists>x. caterpillar x) &
       (\<forall>x. snail x \<longrightarrow> animal x) & (\<exists>x. snail x) &
       (\<forall>x. grain x \<longrightarrow> plant x) & (\<exists>x. grain x) &
       (\<forall>x. animal x \<longrightarrow>
             ((\<forall>y. plant y \<longrightarrow> eats x y)  \<or> 
              (\<forall>y. animal y & smaller_than y x &
                    (\<exists>z. plant z & eats y z) \<longrightarrow> eats x y))) &
       (\<forall>x y. bird y & (snail x \<or> caterpillar x) \<longrightarrow> smaller_than x y) &
       (\<forall>x y. bird x & fox y \<longrightarrow> smaller_than x y) &
       (\<forall>x y. fox x & wolf y \<longrightarrow> smaller_than x y) &
       (\<forall>x y. wolf x & (fox y \<or> grain y) \<longrightarrow> ~eats x y) &
       (\<forall>x y. bird x & caterpillar y \<longrightarrow> eats x y) &
       (\<forall>x y. bird x & snail y \<longrightarrow> ~eats x y) &
       (\<forall>x. (caterpillar x \<or> snail x) \<longrightarrow> (\<exists>y. plant y & eats x y))
       \<longrightarrow> (\<exists>x y. animal x & animal y & (\<exists>z. grain z & eats y z & eats x y))"
by (tactic\<open>Meson.safe_best_meson_tac @{context} 1\<close>)
    \<comment>\<open>Nearly twice as fast as \<open>meson\<close>,
        which performs iterative deepening rather than best-first search\<close>

text\<open>The Los problem. Circulated by John Harrison\<close>
lemma "(\<forall>x y z. P x y & P y z --> P x z) &
       (\<forall>x y z. Q x y & Q y z --> Q x z) &
       (\<forall>x y. P x y --> P y x) &
       (\<forall>x y. P x y | Q x y)
       --> (\<forall>x y. P x y) | (\<forall>x y. Q x y)"
by meson

text\<open>A similar example, suggested by Johannes Schumann and
 credited to Pelletier\<close>
lemma "(\<forall>x y z. P x y --> P y z --> P x z) -->
       (\<forall>x y z. Q x y --> Q y z --> Q x z) -->
       (\<forall>x y. Q x y --> Q y x) -->  (\<forall>x y. P x y | Q x y) -->
       (\<forall>x y. P x y) | (\<forall>x y. Q x y)"
by meson

text\<open>Problem 50.  What has this to do with equality?\<close>
lemma "(\<forall>x. P a x | (\<forall>y. P x y)) --> (\<exists>x. \<forall>y. P x y)"
by blast

text\<open>Problem 54: NOT PROVED\<close>
lemma "(\<forall>y::'a. \<exists>z. \<forall>x. F x z = (x=y)) -->
      ~ (\<exists>w. \<forall>x. F x w = (\<forall>u. F x u --> (\<exists>y. F y u & ~ (\<exists>z. F z u & F z y))))"
oops 


text\<open>Problem 55\<close>

text\<open>Non-equational version, from Manthey and Bry, CADE-9 (Springer, 1988).
  \<open>meson\<close> cannot report who killed Agatha.\<close>
lemma "lives agatha & lives butler & lives charles &
       (killed agatha agatha | killed butler agatha | killed charles agatha) &
       (\<forall>x y. killed x y --> hates x y & ~richer x y) &
       (\<forall>x. hates agatha x --> ~hates charles x) &
       (hates agatha agatha & hates agatha charles) &
       (\<forall>x. lives x & ~richer x agatha --> hates butler x) &
       (\<forall>x. hates agatha x --> hates butler x) &
       (\<forall>x. ~hates x agatha | ~hates x butler | ~hates x charles) -->
       (\<exists>x. killed x agatha)"
by meson

text\<open>Problem 57\<close>
lemma "P (f a b) (f b c) & P (f b c) (f a c) &
      (\<forall>x y z. P x y & P y z --> P x z)    -->   P (f a b) (f a c)"
by blast

text\<open>Problem 58: Challenge found on info-hol\<close>
lemma "\<forall>P Q R x. \<exists>v w. \<forall>y z. P x & Q y --> (P v | R w) & (R z --> Q v)"
by blast

text\<open>Problem 59\<close>
lemma "(\<forall>x. P x = (~P(f x))) --> (\<exists>x. P x & ~P(f x))"
by blast

text\<open>Problem 60\<close>
lemma "\<forall>x. P x (f x) = (\<exists>y. (\<forall>z. P z y --> P z (f x)) & P x y)"
by blast

text\<open>Problem 62 as corrected in JAR 18 (1997), page 135\<close>
lemma "(\<forall>x. p a & (p x --> p(f x)) --> p(f(f x)))  =
       (\<forall>x. (~ p a | p x | p(f(f x))) &
            (~ p a | ~ p(f x) | p(f(f x))))"
by blast

text\<open>Charles Morgan's problems\<close>
context
  fixes T i n
  assumes a: "\<forall>x y. T(i x(i y x))"
    and b: "\<forall>x y z. T(i (i x (i y z)) (i (i x y) (i x z)))"
    and c: "\<forall>x y. T(i (i (n x) (n y)) (i y x))"
    and c': "\<forall>x y. T(i (i y x) (i (n x) (n y)))"
    and d: "\<forall>x y. T(i x y) & T x --> T y"
begin

lemma "\<forall>x. T(i x x)"
  using a b d by blast

lemma "\<forall>x. T(i x (n(n x)))" \<comment>\<open>Problem 66\<close>
  using a b c d by metis

lemma "\<forall>x. T(i (n(n x)) x)" \<comment>\<open>Problem 67\<close>
  using a b c d by meson \<comment>\<open>4.9s on griffon. 51061 inferences, depth 21\<close>

lemma "\<forall>x. T(i x (n(n x)))" \<comment>\<open>Problem 68: not proved.  Listed as satisfiable in TPTP (LCL078-1)\<close>
  using a b c' d oops

end

text\<open>Problem 71, as found in TPTP (SYN007+1.005)\<close>
lemma "p1 = (p2 = (p3 = (p4 = (p5 = (p1 = (p2 = (p3 = (p4 = p5))))))))"
  by blast

end
