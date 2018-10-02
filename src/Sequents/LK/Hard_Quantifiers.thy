(*  Title:      Sequents/LK/Hard_Quantifiers.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Hard examples with quantifiers.  Can be read to test the LK system.
From  F. J. Pelletier,
  Seventy-Five Problems for Testing Automatic Theorem Provers,
  J. Automated Reasoning 2 (1986), 191-216.
  Errata, JAR 4 (1988), 236-236.

Uses pc_tac rather than fast_tac when the former is significantly faster.
*)

theory Hard_Quantifiers
imports "../LK"
begin

lemma "\<turnstile> (\<forall>x. P(x) \<and> Q(x)) \<longleftrightarrow> (\<forall>x. P(x)) \<and> (\<forall>x. Q(x))"
  by fast

lemma "\<turnstile> (\<exists>x. P \<longrightarrow> Q(x)) \<longleftrightarrow> (P \<longrightarrow> (\<exists>x. Q(x)))"
  by fast

lemma "\<turnstile> (\<exists>x. P(x) \<longrightarrow> Q) \<longleftrightarrow> (\<forall>x. P(x)) \<longrightarrow> Q"
  by fast

lemma "\<turnstile> (\<forall>x. P(x)) \<or> Q \<longleftrightarrow> (\<forall>x. P(x) \<or> Q)"
  by fast


text "Problems requiring quantifier duplication"

(*Not provable by fast: needs multiple instantiation of \<forall>*)
lemma "\<turnstile> (\<forall>x. P(x) \<longrightarrow> P(f(x))) \<and> P(d) \<longrightarrow> P(f(f(f(d))))"
  by best_dup

(*Needs double instantiation of the quantifier*)
lemma "\<turnstile> \<exists>x. P(x) \<longrightarrow> P(a) \<and> P(b)"
  by fast_dup

lemma "\<turnstile> \<exists>z. P(z) \<longrightarrow> (\<forall>x. P(x))"
  by best_dup


text "Hard examples with quantifiers"

text "Problem 18"
lemma "\<turnstile> \<exists>y. \<forall>x. P(y)\<longrightarrow>P(x)"
  by best_dup

text "Problem 19"
lemma "\<turnstile> \<exists>x. \<forall>y z. (P(y)\<longrightarrow>Q(z)) \<longrightarrow> (P(x)\<longrightarrow>Q(x))"
  by best_dup

text "Problem 20"
lemma "\<turnstile> (\<forall>x y. \<exists>z. \<forall>w. (P(x) \<and> Q(y)\<longrightarrow>R(z) \<and> S(w)))
    \<longrightarrow> (\<exists>x y. P(x) \<and> Q(y)) \<longrightarrow> (\<exists>z. R(z))"
  by fast

text "Problem 21"
lemma "\<turnstile> (\<exists>x. P \<longrightarrow> Q(x)) \<and> (\<exists>x. Q(x) \<longrightarrow> P) \<longrightarrow> (\<exists>x. P \<longleftrightarrow> Q(x))"
  by best_dup

text "Problem 22"
lemma "\<turnstile> (\<forall>x. P \<longleftrightarrow> Q(x)) \<longrightarrow> (P \<longleftrightarrow> (\<forall>x. Q(x)))"
  by fast

text "Problem 23"
lemma "\<turnstile> (\<forall>x. P \<or> Q(x)) \<longleftrightarrow> (P \<or> (\<forall>x. Q(x)))"
  by best

text "Problem 24"
lemma "\<turnstile> \<not> (\<exists>x. S(x) \<and> Q(x)) \<and> (\<forall>x. P(x) \<longrightarrow> Q(x) \<or> R(x)) \<and>
     \<not> (\<exists>x. P(x)) \<longrightarrow> (\<exists>x. Q(x)) \<and> (\<forall>x. Q(x) \<or> R(x) \<longrightarrow> S(x))
    \<longrightarrow> (\<exists>x. P(x) \<and> R(x))"
  by pc

text "Problem 25"
lemma "\<turnstile> (\<exists>x. P(x)) \<and>
        (\<forall>x. L(x) \<longrightarrow> \<not> (M(x) \<and> R(x))) \<and>
        (\<forall>x. P(x) \<longrightarrow> (M(x) \<and> L(x))) \<and>
        ((\<forall>x. P(x)\<longrightarrow>Q(x)) \<or> (\<exists>x. P(x) \<and> R(x)))
    \<longrightarrow> (\<exists>x. Q(x) \<and> P(x))"
  by best

text "Problem 26"
lemma "\<turnstile> ((\<exists>x. p(x)) \<longleftrightarrow> (\<exists>x. q(x))) \<and>
      (\<forall>x. \<forall>y. p(x) \<and> q(y) \<longrightarrow> (r(x) \<longleftrightarrow> s(y)))
  \<longrightarrow> ((\<forall>x. p(x)\<longrightarrow>r(x)) \<longleftrightarrow> (\<forall>x. q(x)\<longrightarrow>s(x)))"
  by pc

text "Problem 27"
lemma "\<turnstile> (\<exists>x. P(x) \<and> \<not> Q(x)) \<and>
              (\<forall>x. P(x) \<longrightarrow> R(x)) \<and>
              (\<forall>x. M(x) \<and> L(x) \<longrightarrow> P(x)) \<and>
              ((\<exists>x. R(x) \<and> \<not> Q(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> \<not> R(x)))
          \<longrightarrow> (\<forall>x. M(x) \<longrightarrow> \<not> L(x))"
  by pc

text "Problem 28.  AMENDED"
lemma "\<turnstile> (\<forall>x. P(x) \<longrightarrow> (\<forall>x. Q(x))) \<and>
        ((\<forall>x. Q(x) \<or> R(x)) \<longrightarrow> (\<exists>x. Q(x) \<and> S(x))) \<and>
        ((\<exists>x. S(x)) \<longrightarrow> (\<forall>x. L(x) \<longrightarrow> M(x)))
    \<longrightarrow> (\<forall>x. P(x) \<and> L(x) \<longrightarrow> M(x))"
  by pc

text "Problem 29.  Essentially the same as Principia Mathematica *11.71"
lemma "\<turnstile> (\<exists>x. P(x)) \<and> (\<exists>y. Q(y))
    \<longrightarrow> ((\<forall>x. P(x) \<longrightarrow> R(x)) \<and> (\<forall>y. Q(y) \<longrightarrow> S(y)) \<longleftrightarrow>
         (\<forall>x y. P(x) \<and> Q(y) \<longrightarrow> R(x) \<and> S(y)))"
  by pc

text "Problem 30"
lemma "\<turnstile> (\<forall>x. P(x) \<or> Q(x) \<longrightarrow> \<not> R(x)) \<and>
        (\<forall>x. (Q(x) \<longrightarrow> \<not> S(x)) \<longrightarrow> P(x) \<and> R(x))
    \<longrightarrow> (\<forall>x. S(x))"
  by fast

text "Problem 31"
lemma "\<turnstile> \<not> (\<exists>x. P(x) \<and> (Q(x) \<or> R(x))) \<and>
        (\<exists>x. L(x) \<and> P(x)) \<and>
        (\<forall>x. \<not> R(x) \<longrightarrow> M(x))
    \<longrightarrow> (\<exists>x. L(x) \<and> M(x))"
  by fast

text "Problem 32"
lemma "\<turnstile> (\<forall>x. P(x) \<and> (Q(x) \<or> R(x)) \<longrightarrow> S(x)) \<and>
        (\<forall>x. S(x) \<and> R(x) \<longrightarrow> L(x)) \<and>
        (\<forall>x. M(x) \<longrightarrow> R(x))
    \<longrightarrow> (\<forall>x. P(x) \<and> M(x) \<longrightarrow> L(x))"
  by best

text "Problem 33"
lemma "\<turnstile> (\<forall>x. P(a) \<and> (P(x) \<longrightarrow> P(b)) \<longrightarrow> P(c)) \<longleftrightarrow>
     (\<forall>x. (\<not> P(a) \<or> P(x) \<or> P(c)) \<and> (\<not> P(a) \<or> \<not> P(b) \<or> P(c)))"
  by fast

text "Problem 34  AMENDED (TWICE!!)"
(*Andrews's challenge*)
lemma "\<turnstile> ((\<exists>x. \<forall>y. p(x) \<longleftrightarrow> p(y))  \<longleftrightarrow>
               ((\<exists>x. q(x)) \<longleftrightarrow> (\<forall>y. p(y))))     \<longleftrightarrow>
              ((\<exists>x. \<forall>y. q(x) \<longleftrightarrow> q(y))  \<longleftrightarrow>
               ((\<exists>x. p(x)) \<longleftrightarrow> (\<forall>y. q(y))))"
  by best_dup

text "Problem 35"
lemma "\<turnstile> \<exists>x y. P(x,y) \<longrightarrow> (\<forall>u v. P(u,v))"
  by best_dup

text "Problem 36"
lemma "\<turnstile> (\<forall>x. \<exists>y. J(x,y)) \<and>
         (\<forall>x. \<exists>y. G(x,y)) \<and>
         (\<forall>x y. J(x,y) \<or> G(x,y) \<longrightarrow>
         (\<forall>z. J(y,z) \<or> G(y,z) \<longrightarrow> H(x,z)))
         \<longrightarrow> (\<forall>x. \<exists>y. H(x,y))"
  by fast

text "Problem 37"
lemma "\<turnstile> (\<forall>z. \<exists>w. \<forall>x. \<exists>y.
           (P(x,z)\<longrightarrow>P(y,w)) \<and> P(y,z) \<and> (P(y,w) \<longrightarrow> (\<exists>u. Q(u,w)))) \<and>
        (\<forall>x z. \<not> P(x,z) \<longrightarrow> (\<exists>y. Q(y,z))) \<and>
        ((\<exists>x y. Q(x,y)) \<longrightarrow> (\<forall>x. R(x,x)))
    \<longrightarrow> (\<forall>x. \<exists>y. R(x,y))"
  by pc

text "Problem 38"
lemma "\<turnstile> (\<forall>x. p(a) \<and> (p(x) \<longrightarrow> (\<exists>y. p(y) \<and> r(x,y))) \<longrightarrow>
                 (\<exists>z. \<exists>w. p(z) \<and> r(x,w) \<and> r(w,z)))  \<longleftrightarrow>
         (\<forall>x. (\<not> p(a) \<or> p(x) \<or> (\<exists>z. \<exists>w. p(z) \<and> r(x,w) \<and> r(w,z))) \<and>
                 (\<not> p(a) \<or> \<not> (\<exists>y. p(y) \<and> r(x,y)) \<or>
                 (\<exists>z. \<exists>w. p(z) \<and> r(x,w) \<and> r(w,z))))"
  by pc

text "Problem 39"
lemma "\<turnstile> \<not> (\<exists>x. \<forall>y. F(y,x) \<longleftrightarrow> \<not> F(y,y))"
  by fast

text "Problem 40.  AMENDED"
lemma "\<turnstile> (\<exists>y. \<forall>x. F(x,y) \<longleftrightarrow> F(x,x)) \<longrightarrow>
         \<not> (\<forall>x. \<exists>y. \<forall>z. F(z,y) \<longleftrightarrow> \<not> F(z,x))"
  by fast

text "Problem 41"
lemma "\<turnstile> (\<forall>z. \<exists>y. \<forall>x. f(x,y) \<longleftrightarrow> f(x,z) \<and> \<not> f(x,x))
         \<longrightarrow> \<not> (\<exists>z. \<forall>x. f(x,z))"
  by fast

text "Problem 42"
lemma "\<turnstile> \<not> (\<exists>y. \<forall>x. p(x,y) \<longleftrightarrow> \<not> (\<exists>z. p(x,z) \<and> p(z,x)))"
  oops

text "Problem 43"
lemma "\<turnstile> (\<forall>x. \<forall>y. q(x,y) \<longleftrightarrow> (\<forall>z. p(z,x) \<longleftrightarrow> p(z,y)))
          \<longrightarrow> (\<forall>x. (\<forall>y. q(x,y) \<longleftrightarrow> q(y,x)))"
  oops

text "Problem 44"
lemma "\<turnstile> (\<forall>x. f(x) \<longrightarrow>
                 (\<exists>y. g(y) \<and> h(x,y) \<and> (\<exists>y. g(y) \<and> \<not> h(x,y)))) \<and>
         (\<exists>x. j(x) \<and> (\<forall>y. g(y) \<longrightarrow> h(x,y)))
         \<longrightarrow> (\<exists>x. j(x) \<and> \<not> f(x))"
  by fast

text "Problem 45"
lemma "\<turnstile> (\<forall>x. f(x) \<and> (\<forall>y. g(y) \<and> h(x,y) \<longrightarrow> j(x,y))
                      \<longrightarrow> (\<forall>y. g(y) \<and> h(x,y) \<longrightarrow> k(y))) \<and>
      \<not> (\<exists>y. l(y) \<and> k(y)) \<and>
      (\<exists>x. f(x) \<and> (\<forall>y. h(x,y) \<longrightarrow> l(y))
                   \<and> (\<forall>y. g(y) \<and> h(x,y) \<longrightarrow> j(x,y)))
      \<longrightarrow> (\<exists>x. f(x) \<and> \<not> (\<exists>y. g(y) \<and> h(x,y)))"
  by best


text "Problems (mainly) involving equality or functions"

text "Problem 48"
lemma "\<turnstile> (a = b \<or> c = d) \<and> (a = c \<or> b = d) \<longrightarrow> a = d \<or> b = c"
  by (fast add!: subst)

text "Problem 50"
lemma "\<turnstile> (\<forall>x. P(a,x) \<or> (\<forall>y. P(x,y))) \<longrightarrow> (\<exists>x. \<forall>y. P(x,y))"
  by best_dup

text "Problem 51"
lemma "\<turnstile> (\<exists>z w. \<forall>x y. P(x,y) \<longleftrightarrow> (x = z \<and> y = w)) \<longrightarrow>
         (\<exists>z. \<forall>x. \<exists>w. (\<forall>y. P(x,y) \<longleftrightarrow> y = w) \<longleftrightarrow> x = z)"
  by (fast add!: subst)

text "Problem 52"  (*Almost the same as 51. *)
lemma "\<turnstile> (\<exists>z w. \<forall>x y. P(x,y) \<longleftrightarrow> (x = z \<and> y = w)) \<longrightarrow>
         (\<exists>w. \<forall>y. \<exists>z. (\<forall>x. P(x,y) \<longleftrightarrow> x = z) \<longleftrightarrow> y = w)"
  by (fast add!: subst)

text "Problem 56"
lemma "\<turnstile> (\<forall>x.(\<exists>y. P(y) \<and> x = f(y)) \<longrightarrow> P(x)) \<longleftrightarrow> (\<forall>x. P(x) \<longrightarrow> P(f(x)))"
  by (best add: symL subst)
  (*requires tricker to orient the equality properly*)

text "Problem 57"
lemma "\<turnstile> P(f(a,b), f(b,c)) \<and> P(f(b,c), f(a,c)) \<and>
         (\<forall>x y z. P(x,y) \<and> P(y,z) \<longrightarrow> P(x,z)) \<longrightarrow> P(f(a,b), f(a,c))"
  by fast

text "Problem 58!"
lemma "\<turnstile> (\<forall>x y. f(x) = g(y)) \<longrightarrow> (\<forall>x y. f(f(x)) = f(g(y)))"
  by (fast add!: subst)

text "Problem 59"
(*Unification works poorly here -- the abstraction %sobj prevents efficient
  operation of the occurs check*)
lemma "\<turnstile> (\<forall>x. P(x) \<longleftrightarrow> \<not> P(f(x))) \<longrightarrow> (\<exists>x. P(x) \<and> \<not> P(f(x)))"
  using [[unify_trace_bound = 50]]
  by best_dup

text "Problem 60"
lemma "\<turnstile> \<forall>x. P(x,f(x)) \<longleftrightarrow> (\<exists>y. (\<forall>z. P(z,y) \<longrightarrow> P(z,f(x))) \<and> P(x,y))"
  by fast

text "Problem 62 as corrected in JAR 18 (1997), page 135"
lemma "\<turnstile> (\<forall>x. p(a) \<and> (p(x) \<longrightarrow> p(f(x))) \<longrightarrow> p(f(f(x)))) \<longleftrightarrow>
      (\<forall>x. (\<not> p(a) \<or> p(x) \<or> p(f(f(x)))) \<and>
              (\<not> p(a) \<or> \<not> p(f(x)) \<or> p(f(f(x)))))"
  by fast

(*18 June 92: loaded in 372 secs*)
(*19 June 92: loaded in 166 secs except #34, using repeat_goal_tac*)
(*29 June 92: loaded in 370 secs*)
(*18 September 2005: loaded in 1.809 secs*)

end
