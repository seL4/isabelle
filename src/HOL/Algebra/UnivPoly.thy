(*  Title:      HOL/Algebra/UnivPoly.thy
    Author:     Clemens Ballarin, started 9 December 1996
    Copyright:  Clemens Ballarin

Contributions, in particular on long division, by Jesus Aransay.
*)

theory UnivPoly
imports Module RingHom
begin

section {* Univariate Polynomials *}

text {*
  Polynomials are formalised as modules with additional operations for
  extracting coefficients from polynomials and for obtaining monomials
  from coefficients and exponents (record @{text "up_ring"}).  The
  carrier set is a set of bounded functions from Nat to the
  coefficient domain.  Bounded means that these functions return zero
  above a certain bound (the degree).  There is a chapter on the
  formalisation of polynomials in the PhD thesis \cite{Ballarin:1999},
  which was implemented with axiomatic type classes.  This was later
  ported to Locales.
*}


subsection {* The Constructor for Univariate Polynomials *}

text {*
  Functions with finite support.
*}

locale bound =
  fixes z :: 'a
    and n :: nat
    and f :: "nat => 'a"
  assumes bound: "!!m. n < m \<Longrightarrow> f m = z"

declare bound.intro [intro!]
  and bound.bound [dest]

lemma bound_below:
  assumes bound: "bound z m f" and nonzero: "f n \<noteq> z" shows "n \<le> m"
proof (rule classical)
  assume "~ ?thesis"
  then have "m < n" by arith
  with bound have "f n = z" ..
  with nonzero show ?thesis by contradiction
qed

record ('a, 'p) up_ring = "('a, 'p) module" +
  monom :: "['a, nat] => 'p"
  coeff :: "['p, nat] => 'a"

definition
  up :: "('a, 'm) ring_scheme => (nat => 'a) set"
  where "up R = {f. f \<in> UNIV -> carrier R & (EX n. bound \<zero>\<^bsub>R\<^esub> n f)}"

definition UP :: "('a, 'm) ring_scheme => ('a, nat => 'a) up_ring"
  where "UP R = (|
   carrier = up R,
   mult = (%p:up R. %q:up R. %n. \<Oplus>\<^bsub>R\<^esub>i \<in> {..n}. p i \<otimes>\<^bsub>R\<^esub> q (n-i)),
   one = (%i. if i=0 then \<one>\<^bsub>R\<^esub> else \<zero>\<^bsub>R\<^esub>),
   zero = (%i. \<zero>\<^bsub>R\<^esub>),
   add = (%p:up R. %q:up R. %i. p i \<oplus>\<^bsub>R\<^esub> q i),
   smult = (%a:carrier R. %p:up R. %i. a \<otimes>\<^bsub>R\<^esub> p i),
   monom = (%a:carrier R. %n i. if i=n then a else \<zero>\<^bsub>R\<^esub>),
   coeff = (%p:up R. %n. p n) |)"

text {*
  Properties of the set of polynomials @{term up}.
*}

lemma mem_upI [intro]:
  "[| !!n. f n \<in> carrier R; EX n. bound (zero R) n f |] ==> f \<in> up R"
  by (simp add: up_def Pi_def)

lemma mem_upD [dest]:
  "f \<in> up R ==> f n \<in> carrier R"
  by (simp add: up_def Pi_def)

context ring
begin

lemma bound_upD [dest]: "f \<in> up R ==> EX n. bound \<zero> n f" by (simp add: up_def)

lemma up_one_closed: "(%n. if n = 0 then \<one> else \<zero>) \<in> up R" using up_def by force

lemma up_smult_closed: "[| a \<in> carrier R; p \<in> up R |] ==> (%i. a \<otimes> p i) \<in> up R" by force

lemma up_add_closed:
  "[| p \<in> up R; q \<in> up R |] ==> (%i. p i \<oplus> q i) \<in> up R"
proof
  fix n
  assume "p \<in> up R" and "q \<in> up R"
  then show "p n \<oplus> q n \<in> carrier R"
    by auto
next
  assume UP: "p \<in> up R" "q \<in> up R"
  show "EX n. bound \<zero> n (%i. p i \<oplus> q i)"
  proof -
    from UP obtain n where boundn: "bound \<zero> n p" by fast
    from UP obtain m where boundm: "bound \<zero> m q" by fast
    have "bound \<zero> (max n m) (%i. p i \<oplus> q i)"
    proof
      fix i
      assume "max n m < i"
      with boundn and boundm and UP show "p i \<oplus> q i = \<zero>" by fastforce
    qed
    then show ?thesis ..
  qed
qed

lemma up_a_inv_closed:
  "p \<in> up R ==> (%i. \<ominus> (p i)) \<in> up R"
proof
  assume R: "p \<in> up R"
  then obtain n where "bound \<zero> n p" by auto
  then have "bound \<zero> n (%i. \<ominus> p i)" by auto
  then show "EX n. bound \<zero> n (%i. \<ominus> p i)" by auto
qed auto

lemma up_minus_closed:
  "[| p \<in> up R; q \<in> up R |] ==> (%i. p i \<ominus> q i) \<in> up R"
  using mem_upD [of p R] mem_upD [of q R] up_add_closed up_a_inv_closed a_minus_def [of _ R]
  by auto

lemma up_mult_closed:
  "[| p \<in> up R; q \<in> up R |] ==>
  (%n. \<Oplus>i \<in> {..n}. p i \<otimes> q (n-i)) \<in> up R"
proof
  fix n
  assume "p \<in> up R" "q \<in> up R"
  then show "(\<Oplus>i \<in> {..n}. p i \<otimes> q (n-i)) \<in> carrier R"
    by (simp add: mem_upD  funcsetI)
next
  assume UP: "p \<in> up R" "q \<in> up R"
  show "EX n. bound \<zero> n (%n. \<Oplus>i \<in> {..n}. p i \<otimes> q (n-i))"
  proof -
    from UP obtain n where boundn: "bound \<zero> n p" by fast
    from UP obtain m where boundm: "bound \<zero> m q" by fast
    have "bound \<zero> (n + m) (%n. \<Oplus>i \<in> {..n}. p i \<otimes> q (n - i))"
    proof
      fix k assume bound: "n + m < k"
      {
        fix i
        have "p i \<otimes> q (k-i) = \<zero>"
        proof (cases "n < i")
          case True
          with boundn have "p i = \<zero>" by auto
          moreover from UP have "q (k-i) \<in> carrier R" by auto
          ultimately show ?thesis by simp
        next
          case False
          with bound have "m < k-i" by arith
          with boundm have "q (k-i) = \<zero>" by auto
          moreover from UP have "p i \<in> carrier R" by auto
          ultimately show ?thesis by simp
        qed
      }
      then show "(\<Oplus>i \<in> {..k}. p i \<otimes> q (k-i)) = \<zero>"
        by (simp add: Pi_def)
    qed
    then show ?thesis by fast
  qed
qed

end


subsection {* Effect of Operations on Coefficients *}

locale UP =
  fixes R (structure) and P (structure)
  defines P_def: "P == UP R"

locale UP_ring = UP + R: ring R

locale UP_cring = UP + R: cring R

sublocale UP_cring < UP_ring
  by intro_locales [1] (rule P_def)

locale UP_domain = UP + R: "domain" R

sublocale UP_domain < UP_cring
  by intro_locales [1] (rule P_def)

context UP
begin

text {*Temporarily declare @{thm P_def} as simp rule.*}

declare P_def [simp]

lemma up_eqI:
  assumes prem: "!!n. coeff P p n = coeff P q n" and R: "p \<in> carrier P" "q \<in> carrier P"
  shows "p = q"
proof
  fix x
  from prem and R show "p x = q x" by (simp add: UP_def)
qed

lemma coeff_closed [simp]:
  "p \<in> carrier P ==> coeff P p n \<in> carrier R" by (auto simp add: UP_def)

end

context UP_ring 
begin

(* Theorems generalised from commutative rings to rings by Jesus Aransay. *)

lemma coeff_monom [simp]:
  "a \<in> carrier R ==> coeff P (monom P a m) n = (if m=n then a else \<zero>)"
proof -
  assume R: "a \<in> carrier R"
  then have "(%n. if n = m then a else \<zero>) \<in> up R"
    using up_def by force
  with R show ?thesis by (simp add: UP_def)
qed

lemma coeff_zero [simp]: "coeff P \<zero>\<^bsub>P\<^esub> n = \<zero>" by (auto simp add: UP_def)

lemma coeff_one [simp]: "coeff P \<one>\<^bsub>P\<^esub> n = (if n=0 then \<one> else \<zero>)"
  using up_one_closed by (simp add: UP_def)

lemma coeff_smult [simp]:
  "[| a \<in> carrier R; p \<in> carrier P |] ==> coeff P (a \<odot>\<^bsub>P\<^esub> p) n = a \<otimes> coeff P p n"
  by (simp add: UP_def up_smult_closed)

lemma coeff_add [simp]:
  "[| p \<in> carrier P; q \<in> carrier P |] ==> coeff P (p \<oplus>\<^bsub>P\<^esub> q) n = coeff P p n \<oplus> coeff P q n"
  by (simp add: UP_def up_add_closed)

lemma coeff_mult [simp]:
  "[| p \<in> carrier P; q \<in> carrier P |] ==> coeff P (p \<otimes>\<^bsub>P\<^esub> q) n = (\<Oplus>i \<in> {..n}. coeff P p i \<otimes> coeff P q (n-i))"
  by (simp add: UP_def up_mult_closed)

end


subsection {* Polynomials Form a Ring. *}

context UP_ring
begin

text {* Operations are closed over @{term P}. *}

lemma UP_mult_closed [simp]:
  "[| p \<in> carrier P; q \<in> carrier P |] ==> p \<otimes>\<^bsub>P\<^esub> q \<in> carrier P" by (simp add: UP_def up_mult_closed)

lemma UP_one_closed [simp]:
  "\<one>\<^bsub>P\<^esub> \<in> carrier P" by (simp add: UP_def up_one_closed)

lemma UP_zero_closed [intro, simp]:
  "\<zero>\<^bsub>P\<^esub> \<in> carrier P" by (auto simp add: UP_def)

lemma UP_a_closed [intro, simp]:
  "[| p \<in> carrier P; q \<in> carrier P |] ==> p \<oplus>\<^bsub>P\<^esub> q \<in> carrier P" by (simp add: UP_def up_add_closed)

lemma monom_closed [simp]:
  "a \<in> carrier R ==> monom P a n \<in> carrier P" by (auto simp add: UP_def up_def Pi_def)

lemma UP_smult_closed [simp]:
  "[| a \<in> carrier R; p \<in> carrier P |] ==> a \<odot>\<^bsub>P\<^esub> p \<in> carrier P" by (simp add: UP_def up_smult_closed)

end

declare (in UP) P_def [simp del]

text {* Algebraic ring properties *}

context UP_ring
begin

lemma UP_a_assoc:
  assumes R: "p \<in> carrier P" "q \<in> carrier P" "r \<in> carrier P"
  shows "(p \<oplus>\<^bsub>P\<^esub> q) \<oplus>\<^bsub>P\<^esub> r = p \<oplus>\<^bsub>P\<^esub> (q \<oplus>\<^bsub>P\<^esub> r)" by (rule up_eqI, simp add: a_assoc R, simp_all add: R)

lemma UP_l_zero [simp]:
  assumes R: "p \<in> carrier P"
  shows "\<zero>\<^bsub>P\<^esub> \<oplus>\<^bsub>P\<^esub> p = p" by (rule up_eqI, simp_all add: R)

lemma UP_l_neg_ex:
  assumes R: "p \<in> carrier P"
  shows "EX q : carrier P. q \<oplus>\<^bsub>P\<^esub> p = \<zero>\<^bsub>P\<^esub>"
proof -
  let ?q = "%i. \<ominus> (p i)"
  from R have closed: "?q \<in> carrier P"
    by (simp add: UP_def P_def up_a_inv_closed)
  from R have coeff: "!!n. coeff P ?q n = \<ominus> (coeff P p n)"
    by (simp add: UP_def P_def up_a_inv_closed)
  show ?thesis
  proof
    show "?q \<oplus>\<^bsub>P\<^esub> p = \<zero>\<^bsub>P\<^esub>"
      by (auto intro!: up_eqI simp add: R closed coeff R.l_neg)
  qed (rule closed)
qed

lemma UP_a_comm:
  assumes R: "p \<in> carrier P" "q \<in> carrier P"
  shows "p \<oplus>\<^bsub>P\<^esub> q = q \<oplus>\<^bsub>P\<^esub> p" by (rule up_eqI, simp add: a_comm R, simp_all add: R)

lemma UP_m_assoc:
  assumes R: "p \<in> carrier P" "q \<in> carrier P" "r \<in> carrier P"
  shows "(p \<otimes>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> r = p \<otimes>\<^bsub>P\<^esub> (q \<otimes>\<^bsub>P\<^esub> r)"
proof (rule up_eqI)
  fix n
  {
    fix k and a b c :: "nat=>'a"
    assume R: "a \<in> UNIV -> carrier R" "b \<in> UNIV -> carrier R"
      "c \<in> UNIV -> carrier R"
    then have "k <= n ==>
      (\<Oplus>j \<in> {..k}. (\<Oplus>i \<in> {..j}. a i \<otimes> b (j-i)) \<otimes> c (n-j)) =
      (\<Oplus>j \<in> {..k}. a j \<otimes> (\<Oplus>i \<in> {..k-j}. b i \<otimes> c (n-j-i)))"
      (is "_ \<Longrightarrow> ?eq k")
    proof (induct k)
      case 0 then show ?case by (simp add: Pi_def m_assoc)
    next
      case (Suc k)
      then have "k <= n" by arith
      from this R have "?eq k" by (rule Suc)
      with R show ?case
        by (simp cong: finsum_cong
             add: Suc_diff_le Pi_def l_distr r_distr m_assoc)
           (simp cong: finsum_cong add: Pi_def a_ac finsum_ldistr m_assoc)
    qed
  }
  with R show "coeff P ((p \<otimes>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> r) n = coeff P (p \<otimes>\<^bsub>P\<^esub> (q \<otimes>\<^bsub>P\<^esub> r)) n"
    by (simp add: Pi_def)
qed (simp_all add: R)

lemma UP_r_one [simp]:
  assumes R: "p \<in> carrier P" shows "p \<otimes>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub> = p"
proof (rule up_eqI)
  fix n
  show "coeff P (p \<otimes>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) n = coeff P p n"
  proof (cases n)
    case 0 
    {
      with R show ?thesis by simp
    }
  next
    case Suc
    {
      (*JE: in the locale UP_cring the proof was solved only with "by (simp del: finsum_Suc add: finsum_Suc2 Pi_def)", but I did not get it to work here*)
      fix nn assume Succ: "n = Suc nn"
      have "coeff P (p \<otimes>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) (Suc nn) = coeff P p (Suc nn)"
      proof -
        have "coeff P (p \<otimes>\<^bsub>P\<^esub> \<one>\<^bsub>P\<^esub>) (Suc nn) = (\<Oplus>i\<in>{..Suc nn}. coeff P p i \<otimes> (if Suc nn \<le> i then \<one> else \<zero>))" using R by simp
        also have "\<dots> = coeff P p (Suc nn) \<otimes> (if Suc nn \<le> Suc nn then \<one> else \<zero>) \<oplus> (\<Oplus>i\<in>{..nn}. coeff P p i \<otimes> (if Suc nn \<le> i then \<one> else \<zero>))"
          using finsum_Suc [of "(\<lambda>i::nat. coeff P p i \<otimes> (if Suc nn \<le> i then \<one> else \<zero>))" "nn"] unfolding Pi_def using R by simp
        also have "\<dots> = coeff P p (Suc nn) \<otimes> (if Suc nn \<le> Suc nn then \<one> else \<zero>)"
        proof -
          have "(\<Oplus>i\<in>{..nn}. coeff P p i \<otimes> (if Suc nn \<le> i then \<one> else \<zero>)) = (\<Oplus>i\<in>{..nn}. \<zero>)"
            using finsum_cong [of "{..nn}" "{..nn}" "(\<lambda>i::nat. coeff P p i \<otimes> (if Suc nn \<le> i then \<one> else \<zero>))" "(\<lambda>i::nat. \<zero>)"] using R 
            unfolding Pi_def by simp
          also have "\<dots> = \<zero>" by simp
          finally show ?thesis using r_zero R by simp
        qed
        also have "\<dots> = coeff P p (Suc nn)" using R by simp
        finally show ?thesis by simp
      qed
      then show ?thesis using Succ by simp
    }
  qed
qed (simp_all add: R)
  
lemma UP_l_one [simp]:
  assumes R: "p \<in> carrier P"
  shows "\<one>\<^bsub>P\<^esub> \<otimes>\<^bsub>P\<^esub> p = p"
proof (rule up_eqI)
  fix n
  show "coeff P (\<one>\<^bsub>P\<^esub> \<otimes>\<^bsub>P\<^esub> p) n = coeff P p n"
  proof (cases n)
    case 0 with R show ?thesis by simp
  next
    case Suc with R show ?thesis
      by (simp del: finsum_Suc add: finsum_Suc2 Pi_def)
  qed
qed (simp_all add: R)

lemma UP_l_distr:
  assumes R: "p \<in> carrier P" "q \<in> carrier P" "r \<in> carrier P"
  shows "(p \<oplus>\<^bsub>P\<^esub> q) \<otimes>\<^bsub>P\<^esub> r = (p \<otimes>\<^bsub>P\<^esub> r) \<oplus>\<^bsub>P\<^esub> (q \<otimes>\<^bsub>P\<^esub> r)"
  by (rule up_eqI) (simp add: l_distr R Pi_def, simp_all add: R)

lemma UP_r_distr:
  assumes R: "p \<in> carrier P" "q \<in> carrier P" "r \<in> carrier P"
  shows "r \<otimes>\<^bsub>P\<^esub> (p \<oplus>\<^bsub>P\<^esub> q) = (r \<otimes>\<^bsub>P\<^esub> p) \<oplus>\<^bsub>P\<^esub> (r \<otimes>\<^bsub>P\<^esub> q)"
  by (rule up_eqI) (simp add: r_distr R Pi_def, simp_all add: R)

theorem UP_ring: "ring P"
  by (auto intro!: ringI abelian_groupI monoidI UP_a_assoc)
    (auto intro: UP_a_comm UP_l_neg_ex UP_m_assoc UP_l_distr UP_r_distr)

end


subsection {* Polynomials Form a Commutative Ring. *}

context UP_cring
begin

lemma UP_m_comm:
  assumes R1: "p \<in> carrier P" and R2: "q \<in> carrier P" shows "p \<otimes>\<^bsub>P\<^esub> q = q \<otimes>\<^bsub>P\<^esub> p"
proof (rule up_eqI)
  fix n
  {
    fix k and a b :: "nat=>'a"
    assume R: "a \<in> UNIV -> carrier R" "b \<in> UNIV -> carrier R"
    then have "k <= n ==>
      (\<Oplus>i \<in> {..k}. a i \<otimes> b (n-i)) = (\<Oplus>i \<in> {..k}. a (k-i) \<otimes> b (i+n-k))"
      (is "_ \<Longrightarrow> ?eq k")
    proof (induct k)
      case 0 then show ?case by (simp add: Pi_def)
    next
      case (Suc k) then show ?case
        by (subst (2) finsum_Suc2) (simp add: Pi_def a_comm)+
    qed
  }
  note l = this
  from R1 R2 show "coeff P (p \<otimes>\<^bsub>P\<^esub> q) n =  coeff P (q \<otimes>\<^bsub>P\<^esub> p) n"
    unfolding coeff_mult [OF R1 R2, of n] 
    unfolding coeff_mult [OF R2 R1, of n] 
    using l [of "(\<lambda>i. coeff P p i)" "(\<lambda>i. coeff P q i)" "n"] by (simp add: Pi_def m_comm)
qed (simp_all add: R1 R2)


subsection {*Polynomials over a commutative ring for a commutative ring*}

theorem UP_cring:
  "cring P" using UP_ring unfolding cring_def by (auto intro!: comm_monoidI UP_m_assoc UP_m_comm)

end

context UP_ring
begin

lemma UP_a_inv_closed [intro, simp]:
  "p \<in> carrier P ==> \<ominus>\<^bsub>P\<^esub> p \<in> carrier P"
  by (rule abelian_group.a_inv_closed [OF ring.is_abelian_group [OF UP_ring]])

lemma coeff_a_inv [simp]:
  assumes R: "p \<in> carrier P"
  shows "coeff P (\<ominus>\<^bsub>P\<^esub> p) n = \<ominus> (coeff P p n)"
proof -
  from R coeff_closed UP_a_inv_closed have
    "coeff P (\<ominus>\<^bsub>P\<^esub> p) n = \<ominus> coeff P p n \<oplus> (coeff P p n \<oplus> coeff P (\<ominus>\<^bsub>P\<^esub> p) n)"
    by algebra
  also from R have "... =  \<ominus> (coeff P p n)"
    by (simp del: coeff_add add: coeff_add [THEN sym]
      abelian_group.r_neg [OF ring.is_abelian_group [OF UP_ring]])
  finally show ?thesis .
qed

end

sublocale UP_ring < P: ring P using UP_ring .
sublocale UP_cring < P: cring P using UP_cring .


subsection {* Polynomials Form an Algebra *}

context UP_ring
begin

lemma UP_smult_l_distr:
  "[| a \<in> carrier R; b \<in> carrier R; p \<in> carrier P |] ==>
  (a \<oplus> b) \<odot>\<^bsub>P\<^esub> p = a \<odot>\<^bsub>P\<^esub> p \<oplus>\<^bsub>P\<^esub> b \<odot>\<^bsub>P\<^esub> p"
  by (rule up_eqI) (simp_all add: R.l_distr)

lemma UP_smult_r_distr:
  "[| a \<in> carrier R; p \<in> carrier P; q \<in> carrier P |] ==>
  a \<odot>\<^bsub>P\<^esub> (p \<oplus>\<^bsub>P\<^esub> q) = a \<odot>\<^bsub>P\<^esub> p \<oplus>\<^bsub>P\<^esub> a \<odot>\<^bsub>P\<^esub> q"
  by (rule up_eqI) (simp_all add: R.r_distr)

lemma UP_smult_assoc1:
      "[| a \<in> carrier R; b \<in> carrier R; p \<in> carrier P |] ==>
      (a \<otimes> b) \<odot>\<^bsub>P\<^esub> p = a \<odot>\<^bsub>P\<^esub> (b \<odot>\<^bsub>P\<^esub> p)"
  by (rule up_eqI) (simp_all add: R.m_assoc)

lemma UP_smult_zero [simp]:
      "p \<in> carrier P ==> \<zero> \<odot>\<^bsub>P\<^esub> p = \<zero>\<^bsub>P\<^esub>"
  by (rule up_eqI) simp_all

lemma UP_smult_one [simp]:
      "p \<in> carrier P ==> \<one> \<odot>\<^bsub>P\<^esub> p = p"
  by (rule up_eqI) simp_all

lemma UP_smult_assoc2:
  "[| a \<in> carrier R; p \<in> carrier P; q \<in> carrier P |] ==>
  (a \<odot>\<^bsub>P\<^esub> p) \<otimes>\<^bsub>P\<^esub> q = a \<odot>\<^bsub>P\<^esub> (p \<otimes>\<^bsub>P\<^esub> q)"
  by (rule up_eqI) (simp_all add: R.finsum_rdistr R.m_assoc Pi_def)

end

text {*
  Interpretation of lemmas from @{term algebra}.
*}

lemma (in cring) cring:
  "cring R" ..

lemma (in UP_cring) UP_algebra:
  "algebra R P" by (auto intro!: algebraI R.cring UP_cring UP_smult_l_distr UP_smult_r_distr
    UP_smult_assoc1 UP_smult_assoc2)

sublocale UP_cring < algebra R P using UP_algebra .


subsection {* Further Lemmas Involving Monomials *}

context UP_ring
begin

lemma monom_zero [simp]:
  "monom P \<zero> n = \<zero>\<^bsub>P\<^esub>" by (simp add: UP_def P_def)

lemma monom_mult_is_smult:
  assumes R: "a \<in> carrier R" "p \<in> carrier P"
  shows "monom P a 0 \<otimes>\<^bsub>P\<^esub> p = a \<odot>\<^bsub>P\<^esub> p"
proof (rule up_eqI)
  fix n
  show "coeff P (monom P a 0 \<otimes>\<^bsub>P\<^esub> p) n = coeff P (a \<odot>\<^bsub>P\<^esub> p) n"
  proof (cases n)
    case 0 with R show ?thesis by simp
  next
    case Suc with R show ?thesis
      using R.finsum_Suc2 by (simp del: R.finsum_Suc add: R.r_null Pi_def)
  qed
qed (simp_all add: R)

lemma monom_one [simp]:
  "monom P \<one> 0 = \<one>\<^bsub>P\<^esub>"
  by (rule up_eqI) simp_all

lemma monom_add [simp]:
  "[| a \<in> carrier R; b \<in> carrier R |] ==>
  monom P (a \<oplus> b) n = monom P a n \<oplus>\<^bsub>P\<^esub> monom P b n"
  by (rule up_eqI) simp_all

lemma monom_one_Suc:
  "monom P \<one> (Suc n) = monom P \<one> n \<otimes>\<^bsub>P\<^esub> monom P \<one> 1"
proof (rule up_eqI)
  fix k
  show "coeff P (monom P \<one> (Suc n)) k = coeff P (monom P \<one> n \<otimes>\<^bsub>P\<^esub> monom P \<one> 1) k"
  proof (cases "k = Suc n")
    case True show ?thesis
    proof -
      fix m
      from True have less_add_diff:
        "!!i. [| n < i; i <= n + m |] ==> n + m - i < m" by arith
      from True have "coeff P (monom P \<one> (Suc n)) k = \<one>" by simp
      also from True
      have "... = (\<Oplus>i \<in> {..<n} \<union> {n}. coeff P (monom P \<one> n) i \<otimes>
        coeff P (monom P \<one> 1) (k - i))"
        by (simp cong: R.finsum_cong add: Pi_def)
      also have "... = (\<Oplus>i \<in>  {..n}. coeff P (monom P \<one> n) i \<otimes>
        coeff P (monom P \<one> 1) (k - i))"
        by (simp only: ivl_disj_un_singleton)
      also from True
      have "... = (\<Oplus>i \<in> {..n} \<union> {n<..k}. coeff P (monom P \<one> n) i \<otimes>
        coeff P (monom P \<one> 1) (k - i))"
        by (simp cong: R.finsum_cong add: R.finsum_Un_disjoint ivl_disj_int_one
          order_less_imp_not_eq Pi_def)
      also from True have "... = coeff P (monom P \<one> n \<otimes>\<^bsub>P\<^esub> monom P \<one> 1) k"
        by (simp add: ivl_disj_un_one)
      finally show ?thesis .
    qed
  next
    case False
    note neq = False
    let ?s =
      "\<lambda>i. (if n = i then \<one> else \<zero>) \<otimes> (if Suc 0 = k - i then \<one> else \<zero>)"
    from neq have "coeff P (monom P \<one> (Suc n)) k = \<zero>" by simp
    also have "... = (\<Oplus>i \<in> {..k}. ?s i)"
    proof -
      have f1: "(\<Oplus>i \<in> {..<n}. ?s i) = \<zero>"
        by (simp cong: R.finsum_cong add: Pi_def)
      from neq have f2: "(\<Oplus>i \<in> {n}. ?s i) = \<zero>"
        by (simp cong: R.finsum_cong add: Pi_def) arith
      have f3: "n < k ==> (\<Oplus>i \<in> {n<..k}. ?s i) = \<zero>"
        by (simp cong: R.finsum_cong add: order_less_imp_not_eq Pi_def)
      show ?thesis
      proof (cases "k < n")
        case True then show ?thesis by (simp cong: R.finsum_cong add: Pi_def)
      next
        case False then have n_le_k: "n <= k" by arith
        show ?thesis
        proof (cases "n = k")
          case True
          then have "\<zero> = (\<Oplus>i \<in> {..<n} \<union> {n}. ?s i)"
            by (simp cong: R.finsum_cong add: Pi_def)
          also from True have "... = (\<Oplus>i \<in> {..k}. ?s i)"
            by (simp only: ivl_disj_un_singleton)
          finally show ?thesis .
        next
          case False with n_le_k have n_less_k: "n < k" by arith
          with neq have "\<zero> = (\<Oplus>i \<in> {..<n} \<union> {n}. ?s i)"
            by (simp add: R.finsum_Un_disjoint f1 f2 Pi_def del: Un_insert_right)
          also have "... = (\<Oplus>i \<in> {..n}. ?s i)"
            by (simp only: ivl_disj_un_singleton)
          also from n_less_k neq have "... = (\<Oplus>i \<in> {..n} \<union> {n<..k}. ?s i)"
            by (simp add: R.finsum_Un_disjoint f3 ivl_disj_int_one Pi_def)
          also from n_less_k have "... = (\<Oplus>i \<in> {..k}. ?s i)"
            by (simp only: ivl_disj_un_one)
          finally show ?thesis .
        qed
      qed
    qed
    also have "... = coeff P (monom P \<one> n \<otimes>\<^bsub>P\<^esub> monom P \<one> 1) k" by simp
    finally show ?thesis .
  qed
qed (simp_all)

lemma monom_one_Suc2:
  "monom P \<one> (Suc n) = monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> monom P \<one> n"
proof (induct n)
  case 0 show ?case by simp
next
  case Suc
  {
    fix k:: nat
    assume hypo: "monom P \<one> (Suc k) = monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> monom P \<one> k"
    then show "monom P \<one> (Suc (Suc k)) = monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> monom P \<one> (Suc k)"
    proof -
      have lhs: "monom P \<one> (Suc (Suc k)) = monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> monom P \<one> k \<otimes>\<^bsub>P\<^esub> monom P \<one> 1"
        unfolding monom_one_Suc [of "Suc k"] unfolding hypo ..
      note cl = monom_closed [OF R.one_closed, of 1]
      note clk = monom_closed [OF R.one_closed, of k]
      have rhs: "monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> monom P \<one> (Suc k) = monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> monom P \<one> k \<otimes>\<^bsub>P\<^esub> monom P \<one> 1"
        unfolding monom_one_Suc [of k] unfolding sym [OF m_assoc  [OF cl clk cl]] ..
      from lhs rhs show ?thesis by simp
    qed
  }
qed

text{*The following corollary follows from lemmas @{thm "monom_one_Suc"} 
  and @{thm "monom_one_Suc2"}, and is trivial in @{term UP_cring}*}

corollary monom_one_comm: shows "monom P \<one> k \<otimes>\<^bsub>P\<^esub> monom P \<one> 1 = monom P \<one> 1 \<otimes>\<^bsub>P\<^esub> monom P \<one> k"
  unfolding monom_one_Suc [symmetric] monom_one_Suc2 [symmetric] ..

lemma monom_mult_smult:
  "[| a \<in> carrier R; b \<in> carrier R |] ==> monom P (a \<otimes> b) n = a \<odot>\<^bsub>P\<^esub> monom P b n"
  by (rule up_eqI) simp_all

lemma monom_one_mult:
  "monom P \<one> (n + m) = monom P \<one> n \<otimes>\<^bsub>P\<^esub> monom P \<one> m"
proof (induct n)
  case 0 show ?case by simp
next
  case Suc then show ?case
    unfolding add_Suc unfolding monom_one_Suc unfolding Suc.hyps
    using m_assoc monom_one_comm [of m] by simp
qed

lemma monom_one_mult_comm: "monom P \<one> n \<otimes>\<^bsub>P\<^esub> monom P \<one> m = monom P \<one> m \<otimes>\<^bsub>P\<^esub> monom P \<one> n"
  unfolding monom_one_mult [symmetric] by (rule up_eqI) simp_all

lemma monom_mult [simp]:
  assumes a_in_R: "a \<in> carrier R" and b_in_R: "b \<in> carrier R"
  shows "monom P (a \<otimes> b) (n + m) = monom P a n \<otimes>\<^bsub>P\<^esub> monom P b m"
proof (rule up_eqI)
  fix k 
  show "coeff P (monom P (a \<otimes> b) (n + m)) k = coeff P (monom P a n \<otimes>\<^bsub>P\<^esub> monom P b m) k"
  proof (cases "n + m = k")
    case True 
    {
      show ?thesis
        unfolding True [symmetric]
          coeff_mult [OF monom_closed [OF a_in_R, of n] monom_closed [OF b_in_R, of m], of "n + m"] 
          coeff_monom [OF a_in_R, of n] coeff_monom [OF b_in_R, of m]
        using R.finsum_cong [of "{.. n + m}" "{.. n + m}" "(\<lambda>i. (if n = i then a else \<zero>) \<otimes> (if m = n + m - i then b else \<zero>))" 
          "(\<lambda>i. if n = i then a \<otimes> b else \<zero>)"]
          a_in_R b_in_R
        unfolding simp_implies_def
        using R.finsum_singleton [of n "{.. n + m}" "(\<lambda>i. a \<otimes> b)"]
        unfolding Pi_def by auto
    }
  next
    case False
    {
      show ?thesis
        unfolding coeff_monom [OF R.m_closed [OF a_in_R b_in_R], of "n + m" k] apply (simp add: False)
        unfolding coeff_mult [OF monom_closed [OF a_in_R, of n] monom_closed [OF b_in_R, of m], of k]
        unfolding coeff_monom [OF a_in_R, of n] unfolding coeff_monom [OF b_in_R, of m] using False
        using R.finsum_cong [of "{..k}" "{..k}" "(\<lambda>i. (if n = i then a else \<zero>) \<otimes> (if m = k - i then b else \<zero>))" "(\<lambda>i. \<zero>)"]
        unfolding Pi_def simp_implies_def using a_in_R b_in_R by force
    }
  qed
qed (simp_all add: a_in_R b_in_R)

lemma monom_a_inv [simp]:
  "a \<in> carrier R ==> monom P (\<ominus> a) n = \<ominus>\<^bsub>P\<^esub> monom P a n"
  by (rule up_eqI) simp_all

lemma monom_inj:
  "inj_on (%a. monom P a n) (carrier R)"
proof (rule inj_onI)
  fix x y
  assume R: "x \<in> carrier R" "y \<in> carrier R" and eq: "monom P x n = monom P y n"
  then have "coeff P (monom P x n) n = coeff P (monom P y n) n" by simp
  with R show "x = y" by simp
qed

end


subsection {* The Degree Function *}

definition
  deg :: "[('a, 'm) ring_scheme, nat => 'a] => nat"
  where "deg R p = (LEAST n. bound \<zero>\<^bsub>R\<^esub> n (coeff (UP R) p))"

context UP_ring
begin

lemma deg_aboveI:
  "[| (!!m. n < m ==> coeff P p m = \<zero>); p \<in> carrier P |] ==> deg R p <= n"
  by (unfold deg_def P_def) (fast intro: Least_le)

(*
lemma coeff_bound_ex: "EX n. bound n (coeff p)"
proof -
  have "(%n. coeff p n) : UP" by (simp add: coeff_def Rep_UP)
  then obtain n where "bound n (coeff p)" by (unfold UP_def) fast
  then show ?thesis ..
qed

lemma bound_coeff_obtain:
  assumes prem: "(!!n. bound n (coeff p) ==> P)" shows "P"
proof -
  have "(%n. coeff p n) : UP" by (simp add: coeff_def Rep_UP)
  then obtain n where "bound n (coeff p)" by (unfold UP_def) fast
  with prem show P .
qed
*)

lemma deg_aboveD:
  assumes "deg R p < m" and "p \<in> carrier P"
  shows "coeff P p m = \<zero>"
proof -
  from `p \<in> carrier P` obtain n where "bound \<zero> n (coeff P p)"
    by (auto simp add: UP_def P_def)
  then have "bound \<zero> (deg R p) (coeff P p)"
    by (auto simp: deg_def P_def dest: LeastI)
  from this and `deg R p < m` show ?thesis ..
qed

lemma deg_belowI:
  assumes non_zero: "n ~= 0 ==> coeff P p n ~= \<zero>"
    and R: "p \<in> carrier P"
  shows "n <= deg R p"
-- {* Logically, this is a slightly stronger version of
   @{thm [source] deg_aboveD} *}
proof (cases "n=0")
  case True then show ?thesis by simp
next
  case False then have "coeff P p n ~= \<zero>" by (rule non_zero)
  then have "~ deg R p < n" by (fast dest: deg_aboveD intro: R)
  then show ?thesis by arith
qed

lemma lcoeff_nonzero_deg:
  assumes deg: "deg R p ~= 0" and R: "p \<in> carrier P"
  shows "coeff P p (deg R p) ~= \<zero>"
proof -
  from R obtain m where "deg R p <= m" and m_coeff: "coeff P p m ~= \<zero>"
  proof -
    have minus: "!!(n::nat) m. n ~= 0 ==> (n - Suc 0 < m) = (n <= m)"
      by arith
    from deg have "deg R p - 1 < (LEAST n. bound \<zero> n (coeff P p))"
      by (unfold deg_def P_def) simp
    then have "~ bound \<zero> (deg R p - 1) (coeff P p)" by (rule not_less_Least)
    then have "EX m. deg R p - 1 < m & coeff P p m ~= \<zero>"
      by (unfold bound_def) fast
    then have "EX m. deg R p <= m & coeff P p m ~= \<zero>" by (simp add: deg minus)
    then show ?thesis by (auto intro: that)
  qed
  with deg_belowI R have "deg R p = m" by fastforce
  with m_coeff show ?thesis by simp
qed

lemma lcoeff_nonzero_nonzero:
  assumes deg: "deg R p = 0" and nonzero: "p ~= \<zero>\<^bsub>P\<^esub>" and R: "p \<in> carrier P"
  shows "coeff P p 0 ~= \<zero>"
proof -
  have "EX m. coeff P p m ~= \<zero>"
  proof (rule classical)
    assume "~ ?thesis"
    with R have "p = \<zero>\<^bsub>P\<^esub>" by (auto intro: up_eqI)
    with nonzero show ?thesis by contradiction
  qed
  then obtain m where coeff: "coeff P p m ~= \<zero>" ..
  from this and R have "m <= deg R p" by (rule deg_belowI)
  then have "m = 0" by (simp add: deg)
  with coeff show ?thesis by simp
qed

lemma lcoeff_nonzero:
  assumes neq: "p ~= \<zero>\<^bsub>P\<^esub>" and R: "p \<in> carrier P"
  shows "coeff P p (deg R p) ~= \<zero>"
proof (cases "deg R p = 0")
  case True with neq R show ?thesis by (simp add: lcoeff_nonzero_nonzero)
next
  case False with neq R show ?thesis by (simp add: lcoeff_nonzero_deg)
qed

lemma deg_eqI:
  "[| !!m. n < m ==> coeff P p m = \<zero>;
      !!n. n ~= 0 ==> coeff P p n ~= \<zero>; p \<in> carrier P |] ==> deg R p = n"
by (fast intro: le_antisym deg_aboveI deg_belowI)

text {* Degree and polynomial operations *}

lemma deg_add [simp]:
  "p \<in> carrier P \<Longrightarrow> q \<in> carrier P \<Longrightarrow>
  deg R (p \<oplus>\<^bsub>P\<^esub> q) <= max (deg R p) (deg R q)"
by(rule deg_aboveI)(simp_all add: deg_aboveD)

lemma deg_monom_le:
  "a \<in> carrier R ==> deg R (monom P a n) <= n"
  by (intro deg_aboveI) simp_all

lemma deg_monom [simp]:
  "[| a ~= \<zero>; a \<in> carrier R |] ==> deg R (monom P a n) = n"
  by (fastforce intro: le_antisym deg_aboveI deg_belowI)

lemma deg_const [simp]:
  assumes R: "a \<in> carrier R" shows "deg R (monom P a 0) = 0"
proof (rule le_antisym)
  show "deg R (monom P a 0) <= 0" by (rule deg_aboveI) (simp_all add: R)
next
  show "0 <= deg R (monom P a 0)" by (rule deg_belowI) (simp_all add: R)
qed

lemma deg_zero [simp]:
  "deg R \<zero>\<^bsub>P\<^esub> = 0"
proof (rule le_antisym)
  show "deg R \<zero>\<^bsub>P\<^esub> <= 0" by (rule deg_aboveI) simp_all
next
  show "0 <= deg R \<zero>\<^bsub>P\<^esub>" by (rule deg_belowI) simp_all
qed

lemma deg_one [simp]:
  "deg R \<one>\<^bsub>P\<^esub> = 0"
proof (rule le_antisym)
  show "deg R \<one>\<^bsub>P\<^esub> <= 0" by (rule deg_aboveI) simp_all
next
  show "0 <= deg R \<one>\<^bsub>P\<^esub>" by (rule deg_belowI) simp_all
qed

lemma deg_uminus [simp]:
  assumes R: "p \<in> carrier P" shows "deg R (\<ominus>\<^bsub>P\<^esub> p) = deg R p"
proof (rule le_antisym)
  show "deg R (\<ominus>\<^bsub>P\<^esub> p) <= deg R p" by (simp add: deg_aboveI deg_aboveD R)
next
  show "deg R p <= deg R (\<ominus>\<^bsub>P\<^esub> p)"
    by (simp add: deg_belowI lcoeff_nonzero_deg
      inj_on_iff [OF R.a_inv_inj, of _ "\<zero>", simplified] R)
qed

text{*The following lemma is later \emph{overwritten} by the most
  specific one for domains, @{text deg_smult}.*}

lemma deg_smult_ring [simp]:
  "[| a \<in> carrier R; p \<in> carrier P |] ==>
  deg R (a \<odot>\<^bsub>P\<^esub> p) <= (if a = \<zero> then 0 else deg R p)"
  by (cases "a = \<zero>") (simp add: deg_aboveI deg_aboveD)+

end

context UP_domain
begin

lemma deg_smult [simp]:
  assumes R: "a \<in> carrier R" "p \<in> carrier P"
  shows "deg R (a \<odot>\<^bsub>P\<^esub> p) = (if a = \<zero> then 0 else deg R p)"
proof (rule le_antisym)
  show "deg R (a \<odot>\<^bsub>P\<^esub> p) <= (if a = \<zero> then 0 else deg R p)"
    using R by (rule deg_smult_ring)
next
  show "(if a = \<zero> then 0 else deg R p) <= deg R (a \<odot>\<^bsub>P\<^esub> p)"
  proof (cases "a = \<zero>")
  qed (simp, simp add: deg_belowI lcoeff_nonzero_deg integral_iff R)
qed

end

context UP_ring
begin

lemma deg_mult_ring:
  assumes R: "p \<in> carrier P" "q \<in> carrier P"
  shows "deg R (p \<otimes>\<^bsub>P\<^esub> q) <= deg R p + deg R q"
proof (rule deg_aboveI)
  fix m
  assume boundm: "deg R p + deg R q < m"
  {
    fix k i
    assume boundk: "deg R p + deg R q < k"
    then have "coeff P p i \<otimes> coeff P q (k - i) = \<zero>"
    proof (cases "deg R p < i")
      case True then show ?thesis by (simp add: deg_aboveD R)
    next
      case False with boundk have "deg R q < k - i" by arith
      then show ?thesis by (simp add: deg_aboveD R)
    qed
  }
  with boundm R show "coeff P (p \<otimes>\<^bsub>P\<^esub> q) m = \<zero>" by simp
qed (simp add: R)

end

context UP_domain
begin

lemma deg_mult [simp]:
  "[| p ~= \<zero>\<^bsub>P\<^esub>; q ~= \<zero>\<^bsub>P\<^esub>; p \<in> carrier P; q \<in> carrier P |] ==>
  deg R (p \<otimes>\<^bsub>P\<^esub> q) = deg R p + deg R q"
proof (rule le_antisym)
  assume "p \<in> carrier P" " q \<in> carrier P"
  then show "deg R (p \<otimes>\<^bsub>P\<^esub> q) <= deg R p + deg R q" by (rule deg_mult_ring)
next
  let ?s = "(%i. coeff P p i \<otimes> coeff P q (deg R p + deg R q - i))"
  assume R: "p \<in> carrier P" "q \<in> carrier P" and nz: "p ~= \<zero>\<^bsub>P\<^esub>" "q ~= \<zero>\<^bsub>P\<^esub>"
  have less_add_diff: "!!(k::nat) n m. k < n ==> m < n + m - k" by arith
  show "deg R p + deg R q <= deg R (p \<otimes>\<^bsub>P\<^esub> q)"
  proof (rule deg_belowI, simp add: R)
    have "(\<Oplus>i \<in> {.. deg R p + deg R q}. ?s i)
      = (\<Oplus>i \<in> {..< deg R p} \<union> {deg R p .. deg R p + deg R q}. ?s i)"
      by (simp only: ivl_disj_un_one)
    also have "... = (\<Oplus>i \<in> {deg R p .. deg R p + deg R q}. ?s i)"
      by (simp cong: R.finsum_cong add: R.finsum_Un_disjoint ivl_disj_int_one
        deg_aboveD less_add_diff R Pi_def)
    also have "...= (\<Oplus>i \<in> {deg R p} \<union> {deg R p <.. deg R p + deg R q}. ?s i)"
      by (simp only: ivl_disj_un_singleton)
    also have "... = coeff P p (deg R p) \<otimes> coeff P q (deg R q)"
      by (simp cong: R.finsum_cong add: deg_aboveD R Pi_def)
    finally have "(\<Oplus>i \<in> {.. deg R p + deg R q}. ?s i)
      = coeff P p (deg R p) \<otimes> coeff P q (deg R q)" .
    with nz show "(\<Oplus>i \<in> {.. deg R p + deg R q}. ?s i) ~= \<zero>"
      by (simp add: integral_iff lcoeff_nonzero R)
  qed (simp add: R)
qed

end

text{*The following lemmas also can be lifted to @{term UP_ring}.*}

context UP_ring
begin

lemma coeff_finsum:
  assumes fin: "finite A"
  shows "p \<in> A -> carrier P ==>
    coeff P (finsum P p A) k = (\<Oplus>i \<in> A. coeff P (p i) k)"
  using fin by induct (auto simp: Pi_def)

lemma up_repr:
  assumes R: "p \<in> carrier P"
  shows "(\<Oplus>\<^bsub>P\<^esub> i \<in> {..deg R p}. monom P (coeff P p i) i) = p"
proof (rule up_eqI)
  let ?s = "(%i. monom P (coeff P p i) i)"
  fix k
  from R have RR: "!!i. (if i = k then coeff P p i else \<zero>) \<in> carrier R"
    by simp
  show "coeff P (\<Oplus>\<^bsub>P\<^esub> i \<in> {..deg R p}. ?s i) k = coeff P p k"
  proof (cases "k <= deg R p")
    case True
    hence "coeff P (\<Oplus>\<^bsub>P\<^esub> i \<in> {..deg R p}. ?s i) k =
          coeff P (\<Oplus>\<^bsub>P\<^esub> i \<in> {..k} \<union> {k<..deg R p}. ?s i) k"
      by (simp only: ivl_disj_un_one)
    also from True
    have "... = coeff P (\<Oplus>\<^bsub>P\<^esub> i \<in> {..k}. ?s i) k"
      by (simp cong: R.finsum_cong add: R.finsum_Un_disjoint
        ivl_disj_int_one order_less_imp_not_eq2 coeff_finsum R RR Pi_def)
    also
    have "... = coeff P (\<Oplus>\<^bsub>P\<^esub> i \<in> {..<k} \<union> {k}. ?s i) k"
      by (simp only: ivl_disj_un_singleton)
    also have "... = coeff P p k"
      by (simp cong: R.finsum_cong add: coeff_finsum deg_aboveD R RR Pi_def)
    finally show ?thesis .
  next
    case False
    hence "coeff P (\<Oplus>\<^bsub>P\<^esub> i \<in> {..deg R p}. ?s i) k =
          coeff P (\<Oplus>\<^bsub>P\<^esub> i \<in> {..<deg R p} \<union> {deg R p}. ?s i) k"
      by (simp only: ivl_disj_un_singleton)
    also from False have "... = coeff P p k"
      by (simp cong: R.finsum_cong add: coeff_finsum deg_aboveD R Pi_def)
    finally show ?thesis .
  qed
qed (simp_all add: R Pi_def)

lemma up_repr_le:
  "[| deg R p <= n; p \<in> carrier P |] ==>
  (\<Oplus>\<^bsub>P\<^esub> i \<in> {..n}. monom P (coeff P p i) i) = p"
proof -
  let ?s = "(%i. monom P (coeff P p i) i)"
  assume R: "p \<in> carrier P" and "deg R p <= n"
  then have "finsum P ?s {..n} = finsum P ?s ({..deg R p} \<union> {deg R p<..n})"
    by (simp only: ivl_disj_un_one)
  also have "... = finsum P ?s {..deg R p}"
    by (simp cong: P.finsum_cong add: P.finsum_Un_disjoint ivl_disj_int_one
      deg_aboveD R Pi_def)
  also have "... = p" using R by (rule up_repr)
  finally show ?thesis .
qed

end


subsection {* Polynomials over Integral Domains *}

lemma domainI:
  assumes cring: "cring R"
    and one_not_zero: "one R ~= zero R"
    and integral: "!!a b. [| mult R a b = zero R; a \<in> carrier R;
      b \<in> carrier R |] ==> a = zero R | b = zero R"
  shows "domain R"
  by (auto intro!: domain.intro domain_axioms.intro cring.axioms assms
    del: disjCI)

context UP_domain
begin

lemma UP_one_not_zero:
  "\<one>\<^bsub>P\<^esub> ~= \<zero>\<^bsub>P\<^esub>"
proof
  assume "\<one>\<^bsub>P\<^esub> = \<zero>\<^bsub>P\<^esub>"
  hence "coeff P \<one>\<^bsub>P\<^esub> 0 = (coeff P \<zero>\<^bsub>P\<^esub> 0)" by simp
  hence "\<one> = \<zero>" by simp
  with R.one_not_zero show "False" by contradiction
qed

lemma UP_integral:
  "[| p \<otimes>\<^bsub>P\<^esub> q = \<zero>\<^bsub>P\<^esub>; p \<in> carrier P; q \<in> carrier P |] ==> p = \<zero>\<^bsub>P\<^esub> | q = \<zero>\<^bsub>P\<^esub>"
proof -
  fix p q
  assume pq: "p \<otimes>\<^bsub>P\<^esub> q = \<zero>\<^bsub>P\<^esub>" and R: "p \<in> carrier P" "q \<in> carrier P"
  show "p = \<zero>\<^bsub>P\<^esub> | q = \<zero>\<^bsub>P\<^esub>"
  proof (rule classical)
    assume c: "~ (p = \<zero>\<^bsub>P\<^esub> | q = \<zero>\<^bsub>P\<^esub>)"
    with R have "deg R p + deg R q = deg R (p \<otimes>\<^bsub>P\<^esub> q)" by simp
    also from pq have "... = 0" by simp
    finally have "deg R p + deg R q = 0" .
    then have f1: "deg R p = 0 & deg R q = 0" by simp
    from f1 R have "p = (\<Oplus>\<^bsub>P\<^esub> i \<in> {..0}. monom P (coeff P p i) i)"
      by (simp only: up_repr_le)
    also from R have "... = monom P (coeff P p 0) 0" by simp
    finally have p: "p = monom P (coeff P p 0) 0" .
    from f1 R have "q = (\<Oplus>\<^bsub>P\<^esub> i \<in> {..0}. monom P (coeff P q i) i)"
      by (simp only: up_repr_le)
    also from R have "... = monom P (coeff P q 0) 0" by simp
    finally have q: "q = monom P (coeff P q 0) 0" .
    from R have "coeff P p 0 \<otimes> coeff P q 0 = coeff P (p \<otimes>\<^bsub>P\<^esub> q) 0" by simp
    also from pq have "... = \<zero>" by simp
    finally have "coeff P p 0 \<otimes> coeff P q 0 = \<zero>" .
    with R have "coeff P p 0 = \<zero> | coeff P q 0 = \<zero>"
      by (simp add: R.integral_iff)
    with p q show "p = \<zero>\<^bsub>P\<^esub> | q = \<zero>\<^bsub>P\<^esub>" by fastforce
  qed
qed

theorem UP_domain:
  "domain P"
  by (auto intro!: domainI UP_cring UP_one_not_zero UP_integral del: disjCI)

end

text {*
  Interpretation of theorems from @{term domain}.
*}

sublocale UP_domain < "domain" P
  by intro_locales (rule domain.axioms UP_domain)+


subsection {* The Evaluation Homomorphism and Universal Property*}

(* alternative congruence rule (possibly more efficient)
lemma (in abelian_monoid) finsum_cong2:
  "[| !!i. i \<in> A ==> f i \<in> carrier G = True; A = B;
  !!i. i \<in> B ==> f i = g i |] ==> finsum G f A = finsum G g B"
  sorry*)

lemma (in abelian_monoid) boundD_carrier:
  "[| bound \<zero> n f; n < m |] ==> f m \<in> carrier G"
  by auto

context ring
begin

theorem diagonal_sum:
  "[| f \<in> {..n + m::nat} -> carrier R; g \<in> {..n + m} -> carrier R |] ==>
  (\<Oplus>k \<in> {..n + m}. \<Oplus>i \<in> {..k}. f i \<otimes> g (k - i)) =
  (\<Oplus>k \<in> {..n + m}. \<Oplus>i \<in> {..n + m - k}. f k \<otimes> g i)"
proof -
  assume Rf: "f \<in> {..n + m} -> carrier R" and Rg: "g \<in> {..n + m} -> carrier R"
  {
    fix j
    have "j <= n + m ==>
      (\<Oplus>k \<in> {..j}. \<Oplus>i \<in> {..k}. f i \<otimes> g (k - i)) =
      (\<Oplus>k \<in> {..j}. \<Oplus>i \<in> {..j - k}. f k \<otimes> g i)"
    proof (induct j)
      case 0 from Rf Rg show ?case by (simp add: Pi_def)
    next
      case (Suc j)
      have R6: "!!i k. [| k <= j; i <= Suc j - k |] ==> g i \<in> carrier R"
        using Suc by (auto intro!: funcset_mem [OF Rg])
      have R8: "!!i k. [| k <= Suc j; i <= k |] ==> g (k - i) \<in> carrier R"
        using Suc by (auto intro!: funcset_mem [OF Rg])
      have R9: "!!i k. [| k <= Suc j |] ==> f k \<in> carrier R"
        using Suc by (auto intro!: funcset_mem [OF Rf])
      have R10: "!!i k. [| k <= Suc j; i <= Suc j - k |] ==> g i \<in> carrier R"
        using Suc by (auto intro!: funcset_mem [OF Rg])
      have R11: "g 0 \<in> carrier R"
        using Suc by (auto intro!: funcset_mem [OF Rg])
      from Suc show ?case
        by (simp cong: finsum_cong add: Suc_diff_le a_ac
          Pi_def R6 R8 R9 R10 R11)
    qed
  }
  then show ?thesis by fast
qed

theorem cauchy_product:
  assumes bf: "bound \<zero> n f" and bg: "bound \<zero> m g"
    and Rf: "f \<in> {..n} -> carrier R" and Rg: "g \<in> {..m} -> carrier R"
  shows "(\<Oplus>k \<in> {..n + m}. \<Oplus>i \<in> {..k}. f i \<otimes> g (k - i)) =
    (\<Oplus>i \<in> {..n}. f i) \<otimes> (\<Oplus>i \<in> {..m}. g i)"      (* State reverse direction? *)
proof -
  have f: "!!x. f x \<in> carrier R"
  proof -
    fix x
    show "f x \<in> carrier R"
      using Rf bf boundD_carrier by (cases "x <= n") (auto simp: Pi_def)
  qed
  have g: "!!x. g x \<in> carrier R"
  proof -
    fix x
    show "g x \<in> carrier R"
      using Rg bg boundD_carrier by (cases "x <= m") (auto simp: Pi_def)
  qed
  from f g have "(\<Oplus>k \<in> {..n + m}. \<Oplus>i \<in> {..k}. f i \<otimes> g (k - i)) =
      (\<Oplus>k \<in> {..n + m}. \<Oplus>i \<in> {..n + m - k}. f k \<otimes> g i)"
    by (simp add: diagonal_sum Pi_def)
  also have "... = (\<Oplus>k \<in> {..n} \<union> {n<..n + m}. \<Oplus>i \<in> {..n + m - k}. f k \<otimes> g i)"
    by (simp only: ivl_disj_un_one)
  also from f g have "... = (\<Oplus>k \<in> {..n}. \<Oplus>i \<in> {..n + m - k}. f k \<otimes> g i)"
    by (simp cong: finsum_cong
      add: bound.bound [OF bf] finsum_Un_disjoint ivl_disj_int_one Pi_def)
  also from f g
  have "... = (\<Oplus>k \<in> {..n}. \<Oplus>i \<in> {..m} \<union> {m<..n + m - k}. f k \<otimes> g i)"
    by (simp cong: finsum_cong add: ivl_disj_un_one le_add_diff Pi_def)
  also from f g have "... = (\<Oplus>k \<in> {..n}. \<Oplus>i \<in> {..m}. f k \<otimes> g i)"
    by (simp cong: finsum_cong
      add: bound.bound [OF bg] finsum_Un_disjoint ivl_disj_int_one Pi_def)
  also from f g have "... = (\<Oplus>i \<in> {..n}. f i) \<otimes> (\<Oplus>i \<in> {..m}. g i)"
    by (simp add: finsum_ldistr diagonal_sum Pi_def,
      simp cong: finsum_cong add: finsum_rdistr Pi_def)
  finally show ?thesis .
qed

end

lemma (in UP_ring) const_ring_hom:
  "(%a. monom P a 0) \<in> ring_hom R P"
  by (auto intro!: ring_hom_memI intro: up_eqI simp: monom_mult_is_smult)

definition
  eval :: "[('a, 'm) ring_scheme, ('b, 'n) ring_scheme,
           'a => 'b, 'b, nat => 'a] => 'b"
  where "eval R S phi s = (\<lambda>p \<in> carrier (UP R).
    \<Oplus>\<^bsub>S\<^esub>i \<in> {..deg R p}. phi (coeff (UP R) p i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"

context UP
begin

lemma eval_on_carrier:
  fixes S (structure)
  shows "p \<in> carrier P ==>
  eval R S phi s p = (\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R p}. phi (coeff P p i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
  by (unfold eval_def, fold P_def) simp

lemma eval_extensional:
  "eval R S phi p \<in> extensional (carrier P)"
  by (unfold eval_def, fold P_def) simp

end

text {* The universal property of the polynomial ring *}

locale UP_pre_univ_prop = ring_hom_cring + UP_cring

(* FIXME print_locale ring_hom_cring fails *)

locale UP_univ_prop = UP_pre_univ_prop +
  fixes s and Eval
  assumes indet_img_carrier [simp, intro]: "s \<in> carrier S"
  defines Eval_def: "Eval == eval R S h s"

text{*JE: I have moved the following lemma from Ring.thy and lifted then to the locale @{term ring_hom_ring} from @{term ring_hom_cring}.*}
text{*JE: I was considering using it in @{text eval_ring_hom}, but that property does not hold for non commutative rings, so 
  maybe it is not that necessary.*}

lemma (in ring_hom_ring) hom_finsum [simp]:
  "[| finite A; f \<in> A -> carrier R |] ==>
  h (finsum R f A) = finsum S (h o f) A"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case insert then show ?case by (simp add: Pi_def)
qed

context UP_pre_univ_prop
begin

theorem eval_ring_hom:
  assumes S: "s \<in> carrier S"
  shows "eval R S h s \<in> ring_hom P S"
proof (rule ring_hom_memI)
  fix p
  assume R: "p \<in> carrier P"
  then show "eval R S h s p \<in> carrier S"
    by (simp only: eval_on_carrier) (simp add: S Pi_def)
next
  fix p q
  assume R: "p \<in> carrier P" "q \<in> carrier P"
  then show "eval R S h s (p \<oplus>\<^bsub>P\<^esub> q) = eval R S h s p \<oplus>\<^bsub>S\<^esub> eval R S h s q"
  proof (simp only: eval_on_carrier P.a_closed)
    from S R have
      "(\<Oplus>\<^bsub>S \<^esub>i\<in>{..deg R (p \<oplus>\<^bsub>P\<^esub> q)}. h (coeff P (p \<oplus>\<^bsub>P\<^esub> q) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) =
      (\<Oplus>\<^bsub>S \<^esub>i\<in>{..deg R (p \<oplus>\<^bsub>P\<^esub> q)} \<union> {deg R (p \<oplus>\<^bsub>P\<^esub> q)<..max (deg R p) (deg R q)}.
        h (coeff P (p \<oplus>\<^bsub>P\<^esub> q) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
      by (simp cong: S.finsum_cong
        add: deg_aboveD S.finsum_Un_disjoint ivl_disj_int_one Pi_def del: coeff_add)
    also from R have "... =
        (\<Oplus>\<^bsub>S\<^esub> i \<in> {..max (deg R p) (deg R q)}.
          h (coeff P (p \<oplus>\<^bsub>P\<^esub> q) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
      by (simp add: ivl_disj_un_one)
    also from R S have "... =
      (\<Oplus>\<^bsub>S\<^esub>i\<in>{..max (deg R p) (deg R q)}. h (coeff P p i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) \<oplus>\<^bsub>S\<^esub>
      (\<Oplus>\<^bsub>S\<^esub>i\<in>{..max (deg R p) (deg R q)}. h (coeff P q i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
      by (simp cong: S.finsum_cong
        add: S.l_distr deg_aboveD ivl_disj_int_one Pi_def)
    also have "... =
        (\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R p} \<union> {deg R p<..max (deg R p) (deg R q)}.
          h (coeff P p i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) \<oplus>\<^bsub>S\<^esub>
        (\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R q} \<union> {deg R q<..max (deg R p) (deg R q)}.
          h (coeff P q i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
      by (simp only: ivl_disj_un_one le_maxI1 le_maxI2)
    also from R S have "... =
      (\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R p}. h (coeff P p i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) \<oplus>\<^bsub>S\<^esub>
      (\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R q}. h (coeff P q i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
      by (simp cong: S.finsum_cong
        add: deg_aboveD S.finsum_Un_disjoint ivl_disj_int_one Pi_def)
    finally show
      "(\<Oplus>\<^bsub>S\<^esub>i \<in> {..deg R (p \<oplus>\<^bsub>P\<^esub> q)}. h (coeff P (p \<oplus>\<^bsub>P\<^esub> q) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) =
      (\<Oplus>\<^bsub>S\<^esub>i \<in> {..deg R p}. h (coeff P p i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) \<oplus>\<^bsub>S\<^esub>
      (\<Oplus>\<^bsub>S\<^esub>i \<in> {..deg R q}. h (coeff P q i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)" .
  qed
next
  show "eval R S h s \<one>\<^bsub>P\<^esub> = \<one>\<^bsub>S\<^esub>"
    by (simp only: eval_on_carrier UP_one_closed) simp
next
  fix p q
  assume R: "p \<in> carrier P" "q \<in> carrier P"
  then show "eval R S h s (p \<otimes>\<^bsub>P\<^esub> q) = eval R S h s p \<otimes>\<^bsub>S\<^esub> eval R S h s q"
  proof (simp only: eval_on_carrier UP_mult_closed)
    from R S have
      "(\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R (p \<otimes>\<^bsub>P\<^esub> q)}. h (coeff P (p \<otimes>\<^bsub>P\<^esub> q) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) =
      (\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R (p \<otimes>\<^bsub>P\<^esub> q)} \<union> {deg R (p \<otimes>\<^bsub>P\<^esub> q)<..deg R p + deg R q}.
        h (coeff P (p \<otimes>\<^bsub>P\<^esub> q) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
      by (simp cong: S.finsum_cong
        add: deg_aboveD S.finsum_Un_disjoint ivl_disj_int_one Pi_def
        del: coeff_mult)
    also from R have "... =
      (\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R p + deg R q}. h (coeff P (p \<otimes>\<^bsub>P\<^esub> q) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
      by (simp only: ivl_disj_un_one deg_mult_ring)
    also from R S have "... =
      (\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R p + deg R q}.
         \<Oplus>\<^bsub>S\<^esub> k \<in> {..i}.
           h (coeff P p k) \<otimes>\<^bsub>S\<^esub> h (coeff P q (i - k)) \<otimes>\<^bsub>S\<^esub>
           (s (^)\<^bsub>S\<^esub> k \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> (i - k)))"
      by (simp cong: S.finsum_cong add: S.nat_pow_mult Pi_def
        S.m_ac S.finsum_rdistr)
    also from R S have "... =
      (\<Oplus>\<^bsub>S\<^esub> i\<in>{..deg R p}. h (coeff P p i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) \<otimes>\<^bsub>S\<^esub>
      (\<Oplus>\<^bsub>S\<^esub> i\<in>{..deg R q}. h (coeff P q i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
      by (simp add: S.cauchy_product [THEN sym] bound.intro deg_aboveD S.m_ac
        Pi_def)
    finally show
      "(\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R (p \<otimes>\<^bsub>P\<^esub> q)}. h (coeff P (p \<otimes>\<^bsub>P\<^esub> q) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) =
      (\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R p}. h (coeff P p i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) \<otimes>\<^bsub>S\<^esub>
      (\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R q}. h (coeff P q i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)" .
  qed
qed

text {*
  The following lemma could be proved in @{text UP_cring} with the additional
  assumption that @{text h} is closed. *}

lemma (in UP_pre_univ_prop) eval_const:
  "[| s \<in> carrier S; r \<in> carrier R |] ==> eval R S h s (monom P r 0) = h r"
  by (simp only: eval_on_carrier monom_closed) simp

text {* Further properties of the evaluation homomorphism. *}

text {* The following proof is complicated by the fact that in arbitrary
  rings one might have @{term "one R = zero R"}. *}

(* TODO: simplify by cases "one R = zero R" *)

lemma (in UP_pre_univ_prop) eval_monom1:
  assumes S: "s \<in> carrier S"
  shows "eval R S h s (monom P \<one> 1) = s"
proof (simp only: eval_on_carrier monom_closed R.one_closed)
   from S have
    "(\<Oplus>\<^bsub>S\<^esub> i\<in>{..deg R (monom P \<one> 1)}. h (coeff P (monom P \<one> 1) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) =
    (\<Oplus>\<^bsub>S\<^esub> i\<in>{..deg R (monom P \<one> 1)} \<union> {deg R (monom P \<one> 1)<..1}.
      h (coeff P (monom P \<one> 1) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
    by (simp cong: S.finsum_cong del: coeff_monom
      add: deg_aboveD S.finsum_Un_disjoint ivl_disj_int_one Pi_def)
  also have "... =
    (\<Oplus>\<^bsub>S\<^esub> i \<in> {..1}. h (coeff P (monom P \<one> 1) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i)"
    by (simp only: ivl_disj_un_one deg_monom_le R.one_closed)
  also have "... = s"
  proof (cases "s = \<zero>\<^bsub>S\<^esub>")
    case True then show ?thesis by (simp add: Pi_def)
  next
    case False then show ?thesis by (simp add: S Pi_def)
  qed
  finally show "(\<Oplus>\<^bsub>S\<^esub> i \<in> {..deg R (monom P \<one> 1)}.
    h (coeff P (monom P \<one> 1) i) \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> i) = s" .
qed

end

text {* Interpretation of ring homomorphism lemmas. *}

sublocale UP_univ_prop < ring_hom_cring P S Eval
  unfolding Eval_def
  by unfold_locales (fast intro: eval_ring_hom)

lemma (in UP_cring) monom_pow:
  assumes R: "a \<in> carrier R"
  shows "(monom P a n) (^)\<^bsub>P\<^esub> m = monom P (a (^) m) (n * m)"
proof (induct m)
  case 0 from R show ?case by simp
next
  case Suc with R show ?case
    by (simp del: monom_mult add: monom_mult [THEN sym] add_commute)
qed

lemma (in ring_hom_cring) hom_pow [simp]:
  "x \<in> carrier R ==> h (x (^) n) = h x (^)\<^bsub>S\<^esub> (n::nat)"
  by (induct n) simp_all

lemma (in UP_univ_prop) Eval_monom:
  "r \<in> carrier R ==> Eval (monom P r n) = h r \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> n"
proof -
  assume R: "r \<in> carrier R"
  from R have "Eval (monom P r n) = Eval (monom P r 0 \<otimes>\<^bsub>P\<^esub> (monom P \<one> 1) (^)\<^bsub>P\<^esub> n)"
    by (simp del: monom_mult add: monom_mult [THEN sym] monom_pow)
  also
  from R eval_monom1 [where s = s, folded Eval_def]
  have "... = h r \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> n"
    by (simp add: eval_const [where s = s, folded Eval_def])
  finally show ?thesis .
qed

lemma (in UP_pre_univ_prop) eval_monom:
  assumes R: "r \<in> carrier R" and S: "s \<in> carrier S"
  shows "eval R S h s (monom P r n) = h r \<otimes>\<^bsub>S\<^esub> s (^)\<^bsub>S\<^esub> n"
proof -
  interpret UP_univ_prop R S h P s "eval R S h s"
    using UP_pre_univ_prop_axioms P_def R S
    by (auto intro: UP_univ_prop.intro UP_univ_prop_axioms.intro)
  from R
  show ?thesis by (rule Eval_monom)
qed

lemma (in UP_univ_prop) Eval_smult:
  "[| r \<in> carrier R; p \<in> carrier P |] ==> Eval (r \<odot>\<^bsub>P\<^esub> p) = h r \<otimes>\<^bsub>S\<^esub> Eval p"
proof -
  assume R: "r \<in> carrier R" and P: "p \<in> carrier P"
  then show ?thesis
    by (simp add: monom_mult_is_smult [THEN sym]
      eval_const [where s = s, folded Eval_def])
qed

lemma ring_hom_cringI:
  assumes "cring R"
    and "cring S"
    and "h \<in> ring_hom R S"
  shows "ring_hom_cring R S h"
  by (fast intro: ring_hom_cring.intro ring_hom_cring_axioms.intro
    cring.axioms assms)

context UP_pre_univ_prop
begin

lemma UP_hom_unique:
  assumes "ring_hom_cring P S Phi"
  assumes Phi: "Phi (monom P \<one> (Suc 0)) = s"
      "!!r. r \<in> carrier R ==> Phi (monom P r 0) = h r"
  assumes "ring_hom_cring P S Psi"
  assumes Psi: "Psi (monom P \<one> (Suc 0)) = s"
      "!!r. r \<in> carrier R ==> Psi (monom P r 0) = h r"
    and P: "p \<in> carrier P" and S: "s \<in> carrier S"
  shows "Phi p = Psi p"
proof -
  interpret ring_hom_cring P S Phi by fact
  interpret ring_hom_cring P S Psi by fact
  have "Phi p =
      Phi (\<Oplus>\<^bsub>P \<^esub>i \<in> {..deg R p}. monom P (coeff P p i) 0 \<otimes>\<^bsub>P\<^esub> monom P \<one> 1 (^)\<^bsub>P\<^esub> i)"
    by (simp add: up_repr P monom_mult [THEN sym] monom_pow del: monom_mult)
  also
  have "... =
      Psi (\<Oplus>\<^bsub>P \<^esub>i\<in>{..deg R p}. monom P (coeff P p i) 0 \<otimes>\<^bsub>P\<^esub> monom P \<one> 1 (^)\<^bsub>P\<^esub> i)"
    by (simp add: Phi Psi P Pi_def comp_def)
  also have "... = Psi p"
    by (simp add: up_repr P monom_mult [THEN sym] monom_pow del: monom_mult)
  finally show ?thesis .
qed

lemma ring_homD:
  assumes Phi: "Phi \<in> ring_hom P S"
  shows "ring_hom_cring P S Phi"
  by unfold_locales (rule Phi)

theorem UP_universal_property:
  assumes S: "s \<in> carrier S"
  shows "EX! Phi. Phi \<in> ring_hom P S \<inter> extensional (carrier P) &
    Phi (monom P \<one> 1) = s &
    (ALL r : carrier R. Phi (monom P r 0) = h r)"
  using S eval_monom1
  apply (auto intro: eval_ring_hom eval_const eval_extensional)
  apply (rule extensionalityI)
  apply (auto intro: UP_hom_unique ring_homD)
  done

end

text{*JE: The following lemma was added by me; it might be even lifted to a simpler locale*}

context monoid
begin

lemma nat_pow_eone[simp]: assumes x_in_G: "x \<in> carrier G" shows "x (^) (1::nat) = x"
  using nat_pow_Suc [of x 0] unfolding nat_pow_0 [of x] unfolding l_one [OF x_in_G] by simp

end

context UP_ring
begin

abbreviation lcoeff :: "(nat =>'a) => 'a" where "lcoeff p == coeff P p (deg R p)"

lemma lcoeff_nonzero2: assumes p_in_R: "p \<in> carrier P" and p_not_zero: "p \<noteq> \<zero>\<^bsub>P\<^esub>" shows "lcoeff p \<noteq> \<zero>" 
  using lcoeff_nonzero [OF p_not_zero p_in_R] .


subsection{*The long division algorithm: some previous facts.*}

lemma coeff_minus [simp]:
  assumes p: "p \<in> carrier P" and q: "q \<in> carrier P" shows "coeff P (p \<ominus>\<^bsub>P\<^esub> q) n = coeff P p n \<ominus> coeff P q n" 
  unfolding a_minus_def [OF p q] unfolding coeff_add [OF p a_inv_closed [OF q]] unfolding coeff_a_inv [OF q]
  using coeff_closed [OF p, of n] using coeff_closed [OF q, of n] by algebra

lemma lcoeff_closed [simp]: assumes p: "p \<in> carrier P" shows "lcoeff p \<in> carrier R"
  using coeff_closed [OF p, of "deg R p"] by simp

lemma deg_smult_decr: assumes a_in_R: "a \<in> carrier R" and f_in_P: "f \<in> carrier P" shows "deg R (a \<odot>\<^bsub>P\<^esub> f) \<le> deg R f"
  using deg_smult_ring [OF a_in_R f_in_P] by (cases "a = \<zero>", auto)

lemma coeff_monom_mult: assumes R: "c \<in> carrier R" and P: "p \<in> carrier P" 
  shows "coeff P (monom P c n \<otimes>\<^bsub>P\<^esub> p) (m + n) = c \<otimes> (coeff P p m)"
proof -
  have "coeff P (monom P c n \<otimes>\<^bsub>P\<^esub> p) (m + n) = (\<Oplus>i\<in>{..m + n}. (if n = i then c else \<zero>) \<otimes> coeff P p (m + n - i))"
    unfolding coeff_mult [OF monom_closed [OF R, of n] P, of "m + n"] unfolding coeff_monom [OF R, of n] by simp
  also have "(\<Oplus>i\<in>{..m + n}. (if n = i then c else \<zero>) \<otimes> coeff P p (m + n - i)) = 
    (\<Oplus>i\<in>{..m + n}. (if n = i then c \<otimes> coeff P p (m + n - i) else \<zero>))"
    using  R.finsum_cong [of "{..m + n}" "{..m + n}" "(\<lambda>i::nat. (if n = i then c else \<zero>) \<otimes> coeff P p (m + n - i))" 
      "(\<lambda>i::nat. (if n = i then c \<otimes> coeff P p (m + n - i) else \<zero>))"]
    using coeff_closed [OF P] unfolding Pi_def simp_implies_def using R by auto
  also have "\<dots> = c \<otimes> coeff P p m" using R.finsum_singleton [of n "{..m + n}" "(\<lambda>i. c \<otimes> coeff P p (m + n - i))"]
    unfolding Pi_def using coeff_closed [OF P] using P R by auto
  finally show ?thesis by simp
qed

lemma deg_lcoeff_cancel: 
  assumes p_in_P: "p \<in> carrier P" and q_in_P: "q \<in> carrier P" and r_in_P: "r \<in> carrier P" 
  and deg_r_nonzero: "deg R r \<noteq> 0"
  and deg_R_p: "deg R p \<le> deg R r" and deg_R_q: "deg R q \<le> deg R r" 
  and coeff_R_p_eq_q: "coeff P p (deg R r) = \<ominus>\<^bsub>R\<^esub> (coeff P q (deg R r))"
  shows "deg R (p \<oplus>\<^bsub>P\<^esub> q) < deg R r"
proof -
  have deg_le: "deg R (p \<oplus>\<^bsub>P\<^esub> q) \<le> deg R r"
  proof (rule deg_aboveI)
    fix m
    assume deg_r_le: "deg R r < m"
    show "coeff P (p \<oplus>\<^bsub>P\<^esub> q) m = \<zero>"
    proof -
      have slp: "deg R p < m" and "deg R q < m" using deg_R_p deg_R_q using deg_r_le by auto
      then have max_sl: "max (deg R p) (deg R q) < m" by simp
      then have "deg R (p \<oplus>\<^bsub>P\<^esub> q) < m" using deg_add [OF p_in_P q_in_P] by arith
      with deg_R_p deg_R_q show ?thesis using coeff_add [OF p_in_P q_in_P, of m]
        using deg_aboveD [of "p \<oplus>\<^bsub>P\<^esub> q" m] using p_in_P q_in_P by simp 
    qed
  qed (simp add: p_in_P q_in_P)
  moreover have deg_ne: "deg R (p \<oplus>\<^bsub>P\<^esub> q) \<noteq> deg R r"
  proof (rule ccontr)
    assume nz: "\<not> deg R (p \<oplus>\<^bsub>P\<^esub> q) \<noteq> deg R r" then have deg_eq: "deg R (p \<oplus>\<^bsub>P\<^esub> q) = deg R r" by simp
    from deg_r_nonzero have r_nonzero: "r \<noteq> \<zero>\<^bsub>P\<^esub>" by (cases "r = \<zero>\<^bsub>P\<^esub>", simp_all)
    have "coeff P (p \<oplus>\<^bsub>P\<^esub> q) (deg R r) = \<zero>\<^bsub>R\<^esub>" using coeff_add [OF p_in_P q_in_P, of "deg R r"] using coeff_R_p_eq_q
      using coeff_closed [OF p_in_P, of "deg R r"] coeff_closed [OF q_in_P, of "deg R r"] by algebra
    with lcoeff_nonzero [OF r_nonzero r_in_P]  and deg_eq show False using lcoeff_nonzero [of "p \<oplus>\<^bsub>P\<^esub> q"] using p_in_P q_in_P
      using deg_r_nonzero by (cases "p \<oplus>\<^bsub>P\<^esub> q \<noteq> \<zero>\<^bsub>P\<^esub>", auto)
  qed
  ultimately show ?thesis by simp
qed

lemma monom_deg_mult: 
  assumes f_in_P: "f \<in> carrier P" and g_in_P: "g \<in> carrier P" and deg_le: "deg R g \<le> deg R f"
  and a_in_R: "a \<in> carrier R"
  shows "deg R (g \<otimes>\<^bsub>P\<^esub> monom P a (deg R f - deg R g)) \<le> deg R f"
  using deg_mult_ring [OF g_in_P monom_closed [OF a_in_R, of "deg R f - deg R g"]]
  apply (cases "a = \<zero>") using g_in_P apply simp 
  using deg_monom [OF _ a_in_R, of "deg R f - deg R g"] using deg_le by simp

lemma deg_zero_impl_monom:
  assumes f_in_P: "f \<in> carrier P" and deg_f: "deg R f = 0" 
  shows "f = monom P (coeff P f 0) 0"
  apply (rule up_eqI) using coeff_monom [OF coeff_closed [OF f_in_P], of 0 0]
  using f_in_P deg_f using deg_aboveD [of f _] by auto

end


subsection {* The long division proof for commutative rings *}

context UP_cring
begin

lemma exI3: assumes exist: "Pred x y z" 
  shows "\<exists> x y z. Pred x y z"
  using exist by blast

text {* Jacobson's Theorem 2.14 *}

lemma long_div_theorem: 
  assumes g_in_P [simp]: "g \<in> carrier P" and f_in_P [simp]: "f \<in> carrier P"
  and g_not_zero: "g \<noteq> \<zero>\<^bsub>P\<^esub>"
  shows "\<exists> q r (k::nat). (q \<in> carrier P) \<and> (r \<in> carrier P) \<and> (lcoeff g)(^)\<^bsub>R\<^esub>k \<odot>\<^bsub>P\<^esub> f = g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r \<and> (r = \<zero>\<^bsub>P\<^esub> | deg R r < deg R g)"
  using f_in_P
proof (induct "deg R f" arbitrary: "f" rule: nat_less_induct)
  case (1 f)
  note f_in_P [simp] = "1.prems"
  let ?pred = "(\<lambda> q r (k::nat).
    (q \<in> carrier P) \<and> (r \<in> carrier P) 
    \<and> (lcoeff g)(^)\<^bsub>R\<^esub>k \<odot>\<^bsub>P\<^esub> f = g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r \<and> (r = \<zero>\<^bsub>P\<^esub> | deg R r < deg R g))"
  let ?lg = "lcoeff g" and ?lf = "lcoeff f"
  show ?case
  proof (cases "deg R f < deg R g")
    case True
    have "?pred \<zero>\<^bsub>P\<^esub> f 0" using True by force
    then show ?thesis by blast
  next
    case False then have deg_g_le_deg_f: "deg R g \<le> deg R f" by simp
    {
      let ?k = "1::nat"
      let ?f1 = "(g \<otimes>\<^bsub>P\<^esub> (monom P (?lf) (deg R f - deg R g))) \<oplus>\<^bsub>P\<^esub> \<ominus>\<^bsub>P\<^esub> (?lg \<odot>\<^bsub>P\<^esub> f)"
      let ?q = "monom P (?lf) (deg R f - deg R g)"
      have f1_in_carrier: "?f1 \<in> carrier P" and q_in_carrier: "?q \<in> carrier P" by simp_all
      show ?thesis
      proof (cases "deg R f = 0")
        case True
        {
          have deg_g: "deg R g = 0" using True using deg_g_le_deg_f by simp
          have "?pred f \<zero>\<^bsub>P\<^esub> 1"
            using deg_zero_impl_monom [OF g_in_P deg_g]
            using sym [OF monom_mult_is_smult [OF coeff_closed [OF g_in_P, of 0] f_in_P]]
            using deg_g by simp
          then show ?thesis by blast
        }
      next
        case False note deg_f_nzero = False
        {
          have exist: "lcoeff g (^) ?k \<odot>\<^bsub>P\<^esub> f = g \<otimes>\<^bsub>P\<^esub> ?q \<oplus>\<^bsub>P\<^esub> \<ominus>\<^bsub>P\<^esub> ?f1"
            by (simp add: minus_add r_neg sym [
              OF a_assoc [of "g \<otimes>\<^bsub>P\<^esub> ?q" "\<ominus>\<^bsub>P\<^esub> (g \<otimes>\<^bsub>P\<^esub> ?q)" "lcoeff g \<odot>\<^bsub>P\<^esub> f"]])
          have deg_remainder_l_f: "deg R (\<ominus>\<^bsub>P\<^esub> ?f1) < deg R f"
          proof (unfold deg_uminus [OF f1_in_carrier])
            show "deg R ?f1 < deg R f"
            proof (rule deg_lcoeff_cancel)
              show "deg R (\<ominus>\<^bsub>P\<^esub> (?lg \<odot>\<^bsub>P\<^esub> f)) \<le> deg R f"
                using deg_smult_ring [of ?lg f]
                using lcoeff_nonzero2 [OF g_in_P g_not_zero] by simp
              show "deg R (g \<otimes>\<^bsub>P\<^esub> ?q) \<le> deg R f"
                by (simp add: monom_deg_mult [OF f_in_P g_in_P deg_g_le_deg_f, of ?lf])
              show "coeff P (g \<otimes>\<^bsub>P\<^esub> ?q) (deg R f) = \<ominus> coeff P (\<ominus>\<^bsub>P\<^esub> (?lg \<odot>\<^bsub>P\<^esub> f)) (deg R f)"
                unfolding coeff_mult [OF g_in_P monom_closed 
                  [OF lcoeff_closed [OF f_in_P], 
                    of "deg R f - deg R g"], of "deg R f"]
                unfolding coeff_monom [OF lcoeff_closed 
                  [OF f_in_P], of "(deg R f - deg R g)"]
                using R.finsum_cong' [of "{..deg R f}" "{..deg R f}" 
                  "(\<lambda>i. coeff P g i \<otimes> (if deg R f - deg R g = deg R f - i then ?lf else \<zero>))" 
                  "(\<lambda>i. if deg R g = i then coeff P g i \<otimes> ?lf else \<zero>)"]
                using R.finsum_singleton [of "deg R g" "{.. deg R f}" "(\<lambda>i. coeff P g i \<otimes> ?lf)"]
                unfolding Pi_def using deg_g_le_deg_f by force
            qed (simp_all add: deg_f_nzero)
          qed
          then obtain q' r' k'
            where rem_desc: "?lg (^) (k'::nat) \<odot>\<^bsub>P\<^esub> (\<ominus>\<^bsub>P\<^esub> ?f1) = g \<otimes>\<^bsub>P\<^esub> q' \<oplus>\<^bsub>P\<^esub> r'"
            and rem_deg: "(r' = \<zero>\<^bsub>P\<^esub> \<or> deg R r' < deg R g)"
            and q'_in_carrier: "q' \<in> carrier P" and r'_in_carrier: "r' \<in> carrier P"
            using "1.hyps" using f1_in_carrier by blast
          show ?thesis
          proof (rule exI3 [of _ "((?lg (^) k') \<odot>\<^bsub>P\<^esub> ?q \<oplus>\<^bsub>P\<^esub> q')" r' "Suc k'"], intro conjI)
            show "(?lg (^) (Suc k')) \<odot>\<^bsub>P\<^esub> f = g \<otimes>\<^bsub>P\<^esub> ((?lg (^) k') \<odot>\<^bsub>P\<^esub> ?q \<oplus>\<^bsub>P\<^esub> q') \<oplus>\<^bsub>P\<^esub> r'"
            proof -
              have "(?lg (^) (Suc k')) \<odot>\<^bsub>P\<^esub> f = (?lg (^) k') \<odot>\<^bsub>P\<^esub> (g \<otimes>\<^bsub>P\<^esub> ?q \<oplus>\<^bsub>P\<^esub> \<ominus>\<^bsub>P\<^esub> ?f1)"
                using smult_assoc1 [OF _ _ f_in_P] using exist by simp
              also have "\<dots> = (?lg (^) k') \<odot>\<^bsub>P\<^esub> (g \<otimes>\<^bsub>P\<^esub> ?q) \<oplus>\<^bsub>P\<^esub> ((?lg (^) k') \<odot>\<^bsub>P\<^esub> ( \<ominus>\<^bsub>P\<^esub> ?f1))"
                using UP_smult_r_distr by simp
              also have "\<dots> = (?lg (^) k') \<odot>\<^bsub>P\<^esub> (g \<otimes>\<^bsub>P\<^esub> ?q) \<oplus>\<^bsub>P\<^esub> (g \<otimes>\<^bsub>P\<^esub> q' \<oplus>\<^bsub>P\<^esub> r')"
                unfolding rem_desc ..
              also have "\<dots> = (?lg (^) k') \<odot>\<^bsub>P\<^esub> (g \<otimes>\<^bsub>P\<^esub> ?q) \<oplus>\<^bsub>P\<^esub> g \<otimes>\<^bsub>P\<^esub> q' \<oplus>\<^bsub>P\<^esub> r'"
                using sym [OF a_assoc [of "?lg (^) k' \<odot>\<^bsub>P\<^esub> (g \<otimes>\<^bsub>P\<^esub> ?q)" "g \<otimes>\<^bsub>P\<^esub> q'" "r'"]]
                using r'_in_carrier q'_in_carrier by simp
              also have "\<dots> = (?lg (^) k') \<odot>\<^bsub>P\<^esub> (?q \<otimes>\<^bsub>P\<^esub> g) \<oplus>\<^bsub>P\<^esub> q' \<otimes>\<^bsub>P\<^esub> g \<oplus>\<^bsub>P\<^esub> r'"
                using q'_in_carrier by (auto simp add: m_comm)
              also have "\<dots> = (((?lg (^) k') \<odot>\<^bsub>P\<^esub> ?q) \<otimes>\<^bsub>P\<^esub> g) \<oplus>\<^bsub>P\<^esub> q' \<otimes>\<^bsub>P\<^esub> g \<oplus>\<^bsub>P\<^esub> r'" 
                using smult_assoc2 q'_in_carrier "1.prems" by auto
              also have "\<dots> = ((?lg (^) k') \<odot>\<^bsub>P\<^esub> ?q \<oplus>\<^bsub>P\<^esub> q') \<otimes>\<^bsub>P\<^esub> g \<oplus>\<^bsub>P\<^esub> r'"
                using sym [OF l_distr] and q'_in_carrier by auto
              finally show ?thesis using m_comm q'_in_carrier by auto
            qed
          qed (simp_all add: rem_deg q'_in_carrier r'_in_carrier)
        }
      qed
    }
  qed
qed

end


text {*The remainder theorem as corollary of the long division theorem.*}

context UP_cring
begin

lemma deg_minus_monom:
  assumes a: "a \<in> carrier R"
  and R_not_trivial: "(carrier R \<noteq> {\<zero>})"
  shows "deg R (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P a 0) = 1"
  (is "deg R ?g = 1")
proof -
  have "deg R ?g \<le> 1"
  proof (rule deg_aboveI)
    fix m
    assume "(1::nat) < m" 
    then show "coeff P ?g m = \<zero>" 
      using coeff_minus using a by auto algebra
  qed (simp add: a)
  moreover have "deg R ?g \<ge> 1"
  proof (rule deg_belowI)
    show "coeff P ?g 1 \<noteq> \<zero>"
      using a using R.carrier_one_not_zero R_not_trivial by simp algebra
  qed (simp add: a)
  ultimately show ?thesis by simp
qed

lemma lcoeff_monom:
  assumes a: "a \<in> carrier R" and R_not_trivial: "(carrier R \<noteq> {\<zero>})"
  shows "lcoeff (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P a 0) = \<one>"
  using deg_minus_monom [OF a R_not_trivial]
  using coeff_minus a by auto algebra

lemma deg_nzero_nzero:
  assumes deg_p_nzero: "deg R p \<noteq> 0"
  shows "p \<noteq> \<zero>\<^bsub>P\<^esub>"
  using deg_zero deg_p_nzero by auto

lemma deg_monom_minus:
  assumes a: "a \<in> carrier R"
  and R_not_trivial: "carrier R \<noteq> {\<zero>}"
  shows "deg R (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P a 0) = 1"
  (is "deg R ?g = 1")
proof -
  have "deg R ?g \<le> 1"
  proof (rule deg_aboveI)
    fix m::nat assume "1 < m" then show "coeff P ?g m = \<zero>" 
      using coeff_minus [OF monom_closed [OF R.one_closed, of 1] monom_closed [OF a, of 0], of m] 
      using coeff_monom [OF R.one_closed, of 1 m] using coeff_monom [OF a, of 0 m] by auto algebra
  qed (simp add: a)
  moreover have "1 \<le> deg R ?g"
  proof (rule deg_belowI)
    show "coeff P ?g 1 \<noteq> \<zero>" 
      using coeff_minus [OF monom_closed [OF R.one_closed, of 1] monom_closed [OF a, of 0], of 1]
      using coeff_monom [OF R.one_closed, of 1 1] using coeff_monom [OF a, of 0 1] 
      using R_not_trivial using R.carrier_one_not_zero
      by auto algebra
  qed (simp add: a)
  ultimately show ?thesis by simp
qed

lemma eval_monom_expr:
  assumes a: "a \<in> carrier R"
  shows "eval R R id a (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P a 0) = \<zero>"
  (is "eval R R id a ?g = _")
proof -
  interpret UP_pre_univ_prop R R id by unfold_locales simp
  have eval_ring_hom: "eval R R id a \<in> ring_hom P R" using eval_ring_hom [OF a] by simp
  interpret ring_hom_cring P R "eval R R id a" by unfold_locales (rule eval_ring_hom)
  have mon1_closed: "monom P \<one>\<^bsub>R\<^esub> 1 \<in> carrier P" 
    and mon0_closed: "monom P a 0 \<in> carrier P" 
    and min_mon0_closed: "\<ominus>\<^bsub>P\<^esub> monom P a 0 \<in> carrier P"
    using a R.a_inv_closed by auto
  have "eval R R id a ?g = eval R R id a (monom P \<one> 1) \<ominus> eval R R id a (monom P a 0)"
    unfolding P.minus_eq [OF mon1_closed mon0_closed]
    unfolding hom_add [OF mon1_closed min_mon0_closed]
    unfolding hom_a_inv [OF mon0_closed] 
    using R.minus_eq [symmetric] mon1_closed mon0_closed by auto
  also have "\<dots> = a \<ominus> a"
    using eval_monom [OF R.one_closed a, of 1] using eval_monom [OF a a, of 0] using a by simp
  also have "\<dots> = \<zero>"
    using a by algebra
  finally show ?thesis by simp
qed

lemma remainder_theorem_exist:
  assumes f: "f \<in> carrier P" and a: "a \<in> carrier R"
  and R_not_trivial: "carrier R \<noteq> {\<zero>}"
  shows "\<exists> q r. (q \<in> carrier P) \<and> (r \<in> carrier P) \<and> f = (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P a 0) \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r \<and> (deg R r = 0)"
  (is "\<exists> q r. (q \<in> carrier P) \<and> (r \<in> carrier P) \<and> f = ?g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r \<and> (deg R r = 0)")
proof -
  let ?g = "monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P a 0"
  from deg_minus_monom [OF a R_not_trivial]
  have deg_g_nzero: "deg R ?g \<noteq> 0" by simp
  have "\<exists>q r (k::nat). q \<in> carrier P \<and> r \<in> carrier P \<and>
    lcoeff ?g (^) k \<odot>\<^bsub>P\<^esub> f = ?g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r \<and> (r = \<zero>\<^bsub>P\<^esub> \<or> deg R r < deg R ?g)"
    using long_div_theorem [OF _ f deg_nzero_nzero [OF deg_g_nzero]] a
    by auto
  then show ?thesis
    unfolding lcoeff_monom [OF a R_not_trivial]
    unfolding deg_monom_minus [OF a R_not_trivial]
    using smult_one [OF f] using deg_zero by force
qed

lemma remainder_theorem_expression:
  assumes f [simp]: "f \<in> carrier P" and a [simp]: "a \<in> carrier R"
  and q [simp]: "q \<in> carrier P" and r [simp]: "r \<in> carrier P"
  and R_not_trivial: "carrier R \<noteq> {\<zero>}"
  and f_expr: "f = (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P a 0) \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r"
  (is "f = ?g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r" is "f = ?gq \<oplus>\<^bsub>P\<^esub> r")
    and deg_r_0: "deg R r = 0"
    shows "r = monom P (eval R R id a f) 0"
proof -
  interpret UP_pre_univ_prop R R id P by default simp
  have eval_ring_hom: "eval R R id a \<in> ring_hom P R"
    using eval_ring_hom [OF a] by simp
  have "eval R R id a f = eval R R id a ?gq \<oplus>\<^bsub>R\<^esub> eval R R id a r"
    unfolding f_expr using ring_hom_add [OF eval_ring_hom] by auto
  also have "\<dots> = ((eval R R id a ?g) \<otimes> (eval R R id a q)) \<oplus>\<^bsub>R\<^esub> eval R R id a r"
    using ring_hom_mult [OF eval_ring_hom] by auto
  also have "\<dots> = \<zero> \<oplus> eval R R id a r"
    unfolding eval_monom_expr [OF a] using eval_ring_hom 
    unfolding ring_hom_def using q unfolding Pi_def by simp
  also have "\<dots> = eval R R id a r"
    using eval_ring_hom unfolding ring_hom_def using r unfolding Pi_def by simp
  finally have eval_eq: "eval R R id a f = eval R R id a r" by simp
  from deg_zero_impl_monom [OF r deg_r_0]
  have "r = monom P (coeff P r 0) 0" by simp
  with eval_const [OF a, of "coeff P r 0"] eval_eq 
  show ?thesis by auto
qed

corollary remainder_theorem:
  assumes f [simp]: "f \<in> carrier P" and a [simp]: "a \<in> carrier R"
  and R_not_trivial: "carrier R \<noteq> {\<zero>}"
  shows "\<exists> q r. (q \<in> carrier P) \<and> (r \<in> carrier P) \<and> 
     f = (monom P \<one>\<^bsub>R\<^esub> 1 \<ominus>\<^bsub>P\<^esub> monom P a 0) \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> monom P (eval R R id a f) 0"
  (is "\<exists> q r. (q \<in> carrier P) \<and> (r \<in> carrier P) \<and> f = ?g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> monom P (eval R R id a f) 0")
proof -
  from remainder_theorem_exist [OF f a R_not_trivial]
  obtain q r
    where q_r: "q \<in> carrier P \<and> r \<in> carrier P \<and> f = ?g \<otimes>\<^bsub>P\<^esub> q \<oplus>\<^bsub>P\<^esub> r"
    and deg_r: "deg R r = 0" by force
  with remainder_theorem_expression [OF f a _ _ R_not_trivial, of q r]
  show ?thesis by auto
qed

end


subsection {* Sample Application of Evaluation Homomorphism *}

lemma UP_pre_univ_propI:
  assumes "cring R"
    and "cring S"
    and "h \<in> ring_hom R S"
  shows "UP_pre_univ_prop R S h"
  using assms
  by (auto intro!: UP_pre_univ_prop.intro ring_hom_cring.intro
    ring_hom_cring_axioms.intro UP_cring.intro)

definition
  INTEG :: "int ring"
  where "INTEG = (| carrier = UNIV, mult = op *, one = 1, zero = 0, add = op + |)"

lemma INTEG_cring: "cring INTEG"
  by (unfold INTEG_def) (auto intro!: cringI abelian_groupI comm_monoidI
    left_minus distrib_right)

lemma INTEG_id_eval:
  "UP_pre_univ_prop INTEG INTEG id"
  by (fast intro: UP_pre_univ_propI INTEG_cring id_ring_hom)

text {*
  Interpretation now enables to import all theorems and lemmas
  valid in the context of homomorphisms between @{term INTEG} and @{term
  "UP INTEG"} globally.
*}

interpretation INTEG: UP_pre_univ_prop INTEG INTEG id "UP INTEG"
  using INTEG_id_eval by simp_all

lemma INTEG_closed [intro, simp]:
  "z \<in> carrier INTEG"
  by (unfold INTEG_def) simp

lemma INTEG_mult [simp]:
  "mult INTEG z w = z * w"
  by (unfold INTEG_def) simp

lemma INTEG_pow [simp]:
  "pow INTEG z n = z ^ n"
  by (induct n) (simp_all add: INTEG_def nat_pow_def)

lemma "eval INTEG INTEG id 10 (monom (UP INTEG) 5 2) = 500"
  by (simp add: INTEG.eval_monom)

end
