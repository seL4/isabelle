(*
  Title:     Univariate Polynomials
  Id:        $Id$
  Author:    Clemens Ballarin, started 9 December 1996
  Copyright: Clemens Ballarin
*)

header {* Univariate Polynomials *}

theory UnivPoly = Module:

text {*
  Polynomials are formalised as modules with additional operations for
  extracting coefficients from polynomials and for obtaining monomials
  from coefficients and exponents (record @{text "up_ring"}).  The
  carrier set is a set of bounded functions from Nat to the
  coefficient domain.  Bounded means that these functions return zero
  above a certain bound (the degree).  There is a chapter on the
  formalisation of polynomials in my PhD thesis
  (\url{http://www4.in.tum.de/~ballarin/publications/}), which was
  implemented with axiomatic type classes.  This was later ported to
  Locales.
*}


subsection {* The Constructor for Univariate Polynomials *}

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

constdefs (structure R)
  up :: "_ => (nat => 'a) set"
  "up R == {f. f \<in> UNIV -> carrier R & (EX n. bound \<zero> n f)}"
  UP :: "_ => ('a, nat => 'a) up_ring"
  "UP R == (|
    carrier = up R,
    mult = (%p:up R. %q:up R. %n. \<Oplus>i \<in> {..n}. p i \<otimes> q (n-i)),
    one = (%i. if i=0 then \<one> else \<zero>),
    zero = (%i. \<zero>),
    add = (%p:up R. %q:up R. %i. p i \<oplus> q i),
    smult = (%a:carrier R. %p:up R. %i. a \<otimes> p i),
    monom = (%a:carrier R. %n i. if i=n then a else \<zero>),
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

lemma (in cring) bound_upD [dest]:
  "f \<in> up R ==> EX n. bound \<zero> n f"
  by (simp add: up_def)

lemma (in cring) up_one_closed:
   "(%n. if n = 0 then \<one> else \<zero>) \<in> up R"
  using up_def by force

lemma (in cring) up_smult_closed:
  "[| a \<in> carrier R; p \<in> up R |] ==> (%i. a \<otimes> p i) \<in> up R"
  by force

lemma (in cring) up_add_closed:
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
      with boundn and boundm and UP show "p i \<oplus> q i = \<zero>" by fastsimp
    qed
    then show ?thesis ..
  qed
qed

lemma (in cring) up_a_inv_closed:
  "p \<in> up R ==> (%i. \<ominus> (p i)) \<in> up R"
proof
  assume R: "p \<in> up R"
  then obtain n where "bound \<zero> n p" by auto
  then have "bound \<zero> n (%i. \<ominus> p i)" by auto
  then show "EX n. bound \<zero> n (%i. \<ominus> p i)" by auto
qed auto

lemma (in cring) up_mult_closed:
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


subsection {* Effect of operations on coefficients *}

locale UP = struct R + struct P +
  defines P_def: "P == UP R"

locale UP_cring = UP + cring R

locale UP_domain = UP_cring + "domain" R

text {*
  Temporarily declare @{text UP.P_def} as simp rule.
*}  (* TODO: use antiquotation once text (in locale) is supported. *)

declare (in UP) P_def [simp]

lemma (in UP_cring) coeff_monom [simp]:
  "a \<in> carrier R ==>
  coeff P (monom P a m) n = (if m=n then a else \<zero>)"
proof -
  assume R: "a \<in> carrier R"
  then have "(%n. if n = m then a else \<zero>) \<in> up R"
    using up_def by force
  with R show ?thesis by (simp add: UP_def)
qed

lemma (in UP_cring) coeff_zero [simp]:
  "coeff P \<zero>\<^sub>2 n = \<zero>"
  by (auto simp add: UP_def)

lemma (in UP_cring) coeff_one [simp]:
  "coeff P \<one>\<^sub>2 n = (if n=0 then \<one> else \<zero>)"
  using up_one_closed by (simp add: UP_def)

lemma (in UP_cring) coeff_smult [simp]:
  "[| a \<in> carrier R; p \<in> carrier P |] ==>
  coeff P (a \<odot>\<^sub>2 p) n = a \<otimes> coeff P p n"
  by (simp add: UP_def up_smult_closed)

lemma (in UP_cring) coeff_add [simp]:
  "[| p \<in> carrier P; q \<in> carrier P |] ==>
  coeff P (p \<oplus>\<^sub>2 q) n = coeff P p n \<oplus> coeff P q n"
  by (simp add: UP_def up_add_closed)

lemma (in UP_cring) coeff_mult [simp]:
  "[| p \<in> carrier P; q \<in> carrier P |] ==>
  coeff P (p \<otimes>\<^sub>2 q) n = (\<Oplus>i \<in> {..n}. coeff P p i \<otimes> coeff P q (n-i))"
  by (simp add: UP_def up_mult_closed)

lemma (in UP) up_eqI:
  assumes prem: "!!n. coeff P p n = coeff P q n"
    and R: "p \<in> carrier P" "q \<in> carrier P"
  shows "p = q"
proof
  fix x
  from prem and R show "p x = q x" by (simp add: UP_def)
qed

subsection {* Polynomials form a commutative ring. *}

text {* Operations are closed over @{term P}. *}

lemma (in UP_cring) UP_mult_closed [simp]:
  "[| p \<in> carrier P; q \<in> carrier P |] ==> p \<otimes>\<^sub>2 q \<in> carrier P"
  by (simp add: UP_def up_mult_closed)

lemma (in UP_cring) UP_one_closed [simp]:
  "\<one>\<^sub>2 \<in> carrier P"
  by (simp add: UP_def up_one_closed)

lemma (in UP_cring) UP_zero_closed [intro, simp]:
  "\<zero>\<^sub>2 \<in> carrier P"
  by (auto simp add: UP_def)

lemma (in UP_cring) UP_a_closed [intro, simp]:
  "[| p \<in> carrier P; q \<in> carrier P |] ==> p \<oplus>\<^sub>2 q \<in> carrier P"
  by (simp add: UP_def up_add_closed)

lemma (in UP_cring) monom_closed [simp]:
  "a \<in> carrier R ==> monom P a n \<in> carrier P"
  by (auto simp add: UP_def up_def Pi_def)

lemma (in UP_cring) UP_smult_closed [simp]:
  "[| a \<in> carrier R; p \<in> carrier P |] ==> a \<odot>\<^sub>2 p \<in> carrier P"
  by (simp add: UP_def up_smult_closed)

lemma (in UP) coeff_closed [simp]:
  "p \<in> carrier P ==> coeff P p n \<in> carrier R"
  by (auto simp add: UP_def)

declare (in UP) P_def [simp del]

text {* Algebraic ring properties *}

lemma (in UP_cring) UP_a_assoc:
  assumes R: "p \<in> carrier P" "q \<in> carrier P" "r \<in> carrier P"
  shows "(p \<oplus>\<^sub>2 q) \<oplus>\<^sub>2 r = p \<oplus>\<^sub>2 (q \<oplus>\<^sub>2 r)"
  by (rule up_eqI, simp add: a_assoc R, simp_all add: R)

lemma (in UP_cring) UP_l_zero [simp]:
  assumes R: "p \<in> carrier P"
  shows "\<zero>\<^sub>2 \<oplus>\<^sub>2 p = p"
  by (rule up_eqI, simp_all add: R)

lemma (in UP_cring) UP_l_neg_ex:
  assumes R: "p \<in> carrier P"
  shows "EX q : carrier P. q \<oplus>\<^sub>2 p = \<zero>\<^sub>2"
proof -
  let ?q = "%i. \<ominus> (p i)"
  from R have closed: "?q \<in> carrier P"
    by (simp add: UP_def P_def up_a_inv_closed)
  from R have coeff: "!!n. coeff P ?q n = \<ominus> (coeff P p n)"
    by (simp add: UP_def P_def up_a_inv_closed)
  show ?thesis
  proof
    show "?q \<oplus>\<^sub>2 p = \<zero>\<^sub>2"
      by (auto intro!: up_eqI simp add: R closed coeff R.l_neg)
  qed (rule closed)
qed

lemma (in UP_cring) UP_a_comm:
  assumes R: "p \<in> carrier P" "q \<in> carrier P"
  shows "p \<oplus>\<^sub>2 q = q \<oplus>\<^sub>2 p"
  by (rule up_eqI, simp add: a_comm R, simp_all add: R)

ML_setup {*
  simpset_ref() := simpset() setsubgoaler asm_full_simp_tac;
*}

lemma (in UP_cring) UP_m_assoc:
  assumes R: "p \<in> carrier P" "q \<in> carrier P" "r \<in> carrier P"
  shows "(p \<otimes>\<^sub>2 q) \<otimes>\<^sub>2 r = p \<otimes>\<^sub>2 (q \<otimes>\<^sub>2 r)"
proof (rule up_eqI)
  fix n
  {
    fix k and a b c :: "nat=>'a"
    assume R: "a \<in> UNIV -> carrier R" "b \<in> UNIV -> carrier R"
      "c \<in> UNIV -> carrier R"
    then have "k <= n ==>
      (\<Oplus>j \<in> {..k}. (\<Oplus>i \<in> {..j}. a i \<otimes> b (j-i)) \<otimes> c (n-j)) =
      (\<Oplus>j \<in> {..k}. a j \<otimes> (\<Oplus>i \<in> {..k-j}. b i \<otimes> c (n-j-i)))"
      (concl is "?eq k")
    proof (induct k)
      case 0 then show ?case by (simp add: Pi_def m_assoc)
    next
      case (Suc k)
      then have "k <= n" by arith
      then have "?eq k" by (rule Suc)
      with R show ?case
        by (simp cong: finsum_cong
             add: Suc_diff_le Pi_def l_distr r_distr m_assoc)
          (simp cong: finsum_cong add: Pi_def a_ac finsum_ldistr m_assoc)
    qed
  }
  with R show "coeff P ((p \<otimes>\<^sub>2 q) \<otimes>\<^sub>2 r) n = coeff P (p \<otimes>\<^sub>2 (q \<otimes>\<^sub>2 r)) n"
    by (simp add: Pi_def)
qed (simp_all add: R)

ML_setup {*
  simpset_ref() := simpset() setsubgoaler asm_simp_tac;
*}

lemma (in UP_cring) UP_l_one [simp]:
  assumes R: "p \<in> carrier P"
  shows "\<one>\<^sub>2 \<otimes>\<^sub>2 p = p"
proof (rule up_eqI)
  fix n
  show "coeff P (\<one>\<^sub>2 \<otimes>\<^sub>2 p) n = coeff P p n"
  proof (cases n)
    case 0 with R show ?thesis by simp
  next
    case Suc with R show ?thesis
      by (simp del: finsum_Suc add: finsum_Suc2 Pi_def)
  qed
qed (simp_all add: R)

lemma (in UP_cring) UP_l_distr:
  assumes R: "p \<in> carrier P" "q \<in> carrier P" "r \<in> carrier P"
  shows "(p \<oplus>\<^sub>2 q) \<otimes>\<^sub>2 r = (p \<otimes>\<^sub>2 r) \<oplus>\<^sub>2 (q \<otimes>\<^sub>2 r)"
  by (rule up_eqI) (simp add: l_distr R Pi_def, simp_all add: R)

lemma (in UP_cring) UP_m_comm:
  assumes R: "p \<in> carrier P" "q \<in> carrier P"
  shows "p \<otimes>\<^sub>2 q = q \<otimes>\<^sub>2 p"
proof (rule up_eqI)
  fix n
  {
    fix k and a b :: "nat=>'a"
    assume R: "a \<in> UNIV -> carrier R" "b \<in> UNIV -> carrier R"
    then have "k <= n ==>
      (\<Oplus>i \<in> {..k}. a i \<otimes> b (n-i)) =
      (\<Oplus>i \<in> {..k}. a (k-i) \<otimes> b (i+n-k))"
      (concl is "?eq k")
    proof (induct k)
      case 0 then show ?case by (simp add: Pi_def)
    next
      case (Suc k) then show ?case
        by (subst finsum_Suc2) (simp add: Pi_def a_comm)+
    qed
  }
  note l = this
  from R show "coeff P (p \<otimes>\<^sub>2 q) n =  coeff P (q \<otimes>\<^sub>2 p) n"
    apply (simp add: Pi_def)
    apply (subst l)
    apply (auto simp add: Pi_def)
    apply (simp add: m_comm)
    done
qed (simp_all add: R)

theorem (in UP_cring) UP_cring:
  "cring P"
  by (auto intro!: cringI abelian_groupI comm_monoidI UP_a_assoc UP_l_zero
    UP_l_neg_ex UP_a_comm UP_m_assoc UP_l_one UP_m_comm UP_l_distr)

lemma (in UP_cring) UP_ring:  (* preliminary *)
  "ring P"
  by (auto intro: ring.intro cring.axioms UP_cring)

lemma (in UP_cring) UP_a_inv_closed [intro, simp]:
  "p \<in> carrier P ==> \<ominus>\<^sub>2 p \<in> carrier P"
  by (rule abelian_group.a_inv_closed
    [OF ring.is_abelian_group [OF UP_ring]])

lemma (in UP_cring) coeff_a_inv [simp]:
  assumes R: "p \<in> carrier P"
  shows "coeff P (\<ominus>\<^sub>2 p) n = \<ominus> (coeff P p n)"
proof -
  from R coeff_closed UP_a_inv_closed have
    "coeff P (\<ominus>\<^sub>2 p) n = \<ominus> coeff P p n \<oplus> (coeff P p n \<oplus> coeff P (\<ominus>\<^sub>2 p) n)"
    by algebra
  also from R have "... =  \<ominus> (coeff P p n)"
    by (simp del: coeff_add add: coeff_add [THEN sym]
      abelian_group.r_neg [OF ring.is_abelian_group [OF UP_ring]])
  finally show ?thesis .
qed

text {*
  Instantiation of lemmas from @{term cring}.
*}

lemma (in UP_cring) UP_monoid:
  "monoid P"
  by (fast intro!: cring.is_comm_monoid comm_monoid.axioms monoid.intro
    UP_cring)
(* TODO: provide cring.is_monoid *)

lemma (in UP_cring) UP_comm_semigroup:
  "comm_semigroup P"
  by (fast intro!: cring.is_comm_monoid comm_monoid.axioms comm_semigroup.intro
    UP_cring)

lemma (in UP_cring) UP_comm_monoid:
  "comm_monoid P"
  by (fast intro!: cring.is_comm_monoid UP_cring)

lemma (in UP_cring) UP_abelian_monoid:
  "abelian_monoid P"
  by (fast intro!: abelian_group.axioms ring.is_abelian_group UP_ring)

lemma (in UP_cring) UP_abelian_group:
  "abelian_group P"
  by (fast intro!: ring.is_abelian_group UP_ring)

lemmas (in UP_cring) UP_r_one [simp] =
  monoid.r_one [OF UP_monoid]

lemmas (in UP_cring) UP_nat_pow_closed [intro, simp] =
  monoid.nat_pow_closed [OF UP_monoid]

lemmas (in UP_cring) UP_nat_pow_0 [simp] =
  monoid.nat_pow_0 [OF UP_monoid]

lemmas (in UP_cring) UP_nat_pow_Suc [simp] =
  monoid.nat_pow_Suc [OF UP_monoid]

lemmas (in UP_cring) UP_nat_pow_one [simp] =
  monoid.nat_pow_one [OF UP_monoid]

lemmas (in UP_cring) UP_nat_pow_mult =
  monoid.nat_pow_mult [OF UP_monoid]

lemmas (in UP_cring) UP_nat_pow_pow =
  monoid.nat_pow_pow [OF UP_monoid]

lemmas (in UP_cring) UP_m_lcomm =
  comm_semigroup.m_lcomm [OF UP_comm_semigroup]

lemmas (in UP_cring) UP_m_ac = UP_m_assoc UP_m_comm UP_m_lcomm

lemmas (in UP_cring) UP_nat_pow_distr =
  comm_monoid.nat_pow_distr [OF UP_comm_monoid]

lemmas (in UP_cring) UP_a_lcomm = abelian_monoid.a_lcomm [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_r_zero [simp] =
  abelian_monoid.r_zero [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_a_ac = UP_a_assoc UP_a_comm UP_a_lcomm

lemmas (in UP_cring) UP_finsum_empty [simp] =
  abelian_monoid.finsum_empty [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_insert [simp] =
  abelian_monoid.finsum_insert [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_zero [simp] =
  abelian_monoid.finsum_zero [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_closed [simp] =
  abelian_monoid.finsum_closed [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_Un_Int =
  abelian_monoid.finsum_Un_Int [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_Un_disjoint =
  abelian_monoid.finsum_Un_disjoint [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_addf =
  abelian_monoid.finsum_addf [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_cong' =
  abelian_monoid.finsum_cong' [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_0 [simp] =
  abelian_monoid.finsum_0 [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_Suc [simp] =
  abelian_monoid.finsum_Suc [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_Suc2 =
  abelian_monoid.finsum_Suc2 [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_add [simp] =
  abelian_monoid.finsum_add [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_finsum_cong =
  abelian_monoid.finsum_cong [OF UP_abelian_monoid]

lemmas (in UP_cring) UP_minus_closed [intro, simp] =
  abelian_group.minus_closed [OF UP_abelian_group]

lemmas (in UP_cring) UP_a_l_cancel [simp] =
  abelian_group.a_l_cancel [OF UP_abelian_group]

lemmas (in UP_cring) UP_a_r_cancel [simp] =
  abelian_group.a_r_cancel [OF UP_abelian_group]

lemmas (in UP_cring) UP_l_neg =
  abelian_group.l_neg [OF UP_abelian_group]

lemmas (in UP_cring) UP_r_neg =
  abelian_group.r_neg [OF UP_abelian_group]

lemmas (in UP_cring) UP_minus_zero [simp] =
  abelian_group.minus_zero [OF UP_abelian_group]

lemmas (in UP_cring) UP_minus_minus [simp] =
  abelian_group.minus_minus [OF UP_abelian_group]

lemmas (in UP_cring) UP_minus_add =
  abelian_group.minus_add [OF UP_abelian_group]

lemmas (in UP_cring) UP_r_neg2 =
  abelian_group.r_neg2 [OF UP_abelian_group]

lemmas (in UP_cring) UP_r_neg1 =
  abelian_group.r_neg1 [OF UP_abelian_group]

lemmas (in UP_cring) UP_r_distr =
  ring.r_distr [OF UP_ring]

lemmas (in UP_cring) UP_l_null [simp] =
  ring.l_null [OF UP_ring]

lemmas (in UP_cring) UP_r_null [simp] =
  ring.r_null [OF UP_ring]

lemmas (in UP_cring) UP_l_minus =
  ring.l_minus [OF UP_ring]

lemmas (in UP_cring) UP_r_minus =
  ring.r_minus [OF UP_ring]

lemmas (in UP_cring) UP_finsum_ldistr =
  cring.finsum_ldistr [OF UP_cring]

lemmas (in UP_cring) UP_finsum_rdistr =
  cring.finsum_rdistr [OF UP_cring]


subsection {* Polynomials form an Algebra *}

lemma (in UP_cring) UP_smult_l_distr:
  "[| a \<in> carrier R; b \<in> carrier R; p \<in> carrier P |] ==>
  (a \<oplus> b) \<odot>\<^sub>2 p = a \<odot>\<^sub>2 p \<oplus>\<^sub>2 b \<odot>\<^sub>2 p"
  by (rule up_eqI) (simp_all add: R.l_distr)

lemma (in UP_cring) UP_smult_r_distr:
  "[| a \<in> carrier R; p \<in> carrier P; q \<in> carrier P |] ==>
  a \<odot>\<^sub>2 (p \<oplus>\<^sub>2 q) = a \<odot>\<^sub>2 p \<oplus>\<^sub>2 a \<odot>\<^sub>2 q"
  by (rule up_eqI) (simp_all add: R.r_distr)

lemma (in UP_cring) UP_smult_assoc1:
      "[| a \<in> carrier R; b \<in> carrier R; p \<in> carrier P |] ==>
      (a \<otimes> b) \<odot>\<^sub>2 p = a \<odot>\<^sub>2 (b \<odot>\<^sub>2 p)"
  by (rule up_eqI) (simp_all add: R.m_assoc)

lemma (in UP_cring) UP_smult_one [simp]:
      "p \<in> carrier P ==> \<one> \<odot>\<^sub>2 p = p"
  by (rule up_eqI) simp_all

lemma (in UP_cring) UP_smult_assoc2:
  "[| a \<in> carrier R; p \<in> carrier P; q \<in> carrier P |] ==>
  (a \<odot>\<^sub>2 p) \<otimes>\<^sub>2 q = a \<odot>\<^sub>2 (p \<otimes>\<^sub>2 q)"
  by (rule up_eqI) (simp_all add: R.finsum_rdistr R.m_assoc Pi_def)

text {*
  Instantiation of lemmas from @{term algebra}.
*}

(* TODO: move to CRing.thy, really a fact missing from the locales package *)

lemma (in cring) cring:
  "cring R"
  by (fast intro: cring.intro prems)

lemma (in UP_cring) UP_algebra:
  "algebra R P"
  by (auto intro: algebraI cring UP_cring UP_smult_l_distr UP_smult_r_distr
    UP_smult_assoc1 UP_smult_assoc2)

lemmas (in UP_cring) UP_smult_l_null [simp] =
  algebra.smult_l_null [OF UP_algebra]

lemmas (in UP_cring) UP_smult_r_null [simp] =
  algebra.smult_r_null [OF UP_algebra]

lemmas (in UP_cring) UP_smult_l_minus =
  algebra.smult_l_minus [OF UP_algebra]

lemmas (in UP_cring) UP_smult_r_minus =
  algebra.smult_r_minus [OF UP_algebra]

subsection {* Further lemmas involving monomials *}

lemma (in UP_cring) monom_zero [simp]:
  "monom P \<zero> n = \<zero>\<^sub>2"
  by (simp add: UP_def P_def)

ML_setup {*
  simpset_ref() := simpset() setsubgoaler asm_full_simp_tac;
*}

lemma (in UP_cring) monom_mult_is_smult:
  assumes R: "a \<in> carrier R" "p \<in> carrier P"
  shows "monom P a 0 \<otimes>\<^sub>2 p = a \<odot>\<^sub>2 p"
proof (rule up_eqI)
  fix n
  have "coeff P (p \<otimes>\<^sub>2 monom P a 0) n = coeff P (a \<odot>\<^sub>2 p) n"
  proof (cases n)
    case 0 with R show ?thesis by (simp add: R.m_comm)
  next
    case Suc with R show ?thesis
      by (simp cong: finsum_cong add: R.r_null Pi_def)
        (simp add: m_comm)
  qed
  with R show "coeff P (monom P a 0 \<otimes>\<^sub>2 p) n = coeff P (a \<odot>\<^sub>2 p) n"
    by (simp add: UP_m_comm)
qed (simp_all add: R)

ML_setup {*
  simpset_ref() := simpset() setsubgoaler asm_simp_tac;
*}

lemma (in UP_cring) monom_add [simp]:
  "[| a \<in> carrier R; b \<in> carrier R |] ==>
  monom P (a \<oplus> b) n = monom P a n \<oplus>\<^sub>2 monom P b n"
  by (rule up_eqI) simp_all

ML_setup {*
  simpset_ref() := simpset() setsubgoaler asm_full_simp_tac;
*}

lemma (in UP_cring) monom_one_Suc:
  "monom P \<one> (Suc n) = monom P \<one> n \<otimes>\<^sub>2 monom P \<one> 1"
proof (rule up_eqI)
  fix k
  show "coeff P (monom P \<one> (Suc n)) k = coeff P (monom P \<one> n \<otimes>\<^sub>2 monom P \<one> 1) k"
  proof (cases "k = Suc n")
    case True show ?thesis
    proof -
      from True have less_add_diff:
        "!!i. [| n < i; i <= n + m |] ==> n + m - i < m" by arith
      from True have "coeff P (monom P \<one> (Suc n)) k = \<one>" by simp
      also from True
      have "... = (\<Oplus>i \<in> {..n(} \<union> {n}. coeff P (monom P \<one> n) i \<otimes>
        coeff P (monom P \<one> 1) (k - i))"
        by (simp cong: finsum_cong add: finsum_Un_disjoint Pi_def)
      also have "... = (\<Oplus>i \<in>  {..n}. coeff P (monom P \<one> n) i \<otimes>
        coeff P (monom P \<one> 1) (k - i))"
        by (simp only: ivl_disj_un_singleton)
      also from True have "... = (\<Oplus>i \<in> {..n} \<union> {)n..k}. coeff P (monom P \<one> n) i \<otimes>
        coeff P (monom P \<one> 1) (k - i))"
        by (simp cong: finsum_cong add: finsum_Un_disjoint ivl_disj_int_one
          order_less_imp_not_eq Pi_def)
      also from True have "... = coeff P (monom P \<one> n \<otimes>\<^sub>2 monom P \<one> 1) k"
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
      have f1: "(\<Oplus>i \<in> {..n(}. ?s i) = \<zero>" by (simp cong: finsum_cong add: Pi_def)
      from neq have f2: "(\<Oplus>i \<in> {n}. ?s i) = \<zero>"
        by (simp cong: finsum_cong add: Pi_def) arith
      have f3: "n < k ==> (\<Oplus>i \<in> {)n..k}. ?s i) = \<zero>"
        by (simp cong: finsum_cong add: order_less_imp_not_eq Pi_def)
      show ?thesis
      proof (cases "k < n")
        case True then show ?thesis by (simp cong: finsum_cong add: Pi_def)
      next
        case False then have n_le_k: "n <= k" by arith
        show ?thesis
        proof (cases "n = k")
          case True
          then have "\<zero> = (\<Oplus>i \<in> {..n(} \<union> {n}. ?s i)"
            by (simp cong: finsum_cong add: finsum_Un_disjoint
              ivl_disj_int_singleton Pi_def)
          also from True have "... = (\<Oplus>i \<in> {..k}. ?s i)"
            by (simp only: ivl_disj_un_singleton)
          finally show ?thesis .
        next
          case False with n_le_k have n_less_k: "n < k" by arith
          with neq have "\<zero> = (\<Oplus>i \<in> {..n(} \<union> {n}. ?s i)"
            by (simp add: finsum_Un_disjoint f1 f2
              ivl_disj_int_singleton Pi_def del: Un_insert_right)
          also have "... = (\<Oplus>i \<in> {..n}. ?s i)"
            by (simp only: ivl_disj_un_singleton)
          also from n_less_k neq have "... = (\<Oplus>i \<in> {..n} \<union> {)n..k}. ?s i)"
            by (simp add: finsum_Un_disjoint f3 ivl_disj_int_one Pi_def)
          also from n_less_k have "... = (\<Oplus>i \<in> {..k}. ?s i)"
            by (simp only: ivl_disj_un_one)
          finally show ?thesis .
        qed
      qed
    qed
    also have "... = coeff P (monom P \<one> n \<otimes>\<^sub>2 monom P \<one> 1) k" by simp
    finally show ?thesis .
  qed
qed (simp_all)

ML_setup {*
  simpset_ref() := simpset() setsubgoaler asm_simp_tac;
*}

lemma (in UP_cring) monom_mult_smult:
  "[| a \<in> carrier R; b \<in> carrier R |] ==> monom P (a \<otimes> b) n = a \<odot>\<^sub>2 monom P b n"
  by (rule up_eqI) simp_all

lemma (in UP_cring) monom_one [simp]:
  "monom P \<one> 0 = \<one>\<^sub>2"
  by (rule up_eqI) simp_all

lemma (in UP_cring) monom_one_mult:
  "monom P \<one> (n + m) = monom P \<one> n \<otimes>\<^sub>2 monom P \<one> m"
proof (induct n)
  case 0 show ?case by simp
next
  case Suc then show ?case
    by (simp only: add_Suc monom_one_Suc) (simp add: UP_m_ac)
qed

lemma (in UP_cring) monom_mult [simp]:
  assumes R: "a \<in> carrier R" "b \<in> carrier R"
  shows "monom P (a \<otimes> b) (n + m) = monom P a n \<otimes>\<^sub>2 monom P b m"
proof -
  from R have "monom P (a \<otimes> b) (n + m) = monom P (a \<otimes> b \<otimes> \<one>) (n + m)" by simp
  also from R have "... = a \<otimes> b \<odot>\<^sub>2 monom P \<one> (n + m)"
    by (simp add: monom_mult_smult del: r_one)
  also have "... = a \<otimes> b \<odot>\<^sub>2 (monom P \<one> n \<otimes>\<^sub>2 monom P \<one> m)"
    by (simp only: monom_one_mult)
  also from R have "... = a \<odot>\<^sub>2 (b \<odot>\<^sub>2 (monom P \<one> n \<otimes>\<^sub>2 monom P \<one> m))"
    by (simp add: UP_smult_assoc1)
  also from R have "... = a \<odot>\<^sub>2 (b \<odot>\<^sub>2 (monom P \<one> m \<otimes>\<^sub>2 monom P \<one> n))"
    by (simp add: UP_m_comm)
  also from R have "... = a \<odot>\<^sub>2 ((b \<odot>\<^sub>2 monom P \<one> m) \<otimes>\<^sub>2 monom P \<one> n)"
    by (simp add: UP_smult_assoc2)
  also from R have "... = a \<odot>\<^sub>2 (monom P \<one> n \<otimes>\<^sub>2 (b \<odot>\<^sub>2 monom P \<one> m))"
    by (simp add: UP_m_comm)
  also from R have "... = (a \<odot>\<^sub>2 monom P \<one> n) \<otimes>\<^sub>2 (b \<odot>\<^sub>2 monom P \<one> m)"
    by (simp add: UP_smult_assoc2)
  also from R have "... = monom P (a \<otimes> \<one>) n \<otimes>\<^sub>2 monom P (b \<otimes> \<one>) m"
    by (simp add: monom_mult_smult del: r_one)
  also from R have "... = monom P a n \<otimes>\<^sub>2 monom P b m" by simp
  finally show ?thesis .
qed

lemma (in UP_cring) monom_a_inv [simp]:
  "a \<in> carrier R ==> monom P (\<ominus> a) n = \<ominus>\<^sub>2 monom P a n"
  by (rule up_eqI) simp_all

lemma (in UP_cring) monom_inj:
  "inj_on (%a. monom P a n) (carrier R)"
proof (rule inj_onI)
  fix x y
  assume R: "x \<in> carrier R" "y \<in> carrier R" and eq: "monom P x n = monom P y n"
  then have "coeff P (monom P x n) n = coeff P (monom P y n) n" by simp
  with R show "x = y" by simp
qed

subsection {* The degree function *}

constdefs (structure R)
  deg :: "[_, nat => 'a] => nat"
  "deg R p == LEAST n. bound \<zero> n (coeff (UP R) p)"

lemma (in UP_cring) deg_aboveI:
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
lemma (in UP_cring) deg_aboveD:
  "[| deg R p < m; p \<in> carrier P |] ==> coeff P p m = \<zero>"
proof -
  assume R: "p \<in> carrier P" and "deg R p < m"
  from R obtain n where "bound \<zero> n (coeff P p)"
    by (auto simp add: UP_def P_def)
  then have "bound \<zero> (deg R p) (coeff P p)"
    by (auto simp: deg_def P_def dest: LeastI)
  then show ?thesis ..
qed

lemma (in UP_cring) deg_belowI:
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

lemma (in UP_cring) lcoeff_nonzero_deg:
  assumes deg: "deg R p ~= 0" and R: "p \<in> carrier P"
  shows "coeff P p (deg R p) ~= \<zero>"
proof -
  from R obtain m where "deg R p <= m" and m_coeff: "coeff P p m ~= \<zero>"
  proof -
    have minus: "!!(n::nat) m. n ~= 0 ==> (n - Suc 0 < m) = (n <= m)"
      by arith
(* TODO: why does proof not work with "1" *)
    from deg have "deg R p - 1 < (LEAST n. bound \<zero> n (coeff P p))"
      by (unfold deg_def P_def) arith
    then have "~ bound \<zero> (deg R p - 1) (coeff P p)" by (rule not_less_Least)
    then have "EX m. deg R p - 1 < m & coeff P p m ~= \<zero>"
      by (unfold bound_def) fast
    then have "EX m. deg R p <= m & coeff P p m ~= \<zero>" by (simp add: deg minus)
    then show ?thesis by auto
  qed
  with deg_belowI R have "deg R p = m" by fastsimp
  with m_coeff show ?thesis by simp
qed

lemma (in UP_cring) lcoeff_nonzero_nonzero:
  assumes deg: "deg R p = 0" and nonzero: "p ~= \<zero>\<^sub>2" and R: "p \<in> carrier P"
  shows "coeff P p 0 ~= \<zero>"
proof -
  have "EX m. coeff P p m ~= \<zero>"
  proof (rule classical)
    assume "~ ?thesis"
    with R have "p = \<zero>\<^sub>2" by (auto intro: up_eqI)
    with nonzero show ?thesis by contradiction
  qed
  then obtain m where coeff: "coeff P p m ~= \<zero>" ..
  then have "m <= deg R p" by (rule deg_belowI)
  then have "m = 0" by (simp add: deg)
  with coeff show ?thesis by simp
qed

lemma (in UP_cring) lcoeff_nonzero:
  assumes neq: "p ~= \<zero>\<^sub>2" and R: "p \<in> carrier P"
  shows "coeff P p (deg R p) ~= \<zero>"
proof (cases "deg R p = 0")
  case True with neq R show ?thesis by (simp add: lcoeff_nonzero_nonzero)
next
  case False with neq R show ?thesis by (simp add: lcoeff_nonzero_deg)
qed

lemma (in UP_cring) deg_eqI:
  "[| !!m. n < m ==> coeff P p m = \<zero>;
      !!n. n ~= 0 ==> coeff P p n ~= \<zero>; p \<in> carrier P |] ==> deg R p = n"
by (fast intro: le_anti_sym deg_aboveI deg_belowI)

(* Degree and polynomial operations *)

lemma (in UP_cring) deg_add [simp]:
  assumes R: "p \<in> carrier P" "q \<in> carrier P"
  shows "deg R (p \<oplus>\<^sub>2 q) <= max (deg R p) (deg R q)"
proof (cases "deg R p <= deg R q")
  case True show ?thesis
    by (rule deg_aboveI) (simp_all add: True R deg_aboveD)
next
  case False show ?thesis
    by (rule deg_aboveI) (simp_all add: False R deg_aboveD)
qed

lemma (in UP_cring) deg_monom_le:
  "a \<in> carrier R ==> deg R (monom P a n) <= n"
  by (intro deg_aboveI) simp_all

lemma (in UP_cring) deg_monom [simp]:
  "[| a ~= \<zero>; a \<in> carrier R |] ==> deg R (monom P a n) = n"
  by (fastsimp intro: le_anti_sym deg_aboveI deg_belowI)

lemma (in UP_cring) deg_const [simp]:
  assumes R: "a \<in> carrier R" shows "deg R (monom P a 0) = 0"
proof (rule le_anti_sym)
  show "deg R (monom P a 0) <= 0" by (rule deg_aboveI) (simp_all add: R)
next
  show "0 <= deg R (monom P a 0)" by (rule deg_belowI) (simp_all add: R)
qed

lemma (in UP_cring) deg_zero [simp]:
  "deg R \<zero>\<^sub>2 = 0"
proof (rule le_anti_sym)
  show "deg R \<zero>\<^sub>2 <= 0" by (rule deg_aboveI) simp_all
next
  show "0 <= deg R \<zero>\<^sub>2" by (rule deg_belowI) simp_all
qed

lemma (in UP_cring) deg_one [simp]:
  "deg R \<one>\<^sub>2 = 0"
proof (rule le_anti_sym)
  show "deg R \<one>\<^sub>2 <= 0" by (rule deg_aboveI) simp_all
next
  show "0 <= deg R \<one>\<^sub>2" by (rule deg_belowI) simp_all
qed

lemma (in UP_cring) deg_uminus [simp]:
  assumes R: "p \<in> carrier P" shows "deg R (\<ominus>\<^sub>2 p) = deg R p"
proof (rule le_anti_sym)
  show "deg R (\<ominus>\<^sub>2 p) <= deg R p" by (simp add: deg_aboveI deg_aboveD R)
next
  show "deg R p <= deg R (\<ominus>\<^sub>2 p)"
    by (simp add: deg_belowI lcoeff_nonzero_deg
      inj_on_iff [OF a_inv_inj, of _ "\<zero>", simplified] R)
qed

lemma (in UP_domain) deg_smult_ring:
  "[| a \<in> carrier R; p \<in> carrier P |] ==>
  deg R (a \<odot>\<^sub>2 p) <= (if a = \<zero> then 0 else deg R p)"
  by (cases "a = \<zero>") (simp add: deg_aboveI deg_aboveD)+

lemma (in UP_domain) deg_smult [simp]:
  assumes R: "a \<in> carrier R" "p \<in> carrier P"
  shows "deg R (a \<odot>\<^sub>2 p) = (if a = \<zero> then 0 else deg R p)"
proof (rule le_anti_sym)
  show "deg R (a \<odot>\<^sub>2 p) <= (if a = \<zero> then 0 else deg R p)"
    by (rule deg_smult_ring)
next
  show "(if a = \<zero> then 0 else deg R p) <= deg R (a \<odot>\<^sub>2 p)"
  proof (cases "a = \<zero>")
  qed (simp, simp add: deg_belowI lcoeff_nonzero_deg integral_iff R)
qed

lemma (in UP_cring) deg_mult_cring:
  assumes R: "p \<in> carrier P" "q \<in> carrier P"
  shows "deg R (p \<otimes>\<^sub>2 q) <= deg R p + deg R q"
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
  with boundm R show "coeff P (p \<otimes>\<^sub>2 q) m = \<zero>" by simp
qed (simp add: R)

ML_setup {*
  simpset_ref() := simpset() setsubgoaler asm_full_simp_tac;
*}

lemma (in UP_domain) deg_mult [simp]:
  "[| p ~= \<zero>\<^sub>2; q ~= \<zero>\<^sub>2; p \<in> carrier P; q \<in> carrier P |] ==>
  deg R (p \<otimes>\<^sub>2 q) = deg R p + deg R q"
proof (rule le_anti_sym)
  assume "p \<in> carrier P" " q \<in> carrier P"
  show "deg R (p \<otimes>\<^sub>2 q) <= deg R p + deg R q" by (rule deg_mult_cring)
next
  let ?s = "(%i. coeff P p i \<otimes> coeff P q (deg R p + deg R q - i))"
  assume R: "p \<in> carrier P" "q \<in> carrier P" and nz: "p ~= \<zero>\<^sub>2" "q ~= \<zero>\<^sub>2"
  have less_add_diff: "!!(k::nat) n m. k < n ==> m < n + m - k" by arith
  show "deg R p + deg R q <= deg R (p \<otimes>\<^sub>2 q)"
  proof (rule deg_belowI, simp add: R)
    have "finsum R ?s {.. deg R p + deg R q}
      = finsum R ?s ({.. deg R p(} Un {deg R p .. deg R p + deg R q})"
      by (simp only: ivl_disj_un_one)
    also have "... = finsum R ?s {deg R p .. deg R p + deg R q}"
      by (simp cong: finsum_cong add: finsum_Un_disjoint ivl_disj_int_one
        deg_aboveD less_add_diff R Pi_def)
    also have "...= finsum R ?s ({deg R p} Un {)deg R p .. deg R p + deg R q})"
      by (simp only: ivl_disj_un_singleton)
    also have "... = coeff P p (deg R p) \<otimes> coeff P q (deg R q)"
      by (simp cong: finsum_cong add: finsum_Un_disjoint
        ivl_disj_int_singleton deg_aboveD R Pi_def)
    finally have "finsum R ?s {.. deg R p + deg R q}
      = coeff P p (deg R p) \<otimes> coeff P q (deg R q)" .
    with nz show "finsum R ?s {.. deg R p + deg R q} ~= \<zero>"
      by (simp add: integral_iff lcoeff_nonzero R)
    qed (simp add: R)
  qed

lemma (in UP_cring) coeff_finsum:
  assumes fin: "finite A"
  shows "p \<in> A -> carrier P ==>
    coeff P (finsum P p A) k == finsum R (%i. coeff P (p i) k) A"
  using fin by induct (auto simp: Pi_def)

ML_setup {*
  simpset_ref() := simpset() setsubgoaler asm_full_simp_tac;
*}

lemma (in UP_cring) up_repr:
  assumes R: "p \<in> carrier P"
  shows "(\<Oplus>\<^sub>2 i \<in> {..deg R p}. monom P (coeff P p i) i) = p"
proof (rule up_eqI)
  let ?s = "(%i. monom P (coeff P p i) i)"
  fix k
  from R have RR: "!!i. (if i = k then coeff P p i else \<zero>) \<in> carrier R"
    by simp
  show "coeff P (finsum P ?s {..deg R p}) k = coeff P p k"
  proof (cases "k <= deg R p")
    case True
    hence "coeff P (finsum P ?s {..deg R p}) k =
          coeff P (finsum P ?s ({..k} Un {)k..deg R p})) k"
      by (simp only: ivl_disj_un_one)
    also from True
    have "... = coeff P (finsum P ?s {..k}) k"
      by (simp cong: finsum_cong add: finsum_Un_disjoint
        ivl_disj_int_one order_less_imp_not_eq2 coeff_finsum R RR Pi_def)
    also
    have "... = coeff P (finsum P ?s ({..k(} Un {k})) k"
      by (simp only: ivl_disj_un_singleton)
    also have "... = coeff P p k"
      by (simp cong: finsum_cong add: setsum_Un_disjoint
        ivl_disj_int_singleton coeff_finsum deg_aboveD R RR Pi_def)
    finally show ?thesis .
  next
    case False
    hence "coeff P (finsum P ?s {..deg R p}) k =
          coeff P (finsum P ?s ({..deg R p(} Un {deg R p})) k"
      by (simp only: ivl_disj_un_singleton)
    also from False have "... = coeff P p k"
      by (simp cong: finsum_cong add: setsum_Un_disjoint ivl_disj_int_singleton
        coeff_finsum deg_aboveD R Pi_def)
    finally show ?thesis .
  qed
qed (simp_all add: R Pi_def)

lemma (in UP_cring) up_repr_le:
  "[| deg R p <= n; p \<in> carrier P |] ==>
  finsum P (%i. monom P (coeff P p i) i) {..n} = p"
proof -
  let ?s = "(%i. monom P (coeff P p i) i)"
  assume R: "p \<in> carrier P" and "deg R p <= n"
  then have "finsum P ?s {..n} = finsum P ?s ({..deg R p} Un {)deg R p..n})"
    by (simp only: ivl_disj_un_one)
  also have "... = finsum P ?s {..deg R p}"
    by (simp cong: UP_finsum_cong add: UP_finsum_Un_disjoint ivl_disj_int_one
      deg_aboveD R Pi_def)
  also have "... = p" by (rule up_repr)
  finally show ?thesis .
qed

ML_setup {*
  simpset_ref() := simpset() setsubgoaler asm_simp_tac;
*}

subsection {* Polynomials over an integral domain form an integral domain *}

lemma domainI:
  assumes cring: "cring R"
    and one_not_zero: "one R ~= zero R"
    and integral: "!!a b. [| mult R a b = zero R; a \<in> carrier R;
      b \<in> carrier R |] ==> a = zero R | b = zero R"
  shows "domain R"
  by (auto intro!: domain.intro domain_axioms.intro cring.axioms prems
    del: disjCI)

lemma (in UP_domain) UP_one_not_zero:
  "\<one>\<^sub>2 ~= \<zero>\<^sub>2"
proof
  assume "\<one>\<^sub>2 = \<zero>\<^sub>2"
  hence "coeff P \<one>\<^sub>2 0 = (coeff P \<zero>\<^sub>2 0)" by simp
  hence "\<one> = \<zero>" by simp
  with one_not_zero show "False" by contradiction
qed

lemma (in UP_domain) UP_integral:
  "[| p \<otimes>\<^sub>2 q = \<zero>\<^sub>2; p \<in> carrier P; q \<in> carrier P |] ==> p = \<zero>\<^sub>2 | q = \<zero>\<^sub>2"
proof -
  fix p q
  assume pq: "p \<otimes>\<^sub>2 q = \<zero>\<^sub>2" and R: "p \<in> carrier P" "q \<in> carrier P"
  show "p = \<zero>\<^sub>2 | q = \<zero>\<^sub>2"
  proof (rule classical)
    assume c: "~ (p = \<zero>\<^sub>2 | q = \<zero>\<^sub>2)"
    with R have "deg R p + deg R q = deg R (p \<otimes>\<^sub>2 q)" by simp
    also from pq have "... = 0" by simp
    finally have "deg R p + deg R q = 0" .
    then have f1: "deg R p = 0 & deg R q = 0" by simp
    from f1 R have "p = (\<Oplus>\<^sub>2 i \<in> {..0}. monom P (coeff P p i) i)"
      by (simp only: up_repr_le)
    also from R have "... = monom P (coeff P p 0) 0" by simp
    finally have p: "p = monom P (coeff P p 0) 0" .
    from f1 R have "q = (\<Oplus>\<^sub>2 i \<in> {..0}. monom P (coeff P q i) i)"
      by (simp only: up_repr_le)
    also from R have "... = monom P (coeff P q 0) 0" by simp
    finally have q: "q = monom P (coeff P q 0) 0" .
    from R have "coeff P p 0 \<otimes> coeff P q 0 = coeff P (p \<otimes>\<^sub>2 q) 0" by simp
    also from pq have "... = \<zero>" by simp
    finally have "coeff P p 0 \<otimes> coeff P q 0 = \<zero>" .
    with R have "coeff P p 0 = \<zero> | coeff P q 0 = \<zero>"
      by (simp add: R.integral_iff)
    with p q show "p = \<zero>\<^sub>2 | q = \<zero>\<^sub>2" by fastsimp
  qed
qed

theorem (in UP_domain) UP_domain:
  "domain P"
  by (auto intro!: domainI UP_cring UP_one_not_zero UP_integral del: disjCI)

text {*
  Instantiation of results from @{term domain}.
*}

lemmas (in UP_domain) UP_zero_not_one [simp] =
  domain.zero_not_one [OF UP_domain]

lemmas (in UP_domain) UP_integral_iff =
  domain.integral_iff [OF UP_domain]

lemmas (in UP_domain) UP_m_lcancel =
  domain.m_lcancel [OF UP_domain]

lemmas (in UP_domain) UP_m_rcancel =
  domain.m_rcancel [OF UP_domain]

lemma (in UP_domain) smult_integral:
  "[| a \<odot>\<^sub>2 p = \<zero>\<^sub>2; a \<in> carrier R; p \<in> carrier P |] ==> a = \<zero> | p = \<zero>\<^sub>2"
  by (simp add: monom_mult_is_smult [THEN sym] UP_integral_iff
    inj_on_iff [OF monom_inj, of _ "\<zero>", simplified])


subsection {* Evaluation Homomorphism and Universal Property*}

(* alternative congruence rule (possibly more efficient)
lemma (in abelian_monoid) finsum_cong2:
  "[| !!i. i \<in> A ==> f i \<in> carrier G = True; A = B;
  !!i. i \<in> B ==> f i = g i |] ==> finsum G f A = finsum G g B"
  sorry*)

ML_setup {*
  simpset_ref() := simpset() setsubgoaler asm_full_simp_tac;
*}

theorem (in cring) diagonal_sum:
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
      (* The following could be simplified if there was a reasoner for
        total orders integrated with simip. *)
      have R6: "!!i k. [| k <= j; i <= Suc j - k |] ==> g i \<in> carrier R"
        using Suc by (auto intro!: funcset_mem [OF Rg]) arith
      have R8: "!!i k. [| k <= Suc j; i <= k |] ==> g (k - i) \<in> carrier R"
        using Suc by (auto intro!: funcset_mem [OF Rg]) arith
      have R9: "!!i k. [| k <= Suc j |] ==> f k \<in> carrier R"
        using Suc by (auto intro!: funcset_mem [OF Rf])
      have R10: "!!i k. [| k <= Suc j; i <= Suc j - k |] ==> g i \<in> carrier R"
        using Suc by (auto intro!: funcset_mem [OF Rg]) arith
      have R11: "g 0 \<in> carrier R"
        using Suc by (auto intro!: funcset_mem [OF Rg])
      from Suc show ?case
        by (simp cong: finsum_cong add: Suc_diff_le a_ac
          Pi_def R6 R8 R9 R10 R11)
    qed
  }
  then show ?thesis by fast
qed

lemma (in abelian_monoid) boundD_carrier:
  "[| bound \<zero> n f; n < m |] ==> f m \<in> carrier G"
  by auto

theorem (in cring) cauchy_product:
  assumes bf: "bound \<zero> n f" and bg: "bound \<zero> m g"
    and Rf: "f \<in> {..n} -> carrier R" and Rg: "g \<in> {..m} -> carrier R"
  shows "(\<Oplus>k \<in> {..n + m}. \<Oplus>i \<in> {..k}. f i \<otimes> g (k - i)) =
    (\<Oplus>i \<in> {..n}. f i) \<otimes> (\<Oplus>i \<in> {..m}. g i)"        (* State revese direction? *)
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
  also have "... = (\<Oplus>k \<in> {..n} \<union> {)n..n + m}. \<Oplus>i \<in> {..n + m - k}. f k \<otimes> g i)"
    by (simp only: ivl_disj_un_one)
  also from f g have "... = (\<Oplus>k \<in> {..n}. \<Oplus>i \<in> {..n + m - k}. f k \<otimes> g i)"
    by (simp cong: finsum_cong
      add: bound.bound [OF bf] finsum_Un_disjoint ivl_disj_int_one Pi_def)
  also from f g have "... = (\<Oplus>k \<in> {..n}. \<Oplus>i \<in> {..m} \<union> {)m..n + m - k}. f k \<otimes> g i)"
    by (simp cong: finsum_cong add: ivl_disj_un_one le_add_diff Pi_def)
  also from f g have "... = (\<Oplus>k \<in> {..n}. \<Oplus>i \<in> {..m}. f k \<otimes> g i)"
    by (simp cong: finsum_cong
      add: bound.bound [OF bg] finsum_Un_disjoint ivl_disj_int_one Pi_def)
  also from f g have "... = (\<Oplus>i \<in> {..n}. f i) \<otimes> (\<Oplus>i \<in> {..m}. g i)"
    by (simp add: finsum_ldistr diagonal_sum Pi_def,
      simp cong: finsum_cong add: finsum_rdistr Pi_def)
  finally show ?thesis .
qed

lemma (in UP_cring) const_ring_hom:
  "(%a. monom P a 0) \<in> ring_hom R P"
  by (auto intro!: ring_hom_memI intro: up_eqI simp: monom_mult_is_smult)

constdefs (structure S)
  eval :: "[_, _, 'a => 'b, 'b, nat => 'a] => 'b"
  "eval R S phi s == \<lambda>p \<in> carrier (UP R).
    \<Oplus>i \<in> {..deg R p}. phi (coeff (UP R) p i) \<otimes> pow S s i"
(*
  "eval R S phi s p == if p \<in> carrier (UP R)
  then finsum S (%i. mult S (phi (coeff (UP R) p i)) (pow S s i)) {..deg R p}
  else arbitrary"
*)

locale ring_hom_UP_cring = ring_hom_cring R S + UP_cring R

lemma (in ring_hom_UP_cring) eval_on_carrier:
  "p \<in> carrier P ==>
    eval R S phi s p =
    (\<Oplus>\<^sub>2 i \<in> {..deg R p}. phi (coeff P p i) \<otimes>\<^sub>2 pow S s i)"
  by (unfold eval_def, fold P_def) simp

lemma (in ring_hom_UP_cring) eval_extensional:
  "eval R S phi s \<in> extensional (carrier P)"
  by (unfold eval_def, fold P_def) simp

theorem (in ring_hom_UP_cring) eval_ring_hom:
  "s \<in> carrier S ==> eval R S h s \<in> ring_hom P S"
proof (rule ring_hom_memI)
  fix p
  assume RS: "p \<in> carrier P" "s \<in> carrier S"
  then show "eval R S h s p \<in> carrier S"
    by (simp only: eval_on_carrier) (simp add: Pi_def)
next
  fix p q
  assume RS: "p \<in> carrier P" "q \<in> carrier P" "s \<in> carrier S"
  then show "eval R S h s (p \<otimes>\<^sub>3 q) = eval R S h s p \<otimes>\<^sub>2 eval R S h s q"
  proof (simp only: eval_on_carrier UP_mult_closed)
    from RS have
      "(\<Oplus>\<^sub>2 i \<in> {..deg R (p \<otimes>\<^sub>3 q)}. h (coeff P (p \<otimes>\<^sub>3 q) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) =
      (\<Oplus>\<^sub>2 i \<in> {..deg R (p \<otimes>\<^sub>3 q)} \<union> {)deg R (p \<otimes>\<^sub>3 q)..deg R p + deg R q}.
        h (coeff P (p \<otimes>\<^sub>3 q) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
      by (simp cong: finsum_cong
        add: deg_aboveD finsum_Un_disjoint ivl_disj_int_one Pi_def
        del: coeff_mult)
    also from RS have "... =
      (\<Oplus>\<^sub>2 i \<in> {..deg R p + deg R q}. h (coeff P (p \<otimes>\<^sub>3 q) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
      by (simp only: ivl_disj_un_one deg_mult_cring)
    also from RS have "... =
      (\<Oplus>\<^sub>2 i \<in> {..deg R p + deg R q}.
       \<Oplus>\<^sub>2 k \<in> {..i}. h (coeff P p k) \<otimes>\<^sub>2 h (coeff P q (i - k)) \<otimes>\<^sub>2 (s (^)\<^sub>2 k \<otimes>\<^sub>2 s (^)\<^sub>2 (i - k)))"
      by (simp cong: finsum_cong add: nat_pow_mult Pi_def
        S.m_ac S.finsum_rdistr)
    also from RS have "... =
      (\<Oplus>\<^sub>2i\<in>{..deg R p}. h (coeff P p i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) \<otimes>\<^sub>2
      (\<Oplus>\<^sub>2i\<in>{..deg R q}. h (coeff P q i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
      by (simp add: S.cauchy_product [THEN sym] bound.intro deg_aboveD S.m_ac
        Pi_def)
    finally show
      "(\<Oplus>\<^sub>2 i \<in> {..deg R (p \<otimes>\<^sub>3 q)}. h (coeff P (p \<otimes>\<^sub>3 q) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) =
      (\<Oplus>\<^sub>2 i \<in> {..deg R p}. h (coeff P p i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) \<otimes>\<^sub>2
      (\<Oplus>\<^sub>2 i \<in> {..deg R q}. h (coeff P q i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)" .
  qed
next
  fix p q
  assume RS: "p \<in> carrier P" "q \<in> carrier P" "s \<in> carrier S"
  then show "eval R S h s (p \<oplus>\<^sub>3 q) = eval R S h s p \<oplus>\<^sub>2 eval R S h s q"
  proof (simp only: eval_on_carrier UP_a_closed)
    from RS have
      "(\<Oplus>\<^sub>2i \<in> {..deg R (p \<oplus>\<^sub>3 q)}. h (coeff P (p \<oplus>\<^sub>3 q) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) =
      (\<Oplus>\<^sub>2i \<in> {..deg R (p \<oplus>\<^sub>3 q)} \<union> {)deg R (p \<oplus>\<^sub>3 q)..max (deg R p) (deg R q)}.
        h (coeff P (p \<oplus>\<^sub>3 q) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
      by (simp cong: finsum_cong
        add: deg_aboveD finsum_Un_disjoint ivl_disj_int_one Pi_def
        del: coeff_add)
    also from RS have "... =
        (\<Oplus>\<^sub>2 i \<in> {..max (deg R p) (deg R q)}. h (coeff P (p \<oplus>\<^sub>3 q) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
      by (simp add: ivl_disj_un_one)
    also from RS have "... =
      (\<Oplus>\<^sub>2i\<in>{..max (deg R p) (deg R q)}. h (coeff P p i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) \<oplus>\<^sub>2
      (\<Oplus>\<^sub>2i\<in>{..max (deg R p) (deg R q)}. h (coeff P q i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
      by (simp cong: finsum_cong
        add: l_distr deg_aboveD finsum_Un_disjoint ivl_disj_int_one Pi_def)
    also have "... =
        (\<Oplus>\<^sub>2 i \<in> {..deg R p} \<union> {)deg R p..max (deg R p) (deg R q)}.
          h (coeff P p i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) \<oplus>\<^sub>2
        (\<Oplus>\<^sub>2 i \<in> {..deg R q} \<union> {)deg R q..max (deg R p) (deg R q)}.
          h (coeff P q i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
      by (simp only: ivl_disj_un_one le_maxI1 le_maxI2)
    also from RS have "... =
      (\<Oplus>\<^sub>2 i \<in> {..deg R p}. h (coeff P p i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) \<oplus>\<^sub>2
      (\<Oplus>\<^sub>2 i \<in> {..deg R q}. h (coeff P q i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
      by (simp cong: finsum_cong
        add: deg_aboveD finsum_Un_disjoint ivl_disj_int_one Pi_def)
    finally show
      "(\<Oplus>\<^sub>2i \<in> {..deg R (p \<oplus>\<^sub>3 q)}. h (coeff P (p \<oplus>\<^sub>3 q) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) =
      (\<Oplus>\<^sub>2i \<in> {..deg R p}. h (coeff P p i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) \<oplus>\<^sub>2
      (\<Oplus>\<^sub>2i \<in> {..deg R q}. h (coeff P q i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
      .
  qed
next
  assume S: "s \<in> carrier S"
  then show "eval R S h s \<one>\<^sub>3 = \<one>\<^sub>2"
    by (simp only: eval_on_carrier UP_one_closed) simp
qed

text {* Instantiation of ring homomorphism lemmas. *}

lemma (in ring_hom_UP_cring) ring_hom_cring_P_S:
  "s \<in> carrier S ==> ring_hom_cring P S (eval R S h s)"
  by (fast intro!: ring_hom_cring.intro UP_cring cring.axioms prems
  intro: ring_hom_cring_axioms.intro eval_ring_hom)

lemma (in ring_hom_UP_cring) UP_hom_closed [intro, simp]:
  "[| s \<in> carrier S; p \<in> carrier P |] ==> eval R S h s p \<in> carrier S"
  by (rule ring_hom_cring.hom_closed [OF ring_hom_cring_P_S])

lemma (in ring_hom_UP_cring) UP_hom_mult [simp]:
  "[| s \<in> carrier S; p \<in> carrier P; q \<in> carrier P |] ==>
  eval R S h s (p \<otimes>\<^sub>3 q) = eval R S h s p \<otimes>\<^sub>2 eval R S h s q"
  by (rule ring_hom_cring.hom_mult [OF ring_hom_cring_P_S])

lemma (in ring_hom_UP_cring) UP_hom_add [simp]:
  "[| s \<in> carrier S; p \<in> carrier P; q \<in> carrier P |] ==>
  eval R S h s (p \<oplus>\<^sub>3 q) = eval R S h s p \<oplus>\<^sub>2 eval R S h s q"
  by (rule ring_hom_cring.hom_add [OF ring_hom_cring_P_S])

lemma (in ring_hom_UP_cring) UP_hom_one [simp]:
  "s \<in> carrier S ==> eval R S h s \<one>\<^sub>3 = \<one>\<^sub>2"
  by (rule ring_hom_cring.hom_one [OF ring_hom_cring_P_S])

lemma (in ring_hom_UP_cring) UP_hom_zero [simp]:
  "s \<in> carrier S ==> eval R S h s \<zero>\<^sub>3 = \<zero>\<^sub>2"
  by (rule ring_hom_cring.hom_zero [OF ring_hom_cring_P_S])

lemma (in ring_hom_UP_cring) UP_hom_a_inv [simp]:
  "[| s \<in> carrier S; p \<in> carrier P |] ==>
  (eval R S h s) (\<ominus>\<^sub>3 p) = \<ominus>\<^sub>2 (eval R S h s) p"
  by (rule ring_hom_cring.hom_a_inv [OF ring_hom_cring_P_S])

lemma (in ring_hom_UP_cring) UP_hom_finsum [simp]:
  "[| s \<in> carrier S; finite A; f \<in> A -> carrier P |] ==>
  (eval R S h s) (finsum P f A) = finsum S (eval R S h s o f) A"
  by (rule ring_hom_cring.hom_finsum [OF ring_hom_cring_P_S])

lemma (in ring_hom_UP_cring) UP_hom_finprod [simp]:
  "[| s \<in> carrier S; finite A; f \<in> A -> carrier P |] ==>
  (eval R S h s) (finprod P f A) = finprod S (eval R S h s o f) A"
  by (rule ring_hom_cring.hom_finprod [OF ring_hom_cring_P_S])

text {* Further properties of the evaluation homomorphism. *}

(* The following lemma could be proved in UP\_cring with the additional
   assumption that h is closed. *)

lemma (in ring_hom_UP_cring) eval_const:
  "[| s \<in> carrier S; r \<in> carrier R |] ==> eval R S h s (monom P r 0) = h r"
  by (simp only: eval_on_carrier monom_closed) simp

text {* The following proof is complicated by the fact that in arbitrary
  rings one might have @{term "one R = zero R"}. *}

(* TODO: simplify by cases "one R = zero R" *)

lemma (in ring_hom_UP_cring) eval_monom1:
  "s \<in> carrier S ==> eval R S h s (monom P \<one> 1) = s"
proof (simp only: eval_on_carrier monom_closed R.one_closed)
  assume S: "s \<in> carrier S"
  then have
    "(\<Oplus>\<^sub>2 i \<in> {..deg R (monom P \<one> 1)}. h (coeff P (monom P \<one> 1) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) =
    (\<Oplus>\<^sub>2i\<in>{..deg R (monom P \<one> 1)} \<union> {)deg R (monom P \<one> 1)..1}.
      h (coeff P (monom P \<one> 1) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
    by (simp cong: finsum_cong del: coeff_monom
      add: deg_aboveD finsum_Un_disjoint ivl_disj_int_one Pi_def)
  also have "... =
    (\<Oplus>\<^sub>2 i \<in> {..1}. h (coeff P (monom P \<one> 1) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i)"
    by (simp only: ivl_disj_un_one deg_monom_le R.one_closed)
  also have "... = s"
  proof (cases "s = \<zero>\<^sub>2")
    case True then show ?thesis by (simp add: Pi_def)
  next
    case False with S show ?thesis by (simp add: Pi_def)
  qed
  finally show "(\<Oplus>\<^sub>2 i \<in> {..deg R (monom P \<one> 1)}.
    h (coeff P (monom P \<one> 1) i) \<otimes>\<^sub>2 s (^)\<^sub>2 i) = s" .
qed

lemma (in UP_cring) monom_pow:
  assumes R: "a \<in> carrier R"
  shows "(monom P a n) (^)\<^sub>2 m = monom P (a (^) m) (n * m)"
proof (induct m)
  case 0 from R show ?case by simp
next
  case Suc with R show ?case
    by (simp del: monom_mult add: monom_mult [THEN sym] add_commute)
qed

lemma (in ring_hom_cring) hom_pow [simp]:
  "x \<in> carrier R ==> h (x (^) n) = h x (^)\<^sub>2 (n::nat)"
  by (induct n) simp_all

lemma (in ring_hom_UP_cring) UP_hom_pow [simp]:
  "[| s \<in> carrier S; p \<in> carrier P |] ==>
  (eval R S h s) (p (^)\<^sub>3 n) = eval R S h s p (^)\<^sub>2 (n::nat)"
  by (rule ring_hom_cring.hom_pow [OF ring_hom_cring_P_S])

lemma (in ring_hom_UP_cring) eval_monom:
  "[| s \<in> carrier S; r \<in> carrier R |] ==>
  eval R S h s (monom P r n) = h r \<otimes>\<^sub>2 s (^)\<^sub>2 n"
proof -
  assume RS: "s \<in> carrier S" "r \<in> carrier R"
  then have "eval R S h s (monom P r n) =
    eval R S h s (monom P r 0 \<otimes>\<^sub>3 (monom P \<one> 1) (^)\<^sub>3 n)"
    by (simp del: monom_mult UP_hom_mult UP_hom_pow
      add: monom_mult [THEN sym] monom_pow)
  also from RS eval_monom1 have "... = h r \<otimes>\<^sub>2 s (^)\<^sub>2 n"
    by (simp add: eval_const)
  finally show ?thesis .
qed

lemma (in ring_hom_UP_cring) eval_smult:
  "[| s \<in> carrier S; r \<in> carrier R; p \<in> carrier P |] ==>
  eval R S h s (r \<odot>\<^sub>3 p) = h r \<otimes>\<^sub>2 eval R S h s p"
  by (simp add: monom_mult_is_smult [THEN sym] eval_const)

lemma ring_hom_cringI:
  assumes "cring R"
    and "cring S"
    and "h \<in> ring_hom R S"
  shows "ring_hom_cring R S h"
  by (fast intro: ring_hom_cring.intro ring_hom_cring_axioms.intro
    cring.axioms prems)

lemma (in ring_hom_UP_cring) UP_hom_unique:
  assumes Phi: "Phi \<in> ring_hom P S" "Phi (monom P \<one> (Suc 0)) = s"
      "!!r. r \<in> carrier R ==> Phi (monom P r 0) = h r"
    and Psi: "Psi \<in> ring_hom P S" "Psi (monom P \<one> (Suc 0)) = s"
      "!!r. r \<in> carrier R ==> Psi (monom P r 0) = h r"
    and RS: "s \<in> carrier S" "p \<in> carrier P"
  shows "Phi p = Psi p"
proof -
  have Phi_hom: "ring_hom_cring P S Phi"
    by (auto intro: ring_hom_cringI UP_cring S.cring Phi)
  have Psi_hom: "ring_hom_cring P S Psi"
    by (auto intro: ring_hom_cringI UP_cring S.cring Psi)
  have "Phi p = Phi (\<Oplus>\<^sub>3i \<in> {..deg R p}. monom P (coeff P p i) 0 \<otimes>\<^sub>3 monom P \<one> 1 (^)\<^sub>3 i)"
    by (simp add: up_repr RS monom_mult [THEN sym] monom_pow del: monom_mult)
  also have "... = Psi (\<Oplus>\<^sub>3i\<in>{..deg R p}. monom P (coeff P p i) 0 \<otimes>\<^sub>3 monom P \<one> 1 (^)\<^sub>3 i)"
    by (simp add: ring_hom_cring.hom_finsum [OF Phi_hom]
      ring_hom_cring.hom_mult [OF Phi_hom]
      ring_hom_cring.hom_pow [OF Phi_hom] Phi
      ring_hom_cring.hom_finsum [OF Psi_hom]
      ring_hom_cring.hom_mult [OF Psi_hom]
      ring_hom_cring.hom_pow [OF Psi_hom] Psi RS Pi_def comp_def)
  also have "... = Psi p"
    by (simp add: up_repr RS monom_mult [THEN sym] monom_pow del: monom_mult)
  finally show ?thesis .
qed


theorem (in ring_hom_UP_cring) UP_universal_property:
  "s \<in> carrier S ==>
  EX! Phi. Phi \<in> ring_hom P S \<inter> extensional (carrier P) &
    Phi (monom P \<one> 1) = s &
    (ALL r : carrier R. Phi (monom P r 0) = h r)"
  using eval_monom1
  apply (auto intro: eval_ring_hom eval_const eval_extensional)
  apply (rule extensionalityI)
  apply (auto intro: UP_hom_unique)
  done

subsection {* Sample application of evaluation homomorphism *}

lemma ring_hom_UP_cringI:
  assumes "cring R"
    and "cring S"
    and "h \<in> ring_hom R S"
  shows "ring_hom_UP_cring R S h"
  by (fast intro: ring_hom_UP_cring.intro ring_hom_cring_axioms.intro
    cring.axioms prems)

constdefs
  INTEG :: "int ring"
  "INTEG == (| carrier = UNIV, mult = op *, one = 1, zero = 0, add = op + |)"

lemma cring_INTEG:
  "cring INTEG"
  by (unfold INTEG_def) (auto intro!: cringI abelian_groupI comm_monoidI
    zadd_zminus_inverse2 zadd_zmult_distrib)

lemma INTEG_id:
  "ring_hom_UP_cring INTEG INTEG id"
  by (fast intro: ring_hom_UP_cringI cring_INTEG id_ring_hom)

text {*
  An instantiation mechanism would now import all theorems and lemmas
  valid in the context of homomorphisms between @{term INTEG} and @{term
  "UP INTEG"}.
*}

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
  by (simp add: ring_hom_UP_cring.eval_monom [OF INTEG_id])

end
