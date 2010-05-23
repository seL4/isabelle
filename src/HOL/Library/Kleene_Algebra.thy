(*  Title:      HOL/Library/Kleene_Algebra.thy
    Author:     Alexander Krauss, TU Muenchen
    Author:     Tjark Weber, University of Cambridge
*)

header {* Kleene Algebras *}

theory Kleene_Algebra
imports Main 
begin

text {* WARNING: This is work in progress. Expect changes in the future. *}

text {* Various lemmas correspond to entries in a database of theorems
  about Kleene algebras and related structures maintained by Peter
  H\"ofner: see
  \url{http://www.informatik.uni-augsburg.de/~hoefnepe/kleene_db/lemmas/index.html}. *}

subsection {* Preliminaries *}

text {* A class where addition is idempotent. *}

class idem_add = plus +
  assumes add_idem [simp]: "x + x = x"

text {* A class of idempotent abelian semigroups (written additively). *}

class idem_ab_semigroup_add = ab_semigroup_add + idem_add
begin

lemma add_idem2 [simp]: "x + (x + y) = x + y"
unfolding add_assoc[symmetric] by simp

lemma add_idem3 [simp]: "x + (y + x) = x + y"
by (simp add: add_commute)

end

text {* A class where order is defined in terms of addition. *}

class order_by_add = plus + ord +
  assumes order_def: "x \<le> y \<longleftrightarrow> x + y = y"
  assumes strict_order_def: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
begin

lemma ord_simp [simp]: "x \<le> y \<Longrightarrow> x + y = y"
  unfolding order_def .

lemma ord_intro: "x + y = y \<Longrightarrow> x \<le> y"
  unfolding order_def .

end

text {* A class of idempotent abelian semigroups (written additively)
  where order is defined in terms of addition. *}

class ordered_idem_ab_semigroup_add = idem_ab_semigroup_add + order_by_add
begin

lemma ord_simp2 [simp]: "x \<le> y \<Longrightarrow> y + x = y"
  unfolding order_def add_commute .

subclass order proof
  fix x y z :: 'a
  show "x \<le> x"
    unfolding order_def by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding order_def by (metis add_assoc)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    unfolding order_def by (simp add: add_commute)
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (fact strict_order_def)
qed

subclass ordered_ab_semigroup_add proof
  fix a b c :: 'a
  assume "a \<le> b" show "c + a \<le> c + b"
  proof (rule ord_intro)
    have "c + a + (c + b) = a + b + c" by (simp add: add_ac)
    also have "\<dots> = c + b" by (simp add: `a \<le> b` add_ac)
    finally show "c + a + (c + b) = c + b" .
  qed
qed

lemma plus_leI [simp]: 
  "x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x + y \<le> z"
  unfolding order_def by (simp add: add_assoc)

lemma less_add [simp]: "x \<le> x + y" "y \<le> x + y"
unfolding order_def by (auto simp: add_ac)

lemma add_est1 [elim]: "x + y \<le> z \<Longrightarrow> x \<le> z"
using less_add(1) by (rule order_trans)

lemma add_est2 [elim]: "x + y \<le> z \<Longrightarrow> y \<le> z"
using less_add(2) by (rule order_trans)

lemma add_supremum: "(x + y \<le> z) = (x \<le> z \<and> y \<le> z)"
by auto

end

text {* A class of commutative monoids (written additively) where
  order is defined in terms of addition. *}

class ordered_comm_monoid_add = comm_monoid_add + order_by_add
begin

lemma zero_minimum [simp]: "0 \<le> x"
unfolding order_def by simp

end

text {* A class of idempotent commutative monoids (written additively)
  where order is defined in terms of addition. *}

class ordered_idem_comm_monoid_add = ordered_comm_monoid_add + idem_add
begin

subclass ordered_idem_ab_semigroup_add ..

lemma sum_is_zero: "(x + y = 0) = (x = 0 \<and> y = 0)"
by (simp add: add_supremum eq_iff)

end

subsection {* A class of Kleene algebras *}

text {* Class @{text pre_kleene} provides all operations of Kleene
  algebras except for the Kleene star. *}

class pre_kleene = semiring_1 + idem_add + order_by_add
begin

subclass ordered_idem_comm_monoid_add ..

subclass ordered_semiring proof
  fix a b c :: 'a
  assume "a \<le> b"

  show "c * a \<le> c * b"
  proof (rule ord_intro)
    from `a \<le> b` have "c * (a + b) = c * b" by simp
    thus "c * a + c * b = c * b" by (simp add: right_distrib)
  qed

  show "a * c \<le> b * c"
  proof (rule ord_intro)
    from `a \<le> b` have "(a + b) * c = b * c" by simp
    thus "a * c + b * c = b * c" by (simp add: left_distrib)
  qed
qed

end

text {* A class that provides a star operator. *}

class star =
  fixes star :: "'a \<Rightarrow> 'a"

text {* Finally, a class of Kleene algebras. *}

class kleene = pre_kleene + star +
  assumes star1: "1 + a * star a \<le> star a"
  and star2: "1 + star a * a \<le> star a"
  and star3: "a * x \<le> x \<Longrightarrow> star a * x \<le> x"
  and star4: "x * a \<le> x \<Longrightarrow> x * star a \<le> x"
begin

lemma star3' [simp]:
  assumes a: "b + a * x \<le> x"
  shows "star a * b \<le> x"
by (metis assms less_add mult_left_mono order_trans star3 zero_minimum)

lemma star4' [simp]:
  assumes a: "b + x * a \<le> x"
  shows "b * star a \<le> x"
by (metis assms less_add mult_right_mono order_trans star4 zero_minimum)

lemma star_unfold_left: "1 + a * star a = star a"
proof (rule antisym, rule star1)
  have "1 + a * (1 + a * star a) \<le> 1 + a * star a"
    by (metis add_left_mono mult_left_mono star1 zero_minimum)
  with star3' have "star a * 1 \<le> 1 + a * star a" .
  thus "star a \<le> 1 + a * star a" by simp
qed

lemma star_unfold_right: "1 + star a * a = star a"
proof (rule antisym, rule star2)
  have "1 + (1 + star a * a) * a \<le> 1 + star a * a"
    by (metis add_left_mono mult_right_mono star2 zero_minimum)
  with star4' have "1 * star a \<le> 1 + star a * a" .
  thus "star a \<le> 1 + star a * a" by simp
qed

lemma star_zero [simp]: "star 0 = 1"
by (fact star_unfold_left[of 0, simplified, symmetric])

lemma star_one [simp]: "star 1 = 1"
by (metis add_idem2 eq_iff mult_1_right ord_simp2 star3 star_unfold_left)

lemma one_less_star [simp]: "1 \<le> star x"
by (metis less_add(1) star_unfold_left)

lemma ka1 [simp]: "x * star x \<le> star x"
by (metis less_add(2) star_unfold_left)

lemma star_mult_idem [simp]: "star x * star x = star x"
by (metis add_commute add_est1 eq_iff mult_1_right right_distrib star3 star_unfold_left)

lemma less_star [simp]: "x \<le> star x"
by (metis less_add(2) mult_1_right mult_left_mono one_less_star order_trans star_unfold_left zero_minimum)

lemma star_simulation_leq_1:
  assumes a: "a * x \<le> x * b"
  shows "star a * x \<le> x * star b"
proof (rule star3', rule order_trans)
  from a have "a * x * star b \<le> x * b * star b"
    by (rule mult_right_mono) simp
  thus "x + a * (x * star b) \<le> x + x * b * star b"
    using add_left_mono by (auto simp: mult_assoc)
  show "\<dots> \<le> x * star b"
    by (metis add_supremum ka1 mult.right_neutral mult_assoc mult_left_mono one_less_star zero_minimum)
qed

lemma star_simulation_leq_2:
  assumes a: "x * a \<le> b * x"
  shows "x * star a \<le> star b * x"
proof (rule star4', rule order_trans)
  from a have "star b * x * a \<le> star b * b * x"
    by (metis mult_assoc mult_left_mono zero_minimum)
  thus "x + star b * x * a \<le> x + star b * b * x"
    using add_mono by auto
  show "\<dots> \<le> star b * x"
    by (metis add_supremum left_distrib less_add mult.left_neutral mult_assoc mult_right_mono star_unfold_right zero_minimum)
qed

lemma star_simulation [simp]:
  assumes a: "a * x = x * b"
  shows "star a * x = x * star b"
by (metis antisym assms order_refl star_simulation_leq_1 star_simulation_leq_2)

lemma star_slide2 [simp]: "star x * x = x * star x"
by (metis star_simulation)

lemma star_idemp [simp]: "star (star x) = star x"
by (metis add_idem2 eq_iff less_star mult_1_right star3' star_mult_idem star_unfold_left)

lemma star_slide [simp]: "star (x * y) * x = x * star (y * x)"
by (auto simp: mult_assoc star_simulation)

lemma star_one':
  assumes "p * p' = 1" "p' * p = 1"
  shows "p' * star a * p = star (p' * a * p)"
proof -
  from assms
  have "p' * star a * p = p' * star (p * p' * a) * p"
    by simp
  also have "\<dots> = p' * p * star (p' * a * p)"
    by (simp add: mult_assoc)
  also have "\<dots> = star (p' * a * p)"
    by (simp add: assms)
  finally show ?thesis .
qed

lemma x_less_star [simp]: "x \<le> x * star a"
by (metis mult.right_neutral mult_left_mono one_less_star zero_minimum)

lemma star_mono [simp]: "x \<le> y \<Longrightarrow> star x \<le> star y"
by (metis add_commute eq_iff less_star ord_simp2 order_trans star3 star4' star_idemp star_mult_idem x_less_star)

lemma star_sub: "x \<le> 1 \<Longrightarrow> star x = 1"
by (metis add_commute ord_simp star_idemp star_mono star_mult_idem star_one star_unfold_left)

lemma star_unfold2: "star x * y = y + x * star x * y"
by (subst star_unfold_right[symmetric]) (simp add: mult_assoc left_distrib)

lemma star_absorb_one [simp]: "star (x + 1) = star x"
by (metis add_commute eq_iff left_distrib less_add mult_1_left mult_assoc star3 star_mono star_mult_idem star_unfold2 x_less_star)

lemma star_absorb_one' [simp]: "star (1 + x) = star x"
by (subst add_commute) (fact star_absorb_one)

lemma ka16: "(y * star x) * star (y * star x) \<le> star x * star (y * star x)"
by (metis ka1 less_add(1) mult_assoc order_trans star_unfold2)

lemma ka16': "(star x * y) * star (star x * y) \<le> star (star x * y) * star x"
by (metis ka1 mult_assoc order_trans star_slide x_less_star)

lemma ka17: "(x * star x) * star (y * star x) \<le> star x * star (y * star x)"
by (metis ka1 mult_assoc mult_right_mono zero_minimum)

lemma ka18: "(x * star x) * star (y * star x) + (y * star x) * star (y * star x)
  \<le> star x * star (y * star x)"
by (metis ka16 ka17 left_distrib mult_assoc plus_leI)

lemma star_decomp: "star (x + y) = star x * star (y * star x)"
proof (rule antisym)
  have "1 + (x + y) * star x * star (y * star x) \<le>
    1 + x * star x * star (y * star x) + y * star x * star (y * star x)"
    by (metis add_commute add_left_commute eq_iff left_distrib mult_assoc)
  also have "\<dots> \<le> star x * star (y * star x)"
    by (metis add_commute add_est1 add_left_commute ka18 plus_leI star_unfold_left x_less_star)
  finally show "star (x + y) \<le> star x * star (y * star x)"
    by (metis mult_1_right mult_assoc star3')
next
  show "star x * star (y * star x) \<le> star (x + y)"
    by (metis add_assoc add_est1 add_est2 add_left_commute less_star mult_mono'
      star_absorb_one star_absorb_one' star_idemp star_mono star_mult_idem zero_minimum)
qed

lemma ka22: "y * star x \<le> star x * star y \<Longrightarrow>  star y * star x \<le> star x * star y"
by (metis mult_assoc mult_right_mono plus_leI star3' star_mult_idem x_less_star zero_minimum)

lemma ka23: "star y * star x \<le> star x * star y \<Longrightarrow> y * star x \<le> star x * star y"
by (metis less_star mult_right_mono order_trans zero_minimum)

lemma ka24: "star (x + y) \<le> star (star x * star y)"
by (metis add_est1 add_est2 less_add(1) mult_assoc order_def plus_leI star_absorb_one star_mono star_slide2 star_unfold2 star_unfold_left x_less_star)

lemma ka25: "star y * star x \<le> star x * star y \<Longrightarrow> star (star y * star x) \<le> star x * star y"
-- {* Takes several minutes on my computer. *}
by (metis mult_assoc mult_right_mono order_trans star_idemp star_mult_idem star_simulation_leq_2 star_slide x_less_star zero_minimum)

lemma church_rosser: 
  "star y * star x \<le> star x * star y \<Longrightarrow> star (x + y) \<le> star x * star y"
by (metis add_commute ka24 ka25 order_trans)

lemma kleene_bubblesort: "y * x \<le> x * y \<Longrightarrow> star (x + y) \<le> star x * star y"
by (metis church_rosser star_simulation_leq_1 star_simulation_leq_2)

lemma ka27: "star (x + star y) = star (x + y)"
by (metis add_commute star_decomp star_idemp)

lemma ka28: "star (star x + star y) = star (x + y)"
by (metis add_commute ka27)

lemma ka29: "(y * (1 + x) \<le> (1 + x) * star y) = (y * x \<le> (1 + x) * star y)"
by (metis add_supremum left_distrib less_add(1) less_star mult.left_neutral mult.right_neutral order_trans right_distrib)

lemma ka30: "star x * star y \<le> star (x + y)"
by (metis mult_left_mono star_decomp star_mono x_less_star zero_minimum)

lemma simple_simulation: "x * y = 0 \<Longrightarrow> star x * y = y"
by (metis mult.right_neutral mult_zero_right star_simulation star_zero)

lemma ka32: "star (x * y) = 1 + x * star (y * x) * y"
by (metis mult_assoc star_slide star_unfold_left)

lemma ka33: "x * y + 1 \<le> y \<Longrightarrow> star x \<le> y"
by (metis add_commute mult.right_neutral star3')

end

subsection {* Complete lattices are Kleene algebras *}

lemma (in complete_lattice) le_SUPI':
  assumes "l \<le> M i"
  shows "l \<le> (SUP i. M i)"
  using assms by (rule order_trans) (rule le_SUPI [OF UNIV_I])

class kleene_by_complete_lattice = pre_kleene
  + complete_lattice + power + star +
  assumes star_cont: "a * star b * c = SUPR UNIV (\<lambda>n. a * b ^ n * c)"
begin

subclass kleene
proof
  fix a x :: 'a
  
  have [simp]: "1 \<le> star a"
    unfolding star_cont[of 1 a 1, simplified] 
    by (subst power_0[symmetric]) (rule le_SUPI [OF UNIV_I])
  
  show "1 + a * star a \<le> star a"
    apply (rule plus_leI, simp)
    apply (simp add:star_cont[of a a 1, simplified])
    apply (simp add:star_cont[of 1 a 1, simplified])
    apply (subst power_Suc[symmetric])
    by (intro SUP_leI le_SUPI UNIV_I)

  show "1 + star a * a \<le> star a" 
    apply (rule plus_leI, simp)
    apply (simp add:star_cont[of 1 a a, simplified])
    apply (simp add:star_cont[of 1 a 1, simplified])
    by (auto intro: SUP_leI le_SUPI simp add: power_Suc[symmetric] power_commutes simp del: power_Suc)

  show "a * x \<le> x \<Longrightarrow> star a * x \<le> x"
  proof -
    assume a: "a * x \<le> x"

    {
      fix n
      have "a ^ (Suc n) * x \<le> a ^ n * x"
      proof (induct n)
        case 0 thus ?case by (simp add: a)
      next
        case (Suc n)
        hence "a * (a ^ Suc n * x) \<le> a * (a ^ n * x)"
          by (auto intro: mult_mono)
        thus ?case
          by (simp add: mult_assoc)
      qed
    }
    note a = this
    
    {
      fix n have "a ^ n * x \<le> x"
      proof (induct n)
        case 0 show ?case by simp
      next
        case (Suc n) with a[of n]
        show ?case by simp
      qed
    }
    note b = this
    
    show "star a * x \<le> x"
      unfolding star_cont[of 1 a x, simplified]
      by (rule SUP_leI) (rule b)
  qed

  show "x * a \<le> x \<Longrightarrow> x * star a \<le> x" (* symmetric *)
  proof -
    assume a: "x * a \<le> x"

    {
      fix n
      have "x * a ^ (Suc n) \<le> x * a ^ n"
      proof (induct n)
        case 0 thus ?case by (simp add: a)
      next
        case (Suc n)
        hence "(x * a ^ Suc n) * a  \<le> (x * a ^ n) * a"
          by (auto intro: mult_mono)
        thus ?case
          by (simp add: power_commutes mult_assoc)
      qed
    }
    note a = this
    
    {
      fix n have "x * a ^ n \<le> x"
      proof (induct n)
        case 0 show ?case by simp
      next
        case (Suc n) with a[of n]
        show ?case by simp
      qed
    }
    note b = this
    
    show "x * star a \<le> x"
      unfolding star_cont[of x a 1, simplified]
      by (rule SUP_leI) (rule b)
  qed
qed

end

subsection {* Transitive closure *}

context kleene
begin

definition
  tcl_def: "tcl x = star x * x"

lemma tcl_zero: "tcl 0 = 0"
unfolding tcl_def by simp

lemma tcl_unfold_right: "tcl a = a + tcl a * a"
by (metis star_slide2 star_unfold2 tcl_def)

lemma less_tcl: "a \<le> tcl a"
by (metis star_slide2 tcl_def x_less_star)

end

subsection {* A naive algorithm to generate the transitive closure *}

function (default "\<lambda>x. 0", tailrec, domintros)
  mk_tcl :: "('a::{plus,times,ord,zero}) \<Rightarrow> 'a \<Rightarrow> 'a"
where
  "mk_tcl A X = (if X * A \<le> X then X else mk_tcl A (X + X * A))"
  by pat_completeness simp

declare mk_tcl.simps[simp del] (* loops *)

lemma mk_tcl_code[code]:
  "mk_tcl A X = 
  (let XA = X * A 
  in if XA \<le> X then X else mk_tcl A (X + XA))"
  unfolding mk_tcl.simps[of A X] Let_def ..

context kleene
begin

lemma mk_tcl_lemma1: "(X + X * A) * star A = X * star A"
by (metis ka1 left_distrib mult_assoc mult_left_mono ord_simp2 zero_minimum)

lemma mk_tcl_lemma2: "X * A \<le> X \<Longrightarrow> X * star A = X"
by (rule antisym) (auto simp: star4)

end

lemma mk_tcl_correctness:
  fixes X :: "'a::kleene"
  assumes "mk_tcl_dom (A, X)"
  shows "mk_tcl A X = X * star A"
  using assms
  by induct (auto simp: mk_tcl_lemma1 mk_tcl_lemma2)

lemma graph_implies_dom: "mk_tcl_graph x y \<Longrightarrow> mk_tcl_dom x"
  by (rule mk_tcl_graph.induct) (auto intro:accp.accI elim:mk_tcl_rel.cases)

lemma mk_tcl_default: "\<not> mk_tcl_dom (a,x) \<Longrightarrow> mk_tcl a x = 0"
  unfolding mk_tcl_def
  by (rule fundef_default_value[OF mk_tcl_sumC_def graph_implies_dom])

text {* We can replace the dom-Condition of the correctness theorem 
  with something executable: *}

lemma mk_tcl_correctness2:
  fixes A X :: "'a :: {kleene}"
  assumes "mk_tcl A A \<noteq> 0"
  shows "mk_tcl A A = tcl A"
  using assms mk_tcl_default mk_tcl_correctness
  unfolding tcl_def 
  by auto

end
