(*  Title:      HOL/Library/Kleene_Algebras.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen
*)

header "Kleene Algebras"

theory Kleene_Algebras
imports Main 
begin

text {* A type class of Kleene algebras *}

class star =
  fixes star :: "'a \<Rightarrow> 'a"

class idem_add = ab_semigroup_add +
  assumes add_idem [simp]: "x + x = x"
begin

lemma add_idem2[simp]: "(x::'a) + (x + y) = x + y"
unfolding add_assoc[symmetric] by simp

end

class order_by_add = idem_add + ord +
  assumes order_def: "a \<le> b \<longleftrightarrow> a + b = b"
  assumes strict_order_def: "a < b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"
begin

lemma ord_simp1[simp]: "x \<le> y \<Longrightarrow> x + y = y"
  unfolding order_def .

lemma ord_simp2[simp]: "x \<le> y \<Longrightarrow> y + x = y"
  unfolding order_def add_commute .

lemma ord_intro: "x + y = y \<Longrightarrow> x \<le> y"
  unfolding order_def .

subclass order proof
  fix x y z :: 'a
  show "x \<le> x" unfolding order_def by simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
  proof (rule ord_intro)
    assume "x \<le> y" "y \<le> z"
    have "x + z = x + y + z" by (simp add:`y \<le> z` add_assoc)
    also have "\<dots> = y + z" by (simp add:`x \<le> y`)
    also have "\<dots> = z" by (simp add:`y \<le> z`)
    finally show "x + z = z" .
  qed
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding order_def
    by (simp add: add_commute)
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (fact strict_order_def)
qed

lemma plus_leI: 
  "x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x + y \<le> z"
  unfolding order_def by (simp add: add_assoc)

lemma less_add[simp]: "a \<le> a + b" "b \<le> a + b"
unfolding order_def by (auto simp:add_ac)

lemma add_est1: "a + b \<le> c \<Longrightarrow> a \<le> c"
using less_add(1) by (rule order_trans)

lemma add_est2: "a + b \<le> c \<Longrightarrow> b \<le> c"
using less_add(2) by (rule order_trans)

end

class pre_kleene = semiring_1 + order_by_add
begin

subclass pordered_semiring proof
  fix x y z :: 'a

  assume "x \<le> y"
   
  show "z + x \<le> z + y"
  proof (rule ord_intro)
    have "z + x + (z + y) = x + y + z" by (simp add:add_ac)
    also have "\<dots> = z + y" by (simp add:`x \<le> y` add_ac)
    finally show "z + x + (z + y) = z + y" .
  qed

  show "z * x \<le> z * y"
  proof (rule ord_intro)
    from `x \<le> y` have "z * (x + y) = z * y" by simp
    thus "z * x + z * y = z * y" by (simp add:right_distrib)
  qed

  show "x * z \<le> y * z"
  proof (rule ord_intro)
    from `x \<le> y` have "(x + y) * z = y * z" by simp
    thus "x * z + y * z = y * z" by (simp add:left_distrib)
  qed
qed

lemma zero_minimum [simp]: "0 \<le> x"
  unfolding order_def by simp

end

class kleene = pre_kleene + star +
  assumes star1: "1 + a * star a \<le> star a"
  and star2: "1 + star a * a \<le> star a"
  and star3: "a * x \<le> x \<Longrightarrow> star a * x \<le> x"
  and star4: "x * a \<le> x \<Longrightarrow> x * star a \<le> x"
begin

lemma star3':
  assumes a: "b + a * x \<le> x"
  shows "star a * b \<le> x"
proof (rule order_trans)
  from a have "b \<le> x" by (rule add_est1)
  show "star a * b \<le> star a * x"
    by (rule mult_mono) (auto simp:`b \<le> x`)

  from a have "a * x \<le> x" by (rule add_est2)
  with star3 show "star a * x \<le> x" .
qed

lemma star4':
  assumes a: "b + x * a \<le> x"
  shows "b * star a \<le> x"
proof (rule order_trans)
  from a have "b \<le> x" by (rule add_est1)
  show "b * star a \<le> x * star a"
    by (rule mult_mono) (auto simp:`b \<le> x`)

  from a have "x * a \<le> x" by (rule add_est2)
  with star4 show "x * star a \<le> x" .
qed

lemma star_unfold_left:
  shows "1 + a * star a = star a"
proof (rule antisym, rule star1)
  have "1 + a * (1 + a * star a) \<le> 1 + a * star a"
    apply (rule add_mono, rule)
    apply (rule mult_mono, auto)
    apply (rule star1)
    done
  with star3' have "star a * 1 \<le> 1 + a * star a" .
  thus "star a \<le> 1 + a * star a" by simp
qed

lemma star_unfold_right: "1 + star a * a = star a"
proof (rule antisym, rule star2)
  have "1 + (1 + star a * a) * a \<le> 1 + star a * a"
    apply (rule add_mono, rule)
    apply (rule mult_mono, auto)
    apply (rule star2)
    done
  with star4' have "1 * star a \<le> 1 + star a * a" .
  thus "star a \<le> 1 + star a * a" by simp
qed

lemma star_zero[simp]: "star 0 = 1"
by (fact star_unfold_left[of 0, simplified, symmetric])

lemma star_one[simp]: "star 1 = 1"
by (metis add_idem2 eq_iff mult_1_right ord_simp2 star3 star_unfold_left)

lemma one_less_star: "1 \<le> star x"
by (metis less_add(1) star_unfold_left)

lemma ka1: "x * star x \<le> star x"
by (metis less_add(2) star_unfold_left)

lemma star_mult_idem[simp]: "star x * star x = star x"
by (metis add_commute add_est1 eq_iff mult_1_right right_distrib star3 star_unfold_left)

lemma less_star: "x \<le> star x"
by (metis less_add(2) mult_1_right mult_left_mono one_less_star order_trans star_unfold_left zero_minimum)

lemma star_simulation:
  assumes a: "a * x = x * b"
  shows "star a * x = x * star b"
proof (rule antisym)
  show "star a * x \<le> x * star b"
  proof (rule star3', rule order_trans)
    from a have "a * x \<le> x * b" by simp
    hence "a * x * star b \<le> x * b * star b"
      by (rule mult_mono) auto
    thus "x + a * (x * star b) \<le> x + x * b * star b"
      using add_mono by (auto simp: mult_assoc)
    show "\<dots> \<le> x * star b"
    proof -
      have "x * (1 + b * star b) \<le> x * star b"
        by (rule mult_mono[OF _ star1]) auto
      thus ?thesis
        by (simp add:right_distrib mult_assoc)
    qed
  qed
  show "x * star b \<le> star a * x"
  proof (rule star4', rule order_trans)
    from a have b: "x * b \<le> a * x" by simp
    have "star a * x * b \<le> star a * a * x"
      unfolding mult_assoc
      by (rule mult_mono[OF _ b]) auto
    thus "x + star a * x * b \<le> x + star a * a * x"
      using add_mono by auto
    show "\<dots> \<le> star a * x"
    proof -
      have "(1 + star a * a) * x \<le> star a * x"
        by (rule mult_mono[OF star2]) auto
      thus ?thesis
        by (simp add:left_distrib mult_assoc)
    qed
  qed
qed

lemma star_slide2[simp]: "star x * x = x * star x"
by (metis star_simulation)

lemma star_idemp[simp]: "star (star x) = star x"
by (metis add_idem2 eq_iff less_star mult_1_right star3' star_mult_idem star_unfold_left)

lemma star_slide[simp]: "star (x * y) * x = x * star (y * x)"
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

lemma x_less_star[simp]: "x \<le> x * star a"
proof -
  have "x \<le> x * (1 + a * star a)" by (simp add: right_distrib)
  also have "\<dots> = x * star a" by (simp only: star_unfold_left)
  finally show ?thesis .
qed

lemma star_mono:  "x \<le> y \<Longrightarrow>  star x \<le> star y"
by (metis add_commute eq_iff less_star ord_simp2 order_trans star3 star4' star_idemp star_mult_idem x_less_star)

lemma star_sub: "x \<le> 1 \<Longrightarrow> star x = 1"
by (metis add_commute ord_simp1 star_idemp star_mono star_mult_idem star_one star_unfold_left)

lemma star_unfold2: "star x * y = y + x * star x * y"
by (subst star_unfold_right[symmetric]) (simp add: mult_assoc left_distrib)

lemma star_absorb_one[simp]: "star (x + 1) = star x"
by (metis add_commute eq_iff left_distrib less_add(1) less_add(2) mult_1_left mult_assoc star3 star_mono star_mult_idem star_unfold2 x_less_star)

lemma star_absorb_one'[simp]: "star (1 + x) = star x"
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

lemma kleene_church_rosser: 
  "star y * star x \<le> star x * star y \<Longrightarrow> star (x + y) \<le> star x * star y"
oops

lemma star_decomp: "star (a + b) = star a * star (b * star a)"
oops

lemma ka22: "y * star x \<le> star x * star y \<Longrightarrow>  star y * star x \<le> star x * star y"
by (metis mult_assoc mult_right_mono plus_leI star3' star_mult_idem x_less_star zero_minimum)

lemma ka23: "star y * star x \<le> star x * star y \<Longrightarrow> y * star x \<le> star x * star y"
by (metis less_star mult_right_mono order_trans zero_minimum)

lemma ka24: "star (x + y) \<le> star (star x * star y)"
by (metis add_est1 add_est2 less_add(1) mult_assoc order_def plus_leI star_absorb_one star_mono star_slide2 star_unfold2 star_unfold_left x_less_star)

lemma ka25: "star y * star x \<le> star x * star y \<Longrightarrow> star (star y * star x) \<le> star x * star y"
oops

lemma kleene_bubblesort: "y * x \<le> x * y \<Longrightarrow> star (x + y) \<le> star x * star y"
oops

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


subsection {* Transitive Closure *}

context kleene
begin

definition 
  tcl_def:  "tcl x = star x * x"

lemma tcl_zero: "tcl 0 = 0"
unfolding tcl_def by simp

lemma tcl_unfold_right: "tcl a = a + tcl a * a"
proof -
  from star_unfold_right[of a]
  have "a * (1 + star a * a) = a * star a" by simp
  from this[simplified right_distrib, simplified]
  show ?thesis
    by (simp add:tcl_def mult_assoc)
qed

lemma less_tcl: "a \<le> tcl a"
proof -
  have "a \<le> a + tcl a * a" by simp
  also have "\<dots> = tcl a" by (rule tcl_unfold_right[symmetric])
  finally show ?thesis .
qed

end


subsection {* Naive Algorithm to generate the transitive closure *}

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

lemma mk_tcl_lemma1:
  "(X + X * A) * star A = X * star A"
proof -
  have "A * star A \<le> 1 + A * star A" by simp
  also have "\<dots> = star A" by (simp add:star_unfold_left)
  finally have "star A + A * star A = star A" by simp
  hence "X * (star A + A * star A) = X * star A" by simp
  thus ?thesis by (simp add:left_distrib right_distrib mult_assoc)
qed

lemma mk_tcl_lemma2:
  shows "X * A \<le> X \<Longrightarrow> X * star A = X"
  by (rule antisym) (auto simp:star4)

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
  with something executable *}

lemma mk_tcl_correctness2:
  fixes A X :: "'a :: {kleene}"
  assumes "mk_tcl A A \<noteq> 0"
  shows "mk_tcl A A = tcl A"
  using assms mk_tcl_default mk_tcl_correctness
  unfolding tcl_def 
  by auto

end
