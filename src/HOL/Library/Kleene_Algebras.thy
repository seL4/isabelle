(*  Title:      HOL/Library/Kleene_Algebras.thy
    ID:         $Id$
    Author:     Alexander Krauss, TU Muenchen
*)

theory Kleene_Algebras
imports Main 
begin

text {* A type class of kleene algebras *}

class star = 
  fixes star :: "'a \<Rightarrow> 'a"

axclass idem_add \<subseteq> ab_semigroup_add
  add_idem[simp]: "x + x = x"

lemma add_idem2[simp]: "(x::'a::idem_add) + (x + y) = x + y"
  unfolding add_assoc[symmetric]
  by simp

axclass order_by_add \<subseteq> idem_add, ord
  order_def: "a \<le> b \<longleftrightarrow> a + b = b"
  strict_order_def: "a < b \<longleftrightarrow> a \<le> b \<and> a \<noteq> b"

lemma ord_simp1[simp]: "(x::'a::order_by_add) \<le> y \<Longrightarrow> x + y = y"
  unfolding order_def .
lemma ord_simp2[simp]: "(x::'a::order_by_add) \<le> y \<Longrightarrow> y + x = y"
  unfolding order_def add_commute .
lemma ord_intro: "(x::'a::order_by_add) + y = y \<Longrightarrow> x \<le> y"
  unfolding order_def .

instance order_by_add \<subseteq> order
proof
  fix x y z :: 'a
  show "x \<le> x" unfolding order_def by simp

  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z"
  proof (rule ord_intro)
    assume "x \<le> y" "y \<le> z"

    have "x + z = x + y + z" by (simp add:`y \<le> z` add_assoc)
    also have "\<dots> = y + z" by (simp add:`x \<le> y`)
    also have "\<dots> = z" by (simp add:`y \<le> z`)
    finally show "x + z = z" .
  qed

  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y" unfolding order_def
    by (simp add:add_commute)
  show "x < y \<longleftrightarrow> x \<le> y \<and> x \<noteq> y" by (fact strict_order_def)
qed


axclass pre_kleene \<subseteq> semiring_1, order_by_add

instance pre_kleene \<subseteq> pordered_semiring
proof
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

axclass kleene \<subseteq> pre_kleene, star
  star1: "1 + a * star a \<le> star a"
  star2: "1 + star a * a \<le> star a"
  star3: "a * x \<le> x \<Longrightarrow> star a * x \<le> x"
  star4: "x * a \<le> x \<Longrightarrow> x * star a \<le> x"

axclass kleene_by_comp_lat \<subseteq> 
  pre_kleene, comp_lat, recpower, star

  star_cont: "a * star b * c = (SUP n. a * b ^ n * c)"


lemma plus_leI: 
  fixes x :: "'a :: order_by_add"
  shows "x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x + y \<le> z"
  unfolding order_def by (simp add:add_assoc)




lemma le_SUPI':
  fixes l :: "'a :: comp_lat"
  assumes "l \<le> M i"
  shows "l \<le> (SUP i. M i)"
  using prems
  by (rule order_trans) (rule le_SUPI, rule refl)


lemma zero_minimum[simp]: "(0::'a::pre_kleene) \<le> x"
  unfolding order_def by simp

instance kleene_by_comp_lat \<subseteq> kleene
proof

  fix a x :: 'a
  
  have [simp]: "1 \<le> star a"
    unfolding star_cont[of 1 a 1, simplified] 
    by (rule le_SUPI) (rule power_0[symmetric])
  
  show "1 + a * star a \<le> star a" 
    apply (rule plus_leI, simp)
    apply (simp add:star_cont[of a a 1, simplified])
    apply (simp add:star_cont[of 1 a 1, simplified])
    apply (intro SUP_leI le_SUPI)
    by (rule power_Suc[symmetric])

  show "1 + star a * a \<le> star a" 
    apply (rule plus_leI, simp)
    apply (simp add:star_cont[of 1 a a, simplified])
    apply (simp add:star_cont[of 1 a 1, simplified])
    apply (intro SUP_leI le_SUPI)
    by (simp add:power_Suc[symmetric] power_commutes)

  show "a * x \<le> x \<Longrightarrow> star a * x \<le> x"
  proof -
    assume a: "a * x \<le> x"

    {
      fix n
      have "a ^ (Suc n) * x \<le> a ^ n * x"
      proof (induct n)
        case 0 thus ?case by (simp add:a power_Suc)
      next
        case (Suc n)
        hence "a * (a ^ Suc n * x) \<le> a * (a ^ n * x)"
          by (auto intro: mult_mono)
        thus ?case
          by (simp add:power_Suc mult_assoc)
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
        case 0 thus ?case by (simp add:a power_Suc)
      next
        case (Suc n)
        hence "(x * a ^ Suc n) * a  \<le> (x * a ^ n) * a"
          by (auto intro: mult_mono)
        thus ?case
          by (simp add:power_Suc power_commutes mult_assoc)
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

lemma less_add[simp]:  
  fixes a b :: "'a :: order_by_add"
  shows "a \<le> a + b"
  and "b \<le> a + b"
  unfolding order_def 
  by (auto simp:add_ac)

lemma add_est1:
  fixes a b c :: "'a :: order_by_add"
  assumes a: "a + b \<le> c"
  shows "a \<le> c"
  using less_add(1) a
  by (rule order_trans)

lemma add_est2:
  fixes a b c :: "'a :: order_by_add"
  assumes a: "a + b \<le> c"
  shows "b \<le> c"
  using less_add(2) a
  by (rule order_trans)


lemma star3':
  fixes a b x :: "'a :: kleene"
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
  fixes a b x :: "'a :: kleene"
  assumes a: "b + x * a \<le> x"
  shows "b * star a \<le> x"
proof (rule order_trans)
  from a have "b \<le> x" by (rule add_est1)
  show "b * star a \<le> x * star a"
    by (rule mult_mono) (auto simp:`b \<le> x`)

  from a have "x * a \<le> x" by (rule add_est2)
  with star4 show "x * star a \<le> x" .
qed


lemma star_mono:
  fixes x y :: "'a :: kleene"
  assumes "x \<le> y"
  shows "star x \<le> star y"
  oops

lemma star_idemp:
  fixes x :: "'a :: kleene"
  shows "star (star x) = star x"
  oops

lemma zero_star[simp]:
  shows "star (0::'a::kleene) = 1"
  oops


lemma star_unfold_left:
  fixes a :: "'a :: kleene"
  shows "1 + a * star a = star a"
proof (rule order_antisym, rule star1)

  have "1 + a * (1 + a * star a) \<le> 1 + a * star a"
    apply (rule add_mono, rule)
    apply (rule mult_mono, auto)
    apply (rule star1)
    done

  with star3' have "star a * 1 \<le> 1 + a * star a" .
  thus "star a \<le> 1 + a * star a" by simp
qed


lemma star_unfold_right:  
  fixes a :: "'a :: kleene"
  shows "1 + star a * a = star a"
proof (rule order_antisym, rule star2)

  have "1 + (1 + star a * a) * a \<le> 1 + star a * a"
    apply (rule add_mono, rule)
    apply (rule mult_mono, auto)
    apply (rule star2)
    done

  with star4' have "1 * star a \<le> 1 + star a * a" .
  thus "star a \<le> 1 + star a * a" by simp
qed



lemma star_commute:
  fixes a b x :: "'a :: kleene"
  assumes a: "a * x = x * b"
  shows "star a * x = x * star b"
proof (rule order_antisym)

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



lemma star_assoc:
  fixes c d :: "'a :: kleene"
  shows "star (c * d) * c = c * star (d * c)"
  oops

lemma star_dist:
  fixes a b :: "'a :: kleene"
  shows "star (a + b) = star a * star (b * star a)"
  oops

lemma star_one:
  fixes a p p' :: "'a :: kleene"
  assumes "p * p' = 1" and "p' * p = 1"
  shows "p' * star a * p = star (p' * a * p)"
  oops


lemma star_zero: 
  "star (0::'a::kleene) = 1"
  by (rule star_unfold_left[of 0, simplified])


(* Own lemmas *)


lemma x_less_star[simp]: 
  fixes x :: "'a :: kleene"
  shows "x \<le> x * star a"
proof -
  have "x \<le> x * (1 + a * star a)" by (simp add:right_distrib)
  also have "\<dots> = x * star a" by (simp only: star_unfold_left)
  finally show ?thesis .
qed

subsection {* Transitive Closure *}

definition 
  "tcl (x::'a::kleene) = star x * x"


lemma tcl_zero: 
  "tcl (0::'a::kleene) = 0"
  unfolding tcl_def by simp


subsection {* Naive Algorithm to generate the transitive closure *}

function (default "\<lambda>x. 0", tailrec)
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

lemma mk_tcl_lemma1:
  fixes X :: "'a :: kleene"
  shows "(X + X * A) * star A = X * star A"
proof -
  have "A * star A \<le> 1 + A * star A" by simp
  also have "\<dots> = star A" by (simp add:star_unfold_left)
  finally have "star A + A * star A = star A" by simp
  hence "X * (star A + A * star A) = X * star A" by simp
  thus ?thesis by (simp add:left_distrib right_distrib mult_ac)
qed

lemma mk_tcl_lemma2:
  fixes X :: "'a :: kleene"
  shows "X * A \<le> X \<Longrightarrow> X * star A = X"
  by (rule order_antisym) (auto simp:star4)




lemma mk_tcl_correctness:
  fixes A X :: "'a :: {kleene}"
  assumes "mk_tcl_dom (A, X)"
  shows "mk_tcl A X = X * star A"
  using prems
  by induct (auto simp:mk_tcl_lemma1 mk_tcl_lemma2)

lemma graph_implies_dom: "mk_tcl_graph x y \<Longrightarrow> mk_tcl_dom x"
  by (rule mk_tcl_graph.induct) (auto intro:accI elim:mk_tcl_rel.cases)

lemma mk_tcl_default: "\<not> mk_tcl_dom (a,x) \<Longrightarrow> mk_tcl a x = 0"
  unfolding mk_tcl_def
  by (rule fundef_default_value[OF mk_tcl_sum_def graph_implies_dom])


text {* We can replace the dom-Condition of the correctness theorem 
  with something executable *}

lemma mk_tcl_correctness2:
  fixes A X :: "'a :: {kleene}"
  assumes "mk_tcl A A \<noteq> 0"
  shows "mk_tcl A A = tcl A"
  using prems mk_tcl_default mk_tcl_correctness
  unfolding tcl_def 
  by (auto simp:star_commute)





end














