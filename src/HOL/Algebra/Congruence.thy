(*  Title:      HOL/Algebra/Congruence.thy
    Author:     Clemens Ballarin, started 3 January 2008
    with thanks to Paulo Emílio de Vilhena
*)

theory Congruence
  imports
    Main
    "HOL-Library.FuncSet"
begin

section \<open>Objects\<close>

subsection \<open>Structure with Carrier Set.\<close>

record 'a partial_object =
  carrier :: "'a set"

lemma funcset_carrier:
  "\<lbrakk> f \<in> carrier X \<rightarrow> carrier Y; x \<in> carrier X \<rbrakk> \<Longrightarrow> f x \<in> carrier Y"
  by (fact funcset_mem)

lemma funcset_carrier':
  "\<lbrakk> f \<in> carrier A \<rightarrow> carrier A; x \<in> carrier A \<rbrakk> \<Longrightarrow> f x \<in> carrier A"
  by (fact funcset_mem)


subsection \<open>Structure with Carrier and Equivalence Relation \<open>eq\<close>\<close>

record 'a eq_object = "'a partial_object" +
  eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl ".=\<index>" 50)

definition
  elem :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" (infixl ".\<in>\<index>" 50)
  where "x .\<in>\<^bsub>S\<^esub> A \<longleftrightarrow> (\<exists>y \<in> A. x .=\<^bsub>S\<^esub> y)"

definition
  set_eq :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "{.=}\<index>" 50)
  where "A {.=}\<^bsub>S\<^esub> B \<longleftrightarrow> ((\<forall>x \<in> A. x .\<in>\<^bsub>S\<^esub> B) \<and> (\<forall>x \<in> B. x .\<in>\<^bsub>S\<^esub> A))"

definition
  eq_class_of :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set" ("class'_of\<index>")
  where "class_of\<^bsub>S\<^esub> x = {y \<in> carrier S. x .=\<^bsub>S\<^esub> y}"

definition
  eq_closure_of :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set" ("closure'_of\<index>")
  where "closure_of\<^bsub>S\<^esub> A = {y \<in> carrier S. y .\<in>\<^bsub>S\<^esub> A}"

definition
  eq_is_closed :: "_ \<Rightarrow> 'a set \<Rightarrow> bool" ("is'_closed\<index>")
  where "is_closed\<^bsub>S\<^esub> A \<longleftrightarrow> A \<subseteq> carrier S \<and> closure_of\<^bsub>S\<^esub> A = A"

abbreviation
  not_eq :: "_ \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl ".\<noteq>\<index>" 50)
  where "x .\<noteq>\<^bsub>S\<^esub> y \<equiv> \<not>(x .=\<^bsub>S\<^esub> y)"

abbreviation
  not_elem :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" (infixl ".\<notin>\<index>" 50)
  where "x .\<notin>\<^bsub>S\<^esub> A \<equiv> \<not>(x .\<in>\<^bsub>S\<^esub> A)"

abbreviation
  set_not_eq :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "{.\<noteq>}\<index>" 50)
  where "A {.\<noteq>}\<^bsub>S\<^esub> B \<equiv> \<not>(A {.=}\<^bsub>S\<^esub> B)"

locale equivalence =
  fixes S (structure)
  assumes refl [simp, intro]: "x \<in> carrier S \<Longrightarrow> x .= x"
    and sym [sym]: "\<lbrakk> x .= y; x \<in> carrier S; y \<in> carrier S \<rbrakk> \<Longrightarrow> y .= x"
    and trans [trans]:
      "\<lbrakk> x .= y; y .= z; x \<in> carrier S; y \<in> carrier S; z \<in> carrier S \<rbrakk> \<Longrightarrow> x .= z"

(* Lemmas by Stephan Hohe *)

lemma elemI:
  fixes R (structure)
  assumes "a' \<in> A" and "a .= a'"
  shows "a .\<in> A"
unfolding elem_def
using assms
by fast

lemma (in equivalence) elem_exact:
  assumes "a \<in> carrier S" and "a \<in> A"
  shows "a .\<in> A"
using assms
by (fast intro: elemI)

lemma elemE:
  fixes S (structure)
  assumes "a .\<in> A"
    and "\<And>a'. \<lbrakk>a' \<in> A; a .= a'\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms
unfolding elem_def
by fast

lemma (in equivalence) elem_cong_l [trans]:
  assumes cong: "a' .= a"
    and a: "a .\<in> A"
    and carr: "a \<in> carrier S"  "a' \<in> carrier S"
    and Acarr: "A \<subseteq> carrier S"
  shows "a' .\<in> A"
using a
apply (elim elemE, intro elemI)
proof assumption
  fix b
  assume bA: "b \<in> A"
  note [simp] = carr bA[THEN subsetD[OF Acarr]]
  note cong
  also assume "a .= b"
  finally show "a' .= b" by simp
qed

lemma (in equivalence) elem_subsetD:
  assumes "A \<subseteq> B"
    and aA: "a .\<in> A"
  shows "a .\<in> B"
using assms
by (fast intro: elemI elim: elemE dest: subsetD)

lemma (in equivalence) mem_imp_elem [simp, intro]:
  "\<lbrakk> x \<in> A; x \<in> carrier S \<rbrakk> \<Longrightarrow> x .\<in> A"
  unfolding elem_def by blast

lemma set_eqI:
  fixes R (structure)
  assumes ltr: "\<And>a. a \<in> A \<Longrightarrow> a .\<in> B"
    and rtl: "\<And>b. b \<in> B \<Longrightarrow> b .\<in> A"
  shows "A {.=} B"
unfolding set_eq_def
by (fast intro: ltr rtl)

lemma set_eqI2:
  fixes R (structure)
  assumes ltr: "\<And>a b. a \<in> A \<Longrightarrow> \<exists>b\<in>B. a .= b"
    and rtl: "\<And>b. b \<in> B \<Longrightarrow> \<exists>a\<in>A. b .= a"
  shows "A {.=} B"
  by (intro set_eqI, unfold elem_def) (fast intro: ltr rtl)+

lemma set_eqD1:
  fixes R (structure)
  assumes AA': "A {.=} A'"
    and "a \<in> A"
  shows "\<exists>a'\<in>A'. a .= a'"
using assms
unfolding set_eq_def elem_def
by fast

lemma set_eqD2:
  fixes R (structure)
  assumes AA': "A {.=} A'"
    and "a' \<in> A'"
  shows "\<exists>a\<in>A. a' .= a"
using assms
unfolding set_eq_def elem_def
by fast

lemma set_eqE:
  fixes R (structure)
  assumes AB: "A {.=} B"
    and r: "\<lbrakk>\<forall>a\<in>A. a .\<in> B; \<forall>b\<in>B. b .\<in> A\<rbrakk> \<Longrightarrow> P"
  shows "P"
using AB
unfolding set_eq_def
by (blast dest: r)

lemma set_eqE2:
  fixes R (structure)
  assumes AB: "A {.=} B"
    and r: "\<lbrakk>\<forall>a\<in>A. (\<exists>b\<in>B. a .= b); \<forall>b\<in>B. (\<exists>a\<in>A. b .= a)\<rbrakk> \<Longrightarrow> P"
  shows "P"
using AB
unfolding set_eq_def elem_def
by (blast dest: r)

lemma set_eqE':
  fixes R (structure)
  assumes AB: "A {.=} B"
    and aA: "a \<in> A" and bB: "b \<in> B"
    and r: "\<And>a' b'. \<lbrakk>a' \<in> A; b .= a'; b' \<in> B; a .= b'\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from AB aA
      have "\<exists>b'\<in>B. a .= b'" by (rule set_eqD1)
  from this obtain b'
      where b': "b' \<in> B" "a .= b'" by auto

  from AB bB
      have "\<exists>a'\<in>A. b .= a'" by (rule set_eqD2)
  from this obtain a'
      where a': "a' \<in> A" "b .= a'" by auto

  from a' b'
      show "P" by (rule r)
qed

lemma (in equivalence) eq_elem_cong_r [trans]:
  assumes a: "a .\<in> A"
    and cong: "A {.=} A'"
    and carr: "a \<in> carrier S"
    and Carr: "A \<subseteq> carrier S" "A' \<subseteq> carrier S"
  shows "a .\<in> A'"
using a cong
proof (elim elemE set_eqE)
  fix b
  assume bA: "b \<in> A"
     and inA': "\<forall>b\<in>A. b .\<in> A'"
  note [simp] = carr Carr Carr[THEN subsetD] bA
  assume "a .= b"
  also from bA inA'
       have "b .\<in> A'" by fast
  finally
       show "a .\<in> A'" by simp
qed

lemma (in equivalence) set_eq_sym [sym]:
  assumes "A {.=} B"
  shows "B {.=} A"
using assms
unfolding set_eq_def elem_def
by fast

lemma (in equivalence) equal_set_eq_trans [trans]:
  assumes AB: "A = B" and BC: "B {.=} C"
  shows "A {.=} C"
  using AB BC by simp

lemma (in equivalence) set_eq_equal_trans [trans]:
  assumes AB: "A {.=} B" and BC: "B = C"
  shows "A {.=} C"
  using AB BC by simp

lemma (in equivalence) set_eq_trans [trans]:
  assumes AB: "A {.=} B" and BC: "B {.=} C"
    and carr: "A \<subseteq> carrier S"  "B \<subseteq> carrier S"  "C \<subseteq> carrier S"
  shows "A {.=} C"
proof (intro set_eqI)
  fix a
  assume aA: "a \<in> A"
  with carr have "a \<in> carrier S" by fast
  note [simp] = carr this

  from aA
       have "a .\<in> A" by (simp add: elem_exact)
  also note AB
  also note BC
  finally
       show "a .\<in> C" by simp
next
  fix c
  assume cC: "c \<in> C"
  with carr have "c \<in> carrier S" by fast
  note [simp] = carr this

  from cC
       have "c .\<in> C" by (simp add: elem_exact)
  also note BC[symmetric]
  also note AB[symmetric]
  finally
       show "c .\<in> A" by simp
qed

lemma (in equivalence) set_eq_insert_aux:
  assumes x: "x .= x'"
      and carr: "x \<in> carrier S" "x' \<in> carrier S" "A \<subseteq> carrier S"
    shows "\<forall>a \<in> (insert x A). a .\<in> (insert x' A)"
proof
  fix a
  show "a \<in> insert x A \<Longrightarrow> a .\<in> insert x' A"
  proof cases
    assume "a \<in> A"
    thus "a .\<in> insert x' A"
      using carr(3) by blast
  next
    assume "a \<in> insert x A" "a \<notin> A"
    hence "a = x"
      by blast
    thus "a .\<in> insert x' A"
      by (meson x elemI insertI1)
  qed
qed

lemma (in equivalence) set_eq_insert:
  assumes x: "x .= x'"
      and carr: "x \<in> carrier S" "x' \<in> carrier S" "A \<subseteq> carrier S"
    shows "insert x A {.=} insert x' A"
proof-
  have "(\<forall>a \<in> (insert x  A). a .\<in> (insert x' A)) \<and>
        (\<forall>a \<in> (insert x' A). a .\<in> (insert x  A))"
    using set_eq_insert_aux carr x sym by blast
  thus "insert x A {.=} insert x' A"
    using set_eq_def by blast
qed  

lemma (in equivalence) set_eq_pairI:
  assumes xx': "x .= x'"
    and carr: "x \<in> carrier S" "x' \<in> carrier S" "y \<in> carrier S"
  shows "{x, y} {.=} {x', y}"
  using assms set_eq_insert by simp

lemma (in equivalence) is_closedI:
  assumes closed: "\<And>x y. \<lbrakk>x .= y; x \<in> A; y \<in> carrier S\<rbrakk> \<Longrightarrow> y \<in> A"
    and S: "A \<subseteq> carrier S"
  shows "is_closed A"
  unfolding eq_is_closed_def eq_closure_of_def elem_def
  using S
  by (blast dest: closed sym)

lemma (in equivalence) closure_of_eq:
  "\<lbrakk>x .= x'; A \<subseteq> carrier S; x \<in> closure_of A; x' \<in> carrier S\<rbrakk> \<Longrightarrow> x' \<in> closure_of A"
  unfolding eq_closure_of_def elem_def
  by (blast intro: trans sym)

lemma (in equivalence) is_closed_eq [dest]:
  "\<lbrakk>x .= x'; x \<in> A; is_closed A; x \<in> carrier S; x' \<in> carrier S\<rbrakk> \<Longrightarrow> x' \<in> A"
  unfolding eq_is_closed_def
  using closure_of_eq [where A = A]
  by simp

lemma (in equivalence) is_closed_eq_rev [dest]:
  "\<lbrakk>x .= x'; x' \<in> A; is_closed A; x \<in> carrier S; x' \<in> carrier S\<rbrakk> \<Longrightarrow> x \<in> A"
  by (meson subsetD eq_is_closed_def is_closed_eq sym)

lemma closure_of_closed [simp, intro]:
  fixes S (structure)
  shows "closure_of A \<subseteq> carrier S"
unfolding eq_closure_of_def
by fast

lemma closure_of_memI:
  fixes S (structure)
  assumes "a .\<in> A" and "a \<in> carrier S"
  shows "a \<in> closure_of A"
  by (simp add: assms eq_closure_of_def)

lemma closure_ofI2:
  fixes S (structure)
  assumes "a .= a'" and "a' \<in> A" and "a \<in> carrier S"
  shows "a \<in> closure_of A"
  by (meson assms closure_of_memI elem_def)

lemma closure_of_memE:
  fixes S (structure)
  assumes "a \<in> closure_of A"
    and "\<lbrakk>a \<in> carrier S; a .\<in> A\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using eq_closure_of_def assms by fastforce

lemma closure_ofE2:
  fixes S (structure)
  assumes "a \<in> closure_of A"
    and "\<And>a'. \<lbrakk>a \<in> carrier S; a' \<in> A; a .= a'\<rbrakk> \<Longrightarrow> P"
  shows "P"
  by (meson closure_of_memE elemE assms)

lemma (in equivalence) closure_inclusion:
  assumes "A \<subseteq> B"
  shows "closure_of A \<subseteq> closure_of B"
  unfolding eq_closure_of_def
proof
  fix x
  assume "x \<in> {y \<in> carrier S. y .\<in> A}"
  hence "x \<in> carrier S \<and> x .\<in> A"
    by blast
  hence "x \<in> carrier S \<and> x .\<in> B"
    using assms elem_subsetD by blast
  thus "x \<in> {y \<in> carrier S. y .\<in> B}"
    by simp
qed

lemma (in equivalence) classes_small:
  assumes "is_closed B"
    and "A \<subseteq> B"
  shows "closure_of A \<subseteq> B"
proof-
  have "closure_of A \<subseteq> closure_of B"
    using closure_inclusion assms by simp
  thus "closure_of A \<subseteq> B"
    using assms(1) eq_is_closed_def by fastforce
qed

lemma (in equivalence) classes_eq:
  assumes "A \<subseteq> carrier S"
  shows "A {.=} closure_of A"
using assms
by (blast intro: set_eqI elem_exact closure_of_memI elim: closure_of_memE)

lemma (in equivalence) complete_classes:
  assumes c: "is_closed A"
  shows "A = closure_of A"
  using assms by (simp add: eq_is_closed_def)

lemma (in equivalence) closure_idemp_weak:
  "closure_of (closure_of A) {.=} closure_of A"
  by (simp add: classes_eq set_eq_sym)

lemma (in equivalence) closure_idemp_strong:
  assumes "A \<subseteq> carrier S"
  shows "closure_of (closure_of A) = closure_of A"
  using assms closure_of_eq complete_classes is_closedI by auto

lemma (in equivalence) complete_classes2:
  assumes "A \<subseteq> carrier S"
  shows "is_closed (closure_of A)"
  using closure_idemp_strong by (simp add: assms eq_is_closed_def)

lemma equivalence_subset:
  assumes "equivalence L" "A \<subseteq> carrier L"
  shows "equivalence (L\<lparr> carrier := A \<rparr>)"
proof -
  interpret L: equivalence L
    by (simp add: assms)
  show ?thesis
    by (unfold_locales, simp_all add: L.sym assms rev_subsetD, meson L.trans assms(2) contra_subsetD)
qed
  
end
