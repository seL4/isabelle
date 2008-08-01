(*
  Title:  Algebra/Congruence.thy
  Id:     $Id$
  Author: Clemens Ballarin, started 3 January 2008
  Copyright: Clemens Ballarin
*)

theory Congruence imports Main begin

section {* Objects *}

subsection {* Structure with Carrier Set. *}

record 'a partial_object =
  carrier :: "'a set"


subsection {* Structure with Carrier and Equivalence Relation @{text eq} *}

record 'a eq_object = "'a partial_object" +
  eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl ".=\<index>" 50)

constdefs (structure S)
  elem :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" (infixl ".\<in>\<index>" 50)
  "x .\<in> A \<equiv> (\<exists>y \<in> A. x .= y)"

  set_eq :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "{.=}\<index>" 50)
  "A {.=} B == ((\<forall>x \<in> A. x .\<in> B) \<and> (\<forall>x \<in> B. x .\<in> A))"

  eq_class_of :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set" ("class'_of\<index> _")
  "class_of x == {y \<in> carrier S. x .= y}"

  eq_closure_of :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set" ("closure'_of\<index> _")
  "closure_of A == {y \<in> carrier S. y .\<in> A}"

  eq_is_closed :: "_ \<Rightarrow> 'a set \<Rightarrow> bool" ("is'_closed\<index> _")
  "is_closed A == (A \<subseteq> carrier S \<and> closure_of A = A)"

syntax
  not_eq :: "_ \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" (infixl ".\<noteq>\<index>" 50)
  not_elem :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" (infixl ".\<notin>\<index>" 50)
  set_not_eq :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infixl "{.\<noteq>}\<index>" 50)

translations
  "x .\<noteq>\<index> y" == "~(x .=\<index> y)"
  "x .\<notin>\<index> A" == "~(x .\<in>\<index> A)"
  "A {.\<noteq>}\<index> B" == "~(A {.=}\<index> B)"

locale equivalence =
  fixes S (structure)
  assumes refl [simp, intro]: "x \<in> carrier S \<Longrightarrow> x .= x"
    and sym [sym]: "\<lbrakk> x .= y; x \<in> carrier S; y \<in> carrier S \<rbrakk> \<Longrightarrow> y .= x"
    and trans [trans]: "\<lbrakk> x .= y; y .= z; x \<in> carrier S; y \<in> carrier S; z \<in> carrier S \<rbrakk> \<Longrightarrow> x .= z"

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
  "[| x \<in> A; x \<in> carrier S |] ==> x .\<in> A"
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
    and "A \<subseteq> carrier S" "B \<subseteq> carrier S"
  shows "B {.=} A"
using assms
unfolding set_eq_def elem_def
by fast

(* FIXME: the following two required in Isabelle 2008, not Isabelle 2007 *)
(* alternatively, could declare lemmas [trans] = ssubst [where 'a = "'a set"] *)

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

(* FIXME: generalise for insert *)

(*
lemma (in equivalence) set_eq_insert:
  assumes x: "x .= x'"
    and carr: "x \<in> carrier S" "x' \<in> carrier S" "A \<subseteq> carrier S"
  shows "insert x A {.=} insert x' A"
  unfolding set_eq_def elem_def
apply rule
apply rule
apply (case_tac "xa = x")
using x apply fast
apply (subgoal_tac "xa \<in> A") prefer 2 apply fast
apply (rule_tac x=xa in bexI)
using carr apply (rule_tac refl) apply auto [1]
apply safe
*)

lemma (in equivalence) set_eq_pairI:
  assumes xx': "x .= x'"
    and carr: "x \<in> carrier S" "x' \<in> carrier S" "y \<in> carrier S"
  shows "{x, y} {.=} {x', y}"
unfolding set_eq_def elem_def
proof safe
  have "x' \<in> {x', y}" by fast
  with xx' show "\<exists>b\<in>{x', y}. x .= b" by fast
next
  have "y \<in> {x', y}" by fast
  with carr show "\<exists>b\<in>{x', y}. y .= b" by fast
next
  have "x \<in> {x, y}" by fast
  with xx'[symmetric] carr
  show "\<exists>a\<in>{x, y}. x' .= a" by fast
next
  have "y \<in> {x, y}" by fast
  with carr show "\<exists>a\<in>{x, y}. y .= a" by fast
qed

lemma (in equivalence) is_closedI:
  assumes closed: "!!x y. [| x .= y; x \<in> A; y \<in> carrier S |] ==> y \<in> A"
    and S: "A \<subseteq> carrier S"
  shows "is_closed A"
  unfolding eq_is_closed_def eq_closure_of_def elem_def
  using S
  by (blast dest: closed sym)

lemma (in equivalence) closure_of_eq:
  "[| x .= x'; A \<subseteq> carrier S; x \<in> closure_of A; x \<in> carrier S; x' \<in> carrier S |] ==> x' \<in> closure_of A"
  unfolding eq_closure_of_def elem_def
  by (blast intro: trans sym)

lemma (in equivalence) is_closed_eq [dest]:
  "[| x .= x'; x \<in> A; is_closed A; x \<in> carrier S; x' \<in> carrier S |] ==> x' \<in> A"
  unfolding eq_is_closed_def
  using closure_of_eq [where A = A]
  by simp

lemma (in equivalence) is_closed_eq_rev [dest]:
  "[| x .= x'; x' \<in> A; is_closed A; x \<in> carrier S; x' \<in> carrier S |] ==> x \<in> A"
  by (drule sym) (simp_all add: is_closed_eq)

lemma closure_of_closed [simp, intro]:
  fixes S (structure)
  shows "closure_of A \<subseteq> carrier S"
unfolding eq_closure_of_def
by fast

lemma closure_of_memI:
  fixes S (structure)
  assumes "a .\<in> A"
    and "a \<in> carrier S"
  shows "a \<in> closure_of A"
unfolding eq_closure_of_def
using assms
by fast

lemma closure_ofI2:
  fixes S (structure)
  assumes "a .= a'"
    and "a' \<in> A"
    and "a \<in> carrier S"
  shows "a \<in> closure_of A"
unfolding eq_closure_of_def elem_def
using assms
by fast

lemma closure_of_memE:
  fixes S (structure)
  assumes p: "a \<in> closure_of A"
    and r: "\<lbrakk>a \<in> carrier S; a .\<in> A\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from p
      have acarr: "a \<in> carrier S"
      and "a .\<in> A"
      by (simp add: eq_closure_of_def)+
  thus "P" by (rule r)
qed

lemma closure_ofE2:
  fixes S (structure)
  assumes p: "a \<in> closure_of A"
    and r: "\<And>a'. \<lbrakk>a \<in> carrier S; a' \<in> A; a .= a'\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from p have acarr: "a \<in> carrier S" by (simp add: eq_closure_of_def)

  from p have "\<exists>a'\<in>A. a .= a'" by (simp add: eq_closure_of_def elem_def)
  from this obtain a'
      where "a' \<in> A" and "a .= a'" by auto

  from acarr and this
      show "P" by (rule r)
qed

(*
lemma (in equivalence) classes_consistent:
  assumes Acarr: "A \<subseteq> carrier S"
  shows "is_closed (closure_of A)"
apply (blast intro: elemI elim elemE)
using assms
apply (intro is_closedI closure_of_memI, simp)
 apply (elim elemE closure_of_memE)
proof -
  fix x a' a''
  assume carr: "x \<in> carrier S" "a' \<in> carrier S"
  assume a''A: "a'' \<in> A"
  with Acarr have "a'' \<in> carrier S" by fast
  note [simp] = carr this Acarr

  assume "x .= a'"
  also assume "a' .= a''"
  also from a''A
       have "a'' .\<in> A" by (simp add: elem_exact)
  finally show "x .\<in> A" by simp
qed
*)
(*
lemma (in equivalence) classes_small:
  assumes "is_closed B"
    and "A \<subseteq> B"
  shows "closure_of A \<subseteq> B"
using assms
by (blast dest: is_closedD2 elem_subsetD elim: closure_of_memE)

lemma (in equivalence) classes_eq:
  assumes "A \<subseteq> carrier S"
  shows "A {.=} closure_of A"
using assms
by (blast intro: set_eqI elem_exact closure_of_memI elim: closure_of_memE)

lemma (in equivalence) complete_classes:
  assumes c: "is_closed A"
  shows "A = closure_of A"
using assms
by (blast intro: closure_of_memI elem_exact dest: is_closedD1 is_closedD2 closure_of_memE)
*)

end
