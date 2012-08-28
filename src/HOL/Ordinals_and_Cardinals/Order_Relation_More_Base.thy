(*  Title:      HOL/Ordinals_and_Cardinals/Order_Relation_More_Base.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Basics on order-like relations (base).
*)

header {* Basics on Order-Like Relations (Base) *}

theory Order_Relation_More_Base
imports "~~/src/HOL/Library/Order_Relation"
begin


text{* In this section, we develop basic concepts and results pertaining
to order-like relations, i.e., to reflexive and/or transitive and/or symmetric and/or
total relations.  The development is placed on top of the definitions
from the theory @{text "Order_Relation"}.  We also
further define upper and lower bounds operators. *}


locale rel = fixes r :: "'a rel"

text{* The following context encompasses all this section, except
for its last subsection. In other words, for the rest of this section except its last
subsection, we consider a fixed relation @{text "r"}. *}

context rel
begin


subsection {* Auxiliaries *}


lemma refl_on_domain:
"\<lbrakk>refl_on A r; (a,b) : r\<rbrakk> \<Longrightarrow> a \<in> A \<and> b \<in> A"
by(auto simp add: refl_on_def)


corollary well_order_on_domain:
"\<lbrakk>well_order_on A r; (a,b) \<in> r\<rbrakk> \<Longrightarrow> a \<in> A \<and> b \<in> A"
by(simp add: refl_on_domain order_on_defs)


lemma well_order_on_Field:
"well_order_on A r \<Longrightarrow> A = Field r"
by(auto simp add: refl_on_def Field_def order_on_defs)


lemma well_order_on_Well_order:
"well_order_on A r \<Longrightarrow> A = Field r \<and> Well_order r"
using well_order_on_Field by simp


lemma Total_Id_Field:
assumes TOT: "Total r" and NID: "\<not> (r <= Id)"
shows "Field r = Field(r - Id)"
using mono_Field[of "r - Id" r] Diff_subset[of r Id]
proof(auto)
  have "r \<noteq> {}" using NID by fast
  then obtain b and c where "b \<noteq> c \<and> (b,c) \<in> r" using NID by fast
  hence 1: "b \<noteq> c \<and> {b,c} \<le> Field r" by (auto simp: Field_def)
  (*  *)
  fix a assume *: "a \<in> Field r"
  obtain d where 2: "d \<in> Field r" and 3: "d \<noteq> a"
  using * 1 by blast
  hence "(a,d) \<in> r \<or> (d,a) \<in> r" using * TOT
  by (simp add: total_on_def)
  thus "a \<in> Field(r - Id)" using 3 unfolding Field_def by blast
qed


lemma Total_subset_Id:
assumes TOT: "Total r" and SUB: "r \<le> Id"
shows "r = {} \<or> (\<exists>a. r = {(a,a)})"
proof-
  {assume "r \<noteq> {}"
   then obtain a b where 1: "(a,b) \<in> r" by fast
   hence "a = b" using SUB by blast
   hence 2: "(a,a) \<in> r" using 1 by simp
   {fix c d assume "(c,d) \<in> r"
    hence "{a,c,d} \<le> Field r" using 1 unfolding Field_def by blast
    hence "((a,c) \<in> r \<or> (c,a) \<in> r \<or> a = c) \<and>
           ((a,d) \<in> r \<or> (d,a) \<in> r \<or> a = d)"
    using TOT unfolding total_on_def by blast
    hence "a = c \<and> a = d" using SUB by blast
   }
   hence "r \<le> {(a,a)}" by auto
   with 2 have "\<exists>a. r = {(a,a)}" by blast
  }
  thus ?thesis by blast
qed


lemma Linear_order_in_diff_Id:
assumes LI: "Linear_order r" and
        IN1: "a \<in> Field r" and IN2: "b \<in> Field r"
shows "((a,b) \<in> r) = ((b,a) \<notin> r - Id)"
using assms unfolding order_on_defs total_on_def antisym_def Id_def refl_on_def by force


subsection {* The upper and lower bounds operators  *}


text{* Here we define upper (``above") and lower (``below") bounds operators.
We think of @{text "r"} as a {\em non-strict} relation.  The suffix ``S"
at the names of some operators indicates that the bounds are strict -- e.g.,
@{text "underS a"} is the set of all strict lower bounds of @{text "a"} (w.r.t. @{text "r"}).
Capitalization of the first letter in the name reminds that the operator acts on sets, rather
than on individual elements. *}

definition under::"'a \<Rightarrow> 'a set"
where "under a \<equiv> {b. (b,a) \<in> r}"

definition underS::"'a \<Rightarrow> 'a set"
where "underS a \<equiv> {b. b \<noteq> a \<and> (b,a) \<in> r}"

definition Under::"'a set \<Rightarrow> 'a set"
where "Under A \<equiv> {b \<in> Field r. \<forall>a \<in> A. (b,a) \<in> r}"

definition UnderS::"'a set \<Rightarrow> 'a set"
where "UnderS A \<equiv> {b \<in> Field r. \<forall>a \<in> A. b \<noteq> a \<and> (b,a) \<in> r}"

definition above::"'a \<Rightarrow> 'a set"
where "above a \<equiv> {b. (a,b) \<in> r}"

definition aboveS::"'a \<Rightarrow> 'a set"
where "aboveS a \<equiv> {b. b \<noteq> a \<and> (a,b) \<in> r}"

definition Above::"'a set \<Rightarrow> 'a set"
where "Above A \<equiv> {b \<in> Field r. \<forall>a \<in> A. (a,b) \<in> r}"

definition AboveS::"'a set \<Rightarrow> 'a set"
where "AboveS A \<equiv> {b \<in> Field r. \<forall>a \<in> A. b \<noteq> a \<and> (a,b) \<in> r}"
(*  *)

text{* Note:  In the definitions of @{text "Above[S]"} and @{text "Under[S]"},
  we bounded comprehension by @{text "Field r"} in order to properly cover
  the case of @{text "A"} being empty. *}


lemma UnderS_subset_Under: "UnderS A \<le> Under A"
by(auto simp add: UnderS_def Under_def)


lemma underS_subset_under: "underS a \<le> under a"
by(auto simp add: underS_def under_def)


lemma underS_notIn: "a \<notin> underS a"
by(simp add: underS_def)


lemma Refl_under_in: "\<lbrakk>Refl r; a \<in> Field r\<rbrakk> \<Longrightarrow> a \<in> under a"
by(simp add: refl_on_def under_def)


lemma AboveS_disjoint: "A Int (AboveS A) = {}"
by(auto simp add: AboveS_def)


lemma in_AboveS_underS: "a \<in> Field r \<Longrightarrow> a \<in> AboveS (underS a)"
by(auto simp add: AboveS_def underS_def)


lemma Refl_under_underS:
assumes "Refl r" "a \<in> Field r"
shows "under a = underS a \<union> {a}"
unfolding under_def underS_def
using assms refl_on_def[of _ r] by fastforce


lemma underS_empty: "a \<notin> Field r \<Longrightarrow> underS a = {}"
by (auto simp: Field_def underS_def)


lemma under_Field: "under a \<le> Field r"
by(unfold under_def Field_def, auto)


lemma underS_Field: "underS a \<le> Field r"
by(unfold underS_def Field_def, auto)


lemma underS_Field2:
"a \<in> Field r \<Longrightarrow> underS a < Field r"
using assms underS_notIn underS_Field by blast


lemma underS_Field3:
"Field r \<noteq> {} \<Longrightarrow> underS a < Field r"
by(cases "a \<in> Field r", simp add: underS_Field2, auto simp add: underS_empty)


lemma Under_Field: "Under A \<le> Field r"
by(unfold Under_def Field_def, auto)


lemma UnderS_Field: "UnderS A \<le> Field r"
by(unfold UnderS_def Field_def, auto)


lemma AboveS_Field: "AboveS A \<le> Field r"
by(unfold AboveS_def Field_def, auto)


lemma under_incr:
assumes TRANS: "trans r" and REL: "(a,b) \<in> r"
shows "under a \<le> under b"
proof(unfold under_def, auto)
  fix x assume "(x,a) \<in> r"
  with REL TRANS trans_def[of r]
  show "(x,b) \<in> r" by blast
qed


lemma underS_incr:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        REL: "(a,b) \<in> r"
shows "underS a \<le> underS b"
proof(unfold underS_def, auto)
  assume *: "b \<noteq> a" and **: "(b,a) \<in> r"
  with ANTISYM antisym_def[of r] REL
  show False by blast
next
  fix x assume "x \<noteq> a" "(x,a) \<in> r"
  with REL TRANS trans_def[of r]
  show "(x,b) \<in> r" by blast
qed


lemma underS_incl_iff:
assumes LO: "Linear_order r" and
        INa: "a \<in> Field r" and INb: "b \<in> Field r"
shows "(underS a \<le> underS b) = ((a,b) \<in> r)"
proof
  assume "(a,b) \<in> r"
  thus "underS a \<le> underS b" using LO
  by (simp add: order_on_defs underS_incr)
next
  assume *: "underS a \<le> underS b"
  {assume "a = b"
   hence "(a,b) \<in> r" using assms
   by (simp add: order_on_defs refl_on_def)
  }
  moreover
  {assume "a \<noteq> b \<and> (b,a) \<in> r"
   hence "b \<in> underS a" unfolding underS_def by blast
   hence "b \<in> underS b" using * by blast
   hence False by (simp add: underS_notIn)
  }
  ultimately
  show "(a,b) \<in> r" using assms
  order_on_defs[of "Field r" r] total_on_def[of "Field r" r] by blast
qed


lemma under_Under_trans:
assumes TRANS: "trans r" and
        IN1: "a \<in> under b" and IN2: "b \<in> Under C"
shows "a \<in> Under C"
proof-
  have "(a,b) \<in> r \<and> (\<forall>c \<in> C. (b,c) \<in> r)"
  using IN1 IN2 under_def Under_def by blast
  hence "\<forall>c \<in> C. (a,c) \<in> r"
  using TRANS trans_def[of r] by blast
  moreover
  have "a \<in> Field r" using IN1 unfolding Field_def under_def by blast
  ultimately
  show ?thesis unfolding Under_def by blast
qed


lemma under_UnderS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "a \<in> under b" and IN2: "b \<in> UnderS C"
shows "a \<in> UnderS C"
proof-
  from IN2 have "b \<in> Under C"
  using UnderS_subset_Under[of C] by blast
  with assms under_Under_trans
  have "a \<in> Under C" by blast
  (*  *)
  moreover
  have "a \<notin> C"
  proof
    assume *: "a \<in> C"
    have 1: "(a,b) \<in> r"
    using IN1 under_def[of b] by auto
    have "\<forall>c \<in> C. b \<noteq> c \<and> (b,c) \<in> r"
    using IN2 UnderS_def[of C] by blast
    with * have "b \<noteq> a \<and> (b,a) \<in> r" by blast
    with 1 ANTISYM antisym_def[of r]
    show False by blast
  qed
  (*  *)
  ultimately
  show ?thesis unfolding UnderS_def Under_def by fast
qed


end  (* context rel *)

end
