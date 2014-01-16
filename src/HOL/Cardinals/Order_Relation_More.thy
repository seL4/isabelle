(*  Title:      HOL/Cardinals/Order_Relation_More.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Basics on order-like relations.
*)

header {* Basics on Order-Like Relations *}

theory Order_Relation_More
imports Order_Relation_More_FP Main
begin


subsection {* The upper and lower bounds operators  *}

lemma aboveS_subset_above: "aboveS r a \<le> above r a"
by(auto simp add: aboveS_def above_def)

lemma AboveS_subset_Above: "AboveS r A \<le> Above r A"
by(auto simp add: AboveS_def Above_def)

lemma UnderS_disjoint: "A Int (UnderS r A) = {}"
by(auto simp add: UnderS_def)

lemma aboveS_notIn: "a \<notin> aboveS r a"
by(auto simp add: aboveS_def)

lemma Refl_above_in: "\<lbrakk>Refl r; a \<in> Field r\<rbrakk> \<Longrightarrow> a \<in> above r a"
by(auto simp add: refl_on_def above_def)

lemma in_Above_under: "a \<in> Field r \<Longrightarrow> a \<in> Above r (under r a)"
by(auto simp add: Above_def under_def)

lemma in_Under_above: "a \<in> Field r \<Longrightarrow> a \<in> Under r (above r a)"
by(auto simp add: Under_def above_def)

lemma in_UnderS_aboveS: "a \<in> Field r \<Longrightarrow> a \<in> UnderS r (aboveS r a)"
by(auto simp add: UnderS_def aboveS_def)

lemma UnderS_subset_Under: "UnderS r A \<le> Under r A"
by(auto simp add: UnderS_def Under_def)

lemma subset_Above_Under: "B \<le> Field r \<Longrightarrow> B \<le> Above r (Under r B)"
by(auto simp add: Above_def Under_def)

lemma subset_Under_Above: "B \<le> Field r \<Longrightarrow> B \<le> Under r (Above r B)"
by(auto simp add: Under_def Above_def)

lemma subset_AboveS_UnderS: "B \<le> Field r \<Longrightarrow> B \<le> AboveS r (UnderS r B)"
by(auto simp add: AboveS_def UnderS_def)

lemma subset_UnderS_AboveS: "B \<le> Field r \<Longrightarrow> B \<le> UnderS r (AboveS r B)"
by(auto simp add: UnderS_def AboveS_def)

lemma Under_Above_Galois:
"\<lbrakk>B \<le> Field r; C \<le> Field r\<rbrakk> \<Longrightarrow> (B \<le> Above r C) = (C \<le> Under r B)"
by(unfold Above_def Under_def, blast)

lemma UnderS_AboveS_Galois:
"\<lbrakk>B \<le> Field r; C \<le> Field r\<rbrakk> \<Longrightarrow> (B \<le> AboveS r C) = (C \<le> UnderS r B)"
by(unfold AboveS_def UnderS_def, blast)

lemma Refl_above_aboveS:
  assumes REFL: "Refl r" and IN: "a \<in> Field r"
  shows "above r a = aboveS r a \<union> {a}"
proof(unfold above_def aboveS_def, auto)
  show "(a,a) \<in> r" using REFL IN refl_on_def[of _ r] by blast
qed

lemma Linear_order_under_aboveS_Field:
  assumes LIN: "Linear_order r" and IN: "a \<in> Field r"
  shows "Field r = under r a \<union> aboveS r a"
proof(unfold under_def aboveS_def, auto)
  assume "a \<in> Field r" "(a, a) \<notin> r"
  with LIN IN order_on_defs[of _ r] refl_on_def[of _ r]
  show False by auto
next
  fix b assume "b \<in> Field r" "(b, a) \<notin> r"
  with LIN IN order_on_defs[of "Field r" r] total_on_def[of "Field r" r]
  have "(a,b) \<in> r \<or> a = b" by blast
  thus "(a,b) \<in> r"
  using LIN IN order_on_defs[of _ r] refl_on_def[of _ r] by auto
next
  fix b assume "(b, a) \<in> r"
  thus "b \<in> Field r"
  using LIN order_on_defs[of _ r] refl_on_def[of _ r] by blast
next
  fix b assume "b \<noteq> a" "(a, b) \<in> r"
  thus "b \<in> Field r"
  using LIN order_on_defs[of "Field r" r] refl_on_def[of "Field r" r] by blast
qed

lemma Linear_order_underS_above_Field:
assumes LIN: "Linear_order r" and IN: "a \<in> Field r"
shows "Field r = underS r a \<union> above r a"
proof(unfold underS_def above_def, auto)
  assume "a \<in> Field r" "(a, a) \<notin> r"
  with LIN IN order_on_defs[of _ r] refl_on_def[of _ r]
  show False by metis
next
  fix b assume "b \<in> Field r" "(a, b) \<notin> r"
  with LIN IN order_on_defs[of "Field r" r] total_on_def[of "Field r" r]
  have "(b,a) \<in> r \<or> b = a" by blast
  thus "(b,a) \<in> r"
  using LIN IN order_on_defs[of _ r] refl_on_def[of _ r] by auto
next
  fix b assume "b \<noteq> a" "(b, a) \<in> r"
  thus "b \<in> Field r"
  using LIN order_on_defs[of _ r] refl_on_def[of _ r] by blast
next
  fix b assume "(a, b) \<in> r"
  thus "b \<in> Field r"
  using LIN order_on_defs[of "Field r" r] refl_on_def[of "Field r" r] by blast
qed

lemma under_empty: "a \<notin> Field r \<Longrightarrow> under r a = {}"
unfolding Field_def under_def by auto

lemma Under_Field: "Under r A \<le> Field r"
by(unfold Under_def Field_def, auto)

lemma UnderS_Field: "UnderS r A \<le> Field r"
by(unfold UnderS_def Field_def, auto)

lemma above_Field: "above r a \<le> Field r"
by(unfold above_def Field_def, auto)

lemma aboveS_Field: "aboveS r a \<le> Field r"
by(unfold aboveS_def Field_def, auto)

lemma Above_Field: "Above r A \<le> Field r"
by(unfold Above_def Field_def, auto)

lemma Refl_under_Under:
assumes REFL: "Refl r" and NE: "A \<noteq> {}"
shows "Under r A = (\<Inter> a \<in> A. under r a)"
proof
  show "Under r A \<subseteq> (\<Inter> a \<in> A. under r a)"
  by(unfold Under_def under_def, auto)
next
  show "(\<Inter> a \<in> A. under r a) \<subseteq> Under r A"
  proof(auto)
    fix x
    assume *: "\<forall>xa \<in> A. x \<in> under r xa"
    hence "\<forall>xa \<in> A. (x,xa) \<in> r"
    by (simp add: under_def)
    moreover
    {from NE obtain a where "a \<in> A" by blast
     with * have "x \<in> under r a" by simp
     hence "x \<in> Field r"
     using under_Field[of r a] by auto
    }
    ultimately show "x \<in> Under r A"
    unfolding Under_def by auto
  qed
qed

lemma Refl_underS_UnderS:
assumes REFL: "Refl r" and NE: "A \<noteq> {}"
shows "UnderS r A = (\<Inter> a \<in> A. underS r a)"
proof
  show "UnderS r A \<subseteq> (\<Inter> a \<in> A. underS r a)"
  by(unfold UnderS_def underS_def, auto)
next
  show "(\<Inter> a \<in> A. underS r a) \<subseteq> UnderS r A"
  proof(auto)
    fix x
    assume *: "\<forall>xa \<in> A. x \<in> underS r xa"
    hence "\<forall>xa \<in> A. x \<noteq> xa \<and> (x,xa) \<in> r"
    by (auto simp add: underS_def)
    moreover
    {from NE obtain a where "a \<in> A" by blast
     with * have "x \<in> underS r a" by simp
     hence "x \<in> Field r"
     using underS_Field[of r a] by auto
    }
    ultimately show "x \<in> UnderS r A"
    unfolding UnderS_def by auto
  qed
qed

lemma Refl_above_Above:
assumes REFL: "Refl r" and NE: "A \<noteq> {}"
shows "Above r A = (\<Inter> a \<in> A. above r a)"
proof
  show "Above r A \<subseteq> (\<Inter> a \<in> A. above r a)"
  by(unfold Above_def above_def, auto)
next
  show "(\<Inter> a \<in> A. above r a) \<subseteq> Above r A"
  proof(auto)
    fix x
    assume *: "\<forall>xa \<in> A. x \<in> above r xa"
    hence "\<forall>xa \<in> A. (xa,x) \<in> r"
    by (simp add: above_def)
    moreover
    {from NE obtain a where "a \<in> A" by blast
     with * have "x \<in> above r a" by simp
     hence "x \<in> Field r"
     using above_Field[of r a] by auto
    }
    ultimately show "x \<in> Above r A"
    unfolding Above_def by auto
  qed
qed

lemma Refl_aboveS_AboveS:
assumes REFL: "Refl r" and NE: "A \<noteq> {}"
shows "AboveS r A = (\<Inter> a \<in> A. aboveS r a)"
proof
  show "AboveS r A \<subseteq> (\<Inter> a \<in> A. aboveS r a)"
  by(unfold AboveS_def aboveS_def, auto)
next
  show "(\<Inter> a \<in> A. aboveS r a) \<subseteq> AboveS r A"
  proof(auto)
    fix x
    assume *: "\<forall>xa \<in> A. x \<in> aboveS r xa"
    hence "\<forall>xa \<in> A. xa \<noteq> x \<and> (xa,x) \<in> r"
    by (auto simp add: aboveS_def)
    moreover
    {from NE obtain a where "a \<in> A" by blast
     with * have "x \<in> aboveS r a" by simp
     hence "x \<in> Field r"
     using aboveS_Field[of r a] by auto
    }
    ultimately show "x \<in> AboveS r A"
    unfolding AboveS_def by auto
  qed
qed

lemma under_Under_singl: "under r a = Under r {a}"
by(unfold Under_def under_def, auto simp add: Field_def)

lemma underS_UnderS_singl: "underS r a = UnderS r {a}"
by(unfold UnderS_def underS_def, auto simp add: Field_def)

lemma above_Above_singl: "above r a = Above r {a}"
by(unfold Above_def above_def, auto simp add: Field_def)

lemma aboveS_AboveS_singl: "aboveS r a = AboveS r {a}"
by(unfold AboveS_def aboveS_def, auto simp add: Field_def)

lemma Under_decr: "A \<le> B \<Longrightarrow> Under r B \<le> Under r A"
by(unfold Under_def, auto)

lemma UnderS_decr: "A \<le> B \<Longrightarrow> UnderS r B \<le> UnderS r A"
by(unfold UnderS_def, auto)

lemma Above_decr: "A \<le> B \<Longrightarrow> Above r B \<le> Above r A"
by(unfold Above_def, auto)

lemma AboveS_decr: "A \<le> B \<Longrightarrow> AboveS r B \<le> AboveS r A"
by(unfold AboveS_def, auto)

lemma under_incl_iff:
assumes TRANS: "trans r" and REFL: "Refl r" and IN: "a \<in> Field r"
shows "(under r a \<le> under r b) = ((a,b) \<in> r)"
proof
  assume "(a,b) \<in> r"
  thus "under r a \<le> under r b" using TRANS
  by (auto simp add: under_incr)
next
  assume "under r a \<le> under r b"
  moreover
  have "a \<in> under r a" using REFL IN
  by (auto simp add: Refl_under_in)
  ultimately show "(a,b) \<in> r"
  by (auto simp add: under_def)
qed

lemma above_decr:
assumes TRANS: "trans r" and REL: "(a,b) \<in> r"
shows "above r b \<le> above r a"
proof(unfold above_def, auto)
  fix x assume "(b,x) \<in> r"
  with REL TRANS trans_def[of r]
  show "(a,x) \<in> r" by blast
qed

lemma aboveS_decr:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        REL: "(a,b) \<in> r"
shows "aboveS r b \<le> aboveS r a"
proof(unfold aboveS_def, auto)
  assume *: "a \<noteq> b" and **: "(b,a) \<in> r"
  with ANTISYM antisym_def[of r] REL
  show False by auto
next
  fix x assume "x \<noteq> b" "(b,x) \<in> r"
  with REL TRANS trans_def[of r]
  show "(a,x) \<in> r" by blast
qed

lemma under_trans:
assumes TRANS: "trans r" and
        IN1: "a \<in> under r b" and IN2: "b \<in> under r c"
shows "a \<in> under r c"
proof-
  have "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 under_def by fastforce
  hence "(a,c) \<in> r"
  using TRANS trans_def[of r] by blast
  thus ?thesis unfolding under_def by simp
qed

lemma under_underS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "a \<in> under r b" and IN2: "b \<in> underS r c"
shows "a \<in> underS r c"
proof-
  have 0: "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 under_def underS_def by fastforce
  hence 1: "(a,c) \<in> r"
  using TRANS trans_def[of r] by blast
  have 2: "b \<noteq> c" using IN2 underS_def by force
  have 3: "a \<noteq> c"
  proof
    assume "a = c" with 0 2 ANTISYM antisym_def[of r]
    show False by auto
  qed
  from 1 3 show ?thesis unfolding underS_def by simp
qed

lemma underS_under_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "a \<in> underS r b" and IN2: "b \<in> under r c"
shows "a \<in> underS r c"
proof-
  have 0: "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 under_def underS_def by fast
  hence 1: "(a,c) \<in> r"
  using TRANS trans_def[of r] by fast
  have 2: "a \<noteq> b" using IN1 underS_def by force
  have 3: "a \<noteq> c"
  proof
    assume "a = c" with 0 2 ANTISYM antisym_def[of r]
    show False by auto
  qed
  from 1 3 show ?thesis unfolding underS_def by simp
qed

lemma underS_underS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "a \<in> underS r b" and IN2: "b \<in> underS r c"
shows "a \<in> underS r c"
proof-
  have "a \<in> under r b"
  using IN1 underS_subset_under by fast
  with assms under_underS_trans show ?thesis by fast
qed

lemma above_trans:
assumes TRANS: "trans r" and
        IN1: "b \<in> above r a" and IN2: "c \<in> above r b"
shows "c \<in> above r a"
proof-
  have "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 above_def by fast
  hence "(a,c) \<in> r"
  using TRANS trans_def[of r] by blast
  thus ?thesis unfolding above_def by simp
qed

lemma above_aboveS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "b \<in> above r a" and IN2: "c \<in> aboveS r b"
shows "c \<in> aboveS r a"
proof-
  have 0: "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 above_def aboveS_def by fast
  hence 1: "(a,c) \<in> r"
  using TRANS trans_def[of r] by blast
  have 2: "b \<noteq> c" using IN2 aboveS_def by force
  have 3: "a \<noteq> c"
  proof
    assume "a = c" with 0 2 ANTISYM antisym_def[of r]
    show False by auto
  qed
  from 1 3 show ?thesis unfolding aboveS_def by simp
qed

lemma aboveS_above_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "b \<in> aboveS r a" and IN2: "c \<in> above r b"
shows "c \<in> aboveS r a"
proof-
  have 0: "(a,b) \<in> r \<and> (b,c) \<in> r"
  using IN1 IN2 above_def aboveS_def by fast
  hence 1: "(a,c) \<in> r"
  using TRANS trans_def[of r] by blast
  have 2: "a \<noteq> b" using IN1 aboveS_def by force
  have 3: "a \<noteq> c"
  proof
    assume "a = c" with 0 2 ANTISYM antisym_def[of r]
    show False by auto
  qed
  from 1 3 show ?thesis unfolding aboveS_def by simp
qed

lemma aboveS_aboveS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "b \<in> aboveS r a" and IN2: "c \<in> aboveS r b"
shows "c \<in> aboveS r a"
proof-
  have "b \<in> above r a"
  using IN1 aboveS_subset_above by fast
  with assms above_aboveS_trans show ?thesis by fast
qed

lemma under_Under_trans:
assumes TRANS: "trans r" and
        IN1: "a \<in> under r b" and IN2: "b \<in> Under r C"
shows "a \<in> Under r C"
proof-
  have "b \<in> {u \<in> Field r. \<forall>x. x \<in> C \<longrightarrow> (u, x) \<in> r}"
    using IN2 Under_def by force
  hence "(a,b) \<in> r \<and> (\<forall>c \<in> C. (b,c) \<in> r)"
    using IN1 under_def by fast
  hence "\<forall>c \<in> C. (a,c) \<in> r"
  using TRANS trans_def[of r] by blast
  moreover
  have "a \<in> Field r" using IN1 unfolding Field_def under_def by blast
  ultimately
  show ?thesis unfolding Under_def by blast
qed

lemma underS_Under_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "a \<in> underS r b" and IN2: "b \<in> Under r C"
shows "a \<in> UnderS r C"
proof-
  from IN1 have "a \<in> under r b"
  using underS_subset_under[of r b] by fast
  with assms under_Under_trans
  have "a \<in> Under r C" by fast
  (*  *)
  moreover
  have "a \<notin> C"
  proof
    assume *: "a \<in> C"
    have 1: "b \<noteq> a \<and> (a,b) \<in> r"
    using IN1 underS_def[of r b] by auto
    have "\<forall>c \<in> C. (b,c) \<in> r"
    using IN2 Under_def[of r C] by auto
    with * have "(b,a) \<in> r" by simp
    with 1 ANTISYM antisym_def[of r]
    show False by blast
  qed
  (*  *)
  ultimately
  show ?thesis unfolding UnderS_def
  using Under_def by force
qed

lemma underS_UnderS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "a \<in> underS r b" and IN2: "b \<in> UnderS r C"
shows "a \<in> UnderS r C"
proof-
  from IN2 have "b \<in> Under r C"
  using UnderS_subset_Under[of r C] by blast
  with underS_Under_trans assms
  show ?thesis by force
qed

lemma above_Above_trans:
assumes TRANS: "trans r" and
        IN1: "a \<in> above r b" and IN2: "b \<in> Above r C"
shows "a \<in> Above r C"
proof-
  have "(b,a) \<in> r \<and> (\<forall>c \<in> C. (c,b) \<in> r)"
    using IN1[unfolded above_def] IN2[unfolded Above_def] by simp
  hence "\<forall>c \<in> C. (c,a) \<in> r"
  using TRANS trans_def[of r] by blast
  moreover
  have "a \<in> Field r" using IN1[unfolded above_def] Field_def by fast
  ultimately
  show ?thesis unfolding Above_def by auto
qed

lemma aboveS_Above_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "a \<in> aboveS r b" and IN2: "b \<in> Above r C"
shows "a \<in> AboveS r C"
proof-
  from IN1 have "a \<in> above r b"
  using aboveS_subset_above[of r b] by blast
  with assms above_Above_trans
  have "a \<in> Above r C" by fast
  (*  *)
  moreover
  have "a \<notin> C"
  proof
    assume *: "a \<in> C"
    have 1: "b \<noteq> a \<and> (b,a) \<in> r"
    using IN1 aboveS_def[of r b] by auto
    have "\<forall>c \<in> C. (c,b) \<in> r"
    using IN2 Above_def[of r C] by auto
    with * have "(a,b) \<in> r" by simp
    with 1 ANTISYM antisym_def[of r]
    show False by blast
  qed
  (*  *)
  ultimately
  show ?thesis unfolding AboveS_def
  using Above_def by force
qed

lemma above_AboveS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "a \<in> above r b" and IN2: "b \<in> AboveS r C"
shows "a \<in> AboveS r C"
proof-
  from IN2 have "b \<in> Above r C"
  using AboveS_subset_Above[of r C] by blast
  with assms above_Above_trans
  have "a \<in> Above r C" by force
  (*  *)
  moreover
  have "a \<notin> C"
  proof
    assume *: "a \<in> C"
    have 1: "(b,a) \<in> r"
    using IN1 above_def[of r b] by auto
    have "\<forall>c \<in> C. b \<noteq> c \<and> (c,b) \<in> r"
    using IN2 AboveS_def[of r C] by auto
    with * have "b \<noteq> a \<and> (a,b) \<in> r" by simp
    with 1 ANTISYM antisym_def[of r]
    show False by blast
  qed
  (*  *)
  ultimately
  show ?thesis unfolding AboveS_def
  using Above_def by force
qed

lemma aboveS_AboveS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "a \<in> aboveS r b" and IN2: "b \<in> AboveS r C"
shows "a \<in> AboveS r C"
proof-
  from IN2 have "b \<in> Above r C"
  using AboveS_subset_Above[of r C] by blast
  with aboveS_Above_trans assms
  show ?thesis by force
qed

lemma under_UnderS_trans:
assumes TRANS: "trans r" and ANTISYM: "antisym r" and
        IN1: "a \<in> under r b" and IN2: "b \<in> UnderS r C"
shows "a \<in> UnderS r C"
proof-
  from IN2 have "b \<in> Under r C"
  using UnderS_subset_Under[of r C] by blast
  with assms under_Under_trans
  have "a \<in> Under r C" by force
  (*  *)
  moreover
  have "a \<notin> C"
  proof
    assume *: "a \<in> C"
    have 1: "(a,b) \<in> r"
    using IN1 under_def[of r b] by auto
    have "\<forall>c \<in> C. b \<noteq> c \<and> (b,c) \<in> r"
    using IN2 UnderS_def[of r C] by blast
    with * have "b \<noteq> a \<and> (b,a) \<in> r" by blast
    with 1 ANTISYM antisym_def[of r]
    show False by blast
  qed
  (*  *)
  ultimately
  show ?thesis unfolding UnderS_def Under_def by fast
qed


subsection {* Properties depending on more than one relation  *}

lemma under_incr2:
"r \<le> r' \<Longrightarrow> under r a \<le> under r' a"
unfolding under_def by blast

lemma underS_incr2:
"r \<le> r' \<Longrightarrow> underS r a \<le> underS r' a"
unfolding underS_def by blast

(* FIXME: r \<leadsto> r'
lemma Under_incr:
"r \<le> r' \<Longrightarrow> Under r A \<le> Under r A"
unfolding Under_def by blast

lemma UnderS_incr:
"r \<le> r' \<Longrightarrow> UnderS r A \<le> UnderS r A"
unfolding UnderS_def by blast

lemma Under_incr_decr:
"\<lbrakk>r \<le> r'; A' \<le> A\<rbrakk>  \<Longrightarrow> Under r A \<le> Under r A'"
unfolding Under_def by blast

lemma UnderS_incr_decr:
"\<lbrakk>r \<le> r'; A' \<le> A\<rbrakk>  \<Longrightarrow> UnderS r A \<le> UnderS r A'"
unfolding UnderS_def by blast
*)

lemma above_incr2:
"r \<le> r' \<Longrightarrow> above r a \<le> above r' a"
unfolding above_def by blast

lemma aboveS_incr2:
"r \<le> r' \<Longrightarrow> aboveS r a \<le> aboveS r' a"
unfolding aboveS_def by blast

(* FIXME
lemma Above_incr:
"r \<le> r' \<Longrightarrow> Above r A \<le> Above r A"
unfolding Above_def by blast

lemma AboveS_incr:
"r \<le> r' \<Longrightarrow> AboveS r A \<le> AboveS r A"
unfolding AboveS_def by blast

lemma Above_incr_decr:
"\<lbrakk>r \<le> r'; A' \<le> A\<rbrakk> \<Longrightarrow> Above r A \<le> Above r A'"
unfolding Above_def by blast

lemma AboveS_incr_decr:
"\<lbrakk>r \<le> r'; A' \<le> A\<rbrakk> \<Longrightarrow> AboveS r A \<le> AboveS r A'"
unfolding AboveS_def by blast
*)

end
