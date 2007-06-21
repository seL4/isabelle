(*
    ID:         $Id$
    Author:     Amine Chaieb, TU Muenchen
*)

header {* Dense linear order witout endpoints
  and a quantifier elimination procedure in Ferrante and Rackoff style *}

theory Dense_Linear_Order
imports Finite_Set
uses
  "Tools/qelim.ML"
  "Tools/Ferrante_Rackoff/ferrante_rackoff_data.ML"
  ("Tools/Ferrante_Rackoff/ferrante_rackoff.ML")
begin

setup Ferrante_Rackoff_Data.setup

context Linorder
begin

text{* Theorems for @{text "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P\<^bsub>-\<infinity>\<^esub>)"}*}
lemma minf_lt:  "\<exists>z . \<forall>x. x \<sqsubset> z \<longrightarrow> (x \<sqsubset> t \<longleftrightarrow> True)" by auto
lemma minf_gt: "\<exists>z . \<forall>x. x \<sqsubset> z \<longrightarrow>  (t \<sqsubset> x \<longleftrightarrow>  False)"
  by (simp add: not_less) (rule exI[where x="t"], auto simp add: less_le)

lemma minf_le: "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (x \<sqsubseteq> t \<longleftrightarrow> True)" by (auto simp add: less_le)
lemma minf_ge: "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (t \<sqsubseteq> x \<longleftrightarrow> False)"
  by (auto simp add: less_le not_less not_le)
lemma minf_eq: "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (x = t \<longleftrightarrow> False)" by auto
lemma minf_neq: "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (x \<noteq> t \<longleftrightarrow> True)" by auto
lemma minf_P: "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P \<longleftrightarrow> P)" by blast

text{* Theorems for @{text "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P\<^bsub>+\<infinity>\<^esub>)"}*}
lemma pinf_gt:  "\<exists>z . \<forall>x. z \<sqsubset> x \<longrightarrow> (t \<sqsubset> x \<longleftrightarrow> True)" by auto
lemma pinf_lt: "\<exists>z . \<forall>x. z \<sqsubset> x \<longrightarrow>  (x \<sqsubset> t \<longleftrightarrow>  False)"
  by (simp add: not_less) (rule exI[where x="t"], auto simp add: less_le)

lemma pinf_ge: "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (t \<sqsubseteq> x \<longleftrightarrow> True)" by (auto simp add: less_le)
lemma pinf_le: "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (x \<sqsubseteq> t \<longleftrightarrow> False)"
  by (auto simp add: less_le not_less not_le)
lemma pinf_eq: "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (x = t \<longleftrightarrow> False)" by auto
lemma pinf_neq: "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (x \<noteq> t \<longleftrightarrow> True)" by auto
lemma pinf_P: "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (P \<longleftrightarrow> P)" by blast

lemma nmi_lt: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> x \<sqsubset> t \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)" by auto
lemma nmi_gt: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and> t \<sqsubset> x \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)"
  by (auto simp add: le_less)
lemma  nmi_le: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> x\<sqsubseteq> t \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)" by auto
lemma  nmi_ge: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and> t\<sqsubseteq> x \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)" by auto
lemma  nmi_eq: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x = t \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)" by auto
lemma  nmi_neq: "t \<in> U \<Longrightarrow>\<forall>x. \<not>True \<and> x \<noteq> t \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)" by auto
lemma  nmi_P: "\<forall> x. ~P \<and> P \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)" by auto
lemma  nmi_conj: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x) ;
  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)\<rbrakk> \<Longrightarrow>
  \<forall>x. \<not>(P1' \<and> P2') \<and> (P1 x \<and> P2 x) \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)" by auto
lemma  nmi_disj: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x) ;
  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)\<rbrakk> \<Longrightarrow>
  \<forall>x. \<not>(P1' \<or> P2') \<and> (P1 x \<or> P2 x) \<longrightarrow>  (\<exists> u\<in> U. u \<sqsubseteq> x)" by auto

lemma  npi_lt: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x \<sqsubset> t \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u)" by (auto simp add: le_less)
lemma  npi_gt: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> t \<sqsubset> x \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u)" by auto
lemma  npi_le: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x \<sqsubseteq> t \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u)" by auto
lemma  npi_ge: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> t \<sqsubseteq> x \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u)" by auto
lemma  npi_eq: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x = t \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u)" by auto
lemma  npi_neq: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> x \<noteq> t \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u )" by auto
lemma  npi_P: "\<forall> x. ~P \<and> P \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u)" by auto
lemma  npi_conj: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u) ;  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u)\<rbrakk>
  \<Longrightarrow>  \<forall>x. \<not>(P1' \<and> P2') \<and> (P1 x \<and> P2 x) \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u)" by auto
lemma  npi_disj: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u) ; \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u)\<rbrakk>
  \<Longrightarrow> \<forall>x. \<not>(P1' \<or> P2') \<and> (P1 x \<or> P2 x) \<longrightarrow>  (\<exists> u\<in> U. x \<sqsubseteq> u)" by auto

lemma lin_dense_lt: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t \<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> x \<sqsubset> t \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> y \<sqsubset> t)"
proof(clarsimp)
  fix x l u y  assume tU: "t \<in> U" and noU: "\<forall>t. l \<sqsubset> t \<and> t \<sqsubset> u \<longrightarrow> t \<notin> U" and lx: "l \<sqsubset> x"
    and xu: "x\<sqsubset>u"  and px: "x \<sqsubset> t" and ly: "l\<sqsubset>y" and yu:"y \<sqsubset> u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "t \<sqsubset> y"
    from less_trans[OF lx px] less_trans[OF H yu]
    have "l \<sqsubset> t \<and> t \<sqsubset> u"  by simp
    with tU noU have "False" by auto}
  hence "\<not> t \<sqsubset> y"  by auto hence "y \<sqsubseteq> t" by (simp add: not_less)
  thus "y \<sqsubset> t" using tny by (simp add: less_le)
qed

lemma lin_dense_gt: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l \<sqsubset> x \<and> x \<sqsubset> u \<and> t \<sqsubset> x \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> t \<sqsubset> y)"
proof(clarsimp)
  fix x l u y
  assume tU: "t \<in> U" and noU: "\<forall>t. l \<sqsubset> t \<and> t \<sqsubset> u \<longrightarrow> t \<notin> U" and lx: "l \<sqsubset> x" and xu: "x\<sqsubset>u"
  and px: "t \<sqsubset> x" and ly: "l\<sqsubset>y" and yu:"y \<sqsubset> u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "y\<sqsubset> t"
    from less_trans[OF ly H] less_trans[OF px xu] have "l \<sqsubset> t \<and> t \<sqsubset> u" by simp
    with tU noU have "False" by auto}
  hence "\<not> y\<sqsubset>t"  by auto hence "t \<sqsubseteq> y" by (auto simp add: not_less)
  thus "t \<sqsubset> y" using tny by (simp add:less_le)
qed

lemma lin_dense_le: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> x \<sqsubseteq> t \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> y\<sqsubseteq> t)"
proof(clarsimp)
  fix x l u y
  assume tU: "t \<in> U" and noU: "\<forall>t. l \<sqsubset> t \<and> t \<sqsubset> u \<longrightarrow> t \<notin> U" and lx: "l \<sqsubset> x" and xu: "x\<sqsubset>u"
  and px: "x \<sqsubseteq> t" and ly: "l\<sqsubset>y" and yu:"y \<sqsubset> u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "t \<sqsubset> y"
    from less_le_trans[OF lx px] less_trans[OF H yu]
    have "l \<sqsubset> t \<and> t \<sqsubset> u" by simp
    with tU noU have "False" by auto}
  hence "\<not> t \<sqsubset> y"  by auto thus "y \<sqsubseteq> t" by (simp add: not_less)
qed

lemma lin_dense_ge: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> t \<sqsubseteq> x \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> t \<sqsubseteq> y)"
proof(clarsimp)
  fix x l u y
  assume tU: "t \<in> U" and noU: "\<forall>t. l \<sqsubset> t \<and> t \<sqsubset> u \<longrightarrow> t \<notin> U" and lx: "l \<sqsubset> x" and xu: "x\<sqsubset>u"
  and px: "t \<sqsubseteq> x" and ly: "l\<sqsubset>y" and yu:"y \<sqsubset> u"
  from tU noU ly yu have tny: "t\<noteq>y" by auto
  {assume H: "y\<sqsubset> t"
    from less_trans[OF ly H] le_less_trans[OF px xu]
    have "l \<sqsubset> t \<and> t \<sqsubset> u" by simp
    with tU noU have "False" by auto}
  hence "\<not> y\<sqsubset>t"  by auto thus "t \<sqsubseteq> y" by (simp add: not_less)
qed
lemma lin_dense_eq: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> x = t   \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> y= t)"  by auto
lemma lin_dense_neq: "t \<in> U \<Longrightarrow> \<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> x \<noteq> t   \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> y\<noteq> t)"  by auto
lemma lin_dense_P: "\<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P   \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P)"  by auto

lemma lin_dense_conj:
  "\<lbrakk>\<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P1 x
  \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P1 y) ;
  \<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P2 x
  \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P2 y)\<rbrakk> \<Longrightarrow>
  \<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> (P1 x \<and> P2 x)
  \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> (P1 y \<and> P2 y))"
  by blast
lemma lin_dense_disj:
  "\<lbrakk>\<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P1 x
  \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P1 y) ;
  \<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P2 x
  \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P2 y)\<rbrakk> \<Longrightarrow>
  \<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> (P1 x \<or> P2 x)
  \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> (P1 y \<or> P2 y))"
  by blast

lemma npmibnd: "\<lbrakk>\<forall>x. \<not> MP \<and> P x \<longrightarrow> (\<exists> u\<in> U. u \<sqsubseteq> x); \<forall>x. \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. x \<sqsubseteq> u)\<rbrakk>
  \<Longrightarrow> \<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. \<exists> u' \<in> U. u \<sqsubseteq> x \<and> x \<sqsubseteq> u')"
by auto

lemma finite_set_intervals:
  assumes px: "P x" and lx: "l \<sqsubseteq> x" and xu: "x \<sqsubseteq> u" and linS: "l\<in> S"
  and uinS: "u \<in> S" and fS:"finite S" and lS: "\<forall> x\<in> S. l \<sqsubseteq> x" and Su: "\<forall> x\<in> S. x \<sqsubseteq> u"
  shows "\<exists> a \<in> S. \<exists> b \<in> S. (\<forall> y. a \<sqsubset> y \<and> y \<sqsubset> b \<longrightarrow> y \<notin> S) \<and> a \<sqsubseteq> x \<and> x \<sqsubseteq> b \<and> P x"
proof-
  let ?Mx = "{y. y\<in> S \<and> y \<sqsubseteq> x}"
  let ?xM = "{y. y\<in> S \<and> x \<sqsubseteq> y}"
  let ?a = "Max ?Mx"
  let ?b = "Min ?xM"
  have MxS: "?Mx \<subseteq> S" by blast
  hence fMx: "finite ?Mx" using fS finite_subset by auto
  from lx linS have linMx: "l \<in> ?Mx" by blast
  hence Mxne: "?Mx \<noteq> {}" by blast
  have xMS: "?xM \<subseteq> S" by blast
  hence fxM: "finite ?xM" using fS finite_subset by auto
  from xu uinS have linxM: "u \<in> ?xM" by blast
  hence xMne: "?xM \<noteq> {}" by blast
  have ax:"?a \<sqsubseteq> x" using Mxne fMx by auto
  have xb:"x \<sqsubseteq> ?b" using xMne fxM by auto
  have "?a \<in> ?Mx" using Max_in[OF fMx Mxne] by simp hence ainS: "?a \<in> S" using MxS by blast
  have "?b \<in> ?xM" using Min_in[OF fxM xMne] by simp hence binS: "?b \<in> S" using xMS by blast
  have noy:"\<forall> y. ?a \<sqsubset> y \<and> y \<sqsubset> ?b \<longrightarrow> y \<notin> S"
  proof(clarsimp)
    fix y   assume ay: "?a \<sqsubset> y" and yb: "y \<sqsubset> ?b" and yS: "y \<in> S"
    from yS have "y\<in> ?Mx \<or> y\<in> ?xM" by (auto simp add: linear)
    moreover {assume "y \<in> ?Mx" hence "y \<sqsubseteq> ?a" using Mxne fMx by auto with ay have "False" by (simp add: not_le[symmetric])}
    moreover {assume "y \<in> ?xM" hence "?b \<sqsubseteq> y" using xMne fxM by auto with yb have "False" by (simp add: not_le[symmetric])}
    ultimately show "False" by blast
  qed
  from ainS binS noy ax xb px show ?thesis by blast
qed


lemma finite_set_intervals2:
  assumes px: "P x" and lx: "l \<sqsubseteq> x" and xu: "x \<sqsubseteq> u" and linS: "l\<in> S"
  and uinS: "u \<in> S" and fS:"finite S" and lS: "\<forall> x\<in> S. l \<sqsubseteq> x" and Su: "\<forall> x\<in> S. x \<sqsubseteq> u"
  shows "(\<exists> s\<in> S. P s) \<or> (\<exists> a \<in> S. \<exists> b \<in> S. (\<forall> y. a \<sqsubset> y \<and> y \<sqsubset> b \<longrightarrow> y \<notin> S) \<and> a \<sqsubset> x \<and> x \<sqsubset> b \<and> P x)"
proof-
  from finite_set_intervals[where P="P", OF px lx xu linS uinS fS lS Su]
  obtain a and b where
    as: "a\<in> S" and bs: "b\<in> S" and noS:"\<forall>y. a \<sqsubset> y \<and> y \<sqsubset> b \<longrightarrow> y \<notin> S"
    and axb: "a \<sqsubseteq> x \<and> x \<sqsubseteq> b \<and> P x"  by auto
  from axb have "x= a \<or> x= b \<or> (a \<sqsubset> x \<and> x \<sqsubset> b)" by (auto simp add: le_less)
  thus ?thesis using px as bs noS by blast
qed

end

text {* Linear order without upper bounds *}

locale linorder_no_ub = Linorder + assumes gt_ex: "\<forall>x. \<exists>y. x \<sqsubset> y"
begin

lemma ge_ex: "\<forall>x. \<exists>y. x \<sqsubseteq> y" using gt_ex by auto

text {* Theorems for @{text "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (P x \<longleftrightarrow> P\<^bsub>+\<infinity>\<^esub>)"} *}
lemma pinf_conj:
  assumes ex1: "\<exists>z1. \<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
  and ex2: "\<exists>z2. \<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. z \<sqsubset>  x \<longrightarrow> ((P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2'))"
proof-
  from ex1 ex2 obtain z1 and z2 where z1: "\<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
     and z2: "\<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')" by blast
  from gt_ex obtain z where z:"max z1 z2 \<sqsubset> z" by blast
  from z have zz1: "z1 \<sqsubset> z" and zz2: "z2 \<sqsubset> z" by simp_all
  {fix x assume H: "z \<sqsubset> x"
    from less_trans[OF zz1 H] less_trans[OF zz2 H]
    have "(P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2')"  using z1 zz1 z2 zz2 by auto
  }
  thus ?thesis by blast
qed

lemma pinf_disj:
  assumes ex1: "\<exists>z1. \<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
  and ex2: "\<exists>z2. \<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. z \<sqsubset>  x \<longrightarrow> ((P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2'))"
proof-
  from ex1 ex2 obtain z1 and z2 where z1: "\<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
     and z2: "\<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')" by blast
  from gt_ex obtain z where z:"max z1 z2 \<sqsubset> z" by blast
  from z have zz1: "z1 \<sqsubset> z" and zz2: "z2 \<sqsubset> z" by simp_all
  {fix x assume H: "z \<sqsubset> x"
    from less_trans[OF zz1 H] less_trans[OF zz2 H]
    have "(P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2')"  using z1 zz1 z2 zz2 by auto
  }
  thus ?thesis by blast
qed

lemma pinf_ex: assumes ex:"\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (P x \<longleftrightarrow> P1)" and p1: P1 shows "\<exists> x. P x"
proof-
  from ex obtain z where z: "\<forall>x. z \<sqsubset> x \<longrightarrow> (P x \<longleftrightarrow> P1)" by blast
  from gt_ex obtain x where x: "z \<sqsubset> x" by blast
  from z x p1 show ?thesis by blast
qed

end

text {* Linear order without upper bounds *}

locale linorder_no_lb = Linorder + assumes lt_ex: "\<forall>x. \<exists>y. y \<sqsubset> x"
begin

lemma le_ex: "\<forall>x. \<exists>y. y \<sqsubseteq> x" using lt_ex by auto


text {* Theorems for @{text "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P\<^bsub>-\<infinity>\<^esub>)"} *}
lemma minf_conj:
  assumes ex1: "\<exists>z1. \<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
  and ex2: "\<exists>z2. \<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. x \<sqsubset>  z \<longrightarrow> ((P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2'))"
proof-
  from ex1 ex2 obtain z1 and z2 where z1: "\<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"and z2: "\<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')" by blast
  from lt_ex obtain z where z:"z \<sqsubset> min z1 z2" by blast
  from z have zz1: "z \<sqsubset> z1" and zz2: "z \<sqsubset> z2" by simp_all
  {fix x assume H: "x \<sqsubset> z"
    from less_trans[OF H zz1] less_trans[OF H zz2]
    have "(P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2')"  using z1 zz1 z2 zz2 by auto
  }
  thus ?thesis by blast
qed

lemma minf_disj:
  assumes ex1: "\<exists>z1. \<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
  and ex2: "\<exists>z2. \<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. x \<sqsubset>  z \<longrightarrow> ((P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2'))"
proof-
  from ex1 ex2 obtain z1 and z2 where z1: "\<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"and z2: "\<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')" by blast
  from lt_ex obtain z where z:"z \<sqsubset> min z1 z2" by blast
  from z have zz1: "z \<sqsubset> z1" and zz2: "z \<sqsubset> z2" by simp_all
  {fix x assume H: "x \<sqsubset> z"
    from less_trans[OF H zz1] less_trans[OF H zz2]
    have "(P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2')"  using z1 zz1 z2 zz2 by auto
  }
  thus ?thesis by blast
qed

lemma minf_ex: assumes ex:"\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P1)" and p1: P1 shows "\<exists> x. P x"
proof-
  from ex obtain z where z: "\<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P1)" by blast
  from lt_ex obtain x where x: "x \<sqsubset> z" by blast
  from z x p1 show ?thesis by blast
qed

end

locale dense_linear_order = linorder_no_lb + linorder_no_ub +
  fixes between
  assumes between_less: "\<forall>x y. x \<sqsubset> y \<longrightarrow> x \<sqsubset> between x y \<and> between x y \<sqsubset> y"
     and  between_same: "\<forall>x. between x x = x"
begin

lemma rinf_U:
  assumes fU: "finite U"
  and lin_dense: "\<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P x
  \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P y )"
  and nmpiU: "\<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. \<exists> u' \<in> U. u \<sqsubseteq> x \<and> x \<sqsubseteq> u')"
  and nmi: "\<not> MP"  and npi: "\<not> PP"  and ex: "\<exists> x.  P x"
  shows "\<exists> u\<in> U. \<exists> u' \<in> U. P (between u u')"
proof-
  from ex obtain x where px: "P x" by blast
  from px nmi npi nmpiU have "\<exists> u\<in> U. \<exists> u' \<in> U. u \<sqsubseteq> x \<and> x \<sqsubseteq> u'" by auto
  then obtain u and u' where uU:"u\<in> U" and uU': "u' \<in> U" and ux:"u \<sqsubseteq> x" and xu':"x \<sqsubseteq> u'" by auto
  from uU have Une: "U \<noteq> {}" by auto
  let ?l = "Min U"
  let ?u = "Max U"
  have linM: "?l \<in> U" using fU Une by simp
  have uinM: "?u \<in> U" using fU Une by simp
  have lM: "\<forall> t\<in> U. ?l \<sqsubseteq> t" using Une fU by auto
  have Mu: "\<forall> t\<in> U. t \<sqsubseteq> ?u" using Une fU by auto
  have th:"?l \<sqsubseteq> u" using uU Une lM by auto
  from order_trans[OF th ux] have lx: "?l \<sqsubseteq> x" .
  have th: "u' \<sqsubseteq> ?u" using uU' Une Mu by simp
  from order_trans[OF xu' th] have xu: "x \<sqsubseteq> ?u" .
  from finite_set_intervals2[where P="P",OF px lx xu linM uinM fU lM Mu]
  have "(\<exists> s\<in> U. P s) \<or>
      (\<exists> t1\<in> U. \<exists> t2 \<in> U. (\<forall> y. t1 \<sqsubset> y \<and> y \<sqsubset> t2 \<longrightarrow> y \<notin> U) \<and> t1 \<sqsubset> x \<and> x \<sqsubset> t2 \<and> P x)" .
  moreover { fix u assume um: "u\<in>U" and pu: "P u"
    have "between u u = u" by (simp add: between_same)
    with um pu have "P (between u u)" by simp
    with um have ?thesis by blast}
  moreover{
    assume "\<exists> t1\<in> U. \<exists> t2 \<in> U. (\<forall> y. t1 \<sqsubset> y \<and> y \<sqsubset> t2 \<longrightarrow> y \<notin> U) \<and> t1 \<sqsubset> x \<and> x \<sqsubset> t2 \<and> P x"
      then obtain t1 and t2 where t1M: "t1 \<in> U" and t2M: "t2\<in> U"
        and noM: "\<forall> y. t1 \<sqsubset> y \<and> y \<sqsubset> t2 \<longrightarrow> y \<notin> U" and t1x: "t1 \<sqsubset> x" and xt2: "x \<sqsubset> t2" and px: "P x"
        by blast
      from less_trans[OF t1x xt2] have t1t2: "t1 \<sqsubset> t2" .
      let ?u = "between t1 t2"
      from between_less t1t2 have t1lu: "t1 \<sqsubset> ?u" and ut2: "?u \<sqsubset> t2" by auto
      from lin_dense[rule_format, OF] noM t1x xt2 px t1lu ut2 have "P ?u" by blast
      with t1M t2M have ?thesis by blast}
    ultimately show ?thesis by blast
  qed

theorem fr_eq:
  assumes fU: "finite U"
  and lin_dense: "\<forall>x l u. (\<forall> t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P x
   \<longrightarrow> (\<forall> y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P y )"
  and nmibnd: "\<forall>x. \<not> MP \<and> P x \<longrightarrow> (\<exists> u\<in> U. u \<sqsubseteq> x)"
  and npibnd: "\<forall>x. \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. x \<sqsubseteq> u)"
  and mi: "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x = MP)"  and pi: "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (P x = PP)"
  shows "(\<exists> x. P x) \<equiv> (MP \<or> PP \<or> (\<exists> u \<in> U. \<exists> u'\<in> U. P (between u u')))"
  (is "_ \<equiv> (_ \<or> _ \<or> ?F)" is "?E \<equiv> ?D")
proof-
 {
   assume px: "\<exists> x. P x"
   have "MP \<or> PP \<or> (\<not> MP \<and> \<not> PP)" by blast
   moreover {assume "MP \<or> PP" hence "?D" by blast}
   moreover {assume nmi: "\<not> MP" and npi: "\<not> PP"
     from npmibnd[OF nmibnd npibnd]
     have nmpiU: "\<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists> u\<in> U. \<exists> u' \<in> U. u \<sqsubseteq> x \<and> x \<sqsubseteq> u')" .
     from rinf_U[OF fU lin_dense nmpiU nmi npi px] have "?D" by blast}
   ultimately have "?D" by blast}
 moreover
 { assume "?D"
   moreover {assume m:"MP" from minf_ex[OF mi m] have "?E" .}
   moreover {assume p: "PP" from pinf_ex[OF pi p] have "?E" . }
   moreover {assume f:"?F" hence "?E" by blast}
   ultimately have "?E" by blast}
 ultimately have "?E = ?D" by blast thus "?E \<equiv> ?D" by simp
qed

lemmas minf_thms = minf_conj minf_disj minf_eq minf_neq minf_lt minf_le minf_gt minf_ge minf_P
lemmas pinf_thms = pinf_conj pinf_disj pinf_eq pinf_neq pinf_lt pinf_le pinf_gt pinf_ge pinf_P

lemmas nmi_thms = nmi_conj nmi_disj nmi_eq nmi_neq nmi_lt nmi_le nmi_gt nmi_ge nmi_P
lemmas npi_thms = npi_conj npi_disj npi_eq npi_neq npi_lt npi_le npi_gt npi_ge npi_P
lemmas lin_dense_thms = lin_dense_conj lin_dense_disj lin_dense_eq lin_dense_neq lin_dense_lt lin_dense_le lin_dense_gt lin_dense_ge lin_dense_P

lemma ferrack_axiom: "dense_linear_order less_eq less between" by fact
lemma atoms: includes meta_term_syntax
  shows "TERM (op \<sqsubset> :: 'a \<Rightarrow> _)" and "TERM (op \<sqsubseteq>)" and "TERM (op = :: 'a \<Rightarrow> _)" .

declare ferrack_axiom [dlo minf: minf_thms pinf: pinf_thms
    nmi: nmi_thms npi: npi_thms lindense:
    lin_dense_thms qe: fr_eq atoms: atoms]

declaration {*
let
fun generic_whatis phi =
 let
  val [lt, le] = map (Morphism.term phi)
   (ProofContext.read_term_pats @{typ "dummy"} @{context} ["op \<sqsubset>", "op \<sqsubseteq>"]) (* FIXME avoid read? *)
  val le = Morphism.term phi @{term "op \<sqsubseteq>"}
  fun h x t =
   case term_of t of
     Const("op =", _)$y$z => if term_of x aconv y then Ferrante_Rackoff_Data.Eq
                            else Ferrante_Rackoff_Data.Nox
   | @{term "Not"}$(Const("op =", _)$y$z) => if term_of x aconv y then Ferrante_Rackoff_Data.NEq
                            else Ferrante_Rackoff_Data.Nox
   | b$y$z => if Term.could_unify (b, lt) then
                 if term_of x aconv y then Ferrante_Rackoff_Data.Lt
                 else if term_of x aconv z then Ferrante_Rackoff_Data.Gt
                 else Ferrante_Rackoff_Data.Nox
             else if Term.could_unify (b, le) then
                 if term_of x aconv y then Ferrante_Rackoff_Data.Le
                 else if term_of x aconv z then Ferrante_Rackoff_Data.Ge
                 else Ferrante_Rackoff_Data.Nox
             else Ferrante_Rackoff_Data.Nox
   | _ => Ferrante_Rackoff_Data.Nox
 in h end
 val ss = K (HOL_ss addsimps [@{thm "not_less"}, @{thm "not_le"}])
in
 Ferrante_Rackoff_Data.funs  @{thm "ferrack_axiom"}
  {isolate_conv = K (K (K Thm.reflexive)), whatis = generic_whatis, simpset = ss}
end
*}

end

use "Tools/Ferrante_Rackoff/ferrante_rackoff.ML"

method_setup dlo = {*
  Method.ctxt_args (Method.SIMPLE_METHOD' o FerranteRackoff.dlo_tac)
*} "Ferrante and Rackoff's algorithm for quantifier elimination in dense linear orders"

end
