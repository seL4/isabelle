(*  Title       : HOL/Decision_Procs/Dense_Linear_Order.thy
    Author      : Amine Chaieb, TU Muenchen
*)

section \<open>Dense linear order without endpoints
  and a quantifier elimination procedure in Ferrante and Rackoff style\<close>

theory Dense_Linear_Order
imports Main
begin

ML_file \<open>langford_data.ML\<close>
ML_file \<open>ferrante_rackoff_data.ML\<close>

context linorder
begin

lemma less_not_permute[no_atp]: "\<not> (x < y \<and> y < x)"
  by (simp add: not_less linear)

lemma gather_simps[no_atp]:
  "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> U. x < y) \<and> x < u \<and> P x) \<longleftrightarrow>
    (\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> (insert u U). x < y) \<and> P x)"
  "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> U. x < y) \<and> l < x \<and> P x) \<longleftrightarrow>
    (\<exists>x. (\<forall>y \<in> (insert l L). y < x) \<and> (\<forall>y \<in> U. x < y) \<and> P x)"
  "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> U. x < y) \<and> x < u) \<longleftrightarrow>
    (\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> (insert u U). x < y))"
  "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> U. x < y) \<and> l < x) \<longleftrightarrow>
    (\<exists>x. (\<forall>y \<in> (insert l L). y < x) \<and> (\<forall>y \<in> U. x < y))"
  by auto

lemma gather_start [no_atp]: "(\<exists>x. P x) \<equiv> (\<exists>x. (\<forall>y \<in> {}. y < x) \<and> (\<forall>y\<in> {}. x < y) \<and> P x)"
  by simp

text\<open>Theorems for \<open>\<exists>z. \<forall>x. x < z \<longrightarrow> (P x \<longleftrightarrow> P\<^sub>-\<^sub>\<infinity>)\<close>\<close>
lemma minf_lt[no_atp]:  "\<exists>z . \<forall>x. x < z \<longrightarrow> (x < t \<longleftrightarrow> True)" by auto
lemma minf_gt[no_atp]: "\<exists>z . \<forall>x. x < z \<longrightarrow>  (t < x \<longleftrightarrow>  False)"
  by (simp add: not_less) (rule exI[where x="t"], auto simp add: less_le)

lemma minf_le[no_atp]: "\<exists>z. \<forall>x. x < z \<longrightarrow> (x \<le> t \<longleftrightarrow> True)" by (auto simp add: less_le)
lemma minf_ge[no_atp]: "\<exists>z. \<forall>x. x < z \<longrightarrow> (t \<le> x \<longleftrightarrow> False)"
  by (auto simp add: less_le not_less not_le)
lemma minf_eq[no_atp]: "\<exists>z. \<forall>x. x < z \<longrightarrow> (x = t \<longleftrightarrow> False)" by auto
lemma minf_neq[no_atp]: "\<exists>z. \<forall>x. x < z \<longrightarrow> (x \<noteq> t \<longleftrightarrow> True)" by auto
lemma minf_P[no_atp]: "\<exists>z. \<forall>x. x < z \<longrightarrow> (P \<longleftrightarrow> P)" by blast

text\<open>Theorems for \<open>\<exists>z. \<forall>x. x < z \<longrightarrow> (P x \<longleftrightarrow> P\<^sub>+\<^sub>\<infinity>)\<close>\<close>
lemma pinf_gt[no_atp]:  "\<exists>z. \<forall>x. z < x \<longrightarrow> (t < x \<longleftrightarrow> True)" by auto
lemma pinf_lt[no_atp]: "\<exists>z. \<forall>x. z < x \<longrightarrow>  (x < t \<longleftrightarrow>  False)"
  by (simp add: not_less) (rule exI[where x="t"], auto simp add: less_le)

lemma pinf_ge[no_atp]: "\<exists>z. \<forall>x. z < x \<longrightarrow> (t \<le> x \<longleftrightarrow> True)" by (auto simp add: less_le)
lemma pinf_le[no_atp]: "\<exists>z. \<forall>x. z < x \<longrightarrow> (x \<le> t \<longleftrightarrow> False)"
  by (auto simp add: less_le not_less not_le)
lemma pinf_eq[no_atp]: "\<exists>z. \<forall>x. z < x \<longrightarrow> (x = t \<longleftrightarrow> False)" by auto
lemma pinf_neq[no_atp]: "\<exists>z. \<forall>x. z < x \<longrightarrow> (x \<noteq> t \<longleftrightarrow> True)" by auto
lemma pinf_P[no_atp]: "\<exists>z. \<forall>x. z < x \<longrightarrow> (P \<longleftrightarrow> P)" by blast

lemma nmi_lt[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> x < t \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)" by auto
lemma nmi_gt[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and> t < x \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)"
  by (auto simp add: le_less)
lemma  nmi_le[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> x\<le> t \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)" by auto
lemma  nmi_ge[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and> t\<le> x \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)" by auto
lemma  nmi_eq[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x = t \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)" by auto
lemma  nmi_neq[no_atp]: "t \<in> U \<Longrightarrow>\<forall>x. \<not>True \<and> x \<noteq> t \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)" by auto
lemma  nmi_P[no_atp]: "\<forall>x. ~P \<and> P \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)" by auto
lemma  nmi_conj[no_atp]: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists>u\<in> U. u \<le> x) ;
  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)\<rbrakk> \<Longrightarrow>
  \<forall>x. \<not>(P1' \<and> P2') \<and> (P1 x \<and> P2 x) \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)" by auto
lemma  nmi_disj[no_atp]: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists>u\<in> U. u \<le> x) ;
  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)\<rbrakk> \<Longrightarrow>
  \<forall>x. \<not>(P1' \<or> P2') \<and> (P1 x \<or> P2 x) \<longrightarrow>  (\<exists>u\<in> U. u \<le> x)" by auto

lemma  npi_lt[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x < t \<longrightarrow>  (\<exists>u\<in> U. x \<le> u)" by (auto simp add: le_less)
lemma  npi_gt[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> t < x \<longrightarrow>  (\<exists>u\<in> U. x \<le> u)" by auto
lemma  npi_le[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x \<le> t \<longrightarrow>  (\<exists>u\<in> U. x \<le> u)" by auto
lemma  npi_ge[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> t \<le> x \<longrightarrow>  (\<exists>u\<in> U. x \<le> u)" by auto
lemma  npi_eq[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>False \<and>  x = t \<longrightarrow>  (\<exists>u\<in> U. x \<le> u)" by auto
lemma  npi_neq[no_atp]: "t \<in> U \<Longrightarrow> \<forall>x. \<not>True \<and> x \<noteq> t \<longrightarrow>  (\<exists>u\<in> U. x \<le> u )" by auto
lemma  npi_P[no_atp]: "\<forall>x. ~P \<and> P \<longrightarrow>  (\<exists>u\<in> U. x \<le> u)" by auto
lemma  npi_conj[no_atp]: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists>u\<in> U. x \<le> u) ;  \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists>u\<in> U. x \<le> u)\<rbrakk>
  \<Longrightarrow>  \<forall>x. \<not>(P1' \<and> P2') \<and> (P1 x \<and> P2 x) \<longrightarrow>  (\<exists>u\<in> U. x \<le> u)" by auto
lemma  npi_disj[no_atp]: "\<lbrakk>\<forall>x. \<not>P1' \<and> P1 x \<longrightarrow>  (\<exists>u\<in> U. x \<le> u) ; \<forall>x. \<not>P2' \<and> P2 x \<longrightarrow>  (\<exists>u\<in> U. x \<le> u)\<rbrakk>
  \<Longrightarrow> \<forall>x. \<not>(P1' \<or> P2') \<and> (P1 x \<or> P2 x) \<longrightarrow>  (\<exists>u\<in> U. x \<le> u)" by auto

lemma lin_dense_lt[no_atp]:
  "t \<in> U \<Longrightarrow>
    \<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> x < t \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> y < t)"
proof clarsimp
  fix x l u y
  assume tU: "t \<in> U"
    and noU: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U"
    and lx: "l < x"
    and xu: "x < u"
    and px: "x < t"
    and ly: "l < y"
    and yu: "y < u"
  from tU noU ly yu have tny: "t \<noteq> y" by auto
  have False if H: "t < y"
  proof -
    from less_trans[OF lx px] less_trans[OF H yu] have "l < t \<and> t < u"
      by simp
    with tU noU show ?thesis
      by auto
  qed
  then have "\<not> t < y"
    by auto
  then have "y \<le> t"
    by (simp add: not_less)
  then show "y < t"
    using tny by (simp add: less_le)
qed

lemma lin_dense_gt[no_atp]:
  "t \<in> U \<Longrightarrow>
    \<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> t < x \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> t < y)"
proof clarsimp
  fix x l u y
  assume tU: "t \<in> U"
    and noU: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U"
    and lx: "l < x"
    and xu: "x < u"
    and px: "t < x"
    and ly: "l < y"
    and yu: "y < u"
  from tU noU ly yu have tny: "t \<noteq> y" by auto
  have False if H: "y < t"
  proof -
    from less_trans[OF ly H] less_trans[OF px xu] have "l < t \<and> t < u"
      by simp
    with tU noU show ?thesis
      by auto
  qed
  then have "\<not> y < t"
    by auto
  then have "t \<le> y"
    by (auto simp add: not_less)
  then show "t < y"
    using tny by (simp add: less_le)
qed

lemma lin_dense_le[no_atp]:
  "t \<in> U \<Longrightarrow>
    \<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> x \<le> t \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> y \<le> t)"
proof clarsimp
  fix x l u y
  assume tU: "t \<in> U"
    and noU: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U"
    and lx: "l < x"
    and xu: "x < u"
    and px: "x \<le> t"
    and ly: "l < y"
    and yu: "y < u"
  from tU noU ly yu have tny: "t \<noteq> y" by auto
  have False if H: "t < y"
  proof -
    from less_le_trans[OF lx px] less_trans[OF H yu]
    have "l < t \<and> t < u" by simp
    with tU noU show ?thesis by auto
  qed
  then have "\<not> t < y" by auto
  then show "y \<le> t" by (simp add: not_less)
qed

lemma lin_dense_ge[no_atp]:
  "t \<in> U \<Longrightarrow>
    \<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> t \<le> x \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> t \<le> y)"
proof clarsimp
  fix x l u y
  assume tU: "t \<in> U"
    and noU: "\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U"
    and lx: "l < x"
    and xu: "x < u"
    and px: "t \<le> x"
    and ly: "l < y"
    and yu: "y < u"
  from tU noU ly yu have tny: "t \<noteq> y" by auto
  have False if H: "y < t"
  proof -
    from less_trans[OF ly H] le_less_trans[OF px xu]
    have "l < t \<and> t < u" by simp
    with tU noU show ?thesis by auto
  qed
  then have "\<not> y < t" by auto
  then show "t \<le> y" by (simp add: not_less)
qed

lemma lin_dense_eq[no_atp]:
  "t \<in> U \<Longrightarrow>
    \<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> x = t \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> y = t)"
  by auto

lemma lin_dense_neq[no_atp]:
  "t \<in> U \<Longrightarrow>
    \<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> x \<noteq> t \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> y \<noteq> t)"
  by auto

lemma lin_dense_P[no_atp]:
  "\<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> P \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> P)"
  by auto

lemma lin_dense_conj[no_atp]:
  "\<lbrakk>\<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> P1 x
  \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> P1 y) ;
  \<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> P2 x
  \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> P2 y)\<rbrakk> \<Longrightarrow>
  \<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> (P1 x \<and> P2 x)
  \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> (P1 y \<and> P2 y))"
  by blast
lemma lin_dense_disj[no_atp]:
  "\<lbrakk>\<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> P1 x
  \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> P1 y) ;
  \<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> P2 x
  \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> P2 y)\<rbrakk> \<Longrightarrow>
  \<forall>x l u. (\<forall>t. l < t \<and> t < u \<longrightarrow> t \<notin> U) \<and> l < x \<and> x < u \<and> (P1 x \<or> P2 x)
  \<longrightarrow> (\<forall>y. l < y \<and> y < u \<longrightarrow> (P1 y \<or> P2 y))"
  by blast

lemma npmibnd[no_atp]: "\<lbrakk>\<forall>x. \<not> MP \<and> P x \<longrightarrow> (\<exists>u\<in> U. u \<le> x); \<forall>x. \<not>PP \<and> P x \<longrightarrow> (\<exists>u\<in> U. x \<le> u)\<rbrakk>
  \<Longrightarrow> \<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists>u\<in> U. \<exists>u' \<in> U. u \<le> x \<and> x \<le> u')"
  by auto

lemma finite_set_intervals[no_atp]:
  assumes px: "P x"
    and lx: "l \<le> x"
    and xu: "x \<le> u"
    and linS: "l\<in> S"
    and uinS: "u \<in> S"
    and fS:"finite S"
    and lS: "\<forall>x\<in> S. l \<le> x"
    and Su: "\<forall>x\<in> S. x \<le> u"
  shows "\<exists>a \<in> S. \<exists>b \<in> S. (\<forall>y. a < y \<and> y < b \<longrightarrow> y \<notin> S) \<and> a \<le> x \<and> x \<le> b \<and> P x"
proof -
  let ?Mx = "{y. y\<in> S \<and> y \<le> x}"
  let ?xM = "{y. y\<in> S \<and> x \<le> y}"
  let ?a = "Max ?Mx"
  let ?b = "Min ?xM"
  have MxS: "?Mx \<subseteq> S"
    by blast
  then have fMx: "finite ?Mx"
    using fS finite_subset by auto
  from lx linS have linMx: "l \<in> ?Mx"
    by blast
  then have Mxne: "?Mx \<noteq> {}"
    by blast
  have xMS: "?xM \<subseteq> S"
    by blast
  then have fxM: "finite ?xM"
    using fS finite_subset by auto
  from xu uinS have linxM: "u \<in> ?xM"
    by blast
  then have xMne: "?xM \<noteq> {}"
    by blast
  have ax: "?a \<le> x"
    using Mxne fMx by auto
  have xb: "x \<le> ?b"
    using xMne fxM by auto
  have "?a \<in> ?Mx"
    using Max_in[OF fMx Mxne] by simp
  then have ainS: "?a \<in> S"
    using MxS by blast
  have "?b \<in> ?xM"
    using Min_in[OF fxM xMne] by simp
  then have binS: "?b \<in> S"
    using xMS by blast
  have noy: "\<forall>y. ?a < y \<and> y < ?b \<longrightarrow> y \<notin> S"
  proof clarsimp
    fix y
    assume ay: "?a < y" and yb: "y < ?b" and yS: "y \<in> S"
    from yS have "y \<in> ?Mx \<or> y \<in> ?xM"
      by (auto simp add: linear)
    then show False
    proof
      assume "y \<in> ?Mx"
      then have "y \<le> ?a"
        using Mxne fMx by auto
      with ay show ?thesis
        by (simp add: not_le[symmetric])
    next
      assume "y \<in> ?xM"
      then have "?b \<le> y"
        using xMne fxM by auto
      with yb show ?thesis
        by (simp add: not_le[symmetric])
    qed
  qed
  from ainS binS noy ax xb px show ?thesis
    by blast
qed

lemma finite_set_intervals2[no_atp]:
  assumes px: "P x"
    and lx: "l \<le> x"
    and xu: "x \<le> u"
    and linS: "l\<in> S"
    and uinS: "u \<in> S"
    and fS: "finite S"
    and lS: "\<forall>x\<in> S. l \<le> x"
    and Su: "\<forall>x\<in> S. x \<le> u"
  shows "(\<exists>s\<in> S. P s) \<or> (\<exists>a \<in> S. \<exists>b \<in> S. (\<forall>y. a < y \<and> y < b \<longrightarrow> y \<notin> S) \<and> a < x \<and> x < b \<and> P x)"
proof -
  from finite_set_intervals[where P="P", OF px lx xu linS uinS fS lS Su]
  obtain a and b where as: "a \<in> S" and bs: "b \<in> S"
    and noS: "\<forall>y. a < y \<and> y < b \<longrightarrow> y \<notin> S"
    and axb: "a \<le> x \<and> x \<le> b \<and> P x"
    by auto
  from axb have "x = a \<or> x = b \<or> (a < x \<and> x < b)"
    by (auto simp add: le_less)
  then show ?thesis
    using px as bs noS by blast
qed

end


section \<open>The classical QE after Langford for dense linear orders\<close>

context unbounded_dense_linorder
begin

lemma interval_empty_iff: "{y. x < y \<and> y < z} = {} \<longleftrightarrow> \<not> x < z"
  by (auto dest: dense)

lemma dlo_qe_bnds[no_atp]:
  assumes ne: "L \<noteq> {}"
    and neU: "U \<noteq> {}"
    and fL: "finite L"
    and fU: "finite U"
  shows "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> U. x < y)) \<equiv> (\<forall>l \<in> L. \<forall>u \<in> U. l < u)"
proof (simp only: atomize_eq, rule iffI)
  assume H: "\<exists>x. (\<forall>y\<in>L. y < x) \<and> (\<forall>y\<in>U. x < y)"
  then obtain x where xL: "\<forall>y\<in>L. y < x" and xU: "\<forall>y\<in>U. x < y"
    by blast
  have "l < u" if l: "l \<in> L" and u: "u \<in> U" for l u
  proof -
    have "l < x" using xL l by blast
    also have "x < u" using xU u by blast
    finally show ?thesis .
  qed
  then show "\<forall>l\<in>L. \<forall>u\<in>U. l < u" by blast
next
  assume H: "\<forall>l\<in>L. \<forall>u\<in>U. l < u"
  let ?ML = "Max L"
  let ?MU = "Min U"
  from fL ne have th1: "?ML \<in> L" and th1': "\<forall>l\<in>L. l \<le> ?ML"
    by auto
  from fU neU have th2: "?MU \<in> U" and th2': "\<forall>u\<in>U. ?MU \<le> u"
    by auto
  from th1 th2 H have "?ML < ?MU"
    by auto
  with dense obtain w where th3: "?ML < w" and th4: "w < ?MU"
    by blast
  from th3 th1' have "\<forall>l \<in> L. l < w"
    by auto
  moreover from th4 th2' have "\<forall>u \<in> U. w < u"
    by auto
  ultimately show "\<exists>x. (\<forall>y\<in>L. y < x) \<and> (\<forall>y\<in>U. x < y)"
    by auto
qed

lemma dlo_qe_noub[no_atp]:
  assumes ne: "L \<noteq> {}"
    and fL: "finite L"
  shows "(\<exists>x. (\<forall>y \<in> L. y < x) \<and> (\<forall>y \<in> {}. x < y)) \<equiv> True"
proof (simp add: atomize_eq)
  from gt_ex[of "Max L"] obtain M where M: "Max L < M"
    by blast
  from ne fL have "\<forall>x \<in> L. x \<le> Max L"
    by simp
  with M have "\<forall>x\<in>L. x < M"
    by (auto intro: le_less_trans)
  then show "\<exists>x. \<forall>y\<in>L. y < x"
    by blast
qed

lemma dlo_qe_nolb[no_atp]:
  assumes ne: "U \<noteq> {}"
    and fU: "finite U"
  shows "(\<exists>x. (\<forall>y \<in> {}. y < x) \<and> (\<forall>y \<in> U. x < y)) \<equiv> True"
proof (simp add: atomize_eq)
  from lt_ex[of "Min U"] obtain M where M: "M < Min U"
    by blast
  from ne fU have "\<forall>x \<in> U. Min U \<le> x"
    by simp
  with M have "\<forall>x\<in>U. M < x"
    by (auto intro: less_le_trans)
  then show "\<exists>x. \<forall>y\<in>U. x < y"
    by blast
qed

lemma exists_neq[no_atp]: "\<exists>(x::'a). x \<noteq> t" "\<exists>(x::'a). t \<noteq> x"
  using gt_ex[of t] by auto

lemmas dlo_simps[no_atp] = order_refl less_irrefl not_less not_le exists_neq
  le_less neq_iff linear less_not_permute

lemma axiom[no_atp]: "class.unbounded_dense_linorder (\<le>) (<)"
  by (rule unbounded_dense_linorder_axioms)
lemma atoms[no_atp]:
  shows "TERM (less :: 'a \<Rightarrow> _)"
    and "TERM (less_eq :: 'a \<Rightarrow> _)"
    and "TERM ((=) :: 'a \<Rightarrow> _)" .

declare axiom[langford qe: dlo_qe_bnds dlo_qe_nolb dlo_qe_noub gather: gather_start gather_simps atoms: atoms]
declare dlo_simps[langfordsimp]

end

(* FIXME: Move to HOL -- together with the conj_aci_rule in langford.ML *)
lemmas dnf[no_atp] = conj_disj_distribL conj_disj_distribR

lemmas weak_dnf_simps[no_atp] = simp_thms dnf

lemma nnf_simps[no_atp]:
  "(\<not> (P \<and> Q)) \<longleftrightarrow> (\<not> P \<or> \<not> Q)"
  "(\<not> (P \<or> Q)) \<longleftrightarrow> (\<not> P \<and> \<not> Q)"
  "(P \<longrightarrow> Q) \<longleftrightarrow> (\<not> P \<or> Q)"
  "(P \<longleftrightarrow> Q) \<longleftrightarrow> ((P \<and> Q) \<or> (\<not> P \<and> \<not> Q))"
  "(\<not> \<not> P) \<longleftrightarrow> P"
  by blast+

lemma ex_distrib[no_atp]: "(\<exists>x. P x \<or> Q x) \<longleftrightarrow> ((\<exists>x. P x) \<or> (\<exists>x. Q x))"
  by blast

lemmas dnf_simps[no_atp] = weak_dnf_simps nnf_simps ex_distrib

ML_file \<open>langford.ML\<close>
method_setup dlo = \<open>
  Scan.succeed (SIMPLE_METHOD' o Langford.dlo_tac)
\<close> "Langford's algorithm for quantifier elimination in dense linear orders"


section \<open>Contructive dense linear orders yield QE for linear arithmetic over ordered Fields\<close>

text \<open>Linear order without upper bounds\<close>

locale linorder_stupid_syntax = linorder
begin

notation
  less_eq  ("'(\<sqsubseteq>')") and
  less_eq  ("(_/ \<sqsubseteq> _)" [51, 51] 50) and
  less  ("'(\<sqsubset>')") and
  less  ("(_/ \<sqsubset> _)"  [51, 51] 50)

end

locale linorder_no_ub = linorder_stupid_syntax +
  assumes gt_ex: "\<exists>y. less x y"
begin

lemma ge_ex[no_atp]: "\<exists>y. x \<sqsubseteq> y"
  using gt_ex by auto

text \<open>Theorems for \<open>\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (P x \<longleftrightarrow> P\<^sub>+\<^sub>\<infinity>)\<close>\<close>
lemma pinf_conj[no_atp]:
  assumes ex1: "\<exists>z1. \<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
    and ex2: "\<exists>z2. \<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. z \<sqsubset>  x \<longrightarrow> ((P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2'))"
proof -
  from ex1 ex2 obtain z1 and z2
    where z1: "\<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
    and z2: "\<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
    by blast
  from gt_ex obtain z where z:"ord.max less_eq z1 z2 \<sqsubset> z"
    by blast
  from z have zz1: "z1 \<sqsubset> z" and zz2: "z2 \<sqsubset> z"
    by simp_all
  have "(P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2')" if H: "z \<sqsubset> x" for x
    using less_trans[OF zz1 H] less_trans[OF zz2 H] z1 zz1 z2 zz2 by auto
  then show ?thesis
    by blast
qed

lemma pinf_disj[no_atp]:
  assumes ex1: "\<exists>z1. \<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
    and ex2: "\<exists>z2. \<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. z \<sqsubset>  x \<longrightarrow> ((P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2'))"
proof-
  from ex1 ex2 obtain z1 and z2
    where z1: "\<forall>x. z1 \<sqsubset> x \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
    and z2: "\<forall>x. z2 \<sqsubset> x \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
    by blast
  from gt_ex obtain z where z: "ord.max less_eq z1 z2 \<sqsubset> z"
    by blast
  from z have zz1: "z1 \<sqsubset> z" and zz2: "z2 \<sqsubset> z"
    by simp_all
  have "(P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2')" if H: "z \<sqsubset> x" for x
    using less_trans[OF zz1 H] less_trans[OF zz2 H] z1 zz1 z2 zz2 by auto
  then show ?thesis
    by blast
qed

lemma pinf_ex[no_atp]:
  assumes ex: "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (P x \<longleftrightarrow> P1)"
    and p1: P1
  shows "\<exists>x. P x"
proof -
  from ex obtain z where z: "\<forall>x. z \<sqsubset> x \<longrightarrow> (P x \<longleftrightarrow> P1)"
    by blast
  from gt_ex obtain x where x: "z \<sqsubset> x"
    by blast
  from z x p1 show ?thesis
    by blast
qed

end

text \<open>Linear order without upper bounds\<close>

locale linorder_no_lb = linorder_stupid_syntax +
  assumes lt_ex: "\<exists>y. less y x"
begin

lemma le_ex[no_atp]: "\<exists>y. y \<sqsubseteq> x"
  using lt_ex by auto


text \<open>Theorems for \<open>\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P\<^sub>-\<^sub>\<infinity>)\<close>\<close>
lemma minf_conj[no_atp]:
  assumes ex1: "\<exists>z1. \<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
    and ex2: "\<exists>z2. \<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. x \<sqsubset>  z \<longrightarrow> ((P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2'))"
proof -
  from ex1 ex2 obtain z1 and z2
    where z1: "\<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
    and z2: "\<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
    by blast
  from lt_ex obtain z where z: "z \<sqsubset> ord.min less_eq z1 z2"
    by blast
  from z have zz1: "z \<sqsubset> z1" and zz2: "z \<sqsubset> z2"
    by simp_all
  have "(P1 x \<and> P2 x) \<longleftrightarrow> (P1' \<and> P2')" if H: "x \<sqsubset> z" for x
    using less_trans[OF H zz1] less_trans[OF H zz2] z1 zz1 z2 zz2 by auto
  then show ?thesis
    by blast
qed

lemma minf_disj[no_atp]:
  assumes ex1: "\<exists>z1. \<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
    and ex2: "\<exists>z2. \<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
  shows "\<exists>z. \<forall>x. x \<sqsubset>  z \<longrightarrow> ((P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2'))"
proof -
  from ex1 ex2 obtain z1 and z2
    where z1: "\<forall>x. x \<sqsubset> z1 \<longrightarrow> (P1 x \<longleftrightarrow> P1')"
    and z2: "\<forall>x. x \<sqsubset> z2 \<longrightarrow> (P2 x \<longleftrightarrow> P2')"
    by blast
  from lt_ex obtain z where z: "z \<sqsubset> ord.min less_eq z1 z2"
    by blast
  from z have zz1: "z \<sqsubset> z1" and zz2: "z \<sqsubset> z2"
    by simp_all
  have "(P1 x \<or> P2 x) \<longleftrightarrow> (P1' \<or> P2')" if H: "x \<sqsubset> z" for x
    using less_trans[OF H zz1] less_trans[OF H zz2] z1 zz1 z2 zz2 by auto
  then show ?thesis
    by blast
qed

lemma minf_ex[no_atp]:
  assumes ex: "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P1)"
    and p1: P1
  shows "\<exists>x. P x"
proof -
  from ex obtain z where z: "\<forall>x. x \<sqsubset> z \<longrightarrow> (P x \<longleftrightarrow> P1)"
    by blast
  from lt_ex obtain x where x: "x \<sqsubset> z"
    by blast
  from z x p1 show ?thesis
    by blast
qed

end


locale constr_dense_linorder = linorder_no_lb + linorder_no_ub +
  fixes between
  assumes between_less: "less x y \<Longrightarrow> less x (between x y) \<and> less (between x y) y"
    and between_same: "between x x = x"
begin

sublocale dlo: unbounded_dense_linorder
proof (unfold_locales, goal_cases)
  case (1 x y)
  then show ?case
    using between_less [of x y] by auto
next
  case 2
  then show ?case by (rule lt_ex)
next
  case 3
  then show ?case by (rule gt_ex)
qed

lemma rinf_U[no_atp]:
  assumes fU: "finite U"
    and lin_dense: "\<forall>x l u. (\<forall>t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P x
      \<longrightarrow> (\<forall>y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P y )"
    and nmpiU: "\<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists>u\<in> U. \<exists>u' \<in> U. u \<sqsubseteq> x \<and> x \<sqsubseteq> u')"
    and nmi: "\<not> MP"  and npi: "\<not> PP"  and ex: "\<exists>x.  P x"
  shows "\<exists>u\<in> U. \<exists>u' \<in> U. P (between u u')"
proof -
  from ex obtain x where px: "P x"
    by blast
  from px nmi npi nmpiU have "\<exists>u\<in> U. \<exists>u' \<in> U. u \<sqsubseteq> x \<and> x \<sqsubseteq> u'"
    by auto
  then obtain u and u' where uU: "u\<in> U" and uU': "u' \<in> U" and ux: "u \<sqsubseteq> x" and xu': "x \<sqsubseteq> u'"
    by auto
  from uU have Une: "U \<noteq> {}"
    by auto
  let ?l = "linorder.Min less_eq U"
  let ?u = "linorder.Max less_eq U"
  have linM: "?l \<in> U"
    using fU Une by simp
  have uinM: "?u \<in> U"
    using fU Une by simp
  have lM: "\<forall>t\<in> U. ?l \<sqsubseteq> t"
    using Une fU by auto
  have Mu: "\<forall>t\<in> U. t \<sqsubseteq> ?u"
    using Une fU by auto
  have th: "?l \<sqsubseteq> u"
    using uU Une lM by auto
  from order_trans[OF th ux] have lx: "?l \<sqsubseteq> x" .
  have th: "u' \<sqsubseteq> ?u"
    using uU' Une Mu by simp
  from order_trans[OF xu' th] have xu: "x \<sqsubseteq> ?u" .
  from finite_set_intervals2[where P="P",OF px lx xu linM uinM fU lM Mu]
  consider u where "u \<in> U" "P u" |
    t1 t2 where "t1 \<in> U" "t2 \<in> U" "\<forall>y. t1 \<sqsubset> y \<and> y \<sqsubset> t2 \<longrightarrow> y \<notin> U" "t1 \<sqsubset> x" "x \<sqsubset> t2" "P x"
    by blast
  then show ?thesis
  proof cases
    case u: 1
    have "between u u = u" by (simp add: between_same)
    with u have "P (between u u)" by simp
    with u show ?thesis by blast
  next
    case 2
    note t1M = \<open>t1 \<in> U\<close> and t2M = \<open>t2\<in> U\<close>
      and noM = \<open>\<forall>y. t1 \<sqsubset> y \<and> y \<sqsubset> t2 \<longrightarrow> y \<notin> U\<close>
      and t1x = \<open>t1 \<sqsubset> x\<close> and xt2 = \<open>x \<sqsubset> t2\<close>
      and px = \<open>P x\<close>
    from less_trans[OF t1x xt2] have t1t2: "t1 \<sqsubset> t2" .
    let ?u = "between t1 t2"
    from between_less t1t2 have t1lu: "t1 \<sqsubset> ?u" and ut2: "?u \<sqsubset> t2" by auto
    from lin_dense noM t1x xt2 px t1lu ut2 have "P ?u" by blast
    with t1M t2M show ?thesis by blast
  qed
qed

theorem fr_eq[no_atp]:
  assumes fU: "finite U"
    and lin_dense: "\<forall>x l u. (\<forall>t. l \<sqsubset> t \<and> t\<sqsubset> u \<longrightarrow> t \<notin> U) \<and> l\<sqsubset> x \<and> x \<sqsubset> u \<and> P x
     \<longrightarrow> (\<forall>y. l \<sqsubset> y \<and> y \<sqsubset> u \<longrightarrow> P y )"
    and nmibnd: "\<forall>x. \<not> MP \<and> P x \<longrightarrow> (\<exists>u\<in> U. u \<sqsubseteq> x)"
    and npibnd: "\<forall>x. \<not>PP \<and> P x \<longrightarrow> (\<exists>u\<in> U. x \<sqsubseteq> u)"
    and mi: "\<exists>z. \<forall>x. x \<sqsubset> z \<longrightarrow> (P x = MP)"  and pi: "\<exists>z. \<forall>x. z \<sqsubset> x \<longrightarrow> (P x = PP)"
  shows "(\<exists>x. P x) \<equiv> (MP \<or> PP \<or> (\<exists>u \<in> U. \<exists>u'\<in> U. P (between u u')))"
  (is "_ \<equiv> (_ \<or> _ \<or> ?F)" is "?E \<equiv> ?D")
proof -
  have "?E \<longleftrightarrow> ?D"
  proof
    show ?D if px: ?E
    proof -
      consider "MP \<or> PP" | "\<not> MP" "\<not> PP" by blast
      then show ?thesis
      proof cases
        case 1
        then show ?thesis by blast
      next
        case 2
        from npmibnd[OF nmibnd npibnd]
        have nmpiU: "\<forall>x. \<not> MP \<and> \<not>PP \<and> P x \<longrightarrow> (\<exists>u\<in> U. \<exists>u' \<in> U. u \<sqsubseteq> x \<and> x \<sqsubseteq> u')" .
        from rinf_U[OF fU lin_dense nmpiU \<open>\<not> MP\<close> \<open>\<not> PP\<close> px] show ?thesis
          by blast
      qed
    qed
    show ?E if ?D
    proof -
      from that consider MP | PP | ?F by blast
      then show ?thesis
      proof cases
        case 1
        from minf_ex[OF mi this] show ?thesis .
      next
        case 2
        from pinf_ex[OF pi this] show ?thesis .
      next
        case 3
        then show ?thesis by blast
      qed
    qed
  qed
  then show "?E \<equiv> ?D" by simp
qed

lemmas minf_thms[no_atp] = minf_conj minf_disj minf_eq minf_neq minf_lt minf_le minf_gt minf_ge minf_P
lemmas pinf_thms[no_atp] = pinf_conj pinf_disj pinf_eq pinf_neq pinf_lt pinf_le pinf_gt pinf_ge pinf_P

lemmas nmi_thms[no_atp] = nmi_conj nmi_disj nmi_eq nmi_neq nmi_lt nmi_le nmi_gt nmi_ge nmi_P
lemmas npi_thms[no_atp] = npi_conj npi_disj npi_eq npi_neq npi_lt npi_le npi_gt npi_ge npi_P
lemmas lin_dense_thms[no_atp] = lin_dense_conj lin_dense_disj lin_dense_eq lin_dense_neq lin_dense_lt lin_dense_le lin_dense_gt lin_dense_ge lin_dense_P

lemma ferrack_axiom[no_atp]: "constr_dense_linorder less_eq less between"
  by (rule constr_dense_linorder_axioms)

lemma atoms[no_atp]:
  shows "TERM (less :: 'a \<Rightarrow> _)"
    and "TERM (less_eq :: 'a \<Rightarrow> _)"
    and "TERM ((=) :: 'a \<Rightarrow> _)" .

declare ferrack_axiom [ferrack minf: minf_thms pinf: pinf_thms
    nmi: nmi_thms npi: npi_thms lindense:
    lin_dense_thms qe: fr_eq atoms: atoms]

declaration \<open>
let
  fun simps phi = map (Morphism.thm phi) [@{thm "not_less"}, @{thm "not_le"}]
  fun generic_whatis phi =
    let
      val [lt, le] = map (Morphism.term phi) [\<^term>\<open>(\<sqsubset>)\<close>, \<^term>\<open>(\<sqsubseteq>)\<close>]
      fun h x t =
        case Thm.term_of t of
          \<^Const_>\<open>HOL.eq _ for y z\<close> =>
            if Thm.term_of x aconv y then Ferrante_Rackoff_Data.Eq
            else Ferrante_Rackoff_Data.Nox
       | \<^Const_>\<open>Not for \<^Const>\<open>HOL.eq _ for y z\<close>\<close> =>
            if Thm.term_of x aconv y then Ferrante_Rackoff_Data.NEq
            else Ferrante_Rackoff_Data.Nox
       | b$y$z => if Term.could_unify (b, lt) then
                     if Thm.term_of x aconv y then Ferrante_Rackoff_Data.Lt
                     else if Thm.term_of x aconv z then Ferrante_Rackoff_Data.Gt
                     else Ferrante_Rackoff_Data.Nox
                 else if Term.could_unify (b, le) then
                     if Thm.term_of x aconv y then Ferrante_Rackoff_Data.Le
                     else if Thm.term_of x aconv z then Ferrante_Rackoff_Data.Ge
                     else Ferrante_Rackoff_Data.Nox
                 else Ferrante_Rackoff_Data.Nox
       | _ => Ferrante_Rackoff_Data.Nox
  in h end
  fun ss phi ctxt =
    simpset_of (put_simpset HOL_ss ctxt addsimps (simps phi))
in
  Ferrante_Rackoff_Data.funs  @{thm "ferrack_axiom"}
    {isolate_conv = K (K (K Thm.reflexive)), whatis = generic_whatis, simpset = ss}
end
\<close>

end

ML_file \<open>ferrante_rackoff.ML\<close>

method_setup ferrack = \<open>
  Scan.succeed (SIMPLE_METHOD' o FerranteRackoff.dlo_tac)
\<close> "Ferrante and Rackoff's algorithm for quantifier elimination in dense linear orders"


subsection \<open>Ferrante and Rackoff algorithm over ordered fields\<close>

lemma neg_prod_lt:
  fixes c :: "'a::linordered_field"
  assumes "c < 0"
  shows "c * x < 0 \<equiv> x > 0"
proof -
  have "c * x < 0 \<longleftrightarrow> 0 / c < x"
    by (simp only: neg_divide_less_eq[OF \<open>c < 0\<close>] algebra_simps)
  also have "\<dots> \<longleftrightarrow> 0 < x" by simp
  finally show "PROP ?thesis" by simp
qed

lemma pos_prod_lt:
  fixes c :: "'a::linordered_field"
  assumes "c > 0"
  shows "c * x < 0 \<equiv> x < 0"
proof -
  have "c * x < 0 \<longleftrightarrow> 0 /c > x"
    by (simp only: pos_less_divide_eq[OF \<open>c > 0\<close>] algebra_simps)
  also have "\<dots> \<longleftrightarrow> 0 > x" by simp
  finally show "PROP ?thesis" by simp
qed

lemma neg_prod_sum_lt:
  fixes c :: "'a::linordered_field"
  assumes "c < 0"
  shows "c * x + t < 0 \<equiv> x > (- 1 / c) * t"
proof -
  have "c * x + t < 0 \<longleftrightarrow> c * x < - t"
    by (subst less_iff_diff_less_0 [of "c * x" "- t"]) simp
  also have "\<dots> \<longleftrightarrow> - t / c < x"
    by (simp only: neg_divide_less_eq[OF \<open>c < 0\<close>] algebra_simps)
  also have "\<dots> \<longleftrightarrow> (- 1 / c) * t < x" by simp
  finally show "PROP ?thesis" by simp
qed

lemma pos_prod_sum_lt:
  fixes c :: "'a::linordered_field"
  assumes "c > 0"
  shows "c * x + t < 0 \<equiv> x < (- 1 / c) * t"
proof -
  have "c * x + t < 0 \<longleftrightarrow> c * x < - t"
    by (subst less_iff_diff_less_0 [of "c * x" "- t"]) simp
  also have "\<dots> \<longleftrightarrow> - t / c > x"
    by (simp only: pos_less_divide_eq[OF \<open>c > 0\<close>] algebra_simps)
  also have "\<dots> \<longleftrightarrow> (- 1 / c) * t > x" by simp
  finally show "PROP ?thesis" by simp
qed

lemma sum_lt:
  fixes x :: "'a::ordered_ab_group_add"
  shows "x + t < 0 \<equiv> x < - t"
  using less_diff_eq[where a= x and b=t and c=0] by simp

lemma neg_prod_le:
  fixes c :: "'a::linordered_field"
  assumes "c < 0"
  shows "c * x \<le> 0 \<equiv> x \<ge> 0"
proof -
  have "c * x \<le> 0 \<longleftrightarrow> 0 / c \<le> x"
    by (simp only: neg_divide_le_eq[OF \<open>c < 0\<close>] algebra_simps)
  also have "\<dots> \<longleftrightarrow> 0 \<le> x" by simp
  finally show "PROP ?thesis" by simp
qed

lemma pos_prod_le:
  fixes c :: "'a::linordered_field"
  assumes "c > 0"
  shows "c * x \<le> 0 \<equiv> x \<le> 0"
proof -
  have "c * x \<le> 0 \<longleftrightarrow> 0 / c \<ge> x"
    by (simp only: pos_le_divide_eq[OF \<open>c > 0\<close>] algebra_simps)
  also have "\<dots> \<longleftrightarrow> 0 \<ge> x" by simp
  finally show "PROP ?thesis" by simp
qed

lemma neg_prod_sum_le:
  fixes c :: "'a::linordered_field"
  assumes "c < 0"
  shows "c * x + t \<le> 0 \<equiv> x \<ge> (- 1 / c) * t"
proof -
  have "c * x + t \<le> 0 \<longleftrightarrow> c * x \<le> -t"
    by (subst le_iff_diff_le_0 [of "c*x" "-t"]) simp
  also have "\<dots> \<longleftrightarrow> - t / c \<le> x"
    by (simp only: neg_divide_le_eq[OF \<open>c < 0\<close>] algebra_simps)
  also have "\<dots> \<longleftrightarrow> (- 1 / c) * t \<le> x" by simp
  finally show "PROP ?thesis" by simp
qed

lemma pos_prod_sum_le:
  fixes c :: "'a::linordered_field"
  assumes "c > 0"
  shows "c * x + t \<le> 0 \<equiv> x \<le> (- 1 / c) * t"
proof -
  have "c * x + t \<le> 0 \<longleftrightarrow> c * x \<le> - t"
    by (subst le_iff_diff_le_0 [of "c*x" "-t"]) simp
  also have "\<dots> \<longleftrightarrow> - t / c \<ge> x"
    by (simp only: pos_le_divide_eq[OF \<open>c > 0\<close>] algebra_simps)
  also have "\<dots> \<longleftrightarrow> (- 1 / c) * t \<ge> x" by simp
  finally show "PROP ?thesis" by simp
qed

lemma sum_le:
  fixes x :: "'a::ordered_ab_group_add"
  shows "x + t \<le> 0 \<equiv> x \<le> - t"
  using le_diff_eq[where a= x and b=t and c=0] by simp

lemma nz_prod_eq:
  fixes c :: "'a::linordered_field"
  assumes "c \<noteq> 0"
  shows "c * x = 0 \<equiv> x = 0"
  using assms by simp

lemma nz_prod_sum_eq:
  fixes c :: "'a::linordered_field"
  assumes "c \<noteq> 0"
  shows "c * x + t = 0 \<equiv> x = (- 1/c) * t"
proof -
  have "c * x + t = 0 \<longleftrightarrow> c * x = - t"
    by (subst eq_iff_diff_eq_0 [of "c*x" "-t"]) simp
  also have "\<dots> \<longleftrightarrow> x = - t / c"
    by (simp only: nonzero_eq_divide_eq[OF \<open>c \<noteq> 0\<close>] algebra_simps)
  finally show "PROP ?thesis" by simp
qed

lemma sum_eq:
  fixes x :: "'a::ordered_ab_group_add"
  shows "x + t = 0 \<equiv> x = - t"
  using eq_diff_eq[where a= x and b=t and c=0] by simp

interpretation class_dense_linordered_field: constr_dense_linorder
  "(\<le>)" "(<)" "\<lambda>x y. 1/2 * ((x::'a::linordered_field) + y)"
  by unfold_locales (dlo, dlo, auto)

declaration \<open>
let
  fun earlier [] _ = false
    | earlier (h::t) (x, y) =
        if h aconvc y then false else if h aconvc x then true else earlier t (x, y);

  fun earlier_ord vs (x, y) =
    if x aconvc y then EQUAL
    else if earlier vs (x, y) then LESS
    else GREATER;

fun dest_frac ct =
  case Thm.term_of ct of
    \<^Const_>\<open>Rings.divide _ for a b\<close> =>
      Rat.make (snd (HOLogic.dest_number a), snd (HOLogic.dest_number b))
  | \<^Const_>\<open>inverse _ for a\<close> => Rat.make(1, HOLogic.dest_number a |> snd)
  | t => Rat.of_int (snd (HOLogic.dest_number t))

fun whatis x ct = case Thm.term_of ct of
  \<^Const_>\<open>plus _ for \<^Const_>\<open>times _ for _ y\<close> _\<close> =>
     if y aconv Thm.term_of x then ("c*x+t",[(funpow 2 Thm.dest_arg1) ct, Thm.dest_arg ct])
     else ("Nox",[])
| \<^Const_>\<open>plus _ for y _\<close> =>
     if y aconv Thm.term_of x then ("x+t",[Thm.dest_arg ct])
     else ("Nox",[])
| \<^Const_>\<open>times _ for _ y\<close> =>
     if y aconv Thm.term_of x then ("c*x",[Thm.dest_arg1 ct])
     else ("Nox",[])
| t => if t aconv Thm.term_of x then ("x",[]) else ("Nox",[]);

fun xnormalize_conv ctxt [] ct = Thm.reflexive ct
  | xnormalize_conv ctxt (vs as (x::_)) ct =
   case Thm.term_of ct of
   \<^Const_>\<open>less _ for _ \<^Const_>\<open>zero_class.zero _\<close>\<close> =>
    (case whatis x (Thm.dest_arg1 ct) of
    ("c*x+t",[c,t]) =>
       let
        val cr = dest_frac c
        val clt = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val neg = cr < @0
        val cthp = Simplifier.rewrite ctxt
               (Thm.apply \<^cterm>\<open>Trueprop\<close>
                  (if neg then Thm.apply (Thm.apply clt c) cz
                    else Thm.apply (Thm.apply clt cz) c))
        val cth = Thm.equal_elim (Thm.symmetric cthp) TrueI
        val th = Thm.implies_elim (Thm.instantiate' [SOME (Thm.ctyp_of_cterm x)] (map SOME [c,x,t])
             (if neg then @{thm neg_prod_sum_lt} else @{thm pos_prod_sum_lt})) cth
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
                   (Semiring_Normalizer.semiring_normalize_ord_conv ctxt (earlier_ord vs)))) th
      in rth end
    | ("x+t",[t]) =>
       let
        val T = Thm.ctyp_of_cterm x
        val th = Thm.instantiate' [SOME T] [SOME x, SOME t] @{thm "sum_lt"}
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
              (Semiring_Normalizer.semiring_normalize_ord_conv ctxt (earlier_ord vs)))) th
       in  rth end
    | ("c*x",[c]) =>
       let
        val cr = dest_frac c
        val clt = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val neg = cr < @0
        val cthp = Simplifier.rewrite ctxt
               (Thm.apply \<^cterm>\<open>Trueprop\<close>
                  (if neg then Thm.apply (Thm.apply clt c) cz
                    else Thm.apply (Thm.apply clt cz) c))
        val cth = Thm.equal_elim (Thm.symmetric cthp) TrueI
        val th = Thm.implies_elim (Thm.instantiate' [SOME (Thm.ctyp_of_cterm x)] (map SOME [c,x])
             (if neg then @{thm neg_prod_lt} else @{thm pos_prod_lt})) cth
        val rth = th
      in rth end
    | _ => Thm.reflexive ct)


|  \<^Const_>\<open>less_eq _ for _ \<^Const_>\<open>zero_class.zero _\<close>\<close> =>
   (case whatis x (Thm.dest_arg1 ct) of
    ("c*x+t",[c,t]) =>
       let
        val T = Thm.typ_of_cterm x
        val cT = Thm.ctyp_of_cterm x
        val cr = dest_frac c
        val clt = Thm.cterm_of ctxt \<^Const>\<open>less T\<close>
        val cz = Thm.dest_arg ct
        val neg = cr < @0
        val cthp = Simplifier.rewrite ctxt
               (Thm.apply \<^cterm>\<open>Trueprop\<close>
                  (if neg then Thm.apply (Thm.apply clt c) cz
                    else Thm.apply (Thm.apply clt cz) c))
        val cth = Thm.equal_elim (Thm.symmetric cthp) TrueI
        val th = Thm.implies_elim (Thm.instantiate' [SOME cT] (map SOME [c,x,t])
             (if neg then @{thm neg_prod_sum_le} else @{thm pos_prod_sum_le})) cth
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
                   (Semiring_Normalizer.semiring_normalize_ord_conv ctxt (earlier_ord vs)))) th
      in rth end
    | ("x+t",[t]) =>
       let
        val T = Thm.ctyp_of_cterm x
        val th = Thm.instantiate' [SOME T] [SOME x, SOME t] @{thm "sum_le"}
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
              (Semiring_Normalizer.semiring_normalize_ord_conv ctxt (earlier_ord vs)))) th
       in  rth end
    | ("c*x",[c]) =>
       let
        val T = Thm.typ_of_cterm x
        val cT = Thm.ctyp_of_cterm x
        val cr = dest_frac c
        val clt = Thm.cterm_of ctxt \<^Const>\<open>less T\<close>
        val cz = Thm.dest_arg ct
        val neg = cr < @0
        val cthp = Simplifier.rewrite ctxt
               (Thm.apply \<^cterm>\<open>Trueprop\<close>
                  (if neg then Thm.apply (Thm.apply clt c) cz
                    else Thm.apply (Thm.apply clt cz) c))
        val cth = Thm.equal_elim (Thm.symmetric cthp) TrueI
        val th = Thm.implies_elim (Thm.instantiate' [SOME (Thm.ctyp_of_cterm x)] (map SOME [c,x])
             (if neg then @{thm neg_prod_le} else @{thm pos_prod_le})) cth
        val rth = th
      in rth end
    | _ => Thm.reflexive ct)

|  \<^Const_>\<open>HOL.eq _ for _ \<^Const_>\<open>zero_class.zero _\<close>\<close> =>
   (case whatis x (Thm.dest_arg1 ct) of
    ("c*x+t",[c,t]) =>
       let
        val T = Thm.ctyp_of_cterm x
        val cr = dest_frac c
        val ceq = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val cthp = Simplifier.rewrite ctxt
            (Thm.apply \<^cterm>\<open>Trueprop\<close>
             (Thm.apply \<^cterm>\<open>Not\<close> (Thm.apply (Thm.apply ceq c) cz)))
        val cth = Thm.equal_elim (Thm.symmetric cthp) TrueI
        val th = Thm.implies_elim
                 (Thm.instantiate' [SOME T] (map SOME [c,x,t]) @{thm nz_prod_sum_eq}) cth
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
                   (Semiring_Normalizer.semiring_normalize_ord_conv ctxt (earlier_ord vs)))) th
      in rth end
    | ("x+t",[t]) =>
       let
        val T = Thm.ctyp_of_cterm x
        val th = Thm.instantiate' [SOME T] [SOME x, SOME t] @{thm "sum_eq"}
        val rth = Conv.fconv_rule (Conv.arg_conv (Conv.binop_conv
              (Semiring_Normalizer.semiring_normalize_ord_conv ctxt (earlier_ord vs)))) th
       in  rth end
    | ("c*x",[c]) =>
       let
        val T = Thm.ctyp_of_cterm x
        val cr = dest_frac c
        val ceq = Thm.dest_fun2 ct
        val cz = Thm.dest_arg ct
        val cthp = Simplifier.rewrite ctxt
            (Thm.apply \<^cterm>\<open>Trueprop\<close>
             (Thm.apply \<^cterm>\<open>Not\<close> (Thm.apply (Thm.apply ceq c) cz)))
        val cth = Thm.equal_elim (Thm.symmetric cthp) TrueI
        val rth = Thm.implies_elim
                 (Thm.instantiate' [SOME T] (map SOME [c,x]) @{thm nz_prod_eq}) cth
      in rth end
    | _ => Thm.reflexive ct);

local
  val less_iff_diff_less_0 = mk_meta_eq @{thm "less_iff_diff_less_0"}
  val le_iff_diff_le_0 = mk_meta_eq @{thm "le_iff_diff_le_0"}
  val eq_iff_diff_eq_0 = mk_meta_eq @{thm "eq_iff_diff_eq_0"}
  val ss = simpset_of \<^context>
in
fun field_isolate_conv phi ctxt vs ct = case Thm.term_of ct of
  \<^Const_>\<open>less _ for a b\<close> =>
   let val (ca,cb) = Thm.dest_binop ct
       val T = Thm.ctyp_of_cterm ca
       val th = Thm.instantiate' [SOME T] [SOME ca, SOME cb] less_iff_diff_less_0
       val nth = Conv.fconv_rule
         (Conv.arg_conv (Conv.arg1_conv
              (Semiring_Normalizer.semiring_normalize_ord_conv (put_simpset ss ctxt) (earlier_ord vs)))) th
       val rth = Thm.transitive nth (xnormalize_conv ctxt vs (Thm.rhs_of nth))
   in rth end
| \<^Const_>\<open>less_eq _ for a b\<close> =>
   let val (ca,cb) = Thm.dest_binop ct
       val T = Thm.ctyp_of_cterm ca
       val th = Thm.instantiate' [SOME T] [SOME ca, SOME cb] le_iff_diff_le_0
       val nth = Conv.fconv_rule
         (Conv.arg_conv (Conv.arg1_conv
              (Semiring_Normalizer.semiring_normalize_ord_conv (put_simpset ss ctxt) (earlier_ord vs)))) th
       val rth = Thm.transitive nth (xnormalize_conv ctxt vs (Thm.rhs_of nth))
   in rth end

| \<^Const_>\<open>HOL.eq _ for a b\<close> =>
   let val (ca,cb) = Thm.dest_binop ct
       val T = Thm.ctyp_of_cterm ca
       val th = Thm.instantiate' [SOME T] [SOME ca, SOME cb] eq_iff_diff_eq_0
       val nth = Conv.fconv_rule
         (Conv.arg_conv (Conv.arg1_conv
              (Semiring_Normalizer.semiring_normalize_ord_conv (put_simpset ss ctxt) (earlier_ord vs)))) th
       val rth = Thm.transitive nth (xnormalize_conv ctxt vs (Thm.rhs_of nth))
   in rth end
| \<^Const_>\<open>Not for \<^Const_>\<open>HOL.eq _ for a b\<close>\<close> => Conv.arg_conv (field_isolate_conv phi ctxt vs) ct
| _ => Thm.reflexive ct
end;

fun classfield_whatis phi =
 let
  fun h x t =
   case Thm.term_of t of
     \<^Const_>\<open>HOL.eq _ for y z\<close> =>
      if Thm.term_of x aconv y then Ferrante_Rackoff_Data.Eq
      else Ferrante_Rackoff_Data.Nox
   | \<^Const_>\<open>Not for \<^Const_>\<open>HOL.eq _ for y z\<close>\<close> =>
      if Thm.term_of x aconv y then Ferrante_Rackoff_Data.NEq
      else Ferrante_Rackoff_Data.Nox
   | \<^Const_>\<open>less _ for y z\<close> =>
       if Thm.term_of x aconv y then Ferrante_Rackoff_Data.Lt
       else if Thm.term_of x aconv z then Ferrante_Rackoff_Data.Gt
       else Ferrante_Rackoff_Data.Nox
   | \<^Const_>\<open>less_eq _ for y z\<close> =>
       if Thm.term_of x aconv y then Ferrante_Rackoff_Data.Le
       else if Thm.term_of x aconv z then Ferrante_Rackoff_Data.Ge
       else Ferrante_Rackoff_Data.Nox
   | _ => Ferrante_Rackoff_Data.Nox
 in h end;
fun class_field_ss phi ctxt =
  simpset_of (put_simpset HOL_basic_ss ctxt
    addsimps ([@{thm "linorder_not_less"}, @{thm "linorder_not_le"}])
    |> fold Splitter.add_split [@{thm "abs_split"}, @{thm "split_max"}, @{thm "split_min"}])

in
Ferrante_Rackoff_Data.funs @{thm "class_dense_linordered_field.ferrack_axiom"}
  {isolate_conv = field_isolate_conv, whatis = classfield_whatis, simpset = class_field_ss}
end
\<close>

end
