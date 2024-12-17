(*  Title:      HOL/HOLCF/Compact_Basis.thy
    Author:     Brian Huffman
*)

section \<open>A compact basis for powerdomains\<close>

theory Compact_Basis
imports Universal
begin

subsection \<open>A compact basis for powerdomains\<close>

definition "pd_basis = {S::'a::bifinite compact_basis set. finite S \<and> S \<noteq> {}}"

typedef 'a::bifinite pd_basis = "pd_basis :: 'a compact_basis set set"
proof
  show "{a} \<in> ?pd_basis" for a
    by (simp add: pd_basis_def)
qed

lemma finite_Rep_pd_basis [simp]: "finite (Rep_pd_basis u)"
using Rep_pd_basis [of u, unfolded pd_basis_def] by simp

lemma Rep_pd_basis_nonempty [simp]: "Rep_pd_basis u \<noteq> {}"
using Rep_pd_basis [of u, unfolded pd_basis_def] by simp

text \<open>The powerdomain basis type is countable.\<close>

lemma pd_basis_countable: "\<exists>f::'a::bifinite pd_basis \<Rightarrow> nat. inj f" (is "Ex ?P")
proof -
  obtain g :: "'a compact_basis \<Rightarrow> nat" where "inj g"
    using compact_basis.countable ..
  hence image_g_eq: "g ` A = g ` B \<longleftrightarrow> A = B" for A B
    by (rule inj_image_eq_iff)
  have "inj (\<lambda>t. set_encode (g ` Rep_pd_basis t))"
    by (simp add: inj_on_def set_encode_eq image_g_eq Rep_pd_basis_inject)
  thus ?thesis by (rule exI [of ?P])
qed


subsection \<open>Unit and plus constructors\<close>

definition
  PDUnit :: "'a::bifinite compact_basis \<Rightarrow> 'a pd_basis" where
  "PDUnit = (\<lambda>x. Abs_pd_basis {x})"

definition
  PDPlus :: "'a::bifinite pd_basis \<Rightarrow> 'a pd_basis \<Rightarrow> 'a pd_basis" where
  "PDPlus t u = Abs_pd_basis (Rep_pd_basis t \<union> Rep_pd_basis u)"

lemma Rep_PDUnit:
  "Rep_pd_basis (PDUnit x) = {x}"
unfolding PDUnit_def by (rule Abs_pd_basis_inverse) (simp add: pd_basis_def)

lemma Rep_PDPlus:
  "Rep_pd_basis (PDPlus u v) = Rep_pd_basis u \<union> Rep_pd_basis v"
unfolding PDPlus_def by (rule Abs_pd_basis_inverse) (simp add: pd_basis_def)

lemma PDUnit_inject [simp]: "(PDUnit a = PDUnit b) = (a = b)"
unfolding Rep_pd_basis_inject [symmetric] Rep_PDUnit by simp

lemma PDPlus_assoc: "PDPlus (PDPlus t u) v = PDPlus t (PDPlus u v)"
unfolding Rep_pd_basis_inject [symmetric] Rep_PDPlus by (rule Un_assoc)

lemma PDPlus_commute: "PDPlus t u = PDPlus u t"
unfolding Rep_pd_basis_inject [symmetric] Rep_PDPlus by (rule Un_commute)

lemma PDPlus_absorb: "PDPlus t t = t"
unfolding Rep_pd_basis_inject [symmetric] Rep_PDPlus by (rule Un_absorb)

lemma pd_basis_induct1:
  assumes PDUnit: "\<And>a. P (PDUnit a)"
  assumes PDPlus: "\<And>a t. P t \<Longrightarrow> P (PDPlus (PDUnit a) t)"
  shows "P x"
proof (induct x)
  case (Abs_pd_basis y)
  then have "finite y" and "y \<noteq> {}" by (simp_all add: pd_basis_def)
  then show ?case
  proof (induct rule: finite_ne_induct)
    case (singleton x)
    show ?case by (rule PDUnit [unfolded PDUnit_def])
  next
    case (insert x F)
    from insert(4) have "P (PDPlus (PDUnit x) (Abs_pd_basis F))" by (rule PDPlus)
    with insert(1,2) show ?case
      by (simp add: PDUnit_def PDPlus_def Abs_pd_basis_inverse [unfolded pd_basis_def])
  qed
qed

lemma pd_basis_induct:
  assumes PDUnit: "\<And>a. P (PDUnit a)"
  assumes PDPlus: "\<And>t u. \<lbrakk>P t; P u\<rbrakk> \<Longrightarrow> P (PDPlus t u)"
  shows "P x"
  by (induct x rule: pd_basis_induct1) (fact PDUnit, fact PDPlus [OF PDUnit])


subsection \<open>Fold operator\<close>

definition
  fold_pd ::
    "('a::bifinite compact_basis \<Rightarrow> 'b::type) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a pd_basis \<Rightarrow> 'b"
  where "fold_pd g f t = semilattice_set.F f (g ` Rep_pd_basis t)"

lemma fold_pd_PDUnit:
  assumes "semilattice f"
  shows "fold_pd g f (PDUnit x) = g x"
proof -
  from assms interpret semilattice_set f by (rule semilattice_set.intro)
  show ?thesis by (simp add: fold_pd_def Rep_PDUnit)
qed

lemma fold_pd_PDPlus:
  assumes "semilattice f"
  shows "fold_pd g f (PDPlus t u) = f (fold_pd g f t) (fold_pd g f u)"
proof -
  from assms interpret semilattice_set f by (rule semilattice_set.intro)
  show ?thesis by (simp add: image_Un fold_pd_def Rep_PDPlus union)
qed

end

