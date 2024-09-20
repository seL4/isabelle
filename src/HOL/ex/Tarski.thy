(*  Title:      HOL/ex/Tarski.thy
    Author:     Florian Kammüller, Cambridge University Computer Laboratory
*)

section \<open>The Full Theorem of Tarski\<close>

theory Tarski
imports Main "HOL-Library.FuncSet"
begin

text \<open>
  Minimal version of lattice theory plus the full theorem of Tarski:
  The fixedpoints of a complete lattice themselves form a complete
  lattice.

  Illustrates first-class theories, using the Sigma representation of
  structures.  Tidied and converted to Isar by lcp.
\<close>

record 'a potype =
  pset  :: "'a set"
  order :: "('a \<times> 'a) set"

definition monotone :: "['a \<Rightarrow> 'a, 'a set, ('a \<times> 'a) set] \<Rightarrow> bool"
  where "monotone f A r \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. (x, y) \<in> r \<longrightarrow> (f x, f y) \<in> r)"

definition least :: "['a \<Rightarrow> bool, 'a potype] \<Rightarrow> 'a"
  where "least P po = (SOME x. x \<in> pset po \<and> P x \<and> (\<forall>y \<in> pset po. P y \<longrightarrow> (x, y) \<in> order po))"

definition greatest :: "['a \<Rightarrow> bool, 'a potype] \<Rightarrow> 'a"
  where "greatest P po = (SOME x. x \<in> pset po \<and> P x \<and> (\<forall>y \<in> pset po. P y \<longrightarrow> (y, x) \<in> order po))"

definition lub :: "['a set, 'a potype] \<Rightarrow> 'a"
  where "lub S po = least (\<lambda>x. \<forall>y\<in>S. (y, x) \<in> order po) po"

definition glb :: "['a set, 'a potype] \<Rightarrow> 'a"
  where "glb S po = greatest (\<lambda>x. \<forall>y\<in>S. (x, y) \<in> order po) po"

definition isLub :: "['a set, 'a potype, 'a] \<Rightarrow> bool"
  where "isLub S po =
    (\<lambda>L. L \<in> pset po \<and> (\<forall>y\<in>S. (y, L) \<in> order po) \<and>
      (\<forall>z\<in>pset po. (\<forall>y\<in>S. (y, z) \<in> order po) \<longrightarrow> (L, z) \<in> order po))"

definition isGlb :: "['a set, 'a potype, 'a] \<Rightarrow> bool"
  where "isGlb S po =
    (\<lambda>G. (G \<in> pset po \<and> (\<forall>y\<in>S. (G, y) \<in> order po) \<and>
      (\<forall>z \<in> pset po. (\<forall>y\<in>S. (z, y) \<in> order po) \<longrightarrow> (z, G) \<in> order po)))"

definition "fix" :: "['a \<Rightarrow> 'a, 'a set] \<Rightarrow> 'a set"
  where "fix f A  = {x. x \<in> A \<and> f x = x}"

definition interval :: "[('a \<times> 'a) set, 'a, 'a] \<Rightarrow> 'a set"
  where "interval r a b = {x. (a, x) \<in> r \<and> (x, b) \<in> r}"

definition Bot :: "'a potype \<Rightarrow> 'a"
  where "Bot po = least (\<lambda>x. True) po"

definition Top :: "'a potype \<Rightarrow> 'a"
  where "Top po = greatest (\<lambda>x. True) po"

definition PartialOrder :: "'a potype set"
  where "PartialOrder = {P. refl_on (pset P) (order P) \<and> antisym (order P) \<and> trans (order P)}"

definition CompleteLattice :: "'a potype set"
  where "CompleteLattice =
    {cl. cl \<in> PartialOrder \<and>
      (\<forall>S. S \<subseteq> pset cl \<longrightarrow> (\<exists>L. isLub S cl L)) \<and>
      (\<forall>S. S \<subseteq> pset cl \<longrightarrow> (\<exists>G. isGlb S cl G))}"

definition CLF_set :: "('a potype \<times> ('a \<Rightarrow> 'a)) set"
  where "CLF_set =
    (SIGMA cl : CompleteLattice.
      {f. f \<in> pset cl \<rightarrow> pset cl \<and> monotone f (pset cl) (order cl)})"

definition induced :: "['a set, ('a \<times> 'a) set] \<Rightarrow> ('a \<times> 'a) set"
  where "induced A r = {(a, b). a \<in> A \<and> b \<in> A \<and> (a, b) \<in> r}"

definition sublattice :: "('a potype \<times> 'a set) set"
  where "sublattice =
    (SIGMA cl : CompleteLattice.
      {S. S \<subseteq> pset cl \<and> \<lparr>pset = S, order = induced S (order cl)\<rparr> \<in> CompleteLattice})"

abbreviation sublat :: "['a set, 'a potype] \<Rightarrow> bool"  (\<open>_ <<= _\<close> [51, 50] 50)
  where "S <<= cl \<equiv> S \<in> sublattice `` {cl}"

definition dual :: "'a potype \<Rightarrow> 'a potype"
  where "dual po = \<lparr>pset = pset po, order = converse (order po)\<rparr>"

locale S =
  fixes cl :: "'a potype"
    and A :: "'a set"
    and r :: "('a \<times> 'a) set"
  defines A_def: "A \<equiv> pset cl"
     and r_def: "r \<equiv> order cl"

locale PO = S +
  assumes cl_po: "cl \<in> PartialOrder"

locale CL = S +
  assumes cl_co: "cl \<in> CompleteLattice"

sublocale CL < po?: PO
  unfolding A_def r_def
  using CompleteLattice_def PO.intro cl_co by fastforce

locale CLF = S +
  fixes f :: "'a \<Rightarrow> 'a"
    and P :: "'a set"
  assumes f_cl:  "(cl, f) \<in> CLF_set" 
  defines P_def: "P \<equiv> fix f A"

sublocale CLF < cl?: CL
  unfolding A_def r_def CL_def
  using CLF_set_def f_cl by blast

locale Tarski = CLF +
  fixes Y :: "'a set"
    and intY1 :: "'a set"
    and v :: "'a"
  assumes Y_ss: "Y \<subseteq> P"
  defines intY1_def: "intY1 \<equiv> interval r (lub Y cl) (Top cl)"
    and v_def: "v \<equiv>
      glb {x. ((\<lambda>x \<in> intY1. f x) x, x) \<in> induced intY1 r \<and> x \<in> intY1}
        \<lparr>pset = intY1, order = induced intY1 r\<rparr>"


subsection \<open>Partial Order\<close>

context PO
begin

lemma dual: "PO (dual cl)"
proof
  show "dual cl \<in> PartialOrder"
  using cl_po unfolding PartialOrder_def dual_def by auto
qed

lemma PO_imp_refl_on [simp]: "refl_on A r"
  using cl_po by (simp add: PartialOrder_def A_def r_def)

lemma PO_imp_sym [simp]: "antisym r"
  using cl_po by (simp add: PartialOrder_def r_def)

lemma PO_imp_trans [simp]: "trans r"
  using cl_po by (simp add: PartialOrder_def r_def)

lemma reflE: "x \<in> A \<Longrightarrow> (x, x) \<in> r"
  using cl_po by (simp add: PartialOrder_def refl_on_def A_def r_def)

lemma antisymE: "\<lbrakk>(a, b) \<in> r; (b, a) \<in> r\<rbrakk> \<Longrightarrow> a = b"
  using cl_po by (simp add: PartialOrder_def antisym_def r_def)

lemma transE: "\<lbrakk>(a, b) \<in> r; (b, c) \<in> r\<rbrakk> \<Longrightarrow> (a, c) \<in> r"
  using cl_po by (simp add: PartialOrder_def r_def) (unfold trans_def, fast)

lemma monotoneE: "\<lbrakk>monotone f A r; x \<in> A; y \<in> A; (x, y) \<in> r\<rbrakk> \<Longrightarrow> (f x, f y) \<in> r"
  by (simp add: monotone_def)

lemma po_subset_po: 
  assumes "S \<subseteq> A" shows "\<lparr>pset = S, order = induced S r\<rparr> \<in> PartialOrder"
proof -
  have "refl_on S (induced S r)"
    using \<open>S \<subseteq> A\<close> by (auto simp: refl_on_def induced_def intro: reflE)
  moreover
  have "antisym (induced S r)"
    by (auto simp add: antisym_def induced_def intro: antisymE)
  moreover
  have "trans (induced S r)"
    by (auto simp add: trans_def induced_def intro: transE)
  ultimately show ?thesis
    by (simp add: PartialOrder_def)
qed

lemma indE: "\<lbrakk>(x, y) \<in> induced S r; S \<subseteq> A\<rbrakk> \<Longrightarrow> (x, y) \<in> r"
  by (simp add: induced_def)

lemma indI: "\<lbrakk>(x, y) \<in> r; x \<in> S; y \<in> S\<rbrakk> \<Longrightarrow> (x, y) \<in> induced S r"
  by (simp add: induced_def)

end

lemma (in CL) CL_imp_ex_isLub: "S \<subseteq> A \<Longrightarrow> \<exists>L. isLub S cl L"
  using cl_co by (simp add: CompleteLattice_def A_def)

declare (in CL) cl_co [simp]

lemma isLub_lub: "(\<exists>L. isLub S cl L) \<longleftrightarrow> isLub S cl (lub S cl)"
  by (simp add: lub_def least_def isLub_def some_eq_ex [symmetric])

lemma isGlb_glb: "(\<exists>G. isGlb S cl G) \<longleftrightarrow> isGlb S cl (glb S cl)"
  by (simp add: glb_def greatest_def isGlb_def some_eq_ex [symmetric])

lemma isGlb_dual_isLub: "isGlb S cl = isLub S (dual cl)"
  by (simp add: isLub_def isGlb_def dual_def converse_unfold)

lemma isLub_dual_isGlb: "isLub S cl = isGlb S (dual cl)"
  by (simp add: isLub_def isGlb_def dual_def converse_unfold)

lemma (in PO) dualPO: "dual cl \<in> PartialOrder"
  using cl_po by (simp add: PartialOrder_def dual_def)

lemma Rdual:
  assumes major: "\<And>S. S \<subseteq> A \<Longrightarrow> \<exists>L. isLub S po L" and "S \<subseteq> A" and "A = pset po"
  shows "\<exists>G. isGlb S po G"
proof
  show "isGlb S po (lub {y \<in> A. \<forall>k\<in>S. (y, k) \<in> order po} po)"
    using major [of "{y. y \<in> A \<and> (\<forall>k \<in> S. (y, k) \<in> order po)}"] \<open>S \<subseteq> A\<close> \<open>A = pset po\<close>
    apply (simp add: isLub_lub isGlb_def)
    apply (auto simp add: isLub_def)
    done
qed

lemma lub_dual_glb: "lub S cl = glb S (dual cl)"
  by (simp add: lub_def glb_def least_def greatest_def dual_def converse_unfold)

lemma glb_dual_lub: "glb S cl = lub S (dual cl)"
  by (simp add: lub_def glb_def least_def greatest_def dual_def converse_unfold)

lemma CL_subset_PO: "CompleteLattice \<subseteq> PartialOrder"
  by (auto simp: PartialOrder_def CompleteLattice_def)

lemmas CL_imp_PO = CL_subset_PO [THEN subsetD]

context CL
begin

lemma CO_refl_on: "refl_on A r"
  by (rule PO_imp_refl_on)

lemma CO_antisym: "antisym r"
  by (rule PO_imp_sym)

lemma CO_trans: "trans r"
  by (rule PO_imp_trans)

end

lemma CompleteLatticeI:
  "\<lbrakk>po \<in> PartialOrder; \<forall>S. S \<subseteq> pset po \<longrightarrow> (\<exists>L. isLub S po L);
     \<forall>S. S \<subseteq> pset po \<longrightarrow> (\<exists>G. isGlb S po G)\<rbrakk>
    \<Longrightarrow> po \<in> CompleteLattice"
  unfolding CompleteLattice_def by blast

lemma (in CL) CL_dualCL: "dual cl \<in> CompleteLattice"
  using cl_co
  apply (simp add: CompleteLattice_def dual_def)
  apply (simp add: dualPO flip: dual_def isLub_dual_isGlb isGlb_dual_isLub)
  done

context PO
begin

lemma dualA_iff [simp]: "pset (dual cl) = pset cl"
  by (simp add: dual_def)

lemma dualr_iff [simp]: "(x, y) \<in> (order (dual cl)) \<longleftrightarrow> (y, x) \<in> order cl"
  by (simp add: dual_def)

lemma monotone_dual:
  "monotone f (pset cl) (order cl) \<Longrightarrow> monotone f (pset (dual cl)) (order(dual cl))"
  by (simp add: monotone_def)

lemma interval_dual: "\<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> interval r x y = interval (order(dual cl)) y x"
  unfolding interval_def dualr_iff by (auto simp flip: r_def)

lemma interval_not_empty: "interval r a b \<noteq> {} \<Longrightarrow> (a, b) \<in> r"
  by (simp add: interval_def) (use transE in blast)

lemma interval_imp_mem: "x \<in> interval r a b \<Longrightarrow> (a, x) \<in> r"
  by (simp add: interval_def)

lemma left_in_interval: "\<lbrakk>a \<in> A; b \<in> A; interval r a b \<noteq> {}\<rbrakk> \<Longrightarrow> a \<in> interval r a b"
  using interval_def interval_not_empty reflE by fastforce

lemma right_in_interval: "\<lbrakk>a \<in> A; b \<in> A; interval r a b \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> interval r a b"
  by (simp add: A_def PO.dual PO.left_in_interval PO_axioms interval_dual)

end


subsection \<open>sublattice\<close>

lemma (in PO) sublattice_imp_CL:
  "S <<= cl \<Longrightarrow> \<lparr>pset = S, order = induced S r\<rparr> \<in> CompleteLattice"
  by (simp add: sublattice_def CompleteLattice_def r_def)

lemma (in CL) sublatticeI:
  "\<lbrakk>S \<subseteq> A; \<lparr>pset = S, order = induced S r\<rparr> \<in> CompleteLattice\<rbrakk> \<Longrightarrow> S <<= cl"
  by (simp add: sublattice_def A_def r_def)

lemma (in CL) dual: "CL (dual cl)"
proof
  show "dual cl \<in> CompleteLattice"
  using cl_co
  by (simp add: CompleteLattice_def dualPO flip: isGlb_dual_isLub isLub_dual_isGlb)
qed

subsection \<open>lub\<close>

context CL
begin

lemma lub_unique: "\<lbrakk>S \<subseteq> A; isLub S cl x; isLub S cl L\<rbrakk> \<Longrightarrow> x = L"
  by (rule antisymE) (auto simp add: isLub_def r_def)

lemma lub_upper: 
  assumes "S \<subseteq> A" "x \<in> S" shows "(x, lub S cl) \<in> r"
proof -
  obtain L where "isLub S cl L"
    using CL_imp_ex_isLub \<open>S \<subseteq> A\<close> by auto
  then show ?thesis
    by (metis assms(2) isLub_def isLub_lub r_def)
qed

lemma lub_least:
  assumes "S \<subseteq> A" and L: "L \<in> A" "\<forall>x \<in> S. (x, L) \<in> r" shows "(lub S cl, L) \<in> r"
proof -
  obtain L' where "isLub S cl L'"
    using CL_imp_ex_isLub \<open>S \<subseteq> A\<close> by auto
  then show ?thesis
    by (metis A_def L isLub_def isLub_lub r_def)
qed

lemma lub_in_lattice:
  assumes "S \<subseteq> A" shows "lub S cl \<in> A"
proof -
  obtain L where "isLub S cl L"
    using CL_imp_ex_isLub \<open>S \<subseteq> A\<close> by auto
  then show ?thesis
    by (metis A_def isLub_def isLub_lub)
qed

lemma lubI:
  assumes A: "S \<subseteq> A" "L \<in> A" and r: "\<forall>x \<in> S. (x, L) \<in> r" 
     and clo: "\<And>z. \<lbrakk>z \<in> A; (\<forall>y \<in> S. (y, z) \<in> r)\<rbrakk> \<Longrightarrow> (L, z) \<in> r" 
   shows "L = lub S cl"
proof -
  obtain L where "isLub S cl L"
    using CL_imp_ex_isLub assms(1) by auto
  then show ?thesis
    by (simp add: antisymE A clo lub_in_lattice lub_least lub_upper r)
qed

lemma lubIa: "\<lbrakk>S \<subseteq> A; isLub S cl L\<rbrakk> \<Longrightarrow> L = lub S cl"
  by (meson isLub_lub lub_unique)

lemma isLub_in_lattice: "isLub S cl L \<Longrightarrow> L \<in> A"
  by (simp add: isLub_def  A_def)

lemma isLub_upper: "\<lbrakk>isLub S cl L; y \<in> S\<rbrakk> \<Longrightarrow> (y, L) \<in> r"
  by (simp add: isLub_def r_def)

lemma isLub_least: "\<lbrakk>isLub S cl L; z \<in> A; \<forall>y \<in> S. (y, z) \<in> r\<rbrakk> \<Longrightarrow> (L, z) \<in> r"
  by (simp add: isLub_def A_def r_def)

lemma isLubI:
  "\<lbrakk>L \<in> A; \<forall>y \<in> S. (y, L) \<in> r; (\<forall>z \<in> A. (\<forall>y \<in> S. (y, z)\<in>r) \<longrightarrow> (L, z) \<in> r)\<rbrakk> \<Longrightarrow> isLub S cl L"
  by (simp add: isLub_def A_def r_def)

end


subsection \<open>glb\<close>

context CL
begin

lemma glb_in_lattice: "S \<subseteq> A \<Longrightarrow> glb S cl \<in> A"
  by (metis A_def CL.lub_in_lattice dualA_iff glb_dual_lub local.dual)

lemma glb_lower: "\<lbrakk>S \<subseteq> A; x \<in> S\<rbrakk> \<Longrightarrow> (glb S cl, x) \<in> r"
  by (metis A_def CL.lub_upper dualA_iff dualr_iff glb_dual_lub local.dual r_def)

end

text \<open>
  Reduce the sublattice property by using substructural properties;
  abandoned see \<open>Tarski_4.ML\<close>.
\<close>

context CLF
begin

lemma [simp]: "f \<in> pset cl \<rightarrow> pset cl \<and> monotone f (pset cl) (order cl)"
  using f_cl by (simp add: CLF_set_def)

declare f_cl [simp]


lemma f_in_funcset: "f \<in> A \<rightarrow> A"
  by (simp add: A_def)

lemma monotone_f: "monotone f A r"
  by (simp add: A_def r_def)

lemma CLF_dual: "(dual cl, f) \<in> CLF_set"
proof -
  have "Tarski.monotone f A (order (dual cl))"
    by (metis (no_types) A_def PO.monotone_dual PO_axioms dualA_iff monotone_f r_def)
  then show ?thesis
    by (simp add: A_def CLF_set_def CL_dualCL)
qed

lemma dual: "CLF (dual cl) f"
  by (rule CLF.intro) (rule CLF_dual)

end


subsection \<open>fixed points\<close>

lemma fix_subset: "fix f A \<subseteq> A"
  by (auto simp: fix_def)

lemma fix_imp_eq: "x \<in> fix f A \<Longrightarrow> f x = x"
  by (simp add: fix_def)

lemma fixf_subset: "\<lbrakk>A \<subseteq> B; x \<in> fix (\<lambda>y \<in> A. f y) A\<rbrakk> \<Longrightarrow> x \<in> fix f B"
  by (auto simp: fix_def)


subsection \<open>lemmas for Tarski, lub\<close>

context CLF
begin

lemma lubH_le_flubH: 
  assumes "H = {x \<in> A. (x, f x) \<in> r}"
  shows "(lub H cl, f (lub H cl)) \<in> r"
proof (intro lub_least ballI)
  show "H \<subseteq> A"
    using assms
    by auto
  show "f (lub H cl) \<in> A"
    using \<open>H \<subseteq> A\<close> f_in_funcset lub_in_lattice by auto
  show "(x, f (lub H cl)) \<in> r" if "x \<in> H" for x
  proof -
    have "(f x, f (lub H cl)) \<in> r"
      by (meson \<open>H \<subseteq> A\<close> in_mono lub_in_lattice lub_upper monotoneE monotone_f that)
    moreover have "(x, f x) \<in> r"
      using assms that by blast
    ultimately show ?thesis
      using po.transE by blast
  qed
qed

lemma lubH_is_fixp: 
  assumes "H = {x \<in> A. (x, f x) \<in> r}"
  shows "lub H cl \<in> fix f A"
proof -
  have "(f (lub H cl), lub H cl) \<in> r"
  proof -
    have "(lub H cl, f (lub H cl)) \<in> r"
      using assms lubH_le_flubH by blast
    then have "(f (lub H cl), f (f (lub H cl))) \<in> r"
      by (meson PO_imp_refl_on monotoneE monotone_f refl_on_domain)
    then have "f (lub H cl) \<in> H"
      by (metis (no_types, lifting) PO_imp_refl_on assms mem_Collect_eq refl_on_domain)
    then show ?thesis
      by (simp add: assms lub_upper)
  qed
  with assms show ?thesis
    by (simp add: fix_def antisymE lubH_le_flubH lub_in_lattice)
qed

lemma fixf_le_lubH: 
  assumes "H = {x \<in> A. (x, f x) \<in> r}" "x \<in> fix f A"
  shows "(x, lub H cl) \<in> r"
proof -
  have "x \<in> P \<Longrightarrow> x \<in> H"
    by (simp add: assms P_def fix_imp_eq [of _ f A] reflE fix_subset [of f A, THEN subsetD])
  with assms show ?thesis
    by (metis (no_types, lifting) P_def lub_upper mem_Collect_eq subset_eq)
qed


subsection \<open>Tarski fixpoint theorem 1, first part\<close>

lemma T_thm_1_lub: "lub P cl = lub {x \<in> A. (x, f x) \<in> r} cl"
proof -
  have "lub {x \<in> A. (x, f x) \<in> r} cl = lub (fix f A) cl"
  proof (rule antisymE)
    show "(lub {x \<in> A. (x, f x) \<in> r} cl, lub (fix f A) cl) \<in> r"
      by (simp add: fix_subset lubH_is_fixp lub_upper)
    have "\<And>a. a \<in> fix f A \<Longrightarrow> a \<in> A"
      by (meson fix_subset subset_iff)
    then show "(lub (fix f A) cl, lub {x \<in> A. (x, f x) \<in> r} cl) \<in> r"
      by (simp add: fix_subset fixf_le_lubH lubH_is_fixp lub_least)
  qed
  then show ?thesis
    using P_def by auto
qed

lemma glbH_is_fixp: 
  assumes "H = {x \<in> A. (f x, x) \<in> r}" shows "glb H cl \<in> P"
  \<comment> \<open>Tarski for glb\<close>
proof -
  have "glb H cl \<in> fix f (pset (dual cl))"
    using assms CLF.lubH_is_fixp [OF dual] PO.dualr_iff PO_axioms  
    by (fastforce simp add: A_def r_def glb_dual_lub)
  then show ?thesis
    by (simp add: A_def P_def)
qed

lemma T_thm_1_glb: "glb P cl = glb {x \<in> A. (f x, x) \<in> r} cl"
  unfolding glb_dual_lub P_def A_def r_def
  using CLF.T_thm_1_lub dualA_iff dualr_iff local.dual by force


subsection \<open>interval\<close>

lemma rel_imp_elem: "(x, y) \<in> r \<Longrightarrow> x \<in> A"
  using CO_refl_on by (auto simp: refl_on_def)

lemma interval_subset: "\<lbrakk>a \<in> A; b \<in> A\<rbrakk> \<Longrightarrow> interval r a b \<subseteq> A"
  by (simp add: interval_def) (blast intro: rel_imp_elem)

lemma intervalI: "\<lbrakk>(a, x) \<in> r; (x, b) \<in> r\<rbrakk> \<Longrightarrow> x \<in> interval r a b"
  by (simp add: interval_def)

lemma interval_lemma1: "\<lbrakk>S \<subseteq> interval r a b; x \<in> S\<rbrakk> \<Longrightarrow> (a, x) \<in> r"
  unfolding interval_def by fast

lemma interval_lemma2: "\<lbrakk>S \<subseteq> interval r a b; x \<in> S\<rbrakk> \<Longrightarrow> (x, b) \<in> r"
  unfolding interval_def by fast

lemma a_less_lub: "\<lbrakk>S \<subseteq> A; S \<noteq> {}; \<forall>x \<in> S. (a,x) \<in> r; \<forall>y \<in> S. (y, L) \<in> r\<rbrakk> \<Longrightarrow> (a, L) \<in> r"
  by (blast intro: transE)

lemma S_intv_cl: "\<lbrakk>a \<in> A; b \<in> A; S \<subseteq> interval r a b\<rbrakk> \<Longrightarrow> S \<subseteq> A"
  by (simp add: subset_trans [OF _ interval_subset])

lemma L_in_interval:
  assumes "b \<in> A" and S: "S \<subseteq> interval r a b" "isLub S cl L" "S \<noteq> {}"
  shows "L \<in> interval r a b"
proof (rule intervalI)
  show "(a, L) \<in> r"
    by (meson PO_imp_trans all_not_in_conv S interval_lemma1 isLub_upper transD)
  show "(L, b) \<in> r"
    using \<open>b \<in> A\<close> assms interval_lemma2 isLub_least by auto
qed

lemma G_in_interval:
  assumes "b \<in> A" and S: "S \<subseteq> interval r a b" "isGlb S cl G" "S \<noteq> {}"
  shows "G \<in> interval r a b"
proof -
  have "a \<in> A"
    using S(1) \<open>S \<noteq> {}\<close> interval_lemma1 rel_imp_elem by blast
  with assms show ?thesis
    by (metis (no_types) A_def CLF.L_in_interval dualA_iff interval_dual isGlb_dual_isLub local.dual)
qed

lemma intervalPO:
  "\<lbrakk>a \<in> A; b \<in> A; interval r a b \<noteq> {}\<rbrakk>
    \<Longrightarrow> \<lparr>pset = interval r a b, order = induced (interval r a b) r\<rparr> \<in> PartialOrder"
  by (rule po_subset_po) (simp add: interval_subset)

lemma intv_CL_lub:
  assumes "a \<in> A" "b \<in> A" "interval r a b \<noteq> {}" and S: "S \<subseteq> interval r a b"
  shows "\<exists>L. isLub S \<lparr>pset = interval r a b, order = induced (interval r a b) r\<rparr>  L"
proof -
  obtain L where L: "isLub S cl L"
    by (meson CL_imp_ex_isLub S_intv_cl assms(1) assms(2) assms(4))
  show ?thesis
    unfolding isLub_def potype.simps
    proof (intro exI impI conjI ballI)
    let ?L = "(if S = {} then a else L)"
    show Lin: "?L \<in> interval r a b"
      using L L_in_interval assms left_in_interval by auto
    show "(y, ?L) \<in> induced (interval r a b) r" if "y \<in> S" for y
    proof -
      have "S \<noteq> {}"
        using that by blast
      then show ?thesis
        using L Lin S indI isLub_upper that by auto
    qed
  show "(?L, z) \<in> induced (interval r a b) r"
    if "z \<in> interval r a b" and "\<forall>y\<in>S. (y, z) \<in> induced (interval r a b) r" for z
      using that L
      apply (simp add: isLub_def induced_def interval_imp_mem)
      by (metis (full_types) A_def Lin \<open>a \<in> A\<close> \<open>b \<in> A\<close> interval_subset r_def subset_eq)
  qed
qed

lemmas intv_CL_glb = intv_CL_lub [THEN Rdual]

lemma interval_is_sublattice: "\<lbrakk>a \<in> A; b \<in> A; interval r a b \<noteq> {}\<rbrakk> \<Longrightarrow> interval r a b <<= cl"
  apply (rule sublatticeI)
   apply (simp add: interval_subset)
  by (simp add: CompleteLatticeI intervalPO intv_CL_glb intv_CL_lub)

lemmas interv_is_compl_latt = interval_is_sublattice [THEN sublattice_imp_CL]


subsection \<open>Top and Bottom\<close>

lemma Top_dual_Bot: "Top cl = Bot (dual cl)"
  by (simp add: Top_def Bot_def least_def greatest_def)

lemma Bot_dual_Top: "Bot cl = Top (dual cl)"
  by (simp add: Top_def Bot_def least_def greatest_def)

lemma Bot_in_lattice: "Bot cl \<in> A"
  unfolding Bot_def least_def
  apply (rule_tac a = "glb A cl" in someI2)
  using glb_in_lattice glb_lower by (auto simp: A_def r_def)

lemma Top_in_lattice: "Top cl \<in> A"
  using A_def CLF.Bot_in_lattice Top_dual_Bot local.dual by force

lemma Top_prop: "x \<in> A \<Longrightarrow> (x, Top cl) \<in> r"
  unfolding Top_def greatest_def
  apply (rule_tac a = "lub A cl" in someI2)
  using lub_in_lattice lub_upper by (auto simp: A_def r_def)

lemma Bot_prop: "x \<in> A \<Longrightarrow> (Bot cl, x) \<in> r"
  using A_def Bot_dual_Top CLF.Top_prop dualA_iff dualr_iff local.dual r_def by fastforce

lemma Top_intv_not_empty: "x \<in> A \<Longrightarrow> interval r x (Top cl) \<noteq> {}"
  using Top_prop intervalI reflE by force

lemma Bot_intv_not_empty: "x \<in> A \<Longrightarrow> interval r (Bot cl) x \<noteq> {}"
  using Bot_dual_Top Bot_prop intervalI reflE by fastforce


text \<open>the set of fixed points form a partial order\<close>
proposition fixf_po: "\<lparr>pset = P, order = induced P r\<rparr> \<in> PartialOrder"
  by (simp add: P_def fix_subset po_subset_po)

end

context Tarski
begin

lemma Y_subset_A: "Y \<subseteq> A"
  by (rule subset_trans [OF _ fix_subset]) (rule Y_ss [simplified P_def])

lemma lubY_in_A: "lub Y cl \<in> A"
  by (rule Y_subset_A [THEN lub_in_lattice])

lemma lubY_le_flubY: "(lub Y cl, f (lub Y cl)) \<in> r"
proof (intro lub_least Y_subset_A ballI)
  show "f (lub Y cl) \<in> A"
    by (meson Tarski.monotone_def lubY_in_A monotone_f reflE rel_imp_elem)
  show "(x, f (lub Y cl)) \<in> r" if "x \<in> Y" for x
  proof 
    have "\<And>A. Y \<subseteq> A \<Longrightarrow> x \<in> A"
      using that by blast
    moreover have "(x, lub Y cl) \<in> r"
      using that by (simp add: Y_subset_A lub_upper)
    ultimately show "(x, f (lub Y cl)) \<in> r"
      by (metis (no_types) Tarski.Y_ss Tarski_axioms Y_subset_A fix_imp_eq lubY_in_A monotoneE monotone_f)
  qed auto
qed

lemma intY1_subset: "intY1 \<subseteq> A"
  unfolding intY1_def using Top_in_lattice interval_subset lubY_in_A by auto

lemmas intY1_elem = intY1_subset [THEN subsetD]

lemma intY1_f_closed:   
  assumes "x \<in> intY1" shows "f x \<in> intY1"
proof (simp add: intY1_def interval_def, rule conjI)
  show "(lub Y cl, f x) \<in> r"
    using assms intY1_elem interval_imp_mem lubY_in_A unfolding intY1_def
    using lubY_le_flubY monotoneE monotone_f po.transE by blast
  then show "(f x, Top cl) \<in> r"
    by (meson PO_imp_refl_on Top_prop refl_onD2)
qed

lemma intY1_mono: "monotone (\<lambda> x \<in> intY1. f x) intY1 (induced intY1 r)"
  apply (auto simp add: monotone_def induced_def intY1_f_closed)
  apply (blast intro: intY1_elem monotone_f [THEN monotoneE])
  done

lemma intY1_is_cl: "\<lparr>pset = intY1, order = induced intY1 r\<rparr> \<in> CompleteLattice"
  unfolding intY1_def
  by (simp add: Top_in_lattice Top_intv_not_empty interv_is_compl_latt lubY_in_A)

lemma v_in_P: "v \<in> P"
proof -
  have "v \<in> fix (restrict f intY1) intY1"
    unfolding v_def
    apply (rule CLF.glbH_is_fixp
        [OF CLF.intro, unfolded CLF_set_def, of "\<lparr>pset = intY1, order = induced intY1 r\<rparr>", simplified])
    using intY1_f_closed intY1_is_cl intY1_mono apply blast+
    done
  then show ?thesis
    unfolding P_def
  by (meson fixf_subset intY1_subset)
qed

lemma z_in_interval: "\<lbrakk>z \<in> P; \<forall>y\<in>Y. (y, z) \<in> induced P r\<rbrakk> \<Longrightarrow> z \<in> intY1"
  unfolding intY1_def P_def
  by (meson Top_prop Y_subset_A fix_subset in_mono indE intervalI lub_least)

lemma tarski_full_lemma: "\<exists>L. isLub Y \<lparr>pset = P, order = induced P r\<rparr> L"
proof
  have "(y, v) \<in> induced P r" if "y \<in> Y" for y
  proof -
    have "(y, lub Y cl) \<in> r"
      by (simp add: Y_subset_A lub_upper that)
    moreover have "(lub Y cl, v) \<in> r"
      by (metis (no_types, lifting) CL.glb_in_lattice CL.intro intY1_def intY1_is_cl interval_imp_mem lub_dual_glb mem_Collect_eq select_convs(1) subsetI v_def)
    ultimately have "(y, v) \<in> r"
      using po.transE by blast
    then show ?thesis
      using Y_ss indI that v_in_P by auto
  qed
  moreover have "(v, z) \<in> induced P r" if "z \<in> P" "\<forall>y\<in>Y. (y, z) \<in> induced P r" for z
  proof (rule indI)
    have "((\<lambda>x \<in> intY1. f x) z, z) \<in> induced intY1 r"
      by (metis P_def fix_imp_eq in_mono indI intY1_subset reflE restrict_apply' that z_in_interval)
    then show "(v, z) \<in> r"
      by (metis (no_types, lifting) CL.glb_lower CL_def indE intY1_is_cl intY1_subset mem_Collect_eq select_convs(1,2) subsetI that v_def z_in_interval)
  qed (auto simp: that v_in_P)
  ultimately
  show "isLub Y \<lparr>pset = P, order = induced P r\<rparr> v"
    by (simp add: isLub_def v_in_P)
qed

end

lemma CompleteLatticeI_simp:
  "\<lbrakk>po \<in> PartialOrder; \<And>S. S \<subseteq> A \<Longrightarrow> \<exists>L. isLub S po  L; A = pset po\<rbrakk> \<Longrightarrow> po \<in> CompleteLattice"
  by (metis CompleteLatticeI Rdual)

theorem (in CLF) Tarski_full: "\<lparr>pset = P, order = induced P r\<rparr> \<in> CompleteLattice"
proof (intro CompleteLatticeI_simp allI impI)
  show "\<lparr>pset = P, order = induced P r\<rparr> \<in> PartialOrder"
    by (simp add: fixf_po)
  show "\<And>S. S \<subseteq> P \<Longrightarrow> \<exists>L. isLub S \<lparr>pset = P, order = induced P r\<rparr> L"
    unfolding P_def A_def r_def
  proof (rule Tarski.tarski_full_lemma [OF Tarski.intro [OF _ Tarski_axioms.intro]])
    show "CLF cl f" ..
  qed
qed auto

end
