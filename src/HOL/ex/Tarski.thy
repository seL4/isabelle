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

abbreviation sublat :: "['a set, 'a potype] \<Rightarrow> bool"  ("_ <<= _" [51, 50] 50)
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
    apply (simp_all add: A_def r_def)
  apply unfold_locales
  using cl_co unfolding CompleteLattice_def
  apply auto
  done

locale CLF = S +
  fixes f :: "'a \<Rightarrow> 'a"
    and P :: "'a set"
  assumes f_cl:  "(cl, f) \<in> CLF_set" (*was the equivalent "f \<in> CLF_set``{cl}"*)
  defines P_def: "P \<equiv> fix f A"

sublocale CLF < cl?: CL
    apply (simp_all add: A_def r_def)
  apply unfold_locales
  using f_cl unfolding CLF_set_def
  apply auto
  done

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
  apply unfold_locales
  using cl_po
  unfolding PartialOrder_def dual_def
  apply auto
  done

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

lemma po_subset_po: "S \<subseteq> A \<Longrightarrow> \<lparr>pset = S, order = induced S r\<rparr> \<in> PartialOrder"
  apply (simp add: PartialOrder_def)
  apply auto
    \<comment> \<open>refl\<close>
    apply (simp add: refl_on_def induced_def)
    apply (blast intro: reflE)
    \<comment> \<open>antisym\<close>
   apply (simp add: antisym_def induced_def)
   apply (blast intro: antisymE)
    \<comment> \<open>trans\<close>
  apply (simp add: trans_def induced_def)
  apply (blast intro: transE)
  done

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
  "\<forall>S. (S \<subseteq> A \<longrightarrow> (\<exists>L. isLub S \<lparr>pset = A, order = r\<rparr> L))
    \<Longrightarrow> \<forall>S. S \<subseteq> A \<longrightarrow> (\<exists>G. isGlb S \<lparr>pset = A, order = r\<rparr> G)"
  apply safe
  apply (rule_tac x = "lub {y. y \<in> A \<and> (\<forall>k \<in> S. (y, k) \<in> r)} \<lparr>pset = A, order = r\<rparr>" in exI)
  apply (drule_tac x = "{y. y \<in> A \<and> (\<forall>k \<in> S. (y, k) \<in> r)}" in spec)
  apply (drule mp)
   apply fast
  apply (simp add: isLub_lub isGlb_def)
  apply (simp add: isLub_def)
  apply blast
  done

lemma lub_dual_glb: "lub S cl = glb S (dual cl)"
  by (simp add: lub_def glb_def least_def greatest_def dual_def converse_unfold)

lemma glb_dual_lub: "glb S cl = lub S (dual cl)"
  by (simp add: lub_def glb_def least_def greatest_def dual_def converse_unfold)

lemma CL_subset_PO: "CompleteLattice \<subseteq> PartialOrder"
  by (auto simp: PartialOrder_def CompleteLattice_def)

lemmas CL_imp_PO = CL_subset_PO [THEN subsetD]

(*declare CL_imp_PO [THEN PO.PO_imp_refl, simp]
declare CL_imp_PO [THEN PO.PO_imp_sym, simp]
declare CL_imp_PO [THEN PO.PO_imp_trans, simp]*)

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
  apply (fold dual_def)
  apply (simp add: isLub_dual_isGlb [symmetric] isGlb_dual_isLub [symmetric] dualPO)
  done

context PO
begin

lemma dualA_iff: "pset (dual cl) = pset cl"
  by (simp add: dual_def)

lemma dualr_iff: "(x, y) \<in> (order (dual cl)) \<longleftrightarrow> (y, x) \<in> order cl"
  by (simp add: dual_def)

lemma monotone_dual:
  "monotone f (pset cl) (order cl) \<Longrightarrow> monotone f (pset (dual cl)) (order(dual cl))"
  by (simp add: monotone_def dualA_iff dualr_iff)

lemma interval_dual: "\<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> interval r x y = interval (order(dual cl)) y x"
  apply (simp add: interval_def dualr_iff)
  apply (fold r_def)
  apply fast
  done

lemma trans: "(x, y) \<in> r \<Longrightarrow> (y, z) \<in> r \<Longrightarrow> (x, z) \<in> r"
  using cl_po
  apply (auto simp add: PartialOrder_def r_def)
  unfolding trans_def
  apply blast
  done

lemma interval_not_empty: "interval r a b \<noteq> {} \<Longrightarrow> (a, b) \<in> r"
  by (simp add: interval_def) (use trans in blast)

lemma interval_imp_mem: "x \<in> interval r a b \<Longrightarrow> (a, x) \<in> r"
  by (simp add: interval_def)

lemma left_in_interval: "\<lbrakk>a \<in> A; b \<in> A; interval r a b \<noteq> {}\<rbrakk> \<Longrightarrow> a \<in> interval r a b"
  apply (simp (no_asm_simp) add: interval_def)
  apply (simp add: interval_not_empty)
  apply (simp add: reflE)
  done

lemma right_in_interval: "\<lbrakk>a \<in> A; b \<in> A; interval r a b \<noteq> {}\<rbrakk> \<Longrightarrow> b \<in> interval r a b"
  apply (simp (no_asm_simp) add: interval_def)
  apply (simp add: interval_not_empty)
  apply (simp add: reflE)
  done

end


subsection \<open>sublattice\<close>

lemma (in PO) sublattice_imp_CL:
  "S <<= cl \<Longrightarrow> \<lparr>pset = S, order = induced S r\<rparr> \<in> CompleteLattice"
  by (simp add: sublattice_def CompleteLattice_def r_def)

lemma (in CL) sublatticeI:
  "\<lbrakk>S \<subseteq> A; \<lparr>pset = S, order = induced S r\<rparr> \<in> CompleteLattice\<rbrakk> \<Longrightarrow> S <<= cl"
  by (simp add: sublattice_def A_def r_def)

lemma (in CL) dual: "CL (dual cl)"
  apply unfold_locales
  using cl_co
  unfolding CompleteLattice_def
  apply (simp add: dualPO isGlb_dual_isLub [symmetric] isLub_dual_isGlb [symmetric] dualA_iff)
  done


subsection \<open>lub\<close>

context CL
begin

lemma lub_unique: "\<lbrakk>S \<subseteq> A; isLub S cl x; isLub S cl L\<rbrakk> \<Longrightarrow> x = L"
  by (rule antisymE) (auto simp add: isLub_def r_def)

lemma lub_upper: "\<lbrakk>S \<subseteq> A; x \<in> S\<rbrakk> \<Longrightarrow> (x, lub S cl) \<in> r"
  apply (rule CL_imp_ex_isLub [THEN exE], assumption)
  apply (unfold lub_def least_def)
  apply (rule some_equality [THEN ssubst])
    apply (simp add: isLub_def)
   apply (simp add: lub_unique A_def isLub_def)
  apply (simp add: isLub_def r_def)
  done

lemma lub_least: "\<lbrakk>S \<subseteq> A; L \<in> A; \<forall>x \<in> S. (x, L) \<in> r\<rbrakk> \<Longrightarrow> (lub S cl, L) \<in> r"
  apply (rule CL_imp_ex_isLub [THEN exE], assumption)
  apply (unfold lub_def least_def)
  apply (rule_tac s=x in some_equality [THEN ssubst])
    apply (simp add: isLub_def)
   apply (simp add: lub_unique A_def isLub_def)
  apply (simp add: isLub_def r_def A_def)
  done

lemma lub_in_lattice: "S \<subseteq> A \<Longrightarrow> lub S cl \<in> A"
  apply (rule CL_imp_ex_isLub [THEN exE], assumption)
  apply (unfold lub_def least_def)
  apply (subst some_equality)
    apply (simp add: isLub_def)
   prefer 2 apply (simp add: isLub_def A_def)
  apply (simp add: lub_unique A_def isLub_def)
  done

lemma lubI:
  "\<lbrakk>S \<subseteq> A; L \<in> A; \<forall>x \<in> S. (x, L) \<in> r;
    \<forall>z \<in> A. (\<forall>y \<in> S. (y, z) \<in> r) \<longrightarrow> (L, z) \<in> r\<rbrakk> \<Longrightarrow> L = lub S cl"
  apply (rule lub_unique, assumption)
   apply (simp add: isLub_def A_def r_def)
  apply (unfold isLub_def)
  apply (rule conjI)
   apply (fold A_def r_def)
   apply (rule lub_in_lattice, assumption)
  apply (simp add: lub_upper lub_least)
  done

lemma lubIa: "\<lbrakk>S \<subseteq> A; isLub S cl L\<rbrakk> \<Longrightarrow> L = lub S cl"
  by (simp add: lubI isLub_def A_def r_def)

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
  apply (subst glb_dual_lub)
  apply (simp add: A_def)
  apply (rule dualA_iff [THEN subst])
  apply (rule CL.lub_in_lattice)
   apply (rule dual)
  apply (simp add: dualA_iff)
  done

lemma glb_lower: "\<lbrakk>S \<subseteq> A; x \<in> S\<rbrakk> \<Longrightarrow> (glb S cl, x) \<in> r"
  apply (subst glb_dual_lub)
  apply (simp add: r_def)
  apply (rule dualr_iff [THEN subst])
  apply (rule CL.lub_upper)
    apply (rule dual)
   apply (simp add: dualA_iff A_def, assumption)
  done

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
  by (simp add: CLF_set_def  CL_dualCL monotone_dual) (simp add: dualA_iff)

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

lemma lubH_le_flubH: "H = {x. (x, f x) \<in> r \<and> x \<in> A} \<Longrightarrow> (lub H cl, f (lub H cl)) \<in> r"
  apply (rule lub_least, fast)
   apply (rule f_in_funcset [THEN funcset_mem])
   apply (rule lub_in_lattice, fast)
    \<comment> \<open>\<open>\<forall>x:H. (x, f (lub H r)) \<in> r\<close>\<close>
  apply (rule ballI)
  apply (rule transE)
    \<comment> \<open>instantiates \<open>(x, ???z) \<in> order cl to (x, f x)\<close>,\<close>
    \<comment> \<open>because of the def of \<open>H\<close>\<close>
   apply fast
    \<comment> \<open>so it remains to show \<open>(f x, f (lub H cl)) \<in> r\<close>\<close>
  apply (rule_tac f = "f" in monotoneE)
     apply (rule monotone_f, fast)
   apply (rule lub_in_lattice, fast)
  apply (rule lub_upper, fast)
  apply assumption
  done

lemma flubH_le_lubH: "\<lbrakk>H = {x. (x, f x) \<in> r \<and> x \<in> A}\<rbrakk> \<Longrightarrow> (f (lub H cl), lub H cl) \<in> r"
  apply (rule lub_upper, fast)
  apply (rule_tac t = "H" in ssubst, assumption)
  apply (rule CollectI)
  apply (rule conjI)
   apply (rule_tac [2] f_in_funcset [THEN funcset_mem])
   apply (rule_tac [2] lub_in_lattice)
   prefer 2 apply fast
  apply (rule_tac f = f in monotoneE)
     apply (rule monotone_f)
    apply (blast intro: lub_in_lattice)
   apply (blast intro: lub_in_lattice f_in_funcset [THEN funcset_mem])
  apply (simp add: lubH_le_flubH)
  done

lemma lubH_is_fixp: "H = {x. (x, f x) \<in> r \<and> x \<in> A} \<Longrightarrow> lub H cl \<in> fix f A"
  apply (simp add: fix_def)
  apply (rule conjI)
   apply (rule lub_in_lattice, fast)
  apply (rule antisymE)
   apply (simp add: flubH_le_lubH)
  apply (simp add: lubH_le_flubH)
  done

lemma fix_in_H: "\<lbrakk>H = {x. (x, f x) \<in> r \<and> x \<in> A}; x \<in> P\<rbrakk> \<Longrightarrow> x \<in> H"
  by (simp add: P_def fix_imp_eq [of _ f A] reflE fix_subset [of f A, THEN subsetD])

lemma fixf_le_lubH: "H = {x. (x, f x) \<in> r \<and> x \<in> A} \<Longrightarrow> \<forall>x \<in> fix f A. (x, lub H cl) \<in> r"
  apply (rule ballI)
  apply (rule lub_upper)
   apply fast
  apply (rule fix_in_H)
   apply (simp_all add: P_def)
  done

lemma lubH_least_fixf:
  "H = {x. (x, f x) \<in> r \<and> x \<in> A} \<Longrightarrow> \<forall>L. (\<forall>y \<in> fix f A. (y,L) \<in> r) \<longrightarrow> (lub H cl, L) \<in> r"
  apply (rule allI)
  apply (rule impI)
  apply (erule bspec)
  apply (rule lubH_is_fixp, assumption)
  done


subsection \<open>Tarski fixpoint theorem 1, first part\<close>

lemma T_thm_1_lub: "lub P cl = lub {x. (x, f x) \<in> r \<and> x \<in> A} cl"
  apply (rule sym)
  apply (simp add: P_def)
  apply (rule lubI)
     apply (rule fix_subset)
    apply (rule lub_in_lattice, fast)
   apply (simp add: fixf_le_lubH)
  apply (simp add: lubH_least_fixf)
  done

lemma glbH_is_fixp: "H = {x. (f x, x) \<in> r \<and> x \<in> A} \<Longrightarrow> glb H cl \<in> P"
  \<comment> \<open>Tarski for glb\<close>
  apply (simp add: glb_dual_lub P_def A_def r_def)
  apply (rule dualA_iff [THEN subst])
  apply (rule CLF.lubH_is_fixp)
   apply (rule dual)
  apply (simp add: dualr_iff dualA_iff)
  done

lemma T_thm_1_glb: "glb P cl = glb {x. (f x, x) \<in> r \<and> x \<in> A} cl"
  apply (simp add: glb_dual_lub P_def A_def r_def)
  apply (rule dualA_iff [THEN subst])
  apply (simp add: CLF.T_thm_1_lub [of _ f, OF dual] dualPO CL_dualCL CLF_dual dualr_iff)
  done


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

lemma glb_less_b: "\<lbrakk>S \<subseteq> A; S \<noteq> {}; \<forall>x \<in> S. (x,b) \<in> r; \<forall>y \<in> S. (G, y) \<in> r\<rbrakk> \<Longrightarrow> (G, b) \<in> r"
  by (blast intro: transE)

lemma S_intv_cl: "\<lbrakk>a \<in> A; b \<in> A; S \<subseteq> interval r a b\<rbrakk> \<Longrightarrow> S \<subseteq> A"
  by (simp add: subset_trans [OF _ interval_subset])

lemma L_in_interval:
  "\<lbrakk>a \<in> A; b \<in> A; S \<subseteq> interval r a b;
    S \<noteq> {}; isLub S cl L; interval r a b \<noteq> {}\<rbrakk> \<Longrightarrow> L \<in> interval r a b"
  apply (rule intervalI)
   apply (rule a_less_lub)
      prefer 2 apply assumption
     apply (simp add: S_intv_cl)
    apply (rule ballI)
    apply (simp add: interval_lemma1)
   apply (simp add: isLub_upper)
    \<comment> \<open>\<open>(L, b) \<in> r\<close>\<close>
  apply (simp add: isLub_least interval_lemma2)
  done

lemma G_in_interval:
  "\<lbrakk>a \<in> A; b \<in> A; interval r a b \<noteq> {}; S \<subseteq> interval r a b; isGlb S cl G; S \<noteq> {}\<rbrakk>
    \<Longrightarrow> G \<in> interval r a b"
  by (simp add: interval_dual)
    (simp add: CLF.L_in_interval [of _ f, OF dual] dualA_iff A_def isGlb_dual_isLub)

lemma intervalPO:
  "\<lbrakk>a \<in> A; b \<in> A; interval r a b \<noteq> {}\<rbrakk>
    \<Longrightarrow> \<lparr>pset = interval r a b, order = induced (interval r a b) r\<rparr> \<in> PartialOrder"
  by (rule po_subset_po) (simp add: interval_subset)

lemma intv_CL_lub:
  "\<lbrakk>a \<in> A; b \<in> A; interval r a b \<noteq> {}\<rbrakk> \<Longrightarrow>
    \<forall>S. S \<subseteq> interval r a b \<longrightarrow>
      (\<exists>L. isLub S \<lparr>pset = interval r a b, order = induced (interval r a b) r\<rparr>  L)"
  apply (intro strip)
  apply (frule S_intv_cl [THEN CL_imp_ex_isLub])
    prefer 2 apply assumption
   apply assumption
  apply (erule exE)
    \<comment> \<open>define the lub for the interval as\<close>
  apply (rule_tac x = "if S = {} then a else L" in exI)
  apply (simp (no_asm_simp) add: isLub_def split del: if_split)
  apply (intro impI conjI)
    \<comment> \<open>\<open>(if S = {} then a else L) \<in> interval r a b\<close>\<close>
    apply (simp add: CL_imp_PO L_in_interval)
    apply (simp add: left_in_interval)
    \<comment> \<open>lub prop 1\<close>
   apply (case_tac "S = {}")
    \<comment> \<open>\<open>S = {}, y \<in> S = False \<Longrightarrow> everything\<close>\<close>
    apply fast
    \<comment> \<open>\<open>S \<noteq> {}\<close>\<close>
   apply simp
    \<comment> \<open>\<open>\<forall>y\<in>S. (y, L) \<in> induced (interval r a b) r\<close>\<close>
   apply (rule ballI)
   apply (simp add: induced_def  L_in_interval)
   apply (rule conjI)
    apply (rule subsetD)
     apply (simp add: S_intv_cl, assumption)
   apply (simp add: isLub_upper)
    \<comment> \<open>\<open>\<forall>z\<in>interval r a b.
        (\<forall>y\<in>S. (y, z) \<in> induced (interval r a b) r \<longrightarrow>
        (if S = {} then a else L, z) \<in> induced (interval r a b) r\<close>\<close>
  apply (rule ballI)
  apply (rule impI)
  apply (case_tac "S = {}")
    \<comment> \<open>\<open>S = {}\<close>\<close>
   apply simp
   apply (simp add: induced_def  interval_def)
   apply (rule conjI)
    apply (rule reflE, assumption)
   apply (rule interval_not_empty)
   apply (simp add: interval_def)
    \<comment> \<open>\<open>S \<noteq> {}\<close>\<close>
  apply simp
  apply (simp add: induced_def  L_in_interval)
  apply (rule isLub_least, assumption)
   apply (rule subsetD)
    prefer 2 apply assumption
   apply (simp add: S_intv_cl, fast)
  done

lemmas intv_CL_glb = intv_CL_lub [THEN Rdual]

lemma interval_is_sublattice: "\<lbrakk>a \<in> A; b \<in> A; interval r a b \<noteq> {}\<rbrakk> \<Longrightarrow> interval r a b <<= cl"
  apply (rule sublatticeI)
   apply (simp add: interval_subset)
  apply (rule CompleteLatticeI)
    apply (simp add: intervalPO)
   apply (simp add: intv_CL_lub)
  apply (simp add: intv_CL_glb)
  done

lemmas interv_is_compl_latt = interval_is_sublattice [THEN sublattice_imp_CL]


subsection \<open>Top and Bottom\<close>

lemma Top_dual_Bot: "Top cl = Bot (dual cl)"
  by (simp add: Top_def Bot_def least_def greatest_def dualA_iff dualr_iff)

lemma Bot_dual_Top: "Bot cl = Top (dual cl)"
  by (simp add: Top_def Bot_def least_def greatest_def dualA_iff dualr_iff)

lemma Bot_in_lattice: "Bot cl \<in> A"
  apply (simp add: Bot_def least_def)
  apply (rule_tac a = "glb A cl" in someI2)
   apply (simp_all add: glb_in_lattice glb_lower r_def [symmetric] A_def [symmetric])
  done

lemma Top_in_lattice: "Top cl \<in> A"
  apply (simp add: Top_dual_Bot A_def)
  apply (rule dualA_iff [THEN subst])
  apply (rule CLF.Bot_in_lattice [OF dual])
  done

lemma Top_prop: "x \<in> A \<Longrightarrow> (x, Top cl) \<in> r"
  apply (simp add: Top_def greatest_def)
  apply (rule_tac a = "lub A cl" in someI2)
   apply (rule someI2)
    apply (simp_all add: lub_in_lattice lub_upper
      r_def [symmetric] A_def [symmetric])
  done

lemma Bot_prop: "x \<in> A \<Longrightarrow> (Bot cl, x) \<in> r"
  apply (simp add: Bot_dual_Top r_def)
  apply (rule dualr_iff [THEN subst])
  apply (rule CLF.Top_prop [OF dual])
  apply (simp add: dualA_iff A_def)
  done

lemma Top_intv_not_empty: "x \<in> A \<Longrightarrow> interval r x (Top cl) \<noteq> {}"
  apply (rule notI)
  apply (drule_tac a = "Top cl" in equals0D)
  apply (simp add: interval_def)
  apply (simp add: refl_on_def Top_in_lattice Top_prop)
  done

lemma Bot_intv_not_empty: "x \<in> A \<Longrightarrow> interval r (Bot cl) x \<noteq> {}"
  apply (simp add: Bot_dual_Top)
  apply (subst interval_dual)
    prefer 2 apply assumption
   apply (simp add: A_def)
   apply (rule dualA_iff [THEN subst])
   apply (rule CLF.Top_in_lattice [OF dual])
  apply (rule CLF.Top_intv_not_empty [OF dual])
  apply (simp add: dualA_iff A_def)
  done


subsection \<open>fixed points form a partial order\<close>

lemma fixf_po: "\<lparr>pset = P, order = induced P r\<rparr> \<in> PartialOrder"
  by (simp add: P_def fix_subset po_subset_po)

end

context Tarski
begin

lemma Y_subset_A: "Y \<subseteq> A"
  by (rule subset_trans [OF _ fix_subset]) (rule Y_ss [simplified P_def])

lemma lubY_in_A: "lub Y cl \<in> A"
  by (rule Y_subset_A [THEN lub_in_lattice])

lemma lubY_le_flubY: "(lub Y cl, f (lub Y cl)) \<in> r"
  apply (rule lub_least)
    apply (rule Y_subset_A)
   apply (rule f_in_funcset [THEN funcset_mem])
   apply (rule lubY_in_A)
    \<comment> \<open>\<open>Y \<subseteq> P \<Longrightarrow> f x = x\<close>\<close>
  apply (rule ballI)
  apply (rule_tac t = x in fix_imp_eq [THEN subst])
   apply (erule Y_ss [simplified P_def, THEN subsetD])
    \<comment> \<open>\<open>reduce (f x, f (lub Y cl)) \<in> r to (x, lub Y cl) \<in> r\<close> by monotonicity\<close>
  apply (rule_tac f = "f" in monotoneE)
     apply (rule monotone_f)
    apply (simp add: Y_subset_A [THEN subsetD])
   apply (rule lubY_in_A)
  apply (simp add: lub_upper Y_subset_A)
  done

lemma intY1_subset: "intY1 \<subseteq> A"
  apply (unfold intY1_def)
  apply (rule interval_subset)
   apply (rule lubY_in_A)
  apply (rule Top_in_lattice)
  done

lemmas intY1_elem = intY1_subset [THEN subsetD]

lemma intY1_f_closed: "x \<in> intY1 \<Longrightarrow> f x \<in> intY1"
  apply (simp add: intY1_def  interval_def)
  apply (rule conjI)
   apply (rule transE)
    apply (rule lubY_le_flubY)
    \<comment> \<open>\<open>(f (lub Y cl), f x) \<in> r\<close>\<close>
   apply (rule_tac f=f in monotoneE)
      apply (rule monotone_f)
     apply (rule lubY_in_A)
    apply (simp add: intY1_def interval_def  intY1_elem)
   apply (simp add: intY1_def  interval_def)
    \<comment> \<open>\<open>(f x, Top cl) \<in> r\<close>\<close>
  apply (rule Top_prop)
  apply (rule f_in_funcset [THEN funcset_mem])
  apply (simp add: intY1_def interval_def  intY1_elem)
  done

lemma intY1_mono: "monotone (\<lambda> x \<in> intY1. f x) intY1 (induced intY1 r)"
  apply (auto simp add: monotone_def induced_def intY1_f_closed)
  apply (blast intro: intY1_elem monotone_f [THEN monotoneE])
  done

lemma intY1_is_cl: "\<lparr>pset = intY1, order = induced intY1 r\<rparr> \<in> CompleteLattice"
  apply (unfold intY1_def)
  apply (rule interv_is_compl_latt)
    apply (rule lubY_in_A)
   apply (rule Top_in_lattice)
  apply (rule Top_intv_not_empty)
  apply (rule lubY_in_A)
  done

lemma v_in_P: "v \<in> P"
  apply (unfold P_def)
  apply (rule_tac A = intY1 in fixf_subset)
   apply (rule intY1_subset)
  unfolding v_def
  apply (rule CLF.glbH_is_fixp
      [OF CLF.intro, unfolded CLF_set_def, of "\<lparr>pset = intY1, order = induced intY1 r\<rparr>", simplified])
   apply auto
    apply (rule intY1_is_cl)
   apply (erule intY1_f_closed)
  apply (rule intY1_mono)
  done

lemma z_in_interval: "\<lbrakk>z \<in> P; \<forall>y\<in>Y. (y, z) \<in> induced P r\<rbrakk> \<Longrightarrow> z \<in> intY1"
  apply (unfold intY1_def P_def)
  apply (rule intervalI)
   prefer 2
   apply (erule fix_subset [THEN subsetD, THEN Top_prop])
  apply (rule lub_least)
    apply (rule Y_subset_A)
   apply (fast elim!: fix_subset [THEN subsetD])
  apply (simp add: induced_def)
  done

lemma f'z_in_int_rel: "\<lbrakk>z \<in> P; \<forall>y\<in>Y. (y, z) \<in> induced P r\<rbrakk>
  \<Longrightarrow> ((\<lambda>x \<in> intY1. f x) z, z) \<in> induced intY1 r"
  by (simp add: induced_def  intY1_f_closed z_in_interval P_def)
    (simp add: fix_imp_eq [of _ f A] fix_subset [of f A, THEN subsetD] reflE)

lemma tarski_full_lemma: "\<exists>L. isLub Y \<lparr>pset = P, order = induced P r\<rparr> L"
  apply (rule_tac x = "v" in exI)
  apply (simp add: isLub_def)
    \<comment> \<open>\<open>v \<in> P\<close>\<close>
  apply (simp add: v_in_P)
  apply (rule conjI)
    \<comment> \<open>\<open>v\<close> is lub\<close>
    \<comment> \<open>\<open>1. \<forall>y:Y. (y, v) \<in> induced P r\<close>\<close>
   apply (rule ballI)
   apply (simp add: induced_def subsetD v_in_P)
   apply (rule conjI)
    apply (erule Y_ss [THEN subsetD])
   apply (rule_tac b = "lub Y cl" in transE)
    apply (rule lub_upper)
     apply (rule Y_subset_A, assumption)
   apply (rule_tac b = "Top cl" in interval_imp_mem)
   apply (simp add: v_def)
   apply (fold intY1_def)
   apply (rule CL.glb_in_lattice [OF CL.intro [OF intY1_is_cl], simplified])
   apply auto
  apply (rule indI)
    prefer 3 apply assumption
   prefer 2 apply (simp add: v_in_P)
  apply (unfold v_def)
  apply (rule indE)
   apply (rule_tac [2] intY1_subset)
  apply (rule CL.glb_lower [OF CL.intro [OF intY1_is_cl], simplified])
   apply (simp add: CL_imp_PO intY1_is_cl)
   apply force
  apply (simp add: induced_def intY1_f_closed z_in_interval)
  apply (simp add: P_def fix_imp_eq [of _ f A] reflE fix_subset [of f A, THEN subsetD])
  done

end

lemma CompleteLatticeI_simp:
  "\<lbrakk>\<lparr>pset = A, order = r\<rparr> \<in> PartialOrder;
     \<forall>S. S \<subseteq> A \<longrightarrow> (\<exists>L. isLub S \<lparr>pset = A, order = r\<rparr>  L)\<rbrakk>
    \<Longrightarrow> \<lparr>pset = A, order = r\<rparr> \<in> CompleteLattice"
  by (simp add: CompleteLatticeI Rdual)

theorem (in CLF) Tarski_full: "\<lparr>pset = P, order = induced P r\<rparr> \<in> CompleteLattice"
  apply (rule CompleteLatticeI_simp)
   apply (rule fixf_po)
  apply clarify
  apply (simp add: P_def A_def r_def)
  apply (rule Tarski.tarski_full_lemma [OF Tarski.intro [OF _ Tarski_axioms.intro]])
proof -
  show "CLF cl f" ..
qed

end
