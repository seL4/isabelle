(*  Title:      HOL/Metis_Examples/Tarski.thy
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen

Metis example featuring the full theorem of Tarski.
*)

header {* Metis Example Featuring the Full Theorem of Tarski *}

theory Tarski
imports Main "~~/src/HOL/Library/FuncSet"
begin

declare [[metis_new_skolemizer]]

(*Many of these higher-order problems appear to be impossible using the
current linkup. They often seem to need either higher-order unification
or explicit reasoning about connectives such as conjunction. The numerous
set comprehensions are to blame.*)

record 'a potype =
  pset  :: "'a set"
  order :: "('a * 'a) set"

definition monotone :: "['a => 'a, 'a set, ('a *'a)set] => bool" where
  "monotone f A r == \<forall>x\<in>A. \<forall>y\<in>A. (x, y): r --> ((f x), (f y)) : r"

definition least :: "['a => bool, 'a potype] => 'a" where
  "least P po == @ x. x: pset po & P x &
                       (\<forall>y \<in> pset po. P y --> (x,y): order po)"

definition greatest :: "['a => bool, 'a potype] => 'a" where
  "greatest P po == @ x. x: pset po & P x &
                          (\<forall>y \<in> pset po. P y --> (y,x): order po)"

definition lub  :: "['a set, 'a potype] => 'a" where
  "lub S po == least (%x. \<forall>y\<in>S. (y,x): order po) po"

definition glb  :: "['a set, 'a potype] => 'a" where
  "glb S po == greatest (%x. \<forall>y\<in>S. (x,y): order po) po"

definition isLub :: "['a set, 'a potype, 'a] => bool" where
  "isLub S po == %L. (L: pset po & (\<forall>y\<in>S. (y,L): order po) &
                   (\<forall>z\<in>pset po. (\<forall>y\<in>S. (y,z): order po) --> (L,z): order po))"

definition isGlb :: "['a set, 'a potype, 'a] => bool" where
  "isGlb S po == %G. (G: pset po & (\<forall>y\<in>S. (G,y): order po) &
                 (\<forall>z \<in> pset po. (\<forall>y\<in>S. (z,y): order po) --> (z,G): order po))"

definition "fix"    :: "[('a => 'a), 'a set] => 'a set" where
  "fix f A  == {x. x: A & f x = x}"

definition interval :: "[('a*'a) set,'a, 'a ] => 'a set" where
  "interval r a b == {x. (a,x): r & (x,b): r}"

definition Bot :: "'a potype => 'a" where
  "Bot po == least (%x. True) po"

definition Top :: "'a potype => 'a" where
  "Top po == greatest (%x. True) po"

definition PartialOrder :: "('a potype) set" where
  "PartialOrder == {P. refl_on (pset P) (order P) & antisym (order P) &
                       trans (order P)}"

definition CompleteLattice :: "('a potype) set" where
  "CompleteLattice == {cl. cl: PartialOrder &
                        (\<forall>S. S \<subseteq> pset cl --> (\<exists>L. isLub S cl L)) &
                        (\<forall>S. S \<subseteq> pset cl --> (\<exists>G. isGlb S cl G))}"

definition induced :: "['a set, ('a * 'a) set] => ('a *'a)set" where
  "induced A r == {(a,b). a : A & b: A & (a,b): r}"

definition sublattice :: "('a potype * 'a set)set" where
  "sublattice ==
      SIGMA cl: CompleteLattice.
          {S. S \<subseteq> pset cl &
           (| pset = S, order = induced S (order cl) |): CompleteLattice }"

abbreviation
  sublattice_syntax :: "['a set, 'a potype] => bool" ("_ <<= _" [51, 50] 50)
  where "S <<= cl \<equiv> S : sublattice `` {cl}"

definition dual :: "'a potype => 'a potype" where
  "dual po == (| pset = pset po, order = converse (order po) |)"

locale PO =
  fixes cl :: "'a potype"
    and A  :: "'a set"
    and r  :: "('a * 'a) set"
  assumes cl_po:  "cl : PartialOrder"
  defines A_def: "A == pset cl"
     and  r_def: "r == order cl"

locale CL = PO +
  assumes cl_co:  "cl : CompleteLattice"

definition CLF_set :: "('a potype * ('a => 'a)) set" where
  "CLF_set = (SIGMA cl: CompleteLattice.
            {f. f: pset cl -> pset cl & monotone f (pset cl) (order cl)})"

locale CLF = CL +
  fixes f :: "'a => 'a"
    and P :: "'a set"
  assumes f_cl:  "(cl,f) : CLF_set" (*was the equivalent "f : CLF``{cl}"*)
  defines P_def: "P == fix f A"

locale Tarski = CLF +
  fixes Y     :: "'a set"
    and intY1 :: "'a set"
    and v     :: "'a"
  assumes
    Y_ss: "Y \<subseteq> P"
  defines
    intY1_def: "intY1 == interval r (lub Y cl) (Top cl)"
    and v_def: "v == glb {x. ((%x: intY1. f x) x, x): induced intY1 r &
                             x: intY1}
                      (| pset=intY1, order=induced intY1 r|)"

subsection {* Partial Order *}

lemma (in PO) PO_imp_refl_on: "refl_on A r"
apply (insert cl_po)
apply (simp add: PartialOrder_def A_def r_def)
done

lemma (in PO) PO_imp_sym: "antisym r"
apply (insert cl_po)
apply (simp add: PartialOrder_def r_def)
done

lemma (in PO) PO_imp_trans: "trans r"
apply (insert cl_po)
apply (simp add: PartialOrder_def r_def)
done

lemma (in PO) reflE: "x \<in> A ==> (x, x) \<in> r"
apply (insert cl_po)
apply (simp add: PartialOrder_def refl_on_def A_def r_def)
done

lemma (in PO) antisymE: "[| (a, b) \<in> r; (b, a) \<in> r |] ==> a = b"
apply (insert cl_po)
apply (simp add: PartialOrder_def antisym_def r_def)
done

lemma (in PO) transE: "[| (a, b) \<in> r; (b, c) \<in> r|] ==> (a,c) \<in> r"
apply (insert cl_po)
apply (simp add: PartialOrder_def r_def)
apply (unfold trans_def, fast)
done

lemma (in PO) monotoneE:
     "[| monotone f A r;  x \<in> A; y \<in> A; (x, y) \<in> r |] ==> (f x, f y) \<in> r"
by (simp add: monotone_def)

lemma (in PO) po_subset_po:
     "S \<subseteq> A ==> (| pset = S, order = induced S r |) \<in> PartialOrder"
apply (simp (no_asm) add: PartialOrder_def)
apply auto
-- {* refl *}
apply (simp add: refl_on_def induced_def)
apply (blast intro: reflE)
-- {* antisym *}
apply (simp add: antisym_def induced_def)
apply (blast intro: antisymE)
-- {* trans *}
apply (simp add: trans_def induced_def)
apply (blast intro: transE)
done

lemma (in PO) indE: "[| (x, y) \<in> induced S r; S \<subseteq> A |] ==> (x, y) \<in> r"
by (simp add: add: induced_def)

lemma (in PO) indI: "[| (x, y) \<in> r; x \<in> S; y \<in> S |] ==> (x, y) \<in> induced S r"
by (simp add: add: induced_def)

lemma (in CL) CL_imp_ex_isLub: "S \<subseteq> A ==> \<exists>L. isLub S cl L"
apply (insert cl_co)
apply (simp add: CompleteLattice_def A_def)
done

declare (in CL) cl_co [simp]

lemma isLub_lub: "(\<exists>L. isLub S cl L) = isLub S cl (lub S cl)"
by (simp add: lub_def least_def isLub_def some_eq_ex [symmetric])

lemma isGlb_glb: "(\<exists>G. isGlb S cl G) = isGlb S cl (glb S cl)"
by (simp add: glb_def greatest_def isGlb_def some_eq_ex [symmetric])

lemma isGlb_dual_isLub: "isGlb S cl = isLub S (dual cl)"
by (simp add: isLub_def isGlb_def dual_def converse_def)

lemma isLub_dual_isGlb: "isLub S cl = isGlb S (dual cl)"
by (simp add: isLub_def isGlb_def dual_def converse_def)

lemma (in PO) dualPO: "dual cl \<in> PartialOrder"
apply (insert cl_po)
apply (simp add: PartialOrder_def dual_def)
done

lemma Rdual:
     "\<forall>S. (S \<subseteq> A -->( \<exists>L. isLub S (| pset = A, order = r|) L))
      ==> \<forall>S. (S \<subseteq> A --> (\<exists>G. isGlb S (| pset = A, order = r|) G))"
apply safe
apply (rule_tac x = "lub {y. y \<in> A & (\<forall>k \<in> S. (y, k) \<in> r)}
                      (|pset = A, order = r|) " in exI)
apply (drule_tac x = "{y. y \<in> A & (\<forall>k \<in> S. (y,k) \<in> r) }" in spec)
apply (drule mp, fast)
apply (simp add: isLub_lub isGlb_def)
apply (simp add: isLub_def, blast)
done

lemma lub_dual_glb: "lub S cl = glb S (dual cl)"
by (simp add: lub_def glb_def least_def greatest_def dual_def converse_def)

lemma glb_dual_lub: "glb S cl = lub S (dual cl)"
by (simp add: lub_def glb_def least_def greatest_def dual_def converse_def)

lemma CL_subset_PO: "CompleteLattice \<subseteq> PartialOrder"
by (simp add: PartialOrder_def CompleteLattice_def, fast)

lemmas CL_imp_PO = CL_subset_PO [THEN subsetD]

declare PO.PO_imp_refl_on  [OF PO.intro [OF CL_imp_PO], simp]
declare PO.PO_imp_sym   [OF PO.intro [OF CL_imp_PO], simp]
declare PO.PO_imp_trans [OF PO.intro [OF CL_imp_PO], simp]

lemma (in CL) CO_refl_on: "refl_on A r"
by (rule PO_imp_refl_on)

lemma (in CL) CO_antisym: "antisym r"
by (rule PO_imp_sym)

lemma (in CL) CO_trans: "trans r"
by (rule PO_imp_trans)

lemma CompleteLatticeI:
     "[| po \<in> PartialOrder; (\<forall>S. S \<subseteq> pset po --> (\<exists>L. isLub S po L));
         (\<forall>S. S \<subseteq> pset po --> (\<exists>G. isGlb S po G))|]
      ==> po \<in> CompleteLattice"
apply (unfold CompleteLattice_def, blast)
done

lemma (in CL) CL_dualCL: "dual cl \<in> CompleteLattice"
apply (insert cl_co)
apply (simp add: CompleteLattice_def dual_def)
apply (fold dual_def)
apply (simp add: isLub_dual_isGlb [symmetric] isGlb_dual_isLub [symmetric]
                 dualPO)
done

lemma (in PO) dualA_iff: "pset (dual cl) = pset cl"
by (simp add: dual_def)

lemma (in PO) dualr_iff: "((x, y) \<in> (order(dual cl))) = ((y, x) \<in> order cl)"
by (simp add: dual_def)

lemma (in PO) monotone_dual:
     "monotone f (pset cl) (order cl)
     ==> monotone f (pset (dual cl)) (order(dual cl))"
by (simp add: monotone_def dualA_iff dualr_iff)

lemma (in PO) interval_dual:
     "[| x \<in> A; y \<in> A|] ==> interval r x y = interval (order(dual cl)) y x"
apply (simp add: interval_def dualr_iff)
apply (fold r_def, fast)
done

lemma (in PO) interval_not_empty:
     "[| trans r; interval r a b \<noteq> {} |] ==> (a, b) \<in> r"
apply (simp add: interval_def)
apply (unfold trans_def, blast)
done

lemma (in PO) interval_imp_mem: "x \<in> interval r a b ==> (a, x) \<in> r"
by (simp add: interval_def)

lemma (in PO) left_in_interval:
     "[| a \<in> A; b \<in> A; interval r a b \<noteq> {} |] ==> a \<in> interval r a b"
apply (simp (no_asm_simp) add: interval_def)
apply (simp add: PO_imp_trans interval_not_empty)
apply (simp add: reflE)
done

lemma (in PO) right_in_interval:
     "[| a \<in> A; b \<in> A; interval r a b \<noteq> {} |] ==> b \<in> interval r a b"
apply (simp (no_asm_simp) add: interval_def)
apply (simp add: PO_imp_trans interval_not_empty)
apply (simp add: reflE)
done

subsection {* sublattice *}

lemma (in PO) sublattice_imp_CL:
     "S <<= cl  ==> (| pset = S, order = induced S r |) \<in> CompleteLattice"
by (simp add: sublattice_def CompleteLattice_def A_def r_def)

lemma (in CL) sublatticeI:
     "[| S \<subseteq> A; (| pset = S, order = induced S r |) \<in> CompleteLattice |]
      ==> S <<= cl"
by (simp add: sublattice_def A_def r_def)

subsection {* lub *}

lemma (in CL) lub_unique: "[| S \<subseteq> A; isLub S cl x; isLub S cl L|] ==> x = L"
apply (rule antisymE)
apply (auto simp add: isLub_def r_def)
done

lemma (in CL) lub_upper: "[|S \<subseteq> A; x \<in> S|] ==> (x, lub S cl) \<in> r"
apply (rule CL_imp_ex_isLub [THEN exE], assumption)
apply (unfold lub_def least_def)
apply (rule some_equality [THEN ssubst])
  apply (simp add: isLub_def)
 apply (simp add: lub_unique A_def isLub_def)
apply (simp add: isLub_def r_def)
done

lemma (in CL) lub_least:
     "[| S \<subseteq> A; L \<in> A; \<forall>x \<in> S. (x,L) \<in> r |] ==> (lub S cl, L) \<in> r"
apply (rule CL_imp_ex_isLub [THEN exE], assumption)
apply (unfold lub_def least_def)
apply (rule_tac s=x in some_equality [THEN ssubst])
  apply (simp add: isLub_def)
 apply (simp add: lub_unique A_def isLub_def)
apply (simp add: isLub_def r_def A_def)
done

lemma (in CL) lub_in_lattice: "S \<subseteq> A ==> lub S cl \<in> A"
apply (rule CL_imp_ex_isLub [THEN exE], assumption)
apply (unfold lub_def least_def)
apply (subst some_equality)
apply (simp add: isLub_def)
prefer 2 apply (simp add: isLub_def A_def)
apply (simp add: lub_unique A_def isLub_def)
done

lemma (in CL) lubI:
     "[| S \<subseteq> A; L \<in> A; \<forall>x \<in> S. (x,L) \<in> r;
         \<forall>z \<in> A. (\<forall>y \<in> S. (y,z) \<in> r) --> (L,z) \<in> r |] ==> L = lub S cl"
apply (rule lub_unique, assumption)
apply (simp add: isLub_def A_def r_def)
apply (unfold isLub_def)
apply (rule conjI)
apply (fold A_def r_def)
apply (rule lub_in_lattice, assumption)
apply (simp add: lub_upper lub_least)
done

lemma (in CL) lubIa: "[| S \<subseteq> A; isLub S cl L |] ==> L = lub S cl"
by (simp add: lubI isLub_def A_def r_def)

lemma (in CL) isLub_in_lattice: "isLub S cl L ==> L \<in> A"
by (simp add: isLub_def  A_def)

lemma (in CL) isLub_upper: "[|isLub S cl L; y \<in> S|] ==> (y, L) \<in> r"
by (simp add: isLub_def r_def)

lemma (in CL) isLub_least:
     "[| isLub S cl L; z \<in> A; \<forall>y \<in> S. (y, z) \<in> r|] ==> (L, z) \<in> r"
by (simp add: isLub_def A_def r_def)

lemma (in CL) isLubI:
     "[| L \<in> A; \<forall>y \<in> S. (y, L) \<in> r;
         (\<forall>z \<in> A. (\<forall>y \<in> S. (y, z):r) --> (L, z) \<in> r)|] ==> isLub S cl L"
by (simp add: isLub_def A_def r_def)

subsection {* glb *}

lemma (in CL) glb_in_lattice: "S \<subseteq> A ==> glb S cl \<in> A"
apply (subst glb_dual_lub)
apply (simp add: A_def)
apply (rule dualA_iff [THEN subst])
apply (rule CL.lub_in_lattice)
apply (rule CL.intro)
apply (rule PO.intro)
apply (rule dualPO)
apply (rule CL_axioms.intro)
apply (rule CL_dualCL)
apply (simp add: dualA_iff)
done

lemma (in CL) glb_lower: "[|S \<subseteq> A; x \<in> S|] ==> (glb S cl, x) \<in> r"
apply (subst glb_dual_lub)
apply (simp add: r_def)
apply (rule dualr_iff [THEN subst])
apply (rule CL.lub_upper)
apply (rule CL.intro)
apply (rule PO.intro)
apply (rule dualPO)
apply (rule CL_axioms.intro)
apply (rule CL_dualCL)
apply (simp add: dualA_iff A_def, assumption)
done

text {*
  Reduce the sublattice property by using substructural properties;
  abandoned see @{text "Tarski_4.ML"}.
*}

declare (in CLF) f_cl [simp]

lemma (in CLF) [simp]:
    "f: pset cl -> pset cl & monotone f (pset cl) (order cl)"
proof -
  have "\<forall>u v. (v, u) \<in> CLF_set \<longrightarrow> u \<in> {R \<in> pset v \<rightarrow> pset v. monotone R (pset v) (order v)}"
    unfolding CLF_set_def using SigmaE2 by blast
  hence F1: "\<forall>u v. (v, u) \<in> CLF_set \<longrightarrow> u \<in> pset v \<rightarrow> pset v \<and> monotone u (pset v) (order v)"
    using CollectE by blast
  hence "Tarski.monotone f (pset cl) (order cl)" by (metis f_cl)
  hence "(cl, f) \<in> CLF_set \<and> Tarski.monotone f (pset cl) (order cl)"
    by (metis f_cl)
  thus "f \<in> pset cl \<rightarrow> pset cl \<and> Tarski.monotone f (pset cl) (order cl)"
    using F1 by metis
qed

lemma (in CLF) f_in_funcset: "f \<in> A -> A"
by (simp add: A_def)

lemma (in CLF) monotone_f: "monotone f A r"
by (simp add: A_def r_def)

(*never proved, 2007-01-22*)

declare (in CLF) CLF_set_def [simp] CL_dualCL [simp] monotone_dual [simp] dualA_iff [simp]

lemma (in CLF) CLF_dual: "(dual cl, f) \<in> CLF_set"
apply (simp del: dualA_iff)
apply (simp)
done

declare (in CLF) CLF_set_def[simp del] CL_dualCL[simp del] monotone_dual[simp del]
          dualA_iff[simp del]

subsection {* fixed points *}

lemma fix_subset: "fix f A \<subseteq> A"
by (simp add: fix_def, fast)

lemma fix_imp_eq: "x \<in> fix f A ==> f x = x"
by (simp add: fix_def)

lemma fixf_subset:
     "[| A \<subseteq> B; x \<in> fix (%y: A. f y) A |] ==> x \<in> fix f B"
by (simp add: fix_def, auto)

subsection {* lemmas for Tarski, lub *}

(*never proved, 2007-01-22*)

declare CL.lub_least[intro] CLF.f_in_funcset[intro] funcset_mem[intro] CL.lub_in_lattice[intro] PO.transE[intro] PO.monotoneE[intro] CLF.monotone_f[intro] CL.lub_upper[intro]

lemma (in CLF) lubH_le_flubH:
     "H = {x. (x, f x) \<in> r & x \<in> A} ==> (lub H cl, f (lub H cl)) \<in> r"
apply (rule lub_least, fast)
apply (rule f_in_funcset [THEN funcset_mem])
apply (rule lub_in_lattice, fast)
-- {* @{text "\<forall>x:H. (x, f (lub H r)) \<in> r"} *}
apply (rule ballI)
(*never proved, 2007-01-22*)
apply (rule transE)
-- {* instantiates @{text "(x, ?z) \<in> order cl to (x, f x)"}, *}
-- {* because of the def of @{text H} *}
apply fast
-- {* so it remains to show @{text "(f x, f (lub H cl)) \<in> r"} *}
apply (rule_tac f = "f" in monotoneE)
apply (rule monotone_f, fast)
apply (rule lub_in_lattice, fast)
apply (rule lub_upper, fast)
apply assumption
done

declare CL.lub_least[rule del] CLF.f_in_funcset[rule del]
        funcset_mem[rule del] CL.lub_in_lattice[rule del]
        PO.transE[rule del] PO.monotoneE[rule del]
        CLF.monotone_f[rule del] CL.lub_upper[rule del]

(*never proved, 2007-01-22*)

declare CLF.f_in_funcset[intro] funcset_mem[intro] CL.lub_in_lattice[intro]
     PO.monotoneE[intro] CLF.monotone_f[intro] CL.lub_upper[intro]
     CLF.lubH_le_flubH[simp]

lemma (in CLF) flubH_le_lubH:
     "[|  H = {x. (x, f x) \<in> r & x \<in> A} |] ==> (f (lub H cl), lub H cl) \<in> r"
apply (rule lub_upper, fast)
apply (rule_tac t = "H" in ssubst, assumption)
apply (rule CollectI)
apply (rule conjI)
(*??no longer terminates, with combinators
apply (metis CO_refl_on lubH_le_flubH monotone_def monotone_f reflD1 reflD2)
*)
apply (metis CO_refl_on lubH_le_flubH monotoneE [OF monotone_f] refl_onD1 refl_onD2)
apply (metis CO_refl_on lubH_le_flubH refl_onD2)
done

declare CLF.f_in_funcset[rule del] funcset_mem[rule del]
        CL.lub_in_lattice[rule del] PO.monotoneE[rule del]
        CLF.monotone_f[rule del] CL.lub_upper[rule del]
        CLF.lubH_le_flubH[simp del]

(*never proved, 2007-01-22*)

(* Single-step version fails. The conjecture clauses refer to local abstraction
functions (Frees). *)
lemma (in CLF) lubH_is_fixp:
     "H = {x. (x, f x) \<in> r & x \<in> A} ==> lub H cl \<in> fix f A"
apply (simp add: fix_def)
apply (rule conjI)
proof -
  assume A1: "H = {x. (x, f x) \<in> r \<and> x \<in> A}"
  have F1: "\<forall>u v. v \<inter> u \<subseteq> u" by (metis Int_commute Int_lower1)
  have "{R. (R, f R) \<in> r} \<inter> {R. R \<in> A} = H" using A1 by (metis Collect_conj_eq)
  hence "H \<subseteq> {R. R \<in> A}" using F1 by metis
  hence "H \<subseteq> A" by (metis Collect_mem_eq)
  hence "lub H cl \<in> A" by (metis lub_in_lattice)
  thus "lub {x. (x, f x) \<in> r \<and> x \<in> A} cl \<in> A" using A1 by metis
next
  assume A1: "H = {x. (x, f x) \<in> r \<and> x \<in> A}"
  have F1: "\<forall>v. {R. R \<in> v} = v" by (metis Collect_mem_eq)
  have F2: "\<forall>w u. {R. R \<in> u \<and> R \<in> w} = u \<inter> w"
    by (metis Collect_conj_eq Collect_mem_eq)
  have F3: "\<forall>x v. {R. v R \<in> x} = v -` x" by (metis vimage_def)
  hence F4: "A \<inter> (\<lambda>R. (R, f R)) -` r = H" using A1 by auto
  hence F5: "(f (lub H cl), lub H cl) \<in> r" 
    by (metis A1 flubH_le_lubH)
  have F6: "(lub H cl, f (lub H cl)) \<in> r"
    by (metis A1 lubH_le_flubH)
  have "(lub H cl, f (lub H cl)) \<in> r \<longrightarrow> f (lub H cl) = lub H cl"
    using F5 by (metis antisymE)
  hence "f (lub H cl) = lub H cl" using F6 by metis
  thus "H = {x. (x, f x) \<in> r \<and> x \<in> A}
        \<Longrightarrow> f (lub {x. (x, f x) \<in> r \<and> x \<in> A} cl) =
           lub {x. (x, f x) \<in> r \<and> x \<in> A} cl"
    by metis
qed

lemma (in CLF) (*lubH_is_fixp:*)
     "H = {x. (x, f x) \<in> r & x \<in> A} ==> lub H cl \<in> fix f A"
apply (simp add: fix_def)
apply (rule conjI)
apply (metis CO_refl_on lubH_le_flubH refl_onD1)
apply (metis antisymE flubH_le_lubH lubH_le_flubH)
done

lemma (in CLF) fix_in_H:
     "[| H = {x. (x, f x) \<in> r & x \<in> A};  x \<in> P |] ==> x \<in> H"
by (simp add: P_def fix_imp_eq [of _ f A] reflE CO_refl_on
                    fix_subset [of f A, THEN subsetD])

lemma (in CLF) fixf_le_lubH:
     "H = {x. (x, f x) \<in> r & x \<in> A} ==> \<forall>x \<in> fix f A. (x, lub H cl) \<in> r"
apply (rule ballI)
apply (rule lub_upper, fast)
apply (rule fix_in_H)
apply (simp_all add: P_def)
done

lemma (in CLF) lubH_least_fixf:
     "H = {x. (x, f x) \<in> r & x \<in> A}
      ==> \<forall>L. (\<forall>y \<in> fix f A. (y,L) \<in> r) --> (lub H cl, L) \<in> r"
apply (metis P_def lubH_is_fixp)
done

subsection {* Tarski fixpoint theorem 1, first part *}

declare CL.lubI[intro] fix_subset[intro] CL.lub_in_lattice[intro]
        CLF.fixf_le_lubH[simp] CLF.lubH_least_fixf[simp]

lemma (in CLF) T_thm_1_lub: "lub P cl = lub {x. (x, f x) \<in> r & x \<in> A} cl"
(*sledgehammer;*)
apply (rule sym)
apply (simp add: P_def)
apply (rule lubI)
apply (metis P_def fix_subset)
apply (metis Collect_conj_eq Collect_mem_eq Int_commute Int_lower1 lub_in_lattice vimage_def)
(*??no longer terminates, with combinators
apply (metis P_def fix_def fixf_le_lubH)
apply (metis P_def fix_def lubH_least_fixf)
*)
apply (simp add: fixf_le_lubH)
apply (simp add: lubH_least_fixf)
done

declare CL.lubI[rule del] fix_subset[rule del] CL.lub_in_lattice[rule del]
        CLF.fixf_le_lubH[simp del] CLF.lubH_least_fixf[simp del]

(*never proved, 2007-01-22*)

declare glb_dual_lub[simp] PO.dualA_iff[intro] CLF.lubH_is_fixp[intro]
        PO.dualPO[intro] CL.CL_dualCL[intro] PO.dualr_iff[simp]

lemma (in CLF) glbH_is_fixp: "H = {x. (f x, x) \<in> r & x \<in> A} ==> glb H cl \<in> P"
  -- {* Tarski for glb *}
(*sledgehammer;*)
apply (simp add: glb_dual_lub P_def A_def r_def)
apply (rule dualA_iff [THEN subst])
apply (rule CLF.lubH_is_fixp)
apply (rule CLF.intro)
apply (rule CL.intro)
apply (rule PO.intro)
apply (rule dualPO)
apply (rule CL_axioms.intro)
apply (rule CL_dualCL)
apply (rule CLF_axioms.intro)
apply (rule CLF_dual)
apply (simp add: dualr_iff dualA_iff)
done

declare glb_dual_lub[simp del] PO.dualA_iff[rule del] CLF.lubH_is_fixp[rule del]
        PO.dualPO[rule del] CL.CL_dualCL[rule del] PO.dualr_iff[simp del]

(*never proved, 2007-01-22*)

lemma (in CLF) T_thm_1_glb: "glb P cl = glb {x. (f x, x) \<in> r & x \<in> A} cl"
(*sledgehammer;*)
apply (simp add: glb_dual_lub P_def A_def r_def)
apply (rule dualA_iff [THEN subst])
(*never proved, 2007-01-22*)
(*sledgehammer;*)
apply (simp add: CLF.T_thm_1_lub [of _ f, OF CLF.intro, OF CL.intro CLF_axioms.intro, OF PO.intro CL_axioms.intro,
  OF dualPO CL_dualCL] dualPO CL_dualCL CLF_dual dualr_iff)
done

subsection {* interval *}

declare (in CLF) CO_refl_on[simp] refl_on_def [simp]

lemma (in CLF) rel_imp_elem: "(x, y) \<in> r ==> x \<in> A"
by (metis CO_refl_on refl_onD1)

declare (in CLF) CO_refl_on[simp del]  refl_on_def [simp del]

declare (in CLF) rel_imp_elem[intro]
declare interval_def [simp]

lemma (in CLF) interval_subset: "[| a \<in> A; b \<in> A |] ==> interval r a b \<subseteq> A"
by (metis CO_refl_on interval_imp_mem refl_onD refl_onD2 rel_imp_elem subset_eq)

declare (in CLF) rel_imp_elem[rule del]
declare interval_def [simp del]

lemma (in CLF) intervalI:
     "[| (a, x) \<in> r; (x, b) \<in> r |] ==> x \<in> interval r a b"
by (simp add: interval_def)

lemma (in CLF) interval_lemma1:
     "[| S \<subseteq> interval r a b; x \<in> S |] ==> (a, x) \<in> r"
by (unfold interval_def, fast)

lemma (in CLF) interval_lemma2:
     "[| S \<subseteq> interval r a b; x \<in> S |] ==> (x, b) \<in> r"
by (unfold interval_def, fast)

lemma (in CLF) a_less_lub:
     "[| S \<subseteq> A; S \<noteq> {};
         \<forall>x \<in> S. (a,x) \<in> r; \<forall>y \<in> S. (y, L) \<in> r |] ==> (a,L) \<in> r"
by (blast intro: transE)

lemma (in CLF) glb_less_b:
     "[| S \<subseteq> A; S \<noteq> {};
         \<forall>x \<in> S. (x,b) \<in> r; \<forall>y \<in> S. (G, y) \<in> r |] ==> (G,b) \<in> r"
by (blast intro: transE)

lemma (in CLF) S_intv_cl:
     "[| a \<in> A; b \<in> A; S \<subseteq> interval r a b |]==> S \<subseteq> A"
by (simp add: subset_trans [OF _ interval_subset])


lemma (in CLF) L_in_interval:
     "[| a \<in> A; b \<in> A; S \<subseteq> interval r a b;
         S \<noteq> {}; isLub S cl L; interval r a b \<noteq> {} |] ==> L \<in> interval r a b"
(*WON'T TERMINATE
apply (metis CO_trans intervalI interval_lemma1 interval_lemma2 isLub_least isLub_upper subset_empty subset_iff trans_def)
*)
apply (rule intervalI)
apply (rule a_less_lub)
prefer 2 apply assumption
apply (simp add: S_intv_cl)
apply (rule ballI)
apply (simp add: interval_lemma1)
apply (simp add: isLub_upper)
-- {* @{text "(L, b) \<in> r"} *}
apply (simp add: isLub_least interval_lemma2)
done

(*never proved, 2007-01-22*)

lemma (in CLF) G_in_interval:
     "[| a \<in> A; b \<in> A; interval r a b \<noteq> {}; S \<subseteq> interval r a b; isGlb S cl G;
         S \<noteq> {} |] ==> G \<in> interval r a b"
apply (simp add: interval_dual)
apply (simp add: CLF.L_in_interval [of _ f, OF CLF.intro, OF CL.intro CLF_axioms.intro, OF PO.intro CL_axioms.intro]
                 dualA_iff A_def dualPO CL_dualCL CLF_dual isGlb_dual_isLub)
done


lemma (in CLF) intervalPO:
     "[| a \<in> A; b \<in> A; interval r a b \<noteq> {} |]
      ==> (| pset = interval r a b, order = induced (interval r a b) r |)
          \<in> PartialOrder"
proof -
  assume A1: "a \<in> A"
  assume "b \<in> A"
  hence "\<forall>u. u \<in> A \<longrightarrow> interval r u b \<subseteq> A" by (metis interval_subset)
  hence "interval r a b \<subseteq> A" using A1 by metis
  hence "interval r a b \<subseteq> A" by metis
  thus ?thesis by (metis po_subset_po)
qed

lemma (in CLF) intv_CL_lub:
 "[| a \<in> A; b \<in> A; interval r a b \<noteq> {} |]
  ==> \<forall>S. S \<subseteq> interval r a b -->
          (\<exists>L. isLub S (| pset = interval r a b,
                          order = induced (interval r a b) r |)  L)"
apply (intro strip)
apply (frule S_intv_cl [THEN CL_imp_ex_isLub])
prefer 2 apply assumption
apply assumption
apply (erule exE)
-- {* define the lub for the interval as *}
apply (rule_tac x = "if S = {} then a else L" in exI)
apply (simp (no_asm_simp) add: isLub_def split del: split_if)
apply (intro impI conjI)
-- {* @{text "(if S = {} then a else L) \<in> interval r a b"} *}
apply (simp add: CL_imp_PO L_in_interval)
apply (simp add: left_in_interval)
-- {* lub prop 1 *}
apply (case_tac "S = {}")
-- {* @{text "S = {}, y \<in> S = False => everything"} *}
apply fast
-- {* @{text "S \<noteq> {}"} *}
apply simp
-- {* @{text "\<forall>y:S. (y, L) \<in> induced (interval r a b) r"} *}
apply (rule ballI)
apply (simp add: induced_def  L_in_interval)
apply (rule conjI)
apply (rule subsetD)
apply (simp add: S_intv_cl, assumption)
apply (simp add: isLub_upper)
-- {* @{text "\<forall>z:interval r a b. (\<forall>y:S. (y, z) \<in> induced (interval r a b) r \<longrightarrow> (if S = {} then a else L, z) \<in> induced (interval r a b) r"} *}
apply (rule ballI)
apply (rule impI)
apply (case_tac "S = {}")
-- {* @{text "S = {}"} *}
apply simp
apply (simp add: induced_def  interval_def)
apply (rule conjI)
apply (rule reflE, assumption)
apply (rule interval_not_empty)
apply (rule CO_trans)
apply (simp add: interval_def)
-- {* @{text "S \<noteq> {}"} *}
apply simp
apply (simp add: induced_def  L_in_interval)
apply (rule isLub_least, assumption)
apply (rule subsetD)
prefer 2 apply assumption
apply (simp add: S_intv_cl, fast)
done

lemmas (in CLF) intv_CL_glb = intv_CL_lub [THEN Rdual]

(*never proved, 2007-01-22*)

lemma (in CLF) interval_is_sublattice:
     "[| a \<in> A; b \<in> A; interval r a b \<noteq> {} |]
        ==> interval r a b <<= cl"
(*sledgehammer *)
apply (rule sublatticeI)
apply (simp add: interval_subset)
(*never proved, 2007-01-22*)
(*sledgehammer *)
apply (rule CompleteLatticeI)
apply (simp add: intervalPO)
 apply (simp add: intv_CL_lub)
apply (simp add: intv_CL_glb)
done

lemmas (in CLF) interv_is_compl_latt =
    interval_is_sublattice [THEN sublattice_imp_CL]

subsection {* Top and Bottom *}
lemma (in CLF) Top_dual_Bot: "Top cl = Bot (dual cl)"
by (simp add: Top_def Bot_def least_def greatest_def dualA_iff dualr_iff)

lemma (in CLF) Bot_dual_Top: "Bot cl = Top (dual cl)"
by (simp add: Top_def Bot_def least_def greatest_def dualA_iff dualr_iff)


lemma (in CLF) Bot_in_lattice: "Bot cl \<in> A"
(*sledgehammer; *)
apply (simp add: Bot_def least_def)
apply (rule_tac a="glb A cl" in someI2)
apply (simp_all add: glb_in_lattice glb_lower
                     r_def [symmetric] A_def [symmetric])
done

(*first proved 2007-01-25 after relaxing relevance*)

lemma (in CLF) Top_in_lattice: "Top cl \<in> A"
(*sledgehammer;*)
apply (simp add: Top_dual_Bot A_def)
(*first proved 2007-01-25 after relaxing relevance*)
(*sledgehammer*)
apply (rule dualA_iff [THEN subst])
apply (blast intro!: CLF.Bot_in_lattice [OF CLF.intro, OF CL.intro CLF_axioms.intro, OF PO.intro CL_axioms.intro] dualPO CL_dualCL CLF_dual)
done

lemma (in CLF) Top_prop: "x \<in> A ==> (x, Top cl) \<in> r"
apply (simp add: Top_def greatest_def)
apply (rule_tac a="lub A cl" in someI2)
apply (rule someI2)
apply (simp_all add: lub_in_lattice lub_upper
                     r_def [symmetric] A_def [symmetric])
done

(*never proved, 2007-01-22*)

lemma (in CLF) Bot_prop: "x \<in> A ==> (Bot cl, x) \<in> r"
(*sledgehammer*)
apply (simp add: Bot_dual_Top r_def)
apply (rule dualr_iff [THEN subst])
apply (simp add: CLF.Top_prop [of _ f, OF CLF.intro, OF CL.intro CLF_axioms.intro, OF PO.intro CL_axioms.intro]
                 dualA_iff A_def dualPO CL_dualCL CLF_dual)
done


lemma (in CLF) Top_intv_not_empty: "x \<in> A  ==> interval r x (Top cl) \<noteq> {}"
apply (metis Top_in_lattice Top_prop empty_iff intervalI reflE)
done


lemma (in CLF) Bot_intv_not_empty: "x \<in> A ==> interval r (Bot cl) x \<noteq> {}"
apply (metis Bot_prop ex_in_conv intervalI reflE rel_imp_elem)
done

subsection {* fixed points form a partial order *}

lemma (in CLF) fixf_po: "(| pset = P, order = induced P r|) \<in> PartialOrder"
by (simp add: P_def fix_subset po_subset_po)

(*first proved 2007-01-25 after relaxing relevance*)

declare (in Tarski) P_def[simp] Y_ss [simp]
declare fix_subset [intro] subset_trans [intro]

lemma (in Tarski) Y_subset_A: "Y \<subseteq> A"
(*sledgehammer*)
apply (rule subset_trans [OF _ fix_subset])
apply (rule Y_ss [simplified P_def])
done

declare (in Tarski) P_def[simp del] Y_ss [simp del]
declare fix_subset [rule del] subset_trans [rule del]

lemma (in Tarski) lubY_in_A: "lub Y cl \<in> A"
  by (rule Y_subset_A [THEN lub_in_lattice])

(*never proved, 2007-01-22*)

lemma (in Tarski) lubY_le_flubY: "(lub Y cl, f (lub Y cl)) \<in> r"
(*sledgehammer*)
apply (rule lub_least)
apply (rule Y_subset_A)
apply (rule f_in_funcset [THEN funcset_mem])
apply (rule lubY_in_A)
-- {* @{text "Y \<subseteq> P ==> f x = x"} *}
apply (rule ballI)
(*sledgehammer *)
apply (rule_tac t = "x" in fix_imp_eq [THEN subst])
apply (erule Y_ss [simplified P_def, THEN subsetD])
-- {* @{text "reduce (f x, f (lub Y cl)) \<in> r to (x, lub Y cl) \<in> r"} by monotonicity *}
(*sledgehammer*)
apply (rule_tac f = "f" in monotoneE)
apply (rule monotone_f)
apply (simp add: Y_subset_A [THEN subsetD])
apply (rule lubY_in_A)
apply (simp add: lub_upper Y_subset_A)
done

(*first proved 2007-01-25 after relaxing relevance*)

lemma (in Tarski) intY1_subset: "intY1 \<subseteq> A"
(*sledgehammer*)
apply (unfold intY1_def)
apply (rule interval_subset)
apply (rule lubY_in_A)
apply (rule Top_in_lattice)
done

lemmas (in Tarski) intY1_elem = intY1_subset [THEN subsetD]

(*never proved, 2007-01-22*)

lemma (in Tarski) intY1_f_closed: "x \<in> intY1 \<Longrightarrow> f x \<in> intY1"
(*sledgehammer*)
apply (simp add: intY1_def  interval_def)
apply (rule conjI)
apply (rule transE)
apply (rule lubY_le_flubY)
-- {* @{text "(f (lub Y cl), f x) \<in> r"} *}
(*sledgehammer [has been proved before now...]*)
apply (rule_tac f=f in monotoneE)
apply (rule monotone_f)
apply (rule lubY_in_A)
apply (simp add: intY1_def interval_def  intY1_elem)
apply (simp add: intY1_def  interval_def)
-- {* @{text "(f x, Top cl) \<in> r"} *}
apply (rule Top_prop)
apply (rule f_in_funcset [THEN funcset_mem])
apply (simp add: intY1_def interval_def  intY1_elem)
done


lemma (in Tarski) intY1_func: "(%x: intY1. f x) \<in> intY1 -> intY1"
apply (rule restrict_in_funcset)
apply (metis intY1_f_closed restrict_in_funcset)
done


lemma (in Tarski) intY1_mono:
     "monotone (%x: intY1. f x) intY1 (induced intY1 r)"
(*sledgehammer *)
apply (auto simp add: monotone_def induced_def intY1_f_closed)
apply (blast intro: intY1_elem monotone_f [THEN monotoneE])
done

(*proof requires relaxing relevance: 2007-01-25*)

lemma (in Tarski) intY1_is_cl:
    "(| pset = intY1, order = induced intY1 r |) \<in> CompleteLattice"
(*sledgehammer*)
apply (unfold intY1_def)
apply (rule interv_is_compl_latt)
apply (rule lubY_in_A)
apply (rule Top_in_lattice)
apply (rule Top_intv_not_empty)
apply (rule lubY_in_A)
done

(*never proved, 2007-01-22*)

lemma (in Tarski) v_in_P: "v \<in> P"
(*sledgehammer*)
apply (unfold P_def)
apply (rule_tac A = "intY1" in fixf_subset)
apply (rule intY1_subset)
apply (simp add: CLF.glbH_is_fixp [OF CLF.intro, OF CL.intro CLF_axioms.intro, OF PO.intro CL_axioms.intro, OF _ intY1_is_cl, simplified]
                 v_def CL_imp_PO intY1_is_cl CLF_set_def intY1_func intY1_mono)
done


lemma (in Tarski) z_in_interval:
     "[| z \<in> P; \<forall>y\<in>Y. (y, z) \<in> induced P r |] ==> z \<in> intY1"
(*sledgehammer *)
apply (unfold intY1_def P_def)
apply (rule intervalI)
prefer 2
 apply (erule fix_subset [THEN subsetD, THEN Top_prop])
apply (rule lub_least)
apply (rule Y_subset_A)
apply (fast elim!: fix_subset [THEN subsetD])
apply (simp add: induced_def)
done


lemma (in Tarski) f'z_in_int_rel: "[| z \<in> P; \<forall>y\<in>Y. (y, z) \<in> induced P r |]
      ==> ((%x: intY1. f x) z, z) \<in> induced intY1 r"
apply (metis P_def acc_def fix_imp_eq fix_subset indI reflE restrict_apply subset_eq z_in_interval)
done

(*never proved, 2007-01-22*)

lemma (in Tarski) tarski_full_lemma:
     "\<exists>L. isLub Y (| pset = P, order = induced P r |) L"
apply (rule_tac x = "v" in exI)
apply (simp add: isLub_def)
-- {* @{text "v \<in> P"} *}
apply (simp add: v_in_P)
apply (rule conjI)
(*sledgehammer*)
-- {* @{text v} is lub *}
-- {* @{text "1. \<forall>y:Y. (y, v) \<in> induced P r"} *}
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
apply (rule CL.glb_in_lattice [OF CL.intro, OF PO.intro CL_axioms.intro, OF _ intY1_is_cl, simplified])
 apply (simp add: CL_imp_PO intY1_is_cl, force)
-- {* @{text v} is LEAST ub *}
apply clarify
apply (rule indI)
  prefer 3 apply assumption
 prefer 2 apply (simp add: v_in_P)
apply (unfold v_def)
(*never proved, 2007-01-22*)
(*sledgehammer*)
apply (rule indE)
apply (rule_tac [2] intY1_subset)
(*never proved, 2007-01-22*)
(*sledgehammer*)
apply (rule CL.glb_lower [OF CL.intro, OF PO.intro CL_axioms.intro, OF _ intY1_is_cl, simplified])
  apply (simp add: CL_imp_PO intY1_is_cl)
 apply force
apply (simp add: induced_def intY1_f_closed z_in_interval)
apply (simp add: P_def fix_imp_eq [of _ f A] reflE
                 fix_subset [of f A, THEN subsetD])
done

lemma CompleteLatticeI_simp:
     "[| (| pset = A, order = r |) \<in> PartialOrder;
         \<forall>S. S \<subseteq> A --> (\<exists>L. isLub S (| pset = A, order = r |)  L) |]
    ==> (| pset = A, order = r |) \<in> CompleteLattice"
by (simp add: CompleteLatticeI Rdual)

(*never proved, 2007-01-22*)

declare (in CLF) fixf_po[intro] P_def [simp] A_def [simp] r_def [simp]
             Tarski.tarski_full_lemma [intro] cl_po [intro] cl_co [intro]
             CompleteLatticeI_simp [intro]

theorem (in CLF) Tarski_full:
     "(| pset = P, order = induced P r|) \<in> CompleteLattice"
(*sledgehammer*)
apply (rule CompleteLatticeI_simp)
apply (rule fixf_po, clarify)
(*never proved, 2007-01-22*)
(*sledgehammer*)
apply (simp add: P_def A_def r_def)
apply (blast intro!: Tarski.tarski_full_lemma [OF Tarski.intro, OF CLF.intro Tarski_axioms.intro,
  OF CL.intro CLF_axioms.intro, OF PO.intro CL_axioms.intro] cl_po cl_co f_cl)
done

declare (in CLF) fixf_po [rule del] P_def [simp del] A_def [simp del] r_def [simp del]
         Tarski.tarski_full_lemma [rule del] cl_po [rule del] cl_co [rule del]
         CompleteLatticeI_simp [rule del]

end
