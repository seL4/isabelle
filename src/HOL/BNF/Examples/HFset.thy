(*  Title:      HOL/BNF/Examples/HFset.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Hereditary sets.
*)

header {* Hereditary Sets *}

theory HFset
imports "../BNF"
begin


section {* Datatype definition *}

data_raw hfset: 'hfset = "'hfset fset"


section {* Customization of terms *}

subsection{* Constructors *}

definition "Fold hs \<equiv> hfset_ctor hs"

lemma hfset_simps[simp]:
"\<And>hs1 hs2. Fold hs1 = Fold hs2 \<longrightarrow> hs1 = hs2"
unfolding Fold_def hfset.ctor_inject by auto

theorem hfset_cases[elim, case_names Fold]:
assumes Fold: "\<And> hs. h = Fold hs \<Longrightarrow> phi"
shows phi
using Fold unfolding Fold_def
by (cases rule: hfset.ctor_exhaust[of h]) simp

lemma hfset_induct[case_names Fold, induct type: hfset]:
assumes Fold: "\<And> hs. (\<And> h. h |\<in>| hs \<Longrightarrow> phi h) \<Longrightarrow> phi (Fold hs)"
shows "phi t"
apply (induct rule: hfset.ctor_induct)
using Fold unfolding Fold_def fset_fset_member mem_Collect_eq ..

(* alternative induction principle, using fset: *)
lemma hfset_induct_fset[case_names Fold, induct type: hfset]:
assumes Fold: "\<And> hs. (\<And> h. h \<in> fset hs \<Longrightarrow> phi h) \<Longrightarrow> phi (Fold hs)"
shows "phi t"
apply (induct rule: hfset_induct)
using Fold by (metis notin_fset)

subsection{* Recursion and iteration (fold) *}

lemma hfset_ctor_rec:
"hfset_ctor_rec R (Fold hs) = R (map_fset <id, hfset_ctor_rec R> hs)"
using hfset.ctor_rec unfolding Fold_def .

(* The iterator has a simpler form: *)
lemma hfset_ctor_fold:
"hfset_ctor_fold R (Fold hs) = R (map_fset (hfset_ctor_fold R) hs)"
using hfset.ctor_fold unfolding Fold_def .

end
