(*  Title:      Codatatype_Examples/HFset.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Hereditary sets.
*)

header {* Hereditary Sets *}

theory HFset
imports "../Codatatype"
begin


section {* Datatype definition *}

data_raw hfset: 'hfset = "'hfset fset"


section {* Customization of terms *}

subsection{* Constructors *}

definition "Fold hs \<equiv> hfset_fld hs"

lemma hfset_simps[simp]:
"\<And>hs1 hs2. Fold hs1 = Fold hs2 \<longrightarrow> hs1 = hs2"
unfolding Fold_def hfset.fld_inject by auto

theorem hfset_cases[elim, case_names Fold]:
assumes Fold: "\<And> hs. h = Fold hs \<Longrightarrow> phi"
shows phi
using Fold unfolding Fold_def
by (cases rule: hfset.fld_exhaust[of h]) simp

lemma hfset_induct[case_names Fold, induct type: hfset]:
assumes Fold: "\<And> hs. (\<And> h. h |\<in>| hs \<Longrightarrow> phi h) \<Longrightarrow> phi (Fold hs)"
shows "phi t"
apply (induct rule: hfset.fld_induct)
using Fold unfolding Fold_def fset_fset_member mem_Collect_eq ..

(* alternative induction principle, using fset: *)
lemma hfset_induct_fset[case_names Fold, induct type: hfset]:
assumes Fold: "\<And> hs. (\<And> h. h \<in> fset hs \<Longrightarrow> phi h) \<Longrightarrow> phi (Fold hs)"
shows "phi t"
apply (induct rule: hfset_induct)
using Fold by (metis notin_fset)

subsection{* Recursion and iteration *}

lemma hfset_fld_rec:
"hfset_fld_rec R (Fold hs) = R (map_fset <id, hfset_fld_rec R> hs)"
using hfset.fld_rec unfolding Fold_def .

(* The iterator has a simpler form: *)
lemma hfset_fld_iter:
"hfset_fld_iter R (Fold hs) = R (map_fset (hfset_fld_iter R) hs)"
using hfset.fld_iter unfolding Fold_def .

end
