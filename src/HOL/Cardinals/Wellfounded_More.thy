(*  Title:      HOL/Cardinals/Wellfounded_More.thy
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

More on well-founded relations.
*)

header {* More on Well-Founded Relations *}

theory Wellfounded_More
imports Wellfounded_More_Base Order_Relation_More
begin


subsection {* Well-founded recursion via genuine fixpoints *}

(*2*)lemma adm_wf_unique_fixpoint:
fixes r :: "('a * 'a) set" and
      H :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" and
      f :: "'a \<Rightarrow> 'b" and g :: "'a \<Rightarrow> 'b"
assumes WF: "wf r" and ADM: "adm_wf r H" and fFP: "f = H f" and gFP: "g = H g"
shows "f = g"
proof-
  {fix x
   have "f x = g x"
   proof(rule wf_induct[of r "(\<lambda>x. f x = g x)"],
         auto simp add: WF)
     fix x assume "\<forall>y. (y, x) \<in> r \<longrightarrow> f y = g y"
     hence "H f x = H g x" using ADM adm_wf_def[of r H] by auto
     thus "f x = g x" using fFP and gFP by simp
   qed
  }
  thus ?thesis by (simp add: ext)
qed

(*2*)lemma wfrec_unique_fixpoint:
fixes r :: "('a * 'a) set" and
      H :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" and
      f :: "'a \<Rightarrow> 'b"
assumes WF: "wf r" and ADM: "adm_wf r H" and
        fp: "f = H f"
shows "f = wfrec r H"
proof-
  have "H (wfrec r H) = wfrec r H"
  using assms wfrec_fixpoint[of r H] by simp
  thus ?thesis
  using assms adm_wf_unique_fixpoint[of r H "wfrec r H"] by simp
qed

end
