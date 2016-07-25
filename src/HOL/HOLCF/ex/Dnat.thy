(*  Title:      HOL/HOLCF/ex/Dnat.thy
    Author:     Franz Regensburger

Theory for the domain of natural numbers  dnat = one ++ dnat
*)

theory Dnat
imports HOLCF
begin

domain dnat = dzero | dsucc (dpred :: dnat)

definition
  iterator :: "dnat \<rightarrow> ('a \<rightarrow> 'a) \<rightarrow> 'a \<rightarrow> 'a" where
  "iterator = fix\<cdot>(LAM h n f x.
    case n of dzero \<Rightarrow> x
      | dsucc\<cdot>m \<Rightarrow> f\<cdot>(h\<cdot>m\<cdot>f\<cdot>x))"

text \<open>
  \medskip Expand fixed point properties.
\<close>

lemma iterator_def2:
  "iterator = (LAM n f x. case n of dzero \<Rightarrow> x | dsucc\<cdot>m \<Rightarrow> f\<cdot>(iterator\<cdot>m\<cdot>f\<cdot>x))"
  apply (rule trans)
  apply (rule fix_eq2)
  apply (rule iterator_def [THEN eq_reflection])
  apply (rule beta_cfun)
  apply simp
  done

text \<open>\medskip Recursive properties.\<close>

lemma iterator1: "iterator\<cdot>UU\<cdot>f\<cdot>x = UU"
  apply (subst iterator_def2)
  apply simp
  done

lemma iterator2: "iterator\<cdot>dzero\<cdot>f\<cdot>x = x"
  apply (subst iterator_def2)
  apply simp
  done

lemma iterator3: "n \<noteq> UU \<Longrightarrow> iterator\<cdot>(dsucc\<cdot>n)\<cdot>f\<cdot>x = f\<cdot>(iterator\<cdot>n\<cdot>f\<cdot>x)"
  apply (rule trans)
   apply (subst iterator_def2)
   apply simp
  apply (rule refl)
  done

lemmas iterator_rews = iterator1 iterator2 iterator3

lemma dnat_flat: "\<forall>x y::dnat. x \<sqsubseteq> y \<longrightarrow> x = UU \<or> x = y"
  apply (rule allI)
  apply (induct_tac x)
    apply fast
   apply (rule allI)
   apply (case_tac y)
     apply simp
    apply simp
   apply simp
  apply (rule allI)
  apply (case_tac y)
    apply (fast intro!: bottomI)
   apply (thin_tac "\<forall>y. dnat \<sqsubseteq> y \<longrightarrow> dnat = UU \<or> dnat = y")
   apply simp
  apply (simp (no_asm_simp))
  apply (drule_tac x="dnata" in spec)
  apply simp
  done

end
