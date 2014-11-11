section {*  Section 10.4 *}

theory Ex1
imports "../LCF"
begin

axiomatization
  P     :: "'a \<Rightarrow> tr" and
  G     :: "'a \<Rightarrow> 'a" and
  H     :: "'a \<Rightarrow> 'a" and
  K     :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
where
  P_strict:     "P(UU) = UU" and
  K:            "K = (\<lambda>h x. P(x) \<Rightarrow> x | h(h(G(x))))" and
  H:            "H = FIX(K)"


declare P_strict [simp] K [simp]

lemma H_unfold: "H = K(H)"
  apply (simplesubst H)
  apply (rule FIX_eq [symmetric])
  done

lemma H_strict [simp]: "H(UU)=UU"
  apply (simplesubst H_unfold)
  apply simp
  done

lemma H_idemp_lemma: "\<forall>x. H(FIX(K,x)) = FIX(K,x)"
  apply (induct K)
  apply simp
  apply (simp split: COND_cases_iff)
  apply (intro strip)
  apply (subst H_unfold)
  apply simp
  done

lemma H_idemp: "\<forall>x. H(H(x)) = H(x)"
  apply (rule H_idemp_lemma [folded H])
  done

end
