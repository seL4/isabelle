header {*  Section 10.4 *}

theory Ex1
imports LCF
begin

axiomatization
  P     :: "'a => tr" and
  G     :: "'a => 'a" and
  H     :: "'a => 'a" and
  K     :: "('a => 'a) => ('a => 'a)"
where
  P_strict:     "P(UU) = UU" and
  K:            "K = (%h x. P(x) => x | h(h(G(x))))" and
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

lemma H_idemp_lemma: "ALL x. H(FIX(K,x)) = FIX(K,x)"
  apply (tactic {* induct_tac @{context} "K" 1 *})
  apply simp
  apply (simp split: COND_cases_iff)
  apply (intro strip)
  apply (subst H_unfold)
  apply simp
  done

lemma H_idemp: "ALL x. H(H(x)) = H(x)"
  apply (rule H_idemp_lemma [folded H])
  done

end
