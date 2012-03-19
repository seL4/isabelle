header {* Example 3.8 *}

theory Ex2
imports LCF
begin

axiomatization
  P     :: "'a => tr" and
  F     :: "'b => 'b" and
  G     :: "'a => 'a" and
  H     :: "'a => 'b => 'b" and
  K     :: "('a => 'b => 'b) => ('a => 'b => 'b)"
where
  F_strict:     "F(UU) = UU" and
  K:            "K = (%h x y. P(x) => y | F(h(G(x),y)))" and
  H:            "H = FIX(K)"

declare F_strict [simp] K [simp]

lemma example: "ALL x. F(H(x::'a,y::'b)) = H(x,F(y))"
  apply (simplesubst H)
  apply (tactic {* induct_tac @{context} "K:: ('a=>'b=>'b) => ('a=>'b=>'b)" 1 *})
  apply simp
  apply (simp split: COND_cases_iff)
  done

end
