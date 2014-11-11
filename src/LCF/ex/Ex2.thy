section {* Example 3.8 *}

theory Ex2
imports "../LCF"
begin

axiomatization
  P     :: "'a \<Rightarrow> tr" and
  F     :: "'b \<Rightarrow> 'b" and
  G     :: "'a \<Rightarrow> 'a" and
  H     :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" and
  K     :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'b)"
where
  F_strict:     "F(UU) = UU" and
  K:            "K = (\<lambda>h x y. P(x) \<Rightarrow> y | F(h(G(x),y)))" and
  H:            "H = FIX(K)"

declare F_strict [simp] K [simp]

lemma example: "\<forall>x. F(H(x::'a,y::'b)) = H(x,F(y))"
  apply (simplesubst H)
  apply (induct "K:: ('a\<Rightarrow>'b\<Rightarrow>'b) \<Rightarrow> ('a\<Rightarrow>'b\<Rightarrow>'b)")
  apply simp
  apply (simp split: COND_cases_iff)
  done

end
