header {* Addition with fixpoint of successor *}

theory Ex3
imports LCF
begin

axiomatization
  s     :: "'a => 'a" and
  p     :: "'a => 'a => 'a"
where
  p_strict:     "p(UU) = UU" and
  p_s:          "p(s(x),y) = s(p(x,y))"

declare p_strict [simp] p_s [simp]

lemma example: "p(FIX(s),y) = FIX(s)"
  apply (tactic {* induct_tac @{context} "s" 1 *})
  apply simp
  apply simp
  done

end
