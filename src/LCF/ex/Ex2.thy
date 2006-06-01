
(* $Id$ *)

header {* Example 3.8 *}

theory Ex2
imports LCF
begin

consts
  P     :: "'a => tr"
  F     :: "'a => 'a"
  G     :: "'a => 'a"
  H     :: "'a => 'b => 'b"
  K     :: "('a => 'b => 'b) => ('a => 'b => 'b)"

axioms
  F_strict:     "F(UU) = UU"
  K:            "K = (%h x y. P(x) => y | F(h(G(x),y)))"
  H:            "H = FIX(K)"

declare F_strict [simp] K [simp]

lemma example: "ALL x. F(H(x::'a,y::'b)) = H(x,F(y))"
  apply (simplesubst H)
  apply (tactic {* induct_tac "K:: ('a=>'b=>'b) => ('a=>'b=>'b)" 1 *})
  apply (simp (no_asm))
  apply (simp (no_asm_simp) split: COND_cases_iff)
  done

end
