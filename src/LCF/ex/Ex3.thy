
(* $Id$ *)

header {* Addition with fixpoint of successor *}

theory Ex3
imports LCF
begin

consts
  s     :: "'a => 'a"
  p     :: "'a => 'a => 'a"

axioms
  p_strict:     "p(UU) = UU"
  p_s:          "p(s(x),y) = s(p(x,y))"

declare p_strict [simp] p_s [simp]

lemma example: "p(FIX(s),y) = FIX(s)"
  apply (tactic {* induct_tac "s" 1 *})
  apply (simp (no_asm))
  apply (simp (no_asm))
  done

end
