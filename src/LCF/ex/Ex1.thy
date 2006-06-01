
(* $Id$ *)

header {*  Section 10.4 *}

theory Ex1
imports LCF
begin

consts
  P     :: "'a => tr"
  G     :: "'a => 'a"
  H     :: "'a => 'a"
  K     :: "('a => 'a) => ('a => 'a)"

axioms
  P_strict:     "P(UU) = UU"
  K:            "K = (%h x. P(x) => x | h(h(G(x))))"
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
  apply (tactic {* induct_tac "K" 1 *})
  apply (simp (no_asm))
  apply (simp (no_asm) split: COND_cases_iff)
  apply (intro strip)
  apply (subst H_unfold)
  apply (simp (no_asm_simp))
  done

lemma H_idemp: "ALL x. H(H(x)) = H(x)"
  apply (rule H_idemp_lemma [folded H])
  done

end
