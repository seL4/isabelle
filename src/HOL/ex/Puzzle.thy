(*  Title:      HOL/ex/Puzzle.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1993 TU Muenchen

A question from "Bundeswettbewerb Mathematik"

Proof due to Herbert Ehler
*)

theory Puzzle = Main:

consts f :: "nat => nat"

specification (f)
  f_ax [intro!]: "f(f(n)) < f(Suc(n))"
    by (rule exI [of _ id], simp)


lemma lemma0 [rule_format]: "\<forall>n. k=f(n) --> n <= f(n)"
apply (induct_tac "k" rule: nat_less_induct)
apply (rule allI)
apply (rename_tac "i")
apply (case_tac "i")
 apply simp
apply (blast intro!: Suc_leI intro: le_less_trans)
done

lemma lemma1: "n <= f(n)"
by (blast intro: lemma0)

lemma lemma2: "f(n) < f(Suc(n))"
by (blast intro: le_less_trans lemma1)

lemma f_mono [rule_format (no_asm)]: "m <= n --> f(m) <= f(n)"
apply (induct_tac "n")
 apply simp
apply (rule impI)
apply (erule le_SucE)
 apply (cut_tac n = n in lemma2, auto) 
done

lemma f_id: "f(n) = n"
apply (rule order_antisym)
apply (rule_tac [2] lemma1) 
apply (blast intro: leI dest: leD f_mono Suc_leI)
done

end

