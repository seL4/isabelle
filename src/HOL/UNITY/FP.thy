(*  Title:      HOL/UNITY/FP
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

From Misra, "A Logic for Concurrent Programming", 1994
*)

header{*Fixed Point of a Program*}

theory FP = UNITY:

constdefs

  FP_Orig :: "'a program => 'a set"
    "FP_Orig F == Union{A. ALL B. F : stable (A Int B)}"

  FP :: "'a program => 'a set"
    "FP F == {s. F : stable {s}}"

lemma stable_FP_Orig_Int: "F : stable (FP_Orig F Int B)"
apply (unfold FP_Orig_def stable_def)
apply (subst Int_Union2)
apply (blast intro: constrains_UN)
done

lemma FP_Orig_weakest:
    "(!!B. F : stable (A Int B)) ==> A <= FP_Orig F"
by (unfold FP_Orig_def stable_def, blast)

lemma stable_FP_Int: "F : stable (FP F Int B)"
apply (subgoal_tac "FP F Int B = (UN x:B. FP F Int {x}) ")
prefer 2 apply blast
apply (simp (no_asm_simp) add: Int_insert_right)
apply (unfold FP_def stable_def)
apply (rule constrains_UN)
apply (simp (no_asm))
done

lemma FP_equivalence: "FP F = FP_Orig F"
apply (rule equalityI) 
 apply (rule stable_FP_Int [THEN FP_Orig_weakest])
apply (unfold FP_Orig_def FP_def, clarify)
apply (drule_tac x = "{x}" in spec)
apply (simp add: Int_insert_right)
done

lemma FP_weakest:
    "(!!B. F : stable (A Int B)) ==> A <= FP F"
by (simp add: FP_equivalence FP_Orig_weakest)

lemma Compl_FP: 
    "-(FP F) = (UN act: Acts F. -{s. act``{s} <= {s}})"
by (simp add: FP_def stable_def constrains_def, blast)

lemma Diff_FP: "A - (FP F) = (UN act: Acts F. A - {s. act``{s} <= {s}})"
by (simp add: Diff_eq Compl_FP)

end
