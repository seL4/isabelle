(*  Title:      HOL/UNITY/Channel
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Unordered Channel

From Misra, "A Logic for Concurrent Programming" (1994), section 13.3
*)

theory Channel = UNITY_Main:

types state = "nat set"

consts
  F :: "state program"

constdefs
  minSet :: "nat set => nat option"
    "minSet A == if A={} then None else Some (LEAST x. x \<in> A)"

axioms

  UC1:  "F \<in> (minSet -` {Some x}) co (minSet -` (Some`atLeast x))"

  (*  UC1  "F \<in> {s. minSet s = x} co {s. x \<subseteq> minSet s}"  *)

  UC2:  "F \<in> (minSet -` {Some x}) leadsTo {s. x \<notin> s}"


(*None represents "infinity" while Some represents proper integers*)
lemma minSet_eq_SomeD: "minSet A = Some x ==> x \<in> A"
apply (unfold minSet_def)
apply (simp split: split_if_asm)
apply (fast intro: LeastI)
done

lemma minSet_empty [simp]: " minSet{} = None"
by (unfold minSet_def, simp)

lemma minSet_nonempty: "x \<in> A ==> minSet A = Some (LEAST x. x \<in> A)"
by (unfold minSet_def, auto)

lemma minSet_greaterThan:
     "F \<in> (minSet -` {Some x}) leadsTo (minSet -` (Some`greaterThan x))"
apply (rule leadsTo_weaken)
apply (rule_tac x1=x in psp [OF UC2 UC1], safe)
apply (auto dest: minSet_eq_SomeD simp add: linorder_neq_iff)
done

(*The induction*)
lemma Channel_progress_lemma:
     "F \<in> (UNIV-{{}}) leadsTo (minSet -` (Some`atLeast y))"
apply (rule leadsTo_weaken_R)
apply (rule_tac l = y and f = "the o minSet" and B = "{}" 
       in greaterThan_bounded_induct, safe)
apply (simp_all (no_asm_simp))
apply (drule_tac [2] minSet_nonempty)
 prefer 2 apply simp 
apply (rule minSet_greaterThan [THEN leadsTo_weaken], safe)
apply simp_all
apply (drule minSet_nonempty, simp)
done


lemma Channel_progress: "!!y::nat. F \<in> (UNIV-{{}}) leadsTo {s. y \<notin> s}"
apply (rule Channel_progress_lemma [THEN leadsTo_weaken_R], clarify)
apply (frule minSet_nonempty)
apply (auto dest: Suc_le_lessD not_less_Least)
done

end
