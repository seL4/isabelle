(*  Title:      HOL/UNITY/Token
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The Token Ring.

From Misra, "A Logic for Concurrent Programming" (1994), sections 5.2 and 13.2.
*)


theory Token = WFair:

(*process states*)
datatype pstate = Hungry | Eating | Thinking

record state =
  token :: "nat"
  proc  :: "nat => pstate"


constdefs
  HasTok :: "nat => state set"
    "HasTok i == {s. token s = i}"

  H :: "nat => state set"
    "H i == {s. proc s i = Hungry}"

  E :: "nat => state set"
    "E i == {s. proc s i = Eating}"

  T :: "nat => state set"
    "T i == {s. proc s i = Thinking}"


locale Token =
  fixes N and F and nodeOrder and "next"   
  defines nodeOrder_def:
       "nodeOrder j == (inv_image less_than (%i. ((j+N)-i) mod N))  Int
	 	       (lessThan N <*> lessThan N)"
      and next_def:
       "next i == (Suc i) mod N"
  assumes N_positive [iff]: "0<N"
      and TR2:  "F \<in> (T i) co (T i \<union> H i)"
      and TR3:  "F \<in> (H i) co (H i \<union> E i)"
      and TR4:  "F \<in> (H i - HasTok i) co (H i)"
      and TR5:  "F \<in> (HasTok i) co (HasTok i \<union> -(E i))"
      and TR6:  "F \<in> (H i \<inter> HasTok i) leadsTo (E i)"
      and TR7:  "F \<in> (HasTok i) leadsTo (HasTok (next i))"


lemma HasToK_partition: "[| s \<in> HasTok i; s \<in> HasTok j |] ==> i=j"
by (unfold HasTok_def, auto)

lemma not_E_eq: "(s \<notin> E i) = (s \<in> H i | s \<in> T i)"
apply (simp add: H_def E_def T_def)
apply (case_tac "proc s i", auto)
done

lemma (in Token) token_stable: "F \<in> stable (-(E i) \<union> (HasTok i))"
apply (unfold stable_def)
apply (rule constrains_weaken)
apply (rule constrains_Un [OF constrains_Un [OF TR2 TR4] TR5])
apply (auto simp add: not_E_eq)
apply (simp_all add: H_def E_def T_def)
done


(*** Progress under weak fairness ***)

lemma (in Token) wf_nodeOrder: "wf(nodeOrder j)"
apply (unfold nodeOrder_def)
apply (rule wf_less_than [THEN wf_inv_image, THEN wf_subset], blast)
done

lemma (in Token) nodeOrder_eq: 
     "[| i<N; j<N |] ==> ((next i, i) \<in> nodeOrder j) = (i \<noteq> j)"
apply (unfold nodeOrder_def next_def inv_image_def)
apply (auto simp add: mod_Suc mod_geq)
apply (auto split add: nat_diff_split simp add: linorder_neq_iff mod_geq)
done

(*From "A Logic for Concurrent Programming", but not used in Chapter 4.
  Note the use of case_tac.  Reasoning about leadsTo takes practice!*)
lemma (in Token) TR7_nodeOrder:
     "[| i<N; j<N |] ==>    
      F \<in> (HasTok i) leadsTo ({s. (token s, i) \<in> nodeOrder j} \<union> HasTok j)"
apply (case_tac "i=j")
apply (blast intro: subset_imp_leadsTo)
apply (rule TR7 [THEN leadsTo_weaken_R])
apply (auto simp add: HasTok_def nodeOrder_eq)
done


(*Chapter 4 variant, the one actually used below.*)
lemma (in Token) TR7_aux: "[| i<N; j<N; i\<noteq>j |]     
      ==> F \<in> (HasTok i) leadsTo {s. (token s, i) \<in> nodeOrder j}"
apply (rule TR7 [THEN leadsTo_weaken_R])
apply (auto simp add: HasTok_def nodeOrder_eq)
done

lemma (in Token) token_lemma:
     "({s. token s < N} \<inter> token -` {m}) = (if m<N then token -` {m} else {})"
by auto


(*Misra's TR9: the token reaches an arbitrary node*)
lemma  (in Token) leadsTo_j: "j<N ==> F \<in> {s. token s < N} leadsTo (HasTok j)"
apply (rule leadsTo_weaken_R)
apply (rule_tac I = "-{j}" and f = token and B = "{}" 
       in wf_nodeOrder [THEN bounded_induct])
apply (simp_all (no_asm_simp) add: token_lemma vimage_Diff HasTok_def)
 prefer 2 apply blast
apply clarify
apply (rule TR7_aux [THEN leadsTo_weaken])
apply (auto simp add: HasTok_def nodeOrder_def)
done

(*Misra's TR8: a hungry process eventually eats*)
lemma (in Token) token_progress:
     "j<N ==> F \<in> ({s. token s < N} \<inter> H j) leadsTo (E j)"
apply (rule leadsTo_cancel1 [THEN leadsTo_Un_duplicate])
apply (rule_tac [2] TR6)
apply (rule psp [OF leadsTo_j TR3, THEN leadsTo_weaken], blast+)
done


end
