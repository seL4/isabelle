(*  Title:      HOL/UNITY/Counter
    ID:         $Id$
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

A family of similar counters, version close to the original. 

From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Spriner LNCS 1586 (1999), pages 1215-1227.
*)

theory Counter = UNITY_Main:

(* Variables are names *)
datatype name = C | c nat
types state = "name=>int"

consts  
  sum  :: "[nat,state]=>int"
  sumj :: "[nat, nat, state]=>int"

primrec (* sum I s = sigma_{i<I}. s (c i) *)
  "sum 0 s = 0"
  "sum (Suc i) s = s (c i) + sum i s"

primrec
  "sumj 0 i s = 0"
  "sumj (Suc n) i s = (if n=i then sum n s else s (c n) + sumj n i s)"
  
types command = "(state*state)set"

constdefs
  a :: "nat=>command"
 "a i == {(s, s'). s'=s(c i:= s (c i) + 1, C:= s C + 1)}"

  Component :: "nat => state program"
  "Component i ==
    mk_total_program({s. s C = 0 & s (c i) = 0}, {a i},
	             \<Union>G \<in> preserves (%s. s (c i)). Acts G)"



declare Component_def [THEN def_prg_Init, simp]
declare a_def [THEN def_act_simp, simp]

(* Theorems about sum and sumj *)
lemma sum_upd_gt [rule_format (no_asm)]: "\<forall>n. I<n --> sum I (s(c n := x)) = sum I s"
apply (induct_tac "I")
apply auto
done


lemma sum_upd_eq: "sum I (s(c I := x)) = sum I s"
apply (induct_tac "I")
apply (auto simp add: sum_upd_gt [unfolded fun_upd_def])
done

lemma sum_upd_C: "sum I (s(C := x)) = sum I s"
apply (induct_tac "I")
apply auto
done

lemma sumj_upd_ci: "sumj I i (s(c i := x)) = sumj I i s"
apply (induct_tac "I")
apply (auto simp add: sum_upd_eq [unfolded fun_upd_def])
done

lemma sumj_upd_C: "sumj I i (s(C := x)) = sumj I i s"
apply (induct_tac "I")
apply (auto simp add: sum_upd_C [unfolded fun_upd_def])
done

lemma sumj_sum_gt [rule_format (no_asm)]: "\<forall>i. I<i--> (sumj I i s = sum I s)"
apply (induct_tac "I")
apply auto
done

lemma sumj_sum_eq: "(sumj I I s = sum I s)"
apply (induct_tac "I")
apply auto
apply (simp (no_asm) add: sumj_sum_gt)
done

lemma sum_sumj [rule_format (no_asm)]: "\<forall>i. i<I-->(sum I s = s (c i) +  sumj I i s)"
apply (induct_tac "I")
apply (auto simp add: linorder_neq_iff sumj_sum_eq)
done

(* Correctness proofs for Components *)
(* p2 and p3 proofs *)
lemma p2: "Component i \<in> stable {s. s C = s (c i) + k}"
apply (simp add: Component_def)
apply constrains
done

lemma p3: "Component i \<in> stable {s. \<forall>v. v~=c i & v~=C --> s v = k v}"
apply (simp add: Component_def)
apply constrains
done


lemma p2_p3_lemma1: 
"(\<forall>k. Component i \<in> stable ({s. s C = s (c i) + sumj I i k}  
                   \<inter> {s. \<forall>v. v~=c i & v~=C --> s v = k v}))  
   = (Component i \<in> stable {s. s C = s (c i) + sumj I i s})"
apply (simp add: Component_def mk_total_program_def)
apply (auto simp add: constrains_def stable_def sumj_upd_C sumj_upd_ci)
done

lemma p2_p3_lemma2: 
"\<forall>k. Component i \<in> stable ({s. s C = s (c i) + sumj I i k} Int  
                            {s. \<forall>v. v~=c i & v~=C --> s v = k v})"
by (blast intro: stable_Int [OF p2 p3])

lemma p2_p3: "Component i \<in> stable {s.  s C = s (c i) + sumj I i s}"
apply (auto intro!: p2_p3_lemma2 simp add: p2_p3_lemma1 [symmetric])
done

(* Compositional Proof *)

lemma sum_0' [rule_format]: "(\<forall>i. i < I --> s (c i) = 0) --> sum I s = 0"
apply (induct_tac "I")
apply auto
done

(* I could'nt be empty *)
lemma safety: 
"!!I. 0<I ==> (\<Squnion>i \<in> {i. i<I}. Component i) \<in> invariant {s. s C = sum I s}"
apply (unfold invariant_def)
apply (simp (no_asm) add: JN_stable sum_sumj)
apply (force intro: p2_p3 sum_0')
done

end  
