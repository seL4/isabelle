(*  Title:      HOL/UNITY/Comp/Counter.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2001  University of Cambridge

From Charpentier and Chandy,
Examples of Program Composition Illustrating the Use of Universal Properties
   In J. Rolim (editor), Parallel and Distributed Processing,
   Springer LNCS 1586 (1999), pages 1215-1227.
*)

header{*A Family of Similar Counters: Original Version*}

theory Counter imports "../UNITY_Main" begin

(* Variables are names *)
datatype name = C | c nat
type_synonym state = "name=>int"

primrec sum  :: "[nat,state]=>int" where
  (* sum I s = sigma_{i<I}. s (c i) *)
  "sum 0 s = 0"
| "sum (Suc i) s = s (c i) + sum i s"

primrec sumj :: "[nat, nat, state]=>int" where
  "sumj 0 i s = 0"
| "sumj (Suc n) i s = (if n=i then sum n s else s (c n) + sumj n i s)"
  
type_synonym command = "(state*state)set"

definition a :: "nat=>command" where
 "a i = {(s, s'). s'=s(c i:= s (c i) + 1, C:= s C + 1)}"

definition Component :: "nat => state program" where
  "Component i =
    mk_total_program({s. s C = 0 & s (c i) = 0}, {a i},
                     \<Union>G \<in> preserves (%s. s (c i)). Acts G)"



declare Component_def [THEN def_prg_Init, simp]
declare a_def [THEN def_act_simp, simp]

(* Theorems about sum and sumj *)
lemma sum_upd_gt: "I<n ==> sum I (s(c n := x)) = sum I s"
  by (induct I) auto


lemma sum_upd_eq: "sum I (s(c I := x)) = sum I s"
  by (induct I) (auto simp add: sum_upd_gt [unfolded fun_upd_def])

lemma sum_upd_C: "sum I (s(C := x)) = sum I s"
  by (induct I) auto

lemma sumj_upd_ci: "sumj I i (s(c i := x)) = sumj I i s"
  by (induct I) (auto simp add: sum_upd_eq [unfolded fun_upd_def])

lemma sumj_upd_C: "sumj I i (s(C := x)) = sumj I i s"
  by (induct I) (auto simp add: sum_upd_C [unfolded fun_upd_def])

lemma sumj_sum_gt: "I<i ==> sumj I i s = sum I s"
  by (induct I) auto

lemma sumj_sum_eq: "(sumj I I s = sum I s)"
  by (induct I) (auto simp add: sumj_sum_gt)

lemma sum_sumj: "i<I ==> sum I s = s (c i) +  sumj I i s"
  by (induct I) (auto simp add: linorder_neq_iff sumj_sum_eq)

(* Correctness proofs for Components *)
(* p2 and p3 proofs *)
lemma p2: "Component i \<in> stable {s. s C = s (c i) + k}"
by (simp add: Component_def, safety)

lemma p3: "Component i \<in> stable {s. \<forall>v. v\<noteq>c i & v\<noteq>C --> s v = k v}"
by (simp add: Component_def, safety)


lemma p2_p3_lemma1: 
"(\<forall>k. Component i \<in> stable ({s. s C = s (c i) + sumj I i k}  
                   \<inter> {s. \<forall>v. v\<noteq>c i & v\<noteq>C --> s v = k v}))  
   = (Component i \<in> stable {s. s C = s (c i) + sumj I i s})"
apply (simp add: Component_def mk_total_program_def)
apply (auto simp add: constrains_def stable_def sumj_upd_C sumj_upd_ci)
done

lemma p2_p3_lemma2: 
"\<forall>k. Component i \<in> stable ({s. s C = s (c i) + sumj I i k} Int  
                            {s. \<forall>v. v\<noteq>c i & v\<noteq>C --> s v = k v})"
by (blast intro: stable_Int [OF p2 p3])

lemma p2_p3: "Component i \<in> stable {s.  s C = s (c i) + sumj I i s}"
by (auto intro!: p2_p3_lemma2 simp add: p2_p3_lemma1 [symmetric])

(* Compositional Proof *)

lemma sum_0': "(\<And>i. i < I ==> s (c i) = 0) ==> sum I s = 0"
  by (induct I) auto

(* I cannot be empty *)
lemma safety:
     "0<I ==> (\<Squnion>i \<in> {i. i<I}. Component i) \<in> invariant {s. s C = sum I s}"
apply (simp (no_asm) add: invariant_def JN_stable sum_sumj)
apply (force intro: p2_p3 sum_0')
done

end  
