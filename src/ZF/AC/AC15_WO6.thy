(*  Title:      ZF/AC/AC15_WO6.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proofs needed to state that AC10, ..., AC15 are equivalent to the rest.
We need the following:

WO1 ==> AC10(n) ==> AC11 ==> AC12 ==> AC15 ==> WO6

In order to add the formulations AC13 and AC14 we need:

AC10(succ(n)) ==> AC13(n) ==> AC14 ==> AC15

or

AC1 ==> AC13(1);  AC13(m) ==> AC13(n) ==> AC14 ==> AC15    (m\<le>n)

So we don't have to prove all implications of both cases.
Moreover we don't need to prove AC13(1) ==> AC1 and AC11 ==> AC14 as
Rubin & Rubin do.
*)

theory AC15_WO6 = HH + Cardinal_aux:


(* ********************************************************************** *)
(* Lemmas used in the proofs in which the conclusion is AC13, AC14        *)
(* or AC15                                                                *)
(*  - cons_times_nat_not_Finite                                           *)
(*  - ex_fun_AC13_AC15                                                    *)
(* ********************************************************************** *)

lemma lepoll_Sigma: "A\<noteq>0 ==> B \<lesssim> A*B"
apply (unfold lepoll_def)
apply (erule not_emptyE)
apply (rule_tac x = "\<lambda>z \<in> B. <x,z>" in exI)
apply (fast intro!: snd_conv lam_injective)
done

lemma cons_times_nat_not_Finite:
     "0\<notin>A ==> \<forall>B \<in> {cons(0,x*nat). x \<in> A}. ~Finite(B)"
apply clarify 
apply (rule nat_not_Finite [THEN notE] )
apply (subgoal_tac "x ~= 0")
 apply (blast intro: lepoll_Sigma [THEN lepoll_Finite])+
done

lemma lemma1: "[| Union(C)=A; a \<in> A |] ==> \<exists>B \<in> C. a \<in> B & B \<subseteq> A"
by fast

lemma lemma2: 
        "[| pairwise_disjoint(A); B \<in> A; C \<in> A; a \<in> B; a \<in> C |] ==> B=C"
by (unfold pairwise_disjoint_def, blast) 

lemma lemma3: 
     "\<forall>B \<in> {cons(0, x*nat). x \<in> A}. pairwise_disjoint(f`B) &   
	     sets_of_size_between(f`B, 2, n) & Union(f`B)=B   
     ==> \<forall>B \<in> A. \<exists>! u. u \<in> f`cons(0, B*nat) & u \<subseteq> cons(0, B*nat) &   
	     0 \<in> u & 2 \<lesssim> u & u \<lesssim> n"
apply (unfold sets_of_size_between_def)
apply (rule ballI)
apply (erule_tac x="cons(0, B*nat)" in ballE)
 apply (blast dest: lemma1 intro!: lemma2, blast)
done

lemma lemma4: "[| A \<lesssim> i; Ord(i) |] ==> {P(a). a \<in> A} \<lesssim> i"
apply (unfold lepoll_def)
apply (erule exE)
apply (rule_tac x = "\<lambda>x \<in> RepFun(A,P). LEAST j. \<exists>a\<in>A. x=P(a) & f`a=j" 
       in exI)
apply (rule_tac d = "%y. P (converse (f) `y) " in lam_injective)
apply (erule RepFunE)
apply (frule inj_is_fun [THEN apply_type], assumption)
apply (fast intro: LeastI2 elim!: Ord_in_Ord inj_is_fun [THEN apply_type])
apply (erule RepFunE)
apply (rule LeastI2)
  apply fast
 apply (fast elim!: Ord_in_Ord inj_is_fun [THEN apply_type])
apply (fast elim: sym left_inverse [THEN ssubst])
done

lemma lemma5_1:
     "[| B \<in> A; 2 \<lesssim> u(B) |] ==> (\<lambda>x \<in> A. {fst(x). x \<in> u(x)-{0}})`B \<noteq> 0"
apply simp
apply (fast dest: lepoll_Diff_sing 
            elim: lepoll_trans [THEN succ_lepoll_natE] ssubst
            intro!: lepoll_refl)
done

lemma lemma5_2:
     "[|  B \<in> A; u(B) \<subseteq> cons(0, B*nat) |]   
      ==> (\<lambda>x \<in> A. {fst(x). x \<in> u(x)-{0}})`B \<subseteq> B"
apply auto 
done

lemma lemma5_3:
     "[| n \<in> nat; B \<in> A; 0 \<in> u(B); u(B) \<lesssim> succ(n) |]   
      ==> (\<lambda>x \<in> A. {fst(x). x \<in> u(x)-{0}})`B \<lesssim> n"
apply simp
apply (fast elim!: Diff_lepoll [THEN lemma4 [OF _ nat_into_Ord]])
done

lemma ex_fun_AC13_AC15:
     "[| \<forall>B \<in> {cons(0, x*nat). x \<in> A}.   
                pairwise_disjoint(f`B) &   
                sets_of_size_between(f`B, 2, succ(n)) & Union(f`B)=B; 
         n \<in> nat |]   
      ==> \<exists>f. \<forall>B \<in> A. f`B \<noteq> 0 & f`B \<subseteq> B & f`B \<lesssim> n"
by (fast del: subsetI notI
	 dest!: lemma3 theI intro!: lemma5_1 lemma5_2 lemma5_3)


(* ********************************************************************** *)
(* The target proofs                                                      *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC10(n) ==> AC11                                                       *)
(* ********************************************************************** *)

theorem AC10_AC11: "[| n \<in> nat; 1\<le>n; AC10(n) |] ==> AC11"
by (unfold AC10_def AC11_def, blast)

(* ********************************************************************** *)
(* AC11 ==> AC12                                                          *)
(* ********************************************************************** *)

theorem AC11_AC12: "AC11 ==> AC12"
by (unfold AC10_def AC11_def AC11_def AC12_def, blast)

(* ********************************************************************** *)
(* AC12 ==> AC15                                                          *)
(* ********************************************************************** *)

theorem AC12_AC15: "AC12 ==> AC15"
apply (unfold AC12_def AC15_def)
apply (blast del: ballI 
             intro!: cons_times_nat_not_Finite ex_fun_AC13_AC15)
done

(* ********************************************************************** *)
(* AC15 ==> WO6                                                           *)
(* ********************************************************************** *)

lemma OUN_eq_UN: "Ord(x) ==> (\<Union>a<x. F(a)) = (\<Union>a \<in> x. F(a))"
by (fast intro!: ltI dest!: ltD)

lemma AC15_WO6_aux1:
     "\<forall>x \<in> Pow(A)-{0}. f`x\<noteq>0 & f`x \<subseteq> x & f`x \<lesssim> m 
      ==> (\<Union>i<LEAST x. HH(f,A,x)={A}. HH(f,A,i)) = A"
apply (simp add: Ord_Least [THEN OUN_eq_UN])
apply (rule equalityI)
apply (fast dest!: less_Least_subset_x)
apply (blast del: subsetI 
           intro!: f_subsets_imp_UN_HH_eq_x [THEN Diff_eq_0_iff [THEN iffD1]])
done

lemma AC15_WO6_aux2:
     "\<forall>x \<in> Pow(A)-{0}. f`x\<noteq>0 & f`x \<subseteq> x & f`x \<lesssim> m 
      ==> \<forall>x < (LEAST x. HH(f,A,x)={A}). HH(f,A,x) \<lesssim> m"
apply (rule oallI)
apply (drule ltD [THEN less_Least_subset_x])
apply (frule HH_subset_imp_eq)
apply (erule ssubst)
apply (blast dest!: HH_subset_x_imp_subset_Diff_UN [THEN not_emptyI2])
	(*but can't use del: DiffE despite the obvious conflict*)
done

theorem AC15_WO6: "AC15 ==> WO6"
apply (unfold AC15_def WO6_def)
apply (rule allI)
apply (erule_tac x = "Pow (A) -{0}" in allE)
apply (erule impE, fast)
apply (elim bexE conjE exE)
apply (rule bexI)
 apply (rule conjI, assumption)
 apply (rule_tac x = "LEAST i. HH (f,A,i) ={A}" in exI)
 apply (rule_tac x = "\<lambda>j \<in> (LEAST i. HH (f,A,i) ={A}) . HH (f,A,j) " in exI)
 apply (simp_all add: ltD)
apply (fast intro!: Ord_Least lam_type [THEN domain_of_fun]
            elim!: less_Least_subset_x AC15_WO6_aux1 AC15_WO6_aux2) 
done


(* ********************************************************************** *)
(* The proof needed in the first case, not in the second                  *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC10(n) ==> AC13(n-1)  if 2\<le>n                                       *)
(*                                                                        *)
(* Because of the change to the formal definition of AC10(n) we prove     *)
(* the following obviously equivalent theorem \<in>                           *)
(* AC10(n) implies AC13(n) for (1\<le>n)                                   *)
(* ********************************************************************** *)

theorem AC10_AC13: "[| n \<in> nat; 1\<le>n; AC10(n) |] ==> AC13(n)"
apply (unfold AC10_def AC13_def, safe)
apply (erule allE) 
apply (erule impE [OF _ cons_times_nat_not_Finite], assumption) 
apply (fast elim!: impE [OF _ cons_times_nat_not_Finite] 
            dest!: ex_fun_AC13_AC15)
done

(* ********************************************************************** *)
(* The proofs needed in the second case, not in the first                 *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC1 ==> AC13(1)                                                        *)
(* ********************************************************************** *)

lemma AC1_AC13: "AC1 ==> AC13(1)"
apply (unfold AC1_def AC13_def)
apply (rule allI)
apply (erule allE)
apply (rule impI)
apply (drule mp, assumption) 
apply (elim exE)
apply (rule_tac x = "\<lambda>x \<in> A. {f`x}" in exI)
apply (simp add: singleton_eqpoll_1 [THEN eqpoll_imp_lepoll])
done

(* ********************************************************************** *)
(* AC13(m) ==> AC13(n) for m \<subseteq> n                                         *)
(* ********************************************************************** *)

lemma AC13_mono: "[| m\<le>n; AC13(m) |] ==> AC13(n)"
apply (unfold AC13_def)
apply (drule le_imp_lepoll)
apply (fast elim!: lepoll_trans)
done

(* ********************************************************************** *)
(* The proofs necessary for both cases                                    *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC13(n) ==> AC14  if 1 \<subseteq> n                                            *)
(* ********************************************************************** *)

theorem AC13_AC14: "[| n \<in> nat; 1\<le>n; AC13(n) |] ==> AC14"
by (unfold AC13_def AC14_def, auto)

(* ********************************************************************** *)
(* AC14 ==> AC15                                                          *)
(* ********************************************************************** *)

theorem AC14_AC15: "AC14 ==> AC15"
by (unfold AC13_def AC14_def AC15_def, fast)

(* ********************************************************************** *)
(* The redundant proofs; however cited by Rubin & Rubin                   *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* AC13(1) ==> AC1                                                        *)
(* ********************************************************************** *)

lemma lemma_aux: "[| A\<noteq>0; A \<lesssim> 1 |] ==> \<exists>a. A={a}"
by (fast elim!: not_emptyE lepoll_1_is_sing)

lemma AC13_AC1_lemma:
     "\<forall>B \<in> A. f(B)\<noteq>0 & f(B)<=B & f(B) \<lesssim> 1   
      ==> (\<lambda>x \<in> A. THE y. f(x)={y}) \<in> (\<Pi>X \<in> A. X)"
apply (rule lam_type)
apply (drule bspec, assumption)
apply (elim conjE)
apply (erule lemma_aux [THEN exE], assumption)
apply (simp add: the_equality)
done

theorem AC13_AC1: "AC13(1) ==> AC1"
apply (unfold AC13_def AC1_def)
apply (fast elim!: AC13_AC1_lemma)
done

(* ********************************************************************** *)
(* AC11 ==> AC14                                                          *)
(* ********************************************************************** *)

theorem AC11_AC14: "AC11 ==> AC14"
apply (unfold AC11_def AC14_def)
apply (fast intro!: AC10_AC13)
done

end

