(*  Title:      ZF/AC/WO1_AC.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proofs of WO1 ==> AC1 and WO1 ==> AC10(n) for n >= 1

The latter proof is referred to as clear by the Rubins.
However it seems to be quite complicated.
The formal proof presented below is a mechanisation of the proof 
by Lawrence C. Paulson which is the following:

Assume WO1.  Let s be a set of infinite sets.
 
Suppose x \<in> s.  Then x is equipollent to |x| (by WO1), an infinite cardinal
call it K.  Since K = K |+| K = |K+K| (by InfCard_cdouble_eq) there is an 
isomorphism h \<in> bij(K+K, x).  (Here + means disjoint sum.)
 
So there is a partition of x into 2-element sets, namely
 
        {{h(Inl(i)), h(Inr(i))} . i \<in> K}
 
So for all x \<in> s the desired partition exists.  By AC1 (which follows from WO1) 
there exists a function f that chooses a partition for each x \<in> s.  Therefore we 
have AC10(2).

*)

theory WO1_AC = AC_Equiv:

(* ********************************************************************** *)
(* WO1 ==> AC1                                                            *)
(* ********************************************************************** *)

theorem WO1_AC1: "WO1 ==> AC1"
by (unfold AC1_def WO1_def, fast elim!: ex_choice_fun)

(* ********************************************************************** *)
(* WO1 ==> AC10(n) (n >= 1)                                               *)
(* ********************************************************************** *)

lemma lemma1: "[| WO1; \<forall>B \<in> A. \<exists>C \<in> D(B). P(C,B) |] ==> \<exists>f. \<forall>B \<in> A. P(f`B,B)"
apply (unfold WO1_def)
apply (erule_tac x = "Union ({{C \<in> D (B) . P (C,B) }. B \<in> A}) " in allE)
apply (erule exE, drule ex_choice_fun, fast)
apply (erule exE)
apply (rule_tac x = "\<lambda>x \<in> A. f`{C \<in> D (x) . P (C,x) }" in exI)
apply (simp, blast dest!: apply_type [OF _ RepFunI])
done

lemma lemma2_1: "[| ~Finite(B); WO1 |] ==> |B| + |B| \<approx>  B"
apply (unfold WO1_def)
apply (rule eqpoll_trans)
prefer 2 apply (fast elim!: well_ord_cardinal_eqpoll)
apply (rule eqpoll_sym [THEN eqpoll_trans])
apply (fast elim!: well_ord_cardinal_eqpoll)
apply (drule spec [of _ B]) 
apply (clarify dest!: eqpoll_imp_Finite_iff [OF well_ord_cardinal_eqpoll]) 
apply (simp add: cadd_def [symmetric] 
            eqpoll_refl InfCard_cdouble_eq Card_cardinal Inf_Card_is_InfCard) 
done

lemma lemma2_2:
     "f \<in> bij(D+D, B) ==> {{f`Inl(i), f`Inr(i)}. i \<in> D} \<in> Pow(Pow(B))"
by (fast elim!: bij_is_fun [THEN apply_type])


lemma lemma2_3: 
        "f \<in> bij(D+D, B) ==> pairwise_disjoint({{f`Inl(i), f`Inr(i)}. i \<in> D})"
apply (unfold pairwise_disjoint_def)
apply (blast dest: bij_is_inj [THEN inj_apply_equality])
done

lemma lemma2_4:
     "[| f \<in> bij(D+D, B); 1\<le>n |] 
      ==> sets_of_size_between({{f`Inl(i), f`Inr(i)}. i \<in> D}, 2, succ(n))"
apply (simp (no_asm_simp) add: sets_of_size_between_def succ_def)
apply (blast intro!: cons_lepoll_cong 
            intro: singleton_eqpoll_1 [THEN eqpoll_imp_lepoll]  
                   le_imp_subset [THEN subset_imp_lepoll]  lepoll_trans 
            dest: bij_is_inj [THEN inj_apply_equality] elim!: mem_irrefl)
done

lemma lemma2_5: 
     "f \<in> bij(D+D, B) ==> Union({{f`Inl(i), f`Inr(i)}. i \<in> D})=B"
apply (unfold bij_def surj_def)
apply (fast elim!: inj_is_fun [THEN apply_type])
done

lemma lemma2:
     "[| WO1; ~Finite(B); 1\<le>n  |]   
      ==> \<exists>C \<in> Pow(Pow(B)). pairwise_disjoint(C) &   
                sets_of_size_between(C, 2, succ(n)) &   
                Union(C)=B"
apply (drule lemma2_1 [THEN eqpoll_def [THEN def_imp_iff, THEN iffD1]], 
       assumption)
apply (blast intro!: lemma2_2 lemma2_3 lemma2_4 lemma2_5)
done

theorem WO1_AC10: "[| WO1; 1\<le>n |] ==> AC10(n)"
apply (unfold AC10_def)
apply (fast intro!: lemma1 elim!: lemma2)
done

end

