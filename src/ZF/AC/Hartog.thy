(*  Title:      ZF/AC/Hartog.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Hartog's function.
*)

theory Hartog = AC_Equiv:

constdefs
  Hartog :: "i => i"
   "Hartog(X) == LEAST i. ~ i \<lesssim> X"

lemma Ords_in_set: "\<forall>a. Ord(a) --> a \<in> X ==> P"
apply (rule_tac X1 = "{y \<in> X. Ord (y) }" in ON_class [THEN revcut_rl])
apply fast
done

lemma Ord_lepoll_imp_ex_well_ord:
     "[| Ord(a); a \<lesssim> X |] 
      ==> \<exists>Y. Y \<subseteq> X & (\<exists>R. well_ord(Y,R) & ordertype(Y,R)=a)"
apply (unfold lepoll_def)
apply (erule exE)
apply (intro exI conjI)
  apply (erule inj_is_fun [THEN fun_is_rel, THEN image_subset])
 apply (rule well_ord_rvimage [OF bij_is_inj well_ord_Memrel]) 
  apply (erule restrict_bij [THEN bij_converse_bij]) 
apply (rule subset_refl, assumption) 
apply (rule trans) 
apply (rule bij_ordertype_vimage) 
apply (erule restrict_bij [THEN bij_converse_bij]) 
apply (rule subset_refl) 
apply (erule well_ord_Memrel) 
apply (erule ordertype_Memrel) 
done

lemma Ord_lepoll_imp_eq_ordertype:
     "[| Ord(a); a \<lesssim> X |] ==> \<exists>Y. Y \<subseteq> X & (\<exists>R. R \<subseteq> X*X & ordertype(Y,R)=a)"
apply (drule Ord_lepoll_imp_ex_well_ord, assumption, clarify)
apply (intro exI conjI)
apply (erule_tac [3] ordertype_Int, auto) 
done

lemma Ords_lepoll_set_lemma:
     "(\<forall>a. Ord(a) --> a \<lesssim> X) ==>   
       \<forall>a. Ord(a) -->   
        a \<in> {b. Z \<in> Pow(X)*Pow(X*X), \<exists>Y R. Z=<Y,R> & ordertype(Y,R)=b}"
apply (intro allI impI)
apply (elim allE impE, assumption)
apply (blast dest!: Ord_lepoll_imp_eq_ordertype intro: sym) 
done

lemma Ords_lepoll_set: "\<forall>a. Ord(a) --> a \<lesssim> X ==> P"
by (erule Ords_lepoll_set_lemma [THEN Ords_in_set])

lemma ex_Ord_not_lepoll: "\<exists>a. Ord(a) & ~a \<lesssim> X"
apply (rule ccontr)
apply (best intro: Ords_lepoll_set) 
done

lemma not_Hartog_lepoll_self: "~ Hartog(A) \<lesssim> A"
apply (unfold Hartog_def)
apply (rule ex_Ord_not_lepoll [THEN exE])
apply (rule LeastI, auto) 
done

lemmas Hartog_lepoll_selfE = not_Hartog_lepoll_self [THEN notE, standard]

lemma Ord_Hartog: "Ord(Hartog(A))"
by (unfold Hartog_def, rule Ord_Least)

lemma less_HartogE1: "[| i < Hartog(A); ~ i \<lesssim> A |] ==> P"
by (unfold Hartog_def, fast elim: less_LeastE)

lemma less_HartogE: "[| i < Hartog(A); i \<approx> Hartog(A) |] ==> P"
by (blast intro: less_HartogE1 eqpoll_sym eqpoll_imp_lepoll 
                 lepoll_trans [THEN Hartog_lepoll_selfE])

lemma Card_Hartog: "Card(Hartog(A))"
by (fast intro!: CardI Ord_Hartog elim: less_HartogE)

end
