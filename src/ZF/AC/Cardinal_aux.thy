(*  Title:      ZF/AC/Cardinal_aux.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Auxiliary lemmas concerning cardinalities
*)

theory Cardinal_aux = AC_Equiv:

lemma Diff_lepoll: "[| A \<lesssim> succ(m); B \<subseteq> A; B\<noteq>0 |] ==> A-B \<lesssim> m"
apply (rule not_emptyE, (assumption))
apply (blast intro: lepoll_trans [OF subset_imp_lepoll Diff_sing_lepoll])
done


(* ********************************************************************** *)
(* Lemmas involving ordinals and cardinalities used in the proofs         *)
(* concerning AC16 and DC                                                 *)
(* ********************************************************************** *)


(* j=|A| *)
lemma lepoll_imp_ex_le_eqpoll:
     "[| A \<lesssim> i; Ord(i) |] ==> \<exists>j. j le i & A \<approx> j"
by (blast intro!: lepoll_cardinal_le well_ord_Memrel 
                  well_ord_cardinal_eqpoll [THEN eqpoll_sym]
          dest: lepoll_well_ord);

(* j=|A| *)
lemma lesspoll_imp_ex_lt_eqpoll: 
     "[| A \<prec> i; Ord(i) |] ==> \<exists>j. j<i & A \<approx> j"
by (unfold lesspoll_def, blast dest!: lepoll_imp_ex_le_eqpoll elim!: leE)

lemma Inf_Ord_imp_InfCard_cardinal: "[| ~Finite(i); Ord(i) |] ==> InfCard(|i|)"
apply (unfold InfCard_def)
apply (rule conjI)
apply (rule Card_cardinal)
apply (rule Card_nat 
            [THEN Card_def [THEN def_imp_iff, THEN iffD1, THEN ssubst]])
  -- "rewriting would loop!"
apply (rule well_ord_Memrel [THEN well_ord_lepoll_imp_Card_le], assumption) 
apply (rule nat_le_infinite_Ord [THEN le_imp_lepoll], assumption+)
done

text{*An alternative and more general proof goes like this: A and B are both
well-ordered (because they are injected into an ordinal), either A lepoll B
or B lepoll A.  Also both are equipollent to their cardinalities, so
(if A and B are infinite) then A Un B lepoll |A|+|B| = max(|A|,|B|) lepoll i.
In fact, the correctly strengthened version of this theorem appears below.*}
lemma Un_lepoll_Inf_Ord_weak:
     "[|A \<approx> i; B \<approx> i; \<not> Finite(i); Ord(i)|] ==> A \<union> B \<lesssim> i"
apply (rule Un_lepoll_sum [THEN lepoll_trans])
apply (rule lepoll_imp_sum_lepoll_prod [THEN lepoll_trans])
apply (erule eqpoll_trans [THEN eqpoll_imp_lepoll]) 
apply (erule eqpoll_sym) 
apply (rule subset_imp_lepoll [THEN lepoll_trans, THEN lepoll_trans]) 
apply (rule nat_2I [THEN OrdmemD], rule Ord_nat) 
apply (rule nat_le_infinite_Ord [THEN le_imp_lepoll], assumption+) 
apply (erule eqpoll_sym [THEN eqpoll_imp_lepoll]) 
apply (erule prod_eqpoll_cong [THEN eqpoll_imp_lepoll, THEN lepoll_trans],
       assumption)
apply (rule eqpoll_imp_lepoll) 
apply (rule well_ord_Memrel [THEN well_ord_InfCard_square_eq], assumption) 
apply (rule Inf_Ord_imp_InfCard_cardinal, assumption+) 
done

lemma Un_eqpoll_Inf_Ord:
     "[| A \<approx> i; B \<approx> i; ~Finite(i); Ord(i) |] ==> A Un B \<approx> i"
apply (rule eqpollI)
apply (blast intro: Un_lepoll_Inf_Ord_weak) 
apply (erule eqpoll_sym [THEN eqpoll_imp_lepoll, THEN lepoll_trans]) 
apply (rule Un_upper1 [THEN subset_imp_lepoll]) 
done

lemma paired_bij: "?f \<in> bij({{y,z}. y \<in> x}, x)"
apply (rule RepFun_bijective)
apply (simp add: doubleton_eq_iff, blast)
done

lemma paired_eqpoll: "{{y,z}. y \<in> x} \<approx> x"
by (unfold eqpoll_def, fast intro!: paired_bij)

lemma ex_eqpoll_disjoint: "\<exists>B. B \<approx> A & B Int C = 0"
by (fast intro!: paired_eqpoll equals0I elim: mem_asym)

(*Finally we reach this result.  Surely there's a simpler proof, as sketched
  above?*)
lemma Un_lepoll_Inf_Ord:
     "[| A \<lesssim> i; B \<lesssim> i; ~Finite(i); Ord(i) |] ==> A Un B \<lesssim> i"
apply (rule_tac A1 = "i" and C1 = "i" in ex_eqpoll_disjoint [THEN exE])
apply (erule conjE)
apply (drule lepoll_trans) 
apply (erule eqpoll_sym [THEN eqpoll_imp_lepoll])
apply (rule Un_lepoll_Un [THEN lepoll_trans], (assumption+))
apply (blast intro: eqpoll_refl Un_eqpoll_Inf_Ord eqpoll_imp_lepoll) 
done

lemma Least_in_Ord: "[| P(i); i \<in> j; Ord(j) |] ==> (LEAST i. P(i)) \<in> j"
apply (erule Least_le [THEN leE])
apply (erule Ord_in_Ord, assumption)
apply (erule ltE)
apply (fast dest: OrdmemD)
apply (erule subst_elem, assumption)
done

lemma Diff_first_lepoll:
     "[| well_ord(x,r); y \<subseteq> x; y \<lesssim> succ(n); n \<in> nat |] 
      ==> y - {THE b. first(b,y,r)} \<lesssim> n"
apply (case_tac "y=0", simp add: empty_lepollI) 
apply (fast intro!: Diff_sing_lepoll the_first_in)
done

lemma UN_subset_split:
     "(\<Union>x \<in> X. P(x)) \<subseteq> (\<Union>x \<in> X. P(x)-Q(x)) Un (\<Union>x \<in> X. Q(x))"
by blast

lemma UN_sing_lepoll: "Ord(a) ==> (\<Union>x \<in> a. {P(x)}) \<lesssim> a"
apply (unfold lepoll_def)
apply (rule_tac x = "\<lambda>z \<in> (\<Union>x \<in> a. {P (x) }) . (LEAST i. P (i) =z) " in exI)
apply (rule_tac d = "%z. P (z) " in lam_injective)
apply (fast intro!: Least_in_Ord)
apply (fast intro: LeastI elim!: Ord_in_Ord)
done

lemma UN_fun_lepoll_lemma [rule_format]:
     "[| well_ord(T, R); ~Finite(a); Ord(a); n \<in> nat |] 
      ==> \<forall>f. (\<forall>b \<in> a. f`b \<lesssim> n & f`b \<subseteq> T) --> (\<Union>b \<in> a. f`b) \<lesssim> a"
apply (induct_tac "n")
apply (rule allI)
apply (rule impI)
apply (rule_tac b = "\<Union>b \<in> a. f`b" in subst)
apply (rule_tac [2] empty_lepollI)
apply (rule equals0I [symmetric], clarify) 
apply (fast dest: lepoll_0_is_0 [THEN subst])
apply (rule allI)
apply (rule impI)
apply (erule_tac x = "\<lambda>x \<in> a. f`x - {THE b. first (b,f`x,R) }" in allE)
apply (erule impE, simp)
apply (fast intro!: Diff_first_lepoll, simp)
apply (rule UN_subset_split [THEN subset_imp_lepoll, THEN lepoll_trans])
apply (fast intro: Un_lepoll_Inf_Ord UN_sing_lepoll) 
done

lemma UN_fun_lepoll:
     "[| \<forall>b \<in> a. f`b \<lesssim> n & f`b \<subseteq> T; well_ord(T, R);   
         ~Finite(a); Ord(a); n \<in> nat |] ==> (\<Union>b \<in> a. f`b) \<lesssim> a"
by (blast intro: UN_fun_lepoll_lemma); 

lemma UN_lepoll:
     "[| \<forall>b \<in> a. F(b) \<lesssim> n & F(b) \<subseteq> T; well_ord(T, R);   
         ~Finite(a); Ord(a); n \<in> nat |] 
      ==> (\<Union>b \<in> a. F(b)) \<lesssim> a"
apply (rule rev_mp) 
apply (rule_tac f="\<lambda>b \<in> a. F (b)" in UN_fun_lepoll);
apply auto
done

lemma UN_eq_UN_Diffs:
     "Ord(a) ==> (\<Union>b \<in> a. F(b)) = (\<Union>b \<in> a. F(b) - (\<Union>c \<in> b. F(c)))"
apply (rule equalityI)
 prefer 2 apply fast
apply (rule subsetI)
apply (erule UN_E)
apply (rule UN_I)
 apply (rule_tac P = "%z. x \<in> F (z) " in Least_in_Ord, (assumption+))
apply (rule DiffI, best intro: Ord_in_Ord LeastI, clarify)
apply (erule_tac P = "%z. x \<in> F (z) " and i = "c" in less_LeastE)
apply (blast intro: Ord_Least ltI)
done

lemma lepoll_imp_eqpoll_subset: 
     "a \<lesssim> X ==> \<exists>Y. Y \<subseteq> X & a \<approx> Y"
apply (unfold lepoll_def eqpoll_def, clarify) 
apply (blast intro: restrict_bij
             dest: inj_is_fun [THEN fun_is_rel, THEN image_subset]) 
done

(* ********************************************************************** *)
(* Diff_lesspoll_eqpoll_Card                                              *)
(* ********************************************************************** *)

lemma Diff_lesspoll_eqpoll_Card_lemma:
     "[| A\<approx>a; ~Finite(a); Card(a); B \<prec> a; A-B \<prec> a |] ==> P"
apply (elim lesspoll_imp_ex_lt_eqpoll [THEN exE] Card_is_Ord conjE)
apply (frule_tac j=xa in Un_upper1_le [OF lt_Ord lt_Ord], assumption)
apply (frule_tac j=xa in Un_upper2_le [OF lt_Ord lt_Ord], assumption)
apply (drule Un_least_lt, assumption)
apply (drule eqpoll_imp_lepoll [THEN lepoll_trans], 
       rule le_imp_lepoll, assumption)+
apply (case_tac "Finite(x Un xa)");
txt{*finite case*}
 apply (drule Finite_Un [OF lepoll_Finite lepoll_Finite], assumption+) 
 apply (drule subset_Un_Diff [THEN subset_imp_lepoll, THEN lepoll_Finite])
 apply (fast dest: eqpoll_sym [THEN eqpoll_imp_lepoll, THEN lepoll_Finite])
txt{*infinite case*}
apply (drule Un_lepoll_Inf_Ord, (assumption+))
apply (blast intro: le_Ord2) 
apply (drule lesspoll_trans1 
             [OF subset_Un_Diff [THEN subset_imp_lepoll, THEN lepoll_trans] 
                 lt_Card_imp_lesspoll], assumption+)
apply (simp add: lesspoll_def) 
done

lemma Diff_lesspoll_eqpoll_Card:
     "[| A \<approx> a; ~Finite(a); Card(a); B \<prec> a |] ==> A - B \<approx> a"
apply (rule ccontr)
apply (rule Diff_lesspoll_eqpoll_Card_lemma, (assumption+))
apply (blast intro: lesspoll_def [THEN def_imp_iff, THEN iffD2] 
                    subset_imp_lepoll eqpoll_imp_lepoll lepoll_trans)
done

end
