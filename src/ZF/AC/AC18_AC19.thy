(*  Title:      ZF/AC/AC18_AC19.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proof of AC1 ==> AC18 ==> AC19 ==> AC1
*)

theory AC18_AC19 = AC_Equiv:

constdefs
  uu    :: "i => i"
    "uu(a) == {c Un {0}. c \<in> a}"


(* ********************************************************************** *)
(* AC1 ==> AC18                                                           *)
(* ********************************************************************** *)

lemma PROD_subsets:
     "[| f \<in> (\<Pi>b \<in> {P(a). a \<in> A}. b);  \<forall>a \<in> A. P(a)<=Q(a) |]   
      ==> (\<lambda>a \<in> A. f`P(a)) \<in> (\<Pi>a \<in> A. Q(a))"
by (rule lam_type, drule apply_type, auto)

lemma lemma_AC18:
     "[| \<forall>A. 0 \<notin> A --> (\<exists>f. f \<in> (\<Pi>X \<in> A. X)); A \<noteq> 0 |] 
      ==> (\<Inter>a \<in> A. \<Union>b \<in> B(a). X(a, b)) \<subseteq> 
          (\<Union>f \<in> \<Pi>a \<in> A. B(a). \<Inter>a \<in> A. X(a, f`a))"
apply (rule subsetI)
apply (erule_tac x = "{{b \<in> B (a) . x \<in> X (a,b) }. a \<in> A}" in allE)
apply (erule impE, fast)
apply (erule exE)
apply (rule UN_I)
 apply (fast elim!: PROD_subsets)
apply (simp, fast elim!: not_emptyE dest: apply_type [OF _ RepFunI])
done

lemma AC1_AC18: "AC1 ==> AC18"
apply (unfold AC1_def AC18_def)
apply (fast elim!: lemma_AC18 apply_type intro!: equalityI INT_I UN_I)
done

(* ********************************************************************** *)
(* AC18 ==> AC19                                                          *)
(* ********************************************************************** *)

text{*Hard to express because of the need for meta-quantifiers in AC18*}
lemma "AC18 ==> AC19"
proof -
  assume ac18 [unfolded AC18_def, norm_hhf]: AC18
  show AC19
    apply (unfold AC18_def AC19_def)
    apply (intro allI impI) 
    apply (rule ac18 [of _ "%x. x", THEN mp], blast) 
    done
qed

(* ********************************************************************** *)
(* AC19 ==> AC1                                                           *)
(* ********************************************************************** *)

lemma RepRep_conj: 
        "[| A \<noteq> 0; 0 \<notin> A |] ==> {uu(a). a \<in> A} \<noteq> 0 & 0 \<notin> {uu(a). a \<in> A}"
apply (unfold uu_def, auto) 
apply (blast dest!: sym [THEN RepFun_eq_0_iff [THEN iffD1]])
done

lemma lemma1_1: "[|c \<in> a; x = c Un {0}; x \<notin> a |] ==> x - {0} \<in> a"
apply clarify 
apply (rule subst_elem , (assumption))
apply (fast elim: notE subst_elem)
done

lemma lemma1_2: 
        "[| f`(uu(a)) \<notin> a; f \<in> (\<Pi>B \<in> {uu(a). a \<in> A}. B); a \<in> A |]   
                ==> f`(uu(a))-{0} \<in> a"
apply (unfold uu_def, fast elim!: lemma1_1 dest!: apply_type)
done

lemma lemma1: "\<exists>f. f \<in> (\<Pi>B \<in> {uu(a). a \<in> A}. B) ==> \<exists>f. f \<in> (\<Pi>B \<in> A. B)"
apply (erule exE)
apply (rule_tac x = "\<lambda>a\<in>A. if (f` (uu(a)) \<in> a, f` (uu(a)), f` (uu(a))-{0})" 
       in exI)
apply (rule lam_type) 
apply (simp add: lemma1_2)
done

lemma lemma2_1: "a\<noteq>0 ==> 0 \<in> (\<Union>b \<in> uu(a). b)"
by (unfold uu_def, auto)

lemma lemma2: "[| A\<noteq>0; 0\<notin>A |] ==> (\<Inter>x \<in> {uu(a). a \<in> A}. \<Union>b \<in> x. b) \<noteq> 0"
apply (erule not_emptyE) 
apply (rule_tac a = "0" in not_emptyI)
apply (fast intro!: lemma2_1)
done

lemma AC19_AC1: "AC19 ==> AC1"
apply (unfold AC19_def AC1_def, clarify)
apply (case_tac "A=0", force)
apply (erule_tac x = "{uu (a) . a \<in> A}" in allE)
apply (erule impE)
apply (erule RepRep_conj , (assumption))
apply (rule lemma1)
apply (drule lemma2 , (assumption))
apply auto 
done

end
