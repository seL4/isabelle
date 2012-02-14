(*  Title:      ZF/AC/WO6_WO1.thy
    Author:     Krzysztof Grabczewski

Proofs needed to state that formulations WO1,...,WO6 are all equivalent.
The only hard one is WO6 ==> WO1.

Every proof (except WO6 ==> WO1 and WO1 ==> WO2) are described as "clear"
by Rubin & Rubin (page 2). 
They refer reader to a book by Gödel to see the proof WO1 ==> WO2.
Fortunately order types made this proof also very easy.
*)

theory WO6_WO1
imports Cardinal_aux
begin

(* Auxiliary definitions used in proof *)
definition
  NN  :: "i => i"  where
    "NN(y) == {m \<in> nat. \<exists>a. \<exists>f. Ord(a) & domain(f)=a  &  
                        (\<Union>b<a. f`b) = y & (\<forall>b<a. f`b \<lesssim> m)}"
  
definition
  uu  :: "[i, i, i, i] => i"  where
    "uu(f, beta, gamma, delta) == (f`beta * f`gamma) Int f`delta"


(** Definitions for case 1 **)
definition
  vv1 :: "[i, i, i] => i"  where
     "vv1(f,m,b) ==                                                
           let g = LEAST g. (\<exists>d. Ord(d) & (domain(uu(f,b,g,d)) \<noteq> 0 & 
                                 domain(uu(f,b,g,d)) \<lesssim> m));      
               d = LEAST d. domain(uu(f,b,g,d)) \<noteq> 0 &                  
                            domain(uu(f,b,g,d)) \<lesssim> m         
           in  if f`b \<noteq> 0 then domain(uu(f,b,g,d)) else 0"

definition
  ww1 :: "[i, i, i] => i"  where
     "ww1(f,m,b) == f`b - vv1(f,m,b)"

definition
  gg1 :: "[i, i, i] => i"  where
     "gg1(f,a,m) == \<lambda>b \<in> a++a. if b<a then vv1(f,m,b) else ww1(f,m,b--a)"


(** Definitions for case 2 **)
definition
  vv2 :: "[i, i, i, i] => i"  where
     "vv2(f,b,g,s) ==   
           if f`g \<noteq> 0 then {uu(f, b, g, LEAST d. uu(f,b,g,d) \<noteq> 0)`s} else 0"

definition
  ww2 :: "[i, i, i, i] => i"  where
     "ww2(f,b,g,s) == f`g - vv2(f,b,g,s)"

definition
  gg2 :: "[i, i, i, i] => i"  where
     "gg2(f,a,b,s) ==
              \<lambda>g \<in> a++a. if g<a then vv2(f,b,g,s) else ww2(f,b,g--a,s)"


lemma WO2_WO3: "WO2 ==> WO3"
by (unfold WO2_def WO3_def, fast)

(* ********************************************************************** *)

lemma WO3_WO1: "WO3 ==> WO1"
apply (unfold eqpoll_def WO1_def WO3_def)
apply (intro allI)
apply (drule_tac x=A in spec) 
apply (blast intro: bij_is_inj well_ord_rvimage 
                    well_ord_Memrel [THEN well_ord_subset])
done

(* ********************************************************************** *)

lemma WO1_WO2: "WO1 ==> WO2"
apply (unfold eqpoll_def WO1_def WO2_def)
apply (blast intro!: Ord_ordertype ordermap_bij)
done

(* ********************************************************************** *)

lemma lam_sets: "f \<in> A->B ==> (\<lambda>x \<in> A. {f`x}): A -> {{b}. b \<in> B}"
by (fast intro!: lam_type apply_type)

lemma surj_imp_eq': "f \<in> surj(A,B) ==> (\<Union>a \<in> A. {f`a}) = B"
apply (unfold surj_def)
apply (fast elim!: apply_type)
done

lemma surj_imp_eq: "[| f \<in> surj(A,B); Ord(A) |] ==> (\<Union>a<A. {f`a}) = B"
by (fast dest!: surj_imp_eq' intro!: ltI elim!: ltE)

lemma WO1_WO4: "WO1 ==> WO4(1)"
apply (unfold WO1_def WO4_def)
apply (rule allI)
apply (erule_tac x = A in allE)
apply (erule exE)
apply (intro exI conjI)
apply (erule Ord_ordertype)
apply (erule ordermap_bij [THEN bij_converse_bij, THEN bij_is_fun, THEN lam_sets, THEN domain_of_fun])
apply (simp_all add: singleton_eqpoll_1 eqpoll_imp_lepoll Ord_ordertype
       ordermap_bij [THEN bij_converse_bij, THEN bij_is_surj, THEN surj_imp_eq]
       ltD)
done

(* ********************************************************************** *)

lemma WO4_mono: "[| m\<le>n; WO4(m) |] ==> WO4(n)"
apply (unfold WO4_def)
apply (blast dest!: spec intro: lepoll_trans [OF _ le_imp_lepoll])
done

(* ********************************************************************** *)

lemma WO4_WO5: "[| m \<in> nat; 1\<le>m; WO4(m) |] ==> WO5"
by (unfold WO4_def WO5_def, blast)

(* ********************************************************************** *)

lemma WO5_WO6: "WO5 ==> WO6"
by (unfold WO4_def WO5_def WO6_def, blast)


(* ********************************************************************** 
    The proof of "WO6 ==> WO1".  Simplified by L C Paulson.

    From the book "Equivalents of the Axiom of Choice" by Rubin & Rubin,
    pages 2-5
************************************************************************* *)

lemma lt_oadd_odiff_disj:
      "[| k < i++j;  Ord(i);  Ord(j) |] 
       ==> k < i  |  (~ k<i & k = i ++ (k--i) & (k--i)<j)"
apply (rule_tac i = k and j = i in Ord_linear2)
prefer 4 
   apply (drule odiff_lt_mono2, assumption)
   apply (simp add: oadd_odiff_inverse odiff_oadd_inverse)
apply (auto elim!: lt_Ord)
done


(* ********************************************************************** *)
(* The most complicated part of the proof - lemma ii - p. 2-4             *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* some properties of relation uu(beta, gamma, delta) - p. 2              *)
(* ********************************************************************** *)

lemma domain_uu_subset: "domain(uu(f,b,g,d)) \<subseteq> f`b"
by (unfold uu_def, blast)

lemma quant_domain_uu_lepoll_m:
     "\<forall>b<a. f`b \<lesssim> m ==> \<forall>b<a. \<forall>g<a. \<forall>d<a. domain(uu(f,b,g,d)) \<lesssim> m"
by (blast intro: domain_uu_subset [THEN subset_imp_lepoll] lepoll_trans)

lemma uu_subset1: "uu(f,b,g,d) \<subseteq> f`b * f`g"
by (unfold uu_def, blast)

lemma uu_subset2: "uu(f,b,g,d) \<subseteq> f`d"
by (unfold uu_def, blast)

lemma uu_lepoll_m: "[| \<forall>b<a. f`b \<lesssim> m;  d<a |] ==> uu(f,b,g,d) \<lesssim> m"
by (blast intro: uu_subset2 [THEN subset_imp_lepoll] lepoll_trans)

(* ********************************************************************** *)
(* Two cases for lemma ii                                                 *)
(* ********************************************************************** *)
lemma cases: 
     "\<forall>b<a. \<forall>g<a. \<forall>d<a. u(f,b,g,d) \<lesssim> m   
      ==> (\<forall>b<a. f`b \<noteq> 0 -->  
                  (\<exists>g<a. \<exists>d<a. u(f,b,g,d) \<noteq> 0 & u(f,b,g,d) \<prec> m))  
        | (\<exists>b<a. f`b \<noteq> 0 & (\<forall>g<a. \<forall>d<a. u(f,b,g,d) \<noteq> 0 -->   
                                        u(f,b,g,d) \<approx> m))"
apply (unfold lesspoll_def)
apply (blast del: equalityI)
done

(* ********************************************************************** *)
(* Lemmas used in both cases                                              *)
(* ********************************************************************** *)
lemma UN_oadd: "Ord(a) ==> (\<Union>b<a++a. C(b)) = (\<Union>b<a. C(b) Un C(a++b))"
by (blast intro: ltI lt_oadd1 oadd_lt_mono2 dest!: lt_oadd_disj)


(* ********************************************************************** *)
(* Case 1: lemmas                                                        *)
(* ********************************************************************** *)

lemma vv1_subset: "vv1(f,m,b) \<subseteq> f`b"
by (simp add: vv1_def Let_def domain_uu_subset)

(* ********************************************************************** *)
(* Case 1: Union of images is the whole "y"                              *)
(* ********************************************************************** *)
lemma UN_gg1_eq: 
  "[| Ord(a);  m \<in> nat |] ==> (\<Union>b<a++a. gg1(f,a,m)`b) = (\<Union>b<a. f`b)"
by (simp add: gg1_def UN_oadd lt_oadd1 oadd_le_self [THEN le_imp_not_lt] 
              lt_Ord odiff_oadd_inverse ltD vv1_subset [THEN Diff_partition]
              ww1_def)

lemma domain_gg1: "domain(gg1(f,a,m)) = a++a"
by (simp add: lam_funtype [THEN domain_of_fun] gg1_def)

(* ********************************************************************** *)
(* every value of defined function is less than or equipollent to m       *)
(* ********************************************************************** *)
lemma nested_LeastI:
     "[| P(a, b);  Ord(a);  Ord(b);   
         Least_a = (LEAST a. \<exists>x. Ord(x) & P(a, x)) |]   
      ==> P(Least_a, LEAST b. P(Least_a, b))"
apply (erule ssubst)
apply (rule_tac Q = "%z. P (z, LEAST b. P (z, b))" in LeastI2)
apply (fast elim!: LeastI)+
done

lemmas nested_Least_instance =
       nested_LeastI [of "%g d. domain(uu(f,b,g,d)) \<noteq> 0 & 
                                domain(uu(f,b,g,d)) \<lesssim> m"] for f b m

lemma gg1_lepoll_m: 
     "[| Ord(a);  m \<in> nat;   
         \<forall>b<a. f`b \<noteq>0 -->                                        
             (\<exists>g<a. \<exists>d<a. domain(uu(f,b,g,d)) \<noteq> 0  &                
                          domain(uu(f,b,g,d)) \<lesssim> m);             
         \<forall>b<a. f`b \<lesssim> succ(m);  b<a++a |] 
      ==> gg1(f,a,m)`b \<lesssim> m"
apply (simp add: gg1_def empty_lepollI)
apply (safe dest!: lt_oadd_odiff_disj)
(*Case b<a   \<in> show vv1(f,m,b) \<lesssim> m *)
 apply (simp add: vv1_def Let_def empty_lepollI)
 apply (fast intro: nested_Least_instance [THEN conjunct2]
             elim!: lt_Ord)
(*Case a\<le>b \<in> show ww1(f,m,b--a) \<lesssim> m *)
apply (simp add: ww1_def empty_lepollI)
apply (case_tac "f` (b--a) = 0", simp add: empty_lepollI)
apply (rule Diff_lepoll, blast)
apply (rule vv1_subset)
apply (drule ospec [THEN mp], assumption+)
apply (elim oexE conjE)
apply (simp add: vv1_def Let_def lt_Ord nested_Least_instance [THEN conjunct1])
done

(* ********************************************************************** *)
(* Case 2: lemmas                                                        *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(* Case 2: vv2_subset                                                    *)
(* ********************************************************************** *)

lemma ex_d_uu_not_empty:
     "[| b<a;  g<a;  f`b\<noteq>0;  f`g\<noteq>0;         
         y*y \<subseteq> y;  (\<Union>b<a. f`b)=y |] 
      ==> \<exists>d<a. uu(f,b,g,d) \<noteq> 0"
by (unfold uu_def, blast) 

lemma uu_not_empty:
     "[| b<a; g<a; f`b\<noteq>0; f`g\<noteq>0;  y*y \<subseteq> y; (\<Union>b<a. f`b)=y |]   
      ==> uu(f,b,g,LEAST d. (uu(f,b,g,d) \<noteq> 0)) \<noteq> 0"
apply (drule ex_d_uu_not_empty, assumption+)
apply (fast elim!: LeastI lt_Ord)
done

lemma not_empty_rel_imp_domain: "[| r \<subseteq> A*B; r\<noteq>0 |] ==> domain(r)\<noteq>0"
by blast

lemma Least_uu_not_empty_lt_a:
     "[| b<a; g<a; f`b\<noteq>0; f`g\<noteq>0; y*y \<subseteq> y; (\<Union>b<a. f`b)=y |]   
      ==> (LEAST d. uu(f,b,g,d) \<noteq> 0) < a"
apply (erule ex_d_uu_not_empty [THEN oexE], assumption+)
apply (blast intro: Least_le [THEN lt_trans1] lt_Ord)
done

lemma subset_Diff_sing: "[| B \<subseteq> A; a\<notin>B |] ==> B \<subseteq> A-{a}"
by blast

(*Could this be proved more directly?*)
lemma supset_lepoll_imp_eq:
     "[| A \<lesssim> m; m \<lesssim> B; B \<subseteq> A; m \<in> nat |] ==> A=B"
apply (erule natE)
apply (fast dest!: lepoll_0_is_0 intro!: equalityI)
apply (safe intro!: equalityI)
apply (rule ccontr)
apply (rule succ_lepoll_natE)
 apply (erule lepoll_trans)  
 apply (rule lepoll_trans)  
  apply (erule subset_Diff_sing [THEN subset_imp_lepoll], assumption)
 apply (rule Diff_sing_lepoll, assumption+) 
done

lemma uu_Least_is_fun:
     "[| \<forall>g<a. \<forall>d<a. domain(uu(f, b, g, d))\<noteq>0 -->                
          domain(uu(f, b, g, d)) \<approx> succ(m);                         
          \<forall>b<a. f`b \<lesssim> succ(m);  y*y \<subseteq> y;                        
          (\<Union>b<a. f`b)=y;  b<a;  g<a;  d<a;                             
          f`b\<noteq>0;  f`g\<noteq>0;  m \<in> nat;  s \<in> f`b |] 
      ==> uu(f, b, g, LEAST d. uu(f,b,g,d)\<noteq>0) \<in> f`b -> f`g"
apply (drule_tac x2=g in ospec [THEN ospec, THEN mp])
   apply (rule_tac [3] not_empty_rel_imp_domain [OF uu_subset1 uu_not_empty])
        apply (rule_tac [2] Least_uu_not_empty_lt_a, assumption+)
apply (rule rel_is_fun)
    apply (erule eqpoll_sym [THEN eqpoll_imp_lepoll]) 
   apply (erule uu_lepoll_m) 
   apply (rule Least_uu_not_empty_lt_a, assumption+) 
apply (rule uu_subset1)
apply (rule supset_lepoll_imp_eq [OF _ eqpoll_sym [THEN eqpoll_imp_lepoll]])
apply (fast intro!: domain_uu_subset)+
done

lemma vv2_subset: 
     "[| \<forall>g<a. \<forall>d<a. domain(uu(f, b, g, d))\<noteq>0 -->             
                       domain(uu(f, b, g, d)) \<approx> succ(m);
         \<forall>b<a. f`b \<lesssim> succ(m); y*y \<subseteq> y;
         (\<Union>b<a. f`b)=y;  b<a;  g<a;  m \<in> nat;  s \<in> f`b |] 
      ==> vv2(f,b,g,s) \<subseteq> f`g"
apply (simp add: vv2_def)
apply (blast intro: uu_Least_is_fun [THEN apply_type])
done

(* ********************************************************************** *)
(* Case 2: Union of images is the whole "y"                              *)
(* ********************************************************************** *)
lemma UN_gg2_eq: 
     "[| \<forall>g<a. \<forall>d<a. domain(uu(f,b,g,d)) \<noteq> 0 -->              
               domain(uu(f,b,g,d)) \<approx> succ(m);                         
         \<forall>b<a. f`b \<lesssim> succ(m); y*y \<subseteq> y;                        
         (\<Union>b<a. f`b)=y;  Ord(a);  m \<in> nat;  s \<in> f`b;  b<a |] 
      ==> (\<Union>g<a++a. gg2(f,a,b,s) ` g) = y"
apply (unfold gg2_def)
apply (drule sym) 
apply (simp add: ltD UN_oadd  oadd_le_self [THEN le_imp_not_lt] 
                 lt_Ord odiff_oadd_inverse ww2_def 
                 vv2_subset [THEN Diff_partition])
done

lemma domain_gg2: "domain(gg2(f,a,b,s)) = a++a"
by (simp add: lam_funtype [THEN domain_of_fun] gg2_def)


(* ********************************************************************** *)
(* every value of defined function is less than or equipollent to m       *)
(* ********************************************************************** *)

lemma vv2_lepoll: "[| m \<in> nat; m\<noteq>0 |] ==> vv2(f,b,g,s) \<lesssim> m"
apply (unfold vv2_def)
apply (simp add: empty_lepollI)
apply (fast dest!: le_imp_subset [THEN subset_imp_lepoll, THEN lepoll_0_is_0] 
       intro!: singleton_eqpoll_1 [THEN eqpoll_imp_lepoll, THEN lepoll_trans]
               not_lt_imp_le [THEN le_imp_subset, THEN subset_imp_lepoll]
               nat_into_Ord nat_1I)
done

lemma ww2_lepoll: 
    "[| \<forall>b<a. f`b \<lesssim> succ(m);  g<a;  m \<in> nat;  vv2(f,b,g,d) \<subseteq> f`g |]  
     ==> ww2(f,b,g,d) \<lesssim> m"
apply (unfold ww2_def)
apply (case_tac "f`g = 0")
apply (simp add: empty_lepollI)
apply (drule ospec, assumption)
apply (rule Diff_lepoll, assumption+)
apply (simp add: vv2_def not_emptyI)
done

lemma gg2_lepoll_m: 
     "[| \<forall>g<a. \<forall>d<a. domain(uu(f,b,g,d)) \<noteq> 0 -->              
                      domain(uu(f,b,g,d)) \<approx> succ(m);                         
         \<forall>b<a. f`b \<lesssim> succ(m);  y*y \<subseteq> y;                     
         (\<Union>b<a. f`b)=y;  b<a;  s \<in> f`b;  m \<in> nat;  m\<noteq> 0;  g<a++a |] 
      ==> gg2(f,a,b,s) ` g \<lesssim> m"
apply (simp add: gg2_def empty_lepollI)
apply (safe elim!: lt_Ord2 dest!: lt_oadd_odiff_disj)
 apply (simp add: vv2_lepoll)
apply (simp add: ww2_lepoll vv2_subset)
done

(* ********************************************************************** *)
(* lemma ii                                                               *)
(* ********************************************************************** *)
lemma lemma_ii: "[| succ(m) \<in> NN(y); y*y \<subseteq> y; m \<in> nat; m\<noteq>0 |] ==> m \<in> NN(y)"
apply (unfold NN_def)
apply (elim CollectE exE conjE) 
apply (rule quant_domain_uu_lepoll_m [THEN cases, THEN disjE], assumption)
(* case 1 *)
apply (simp add: lesspoll_succ_iff)
apply (rule_tac x = "a++a" in exI)
apply (fast intro!: Ord_oadd domain_gg1 UN_gg1_eq gg1_lepoll_m)
(* case 2 *)
apply (elim oexE conjE)
apply (rule_tac A = "f`?B" in not_emptyE, assumption)
apply (rule CollectI)
apply (erule succ_natD)
apply (rule_tac x = "a++a" in exI)
apply (rule_tac x = "gg2 (f,a,b,x) " in exI)
apply (simp add: Ord_oadd domain_gg2 UN_gg2_eq gg2_lepoll_m)
done


(* ********************************************************************** *)
(* lemma iv - p. 4:                                                       *)
(* For every set x there is a set y such that   x Un (y * y) \<subseteq> y         *)
(* ********************************************************************** *)


(* The leading \<forall>-quantifier looks odd but makes the proofs shorter 
   (used only in the following two lemmas)                          *)

lemma z_n_subset_z_succ_n:
     "\<forall>n \<in> nat. rec(n, x, %k r. r Un r*r) \<subseteq> rec(succ(n), x, %k r. r Un r*r)"
by (fast intro: rec_succ [THEN ssubst])

lemma le_subsets:
     "[| \<forall>n \<in> nat. f(n)<=f(succ(n)); n\<le>m; n \<in> nat; m \<in> nat |]   
      ==> f(n)<=f(m)"
apply (erule_tac P = "n\<le>m" in rev_mp)
apply (rule_tac P = "%z. n\<le>z --> f (n) \<subseteq> f (z) " in nat_induct) 
apply (auto simp add: le_iff) 
done

lemma le_imp_rec_subset:
     "[| n\<le>m; m \<in> nat |] 
      ==> rec(n, x, %k r. r Un r*r) \<subseteq> rec(m, x, %k r. r Un r*r)"
apply (rule z_n_subset_z_succ_n [THEN le_subsets])
apply (blast intro: lt_nat_in_nat)+
done

lemma lemma_iv: "\<exists>y. x Un y*y \<subseteq> y"
apply (rule_tac x = "\<Union>n \<in> nat. rec (n, x, %k r. r Un r*r) " in exI)
apply safe
apply (rule nat_0I [THEN UN_I], simp)
apply (rule_tac a = "succ (n Un na) " in UN_I)
apply (erule Un_nat_type [THEN nat_succI], assumption)
apply (auto intro: le_imp_rec_subset [THEN subsetD] 
            intro!: Un_upper1_le Un_upper2_le Un_nat_type 
            elim!: nat_into_Ord)
done

(* ********************************************************************** *)
(* Rubin & Rubin wrote,                                                   *)
(* "It follows from (ii) and mathematical induction that if y*y \<subseteq> y then *)
(* y can be well-ordered"                                                 *)

(* In fact we have to prove                                               *)
(*      * WO6 ==> NN(y) \<noteq> 0                                              *)
(*      * reverse induction which lets us infer that 1 \<in> NN(y)            *)
(*      * 1 \<in> NN(y) ==> y can be well-ordered                             *)
(* ********************************************************************** *)

(* ********************************************************************** *)
(*      WO6 ==> NN(y) \<noteq> 0                                                *)
(* ********************************************************************** *)

lemma WO6_imp_NN_not_empty: "WO6 ==> NN(y) \<noteq> 0"
by (unfold WO6_def NN_def, clarify, blast)

(* ********************************************************************** *)
(*      1 \<in> NN(y) ==> y can be well-ordered                               *)
(* ********************************************************************** *)

lemma lemma1:
     "[| (\<Union>b<a. f`b)=y; x \<in> y; \<forall>b<a. f`b \<lesssim> 1; Ord(a) |] ==> \<exists>c<a. f`c = {x}"
by (fast elim!: lepoll_1_is_sing)

lemma lemma2:
     "[| (\<Union>b<a. f`b)=y; x \<in> y; \<forall>b<a. f`b \<lesssim> 1; Ord(a) |]   
      ==> f` (LEAST i. f`i = {x}) = {x}"
apply (drule lemma1, assumption+)
apply (fast elim!: lt_Ord intro: LeastI)
done

lemma NN_imp_ex_inj: "1 \<in> NN(y) ==> \<exists>a f. Ord(a) & f \<in> inj(y, a)"
apply (unfold NN_def)
apply (elim CollectE exE conjE)
apply (rule_tac x = a in exI)
apply (rule_tac x = "\<lambda>x \<in> y. LEAST i. f`i = {x}" in exI)
apply (rule conjI, assumption)
apply (rule_tac d = "%i. THE x. x \<in> f`i" in lam_injective)
apply (drule lemma1, assumption+)
apply (fast elim!: Least_le [THEN lt_trans1, THEN ltD] lt_Ord)
apply (rule lemma2 [THEN ssubst], assumption+, blast)
done

lemma y_well_ord: "[| y*y \<subseteq> y; 1 \<in> NN(y) |] ==> \<exists>r. well_ord(y, r)"
apply (drule NN_imp_ex_inj)
apply (fast elim!: well_ord_rvimage [OF _ well_ord_Memrel])
done

(* ********************************************************************** *)
(*      reverse induction which lets us infer that 1 \<in> NN(y)              *)
(* ********************************************************************** *)

lemma rev_induct_lemma [rule_format]: 
     "[| n \<in> nat; !!m. [| m \<in> nat; m\<noteq>0; P(succ(m)) |] ==> P(m) |]   
      ==> n\<noteq>0 --> P(n) --> P(1)"
by (erule nat_induct, blast+)

lemma rev_induct:
     "[| n \<in> nat;  P(n);  n\<noteq>0;   
         !!m. [| m \<in> nat; m\<noteq>0; P(succ(m)) |] ==> P(m) |]   
      ==> P(1)"
by (rule rev_induct_lemma, blast+)

lemma NN_into_nat: "n \<in> NN(y) ==> n \<in> nat"
by (simp add: NN_def)

lemma lemma3: "[| n \<in> NN(y); y*y \<subseteq> y; n\<noteq>0 |] ==> 1 \<in> NN(y)"
apply (rule rev_induct [OF NN_into_nat], assumption+)
apply (rule lemma_ii, assumption+)
done

(* ********************************************************************** *)
(* Main theorem "WO6 ==> WO1"                                             *)
(* ********************************************************************** *)

(* another helpful lemma *)
lemma NN_y_0: "0 \<in> NN(y) ==> y=0"
apply (unfold NN_def) 
apply (fast intro!: equalityI dest!: lepoll_0_is_0 elim: subst)
done

lemma WO6_imp_WO1: "WO6 ==> WO1"
apply (unfold WO1_def)
apply (rule allI)
apply (case_tac "A=0")
apply (fast intro!: well_ord_Memrel nat_0I [THEN nat_into_Ord])
apply (rule_tac x = A in lemma_iv [elim_format])
apply (erule exE)
apply (drule WO6_imp_NN_not_empty)
apply (erule Un_subset_iff [THEN iffD1, THEN conjE])
apply (erule_tac A = "NN (y) " in not_emptyE)
apply (frule y_well_ord)
 apply (fast intro!: lemma3 dest!: NN_y_0 elim!: not_emptyE)
apply (fast elim: well_ord_subset)
done

end
