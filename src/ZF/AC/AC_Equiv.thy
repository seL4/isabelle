(*  Title:      ZF/AC/AC_Equiv.thy
    ID:         $Id$
    Author:     Krzysztof Grabczewski

Axioms AC1 -- AC19 come from "Equivalents of the Axiom of Choice, II"
by H. Rubin and J.E. Rubin, 1985.

Axiom AC0 comes from "Axiomatic Set Theory" by P. Suppes, 1972.

Some Isabelle proofs of equivalences of these axioms are formalizations of
proofs presented by the Rubins.  The others are based on the Rubins' proofs,
but slightly changed.
*)

theory AC_Equiv = Main: (*obviously not Main_ZFC*)

constdefs
  
(* Well Ordering Theorems *)
  WO1 :: o
    "WO1 == \<forall>A. \<exists>R. well_ord(A,R)"

  WO2 :: o
    "WO2 == \<forall>A. \<exists>a. Ord(a) & A\<approx>a"

  WO3 :: o
    "WO3 == \<forall>A. \<exists>a. Ord(a) & (\<exists>b. b \<subseteq> a & A\<approx>b)"

  WO4 :: "i => o"
    "WO4(m) == \<forall>A. \<exists>a f. Ord(a) & domain(f)=a &   
		         (\<Union>b<a. f`b) = A & (\<forall>b<a. f`b \<lesssim> m)"

  WO5 :: o
    "WO5 == \<exists>m \<in> nat. 1\<le>m & WO4(m)"

  WO6 :: o
    "WO6 == \<forall>A. \<exists>m \<in> nat. 1\<le>m & (\<exists>a f. Ord(a) & domain(f)=a
		               & (\<Union>b<a. f`b) = A & (\<forall>b<a. f`b \<lesssim> m))"

  WO7 :: o
    "WO7 == \<forall>A. Finite(A) <-> (\<forall>R. well_ord(A,R) --> well_ord(A,converse(R)))"

  WO8 :: o
    "WO8 == \<forall>A. (\<exists>f. f \<in> (\<Pi>X \<in> A. X)) --> (\<exists>R. well_ord(A,R))"


(* Auxiliary concepts needed below *)
  pairwise_disjoint :: "i => o"
    "pairwise_disjoint(A) == \<forall>A1 \<in> A. \<forall>A2 \<in> A. A1 Int A2 \<noteq> 0 --> A1=A2"

  sets_of_size_between :: "[i, i, i] => o"
    "sets_of_size_between(A,m,n) == \<forall>B \<in> A. m \<lesssim> B & B \<lesssim> n"


(* Axioms of Choice *)  
  AC0 :: o
    "AC0 == \<forall>A. \<exists>f. f \<in> (\<Pi>X \<in> Pow(A)-{0}. X)"

  AC1 :: o
    "AC1 == \<forall>A. 0\<notin>A --> (\<exists>f. f \<in> (\<Pi>X \<in> A. X))"

  AC2 :: o
    "AC2 == \<forall>A. 0\<notin>A & pairwise_disjoint(A)   
		   --> (\<exists>C. \<forall>B \<in> A. \<exists>y. B Int C = {y})"
  AC3 :: o
    "AC3 == \<forall>A B. \<forall>f \<in> A->B. \<exists>g. g \<in> (\<Pi>x \<in> {a \<in> A. f`a\<noteq>0}. f`x)"

  AC4 :: o
    "AC4 == \<forall>R A B. (R \<subseteq> A*B --> (\<exists>f. f \<in> (\<Pi>x \<in> domain(R). R``{x})))"

  AC5 :: o
    "AC5 == \<forall>A B. \<forall>f \<in> A->B. \<exists>g \<in> range(f)->A. \<forall>x \<in> domain(g). f`(g`x) = x"

  AC6 :: o
    "AC6 == \<forall>A. 0\<notin>A --> (\<Pi>B \<in> A. B)\<noteq>0"

  AC7 :: o
    "AC7 == \<forall>A. 0\<notin>A & (\<forall>B1 \<in> A. \<forall>B2 \<in> A. B1\<approx>B2) --> (\<Pi>B \<in> A. B) \<noteq> 0"

  AC8 :: o
    "AC8 == \<forall>A. (\<forall>B \<in> A. \<exists>B1 B2. B=<B1,B2> & B1\<approx>B2)   
		   --> (\<exists>f. \<forall>B \<in> A. f`B \<in> bij(fst(B),snd(B)))"

  AC9 :: o
    "AC9 == \<forall>A. (\<forall>B1 \<in> A. \<forall>B2 \<in> A. B1\<approx>B2) -->   
		   (\<exists>f. \<forall>B1 \<in> A. \<forall>B2 \<in> A. f`<B1,B2> \<in> bij(B1,B2))"

  AC10 :: "i => o"
    "AC10(n) ==  \<forall>A. (\<forall>B \<in> A. ~Finite(B)) -->   
		   (\<exists>f. \<forall>B \<in> A. (pairwise_disjoint(f`B) &   
		   sets_of_size_between(f`B, 2, succ(n)) & Union(f`B)=B))"

  AC11 :: o
    "AC11 == \<exists>n \<in> nat. 1\<le>n & AC10(n)"

  AC12 :: o
    "AC12 == \<forall>A. (\<forall>B \<in> A. ~Finite(B)) -->
  	         (\<exists>n \<in> nat. 1\<le>n & (\<exists>f. \<forall>B \<in> A. (pairwise_disjoint(f`B) &   
	              sets_of_size_between(f`B, 2, succ(n)) & Union(f`B)=B)))"

  AC13 :: "i => o"
    "AC13(m) == \<forall>A. 0\<notin>A --> (\<exists>f. \<forall>B \<in> A. f`B\<noteq>0 & f`B \<subseteq> B & f`B \<lesssim> m)"

  AC14 :: o
    "AC14 == \<exists>m \<in> nat. 1\<le>m & AC13(m)"

  AC15 :: o
    "AC15 == \<forall>A. 0\<notin>A --> 
                 (\<exists>m \<in> nat. 1\<le>m & (\<exists>f. \<forall>B \<in> A. f`B\<noteq>0 & f`B \<subseteq> B & f`B \<lesssim> m))"

  AC16 :: "[i, i] => o"
    "AC16(n, k)  == 
       \<forall>A. ~Finite(A) -->   
	   (\<exists>T. T \<subseteq> {X \<in> Pow(A). X\<approx>succ(n)} &   
	   (\<forall>X \<in> {X \<in> Pow(A). X\<approx>succ(k)}. \<exists>! Y. Y \<in> T & X \<subseteq> Y))"

  AC17 :: o
    "AC17 == \<forall>A. \<forall>g \<in> (Pow(A)-{0} -> A) -> Pow(A)-{0}.   
		   \<exists>f \<in> Pow(A)-{0} -> A. f`(g`f) \<in> g`f"

  AC18 :: "prop" ("AC18")
    "AC18 == (!!X A B. A\<noteq>0 & (\<forall>a \<in> A. B(a) \<noteq> 0) -->   
		((\<Inter>a \<in> A. \<Union>b \<in> B(a). X(a,b)) =   
		(\<Union>f \<in> \<Pi>a \<in> A. B(a). \<Inter>a \<in> A. X(a, f`a))))"
  --"AC18 can be expressed only using meta-level quantification"

  AC19 :: o
    "AC19 == \<forall>A. A\<noteq>0 & 0\<notin>A --> ((\<Inter>a \<in> A. \<Union>b \<in> a. b) =   
		   (\<Union>f \<in> (\<Pi>B \<in> A. B). \<Inter>a \<in> A. f`a))"



(* ********************************************************************** *)
(*                    Theorems concerning ordinals                        *)
(* ********************************************************************** *)

(* lemma for ordertype_Int *)
lemma rvimage_id: "rvimage(A,id(A),r) = r Int A*A"
apply (unfold rvimage_def)
apply (rule equalityI, safe)
apply (drule_tac P = "%a. <id (A) `xb,a>:r" in id_conv [THEN subst],
       assumption)
apply (drule_tac P = "%a. <a,ya>:r" in id_conv [THEN subst], (assumption+))
apply (fast intro: id_conv [THEN ssubst])
done

(* used only in Hartog.ML *)
lemma ordertype_Int:
     "well_ord(A,r) ==> ordertype(A, r Int A*A) = ordertype(A,r)"
apply (rule_tac P = "%a. ordertype (A,a) =ordertype (A,r) " in rvimage_id [THEN subst])
apply (erule id_bij [THEN bij_ordertype_vimage])
done

lemma lam_sing_bij: "(\<lambda>x \<in> A. {x}) \<in> bij(A, {{x}. x \<in> A})"
apply (rule_tac d = "%z. THE x. z={x}" in lam_bijective)
apply (auto simp add: the_equality)
done

lemma inj_strengthen_type: 
     "[| f \<in> inj(A, B);  !!a. a \<in> A ==> f`a \<in> C |] ==> f \<in> inj(A,C)"
by (unfold inj_def, blast intro: Pi_type) 

lemma nat_not_Finite: "~ Finite(nat)"
by (unfold Finite_def, blast dest: eqpoll_imp_lepoll ltI lt_not_lepoll)

lemmas le_imp_lepoll = le_imp_subset [THEN subset_imp_lepoll]

(* ********************************************************************** *)
(* Another elimination rule for \<exists>!                                       *)
(* ********************************************************************** *)

lemma ex1_two_eq: "[| \<exists>! x. P(x); P(x); P(y) |] ==> x=y"
by blast

(* ********************************************************************** *)
(* image of a surjection                                                  *)
(* ********************************************************************** *)

lemma surj_image_eq: "f \<in> surj(A, B) ==> f``A = B"
apply (unfold surj_def)
apply (erule CollectE)
apply (rule image_fun [THEN ssubst], assumption, rule subset_refl)
apply (blast dest: apply_type) 
done


(* ********************************************************************** *)
(* Lemmas used in the proofs like WO? ==> AC?                             *)
(* ********************************************************************** *)

lemma first_in_B:
     "[| well_ord(Union(A),r); 0\<notin>A; B \<in> A |] ==> (THE b. first(b,B,r)) \<in> B"
by (blast dest!: well_ord_imp_ex1_first
                    [THEN theI, THEN first_def [THEN def_imp_iff, THEN iffD1]])

lemma ex_choice_fun: "[| well_ord(Union(A), R); 0\<notin>A |] ==> \<exists>f. f:(\<Pi>X \<in> A. X)"
by (fast elim!: first_in_B intro!: lam_type)

lemma ex_choice_fun_Pow: "well_ord(A, R) ==> \<exists>f. f:(\<Pi>X \<in> Pow(A)-{0}. X)"
by (fast elim!: well_ord_subset [THEN ex_choice_fun])


(* ********************************************************************** *)
(* Lemmas needed to state when a finite relation is a function.           *)
(*     The criteria are cardinalities of the relation and its domain.     *)
(*     Used in WO6WO1.ML                                                  *)
(* ********************************************************************** *)

(*Using AC we could trivially prove, for all u, domain(u) \<lesssim> u*)
lemma lepoll_m_imp_domain_lepoll_m: 
     "[| m \<in> nat; u \<lesssim> m |] ==> domain(u) \<lesssim> m"
apply (unfold lepoll_def)
apply (erule exE)
apply (rule_tac x = "\<lambda>x \<in> domain(u). LEAST i. \<exists>y. <x,y> \<in> u & f`<x,y> = i" 
       in exI)
apply (rule_tac d = "%y. fst (converse(f) ` y) " in lam_injective)
apply (fast intro: LeastI2 nat_into_Ord [THEN Ord_in_Ord] 
                           inj_is_fun [THEN apply_type])
apply (erule domainE)
apply (frule inj_is_fun [THEN apply_type], assumption)
apply (rule LeastI2)
apply (auto elim!: nat_into_Ord [THEN Ord_in_Ord])
done

lemma rel_domain_ex1: 
    "[| succ(m) \<lesssim> domain(r); r \<lesssim> succ(m); m \<in> nat |] ==> function(r)"
apply (unfold function_def, safe)
apply (rule ccontr) 
apply (fast elim!: lepoll_trans [THEN succ_lepoll_natE] 
                   lepoll_m_imp_domain_lepoll_m [OF _ Diff_sing_lepoll]
            elim: domain_Diff_eq [OF _ not_sym, THEN subst])
done

lemma rel_is_fun:
     "[| succ(m) \<lesssim> domain(r);  r \<lesssim> succ(m);  m \<in> nat;   
         r \<subseteq> A*B; A=domain(r) |] ==> r \<in> A->B"
by (simp add: Pi_iff rel_domain_ex1)

end
