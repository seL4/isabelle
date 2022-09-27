(*  Title:      ZF/AC/AC_Equiv.thy
    Author:     Krzysztof Grabczewski

Axioms AC1 -- AC19 come from "Equivalents of the Axiom of Choice, II"
by H. Rubin and J.E. Rubin, 1985.

Axiom AC0 comes from "Axiomatic Set Theory" by P. Suppes, 1972.

Some Isabelle proofs of equivalences of these axioms are formalizations of
proofs presented by the Rubins.  The others are based on the Rubins' proofs,
but slightly changed.
*)

theory AC_Equiv
imports ZF
begin (*obviously not ZFC*)

(* Well Ordering Theorems *)

definition  
    "WO1 \<equiv> \<forall>A. \<exists>R. well_ord(A,R)"

definition  
    "WO2 \<equiv> \<forall>A. \<exists>a. Ord(a) \<and> A\<approx>a"

definition  
    "WO3 \<equiv> \<forall>A. \<exists>a. Ord(a) \<and> (\<exists>b. b \<subseteq> a \<and> A\<approx>b)"

definition  
    "WO4(m) \<equiv> \<forall>A. \<exists>a f. Ord(a) \<and> domain(f)=a \<and>   
                         (\<Union>b<a. f`b) = A \<and> (\<forall>b<a. f`b \<lesssim> m)"

definition  
    "WO5 \<equiv> \<exists>m \<in> nat. 1\<le>m \<and> WO4(m)"

definition  
    "WO6 \<equiv> \<forall>A. \<exists>m \<in> nat. 1\<le>m \<and> (\<exists>a f. Ord(a) \<and> domain(f)=a
                               \<and> (\<Union>b<a. f`b) = A \<and> (\<forall>b<a. f`b \<lesssim> m))"

definition  
    "WO7 \<equiv> \<forall>A. Finite(A) \<longleftrightarrow> (\<forall>R. well_ord(A,R) \<longrightarrow> well_ord(A,converse(R)))"

definition  
    "WO8 \<equiv> \<forall>A. (\<exists>f. f \<in> (\<Prod>X \<in> A. X)) \<longrightarrow> (\<exists>R. well_ord(A,R))"


definition
(* Auxiliary concepts needed below *)
  pairwise_disjoint :: "i \<Rightarrow> o"  where
    "pairwise_disjoint(A) \<equiv> \<forall>A1 \<in> A. \<forall>A2 \<in> A. A1 \<inter> A2 \<noteq> 0 \<longrightarrow> A1=A2"

definition
  sets_of_size_between :: "[i, i, i] \<Rightarrow> o"  where
    "sets_of_size_between(A,m,n) \<equiv> \<forall>B \<in> A. m \<lesssim> B \<and> B \<lesssim> n"


(* Axioms of Choice *)  
definition
    "AC0 \<equiv> \<forall>A. \<exists>f. f \<in> (\<Prod>X \<in> Pow(A)-{0}. X)"

definition
    "AC1 \<equiv> \<forall>A. 0\<notin>A \<longrightarrow> (\<exists>f. f \<in> (\<Prod>X \<in> A. X))"

definition
    "AC2 \<equiv> \<forall>A. 0\<notin>A \<and> pairwise_disjoint(A)   
                   \<longrightarrow> (\<exists>C. \<forall>B \<in> A. \<exists>y. B \<inter> C = {y})"
definition
    "AC3 \<equiv> \<forall>A B. \<forall>f \<in> A->B. \<exists>g. g \<in> (\<Prod>x \<in> {a \<in> A. f`a\<noteq>0}. f`x)"

definition
    "AC4 \<equiv> \<forall>R A B. (R \<subseteq> A*B \<longrightarrow> (\<exists>f. f \<in> (\<Prod>x \<in> domain(R). R``{x})))"

definition
    "AC5 \<equiv> \<forall>A B. \<forall>f \<in> A->B. \<exists>g \<in> range(f)->A. \<forall>x \<in> domain(g). f`(g`x) = x"

definition
    "AC6 \<equiv> \<forall>A. 0\<notin>A \<longrightarrow> (\<Prod>B \<in> A. B)\<noteq>0"

definition
    "AC7 \<equiv> \<forall>A. 0\<notin>A \<and> (\<forall>B1 \<in> A. \<forall>B2 \<in> A. B1\<approx>B2) \<longrightarrow> (\<Prod>B \<in> A. B) \<noteq> 0"

definition
    "AC8 \<equiv> \<forall>A. (\<forall>B \<in> A. \<exists>B1 B2. B=\<langle>B1,B2\<rangle> \<and> B1\<approx>B2)   
                   \<longrightarrow> (\<exists>f. \<forall>B \<in> A. f`B \<in> bij(fst(B),snd(B)))"

definition
    "AC9 \<equiv> \<forall>A. (\<forall>B1 \<in> A. \<forall>B2 \<in> A. B1\<approx>B2) \<longrightarrow>   
                   (\<exists>f. \<forall>B1 \<in> A. \<forall>B2 \<in> A. f`\<langle>B1,B2\<rangle> \<in> bij(B1,B2))"

definition
    "AC10(n) \<equiv>  \<forall>A. (\<forall>B \<in> A. \<not>Finite(B)) \<longrightarrow>   
                   (\<exists>f. \<forall>B \<in> A. (pairwise_disjoint(f`B) \<and>   
                   sets_of_size_between(f`B, 2, succ(n)) \<and> \<Union>(f`B)=B))"

definition
    "AC11 \<equiv> \<exists>n \<in> nat. 1\<le>n \<and> AC10(n)"

definition
    "AC12 \<equiv> \<forall>A. (\<forall>B \<in> A. \<not>Finite(B)) \<longrightarrow>
                 (\<exists>n \<in> nat. 1\<le>n \<and> (\<exists>f. \<forall>B \<in> A. (pairwise_disjoint(f`B) \<and>   
                      sets_of_size_between(f`B, 2, succ(n)) \<and> \<Union>(f`B)=B)))"

definition
    "AC13(m) \<equiv> \<forall>A. 0\<notin>A \<longrightarrow> (\<exists>f. \<forall>B \<in> A. f`B\<noteq>0 \<and> f`B \<subseteq> B \<and> f`B \<lesssim> m)"

definition
    "AC14 \<equiv> \<exists>m \<in> nat. 1\<le>m \<and> AC13(m)"

definition
    "AC15 \<equiv> \<forall>A. 0\<notin>A \<longrightarrow> 
                 (\<exists>m \<in> nat. 1\<le>m \<and> (\<exists>f. \<forall>B \<in> A. f`B\<noteq>0 \<and> f`B \<subseteq> B \<and> f`B \<lesssim> m))"

definition
    "AC16(n, k)  \<equiv> 
       \<forall>A. \<not>Finite(A) \<longrightarrow>   
           (\<exists>T. T \<subseteq> {X \<in> Pow(A). X\<approx>succ(n)} \<and>   
           (\<forall>X \<in> {X \<in> Pow(A). X\<approx>succ(k)}. \<exists>! Y. Y \<in> T \<and> X \<subseteq> Y))"

definition
    "AC17 \<equiv> \<forall>A. \<forall>g \<in> (Pow(A)-{0} -> A) -> Pow(A)-{0}.   
                   \<exists>f \<in> Pow(A)-{0} -> A. f`(g`f) \<in> g`f"

locale AC18 =
  assumes AC18: "A\<noteq>0 \<and> (\<forall>a \<in> A. B(a) \<noteq> 0) \<longrightarrow>
    ((\<Inter>a \<in> A. \<Union>b \<in> B(a). X(a,b)) =   
      (\<Union>f \<in> \<Prod>a \<in> A. B(a). \<Inter>a \<in> A. X(a, f`a)))"
  \<comment> \<open>AC18 cannot be expressed within the object-logic\<close>

definition
    "AC19 \<equiv> \<forall>A. A\<noteq>0 \<and> 0\<notin>A \<longrightarrow> ((\<Inter>a \<in> A. \<Union>b \<in> a. b) =   
                   (\<Union>f \<in> (\<Prod>B \<in> A. B). \<Inter>a \<in> A. f`a))"



(* ********************************************************************** *)
(*                    Theorems concerning ordinals                        *)
(* ********************************************************************** *)

(* lemma for ordertype_Int *)
lemma rvimage_id: "rvimage(A,id(A),r) = r \<inter> A*A"
apply (unfold rvimage_def)
apply (rule equalityI, safe)
apply (drule_tac P = "\<lambda>a. <id (A) `xb,a>:r" in id_conv [THEN subst],
       assumption)
apply (drule_tac P = "\<lambda>a. \<langle>a,ya\<rangle>:r" in id_conv [THEN subst], (assumption+))
apply (fast intro: id_conv [THEN ssubst])
done

(* used only in Hartog.ML *)
lemma ordertype_Int:
     "well_ord(A,r) \<Longrightarrow> ordertype(A, r \<inter> A*A) = ordertype(A,r)"
apply (rule_tac P = "\<lambda>a. ordertype (A,a) =ordertype (A,r) " in rvimage_id [THEN subst])
apply (erule id_bij [THEN bij_ordertype_vimage])
done

lemma lam_sing_bij: "(\<lambda>x \<in> A. {x}) \<in> bij(A, {{x}. x \<in> A})"
apply (rule_tac d = "\<lambda>z. THE x. z={x}" in lam_bijective)
apply (auto simp add: the_equality)
done

lemma inj_strengthen_type: 
     "\<lbrakk>f \<in> inj(A, B);  \<And>a. a \<in> A \<Longrightarrow> f`a \<in> C\<rbrakk> \<Longrightarrow> f \<in> inj(A,C)"
by (unfold inj_def, blast intro: Pi_type) 

(* ********************************************************************** *)
(* Another elimination rule for \<exists>!                                       *)
(* ********************************************************************** *)

lemma ex1_two_eq: "\<lbrakk>\<exists>! x. P(x); P(x); P(y)\<rbrakk> \<Longrightarrow> x=y"
by blast

(* ********************************************************************** *)
(* Lemmas used in the proofs like WO? \<Longrightarrow> AC?                             *)
(* ********************************************************************** *)

lemma first_in_B:
     "\<lbrakk>well_ord(\<Union>(A),r); 0 \<notin> A; B \<in> A\<rbrakk> \<Longrightarrow> (THE b. first(b,B,r)) \<in> B"
by (blast dest!: well_ord_imp_ex1_first
                    [THEN theI, THEN first_def [THEN def_imp_iff, THEN iffD1]])

lemma ex_choice_fun: "\<lbrakk>well_ord(\<Union>(A), R); 0 \<notin> A\<rbrakk> \<Longrightarrow> \<exists>f. f \<in> (\<Prod>X \<in> A. X)"
by (fast elim!: first_in_B intro!: lam_type)

lemma ex_choice_fun_Pow: "well_ord(A, R) \<Longrightarrow> \<exists>f. f \<in> (\<Prod>X \<in> Pow(A)-{0}. X)"
by (fast elim!: well_ord_subset [THEN ex_choice_fun])


(* ********************************************************************** *)
(* Lemmas needed to state when a finite relation is a function.           *)
(*     The criteria are cardinalities of the relation and its domain.     *)
(*     Used in WO6WO1.ML                                                  *)
(* ********************************************************************** *)

(*Using AC we could trivially prove, for all u, domain(u) \<lesssim> u*)
lemma lepoll_m_imp_domain_lepoll_m: 
     "\<lbrakk>m \<in> nat; u \<lesssim> m\<rbrakk> \<Longrightarrow> domain(u) \<lesssim> m"
apply (unfold lepoll_def)
apply (erule exE)
apply (rule_tac x = "\<lambda>x \<in> domain(u). \<mu> i. \<exists>y. \<langle>x,y\<rangle> \<in> u \<and> f`\<langle>x,y\<rangle> = i" 
       in exI)
apply (rule_tac d = "\<lambda>y. fst (converse(f) ` y) " in lam_injective)
apply (fast intro: LeastI2 nat_into_Ord [THEN Ord_in_Ord] 
                           inj_is_fun [THEN apply_type])
apply (erule domainE)
apply (frule inj_is_fun [THEN apply_type], assumption)
apply (rule LeastI2)
apply (auto elim!: nat_into_Ord [THEN Ord_in_Ord])
done

lemma rel_domain_ex1: 
    "\<lbrakk>succ(m) \<lesssim> domain(r); r \<lesssim> succ(m); m \<in> nat\<rbrakk> \<Longrightarrow> function(r)"
apply (unfold function_def, safe)
apply (rule ccontr) 
apply (fast elim!: lepoll_trans [THEN succ_lepoll_natE] 
                   lepoll_m_imp_domain_lepoll_m [OF _ Diff_sing_lepoll]
            elim: domain_Diff_eq [OF _ not_sym, THEN subst])
done

lemma rel_is_fun:
     "\<lbrakk>succ(m) \<lesssim> domain(r);  r \<lesssim> succ(m);  m \<in> nat;   
         r \<subseteq> A*B; A=domain(r)\<rbrakk> \<Longrightarrow> r \<in> A->B"
by (simp add: Pi_iff rel_domain_ex1)

end
