(*  Title:      ZF/Coind/Map.thy
    ID:         $Id$
    Author:     Jacob Frost, Cambridge University Computer Laboratory
    Copyright   1995  University of Cambridge


Some sample proofs of inclusions for the final coalgebra "U" (by lcp) 

*)

theory Map = Main:

constdefs
  TMap :: "[i,i] => i"
   "TMap(A,B) == {m \<in> Pow(A*Union(B)).\<forall>a \<in> A. m``{a} \<in> B}"

  PMap :: "[i,i] => i"
   "PMap(A,B) == TMap(A,cons(0,B))"

(* Note: 0 \<in> B ==> TMap(A,B) = PMap(A,B) *)
  
  map_emp :: i
   "map_emp == 0"

  map_owr :: "[i,i,i]=>i"
   "map_owr(m,a,b) == \<Sigma>x \<in> {a} Un domain(m). if x=a then b else m``{x}"

  map_app :: "[i,i]=>i"
   "map_app(m,a) == m``{a}"
  
lemma "{0,1} \<subseteq> {1} Un TMap(I, {0,1})"
by (unfold TMap_def, blast)

lemma "{0} Un TMap(I,1) \<subseteq> {1} Un TMap(I, {0} Un TMap(I,1))"
by (unfold TMap_def, blast)

lemma "{0,1} Un TMap(I,2) \<subseteq> {1} Un TMap(I, {0,1} Un TMap(I,2))"
by (unfold TMap_def, blast)

(*A bit too slow.
lemma "{0,1} Un TMap(I,TMap(I,2)) Un TMap(I,2) \<subseteq>  
       {1} Un TMap(I, {0,1} Un TMap(I,TMap(I,2)) Un TMap(I,2))"
by (unfold TMap_def, blast)
*)

(* ############################################################ *)
(* Lemmas                                                       *)
(* ############################################################ *)

lemma qbeta_if: "Sigma(A,B)``{a} = (if a \<in> A then B(a) else 0)"
by auto

lemma qbeta: "a \<in> A ==> Sigma(A,B)``{a} = B(a)"
by fast

lemma qbeta_emp: "a\<notin>A ==> Sigma(A,B)``{a} = 0"
by fast

lemma image_Sigma1: "a \<notin> A ==> Sigma(A,B)``{a}=0"
by fast


(* ############################################################ *)
(* Inclusion in Quine Universes                                 *)
(* ############################################################ *)

(* Lemmas *)

lemma MapQU_lemma: 
    "A \<subseteq> univ(X) ==> Pow(A * Union(quniv(X))) \<subseteq> quniv(X)"
apply (unfold quniv_def)
apply (rule Pow_mono)
apply (rule subset_trans [OF Sigma_mono product_univ])
apply (erule subset_trans)
apply (rule arg_subset_eclose [THEN univ_mono])
apply (simp add: Union_Pow_eq)
done

(* Theorems *)

lemma mapQU:
  "[| m \<in> PMap(A,quniv(B)); !!x. x \<in> A ==> x \<in> univ(B) |] ==> m \<in> quniv(B)"
apply (unfold PMap_def TMap_def)
apply (blast intro!: MapQU_lemma [THEN subsetD]) 
done

(* ############################################################ *)
(* Monotonicity                                                 *)
(* ############################################################ *)

lemma PMap_mono: "B \<subseteq> C ==> PMap(A,B)<=PMap(A,C)"
by (unfold PMap_def TMap_def, blast)


(* ############################################################ *)
(* Introduction Rules                                           *)
(* ############################################################ *)

(** map_emp **)

lemma pmap_empI: "map_emp \<in> PMap(A,B)"
by (unfold map_emp_def PMap_def TMap_def, auto)

(** map_owr **)

lemma pmap_owrI: 
  "[| m \<in> PMap(A,B); a \<in> A; b \<in> B |]  ==> map_owr(m,a,b):PMap(A,B)"
apply (unfold map_owr_def PMap_def TMap_def, safe)
apply (simp_all add: if_iff, auto)
(*Remaining subgoal*)
apply (rule excluded_middle [THEN disjE])
apply (erule image_Sigma1)
apply (drule_tac psi = "?uu \<notin> B" in asm_rl)
apply (auto simp add: qbeta)
done

(** map_app **)

lemma tmap_app_notempty: 
  "[| m \<in> TMap(A,B); a \<in> domain(m) |] ==> map_app(m,a) \<noteq>0"
by (unfold TMap_def map_app_def, blast)

lemma tmap_appI: 
  "[| m \<in> TMap(A,B); a \<in> domain(m) |] ==> map_app(m,a):B"
by (unfold TMap_def map_app_def domain_def, blast)

lemma pmap_appI: 
  "[| m \<in> PMap(A,B); a \<in> domain(m) |] ==> map_app(m,a):B"
apply (unfold PMap_def)
apply (frule tmap_app_notempty, assumption)
apply (drule tmap_appI, auto)
done

(** domain **)

lemma tmap_domainD: 
  "[| m \<in> TMap(A,B); a \<in> domain(m) |] ==> a \<in> A"
by (unfold TMap_def, blast)

lemma pmap_domainD: 
  "[| m \<in> PMap(A,B); a \<in> domain(m) |] ==> a \<in> A"
by (unfold PMap_def TMap_def, blast)


(* ############################################################ *)
(* Equalities                                                   *)
(* ############################################################ *)

(** Domain **)

(* Lemmas *)

lemma domain_UN: "domain(\<Union>x \<in> A. B(x)) = (\<Union>x \<in> A. domain(B(x)))"
by fast


lemma domain_Sigma: "domain(Sigma(A,B)) = {x \<in> A. \<exists>y. y \<in> B(x)}"
by blast

(* Theorems *)

lemma map_domain_emp: "domain(map_emp) = 0"
by (unfold map_emp_def, blast)

lemma map_domain_owr: 
  "b \<noteq> 0 ==> domain(map_owr(f,a,b)) = {a} Un domain(f)"
apply (unfold map_owr_def)
apply (auto simp add: domain_Sigma)
done

(** Application **)

lemma map_app_owr: 
  "map_app(map_owr(f,a,b),c) = (if c=a then b else map_app(f,c))"
by (simp add: qbeta_if  map_app_def map_owr_def, blast)

lemma map_app_owr1: "map_app(map_owr(f,a,b),a) = b"
by (simp add: map_app_owr)

lemma map_app_owr2: "c \<noteq> a ==> map_app(map_owr(f,a,b),c)= map_app(f,c)"
by (simp add: map_app_owr)

end
