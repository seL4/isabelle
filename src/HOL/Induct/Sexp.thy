(*  Title:      HOL/Induct/Sexp.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

S-expressions, general binary trees for defining recursive data
structures by hand.
*)

theory Sexp = Datatype_Universe + Inductive:
consts
  sexp      :: "'a item set"

inductive sexp
  intros
    LeafI:  "Leaf(a) \<in> sexp"
    NumbI:  "Numb(i) \<in> sexp"
    SconsI: "[| M \<in> sexp;  N \<in> sexp |] ==> Scons M N \<in> sexp"

constdefs

  sexp_case :: "['a=>'b, nat=>'b, ['a item, 'a item]=>'b, 
                'a item] => 'b"
   "sexp_case c d e M == THE z. (EX x.   M=Leaf(x) & z=c(x))  
                            | (EX k.   M=Numb(k) & z=d(k))  
                            | (EX N1 N2. M = Scons N1 N2  & z=e N1 N2)"

  pred_sexp :: "('a item * 'a item)set"
     "pred_sexp == \<Union>M \<in> sexp. \<Union>N \<in> sexp. {(M, Scons M N), (N, Scons M N)}"

  sexp_rec  :: "['a item, 'a=>'b, nat=>'b,      
                ['a item, 'a item, 'b, 'b]=>'b] => 'b"
   "sexp_rec M c d e == wfrec pred_sexp
             (%g. sexp_case c d (%N1 N2. e N1 N2 (g N1) (g N2))) M"


(** sexp_case **)

lemma sexp_case_Leaf [simp]: "sexp_case c d e (Leaf a) = c(a)"
by (simp add: sexp_case_def, blast)

lemma sexp_case_Numb [simp]: "sexp_case c d e (Numb k) = d(k)"
by (simp add: sexp_case_def, blast)

lemma sexp_case_Scons [simp]: "sexp_case c d e (Scons M N) = e M N"
by (simp add: sexp_case_def)



(** Introduction rules for sexp constructors **)

lemma sexp_In0I: "M \<in> sexp ==> In0(M) \<in> sexp"
apply (simp add: In0_def) 
apply (erule sexp.NumbI [THEN sexp.SconsI])
done

lemma sexp_In1I: "M \<in> sexp ==> In1(M) \<in> sexp"
apply (simp add: In1_def) 
apply (erule sexp.NumbI [THEN sexp.SconsI])
done

declare sexp.intros [intro,simp]

lemma range_Leaf_subset_sexp: "range(Leaf) <= sexp"
by blast

lemma Scons_D: "Scons M N \<in> sexp ==> M \<in> sexp & N \<in> sexp"
apply (erule setup_induction)
apply (erule sexp.induct, blast+)
done

(** Introduction rules for 'pred_sexp' **)

lemma pred_sexp_subset_Sigma: "pred_sexp <= sexp <*> sexp"
by (simp add: pred_sexp_def, blast)

(* (a,b) \<in> pred_sexp^+ ==> a \<in> sexp *)
lemmas trancl_pred_sexpD1 = 
    pred_sexp_subset_Sigma
	 [THEN trancl_subset_Sigma, THEN subsetD, THEN SigmaD1]
and trancl_pred_sexpD2 = 
    pred_sexp_subset_Sigma
	 [THEN trancl_subset_Sigma, THEN subsetD, THEN SigmaD2]

lemma pred_sexpI1: 
    "[| M \<in> sexp;  N \<in> sexp |] ==> (M, Scons M N) \<in> pred_sexp"
by (simp add: pred_sexp_def, blast)

lemma pred_sexpI2: 
    "[| M \<in> sexp;  N \<in> sexp |] ==> (N, Scons M N) \<in> pred_sexp"
by (simp add: pred_sexp_def, blast)

(*Combinations involving transitivity and the rules above*)
lemmas pred_sexp_t1 [simp] = pred_sexpI1 [THEN r_into_trancl]
and    pred_sexp_t2 [simp] = pred_sexpI2 [THEN r_into_trancl]

lemmas pred_sexp_trans1 [simp] = trans_trancl [THEN transD, OF _ pred_sexp_t1]
and    pred_sexp_trans2 [simp] = trans_trancl [THEN transD, OF _ pred_sexp_t2]

(*Proves goals of the form (M,N):pred_sexp^+ provided M,N:sexp*)
declare cut_apply [simp] 

lemma pred_sexpE:
    "[| p \<in> pred_sexp;                                        
        !!M N. [| p = (M, Scons M N);  M \<in> sexp;  N \<in> sexp |] ==> R;  
        !!M N. [| p = (N, Scons M N);  M \<in> sexp;  N \<in> sexp |] ==> R   
     |] ==> R"
by (simp add: pred_sexp_def, blast) 

lemma wf_pred_sexp: "wf(pred_sexp)"
apply (rule pred_sexp_subset_Sigma [THEN wfI])
apply (erule sexp.induct)
apply (blast elim!: pred_sexpE)+
done


(*** sexp_rec -- by wf recursion on pred_sexp ***)

lemma sexp_rec_unfold_lemma:
     "(%M. sexp_rec M c d e) ==
      wfrec pred_sexp (%g. sexp_case c d (%N1 N2. e N1 N2 (g N1) (g N2)))"
by (simp add: sexp_rec_def)

lemmas sexp_rec_unfold = def_wfrec [OF sexp_rec_unfold_lemma wf_pred_sexp]

(* sexp_rec a c d e =
   sexp_case c d
    (%N1 N2.
        e N1 N2 (cut (%M. sexp_rec M c d e) pred_sexp a N1)
         (cut (%M. sexp_rec M c d e) pred_sexp a N2)) a
*)

(** conversion rules **)

lemma sexp_rec_Leaf: "sexp_rec (Leaf a) c d h = c(a)"
apply (subst sexp_rec_unfold)
apply (rule sexp_case_Leaf)
done

lemma sexp_rec_Numb: "sexp_rec (Numb k) c d h = d(k)"
apply (subst sexp_rec_unfold)
apply (rule sexp_case_Numb)
done

lemma sexp_rec_Scons: "[| M \<in> sexp;  N \<in> sexp |] ==>  
     sexp_rec (Scons M N) c d h = h M N (sexp_rec M c d h) (sexp_rec N c d h)"
apply (rule sexp_rec_unfold [THEN trans])
apply (simp add: pred_sexpI1 pred_sexpI2)
done

end
