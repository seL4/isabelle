(*  Title:      HOL/UNITY/Follows
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge
*)

header{*The Follows Relation of Charpentier and Sivilotte*}

theory Follows = SubstAx + ListOrder + Multiset:

constdefs

  Follows :: "['a => 'b::{order}, 'a => 'b::{order}] => 'a program set"
                 (infixl "Fols" 65)
   "f Fols g == Increasing g \<inter> Increasing f Int
                Always {s. f s \<le> g s} Int
                (\<Inter>k. {s. k \<le> g s} LeadsTo {s. k \<le> f s})"


(*Does this hold for "invariant"?*)
lemma mono_Always_o:
     "mono h ==> Always {s. f s \<le> g s} \<subseteq> Always {s. h (f s) \<le> h (g s)}"
apply (simp add: Always_eq_includes_reachable)
apply (blast intro: monoD)
done

lemma mono_LeadsTo_o:
     "mono (h::'a::order => 'b::order)  
      ==> (\<Inter>j. {s. j \<le> g s} LeadsTo {s. j \<le> f s}) \<subseteq>  
          (\<Inter>k. {s. k \<le> h (g s)} LeadsTo {s. k \<le> h (f s)})"
apply auto
apply (rule single_LeadsTo_I)
apply (drule_tac x = "g s" in spec)
apply (erule LeadsTo_weaken)
apply (blast intro: monoD order_trans)+
done

lemma Follows_constant [iff]: "F \<in> (%s. c) Fols (%s. c)"
by (unfold Follows_def, auto)

lemma mono_Follows_o: "mono h ==> f Fols g \<subseteq> (h o f) Fols (h o g)"
apply (unfold Follows_def, clarify)
apply (simp add: mono_Increasing_o [THEN [2] rev_subsetD]
                 mono_Always_o [THEN [2] rev_subsetD]
                 mono_LeadsTo_o [THEN [2] rev_subsetD, THEN INT_D])
done

lemma mono_Follows_apply:
     "mono h ==> f Fols g \<subseteq> (%x. h (f x)) Fols (%x. h (g x))"
apply (drule mono_Follows_o)
apply (force simp add: o_def)
done

lemma Follows_trans: 
     "[| F \<in> f Fols g;  F \<in> g Fols h |] ==> F \<in> f Fols h"
apply (unfold Follows_def)
apply (simp add: Always_eq_includes_reachable)
apply (blast intro: order_trans LeadsTo_Trans)
done


subsection{*Destruction rules*}

lemma Follows_Increasing1: "F \<in> f Fols g ==> F \<in> Increasing f"
by (unfold Follows_def, blast)

lemma Follows_Increasing2: "F \<in> f Fols g ==> F \<in> Increasing g"
by (unfold Follows_def, blast)

lemma Follows_Bounded: "F \<in> f Fols g ==> F \<in> Always {s. f s \<subseteq> g s}"
by (unfold Follows_def, blast)

lemma Follows_LeadsTo: 
     "F \<in> f Fols g ==> F \<in> {s. k \<le> g s} LeadsTo {s. k \<le> f s}"
by (unfold Follows_def, blast)

lemma Follows_LeadsTo_pfixLe:
     "F \<in> f Fols g ==> F \<in> {s. k pfixLe g s} LeadsTo {s. k pfixLe f s}"
apply (rule single_LeadsTo_I, clarify)
apply (drule_tac k="g s" in Follows_LeadsTo)
apply (erule LeadsTo_weaken)
 apply blast 
apply (blast intro: pfixLe_trans prefix_imp_pfixLe)
done

lemma Follows_LeadsTo_pfixGe:
     "F \<in> f Fols g ==> F \<in> {s. k pfixGe g s} LeadsTo {s. k pfixGe f s}"
apply (rule single_LeadsTo_I, clarify)
apply (drule_tac k="g s" in Follows_LeadsTo)
apply (erule LeadsTo_weaken)
 apply blast 
apply (blast intro: pfixGe_trans prefix_imp_pfixGe)
done


lemma Always_Follows1: 
     "[| F \<in> Always {s. f s = f' s}; F \<in> f Fols g |] ==> F \<in> f' Fols g"

apply (unfold Follows_def Increasing_def Stable_def, auto)
apply (erule_tac [3] Always_LeadsTo_weaken)
apply (erule_tac A = "{s. z \<le> f s}" and A' = "{s. z \<le> f s}" 
       in Always_Constrains_weaken, auto)
apply (drule Always_Int_I, assumption)
apply (force intro: Always_weaken)
done

lemma Always_Follows2: 
     "[| F \<in> Always {s. g s = g' s}; F \<in> f Fols g |] ==> F \<in> f Fols g'"
apply (unfold Follows_def Increasing_def Stable_def, auto)
apply (erule_tac [3] Always_LeadsTo_weaken)
apply (erule_tac A = "{s. z \<le> g s}" and A' = "{s. z \<le> g s}"
       in Always_Constrains_weaken, auto)
apply (drule Always_Int_I, assumption)
apply (force intro: Always_weaken)
done


subsection{*Union properties (with the subset ordering)*}

(*Can replace "Un" by any sup.  But existing max only works for linorders.*)
lemma increasing_Un: 
    "[| F \<in> increasing f;  F \<in> increasing g |]  
     ==> F \<in> increasing (%s. (f s) \<union> (g s))"
apply (unfold increasing_def stable_def constrains_def, auto)
apply (drule_tac x = "f xa" in spec)
apply (drule_tac x = "g xa" in spec)
apply (blast dest!: bspec)
done

lemma Increasing_Un: 
    "[| F \<in> Increasing f;  F \<in> Increasing g |]  
     ==> F \<in> Increasing (%s. (f s) \<union> (g s))"
apply (auto simp add: Increasing_def Stable_def Constrains_def
                      stable_def constrains_def)
apply (drule_tac x = "f xa" in spec)
apply (drule_tac x = "g xa" in spec)
apply (blast dest!: bspec)
done


lemma Always_Un:
     "[| F \<in> Always {s. f' s \<le> f s}; F \<in> Always {s. g' s \<le> g s} |]  
      ==> F \<in> Always {s. f' s \<union> g' s \<le> f s \<union> g s}"
by (simp add: Always_eq_includes_reachable, blast)

(*Lemma to re-use the argument that one variable increases (progress)
  while the other variable doesn't decrease (safety)*)
lemma Follows_Un_lemma:
     "[| F \<in> Increasing f; F \<in> Increasing g;  
         F \<in> Increasing g'; F \<in> Always {s. f' s \<le> f s}; 
         \<forall>k. F \<in> {s. k \<le> f s} LeadsTo {s. k \<le> f' s} |] 
      ==> F \<in> {s. k \<le> f s \<union> g s} LeadsTo {s. k \<le> f' s \<union> g s}"
apply (rule single_LeadsTo_I)
apply (drule_tac x = "f s" in IncreasingD)
apply (drule_tac x = "g s" in IncreasingD)
apply (rule LeadsTo_weaken)
apply (rule PSP_Stable)
apply (erule_tac x = "f s" in spec)
apply (erule Stable_Int, assumption, blast+)
done

lemma Follows_Un: 
    "[| F \<in> f' Fols f;  F \<in> g' Fols g |]  
     ==> F \<in> (%s. (f' s) \<union> (g' s)) Fols (%s. (f s) \<union> (g s))"
apply (unfold Follows_def)
apply (simp add: Increasing_Un Always_Un, auto)
apply (rule LeadsTo_Trans)
apply (blast intro: Follows_Un_lemma)
(*Weakening is used to exchange Un's arguments*)
apply (blast intro: Follows_Un_lemma [THEN LeadsTo_weaken])
done


subsection{*Multiset union properties (with the multiset ordering)*}

lemma increasing_union: 
    "[| F \<in> increasing f;  F \<in> increasing g |]  
     ==> F \<in> increasing (%s. (f s) + (g s :: ('a::order) multiset))"
apply (unfold increasing_def stable_def constrains_def, auto)
apply (drule_tac x = "f xa" in spec)
apply (drule_tac x = "g xa" in spec)
apply (drule bspec, assumption) 
apply (blast intro: union_le_mono order_trans)
done

lemma Increasing_union: 
    "[| F \<in> Increasing f;  F \<in> Increasing g |]  
     ==> F \<in> Increasing (%s. (f s) + (g s :: ('a::order) multiset))"
apply (auto simp add: Increasing_def Stable_def Constrains_def
                      stable_def constrains_def)
apply (drule_tac x = "f xa" in spec)
apply (drule_tac x = "g xa" in spec)
apply (drule bspec, assumption) 
apply (blast intro: union_le_mono order_trans)
done

lemma Always_union:
     "[| F \<in> Always {s. f' s \<le> f s}; F \<in> Always {s. g' s \<le> g s} |]  
      ==> F \<in> Always {s. f' s + g' s \<le> f s + (g s :: ('a::order) multiset)}"
apply (simp add: Always_eq_includes_reachable)
apply (blast intro: union_le_mono)
done

(*Except the last line, IDENTICAL to the proof script for Follows_Un_lemma*)
lemma Follows_union_lemma:
     "[| F \<in> Increasing f; F \<in> Increasing g;  
         F \<in> Increasing g'; F \<in> Always {s. f' s \<le> f s}; 
         \<forall>k::('a::order) multiset.  
           F \<in> {s. k \<le> f s} LeadsTo {s. k \<le> f' s} |] 
      ==> F \<in> {s. k \<le> f s + g s} LeadsTo {s. k \<le> f' s + g s}"
apply (rule single_LeadsTo_I)
apply (drule_tac x = "f s" in IncreasingD)
apply (drule_tac x = "g s" in IncreasingD)
apply (rule LeadsTo_weaken)
apply (rule PSP_Stable)
apply (erule_tac x = "f s" in spec)
apply (erule Stable_Int, assumption, blast)
apply (blast intro: union_le_mono order_trans)
done

(*The !! is there to influence to effect of permutative rewriting at the end*)
lemma Follows_union: 
     "!!g g' ::'b => ('a::order) multiset.  
        [| F \<in> f' Fols f;  F \<in> g' Fols g |]  
        ==> F \<in> (%s. (f' s) + (g' s)) Fols (%s. (f s) + (g s))"
apply (unfold Follows_def)
apply (simp add: Increasing_union Always_union, auto)
apply (rule LeadsTo_Trans)
apply (blast intro: Follows_union_lemma)
(*now exchange union's arguments*)
apply (simp add: union_commute)
apply (blast intro: Follows_union_lemma)
done

lemma Follows_setsum:
     "!!f ::['c,'b] => ('a::order) multiset.  
        [| \<forall>i \<in> I. F \<in> f' i Fols f i;  finite I |]  
        ==> F \<in> (%s. \<Sum>i \<in> I. f' i s) Fols (%s. \<Sum>i \<in> I. f i s)"
apply (erule rev_mp)
apply (erule finite_induct, simp) 
apply (simp add: Follows_union)
done


(*Currently UNUSED, but possibly of interest*)
lemma Increasing_imp_Stable_pfixGe:
     "F \<in> Increasing func ==> F \<in> Stable {s. h pfixGe (func s)}"
apply (simp add: Increasing_def Stable_def Constrains_def constrains_def)
apply (blast intro: trans_Ge [THEN trans_genPrefix, THEN transD] 
                    prefix_imp_pfixGe)
done

(*Currently UNUSED, but possibly of interest*)
lemma LeadsTo_le_imp_pfixGe:
     "\<forall>z. F \<in> {s. z \<le> f s} LeadsTo {s. z \<le> g s}  
      ==> F \<in> {s. z pfixGe f s} LeadsTo {s. z pfixGe g s}"
apply (rule single_LeadsTo_I)
apply (drule_tac x = "f s" in spec)
apply (erule LeadsTo_weaken)
 prefer 2
 apply (blast intro: trans_Ge [THEN trans_genPrefix, THEN transD] 
                     prefix_imp_pfixGe, blast)
done

end
