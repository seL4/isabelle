(*  Title:      HOL/UNITY/Follows
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The "Follows" relation of Charpentier and Sivilotte
*)

theory Follows = SubstAx + ListOrder + Multiset:

constdefs

  Follows :: "['a => 'b::{order}, 'a => 'b::{order}] => 'a program set"
                 (infixl "Fols" 65)
   "f Fols g == Increasing g Int Increasing f Int
                Always {s. f s <= g s} Int
                (INT k. {s. k <= g s} LeadsTo {s. k <= f s})"


(*Does this hold for "invariant"?*)
lemma mono_Always_o:
     "mono h ==> Always {s. f s <= g s} <= Always {s. h (f s) <= h (g s)}"
apply (simp add: Always_eq_includes_reachable)
apply (blast intro: monoD)
done

lemma mono_LeadsTo_o:
     "mono (h::'a::order => 'b::order)  
      ==> (INT j. {s. j <= g s} LeadsTo {s. j <= f s}) <=  
          (INT k. {s. k <= h (g s)} LeadsTo {s. k <= h (f s)})"
apply auto
apply (rule single_LeadsTo_I)
apply (drule_tac x = "g s" in spec)
apply (erule LeadsTo_weaken)
apply (blast intro: monoD order_trans)+
done

lemma Follows_constant: "F : (%s. c) Fols (%s. c)"
by (unfold Follows_def, auto)
declare Follows_constant [iff]

lemma mono_Follows_o: "mono h ==> f Fols g <= (h o f) Fols (h o g)"
apply (unfold Follows_def, clarify)
apply (simp add: mono_Increasing_o [THEN [2] rev_subsetD]
                 mono_Always_o [THEN [2] rev_subsetD]
                 mono_LeadsTo_o [THEN [2] rev_subsetD, THEN INT_D])
done

lemma mono_Follows_apply:
     "mono h ==> f Fols g <= (%x. h (f x)) Fols (%x. h (g x))"
apply (drule mono_Follows_o)
apply (force simp add: o_def)
done

lemma Follows_trans: 
     "[| F : f Fols g;  F: g Fols h |] ==> F : f Fols h"
apply (unfold Follows_def)
apply (simp add: Always_eq_includes_reachable)
apply (blast intro: order_trans LeadsTo_Trans)
done


(** Destructiom rules **)

lemma Follows_Increasing1: 
     "F : f Fols g ==> F : Increasing f"

apply (unfold Follows_def, blast)
done

lemma Follows_Increasing2: 
     "F : f Fols g ==> F : Increasing g"
apply (unfold Follows_def, blast)
done

lemma Follows_Bounded: 
     "F : f Fols g ==> F : Always {s. f s <= g s}"
apply (unfold Follows_def, blast)
done

lemma Follows_LeadsTo: 
     "F : f Fols g ==> F : {s. k <= g s} LeadsTo {s. k <= f s}"
apply (unfold Follows_def, blast)
done

lemma Follows_LeadsTo_pfixLe:
     "F : f Fols g ==> F : {s. k pfixLe g s} LeadsTo {s. k pfixLe f s}"
apply (rule single_LeadsTo_I, clarify)
apply (drule_tac k="g s" in Follows_LeadsTo)
apply (erule LeadsTo_weaken)
 apply blast 
apply (blast intro: pfixLe_trans prefix_imp_pfixLe)
done

lemma Follows_LeadsTo_pfixGe:
     "F : f Fols g ==> F : {s. k pfixGe g s} LeadsTo {s. k pfixGe f s}"
apply (rule single_LeadsTo_I, clarify)
apply (drule_tac k="g s" in Follows_LeadsTo)
apply (erule LeadsTo_weaken)
 apply blast 
apply (blast intro: pfixGe_trans prefix_imp_pfixGe)
done


lemma Always_Follows1: 
     "[| F : Always {s. f s = f' s}; F : f Fols g |] ==> F : f' Fols g"

apply (unfold Follows_def Increasing_def Stable_def, auto)
apply (erule_tac [3] Always_LeadsTo_weaken)
apply (erule_tac A = "{s. z <= f s}" and A' = "{s. z <= f s}" in Always_Constrains_weaken, auto)
apply (drule Always_Int_I, assumption)
apply (force intro: Always_weaken)
done

lemma Always_Follows2: 
     "[| F : Always {s. g s = g' s}; F : f Fols g |] ==> F : f Fols g'"
apply (unfold Follows_def Increasing_def Stable_def, auto)
apply (erule_tac [3] Always_LeadsTo_weaken)
apply (erule_tac A = "{s. z <= g s}" and A' = "{s. z <= g s}" in Always_Constrains_weaken, auto)
apply (drule Always_Int_I, assumption)
apply (force intro: Always_weaken)
done


(** Union properties (with the subset ordering) **)

(*Can replace "Un" by any sup.  But existing max only works for linorders.*)
lemma increasing_Un: 
    "[| F : increasing f;  F: increasing g |]  
     ==> F : increasing (%s. (f s) Un (g s))"
apply (unfold increasing_def stable_def constrains_def, auto)
apply (drule_tac x = "f xa" in spec)
apply (drule_tac x = "g xa" in spec)
apply (blast dest!: bspec)
done

lemma Increasing_Un: 
    "[| F : Increasing f;  F: Increasing g |]  
     ==> F : Increasing (%s. (f s) Un (g s))"
apply (unfold Increasing_def Stable_def Constrains_def stable_def constrains_def, auto)
apply (drule_tac x = "f xa" in spec)
apply (drule_tac x = "g xa" in spec)
apply (blast dest!: bspec)
done


lemma Always_Un:
     "[| F : Always {s. f' s <= f s}; F : Always {s. g' s <= g s} |]  
      ==> F : Always {s. f' s Un g' s <= f s Un g s}"
apply (simp add: Always_eq_includes_reachable, blast)
done

(*Lemma to re-use the argument that one variable increases (progress)
  while the other variable doesn't decrease (safety)*)
lemma Follows_Un_lemma:
     "[| F : Increasing f; F : Increasing g;  
         F : Increasing g'; F : Always {s. f' s <= f s}; 
         ALL k. F : {s. k <= f s} LeadsTo {s. k <= f' s} |] 
      ==> F : {s. k <= f s Un g s} LeadsTo {s. k <= f' s Un g s}"
apply (rule single_LeadsTo_I)
apply (drule_tac x = "f s" in IncreasingD)
apply (drule_tac x = "g s" in IncreasingD)
apply (rule LeadsTo_weaken)
apply (rule PSP_Stable)
apply (erule_tac x = "f s" in spec)
apply (erule Stable_Int, assumption)
apply blast
apply blast
done

lemma Follows_Un: 
    "[| F : f' Fols f;  F: g' Fols g |]  
     ==> F : (%s. (f' s) Un (g' s)) Fols (%s. (f s) Un (g s))"
apply (unfold Follows_def)
apply (simp add: Increasing_Un Always_Un, auto)
apply (rule LeadsTo_Trans)
apply (blast intro: Follows_Un_lemma)
(*Weakening is used to exchange Un's arguments*)
apply (blast intro: Follows_Un_lemma [THEN LeadsTo_weaken])
done


(** Multiset union properties (with the multiset ordering) **)

lemma increasing_union: 
    "[| F : increasing f;  F: increasing g |]  
     ==> F : increasing (%s. (f s) + (g s :: ('a::order) multiset))"

apply (unfold increasing_def stable_def constrains_def, auto)
apply (drule_tac x = "f xa" in spec)
apply (drule_tac x = "g xa" in spec)
apply (drule bspec, assumption) 
apply (blast intro: union_le_mono order_trans)
done

lemma Increasing_union: 
    "[| F : Increasing f;  F: Increasing g |]  
     ==> F : Increasing (%s. (f s) + (g s :: ('a::order) multiset))"
apply (unfold Increasing_def Stable_def Constrains_def stable_def constrains_def, auto)
apply (drule_tac x = "f xa" in spec)
apply (drule_tac x = "g xa" in spec)
apply (drule bspec, assumption) 
apply (blast intro: union_le_mono order_trans)
done

lemma Always_union:
     "[| F : Always {s. f' s <= f s}; F : Always {s. g' s <= g s} |]  
      ==> F : Always {s. f' s + g' s <= f s + (g s :: ('a::order) multiset)}"
apply (simp add: Always_eq_includes_reachable)
apply (blast intro: union_le_mono)
done

(*Except the last line, IDENTICAL to the proof script for Follows_Un_lemma*)
lemma Follows_union_lemma:
     "[| F : Increasing f; F : Increasing g;  
         F : Increasing g'; F : Always {s. f' s <= f s}; 
         ALL k::('a::order) multiset.  
           F : {s. k <= f s} LeadsTo {s. k <= f' s} |] 
      ==> F : {s. k <= f s + g s} LeadsTo {s. k <= f' s + g s}"
apply (rule single_LeadsTo_I)
apply (drule_tac x = "f s" in IncreasingD)
apply (drule_tac x = "g s" in IncreasingD)
apply (rule LeadsTo_weaken)
apply (rule PSP_Stable)
apply (erule_tac x = "f s" in spec)
apply (erule Stable_Int, assumption)
apply blast
apply (blast intro: union_le_mono order_trans)
done

(*The !! is there to influence to effect of permutative rewriting at the end*)
lemma Follows_union: 
     "!!g g' ::'b => ('a::order) multiset.  
        [| F : f' Fols f;  F: g' Fols g |]  
        ==> F : (%s. (f' s) + (g' s)) Fols (%s. (f s) + (g s))"
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
        [| ALL i: I. F : f' i Fols f i;  finite I |]  
        ==> F : (%s. \<Sum>i:I. f' i s) Fols (%s. \<Sum>i:I. f i s)"
apply (erule rev_mp)
apply (erule finite_induct, simp) 
apply (simp add: Follows_union)
done


(*Currently UNUSED, but possibly of interest*)
lemma Increasing_imp_Stable_pfixGe:
     "F : Increasing func ==> F : Stable {s. h pfixGe (func s)}"
apply (simp add: Increasing_def Stable_def Constrains_def constrains_def)
apply (blast intro: trans_Ge [THEN trans_genPrefix, THEN transD] 
                    prefix_imp_pfixGe)
done

(*Currently UNUSED, but possibly of interest*)
lemma LeadsTo_le_imp_pfixGe:
     "ALL z. F : {s. z <= f s} LeadsTo {s. z <= g s}  
      ==> F : {s. z pfixGe f s} LeadsTo {s. z pfixGe g s}"
apply (rule single_LeadsTo_I)
apply (drule_tac x = "f s" in spec)
apply (erule LeadsTo_weaken)
 prefer 2
 apply (blast intro: trans_Ge [THEN trans_genPrefix, THEN transD] 
                     prefix_imp_pfixGe, blast)
done

end
