(*  Title:      HOL/UNITY/Constrains
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak safety relations: restricted to the set of reachable states.
*)

theory Constrains = UNITY:

consts traces :: "['a set, ('a * 'a)set set] => ('a * 'a list) set"

  (*Initial states and program => (final state, reversed trace to it)...
    Arguments MUST be curried in an inductive definition*)

inductive "traces init acts"  
  intros 
         (*Initial trace is empty*)
    Init:  "s: init ==> (s,[]) : traces init acts"

    Acts:  "[| act: acts;  (s,evs) : traces init acts;  (s,s'): act |]
	    ==> (s', s#evs) : traces init acts"


consts reachable :: "'a program => 'a set"

inductive "reachable F"
  intros 
    Init:  "s: Init F ==> s : reachable F"

    Acts:  "[| act: Acts F;  s : reachable F;  (s,s'): act |]
	    ==> s' : reachable F"

constdefs
  Constrains :: "['a set, 'a set] => 'a program set"  (infixl "Co" 60)
    "A Co B == {F. F : (reachable F Int A)  co  B}"

  Unless  :: "['a set, 'a set] => 'a program set"     (infixl "Unless" 60)
    "A Unless B == (A-B) Co (A Un B)"

  Stable     :: "'a set => 'a program set"
    "Stable A == A Co A"

  (*Always is the weak form of "invariant"*)
  Always :: "'a set => 'a program set"
    "Always A == {F. Init F <= A} Int Stable A"

  (*Polymorphic in both states and the meaning of <= *)
  Increasing :: "['a => 'b::{order}] => 'a program set"
    "Increasing f == INT z. Stable {s. z <= f s}"


(*** traces and reachable ***)

lemma reachable_equiv_traces:
     "reachable F = {s. EX evs. (s,evs): traces (Init F) (Acts F)}"
apply safe
apply (erule_tac [2] traces.induct)
apply (erule reachable.induct)
apply (blast intro: reachable.intros traces.intros)+
done

lemma Init_subset_reachable: "Init F <= reachable F"
by (blast intro: reachable.intros)

lemma stable_reachable [intro!,simp]:
     "Acts G <= Acts F ==> G : stable (reachable F)"
by (blast intro: stableI constrainsI reachable.intros)

(*The set of all reachable states is an invariant...*)
lemma invariant_reachable: "F : invariant (reachable F)"
apply (simp add: invariant_def)
apply (blast intro: reachable.intros)
done

(*...in fact the strongest invariant!*)
lemma invariant_includes_reachable: "F : invariant A ==> reachable F <= A"
apply (simp add: stable_def constrains_def invariant_def)
apply (rule subsetI)
apply (erule reachable.induct)
apply (blast intro: reachable.intros)+
done


(*** Co ***)

(*F : B co B' ==> F : (reachable F Int B) co (reachable F Int B')*)
lemmas constrains_reachable_Int =  
    subset_refl [THEN stable_reachable [unfolded stable_def], 
                 THEN constrains_Int, standard]

(*Resembles the previous definition of Constrains*)
lemma Constrains_eq_constrains: 
     "A Co B = {F. F : (reachable F  Int  A) co (reachable F  Int  B)}"
apply (unfold Constrains_def)
apply (blast dest: constrains_reachable_Int intro: constrains_weaken)
done

lemma constrains_imp_Constrains: "F : A co A' ==> F : A Co A'"
apply (unfold Constrains_def)
apply (blast intro: constrains_weaken_L)
done

lemma stable_imp_Stable: "F : stable A ==> F : Stable A"
apply (unfold stable_def Stable_def)
apply (erule constrains_imp_Constrains)
done

lemma ConstrainsI: 
    "(!!act s s'. [| act: Acts F;  (s,s') : act;  s: A |] ==> s': A')  
     ==> F : A Co A'"
apply (rule constrains_imp_Constrains)
apply (blast intro: constrainsI)
done

lemma Constrains_empty [iff]: "F : {} Co B"
by (unfold Constrains_def constrains_def, blast)

lemma Constrains_UNIV [iff]: "F : A Co UNIV"
by (blast intro: ConstrainsI)

lemma Constrains_weaken_R: 
    "[| F : A Co A'; A'<=B' |] ==> F : A Co B'"
apply (unfold Constrains_def)
apply (blast intro: constrains_weaken_R)
done

lemma Constrains_weaken_L: 
    "[| F : A Co A'; B<=A |] ==> F : B Co A'"
apply (unfold Constrains_def)
apply (blast intro: constrains_weaken_L)
done

lemma Constrains_weaken: 
   "[| F : A Co A'; B<=A; A'<=B' |] ==> F : B Co B'"
apply (unfold Constrains_def)
apply (blast intro: constrains_weaken)
done

(** Union **)

lemma Constrains_Un: 
    "[| F : A Co A'; F : B Co B' |] ==> F : (A Un B) Co (A' Un B')"
apply (unfold Constrains_def)
apply (blast intro: constrains_Un [THEN constrains_weaken])
done

lemma Constrains_UN: 
  assumes Co: "!!i. i:I ==> F : (A i) Co (A' i)"
  shows "F : (UN i:I. A i) Co (UN i:I. A' i)"
apply (unfold Constrains_def)
apply (rule CollectI)
apply (rule Co [unfolded Constrains_def, THEN CollectD, THEN constrains_UN, 
                THEN constrains_weaken],   auto)
done

(** Intersection **)

lemma Constrains_Int: 
    "[| F : A Co A'; F : B Co B' |] ==> F : (A Int B) Co (A' Int B')"
apply (unfold Constrains_def)
apply (blast intro: constrains_Int [THEN constrains_weaken])
done

lemma Constrains_INT: 
  assumes Co: "!!i. i:I ==> F : (A i) Co (A' i)"
  shows "F : (INT i:I. A i) Co (INT i:I. A' i)"
apply (unfold Constrains_def)
apply (rule CollectI)
apply (rule Co [unfolded Constrains_def, THEN CollectD, THEN constrains_INT, 
                THEN constrains_weaken],   auto)
done

lemma Constrains_imp_subset: "F : A Co A' ==> reachable F Int A <= A'"
by (simp add: constrains_imp_subset Constrains_def)

lemma Constrains_trans: "[| F : A Co B; F : B Co C |] ==> F : A Co C"
apply (simp add: Constrains_eq_constrains)
apply (blast intro: constrains_trans constrains_weaken)
done

lemma Constrains_cancel:
     "[| F : A Co (A' Un B); F : B Co B' |] ==> F : A Co (A' Un B')"
by (simp add: Constrains_eq_constrains constrains_def, blast)


(*** Stable ***)

(*Useful because there's no Stable_weaken.  [Tanja Vos]*)
lemma Stable_eq: "[| F: Stable A; A = B |] ==> F : Stable B"
by blast

lemma Stable_eq_stable: "(F : Stable A) = (F : stable (reachable F Int A))"
by (simp add: Stable_def Constrains_eq_constrains stable_def)

lemma StableI: "F : A Co A ==> F : Stable A"
by (unfold Stable_def, assumption)

lemma StableD: "F : Stable A ==> F : A Co A"
by (unfold Stable_def, assumption)

lemma Stable_Un: 
    "[| F : Stable A; F : Stable A' |] ==> F : Stable (A Un A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Un)
done

lemma Stable_Int: 
    "[| F : Stable A; F : Stable A' |] ==> F : Stable (A Int A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Int)
done

lemma Stable_Constrains_Un: 
    "[| F : Stable C; F : A Co (C Un A') |]    
     ==> F : (C Un A) Co (C Un A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Un [THEN Constrains_weaken])
done

lemma Stable_Constrains_Int: 
    "[| F : Stable C; F : (C Int A) Co A' |]    
     ==> F : (C Int A) Co (C Int A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Int [THEN Constrains_weaken])
done

lemma Stable_UN: 
    "(!!i. i:I ==> F : Stable (A i)) ==> F : Stable (UN i:I. A i)"
by (simp add: Stable_def Constrains_UN) 

lemma Stable_INT: 
    "(!!i. i:I ==> F : Stable (A i)) ==> F : Stable (INT i:I. A i)"
by (simp add: Stable_def Constrains_INT) 

lemma Stable_reachable: "F : Stable (reachable F)"
by (simp add: Stable_eq_stable)



(*** Increasing ***)

lemma IncreasingD: 
     "F : Increasing f ==> F : Stable {s. x <= f s}"
by (unfold Increasing_def, blast)

lemma mono_Increasing_o: 
     "mono g ==> Increasing f <= Increasing (g o f)"
apply (simp add: Increasing_def Stable_def Constrains_def stable_def 
                 constrains_def)
apply (blast intro: monoD order_trans)
done

lemma strict_IncreasingD: 
     "!!z::nat. F : Increasing f ==> F: Stable {s. z < f s}"
by (simp add: Increasing_def Suc_le_eq [symmetric])

lemma increasing_imp_Increasing: 
     "F : increasing f ==> F : Increasing f"
apply (unfold increasing_def Increasing_def)
apply (blast intro: stable_imp_Stable)
done

lemmas Increasing_constant =  
    increasing_constant [THEN increasing_imp_Increasing, standard, iff]


(*** The Elimination Theorem.  The "free" m has become universally quantified!
     Should the premise be !!m instead of ALL m ?  Would make it harder to use
     in forward proof. ***)

lemma Elimination: 
    "[| ALL m. F : {s. s x = m} Co (B m) |]  
     ==> F : {s. s x : M} Co (UN m:M. B m)"

by (unfold Constrains_def constrains_def, blast)

(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
lemma Elimination_sing: 
    "(ALL m. F : {m} Co (B m)) ==> F : M Co (UN m:M. B m)"
by (unfold Constrains_def constrains_def, blast)


(*** Specialized laws for handling Always ***)

(** Natural deduction rules for "Always A" **)

lemma AlwaysI: "[| Init F<=A;  F : Stable A |] ==> F : Always A"
by (simp add: Always_def)

lemma AlwaysD: "F : Always A ==> Init F<=A & F : Stable A"
by (simp add: Always_def)

lemmas AlwaysE = AlwaysD [THEN conjE, standard]
lemmas Always_imp_Stable = AlwaysD [THEN conjunct2, standard]


(*The set of all reachable states is Always*)
lemma Always_includes_reachable: "F : Always A ==> reachable F <= A"
apply (simp add: Stable_def Constrains_def constrains_def Always_def)
apply (rule subsetI)
apply (erule reachable.induct)
apply (blast intro: reachable.intros)+
done

lemma invariant_imp_Always: 
     "F : invariant A ==> F : Always A"
apply (unfold Always_def invariant_def Stable_def stable_def)
apply (blast intro: constrains_imp_Constrains)
done

lemmas Always_reachable =
    invariant_reachable [THEN invariant_imp_Always, standard]

lemma Always_eq_invariant_reachable:
     "Always A = {F. F : invariant (reachable F Int A)}"
apply (simp add: Always_def invariant_def Stable_def Constrains_eq_constrains
                 stable_def)
apply (blast intro: reachable.intros)
done

(*the RHS is the traditional definition of the "always" operator*)
lemma Always_eq_includes_reachable: "Always A = {F. reachable F <= A}"
by (auto dest: invariant_includes_reachable simp add: Int_absorb2 invariant_reachable Always_eq_invariant_reachable)

lemma Always_UNIV_eq [simp]: "Always UNIV = UNIV"
by (auto simp add: Always_eq_includes_reachable)

lemma UNIV_AlwaysI: "UNIV <= A ==> F : Always A"
by (auto simp add: Always_eq_includes_reachable)

lemma Always_eq_UN_invariant: "Always A = (UN I: Pow A. invariant I)"
apply (simp add: Always_eq_includes_reachable)
apply (blast intro: invariantI Init_subset_reachable [THEN subsetD] 
                    invariant_includes_reachable [THEN subsetD])
done

lemma Always_weaken: "[| F : Always A; A <= B |] ==> F : Always B"
by (auto simp add: Always_eq_includes_reachable)


(*** "Co" rules involving Always ***)

lemma Always_Constrains_pre:
     "F : Always INV ==> (F : (INV Int A) Co A') = (F : A Co A')"
by (simp add: Always_includes_reachable [THEN Int_absorb2] Constrains_def 
              Int_assoc [symmetric])

lemma Always_Constrains_post:
     "F : Always INV ==> (F : A Co (INV Int A')) = (F : A Co A')"
by (simp add: Always_includes_reachable [THEN Int_absorb2] 
              Constrains_eq_constrains Int_assoc [symmetric])

(* [| F : Always INV;  F : (INV Int A) Co A' |] ==> F : A Co A' *)
lemmas Always_ConstrainsI = Always_Constrains_pre [THEN iffD1, standard]

(* [| F : Always INV;  F : A Co A' |] ==> F : A Co (INV Int A') *)
lemmas Always_ConstrainsD = Always_Constrains_post [THEN iffD2, standard]

(*The analogous proof of Always_LeadsTo_weaken doesn't terminate*)
lemma Always_Constrains_weaken:
     "[| F : Always C;  F : A Co A';    
         C Int B <= A;   C Int A' <= B' |]  
      ==> F : B Co B'"
apply (rule Always_ConstrainsI, assumption)
apply (drule Always_ConstrainsD, assumption)
apply (blast intro: Constrains_weaken)
done


(** Conjoining Always properties **)

lemma Always_Int_distrib: "Always (A Int B) = Always A Int Always B"
by (auto simp add: Always_eq_includes_reachable)

lemma Always_INT_distrib: "Always (INTER I A) = (INT i:I. Always (A i))"
by (auto simp add: Always_eq_includes_reachable)

lemma Always_Int_I:
     "[| F : Always A;  F : Always B |] ==> F : Always (A Int B)"
by (simp add: Always_Int_distrib)

(*Allows a kind of "implication introduction"*)
lemma Always_Compl_Un_eq:
     "F : Always A ==> (F : Always (-A Un B)) = (F : Always B)"
by (auto simp add: Always_eq_includes_reachable)

(*Delete the nearest invariance assumption (which will be the second one
  used by Always_Int_I) *)
lemmas Always_thin = thin_rl [of "F : Always A", standard]

end
