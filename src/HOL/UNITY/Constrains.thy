(*  Title:      HOL/UNITY/Constrains
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

Weak safety relations: restricted to the set of reachable states.
*)

header{*Weak Safety*}

theory Constrains = UNITY:

consts traces :: "['a set, ('a * 'a)set set] => ('a * 'a list) set"

  (*Initial states and program => (final state, reversed trace to it)...
    Arguments MUST be curried in an inductive definition*)

inductive "traces init acts"  
  intros 
         (*Initial trace is empty*)
    Init:  "s \<in> init ==> (s,[]) \<in> traces init acts"

    Acts:  "[| act: acts;  (s,evs) \<in> traces init acts;  (s,s'): act |]
	    ==> (s', s#evs) \<in> traces init acts"


consts reachable :: "'a program => 'a set"

inductive "reachable F"
  intros 
    Init:  "s \<in> Init F ==> s \<in> reachable F"

    Acts:  "[| act: Acts F;  s \<in> reachable F;  (s,s'): act |]
	    ==> s' \<in> reachable F"

constdefs
  Constrains :: "['a set, 'a set] => 'a program set"  (infixl "Co" 60)
    "A Co B == {F. F \<in> (reachable F \<inter> A)  co  B}"

  Unless  :: "['a set, 'a set] => 'a program set"     (infixl "Unless" 60)
    "A Unless B == (A-B) Co (A \<union> B)"

  Stable     :: "'a set => 'a program set"
    "Stable A == A Co A"

  (*Always is the weak form of "invariant"*)
  Always :: "'a set => 'a program set"
    "Always A == {F. Init F \<subseteq> A} \<inter> Stable A"

  (*Polymorphic in both states and the meaning of \<le> *)
  Increasing :: "['a => 'b::{order}] => 'a program set"
    "Increasing f == \<Inter>z. Stable {s. z \<le> f s}"


subsection{*traces and reachable*}

lemma reachable_equiv_traces:
     "reachable F = {s. \<exists>evs. (s,evs): traces (Init F) (Acts F)}"
apply safe
apply (erule_tac [2] traces.induct)
apply (erule reachable.induct)
apply (blast intro: reachable.intros traces.intros)+
done

lemma Init_subset_reachable: "Init F \<subseteq> reachable F"
by (blast intro: reachable.intros)

lemma stable_reachable [intro!,simp]:
     "Acts G \<subseteq> Acts F ==> G \<in> stable (reachable F)"
by (blast intro: stableI constrainsI reachable.intros)

(*The set of all reachable states is an invariant...*)
lemma invariant_reachable: "F \<in> invariant (reachable F)"
apply (simp add: invariant_def)
apply (blast intro: reachable.intros)
done

(*...in fact the strongest invariant!*)
lemma invariant_includes_reachable: "F \<in> invariant A ==> reachable F \<subseteq> A"
apply (simp add: stable_def constrains_def invariant_def)
apply (rule subsetI)
apply (erule reachable.induct)
apply (blast intro: reachable.intros)+
done


subsection{*Co*}

(*F \<in> B co B' ==> F \<in> (reachable F \<inter> B) co (reachable F \<inter> B')*)
lemmas constrains_reachable_Int =  
    subset_refl [THEN stable_reachable [unfolded stable_def], 
                 THEN constrains_Int, standard]

(*Resembles the previous definition of Constrains*)
lemma Constrains_eq_constrains: 
     "A Co B = {F. F \<in> (reachable F  \<inter>  A) co (reachable F  \<inter>  B)}"
apply (unfold Constrains_def)
apply (blast dest: constrains_reachable_Int intro: constrains_weaken)
done

lemma constrains_imp_Constrains: "F \<in> A co A' ==> F \<in> A Co A'"
apply (unfold Constrains_def)
apply (blast intro: constrains_weaken_L)
done

lemma stable_imp_Stable: "F \<in> stable A ==> F \<in> Stable A"
apply (unfold stable_def Stable_def)
apply (erule constrains_imp_Constrains)
done

lemma ConstrainsI: 
    "(!!act s s'. [| act: Acts F;  (s,s') \<in> act;  s \<in> A |] ==> s': A')  
     ==> F \<in> A Co A'"
apply (rule constrains_imp_Constrains)
apply (blast intro: constrainsI)
done

lemma Constrains_empty [iff]: "F \<in> {} Co B"
by (unfold Constrains_def constrains_def, blast)

lemma Constrains_UNIV [iff]: "F \<in> A Co UNIV"
by (blast intro: ConstrainsI)

lemma Constrains_weaken_R: 
    "[| F \<in> A Co A'; A'<=B' |] ==> F \<in> A Co B'"
apply (unfold Constrains_def)
apply (blast intro: constrains_weaken_R)
done

lemma Constrains_weaken_L: 
    "[| F \<in> A Co A'; B \<subseteq> A |] ==> F \<in> B Co A'"
apply (unfold Constrains_def)
apply (blast intro: constrains_weaken_L)
done

lemma Constrains_weaken: 
   "[| F \<in> A Co A'; B \<subseteq> A; A'<=B' |] ==> F \<in> B Co B'"
apply (unfold Constrains_def)
apply (blast intro: constrains_weaken)
done

(** Union **)

lemma Constrains_Un: 
    "[| F \<in> A Co A'; F \<in> B Co B' |] ==> F \<in> (A \<union> B) Co (A' \<union> B')"
apply (unfold Constrains_def)
apply (blast intro: constrains_Un [THEN constrains_weaken])
done

lemma Constrains_UN: 
  assumes Co: "!!i. i \<in> I ==> F \<in> (A i) Co (A' i)"
  shows "F \<in> (\<Union>i \<in> I. A i) Co (\<Union>i \<in> I. A' i)"
apply (unfold Constrains_def)
apply (rule CollectI)
apply (rule Co [unfolded Constrains_def, THEN CollectD, THEN constrains_UN, 
                THEN constrains_weaken],   auto)
done

(** Intersection **)

lemma Constrains_Int: 
    "[| F \<in> A Co A'; F \<in> B Co B' |] ==> F \<in> (A \<inter> B) Co (A' \<inter> B')"
apply (unfold Constrains_def)
apply (blast intro: constrains_Int [THEN constrains_weaken])
done

lemma Constrains_INT: 
  assumes Co: "!!i. i \<in> I ==> F \<in> (A i) Co (A' i)"
  shows "F \<in> (\<Inter>i \<in> I. A i) Co (\<Inter>i \<in> I. A' i)"
apply (unfold Constrains_def)
apply (rule CollectI)
apply (rule Co [unfolded Constrains_def, THEN CollectD, THEN constrains_INT, 
                THEN constrains_weaken],   auto)
done

lemma Constrains_imp_subset: "F \<in> A Co A' ==> reachable F \<inter> A \<subseteq> A'"
by (simp add: constrains_imp_subset Constrains_def)

lemma Constrains_trans: "[| F \<in> A Co B; F \<in> B Co C |] ==> F \<in> A Co C"
apply (simp add: Constrains_eq_constrains)
apply (blast intro: constrains_trans constrains_weaken)
done

lemma Constrains_cancel:
     "[| F \<in> A Co (A' \<union> B); F \<in> B Co B' |] ==> F \<in> A Co (A' \<union> B')"
by (simp add: Constrains_eq_constrains constrains_def, blast)


subsection{*Stable*}

(*Useful because there's no Stable_weaken.  [Tanja Vos]*)
lemma Stable_eq: "[| F \<in> Stable A; A = B |] ==> F \<in> Stable B"
by blast

lemma Stable_eq_stable: "(F \<in> Stable A) = (F \<in> stable (reachable F \<inter> A))"
by (simp add: Stable_def Constrains_eq_constrains stable_def)

lemma StableI: "F \<in> A Co A ==> F \<in> Stable A"
by (unfold Stable_def, assumption)

lemma StableD: "F \<in> Stable A ==> F \<in> A Co A"
by (unfold Stable_def, assumption)

lemma Stable_Un: 
    "[| F \<in> Stable A; F \<in> Stable A' |] ==> F \<in> Stable (A \<union> A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Un)
done

lemma Stable_Int: 
    "[| F \<in> Stable A; F \<in> Stable A' |] ==> F \<in> Stable (A \<inter> A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Int)
done

lemma Stable_Constrains_Un: 
    "[| F \<in> Stable C; F \<in> A Co (C \<union> A') |]    
     ==> F \<in> (C \<union> A) Co (C \<union> A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Un [THEN Constrains_weaken])
done

lemma Stable_Constrains_Int: 
    "[| F \<in> Stable C; F \<in> (C \<inter> A) Co A' |]    
     ==> F \<in> (C \<inter> A) Co (C \<inter> A')"
apply (unfold Stable_def)
apply (blast intro: Constrains_Int [THEN Constrains_weaken])
done

lemma Stable_UN: 
    "(!!i. i \<in> I ==> F \<in> Stable (A i)) ==> F \<in> Stable (\<Union>i \<in> I. A i)"
by (simp add: Stable_def Constrains_UN) 

lemma Stable_INT: 
    "(!!i. i \<in> I ==> F \<in> Stable (A i)) ==> F \<in> Stable (\<Inter>i \<in> I. A i)"
by (simp add: Stable_def Constrains_INT) 

lemma Stable_reachable: "F \<in> Stable (reachable F)"
by (simp add: Stable_eq_stable)



subsection{*Increasing*}

lemma IncreasingD: 
     "F \<in> Increasing f ==> F \<in> Stable {s. x \<le> f s}"
by (unfold Increasing_def, blast)

lemma mono_Increasing_o: 
     "mono g ==> Increasing f \<subseteq> Increasing (g o f)"
apply (simp add: Increasing_def Stable_def Constrains_def stable_def 
                 constrains_def)
apply (blast intro: monoD order_trans)
done

lemma strict_IncreasingD: 
     "!!z::nat. F \<in> Increasing f ==> F \<in> Stable {s. z < f s}"
by (simp add: Increasing_def Suc_le_eq [symmetric])

lemma increasing_imp_Increasing: 
     "F \<in> increasing f ==> F \<in> Increasing f"
apply (unfold increasing_def Increasing_def)
apply (blast intro: stable_imp_Stable)
done

lemmas Increasing_constant =  
    increasing_constant [THEN increasing_imp_Increasing, standard, iff]


subsection{*The Elimination Theorem*}

(*The "free" m has become universally quantified! Should the premise be !!m
instead of \<forall>m ?  Would make it harder to use in forward proof.*)

lemma Elimination: 
    "[| \<forall>m. F \<in> {s. s x = m} Co (B m) |]  
     ==> F \<in> {s. s x \<in> M} Co (\<Union>m \<in> M. B m)"
by (unfold Constrains_def constrains_def, blast)

(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
lemma Elimination_sing: 
    "(\<forall>m. F \<in> {m} Co (B m)) ==> F \<in> M Co (\<Union>m \<in> M. B m)"
by (unfold Constrains_def constrains_def, blast)


subsection{*Specialized laws for handling Always*}

(** Natural deduction rules for "Always A" **)

lemma AlwaysI: "[| Init F \<subseteq> A;  F \<in> Stable A |] ==> F \<in> Always A"
by (simp add: Always_def)

lemma AlwaysD: "F \<in> Always A ==> Init F \<subseteq> A & F \<in> Stable A"
by (simp add: Always_def)

lemmas AlwaysE = AlwaysD [THEN conjE, standard]
lemmas Always_imp_Stable = AlwaysD [THEN conjunct2, standard]


(*The set of all reachable states is Always*)
lemma Always_includes_reachable: "F \<in> Always A ==> reachable F \<subseteq> A"
apply (simp add: Stable_def Constrains_def constrains_def Always_def)
apply (rule subsetI)
apply (erule reachable.induct)
apply (blast intro: reachable.intros)+
done

lemma invariant_imp_Always: 
     "F \<in> invariant A ==> F \<in> Always A"
apply (unfold Always_def invariant_def Stable_def stable_def)
apply (blast intro: constrains_imp_Constrains)
done

lemmas Always_reachable =
    invariant_reachable [THEN invariant_imp_Always, standard]

lemma Always_eq_invariant_reachable:
     "Always A = {F. F \<in> invariant (reachable F \<inter> A)}"
apply (simp add: Always_def invariant_def Stable_def Constrains_eq_constrains
                 stable_def)
apply (blast intro: reachable.intros)
done

(*the RHS is the traditional definition of the "always" operator*)
lemma Always_eq_includes_reachable: "Always A = {F. reachable F \<subseteq> A}"
by (auto dest: invariant_includes_reachable simp add: Int_absorb2 invariant_reachable Always_eq_invariant_reachable)

lemma Always_UNIV_eq [simp]: "Always UNIV = UNIV"
by (auto simp add: Always_eq_includes_reachable)

lemma UNIV_AlwaysI: "UNIV \<subseteq> A ==> F \<in> Always A"
by (auto simp add: Always_eq_includes_reachable)

lemma Always_eq_UN_invariant: "Always A = (\<Union>I \<in> Pow A. invariant I)"
apply (simp add: Always_eq_includes_reachable)
apply (blast intro: invariantI Init_subset_reachable [THEN subsetD] 
                    invariant_includes_reachable [THEN subsetD])
done

lemma Always_weaken: "[| F \<in> Always A; A \<subseteq> B |] ==> F \<in> Always B"
by (auto simp add: Always_eq_includes_reachable)


subsection{*"Co" rules involving Always*}

lemma Always_Constrains_pre:
     "F \<in> Always INV ==> (F \<in> (INV \<inter> A) Co A') = (F \<in> A Co A')"
by (simp add: Always_includes_reachable [THEN Int_absorb2] Constrains_def 
              Int_assoc [symmetric])

lemma Always_Constrains_post:
     "F \<in> Always INV ==> (F \<in> A Co (INV \<inter> A')) = (F \<in> A Co A')"
by (simp add: Always_includes_reachable [THEN Int_absorb2] 
              Constrains_eq_constrains Int_assoc [symmetric])

(* [| F \<in> Always INV;  F \<in> (INV \<inter> A) Co A' |] ==> F \<in> A Co A' *)
lemmas Always_ConstrainsI = Always_Constrains_pre [THEN iffD1, standard]

(* [| F \<in> Always INV;  F \<in> A Co A' |] ==> F \<in> A Co (INV \<inter> A') *)
lemmas Always_ConstrainsD = Always_Constrains_post [THEN iffD2, standard]

(*The analogous proof of Always_LeadsTo_weaken doesn't terminate*)
lemma Always_Constrains_weaken:
     "[| F \<in> Always C;  F \<in> A Co A';    
         C \<inter> B \<subseteq> A;   C \<inter> A' \<subseteq> B' |]  
      ==> F \<in> B Co B'"
apply (rule Always_ConstrainsI, assumption)
apply (drule Always_ConstrainsD, assumption)
apply (blast intro: Constrains_weaken)
done


(** Conjoining Always properties **)

lemma Always_Int_distrib: "Always (A \<inter> B) = Always A \<inter> Always B"
by (auto simp add: Always_eq_includes_reachable)

lemma Always_INT_distrib: "Always (INTER I A) = (\<Inter>i \<in> I. Always (A i))"
by (auto simp add: Always_eq_includes_reachable)

lemma Always_Int_I:
     "[| F \<in> Always A;  F \<in> Always B |] ==> F \<in> Always (A \<inter> B)"
by (simp add: Always_Int_distrib)

(*Allows a kind of "implication introduction"*)
lemma Always_Compl_Un_eq:
     "F \<in> Always A ==> (F \<in> Always (-A \<union> B)) = (F \<in> Always B)"
by (auto simp add: Always_eq_includes_reachable)

(*Delete the nearest invariance assumption (which will be the second one
  used by Always_Int_I) *)
lemmas Always_thin = thin_rl [of "F \<in> Always A", standard]

end
