(*  Title:      HOL/UNITY/UNITY
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The basic UNITY theory (revised version, based upon the "co" operator)

From Misra, "A Logic for Concurrent Programming", 1994
*)

theory UNITY = Main:

typedef (Program)
  'a program = "{(init:: 'a set, acts :: ('a * 'a)set set,
		   allowed :: ('a * 'a)set set). Id:acts & Id: allowed}" 
  by blast

constdefs
  constrains :: "['a set, 'a set] => 'a program set"  (infixl "co"     60)
    "A co B == {F. ALL act: Acts F. act``A <= B}"

  unless  :: "['a set, 'a set] => 'a program set"  (infixl "unless" 60)
    "A unless B == (A-B) co (A Un B)"

  mk_program :: "('a set * ('a * 'a)set set * ('a * 'a)set set)
		   => 'a program"
    "mk_program == %(init, acts, allowed).
                      Abs_Program (init, insert Id acts, insert Id allowed)"

  Init :: "'a program => 'a set"
    "Init F == (%(init, acts, allowed). init) (Rep_Program F)"

  Acts :: "'a program => ('a * 'a)set set"
    "Acts F == (%(init, acts, allowed). acts) (Rep_Program F)"

  AllowedActs :: "'a program => ('a * 'a)set set"
    "AllowedActs F == (%(init, acts, allowed). allowed) (Rep_Program F)"

  Allowed :: "'a program => 'a program set"
    "Allowed F == {G. Acts G <= AllowedActs F}"

  stable     :: "'a set => 'a program set"
    "stable A == A co A"

  strongest_rhs :: "['a program, 'a set] => 'a set"
    "strongest_rhs F A == Inter {B. F : A co B}"

  invariant :: "'a set => 'a program set"
    "invariant A == {F. Init F <= A} Int stable A"

  (*Polymorphic in both states and the meaning of <= *)
  increasing :: "['a => 'b::{order}] => 'a program set"
    "increasing f == INT z. stable {s. z <= f s}"


(*Perhaps equalities.ML shouldn't add this in the first place!*)
declare image_Collect [simp del]

(*** The abstract type of programs ***)

lemmas program_typedef =
     Rep_Program Rep_Program_inverse Abs_Program_inverse 
     Program_def Init_def Acts_def AllowedActs_def mk_program_def

lemma Id_in_Acts [iff]: "Id : Acts F"
apply (cut_tac x = F in Rep_Program)
apply (auto simp add: program_typedef) 
done

lemma insert_Id_Acts [iff]: "insert Id (Acts F) = Acts F"
by (simp add: insert_absorb Id_in_Acts)

lemma Id_in_AllowedActs [iff]: "Id : AllowedActs F"
apply (cut_tac x = F in Rep_Program)
apply (auto simp add: program_typedef) 
done

lemma insert_Id_AllowedActs [iff]: "insert Id (AllowedActs F) = AllowedActs F"
by (simp add: insert_absorb Id_in_AllowedActs)

(** Inspectors for type "program" **)

lemma Init_eq [simp]: "Init (mk_program (init,acts,allowed)) = init"
by (auto simp add: program_typedef)

lemma Acts_eq [simp]: "Acts (mk_program (init,acts,allowed)) = insert Id acts"
by (auto simp add: program_typedef)

lemma AllowedActs_eq [simp]:
     "AllowedActs (mk_program (init,acts,allowed)) = insert Id allowed"
by (auto simp add: program_typedef)

(** Equality for UNITY programs **)

lemma surjective_mk_program [simp]:
     "mk_program (Init F, Acts F, AllowedActs F) = F"
apply (cut_tac x = F in Rep_Program)
apply (auto simp add: program_typedef)
apply (drule_tac f = Abs_Program in arg_cong)+
apply (simp add: program_typedef insert_absorb)
done

lemma program_equalityI:
     "[| Init F = Init G; Acts F = Acts G; AllowedActs F = AllowedActs G |]  
      ==> F = G"
apply (rule_tac t = F in surjective_mk_program [THEN subst])
apply (rule_tac t = G in surjective_mk_program [THEN subst], simp)
done

lemma program_equalityE:
     "[| F = G;  
         [| Init F = Init G; Acts F = Acts G; AllowedActs F = AllowedActs G |] 
         ==> P |] ==> P"
by simp 

lemma program_equality_iff:
     "(F=G) =   
      (Init F = Init G & Acts F = Acts G &AllowedActs F = AllowedActs G)"
by (blast intro: program_equalityI program_equalityE)


(*** These rules allow "lazy" definition expansion 
     They avoid expanding the full program, which is a large expression
***)

lemma def_prg_Init: "F == mk_program (init,acts,allowed) ==> Init F = init"
by auto

lemma def_prg_Acts:
     "F == mk_program (init,acts,allowed) ==> Acts F = insert Id acts"
by auto

lemma def_prg_AllowedActs:
     "F == mk_program (init,acts,allowed)  
      ==> AllowedActs F = insert Id allowed"
by auto

(*The program is not expanded, but its Init and Acts are*)
lemma def_prg_simps:
    "[| F == mk_program (init,acts,allowed) |]  
     ==> Init F = init & Acts F = insert Id acts"
by simp

(*An action is expanded only if a pair of states is being tested against it*)
lemma def_act_simp:
     "[| act == {(s,s'). P s s'} |] ==> ((s,s') : act) = P s s'"
by auto

(*A set is expanded only if an element is being tested against it*)
lemma def_set_simp: "A == B ==> (x : A) = (x : B)"
by auto


(*** co ***)

lemma constrainsI: 
    "(!!act s s'. [| act: Acts F;  (s,s') : act;  s: A |] ==> s': A')  
     ==> F : A co A'"
by (simp add: constrains_def, blast)

lemma constrainsD: 
    "[| F : A co A'; act: Acts F;  (s,s'): act;  s: A |] ==> s': A'"
by (unfold constrains_def, blast)

lemma constrains_empty [iff]: "F : {} co B"
by (unfold constrains_def, blast)

lemma constrains_empty2 [iff]: "(F : A co {}) = (A={})"
by (unfold constrains_def, blast)

lemma constrains_UNIV [iff]: "(F : UNIV co B) = (B = UNIV)"
by (unfold constrains_def, blast)

lemma constrains_UNIV2 [iff]: "F : A co UNIV"
by (unfold constrains_def, blast)

(*monotonic in 2nd argument*)
lemma constrains_weaken_R: 
    "[| F : A co A'; A'<=B' |] ==> F : A co B'"
by (unfold constrains_def, blast)

(*anti-monotonic in 1st argument*)
lemma constrains_weaken_L: 
    "[| F : A co A'; B<=A |] ==> F : B co A'"
by (unfold constrains_def, blast)

lemma constrains_weaken: 
   "[| F : A co A'; B<=A; A'<=B' |] ==> F : B co B'"
by (unfold constrains_def, blast)

(** Union **)

lemma constrains_Un: 
    "[| F : A co A'; F : B co B' |] ==> F : (A Un B) co (A' Un B')"
by (unfold constrains_def, blast)

lemma constrains_UN: 
    "(!!i. i:I ==> F : (A i) co (A' i)) 
     ==> F : (UN i:I. A i) co (UN i:I. A' i)"
by (unfold constrains_def, blast)

lemma constrains_Un_distrib: "(A Un B) co C = (A co C) Int (B co C)"
by (unfold constrains_def, blast)

lemma constrains_UN_distrib: "(UN i:I. A i) co B = (INT i:I. A i co B)"
by (unfold constrains_def, blast)

lemma constrains_Int_distrib: "C co (A Int B) = (C co A) Int (C co B)"
by (unfold constrains_def, blast)

lemma constrains_INT_distrib: "A co (INT i:I. B i) = (INT i:I. A co B i)"
by (unfold constrains_def, blast)

(** Intersection **)

lemma constrains_Int: 
    "[| F : A co A'; F : B co B' |] ==> F : (A Int B) co (A' Int B')"
by (unfold constrains_def, blast)

lemma constrains_INT: 
    "(!!i. i:I ==> F : (A i) co (A' i)) 
     ==> F : (INT i:I. A i) co (INT i:I. A' i)"
by (unfold constrains_def, blast)

lemma constrains_imp_subset: "F : A co A' ==> A <= A'"
by (unfold constrains_def, auto)

(*The reasoning is by subsets since "co" refers to single actions
  only.  So this rule isn't that useful.*)
lemma constrains_trans: 
    "[| F : A co B; F : B co C |] ==> F : A co C"
by (unfold constrains_def, blast)

lemma constrains_cancel: 
   "[| F : A co (A' Un B); F : B co B' |] ==> F : A co (A' Un B')"
by (unfold constrains_def, clarify, blast)


(*** unless ***)

lemma unlessI: "F : (A-B) co (A Un B) ==> F : A unless B"
by (unfold unless_def, assumption)

lemma unlessD: "F : A unless B ==> F : (A-B) co (A Un B)"
by (unfold unless_def, assumption)


(*** stable ***)

lemma stableI: "F : A co A ==> F : stable A"
by (unfold stable_def, assumption)

lemma stableD: "F : stable A ==> F : A co A"
by (unfold stable_def, assumption)

lemma stable_UNIV [simp]: "stable UNIV = UNIV"
by (unfold stable_def constrains_def, auto)

(** Union **)

lemma stable_Un: 
    "[| F : stable A; F : stable A' |] ==> F : stable (A Un A')"

apply (unfold stable_def)
apply (blast intro: constrains_Un)
done

lemma stable_UN: 
    "(!!i. i:I ==> F : stable (A i)) ==> F : stable (UN i:I. A i)"
apply (unfold stable_def)
apply (blast intro: constrains_UN)
done

(** Intersection **)

lemma stable_Int: 
    "[| F : stable A;  F : stable A' |] ==> F : stable (A Int A')"
apply (unfold stable_def)
apply (blast intro: constrains_Int)
done

lemma stable_INT: 
    "(!!i. i:I ==> F : stable (A i)) ==> F : stable (INT i:I. A i)"
apply (unfold stable_def)
apply (blast intro: constrains_INT)
done

lemma stable_constrains_Un: 
    "[| F : stable C; F : A co (C Un A') |] ==> F : (C Un A) co (C Un A')"
by (unfold stable_def constrains_def, blast)

lemma stable_constrains_Int: 
  "[| F : stable C; F :  (C Int A) co A' |] ==> F : (C Int A) co (C Int A')"
by (unfold stable_def constrains_def, blast)

(*[| F : stable C; F :  (C Int A) co A |] ==> F : stable (C Int A) *)
lemmas stable_constrains_stable = stable_constrains_Int [THEN stableI, standard]


(*** invariant ***)

lemma invariantI: "[| Init F<=A;  F: stable A |] ==> F : invariant A"
by (simp add: invariant_def)

(*Could also say "invariant A Int invariant B <= invariant (A Int B)"*)
lemma invariant_Int:
     "[| F : invariant A;  F : invariant B |] ==> F : invariant (A Int B)"
by (auto simp add: invariant_def stable_Int)


(*** increasing ***)

lemma increasingD: 
     "F : increasing f ==> F : stable {s. z <= f s}"

by (unfold increasing_def, blast)

lemma increasing_constant [iff]: "F : increasing (%s. c)"
by (unfold increasing_def stable_def, auto)

lemma mono_increasing_o: 
     "mono g ==> increasing f <= increasing (g o f)"
apply (unfold increasing_def stable_def constrains_def, auto)
apply (blast intro: monoD order_trans)
done

(*Holds by the theorem (Suc m <= n) = (m < n) *)
lemma strict_increasingD: 
     "!!z::nat. F : increasing f ==> F: stable {s. z < f s}"
by (simp add: increasing_def Suc_le_eq [symmetric])


(** The Elimination Theorem.  The "free" m has become universally quantified!
    Should the premise be !!m instead of ALL m ?  Would make it harder to use
    in forward proof. **)

lemma elimination: 
    "[| ALL m:M. F : {s. s x = m} co (B m) |]  
     ==> F : {s. s x : M} co (UN m:M. B m)"
by (unfold constrains_def, blast)

(*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*)
lemma elimination_sing: 
    "(ALL m:M. F : {m} co (B m)) ==> F : M co (UN m:M. B m)"
by (unfold constrains_def, blast)



(*** Theoretical Results from Section 6 ***)

lemma constrains_strongest_rhs: 
    "F : A co (strongest_rhs F A )"
by (unfold constrains_def strongest_rhs_def, blast)

lemma strongest_rhs_is_strongest: 
    "F : A co B ==> strongest_rhs F A <= B"
by (unfold constrains_def strongest_rhs_def, blast)


(** Ad-hoc set-theory rules **)

lemma Un_Diff_Diff [simp]: "A Un B - (A - B) = B"
by blast

lemma Int_Union_Union: "Union(B) Int A = Union((%C. C Int A)`B)"
by blast

(** Needed for WF reasoning in WFair.ML **)

lemma Image_less_than [simp]: "less_than `` {k} = greaterThan k"
by blast

lemma Image_inverse_less_than [simp]: "less_than^-1 `` {k} = lessThan k"
by blast

end
