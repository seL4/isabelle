(*  Title:      HOL/UNITY/UNITY.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1998  University of Cambridge

The basic UNITY theory (revised version, based upon the "co"
operator).

From Misra, "A Logic for Concurrent Programming", 1994.
*)

header {*The Basic UNITY Theory*}

theory UNITY imports Main begin

typedef (Program)
  'a program = "{(init:: 'a set, acts :: ('a * 'a)set set,
                   allowed :: ('a * 'a)set set). Id \<in> acts & Id: allowed}" 
  by blast

definition Acts :: "'a program => ('a * 'a)set set" where
    "Acts F == (%(init, acts, allowed). acts) (Rep_Program F)"

definition "constrains" :: "['a set, 'a set] => 'a program set"  (infixl "co"     60) where
    "A co B == {F. \<forall>act \<in> Acts F. act``A \<subseteq> B}"

definition unless  :: "['a set, 'a set] => 'a program set"  (infixl "unless" 60)  where
    "A unless B == (A-B) co (A \<union> B)"

definition mk_program :: "('a set * ('a * 'a)set set * ('a * 'a)set set)
                   => 'a program" where
    "mk_program == %(init, acts, allowed).
                      Abs_Program (init, insert Id acts, insert Id allowed)"

definition Init :: "'a program => 'a set" where
    "Init F == (%(init, acts, allowed). init) (Rep_Program F)"

definition AllowedActs :: "'a program => ('a * 'a)set set" where
    "AllowedActs F == (%(init, acts, allowed). allowed) (Rep_Program F)"

definition Allowed :: "'a program => 'a program set" where
    "Allowed F == {G. Acts G \<subseteq> AllowedActs F}"

definition stable     :: "'a set => 'a program set" where
    "stable A == A co A"

definition strongest_rhs :: "['a program, 'a set] => 'a set" where
    "strongest_rhs F A == Inter {B. F \<in> A co B}"

definition invariant :: "'a set => 'a program set" where
    "invariant A == {F. Init F \<subseteq> A} \<inter> stable A"

definition increasing :: "['a => 'b::{order}] => 'a program set" where
    --{*Polymorphic in both states and the meaning of @{text "\<le>"}*}
    "increasing f == \<Inter>z. stable {s. z \<le> f s}"


text{*Perhaps HOL shouldn't add this in the first place!*}
declare image_Collect [simp del]

subsubsection{*The abstract type of programs*}

lemmas program_typedef =
     Rep_Program Rep_Program_inverse Abs_Program_inverse 
     Program_def Init_def Acts_def AllowedActs_def mk_program_def

lemma Id_in_Acts [iff]: "Id \<in> Acts F"
apply (cut_tac x = F in Rep_Program)
apply (auto simp add: program_typedef) 
done

lemma insert_Id_Acts [iff]: "insert Id (Acts F) = Acts F"
by (simp add: insert_absorb Id_in_Acts)

lemma Acts_nonempty [simp]: "Acts F \<noteq> {}"
by auto

lemma Id_in_AllowedActs [iff]: "Id \<in> AllowedActs F"
apply (cut_tac x = F in Rep_Program)
apply (auto simp add: program_typedef) 
done

lemma insert_Id_AllowedActs [iff]: "insert Id (AllowedActs F) = AllowedActs F"
by (simp add: insert_absorb Id_in_AllowedActs)

subsubsection{*Inspectors for type "program"*}

lemma Init_eq [simp]: "Init (mk_program (init,acts,allowed)) = init"
by (simp add: program_typedef)

lemma Acts_eq [simp]: "Acts (mk_program (init,acts,allowed)) = insert Id acts"
by (simp add: program_typedef)

lemma AllowedActs_eq [simp]:
     "AllowedActs (mk_program (init,acts,allowed)) = insert Id allowed"
by (simp add: program_typedef)

subsubsection{*Equality for UNITY programs*}

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


subsubsection{*co*}

lemma constrainsI: 
    "(!!act s s'. [| act: Acts F;  (s,s') \<in> act;  s \<in> A |] ==> s': A')  
     ==> F \<in> A co A'"
by (simp add: constrains_def, blast)

lemma constrainsD: 
    "[| F \<in> A co A'; act: Acts F;  (s,s'): act;  s \<in> A |] ==> s': A'"
by (unfold constrains_def, blast)

lemma constrains_empty [iff]: "F \<in> {} co B"
by (unfold constrains_def, blast)

lemma constrains_empty2 [iff]: "(F \<in> A co {}) = (A={})"
by (unfold constrains_def, blast)

lemma constrains_UNIV [iff]: "(F \<in> UNIV co B) = (B = UNIV)"
by (unfold constrains_def, blast)

lemma constrains_UNIV2 [iff]: "F \<in> A co UNIV"
by (unfold constrains_def, blast)

text{*monotonic in 2nd argument*}
lemma constrains_weaken_R: 
    "[| F \<in> A co A'; A'<=B' |] ==> F \<in> A co B'"
by (unfold constrains_def, blast)

text{*anti-monotonic in 1st argument*}
lemma constrains_weaken_L: 
    "[| F \<in> A co A'; B \<subseteq> A |] ==> F \<in> B co A'"
by (unfold constrains_def, blast)

lemma constrains_weaken: 
   "[| F \<in> A co A'; B \<subseteq> A; A'<=B' |] ==> F \<in> B co B'"
by (unfold constrains_def, blast)

subsubsection{*Union*}

lemma constrains_Un: 
    "[| F \<in> A co A'; F \<in> B co B' |] ==> F \<in> (A \<union> B) co (A' \<union> B')"
by (unfold constrains_def, blast)

lemma constrains_UN: 
    "(!!i. i \<in> I ==> F \<in> (A i) co (A' i)) 
     ==> F \<in> (\<Union>i \<in> I. A i) co (\<Union>i \<in> I. A' i)"
by (unfold constrains_def, blast)

lemma constrains_Un_distrib: "(A \<union> B) co C = (A co C) \<inter> (B co C)"
by (unfold constrains_def, blast)

lemma constrains_UN_distrib: "(\<Union>i \<in> I. A i) co B = (\<Inter>i \<in> I. A i co B)"
by (unfold constrains_def, blast)

lemma constrains_Int_distrib: "C co (A \<inter> B) = (C co A) \<inter> (C co B)"
by (unfold constrains_def, blast)

lemma constrains_INT_distrib: "A co (\<Inter>i \<in> I. B i) = (\<Inter>i \<in> I. A co B i)"
by (unfold constrains_def, blast)

subsubsection{*Intersection*}

lemma constrains_Int: 
    "[| F \<in> A co A'; F \<in> B co B' |] ==> F \<in> (A \<inter> B) co (A' \<inter> B')"
by (unfold constrains_def, blast)

lemma constrains_INT: 
    "(!!i. i \<in> I ==> F \<in> (A i) co (A' i)) 
     ==> F \<in> (\<Inter>i \<in> I. A i) co (\<Inter>i \<in> I. A' i)"
by (unfold constrains_def, blast)

lemma constrains_imp_subset: "F \<in> A co A' ==> A \<subseteq> A'"
by (unfold constrains_def, auto)

text{*The reasoning is by subsets since "co" refers to single actions
  only.  So this rule isn't that useful.*}
lemma constrains_trans: 
    "[| F \<in> A co B; F \<in> B co C |] ==> F \<in> A co C"
by (unfold constrains_def, blast)

lemma constrains_cancel: 
   "[| F \<in> A co (A' \<union> B); F \<in> B co B' |] ==> F \<in> A co (A' \<union> B')"
by (unfold constrains_def, clarify, blast)


subsubsection{*unless*}

lemma unlessI: "F \<in> (A-B) co (A \<union> B) ==> F \<in> A unless B"
by (unfold unless_def, assumption)

lemma unlessD: "F \<in> A unless B ==> F \<in> (A-B) co (A \<union> B)"
by (unfold unless_def, assumption)


subsubsection{*stable*}

lemma stableI: "F \<in> A co A ==> F \<in> stable A"
by (unfold stable_def, assumption)

lemma stableD: "F \<in> stable A ==> F \<in> A co A"
by (unfold stable_def, assumption)

lemma stable_UNIV [simp]: "stable UNIV = UNIV"
by (unfold stable_def constrains_def, auto)

subsubsection{*Union*}

lemma stable_Un: 
    "[| F \<in> stable A; F \<in> stable A' |] ==> F \<in> stable (A \<union> A')"

apply (unfold stable_def)
apply (blast intro: constrains_Un)
done

lemma stable_UN: 
    "(!!i. i \<in> I ==> F \<in> stable (A i)) ==> F \<in> stable (\<Union>i \<in> I. A i)"
apply (unfold stable_def)
apply (blast intro: constrains_UN)
done

lemma stable_Union: 
    "(!!A. A \<in> X ==> F \<in> stable A) ==> F \<in> stable (\<Union>X)"
by (unfold stable_def constrains_def, blast)

subsubsection{*Intersection*}

lemma stable_Int: 
    "[| F \<in> stable A;  F \<in> stable A' |] ==> F \<in> stable (A \<inter> A')"
apply (unfold stable_def)
apply (blast intro: constrains_Int)
done

lemma stable_INT: 
    "(!!i. i \<in> I ==> F \<in> stable (A i)) ==> F \<in> stable (\<Inter>i \<in> I. A i)"
apply (unfold stable_def)
apply (blast intro: constrains_INT)
done

lemma stable_Inter: 
    "(!!A. A \<in> X ==> F \<in> stable A) ==> F \<in> stable (\<Inter>X)"
by (unfold stable_def constrains_def, blast)

lemma stable_constrains_Un: 
    "[| F \<in> stable C; F \<in> A co (C \<union> A') |] ==> F \<in> (C \<union> A) co (C \<union> A')"
by (unfold stable_def constrains_def, blast)

lemma stable_constrains_Int: 
  "[| F \<in> stable C; F \<in>  (C \<inter> A) co A' |] ==> F \<in> (C \<inter> A) co (C \<inter> A')"
by (unfold stable_def constrains_def, blast)

(*[| F \<in> stable C; F \<in>  (C \<inter> A) co A |] ==> F \<in> stable (C \<inter> A) *)
lemmas stable_constrains_stable = stable_constrains_Int[THEN stableI]


subsubsection{*invariant*}

lemma invariantI: "[| Init F \<subseteq> A;  F \<in> stable A |] ==> F \<in> invariant A"
by (simp add: invariant_def)

text{*Could also say @{term "invariant A \<inter> invariant B \<subseteq> invariant(A \<inter> B)"}*}
lemma invariant_Int:
     "[| F \<in> invariant A;  F \<in> invariant B |] ==> F \<in> invariant (A \<inter> B)"
by (auto simp add: invariant_def stable_Int)


subsubsection{*increasing*}

lemma increasingD: 
     "F \<in> increasing f ==> F \<in> stable {s. z \<subseteq> f s}"
by (unfold increasing_def, blast)

lemma increasing_constant [iff]: "F \<in> increasing (%s. c)"
by (unfold increasing_def stable_def, auto)

lemma mono_increasing_o: 
     "mono g ==> increasing f \<subseteq> increasing (g o f)"
apply (unfold increasing_def stable_def constrains_def, auto)
apply (blast intro: monoD order_trans)
done

(*Holds by the theorem (Suc m \<subseteq> n) = (m < n) *)
lemma strict_increasingD: 
     "!!z::nat. F \<in> increasing f ==> F \<in> stable {s. z < f s}"
by (simp add: increasing_def Suc_le_eq [symmetric])


(** The Elimination Theorem.  The "free" m has become universally quantified!
    Should the premise be !!m instead of \<forall>m ?  Would make it harder to use
    in forward proof. **)

lemma elimination: 
    "[| \<forall>m \<in> M. F \<in> {s. s x = m} co (B m) |]  
     ==> F \<in> {s. s x \<in> M} co (\<Union>m \<in> M. B m)"
by (unfold constrains_def, blast)

text{*As above, but for the trivial case of a one-variable state, in which the
  state is identified with its one variable.*}
lemma elimination_sing: 
    "(\<forall>m \<in> M. F \<in> {m} co (B m)) ==> F \<in> M co (\<Union>m \<in> M. B m)"
by (unfold constrains_def, blast)



subsubsection{*Theoretical Results from Section 6*}

lemma constrains_strongest_rhs: 
    "F \<in> A co (strongest_rhs F A )"
by (unfold constrains_def strongest_rhs_def, blast)

lemma strongest_rhs_is_strongest: 
    "F \<in> A co B ==> strongest_rhs F A \<subseteq> B"
by (unfold constrains_def strongest_rhs_def, blast)


subsubsection{*Ad-hoc set-theory rules*}

lemma Un_Diff_Diff [simp]: "A \<union> B - (A - B) = B"
by blast

lemma Int_Union_Union: "Union(B) \<inter> A = Union((%C. C \<inter> A)`B)"
by blast

text{*Needed for WF reasoning in WFair.thy*}

lemma Image_less_than [simp]: "less_than `` {k} = greaterThan k"
by blast

lemma Image_inverse_less_than [simp]: "less_than^-1 `` {k} = lessThan k"
by blast


subsection{*Partial versus Total Transitions*}

definition totalize_act :: "('a * 'a)set => ('a * 'a)set" where
    "totalize_act act == act \<union> Id_on (-(Domain act))"

definition totalize :: "'a program => 'a program" where
    "totalize F == mk_program (Init F,
                               totalize_act ` Acts F,
                               AllowedActs F)"

definition mk_total_program :: "('a set * ('a * 'a)set set * ('a * 'a)set set)
                   => 'a program" where
    "mk_total_program args == totalize (mk_program args)"

definition all_total :: "'a program => bool" where
    "all_total F == \<forall>act \<in> Acts F. Domain act = UNIV"
  
lemma insert_Id_image_Acts: "f Id = Id ==> insert Id (f`Acts F) = f ` Acts F"
by (blast intro: sym [THEN image_eqI])


subsubsection{*Basic properties*}

lemma totalize_act_Id [simp]: "totalize_act Id = Id"
by (simp add: totalize_act_def) 

lemma Domain_totalize_act [simp]: "Domain (totalize_act act) = UNIV"
by (auto simp add: totalize_act_def)

lemma Init_totalize [simp]: "Init (totalize F) = Init F"
by (unfold totalize_def, auto)

lemma Acts_totalize [simp]: "Acts (totalize F) = (totalize_act ` Acts F)"
by (simp add: totalize_def insert_Id_image_Acts) 

lemma AllowedActs_totalize [simp]: "AllowedActs (totalize F) = AllowedActs F"
by (simp add: totalize_def)

lemma totalize_constrains_iff [simp]: "(totalize F \<in> A co B) = (F \<in> A co B)"
by (simp add: totalize_def totalize_act_def constrains_def, blast)

lemma totalize_stable_iff [simp]: "(totalize F \<in> stable A) = (F \<in> stable A)"
by (simp add: stable_def)

lemma totalize_invariant_iff [simp]:
     "(totalize F \<in> invariant A) = (F \<in> invariant A)"
by (simp add: invariant_def)

lemma all_total_totalize: "all_total (totalize F)"
by (simp add: totalize_def all_total_def)

lemma Domain_iff_totalize_act: "(Domain act = UNIV) = (totalize_act act = act)"
by (force simp add: totalize_act_def)

lemma all_total_imp_totalize: "all_total F ==> (totalize F = F)"
apply (simp add: all_total_def totalize_def) 
apply (rule program_equalityI)
  apply (simp_all add: Domain_iff_totalize_act image_def)
done

lemma all_total_iff_totalize: "all_total F = (totalize F = F)"
apply (rule iffI) 
 apply (erule all_total_imp_totalize) 
apply (erule subst) 
apply (rule all_total_totalize) 
done

lemma mk_total_program_constrains_iff [simp]:
     "(mk_total_program args \<in> A co B) = (mk_program args \<in> A co B)"
by (simp add: mk_total_program_def)


subsection{*Rules for Lazy Definition Expansion*}

text{*They avoid expanding the full program, which is a large expression*}

lemma def_prg_Init:
     "F = mk_total_program (init,acts,allowed) ==> Init F = init"
by (simp add: mk_total_program_def)

lemma def_prg_Acts:
     "F = mk_total_program (init,acts,allowed) 
      ==> Acts F = insert Id (totalize_act ` acts)"
by (simp add: mk_total_program_def)

lemma def_prg_AllowedActs:
     "F = mk_total_program (init,acts,allowed)  
      ==> AllowedActs F = insert Id allowed"
by (simp add: mk_total_program_def)

text{*An action is expanded if a pair of states is being tested against it*}
lemma def_act_simp:
     "act = {(s,s'). P s s'} ==> ((s,s') \<in> act) = P s s'"
by (simp add: mk_total_program_def)

text{*A set is expanded only if an element is being tested against it*}
lemma def_set_simp: "A = B ==> (x \<in> A) = (x \<in> B)"
by (simp add: mk_total_program_def)

subsubsection{*Inspectors for type "program"*}

lemma Init_total_eq [simp]:
     "Init (mk_total_program (init,acts,allowed)) = init"
by (simp add: mk_total_program_def)

lemma Acts_total_eq [simp]:
    "Acts(mk_total_program(init,acts,allowed)) = insert Id (totalize_act`acts)"
by (simp add: mk_total_program_def)

lemma AllowedActs_total_eq [simp]:
     "AllowedActs (mk_total_program (init,acts,allowed)) = insert Id allowed"
by (auto simp add: mk_total_program_def)

end
