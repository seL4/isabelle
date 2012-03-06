(*  Title:      ZF/UNITY/State.thy
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Formalizes UNITY-program states using dependent types so that:
 - variables are typed.
 - the state space is uniform, common to all defined programs.
 - variables can be quantified over.
*)

header{*UNITY Program States*}

theory State imports Main begin

consts var :: i
datatype var = Var("i \<in> list(nat)")
  type_intros  nat_subset_univ [THEN list_subset_univ, THEN subsetD]

consts
  type_of :: "i=>i"
  default_val :: "i=>i"

definition
  "state == \<Pi> x \<in> var. cons(default_val(x), type_of(x))"

definition
  "st0 == \<lambda>x \<in> var. default_val(x)"
  
definition
  st_set  :: "i=>o"  where
(* To prevent typing conditions like `A<=state' from
   being used in combination with the rules `constrains_weaken', etc. *)
  "st_set(A) == A<=state"

definition
  st_compl :: "i=>i"  where
  "st_compl(A) == state-A"


lemma st0_in_state [simp,TC]: "st0 \<in> state"
by (simp add: state_def st0_def)

lemma st_set_Collect [iff]: "st_set({x \<in> state. P(x)})"
by (simp add: st_set_def, auto)

lemma st_set_0 [iff]: "st_set(0)"
by (simp add: st_set_def)

lemma st_set_state [iff]: "st_set(state)"
by (simp add: st_set_def)

(* Union *)

lemma st_set_Un_iff [iff]: "st_set(A \<union> B) \<longleftrightarrow> st_set(A) & st_set(B)"
by (simp add: st_set_def, auto)

lemma st_set_Union_iff [iff]: "st_set(\<Union>(S)) \<longleftrightarrow> (\<forall>A \<in> S. st_set(A))"
by (simp add: st_set_def, auto)

(* Intersection *)

lemma st_set_Int [intro!]: "st_set(A) | st_set(B) ==> st_set(A \<inter> B)"
by (simp add: st_set_def, auto)

lemma st_set_Inter [intro!]: 
   "(S=0) | (\<exists>A \<in> S. st_set(A)) ==> st_set(\<Inter>(S))"
apply (simp add: st_set_def Inter_def, auto)
done

(* Diff *)
lemma st_set_DiffI [intro!]: "st_set(A) ==> st_set(A - B)"
by (simp add: st_set_def, auto)

lemma Collect_Int_state [simp]: "Collect(state,P) \<inter> state = Collect(state,P)"
by auto

lemma state_Int_Collect [simp]: "state \<inter> Collect(state,P) = Collect(state,P)"
by auto


(* Introduction and destruction rules for st_set *)

lemma st_setI: "A \<subseteq> state ==> st_set(A)"
by (simp add: st_set_def)

lemma st_setD: "st_set(A) ==> A<=state"
by (simp add: st_set_def)

lemma st_set_subset: "[| st_set(A); B<=A |] ==> st_set(B)"
by (simp add: st_set_def, auto)


lemma state_update_type: 
     "[| s \<in> state; x \<in> var; y \<in> type_of(x) |] ==> s(x:=y):state"
apply (simp add: state_def)
apply (blast intro: update_type)
done

lemma st_set_compl [simp]: "st_set(st_compl(A))"
by (simp add: st_compl_def, auto)

lemma st_compl_iff [simp]: "x \<in> st_compl(A) \<longleftrightarrow> x \<in> state & x \<notin> A"
by (simp add: st_compl_def)

lemma st_compl_Collect [simp]:
     "st_compl({s \<in> state. P(s)}) = {s \<in> state. ~P(s)}"
by (simp add: st_compl_def, auto)

(*For using "disjunction" (union over an index set) to eliminate a variable.*)
lemma UN_conj_eq:
     "\<forall>d\<in>D. f(d) \<in> A ==> (\<Union>k\<in>A. {d\<in>D. P(d) & f(d) = k}) = {d\<in>D. P(d)}"
by blast

end
