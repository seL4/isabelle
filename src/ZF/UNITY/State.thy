(*  Title:      HOL/UNITY/State.thy
    ID:         $Id$
    Author:     Sidi O Ehmety, Computer Laboratory
    Copyright   2001  University of Cambridge

Formalizes UNITY-program states using dependent types so that:
 - variables are typed.
 - the state space is uniform, common to all defined programs.
 - variables can be quantified over.
*)

header{*UNITY Program States*}

theory State = Main:

consts var :: i
datatype var = Var("i \<in> list(nat)")
  type_intros  nat_subset_univ [THEN list_subset_univ, THEN subsetD]

consts
  type_of :: "i=>i"
  default_val :: "i=>i"

constdefs
  state   :: i
   "state == \<Pi>x \<in> var. cons(default_val(x), type_of(x))"

  st0     :: i
   "st0 == \<lambda>x \<in> var. default_val(x)"
  
  st_set  :: "i=>o"
(* To prevent typing conditions like `A<=state' from
   being used in combination with the rules `constrains_weaken', etc. *)
  "st_set(A) == A<=state"

  st_compl :: "i=>i"
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

lemma st_set_Un_iff [iff]: "st_set(A Un B) <-> st_set(A) & st_set(B)"
by (simp add: st_set_def, auto)

lemma st_set_Union_iff [iff]: "st_set(Union(S)) <-> (\<forall>A \<in> S. st_set(A))"
by (simp add: st_set_def, auto)

(* Intersection *)

lemma st_set_Int [intro!]: "st_set(A) | st_set(B) ==> st_set(A Int B)"
by (simp add: st_set_def, auto)

lemma st_set_Inter [intro!]: 
   "(S=0) | (\<exists>A \<in> S. st_set(A)) ==> st_set(Inter(S))"
apply (simp add: st_set_def Inter_def, auto)
done

(* Diff *)
lemma st_set_DiffI [intro!]: "st_set(A) ==> st_set(A - B)"
by (simp add: st_set_def, auto)

lemma Collect_Int_state [simp]: "Collect(state,P) Int state = Collect(state,P)"
by auto

lemma state_Int_Collect [simp]: "state Int Collect(state,P) = Collect(state,P)"
by auto


(* Introduction and destruction rules for st_set *)

lemma st_setI: "A <= state ==> st_set(A)"
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

lemma st_compl_iff [simp]: "x \<in> st_compl(A) <-> x \<in> state & x \<notin> A"
by (simp add: st_compl_def)

lemma st_compl_Collect [simp]:
     "st_compl({s \<in> state. P(s)}) = {s \<in> state. ~P(s)}"
by (simp add: st_compl_def, auto)

(*For using "disjunction" (union over an index set) to eliminate a variable.*)
lemma UN_conj_eq:
     "\<forall>d\<in>D. f(d) \<in> A ==> (\<Union>k\<in>A. {d\<in>D. P(d) & f(d) = k}) = {d\<in>D. P(d)}"
by blast


ML
{*
val st_set_def = thm "st_set_def";
val state_def = thm "state_def";

val st0_in_state = thm "st0_in_state";
val st_set_Collect = thm "st_set_Collect";
val st_set_0 = thm "st_set_0";
val st_set_state = thm "st_set_state";
val st_set_Un_iff = thm "st_set_Un_iff";
val st_set_Union_iff = thm "st_set_Union_iff";
val st_set_Int = thm "st_set_Int";
val st_set_Inter = thm "st_set_Inter";
val st_set_DiffI = thm "st_set_DiffI";
val Collect_Int_state = thm "Collect_Int_state";
val state_Int_Collect = thm "state_Int_Collect";
val st_setI = thm "st_setI";
val st_setD = thm "st_setD";
val st_set_subset = thm "st_set_subset";
val state_update_type = thm "state_update_type";
val st_set_compl = thm "st_set_compl";
val st_compl_iff = thm "st_compl_iff";
val st_compl_Collect = thm "st_compl_Collect";
*}

end
