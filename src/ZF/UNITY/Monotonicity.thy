(*  Title:      ZF/UNITY/Monotonicity.thy
    Author:     Sidi O Ehmety, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge

Monotonicity of an operator (meta-function) with respect to arbitrary
set relations.
*)

header{*Monotonicity of an Operator WRT a Relation*}

theory Monotonicity imports GenPrefix MultisetSum
begin

definition
  mono1 :: "[i, i, i, i, i=>i] => o"  where
  "mono1(A, r, B, s, f) ==
    (\<forall>x \<in> A. \<forall>y \<in> A. <x,y> \<in> r \<longrightarrow> <f(x), f(y)> \<in> s) & (\<forall>x \<in> A. f(x) \<in> B)"

  (* monotonicity of a 2-place meta-function f *)

definition
  mono2 :: "[i, i, i, i, i, i, [i,i]=>i] => o"  where
  "mono2(A, r, B, s, C, t, f) == 
    (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>u \<in> B. \<forall>v \<in> B.
              <x,y> \<in> r & <u,v> \<in> s \<longrightarrow> <f(x,u), f(y,v)> \<in> t) &
    (\<forall>x \<in> A. \<forall>y \<in> B. f(x,y) \<in> C)"

 (* Internalized relations on sets and multisets *)

definition
  SetLe :: "i =>i"  where
  "SetLe(A) == {<x,y> \<in> Pow(A)*Pow(A). x \<subseteq> y}"

definition
  MultLe :: "[i,i] =>i"  where
  "MultLe(A, r) == multirel(A, r - id(A)) \<union> id(Mult(A))"


lemma mono1D: 
  "[| mono1(A, r, B, s, f); <x, y> \<in> r; x \<in> A; y \<in> A |] ==> <f(x), f(y)> \<in> s"
by (unfold mono1_def, auto)

lemma mono2D: 
     "[| mono2(A, r, B, s, C, t, f);  
         <x, y> \<in> r; <u,v> \<in> s; x \<in> A; y \<in> A; u \<in> B; v \<in> B |] 
      ==> <f(x, u), f(y,v)> \<in> t"
by (unfold mono2_def, auto)


(** Monotonicity of take **)

lemma take_mono_left_lemma:
     "[| i \<le> j; xs \<in> list(A); i \<in> nat; j \<in> nat |] 
      ==> <take(i, xs), take(j, xs)> \<in> prefix(A)"
apply (case_tac "length (xs) \<le> i")
 apply (subgoal_tac "length (xs) \<le> j")
  apply (simp)
 apply (blast intro: le_trans)
apply (drule not_lt_imp_le, auto)
apply (case_tac "length (xs) \<le> j")
 apply (auto simp add: take_prefix)
apply (drule not_lt_imp_le, auto)
apply (drule_tac m = i in less_imp_succ_add, auto)
apply (subgoal_tac "i #+ k \<le> length (xs) ")
 apply (simp add: take_add prefix_iff take_type drop_type)
apply (blast intro: leI)
done

lemma take_mono_left:
     "[| i \<le> j; xs \<in> list(A); j \<in> nat |]
      ==> <take(i, xs), take(j, xs)> \<in> prefix(A)"
by (blast intro: le_in_nat take_mono_left_lemma) 

lemma take_mono_right:
     "[| <xs,ys> \<in> prefix(A); i \<in> nat |] 
      ==> <take(i, xs), take(i, ys)> \<in> prefix(A)"
by (auto simp add: prefix_iff)

lemma take_mono:
     "[| i \<le> j; <xs, ys> \<in> prefix(A); j \<in> nat |]
      ==> <take(i, xs), take(j, ys)> \<in> prefix(A)"
apply (rule_tac b = "take (j, xs) " in prefix_trans)
apply (auto dest: prefix_type [THEN subsetD] intro: take_mono_left take_mono_right)
done

lemma mono_take [iff]:
     "mono2(nat, Le, list(A), prefix(A), list(A), prefix(A), take)"
apply (unfold mono2_def Le_def, auto)
apply (blast intro: take_mono)
done

(** Monotonicity of length **)

lemmas length_mono = prefix_length_le

lemma mono_length [iff]:
     "mono1(list(A), prefix(A), nat, Le, length)"
apply (unfold mono1_def)
apply (auto dest: prefix_length_le simp add: Le_def)
done

(** Monotonicity of \<union> **)

lemma mono_Un [iff]: 
     "mono2(Pow(A), SetLe(A), Pow(A), SetLe(A), Pow(A), SetLe(A), op Un)"
by (unfold mono2_def SetLe_def, auto)

(* Monotonicity of multiset union *)

lemma mono_munion [iff]: 
     "mono2(Mult(A), MultLe(A,r), Mult(A), MultLe(A, r), Mult(A), MultLe(A, r), munion)"
apply (unfold mono2_def MultLe_def)
apply (auto simp add: Mult_iff_multiset)
apply (blast intro: munion_multirel_mono munion_multirel_mono1 munion_multirel_mono2 multiset_into_Mult)+
done

lemma mono_succ [iff]: "mono1(nat, Le, nat, Le, succ)"
by (unfold mono1_def Le_def, auto)

end