(*  Title:      ZF/mono
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

Monotonicity of various operations
*)

theory mono = Sum + func:

(** Replacement, in its various formulations **)

(*Not easy to express monotonicity in P, since any "bigger" predicate
  would have to be single-valued*)
lemma Replace_mono: "A<=B ==> Replace(A,P) <= Replace(B,P)"
by (blast elim!: ReplaceE)

lemma RepFun_mono: "A<=B ==> {f(x). x:A} <= {f(x). x:B}"
by blast

lemma Pow_mono: "A<=B ==> Pow(A) <= Pow(B)"
by blast

lemma Union_mono: "A<=B ==> Union(A) <= Union(B)"
by blast

lemma UN_mono:
    "[| A<=C;  !!x. x:A ==> B(x)<=D(x) |] ==> (UN x:A. B(x)) <= (UN x:C. D(x))"
by blast  

(*Intersection is ANTI-monotonic.  There are TWO premises! *)
lemma Inter_anti_mono: "[| A<=B;  a:A |] ==> Inter(B) <= Inter(A)"
by blast

lemma cons_mono: "C<=D ==> cons(a,C) <= cons(a,D)"
by blast

lemma Un_mono: "[| A<=C;  B<=D |] ==> A Un B <= C Un D"
by blast

lemma Int_mono: "[| A<=C;  B<=D |] ==> A Int B <= C Int D"
by blast

lemma Diff_mono: "[| A<=C;  D<=B |] ==> A-B <= C-D"
by blast

(** Standard products, sums and function spaces **)

lemma Sigma_mono [rule_format]:
     "[| A<=C;  !!x. x:A --> B(x) <= D(x) |] ==> Sigma(A,B) <= Sigma(C,D)"
by blast

lemma sum_mono: "[| A<=C;  B<=D |] ==> A+B <= C+D"
by (unfold sum_def, blast)

(*Note that B->A and C->A are typically disjoint!*)
lemma Pi_mono: "B<=C ==> A->B <= A->C"
by (blast intro: lam_type elim: Pi_lamE)

lemma lam_mono: "A<=B ==> Lambda(A,c) <= Lambda(B,c)"
apply (unfold lam_def)
apply (erule RepFun_mono)
done

(** Converse, domain, range, field **)

lemma converse_mono: "r<=s ==> converse(r) <= converse(s)"
by blast

lemma domain_mono: "r<=s ==> domain(r)<=domain(s)"
by blast

lemmas domain_rel_subset = subset_trans [OF domain_mono domain_subset]

lemma range_mono: "r<=s ==> range(r)<=range(s)"
by blast

lemmas range_rel_subset = subset_trans [OF range_mono range_subset]

lemma field_mono: "r<=s ==> field(r)<=field(s)"
by blast

lemma field_rel_subset: "r <= A*A ==> field(r) <= A"
by (erule field_mono [THEN subset_trans], blast)


(** Images **)

lemma image_pair_mono:
    "[| !! x y. <x,y>:r ==> <x,y>:s;  A<=B |] ==> r``A <= s``B"
by blast 

lemma vimage_pair_mono:
    "[| !! x y. <x,y>:r ==> <x,y>:s;  A<=B |] ==> r-``A <= s-``B"
by blast 

lemma image_mono: "[| r<=s;  A<=B |] ==> r``A <= s``B"
by blast

lemma vimage_mono: "[| r<=s;  A<=B |] ==> r-``A <= s-``B"
by blast

lemma Collect_mono:
    "[| A<=B;  !!x. x:A ==> P(x) --> Q(x) |] ==> Collect(A,P) <= Collect(B,Q)"
by blast

(*Used in intr_elim.ML and in individual datatype definitions*)
lemmas basic_monos = subset_refl imp_refl disj_mono conj_mono ex_mono 
                     Collect_mono Part_mono in_mono

ML
{*
val Replace_mono = thm "Replace_mono";
val RepFun_mono = thm "RepFun_mono";
val Pow_mono = thm "Pow_mono";
val Union_mono = thm "Union_mono";
val UN_mono = thm "UN_mono";
val Inter_anti_mono = thm "Inter_anti_mono";
val cons_mono = thm "cons_mono";
val Un_mono = thm "Un_mono";
val Int_mono = thm "Int_mono";
val Diff_mono = thm "Diff_mono";
val Sigma_mono = thm "Sigma_mono";
val sum_mono = thm "sum_mono";
val Pi_mono = thm "Pi_mono";
val lam_mono = thm "lam_mono";
val converse_mono = thm "converse_mono";
val domain_mono = thm "domain_mono";
val domain_rel_subset = thm "domain_rel_subset";
val range_mono = thm "range_mono";
val range_rel_subset = thm "range_rel_subset";
val field_mono = thm "field_mono";
val field_rel_subset = thm "field_rel_subset";
val image_pair_mono = thm "image_pair_mono";
val vimage_pair_mono = thm "vimage_pair_mono";
val image_mono = thm "image_mono";
val vimage_mono = thm "vimage_mono";
val Collect_mono = thm "Collect_mono";

val basic_monos = thms "basic_monos";
*}

end
