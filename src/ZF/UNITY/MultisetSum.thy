(*  Title:      ZF/UNITY/MultusetSum.thy
    ID:         $Id$
    Author:     Sidi O Ehmety
*)

header {*Setsum for Multisets*}

theory MultisetSum
imports "../Induct/Multiset"
begin

constdefs

  lcomm :: "[i, i, [i,i]=>i]=>o"
  "lcomm(A, B, f) ==
   (\<forall>x \<in> A. \<forall>y \<in> A. \<forall>z \<in> B. f(x, f(y, z))= f(y, f(x, z)))  &
   (\<forall>x \<in> A. \<forall>y \<in> B. f(x, y) \<in> B)"

  general_setsum :: "[i,i,i, [i,i]=>i, i=>i] =>i"
   "general_setsum(C, B, e, f, g) ==
    if Finite(C) then fold[cons(e, B)](%x y. f(g(x), y), e, C) else e"

  msetsum :: "[i=>i, i, i]=>i"
  "msetsum(g, C, B) == normalize(general_setsum(C, Mult(B), 0, op +#, g))"

  (* sum for naturals *)
  nsetsum :: "[i=>i, i] =>i"
  "nsetsum(g, C) == general_setsum(C, nat, 0, op #+, g)"


lemma mset_of_normalize: "mset_of(normalize(M)) \<subseteq> mset_of(M)"
by (auto simp add: mset_of_def normalize_def)

lemma general_setsum_0 [simp]: "general_setsum(0, B, e, f, g) = e"
by (simp add: general_setsum_def)

lemma general_setsum_cons [simp]: 
"[| C \<in> Fin(A); a \<in> A; a\<notin>C; e \<in> B; \<forall>x \<in> A. g(x) \<in> B; lcomm(B, B, f) |] ==>  
  general_setsum(cons(a, C), B, e, f, g) =  
    f(g(a), general_setsum(C, B, e, f,g))"
apply (simp add: general_setsum_def)
apply  (auto simp add: Fin_into_Finite [THEN Finite_cons] cons_absorb)
prefer 2 apply (blast dest: Fin_into_Finite)
apply (rule fold_typing.fold_cons)
apply (auto simp add: fold_typing_def lcomm_def)
done

(** lcomm **)

lemma lcomm_mono: "[| C\<subseteq>A; lcomm(A, B, f) |] ==> lcomm(C, B,f)"
by (auto simp add: lcomm_def, blast)

lemma munion_lcomm [simp]: "lcomm(Mult(A), Mult(A), op +#)"
by (auto simp add: lcomm_def Mult_iff_multiset munion_lcommute)

(** msetsum **)

lemma multiset_general_setsum: 
     "[| C \<in> Fin(A); \<forall>x \<in> A. multiset(g(x))& mset_of(g(x))\<subseteq>B  |]   
      ==> multiset(general_setsum(C, B -||> nat - {0}, 0, \<lambda>u v. u +# v, g))"
apply (erule Fin_induct, auto)
apply (subst general_setsum_cons)
apply (auto simp add: Mult_iff_multiset)
done

lemma msetsum_0 [simp]: "msetsum(g, 0, B) = 0"
by (simp add: msetsum_def)

lemma msetsum_cons [simp]: 
  "[| C \<in> Fin(A); a\<notin>C; a \<in> A; \<forall>x \<in> A. multiset(g(x)) & mset_of(g(x))\<subseteq>B  |]   
   ==> msetsum(g, cons(a, C), B) = g(a) +#  msetsum(g, C, B)"
apply (simp add: msetsum_def)
apply (subst general_setsum_cons)
apply (auto simp add: multiset_general_setsum Mult_iff_multiset)
done

(* msetsum type *)

lemma msetsum_multiset: "multiset(msetsum(g, C, B))"
by (simp add: msetsum_def)

lemma mset_of_msetsum: 
     "[| C \<in> Fin(A); \<forall>x \<in> A. multiset(g(x)) & mset_of(g(x))\<subseteq>B |]   
      ==> mset_of(msetsum(g, C, B))\<subseteq>B"
by (erule Fin_induct, auto)


(*The reversed orientation looks more natural, but LOOPS as a simprule!*)
lemma msetsum_Un_Int: 
     "[| C \<in> Fin(A); D \<in> Fin(A); \<forall>x \<in> A. multiset(g(x)) & mset_of(g(x))\<subseteq>B |]
      ==> msetsum(g, C Un D, B) +# msetsum(g, C Int D, B)  
        = msetsum(g, C, B) +# msetsum(g, D, B)"
apply (erule Fin_induct)
apply (subgoal_tac [2] "cons (x, y) Un D = cons (x, y Un D) ")
apply (auto simp add: msetsum_multiset)
apply (subgoal_tac "y Un D \<in> Fin (A) & y Int D \<in> Fin (A) ")
apply clarify
apply (case_tac "x \<in> D")
apply (subgoal_tac [2] "cons (x, y) Int D = y Int D")
apply (subgoal_tac "cons (x, y) Int D = cons (x, y Int D) ")
apply (simp_all (no_asm_simp) add: cons_absorb munion_assoc msetsum_multiset)
apply (simp (no_asm_simp) add: munion_lcommute msetsum_multiset)
apply auto
done


lemma msetsum_Un_disjoint:
     "[| C \<in> Fin(A); D \<in> Fin(A); C Int D = 0;  
         \<forall>x \<in> A. multiset(g(x)) & mset_of(g(x))\<subseteq>B |]  
      ==> msetsum(g, C Un D, B) = msetsum(g, C, B) +# msetsum(g,D, B)"
apply (subst msetsum_Un_Int [symmetric])
apply (auto simp add: msetsum_multiset)
done

lemma UN_Fin_lemma [rule_format (no_asm)]:
     "I \<in> Fin(A) ==> (\<forall>i \<in> I. C(i) \<in> Fin(B)) --> (\<Union>i \<in> I. C(i)):Fin(B)"
by (erule Fin_induct, auto)
 
lemma msetsum_UN_disjoint [rule_format (no_asm)]:
     "[| I \<in> Fin(K); \<forall>i \<in> K. C(i) \<in> Fin(A) |] ==>  
      (\<forall>x \<in> A. multiset(f(x)) & mset_of(f(x))\<subseteq>B) -->   
      (\<forall>i \<in> I. \<forall>j \<in> I. i\<noteq>j --> C(i) Int C(j) = 0) -->  
	msetsum(f, \<Union>i \<in> I. C(i), B) = msetsum (%i. msetsum(f, C(i),B), I, B)"
apply (erule Fin_induct, auto)
apply (subgoal_tac "\<forall>i \<in> y. x \<noteq> i")
 prefer 2 apply blast
apply (subgoal_tac "C(x) Int (\<Union>i \<in> y. C (i)) = 0")
 prefer 2 apply blast
apply (subgoal_tac " (\<Union>i \<in> y. C (i)):Fin (A) & C(x) :Fin (A) ")
prefer 2 apply (blast intro: UN_Fin_lemma dest: FinD, clarify)
apply (simp (no_asm_simp) add: msetsum_Un_disjoint)
apply (subgoal_tac "\<forall>x \<in> K. multiset (msetsum (f, C(x), B)) & mset_of (msetsum (f, C(x), B)) \<subseteq> B")
apply (simp (no_asm_simp))
apply clarify
apply (drule_tac x = xa in bspec)
apply (simp_all (no_asm_simp) add: msetsum_multiset mset_of_msetsum)
done

lemma msetsum_addf: 
    "[| C \<in> Fin(A);  
      \<forall>x \<in> A. multiset(f(x)) & mset_of(f(x))\<subseteq>B;  
      \<forall>x \<in> A. multiset(g(x)) & mset_of(g(x))\<subseteq>B |] ==> 
      msetsum(%x. f(x) +# g(x), C, B) = msetsum(f, C, B) +# msetsum(g, C, B)"
apply (subgoal_tac "\<forall>x \<in> A. multiset (f(x) +# g(x)) & mset_of (f(x) +# g(x)) \<subseteq> B")
apply (erule Fin_induct)
apply (auto simp add: munion_ac) 
done

lemma msetsum_cong: 
    "[| C=D; !!x. x \<in> D ==> f(x) = g(x) |]
     ==> msetsum(f, C, B) = msetsum(g, D, B)"
by (simp add: msetsum_def general_setsum_def cong add: fold_cong)

lemma multiset_union_diff: "[| multiset(M); multiset(N) |] ==> M +# N -# N = M"
by (simp add: multiset_equality)

lemma msetsum_Un: "[| C \<in> Fin(A); D \<in> Fin(A);  
  \<forall>x \<in> A. multiset(f(x)) & mset_of(f(x)) \<subseteq> B  |]  
   ==> msetsum(f, C Un D, B) =  
          msetsum(f, C, B) +# msetsum(f, D, B) -# msetsum(f, C Int D, B)"
apply (subgoal_tac "C Un D \<in> Fin (A) & C Int D \<in> Fin (A) ")
apply clarify
apply (subst msetsum_Un_Int [symmetric])
apply (simp_all (no_asm_simp) add: msetsum_multiset multiset_union_diff)
apply (blast dest: FinD)
done

lemma nsetsum_0 [simp]: "nsetsum(g, 0)=0"
by (simp add: nsetsum_def)

lemma nsetsum_cons [simp]: 
     "[| Finite(C); x\<notin>C |] ==> nsetsum(g, cons(x, C))= g(x) #+ nsetsum(g, C)"
apply (simp add: nsetsum_def general_setsum_def)
apply (rule_tac A = "cons (x, C)" in fold_typing.fold_cons)
apply (auto intro: Finite_cons_lemma simp add: fold_typing_def)
done

lemma nsetsum_type [simp,TC]: "nsetsum(g, C) \<in> nat"
apply (case_tac "Finite (C) ")
 prefer 2 apply (simp add: nsetsum_def general_setsum_def)
apply (erule Finite_induct, auto)
done

ML
{*
val mset_of_normalize = thm "mset_of_normalize";
val general_setsum_0 = thm "general_setsum_0";
val general_setsum_cons = thm "general_setsum_cons";
val lcomm_mono = thm "lcomm_mono";
val munion_lcomm = thm "munion_lcomm";
val multiset_general_setsum = thm "multiset_general_setsum";
val msetsum_0 = thm "msetsum_0";
val msetsum_cons = thm "msetsum_cons";
val msetsum_multiset = thm "msetsum_multiset";
val mset_of_msetsum = thm "mset_of_msetsum";
val msetsum_Un_Int = thm "msetsum_Un_Int";
val msetsum_Un_disjoint = thm "msetsum_Un_disjoint";
val UN_Fin_lemma = thm "UN_Fin_lemma";
val msetsum_UN_disjoint = thm "msetsum_UN_disjoint";
val msetsum_addf = thm "msetsum_addf";
val msetsum_cong = thm "msetsum_cong";
val multiset_union_diff = thm "multiset_union_diff";
val msetsum_Un = thm "msetsum_Un";
val nsetsum_0 = thm "nsetsum_0";
val nsetsum_cons = thm "nsetsum_cons";
val nsetsum_type = thm "nsetsum_type";
*}

end