(*  Title:      ZF/fixedpt.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Least and greatest fixed points; the Knaster-Tarski Theorem

Proved in the lattice of subsets of D, namely Pow(D), with Inter as glb
*)

theory Fixedpt = equalities:

constdefs
  
  (*monotone operator from Pow(D) to itself*)
  bnd_mono :: "[i,i=>i]=>o"
     "bnd_mono(D,h) == h(D)<=D & (ALL W X. W<=X --> X<=D --> h(W) <= h(X))"

  lfp      :: "[i,i=>i]=>i"
     "lfp(D,h) == Inter({X: Pow(D). h(X) <= X})"

  gfp      :: "[i,i=>i]=>i"
     "gfp(D,h) == Union({X: Pow(D). X <= h(X)})"


(*** Monotone operators ***)

lemma bnd_monoI:
    "[| h(D)<=D;   
        !!W X. [| W<=D;  X<=D;  W<=X |] ==> h(W) <= h(X)   
     |] ==> bnd_mono(D,h)"
by (unfold bnd_mono_def, clarify, blast)  

lemma bnd_monoD1: "bnd_mono(D,h) ==> h(D) <= D"
apply (unfold bnd_mono_def)
apply (erule conjunct1)
done

lemma bnd_monoD2: "[| bnd_mono(D,h);  W<=X;  X<=D |] ==> h(W) <= h(X)"
by (unfold bnd_mono_def, blast)

lemma bnd_mono_subset:
    "[| bnd_mono(D,h);  X<=D |] ==> h(X) <= D"
by (unfold bnd_mono_def, clarify, blast) 

lemma bnd_mono_Un:
     "[| bnd_mono(D,h);  A <= D;  B <= D |] ==> h(A) Un h(B) <= h(A Un B)"
apply (unfold bnd_mono_def)
apply (rule Un_least, blast+)
done

(*unused*)
lemma bnd_mono_UN:
     "[| bnd_mono(D,h);  \<forall>i\<in>I. A(i) <= D |] 
      ==> (\<Union>i\<in>I. h(A(i))) <= h((\<Union>i\<in>I. A(i)))"
apply (unfold bnd_mono_def) 
apply (rule UN_least)
apply (elim conjE) 
apply (drule_tac x="A(i)" in spec)
apply (drule_tac x="(\<Union>i\<in>I. A(i))" in spec) 
apply blast 
done

(*Useful??*)
lemma bnd_mono_Int:
     "[| bnd_mono(D,h);  A <= D;  B <= D |] ==> h(A Int B) <= h(A) Int h(B)"
apply (rule Int_greatest) 
apply (erule bnd_monoD2, rule Int_lower1, assumption) 
apply (erule bnd_monoD2, rule Int_lower2, assumption) 
done

(**** Proof of Knaster-Tarski Theorem for the lfp ****)

(*lfp is contained in each pre-fixedpoint*)
lemma lfp_lowerbound: 
    "[| h(A) <= A;  A<=D |] ==> lfp(D,h) <= A"
by (unfold lfp_def, blast)

(*Unfolding the defn of Inter dispenses with the premise bnd_mono(D,h)!*)
lemma lfp_subset: "lfp(D,h) <= D"
by (unfold lfp_def Inter_def, blast)

(*Used in datatype package*)
lemma def_lfp_subset:  "A == lfp(D,h) ==> A <= D"
apply simp
apply (rule lfp_subset)
done

lemma lfp_greatest:  
    "[| h(D) <= D;  !!X. [| h(X) <= X;  X<=D |] ==> A<=X |] ==> A <= lfp(D,h)"
by (unfold lfp_def, blast) 

lemma lfp_lemma1:  
    "[| bnd_mono(D,h);  h(A)<=A;  A<=D |] ==> h(lfp(D,h)) <= A"
apply (erule bnd_monoD2 [THEN subset_trans])
apply (rule lfp_lowerbound, assumption+)
done

lemma lfp_lemma2: "bnd_mono(D,h) ==> h(lfp(D,h)) <= lfp(D,h)"
apply (rule bnd_monoD1 [THEN lfp_greatest])
apply (rule_tac [2] lfp_lemma1)
apply (assumption+)
done

lemma lfp_lemma3: 
    "bnd_mono(D,h) ==> lfp(D,h) <= h(lfp(D,h))"
apply (rule lfp_lowerbound)
apply (rule bnd_monoD2, assumption)
apply (rule lfp_lemma2, assumption)
apply (erule_tac [2] bnd_mono_subset)
apply (rule lfp_subset)+
done

lemma lfp_unfold: "bnd_mono(D,h) ==> lfp(D,h) = h(lfp(D,h))"
apply (rule equalityI) 
apply (erule lfp_lemma3) 
apply (erule lfp_lemma2) 
done

(*Definition form, to control unfolding*)
lemma def_lfp_unfold:
    "[| A==lfp(D,h);  bnd_mono(D,h) |] ==> A = h(A)"
apply simp
apply (erule lfp_unfold)
done

(*** General induction rule for least fixedpoints ***)

lemma Collect_is_pre_fixedpt:
    "[| bnd_mono(D,h);  !!x. x : h(Collect(lfp(D,h),P)) ==> P(x) |]
     ==> h(Collect(lfp(D,h),P)) <= Collect(lfp(D,h),P)"
by (blast intro: lfp_lemma2 [THEN subsetD] bnd_monoD2 [THEN subsetD] 
                 lfp_subset [THEN subsetD]) 

(*This rule yields an induction hypothesis in which the components of a
  data structure may be assumed to be elements of lfp(D,h)*)
lemma induct:
    "[| bnd_mono(D,h);  a : lfp(D,h);                    
        !!x. x : h(Collect(lfp(D,h),P)) ==> P(x)         
     |] ==> P(a)"
apply (rule Collect_is_pre_fixedpt
              [THEN lfp_lowerbound, THEN subsetD, THEN CollectD2])
apply (rule_tac [3] lfp_subset [THEN Collect_subset [THEN subset_trans]], 
       blast+)
done

(*Definition form, to control unfolding*)
lemma def_induct:
    "[| A == lfp(D,h);  bnd_mono(D,h);  a:A;    
        !!x. x : h(Collect(A,P)) ==> P(x)  
     |] ==> P(a)"
by (rule induct, blast+)

(*This version is useful when "A" is not a subset of D
  second premise could simply be h(D Int A) <= D or !!X. X<=D ==> h(X)<=D *)
lemma lfp_Int_lowerbound:
    "[| h(D Int A) <= A;  bnd_mono(D,h) |] ==> lfp(D,h) <= A" 
apply (rule lfp_lowerbound [THEN subset_trans])
apply (erule bnd_mono_subset [THEN Int_greatest], blast+)
done

(*Monotonicity of lfp, where h precedes i under a domain-like partial order
  monotonicity of h is not strictly necessary; h must be bounded by D*)
lemma lfp_mono:
  assumes hmono: "bnd_mono(D,h)"
      and imono: "bnd_mono(E,i)"
      and subhi: "!!X. X<=D ==> h(X) <= i(X)"
    shows "lfp(D,h) <= lfp(E,i)"
apply (rule bnd_monoD1 [THEN lfp_greatest])
apply (rule imono)
apply (rule hmono [THEN [2] lfp_Int_lowerbound])
apply (rule Int_lower1 [THEN subhi, THEN subset_trans])
apply (rule imono [THEN bnd_monoD2, THEN subset_trans], auto) 
done

(*This (unused) version illustrates that monotonicity is not really needed,
  but both lfp's must be over the SAME set D;  Inter is anti-monotonic!*)
lemma lfp_mono2:
    "[| i(D) <= D;  !!X. X<=D ==> h(X) <= i(X)  |] ==> lfp(D,h) <= lfp(D,i)"
apply (rule lfp_greatest, assumption)
apply (rule lfp_lowerbound, blast, assumption)
done


(**** Proof of Knaster-Tarski Theorem for the gfp ****)

(*gfp contains each post-fixedpoint that is contained in D*)
lemma gfp_upperbound: "[| A <= h(A);  A<=D |] ==> A <= gfp(D,h)"
apply (unfold gfp_def)
apply (rule PowI [THEN CollectI, THEN Union_upper])
apply (assumption+)
done

lemma gfp_subset: "gfp(D,h) <= D"
by (unfold gfp_def, blast)

(*Used in datatype package*)
lemma def_gfp_subset: "A==gfp(D,h) ==> A <= D"
apply simp
apply (rule gfp_subset)
done

lemma gfp_least: 
    "[| bnd_mono(D,h);  !!X. [| X <= h(X);  X<=D |] ==> X<=A |] ==>  
     gfp(D,h) <= A"
apply (unfold gfp_def)
apply (blast dest: bnd_monoD1) 
done

lemma gfp_lemma1: 
    "[| bnd_mono(D,h);  A<=h(A);  A<=D |] ==> A <= h(gfp(D,h))"
apply (rule subset_trans, assumption)
apply (erule bnd_monoD2)
apply (rule_tac [2] gfp_subset)
apply (simp add: gfp_upperbound)
done

lemma gfp_lemma2: "bnd_mono(D,h) ==> gfp(D,h) <= h(gfp(D,h))"
apply (rule gfp_least)
apply (rule_tac [2] gfp_lemma1)
apply (assumption+)
done

lemma gfp_lemma3: 
    "bnd_mono(D,h) ==> h(gfp(D,h)) <= gfp(D,h)"
apply (rule gfp_upperbound)
apply (rule bnd_monoD2, assumption)
apply (rule gfp_lemma2, assumption)
apply (erule bnd_mono_subset, rule gfp_subset)+
done

lemma gfp_unfold: "bnd_mono(D,h) ==> gfp(D,h) = h(gfp(D,h))"
apply (rule equalityI) 
apply (erule gfp_lemma2) 
apply (erule gfp_lemma3) 
done

(*Definition form, to control unfolding*)
lemma def_gfp_unfold:
    "[| A==gfp(D,h);  bnd_mono(D,h) |] ==> A = h(A)"
apply simp
apply (erule gfp_unfold)
done


(*** Coinduction rules for greatest fixed points ***)

(*weak version*)
lemma weak_coinduct: "[| a: X;  X <= h(X);  X <= D |] ==> a : gfp(D,h)"
by (blast intro: gfp_upperbound [THEN subsetD])

lemma coinduct_lemma:
    "[| X <= h(X Un gfp(D,h));  X <= D;  bnd_mono(D,h) |] ==>   
     X Un gfp(D,h) <= h(X Un gfp(D,h))"
apply (erule Un_least)
apply (rule gfp_lemma2 [THEN subset_trans], assumption)
apply (rule Un_upper2 [THEN subset_trans])
apply (rule bnd_mono_Un, assumption+) 
apply (rule gfp_subset)
done

(*strong version*)
lemma coinduct:
     "[| bnd_mono(D,h);  a: X;  X <= h(X Un gfp(D,h));  X <= D |]
      ==> a : gfp(D,h)"
apply (rule weak_coinduct)
apply (erule_tac [2] coinduct_lemma)
apply (simp_all add: gfp_subset Un_subset_iff) 
done

(*Definition form, to control unfolding*)
lemma def_coinduct:
    "[| A == gfp(D,h);  bnd_mono(D,h);  a: X;  X <= h(X Un A);  X <= D |] ==>  
     a : A"
apply simp
apply (rule coinduct, assumption+)
done

(*The version used in the induction/coinduction package*)
lemma def_Collect_coinduct:
    "[| A == gfp(D, %w. Collect(D,P(w)));  bnd_mono(D, %w. Collect(D,P(w)));   
        a: X;  X <= D;  !!z. z: X ==> P(X Un A, z) |] ==>  
     a : A"
apply (rule def_coinduct, assumption+, blast+)
done

(*Monotonicity of gfp!*)
lemma gfp_mono:
    "[| bnd_mono(D,h);  D <= E;                  
        !!X. X<=D ==> h(X) <= i(X)  |] ==> gfp(D,h) <= gfp(E,i)"
apply (rule gfp_upperbound)
apply (rule gfp_lemma2 [THEN subset_trans], assumption)
apply (blast del: subsetI intro: gfp_subset) 
apply (blast del: subsetI intro: subset_trans gfp_subset) 
done

ML
{*
val bnd_mono_def = thm "bnd_mono_def";
val lfp_def = thm "lfp_def";
val gfp_def = thm "gfp_def";

val bnd_monoI = thm "bnd_monoI";
val bnd_monoD1 = thm "bnd_monoD1";
val bnd_monoD2 = thm "bnd_monoD2";
val bnd_mono_subset = thm "bnd_mono_subset";
val bnd_mono_Un = thm "bnd_mono_Un";
val bnd_mono_Int = thm "bnd_mono_Int";
val lfp_lowerbound = thm "lfp_lowerbound";
val lfp_subset = thm "lfp_subset";
val def_lfp_subset = thm "def_lfp_subset";
val lfp_greatest = thm "lfp_greatest";
val lfp_unfold = thm "lfp_unfold";
val def_lfp_unfold = thm "def_lfp_unfold";
val Collect_is_pre_fixedpt = thm "Collect_is_pre_fixedpt";
val induct = thm "induct";
val def_induct = thm "def_induct";
val lfp_Int_lowerbound = thm "lfp_Int_lowerbound";
val lfp_mono = thm "lfp_mono";
val lfp_mono2 = thm "lfp_mono2";
val gfp_upperbound = thm "gfp_upperbound";
val gfp_subset = thm "gfp_subset";
val def_gfp_subset = thm "def_gfp_subset";
val gfp_least = thm "gfp_least";
val gfp_unfold = thm "gfp_unfold";
val def_gfp_unfold = thm "def_gfp_unfold";
val weak_coinduct = thm "weak_coinduct";
val coinduct = thm "coinduct";
val def_coinduct = thm "def_coinduct";
val def_Collect_coinduct = thm "def_Collect_coinduct";
val gfp_mono = thm "gfp_mono";
*}


end
