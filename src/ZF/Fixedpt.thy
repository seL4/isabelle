(*  Title:      ZF/Fixedpt.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

header{*Least and Greatest Fixed Points; the Knaster-Tarski Theorem*}

theory Fixedpt imports equalities begin

definition 
  (*monotone operator from Pow(D) to itself*)
  bnd_mono :: "[i,i=>i]=>o"  where
     "bnd_mono(D,h) == h(D)<=D & (\<forall>W X. W<=X \<longrightarrow> X<=D \<longrightarrow> h(W) \<subseteq> h(X))"

definition 
  lfp      :: "[i,i=>i]=>i"  where
     "lfp(D,h) == \<Inter>({X: Pow(D). h(X) \<subseteq> X})"

definition 
  gfp      :: "[i,i=>i]=>i"  where
     "gfp(D,h) == \<Union>({X: Pow(D). X \<subseteq> h(X)})"

text{*The theorem is proved in the lattice of subsets of @{term D}, 
      namely @{term "Pow(D)"}, with Inter as the greatest lower bound.*}

subsection{*Monotone Operators*}

lemma bnd_monoI:
    "[| h(D)<=D;   
        !!W X. [| W<=D;  X<=D;  W<=X |] ==> h(W) \<subseteq> h(X)   
     |] ==> bnd_mono(D,h)"
by (unfold bnd_mono_def, clarify, blast)  

lemma bnd_monoD1: "bnd_mono(D,h) ==> h(D) \<subseteq> D"
apply (unfold bnd_mono_def)
apply (erule conjunct1)
done

lemma bnd_monoD2: "[| bnd_mono(D,h);  W<=X;  X<=D |] ==> h(W) \<subseteq> h(X)"
by (unfold bnd_mono_def, blast)

lemma bnd_mono_subset:
    "[| bnd_mono(D,h);  X<=D |] ==> h(X) \<subseteq> D"
by (unfold bnd_mono_def, clarify, blast) 

lemma bnd_mono_Un:
     "[| bnd_mono(D,h);  A \<subseteq> D;  B \<subseteq> D |] ==> h(A) \<union> h(B) \<subseteq> h(A \<union> B)"
apply (unfold bnd_mono_def)
apply (rule Un_least, blast+)
done

(*unused*)
lemma bnd_mono_UN:
     "[| bnd_mono(D,h);  \<forall>i\<in>I. A(i) \<subseteq> D |] 
      ==> (\<Union>i\<in>I. h(A(i))) \<subseteq> h((\<Union>i\<in>I. A(i)))"
apply (unfold bnd_mono_def) 
apply (rule UN_least)
apply (elim conjE) 
apply (drule_tac x="A(i)" in spec)
apply (drule_tac x="(\<Union>i\<in>I. A(i))" in spec) 
apply blast 
done

(*Useful??*)
lemma bnd_mono_Int:
     "[| bnd_mono(D,h);  A \<subseteq> D;  B \<subseteq> D |] ==> h(A \<inter> B) \<subseteq> h(A) \<inter> h(B)"
apply (rule Int_greatest) 
apply (erule bnd_monoD2, rule Int_lower1, assumption) 
apply (erule bnd_monoD2, rule Int_lower2, assumption) 
done

subsection{*Proof of Knaster-Tarski Theorem using @{term lfp}*}

(*lfp is contained in each pre-fixedpoint*)
lemma lfp_lowerbound: 
    "[| h(A) \<subseteq> A;  A<=D |] ==> lfp(D,h) \<subseteq> A"
by (unfold lfp_def, blast)

(*Unfolding the defn of Inter dispenses with the premise bnd_mono(D,h)!*)
lemma lfp_subset: "lfp(D,h) \<subseteq> D"
by (unfold lfp_def Inter_def, blast)

(*Used in datatype package*)
lemma def_lfp_subset:  "A == lfp(D,h) ==> A \<subseteq> D"
apply simp
apply (rule lfp_subset)
done

lemma lfp_greatest:  
    "[| h(D) \<subseteq> D;  !!X. [| h(X) \<subseteq> X;  X<=D |] ==> A<=X |] ==> A \<subseteq> lfp(D,h)"
by (unfold lfp_def, blast) 

lemma lfp_lemma1:  
    "[| bnd_mono(D,h);  h(A)<=A;  A<=D |] ==> h(lfp(D,h)) \<subseteq> A"
apply (erule bnd_monoD2 [THEN subset_trans])
apply (rule lfp_lowerbound, assumption+)
done

lemma lfp_lemma2: "bnd_mono(D,h) ==> h(lfp(D,h)) \<subseteq> lfp(D,h)"
apply (rule bnd_monoD1 [THEN lfp_greatest])
apply (rule_tac [2] lfp_lemma1)
apply (assumption+)
done

lemma lfp_lemma3: 
    "bnd_mono(D,h) ==> lfp(D,h) \<subseteq> h(lfp(D,h))"
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

subsection{*General Induction Rule for Least Fixedpoints*}

lemma Collect_is_pre_fixedpt:
    "[| bnd_mono(D,h);  !!x. x \<in> h(Collect(lfp(D,h),P)) ==> P(x) |]
     ==> h(Collect(lfp(D,h),P)) \<subseteq> Collect(lfp(D,h),P)"
by (blast intro: lfp_lemma2 [THEN subsetD] bnd_monoD2 [THEN subsetD] 
                 lfp_subset [THEN subsetD]) 

(*This rule yields an induction hypothesis in which the components of a
  data structure may be assumed to be elements of lfp(D,h)*)
lemma induct:
    "[| bnd_mono(D,h);  a \<in> lfp(D,h);                    
        !!x. x \<in> h(Collect(lfp(D,h),P)) ==> P(x)         
     |] ==> P(a)"
apply (rule Collect_is_pre_fixedpt
              [THEN lfp_lowerbound, THEN subsetD, THEN CollectD2])
apply (rule_tac [3] lfp_subset [THEN Collect_subset [THEN subset_trans]], 
       blast+)
done

(*Definition form, to control unfolding*)
lemma def_induct:
    "[| A == lfp(D,h);  bnd_mono(D,h);  a:A;    
        !!x. x \<in> h(Collect(A,P)) ==> P(x)  
     |] ==> P(a)"
by (rule induct, blast+)

(*This version is useful when "A" is not a subset of D
  second premise could simply be h(D \<inter> A) \<subseteq> D or !!X. X<=D ==> h(X)<=D *)
lemma lfp_Int_lowerbound:
    "[| h(D \<inter> A) \<subseteq> A;  bnd_mono(D,h) |] ==> lfp(D,h) \<subseteq> A" 
apply (rule lfp_lowerbound [THEN subset_trans])
apply (erule bnd_mono_subset [THEN Int_greatest], blast+)
done

(*Monotonicity of lfp, where h precedes i under a domain-like partial order
  monotonicity of h is not strictly necessary; h must be bounded by D*)
lemma lfp_mono:
  assumes hmono: "bnd_mono(D,h)"
      and imono: "bnd_mono(E,i)"
      and subhi: "!!X. X<=D ==> h(X) \<subseteq> i(X)"
    shows "lfp(D,h) \<subseteq> lfp(E,i)"
apply (rule bnd_monoD1 [THEN lfp_greatest])
apply (rule imono)
apply (rule hmono [THEN [2] lfp_Int_lowerbound])
apply (rule Int_lower1 [THEN subhi, THEN subset_trans])
apply (rule imono [THEN bnd_monoD2, THEN subset_trans], auto) 
done

(*This (unused) version illustrates that monotonicity is not really needed,
  but both lfp's must be over the SAME set D;  Inter is anti-monotonic!*)
lemma lfp_mono2:
    "[| i(D) \<subseteq> D;  !!X. X<=D ==> h(X) \<subseteq> i(X)  |] ==> lfp(D,h) \<subseteq> lfp(D,i)"
apply (rule lfp_greatest, assumption)
apply (rule lfp_lowerbound, blast, assumption)
done

lemma lfp_cong:
     "[|D=D'; !!X. X \<subseteq> D' ==> h(X) = h'(X)|] ==> lfp(D,h) = lfp(D',h')"
apply (simp add: lfp_def)
apply (rule_tac t=Inter in subst_context)
apply (rule Collect_cong, simp_all) 
done 


subsection{*Proof of Knaster-Tarski Theorem using @{term gfp}*}

(*gfp contains each post-fixedpoint that is contained in D*)
lemma gfp_upperbound: "[| A \<subseteq> h(A);  A<=D |] ==> A \<subseteq> gfp(D,h)"
apply (unfold gfp_def)
apply (rule PowI [THEN CollectI, THEN Union_upper])
apply (assumption+)
done

lemma gfp_subset: "gfp(D,h) \<subseteq> D"
by (unfold gfp_def, blast)

(*Used in datatype package*)
lemma def_gfp_subset: "A==gfp(D,h) ==> A \<subseteq> D"
apply simp
apply (rule gfp_subset)
done

lemma gfp_least: 
    "[| bnd_mono(D,h);  !!X. [| X \<subseteq> h(X);  X<=D |] ==> X<=A |] ==>  
     gfp(D,h) \<subseteq> A"
apply (unfold gfp_def)
apply (blast dest: bnd_monoD1) 
done

lemma gfp_lemma1: 
    "[| bnd_mono(D,h);  A<=h(A);  A<=D |] ==> A \<subseteq> h(gfp(D,h))"
apply (rule subset_trans, assumption)
apply (erule bnd_monoD2)
apply (rule_tac [2] gfp_subset)
apply (simp add: gfp_upperbound)
done

lemma gfp_lemma2: "bnd_mono(D,h) ==> gfp(D,h) \<subseteq> h(gfp(D,h))"
apply (rule gfp_least)
apply (rule_tac [2] gfp_lemma1)
apply (assumption+)
done

lemma gfp_lemma3: 
    "bnd_mono(D,h) ==> h(gfp(D,h)) \<subseteq> gfp(D,h)"
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


subsection{*Coinduction Rules for Greatest Fixed Points*}

(*weak version*)
lemma weak_coinduct: "[| a: X;  X \<subseteq> h(X);  X \<subseteq> D |] ==> a \<in> gfp(D,h)"
by (blast intro: gfp_upperbound [THEN subsetD])

lemma coinduct_lemma:
    "[| X \<subseteq> h(X \<union> gfp(D,h));  X \<subseteq> D;  bnd_mono(D,h) |] ==>   
     X \<union> gfp(D,h) \<subseteq> h(X \<union> gfp(D,h))"
apply (erule Un_least)
apply (rule gfp_lemma2 [THEN subset_trans], assumption)
apply (rule Un_upper2 [THEN subset_trans])
apply (rule bnd_mono_Un, assumption+) 
apply (rule gfp_subset)
done

(*strong version*)
lemma coinduct:
     "[| bnd_mono(D,h);  a: X;  X \<subseteq> h(X \<union> gfp(D,h));  X \<subseteq> D |]
      ==> a \<in> gfp(D,h)"
apply (rule weak_coinduct)
apply (erule_tac [2] coinduct_lemma)
apply (simp_all add: gfp_subset Un_subset_iff) 
done

(*Definition form, to control unfolding*)
lemma def_coinduct:
    "[| A == gfp(D,h);  bnd_mono(D,h);  a: X;  X \<subseteq> h(X \<union> A);  X \<subseteq> D |] ==>  
     a \<in> A"
apply simp
apply (rule coinduct, assumption+)
done

(*The version used in the induction/coinduction package*)
lemma def_Collect_coinduct:
    "[| A == gfp(D, %w. Collect(D,P(w)));  bnd_mono(D, %w. Collect(D,P(w)));   
        a: X;  X \<subseteq> D;  !!z. z: X ==> P(X \<union> A, z) |] ==>  
     a \<in> A"
apply (rule def_coinduct, assumption+, blast+)
done

(*Monotonicity of gfp!*)
lemma gfp_mono:
    "[| bnd_mono(D,h);  D \<subseteq> E;                  
        !!X. X<=D ==> h(X) \<subseteq> i(X)  |] ==> gfp(D,h) \<subseteq> gfp(E,i)"
apply (rule gfp_upperbound)
apply (rule gfp_lemma2 [THEN subset_trans], assumption)
apply (blast del: subsetI intro: gfp_subset) 
apply (blast del: subsetI intro: subset_trans gfp_subset) 
done

end
