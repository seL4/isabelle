theory WF_absolute = WFrec:

subsection{*Transitive closure without fixedpoints*}

constdefs
  rtrancl_alt :: "[i,i]=>i"
    "rtrancl_alt(A,r) == 
       {p \<in> A*A. \<exists>n\<in>nat. \<exists>f \<in> succ(n) -> A.
                 (\<exists>x y. p = <x,y> &  f`0 = x & f`n = y) &
                       (\<forall>i\<in>n. <f`i, f`succ(i)> \<in> r)}"

lemma alt_rtrancl_lemma1 [rule_format]: 
    "n \<in> nat
     ==> \<forall>f \<in> succ(n) -> field(r). 
         (\<forall>i\<in>n. \<langle>f`i, f ` succ(i)\<rangle> \<in> r) --> \<langle>f`0, f`n\<rangle> \<in> r^*"
apply (induct_tac n) 
apply (simp_all add: apply_funtype rtrancl_refl, clarify) 
apply (rename_tac n f) 
apply (rule rtrancl_into_rtrancl) 
 prefer 2 apply assumption
apply (drule_tac x="restrict(f,succ(n))" in bspec)
 apply (blast intro: restrict_type2) 
apply (simp add: Ord_succ_mem_iff nat_0_le [THEN ltD] leI [THEN ltD] ltI) 
done

lemma rtrancl_alt_subset_rtrancl: "rtrancl_alt(field(r),r) <= r^*"
apply (simp add: rtrancl_alt_def)
apply (blast intro: alt_rtrancl_lemma1 )  
done

lemma rtrancl_subset_rtrancl_alt: "r^* <= rtrancl_alt(field(r),r)"
apply (simp add: rtrancl_alt_def, clarify) 
apply (frule rtrancl_type [THEN subsetD], clarify, simp) 
apply (erule rtrancl_induct) 
 txt{*Base case, trivial*}
 apply (rule_tac x=0 in bexI) 
  apply (rule_tac x="lam x:1. xa" in bexI) 
   apply simp_all 
txt{*Inductive step*}
apply clarify 
apply (rename_tac n f) 
apply (rule_tac x="succ(n)" in bexI) 
 apply (rule_tac x="lam i:succ(succ(n)). if i=succ(n) then z else f`i" in bexI)
  apply (simp add: Ord_succ_mem_iff nat_0_le [THEN ltD] leI [THEN ltD] ltI) 
  apply (blast intro: mem_asym)  
 apply typecheck 
 apply auto 
done

lemma rtrancl_alt_eq_rtrancl: "rtrancl_alt(field(r),r) = r^*"
by (blast del: subsetI
	  intro: rtrancl_alt_subset_rtrancl rtrancl_subset_rtrancl_alt) 


constdefs

  rtran_closure :: "[i=>o,i,i] => o"
    "rtran_closure(M,r,s) == 
        \<forall>A. M(A) --> is_field(M,r,A) -->
 	 (\<forall>p. M(p) --> 
          (p \<in> s <-> 
           (\<exists>n\<in>nat. M(n) & 
            (\<exists>n'. M(n') & successor(M,n,n') &
             (\<exists>f. M(f) & typed_function(M,n',A,f) &
              (\<exists>x\<in>A. M(x) & (\<exists>y\<in>A. M(y) & pair(M,x,y,p) &  
                   fun_apply(M,f,0,x) & fun_apply(M,f,n,y))) &
              (\<forall>i\<in>n. M(i) -->
                (\<forall>i'. M(i') --> successor(M,i,i') -->
                 (\<forall>fi. M(fi) --> fun_apply(M,f,i,fi) -->
                  (\<forall>fi'. M(fi') --> fun_apply(M,f,i',fi') -->
                   (\<forall>q. M(q) --> pair(M,fi,fi',q) --> q \<in> r))))))))))"

  tran_closure :: "[i=>o,i,i] => o"
    "tran_closure(M,r,t) == 
         \<exists>s. M(s) & rtran_closure(M,r,s) & composition(M,r,s,t)"


locale M_trancl = M_axioms +
(*THEY NEED RELATIVIZATION*)
  assumes rtrancl_separation:
     "[| M(r); M(A) |] ==>
	separation
	   (M, \<lambda>p. \<exists>n\<in>nat. \<exists>f \<in> succ(n) -> A.
                    (\<exists>x y. p = <x,y> &  f`0 = x & f`n = y) &
                          (\<forall>i\<in>n. <f`i, f`succ(i)> \<in> r))"
      and wellfounded_trancl_separation:
     "[| M(r); M(Z) |] ==> separation (M, \<lambda>x. \<exists>w. M(w) & \<langle>w,x\<rangle> \<in> r^+ & w \<in> Z)"


lemma (in M_trancl) rtran_closure_rtrancl: 
     "M(r) ==> rtran_closure(M,r,rtrancl(r))"
apply (simp add: rtran_closure_def rtrancl_alt_eq_rtrancl [symmetric] 
                 rtrancl_alt_def field_closed typed_apply_abs apply_closed
                 Ord_succ_mem_iff M_nat  nat_0_le [THEN ltD], clarify) 
apply (rule iffI) 
 apply clarify 
 apply simp 
 apply (rename_tac n f) 
 apply (rule_tac x=n in bexI) 
  apply (rule_tac x=f in exI) 
  apply simp
  apply (blast dest: finite_fun_closed dest: transM)
 apply assumption
apply clarify
apply (simp add: nat_0_le [THEN ltD] apply_funtype, blast)  
done

lemma (in M_trancl) rtrancl_closed [intro,simp]: 
     "M(r) ==> M(rtrancl(r))"
apply (insert rtrancl_separation [of r "field(r)"]) 
apply (simp add: rtrancl_alt_eq_rtrancl [symmetric] 
                 rtrancl_alt_def field_closed typed_apply_abs apply_closed
                 Ord_succ_mem_iff M_nat
                 nat_0_le [THEN ltD] leI [THEN ltD] ltI apply_funtype)
done

lemma (in M_trancl) rtrancl_abs [simp]: 
     "[| M(r); M(z) |] ==> rtran_closure(M,r,z) <-> z = rtrancl(r)"
apply (rule iffI)
 txt{*Proving the right-to-left implication*}
 prefer 2 apply (blast intro: rtran_closure_rtrancl) 
apply (rule M_equalityI)
apply (simp add: rtran_closure_def rtrancl_alt_eq_rtrancl [symmetric] 
                 rtrancl_alt_def field_closed typed_apply_abs apply_closed
                 Ord_succ_mem_iff M_nat
                 nat_0_le [THEN ltD] leI [THEN ltD] ltI apply_funtype) 
 prefer 2 apply assumption
 prefer 2 apply blast
apply (rule iffI, clarify) 
apply (simp add: nat_0_le [THEN ltD]  apply_funtype, blast, clarify)  
apply simp 
 apply (rename_tac n f) 
 apply (rule_tac x=n in bexI) 
  apply (rule_tac x=f in exI)
  apply (blast dest!: finite_fun_closed, assumption)
done


lemma (in M_trancl) trancl_closed [intro,simp]: 
     "M(r) ==> M(trancl(r))"
by (simp add: trancl_def comp_closed rtrancl_closed) 

lemma (in M_trancl) trancl_abs [simp]: 
     "[| M(r); M(z) |] ==> tran_closure(M,r,z) <-> z = trancl(r)"
by (simp add: tran_closure_def trancl_def) 


text{*Alternative proof of @{text wf_on_trancl}; inspiration for the 
      relativized version.  Original version is on theory WF.*}
lemma "[| wf[A](r);  r-``A <= A |] ==> wf[A](r^+)"
apply (simp add: wf_on_def wf_def) 
apply (safe intro!: equalityI)
apply (drule_tac x = "{x\<in>A. \<exists>w. \<langle>w,x\<rangle> \<in> r^+ & w \<in> Z}" in spec) 
apply (blast elim: tranclE) 
done


lemma (in M_trancl) wellfounded_on_trancl:
     "[| wellfounded_on(M,A,r);  r-``A <= A; M(r); M(A) |]
      ==> wellfounded_on(M,A,r^+)" 
apply (simp add: wellfounded_on_def) 
apply (safe intro!: equalityI)
apply (rename_tac Z x)
apply (subgoal_tac "M({x\<in>A. \<exists>w. M(w) & \<langle>w,x\<rangle> \<in> r^+ & w \<in> Z})") 
 prefer 2 
 apply (simp add: wellfounded_trancl_separation) 
apply (drule_tac x = "{x\<in>A. \<exists>w. M(w) & \<langle>w,x\<rangle> \<in> r^+ & w \<in> Z}" in spec) 
apply safe
apply (blast dest: transM, simp) 
apply (rename_tac y w) 
apply (drule_tac x=w in bspec, assumption, clarify)
apply (erule tranclE)
  apply (blast dest: transM)   (*transM is needed to prove M(xa)*)
 apply blast 
done


text{*Relativized to M: Every well-founded relation is a subset of some
inverse image of an ordinal.  Key step is the construction (in M) of a 
rank function.*}


(*NEEDS RELATIVIZATION*)
locale M_recursion = M_trancl +
  assumes wfrank_separation':
     "[| M(r); M(A) |] ==>
	separation
	   (M, \<lambda>x. x \<in> A --> 
		~(\<exists>f. M(f) \<and> is_recfun(r^+, x, %x f. range(f), f)))"
 and wfrank_strong_replacement':
     "M(r) ==>
      strong_replacement(M, \<lambda>x z. \<exists>y f. M(y) & M(f) &
		  pair(M,x,y,z) & is_recfun(r^+, x, %x f. range(f), f) & 
		  y = range(f))"
 and Ord_wfrank_separation:
     "[| M(r); M(A) |] ==>
      separation (M, \<lambda>x. x \<in> A \<longrightarrow>
                \<not> (\<forall>f. M(f) \<longrightarrow>
                       is_recfun(r^+, x, \<lambda>x. range, f) \<longrightarrow> Ord(range(f))))"

constdefs 
 wellfoundedrank :: "[i=>o,i,i] => i"
    "wellfoundedrank(M,r,A) == 
        {p. x\<in>A, \<exists>y f. M(y) & M(f) & 
                       p = <x,y> & is_recfun(r^+, x, %x f. range(f), f) & 
                       y = range(f)}"

lemma (in M_recursion) exists_wfrank:
    "[| wellfounded(M,r); r \<subseteq> A*A; a\<in>A; M(r); M(A) |]
     ==> \<exists>f. M(f) & is_recfun(r^+, a, %x f. range(f), f)"
apply (rule wellfounded_exists_is_recfun [of A]) 
apply (blast intro: wellfounded_on_trancl wellfounded_imp_wellfounded_on)
apply (rule trans_trancl [THEN trans_imp_trans_on], assumption+)
apply (simp_all add: trancl_subset_times) 
done

lemma (in M_recursion) M_wellfoundedrank:
    "[| wellfounded(M,r); r \<subseteq> A*A; M(r); M(A) |] 
     ==> M(wellfoundedrank(M,r,A))"
apply (insert wfrank_strong_replacement' [of r]) 
apply (simp add: wellfoundedrank_def) 
apply (rule strong_replacement_closed) 
   apply assumption+
 apply (rule univalent_is_recfun) 
     apply (blast intro: wellfounded_on_trancl wellfounded_imp_wellfounded_on)
    apply (rule trans_on_trancl) 
   apply (simp add: trancl_subset_times) 
  apply blast+
done

lemma (in M_recursion) Ord_wfrank_range [rule_format]:
    "[| wellfounded(M,r); r \<subseteq> A*A; a\<in>A; M(r); M(A) |]
     ==> \<forall>f. M(f) --> is_recfun(r^+, a, %x f. range(f), f) --> Ord(range(f))"
apply (subgoal_tac "wellfounded_on(M, A, r^+)") 
 prefer 2
 apply (blast intro: wellfounded_on_trancl wellfounded_imp_wellfounded_on)
apply (erule wellfounded_on_induct2, assumption+)
apply (simp add: trancl_subset_times) 
apply (blast intro: Ord_wfrank_separation, clarify)
txt{*The reasoning in both cases is that we get @{term y} such that
   @{term "\<langle>y, x\<rangle> \<in> r^+"}.  We find that 
   @{term "f`y = restrict(f, r^+ -`` {y})"}. *}
apply (rule OrdI [OF _ Ord_is_Transset])
 txt{*An ordinal is a transitive set...*}
 apply (simp add: Transset_def) 
 apply clarify
 apply (frule apply_recfun2, assumption) 
 apply (force simp add: restrict_iff)
txt{*...of ordinals.  This second case requires the induction hyp.*} 
apply clarify 
apply (rename_tac i y)
apply (frule apply_recfun2, assumption) 
apply (frule is_recfun_imp_in_r, assumption) 
apply (frule is_recfun_restrict) 
    (*simp_all won't work*)
    apply (simp add: trans_on_trancl trancl_subset_times)+  
apply (drule spec [THEN mp], assumption)
apply (subgoal_tac "M(restrict(f, r^+ -`` {y}))")
 apply (drule_tac x="restrict(f, r^+ -`` {y})" in spec) 
 apply (simp add: function_apply_equality [OF _ is_recfun_imp_function])
apply (blast dest: pair_components_in_M)
done

lemma (in M_recursion) Ord_range_wellfoundedrank:
    "[| wellfounded(M,r); r \<subseteq> A*A;  M(r); M(A) |] 
     ==> Ord (range(wellfoundedrank(M,r,A)))"
apply (subgoal_tac "wellfounded_on(M, A, r^+)") 
 prefer 2
 apply (blast intro: wellfounded_on_trancl wellfounded_imp_wellfounded_on)
apply (frule trancl_subset_times) 
apply (simp add: wellfoundedrank_def)
apply (rule OrdI [OF _ Ord_is_Transset])
 prefer 2
 txt{*by our previous result the range consists of ordinals.*} 
 apply (blast intro: Ord_wfrank_range) 
txt{*We still must show that the range is a transitive set.*}
apply (simp add: Transset_def, clarify)
apply simp
apply (rename_tac x i f u)   
apply (frule is_recfun_imp_in_r, assumption) 
apply (subgoal_tac "M(u) & M(i) & M(x)") 
 prefer 2 apply (blast dest: transM, clarify) 
apply (rule_tac a=u in rangeI) 
apply (rule ReplaceI) 
  apply (rule_tac x=i in exI, simp) 
  apply (rule_tac x="restrict(f, r^+ -`` {u})" in exI)
  apply (blast intro: is_recfun_restrict trans_on_trancl dest: apply_recfun2)
 apply blast
txt{*Unicity requirement of Replacement*} 
apply clarify
apply (frule apply_recfun2, assumption) 
apply (simp add: trans_on_trancl is_recfun_cut)+
done

lemma (in M_recursion) function_wellfoundedrank:
    "[| wellfounded(M,r); r \<subseteq> A*A;  M(r); M(A)|]
     ==> function(wellfoundedrank(M,r,A))"
apply (simp add: wellfoundedrank_def function_def, clarify) 
txt{*Uniqueness: repeated below!*}
apply (drule is_recfun_functional, assumption)
    apply (blast intro: wellfounded_on_trancl wellfounded_imp_wellfounded_on)
    apply (simp_all add: trancl_subset_times 
                         trans_trancl [THEN trans_imp_trans_on]) 
apply (blast dest: transM) 
done

lemma (in M_recursion) domain_wellfoundedrank:
    "[| wellfounded(M,r); r \<subseteq> A*A;  M(r); M(A)|]
     ==> domain(wellfoundedrank(M,r,A)) = A"
apply (simp add: wellfoundedrank_def function_def) 
apply (rule equalityI, auto)
apply (frule transM, assumption)  
apply (frule exists_wfrank, assumption+)
apply clarify 
apply (rule domainI) 
apply (rule ReplaceI)
apply (rule_tac x="range(f)" in exI)
apply simp  
apply (rule_tac x=f in exI, blast)
apply assumption
txt{*Uniqueness (for Replacement): repeated above!*}
apply clarify
apply (drule is_recfun_functional, assumption)
    apply (blast intro: wellfounded_on_trancl wellfounded_imp_wellfounded_on)
    apply (simp_all add: trancl_subset_times 
                         trans_trancl [THEN trans_imp_trans_on]) 
done

lemma (in M_recursion) wellfoundedrank_type:
    "[| wellfounded(M,r); r \<subseteq> A*A;  M(r); M(A)|]
     ==> wellfoundedrank(M,r,A) \<in> A -> range(wellfoundedrank(M,r,A))"
apply (frule function_wellfoundedrank, assumption+) 
apply (frule function_imp_Pi) 
 apply (simp add: wellfoundedrank_def relation_def) 
 apply blast  
apply (simp add: domain_wellfoundedrank)
done

lemma (in M_recursion) Ord_wellfoundedrank:
    "[| wellfounded(M,r); a \<in> A; r \<subseteq> A*A;  M(r); M(A) |] 
     ==> Ord(wellfoundedrank(M,r,A) ` a)"
by (blast intro: apply_funtype [OF wellfoundedrank_type]
                 Ord_in_Ord [OF Ord_range_wellfoundedrank])

lemma (in M_recursion) wellfoundedrank_eq:
     "[| is_recfun(r^+, a, %x. range, f);
         wellfounded(M,r);  a \<in> A; r \<subseteq> A*A;  M(f); M(r); M(A)|] 
      ==> wellfoundedrank(M,r,A) ` a = range(f)"
apply (rule apply_equality) 
 prefer 2 apply (blast intro: wellfoundedrank_type ) 
apply (simp add: wellfoundedrank_def)
apply (rule ReplaceI)
  apply (rule_tac x="range(f)" in exI) 
  apply blast 
 apply assumption
txt{*Unicity requirement of Replacement*} 
apply clarify
apply (drule is_recfun_functional, assumption)
    apply (blast intro: wellfounded_on_trancl wellfounded_imp_wellfounded_on)
    apply (simp_all add: trancl_subset_times 
                         trans_trancl [THEN trans_imp_trans_on])
apply (blast dest: transM) 
done

end
