theory WF_absolute = WF_extras + WFrec:


subsection{*Transitive closure without fixedpoints*}

(*Ordinal.thy: just after succ_le_iff?*)
lemma Ord_succ_mem_iff: "Ord(j) ==> succ(i) \<in> succ(j) <-> i\<in>j"
apply (insert succ_le_iff [of i j]) 
apply (simp add: lt_def) 
done

constdefs
  rtrancl_alt :: "[i,i]=>i"
    "rtrancl_alt(A,r) == 
       {p \<in> A*A. \<exists>n\<in>nat. \<exists>f \<in> succ(n) -> A.
                 \<exists>x y. p = <x,y> &  f`0 = x & f`n = y &
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
apply (frule rtrancl_type [THEN subsetD], clarify) 
apply simp 
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


text{*Relativized to M: Every well-founded relation is a subset of some
inverse image of an ordinal.  Key step is the construction (in M) of a 
rank function.*}


(*NEEDS RELATIVIZATION*)
locale M_recursion = M_axioms +
  assumes wfrank_separation':
     "[| M(r); M(a); r \<subseteq> A*A |] ==>
	separation
	   (M, \<lambda>x. x \<in> A --> 
		~(\<exists>f. M(f) \<and> 
		      is_recfun(r, x, %x f. \<Union>y \<in> r-``{x}. succ(f`y), f)))"
 and wfrank_strong_replacement':
     "[| M(r); M(a); r \<subseteq> A*A |] ==>
      strong_replacement(M, \<lambda>x z. \<exists>y g. M(y) & M(g) &
		  pair(M,x,y,z) & 
		  is_recfun(r, x, %x f. \<Union>y \<in> r-``{x}. succ(f`y), f) & 
		  y = (\<Union>y \<in> r-``{x}. succ(g`y)))"


constdefs (*????????????????NEEDED?*)
 is_wfrank_fun :: "[i=>o,i,i,i] => o"
    "is_wfrank_fun(M,r,a,f) == 
       function(f) & domain(f) = r-``{a} & 
       (\<forall>x. M(x) --> <x,a> \<in> r --> f`x = (\<Union>y \<in> r-``{x}. succ(f`y)))"




lemma (in M_recursion) exists_wfrank:
    "[| wellfounded(M,r); r \<subseteq> A*A; a\<in>A; M(r); M(A) |]
     ==> \<exists>f. M(f) & is_recfun(r, a, %x g. (\<Union>y \<in> r-``{x}. succ(g`y)), f)"
apply (rule exists_is_recfun [of A r]) 
apply (erule wellfounded_imp_wellfounded_on) 
apply assumption; 
apply (rule trans_Memrel [THEN trans_imp_trans_on], simp)  
apply (rule succI1) 
apply (blast intro: wfrank_separation') 
apply (blast intro: wfrank_strong_replacement') 
apply (simp_all add: Memrel_type Memrel_closed Un_closed image_closed)
done

lemma (in M_recursion) exists_wfrank_fun:
    "[| Ord(j);  M(i);  M(j) |] ==> \<exists>f. M(f) & is_wfrank_fun(M,i,succ(j),f)"
apply (rule exists_wfrank [THEN exE])
apply (erule Ord_succ, assumption, simp) 
apply (rename_tac f, clarify) 
apply (frule is_recfun_type)
apply (rule_tac x=f in exI) 
apply (simp add: fun_is_function domain_of_fun lt_Memrel apply_recfun lt_def
                 is_wfrank_fun_eq Ord_trans [OF _ succI1])
done

lemma (in M_recursion) is_wfrank_fun_apply:
    "[| x < j; M(i); M(j); M(f); is_wfrank_fun(M,r,a,f) |] 
     ==> f`x = i Un (\<Union>k\<in>x. {f ` k})"
apply (simp add: is_wfrank_fun_eq lt_Ord2) 
apply (frule lt_closed, simp) 
apply (subgoal_tac "x <= domain(f)")
 apply (simp add: Ord_trans [OF _ succI1] image_function)
 apply (blast intro: elim:); 
apply (blast intro: dest!: leI [THEN le_imp_subset] ) 
done

lemma (in M_recursion) is_wfrank_fun_eq_wfrank [rule_format]:
    "[| is_wfrank_fun(M,i,J,f); M(i); M(J); M(f); Ord(i); Ord(j) |] 
     ==> j<J --> f`j = i++j"
apply (erule_tac i=j in trans_induct, clarify) 
apply (subgoal_tac "\<forall>k\<in>x. k<J")
 apply (simp (no_asm_simp) add: is_wfrank_def wfrank_unfold is_wfrank_fun_apply)
apply (blast intro: lt_trans ltI lt_Ord) 
done

lemma (in M_recursion) wfrank_abs_fun_apply_iff:
    "[| M(i); M(J); M(f); M(k); j<J; is_wfrank_fun(M,i,J,f) |] 
     ==> fun_apply(M,f,j,k) <-> f`j = k"
by (auto simp add: lt_def is_wfrank_fun_eq subsetD apply_abs) 

lemma (in M_recursion) Ord_wfrank_abs:
    "[| M(i); M(j); M(k); Ord(i); Ord(j) |] ==> is_wfrank(M,r,a,k) <-> k = i++j"
apply (simp add: is_wfrank_def wfrank_abs_fun_apply_iff is_wfrank_fun_eq_wfrank)
apply (frule exists_wfrank_fun [of j i], blast+)
done

lemma (in M_recursion) wfrank_abs:
    "[| M(i); M(j); M(k) |] ==> is_wfrank(M,r,a,k) <-> k = i++j"
apply (case_tac "Ord(i) & Ord(j)")
 apply (simp add: Ord_wfrank_abs)
apply (auto simp add: is_wfrank_def wfrank_eq_if_raw_wfrank)
done

lemma (in M_recursion) wfrank_closed [intro]:
    "[| M(i); M(j) |] ==> M(i++j)"
apply (simp add: wfrank_eq_if_raw_wfrank, clarify) 
apply (simp add: raw_wfrank_eq_wfrank) 
apply (frule exists_wfrank_fun [of j i], auto)
apply (simp add: apply_closed is_wfrank_fun_eq_wfrank [symmetric]) 
done



constdefs
  wfrank :: "[i,i]=>i"
    "wfrank(r,a) == wfrec(r, a, %x f. \<Union>y \<in> r-``{x}. succ(f`y))"

constdefs
  wftype :: "i=>i"
    "wftype(r) == \<Union>y \<in> range(r). succ(wfrank(r,y))"

lemma (in M_axioms) wfrank: "wellfounded(M,r) ==> wfrank(r,a) = (\<Union>y \<in> r-``{a}. succ(wfrank(r,y)))"
by (subst wfrank_def [THEN def_wfrec], simp_all)

lemma (in M_axioms) Ord_wfrank: "wellfounded(M,r) ==> Ord(wfrank(r,a))"
apply (rule_tac a="a" in wf_induct, assumption)
apply (subst wfrank, assumption)
apply (rule Ord_succ [THEN Ord_UN], blast) 
done

lemma (in M_axioms) wfrank_lt: "[|wellfounded(M,r); <a,b> \<in> r|] ==> wfrank(r,a) < wfrank(r,b)"
apply (rule_tac a1 = "b" in wfrank [THEN ssubst], assumption)
apply (rule UN_I [THEN ltI])
apply (simp add: Ord_wfrank vimage_iff)+
done

lemma (in M_axioms) Ord_wftype: "wellfounded(M,r) ==> Ord(wftype(r))"
by (simp add: wftype_def Ord_wfrank)

lemma (in M_axioms) wftypeI: "\<lbrakk>wellfounded(M,r);  x \<in> field(r)\<rbrakk> \<Longrightarrow> wfrank(r,x) \<in> wftype(r)"
apply (simp add: wftype_def) 
apply (blast intro: wfrank_lt [THEN ltD]) 
done


lemma (in M_axioms) wf_imp_subset_rvimage:
     "[|wellfounded(M,r); r \<subseteq> A*A|] ==> \<exists>i f. Ord(i) & r <= rvimage(A, f, Memrel(i))"
apply (rule_tac x="wftype(r)" in exI) 
apply (rule_tac x="\<lambda>x\<in>A. wfrank(r,x)" in exI) 
apply (simp add: Ord_wftype, clarify) 
apply (frule subsetD, assumption, clarify) 
apply (simp add: rvimage_iff wfrank_lt [THEN ltD])
apply (blast intro: wftypeI  ) 
done




end
