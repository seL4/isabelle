header {*Absoluteness Properties for Recursive Datatypes*}

theory Datatype_absolute = Formula + WF_absolute:


subsection{*The lfp of a continuous function can be expressed as a union*}

constdefs
  contin :: "[i=>i]=>o"
   "contin(h) == (\<forall>A. A\<noteq>0 --> h(\<Union>A) = (\<Union>X\<in>A. h(X)))"

lemma bnd_mono_iterates_subset: "[|bnd_mono(D, h); n \<in> nat|] ==> h^n (0) <= D"
apply (induct_tac n) 
 apply (simp_all add: bnd_mono_def, blast) 
done


lemma contin_iterates_eq: 
    "contin(h) \<Longrightarrow> h(\<Union>n\<in>nat. h^n (0)) = (\<Union>n\<in>nat. h^n (0))"
apply (simp add: contin_def) 
apply (rule trans) 
apply (rule equalityI) 
 apply (simp_all add: UN_subset_iff) 
 apply safe
 apply (erule_tac [2] natE) 
  apply (rule_tac a="succ(x)" in UN_I) 
   apply simp_all 
apply blast 
done

lemma lfp_subset_Union:
     "[|bnd_mono(D, h); contin(h)|] ==> lfp(D,h) <= (\<Union>n\<in>nat. h^n(0))"
apply (rule lfp_lowerbound) 
 apply (simp add: contin_iterates_eq) 
apply (simp add: contin_def bnd_mono_iterates_subset UN_subset_iff) 
done

lemma Union_subset_lfp:
     "bnd_mono(D,h) ==> (\<Union>n\<in>nat. h^n(0)) <= lfp(D,h)"
apply (simp add: UN_subset_iff)
apply (rule ballI)  
apply (induct_tac n, simp_all) 
apply (rule subset_trans [of _ "h(lfp(D,h))"])
 apply (blast dest: bnd_monoD2 [OF _ _ lfp_subset] )  
apply (erule lfp_lemma2) 
done

lemma lfp_eq_Union:
     "[|bnd_mono(D, h); contin(h)|] ==> lfp(D,h) = (\<Union>n\<in>nat. h^n(0))"
by (blast del: subsetI 
          intro: lfp_subset_Union Union_subset_lfp)


subsection {*lists without univ*}

lemmas datatype_univs = A_into_univ Inl_in_univ Inr_in_univ 
                        Pair_in_univ zero_in_univ

lemma list_fun_bnd_mono: "bnd_mono(univ(A), \<lambda>X. {0} + A*X)"
apply (rule bnd_monoI)
 apply (intro subset_refl zero_subset_univ A_subset_univ 
	      sum_subset_univ Sigma_subset_univ) 
 apply (blast intro!: subset_refl sum_mono Sigma_mono del: subsetI)
done

lemma list_fun_contin: "contin(\<lambda>X. {0} + A*X)"
by (simp add: contin_def, blast)

text{*Re-expresses lists using sum and product*}
lemma list_eq_lfp2: "list(A) = lfp(univ(A), \<lambda>X. {0} + A*X)"
apply (simp add: list_def) 
apply (rule equalityI) 
 apply (rule lfp_lowerbound) 
  prefer 2 apply (rule lfp_subset)
 apply (clarify, subst lfp_unfold [OF list_fun_bnd_mono])
 apply (simp add: Nil_def Cons_def)
 apply blast 
txt{*Opposite inclusion*}
apply (rule lfp_lowerbound) 
 prefer 2 apply (rule lfp_subset) 
apply (clarify, subst lfp_unfold [OF list.bnd_mono]) 
apply (simp add: Nil_def Cons_def)
apply (blast intro: datatype_univs
             dest: lfp_subset [THEN subsetD])
done

text{*Re-expresses lists using "iterates", no univ.*}
lemma list_eq_Union:
     "list(A) = (\<Union>n\<in>nat. (\<lambda>X. {0} + A*X) ^ n (0))"
by (simp add: list_eq_lfp2 lfp_eq_Union list_fun_bnd_mono list_fun_contin)


subsection {*Absoluteness for "Iterates"*}

constdefs

  iterates_MH :: "[i=>o, [i,i]=>o, i, i, i, i] => o"
   "iterates_MH(M,isF,v,n,g,z) ==
        is_nat_case(M, v, \<lambda>m u. \<exists>gm[M]. fun_apply(M,g,m,gm) & isF(gm,u),
                    n, z)"

  iterates_replacement :: "[i=>o, [i,i]=>o, i] => o"
   "iterates_replacement(M,isF,v) ==
      \<forall>n[M]. n\<in>nat --> 
         wfrec_replacement(M, iterates_MH(M,isF,v), Memrel(succ(n)))"

lemma (in M_axioms) iterates_MH_abs:
  "[| relativize1(M,isF,F); M(n); M(g); M(z) |] 
   ==> iterates_MH(M,isF,v,n,g,z) <-> z = nat_case(v, \<lambda>m. F(g`m), n)"
by (simp add: nat_case_abs [of _ "\<lambda>m. F(g ` m)"]
              relativize1_def iterates_MH_def)  

lemma (in M_axioms) iterates_imp_wfrec_replacement:
  "[|relativize1(M,isF,F); n \<in> nat; iterates_replacement(M,isF,v)|] 
   ==> wfrec_replacement(M, \<lambda>n f z. z = nat_case(v, \<lambda>m. F(f`m), n), 
                       Memrel(succ(n)))" 
by (simp add: iterates_replacement_def iterates_MH_abs)

theorem (in M_trancl) iterates_abs:
  "[| iterates_replacement(M,isF,v); relativize1(M,isF,F);
      n \<in> nat; M(v); M(z); \<forall>x[M]. M(F(x)) |] 
   ==> is_wfrec(M, iterates_MH(M,isF,v), Memrel(succ(n)), n, z) <->
       z = iterates(F,n,v)" 
apply (frule iterates_imp_wfrec_replacement, assumption+)
apply (simp add: wf_Memrel trans_Memrel relation_Memrel nat_into_M
                 relativize2_def iterates_MH_abs 
                 iterates_nat_def recursor_def transrec_def 
                 eclose_sing_Ord_eq nat_into_M
         trans_wfrec_abs [of _ _ _ _ "\<lambda>n g. nat_case(v, \<lambda>m. F(g`m), n)"])
done


lemma (in M_wfrank) iterates_closed [intro,simp]:
  "[| iterates_replacement(M,isF,v); relativize1(M,isF,F);
      n \<in> nat; M(v); \<forall>x[M]. M(F(x)) |] 
   ==> M(iterates(F,n,v))"
apply (frule iterates_imp_wfrec_replacement, assumption+)
apply (simp add: wf_Memrel trans_Memrel relation_Memrel nat_into_M
                 relativize2_def iterates_MH_abs 
                 iterates_nat_def recursor_def transrec_def 
                 eclose_sing_Ord_eq nat_into_M
         trans_wfrec_closed [of _ _ _ "\<lambda>n g. nat_case(v, \<lambda>m. F(g`m), n)"])
done


constdefs
  is_list_functor :: "[i=>o,i,i,i] => o"
    "is_list_functor(M,A,X,Z) == 
        \<exists>n1[M]. \<exists>AX[M]. 
         number1(M,n1) & cartprod(M,A,X,AX) & is_sum(M,n1,AX,Z)"

lemma (in M_axioms) list_functor_abs [simp]: 
     "[| M(A); M(X); M(Z) |] ==> is_list_functor(M,A,X,Z) <-> (Z = {0} + A*X)"
by (simp add: is_list_functor_def singleton_0 nat_into_M)


locale M_datatypes = M_wfrank +
 assumes list_replacement1: 
   "M(A) ==> iterates_replacement(M, is_list_functor(M,A), 0)"
  and list_replacement2: 
   "M(A) ==> strong_replacement(M, 
         \<lambda>n y. n\<in>nat & 
               (\<exists>sn[M]. \<exists>msn[M]. successor(M,n,sn) & membership(M,sn,msn) &
               is_wfrec(M, iterates_MH(M,is_list_functor(M,A), 0), 
                        msn, n, y)))"

lemma (in M_datatypes) list_replacement2': 
  "M(A) ==> strong_replacement(M, \<lambda>n y. n\<in>nat & y = (\<lambda>X. {0} + A * X)^n (0))"
apply (insert list_replacement2 [of A]) 
apply (rule strong_replacement_cong [THEN iffD1])  
apply (rule conj_cong [OF iff_refl iterates_abs [of "is_list_functor(M,A)"]]) 
apply (simp_all add: list_replacement1 relativize1_def) 
done

lemma (in M_datatypes) list_closed [intro,simp]:
     "M(A) ==> M(list(A))"
apply (insert list_replacement1)
by  (simp add: RepFun_closed2 list_eq_Union 
               list_replacement2' relativize1_def
               iterates_closed [of "is_list_functor(M,A)"])


end
