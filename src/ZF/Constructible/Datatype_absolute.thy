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

lemma (in M_trancl) iterates_relativize:
  "[|n \<in> nat; M(v); \<forall>x[M]. M(F(x));
     strong_replacement(M, 
       \<lambda>x z. \<exists>y[M]. \<exists>g[M]. pair(M,x,y,z) &
              M_is_recfun(M, \<lambda>n f z. z = nat_case(v, \<lambda>m. F(f`m), n), 
                          Memrel(succ(n)), x, g) &
              y = nat_case(v, \<lambda>m. F(g`m), x))|] 
   ==> iterates(F,n,v) = z <-> 
       (\<exists>g[M]. is_recfun(Memrel(succ(n)), n, 
                             \<lambda>n g. nat_case(v, \<lambda>m. F(g`m), n), g) &
            z = nat_case(v, \<lambda>m. F(g`m), n))"
by (simp add: iterates_nat_def recursor_def transrec_def 
              eclose_sing_Ord_eq trans_wfrec_relativize nat_into_M
              wf_Memrel trans_Memrel relation_Memrel
              is_recfun_abs [of "\<lambda>n g. nat_case(v, \<lambda>m. F(g`m), n)"])

lemma (in M_wfrank) iterates_closed [intro,simp]:
  "[|n \<in> nat; M(v); \<forall>x[M]. M(F(x));
     strong_replacement(M, 
       \<lambda>x z. \<exists>y[M]. \<exists>g[M]. pair(M, x, y, z) &
              is_recfun (Memrel(succ(n)), x,
                         \<lambda>n f. nat_case(v, \<lambda>m. F(f`m), n), g) &
              y = nat_case(v, \<lambda>m. F(g`m), x))|] 
   ==> M(iterates(F,n,v))"
by (simp add: iterates_nat_def recursor_def transrec_def 
              eclose_sing_Ord_eq trans_wfrec_closed nat_into_M
              wf_Memrel trans_Memrel relation_Memrel nat_case_closed)


constdefs
  is_list_functor :: "[i=>o,i,i,i] => o"
    "is_list_functor(M,A,X,Z) == 
        \<exists>n1[M]. \<exists>AX[M]. 
         number1(M,n1) & cartprod(M,A,X,AX) & is_sum(M,n1,AX,Z)"

  list_functor_case :: "[i=>o,i,i,i,i] => o"
    --{*Abbreviation for the definition of lists below*}
    "list_functor_case(M,A,g,x,y) == 
        is_nat_case(M, 0, 
             \<lambda>m u. \<exists>gm[M]. fun_apply(M,g,m,gm) & is_list_functor(M,A,gm,u),
             x, y)"

lemma (in M_axioms) list_functor_abs [simp]: 
     "[| M(A); M(X); M(Z) |] ==> is_list_functor(M,A,X,Z) <-> (Z = {0} + A*X)"
by (simp add: is_list_functor_def singleton_0 nat_into_M)

lemma (in M_axioms) list_functor_case_abs: 
     "[| M(A); M(n); M(y); M(g) |] 
      ==> list_functor_case(M,A,g,n,y) <-> 
          y = nat_case(0, \<lambda>m. {0} + A * g`m, n)"
by (simp add: list_functor_case_def nat_into_M)


locale M_datatypes = M_wfrank +
  assumes list_replacement1: 
       "[|M(A); n \<in> nat|] ==> 
	strong_replacement(M, 
	  \<lambda>x z. \<exists>y[M]. \<exists>g[M]. \<exists>sucn[M]. \<exists>memr[M]. 
		 pair(M,x,y,z) & successor(M,n,sucn) & 
		 membership(M,sucn,memr) &
		 M_is_recfun(M, \<lambda>n f z. list_functor_case(M,A,f,n,z), 
                             memr, x, g) &
                 list_functor_case(M,A,g,x,y))"
(*THEY NEED RELATIVIZATION*)
      and list_replacement2: 
           "M(A) ==> strong_replacement(M, \<lambda>x y. y = (\<lambda>X. {0} + A * X)^x (0))"



lemma (in M_datatypes) list_replacement1':
  "[|M(A); n \<in> nat|]
   ==> strong_replacement
	  (M, \<lambda>x z. \<exists>y[M]. z = \<langle>x,y\<rangle> &
               (\<exists>g[M]. is_recfun (Memrel(succ(n)), x,
		          \<lambda>n f. nat_case(0, \<lambda>m. {0} + A * f`m, n), g) &
 	       y = nat_case(0, \<lambda>m. {0} + A * g ` m, x)))"
apply (insert list_replacement1 [of A n], simp add: nat_into_M)
apply (simp add: nat_into_M list_functor_case_abs
                 is_recfun_abs [of "\<lambda>n f. nat_case(0, \<lambda>m. {0} + A * f`m, n)"])
done

lemma (in M_datatypes) list_replacement2': 
  "M(A) ==> strong_replacement(M, \<lambda>x y. y = (\<lambda>X. {0} + A * X)^x (0))"
by (insert list_replacement2, simp add: nat_into_M) 


lemma (in M_datatypes) list_closed [intro,simp]:
     "M(A) ==> M(list(A))"
by (simp add: list_eq_Union list_replacement1' list_replacement2')


end
