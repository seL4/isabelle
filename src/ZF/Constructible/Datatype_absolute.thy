header {*Absoluteness Properties for Recursive Datatypes*}

theory Datatype_absolute = Formula + WF_absolute:


subsection{*The lfp of a continuous function can be expressed as a union*}

constdefs
  directed :: "i=>o"
   "directed(A) == A\<noteq>0 & (\<forall>x\<in>A. \<forall>y\<in>A. x \<union> y \<in> A)"

  contin :: "(i=>i) => o"
   "contin(h) == (\<forall>A. directed(A) --> h(\<Union>A) = (\<Union>X\<in>A. h(X)))"

lemma bnd_mono_iterates_subset: "[|bnd_mono(D, h); n \<in> nat|] ==> h^n (0) <= D"
apply (induct_tac n) 
 apply (simp_all add: bnd_mono_def, blast) 
done

lemma bnd_mono_increasing [rule_format]:
     "[|i \<in> nat; j \<in> nat; bnd_mono(D,h)|] ==> i \<le> j --> h^i(0) \<subseteq> h^j(0)"
apply (rule_tac m=i and n=j in diff_induct, simp_all)
apply (blast del: subsetI
	     intro: bnd_mono_iterates_subset bnd_monoD2 [of concl: h] ) 
done

lemma directed_iterates: "bnd_mono(D,h) ==> directed({h^n (0). n\<in>nat})"
apply (simp add: directed_def, clarify) 
apply (rename_tac i j)
apply (rule_tac x="i \<union> j" in bexI) 
apply (rule_tac i = i and j = j in Ord_linear_le)
apply (simp_all add: subset_Un_iff [THEN iffD1] le_imp_subset
                     subset_Un_iff2 [THEN iffD1])
apply (simp_all add: subset_Un_iff [THEN iff_sym] bnd_mono_increasing
                     subset_Un_iff2 [THEN iff_sym])
done


lemma contin_iterates_eq: 
    "[|bnd_mono(D, h); contin(h)|] 
     ==> h(\<Union>n\<in>nat. h^n (0)) = (\<Union>n\<in>nat. h^n (0))"
apply (simp add: contin_def directed_iterates) 
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


subsubsection{*Some Standard Datatype Constructions Preserve Continuity*}

lemma contin_imp_mono: "[|X\<subseteq>Y; contin(F)|] ==> F(X) \<subseteq> F(Y)"
apply (simp add: contin_def) 
apply (drule_tac x="{X,Y}" in spec) 
apply (simp add: directed_def subset_Un_iff2 Un_commute) 
done

lemma sum_contin: "[|contin(F); contin(G)|] ==> contin(\<lambda>X. F(X) + G(X))"
by (simp add: contin_def, blast)

lemma prod_contin: "[|contin(F); contin(G)|] ==> contin(\<lambda>X. F(X) * G(X))" 
apply (subgoal_tac "\<forall>B C. F(B) \<subseteq> F(B \<union> C)")
 prefer 2 apply (simp add: Un_upper1 contin_imp_mono) 
apply (subgoal_tac "\<forall>B C. G(C) \<subseteq> G(B \<union> C)")
 prefer 2 apply (simp add: Un_upper2 contin_imp_mono) 
apply (simp add: contin_def, clarify) 
apply (rule equalityI) 
 prefer 2 apply blast 
apply clarify 
apply (rename_tac B C) 
apply (rule_tac a="B \<union> C" in UN_I) 
 apply (simp add: directed_def, blast)  
done

lemma const_contin: "contin(\<lambda>X. A)"
by (simp add: contin_def directed_def)

lemma id_contin: "contin(\<lambda>X. X)"
by (simp add: contin_def)



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


subsection {*lists without univ*}

lemmas datatype_univs = Inl_in_univ Inr_in_univ 
                        Pair_in_univ nat_into_univ A_into_univ 

lemma list_fun_bnd_mono: "bnd_mono(univ(A), \<lambda>X. {0} + A*X)"
apply (rule bnd_monoI)
 apply (intro subset_refl zero_subset_univ A_subset_univ 
	      sum_subset_univ Sigma_subset_univ) 
apply (rule subset_refl sum_mono Sigma_mono | assumption)+
done

lemma list_fun_contin: "contin(\<lambda>X. {0} + A*X)"
by (intro sum_contin prod_contin id_contin const_contin) 

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


constdefs
  is_list_functor :: "[i=>o,i,i,i] => o"
    "is_list_functor(M,A,X,Z) == 
        \<exists>n1[M]. \<exists>AX[M]. 
         number1(M,n1) & cartprod(M,A,X,AX) & is_sum(M,n1,AX,Z)"

lemma (in M_axioms) list_functor_abs [simp]: 
     "[| M(A); M(X); M(Z) |] ==> is_list_functor(M,A,X,Z) <-> (Z = {0} + A*X)"
by (simp add: is_list_functor_def singleton_0 nat_into_M)


subsection {*formulas without univ*}

lemma formula_fun_bnd_mono:
     "bnd_mono(univ(0), \<lambda>X. ((nat*nat) + (nat*nat)) + (X + (X*X + X)))"
apply (rule bnd_monoI)
 apply (intro subset_refl zero_subset_univ A_subset_univ 
	      sum_subset_univ Sigma_subset_univ nat_subset_univ) 
apply (rule subset_refl sum_mono Sigma_mono | assumption)+
done

lemma formula_fun_contin:
     "contin(\<lambda>X. ((nat*nat) + (nat*nat)) + (X + (X*X + X)))"
by (intro sum_contin prod_contin id_contin const_contin) 


text{*Re-expresses formulas using sum and product*}
lemma formula_eq_lfp2:
    "formula = lfp(univ(0), \<lambda>X. ((nat*nat) + (nat*nat)) + (X + (X*X + X)))"
apply (simp add: formula_def) 
apply (rule equalityI) 
 apply (rule lfp_lowerbound) 
  prefer 2 apply (rule lfp_subset)
 apply (clarify, subst lfp_unfold [OF formula_fun_bnd_mono])
 apply (simp add: Member_def Equal_def Neg_def And_def Forall_def)
 apply blast 
txt{*Opposite inclusion*}
apply (rule lfp_lowerbound) 
 prefer 2 apply (rule lfp_subset, clarify) 
apply (subst lfp_unfold [OF formula.bnd_mono, simplified]) 
apply (simp add: Member_def Equal_def Neg_def And_def Forall_def)  
apply (elim sumE SigmaE, simp_all) 
apply (blast intro: datatype_univs dest: lfp_subset [THEN subsetD])+  
done

text{*Re-expresses formulas using "iterates", no univ.*}
lemma formula_eq_Union:
     "formula = 
      (\<Union>n\<in>nat. (\<lambda>X. ((nat*nat) + (nat*nat)) + (X + (X*X + X))) ^ n (0))"
by (simp add: formula_eq_lfp2 lfp_eq_Union formula_fun_bnd_mono 
              formula_fun_contin)


constdefs
  is_formula_functor :: "[i=>o,i,i] => o"
    "is_formula_functor(M,X,Z) == 
        \<exists>nat'[M]. \<exists>natnat[M]. \<exists>natnatsum[M]. \<exists>XX[M]. \<exists>X3[M]. \<exists>X4[M]. 
          omega(M,nat') & cartprod(M,nat',nat',natnat) & 
          is_sum(M,natnat,natnat,natnatsum) &
          cartprod(M,X,X,XX) & is_sum(M,XX,X,X3) & is_sum(M,X,X3,X4) &
          is_sum(M,natnatsum,X4,Z)"

lemma (in M_axioms) formula_functor_abs [simp]: 
     "[| M(X); M(Z) |] 
      ==> is_formula_functor(M,X,Z) <-> 
          Z = ((nat*nat) + (nat*nat)) + (X + (X*X + X))"
by (simp add: is_formula_functor_def) 


subsection{*@{term M} Contains the List and Formula Datatypes*}

constdefs
  list_N :: "[i,i] => i"
    "list_N(A,n) == (\<lambda>X. {0} + A * X)^n (0)"

lemma Nil_in_list_N [simp]: "[] \<in> list_N(A,succ(n))"
by (simp add: list_N_def Nil_def)

lemma Cons_in_list_N [simp]:
     "Cons(a,l) \<in> list_N(A,succ(n)) <-> a\<in>A & l \<in> list_N(A,n)"
by (simp add: list_N_def Cons_def) 

text{*These two aren't simprules because they reveal the underlying
list representation.*}
lemma list_N_0: "list_N(A,0) = 0"
by (simp add: list_N_def)

lemma list_N_succ: "list_N(A,succ(n)) = {0} + A * (list_N(A,n))"
by (simp add: list_N_def)

lemma list_N_imp_list:
  "[| l \<in> list_N(A,n); n \<in> nat |] ==> l \<in> list(A)"
by (force simp add: list_eq_Union list_N_def)

lemma list_N_imp_length_lt [rule_format]:
     "n \<in> nat ==> \<forall>l \<in> list_N(A,n). length(l) < n"
apply (induct_tac n)  
apply (auto simp add: list_N_0 list_N_succ 
                      Nil_def [symmetric] Cons_def [symmetric]) 
done

lemma list_imp_list_N [rule_format]:
     "l \<in> list(A) ==> \<forall>n\<in>nat. length(l) < n --> l \<in> list_N(A, n)"
apply (induct_tac l)
apply (force elim: natE)+
done

lemma list_N_imp_eq_length:
      "[|n \<in> nat; l \<notin> list_N(A, n); l \<in> list_N(A, succ(n))|] 
       ==> n = length(l)"
apply (rule le_anti_sym) 
 prefer 2 apply (simp add: list_N_imp_length_lt) 
apply (frule list_N_imp_list, simp)
apply (simp add: not_lt_iff_le [symmetric]) 
apply (blast intro: list_imp_list_N) 
done
  
text{*Express @{term list_rec} without using @{term rank} or @{term Vset},
neither of which is absolute.*}
lemma (in M_triv_axioms) list_rec_eq:
  "l \<in> list(A) ==>
   list_rec(a,g,l) = 
   transrec (succ(length(l)),
      \<lambda>x h. Lambda (list_N(A,x),
             list_case' (a, 
                \<lambda>a l. g(a, l, h ` succ(length(l)) ` l)))) ` l"
apply (induct_tac l) 
apply (subst transrec, simp) 
apply (subst transrec) 
apply (simp add: list_imp_list_N) 
done

constdefs
  is_list_N :: "[i=>o,i,i,i] => o"
    "is_list_N(M,A,n,Z) == 
      \<exists>zero[M]. \<exists>sn[M]. \<exists>msn[M]. 
       empty(M,zero) & 
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, is_list_functor(M,A),zero), msn, n, Z)"
  
  mem_list :: "[i=>o,i,i] => o"
    "mem_list(M,A,l) == 
      \<exists>n[M]. \<exists>listn[M]. 
       finite_ordinal(M,n) & is_list_N(M,A,n,listn) & l \<in> listn"

  is_list :: "[i=>o,i,i] => o"
    "is_list(M,A,Z) == \<forall>l[M]. l \<in> Z <-> mem_list(M,A,l)"

constdefs
  is_formula_n :: "[i=>o,i,i] => o"
    "is_formula_n(M,n,Z) == 
      \<exists>zero[M]. \<exists>sn[M]. \<exists>msn[M]. 
       empty(M,zero) & 
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, is_formula_functor(M),zero), msn, n, Z)"
  
  mem_formula :: "[i=>o,i] => o"
    "mem_formula(M,p) == 
      \<exists>n[M]. \<exists>formn[M]. 
       finite_ordinal(M,n) & is_formula_n(M,n,formn) & p \<in> formn"

  is_formula :: "[i=>o,i] => o"
    "is_formula(M,Z) == \<forall>p[M]. p \<in> Z <-> mem_formula(M,p)"

locale (open) M_datatypes = M_wfrank +
 assumes list_replacement1: 
   "M(A) ==> iterates_replacement(M, is_list_functor(M,A), 0)"
  and list_replacement2: 
   "M(A) ==> strong_replacement(M, 
         \<lambda>n y. n\<in>nat & 
               (\<exists>sn[M]. \<exists>msn[M]. successor(M,n,sn) & membership(M,sn,msn) &
               is_wfrec(M, iterates_MH(M,is_list_functor(M,A), 0), 
                        msn, n, y)))"
  and formula_replacement1: 
   "iterates_replacement(M, is_formula_functor(M), 0)"
  and formula_replacement2: 
   "strong_replacement(M, 
         \<lambda>n y. n\<in>nat & 
               (\<exists>sn[M]. \<exists>msn[M]. successor(M,n,sn) & membership(M,sn,msn) &
               is_wfrec(M, iterates_MH(M,is_formula_functor(M), 0), 
                        msn, n, y)))"


subsubsection{*Absoluteness of the List Construction*}

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

lemma (in M_datatypes) list_N_abs [simp]:
     "[|M(A); n\<in>nat; M(Z)|] 
      ==> is_list_N(M,A,n,Z) <-> Z = list_N(A,n)"
apply (insert list_replacement1)
apply (simp add: is_list_N_def list_N_def relativize1_def nat_into_M
                 iterates_abs [of "is_list_functor(M,A)" _ "\<lambda>X. {0} + A*X"])
done

lemma (in M_datatypes) list_N_closed [intro,simp]:
     "[|M(A); n\<in>nat|] ==> M(list_N(A,n))"
apply (insert list_replacement1)
apply (simp add: is_list_N_def list_N_def relativize1_def nat_into_M
                 iterates_closed [of "is_list_functor(M,A)"])
done

lemma (in M_datatypes) mem_list_abs [simp]:
     "M(A) ==> mem_list(M,A,l) <-> l \<in> list(A)"
apply (insert list_replacement1)
apply (simp add: mem_list_def list_N_def relativize1_def list_eq_Union
                 iterates_closed [of "is_list_functor(M,A)"]) 
done

lemma (in M_datatypes) list_abs [simp]:
     "[|M(A); M(Z)|] ==> is_list(M,A,Z) <-> Z = list(A)"
apply (simp add: is_list_def, safe)
apply (rule M_equalityI, simp_all)
done

subsubsection{*Absoluteness of Formulas*}

lemma (in M_datatypes) formula_replacement2': 
  "strong_replacement(M, \<lambda>n y. n\<in>nat & y = (\<lambda>X. ((nat*nat) + (nat*nat)) + (X + (X*X + X)))^n (0))"
apply (insert formula_replacement2) 
apply (rule strong_replacement_cong [THEN iffD1])  
apply (rule conj_cong [OF iff_refl iterates_abs [of "is_formula_functor(M)"]]) 
apply (simp_all add: formula_replacement1 relativize1_def) 
done

lemma (in M_datatypes) formula_closed [intro,simp]:
     "M(formula)"
apply (insert formula_replacement1)
apply  (simp add: RepFun_closed2 formula_eq_Union 
                  formula_replacement2' relativize1_def
                  iterates_closed [of "is_formula_functor(M)"])
done

lemma (in M_datatypes) is_formula_n_abs [simp]:
     "[|n\<in>nat; M(Z)|] 
      ==> is_formula_n(M,n,Z) <-> 
          Z = (\<lambda>X. ((nat*nat) + (nat*nat)) + (X + (X*X + X)))^n (0)"
apply (insert formula_replacement1)
apply (simp add: is_formula_n_def relativize1_def nat_into_M
                 iterates_abs [of "is_formula_functor(M)" _ 
                        "\<lambda>X. ((nat*nat) + (nat*nat)) + (X + (X*X + X))"])
done

lemma (in M_datatypes) mem_formula_abs [simp]:
     "mem_formula(M,l) <-> l \<in> formula"
apply (insert formula_replacement1)
apply (simp add: mem_formula_def relativize1_def formula_eq_Union
                 iterates_closed [of "is_formula_functor(M)"]) 
done

lemma (in M_datatypes) formula_abs [simp]:
     "[|M(Z)|] ==> is_formula(M,Z) <-> Z = formula"
apply (simp add: is_formula_def, safe)
apply (rule M_equalityI, simp_all)
done


subsection{*Absoluteness for Some List Operators*}

subsection{*Absoluteness for @{text \<epsilon>}-Closure: the @{term eclose} Operator*}

text{*Re-expresses eclose using "iterates"*}
lemma eclose_eq_Union:
     "eclose(A) = (\<Union>n\<in>nat. Union^n (A))"
apply (simp add: eclose_def) 
apply (rule UN_cong) 
apply (rule refl)
apply (induct_tac n)
apply (simp add: nat_rec_0)  
apply (simp add: nat_rec_succ) 
done

constdefs
  is_eclose_n :: "[i=>o,i,i,i] => o"
    "is_eclose_n(M,A,n,Z) == 
      \<exists>sn[M]. \<exists>msn[M]. 
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, big_union(M), A), msn, n, Z)"
  
  mem_eclose :: "[i=>o,i,i] => o"
    "mem_eclose(M,A,l) == 
      \<exists>n[M]. \<exists>eclosen[M]. 
       finite_ordinal(M,n) & is_eclose_n(M,A,n,eclosen) & l \<in> eclosen"

  is_eclose :: "[i=>o,i,i] => o"
    "is_eclose(M,A,Z) == \<forall>u[M]. u \<in> Z <-> mem_eclose(M,A,u)"


locale (open) M_eclose = M_wfrank +
 assumes eclose_replacement1: 
   "M(A) ==> iterates_replacement(M, big_union(M), A)"
  and eclose_replacement2: 
   "M(A) ==> strong_replacement(M, 
         \<lambda>n y. n\<in>nat & 
               (\<exists>sn[M]. \<exists>msn[M]. successor(M,n,sn) & membership(M,sn,msn) &
               is_wfrec(M, iterates_MH(M,big_union(M), A), 
                        msn, n, y)))"

lemma (in M_eclose) eclose_replacement2': 
  "M(A) ==> strong_replacement(M, \<lambda>n y. n\<in>nat & y = Union^n (A))"
apply (insert eclose_replacement2 [of A]) 
apply (rule strong_replacement_cong [THEN iffD1])  
apply (rule conj_cong [OF iff_refl iterates_abs [of "big_union(M)"]]) 
apply (simp_all add: eclose_replacement1 relativize1_def) 
done

lemma (in M_eclose) eclose_closed [intro,simp]:
     "M(A) ==> M(eclose(A))"
apply (insert eclose_replacement1)
by  (simp add: RepFun_closed2 eclose_eq_Union 
               eclose_replacement2' relativize1_def
               iterates_closed [of "big_union(M)"])

lemma (in M_eclose) is_eclose_n_abs [simp]:
     "[|M(A); n\<in>nat; M(Z)|] ==> is_eclose_n(M,A,n,Z) <-> Z = Union^n (A)"
apply (insert eclose_replacement1)
apply (simp add: is_eclose_n_def relativize1_def nat_into_M
                 iterates_abs [of "big_union(M)" _ "Union"])
done

lemma (in M_eclose) mem_eclose_abs [simp]:
     "M(A) ==> mem_eclose(M,A,l) <-> l \<in> eclose(A)"
apply (insert eclose_replacement1)
apply (simp add: mem_eclose_def relativize1_def eclose_eq_Union
                 iterates_closed [of "big_union(M)"]) 
done

lemma (in M_eclose) eclose_abs [simp]:
     "[|M(A); M(Z)|] ==> is_eclose(M,A,Z) <-> Z = eclose(A)"
apply (simp add: is_eclose_def, safe)
apply (rule M_equalityI, simp_all)
done




subsection {*Absoluteness for @{term transrec}*}


text{* @{term "transrec(a,H) \<equiv> wfrec(Memrel(eclose({a})), a, H)"} *}
constdefs

  is_transrec :: "[i=>o, [i,i,i]=>o, i, i] => o"
   "is_transrec(M,MH,a,z) == 
      \<exists>sa[M]. \<exists>esa[M]. \<exists>mesa[M]. 
       upair(M,a,a,sa) & is_eclose(M,sa,esa) & membership(M,esa,mesa) &
       is_wfrec(M,MH,mesa,a,z)"

  transrec_replacement :: "[i=>o, [i,i,i]=>o, i] => o"
   "transrec_replacement(M,MH,a) ==
      \<exists>sa[M]. \<exists>esa[M]. \<exists>mesa[M]. 
       upair(M,a,a,sa) & is_eclose(M,sa,esa) & membership(M,esa,mesa) &
       wfrec_replacement(M,MH,mesa)"

text{*The condition @{term "Ord(i)"} lets us use the simpler 
  @{text "trans_wfrec_abs"} rather than @{text "trans_wfrec_abs"},
  which I haven't even proved yet. *}
theorem (in M_eclose) transrec_abs:
  "[|Ord(i);  M(i);  M(z);
     transrec_replacement(M,MH,i);  relativize2(M,MH,H);
     \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g))|] 
   ==> is_transrec(M,MH,i,z) <-> z = transrec(i,H)" 
by (simp add: trans_wfrec_abs transrec_replacement_def is_transrec_def
       transrec_def eclose_sing_Ord_eq wf_Memrel trans_Memrel relation_Memrel)


theorem (in M_eclose) transrec_closed:
     "[|Ord(i);  M(i);  M(z);
	transrec_replacement(M,MH,i);  relativize2(M,MH,H);
	\<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g))|] 
      ==> M(transrec(i,H))"
by (simp add: trans_wfrec_closed transrec_replacement_def is_transrec_def
       transrec_def eclose_sing_Ord_eq wf_Memrel trans_Memrel relation_Memrel)



subsection{*Absoluteness for the List Operator @{term length}*}
constdefs

  is_length :: "[i=>o,i,i,i] => o"
    "is_length(M,A,l,n) == 
       \<exists>sn[M]. \<exists>list_n[M]. \<exists>list_sn[M]. 
        is_list_N(M,A,n,list_n) & l \<notin> list_n &
        successor(M,n,sn) & is_list_N(M,A,sn,list_sn) & l \<in> list_sn"


lemma (in M_datatypes) length_abs [simp]:
     "[|M(A); l \<in> list(A); n \<in> nat|] ==> is_length(M,A,l,n) <-> n = length(l)"
apply (subgoal_tac "M(l) & M(n)")
 prefer 2 apply (blast dest: transM)  
apply (simp add: is_length_def)
apply (blast intro: list_imp_list_N nat_into_Ord list_N_imp_eq_length
             dest: list_N_imp_length_lt)
done

text{*Proof is trivial since @{term length} returns natural numbers.*}
lemma (in M_triv_axioms) length_closed [intro,simp]:
     "l \<in> list(A) ==> M(length(l))"
by (simp add: nat_into_M ) 


subsection {*Absoluteness for @{term nth}*}

lemma nth_eq_hd_iterates_tl [rule_format]:
     "xs \<in> list(A) ==> \<forall>n \<in> nat. nth(n,xs) = hd' (tl'^n (xs))"
apply (induct_tac xs) 
apply (simp add: iterates_tl_Nil hd'_Nil, clarify) 
apply (erule natE)
apply (simp add: hd'_Cons) 
apply (simp add: tl'_Cons iterates_commute) 
done

lemma (in M_axioms) iterates_tl'_closed:
     "[|n \<in> nat; M(x)|] ==> M(tl'^n (x))"
apply (induct_tac n, simp) 
apply (simp add: tl'_Cons tl'_closed) 
done

locale (open) M_nth = M_datatypes +
 assumes nth_replacement1: 
   "M(xs) ==> iterates_replacement(M, %l t. is_tl(M,l,t), xs)"

text{*Immediate by type-checking*}
lemma (in M_datatypes) nth_closed [intro,simp]:
     "[|xs \<in> list(A); n \<in> nat; M(A)|] ==> M(nth(n,xs))" 
apply (case_tac "n < length(xs)")
 apply (blast intro: nth_type transM)
apply (simp add: not_lt_iff_le nth_eq_0)
done

constdefs
  is_nth :: "[i=>o,i,i,i] => o"
    "is_nth(M,n,l,Z) == 
      \<exists>X[M]. \<exists>sn[M]. \<exists>msn[M]. 
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, is_tl(M), l), msn, n, X) &
       is_hd(M,X,Z)"
 
lemma (in M_nth) nth_abs [simp]:
     "[|M(A); n \<in> nat; l \<in> list(A); M(Z)|] 
      ==> is_nth(M,n,l,Z) <-> Z = nth(n,l)"
apply (subgoal_tac "M(l)") 
 prefer 2 apply (blast intro: transM)
apply (insert nth_replacement1)
apply (simp add: is_nth_def nth_eq_hd_iterates_tl nat_into_M
                 tl'_closed iterates_tl'_closed 
                 iterates_abs [OF _ relativize1_tl])
done


end
