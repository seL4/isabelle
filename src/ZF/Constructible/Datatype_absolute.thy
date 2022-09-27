(*  Title:      ZF/Constructible/Datatype_absolute.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>Absoluteness Properties for Recursive Datatypes\<close>

theory Datatype_absolute imports Formula WF_absolute begin


subsection\<open>The lfp of a continuous function can be expressed as a union\<close>

definition
  directed :: "i=>o" where
   "directed(A) \<equiv> A\<noteq>0 \<and> (\<forall>x\<in>A. \<forall>y\<in>A. x \<union> y \<in> A)"

definition
  contin :: "(i=>i) => o" where
   "contin(h) \<equiv> (\<forall>A. directed(A) \<longrightarrow> h(\<Union>A) = (\<Union>X\<in>A. h(X)))"

lemma bnd_mono_iterates_subset: "\<lbrakk>bnd_mono(D, h); n \<in> nat\<rbrakk> \<Longrightarrow> h^n (0) \<subseteq> D"
apply (induct_tac n) 
 apply (simp_all add: bnd_mono_def, blast) 
done

lemma bnd_mono_increasing [rule_format]:
     "\<lbrakk>i \<in> nat; j \<in> nat; bnd_mono(D,h)\<rbrakk> \<Longrightarrow> i \<le> j \<longrightarrow> h^i(0) \<subseteq> h^j(0)"
apply (rule_tac m=i and n=j in diff_induct, simp_all)
apply (blast del: subsetI
             intro: bnd_mono_iterates_subset bnd_monoD2 [of concl: h]) 
done

lemma directed_iterates: "bnd_mono(D,h) \<Longrightarrow> directed({h^n (0). n\<in>nat})"
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
    "\<lbrakk>bnd_mono(D, h); contin(h)\<rbrakk> 
     \<Longrightarrow> h(\<Union>n\<in>nat. h^n (0)) = (\<Union>n\<in>nat. h^n (0))"
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
     "\<lbrakk>bnd_mono(D, h); contin(h)\<rbrakk> \<Longrightarrow> lfp(D,h) \<subseteq> (\<Union>n\<in>nat. h^n(0))"
apply (rule lfp_lowerbound) 
 apply (simp add: contin_iterates_eq) 
apply (simp add: contin_def bnd_mono_iterates_subset UN_subset_iff) 
done

lemma Union_subset_lfp:
     "bnd_mono(D,h) \<Longrightarrow> (\<Union>n\<in>nat. h^n(0)) \<subseteq> lfp(D,h)"
apply (simp add: UN_subset_iff)
apply (rule ballI)  
apply (induct_tac n, simp_all) 
apply (rule subset_trans [of _ "h(lfp(D,h))"])
 apply (blast dest: bnd_monoD2 [OF _ _ lfp_subset])  
apply (erule lfp_lemma2) 
done

lemma lfp_eq_Union:
     "\<lbrakk>bnd_mono(D, h); contin(h)\<rbrakk> \<Longrightarrow> lfp(D,h) = (\<Union>n\<in>nat. h^n(0))"
by (blast del: subsetI 
          intro: lfp_subset_Union Union_subset_lfp)


subsubsection\<open>Some Standard Datatype Constructions Preserve Continuity\<close>

lemma contin_imp_mono: "\<lbrakk>X\<subseteq>Y; contin(F)\<rbrakk> \<Longrightarrow> F(X) \<subseteq> F(Y)"
apply (simp add: contin_def) 
apply (drule_tac x="{X,Y}" in spec) 
apply (simp add: directed_def subset_Un_iff2 Un_commute) 
done

lemma sum_contin: "\<lbrakk>contin(F); contin(G)\<rbrakk> \<Longrightarrow> contin(\<lambda>X. F(X) + G(X))"
by (simp add: contin_def, blast)

lemma prod_contin: "\<lbrakk>contin(F); contin(G)\<rbrakk> \<Longrightarrow> contin(\<lambda>X. F(X) * G(X))" 
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



subsection \<open>Absoluteness for "Iterates"\<close>

definition
  iterates_MH :: "[i=>o, [i,i]=>o, i, i, i, i] => o" where
   "iterates_MH(M,isF,v,n,g,z) \<equiv>
        is_nat_case(M, v, \<lambda>m u. \<exists>gm[M]. fun_apply(M,g,m,gm) \<and> isF(gm,u),
                    n, z)"

definition
  is_iterates :: "[i=>o, [i,i]=>o, i, i, i] => o" where
    "is_iterates(M,isF,v,n,Z) \<equiv> 
      \<exists>sn[M]. \<exists>msn[M]. successor(M,n,sn) \<and> membership(M,sn,msn) \<and>
                       is_wfrec(M, iterates_MH(M,isF,v), msn, n, Z)"

definition
  iterates_replacement :: "[i=>o, [i,i]=>o, i] => o" where
   "iterates_replacement(M,isF,v) \<equiv>
      \<forall>n[M]. n\<in>nat \<longrightarrow> 
         wfrec_replacement(M, iterates_MH(M,isF,v), Memrel(succ(n)))"

lemma (in M_basic) iterates_MH_abs:
  "\<lbrakk>relation1(M,isF,F); M(n); M(g); M(z)\<rbrakk> 
   \<Longrightarrow> iterates_MH(M,isF,v,n,g,z) \<longleftrightarrow> z = nat_case(v, \<lambda>m. F(g`m), n)"
by (simp add: nat_case_abs [of _ "\<lambda>m. F(g ` m)"]
              relation1_def iterates_MH_def)  

lemma (in M_trancl) iterates_imp_wfrec_replacement:
  "\<lbrakk>relation1(M,isF,F); n \<in> nat; iterates_replacement(M,isF,v)\<rbrakk> 
   \<Longrightarrow> wfrec_replacement(M, \<lambda>n f z. z = nat_case(v, \<lambda>m. F(f`m), n), 
                       Memrel(succ(n)))" 
by (simp add: iterates_replacement_def iterates_MH_abs)

theorem (in M_trancl) iterates_abs:
  "\<lbrakk>iterates_replacement(M,isF,v); relation1(M,isF,F);
      n \<in> nat; M(v); M(z); \<forall>x[M]. M(F(x))\<rbrakk> 
   \<Longrightarrow> is_iterates(M,isF,v,n,z) \<longleftrightarrow> z = iterates(F,n,v)" 
apply (frule iterates_imp_wfrec_replacement, assumption+)
apply (simp add: wf_Memrel trans_Memrel relation_Memrel 
                 is_iterates_def relation2_def iterates_MH_abs 
                 iterates_nat_def recursor_def transrec_def 
                 eclose_sing_Ord_eq nat_into_M
         trans_wfrec_abs [of _ _ _ _ "\<lambda>n g. nat_case(v, \<lambda>m. F(g`m), n)"])
done


lemma (in M_trancl) iterates_closed [intro,simp]:
  "\<lbrakk>iterates_replacement(M,isF,v); relation1(M,isF,F);
      n \<in> nat; M(v); \<forall>x[M]. M(F(x))\<rbrakk> 
   \<Longrightarrow> M(iterates(F,n,v))"
apply (frule iterates_imp_wfrec_replacement, assumption+)
apply (simp add: wf_Memrel trans_Memrel relation_Memrel 
                 relation2_def iterates_MH_abs 
                 iterates_nat_def recursor_def transrec_def 
                 eclose_sing_Ord_eq nat_into_M
         trans_wfrec_closed [of _ _ _ "\<lambda>n g. nat_case(v, \<lambda>m. F(g`m), n)"])
done


subsection \<open>lists without univ\<close>

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

text\<open>Re-expresses lists using sum and product\<close>
lemma list_eq_lfp2: "list(A) = lfp(univ(A), \<lambda>X. {0} + A*X)"
apply (simp add: list_def) 
apply (rule equalityI) 
 apply (rule lfp_lowerbound) 
  prefer 2 apply (rule lfp_subset)
 apply (clarify, subst lfp_unfold [OF list_fun_bnd_mono])
 apply (simp add: Nil_def Cons_def)
 apply blast 
txt\<open>Opposite inclusion\<close>
apply (rule lfp_lowerbound) 
 prefer 2 apply (rule lfp_subset) 
apply (clarify, subst lfp_unfold [OF list.bnd_mono]) 
apply (simp add: Nil_def Cons_def)
apply (blast intro: datatype_univs
             dest: lfp_subset [THEN subsetD])
done

text\<open>Re-expresses lists using "iterates", no univ.\<close>
lemma list_eq_Union:
     "list(A) = (\<Union>n\<in>nat. (\<lambda>X. {0} + A*X) ^ n (0))"
by (simp add: list_eq_lfp2 lfp_eq_Union list_fun_bnd_mono list_fun_contin)


definition
  is_list_functor :: "[i=>o,i,i,i] => o" where
    "is_list_functor(M,A,X,Z) \<equiv> 
        \<exists>n1[M]. \<exists>AX[M]. 
         number1(M,n1) \<and> cartprod(M,A,X,AX) \<and> is_sum(M,n1,AX,Z)"

lemma (in M_basic) list_functor_abs [simp]: 
     "\<lbrakk>M(A); M(X); M(Z)\<rbrakk> \<Longrightarrow> is_list_functor(M,A,X,Z) \<longleftrightarrow> (Z = {0} + A*X)"
by (simp add: is_list_functor_def singleton_0 nat_into_M)


subsection \<open>formulas without univ\<close>

lemma formula_fun_bnd_mono:
     "bnd_mono(univ(0), \<lambda>X. ((nat*nat) + (nat*nat)) + (X*X + X))"
apply (rule bnd_monoI)
 apply (intro subset_refl zero_subset_univ A_subset_univ 
              sum_subset_univ Sigma_subset_univ nat_subset_univ) 
apply (rule subset_refl sum_mono Sigma_mono | assumption)+
done

lemma formula_fun_contin:
     "contin(\<lambda>X. ((nat*nat) + (nat*nat)) + (X*X + X))"
by (intro sum_contin prod_contin id_contin const_contin) 


text\<open>Re-expresses formulas using sum and product\<close>
lemma formula_eq_lfp2:
    "formula = lfp(univ(0), \<lambda>X. ((nat*nat) + (nat*nat)) + (X*X + X))"
apply (simp add: formula_def) 
apply (rule equalityI) 
 apply (rule lfp_lowerbound) 
  prefer 2 apply (rule lfp_subset)
 apply (clarify, subst lfp_unfold [OF formula_fun_bnd_mono])
 apply (simp add: Member_def Equal_def Nand_def Forall_def)
 apply blast 
txt\<open>Opposite inclusion\<close>
apply (rule lfp_lowerbound) 
 prefer 2 apply (rule lfp_subset, clarify) 
apply (subst lfp_unfold [OF formula.bnd_mono, simplified]) 
apply (simp add: Member_def Equal_def Nand_def Forall_def)  
apply (elim sumE SigmaE, simp_all) 
apply (blast intro: datatype_univs dest: lfp_subset [THEN subsetD])+  
done

text\<open>Re-expresses formulas using "iterates", no univ.\<close>
lemma formula_eq_Union:
     "formula = 
      (\<Union>n\<in>nat. (\<lambda>X. ((nat*nat) + (nat*nat)) + (X*X + X)) ^ n (0))"
by (simp add: formula_eq_lfp2 lfp_eq_Union formula_fun_bnd_mono 
              formula_fun_contin)


definition
  is_formula_functor :: "[i=>o,i,i] => o" where
    "is_formula_functor(M,X,Z) \<equiv> 
        \<exists>nat'[M]. \<exists>natnat[M]. \<exists>natnatsum[M]. \<exists>XX[M]. \<exists>X3[M]. 
          omega(M,nat') \<and> cartprod(M,nat',nat',natnat) \<and> 
          is_sum(M,natnat,natnat,natnatsum) \<and>
          cartprod(M,X,X,XX) \<and> is_sum(M,XX,X,X3) \<and> 
          is_sum(M,natnatsum,X3,Z)"

lemma (in M_trancl) formula_functor_abs [simp]: 
     "\<lbrakk>M(X); M(Z)\<rbrakk> 
      \<Longrightarrow> is_formula_functor(M,X,Z) \<longleftrightarrow> 
          Z = ((nat*nat) + (nat*nat)) + (X*X + X)"
by (simp add: is_formula_functor_def) 


subsection\<open>\<^term>\<open>M\<close> Contains the List and Formula Datatypes\<close>

definition
  list_N :: "[i,i] => i" where
    "list_N(A,n) \<equiv> (\<lambda>X. {0} + A * X)^n (0)"

lemma Nil_in_list_N [simp]: "[] \<in> list_N(A,succ(n))"
by (simp add: list_N_def Nil_def)

lemma Cons_in_list_N [simp]:
     "Cons(a,l) \<in> list_N(A,succ(n)) \<longleftrightarrow> a\<in>A \<and> l \<in> list_N(A,n)"
by (simp add: list_N_def Cons_def) 

text\<open>These two aren't simprules because they reveal the underlying
list representation.\<close>
lemma list_N_0: "list_N(A,0) = 0"
by (simp add: list_N_def)

lemma list_N_succ: "list_N(A,succ(n)) = {0} + A * (list_N(A,n))"
by (simp add: list_N_def)

lemma list_N_imp_list:
  "\<lbrakk>l \<in> list_N(A,n); n \<in> nat\<rbrakk> \<Longrightarrow> l \<in> list(A)"
by (force simp add: list_eq_Union list_N_def)

lemma list_N_imp_length_lt [rule_format]:
     "n \<in> nat \<Longrightarrow> \<forall>l \<in> list_N(A,n). length(l) < n"
apply (induct_tac n)  
apply (auto simp add: list_N_0 list_N_succ 
                      Nil_def [symmetric] Cons_def [symmetric]) 
done

lemma list_imp_list_N [rule_format]:
     "l \<in> list(A) \<Longrightarrow> \<forall>n\<in>nat. length(l) < n \<longrightarrow> l \<in> list_N(A, n)"
apply (induct_tac l)
apply (force elim: natE)+
done

lemma list_N_imp_eq_length:
      "\<lbrakk>n \<in> nat; l \<notin> list_N(A, n); l \<in> list_N(A, succ(n))\<rbrakk> 
       \<Longrightarrow> n = length(l)"
apply (rule le_anti_sym) 
 prefer 2 apply (simp add: list_N_imp_length_lt) 
apply (frule list_N_imp_list, simp)
apply (simp add: not_lt_iff_le [symmetric]) 
apply (blast intro: list_imp_list_N) 
done
  
text\<open>Express \<^term>\<open>list_rec\<close> without using \<^term>\<open>rank\<close> or \<^term>\<open>Vset\<close>,
neither of which is absolute.\<close>
lemma (in M_trivial) list_rec_eq:
  "l \<in> list(A) \<Longrightarrow>
   list_rec(a,g,l) = 
   transrec (succ(length(l)),
      \<lambda>x h. Lambda (list(A),
                    list_case' (a, 
                           \<lambda>a l. g(a, l, h ` succ(length(l)) ` l)))) ` l"
apply (induct_tac l) 
apply (subst transrec, simp) 
apply (subst transrec) 
apply (simp add: list_imp_list_N) 
done

definition
  is_list_N :: "[i=>o,i,i,i] => o" where
    "is_list_N(M,A,n,Z) \<equiv> 
      \<exists>zero[M]. empty(M,zero) \<and> 
                is_iterates(M, is_list_functor(M,A), zero, n, Z)"

definition  
  mem_list :: "[i=>o,i,i] => o" where
    "mem_list(M,A,l) \<equiv> 
      \<exists>n[M]. \<exists>listn[M]. 
       finite_ordinal(M,n) \<and> is_list_N(M,A,n,listn) \<and> l \<in> listn"

definition
  is_list :: "[i=>o,i,i] => o" where
    "is_list(M,A,Z) \<equiv> \<forall>l[M]. l \<in> Z \<longleftrightarrow> mem_list(M,A,l)"

subsubsection\<open>Towards Absoluteness of \<^term>\<open>formula_rec\<close>\<close>

consts   depth :: "i=>i"
primrec
  "depth(Member(x,y)) = 0"
  "depth(Equal(x,y))  = 0"
  "depth(Nand(p,q)) = succ(depth(p) \<union> depth(q))"
  "depth(Forall(p)) = succ(depth(p))"

lemma depth_type [TC]: "p \<in> formula \<Longrightarrow> depth(p) \<in> nat"
by (induct_tac p, simp_all) 


definition
  formula_N :: "i => i" where
    "formula_N(n) \<equiv> (\<lambda>X. ((nat*nat) + (nat*nat)) + (X*X + X)) ^ n (0)"

lemma Member_in_formula_N [simp]:
     "Member(x,y) \<in> formula_N(succ(n)) \<longleftrightarrow> x \<in> nat \<and> y \<in> nat"
by (simp add: formula_N_def Member_def) 

lemma Equal_in_formula_N [simp]:
     "Equal(x,y) \<in> formula_N(succ(n)) \<longleftrightarrow> x \<in> nat \<and> y \<in> nat"
by (simp add: formula_N_def Equal_def) 

lemma Nand_in_formula_N [simp]:
     "Nand(x,y) \<in> formula_N(succ(n)) \<longleftrightarrow> x \<in> formula_N(n) \<and> y \<in> formula_N(n)"
by (simp add: formula_N_def Nand_def) 

lemma Forall_in_formula_N [simp]:
     "Forall(x) \<in> formula_N(succ(n)) \<longleftrightarrow> x \<in> formula_N(n)"
by (simp add: formula_N_def Forall_def) 

text\<open>These two aren't simprules because they reveal the underlying
formula representation.\<close>
lemma formula_N_0: "formula_N(0) = 0"
by (simp add: formula_N_def)

lemma formula_N_succ:
     "formula_N(succ(n)) = 
      ((nat*nat) + (nat*nat)) + (formula_N(n) * formula_N(n) + formula_N(n))"
by (simp add: formula_N_def)

lemma formula_N_imp_formula:
  "\<lbrakk>p \<in> formula_N(n); n \<in> nat\<rbrakk> \<Longrightarrow> p \<in> formula"
by (force simp add: formula_eq_Union formula_N_def)

lemma formula_N_imp_depth_lt [rule_format]:
     "n \<in> nat \<Longrightarrow> \<forall>p \<in> formula_N(n). depth(p) < n"
apply (induct_tac n)  
apply (auto simp add: formula_N_0 formula_N_succ 
                      depth_type formula_N_imp_formula Un_least_lt_iff
                      Member_def [symmetric] Equal_def [symmetric]
                      Nand_def [symmetric] Forall_def [symmetric]) 
done

lemma formula_imp_formula_N [rule_format]:
     "p \<in> formula \<Longrightarrow> \<forall>n\<in>nat. depth(p) < n \<longrightarrow> p \<in> formula_N(n)"
apply (induct_tac p)
apply (simp_all add: succ_Un_distrib Un_least_lt_iff) 
apply (force elim: natE)+
done

lemma formula_N_imp_eq_depth:
      "\<lbrakk>n \<in> nat; p \<notin> formula_N(n); p \<in> formula_N(succ(n))\<rbrakk> 
       \<Longrightarrow> n = depth(p)"
apply (rule le_anti_sym) 
 prefer 2 apply (simp add: formula_N_imp_depth_lt) 
apply (frule formula_N_imp_formula, simp)
apply (simp add: not_lt_iff_le [symmetric]) 
apply (blast intro: formula_imp_formula_N) 
done


text\<open>This result and the next are unused.\<close>
lemma formula_N_mono [rule_format]:
  "\<lbrakk>m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> m\<le>n \<longrightarrow> formula_N(m) \<subseteq> formula_N(n)"
apply (rule_tac m = m and n = n in diff_induct)
apply (simp_all add: formula_N_0 formula_N_succ, blast) 
done

lemma formula_N_distrib:
  "\<lbrakk>m \<in> nat; n \<in> nat\<rbrakk> \<Longrightarrow> formula_N(m \<union> n) = formula_N(m) \<union> formula_N(n)"
apply (rule_tac i = m and j = n in Ord_linear_le, auto) 
apply (simp_all add: subset_Un_iff [THEN iffD1] subset_Un_iff2 [THEN iffD1] 
                     le_imp_subset formula_N_mono)
done

definition
  is_formula_N :: "[i=>o,i,i] => o" where
    "is_formula_N(M,n,Z) \<equiv> 
      \<exists>zero[M]. empty(M,zero) \<and> 
                is_iterates(M, is_formula_functor(M), zero, n, Z)"


definition  
  mem_formula :: "[i=>o,i] => o" where
    "mem_formula(M,p) \<equiv> 
      \<exists>n[M]. \<exists>formn[M]. 
       finite_ordinal(M,n) \<and> is_formula_N(M,n,formn) \<and> p \<in> formn"

definition
  is_formula :: "[i=>o,i] => o" where
    "is_formula(M,Z) \<equiv> \<forall>p[M]. p \<in> Z \<longleftrightarrow> mem_formula(M,p)"

locale M_datatypes = M_trancl +
 assumes list_replacement1:
   "M(A) \<Longrightarrow> iterates_replacement(M, is_list_functor(M,A), 0)"
  and list_replacement2:
   "M(A) \<Longrightarrow> strong_replacement(M,
         \<lambda>n y. n\<in>nat \<and> is_iterates(M, is_list_functor(M,A), 0, n, y))"
  and formula_replacement1:
   "iterates_replacement(M, is_formula_functor(M), 0)"
  and formula_replacement2:
   "strong_replacement(M,
         \<lambda>n y. n\<in>nat \<and> is_iterates(M, is_formula_functor(M), 0, n, y))"
  and nth_replacement:
   "M(l) \<Longrightarrow> iterates_replacement(M, %l t. is_tl(M,l,t), l)"


subsubsection\<open>Absoluteness of the List Construction\<close>

lemma (in M_datatypes) list_replacement2':
  "M(A) \<Longrightarrow> strong_replacement(M, \<lambda>n y. n\<in>nat \<and> y = (\<lambda>X. {0} + A * X)^n (0))"
apply (insert list_replacement2 [of A])
apply (rule strong_replacement_cong [THEN iffD1])
apply (rule conj_cong [OF iff_refl iterates_abs [of "is_list_functor(M,A)"]])
apply (simp_all add: list_replacement1 relation1_def)
done

lemma (in M_datatypes) list_closed [intro,simp]:
     "M(A) \<Longrightarrow> M(list(A))"
apply (insert list_replacement1)
by  (simp add: RepFun_closed2 list_eq_Union
               list_replacement2' relation1_def
               iterates_closed [of "is_list_functor(M,A)"])

text\<open>WARNING: use only with \<open>dest:\<close> or with variables fixed!\<close>
lemmas (in M_datatypes) list_into_M = transM [OF _ list_closed]

lemma (in M_datatypes) list_N_abs [simp]:
     "\<lbrakk>M(A); n\<in>nat; M(Z)\<rbrakk>
      \<Longrightarrow> is_list_N(M,A,n,Z) \<longleftrightarrow> Z = list_N(A,n)"
apply (insert list_replacement1)
apply (simp add: is_list_N_def list_N_def relation1_def nat_into_M
                 iterates_abs [of "is_list_functor(M,A)" _ "\<lambda>X. {0} + A*X"])
done

lemma (in M_datatypes) list_N_closed [intro,simp]:
     "\<lbrakk>M(A); n\<in>nat\<rbrakk> \<Longrightarrow> M(list_N(A,n))"
apply (insert list_replacement1)
apply (simp add: is_list_N_def list_N_def relation1_def nat_into_M
                 iterates_closed [of "is_list_functor(M,A)"])
done

lemma (in M_datatypes) mem_list_abs [simp]:
     "M(A) \<Longrightarrow> mem_list(M,A,l) \<longleftrightarrow> l \<in> list(A)"
apply (insert list_replacement1)
apply (simp add: mem_list_def list_N_def relation1_def list_eq_Union
                 iterates_closed [of "is_list_functor(M,A)"])
done

lemma (in M_datatypes) list_abs [simp]:
     "\<lbrakk>M(A); M(Z)\<rbrakk> \<Longrightarrow> is_list(M,A,Z) \<longleftrightarrow> Z = list(A)"
apply (simp add: is_list_def, safe)
apply (rule M_equalityI, simp_all)
done

subsubsection\<open>Absoluteness of Formulas\<close>

lemma (in M_datatypes) formula_replacement2':
  "strong_replacement(M, \<lambda>n y. n\<in>nat \<and> y = (\<lambda>X. ((nat*nat) + (nat*nat)) + (X*X + X))^n (0))"
apply (insert formula_replacement2)
apply (rule strong_replacement_cong [THEN iffD1])
apply (rule conj_cong [OF iff_refl iterates_abs [of "is_formula_functor(M)"]])
apply (simp_all add: formula_replacement1 relation1_def)
done

lemma (in M_datatypes) formula_closed [intro,simp]:
     "M(formula)"
apply (insert formula_replacement1)
apply  (simp add: RepFun_closed2 formula_eq_Union
                  formula_replacement2' relation1_def
                  iterates_closed [of "is_formula_functor(M)"])
done

lemmas (in M_datatypes) formula_into_M = transM [OF _ formula_closed]

lemma (in M_datatypes) formula_N_abs [simp]:
     "\<lbrakk>n\<in>nat; M(Z)\<rbrakk>
      \<Longrightarrow> is_formula_N(M,n,Z) \<longleftrightarrow> Z = formula_N(n)"
apply (insert formula_replacement1)
apply (simp add: is_formula_N_def formula_N_def relation1_def nat_into_M
                 iterates_abs [of "is_formula_functor(M)" _
                                  "\<lambda>X. ((nat*nat) + (nat*nat)) + (X*X + X)"])
done

lemma (in M_datatypes) formula_N_closed [intro,simp]:
     "n\<in>nat \<Longrightarrow> M(formula_N(n))"
apply (insert formula_replacement1)
apply (simp add: is_formula_N_def formula_N_def relation1_def nat_into_M
                 iterates_closed [of "is_formula_functor(M)"])
done

lemma (in M_datatypes) mem_formula_abs [simp]:
     "mem_formula(M,l) \<longleftrightarrow> l \<in> formula"
apply (insert formula_replacement1)
apply (simp add: mem_formula_def relation1_def formula_eq_Union formula_N_def
                 iterates_closed [of "is_formula_functor(M)"])
done

lemma (in M_datatypes) formula_abs [simp]:
     "\<lbrakk>M(Z)\<rbrakk> \<Longrightarrow> is_formula(M,Z) \<longleftrightarrow> Z = formula"
apply (simp add: is_formula_def, safe)
apply (rule M_equalityI, simp_all)
done


subsection\<open>Absoluteness for \<open>\<epsilon>\<close>-Closure: the \<^term>\<open>eclose\<close> Operator\<close>

text\<open>Re-expresses eclose using "iterates"\<close>
lemma eclose_eq_Union:
     "eclose(A) = (\<Union>n\<in>nat. Union^n (A))"
apply (simp add: eclose_def)
apply (rule UN_cong)
apply (rule refl)
apply (induct_tac n)
apply (simp add: nat_rec_0)
apply (simp add: nat_rec_succ)
done

definition
  is_eclose_n :: "[i=>o,i,i,i] => o" where
    "is_eclose_n(M,A,n,Z) \<equiv> is_iterates(M, big_union(M), A, n, Z)"

definition
  mem_eclose :: "[i=>o,i,i] => o" where
    "mem_eclose(M,A,l) \<equiv>
      \<exists>n[M]. \<exists>eclosen[M].
       finite_ordinal(M,n) \<and> is_eclose_n(M,A,n,eclosen) \<and> l \<in> eclosen"

definition
  is_eclose :: "[i=>o,i,i] => o" where
    "is_eclose(M,A,Z) \<equiv> \<forall>u[M]. u \<in> Z \<longleftrightarrow> mem_eclose(M,A,u)"


locale M_eclose = M_datatypes +
 assumes eclose_replacement1:
   "M(A) \<Longrightarrow> iterates_replacement(M, big_union(M), A)"
  and eclose_replacement2:
   "M(A) \<Longrightarrow> strong_replacement(M,
         \<lambda>n y. n\<in>nat \<and> is_iterates(M, big_union(M), A, n, y))"

lemma (in M_eclose) eclose_replacement2':
  "M(A) \<Longrightarrow> strong_replacement(M, \<lambda>n y. n\<in>nat \<and> y = Union^n (A))"
apply (insert eclose_replacement2 [of A])
apply (rule strong_replacement_cong [THEN iffD1])
apply (rule conj_cong [OF iff_refl iterates_abs [of "big_union(M)"]])
apply (simp_all add: eclose_replacement1 relation1_def)
done

lemma (in M_eclose) eclose_closed [intro,simp]:
     "M(A) \<Longrightarrow> M(eclose(A))"
apply (insert eclose_replacement1)
by  (simp add: RepFun_closed2 eclose_eq_Union
               eclose_replacement2' relation1_def
               iterates_closed [of "big_union(M)"])

lemma (in M_eclose) is_eclose_n_abs [simp]:
     "\<lbrakk>M(A); n\<in>nat; M(Z)\<rbrakk> \<Longrightarrow> is_eclose_n(M,A,n,Z) \<longleftrightarrow> Z = Union^n (A)"
apply (insert eclose_replacement1)
apply (simp add: is_eclose_n_def relation1_def nat_into_M
                 iterates_abs [of "big_union(M)" _ "Union"])
done

lemma (in M_eclose) mem_eclose_abs [simp]:
     "M(A) \<Longrightarrow> mem_eclose(M,A,l) \<longleftrightarrow> l \<in> eclose(A)"
apply (insert eclose_replacement1)
apply (simp add: mem_eclose_def relation1_def eclose_eq_Union
                 iterates_closed [of "big_union(M)"])
done

lemma (in M_eclose) eclose_abs [simp]:
     "\<lbrakk>M(A); M(Z)\<rbrakk> \<Longrightarrow> is_eclose(M,A,Z) \<longleftrightarrow> Z = eclose(A)"
apply (simp add: is_eclose_def, safe)
apply (rule M_equalityI, simp_all)
done


subsection \<open>Absoluteness for \<^term>\<open>transrec\<close>\<close>

text\<open>\<^prop>\<open>transrec(a,H) \<equiv> wfrec(Memrel(eclose({a})), a, H)\<close>\<close>

definition
  is_transrec :: "[i=>o, [i,i,i]=>o, i, i] => o" where
   "is_transrec(M,MH,a,z) \<equiv>
      \<exists>sa[M]. \<exists>esa[M]. \<exists>mesa[M].
       upair(M,a,a,sa) \<and> is_eclose(M,sa,esa) \<and> membership(M,esa,mesa) \<and>
       is_wfrec(M,MH,mesa,a,z)"

definition
  transrec_replacement :: "[i=>o, [i,i,i]=>o, i] => o" where
   "transrec_replacement(M,MH,a) \<equiv>
      \<exists>sa[M]. \<exists>esa[M]. \<exists>mesa[M].
       upair(M,a,a,sa) \<and> is_eclose(M,sa,esa) \<and> membership(M,esa,mesa) \<and>
       wfrec_replacement(M,MH,mesa)"

text\<open>The condition \<^term>\<open>Ord(i)\<close> lets us use the simpler
  \<open>trans_wfrec_abs\<close> rather than \<open>trans_wfrec_abs\<close>,
  which I haven't even proved yet.\<close>
theorem (in M_eclose) transrec_abs:
  "\<lbrakk>transrec_replacement(M,MH,i);  relation2(M,MH,H);
     Ord(i);  M(i);  M(z);
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk>
   \<Longrightarrow> is_transrec(M,MH,i,z) \<longleftrightarrow> z = transrec(i,H)"
by (simp add: trans_wfrec_abs transrec_replacement_def is_transrec_def
       transrec_def eclose_sing_Ord_eq wf_Memrel trans_Memrel relation_Memrel)


theorem (in M_eclose) transrec_closed:
     "\<lbrakk>transrec_replacement(M,MH,i);  relation2(M,MH,H);
        Ord(i);  M(i);
        \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk>
      \<Longrightarrow> M(transrec(i,H))"
by (simp add: trans_wfrec_closed transrec_replacement_def is_transrec_def
        transrec_def eclose_sing_Ord_eq wf_Memrel trans_Memrel relation_Memrel)


text\<open>Helps to prove instances of \<^term>\<open>transrec_replacement\<close>\<close>
lemma (in M_eclose) transrec_replacementI:
   "\<lbrakk>M(a);
      strong_replacement (M,
                  \<lambda>x z. \<exists>y[M]. pair(M, x, y, z) \<and>
                               is_wfrec(M,MH,Memrel(eclose({a})),x,y))\<rbrakk>
    \<Longrightarrow> transrec_replacement(M,MH,a)"
by (simp add: transrec_replacement_def wfrec_replacement_def)


subsection\<open>Absoluteness for the List Operator \<^term>\<open>length\<close>\<close>
text\<open>But it is never used.\<close>

definition
  is_length :: "[i=>o,i,i,i] => o" where
    "is_length(M,A,l,n) \<equiv>
       \<exists>sn[M]. \<exists>list_n[M]. \<exists>list_sn[M].
        is_list_N(M,A,n,list_n) \<and> l \<notin> list_n \<and>
        successor(M,n,sn) \<and> is_list_N(M,A,sn,list_sn) \<and> l \<in> list_sn"


lemma (in M_datatypes) length_abs [simp]:
     "\<lbrakk>M(A); l \<in> list(A); n \<in> nat\<rbrakk> \<Longrightarrow> is_length(M,A,l,n) \<longleftrightarrow> n = length(l)"
apply (subgoal_tac "M(l) \<and> M(n)")
 prefer 2 apply (blast dest: transM)
apply (simp add: is_length_def)
apply (blast intro: list_imp_list_N nat_into_Ord list_N_imp_eq_length
             dest: list_N_imp_length_lt)
done

text\<open>Proof is trivial since \<^term>\<open>length\<close> returns natural numbers.\<close>
lemma (in M_trivial) length_closed [intro,simp]:
     "l \<in> list(A) \<Longrightarrow> M(length(l))"
by (simp add: nat_into_M)


subsection \<open>Absoluteness for the List Operator \<^term>\<open>nth\<close>\<close>

lemma nth_eq_hd_iterates_tl [rule_format]:
     "xs \<in> list(A) \<Longrightarrow> \<forall>n \<in> nat. nth(n,xs) = hd' (tl'^n (xs))"
apply (induct_tac xs)
apply (simp add: iterates_tl_Nil hd'_Nil, clarify)
apply (erule natE)
apply (simp add: hd'_Cons)
apply (simp add: tl'_Cons iterates_commute)
done

lemma (in M_basic) iterates_tl'_closed:
     "\<lbrakk>n \<in> nat; M(x)\<rbrakk> \<Longrightarrow> M(tl'^n (x))"
apply (induct_tac n, simp)
apply (simp add: tl'_Cons tl'_closed)
done

text\<open>Immediate by type-checking\<close>
lemma (in M_datatypes) nth_closed [intro,simp]:
     "\<lbrakk>xs \<in> list(A); n \<in> nat; M(A)\<rbrakk> \<Longrightarrow> M(nth(n,xs))"
apply (case_tac "n < length(xs)")
 apply (blast intro: nth_type transM)
apply (simp add: not_lt_iff_le nth_eq_0)
done

definition
  is_nth :: "[i=>o,i,i,i] => o" where
    "is_nth(M,n,l,Z) \<equiv>
      \<exists>X[M]. is_iterates(M, is_tl(M), l, n, X) \<and> is_hd(M,X,Z)"

lemma (in M_datatypes) nth_abs [simp]:
     "\<lbrakk>M(A); n \<in> nat; l \<in> list(A); M(Z)\<rbrakk>
      \<Longrightarrow> is_nth(M,n,l,Z) \<longleftrightarrow> Z = nth(n,l)"
apply (subgoal_tac "M(l)")
 prefer 2 apply (blast intro: transM)
apply (simp add: is_nth_def nth_eq_hd_iterates_tl nat_into_M
                 tl'_closed iterates_tl'_closed
                 iterates_abs [OF _ relation1_tl] nth_replacement)
done


subsection\<open>Relativization and Absoluteness for the \<^term>\<open>formula\<close> Constructors\<close>

definition
  is_Member :: "[i=>o,i,i,i] => o" where
     \<comment> \<open>because \<^term>\<open>Member(x,y) \<equiv> Inl(Inl(\<langle>x,y\<rangle>))\<close>\<close>
    "is_Member(M,x,y,Z) \<equiv>
        \<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) \<and> is_Inl(M,p,u) \<and> is_Inl(M,u,Z)"

lemma (in M_trivial) Member_abs [simp]:
     "\<lbrakk>M(x); M(y); M(Z)\<rbrakk> \<Longrightarrow> is_Member(M,x,y,Z) \<longleftrightarrow> (Z = Member(x,y))"
by (simp add: is_Member_def Member_def)

lemma (in M_trivial) Member_in_M_iff [iff]:
     "M(Member(x,y)) \<longleftrightarrow> M(x) \<and> M(y)"
by (simp add: Member_def)

definition
  is_Equal :: "[i=>o,i,i,i] => o" where
     \<comment> \<open>because \<^term>\<open>Equal(x,y) \<equiv> Inl(Inr(\<langle>x,y\<rangle>))\<close>\<close>
    "is_Equal(M,x,y,Z) \<equiv>
        \<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) \<and> is_Inr(M,p,u) \<and> is_Inl(M,u,Z)"

lemma (in M_trivial) Equal_abs [simp]:
     "\<lbrakk>M(x); M(y); M(Z)\<rbrakk> \<Longrightarrow> is_Equal(M,x,y,Z) \<longleftrightarrow> (Z = Equal(x,y))"
by (simp add: is_Equal_def Equal_def)

lemma (in M_trivial) Equal_in_M_iff [iff]: "M(Equal(x,y)) \<longleftrightarrow> M(x) \<and> M(y)"
by (simp add: Equal_def)

definition
  is_Nand :: "[i=>o,i,i,i] => o" where
     \<comment> \<open>because \<^term>\<open>Nand(x,y) \<equiv> Inr(Inl(\<langle>x,y\<rangle>))\<close>\<close>
    "is_Nand(M,x,y,Z) \<equiv>
        \<exists>p[M]. \<exists>u[M]. pair(M,x,y,p) \<and> is_Inl(M,p,u) \<and> is_Inr(M,u,Z)"

lemma (in M_trivial) Nand_abs [simp]:
     "\<lbrakk>M(x); M(y); M(Z)\<rbrakk> \<Longrightarrow> is_Nand(M,x,y,Z) \<longleftrightarrow> (Z = Nand(x,y))"
by (simp add: is_Nand_def Nand_def)

lemma (in M_trivial) Nand_in_M_iff [iff]: "M(Nand(x,y)) \<longleftrightarrow> M(x) \<and> M(y)"
by (simp add: Nand_def)

definition
  is_Forall :: "[i=>o,i,i] => o" where
     \<comment> \<open>because \<^term>\<open>Forall(x) \<equiv> Inr(Inr(p))\<close>\<close>
    "is_Forall(M,p,Z) \<equiv> \<exists>u[M]. is_Inr(M,p,u) \<and> is_Inr(M,u,Z)"

lemma (in M_trivial) Forall_abs [simp]:
     "\<lbrakk>M(x); M(Z)\<rbrakk> \<Longrightarrow> is_Forall(M,x,Z) \<longleftrightarrow> (Z = Forall(x))"
by (simp add: is_Forall_def Forall_def)

lemma (in M_trivial) Forall_in_M_iff [iff]: "M(Forall(x)) \<longleftrightarrow> M(x)"
by (simp add: Forall_def)



subsection \<open>Absoluteness for \<^term>\<open>formula_rec\<close>\<close>

definition
  formula_rec_case :: "[[i,i]=>i, [i,i]=>i, [i,i,i,i]=>i, [i,i]=>i, i, i] => i" where
    \<comment> \<open>the instance of \<^term>\<open>formula_case\<close> in \<^term>\<open>formula_rec\<close>\<close>
   "formula_rec_case(a,b,c,d,h) \<equiv>
        formula_case (a, b,
                \<lambda>u v. c(u, v, h ` succ(depth(u)) ` u,
                              h ` succ(depth(v)) ` v),
                \<lambda>u. d(u, h ` succ(depth(u)) ` u))"

text\<open>Unfold \<^term>\<open>formula_rec\<close> to \<^term>\<open>formula_rec_case\<close>.
     Express \<^term>\<open>formula_rec\<close> without using \<^term>\<open>rank\<close> or \<^term>\<open>Vset\<close>,
neither of which is absolute.\<close>
lemma (in M_trivial) formula_rec_eq:
  "p \<in> formula \<Longrightarrow>
   formula_rec(a,b,c,d,p) =
   transrec (succ(depth(p)),
             \<lambda>x h. Lambda (formula, formula_rec_case(a,b,c,d,h))) ` p"
apply (simp add: formula_rec_case_def)
apply (induct_tac p)
   txt\<open>Base case for \<^term>\<open>Member\<close>\<close>
   apply (subst transrec, simp add: formula.intros)
  txt\<open>Base case for \<^term>\<open>Equal\<close>\<close>
  apply (subst transrec, simp add: formula.intros)
 txt\<open>Inductive step for \<^term>\<open>Nand\<close>\<close>
 apply (subst transrec)
 apply (simp add: succ_Un_distrib formula.intros)
txt\<open>Inductive step for \<^term>\<open>Forall\<close>\<close>
apply (subst transrec)
apply (simp add: formula_imp_formula_N formula.intros)
done


subsubsection\<open>Absoluteness for the Formula Operator \<^term>\<open>depth\<close>\<close>

definition
  is_depth :: "[i=>o,i,i] => o" where
    "is_depth(M,p,n) \<equiv>
       \<exists>sn[M]. \<exists>formula_n[M]. \<exists>formula_sn[M].
        is_formula_N(M,n,formula_n) \<and> p \<notin> formula_n \<and>
        successor(M,n,sn) \<and> is_formula_N(M,sn,formula_sn) \<and> p \<in> formula_sn"


lemma (in M_datatypes) depth_abs [simp]:
     "\<lbrakk>p \<in> formula; n \<in> nat\<rbrakk> \<Longrightarrow> is_depth(M,p,n) \<longleftrightarrow> n = depth(p)"
apply (subgoal_tac "M(p) \<and> M(n)")
 prefer 2 apply (blast dest: transM)
apply (simp add: is_depth_def)
apply (blast intro: formula_imp_formula_N nat_into_Ord formula_N_imp_eq_depth
             dest: formula_N_imp_depth_lt)
done

text\<open>Proof is trivial since \<^term>\<open>depth\<close> returns natural numbers.\<close>
lemma (in M_trivial) depth_closed [intro,simp]:
     "p \<in> formula \<Longrightarrow> M(depth(p))"
by (simp add: nat_into_M)


subsubsection\<open>\<^term>\<open>is_formula_case\<close>: relativization of \<^term>\<open>formula_case\<close>\<close>

definition
 is_formula_case ::
    "[i=>o, [i,i,i]=>o, [i,i,i]=>o, [i,i,i]=>o, [i,i]=>o, i, i] => o" where
  \<comment> \<open>no constraint on non-formulas\<close>
  "is_formula_case(M, is_a, is_b, is_c, is_d, p, z) \<equiv>
      (\<forall>x[M]. \<forall>y[M]. finite_ordinal(M,x) \<longrightarrow> finite_ordinal(M,y) \<longrightarrow>
                      is_Member(M,x,y,p) \<longrightarrow> is_a(x,y,z)) \<and>
      (\<forall>x[M]. \<forall>y[M]. finite_ordinal(M,x) \<longrightarrow> finite_ordinal(M,y) \<longrightarrow>
                      is_Equal(M,x,y,p) \<longrightarrow> is_b(x,y,z)) \<and>
      (\<forall>x[M]. \<forall>y[M]. mem_formula(M,x) \<longrightarrow> mem_formula(M,y) \<longrightarrow>
                     is_Nand(M,x,y,p) \<longrightarrow> is_c(x,y,z)) \<and>
      (\<forall>x[M]. mem_formula(M,x) \<longrightarrow> is_Forall(M,x,p) \<longrightarrow> is_d(x,z))"

lemma (in M_datatypes) formula_case_abs [simp]:
     "\<lbrakk>Relation2(M,nat,nat,is_a,a); Relation2(M,nat,nat,is_b,b);
         Relation2(M,formula,formula,is_c,c); Relation1(M,formula,is_d,d);
         p \<in> formula; M(z)\<rbrakk>
      \<Longrightarrow> is_formula_case(M,is_a,is_b,is_c,is_d,p,z) \<longleftrightarrow>
          z = formula_case(a,b,c,d,p)"
apply (simp add: formula_into_M is_formula_case_def)
apply (erule formula.cases)
   apply (simp_all add: Relation1_def Relation2_def)
done

lemma (in M_datatypes) formula_case_closed [intro,simp]:
  "\<lbrakk>p \<in> formula;
     \<forall>x[M]. \<forall>y[M]. x\<in>nat \<longrightarrow> y\<in>nat \<longrightarrow> M(a(x,y));
     \<forall>x[M]. \<forall>y[M]. x\<in>nat \<longrightarrow> y\<in>nat \<longrightarrow> M(b(x,y));
     \<forall>x[M]. \<forall>y[M]. x\<in>formula \<longrightarrow> y\<in>formula \<longrightarrow> M(c(x,y));
     \<forall>x[M]. x\<in>formula \<longrightarrow> M(d(x))\<rbrakk> \<Longrightarrow> M(formula_case(a,b,c,d,p))"
by (erule formula.cases, simp_all)


subsubsection \<open>Absoluteness for \<^term>\<open>formula_rec\<close>: Final Results\<close>

definition
  is_formula_rec :: "[i=>o, [i,i,i]=>o, i, i] => o" where
    \<comment> \<open>predicate to relativize the functional \<^term>\<open>formula_rec\<close>\<close>
   "is_formula_rec(M,MH,p,z)  \<equiv>
      \<exists>dp[M]. \<exists>i[M]. \<exists>f[M]. finite_ordinal(M,dp) \<and> is_depth(M,p,dp) \<and>
             successor(M,dp,i) \<and> fun_apply(M,f,p,z) \<and> is_transrec(M,MH,i,f)"


text\<open>Sufficient conditions to relativize the instance of \<^term>\<open>formula_case\<close>
      in \<^term>\<open>formula_rec\<close>\<close>
lemma (in M_datatypes) Relation1_formula_rec_case:
     "\<lbrakk>Relation2(M, nat, nat, is_a, a);
        Relation2(M, nat, nat, is_b, b);
        Relation2 (M, formula, formula,
           is_c, \<lambda>u v. c(u, v, h`succ(depth(u))`u, h`succ(depth(v))`v));
        Relation1(M, formula,
           is_d, \<lambda>u. d(u, h ` succ(depth(u)) ` u));
        M(h)\<rbrakk>
      \<Longrightarrow> Relation1(M, formula,
                         is_formula_case (M, is_a, is_b, is_c, is_d),
                         formula_rec_case(a, b, c, d, h))"
apply (simp (no_asm) add: formula_rec_case_def Relation1_def)
apply (simp)
done


text\<open>This locale packages the premises of the following theorems,
      which is the normal purpose of locales.  It doesn't accumulate
      constraints on the class \<^term>\<open>M\<close>, as in most of this development.\<close>
locale Formula_Rec = M_eclose +
  fixes a and is_a and b and is_b and c and is_c and d and is_d and MH
  defines
      "MH(u::i,f,z) \<equiv>
        \<forall>fml[M]. is_formula(M,fml) \<longrightarrow>
             is_lambda
         (M, fml, is_formula_case (M, is_a, is_b, is_c(f), is_d(f)), z)"

  assumes a_closed: "\<lbrakk>x\<in>nat; y\<in>nat\<rbrakk> \<Longrightarrow> M(a(x,y))"
      and a_rel:    "Relation2(M, nat, nat, is_a, a)"
      and b_closed: "\<lbrakk>x\<in>nat; y\<in>nat\<rbrakk> \<Longrightarrow> M(b(x,y))"
      and b_rel:    "Relation2(M, nat, nat, is_b, b)"
      and c_closed: "\<lbrakk>x \<in> formula; y \<in> formula; M(gx); M(gy)\<rbrakk>
                     \<Longrightarrow> M(c(x, y, gx, gy))"
      and c_rel:
         "M(f) \<Longrightarrow>
          Relation2 (M, formula, formula, is_c(f),
             \<lambda>u v. c(u, v, f ` succ(depth(u)) ` u, f ` succ(depth(v)) ` v))"
      and d_closed: "\<lbrakk>x \<in> formula; M(gx)\<rbrakk> \<Longrightarrow> M(d(x, gx))"
      and d_rel:
         "M(f) \<Longrightarrow>
          Relation1(M, formula, is_d(f), \<lambda>u. d(u, f ` succ(depth(u)) ` u))"
      and fr_replace: "n \<in> nat \<Longrightarrow> transrec_replacement(M,MH,n)"
      and fr_lam_replace:
           "M(g) \<Longrightarrow>
            strong_replacement
              (M, \<lambda>x y. x \<in> formula \<and>
                  y = \<langle>x, formula_rec_case(a,b,c,d,g,x)\<rangle>)"

lemma (in Formula_Rec) formula_rec_case_closed:
    "\<lbrakk>M(g); p \<in> formula\<rbrakk> \<Longrightarrow> M(formula_rec_case(a, b, c, d, g, p))"
by (simp add: formula_rec_case_def a_closed b_closed c_closed d_closed)

lemma (in Formula_Rec) formula_rec_lam_closed:
    "M(g) \<Longrightarrow> M(Lambda (formula, formula_rec_case(a,b,c,d,g)))"
by (simp add: lam_closed2 fr_lam_replace formula_rec_case_closed)

lemma (in Formula_Rec) MH_rel2:
     "relation2 (M, MH,
             \<lambda>x h. Lambda (formula, formula_rec_case(a,b,c,d,h)))"
apply (simp add: relation2_def MH_def, clarify)
apply (rule lambda_abs2)
apply (rule Relation1_formula_rec_case)
apply (simp_all add: a_rel b_rel c_rel d_rel formula_rec_case_closed)
done

lemma (in Formula_Rec) fr_transrec_closed:
    "n \<in> nat
     \<Longrightarrow> M(transrec
          (n, \<lambda>x h. Lambda(formula, formula_rec_case(a, b, c, d, h))))"
by (simp add: transrec_closed [OF fr_replace MH_rel2]
              nat_into_M formula_rec_lam_closed)

text\<open>The main two results: \<^term>\<open>formula_rec\<close> is absolute for \<^term>\<open>M\<close>.\<close>
theorem (in Formula_Rec) formula_rec_closed:
    "p \<in> formula \<Longrightarrow> M(formula_rec(a,b,c,d,p))"
by (simp add: formula_rec_eq fr_transrec_closed
              transM [OF _ formula_closed])

theorem (in Formula_Rec) formula_rec_abs:
  "\<lbrakk>p \<in> formula; M(z)\<rbrakk>
   \<Longrightarrow> is_formula_rec(M,MH,p,z) \<longleftrightarrow> z = formula_rec(a,b,c,d,p)"
by (simp add: is_formula_rec_def formula_rec_eq transM [OF _ formula_closed]
              transrec_abs [OF fr_replace MH_rel2] depth_type
              fr_transrec_closed formula_rec_lam_closed eq_commute)


end
