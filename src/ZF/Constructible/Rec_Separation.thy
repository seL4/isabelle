(*  Title:      ZF/Constructible/Rec_Separation.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge
*)

header {*Separation for Facts About Recursion*}

theory Rec_Separation = Separation + Internalize:

text{*This theory proves all instances needed for locales @{text
"M_trancl"}, @{text "M_wfrank"} and @{text "M_datatypes"}*}

lemma eq_succ_imp_lt: "[|i = succ(j); Ord(i)|] ==> j<i"
by simp


subsection{*The Locale @{text "M_trancl"}*}

subsubsection{*Separation for Reflexive/Transitive Closure*}

text{*First, The Defining Formula*}

(* "rtran_closure_mem(M,A,r,p) ==
      \<exists>nnat[M]. \<exists>n[M]. \<exists>n'[M].
       omega(M,nnat) & n\<in>nnat & successor(M,n,n') &
       (\<exists>f[M]. typed_function(M,n',A,f) &
        (\<exists>x[M]. \<exists>y[M]. \<exists>zero[M]. pair(M,x,y,p) & empty(M,zero) &
          fun_apply(M,f,zero,x) & fun_apply(M,f,n,y)) &
        (\<forall>j[M]. j\<in>n -->
          (\<exists>fj[M]. \<exists>sj[M]. \<exists>fsj[M]. \<exists>ffp[M].
            fun_apply(M,f,j,fj) & successor(M,j,sj) &
            fun_apply(M,f,sj,fsj) & pair(M,fj,fsj,ffp) & ffp \<in> r)))"*)
constdefs rtran_closure_mem_fm :: "[i,i,i]=>i"
 "rtran_closure_mem_fm(A,r,p) ==
   Exists(Exists(Exists(
    And(omega_fm(2),
     And(Member(1,2),
      And(succ_fm(1,0),
       Exists(And(typed_function_fm(1, A#+4, 0),
        And(Exists(Exists(Exists(
              And(pair_fm(2,1,p#+7),
               And(empty_fm(0),
                And(fun_apply_fm(3,0,2), fun_apply_fm(3,5,1))))))),
            Forall(Implies(Member(0,3),
             Exists(Exists(Exists(Exists(
              And(fun_apply_fm(5,4,3),
               And(succ_fm(4,2),
                And(fun_apply_fm(5,2,1),
                 And(pair_fm(3,1,0), Member(0,r#+9))))))))))))))))))))"


lemma rtran_closure_mem_type [TC]:
 "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> rtran_closure_mem_fm(x,y,z) \<in> formula"
by (simp add: rtran_closure_mem_fm_def)

lemma arity_rtran_closure_mem_fm [simp]:
     "[| x \<in> nat; y \<in> nat; z \<in> nat |]
      ==> arity(rtran_closure_mem_fm(x,y,z)) = succ(x) \<union> succ(y) \<union> succ(z)"
by (simp add: rtran_closure_mem_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_rtran_closure_mem_fm [simp]:
   "[| x \<in> nat; y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, rtran_closure_mem_fm(x,y,z), env) <->
        rtran_closure_mem(**A, nth(x,env), nth(y,env), nth(z,env))"
by (simp add: rtran_closure_mem_fm_def rtran_closure_mem_def)

lemma rtran_closure_mem_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i \<in> nat; j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> rtran_closure_mem(**A, x, y, z) <-> sats(A, rtran_closure_mem_fm(i,j,k), env)"
by (simp add: sats_rtran_closure_mem_fm)

theorem rtran_closure_mem_reflection:
     "REFLECTS[\<lambda>x. rtran_closure_mem(L,f(x),g(x),h(x)),
               \<lambda>i x. rtran_closure_mem(**Lset(i),f(x),g(x),h(x))]"
apply (simp only: rtran_closure_mem_def setclass_simps)
apply (intro FOL_reflections function_reflections fun_plus_reflections)
done

text{*Separation for @{term "rtrancl(r)"}.*}
lemma rtrancl_separation:
     "[| L(r); L(A) |] ==> separation (L, rtran_closure_mem(L,A,r))"
apply (rule separation_CollectI)
apply (rule_tac A="{r,A,z}" in subset_LsetE, blast)
apply (rule ReflectsE [OF rtran_closure_mem_reflection], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule_tac env = "[u,r,A]" in rtran_closure_mem_iff_sats)
apply (rule sep_rules | simp)+
done


subsubsection{*Reflexive/Transitive Closure, Internalized*}

(*  "rtran_closure(M,r,s) ==
        \<forall>A[M]. is_field(M,r,A) -->
         (\<forall>p[M]. p \<in> s <-> rtran_closure_mem(M,A,r,p))" *)
constdefs rtran_closure_fm :: "[i,i]=>i"
 "rtran_closure_fm(r,s) ==
   Forall(Implies(field_fm(succ(r),0),
                  Forall(Iff(Member(0,succ(succ(s))),
                             rtran_closure_mem_fm(1,succ(succ(r)),0)))))"

lemma rtran_closure_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> rtran_closure_fm(x,y) \<in> formula"
by (simp add: rtran_closure_fm_def)

lemma arity_rtran_closure_fm [simp]:
     "[| x \<in> nat; y \<in> nat |]
      ==> arity(rtran_closure_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: rtran_closure_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_rtran_closure_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, rtran_closure_fm(x,y), env) <->
        rtran_closure(**A, nth(x,env), nth(y,env))"
by (simp add: rtran_closure_fm_def rtran_closure_def)

lemma rtran_closure_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> rtran_closure(**A, x, y) <-> sats(A, rtran_closure_fm(i,j), env)"
by simp

theorem rtran_closure_reflection:
     "REFLECTS[\<lambda>x. rtran_closure(L,f(x),g(x)),
               \<lambda>i x. rtran_closure(**Lset(i),f(x),g(x))]"
apply (simp only: rtran_closure_def setclass_simps)
apply (intro FOL_reflections function_reflections rtran_closure_mem_reflection)
done


subsubsection{*Transitive Closure of a Relation, Internalized*}

(*  "tran_closure(M,r,t) ==
         \<exists>s[M]. rtran_closure(M,r,s) & composition(M,r,s,t)" *)
constdefs tran_closure_fm :: "[i,i]=>i"
 "tran_closure_fm(r,s) ==
   Exists(And(rtran_closure_fm(succ(r),0), composition_fm(succ(r),0,succ(s))))"

lemma tran_closure_type [TC]:
     "[| x \<in> nat; y \<in> nat |] ==> tran_closure_fm(x,y) \<in> formula"
by (simp add: tran_closure_fm_def)

lemma arity_tran_closure_fm [simp]:
     "[| x \<in> nat; y \<in> nat |]
      ==> arity(tran_closure_fm(x,y)) = succ(x) \<union> succ(y)"
by (simp add: tran_closure_fm_def succ_Un_distrib [symmetric] Un_ac)

lemma sats_tran_closure_fm [simp]:
   "[| x \<in> nat; y \<in> nat; env \<in> list(A)|]
    ==> sats(A, tran_closure_fm(x,y), env) <->
        tran_closure(**A, nth(x,env), nth(y,env))"
by (simp add: tran_closure_fm_def tran_closure_def)

lemma tran_closure_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y;
          i \<in> nat; j \<in> nat; env \<in> list(A)|]
       ==> tran_closure(**A, x, y) <-> sats(A, tran_closure_fm(i,j), env)"
by simp

theorem tran_closure_reflection:
     "REFLECTS[\<lambda>x. tran_closure(L,f(x),g(x)),
               \<lambda>i x. tran_closure(**Lset(i),f(x),g(x))]"
apply (simp only: tran_closure_def setclass_simps)
apply (intro FOL_reflections function_reflections
             rtran_closure_reflection composition_reflection)
done


subsection{*Separation for the Proof of @{text "wellfounded_on_trancl"}*}

lemma wellfounded_trancl_reflects:
  "REFLECTS[\<lambda>x. \<exists>w[L]. \<exists>wx[L]. \<exists>rp[L].
                 w \<in> Z & pair(L,w,x,wx) & tran_closure(L,r,rp) & wx \<in> rp,
   \<lambda>i x. \<exists>w \<in> Lset(i). \<exists>wx \<in> Lset(i). \<exists>rp \<in> Lset(i).
       w \<in> Z & pair(**Lset(i),w,x,wx) & tran_closure(**Lset(i),r,rp) &
       wx \<in> rp]"
by (intro FOL_reflections function_reflections fun_plus_reflections
          tran_closure_reflection)


lemma wellfounded_trancl_separation:
         "[| L(r); L(Z) |] ==>
          separation (L, \<lambda>x.
              \<exists>w[L]. \<exists>wx[L]. \<exists>rp[L].
               w \<in> Z & pair(L,w,x,wx) & tran_closure(L,r,rp) & wx \<in> rp)"
apply (rule separation_CollectI)
apply (rule_tac A="{r,Z,z}" in subset_LsetE, blast)
apply (rule ReflectsE [OF wellfounded_trancl_reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[w,u,r,Z]" in mem_iff_sats)
apply (rule sep_rules tran_closure_iff_sats | simp)+
done


subsubsection{*Instantiating the locale @{text M_trancl}*}

lemma M_trancl_axioms_L: "M_trancl_axioms(L)"
  apply (rule M_trancl_axioms.intro)
   apply (assumption | rule rtrancl_separation wellfounded_trancl_separation)+
  done

theorem M_trancl_L: "PROP M_trancl(L)"
by (rule M_trancl.intro
         [OF M_triv_axioms_L M_axioms_axioms_L M_trancl_axioms_L])

lemmas iterates_abs = M_trancl.iterates_abs [OF M_trancl_L]
  and rtran_closure_rtrancl = M_trancl.rtran_closure_rtrancl [OF M_trancl_L]
  and rtrancl_closed = M_trancl.rtrancl_closed [OF M_trancl_L]
  and rtrancl_abs = M_trancl.rtrancl_abs [OF M_trancl_L]
  and trancl_closed = M_trancl.trancl_closed [OF M_trancl_L]
  and trancl_abs = M_trancl.trancl_abs [OF M_trancl_L]
  and wellfounded_on_trancl = M_trancl.wellfounded_on_trancl [OF M_trancl_L]
  and wellfounded_trancl = M_trancl.wellfounded_trancl [OF M_trancl_L]
  and wfrec_relativize = M_trancl.wfrec_relativize [OF M_trancl_L]
  and trans_wfrec_relativize = M_trancl.trans_wfrec_relativize [OF M_trancl_L]
  and trans_wfrec_abs = M_trancl.trans_wfrec_abs [OF M_trancl_L]
  and trans_eq_pair_wfrec_iff = M_trancl.trans_eq_pair_wfrec_iff [OF M_trancl_L]
  and eq_pair_wfrec_iff = M_trancl.eq_pair_wfrec_iff [OF M_trancl_L]

declare rtrancl_closed [intro,simp]
declare rtrancl_abs [simp]
declare trancl_closed [intro,simp]
declare trancl_abs [simp]


subsection{*The Locale @{text "M_wfrank"}*}

subsubsection{*Separation for @{term "wfrank"}*}

lemma wfrank_Reflects:
 "REFLECTS[\<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) -->
              ~ (\<exists>f[L]. M_is_recfun(L, %x f y. is_range(L,f,y), rplus, x, f)),
      \<lambda>i x. \<forall>rplus \<in> Lset(i). tran_closure(**Lset(i),r,rplus) -->
         ~ (\<exists>f \<in> Lset(i).
            M_is_recfun(**Lset(i), %x f y. is_range(**Lset(i),f,y),
                        rplus, x, f))]"
by (intro FOL_reflections function_reflections is_recfun_reflection tran_closure_reflection)

lemma wfrank_separation:
     "L(r) ==>
      separation (L, \<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) -->
         ~ (\<exists>f[L]. M_is_recfun(L, %x f y. is_range(L,f,y), rplus, x, f)))"
apply (rule separation_CollectI)
apply (rule_tac A="{r,z}" in subset_LsetE, blast)
apply (rule ReflectsE [OF wfrank_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule ball_iff_sats imp_iff_sats)+
apply (rule_tac env="[rplus,u,r]" in tran_closure_iff_sats)
apply (rule sep_rules | simp)+
apply (rule sep_rules is_recfun_iff_sats | simp)+
done


subsubsection{*Replacement for @{term "wfrank"}*}

lemma wfrank_replacement_Reflects:
 "REFLECTS[\<lambda>z. \<exists>x[L]. x \<in> A &
        (\<forall>rplus[L]. tran_closure(L,r,rplus) -->
         (\<exists>y[L]. \<exists>f[L]. pair(L,x,y,z)  &
                        M_is_recfun(L, %x f y. is_range(L,f,y), rplus, x, f) &
                        is_range(L,f,y))),
 \<lambda>i z. \<exists>x \<in> Lset(i). x \<in> A &
      (\<forall>rplus \<in> Lset(i). tran_closure(**Lset(i),r,rplus) -->
       (\<exists>y \<in> Lset(i). \<exists>f \<in> Lset(i). pair(**Lset(i),x,y,z)  &
         M_is_recfun(**Lset(i), %x f y. is_range(**Lset(i),f,y), rplus, x, f) &
         is_range(**Lset(i),f,y)))]"
by (intro FOL_reflections function_reflections fun_plus_reflections
             is_recfun_reflection tran_closure_reflection)


lemma wfrank_strong_replacement:
     "L(r) ==>
      strong_replacement(L, \<lambda>x z.
         \<forall>rplus[L]. tran_closure(L,r,rplus) -->
         (\<exists>y[L]. \<exists>f[L]. pair(L,x,y,z)  &
                        M_is_recfun(L, %x f y. is_range(L,f,y), rplus, x, f) &
                        is_range(L,f,y)))"
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (rule_tac A="{B,r,z}" in subset_LsetE, blast)
apply (rule ReflectsE [OF wfrank_replacement_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats ball_iff_sats conj_iff_sats)+
apply (rule_tac env = "[x,u,B,r]" in mem_iff_sats)
apply (rule sep_rules list.intros app_type tran_closure_iff_sats is_recfun_iff_sats | simp)+
done


subsubsection{*Separation for Proving @{text Ord_wfrank_range}*}

lemma Ord_wfrank_Reflects:
 "REFLECTS[\<lambda>x. \<forall>rplus[L]. tran_closure(L,r,rplus) -->
          ~ (\<forall>f[L]. \<forall>rangef[L].
             is_range(L,f,rangef) -->
             M_is_recfun(L, \<lambda>x f y. is_range(L,f,y), rplus, x, f) -->
             ordinal(L,rangef)),
      \<lambda>i x. \<forall>rplus \<in> Lset(i). tran_closure(**Lset(i),r,rplus) -->
          ~ (\<forall>f \<in> Lset(i). \<forall>rangef \<in> Lset(i).
             is_range(**Lset(i),f,rangef) -->
             M_is_recfun(**Lset(i), \<lambda>x f y. is_range(**Lset(i),f,y),
                         rplus, x, f) -->
             ordinal(**Lset(i),rangef))]"
by (intro FOL_reflections function_reflections is_recfun_reflection
          tran_closure_reflection ordinal_reflection)

lemma  Ord_wfrank_separation:
     "L(r) ==>
      separation (L, \<lambda>x.
         \<forall>rplus[L]. tran_closure(L,r,rplus) -->
          ~ (\<forall>f[L]. \<forall>rangef[L].
             is_range(L,f,rangef) -->
             M_is_recfun(L, \<lambda>x f y. is_range(L,f,y), rplus, x, f) -->
             ordinal(L,rangef)))"
apply (rule separation_CollectI)
apply (rule_tac A="{r,z}" in subset_LsetE, blast)
apply (rule ReflectsE [OF Ord_wfrank_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule ball_iff_sats imp_iff_sats)+
apply (rule_tac env="[rplus,u,r]" in tran_closure_iff_sats)
apply (rule sep_rules is_recfun_iff_sats | simp)+
done


subsubsection{*Instantiating the locale @{text M_wfrank}*}

lemma M_wfrank_axioms_L: "M_wfrank_axioms(L)"
  apply (rule M_wfrank_axioms.intro)
   apply (assumption | rule
     wfrank_separation wfrank_strong_replacement Ord_wfrank_separation)+
  done

theorem M_wfrank_L: "PROP M_wfrank(L)"
  apply (rule M_wfrank.intro)
     apply (rule M_trancl.axioms [OF M_trancl_L])+
  apply (rule M_wfrank_axioms_L) 
  done

lemmas iterates_closed = M_wfrank.iterates_closed [OF M_wfrank_L]
  and exists_wfrank = M_wfrank.exists_wfrank [OF M_wfrank_L]
  and M_wellfoundedrank = M_wfrank.M_wellfoundedrank [OF M_wfrank_L]
  and Ord_wfrank_range = M_wfrank.Ord_wfrank_range [OF M_wfrank_L]
  and Ord_range_wellfoundedrank = M_wfrank.Ord_range_wellfoundedrank [OF M_wfrank_L]
  and function_wellfoundedrank = M_wfrank.function_wellfoundedrank [OF M_wfrank_L]
  and domain_wellfoundedrank = M_wfrank.domain_wellfoundedrank [OF M_wfrank_L]
  and wellfoundedrank_type = M_wfrank.wellfoundedrank_type [OF M_wfrank_L]
  and Ord_wellfoundedrank = M_wfrank.Ord_wellfoundedrank [OF M_wfrank_L]
  and wellfoundedrank_eq = M_wfrank.wellfoundedrank_eq [OF M_wfrank_L]
  and wellfoundedrank_lt = M_wfrank.wellfoundedrank_lt [OF M_wfrank_L]
  and wellfounded_imp_subset_rvimage = M_wfrank.wellfounded_imp_subset_rvimage [OF M_wfrank_L]
  and wellfounded_imp_wf = M_wfrank.wellfounded_imp_wf [OF M_wfrank_L]
  and wellfounded_on_imp_wf_on = M_wfrank.wellfounded_on_imp_wf_on [OF M_wfrank_L]
  and wf_abs = M_wfrank.wf_abs [OF M_wfrank_L]
  and wf_on_abs = M_wfrank.wf_on_abs [OF M_wfrank_L]
  and wfrec_replacement_iff = M_wfrank.wfrec_replacement_iff [OF M_wfrank_L]
  and trans_wfrec_closed = M_wfrank.trans_wfrec_closed [OF M_wfrank_L]
  and wfrec_closed = M_wfrank.wfrec_closed [OF M_wfrank_L]

declare iterates_closed [intro,simp]
declare Ord_wfrank_range [rule_format]
declare wf_abs [simp]
declare wf_on_abs [simp]


subsection{*@{term L} is Closed Under the Operator @{term list}*}

subsubsection{*Instances of Replacement for Lists*}

lemma list_replacement1_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L,u,y,x) \<and>
         is_wfrec(L, iterates_MH(L, is_list_functor(L,A), 0), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) \<and>
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i),
                          is_list_functor(**Lset(i), A), 0), memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection list_functor_reflection)


lemma list_replacement1:
   "L(A) ==> iterates_replacement(L, is_list_functor(L,A), 0)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (insert nonempty)
apply (subgoal_tac "L(Memrel(succ(n)))")
apply (rule_tac A="{B,A,n,z,0,Memrel(succ(n))}" in subset_LsetE, blast)
apply (rule ReflectsE [OF list_replacement1_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2 Memrel_closed)
apply (elim conjE)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,n,B,0,Memrel(succ(n))]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats list_functor_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done


lemma list_replacement2_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn[L]. \<exists>msn[L]. successor(L, u, sn) \<and> membership(L, sn, msn) \<and>
           is_wfrec (L, iterates_MH (L, is_list_functor(L, A), 0),
                              msn, u, x)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn \<in> Lset(i). \<exists>msn \<in> Lset(i).
          successor(**Lset(i), u, sn) \<and> membership(**Lset(i), sn, msn) \<and>
           is_wfrec (**Lset(i),
                 iterates_MH (**Lset(i), is_list_functor(**Lset(i), A), 0),
                     msn, u, x))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection list_functor_reflection)


lemma list_replacement2:
   "L(A) ==> strong_replacement(L,
         \<lambda>n y. n\<in>nat &
               (\<exists>sn[L]. \<exists>msn[L]. successor(L,n,sn) & membership(L,sn,msn) &
               is_wfrec(L, iterates_MH(L,is_list_functor(L,A), 0),
                        msn, n, y)))"
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (insert nonempty)
apply (rule_tac A="{A,B,z,0,nat}" in subset_LsetE)
apply (blast intro: L_nat)
apply (rule ReflectsE [OF list_replacement2_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,B,0,nat]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats list_functor_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done


subsection{*@{term L} is Closed Under the Operator @{term formula}*}

subsubsection{*Instances of Replacement for Formulas*}

lemma formula_replacement1_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L,u,y,x) \<and>
         is_wfrec(L, iterates_MH(L, is_formula_functor(L), 0), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) \<and>
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i),
                          is_formula_functor(**Lset(i)), 0), memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection formula_functor_reflection)

lemma formula_replacement1:
   "iterates_replacement(L, is_formula_functor(L), 0)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (insert nonempty)
apply (subgoal_tac "L(Memrel(succ(n)))")
apply (rule_tac A="{B,n,z,0,Memrel(succ(n))}" in subset_LsetE, blast)
apply (rule ReflectsE [OF formula_replacement1_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2 Memrel_closed)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,n,B,0,Memrel(succ(n))]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats formula_functor_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done

lemma formula_replacement2_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn[L]. \<exists>msn[L]. successor(L, u, sn) \<and> membership(L, sn, msn) \<and>
           is_wfrec (L, iterates_MH (L, is_formula_functor(L), 0),
                              msn, u, x)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn \<in> Lset(i). \<exists>msn \<in> Lset(i).
          successor(**Lset(i), u, sn) \<and> membership(**Lset(i), sn, msn) \<and>
           is_wfrec (**Lset(i),
                 iterates_MH (**Lset(i), is_formula_functor(**Lset(i)), 0),
                     msn, u, x))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection formula_functor_reflection)


lemma formula_replacement2:
   "strong_replacement(L,
         \<lambda>n y. n\<in>nat &
               (\<exists>sn[L]. \<exists>msn[L]. successor(L,n,sn) & membership(L,sn,msn) &
               is_wfrec(L, iterates_MH(L,is_formula_functor(L), 0),
                        msn, n, y)))"
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (insert nonempty)
apply (rule_tac A="{B,z,0,nat}" in subset_LsetE)
apply (blast intro: L_nat)
apply (rule ReflectsE [OF formula_replacement2_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,B,0,nat]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats formula_functor_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done

text{*NB The proofs for type @{term formula} are virtually identical to those
for @{term "list(A)"}.  It was a cut-and-paste job! *}


subsubsection{*The Formula @{term is_nth}, Internalized*}

(* "is_nth(M,n,l,Z) == 
      \<exists>X[M]. \<exists>sn[M]. \<exists>msn[M]. 
       2       1       0
       successor(M,n,sn) & membership(M,sn,msn) &
       is_wfrec(M, iterates_MH(M, is_tl(M), l), msn, n, X) &
       is_hd(M,X,Z)" *)
constdefs nth_fm :: "[i,i,i]=>i"
    "nth_fm(n,l,Z) == 
       Exists(Exists(Exists(
         And(succ_fm(n#+3,1),
          And(Memrel_fm(1,0),
           And(is_wfrec_fm(iterates_MH_fm(tl_fm(1,0),l#+8,2,1,0), 0, n#+3, 2), hd_fm(2,Z#+3)))))))"

lemma nth_fm_type [TC]:
 "[| x \<in> nat; y \<in> nat; z \<in> nat |] ==> nth_fm(x,y,z) \<in> formula"
by (simp add: nth_fm_def)

lemma sats_nth_fm [simp]:
   "[| x < length(env); y \<in> nat; z \<in> nat; env \<in> list(A)|]
    ==> sats(A, nth_fm(x,y,z), env) <->
        is_nth(**A, nth(x,env), nth(y,env), nth(z,env))"
apply (frule lt_length_in_nat, assumption)  
apply (simp add: nth_fm_def is_nth_def sats_is_wfrec_fm sats_iterates_MH_fm) 
done

lemma nth_iff_sats:
      "[| nth(i,env) = x; nth(j,env) = y; nth(k,env) = z;
          i < length(env); j \<in> nat; k \<in> nat; env \<in> list(A)|]
       ==> is_nth(**A, x, y, z) <-> sats(A, nth_fm(i,j,k), env)"
by (simp add: sats_nth_fm)

theorem nth_reflection:
     "REFLECTS[\<lambda>x. is_nth(L, f(x), g(x), h(x)),  
               \<lambda>i x. is_nth(**Lset(i), f(x), g(x), h(x))]"
apply (simp only: is_nth_def setclass_simps)
apply (intro FOL_reflections function_reflections is_wfrec_reflection 
             iterates_MH_reflection hd_reflection tl_reflection) 
done


subsubsection{*An Instance of Replacement for @{term nth}*}

lemma nth_replacement_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L,u,y,x) \<and>
         is_wfrec(L, iterates_MH(L, is_tl(L), z), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) \<and>
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i),
                          is_tl(**Lset(i)), z), memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection list_functor_reflection tl_reflection)

lemma nth_replacement:
   "L(w) ==> iterates_replacement(L, %l t. is_tl(L,l,t), w)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule rallI)
apply (rule separation_CollectI)
apply (subgoal_tac "L(Memrel(succ(n)))")
apply (rule_tac A="{A,n,w,z,Memrel(succ(n))}" in subset_LsetE, blast)
apply (rule ReflectsE [OF nth_replacement_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2 Memrel_closed)
apply (elim conjE)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,z,w,Memrel(succ(n))]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats tl_iff_sats
            is_wfrec_iff_sats iterates_MH_iff_sats quasinat_iff_sats | simp)+
done



subsubsection{*Instantiating the locale @{text M_datatypes}*}

lemma M_datatypes_axioms_L: "M_datatypes_axioms(L)"
  apply (rule M_datatypes_axioms.intro)
      apply (assumption | rule
        list_replacement1 list_replacement2
        formula_replacement1 formula_replacement2
        nth_replacement)+
  done

theorem M_datatypes_L: "PROP M_datatypes(L)"
  apply (rule M_datatypes.intro)
      apply (rule M_wfrank.axioms [OF M_wfrank_L])+
 apply (rule M_datatypes_axioms_L) 
 done

lemmas list_closed = M_datatypes.list_closed [OF M_datatypes_L]
  and formula_closed = M_datatypes.formula_closed [OF M_datatypes_L]
  and list_abs = M_datatypes.list_abs [OF M_datatypes_L]
  and formula_abs = M_datatypes.formula_abs [OF M_datatypes_L]
  and nth_abs = M_datatypes.nth_abs [OF M_datatypes_L]

declare list_closed [intro,simp]
declare formula_closed [intro,simp]
declare list_abs [simp]
declare formula_abs [simp]
declare nth_abs [simp]


subsection{*@{term L} is Closed Under the Operator @{term eclose}*}

subsubsection{*Instances of Replacement for @{term eclose}*}

lemma eclose_replacement1_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> (\<exists>y[L]. pair(L,u,y,x) \<and>
         is_wfrec(L, iterates_MH(L, big_union(L), A), memsn, u, y)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> (\<exists>y \<in> Lset(i). pair(**Lset(i), u, y, x) \<and>
         is_wfrec(**Lset(i),
                  iterates_MH(**Lset(i), big_union(**Lset(i)), A),
                  memsn, u, y))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection)

lemma eclose_replacement1:
   "L(A) ==> iterates_replacement(L, big_union(L), A)"
apply (unfold iterates_replacement_def wfrec_replacement_def, clarify)
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (subgoal_tac "L(Memrel(succ(n)))")
apply (rule_tac A="{B,A,n,z,Memrel(succ(n))}" in subset_LsetE, blast)
apply (rule ReflectsE [OF eclose_replacement1_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2 Memrel_closed)
apply (elim conjE)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,n,B,Memrel(succ(n))]" in mem_iff_sats)
apply (rule sep_rules iterates_MH_iff_sats is_nat_case_iff_sats
             is_wfrec_iff_sats big_union_iff_sats quasinat_iff_sats | simp)+
done


lemma eclose_replacement2_Reflects:
 "REFLECTS
   [\<lambda>x. \<exists>u[L]. u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn[L]. \<exists>msn[L]. successor(L, u, sn) \<and> membership(L, sn, msn) \<and>
           is_wfrec (L, iterates_MH (L, big_union(L), A),
                              msn, u, x)),
    \<lambda>i x. \<exists>u \<in> Lset(i). u \<in> B \<and> u \<in> nat \<and>
         (\<exists>sn \<in> Lset(i). \<exists>msn \<in> Lset(i).
          successor(**Lset(i), u, sn) \<and> membership(**Lset(i), sn, msn) \<and>
           is_wfrec (**Lset(i),
                 iterates_MH (**Lset(i), big_union(**Lset(i)), A),
                     msn, u, x))]"
by (intro FOL_reflections function_reflections is_wfrec_reflection
          iterates_MH_reflection)


lemma eclose_replacement2:
   "L(A) ==> strong_replacement(L,
         \<lambda>n y. n\<in>nat &
               (\<exists>sn[L]. \<exists>msn[L]. successor(L,n,sn) & membership(L,sn,msn) &
               is_wfrec(L, iterates_MH(L,big_union(L), A),
                        msn, n, y)))"
apply (rule strong_replacementI)
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (rule_tac A="{A,B,z,nat}" in subset_LsetE)
apply (blast intro: L_nat)
apply (rule ReflectsE [OF eclose_replacement2_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac v)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[u,v,A,B,nat]" in mem_iff_sats)
apply (rule sep_rules is_nat_case_iff_sats iterates_MH_iff_sats
              is_wfrec_iff_sats big_union_iff_sats quasinat_iff_sats | simp)+
done


subsubsection{*Instantiating the locale @{text M_eclose}*}

lemma M_eclose_axioms_L: "M_eclose_axioms(L)"
  apply (rule M_eclose_axioms.intro)
   apply (assumption | rule eclose_replacement1 eclose_replacement2)+
  done

theorem M_eclose_L: "PROP M_eclose(L)"
  apply (rule M_eclose.intro)
       apply (rule M_datatypes.axioms [OF M_datatypes_L])+
  apply (rule M_eclose_axioms_L)
  done

lemmas eclose_closed [intro, simp] = M_eclose.eclose_closed [OF M_eclose_L]
  and eclose_abs [intro, simp] = M_eclose.eclose_abs [OF M_eclose_L]
  and transrec_replacementI = M_eclose.transrec_replacementI [OF M_eclose_L]

end
