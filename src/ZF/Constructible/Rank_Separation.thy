(*  Title:      ZF/Constructible/Rank_Separation.thy
    ID:   $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header {*Separation for Facts About Order Types, Rank Functions and 
      Well-Founded Relations*}

theory Rank_Separation = Rank + Rec_Separation:


text{*This theory proves all instances needed for locales
       @{text "M_ordertype"} and  @{text "M_wfrank"}*}

subsection{*The Locale @{text "M_ordertype"}*}

subsubsection{*Separation for Order-Isomorphisms*}

lemma well_ord_iso_Reflects:
  "REFLECTS[\<lambda>x. x\<in>A -->
                (\<exists>y[L]. \<exists>p[L]. fun_apply(L,f,x,y) & pair(L,y,x,p) & p \<in> r),
        \<lambda>i x. x\<in>A --> (\<exists>y \<in> Lset(i). \<exists>p \<in> Lset(i).
                fun_apply(**Lset(i),f,x,y) & pair(**Lset(i),y,x,p) & p \<in> r)]"
by (intro FOL_reflections function_reflections)

lemma well_ord_iso_separation:
     "[| L(A); L(f); L(r) |]
      ==> separation (L, \<lambda>x. x\<in>A --> (\<exists>y[L]. (\<exists>p[L].
                     fun_apply(L,f,x,y) & pair(L,y,x,p) & p \<in> r)))"
apply (rule gen_separation [OF well_ord_iso_Reflects, of "{A,f,r}"], simp)
apply (drule mem_Lset_imp_subset_Lset, clarsimp)
apply (rule DPow_LsetI)
apply (rule imp_iff_sats)
apply (rule_tac env = "[x,A,f,r]" in mem_iff_sats)
apply (rule sep_rules | simp)+
done


subsubsection{*Separation for @{term "obase"}*}

lemma obase_reflects:
  "REFLECTS[\<lambda>a. \<exists>x[L]. \<exists>g[L]. \<exists>mx[L]. \<exists>par[L].
             ordinal(L,x) & membership(L,x,mx) & pred_set(L,A,a,r,par) &
             order_isomorphism(L,par,r,x,mx,g),
        \<lambda>i a. \<exists>x \<in> Lset(i). \<exists>g \<in> Lset(i). \<exists>mx \<in> Lset(i). \<exists>par \<in> Lset(i).
             ordinal(**Lset(i),x) & membership(**Lset(i),x,mx) & pred_set(**Lset(i),A,a,r,par) &
             order_isomorphism(**Lset(i),par,r,x,mx,g)]"
by (intro FOL_reflections function_reflections fun_plus_reflections)

lemma obase_separation:
     --{*part of the order type formalization*}
     "[| L(A); L(r) |]
      ==> separation(L, \<lambda>a. \<exists>x[L]. \<exists>g[L]. \<exists>mx[L]. \<exists>par[L].
             ordinal(L,x) & membership(L,x,mx) & pred_set(L,A,a,r,par) &
             order_isomorphism(L,par,r,x,mx,g))"
apply (rule gen_separation [OF obase_reflects, of "{A,r}"], simp)
apply (drule mem_Lset_imp_subset_Lset, clarsimp)
apply (rule DPow_LsetI)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[x,a,A,r]" in ordinal_iff_sats)
apply (rule sep_rules | simp)+
done


subsubsection{*Separation for a Theorem about @{term "obase"}*}

lemma obase_equals_reflects:
  "REFLECTS[\<lambda>x. x\<in>A --> ~(\<exists>y[L]. \<exists>g[L].
                ordinal(L,y) & (\<exists>my[L]. \<exists>pxr[L].
                membership(L,y,my) & pred_set(L,A,x,r,pxr) &
                order_isomorphism(L,pxr,r,y,my,g))),
        \<lambda>i x. x\<in>A --> ~(\<exists>y \<in> Lset(i). \<exists>g \<in> Lset(i).
                ordinal(**Lset(i),y) & (\<exists>my \<in> Lset(i). \<exists>pxr \<in> Lset(i).
                membership(**Lset(i),y,my) & pred_set(**Lset(i),A,x,r,pxr) &
                order_isomorphism(**Lset(i),pxr,r,y,my,g)))]"
by (intro FOL_reflections function_reflections fun_plus_reflections)

lemma obase_equals_separation:
     "[| L(A); L(r) |]
      ==> separation (L, \<lambda>x. x\<in>A --> ~(\<exists>y[L]. \<exists>g[L].
                              ordinal(L,y) & (\<exists>my[L]. \<exists>pxr[L].
                              membership(L,y,my) & pred_set(L,A,x,r,pxr) &
                              order_isomorphism(L,pxr,r,y,my,g))))"
apply (rule gen_separation [OF obase_equals_reflects, of "{A,r}"], simp)
apply (drule mem_Lset_imp_subset_Lset, clarsimp)
apply (rule DPow_LsetI)
apply (rule imp_iff_sats ball_iff_sats disj_iff_sats not_iff_sats)+
apply (rule_tac env = "[x,A,r]" in mem_iff_sats)
apply (rule sep_rules | simp)+
done


subsubsection{*Replacement for @{term "omap"}*}

lemma omap_reflects:
 "REFLECTS[\<lambda>z. \<exists>a[L]. a\<in>B & (\<exists>x[L]. \<exists>g[L]. \<exists>mx[L]. \<exists>par[L].
     ordinal(L,x) & pair(L,a,x,z) & membership(L,x,mx) &
     pred_set(L,A,a,r,par) & order_isomorphism(L,par,r,x,mx,g)),
 \<lambda>i z. \<exists>a \<in> Lset(i). a\<in>B & (\<exists>x \<in> Lset(i). \<exists>g \<in> Lset(i). \<exists>mx \<in> Lset(i).
        \<exists>par \<in> Lset(i).
         ordinal(**Lset(i),x) & pair(**Lset(i),a,x,z) &
         membership(**Lset(i),x,mx) & pred_set(**Lset(i),A,a,r,par) &
         order_isomorphism(**Lset(i),par,r,x,mx,g))]"
by (intro FOL_reflections function_reflections fun_plus_reflections)

lemma omap_replacement:
     "[| L(A); L(r) |]
      ==> strong_replacement(L,
             \<lambda>a z. \<exists>x[L]. \<exists>g[L]. \<exists>mx[L]. \<exists>par[L].
             ordinal(L,x) & pair(L,a,x,z) & membership(L,x,mx) &
             pred_set(L,A,a,r,par) & order_isomorphism(L,par,r,x,mx,g))"
apply (rule strong_replacementI)
apply (rename_tac B)
apply (rule_tac u="{A,r,B}" in gen_separation [OF omap_reflects], simp)
apply (drule mem_Lset_imp_subset_Lset, clarsimp)
apply (rule DPow_LsetI)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[a,z,A,B,r]" in mem_iff_sats)
apply (rule sep_rules | simp)+
done



subsection{*Instantiating the locale @{text M_ordertype}*}
text{*Separation (and Strong Replacement) for basic set-theoretic constructions
such as intersection, Cartesian Product and image.*}

lemma M_ordertype_axioms_L: "M_ordertype_axioms(L)"
  apply (rule M_ordertype_axioms.intro)
       apply (assumption | rule well_ord_iso_separation
	 obase_separation obase_equals_separation
	 omap_replacement)+
  done

theorem M_ordertype_L: "PROP M_ordertype(L)"
apply (rule M_ordertype.intro)
     apply (rule M_basic.axioms [OF M_basic_L])+
apply (rule M_ordertype_axioms_L) 
done


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
apply (rule gen_separation [OF wfrank_Reflects], simp)
apply (rule DPow_LsetI)
apply (rule ball_iff_sats imp_iff_sats)+
apply (rule_tac env="[rplus,x,r]" in tran_closure_iff_sats)
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
apply (rule_tac u="{r,A}" in gen_separation [OF wfrank_replacement_Reflects], 
       simp)
apply (drule mem_Lset_imp_subset_Lset, clarsimp)
apply (rule DPow_LsetI)
apply (rule bex_iff_sats ball_iff_sats conj_iff_sats)+
apply (rule_tac env = "[x,z,A,r]" in mem_iff_sats)
apply (rule sep_rules list.intros app_type tran_closure_iff_sats 
            is_recfun_iff_sats | simp)+
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
apply (rule gen_separation [OF Ord_wfrank_Reflects], simp)
apply (rule DPow_LsetI)
apply (rule ball_iff_sats imp_iff_sats)+
apply (rule_tac env="[rplus,x,r]" in tran_closure_iff_sats)
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

lemmas exists_wfrank = M_wfrank.exists_wfrank [OF M_wfrank_L]
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

end