(*  Title:      ZF/Constructible/Separation.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge
*)

header{*Early Instances of Separation and Strong Replacement*}

theory Separation = L_axioms + WF_absolute:

text{*This theory proves all instances needed for locale @{text "M_axioms"}*}

text{*Helps us solve for de Bruijn indices!*}
lemma nth_ConsI: "[|nth(n,l) = x; n \<in> nat|] ==> nth(succ(n), Cons(a,l)) = x"
by simp

lemmas nth_rules = nth_0 nth_ConsI nat_0I nat_succI
lemmas sep_rules = nth_0 nth_ConsI FOL_iff_sats function_iff_sats
                   fun_plus_iff_sats

lemma Collect_conj_in_DPow:
     "[| {x\<in>A. P(x)} \<in> DPow(A);  {x\<in>A. Q(x)} \<in> DPow(A) |]
      ==> {x\<in>A. P(x) & Q(x)} \<in> DPow(A)"
by (simp add: Int_in_DPow Collect_Int_Collect_eq [symmetric])

lemma Collect_conj_in_DPow_Lset:
     "[|z \<in> Lset(j); {x \<in> Lset(j). P(x)} \<in> DPow(Lset(j))|]
      ==> {x \<in> Lset(j). x \<in> z & P(x)} \<in> DPow(Lset(j))"
apply (frule mem_Lset_imp_subset_Lset)
apply (simp add: Collect_conj_in_DPow Collect_mem_eq
                 subset_Int_iff2 elem_subset_in_DPow)
done

lemma separation_CollectI:
     "(\<And>z. L(z) ==> L({x \<in> z . P(x)})) ==> separation(L, \<lambda>x. P(x))"
apply (unfold separation_def, clarify)
apply (rule_tac x="{x\<in>z. P(x)}" in rexI)
apply simp_all
done

text{*Reduces the original comprehension to the reflected one*}
lemma reflection_imp_L_separation:
      "[| \<forall>x\<in>Lset(j). P(x) <-> Q(x);
          {x \<in> Lset(j) . Q(x)} \<in> DPow(Lset(j));
          Ord(j);  z \<in> Lset(j)|] ==> L({x \<in> z . P(x)})"
apply (rule_tac i = "succ(j)" in L_I)
 prefer 2 apply simp
apply (subgoal_tac "{x \<in> z. P(x)} = {x \<in> Lset(j). x \<in> z & (Q(x))}")
 prefer 2
 apply (blast dest: mem_Lset_imp_subset_Lset)
apply (simp add: Lset_succ Collect_conj_in_DPow_Lset)
done


subsection{*Separation for Intersection*}

lemma Inter_Reflects:
     "REFLECTS[\<lambda>x. \<forall>y[L]. y\<in>A --> x \<in> y,
               \<lambda>i x. \<forall>y\<in>Lset(i). y\<in>A --> x \<in> y]"
by (intro FOL_reflections)

lemma Inter_separation:
     "L(A) ==> separation(L, \<lambda>x. \<forall>y[L]. y\<in>A --> x\<in>y)"
apply (rule separation_CollectI)
apply (rule_tac A="{A,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF Inter_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rule ball_iff_sats)
apply (rule imp_iff_sats)
apply (rule_tac [2] i=1 and j=0 and env="[y,x,A]" in mem_iff_sats)
apply (rule_tac i=0 and j=2 in mem_iff_sats)
apply (simp_all add: succ_Un_distrib [symmetric])
done

subsection{*Separation for Set Difference*}

lemma Diff_Reflects:
     "REFLECTS[\<lambda>x. x \<notin> B, \<lambda>i x. x \<notin> B]"
by (intro FOL_reflections)  

lemma Diff_separation:
     "L(B) ==> separation(L, \<lambda>x. x \<notin> B)"
apply (rule separation_CollectI) 
apply (rule_tac A="{B,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF Diff_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI) 
apply (rule not_iff_sats) 
apply (rule_tac env="[x,B]" in mem_iff_sats)
apply (rule sep_rules | simp)+
done

subsection{*Separation for Cartesian Product*}

lemma cartprod_Reflects:
     "REFLECTS[\<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. y\<in>B & pair(L,x,y,z)),
                \<lambda>i z. \<exists>x\<in>Lset(i). x\<in>A & (\<exists>y\<in>Lset(i). y\<in>B &
                                   pair(**Lset(i),x,y,z))]"
by (intro FOL_reflections function_reflections)

lemma cartprod_separation:
     "[| L(A); L(B) |]
      ==> separation(L, \<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. y\<in>B & pair(L,x,y,z)))"
apply (rule separation_CollectI)
apply (rule_tac A="{A,B,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF cartprod_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac i=0 and j=2 and env="[x,u,A,B]" in mem_iff_sats, simp_all)
apply (rule sep_rules | simp)+
done

subsection{*Separation for Image*}

lemma image_Reflects:
     "REFLECTS[\<lambda>y. \<exists>p[L]. p\<in>r & (\<exists>x[L]. x\<in>A & pair(L,x,y,p)),
           \<lambda>i y. \<exists>p\<in>Lset(i). p\<in>r & (\<exists>x\<in>Lset(i). x\<in>A & pair(**Lset(i),x,y,p))]"
by (intro FOL_reflections function_reflections)

lemma image_separation:
     "[| L(A); L(r) |]
      ==> separation(L, \<lambda>y. \<exists>p[L]. p\<in>r & (\<exists>x[L]. x\<in>A & pair(L,x,y,p)))"
apply (rule separation_CollectI)
apply (rule_tac A="{A,r,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF image_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac env="[p,y,A,r]" in mem_iff_sats)
apply (rule sep_rules | simp)+
done


subsection{*Separation for Converse*}

lemma converse_Reflects:
  "REFLECTS[\<lambda>z. \<exists>p[L]. p\<in>r & (\<exists>x[L]. \<exists>y[L]. pair(L,x,y,p) & pair(L,y,x,z)),
     \<lambda>i z. \<exists>p\<in>Lset(i). p\<in>r & (\<exists>x\<in>Lset(i). \<exists>y\<in>Lset(i).
                     pair(**Lset(i),x,y,p) & pair(**Lset(i),y,x,z))]"
by (intro FOL_reflections function_reflections)

lemma converse_separation:
     "L(r) ==> separation(L,
         \<lambda>z. \<exists>p[L]. p\<in>r & (\<exists>x[L]. \<exists>y[L]. pair(L,x,y,p) & pair(L,y,x,z)))"
apply (rule separation_CollectI)
apply (rule_tac A="{r,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF converse_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac i=0 and j=2 and env="[p,u,r]" in mem_iff_sats, simp_all)
apply (rule sep_rules | simp)+
done


subsection{*Separation for Restriction*}

lemma restrict_Reflects:
     "REFLECTS[\<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. pair(L,x,y,z)),
        \<lambda>i z. \<exists>x\<in>Lset(i). x\<in>A & (\<exists>y\<in>Lset(i). pair(**Lset(i),x,y,z))]"
by (intro FOL_reflections function_reflections)

lemma restrict_separation:
   "L(A) ==> separation(L, \<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. pair(L,x,y,z)))"
apply (rule separation_CollectI)
apply (rule_tac A="{A,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF restrict_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac i=0 and j=2 and env="[x,u,A]" in mem_iff_sats, simp_all)
apply (rule sep_rules | simp)+
done


subsection{*Separation for Composition*}

lemma comp_Reflects:
     "REFLECTS[\<lambda>xz. \<exists>x[L]. \<exists>y[L]. \<exists>z[L]. \<exists>xy[L]. \<exists>yz[L].
                  pair(L,x,z,xz) & pair(L,x,y,xy) & pair(L,y,z,yz) &
                  xy\<in>s & yz\<in>r,
        \<lambda>i xz. \<exists>x\<in>Lset(i). \<exists>y\<in>Lset(i). \<exists>z\<in>Lset(i). \<exists>xy\<in>Lset(i). \<exists>yz\<in>Lset(i).
                  pair(**Lset(i),x,z,xz) & pair(**Lset(i),x,y,xy) &
                  pair(**Lset(i),y,z,yz) & xy\<in>s & yz\<in>r]"
by (intro FOL_reflections function_reflections)

lemma comp_separation:
     "[| L(r); L(s) |]
      ==> separation(L, \<lambda>xz. \<exists>x[L]. \<exists>y[L]. \<exists>z[L]. \<exists>xy[L]. \<exists>yz[L].
                  pair(L,x,z,xz) & pair(L,x,y,xy) & pair(L,y,z,yz) &
                  xy\<in>s & yz\<in>r)"
apply (rule separation_CollectI)
apply (rule_tac A="{r,s,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF comp_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats)+
apply (rename_tac x y z)
apply (rule conj_iff_sats)
apply (rule_tac env="[z,y,x,u,r,s]" in pair_iff_sats)
apply (rule sep_rules | simp)+
done

subsection{*Separation for Predecessors in an Order*}

lemma pred_Reflects:
     "REFLECTS[\<lambda>y. \<exists>p[L]. p\<in>r & pair(L,y,x,p),
                    \<lambda>i y. \<exists>p \<in> Lset(i). p\<in>r & pair(**Lset(i),y,x,p)]"
by (intro FOL_reflections function_reflections)

lemma pred_separation:
     "[| L(r); L(x) |] ==> separation(L, \<lambda>y. \<exists>p[L]. p\<in>r & pair(L,y,x,p))"
apply (rule separation_CollectI)
apply (rule_tac A="{r,x,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF pred_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac env = "[p,u,r,x]" in mem_iff_sats)
apply (rule sep_rules | simp)+
done


subsection{*Separation for the Membership Relation*}

lemma Memrel_Reflects:
     "REFLECTS[\<lambda>z. \<exists>x[L]. \<exists>y[L]. pair(L,x,y,z) & x \<in> y,
            \<lambda>i z. \<exists>x \<in> Lset(i). \<exists>y \<in> Lset(i). pair(**Lset(i),x,y,z) & x \<in> y]"
by (intro FOL_reflections function_reflections)

lemma Memrel_separation:
     "separation(L, \<lambda>z. \<exists>x[L]. \<exists>y[L]. pair(L,x,y,z) & x \<in> y)"
apply (rule separation_CollectI)
apply (rule_tac A="{z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF Memrel_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[y,x,u]" in pair_iff_sats)
apply (rule sep_rules | simp)+
done


subsection{*Replacement for FunSpace*}

lemma funspace_succ_Reflects:
 "REFLECTS[\<lambda>z. \<exists>p[L]. p\<in>A & (\<exists>f[L]. \<exists>b[L]. \<exists>nb[L]. \<exists>cnbf[L].
            pair(L,f,b,p) & pair(L,n,b,nb) & is_cons(L,nb,f,cnbf) &
            upair(L,cnbf,cnbf,z)),
        \<lambda>i z. \<exists>p \<in> Lset(i). p\<in>A & (\<exists>f \<in> Lset(i). \<exists>b \<in> Lset(i).
              \<exists>nb \<in> Lset(i). \<exists>cnbf \<in> Lset(i).
                pair(**Lset(i),f,b,p) & pair(**Lset(i),n,b,nb) &
                is_cons(**Lset(i),nb,f,cnbf) & upair(**Lset(i),cnbf,cnbf,z))]"
by (intro FOL_reflections function_reflections)

lemma funspace_succ_replacement:
     "L(n) ==>
      strong_replacement(L, \<lambda>p z. \<exists>f[L]. \<exists>b[L]. \<exists>nb[L]. \<exists>cnbf[L].
                pair(L,f,b,p) & pair(L,n,b,nb) & is_cons(L,nb,f,cnbf) &
                upair(L,cnbf,cnbf,z))"
apply (rule strong_replacementI)
apply (rule rallI)
apply (rule separation_CollectI)
apply (rule_tac A="{n,A,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF funspace_succ_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac env = "[p,u,n,A]" in mem_iff_sats)
apply (rule sep_rules | simp)+
done


subsection{*Separation for Order-Isomorphisms*}

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
apply (rule separation_CollectI)
apply (rule_tac A="{A,f,r,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF well_ord_iso_Reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule imp_iff_sats)
apply (rule_tac env = "[u,A,f,r]" in mem_iff_sats)
apply (rule sep_rules | simp)+
done


subsection{*Separation for @{term "obase"}*}

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
apply (rule separation_CollectI)
apply (rule_tac A="{A,r,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF obase_reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac env = "[x,u,A,r]" in ordinal_iff_sats)
apply (rule sep_rules | simp)+
done


subsection{*Separation for a Theorem about @{term "obase"}*}

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
apply (rule separation_CollectI)
apply (rule_tac A="{A,r,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF obase_equals_reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule imp_iff_sats ball_iff_sats disj_iff_sats not_iff_sats)+
apply (rule_tac env = "[u,A,r]" in mem_iff_sats)
apply (rule sep_rules | simp)+
done


subsection{*Replacement for @{term "omap"}*}

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
apply (rule rallI)
apply (rename_tac B)
apply (rule separation_CollectI)
apply (rule_tac A="{A,B,r,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF omap_reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[a,u,A,B,r]" in mem_iff_sats)
apply (rule sep_rules | simp)+
done


subsection{*Separation for a Theorem about @{term "obase"}*}

lemma is_recfun_reflects:
  "REFLECTS[\<lambda>x. \<exists>xa[L]. \<exists>xb[L].
                pair(L,x,a,xa) & xa \<in> r & pair(L,x,b,xb) & xb \<in> r &
                (\<exists>fx[L]. \<exists>gx[L]. fun_apply(L,f,x,fx) & fun_apply(L,g,x,gx) &
                                   fx \<noteq> gx),
   \<lambda>i x. \<exists>xa \<in> Lset(i). \<exists>xb \<in> Lset(i).
          pair(**Lset(i),x,a,xa) & xa \<in> r & pair(**Lset(i),x,b,xb) & xb \<in> r &
                (\<exists>fx \<in> Lset(i). \<exists>gx \<in> Lset(i). fun_apply(**Lset(i),f,x,fx) &
                  fun_apply(**Lset(i),g,x,gx) & fx \<noteq> gx)]"
by (intro FOL_reflections function_reflections fun_plus_reflections)

lemma is_recfun_separation:
     --{*for well-founded recursion*}
     "[| L(r); L(f); L(g); L(a); L(b) |]
     ==> separation(L,
            \<lambda>x. \<exists>xa[L]. \<exists>xb[L].
                pair(L,x,a,xa) & xa \<in> r & pair(L,x,b,xb) & xb \<in> r &
                (\<exists>fx[L]. \<exists>gx[L]. fun_apply(L,f,x,fx) & fun_apply(L,g,x,gx) &
                                   fx \<noteq> gx))"
apply (rule separation_CollectI)
apply (rule_tac A="{r,f,g,a,b,z}" in subset_LsetE, blast )
apply (rule ReflectsE [OF is_recfun_reflects], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPow_LsetI)
apply (rename_tac u)
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[xa,u,r,f,g,a,b]" in pair_iff_sats)
apply (rule sep_rules | simp)+
done


subsection{*Instantiating the locale @{text M_axioms}*}
text{*Separation (and Strong Replacement) for basic set-theoretic constructions
such as intersection, Cartesian Product and image.*}

lemma M_axioms_axioms_L: "M_axioms_axioms(L)"
  apply (rule M_axioms_axioms.intro)
       apply (assumption | rule
	 Inter_separation Diff_separation cartprod_separation image_separation
	 converse_separation restrict_separation
	 comp_separation pred_separation Memrel_separation
	 funspace_succ_replacement well_ord_iso_separation
	 obase_separation obase_equals_separation
	 omap_replacement is_recfun_separation)+
  done

theorem M_axioms_L: "PROP M_axioms(L)"
by (rule M_axioms.intro [OF M_triv_axioms_L M_axioms_axioms_L])


lemmas cartprod_iff = M_axioms.cartprod_iff [OF M_axioms_L]
  and cartprod_closed = M_axioms.cartprod_closed [OF M_axioms_L]
  and sum_closed = M_axioms.sum_closed [OF M_axioms_L]
  and M_converse_iff = M_axioms.M_converse_iff [OF M_axioms_L]
  and converse_closed = M_axioms.converse_closed [OF M_axioms_L]
  and converse_abs = M_axioms.converse_abs [OF M_axioms_L]
  and image_closed = M_axioms.image_closed [OF M_axioms_L]
  and vimage_abs = M_axioms.vimage_abs [OF M_axioms_L]
  and vimage_closed = M_axioms.vimage_closed [OF M_axioms_L]
  and domain_abs = M_axioms.domain_abs [OF M_axioms_L]
  and domain_closed = M_axioms.domain_closed [OF M_axioms_L]
  and range_abs = M_axioms.range_abs [OF M_axioms_L]
  and range_closed = M_axioms.range_closed [OF M_axioms_L]
  and field_abs = M_axioms.field_abs [OF M_axioms_L]
  and field_closed = M_axioms.field_closed [OF M_axioms_L]
  and relation_abs = M_axioms.relation_abs [OF M_axioms_L]
  and function_abs = M_axioms.function_abs [OF M_axioms_L]
  and apply_closed = M_axioms.apply_closed [OF M_axioms_L]
  and apply_abs = M_axioms.apply_abs [OF M_axioms_L]
  and typed_function_abs = M_axioms.typed_function_abs [OF M_axioms_L]
  and injection_abs = M_axioms.injection_abs [OF M_axioms_L]
  and surjection_abs = M_axioms.surjection_abs [OF M_axioms_L]
  and bijection_abs = M_axioms.bijection_abs [OF M_axioms_L]
  and M_comp_iff = M_axioms.M_comp_iff [OF M_axioms_L]
  and comp_closed = M_axioms.comp_closed [OF M_axioms_L]
  and composition_abs = M_axioms.composition_abs [OF M_axioms_L]
  and restriction_is_function = M_axioms.restriction_is_function [OF M_axioms_L]
  and restriction_abs = M_axioms.restriction_abs [OF M_axioms_L]
  and M_restrict_iff = M_axioms.M_restrict_iff [OF M_axioms_L]
  and restrict_closed = M_axioms.restrict_closed [OF M_axioms_L]
  and Inter_abs = M_axioms.Inter_abs [OF M_axioms_L]
  and Inter_closed = M_axioms.Inter_closed [OF M_axioms_L]
  and Int_closed = M_axioms.Int_closed [OF M_axioms_L]
  and finite_fun_closed = M_axioms.finite_fun_closed [OF M_axioms_L]
  and is_funspace_abs = M_axioms.is_funspace_abs [OF M_axioms_L]
  and succ_fun_eq2 = M_axioms.succ_fun_eq2 [OF M_axioms_L]
  and funspace_succ = M_axioms.funspace_succ [OF M_axioms_L]
  and finite_funspace_closed = M_axioms.finite_funspace_closed [OF M_axioms_L]

lemmas is_recfun_equal = M_axioms.is_recfun_equal [OF M_axioms_L]
  and is_recfun_cut = M_axioms.is_recfun_cut [OF M_axioms_L]
  and is_recfun_functional = M_axioms.is_recfun_functional [OF M_axioms_L]
  and is_recfun_relativize = M_axioms.is_recfun_relativize [OF M_axioms_L]
  and is_recfun_restrict = M_axioms.is_recfun_restrict [OF M_axioms_L]
  and univalent_is_recfun = M_axioms.univalent_is_recfun [OF M_axioms_L]
  and exists_is_recfun_indstep = M_axioms.exists_is_recfun_indstep [OF M_axioms_L]
  and wellfounded_exists_is_recfun = M_axioms.wellfounded_exists_is_recfun [OF M_axioms_L]
  and wf_exists_is_recfun = M_axioms.wf_exists_is_recfun [OF M_axioms_L]
  and is_recfun_abs = M_axioms.is_recfun_abs [OF M_axioms_L]
  and irreflexive_abs = M_axioms.irreflexive_abs [OF M_axioms_L]
  and transitive_rel_abs = M_axioms.transitive_rel_abs [OF M_axioms_L]
  and linear_rel_abs = M_axioms.linear_rel_abs [OF M_axioms_L]
  and wellordered_is_trans_on = M_axioms.wellordered_is_trans_on [OF M_axioms_L]
  and wellordered_is_linear = M_axioms.wellordered_is_linear [OF M_axioms_L]
  and wellordered_is_wellfounded_on = M_axioms.wellordered_is_wellfounded_on [OF M_axioms_L]
  and wellfounded_imp_wellfounded_on = M_axioms.wellfounded_imp_wellfounded_on [OF M_axioms_L]
  and wellfounded_on_subset_A = M_axioms.wellfounded_on_subset_A [OF M_axioms_L]
  and wellfounded_on_iff_wellfounded = M_axioms.wellfounded_on_iff_wellfounded [OF M_axioms_L]
  and wellfounded_on_imp_wellfounded = M_axioms.wellfounded_on_imp_wellfounded [OF M_axioms_L]
  and wellfounded_on_field_imp_wellfounded = M_axioms.wellfounded_on_field_imp_wellfounded [OF M_axioms_L]
  and wellfounded_iff_wellfounded_on_field = M_axioms.wellfounded_iff_wellfounded_on_field [OF M_axioms_L]
  and wellfounded_induct = M_axioms.wellfounded_induct [OF M_axioms_L]
  and wellfounded_on_induct = M_axioms.wellfounded_on_induct [OF M_axioms_L]
  and wellfounded_on_induct2 = M_axioms.wellfounded_on_induct2 [OF M_axioms_L]
  and linear_imp_relativized = M_axioms.linear_imp_relativized [OF M_axioms_L]
  and trans_on_imp_relativized = M_axioms.trans_on_imp_relativized [OF M_axioms_L]
  and wf_on_imp_relativized = M_axioms.wf_on_imp_relativized [OF M_axioms_L]
  and wf_imp_relativized = M_axioms.wf_imp_relativized [OF M_axioms_L]
  and well_ord_imp_relativized = M_axioms.well_ord_imp_relativized [OF M_axioms_L]
  and order_isomorphism_abs = M_axioms.order_isomorphism_abs [OF M_axioms_L]
  and pred_set_abs = M_axioms.pred_set_abs [OF M_axioms_L]

lemmas pred_closed = M_axioms.pred_closed [OF M_axioms_L]
  and membership_abs = M_axioms.membership_abs [OF M_axioms_L]
  and M_Memrel_iff = M_axioms.M_Memrel_iff [OF M_axioms_L]
  and Memrel_closed = M_axioms.Memrel_closed [OF M_axioms_L]
  and wellordered_iso_predD = M_axioms.wellordered_iso_predD [OF M_axioms_L]
  and wellordered_iso_pred_eq = M_axioms.wellordered_iso_pred_eq [OF M_axioms_L]
  and wellfounded_on_asym = M_axioms.wellfounded_on_asym [OF M_axioms_L]
  and wellordered_asym = M_axioms.wellordered_asym [OF M_axioms_L]
  and ord_iso_pred_imp_lt = M_axioms.ord_iso_pred_imp_lt [OF M_axioms_L]
  and obase_iff = M_axioms.obase_iff [OF M_axioms_L]
  and omap_iff = M_axioms.omap_iff [OF M_axioms_L]
  and omap_unique = M_axioms.omap_unique [OF M_axioms_L]
  and omap_yields_Ord = M_axioms.omap_yields_Ord [OF M_axioms_L]
  and otype_iff = M_axioms.otype_iff [OF M_axioms_L]
  and otype_eq_range = M_axioms.otype_eq_range [OF M_axioms_L]
  and Ord_otype = M_axioms.Ord_otype [OF M_axioms_L]
  and domain_omap = M_axioms.domain_omap [OF M_axioms_L]
  and omap_subset = M_axioms.omap_subset [OF M_axioms_L]
  and omap_funtype = M_axioms.omap_funtype [OF M_axioms_L]
  and wellordered_omap_bij = M_axioms.wellordered_omap_bij [OF M_axioms_L]
  and omap_ord_iso = M_axioms.omap_ord_iso [OF M_axioms_L]
  and Ord_omap_image_pred = M_axioms.Ord_omap_image_pred [OF M_axioms_L]
  and restrict_omap_ord_iso = M_axioms.restrict_omap_ord_iso [OF M_axioms_L]
  and obase_equals = M_axioms.obase_equals [OF M_axioms_L]
  and omap_ord_iso_otype = M_axioms.omap_ord_iso_otype [OF M_axioms_L]
  and obase_exists = M_axioms.obase_exists [OF M_axioms_L]
  and omap_exists = M_axioms.omap_exists [OF M_axioms_L]
  and otype_exists = M_axioms.otype_exists [OF M_axioms_L]
  and omap_ord_iso_otype' = M_axioms.omap_ord_iso_otype' [OF M_axioms_L]
  and ordertype_exists = M_axioms.ordertype_exists [OF M_axioms_L]
  and relativized_imp_well_ord = M_axioms.relativized_imp_well_ord [OF M_axioms_L]
  and well_ord_abs = M_axioms.well_ord_abs [OF M_axioms_L]

declare cartprod_closed [intro, simp]
declare sum_closed [intro, simp]
declare converse_closed [intro, simp]
declare converse_abs [simp]
declare image_closed [intro, simp]
declare vimage_abs [simp]
declare vimage_closed [intro, simp]
declare domain_abs [simp]
declare domain_closed [intro, simp]
declare range_abs [simp]
declare range_closed [intro, simp]
declare field_abs [simp]
declare field_closed [intro, simp]
declare relation_abs [simp]
declare function_abs [simp]
declare apply_closed [intro, simp]
declare typed_function_abs [simp]
declare injection_abs [simp]
declare surjection_abs [simp]
declare bijection_abs [simp]
declare comp_closed [intro, simp]
declare composition_abs [simp]
declare restriction_abs [simp]
declare restrict_closed [intro, simp]
declare Inter_abs [simp]
declare Inter_closed [intro, simp]
declare Int_closed [intro, simp]
declare is_funspace_abs [simp]
declare finite_funspace_closed [intro, simp]

end
