header{*Some Instances of Separation and Strong Replacement*}

(*This theory proves all instances needed for locale M_axioms*)

theory Separation = L_axioms + WFrec:

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
apply (rule DPowI2) 
apply (rule ball_iff_sats) 
apply (rule imp_iff_sats)
apply (rule_tac [2] i=1 and j=0 and env="[y,x,A]" in mem_iff_sats)
apply (rule_tac i=0 and j=2 in mem_iff_sats)
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u)  
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule_tac i=0 and j=2 and env="[x,u,A,B]" in mem_iff_sats, simp_all)
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule_tac env="[p,y,A,r]" in mem_iff_sats)
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule_tac i=0 and j="2" and env="[p,u,r]" in mem_iff_sats, simp_all)
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats) 
apply (rule conj_iff_sats)
apply (rule_tac i=0 and j="2" and env="[x,u,A]" in mem_iff_sats, simp_all)
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats)+
apply (rename_tac x y z)  
apply (rule conj_iff_sats)
apply (rule_tac env="[z,y,x,u,r,s]" in pair_iff_sats)
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac env = "[p,u,r,x]" in mem_iff_sats) 
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[y,x,u]" in pair_iff_sats) 
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac env = "[x,u,n,A]" in mem_iff_sats) 
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule imp_iff_sats)
apply (rule_tac env = "[u,A,f,r]" in mem_iff_sats) 
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats)
apply (rule conj_iff_sats)
apply (rule_tac env = "[x,u,A,r]" in ordinal_iff_sats) 
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule imp_iff_sats ball_iff_sats disj_iff_sats not_iff_sats)+
apply (rule_tac env = "[u,A,r]" in mem_iff_sats) 
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[x,u,A,B,r]" in mem_iff_sats) 
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
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
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[x,u,r,f,g,a,b]" in pair_iff_sats) 
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
done


ML
{*
val Inter_separation = thm "Inter_separation";
val cartprod_separation = thm "cartprod_separation";
val image_separation = thm "image_separation";
val converse_separation = thm "converse_separation";
val restrict_separation = thm "restrict_separation";
val comp_separation = thm "comp_separation";
val pred_separation = thm "pred_separation";
val Memrel_separation = thm "Memrel_separation";
val funspace_succ_replacement = thm "funspace_succ_replacement";
val well_ord_iso_separation = thm "well_ord_iso_separation";
val obase_separation = thm "obase_separation";
val obase_equals_separation = thm "obase_equals_separation";
val omap_replacement = thm "omap_replacement";
val is_recfun_separation = thm "is_recfun_separation";

val m_axioms = 
    [Inter_separation, cartprod_separation, image_separation, 
     converse_separation, restrict_separation, comp_separation, 
     pred_separation, Memrel_separation, funspace_succ_replacement, 
     well_ord_iso_separation, obase_separation,
     obase_equals_separation, omap_replacement, is_recfun_separation]

fun axiomsL th =
    kill_flex_triv_prems (m_axioms MRS (trivaxL th));

bind_thm ("cartprod_iff", axiomsL (thm "M_axioms.cartprod_iff"));
bind_thm ("cartprod_closed", axiomsL (thm "M_axioms.cartprod_closed"));
bind_thm ("sum_closed", axiomsL (thm "M_axioms.sum_closed"));
bind_thm ("M_converse_iff", axiomsL (thm "M_axioms.M_converse_iff"));
bind_thm ("converse_closed", axiomsL (thm "M_axioms.converse_closed"));
bind_thm ("converse_abs", axiomsL (thm "M_axioms.converse_abs"));
bind_thm ("image_closed", axiomsL (thm "M_axioms.image_closed"));
bind_thm ("vimage_abs", axiomsL (thm "M_axioms.vimage_abs"));
bind_thm ("vimage_closed", axiomsL (thm "M_axioms.vimage_closed"));
bind_thm ("domain_abs", axiomsL (thm "M_axioms.domain_abs"));
bind_thm ("domain_closed", axiomsL (thm "M_axioms.domain_closed"));
bind_thm ("range_abs", axiomsL (thm "M_axioms.range_abs"));
bind_thm ("range_closed", axiomsL (thm "M_axioms.range_closed"));
bind_thm ("field_abs", axiomsL (thm "M_axioms.field_abs"));
bind_thm ("field_closed", axiomsL (thm "M_axioms.field_closed"));
bind_thm ("relation_abs", axiomsL (thm "M_axioms.relation_abs"));
bind_thm ("function_abs", axiomsL (thm "M_axioms.function_abs"));
bind_thm ("apply_closed", axiomsL (thm "M_axioms.apply_closed"));
bind_thm ("apply_abs", axiomsL (thm "M_axioms.apply_abs"));
bind_thm ("typed_apply_abs", axiomsL (thm "M_axioms.typed_apply_abs"));
bind_thm ("typed_function_abs", axiomsL (thm "M_axioms.typed_function_abs"));
bind_thm ("injection_abs", axiomsL (thm "M_axioms.injection_abs"));
bind_thm ("surjection_abs", axiomsL (thm "M_axioms.surjection_abs"));
bind_thm ("bijection_abs", axiomsL (thm "M_axioms.bijection_abs"));
bind_thm ("M_comp_iff", axiomsL (thm "M_axioms.M_comp_iff"));
bind_thm ("comp_closed", axiomsL (thm "M_axioms.comp_closed"));
bind_thm ("composition_abs", axiomsL (thm "M_axioms.composition_abs"));
bind_thm ("restriction_is_function", axiomsL (thm "M_axioms.restriction_is_function"));
bind_thm ("restriction_abs", axiomsL (thm "M_axioms.restriction_abs"));
bind_thm ("M_restrict_iff", axiomsL (thm "M_axioms.M_restrict_iff"));
bind_thm ("restrict_closed", axiomsL (thm "M_axioms.restrict_closed"));
bind_thm ("Inter_abs", axiomsL (thm "M_axioms.Inter_abs"));
bind_thm ("Inter_closed", axiomsL (thm "M_axioms.Inter_closed"));
bind_thm ("Int_closed", axiomsL (thm "M_axioms.Int_closed"));
bind_thm ("finite_fun_closed", axiomsL (thm "M_axioms.finite_fun_closed"));
bind_thm ("is_funspace_abs", axiomsL (thm "M_axioms.is_funspace_abs"));
bind_thm ("succ_fun_eq2", axiomsL (thm "M_axioms.succ_fun_eq2"));
bind_thm ("funspace_succ", axiomsL (thm "M_axioms.funspace_succ"));
bind_thm ("finite_funspace_closed", axiomsL (thm "M_axioms.finite_funspace_closed"));
*}

ML
{*
bind_thm ("is_recfun_equal", axiomsL (thm "M_axioms.is_recfun_equal"));  
bind_thm ("is_recfun_cut", axiomsL (thm "M_axioms.is_recfun_cut")); 
bind_thm ("is_recfun_functional", axiomsL (thm "M_axioms.is_recfun_functional"));
bind_thm ("is_recfun_relativize", axiomsL (thm "M_axioms.is_recfun_relativize"));
bind_thm ("is_recfun_restrict", axiomsL (thm "M_axioms.is_recfun_restrict"));
bind_thm ("univalent_is_recfun", axiomsL (thm "M_axioms.univalent_is_recfun"));
bind_thm ("exists_is_recfun_indstep", axiomsL (thm "M_axioms.exists_is_recfun_indstep"));
bind_thm ("wellfounded_exists_is_recfun", axiomsL (thm "M_axioms.wellfounded_exists_is_recfun"));
bind_thm ("wf_exists_is_recfun", axiomsL (thm "M_axioms.wf_exists_is_recfun")); 
bind_thm ("is_recfun_iff_M", axiomsL (thm "M_axioms.is_recfun_iff_M"));
bind_thm ("irreflexive_abs", axiomsL (thm "M_axioms.irreflexive_abs"));  
bind_thm ("transitive_rel_abs", axiomsL (thm "M_axioms.transitive_rel_abs"));  
bind_thm ("linear_rel_abs", axiomsL (thm "M_axioms.linear_rel_abs"));  
bind_thm ("wellordered_is_trans_on", axiomsL (thm "M_axioms.wellordered_is_trans_on")); 
bind_thm ("wellordered_is_linear", axiomsL (thm "M_axioms.wellordered_is_linear")); 
bind_thm ("wellordered_is_wellfounded_on", axiomsL (thm "M_axioms.wellordered_is_wellfounded_on")); 
bind_thm ("wellfounded_imp_wellfounded_on", axiomsL (thm "M_axioms.wellfounded_imp_wellfounded_on")); 
bind_thm ("wellfounded_on_subset_A", axiomsL (thm "M_axioms.wellfounded_on_subset_A"));
bind_thm ("wellfounded_on_iff_wellfounded", axiomsL (thm "M_axioms.wellfounded_on_iff_wellfounded"));
bind_thm ("wellfounded_on_imp_wellfounded", axiomsL (thm "M_axioms.wellfounded_on_imp_wellfounded"));
bind_thm ("wellfounded_on_field_imp_wellfounded", axiomsL (thm "M_axioms.wellfounded_on_field_imp_wellfounded"));
bind_thm ("wellfounded_iff_wellfounded_on_field", axiomsL (thm "M_axioms.wellfounded_iff_wellfounded_on_field"));
bind_thm ("wellfounded_induct", axiomsL (thm "M_axioms.wellfounded_induct")); 
bind_thm ("wellfounded_on_induct", axiomsL (thm "M_axioms.wellfounded_on_induct")); 
bind_thm ("wellfounded_on_induct2", axiomsL (thm "M_axioms.wellfounded_on_induct2")); 
bind_thm ("linear_imp_relativized", axiomsL (thm "M_axioms.linear_imp_relativized")); 
bind_thm ("trans_on_imp_relativized", axiomsL (thm "M_axioms.trans_on_imp_relativized")); 
bind_thm ("wf_on_imp_relativized", axiomsL (thm "M_axioms.wf_on_imp_relativized")); 
bind_thm ("wf_imp_relativized", axiomsL (thm "M_axioms.wf_imp_relativized")); 
bind_thm ("well_ord_imp_relativized", axiomsL (thm "M_axioms.well_ord_imp_relativized")); 
bind_thm ("order_isomorphism_abs", axiomsL (thm "M_axioms.order_isomorphism_abs"));  
bind_thm ("pred_set_abs", axiomsL (thm "M_axioms.pred_set_abs"));  
*}

ML
{*
bind_thm ("pred_closed", axiomsL (thm "M_axioms.pred_closed"));  
bind_thm ("membership_abs", axiomsL (thm "M_axioms.membership_abs"));  
bind_thm ("M_Memrel_iff", axiomsL (thm "M_axioms.M_Memrel_iff"));
bind_thm ("Memrel_closed", axiomsL (thm "M_axioms.Memrel_closed"));  
bind_thm ("wellordered_iso_predD", axiomsL (thm "M_axioms.wellordered_iso_predD"));
bind_thm ("wellordered_iso_pred_eq", axiomsL (thm "M_axioms.wellordered_iso_pred_eq"));
bind_thm ("wellfounded_on_asym", axiomsL (thm "M_axioms.wellfounded_on_asym"));
bind_thm ("wellordered_asym", axiomsL (thm "M_axioms.wellordered_asym"));
bind_thm ("ord_iso_pred_imp_lt", axiomsL (thm "M_axioms.ord_iso_pred_imp_lt"));
bind_thm ("obase_iff", axiomsL (thm "M_axioms.obase_iff"));
bind_thm ("omap_iff", axiomsL (thm "M_axioms.omap_iff"));
bind_thm ("omap_unique", axiomsL (thm "M_axioms.omap_unique"));
bind_thm ("omap_yields_Ord", axiomsL (thm "M_axioms.omap_yields_Ord"));
bind_thm ("otype_iff", axiomsL (thm "M_axioms.otype_iff"));
bind_thm ("otype_eq_range", axiomsL (thm "M_axioms.otype_eq_range"));
bind_thm ("Ord_otype", axiomsL (thm "M_axioms.Ord_otype"));
bind_thm ("domain_omap", axiomsL (thm "M_axioms.domain_omap"));
bind_thm ("omap_subset", axiomsL (thm "M_axioms.omap_subset")); 
bind_thm ("omap_funtype", axiomsL (thm "M_axioms.omap_funtype")); 
bind_thm ("wellordered_omap_bij", axiomsL (thm "M_axioms.wellordered_omap_bij"));
bind_thm ("omap_ord_iso", axiomsL (thm "M_axioms.omap_ord_iso"));
bind_thm ("Ord_omap_image_pred", axiomsL (thm "M_axioms.Ord_omap_image_pred"));
bind_thm ("restrict_omap_ord_iso", axiomsL (thm "M_axioms.restrict_omap_ord_iso"));
bind_thm ("obase_equals", axiomsL (thm "M_axioms.obase_equals")); 
bind_thm ("omap_ord_iso_otype", axiomsL (thm "M_axioms.omap_ord_iso_otype"));
bind_thm ("obase_exists", axiomsL (thm "M_axioms.obase_exists"));
bind_thm ("omap_exists", axiomsL (thm "M_axioms.omap_exists"));
bind_thm ("otype_exists", axiomsL (thm "M_axioms.otype_exists"));
bind_thm ("omap_ord_iso_otype", axiomsL (thm "M_axioms.omap_ord_iso_otype"));
bind_thm ("ordertype_exists", axiomsL (thm "M_axioms.ordertype_exists"));
bind_thm ("relativized_imp_well_ord", axiomsL (thm "M_axioms.relativized_imp_well_ord")); 
bind_thm ("well_ord_abs", axiomsL (thm "M_axioms.well_ord_abs"));  
*}

declare cartprod_closed [intro,simp]
declare sum_closed [intro,simp]
declare converse_closed [intro,simp]
declare converse_abs [simp]
declare image_closed [intro,simp]
declare vimage_abs [simp]
declare vimage_closed [intro,simp]
declare domain_abs [simp]
declare domain_closed [intro,simp]
declare range_abs [simp]
declare range_closed [intro,simp]
declare field_abs [simp]
declare field_closed [intro,simp]
declare relation_abs [simp]
declare function_abs [simp]
declare apply_closed [intro,simp]
declare typed_function_abs [simp]
declare injection_abs [simp]
declare surjection_abs [simp]
declare bijection_abs [simp]
declare comp_closed [intro,simp]
declare composition_abs [simp]
declare restriction_abs [simp]
declare restrict_closed [intro,simp]
declare Inter_abs [simp]
declare Inter_closed [intro,simp]
declare Int_closed [intro,simp]
declare finite_fun_closed [rule_format]
declare is_funspace_abs [simp]
declare finite_funspace_closed [intro,simp]


(***NOW FOR THE LOCALE M_TRANCL***)

subsection{*Separation for Reflexive/Transitive Closure*}

lemma rtrancl_reflects:
  "REFLECTS[\<lambda>p. 
    \<exists>nnat[L]. \<exists>n[L]. \<exists>n'[L]. omega(L,nnat) & n\<in>nnat & successor(L,n,n') &
     (\<exists>f[L]. 
      typed_function(L,n',A,f) &
      (\<exists>x[L]. \<exists>y[L]. \<exists>zero[L]. pair(L,x,y,p) & empty(L,zero) &
	fun_apply(L,f,zero,x) & fun_apply(L,f,n,y)) &
	(\<forall>j[L]. j\<in>n --> 
	  (\<exists>fj[L]. \<exists>sj[L]. \<exists>fsj[L]. \<exists>ffp[L]. 
	    fun_apply(L,f,j,fj) & successor(L,j,sj) &
	    fun_apply(L,f,sj,fsj) & pair(L,fj,fsj,ffp) & ffp \<in> r))),
\<lambda>i p. 
    \<exists>nnat \<in> Lset(i). \<exists>n \<in> Lset(i). \<exists>n' \<in> Lset(i). 
     omega(**Lset(i),nnat) & n\<in>nnat & successor(**Lset(i),n,n') &
     (\<exists>f \<in> Lset(i). 
      typed_function(**Lset(i),n',A,f) &
      (\<exists>x \<in> Lset(i). \<exists>y \<in> Lset(i). \<exists>zero \<in> Lset(i). pair(**Lset(i),x,y,p) & empty(**Lset(i),zero) &
	fun_apply(**Lset(i),f,zero,x) & fun_apply(**Lset(i),f,n,y)) &
	(\<forall>j \<in> Lset(i). j\<in>n --> 
	  (\<exists>fj \<in> Lset(i). \<exists>sj \<in> Lset(i). \<exists>fsj \<in> Lset(i). \<exists>ffp \<in> Lset(i). 
	    fun_apply(**Lset(i),f,j,fj) & successor(**Lset(i),j,sj) &
	    fun_apply(**Lset(i),f,sj,fsj) & pair(**Lset(i),fj,fsj,ffp) & ffp \<in> r)))]"
by (intro FOL_reflections function_reflections fun_plus_reflections)


text{*This formula describes @{term "rtrancl(r)"}.*}
lemma rtrancl_separation:
     "[| L(r); L(A) |] ==>
      separation (L, \<lambda>p. 
	  \<exists>nnat[L]. \<exists>n[L]. \<exists>n'[L]. 
           omega(L,nnat) & n\<in>nnat & successor(L,n,n') &
	   (\<exists>f[L]. 
	    typed_function(L,n',A,f) &
	    (\<exists>x[L]. \<exists>y[L]. \<exists>zero[L]. pair(L,x,y,p) & empty(L,zero) &
	      fun_apply(L,f,zero,x) & fun_apply(L,f,n,y)) &
	      (\<forall>j[L]. j\<in>n --> 
		(\<exists>fj[L]. \<exists>sj[L]. \<exists>fsj[L]. \<exists>ffp[L]. 
		  fun_apply(L,f,j,fj) & successor(L,j,sj) &
		  fun_apply(L,f,sj,fsj) & pair(L,fj,fsj,ffp) & ffp \<in> r))))"
apply (rule separation_CollectI) 
apply (rule_tac A="{r,A,z}" in subset_LsetE, blast ) 
apply (rule ReflectsE [OF rtrancl_reflects], assumption)
apply (drule subset_Lset_ltD, assumption) 
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2)
apply (rule DPowI2)
apply (rename_tac u) 
apply (rule bex_iff_sats conj_iff_sats)+
apply (rule_tac env = "[x,u,r,A]" in omega_iff_sats)
txt{*SLOW, maybe just due to the formula's size*}
apply (rule sep_rules | simp)+
apply (simp_all add: succ_Un_distrib [symmetric])
done


end
