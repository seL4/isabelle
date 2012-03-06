(*  Title:      ZF/Constructible/Separation.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header{*Early Instances of Separation and Strong Replacement*}

theory Separation imports L_axioms WF_absolute begin

text{*This theory proves all instances needed for locale @{text "M_basic"}*}

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
      "[| \<forall>x\<in>Lset(j). P(x) \<longleftrightarrow> Q(x);
          {x \<in> Lset(j) . Q(x)} \<in> DPow(Lset(j));
          Ord(j);  z \<in> Lset(j)|] ==> L({x \<in> z . P(x)})"
apply (rule_tac i = "succ(j)" in L_I)
 prefer 2 apply simp
apply (subgoal_tac "{x \<in> z. P(x)} = {x \<in> Lset(j). x \<in> z & (Q(x))}")
 prefer 2
 apply (blast dest: mem_Lset_imp_subset_Lset)
apply (simp add: Lset_succ Collect_conj_in_DPow_Lset)
done

text{*Encapsulates the standard proof script for proving instances of 
      Separation.*}
lemma gen_separation:
 assumes reflection: "REFLECTS [P,Q]"
     and Lu:         "L(u)"
     and collI: "!!j. u \<in> Lset(j)
                \<Longrightarrow> Collect(Lset(j), Q(j)) \<in> DPow(Lset(j))"
 shows "separation(L,P)"
apply (rule separation_CollectI)
apply (rule_tac A="{u,z}" in subset_LsetE, blast intro: Lu)
apply (rule ReflectsE [OF reflection], assumption)
apply (drule subset_Lset_ltD, assumption)
apply (erule reflection_imp_L_separation)
  apply (simp_all add: lt_Ord2, clarify)
apply (rule collI, assumption)
done

text{*As above, but typically @{term u} is a finite enumeration such as
  @{term "{a,b}"}; thus the new subgoal gets the assumption
  @{term "{a,b} \<subseteq> Lset(i)"}, which is logically equivalent to 
  @{term "a \<in> Lset(i)"} and @{term "b \<in> Lset(i)"}.*}
lemma gen_separation_multi:
 assumes reflection: "REFLECTS [P,Q]"
     and Lu:         "L(u)"
     and collI: "!!j. u \<subseteq> Lset(j)
                \<Longrightarrow> Collect(Lset(j), Q(j)) \<in> DPow(Lset(j))"
 shows "separation(L,P)"
apply (rule gen_separation [OF reflection Lu])
apply (drule mem_Lset_imp_subset_Lset)
apply (erule collI) 
done


subsection{*Separation for Intersection*}

lemma Inter_Reflects:
     "REFLECTS[\<lambda>x. \<forall>y[L]. y\<in>A \<longrightarrow> x \<in> y,
               \<lambda>i x. \<forall>y\<in>Lset(i). y\<in>A \<longrightarrow> x \<in> y]"
by (intro FOL_reflections)

lemma Inter_separation:
     "L(A) ==> separation(L, \<lambda>x. \<forall>y[L]. y\<in>A \<longrightarrow> x\<in>y)"
apply (rule gen_separation [OF Inter_Reflects], simp)
apply (rule DPow_LsetI)
 txt{*I leave this one example of a manual proof.  The tedium of manually
      instantiating @{term i}, @{term j} and @{term env} is obvious. *}
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
apply (rule gen_separation [OF Diff_Reflects], simp)
apply (rule_tac env="[B]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done

subsection{*Separation for Cartesian Product*}

lemma cartprod_Reflects:
     "REFLECTS[\<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. y\<in>B & pair(L,x,y,z)),
                \<lambda>i z. \<exists>x\<in>Lset(i). x\<in>A & (\<exists>y\<in>Lset(i). y\<in>B &
                                   pair(##Lset(i),x,y,z))]"
by (intro FOL_reflections function_reflections)

lemma cartprod_separation:
     "[| L(A); L(B) |]
      ==> separation(L, \<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. y\<in>B & pair(L,x,y,z)))"
apply (rule gen_separation_multi [OF cartprod_Reflects, of "{A,B}"], auto)
apply (rule_tac env="[A,B]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done

subsection{*Separation for Image*}

lemma image_Reflects:
     "REFLECTS[\<lambda>y. \<exists>p[L]. p\<in>r & (\<exists>x[L]. x\<in>A & pair(L,x,y,p)),
           \<lambda>i y. \<exists>p\<in>Lset(i). p\<in>r & (\<exists>x\<in>Lset(i). x\<in>A & pair(##Lset(i),x,y,p))]"
by (intro FOL_reflections function_reflections)

lemma image_separation:
     "[| L(A); L(r) |]
      ==> separation(L, \<lambda>y. \<exists>p[L]. p\<in>r & (\<exists>x[L]. x\<in>A & pair(L,x,y,p)))"
apply (rule gen_separation_multi [OF image_Reflects, of "{A,r}"], auto)
apply (rule_tac env="[A,r]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection{*Separation for Converse*}

lemma converse_Reflects:
  "REFLECTS[\<lambda>z. \<exists>p[L]. p\<in>r & (\<exists>x[L]. \<exists>y[L]. pair(L,x,y,p) & pair(L,y,x,z)),
     \<lambda>i z. \<exists>p\<in>Lset(i). p\<in>r & (\<exists>x\<in>Lset(i). \<exists>y\<in>Lset(i).
                     pair(##Lset(i),x,y,p) & pair(##Lset(i),y,x,z))]"
by (intro FOL_reflections function_reflections)

lemma converse_separation:
     "L(r) ==> separation(L,
         \<lambda>z. \<exists>p[L]. p\<in>r & (\<exists>x[L]. \<exists>y[L]. pair(L,x,y,p) & pair(L,y,x,z)))"
apply (rule gen_separation [OF converse_Reflects], simp)
apply (rule_tac env="[r]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection{*Separation for Restriction*}

lemma restrict_Reflects:
     "REFLECTS[\<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. pair(L,x,y,z)),
        \<lambda>i z. \<exists>x\<in>Lset(i). x\<in>A & (\<exists>y\<in>Lset(i). pair(##Lset(i),x,y,z))]"
by (intro FOL_reflections function_reflections)

lemma restrict_separation:
   "L(A) ==> separation(L, \<lambda>z. \<exists>x[L]. x\<in>A & (\<exists>y[L]. pair(L,x,y,z)))"
apply (rule gen_separation [OF restrict_Reflects], simp)
apply (rule_tac env="[A]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection{*Separation for Composition*}

lemma comp_Reflects:
     "REFLECTS[\<lambda>xz. \<exists>x[L]. \<exists>y[L]. \<exists>z[L]. \<exists>xy[L]. \<exists>yz[L].
                  pair(L,x,z,xz) & pair(L,x,y,xy) & pair(L,y,z,yz) &
                  xy\<in>s & yz\<in>r,
        \<lambda>i xz. \<exists>x\<in>Lset(i). \<exists>y\<in>Lset(i). \<exists>z\<in>Lset(i). \<exists>xy\<in>Lset(i). \<exists>yz\<in>Lset(i).
                  pair(##Lset(i),x,z,xz) & pair(##Lset(i),x,y,xy) &
                  pair(##Lset(i),y,z,yz) & xy\<in>s & yz\<in>r]"
by (intro FOL_reflections function_reflections)

lemma comp_separation:
     "[| L(r); L(s) |]
      ==> separation(L, \<lambda>xz. \<exists>x[L]. \<exists>y[L]. \<exists>z[L]. \<exists>xy[L]. \<exists>yz[L].
                  pair(L,x,z,xz) & pair(L,x,y,xy) & pair(L,y,z,yz) &
                  xy\<in>s & yz\<in>r)"
apply (rule gen_separation_multi [OF comp_Reflects, of "{r,s}"], auto)
txt{*Subgoals after applying general ``separation'' rule:
     @{subgoals[display,indent=0,margin=65]}*}
apply (rule_tac env="[r,s]" in DPow_LsetI)
txt{*Subgoals ready for automatic synthesis of a formula:
     @{subgoals[display,indent=0,margin=65]}*}
apply (rule sep_rules | simp)+
done


subsection{*Separation for Predecessors in an Order*}

lemma pred_Reflects:
     "REFLECTS[\<lambda>y. \<exists>p[L]. p\<in>r & pair(L,y,x,p),
                    \<lambda>i y. \<exists>p \<in> Lset(i). p\<in>r & pair(##Lset(i),y,x,p)]"
by (intro FOL_reflections function_reflections)

lemma pred_separation:
     "[| L(r); L(x) |] ==> separation(L, \<lambda>y. \<exists>p[L]. p\<in>r & pair(L,y,x,p))"
apply (rule gen_separation_multi [OF pred_Reflects, of "{r,x}"], auto)
apply (rule_tac env="[r,x]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection{*Separation for the Membership Relation*}

lemma Memrel_Reflects:
     "REFLECTS[\<lambda>z. \<exists>x[L]. \<exists>y[L]. pair(L,x,y,z) & x \<in> y,
            \<lambda>i z. \<exists>x \<in> Lset(i). \<exists>y \<in> Lset(i). pair(##Lset(i),x,y,z) & x \<in> y]"
by (intro FOL_reflections function_reflections)

lemma Memrel_separation:
     "separation(L, \<lambda>z. \<exists>x[L]. \<exists>y[L]. pair(L,x,y,z) & x \<in> y)"
apply (rule gen_separation [OF Memrel_Reflects nonempty])
apply (rule_tac env="[]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection{*Replacement for FunSpace*}

lemma funspace_succ_Reflects:
 "REFLECTS[\<lambda>z. \<exists>p[L]. p\<in>A & (\<exists>f[L]. \<exists>b[L]. \<exists>nb[L]. \<exists>cnbf[L].
            pair(L,f,b,p) & pair(L,n,b,nb) & is_cons(L,nb,f,cnbf) &
            upair(L,cnbf,cnbf,z)),
        \<lambda>i z. \<exists>p \<in> Lset(i). p\<in>A & (\<exists>f \<in> Lset(i). \<exists>b \<in> Lset(i).
              \<exists>nb \<in> Lset(i). \<exists>cnbf \<in> Lset(i).
                pair(##Lset(i),f,b,p) & pair(##Lset(i),n,b,nb) &
                is_cons(##Lset(i),nb,f,cnbf) & upair(##Lset(i),cnbf,cnbf,z))]"
by (intro FOL_reflections function_reflections)

lemma funspace_succ_replacement:
     "L(n) ==>
      strong_replacement(L, \<lambda>p z. \<exists>f[L]. \<exists>b[L]. \<exists>nb[L]. \<exists>cnbf[L].
                pair(L,f,b,p) & pair(L,n,b,nb) & is_cons(L,nb,f,cnbf) &
                upair(L,cnbf,cnbf,z))"
apply (rule strong_replacementI)
apply (rule_tac u="{n,B}" in gen_separation_multi [OF funspace_succ_Reflects], 
       auto)
apply (rule_tac env="[n,B]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection{*Separation for a Theorem about @{term "is_recfun"}*}

lemma is_recfun_reflects:
  "REFLECTS[\<lambda>x. \<exists>xa[L]. \<exists>xb[L].
                pair(L,x,a,xa) & xa \<in> r & pair(L,x,b,xb) & xb \<in> r &
                (\<exists>fx[L]. \<exists>gx[L]. fun_apply(L,f,x,fx) & fun_apply(L,g,x,gx) &
                                   fx \<noteq> gx),
   \<lambda>i x. \<exists>xa \<in> Lset(i). \<exists>xb \<in> Lset(i).
          pair(##Lset(i),x,a,xa) & xa \<in> r & pair(##Lset(i),x,b,xb) & xb \<in> r &
                (\<exists>fx \<in> Lset(i). \<exists>gx \<in> Lset(i). fun_apply(##Lset(i),f,x,fx) &
                  fun_apply(##Lset(i),g,x,gx) & fx \<noteq> gx)]"
by (intro FOL_reflections function_reflections fun_plus_reflections)

lemma is_recfun_separation:
     --{*for well-founded recursion*}
     "[| L(r); L(f); L(g); L(a); L(b) |]
     ==> separation(L,
            \<lambda>x. \<exists>xa[L]. \<exists>xb[L].
                pair(L,x,a,xa) & xa \<in> r & pair(L,x,b,xb) & xb \<in> r &
                (\<exists>fx[L]. \<exists>gx[L]. fun_apply(L,f,x,fx) & fun_apply(L,g,x,gx) &
                                   fx \<noteq> gx))"
apply (rule gen_separation_multi [OF is_recfun_reflects, of "{r,f,g,a,b}"], 
            auto)
apply (rule_tac env="[r,f,g,a,b]" in DPow_LsetI)
apply (rule sep_rules | simp)+
done


subsection{*Instantiating the locale @{text M_basic}*}
text{*Separation (and Strong Replacement) for basic set-theoretic constructions
such as intersection, Cartesian Product and image.*}

lemma M_basic_axioms_L: "M_basic_axioms(L)"
  apply (rule M_basic_axioms.intro)
       apply (assumption | rule
         Inter_separation Diff_separation cartprod_separation image_separation
         converse_separation restrict_separation
         comp_separation pred_separation Memrel_separation
         funspace_succ_replacement is_recfun_separation)+
  done

theorem M_basic_L: "PROP M_basic(L)"
by (rule M_basic.intro [OF M_trivial_L M_basic_axioms_L])

interpretation L?: M_basic L by (rule M_basic_L)


end
