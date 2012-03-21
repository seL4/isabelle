(*  Title:      ZF/Constructible/Wellorderings.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header {*Relativized Wellorderings*}

theory Wellorderings imports Relative begin

text{*We define functions analogous to @{term ordermap} @{term ordertype} 
      but without using recursion.  Instead, there is a direct appeal
      to Replacement.  This will be the basis for a version relativized
      to some class @{text M}.  The main result is Theorem I 7.6 in Kunen,
      page 17.*}


subsection{*Wellorderings*}

definition
  irreflexive :: "[i=>o,i,i]=>o" where
    "irreflexive(M,A,r) == \<forall>x[M]. x\<in>A \<longrightarrow> <x,x> \<notin> r"
  
definition
  transitive_rel :: "[i=>o,i,i]=>o" where
    "transitive_rel(M,A,r) == 
        \<forall>x[M]. x\<in>A \<longrightarrow> (\<forall>y[M]. y\<in>A \<longrightarrow> (\<forall>z[M]. z\<in>A \<longrightarrow> 
                          <x,y>\<in>r \<longrightarrow> <y,z>\<in>r \<longrightarrow> <x,z>\<in>r))"

definition
  linear_rel :: "[i=>o,i,i]=>o" where
    "linear_rel(M,A,r) == 
        \<forall>x[M]. x\<in>A \<longrightarrow> (\<forall>y[M]. y\<in>A \<longrightarrow> <x,y>\<in>r | x=y | <y,x>\<in>r)"

definition
  wellfounded :: "[i=>o,i]=>o" where
    --{*EVERY non-empty set has an @{text r}-minimal element*}
    "wellfounded(M,r) == 
        \<forall>x[M]. x\<noteq>0 \<longrightarrow> (\<exists>y[M]. y\<in>x & ~(\<exists>z[M]. z\<in>x & <z,y> \<in> r))"
definition
  wellfounded_on :: "[i=>o,i,i]=>o" where
    --{*every non-empty SUBSET OF @{text A} has an @{text r}-minimal element*}
    "wellfounded_on(M,A,r) == 
        \<forall>x[M]. x\<noteq>0 \<longrightarrow> x\<subseteq>A \<longrightarrow> (\<exists>y[M]. y\<in>x & ~(\<exists>z[M]. z\<in>x & <z,y> \<in> r))"

definition
  wellordered :: "[i=>o,i,i]=>o" where
    --{*linear and wellfounded on @{text A}*}
    "wellordered(M,A,r) == 
        transitive_rel(M,A,r) & linear_rel(M,A,r) & wellfounded_on(M,A,r)"


subsubsection {*Trivial absoluteness proofs*}

lemma (in M_basic) irreflexive_abs [simp]: 
     "M(A) ==> irreflexive(M,A,r) \<longleftrightarrow> irrefl(A,r)"
by (simp add: irreflexive_def irrefl_def)

lemma (in M_basic) transitive_rel_abs [simp]: 
     "M(A) ==> transitive_rel(M,A,r) \<longleftrightarrow> trans[A](r)"
by (simp add: transitive_rel_def trans_on_def)

lemma (in M_basic) linear_rel_abs [simp]: 
     "M(A) ==> linear_rel(M,A,r) \<longleftrightarrow> linear(A,r)"
by (simp add: linear_rel_def linear_def)

lemma (in M_basic) wellordered_is_trans_on: 
    "[| wellordered(M,A,r); M(A) |] ==> trans[A](r)"
by (auto simp add: wellordered_def)

lemma (in M_basic) wellordered_is_linear: 
    "[| wellordered(M,A,r); M(A) |] ==> linear(A,r)"
by (auto simp add: wellordered_def)

lemma (in M_basic) wellordered_is_wellfounded_on: 
    "[| wellordered(M,A,r); M(A) |] ==> wellfounded_on(M,A,r)"
by (auto simp add: wellordered_def)

lemma (in M_basic) wellfounded_imp_wellfounded_on: 
    "[| wellfounded(M,r); M(A) |] ==> wellfounded_on(M,A,r)"
by (auto simp add: wellfounded_def wellfounded_on_def)

lemma (in M_basic) wellfounded_on_subset_A:
     "[| wellfounded_on(M,A,r);  B<=A |] ==> wellfounded_on(M,B,r)"
by (simp add: wellfounded_on_def, blast)


subsubsection {*Well-founded relations*}

lemma  (in M_basic) wellfounded_on_iff_wellfounded:
     "wellfounded_on(M,A,r) \<longleftrightarrow> wellfounded(M, r \<inter> A*A)"
apply (simp add: wellfounded_on_def wellfounded_def, safe)
 apply force
apply (drule_tac x=x in rspec, assumption, blast) 
done

lemma (in M_basic) wellfounded_on_imp_wellfounded:
     "[|wellfounded_on(M,A,r); r \<subseteq> A*A|] ==> wellfounded(M,r)"
by (simp add: wellfounded_on_iff_wellfounded subset_Int_iff)

lemma (in M_basic) wellfounded_on_field_imp_wellfounded:
     "wellfounded_on(M, field(r), r) ==> wellfounded(M,r)"
by (simp add: wellfounded_def wellfounded_on_iff_wellfounded, fast)

lemma (in M_basic) wellfounded_iff_wellfounded_on_field:
     "M(r) ==> wellfounded(M,r) \<longleftrightarrow> wellfounded_on(M, field(r), r)"
by (blast intro: wellfounded_imp_wellfounded_on
                 wellfounded_on_field_imp_wellfounded)

(*Consider the least z in domain(r) such that P(z) does not hold...*)
lemma (in M_basic) wellfounded_induct: 
     "[| wellfounded(M,r); M(a); M(r); separation(M, \<lambda>x. ~P(x));  
         \<forall>x. M(x) & (\<forall>y. <y,x> \<in> r \<longrightarrow> P(y)) \<longrightarrow> P(x) |]
      ==> P(a)"
apply (simp (no_asm_use) add: wellfounded_def)
apply (drule_tac x="{z \<in> domain(r). ~P(z)}" in rspec)
apply (blast dest: transM)+
done

lemma (in M_basic) wellfounded_on_induct: 
     "[| a\<in>A;  wellfounded_on(M,A,r);  M(A);  
       separation(M, \<lambda>x. x\<in>A \<longrightarrow> ~P(x));  
       \<forall>x\<in>A. M(x) & (\<forall>y\<in>A. <y,x> \<in> r \<longrightarrow> P(y)) \<longrightarrow> P(x) |]
      ==> P(a)"
apply (simp (no_asm_use) add: wellfounded_on_def)
apply (drule_tac x="{z\<in>A. z\<in>A \<longrightarrow> ~P(z)}" in rspec)
apply (blast intro: transM)+
done


subsubsection {*Kunen's lemma IV 3.14, page 123*}

lemma (in M_basic) linear_imp_relativized: 
     "linear(A,r) ==> linear_rel(M,A,r)" 
by (simp add: linear_def linear_rel_def) 

lemma (in M_basic) trans_on_imp_relativized: 
     "trans[A](r) ==> transitive_rel(M,A,r)" 
by (unfold transitive_rel_def trans_on_def, blast) 

lemma (in M_basic) wf_on_imp_relativized: 
     "wf[A](r) ==> wellfounded_on(M,A,r)" 
apply (simp add: wellfounded_on_def wf_def wf_on_def, clarify) 
apply (drule_tac x=x in spec, blast) 
done

lemma (in M_basic) wf_imp_relativized: 
     "wf(r) ==> wellfounded(M,r)" 
apply (simp add: wellfounded_def wf_def, clarify) 
apply (drule_tac x=x in spec, blast) 
done

lemma (in M_basic) well_ord_imp_relativized: 
     "well_ord(A,r) ==> wellordered(M,A,r)" 
by (simp add: wellordered_def well_ord_def tot_ord_def part_ord_def
       linear_imp_relativized trans_on_imp_relativized wf_on_imp_relativized)

text{*The property being well founded (and hence of being well ordered) is not absolute: 
the set that doesn't contain a minimal element may not exist in the class M. 
However, every set that is well founded in a transitive model M is well founded (page 124).*}

subsection{* Relativized versions of order-isomorphisms and order types *}

lemma (in M_basic) order_isomorphism_abs [simp]: 
     "[| M(A); M(B); M(f) |] 
      ==> order_isomorphism(M,A,r,B,s,f) \<longleftrightarrow> f \<in> ord_iso(A,r,B,s)"
by (simp add: apply_closed order_isomorphism_def ord_iso_def)

lemma (in M_basic) pred_set_abs [simp]: 
     "[| M(r); M(B) |] ==> pred_set(M,A,x,r,B) \<longleftrightarrow> B = Order.pred(A,x,r)"
apply (simp add: pred_set_def Order.pred_def)
apply (blast dest: transM) 
done

lemma (in M_basic) pred_closed [intro,simp]: 
     "[| M(A); M(r); M(x) |] ==> M(Order.pred(A,x,r))"
apply (simp add: Order.pred_def) 
apply (insert pred_separation [of r x], simp) 
done

lemma (in M_basic) membership_abs [simp]: 
     "[| M(r); M(A) |] ==> membership(M,A,r) \<longleftrightarrow> r = Memrel(A)"
apply (simp add: membership_def Memrel_def, safe)
  apply (rule equalityI) 
   apply clarify 
   apply (frule transM, assumption)
   apply blast
  apply clarify 
  apply (subgoal_tac "M(<xb,ya>)", blast) 
  apply (blast dest: transM) 
 apply auto 
done

lemma (in M_basic) M_Memrel_iff:
     "M(A) ==> 
      Memrel(A) = {z \<in> A*A. \<exists>x[M]. \<exists>y[M]. z = \<langle>x,y\<rangle> & x \<in> y}"
apply (simp add: Memrel_def) 
apply (blast dest: transM)
done 

lemma (in M_basic) Memrel_closed [intro,simp]: 
     "M(A) ==> M(Memrel(A))"
apply (simp add: M_Memrel_iff) 
apply (insert Memrel_separation, simp)
done


subsection {* Main results of Kunen, Chapter 1 section 6 *}

text{*Subset properties-- proved outside the locale*}

lemma linear_rel_subset: 
    "[| linear_rel(M,A,r);  B<=A |] ==> linear_rel(M,B,r)"
by (unfold linear_rel_def, blast)

lemma transitive_rel_subset: 
    "[| transitive_rel(M,A,r);  B<=A |] ==> transitive_rel(M,B,r)"
by (unfold transitive_rel_def, blast)

lemma wellfounded_on_subset: 
    "[| wellfounded_on(M,A,r);  B<=A |] ==> wellfounded_on(M,B,r)"
by (unfold wellfounded_on_def subset_def, blast)

lemma wellordered_subset: 
    "[| wellordered(M,A,r);  B<=A |] ==> wellordered(M,B,r)"
apply (unfold wellordered_def)
apply (blast intro: linear_rel_subset transitive_rel_subset 
                    wellfounded_on_subset)
done

lemma (in M_basic) wellfounded_on_asym:
     "[| wellfounded_on(M,A,r);  <a,x>\<in>r;  a\<in>A; x\<in>A;  M(A) |] ==> <x,a>\<notin>r"
apply (simp add: wellfounded_on_def) 
apply (drule_tac x="{x,a}" in rspec) 
apply (blast dest: transM)+
done

lemma (in M_basic) wellordered_asym:
     "[| wellordered(M,A,r);  <a,x>\<in>r;  a\<in>A; x\<in>A;  M(A) |] ==> <x,a>\<notin>r"
by (simp add: wellordered_def, blast dest: wellfounded_on_asym)

end
