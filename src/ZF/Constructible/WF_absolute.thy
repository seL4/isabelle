(*  Title:      ZF/Constructible/WF_absolute.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   2002  University of Cambridge
*)

header {*Absoluteness for Well-Founded Relations and Well-Founded Recursion*}

theory WF_absolute = WFrec:

subsection{*Every well-founded relation is a subset of some inverse image of
      an ordinal*}

lemma wf_rvimage_Ord: "Ord(i) \<Longrightarrow> wf(rvimage(A, f, Memrel(i)))"
by (blast intro: wf_rvimage wf_Memrel)


constdefs
  wfrank :: "[i,i]=>i"
    "wfrank(r,a) == wfrec(r, a, %x f. \<Union>y \<in> r-``{x}. succ(f`y))"

constdefs
  wftype :: "i=>i"
    "wftype(r) == \<Union>y \<in> range(r). succ(wfrank(r,y))"

lemma wfrank: "wf(r) ==> wfrank(r,a) = (\<Union>y \<in> r-``{a}. succ(wfrank(r,y)))"
by (subst wfrank_def [THEN def_wfrec], simp_all)

lemma Ord_wfrank: "wf(r) ==> Ord(wfrank(r,a))"
apply (rule_tac a=a in wf_induct, assumption)
apply (subst wfrank, assumption)
apply (rule Ord_succ [THEN Ord_UN], blast)
done

lemma wfrank_lt: "[|wf(r); <a,b> \<in> r|] ==> wfrank(r,a) < wfrank(r,b)"
apply (rule_tac a1 = b in wfrank [THEN ssubst], assumption)
apply (rule UN_I [THEN ltI])
apply (simp add: Ord_wfrank vimage_iff)+
done

lemma Ord_wftype: "wf(r) ==> Ord(wftype(r))"
by (simp add: wftype_def Ord_wfrank)

lemma wftypeI: "\<lbrakk>wf(r);  x \<in> field(r)\<rbrakk> \<Longrightarrow> wfrank(r,x) \<in> wftype(r)"
apply (simp add: wftype_def)
apply (blast intro: wfrank_lt [THEN ltD])
done


lemma wf_imp_subset_rvimage:
     "[|wf(r); r \<subseteq> A*A|] ==> \<exists>i f. Ord(i) & r <= rvimage(A, f, Memrel(i))"
apply (rule_tac x="wftype(r)" in exI)
apply (rule_tac x="\<lambda>x\<in>A. wfrank(r,x)" in exI)
apply (simp add: Ord_wftype, clarify)
apply (frule subsetD, assumption, clarify)
apply (simp add: rvimage_iff wfrank_lt [THEN ltD])
apply (blast intro: wftypeI)
done

theorem wf_iff_subset_rvimage:
  "relation(r) ==> wf(r) <-> (\<exists>i f A. Ord(i) & r <= rvimage(A, f, Memrel(i)))"
by (blast dest!: relation_field_times_field wf_imp_subset_rvimage
          intro: wf_rvimage_Ord [THEN wf_subset])


subsection{*Transitive closure without fixedpoints*}

constdefs
  rtrancl_alt :: "[i,i]=>i"
    "rtrancl_alt(A,r) ==
       {p \<in> A*A. \<exists>n\<in>nat. \<exists>f \<in> succ(n) -> A.
                 (\<exists>x y. p = <x,y> &  f`0 = x & f`n = y) &
                       (\<forall>i\<in>n. <f`i, f`succ(i)> \<in> r)}"

lemma alt_rtrancl_lemma1 [rule_format]:
    "n \<in> nat
     ==> \<forall>f \<in> succ(n) -> field(r).
         (\<forall>i\<in>n. \<langle>f`i, f ` succ(i)\<rangle> \<in> r) --> \<langle>f`0, f`n\<rangle> \<in> r^*"
apply (induct_tac n)
apply (simp_all add: apply_funtype rtrancl_refl, clarify)
apply (rename_tac n f)
apply (rule rtrancl_into_rtrancl)
 prefer 2 apply assumption
apply (drule_tac x="restrict(f,succ(n))" in bspec)
 apply (blast intro: restrict_type2)
apply (simp add: Ord_succ_mem_iff nat_0_le [THEN ltD] leI [THEN ltD] ltI)
done

lemma rtrancl_alt_subset_rtrancl: "rtrancl_alt(field(r),r) <= r^*"
apply (simp add: rtrancl_alt_def)
apply (blast intro: alt_rtrancl_lemma1)
done

lemma rtrancl_subset_rtrancl_alt: "r^* <= rtrancl_alt(field(r),r)"
apply (simp add: rtrancl_alt_def, clarify)
apply (frule rtrancl_type [THEN subsetD], clarify, simp)
apply (erule rtrancl_induct)
 txt{*Base case, trivial*}
 apply (rule_tac x=0 in bexI)
  apply (rule_tac x="lam x:1. xa" in bexI)
   apply simp_all
txt{*Inductive step*}
apply clarify
apply (rename_tac n f)
apply (rule_tac x="succ(n)" in bexI)
 apply (rule_tac x="lam i:succ(succ(n)). if i=succ(n) then z else f`i" in bexI)
  apply (simp add: Ord_succ_mem_iff nat_0_le [THEN ltD] leI [THEN ltD] ltI)
  apply (blast intro: mem_asym)
 apply typecheck
 apply auto
done

lemma rtrancl_alt_eq_rtrancl: "rtrancl_alt(field(r),r) = r^*"
by (blast del: subsetI
	  intro: rtrancl_alt_subset_rtrancl rtrancl_subset_rtrancl_alt)


constdefs

  rtran_closure_mem :: "[i=>o,i,i,i] => o"
    --{*The property of belonging to @{text "rtran_closure(r)"}*}
    "rtran_closure_mem(M,A,r,p) ==
	      \<exists>nnat[M]. \<exists>n[M]. \<exists>n'[M]. 
               omega(M,nnat) & n\<in>nnat & successor(M,n,n') &
	       (\<exists>f[M]. typed_function(M,n',A,f) &
		(\<exists>x[M]. \<exists>y[M]. \<exists>zero[M]. pair(M,x,y,p) & empty(M,zero) &
		  fun_apply(M,f,zero,x) & fun_apply(M,f,n,y)) &
		  (\<forall>j[M]. j\<in>n --> 
		    (\<exists>fj[M]. \<exists>sj[M]. \<exists>fsj[M]. \<exists>ffp[M]. 
		      fun_apply(M,f,j,fj) & successor(M,j,sj) &
		      fun_apply(M,f,sj,fsj) & pair(M,fj,fsj,ffp) & ffp \<in> r)))"

  rtran_closure :: "[i=>o,i,i] => o"
    "rtran_closure(M,r,s) == 
        \<forall>A[M]. is_field(M,r,A) -->
 	 (\<forall>p[M]. p \<in> s <-> rtran_closure_mem(M,A,r,p))"

  tran_closure :: "[i=>o,i,i] => o"
    "tran_closure(M,r,t) ==
         \<exists>s[M]. rtran_closure(M,r,s) & composition(M,r,s,t)"

lemma (in M_axioms) rtran_closure_mem_iff:
     "[|M(A); M(r); M(p)|]
      ==> rtran_closure_mem(M,A,r,p) <->
          (\<exists>n[M]. n\<in>nat & 
           (\<exists>f[M]. f \<in> succ(n) -> A &
            (\<exists>x[M]. \<exists>y[M]. p = <x,y> & f`0 = x & f`n = y) &
                           (\<forall>i\<in>n. <f`i, f`succ(i)> \<in> r)))"
by (simp add: rtran_closure_mem_def Ord_succ_mem_iff nat_0_le [THEN ltD]) 


locale M_trancl = M_axioms +
  assumes rtrancl_separation:
	 "[| M(r); M(A) |] ==> separation (M, rtran_closure_mem(M,A,r))"
      and wellfounded_trancl_separation:
	 "[| M(r); M(Z) |] ==> 
	  separation (M, \<lambda>x. 
	      \<exists>w[M]. \<exists>wx[M]. \<exists>rp[M]. 
	       w \<in> Z & pair(M,w,x,wx) & tran_closure(M,r,rp) & wx \<in> rp)"


lemma (in M_trancl) rtran_closure_rtrancl:
     "M(r) ==> rtran_closure(M,r,rtrancl(r))"
apply (simp add: rtran_closure_def rtran_closure_mem_iff 
                 rtrancl_alt_eq_rtrancl [symmetric] rtrancl_alt_def)
apply (auto simp add: nat_0_le [THEN ltD] apply_funtype) 
done

lemma (in M_trancl) rtrancl_closed [intro,simp]:
     "M(r) ==> M(rtrancl(r))"
apply (insert rtrancl_separation [of r "field(r)"])
apply (simp add: rtrancl_alt_eq_rtrancl [symmetric]
                 rtrancl_alt_def rtran_closure_mem_iff)
done

lemma (in M_trancl) rtrancl_abs [simp]:
     "[| M(r); M(z) |] ==> rtran_closure(M,r,z) <-> z = rtrancl(r)"
apply (rule iffI)
 txt{*Proving the right-to-left implication*}
 prefer 2 apply (blast intro: rtran_closure_rtrancl)
apply (rule M_equalityI)
apply (simp add: rtran_closure_def rtrancl_alt_eq_rtrancl [symmetric]
                 rtrancl_alt_def rtran_closure_mem_iff)
apply (auto simp add: nat_0_le [THEN ltD] apply_funtype) 
done

lemma (in M_trancl) trancl_closed [intro,simp]:
     "M(r) ==> M(trancl(r))"
by (simp add: trancl_def comp_closed rtrancl_closed)

lemma (in M_trancl) trancl_abs [simp]:
     "[| M(r); M(z) |] ==> tran_closure(M,r,z) <-> z = trancl(r)"
by (simp add: tran_closure_def trancl_def)

lemma (in M_trancl) wellfounded_trancl_separation':
     "[| M(r); M(Z) |] ==> separation (M, \<lambda>x. \<exists>w[M]. w \<in> Z & <w,x> \<in> r^+)"
by (insert wellfounded_trancl_separation [of r Z], simp) 

text{*Alternative proof of @{text wf_on_trancl}; inspiration for the
      relativized version.  Original version is on theory WF.*}
lemma "[| wf[A](r);  r-``A <= A |] ==> wf[A](r^+)"
apply (simp add: wf_on_def wf_def)
apply (safe intro!: equalityI)
apply (drule_tac x = "{x\<in>A. \<exists>w. \<langle>w,x\<rangle> \<in> r^+ & w \<in> Z}" in spec)
apply (blast elim: tranclE)
done

lemma (in M_trancl) wellfounded_on_trancl:
     "[| wellfounded_on(M,A,r);  r-``A <= A; M(r); M(A) |]
      ==> wellfounded_on(M,A,r^+)"
apply (simp add: wellfounded_on_def)
apply (safe intro!: equalityI)
apply (rename_tac Z x)
apply (subgoal_tac "M({x\<in>A. \<exists>w[M]. w \<in> Z & \<langle>w,x\<rangle> \<in> r^+})")
 prefer 2
 apply (blast intro: wellfounded_trancl_separation') 
apply (drule_tac x = "{x\<in>A. \<exists>w[M]. w \<in> Z & \<langle>w,x\<rangle> \<in> r^+}" in rspec, safe)
apply (blast dest: transM, simp)
apply (rename_tac y w)
apply (drule_tac x=w in bspec, assumption, clarify)
apply (erule tranclE)
  apply (blast dest: transM)   (*transM is needed to prove M(xa)*)
 apply blast
done

lemma (in M_trancl) wellfounded_trancl:
     "[|wellfounded(M,r); M(r)|] ==> wellfounded(M,r^+)"
apply (rotate_tac -1)
apply (simp add: wellfounded_iff_wellfounded_on_field)
apply (rule wellfounded_on_subset_A, erule wellfounded_on_trancl)
   apply blast
  apply (simp_all add: trancl_type [THEN field_rel_subset])
done

text{*Relativized to M: Every well-founded relation is a subset of some
inverse image of an ordinal.  Key step is the construction (in M) of a
rank function.*}


locale M_wfrank = M_trancl +
  assumes wfrank_separation:
     "M(r) ==>
      separation (M, \<lambda>x. 
         \<forall>rplus[M]. tran_closure(M,r,rplus) -->
         ~ (\<exists>f[M]. M_is_recfun(M, %x f y. is_range(M,f,y), rplus, x, f)))"
 and wfrank_strong_replacement:
     "M(r) ==>
      strong_replacement(M, \<lambda>x z. 
         \<forall>rplus[M]. tran_closure(M,r,rplus) -->
         (\<exists>y[M]. \<exists>f[M]. pair(M,x,y,z)  & 
                        M_is_recfun(M, %x f y. is_range(M,f,y), rplus, x, f) &
                        is_range(M,f,y)))"
 and Ord_wfrank_separation:
     "M(r) ==>
      separation (M, \<lambda>x.
         \<forall>rplus[M]. tran_closure(M,r,rplus) --> 
          ~ (\<forall>f[M]. \<forall>rangef[M]. 
             is_range(M,f,rangef) -->
             M_is_recfun(M, \<lambda>x f y. is_range(M,f,y), rplus, x, f) -->
             ordinal(M,rangef)))" 

text{*Proving that the relativized instances of Separation or Replacement
agree with the "real" ones.*}

lemma (in M_wfrank) wfrank_separation':
     "M(r) ==>
      separation
	   (M, \<lambda>x. ~ (\<exists>f[M]. is_recfun(r^+, x, %x f. range(f), f)))"
apply (insert wfrank_separation [of r])
apply (simp add: relativize2_def is_recfun_abs [of "%x. range"])
done

lemma (in M_wfrank) wfrank_strong_replacement':
     "M(r) ==>
      strong_replacement(M, \<lambda>x z. \<exists>y[M]. \<exists>f[M]. 
		  pair(M,x,y,z) & is_recfun(r^+, x, %x f. range(f), f) &
		  y = range(f))"
apply (insert wfrank_strong_replacement [of r])
apply (simp add: relativize2_def is_recfun_abs [of "%x. range"])
done

lemma (in M_wfrank) Ord_wfrank_separation':
     "M(r) ==>
      separation (M, \<lambda>x. 
         ~ (\<forall>f[M]. is_recfun(r^+, x, \<lambda>x. range, f) --> Ord(range(f))))" 
apply (insert Ord_wfrank_separation [of r])
apply (simp add: relativize2_def is_recfun_abs [of "%x. range"])
done

text{*This function, defined using replacement, is a rank function for
well-founded relations within the class M.*}
constdefs
 wellfoundedrank :: "[i=>o,i,i] => i"
    "wellfoundedrank(M,r,A) ==
        {p. x\<in>A, \<exists>y[M]. \<exists>f[M]. 
                       p = <x,y> & is_recfun(r^+, x, %x f. range(f), f) &
                       y = range(f)}"

lemma (in M_wfrank) exists_wfrank:
    "[| wellfounded(M,r); M(a); M(r) |]
     ==> \<exists>f[M]. is_recfun(r^+, a, %x f. range(f), f)"
apply (rule wellfounded_exists_is_recfun)
      apply (blast intro: wellfounded_trancl)
     apply (rule trans_trancl)
    apply (erule wfrank_separation')
   apply (erule wfrank_strong_replacement')
apply (simp_all add: trancl_subset_times)
done

lemma (in M_wfrank) M_wellfoundedrank:
    "[| wellfounded(M,r); M(r); M(A) |] ==> M(wellfoundedrank(M,r,A))"
apply (insert wfrank_strong_replacement' [of r])
apply (simp add: wellfoundedrank_def)
apply (rule strong_replacement_closed)
   apply assumption+
 apply (rule univalent_is_recfun)
   apply (blast intro: wellfounded_trancl)
  apply (rule trans_trancl)
 apply (simp add: trancl_subset_times) 
apply (blast dest: transM) 
done

lemma (in M_wfrank) Ord_wfrank_range [rule_format]:
    "[| wellfounded(M,r); a\<in>A; M(r); M(A) |]
     ==> \<forall>f[M]. is_recfun(r^+, a, %x f. range(f), f) --> Ord(range(f))"
apply (drule wellfounded_trancl, assumption)
apply (rule wellfounded_induct, assumption, erule (1) transM)
  apply simp
 apply (blast intro: Ord_wfrank_separation', clarify)
txt{*The reasoning in both cases is that we get @{term y} such that
   @{term "\<langle>y, x\<rangle> \<in> r^+"}.  We find that
   @{term "f`y = restrict(f, r^+ -`` {y})"}. *}
apply (rule OrdI [OF _ Ord_is_Transset])
 txt{*An ordinal is a transitive set...*}
 apply (simp add: Transset_def)
 apply clarify
 apply (frule apply_recfun2, assumption)
 apply (force simp add: restrict_iff)
txt{*...of ordinals.  This second case requires the induction hyp.*}
apply clarify
apply (rename_tac i y)
apply (frule apply_recfun2, assumption)
apply (frule is_recfun_imp_in_r, assumption)
apply (frule is_recfun_restrict)
    (*simp_all won't work*)
    apply (simp add: trans_trancl trancl_subset_times)+
apply (drule spec [THEN mp], assumption)
apply (subgoal_tac "M(restrict(f, r^+ -`` {y}))")
 apply (drule_tac x="restrict(f, r^+ -`` {y})" in rspec)
apply assumption
 apply (simp add: function_apply_equality [OF _ is_recfun_imp_function])
apply (blast dest: pair_components_in_M)
done

lemma (in M_wfrank) Ord_range_wellfoundedrank:
    "[| wellfounded(M,r); r \<subseteq> A*A;  M(r); M(A) |]
     ==> Ord (range(wellfoundedrank(M,r,A)))"
apply (frule wellfounded_trancl, assumption)
apply (frule trancl_subset_times)
apply (simp add: wellfoundedrank_def)
apply (rule OrdI [OF _ Ord_is_Transset])
 prefer 2
 txt{*by our previous result the range consists of ordinals.*}
 apply (blast intro: Ord_wfrank_range)
txt{*We still must show that the range is a transitive set.*}
apply (simp add: Transset_def, clarify, simp)
apply (rename_tac x i f u)
apply (frule is_recfun_imp_in_r, assumption)
apply (subgoal_tac "M(u) & M(i) & M(x)")
 prefer 2 apply (blast dest: transM, clarify)
apply (rule_tac a=u in rangeI)
apply (rule_tac x=u in ReplaceI)
  apply simp 
  apply (rule_tac x="restrict(f, r^+ -`` {u})" in rexI)
   apply (blast intro: is_recfun_restrict trans_trancl dest: apply_recfun2)
  apply simp 
apply blast 
txt{*Unicity requirement of Replacement*}
apply clarify
apply (frule apply_recfun2, assumption)
apply (simp add: trans_trancl is_recfun_cut)
done

lemma (in M_wfrank) function_wellfoundedrank:
    "[| wellfounded(M,r); M(r); M(A)|]
     ==> function(wellfoundedrank(M,r,A))"
apply (simp add: wellfoundedrank_def function_def, clarify)
txt{*Uniqueness: repeated below!*}
apply (drule is_recfun_functional, assumption)
     apply (blast intro: wellfounded_trancl)
    apply (simp_all add: trancl_subset_times trans_trancl)
done

lemma (in M_wfrank) domain_wellfoundedrank:
    "[| wellfounded(M,r); M(r); M(A)|]
     ==> domain(wellfoundedrank(M,r,A)) = A"
apply (simp add: wellfoundedrank_def function_def)
apply (rule equalityI, auto)
apply (frule transM, assumption)
apply (frule_tac a=x in exists_wfrank, assumption+, clarify)
apply (rule_tac b="range(f)" in domainI)
apply (rule_tac x=x in ReplaceI)
  apply simp 
  apply (rule_tac x=f in rexI, blast, simp_all)
txt{*Uniqueness (for Replacement): repeated above!*}
apply clarify
apply (drule is_recfun_functional, assumption)
    apply (blast intro: wellfounded_trancl)
    apply (simp_all add: trancl_subset_times trans_trancl)
done

lemma (in M_wfrank) wellfoundedrank_type:
    "[| wellfounded(M,r);  M(r); M(A)|]
     ==> wellfoundedrank(M,r,A) \<in> A -> range(wellfoundedrank(M,r,A))"
apply (frule function_wellfoundedrank [of r A], assumption+)
apply (frule function_imp_Pi)
 apply (simp add: wellfoundedrank_def relation_def)
 apply blast
apply (simp add: domain_wellfoundedrank)
done

lemma (in M_wfrank) Ord_wellfoundedrank:
    "[| wellfounded(M,r); a \<in> A; r \<subseteq> A*A;  M(r); M(A) |]
     ==> Ord(wellfoundedrank(M,r,A) ` a)"
by (blast intro: apply_funtype [OF wellfoundedrank_type]
                 Ord_in_Ord [OF Ord_range_wellfoundedrank])

lemma (in M_wfrank) wellfoundedrank_eq:
     "[| is_recfun(r^+, a, %x. range, f);
         wellfounded(M,r);  a \<in> A; M(f); M(r); M(A)|]
      ==> wellfoundedrank(M,r,A) ` a = range(f)"
apply (rule apply_equality)
 prefer 2 apply (blast intro: wellfoundedrank_type)
apply (simp add: wellfoundedrank_def)
apply (rule ReplaceI)
  apply (rule_tac x="range(f)" in rexI) 
  apply blast
 apply simp_all
txt{*Unicity requirement of Replacement*}
apply clarify
apply (drule is_recfun_functional, assumption)
    apply (blast intro: wellfounded_trancl)
    apply (simp_all add: trancl_subset_times trans_trancl)
done


lemma (in M_wfrank) wellfoundedrank_lt:
     "[| <a,b> \<in> r;
         wellfounded(M,r); r \<subseteq> A*A;  M(r); M(A)|]
      ==> wellfoundedrank(M,r,A) ` a < wellfoundedrank(M,r,A) ` b"
apply (frule wellfounded_trancl, assumption)
apply (subgoal_tac "a\<in>A & b\<in>A")
 prefer 2 apply blast
apply (simp add: lt_def Ord_wellfoundedrank, clarify)
apply (frule exists_wfrank [of concl: _ b], erule (1) transM, assumption)
apply clarify
apply (rename_tac fb)
apply (frule is_recfun_restrict [of concl: "r^+" a])
    apply (rule trans_trancl, assumption)
   apply (simp_all add: r_into_trancl trancl_subset_times)
txt{*Still the same goal, but with new @{text is_recfun} assumptions.*}
apply (simp add: wellfoundedrank_eq)
apply (frule_tac a=a in wellfoundedrank_eq, assumption+)
   apply (simp_all add: transM [of a])
txt{*We have used equations for wellfoundedrank and now must use some
    for  @{text is_recfun}. *}
apply (rule_tac a=a in rangeI)
apply (simp add: is_recfun_type [THEN apply_iff] vimage_singleton_iff
                 r_into_trancl apply_recfun r_into_trancl)
done


lemma (in M_wfrank) wellfounded_imp_subset_rvimage:
     "[|wellfounded(M,r); r \<subseteq> A*A; M(r); M(A)|]
      ==> \<exists>i f. Ord(i) & r <= rvimage(A, f, Memrel(i))"
apply (rule_tac x="range(wellfoundedrank(M,r,A))" in exI)
apply (rule_tac x="wellfoundedrank(M,r,A)" in exI)
apply (simp add: Ord_range_wellfoundedrank, clarify)
apply (frule subsetD, assumption, clarify)
apply (simp add: rvimage_iff wellfoundedrank_lt [THEN ltD])
apply (blast intro: apply_rangeI wellfoundedrank_type)
done

lemma (in M_wfrank) wellfounded_imp_wf:
     "[|wellfounded(M,r); relation(r); M(r)|] ==> wf(r)"
by (blast dest!: relation_field_times_field wellfounded_imp_subset_rvimage
          intro: wf_rvimage_Ord [THEN wf_subset])

lemma (in M_wfrank) wellfounded_on_imp_wf_on:
     "[|wellfounded_on(M,A,r); relation(r); M(r); M(A)|] ==> wf[A](r)"
apply (simp add: wellfounded_on_iff_wellfounded wf_on_def)
apply (rule wellfounded_imp_wf)
apply (simp_all add: relation_def)
done


theorem (in M_wfrank) wf_abs [simp]:
     "[|relation(r); M(r)|] ==> wellfounded(M,r) <-> wf(r)"
by (blast intro: wellfounded_imp_wf wf_imp_relativized)

theorem (in M_wfrank) wf_on_abs [simp]:
     "[|relation(r); M(r); M(A)|] ==> wellfounded_on(M,A,r) <-> wf[A](r)"
by (blast intro: wellfounded_on_imp_wf_on wf_on_imp_relativized)


text{*absoluteness for wfrec-defined functions.*}

(*first use is_recfun, then M_is_recfun*)

lemma (in M_trancl) wfrec_relativize:
  "[|wf(r); M(a); M(r);  
     strong_replacement(M, \<lambda>x z. \<exists>y[M]. \<exists>g[M].
          pair(M,x,y,z) & 
          is_recfun(r^+, x, \<lambda>x f. H(x, restrict(f, r -`` {x})), g) & 
          y = H(x, restrict(g, r -`` {x}))); 
     \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g))|] 
   ==> wfrec(r,a,H) = z <-> 
       (\<exists>f[M]. is_recfun(r^+, a, \<lambda>x f. H(x, restrict(f, r -`` {x})), f) & 
            z = H(a,restrict(f,r-``{a})))"
apply (frule wf_trancl) 
apply (simp add: wftrec_def wfrec_def, safe)
 apply (frule wf_exists_is_recfun 
              [of concl: "r^+" a "\<lambda>x f. H(x, restrict(f, r -`` {x}))"]) 
      apply (simp_all add: trans_trancl function_restrictI trancl_subset_times)
 apply (clarify, rule_tac x=x in rexI) 
 apply (simp_all add: the_recfun_eq trans_trancl trancl_subset_times)
done


text{*Assuming @{term r} is transitive simplifies the occurrences of @{text H}.
      The premise @{term "relation(r)"} is necessary 
      before we can replace @{term "r^+"} by @{term r}. *}
theorem (in M_trancl) trans_wfrec_relativize:
  "[|wf(r);  trans(r);  relation(r);  M(r);  M(a);
     wfrec_replacement(M,MH,r);  relativize2(M,MH,H);
     \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g))|] 
   ==> wfrec(r,a,H) = z <-> (\<exists>f[M]. is_recfun(r,a,H,f) & z = H(a,f))" 
apply (frule wfrec_replacement', assumption+) 
apply (simp cong: is_recfun_cong
           add: wfrec_relativize trancl_eq_r
                is_recfun_restrict_idem domain_restrict_idem)
done

theorem (in M_trancl) trans_wfrec_abs:
  "[|wf(r);  trans(r);  relation(r);  M(r);  M(a);  M(z);
     wfrec_replacement(M,MH,r);  relativize2(M,MH,H);
     \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g))|] 
   ==> is_wfrec(M,MH,r,a,z) <-> z=wfrec(r,a,H)" 
apply (simp add: trans_wfrec_relativize [THEN iff_sym] is_wfrec_abs, blast) 
done

lemma (in M_trancl) trans_eq_pair_wfrec_iff:
  "[|wf(r);  trans(r); relation(r); M(r);  M(y); 
     wfrec_replacement(M,MH,r);  relativize2(M,MH,H);
     \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g))|] 
   ==> y = <x, wfrec(r, x, H)> <-> 
       (\<exists>f[M]. is_recfun(r,x,H,f) & y = <x, H(x,f)>)"
apply safe 
 apply (simp add: trans_wfrec_relativize [THEN iff_sym, of concl: _ x]) 
txt{*converse direction*}
apply (rule sym)
apply (simp add: trans_wfrec_relativize, blast) 
done


subsection{*M is closed under well-founded recursion*}

text{*Lemma with the awkward premise mentioning @{text wfrec}.*}
lemma (in M_wfrank) wfrec_closed_lemma [rule_format]:
     "[|wf(r); M(r); 
        strong_replacement(M, \<lambda>x y. y = \<langle>x, wfrec(r, x, H)\<rangle>);
        \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g)) |] 
      ==> M(a) --> M(wfrec(r,a,H))"
apply (rule_tac a=a in wf_induct, assumption+)
apply (subst wfrec, assumption, clarify)
apply (drule_tac x1=x and x="\<lambda>x\<in>r -`` {x}. wfrec(r, x, H)" 
       in rspec [THEN rspec]) 
apply (simp_all add: function_lam) 
apply (blast intro: lam_closed dest: pair_components_in_M) 
done

text{*Eliminates one instance of replacement.*}
lemma (in M_wfrank) wfrec_replacement_iff:
     "strong_replacement(M, \<lambda>x z. 
          \<exists>y[M]. pair(M,x,y,z) & (\<exists>g[M]. is_recfun(r,x,H,g) & y = H(x,g))) <->
      strong_replacement(M, 
           \<lambda>x y. \<exists>f[M]. is_recfun(r,x,H,f) & y = <x, H(x,f)>)"
apply simp 
apply (rule strong_replacement_cong, blast) 
done

text{*Useful version for transitive relations*}
theorem (in M_wfrank) trans_wfrec_closed:
     "[|wf(r); trans(r); relation(r); M(r); M(a);
       wfrec_replacement(M,MH,r);  relativize2(M,MH,H);
        \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g)) |] 
      ==> M(wfrec(r,a,H))"
apply (frule wfrec_replacement', assumption+) 
apply (frule wfrec_replacement_iff [THEN iffD1]) 
apply (rule wfrec_closed_lemma, assumption+) 
apply (simp_all add: wfrec_replacement_iff trans_eq_pair_wfrec_iff) 
done

subsection{*Absoluteness without assuming transitivity*}
lemma (in M_trancl) eq_pair_wfrec_iff:
  "[|wf(r);  M(r);  M(y); 
     strong_replacement(M, \<lambda>x z. \<exists>y[M]. \<exists>g[M].
          pair(M,x,y,z) & 
          is_recfun(r^+, x, \<lambda>x f. H(x, restrict(f, r -`` {x})), g) & 
          y = H(x, restrict(g, r -`` {x}))); 
     \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g))|] 
   ==> y = <x, wfrec(r, x, H)> <-> 
       (\<exists>f[M]. is_recfun(r^+, x, \<lambda>x f. H(x, restrict(f, r -`` {x})), f) & 
            y = <x, H(x,restrict(f,r-``{x}))>)"
apply safe  
 apply (simp add: wfrec_relativize [THEN iff_sym, of concl: _ x]) 
txt{*converse direction*}
apply (rule sym)
apply (simp add: wfrec_relativize, blast) 
done

text{*Full version not assuming transitivity, but maybe not very useful.*}
theorem (in M_wfrank) wfrec_closed:
     "[|wf(r); M(r); M(a);
        wfrec_replacement(M,MH,r^+);  
        relativize2(M,MH, \<lambda>x f. H(x, restrict(f, r -`` {x})));
        \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g)) |] 
      ==> M(wfrec(r,a,H))"
apply (frule wfrec_replacement' 
               [of MH "r^+" "\<lambda>x f. H(x, restrict(f, r -`` {x}))"])
   prefer 4
   apply (frule wfrec_replacement_iff [THEN iffD1]) 
   apply (rule wfrec_closed_lemma, assumption+) 
     apply (simp_all add: eq_pair_wfrec_iff func.function_restrictI) 
done

end
