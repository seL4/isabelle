(*  Title:      ZF/Constructible/WF_absolute.thy
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

section \<open>Absoluteness of Well-Founded Recursion\<close>

theory WF_absolute imports WFrec begin

subsection\<open>Transitive closure without fixedpoints\<close>

definition
  rtrancl_alt :: "[i,i]\<Rightarrow>i" where
    "rtrancl_alt(A,r) \<equiv>
       {p \<in> A*A. \<exists>n\<in>nat. \<exists>f \<in> succ(n) -> A.
                 (\<exists>x y. p = \<langle>x,y\<rangle> \<and>  f`0 = x \<and> f`n = y) \<and>
                       (\<forall>i\<in>n. <f`i, f`succ(i)> \<in> r)}"

lemma alt_rtrancl_lemma1 [rule_format]:
    "n \<in> nat
     \<Longrightarrow> \<forall>f \<in> succ(n) -> field(r).
         (\<forall>i\<in>n. \<langle>f`i, f ` succ(i)\<rangle> \<in> r) \<longrightarrow> \<langle>f`0, f`n\<rangle> \<in> r^*"
apply (induct_tac n)
apply (simp_all add: apply_funtype rtrancl_refl, clarify)
apply (rename_tac n f)
apply (rule rtrancl_into_rtrancl)
 prefer 2 apply assumption
apply (drule_tac x="restrict(f,succ(n))" in bspec)
 apply (blast intro: restrict_type2)
apply (simp add: Ord_succ_mem_iff nat_0_le [THEN ltD] leI [THEN ltD] ltI)
done

lemma rtrancl_alt_subset_rtrancl: "rtrancl_alt(field(r),r) \<subseteq> r^*"
apply (simp add: rtrancl_alt_def)
apply (blast intro: alt_rtrancl_lemma1)
done

lemma rtrancl_subset_rtrancl_alt: "r^* \<subseteq> rtrancl_alt(field(r),r)"
apply (simp add: rtrancl_alt_def, clarify)
apply (frule rtrancl_type [THEN subsetD], clarify, simp)
apply (erule rtrancl_induct)
 txt\<open>Base case, trivial\<close>
 apply (rule_tac x=0 in bexI)
  apply (rule_tac x="\<lambda>x\<in>1. xa" in bexI)
   apply simp_all
txt\<open>Inductive step\<close>
apply clarify
apply (rename_tac n f)
apply (rule_tac x="succ(n)" in bexI)
 apply (rule_tac x="\<lambda>i\<in>succ(succ(n)). if i=succ(n) then z else f`i" in bexI)
  apply (simp add: Ord_succ_mem_iff nat_0_le [THEN ltD] leI [THEN ltD] ltI)
  apply (blast intro: mem_asym)
 apply typecheck
 apply auto
done

lemma rtrancl_alt_eq_rtrancl: "rtrancl_alt(field(r),r) = r^*"
by (blast del: subsetI
          intro: rtrancl_alt_subset_rtrancl rtrancl_subset_rtrancl_alt)


definition
  rtran_closure_mem :: "[i\<Rightarrow>o,i,i,i] \<Rightarrow> o" where
    \<comment> \<open>The property of belonging to \<open>rtran_closure(r)\<close>\<close>
    "rtran_closure_mem(M,A,r,p) \<equiv>
              \<exists>nnat[M]. \<exists>n[M]. \<exists>n'[M]. 
               omega(M,nnat) \<and> n\<in>nnat \<and> successor(M,n,n') \<and>
               (\<exists>f[M]. typed_function(M,n',A,f) \<and>
                (\<exists>x[M]. \<exists>y[M]. \<exists>zero[M]. pair(M,x,y,p) \<and> empty(M,zero) \<and>
                  fun_apply(M,f,zero,x) \<and> fun_apply(M,f,n,y)) \<and>
                  (\<forall>j[M]. j\<in>n \<longrightarrow> 
                    (\<exists>fj[M]. \<exists>sj[M]. \<exists>fsj[M]. \<exists>ffp[M]. 
                      fun_apply(M,f,j,fj) \<and> successor(M,j,sj) \<and>
                      fun_apply(M,f,sj,fsj) \<and> pair(M,fj,fsj,ffp) \<and> ffp \<in> r)))"

definition
  rtran_closure :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "rtran_closure(M,r,s) \<equiv> 
        \<forall>A[M]. is_field(M,r,A) \<longrightarrow>
         (\<forall>p[M]. p \<in> s \<longleftrightarrow> rtran_closure_mem(M,A,r,p))"

definition
  tran_closure :: "[i\<Rightarrow>o,i,i] \<Rightarrow> o" where
    "tran_closure(M,r,t) \<equiv>
         \<exists>s[M]. rtran_closure(M,r,s) \<and> composition(M,r,s,t)"
    
locale M_trancl = M_basic +
  assumes rtrancl_separation:
         "\<lbrakk>M(r); M(A)\<rbrakk> \<Longrightarrow> separation (M, rtran_closure_mem(M,A,r))"
      and wellfounded_trancl_separation:
         "\<lbrakk>M(r); M(Z)\<rbrakk> \<Longrightarrow> 
          separation (M, \<lambda>x. 
              \<exists>w[M]. \<exists>wx[M]. \<exists>rp[M]. 
               w \<in> Z \<and> pair(M,w,x,wx) \<and> tran_closure(M,r,rp) \<and> wx \<in> rp)"
      and M_nat [iff] : "M(nat)"

lemma (in M_trancl) rtran_closure_mem_iff:
     "\<lbrakk>M(A); M(r); M(p)\<rbrakk>
      \<Longrightarrow> rtran_closure_mem(M,A,r,p) \<longleftrightarrow>
          (\<exists>n[M]. n\<in>nat \<and> 
           (\<exists>f[M]. f \<in> succ(n) -> A \<and>
            (\<exists>x[M]. \<exists>y[M]. p = \<langle>x,y\<rangle> \<and> f`0 = x \<and> f`n = y) \<and>
                           (\<forall>i\<in>n. <f`i, f`succ(i)> \<in> r)))"
  apply (simp add: rtran_closure_mem_def Ord_succ_mem_iff nat_0_le [THEN ltD]) 
done

lemma (in M_trancl) rtran_closure_rtrancl:
     "M(r) \<Longrightarrow> rtran_closure(M,r,rtrancl(r))"
apply (simp add: rtran_closure_def rtran_closure_mem_iff 
                 rtrancl_alt_eq_rtrancl [symmetric] rtrancl_alt_def)
apply (auto simp add: nat_0_le [THEN ltD] apply_funtype) 
done

lemma (in M_trancl) rtrancl_closed [intro,simp]:
     "M(r) \<Longrightarrow> M(rtrancl(r))"
apply (insert rtrancl_separation [of r "field(r)"])
apply (simp add: rtrancl_alt_eq_rtrancl [symmetric]
                 rtrancl_alt_def rtran_closure_mem_iff)
done

lemma (in M_trancl) rtrancl_abs [simp]:
     "\<lbrakk>M(r); M(z)\<rbrakk> \<Longrightarrow> rtran_closure(M,r,z) \<longleftrightarrow> z = rtrancl(r)"
apply (rule iffI)
 txt\<open>Proving the right-to-left implication\<close>
 prefer 2 apply (blast intro: rtran_closure_rtrancl)
apply (rule M_equalityI)
apply (simp add: rtran_closure_def rtrancl_alt_eq_rtrancl [symmetric]
                 rtrancl_alt_def rtran_closure_mem_iff)
apply (auto simp add: nat_0_le [THEN ltD] apply_funtype) 
done

lemma (in M_trancl) trancl_closed [intro,simp]:
     "M(r) \<Longrightarrow> M(trancl(r))"
by (simp add: trancl_def)

lemma (in M_trancl) trancl_abs [simp]:
     "\<lbrakk>M(r); M(z)\<rbrakk> \<Longrightarrow> tran_closure(M,r,z) \<longleftrightarrow> z = trancl(r)"
by (simp add: tran_closure_def trancl_def)

lemma (in M_trancl) wellfounded_trancl_separation':
     "\<lbrakk>M(r); M(Z)\<rbrakk> \<Longrightarrow> separation (M, \<lambda>x. \<exists>w[M]. w \<in> Z \<and> \<langle>w,x\<rangle> \<in> r^+)"
by (insert wellfounded_trancl_separation [of r Z], simp) 

text\<open>Alternative proof of \<open>wf_on_trancl\<close>; inspiration for the
      relativized version.  Original version is on theory WF.\<close>
lemma "\<lbrakk>wf[A](r);  r-``A \<subseteq> A\<rbrakk> \<Longrightarrow> wf[A](r^+)"
apply (simp add: wf_on_def wf_def)
apply (safe)
apply (drule_tac x = "{x\<in>A. \<exists>w. \<langle>w,x\<rangle> \<in> r^+ \<and> w \<in> Z}" in spec)
apply (blast elim: tranclE)
done

lemma (in M_trancl) wellfounded_on_trancl:
     "\<lbrakk>wellfounded_on(M,A,r);  r-``A \<subseteq> A; M(r); M(A)\<rbrakk>
      \<Longrightarrow> wellfounded_on(M,A,r^+)"
apply (simp add: wellfounded_on_def)
apply (safe intro!: equalityI)
apply (rename_tac Z x)
apply (subgoal_tac "M({x\<in>A. \<exists>w[M]. w \<in> Z \<and> \<langle>w,x\<rangle> \<in> r^+})")
 prefer 2
 apply (blast intro: wellfounded_trancl_separation') 
apply (drule_tac x = "{x\<in>A. \<exists>w[M]. w \<in> Z \<and> \<langle>w,x\<rangle> \<in> r^+}" in rspec, safe)
apply (blast dest: transM, simp)
apply (rename_tac y w)
apply (drule_tac x=w in bspec, assumption, clarify)
apply (erule tranclE)
  apply (blast dest: transM)   (*transM is needed to prove M(xa)*)
 apply blast
done

lemma (in M_trancl) wellfounded_trancl:
     "\<lbrakk>wellfounded(M,r); M(r)\<rbrakk> \<Longrightarrow> wellfounded(M,r^+)"
apply (simp add: wellfounded_iff_wellfounded_on_field)
apply (rule wellfounded_on_subset_A, erule wellfounded_on_trancl)
   apply blast
  apply (simp_all add: trancl_type [THEN field_rel_subset])
done


text\<open>Absoluteness for wfrec-defined functions.\<close>

(*first use is_recfun, then M_is_recfun*)

lemma (in M_trancl) wfrec_relativize:
  "\<lbrakk>wf(r); M(a); M(r);  
     strong_replacement(M, \<lambda>x z. \<exists>y[M]. \<exists>g[M].
          pair(M,x,y,z) \<and> 
          is_recfun(r^+, x, \<lambda>x f. H(x, restrict(f, r -`` {x})), g) \<and> 
          y = H(x, restrict(g, r -`` {x}))); 
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk> 
   \<Longrightarrow> wfrec(r,a,H) = z \<longleftrightarrow> 
       (\<exists>f[M]. is_recfun(r^+, a, \<lambda>x f. H(x, restrict(f, r -`` {x})), f) \<and> 
            z = H(a,restrict(f,r-``{a})))"
apply (frule wf_trancl) 
apply (simp add: wftrec_def wfrec_def, safe)
 apply (frule wf_exists_is_recfun 
              [of concl: "r^+" a "\<lambda>x f. H(x, restrict(f, r -`` {x}))"]) 
      apply (simp_all add: trans_trancl function_restrictI trancl_subset_times)
 apply (clarify, rule_tac x=x in rexI) 
 apply (simp_all add: the_recfun_eq trans_trancl trancl_subset_times)
done


text\<open>Assuming \<^term>\<open>r\<close> is transitive simplifies the occurrences of \<open>H\<close>.
      The premise \<^term>\<open>relation(r)\<close> is necessary 
      before we can replace \<^term>\<open>r^+\<close> by \<^term>\<open>r\<close>.\<close>
theorem (in M_trancl) trans_wfrec_relativize:
  "\<lbrakk>wf(r);  trans(r);  relation(r);  M(r);  M(a);
     wfrec_replacement(M,MH,r);  relation2(M,MH,H);
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk> 
   \<Longrightarrow> wfrec(r,a,H) = z \<longleftrightarrow> (\<exists>f[M]. is_recfun(r,a,H,f) \<and> z = H(a,f))" 
apply (frule wfrec_replacement', assumption+) 
apply (simp cong: is_recfun_cong
           add: wfrec_relativize trancl_eq_r
                is_recfun_restrict_idem domain_restrict_idem)
done

theorem (in M_trancl) trans_wfrec_abs:
  "\<lbrakk>wf(r);  trans(r);  relation(r);  M(r);  M(a);  M(z);
     wfrec_replacement(M,MH,r);  relation2(M,MH,H);
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk> 
   \<Longrightarrow> is_wfrec(M,MH,r,a,z) \<longleftrightarrow> z=wfrec(r,a,H)" 
by (simp add: trans_wfrec_relativize [THEN iff_sym] is_wfrec_abs, blast) 


lemma (in M_trancl) trans_eq_pair_wfrec_iff:
  "\<lbrakk>wf(r);  trans(r); relation(r); M(r);  M(y); 
     wfrec_replacement(M,MH,r);  relation2(M,MH,H);
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk> 
   \<Longrightarrow> y = <x, wfrec(r, x, H)> \<longleftrightarrow> 
       (\<exists>f[M]. is_recfun(r,x,H,f) \<and> y = <x, H(x,f)>)"
apply safe 
 apply (simp add: trans_wfrec_relativize [THEN iff_sym, of concl: _ x]) 
txt\<open>converse direction\<close>
apply (rule sym)
apply (simp add: trans_wfrec_relativize, blast) 
done


subsection\<open>M is closed under well-founded recursion\<close>

text\<open>Lemma with the awkward premise mentioning \<open>wfrec\<close>.\<close>
lemma (in M_trancl) wfrec_closed_lemma [rule_format]:
     "\<lbrakk>wf(r); M(r); 
        strong_replacement(M, \<lambda>x y. y = \<langle>x, wfrec(r, x, H)\<rangle>);
        \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk> 
      \<Longrightarrow> M(a) \<longrightarrow> M(wfrec(r,a,H))"
apply (rule_tac a=a in wf_induct, assumption+)
apply (subst wfrec, assumption, clarify)
apply (drule_tac x1=x and x="\<lambda>x\<in>r -`` {x}. wfrec(r, x, H)" 
       in rspec [THEN rspec]) 
apply (simp_all add: function_lam) 
apply (blast intro: lam_closed dest: pair_components_in_M) 
done

text\<open>Eliminates one instance of replacement.\<close>
lemma (in M_trancl) wfrec_replacement_iff:
     "strong_replacement(M, \<lambda>x z. 
          \<exists>y[M]. pair(M,x,y,z) \<and> (\<exists>g[M]. is_recfun(r,x,H,g) \<and> y = H(x,g))) \<longleftrightarrow>
      strong_replacement(M, 
           \<lambda>x y. \<exists>f[M]. is_recfun(r,x,H,f) \<and> y = <x, H(x,f)>)"
apply simp 
apply (rule strong_replacement_cong, blast) 
done

text\<open>Useful version for transitive relations\<close>
theorem (in M_trancl) trans_wfrec_closed:
     "\<lbrakk>wf(r); trans(r); relation(r); M(r); M(a);
       wfrec_replacement(M,MH,r);  relation2(M,MH,H);
        \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk> 
      \<Longrightarrow> M(wfrec(r,a,H))"
apply (frule wfrec_replacement', assumption+) 
apply (frule wfrec_replacement_iff [THEN iffD1]) 
apply (rule wfrec_closed_lemma, assumption+) 
apply (simp_all add: wfrec_replacement_iff trans_eq_pair_wfrec_iff) 
done

subsection\<open>Absoluteness without assuming transitivity\<close>
lemma (in M_trancl) eq_pair_wfrec_iff:
  "\<lbrakk>wf(r);  M(r);  M(y); 
     strong_replacement(M, \<lambda>x z. \<exists>y[M]. \<exists>g[M].
          pair(M,x,y,z) \<and> 
          is_recfun(r^+, x, \<lambda>x f. H(x, restrict(f, r -`` {x})), g) \<and> 
          y = H(x, restrict(g, r -`` {x}))); 
     \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk> 
   \<Longrightarrow> y = <x, wfrec(r, x, H)> \<longleftrightarrow> 
       (\<exists>f[M]. is_recfun(r^+, x, \<lambda>x f. H(x, restrict(f, r -`` {x})), f) \<and> 
            y = <x, H(x,restrict(f,r-``{x}))>)"
apply safe  
 apply (simp add: wfrec_relativize [THEN iff_sym, of concl: _ x]) 
txt\<open>converse direction\<close>
apply (rule sym)
apply (simp add: wfrec_relativize, blast) 
done

text\<open>Full version not assuming transitivity, but maybe not very useful.\<close>
theorem (in M_trancl) wfrec_closed:
     "\<lbrakk>wf(r); M(r); M(a);
        wfrec_replacement(M,MH,r^+);  
        relation2(M,MH, \<lambda>x f. H(x, restrict(f, r -`` {x})));
        \<forall>x[M]. \<forall>g[M]. function(g) \<longrightarrow> M(H(x,g))\<rbrakk> 
      \<Longrightarrow> M(wfrec(r,a,H))"
apply (frule wfrec_replacement' 
               [of MH "r^+" "\<lambda>x f. H(x, restrict(f, r -`` {x}))"])
   prefer 4
   apply (frule wfrec_replacement_iff [THEN iffD1]) 
   apply (rule wfrec_closed_lemma, assumption+) 
     apply (simp_all add: eq_pair_wfrec_iff func.function_restrictI) 
done

end
