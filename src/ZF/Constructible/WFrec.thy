theory WFrec = Wellorderings:


(*Many of these might be useful in WF.thy*)

lemma apply_recfun2:
    "[| is_recfun(r,a,H,f); <x,i>:f |] ==> i = H(x, restrict(f,r-``{x}))"
apply (frule apply_recfun) 
 apply (blast dest: is_recfun_type fun_is_rel) 
apply (simp add: function_apply_equality [OF _ is_recfun_imp_function])
done

text{*Expresses @{text is_recfun} as a recursion equation*}
lemma is_recfun_iff_equation:
     "is_recfun(r,a,H,f) <->
	   f \<in> r -`` {a} \<rightarrow> range(f) &
	   (\<forall>x \<in> r-``{a}. f`x = H(x, restrict(f, r-``{x})))"  
apply (rule iffI) 
 apply (simp add: is_recfun_type apply_recfun Ball_def vimage_singleton_iff, 
        clarify)  
apply (simp add: is_recfun_def) 
apply (rule fun_extension) 
  apply assumption
 apply (fast intro: lam_type, simp) 
done

lemma is_recfun_imp_in_r: "[|is_recfun(r,a,H,f); \<langle>x,i\<rangle> \<in> f|] ==> \<langle>x, a\<rangle> \<in> r"
by (blast dest: is_recfun_type fun_is_rel)

lemma trans_Int_eq:
      "[| trans(r); <y,x> \<in> r |] ==> r -`` {x} \<inter> r -`` {y} = r -`` {y}"
by (blast intro: transD) 

lemma is_recfun_restrict_idem:
     "is_recfun(r,a,H,f) ==> restrict(f, r -`` {a}) = f"
apply (drule is_recfun_type)
apply (auto simp add: Pi_iff subset_Sigma_imp_relation restrict_idem)  
done

lemma is_recfun_cong_lemma:
  "[| is_recfun(r,a,H,f); r = r'; a = a'; f = f'; 
      !!x g. [| <x,a'> \<in> r'; relation(g); domain(g) <= r' -``{x} |] 
             ==> H(x,g) = H'(x,g) |]
   ==> is_recfun(r',a',H',f')"
apply (simp add: is_recfun_def) 
apply (erule trans) 
apply (rule lam_cong) 
apply (simp_all add: vimage_singleton_iff Int_lower2)  
done

text{*For @{text is_recfun} we need only pay attention to functions
      whose domains are initial segments of @{term r}.*}
lemma is_recfun_cong:
  "[| r = r'; a = a'; f = f'; 
      !!x g. [| <x,a'> \<in> r'; relation(g); domain(g) <= r' -``{x} |] 
             ==> H(x,g) = H'(x,g) |]
   ==> is_recfun(r,a,H,f) <-> is_recfun(r',a',H',f')"
apply (rule iffI)
txt{*Messy: fast and blast don't work for some reason*}
apply (erule is_recfun_cong_lemma, auto) 
apply (erule is_recfun_cong_lemma)
apply (blast intro: sym)+
done


text{*Stated using @{term "trans(r)"} rather than
      @{term "transitive_rel(M,A,r)"} because the latter rewrites to
      the former anyway, by @{text transitive_rel_abs}.
      As always, theorems should be expressed in simplified form.
      The last three M-premises are redundant because of @{term "M(r)"}, 
      but without them we'd have to undertake
      more work to set up the induction formula.*}
lemma (in M_axioms) is_recfun_equal [rule_format]: 
    "[|is_recfun(r,a,H,f);  is_recfun(r,b,H,g);  
       wellfounded(M,r);  trans(r);
       M(f); M(g); M(r); M(x); M(a); M(b) |] 
     ==> <x,a> \<in> r --> <x,b> \<in> r --> f`x=g`x"
apply (frule_tac f="f" in is_recfun_type) 
apply (frule_tac f="g" in is_recfun_type) 
apply (simp add: is_recfun_def)
apply (erule_tac a=x in wellfounded_induct, assumption+)
txt{*Separation to justify the induction*}
 apply (force intro: is_recfun_separation)
txt{*Now the inductive argument itself*}
apply clarify 
apply (erule ssubst)+
apply (simp (no_asm_simp) add: vimage_singleton_iff restrict_def)
apply (rename_tac x1)
apply (rule_tac t="%z. H(x1,z)" in subst_context) 
apply (subgoal_tac "ALL y : r-``{x1}. ALL z. <y,z>:f <-> <y,z>:g")
 apply (blast intro: transD) 
apply (simp add: apply_iff) 
apply (blast intro: transD sym) 
done

lemma (in M_axioms) is_recfun_cut: 
    "[|is_recfun(r,a,H,f);  is_recfun(r,b,H,g);  
       wellfounded(M,r); trans(r); 
       M(f); M(g); M(r); <b,a> \<in> r |]   
      ==> restrict(f, r-``{b}) = g"
apply (frule_tac f="f" in is_recfun_type) 
apply (rule fun_extension) 
apply (blast intro: transD restrict_type2) 
apply (erule is_recfun_type, simp) 
apply (blast intro: is_recfun_equal transD dest: transM) 
done

lemma (in M_axioms) is_recfun_functional:
     "[|is_recfun(r,a,H,f);  is_recfun(r,a,H,g);  
       wellfounded(M,r); trans(r); M(f); M(g); M(r) |] ==> f=g"
apply (rule fun_extension)
apply (erule is_recfun_type)+
apply (blast intro!: is_recfun_equal dest: transM) 
done 

text{*Tells us that @{text is_recfun} can (in principle) be relativized.*}
lemma (in M_axioms) is_recfun_relativize:
  "[| M(r); M(f); \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g)) |] 
   ==> is_recfun(r,a,H,f) <->
       (\<forall>z[M]. z \<in> f <-> 
        (\<exists>x[M]. <x,a> \<in> r & z = <x, H(x, restrict(f, r-``{x}))>))";
apply (simp add: is_recfun_def lam_def)
apply (safe intro!: equalityI) 
   apply (drule equalityD1 [THEN subsetD], assumption) 
   apply (blast dest: pair_components_in_M) 
  apply (blast elim!: equalityE dest: pair_components_in_M)
 apply (frule transM, assumption, rotate_tac -1) 
 apply simp  
 apply blast
apply (subgoal_tac "is_function(M,f)")
 txt{*We use @{term "is_function"} rather than @{term "function"} because
      the subgoal's easier to prove with relativized quantifiers!*}
 prefer 2 apply (simp add: is_function_def) 
apply (frule pair_components_in_M, assumption) 
apply (simp add: is_recfun_imp_function function_restrictI) 
done

(* ideas for further weaking the H-closure premise:
apply (drule spec [THEN spec]) 
apply (erule mp)
apply (intro conjI)
apply (blast dest!: pair_components_in_M)
apply (blast intro!: function_restrictI dest!: pair_components_in_M)
apply (blast intro!: function_restrictI dest!: pair_components_in_M)
apply (simp only: subset_iff domain_iff restrict_iff vimage_iff) 
apply (simp add: vimage_singleton_iff) 
apply (intro allI impI conjI)
apply (blast intro: transM dest!: pair_components_in_M)
prefer 4;apply blast 
*)

lemma (in M_axioms) is_recfun_restrict:
     "[| wellfounded(M,r); trans(r); is_recfun(r,x,H,f); \<langle>y,x\<rangle> \<in> r; 
       M(r); M(f); 
       \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g)) |]
       ==> is_recfun(r, y, H, restrict(f, r -`` {y}))"
apply (frule pair_components_in_M, assumption, clarify) 
apply (simp (no_asm_simp) add: is_recfun_relativize restrict_iff
           trans_Int_eq)
apply safe
  apply (simp_all add: vimage_singleton_iff is_recfun_type [THEN apply_iff]) 
  apply (frule_tac x=xa in pair_components_in_M, assumption)
  apply (frule_tac x=xa in apply_recfun, blast intro: transD)  
  apply (simp add: is_recfun_type [THEN apply_iff] 
                   is_recfun_imp_function function_restrictI)
apply (blast intro: apply_recfun dest: transD)
done
 
lemma (in M_axioms) restrict_Y_lemma:
   "[| wellfounded(M,r); trans(r); M(r);
       \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g));  M(Y);
       \<forall>b[M]. 
	   b \<in> Y <->
	   (\<exists>x[M]. <x,a1> \<in> r &
            (\<exists>y[M]. b = \<langle>x,y\<rangle> & (\<exists>g[M]. is_recfun(r,x,H,g) \<and> y = H(x,g))));
          \<langle>x,a1\<rangle> \<in> r; is_recfun(r,x,H,f); M(f) |]
       ==> restrict(Y, r -`` {x}) = f"
apply (subgoal_tac "\<forall>y \<in> r-``{x}. \<forall>z. <y,z>:Y <-> <y,z>:f") 
 apply (simp (no_asm_simp) add: restrict_def) 
 apply (thin_tac "rall(M,?P)")+  --{*essential for efficiency*}
 apply (frule is_recfun_type [THEN fun_is_rel], blast)
apply (frule pair_components_in_M, assumption, clarify) 
apply (rule iffI)
 apply (frule_tac y="<y,z>" in transM, assumption )
 apply (rotate_tac -1)   
 apply (clarsimp simp add: vimage_singleton_iff is_recfun_type [THEN apply_iff]
			   apply_recfun is_recfun_cut) 
txt{*Opposite inclusion: something in f, show in Y*}
apply (frule_tac y="<y,z>" in transM, assumption)  
apply (simp add: vimage_singleton_iff) 
apply (rule conjI) 
 apply (blast dest: transD) 
apply (rule_tac x="restrict(f, r -`` {y})" in rexI) 
apply (simp_all add: is_recfun_restrict
                     apply_recfun is_recfun_type [THEN apply_iff]) 
done

text{*For typical applications of Replacement for recursive definitions*}
lemma (in M_axioms) univalent_is_recfun:
     "[|wellfounded(M,r); trans(r); M(r)|]
      ==> univalent (M, A, \<lambda>x p. 
              \<exists>y[M]. p = \<langle>x,y\<rangle> & (\<exists>f[M]. is_recfun(r,x,H,f) & y = H(x,f)))"
apply (simp add: univalent_def) 
apply (blast dest: is_recfun_functional) 
done


text{*Proof of the inductive step for @{text exists_is_recfun}, since
      we must prove two versions.*}
lemma (in M_axioms) exists_is_recfun_indstep:
    "[|\<forall>y. \<langle>y, a1\<rangle> \<in> r --> (\<exists>f[M]. is_recfun(r, y, H, f)); 
       wellfounded(M,r); trans(r); M(r); M(a1);
       strong_replacement(M, \<lambda>x z. 
              \<exists>y[M]. \<exists>g[M]. pair(M,x,y,z) & is_recfun(r,x,H,g) & y = H(x,g)); 
       \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g))|]   
      ==> \<exists>f[M]. is_recfun(r,a1,H,f)"
apply (drule_tac A="r-``{a1}" in strong_replacementD)
  apply blast 
 txt{*Discharge the "univalent" obligation of Replacement*}
 apply (simp add: univalent_is_recfun) 
txt{*Show that the constructed object satisfies @{text is_recfun}*} 
apply clarify 
apply (rule_tac x=Y in rexI)  
txt{*Unfold only the top-level occurrence of @{term is_recfun}*}
apply (simp (no_asm_simp) add: is_recfun_relativize [of concl: _ a1])
txt{*The big iff-formula defining @{term Y} is now redundant*}
apply safe 
 apply (simp add: vimage_singleton_iff restrict_Y_lemma [of r H _ a1]) 
txt{*one more case*}
apply (simp (no_asm_simp) add: Bex_def vimage_singleton_iff)
apply (drule_tac x1=x in spec [THEN mp], assumption, clarify) 
apply (rename_tac f) 
apply (rule_tac x=f in rexI) 
apply (simp_all add: restrict_Y_lemma [of r H])
txt{*FIXME: should not be needed!*}
apply (subst restrict_Y_lemma [of r H])
apply (simp add: vimage_singleton_iff)+
apply blast+
done

text{*Relativized version, when we have the (currently weaker) premise
      @{term "wellfounded(M,r)"}*}
lemma (in M_axioms) wellfounded_exists_is_recfun:
    "[|wellfounded(M,r);  trans(r);  
       separation(M, \<lambda>x. ~ (\<exists>f[M]. is_recfun(r, x, H, f)));
       strong_replacement(M, \<lambda>x z. 
          \<exists>y[M]. \<exists>g[M]. pair(M,x,y,z) & is_recfun(r,x,H,g) & y = H(x,g)); 
       M(r);  M(a);  
       \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g)) |]   
      ==> \<exists>f[M]. is_recfun(r,a,H,f)"
apply (rule wellfounded_induct, assumption+, clarify)
apply (rule exists_is_recfun_indstep, assumption+)
done

lemma (in M_axioms) wf_exists_is_recfun [rule_format]:
    "[|wf(r);  trans(r);  M(r);  
       strong_replacement(M, \<lambda>x z. 
         \<exists>y[M]. \<exists>g[M]. pair(M,x,y,z) & is_recfun(r,x,H,g) & y = H(x,g)); 
       \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g)) |]   
      ==> M(a) --> (\<exists>f[M]. is_recfun(r,a,H,f))"
apply (rule wf_induct, assumption+)
apply (frule wf_imp_relativized)
apply (intro impI)
apply (rule exists_is_recfun_indstep) 
      apply (blast dest: transM del: rev_rallE, assumption+)
done

constdefs
 M_is_recfun :: "[i=>o, i, i, [i=>o,i,i,i]=>o, i] => o"
   "M_is_recfun(M,r,a,MH,f) == 
     \<forall>z[M]. z \<in> f <-> 
            (\<exists>x[M]. \<exists>y[M]. \<exists>xa[M]. \<exists>sx[M]. \<exists>r_sx[M]. \<exists>f_r_sx[M]. 
	       pair(M,x,y,z) & pair(M,x,a,xa) & upair(M,x,x,sx) &
               pre_image(M,r,sx,r_sx) & restriction(M,f,r_sx,f_r_sx) &
               xa \<in> r & MH(M, x, f_r_sx, y))"

lemma (in M_axioms) is_recfun_iff_M:
     "[| M(r); M(a); M(f); \<forall>x[M]. \<forall>g[M]. function(g) --> M(H(x,g));
       \<forall>x g y. M(x) --> M(g) --> M(y) --> MH(M,x,g,y) <-> y = H(x,g) |] ==>
       is_recfun(r,a,H,f) <-> M_is_recfun(M,r,a,MH,f)"
apply (simp add: M_is_recfun_def is_recfun_relativize)
apply (rule rall_cong)
apply (blast dest: transM)
done

lemma M_is_recfun_cong [cong]:
     "[| r = r'; a = a'; f = f'; 
       !!x g y. [| M(x); M(g); M(y) |] ==> MH(M,x,g,y) <-> MH'(M,x,g,y) |]
      ==> M_is_recfun(M,r,a,MH,f) <-> M_is_recfun(M,r',a',MH',f')"
by (simp add: M_is_recfun_def) 


constdefs
 (*This expresses ordinal addition as a formula in the LAST.  It also 
   provides an abbreviation that can be used in the instance of strong
   replacement below.  Here j is used to define the relation, namely
   Memrel(succ(j)), while x determines the domain of f.*)
 is_oadd_fun :: "[i=>o,i,i,i,i] => o"
    "is_oadd_fun(M,i,j,x,f) == 
       (\<forall>sj msj. M(sj) --> M(msj) --> 
                 successor(M,j,sj) --> membership(M,sj,msj) --> 
	         M_is_recfun(M, msj, x, 
		     %M x g y. \<exists>gx. M(gx) & image(M,g,x,gx) & union(M,i,gx,y),
		     f))"

 is_oadd :: "[i=>o,i,i,i] => o"
    "is_oadd(M,i,j,k) == 
        (~ ordinal(M,i) & ~ ordinal(M,j) & k=0) |
        (~ ordinal(M,i) & ordinal(M,j) & k=j) |
        (ordinal(M,i) & ~ ordinal(M,j) & k=i) |
        (ordinal(M,i) & ordinal(M,j) & 
	 (\<exists>f fj sj. M(f) & M(fj) & M(sj) & 
		    successor(M,j,sj) & is_oadd_fun(M,i,sj,sj,f) & 
		    fun_apply(M,f,j,fj) & fj = k))"

 (*NEEDS RELATIVIZATION*)
 omult_eqns :: "[i,i,i,i] => o"
    "omult_eqns(i,x,g,z) ==
            Ord(x) & 
	    (x=0 --> z=0) &
            (\<forall>j. x = succ(j) --> z = g`j ++ i) &
            (Limit(x) --> z = \<Union>(g``x))"

 is_omult_fun :: "[i=>o,i,i,i] => o"
    "is_omult_fun(M,i,j,f) == 
	    (\<exists>df. M(df) & is_function(M,f) & 
                  is_domain(M,f,df) & subset(M, j, df)) & 
            (\<forall>x\<in>j. omult_eqns(i,x,f,f`x))"

 is_omult :: "[i=>o,i,i,i] => o"
    "is_omult(M,i,j,k) == 
	\<exists>f fj sj. M(f) & M(fj) & M(sj) & 
                  successor(M,j,sj) & is_omult_fun(M,i,sj,f) & 
                  fun_apply(M,f,j,fj) & fj = k"


locale M_ord_arith = M_axioms +
  assumes oadd_strong_replacement:
   "[| M(i); M(j) |] ==>
    strong_replacement(M, 
         \<lambda>x z. \<exists>y[M]. pair(M,x,y,z) & 
                  (\<exists>f[M]. \<exists>fx[M]. is_oadd_fun(M,i,j,x,f) & 
		           image(M,f,x,fx) & y = i Un fx))"

 and omult_strong_replacement':
   "[| M(i); M(j) |] ==>
    strong_replacement(M, 
         \<lambda>x z. \<exists>y[M]. z = <x,y> &
	     (\<exists>g[M]. is_recfun(Memrel(succ(j)),x,%x g. THE z. omult_eqns(i,x,g,z),g) & 
	     y = (THE z. omult_eqns(i, x, g, z))))" 



text{*@{text is_oadd_fun}: Relating the pure "language of set theory" to Isabelle/ZF*}
lemma (in M_ord_arith) is_oadd_fun_iff:
   "[| a\<le>j; M(i); M(j); M(a); M(f) |] 
    ==> is_oadd_fun(M,i,j,a,f) <->
	f \<in> a \<rightarrow> range(f) & (\<forall>x. M(x) --> x < a --> f`x = i Un f``x)"
apply (frule lt_Ord) 
apply (simp add: is_oadd_fun_def Memrel_closed Un_closed 
             is_recfun_iff_M [of concl: _ _ "%x g. i Un g``x", THEN iff_sym]
             image_closed is_recfun_iff_equation  
             Ball_def lt_trans [OF ltI, of _ a] lt_Memrel)
apply (simp add: lt_def) 
apply (blast dest: transM) 
done


lemma (in M_ord_arith) oadd_strong_replacement':
    "[| M(i); M(j) |] ==>
     strong_replacement(M, 
            \<lambda>x z. \<exists>y[M]. z = <x,y> &
		  (\<exists>g[M]. is_recfun(Memrel(succ(j)),x,%x g. i Un g``x,g) & 
		  y = i Un g``x))" 
apply (insert oadd_strong_replacement [of i j]) 
apply (simp add: Memrel_closed Un_closed image_closed is_oadd_fun_def
                 is_recfun_iff_M)  
done


lemma (in M_ord_arith) exists_oadd:
    "[| Ord(j);  M(i);  M(j) |]
     ==> \<exists>f[M]. is_recfun(Memrel(succ(j)), j, %x g. i Un g``x, f)"
apply (rule wf_exists_is_recfun [OF wf_Memrel trans_Memrel])
    apply (simp_all add: Memrel_type oadd_strong_replacement') 
done 

lemma (in M_ord_arith) exists_oadd_fun:
    "[| Ord(j);  M(i);  M(j) |] ==> \<exists>f[M]. is_oadd_fun(M,i,succ(j),succ(j),f)"
apply (rule exists_oadd [THEN rexE])
apply (erule Ord_succ, assumption, simp) 
apply (rename_tac f) 
apply (frule is_recfun_type)
apply (rule_tac x=f in rexI) 
 apply (simp add: fun_is_function domain_of_fun lt_Memrel apply_recfun lt_def
                  is_oadd_fun_iff Ord_trans [OF _ succI1], assumption)
done

lemma (in M_ord_arith) is_oadd_fun_apply:
    "[| x < j; M(i); M(j); M(f); is_oadd_fun(M,i,j,j,f) |] 
     ==> f`x = i Un (\<Union>k\<in>x. {f ` k})"
apply (simp add: is_oadd_fun_iff lt_Ord2, clarify) 
apply (frule lt_closed, simp)
apply (frule leI [THEN le_imp_subset])  
apply (simp add: image_fun, blast) 
done

lemma (in M_ord_arith) is_oadd_fun_iff_oadd [rule_format]:
    "[| is_oadd_fun(M,i,J,J,f); M(i); M(J); M(f); Ord(i); Ord(j) |] 
     ==> j<J --> f`j = i++j"
apply (erule_tac i=j in trans_induct, clarify) 
apply (subgoal_tac "\<forall>k\<in>x. k<J")
 apply (simp (no_asm_simp) add: is_oadd_def oadd_unfold is_oadd_fun_apply)
apply (blast intro: lt_trans ltI lt_Ord) 
done

lemma (in M_ord_arith) oadd_abs_fun_apply_iff:
    "[| M(i); M(J); M(f); M(k); j<J; is_oadd_fun(M,i,J,J,f) |] 
     ==> fun_apply(M,f,j,k) <-> f`j = k"
by (force simp add: lt_def is_oadd_fun_iff subsetD typed_apply_abs) 

lemma (in M_ord_arith) Ord_oadd_abs:
    "[| M(i); M(j); M(k); Ord(i); Ord(j) |] ==> is_oadd(M,i,j,k) <-> k = i++j"
apply (simp add: is_oadd_def oadd_abs_fun_apply_iff is_oadd_fun_iff_oadd)
apply (frule exists_oadd_fun [of j i], blast+)
done

lemma (in M_ord_arith) oadd_abs:
    "[| M(i); M(j); M(k) |] ==> is_oadd(M,i,j,k) <-> k = i++j"
apply (case_tac "Ord(i) & Ord(j)")
 apply (simp add: Ord_oadd_abs)
apply (auto simp add: is_oadd_def oadd_eq_if_raw_oadd)
done

lemma (in M_ord_arith) oadd_closed [intro,simp]:
    "[| M(i); M(j) |] ==> M(i++j)"
apply (simp add: oadd_eq_if_raw_oadd, clarify) 
apply (simp add: raw_oadd_eq_oadd) 
apply (frule exists_oadd_fun [of j i], auto)
apply (simp add: apply_closed is_oadd_fun_iff_oadd [symmetric]) 
done


text{*Ordinal Multiplication*}

lemma omult_eqns_unique:
     "[| omult_eqns(i,x,g,z); omult_eqns(i,x,g,z') |] ==> z=z'";
apply (simp add: omult_eqns_def, clarify) 
apply (erule Ord_cases, simp_all) 
done

lemma omult_eqns_0: "omult_eqns(i,0,g,z) <-> z=0"
by (simp add: omult_eqns_def)

lemma the_omult_eqns_0: "(THE z. omult_eqns(i,0,g,z)) = 0"
by (simp add: omult_eqns_0)

lemma omult_eqns_succ: "omult_eqns(i,succ(j),g,z) <-> Ord(j) & z = g`j ++ i"
by (simp add: omult_eqns_def)

lemma the_omult_eqns_succ:
     "Ord(j) ==> (THE z. omult_eqns(i,succ(j),g,z)) = g`j ++ i"
by (simp add: omult_eqns_succ) 

lemma omult_eqns_Limit:
     "Limit(x) ==> omult_eqns(i,x,g,z) <-> z = \<Union>(g``x)"
apply (simp add: omult_eqns_def) 
apply (blast intro: Limit_is_Ord) 
done

lemma the_omult_eqns_Limit:
     "Limit(x) ==> (THE z. omult_eqns(i,x,g,z)) = \<Union>(g``x)"
by (simp add: omult_eqns_Limit)

lemma omult_eqns_Not: "~ Ord(x) ==> ~ omult_eqns(i,x,g,z)"
by (simp add: omult_eqns_def)


lemma (in M_ord_arith) the_omult_eqns_closed:
    "[| M(i); M(x); M(g); function(g) |] 
     ==> M(THE z. omult_eqns(i, x, g, z))"
apply (case_tac "Ord(x)")
 prefer 2 apply (simp add: omult_eqns_Not) --{*trivial, non-Ord case*}
apply (erule Ord_cases) 
  apply (simp add: omult_eqns_0)
 apply (simp add: omult_eqns_succ apply_closed oadd_closed) 
apply (simp add: omult_eqns_Limit) 
done

lemma (in M_ord_arith) exists_omult:
    "[| Ord(j);  M(i);  M(j) |]
     ==> \<exists>f[M]. is_recfun(Memrel(succ(j)), j, %x g. THE z. omult_eqns(i,x,g,z), f)"
apply (rule wf_exists_is_recfun [OF wf_Memrel trans_Memrel])
    apply (simp_all add: Memrel_type omult_strong_replacement') 
apply (blast intro: the_omult_eqns_closed) 
done

lemma (in M_ord_arith) exists_omult_fun:
    "[| Ord(j);  M(i);  M(j) |] ==> \<exists>f[M]. is_omult_fun(M,i,succ(j),f)"
apply (rule exists_omult [THEN rexE])
apply (erule Ord_succ, assumption, simp) 
apply (rename_tac f) 
apply (frule is_recfun_type)
apply (rule_tac x=f in rexI) 
apply (simp add: fun_is_function domain_of_fun lt_Memrel apply_recfun lt_def
                 is_omult_fun_def Ord_trans [OF _ succI1])
 apply (force dest: Ord_in_Ord' 
              simp add: omult_eqns_def the_omult_eqns_0 the_omult_eqns_succ
                        the_omult_eqns_Limit, assumption)
done

lemma (in M_ord_arith) is_omult_fun_apply_0:
    "[| 0 < j; is_omult_fun(M,i,j,f) |] ==> f`0 = 0"
by (simp add: is_omult_fun_def omult_eqns_def lt_def ball_conj_distrib)

lemma (in M_ord_arith) is_omult_fun_apply_succ:
    "[| succ(x) < j; is_omult_fun(M,i,j,f) |] ==> f`succ(x) = f`x ++ i"
by (simp add: is_omult_fun_def omult_eqns_def lt_def, blast) 

lemma (in M_ord_arith) is_omult_fun_apply_Limit:
    "[| x < j; Limit(x); M(j); M(f); is_omult_fun(M,i,j,f) |] 
     ==> f ` x = (\<Union>y\<in>x. f`y)"
apply (simp add: is_omult_fun_def omult_eqns_def domain_closed lt_def, clarify)
apply (drule subset_trans [OF OrdmemD], assumption+)  
apply (simp add: ball_conj_distrib omult_Limit image_function)
done

lemma (in M_ord_arith) is_omult_fun_eq_omult:
    "[| is_omult_fun(M,i,J,f); M(J); M(f); Ord(i); Ord(j) |] 
     ==> j<J --> f`j = i**j"
apply (erule_tac i=j in trans_induct3)
apply (safe del: impCE)
  apply (simp add: is_omult_fun_apply_0) 
 apply (subgoal_tac "x<J") 
  apply (simp add: is_omult_fun_apply_succ omult_succ)  
 apply (blast intro: lt_trans) 
apply (subgoal_tac "\<forall>k\<in>x. k<J")
 apply (simp add: is_omult_fun_apply_Limit omult_Limit) 
apply (blast intro: lt_trans ltI lt_Ord) 
done

lemma (in M_ord_arith) omult_abs_fun_apply_iff:
    "[| M(i); M(J); M(f); M(k); j<J; is_omult_fun(M,i,J,f) |] 
     ==> fun_apply(M,f,j,k) <-> f`j = k"
by (auto simp add: lt_def is_omult_fun_def subsetD apply_abs) 

lemma (in M_ord_arith) omult_abs:
    "[| M(i); M(j); M(k); Ord(i); Ord(j) |] ==> is_omult(M,i,j,k) <-> k = i**j"
apply (simp add: is_omult_def omult_abs_fun_apply_iff is_omult_fun_eq_omult)
apply (frule exists_omult_fun [of j i], blast+)
done

end

