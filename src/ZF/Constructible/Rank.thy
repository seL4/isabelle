(*  Title:      ZF/Constructible/Rank.thy
    ID:   $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
*)

header {*Absoluteness for Order Types, Rank Functions and Well-Founded 
         Relations*}

theory Rank = WF_absolute:

subsection {*Order Types: A Direct Construction by Replacement*}

locale M_ordertype = M_basic +
assumes well_ord_iso_separation:
     "[| M(A); M(f); M(r) |]
      ==> separation (M, \<lambda>x. x\<in>A --> (\<exists>y[M]. (\<exists>p[M].
		     fun_apply(M,f,x,y) & pair(M,y,x,p) & p \<in> r)))"
  and obase_separation:
     --{*part of the order type formalization*}
     "[| M(A); M(r) |]
      ==> separation(M, \<lambda>a. \<exists>x[M]. \<exists>g[M]. \<exists>mx[M]. \<exists>par[M].
	     ordinal(M,x) & membership(M,x,mx) & pred_set(M,A,a,r,par) &
	     order_isomorphism(M,par,r,x,mx,g))"
  and obase_equals_separation:
     "[| M(A); M(r) |]
      ==> separation (M, \<lambda>x. x\<in>A --> ~(\<exists>y[M]. \<exists>g[M].
			      ordinal(M,y) & (\<exists>my[M]. \<exists>pxr[M].
			      membership(M,y,my) & pred_set(M,A,x,r,pxr) &
			      order_isomorphism(M,pxr,r,y,my,g))))"
  and omap_replacement:
     "[| M(A); M(r) |]
      ==> strong_replacement(M,
             \<lambda>a z. \<exists>x[M]. \<exists>g[M]. \<exists>mx[M]. \<exists>par[M].
	     ordinal(M,x) & pair(M,a,x,z) & membership(M,x,mx) &
	     pred_set(M,A,a,r,par) & order_isomorphism(M,par,r,x,mx,g))"


text{*Inductive argument for Kunen's Lemma I 6.1, etc.
      Simple proof from Halmos, page 72*}
lemma  (in M_ordertype) wellordered_iso_subset_lemma: 
     "[| wellordered(M,A,r);  f \<in> ord_iso(A,r, A',r);  A'<= A;  y \<in> A;  
       M(A);  M(f);  M(r) |] ==> ~ <f`y, y> \<in> r"
apply (unfold wellordered_def ord_iso_def)
apply (elim conjE CollectE) 
apply (erule wellfounded_on_induct, assumption+)
 apply (insert well_ord_iso_separation [of A f r])
 apply (simp, clarify) 
apply (drule_tac a = x in bij_is_fun [THEN apply_type], assumption, blast)
done


text{*Kunen's Lemma I 6.1, page 14: 
      there's no order-isomorphism to an initial segment of a well-ordering*}
lemma (in M_ordertype) wellordered_iso_predD:
     "[| wellordered(M,A,r);  f \<in> ord_iso(A, r, Order.pred(A,x,r), r);  
       M(A);  M(f);  M(r) |] ==> x \<notin> A"
apply (rule notI) 
apply (frule wellordered_iso_subset_lemma, assumption)
apply (auto elim: predE)  
(*Now we know  ~ (f`x < x) *)
apply (drule ord_iso_is_bij [THEN bij_is_fun, THEN apply_type], assumption)
(*Now we also know f`x  \<in> pred(A,x,r);  contradiction! *)
apply (simp add: Order.pred_def)
done


lemma (in M_ordertype) wellordered_iso_pred_eq_lemma:
     "[| f \<in> \<langle>Order.pred(A,y,r), r\<rangle> \<cong> \<langle>Order.pred(A,x,r), r\<rangle>;
       wellordered(M,A,r); x\<in>A; y\<in>A; M(A); M(f); M(r) |] ==> <x,y> \<notin> r"
apply (frule wellordered_is_trans_on, assumption)
apply (rule notI) 
apply (drule_tac x2=y and x=x and r2=r in 
         wellordered_subset [OF _ pred_subset, THEN wellordered_iso_predD]) 
apply (simp add: trans_pred_pred_eq) 
apply (blast intro: predI dest: transM)+
done


text{*Simple consequence of Lemma 6.1*}
lemma (in M_ordertype) wellordered_iso_pred_eq:
     "[| wellordered(M,A,r);
       f \<in> ord_iso(Order.pred(A,a,r), r, Order.pred(A,c,r), r);   
       M(A);  M(f);  M(r);  a\<in>A;  c\<in>A |] ==> a=c"
apply (frule wellordered_is_trans_on, assumption)
apply (frule wellordered_is_linear, assumption)
apply (erule_tac x=a and y=c in linearE, auto) 
apply (drule ord_iso_sym)
(*two symmetric cases*)
apply (blast dest: wellordered_iso_pred_eq_lemma)+ 
done


text{*Following Kunen's Theorem I 7.6, page 17.  Note that this material is
not required elsewhere.*}

text{*Can't use @{text well_ord_iso_preserving} because it needs the
strong premise @{term "well_ord(A,r)"}*}
lemma (in M_ordertype) ord_iso_pred_imp_lt:
     "[| f \<in> ord_iso(Order.pred(A,x,r), r, i, Memrel(i));
         g \<in> ord_iso(Order.pred(A,y,r), r, j, Memrel(j));
         wellordered(M,A,r);  x \<in> A;  y \<in> A; M(A); M(r); M(f); M(g); M(j);
         Ord(i); Ord(j); \<langle>x,y\<rangle> \<in> r |]
      ==> i < j"
apply (frule wellordered_is_trans_on, assumption)
apply (frule_tac y=y in transM, assumption) 
apply (rule_tac i=i and j=j in Ord_linear_lt, auto)  
txt{*case @{term "i=j"} yields a contradiction*}
 apply (rule_tac x1=x and A1="Order.pred(A,y,r)" in 
          wellordered_iso_predD [THEN notE]) 
   apply (blast intro: wellordered_subset [OF _ pred_subset]) 
  apply (simp add: trans_pred_pred_eq)
  apply (blast intro: Ord_iso_implies_eq ord_iso_sym ord_iso_trans) 
 apply (simp_all add: pred_iff pred_closed converse_closed comp_closed)
txt{*case @{term "j<i"} also yields a contradiction*}
apply (frule restrict_ord_iso2, assumption+) 
apply (frule ord_iso_sym [THEN ord_iso_is_bij, THEN bij_is_fun]) 
apply (frule apply_type, blast intro: ltD) 
  --{*thus @{term "converse(f)`j \<in> Order.pred(A,x,r)"}*}
apply (simp add: pred_iff) 
apply (subgoal_tac
       "\<exists>h[M]. h \<in> ord_iso(Order.pred(A,y,r), r, 
                               Order.pred(A, converse(f)`j, r), r)")
 apply (clarify, frule wellordered_iso_pred_eq, assumption+)
 apply (blast dest: wellordered_asym)  
apply (intro rexI)
 apply (blast intro: Ord_iso_implies_eq ord_iso_sym ord_iso_trans)+
done


lemma ord_iso_converse1:
     "[| f: ord_iso(A,r,B,s);  <b, f`a>: s;  a:A;  b:B |] 
      ==> <converse(f) ` b, a> : r"
apply (frule ord_iso_converse, assumption+) 
apply (blast intro: ord_iso_is_bij [THEN bij_is_fun, THEN apply_funtype]) 
apply (simp add: left_inverse_bij [OF ord_iso_is_bij])
done


constdefs
  
  obase :: "[i=>o,i,i] => i"
       --{*the domain of @{text om}, eventually shown to equal @{text A}*}
   "obase(M,A,r) == {a\<in>A. \<exists>x[M]. \<exists>g[M]. Ord(x) & 
                          g \<in> ord_iso(Order.pred(A,a,r),r,x,Memrel(x))}"

  omap :: "[i=>o,i,i,i] => o"  
    --{*the function that maps wosets to order types*}
   "omap(M,A,r,f) == 
	\<forall>z[M].
         z \<in> f <-> (\<exists>a\<in>A. \<exists>x[M]. \<exists>g[M]. z = <a,x> & Ord(x) & 
                        g \<in> ord_iso(Order.pred(A,a,r),r,x,Memrel(x)))"


  otype :: "[i=>o,i,i,i] => o"  --{*the order types themselves*}
   "otype(M,A,r,i) == \<exists>f[M]. omap(M,A,r,f) & is_range(M,f,i)"


text{*Can also be proved with the premise @{term "M(z)"} instead of
      @{term "M(f)"}, but that version is less useful.  This lemma
      is also more useful than the definition, @{text omap_def}.*}
lemma (in M_ordertype) omap_iff:
     "[| omap(M,A,r,f); M(A); M(f) |] 
      ==> z \<in> f <->
          (\<exists>a\<in>A. \<exists>x[M]. \<exists>g[M]. z = <a,x> & Ord(x) & 
                                g \<in> ord_iso(Order.pred(A,a,r),r,x,Memrel(x)))"
apply (simp add: omap_def Memrel_closed pred_closed) 
apply (rule iffI)
 apply (drule_tac [2] x=z in rspec)
 apply (drule_tac x=z in rspec)
 apply (blast dest: transM)+
done

lemma (in M_ordertype) omap_unique:
     "[| omap(M,A,r,f); omap(M,A,r,f'); M(A); M(r); M(f); M(f') |] ==> f' = f" 
apply (rule equality_iffI) 
apply (simp add: omap_iff) 
done

lemma (in M_ordertype) omap_yields_Ord:
     "[| omap(M,A,r,f); \<langle>a,x\<rangle> \<in> f; M(a); M(x) |]  ==> Ord(x)"
  by (simp add: omap_def)

lemma (in M_ordertype) otype_iff:
     "[| otype(M,A,r,i); M(A); M(r); M(i) |] 
      ==> x \<in> i <-> 
          (M(x) & Ord(x) & 
           (\<exists>a\<in>A. \<exists>g[M]. g \<in> ord_iso(Order.pred(A,a,r),r,x,Memrel(x))))"
apply (auto simp add: omap_iff otype_def)
 apply (blast intro: transM) 
apply (rule rangeI) 
apply (frule transM, assumption)
apply (simp add: omap_iff, blast)
done

lemma (in M_ordertype) otype_eq_range:
     "[| omap(M,A,r,f); otype(M,A,r,i); M(A); M(r); M(f); M(i) |] 
      ==> i = range(f)"
apply (auto simp add: otype_def omap_iff)
apply (blast dest: omap_unique) 
done


lemma (in M_ordertype) Ord_otype:
     "[| otype(M,A,r,i); trans[A](r); M(A); M(r); M(i) |] ==> Ord(i)"
apply (rule OrdI) 
prefer 2 
    apply (simp add: Ord_def otype_def omap_def) 
    apply clarify 
    apply (frule pair_components_in_M, assumption) 
    apply blast 
apply (auto simp add: Transset_def otype_iff) 
  apply (blast intro: transM)
 apply (blast intro: Ord_in_Ord) 
apply (rename_tac y a g)
apply (frule ord_iso_sym [THEN ord_iso_is_bij, THEN bij_is_fun, 
			  THEN apply_funtype],  assumption)  
apply (rule_tac x="converse(g)`y" in bexI)
 apply (frule_tac a="converse(g) ` y" in ord_iso_restrict_pred, assumption) 
apply (safe elim!: predE) 
apply (blast intro: restrict_ord_iso ord_iso_sym ltI dest: transM)
done

lemma (in M_ordertype) domain_omap:
     "[| omap(M,A,r,f);  M(A); M(r); M(B); M(f) |] 
      ==> domain(f) = obase(M,A,r)"
apply (simp add: domain_closed obase_def) 
apply (rule equality_iffI) 
apply (simp add: domain_iff omap_iff, blast) 
done

lemma (in M_ordertype) omap_subset: 
     "[| omap(M,A,r,f); otype(M,A,r,i); 
       M(A); M(r); M(f); M(B); M(i) |] ==> f \<subseteq> obase(M,A,r) * i"
apply clarify 
apply (simp add: omap_iff obase_def) 
apply (force simp add: otype_iff) 
done

lemma (in M_ordertype) omap_funtype: 
     "[| omap(M,A,r,f); otype(M,A,r,i); 
         M(A); M(r); M(f); M(i) |] ==> f \<in> obase(M,A,r) -> i"
apply (simp add: domain_omap omap_subset Pi_iff function_def omap_iff) 
apply (blast intro: Ord_iso_implies_eq ord_iso_sym ord_iso_trans) 
done


lemma (in M_ordertype) wellordered_omap_bij:
     "[| wellordered(M,A,r); omap(M,A,r,f); otype(M,A,r,i); 
       M(A); M(r); M(f); M(i) |] ==> f \<in> bij(obase(M,A,r),i)"
apply (insert omap_funtype [of A r f i]) 
apply (auto simp add: bij_def inj_def) 
prefer 2  apply (blast intro: fun_is_surj dest: otype_eq_range) 
apply (frule_tac a=w in apply_Pair, assumption) 
apply (frule_tac a=x in apply_Pair, assumption) 
apply (simp add: omap_iff) 
apply (blast intro: wellordered_iso_pred_eq ord_iso_sym ord_iso_trans) 
done


text{*This is not the final result: we must show @{term "oB(A,r) = A"}*}
lemma (in M_ordertype) omap_ord_iso:
     "[| wellordered(M,A,r); omap(M,A,r,f); otype(M,A,r,i); 
       M(A); M(r); M(f); M(i) |] ==> f \<in> ord_iso(obase(M,A,r),r,i,Memrel(i))"
apply (rule ord_isoI)
 apply (erule wellordered_omap_bij, assumption+) 
apply (insert omap_funtype [of A r f i], simp) 
apply (frule_tac a=x in apply_Pair, assumption) 
apply (frule_tac a=y in apply_Pair, assumption) 
apply (auto simp add: omap_iff)
 txt{*direction 1: assuming @{term "\<langle>x,y\<rangle> \<in> r"}*}
 apply (blast intro: ltD ord_iso_pred_imp_lt)
 txt{*direction 2: proving @{term "\<langle>x,y\<rangle> \<in> r"} using linearity of @{term r}*}
apply (rename_tac x y g ga) 
apply (frule wellordered_is_linear, assumption, 
       erule_tac x=x and y=y in linearE, assumption+) 
txt{*the case @{term "x=y"} leads to immediate contradiction*} 
apply (blast elim: mem_irrefl) 
txt{*the case @{term "\<langle>y,x\<rangle> \<in> r"}: handle like the opposite direction*}
apply (blast dest: ord_iso_pred_imp_lt ltD elim: mem_asym) 
done

lemma (in M_ordertype) Ord_omap_image_pred:
     "[| wellordered(M,A,r); omap(M,A,r,f); otype(M,A,r,i); 
       M(A); M(r); M(f); M(i); b \<in> A |] ==> Ord(f `` Order.pred(A,b,r))"
apply (frule wellordered_is_trans_on, assumption)
apply (rule OrdI) 
	prefer 2 apply (simp add: image_iff omap_iff Ord_def, blast) 
txt{*Hard part is to show that the image is a transitive set.*}
apply (simp add: Transset_def, clarify) 
apply (simp add: image_iff pred_iff apply_iff [OF omap_funtype [of A r f i]])
apply (rename_tac c j, clarify)
apply (frule omap_funtype [of A r f, THEN apply_funtype], assumption+)
apply (subgoal_tac "j : i") 
	prefer 2 apply (blast intro: Ord_trans Ord_otype)
apply (subgoal_tac "converse(f) ` j : obase(M,A,r)") 
	prefer 2 
	apply (blast dest: wellordered_omap_bij [THEN bij_converse_bij, 
                                      THEN bij_is_fun, THEN apply_funtype])
apply (rule_tac x="converse(f) ` j" in bexI) 
 apply (simp add: right_inverse_bij [OF wellordered_omap_bij]) 
apply (intro predI conjI)
 apply (erule_tac b=c in trans_onD) 
 apply (rule ord_iso_converse1 [OF omap_ord_iso [of A r f i]])
apply (auto simp add: obase_def)
done

lemma (in M_ordertype) restrict_omap_ord_iso:
     "[| wellordered(M,A,r); omap(M,A,r,f); otype(M,A,r,i); 
       D \<subseteq> obase(M,A,r); M(A); M(r); M(f); M(i) |] 
      ==> restrict(f,D) \<in> (\<langle>D,r\<rangle> \<cong> \<langle>f``D, Memrel(f``D)\<rangle>)"
apply (frule ord_iso_restrict_image [OF omap_ord_iso [of A r f i]], 
       assumption+)
apply (drule ord_iso_sym [THEN subset_ord_iso_Memrel]) 
apply (blast dest: subsetD [OF omap_subset]) 
apply (drule ord_iso_sym, simp) 
done

lemma (in M_ordertype) obase_equals: 
     "[| wellordered(M,A,r); omap(M,A,r,f); otype(M,A,r,i);
       M(A); M(r); M(f); M(i) |] ==> obase(M,A,r) = A"
apply (rule equalityI, force simp add: obase_def, clarify) 
apply (unfold obase_def, simp) 
apply (frule wellordered_is_wellfounded_on, assumption)
apply (erule wellfounded_on_induct, assumption+)
 apply (frule obase_equals_separation [of A r], assumption) 
 apply (simp, clarify) 
apply (rename_tac b) 
apply (subgoal_tac "Order.pred(A,b,r) <= obase(M,A,r)") 
 apply (blast intro!: restrict_omap_ord_iso Ord_omap_image_pred)
apply (force simp add: pred_iff obase_def)  
done



text{*Main result: @{term om} gives the order-isomorphism 
      @{term "\<langle>A,r\<rangle> \<cong> \<langle>i, Memrel(i)\<rangle>"} *}
theorem (in M_ordertype) omap_ord_iso_otype:
     "[| wellordered(M,A,r); omap(M,A,r,f); otype(M,A,r,i);
       M(A); M(r); M(f); M(i) |] ==> f \<in> ord_iso(A, r, i, Memrel(i))"
apply (frule omap_ord_iso, assumption+)
apply (simp add: obase_equals)  
done 

lemma (in M_ordertype) obase_exists:
     "[| M(A); M(r) |] ==> M(obase(M,A,r))"
apply (simp add: obase_def) 
apply (insert obase_separation [of A r])
apply (simp add: separation_def)  
done

lemma (in M_ordertype) omap_exists:
     "[| M(A); M(r) |] ==> \<exists>z[M]. omap(M,A,r,z)"
apply (simp add: omap_def) 
apply (insert omap_replacement [of A r])
apply (simp add: strong_replacement_def) 
apply (drule_tac x="obase(M,A,r)" in rspec) 
 apply (simp add: obase_exists) 
apply (simp add: Memrel_closed pred_closed obase_def)
apply (erule impE) 
 apply (clarsimp simp add: univalent_def)
 apply (blast intro: Ord_iso_implies_eq ord_iso_sym ord_iso_trans, clarify)  
apply (rule_tac x=Y in rexI) 
apply (simp add: Memrel_closed pred_closed obase_def, blast, assumption)
done

declare rall_simps [simp] rex_simps [simp]

lemma (in M_ordertype) otype_exists:
     "[| wellordered(M,A,r); M(A); M(r) |] ==> \<exists>i[M]. otype(M,A,r,i)"
apply (insert omap_exists [of A r])  
apply (simp add: otype_def, safe)
apply (rule_tac x="range(x)" in rexI) 
apply blast+
done

lemma (in M_ordertype) ordertype_exists:
     "[| wellordered(M,A,r); M(A); M(r) |]
      ==> \<exists>f[M]. (\<exists>i[M]. Ord(i) & f \<in> ord_iso(A, r, i, Memrel(i)))"
apply (insert obase_exists [of A r] omap_exists [of A r] otype_exists [of A r], simp, clarify)
apply (rename_tac i) 
apply (subgoal_tac "Ord(i)", blast intro: omap_ord_iso_otype)
apply (rule Ord_otype) 
    apply (force simp add: otype_def range_closed) 
   apply (simp_all add: wellordered_is_trans_on) 
done


lemma (in M_ordertype) relativized_imp_well_ord: 
     "[| wellordered(M,A,r); M(A); M(r) |] ==> well_ord(A,r)" 
apply (insert ordertype_exists [of A r], simp)
apply (blast intro: well_ord_ord_iso well_ord_Memrel)  
done

subsection {*Kunen's theorem 5.4, page 127*}

text{*(a) The notion of Wellordering is absolute*}
theorem (in M_ordertype) well_ord_abs [simp]: 
     "[| M(A); M(r) |] ==> wellordered(M,A,r) <-> well_ord(A,r)" 
by (blast intro: well_ord_imp_relativized relativized_imp_well_ord)  


text{*(b) Order types are absolute*}
theorem (in M_ordertype) 
     "[| wellordered(M,A,r); f \<in> ord_iso(A, r, i, Memrel(i));
       M(A); M(r); M(f); M(i); Ord(i) |] ==> i = ordertype(A,r)"
by (blast intro: Ord_ordertype relativized_imp_well_ord ordertype_ord_iso
                 Ord_iso_implies_eq ord_iso_sym ord_iso_trans)


subsection{*Ordinal Arithmetic: Two Examples of Recursion*}

text{*Note: the remainder of this theory is not needed elsewhere.*}

subsubsection{*Ordinal Addition*}

(*FIXME: update to use new techniques!!*)
constdefs
 (*This expresses ordinal addition in the language of ZF.  It also 
   provides an abbreviation that can be used in the instance of strong
   replacement below.  Here j is used to define the relation, namely
   Memrel(succ(j)), while x determines the domain of f.*)
 is_oadd_fun :: "[i=>o,i,i,i,i] => o"
    "is_oadd_fun(M,i,j,x,f) == 
       (\<forall>sj msj. M(sj) --> M(msj) --> 
                 successor(M,j,sj) --> membership(M,sj,msj) --> 
	         M_is_recfun(M, 
		     %x g y. \<exists>gx[M]. image(M,g,x,gx) & union(M,i,gx,y),
		     msj, x, f))"

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


locale M_ord_arith = M_ordertype +
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
             relation2_def is_recfun_abs [of "%x g. i Un g``x"]
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
apply (simp add: is_oadd_fun_def relation2_def
                 is_recfun_abs [of "%x g. i Un g``x"])  
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

lemma (in M_ord_arith) Ord_oadd_abs:
    "[| M(i); M(j); M(k); Ord(i); Ord(j) |] ==> is_oadd(M,i,j,k) <-> k = i++j"
apply (simp add: is_oadd_def is_oadd_fun_iff_oadd)
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


subsubsection{*Ordinal Multiplication*}

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

lemma (in M_ord_arith) omult_abs:
    "[| M(i); M(j); M(k); Ord(i); Ord(j) |] ==> is_omult(M,i,j,k) <-> k = i**j"
apply (simp add: is_omult_def is_omult_fun_eq_omult)
apply (frule exists_omult_fun [of j i], blast+)
done



subsection {*Absoluteness of Well-Founded Relations*}

text{*Relativized to @{term M}: Every well-founded relation is a subset of some
inverse image of an ordinal.  Key step is the construction (in @{term M}) of a
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
apply (simp add: relation2_def is_recfun_abs [of "%x. range"])
done

lemma (in M_wfrank) wfrank_strong_replacement':
     "M(r) ==>
      strong_replacement(M, \<lambda>x z. \<exists>y[M]. \<exists>f[M]. 
		  pair(M,x,y,z) & is_recfun(r^+, x, %x f. range(f), f) &
		  y = range(f))"
apply (insert wfrank_strong_replacement [of r])
apply (simp add: relation2_def is_recfun_abs [of "%x. range"])
done

lemma (in M_wfrank) Ord_wfrank_separation':
     "M(r) ==>
      separation (M, \<lambda>x. 
         ~ (\<forall>f[M]. is_recfun(r^+, x, \<lambda>x. range, f) --> Ord(range(f))))" 
apply (insert Ord_wfrank_separation [of r])
apply (simp add: relation2_def is_recfun_abs [of "%x. range"])
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


theorem (in M_wfrank) wf_abs:
     "[|relation(r); M(r)|] ==> wellfounded(M,r) <-> wf(r)"
by (blast intro: wellfounded_imp_wf wf_imp_relativized)

theorem (in M_wfrank) wf_on_abs:
     "[|relation(r); M(r); M(A)|] ==> wellfounded_on(M,A,r) <-> wf[A](r)"
by (blast intro: wellfounded_on_imp_wf_on wf_on_imp_relativized)

end