header {*Relativized Wellorderings*}

theory Wellorderings = Relative:

text{*We define functions analogous to @{term ordermap} @{term ordertype} 
      but without using recursion.  Instead, there is a direct appeal
      to Replacement.  This will be the basis for a version relativized
      to some class @{text M}.  The main result is Theorem I 7.6 in Kunen,
      page 17.*}


subsection{*Wellorderings*}

constdefs
  irreflexive :: "[i=>o,i,i]=>o"
    "irreflexive(M,A,r) == \<forall>x\<in>A. M(x) --> <x,x> \<notin> r"
  
  transitive_rel :: "[i=>o,i,i]=>o"
    "transitive_rel(M,A,r) == 
	\<forall>x\<in>A. M(x) --> (\<forall>y\<in>A. M(y) --> (\<forall>z\<in>A. M(z) --> 
                          <x,y>\<in>r --> <y,z>\<in>r --> <x,z>\<in>r))"

  linear_rel :: "[i=>o,i,i]=>o"
    "linear_rel(M,A,r) == 
	\<forall>x\<in>A. M(x) --> (\<forall>y\<in>A. M(y) --> <x,y>\<in>r | x=y | <y,x>\<in>r)"

  wellfounded :: "[i=>o,i]=>o"
    --{*EVERY non-empty set has an @{text r}-minimal element*}
    "wellfounded(M,r) == 
	\<forall>x. M(x) --> ~ empty(M,x) 
                 --> (\<exists>y\<in>x. M(y) & ~(\<exists>z\<in>x. M(z) & <z,y> \<in> r))"
  wellfounded_on :: "[i=>o,i,i]=>o"
    --{*every non-empty SUBSET OF @{text A} has an @{text r}-minimal element*}
    "wellfounded_on(M,A,r) == 
	\<forall>x. M(x) --> ~ empty(M,x) --> subset(M,x,A)
                 --> (\<exists>y\<in>x. M(y) & ~(\<exists>z\<in>x. M(z) & <z,y> \<in> r))"

  wellordered :: "[i=>o,i,i]=>o"
    --{*every non-empty subset of @{text A} has an @{text r}-minimal element*}
    "wellordered(M,A,r) == 
	transitive_rel(M,A,r) & linear_rel(M,A,r) & wellfounded_on(M,A,r)"


subsubsection {*Trivial absoluteness proofs*}

lemma (in M_axioms) irreflexive_abs [simp]: 
     "M(A) ==> irreflexive(M,A,r) <-> irrefl(A,r)"
by (simp add: irreflexive_def irrefl_def)

lemma (in M_axioms) transitive_rel_abs [simp]: 
     "M(A) ==> transitive_rel(M,A,r) <-> trans[A](r)"
by (simp add: transitive_rel_def trans_on_def)

lemma (in M_axioms) linear_rel_abs [simp]: 
     "M(A) ==> linear_rel(M,A,r) <-> linear(A,r)"
by (simp add: linear_rel_def linear_def)

lemma (in M_axioms) wellordered_is_trans_on: 
    "[| wellordered(M,A,r); M(A) |] ==> trans[A](r)"
by (auto simp add: wellordered_def )

lemma (in M_axioms) wellordered_is_linear: 
    "[| wellordered(M,A,r); M(A) |] ==> linear(A,r)"
by (auto simp add: wellordered_def )

lemma (in M_axioms) wellordered_is_wellfounded_on: 
    "[| wellordered(M,A,r); M(A) |] ==> wellfounded_on(M,A,r)"
by (auto simp add: wellordered_def )

lemma (in M_axioms) wellfounded_imp_wellfounded_on: 
    "[| wellfounded(M,r); M(A) |] ==> wellfounded_on(M,A,r)"
by (auto simp add: wellfounded_def wellfounded_on_def)

lemma (in M_axioms) wellfounded_on_subset_A:
     "[| wellfounded_on(M,A,r);  B<=A |] ==> wellfounded_on(M,B,r)"
by (simp add: wellfounded_on_def, blast)


subsubsection {*Well-founded relations*}

lemma  (in M_axioms) wellfounded_on_iff_wellfounded:
     "wellfounded_on(M,A,r) <-> wellfounded(M, r \<inter> A*A)"
apply (simp add: wellfounded_on_def wellfounded_def, safe)
 apply blast 
apply (drule_tac x=x in spec, blast) 
done

lemma (in M_axioms) wellfounded_on_imp_wellfounded:
     "[|wellfounded_on(M,A,r); r \<subseteq> A*A|] ==> wellfounded(M,r)"
by (simp add: wellfounded_on_iff_wellfounded subset_Int_iff)

lemma (in M_axioms) wellfounded_on_field_imp_wellfounded:
     "wellfounded_on(M, field(r), r) ==> wellfounded(M,r)"
by (simp add: wellfounded_def wellfounded_on_iff_wellfounded, fast)

lemma (in M_axioms) wellfounded_iff_wellfounded_on_field:
     "M(r) ==> wellfounded(M,r) <-> wellfounded_on(M, field(r), r)"
by (blast intro: wellfounded_imp_wellfounded_on
                 wellfounded_on_field_imp_wellfounded)

(*Consider the least z in domain(r) such that P(z) does not hold...*)
lemma (in M_axioms) wellfounded_induct: 
     "[| wellfounded(M,r); M(a); M(r); separation(M, \<lambda>x. ~P(x));  
         \<forall>x. M(x) & (\<forall>y. <y,x> \<in> r --> P(y)) --> P(x) |]
      ==> P(a)";
apply (simp (no_asm_use) add: wellfounded_def)
apply (drule_tac x="{z \<in> domain(r). ~P(z)}" in spec)
apply (blast dest: transM)
done

lemma (in M_axioms) wellfounded_on_induct: 
     "[| a\<in>A;  wellfounded_on(M,A,r);  M(A);  
       separation(M, \<lambda>x. x\<in>A --> ~P(x));  
       \<forall>x\<in>A. M(x) & (\<forall>y\<in>A. <y,x> \<in> r --> P(y)) --> P(x) |]
      ==> P(a)";
apply (simp (no_asm_use) add: wellfounded_on_def)
apply (drule_tac x="{z\<in>A. z\<in>A --> ~P(z)}" in spec)
apply (blast intro: transM) 
done

text{*The assumption @{term "r \<subseteq> A*A"} justifies strengthening the induction
      hypothesis by removing the restriction to @{term A}.*}
lemma (in M_axioms) wellfounded_on_induct2: 
     "[| a\<in>A;  wellfounded_on(M,A,r);  M(A);  r \<subseteq> A*A;  
       separation(M, \<lambda>x. x\<in>A --> ~P(x));  
       \<forall>x\<in>A. M(x) & (\<forall>y. <y,x> \<in> r --> P(y)) --> P(x) |]
      ==> P(a)";
by (rule wellfounded_on_induct, assumption+, blast)


subsubsection {*Kunen's lemma IV 3.14, page 123*}

lemma (in M_axioms) linear_imp_relativized: 
     "linear(A,r) ==> linear_rel(M,A,r)" 
by (simp add: linear_def linear_rel_def) 

lemma (in M_axioms) trans_on_imp_relativized: 
     "trans[A](r) ==> transitive_rel(M,A,r)" 
by (unfold transitive_rel_def trans_on_def, blast) 

lemma (in M_axioms) wf_on_imp_relativized: 
     "wf[A](r) ==> wellfounded_on(M,A,r)" 
apply (simp add: wellfounded_on_def wf_def wf_on_def, clarify) 
apply (drule_tac x="x" in spec, blast) 
done

lemma (in M_axioms) wf_imp_relativized: 
     "wf(r) ==> wellfounded(M,r)" 
apply (simp add: wellfounded_def wf_def, clarify) 
apply (drule_tac x="x" in spec, blast) 
done

lemma (in M_axioms) well_ord_imp_relativized: 
     "well_ord(A,r) ==> wellordered(M,A,r)" 
by (simp add: wellordered_def well_ord_def tot_ord_def part_ord_def
       linear_imp_relativized trans_on_imp_relativized wf_on_imp_relativized)


subsection{* Relativized versions of order-isomorphisms and order types *}

lemma (in M_axioms) order_isomorphism_abs [simp]: 
     "[| M(A); M(B); M(f) |] 
      ==> order_isomorphism(M,A,r,B,s,f) <-> f \<in> ord_iso(A,r,B,s)"
by (simp add: typed_apply_abs [OF bij_is_fun] apply_closed 
              order_isomorphism_def ord_iso_def)


lemma (in M_axioms) pred_set_abs [simp]: 
     "[| M(r); M(B) |] ==> pred_set(M,A,x,r,B) <-> B = Order.pred(A,x,r)"
apply (simp add: pred_set_def Order.pred_def)
apply (blast dest: transM) 
done

lemma (in M_axioms) pred_closed [intro,simp]: 
     "[| M(A); M(r); M(x) |] ==> M(Order.pred(A,x,r))"
apply (simp add: Order.pred_def) 
apply (insert pred_separation [of r x], simp) 
done

lemma (in M_axioms) membership_abs [simp]: 
     "[| M(r); M(A) |] ==> membership(M,A,r) <-> r = Memrel(A)"
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

lemma (in M_axioms) M_Memrel_iff:
     "M(A) ==> 
      Memrel(A) = {z \<in> A*A. \<exists>x. M(x) \<and> (\<exists>y. M(y) \<and> z = \<langle>x,y\<rangle> \<and> x \<in> y)}"
apply (simp add: Memrel_def) 
apply (blast dest: transM)
done 

lemma (in M_axioms) Memrel_closed [intro,simp]: 
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

text{*Inductive argument for Kunen's Lemma 6.1, etc.
      Simple proof from Halmos, page 72*}
lemma  (in M_axioms) wellordered_iso_subset_lemma: 
     "[| wellordered(M,A,r);  f \<in> ord_iso(A,r, A',r);  A'<= A;  y \<in> A;  
       M(A);  M(f);  M(r) |] ==> ~ <f`y, y> \<in> r"
apply (unfold wellordered_def ord_iso_def)
apply (elim conjE CollectE) 
apply (erule wellfounded_on_induct, assumption+)
 apply (insert well_ord_iso_separation [of A f r])
 apply (simp add: typed_apply_abs [OF bij_is_fun] apply_closed, clarify) 
apply (drule_tac a = x in bij_is_fun [THEN apply_type], assumption, blast)
done


text{*Kunen's Lemma 6.1: there's no order-isomorphism to an initial segment
      of a well-ordering*}
lemma (in M_axioms) wellordered_iso_predD:
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


lemma (in M_axioms) wellordered_iso_pred_eq_lemma:
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
lemma (in M_axioms) wellordered_iso_pred_eq:
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

lemma (in M_axioms) wellfounded_on_asym:
     "[| wellfounded_on(M,A,r);  <a,x>\<in>r;  a\<in>A; x\<in>A;  M(A) |] ==> <x,a>\<notin>r"
apply (simp add: wellfounded_on_def) 
apply (drule_tac x="{x,a}" in spec) 
apply (simp add: cons_closed) 
apply (blast dest: transM) 
done

lemma (in M_axioms) wellordered_asym:
     "[| wellordered(M,A,r);  <a,x>\<in>r;  a\<in>A; x\<in>A;  M(A) |] ==> <x,a>\<notin>r"
by (simp add: wellordered_def, blast dest: wellfounded_on_asym)


text{*Surely a shorter proof using lemmas in @{text Order}?
     Like well_ord_iso_preserving?*}
lemma (in M_axioms) ord_iso_pred_imp_lt:
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
       "\<exists>h. M(h) & h \<in> ord_iso(Order.pred(A,y,r), r, 
                               Order.pred(A, converse(f)`j, r), r)")
 apply (clarify, frule wellordered_iso_pred_eq, assumption+)
 apply (blast dest: wellordered_asym)  
apply (intro exI conjI) 
 prefer 2 apply (blast intro: Ord_iso_implies_eq ord_iso_sym ord_iso_trans)+
done


lemma ord_iso_converse1:
     "[| f: ord_iso(A,r,B,s);  <b, f`a>: s;  a:A;  b:B |] 
      ==> <converse(f) ` b, a> : r"
apply (frule ord_iso_converse, assumption+) 
apply (blast intro: ord_iso_is_bij [THEN bij_is_fun, THEN apply_funtype]) 
apply (simp add: left_inverse_bij [OF ord_iso_is_bij])
done


subsection {* Order Types: A Direct Construction by Replacement*}

text{*This follows Kunen's Theorem I 7.6, page 17.*}

constdefs
  
  obase :: "[i=>o,i,i,i] => o"
       --{*the domain of @{text om}, eventually shown to equal @{text A}*}
   "obase(M,A,r,z) == 
	\<forall>a[M]. 
         a \<in> z <-> 
          (a\<in>A & (\<exists>x g mx par. M(x) & M(g) & M(mx) & M(par) & ordinal(M,x) & 
                               membership(M,x,mx) & pred_set(M,A,a,r,par) &  
                               order_isomorphism(M,par,r,x,mx,g)))"


  omap :: "[i=>o,i,i,i] => o"  
    --{*the function that maps wosets to order types*}
   "omap(M,A,r,f) == 
	\<forall>z[M].
         z \<in> f <-> 
          (\<exists>a\<in>A. M(a) & 
           (\<exists>x g mx par. M(x) & M(g) & M(mx) & M(par) & ordinal(M,x) & 
                         pair(M,a,x,z) & membership(M,x,mx) & 
                         pred_set(M,A,a,r,par) &  
                         order_isomorphism(M,par,r,x,mx,g)))"


  otype :: "[i=>o,i,i,i] => o"  --{*the order types themselves*}
   "otype(M,A,r,i) == \<exists>f. M(f) & omap(M,A,r,f) & is_range(M,f,i)"



lemma (in M_axioms) obase_iff:
     "[| M(A); M(r); M(z) |] 
      ==> obase(M,A,r,z) <-> 
          z = {a\<in>A. \<exists>x g. M(x) & M(g) & Ord(x) & 
                          g \<in> ord_iso(Order.pred(A,a,r),r,x,Memrel(x))}"
apply (simp add: obase_def Memrel_closed pred_closed)
apply (rule iffI) 
 prefer 2 apply blast 
apply (rule equalityI) 
 apply (clarify, frule transM, assumption, rotate_tac -1, simp) 
apply (clarify, frule transM, assumption, force)
done

text{*Can also be proved with the premise @{term "M(z)"} instead of
      @{term "M(f)"}, but that version is less useful.*}
lemma (in M_axioms) omap_iff:
     "[| omap(M,A,r,f); M(A); M(r); M(f) |] 
      ==> z \<in> f <->
      (\<exists>a\<in>A. \<exists>x g. M(x) & M(g) & z = <a,x> & Ord(x) & 
                   g \<in> ord_iso(Order.pred(A,a,r),r,x,Memrel(x)))"
apply (rotate_tac 1) 
apply (simp add: omap_def Memrel_closed pred_closed) 
apply (rule iffI)
 apply (drule_tac [2] x=z in rspec)
 apply (drule_tac x=z in rspec)
 apply (blast dest: transM)+
done

lemma (in M_axioms) omap_unique:
     "[| omap(M,A,r,f); omap(M,A,r,f'); M(A); M(r); M(f); M(f') |] ==> f' = f" 
apply (rule equality_iffI) 
apply (simp add: omap_iff) 
done

lemma (in M_axioms) omap_yields_Ord:
     "[| omap(M,A,r,f); \<langle>a,x\<rangle> \<in> f; M(a); M(x) |]  ==> Ord(x)"
apply (simp add: omap_def, blast) 
done

lemma (in M_axioms) otype_iff:
     "[| otype(M,A,r,i); M(A); M(r); M(i) |] 
      ==> x \<in> i <-> 
          (\<exists>a\<in>A. \<exists>g. M(x) & M(g) & Ord(x) & 
                     g \<in> ord_iso(Order.pred(A,a,r),r,x,Memrel(x)))"
apply (simp add: otype_def, auto)
  apply (blast dest: transM)
 apply (blast dest!: omap_iff intro: transM)
apply (rename_tac a g) 
apply (rule_tac a=a in rangeI) 
apply (frule transM, assumption)
apply (simp add: omap_iff, blast)
done

lemma (in M_axioms) otype_eq_range:
     "[| omap(M,A,r,f); otype(M,A,r,i); M(A); M(r); M(f); M(i) |] ==> i = range(f)"
apply (auto simp add: otype_def omap_iff)
apply (blast dest: omap_unique) 
done


lemma (in M_axioms) Ord_otype:
     "[| otype(M,A,r,i); trans[A](r); M(A); M(r); M(i) |] ==> Ord(i)"
apply (rotate_tac 1) 
apply (rule OrdI) 
prefer 2 
    apply (simp add: Ord_def otype_def omap_def) 
    apply clarify 
    apply (frule pair_components_in_M, assumption) 
    apply blast 
apply (auto simp add: Transset_def otype_iff) 
 apply (blast intro: transM)
apply (rename_tac y a g)
apply (frule ord_iso_sym [THEN ord_iso_is_bij, THEN bij_is_fun, 
			  THEN apply_funtype],  assumption)  
apply (rule_tac x="converse(g)`y" in bexI)
 apply (frule_tac a="converse(g) ` y" in ord_iso_restrict_pred, assumption) 
apply (safe elim!: predE) 
apply (intro conjI exI) 
prefer 3
  apply (blast intro: restrict_ord_iso ord_iso_sym ltI)
 apply (blast intro: transM)
 apply (blast intro: Ord_in_Ord)
done

lemma (in M_axioms) domain_omap:
     "[| omap(M,A,r,f);  obase(M,A,r,B); M(A); M(r); M(B); M(f) |] 
      ==> domain(f) = B"
apply (rotate_tac 2) 
apply (simp add: domain_closed obase_iff) 
apply (rule equality_iffI) 
apply (simp add: domain_iff omap_iff, blast) 
done

lemma (in M_axioms) omap_subset: 
     "[| omap(M,A,r,f); obase(M,A,r,B); otype(M,A,r,i); 
       M(A); M(r); M(f); M(B); M(i) |] ==> f \<subseteq> B * i"
apply (rotate_tac 3, clarify) 
apply (simp add: omap_iff obase_iff) 
apply (force simp add: otype_iff) 
done

lemma (in M_axioms) omap_funtype: 
     "[| omap(M,A,r,f); obase(M,A,r,B); otype(M,A,r,i); 
       M(A); M(r); M(f); M(B); M(i) |] ==> f \<in> B -> i"
apply (rotate_tac 3) 
apply (simp add: domain_omap omap_subset Pi_iff function_def omap_iff) 
apply (blast intro: Ord_iso_implies_eq ord_iso_sym ord_iso_trans) 
done


lemma (in M_axioms) wellordered_omap_bij:
     "[| wellordered(M,A,r); omap(M,A,r,f); obase(M,A,r,B); otype(M,A,r,i); 
       M(A); M(r); M(f); M(B); M(i) |] ==> f \<in> bij(B,i)"
apply (insert omap_funtype [of A r f B i]) 
apply (auto simp add: bij_def inj_def) 
prefer 2  apply (blast intro: fun_is_surj dest: otype_eq_range) 
apply (frule_tac a="w" in apply_Pair, assumption) 
apply (frule_tac a="x" in apply_Pair, assumption) 
apply (simp add: omap_iff) 
apply (blast intro: wellordered_iso_pred_eq ord_iso_sym ord_iso_trans) 
done


text{*This is not the final result: we must show @{term "oB(A,r) = A"}*}
lemma (in M_axioms) omap_ord_iso:
     "[| wellordered(M,A,r); omap(M,A,r,f); obase(M,A,r,B); otype(M,A,r,i); 
       M(A); M(r); M(f); M(B); M(i) |] ==> f \<in> ord_iso(B,r,i,Memrel(i))"
apply (rule ord_isoI)
 apply (erule wellordered_omap_bij, assumption+) 
apply (insert omap_funtype [of A r f B i], simp) 
apply (frule_tac a="x" in apply_Pair, assumption) 
apply (frule_tac a="y" in apply_Pair, assumption) 
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

lemma (in M_axioms) Ord_omap_image_pred:
     "[| wellordered(M,A,r); omap(M,A,r,f); obase(M,A,r,B); otype(M,A,r,i); 
       M(A); M(r); M(f); M(B); M(i); b \<in> A |] ==> Ord(f `` Order.pred(A,b,r))"
apply (frule wellordered_is_trans_on, assumption)
apply (rule OrdI) 
	prefer 2 apply (simp add: image_iff omap_iff Ord_def, blast) 
txt{*Hard part is to show that the image is a transitive set.*}
apply (rotate_tac 3)
apply (simp add: Transset_def, clarify) 
apply (simp add: image_iff pred_iff apply_iff [OF omap_funtype [of A r f B i]])
apply (rename_tac c j, clarify)
apply (frule omap_funtype [of A r f B, THEN apply_funtype], assumption+)
apply (subgoal_tac "j : i") 
	prefer 2 apply (blast intro: Ord_trans Ord_otype)
apply (subgoal_tac "converse(f) ` j : B") 
	prefer 2 
	apply (blast dest: wellordered_omap_bij [THEN bij_converse_bij, 
                                      THEN bij_is_fun, THEN apply_funtype])
apply (rule_tac x="converse(f) ` j" in bexI) 
 apply (simp add: right_inverse_bij [OF wellordered_omap_bij]) 
apply (intro predI conjI)
 apply (erule_tac b=c in trans_onD) 
 apply (rule ord_iso_converse1 [OF omap_ord_iso [of A r f B i]])
apply (auto simp add: obase_iff)
done

lemma (in M_axioms) restrict_omap_ord_iso:
     "[| wellordered(M,A,r); omap(M,A,r,f); obase(M,A,r,B); otype(M,A,r,i); 
       D \<subseteq> B; M(A); M(r); M(f); M(B); M(i) |] 
      ==> restrict(f,D) \<in> (\<langle>D,r\<rangle> \<cong> \<langle>f``D, Memrel(f``D)\<rangle>)"
apply (frule ord_iso_restrict_image [OF omap_ord_iso [of A r f B i]], 
       assumption+)
apply (drule ord_iso_sym [THEN subset_ord_iso_Memrel]) 
apply (blast dest: subsetD [OF omap_subset]) 
apply (drule ord_iso_sym, simp) 
done

lemma (in M_axioms) obase_equals: 
     "[| wellordered(M,A,r); omap(M,A,r,f); obase(M,A,r,B); otype(M,A,r,i);
       M(A); M(r); M(f); M(B); M(i) |] ==> B = A"
apply (rotate_tac 4)
apply (rule equalityI, force simp add: obase_iff, clarify) 
apply (subst obase_iff [of A r B, THEN iffD1], assumption+, simp) 
apply (frule wellordered_is_wellfounded_on, assumption)
apply (erule wellfounded_on_induct, assumption+)
 apply (insert obase_equals_separation, simp add: Memrel_closed pred_closed, clarify) 
apply (rename_tac b) 
apply (subgoal_tac "Order.pred(A,b,r) <= B") 
 prefer 2 apply (force simp add: pred_iff obase_iff)  
apply (intro conjI exI) 
    prefer 4 apply (blast intro: restrict_omap_ord_iso) 
apply (blast intro: Ord_omap_image_pred)+
done



text{*Main result: @{term om} gives the order-isomorphism 
      @{term "\<langle>A,r\<rangle> \<cong> \<langle>i, Memrel(i)\<rangle>"} *}
theorem (in M_axioms) omap_ord_iso_otype:
     "[| wellordered(M,A,r); omap(M,A,r,f); obase(M,A,r,B); otype(M,A,r,i);
       M(A); M(r); M(f); M(B); M(i) |] ==> f \<in> ord_iso(A, r, i, Memrel(i))"
apply (frule omap_ord_iso, assumption+) 
apply (frule obase_equals, assumption+, blast) 
done 

lemma (in M_axioms) obase_exists:
     "[| M(A); M(r) |] ==> \<exists>z[M]. obase(M,A,r,z)"
apply (simp add: obase_def) 
apply (insert obase_separation [of A r])
apply (simp add: separation_def)  
done

lemma (in M_axioms) omap_exists:
     "[| M(A); M(r) |] ==> \<exists>z[M]. omap(M,A,r,z)"
apply (insert obase_exists [of A r]) 
apply (simp add: omap_def) 
apply (insert omap_replacement [of A r])
apply (simp add: strong_replacement_def, clarify) 
apply (drule_tac x=x in spec, clarify) 
apply (simp add: Memrel_closed pred_closed obase_iff)
apply (erule impE) 
 apply (clarsimp simp add: univalent_def)
 apply (blast intro: Ord_iso_implies_eq ord_iso_sym ord_iso_trans, clarify)  
apply (rule_tac x=Y in rexI) 
apply (simp add: Memrel_closed pred_closed obase_iff, blast, assumption)
done

declare rall_simps [simp] rex_simps [simp]

lemma (in M_axioms) otype_exists:
     "[| wellordered(M,A,r); M(A); M(r) |] ==> \<exists>i. M(i) & otype(M,A,r,i)"
apply (insert omap_exists [of A r])  
apply (simp add: otype_def, safe)
apply (rule_tac x="range(x)" in exI) 
apply blast 
done

theorem (in M_axioms) omap_ord_iso_otype:
     "[| wellordered(M,A,r); M(A); M(r) |]
      ==> \<exists>f. M(f) & (\<exists>i. M(i) & Ord(i) & f \<in> ord_iso(A, r, i, Memrel(i)))"
apply (insert obase_exists [of A r] omap_exists [of A r] otype_exists [of A r], simp, clarify)
apply (subgoal_tac "Ord(i)", blast intro: omap_ord_iso_otype) 
apply (rule Ord_otype) 
    apply (force simp add: otype_def range_closed) 
   apply (simp_all add: wellordered_is_trans_on) 
done

lemma (in M_axioms) ordertype_exists:
     "[| wellordered(M,A,r); M(A); M(r) |]
      ==> \<exists>f. M(f) & (\<exists>i. M(i) & Ord(i) & f \<in> ord_iso(A, r, i, Memrel(i)))"
apply (insert obase_exists [of A r] omap_exists [of A r] otype_exists [of A r], simp, clarify)
apply (subgoal_tac "Ord(i)", blast intro: omap_ord_iso_otype) 
apply (rule Ord_otype) 
    apply (force simp add: otype_def range_closed) 
   apply (simp_all add: wellordered_is_trans_on) 
done


lemma (in M_axioms) relativized_imp_well_ord: 
     "[| wellordered(M,A,r); M(A); M(r) |] ==> well_ord(A,r)" 
apply (insert ordertype_exists [of A r], simp)
apply (blast intro: well_ord_ord_iso well_ord_Memrel )  
done

subsection {*Kunen's theorem 5.4, poage 127*}

text{*(a) The notion of Wellordering is absolute*}
theorem (in M_axioms) well_ord_abs [simp]: 
     "[| M(A); M(r) |] ==> wellordered(M,A,r) <-> well_ord(A,r)" 
by (blast intro: well_ord_imp_relativized relativized_imp_well_ord)  


text{*(b) Order types are absolute*}
lemma (in M_axioms) 
     "[| wellordered(M,A,r); f \<in> ord_iso(A, r, i, Memrel(i));
       M(A); M(r); M(f); M(i); Ord(i) |] ==> i = ordertype(A,r)"
by (blast intro: Ord_ordertype relativized_imp_well_ord ordertype_ord_iso
                 Ord_iso_implies_eq ord_iso_sym ord_iso_trans)

end
