(*  Title:      ZF/WF.thy
    Author:     Tobias Nipkow and Lawrence C Paulson
    Copyright   1994  University of Cambridge

Derived first for transitive relations, and finally for arbitrary WF relations
via wf_trancl and trans_trancl.

It is difficult to derive this general case directly, using r^+ instead of
r.  In is_recfun, the two occurrences of the relation must have the same
form.  Inserting r^+ in the_recfun or wftrec yields a recursion rule with
r^+ -`` {a} instead of r-``{a}.  This recursion rule is stronger in
principle, but harder to use, especially to prove wfrec_eclose_eq in
epsilon.ML.  Expanding out the definition of wftrec in wfrec would yield
a mess.
*)

header{*Well-Founded Recursion*}

theory WF imports Trancl begin

definition
  wf           :: "i=>o"  where
    (*r is a well-founded relation*)
    "wf(r) == \<forall>Z. Z=0 | (\<exists>x\<in>Z. \<forall>y. <y,x>:r \<longrightarrow> ~ y:Z)"

definition
  wf_on        :: "[i,i]=>o"                      ("wf[_]'(_')")  where
    (*r is well-founded on A*)
    "wf_on(A,r) == wf(r \<inter> A*A)"

definition
  is_recfun    :: "[i, i, [i,i]=>i, i] =>o"  where
    "is_recfun(r,a,H,f) == (f = (\<lambda>x\<in>r-``{a}. H(x, restrict(f, r-``{x}))))"

definition
  the_recfun   :: "[i, i, [i,i]=>i] =>i"  where
    "the_recfun(r,a,H) == (THE f. is_recfun(r,a,H,f))"

definition
  wftrec :: "[i, i, [i,i]=>i] =>i"  where
    "wftrec(r,a,H) == H(a, the_recfun(r,a,H))"

definition
  wfrec :: "[i, i, [i,i]=>i] =>i"  where
    (*public version.  Does not require r to be transitive*)
    "wfrec(r,a,H) == wftrec(r^+, a, %x f. H(x, restrict(f,r-``{x})))"

definition
  wfrec_on     :: "[i, i, i, [i,i]=>i] =>i"       ("wfrec[_]'(_,_,_')")  where
    "wfrec[A](r,a,H) == wfrec(r \<inter> A*A, a, H)"


subsection{*Well-Founded Relations*}

subsubsection{*Equivalences between @{term wf} and @{term wf_on}*}

lemma wf_imp_wf_on: "wf(r) ==> wf[A](r)"
by (unfold wf_def wf_on_def, force)

lemma wf_on_imp_wf: "[|wf[A](r); r \<subseteq> A*A|] ==> wf(r)";
by (simp add: wf_on_def subset_Int_iff)

lemma wf_on_field_imp_wf: "wf[field(r)](r) ==> wf(r)"
by (unfold wf_def wf_on_def, fast)

lemma wf_iff_wf_on_field: "wf(r) <-> wf[field(r)](r)"
by (blast intro: wf_imp_wf_on wf_on_field_imp_wf)

lemma wf_on_subset_A: "[| wf[A](r);  B<=A |] ==> wf[B](r)"
by (unfold wf_on_def wf_def, fast)

lemma wf_on_subset_r: "[| wf[A](r); s<=r |] ==> wf[A](s)"
by (unfold wf_on_def wf_def, fast)

lemma wf_subset: "[|wf(s); r<=s|] ==> wf(r)"
by (simp add: wf_def, fast)

subsubsection{*Introduction Rules for @{term wf_on}*}

text{*If every non-empty subset of @{term A} has an @{term r}-minimal element
   then we have @{term "wf[A](r)"}.*}
lemma wf_onI:
 assumes prem: "!!Z u. [| Z<=A;  u:Z;  \<forall>x\<in>Z. \<exists>y\<in>Z. <y,x>:r |] ==> False"
 shows         "wf[A](r)"
apply (unfold wf_on_def wf_def)
apply (rule equals0I [THEN disjCI, THEN allI])
apply (rule_tac Z = Z in prem, blast+)
done

text{*If @{term r} allows well-founded induction over @{term A}
   then we have @{term "wf[A](r)"}.   Premise is equivalent to
  @{prop "!!B. \<forall>x\<in>A. (\<forall>y. <y,x>: r \<longrightarrow> y:B) \<longrightarrow> x:B ==> A<=B"} *}
lemma wf_onI2:
 assumes prem: "!!y B. [| \<forall>x\<in>A. (\<forall>y\<in>A. <y,x>:r \<longrightarrow> y:B) \<longrightarrow> x:B;   y:A |]
                       ==> y:B"
 shows         "wf[A](r)"
apply (rule wf_onI)
apply (rule_tac c=u in prem [THEN DiffE])
  prefer 3 apply blast
 apply fast+
done


subsubsection{*Well-founded Induction*}

text{*Consider the least @{term z} in @{term "domain(r)"} such that
  @{term "P(z)"} does not hold...*}
lemma wf_induct [induct set: wf]:
    "[| wf(r);
        !!x.[| \<forall>y. <y,x>: r \<longrightarrow> P(y) |] ==> P(x) |]
     ==> P(a)"
apply (unfold wf_def)
apply (erule_tac x = "{z \<in> domain(r). ~ P(z)}" in allE)
apply blast
done

lemmas wf_induct_rule = wf_induct [rule_format, induct set: wf]

text{*The form of this rule is designed to match @{text wfI}*}
lemma wf_induct2:
    "[| wf(r);  a:A;  field(r)<=A;
        !!x.[| x: A;  \<forall>y. <y,x>: r \<longrightarrow> P(y) |] ==> P(x) |]
     ==>  P(a)"
apply (erule_tac P="a:A" in rev_mp)
apply (erule_tac a=a in wf_induct, blast)
done

lemma field_Int_square: "field(r \<inter> A*A) \<subseteq> A"
by blast

lemma wf_on_induct [consumes 2, induct set: wf_on]:
    "[| wf[A](r);  a:A;
        !!x.[| x: A;  \<forall>y\<in>A. <y,x>: r \<longrightarrow> P(y) |] ==> P(x)
     |]  ==>  P(a)"
apply (unfold wf_on_def)
apply (erule wf_induct2, assumption)
apply (rule field_Int_square, blast)
done

lemmas wf_on_induct_rule =
  wf_on_induct [rule_format, consumes 2, induct set: wf_on]


text{*If @{term r} allows well-founded induction
   then we have @{term "wf(r)"}.*}
lemma wfI:
    "[| field(r)<=A;
        !!y B. [| \<forall>x\<in>A. (\<forall>y\<in>A. <y,x>:r \<longrightarrow> y:B) \<longrightarrow> x:B;  y:A|]
               ==> y:B |]
     ==>  wf(r)"
apply (rule wf_on_subset_A [THEN wf_on_field_imp_wf])
apply (rule wf_onI2)
 prefer 2 apply blast
apply blast
done


subsection{*Basic Properties of Well-Founded Relations*}

lemma wf_not_refl: "wf(r) ==> <a,a> \<notin> r"
by (erule_tac a=a in wf_induct, blast)

lemma wf_not_sym [rule_format]: "wf(r) ==> \<forall>x. <a,x>:r \<longrightarrow> <x,a> \<notin> r"
by (erule_tac a=a in wf_induct, blast)

(* @{term"[| wf(r);  <a,x> \<in> r;  ~P ==> <x,a> \<in> r |] ==> P"} *)
lemmas wf_asym = wf_not_sym [THEN swap]

lemma wf_on_not_refl: "[| wf[A](r); a: A |] ==> <a,a> \<notin> r"
by (erule_tac a=a in wf_on_induct, assumption, blast)

lemma wf_on_not_sym [rule_format]:
     "[| wf[A](r);  a:A |] ==> \<forall>b\<in>A. <a,b>:r \<longrightarrow> <b,a>\<notin>r"
apply (erule_tac a=a in wf_on_induct, assumption, blast)
done

lemma wf_on_asym:
     "[| wf[A](r);  ~Z ==> <a,b> \<in> r;
         <b,a> \<notin> r ==> Z; ~Z ==> a \<in> A; ~Z ==> b \<in> A |] ==> Z"
by (blast dest: wf_on_not_sym)


(*Needed to prove well_ordI.  Could also reason that wf[A](r) means
  wf(r \<inter> A*A);  thus wf( (r \<inter> A*A)^+ ) and use wf_not_refl *)
lemma wf_on_chain3:
     "[| wf[A](r); <a,b>:r; <b,c>:r; <c,a>:r; a:A; b:A; c:A |] ==> P"
apply (subgoal_tac "\<forall>y\<in>A. \<forall>z\<in>A. <a,y>:r \<longrightarrow> <y,z>:r \<longrightarrow> <z,a>:r \<longrightarrow> P",
       blast)
apply (erule_tac a=a in wf_on_induct, assumption, blast)
done



text{*transitive closure of a WF relation is WF provided
  @{term A} is downward closed*}
lemma wf_on_trancl:
    "[| wf[A](r);  r-``A \<subseteq> A |] ==> wf[A](r^+)"
apply (rule wf_onI2)
apply (frule bspec [THEN mp], assumption+)
apply (erule_tac a = y in wf_on_induct, assumption)
apply (blast elim: tranclE, blast)
done

lemma wf_trancl: "wf(r) ==> wf(r^+)"
apply (simp add: wf_iff_wf_on_field)
apply (rule wf_on_subset_A)
 apply (erule wf_on_trancl)
 apply blast
apply (rule trancl_type [THEN field_rel_subset])
done


text{*@{term "r-``{a}"} is the set of everything under @{term a} in @{term r}*}

lemmas underI = vimage_singleton_iff [THEN iffD2]
lemmas underD = vimage_singleton_iff [THEN iffD1]


subsection{*The Predicate @{term is_recfun}*}

lemma is_recfun_type: "is_recfun(r,a,H,f) ==> f: r-``{a} -> range(f)"
apply (unfold is_recfun_def)
apply (erule ssubst)
apply (rule lamI [THEN rangeI, THEN lam_type], assumption)
done

lemmas is_recfun_imp_function = is_recfun_type [THEN fun_is_function]

lemma apply_recfun:
    "[| is_recfun(r,a,H,f); <x,a>:r |] ==> f`x = H(x, restrict(f,r-``{x}))"
apply (unfold is_recfun_def)
  txt{*replace f only on the left-hand side*}
apply (erule_tac P = "%x.?t(x) = ?u" in ssubst)
apply (simp add: underI)
done

lemma is_recfun_equal [rule_format]:
     "[| wf(r);  trans(r);  is_recfun(r,a,H,f);  is_recfun(r,b,H,g) |]
      ==> <x,a>:r \<longrightarrow> <x,b>:r \<longrightarrow> f`x=g`x"
apply (frule_tac f = f in is_recfun_type)
apply (frule_tac f = g in is_recfun_type)
apply (simp add: is_recfun_def)
apply (erule_tac a=x in wf_induct)
apply (intro impI)
apply (elim ssubst)
apply (simp (no_asm_simp) add: vimage_singleton_iff restrict_def)
apply (rule_tac t = "%z. H (?x,z) " in subst_context)
apply (subgoal_tac "\<forall>y\<in>r-``{x}. \<forall>z. <y,z>:f <-> <y,z>:g")
 apply (blast dest: transD)
apply (simp add: apply_iff)
apply (blast dest: transD intro: sym)
done

lemma is_recfun_cut:
     "[| wf(r);  trans(r);
         is_recfun(r,a,H,f);  is_recfun(r,b,H,g);  <b,a>:r |]
      ==> restrict(f, r-``{b}) = g"
apply (frule_tac f = f in is_recfun_type)
apply (rule fun_extension)
  apply (blast dest: transD intro: restrict_type2)
 apply (erule is_recfun_type, simp)
apply (blast dest: transD intro: is_recfun_equal)
done

subsection{*Recursion: Main Existence Lemma*}

lemma is_recfun_functional:
     "[| wf(r); trans(r); is_recfun(r,a,H,f); is_recfun(r,a,H,g) |]  ==>  f=g"
by (blast intro: fun_extension is_recfun_type is_recfun_equal)

lemma the_recfun_eq:
    "[| is_recfun(r,a,H,f);  wf(r);  trans(r) |] ==> the_recfun(r,a,H) = f"
apply (unfold the_recfun_def)
apply (blast intro: is_recfun_functional)
done

(*If some f satisfies is_recfun(r,a,H,-) then so does the_recfun(r,a,H) *)
lemma is_the_recfun:
    "[| is_recfun(r,a,H,f);  wf(r);  trans(r) |]
     ==> is_recfun(r, a, H, the_recfun(r,a,H))"
by (simp add: the_recfun_eq)

lemma unfold_the_recfun:
     "[| wf(r);  trans(r) |] ==> is_recfun(r, a, H, the_recfun(r,a,H))"
apply (rule_tac a=a in wf_induct, assumption)
apply (rename_tac a1)
apply (rule_tac f = "\<lambda>y\<in>r-``{a1}. wftrec (r,y,H)" in is_the_recfun)
  apply typecheck
apply (unfold is_recfun_def wftrec_def)
  --{*Applying the substitution: must keep the quantified assumption!*}
apply (rule lam_cong [OF refl])
apply (drule underD)
apply (fold is_recfun_def)
apply (rule_tac t = "%z. H(?x,z)" in subst_context)
apply (rule fun_extension)
  apply (blast intro: is_recfun_type)
 apply (rule lam_type [THEN restrict_type2])
  apply blast
 apply (blast dest: transD)
apply (frule spec [THEN mp], assumption)
apply (subgoal_tac "<xa,a1> \<in> r")
 apply (drule_tac x1 = xa in spec [THEN mp], assumption)
apply (simp add: vimage_singleton_iff
                 apply_recfun is_recfun_cut)
apply (blast dest: transD)
done


subsection{*Unfolding @{term "wftrec(r,a,H)"}*}

lemma the_recfun_cut:
     "[| wf(r);  trans(r);  <b,a>:r |]
      ==> restrict(the_recfun(r,a,H), r-``{b}) = the_recfun(r,b,H)"
by (blast intro: is_recfun_cut unfold_the_recfun)

(*NOT SUITABLE FOR REWRITING: it is recursive!*)
lemma wftrec:
    "[| wf(r);  trans(r) |] ==>
          wftrec(r,a,H) = H(a, \<lambda>x\<in>r-``{a}. wftrec(r,x,H))"
apply (unfold wftrec_def)
apply (subst unfold_the_recfun [unfolded is_recfun_def])
apply (simp_all add: vimage_singleton_iff [THEN iff_sym] the_recfun_cut)
done


subsubsection{*Removal of the Premise @{term "trans(r)"}*}

(*NOT SUITABLE FOR REWRITING: it is recursive!*)
lemma wfrec:
    "wf(r) ==> wfrec(r,a,H) = H(a, \<lambda>x\<in>r-``{a}. wfrec(r,x,H))"
apply (unfold wfrec_def)
apply (erule wf_trancl [THEN wftrec, THEN ssubst])
 apply (rule trans_trancl)
apply (rule vimage_pair_mono [THEN restrict_lam_eq, THEN subst_context])
 apply (erule r_into_trancl)
apply (rule subset_refl)
done

(*This form avoids giant explosions in proofs.  NOTE USE OF == *)
lemma def_wfrec:
    "[| !!x. h(x)==wfrec(r,x,H);  wf(r) |] ==>
     h(a) = H(a, \<lambda>x\<in>r-``{a}. h(x))"
apply simp
apply (elim wfrec)
done

lemma wfrec_type:
    "[| wf(r);  a:A;  field(r)<=A;
        !!x u. [| x: A;  u: Pi(r-``{x}, B) |] ==> H(x,u) \<in> B(x)
     |] ==> wfrec(r,a,H) \<in> B(a)"
apply (rule_tac a = a in wf_induct2, assumption+)
apply (subst wfrec, assumption)
apply (simp add: lam_type underD)
done


lemma wfrec_on:
 "[| wf[A](r);  a: A |] ==>
         wfrec[A](r,a,H) = H(a, \<lambda>x\<in>(r-``{a}) \<inter> A. wfrec[A](r,x,H))"
apply (unfold wf_on_def wfrec_on_def)
apply (erule wfrec [THEN trans])
apply (simp add: vimage_Int_square cons_subset_iff)
done

text{*Minimal-element characterization of well-foundedness*}
lemma wf_eq_minimal:
     "wf(r) <-> (\<forall>Q x. x:Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. <y,z>:r \<longrightarrow> y\<notin>Q))"
by (unfold wf_def, blast)

end
