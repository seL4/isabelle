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

section\<open>Well-Founded Recursion\<close>

theory WF imports Trancl begin

definition
  wf           :: "i\<Rightarrow>o"  where
    (*r is a well-founded relation*)
    "wf(r) \<equiv> \<forall>Z. Z=0 | (\<exists>x\<in>Z. \<forall>y. \<langle>y,x\<rangle>:r \<longrightarrow> \<not> y \<in> Z)"

definition
  wf_on :: "[i,i]\<Rightarrow>o"  (\<open>(\<open>open_block notation=\<open>mixfix wf_on\<close>\<close>wf[_]'(_'))\<close>)  where
    (*r is well-founded on A*)
    "wf_on(A,r) \<equiv> wf(r \<inter> A*A)"

definition
  is_recfun    :: "[i, i, [i,i]\<Rightarrow>i, i] \<Rightarrow>o"  where
    "is_recfun(r,a,H,f) \<equiv> (f = (\<lambda>x\<in>r-``{a}. H(x, restrict(f, r-``{x}))))"

definition
  the_recfun   :: "[i, i, [i,i]\<Rightarrow>i] \<Rightarrow>i"  where
    "the_recfun(r,a,H) \<equiv> (THE f. is_recfun(r,a,H,f))"

definition
  wftrec :: "[i, i, [i,i]\<Rightarrow>i] \<Rightarrow>i"  where
    "wftrec(r,a,H) \<equiv> H(a, the_recfun(r,a,H))"

definition
  wfrec :: "[i, i, [i,i]\<Rightarrow>i] \<Rightarrow>i"  where
    (*public version.  Does not require r to be transitive*)
    "wfrec(r,a,H) \<equiv> wftrec(r^+, a, \<lambda>x f. H(x, restrict(f,r-``{x})))"

definition
  wfrec_on :: "[i, i, i, [i,i]\<Rightarrow>i] \<Rightarrow>i"  (\<open>(\<open>open_block notation=\<open>mixfix wfrec_on\<close>\<close>wfrec[_]'(_,_,_'))\<close>)
  where "wfrec[A](r,a,H) \<equiv> wfrec(r \<inter> A*A, a, H)"


subsection\<open>Well-Founded Relations\<close>

subsubsection\<open>Equivalences between \<^term>\<open>wf\<close> and \<^term>\<open>wf_on\<close>\<close>

lemma wf_imp_wf_on: "wf(r) \<Longrightarrow> wf[A](r)"
by (unfold wf_def wf_on_def, force)

lemma wf_on_imp_wf: "\<lbrakk>wf[A](r); r \<subseteq> A*A\<rbrakk> \<Longrightarrow> wf(r)"
by (simp add: wf_on_def subset_Int_iff)

lemma wf_on_field_imp_wf: "wf[field(r)](r) \<Longrightarrow> wf(r)"
by (unfold wf_def wf_on_def, fast)

lemma wf_iff_wf_on_field: "wf(r) \<longleftrightarrow> wf[field(r)](r)"
by (blast intro: wf_imp_wf_on wf_on_field_imp_wf)

lemma wf_on_subset_A: "\<lbrakk>wf[A](r);  B<=A\<rbrakk> \<Longrightarrow> wf[B](r)"
by (unfold wf_on_def wf_def, fast)

lemma wf_on_subset_r: "\<lbrakk>wf[A](r); s<=r\<rbrakk> \<Longrightarrow> wf[A](s)"
by (unfold wf_on_def wf_def, fast)

lemma wf_subset: "\<lbrakk>wf(s); r<=s\<rbrakk> \<Longrightarrow> wf(r)"
by (simp add: wf_def, fast)

subsubsection\<open>Introduction Rules for \<^term>\<open>wf_on\<close>\<close>

text\<open>If every non-empty subset of \<^term>\<open>A\<close> has an \<^term>\<open>r\<close>-minimal element
   then we have \<^term>\<open>wf[A](r)\<close>.\<close>
lemma wf_onI:
 assumes prem: "\<And>Z u. \<lbrakk>Z<=A;  u \<in> Z;  \<forall>x\<in>Z. \<exists>y\<in>Z. \<langle>y,x\<rangle>:r\<rbrakk> \<Longrightarrow> False"
 shows         "wf[A](r)"
  unfolding wf_on_def wf_def
apply (rule equals0I [THEN disjCI, THEN allI])
apply (rule_tac Z = Z in prem, blast+)
done

text\<open>If \<^term>\<open>r\<close> allows well-founded induction over \<^term>\<open>A\<close>
   then we have \<^term>\<open>wf[A](r)\<close>.   Premise is equivalent to
  \<^prop>\<open>\<And>B. \<forall>x\<in>A. (\<forall>y. \<langle>y,x\<rangle>: r \<longrightarrow> y \<in> B) \<longrightarrow> x \<in> B \<Longrightarrow> A<=B\<close>\<close>
lemma wf_onI2:
 assumes prem: "\<And>y B. \<lbrakk>\<forall>x\<in>A. (\<forall>y\<in>A. \<langle>y,x\<rangle>:r \<longrightarrow> y \<in> B) \<longrightarrow> x \<in> B;   y \<in> A\<rbrakk>
                       \<Longrightarrow> y \<in> B"
 shows         "wf[A](r)"
apply (rule wf_onI)
apply (rule_tac c=u in prem [THEN DiffE])
  prefer 3 apply blast
 apply fast+
done


subsubsection\<open>Well-founded Induction\<close>

text\<open>Consider the least \<^term>\<open>z\<close> in \<^term>\<open>domain(r)\<close> such that
  \<^term>\<open>P(z)\<close> does not hold...\<close>
lemma wf_induct_raw:
    "\<lbrakk>wf(r);
        \<And>x.\<lbrakk>\<forall>y. \<langle>y,x\<rangle>: r \<longrightarrow> P(y)\<rbrakk> \<Longrightarrow> P(x)\<rbrakk>
     \<Longrightarrow> P(a)"
  unfolding wf_def
apply (erule_tac x = "{z \<in> domain(r). \<not> P(z)}" in allE)
apply blast
done

lemmas wf_induct = wf_induct_raw [rule_format, consumes 1, case_names step, induct set: wf]

text\<open>The form of this rule is designed to match \<open>wfI\<close>\<close>
lemma wf_induct2:
    "\<lbrakk>wf(r);  a \<in> A;  field(r)<=A;
        \<And>x.\<lbrakk>x \<in> A;  \<forall>y. \<langle>y,x\<rangle>: r \<longrightarrow> P(y)\<rbrakk> \<Longrightarrow> P(x)\<rbrakk>
     \<Longrightarrow>  P(a)"
apply (erule_tac P="a \<in> A" in rev_mp)
apply (erule_tac a=a in wf_induct, blast)
done

lemma field_Int_square: "field(r \<inter> A*A) \<subseteq> A"
by blast

lemma wf_on_induct_raw [consumes 2, induct set: wf_on]:
    "\<lbrakk>wf[A](r);  a \<in> A;
        \<And>x.\<lbrakk>x \<in> A;  \<forall>y\<in>A. \<langle>y,x\<rangle>: r \<longrightarrow> P(y)\<rbrakk> \<Longrightarrow> P(x)
\<rbrakk>  \<Longrightarrow>  P(a)"
  unfolding wf_on_def
apply (erule wf_induct2, assumption)
apply (rule field_Int_square, blast)
done

lemma wf_on_induct [consumes 2, case_names step, induct set: wf_on]:
  "wf[A](r) \<Longrightarrow> a \<in> A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> (\<And>y. y \<in> A \<Longrightarrow> \<langle>y, x\<rangle> \<in> r \<Longrightarrow> P(y)) \<Longrightarrow> P(x)) \<Longrightarrow> P(a)"
  using wf_on_induct_raw [of A r a P] by simp

text\<open>If \<^term>\<open>r\<close> allows well-founded induction
   then we have \<^term>\<open>wf(r)\<close>.\<close>
lemma wfI:
    "\<lbrakk>field(r)<=A;
        \<And>y B. \<lbrakk>\<forall>x\<in>A. (\<forall>y\<in>A. \<langle>y,x\<rangle>:r \<longrightarrow> y \<in> B) \<longrightarrow> x \<in> B;  y \<in> A\<rbrakk>
               \<Longrightarrow> y \<in> B\<rbrakk>
     \<Longrightarrow>  wf(r)"
apply (rule wf_on_subset_A [THEN wf_on_field_imp_wf])
apply (rule wf_onI2)
 prefer 2 apply blast
apply blast
done


subsection\<open>Basic Properties of Well-Founded Relations\<close>

lemma wf_not_refl: "wf(r) \<Longrightarrow> \<langle>a,a\<rangle> \<notin> r"
by (erule_tac a=a in wf_induct, blast)

lemma wf_not_sym [rule_format]: "wf(r) \<Longrightarrow> \<forall>x. \<langle>a,x\<rangle>:r \<longrightarrow> \<langle>x,a\<rangle> \<notin> r"
by (erule_tac a=a in wf_induct, blast)

(* @{term"\<lbrakk>wf(r);  \<langle>a,x\<rangle> \<in> r;  \<not>P \<Longrightarrow> \<langle>x,a\<rangle> \<in> r\<rbrakk> \<Longrightarrow> P"} *)
lemmas wf_asym = wf_not_sym [THEN swap]

lemma wf_on_not_refl: "\<lbrakk>wf[A](r); a \<in> A\<rbrakk> \<Longrightarrow> \<langle>a,a\<rangle> \<notin> r"
by (erule_tac a=a in wf_on_induct, assumption, blast)

lemma wf_on_not_sym:
     "\<lbrakk>wf[A](r);  a \<in> A\<rbrakk> \<Longrightarrow> (\<And>b. b\<in>A \<Longrightarrow> \<langle>a,b\<rangle>:r \<Longrightarrow> \<langle>b,a\<rangle>\<notin>r)"
apply (atomize (full), intro impI)
apply (erule_tac a=a in wf_on_induct, assumption, blast)
done

lemma wf_on_asym:
     "\<lbrakk>wf[A](r);  \<not>Z \<Longrightarrow> \<langle>a,b\<rangle> \<in> r;
         \<langle>b,a\<rangle> \<notin> r \<Longrightarrow> Z; \<not>Z \<Longrightarrow> a \<in> A; \<not>Z \<Longrightarrow> b \<in> A\<rbrakk> \<Longrightarrow> Z"
by (blast dest: wf_on_not_sym)


(*Needed to prove well_ordI.  Could also reason that wf[A](r) means
  wf(r \<inter> A*A);  thus wf( (r \<inter> A*A)^+ ) and use wf_not_refl *)
lemma wf_on_chain3:
     "\<lbrakk>wf[A](r); \<langle>a,b\<rangle>:r; \<langle>b,c\<rangle>:r; \<langle>c,a\<rangle>:r; a \<in> A; b \<in> A; c \<in> A\<rbrakk> \<Longrightarrow> P"
apply (subgoal_tac "\<forall>y\<in>A. \<forall>z\<in>A. \<langle>a,y\<rangle>:r \<longrightarrow> \<langle>y,z\<rangle>:r \<longrightarrow> \<langle>z,a\<rangle>:r \<longrightarrow> P",
       blast)
apply (erule_tac a=a in wf_on_induct, assumption, blast)
done



text\<open>transitive closure of a WF relation is WF provided
  \<^term>\<open>A\<close> is downward closed\<close>
lemma wf_on_trancl:
    "\<lbrakk>wf[A](r);  r-``A \<subseteq> A\<rbrakk> \<Longrightarrow> wf[A](r^+)"
apply (rule wf_onI2)
apply (frule bspec [THEN mp], assumption+)
apply (erule_tac a = y in wf_on_induct, assumption)
apply (blast elim: tranclE, blast)
done

lemma wf_trancl: "wf(r) \<Longrightarrow> wf(r^+)"
apply (simp add: wf_iff_wf_on_field)
apply (rule wf_on_subset_A)
 apply (erule wf_on_trancl)
 apply blast
apply (rule trancl_type [THEN field_rel_subset])
done


text\<open>\<^term>\<open>r-``{a}\<close> is the set of everything under \<^term>\<open>a\<close> in \<^term>\<open>r\<close>\<close>

lemmas underI = vimage_singleton_iff [THEN iffD2]
lemmas underD = vimage_singleton_iff [THEN iffD1]


subsection\<open>The Predicate \<^term>\<open>is_recfun\<close>\<close>

lemma is_recfun_type: "is_recfun(r,a,H,f) \<Longrightarrow> f \<in> r-``{a} -> range(f)"
  unfolding is_recfun_def
apply (erule ssubst)
apply (rule lamI [THEN rangeI, THEN lam_type], assumption)
done

lemmas is_recfun_imp_function = is_recfun_type [THEN fun_is_function]

lemma apply_recfun:
    "\<lbrakk>is_recfun(r,a,H,f); \<langle>x,a\<rangle>:r\<rbrakk> \<Longrightarrow> f`x = H(x, restrict(f,r-``{x}))"
  unfolding is_recfun_def
  txt\<open>replace f only on the left-hand side\<close>
apply (erule_tac P = "\<lambda>x. t(x) = u" for t u in ssubst)
apply (simp add: underI)
done

lemma is_recfun_equal [rule_format]:
     "\<lbrakk>wf(r);  trans(r);  is_recfun(r,a,H,f);  is_recfun(r,b,H,g)\<rbrakk>
      \<Longrightarrow> \<langle>x,a\<rangle>:r \<longrightarrow> \<langle>x,b\<rangle>:r \<longrightarrow> f`x=g`x"
apply (frule_tac f = f in is_recfun_type)
apply (frule_tac f = g in is_recfun_type)
apply (simp add: is_recfun_def)
apply (erule_tac a=x in wf_induct)
apply (intro impI)
apply (elim ssubst)
apply (simp (no_asm_simp) add: vimage_singleton_iff restrict_def)
apply (rule_tac t = "\<lambda>z. H (x, z)" for x in subst_context)
apply (subgoal_tac "\<forall>y\<in>r-``{x}. \<forall>z. \<langle>y,z\<rangle>:f \<longleftrightarrow> \<langle>y,z\<rangle>:g")
 apply (blast dest: transD)
apply (simp add: apply_iff)
apply (blast dest: transD intro: sym)
done

lemma is_recfun_cut:
     "\<lbrakk>wf(r);  trans(r);
         is_recfun(r,a,H,f);  is_recfun(r,b,H,g);  \<langle>b,a\<rangle>:r\<rbrakk>
      \<Longrightarrow> restrict(f, r-``{b}) = g"
apply (frule_tac f = f in is_recfun_type)
apply (rule fun_extension)
  apply (blast dest: transD intro: restrict_type2)
 apply (erule is_recfun_type, simp)
apply (blast dest: transD intro: is_recfun_equal)
done

subsection\<open>Recursion: Main Existence Lemma\<close>

lemma is_recfun_functional:
     "\<lbrakk>wf(r); trans(r); is_recfun(r,a,H,f); is_recfun(r,a,H,g)\<rbrakk>  \<Longrightarrow>  f=g"
by (blast intro: fun_extension is_recfun_type is_recfun_equal)

lemma the_recfun_eq:
    "\<lbrakk>is_recfun(r,a,H,f);  wf(r);  trans(r)\<rbrakk> \<Longrightarrow> the_recfun(r,a,H) = f"
  unfolding the_recfun_def
apply (blast intro: is_recfun_functional)
done

(*If some f satisfies is_recfun(r,a,H,-) then so does the_recfun(r,a,H) *)
lemma is_the_recfun:
    "\<lbrakk>is_recfun(r,a,H,f);  wf(r);  trans(r)\<rbrakk>
     \<Longrightarrow> is_recfun(r, a, H, the_recfun(r,a,H))"
by (simp add: the_recfun_eq)

lemma unfold_the_recfun:
     "\<lbrakk>wf(r);  trans(r)\<rbrakk> \<Longrightarrow> is_recfun(r, a, H, the_recfun(r,a,H))"
apply (rule_tac a=a in wf_induct, assumption)
apply (rename_tac a1)
apply (rule_tac f = "\<lambda>y\<in>r-``{a1}. wftrec (r,y,H)" in is_the_recfun)
  apply typecheck
  unfolding is_recfun_def wftrec_def
  \<comment> \<open>Applying the substitution: must keep the quantified assumption!\<close>
apply (rule lam_cong [OF refl])
apply (drule underD)
apply (fold is_recfun_def)
apply (rule_tac t = "\<lambda>z. H(x, z)" for x in subst_context)
apply (rule fun_extension)
  apply (blast intro: is_recfun_type)
 apply (rule lam_type [THEN restrict_type2])
  apply blast
 apply (blast dest: transD)
apply atomize
apply (frule spec [THEN mp], assumption)
apply (subgoal_tac "\<langle>xa,a1\<rangle> \<in> r")
 apply (drule_tac x1 = xa in spec [THEN mp], assumption)
apply (simp add: vimage_singleton_iff
                 apply_recfun is_recfun_cut)
apply (blast dest: transD)
done


subsection\<open>Unfolding \<^term>\<open>wftrec(r,a,H)\<close>\<close>

lemma the_recfun_cut:
     "\<lbrakk>wf(r);  trans(r);  \<langle>b,a\<rangle>:r\<rbrakk>
      \<Longrightarrow> restrict(the_recfun(r,a,H), r-``{b}) = the_recfun(r,b,H)"
by (blast intro: is_recfun_cut unfold_the_recfun)

(*NOT SUITABLE FOR REWRITING: it is recursive!*)
lemma wftrec:
    "\<lbrakk>wf(r);  trans(r)\<rbrakk> \<Longrightarrow>
          wftrec(r,a,H) = H(a, \<lambda>x\<in>r-``{a}. wftrec(r,x,H))"
  unfolding wftrec_def
apply (subst unfold_the_recfun [unfolded is_recfun_def])
apply (simp_all add: vimage_singleton_iff [THEN iff_sym] the_recfun_cut)
done


subsubsection\<open>Removal of the Premise \<^term>\<open>trans(r)\<close>\<close>

(*NOT SUITABLE FOR REWRITING: it is recursive!*)
lemma wfrec:
    "wf(r) \<Longrightarrow> wfrec(r,a,H) = H(a, \<lambda>x\<in>r-``{a}. wfrec(r,x,H))"
  unfolding wfrec_def
apply (erule wf_trancl [THEN wftrec, THEN ssubst])
 apply (rule trans_trancl)
apply (rule vimage_pair_mono [THEN restrict_lam_eq, THEN subst_context])
 apply (erule r_into_trancl)
apply (rule subset_refl)
done

(*This form avoids giant explosions in proofs.  NOTE USE OF \<equiv> *)
lemma def_wfrec:
    "\<lbrakk>\<And>x. h(x)\<equiv>wfrec(r,x,H);  wf(r)\<rbrakk> \<Longrightarrow>
     h(a) = H(a, \<lambda>x\<in>r-``{a}. h(x))"
apply simp
apply (elim wfrec)
done

lemma wfrec_type:
    "\<lbrakk>wf(r);  a \<in> A;  field(r)<=A;
        \<And>x u. \<lbrakk>x \<in> A;  u \<in> Pi(r-``{x}, B)\<rbrakk> \<Longrightarrow> H(x,u) \<in> B(x)
\<rbrakk> \<Longrightarrow> wfrec(r,a,H) \<in> B(a)"
apply (rule_tac a = a in wf_induct2, assumption+)
apply (subst wfrec, assumption)
apply (simp add: lam_type underD)
done


lemma wfrec_on:
 "\<lbrakk>wf[A](r);  a \<in> A\<rbrakk> \<Longrightarrow>
         wfrec[A](r,a,H) = H(a, \<lambda>x\<in>(r-``{a}) \<inter> A. wfrec[A](r,x,H))"
  unfolding wf_on_def wfrec_on_def
apply (erule wfrec [THEN trans])
apply (simp add: vimage_Int_square)
done

text\<open>Minimal-element characterization of well-foundedness\<close>
lemma wf_eq_minimal: "wf(r) \<longleftrightarrow> (\<forall>Q x. x \<in> Q \<longrightarrow> (\<exists>z\<in>Q. \<forall>y. \<langle>y,z\<rangle>:r \<longrightarrow> y\<notin>Q))"
  unfolding wf_def by blast

end
