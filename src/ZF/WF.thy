(*  Title:      ZF/WF.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Lawrence C Paulson
    Copyright   1994  University of Cambridge

Well-founded Recursion

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

theory WF = Trancl + mono + equalities:

constdefs
  wf           :: "i=>o"
    (*r is a well-founded relation*)
    "wf(r) == ALL Z. Z=0 | (EX x:Z. ALL y. <y,x>:r --> ~ y:Z)"

  wf_on        :: "[i,i]=>o"                      ("wf[_]'(_')")
    (*r is well-founded on A*)
    "wf_on(A,r) == wf(r Int A*A)"

  is_recfun    :: "[i, i, [i,i]=>i, i] =>o"
    "is_recfun(r,a,H,f) == (f = (lam x: r-``{a}. H(x, restrict(f, r-``{x}))))"

  the_recfun   :: "[i, i, [i,i]=>i] =>i"
    "the_recfun(r,a,H) == (THE f. is_recfun(r,a,H,f))"

  wftrec :: "[i, i, [i,i]=>i] =>i"
    "wftrec(r,a,H) == H(a, the_recfun(r,a,H))"

  wfrec :: "[i, i, [i,i]=>i] =>i"
    (*public version.  Does not require r to be transitive*)
    "wfrec(r,a,H) == wftrec(r^+, a, %x f. H(x, restrict(f,r-``{x})))"

  wfrec_on     :: "[i, i, i, [i,i]=>i] =>i"       ("wfrec[_]'(_,_,_')")
    "wfrec[A](r,a,H) == wfrec(r Int A*A, a, H)"


(*** Well-founded relations ***)

(** Equivalences between wf and wf_on **)

lemma wf_imp_wf_on: "wf(r) ==> wf[A](r)"
apply (unfold wf_def wf_on_def, clarify) (*needed for blast's efficiency*)
apply blast
done

lemma wf_on_imp_wf: "[|wf[A](r); r <= A*A|] ==> wf(r)";
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

(** Introduction rules for wf_on **)

lemma wf_onI:
(*If every non-empty subset of A has an r-minimal element then wf[A](r).*)
 assumes prem: "!!Z u. [| Z<=A;  u:Z;  ALL x:Z. EX y:Z. <y,x>:r |] ==> False"
 shows         "wf[A](r)"
apply (unfold wf_on_def wf_def)
apply (rule equals0I [THEN disjCI, THEN allI])
apply (rule_tac Z = "Z" in prem, blast+)
done

(*If r allows well-founded induction over A then wf[A](r)
  Premise is equivalent to
  !!B. ALL x:A. (ALL y. <y,x>: r --> y:B) --> x:B ==> A<=B  *)
lemma wf_onI2:
 assumes prem: "!!y B. [| ALL x:A. (ALL y:A. <y,x>:r --> y:B) --> x:B;   y:A |]
                       ==> y:B"
 shows         "wf[A](r)"
apply (rule wf_onI)
apply (rule_tac c=u in prem [THEN DiffE])
  prefer 3 apply blast 
 apply fast+
done


(** Well-founded Induction **)

(*Consider the least z in domain(r) such that P(z) does not hold...*)
lemma wf_induct:
    "[| wf(r);
        !!x.[| ALL y. <y,x>: r --> P(y) |] ==> P(x)
     |]  ==>  P(a)"
apply (unfold wf_def) 
apply (erule_tac x = "{z : domain(r). ~ P(z)}" in allE)
apply blast 
done

(*fixed up for induct method*)
lemmas wf_induct = wf_induct [induct set: wf]
  and wf_induct_rule = wf_induct [rule_format, induct set: wf]

(*The form of this rule is designed to match wfI*)
lemma wf_induct2:
    "[| wf(r);  a:A;  field(r)<=A;
        !!x.[| x: A;  ALL y. <y,x>: r --> P(y) |] ==> P(x) |]
     ==>  P(a)"
apply (erule_tac P="a:A" in rev_mp)
apply (erule_tac a=a in wf_induct, blast) 
done

lemma field_Int_square: "field(r Int A*A) <= A"
by blast

lemma wf_on_induct:
    "[| wf[A](r);  a:A;
        !!x.[| x: A;  ALL y:A. <y,x>: r --> P(y) |] ==> P(x)
     |]  ==>  P(a)"
apply (unfold wf_on_def) 
apply (erule wf_induct2, assumption)
apply (rule field_Int_square, blast)
done

(*fixed up for induct method*)
lemmas wf_on_induct = wf_on_induct [consumes 2, induct set: wf_on]
   and wf_on_induct_rule = 
	 wf_on_induct [rule_format, consumes 2, induct set: wf_on]


(*If r allows well-founded induction then wf(r)*)
lemma wfI:
    "[| field(r)<=A;
        !!y B. [| ALL x:A. (ALL y:A. <y,x>:r --> y:B) --> x:B;  y:A|]
               ==> y:B |]
     ==>  wf(r)"
apply (rule wf_on_subset_A [THEN wf_on_field_imp_wf])
apply (rule wf_onI2)
 prefer 2 apply blast  
apply blast 
done


(*** Properties of well-founded relations ***)

lemma wf_not_refl: "wf(r) ==> <a,a> ~: r"
by (erule_tac a=a in wf_induct, blast)

lemma wf_not_sym [rule_format]: "wf(r) ==> ALL x. <a,x>:r --> <x,a> ~: r"
by (erule_tac a=a in wf_induct, blast)

(* [| wf(r);  <a,x> : r;  ~P ==> <x,a> : r |] ==> P *)
lemmas wf_asym = wf_not_sym [THEN swap, standard]

lemma wf_on_not_refl: "[| wf[A](r); a: A |] ==> <a,a> ~: r"
by (erule_tac a=a in wf_on_induct, assumption, blast)

lemma wf_on_not_sym [rule_format]:
     "[| wf[A](r);  a:A |] ==> ALL b:A. <a,b>:r --> <b,a>~:r"
apply (erule_tac a=a in wf_on_induct, assumption, blast)
done

lemma wf_on_asym:
     "[| wf[A](r);  ~Z ==> <a,b> : r;
         <b,a> ~: r ==> Z; ~Z ==> a : A; ~Z ==> b : A |] ==> Z"
by (blast dest: wf_on_not_sym) 


(*Needed to prove well_ordI.  Could also reason that wf[A](r) means
  wf(r Int A*A);  thus wf( (r Int A*A)^+ ) and use wf_not_refl *)
lemma wf_on_chain3:
     "[| wf[A](r); <a,b>:r; <b,c>:r; <c,a>:r; a:A; b:A; c:A |] ==> P"
apply (subgoal_tac "ALL y:A. ALL z:A. <a,y>:r --> <y,z>:r --> <z,a>:r --> P",
       blast) 
apply (erule_tac a=a in wf_on_induct, assumption, blast)
done




(*transitive closure of a WF relation is WF provided A is downwards closed*)
lemma wf_on_trancl:
    "[| wf[A](r);  r-``A <= A |] ==> wf[A](r^+)"
apply (rule wf_onI2)
apply (frule bspec [THEN mp], assumption+)
apply (erule_tac a = "y" in wf_on_induct, assumption)
apply (blast elim: tranclE, blast) 
done

lemma wf_trancl: "wf(r) ==> wf(r^+)"
apply (simp add: wf_iff_wf_on_field)
apply (rule wf_on_subset_A) 
 apply (erule wf_on_trancl)
 apply blast 
apply (rule trancl_type [THEN field_rel_subset])
done



(** r-``{a} is the set of everything under a in r **)

lemmas underI = vimage_singleton_iff [THEN iffD2, standard]
lemmas underD = vimage_singleton_iff [THEN iffD1, standard]

(** is_recfun **)

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
      ==> <x,a>:r --> <x,b>:r --> f`x=g`x"
apply (frule_tac f = "f" in is_recfun_type)
apply (frule_tac f = "g" in is_recfun_type)
apply (simp add: is_recfun_def)
apply (erule_tac a=x in wf_induct)
apply (intro impI)
apply (elim ssubst)
apply (simp (no_asm_simp) add: vimage_singleton_iff restrict_def)
apply (rule_tac t = "%z. H (?x,z) " in subst_context)
apply (subgoal_tac "ALL y : r-``{x}. ALL z. <y,z>:f <-> <y,z>:g")
 apply (blast dest: transD)
apply (simp add: apply_iff)
apply (blast dest: transD intro: sym)
done

lemma is_recfun_cut:
     "[| wf(r);  trans(r);
         is_recfun(r,a,H,f);  is_recfun(r,b,H,g);  <b,a>:r |]
      ==> restrict(f, r-``{b}) = g"
apply (frule_tac f = "f" in is_recfun_type)
apply (rule fun_extension)
  apply (blast dest: transD intro: restrict_type2)
 apply (erule is_recfun_type, simp)
apply (blast dest: transD intro: is_recfun_equal)
done

(*** Main Existence Lemma ***)

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
apply (rule_tac f = "lam y: r-``{a1}. wftrec (r,y,H)" in is_the_recfun)
  apply typecheck
apply (unfold is_recfun_def wftrec_def)
(*Applying the substitution: must keep the quantified assumption!!*)
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
apply (subgoal_tac "<xa,a1> : r")
 apply (drule_tac x1 = "xa" in spec [THEN mp], assumption)
apply (simp add: vimage_singleton_iff 
                 apply_recfun is_recfun_cut)
apply (blast dest: transD)
done


(*** Unfolding wftrec ***)

lemma the_recfun_cut:
     "[| wf(r);  trans(r);  <b,a>:r |]
      ==> restrict(the_recfun(r,a,H), r-``{b}) = the_recfun(r,b,H)"
by (blast intro: is_recfun_cut unfold_the_recfun)

(*NOT SUITABLE FOR REWRITING: it is recursive!*)
lemma wftrec:
    "[| wf(r);  trans(r) |] ==>
          wftrec(r,a,H) = H(a, lam x: r-``{a}. wftrec(r,x,H))"
apply (unfold wftrec_def)
apply (subst unfold_the_recfun [unfolded is_recfun_def])
apply (simp_all add: vimage_singleton_iff [THEN iff_sym] the_recfun_cut)
done

(** Removal of the premise trans(r) **)

(*NOT SUITABLE FOR REWRITING: it is recursive!*)
lemma wfrec:
    "wf(r) ==> wfrec(r,a,H) = H(a, lam x:r-``{a}. wfrec(r,x,H))"
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
     h(a) = H(a, lam x: r-``{a}. h(x))"
apply simp
apply (elim wfrec) 
done

lemma wfrec_type:
    "[| wf(r);  a:A;  field(r)<=A;
        !!x u. [| x: A;  u: Pi(r-``{x}, B) |] ==> H(x,u) : B(x)
     |] ==> wfrec(r,a,H) : B(a)"
apply (rule_tac a = "a" in wf_induct2, assumption+)
apply (subst wfrec, assumption)
apply (simp add: lam_type underD)  
done


lemma wfrec_on:
 "[| wf[A](r);  a: A |] ==>
         wfrec[A](r,a,H) = H(a, lam x: (r-``{a}) Int A. wfrec[A](r,x,H))"
apply (unfold wf_on_def wfrec_on_def)
apply (erule wfrec [THEN trans])
apply (simp add: vimage_Int_square cons_subset_iff)
done

(*Minimal-element characterization of well-foundedness*)
lemma wf_eq_minimal:
     "wf(r) <-> (ALL Q x. x:Q --> (EX z:Q. ALL y. <y,z>:r --> y~:Q))"
apply (unfold wf_def, blast)
done

ML
{*
val wf_def = thm "wf_def";
val wf_on_def = thm "wf_on_def";

val wf_imp_wf_on = thm "wf_imp_wf_on";
val wf_on_field_imp_wf = thm "wf_on_field_imp_wf";
val wf_iff_wf_on_field = thm "wf_iff_wf_on_field";
val wf_on_subset_A = thm "wf_on_subset_A";
val wf_on_subset_r = thm "wf_on_subset_r";
val wf_onI = thm "wf_onI";
val wf_onI2 = thm "wf_onI2";
val wf_induct = thm "wf_induct";
val wf_induct2 = thm "wf_induct2";
val field_Int_square = thm "field_Int_square";
val wf_on_induct = thm "wf_on_induct";
val wfI = thm "wfI";
val wf_not_refl = thm "wf_not_refl";
val wf_not_sym = thm "wf_not_sym";
val wf_asym = thm "wf_asym";
val wf_on_not_refl = thm "wf_on_not_refl";
val wf_on_not_sym = thm "wf_on_not_sym";
val wf_on_asym = thm "wf_on_asym";
val wf_on_chain3 = thm "wf_on_chain3";
val wf_on_trancl = thm "wf_on_trancl";
val wf_trancl = thm "wf_trancl";
val underI = thm "underI";
val underD = thm "underD";
val is_recfun_type = thm "is_recfun_type";
val apply_recfun = thm "apply_recfun";
val is_recfun_equal = thm "is_recfun_equal";
val is_recfun_cut = thm "is_recfun_cut";
val is_recfun_functional = thm "is_recfun_functional";
val is_the_recfun = thm "is_the_recfun";
val unfold_the_recfun = thm "unfold_the_recfun";
val the_recfun_cut = thm "the_recfun_cut";
val wftrec = thm "wftrec";
val wfrec = thm "wfrec";
val def_wfrec = thm "def_wfrec";
val wfrec_type = thm "wfrec_type";
val wfrec_on = thm "wfrec_on";
val wf_eq_minimal = thm "wf_eq_minimal";
*}

end
