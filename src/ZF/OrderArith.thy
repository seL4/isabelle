(*  Title:      ZF/OrderArith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

*)

header{*Combining Orderings: Foundations of Ordinal Arithmetic*}

theory OrderArith = Order + Sum + Ordinal:
constdefs

  (*disjoint sum of two relations; underlies ordinal addition*)
  radd    :: "[i,i,i,i]=>i"
    "radd(A,r,B,s) == 
                {z: (A+B) * (A+B).  
                    (EX x y. z = <Inl(x), Inr(y)>)   |   
                    (EX x' x. z = <Inl(x'), Inl(x)> & <x',x>:r)   |      
                    (EX y' y. z = <Inr(y'), Inr(y)> & <y',y>:s)}"

  (*lexicographic product of two relations; underlies ordinal multiplication*)
  rmult   :: "[i,i,i,i]=>i"
    "rmult(A,r,B,s) == 
                {z: (A*B) * (A*B).  
                    EX x' y' x y. z = <<x',y'>, <x,y>> &         
                       (<x',x>: r | (x'=x & <y',y>: s))}"

  (*inverse image of a relation*)
  rvimage :: "[i,i,i]=>i"
    "rvimage(A,f,r) == {z: A*A. EX x y. z = <x,y> & <f`x,f`y>: r}"

  measure :: "[i, i\<Rightarrow>i] \<Rightarrow> i"
    "measure(A,f) == {<x,y>: A*A. f(x) < f(y)}"


subsection{*Addition of Relations -- Disjoint Sum*}

subsubsection{*Rewrite rules.  Can be used to obtain introduction rules*}

lemma radd_Inl_Inr_iff [iff]: 
    "<Inl(a), Inr(b)> : radd(A,r,B,s)  <->  a:A & b:B"
by (unfold radd_def, blast)

lemma radd_Inl_iff [iff]: 
    "<Inl(a'), Inl(a)> : radd(A,r,B,s)  <->  a':A & a:A & <a',a>:r"
by (unfold radd_def, blast)

lemma radd_Inr_iff [iff]: 
    "<Inr(b'), Inr(b)> : radd(A,r,B,s) <->  b':B & b:B & <b',b>:s"
by (unfold radd_def, blast)

lemma radd_Inr_Inl_iff [simp]: 
    "<Inr(b), Inl(a)> : radd(A,r,B,s) <-> False"
by (unfold radd_def, blast)

declare radd_Inr_Inl_iff [THEN iffD1, dest!] 

subsubsection{*Elimination Rule*}

lemma raddE:
    "[| <p',p> : radd(A,r,B,s);                  
        !!x y. [| p'=Inl(x); x:A; p=Inr(y); y:B |] ==> Q;        
        !!x' x. [| p'=Inl(x'); p=Inl(x); <x',x>: r; x':A; x:A |] ==> Q;  
        !!y' y. [| p'=Inr(y'); p=Inr(y); <y',y>: s; y':B; y:B |] ==> Q   
     |] ==> Q"
by (unfold radd_def, blast) 

subsubsection{*Type checking*}

lemma radd_type: "radd(A,r,B,s) <= (A+B) * (A+B)"
apply (unfold radd_def)
apply (rule Collect_subset)
done

lemmas field_radd = radd_type [THEN field_rel_subset]

subsubsection{*Linearity*}

lemma linear_radd: 
    "[| linear(A,r);  linear(B,s) |] ==> linear(A+B,radd(A,r,B,s))"
by (unfold linear_def, blast) 


subsubsection{*Well-foundedness*}

lemma wf_on_radd: "[| wf[A](r);  wf[B](s) |] ==> wf[A+B](radd(A,r,B,s))"
apply (rule wf_onI2)
apply (subgoal_tac "ALL x:A. Inl (x) : Ba")
 --{*Proving the lemma, which is needed twice!*}
 prefer 2
 apply (erule_tac V = "y : A + B" in thin_rl)
 apply (rule_tac ballI)
 apply (erule_tac r = r and a = x in wf_on_induct, assumption)
 apply blast 
txt{*Returning to main part of proof*}
apply safe
apply blast
apply (erule_tac r = s and a = ya in wf_on_induct, assumption, blast) 
done

lemma wf_radd: "[| wf(r);  wf(s) |] ==> wf(radd(field(r),r,field(s),s))"
apply (simp add: wf_iff_wf_on_field)
apply (rule wf_on_subset_A [OF _ field_radd])
apply (blast intro: wf_on_radd) 
done

lemma well_ord_radd:
     "[| well_ord(A,r);  well_ord(B,s) |] ==> well_ord(A+B, radd(A,r,B,s))"
apply (rule well_ordI)
apply (simp add: well_ord_def wf_on_radd)
apply (simp add: well_ord_def tot_ord_def linear_radd)
done

subsubsection{*An @{term ord_iso} congruence law*}

lemma sum_bij:
     "[| f: bij(A,C);  g: bij(B,D) |]
      ==> (lam z:A+B. case(%x. Inl(f`x), %y. Inr(g`y), z)) : bij(A+B, C+D)"
apply (rule_tac d = "case (%x. Inl (converse(f)`x), %y. Inr(converse(g)`y))" 
       in lam_bijective)
apply (typecheck add: bij_is_inj inj_is_fun) 
apply (auto simp add: left_inverse_bij right_inverse_bij) 
done

lemma sum_ord_iso_cong: 
    "[| f: ord_iso(A,r,A',r');  g: ord_iso(B,s,B',s') |] ==>      
            (lam z:A+B. case(%x. Inl(f`x), %y. Inr(g`y), z))             
            : ord_iso(A+B, radd(A,r,B,s), A'+B', radd(A',r',B',s'))"
apply (unfold ord_iso_def)
apply (safe intro!: sum_bij)
(*Do the beta-reductions now*)
apply (auto cong add: conj_cong simp add: bij_is_fun [THEN apply_type])
done

(*Could we prove an ord_iso result?  Perhaps 
     ord_iso(A+B, radd(A,r,B,s), A Un B, r Un s) *)
lemma sum_disjoint_bij: "A Int B = 0 ==>      
            (lam z:A+B. case(%x. x, %y. y, z)) : bij(A+B, A Un B)"
apply (rule_tac d = "%z. if z:A then Inl (z) else Inr (z) " in lam_bijective)
apply auto
done

subsubsection{*Associativity*}

lemma sum_assoc_bij:
     "(lam z:(A+B)+C. case(case(Inl, %y. Inr(Inl(y))), %y. Inr(Inr(y)), z))  
      : bij((A+B)+C, A+(B+C))"
apply (rule_tac d = "case (%x. Inl (Inl (x)), case (%x. Inl (Inr (x)), Inr))" 
       in lam_bijective)
apply auto
done

lemma sum_assoc_ord_iso:
     "(lam z:(A+B)+C. case(case(Inl, %y. Inr(Inl(y))), %y. Inr(Inr(y)), z))  
      : ord_iso((A+B)+C, radd(A+B, radd(A,r,B,s), C, t),     
                A+(B+C), radd(A, r, B+C, radd(B,s,C,t)))"
by (rule sum_assoc_bij [THEN ord_isoI], auto)


subsection{*Multiplication of Relations -- Lexicographic Product*}

subsubsection{*Rewrite rule.  Can be used to obtain introduction rules*}

lemma  rmult_iff [iff]: 
    "<<a',b'>, <a,b>> : rmult(A,r,B,s) <->        
            (<a',a>: r  & a':A & a:A & b': B & b: B) |   
            (<b',b>: s  & a'=a & a:A & b': B & b: B)"

by (unfold rmult_def, blast)

lemma rmultE: 
    "[| <<a',b'>, <a,b>> : rmult(A,r,B,s);               
        [| <a',a>: r;  a':A;  a:A;  b':B;  b:B |] ==> Q;         
        [| <b',b>: s;  a:A;  a'=a;  b':B;  b:B |] ==> Q  
     |] ==> Q"
by blast 

subsubsection{*Type checking*}

lemma rmult_type: "rmult(A,r,B,s) <= (A*B) * (A*B)"
by (unfold rmult_def, rule Collect_subset)

lemmas field_rmult = rmult_type [THEN field_rel_subset]

subsubsection{*Linearity*}

lemma linear_rmult:
    "[| linear(A,r);  linear(B,s) |] ==> linear(A*B,rmult(A,r,B,s))"
by (simp add: linear_def, blast) 

subsubsection{*Well-foundedness*}

lemma wf_on_rmult: "[| wf[A](r);  wf[B](s) |] ==> wf[A*B](rmult(A,r,B,s))"
apply (rule wf_onI2)
apply (erule SigmaE)
apply (erule ssubst)
apply (subgoal_tac "ALL b:B. <x,b>: Ba", blast)
apply (erule_tac a = x in wf_on_induct, assumption)
apply (rule ballI)
apply (erule_tac a = b in wf_on_induct, assumption)
apply (best elim!: rmultE bspec [THEN mp])
done


lemma wf_rmult: "[| wf(r);  wf(s) |] ==> wf(rmult(field(r),r,field(s),s))"
apply (simp add: wf_iff_wf_on_field)
apply (rule wf_on_subset_A [OF _ field_rmult])
apply (blast intro: wf_on_rmult) 
done

lemma well_ord_rmult:
     "[| well_ord(A,r);  well_ord(B,s) |] ==> well_ord(A*B, rmult(A,r,B,s))"
apply (rule well_ordI)
apply (simp add: well_ord_def wf_on_rmult)
apply (simp add: well_ord_def tot_ord_def linear_rmult)
done


subsubsection{*An @{term ord_iso} congruence law*}

lemma prod_bij:
     "[| f: bij(A,C);  g: bij(B,D) |] 
      ==> (lam <x,y>:A*B. <f`x, g`y>) : bij(A*B, C*D)"
apply (rule_tac d = "%<x,y>. <converse (f) `x, converse (g) `y>" 
       in lam_bijective)
apply (typecheck add: bij_is_inj inj_is_fun) 
apply (auto simp add: left_inverse_bij right_inverse_bij) 
done

lemma prod_ord_iso_cong: 
    "[| f: ord_iso(A,r,A',r');  g: ord_iso(B,s,B',s') |]      
     ==> (lam <x,y>:A*B. <f`x, g`y>)                                  
         : ord_iso(A*B, rmult(A,r,B,s), A'*B', rmult(A',r',B',s'))"
apply (unfold ord_iso_def)
apply (safe intro!: prod_bij)
apply (simp_all add: bij_is_fun [THEN apply_type])
apply (blast intro: bij_is_inj [THEN inj_apply_equality])
done

lemma singleton_prod_bij: "(lam z:A. <x,z>) : bij(A, {x}*A)"
by (rule_tac d = snd in lam_bijective, auto)

(*Used??*)
lemma singleton_prod_ord_iso:
     "well_ord({x},xr) ==>   
          (lam z:A. <x,z>) : ord_iso(A, r, {x}*A, rmult({x}, xr, A, r))"
apply (rule singleton_prod_bij [THEN ord_isoI])
apply (simp (no_asm_simp))
apply (blast dest: well_ord_is_wf [THEN wf_on_not_refl])
done

(*Here we build a complicated function term, then simplify it using
  case_cong, id_conv, comp_lam, case_case.*)
lemma prod_sum_singleton_bij:
     "a~:C ==>  
       (lam x:C*B + D. case(%x. x, %y.<a,y>, x))  
       : bij(C*B + D, C*B Un {a}*D)"
apply (rule subst_elem)
apply (rule id_bij [THEN sum_bij, THEN comp_bij])
apply (rule singleton_prod_bij)
apply (rule sum_disjoint_bij, blast)
apply (simp (no_asm_simp) cong add: case_cong)
apply (rule comp_lam [THEN trans, symmetric])
apply (fast elim!: case_type)
apply (simp (no_asm_simp) add: case_case)
done

lemma prod_sum_singleton_ord_iso:
 "[| a:A;  well_ord(A,r) |] ==>  
    (lam x:pred(A,a,r)*B + pred(B,b,s). case(%x. x, %y.<a,y>, x))  
    : ord_iso(pred(A,a,r)*B + pred(B,b,s),               
                  radd(A*B, rmult(A,r,B,s), B, s),       
              pred(A,a,r)*B Un {a}*pred(B,b,s), rmult(A,r,B,s))"
apply (rule prod_sum_singleton_bij [THEN ord_isoI])
apply (simp (no_asm_simp) add: pred_iff well_ord_is_wf [THEN wf_on_not_refl])
apply (auto elim!: well_ord_is_wf [THEN wf_on_asym] predE)
done

subsubsection{*Distributive law*}

lemma sum_prod_distrib_bij:
     "(lam <x,z>:(A+B)*C. case(%y. Inl(<y,z>), %y. Inr(<y,z>), x))  
      : bij((A+B)*C, (A*C)+(B*C))"
by (rule_tac d = "case (%<x,y>.<Inl (x),y>, %<x,y>.<Inr (x),y>) " 
    in lam_bijective, auto)

lemma sum_prod_distrib_ord_iso:
 "(lam <x,z>:(A+B)*C. case(%y. Inl(<y,z>), %y. Inr(<y,z>), x))  
  : ord_iso((A+B)*C, rmult(A+B, radd(A,r,B,s), C, t),  
            (A*C)+(B*C), radd(A*C, rmult(A,r,C,t), B*C, rmult(B,s,C,t)))"
by (rule sum_prod_distrib_bij [THEN ord_isoI], auto)

subsubsection{*Associativity*}

lemma prod_assoc_bij:
     "(lam <<x,y>, z>:(A*B)*C. <x,<y,z>>) : bij((A*B)*C, A*(B*C))"
by (rule_tac d = "%<x, <y,z>>. <<x,y>, z>" in lam_bijective, auto)

lemma prod_assoc_ord_iso:
 "(lam <<x,y>, z>:(A*B)*C. <x,<y,z>>)                    
  : ord_iso((A*B)*C, rmult(A*B, rmult(A,r,B,s), C, t),   
            A*(B*C), rmult(A, r, B*C, rmult(B,s,C,t)))"
by (rule prod_assoc_bij [THEN ord_isoI], auto)

subsection{*Inverse Image of a Relation*}

subsubsection{*Rewrite rule*}

lemma rvimage_iff: "<a,b> : rvimage(A,f,r)  <->  <f`a,f`b>: r & a:A & b:A"
by (unfold rvimage_def, blast)

subsubsection{*Type checking*}

lemma rvimage_type: "rvimage(A,f,r) <= A*A"
by (unfold rvimage_def, rule Collect_subset)

lemmas field_rvimage = rvimage_type [THEN field_rel_subset]

lemma rvimage_converse: "rvimage(A,f, converse(r)) = converse(rvimage(A,f,r))"
by (unfold rvimage_def, blast)


subsubsection{*Partial Ordering Properties*}

lemma irrefl_rvimage: 
    "[| f: inj(A,B);  irrefl(B,r) |] ==> irrefl(A, rvimage(A,f,r))"
apply (unfold irrefl_def rvimage_def)
apply (blast intro: inj_is_fun [THEN apply_type])
done

lemma trans_on_rvimage: 
    "[| f: inj(A,B);  trans[B](r) |] ==> trans[A](rvimage(A,f,r))"
apply (unfold trans_on_def rvimage_def)
apply (blast intro: inj_is_fun [THEN apply_type])
done

lemma part_ord_rvimage: 
    "[| f: inj(A,B);  part_ord(B,r) |] ==> part_ord(A, rvimage(A,f,r))"
apply (unfold part_ord_def)
apply (blast intro!: irrefl_rvimage trans_on_rvimage)
done

subsubsection{*Linearity*}

lemma linear_rvimage:
    "[| f: inj(A,B);  linear(B,r) |] ==> linear(A,rvimage(A,f,r))"
apply (simp add: inj_def linear_def rvimage_iff) 
apply (blast intro: apply_funtype) 
done

lemma tot_ord_rvimage: 
    "[| f: inj(A,B);  tot_ord(B,r) |] ==> tot_ord(A, rvimage(A,f,r))"
apply (unfold tot_ord_def)
apply (blast intro!: part_ord_rvimage linear_rvimage)
done


subsubsection{*Well-foundedness*}

lemma wf_rvimage [intro!]: "wf(r) ==> wf(rvimage(A,f,r))"
apply (simp (no_asm_use) add: rvimage_def wf_eq_minimal)
apply clarify
apply (subgoal_tac "EX w. w : {w: {f`x. x:Q}. EX x. x: Q & (f`x = w) }")
 apply (erule allE)
 apply (erule impE)
 apply assumption
 apply blast
apply blast 
done

text{*But note that the combination of @{text wf_imp_wf_on} and
 @{text wf_rvimage} gives @{term "wf(r) ==> wf[C](rvimage(A,f,r))"}*}
lemma wf_on_rvimage: "[| f: A->B;  wf[B](r) |] ==> wf[A](rvimage(A,f,r))"
apply (rule wf_onI2)
apply (subgoal_tac "ALL z:A. f`z=f`y --> z: Ba")
 apply blast
apply (erule_tac a = "f`y" in wf_on_induct)
 apply (blast intro!: apply_funtype)
apply (blast intro!: apply_funtype dest!: rvimage_iff [THEN iffD1])
done

(*Note that we need only wf[A](...) and linear(A,...) to get the result!*)
lemma well_ord_rvimage:
     "[| f: inj(A,B);  well_ord(B,r) |] ==> well_ord(A, rvimage(A,f,r))"
apply (rule well_ordI)
apply (unfold well_ord_def tot_ord_def)
apply (blast intro!: wf_on_rvimage inj_is_fun)
apply (blast intro!: linear_rvimage)
done

lemma ord_iso_rvimage: 
    "f: bij(A,B) ==> f: ord_iso(A, rvimage(A,f,s), B, s)"
apply (unfold ord_iso_def)
apply (simp add: rvimage_iff)
done

lemma ord_iso_rvimage_eq: 
    "f: ord_iso(A,r, B,s) ==> rvimage(A,f,s) = r Int A*A"
by (unfold ord_iso_def rvimage_def, blast)


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


subsection{*Other Results*}

lemma wf_times: "A Int B = 0 ==> wf(A*B)"
by (simp add: wf_def, blast)

text{*Could also be used to prove @{text wf_radd}*}
lemma wf_Un:
     "[| range(r) Int domain(s) = 0; wf(r);  wf(s) |] ==> wf(r Un s)"
apply (simp add: wf_def, clarify) 
apply (rule equalityI) 
 prefer 2 apply blast 
apply clarify 
apply (drule_tac x=Z in spec)
apply (drule_tac x="Z Int domain(s)" in spec)
apply simp 
apply (blast intro: elim: equalityE) 
done

subsubsection{*The Empty Relation*}

lemma wf0: "wf(0)"
by (simp add: wf_def, blast)

lemma linear0: "linear(0,0)"
by (simp add: linear_def)

lemma well_ord0: "well_ord(0,0)"
by (blast intro: wf_imp_wf_on well_ordI wf0 linear0)

subsubsection{*The "measure" relation is useful with wfrec*}

lemma measure_eq_rvimage_Memrel:
     "measure(A,f) = rvimage(A,Lambda(A,f),Memrel(Collect(RepFun(A,f),Ord)))"
apply (simp (no_asm) add: measure_def rvimage_def Memrel_iff)
apply (rule equalityI, auto)
apply (auto intro: Ord_in_Ord simp add: lt_def)
done

lemma wf_measure [iff]: "wf(measure(A,f))"
by (simp (no_asm) add: measure_eq_rvimage_Memrel wf_Memrel wf_rvimage)

lemma measure_iff [iff]: "<x,y> : measure(A,f) <-> x:A & y:A & f(x)<f(y)"
by (simp (no_asm) add: measure_def)

lemma linear_measure: 
 assumes Ordf: "!!x. x \<in> A ==> Ord(f(x))"
     and inj:  "!!x y. [|x \<in> A; y \<in> A; f(x) = f(y) |] ==> x=y"
 shows "linear(A, measure(A,f))"
apply (auto simp add: linear_def) 
apply (rule_tac i="f(x)" and j="f(y)" in Ord_linear_lt) 
    apply (simp_all add: Ordf) 
apply (blast intro: inj) 
done

lemma wf_on_measure: "wf[B](measure(A,f))"
by (rule wf_imp_wf_on [OF wf_measure])

lemma well_ord_measure: 
 assumes Ordf: "!!x. x \<in> A ==> Ord(f(x))"
     and inj:  "!!x y. [|x \<in> A; y \<in> A; f(x) = f(y) |] ==> x=y"
 shows "well_ord(A, measure(A,f))"
apply (rule well_ordI)
apply (rule wf_on_measure) 
apply (blast intro: linear_measure Ordf inj) 
done

lemma measure_type: "measure(A,f) <= A*A"
by (auto simp add: measure_def)

subsubsection{*Well-foundedness of Unions*}

lemma wf_on_Union:
 assumes wfA: "wf[A](r)"
     and wfB: "!!a. a\<in>A ==> wf[B(a)](s)"
     and ok: "!!a u v. [|<u,v> \<in> s; v \<in> B(a); a \<in> A|] 
                       ==> (\<exists>a'\<in>A. <a',a> \<in> r & u \<in> B(a')) | u \<in> B(a)"
 shows "wf[\<Union>a\<in>A. B(a)](s)"
apply (rule wf_onI2)
apply (erule UN_E)
apply (subgoal_tac "\<forall>z \<in> B(a). z \<in> Ba", blast)
apply (rule_tac a = a in wf_on_induct [OF wfA], assumption)
apply (rule ballI)
apply (rule_tac a = z in wf_on_induct [OF wfB], assumption, assumption)
apply (rename_tac u) 
apply (drule_tac x=u in bspec, blast) 
apply (erule mp, clarify)
apply (frule ok, assumption+, blast) 
done

subsubsection{*Bijections involving Powersets*}

lemma Pow_sum_bij:
    "(\<lambda>Z \<in> Pow(A+B). <{x \<in> A. Inl(x) \<in> Z}, {y \<in> B. Inr(y) \<in> Z}>)  
     \<in> bij(Pow(A+B), Pow(A)*Pow(B))"
apply (rule_tac d = "%<X,Y>. {Inl (x). x \<in> X} Un {Inr (y). y \<in> Y}" 
       in lam_bijective)
apply force+
done

text{*As a special case, we have @{term "bij(Pow(A*B), A -> Pow(B))"} *}
lemma Pow_Sigma_bij:
    "(\<lambda>r \<in> Pow(Sigma(A,B)). \<lambda>x \<in> A. r``{x})  
     \<in> bij(Pow(Sigma(A,B)), \<Pi> x \<in> A. Pow(B(x)))"
apply (rule_tac d = "%f. \<Union>x \<in> A. \<Union>y \<in> f`x. {<x,y>}" in lam_bijective)
apply (blast intro: lam_type)
apply (blast dest: apply_type, simp_all)
apply fast (*strange, but blast can't do it*)
apply (rule fun_extension, auto)
by blast


ML {*
val measure_def = thm "measure_def";
val radd_Inl_Inr_iff = thm "radd_Inl_Inr_iff";
val radd_Inl_iff = thm "radd_Inl_iff";
val radd_Inr_iff = thm "radd_Inr_iff";
val radd_Inr_Inl_iff = thm "radd_Inr_Inl_iff";
val raddE = thm "raddE";
val radd_type = thm "radd_type";
val field_radd = thm "field_radd";
val linear_radd = thm "linear_radd";
val wf_on_radd = thm "wf_on_radd";
val wf_radd = thm "wf_radd";
val well_ord_radd = thm "well_ord_radd";
val sum_bij = thm "sum_bij";
val sum_ord_iso_cong = thm "sum_ord_iso_cong";
val sum_disjoint_bij = thm "sum_disjoint_bij";
val sum_assoc_bij = thm "sum_assoc_bij";
val sum_assoc_ord_iso = thm "sum_assoc_ord_iso";
val rmult_iff = thm "rmult_iff";
val rmultE = thm "rmultE";
val rmult_type = thm "rmult_type";
val field_rmult = thm "field_rmult";
val linear_rmult = thm "linear_rmult";
val wf_on_rmult = thm "wf_on_rmult";
val wf_rmult = thm "wf_rmult";
val well_ord_rmult = thm "well_ord_rmult";
val prod_bij = thm "prod_bij";
val prod_ord_iso_cong = thm "prod_ord_iso_cong";
val singleton_prod_bij = thm "singleton_prod_bij";
val singleton_prod_ord_iso = thm "singleton_prod_ord_iso";
val prod_sum_singleton_bij = thm "prod_sum_singleton_bij";
val prod_sum_singleton_ord_iso = thm "prod_sum_singleton_ord_iso";
val sum_prod_distrib_bij = thm "sum_prod_distrib_bij";
val sum_prod_distrib_ord_iso = thm "sum_prod_distrib_ord_iso";
val prod_assoc_bij = thm "prod_assoc_bij";
val prod_assoc_ord_iso = thm "prod_assoc_ord_iso";
val rvimage_iff = thm "rvimage_iff";
val rvimage_type = thm "rvimage_type";
val field_rvimage = thm "field_rvimage";
val rvimage_converse = thm "rvimage_converse";
val irrefl_rvimage = thm "irrefl_rvimage";
val trans_on_rvimage = thm "trans_on_rvimage";
val part_ord_rvimage = thm "part_ord_rvimage";
val linear_rvimage = thm "linear_rvimage";
val tot_ord_rvimage = thm "tot_ord_rvimage";
val wf_rvimage = thm "wf_rvimage";
val wf_on_rvimage = thm "wf_on_rvimage";
val well_ord_rvimage = thm "well_ord_rvimage";
val ord_iso_rvimage = thm "ord_iso_rvimage";
val ord_iso_rvimage_eq = thm "ord_iso_rvimage_eq";
val measure_eq_rvimage_Memrel = thm "measure_eq_rvimage_Memrel";
val wf_measure = thm "wf_measure";
val measure_iff = thm "measure_iff";
*}

end
