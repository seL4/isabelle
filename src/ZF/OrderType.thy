(*  Title:      ZF/OrderType.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

*)

header{*Order Types and Ordinal Arithmetic*}

theory OrderType = OrderArith + OrdQuant + Nat:

text{*The order type of a well-ordering is the least ordinal isomorphic to it.
Ordinal arithmetic is traditionally defined in terms of order types, as it is
here.  But a definition by transfinite recursion would be much simpler!*}

constdefs
  
  ordermap  :: "[i,i]=>i"
   "ordermap(A,r) == lam x:A. wfrec[A](r, x, %x f. f `` pred(A,x,r))"

  ordertype :: "[i,i]=>i"
   "ordertype(A,r) == ordermap(A,r)``A"

  (*alternative definition of ordinal numbers*)
  Ord_alt   :: "i => o"
   "Ord_alt(X) == well_ord(X, Memrel(X)) & (ALL u:X. u=pred(X, u, Memrel(X)))"

  (*coercion to ordinal: if not, just 0*)
  ordify    :: "i=>i"
    "ordify(x) == if Ord(x) then x else 0"

  (*ordinal multiplication*)
  omult      :: "[i,i]=>i"           (infixl "**" 70)
   "i ** j == ordertype(j*i, rmult(j,Memrel(j),i,Memrel(i)))"

  (*ordinal addition*)
  raw_oadd   :: "[i,i]=>i"
    "raw_oadd(i,j) == ordertype(i+j, radd(i,Memrel(i),j,Memrel(j)))"

  oadd      :: "[i,i]=>i"           (infixl "++" 65)
    "i ++ j == raw_oadd(ordify(i),ordify(j))"

  (*ordinal subtraction*)
  odiff      :: "[i,i]=>i"           (infixl "--" 65)
    "i -- j == ordertype(i-j, Memrel(i))"

  
syntax (xsymbols)
  "op **"     :: "[i,i] => i"          (infixl "\<times>\<times>" 70)

syntax (HTML output)
  "op **"     :: "[i,i] => i"          (infixl "\<times>\<times>" 70)


subsection{*Proofs needing the combination of Ordinal.thy and Order.thy*}

lemma le_well_ord_Memrel: "j le i ==> well_ord(j, Memrel(i))"
apply (rule well_ordI)
apply (rule wf_Memrel [THEN wf_imp_wf_on])
apply (simp add: ltD lt_Ord linear_def
                 ltI [THEN lt_trans2 [of _ j i]])
apply (intro ballI Ord_linear)
apply (blast intro: Ord_in_Ord lt_Ord)+
done

(*"Ord(i) ==> well_ord(i, Memrel(i))"*)
lemmas well_ord_Memrel = le_refl [THEN le_well_ord_Memrel]

(*Kunen's Theorem 7.3 (i), page 16;  see also Ordinal/Ord_in_Ord
  The smaller ordinal is an initial segment of the larger *)
lemma lt_pred_Memrel: 
    "j<i ==> pred(i, j, Memrel(i)) = j"
apply (unfold pred_def lt_def)
apply (simp (no_asm_simp))
apply (blast intro: Ord_trans)
done

lemma pred_Memrel: 
      "x:A ==> pred(A, x, Memrel(A)) = A Int x"
by (unfold pred_def Memrel_def, blast)

lemma Ord_iso_implies_eq_lemma:
     "[| j<i;  f: ord_iso(i,Memrel(i),j,Memrel(j)) |] ==> R"
apply (frule lt_pred_Memrel)
apply (erule ltE)
apply (rule well_ord_Memrel [THEN well_ord_iso_predE, of i f j], auto) 
apply (unfold ord_iso_def)
(*Combining the two simplifications causes looping*)
apply (simp (no_asm_simp))
apply (blast intro: bij_is_fun [THEN apply_type] Ord_trans)
done

(*Kunen's Theorem 7.3 (ii), page 16.  Isomorphic ordinals are equal*)
lemma Ord_iso_implies_eq:
     "[| Ord(i);  Ord(j);  f:  ord_iso(i,Memrel(i),j,Memrel(j)) |]     
      ==> i=j"
apply (rule_tac i = i and j = j in Ord_linear_lt)
apply (blast intro: ord_iso_sym Ord_iso_implies_eq_lemma)+
done


subsection{*Ordermap and ordertype*}

lemma ordermap_type: 
    "ordermap(A,r) : A -> ordertype(A,r)"
apply (unfold ordermap_def ordertype_def)
apply (rule lam_type)
apply (rule lamI [THEN imageI], assumption+)
done

subsubsection{*Unfolding of ordermap *}

(*Useful for cardinality reasoning; see CardinalArith.ML*)
lemma ordermap_eq_image: 
    "[| wf[A](r);  x:A |]
     ==> ordermap(A,r) ` x = ordermap(A,r) `` pred(A,x,r)"
apply (unfold ordermap_def pred_def)
apply (simp (no_asm_simp))
apply (erule wfrec_on [THEN trans], assumption)
apply (simp (no_asm_simp) add: subset_iff image_lam vimage_singleton_iff)
done

(*Useful for rewriting PROVIDED pred is not unfolded until later!*)
lemma ordermap_pred_unfold:
     "[| wf[A](r);  x:A |]
      ==> ordermap(A,r) ` x = {ordermap(A,r)`y . y : pred(A,x,r)}"
by (simp add: ordermap_eq_image pred_subset ordermap_type [THEN image_fun])

(*pred-unfolded version.  NOT suitable for rewriting -- loops!*)
lemmas ordermap_unfold = ordermap_pred_unfold [simplified pred_def] 

(*The theorem above is 

[| wf[A](r); x : A |]
==> ordermap(A,r) ` x = {ordermap(A,r) ` y . y: {y: A . <y,x> : r}}

NOTE: the definition of ordermap used here delivers ordinals only if r is
transitive.  If r is the predecessor relation on the naturals then
ordermap(nat,predr) ` n equals {n-1} and not n.  A more complicated definition,
like

  ordermap(A,r) ` x = Union{succ(ordermap(A,r) ` y) . y: {y: A . <y,x> : r}},

might eliminate the need for r to be transitive.
*)


subsubsection{*Showing that ordermap, ordertype yield ordinals *}

lemma Ord_ordermap: 
    "[| well_ord(A,r);  x:A |] ==> Ord(ordermap(A,r) ` x)"
apply (unfold well_ord_def tot_ord_def part_ord_def, safe)
apply (rule_tac a=x in wf_on_induct, assumption+)
apply (simp (no_asm_simp) add: ordermap_pred_unfold)
apply (rule OrdI [OF _ Ord_is_Transset])
apply (unfold pred_def Transset_def)
apply (blast intro: trans_onD
	     dest!: ordermap_unfold [THEN equalityD1])+ 
done

lemma Ord_ordertype: 
    "well_ord(A,r) ==> Ord(ordertype(A,r))"
apply (unfold ordertype_def)
apply (subst image_fun [OF ordermap_type subset_refl])
apply (rule OrdI [OF _ Ord_is_Transset])
prefer 2 apply (blast intro: Ord_ordermap)
apply (unfold Transset_def well_ord_def)
apply (blast intro: trans_onD
	     dest!: ordermap_unfold [THEN equalityD1])
done


subsubsection{*ordermap preserves the orderings in both directions *}

lemma ordermap_mono:
     "[| <w,x>: r;  wf[A](r);  w: A; x: A |]
      ==> ordermap(A,r)`w : ordermap(A,r)`x"
apply (erule_tac x1 = x in ordermap_unfold [THEN ssubst], assumption, blast)
done

(*linearity of r is crucial here*)
lemma converse_ordermap_mono: 
    "[| ordermap(A,r)`w : ordermap(A,r)`x;  well_ord(A,r); w: A; x: A |]
     ==> <w,x>: r"
apply (unfold well_ord_def tot_ord_def, safe)
apply (erule_tac x=w and y=x in linearE, assumption+) 
apply (blast elim!: mem_not_refl [THEN notE])
apply (blast dest: ordermap_mono intro: mem_asym) 
done

lemmas ordermap_surj = 
    ordermap_type [THEN surj_image, unfolded ordertype_def [symmetric]]

lemma ordermap_bij: 
    "well_ord(A,r) ==> ordermap(A,r) : bij(A, ordertype(A,r))"
apply (unfold well_ord_def tot_ord_def bij_def inj_def)
apply (force intro!: ordermap_type ordermap_surj 
             elim: linearE dest: ordermap_mono 
             simp add: mem_not_refl)
done

subsubsection{*Isomorphisms involving ordertype *}

lemma ordertype_ord_iso: 
 "well_ord(A,r)
  ==> ordermap(A,r) : ord_iso(A,r, ordertype(A,r), Memrel(ordertype(A,r)))"
apply (unfold ord_iso_def)
apply (safe elim!: well_ord_is_wf 
            intro!: ordermap_type [THEN apply_type] ordermap_mono ordermap_bij)
apply (blast dest!: converse_ordermap_mono)
done

lemma ordertype_eq:
     "[| f: ord_iso(A,r,B,s);  well_ord(B,s) |]
      ==> ordertype(A,r) = ordertype(B,s)"
apply (frule well_ord_ord_iso, assumption)
apply (rule Ord_iso_implies_eq, (erule Ord_ordertype)+)
apply (blast intro: ord_iso_trans ord_iso_sym ordertype_ord_iso)
done

lemma ordertype_eq_imp_ord_iso:
     "[| ordertype(A,r) = ordertype(B,s); well_ord(A,r);  well_ord(B,s) |] 
      ==> EX f. f: ord_iso(A,r,B,s)"
apply (rule exI)
apply (rule ordertype_ord_iso [THEN ord_iso_trans], assumption)
apply (erule ssubst)
apply (erule ordertype_ord_iso [THEN ord_iso_sym])
done

subsubsection{*Basic equalities for ordertype *}

(*Ordertype of Memrel*)
lemma le_ordertype_Memrel: "j le i ==> ordertype(j,Memrel(i)) = j"
apply (rule Ord_iso_implies_eq [symmetric])
apply (erule ltE, assumption)
apply (blast intro: le_well_ord_Memrel Ord_ordertype)
apply (rule ord_iso_trans)
apply (erule_tac [2] le_well_ord_Memrel [THEN ordertype_ord_iso])
apply (rule id_bij [THEN ord_isoI])
apply (simp (no_asm_simp))
apply (fast elim: ltE Ord_in_Ord Ord_trans)
done

(*"Ord(i) ==> ordertype(i, Memrel(i)) = i"*)
lemmas ordertype_Memrel = le_refl [THEN le_ordertype_Memrel]

lemma ordertype_0 [simp]: "ordertype(0,r) = 0"
apply (rule id_bij [THEN ord_isoI, THEN ordertype_eq, THEN trans])
apply (erule emptyE)
apply (rule well_ord_0)
apply (rule Ord_0 [THEN ordertype_Memrel])
done

(*Ordertype of rvimage:  [| f: bij(A,B);  well_ord(B,s) |] ==>
                         ordertype(A, rvimage(A,f,s)) = ordertype(B,s) *)
lemmas bij_ordertype_vimage = ord_iso_rvimage [THEN ordertype_eq]

subsubsection{*A fundamental unfolding law for ordertype. *}

(*Ordermap returns the same result if applied to an initial segment*)
lemma ordermap_pred_eq_ordermap:
     "[| well_ord(A,r);  y:A;  z: pred(A,y,r) |]
      ==> ordermap(pred(A,y,r), r) ` z = ordermap(A, r) ` z"
apply (frule wf_on_subset_A [OF well_ord_is_wf pred_subset])
apply (rule_tac a=z in wf_on_induct, assumption+)
apply (safe elim!: predE)
apply (simp (no_asm_simp) add: ordermap_pred_unfold well_ord_is_wf pred_iff)
(*combining these two simplifications LOOPS! *)
apply (simp (no_asm_simp) add: pred_pred_eq)
apply (simp add: pred_def)
apply (rule RepFun_cong [OF _ refl])
apply (drule well_ord_is_trans_on)
apply (fast elim!: trans_onD)
done

lemma ordertype_unfold: 
    "ordertype(A,r) = {ordermap(A,r)`y . y : A}"
apply (unfold ordertype_def)
apply (rule image_fun [OF ordermap_type subset_refl])
done

text{*Theorems by Krzysztof Grabczewski; proofs simplified by lcp *}

lemma ordertype_pred_subset: "[| well_ord(A,r);  x:A |] ==>              
          ordertype(pred(A,x,r),r) <= ordertype(A,r)"
apply (simp add: ordertype_unfold well_ord_subset [OF _ pred_subset])
apply (fast intro: ordermap_pred_eq_ordermap elim: predE)
done

lemma ordertype_pred_lt:
     "[| well_ord(A,r);  x:A |]
      ==> ordertype(pred(A,x,r),r) < ordertype(A,r)"
apply (rule ordertype_pred_subset [THEN subset_imp_le, THEN leE])
apply (simp_all add: Ord_ordertype well_ord_subset [OF _ pred_subset])
apply (erule sym [THEN ordertype_eq_imp_ord_iso, THEN exE])
apply (erule_tac [3] well_ord_iso_predE)
apply (simp_all add: well_ord_subset [OF _ pred_subset])
done

(*May rewrite with this -- provided no rules are supplied for proving that
        well_ord(pred(A,x,r), r) *)
lemma ordertype_pred_unfold:
     "well_ord(A,r)
      ==> ordertype(A,r) = {ordertype(pred(A,x,r),r). x:A}"
apply (rule equalityI)
apply (safe intro!: ordertype_pred_lt [THEN ltD])
apply (auto simp add: ordertype_def well_ord_is_wf [THEN ordermap_eq_image]
                      ordermap_type [THEN image_fun]
                      ordermap_pred_eq_ordermap pred_subset)
done


subsection{*Alternative definition of ordinal*}

(*proof by Krzysztof Grabczewski*)
lemma Ord_is_Ord_alt: "Ord(i) ==> Ord_alt(i)"
apply (unfold Ord_alt_def)
apply (rule conjI)
apply (erule well_ord_Memrel)
apply (unfold Ord_def Transset_def pred_def Memrel_def, blast) 
done

(*proof by lcp*)
lemma Ord_alt_is_Ord: 
    "Ord_alt(i) ==> Ord(i)"
apply (unfold Ord_alt_def Ord_def Transset_def well_ord_def 
                     tot_ord_def part_ord_def trans_on_def)
apply (simp add: pred_Memrel)
apply (blast elim!: equalityE)
done


subsection{*Ordinal Addition*}

subsubsection{*Order Type calculations for radd *}

text{*Addition with 0 *}

lemma bij_sum_0: "(lam z:A+0. case(%x. x, %y. y, z)) : bij(A+0, A)"
apply (rule_tac d = Inl in lam_bijective, safe)
apply (simp_all (no_asm_simp))
done

lemma ordertype_sum_0_eq:
     "well_ord(A,r) ==> ordertype(A+0, radd(A,r,0,s)) = ordertype(A,r)"
apply (rule bij_sum_0 [THEN ord_isoI, THEN ordertype_eq])
prefer 2 apply assumption
apply force
done

lemma bij_0_sum: "(lam z:0+A. case(%x. x, %y. y, z)) : bij(0+A, A)"
apply (rule_tac d = Inr in lam_bijective, safe)
apply (simp_all (no_asm_simp))
done

lemma ordertype_0_sum_eq:
     "well_ord(A,r) ==> ordertype(0+A, radd(0,s,A,r)) = ordertype(A,r)"
apply (rule bij_0_sum [THEN ord_isoI, THEN ordertype_eq])
prefer 2 apply assumption
apply force
done

text{*Initial segments of radd.  Statements by Grabczewski *}

(*In fact, pred(A+B, Inl(a), radd(A,r,B,s)) = pred(A,a,r)+0 *)
lemma pred_Inl_bij: 
 "a:A ==> (lam x:pred(A,a,r). Inl(x))     
          : bij(pred(A,a,r), pred(A+B, Inl(a), radd(A,r,B,s)))"
apply (unfold pred_def)
apply (rule_tac d = "case (%x. x, %y. y) " in lam_bijective)
apply auto
done

lemma ordertype_pred_Inl_eq:
     "[| a:A;  well_ord(A,r) |]
      ==> ordertype(pred(A+B, Inl(a), radd(A,r,B,s)), radd(A,r,B,s)) =  
          ordertype(pred(A,a,r), r)"
apply (rule pred_Inl_bij [THEN ord_isoI, THEN ord_iso_sym, THEN ordertype_eq])
apply (simp_all add: well_ord_subset [OF _ pred_subset])
apply (simp add: pred_def)
done

lemma pred_Inr_bij: 
 "b:B ==>   
         id(A+pred(B,b,s))       
         : bij(A+pred(B,b,s), pred(A+B, Inr(b), radd(A,r,B,s)))"
apply (unfold pred_def id_def)
apply (rule_tac d = "%z. z" in lam_bijective, auto) 
done

lemma ordertype_pred_Inr_eq:
     "[| b:B;  well_ord(A,r);  well_ord(B,s) |]
      ==> ordertype(pred(A+B, Inr(b), radd(A,r,B,s)), radd(A,r,B,s)) =  
          ordertype(A+pred(B,b,s), radd(A,r,pred(B,b,s),s))"
apply (rule pred_Inr_bij [THEN ord_isoI, THEN ord_iso_sym, THEN ordertype_eq])
prefer 2 apply (force simp add: pred_def id_def, assumption)
apply (blast intro: well_ord_radd well_ord_subset [OF _ pred_subset])
done


subsubsection{*ordify: trivial coercion to an ordinal *}

lemma Ord_ordify [iff, TC]: "Ord(ordify(x))"
by (simp add: ordify_def)

(*Collapsing*)
lemma ordify_idem [simp]: "ordify(ordify(x)) = ordify(x)"
by (simp add: ordify_def)


subsubsection{*Basic laws for ordinal addition *}

lemma Ord_raw_oadd: "[|Ord(i); Ord(j)|] ==> Ord(raw_oadd(i,j))"
by (simp add: raw_oadd_def ordify_def Ord_ordertype well_ord_radd
              well_ord_Memrel)

lemma Ord_oadd [iff,TC]: "Ord(i++j)"
by (simp add: oadd_def Ord_raw_oadd)


text{*Ordinal addition with zero *}

lemma raw_oadd_0: "Ord(i) ==> raw_oadd(i,0) = i"
by (simp add: raw_oadd_def ordify_def ordertype_sum_0_eq
              ordertype_Memrel well_ord_Memrel)

lemma oadd_0 [simp]: "Ord(i) ==> i++0 = i"
apply (simp (no_asm_simp) add: oadd_def raw_oadd_0 ordify_def)
done

lemma raw_oadd_0_left: "Ord(i) ==> raw_oadd(0,i) = i"
by (simp add: raw_oadd_def ordify_def ordertype_0_sum_eq ordertype_Memrel
              well_ord_Memrel)

lemma oadd_0_left [simp]: "Ord(i) ==> 0++i = i"
by (simp add: oadd_def raw_oadd_0_left ordify_def)


lemma oadd_eq_if_raw_oadd:
     "i++j = (if Ord(i) then (if Ord(j) then raw_oadd(i,j) else i)  
              else (if Ord(j) then j else 0))"
by (simp add: oadd_def ordify_def raw_oadd_0_left raw_oadd_0)

lemma raw_oadd_eq_oadd: "[|Ord(i); Ord(j)|] ==> raw_oadd(i,j) = i++j"
by (simp add: oadd_def ordify_def)

(*** Further properties of ordinal addition.  Statements by Grabczewski,
    proofs by lcp. ***)

(*Surely also provable by transfinite induction on j?*)
lemma lt_oadd1: "k<i ==> k < i++j"
apply (simp add: oadd_def ordify_def lt_Ord2 raw_oadd_0, clarify)
apply (simp add: raw_oadd_def)
apply (rule ltE, assumption)
apply (rule ltI)
apply (force simp add: ordertype_pred_unfold well_ord_radd well_ord_Memrel
          ordertype_pred_Inl_eq lt_pred_Memrel leI [THEN le_ordertype_Memrel])
apply (blast intro: Ord_ordertype well_ord_radd well_ord_Memrel)
done

(*Thus also we obtain the rule  i++j = k ==> i le k *)
lemma oadd_le_self: "Ord(i) ==> i le i++j"
apply (rule all_lt_imp_le)
apply (auto simp add: Ord_oadd lt_oadd1) 
done

text{*Various other results *}

lemma id_ord_iso_Memrel: "A<=B ==> id(A) : ord_iso(A, Memrel(A), A, Memrel(B))"
apply (rule id_bij [THEN ord_isoI])
apply (simp (no_asm_simp))
apply blast
done

lemma subset_ord_iso_Memrel:
     "[| f: ord_iso(A,Memrel(B),C,r); A<=B |] ==> f: ord_iso(A,Memrel(A),C,r)"
apply (frule ord_iso_is_bij [THEN bij_is_fun, THEN fun_is_rel]) 
apply (frule ord_iso_trans [OF id_ord_iso_Memrel], assumption) 
apply (simp add: right_comp_id) 
done

lemma restrict_ord_iso:
     "[| f \<in> ord_iso(i, Memrel(i), Order.pred(A,a,r), r);  a \<in> A; j < i; 
       trans[A](r) |]
      ==> restrict(f,j) \<in> ord_iso(j, Memrel(j), Order.pred(A,f`j,r), r)"
apply (frule ltD) 
apply (frule ord_iso_is_bij [THEN bij_is_fun, THEN apply_type], assumption) 
apply (frule ord_iso_restrict_pred, assumption) 
apply (simp add: pred_iff trans_pred_pred_eq lt_pred_Memrel)
apply (blast intro!: subset_ord_iso_Memrel le_imp_subset [OF leI]) 
done

lemma restrict_ord_iso2:
     "[| f \<in> ord_iso(Order.pred(A,a,r), r, i, Memrel(i));  a \<in> A; 
       j < i; trans[A](r) |]
      ==> converse(restrict(converse(f), j)) 
          \<in> ord_iso(Order.pred(A, converse(f)`j, r), r, j, Memrel(j))"
by (blast intro: restrict_ord_iso ord_iso_sym ltI)

lemma ordertype_sum_Memrel:
     "[| well_ord(A,r);  k<j |]
      ==> ordertype(A+k, radd(A, r, k, Memrel(j))) =  
          ordertype(A+k, radd(A, r, k, Memrel(k)))"
apply (erule ltE)
apply (rule ord_iso_refl [THEN sum_ord_iso_cong, THEN ordertype_eq])
apply (erule OrdmemD [THEN id_ord_iso_Memrel, THEN ord_iso_sym])
apply (simp_all add: well_ord_radd well_ord_Memrel)
done

lemma oadd_lt_mono2: "k<j ==> i++k < i++j"
apply (simp add: oadd_def ordify_def raw_oadd_0_left lt_Ord lt_Ord2, clarify)
apply (simp add: raw_oadd_def)
apply (rule ltE, assumption)
apply (rule ordertype_pred_unfold [THEN equalityD2, THEN subsetD, THEN ltI])
apply (simp_all add: Ord_ordertype well_ord_radd well_ord_Memrel)
apply (rule bexI)
apply (erule_tac [2] InrI)
apply (simp add: ordertype_pred_Inr_eq well_ord_Memrel lt_pred_Memrel
                 leI [THEN le_ordertype_Memrel] ordertype_sum_Memrel)
done

lemma oadd_lt_cancel2: "[| i++j < i++k;  Ord(j) |] ==> j<k"
apply (simp (asm_lr) add: oadd_eq_if_raw_oadd split add: split_if_asm)
 prefer 2
 apply (frule_tac i = i and j = j in oadd_le_self)
 apply (simp (asm_lr) add: oadd_def ordify_def lt_Ord not_lt_iff_le [THEN iff_sym])
apply (rule Ord_linear_lt, auto) 
apply (simp_all add: raw_oadd_eq_oadd)
apply (blast dest: oadd_lt_mono2 elim: lt_irrefl lt_asym)+
done

lemma oadd_lt_iff2: "Ord(j) ==> i++j < i++k <-> j<k"
by (blast intro!: oadd_lt_mono2 dest!: oadd_lt_cancel2)

lemma oadd_inject: "[| i++j = i++k;  Ord(j); Ord(k) |] ==> j=k"
apply (simp add: oadd_eq_if_raw_oadd split add: split_if_asm)
apply (simp add: raw_oadd_eq_oadd)
apply (rule Ord_linear_lt, auto) 
apply (force dest: oadd_lt_mono2 [of concl: i] simp add: lt_not_refl)+
done

lemma lt_oadd_disj: "k < i++j ==> k<i | (EX l:j. k = i++l )"
apply (simp add: Ord_in_Ord' [of _ j] oadd_eq_if_raw_oadd
            split add: split_if_asm)
 prefer 2
 apply (simp add: Ord_in_Ord' [of _ j] lt_def)
apply (simp add: ordertype_pred_unfold well_ord_radd well_ord_Memrel raw_oadd_def)
apply (erule ltD [THEN RepFunE])
apply (force simp add: ordertype_pred_Inl_eq well_ord_Memrel ltI 
                       lt_pred_Memrel le_ordertype_Memrel leI
                       ordertype_pred_Inr_eq ordertype_sum_Memrel)
done


subsubsection{*Ordinal addition with successor -- via associativity! *}

lemma oadd_assoc: "(i++j)++k = i++(j++k)"
apply (simp add: oadd_eq_if_raw_oadd Ord_raw_oadd raw_oadd_0 raw_oadd_0_left, clarify)
apply (simp add: raw_oadd_def)
apply (rule ordertype_eq [THEN trans])
apply (rule sum_ord_iso_cong [OF ordertype_ord_iso [THEN ord_iso_sym] 
                                 ord_iso_refl])
apply (simp_all add: Ord_ordertype well_ord_radd well_ord_Memrel)
apply (rule sum_assoc_ord_iso [THEN ordertype_eq, THEN trans])
apply (rule_tac [2] ordertype_eq)
apply (rule_tac [2] sum_ord_iso_cong [OF ord_iso_refl ordertype_ord_iso])
apply (blast intro: Ord_ordertype well_ord_radd well_ord_Memrel)+
done

lemma oadd_unfold: "[| Ord(i);  Ord(j) |] ==> i++j = i Un (\<Union>k\<in>j. {i++k})"
apply (rule subsetI [THEN equalityI])
apply (erule ltI [THEN lt_oadd_disj, THEN disjE])
apply (blast intro: Ord_oadd) 
apply (blast elim!: ltE, blast) 
apply (force intro: lt_oadd1 oadd_lt_mono2 simp add: Ord_mem_iff_lt)
done

lemma oadd_1: "Ord(i) ==> i++1 = succ(i)"
apply (simp (no_asm_simp) add: oadd_unfold Ord_1 oadd_0)
apply blast
done

lemma oadd_succ [simp]: "Ord(j) ==> i++succ(j) = succ(i++j)"
apply (simp add: oadd_eq_if_raw_oadd, clarify)
apply (simp add: raw_oadd_eq_oadd)
apply (simp add: oadd_1 [of j, symmetric] oadd_1 [of "i++j", symmetric]
                 oadd_assoc)
done


text{*Ordinal addition with limit ordinals *}

lemma oadd_UN:
     "[| !!x. x:A ==> Ord(j(x));  a:A |]
      ==> i ++ (\<Union>x\<in>A. j(x)) = (\<Union>x\<in>A. i++j(x))"
by (blast intro: ltI Ord_UN Ord_oadd lt_oadd1 [THEN ltD] 
                 oadd_lt_mono2 [THEN ltD] 
          elim!: ltE dest!: ltI [THEN lt_oadd_disj])

lemma oadd_Limit: "Limit(j) ==> i++j = (\<Union>k\<in>j. i++k)"
apply (frule Limit_has_0 [THEN ltD])
apply (simp add: Limit_is_Ord [THEN Ord_in_Ord] oadd_UN [symmetric] 
                 Union_eq_UN [symmetric] Limit_Union_eq)
done

lemma oadd_eq_0_iff: "[| Ord(i); Ord(j) |] ==> (i ++ j) = 0 <-> i=0 & j=0"
apply (erule trans_induct3 [of j])
apply (simp_all add: oadd_Limit)
apply (simp add: Union_empty_iff Limit_def lt_def, blast)
done

lemma oadd_eq_lt_iff: "[| Ord(i); Ord(j) |] ==> 0 < (i ++ j) <-> 0<i | 0<j"
by (simp add: Ord_0_lt_iff [symmetric] oadd_eq_0_iff)

lemma oadd_LimitI: "[| Ord(i); Limit(j) |] ==> Limit(i ++ j)"
apply (simp add: oadd_Limit)
apply (frule Limit_has_1 [THEN ltD])
apply (rule increasing_LimitI)
 apply (rule Ord_0_lt)
  apply (blast intro: Ord_in_Ord [OF Limit_is_Ord])
 apply (force simp add: Union_empty_iff oadd_eq_0_iff
                        Limit_is_Ord [of j, THEN Ord_in_Ord], auto)
apply (rule_tac x="succ(y)" in bexI)
 apply (simp add: ltI Limit_is_Ord [of j, THEN Ord_in_Ord])
apply (simp add: Limit_def lt_def) 
done

text{*Order/monotonicity properties of ordinal addition *}

lemma oadd_le_self2: "Ord(i) ==> i le j++i"
apply (erule_tac i = i in trans_induct3)
apply (simp (no_asm_simp) add: Ord_0_le)
apply (simp (no_asm_simp) add: oadd_succ succ_leI)
apply (simp (no_asm_simp) add: oadd_Limit)
apply (rule le_trans)
apply (rule_tac [2] le_implies_UN_le_UN)
apply (erule_tac [2] bspec)
 prefer 2 apply assumption
apply (simp add: Union_eq_UN [symmetric] Limit_Union_eq le_refl Limit_is_Ord)
done

lemma oadd_le_mono1: "k le j ==> k++i le j++i"
apply (frule lt_Ord)
apply (frule le_Ord2)
apply (simp add: oadd_eq_if_raw_oadd, clarify)
apply (simp add: raw_oadd_eq_oadd)
apply (erule_tac i = i in trans_induct3)
apply (simp (no_asm_simp))
apply (simp (no_asm_simp) add: oadd_succ succ_le_iff)
apply (simp (no_asm_simp) add: oadd_Limit)
apply (rule le_implies_UN_le_UN, blast)
done

lemma oadd_lt_mono: "[| i' le i;  j'<j |] ==> i'++j' < i++j"
by (blast intro: lt_trans1 oadd_le_mono1 oadd_lt_mono2 Ord_succD elim: ltE)

lemma oadd_le_mono: "[| i' le i;  j' le j |] ==> i'++j' le i++j"
by (simp del: oadd_succ add: oadd_succ [symmetric] le_Ord2 oadd_lt_mono)

lemma oadd_le_iff2: "[| Ord(j); Ord(k) |] ==> i++j le i++k <-> j le k"
by (simp del: oadd_succ add: oadd_lt_iff2 oadd_succ [symmetric] Ord_succ)

lemma oadd_lt_self: "[| Ord(i);  0<j |] ==> i < i++j"
apply (rule lt_trans2) 
apply (erule le_refl) 
apply (simp only: lt_Ord2  oadd_1 [of i, symmetric]) 
apply (blast intro: succ_leI oadd_le_mono)
done

text{*Every ordinal is exceeded by some limit ordinal.*}
lemma Ord_imp_greater_Limit: "Ord(i) ==> \<exists>k. i<k & Limit(k)"
apply (rule_tac x="i ++ nat" in exI) 
apply (blast intro: oadd_LimitI  oadd_lt_self  Limit_nat [THEN Limit_has_0])
done

lemma Ord2_imp_greater_Limit: "[|Ord(i); Ord(j)|] ==> \<exists>k. i<k & j<k & Limit(k)"
apply (insert Ord_Un [of i j, THEN Ord_imp_greater_Limit]) 
apply (simp add: Un_least_lt_iff) 
done


subsection{*Ordinal Subtraction*}

text{*The difference is @{term "ordertype(j-i, Memrel(j))"}.
    It's probably simpler to define the difference recursively!*}

lemma bij_sum_Diff:
     "A<=B ==> (lam y:B. if(y:A, Inl(y), Inr(y))) : bij(B, A+(B-A))"
apply (rule_tac d = "case (%x. x, %y. y) " in lam_bijective)
apply (blast intro!: if_type)
apply (fast intro!: case_type)
apply (erule_tac [2] sumE)
apply (simp_all (no_asm_simp))
done

lemma ordertype_sum_Diff:
     "i le j ==>   
            ordertype(i+(j-i), radd(i,Memrel(j),j-i,Memrel(j))) =        
            ordertype(j, Memrel(j))"
apply (safe dest!: le_subset_iff [THEN iffD1])
apply (rule bij_sum_Diff [THEN ord_isoI, THEN ord_iso_sym, THEN ordertype_eq])
apply (erule_tac [3] well_ord_Memrel, assumption)
apply (simp (no_asm_simp))
apply (frule_tac j = y in Ord_in_Ord, assumption)
apply (frule_tac j = x in Ord_in_Ord, assumption)
apply (simp (no_asm_simp) add: Ord_mem_iff_lt lt_Ord not_lt_iff_le)
apply (blast intro: lt_trans2 lt_trans)
done

lemma Ord_odiff [simp,TC]: 
    "[| Ord(i);  Ord(j) |] ==> Ord(i--j)"
apply (unfold odiff_def)
apply (blast intro: Ord_ordertype Diff_subset well_ord_subset well_ord_Memrel)
done


lemma raw_oadd_ordertype_Diff: 
   "i le j   
    ==> raw_oadd(i,j--i) = ordertype(i+(j-i), radd(i,Memrel(j),j-i,Memrel(j)))"
apply (simp add: raw_oadd_def odiff_def)
apply (safe dest!: le_subset_iff [THEN iffD1])
apply (rule sum_ord_iso_cong [THEN ordertype_eq])
apply (erule id_ord_iso_Memrel)
apply (rule ordertype_ord_iso [THEN ord_iso_sym])
apply (blast intro: well_ord_radd Diff_subset well_ord_subset well_ord_Memrel)+
done

lemma oadd_odiff_inverse: "i le j ==> i ++ (j--i) = j"
by (simp add: lt_Ord le_Ord2 oadd_def ordify_def raw_oadd_ordertype_Diff
              ordertype_sum_Diff ordertype_Memrel lt_Ord2 [THEN Ord_succD])

(*By oadd_inject, the difference between i and j is unique.  Note that we get
  i++j = k  ==>  j = k--i.  *)
lemma odiff_oadd_inverse: "[| Ord(i); Ord(j) |] ==> (i++j) -- i = j"
apply (rule oadd_inject)
apply (blast intro: oadd_odiff_inverse oadd_le_self)
apply (blast intro: Ord_ordertype Ord_oadd Ord_odiff)+
done

lemma odiff_lt_mono2: "[| i<j;  k le i |] ==> i--k < j--k"
apply (rule_tac i = k in oadd_lt_cancel2)
apply (simp add: oadd_odiff_inverse)
apply (subst oadd_odiff_inverse)
apply (blast intro: le_trans leI, assumption)
apply (simp (no_asm_simp) add: lt_Ord le_Ord2)
done


subsection{*Ordinal Multiplication*}

lemma Ord_omult [simp,TC]: 
    "[| Ord(i);  Ord(j) |] ==> Ord(i**j)"
apply (unfold omult_def)
apply (blast intro: Ord_ordertype well_ord_rmult well_ord_Memrel)
done

subsubsection{*A useful unfolding law *}

lemma pred_Pair_eq: 
 "[| a:A;  b:B |] ==> pred(A*B, <a,b>, rmult(A,r,B,s)) =      
                      pred(A,a,r)*B Un ({a} * pred(B,b,s))"
apply (unfold pred_def, blast)
done

lemma ordertype_pred_Pair_eq:
     "[| a:A;  b:B;  well_ord(A,r);  well_ord(B,s) |] ==>            
         ordertype(pred(A*B, <a,b>, rmult(A,r,B,s)), rmult(A,r,B,s)) =  
         ordertype(pred(A,a,r)*B + pred(B,b,s),                         
                  radd(A*B, rmult(A,r,B,s), B, s))"
apply (simp (no_asm_simp) add: pred_Pair_eq)
apply (rule ordertype_eq [symmetric])
apply (rule prod_sum_singleton_ord_iso)
apply (simp_all add: pred_subset well_ord_rmult [THEN well_ord_subset])
apply (blast intro: pred_subset well_ord_rmult [THEN well_ord_subset] 
             elim!: predE)
done

lemma ordertype_pred_Pair_lemma: 
    "[| i'<i;  j'<j |]
     ==> ordertype(pred(i*j, <i',j'>, rmult(i,Memrel(i),j,Memrel(j))),  
                   rmult(i,Memrel(i),j,Memrel(j))) =                    
         raw_oadd (j**i', j')"
apply (unfold raw_oadd_def omult_def)
apply (simp add: ordertype_pred_Pair_eq lt_pred_Memrel ltD lt_Ord2 
                 well_ord_Memrel)
apply (rule trans)
 apply (rule_tac [2] ordertype_ord_iso 
                      [THEN sum_ord_iso_cong, THEN ordertype_eq])
  apply (rule_tac [3] ord_iso_refl)
apply (rule id_bij [THEN ord_isoI, THEN ordertype_eq])
apply (elim SigmaE sumE ltE ssubst)
apply (simp_all add: well_ord_rmult well_ord_radd well_ord_Memrel
                     Ord_ordertype lt_Ord lt_Ord2) 
apply (blast intro: Ord_trans)+
done

lemma lt_omult: 
 "[| Ord(i);  Ord(j);  k<j**i |]
  ==> EX j' i'. k = j**i' ++ j' & j'<j & i'<i"
apply (unfold omult_def)
apply (simp add: ordertype_pred_unfold well_ord_rmult well_ord_Memrel)
apply (safe elim!: ltE)
apply (simp add: ordertype_pred_Pair_lemma ltI raw_oadd_eq_oadd 
            omult_def [symmetric] Ord_in_Ord' [of _ i] Ord_in_Ord' [of _ j])
apply (blast intro: ltI)
done

lemma omult_oadd_lt: 
     "[| j'<j;  i'<i |] ==> j**i' ++ j'  <  j**i"
apply (unfold omult_def)
apply (rule ltI)
 prefer 2
 apply (simp add: Ord_ordertype well_ord_rmult well_ord_Memrel lt_Ord2)
apply (simp add: ordertype_pred_unfold well_ord_rmult well_ord_Memrel lt_Ord2)
apply (rule bexI)
prefer 2 apply (blast elim!: ltE)
apply (simp add: ordertype_pred_Pair_lemma ltI omult_def [symmetric])
apply (simp add: lt_Ord lt_Ord2 raw_oadd_eq_oadd)
done

lemma omult_unfold:
     "[| Ord(i);  Ord(j) |] ==> j**i = (\<Union>j'\<in>j. \<Union>i'\<in>i. {j**i' ++ j'})"
apply (rule subsetI [THEN equalityI])
apply (rule lt_omult [THEN exE])
apply (erule_tac [3] ltI)
apply (simp_all add: Ord_omult) 
apply (blast elim!: ltE)
apply (blast intro: omult_oadd_lt [THEN ltD] ltI)
done

subsubsection{*Basic laws for ordinal multiplication *}

text{*Ordinal multiplication by zero *}

lemma omult_0 [simp]: "i**0 = 0"
apply (unfold omult_def)
apply (simp (no_asm_simp))
done

lemma omult_0_left [simp]: "0**i = 0"
apply (unfold omult_def)
apply (simp (no_asm_simp))
done

text{*Ordinal multiplication by 1 *}

lemma omult_1 [simp]: "Ord(i) ==> i**1 = i"
apply (unfold omult_def)
apply (rule_tac s1="Memrel(i)" 
       in ord_isoI [THEN ordertype_eq, THEN trans])
apply (rule_tac c = snd and d = "%z.<0,z>"  in lam_bijective)
apply (auto elim!: snd_type well_ord_Memrel ordertype_Memrel)
done

lemma omult_1_left [simp]: "Ord(i) ==> 1**i = i"
apply (unfold omult_def)
apply (rule_tac s1="Memrel(i)" 
       in ord_isoI [THEN ordertype_eq, THEN trans])
apply (rule_tac c = fst and d = "%z.<z,0>" in lam_bijective)
apply (auto elim!: fst_type well_ord_Memrel ordertype_Memrel)
done

text{*Distributive law for ordinal multiplication and addition *}

lemma oadd_omult_distrib:
     "[| Ord(i);  Ord(j);  Ord(k) |] ==> i**(j++k) = (i**j)++(i**k)"
apply (simp add: oadd_eq_if_raw_oadd)
apply (simp add: omult_def raw_oadd_def)
apply (rule ordertype_eq [THEN trans])
apply (rule prod_ord_iso_cong [OF ordertype_ord_iso [THEN ord_iso_sym] 
                                  ord_iso_refl])
apply (simp_all add: well_ord_rmult well_ord_radd well_ord_Memrel 
                     Ord_ordertype)
apply (rule sum_prod_distrib_ord_iso [THEN ordertype_eq, THEN trans])
apply (rule_tac [2] ordertype_eq)
apply (rule_tac [2] sum_ord_iso_cong [OF ordertype_ord_iso ordertype_ord_iso])
apply (simp_all add: well_ord_rmult well_ord_radd well_ord_Memrel 
                     Ord_ordertype)
done

lemma omult_succ: "[| Ord(i);  Ord(j) |] ==> i**succ(j) = (i**j)++i"
by (simp del: oadd_succ add: oadd_1 [of j, symmetric] oadd_omult_distrib)

text{*Associative law *}

lemma omult_assoc: 
    "[| Ord(i);  Ord(j);  Ord(k) |] ==> (i**j)**k = i**(j**k)"
apply (unfold omult_def)
apply (rule ordertype_eq [THEN trans])
apply (rule prod_ord_iso_cong [OF ord_iso_refl 
                                  ordertype_ord_iso [THEN ord_iso_sym]])
apply (blast intro: well_ord_rmult well_ord_Memrel)+
apply (rule prod_assoc_ord_iso 
             [THEN ord_iso_sym, THEN ordertype_eq, THEN trans])
apply (rule_tac [2] ordertype_eq)
apply (rule_tac [2] prod_ord_iso_cong [OF ordertype_ord_iso ord_iso_refl])
apply (blast intro: well_ord_rmult well_ord_Memrel Ord_ordertype)+
done


text{*Ordinal multiplication with limit ordinals *}

lemma omult_UN: 
     "[| Ord(i);  !!x. x:A ==> Ord(j(x)) |]
      ==> i ** (\<Union>x\<in>A. j(x)) = (\<Union>x\<in>A. i**j(x))"
by (simp (no_asm_simp) add: Ord_UN omult_unfold, blast)

lemma omult_Limit: "[| Ord(i);  Limit(j) |] ==> i**j = (\<Union>k\<in>j. i**k)"
by (simp add: Limit_is_Ord [THEN Ord_in_Ord] omult_UN [symmetric] 
              Union_eq_UN [symmetric] Limit_Union_eq)


subsubsection{*Ordering/monotonicity properties of ordinal multiplication *}

(*As a special case we have "[| 0<i;  0<j |] ==> 0 < i**j" *)
lemma lt_omult1: "[| k<i;  0<j |] ==> k < i**j"
apply (safe elim!: ltE intro!: ltI Ord_omult)
apply (force simp add: omult_unfold)
done

lemma omult_le_self: "[| Ord(i);  0<j |] ==> i le i**j"
by (blast intro: all_lt_imp_le Ord_omult lt_omult1 lt_Ord2)

lemma omult_le_mono1: "[| k le j;  Ord(i) |] ==> k**i le j**i"
apply (frule lt_Ord)
apply (frule le_Ord2)
apply (erule trans_induct3)
apply (simp (no_asm_simp) add: le_refl Ord_0)
apply (simp (no_asm_simp) add: omult_succ oadd_le_mono)
apply (simp (no_asm_simp) add: omult_Limit)
apply (rule le_implies_UN_le_UN, blast)
done

lemma omult_lt_mono2: "[| k<j;  0<i |] ==> i**k < i**j"
apply (rule ltI)
apply (simp (no_asm_simp) add: omult_unfold lt_Ord2)
apply (safe elim!: ltE intro!: Ord_omult)
apply (force simp add: Ord_omult)
done

lemma omult_le_mono2: "[| k le j;  Ord(i) |] ==> i**k le i**j"
apply (rule subset_imp_le)
apply (safe elim!: ltE dest!: Ord_succD intro!: Ord_omult)
apply (simp add: omult_unfold)
apply (blast intro: Ord_trans) 
done

lemma omult_le_mono: "[| i' le i;  j' le j |] ==> i'**j' le i**j"
by (blast intro: le_trans omult_le_mono1 omult_le_mono2 Ord_succD elim: ltE)

lemma omult_lt_mono: "[| i' le i;  j'<j;  0<i |] ==> i'**j' < i**j"
by (blast intro: lt_trans1 omult_le_mono1 omult_lt_mono2 Ord_succD elim: ltE)

lemma omult_le_self2: "[| Ord(i);  0<j |] ==> i le j**i"
apply (frule lt_Ord2)
apply (erule_tac i = i in trans_induct3)
apply (simp (no_asm_simp))
apply (simp (no_asm_simp) add: omult_succ)
apply (erule lt_trans1)
apply (rule_tac b = "j**x" in oadd_0 [THEN subst], rule_tac [2] oadd_lt_mono2)
apply (blast intro: Ord_omult, assumption)
apply (simp (no_asm_simp) add: omult_Limit)
apply (rule le_trans)
apply (rule_tac [2] le_implies_UN_le_UN)
prefer 2 apply blast
apply (simp (no_asm_simp) add: Union_eq_UN [symmetric] Limit_Union_eq Limit_is_Ord)
done


text{*Further properties of ordinal multiplication *}

lemma omult_inject: "[| i**j = i**k;  0<i;  Ord(j);  Ord(k) |] ==> j=k"
apply (rule Ord_linear_lt)
prefer 4 apply assumption
apply auto 
apply (force dest: omult_lt_mono2 simp add: lt_not_refl)+
done

subsection{*The Relation @{term Lt}*}

lemma wf_Lt: "wf(Lt)"
apply (rule wf_subset) 
apply (rule wf_Memrel) 
apply (auto simp add: Lt_def Memrel_def lt_def) 
done

lemma irrefl_Lt: "irrefl(A,Lt)"
by (auto simp add: Lt_def irrefl_def)

lemma trans_Lt: "trans[A](Lt)"
apply (simp add: Lt_def trans_on_def) 
apply (blast intro: lt_trans) 
done

lemma part_ord_Lt: "part_ord(A,Lt)"
by (simp add: part_ord_def irrefl_Lt trans_Lt)

lemma linear_Lt: "linear(nat,Lt)"
apply (auto dest!: not_lt_imp_le simp add: Lt_def linear_def le_iff) 
apply (drule lt_asym, auto) 
done

lemma tot_ord_Lt: "tot_ord(nat,Lt)"
by (simp add: tot_ord_def linear_Lt part_ord_Lt)

lemma well_ord_Lt: "well_ord(nat,Lt)"
by (simp add: well_ord_def wf_Lt wf_imp_wf_on tot_ord_Lt)



ML {*
val ordermap_def = thm "ordermap_def";
val ordertype_def = thm "ordertype_def";
val Ord_alt_def = thm "Ord_alt_def";
val ordify_def = thm "ordify_def";

val Ord_in_Ord' = thm "Ord_in_Ord'";
val le_well_ord_Memrel = thm "le_well_ord_Memrel";
val well_ord_Memrel = thm "well_ord_Memrel";
val lt_pred_Memrel = thm "lt_pred_Memrel";
val pred_Memrel = thm "pred_Memrel";
val Ord_iso_implies_eq = thm "Ord_iso_implies_eq";
val ordermap_type = thm "ordermap_type";
val ordermap_eq_image = thm "ordermap_eq_image";
val ordermap_pred_unfold = thm "ordermap_pred_unfold";
val ordermap_unfold = thm "ordermap_unfold";
val Ord_ordermap = thm "Ord_ordermap";
val Ord_ordertype = thm "Ord_ordertype";
val ordermap_mono = thm "ordermap_mono";
val converse_ordermap_mono = thm "converse_ordermap_mono";
val ordermap_surj = thm "ordermap_surj";
val ordermap_bij = thm "ordermap_bij";
val ordertype_ord_iso = thm "ordertype_ord_iso";
val ordertype_eq = thm "ordertype_eq";
val ordertype_eq_imp_ord_iso = thm "ordertype_eq_imp_ord_iso";
val le_ordertype_Memrel = thm "le_ordertype_Memrel";
val ordertype_Memrel = thm "ordertype_Memrel";
val ordertype_0 = thm "ordertype_0";
val bij_ordertype_vimage = thm "bij_ordertype_vimage";
val ordermap_pred_eq_ordermap = thm "ordermap_pred_eq_ordermap";
val ordertype_unfold = thm "ordertype_unfold";
val ordertype_pred_subset = thm "ordertype_pred_subset";
val ordertype_pred_lt = thm "ordertype_pred_lt";
val ordertype_pred_unfold = thm "ordertype_pred_unfold";
val Ord_is_Ord_alt = thm "Ord_is_Ord_alt";
val Ord_alt_is_Ord = thm "Ord_alt_is_Ord";
val bij_sum_0 = thm "bij_sum_0";
val ordertype_sum_0_eq = thm "ordertype_sum_0_eq";
val bij_0_sum = thm "bij_0_sum";
val ordertype_0_sum_eq = thm "ordertype_0_sum_eq";
val pred_Inl_bij = thm "pred_Inl_bij";
val ordertype_pred_Inl_eq = thm "ordertype_pred_Inl_eq";
val pred_Inr_bij = thm "pred_Inr_bij";
val ordertype_pred_Inr_eq = thm "ordertype_pred_Inr_eq";
val Ord_ordify = thm "Ord_ordify";
val ordify_idem = thm "ordify_idem";
val Ord_raw_oadd = thm "Ord_raw_oadd";
val Ord_oadd = thm "Ord_oadd";
val raw_oadd_0 = thm "raw_oadd_0";
val oadd_0 = thm "oadd_0";
val raw_oadd_0_left = thm "raw_oadd_0_left";
val oadd_0_left = thm "oadd_0_left";
val oadd_eq_if_raw_oadd = thm "oadd_eq_if_raw_oadd";
val raw_oadd_eq_oadd = thm "raw_oadd_eq_oadd";
val lt_oadd1 = thm "lt_oadd1";
val oadd_le_self = thm "oadd_le_self";
val id_ord_iso_Memrel = thm "id_ord_iso_Memrel";
val ordertype_sum_Memrel = thm "ordertype_sum_Memrel";
val oadd_lt_mono2 = thm "oadd_lt_mono2";
val oadd_lt_cancel2 = thm "oadd_lt_cancel2";
val oadd_lt_iff2 = thm "oadd_lt_iff2";
val oadd_inject = thm "oadd_inject";
val lt_oadd_disj = thm "lt_oadd_disj";
val oadd_assoc = thm "oadd_assoc";
val oadd_unfold = thm "oadd_unfold";
val oadd_1 = thm "oadd_1";
val oadd_succ = thm "oadd_succ";
val oadd_UN = thm "oadd_UN";
val oadd_Limit = thm "oadd_Limit";
val oadd_le_self2 = thm "oadd_le_self2";
val oadd_le_mono1 = thm "oadd_le_mono1";
val oadd_lt_mono = thm "oadd_lt_mono";
val oadd_le_mono = thm "oadd_le_mono";
val oadd_le_iff2 = thm "oadd_le_iff2";
val bij_sum_Diff = thm "bij_sum_Diff";
val ordertype_sum_Diff = thm "ordertype_sum_Diff";
val Ord_odiff = thm "Ord_odiff";
val raw_oadd_ordertype_Diff = thm "raw_oadd_ordertype_Diff";
val oadd_odiff_inverse = thm "oadd_odiff_inverse";
val odiff_oadd_inverse = thm "odiff_oadd_inverse";
val odiff_lt_mono2 = thm "odiff_lt_mono2";
val Ord_omult = thm "Ord_omult";
val pred_Pair_eq = thm "pred_Pair_eq";
val ordertype_pred_Pair_eq = thm "ordertype_pred_Pair_eq";
val lt_omult = thm "lt_omult";
val omult_oadd_lt = thm "omult_oadd_lt";
val omult_unfold = thm "omult_unfold";
val omult_0 = thm "omult_0";
val omult_0_left = thm "omult_0_left";
val omult_1 = thm "omult_1";
val omult_1_left = thm "omult_1_left";
val oadd_omult_distrib = thm "oadd_omult_distrib";
val omult_succ = thm "omult_succ";
val omult_assoc = thm "omult_assoc";
val omult_UN = thm "omult_UN";
val omult_Limit = thm "omult_Limit";
val lt_omult1 = thm "lt_omult1";
val omult_le_self = thm "omult_le_self";
val omult_le_mono1 = thm "omult_le_mono1";
val omult_lt_mono2 = thm "omult_lt_mono2";
val omult_le_mono2 = thm "omult_le_mono2";
val omult_le_mono = thm "omult_le_mono";
val omult_lt_mono = thm "omult_lt_mono";
val omult_le_self2 = thm "omult_le_self2";
val omult_inject = thm "omult_inject";

val wf_Lt = thm "wf_Lt";
val irrefl_Lt = thm "irrefl_Lt";
val trans_Lt = thm "trans_Lt";
val part_ord_Lt = thm "part_ord_Lt";
val linear_Lt = thm "linear_Lt";
val tot_ord_Lt = thm "tot_ord_Lt";
val well_ord_Lt = thm "well_ord_Lt";
*}

end
