(*  Title:      ZF/Order.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Orders in Zermelo-Fraenkel Set Theory

Results from the book "Set Theory: an Introduction to Independence Proofs"
        by Kenneth Kunen.  Chapter 1, section 6.
*)

theory Order = WF + Perm:

constdefs

  part_ord :: "[i,i]=>o"          	(*Strict partial ordering*)
   "part_ord(A,r) == irrefl(A,r) & trans[A](r)"

  linear   :: "[i,i]=>o"          	(*Strict total ordering*)
   "linear(A,r) == (ALL x:A. ALL y:A. <x,y>:r | x=y | <y,x>:r)"

  tot_ord  :: "[i,i]=>o"          	(*Strict total ordering*)
   "tot_ord(A,r) == part_ord(A,r) & linear(A,r)"

  well_ord :: "[i,i]=>o"          	(*Well-ordering*)
   "well_ord(A,r) == tot_ord(A,r) & wf[A](r)"

  mono_map :: "[i,i,i,i]=>i"      	(*Order-preserving maps*)
   "mono_map(A,r,B,s) ==
	      {f: A->B. ALL x:A. ALL y:A. <x,y>:r --> <f`x,f`y>:s}"

  ord_iso  :: "[i,i,i,i]=>i"		(*Order isomorphisms*)
   "ord_iso(A,r,B,s) ==
	      {f: bij(A,B). ALL x:A. ALL y:A. <x,y>:r <-> <f`x,f`y>:s}"

  pred     :: "[i,i,i]=>i"		(*Set of predecessors*)
   "pred(A,x,r) == {y:A. <y,x>:r}"

  ord_iso_map :: "[i,i,i,i]=>i"      	(*Construction for linearity theorem*)
   "ord_iso_map(A,r,B,s) ==
     UN x:A. UN y:B. UN f: ord_iso(pred(A,x,r), r, pred(B,y,s), s). {<x,y>}"

  first :: "[i, i, i] => o"
    "first(u, X, R) == u:X & (ALL v:X. v~=u --> <u,v> : R)"


syntax (xsymbols)
    ord_iso :: "[i,i,i,i]=>i"      ("(\<langle>_, _\<rangle> \<cong>/ \<langle>_, _\<rangle>)" 51)


(** Basic properties of the definitions **)

(*needed?*)
lemma part_ord_Imp_asym:
    "part_ord(A,r) ==> asym(r Int A*A)"
by (unfold part_ord_def irrefl_def trans_on_def asym_def, blast)

lemma linearE:
    "[| linear(A,r);  x:A;  y:A;
        <x,y>:r ==> P;  x=y ==> P;  <y,x>:r ==> P |]
     ==> P"
by (simp add: linear_def, blast)


(** General properties of well_ord **)

lemma well_ordI:
    "[| wf[A](r); linear(A,r) |] ==> well_ord(A,r)"
apply (simp add: irrefl_def part_ord_def tot_ord_def
                 trans_on_def well_ord_def wf_on_not_refl)
apply (fast elim: linearE wf_on_asym wf_on_chain3)
done

lemma well_ord_is_wf:
    "well_ord(A,r) ==> wf[A](r)"
by (unfold well_ord_def, safe)

lemma well_ord_is_trans_on:
    "well_ord(A,r) ==> trans[A](r)"
by (unfold well_ord_def tot_ord_def part_ord_def, safe)

lemma well_ord_is_linear: "well_ord(A,r) ==> linear(A,r)"
by (unfold well_ord_def tot_ord_def, blast)


(** Derived rules for pred(A,x,r) **)

lemma pred_iff: "y : pred(A,x,r) <-> <y,x>:r & y:A"
by (unfold pred_def, blast)

lemmas predI = conjI [THEN pred_iff [THEN iffD2]]

lemma predE: "[| y: pred(A,x,r);  [| y:A; <y,x>:r |] ==> P |] ==> P"
by (simp add: pred_def)

lemma pred_subset_under: "pred(A,x,r) <= r -`` {x}"
by (simp add: pred_def, blast)

lemma pred_subset: "pred(A,x,r) <= A"
by (simp add: pred_def, blast)

lemma pred_pred_eq:
    "pred(pred(A,x,r), y, r) = pred(A,x,r) Int pred(A,y,r)"
by (simp add: pred_def, blast)

lemma trans_pred_pred_eq:
    "[| trans[A](r);  <y,x>:r;  x:A;  y:A |]
     ==> pred(pred(A,x,r), y, r) = pred(A,y,r)"
by (unfold trans_on_def pred_def, blast)


(** The ordering's properties hold over all subsets of its domain
    [including initial segments of the form pred(A,x,r) **)

(*Note: a relation s such that s<=r need not be a partial ordering*)
lemma part_ord_subset:
    "[| part_ord(A,r);  B<=A |] ==> part_ord(B,r)"
by (unfold part_ord_def irrefl_def trans_on_def, blast)

lemma linear_subset:
    "[| linear(A,r);  B<=A |] ==> linear(B,r)"
by (unfold linear_def, blast)

lemma tot_ord_subset:
    "[| tot_ord(A,r);  B<=A |] ==> tot_ord(B,r)"
apply (unfold tot_ord_def)
apply (fast elim!: part_ord_subset linear_subset)
done

lemma well_ord_subset:
    "[| well_ord(A,r);  B<=A |] ==> well_ord(B,r)"
apply (unfold well_ord_def)
apply (fast elim!: tot_ord_subset wf_on_subset_A)
done


(** Relations restricted to a smaller domain, by Krzysztof Grabczewski **)

lemma irrefl_Int_iff: "irrefl(A,r Int A*A) <-> irrefl(A,r)"
by (unfold irrefl_def, blast)

lemma trans_on_Int_iff: "trans[A](r Int A*A) <-> trans[A](r)"
by (unfold trans_on_def, blast)

lemma part_ord_Int_iff: "part_ord(A,r Int A*A) <-> part_ord(A,r)"
apply (unfold part_ord_def)
apply (simp add: irrefl_Int_iff trans_on_Int_iff)
done

lemma linear_Int_iff: "linear(A,r Int A*A) <-> linear(A,r)"
by (unfold linear_def, blast)

lemma tot_ord_Int_iff: "tot_ord(A,r Int A*A) <-> tot_ord(A,r)"
apply (unfold tot_ord_def)
apply (simp add: part_ord_Int_iff linear_Int_iff)
done

lemma wf_on_Int_iff: "wf[A](r Int A*A) <-> wf[A](r)"
apply (unfold wf_on_def wf_def, fast) (*10 times faster than Blast_tac!*)
done

lemma well_ord_Int_iff: "well_ord(A,r Int A*A) <-> well_ord(A,r)"
apply (unfold well_ord_def)
apply (simp add: tot_ord_Int_iff wf_on_Int_iff)
done


(** Relations over the Empty Set **)

lemma irrefl_0: "irrefl(0,r)"
by (unfold irrefl_def, blast)

lemma trans_on_0: "trans[0](r)"
by (unfold trans_on_def, blast)

lemma part_ord_0: "part_ord(0,r)"
apply (unfold part_ord_def)
apply (simp add: irrefl_0 trans_on_0)
done

lemma linear_0: "linear(0,r)"
by (unfold linear_def, blast)

lemma tot_ord_0: "tot_ord(0,r)"
apply (unfold tot_ord_def)
apply (simp add: part_ord_0 linear_0)
done

lemma wf_on_0: "wf[0](r)"
by (unfold wf_on_def wf_def, blast)

lemma well_ord_0: "well_ord(0,r)"
apply (unfold well_ord_def)
apply (simp add: tot_ord_0 wf_on_0)
done


(** The unit set is well-ordered by the empty relation (Grabczewski) **)

lemma tot_ord_unit: "tot_ord({a},0)"
by (simp add: irrefl_def trans_on_def part_ord_def linear_def tot_ord_def)

lemma wf_on_unit: "wf[{a}](0)"
by (simp add: wf_on_def wf_def, fast)

lemma well_ord_unit: "well_ord({a},0)"
apply (unfold well_ord_def)
apply (simp add: tot_ord_unit wf_on_unit)
done


(** Order-preserving (monotone) maps **)

lemma mono_map_is_fun: "f: mono_map(A,r,B,s) ==> f: A->B"
by (simp add: mono_map_def)

lemma mono_map_is_inj:
    "[| linear(A,r);  wf[B](s);  f: mono_map(A,r,B,s) |] ==> f: inj(A,B)"
apply (unfold mono_map_def inj_def, clarify)
apply (erule_tac x=w and y=x in linearE, assumption+)
apply (force intro: apply_type dest: wf_on_not_refl)+
done


(** Order-isomorphisms -- or similarities, as Suppes calls them **)

lemma ord_isoI:
    "[| f: bij(A, B);
        !!x y. [| x:A; y:A |] ==> <x, y> : r <-> <f`x, f`y> : s |]
     ==> f: ord_iso(A,r,B,s)"
by (simp add: ord_iso_def)

lemma ord_iso_is_mono_map:
    "f: ord_iso(A,r,B,s) ==> f: mono_map(A,r,B,s)"
apply (simp add: ord_iso_def mono_map_def)
apply (blast dest!: bij_is_fun)
done

lemma ord_iso_is_bij:
    "f: ord_iso(A,r,B,s) ==> f: bij(A,B)"
by (simp add: ord_iso_def)

(*Needed?  But ord_iso_converse is!*)
lemma ord_iso_apply:
    "[| f: ord_iso(A,r,B,s);  <x,y>: r;  x:A;  y:A |] ==> <f`x, f`y> : s"
by (simp add: ord_iso_def, blast)

lemma ord_iso_converse:
    "[| f: ord_iso(A,r,B,s);  <x,y>: s;  x:B;  y:B |]
     ==> <converse(f) ` x, converse(f) ` y> : r"
apply (simp add: ord_iso_def, clarify)
apply (erule bspec [THEN bspec, THEN iffD2])
apply (erule asm_rl bij_converse_bij [THEN bij_is_fun, THEN apply_type])+
apply (auto simp add: right_inverse_bij)
done


(** Symmetry and Transitivity Rules **)

(*Reflexivity of similarity*)
lemma ord_iso_refl: "id(A): ord_iso(A,r,A,r)"
by (rule id_bij [THEN ord_isoI], simp)

(*Symmetry of similarity*)
lemma ord_iso_sym: "f: ord_iso(A,r,B,s) ==> converse(f): ord_iso(B,s,A,r)"
apply (simp add: ord_iso_def)
apply (auto simp add: right_inverse_bij bij_converse_bij
                      bij_is_fun [THEN apply_funtype])
done

(*Transitivity of similarity*)
lemma mono_map_trans:
    "[| g: mono_map(A,r,B,s);  f: mono_map(B,s,C,t) |]
     ==> (f O g): mono_map(A,r,C,t)"
apply (unfold mono_map_def)
apply (auto simp add: comp_fun)
done

(*Transitivity of similarity: the order-isomorphism relation*)
lemma ord_iso_trans:
    "[| g: ord_iso(A,r,B,s);  f: ord_iso(B,s,C,t) |]
     ==> (f O g): ord_iso(A,r,C,t)"
apply (unfold ord_iso_def, clarify)
apply (frule bij_is_fun [of f])
apply (frule bij_is_fun [of g])
apply (auto simp add: comp_bij)
done

(** Two monotone maps can make an order-isomorphism **)

lemma mono_ord_isoI:
    "[| f: mono_map(A,r,B,s);  g: mono_map(B,s,A,r);
        f O g = id(B);  g O f = id(A) |] ==> f: ord_iso(A,r,B,s)"
apply (simp add: ord_iso_def mono_map_def, safe)
apply (intro fg_imp_bijective, auto)
apply (subgoal_tac "<g` (f`x), g` (f`y) > : r")
apply (simp add: comp_eq_id_iff [THEN iffD1])
apply (blast intro: apply_funtype)
done

lemma well_ord_mono_ord_isoI:
     "[| well_ord(A,r);  well_ord(B,s);
         f: mono_map(A,r,B,s);  converse(f): mono_map(B,s,A,r) |]
      ==> f: ord_iso(A,r,B,s)"
apply (intro mono_ord_isoI, auto)
apply (frule mono_map_is_fun [THEN fun_is_rel])
apply (erule converse_converse [THEN subst], rule left_comp_inverse)
apply (blast intro: left_comp_inverse mono_map_is_inj well_ord_is_linear
                    well_ord_is_wf)+
done


(** Order-isomorphisms preserve the ordering's properties **)

lemma part_ord_ord_iso:
    "[| part_ord(B,s);  f: ord_iso(A,r,B,s) |] ==> part_ord(A,r)"
apply (simp add: part_ord_def irrefl_def trans_on_def ord_iso_def)
apply (fast intro: bij_is_fun [THEN apply_type])
done

lemma linear_ord_iso:
    "[| linear(B,s);  f: ord_iso(A,r,B,s) |] ==> linear(A,r)"
apply (simp add: linear_def ord_iso_def, safe)
apply (drule_tac x1 = "f`x" and x = "f`y" in bspec [THEN bspec])
apply (safe elim!: bij_is_fun [THEN apply_type])
apply (drule_tac t = "op ` (converse (f))" in subst_context)
apply (simp add: left_inverse_bij)
done

lemma wf_on_ord_iso:
    "[| wf[B](s);  f: ord_iso(A,r,B,s) |] ==> wf[A](r)"
apply (simp add: wf_on_def wf_def ord_iso_def, safe)
apply (drule_tac x = "{f`z. z:Z Int A}" in spec)
apply (safe intro!: equalityI)
apply (blast dest!: equalityD1 intro: bij_is_fun [THEN apply_type])+
done

lemma well_ord_ord_iso:
    "[| well_ord(B,s);  f: ord_iso(A,r,B,s) |] ==> well_ord(A,r)"
apply (unfold well_ord_def tot_ord_def)
apply (fast elim!: part_ord_ord_iso linear_ord_iso wf_on_ord_iso)
done


(*** Main results of Kunen, Chapter 1 section 6 ***)

(*Inductive argument for Kunen's Lemma 6.1, etc.
  Simple proof from Halmos, page 72*)
lemma well_ord_iso_subset_lemma:
     "[| well_ord(A,r);  f: ord_iso(A,r, A',r);  A'<= A;  y: A |]
      ==> ~ <f`y, y>: r"
apply (simp add: well_ord_def ord_iso_def)
apply (elim conjE CollectE)
apply (rule_tac a=y in wf_on_induct, assumption+)
apply (blast dest: bij_is_fun [THEN apply_type])
done

(*Kunen's Lemma 6.1: there's no order-isomorphism to an initial segment
                     of a well-ordering*)
lemma well_ord_iso_predE:
     "[| well_ord(A,r);  f : ord_iso(A, r, pred(A,x,r), r);  x:A |] ==> P"
apply (insert well_ord_iso_subset_lemma [of A r f "pred(A,x,r)" x])
apply (simp add: pred_subset)
(*Now we know  f`x < x *)
apply (drule ord_iso_is_bij [THEN bij_is_fun, THEN apply_type], assumption)
(*Now we also know f`x : pred(A,x,r);  contradiction! *)
apply (simp add: well_ord_def pred_def)
done

(*Simple consequence of Lemma 6.1*)
lemma well_ord_iso_pred_eq:
     "[| well_ord(A,r);  f : ord_iso(pred(A,a,r), r, pred(A,c,r), r);
         a:A;  c:A |] ==> a=c"
apply (frule well_ord_is_trans_on)
apply (frule well_ord_is_linear)
apply (erule_tac x=a and y=c in linearE, assumption+)
apply (drule ord_iso_sym)
(*two symmetric cases*)
apply (auto elim!: well_ord_subset [OF _ pred_subset, THEN well_ord_iso_predE]
            intro!: predI
            simp add: trans_pred_pred_eq)
done

(*Does not assume r is a wellordering!*)
lemma ord_iso_image_pred:
     "[|f : ord_iso(A,r,B,s);  a:A|] ==> f `` pred(A,a,r) = pred(B, f`a, s)"
apply (unfold ord_iso_def pred_def)
apply (erule CollectE)
apply (simp (no_asm_simp) add: image_fun [OF bij_is_fun Collect_subset])
apply (rule equalityI)
apply (safe elim!: bij_is_fun [THEN apply_type])
apply (rule RepFun_eqI)
apply (blast intro!: right_inverse_bij [symmetric])
apply (auto simp add: right_inverse_bij  bij_is_fun [THEN apply_funtype])
done

lemma ord_iso_restrict_image:
     "[| f : ord_iso(A,r,B,s);  C<=A |] 
      ==> restrict(f,C) : ord_iso(C, r, f``C, s)"
apply (simp add: ord_iso_def) 
apply (blast intro: bij_is_inj restrict_bij) 
done

(*But in use, A and B may themselves be initial segments.  Then use
  trans_pred_pred_eq to simplify the pred(pred...) terms.  See just below.*)
lemma ord_iso_restrict_pred:
   "[| f : ord_iso(A,r,B,s);   a:A |]
    ==> restrict(f, pred(A,a,r)) : ord_iso(pred(A,a,r), r, pred(B, f`a, s), s)"
apply (simp add: ord_iso_image_pred [symmetric]) 
apply (blast intro: ord_iso_restrict_image elim: predE) 
done

(*Tricky; a lot of forward proof!*)
lemma well_ord_iso_preserving:
     "[| well_ord(A,r);  well_ord(B,s);  <a,c>: r;
         f : ord_iso(pred(A,a,r), r, pred(B,b,s), s);
         g : ord_iso(pred(A,c,r), r, pred(B,d,s), s);
         a:A;  c:A;  b:B;  d:B |] ==> <b,d>: s"
apply (frule ord_iso_is_bij [THEN bij_is_fun, THEN apply_type], (erule asm_rl predI predE)+)
apply (subgoal_tac "b = g`a")
apply (simp (no_asm_simp))
apply (rule well_ord_iso_pred_eq, auto)
apply (frule ord_iso_restrict_pred, (erule asm_rl predI)+)
apply (simp add: well_ord_is_trans_on trans_pred_pred_eq)
apply (erule ord_iso_sym [THEN ord_iso_trans], assumption)
done

(*See Halmos, page 72*)
lemma well_ord_iso_unique_lemma:
     "[| well_ord(A,r);
         f: ord_iso(A,r, B,s);  g: ord_iso(A,r, B,s);  y: A |]
      ==> ~ <g`y, f`y> : s"
apply (frule well_ord_iso_subset_lemma)
apply (rule_tac f = "converse (f) " and g = g in ord_iso_trans)
apply auto
apply (blast intro: ord_iso_sym)
apply (frule ord_iso_is_bij [of f])
apply (frule ord_iso_is_bij [of g])
apply (frule ord_iso_converse)
apply (blast intro!: bij_converse_bij
             intro: bij_is_fun apply_funtype)+
apply (erule notE)
apply (simp add: left_inverse_bij bij_is_fun comp_fun_apply [of _ A B])
done


(*Kunen's Lemma 6.2: Order-isomorphisms between well-orderings are unique*)
lemma well_ord_iso_unique: "[| well_ord(A,r);
         f: ord_iso(A,r, B,s);  g: ord_iso(A,r, B,s) |] ==> f = g"
apply (rule fun_extension)
apply (erule ord_iso_is_bij [THEN bij_is_fun])+
apply (subgoal_tac "f`x : B & g`x : B & linear(B,s)")
 apply (simp add: linear_def)
 apply (blast dest: well_ord_iso_unique_lemma)
apply (blast intro: ord_iso_is_bij bij_is_fun apply_funtype
                    well_ord_is_linear well_ord_ord_iso ord_iso_sym)
done

(** Towards Kunen's Theorem 6.3: linearity of the similarity relation **)

lemma ord_iso_map_subset: "ord_iso_map(A,r,B,s) <= A*B"
by (unfold ord_iso_map_def, blast)

lemma domain_ord_iso_map: "domain(ord_iso_map(A,r,B,s)) <= A"
by (unfold ord_iso_map_def, blast)

lemma range_ord_iso_map: "range(ord_iso_map(A,r,B,s)) <= B"
by (unfold ord_iso_map_def, blast)

lemma converse_ord_iso_map:
    "converse(ord_iso_map(A,r,B,s)) = ord_iso_map(B,s,A,r)"
apply (unfold ord_iso_map_def)
apply (blast intro: ord_iso_sym)
done

lemma function_ord_iso_map:
    "well_ord(B,s) ==> function(ord_iso_map(A,r,B,s))"
apply (unfold ord_iso_map_def function_def)
apply (blast intro: well_ord_iso_pred_eq ord_iso_sym ord_iso_trans)
done

lemma ord_iso_map_fun: "well_ord(B,s) ==> ord_iso_map(A,r,B,s)
           : domain(ord_iso_map(A,r,B,s)) -> range(ord_iso_map(A,r,B,s))"
by (simp add: Pi_iff function_ord_iso_map
                 ord_iso_map_subset [THEN domain_times_range])

lemma ord_iso_map_mono_map:
    "[| well_ord(A,r);  well_ord(B,s) |]
     ==> ord_iso_map(A,r,B,s)
           : mono_map(domain(ord_iso_map(A,r,B,s)), r,
                      range(ord_iso_map(A,r,B,s)), s)"
apply (unfold mono_map_def)
apply (simp (no_asm_simp) add: ord_iso_map_fun)
apply safe
apply (subgoal_tac "x:A & ya:A & y:B & yb:B")
 apply (simp add: apply_equality [OF _  ord_iso_map_fun])
 apply (unfold ord_iso_map_def)
 apply (blast intro: well_ord_iso_preserving, blast)
done

lemma ord_iso_map_ord_iso:
    "[| well_ord(A,r);  well_ord(B,s) |] ==> ord_iso_map(A,r,B,s)
           : ord_iso(domain(ord_iso_map(A,r,B,s)), r,
                      range(ord_iso_map(A,r,B,s)), s)"
apply (rule well_ord_mono_ord_isoI)
   prefer 4
   apply (rule converse_ord_iso_map [THEN subst])
   apply (simp add: ord_iso_map_mono_map
		    ord_iso_map_subset [THEN converse_converse])
apply (blast intro!: domain_ord_iso_map range_ord_iso_map
             intro: well_ord_subset ord_iso_map_mono_map)+
done


(*One way of saying that domain(ord_iso_map(A,r,B,s)) is downwards-closed*)
lemma domain_ord_iso_map_subset:
     "[| well_ord(A,r);  well_ord(B,s);
         a: A;  a ~: domain(ord_iso_map(A,r,B,s)) |]
      ==>  domain(ord_iso_map(A,r,B,s)) <= pred(A, a, r)"
apply (unfold ord_iso_map_def)
apply (safe intro!: predI)
(*Case analysis on  xa vs a in r *)
apply (simp (no_asm_simp))
apply (frule_tac A = A in well_ord_is_linear)
apply (rename_tac b y f)
apply (erule_tac x=b and y=a in linearE, assumption+)
(*Trivial case: b=a*)
apply clarify
apply blast
(*Harder case: <a, xa>: r*)
apply (frule ord_iso_is_bij [THEN bij_is_fun, THEN apply_type],
       (erule asm_rl predI predE)+)
apply (frule ord_iso_restrict_pred)
 apply (simp add: pred_iff)
apply (simp split: split_if_asm
          add: well_ord_is_trans_on trans_pred_pred_eq domain_UN domain_Union, blast)
done

(*For the 4-way case analysis in the main result*)
lemma domain_ord_iso_map_cases:
     "[| well_ord(A,r);  well_ord(B,s) |]
      ==> domain(ord_iso_map(A,r,B,s)) = A |
          (EX x:A. domain(ord_iso_map(A,r,B,s)) = pred(A,x,r))"
apply (frule well_ord_is_wf)
apply (unfold wf_on_def wf_def)
apply (drule_tac x = "A-domain (ord_iso_map (A,r,B,s))" in spec)
apply safe
(*The first case: the domain equals A*)
apply (rule domain_ord_iso_map [THEN equalityI])
apply (erule Diff_eq_0_iff [THEN iffD1])
(*The other case: the domain equals an initial segment*)
apply (blast del: domainI subsetI
	     elim!: predE
	     intro!: domain_ord_iso_map_subset
             intro: subsetI)+
done

(*As above, by duality*)
lemma range_ord_iso_map_cases:
    "[| well_ord(A,r);  well_ord(B,s) |]
     ==> range(ord_iso_map(A,r,B,s)) = B |
         (EX y:B. range(ord_iso_map(A,r,B,s)) = pred(B,y,s))"
apply (rule converse_ord_iso_map [THEN subst])
apply (simp add: domain_ord_iso_map_cases)
done

(*Kunen's Theorem 6.3: Fundamental Theorem for Well-Ordered Sets*)
lemma well_ord_trichotomy:
   "[| well_ord(A,r);  well_ord(B,s) |]
    ==> ord_iso_map(A,r,B,s) : ord_iso(A, r, B, s) |
        (EX x:A. ord_iso_map(A,r,B,s) : ord_iso(pred(A,x,r), r, B, s)) |
        (EX y:B. ord_iso_map(A,r,B,s) : ord_iso(A, r, pred(B,y,s), s))"
apply (frule_tac B = B in domain_ord_iso_map_cases, assumption)
apply (frule_tac B = B in range_ord_iso_map_cases, assumption)
apply (drule ord_iso_map_ord_iso, assumption)
apply (elim disjE bexE)
   apply (simp_all add: bexI)
apply (rule wf_on_not_refl [THEN notE])
  apply (erule well_ord_is_wf)
 apply assumption
apply (subgoal_tac "<x,y>: ord_iso_map (A,r,B,s) ")
 apply (drule rangeI)
 apply (simp add: pred_def)
apply (unfold ord_iso_map_def, blast)
done


(*** Properties of converse(r), by Krzysztof Grabczewski ***)

lemma irrefl_converse: "irrefl(A,r) ==> irrefl(A,converse(r))"
by (unfold irrefl_def, blast)

lemma trans_on_converse: "trans[A](r) ==> trans[A](converse(r))"
by (unfold trans_on_def, blast)

lemma part_ord_converse: "part_ord(A,r) ==> part_ord(A,converse(r))"
apply (unfold part_ord_def)
apply (blast intro!: irrefl_converse trans_on_converse)
done

lemma linear_converse: "linear(A,r) ==> linear(A,converse(r))"
by (unfold linear_def, blast)

lemma tot_ord_converse: "tot_ord(A,r) ==> tot_ord(A,converse(r))"
apply (unfold tot_ord_def)
apply (blast intro!: part_ord_converse linear_converse)
done


(** By Krzysztof Grabczewski.
    Lemmas involving the first element of a well ordered set **)

lemma first_is_elem: "first(b,B,r) ==> b:B"
by (unfold first_def, blast)

lemma well_ord_imp_ex1_first:
        "[| well_ord(A,r); B<=A; B~=0 |] ==> (EX! b. first(b,B,r))"
apply (unfold well_ord_def wf_on_def wf_def first_def)
apply (elim conjE allE disjE, blast)
apply (erule bexE)
apply (rule_tac a = x in ex1I, auto)
apply (unfold tot_ord_def linear_def, blast)
done

lemma the_first_in:
     "[| well_ord(A,r); B<=A; B~=0 |] ==> (THE b. first(b,B,r)) : B"
apply (drule well_ord_imp_ex1_first, assumption+)
apply (rule first_is_elem)
apply (erule theI)
done

ML {*
val pred_def = thm "pred_def"
val linear_def = thm "linear_def"
val part_ord_def = thm "part_ord_def"
val tot_ord_def = thm "tot_ord_def"
val well_ord_def = thm "well_ord_def"
val ord_iso_def = thm "ord_iso_def"
val mono_map_def = thm "mono_map_def";

val part_ord_Imp_asym = thm "part_ord_Imp_asym";
val linearE = thm "linearE";
val well_ordI = thm "well_ordI";
val well_ord_is_wf = thm "well_ord_is_wf";
val well_ord_is_trans_on = thm "well_ord_is_trans_on";
val well_ord_is_linear = thm "well_ord_is_linear";
val pred_iff = thm "pred_iff";
val predI = thm "predI";
val predE = thm "predE";
val pred_subset_under = thm "pred_subset_under";
val pred_subset = thm "pred_subset";
val pred_pred_eq = thm "pred_pred_eq";
val trans_pred_pred_eq = thm "trans_pred_pred_eq";
val part_ord_subset = thm "part_ord_subset";
val linear_subset = thm "linear_subset";
val tot_ord_subset = thm "tot_ord_subset";
val well_ord_subset = thm "well_ord_subset";
val irrefl_Int_iff = thm "irrefl_Int_iff";
val trans_on_Int_iff = thm "trans_on_Int_iff";
val part_ord_Int_iff = thm "part_ord_Int_iff";
val linear_Int_iff = thm "linear_Int_iff";
val tot_ord_Int_iff = thm "tot_ord_Int_iff";
val wf_on_Int_iff = thm "wf_on_Int_iff";
val well_ord_Int_iff = thm "well_ord_Int_iff";
val irrefl_0 = thm "irrefl_0";
val trans_on_0 = thm "trans_on_0";
val part_ord_0 = thm "part_ord_0";
val linear_0 = thm "linear_0";
val tot_ord_0 = thm "tot_ord_0";
val wf_on_0 = thm "wf_on_0";
val well_ord_0 = thm "well_ord_0";
val tot_ord_unit = thm "tot_ord_unit";
val wf_on_unit = thm "wf_on_unit";
val well_ord_unit = thm "well_ord_unit";
val mono_map_is_fun = thm "mono_map_is_fun";
val mono_map_is_inj = thm "mono_map_is_inj";
val ord_isoI = thm "ord_isoI";
val ord_iso_is_mono_map = thm "ord_iso_is_mono_map";
val ord_iso_is_bij = thm "ord_iso_is_bij";
val ord_iso_apply = thm "ord_iso_apply";
val ord_iso_converse = thm "ord_iso_converse";
val ord_iso_refl = thm "ord_iso_refl";
val ord_iso_sym = thm "ord_iso_sym";
val mono_map_trans = thm "mono_map_trans";
val ord_iso_trans = thm "ord_iso_trans";
val mono_ord_isoI = thm "mono_ord_isoI";
val well_ord_mono_ord_isoI = thm "well_ord_mono_ord_isoI";
val part_ord_ord_iso = thm "part_ord_ord_iso";
val linear_ord_iso = thm "linear_ord_iso";
val wf_on_ord_iso = thm "wf_on_ord_iso";
val well_ord_ord_iso = thm "well_ord_ord_iso";
val well_ord_iso_predE = thm "well_ord_iso_predE";
val well_ord_iso_pred_eq = thm "well_ord_iso_pred_eq";
val ord_iso_image_pred = thm "ord_iso_image_pred";
val ord_iso_restrict_pred = thm "ord_iso_restrict_pred";
val well_ord_iso_preserving = thm "well_ord_iso_preserving";
val well_ord_iso_unique = thm "well_ord_iso_unique";
val ord_iso_map_subset = thm "ord_iso_map_subset";
val domain_ord_iso_map = thm "domain_ord_iso_map";
val range_ord_iso_map = thm "range_ord_iso_map";
val converse_ord_iso_map = thm "converse_ord_iso_map";
val function_ord_iso_map = thm "function_ord_iso_map";
val ord_iso_map_fun = thm "ord_iso_map_fun";
val ord_iso_map_mono_map = thm "ord_iso_map_mono_map";
val ord_iso_map_ord_iso = thm "ord_iso_map_ord_iso";
val domain_ord_iso_map_subset = thm "domain_ord_iso_map_subset";
val domain_ord_iso_map_cases = thm "domain_ord_iso_map_cases";
val range_ord_iso_map_cases = thm "range_ord_iso_map_cases";
val well_ord_trichotomy = thm "well_ord_trichotomy";
val irrefl_converse = thm "irrefl_converse";
val trans_on_converse = thm "trans_on_converse";
val part_ord_converse = thm "part_ord_converse";
val linear_converse = thm "linear_converse";
val tot_ord_converse = thm "tot_ord_converse";
val first_is_elem = thm "first_is_elem";
val well_ord_imp_ex1_first = thm "well_ord_imp_ex1_first";
val the_first_in = thm "the_first_in";
*}

end
