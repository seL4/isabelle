(*  Title:      ZF/ex/LList.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Codatatype definition of Lazy Lists
*)

(*These commands cause classical reasoning to regard the subset relation
  as primitive, not reducing it to membership*)
  
Delrules [subsetI, subsetCE];
AddSIs [subset_refl, cons_subsetI, subset_consI, 
	Union_least, UN_least, Un_least, 
	Inter_greatest, Int_greatest, RepFun_subset,
	Un_upper1, Un_upper2, Int_lower1, Int_lower2];

(*An elimination rule, for type-checking*)
val LConsE = llist.mk_cases "LCons(a,l) : llist(A)";

(*Proving freeness results*)
val LCons_iff      = llist.mk_free "LCons(a,l)=LCons(a',l') <-> a=a' & l=l'";
val LNil_LCons_iff = llist.mk_free "~ LNil=LCons(a,l)";

Goal "llist(A) = {0} <+> (A <*> llist(A))";
let open llist  val rew = rewrite_rule con_defs in  
by (fast_tac (claset() addSIs (subsetI ::map rew intrs) addEs [rew elim]) 1)
end;
qed "llist_unfold";

(*** Lemmas to justify using "llist" in other recursive type definitions ***)

Goalw llist.defs "A<=B ==> llist(A) <= llist(B)";
by (rtac gfp_mono 1);
by (REPEAT (rtac llist.bnd_mono 1));
by (REPEAT (ares_tac (quniv_mono::basic_monos) 1));
qed "llist_mono";

(** Closure of quniv(A) under llist -- why so complex?  Its a gfp... **)

AddSIs [QPair_Int_Vset_subset_UN RS subset_trans, 
                                 QPair_subset_univ,
                                 empty_subsetI, one_in_quniv RS qunivD];
AddSDs [qunivD];
AddSEs [Ord_in_Ord];

Goal "Ord(i) ==> ALL l: llist(quniv(A)). l Int Vset(i) <= univ(eclose(A))";
by (etac trans_induct 1);
by (rtac ballI 1);
by (etac llist.elim 1);
by (rewrite_goals_tac ([QInl_def,QInr_def]@llist.con_defs));
(*LNil case*)
by (Asm_simp_tac 1);
(*LCons case*)
by (deepen_tac (claset() addIs [Ord_trans, Int_lower1 RS subset_trans]) 2 1);
qed "llist_quniv_lemma";

Goal "llist(quniv(A)) <= quniv(A)";
by (rtac (qunivI RS subsetI) 1);
by (rtac Int_Vset_subset 1);
by (REPEAT (ares_tac [llist_quniv_lemma RS bspec] 1));
qed "llist_quniv";

bind_thm ("llist_subset_quniv",
    (llist_mono RS (llist_quniv RSN (2,subset_trans))));


(*** Lazy List Equality: lleq ***)

AddSIs [QPair_Int_Vset_subset_UN RS subset_trans, QPair_mono];
AddSEs [Ord_in_Ord, Pair_inject];

(*Lemma for proving finality.  Unfold the lazy list; use induction hypothesis*)
Goal "Ord(i) ==> ALL l l'. <l,l'> : lleq(A) --> l Int Vset(i) <= l'";
by (etac trans_induct 1);
by (REPEAT (resolve_tac [allI, impI] 1));
by (etac lleq.elim 1);
by (rewrite_goals_tac (QInr_def::llist.con_defs));
by Safe_tac;
by (fast_tac (subset_cs addSEs [Ord_trans, make_elim bspec]) 1);
qed "lleq_Int_Vset_subset_lemma";

bind_thm ("lleq_Int_Vset_subset",
        (lleq_Int_Vset_subset_lemma RS spec RS spec RS mp));


(*lleq(A) is a symmetric relation because qconverse(lleq(A)) is a fixedpoint*)
val [prem] = goal LList.thy "<l,l'> : lleq(A) ==> <l',l> : lleq(A)";
by (rtac (prem RS converseI RS lleq.coinduct) 1);
by (rtac (lleq.dom_subset RS converse_type) 1);
by Safe_tac;
by (etac lleq.elim 1);
by (ALLGOALS Fast_tac);
qed "lleq_symmetric";

Goal "<l,l'> : lleq(A) ==> l=l'";
by (rtac equalityI 1);
by (REPEAT (ares_tac [lleq_Int_Vset_subset RS Int_Vset_subset] 1
     ORELSE etac lleq_symmetric 1));
qed "lleq_implies_equal";

val [eqprem,lprem] = goal LList.thy
    "[| l=l';  l: llist(A) |] ==> <l,l'> : lleq(A)";
by (res_inst_tac [("X", "{<l,l>. l: llist(A)}")] lleq.coinduct 1);
by (rtac (lprem RS RepFunI RS (eqprem RS subst)) 1);
by Safe_tac;
by (etac llist.elim 1);
by (ALLGOALS Fast_tac);
qed "equal_llist_implies_leq";


(*** Lazy List Functions ***)

(*Examples of coinduction for type-checking and to prove llist equations*)

(*** lconst -- defined directly using lfp, but equivalent to a LList_corec ***)

Goalw llist.con_defs "bnd_mono(univ(a), %l. LCons(a,l))";
by (rtac bnd_monoI 1);
by (REPEAT (ares_tac [subset_refl, QInr_mono, QPair_mono] 2));
by (REPEAT (ares_tac [subset_refl, A_subset_univ, 
                      QInr_subset_univ, QPair_subset_univ] 1));
qed "lconst_fun_bnd_mono";

(* lconst(a) = LCons(a,lconst(a)) *)
bind_thm ("lconst",
    ([lconst_def, lconst_fun_bnd_mono] MRS def_lfp_unfold));

val lconst_subset = lconst_def RS def_lfp_subset;

bind_thm ("member_subset_Union_eclose", (arg_into_eclose RS Union_upper));

Goal "a : A ==> lconst(a) : quniv(A)";
by (rtac (lconst_subset RS subset_trans RS qunivI) 1);
by (etac (arg_into_eclose RS eclose_subset RS univ_mono) 1);
qed "lconst_in_quniv";

Goal "a:A ==> lconst(a): llist(A)";
by (rtac (singletonI RS llist.coinduct) 1);
by (etac (lconst_in_quniv RS singleton_subsetI) 1);
by (fast_tac (claset() addSIs [lconst]) 1);
qed "lconst_type";

(*** flip --- equations merely assumed; certain consequences proved ***)

Addsimps [flip_LNil, flip_LCons, not_type];

goal QUniv.thy "!!b. b:bool ==> b Int X <= univ(eclose(A))";
by (fast_tac (claset() addIs [Int_lower1 RS subset_trans] addSEs [boolE]) 1);
qed "bool_Int_subset_univ";

AddSIs [not_type];
AddIs  [bool_Int_subset_univ];

(*Reasoning borrowed from lleq.ML; a similar proof works for all
  "productive" functions -- cf Coquand's "Infinite Objects in Type Theory".*)
Goal "Ord(i) ==> ALL l: llist(bool). flip(l) Int Vset(i) <= \
\                   univ(eclose(bool))";
by (etac trans_induct 1);
by (rtac ballI 1);
by (etac llist.elim 1);
by (ALLGOALS Asm_simp_tac);
by (ALLGOALS 
    (asm_simp_tac (simpset() addsimps [QInl_def,QInr_def] @ llist.con_defs)));
(*LCons case*)
by (deepen_tac (claset() addIs [Ord_trans, Int_lower1 RS subset_trans]) 2 1);
qed "flip_llist_quniv_lemma";

Goal "l: llist(bool) ==> flip(l) : quniv(bool)";
by (rtac (flip_llist_quniv_lemma RS bspec RS Int_Vset_subset RS qunivI) 1);
by (REPEAT (assume_tac 1));
qed "flip_in_quniv";

val [prem] = goal LList.thy "l : llist(bool) ==> flip(l): llist(bool)";
by (res_inst_tac [("X", "{flip(l) . l:llist(bool)}")]
       llist.coinduct 1);
by (rtac (prem RS RepFunI) 1);
by (fast_tac (claset() addSIs [flip_in_quniv]) 1);
by (etac RepFunE 1);
by (etac llist.elim 1);
by (ALLGOALS Asm_simp_tac);
by (Fast_tac 1);
qed "flip_type";

val [prem] = goal LList.thy
    "l : llist(bool) ==> flip(flip(l)) = l";
by (res_inst_tac [("X1", "{<flip(flip(l)),l> . l:llist(bool)}")]
       (lleq.coinduct RS lleq_implies_equal) 1);
by (rtac (prem RS RepFunI) 1);
by (fast_tac (claset() addSIs [flip_type]) 1);
by (etac RepFunE 1);
by (etac llist.elim 1);
by (Asm_simp_tac 1);
by (asm_full_simp_tac (simpset() addsimps [flip_type, not_not]) 1);
qed "flip_flip";
