(*  Title:      HOL/Induct/LList
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

SHOULD LListD_Fun_CONS_I, etc., be equations (for rewriting)?
*)

bind_thm ("UN1_I", UNIV_I RS UN_I);

(** Simplification **)

Addsplits [option.split];

(*This justifies using llist in other recursive type definitions*)
Goalw llist.defs "A<=B ==> llist(A) <= llist(B)";
by (rtac gfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "llist_mono";


Goal "llist(A) = usum {Numb(0)} (uprod A (llist A))";
let val rew = rewrite_rule [NIL_def, CONS_def] in  
by (fast_tac (claset() addSIs (map rew llist.intrs)
                       addEs [rew llist.elim]) 1)
end;
qed "llist_unfold";


(*** Type checking by coinduction, using list_Fun 
     THE COINDUCTIVE DEFINITION PACKAGE COULD DO THIS!
***)

Goalw [list_Fun_def]
    "[| M : X;  X <= list_Fun A (X Un llist(A)) |] ==>  M : llist(A)";
by (etac llist.coinduct 1);
by (etac (subsetD RS CollectD) 1);
by (assume_tac 1);
qed "llist_coinduct";

Goalw [list_Fun_def, NIL_def] "NIL: list_Fun A X";
by (Fast_tac 1);
qed "list_Fun_NIL_I";
AddIffs [list_Fun_NIL_I];

Goalw [list_Fun_def,CONS_def]
    "[| M: A;  N: X |] ==> CONS M N : list_Fun A X";
by (Fast_tac 1);
qed "list_Fun_CONS_I";
Addsimps [list_Fun_CONS_I];
AddSIs   [list_Fun_CONS_I];

(*Utilise the "strong" part, i.e. gfp(f)*)
Goalw (llist.defs @ [list_Fun_def])
    "M: llist(A) ==> M : list_Fun A (X Un llist(A))";
by (etac (llist.mono RS gfp_fun_UnI2) 1);
qed "list_Fun_llist_I";

(*** LList_corec satisfies the desired recurion equation ***)

(*A continuity result?*)
Goalw [CONS_def] "CONS M (UN x. f(x)) = (UN x. CONS M (f x))";
by (simp_tac (simpset() addsimps [In1_UN1, Scons_UN1_y]) 1);
qed "CONS_UN1";

Goalw [CONS_def] "[| M<=M';  N<=N' |] ==> CONS M N <= CONS M' N'";
by (REPEAT (ares_tac [In1_mono,Scons_mono] 1));
qed "CONS_mono";

Addsimps [LList_corec_fun_def RS def_nat_rec_0,
          LList_corec_fun_def RS def_nat_rec_Suc];

(** The directions of the equality are proved separately **)

Goalw [LList_corec_def]
    "LList_corec a f <= \
\    (case f a of None => NIL | Some(z,w) => CONS z (LList_corec w f))";
by (rtac UN_least 1);
by (case_tac "k" 1);
by (ALLGOALS Asm_simp_tac);
by (REPEAT (resolve_tac [allI, impI, subset_refl RS CONS_mono, 
			 UNIV_I RS UN_upper] 1));
qed "LList_corec_subset1";

Goalw [LList_corec_def]
    "(case f a of None => NIL | Some(z,w) => CONS z (LList_corec w f)) <= \
\    LList_corec a f";
by (simp_tac (simpset() addsimps [CONS_UN1]) 1);
by Safe_tac;
by (ALLGOALS (res_inst_tac [("a","Suc(?k)")] UN_I));
by (ALLGOALS Asm_simp_tac);
qed "LList_corec_subset2";

(*the recursion equation for LList_corec -- NOT SUITABLE FOR REWRITING!*)
Goal "LList_corec a f =  \
\     (case f a of None => NIL | Some(z,w) => CONS z (LList_corec w f))";
by (REPEAT (resolve_tac [equalityI, LList_corec_subset1, 
                         LList_corec_subset2] 1));
qed "LList_corec";

(*definitional version of same*)
val [rew] = 
Goal "[| !!x. h(x) == LList_corec x f |]     \
\     ==> h(a) = (case f a of None => NIL | Some(z,w) => CONS z (h w))";
by (rewtac rew);
by (rtac LList_corec 1);
qed "def_LList_corec";

(*A typical use of co-induction to show membership in the gfp. 
  Bisimulation is  range(%x. LList_corec x f) *)
Goal "LList_corec a f : llist UNIV";
by (res_inst_tac [("X", "range(%x. LList_corec x ?g)")] llist_coinduct 1);
by (rtac rangeI 1);
by Safe_tac;
by (stac LList_corec 1);
by (Simp_tac 1);
qed "LList_corec_type";


(**** llist equality as a gfp; the bisimulation principle ****)

(*This theorem is actually used, unlike the many similar ones in ZF*)
Goal "LListD r = dsum (diag {Numb 0}) (dprod r (LListD r))";
let val rew = rewrite_rule [NIL_def, CONS_def] in  
by (fast_tac (claset() addSIs (map rew LListD.intrs)
                      addEs [rew LListD.elim]) 1)
end;
qed "LListD_unfold";

Goal "!M N. (M,N) : LListD(diag A) --> ntrunc k M = ntrunc k N";
by (res_inst_tac [("n", "k")] less_induct 1);
by (safe_tac (claset() delrules [equalityI]));
by (etac LListD.elim 1);
by (safe_tac (claset() delrules [equalityI]));
by (case_tac "n" 1);
by (Asm_simp_tac 1);
by (rename_tac "n'" 1);
by (case_tac "n'" 1);
by (asm_simp_tac (simpset() addsimps [CONS_def]) 1);
by (asm_simp_tac (simpset() addsimps [CONS_def, less_Suc_eq]) 1);
qed "LListD_implies_ntrunc_equality";

(*The domain of the LListD relation*)
Goalw (llist.defs @ [NIL_def, CONS_def])
    "Domain (LListD(diag A)) <= llist(A)";
by (rtac gfp_upperbound 1);
(*avoids unfolding LListD on the rhs*)
by (res_inst_tac [("P", "%x. Domain x <= ?B")] (LListD_unfold RS ssubst) 1);
by (Simp_tac 1);
by (Fast_tac 1);
qed "Domain_LListD";

(*This inclusion justifies the use of coinduction to show M=N*)
Goal "LListD(diag A) <= diag(llist(A))";
by (rtac subsetI 1);
by (res_inst_tac [("p","x")] PairE 1);
by Safe_tac;
by (rtac diag_eqI 1);
by (rtac (LListD_implies_ntrunc_equality RS spec RS spec RS mp RS 
          ntrunc_equality) 1);
by (assume_tac 1);
by (etac (DomainI RS (Domain_LListD RS subsetD)) 1);
qed "LListD_subset_diag";


(** Coinduction, using LListD_Fun
    THE COINDUCTIVE DEFINITION PACKAGE COULD DO THIS!
 **)

Goalw [LListD_Fun_def] "A<=B ==> LListD_Fun r A <= LListD_Fun r B";
by (REPEAT (ares_tac basic_monos 1));
qed "LListD_Fun_mono";

Goalw [LListD_Fun_def]
    "[| M : X;  X <= LListD_Fun r (X Un LListD(r)) |] ==>  M : LListD(r)";
by (etac LListD.coinduct 1);
by (etac (subsetD RS CollectD) 1);
by (assume_tac 1);
qed "LListD_coinduct";

Goalw [LListD_Fun_def,NIL_def] "(NIL,NIL) : LListD_Fun r s";
by (Fast_tac 1);
qed "LListD_Fun_NIL_I";

Goalw [LListD_Fun_def,CONS_def]
 "[| x:A;  (M,N):s |] ==> (CONS x M, CONS x N) : LListD_Fun (diag A) s";
by (Fast_tac 1);
qed "LListD_Fun_CONS_I";

(*Utilise the "strong" part, i.e. gfp(f)*)
Goalw (LListD.defs @ [LListD_Fun_def])
    "M: LListD(r) ==> M : LListD_Fun r (X Un LListD(r))";
by (etac (LListD.mono RS gfp_fun_UnI2) 1);
qed "LListD_Fun_LListD_I";


(*This converse inclusion helps to strengthen LList_equalityI*)
Goal "diag(llist(A)) <= LListD(diag A)";
by (rtac subsetI 1);
by (etac LListD_coinduct 1);
by (rtac subsetI 1);
by (etac diagE 1);
by (etac ssubst 1);
by (eresolve_tac [llist.elim] 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [diagI, LListD_Fun_NIL_I,
				       LListD_Fun_CONS_I])));
qed "diag_subset_LListD";

Goal "LListD(diag A) = diag(llist(A))";
by (REPEAT (resolve_tac [equalityI, LListD_subset_diag, 
                         diag_subset_LListD] 1));
qed "LListD_eq_diag";

Goal "M: llist(A) ==> (M,M) : LListD_Fun (diag A) (X Un diag(llist(A)))";
by (rtac (LListD_eq_diag RS subst) 1);
by (rtac LListD_Fun_LListD_I 1);
by (asm_simp_tac (simpset() addsimps [LListD_eq_diag, diagI]) 1);
qed "LListD_Fun_diag_I";


(** To show two LLists are equal, exhibit a bisimulation! 
      [also admits true equality]
   Replace "A" by some particular set, like {x.True}??? *)
Goal "[| (M,N) : r;  r <= LListD_Fun (diag A) (r Un diag(llist(A))) \
\         |] ==>  M=N";
by (rtac (LListD_subset_diag RS subsetD RS diagE) 1);
by (etac LListD_coinduct 1);
by (asm_simp_tac (simpset() addsimps [LListD_eq_diag]) 1);
by Safe_tac;
qed "LList_equalityI";


(*** Finality of llist(A): Uniqueness of functions defined by corecursion ***)

(*We must remove Pair_eq because it may turn an instance of reflexivity
  (h1 b, h2 b) = (h1 ?x17, h2 ?x17) into a conjunction! 
  (or strengthen the Solver?) 
*)
Delsimps [Pair_eq];

(*abstract proof using a bisimulation*)
val [prem1,prem2] = 
Goal
 "[| !!x. h1(x) = (case f x of None => NIL | Some(z,w) => CONS z (h1 w));  \
\    !!x. h2(x) = (case f x of None => NIL | Some(z,w) => CONS z (h2 w)) |]\
\ ==> h1=h2";
by (rtac ext 1);
(*next step avoids an unknown (and flexflex pair) in simplification*)
by (res_inst_tac [("A", "UNIV"),
                  ("r", "range(%u. (h1(u),h2(u)))")] LList_equalityI 1);
by (rtac rangeI 1);
by Safe_tac;
by (stac prem1 1);
by (stac prem2 1);
by (simp_tac (simpset() addsimps [LListD_Fun_NIL_I,
				  UNIV_I RS LListD_Fun_CONS_I]) 1);
qed "LList_corec_unique";

val [prem] = 
Goal 
 "[| !!x. h(x) = (case f x of None => NIL | Some(z,w) => CONS z (h w)) |] \
\ ==> h = (%x. LList_corec x f)";
by (rtac (LList_corec RS (prem RS LList_corec_unique)) 1);
qed "equals_LList_corec";


(** Obsolete LList_corec_unique proof: complete induction, not coinduction **)

Goalw [CONS_def] "ntrunc (Suc 0) (CONS M N) = {}";
by (rtac ntrunc_one_In1 1);
qed "ntrunc_one_CONS";

Goalw [CONS_def]
    "ntrunc (Suc(Suc(k))) (CONS M N) = CONS (ntrunc k M) (ntrunc k N)";
by (Simp_tac 1);
qed "ntrunc_CONS";

Addsimps [ntrunc_one_CONS, ntrunc_CONS];


val [prem1,prem2] = 
Goal 
 "[| !!x. h1(x) = (case f x of None => NIL | Some(z,w) => CONS z (h1 w));  \
\    !!x. h2(x) = (case f x of None => NIL | Some(z,w) => CONS z (h2 w)) |]\
\ ==> h1=h2";
by (rtac (ntrunc_equality RS ext) 1);
by (rename_tac "x k" 1);
by (res_inst_tac [("x", "x")] spec 1);
by (res_inst_tac [("n", "k")] less_induct 1);
by (rename_tac "n" 1);
by (rtac allI 1);
by (rename_tac "y" 1);
by (stac prem1 1);
by (stac prem2 1);
by (Simp_tac 1);
by (strip_tac 1);
by (case_tac "n" 1);
by (rename_tac "m" 2);
by (case_tac "m" 2);
by (ALLGOALS (asm_simp_tac (simpset() addsimps [less_Suc_eq])));
result();


(*** Lconst -- defined directly using lfp, but equivalent to a LList_corec ***)

Goal "mono(CONS(M))";
by (REPEAT (ares_tac [monoI, subset_refl, CONS_mono] 1));
qed "Lconst_fun_mono";

(* Lconst(M) = CONS M (Lconst M) *)
bind_thm ("Lconst", (Lconst_fun_mono RS (Lconst_def RS def_lfp_Tarski)));

(*A typical use of co-induction to show membership in the gfp.
  The containing set is simply the singleton {Lconst(M)}. *)
Goal "M:A ==> Lconst(M): llist(A)";
by (rtac (singletonI RS llist_coinduct) 1);
by Safe_tac;
by (res_inst_tac [("P", "%u. u: ?A")] (Lconst RS ssubst) 1);
by (REPEAT (ares_tac [list_Fun_CONS_I, singletonI, UnI1] 1));
qed "Lconst_type";

Goal "Lconst(M) = LList_corec M (%x. Some(x,x))";
by (rtac (equals_LList_corec RS fun_cong) 1);
by (Simp_tac 1);
by (rtac Lconst 1);
qed "Lconst_eq_LList_corec";

(*Thus we could have used gfp in the definition of Lconst*)
Goal "gfp(%N. CONS M N) = LList_corec M (%x. Some(x,x))";
by (rtac (equals_LList_corec RS fun_cong) 1);
by (Simp_tac 1);
by (rtac (Lconst_fun_mono RS gfp_Tarski) 1);
qed "gfp_Lconst_eq_LList_corec";


(*** Isomorphisms ***)

Goal "inj Rep_LList";
by (rtac inj_inverseI 1);
by (rtac Rep_LList_inverse 1);
qed "inj_Rep_LList";

Goal "inj_on Abs_LList LList";
by (rtac inj_on_inverseI 1);
by (etac Abs_LList_inverse 1);
qed "inj_on_Abs_LList";

Goalw [LList_def] "x : llist (range Leaf) ==> x : LList";
by (Asm_simp_tac 1);
qed "LListI";

Goalw [LList_def] "x : LList ==> x : llist (range Leaf)";
by (Asm_simp_tac 1);
qed "LListD";


(** Distinctness of constructors **)

Goalw [LNil_def,LCons_def] "~ LCons x xs = LNil";
by (rtac (CONS_not_NIL RS (inj_on_Abs_LList RS inj_on_contraD)) 1);
by (REPEAT (resolve_tac (llist.intrs @
			 [rangeI, LListI, Rep_LList RS LListD]) 1));
qed "LCons_not_LNil";

bind_thm ("LNil_not_LCons", LCons_not_LNil RS not_sym);

AddIffs [LCons_not_LNil, LNil_not_LCons];


(** llist constructors **)

Goalw [LNil_def] "Rep_LList LNil = NIL";
by (rtac (llist.NIL_I RS LListI RS Abs_LList_inverse) 1);
qed "Rep_LList_LNil";

Goalw [LCons_def] "Rep_LList(LCons x l) = CONS (Leaf x) (Rep_LList l)";
by (REPEAT (resolve_tac [llist.CONS_I RS LListI RS Abs_LList_inverse,
                         rangeI, Rep_LList RS LListD] 1));
qed "Rep_LList_LCons";

(** Injectiveness of CONS and LCons **)

Goalw [CONS_def] "(CONS M N=CONS M' N') = (M=M' & N=N')";
by (fast_tac (claset() addSEs [Scons_inject]) 1);
qed "CONS_CONS_eq2";

bind_thm ("CONS_inject", CONS_CONS_eq RS iffD1 RS conjE);


(*For reasoning about abstract llist constructors*)

AddIs [Rep_LList RS LListD, LListI];
AddIs llist.intrs;

AddSDs [inj_on_Abs_LList RS inj_onD,
        inj_Rep_LList RS injD];

Goalw [LCons_def] "(LCons x xs=LCons y ys) = (x=y & xs=ys)";
by (Fast_tac 1);
qed "LCons_LCons_eq";

AddIffs [LCons_LCons_eq];

Goal "CONS M N: llist(A) ==> M: A & N: llist(A)";
by (etac llist.elim 1);
by (etac CONS_neq_NIL 1);
by (Fast_tac 1);
qed "CONS_D2";


(****** Reasoning about llist(A) ******)

Addsimps [List_case_NIL, List_case_CONS];

(*A special case of list_equality for functions over lazy lists*)
val [Mlist,gMlist,NILcase,CONScase] = 
Goal
 "[| M: llist(A); g(NIL): llist(A);                             \
\    f(NIL)=g(NIL);                                             \
\    !!x l. [| x:A;  l: llist(A) |] ==>                         \
\           (f(CONS x l),g(CONS x l)) :                         \
\               LListD_Fun (diag A) ((%u.(f(u),g(u)))``llist(A) Un  \
\                                   diag(llist(A)))             \
\ |] ==> f(M) = g(M)";
by (rtac LList_equalityI 1);
by (rtac (Mlist RS imageI) 1);
by (rtac image_subsetI 1);
by (etac llist.elim 1);
by (etac ssubst 1);
by (stac NILcase 1);
by (rtac (gMlist RS LListD_Fun_diag_I) 1);
by (etac ssubst 1);
by (REPEAT (ares_tac [CONScase] 1));
qed "LList_fun_equalityI";


(*** The functional "Lmap" ***)

Goal "Lmap f NIL = NIL";
by (rtac (Lmap_def RS def_LList_corec RS trans) 1);
by (Simp_tac 1);
qed "Lmap_NIL";

Goal "Lmap f (CONS M N) = CONS (f M) (Lmap f N)";
by (rtac (Lmap_def RS def_LList_corec RS trans) 1);
by (Simp_tac 1);
qed "Lmap_CONS";

Addsimps [Lmap_NIL, Lmap_CONS];

(*Another type-checking proof by coinduction*)
val [major,minor] = 
Goal "[| M: llist(A);  !!x. x:A ==> f(x):B |] ==> Lmap f M: llist(B)";
by (rtac (major RS imageI RS llist_coinduct) 1);
by Safe_tac;
by (etac llist.elim 1);
by (ALLGOALS Asm_simp_tac);
by (REPEAT (ares_tac [list_Fun_NIL_I, list_Fun_CONS_I, 
                      minor, imageI, UnI1] 1));
qed "Lmap_type";

(*This type checking rule synthesises a sufficiently large set for f*)
Goal "M: llist(A) ==> Lmap f M: llist(f``A)";
by (etac Lmap_type 1);
by (etac imageI 1);
qed "Lmap_type2";

(** Two easy results about Lmap **)

Goalw [o_def] "M: llist(A) ==> Lmap (f o g) M = Lmap f (Lmap g M)";
by (dtac imageI 1);
by (etac LList_equalityI 1);
by Safe_tac;
by (etac llist.elim 1);
by (ALLGOALS Asm_simp_tac);
by (REPEAT (ares_tac [LListD_Fun_NIL_I, imageI, UnI1,
                      rangeI RS LListD_Fun_CONS_I] 1));
qed "Lmap_compose";

Goal "M: llist(A) ==> Lmap (%x. x) M = M";
by (dtac imageI 1);
by (etac LList_equalityI 1);
by Safe_tac;
by (etac llist.elim 1);
by (ALLGOALS Asm_simp_tac);
by (REPEAT (ares_tac [LListD_Fun_NIL_I, imageI RS UnI1,
                      rangeI RS LListD_Fun_CONS_I] 1));
qed "Lmap_ident";


(*** Lappend -- its two arguments cause some complications! ***)

Goalw [Lappend_def] "Lappend NIL NIL = NIL";
by (rtac (LList_corec RS trans) 1);
by (Simp_tac 1);
qed "Lappend_NIL_NIL";

Goalw [Lappend_def]
    "Lappend NIL (CONS N N') = CONS N (Lappend NIL N')";
by (rtac (LList_corec RS trans) 1);
by (Simp_tac 1);
qed "Lappend_NIL_CONS";

Goalw [Lappend_def]
    "Lappend (CONS M M') N = CONS M (Lappend M' N)";
by (rtac (LList_corec RS trans) 1);
by (Simp_tac 1);
qed "Lappend_CONS";

Addsimps [llist.NIL_I, Lappend_NIL_NIL, Lappend_NIL_CONS,
          Lappend_CONS, LListD_Fun_CONS_I, range_eqI, image_eqI];


Goal "M: llist(A) ==> Lappend NIL M = M";
by (etac LList_fun_equalityI 1);
by (ALLGOALS Asm_simp_tac);
qed "Lappend_NIL";

Goal "M: llist(A) ==> Lappend M NIL = M";
by (etac LList_fun_equalityI 1);
by (ALLGOALS Asm_simp_tac);
qed "Lappend_NIL2";

Addsimps [Lappend_NIL, Lappend_NIL2];


(** Alternative type-checking proofs for Lappend **)

(*weak co-induction: bisimulation and case analysis on both variables*)
Goal "[| M: llist(A); N: llist(A) |] ==> Lappend M N: llist(A)";
by (res_inst_tac
    [("X", "UN u:llist(A). UN v: llist(A). {Lappend u v}")] llist_coinduct 1);
by (Fast_tac 1);
by Safe_tac;
by (eres_inst_tac [("aa", "u")] llist.elim 1);
by (eres_inst_tac [("aa", "v")] llist.elim 1);
by (ALLGOALS Asm_simp_tac);
by (Blast_tac 1);
qed "Lappend_type";

(*strong co-induction: bisimulation and case analysis on one variable*)
Goal "[| M: llist(A); N: llist(A) |] ==> Lappend M N: llist(A)";
by (res_inst_tac [("X", "(%u. Lappend u N)``llist(A)")] llist_coinduct 1);
by (etac imageI 1);
by (rtac image_subsetI 1);
by (eres_inst_tac [("aa", "x")] llist.elim 1);
by (asm_simp_tac (simpset() addsimps [list_Fun_llist_I]) 1);
by (Asm_simp_tac 1);
qed "Lappend_type";

(**** Lazy lists as the type 'a llist -- strongly typed versions of above ****)

(** llist_case: case analysis for 'a llist **)

Addsimps ([LListI RS Abs_LList_inverse, Rep_LList_inverse,
           Rep_LList RS LListD, rangeI, inj_Leaf, inv_f_f] @ llist.intrs);

Goalw [llist_case_def,LNil_def]  "llist_case c d LNil = c";
by (Simp_tac 1);
qed "llist_case_LNil";

Goalw [llist_case_def,LCons_def]
    "llist_case c d (LCons M N) = d M N";
by (Simp_tac 1);
qed "llist_case_LCons";

(*Elimination is case analysis, not induction.*)
val [prem1,prem2] = 
Goalw [NIL_def,CONS_def]
     "[| l=LNil ==> P;  !!x l'. l=LCons x l' ==> P |] ==> P";
by (rtac (Rep_LList RS LListD RS llist.elim) 1);
by (rtac (inj_Rep_LList RS injD RS prem1) 1);
by (stac Rep_LList_LNil 1);
by (assume_tac 1);
by (etac rangeE 1);
by (rtac (inj_Rep_LList RS injD RS prem2) 1);
by (asm_simp_tac (simpset() delsimps [CONS_CONS_eq] 
		            addsimps [Rep_LList_LCons]) 1);
by (etac (LListI RS Abs_LList_inverse RS ssubst) 1);
by (rtac refl 1);
qed "llistE";

(** llist_corec: corecursion for 'a llist **)

(*Lemma for the proof of llist_corec*)
Goal "LList_corec a \
\          (%z. case f z of None => None | Some(v,w) => Some(Leaf(v),w)) : \
\       llist(range Leaf)";
by (res_inst_tac [("X", "range(%x. LList_corec x ?g)")] llist_coinduct 1);
by (rtac rangeI 1);
by Safe_tac;
by (stac LList_corec 1);
by (Force_tac 1);
qed "LList_corec_type2";

Goalw [llist_corec_def,LNil_def,LCons_def]
    "llist_corec a f =  \
\    (case f a of None => LNil | Some(z,w) => LCons z (llist_corec w f))";
by (stac LList_corec 1);
by (case_tac "f a" 1);
by (asm_simp_tac (simpset() addsimps [LList_corec_type2]) 1);
by (force_tac (claset(), simpset() addsimps [LList_corec_type2]) 1);
qed "llist_corec";

(*definitional version of same*)
val [rew] = 
Goal "[| !!x. h(x) == llist_corec x f |] ==>     \
\     h(a) = (case f a of None => LNil | Some(z,w) => LCons z (h w))";
by (rewtac rew);
by (rtac llist_corec 1);
qed "def_llist_corec";

(**** Proofs about type 'a llist functions ****)

(*** Deriving llist_equalityI -- llist equality is a bisimulation ***)

Goalw [LListD_Fun_def]
    "r <= (llist A) <*> (llist A) ==> \
\           LListD_Fun (diag A) r <= (llist A) <*> (llist A)";
by (stac llist_unfold 1);
by (simp_tac (simpset() addsimps [NIL_def, CONS_def]) 1);
by (Fast_tac 1);
qed "LListD_Fun_subset_Times_llist";

Goal "prod_fun Rep_LList Rep_LList `` r <= \
\    (llist(range Leaf)) <*> (llist(range Leaf))";
by (fast_tac (claset() delrules [image_subsetI]
		       addIs [Rep_LList RS LListD]) 1);
qed "subset_Times_llist";

Goal "r <= (llist(range Leaf)) <*> (llist(range Leaf)) ==> \
\    prod_fun (Rep_LList o Abs_LList) (Rep_LList o Abs_LList) `` r <= r";
by Safe_tac;
by (etac (subsetD RS SigmaE2) 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [LListI RS Abs_LList_inverse]) 1);
qed "prod_fun_lemma";

Goal "prod_fun Rep_LList  Rep_LList `` range(%x. (x, x)) = \
\    diag(llist(range Leaf))";
by (rtac equalityI 1);
by (Blast_tac 1);
by (fast_tac (claset() delSWrapper "split_all_tac"
		       addSEs [LListI RS Abs_LList_inverse RS subst]) 1);
qed "prod_fun_range_eq_diag";

(*Used with lfilter*)
Goalw [llistD_Fun_def, prod_fun_def]
    "A<=B ==> llistD_Fun A <= llistD_Fun B";
by Auto_tac;
by (rtac image_eqI 1);
by (blast_tac (claset() addIs [impOfSubs LListD_Fun_mono]) 2);
by (Force_tac 1);
qed "llistD_Fun_mono";

(** To show two llists are equal, exhibit a bisimulation! 
      [also admits true equality] **)
Goalw [llistD_Fun_def]
    "[| (l1,l2) : r;  r <= llistD_Fun(r Un range(%x.(x,x))) |] ==> l1=l2";
by (rtac (inj_Rep_LList RS injD) 1);
by (res_inst_tac [("r", "prod_fun Rep_LList Rep_LList ``r"),
                  ("A", "range(Leaf)")] 
        LList_equalityI 1);
by (etac prod_fun_imageI 1);
by (etac (image_mono RS subset_trans) 1);
by (rtac (image_compose RS subst) 1);
by (rtac (prod_fun_compose RS subst) 1);
by (stac image_Un 1);
by (stac prod_fun_range_eq_diag 1);
by (rtac (LListD_Fun_subset_Times_llist RS prod_fun_lemma) 1);
by (rtac (subset_Times_llist RS Un_least) 1);
by (rtac diag_subset_Times 1);
qed "llist_equalityI";

(** Rules to prove the 2nd premise of llist_equalityI **)
Goalw [llistD_Fun_def,LNil_def] "(LNil,LNil) : llistD_Fun(r)";
by (rtac (LListD_Fun_NIL_I RS prod_fun_imageI) 1);
qed "llistD_Fun_LNil_I";

Goalw [llistD_Fun_def,LCons_def]
    "(l1,l2):r ==> (LCons x l1, LCons x l2) : llistD_Fun(r)";
by (rtac (rangeI RS LListD_Fun_CONS_I RS prod_fun_imageI) 1);
by (etac prod_fun_imageI 1);
qed "llistD_Fun_LCons_I";

(*Utilise the "strong" part, i.e. gfp(f)*)
Goalw [llistD_Fun_def] "(l,l) : llistD_Fun(r Un range(%x.(x,x)))";
by (rtac (Rep_LList_inverse RS subst) 1);
by (rtac prod_fun_imageI 1);
by (stac image_Un 1);
by (stac prod_fun_range_eq_diag 1);
by (rtac (Rep_LList RS LListD RS LListD_Fun_diag_I) 1);
qed "llistD_Fun_range_I";

(*A special case of list_equality for functions over lazy lists*)
val [prem1,prem2] =
Goal "[| f(LNil)=g(LNil);                                                \
\        !!x l. (f(LCons x l),g(LCons x l)) :                            \
\               llistD_Fun(range(%u. (f(u),g(u))) Un range(%v. (v,v)))   \
\     |] ==> f(l) = (g(l :: 'a llist) :: 'b llist)";
by (res_inst_tac [("r", "range(%u. (f(u),g(u)))")] llist_equalityI 1);
by (rtac rangeI 1);
by (rtac subsetI 1);
by (etac rangeE 1);
by (etac ssubst 1);
by (res_inst_tac [("l", "u")] llistE 1);
by (etac ssubst 1);
by (stac prem1 1);
by (rtac llistD_Fun_range_I 1);
by (etac ssubst 1);
by (rtac prem2 1);
qed "llist_fun_equalityI";

(*simpset for llist bisimulations*)
Addsimps [llist_case_LNil, llist_case_LCons, 
          llistD_Fun_LNil_I, llistD_Fun_LCons_I];


(*** The functional "lmap" ***)

Goal "lmap f LNil = LNil";
by (rtac (lmap_def RS def_llist_corec RS trans) 1);
by (Simp_tac 1);
qed "lmap_LNil";

Goal "lmap f (LCons M N) = LCons (f M) (lmap f N)";
by (rtac (lmap_def RS def_llist_corec RS trans) 1);
by (Simp_tac 1);
qed "lmap_LCons";

Addsimps [lmap_LNil, lmap_LCons];


(** Two easy results about lmap **)

Goal "lmap (f o g) l = lmap f (lmap g l)";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS Simp_tac);
qed "lmap_compose";

Goal "lmap (%x. x) l = l";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS Simp_tac);
qed "lmap_ident";


(*** iterates -- llist_fun_equalityI cannot be used! ***)

Goal "iterates f x = LCons x (iterates f (f x))";
by (rtac (iterates_def RS def_llist_corec RS trans) 1);
by (Simp_tac 1);
qed "iterates";

Goal "lmap f (iterates f x) = iterates f (f x)";
by (res_inst_tac [("r", "range(%u.(lmap f (iterates f u),iterates f (f u)))")] 
    llist_equalityI 1);
by (rtac rangeI 1);
by Safe_tac;
by (res_inst_tac [("x1", "f(u)")] (iterates RS ssubst) 1);
by (res_inst_tac [("x1", "u")] (iterates RS ssubst) 1);
by (Simp_tac 1);
qed "lmap_iterates";

Goal "iterates f x = LCons x (lmap f (iterates f x))";
by (stac lmap_iterates 1);
by (rtac iterates 1);
qed "iterates_lmap";

(*** A rather complex proof about iterates -- cf Andy Pitts ***)

(** Two lemmas about natrec n x (%m.g), which is essentially (g^n)(x) **)

Goal "nat_rec (LCons b l) (%m. lmap(f)) n =      \
\    LCons (nat_rec b (%m. f) n) (nat_rec l (%m. lmap(f)) n)";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "fun_power_lmap";

goal Nat.thy "nat_rec (g x) (%m. g) n = nat_rec x (%m. g) (Suc n)";
by (induct_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "fun_power_Suc";

val Pair_cong = read_instantiate_sg (sign_of Prod.thy)
 [("f","Pair")] (standard(refl RS cong RS cong));

(*The bisimulation consists of {(lmap(f)^n (h(u)), lmap(f)^n (iterates(f,u)))}
  for all u and all n::nat.*)
val [prem] = Goal "(!!x. h(x) = LCons x (lmap f (h x))) ==> h = iterates(f)";
by (rtac ext 1);
by (res_inst_tac [("r", 
   "UN u. range(%n. (nat_rec (h u) (%m y. lmap f y) n, \
\                    nat_rec (iterates f u) (%m y. lmap f y) n))")] 
    llist_equalityI 1);
by (REPEAT (resolve_tac [UN1_I, range_eqI, Pair_cong, nat_rec_0 RS sym] 1));
by (Clarify_tac 1);
by (stac iterates 1);
by (stac prem 1);
by (stac fun_power_lmap 1);
by (stac fun_power_lmap 1);
by (rtac llistD_Fun_LCons_I 1);
by (rtac (lmap_iterates RS subst) 1);
by (stac fun_power_Suc 1);
by (stac fun_power_Suc 1);
by (rtac (UN1_I RS UnI1) 1);
by (rtac rangeI 1);
qed "iterates_equality";


(*** lappend -- its two arguments cause some complications! ***)

Goalw [lappend_def] "lappend LNil LNil = LNil";
by (rtac (llist_corec RS trans) 1);
by (Simp_tac 1);
qed "lappend_LNil_LNil";

Goalw [lappend_def]
    "lappend LNil (LCons l l') = LCons l (lappend LNil l')";
by (rtac (llist_corec RS trans) 1);
by (Simp_tac 1);
qed "lappend_LNil_LCons";

Goalw [lappend_def]
    "lappend (LCons l l') N = LCons l (lappend l' N)";
by (rtac (llist_corec RS trans) 1);
by (Simp_tac 1);
qed "lappend_LCons";

Addsimps [lappend_LNil_LNil, lappend_LNil_LCons, lappend_LCons];

Goal "lappend LNil l = l";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS Simp_tac);
qed "lappend_LNil";

Goal "lappend l LNil = l";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS Simp_tac);
qed "lappend_LNil2";

Addsimps [lappend_LNil, lappend_LNil2];

(*The infinite first argument blocks the second*)
Goal "lappend (iterates f x) N = iterates f x";
by (res_inst_tac [("r", "range(%u.(lappend (iterates f u) N,iterates f u))")] 
    llist_equalityI 1);
by (rtac rangeI 1);
by Safe_tac;
by (stac iterates 1);
by (Simp_tac 1);
qed "lappend_iterates";

(** Two proofs that lmap distributes over lappend **)

(*Long proof requiring case analysis on both both arguments*)
Goal "lmap f (lappend l n) = lappend (lmap f l) (lmap f n)";
by (res_inst_tac 
    [("r",  
      "UN n. range(%l.(lmap f (lappend l n),lappend (lmap f l) (lmap f n)))")] 
    llist_equalityI 1);
by (rtac UN1_I 1);
by (rtac rangeI 1);
by Safe_tac;
by (res_inst_tac [("l", "l")] llistE 1);
by (res_inst_tac [("l", "n")] llistE 1);
by (ALLGOALS Asm_simp_tac);
by (REPEAT_SOME (ares_tac [llistD_Fun_LCons_I, UN1_I RS UnI1, rangeI]));
qed "lmap_lappend_distrib";

(*Shorter proof of theorem above using llist_equalityI as strong coinduction*)
Goal "lmap f (lappend l n) = lappend (lmap f l) (lmap f n)";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (Simp_tac 1);
by (Simp_tac 1);
qed "lmap_lappend_distrib";

(*Without strong coinduction, three case analyses might be needed*)
Goal "lappend (lappend l1 l2) l3 = lappend l1 (lappend l2 l3)";
by (res_inst_tac [("l","l1")] llist_fun_equalityI 1);
by (Simp_tac 1);
by (Simp_tac 1);
qed "lappend_assoc";
