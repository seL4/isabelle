(*  Title:      HOL/llist
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

SHOULD LListD_Fun_CONS_I, etc., be equations (for rewriting)?
*)

open LList;

(** Simplification **)

simpset := !simpset setloop split_tac [expand_split, expand_sum_case];

(*For adding _eqI rules to a simpset; we must remove Pair_eq because
  it may turn an instance of reflexivity into a conjunction!*)
fun add_eqI ss = ss addsimps [range_eqI, image_eqI] 
                    delsimps [Pair_eq];


(*This justifies using llist in other recursive type definitions*)
goalw LList.thy llist.defs "!!A B. A<=B ==> llist(A) <= llist(B)";
by (rtac gfp_mono 1);
by (REPEAT (ares_tac basic_monos 1));
qed "llist_mono";


goal LList.thy "llist(A) = {Numb(0)} <+> (A <*> llist(A))";
let val rew = rewrite_rule [NIL_def, CONS_def] in  
by (fast_tac (univ_cs addSIs (equalityI :: map rew llist.intrs)
                      addEs [rew llist.elim]) 1)
end;
qed "llist_unfold";


(*** Type checking by coinduction, using list_Fun 
     THE COINDUCTIVE DEFINITION PACKAGE COULD DO THIS!
***)

goalw LList.thy [list_Fun_def]
    "!!M. [| M : X;  X <= list_Fun A (X Un llist(A)) |] ==>  M : llist(A)";
by (etac llist.coinduct 1);
by (etac (subsetD RS CollectD) 1);
by (assume_tac 1);
qed "llist_coinduct";

goalw LList.thy [list_Fun_def, NIL_def] "NIL: list_Fun A X";
by (fast_tac set_cs 1);
qed "list_Fun_NIL_I";

goalw LList.thy [list_Fun_def,CONS_def]
    "!!M N. [| M: A;  N: X |] ==> CONS M N : list_Fun A X";
by (fast_tac set_cs 1);
qed "list_Fun_CONS_I";

(*Utilise the "strong" part, i.e. gfp(f)*)
goalw LList.thy (llist.defs @ [list_Fun_def])
    "!!M N. M: llist(A) ==> M : list_Fun A (X Un llist(A))";
by (etac (llist.mono RS gfp_fun_UnI2) 1);
qed "list_Fun_llist_I";

(*** LList_corec satisfies the desired recurion equation ***)

(*A continuity result?*)
goalw LList.thy [CONS_def] "CONS M (UN x.f(x)) = (UN x. CONS M (f x))";
by (simp_tac (!simpset addsimps [In1_UN1, Scons_UN1_y]) 1);
qed "CONS_UN1";

(*UNUSED; obsolete?
goal Prod.thy "split p (%x y.UN z.f x y z) = (UN z. split p (%x y.f x y z))";
by (simp_tac (!simpset setloop (split_tac [expand_split])) 1);
qed "split_UN1";

goal Sum.thy "sum_case s f (%y.UN z.g y z) = (UN z.sum_case s f (%y.g y z))";
by (simp_tac (!simpset setloop (split_tac [expand_sum_case])) 1);
qed "sum_case2_UN1";
*)

val prems = goalw LList.thy [CONS_def]
    "[| M<=M';  N<=N' |] ==> CONS M N <= CONS M' N'";
by (REPEAT (resolve_tac ([In1_mono,Scons_mono]@prems) 1));
qed "CONS_mono";

Addsimps [LList_corec_fun_def RS def_nat_rec_0,
          LList_corec_fun_def RS def_nat_rec_Suc];

(** The directions of the equality are proved separately **)

goalw LList.thy [LList_corec_def]
    "LList_corec a f <= sum_case (%u.NIL) \
\                          (split(%z w. CONS z (LList_corec w f))) (f a)";
by (rtac UN1_least 1);
by (res_inst_tac [("n","k")] natE 1);
by (ALLGOALS (Asm_simp_tac));
by (REPEAT (resolve_tac [allI, impI, subset_refl RS CONS_mono, UN1_upper] 1));
qed "LList_corec_subset1";

goalw LList.thy [LList_corec_def]
    "sum_case (%u.NIL) (split(%z w. CONS z (LList_corec w f))) (f a) <= \
\    LList_corec a f";
by (simp_tac (!simpset addsimps [CONS_UN1]) 1);
by (safe_tac set_cs);
by (ALLGOALS (res_inst_tac [("x","Suc(?k)")] UN1_I THEN' Asm_simp_tac));
qed "LList_corec_subset2";

(*the recursion equation for LList_corec -- NOT SUITABLE FOR REWRITING!*)
goal LList.thy
    "LList_corec a f = sum_case (%u. NIL) \
\                           (split(%z w. CONS z (LList_corec w f))) (f a)";
by (REPEAT (resolve_tac [equalityI, LList_corec_subset1, 
                         LList_corec_subset2] 1));
qed "LList_corec";

(*definitional version of same*)
val [rew] = goal LList.thy
    "[| !!x. h(x) == LList_corec x f |] ==>     \
\    h(a) = sum_case (%u.NIL) (split(%z w. CONS z (h w))) (f a)";
by (rewtac rew);
by (rtac LList_corec 1);
qed "def_LList_corec";

(*A typical use of co-induction to show membership in the gfp. 
  Bisimulation is  range(%x. LList_corec x f) *)
goal LList.thy "LList_corec a f : llist({u.True})";
by (res_inst_tac [("X", "range(%x.LList_corec x ?g)")] llist_coinduct 1);
by (rtac rangeI 1);
by (safe_tac set_cs);
by (stac LList_corec 1);
by (simp_tac (!simpset addsimps [list_Fun_NIL_I, list_Fun_CONS_I, CollectI]
                       |> add_eqI) 1);
qed "LList_corec_type";

(*Lemma for the proof of llist_corec*)
goal LList.thy
   "LList_corec a (%z.sum_case Inl (split(%v w.Inr((Leaf(v),w)))) (f z)) : \
\   llist(range Leaf)";
by (res_inst_tac [("X", "range(%x.LList_corec x ?g)")] llist_coinduct 1);
by (rtac rangeI 1);
by (safe_tac set_cs);
by (stac LList_corec 1);
by (asm_simp_tac (!simpset addsimps [list_Fun_NIL_I]) 1);
by (fast_tac (set_cs addSIs [list_Fun_CONS_I]) 1);
qed "LList_corec_type2";


(**** llist equality as a gfp; the bisimulation principle ****)

(*This theorem is actually used, unlike the many similar ones in ZF*)
goal LList.thy "LListD(r) = diag({Numb(0)}) <++> (r <**> LListD(r))";
let val rew = rewrite_rule [NIL_def, CONS_def] in  
by (fast_tac (univ_cs addSIs (equalityI :: map rew LListD.intrs)
                      addEs [rew LListD.elim]) 1)
end;
qed "LListD_unfold";

goal LList.thy "!M N. (M,N) : LListD(diag(A)) --> ntrunc k M = ntrunc k N";
by (res_inst_tac [("n", "k")] less_induct 1);
by (safe_tac set_cs);
by (etac LListD.elim 1);
by (safe_tac (prod_cs addSEs [diagE]));
by (res_inst_tac [("n", "n")] natE 1);
by (asm_simp_tac (!simpset addsimps [ntrunc_0]) 1);
by (rename_tac "n'" 1);
by (res_inst_tac [("n", "n'")] natE 1);
by (asm_simp_tac (!simpset addsimps [CONS_def, ntrunc_one_In1]) 1);
by (asm_simp_tac (!simpset addsimps [CONS_def, ntrunc_In1, ntrunc_Scons, less_Suc_eq]) 1);
qed "LListD_implies_ntrunc_equality";

(*The domain of the LListD relation*)
goalw LList.thy (llist.defs @ [NIL_def, CONS_def])
    "fst``LListD(diag(A)) <= llist(A)";
by (rtac gfp_upperbound 1);
(*avoids unfolding LListD on the rhs*)
by (res_inst_tac [("P", "%x. fst``x <= ?B")] (LListD_unfold RS ssubst) 1);
by (Simp_tac 1);
by (fast_tac univ_cs 1);
qed "fst_image_LListD";

(*This inclusion justifies the use of coinduction to show M=N*)
goal LList.thy "LListD(diag(A)) <= diag(llist(A))";
by (rtac subsetI 1);
by (res_inst_tac [("p","x")] PairE 1);
by (safe_tac HOL_cs);
by (rtac diag_eqI 1);
by (rtac (LListD_implies_ntrunc_equality RS spec RS spec RS mp RS 
          ntrunc_equality) 1);
by (assume_tac 1);
by (etac (fst_imageI RS (fst_image_LListD RS subsetD)) 1);
qed "LListD_subset_diag";

(** Coinduction, using LListD_Fun
    THE COINDUCTIVE DEFINITION PACKAGE COULD DO THIS!
 **)

goalw LList.thy [LListD_Fun_def]
    "!!M. [| M : X;  X <= LListD_Fun r (X Un LListD(r)) |] ==>  M : LListD(r)";
by (etac LListD.coinduct 1);
by (etac (subsetD RS CollectD) 1);
by (assume_tac 1);
qed "LListD_coinduct";

goalw LList.thy [LListD_Fun_def,NIL_def] "(NIL,NIL) : LListD_Fun r s";
by (fast_tac set_cs 1);
qed "LListD_Fun_NIL_I";

goalw LList.thy [LListD_Fun_def,CONS_def]
 "!!x. [| x:A;  (M,N):s |] ==> (CONS x M, CONS x N) : LListD_Fun (diag A) s";
by (fast_tac univ_cs 1);
qed "LListD_Fun_CONS_I";

(*Utilise the "strong" part, i.e. gfp(f)*)
goalw LList.thy (LListD.defs @ [LListD_Fun_def])
    "!!M N. M: LListD(r) ==> M : LListD_Fun r (X Un LListD(r))";
by (etac (LListD.mono RS gfp_fun_UnI2) 1);
qed "LListD_Fun_LListD_I";


(*This converse inclusion helps to strengthen LList_equalityI*)
goal LList.thy "diag(llist(A)) <= LListD(diag(A))";
by (rtac subsetI 1);
by (etac LListD_coinduct 1);
by (rtac subsetI 1);
by (etac diagE 1);
by (etac ssubst 1);
by (eresolve_tac [llist.elim] 1);
by (ALLGOALS
    (asm_simp_tac (!simpset addsimps [diagI, LListD_Fun_NIL_I,
                                      LListD_Fun_CONS_I])));
qed "diag_subset_LListD";

goal LList.thy "LListD(diag(A)) = diag(llist(A))";
by (REPEAT (resolve_tac [equalityI, LListD_subset_diag, 
                         diag_subset_LListD] 1));
qed "LListD_eq_diag";

goal LList.thy 
    "!!M N. M: llist(A) ==> (M,M) : LListD_Fun (diag A) (X Un diag(llist(A)))";
by (rtac (LListD_eq_diag RS subst) 1);
by (rtac LListD_Fun_LListD_I 1);
by (asm_simp_tac (!simpset addsimps [LListD_eq_diag, diagI]) 1);
qed "LListD_Fun_diag_I";


(** To show two LLists are equal, exhibit a bisimulation! 
      [also admits true equality]
   Replace "A" by some particular set, like {x.True}??? *)
goal LList.thy 
    "!!r. [| (M,N) : r;  r <= LListD_Fun (diag A) (r Un diag(llist(A))) \
\         |] ==>  M=N";
by (rtac (LListD_subset_diag RS subsetD RS diagE) 1);
by (etac LListD_coinduct 1);
by (asm_simp_tac (!simpset addsimps [LListD_eq_diag]) 1);
by (safe_tac prod_cs);
qed "LList_equalityI";


(*** Finality of llist(A): Uniqueness of functions defined by corecursion ***)

(*abstract proof using a bisimulation*)
val [prem1,prem2] = goal LList.thy
 "[| !!x. h1(x) = sum_case (%u.NIL) (split(%z w. CONS z (h1 w))) (f x);  \
\    !!x. h2(x) = sum_case (%u.NIL) (split(%z w. CONS z (h2 w))) (f x) |]\
\ ==> h1=h2";
by (rtac ext 1);
(*next step avoids an unknown (and flexflex pair) in simplification*)
by (res_inst_tac [("A", "{u.True}"),
                  ("r", "range(%u. (h1(u),h2(u)))")] LList_equalityI 1);
by (rtac rangeI 1);
by (safe_tac set_cs);
by (stac prem1 1);
by (stac prem2 1);
by (simp_tac (!simpset addsimps [LListD_Fun_NIL_I,
                                 CollectI RS LListD_Fun_CONS_I]
                       |> add_eqI) 1);
qed "LList_corec_unique";

val [prem] = goal LList.thy
 "[| !!x. h(x) = sum_case (%u.NIL) (split(%z w. CONS z (h w))) (f x) |] \
\ ==> h = (%x.LList_corec x f)";
by (rtac (LList_corec RS (prem RS LList_corec_unique)) 1);
qed "equals_LList_corec";


(** Obsolete LList_corec_unique proof: complete induction, not coinduction **)

goalw LList.thy [CONS_def] "ntrunc (Suc 0) (CONS M N) = {}";
by (rtac ntrunc_one_In1 1);
qed "ntrunc_one_CONS";

goalw LList.thy [CONS_def]
    "ntrunc (Suc(Suc(k))) (CONS M N) = CONS (ntrunc k M) (ntrunc k N)";
by (simp_tac (!simpset addsimps [ntrunc_Scons,ntrunc_In1]) 1);
qed "ntrunc_CONS";

val [prem1,prem2] = goal LList.thy
 "[| !!x. h1(x) = sum_case (%u.NIL) (split(%z w. CONS z (h1 w))) (f x);  \
\    !!x. h2(x) = sum_case (%u.NIL) (split(%z w. CONS z (h2 w))) (f x) |]\
\ ==> h1=h2";
by (rtac (ntrunc_equality RS ext) 1);
by (res_inst_tac [("x", "x")] spec 1);
by (res_inst_tac [("n", "k")] less_induct 1);
by (rtac allI 1);
by (stac prem1 1);
by (stac prem2 1);
by (simp_tac (!simpset setloop (split_tac [expand_sum_case])) 1);
by (strip_tac 1);
by (res_inst_tac [("n", "n")] natE 1);
by (res_inst_tac [("n", "xb")] natE 2);
by (ALLGOALS(asm_simp_tac(!simpset addsimps
            [ntrunc_0,ntrunc_one_CONS,ntrunc_CONS, less_Suc_eq])));
result();


(*** Lconst -- defined directly using lfp, but equivalent to a LList_corec ***)

goal LList.thy "mono(CONS(M))";
by (REPEAT (ares_tac [monoI, subset_refl, CONS_mono] 1));
qed "Lconst_fun_mono";

(* Lconst(M) = CONS M (Lconst M) *)
bind_thm ("Lconst", (Lconst_fun_mono RS (Lconst_def RS def_lfp_Tarski)));

(*A typical use of co-induction to show membership in the gfp.
  The containing set is simply the singleton {Lconst(M)}. *)
goal LList.thy "!!M A. M:A ==> Lconst(M): llist(A)";
by (rtac (singletonI RS llist_coinduct) 1);
by (safe_tac set_cs);
by (res_inst_tac [("P", "%u. u: ?A")] (Lconst RS ssubst) 1);
by (REPEAT (ares_tac [list_Fun_CONS_I, singletonI, UnI1] 1));
qed "Lconst_type";

goal LList.thy "Lconst(M) = LList_corec M (%x.Inr((x,x)))";
by (rtac (equals_LList_corec RS fun_cong) 1);
by (Simp_tac 1);
by (rtac Lconst 1);
qed "Lconst_eq_LList_corec";

(*Thus we could have used gfp in the definition of Lconst*)
goal LList.thy "gfp(%N. CONS M N) = LList_corec M (%x.Inr((x,x)))";
by (rtac (equals_LList_corec RS fun_cong) 1);
by (Simp_tac 1);
by (rtac (Lconst_fun_mono RS gfp_Tarski) 1);
qed "gfp_Lconst_eq_LList_corec";


(*** Isomorphisms ***)

goal LList.thy "inj(Rep_llist)";
by (rtac inj_inverseI 1);
by (rtac Rep_llist_inverse 1);
qed "inj_Rep_llist";

goal LList.thy "inj_onto Abs_llist (llist(range Leaf))";
by (rtac inj_onto_inverseI 1);
by (etac Abs_llist_inverse 1);
qed "inj_onto_Abs_llist";

(** Distinctness of constructors **)

goalw LList.thy [LNil_def,LCons_def] "~ LCons x xs = LNil";
by (rtac (CONS_not_NIL RS (inj_onto_Abs_llist RS inj_onto_contraD)) 1);
by (REPEAT (resolve_tac (llist.intrs @ [rangeI, Rep_llist]) 1));
qed "LCons_not_LNil";

bind_thm ("LNil_not_LCons", (LCons_not_LNil RS not_sym));

bind_thm ("LCons_neq_LNil", (LCons_not_LNil RS notE));
val LNil_neq_LCons = sym RS LCons_neq_LNil;

(** llist constructors **)

goalw LList.thy [LNil_def]
    "Rep_llist(LNil) = NIL";
by (rtac (llist.NIL_I RS Abs_llist_inverse) 1);
qed "Rep_llist_LNil";

goalw LList.thy [LCons_def]
    "Rep_llist(LCons x l) = CONS (Leaf x) (Rep_llist l)";
by (REPEAT (resolve_tac [llist.CONS_I RS Abs_llist_inverse,
                         rangeI, Rep_llist] 1));
qed "Rep_llist_LCons";

(** Injectiveness of CONS and LCons **)

goalw LList.thy [CONS_def] "(CONS M N=CONS M' N') = (M=M' & N=N')";
by (fast_tac (HOL_cs addSEs [Scons_inject, make_elim In1_inject]) 1);
qed "CONS_CONS_eq2";

bind_thm ("CONS_inject", (CONS_CONS_eq RS iffD1 RS conjE));


(*For reasoning about abstract llist constructors*)
val llist_cs = set_cs addIs [Rep_llist]@llist.intrs
                      addSEs [CONS_neq_NIL,NIL_neq_CONS,CONS_inject]
                      addSDs [inj_onto_Abs_llist RS inj_ontoD,
                              inj_Rep_llist RS injD, Leaf_inject];

goalw LList.thy [LCons_def] "(LCons x xs=LCons y ys) = (x=y & xs=ys)";
by (fast_tac llist_cs 1);
qed "LCons_LCons_eq";
bind_thm ("LCons_inject", (LCons_LCons_eq RS iffD1 RS conjE));

val [major] = goal LList.thy "CONS M N: llist(A) ==> M: A & N: llist(A)";
by (rtac (major RS llist.elim) 1);
by (etac CONS_neq_NIL 1);
by (fast_tac llist_cs 1);
qed "CONS_D2";


(****** Reasoning about llist(A) ******)

Addsimps [List_case_NIL, List_case_CONS];

(*A special case of list_equality for functions over lazy lists*)
val [Mlist,gMlist,NILcase,CONScase] = goal LList.thy
 "[| M: llist(A); g(NIL): llist(A);                             \
\    f(NIL)=g(NIL);                                             \
\    !!x l. [| x:A;  l: llist(A) |] ==>                         \
\           (f(CONS x l),g(CONS x l)) :                         \
\               LListD_Fun (diag A) ((%u.(f(u),g(u)))``llist(A) Un  \
\                                   diag(llist(A)))             \
\ |] ==> f(M) = g(M)";
by (rtac LList_equalityI 1);
by (rtac (Mlist RS imageI) 1);
by (rtac subsetI 1);
by (etac imageE 1);
by (etac ssubst 1);
by (etac llist.elim 1);
by (etac ssubst 1);
by (stac NILcase 1);
by (rtac (gMlist RS LListD_Fun_diag_I) 1);
by (etac ssubst 1);
by (REPEAT (ares_tac [CONScase] 1));
qed "LList_fun_equalityI";


(*** The functional "Lmap" ***)

goal LList.thy "Lmap f NIL = NIL";
by (rtac (Lmap_def RS def_LList_corec RS trans) 1);
by (Simp_tac 1);
qed "Lmap_NIL";

goal LList.thy "Lmap f (CONS M N) = CONS (f M) (Lmap f N)";
by (rtac (Lmap_def RS def_LList_corec RS trans) 1);
by (Simp_tac 1);
qed "Lmap_CONS";

(*Another type-checking proof by coinduction*)
val [major,minor] = goal LList.thy
    "[| M: llist(A);  !!x. x:A ==> f(x):B |] ==> Lmap f M: llist(B)";
by (rtac (major RS imageI RS llist_coinduct) 1);
by (safe_tac set_cs);
by (etac llist.elim 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [Lmap_NIL,Lmap_CONS])));
by (REPEAT (ares_tac [list_Fun_NIL_I, list_Fun_CONS_I, 
                      minor, imageI, UnI1] 1));
qed "Lmap_type";

(*This type checking rule synthesises a sufficiently large set for f*)
val [major] = goal LList.thy  "M: llist(A) ==> Lmap f M: llist(f``A)";
by (rtac (major RS Lmap_type) 1);
by (etac imageI 1);
qed "Lmap_type2";

(** Two easy results about Lmap **)

val [prem] = goalw LList.thy [o_def]
    "M: llist(A) ==> Lmap (f o g) M = Lmap f (Lmap g M)";
by (rtac (prem RS imageI RS LList_equalityI) 1);
by (safe_tac set_cs);
by (etac llist.elim 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [Lmap_NIL,Lmap_CONS])));
by (REPEAT (ares_tac [LListD_Fun_NIL_I, imageI, UnI1,
                      rangeI RS LListD_Fun_CONS_I] 1));
qed "Lmap_compose";

val [prem] = goal LList.thy "M: llist(A) ==> Lmap (%x.x) M = M";
by (rtac (prem RS imageI RS LList_equalityI) 1);
by (safe_tac set_cs);
by (etac llist.elim 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [Lmap_NIL,Lmap_CONS])));
by (REPEAT (ares_tac [LListD_Fun_NIL_I, imageI RS UnI1,
                      rangeI RS LListD_Fun_CONS_I] 1));
qed "Lmap_ident";


(*** Lappend -- its two arguments cause some complications! ***)

goalw LList.thy [Lappend_def] "Lappend NIL NIL = NIL";
by (rtac (LList_corec RS trans) 1);
by (Simp_tac 1);
qed "Lappend_NIL_NIL";

goalw LList.thy [Lappend_def]
    "Lappend NIL (CONS N N') = CONS N (Lappend NIL N')";
by (rtac (LList_corec RS trans) 1);
by (Simp_tac 1);
qed "Lappend_NIL_CONS";

goalw LList.thy [Lappend_def]
    "Lappend (CONS M M') N = CONS M (Lappend M' N)";
by (rtac (LList_corec RS trans) 1);
by (Simp_tac 1);
qed "Lappend_CONS";

Addsimps [llist.NIL_I, Lappend_NIL_NIL, Lappend_NIL_CONS,
          Lappend_CONS, LListD_Fun_CONS_I, range_eqI, image_eqI];
Delsimps [Pair_eq];

goal LList.thy "!!M. M: llist(A) ==> Lappend NIL M = M";
by (etac LList_fun_equalityI 1);
by (ALLGOALS Asm_simp_tac);
qed "Lappend_NIL";

goal LList.thy "!!M. M: llist(A) ==> Lappend M NIL = M";
by (etac LList_fun_equalityI 1);
by (ALLGOALS Asm_simp_tac);
qed "Lappend_NIL2";

(** Alternative type-checking proofs for Lappend **)

(*weak co-induction: bisimulation and case analysis on both variables*)
goal LList.thy
    "!!M N. [| M: llist(A); N: llist(A) |] ==> Lappend M N: llist(A)";
by (res_inst_tac
    [("X", "UN u:llist(A). UN v: llist(A). {Lappend u v}")] llist_coinduct 1);
by (fast_tac set_cs 1);
by (safe_tac set_cs);
by (eres_inst_tac [("a", "u")] llist.elim 1);
by (eres_inst_tac [("a", "v")] llist.elim 1);
by (ALLGOALS
    (Asm_simp_tac THEN'
     fast_tac (set_cs addSIs [llist.NIL_I, list_Fun_NIL_I, list_Fun_CONS_I])));
qed "Lappend_type";

(*strong co-induction: bisimulation and case analysis on one variable*)
goal LList.thy
    "!!M N. [| M: llist(A); N: llist(A) |] ==> Lappend M N: llist(A)";
by (res_inst_tac [("X", "(%u.Lappend u N)``llist(A)")] llist_coinduct 1);
by (etac imageI 1);
by (rtac subsetI 1);
by (etac imageE 1);
by (eres_inst_tac [("a", "u")] llist.elim 1);
by (asm_simp_tac (!simpset addsimps [Lappend_NIL, list_Fun_llist_I]) 1);
by (Asm_simp_tac 1);
by (fast_tac (set_cs addSIs [list_Fun_CONS_I]) 1);
qed "Lappend_type";

(**** Lazy lists as the type 'a llist -- strongly typed versions of above ****)

(** llist_case: case analysis for 'a llist **)

Addsimps ([Abs_llist_inverse, Rep_llist_inverse,
           Rep_llist, rangeI, inj_Leaf, Inv_f_f] @ llist.intrs);

goalw LList.thy [llist_case_def,LNil_def]  "llist_case c d LNil = c";
by (Simp_tac 1);
qed "llist_case_LNil";

goalw LList.thy [llist_case_def,LCons_def]
    "llist_case c d (LCons M N) = d M N";
by (Simp_tac 1);
qed "llist_case_LCons";

(*Elimination is case analysis, not induction.*)
val [prem1,prem2] = goalw LList.thy [NIL_def,CONS_def]
    "[| l=LNil ==> P;  !!x l'. l=LCons x l' ==> P \
\    |] ==> P";
by (rtac (Rep_llist RS llist.elim) 1);
by (rtac (inj_Rep_llist RS injD RS prem1) 1);
by (stac Rep_llist_LNil 1);
by (assume_tac 1);
by (etac rangeE 1);
by (rtac (inj_Rep_llist RS injD RS prem2) 1);
by (asm_simp_tac (!simpset delsimps [CONS_CONS_eq] addsimps [Rep_llist_LCons]) 1);
by (etac (Abs_llist_inverse RS ssubst) 1);
by (rtac refl 1);
qed "llistE";

(** llist_corec: corecursion for 'a llist **)

goalw LList.thy [llist_corec_def,LNil_def,LCons_def]
    "llist_corec a f = sum_case (%u. LNil) \
\                           (split(%z w. LCons z (llist_corec w f))) (f a)";
by (stac LList_corec 1);
by (res_inst_tac [("s","f(a)")] sumE 1);
by (asm_simp_tac (!simpset addsimps [LList_corec_type2]) 1);
by (res_inst_tac [("p","y")] PairE 1);
by (asm_simp_tac (!simpset addsimps [LList_corec_type2]) 1);
(*FIXME: correct case splits usd to be found automatically:
by (ASM_SIMP_TAC(!simpset addsimps [LList_corec_type2]) 1);*)
qed "llist_corec";

(*definitional version of same*)
val [rew] = goal LList.thy
    "[| !!x. h(x) == llist_corec x f |] ==>     \
\    h(a) = sum_case (%u.LNil) (split(%z w. LCons z (h w))) (f a)";
by (rewtac rew);
by (rtac llist_corec 1);
qed "def_llist_corec";

(**** Proofs about type 'a llist functions ****)

(*** Deriving llist_equalityI -- llist equality is a bisimulation ***)

goalw LList.thy [LListD_Fun_def]
    "!!r A. r <= (llist A) Times (llist A) ==> \
\           LListD_Fun (diag A) r <= (llist A) Times (llist A)";
by (stac llist_unfold 1);
by (simp_tac (!simpset addsimps [NIL_def, CONS_def]) 1);
by (fast_tac univ_cs 1);
qed "LListD_Fun_subset_Sigma_llist";

goal LList.thy
    "prod_fun Rep_llist Rep_llist `` r <= \
\    (llist(range Leaf)) Times (llist(range Leaf))";
by (fast_tac (prod_cs addIs [Rep_llist]) 1);
qed "subset_Sigma_llist";

val [prem] = goal LList.thy
    "r <= (llist(range Leaf)) Times (llist(range Leaf)) ==> \
\    prod_fun (Rep_llist o Abs_llist) (Rep_llist o Abs_llist) `` r <= r";
by (safe_tac prod_cs);
by (rtac (prem RS subsetD RS SigmaE2) 1);
by (assume_tac 1);
by (asm_simp_tac (!simpset addsimps [o_def,prod_fun,Abs_llist_inverse]) 1);
qed "prod_fun_lemma";

goal LList.thy
    "prod_fun Rep_llist  Rep_llist `` range(%x. (x, x)) = \
\    diag(llist(range Leaf))";
by (rtac equalityI 1);
by (fast_tac (univ_cs addIs [Rep_llist]) 1);
by (fast_tac (univ_cs addSEs [Abs_llist_inverse RS subst]) 1);
qed "prod_fun_range_eq_diag";

(** To show two llists are equal, exhibit a bisimulation! 
      [also admits true equality] **)
val [prem1,prem2] = goalw LList.thy [llistD_Fun_def]
    "[| (l1,l2) : r;  r <= llistD_Fun(r Un range(%x.(x,x))) |] ==> l1=l2";
by (rtac (inj_Rep_llist RS injD) 1);
by (res_inst_tac [("r", "prod_fun Rep_llist Rep_llist ``r"),
                  ("A", "range(Leaf)")] 
        LList_equalityI 1);
by (rtac (prem1 RS prod_fun_imageI) 1);
by (rtac (prem2 RS image_mono RS subset_trans) 1);
by (rtac (image_compose RS subst) 1);
by (rtac (prod_fun_compose RS subst) 1);
by (rtac (image_Un RS ssubst) 1);
by (stac prod_fun_range_eq_diag 1);
by (rtac (LListD_Fun_subset_Sigma_llist RS prod_fun_lemma) 1);
by (rtac (subset_Sigma_llist RS Un_least) 1);
by (rtac diag_subset_Sigma 1);
qed "llist_equalityI";

(** Rules to prove the 2nd premise of llist_equalityI **)
goalw LList.thy [llistD_Fun_def,LNil_def] "(LNil,LNil) : llistD_Fun(r)";
by (rtac (LListD_Fun_NIL_I RS prod_fun_imageI) 1);
qed "llistD_Fun_LNil_I";

val [prem] = goalw LList.thy [llistD_Fun_def,LCons_def]
    "(l1,l2):r ==> (LCons x l1, LCons x l2) : llistD_Fun(r)";
by (rtac (rangeI RS LListD_Fun_CONS_I RS prod_fun_imageI) 1);
by (rtac (prem RS prod_fun_imageI) 1);
qed "llistD_Fun_LCons_I";

(*Utilise the "strong" part, i.e. gfp(f)*)
goalw LList.thy [llistD_Fun_def]
     "!!l. (l,l) : llistD_Fun(r Un range(%x.(x,x)))";
by (rtac (Rep_llist_inverse RS subst) 1);
by (rtac prod_fun_imageI 1);
by (rtac (image_Un RS ssubst) 1);
by (stac prod_fun_range_eq_diag 1);
by (rtac (Rep_llist RS LListD_Fun_diag_I) 1);
qed "llistD_Fun_range_I";

(*A special case of list_equality for functions over lazy lists*)
val [prem1,prem2] = goal LList.thy
    "[| f(LNil)=g(LNil);                                                \
\       !!x l. (f(LCons x l),g(LCons x l)) :                            \
\              llistD_Fun(range(%u. (f(u),g(u))) Un range(%v. (v,v)))   \
\    |] ==> f(l) = (g(l :: 'a llist) :: 'b llist)";
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

goal LList.thy "lmap f LNil = LNil";
by (rtac (lmap_def RS def_llist_corec RS trans) 1);
by (Simp_tac 1);
qed "lmap_LNil";

goal LList.thy "lmap f (LCons M N) = LCons (f M) (lmap f N)";
by (rtac (lmap_def RS def_llist_corec RS trans) 1);
by (Simp_tac 1);
qed "lmap_LCons";


(** Two easy results about lmap **)

goal LList.thy "lmap (f o g) l = lmap f (lmap g l)";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS (simp_tac (!simpset addsimps [lmap_LNil, lmap_LCons])));
qed "lmap_compose";

goal LList.thy "lmap (%x.x) l = l";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS (simp_tac (!simpset addsimps [lmap_LNil, lmap_LCons])));
qed "lmap_ident";


(*** iterates -- llist_fun_equalityI cannot be used! ***)

goal LList.thy "iterates f x = LCons x (iterates f (f x))";
by (rtac (iterates_def RS def_llist_corec RS trans) 1);
by (Simp_tac 1);
qed "iterates";

goal LList.thy "lmap f (iterates f x) = iterates f (f x)";
by (res_inst_tac [("r", "range(%u.(lmap f (iterates f u),iterates f (f u)))")] 
    llist_equalityI 1);
by (rtac rangeI 1);
by (safe_tac set_cs);
by (res_inst_tac [("x1", "f(u)")] (iterates RS ssubst) 1);
by (res_inst_tac [("x1", "u")] (iterates RS ssubst) 1);
by (simp_tac (!simpset addsimps [lmap_LCons]) 1);
qed "lmap_iterates";

goal LList.thy "iterates f x = LCons x (lmap f (iterates f x))";
by (rtac (lmap_iterates RS ssubst) 1);
by (rtac iterates 1);
qed "iterates_lmap";

(*** A rather complex proof about iterates -- cf Andy Pitts ***)

(** Two lemmas about natrec n x (%m.g), which is essentially (g^n)(x) **)

goal LList.thy
    "nat_rec n (LCons b l) (%m. lmap(f)) =      \
\    LCons (nat_rec n b (%m. f)) (nat_rec n l (%m. lmap(f)))";
by (nat_ind_tac "n" 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps [lmap_LCons])));
qed "fun_power_lmap";

goal Nat.thy "nat_rec n (g x) (%m. g) = nat_rec (Suc n) x (%m. g)";
by (nat_ind_tac "n" 1);
by (ALLGOALS Asm_simp_tac);
qed "fun_power_Suc";

val Pair_cong = read_instantiate_sg (sign_of Prod.thy)
 [("f","Pair")] (standard(refl RS cong RS cong));

(*The bisimulation consists of {(lmap(f)^n (h(u)), lmap(f)^n (iterates(f,u)))}
  for all u and all n::nat.*)
val [prem] = goal LList.thy
    "(!!x. h(x) = LCons x (lmap f (h x))) ==> h = iterates(f)";
by (rtac ext 1);
by (res_inst_tac [("r", 
   "UN u. range(%n. (nat_rec n (h u) (%m y.lmap f y), \
\                    nat_rec n (iterates f u) (%m y.lmap f y)))")] 
    llist_equalityI 1);
by (REPEAT (resolve_tac [UN1_I, range_eqI, Pair_cong, nat_rec_0 RS sym] 1));
by (safe_tac set_cs);
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

goalw LList.thy [lappend_def] "lappend LNil LNil = LNil";
by (rtac (llist_corec RS trans) 1);
by (Simp_tac 1);
qed "lappend_LNil_LNil";

goalw LList.thy [lappend_def]
    "lappend LNil (LCons l l') = LCons l (lappend LNil l')";
by (rtac (llist_corec RS trans) 1);
by (Simp_tac 1);
qed "lappend_LNil_LCons";

goalw LList.thy [lappend_def]
    "lappend (LCons l l') N = LCons l (lappend l' N)";
by (rtac (llist_corec RS trans) 1);
by (Simp_tac 1);
qed "lappend_LCons";

goal LList.thy "lappend LNil l = l";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS 
    (simp_tac (!simpset addsimps [lappend_LNil_LNil, lappend_LNil_LCons])));
qed "lappend_LNil";

goal LList.thy "lappend l LNil = l";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (ALLGOALS 
    (simp_tac (!simpset addsimps [lappend_LNil_LNil, lappend_LCons])));
qed "lappend_LNil2";

(*The infinite first argument blocks the second*)
goal LList.thy "lappend (iterates f x) N = iterates f x";
by (res_inst_tac [("r", "range(%u.(lappend (iterates f u) N,iterates f u))")] 
    llist_equalityI 1);
by (rtac rangeI 1);
by (safe_tac set_cs);
by (stac iterates 1);
by (simp_tac (!simpset addsimps [lappend_LCons]) 1);
qed "lappend_iterates";

(** Two proofs that lmap distributes over lappend **)

(*Long proof requiring case analysis on both both arguments*)
goal LList.thy "lmap f (lappend l n) = lappend (lmap f l) (lmap f n)";
by (res_inst_tac 
    [("r",  
      "UN n. range(%l.(lmap f (lappend l n),lappend (lmap f l) (lmap f n)))")] 
    llist_equalityI 1);
by (rtac UN1_I 1);
by (rtac rangeI 1);
by (safe_tac set_cs);
by (res_inst_tac [("l", "l")] llistE 1);
by (res_inst_tac [("l", "n")] llistE 1);
by (ALLGOALS (asm_simp_tac (!simpset addsimps
      [lappend_LNil_LNil,lappend_LCons,lappend_LNil_LCons,
       lmap_LNil,lmap_LCons])));
by (REPEAT_SOME (ares_tac [llistD_Fun_LCons_I, UN1_I RS UnI1, rangeI]));
by (rtac range_eqI 1);
by (rtac (refl RS Pair_cong) 1);
by (stac lmap_LNil 1);
by (rtac refl 1);
qed "lmap_lappend_distrib";

(*Shorter proof of theorem above using llist_equalityI as strong coinduction*)
goal LList.thy "lmap f (lappend l n) = lappend (lmap f l) (lmap f n)";
by (res_inst_tac [("l","l")] llist_fun_equalityI 1);
by (simp_tac (!simpset addsimps [lappend_LNil, lmap_LNil])1);
by (simp_tac (!simpset addsimps [lappend_LCons, lmap_LCons]) 1);
qed "lmap_lappend_distrib";

(*Without strong coinduction, three case analyses might be needed*)
goal LList.thy "lappend (lappend l1 l2) l3 = lappend l1 (lappend l2 l3)";
by (res_inst_tac [("l","l1")] llist_fun_equalityI 1);
by (simp_tac (!simpset addsimps [lappend_LNil])1);
by (simp_tac (!simpset addsimps [lappend_LCons]) 1);
qed "lappend_assoc";
