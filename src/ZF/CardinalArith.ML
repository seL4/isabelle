(*  Title: 	ZF/CardinalArith.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinal arithmetic -- WITHOUT the Axiom of Choice
*)

open CardinalArith;

(*Use AC to discharge first premise*)
goal CardinalArith.thy
    "!!A B. [| well_ord(B,r);  A lepoll B |] ==> |A| le |B|";
by (res_inst_tac [("i","|A|"),("j","|B|")] Ord_linear_le 1);
by (REPEAT_FIRST (ares_tac [Ord_cardinal, le_eqI]));
by (rtac (eqpollI RS cardinal_cong) 1 THEN assume_tac 1);
by (rtac lepoll_trans 1);
by (rtac (well_ord_cardinal_eqpoll RS eqpoll_sym RS eqpoll_imp_lepoll) 1);
by (assume_tac 1);
by (etac (le_imp_subset RS subset_imp_lepoll RS lepoll_trans) 1);
by (rtac eqpoll_imp_lepoll 1);
by (rewtac lepoll_def);
by (etac exE 1);
by (rtac well_ord_cardinal_eqpoll 1);
by (etac well_ord_rvimage 1);
by (assume_tac 1);
val well_ord_lepoll_imp_le = result();

val case_ss = ZF_ss addsimps [Inl_iff, Inl_Inr_iff, Inr_iff, Inr_Inl_iff,
			      case_Inl, case_Inr, InlI, InrI];


(** Congruence laws for successor, cardinal addition and multiplication **)

val bij_inverse_ss =
    case_ss addsimps [bij_is_fun RS apply_type,
		      bij_converse_bij RS bij_is_fun RS apply_type,
		      left_inverse_bij, right_inverse_bij];


(*Congruence law for  succ  under equipollence*)
goalw CardinalArith.thy [eqpoll_def]
    "!!A B. A eqpoll B ==> succ(A) eqpoll succ(B)";
by (safe_tac ZF_cs);
by (rtac exI 1);
by (res_inst_tac [("c", "%z.if(z=A,B,f`z)"), 
                  ("d", "%z.if(z=B,A,converse(f)`z)")] lam_bijective 1);
by (ALLGOALS
    (asm_simp_tac (bij_inverse_ss addsimps [succI2, mem_imp_not_eq]
 		                  setloop etac succE )));
val succ_eqpoll_cong = result();

(*Congruence law for + under equipollence*)
goalw CardinalArith.thy [eqpoll_def]
    "!!A B C D. [| A eqpoll C;  B eqpoll D |] ==> A+B eqpoll C+D";
by (safe_tac ZF_cs);
by (rtac exI 1);
by (res_inst_tac [("c", "case(%x. Inl(f`x), %y. Inr(fa`y))"),
	 ("d", "case(%x. Inl(converse(f)`x), %y. Inr(converse(fa)`y))")] 
    lam_bijective 1);
by (safe_tac (ZF_cs addSEs [sumE]));
by (ALLGOALS (asm_simp_tac bij_inverse_ss));
val sum_eqpoll_cong = result();

(*Congruence law for * under equipollence*)
goalw CardinalArith.thy [eqpoll_def]
    "!!A B C D. [| A eqpoll C;  B eqpoll D |] ==> A*B eqpoll C*D";
by (safe_tac ZF_cs);
by (rtac exI 1);
by (res_inst_tac [("c", "split(%x y. <f`x, fa`y>)"),
		  ("d", "split(%x y. <converse(f)`x, converse(fa)`y>)")] 
    lam_bijective 1);
by (safe_tac ZF_cs);
by (ALLGOALS (asm_simp_tac bij_inverse_ss));
val prod_eqpoll_cong = result();


(*** Cardinal addition ***)

(** Cardinal addition is commutative **)

(*Easier to prove the two directions separately*)
goalw CardinalArith.thy [eqpoll_def] "A+B eqpoll B+A";
by (rtac exI 1);
by (res_inst_tac [("c", "case(Inr, Inl)"), ("d", "case(Inr, Inl)")] 
    lam_bijective 1);
by (safe_tac (ZF_cs addSEs [sumE]));
by (ALLGOALS (asm_simp_tac case_ss));
val sum_commute_eqpoll = result();

goalw CardinalArith.thy [cadd_def] "i |+| j = j |+| i";
by (rtac (sum_commute_eqpoll RS cardinal_cong) 1);
val cadd_commute = result();

(** Cardinal addition is associative **)

goalw CardinalArith.thy [eqpoll_def] "(A+B)+C eqpoll A+(B+C)";
by (rtac exI 1);
by (res_inst_tac [("c", "case(case(Inl, %y.Inr(Inl(y))), %y. Inr(Inr(y)))"),
		  ("d", "case(%x.Inl(Inl(x)), case(%x.Inl(Inr(x)), Inr))")] 
    lam_bijective 1);
by (ALLGOALS (asm_simp_tac (case_ss setloop etac sumE)));
val sum_assoc_eqpoll = result();

(*Unconditional version requires AC*)
goalw CardinalArith.thy [cadd_def]
    "!!i j k. [| Ord(i); Ord(j); Ord(k) |] ==>	\
\             (i |+| j) |+| k = i |+| (j |+| k)";
by (rtac cardinal_cong 1);
br ([well_ord_cardinal_eqpoll, eqpoll_refl] MRS sum_eqpoll_cong RS
    eqpoll_trans) 1;
by (rtac (sum_assoc_eqpoll RS eqpoll_trans) 2);
br ([eqpoll_refl, well_ord_cardinal_eqpoll] MRS sum_eqpoll_cong RS
    eqpoll_sym) 2;
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel] 1));
val Ord_cadd_assoc = result();

(** 0 is the identity for addition **)

goalw CardinalArith.thy [eqpoll_def] "0+A eqpoll A";
by (rtac exI 1);
by (res_inst_tac [("c", "case(%x.x, %y.y)"), ("d", "Inr")] 
    lam_bijective 1);
by (ALLGOALS (asm_simp_tac (case_ss setloop eresolve_tac [sumE,emptyE])));
val sum_0_eqpoll = result();

goalw CardinalArith.thy [cadd_def] "!!i. Card(i) ==> 0 |+| i = i";
by (asm_simp_tac (ZF_ss addsimps [sum_0_eqpoll RS cardinal_cong, 
				  Card_cardinal_eq]) 1);
val cadd_0 = result();

(** Addition of finite cardinals is "ordinary" addition **)

goalw CardinalArith.thy [eqpoll_def] "succ(A)+B eqpoll succ(A+B)";
by (rtac exI 1);
by (res_inst_tac [("c", "%z.if(z=Inl(A),A+B,z)"), 
		  ("d", "%z.if(z=A+B,Inl(A),z)")] 
    lam_bijective 1);
by (ALLGOALS
    (asm_simp_tac (case_ss addsimps [succI2, mem_imp_not_eq]
		           setloop eresolve_tac [sumE,succE])));
val sum_succ_eqpoll = result();

(*Pulling the  succ(...)  outside the |...| requires m, n: nat  *)
(*Unconditional version requires AC*)
goalw CardinalArith.thy [cadd_def]
    "!!m n. [| Ord(m);  Ord(n) |] ==> succ(m) |+| n = |succ(m |+| n)|";
by (rtac (sum_succ_eqpoll RS cardinal_cong RS trans) 1);
by (rtac (succ_eqpoll_cong RS cardinal_cong) 1);
by (rtac (well_ord_cardinal_eqpoll RS eqpoll_sym) 1);
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel] 1));
val cadd_succ_lemma = result();

val [mnat,nnat] = goal CardinalArith.thy
    "[| m: nat;  n: nat |] ==> m |+| n = m#+n";
by (cut_facts_tac [nnat] 1);
by (nat_ind_tac "m" [mnat] 1);
by (asm_simp_tac (arith_ss addsimps [nat_into_Card RS cadd_0]) 1);
by (asm_simp_tac (arith_ss addsimps [nat_into_Ord, cadd_succ_lemma,
				     nat_into_Card RS Card_cardinal_eq]) 1);
val nat_cadd_eq_add = result();


(*** Cardinal multiplication ***)

(** Cardinal multiplication is commutative **)

(*Easier to prove the two directions separately*)
goalw CardinalArith.thy [eqpoll_def] "A*B eqpoll B*A";
by (rtac exI 1);
by (res_inst_tac [("c", "split(%x y.<y,x>)"), ("d", "split(%x y.<y,x>)")] 
    lam_bijective 1);
by (safe_tac ZF_cs);
by (ALLGOALS (asm_simp_tac ZF_ss));
val prod_commute_eqpoll = result();

goalw CardinalArith.thy [cmult_def] "i |*| j = j |*| i";
by (rtac (prod_commute_eqpoll RS cardinal_cong) 1);
val cmult_commute = result();

(** Cardinal multiplication is associative **)

goalw CardinalArith.thy [eqpoll_def] "(A*B)*C eqpoll A*(B*C)";
by (rtac exI 1);
by (res_inst_tac [("c", "split(%w z. split(%x y. <x,<y,z>>, w))"),
		  ("d", "split(%x.   split(%y z. <<x,y>, z>))")] 
    lam_bijective 1);
by (safe_tac ZF_cs);
by (ALLGOALS (asm_simp_tac ZF_ss));
val prod_assoc_eqpoll = result();

(*Unconditional version requires AC*)
goalw CardinalArith.thy [cmult_def]
    "!!i j k. [| Ord(i); Ord(j); Ord(k) |] ==>	\
\             (i |*| j) |*| k = i |*| (j |*| k)";
by (rtac cardinal_cong 1);
br ([well_ord_cardinal_eqpoll, eqpoll_refl] MRS prod_eqpoll_cong RS
    eqpoll_trans) 1;
by (rtac (prod_assoc_eqpoll RS eqpoll_trans) 2);
br ([eqpoll_refl, well_ord_cardinal_eqpoll] MRS prod_eqpoll_cong RS
    eqpoll_sym) 2;
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel] 1));
val Ord_cmult_assoc = result();

(** Cardinal multiplication distributes over addition **)

goalw CardinalArith.thy [eqpoll_def] "(A+B)*C eqpoll (A*C)+(B*C)";
by (rtac exI 1);
by (res_inst_tac
    [("c", "split(%x z. case(%y.Inl(<y,z>), %y.Inr(<y,z>), x))"),
     ("d", "case(split(%x y.<Inl(x),y>), split(%x y.<Inr(x),y>))")] 
    lam_bijective 1);
by (safe_tac (ZF_cs addSEs [sumE]));
by (ALLGOALS (asm_simp_tac case_ss));
val sum_prod_distrib_eqpoll = result();

goalw CardinalArith.thy [lepoll_def, inj_def] "A lepoll A*A";
by (res_inst_tac [("x", "lam x:A. <x,x>")] exI 1);
by (simp_tac (ZF_ss addsimps [lam_type]) 1);
val prod_square_lepoll = result();

goalw CardinalArith.thy [cmult_def] "!!k. Card(k) ==> k le k |*| k";
by (rtac le_trans 1);
by (rtac well_ord_lepoll_imp_le 2);
by (rtac prod_square_lepoll 3);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel, Card_is_Ord] 2));
by (asm_simp_tac (ZF_ss addsimps [le_refl, Card_is_Ord, Card_cardinal_eq]) 1);
val cmult_square_le = result();

(** Multiplication by 0 yields 0 **)

goalw CardinalArith.thy [eqpoll_def] "0*A eqpoll 0";
by (rtac exI 1);
by (rtac lam_bijective 1);
by (safe_tac ZF_cs);
val prod_0_eqpoll = result();

goalw CardinalArith.thy [cmult_def] "0 |*| i = 0";
by (asm_simp_tac (ZF_ss addsimps [prod_0_eqpoll RS cardinal_cong, 
				  Card_0 RS Card_cardinal_eq]) 1);
val cmult_0 = result();

(** 1 is the identity for multiplication **)

goalw CardinalArith.thy [eqpoll_def] "{x}*A eqpoll A";
by (rtac exI 1);
by (res_inst_tac [("c", "snd"), ("d", "%z.<x,z>")] lam_bijective 1);
by (safe_tac ZF_cs);
by (ALLGOALS (asm_simp_tac ZF_ss));
val prod_singleton_eqpoll = result();

goalw CardinalArith.thy [cmult_def, succ_def] "!!i. Card(i) ==> 1 |*| i = i";
by (asm_simp_tac (ZF_ss addsimps [prod_singleton_eqpoll RS cardinal_cong, 
				  Card_cardinal_eq]) 1);
val cmult_1 = result();

(** Multiplication of finite cardinals is "ordinary" multiplication **)

goalw CardinalArith.thy [eqpoll_def] "succ(A)*B eqpoll B + A*B";
by (rtac exI 1);
by (res_inst_tac [("c", "split(%x y. if(x=A, Inl(y), Inr(<x,y>)))"), 
		  ("d", "case(%y. <A,y>, %z.z)")] 
    lam_bijective 1);
by (safe_tac (ZF_cs addSEs [sumE]));
by (ALLGOALS
    (asm_simp_tac (case_ss addsimps [succI2, if_type, mem_imp_not_eq])));
val prod_succ_eqpoll = result();


(*Unconditional version requires AC*)
goalw CardinalArith.thy [cmult_def, cadd_def]
    "!!m n. [| Ord(m);  Ord(n) |] ==> succ(m) |*| n = n |+| (m |*| n)";
by (rtac (prod_succ_eqpoll RS cardinal_cong RS trans) 1);
by (rtac (cardinal_cong RS sym) 1);
by (rtac ([eqpoll_refl, well_ord_cardinal_eqpoll] MRS sum_eqpoll_cong) 1);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel] 1));
val cmult_succ_lemma = result();

val [mnat,nnat] = goal CardinalArith.thy
    "[| m: nat;  n: nat |] ==> m |*| n = m#*n";
by (cut_facts_tac [nnat] 1);
by (nat_ind_tac "m" [mnat] 1);
by (asm_simp_tac (arith_ss addsimps [cmult_0]) 1);
by (asm_simp_tac (arith_ss addsimps [nat_into_Ord, cmult_succ_lemma,
				     nat_cadd_eq_add]) 1);
val nat_cmult_eq_mult = result();


(*** Infinite Cardinals are Limit Ordinals ***)

goalw CardinalArith.thy [lepoll_def, inj_def]
    "!!i. nat <= A ==> succ(A) lepoll A";
by (res_inst_tac [("x",
   "lam z:succ(A). if(z=A, 0, if(z:nat, succ(z), z))")] exI 1);
by (rtac (lam_type RS CollectI) 1);
by (rtac if_type 1);
by (etac ([asm_rl, nat_0I] MRS subsetD) 1);
by (etac succE 1);
by (contr_tac 1);
by (rtac if_type 1);
by (assume_tac 2);
by (etac ([asm_rl, nat_succI] MRS subsetD) 1 THEN assume_tac 1);
by (REPEAT (rtac ballI 1));
by (asm_simp_tac 
    (ZF_ss addsimps [succ_inject_iff, succ_not_0, succ_not_0 RS not_sym]
           setloop split_tac [expand_if]) 1);
by (safe_tac (ZF_cs addSIs [nat_0I, nat_succI]));
val nat_succ_lepoll = result();

goal CardinalArith.thy "!!i. nat <= A ==> succ(A) eqpoll A";
by (etac (nat_succ_lepoll RS eqpollI) 1);
by (rtac (subset_succI RS subset_imp_lepoll) 1);
val nat_succ_eqpoll = result();

goalw CardinalArith.thy [InfCard_def] "!!i. InfCard(i) ==> Card(i)";
by (etac conjunct1 1);
val InfCard_is_Card = result();

(*Kunen's Lemma 10.11*)
goalw CardinalArith.thy [InfCard_def] "!!i. InfCard(i) ==> Limit(i)";
by (etac conjE 1);
by (rtac (ltI RS non_succ_LimitI) 1);
by (etac ([asm_rl, nat_0I] MRS (le_imp_subset RS subsetD)) 1);
by (etac Card_is_Ord 1);
by (safe_tac (ZF_cs addSDs [Limit_nat RS Limit_le_succD]));
by (forward_tac [Card_is_Ord RS Ord_succD] 1);
by (rewtac Card_def);
by (res_inst_tac [("i", "succ(y)")] lt_irrefl 1);
by (dtac (le_imp_subset RS nat_succ_eqpoll RS cardinal_cong) 1);
(*Tricky combination of substitutions; backtracking needed*)
by (etac ssubst 1 THEN etac ssubst 1 THEN rtac Ord_cardinal_le 1);
by (assume_tac 1);
val InfCard_is_Limit = result();



(*** An infinite cardinal equals its square (Kunen, Thm 10.12, page 29) ***)

(*A general fact about ordermap*)
goalw Cardinal.thy [eqpoll_def]
    "!!A. [| well_ord(A,r);  x:A |] ==> ordermap(A,r)`x eqpoll pred(A,x,r)";
by (rtac exI 1);
by (asm_simp_tac (ZF_ss addsimps [ordermap_eq_image, well_ord_is_wf]) 1);
by (etac (ordertype_bij RS bij_is_inj RS restrict_bij RS bij_converse_bij) 1);
by (rtac pred_subset 1);
val ordermap_eqpoll_pred = result();

(** Establishing the well-ordering **)

goalw CardinalArith.thy [inj_def]
 "!!k. Ord(k) ==>	\
\ (lam z:k*k. split(%x y. <x Un y, <x, y>>, z)) : inj(k*k, k*k*k)";
by (safe_tac ZF_cs);
by (fast_tac (ZF_cs addIs [lam_type, Un_least_lt RS ltD, ltI]
                    addSEs [split_type]) 1);
by (asm_full_simp_tac ZF_ss 1);
val csquare_lam_inj = result();

goalw CardinalArith.thy [csquare_rel_def]
 "!!k. Ord(k) ==> well_ord(k*k, csquare_rel(k))";
by (rtac (csquare_lam_inj RS well_ord_rvimage) 1);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel] 1));
val well_ord_csquare = result();

(** Characterising initial segments of the well-ordering **)

goalw CardinalArith.thy [csquare_rel_def]
 "!!k. [| x<k;  y<k;  z<k |] ==> \
\      <<x,y>, <z,z>> : csquare_rel(k) --> x le z & y le z";
by (REPEAT (etac ltE 1));
by (asm_simp_tac (ZF_ss addsimps [rvimage_iff, rmult_iff, Memrel_iff,
                                  Un_absorb, Un_least_mem_iff, ltD]) 1);
by (safe_tac (ZF_cs addSEs [mem_irrefl] 
                    addSIs [Un_upper1_le, Un_upper2_le]));
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps [lt_def, succI2, Ord_succ])));
val csquareD_lemma = result();
val csquareD = csquareD_lemma RS mp |> standard;

goalw CardinalArith.thy [pred_def]
 "!!k. z<k ==> pred(k*k, <z,z>, csquare_rel(k)) <= succ(z)*succ(z)";
by (safe_tac (lemmas_cs addSEs [SigmaE]));	(*avoids using succCI*)
by (rtac (csquareD RS conjE) 1);
by (rewtac lt_def);
by (assume_tac 4);
by (ALLGOALS (fast_tac ZF_cs));
val pred_csquare_subset = result();

goalw CardinalArith.thy [csquare_rel_def]
 "!!k. [| x<z;  y<z;  z<k |] ==> \
\      <<x,y>, <z,z>> : csquare_rel(k)";
by (subgoals_tac ["x<k", "y<k"] 1);
by (REPEAT (eresolve_tac [asm_rl, lt_trans] 2));
by (REPEAT (etac ltE 1));
by (asm_simp_tac (ZF_ss addsimps [rvimage_iff, rmult_iff, Memrel_iff,
                                  Un_absorb, Un_least_mem_iff, ltD]) 1);
val csquare_ltI = result();

(*Part of the traditional proof.  UNUSED since it's harder to prove & apply *)
goalw CardinalArith.thy [csquare_rel_def]
 "!!k. [| x le z;  y le z;  z<k |] ==> \
\      <<x,y>, <z,z>> : csquare_rel(k) | x=z & y=z";
by (subgoals_tac ["x<k", "y<k"] 1);
by (REPEAT (eresolve_tac [asm_rl, lt_trans1] 2));
by (REPEAT (etac ltE 1));
by (asm_simp_tac (ZF_ss addsimps [rvimage_iff, rmult_iff, Memrel_iff,
                                  Un_absorb, Un_least_mem_iff, ltD]) 1);
by (REPEAT_FIRST (etac succE));
by (ALLGOALS
    (asm_simp_tac (ZF_ss addsimps [subset_Un_iff RS iff_sym, 
				   subset_Un_iff2 RS iff_sym, OrdmemD])));
val csquare_or_eqI = result();

(** The cardinality of initial segments **)

goal CardinalArith.thy
    "!!k. [| InfCard(k);  x<k;  y<k;  z=succ(x Un y) |] ==> \
\         ordermap(k*k, csquare_rel(k)) ` <x,y> lepoll 		\
\         ordermap(k*k, csquare_rel(k)) ` <z,z>";
by (subgoals_tac ["z<k", "well_ord(k*k, csquare_rel(k))"] 1);
by (etac (InfCard_is_Card RS Card_is_Ord RS well_ord_csquare) 2);
by (fast_tac (ZF_cs addSIs [Un_least_lt, InfCard_is_Limit, Limit_has_succ]) 2);
by (rtac (OrdmemD RS subset_imp_lepoll) 1);
by (res_inst_tac [("z1","z")] (csquare_ltI RS less_imp_ordermap_in) 1);
by (etac well_ord_is_wf 4);
by (ALLGOALS 
    (fast_tac (ZF_cs addSIs [Un_upper1_le, Un_upper2_le, Ord_ordermap] 
                     addSEs [ltE])));
val ordermap_z_lepoll = result();

(*Kunen: "each <x,y>: k*k has no more than z*z predecessors..." (page 29) *)
goalw CardinalArith.thy [cmult_def]
  "!!k. [| InfCard(k);  x<k;  y<k;  z=succ(x Un y) |] ==> \
\       | ordermap(k*k, csquare_rel(k)) ` <x,y> | le  |succ(z)| |*| |succ(z)|";
by (rtac (well_ord_rmult RS well_ord_lepoll_imp_le) 1);
by (REPEAT (ares_tac [Ord_cardinal, well_ord_Memrel] 1));
by (subgoals_tac ["z<k"] 1);
by (fast_tac (ZF_cs addSIs [Un_least_lt, InfCard_is_Limit, 
                            Limit_has_succ]) 2);
by (rtac (ordermap_z_lepoll RS lepoll_trans) 1);
by (REPEAT_SOME assume_tac);
by (rtac (ordermap_eqpoll_pred RS eqpoll_imp_lepoll RS lepoll_trans) 1);
by (etac (InfCard_is_Card RS Card_is_Ord RS well_ord_csquare) 1);
by (fast_tac (ZF_cs addIs [ltD]) 1);
by (rtac (pred_csquare_subset RS subset_imp_lepoll RS lepoll_trans) 1 THEN
    assume_tac 1);
by (REPEAT_FIRST (etac ltE));
by (rtac (prod_eqpoll_cong RS eqpoll_sym RS eqpoll_imp_lepoll) 1);
by (REPEAT_FIRST (etac (Ord_succ RS Ord_cardinal_eqpoll)));
val ordermap_csquare_le = result();

(*Kunen: "... so the order type <= k" *)
goal CardinalArith.thy
    "!!k. [| InfCard(k);  ALL y:k. InfCard(y) --> y |*| y = y |]  ==>  \
\         ordertype(k*k, csquare_rel(k)) le k";
by (forward_tac [InfCard_is_Card RS Card_is_Ord] 1);
by (rtac all_lt_imp_le 1);
by (assume_tac 1);
by (etac (well_ord_csquare RS Ord_ordertype) 1);
by (rtac Card_lt_imp_lt 1);
by (etac InfCard_is_Card 3);
by (etac ltE 2 THEN assume_tac 2);
by (asm_full_simp_tac (ZF_ss addsimps [ordertype_unfold]) 1);
by (safe_tac (ZF_cs addSEs [ltE]));
by (subgoals_tac ["Ord(xb)", "Ord(y)"] 1);
by (REPEAT (eresolve_tac [asm_rl, Ord_in_Ord] 2));
by (rtac (ordermap_csquare_le RS lt_trans1) 1  THEN
    REPEAT (ares_tac [refl] 1 ORELSE etac ltI 1));
by (res_inst_tac [("i","xb Un y"), ("j","nat")] Ord_linear2 1  THEN
    REPEAT (ares_tac [Ord_Un, Ord_nat] 1));
(*the finite case: xb Un y < nat *)
by (res_inst_tac [("j", "nat")] lt_trans2 1);
by (asm_full_simp_tac (FOL_ss addsimps [InfCard_def]) 2);
by (asm_full_simp_tac
    (ZF_ss addsimps [lt_def, nat_cmult_eq_mult, nat_succI, mult_type,
		     nat_into_Card RS Card_cardinal_eq, Ord_nat]) 1);
(*case nat le (xb Un y), equivalently InfCard(xb Un y)  *)
by (asm_full_simp_tac
    (ZF_ss addsimps [le_imp_subset RS nat_succ_eqpoll RS cardinal_cong,
		     le_succ_iff, InfCard_def, Card_cardinal, Un_least_lt, 
		     Ord_Un, ltI, nat_le_cardinal,
		     Ord_cardinal_le RS lt_trans1 RS ltD]) 1);
val ordertype_csquare_le = result();

(*This lemma can easily be generalized to premise well_ord(A*A,r) *)
goalw CardinalArith.thy [cmult_def]
    "!!k. Ord(k) ==> k |*| k  =  |ordertype(k*k, csquare_rel(k))|";
by (rtac cardinal_cong 1);
by (rewtac eqpoll_def);
by (rtac exI 1);
by (etac (well_ord_csquare RS ordertype_bij) 1);
val csquare_eq_ordertype = result();

(*Main result: Kunen's Theorem 10.12*)
goal CardinalArith.thy
    "!!k. InfCard(k) ==> k |*| k = k";
by (forward_tac [InfCard_is_Card RS Card_is_Ord] 1);
by (etac rev_mp 1);
by (trans_ind_tac "k" [] 1);
by (rtac impI 1);
by (rtac le_anti_sym 1);
by (etac (InfCard_is_Card RS cmult_square_le) 2);
by (rtac (ordertype_csquare_le RSN (2, le_trans)) 1);
by (assume_tac 2);
by (assume_tac 2);
by (asm_simp_tac 
    (ZF_ss addsimps [csquare_eq_ordertype, Ord_cardinal_le,
                     well_ord_csquare RS Ord_ordertype]) 1);
val InfCard_csquare_eq = result();
