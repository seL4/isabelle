(*  Title: 	ZF/CardinalArith.ML
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinal arithmetic -- WITHOUT the Axiom of Choice

Note: Could omit proving the associative laws for cardinal addition and
multiplication.  On finite cardinals these operations coincide with
addition and multiplication of natural numbers; on infinite cardinals they
coincide with union (maximum).  Either way we get associativity for free.
*)

open CardinalArith;

(*** Elementary properties ***)

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
qed "well_ord_lepoll_imp_Card_le";

(*Each element of Fin(A) is equivalent to a natural number*)
goal CardinalArith.thy
    "!!X A. X: Fin(A) ==> EX n:nat. X eqpoll n";
by (etac Fin_induct 1);
by (fast_tac (ZF_cs addIs [eqpoll_refl, nat_0I]) 1);
by (fast_tac (ZF_cs addSIs [cons_eqpoll_cong, 
			    rewrite_rule [succ_def] nat_succI] 
                            addSEs [mem_irrefl]) 1);
qed "Fin_eqpoll";

(*** Cardinal addition ***)

(** Cardinal addition is commutative **)

goalw CardinalArith.thy [eqpoll_def] "A+B eqpoll B+A";
by (rtac exI 1);
by (res_inst_tac [("c", "case(Inr, Inl)"), ("d", "case(Inr, Inl)")] 
    lam_bijective 1);
by (safe_tac (ZF_cs addSEs [sumE]));
by (ALLGOALS (asm_simp_tac case_ss));
qed "sum_commute_eqpoll";

goalw CardinalArith.thy [cadd_def] "i |+| j = j |+| i";
by (rtac (sum_commute_eqpoll RS cardinal_cong) 1);
qed "cadd_commute";

(** Cardinal addition is associative **)

goalw CardinalArith.thy [eqpoll_def] "(A+B)+C eqpoll A+(B+C)";
by (rtac exI 1);
by (res_inst_tac [("c", "case(case(Inl, %y.Inr(Inl(y))), %y. Inr(Inr(y)))"),
		  ("d", "case(%x.Inl(Inl(x)), case(%x.Inl(Inr(x)), Inr))")] 
    lam_bijective 1);
by (ALLGOALS (asm_simp_tac (case_ss setloop etac sumE)));
qed "sum_assoc_eqpoll";

(*Unconditional version requires AC*)
goalw CardinalArith.thy [cadd_def]
    "!!i j k. [| well_ord(i,ri); well_ord(j,rj); well_ord(k,rk) |] ==>	\
\             (i |+| j) |+| k = i |+| (j |+| k)";
by (rtac cardinal_cong 1);
by (rtac ([well_ord_cardinal_eqpoll, eqpoll_refl] MRS sum_eqpoll_cong RS
	  eqpoll_trans) 1);
by (rtac (sum_assoc_eqpoll RS eqpoll_trans) 2);
by (rtac ([eqpoll_refl, well_ord_cardinal_eqpoll] MRS sum_eqpoll_cong RS
	  eqpoll_sym) 2);
by (REPEAT (ares_tac [well_ord_radd] 1));
qed "well_ord_cadd_assoc";

(** 0 is the identity for addition **)

goalw CardinalArith.thy [eqpoll_def] "0+A eqpoll A";
by (rtac exI 1);
by (res_inst_tac [("c", "case(%x.x, %y.y)"), ("d", "Inr")] 
    lam_bijective 1);
by (ALLGOALS (asm_simp_tac (case_ss setloop eresolve_tac [sumE,emptyE])));
qed "sum_0_eqpoll";

goalw CardinalArith.thy [cadd_def] "!!K. Card(K) ==> 0 |+| K = K";
by (asm_simp_tac (ZF_ss addsimps [sum_0_eqpoll RS cardinal_cong, 
				  Card_cardinal_eq]) 1);
qed "cadd_0";

(** Addition by another cardinal **)

goalw CardinalArith.thy [lepoll_def, inj_def] "A lepoll A+B";
by (res_inst_tac [("x", "lam x:A. Inl(x)")] exI 1);
by (asm_simp_tac (sum_ss addsimps [lam_type]) 1);
qed "sum_lepoll_self";

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)
goalw CardinalArith.thy [cadd_def]
    "!!K. [| Card(K);  Ord(L) |] ==> K le (K |+| L)";
by (rtac ([Card_cardinal_le, well_ord_lepoll_imp_Card_le] MRS le_trans) 1);
by (rtac sum_lepoll_self 3);
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel, Card_is_Ord] 1));
qed "cadd_le_self";

(** Monotonicity of addition **)

goalw CardinalArith.thy [lepoll_def]
     "!!A B C D. [| A lepoll C;  B lepoll D |] ==> A + B  lepoll  C + D";
by (REPEAT (etac exE 1));
by (res_inst_tac [("x", "lam z:A+B. case(%w. Inl(f`w), %y. Inr(fa`y), z)")] 
    exI 1);
by (res_inst_tac 
      [("d", "case(%w. Inl(converse(f)`w), %y. Inr(converse(fa)`y))")] 
      lam_injective 1);
by (typechk_tac ([inj_is_fun,case_type, InlI, InrI] @ ZF_typechecks));
by (etac sumE 1);
by (ALLGOALS (asm_simp_tac (sum_ss addsimps [left_inverse])));
qed "sum_lepoll_mono";

goalw CardinalArith.thy [cadd_def]
    "!!K. [| K' le K;  L' le L |] ==> (K' |+| L') le (K |+| L)";
by (safe_tac (ZF_cs addSDs [le_subset_iff RS iffD1]));
by (rtac well_ord_lepoll_imp_Card_le 1);
by (REPEAT (ares_tac [sum_lepoll_mono, subset_imp_lepoll] 2));
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel] 1));
qed "cadd_le_mono";

(** Addition of finite cardinals is "ordinary" addition **)

goalw CardinalArith.thy [eqpoll_def] "succ(A)+B eqpoll succ(A+B)";
by (rtac exI 1);
by (res_inst_tac [("c", "%z.if(z=Inl(A),A+B,z)"), 
		  ("d", "%z.if(z=A+B,Inl(A),z)")] 
    lam_bijective 1);
by (ALLGOALS
    (asm_simp_tac (case_ss addsimps [succI2, mem_imp_not_eq]
		           setloop eresolve_tac [sumE,succE])));
qed "sum_succ_eqpoll";

(*Pulling the  succ(...)  outside the |...| requires m, n: nat  *)
(*Unconditional version requires AC*)
goalw CardinalArith.thy [cadd_def]
    "!!m n. [| Ord(m);  Ord(n) |] ==> succ(m) |+| n = |succ(m |+| n)|";
by (rtac (sum_succ_eqpoll RS cardinal_cong RS trans) 1);
by (rtac (succ_eqpoll_cong RS cardinal_cong) 1);
by (rtac (well_ord_cardinal_eqpoll RS eqpoll_sym) 1);
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel] 1));
qed "cadd_succ_lemma";

val [mnat,nnat] = goal CardinalArith.thy
    "[| m: nat;  n: nat |] ==> m |+| n = m#+n";
by (cut_facts_tac [nnat] 1);
by (nat_ind_tac "m" [mnat] 1);
by (asm_simp_tac (arith_ss addsimps [nat_into_Card RS cadd_0]) 1);
by (asm_simp_tac (arith_ss addsimps [nat_into_Ord, cadd_succ_lemma,
				     nat_into_Card RS Card_cardinal_eq]) 1);
qed "nat_cadd_eq_add";


(*** Cardinal multiplication ***)

(** Cardinal multiplication is commutative **)

(*Easier to prove the two directions separately*)
goalw CardinalArith.thy [eqpoll_def] "A*B eqpoll B*A";
by (rtac exI 1);
by (res_inst_tac [("c", "split(%x y.<y,x>)"), ("d", "split(%x y.<y,x>)")] 
    lam_bijective 1);
by (safe_tac ZF_cs);
by (ALLGOALS (asm_simp_tac ZF_ss));
qed "prod_commute_eqpoll";

goalw CardinalArith.thy [cmult_def] "i |*| j = j |*| i";
by (rtac (prod_commute_eqpoll RS cardinal_cong) 1);
qed "cmult_commute";

(** Cardinal multiplication is associative **)

goalw CardinalArith.thy [eqpoll_def] "(A*B)*C eqpoll A*(B*C)";
by (rtac exI 1);
by (res_inst_tac [("c", "split(%w z. split(%x y. <x,<y,z>>, w))"),
		  ("d", "split(%x.   split(%y z. <<x,y>, z>))")] 
    lam_bijective 1);
by (safe_tac ZF_cs);
by (ALLGOALS (asm_simp_tac ZF_ss));
qed "prod_assoc_eqpoll";

(*Unconditional version requires AC*)
goalw CardinalArith.thy [cmult_def]
    "!!i j k. [| well_ord(i,ri); well_ord(j,rj); well_ord(k,rk) |] ==>	\
\             (i |*| j) |*| k = i |*| (j |*| k)";
by (rtac cardinal_cong 1);
by (rtac ([well_ord_cardinal_eqpoll, eqpoll_refl] MRS prod_eqpoll_cong RS
	  eqpoll_trans) 1);
by (rtac (prod_assoc_eqpoll RS eqpoll_trans) 2);
by (rtac ([eqpoll_refl, well_ord_cardinal_eqpoll] MRS prod_eqpoll_cong RS
	  eqpoll_sym) 2);
by (REPEAT (ares_tac [well_ord_rmult] 1));
qed "well_ord_cmult_assoc";

(** Cardinal multiplication distributes over addition **)

goalw CardinalArith.thy [eqpoll_def] "(A+B)*C eqpoll (A*C)+(B*C)";
by (rtac exI 1);
by (res_inst_tac
    [("c", "split(%x z. case(%y.Inl(<y,z>), %y.Inr(<y,z>), x))"),
     ("d", "case(split(%x y.<Inl(x),y>), split(%x y.<Inr(x),y>))")] 
    lam_bijective 1);
by (safe_tac (ZF_cs addSEs [sumE]));
by (ALLGOALS (asm_simp_tac case_ss));
qed "sum_prod_distrib_eqpoll";

(** Multiplication by 0 yields 0 **)

goalw CardinalArith.thy [eqpoll_def] "0*A eqpoll 0";
by (rtac exI 1);
by (rtac lam_bijective 1);
by (safe_tac ZF_cs);
qed "prod_0_eqpoll";

goalw CardinalArith.thy [cmult_def] "0 |*| i = 0";
by (asm_simp_tac (ZF_ss addsimps [prod_0_eqpoll RS cardinal_cong, 
				  Card_0 RS Card_cardinal_eq]) 1);
qed "cmult_0";

(** 1 is the identity for multiplication **)

goalw CardinalArith.thy [eqpoll_def] "{x}*A eqpoll A";
by (rtac exI 1);
by (res_inst_tac [("c", "snd"), ("d", "%z.<x,z>")] lam_bijective 1);
by (safe_tac ZF_cs);
by (ALLGOALS (asm_simp_tac ZF_ss));
qed "prod_singleton_eqpoll";

goalw CardinalArith.thy [cmult_def, succ_def] "!!K. Card(K) ==> 1 |*| K = K";
by (asm_simp_tac (ZF_ss addsimps [prod_singleton_eqpoll RS cardinal_cong, 
				  Card_cardinal_eq]) 1);
qed "cmult_1";

(*** Some inequalities for multiplication ***)

goalw CardinalArith.thy [lepoll_def, inj_def] "A lepoll A*A";
by (res_inst_tac [("x", "lam x:A. <x,x>")] exI 1);
by (simp_tac (ZF_ss addsimps [lam_type]) 1);
qed "prod_square_lepoll";

(*Could probably weaken the premise to well_ord(K,r), or remove using AC*)
goalw CardinalArith.thy [cmult_def] "!!K. Card(K) ==> K le K |*| K";
by (rtac le_trans 1);
by (rtac well_ord_lepoll_imp_Card_le 2);
by (rtac prod_square_lepoll 3);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel, Card_is_Ord] 2));
by (asm_simp_tac (ZF_ss addsimps [le_refl, Card_is_Ord, Card_cardinal_eq]) 1);
qed "cmult_square_le";

(** Multiplication by a non-zero cardinal **)

goalw CardinalArith.thy [lepoll_def, inj_def] "!!b. b: B ==> A lepoll A*B";
by (res_inst_tac [("x", "lam x:A. <x,b>")] exI 1);
by (asm_simp_tac (ZF_ss addsimps [lam_type]) 1);
qed "prod_lepoll_self";

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)
goalw CardinalArith.thy [cmult_def]
    "!!K. [| Card(K);  Ord(L);  0<L |] ==> K le (K |*| L)";
by (rtac ([Card_cardinal_le, well_ord_lepoll_imp_Card_le] MRS le_trans) 1);
by (rtac prod_lepoll_self 3);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel, Card_is_Ord, ltD] 1));
qed "cmult_le_self";

(** Monotonicity of multiplication **)

goalw CardinalArith.thy [lepoll_def]
     "!!A B C D. [| A lepoll C;  B lepoll D |] ==> A * B  lepoll  C * D";
by (REPEAT (etac exE 1));
by (res_inst_tac [("x", "lam z:A*B. split(%w y.<f`w, fa`y>, z)")] exI 1);
by (res_inst_tac [("d", "split(%w y.<converse(f)`w, converse(fa)`y>)")] 
		  lam_injective 1);
by (typechk_tac (inj_is_fun::ZF_typechecks));
by (etac SigmaE 1);
by (asm_simp_tac (ZF_ss addsimps [left_inverse]) 1);
qed "prod_lepoll_mono";

goalw CardinalArith.thy [cmult_def]
    "!!K. [| K' le K;  L' le L |] ==> (K' |*| L') le (K |*| L)";
by (safe_tac (ZF_cs addSDs [le_subset_iff RS iffD1]));
by (rtac well_ord_lepoll_imp_Card_le 1);
by (REPEAT (ares_tac [prod_lepoll_mono, subset_imp_lepoll] 2));
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel] 1));
qed "cmult_le_mono";

(*** Multiplication of finite cardinals is "ordinary" multiplication ***)

goalw CardinalArith.thy [eqpoll_def] "succ(A)*B eqpoll B + A*B";
by (rtac exI 1);
by (res_inst_tac [("c", "split(%x y. if(x=A, Inl(y), Inr(<x,y>)))"), 
		  ("d", "case(%y. <A,y>, %z.z)")] 
    lam_bijective 1);
by (safe_tac (ZF_cs addSEs [sumE]));
by (ALLGOALS
    (asm_simp_tac (case_ss addsimps [succI2, if_type, mem_imp_not_eq])));
qed "prod_succ_eqpoll";

(*Unconditional version requires AC*)
goalw CardinalArith.thy [cmult_def, cadd_def]
    "!!m n. [| Ord(m);  Ord(n) |] ==> succ(m) |*| n = n |+| (m |*| n)";
by (rtac (prod_succ_eqpoll RS cardinal_cong RS trans) 1);
by (rtac (cardinal_cong RS sym) 1);
by (rtac ([eqpoll_refl, well_ord_cardinal_eqpoll] MRS sum_eqpoll_cong) 1);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel] 1));
qed "cmult_succ_lemma";

val [mnat,nnat] = goal CardinalArith.thy
    "[| m: nat;  n: nat |] ==> m |*| n = m#*n";
by (cut_facts_tac [nnat] 1);
by (nat_ind_tac "m" [mnat] 1);
by (asm_simp_tac (arith_ss addsimps [cmult_0]) 1);
by (asm_simp_tac (arith_ss addsimps [nat_into_Ord, cmult_succ_lemma,
				     nat_cadd_eq_add]) 1);
qed "nat_cmult_eq_mult";

goal CardinalArith.thy "!!m n. Card(n) ==> 2 |*| n = n |+| n";
by (asm_simp_tac 
    (ZF_ss addsimps [Ord_0, Ord_succ, cmult_0, cmult_succ_lemma, Card_is_Ord,
		     read_instantiate [("j","0")] cadd_commute, cadd_0]) 1);
qed "cmult_2";


(*** Infinite Cardinals are Limit Ordinals ***)

(*This proof is modelled upon one assuming nat<=A, with injection
  lam z:cons(u,A). if(z=u, 0, if(z : nat, succ(z), z))  and inverse
  %y. if(y:nat, nat_case(u,%z.z,y), y).  If f: inj(nat,A) then
  range(f) behaves like the natural numbers.*)
goalw CardinalArith.thy [lepoll_def]
    "!!i. nat lepoll A ==> cons(u,A) lepoll A";
by (etac exE 1);
by (res_inst_tac [("x",
    "lam z:cons(u,A). if(z=u, f`0, 	\
\                        if(z: range(f), f`succ(converse(f)`z), z))")] exI 1);
by (res_inst_tac [("d", "%y. if(y: range(f), 	\
\                               nat_case(u, %z.f`z, converse(f)`y), y)")] 
    lam_injective 1);
by (fast_tac (ZF_cs addSIs [if_type, nat_0I, nat_succI, apply_type]
                    addIs  [inj_is_fun, inj_converse_fun]) 1);
by (asm_simp_tac 
    (ZF_ss addsimps [inj_is_fun RS apply_rangeI,
		     inj_converse_fun RS apply_rangeI,
		     inj_converse_fun RS apply_funtype,
		     left_inverse, right_inverse, nat_0I, nat_succI, 
		     nat_case_0, nat_case_succ]
           setloop split_tac [expand_if]) 1);
qed "nat_cons_lepoll";

goal CardinalArith.thy "!!i. nat lepoll A ==> cons(u,A) eqpoll A";
by (etac (nat_cons_lepoll RS eqpollI) 1);
by (rtac (subset_consI RS subset_imp_lepoll) 1);
qed "nat_cons_eqpoll";

(*Specialized version required below*)
goalw CardinalArith.thy [succ_def] "!!i. nat <= A ==> succ(A) eqpoll A";
by (eresolve_tac [subset_imp_lepoll RS nat_cons_eqpoll] 1);
qed "nat_succ_eqpoll";

goalw CardinalArith.thy [InfCard_def] "InfCard(nat)";
by (fast_tac (ZF_cs addIs [Card_nat, le_refl, Card_is_Ord]) 1);
qed "InfCard_nat";

goalw CardinalArith.thy [InfCard_def] "!!K. InfCard(K) ==> Card(K)";
by (etac conjunct1 1);
qed "InfCard_is_Card";

goalw CardinalArith.thy [InfCard_def]
    "!!K L. [| InfCard(K);  Card(L) |] ==> InfCard(K Un L)";
by (asm_simp_tac (ZF_ss addsimps [Card_Un, Un_upper1_le RSN (2,le_trans), 
				  Card_is_Ord]) 1);
qed "InfCard_Un";

(*Kunen's Lemma 10.11*)
goalw CardinalArith.thy [InfCard_def] "!!K. InfCard(K) ==> Limit(K)";
by (etac conjE 1);
by (forward_tac [Card_is_Ord] 1);
by (rtac (ltI RS non_succ_LimitI) 1);
by (etac ([asm_rl, nat_0I] MRS (le_imp_subset RS subsetD)) 1);
by (safe_tac (ZF_cs addSDs [Limit_nat RS Limit_le_succD]));
by (rewtac Card_def);
by (dtac trans 1);
by (etac (le_imp_subset RS nat_succ_eqpoll RS cardinal_cong) 1);
by (etac (Ord_succD RS Ord_cardinal_le RS lt_trans2 RS lt_irrefl) 1);
by (REPEAT (ares_tac [le_eqI, Ord_cardinal] 1));
qed "InfCard_is_Limit";


(*** An infinite cardinal equals its square (Kunen, Thm 10.12, page 29) ***)

(*A general fact about ordermap*)
goalw Cardinal.thy [eqpoll_def]
    "!!A. [| well_ord(A,r);  x:A |] ==> ordermap(A,r)`x eqpoll pred(A,x,r)";
by (rtac exI 1);
by (asm_simp_tac (ZF_ss addsimps [ordermap_eq_image, well_ord_is_wf]) 1);
by (etac (ordermap_bij RS bij_is_inj RS restrict_bij RS bij_converse_bij) 1);
by (rtac pred_subset 1);
qed "ordermap_eqpoll_pred";

(** Establishing the well-ordering **)

goalw CardinalArith.thy [inj_def]
 "!!K. Ord(K) ==>	\
\ (lam z:K*K. split(%x y. <x Un y, <x, y>>, z)) : inj(K*K, K*K*K)";
by (safe_tac ZF_cs);
by (fast_tac (ZF_cs addIs [lam_type, Un_least_lt RS ltD, ltI]
                    addSEs [split_type]) 1);
by (asm_full_simp_tac ZF_ss 1);
qed "csquare_lam_inj";

goalw CardinalArith.thy [csquare_rel_def]
 "!!K. Ord(K) ==> well_ord(K*K, csquare_rel(K))";
by (rtac (csquare_lam_inj RS well_ord_rvimage) 1);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel] 1));
qed "well_ord_csquare";

(** Characterising initial segments of the well-ordering **)

goalw CardinalArith.thy [csquare_rel_def]
 "!!K. [| x<K;  y<K;  z<K |] ==> \
\      <<x,y>, <z,z>> : csquare_rel(K) --> x le z & y le z";
by (REPEAT (etac ltE 1));
by (asm_simp_tac (ZF_ss addsimps [rvimage_iff, rmult_iff, Memrel_iff,
                                  Un_absorb, Un_least_mem_iff, ltD]) 1);
by (safe_tac (ZF_cs addSEs [mem_irrefl] 
                    addSIs [Un_upper1_le, Un_upper2_le]));
by (ALLGOALS (asm_simp_tac (ZF_ss addsimps [lt_def, succI2, Ord_succ])));
val csquareD_lemma = result();

bind_thm ("csquareD", csquareD_lemma RS mp);

goalw CardinalArith.thy [pred_def]
 "!!K. z<K ==> pred(K*K, <z,z>, csquare_rel(K)) <= succ(z)*succ(z)";
by (safe_tac (lemmas_cs addSEs [SigmaE]));	(*avoids using succCI*)
by (rtac (csquareD RS conjE) 1);
by (rewtac lt_def);
by (assume_tac 4);
by (ALLGOALS (fast_tac ZF_cs));
qed "pred_csquare_subset";

goalw CardinalArith.thy [csquare_rel_def]
 "!!K. [| x<z;  y<z;  z<K |] ==>  <<x,y>, <z,z>> : csquare_rel(K)";
by (subgoals_tac ["x<K", "y<K"] 1);
by (REPEAT (eresolve_tac [asm_rl, lt_trans] 2));
by (REPEAT (etac ltE 1));
by (asm_simp_tac (ZF_ss addsimps [rvimage_iff, rmult_iff, Memrel_iff,
                                  Un_absorb, Un_least_mem_iff, ltD]) 1);
qed "csquare_ltI";

(*Part of the traditional proof.  UNUSED since it's harder to prove & apply *)
goalw CardinalArith.thy [csquare_rel_def]
 "!!K. [| x le z;  y le z;  z<K |] ==> \
\      <<x,y>, <z,z>> : csquare_rel(K) | x=z & y=z";
by (subgoals_tac ["x<K", "y<K"] 1);
by (REPEAT (eresolve_tac [asm_rl, lt_trans1] 2));
by (REPEAT (etac ltE 1));
by (asm_simp_tac (ZF_ss addsimps [rvimage_iff, rmult_iff, Memrel_iff,
                                  Un_absorb, Un_least_mem_iff, ltD]) 1);
by (REPEAT_FIRST (etac succE));
by (ALLGOALS
    (asm_simp_tac (ZF_ss addsimps [subset_Un_iff RS iff_sym, 
				   subset_Un_iff2 RS iff_sym, OrdmemD])));
qed "csquare_or_eqI";

(** The cardinality of initial segments **)

goal CardinalArith.thy
    "!!K. [| InfCard(K);  x<K;  y<K;  z=succ(x Un y) |] ==> \
\         ordermap(K*K, csquare_rel(K)) ` <x,y> lepoll 		\
\         ordermap(K*K, csquare_rel(K)) ` <z,z>";
by (subgoals_tac ["z<K", "well_ord(K*K, csquare_rel(K))"] 1);
by (etac (InfCard_is_Card RS Card_is_Ord RS well_ord_csquare) 2);
by (fast_tac (ZF_cs addSIs [Un_least_lt, InfCard_is_Limit, Limit_has_succ]) 2);
by (rtac (OrdmemD RS subset_imp_lepoll) 1);
by (res_inst_tac [("z1","z")] (csquare_ltI RS ordermap_mono) 1);
by (etac well_ord_is_wf 4);
by (ALLGOALS 
    (fast_tac (ZF_cs addSIs [Un_upper1_le, Un_upper2_le, Ord_ordermap] 
                     addSEs [ltE])));
qed "ordermap_z_lepoll";

(*Kunen: "each <x,y>: K*K has no more than z*z predecessors..." (page 29) *)
goalw CardinalArith.thy [cmult_def]
  "!!K. [| InfCard(K);  x<K;  y<K;  z=succ(x Un y) |] ==> \
\       | ordermap(K*K, csquare_rel(K)) ` <x,y> | le  |succ(z)| |*| |succ(z)|";
by (rtac (well_ord_rmult RS well_ord_lepoll_imp_Card_le) 1);
by (REPEAT (ares_tac [Ord_cardinal, well_ord_Memrel] 1));
by (subgoals_tac ["z<K"] 1);
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
qed "ordermap_csquare_le";

(*Kunen: "... so the order type <= K" *)
goal CardinalArith.thy
    "!!K. [| InfCard(K);  ALL y:K. InfCard(y) --> y |*| y = y |]  ==>  \
\         ordertype(K*K, csquare_rel(K)) le K";
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
qed "ordertype_csquare_le";

(*This lemma can easily be generalized to premise well_ord(A*A,r) *)
goalw CardinalArith.thy [cmult_def]
    "!!K. Ord(K) ==> K |*| K  =  |ordertype(K*K, csquare_rel(K))|";
by (rtac cardinal_cong 1);
by (rewtac eqpoll_def);
by (rtac exI 1);
by (etac (well_ord_csquare RS ordermap_bij) 1);
qed "csquare_eq_ordertype";

(*Main result: Kunen's Theorem 10.12*)
goal CardinalArith.thy "!!K. InfCard(K) ==> K |*| K = K";
by (forward_tac [InfCard_is_Card RS Card_is_Ord] 1);
by (etac rev_mp 1);
by (trans_ind_tac "K" [] 1);
by (rtac impI 1);
by (rtac le_anti_sym 1);
by (etac (InfCard_is_Card RS cmult_square_le) 2);
by (rtac (ordertype_csquare_le RSN (2, le_trans)) 1);
by (assume_tac 2);
by (assume_tac 2);
by (asm_simp_tac 
    (ZF_ss addsimps [csquare_eq_ordertype, Ord_cardinal_le,
                     well_ord_csquare RS Ord_ordertype]) 1);
qed "InfCard_csquare_eq";

(*Corollary for arbitrary well-ordered sets (all sets, assuming AC)*)
goal CardinalArith.thy
    "!!A. [| well_ord(A,r);  InfCard(|A|) |] ==> A*A eqpoll A";
by (resolve_tac [prod_eqpoll_cong RS eqpoll_trans] 1);
by (REPEAT (etac (well_ord_cardinal_eqpoll RS eqpoll_sym) 1));
by (rtac well_ord_cardinal_eqE 1);
by (REPEAT (ares_tac [Ord_cardinal, well_ord_rmult, well_ord_Memrel] 1));
by (asm_simp_tac (ZF_ss addsimps [symmetric cmult_def, InfCard_csquare_eq]) 1);
qed "well_ord_InfCard_square_eq";

(** Toward's Kunen's Corollary 10.13 (1) **)

goal CardinalArith.thy "!!K. [| InfCard(K);  L le K;  0<L |] ==> K |*| L = K";
by (rtac le_anti_sym 1);
by (etac ltE 2 THEN
    REPEAT (ares_tac [cmult_le_self, InfCard_is_Card] 2));
by (forward_tac [InfCard_is_Card RS Card_is_Ord RS le_refl] 1);
by (resolve_tac [cmult_le_mono RS le_trans] 1 THEN REPEAT (assume_tac 1));
by (asm_simp_tac (ZF_ss addsimps [InfCard_csquare_eq]) 1);
qed "InfCard_le_cmult_eq";

(*Corollary 10.13 (1), for cardinal multiplication*)
goal CardinalArith.thy
    "!!K. [| InfCard(K);  InfCard(L) |] ==> K |*| L = K Un L";
by (res_inst_tac [("i","K"),("j","L")] Ord_linear_le 1);
by (typechk_tac [InfCard_is_Card, Card_is_Ord]);
by (resolve_tac [cmult_commute RS ssubst] 1);
by (resolve_tac [Un_commute RS ssubst] 1);
by (ALLGOALS
    (asm_simp_tac 
     (ZF_ss addsimps [InfCard_is_Limit RS Limit_has_0, InfCard_le_cmult_eq,
		      subset_Un_iff2 RS iffD1, le_imp_subset])));
qed "InfCard_cmult_eq";

(*This proof appear to be the simplest!*)
goal CardinalArith.thy "!!K. InfCard(K) ==> K |+| K = K";
by (asm_simp_tac
    (ZF_ss addsimps [cmult_2 RS sym, InfCard_is_Card, cmult_commute]) 1);
by (rtac InfCard_le_cmult_eq 1);
by (typechk_tac [Ord_0, le_refl, leI]);
by (typechk_tac [InfCard_is_Limit, Limit_has_0, Limit_has_succ]);
qed "InfCard_cdouble_eq";

(*Corollary 10.13 (1), for cardinal addition*)
goal CardinalArith.thy "!!K. [| InfCard(K);  L le K |] ==> K |+| L = K";
by (rtac le_anti_sym 1);
by (etac ltE 2 THEN
    REPEAT (ares_tac [cadd_le_self, InfCard_is_Card] 2));
by (forward_tac [InfCard_is_Card RS Card_is_Ord RS le_refl] 1);
by (resolve_tac [cadd_le_mono RS le_trans] 1 THEN REPEAT (assume_tac 1));
by (asm_simp_tac (ZF_ss addsimps [InfCard_cdouble_eq]) 1);
qed "InfCard_le_cadd_eq";

goal CardinalArith.thy
    "!!K. [| InfCard(K);  InfCard(L) |] ==> K |+| L = K Un L";
by (res_inst_tac [("i","K"),("j","L")] Ord_linear_le 1);
by (typechk_tac [InfCard_is_Card, Card_is_Ord]);
by (resolve_tac [cadd_commute RS ssubst] 1);
by (resolve_tac [Un_commute RS ssubst] 1);
by (ALLGOALS
    (asm_simp_tac 
     (ZF_ss addsimps [InfCard_le_cadd_eq,
		      subset_Un_iff2 RS iffD1, le_imp_subset])));
qed "InfCard_cadd_eq";

(*The other part, Corollary 10.13 (2), refers to the cardinality of the set
  of all n-tuples of elements of K.  A better version for the Isabelle theory
  might be  InfCard(K) ==> |list(K)| = K.
*)

(*** For every cardinal number there exists a greater one
     [Kunen's Theorem 10.16, which would be trivial using AC] ***)

goalw CardinalArith.thy [jump_cardinal_def] "Ord(jump_cardinal(K))";
by (rtac (Ord_is_Transset RSN (2,OrdI)) 1);
by (safe_tac (ZF_cs addSIs [Ord_ordertype]));
by (rewtac Transset_def);
by (safe_tac ZF_cs);
by (rtac (ordertype_subset RS exE) 1 THEN REPEAT (assume_tac 1));
by (rtac UN_I 1);
by (rtac ReplaceI 2);
by (ALLGOALS (fast_tac (ZF_cs addSEs [well_ord_subset])));
qed "Ord_jump_cardinal";

(*Allows selective unfolding.  Less work than deriving intro/elim rules*)
goalw CardinalArith.thy [jump_cardinal_def]
     "i : jump_cardinal(K) <->   \
\         (EX r X. r <= K*K & X <= K & well_ord(X,r) & i = ordertype(X,r))";
by (fast_tac subset_cs 1);	(*It's vital to avoid reasoning about <=*)
qed "jump_cardinal_iff";

(*The easy part of Theorem 10.16: jump_cardinal(K) exceeds K*)
goal CardinalArith.thy "!!K. Ord(K) ==> K < jump_cardinal(K)";
by (resolve_tac [Ord_jump_cardinal RSN (2,ltI)] 1);
by (resolve_tac [jump_cardinal_iff RS iffD2] 1);
by (REPEAT_FIRST (ares_tac [exI, conjI, well_ord_Memrel]));
by (rtac subset_refl 2);
by (asm_simp_tac (ZF_ss addsimps [Memrel_def, subset_iff]) 1);
by (asm_simp_tac (ZF_ss addsimps [ordertype_Memrel]) 1);
qed "K_lt_jump_cardinal";

(*The proof by contradiction: the bijection f yields a wellordering of X
  whose ordertype is jump_cardinal(K).  *)
goal CardinalArith.thy
    "!!K. [| well_ord(X,r);  r <= K * K;  X <= K;	\
\            f : bij(ordertype(X,r), jump_cardinal(K)) 	\
\	  |] ==> jump_cardinal(K) : jump_cardinal(K)";
by (subgoal_tac "f O ordermap(X,r): bij(X, jump_cardinal(K))" 1);
by (REPEAT (ares_tac [comp_bij, ordermap_bij] 2));
by (resolve_tac [jump_cardinal_iff RS iffD2] 1);
by (REPEAT_FIRST (resolve_tac [exI, conjI]));
by (rtac ([rvimage_type, Sigma_mono] MRS subset_trans) 1);
by (REPEAT (assume_tac 1));
by (etac (bij_is_inj RS well_ord_rvimage) 1);
by (rtac (Ord_jump_cardinal RS well_ord_Memrel) 1);
by (asm_simp_tac
    (ZF_ss addsimps [well_ord_Memrel RSN (2, bij_ordertype_vimage), 
		     ordertype_Memrel, Ord_jump_cardinal]) 1);
qed "Card_jump_cardinal_lemma";

(*The hard part of Theorem 10.16: jump_cardinal(K) is itself a cardinal*)
goal CardinalArith.thy "Card(jump_cardinal(K))";
by (rtac (Ord_jump_cardinal RS CardI) 1);
by (rewtac eqpoll_def);
by (safe_tac (ZF_cs addSDs [ltD, jump_cardinal_iff RS iffD1]));
by (REPEAT (ares_tac [Card_jump_cardinal_lemma RS mem_irrefl] 1));
qed "Card_jump_cardinal";

(*** Basic properties of successor cardinals ***)

goalw CardinalArith.thy [csucc_def]
    "!!K. Ord(K) ==> Card(csucc(K)) & K < csucc(K)";
by (rtac LeastI 1);
by (REPEAT (ares_tac [conjI, Card_jump_cardinal, K_lt_jump_cardinal,
		      Ord_jump_cardinal] 1));
qed "csucc_basic";

bind_thm ("Card_csucc", csucc_basic RS conjunct1);

bind_thm ("lt_csucc", csucc_basic RS conjunct2);

goal CardinalArith.thy "!!K. Ord(K) ==> 0 < csucc(K)";
by (resolve_tac [[Ord_0_le, lt_csucc] MRS lt_trans1] 1);
by (REPEAT (assume_tac 1));
qed "Ord_0_lt_csucc";

goalw CardinalArith.thy [csucc_def]
    "!!K L. [| Card(L);  K<L |] ==> csucc(K) le L";
by (rtac Least_le 1);
by (REPEAT (ares_tac [conjI, Card_is_Ord] 1));
qed "csucc_le";

goal CardinalArith.thy
    "!!K. [| Ord(i); Card(K) |] ==> i < csucc(K) <-> |i| le K";
by (rtac iffI 1);
by (rtac Card_lt_imp_lt 2);
by (etac lt_trans1 2);
by (REPEAT (ares_tac [lt_csucc, Card_csucc, Card_is_Ord] 2));
by (resolve_tac [notI RS not_lt_imp_le] 1);
by (resolve_tac [Card_cardinal RS csucc_le RS lt_trans1 RS lt_irrefl] 1);
by (assume_tac 1);
by (resolve_tac [Ord_cardinal_le RS lt_trans1] 1);
by (REPEAT (ares_tac [Ord_cardinal] 1
     ORELSE eresolve_tac [ltE, Card_is_Ord] 1));
qed "lt_csucc_iff";

goal CardinalArith.thy
    "!!K' K. [| Card(K'); Card(K) |] ==> K' < csucc(K) <-> K' le K";
by (asm_simp_tac 
    (ZF_ss addsimps [lt_csucc_iff, Card_cardinal_eq, Card_is_Ord]) 1);
qed "Card_lt_csucc_iff";

goalw CardinalArith.thy [InfCard_def]
    "!!K. InfCard(K) ==> InfCard(csucc(K))";
by (asm_simp_tac (ZF_ss addsimps [Card_csucc, Card_is_Ord, 
				  lt_csucc RS leI RSN (2,le_trans)]) 1);
qed "InfCard_csucc";

