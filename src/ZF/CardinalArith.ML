(*  Title:      ZF/CardinalArith.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge

Cardinal arithmetic -- WITHOUT the Axiom of Choice

Note: Could omit proving the algebraic laws for cardinal addition and
multiplication.  On finite cardinals these operations coincide with
addition and multiplication of natural numbers; on infinite cardinals they
coincide with union (maximum).  Either way we get most laws for free.
*)

(*** Cardinal addition ***)

(** Cardinal addition is commutative **)

Goalw [eqpoll_def] "A+B eqpoll B+A";
by (rtac exI 1);
by (res_inst_tac [("c", "case(Inr, Inl)"), ("d", "case(Inr, Inl)")] 
    lam_bijective 1);
by Auto_tac;
qed "sum_commute_eqpoll";

Goalw [cadd_def] "i |+| j = j |+| i";
by (rtac (sum_commute_eqpoll RS cardinal_cong) 1);
qed "cadd_commute";

(** Cardinal addition is associative **)

Goalw [eqpoll_def] "(A+B)+C eqpoll A+(B+C)";
by (rtac exI 1);
by (rtac sum_assoc_bij 1);
qed "sum_assoc_eqpoll";

(*Unconditional version requires AC*)
Goalw [cadd_def]
    "[| well_ord(i,ri); well_ord(j,rj); well_ord(k,rk) |] ==>  \
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

Goalw [eqpoll_def] "0+A eqpoll A";
by (rtac exI 1);
by (rtac bij_0_sum 1);
qed "sum_0_eqpoll";

Goalw [cadd_def] "Card(K) ==> 0 |+| K = K";
by (asm_simp_tac (simpset() addsimps [sum_0_eqpoll RS cardinal_cong, 
				      Card_cardinal_eq]) 1);
qed "cadd_0";
Addsimps [cadd_0];

(** Addition by another cardinal **)

Goalw [lepoll_def, inj_def] "A lepoll A+B";
by (res_inst_tac [("x", "lam x:A. Inl(x)")] exI 1);
by (Asm_simp_tac 1);
qed "sum_lepoll_self";

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)
Goalw [cadd_def]
    "[| Card(K);  Ord(L) |] ==> K le (K |+| L)";
by (rtac ([Card_cardinal_le, well_ord_lepoll_imp_Card_le] MRS le_trans) 1);
by (rtac sum_lepoll_self 3);
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel, Card_is_Ord] 1));
qed "cadd_le_self";

(** Monotonicity of addition **)

Goalw [lepoll_def]
     "[| A lepoll C;  B lepoll D |] ==> A + B  lepoll  C + D";
by (REPEAT (etac exE 1));
by (res_inst_tac [("x", "lam z:A+B. case(%w. Inl(f`w), %y. Inr(fa`y), z)")] 
    exI 1);
by (res_inst_tac 
      [("d", "case(%w. Inl(converse(f)`w), %y. Inr(converse(fa)`y))")] 
      lam_injective 1);
by (typecheck_tac (tcset() addTCs [inj_is_fun]));
by Auto_tac;
qed "sum_lepoll_mono";

Goalw [cadd_def]
    "[| K' le K;  L' le L |] ==> (K' |+| L') le (K |+| L)";
by (safe_tac (claset() addSDs [le_subset_iff RS iffD1]));
by (rtac well_ord_lepoll_imp_Card_le 1);
by (REPEAT (ares_tac [sum_lepoll_mono, subset_imp_lepoll] 2));
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel] 1));
qed "cadd_le_mono";

(** Addition of finite cardinals is "ordinary" addition **)

Goalw [eqpoll_def] "succ(A)+B eqpoll succ(A+B)";
by (rtac exI 1);
by (res_inst_tac [("c", "%z. if z=Inl(A) then A+B else z"), 
                  ("d", "%z. if z=A+B then Inl(A) else z")] 
    lam_bijective 1);
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [succI2, mem_imp_not_eq]
                             setloop eresolve_tac [sumE,succE])));
qed "sum_succ_eqpoll";

(*Pulling the  succ(...)  outside the |...| requires m, n: nat  *)
(*Unconditional version requires AC*)
Goalw [cadd_def]
    "[| Ord(m);  Ord(n) |] ==> succ(m) |+| n = |succ(m |+| n)|";
by (rtac (sum_succ_eqpoll RS cardinal_cong RS trans) 1);
by (rtac (succ_eqpoll_cong RS cardinal_cong) 1);
by (rtac (well_ord_cardinal_eqpoll RS eqpoll_sym) 1);
by (REPEAT (ares_tac [well_ord_radd, well_ord_Memrel] 1));
qed "cadd_succ_lemma";

Goal "[| m: nat;  n: nat |] ==> m |+| n = m#+n";
by (induct_tac "m" 1);
by (asm_simp_tac (simpset() addsimps [nat_into_Card RS cadd_0]) 1);
by (asm_simp_tac (simpset() addsimps [nat_into_Ord, cadd_succ_lemma,
				      nat_into_Card RS Card_cardinal_eq]) 1);
qed "nat_cadd_eq_add";


(*** Cardinal multiplication ***)

(** Cardinal multiplication is commutative **)

(*Easier to prove the two directions separately*)
Goalw [eqpoll_def] "A*B eqpoll B*A";
by (rtac exI 1);
by (res_inst_tac [("c", "%<x,y>.<y,x>"), ("d", "%<x,y>.<y,x>")] 
    lam_bijective 1);
by Safe_tac;
by (ALLGOALS (Asm_simp_tac));
qed "prod_commute_eqpoll";

Goalw [cmult_def] "i |*| j = j |*| i";
by (rtac (prod_commute_eqpoll RS cardinal_cong) 1);
qed "cmult_commute";

(** Cardinal multiplication is associative **)

Goalw [eqpoll_def] "(A*B)*C eqpoll A*(B*C)";
by (rtac exI 1);
by (rtac prod_assoc_bij 1);
qed "prod_assoc_eqpoll";

(*Unconditional version requires AC*)
Goalw [cmult_def]
    "[| well_ord(i,ri); well_ord(j,rj); well_ord(k,rk) |] ==>  \
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

Goalw [eqpoll_def] "(A+B)*C eqpoll (A*C)+(B*C)";
by (rtac exI 1);
by (rtac sum_prod_distrib_bij 1);
qed "sum_prod_distrib_eqpoll";

Goalw [cadd_def, cmult_def]
    "[| well_ord(i,ri); well_ord(j,rj); well_ord(k,rk) |] ==>  \
\             (i |+| j) |*| k = (i |*| k) |+| (j |*| k)";
by (rtac cardinal_cong 1);
by (rtac ([well_ord_cardinal_eqpoll, eqpoll_refl] MRS prod_eqpoll_cong RS
          eqpoll_trans) 1);
by (rtac (sum_prod_distrib_eqpoll RS eqpoll_trans) 2);
by (rtac ([well_ord_cardinal_eqpoll, well_ord_cardinal_eqpoll] MRS 
	  sum_eqpoll_cong RS eqpoll_sym) 2);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_radd] 1));
qed "well_ord_cadd_cmult_distrib";

(** Multiplication by 0 yields 0 **)

Goalw [eqpoll_def] "0*A eqpoll 0";
by (rtac exI 1);
by (rtac lam_bijective 1);
by Safe_tac;
qed "prod_0_eqpoll";

Goalw [cmult_def] "0 |*| i = 0";
by (asm_simp_tac (simpset() addsimps [prod_0_eqpoll RS cardinal_cong, 
				      Card_0 RS Card_cardinal_eq]) 1);
qed "cmult_0";
Addsimps [cmult_0];

(** 1 is the identity for multiplication **)

Goalw [eqpoll_def] "{x}*A eqpoll A";
by (rtac exI 1);
by (resolve_tac [singleton_prod_bij RS bij_converse_bij] 1);
qed "prod_singleton_eqpoll";

Goalw [cmult_def, succ_def] "Card(K) ==> 1 |*| K = K";
by (asm_simp_tac (simpset() addsimps [prod_singleton_eqpoll RS cardinal_cong, 
				      Card_cardinal_eq]) 1);
qed "cmult_1";
Addsimps [cmult_1];

(*** Some inequalities for multiplication ***)

Goalw [lepoll_def, inj_def] "A lepoll A*A";
by (res_inst_tac [("x", "lam x:A. <x,x>")] exI 1);
by (Simp_tac 1);
qed "prod_square_lepoll";

(*Could probably weaken the premise to well_ord(K,r), or remove using AC*)
Goalw [cmult_def] "Card(K) ==> K le K |*| K";
by (rtac le_trans 1);
by (rtac well_ord_lepoll_imp_Card_le 2);
by (rtac prod_square_lepoll 3);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel, Card_is_Ord] 2));
by (asm_simp_tac (simpset() 
		  addsimps [le_refl, Card_is_Ord, Card_cardinal_eq]) 1);
qed "cmult_square_le";

(** Multiplication by a non-zero cardinal **)

Goalw [lepoll_def, inj_def] "b: B ==> A lepoll A*B";
by (res_inst_tac [("x", "lam x:A. <x,b>")] exI 1);
by (Asm_simp_tac 1);
qed "prod_lepoll_self";

(*Could probably weaken the premises to well_ord(K,r), or removing using AC*)
Goalw [cmult_def]
    "[| Card(K);  Ord(L);  0<L |] ==> K le (K |*| L)";
by (rtac ([Card_cardinal_le, well_ord_lepoll_imp_Card_le] MRS le_trans) 1);
by (rtac prod_lepoll_self 3);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel, Card_is_Ord, ltD] 1));
qed "cmult_le_self";

(** Monotonicity of multiplication **)

Goalw [lepoll_def]
     "[| A lepoll C;  B lepoll D |] ==> A * B  lepoll  C * D";
by (REPEAT (etac exE 1));
by (res_inst_tac [("x", "lam <w,y>:A*B. <f`w, fa`y>")] exI 1);
by (res_inst_tac [("d", "%<w,y>.<converse(f)`w, converse(fa)`y>")] 
                  lam_injective 1);
by (typecheck_tac (tcset() addTCs [inj_is_fun]));
by Auto_tac;
qed "prod_lepoll_mono";

Goalw [cmult_def]
    "[| K' le K;  L' le L |] ==> (K' |*| L') le (K |*| L)";
by (safe_tac (claset() addSDs [le_subset_iff RS iffD1]));
by (rtac well_ord_lepoll_imp_Card_le 1);
by (REPEAT (ares_tac [prod_lepoll_mono, subset_imp_lepoll] 2));
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel] 1));
qed "cmult_le_mono";

(*** Multiplication of finite cardinals is "ordinary" multiplication ***)

Goalw [eqpoll_def] "succ(A)*B eqpoll B + A*B";
by (rtac exI 1);
by (res_inst_tac [("c", "%<x,y>. if x=A then Inl(y) else Inr(<x,y>)"), 
                  ("d", "case(%y. <A,y>, %z. z)")] 
    lam_bijective 1);
by Safe_tac;
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [succI2, if_type, mem_imp_not_eq])));
qed "prod_succ_eqpoll";

(*Unconditional version requires AC*)
Goalw [cmult_def, cadd_def]
    "[| Ord(m);  Ord(n) |] ==> succ(m) |*| n = n |+| (m |*| n)";
by (rtac (prod_succ_eqpoll RS cardinal_cong RS trans) 1);
by (rtac (cardinal_cong RS sym) 1);
by (rtac ([eqpoll_refl, well_ord_cardinal_eqpoll] MRS sum_eqpoll_cong) 1);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel] 1));
qed "cmult_succ_lemma";

Goal "[| m: nat;  n: nat |] ==> m |*| n = m#*n";
by (induct_tac "m" 1);
by (Asm_simp_tac 1);
by (asm_simp_tac (simpset() addsimps [nat_into_Ord, cmult_succ_lemma,
				      nat_cadd_eq_add]) 1);
qed "nat_cmult_eq_mult";

Goal "Card(n) ==> 2 |*| n = n |+| n";
by (asm_simp_tac 
    (simpset() addsimps [cmult_succ_lemma, Card_is_Ord,
			 read_instantiate [("j","0")] cadd_commute]) 1);
qed "cmult_2";


val sum_lepoll_prod = [sum_eq_2_times RS equalityD1 RS subset_imp_lepoll,
        asm_rl, lepoll_refl] MRS (prod_lepoll_mono RSN (2, lepoll_trans))
        |> standard;

Goal "[| A lepoll B; 2 lepoll A |] ==> A+B lepoll A*B";
by (REPEAT (ares_tac [[sum_lepoll_mono, sum_lepoll_prod]
                MRS lepoll_trans, lepoll_refl] 1));
qed "lepoll_imp_sum_lepoll_prod";


(*** Infinite Cardinals are Limit Ordinals ***)

(*This proof is modelled upon one assuming nat<=A, with injection
  lam z:cons(u,A). if z=u then 0 else if z : nat then succ(z) else z 
  and inverse %y. if y:nat then nat_case(u, %z. z, y) else y.  \
  If f: inj(nat,A) then range(f) behaves like the natural numbers.*)
Goalw [lepoll_def] "nat lepoll A ==> cons(u,A) lepoll A";
by (etac exE 1);
by (res_inst_tac [("x",
    "lam z:cons(u,A). if z=u then f`0      \
\                     else if z: range(f) then f`succ(converse(f)`z)  \
\                     else z")] exI 1);
by (res_inst_tac [("d", "%y. if y: range(f)     \
\                            then nat_case(u, %z. f`z, converse(f)`y) \
\                            else y")] 
    lam_injective 1);
by (fast_tac (claset() addSIs [if_type, apply_type]
                       addIs  [inj_is_fun, inj_converse_fun]) 1);
by (asm_simp_tac 
    (simpset() addsimps [inj_is_fun RS apply_rangeI,
			 inj_converse_fun RS apply_rangeI,
			 inj_converse_fun RS apply_funtype]) 1);
qed "nat_cons_lepoll";

Goal "nat lepoll A ==> cons(u,A) eqpoll A";
by (etac (nat_cons_lepoll RS eqpollI) 1);
by (rtac (subset_consI RS subset_imp_lepoll) 1);
qed "nat_cons_eqpoll";

(*Specialized version required below*)
Goalw [succ_def] "nat <= A ==> succ(A) eqpoll A";
by (eresolve_tac [subset_imp_lepoll RS nat_cons_eqpoll] 1);
qed "nat_succ_eqpoll";

Goalw [InfCard_def] "InfCard(nat)";
by (blast_tac (claset() addIs [Card_nat, le_refl, Card_is_Ord]) 1);
qed "InfCard_nat";

Goalw [InfCard_def] "InfCard(K) ==> Card(K)";
by (etac conjunct1 1);
qed "InfCard_is_Card";

Goalw [InfCard_def]
    "[| InfCard(K);  Card(L) |] ==> InfCard(K Un L)";
by (asm_simp_tac (simpset() addsimps [Card_Un, Un_upper1_le RSN (2,le_trans), 
				      Card_is_Ord]) 1);
qed "InfCard_Un";

(*Kunen's Lemma 10.11*)
Goalw [InfCard_def] "InfCard(K) ==> Limit(K)";
by (etac conjE 1);
by (forward_tac [Card_is_Ord] 1);
by (rtac (ltI RS non_succ_LimitI) 1);
by (etac ([asm_rl, nat_0I] MRS (le_imp_subset RS subsetD)) 1);
by (safe_tac (claset() addSDs [Limit_nat RS Limit_le_succD]));
by (rewtac Card_def);
by (dtac trans 1);
by (etac (le_imp_subset RS nat_succ_eqpoll RS cardinal_cong) 1);
by (etac (Ord_cardinal_le RS lt_trans2 RS lt_irrefl) 1);
by (REPEAT (ares_tac [le_eqI, Ord_cardinal] 1));
qed "InfCard_is_Limit";


(*** An infinite cardinal equals its square (Kunen, Thm 10.12, page 29) ***)

(*A general fact about ordermap*)
Goalw [eqpoll_def]
    "[| well_ord(A,r);  x:A |] ==> ordermap(A,r)`x eqpoll pred(A,x,r)";
by (rtac exI 1);
by (asm_simp_tac (simpset() addsimps [ordermap_eq_image, well_ord_is_wf]) 1);
by (etac (ordermap_bij RS bij_is_inj RS restrict_bij RS bij_converse_bij) 1);
by (rtac pred_subset 1);
qed "ordermap_eqpoll_pred";

(** Establishing the well-ordering **)

Goalw [inj_def] "Ord(K) ==> (lam <x,y>:K*K. <x Un y, x, y>) : inj(K*K, K*K*K)";
by (force_tac (claset() addIs [lam_type, Un_least_lt RS ltD, ltI],
	       simpset()) 1);
qed "csquare_lam_inj";

Goalw [csquare_rel_def] "Ord(K) ==> well_ord(K*K, csquare_rel(K))";
by (rtac (csquare_lam_inj RS well_ord_rvimage) 1);
by (REPEAT (ares_tac [well_ord_rmult, well_ord_Memrel] 1));
qed "well_ord_csquare";

(** Characterising initial segments of the well-ordering **)

Goalw [csquare_rel_def]
 "[| <<x,y>, <z,z>> : csquare_rel(K);  x<K;  y<K;  z<K |] ==> x le z & y le z";
by (etac rev_mp 1);
by (REPEAT (etac ltE 1));
by (asm_simp_tac (simpset() addsimps [rvimage_iff, rmult_iff, Memrel_iff,
				      Un_absorb, Un_least_mem_iff, ltD]) 1);
by (safe_tac (claset() addSEs [mem_irrefl] 
                       addSIs [Un_upper1_le, Un_upper2_le]));
by (ALLGOALS (asm_simp_tac (simpset() addsimps [lt_def, succI2, Ord_succ])));
qed "csquareD";

Goalw [pred_def]
 "z<K ==> pred(K*K, <z,z>, csquare_rel(K)) <= succ(z)*succ(z)";
by (safe_tac (claset() delrules [SigmaI,succCI]));  (*avoids using succCI,...*)
by (etac (csquareD RS conjE) 1);
by (rewtac lt_def);
by (ALLGOALS Blast_tac);
qed "pred_csquare_subset";

Goalw [csquare_rel_def]
 "[| x<z;  y<z;  z<K |] ==>  <<x,y>, <z,z>> : csquare_rel(K)";
by (subgoals_tac ["x<K", "y<K"] 1);
by (REPEAT (eresolve_tac [asm_rl, lt_trans] 2));
by (REPEAT (etac ltE 1));
by (asm_simp_tac (simpset() addsimps [rvimage_iff, rmult_iff, Memrel_iff,
				      Un_absorb, Un_least_mem_iff, ltD]) 1);
qed "csquare_ltI";

(*Part of the traditional proof.  UNUSED since it's harder to prove & apply *)
Goalw [csquare_rel_def]
 "[| x le z;  y le z;  z<K |] ==> \
\      <<x,y>, <z,z>> : csquare_rel(K) | x=z & y=z";
by (subgoals_tac ["x<K", "y<K"] 1);
by (REPEAT (eresolve_tac [asm_rl, lt_trans1] 2));
by (REPEAT (etac ltE 1));
by (asm_simp_tac (simpset() addsimps [rvimage_iff, rmult_iff, Memrel_iff,
				      Un_absorb, Un_least_mem_iff, ltD]) 1);
by (REPEAT_FIRST (etac succE));
by (ALLGOALS
    (asm_simp_tac (simpset() addsimps [subset_Un_iff RS iff_sym, 
				       subset_Un_iff2 RS iff_sym, OrdmemD])));
qed "csquare_or_eqI";

(** The cardinality of initial segments **)

Goal "[| Limit(K);  x<K;  y<K;  z=succ(x Un y) |] ==> \
\         ordermap(K*K, csquare_rel(K)) ` <x,y> <               \
\         ordermap(K*K, csquare_rel(K)) ` <z,z>";
by (subgoals_tac ["z<K", "well_ord(K*K, csquare_rel(K))"] 1);
by (etac (Limit_is_Ord RS well_ord_csquare) 2);
by (blast_tac (claset() addSIs [Un_least_lt, Limit_has_succ]) 2);
by (rtac (csquare_ltI RS ordermap_mono RS ltI) 1);
by (etac well_ord_is_wf 4);
by (ALLGOALS 
    (blast_tac (claset() addSIs [Un_upper1_le, Un_upper2_le, Ord_ordermap] 
                         addSEs [ltE])));
qed "ordermap_z_lt";

(*Kunen: "each <x,y>: K*K has no more than z*z predecessors..." (page 29) *)
Goalw [cmult_def]
  "[| Limit(K);  x<K;  y<K;  z=succ(x Un y) |] ==> \
\       | ordermap(K*K, csquare_rel(K)) ` <x,y> | le  |succ(z)| |*| |succ(z)|";
by (rtac (well_ord_rmult RS well_ord_lepoll_imp_Card_le) 1);
by (REPEAT (ares_tac [Ord_cardinal, well_ord_Memrel] 1));
by (subgoals_tac ["z<K"] 1);
by (blast_tac (claset() addSIs [Un_least_lt, Limit_has_succ]) 2);
by (rtac (ordermap_z_lt RS leI RS le_imp_lepoll RS lepoll_trans) 1);
by (REPEAT_SOME assume_tac);
by (rtac (ordermap_eqpoll_pred RS eqpoll_imp_lepoll RS lepoll_trans) 1);
by (etac (Limit_is_Ord RS well_ord_csquare) 1);
by (blast_tac (claset() addIs [ltD]) 1);
by (rtac (pred_csquare_subset RS subset_imp_lepoll RS lepoll_trans) 1 THEN
    assume_tac 1);
by (REPEAT_FIRST (etac ltE));
by (rtac (prod_eqpoll_cong RS eqpoll_sym RS eqpoll_imp_lepoll) 1);
by (REPEAT_FIRST (etac (Ord_succ RS Ord_cardinal_eqpoll)));
qed "ordermap_csquare_le";

(*Kunen: "... so the order type <= K" *)
Goal "[| InfCard(K);  ALL y:K. InfCard(y) --> y |*| y = y |]  ==>  \
\         ordertype(K*K, csquare_rel(K)) le K";
by (forward_tac [InfCard_is_Card RS Card_is_Ord] 1);
by (rtac all_lt_imp_le 1);
by (assume_tac 1);
by (etac (well_ord_csquare RS Ord_ordertype) 1);
by (rtac Card_lt_imp_lt 1);
by (etac InfCard_is_Card 3);
by (etac ltE 2 THEN assume_tac 2);
by (asm_full_simp_tac (simpset() addsimps [ordertype_unfold]) 1);
by (safe_tac (claset() addSEs [ltE]));
by (subgoals_tac ["Ord(xb)", "Ord(y)"] 1);
by (REPEAT (eresolve_tac [asm_rl, Ord_in_Ord] 2));
by (rtac (InfCard_is_Limit RS ordermap_csquare_le RS lt_trans1) 1  THEN
    REPEAT (ares_tac [refl] 1 ORELSE etac ltI 1));
by (res_inst_tac [("i","xb Un y"), ("j","nat")] Ord_linear2 1  THEN
    REPEAT (ares_tac [Ord_Un, Ord_nat] 1));
(*the finite case: xb Un y < nat *)
by (res_inst_tac [("j", "nat")] lt_trans2 1);
by (asm_full_simp_tac (simpset() addsimps [InfCard_def]) 2);
by (asm_full_simp_tac
    (simpset() addsimps [lt_def, nat_cmult_eq_mult, nat_succI, mult_type,
			 nat_into_Card RS Card_cardinal_eq, Ord_nat]) 1);
(*case nat le (xb Un y) *)
by (asm_full_simp_tac
    (simpset() addsimps [le_imp_subset RS nat_succ_eqpoll RS cardinal_cong,
			 le_succ_iff, InfCard_def, Card_cardinal, Un_least_lt, 
			 Ord_Un, ltI, nat_le_cardinal,
			 Ord_cardinal_le RS lt_trans1 RS ltD]) 1);
qed "ordertype_csquare_le";

(*Main result: Kunen's Theorem 10.12*)
Goal "InfCard(K) ==> K |*| K = K";
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
    (simpset() addsimps [cmult_def, Ord_cardinal_le,
			 well_ord_csquare RS ordermap_bij RS 
			 bij_imp_eqpoll RS cardinal_cong,
			 well_ord_csquare RS Ord_ordertype]) 1);
qed "InfCard_csquare_eq";

(*Corollary for arbitrary well-ordered sets (all sets, assuming AC)*)
Goal "[| well_ord(A,r);  InfCard(|A|) |] ==> A*A eqpoll A";
by (resolve_tac [prod_eqpoll_cong RS eqpoll_trans] 1);
by (REPEAT (etac (well_ord_cardinal_eqpoll RS eqpoll_sym) 1));
by (rtac well_ord_cardinal_eqE 1);
by (REPEAT (ares_tac [Ord_cardinal, well_ord_rmult, well_ord_Memrel] 1));
by (asm_simp_tac (simpset() 
		  addsimps [symmetric cmult_def, InfCard_csquare_eq]) 1);
qed "well_ord_InfCard_square_eq";

(** Toward's Kunen's Corollary 10.13 (1) **)

Goal "[| InfCard(K);  L le K;  0<L |] ==> K |*| L = K";
by (rtac le_anti_sym 1);
by (etac ltE 2 THEN
    REPEAT (ares_tac [cmult_le_self, InfCard_is_Card] 2));
by (forward_tac [InfCard_is_Card RS Card_is_Ord RS le_refl] 1);
by (resolve_tac [cmult_le_mono RS le_trans] 1 THEN REPEAT (assume_tac 1));
by (asm_simp_tac (simpset() addsimps [InfCard_csquare_eq]) 1);
qed "InfCard_le_cmult_eq";

(*Corollary 10.13 (1), for cardinal multiplication*)
Goal "[| InfCard(K);  InfCard(L) |] ==> K |*| L = K Un L";
by (res_inst_tac [("i","K"),("j","L")] Ord_linear_le 1);
by (typecheck_tac (tcset() addTCs [InfCard_is_Card, Card_is_Ord]));
by (resolve_tac [cmult_commute RS ssubst] 1);
by (resolve_tac [Un_commute RS ssubst] 1);
by (ALLGOALS
    (asm_simp_tac 
     (simpset() addsimps [InfCard_is_Limit RS Limit_has_0, InfCard_le_cmult_eq,
			  subset_Un_iff2 RS iffD1, le_imp_subset])));
qed "InfCard_cmult_eq";

Goal "InfCard(K) ==> K |+| K = K";
by (asm_simp_tac
    (simpset() addsimps [cmult_2 RS sym, InfCard_is_Card, cmult_commute]) 1);
by (asm_simp_tac 
    (simpset() addsimps [InfCard_le_cmult_eq, InfCard_is_Limit, 
			 Limit_has_0, Limit_has_succ]) 1);
qed "InfCard_cdouble_eq";

(*Corollary 10.13 (1), for cardinal addition*)
Goal "[| InfCard(K);  L le K |] ==> K |+| L = K";
by (rtac le_anti_sym 1);
by (etac ltE 2 THEN
    REPEAT (ares_tac [cadd_le_self, InfCard_is_Card] 2));
by (forward_tac [InfCard_is_Card RS Card_is_Ord RS le_refl] 1);
by (resolve_tac [cadd_le_mono RS le_trans] 1 THEN REPEAT (assume_tac 1));
by (asm_simp_tac (simpset() addsimps [InfCard_cdouble_eq]) 1);
qed "InfCard_le_cadd_eq";

Goal "[| InfCard(K);  InfCard(L) |] ==> K |+| L = K Un L";
by (res_inst_tac [("i","K"),("j","L")] Ord_linear_le 1);
by (typecheck_tac (tcset() addTCs [InfCard_is_Card, Card_is_Ord]));
by (resolve_tac [cadd_commute RS ssubst] 1);
by (resolve_tac [Un_commute RS ssubst] 1);
by (ALLGOALS
    (asm_simp_tac 
     (simpset() addsimps [InfCard_le_cadd_eq,
			  subset_Un_iff2 RS iffD1, le_imp_subset])));
qed "InfCard_cadd_eq";

(*The other part, Corollary 10.13 (2), refers to the cardinality of the set
  of all n-tuples of elements of K.  A better version for the Isabelle theory
  might be  InfCard(K) ==> |list(K)| = K.
*)

(*** For every cardinal number there exists a greater one
     [Kunen's Theorem 10.16, which would be trivial using AC] ***)

Goalw [jump_cardinal_def] "Ord(jump_cardinal(K))";
by (rtac (Ord_is_Transset RSN (2,OrdI)) 1);
by (blast_tac (claset() addSIs [Ord_ordertype]) 2);
by (rewtac Transset_def);
by (safe_tac subset_cs);
by (asm_full_simp_tac (simpset() addsimps [ordertype_pred_unfold]) 1);
by Safe_tac;
by (rtac UN_I 1);
by (rtac ReplaceI 2);
by (ALLGOALS (blast_tac (claset() addIs [well_ord_subset] addSEs [predE])));
qed "Ord_jump_cardinal";

(*Allows selective unfolding.  Less work than deriving intro/elim rules*)
Goalw [jump_cardinal_def]
     "i : jump_cardinal(K) <->   \
\         (EX r X. r <= K*K & X <= K & well_ord(X,r) & i = ordertype(X,r))";
by (fast_tac subset_cs 1);      (*It's vital to avoid reasoning about <=*)
qed "jump_cardinal_iff";

(*The easy part of Theorem 10.16: jump_cardinal(K) exceeds K*)
Goal "Ord(K) ==> K < jump_cardinal(K)";
by (resolve_tac [Ord_jump_cardinal RSN (2,ltI)] 1);
by (resolve_tac [jump_cardinal_iff RS iffD2] 1);
by (REPEAT_FIRST (ares_tac [exI, conjI, well_ord_Memrel]));
by (rtac subset_refl 2);
by (asm_simp_tac (simpset() addsimps [Memrel_def, subset_iff]) 1);
by (asm_simp_tac (simpset() addsimps [ordertype_Memrel]) 1);
qed "K_lt_jump_cardinal";

(*The proof by contradiction: the bijection f yields a wellordering of X
  whose ordertype is jump_cardinal(K).  *)
Goal "[| well_ord(X,r);  r <= K * K;  X <= K;       \
\            f : bij(ordertype(X,r), jump_cardinal(K))  \
\         |] ==> jump_cardinal(K) : jump_cardinal(K)";
by (subgoal_tac "f O ordermap(X,r): bij(X, jump_cardinal(K))" 1);
by (REPEAT (ares_tac [comp_bij, ordermap_bij] 2));
by (resolve_tac [jump_cardinal_iff RS iffD2] 1);
by (REPEAT_FIRST (resolve_tac [exI, conjI]));
by (rtac ([rvimage_type, Sigma_mono] MRS subset_trans) 1);
by (REPEAT (assume_tac 1));
by (etac (bij_is_inj RS well_ord_rvimage) 1);
by (rtac (Ord_jump_cardinal RS well_ord_Memrel) 1);
by (asm_simp_tac
    (simpset() addsimps [well_ord_Memrel RSN (2, bij_ordertype_vimage), 
			 ordertype_Memrel, Ord_jump_cardinal]) 1);
qed "Card_jump_cardinal_lemma";

(*The hard part of Theorem 10.16: jump_cardinal(K) is itself a cardinal*)
Goal "Card(jump_cardinal(K))";
by (rtac (Ord_jump_cardinal RS CardI) 1);
by (rewtac eqpoll_def);
by (safe_tac (claset() addSDs [ltD, jump_cardinal_iff RS iffD1]));
by (REPEAT (ares_tac [Card_jump_cardinal_lemma RS mem_irrefl] 1));
qed "Card_jump_cardinal";

(*** Basic properties of successor cardinals ***)

Goalw [csucc_def]
    "Ord(K) ==> Card(csucc(K)) & K < csucc(K)";
by (rtac LeastI 1);
by (REPEAT (ares_tac [conjI, Card_jump_cardinal, K_lt_jump_cardinal,
                      Ord_jump_cardinal] 1));
qed "csucc_basic";

bind_thm ("Card_csucc", csucc_basic RS conjunct1);

bind_thm ("lt_csucc", csucc_basic RS conjunct2);

Goal "Ord(K) ==> 0 < csucc(K)";
by (resolve_tac [[Ord_0_le, lt_csucc] MRS lt_trans1] 1);
by (REPEAT (assume_tac 1));
qed "Ord_0_lt_csucc";

Goalw [csucc_def]
    "[| Card(L);  K<L |] ==> csucc(K) le L";
by (rtac Least_le 1);
by (REPEAT (ares_tac [conjI, Card_is_Ord] 1));
qed "csucc_le";

Goal "[| Ord(i); Card(K) |] ==> i < csucc(K) <-> |i| le K";
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

Goal "!!K' K. [| Card(K'); Card(K) |] ==> K' < csucc(K) <-> K' le K";
by (asm_simp_tac 
    (simpset() addsimps [lt_csucc_iff, Card_cardinal_eq, Card_is_Ord]) 1);
qed "Card_lt_csucc_iff";

Goalw [InfCard_def]
    "InfCard(K) ==> InfCard(csucc(K))";
by (asm_simp_tac (simpset() addsimps [Card_csucc, Card_is_Ord, 
				      lt_csucc RS leI RSN (2,le_trans)]) 1);
qed "InfCard_csucc";


(*** Finite sets ***)

Goal "n: nat ==> ALL A. A eqpoll n --> A : Fin(A)";
by (induct_tac "n" 1);
by (simp_tac (simpset() addsimps eqpoll_0_iff::Fin.intrs) 1);
by (Clarify_tac 1);
by (subgoal_tac "EX u. u:A" 1);
by (etac exE 1);
by (resolve_tac [Diff_sing_eqpoll RS revcut_rl] 1);
by (assume_tac 2);
by (assume_tac 1);
by (res_inst_tac [("b", "A")] (cons_Diff RS subst) 1);
by (assume_tac 1);
by (resolve_tac [Fin.consI] 1);
by (Blast_tac 1);
by (blast_tac (claset() addIs [subset_consI  RS Fin_mono RS subsetD]) 1); 
(*Now for the lemma assumed above*)
by (rewtac eqpoll_def);
by (blast_tac (claset() addIs [bij_converse_bij RS bij_is_fun RS apply_type]) 1);
val lemma = result();

Goalw [Finite_def] "Finite(A) ==> A : Fin(A)";
by (blast_tac (claset() addIs [lemma RS spec RS mp]) 1);
qed "Finite_into_Fin";

Goal "A : Fin(U) ==> Finite(A)";
by (fast_tac (claset() addSIs [Finite_0, Finite_cons] addEs [Fin.induct]) 1);
qed "Fin_into_Finite";

Goal "Finite(A) <-> A : Fin(A)";
by (blast_tac (claset() addIs [Finite_into_Fin, Fin_into_Finite]) 1);
qed "Finite_Fin_iff";

Goal "[| Finite(A); Finite(B) |] ==> Finite(A Un B)";
by (blast_tac (claset() addSIs [Fin_into_Finite, Fin_UnI] 
                        addSDs [Finite_into_Fin]
                        addIs  [Un_upper1 RS Fin_mono RS subsetD,
	 		        Un_upper2 RS Fin_mono RS subsetD]) 1);
qed "Finite_Un";


(** Removing elements from a finite set decreases its cardinality **)

Goal "A: Fin(U) ==> x~:A --> ~ cons(x,A) lepoll A";
by (etac Fin_induct 1);
by (simp_tac (simpset() addsimps [lepoll_0_iff]) 1);
by (subgoal_tac "cons(x,cons(xa,y)) = cons(xa,cons(x,y))" 1);
by (Asm_simp_tac 1);
by (blast_tac (claset() addSDs [cons_lepoll_consD]) 1);
by (Blast_tac 1);
qed "Fin_imp_not_cons_lepoll";

Goal "[| Finite(A);  a~:A |] ==> |cons(a,A)| = succ(|A|)";
by (rewtac cardinal_def);
by (rtac Least_equality 1);
by (fold_tac [cardinal_def]);
by (simp_tac (simpset() addsimps [succ_def]) 1);
by (blast_tac (claset() addIs [cons_eqpoll_cong, well_ord_cardinal_eqpoll] 
                        addSEs [mem_irrefl]
                        addSDs [Finite_imp_well_ord]) 1);
by (blast_tac (claset() addIs [Ord_succ, Card_cardinal, Card_is_Ord]) 1);
by (rtac notI 1);
by (resolve_tac [Finite_into_Fin RS Fin_imp_not_cons_lepoll RS mp RS notE] 1);
by (assume_tac 1);
by (assume_tac 1);
by (eresolve_tac [eqpoll_sym RS eqpoll_imp_lepoll RS lepoll_trans] 1);
by (eresolve_tac [le_imp_lepoll RS lepoll_trans] 1);
by (blast_tac (claset() addIs [well_ord_cardinal_eqpoll RS eqpoll_imp_lepoll] 
                    addSDs [Finite_imp_well_ord]) 1);
qed "Finite_imp_cardinal_cons";


Goal "[| Finite(A);  a:A |] ==> succ(|A-{a}|) = |A|";
by (res_inst_tac [("b", "A")] (cons_Diff RS subst) 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [Finite_imp_cardinal_cons,
                                  Diff_subset RS subset_Finite]) 1);
by (asm_simp_tac (simpset() addsimps [cons_Diff]) 1);
qed "Finite_imp_succ_cardinal_Diff";

Goal "[| Finite(A);  a:A |] ==> |A-{a}| < |A|";
by (rtac succ_leE 1);
by (asm_simp_tac (simpset() addsimps [Finite_imp_succ_cardinal_Diff, 
				      Ord_cardinal RS le_refl]) 1);
qed "Finite_imp_cardinal_Diff";


(** Theorems by Krzysztof Grabczewski, proofs by lcp **)

val nat_implies_well_ord =
  (transfer CardinalArith.thy nat_into_Ord) RS well_ord_Memrel;

Goal "[| m:nat; n:nat |] ==> m + n eqpoll m #+ n";
by (rtac eqpoll_trans 1);
by (resolve_tac [well_ord_radd RS well_ord_cardinal_eqpoll RS eqpoll_sym] 1);
by (REPEAT (etac nat_implies_well_ord 1));
by (asm_simp_tac (simpset() 
		  addsimps [nat_cadd_eq_add RS sym, cadd_def, eqpoll_refl]) 1);
qed "nat_sum_eqpoll_sum";

