(*  Title: 	ZF/ordinal.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For ordinal.thy.  Ordinals in Zermelo-Fraenkel Set Theory 
*)

open Ord;

(*** Rules for Transset ***)

(** Two neat characterisations of Transset **)

goalw Ord.thy [Transset_def] "Transset(A) <-> A<=Pow(A)";
by (fast_tac ZF_cs 1);
val Transset_iff_Pow = result();

goalw Ord.thy [Transset_def] "Transset(A) <-> Union(succ(A)) = A";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val Transset_iff_Union_succ = result();

(** Consequences of downwards closure **)

goalw Ord.thy [Transset_def]
    "!!C a b. [| Transset(C); {a,b}: C |] ==> a:C & b: C";
by (fast_tac ZF_cs 1);
val Transset_doubleton_D = result();

val [prem1,prem2] = goalw Ord.thy [Pair_def]
    "[| Transset(C); <a,b>: C |] ==> a:C & b: C";
by (cut_facts_tac [prem2] 1);	
by (fast_tac (ZF_cs addSDs [prem1 RS Transset_doubleton_D]) 1);
val Transset_Pair_D = result();

val prem1::prems = goal Ord.thy
    "[| Transset(C); A*B <= C; b: B |] ==> A <= C";
by (cut_facts_tac prems 1);
by (fast_tac (ZF_cs addSDs [prem1 RS Transset_Pair_D]) 1);
val Transset_includes_domain = result();

val prem1::prems = goal Ord.thy
    "[| Transset(C); A*B <= C; a: A |] ==> B <= C";
by (cut_facts_tac prems 1);
by (fast_tac (ZF_cs addSDs [prem1 RS Transset_Pair_D]) 1);
val Transset_includes_range = result();

val [prem1,prem2] = goalw (merge_theories(Ord.thy,Sum.thy)) [sum_def]
    "[| Transset(C); A+B <= C |] ==> A <= C & B <= C";
br (prem2 RS (Un_subset_iff RS iffD1) RS conjE) 1;
by (REPEAT (etac (prem1 RS Transset_includes_range) 1
     ORELSE resolve_tac [conjI, singletonI] 1));
val Transset_includes_summands = result();

val [prem] = goalw (merge_theories(Ord.thy,Sum.thy)) [sum_def]
    "Transset(C) ==> (A+B) Int C <= (A Int C) + (B Int C)";
br (Int_Un_distrib RS ssubst) 1;
by (fast_tac (ZF_cs addSDs [prem RS Transset_Pair_D]) 1);
val Transset_sum_Int_subset = result();

(** Closure properties **)

goalw Ord.thy [Transset_def] "Transset(0)";
by (fast_tac ZF_cs 1);
val Transset_0 = result();

goalw Ord.thy [Transset_def]
    "!!i j. [| Transset(i);  Transset(j) |] ==> Transset(i Un j)";
by (fast_tac ZF_cs 1);
val Transset_Un = result();

goalw Ord.thy [Transset_def]
    "!!i j. [| Transset(i);  Transset(j) |] ==> Transset(i Int j)";
by (fast_tac ZF_cs 1);
val Transset_Int = result();

goalw Ord.thy [Transset_def] "!!i. Transset(i) ==> Transset(succ(i))";
by (fast_tac ZF_cs 1);
val Transset_succ = result();

goalw Ord.thy [Transset_def] "!!i. Transset(i) ==> Transset(Pow(i))";
by (fast_tac ZF_cs 1);
val Transset_Pow = result();

goalw Ord.thy [Transset_def] "!!A. Transset(A) ==> Transset(Union(A))";
by (fast_tac ZF_cs 1);
val Transset_Union = result();

val [Transprem] = goalw Ord.thy [Transset_def]
    "[| !!i. i:A ==> Transset(i) |] ==> Transset(Union(A))";
by (fast_tac (ZF_cs addEs [Transprem RS bspec RS subsetD]) 1);
val Transset_Union_family = result();

val [prem,Transprem] = goalw Ord.thy [Transset_def]
    "[| j:A;  !!i. i:A ==> Transset(i) |] ==> Transset(Inter(A))";
by (cut_facts_tac [prem] 1);
by (fast_tac (ZF_cs addEs [Transprem RS bspec RS subsetD]) 1);
val Transset_Inter_family = result();

(*** Natural Deduction rules for Ord ***)

val prems = goalw Ord.thy [Ord_def]
    "[| Transset(i);  !!x. x:i ==> Transset(x) |]  ==>  Ord(i) ";
by (REPEAT (ares_tac (prems@[ballI,conjI]) 1));
val OrdI = result();

val [major] = goalw Ord.thy [Ord_def]
    "Ord(i) ==> Transset(i)";
by (rtac (major RS conjunct1) 1);
val Ord_is_Transset = result();

val [major,minor] = goalw Ord.thy [Ord_def]
    "[| Ord(i);  j:i |] ==> Transset(j) ";
by (rtac (minor RS (major RS conjunct2 RS bspec)) 1);
val Ord_contains_Transset = result();

(*** Lemmas for ordinals ***)

goalw Ord.thy [Ord_def,Transset_def] "!!i j. [| Ord(i);  j:i |] ==> Ord(j) ";
by (fast_tac ZF_cs 1);
val Ord_in_Ord = result();

goal Ord.thy "!!i j. [| Ord(i);  Transset(j);  j<=i |] ==> Ord(j)";
by (REPEAT (ares_tac [OrdI] 1
     ORELSE eresolve_tac [Ord_contains_Transset, subsetD] 1));
val Ord_subset_Ord = result();

goalw Ord.thy [Ord_def,Transset_def] "!!i j. [| j:i;  Ord(i) |] ==> j<=i";
by (fast_tac ZF_cs 1);
val OrdmemD = result();

goal Ord.thy "!!i j k. [| i:j;  j:k;  Ord(k) |] ==> i:k";
by (REPEAT (ares_tac [OrdmemD RS subsetD] 1));
val Ord_trans = result();

goal Ord.thy "!!i j. [| i:j;  Ord(j) |] ==> succ(i) <= j";
by (REPEAT (ares_tac [OrdmemD RSN (2,succ_subsetI)] 1));
val Ord_succ_subsetI = result();


(*** The construction of ordinals: 0, succ, Union ***)

goal Ord.thy "Ord(0)";
by (REPEAT (ares_tac [OrdI,Transset_0] 1 ORELSE etac emptyE 1));
val Ord_0 = result();

goal Ord.thy "!!i. Ord(i) ==> Ord(succ(i))";
by (REPEAT (ares_tac [OrdI,Transset_succ] 1
     ORELSE eresolve_tac [succE,ssubst,Ord_is_Transset,
			  Ord_contains_Transset] 1));
val Ord_succ = result();

val nonempty::prems = goal Ord.thy
    "[| j:A;  !!i. i:A ==> Ord(i) |] ==> Ord(Inter(A))";
by (rtac (nonempty RS Transset_Inter_family RS OrdI) 1);
by (rtac Ord_is_Transset 1);
by (REPEAT (ares_tac ([Ord_contains_Transset,nonempty]@prems) 1
     ORELSE etac InterD 1));
val Ord_Inter = result();

val jmemA::prems = goal Ord.thy
    "[| j:A;  !!x. x:A ==> Ord(B(x)) |] ==> Ord(INT x:A. B(x))";
by (rtac (jmemA RS RepFunI RS Ord_Inter) 1);
by (etac RepFunE 1);
by (etac ssubst 1);
by (eresolve_tac prems 1);
val Ord_INT = result();


(*** Natural Deduction rules for Memrel ***)

goalw Ord.thy [Memrel_def] "<a,b> : Memrel(A) <-> a:b & a:A & b:A";
by (fast_tac ZF_cs 1);
val Memrel_iff = result();

val prems = goal Ord.thy "[| a: b;  a: A;  b: A |]  ==>  <a,b> : Memrel(A)";
by (REPEAT (resolve_tac (prems@[conjI, Memrel_iff RS iffD2]) 1));
val MemrelI = result();

val [major,minor] = goal Ord.thy
    "[| <a,b> : Memrel(A);  \
\       [| a: A;  b: A;  a:b |]  ==> P \
\    |]  ==> P";
by (rtac (major RS (Memrel_iff RS iffD1) RS conjE) 1);
by (etac conjE 1);
by (rtac minor 1);
by (REPEAT (assume_tac 1));
val MemrelE = result();

(*The membership relation (as a set) is well-founded.
  Proof idea: show A<=B by applying the foundation axiom to A-B *)
goalw Ord.thy [wf_def] "wf(Memrel(A))";
by (EVERY1 [rtac (foundation RS disjE RS allI),
	    etac disjI1,
	    etac bexE, 
	    rtac (impI RS allI RS bexI RS disjI2),
	    etac MemrelE,
	    etac bspec,
	    REPEAT o assume_tac]);
val wf_Memrel = result();

(*** Transfinite induction ***)

(*Epsilon induction over a transitive set*)
val major::prems = goalw Ord.thy [Transset_def]
    "[| i: k;  Transset(k);                          \
\       !!x.[| x: k;  ALL y:x. P(y) |] ==> P(x) \
\    |]  ==>  P(i)";
by (rtac (major RS (wf_Memrel RS wf_induct2)) 1);
by (fast_tac (ZF_cs addEs [MemrelE]) 1);
by (resolve_tac prems 1);
by (assume_tac 1);
by (cut_facts_tac prems 1);
by (fast_tac (ZF_cs addIs [MemrelI]) 1);
val Transset_induct = result();

(*Induction over an ordinal*)
val Ord_induct = Ord_is_Transset RSN (2, Transset_induct);

(*Induction over the class of ordinals -- a useful corollary of Ord_induct*)
val [major,indhyp] = goal Ord.thy
    "[| Ord(i); \
\       !!x.[| Ord(x);  ALL y:x. P(y) |] ==> P(x) \
\    |]  ==>  P(i)";
by (rtac (major RS Ord_succ RS (succI1 RS Ord_induct)) 1);
by (rtac indhyp 1);
by (rtac (major RS Ord_succ RS Ord_in_Ord) 1);
by (REPEAT (assume_tac 1));
val trans_induct = result();

(*Perform induction on i, then prove the Ord(i) subgoal using prems. *)
fun trans_ind_tac a prems i = 
    EVERY [res_inst_tac [("i",a)] trans_induct i,
	   rename_last_tac a ["1"] (i+1),
	   ares_tac prems i];


(*** Fundamental properties of the epsilon ordering (< on ordinals) ***)

(*Finds contradictions for the following proof*)
val Ord_trans_tac = EVERY' [etac notE, etac Ord_trans, REPEAT o atac];

(** Proving that "member" is a linear ordering on the ordinals **)

val prems = goal Ord.thy
    "Ord(i) ==> (ALL j. Ord(j) --> i:j | i=j | j:i)";
by (trans_ind_tac "i" prems 1);
by (rtac (impI RS allI) 1);
by (trans_ind_tac "j" [] 1);
by (DEPTH_SOLVE (swap_res_tac [disjCI,equalityI,subsetI] 1
     ORELSE ball_tac 1
     ORELSE eresolve_tac [impE,disjE,allE] 1 
     ORELSE hyp_subst_tac 1
     ORELSE Ord_trans_tac 1));
val Ord_linear_lemma = result();

val ordi::ordj::prems = goal Ord.thy
    "[| Ord(i);  Ord(j);  i:j ==> P;  i=j ==> P;  j:i ==> P |] \
\    ==> P";
by (rtac (ordi RS Ord_linear_lemma RS spec RS impE) 1);
by (rtac ordj 1);
by (REPEAT (eresolve_tac (prems@[asm_rl,disjE]) 1)); 
val Ord_linear = result();

val prems = goal Ord.thy
    "[| Ord(i);  Ord(j);  i<=j ==> P;  j<=i ==> P |] \
\    ==> P";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear 1);
by (DEPTH_SOLVE (ares_tac (prems@[subset_refl]) 1
          ORELSE eresolve_tac [asm_rl,OrdmemD,ssubst] 1));
val Ord_subset = result();

goal Ord.thy "!!i j. [| j<=i;  ~ i<=j;  Ord(i);  Ord(j) |] ==> j:i";
by (etac Ord_linear 1);
by (REPEAT (ares_tac [subset_refl] 1
     ORELSE eresolve_tac [notE,OrdmemD,ssubst] 1));
val Ord_member = result();

val [prem] = goal Ord.thy "Ord(i) ==> 0: succ(i)";
by (rtac (empty_subsetI RS Ord_member) 1);
by (fast_tac ZF_cs 1);
by (rtac (prem RS Ord_succ) 1);
by (rtac Ord_0 1);
val Ord_0_mem_succ = result();

goal Ord.thy "!!i j. [| Ord(i);  Ord(j) |] ==> j:i <-> j<=i & ~(i<=j)";
by (rtac iffI 1);
by (rtac conjI 1);
by (etac OrdmemD 1);
by (rtac (mem_anti_refl RS notI) 2);
by (etac subsetD 2);
by (REPEAT (eresolve_tac [asm_rl, conjE, Ord_member] 1));
val Ord_member_iff = result();

goal Ord.thy "!!i. Ord(i) ==> 0:i  <-> ~ i=0";
be (Ord_0 RSN (2,Ord_member_iff) RS iff_trans) 1;
by (fast_tac eq_cs 1);
val Ord_0_member_iff = result();

(** For ordinals, i: succ(j) means 'less-than or equals' **)

goal Ord.thy "!!i j. [| j<=i;  Ord(i);  Ord(j) |] ==> j : succ(i)";
by (rtac Ord_member 1);
by (REPEAT (ares_tac [Ord_succ] 3));
by (rtac (mem_anti_refl RS notI) 2);
by (etac subsetD 2);
by (ALLGOALS (fast_tac ZF_cs));
val member_succI = result();

goalw Ord.thy [Transset_def,Ord_def]
    "!!i j. [| i : succ(j);  Ord(j) |] ==> i<=j";
by (fast_tac ZF_cs 1);
val member_succD = result();

goal Ord.thy "!!i j. [| Ord(i);  Ord(j) |] ==> j:succ(i) <-> j<=i";
by (fast_tac (subset_cs addSEs [member_succI, member_succD]) 1);
val member_succ_iff = result();

goal Ord.thy
    "!!i j. [| Ord(i);  Ord(j) |] ==> i<=succ(j) <-> i<=j | i=succ(j)";
by (ASM_SIMP_TAC (ZF_ss addrews [member_succ_iff RS iff_sym, Ord_succ]) 1);
by (fast_tac ZF_cs 1);
val subset_succ_iff = result();

goal Ord.thy "!!i j. [| i:succ(j);  j:k;  Ord(k) |] ==> i:k";
by (fast_tac (ZF_cs addEs [Ord_trans]) 1);
val Ord_trans1 = result();

goal Ord.thy "!!i j. [| i:j;  j:succ(k);  Ord(k) |] ==> i:k";
by (fast_tac (ZF_cs addEs [Ord_trans]) 1);
val Ord_trans2 = result();

goal Ord.thy "!!i jk. [| i:j;  j<=k;  Ord(k) |] ==> i:k";
by (fast_tac (ZF_cs addEs [Ord_trans]) 1);
val Ord_transsub2 = result();

goal Ord.thy "!!i j. [| i:j;  Ord(j) |] ==> succ(i) : succ(j)";
by (rtac member_succI 1);
by (REPEAT (ares_tac [subsetI,Ord_succ,Ord_in_Ord] 1   
     ORELSE eresolve_tac [succE,Ord_trans,ssubst] 1));
val succ_mem_succI = result();

goal Ord.thy "!!i j. [| succ(i) : succ(j);  Ord(j) |] ==> i:j";
by (REPEAT (eresolve_tac [asm_rl, make_elim member_succD, succ_subsetE] 1));
val succ_mem_succE = result();

goal Ord.thy "!!i j. Ord(j) ==> succ(i) : succ(j) <-> i:j";
by (REPEAT (ares_tac [iffI,succ_mem_succI,succ_mem_succE] 1));
val succ_mem_succ_iff = result();

goal Ord.thy "!!i j. [| i<=j;  Ord(i);  Ord(j) |] ==> succ(i) <= succ(j)";
by (rtac (member_succI RS succ_mem_succI RS member_succD) 1);
by (REPEAT (ares_tac [Ord_succ] 1));
val Ord_succ_mono = result();

goal Ord.thy "!!i j k. [| i:k;  j:k;  Ord(k) |] ==> i Un j : k";
by (res_inst_tac [("i","i"),("j","j")] Ord_subset 1);
by (REPEAT (eresolve_tac [asm_rl, Ord_in_Ord] 1));
by (ASM_SIMP_TAC (ZF_ss addrews [subset_Un_iff RS iffD1]) 1);
by (rtac (Un_commute RS ssubst) 1);
by (ASM_SIMP_TAC (ZF_ss addrews [subset_Un_iff RS iffD1]) 1);
val Ord_member_UnI = result();

goal Ord.thy "!!i j k. [| i:k;  j:k;  Ord(k) |] ==> i Int j : k";
by (res_inst_tac [("i","i"),("j","j")] Ord_subset 1);
by (REPEAT (eresolve_tac [asm_rl, Ord_in_Ord] 1));
by (ASM_SIMP_TAC (ZF_ss addrews [subset_Int_iff RS iffD1]) 1);
by (rtac (Int_commute RS ssubst) 1);
by (ASM_SIMP_TAC (ZF_ss addrews [subset_Int_iff RS iffD1]) 1);
val Ord_member_IntI = result();


(*** Results about limits ***)

val prems = goal Ord.thy "[| !!i. i:A ==> Ord(i) |] ==> Ord(Union(A))";
by (rtac (Ord_is_Transset RS Transset_Union_family RS OrdI) 1);
by (REPEAT (etac UnionE 1 ORELSE ares_tac ([Ord_contains_Transset]@prems) 1));
val Ord_Union = result();

val prems = goal Ord.thy "[| !!x. x:A ==> Ord(B(x)) |] ==> Ord(UN x:A. B(x))";
by (rtac Ord_Union 1);
by (etac RepFunE 1);
by (etac ssubst 1);
by (eresolve_tac prems 1);
val Ord_UN = result();

(*The upper bound must be a successor ordinal --
  consider that (UN i:nat.i)=nat although nat is an upper bound of each i*)
val [ordi,limit] = goal Ord.thy
    "[| Ord(i);  !!y. y:A ==> f(y): succ(i) |] ==> (UN y:A. f(y)) : succ(i)";
by (rtac (member_succD RS UN_least RS member_succI) 1);
by (REPEAT (ares_tac [ordi, Ord_UN, ordi RS Ord_succ RS Ord_in_Ord,
		      limit] 1));
val sup_least = result();

val [jmemi,ordi,limit] = goal Ord.thy
    "[| j: i;  Ord(i);  !!y. y:A ==> f(y): j |] ==> (UN y:A. succ(f(y))) : i";
by (cut_facts_tac [jmemi RS (ordi RS Ord_in_Ord)] 1);
by (rtac (sup_least RS Ord_trans2) 1);
by (REPEAT (ares_tac [jmemi, ordi, succ_mem_succI, limit] 1));
val sup_least2 = result();

goal Ord.thy "!!i. Ord(i) ==> (UN y:i. succ(y)) = i";
by (fast_tac (eq_cs addSEs [Ord_trans1]) 1);
val Ord_equality = result();

(*Holds for all transitive sets, not just ordinals*)
goal Ord.thy "!!i. Ord(i) ==> Union(i) <= i";
by (fast_tac (ZF_cs addSEs [Ord_trans]) 1);
val Ord_Union_subset = result();
