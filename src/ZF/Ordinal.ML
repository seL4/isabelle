(*  Title: 	ZF/Ordinal.thy
    ID:         $Id$
    Author: 	Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For Ordinal.thy.  Ordinals in Zermelo-Fraenkel Set Theory 
*)

open Ordinal;

(*** Rules for Transset ***)

(** Two neat characterisations of Transset **)

goalw Ordinal.thy [Transset_def] "Transset(A) <-> A<=Pow(A)";
by (fast_tac ZF_cs 1);
val Transset_iff_Pow = result();

goalw Ordinal.thy [Transset_def] "Transset(A) <-> Union(succ(A)) = A";
by (fast_tac (eq_cs addSEs [equalityE]) 1);
val Transset_iff_Union_succ = result();

(** Consequences of downwards closure **)

goalw Ordinal.thy [Transset_def]
    "!!C a b. [| Transset(C); {a,b}: C |] ==> a:C & b: C";
by (fast_tac ZF_cs 1);
val Transset_doubleton_D = result();

val [prem1,prem2] = goalw Ordinal.thy [Pair_def]
    "[| Transset(C); <a,b>: C |] ==> a:C & b: C";
by (cut_facts_tac [prem2] 1);	
by (fast_tac (ZF_cs addSDs [prem1 RS Transset_doubleton_D]) 1);
val Transset_Pair_D = result();

val prem1::prems = goal Ordinal.thy
    "[| Transset(C); A*B <= C; b: B |] ==> A <= C";
by (cut_facts_tac prems 1);
by (fast_tac (ZF_cs addSDs [prem1 RS Transset_Pair_D]) 1);
val Transset_includes_domain = result();

val prem1::prems = goal Ordinal.thy
    "[| Transset(C); A*B <= C; a: A |] ==> B <= C";
by (cut_facts_tac prems 1);
by (fast_tac (ZF_cs addSDs [prem1 RS Transset_Pair_D]) 1);
val Transset_includes_range = result();

val [prem1,prem2] = goalw (merge_theories(Ordinal.thy,Sum.thy)) [sum_def]
    "[| Transset(C); A+B <= C |] ==> A <= C & B <= C";
by (rtac (prem2 RS (Un_subset_iff RS iffD1) RS conjE) 1);
by (REPEAT (etac (prem1 RS Transset_includes_range) 1
     ORELSE resolve_tac [conjI, singletonI] 1));
val Transset_includes_summands = result();

val [prem] = goalw (merge_theories(Ordinal.thy,Sum.thy)) [sum_def]
    "Transset(C) ==> (A+B) Int C <= (A Int C) + (B Int C)";
by (rtac (Int_Un_distrib RS ssubst) 1);
by (fast_tac (ZF_cs addSDs [prem RS Transset_Pair_D]) 1);
val Transset_sum_Int_subset = result();

(** Closure properties **)

goalw Ordinal.thy [Transset_def] "Transset(0)";
by (fast_tac ZF_cs 1);
val Transset_0 = result();

goalw Ordinal.thy [Transset_def]
    "!!i j. [| Transset(i);  Transset(j) |] ==> Transset(i Un j)";
by (fast_tac ZF_cs 1);
val Transset_Un = result();

goalw Ordinal.thy [Transset_def]
    "!!i j. [| Transset(i);  Transset(j) |] ==> Transset(i Int j)";
by (fast_tac ZF_cs 1);
val Transset_Int = result();

goalw Ordinal.thy [Transset_def] "!!i. Transset(i) ==> Transset(succ(i))";
by (fast_tac ZF_cs 1);
val Transset_succ = result();

goalw Ordinal.thy [Transset_def] "!!i. Transset(i) ==> Transset(Pow(i))";
by (fast_tac ZF_cs 1);
val Transset_Pow = result();

goalw Ordinal.thy [Transset_def] "!!A. Transset(A) ==> Transset(Union(A))";
by (fast_tac ZF_cs 1);
val Transset_Union = result();

val [Transprem] = goalw Ordinal.thy [Transset_def]
    "[| !!i. i:A ==> Transset(i) |] ==> Transset(Union(A))";
by (fast_tac (ZF_cs addEs [Transprem RS bspec RS subsetD]) 1);
val Transset_Union_family = result();

val [prem,Transprem] = goalw Ordinal.thy [Transset_def]
    "[| j:A;  !!i. i:A ==> Transset(i) |] ==> Transset(Inter(A))";
by (cut_facts_tac [prem] 1);
by (fast_tac (ZF_cs addEs [Transprem RS bspec RS subsetD]) 1);
val Transset_Inter_family = result();

(*** Natural Deduction rules for Ord ***)

val prems = goalw Ordinal.thy [Ord_def]
    "[| Transset(i);  !!x. x:i ==> Transset(x) |]  ==>  Ord(i) ";
by (REPEAT (ares_tac (prems@[ballI,conjI]) 1));
val OrdI = result();

val [major] = goalw Ordinal.thy [Ord_def]
    "Ord(i) ==> Transset(i)";
by (rtac (major RS conjunct1) 1);
val Ord_is_Transset = result();

val [major,minor] = goalw Ordinal.thy [Ord_def]
    "[| Ord(i);  j:i |] ==> Transset(j) ";
by (rtac (minor RS (major RS conjunct2 RS bspec)) 1);
val Ord_contains_Transset = result();

(*** Lemmas for ordinals ***)

goalw Ordinal.thy [Ord_def,Transset_def] "!!i j.[| Ord(i);  j:i |] ==> Ord(j)";
by (fast_tac ZF_cs 1);
val Ord_in_Ord = result();

(* Ord(succ(j)) ==> Ord(j) *)
val Ord_succD = succI1 RSN (2, Ord_in_Ord);

goal Ordinal.thy "!!i j. [| Ord(i);  Transset(j);  j<=i |] ==> Ord(j)";
by (REPEAT (ares_tac [OrdI] 1
     ORELSE eresolve_tac [Ord_contains_Transset, subsetD] 1));
val Ord_subset_Ord = result();

goalw Ordinal.thy [Ord_def,Transset_def] "!!i j. [| j:i;  Ord(i) |] ==> j<=i";
by (fast_tac ZF_cs 1);
val OrdmemD = result();

goal Ordinal.thy "!!i j k. [| i:j;  j:k;  Ord(k) |] ==> i:k";
by (REPEAT (ares_tac [OrdmemD RS subsetD] 1));
val Ord_trans = result();

goal Ordinal.thy "!!i j. [| i:j;  Ord(j) |] ==> succ(i) <= j";
by (REPEAT (ares_tac [OrdmemD RSN (2,succ_subsetI)] 1));
val Ord_succ_subsetI = result();


(*** The construction of ordinals: 0, succ, Union ***)

goal Ordinal.thy "Ord(0)";
by (REPEAT (ares_tac [OrdI,Transset_0] 1 ORELSE etac emptyE 1));
val Ord_0 = result();

goal Ordinal.thy "!!i. Ord(i) ==> Ord(succ(i))";
by (REPEAT (ares_tac [OrdI,Transset_succ] 1
     ORELSE eresolve_tac [succE,ssubst,Ord_is_Transset,
			  Ord_contains_Transset] 1));
val Ord_succ = result();

goal Ordinal.thy "Ord(succ(i)) <-> Ord(i)";
by (fast_tac (ZF_cs addIs [Ord_succ] addDs [Ord_succD]) 1);
val Ord_succ_iff = result();

goalw Ordinal.thy [Ord_def] "!!i j. [| Ord(i); Ord(j) |] ==> Ord(i Un j)";
by (fast_tac (ZF_cs addSIs [Transset_Un]) 1);
val Ord_Un = result();

goalw Ordinal.thy [Ord_def] "!!i j. [| Ord(i); Ord(j) |] ==> Ord(i Int j)";
by (fast_tac (ZF_cs addSIs [Transset_Int]) 1);
val Ord_Int = result();

val nonempty::prems = goal Ordinal.thy
    "[| j:A;  !!i. i:A ==> Ord(i) |] ==> Ord(Inter(A))";
by (rtac (nonempty RS Transset_Inter_family RS OrdI) 1);
by (rtac Ord_is_Transset 1);
by (REPEAT (ares_tac ([Ord_contains_Transset,nonempty]@prems) 1
     ORELSE etac InterD 1));
val Ord_Inter = result();

val jmemA::prems = goal Ordinal.thy
    "[| j:A;  !!x. x:A ==> Ord(B(x)) |] ==> Ord(INT x:A. B(x))";
by (rtac (jmemA RS RepFunI RS Ord_Inter) 1);
by (etac RepFunE 1);
by (etac ssubst 1);
by (eresolve_tac prems 1);
val Ord_INT = result();

(*There is no set of all ordinals, for then it would contain itself*)
goal Ordinal.thy "~ (ALL i. i:X <-> Ord(i))";
by (rtac notI 1);
by (forw_inst_tac [("x", "X")] spec 1);
by (safe_tac (ZF_cs addSEs [mem_anti_refl]));
by (swap_res_tac [Ord_is_Transset RSN (2,OrdI)] 1);
by (fast_tac ZF_cs 2);
bw Transset_def;
by (safe_tac ZF_cs);
by (asm_full_simp_tac ZF_ss 1);
by (REPEAT (eresolve_tac [asm_rl, Ord_in_Ord] 1));
val ON_class = result();

(*** < is 'less than' for ordinals ***)

goalw Ordinal.thy [lt_def] "!!i j. [| i:j;  Ord(j) |] ==> i<j";
by (REPEAT (ares_tac [conjI] 1));
val ltI = result();

val major::prems = goalw Ordinal.thy [lt_def]
    "[| i<j;  [| i:j;  Ord(i);  Ord(j) |] ==> P |] ==> P";
by (rtac (major RS conjE) 1);
by (REPEAT (ares_tac (prems@[Ord_in_Ord]) 1));
val ltE = result();

goal Ordinal.thy "!!i j. i<j ==> i:j";
by (etac ltE 1);
by (assume_tac 1);
val ltD = result();

goalw Ordinal.thy [lt_def] "~ i<0";
by (fast_tac ZF_cs 1);
val not_lt0 = result();

(* i<0 ==> R *)
val lt0E = standard (not_lt0 RS notE);

goal Ordinal.thy "!!i j k. [| i<j;  j<k |] ==> i<k";
by (fast_tac (ZF_cs addSIs [ltI] addSEs [ltE, Ord_trans]) 1);
val lt_trans = result();

goalw Ordinal.thy [lt_def] "!!i j. [| i<j;  j<i |] ==> P";
by (REPEAT (eresolve_tac [asm_rl, conjE, mem_anti_sym] 1));
val lt_anti_sym = result();

val lt_anti_refl = prove_goal Ordinal.thy "i<i ==> P"
 (fn [major]=> [ (rtac (major RS (major RS lt_anti_sym)) 1) ]);

val lt_not_refl = prove_goal Ordinal.thy "~ i<i"
 (fn _=> [ (rtac notI 1), (etac lt_anti_refl 1) ]);

(** le is less than or equals;  recall  i le j  abbrevs  i<succ(j) !! **)

goalw Ordinal.thy [lt_def] "i le j <-> i<j | (i=j & Ord(j))";
by (fast_tac (ZF_cs addSIs [Ord_succ] addSDs [Ord_succD]) 1);
val le_iff = result();

goal Ordinal.thy "!!i j. i<j ==> i le j";
by (asm_simp_tac (ZF_ss addsimps [le_iff]) 1);
val leI = result();

goal Ordinal.thy "!!i. [| i=j;  Ord(j) |] ==> i le j";
by (asm_simp_tac (ZF_ss addsimps [le_iff]) 1);
val le_eqI = result();

val le_refl = refl RS le_eqI;

val [prem] = goal Ordinal.thy "(~ (i=j & Ord(j)) ==> i<j) ==> i le j";
by (rtac (disjCI RS (le_iff RS iffD2)) 1);
by (etac prem 1);
val leCI = result();

val major::prems = goal Ordinal.thy
    "[| i le j;  i<j ==> P;  [| i=j;  Ord(j) |] ==> P |] ==> P";
by (rtac (major RS (le_iff RS iffD1 RS disjE)) 1);
by (DEPTH_SOLVE (ares_tac prems 1 ORELSE etac conjE 1));
val leE = result();

goal Ordinal.thy "!!i j. [| i le j;  j le i |] ==> i=j";
by (asm_full_simp_tac (ZF_ss addsimps [le_iff]) 1);
by (fast_tac (ZF_cs addEs [lt_anti_sym]) 1);
val le_asym = result();

goal Ordinal.thy "i le 0 <-> i=0";
by (fast_tac (ZF_cs addSIs [Ord_0 RS le_refl] addSEs [leE, lt0E]) 1);
val le0_iff = result();

val le0D = standard (le0_iff RS iffD1);

val lt_cs = 
    ZF_cs addSIs [le_refl, leCI]
          addSDs [le0D]
          addSEs [lt_anti_refl, lt0E, leE];


(*** Natural Deduction rules for Memrel ***)

goalw Ordinal.thy [Memrel_def] "<a,b> : Memrel(A) <-> a:b & a:A & b:A";
by (fast_tac ZF_cs 1);
val Memrel_iff = result();

val prems = goal Ordinal.thy "[| a: b;  a: A;  b: A |] ==> <a,b> : Memrel(A)";
by (REPEAT (resolve_tac (prems@[conjI, Memrel_iff RS iffD2]) 1));
val MemrelI = result();

val [major,minor] = goal Ordinal.thy
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
goalw Ordinal.thy [wf_def] "wf(Memrel(A))";
by (EVERY1 [rtac (foundation RS disjE RS allI),
	    etac disjI1,
	    etac bexE, 
	    rtac (impI RS allI RS bexI RS disjI2),
	    etac MemrelE,
	    etac bspec,
	    REPEAT o assume_tac]);
val wf_Memrel = result();

(*Transset(i) does not suffice, though ALL j:i.Transset(j) does*)
goalw Ordinal.thy [Ord_def, Transset_def, trans_def]
    "!!i. Ord(i) ==> trans(Memrel(i))";
by (fast_tac (ZF_cs addSIs [MemrelI] addSEs [MemrelE]) 1);
val trans_Memrel = result();

(*If Transset(A) then Memrel(A) internalizes the membership relation below A*)
goalw Ordinal.thy [Transset_def]
    "!!A. Transset(A) ==> <a,b> : Memrel(A) <-> a:b & b:A";
by (fast_tac (ZF_cs addSIs [MemrelI] addSEs [MemrelE]) 1);
val Transset_Memrel_iff = result();


(*** Transfinite induction ***)

(*Epsilon induction over a transitive set*)
val major::prems = goalw Ordinal.thy [Transset_def]
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
val [major,indhyp] = goal Ordinal.thy
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

(** Proving that < is a linear ordering on the ordinals **)

val prems = goal Ordinal.thy
    "Ord(i) ==> (ALL j. Ord(j) --> i:j | i=j | j:i)";
by (trans_ind_tac "i" prems 1);
by (rtac (impI RS allI) 1);
by (trans_ind_tac "j" [] 1);
by (DEPTH_SOLVE (step_tac eq_cs 1 ORELSE Ord_trans_tac 1));
val Ord_linear_lemma = result();
val Ord_linear = standard (Ord_linear_lemma RS spec RS mp);

(*The trichotomy law for ordinals!*)
val ordi::ordj::prems = goalw Ordinal.thy [lt_def]
    "[| Ord(i);  Ord(j);  i<j ==> P;  i=j ==> P;  j<i ==> P |] ==> P";
by (rtac ([ordi,ordj] MRS Ord_linear RS disjE) 1);
by (etac disjE 2);
by (DEPTH_SOLVE (ares_tac ([ordi,ordj,conjI] @ prems) 1));
val Ord_linear_lt = result();

val prems = goal Ordinal.thy
    "[| Ord(i);  Ord(j);  i<j ==> P;  j le i ==> P |]  ==> P";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear_lt 1);
by (DEPTH_SOLVE (ares_tac ([leI, sym RS le_eqI] @ prems) 1));
val Ord_linear2 = result();

val prems = goal Ordinal.thy
    "[| Ord(i);  Ord(j);  i le j ==> P;  j le i ==> P |]  ==> P";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear_lt 1);
by (DEPTH_SOLVE (ares_tac ([leI,le_eqI] @ prems) 1));
val Ord_linear_le = result();

goal Ordinal.thy "!!i j. j le i ==> ~ i<j";
by (fast_tac (lt_cs addEs [lt_anti_sym]) 1);
val le_imp_not_lt = result();

goal Ordinal.thy "!!i j. [| ~ i<j;  Ord(i);  Ord(j) |] ==> j le i";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear2 1);
by (REPEAT (SOMEGOAL assume_tac));
by (fast_tac (lt_cs addEs [lt_anti_sym]) 1);
val not_lt_imp_le = result();

goal Ordinal.thy "!!i j. [| Ord(i);  Ord(j) |] ==> ~ i<j <-> j le i";
by (REPEAT (ares_tac [iffI, le_imp_not_lt, not_lt_imp_le] 1));
val not_lt_iff_le = result();

goal Ordinal.thy "!!i j. [| Ord(i);  Ord(j) |] ==> ~ i le j <-> j<i";
by (asm_simp_tac (ZF_ss addsimps [not_lt_iff_le RS iff_sym]) 1);
val not_le_iff_lt = result();

goal Ordinal.thy "!!i. Ord(i) ==> 0 le i";
by (etac (not_lt_iff_le RS iffD1) 1);
by (REPEAT (resolve_tac [Ord_0, not_lt0] 1));
val Ord_0_le = result();

goal Ordinal.thy "!!i. [| Ord(i);  i~=0 |] ==> 0<i";
by (etac (not_le_iff_lt RS iffD1) 1);
by (rtac Ord_0 1);
by (fast_tac lt_cs 1);
val Ord_0_lt = result();

(*** Results about less-than or equals ***)

(** For ordinals, j<=i (subset) implies j le i (less-than or equals) **)

goal Ordinal.thy "!!i j. [| j<=i;  Ord(i);  Ord(j) |] ==> j le i";
by (rtac (not_lt_iff_le RS iffD1) 1);
by (assume_tac 1);
by (assume_tac 1);
by (fast_tac (ZF_cs addEs [ltE, mem_anti_refl]) 1);
val subset_imp_le = result();

goal Ordinal.thy "!!i j. i le j ==> i<=j";
by (etac leE 1);
by (fast_tac ZF_cs 2);
by (fast_tac (subset_cs addIs [OrdmemD] addEs [ltE]) 1);
val le_imp_subset = result();

goal Ordinal.thy "j le i <-> j<=i & Ord(i) & Ord(j)";
by (fast_tac (ZF_cs addSEs [subset_imp_le, le_imp_subset]
	            addEs [ltE, make_elim Ord_succD]) 1);
val le_subset_iff = result();

goal Ordinal.thy "i le succ(j) <-> i le j | i=succ(j) & Ord(i)";
by (simp_tac (ZF_ss addsimps [le_iff]) 1);
by (fast_tac (ZF_cs addIs [Ord_succ] addDs [Ord_succD]) 1);
val le_succ_iff = result();

(*Just a variant of subset_imp_le*)
val [ordi,ordj,minor] = goal Ordinal.thy
    "[| Ord(i);  Ord(j);  !!x. x<j ==> x<i |] ==> j le i";
by (REPEAT_FIRST (ares_tac [notI RS not_lt_imp_le, ordi, ordj]));
be (minor RS lt_anti_refl) 1;
val all_lt_imp_le = result();

(** Transitive laws **)

goal Ordinal.thy "!!i j. [| i le j;  j<k |] ==> i<k";
by (fast_tac (ZF_cs addEs [leE, lt_trans]) 1);
val lt_trans1 = result();

goal Ordinal.thy "!!i j. [| i<j;  j le k |] ==> i<k";
by (fast_tac (ZF_cs addEs [leE, lt_trans]) 1);
val lt_trans2 = result();

goal Ordinal.thy "!!i j. [| i le j;  j le k |] ==> i le k";
by (REPEAT (ares_tac [lt_trans1] 1));
val le_trans = result();

goal Ordinal.thy "!!i j. i<j ==> succ(i) le j";
by (rtac (not_lt_iff_le RS iffD1) 1);
by (fast_tac (lt_cs addEs [lt_anti_sym]) 3);
by (ALLGOALS (fast_tac (ZF_cs addEs [ltE] addIs [Ord_succ])));
val succ_leI = result();

goal Ordinal.thy "!!i j. succ(i) le j ==> i<j";
by (rtac (not_le_iff_lt RS iffD1) 1);
by (fast_tac (lt_cs addEs [lt_anti_sym]) 3);
by (ALLGOALS (fast_tac (ZF_cs addEs [ltE, make_elim Ord_succD])));
val succ_leE = result();

goal Ordinal.thy "succ(i) le j <-> i<j";
by (REPEAT (ares_tac [iffI,succ_leI,succ_leE] 1));
val succ_le_iff = result();

(** Union and Intersection **)

goal Ordinal.thy "!!i j. [| Ord(i); Ord(j) |] ==> i le i Un j";
by (rtac (Un_upper1 RS subset_imp_le) 1);
by (REPEAT (ares_tac [Ord_Un] 1));
val Un_upper1_le = result();

goal Ordinal.thy "!!i j. [| Ord(i); Ord(j) |] ==> j le i Un j";
by (rtac (Un_upper2 RS subset_imp_le) 1);
by (REPEAT (ares_tac [Ord_Un] 1));
val Un_upper2_le = result();

(*Replacing k by succ(k') yields the similar rule for le!*)
goal Ordinal.thy "!!i j k. [| i<k;  j<k |] ==> i Un j < k";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear_le 1);
by (rtac (Un_commute RS ssubst) 4);
by (asm_full_simp_tac (ZF_ss addsimps [le_subset_iff, subset_Un_iff]) 4);
by (asm_full_simp_tac (ZF_ss addsimps [le_subset_iff, subset_Un_iff]) 3);
by (REPEAT (eresolve_tac [asm_rl, ltE] 1));
val Un_least_lt = result();

goal Ordinal.thy "!!i j. [| Ord(i); Ord(j) |] ==> i Un j < k  <->  i<k & j<k";
by (safe_tac (ZF_cs addSIs [Un_least_lt]));
br (Un_upper2_le RS lt_trans1) 2;
br (Un_upper1_le RS lt_trans1) 1;
by (REPEAT_SOME assume_tac);
val Un_least_lt_iff = result();

val [ordi,ordj,ordk] = goal Ordinal.thy
    "[| Ord(i); Ord(j); Ord(k) |] ==> i Un j : k  <->  i:k & j:k";
by (cut_facts_tac [[ordi,ordj] MRS 
		   read_instantiate [("k","k")] Un_least_lt_iff] 1);
by (asm_full_simp_tac (ZF_ss addsimps [lt_def,ordi,ordj,ordk]) 1);
val Un_least_mem_iff = result();

(*Replacing k by succ(k') yields the similar rule for le!*)
goal Ordinal.thy "!!i j k. [| i<k;  j<k |] ==> i Int j < k";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear_le 1);
by (rtac (Int_commute RS ssubst) 4);
by (asm_full_simp_tac (ZF_ss addsimps [le_subset_iff, subset_Int_iff]) 4);
by (asm_full_simp_tac (ZF_ss addsimps [le_subset_iff, subset_Int_iff]) 3);
by (REPEAT (eresolve_tac [asm_rl, ltE] 1));
val Int_greatest_lt = result();

(*FIXME: the Intersection duals are missing!*)


(*** Results about limits ***)

val prems = goal Ordinal.thy "[| !!i. i:A ==> Ord(i) |] ==> Ord(Union(A))";
by (rtac (Ord_is_Transset RS Transset_Union_family RS OrdI) 1);
by (REPEAT (etac UnionE 1 ORELSE ares_tac ([Ord_contains_Transset]@prems) 1));
val Ord_Union = result();

val prems = goal Ordinal.thy
    "[| !!x. x:A ==> Ord(B(x)) |] ==> Ord(UN x:A. B(x))";
by (rtac Ord_Union 1);
by (etac RepFunE 1);
by (etac ssubst 1);
by (eresolve_tac prems 1);
val Ord_UN = result();

(* No < version; consider (UN i:nat.i)=nat *)
val [ordi,limit] = goal Ordinal.thy
    "[| Ord(i);  !!x. x:A ==> b(x) le i |] ==> (UN x:A. b(x)) le i";
by (rtac (le_imp_subset RS UN_least RS subset_imp_le) 1);
by (REPEAT (ares_tac [ordi, Ord_UN, limit] 1 ORELSE etac (limit RS ltE) 1));
val UN_least_le = result();

val [jlti,limit] = goal Ordinal.thy
    "[| j<i;  !!x. x:A ==> b(x)<j |] ==> (UN x:A. succ(b(x))) < i";
by (rtac (jlti RS ltE) 1);
by (rtac (UN_least_le RS lt_trans2) 1);
by (REPEAT (ares_tac [jlti, succ_leI, limit] 1));
val UN_succ_least_lt = result();

val prems = goal Ordinal.thy
    "[| a: A;  i le b(a);  !!x. x:A ==> Ord(b(x)) |] ==> i le (UN x:A. b(x))";
by (resolve_tac (prems RL [ltE]) 1);
by (rtac (le_imp_subset RS subset_trans RS subset_imp_le) 1);
by (REPEAT (ares_tac (prems @ [UN_upper, Ord_UN]) 1));
val UN_upper_le = result();

goal Ordinal.thy "!!i. Ord(i) ==> (UN y:i. succ(y)) = i";
by (fast_tac (eq_cs addEs [Ord_trans]) 1);
val Ord_equality = result();

(*Holds for all transitive sets, not just ordinals*)
goal Ordinal.thy "!!i. Ord(i) ==> Union(i) <= i";
by (fast_tac (ZF_cs addSEs [Ord_trans]) 1);
val Ord_Union_subset = result();


(*** Limit ordinals -- general properties ***)

goalw Ordinal.thy [Limit_def] "!!i. Limit(i) ==> Union(i) = i";
by (fast_tac (eq_cs addSIs [ltI] addSEs [ltE] addEs [Ord_trans]) 1);
val Limit_Union_eq = result();

goalw Ordinal.thy [Limit_def] "!!i. Limit(i) ==> Ord(i)";
by (etac conjunct1 1);
val Limit_is_Ord = result();

goalw Ordinal.thy [Limit_def] "!!i. Limit(i) ==> 0 < i";
by (etac (conjunct2 RS conjunct1) 1);
val Limit_has_0 = result();

goalw Ordinal.thy [Limit_def] "!!i. [| Limit(i);  j<i |] ==> succ(j) < i";
by (fast_tac ZF_cs 1);
val Limit_has_succ = result();

goalw Ordinal.thy [Limit_def]
    "!!i. [| 0<i;  ALL y. succ(y) ~= i |] ==> Limit(i)";
by (safe_tac subset_cs);
by (rtac (not_le_iff_lt RS iffD1) 2);
by (fast_tac (lt_cs addEs [lt_anti_sym]) 4);
by (REPEAT (eresolve_tac [asm_rl, ltE, Ord_succ] 1));
val non_succ_LimitI = result();

goal Ordinal.thy "!!i. Limit(succ(i)) ==> P";
br lt_anti_refl 1;
br Limit_has_succ 1;
ba 1;
be (Limit_is_Ord RS Ord_succD RS le_refl) 1;
val succ_LimitE = result();

goal Ordinal.thy "!!i. [| Limit(i);  i le succ(j) |] ==> i le j";
by (safe_tac (ZF_cs addSEs [succ_LimitE, leE]));
val Limit_le_succD = result();


