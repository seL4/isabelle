(*  Title:      ZF/Ordinal.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge

For Ordinal.thy.  Ordinals in Zermelo-Fraenkel Set Theory 
*)

open Ordinal;

(*** Rules for Transset ***)

(** Two neat characterisations of Transset **)

goalw Ordinal.thy [Transset_def] "Transset(A) <-> A<=Pow(A)";
by (Blast_tac 1);
qed "Transset_iff_Pow";

goalw Ordinal.thy [Transset_def] "Transset(A) <-> Union(succ(A)) = A";
by (blast_tac (claset() addSEs [equalityE]) 1);
qed "Transset_iff_Union_succ";

(** Consequences of downwards closure **)

goalw Ordinal.thy [Transset_def]
    "!!C a b. [| Transset(C); {a,b}: C |] ==> a:C & b: C";
by (Blast_tac 1);
qed "Transset_doubleton_D";

val [prem1,prem2] = goalw Ordinal.thy [Pair_def]
    "[| Transset(C); <a,b>: C |] ==> a:C & b: C";
by (cut_facts_tac [prem2] 1);   
by (blast_tac (claset() addSDs [prem1 RS Transset_doubleton_D]) 1);
qed "Transset_Pair_D";

val prem1::prems = goal Ordinal.thy
    "[| Transset(C); A*B <= C; b: B |] ==> A <= C";
by (cut_facts_tac prems 1);
by (blast_tac (claset() addSDs [prem1 RS Transset_Pair_D]) 1);
qed "Transset_includes_domain";

val prem1::prems = goal Ordinal.thy
    "[| Transset(C); A*B <= C; a: A |] ==> B <= C";
by (cut_facts_tac prems 1);
by (blast_tac (claset() addSDs [prem1 RS Transset_Pair_D]) 1);
qed "Transset_includes_range";

(** Closure properties **)

goalw Ordinal.thy [Transset_def] "Transset(0)";
by (Blast_tac 1);
qed "Transset_0";

goalw Ordinal.thy [Transset_def]
    "!!i j. [| Transset(i);  Transset(j) |] ==> Transset(i Un j)";
by (Blast_tac 1);
qed "Transset_Un";

goalw Ordinal.thy [Transset_def]
    "!!i j. [| Transset(i);  Transset(j) |] ==> Transset(i Int j)";
by (Blast_tac 1);
qed "Transset_Int";

goalw Ordinal.thy [Transset_def] "!!i. Transset(i) ==> Transset(succ(i))";
by (Blast_tac 1);
qed "Transset_succ";

goalw Ordinal.thy [Transset_def] "!!i. Transset(i) ==> Transset(Pow(i))";
by (Blast_tac 1);
qed "Transset_Pow";

goalw Ordinal.thy [Transset_def] "!!A. Transset(A) ==> Transset(Union(A))";
by (Blast_tac 1);
qed "Transset_Union";

val [Transprem] = goalw Ordinal.thy [Transset_def]
    "[| !!i. i:A ==> Transset(i) |] ==> Transset(Union(A))";
by (blast_tac (claset() addDs [Transprem RS bspec RS subsetD]) 1);
qed "Transset_Union_family";

val [prem,Transprem] = goalw Ordinal.thy [Transset_def]
    "[| j:A;  !!i. i:A ==> Transset(i) |] ==> Transset(Inter(A))";
by (cut_facts_tac [prem] 1);
by (blast_tac (claset() addDs [Transprem RS bspec RS subsetD]) 1);
qed "Transset_Inter_family";

(*** Natural Deduction rules for Ord ***)

val prems = goalw Ordinal.thy [Ord_def]
    "[| Transset(i);  !!x. x:i ==> Transset(x) |]  ==>  Ord(i)";
by (REPEAT (ares_tac (prems@[ballI,conjI]) 1));
qed "OrdI";

val [major] = goalw Ordinal.thy [Ord_def]
    "Ord(i) ==> Transset(i)";
by (rtac (major RS conjunct1) 1);
qed "Ord_is_Transset";

val [major,minor] = goalw Ordinal.thy [Ord_def]
    "[| Ord(i);  j:i |] ==> Transset(j) ";
by (rtac (minor RS (major RS conjunct2 RS bspec)) 1);
qed "Ord_contains_Transset";

(*** Lemmas for ordinals ***)

goalw Ordinal.thy [Ord_def,Transset_def] "!!i j.[| Ord(i);  j:i |] ==> Ord(j)";
by (Blast_tac 1);
qed "Ord_in_Ord";

(* Ord(succ(j)) ==> Ord(j) *)
val Ord_succD = succI1 RSN (2, Ord_in_Ord);

AddSDs [Ord_succD];

goal Ordinal.thy "!!i j. [| Ord(i);  Transset(j);  j<=i |] ==> Ord(j)";
by (REPEAT (ares_tac [OrdI] 1
     ORELSE eresolve_tac [Ord_contains_Transset, subsetD] 1));
qed "Ord_subset_Ord";

goalw Ordinal.thy [Ord_def,Transset_def] "!!i j. [| j:i;  Ord(i) |] ==> j<=i";
by (Blast_tac 1);
qed "OrdmemD";

goal Ordinal.thy "!!i j k. [| i:j;  j:k;  Ord(k) |] ==> i:k";
by (REPEAT (ares_tac [OrdmemD RS subsetD] 1));
qed "Ord_trans";

goal Ordinal.thy "!!i j. [| i:j;  Ord(j) |] ==> succ(i) <= j";
by (REPEAT (ares_tac [OrdmemD RSN (2,succ_subsetI)] 1));
qed "Ord_succ_subsetI";


(*** The construction of ordinals: 0, succ, Union ***)

goal Ordinal.thy "Ord(0)";
by (REPEAT (ares_tac [OrdI,Transset_0] 1 ORELSE etac emptyE 1));
qed "Ord_0";

goal Ordinal.thy "!!i. Ord(i) ==> Ord(succ(i))";
by (REPEAT (ares_tac [OrdI,Transset_succ] 1
     ORELSE eresolve_tac [succE,ssubst,Ord_is_Transset,
                          Ord_contains_Transset] 1));
qed "Ord_succ";

bind_thm ("Ord_1", Ord_0 RS Ord_succ);

goal Ordinal.thy "Ord(succ(i)) <-> Ord(i)";
by (blast_tac (claset() addIs [Ord_succ] addDs [Ord_succD]) 1);
qed "Ord_succ_iff";

Addsimps [Ord_0, Ord_succ_iff];
AddSIs   [Ord_0, Ord_succ];

goalw Ordinal.thy [Ord_def] "!!i j. [| Ord(i); Ord(j) |] ==> Ord(i Un j)";
by (blast_tac (claset() addSIs [Transset_Un]) 1);
qed "Ord_Un";

goalw Ordinal.thy [Ord_def] "!!i j. [| Ord(i); Ord(j) |] ==> Ord(i Int j)";
by (blast_tac (claset() addSIs [Transset_Int]) 1);
qed "Ord_Int";

val nonempty::prems = goal Ordinal.thy
    "[| j:A;  !!i. i:A ==> Ord(i) |] ==> Ord(Inter(A))";
by (rtac (nonempty RS Transset_Inter_family RS OrdI) 1);
by (rtac Ord_is_Transset 1);
by (REPEAT (ares_tac ([Ord_contains_Transset,nonempty]@prems) 1
     ORELSE etac InterD 1));
qed "Ord_Inter";

val jmemA::prems = goal Ordinal.thy
    "[| j:A;  !!x. x:A ==> Ord(B(x)) |] ==> Ord(INT x:A. B(x))";
by (rtac (jmemA RS RepFunI RS Ord_Inter) 1);
by (etac RepFunE 1);
by (etac ssubst 1);
by (eresolve_tac prems 1);
qed "Ord_INT";

(*There is no set of all ordinals, for then it would contain itself*)
goal Ordinal.thy "~ (ALL i. i:X <-> Ord(i))";
by (rtac notI 1);
by (forw_inst_tac [("x", "X")] spec 1);
by (safe_tac (claset() addSEs [mem_irrefl]));
by (swap_res_tac [Ord_is_Transset RSN (2,OrdI)] 1);
by (Blast_tac 2);
by (rewtac Transset_def);
by Safe_tac;
by (Asm_full_simp_tac 1);
by (REPEAT (eresolve_tac [asm_rl, Ord_in_Ord] 1));
qed "ON_class";

(*** < is 'less than' for ordinals ***)

goalw Ordinal.thy [lt_def] "!!i j. [| i:j;  Ord(j) |] ==> i<j";
by (REPEAT (ares_tac [conjI] 1));
qed "ltI";

val major::prems = goalw Ordinal.thy [lt_def]
    "[| i<j;  [| i:j;  Ord(i);  Ord(j) |] ==> P |] ==> P";
by (rtac (major RS conjE) 1);
by (REPEAT (ares_tac (prems@[Ord_in_Ord]) 1));
qed "ltE";

goal Ordinal.thy "!!i j. i<j ==> i:j";
by (etac ltE 1);
by (assume_tac 1);
qed "ltD";

goalw Ordinal.thy [lt_def] "~ i<0";
by (Blast_tac 1);
qed "not_lt0";

Addsimps [not_lt0];

goal Ordinal.thy "!!i j. j<i ==> Ord(j)";
by (etac ltE 1 THEN assume_tac 1);
qed "lt_Ord";

goal Ordinal.thy "!!i j. j<i ==> Ord(i)";
by (etac ltE 1 THEN assume_tac 1);
qed "lt_Ord2";

(* "ja le j ==> Ord(j)" *)
bind_thm ("le_Ord2", lt_Ord2 RS Ord_succD);

(* i<0 ==> R *)
bind_thm ("lt0E", not_lt0 RS notE);

goal Ordinal.thy "!!i j k. [| i<j;  j<k |] ==> i<k";
by (blast_tac (claset() addSIs [ltI] addSEs [ltE] addIs [Ord_trans]) 1);
qed "lt_trans";

goalw Ordinal.thy [lt_def] "!!i j. [| i<j;  j<i |] ==> P";
by (REPEAT (eresolve_tac [asm_rl, conjE, mem_asym] 1));
qed "lt_asym";

qed_goal "lt_irrefl" Ordinal.thy "i<i ==> P"
 (fn [major]=> [ (rtac (major RS (major RS lt_asym)) 1) ]);

qed_goal "lt_not_refl" Ordinal.thy "~ i<i"
 (fn _=> [ (rtac notI 1), (etac lt_irrefl 1) ]);

AddSEs [lt_irrefl, lt0E];

(** le is less than or equals;  recall  i le j  abbrevs  i<succ(j) !! **)

goalw Ordinal.thy [lt_def] "i le j <-> i<j | (i=j & Ord(j))";
by (blast_tac (claset() addSIs [Ord_succ] addSDs [Ord_succD]) 1);
qed "le_iff";

(*Equivalently, i<j ==> i < succ(j)*)
goal Ordinal.thy "!!i j. i<j ==> i le j";
by (asm_simp_tac (simpset() addsimps [le_iff]) 1);
qed "leI";

goal Ordinal.thy "!!i. [| i=j;  Ord(j) |] ==> i le j";
by (asm_simp_tac (simpset() addsimps [le_iff]) 1);
qed "le_eqI";

val le_refl = refl RS le_eqI;

val [prem] = goal Ordinal.thy "(~ (i=j & Ord(j)) ==> i<j) ==> i le j";
by (rtac (disjCI RS (le_iff RS iffD2)) 1);
by (etac prem 1);
qed "leCI";

val major::prems = goal Ordinal.thy
    "[| i le j;  i<j ==> P;  [| i=j;  Ord(j) |] ==> P |] ==> P";
by (rtac (major RS (le_iff RS iffD1 RS disjE)) 1);
by (DEPTH_SOLVE (ares_tac prems 1 ORELSE etac conjE 1));
qed "leE";

goal Ordinal.thy "!!i j. [| i le j;  j le i |] ==> i=j";
by (asm_full_simp_tac (simpset() addsimps [le_iff]) 1);
by (blast_tac (claset() addEs [lt_asym]) 1);
qed "le_anti_sym";

goal Ordinal.thy "i le 0 <-> i=0";
by (blast_tac (claset() addSIs [Ord_0 RS le_refl] addSEs [leE]) 1);
qed "le0_iff";

bind_thm ("le0D", le0_iff RS iffD1);

AddIs [le_refl];
AddSDs [le0D];
Addsimps [le0_iff];

(*blast_tac will NOT see lt_asym*)
val le_cs = claset() addSIs [leCI] addSEs [leE] addEs [lt_asym];


(*** Natural Deduction rules for Memrel ***)

goalw Ordinal.thy [Memrel_def] "<a,b> : Memrel(A) <-> a:b & a:A & b:A";
by (Blast_tac 1);
qed "Memrel_iff";

goal Ordinal.thy "!!A. [| a: b;  a: A;  b: A |] ==> <a,b> : Memrel(A)";
by (REPEAT (ares_tac [conjI, Memrel_iff RS iffD2] 1));
qed "MemrelI";

val [major,minor] = goal Ordinal.thy
    "[| <a,b> : Memrel(A);  \
\       [| a: A;  b: A;  a:b |]  ==> P \
\    |]  ==> P";
by (rtac (major RS (Memrel_iff RS iffD1) RS conjE) 1);
by (etac conjE 1);
by (rtac minor 1);
by (REPEAT (assume_tac 1));
qed "MemrelE";

AddSIs [MemrelI];
AddSEs [MemrelE];

goalw Ordinal.thy [Memrel_def] "Memrel(A) <= A*A";
by (Blast_tac 1);
qed "Memrel_type";

goalw Ordinal.thy [Memrel_def] "!!A B. A<=B ==> Memrel(A) <= Memrel(B)";
by (Blast_tac 1);
qed "Memrel_mono";

goalw Ordinal.thy [Memrel_def] "Memrel(0) = 0";
by (Blast_tac 1);
qed "Memrel_0";

goalw Ordinal.thy [Memrel_def] "Memrel(1) = 0";
by (Blast_tac 1);
qed "Memrel_1";

Addsimps [Memrel_0, Memrel_1];

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
qed "wf_Memrel";

(*Transset(i) does not suffice, though ALL j:i.Transset(j) does*)
goalw Ordinal.thy [Ord_def, Transset_def, trans_def]
    "!!i. Ord(i) ==> trans(Memrel(i))";
by (Blast_tac 1);
qed "trans_Memrel";

(*If Transset(A) then Memrel(A) internalizes the membership relation below A*)
goalw Ordinal.thy [Transset_def]
    "!!A. Transset(A) ==> <a,b> : Memrel(A) <-> a:b & b:A";
by (Blast_tac 1);
qed "Transset_Memrel_iff";


(*** Transfinite induction ***)

(*Epsilon induction over a transitive set*)
val major::prems = goalw Ordinal.thy [Transset_def]
    "[| i: k;  Transset(k);                          \
\       !!x.[| x: k;  ALL y:x. P(y) |] ==> P(x) \
\    |]  ==>  P(i)";
by (rtac (major RS (wf_Memrel RS wf_induct2)) 1);
by (Blast_tac 1);
by (resolve_tac prems 1);
by (assume_tac 1);
by (cut_facts_tac prems 1);
by (Blast_tac 1);
qed "Transset_induct";

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
qed "trans_induct";

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
by (DEPTH_SOLVE (Step_tac 1 ORELSE Ord_trans_tac 1));
qed_spec_mp "Ord_linear";

(*The trichotomy law for ordinals!*)
val ordi::ordj::prems = goalw Ordinal.thy [lt_def]
    "[| Ord(i);  Ord(j);  i<j ==> P;  i=j ==> P;  j<i ==> P |] ==> P";
by (rtac ([ordi,ordj] MRS Ord_linear RS disjE) 1);
by (etac disjE 2);
by (DEPTH_SOLVE (ares_tac ([ordi,ordj,conjI] @ prems) 1));
qed "Ord_linear_lt";

val prems = goal Ordinal.thy
    "[| Ord(i);  Ord(j);  i<j ==> P;  j le i ==> P |]  ==> P";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear_lt 1);
by (DEPTH_SOLVE (ares_tac ([leI, sym RS le_eqI] @ prems) 1));
qed "Ord_linear2";

val prems = goal Ordinal.thy
    "[| Ord(i);  Ord(j);  i le j ==> P;  j le i ==> P |]  ==> P";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear_lt 1);
by (DEPTH_SOLVE (ares_tac ([leI,le_eqI] @ prems) 1));
qed "Ord_linear_le";

goal Ordinal.thy "!!i j. j le i ==> ~ i<j";
by (blast_tac le_cs 1);
qed "le_imp_not_lt";

goal Ordinal.thy "!!i j. [| ~ i<j;  Ord(i);  Ord(j) |] ==> j le i";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear2 1);
by (REPEAT (SOMEGOAL assume_tac));
by (blast_tac le_cs 1);
qed "not_lt_imp_le";

(** Some rewrite rules for <, le **)

goalw Ordinal.thy [lt_def] "!!i j. Ord(j) ==> i:j <-> i<j";
by (Blast_tac 1);
qed "Ord_mem_iff_lt";

goal Ordinal.thy "!!i j. [| Ord(i);  Ord(j) |] ==> ~ i<j <-> j le i";
by (REPEAT (ares_tac [iffI, le_imp_not_lt, not_lt_imp_le] 1));
qed "not_lt_iff_le";

goal Ordinal.thy "!!i j. [| Ord(i);  Ord(j) |] ==> ~ i le j <-> j<i";
by (asm_simp_tac (simpset() addsimps [not_lt_iff_le RS iff_sym]) 1);
qed "not_le_iff_lt";

(*This is identical to 0<succ(i) *)
goal Ordinal.thy "!!i. Ord(i) ==> 0 le i";
by (etac (not_lt_iff_le RS iffD1) 1);
by (REPEAT (resolve_tac [Ord_0, not_lt0] 1));
qed "Ord_0_le";

goal Ordinal.thy "!!i. [| Ord(i);  i~=0 |] ==> 0<i";
by (etac (not_le_iff_lt RS iffD1) 1);
by (rtac Ord_0 1);
by (Blast_tac 1);
qed "Ord_0_lt";

(*** Results about less-than or equals ***)

(** For ordinals, j<=i (subset) implies j le i (less-than or equals) **)

goal Ordinal.thy "!!i j. [| j<=i;  Ord(i);  Ord(j) |] ==> j le i";
by (rtac (not_lt_iff_le RS iffD1) 1);
by (assume_tac 1);
by (assume_tac 1);
by (blast_tac (claset() addEs [ltE, mem_irrefl]) 1);
qed "subset_imp_le";

goal Ordinal.thy "!!i j. i le j ==> i<=j";
by (etac leE 1);
by (Blast_tac 2);
by (blast_tac (subset_cs addIs [OrdmemD] addEs [ltE]) 1);
qed "le_imp_subset";

goal Ordinal.thy "j le i <-> j<=i & Ord(i) & Ord(j)";
by (blast_tac (claset() addDs [Ord_succD, subset_imp_le, le_imp_subset]
                       addEs [ltE]) 1);
qed "le_subset_iff";

goal Ordinal.thy "i le succ(j) <-> i le j | i=succ(j) & Ord(i)";
by (simp_tac (simpset() addsimps [le_iff]) 1);
by (blast_tac (claset() addIs [Ord_succ] addDs [Ord_succD]) 1);
qed "le_succ_iff";

(*Just a variant of subset_imp_le*)
val [ordi,ordj,minor] = goal Ordinal.thy
    "[| Ord(i);  Ord(j);  !!x. x<j ==> x<i |] ==> j le i";
by (REPEAT_FIRST (ares_tac [notI RS not_lt_imp_le, ordi, ordj]));
by (etac (minor RS lt_irrefl) 1);
qed "all_lt_imp_le";

(** Transitive laws **)

goal Ordinal.thy "!!i j. [| i le j;  j<k |] ==> i<k";
by (blast_tac (claset() addSEs [leE] addIs [lt_trans]) 1);
qed "lt_trans1";

goal Ordinal.thy "!!i j. [| i<j;  j le k |] ==> i<k";
by (blast_tac (claset() addSEs [leE] addIs [lt_trans]) 1);
qed "lt_trans2";

goal Ordinal.thy "!!i j. [| i le j;  j le k |] ==> i le k";
by (REPEAT (ares_tac [lt_trans1] 1));
qed "le_trans";

goal Ordinal.thy "!!i j. i<j ==> succ(i) le j";
by (rtac (not_lt_iff_le RS iffD1) 1);
by (blast_tac le_cs 3);
by (ALLGOALS (blast_tac (claset() addEs [ltE])));
qed "succ_leI";

(*Identical to  succ(i) < succ(j) ==> i<j  *)
goal Ordinal.thy "!!i j. succ(i) le j ==> i<j";
by (rtac (not_le_iff_lt RS iffD1) 1);
by (fast_tac le_cs 3);
by (ALLGOALS (blast_tac (claset() addEs [ltE, make_elim Ord_succD])));
qed "succ_leE";

goal Ordinal.thy "succ(i) le j <-> i<j";
by (REPEAT (ares_tac [iffI,succ_leI,succ_leE] 1));
qed "succ_le_iff";

Addsimps [succ_le_iff];

goal Ordinal.thy "!!i j. succ(i) le succ(j) ==> i le j";
by (blast_tac (claset() addSDs [succ_leE]) 1);
qed "succ_le_imp_le";

(** Union and Intersection **)

goal Ordinal.thy "!!i j. [| Ord(i); Ord(j) |] ==> i le i Un j";
by (rtac (Un_upper1 RS subset_imp_le) 1);
by (REPEAT (ares_tac [Ord_Un] 1));
qed "Un_upper1_le";

goal Ordinal.thy "!!i j. [| Ord(i); Ord(j) |] ==> j le i Un j";
by (rtac (Un_upper2 RS subset_imp_le) 1);
by (REPEAT (ares_tac [Ord_Un] 1));
qed "Un_upper2_le";

(*Replacing k by succ(k') yields the similar rule for le!*)
goal Ordinal.thy "!!i j k. [| i<k;  j<k |] ==> i Un j < k";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear_le 1);
by (stac Un_commute 4);
by (asm_full_simp_tac (simpset() addsimps [le_subset_iff, subset_Un_iff]) 4);
by (asm_full_simp_tac (simpset() addsimps [le_subset_iff, subset_Un_iff]) 3);
by (REPEAT (eresolve_tac [asm_rl, ltE] 1));
qed "Un_least_lt";

goal Ordinal.thy "!!i j. [| Ord(i); Ord(j) |] ==> i Un j < k  <->  i<k & j<k";
by (safe_tac (claset() addSIs [Un_least_lt]));
by (rtac (Un_upper2_le RS lt_trans1) 2);
by (rtac (Un_upper1_le RS lt_trans1) 1);
by (REPEAT_SOME assume_tac);
qed "Un_least_lt_iff";

val [ordi,ordj,ordk] = goal Ordinal.thy
    "[| Ord(i); Ord(j); Ord(k) |] ==> i Un j : k  <->  i:k & j:k";
by (cut_facts_tac [[ordi,ordj] MRS 
                   read_instantiate [("k","k")] Un_least_lt_iff] 1);
by (asm_full_simp_tac (simpset() addsimps [lt_def,ordi,ordj,ordk]) 1);
qed "Un_least_mem_iff";

(*Replacing k by succ(k') yields the similar rule for le!*)
goal Ordinal.thy "!!i j k. [| i<k;  j<k |] ==> i Int j < k";
by (res_inst_tac [("i","i"),("j","j")] Ord_linear_le 1);
by (stac Int_commute 4);
by (asm_full_simp_tac (simpset() addsimps [le_subset_iff, subset_Int_iff]) 4);
by (asm_full_simp_tac (simpset() addsimps [le_subset_iff, subset_Int_iff]) 3);
by (REPEAT (eresolve_tac [asm_rl, ltE] 1));
qed "Int_greatest_lt";

(*FIXME: the Intersection duals are missing!*)


(*** Results about limits ***)

val prems = goal Ordinal.thy "[| !!i. i:A ==> Ord(i) |] ==> Ord(Union(A))";
by (rtac (Ord_is_Transset RS Transset_Union_family RS OrdI) 1);
by (REPEAT (etac UnionE 1 ORELSE ares_tac ([Ord_contains_Transset]@prems) 1));
qed "Ord_Union";

val prems = goal Ordinal.thy
    "[| !!x. x:A ==> Ord(B(x)) |] ==> Ord(UN x:A. B(x))";
by (rtac Ord_Union 1);
by (etac RepFunE 1);
by (etac ssubst 1);
by (eresolve_tac prems 1);
qed "Ord_UN";

(* No < version; consider (UN i:nat.i)=nat *)
val [ordi,limit] = goal Ordinal.thy
    "[| Ord(i);  !!x. x:A ==> b(x) le i |] ==> (UN x:A. b(x)) le i";
by (rtac (le_imp_subset RS UN_least RS subset_imp_le) 1);
by (REPEAT (ares_tac [ordi, Ord_UN, limit] 1 ORELSE etac (limit RS ltE) 1));
qed "UN_least_le";

val [jlti,limit] = goal Ordinal.thy
    "[| j<i;  !!x. x:A ==> b(x)<j |] ==> (UN x:A. succ(b(x))) < i";
by (rtac (jlti RS ltE) 1);
by (rtac (UN_least_le RS lt_trans2) 1);
by (REPEAT (ares_tac [jlti, succ_leI, limit] 1));
qed "UN_succ_least_lt";

val prems = goal Ordinal.thy
    "[| a: A;  i le b(a);  !!x. x:A ==> Ord(b(x)) |] ==> i le (UN x:A. b(x))";
by (resolve_tac (prems RL [ltE]) 1);
by (rtac (le_imp_subset RS subset_trans RS subset_imp_le) 1);
by (REPEAT (ares_tac (prems @ [UN_upper, Ord_UN]) 1));
qed "UN_upper_le";

val [leprem] = goal Ordinal.thy
    "[| !!x. x:A ==> c(x) le d(x) |] ==> (UN x:A. c(x)) le (UN x:A. d(x))";
by (rtac UN_least_le 1);
by (rtac UN_upper_le 2);
by (REPEAT (ares_tac [leprem] 2));
by (rtac Ord_UN 1);
by (REPEAT (eresolve_tac [asm_rl, leprem RS ltE] 1
     ORELSE dtac Ord_succD 1));
qed "le_implies_UN_le_UN";

goal Ordinal.thy "!!i. Ord(i) ==> (UN y:i. succ(y)) = i";
by (blast_tac (claset() addIs [Ord_trans]) 1);
qed "Ord_equality";

(*Holds for all transitive sets, not just ordinals*)
goal Ordinal.thy "!!i. Ord(i) ==> Union(i) <= i";
by (blast_tac (claset() addIs [Ord_trans]) 1);
qed "Ord_Union_subset";


(*** Limit ordinals -- general properties ***)

goalw Ordinal.thy [Limit_def] "!!i. Limit(i) ==> Union(i) = i";
by (fast_tac (claset() addSIs [ltI] addSEs [ltE] addEs [Ord_trans]) 1);
qed "Limit_Union_eq";

goalw Ordinal.thy [Limit_def] "!!i. Limit(i) ==> Ord(i)";
by (etac conjunct1 1);
qed "Limit_is_Ord";

goalw Ordinal.thy [Limit_def] "!!i. Limit(i) ==> 0 < i";
by (etac (conjunct2 RS conjunct1) 1);
qed "Limit_has_0";

goalw Ordinal.thy [Limit_def] "!!i. [| Limit(i);  j<i |] ==> succ(j) < i";
by (Blast_tac 1);
qed "Limit_has_succ";

goalw Ordinal.thy [Limit_def]
    "!!i. [| 0<i;  ALL y. succ(y) ~= i |] ==> Limit(i)";
by (safe_tac subset_cs);
by (rtac (not_le_iff_lt RS iffD1) 2);
by (blast_tac le_cs 4);
by (REPEAT (eresolve_tac [asm_rl, ltE, Ord_succ] 1));
qed "non_succ_LimitI";

goal Ordinal.thy "!!i. Limit(succ(i)) ==> P";
by (rtac lt_irrefl 1);
by (rtac Limit_has_succ 1);
by (assume_tac 1);
by (etac (Limit_is_Ord RS Ord_succD RS le_refl) 1);
qed "succ_LimitE";

goal Ordinal.thy "!!i. [| Limit(i);  i le succ(j) |] ==> i le j";
by (safe_tac (claset() addSEs [succ_LimitE, leE]));
qed "Limit_le_succD";

(** Traditional 3-way case analysis on ordinals **)

goal Ordinal.thy "!!i. Ord(i) ==> i=0 | (EX j. Ord(j) & i=succ(j)) | Limit(i)";
by (blast_tac (claset() addSIs [non_succ_LimitI, Ord_0_lt]
                      addSDs [Ord_succD]) 1);
qed "Ord_cases_disj";

val major::prems = goal Ordinal.thy
    "[| Ord(i);                 \
\       i=0                          ==> P;     \
\       !!j. [| Ord(j); i=succ(j) |] ==> P;     \
\       Limit(i)                     ==> P      \
\    |] ==> P";
by (cut_facts_tac [major RS Ord_cases_disj] 1);
by (REPEAT (eresolve_tac (prems@[asm_rl, disjE, exE, conjE]) 1));
qed "Ord_cases";

val major::prems = goal Ordinal.thy
     "[| Ord(i);                \
\        P(0);                  \
\        !!x. [| Ord(x);  P(x) |] ==> P(succ(x));       \
\        !!x. [| Limit(x);  ALL y:x. P(y) |] ==> P(x)   \
\     |] ==> P(i)";
by (resolve_tac [major RS trans_induct] 1);
by (etac Ord_cases 1);
by (ALLGOALS (blast_tac (claset() addIs prems)));
qed "trans_induct3";
