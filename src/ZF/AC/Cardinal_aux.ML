(*  Title: 	ZF/AC/Cardinal_aux.ML
    ID:         $Id$
    Author: 	Krzysztof Grabczewski

Auxiliary lemmas concerning cardinalities
*)

open Cardinal_aux;

(* ********************************************************************** *)
(* Lemmas involving ordinals and cardinalities used in the proofs 	  *)
(* concerning AC16 and DC						  *)
(* ********************************************************************** *)

val nat_0_in_2 =  Ord_0 RS le_refl RS leI RS ltD;

goalw thy [InfCard_def] "!!i. [| ~Finite(i); Ord(i) |] ==> InfCard(|i|)";
by (rtac conjI 1);
by (rtac Card_cardinal 1);
by (resolve_tac [Card_nat RS (Card_def RS def_imp_iff RS iffD1 RS ssubst)] 1);
by (resolve_tac [nat_le_infinite_Ord RS le_imp_lepoll
	RSN (2, well_ord_Memrel RS well_ord_lepoll_imp_Card_le)] 1 
    THEN REPEAT (assume_tac 1));
val Inf_Ord_imp_InfCard_cardinal = result();

goalw thy [lepoll_def] "A Un B lepoll A+B";
by (res_inst_tac [("x","lam x: A Un B. if (x:A,Inl(x),Inr(x))")] exI 1);
by (res_inst_tac [("d","%z. snd(z)")] lam_injective 1);
by (split_tac [expand_if] 1);
by (fast_tac (AC_cs addSIs [InlI, InrI]) 1);
by (split_tac [expand_if] 1);
by (asm_full_simp_tac (AC_ss addsimps [Inl_def, Inr_def]) 1);
val Un_lepoll_sum = result();

goalw thy [sum_def] "A+A = 2*A";
by (fast_tac (AC_cs addIs [equalityI]
	addSIs [singletonI, nat_0_in_2, succI1]
	addSEs [succE, singletonE]) 1);
val sum_eq_2_times = result();

val sum_lepoll_prod = [sum_eq_2_times RS equalityD1 RS subset_imp_lepoll,
	asm_rl, lepoll_refl] MRS (prod_lepoll_mono RSN (2, lepoll_trans))
	|> standard;

goal thy "!!A. [| A lepoll B; 2 lepoll A |] ==> A+B lepoll A*B";
by (REPEAT (ares_tac [[sum_lepoll_mono, sum_lepoll_prod]
		MRS lepoll_trans, lepoll_refl] 1));
val lepoll_imp_sum_lepoll_prod = result();

goal thy "!!A. [| A eqpoll i; B eqpoll i; ~Finite(i); Ord(i) |]  \
\		==> A Un B eqpoll i";
by (rtac eqpollI 1);
by (eresolve_tac [subset_imp_lepoll RSN (2, eqpoll_sym RS eqpoll_imp_lepoll
	RS  lepoll_trans)] 2);
by (fast_tac AC_cs 2);
by (resolve_tac [Un_lepoll_sum RS lepoll_trans] 1);
by (resolve_tac [lepoll_imp_sum_lepoll_prod RS lepoll_trans] 1);
by (eresolve_tac [eqpoll_sym RSN (2, eqpoll_trans) RS eqpoll_imp_lepoll] 1
	THEN (assume_tac 1));
by (resolve_tac [nat_le_infinite_Ord RS le_imp_lepoll RS 
	(Ord_nat RS (nat_2I RS OrdmemD) RS subset_imp_lepoll RS lepoll_trans)
	RS (eqpoll_sym RS eqpoll_imp_lepoll RSN (2, lepoll_trans))] 1 
    THEN (REPEAT (assume_tac 1)));
by (eresolve_tac [prod_eqpoll_cong RS eqpoll_imp_lepoll RS lepoll_trans] 1 
    THEN (assume_tac 1));
by (resolve_tac [Inf_Ord_imp_InfCard_cardinal RSN (2, well_ord_Memrel RS 
	well_ord_InfCard_square_eq) RS eqpoll_imp_lepoll] 1 
    THEN REPEAT (assume_tac 1));
val Un_eqpoll_Inf_Ord = result();

goalw thy [lepoll_def] "!!A. [| A lepoll B; C lepoll D; B Int D = 0 |]  \
\			==> A Un C lepoll B Un D";
by (REPEAT (etac exE 1));
by (res_inst_tac [("x","lam a: A Un C. if(a:A, f`a, fa`a)")] exI 1);
by (res_inst_tac [("d","%z. if(z:B, converse(f)`z, converse(fa)`z)")]
	lam_injective 1);
by (split_tac [expand_if] 1);
by (etac UnE 1);
by (fast_tac (AC_cs addSEs [inj_is_fun RS apply_type]) 1);
by (rtac conjI 1);
by (fast_tac (AC_cs addSEs [inj_is_fun RS apply_type]) 1);
by (fast_tac (AC_cs addSEs [inj_is_fun RS apply_type] addSIs [UnI2]) 1);
by (REPEAT (split_tac [expand_if] 1));
by (rtac conjI 1);
by (fast_tac (AC_cs addSEs [left_inverse, inj_is_fun RS apply_type]
	addEs [swap]) 1);
by (rtac impI 1);
by (etac UnE 1);
by (contr_tac 1);
by (rtac conjI 1);
by (rtac impI 1);
by (etac equals0D 1);
by (fast_tac (AC_cs addSEs [inj_is_fun RS apply_type]) 1);
by (fast_tac (AC_cs addSEs [left_inverse]) 1);
val Un_lepoll_Un = result();

goal ZF.thy "{x, y} - {y} = {x} - {y}";
by (fast_tac eq_cs 1);
val double_Diff_sing = result();

goal ZF.thy "if({y,z}-{z}=0, z, THE w. {y,z}-{z}={w}) = y";
by (split_tac [expand_if] 1);
by (asm_full_simp_tac (ZF_ss addsimps [double_Diff_sing, Diff_eq_0_iff]) 1);
by (fast_tac (ZF_cs addSIs [the_equality, equalityI, equals0I]
		addEs [equalityE] addSEs [singletonE]) 1);
val paired_bij_lemma = result();

goal thy "(lam y:{{y,z}. y:x}. if(y-{z}=0, z, THE w. y-{z}={w}))  \
\		: bij({{y,z}. y:x}, x)";
by (res_inst_tac [("d","%a. {a,z}")] lam_bijective 1);
by (TRYALL (fast_tac (AC_cs addSEs [RepFunE] addSIs [RepFunI] 
		addss (AC_ss addsimps [paired_bij_lemma]))));
val paired_bij = result();

goalw thy [eqpoll_def] "{{y,z}. y:x} eqpoll x";
by (fast_tac (AC_cs addSIs [paired_bij]) 1);
val paired_eqpoll = result();

goal thy "!!A. EX B. B eqpoll A & B Int C = 0";
by (fast_tac (AC_cs addSIs [paired_eqpoll, equals0I] addEs [mem_asym]) 1);
val ex_eqpoll_disjoint = result();

goal thy "!!A. [| A lepoll i; B lepoll i; ~Finite(i); Ord(i) |]  \
\		==> A Un B lepoll i";
by (res_inst_tac [("A1","i"), ("C1","i")] (ex_eqpoll_disjoint RS exE) 1);
by (etac conjE 1);
by (dresolve_tac [eqpoll_sym RS eqpoll_imp_lepoll RSN (2, lepoll_trans)] 1);
by (assume_tac 1);
by (resolve_tac [Un_lepoll_Un RS lepoll_trans] 1 THEN (REPEAT (assume_tac 1)));
by (eresolve_tac [eqpoll_refl RSN (2, Un_eqpoll_Inf_Ord) RS
	eqpoll_imp_lepoll] 1
	THEN (REPEAT (assume_tac 1)));
val Un_lepoll_Inf_Ord = result();

goal thy "!!P. [| P(i); i:j; Ord(j) |] ==> (LEAST i. P(i)) : j";
by (eresolve_tac [Least_le RS leE] 1);
by (etac Ord_in_Ord 1 THEN (assume_tac 1));
by (etac ltE 1);
by (fast_tac (AC_cs addDs [OrdmemD]) 1);
by (etac subst_elem 1 THEN (assume_tac 1));
val Least_in_Ord = result();

goal thy "!!x. [| well_ord(x,r); y<=x; y lepoll succ(n); n:nat |]  \
\	==> y-{THE b. first(b,y,r)} lepoll n";
by (res_inst_tac [("Q","y=0")] (excluded_middle RS disjE) 1);
by (fast_tac (AC_cs addSIs [Diff_sing_lepoll, the_first_in]) 1);
by (res_inst_tac [("b","y-{THE b. first(b, y, r)}")] subst 1);
by (rtac empty_lepollI 2);
by (fast_tac (AC_cs addSIs [equalityI]) 1);
val Diff_first_lepoll = result();

goal thy "(UN x:X. P(x)) <= (UN x:X. P(x)-Q(x)) Un (UN x:X. Q(x))";
by (fast_tac AC_cs 1);
val UN_subset_split = result();

goalw thy [lepoll_def] "!!a. Ord(a) ==> (UN x:a. {P(x)}) lepoll a";
by (res_inst_tac [("x","lam z:(UN x:a. {P(x)}). (LEAST i. P(i)=z)")] exI 1);
by (res_inst_tac [("d","%z. P(z)")] lam_injective 1);
by (fast_tac (AC_cs addSIs [Least_in_Ord]) 1);
by (fast_tac (AC_cs addIs [LeastI] addSEs [singletonE, Ord_in_Ord]) 1);
val UN_sing_lepoll = result();

goal thy "!!a T. [| well_ord(T, R); ~Finite(a); Ord(a); n:nat |] ==>  \
\	ALL f. (ALL b:a. f`b lepoll n & f`b <= T) --> (UN b:a. f`b) lepoll a";
by (etac nat_induct 1);
by (rtac allI 1);
by (rtac impI 1);
by (res_inst_tac [("b","UN b:a. f`b")] subst 1);
by (rtac empty_lepollI 2);
by (resolve_tac [equals0I RS sym] 1);
by (REPEAT (eresolve_tac [UN_E, allE] 1));
by (fast_tac (AC_cs addDs [lepoll_0_is_0 RS subst]) 1);
by (rtac allI 1);
by (rtac impI 1);
by (eres_inst_tac [("x","lam x:a. f`x - {THE b. first(b,f`x,R)}")] allE 1);
by (etac impE 1);
by (asm_full_simp_tac AC_ss 1);
by (fast_tac (AC_cs addSIs [Diff_first_lepoll]) 1);
by (asm_full_simp_tac AC_ss 1);
by (resolve_tac [UN_subset_split RS subset_imp_lepoll RS lepoll_trans] 1);
by (rtac Un_lepoll_Inf_Ord 1 THEN (REPEAT_FIRST assume_tac));
by (etac UN_sing_lepoll 1);
val UN_fun_lepoll_lemma = result();

goal thy "!!a f. [| ALL b:a. f`b lepoll n & f`b <= T; well_ord(T, R);  \
\	~Finite(a); Ord(a); n:nat |] ==> (UN b:a. f`b) lepoll a";
by (eresolve_tac [UN_fun_lepoll_lemma RS allE] 1 THEN (REPEAT (assume_tac 1)));
by (fast_tac AC_cs 1);
val UN_fun_lepoll = result();

goal thy "!!a f. [| ALL b:a. F(b) lepoll n & F(b) <= T; well_ord(T, R);  \
\	~Finite(a); Ord(a); n:nat |] ==> (UN b:a. F(b)) lepoll a";
by (rtac impE 1 THEN (assume_tac 3));
by (res_inst_tac [("f","lam b:a. F(b)")] (UN_fun_lepoll) 2 
	THEN (TRYALL assume_tac));
by (simp_tac AC_ss 2);
by (asm_full_simp_tac AC_ss 1);
val UN_lepoll = result();

goal thy "!!a. Ord(a) ==> (UN b:a. F(b)) = (UN b:a. F(b) - (UN c:b. F(c)))";
by (rtac equalityI 1);
by (fast_tac AC_cs 2);
by (rtac subsetI 1);
by (etac UN_E 1);
by (rtac UN_I 1);
by (res_inst_tac [("P","%z. x:F(z)")] Least_in_Ord 1 THEN (REPEAT (assume_tac 1)));
by (rtac DiffI 1);
by (resolve_tac [Ord_in_Ord RSN (2, LeastI)] 1 THEN (REPEAT (assume_tac 1)));
by (rtac notI 1);
by (etac UN_E 1);
by (eres_inst_tac [("P","%z. x:F(z)"),("i","c")] less_LeastE 1);
by (eresolve_tac [Ord_Least RSN (2, ltI)] 1);
val UN_eq_UN_Diffs = result();

goalw thy [eqpoll_def] "!!A B. A Int B = 0 ==> A Un B eqpoll A + B";
by (res_inst_tac [("x","lam a:A Un B. if(a:A,Inl(a),Inr(a))")] exI 1);
by (res_inst_tac [("d","%z. case(%x.x, %x.x, z)")] lam_bijective 1);
by (fast_tac (AC_cs addSIs [if_type, InlI, InrI]) 1);
by (TRYALL (etac sumE ));
by (TRYALL (split_tac [expand_if]));
by (TRYALL (asm_simp_tac sum_ss));
by (fast_tac (AC_cs addDs [equals0D]) 1);
val disj_Un_eqpoll_sum = result();

goalw thy [lepoll_def, eqpoll_def]
	"!!X a. a lepoll X ==> EX Y. Y<=X & a eqpoll Y";
by (etac exE 1);
by (forward_tac [subset_refl RSN (2, restrict_bij)] 1);
by (res_inst_tac [("x","f``a")] exI 1);
by (fast_tac (AC_cs addSEs [inj_is_fun RS fun_is_rel RS image_subset]) 1);
val lepoll_imp_eqpoll_subset = result();

(* ********************************************************************** *)
(* Some other lemmas							  *)
(* ********************************************************************** *)

goal thy "!!m n. [| m:nat; n:nat |] ==> m + n eqpoll m #+ n";
by (rtac eqpoll_trans 1);
by (eresolve_tac [nat_implies_well_ord RS (
                  nat_implies_well_ord RSN (2,
                  well_ord_radd RS well_ord_cardinal_eqpoll)) RS eqpoll_sym] 1 
    THEN (assume_tac 1));
by (eresolve_tac [nat_cadd_eq_add RS subst] 1 THEN (assume_tac 1));
by (asm_full_simp_tac (AC_ss addsimps [cadd_def, eqpoll_refl]) 1);
val nat_sum_eqpoll_sum = result();

val eqpoll_ordertype =
	ordermap_bij RS (exI RS (eqpoll_def RS (def_imp_iff RS iffD2)));

goalw thy [lesspoll_def]
	"!!a. [| b lesspoll a; well_ord(a,r); well_ord(b,s) |]  \
\		==> ordertype(b,s) < ordertype(a,r)";
by (forw_inst_tac [("A2","b")]
	([Ord_ordertype, Ord_ordertype] MRS Ord_linear) 1
	THEN REPEAT (assume_tac 1));
by (etac disjE 1);
by (etac ltI 1);
by (etac Ord_ordertype 1);
by (etac disjE 1);
by (REPEAT (eresolve_tac [conjE,notE] 1));
by (resolve_tac [exI RS (eqpoll_def RS (def_imp_iff RS iffD2))] 1);
by (eresolve_tac [ordermap_bij RS comp_bij] 1);
by (etac ssubst 1);
by (eresolve_tac [ordermap_bij RS bij_converse_bij] 1);
by (REPEAT (eresolve_tac [conjE,notE] 1));
by (etac eqpollI 1);
by (resolve_tac [Ord_ordertype RSN (2, OrdmemD RS subset_imp_lepoll) RSN (2, 
                 eqpoll_ordertype RS eqpoll_imp_lepoll RS (
                 eqpoll_ordertype RS eqpoll_sym RS eqpoll_imp_lepoll RSN (3, 
                 lepoll_trans RS lepoll_trans)))] 1 
    THEN (REPEAT (assume_tac 1)));
val lesspoll_ordertype_lt = result();

goalw thy [lesspoll_def] "!!A. A lesspoll B ==> A lepoll B";
by (fast_tac AC_cs 1);
val lesspoll_imp_lepoll = result();

goalw thy [lepoll_def]
	"!!A. [| A lepoll B; well_ord(B,r) |] ==> EX s. well_ord(A,s)";
by (fast_tac (AC_cs addSEs [well_ord_rvimage]) 1);
val lepoll_well_ord = result();

goal thy "!!A a. [| A lesspoll a; Ord(a) |] ==> EX b. b<a & A eqpoll b";
by (resolve_tac [well_ord_Memrel RSN (2,
	lesspoll_imp_lepoll RS lepoll_well_ord) RS exE] 1
	THEN (REPEAT (assume_tac 1)));
by (dresolve_tac [well_ord_Memrel RSN (2, lesspoll_ordertype_lt)] 1
	THEN (REPEAT (assume_tac 1)));
by (fast_tac (AC_cs addSEs [eqpoll_ordertype]
		addEs [ordertype_Memrel RS subst]) 1);
val lesspoll_imp_ex_lt_eqpoll = result();

goalw thy [lesspoll_def] "A lepoll B <-> A lesspoll B | A eqpoll B";
by (fast_tac (AC_cs addSIs [eqpollI] addSEs [eqpollE]) 1);
val lepoll_iff_leqpoll = result();

goal thy "!!A. [| A lepoll a; Ord(a) |] ==> EX b. b le a & A eqpoll b";
by (eresolve_tac [lepoll_iff_leqpoll RS iffD1 RS disjE] 1);
by (fast_tac (AC_cs addSDs [lesspoll_imp_ex_lt_eqpoll] addSIs [leI]) 1);
by (fast_tac (AC_cs addSIs [le_refl]) 1);
val lepoll_imp_ex_le_eqpoll = result();

goal thy "!!m. [| m le n; n:nat |] ==> m:nat";
by (fast_tac (AC_cs addSDs [nat_succI RS (Ord_nat RSN (2, OrdmemD))]
	addSEs [ltE]) 1);
val le_in_nat = result();

goalw thy [Finite_def] "!!A. [| Finite(A); Finite(B) |] ==> Finite(A Un B)";
by (REPEAT (etac bexE 1));
by (REPEAT (dtac eqpoll_imp_lepoll 1));
by (dtac sum_lepoll_mono 1 THEN (assume_tac 1));
by (dresolve_tac [nat_sum_eqpoll_sum RS eqpoll_imp_lepoll RSN (2, 
                  Un_lepoll_sum RS lepoll_trans RS lepoll_trans)] 1 
	THEN (REPEAT (assume_tac 1)));
by (forw_inst_tac [("n2","na")]
	(add_type RS nat_into_Ord RSN (2, lepoll_imp_ex_le_eqpoll)) 1 
	THEN (REPEAT (assume_tac 1)));
by (fast_tac (AC_cs addSEs [add_type RSN (2, le_in_nat)]) 1);
val Finite_Un = result();

goal thy "A <= B Un (A - B)";
by (fast_tac AC_cs 1);
val subset_Un_Diff = result();

goalw thy [lesspoll_def] "!!a. [| Card(a); i<a |] ==> i lesspoll a";
by (dresolve_tac [Card_iff_initial RS iffD1] 1);
by (fast_tac (AC_cs addSEs [leI RS le_imp_lepoll]) 1);
val lt_Card_imp_lesspoll = result();

(* ********************************************************************** *)
(* Diff_lesspoll_eqpoll_Card						  *)
(* ********************************************************************** *)

goal thy "!!A B. [| A eqpoll a; ~Finite(a); Card(a); B lesspoll a;  \
\		A-B lesspoll a |] ==> P";
by (REPEAT (eresolve_tac [lesspoll_imp_ex_lt_eqpoll RS exE,
	Card_is_Ord, conjE] 1));
by (forw_inst_tac [("j","xa")] (lt_Ord RS (lt_Ord RSN (2, Un_upper1_le))) 1
	THEN (assume_tac 1));
by (forw_inst_tac [("j","xa")] (lt_Ord RS (lt_Ord RSN (2, Un_upper2_le))) 1
	THEN (assume_tac 1));
by (dtac Un_least_lt 1 THEN (assume_tac 1));
by (dresolve_tac [le_imp_lepoll RSN
	(2, eqpoll_imp_lepoll RS lepoll_trans)] 1
	THEN (assume_tac 1));
by (dresolve_tac [le_imp_lepoll RSN
	(2, eqpoll_imp_lepoll RS lepoll_trans)] 1
	THEN (assume_tac 1));
by (res_inst_tac [("Q","Finite(x Un xa)")] (excluded_middle RS disjE) 1);
by (dresolve_tac [[lepoll_Finite, lepoll_Finite] MRS Finite_Un] 2
	THEN (REPEAT (assume_tac 2)));
by (dresolve_tac [subset_Un_Diff RS subset_imp_lepoll RS lepoll_Finite] 2);
by (fast_tac (AC_cs
	addDs [eqpoll_sym RS eqpoll_imp_lepoll RS lepoll_Finite]) 2);
by (dresolve_tac [ Un_lepoll_Inf_Ord] 1
	THEN (REPEAT (assume_tac 1)));
by (fast_tac (AC_cs addSEs [ltE, Ord_in_Ord]) 1);
by (dresolve_tac [subset_Un_Diff RS subset_imp_lepoll RS lepoll_trans RSN
	(3, lt_Card_imp_lesspoll RS lepoll_lesspoll_lesspoll)] 1
	THEN (TRYALL assume_tac));
by (fast_tac (AC_cs addSDs [lesspoll_def RS def_imp_iff RS iffD1]) 1);
val Diff_lesspoll_eqpoll_Card_lemma = result();

goal thy "!!A. [| A eqpoll a; ~Finite(a); Card(a); B lesspoll a |]  \
\	==> A - B eqpoll a";
by (rtac swap 1 THEN (fast_tac AC_cs 1));
by (rtac Diff_lesspoll_eqpoll_Card_lemma 1 THEN (REPEAT (assume_tac 1)));
by (fast_tac (AC_cs addSIs [lesspoll_def RS def_imp_iff RS iffD2,
	subset_imp_lepoll RS (eqpoll_imp_lepoll RSN (2, lepoll_trans))]) 1);
val Diff_lesspoll_eqpoll_Card = result();

