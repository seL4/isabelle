(*  Title: 	ZF/AC/WO1_AC.ML
    ID:         $Id$
    Author: 	Krzysztof Gr`abczewski

The proofs of WO1 ==> AC1 and WO1 ==> AC10(n) for n >= 1

The latter proof is referred to as clear by the Rubins.
However it seems to be quite complicated.
The formal proof presented below is a mechanisation of the proof 
by Lawrence C. Paulson which is the following:

Assume WO1.  Let s be a set of infinite sets.
 
Suppose x:s.  Then x is equipollent to |x| (by WO1), an infinite cardinal; 
call it K.  Since K = K |+| K = |K+K| (by InfCard_cdouble_eq) there is an 
isomorphism h: bij(K+K, x).  (Here + means disjoint sum.)
 
So there is a partition of x into 2-element sets, namely
 
        {{h(Inl(i)), h(Inr(i))} . i:K}
 
So for all x:s the desired partition exists.  By AC1 (which follows from WO1) 
there exists a function f that chooses a partition for each x:s.  Therefore we 
have AC10(2).

*)

open WO1_AC;

(* ********************************************************************** *)
(* WO1 ==> AC1								  *)
(* ********************************************************************** *)

goalw thy [AC1_def, WO1_def] "!!Z. WO1 ==> AC1";
by (fast_tac (AC_cs addSEs [ex_choice_fun]) 1);
qed "WO1_AC1";

(* ********************************************************************** *)
(* WO1 ==> AC10(n) (n >= 1)						  *)
(* ********************************************************************** *)

goalw thy [WO1_def] "!!A. [| WO1; ALL B:A. EX C:D(B). P(C,B) |]  \
\		==> EX f. ALL B:A. P(f`B,B)";
by (eres_inst_tac [("x","Union({{C:D(B). P(C,B)}. B:A})")] allE 1);
by (eresolve_tac [exE] 1);
by (dresolve_tac [ex_choice_fun] 1);
by (fast_tac (AC_cs addEs [RepFunE, sym RS equals0D]) 1);
by (eresolve_tac [exE] 1);
by (res_inst_tac [("x","lam x:A. f`{C:D(x). P(C,x)}")] exI 1);
by (asm_full_simp_tac AC_ss 1);
by (fast_tac (AC_cs addSDs [RepFunI RSN (2, apply_type)]
		addSEs [CollectD2]) 1);
val lemma1 = result();

goalw thy [WO1_def] "!!A. [| ~Finite(B); WO1 |] ==> |B| + |B| eqpoll  B";
by (resolve_tac [eqpoll_trans] 1);
by (fast_tac (AC_cs addSEs [well_ord_cardinal_eqpoll]) 2);
by (resolve_tac [eqpoll_sym RS eqpoll_trans] 1);
by (fast_tac (AC_cs addSEs [well_ord_cardinal_eqpoll]) 1);
by (resolve_tac [cadd_def RS def_imp_eq RS subst] 1);
by (resolve_tac [Card_cardinal RSN (2, Inf_Card_is_InfCard) RS 
			InfCard_cdouble_eq RS ssubst] 1);
by (resolve_tac [eqpoll_refl] 2);
by (resolve_tac [notI] 1);
by (eresolve_tac [notE] 1);
by (resolve_tac [eqpoll_sym RS eqpoll_imp_lepoll RS lepoll_Finite] 1
	THEN (assume_tac 2));
by (fast_tac (AC_cs addSEs [well_ord_cardinal_eqpoll]) 1);
val lemma2_1 = result();

goal thy "!!f. f : bij(D+D, B) ==> {{f`Inl(i), f`Inr(i)}. i:D} : Pow(Pow(B))";
by (fast_tac (AC_cs addSIs [InlI, InrI]
		addSEs [RepFunE, bij_is_fun RS apply_type]) 1);
val lemma2_2 = result();

goal thy "!!f. [| f:inj(A,B); f`a = f`b; a:A; b:A |] ==> a=b";
by (resolve_tac [inj_equality] 1);
by (TRYALL (fast_tac (AC_cs addSEs [inj_is_fun RS apply_Pair] addEs [subst])));
val lemma = result();

goalw thy AC_aux_defs
	"!!f. f : bij(D+D, B) ==>  \
\		pairwise_disjoint({{f`Inl(i), f`Inr(i)}. i:D})";
by (fast_tac (AC_cs addSEs [RepFunE, not_emptyE] 
	addDs [bij_is_inj RS lemma, Inl_iff RS iffD1,
		Inr_iff RS iffD1, Inl_Inr_iff RS iffD1 RS FalseE,
		Inr_Inl_iff RS iffD1 RS FalseE]
	addSIs [InlI, InrI]) 1);
val lemma2_3 = result();

val [major, minor] = goalw thy AC_aux_defs 
	"[| f : bij(D+D, B); 1 le n |] ==>  \
\	sets_of_size_between({{f`Inl(i), f`Inr(i)}. i:D}, 2, succ(n))";
by (rewrite_goals_tac [succ_def]);
by (fast_tac (AC_cs addSIs [cons_lepoll_cong, minor, lepoll_refl, InlI, InrI] 
	addIs [singleton_eqpoll_1 RS eqpoll_imp_lepoll RS lepoll_trans,
		le_imp_subset RS subset_imp_lepoll]
	addDs [major RS bij_is_inj RS lemma, Inl_Inr_iff RS iffD1 RS FalseE]
	addSEs [RepFunE, not_emptyE, mem_irrefl]) 1);
val lemma2_4 = result();

goalw thy [bij_def, surj_def]
	"!!f. f : bij(D+D, B) ==> Union({{f`Inl(i), f`Inr(i)}. i:D})=B";
by (fast_tac (AC_cs addSEs [inj_is_fun RS apply_type, CollectE, sumE]
	addSIs [InlI, InrI, equalityI]) 1);
val lemma2_5 = result();

goal thy "!!A. [| WO1; ~Finite(B); 1 le n  |]  \
\	==> EX C:Pow(Pow(B)). pairwise_disjoint(C) &  \
\		sets_of_size_between(C, 2, succ(n)) &  \
\		Union(C)=B";
by (eresolve_tac [lemma2_1 RS (eqpoll_def RS def_imp_iff RS iffD1 RS exE)] 1
	THEN (assume_tac 1));
by (fast_tac (FOL_cs addSIs [bexI]
		addSEs [lemma2_2, lemma2_3, lemma2_4, lemma2_5]) 1);
val lemma2 = result();

goalw thy AC_defs "!!n. [| WO1; 1 le n |] ==> AC10(n)";
by (fast_tac (AC_cs addSIs [lemma1] addSEs [lemma2]) 1);
qed "WO1_AC10";
