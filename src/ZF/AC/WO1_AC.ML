(*  Title:      ZF/AC/WO1_AC.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proofs of WO1 ==> AC1 and WO1 ==> AC10(n) for n >= 1

The latter proof is referred to as clear by the Rubins.
However it seems to be quite complicated.
The formal proof presented below is a mechanisation of the proof 
by Lawrence C. Paulson which is the following:

Assume WO1.  Let s be a set of infinite sets.
 
Suppose x \\<in> s.  Then x is equipollent to |x| (by WO1), an infinite cardinal; 
call it K.  Since K = K |+| K = |K+K| (by InfCard_cdouble_eq) there is an 
isomorphism h \\<in> bij(K+K, x).  (Here + means disjoint sum.)
 
So there is a partition of x into 2-element sets, namely
 
        {{h(Inl(i)), h(Inr(i))} . i \\<in> K}
 
So for all x \\<in> s the desired partition exists.  By AC1 (which follows from WO1) 
there exists a function f that chooses a partition for each x \\<in> s.  Therefore we 
have AC10(2).

*)

(* ********************************************************************** *)
(* WO1 ==> AC1                                                            *)
(* ********************************************************************** *)

Goalw [AC1_def, WO1_def] "WO1 ==> AC1";
by (fast_tac (claset() addSEs [ex_choice_fun]) 1);
qed "WO1_AC1";

(* ********************************************************************** *)
(* WO1 ==> AC10(n) (n >= 1)                                               *)
(* ********************************************************************** *)

Goalw [WO1_def] "[| WO1; \\<forall>B \\<in> A. \\<exists>C \\<in> D(B). P(C,B) |]  \
\               ==> \\<exists>f. \\<forall>B \\<in> A. P(f`B,B)";
by (eres_inst_tac [("x","Union({{C \\<in> D(B). P(C,B)}. B \\<in> A})")] allE 1);
by (etac exE 1);
by (dtac ex_choice_fun 1);
by (Fast_tac 1);
by (etac exE 1);
by (res_inst_tac [("x","\\<lambda>x \\<in> A. f`{C \\<in> D(x). P(C,x)}")] exI 1);
by (Asm_full_simp_tac 1);
by (blast_tac (claset() addSDs [RepFunI RSN (2, apply_type)]) 1);
val lemma1 = result();

Goalw [WO1_def] "[| ~Finite(B); WO1 |] ==> |B| + |B| eqpoll  B";
by (rtac eqpoll_trans 1);
by (fast_tac (claset() addSEs [well_ord_cardinal_eqpoll]) 2);
by (resolve_tac [eqpoll_sym RS eqpoll_trans] 1);
by (fast_tac (claset() addSEs [well_ord_cardinal_eqpoll]) 1);
by (fold_tac [cadd_def]);
by (resolve_tac [Card_cardinal RSN (2, Inf_Card_is_InfCard) RS 
		 InfCard_cdouble_eq RS ssubst] 1);
by (rtac eqpoll_refl 2);
by (rtac notI 1);
by (etac notE 1);
by (resolve_tac [eqpoll_sym RS eqpoll_imp_lepoll RS lepoll_Finite] 1
        THEN (assume_tac 2));
by (fast_tac (claset() addSEs [well_ord_cardinal_eqpoll]) 1);
val lemma2_1 = result();

Goal "f \\<in> bij(D+D, B) ==> {{f`Inl(i), f`Inr(i)}. i \\<in> D} \\<in> Pow(Pow(B))";
by (fast_tac (claset() addSEs [bij_is_fun RS apply_type]) 1);
val lemma2_2 = result();

Goal "[| f \\<in> inj(A,B); f`a = f`b; a \\<in> A; b \\<in> A |] ==> a=b";
by (rtac inj_equality 1);
by (TRYALL (fast_tac (claset() addSEs [inj_is_fun RS apply_Pair] addEs [subst])));
val lemma = result();

Goalw AC_aux_defs
        "f \\<in> bij(D+D, B) ==> pairwise_disjoint({{f`Inl(i), f`Inr(i)}. i \\<in> D})";
by (blast_tac (claset() addDs [bij_is_inj RS lemma]) 1);
val lemma2_3 = result();

val [major, minor] = goalw thy AC_aux_defs 
        "[| f \\<in> bij(D+D, B); 1 le n |] ==>  \
\       sets_of_size_between({{f`Inl(i), f`Inr(i)}. i \\<in> D}, 2, succ(n))";
by (rewtac succ_def);
by (fast_tac (claset() 
        addSIs [cons_lepoll_cong, minor, lepoll_refl] 
        addIs [singleton_eqpoll_1 RS eqpoll_imp_lepoll RS lepoll_trans,
                le_imp_subset RS subset_imp_lepoll]
        addDs [major RS bij_is_inj RS lemma]
        addSEs [mem_irrefl]) 1);
val lemma2_4 = result();

Goalw [bij_def, surj_def]
        "f \\<in> bij(D+D, B) ==> Union({{f`Inl(i), f`Inr(i)}. i \\<in> D})=B";
by (fast_tac (claset() addSEs [inj_is_fun RS apply_type]) 1);
val lemma2_5 = result();

Goal "[| WO1; ~Finite(B); 1 le n  |]  \
\       ==> \\<exists>C \\<in> Pow(Pow(B)). pairwise_disjoint(C) &  \
\               sets_of_size_between(C, 2, succ(n)) &  \
\               Union(C)=B";
by (eresolve_tac [lemma2_1 RS (eqpoll_def RS def_imp_iff RS iffD1 RS exE)] 1
        THEN (assume_tac 1));
by (fast_tac (FOL_cs addSIs [bexI]
                addSEs [lemma2_2, lemma2_3, lemma2_4, lemma2_5]) 1);
val lemma2 = result();

Goalw AC_defs "[| WO1; 1 le n |] ==> AC10(n)";
by (fast_tac (claset() addSIs [lemma1] addSEs [lemma2]) 1);
qed "WO1_AC10";
