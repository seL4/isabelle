(*  Title:      HOL/IMP/Transition.ML
    ID:         $Id$
    Author:     Tobias Nipkow & Robert Sandner, TUM
    Copyright   1996 TUM

Equivalence of Natural and Transition semantics
*)

section "Winskel's Proof";

AddSEs [rel_pow_0_E];

val evalc1_SEs = 
    map evalc1.mk_cases
       ["(SKIP,s) -1-> t", 
	"(x:=a,s) -1-> t",
	"(c1;c2, s) -1-> t", 
	"(IF b THEN c1 ELSE c2, s) -1-> t",
        "(WHILE b DO c, s) -1-> t"];

val evalc1_E = evalc1.mk_cases "(WHILE b DO c,s) -1-> t";

AddSEs evalc1_SEs;

AddIs evalc1.intrs;

Goal "(SKIP,s) -m-> (SKIP,t) ==> s = t & m = 0";
by (etac rel_pow_E2 1);
by (Asm_full_simp_tac 1);
by (Fast_tac 1);
val hlemma = result();


Goal "!s t u c d. (c,s) -n-> (SKIP,t) --> (d,t) -*-> (SKIP,u) --> \
\              (c;d, s) -*-> (SKIP, u)";
by (induct_tac "n" 1);
 by (fast_tac (claset() addIs [rtrancl_into_rtrancl2])1);
by (fast_tac  (claset() addIs [rtrancl_into_rtrancl2]addSDs [rel_pow_Suc_D2])1);
qed_spec_mp "lemma1";


Goal "<c,s> -c-> s1 ==> (c,s) -*-> (SKIP,s1)";
by (etac evalc.induct 1);

(* SKIP *)
by (rtac rtrancl_refl 1);

(* ASSIGN *)
by (fast_tac (claset() addSIs [r_into_rtrancl]) 1);

(* SEMI *)
by (fast_tac (claset() addDs [rtrancl_imp_UN_rel_pow] addIs [lemma1]) 1);

(* IF *)
by (fast_tac (claset() addIs [rtrancl_into_rtrancl2]) 1);
by (fast_tac (claset() addIs [rtrancl_into_rtrancl2]) 1);

(* WHILE *)
by (fast_tac (claset() addSIs [r_into_rtrancl]) 1);
by (fast_tac (claset() addDs [rtrancl_imp_UN_rel_pow]
                        addIs [rtrancl_into_rtrancl2,lemma1]) 1);

qed "evalc_impl_evalc1";


Goal "!c d s u. (c;d,s) -n-> (SKIP,u) --> \
\            (? t m. (c,s) -*-> (SKIP,t) & (d,t) -m-> (SKIP,u) & m <= n)";
by (induct_tac "n" 1);
 (* case n = 0 *)
 by (fast_tac (claset() addss simpset()) 1);
(* induction step *)
by (fast_tac (claset() addSIs [le_SucI,le_refl]
                     addSDs [rel_pow_Suc_D2]
                     addSEs [rel_pow_imp_rtrancl,rtrancl_into_rtrancl2]) 1);
qed_spec_mp "lemma2";

Goal "!s t. (c,s) -*-> (SKIP,t) --> <c,s> -c-> t";
by (induct_tac "c" 1);
by (safe_tac (claset() addSDs [rtrancl_imp_UN_rel_pow]));

(* SKIP *)
by (fast_tac (claset() addSEs [rel_pow_E2]) 1);

(* ASSIGN *)
by (fast_tac (claset() addSDs [hlemma]  addSEs [rel_pow_E2]) 1);

(* SEMI *)
by (fast_tac (claset() addSDs [lemma2,rel_pow_imp_rtrancl]) 1);

(* IF *)
by (etac rel_pow_E2 1);
by (Asm_full_simp_tac 1);
by (fast_tac (claset() addSDs [rel_pow_imp_rtrancl]) 1);

(* WHILE, induction on the length of the computation *)
by (eres_inst_tac [("P","?X -n-> ?Y")] rev_mp 1);
by (res_inst_tac [("x","s")] spec 1);
by (res_inst_tac [("n","n")] less_induct 1);
by (strip_tac 1);
by (etac rel_pow_E2 1);
 by (Asm_full_simp_tac 1);
by (etac evalc1_E 1);

(* WhileFalse *)
 by (fast_tac (claset() addSDs [hlemma]) 1);

(* WhileTrue *)
by (fast_tac(claset() addSDs[lemma2,le_imp_less_or_eq,less_Suc_eq RS iffD2])1);

qed_spec_mp "evalc1_impl_evalc";


(**** proof of the equivalence of evalc and evalc1 ****)

Goal "((c, s) -*-> (SKIP, t)) = (<c,s> -c-> t)";
by (fast_tac (HOL_cs addSEs [evalc1_impl_evalc,evalc_impl_evalc1]) 1);
qed "evalc1_eq_evalc";


section "A Proof Without -n->";

Goal "(c1,s1) -*-> (SKIP,s2) ==> \
\ (c2,s2) -*-> cs3 --> (c1;c2,s1) -*-> cs3";
by (etac converse_rtrancl_induct2 1);
by (fast_tac (claset() addIs [rtrancl_into_rtrancl2]) 1);
by (fast_tac (claset() addIs [rtrancl_into_rtrancl2]) 1);
qed_spec_mp "my_lemma1";


Goal "<c,s> -c-> s1 ==> (c,s) -*-> (SKIP,s1)";
by (etac evalc.induct 1);

(* SKIP *)
by (rtac rtrancl_refl 1);

(* ASSIGN *)
by (fast_tac (claset() addSIs [r_into_rtrancl]) 1);

(* SEMI *)
by (fast_tac (claset() addIs [my_lemma1]) 1);

(* IF *)
by (fast_tac (claset() addIs [rtrancl_into_rtrancl2]) 1);
by (fast_tac (claset() addIs [rtrancl_into_rtrancl2]) 1);

(* WHILE *)
by (fast_tac (claset() addSIs [r_into_rtrancl]) 1);
by (fast_tac (claset() addIs [rtrancl_into_rtrancl2,my_lemma1]) 1);

qed "evalc_impl_evalc1";

(* The opposite direction is based on a Coq proof done by Ranan Fraer and
   Yves Bertot. The following sketch is from an email by Ranan Fraer.
*)
(*
First we've broke it into 2 lemmas:

Lemma 1
((c,s) --> (SKIP,t)) => (<c,s> -c-> t)

This is a quick one, dealing with the cases skip, assignment
and while_false.

Lemma 2
((c,s) -*-> (c',s')) /\ <c',s'> -c'-> t
  => 
<c,s> -c-> t

This is proved by rule induction on the  -*-> relation
and the induction step makes use of a third lemma: 

Lemma 3
((c,s) --> (c',s')) /\ <c',s'> -c'-> t
  => 
<c,s> -c-> t

This captures the essence of the proof, as it shows that <c',s'> 
behaves as the continuation of <c,s> with respect to the natural
semantics.
The proof of Lemma 3 goes by rule induction on the --> relation,
dealing with the cases sequence1, sequence2, if_true, if_false and
while_true. In particular in the case (sequence1) we make use again
of Lemma 1.
*)

(*Delsimps [update_apply];*)
Goal "((c,s) -1-> (c',s')) ==> (!t. <c',s'> -c-> t --> <c,s> -c-> t)";
by (etac evalc1.induct 1);
by Auto_tac;
qed_spec_mp "FB_lemma3";
(*Addsimps [update_apply];*)

val [major] = goal Transition.thy
  "(c,s) -*-> (c',s') ==> <c',s'> -c-> t --> <c,s> -c-> t";
by (rtac (major RS rtrancl_induct2) 1);
 by (Fast_tac 1);
by (fast_tac (claset() addIs [FB_lemma3]) 1);
qed_spec_mp "FB_lemma2";

Goal "(c,s) -*-> (SKIP,t) ==> <c,s> -c-> t";
by (fast_tac (claset() addEs [FB_lemma2]) 1);
qed "evalc1_impl_evalc";


section "The proof in Nielson and Nielson";

(* The more precise n=i1+i2+1 is proved by the same script but complicates
   life further down, where i1,i2 < n is needed.
*)
Goal "!c1 s. (c1;c2,s) -n-> (SKIP,t) --> \
\     (? i1 i2 u. (c1,s) -i1-> (SKIP,u) & (c2,u) -i2-> (SKIP,t) & i1<n & i2<n)";
by (induct_tac "n" 1);
 by (fast_tac (claset() addSDs [hlemma]) 1);
by (fast_tac (claset() addSIs [rel_pow_0_I,rel_pow_Suc_I2]
                      addSDs [rel_pow_Suc_D2] addss simpset()) 1);
qed_spec_mp "comp_decomp_lemma";

Goal "!c s t. (c,s) -n-> (SKIP,t) --> <c,s> -c-> t";
by (res_inst_tac [("n","n")] less_induct 1);
by (Clarify_tac 1);
by (etac rel_pow_E2 1);
 by (asm_full_simp_tac (simpset() addsimps evalc.intrs) 1);
by (exhaust_tac "c" 1);
    by (fast_tac (claset() addSDs [hlemma]) 1);
   by (Blast_tac 1);
  by (blast_tac (claset() addSDs [rel_pow_Suc_I2 RS comp_decomp_lemma]) 1);
 by (Blast_tac 1);
by (Blast_tac 1);
qed_spec_mp "evalc1_impl_evalc";
