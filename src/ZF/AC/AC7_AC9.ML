(*  Title:      ZF/AC/AC7-AC9.ML
    ID:         $Id$
    Author:     Krzysztof Grabczewski

The proofs needed to state that AC7, AC8 and AC9 are equivalent to the previous
instances of AC.
*)

(* ********************************************************************** *)
(* Lemmas used in the proofs AC7 ==> AC6 and AC9 ==> AC1                  *)
(*  - Sigma_fun_space_not0                                                *)
(*  - Sigma_fun_space_eqpoll                                              *)
(* ********************************************************************** *)

Goal "[| 0~:A; B:A |] ==> (nat->Union(A)) * B ~= 0";
by (blast_tac (claset() addSDs [Sigma_empty_iff RS iffD1, 
				Union_empty_iff RS iffD1]) 1);
qed "Sigma_fun_space_not0";

Goalw [inj_def]
        "C:A ==> (lam g:(nat->Union(A))*C.  \
\               (lam n:nat. if(n=0, snd(g), fst(g)`(n #- 1))))  \
\               : inj((nat->Union(A))*C, (nat->Union(A)) ) ";
by (rtac CollectI 1);
by (fast_tac (claset() addSIs [lam_type,RepFunI,if_type,snd_type,apply_type,
                                fst_type,diff_type,nat_succI,nat_0I]) 1);
by (REPEAT (resolve_tac [ballI, impI] 1));
by (Asm_full_simp_tac 1);
by (REPEAT (etac SigmaE 1));
by (REPEAT (hyp_subst_tac 1));
by (Asm_full_simp_tac 1);
by (rtac conjI 1);
by (dresolve_tac [nat_0I RSN (2, lam_eqE)] 2);
by (Asm_full_simp_tac 2);
by (rtac fun_extension 1 THEN  REPEAT (assume_tac 1));
by (dresolve_tac [nat_succI RSN (2, lam_eqE)] 1 THEN (assume_tac 1));
by (asm_full_simp_tac (simpset() addsimps [succ_not_0 RS if_not_P]) 1);
val lemma = result();

Goal "[| C:A; 0~:A |] ==> (nat->Union(A)) * C eqpoll (nat->Union(A))";
by (rtac eqpollI 1);
by (fast_tac (claset() addSEs [prod_lepoll_self, not_sym RS not_emptyE,
                subst_elem] addEs [swap]) 2);
by (rewtac lepoll_def);
by (fast_tac (claset() addSIs [lemma]) 1);
qed "Sigma_fun_space_eqpoll";


(* ********************************************************************** *)
(* AC6 ==> AC7                                                            *)
(* ********************************************************************** *)

Goalw AC_defs "AC6 ==> AC7";
by (Blast_tac 1);
qed "AC6_AC7";

(* ********************************************************************** *)
(* AC7 ==> AC6, Rubin & Rubin p. 12, Theorem 2.8                          *)
(* The case of the empty family of sets added in order to complete        *)
(* the proof.                                                             *)
(* ********************************************************************** *)

Goal "y: (PROD B:A. Y*B) ==> (lam B:A. snd(y`B)): (PROD B:A. B)";
by (fast_tac (claset() addSIs [lam_type, snd_type, apply_type]) 1);
val lemma1_1 = result();

Goal "y: (PROD B:{Y*C. C:A}. B) ==> (lam B:A. y`(Y*B)): (PROD B:A. Y*B)";
by (fast_tac (claset() addSIs [lam_type, apply_type]) 1);
val lemma1_2 = result();

Goal "(PROD B:{(nat->Union(A))*C. C:A}. B) ~= 0 ==> (PROD B:A. B) ~= 0";
by (fast_tac (claset() addSIs [equals0I,lemma1_1, lemma1_2]) 1);
val lemma1 = result();

Goal "0 ~: A ==> 0 ~: {(nat -> Union(A)) * C. C:A}";
by (fast_tac (claset() addEs [Sigma_fun_space_not0 RS not_sym RS notE]) 1);
val lemma2 = result();

Goalw AC_defs "AC7 ==> AC6";
by (rtac allI 1);
by (rtac impI 1);
by (case_tac "A=0" 1);
by (Asm_simp_tac 1);
by (rtac lemma1 1);
by (etac allE 1);
by (etac impE 1 THEN (assume_tac 2));
by (blast_tac (claset() addSIs [lemma2] 
                addIs [eqpoll_sym, eqpoll_trans, Sigma_fun_space_eqpoll]) 1); 
qed "AC7_AC6";


(* ********************************************************************** *)
(* AC1 ==> AC8                                                            *)
(* ********************************************************************** *)

Goalw [eqpoll_def]
        "ALL B:A. EX B1 B2. B=<B1,B2> & B1 eqpoll B2  \
\       ==> 0 ~: { bij(fst(B),snd(B)). B:A }";
by Auto_tac;
val lemma1 = result();

Goal "[| f: (PROD X:RepFun(A,p). X); D:A |] ==> (lam x:A. f`p(x))`D : p(D)";
by (resolve_tac [beta RS ssubst] 1 THEN (assume_tac 1));
by (fast_tac (claset() addSEs [apply_type]) 1);
val lemma2 = result();

Goalw AC_defs "AC1 ==> AC8";
by (Clarify_tac 1);
by (dtac lemma1 1);
by (fast_tac (claset() addSEs [lemma2]) 1);
qed "AC1_AC8";


(* ********************************************************************** *)
(* AC8 ==> AC9                                                            *)
(*  - this proof replaces the following two from Rubin & Rubin:           *)
(*    AC8 ==> AC1 and AC1 ==> AC9                                         *)
(* ********************************************************************** *)

Goal "ALL B1:A. ALL B2:A. B1 eqpoll B2 ==>  \
\               ALL B:A*A. EX B1 B2. B=<B1,B2> & B1 eqpoll B2";
by (Fast_tac 1);
val lemma1 = result();

Goal "f:bij(fst(<a,b>),snd(<a,b>)) ==> f:bij(a,b)";
by (Asm_full_simp_tac 1);
val lemma2 = result();

Goalw AC_defs "AC8 ==> AC9";
by (rtac allI 1);
by (rtac impI 1);
by (etac allE 1);
by (etac impE 1);
by (etac lemma1 1);
by (fast_tac (claset() addSEs [lemma2]) 1);
qed "AC8_AC9";


(* ********************************************************************** *)
(* AC9 ==> AC1                                                            *)
(* The idea of this proof comes from "Equivalents of the Axiom of Choice" *)
(* by Rubin & Rubin. But (x * y) is not necessarily equipollent to        *)
(* (x * y) Un {0} when y is a set of total functions acting from nat to   *)
(* Union(A) -- therefore we have used the set (y * nat) instead of y.     *)
(* ********************************************************************** *)

(* Rules nedded to prove lemma1 *)
val snd_lepoll_SigmaI = prod_lepoll_self RS 
        ((prod_commute_eqpoll RS eqpoll_imp_lepoll) RSN (2,lepoll_trans));


Goal "[|0 \\<notin> A; B \\<in> A|] ==> nat \\<lesssim> ((nat \\<rightarrow> Union(A)) \\<times> B) \\<times> nat";
by (blast_tac (claset() addDs [Sigma_fun_space_not0]
                        addIs [snd_lepoll_SigmaI]) 1);
qed "nat_lepoll_lemma";


Goal "[| 0~:A;  A~=0;  \
\        C = {((nat->Union(A))*B)*nat. B:A}  Un \
\            {cons(0,((nat->Union(A))*B)*nat). B:A}; \
\        B1: C;  B2: C |]  \
\     ==> B1 eqpoll B2";
by (blast_tac
    (claset() addSIs [nat_lepoll_lemma, nat_cons_eqpoll RS eqpoll_trans, 
                      eqpoll_refl RSN (2, prod_eqpoll_cong)]
              addIs [eqpoll_trans, eqpoll_sym, Sigma_fun_space_eqpoll]) 1);
val lemma1 = result();

Goal "ALL B1:{(F*B)*N. B:A} Un {cons(0,(F*B)*N). B:A}.  \
\       ALL B2:{(F*B)*N. B:A}  \
\       Un {cons(0,(F*B)*N). B:A}. f`<B1,B2> : bij(B1, B2)  \
\       ==> (lam B:A. snd(fst((f`<cons(0,(F*B)*N),(F*B)*N>)`0))) :  \
\               (PROD X:A. X)";
by (rtac lam_type 1);
by (rtac snd_type 1);
by (rtac fst_type 1);
by (resolve_tac [consI1 RSN (2, apply_type)] 1);
by (fast_tac (claset() addSIs [fun_weaken_type, bij_is_fun]) 1);
val lemma2 = result();

Goalw AC_defs "AC9 ==> AC1";
by (rtac allI 1);
by (rtac impI 1);
by (etac allE 1);
by (case_tac "A=0" 1);
by (blast_tac (claset() addDs [lemma1,lemma2]) 2); 
by Auto_tac;  
qed "AC9_AC1";
