(*  Title:      HOLCF/Pcpo.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

introduction of the classes cpo and pcpo 
*)
 

(* ------------------------------------------------------------------------ *)
(* derive the old rule minimal                                              *)
(* ------------------------------------------------------------------------ *)
 
Goalw [UU_def] "ALL z. UU << z";
by (rtac (select_eq_Ex RS iffD2) 1);
by (rtac least 1);
qed "UU_least";

bind_thm("minimal", UU_least RS spec);

AddIffs [minimal];

(* ------------------------------------------------------------------------ *)
(* in cpo's everthing equal to THE lub has lub properties for every chain  *)
(* ------------------------------------------------------------------------ *)

Goal "[| chain(S); lub(range(S)) = (l::'a::cpo) |] ==> range(S) <<| l ";
by (blast_tac (claset() addDs [cpo] addIs [lubI]) 1);
qed "thelubE";

(* ------------------------------------------------------------------------ *)
(* Properties of the lub                                                    *)
(* ------------------------------------------------------------------------ *)


Goal "chain (S::nat => 'a::cpo) ==> S(x) << lub(range(S))";
by (blast_tac (claset() addDs [cpo] addIs [lubI RS is_ub_lub]) 1);
qed "is_ub_thelub";

Goal "[| chain (S::nat => 'a::cpo); range(S) <| x |] ==> lub(range S) << x";
by (blast_tac (claset() addDs [cpo] addIs [lubI RS is_lub_lub]) 1);
qed "is_lub_thelub";


Goal "chain Y ==> max_in_chain i Y = (lub(range(Y)) = ((Y i)::'a::cpo))";
by (rtac iffI 1);
by (fast_tac (HOL_cs addSIs [thelubI,lub_finch1]) 1);
by (rewtac max_in_chain_def);
by (safe_tac (HOL_cs addSIs [antisym_less]));
by (fast_tac (HOL_cs addSEs [chain_mono3]) 1);
by (dtac sym 1);
by (force_tac (HOL_cs addSEs [is_ub_thelub], simpset()) 1);
qed "maxinch_is_thelub";


(* ------------------------------------------------------------------------ *)
(* the << relation between two chains is preserved by their lubs            *)
(* ------------------------------------------------------------------------ *)

Goal "[|chain(C1::(nat=>'a::cpo));chain(C2); ALL k. C1(k) << C2(k)|]\
\     ==> lub(range(C1)) << lub(range(C2))";
by (etac is_lub_thelub 1);
by (rtac ub_rangeI 1);
by (rtac trans_less 1);
by (etac spec 1);
by (etac is_ub_thelub 1);
qed "lub_mono";

(* ------------------------------------------------------------------------ *)
(* the = relation between two chains is preserved by their lubs            *)
(* ------------------------------------------------------------------------ *)

Goal "[| chain(C1::(nat=>'a::cpo));chain(C2);ALL k. C1(k)=C2(k)|]\
\     ==> lub(range(C1))=lub(range(C2))";
by (rtac antisym_less 1);
by (rtac lub_mono 1);
by (atac 1);
by (atac 1);
by (strip_tac 1);
by (rtac (antisym_less_inverse RS conjunct1) 1);
by (etac spec 1);
by (rtac lub_mono 1);
by (atac 1);
by (atac 1);
by (strip_tac 1);
by (rtac (antisym_less_inverse RS conjunct2) 1);
by (etac spec 1);
qed "lub_equal";

(* ------------------------------------------------------------------------ *)
(* more results about mono and = of lubs of chains                          *)
(* ------------------------------------------------------------------------ *)

Goal "[|EX j. ALL i. j<i --> X(i::nat)=Y(i);chain(X::nat=>'a::cpo);chain(Y)|]\
\ ==> lub(range(X))<<lub(range(Y))";
by (etac  exE 1);
by (rtac is_lub_thelub 1);
by (assume_tac 1);
by (rtac ub_rangeI 1);
by (strip_tac 1);
by (case_tac "j<i" 1);
by (res_inst_tac [("s","Y(i)"),("t","X(i)")] subst 1);
by (rtac sym 1);
by (Fast_tac 1);
by (rtac is_ub_thelub 1);
by (assume_tac 1);
by (res_inst_tac [("y","X(Suc(j))")] trans_less 1);
by (rtac chain_mono 1);
by (assume_tac 1);
by (rtac (not_less_eq RS subst) 1);
by (atac 1);
by (res_inst_tac [("s","Y(Suc(j))"),("t","X(Suc(j))")] subst 1);
by (Asm_simp_tac 1);
by (etac is_ub_thelub 1);
qed "lub_mono2";

Goal "[|EX j. ALL i. j<i --> X(i)=Y(i); chain(X::nat=>'a::cpo); chain(Y)|]\
\     ==> lub(range(X))=lub(range(Y))";
by (blast_tac (claset() addIs [antisym_less, lub_mono2, sym]) 1);
qed "lub_equal2";

Goal "[|chain(Y::nat=>'a::cpo);chain(X);\
\ALL i. EX j. Y(i)<< X(j)|]==> lub(range(Y))<<lub(range(X))";
by (rtac is_lub_thelub 1);
by (atac 1);
by (rtac ub_rangeI 1);
by (strip_tac 1);
by (etac allE 1);
by (etac exE 1);
by (rtac trans_less 1);
by (rtac is_ub_thelub 2);
by (atac 2);
by (atac 1);
qed "lub_mono3";

(* ------------------------------------------------------------------------ *)
(* usefull lemmas about UU                                                  *)
(* ------------------------------------------------------------------------ *)

Goal "(x=UU)=(x<<UU)";
by (rtac iffI 1);
by (hyp_subst_tac 1);
by (rtac refl_less 1);
by (rtac antisym_less 1);
by (atac 1);
by (rtac minimal 1);
qed "eq_UU_iff";

Goal "x << UU ==> x = UU";
by (stac eq_UU_iff 1);
by (assume_tac 1);
qed "UU_I";

Goal "~(x::'a::po)<<y ==> ~x=y";
by Auto_tac;
qed "not_less2not_eq";

Goal "[|chain(Y);lub(range(Y))=UU|] ==> ALL i. Y(i)=UU";
by (rtac allI 1);
by (rtac antisym_less 1);
by (rtac minimal 2);
by (etac subst 1);
by (etac is_ub_thelub 1);
qed "chain_UU_I";


Goal "ALL i. Y(i::nat)=UU ==> lub(range(Y::(nat=>'a::pcpo)))=UU";
by (rtac lub_chain_maxelem 1);
by (etac spec 1);
by (rtac allI 1);
by (rtac (antisym_less_inverse RS conjunct1) 1);
by (etac spec 1);
qed "chain_UU_I_inverse";

Goal "~lub(range(Y::(nat=>'a::pcpo)))=UU ==> EX i.~ Y(i)=UU";
by (blast_tac (claset() addIs [chain_UU_I_inverse]) 1);
qed "chain_UU_I_inverse2";

Goal "[| x<<y; ~x=UU |] ==> ~y=UU";
by (blast_tac (claset() addIs [UU_I]) 1);
qed "notUU_I";

Goal 
 "[|EX j. ~Y(j)=UU;chain(Y::nat=>'a::pcpo)|] ==> EX j. ALL i. j<i-->~Y(i)=UU";
by (blast_tac (claset() addDs [notUU_I, chain_mono]) 1);
qed "chain_mono2";

(**************************************)
(* some properties for chfin and flat *)
(**************************************)

(* ------------------------------------------------------------------------ *)
(* flat types are chfin                                              *)
(* ------------------------------------------------------------------------ *)

(*Used only in an "instance" declaration (Fun1.thy)*)
Goalw [max_in_chain_def]
     "ALL Y::nat=>'a::flat. chain Y --> (EX n. max_in_chain n Y)";
by (Clarify_tac 1);
by (case_tac "ALL i. Y(i)=UU" 1);
by (res_inst_tac [("x","0")] exI 1);
by (Asm_simp_tac 1);
by (Asm_full_simp_tac 1);
by (etac exE 1);
by (res_inst_tac [("x","i")] exI 1);
by (strip_tac 1);
by (etac (le_imp_less_or_eq RS disjE) 1);
by Safe_tac;
by (blast_tac (claset() addDs [chain_mono, ax_flat RS spec RS spec RS mp]) 1);
qed "flat_imp_chfin";

(* flat subclass of chfin --> adm_flat not needed *)

Goal "(a::'a::flat) ~= UU ==> a << b = (a = b)";
by (safe_tac (HOL_cs addSIs [refl_less]));
by (dtac (ax_flat RS spec RS spec RS mp) 1);
by (fast_tac (HOL_cs addSIs [refl_less,ax_flat RS spec RS spec RS mp]) 1);
qed "flat_eq";

Goal "chain (Y::nat=>'a::chfin) ==> finite_chain Y";
by (force_tac (HOL_cs, simpset() addsimps [chfin,finite_chain_def]) 1);
qed "chfin2finch";

(* ------------------------------------------------------------------------ *)
(* lemmata for improved admissibility introdution rule                      *)
(* ------------------------------------------------------------------------ *)

val prems = Goal
"[|chain Y; ALL i. P (Y i); \
\  (!!Y. [| chain Y; ALL i. P (Y i); ~ finite_chain Y |] ==> P (lub(range Y)))\
\ |] ==> P (lub (range Y))";
by (cut_facts_tac prems 1);
by (case_tac "finite_chain Y" 1);
by (eresolve_tac prems 2);
by (atac 2);
by (atac 2);
by (rewtac finite_chain_def);
by (safe_tac HOL_cs);
by (etac (lub_finch1 RS thelubI RS ssubst) 1);
by (atac 1);
by (etac spec 1);
qed "infinite_chain_adm_lemma";

val prems = Goal
"[|chain Y;  ALL i. P (Y i); \
\  (!!Y. [| chain Y; ALL i. P (Y i);  \
\           ALL i. EX j. i < j & Y i ~= Y j & Y i << Y j|]\
\ ==> P (lub (range Y))) |] ==> P (lub (range Y))";
by (cut_facts_tac prems 1);
by (etac infinite_chain_adm_lemma 1);
by (atac 1);
by (etac thin_rl 1);
by (rewtac finite_chain_def);
by (rewtac max_in_chain_def);
by (fast_tac (HOL_cs addIs prems
		     addDs [le_imp_less_or_eq] addEs [chain_mono]) 1);
qed "increasing_chain_adm_lemma";
