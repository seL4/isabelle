(*  Title:      HOLCF/pcpo.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for pcpo.thy
*)
 
open Pcpo;


(* ------------------------------------------------------------------------ *)
(* derive the old rule minimal                                              *)
(* ------------------------------------------------------------------------ *)

qed_goalw "UU_least" thy [ UU_def ] "!z.UU << z"
(fn prems => [ 
        (rtac (select_eq_Ex RS iffD2) 1),
        (rtac least 1)]);

bind_thm("minimal",UU_least RS spec);

(* ------------------------------------------------------------------------ *)
(* in cpo's everthing equal to THE lub has lub properties for every chain  *)
(* ------------------------------------------------------------------------ *)

qed_goal "thelubE"  thy 
        "[| is_chain(S);lub(range(S)) = (l::'a::cpo)|] ==> range(S) <<| l "
(fn prems =>
        [
        (cut_facts_tac prems 1), 
        (hyp_subst_tac 1),
        (rtac lubI 1),
        (etac cpo 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Properties of the lub                                                    *)
(* ------------------------------------------------------------------------ *)


bind_thm ("is_ub_thelub", cpo RS lubI RS is_ub_lub);
(* is_chain(?S1) ==> ?S1(?x) << lub(range(?S1))                             *)

bind_thm ("is_lub_thelub", cpo RS lubI RS is_lub_lub);
(* [| is_chain(?S5); range(?S5) <| ?x1 |] ==> lub(range(?S5)) << ?x1        *)

qed_goal "maxinch_is_thelub" thy "is_chain Y ==> \
\       max_in_chain i Y = (lub(range(Y)) = ((Y i)::'a::cpo))" 
(fn prems => 
        [
        cut_facts_tac prems 1,
        rtac iffI 1,
        fast_tac (HOL_cs addSIs [thelubI,lub_finch1]) 1,
        rewtac max_in_chain_def,
        safe_tac (HOL_cs addSIs [antisym_less]),
        fast_tac (HOL_cs addSEs [chain_mono3]) 1,
        dtac sym 1,
        fast_tac ((HOL_cs addSEs [is_ub_thelub]) addss !simpset) 1
        ]);


(* ------------------------------------------------------------------------ *)
(* the << relation between two chains is preserved by their lubs            *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_mono" thy 
        "[|is_chain(C1::(nat=>'a::cpo));is_chain(C2); ! k. C1(k) << C2(k)|]\
\           ==> lub(range(C1)) << lub(range(C2))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac is_lub_thelub 1),
        (rtac ub_rangeI 1),
        (rtac allI 1),
        (rtac trans_less 1),
        (etac spec 1),
        (etac is_ub_thelub 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* the = relation between two chains is preserved by their lubs            *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_equal" thy
"[| is_chain(C1::(nat=>'a::cpo));is_chain(C2);!k.C1(k)=C2(k)|]\
\       ==> lub(range(C1))=lub(range(C2))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac antisym_less 1),
        (rtac lub_mono 1),
        (atac 1),
        (atac 1),
        (strip_tac 1),
        (rtac (antisym_less_inverse RS conjunct1) 1),
        (etac spec 1),
        (rtac lub_mono 1),
        (atac 1),
        (atac 1),
        (strip_tac 1),
        (rtac (antisym_less_inverse RS conjunct2) 1),
        (etac spec 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* more results about mono and = of lubs of chains                          *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_mono2" thy 
"[|? j.!i. j<i --> X(i::nat)=Y(i);is_chain(X::nat=>'a::cpo);is_chain(Y)|]\
\ ==> lub(range(X))<<lub(range(Y))"
 (fn prems =>
        [
        (rtac  exE 1),
        (resolve_tac prems 1),
        (rtac is_lub_thelub 1),
        (resolve_tac prems 1),
        (rtac ub_rangeI 1),
        (strip_tac 1),
        (case_tac "x<i" 1),
        (res_inst_tac [("s","Y(i)"),("t","X(i)")] subst 1),
        (rtac sym 1),
        (Fast_tac 1),
        (rtac is_ub_thelub 1),
        (resolve_tac prems 1),
        (res_inst_tac [("y","X(Suc(x))")] trans_less 1),
        (rtac (chain_mono RS mp) 1),
        (resolve_tac prems 1),
        (rtac (not_less_eq RS subst) 1),
        (atac 1),
        (res_inst_tac [("s","Y(Suc(x))"),("t","X(Suc(x))")] subst 1),
        (rtac sym 1),
        (Asm_simp_tac 1),
        (rtac is_ub_thelub 1),
        (resolve_tac prems 1)
        ]);

qed_goal "lub_equal2" thy 
"[|? j.!i. j<i --> X(i)=Y(i);is_chain(X::nat=>'a::cpo);is_chain(Y)|]\
\ ==> lub(range(X))=lub(range(Y))"
 (fn prems =>
        [
        (rtac antisym_less 1),
        (rtac lub_mono2 1),
        (REPEAT (resolve_tac prems 1)),
        (cut_facts_tac prems 1),
        (rtac lub_mono2 1),
        Safe_tac,
        (Step_tac 1),
        Safe_tac,
        (rtac sym 1),
        (Fast_tac 1)
        ]);

qed_goal "lub_mono3" thy "[|is_chain(Y::nat=>'a::cpo);is_chain(X);\
\! i. ? j. Y(i)<< X(j)|]==> lub(range(Y))<<lub(range(X))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lub_thelub 1),
        (atac 1),
        (rtac ub_rangeI 1),
        (strip_tac 1),
        (etac allE 1),
        (etac exE 1),
        (rtac trans_less 1),
        (rtac is_ub_thelub 2),
        (atac 2),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* usefull lemmas about UU                                                  *)
(* ------------------------------------------------------------------------ *)

val eq_UU_sym = prove_goal thy "(UU = x) = (x = UU)" (fn _ => [
        Fast_tac 1]);

qed_goal "eq_UU_iff" thy "(x=UU)=(x<<UU)"
 (fn prems =>
        [
        (rtac iffI 1),
        (hyp_subst_tac 1),
        (rtac refl_less 1),
        (rtac antisym_less 1),
        (atac 1),
        (rtac minimal 1)
        ]);

qed_goal "UU_I" thy "x << UU ==> x = UU"
 (fn prems =>
        [
        (stac eq_UU_iff 1),
        (resolve_tac prems 1)
        ]);

qed_goal "not_less2not_eq" thy "~(x::'a::po)<<y ==> ~x=y"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac classical2 1),
        (atac 1),
        (hyp_subst_tac 1),
        (rtac refl_less 1)
        ]);

qed_goal "chain_UU_I" thy
        "[|is_chain(Y);lub(range(Y))=UU|] ==> ! i.Y(i)=UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac allI 1),
        (rtac antisym_less 1),
        (rtac minimal 2),
        (etac subst 1),
        (etac is_ub_thelub 1)
        ]);


qed_goal "chain_UU_I_inverse" thy 
        "!i.Y(i::nat)=UU ==> lub(range(Y::(nat=>'a::pcpo)))=UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac lub_chain_maxelem 1),
        (rtac exI 1),
        (etac spec 1),
        (rtac allI 1),
        (rtac (antisym_less_inverse RS conjunct1) 1),
        (etac spec 1)
        ]);

qed_goal "chain_UU_I_inverse2" thy 
        "~lub(range(Y::(nat=>'a::pcpo)))=UU ==> ? i.~ Y(i)=UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (not_all RS iffD1) 1),
        (rtac swap 1),
        (rtac chain_UU_I_inverse 2),
        (etac notnotD 2),
        (atac 1)
        ]);


qed_goal "notUU_I" thy "[| x<<y; ~x=UU |] ==> ~y=UU"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac contrapos 1),
        (rtac UU_I 1),
        (hyp_subst_tac 1),
        (atac 1)
        ]);


qed_goal "chain_mono2" thy 
"[|? j.~Y(j)=UU;is_chain(Y::nat=>'a::pcpo)|]\
\ ==> ? j.!i.j<i-->~Y(i)=UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        Safe_tac,
        (Step_tac 1),
        (strip_tac 1),
        (rtac notUU_I 1),
        (atac 2),
        (etac (chain_mono RS mp) 1),
        (atac 1)
        ]);

(**************************************)
(* some properties for chfin and flat *)
(**************************************)

(* ------------------------------------------------------------------------ *)
(* flat types are chain_finite                                              *)
(* ------------------------------------------------------------------------ *)

qed_goalw "flat_imp_chain_finite" thy [max_in_chain_def]
        "!Y::nat=>'a::flat.is_chain Y-->(? n.max_in_chain n Y)"
 (fn _ =>
        [
        (strip_tac 1),
        (case_tac "!i.Y(i)=UU" 1),
        (res_inst_tac [("x","0")] exI 1),
	(Asm_simp_tac 1),
 	(Asm_full_simp_tac 1),
 	(etac exE 1),
        (res_inst_tac [("x","i")] exI 1),
        (strip_tac 1),
        (dres_inst_tac [("x","i"),("y","j")] chain_mono 1),
        (etac (le_imp_less_or_eq RS disjE) 1),
	Safe_tac,
	(dtac (ax_flat RS spec RS spec RS mp) 1),
	(Fast_tac 1)
        ]);

(* flat subclass of chfin --> adm_flat not needed *)

qed_goal "flat_eq" thy "(a::'a::flat) ~= UU ==> a << b = (a = b)" 
(fn prems=>
	[
        cut_facts_tac prems 1,
        safe_tac (HOL_cs addSIs [refl_less]),
	dtac (ax_flat RS spec RS spec RS mp) 1,
	fast_tac (HOL_cs addSIs [refl_less,ax_flat RS spec RS spec RS mp]) 1
	]);

qed_goal "chfin2finch" thy 
    "is_chain (Y::nat=>'a::chfin) ==> finite_chain Y"
	(fn prems => 
	[
	cut_facts_tac prems 1,
	fast_tac (HOL_cs addss 
		 (!simpset addsimps [chfin,finite_chain_def])) 1
	]);

(* ------------------------------------------------------------------------ *)
(* lemmata for improved admissibility introdution rule                      *)
(* ------------------------------------------------------------------------ *)

qed_goal "infinite_chain_adm_lemma" Porder.thy 
"[|is_chain Y; !i. P (Y i); \
\  (!!Y. [| is_chain Y; !i. P (Y i); ~ finite_chain Y |] ==> P (lub (range Y)))\
\ |] ==> P (lub (range Y))"
 (fn prems => [
        cut_facts_tac prems 1,
        case_tac "finite_chain Y" 1,
         eresolve_tac prems 2, atac 2, atac 2,
        rewtac finite_chain_def,
        safe_tac HOL_cs,
        etac (lub_finch1 RS thelubI RS ssubst) 1, atac 1, etac spec 1]);

qed_goal "increasing_chain_adm_lemma" Porder.thy 
"[|is_chain Y; !i. P (Y i); \
\  (!!Y. [| is_chain Y; !i. P (Y i); !i. ? j. i < j & Y i ~= Y j & Y i << Y j|]\
\ ==> P (lub (range Y))) |] ==> P (lub (range Y))"
 (fn prems => [
        cut_facts_tac prems 1,
        etac infinite_chain_adm_lemma 1, atac 1, etac thin_rl 1,
        rewtac finite_chain_def,
        safe_tac HOL_cs,
        etac swap 1,
        rewtac max_in_chain_def,
        resolve_tac prems 1, atac 1, atac 1,
        fast_tac (HOL_cs addDs [le_imp_less_or_eq] 
                         addEs [chain_mono RS mp]) 1]);
