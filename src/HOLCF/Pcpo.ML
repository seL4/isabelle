(*  Title: 	HOLCF/pcpo.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for pcpo.thy
*)
 
open Pcpo;

(* ------------------------------------------------------------------------ *)
(* in pcpo's everthing equal to THE lub has lub properties for every chain  *)
(* ------------------------------------------------------------------------ *)

qed_goal "thelubE"  Pcpo.thy 
	"[| is_chain(S);lub(range(S)) = (l::'a::pcpo)|] ==> range(S) <<| l "
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


val is_ub_thelub = (cpo RS lubI RS is_ub_lub);
(* is_chain(?S1) ==> ?S1(?x) << lub(range(?S1))                             *)

val is_lub_thelub = (cpo RS lubI RS is_lub_lub);
(* [| is_chain(?S5); range(?S5) <| ?x1 |] ==> lub(range(?S5)) << ?x1        *)


(* ------------------------------------------------------------------------ *)
(* the << relation between two chains is preserved by their lubs            *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_mono" Pcpo.thy 
	"[|is_chain(C1::(nat=>'a::pcpo));is_chain(C2); ! k. C1(k) << C2(k)|]\
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

qed_goal "lub_equal" Pcpo.thy
"[| is_chain(C1::(nat=>'a::pcpo));is_chain(C2);!k.C1(k)=C2(k)|]\
\	==> lub(range(C1))=lub(range(C2))"
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

qed_goal "lub_mono2" Pcpo.thy 
"[|? j.!i. j<i --> X(i::nat)=Y(i);is_chain(X::nat=>'a::pcpo);is_chain(Y)|]\
\ ==> lub(range(X))<<lub(range(Y))"
 (fn prems =>
	[
	(rtac  exE 1),
	(resolve_tac prems 1),
	(rtac is_lub_thelub 1),
	(resolve_tac prems 1),
	(rtac ub_rangeI 1),
	(strip_tac 1),
	(res_inst_tac [("Q","x<i")] classical2 1),
	(res_inst_tac [("s","Y(i)"),("t","X(i)")] subst 1),
	(rtac sym 1),
	(fast_tac HOL_cs 1),
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

qed_goal "lub_equal2" Pcpo.thy 
"[|? j.!i. j<i --> X(i)=Y(i);is_chain(X::nat=>'a::pcpo);is_chain(Y)|]\
\ ==> lub(range(X))=lub(range(Y))"
 (fn prems =>
	[
	(rtac antisym_less 1),
	(rtac lub_mono2 1),
	(REPEAT (resolve_tac prems 1)),
	(cut_facts_tac prems 1),
	(rtac lub_mono2 1),
	(safe_tac HOL_cs),
	(step_tac HOL_cs 1),
	(safe_tac HOL_cs),
	(rtac sym 1),
	(fast_tac HOL_cs 1)
	]);

qed_goal "lub_mono3" Pcpo.thy "[|is_chain(Y::nat=>'a::pcpo);is_chain(X);\
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

qed_goal "eq_UU_iff" Pcpo.thy "(x=UU)=(x<<UU)"
 (fn prems =>
	[
	(rtac iffI 1),
	(hyp_subst_tac 1),
	(rtac refl_less 1),
	(rtac antisym_less 1),
	(atac 1),
	(rtac minimal 1)
	]);

qed_goal "UU_I" Pcpo.thy "x << UU ==> x = UU"
 (fn prems =>
	[
	(rtac (eq_UU_iff RS ssubst) 1),
	(resolve_tac prems 1)
	]);

qed_goal "not_less2not_eq" Pcpo.thy "~x<<y ==> ~x=y"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac classical3 1),
	(atac 1),
	(hyp_subst_tac 1),
	(rtac refl_less 1)
	]);

qed_goal "chain_UU_I" Pcpo.thy
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


qed_goal "chain_UU_I_inverse" Pcpo.thy 
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

qed_goal "chain_UU_I_inverse2" Pcpo.thy 
	"~lub(range(Y::(nat=>'a::pcpo)))=UU ==> ? i.~ Y(i)=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (notall2ex RS iffD1) 1),
	(rtac swap 1),
	(rtac chain_UU_I_inverse 2),
	(etac notnotD 2),
	(atac 1)
	]);


qed_goal "notUU_I" Pcpo.thy "[| x<<y; ~x=UU |] ==> ~y=UU"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(etac contrapos 1),
	(rtac UU_I 1),
	(hyp_subst_tac 1),
	(atac 1)
	]);


qed_goal "chain_mono2" Pcpo.thy 
"[|? j.~Y(j)=UU;is_chain(Y::nat=>'a::pcpo)|]\
\ ==> ? j.!i.j<i-->~Y(i)=UU"
 (fn prems =>
	[
	(cut_facts_tac prems 1),
	(safe_tac HOL_cs),
	(step_tac HOL_cs 1),
	(strip_tac 1),
	(rtac notUU_I 1),
	(atac 2),
	(etac (chain_mono RS mp) 1),
	(atac 1)
	]);




(* ------------------------------------------------------------------------ *)
(* uniqueness in void                                                       *)
(* ------------------------------------------------------------------------ *)

qed_goal "unique_void2" Pcpo.thy "(x::void)=UU"
 (fn prems =>
	[
	(rtac (inst_void_pcpo RS ssubst) 1),
	(rtac (Rep_Void_inverse RS subst) 1),
	(rtac (Rep_Void_inverse RS subst) 1),
	(rtac arg_cong 1),
	(rtac box_equals 1),
	(rtac refl 1),
	(rtac (unique_void RS sym) 1),
	(rtac (unique_void RS sym) 1)
	]);


