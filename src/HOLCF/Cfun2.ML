(*  Title:      HOLCF/cfun2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for cfun2.thy 
*)

open Cfun2;

(* for compatibility with old HOLCF-Version *)
qed_goal "inst_cfun_po" thy "(op <<)=(%f1 f2. Rep_CFun f1 << Rep_CFun f2)"
 (fn prems => 
        [
	(fold_goals_tac [less_cfun_def]),
	(rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* access to less_cfun in class po                                          *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_cfun" thy "( f1 << f2 ) = (Rep_CFun(f1) << Rep_CFun(f2))"
(fn prems =>
        [
        (simp_tac (simpset() addsimps [inst_cfun_po]) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Type 'a ->'b  is pointed                                                 *)
(* ------------------------------------------------------------------------ *)

qed_goal "minimal_cfun" thy "Abs_CFun(% x. UU) << f"
(fn prems =>
        [
        (stac less_cfun 1),
        (stac Abs_Cfun_inverse2 1),
        (rtac cont_const 1),
        (rtac minimal_fun 1)
        ]);

bind_thm ("UU_cfun_def",minimal_cfun RS minimal2UU RS sym);

qed_goal "least_cfun" thy "? x::'a->'b::pcpo.!y. x<<y"
(fn prems =>
        [
        (res_inst_tac [("x","Abs_CFun(% x. UU)")] exI 1),
        (rtac (minimal_cfun RS allI) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Rep_CFun yields continuous functions in 'a => 'b                             *)
(* this is continuity of Rep_CFun in its 'second' argument                      *)
(* cont_Rep_CFun2 ==> monofun_Rep_CFun2 & contlub_Rep_CFun2                            *)
(* ------------------------------------------------------------------------ *)

qed_goal "cont_Rep_CFun2" thy "cont(Rep_CFun(fo))"
(fn prems =>
        [
        (res_inst_tac [("P","cont")] CollectD 1),
        (fold_goals_tac [CFun_def]),
        (rtac Rep_Cfun 1)
        ]);

bind_thm ("monofun_Rep_CFun2", cont_Rep_CFun2 RS cont2mono);
(* monofun(Rep_CFun(?fo1)) *)


bind_thm ("contlub_Rep_CFun2", cont_Rep_CFun2 RS cont2contlub);
(* contlub(Rep_CFun(?fo1)) *)

(* ------------------------------------------------------------------------ *)
(* expanded thms cont_Rep_CFun2, contlub_Rep_CFun2                                 *)
(* looks nice with mixfix syntac                                            *)
(* ------------------------------------------------------------------------ *)

bind_thm ("cont_cfun_arg", (cont_Rep_CFun2 RS contE RS spec RS mp));
(* chain(?x1) ==> range (%i. ?fo3`(?x1 i)) <<| ?fo3`(lub (range ?x1))    *)
 
bind_thm ("contlub_cfun_arg", (contlub_Rep_CFun2 RS contlubE RS spec RS mp));
(* chain(?x1) ==> ?fo4`(lub (range ?x1)) = lub (range (%i. ?fo4`(?x1 i))) *)


(* ------------------------------------------------------------------------ *)
(* Rep_CFun is monotone in its 'first' argument                                 *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_Rep_CFun1" thy [monofun] "monofun(Rep_CFun)"
(fn prems =>
        [
        (strip_tac 1),
        (etac (less_cfun RS subst) 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* monotonicity of application Rep_CFun in mixfix syntax [_]_                   *)
(* ------------------------------------------------------------------------ *)

qed_goal "monofun_cfun_fun" thy  "f1 << f2 ==> f1`x << f2`x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("x","x")] spec 1),
        (rtac (less_fun RS subst) 1),
        (etac (monofun_Rep_CFun1 RS monofunE RS spec RS spec RS mp) 1)
        ]);


bind_thm ("monofun_cfun_arg", monofun_Rep_CFun2 RS monofunE RS spec RS spec RS mp);
(* ?x2 << ?x1 ==> ?fo5`?x2 << ?fo5`?x1                                      *)

(* ------------------------------------------------------------------------ *)
(* monotonicity of Rep_CFun in both arguments in mixfix syntax [_]_             *)
(* ------------------------------------------------------------------------ *)

qed_goal "monofun_cfun" thy
        "[|f1<<f2;x1<<x2|] ==> f1`x1 << f2`x2"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac trans_less 1),
        (etac monofun_cfun_arg 1),
        (etac monofun_cfun_fun 1)
        ]);


qed_goal "strictI" thy "f`x = UU ==> f`UU = UU" (fn prems => [
        cut_facts_tac prems 1,
        rtac (eq_UU_iff RS iffD2) 1,
        etac subst 1,
        rtac (minimal RS monofun_cfun_arg) 1]);


(* ------------------------------------------------------------------------ *)
(* ch2ch - rules for the type 'a -> 'b                                      *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

qed_goal "ch2ch_Rep_CFunR" thy 
 "chain(Y) ==> chain(%i. f`(Y i))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac (monofun_Rep_CFun2 RS ch2ch_MF2R) 1)
        ]);


bind_thm ("ch2ch_Rep_CFunL", monofun_Rep_CFun1 RS ch2ch_MF2L);
(* chain(?F) ==> chain (%i. ?F i`?x)                                  *)


(* ------------------------------------------------------------------------ *)
(*  the lub of a chain of continous functions is monotone                   *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_cfun_mono" thy 
        "chain(F) ==> monofun(% x. lub(range(% j.(F j)`x)))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac lub_MF2_mono 1),
        (rtac monofun_Rep_CFun1 1),
        (rtac (monofun_Rep_CFun2 RS allI) 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* a lemma about the exchange of lubs for type 'a -> 'b                     *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

qed_goal "ex_lubcfun" thy
        "[| chain(F); chain(Y) |] ==>\
\               lub(range(%j. lub(range(%i. F(j)`(Y i))))) =\
\               lub(range(%i. lub(range(%j. F(j)`(Y i)))))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac ex_lubMF2 1),
        (rtac monofun_Rep_CFun1 1),
        (rtac (monofun_Rep_CFun2 RS allI) 1),
        (atac 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* the lub of a chain of cont. functions is continuous                      *)
(* ------------------------------------------------------------------------ *)

qed_goal "cont_lubcfun" thy 
        "chain(F) ==> cont(% x. lub(range(% j. F(j)`x)))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac monocontlub2cont 1),
        (etac lub_cfun_mono 1),
        (rtac contlubI 1),
        (strip_tac 1),
        (stac (contlub_cfun_arg RS ext) 1),
        (atac 1),
        (etac ex_lubcfun 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* type 'a -> 'b is chain complete                                          *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_cfun" thy 
  "chain(CCF) ==> range(CCF) <<| (LAM x. lub(range(% i. CCF(i)`x)))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),  
        (rtac allI 1),
        (stac less_cfun 1),
        (stac Abs_Cfun_inverse2 1),
        (etac cont_lubcfun 1),
        (rtac (lub_fun RS is_lubE RS conjunct1 RS ub_rangeE RS spec) 1),
        (etac (monofun_Rep_CFun1 RS ch2ch_monofun) 1),
        (strip_tac 1),
        (stac less_cfun 1),
        (stac Abs_Cfun_inverse2 1),
        (etac cont_lubcfun 1),
        (rtac (lub_fun RS is_lubE RS conjunct2 RS spec RS mp) 1),
        (etac (monofun_Rep_CFun1 RS ch2ch_monofun) 1),
        (etac (monofun_Rep_CFun1 RS ub2ub_monofun) 1)
        ]);

bind_thm ("thelub_cfun", lub_cfun RS thelubI);
(* 
chain(?CCF1) ==>  lub (range ?CCF1) = (LAM x. lub (range (%i. ?CCF1 i`x)))
*)

qed_goal "cpo_cfun" thy 
  "chain(CCF::nat=>('a->'b)) ==> ? x. range(CCF) <<| x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac exI 1),
        (etac lub_cfun 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Extensionality in 'a -> 'b                                               *)
(* ------------------------------------------------------------------------ *)

qed_goal "ext_cfun" Cfun1.thy "(!!x. f`x = g`x) ==> f = g"
 (fn prems =>
        [
        (res_inst_tac [("t","f")] (Rep_Cfun_inverse RS subst) 1),
        (res_inst_tac [("t","g")] (Rep_Cfun_inverse RS subst) 1),
        (res_inst_tac [("f","Abs_CFun")] arg_cong 1),
        (rtac ext 1),
        (resolve_tac prems 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Monotonicity of Abs_CFun                                                     *)
(* ------------------------------------------------------------------------ *)

qed_goal "semi_monofun_Abs_CFun" thy 
        "[|cont(f);cont(g);f<<g|]==>Abs_CFun(f)<<Abs_CFun(g)"
 (fn prems =>
        [
        (rtac (less_cfun RS iffD2) 1),
        (stac Abs_Cfun_inverse2 1),
        (resolve_tac prems 1),
        (stac Abs_Cfun_inverse2 1),
        (resolve_tac prems 1),
        (resolve_tac prems 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Extenionality wrt. << in 'a -> 'b                                        *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_cfun2" thy "(!!x. f`x << g`x) ==> f << g"
 (fn prems =>
        [
        (res_inst_tac [("t","f")] (Rep_Cfun_inverse RS subst) 1),
        (res_inst_tac [("t","g")] (Rep_Cfun_inverse RS subst) 1),
        (rtac semi_monofun_Abs_CFun 1),
        (rtac cont_Rep_CFun2 1),
        (rtac cont_Rep_CFun2 1),
        (rtac (less_fun RS iffD2) 1),
        (rtac allI 1),
        (resolve_tac prems 1)
        ]);


