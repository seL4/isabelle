(*  Title:      HOLCF/cfun2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for cfun2.thy 
*)

open Cfun2;

(* ------------------------------------------------------------------------ *)
(* access to less_cfun in class po                                          *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_cfun" Cfun2.thy "( f1 << f2 ) = (fapp(f1) << fapp(f2))"
(fn prems =>
        [
        (rtac (inst_cfun_po RS ssubst) 1),
        (fold_goals_tac [less_cfun_def]),
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Type 'a ->'b  is pointed                                                 *)
(* ------------------------------------------------------------------------ *)

qed_goalw "minimal_cfun" Cfun2.thy [UU_cfun_def] "UU_cfun << f"
(fn prems =>
        [
        (rtac (less_cfun RS ssubst) 1),
        (rtac (Abs_Cfun_inverse2 RS ssubst) 1),
        (rtac cont_const 1),
        (fold_goals_tac [UU_fun_def]),
        (rtac minimal_fun 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* fapp yields continuous functions in 'a => 'b                             *)
(* this is continuity of fapp in its 'second' argument                      *)
(* cont_fapp2 ==> monofun_fapp2 & contlub_fapp2                            *)
(* ------------------------------------------------------------------------ *)

qed_goal "cont_fapp2" Cfun2.thy "cont(fapp(fo))"
(fn prems =>
        [
        (res_inst_tac [("P","cont")] CollectD 1),
        (fold_goals_tac [Cfun_def]),
        (rtac Rep_Cfun 1)
        ]);

val monofun_fapp2 = cont_fapp2 RS cont2mono;
(* monofun(fapp(?fo1)) *)


val contlub_fapp2 = cont_fapp2 RS cont2contlub;
(* contlub(fapp(?fo1)) *)

(* ------------------------------------------------------------------------ *)
(* expanded thms cont_fapp2, contlub_fapp2                                 *)
(* looks nice with mixfix syntac                                            *)
(* ------------------------------------------------------------------------ *)

val cont_cfun_arg = (cont_fapp2 RS contE RS spec RS mp);
(* is_chain(?x1) ==> range (%i. ?fo3`(?x1 i)) <<| ?fo3`(lub (range ?x1))    *)
 
val contlub_cfun_arg = (contlub_fapp2 RS contlubE RS spec RS mp);
(* is_chain(?x1) ==> ?fo4`(lub (range ?x1)) = lub (range (%i. ?fo4`(?x1 i))) *)


(* ------------------------------------------------------------------------ *)
(* fapp is monotone in its 'first' argument                                 *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_fapp1" Cfun2.thy [monofun] "monofun(fapp)"
(fn prems =>
        [
        (strip_tac 1),
        (etac (less_cfun RS subst) 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* monotonicity of application fapp in mixfix syntax [_]_                   *)
(* ------------------------------------------------------------------------ *)

qed_goal "monofun_cfun_fun" Cfun2.thy  "f1 << f2 ==> f1`x << f2`x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("x","x")] spec 1),
        (rtac (less_fun RS subst) 1),
        (etac (monofun_fapp1 RS monofunE RS spec RS spec RS mp) 1)
        ]);


val monofun_cfun_arg = (monofun_fapp2 RS monofunE RS spec RS spec RS mp);
(* ?x2 << ?x1 ==> ?fo5`?x2 << ?fo5`?x1                                      *)

(* ------------------------------------------------------------------------ *)
(* monotonicity of fapp in both arguments in mixfix syntax [_]_             *)
(* ------------------------------------------------------------------------ *)

qed_goal "monofun_cfun" Cfun2.thy
        "[|f1<<f2;x1<<x2|] ==> f1`x1 << f2`x2"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac trans_less 1),
        (etac monofun_cfun_arg 1),
        (etac monofun_cfun_fun 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* ch2ch - rules for the type 'a -> 'b                                      *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

qed_goal "ch2ch_fappR" Cfun2.thy 
 "is_chain(Y) ==> is_chain(%i. f`(Y i))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac (monofun_fapp2 RS ch2ch_MF2R) 1)
        ]);


val ch2ch_fappL = (monofun_fapp1 RS ch2ch_MF2L);
(* is_chain(?F) ==> is_chain (%i. ?F i`?x)                                  *)


(* ------------------------------------------------------------------------ *)
(*  the lub of a chain of continous functions is monotone                   *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_cfun_mono" Cfun2.thy 
        "is_chain(F) ==> monofun(% x.lub(range(% j.(F j)`x)))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac lub_MF2_mono 1),
        (rtac monofun_fapp1 1),
        (rtac (monofun_fapp2 RS allI) 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* a lemma about the exchange of lubs for type 'a -> 'b                     *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

qed_goal "ex_lubcfun" Cfun2.thy
        "[| is_chain(F); is_chain(Y) |] ==>\
\               lub(range(%j. lub(range(%i. F(j)`(Y i))))) =\
\               lub(range(%i. lub(range(%j. F(j)`(Y i)))))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac ex_lubMF2 1),
        (rtac monofun_fapp1 1),
        (rtac (monofun_fapp2 RS allI) 1),
        (atac 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* the lub of a chain of cont. functions is continuous                      *)
(* ------------------------------------------------------------------------ *)

qed_goal "cont_lubcfun" Cfun2.thy 
        "is_chain(F) ==> cont(% x.lub(range(% j.F(j)`x)))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac monocontlub2cont 1),
        (etac lub_cfun_mono 1),
        (rtac contlubI 1),
        (strip_tac 1),
        (rtac (contlub_cfun_arg RS ext RS ssubst) 1),
        (atac 1),
        (etac ex_lubcfun 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* type 'a -> 'b is chain complete                                          *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_cfun" Cfun2.thy 
  "is_chain(CCF) ==> range(CCF) <<| (LAM x.lub(range(% i.CCF(i)`x)))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),  
        (rtac allI 1),
        (rtac (less_cfun RS ssubst) 1),
        (rtac (Abs_Cfun_inverse2 RS ssubst) 1),
        (etac cont_lubcfun 1),
        (rtac (lub_fun RS is_lubE RS conjunct1 RS ub_rangeE RS spec) 1),
        (etac (monofun_fapp1 RS ch2ch_monofun) 1),
        (strip_tac 1),
        (rtac (less_cfun RS ssubst) 1),
        (rtac (Abs_Cfun_inverse2 RS ssubst) 1),
        (etac cont_lubcfun 1),
        (rtac (lub_fun RS is_lubE RS conjunct2 RS spec RS mp) 1),
        (etac (monofun_fapp1 RS ch2ch_monofun) 1),
        (etac (monofun_fapp1 RS ub2ub_monofun) 1)
        ]);

val thelub_cfun = (lub_cfun RS thelubI);
(* 
is_chain(?CCF1) ==>  lub (range ?CCF1) = (LAM x. lub (range (%i. ?CCF1 i`x)))
*)

qed_goal "cpo_cfun" Cfun2.thy 
  "is_chain(CCF::nat=>('a::pcpo->'b::pcpo)) ==> ? x. range(CCF) <<| x"
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
        (res_inst_tac [("f","fabs")] arg_cong 1),
        (rtac ext 1),
        (resolve_tac prems 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Monotonicity of fabs                                                     *)
(* ------------------------------------------------------------------------ *)

qed_goal "semi_monofun_fabs" Cfun2.thy 
        "[|cont(f);cont(g);f<<g|]==>fabs(f)<<fabs(g)"
 (fn prems =>
        [
        (rtac (less_cfun RS iffD2) 1),
        (rtac (Abs_Cfun_inverse2 RS ssubst) 1),
        (resolve_tac prems 1),
        (rtac (Abs_Cfun_inverse2 RS ssubst) 1),
        (resolve_tac prems 1),
        (resolve_tac prems 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Extenionality wrt. << in 'a -> 'b                                        *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_cfun2" Cfun2.thy "(!!x. f`x << g`x) ==> f << g"
 (fn prems =>
        [
        (res_inst_tac [("t","f")] (Rep_Cfun_inverse RS subst) 1),
        (res_inst_tac [("t","g")] (Rep_Cfun_inverse RS subst) 1),
        (rtac semi_monofun_fabs 1),
        (rtac cont_fapp2 1),
        (rtac cont_fapp2 1),
        (rtac (less_fun RS iffD2) 1),
        (rtac allI 1),
        (resolve_tac prems 1)
        ]);


