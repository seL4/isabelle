(*  Title:      HOLCF/Cfun2
    ID:         $Id$
    Author:     Franz Regensburger

Class Instance ->::(cpo,cpo)po
*)

(* for compatibility with old HOLCF-Version *)
Goal "(op <<)=(%f1 f2. Rep_CFun f1 << Rep_CFun f2)";
by (fold_goals_tac [less_cfun_def]);
by (rtac refl 1);
qed "inst_cfun_po";

(* ------------------------------------------------------------------------ *)
(* access to less_cfun in class po                                          *)
(* ------------------------------------------------------------------------ *)

Goal "( f1 << f2 ) = (Rep_CFun(f1) << Rep_CFun(f2))";
by (simp_tac (simpset() addsimps [inst_cfun_po]) 1);
qed "less_cfun";

(* ------------------------------------------------------------------------ *)
(* Type 'a ->'b  is pointed                                                 *)
(* ------------------------------------------------------------------------ *)

Goal "Abs_CFun(% x. UU) << f";
by (stac less_cfun 1);
by (stac Abs_Cfun_inverse2 1);
by (rtac cont_const 1);
by (rtac minimal_fun 1);
qed "minimal_cfun";

bind_thm ("UU_cfun_def",minimal_cfun RS minimal2UU RS sym);

Goal "? x::'a->'b::pcpo.!y. x<<y";
by (res_inst_tac [("x","Abs_CFun(% x. UU)")] exI 1);
by (rtac (minimal_cfun RS allI) 1);
qed "least_cfun";

(* ------------------------------------------------------------------------ *)
(* Rep_CFun yields continuous functions in 'a => 'b                             *)
(* this is continuity of Rep_CFun in its 'second' argument                      *)
(* cont_Rep_CFun2 ==> monofun_Rep_CFun2 & contlub_Rep_CFun2                            *)
(* ------------------------------------------------------------------------ *)

Goal "cont(Rep_CFun(fo))";
by (res_inst_tac [("P","cont")] CollectD 1);
by (fold_goals_tac [CFun_def]);
by (rtac Rep_Cfun 1);
qed "cont_Rep_CFun2";

bind_thm ("monofun_Rep_CFun2", cont_Rep_CFun2 RS cont2mono);
(* monofun(Rep_CFun(?fo1)) *)


bind_thm ("contlub_Rep_CFun2", cont_Rep_CFun2 RS cont2contlub);
(* contlub(Rep_CFun(?fo1)) *)

(* ------------------------------------------------------------------------ *)
(* expanded thms cont_Rep_CFun2, contlub_Rep_CFun2                                 *)
(* looks nice with mixfix syntac                                            *)
(* ------------------------------------------------------------------------ *)

bind_thm ("cont_cfun_arg", (cont_Rep_CFun2 RS contE RS spec RS mp));
(* chain(?x1) ==> range (%i. ?fo3$(?x1 i)) <<| ?fo3$(lub (range ?x1))    *)
 
bind_thm ("contlub_cfun_arg", (contlub_Rep_CFun2 RS contlubE RS spec RS mp));
(* chain(?x1) ==> ?fo4$(lub (range ?x1)) = lub (range (%i. ?fo4$(?x1 i))) *)


(* ------------------------------------------------------------------------ *)
(* Rep_CFun is monotone in its 'first' argument                                 *)
(* ------------------------------------------------------------------------ *)

Goalw [monofun] "monofun(Rep_CFun)";
by (strip_tac 1);
by (etac (less_cfun RS subst) 1);
qed "monofun_Rep_CFun1";


(* ------------------------------------------------------------------------ *)
(* monotonicity of application Rep_CFun in mixfix syntax [_]_                   *)
(* ------------------------------------------------------------------------ *)

Goal  "f1 << f2 ==> f1$x << f2$x";
by (res_inst_tac [("x","x")] spec 1);
by (rtac (less_fun RS subst) 1);
by (etac (monofun_Rep_CFun1 RS monofunE RS spec RS spec RS mp) 1);
qed "monofun_cfun_fun";


bind_thm ("monofun_cfun_arg", monofun_Rep_CFun2 RS monofunE RS spec RS spec RS mp);
(* ?x2 << ?x1 ==> ?fo5$?x2 << ?fo5$?x1                                      *)

Goal "chain Y ==> chain (%i. f\\<cdot>(Y i))";
by (rtac chainI 1);
by (rtac monofun_cfun_arg 1);
by (etac chainE 1);
qed "chain_monofun";


(* ------------------------------------------------------------------------ *)
(* monotonicity of Rep_CFun in both arguments in mixfix syntax [_]_             *)
(* ------------------------------------------------------------------------ *)

Goal "[|f1<<f2;x1<<x2|] ==> f1$x1 << f2$x2";
by (rtac trans_less 1);
by (etac monofun_cfun_arg 1);
by (etac monofun_cfun_fun 1);
qed "monofun_cfun";


Goal "f$x = UU ==> f$UU = UU";
by (rtac (eq_UU_iff RS iffD2) 1);
by (etac subst 1);
by (rtac (minimal RS monofun_cfun_arg) 1);
qed "strictI";


(* ------------------------------------------------------------------------ *)
(* ch2ch - rules for the type 'a -> 'b                                      *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

Goal "chain(Y) ==> chain(%i. f$(Y i))";
by (etac (monofun_Rep_CFun2 RS ch2ch_MF2R) 1);
qed "ch2ch_Rep_CFunR";


bind_thm ("ch2ch_Rep_CFunL", monofun_Rep_CFun1 RS ch2ch_MF2L);
(* chain(?F) ==> chain (%i. ?F i$?x)                                  *)


(* ------------------------------------------------------------------------ *)
(*  the lub of a chain of continous functions is monotone                   *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

Goal "chain(F) ==> monofun(% x. lub(range(% j.(F j)$x)))";
by (rtac lub_MF2_mono 1);
by (rtac monofun_Rep_CFun1 1);
by (rtac (monofun_Rep_CFun2 RS allI) 1);
by (atac 1);
qed "lub_cfun_mono";

(* ------------------------------------------------------------------------ *)
(* a lemma about the exchange of lubs for type 'a -> 'b                     *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

Goal "[| chain(F); chain(Y) |] ==>\
\               lub(range(%j. lub(range(%i. F(j)$(Y i))))) =\
\               lub(range(%i. lub(range(%j. F(j)$(Y i)))))";
by (rtac ex_lubMF2 1);
by (rtac monofun_Rep_CFun1 1);
by (rtac (monofun_Rep_CFun2 RS allI) 1);
by (atac 1);
by (atac 1);
qed "ex_lubcfun";

(* ------------------------------------------------------------------------ *)
(* the lub of a chain of cont. functions is continuous                      *)
(* ------------------------------------------------------------------------ *)

Goal "chain(F) ==> cont(% x. lub(range(% j. F(j)$x)))";
by (rtac monocontlub2cont 1);
by (etac lub_cfun_mono 1);
by (rtac contlubI 1);
by (strip_tac 1);
by (stac (contlub_cfun_arg RS ext) 1);
by (atac 1);
by (etac ex_lubcfun 1);
by (atac 1);
qed "cont_lubcfun";

(* ------------------------------------------------------------------------ *)
(* type 'a -> 'b is chain complete                                          *)
(* ------------------------------------------------------------------------ *)

Goal "chain(CCF) ==> range(CCF) <<| (LAM x. lub(range(% i. CCF(i)$x)))";
by (rtac is_lubI 1);
by (rtac ub_rangeI 1);
by (stac less_cfun 1);
by (stac Abs_Cfun_inverse2 1);
by (etac cont_lubcfun 1);
by (rtac (lub_fun RS is_lubD1 RS ub_rangeD) 1);
by (etac (monofun_Rep_CFun1 RS ch2ch_monofun) 1);
by (stac less_cfun 1);
by (stac Abs_Cfun_inverse2 1);
by (etac cont_lubcfun 1);
by (rtac (lub_fun RS is_lub_lub) 1);
by (etac (monofun_Rep_CFun1 RS ch2ch_monofun) 1);
by (etac (monofun_Rep_CFun1 RS ub2ub_monofun) 1);
qed "lub_cfun";

bind_thm ("thelub_cfun", lub_cfun RS thelubI);
(* 
chain(?CCF1) ==>  lub (range ?CCF1) = (LAM x. lub (range (%i. ?CCF1 i$x)))
*)

Goal "chain(CCF::nat=>('a->'b)) ==> ? x. range(CCF) <<| x";
by (rtac exI 1);
by (etac lub_cfun 1);
qed "cpo_cfun";


(* ------------------------------------------------------------------------ *)
(* Extensionality in 'a -> 'b                                               *)
(* ------------------------------------------------------------------------ *)

val prems = Goal "(!!x. f$x = g$x) ==> f = g";
by (res_inst_tac [("t","f")] (Rep_Cfun_inverse RS subst) 1);
by (res_inst_tac [("t","g")] (Rep_Cfun_inverse RS subst) 1);
by (res_inst_tac [("f","Abs_CFun")] arg_cong 1);
by (rtac ext 1);
by (resolve_tac prems 1);
qed "ext_cfun";

(* ------------------------------------------------------------------------ *)
(* Monotonicity of Abs_CFun                                                     *)
(* ------------------------------------------------------------------------ *)

Goal "[| cont(f); cont(g); f<<g|] ==> Abs_CFun(f)<<Abs_CFun(g)";
by (rtac (less_cfun RS iffD2) 1);
by (stac Abs_Cfun_inverse2 1);
by (assume_tac 1);
by (stac Abs_Cfun_inverse2 1);
by (assume_tac 1);
by (assume_tac 1);
qed "semi_monofun_Abs_CFun";

(* ------------------------------------------------------------------------ *)
(* Extenionality wrt. << in 'a -> 'b                                        *)
(* ------------------------------------------------------------------------ *)

val prems = Goal "(!!x. f$x << g$x) ==> f << g";
by (res_inst_tac [("t","f")] (Rep_Cfun_inverse RS subst) 1);
by (res_inst_tac [("t","g")] (Rep_Cfun_inverse RS subst) 1);
by (rtac semi_monofun_Abs_CFun 1);
by (rtac cont_Rep_CFun2 1);
by (rtac cont_Rep_CFun2 1);
by (rtac (less_fun RS iffD2) 1);
by (rtac allI 1);
by (resolve_tac prems 1);
qed "less_cfun2";


