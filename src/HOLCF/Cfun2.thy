(*  Title:      HOLCF/Cfun2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance ->::(cpo,cpo)po

*)

theory Cfun2 = Cfun1:

instance "->"::(cpo,cpo)po
apply (intro_classes)
apply (rule refl_less_cfun)
apply (rule antisym_less_cfun, assumption+)
apply (rule trans_less_cfun, assumption+)
done

(*  Title:      HOLCF/Cfun2
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance ->::(cpo,cpo)po
*)

(* for compatibility with old HOLCF-Version *)
lemma inst_cfun_po: "(op <<)=(%f1 f2. Rep_CFun f1 << Rep_CFun f2)"
apply (fold less_cfun_def)
apply (rule refl)
done

(* ------------------------------------------------------------------------ *)
(* access to less_cfun in class po                                          *)
(* ------------------------------------------------------------------------ *)

lemma less_cfun: "( f1 << f2 ) = (Rep_CFun(f1) << Rep_CFun(f2))"
apply (simp (no_asm) add: inst_cfun_po)
done

(* ------------------------------------------------------------------------ *)
(* Type 'a ->'b  is pointed                                                 *)
(* ------------------------------------------------------------------------ *)

lemma minimal_cfun: "Abs_CFun(% x. UU) << f"
apply (subst less_cfun)
apply (subst Abs_Cfun_inverse2)
apply (rule cont_const)
apply (rule minimal_fun)
done

lemmas UU_cfun_def = minimal_cfun [THEN minimal2UU, symmetric, standard]

lemma least_cfun: "? x::'a->'b::pcpo.!y. x<<y"
apply (rule_tac x = "Abs_CFun (% x. UU) " in exI)
apply (rule minimal_cfun [THEN allI])
done

(* ------------------------------------------------------------------------ *)
(* Rep_CFun yields continuous functions in 'a => 'b                             *)
(* this is continuity of Rep_CFun in its 'second' argument                      *)
(* cont_Rep_CFun2 ==> monofun_Rep_CFun2 & contlub_Rep_CFun2                            *)
(* ------------------------------------------------------------------------ *)

lemma cont_Rep_CFun2: "cont(Rep_CFun(fo))"
apply (rule_tac P = "cont" in CollectD)
apply (fold CFun_def)
apply (rule Rep_Cfun)
done

lemmas monofun_Rep_CFun2 = cont_Rep_CFun2 [THEN cont2mono, standard]
(* monofun(Rep_CFun(?fo1)) *)


lemmas contlub_Rep_CFun2 = cont_Rep_CFun2 [THEN cont2contlub, standard]
(* contlub(Rep_CFun(?fo1)) *)

(* ------------------------------------------------------------------------ *)
(* expanded thms cont_Rep_CFun2, contlub_Rep_CFun2                                 *)
(* looks nice with mixfix syntac                                            *)
(* ------------------------------------------------------------------------ *)

lemmas cont_cfun_arg = cont_Rep_CFun2 [THEN contE, THEN spec, THEN mp]
(* chain(?x1) ==> range (%i. ?fo3$(?x1 i)) <<| ?fo3$(lub (range ?x1))    *)
 
lemmas contlub_cfun_arg = contlub_Rep_CFun2 [THEN contlubE, THEN spec, THEN mp]
(* chain(?x1) ==> ?fo4$(lub (range ?x1)) = lub (range (%i. ?fo4$(?x1 i))) *)


(* ------------------------------------------------------------------------ *)
(* Rep_CFun is monotone in its 'first' argument                                 *)
(* ------------------------------------------------------------------------ *)

lemma monofun_Rep_CFun1: "monofun(Rep_CFun)"
apply (unfold monofun)
apply (intro strip)
apply (erule less_cfun [THEN subst])
done


(* ------------------------------------------------------------------------ *)
(* monotonicity of application Rep_CFun in mixfix syntax [_]_                   *)
(* ------------------------------------------------------------------------ *)

lemma monofun_cfun_fun: "f1 << f2 ==> f1$x << f2$x"
apply (rule_tac x = "x" in spec)
apply (rule less_fun [THEN subst])
apply (erule monofun_Rep_CFun1 [THEN monofunE, THEN spec, THEN spec, THEN mp])
done


lemmas monofun_cfun_arg = monofun_Rep_CFun2 [THEN monofunE, THEN spec, THEN spec, THEN mp, standard]
(* ?x2 << ?x1 ==> ?fo5$?x2 << ?fo5$?x1                                      *)

lemma chain_monofun: "chain Y ==> chain (%i. f\<cdot>(Y i))"
apply (rule chainI)
apply (rule monofun_cfun_arg)
apply (erule chainE)
done


(* ------------------------------------------------------------------------ *)
(* monotonicity of Rep_CFun in both arguments in mixfix syntax [_]_             *)
(* ------------------------------------------------------------------------ *)

lemma monofun_cfun: "[|f1<<f2;x1<<x2|] ==> f1$x1 << f2$x2"
apply (rule trans_less)
apply (erule monofun_cfun_arg)
apply (erule monofun_cfun_fun)
done


lemma strictI: "f$x = UU ==> f$UU = UU"
apply (rule eq_UU_iff [THEN iffD2])
apply (erule subst)
apply (rule minimal [THEN monofun_cfun_arg])
done


(* ------------------------------------------------------------------------ *)
(* ch2ch - rules for the type 'a -> 'b                                      *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

lemma ch2ch_Rep_CFunR: "chain(Y) ==> chain(%i. f$(Y i))"
apply (erule monofun_Rep_CFun2 [THEN ch2ch_MF2R])
done


lemmas ch2ch_Rep_CFunL = monofun_Rep_CFun1 [THEN ch2ch_MF2L, standard]
(* chain(?F) ==> chain (%i. ?F i$?x)                                  *)


(* ------------------------------------------------------------------------ *)
(*  the lub of a chain of continous functions is monotone                   *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

lemma lub_cfun_mono: "chain(F) ==> monofun(% x. lub(range(% j.(F j)$x)))"
apply (rule lub_MF2_mono)
apply (rule monofun_Rep_CFun1)
apply (rule monofun_Rep_CFun2 [THEN allI])
apply assumption
done

(* ------------------------------------------------------------------------ *)
(* a lemma about the exchange of lubs for type 'a -> 'b                     *)
(* use MF2 lemmas from Cont.ML                                              *)
(* ------------------------------------------------------------------------ *)

lemma ex_lubcfun: "[| chain(F); chain(Y) |] ==> 
                lub(range(%j. lub(range(%i. F(j)$(Y i))))) = 
                lub(range(%i. lub(range(%j. F(j)$(Y i)))))"
apply (rule ex_lubMF2)
apply (rule monofun_Rep_CFun1)
apply (rule monofun_Rep_CFun2 [THEN allI])
apply assumption
apply assumption
done

(* ------------------------------------------------------------------------ *)
(* the lub of a chain of cont. functions is continuous                      *)
(* ------------------------------------------------------------------------ *)

lemma cont_lubcfun: "chain(F) ==> cont(% x. lub(range(% j. F(j)$x)))"
apply (rule monocontlub2cont)
apply (erule lub_cfun_mono)
apply (rule contlubI)
apply (intro strip)
apply (subst contlub_cfun_arg [THEN ext])
apply assumption
apply (erule ex_lubcfun)
apply assumption
done

(* ------------------------------------------------------------------------ *)
(* type 'a -> 'b is chain complete                                          *)
(* ------------------------------------------------------------------------ *)

lemma lub_cfun: "chain(CCF) ==> range(CCF) <<| (LAM x. lub(range(% i. CCF(i)$x)))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (subst less_cfun)
apply (subst Abs_Cfun_inverse2)
apply (erule cont_lubcfun)
apply (rule lub_fun [THEN is_lubD1, THEN ub_rangeD])
apply (erule monofun_Rep_CFun1 [THEN ch2ch_monofun])
apply (subst less_cfun)
apply (subst Abs_Cfun_inverse2)
apply (erule cont_lubcfun)
apply (rule lub_fun [THEN is_lub_lub])
apply (erule monofun_Rep_CFun1 [THEN ch2ch_monofun])
apply (erule monofun_Rep_CFun1 [THEN ub2ub_monofun])
done

lemmas thelub_cfun = lub_cfun [THEN thelubI, standard]
(* 
chain(?CCF1) ==>  lub (range ?CCF1) = (LAM x. lub (range (%i. ?CCF1 i$x)))
*)

lemma cpo_cfun: "chain(CCF::nat=>('a->'b)) ==> ? x. range(CCF) <<| x"
apply (rule exI)
apply (erule lub_cfun)
done


(* ------------------------------------------------------------------------ *)
(* Extensionality in 'a -> 'b                                               *)
(* ------------------------------------------------------------------------ *)

lemma ext_cfun: "(!!x. f$x = g$x) ==> f = g"
apply (rule_tac t = "f" in Rep_Cfun_inverse [THEN subst])
apply (rule_tac t = "g" in Rep_Cfun_inverse [THEN subst])
apply (rule_tac f = "Abs_CFun" in arg_cong)
apply (rule ext)
apply simp
done

(* ------------------------------------------------------------------------ *)
(* Monotonicity of Abs_CFun                                                     *)
(* ------------------------------------------------------------------------ *)

lemma semi_monofun_Abs_CFun: "[| cont(f); cont(g); f<<g|] ==> Abs_CFun(f)<<Abs_CFun(g)"
apply (rule less_cfun [THEN iffD2])
apply (subst Abs_Cfun_inverse2)
apply assumption
apply (subst Abs_Cfun_inverse2)
apply assumption
apply assumption
done

(* ------------------------------------------------------------------------ *)
(* Extenionality wrt. << in 'a -> 'b                                        *)
(* ------------------------------------------------------------------------ *)

lemma less_cfun2: "(!!x. f$x << g$x) ==> f << g"
apply (rule_tac t = "f" in Rep_Cfun_inverse [THEN subst])
apply (rule_tac t = "g" in Rep_Cfun_inverse [THEN subst])
apply (rule semi_monofun_Abs_CFun)
apply (rule cont_Rep_CFun2)
apply (rule cont_Rep_CFun2)
apply (rule less_fun [THEN iffD2])
apply (rule allI)
apply simp
done

end
