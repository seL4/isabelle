(*  Title:      HOLCF/ssum3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class instance of  ++ for class pcpo
*)

theory Ssum3 = Ssum2:

instance "++" :: (pcpo,pcpo)pcpo
apply (intro_classes)
apply (erule cpo_ssum)
apply (rule least_ssum)
done

consts  
        sinl    :: "'a -> ('a++'b)" 
        sinr    :: "'b -> ('a++'b)" 
        sscase  :: "('a->'c)->('b->'c)->('a ++ 'b)-> 'c"

defs

sinl_def:        "sinl   == (LAM x. Isinl(x))"
sinr_def:        "sinr   == (LAM x. Isinr(x))"
sscase_def:      "sscase   == (LAM f g s. Iwhen(f)(g)(s))"

translations
"case s of sinl$x => t1 | sinr$y => t2" == "sscase$(LAM x. t1)$(LAM y. t2)$s"

(*  Title:      HOLCF/Ssum3.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class instance of  ++ for class pcpo
*)

(* for compatibility with old HOLCF-Version *)
lemma inst_ssum_pcpo: "UU = Isinl UU"
apply (simp add: UU_def UU_ssum_def)
done

declare inst_ssum_pcpo [symmetric, simp]

(* ------------------------------------------------------------------------ *)
(* continuity for Isinl and Isinr                                           *)
(* ------------------------------------------------------------------------ *)

lemma contlub_Isinl: "contlub(Isinl)"
apply (rule contlubI)
apply (intro strip)
apply (rule trans)
apply (rule_tac [2] thelub_ssum1a [symmetric])
apply (rule_tac [3] allI)
apply (rule_tac [3] exI)
apply (rule_tac [3] refl)
apply (erule_tac [2] monofun_Isinl [THEN ch2ch_monofun])
apply (case_tac "lub (range (Y))=UU")
apply (rule_tac s = "UU" and t = "lub (range (Y))" in ssubst)
apply assumption
apply (rule_tac f = "Isinl" in arg_cong)
apply (rule chain_UU_I_inverse [symmetric])
apply (rule allI)
apply (rule_tac s = "UU" and t = "Y (i) " in ssubst)
apply (erule chain_UU_I [THEN spec])
apply assumption
apply (rule Iwhen1)
apply (rule_tac f = "Isinl" in arg_cong)
apply (rule lub_equal)
apply assumption
apply (rule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (erule monofun_Isinl [THEN ch2ch_monofun])
apply (rule allI)
apply (case_tac "Y (k) =UU")
apply (erule ssubst)
apply (rule Iwhen1[symmetric])
apply simp
done

lemma contlub_Isinr: "contlub(Isinr)"
apply (rule contlubI)
apply (intro strip)
apply (rule trans)
apply (rule_tac [2] thelub_ssum1b [symmetric])
apply (rule_tac [3] allI)
apply (rule_tac [3] exI)
apply (rule_tac [3] refl)
apply (erule_tac [2] monofun_Isinr [THEN ch2ch_monofun])
apply (case_tac "lub (range (Y))=UU")
apply (rule_tac s = "UU" and t = "lub (range (Y))" in ssubst)
apply assumption
apply (rule arg_cong, rule chain_UU_I_inverse [symmetric])
apply (rule allI)
apply (rule_tac s = "UU" and t = "Y (i) " in ssubst)
apply (erule chain_UU_I [THEN spec])
apply assumption
apply (rule strict_IsinlIsinr [THEN subst])
apply (rule Iwhen1)
apply (rule arg_cong, rule lub_equal)
apply assumption
apply (rule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (erule monofun_Isinr [THEN ch2ch_monofun])
apply (rule allI)
apply (case_tac "Y (k) =UU")
apply (simp only: Ssum0_ss)
apply simp
done

lemma cont_Isinl: "cont(Isinl)"
apply (rule monocontlub2cont)
apply (rule monofun_Isinl)
apply (rule contlub_Isinl)
done

lemma cont_Isinr: "cont(Isinr)"
apply (rule monocontlub2cont)
apply (rule monofun_Isinr)
apply (rule contlub_Isinr)
done

declare cont_Isinl [iff] cont_Isinr [iff]


(* ------------------------------------------------------------------------ *)
(* continuity for Iwhen in the firts two arguments                          *)
(* ------------------------------------------------------------------------ *)

lemma contlub_Iwhen1: "contlub(Iwhen)"
apply (rule contlubI)
apply (intro strip)
apply (rule trans)
apply (rule_tac [2] thelub_fun [symmetric])
apply (erule_tac [2] monofun_Iwhen1 [THEN ch2ch_monofun])
apply (rule expand_fun_eq [THEN iffD2])
apply (intro strip)
apply (rule trans)
apply (rule_tac [2] thelub_fun [symmetric])
apply (rule_tac [2] ch2ch_fun)
apply (erule_tac [2] monofun_Iwhen1 [THEN ch2ch_monofun])
apply (rule expand_fun_eq [THEN iffD2])
apply (intro strip)
apply (rule_tac p = "xa" in IssumE)
apply (simp only: Ssum0_ss)
apply (rule lub_const [THEN thelubI, symmetric])
apply simp
apply (erule contlub_cfun_fun)
apply simp
apply (rule lub_const [THEN thelubI, symmetric])
done

lemma contlub_Iwhen2: "contlub(Iwhen(f))"
apply (rule contlubI)
apply (intro strip)
apply (rule trans)
apply (rule_tac [2] thelub_fun [symmetric])
apply (erule_tac [2] monofun_Iwhen2 [THEN ch2ch_monofun])
apply (rule expand_fun_eq [THEN iffD2])
apply (intro strip)
apply (rule_tac p = "x" in IssumE)
apply (simp only: Ssum0_ss)
apply (rule lub_const [THEN thelubI, symmetric])
apply simp
apply (rule lub_const [THEN thelubI, symmetric])
apply simp
apply (erule contlub_cfun_fun)
done

(* ------------------------------------------------------------------------ *)
(* continuity for Iwhen in its third argument                               *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* first 5 ugly lemmas                                                      *)
(* ------------------------------------------------------------------------ *)

lemma ssum_lemma9: "[| chain(Y); lub(range(Y)) = Isinl(x)|] ==> !i.? x. Y(i)=Isinl(x)"
apply (intro strip)
apply (rule_tac p = "Y (i) " in IssumE)
apply (erule exI)
apply (erule exI)
apply (rule_tac P = "y=UU" in notE)
apply assumption
apply (rule less_ssum3d [THEN iffD1])
apply (erule subst)
apply (erule subst)
apply (erule is_ub_thelub)
done


lemma ssum_lemma10: "[| chain(Y); lub(range(Y)) = Isinr(x)|] ==> !i.? x. Y(i)=Isinr(x)"
apply (intro strip)
apply (rule_tac p = "Y (i) " in IssumE)
apply (rule exI)
apply (erule trans)
apply (rule strict_IsinlIsinr)
apply (erule_tac [2] exI)
apply (rule_tac P = "xa=UU" in notE)
apply assumption
apply (rule less_ssum3c [THEN iffD1])
apply (erule subst)
apply (erule subst)
apply (erule is_ub_thelub)
done

lemma ssum_lemma11: "[| chain(Y); lub(range(Y)) = Isinl(UU) |] ==> 
    Iwhen f g (lub(range Y)) = lub(range(%i. Iwhen f g (Y i)))"
apply (simp only: Ssum0_ss)
apply (rule chain_UU_I_inverse [symmetric])
apply (rule allI)
apply (rule_tac s = "Isinl (UU) " and t = "Y (i) " in subst)
apply (rule inst_ssum_pcpo [THEN subst])
apply (rule chain_UU_I [THEN spec, symmetric])
apply assumption
apply (erule inst_ssum_pcpo [THEN ssubst])
apply (simp only: Ssum0_ss)
done

lemma ssum_lemma12: "[| chain(Y); lub(range(Y)) = Isinl(x); x ~= UU |] ==> 
    Iwhen f g (lub(range Y)) = lub(range(%i. Iwhen f g (Y i)))"
apply simp
apply (rule_tac t = "x" in subst)
apply (rule inject_Isinl)
apply (rule trans)
prefer 2 apply (assumption)
apply (rule thelub_ssum1a [symmetric])
apply assumption
apply (erule ssum_lemma9)
apply assumption
apply (rule trans)
apply (rule contlub_cfun_arg)
apply (rule monofun_Iwhen3 [THEN ch2ch_monofun])
apply assumption
apply (rule lub_equal2)
apply (rule chain_mono2 [THEN exE])
prefer 2 apply (assumption)
apply (rule chain_UU_I_inverse2)
apply (subst inst_ssum_pcpo)
apply (erule contrapos_np)
apply (rule inject_Isinl)
apply (rule trans)
apply (erule sym)
apply (erule notnotD)
apply (rule exI)
apply (intro strip)
apply (rule ssum_lemma9 [THEN spec, THEN exE])
apply assumption
apply assumption
apply (rule_tac t = "Y (i) " in ssubst)
apply assumption
apply (rule trans)
apply (rule cfun_arg_cong)
apply (rule Iwhen2)
apply force
apply (rule_tac t = "Y (i) " in ssubst)
apply assumption
apply auto
apply (subst Iwhen2)
apply force
apply (rule refl)
apply (rule monofun_Rep_CFun2 [THEN ch2ch_monofun])
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
done


lemma ssum_lemma13: "[| chain(Y); lub(range(Y)) = Isinr(x); x ~= UU |] ==> 
    Iwhen f g (lub(range Y)) = lub(range(%i. Iwhen f g (Y i)))"
apply simp
apply (rule_tac t = "x" in subst)
apply (rule inject_Isinr)
apply (rule trans)
prefer 2 apply (assumption)
apply (rule thelub_ssum1b [symmetric])
apply assumption
apply (erule ssum_lemma10)
apply assumption
apply (rule trans)
apply (rule contlub_cfun_arg)
apply (rule monofun_Iwhen3 [THEN ch2ch_monofun])
apply assumption
apply (rule lub_equal2)
apply (rule chain_mono2 [THEN exE])
prefer 2 apply (assumption)
apply (rule chain_UU_I_inverse2)
apply (subst inst_ssum_pcpo)
apply (erule contrapos_np)
apply (rule inject_Isinr)
apply (rule trans)
apply (erule sym)
apply (rule strict_IsinlIsinr [THEN subst])
apply (erule notnotD)
apply (rule exI)
apply (intro strip)
apply (rule ssum_lemma10 [THEN spec, THEN exE])
apply assumption
apply assumption
apply (rule_tac t = "Y (i) " in ssubst)
apply assumption
apply (rule trans)
apply (rule cfun_arg_cong)
apply (rule Iwhen3)
apply force
apply (rule_tac t = "Y (i) " in ssubst)
apply assumption
apply (subst Iwhen3)
apply force
apply (rule_tac t = "Y (i) " in ssubst)
apply assumption
apply simp
apply (rule monofun_Rep_CFun2 [THEN ch2ch_monofun])
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
done


lemma contlub_Iwhen3: "contlub(Iwhen(f)(g))"
apply (rule contlubI)
apply (intro strip)
apply (rule_tac p = "lub (range (Y))" in IssumE)
apply (erule ssum_lemma11)
apply assumption
apply (erule ssum_lemma12)
apply assumption
apply assumption
apply (erule ssum_lemma13)
apply assumption
apply assumption
done

lemma cont_Iwhen1: "cont(Iwhen)"
apply (rule monocontlub2cont)
apply (rule monofun_Iwhen1)
apply (rule contlub_Iwhen1)
done

lemma cont_Iwhen2: "cont(Iwhen(f))"
apply (rule monocontlub2cont)
apply (rule monofun_Iwhen2)
apply (rule contlub_Iwhen2)
done

lemma cont_Iwhen3: "cont(Iwhen(f)(g))"
apply (rule monocontlub2cont)
apply (rule monofun_Iwhen3)
apply (rule contlub_Iwhen3)
done

(* ------------------------------------------------------------------------ *)
(* continuous versions of lemmas for 'a ++ 'b                               *)
(* ------------------------------------------------------------------------ *)

lemma strict_sinl: "sinl$UU =UU"

apply (unfold sinl_def)
apply (simp add: cont_Isinl)
done
declare strict_sinl [simp]

lemma strict_sinr: "sinr$UU=UU"
apply (unfold sinr_def)
apply (simp add: cont_Isinr)
done
declare strict_sinr [simp]

lemma noteq_sinlsinr: 
        "sinl$a=sinr$b ==> a=UU & b=UU"
apply (unfold sinl_def sinr_def)
apply (auto dest!: noteq_IsinlIsinr)
done

lemma inject_sinl: 
        "sinl$a1=sinl$a2==> a1=a2"
apply (unfold sinl_def sinr_def)
apply auto
done

lemma inject_sinr: 
        "sinr$a1=sinr$a2==> a1=a2"
apply (unfold sinl_def sinr_def)
apply auto
done

declare inject_sinl [dest!] inject_sinr [dest!]

lemma defined_sinl: "x~=UU ==> sinl$x ~= UU"
apply (erule contrapos_nn)
apply (rule inject_sinl)
apply auto
done
declare defined_sinl [simp]

lemma defined_sinr: "x~=UU ==> sinr$x ~= UU"
apply (erule contrapos_nn)
apply (rule inject_sinr)
apply auto
done
declare defined_sinr [simp]

lemma Exh_Ssum1: 
        "z=UU | (? a. z=sinl$a & a~=UU) | (? b. z=sinr$b & b~=UU)"
apply (unfold sinl_def sinr_def)
apply simp
apply (subst inst_ssum_pcpo)
apply (rule Exh_Ssum)
done


lemma ssumE:
assumes major: "p=UU ==> Q"
assumes prem2: "!!x.[|p=sinl$x; x~=UU |] ==> Q"
assumes prem3: "!!y.[|p=sinr$y; y~=UU |] ==> Q"
shows "Q"
apply (rule major [THEN IssumE])
apply (subst inst_ssum_pcpo)
apply assumption
apply (rule prem2)
prefer 2 apply (assumption)
apply (simp add: sinl_def)
apply (rule prem3)
prefer 2 apply (assumption)
apply (simp add: sinr_def)
done


lemma ssumE2:
assumes preml: "!!x.[|p=sinl$x|] ==> Q"
assumes premr: "!!y.[|p=sinr$y|] ==> Q"
shows "Q"
apply (rule IssumE2)
apply (rule preml)
apply (rule_tac [2] premr)
apply (unfold sinl_def sinr_def)
apply auto
done

lemmas ssum_conts = cont_lemmas1 cont_Iwhen1 cont_Iwhen2
                cont_Iwhen3 cont2cont_CF1L

lemma sscase1: 
        "sscase$f$g$UU = UU"
apply (unfold sscase_def sinl_def sinr_def)
apply (subst inst_ssum_pcpo)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (simp only: Ssum0_ss)
done
declare sscase1 [simp]


lemma sscase2: 
        "x~=UU==> sscase$f$g$(sinl$x) = f$x"
apply (unfold sscase_def sinl_def sinr_def)
apply (simplesubst beta_cfun)
apply (rule cont_Isinl)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply simp
done
declare sscase2 [simp]

lemma sscase3: 
        "x~=UU==> sscase$f$g$(sinr$x) = g$x"
apply (unfold sscase_def sinl_def sinr_def)
apply (simplesubst beta_cfun)
apply (rule cont_Isinr)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply simp
done
declare sscase3 [simp]


lemma less_ssum4a: 
        "(sinl$x << sinl$y) = (x << y)"

apply (unfold sinl_def sinr_def)
apply (subst beta_cfun)
apply (rule cont_Isinl)
apply (subst beta_cfun)
apply (rule cont_Isinl)
apply (rule less_ssum3a)
done

lemma less_ssum4b: 
        "(sinr$x << sinr$y) = (x << y)"
apply (unfold sinl_def sinr_def)
apply (subst beta_cfun)
apply (rule cont_Isinr)
apply (subst beta_cfun)
apply (rule cont_Isinr)
apply (rule less_ssum3b)
done

lemma less_ssum4c: 
        "(sinl$x << sinr$y) = (x = UU)"
apply (unfold sinl_def sinr_def)
apply (simplesubst beta_cfun)
apply (rule cont_Isinr)
apply (subst beta_cfun)
apply (rule cont_Isinl)
apply (rule less_ssum3c)
done

lemma less_ssum4d: 
        "(sinr$x << sinl$y) = (x = UU)"
apply (unfold sinl_def sinr_def)
apply (simplesubst beta_cfun)
apply (rule cont_Isinl)
apply (subst beta_cfun)
apply (rule cont_Isinr)
apply (rule less_ssum3d)
done

lemma ssum_chainE: 
        "chain(Y) ==> (!i.? x.(Y i)=sinl$x)|(!i.? y.(Y i)=sinr$y)"
apply (unfold sinl_def sinr_def)
apply simp
apply (erule ssum_lemma4)
done


lemma thelub_ssum2a: 
"[| chain(Y); !i.? x. Y(i) = sinl$x |] ==>  
    lub(range(Y)) = sinl$(lub(range(%i. sscase$(LAM x. x)$(LAM y. UU)$(Y i))))"

apply (unfold sinl_def sinr_def sscase_def)
apply (subst beta_cfun)
apply (rule cont_Isinl)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (subst beta_cfun [THEN ext])
apply (intro ssum_conts)
apply (rule thelub_ssum1a)
apply assumption
apply (rule allI)
apply (erule allE)
apply (erule exE)
apply (rule exI)
apply (erule box_equals)
apply (rule refl)
apply simp
done

lemma thelub_ssum2b: 
"[| chain(Y); !i.? x. Y(i) = sinr$x |] ==>  
    lub(range(Y)) = sinr$(lub(range(%i. sscase$(LAM y. UU)$(LAM x. x)$(Y i))))"
apply (unfold sinl_def sinr_def sscase_def)
apply (subst beta_cfun)
apply (rule cont_Isinr)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (subst beta_cfun)
apply (intro ssum_conts)
apply (subst beta_cfun [THEN ext])
apply (intro ssum_conts)
apply (rule thelub_ssum1b)
apply assumption
apply (rule allI)
apply (erule allE)
apply (erule exE)
apply (rule exI)
apply (erule box_equals)
apply (rule refl)
apply simp
done

lemma thelub_ssum2a_rev: 
        "[| chain(Y); lub(range(Y)) = sinl$x|] ==> !i.? x. Y(i)=sinl$x"
apply (unfold sinl_def sinr_def)
apply simp
apply (erule ssum_lemma9)
apply simp
done

lemma thelub_ssum2b_rev: 
     "[| chain(Y); lub(range(Y)) = sinr$x|] ==> !i.? x. Y(i)=sinr$x"
apply (unfold sinl_def sinr_def)
apply simp
apply (erule ssum_lemma10)
apply simp
done

lemma thelub_ssum3: "chain(Y) ==>  
    lub(range(Y)) = sinl$(lub(range(%i. sscase$(LAM x. x)$(LAM y. UU)$(Y i)))) 
  | lub(range(Y)) = sinr$(lub(range(%i. sscase$(LAM y. UU)$(LAM x. x)$(Y i))))"
apply (rule ssum_chainE [THEN disjE])
apply assumption
apply (rule disjI1)
apply (erule thelub_ssum2a)
apply assumption
apply (rule disjI2)
apply (erule thelub_ssum2b)
apply assumption
done

lemma sscase4: "sscase$sinl$sinr$z=z"
apply (rule_tac p = "z" in ssumE)
apply auto
done


(* ------------------------------------------------------------------------ *)
(* install simplifier for Ssum                                              *)
(* ------------------------------------------------------------------------ *)

lemmas Ssum_rews = strict_sinl strict_sinr defined_sinl defined_sinr
                sscase1 sscase2 sscase3

end
