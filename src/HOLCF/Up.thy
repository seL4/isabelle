(*  Title:      HOLCF/Up1.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Lifting.
*)

header {* The type of lifted values *}

theory Up = Cfun + Sum_Type + Datatype:

(* new type for lifting *)

typedef (Up) ('a) "u" = "{x::(unit + 'a).True}"
by auto

instance u :: (sq_ord)sq_ord ..

consts
  Iup         :: "'a => ('a)u"
  Ifup        :: "('a->'b)=>('a)u => 'b"

defs
  Iup_def:     "Iup x == Abs_Up(Inr(x))"
  Ifup_def:    "Ifup(f)(x)== case Rep_Up(x) of Inl(y) => UU | Inr(z) => f$z"

defs (overloaded)
  less_up_def: "(op <<) == (%x1 x2. case Rep_Up(x1) of                 
               Inl(y1) => True          
             | Inr(y2) => (case Rep_Up(x2) of Inl(z1) => False       
                                            | Inr(z2) => y2<<z2))"

lemma Abs_Up_inverse2: "Rep_Up (Abs_Up y) = y"
apply (simp (no_asm) add: Up_def Abs_Up_inverse)
done

lemma Exh_Up: "z = Abs_Up(Inl ()) | (? x. z = Iup x)"
apply (unfold Iup_def)
apply (rule Rep_Up_inverse [THEN subst])
apply (rule_tac s = "Rep_Up z" in sumE)
apply (rule disjI1)
apply (rule_tac f = "Abs_Up" in arg_cong)
apply (rule unit_eq [THEN subst])
apply assumption
apply (rule disjI2)
apply (rule exI)
apply (rule_tac f = "Abs_Up" in arg_cong)
apply assumption
done

lemma inj_Abs_Up: "inj(Abs_Up)"
apply (rule inj_on_inverseI)
apply (rule Abs_Up_inverse2)
done

lemma inj_Rep_Up: "inj(Rep_Up)"
apply (rule inj_on_inverseI)
apply (rule Rep_Up_inverse)
done

lemma inject_Iup: "Iup x=Iup y ==> x=y"
apply (unfold Iup_def)
apply (rule inj_Inr [THEN injD])
apply (rule inj_Abs_Up [THEN injD])
apply assumption
done

declare inject_Iup [dest!]

lemma defined_Iup: "Iup x~=Abs_Up(Inl ())"
apply (unfold Iup_def)
apply (rule notI)
apply (rule notE)
apply (rule Inl_not_Inr)
apply (rule sym)
apply (erule inj_Abs_Up [THEN injD])
done


lemma upE: "[| p=Abs_Up(Inl ()) ==> Q; !!x. p=Iup(x)==>Q|] ==>Q"
apply (rule Exh_Up [THEN disjE])
apply fast
apply (erule exE)
apply fast
done

lemma Ifup1: "Ifup(f)(Abs_Up(Inl ()))=UU"
apply (unfold Ifup_def)
apply (subst Abs_Up_inverse2)
apply (subst sum_case_Inl)
apply (rule refl)
done

lemma Ifup2: 
        "Ifup(f)(Iup(x))=f$x"
apply (unfold Ifup_def Iup_def)
apply (subst Abs_Up_inverse2)
apply (subst sum_case_Inr)
apply (rule refl)
done

lemmas Up0_ss = Ifup1 Ifup2

declare Ifup1 [simp] Ifup2 [simp]

lemma less_up1a: 
        "Abs_Up(Inl ())<< z"
apply (unfold less_up_def)
apply (subst Abs_Up_inverse2)
apply (subst sum_case_Inl)
apply (rule TrueI)
done

lemma less_up1b: 
        "~(Iup x) << (Abs_Up(Inl ()))"
apply (unfold Iup_def less_up_def)
apply (rule notI)
apply (rule iffD1)
prefer 2 apply (assumption)
apply (subst Abs_Up_inverse2)
apply (subst Abs_Up_inverse2)
apply (subst sum_case_Inr)
apply (subst sum_case_Inl)
apply (rule refl)
done

lemma less_up1c: 
        "(Iup x) << (Iup y)=(x<<y)"
apply (unfold Iup_def less_up_def)
apply (subst Abs_Up_inverse2)
apply (subst Abs_Up_inverse2)
apply (subst sum_case_Inr)
apply (subst sum_case_Inr)
apply (rule refl)
done

declare less_up1a [iff] less_up1b [iff] less_up1c [iff]

lemma refl_less_up: "(p::'a u) << p"
apply (rule_tac p = "p" in upE)
apply auto
done

lemma antisym_less_up: "[|(p1::'a u) << p2;p2 << p1|] ==> p1=p2"
apply (rule_tac p = "p1" in upE)
apply simp
apply (rule_tac p = "p2" in upE)
apply (erule sym)
apply simp
apply (rule_tac p = "p2" in upE)
apply simp
apply simp
apply (drule antisym_less, assumption)
apply simp
done

lemma trans_less_up: "[|(p1::'a u) << p2;p2 << p3|] ==> p1 << p3"
apply (rule_tac p = "p1" in upE)
apply simp
apply (rule_tac p = "p2" in upE)
apply simp
apply (rule_tac p = "p3" in upE)
apply auto
apply (blast intro: trans_less)
done

(* Class Instance u::(pcpo)po *)

instance u :: (pcpo)po
apply (intro_classes)
apply (rule refl_less_up)
apply (rule antisym_less_up, assumption+)
apply (rule trans_less_up, assumption+)
done

(* for compatibility with old HOLCF-Version *)
lemma inst_up_po: "(op <<)=(%x1 x2. case Rep_Up(x1) of                 
                Inl(y1) => True  
              | Inr(y2) => (case Rep_Up(x2) of Inl(z1) => False  
                                             | Inr(z2) => y2<<z2))"
apply (fold less_up_def)
apply (rule refl)
done

(* -------------------------------------------------------------------------*)
(* type ('a)u is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

lemma minimal_up: "Abs_Up(Inl ()) << z"
apply (simp (no_asm) add: less_up1a)
done

lemmas UU_up_def = minimal_up [THEN minimal2UU, symmetric, standard]

lemma least_up: "EX x::'a u. ALL y. x<<y"
apply (rule_tac x = "Abs_Up (Inl ())" in exI)
apply (rule minimal_up [THEN allI])
done

(* -------------------------------------------------------------------------*)
(* access to less_up in class po                                          *)
(* ------------------------------------------------------------------------ *)

lemma less_up2b: "~ Iup(x) << Abs_Up(Inl ())"
apply (simp (no_asm) add: less_up1b)
done

lemma less_up2c: "(Iup(x)<<Iup(y)) = (x<<y)"
apply (simp (no_asm) add: less_up1c)
done

(* ------------------------------------------------------------------------ *)
(* Iup and Ifup are monotone                                               *)
(* ------------------------------------------------------------------------ *)

lemma monofun_Iup: "monofun(Iup)"

apply (unfold monofun)
apply (intro strip)
apply (erule less_up2c [THEN iffD2])
done

lemma monofun_Ifup1: "monofun(Ifup)"
apply (unfold monofun)
apply (intro strip)
apply (rule less_fun [THEN iffD2])
apply (intro strip)
apply (rule_tac p = "xa" in upE)
apply simp
apply simp
apply (erule monofun_cfun_fun)
done

lemma monofun_Ifup2: "monofun(Ifup(f))"
apply (unfold monofun)
apply (intro strip)
apply (rule_tac p = "x" in upE)
apply simp
apply simp
apply (rule_tac p = "y" in upE)
apply simp
apply simp
apply (erule monofun_cfun_arg)
done

(* ------------------------------------------------------------------------ *)
(* Some kind of surjectivity lemma                                          *)
(* ------------------------------------------------------------------------ *)

lemma up_lemma1: "z=Iup(x) ==> Iup(Ifup(LAM x. x)(z)) = z"
apply simp
done

(* ------------------------------------------------------------------------ *)
(* ('a)u is a cpo                                                           *)
(* ------------------------------------------------------------------------ *)

lemma lub_up1a: "[|chain(Y);EX i x. Y(i)=Iup(x)|]  
      ==> range(Y) <<| Iup(lub(range(%i.(Ifup (LAM x. x) (Y(i))))))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule_tac p = "Y (i) " in upE)
apply (rule_tac s = "Abs_Up (Inl ())" and t = "Y (i) " in subst)
apply (erule sym)
apply (rule minimal_up)
apply (rule_tac t = "Y (i) " in up_lemma1 [THEN subst])
apply assumption
apply (rule less_up2c [THEN iffD2])
apply (rule is_ub_thelub)
apply (erule monofun_Ifup2 [THEN ch2ch_monofun])
apply (rule_tac p = "u" in upE)
apply (erule exE)
apply (erule exE)
apply (rule_tac P = "Y (i) <<Abs_Up (Inl ())" in notE)
apply (rule_tac s = "Iup (x) " and t = "Y (i) " in ssubst)
apply assumption
apply (rule less_up2b)
apply (erule subst)
apply (erule ub_rangeD)
apply (rule_tac t = "u" in up_lemma1 [THEN subst])
apply assumption
apply (rule less_up2c [THEN iffD2])
apply (rule is_lub_thelub)
apply (erule monofun_Ifup2 [THEN ch2ch_monofun])
apply (erule monofun_Ifup2 [THEN ub2ub_monofun])
done

lemma lub_up1b: "[|chain(Y); ALL i x. Y(i)~=Iup(x)|] ==> range(Y) <<| Abs_Up (Inl ())"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule_tac p = "Y (i) " in upE)
apply (rule_tac s = "Abs_Up (Inl ())" and t = "Y (i) " in ssubst)
apply assumption
apply (rule refl_less)
apply (rule notE)
apply (drule spec)
apply (drule spec)
apply assumption
apply assumption
apply (rule minimal_up)
done

lemmas thelub_up1a = lub_up1a [THEN thelubI, standard]
(*
[| chain ?Y1; EX i x. ?Y1 i = Iup x |] ==>
 lub (range ?Y1) = Iup (lub (range (%i. Iup (LAM x. x) (?Y1 i))))
*)

lemmas thelub_up1b = lub_up1b [THEN thelubI, standard]
(*
[| chain ?Y1; ! i x. ?Y1 i ~= Iup x |] ==>
 lub (range ?Y1) = UU_up
*)

lemma cpo_up: "chain(Y::nat=>('a)u) ==> EX x. range(Y) <<|x"
apply (rule disjE)
apply (rule_tac [2] exI)
apply (erule_tac [2] lub_up1a)
prefer 2 apply (assumption)
apply (rule_tac [2] exI)
apply (erule_tac [2] lub_up1b)
prefer 2 apply (assumption)
apply fast
done

(* Class instance of  ('a)u for class pcpo *)

instance u :: (pcpo)pcpo
apply (intro_classes)
apply (erule cpo_up)
apply (rule least_up)
done

constdefs  
        up  :: "'a -> ('a)u"
       "up  == (LAM x. Iup(x))"
        fup :: "('a->'c)-> ('a)u -> 'c"
       "fup == (LAM f p. Ifup(f)(p))"

translations
"case l of up$x => t1" == "fup$(LAM x. t1)$l"

(* for compatibility with old HOLCF-Version *)
lemma inst_up_pcpo: "UU = Abs_Up(Inl ())"
apply (simp add: UU_def UU_up_def)
done

(* -------------------------------------------------------------------------*)
(* some lemmas restated for class pcpo                                      *)
(* ------------------------------------------------------------------------ *)

lemma less_up3b: "~ Iup(x) << UU"
apply (subst inst_up_pcpo)
apply (rule less_up2b)
done

lemma defined_Iup2: "Iup(x) ~= UU"
apply (subst inst_up_pcpo)
apply (rule defined_Iup)
done
declare defined_Iup2 [iff]

(* ------------------------------------------------------------------------ *)
(* continuity for Iup                                                       *)
(* ------------------------------------------------------------------------ *)

lemma contlub_Iup: "contlub(Iup)"
apply (rule contlubI)
apply (intro strip)
apply (rule trans)
apply (rule_tac [2] thelub_up1a [symmetric])
prefer 3 apply fast
apply (erule_tac [2] monofun_Iup [THEN ch2ch_monofun])
apply (rule_tac f = "Iup" in arg_cong)
apply (rule lub_equal)
apply assumption
apply (rule monofun_Ifup2 [THEN ch2ch_monofun])
apply (erule monofun_Iup [THEN ch2ch_monofun])
apply simp
done

lemma cont_Iup: "cont(Iup)"
apply (rule monocontlub2cont)
apply (rule monofun_Iup)
apply (rule contlub_Iup)
done
declare cont_Iup [iff]

(* ------------------------------------------------------------------------ *)
(* continuity for Ifup                                                     *)
(* ------------------------------------------------------------------------ *)

lemma contlub_Ifup1: "contlub(Ifup)"
apply (rule contlubI)
apply (intro strip)
apply (rule trans)
apply (rule_tac [2] thelub_fun [symmetric])
apply (erule_tac [2] monofun_Ifup1 [THEN ch2ch_monofun])
apply (rule ext)
apply (rule_tac p = "x" in upE)
apply simp
apply (rule lub_const [THEN thelubI, symmetric])
apply simp
apply (erule contlub_cfun_fun)
done


lemma contlub_Ifup2: "contlub(Ifup(f))"
apply (rule contlubI)
apply (intro strip)
apply (rule disjE)
defer 1
apply (subst thelub_up1a)
apply assumption
apply assumption
apply simp
prefer 2
apply (subst thelub_up1b)
apply assumption
apply assumption
apply simp
apply (rule chain_UU_I_inverse [symmetric])
apply (rule allI)
apply (rule_tac p = "Y(i)" in upE)
apply simp
apply simp
apply (subst contlub_cfun_arg)
apply  (erule monofun_Ifup2 [THEN ch2ch_monofun])
apply (rule lub_equal2)
apply   (rule_tac [2] monofun_Rep_CFun2 [THEN ch2ch_monofun])
apply   (erule_tac [2] monofun_Ifup2 [THEN ch2ch_monofun])
apply  (erule_tac [2] monofun_Ifup2 [THEN ch2ch_monofun])
apply (rule chain_mono2 [THEN exE])
prefer 2 apply   (assumption)
apply  (erule exE)
apply  (erule exE)
apply  (rule exI)
apply  (rule_tac s = "Iup (x) " and t = "Y (i) " in ssubst)
apply   assumption
apply  (rule defined_Iup2)
apply (rule exI)
apply (intro strip)
apply (rule_tac p = "Y (i) " in upE)
prefer 2 apply simp
apply (rule_tac P = "Y (i) = UU" in notE)
apply  fast
apply (subst inst_up_pcpo)
apply assumption
apply fast
done

lemma cont_Ifup1: "cont(Ifup)"
apply (rule monocontlub2cont)
apply (rule monofun_Ifup1)
apply (rule contlub_Ifup1)
done

lemma cont_Ifup2: "cont(Ifup(f))"
apply (rule monocontlub2cont)
apply (rule monofun_Ifup2)
apply (rule contlub_Ifup2)
done


(* ------------------------------------------------------------------------ *)
(* continuous versions of lemmas for ('a)u                                  *)
(* ------------------------------------------------------------------------ *)

lemma Exh_Up1: "z = UU | (EX x. z = up$x)"

apply (unfold up_def)
apply simp
apply (subst inst_up_pcpo)
apply (rule Exh_Up)
done

lemma inject_up: "up$x=up$y ==> x=y"
apply (unfold up_def)
apply (rule inject_Iup)
apply auto
done

lemma defined_up: " up$x ~= UU"
apply (unfold up_def)
apply auto
done

lemma upE1: 
        "[| p=UU ==> Q; !!x. p=up$x==>Q|] ==>Q"
apply (unfold up_def)
apply (rule upE)
apply (simp only: inst_up_pcpo)
apply fast
apply simp
done

lemmas up_conts = cont_lemmas1 cont_Iup cont_Ifup1 cont_Ifup2 cont2cont_CF1L

lemma fup1: "fup$f$UU=UU"
apply (unfold up_def fup_def)
apply (subst inst_up_pcpo)
apply (subst beta_cfun)
apply (intro up_conts)
apply (subst beta_cfun)
apply (rule cont_Ifup2)
apply simp
done

lemma fup2: "fup$f$(up$x)=f$x"
apply (unfold up_def fup_def)
apply (simplesubst beta_cfun)
apply (rule cont_Iup)
apply (subst beta_cfun)
apply (intro up_conts)
apply (subst beta_cfun)
apply (rule cont_Ifup2)
apply simp
done

lemma less_up4b: "~ up$x << UU"
apply (unfold up_def fup_def)
apply simp
apply (rule less_up3b)
done

lemma less_up4c: 
         "(up$x << up$y) = (x<<y)"
apply (unfold up_def fup_def)
apply simp
done

lemma thelub_up2a: 
"[| chain(Y); EX i x. Y(i) = up$x |] ==> 
       lub(range(Y)) = up$(lub(range(%i. fup$(LAM x. x)$(Y i))))"
apply (unfold up_def fup_def)
apply (subst beta_cfun)
apply (rule cont_Iup)
apply (subst beta_cfun)
apply (intro up_conts)
apply (subst beta_cfun [THEN ext])
apply (rule cont_Ifup2)
apply (rule thelub_up1a)
apply assumption
apply (erule exE)
apply (erule exE)
apply (rule exI)
apply (rule exI)
apply (erule box_equals)
apply (rule refl)
apply simp
done



lemma thelub_up2b: 
"[| chain(Y); ! i x. Y(i) ~= up$x |] ==> lub(range(Y)) = UU"
apply (unfold up_def fup_def)
apply (subst inst_up_pcpo)
apply (rule thelub_up1b)
apply assumption
apply (intro strip)
apply (drule spec)
apply (drule spec)
apply simp
done


lemma up_lemma2: "(EX x. z = up$x) = (z~=UU)"
apply (rule iffI)
apply (erule exE)
apply simp
apply (rule defined_up)
apply (rule_tac p = "z" in upE1)
apply (erule notE)
apply assumption
apply (erule exI)
done


lemma thelub_up2a_rev: "[| chain(Y); lub(range(Y)) = up$x |] ==> EX i x. Y(i) = up$x"
apply (rule exE)
apply (rule chain_UU_I_inverse2)
apply (rule up_lemma2 [THEN iffD1])
apply (erule exI)
apply (rule exI)
apply (rule up_lemma2 [THEN iffD2])
apply assumption
done

lemma thelub_up2b_rev: "[| chain(Y); lub(range(Y)) = UU |] ==> ! i x.  Y(i) ~= up$x"
apply (blast dest!: chain_UU_I [THEN spec] exI [THEN up_lemma2 [THEN iffD1]])
done


lemma thelub_up3: "chain(Y) ==> lub(range(Y)) = UU |  
                   lub(range(Y)) = up$(lub(range(%i. fup$(LAM x. x)$(Y i))))"
apply (rule disjE)
apply (rule_tac [2] disjI1)
apply (rule_tac [2] thelub_up2b)
prefer 2 apply (assumption)
prefer 2 apply (assumption)
apply (rule_tac [2] disjI2)
apply (rule_tac [2] thelub_up2a)
prefer 2 apply (assumption)
prefer 2 apply (assumption)
apply fast
done

lemma fup3: "fup$up$x=x"
apply (rule_tac p = "x" in upE1)
apply (simp add: fup1 fup2)
apply (simp add: fup1 fup2)
done

(* ------------------------------------------------------------------------ *)
(* install simplifier for ('a)u                                             *)
(* ------------------------------------------------------------------------ *)

declare fup1 [simp] fup2 [simp] defined_up [simp]

end



