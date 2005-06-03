(*  Title:      HOLCF/Up.thy
    ID:         $Id$
    Author:     Franz Regensburger and Brian Huffman

Lifting.
*)

header {* The type of lifted values *}

theory Up
imports Cfun Sum_Type Datatype
begin

defaultsort cpo

subsection {* Definition of new type for lifting *}

typedef (Up) ('a) "u" = "UNIV :: (unit + 'a) set" ..

consts
  Iup         :: "'a => ('a)u"
  Ifup        :: "('a->'b)=>('a)u => 'b::pcpo"

defs
  Iup_def:     "Iup x == Abs_Up(Inr(x))"
  Ifup_def:    "Ifup(f)(x)== case Rep_Up(x) of Inl(y) => UU | Inr(z) => f$z"

lemma Abs_Up_inverse2: "Rep_Up (Abs_Up y) = y"
by (simp add: Up_def Abs_Up_inverse)

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

lemma inject_Iup [dest!]: "Iup x=Iup y ==> x=y"
apply (unfold Iup_def)
apply (rule inj_Inr [THEN injD])
apply (rule inj_Abs_Up [THEN injD])
apply assumption
done

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

lemma Ifup1 [simp]: "Ifup(f)(Abs_Up(Inl ()))=UU"
apply (unfold Ifup_def)
apply (subst Abs_Up_inverse2)
apply (subst sum_case_Inl)
apply (rule refl)
done

lemma Ifup2 [simp]: "Ifup(f)(Iup(x))=f$x"
apply (unfold Ifup_def Iup_def)
apply (subst Abs_Up_inverse2)
apply (subst sum_case_Inr)
apply (rule refl)
done

subsection {* Ordering on type @{typ "'a u"} *}

instance u :: (sq_ord) sq_ord ..

defs (overloaded)
  less_up_def: "(op <<) == (%x1 x2. case Rep_Up(x1) of                 
               Inl(y1) => True          
             | Inr(y2) => (case Rep_Up(x2) of Inl(z1) => False       
                                            | Inr(z2) => y2<<z2))"

lemma less_up1a [iff]: 
        "Abs_Up(Inl ())<< z"
by (simp add: less_up_def Abs_Up_inverse2)

lemma less_up1b [iff]: 
        "~(Iup x) << (Abs_Up(Inl ()))"
by (simp add: Iup_def less_up_def Abs_Up_inverse2)

lemma less_up1c [iff]: 
        "(Iup x) << (Iup y)=(x<<y)"
by (simp add: Iup_def less_up_def Abs_Up_inverse2)

subsection {* Type @{typ "'a u"} is a partial order *}

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

instance u :: (cpo) po
by intro_classes
  (assumption | rule refl_less_up antisym_less_up trans_less_up)+

text {* for compatibility with old HOLCF-Version *}
lemma inst_up_po: "(op <<)=(%x1 x2. case Rep_Up(x1) of                 
                Inl(y1) => True  
              | Inr(y2) => (case Rep_Up(x2) of Inl(z1) => False  
                                             | Inr(z2) => y2<<z2))"
apply (fold less_up_def)
apply (rule refl)
done

subsection {* Monotonicity of @{term Iup} and @{term Ifup} *}

lemma monofun_Iup: "monofun(Iup)"
by (simp add: monofun_def)

lemma monofun_Ifup1: "monofun(Ifup)"
apply (rule monofunI)
apply (rule less_fun [THEN iffD2, rule_format])
apply (rule_tac p = "xa" in upE)
apply simp
apply simp
apply (erule monofun_cfun_fun)
done

lemma monofun_Ifup2: "monofun(Ifup(f))"
apply (rule monofunI)
apply (rule_tac p = "x" in upE)
apply simp
apply simp
apply (rule_tac p = "y" in upE)
apply simp
apply simp
apply (erule monofun_cfun_arg)
done

subsection {* Type @{typ "'a u"} is a cpo *}

text {* Some kind of surjectivity lemma *}

lemma up_lemma1: "z=Iup(x) ==> Iup(Ifup(LAM x. x)(z)) = z"
by simp

lemma lub_up1a: "[|chain(Y);EX i x. Y(i)=Iup(x)|]  
      ==> range(Y) <<| Iup(lub(range(%i.(Ifup (LAM x. x) (Y(i))))))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule_tac p = "Y (i) " in upE)
apply (rule_tac s = "Abs_Up (Inl ())" and t = "Y (i) " in subst)
apply (erule sym)
apply (rule less_up1a)
apply (rule_tac t = "Y (i) " in up_lemma1 [THEN subst])
apply assumption
apply (rule less_up1c [THEN iffD2])
apply (rule is_ub_thelub)
apply (erule monofun_Ifup2 [THEN ch2ch_monofun])
apply (rule_tac p = "u" in upE)
apply (erule exE)
apply (erule exE)
apply (rule_tac P = "Y (i) <<Abs_Up (Inl ())" in notE)
apply (rule_tac s = "Iup (x) " and t = "Y (i) " in ssubst)
apply assumption
apply (rule less_up1b)
apply (erule subst)
apply (erule ub_rangeD)
apply (rule_tac t = "u" in up_lemma1 [THEN subst])
apply assumption
apply (rule less_up1c [THEN iffD2])
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
apply simp
apply (rule less_up1a)
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

text {* New versions where @{typ "'a"} does not have to be a pcpo *}

lemma up_lemma1a: "EX x. z=Iup(x) ==> Iup(THE a. Iup a = z) = z"
apply (erule exE)
apply (rule theI)
apply (erule sym)
apply simp
apply (erule inject_Iup)
done

text {* Now some lemmas about chains of @{typ "'a u"} elements *}

lemma up_chain_lemma1:
  "[| chain Y; EX x. Y j = Iup x |] ==> EX x. Y (i + j) = Iup x"
apply (drule_tac x="j" and y="i + j" in chain_mono3)
apply (rule le_add2)
apply (rule_tac p="Y (i + j)" in upE)
apply auto
done

lemma up_chain_lemma2:
  "[| chain Y; EX x. Y j = Iup x |] ==>
    Iup (THE a. Iup a = Y (i + j)) = Y (i + j)"
apply (drule_tac i=i in up_chain_lemma1)
apply assumption
apply (erule up_lemma1a)
done

lemma up_chain_lemma3:
  "[| chain Y; EX x. Y j = Iup x |] ==> chain (%i. THE a. Iup a = Y (i + j))"
apply (rule chainI)
apply (rule less_up1c [THEN iffD1])
apply (simp only: up_chain_lemma2)
apply (simp add: chainE)
done

lemma up_chain_lemma4:
  "[| chain Y; EX x. Y j = Iup x |] ==>
    (%i. Y (i + j)) = (%i. Iup (THE a. Iup a = Y (i + j)))"
apply (rule ext)
apply (rule up_chain_lemma2 [symmetric])
apply assumption+
done

lemma is_lub_range_shift:
  "[| chain S; range (%i. S (i + j)) <<| x |] ==> range S <<| x"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (rule trans_less)
apply (erule chain_mono3)
apply (rule le_add1)
apply (erule is_ub_lub)
apply (erule is_lub_lub)
apply (rule ub_rangeI)
apply (erule ub_rangeD)
done

lemma is_lub_Iup:
  "range S <<| x \<Longrightarrow> range (%i. Iup (S i)) <<| Iup x"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (subst less_up1c)
apply (erule is_ub_lub)
apply (rule_tac p=u in upE)
apply (drule ub_rangeD)
apply (simp only: less_up1b)
apply (simp only: less_up1c)
apply (erule is_lub_lub)
apply (rule ub_rangeI)
apply (drule_tac i=i in ub_rangeD)
apply (simp only: less_up1c)
done

lemma lub_up1c: "[|chain(Y); EX x. Y(j)=Iup(x)|]  
      ==> range(Y) <<| Iup(lub(range(%i. THE a. Iup a = Y(i + j))))"
apply (rule_tac j=j in is_lub_range_shift)
apply assumption
apply (subst up_chain_lemma4)
apply assumption+
apply (rule is_lub_Iup)
apply (rule thelubE [OF _ refl])
apply (rule up_chain_lemma3)
apply assumption+
done

lemmas thelub_up1c = lub_up1c [THEN thelubI, standard]

lemma cpo_up: "chain(Y::nat=>('a)u) ==> EX x. range(Y) <<|x"
apply (case_tac "EX i x. Y i = Iup x")
apply (erule exE)
apply (rule exI)
apply (erule lub_up1c)
apply assumption
apply (rule exI)
apply (erule lub_up1b)
apply simp
done

instance u :: (cpo) cpo
by intro_classes (rule cpo_up)

subsection {* Type @{typ "'a u"} is pointed *}

lemma minimal_up: "Abs_Up(Inl ()) << z"
by (rule less_up1a)

lemmas UU_up_def = minimal_up [THEN minimal2UU, symmetric, standard]

lemma least_up: "EX x::'a u. ALL y. x<<y"
apply (rule_tac x = "Abs_Up (Inl ())" in exI)
apply (rule minimal_up [THEN allI])
done

instance u :: (cpo) pcpo
by intro_classes (rule least_up)

text {* for compatibility with old HOLCF-Version *}
lemma inst_up_pcpo: "UU = Abs_Up(Inl ())"
by (simp add: UU_def UU_up_def)

text {* some lemmas restated for class pcpo *}

lemma less_up3b: "~ Iup(x) << UU"
apply (subst inst_up_pcpo)
apply (rule less_up1b)
done

lemma defined_Iup2 [iff]: "Iup(x) ~= UU"
apply (subst inst_up_pcpo)
apply (rule defined_Iup)
done

subsection {* Continuity of @{term Iup} and @{term Ifup} *}

text {* continuity for @{term Iup} *}

lemma cont_Iup [iff]: "cont(Iup)"
apply (rule contI)
apply (rule is_lub_Iup)
apply (erule thelubE [OF _ refl])
done

lemmas contlub_Iup = cont_Iup [THEN cont2contlub]

text {* continuity for @{term Ifup} *}

lemma contlub_Ifup1: "contlub(Ifup)"
apply (rule contlubI)
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
apply (case_tac "EX i x. Y i = Iup x")
apply (erule exE)
apply (subst thelub_up1c)
apply assumption
apply assumption
apply simp
prefer 2
apply (subst thelub_up1b)
apply assumption
apply simp
apply simp
apply (rule chain_UU_I_inverse [symmetric])
apply (rule allI)
apply (rule_tac p = "Y(i)" in upE)
apply simp
apply simp
apply (subst contlub_cfun_arg)
apply  (erule up_chain_lemma3)
apply  assumption
apply (rule trans)
prefer 2
apply (rule_tac j=i in lub_range_shift)
apply (erule monofun_Ifup2 [THEN ch2ch_monofun])
apply (rule lub_equal [rule_format])
apply (rule chain_monofun)
apply (erule up_chain_lemma3)
apply assumption
apply (rule monofun_Ifup2 [THEN ch2ch_monofun])
apply (erule chain_shift)
apply (drule_tac i=k in up_chain_lemma1)
apply assumption
apply clarify
apply simp
apply (subst the_equality)
apply (rule refl)
apply (erule inject_Iup)
apply (rule refl)
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

subsection {* Continuous versions of constants *}

constdefs  
        up  :: "'a -> ('a)u"
       "up  == (LAM x. Iup(x))"
        fup :: "('a->'c)-> ('a)u -> 'c::pcpo"
       "fup == (LAM f p. Ifup(f)(p))"

translations
"case l of up$x => t1" == "fup$(LAM x. t1)$l"

text {* continuous versions of lemmas for @{typ "('a)u"} *}

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

lemma defined_up [simp]: " up$x ~= UU"
by (simp add: up_def)

lemma upE1: 
        "[| p=UU ==> Q; !!x. p=up$x==>Q|] ==>Q"
apply (unfold up_def)
apply (rule upE)
apply (simp only: inst_up_pcpo)
apply fast
apply simp
done

lemmas up_conts = cont_lemmas1 cont_Iup cont_Ifup1 cont_Ifup2 cont2cont_CF1L

lemma fup1 [simp]: "fup$f$UU=UU"
apply (unfold up_def fup_def)
apply (subst inst_up_pcpo)
apply (subst beta_cfun)
apply (intro up_conts)
apply (subst beta_cfun)
apply (rule cont_Ifup2)
apply simp
done

lemma fup2 [simp]: "fup$f$(up$x)=f$x"
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
by (simp add: up_def fup_def less_up3b)

lemma less_up4c: "(up$x << up$y) = (x<<y)"
by (simp add: up_def fup_def)

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
apply (erule thelub_up1b)
apply simp
done

lemma up_lemma2: "(EX x. z = up$x) = (z~=UU)"
apply (rule iffI)
apply (erule exE)
apply simp
apply (rule_tac p = "z" in upE1)
apply simp
apply (erule exI)
done

lemma thelub_up2a_rev:
  "[| chain(Y); lub(range(Y)) = up$x |] ==> EX i x. Y(i) = up$x"
apply (rule exE)
apply (rule chain_UU_I_inverse2)
apply (rule up_lemma2 [THEN iffD1])
apply (erule exI)
apply (rule exI)
apply (rule up_lemma2 [THEN iffD2])
apply assumption
done

lemma thelub_up2b_rev:
  "[| chain(Y); lub(range(Y)) = UU |] ==> ! i x.  Y(i) ~= up$x"
by (blast dest!: chain_UU_I [THEN spec] exI [THEN up_lemma2 [THEN iffD1]])

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
apply simp
apply simp
done

text {* for backward compatibility *}

lemmas less_up2b = less_up1b
lemmas less_up2c = less_up1c

end
