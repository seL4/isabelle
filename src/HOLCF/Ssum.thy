(*  Title:      HOLCF/Ssum0.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Strict sum with typedef
*)

header {* The type of strict sums *}

theory Ssum
imports Cfun
begin

subsection {* Definition of strict sum type *}

constdefs
  Sinl_Rep      :: "['a,'a,'b,bool]=>bool"
 "Sinl_Rep == (%a.%x y p. (a~=UU --> x=a & p))"
  Sinr_Rep      :: "['b,'a,'b,bool]=>bool"
 "Sinr_Rep == (%b.%x y p.(b~=UU --> y=b & ~p))"

typedef (Ssum)  ('a, 'b) "++" (infixr 10) = 
	"{f.(? a. f=Sinl_Rep(a::'a))|(? b. f=Sinr_Rep(b::'b))}"
by auto

syntax (xsymbols)
  "++"		:: "[type, type] => type"	("(_ \<oplus>/ _)" [21, 20] 20)
syntax (HTML output)
  "++"		:: "[type, type] => type"	("(_ \<oplus>/ _)" [21, 20] 20)

consts
  Isinl         :: "'a => ('a ++ 'b)"
  Isinr         :: "'b => ('a ++ 'b)"
  Iwhen         :: "('a->'c)=>('b->'c)=>('a ++ 'b)=> 'c"

defs   -- {*defining the abstract constants*}
  Isinl_def:     "Isinl(a) == Abs_Ssum(Sinl_Rep(a))"
  Isinr_def:     "Isinr(b) == Abs_Ssum(Sinr_Rep(b))"

  Iwhen_def:     "Iwhen(f)(g)(s) == @z.
                                    (s=Isinl(UU) --> z=UU)
                        &(!a. a~=UU & s=Isinl(a) --> z=f$a)  
                        &(!b. b~=UU & s=Isinr(b) --> z=g$b)"  

text {* A non-emptiness result for Ssum *}

lemma SsumIl: "Sinl_Rep(a):Ssum"
by (unfold Ssum_def) blast

lemma SsumIr: "Sinr_Rep(a):Ssum"
by (unfold Ssum_def) blast

lemma inj_on_Abs_Ssum: "inj_on Abs_Ssum Ssum"
apply (rule inj_on_inverseI)
apply (erule Abs_Ssum_inverse)
done

text {* Strictness of @{term Sinr_Rep}, @{term Sinl_Rep} and @{term Isinl}, @{term Isinr} *}

lemma strict_SinlSinr_Rep: 
 "Sinl_Rep(UU) = Sinr_Rep(UU)"
apply (unfold Sinr_Rep_def Sinl_Rep_def)
apply (rule ext)+
apply fast
done

lemma strict_IsinlIsinr: "Isinl(UU) = Isinr(UU)"
apply (unfold Isinl_def Isinr_def)
apply (rule strict_SinlSinr_Rep [THEN arg_cong])
done

text {* distinctness of @{term Sinl_Rep}, @{term Sinr_Rep} and @{term Isinl}, @{term Isinr} *}

lemma noteq_SinlSinr_Rep: 
        "(Sinl_Rep(a) = Sinr_Rep(b)) ==> a=UU & b=UU"
apply (unfold Sinl_Rep_def Sinr_Rep_def)
apply (blast dest!: fun_cong)
done

lemma noteq_IsinlIsinr: 
        "Isinl(a)=Isinr(b) ==> a=UU & b=UU"
apply (unfold Isinl_def Isinr_def)
apply (rule noteq_SinlSinr_Rep)
apply (erule inj_on_Abs_Ssum [THEN inj_onD])
apply (rule SsumIl)
apply (rule SsumIr)
done

text {* injectivity of @{term Sinl_Rep}, @{term Sinr_Rep} and @{term Isinl}, @{term Isinr} *}

lemma inject_Sinl_Rep1: "(Sinl_Rep(a) = Sinl_Rep(UU)) ==> a=UU"
apply (unfold Sinl_Rep_def)
apply (blast dest!: fun_cong)
done

lemma inject_Sinr_Rep1: "(Sinr_Rep(b) = Sinr_Rep(UU)) ==> b=UU"
apply (unfold Sinr_Rep_def)
apply (blast dest!: fun_cong)
done

lemma inject_Sinl_Rep2: 
"[| a1~=UU ; a2~=UU ; Sinl_Rep(a1)=Sinl_Rep(a2) |] ==> a1=a2"
apply (unfold Sinl_Rep_def)
apply (blast dest!: fun_cong)
done

lemma inject_Sinr_Rep2: 
"[|b1~=UU ; b2~=UU ; Sinr_Rep(b1)=Sinr_Rep(b2) |] ==> b1=b2"
apply (unfold Sinr_Rep_def)
apply (blast dest!: fun_cong)
done

lemma inject_Sinl_Rep: "Sinl_Rep(a1)=Sinl_Rep(a2) ==> a1=a2"
apply (case_tac "a1=UU")
apply simp
apply (rule inject_Sinl_Rep1 [symmetric])
apply (erule sym)
apply (case_tac "a2=UU")
apply simp
apply (drule inject_Sinl_Rep1)
apply simp
apply (erule inject_Sinl_Rep2)
apply assumption
apply assumption
done

lemma inject_Sinr_Rep: "Sinr_Rep(b1)=Sinr_Rep(b2) ==> b1=b2"
apply (case_tac "b1=UU")
apply simp
apply (rule inject_Sinr_Rep1 [symmetric])
apply (erule sym)
apply (case_tac "b2=UU")
apply simp
apply (drule inject_Sinr_Rep1)
apply simp
apply (erule inject_Sinr_Rep2)
apply assumption
apply assumption
done

lemma inject_Isinl: "Isinl(a1)=Isinl(a2)==> a1=a2"
apply (unfold Isinl_def)
apply (rule inject_Sinl_Rep)
apply (erule inj_on_Abs_Ssum [THEN inj_onD])
apply (rule SsumIl)
apply (rule SsumIl)
done

lemma inject_Isinr: "Isinr(b1)=Isinr(b2) ==> b1=b2"
apply (unfold Isinr_def)
apply (rule inject_Sinr_Rep)
apply (erule inj_on_Abs_Ssum [THEN inj_onD])
apply (rule SsumIr)
apply (rule SsumIr)
done

declare inject_Isinl [dest!] inject_Isinr [dest!]
declare noteq_IsinlIsinr [dest!]
declare noteq_IsinlIsinr [OF sym, dest!]

lemma inject_Isinl_rev: "a1~=a2 ==> Isinl(a1) ~= Isinl(a2)"
by blast

lemma inject_Isinr_rev: "b1~=b2 ==> Isinr(b1) ~= Isinr(b2)"
by blast

text {* Exhaustion of the strict sum @{typ "'a ++ 'b"} *}
text {* choice of the bottom representation is arbitrary *}

lemma Exh_Ssum: 
        "z=Isinl(UU) | (? a. z=Isinl(a) & a~=UU) | (? b. z=Isinr(b) & b~=UU)"
apply (unfold Isinl_def Isinr_def)
apply (rule Rep_Ssum[unfolded Ssum_def, THEN CollectE])
apply (erule disjE)
apply (erule exE)
apply (case_tac "z= Abs_Ssum (Sinl_Rep (UU))")
apply (erule disjI1)
apply (rule disjI2)
apply (rule disjI1)
apply (rule exI)
apply (rule conjI)
apply (rule Rep_Ssum_inverse [symmetric, THEN trans])
apply (erule arg_cong)
apply (rule_tac Q = "Sinl_Rep (a) =Sinl_Rep (UU) " in contrapos_nn)
apply (erule_tac [2] arg_cong)
apply (erule contrapos_nn)
apply (rule Rep_Ssum_inverse [symmetric, THEN trans])
apply (rule trans)
apply (erule arg_cong)
apply (erule arg_cong)
apply (erule exE)
apply (case_tac "z= Abs_Ssum (Sinl_Rep (UU))")
apply (erule disjI1)
apply (rule disjI2)
apply (rule disjI2)
apply (rule exI)
apply (rule conjI)
apply (rule Rep_Ssum_inverse [symmetric, THEN trans])
apply (erule arg_cong)
apply (rule_tac Q = "Sinr_Rep (b) =Sinl_Rep (UU) " in contrapos_nn)
prefer 2 apply simp
apply (rule strict_SinlSinr_Rep [symmetric])
apply (erule contrapos_nn)
apply (rule Rep_Ssum_inverse [symmetric, THEN trans])
apply (rule trans)
apply (erule arg_cong)
apply (erule arg_cong)
done

text {* elimination rules for the strict sum @{typ "'a ++ 'b"} *}

lemma IssumE:
        "[|p=Isinl(UU) ==> Q ; 
        !!x.[|p=Isinl(x); x~=UU |] ==> Q; 
        !!y.[|p=Isinr(y); y~=UU |] ==> Q|] ==> Q"
apply (rule Exh_Ssum [THEN disjE])
apply auto
done

lemma IssumE2:
"[| !!x. [| p = Isinl(x) |] ==> Q;   !!y. [| p = Isinr(y) |] ==> Q |] ==>Q"
apply (rule IssumE)
apply auto
done

text {* rewrites for @{term Iwhen} *}

lemma Iwhen1: 
        "Iwhen f g (Isinl UU) = UU"
apply (unfold Iwhen_def)
apply (rule some_equality)
apply (rule conjI)
apply fast
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "a=UU" in notE)
apply fast
apply (rule inject_Isinl)
apply (rule sym)
apply fast
apply (intro strip)
apply (rule_tac P = "b=UU" in notE)
apply fast
apply (rule inject_Isinr)
apply (rule sym)
apply (rule strict_IsinlIsinr [THEN subst])
apply fast
apply fast
done


lemma Iwhen2: 
        "x~=UU ==> Iwhen f g (Isinl x) = f$x"
apply (unfold Iwhen_def)
apply (rule some_equality)
prefer 2 apply fast
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "x=UU" in notE)
apply assumption
apply (rule inject_Isinl)
apply assumption
apply (rule conjI)
apply (intro strip)
apply (rule cfun_arg_cong)
apply (rule inject_Isinl)
apply fast
apply (intro strip)
apply (rule_tac P = "Isinl (x) = Isinr (b) " in notE)
prefer 2 apply fast
apply (rule contrapos_nn)
apply (erule_tac [2] noteq_IsinlIsinr)
apply fast
done

lemma Iwhen3: 
        "y~=UU ==> Iwhen f g (Isinr y) = g$y"
apply (unfold Iwhen_def)
apply (rule some_equality)
prefer 2 apply fast
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "y=UU" in notE)
apply assumption
apply (rule inject_Isinr)
apply (rule strict_IsinlIsinr [THEN subst])
apply assumption
apply (rule conjI)
apply (intro strip)
apply (rule_tac P = "Isinr (y) = Isinl (a) " in notE)
prefer 2 apply fast
apply (rule contrapos_nn)
apply (erule_tac [2] sym [THEN noteq_IsinlIsinr])
apply fast
apply (intro strip)
apply (rule cfun_arg_cong)
apply (rule inject_Isinr)
apply fast
done

text {* instantiate the simplifier *}

lemmas Ssum0_ss = strict_IsinlIsinr[symmetric] Iwhen1 Iwhen2 Iwhen3

declare Ssum0_ss [simp]

subsection {* Ordering for type @{typ "'a ++ 'b"} *}

instance "++"::(pcpo, pcpo) sq_ord ..

defs (overloaded)
  less_ssum_def: "(op <<) == (%s1 s2.@z.
         (! u x. s1=Isinl u & s2=Isinl x --> z = u << x)
        &(! v y. s1=Isinr v & s2=Isinr y --> z = v << y)
        &(! u y. s1=Isinl u & s2=Isinr y --> z = (u = UU))
        &(! v x. s1=Isinr v & s2=Isinl x --> z = (v = UU)))"

lemma less_ssum1a: 
"[|s1=Isinl(x::'a); s2=Isinl(y::'a)|] ==> s1 << s2 = (x << y)"
apply (unfold less_ssum_def)
apply (rule some_equality)
prefer 2 apply simp
apply (safe elim!: UU_I)
done

lemma less_ssum1b: 
"[|s1=Isinr(x::'b); s2=Isinr(y::'b)|] ==> s1 << s2 = (x << y)"
apply (unfold less_ssum_def)
apply (rule some_equality)
prefer 2 apply simp
apply (safe elim!: UU_I)
done

lemma less_ssum1c: 
"[|s1=Isinl(x::'a); s2=Isinr(y::'b)|] ==> s1 << s2 = ((x::'a) = UU)"
apply (unfold less_ssum_def)
apply (rule some_equality)
prefer 2
apply (drule conjunct2)
apply (drule conjunct2)
apply (drule conjunct1)
apply (drule spec)
apply (drule spec)
apply (erule mp)
apply fast
apply (safe elim!: UU_I)
done

lemma less_ssum1d: 
"[|s1=Isinr(x); s2=Isinl(y)|] ==> s1 << s2 = (x = UU)"
apply (unfold less_ssum_def)
apply (rule some_equality)
prefer 2
apply (drule conjunct2)
apply (drule conjunct2)
apply (drule conjunct2)
apply (drule spec)
apply (drule spec)
apply (erule mp)
apply fast
apply (safe elim!: UU_I)
done

text {* optimize lemmas about @{term less_ssum} *}

lemma less_ssum2a: "(Isinl x) << (Isinl y) = (x << y)"
apply (rule less_ssum1a)
apply (rule refl)
apply (rule refl)
done

lemma less_ssum2b: "(Isinr x) << (Isinr y) = (x << y)"
apply (rule less_ssum1b)
apply (rule refl)
apply (rule refl)
done

lemma less_ssum2c: "(Isinl x) << (Isinr y) = (x = UU)"
apply (rule less_ssum1c)
apply (rule refl)
apply (rule refl)
done

lemma less_ssum2d: "(Isinr x) << (Isinl y) = (x = UU)"
apply (rule less_ssum1d)
apply (rule refl)
apply (rule refl)
done

subsection {* Type @{typ "'a ++ 'b"} is a partial order *}

lemma refl_less_ssum: "(p::'a++'b) << p"
apply (rule_tac p = "p" in IssumE2)
apply (simp add: less_ssum2a)
apply (simp add: less_ssum2b)
done

lemma antisym_less_ssum: "[|(p1::'a++'b) << p2; p2 << p1|] ==> p1=p2"
apply (rule_tac p = "p1" in IssumE2)
apply simp
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (rule_tac f = "Isinl" in arg_cong)
apply (rule antisym_less)
apply (erule less_ssum2a [THEN iffD1])
apply (erule less_ssum2a [THEN iffD1])
apply simp
apply (erule less_ssum2d [THEN iffD1, THEN ssubst])
apply (erule less_ssum2c [THEN iffD1, THEN ssubst])
apply (rule strict_IsinlIsinr)
apply simp
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (erule less_ssum2c [THEN iffD1, THEN ssubst])
apply (erule less_ssum2d [THEN iffD1, THEN ssubst])
apply (rule strict_IsinlIsinr [symmetric])
apply simp
apply (rule_tac f = "Isinr" in arg_cong)
apply (rule antisym_less)
apply (erule less_ssum2b [THEN iffD1])
apply (erule less_ssum2b [THEN iffD1])
done

lemma trans_less_ssum: "[|(p1::'a++'b) << p2; p2 << p3|] ==> p1 << p3"
apply (rule_tac p = "p1" in IssumE2)
apply simp
apply (rule_tac p = "p3" in IssumE2)
apply simp
apply (rule less_ssum2a [THEN iffD2])
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (rule trans_less)
apply (erule less_ssum2a [THEN iffD1])
apply (erule less_ssum2a [THEN iffD1])
apply simp
apply (erule less_ssum2c [THEN iffD1, THEN ssubst])
apply (rule minimal)
apply simp
apply (rule less_ssum2c [THEN iffD2])
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (rule UU_I)
apply (rule trans_less)
apply (erule less_ssum2a [THEN iffD1])
apply (rule antisym_less_inverse [THEN conjunct1])
apply (erule less_ssum2c [THEN iffD1])
apply simp
apply (erule less_ssum2c [THEN iffD1])
apply simp
apply (rule_tac p = "p3" in IssumE2)
apply simp
apply (rule less_ssum2d [THEN iffD2])
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (erule less_ssum2d [THEN iffD1])
apply simp
apply (rule UU_I)
apply (rule trans_less)
apply (erule less_ssum2b [THEN iffD1])
apply (rule antisym_less_inverse [THEN conjunct1])
apply (erule less_ssum2d [THEN iffD1])
apply simp
apply (rule less_ssum2b [THEN iffD2])
apply (rule_tac p = "p2" in IssumE2)
apply simp
apply (erule less_ssum2d [THEN iffD1, THEN ssubst])
apply (rule minimal)
apply simp
apply (rule trans_less)
apply (erule less_ssum2b [THEN iffD1])
apply (erule less_ssum2b [THEN iffD1])
done

instance "++" :: (pcpo, pcpo) po
by intro_classes
  (assumption | rule refl_less_ssum antisym_less_ssum trans_less_ssum)+

text {* for compatibility with old HOLCF-Version *}
lemma inst_ssum_po: "(op <<)=(%s1 s2.@z.
         (! u x. s1=Isinl u & s2=Isinl x --> z = u << x)
        &(! v y. s1=Isinr v & s2=Isinr y --> z = v << y)
        &(! u y. s1=Isinl u & s2=Isinr y --> z = (u = UU))
        &(! v x. s1=Isinr v & s2=Isinl x --> z = (v = UU)))"
apply (fold less_ssum_def)
apply (rule refl)
done

subsection {* Type @{typ "'a ++ 'b"} is pointed *}

lemma minimal_ssum: "Isinl UU << s"
apply (rule_tac p = "s" in IssumE2)
apply simp
apply (rule less_ssum2a [THEN iffD2])
apply (rule minimal)
apply simp
apply (subst strict_IsinlIsinr)
apply (rule less_ssum2b [THEN iffD2])
apply (rule minimal)
done

lemmas UU_ssum_def = minimal_ssum [THEN minimal2UU, symmetric, standard]

lemma least_ssum: "? x::'a++'b.!y. x<<y"
apply (rule_tac x = "Isinl UU" in exI)
apply (rule minimal_ssum [THEN allI])
done

subsection {* Monotonicity of @{term Isinl}, @{term Isinr}, @{term Iwhen} *}

text {* @{term Isinl} and @{term Isinr} are monotone *}

lemma monofun_Isinl: "monofun(Isinl)"
by (simp add: monofun less_ssum2a)

lemma monofun_Isinr: "monofun(Isinr)"
by (simp add: monofun less_ssum2b)

text {* @{term Iwhen} is monotone in all arguments *}

lemma monofun_Iwhen1: "monofun(Iwhen)"
apply (rule monofunI [rule_format])
apply (rule less_fun [THEN iffD2, rule_format])
apply (rule less_fun [THEN iffD2, rule_format])
apply (rule_tac p = "xb" in IssumE)
apply simp
apply simp
apply (erule monofun_cfun_fun)
apply simp
done

lemma monofun_Iwhen2: "monofun(Iwhen(f))"
apply (rule monofunI [rule_format])
apply (rule less_fun [THEN iffD2, rule_format])
apply (rule_tac p = "xa" in IssumE)
apply simp
apply simp
apply simp
apply (erule monofun_cfun_fun)
done

lemma monofun_Iwhen3: "monofun(Iwhen(f)(g))"
apply (rule monofunI [rule_format])
apply (rule_tac p = "x" in IssumE)
apply simp
apply (rule_tac p = "y" in IssumE)
apply simp
apply (rule_tac P = "xa=UU" in notE)
apply assumption
apply (rule UU_I)
apply (rule less_ssum2a [THEN iffD1])
apply assumption
apply simp
apply (rule monofun_cfun_arg)
apply (erule less_ssum2a [THEN iffD1])
apply (simp del: Iwhen2)
apply (rule_tac s = "UU" and t = "xa" in subst)
apply (erule less_ssum2c [THEN iffD1, symmetric])
apply simp
apply (rule_tac p = "y" in IssumE)
apply simp
apply (simp only: less_ssum2d)
apply (simp only: less_ssum2d)
apply simp
apply (rule monofun_cfun_arg)
apply (erule less_ssum2b [THEN iffD1])
done

text {* some kind of exhaustion rules for chains in @{typ "'a ++ 'b"} *}

lemma ssum_lemma1: "[|~(!i.? x. Y(i::nat)=Isinl(x))|] ==> (? i.! x. Y(i)~=Isinl(x))"
by fast

lemma ssum_lemma2: "[|(? i.!x.(Y::nat => 'a++'b)(i::nat)~=Isinl(x::'a))|]   
      ==> (? i y. (Y::nat => 'a++'b)(i::nat)=Isinr(y::'b) & y~=UU)"
apply (erule exE)
apply (rule_tac p = "Y (i) " in IssumE)
apply (drule spec)
apply (erule notE, assumption)
apply (drule spec)
apply (erule notE, assumption)
apply fast
done

lemma ssum_lemma3: "[|chain(Y);(? i x. Y(i)=Isinr(x::'b) & (x::'b)~=UU)|]  
      ==> (!i.? y. Y(i)=Isinr(y))"
apply (erule exE)
apply (erule exE)
apply (rule allI)
apply (rule_tac p = "Y (ia) " in IssumE)
apply (rule exI)
apply (rule trans)
apply (rule_tac [2] strict_IsinlIsinr)
apply assumption
apply (erule_tac [2] exI)
apply (erule conjE)
apply (rule_tac m = "i" and n = "ia" in nat_less_cases)
prefer 2 apply simp
apply (rule exI, rule refl)
apply (erule_tac P = "x=UU" in notE)
apply (rule less_ssum2d [THEN iffD1])
apply (erule_tac s = "Y (i) " and t = "Isinr (x) ::'a++'b" in subst)
apply (erule_tac s = "Y (ia) " and t = "Isinl (xa) ::'a++'b" in subst)
apply (erule chain_mono)
apply assumption
apply (erule_tac P = "xa=UU" in notE)
apply (rule less_ssum2c [THEN iffD1])
apply (erule_tac s = "Y (i) " and t = "Isinr (x) ::'a++'b" in subst)
apply (erule_tac s = "Y (ia) " and t = "Isinl (xa) ::'a++'b" in subst)
apply (erule chain_mono)
apply assumption
done

lemma ssum_lemma4: "chain(Y) ==> (!i.? x. Y(i)=Isinl(x))|(!i.? y. Y(i)=Isinr(y))"
apply (rule case_split_thm)
apply (erule disjI1)
apply (rule disjI2)
apply (erule ssum_lemma3)
apply (rule ssum_lemma2)
apply (erule ssum_lemma1)
done

text {* restricted surjectivity of @{term Isinl} *}

lemma ssum_lemma5: "z=Isinl(x)==> Isinl((Iwhen (LAM x. x) (LAM y. UU))(z)) = z"
apply simp
apply (case_tac "x=UU")
apply simp
apply simp
done

text {* restricted surjectivity of @{term Isinr} *}

lemma ssum_lemma6: "z=Isinr(x)==> Isinr((Iwhen (LAM y. UU) (LAM x. x))(z)) = z"
apply simp
apply (case_tac "x=UU")
apply simp
apply simp
done

text {* technical lemmas *}

lemma ssum_lemma7: "[|Isinl(x) << z; x~=UU|] ==> ? y. z=Isinl(y) & y~=UU"
apply (rule_tac p = "z" in IssumE)
apply simp
apply (erule notE)
apply (rule antisym_less)
apply (erule less_ssum2a [THEN iffD1])
apply (rule minimal)
apply fast
apply simp
apply (rule notE)
apply (erule_tac [2] less_ssum2c [THEN iffD1])
apply assumption
done

lemma ssum_lemma8: "[|Isinr(x) << z; x~=UU|] ==> ? y. z=Isinr(y) & y~=UU"
apply (rule_tac p = "z" in IssumE)
apply simp
apply (erule notE)
apply (erule less_ssum2d [THEN iffD1])
apply simp
apply (rule notE)
apply (erule_tac [2] less_ssum2d [THEN iffD1])
apply assumption
apply fast
done

subsection {* Type @{typ "'a ++ 'b"} is a cpo in three steps *}

lemma lub_ssum1a: "[|chain(Y);(!i.? x. Y(i)=Isinl(x))|] ==> 
      range(Y) <<| Isinl(lub(range(%i.(Iwhen (LAM x. x) (LAM y. UU))(Y i))))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (erule allE)
apply (erule exE)
apply (rule_tac t = "Y (i) " in ssum_lemma5 [THEN subst])
apply assumption
apply (rule monofun_Isinl [THEN monofunE, THEN spec, THEN spec, THEN mp])
apply (rule is_ub_thelub)
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (rule_tac p = "u" in IssumE2)
apply (rule_tac t = "u" in ssum_lemma5 [THEN subst])
apply assumption
apply (rule monofun_Isinl [THEN monofunE, THEN spec, THEN spec, THEN mp])
apply (rule is_lub_thelub)
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (erule monofun_Iwhen3 [THEN ub2ub_monofun])
apply simp
apply (rule less_ssum2c [THEN iffD2])
apply (rule chain_UU_I_inverse)
apply (rule allI)
apply (rule_tac p = "Y (i) " in IssumE)
apply simp
apply simp
apply (erule notE)
apply (rule less_ssum2c [THEN iffD1])
apply (rule_tac t = "Isinl (x) " in subst)
apply assumption
apply (erule ub_rangeD)
apply simp
done

lemma lub_ssum1b: "[|chain(Y);(!i.? x. Y(i)=Isinr(x))|] ==> 
      range(Y) <<| Isinr(lub(range(%i.(Iwhen (LAM y. UU) (LAM x. x))(Y i))))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (erule allE)
apply (erule exE)
apply (rule_tac t = "Y (i) " in ssum_lemma6 [THEN subst])
apply assumption
apply (rule monofun_Isinr [THEN monofunE, THEN spec, THEN spec, THEN mp])
apply (rule is_ub_thelub)
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (rule_tac p = "u" in IssumE2)
apply simp
apply (rule less_ssum2d [THEN iffD2])
apply (rule chain_UU_I_inverse)
apply (rule allI)
apply (rule_tac p = "Y (i) " in IssumE)
apply simp
apply simp
apply (erule notE)
apply (rule less_ssum2d [THEN iffD1])
apply (rule_tac t = "Isinr (y) " in subst)
apply assumption
apply (erule ub_rangeD)
apply (rule_tac t = "u" in ssum_lemma6 [THEN subst])
apply assumption
apply (rule monofun_Isinr [THEN monofunE, THEN spec, THEN spec, THEN mp])
apply (rule is_lub_thelub)
apply (erule monofun_Iwhen3 [THEN ch2ch_monofun])
apply (erule monofun_Iwhen3 [THEN ub2ub_monofun])
done

lemmas thelub_ssum1a = lub_ssum1a [THEN thelubI, standard]
(*
[| chain ?Y1; ! i. ? x. ?Y1 i = Isinl x |] ==>
 lub (range ?Y1) = Isinl
 (lub (range (%i. Iwhen (LAM x. x) (LAM y. UU) (?Y1 i))))
*)

lemmas thelub_ssum1b = lub_ssum1b [THEN thelubI, standard]
(*
[| chain ?Y1; ! i. ? x. ?Y1 i = Isinr x |] ==>
 lub (range ?Y1) = Isinr
 (lub (range (%i. Iwhen (LAM y. UU) (LAM x. x) (?Y1 i))))
*)

lemma cpo_ssum: "chain(Y::nat=>'a ++'b) ==> ? x. range(Y) <<|x"
apply (rule ssum_lemma4 [THEN disjE])
apply assumption
apply (rule exI)
apply (erule lub_ssum1a)
apply assumption
apply (rule exI)
apply (erule lub_ssum1b)
apply assumption
done

instance "++" :: (pcpo, pcpo) cpo
by intro_classes (rule cpo_ssum)

instance "++" :: (pcpo, pcpo) pcpo
by intro_classes (rule least_ssum)

text {* for compatibility with old HOLCF-Version *}
lemma inst_ssum_pcpo: "UU = Isinl UU"
apply (simp add: UU_def UU_ssum_def)
done

declare inst_ssum_pcpo [symmetric, simp]

subsection {* Continuous versions of constants *}

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

text {* continuity for @{term Isinl} and @{term Isinr} *}

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

lemma cont_Isinl [iff]: "cont(Isinl)"
apply (rule monocontlub2cont)
apply (rule monofun_Isinl)
apply (rule contlub_Isinl)
done

lemma cont_Isinr [iff]: "cont(Isinr)"
apply (rule monocontlub2cont)
apply (rule monofun_Isinr)
apply (rule contlub_Isinr)
done

text {* continuity for @{term Iwhen} in the first two arguments *}

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

text {* continuity for @{term Iwhen} in its third argument *}

text {* first 5 ugly lemmas *}

lemma ssum_lemma9: "[| chain(Y); lub(range(Y)) = Isinl(x)|] ==> !i.? x. Y(i)=Isinl(x)"
apply (intro strip)
apply (rule_tac p = "Y (i) " in IssumE)
apply (erule exI)
apply (erule exI)
apply (rule_tac P = "y=UU" in notE)
apply assumption
apply (rule less_ssum2d [THEN iffD1])
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
apply (rule less_ssum2c [THEN iffD1])
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

text {* continuous versions of lemmas for @{typ "'a ++ 'b"} *}

lemma strict_sinl [simp]: "sinl$UU =UU"
apply (unfold sinl_def)
apply (simp add: cont_Isinl)
done

lemma strict_sinr [simp]: "sinr$UU=UU"
apply (unfold sinr_def)
apply (simp add: cont_Isinr)
done

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

lemma defined_sinl [simp]: "x~=UU ==> sinl$x ~= UU"
apply (erule contrapos_nn)
apply (rule inject_sinl)
apply auto
done

lemma defined_sinr [simp]: "x~=UU ==> sinr$x ~= UU"
apply (erule contrapos_nn)
apply (rule inject_sinr)
apply auto
done

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

lemma sscase1 [simp]: 
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

lemma sscase2 [simp]: 
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

lemma sscase3 [simp]: 
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

lemma less_ssum4a: 
        "(sinl$x << sinl$y) = (x << y)"
apply (unfold sinl_def sinr_def)
apply (subst beta_cfun)
apply (rule cont_Isinl)
apply (subst beta_cfun)
apply (rule cont_Isinl)
apply (rule less_ssum2a)
done

lemma less_ssum4b: 
        "(sinr$x << sinr$y) = (x << y)"
apply (unfold sinl_def sinr_def)
apply (subst beta_cfun)
apply (rule cont_Isinr)
apply (subst beta_cfun)
apply (rule cont_Isinr)
apply (rule less_ssum2b)
done

lemma less_ssum4c: 
        "(sinl$x << sinr$y) = (x = UU)"
apply (unfold sinl_def sinr_def)
apply (simplesubst beta_cfun)
apply (rule cont_Isinr)
apply (subst beta_cfun)
apply (rule cont_Isinl)
apply (rule less_ssum2c)
done

lemma less_ssum4d: 
        "(sinr$x << sinl$y) = (x = UU)"
apply (unfold sinl_def sinr_def)
apply (simplesubst beta_cfun)
apply (rule cont_Isinl)
apply (subst beta_cfun)
apply (rule cont_Isinr)
apply (rule less_ssum2d)
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

text {* install simplifier for Ssum *}

lemmas Ssum_rews = strict_sinl strict_sinr defined_sinl defined_sinr
                sscase1 sscase2 sscase3

text {* for backward compatibility *}

lemmas less_ssum3a = less_ssum2a
lemmas less_ssum3b = less_ssum2b
lemmas less_ssum3c = less_ssum2c
lemmas less_ssum3d = less_ssum2d

end
