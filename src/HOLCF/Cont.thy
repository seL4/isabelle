(*  Title:      HOLCF/cont.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

    Results about continuity and monotonicity
*)

header {* Continuity and monotonicity *}

theory Cont
imports FunCpo
begin

text {*
   Now we change the default class! Form now on all untyped type variables are
   of default class po
*}

defaultsort po

consts  
        monofun :: "('a => 'b) => bool"  -- "monotonicity"
        contlub :: "('a::cpo => 'b::cpo) => bool"  -- "first cont. def"
        cont    :: "('a::cpo => 'b::cpo) => bool"  -- "secnd cont. def"

defs 

monofun:         "monofun(f) == ! x y. x << y --> f(x) << f(y)"

contlub:         "contlub(f) == ! Y. chain(Y) --> 
                                f(lub(range(Y))) = lub(range(% i. f(Y(i))))"

cont:            "cont(f)   == ! Y. chain(Y) --> 
                                range(% i. f(Y(i))) <<| f(lub(range(Y)))"

text {*
  the main purpose of cont.thy is to show:
  @{prop "monofun(f) & contlub(f) == cont(f)"}
*}

text {* access to definition *}

lemma contlubI:
        "! Y. chain(Y) --> f(lub(range(Y))) = lub(range(%i. f(Y(i))))==>
        contlub(f)"
by (unfold contlub)

lemma contlubE: 
        " contlub(f)==> 
          ! Y. chain(Y) --> f(lub(range(Y))) = lub(range(%i. f(Y(i))))"
by (unfold contlub)

lemma contI: 
 "! Y. chain(Y) --> range(% i. f(Y(i))) <<| f(lub(range(Y))) ==> cont(f)"
by (unfold cont)

lemma contE: 
 "cont(f) ==> ! Y. chain(Y) --> range(% i. f(Y(i))) <<| f(lub(range(Y)))"
by (unfold cont)

lemma monofunI: 
        "! x y. x << y --> f(x) << f(y) ==> monofun(f)"
by (unfold monofun)

lemma monofunE: 
        "monofun(f) ==> ! x y. x << y --> f(x) << f(y)"
by (unfold monofun)

text {* monotone functions map chains to chains *}

lemma ch2ch_monofun: 
        "[| monofun(f); chain(Y) |] ==> chain(%i. f(Y(i)))"
apply (rule chainI)
apply (erule monofunE [rule_format])
apply (erule chainE)
done

text {* monotone functions map upper bound to upper bounds *}

lemma ub2ub_monofun: 
 "[| monofun(f); range(Y) <| u|]  ==> range(%i. f(Y(i))) <| f(u)"
apply (rule ub_rangeI)
apply (erule monofunE [rule_format])
apply (erule ub_rangeD)
done

text {* left to right: @{prop "monofun(f) & contlub(f) ==> cont(f)"} *}

lemma monocontlub2cont: 
        "[|monofun(f);contlub(f)|] ==> cont(f)"
apply (rule contI [rule_format])
apply (rule thelubE)
apply (erule ch2ch_monofun)
apply assumption
apply (erule contlubE [rule_format, symmetric])
apply assumption
done

text {* first a lemma about binary chains *}

lemma binchain_cont: "[| cont(f); x << y |]   
      ==> range(%i::nat. f(if i = 0 then x else y)) <<| f(y)"
apply (rule subst)
prefer 2 apply (erule contE [rule_format])
apply (erule bin_chain)
apply (rule_tac y = "y" in arg_cong)
apply (erule lub_bin_chain [THEN thelubI])
done

text {* right to left: @{prop "cont(f) ==> monofun(f) & contlub(f)"} *}
text {* part1: @{prop "cont(f) ==> monofun(f)"} *}

lemma cont2mono: "cont(f) ==> monofun(f)"
apply (rule monofunI [rule_format])
apply (drule binchain_cont [THEN is_ub_lub])
apply (auto split add: split_if_asm)
done

text {* right to left: @{prop "cont(f) ==> monofun(f) & contlub(f)"} *}
text {* part2: @{prop "cont(f) ==> contlub(f)"} *}

lemma cont2contlub: "cont(f) ==> contlub(f)"
apply (rule contlubI [rule_format])
apply (rule thelubI [symmetric])
apply (erule contE [rule_format])
apply assumption
done

text {* monotone functions map finite chains to finite chains *}

lemma monofun_finch2finch: 
  "[| monofun f; finite_chain Y |] ==> finite_chain (%n. f (Y n))"
apply (unfold finite_chain_def)
apply (force elim!: ch2ch_monofun simp add: max_in_chain_def)
done

text {* The same holds for continuous functions *}

lemmas cont_finch2finch = cont2mono [THEN monofun_finch2finch, standard]
(* [| cont ?f; finite_chain ?Y |] ==> finite_chain (%n. ?f (?Y n)) *)

text {*
  The following results are about a curried function that is monotone
  in both arguments
*}

lemma ch2ch_MF2L: 
"[|monofun(MF2); chain(F)|] ==> chain(%i. MF2 (F i) x)"
by (erule ch2ch_monofun [THEN ch2ch_fun])

lemma ch2ch_MF2R: 
"[|monofun(MF2(f)); chain(Y)|] ==> chain(%i. MF2 f (Y i))"
by (erule ch2ch_monofun)

lemma ch2ch_MF2LR: 
"[|monofun(MF2); !f. monofun(MF2(f)); chain(F); chain(Y)|] ==>  
   chain(%i. MF2(F(i))(Y(i)))"
apply (rule chainI)
apply (rule trans_less)
apply (erule ch2ch_MF2L [THEN chainE])
apply assumption
apply (rule monofunE [rule_format], erule spec)
apply (erule chainE)
done

lemma ch2ch_lubMF2R: 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo)); 
   !f. monofun(MF2(f)::('b::po=>'c::cpo)); 
        chain(F);chain(Y)|] ==>  
        chain(%j. lub(range(%i. MF2 (F j) (Y i))))"
apply (rule lub_mono [THEN chainI])
apply (rule ch2ch_MF2R, erule spec)
apply assumption
apply (rule ch2ch_MF2R, erule spec)
apply assumption
apply (rule allI)
apply (rule chainE)
apply (erule ch2ch_MF2L)
apply assumption
done

lemma ch2ch_lubMF2L: 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo)); 
   !f. monofun(MF2(f)::('b::po=>'c::cpo)); 
        chain(F);chain(Y)|] ==>  
        chain(%i. lub(range(%j. MF2 (F j) (Y i))))"
apply (rule lub_mono [THEN chainI])
apply (erule ch2ch_MF2L)
apply assumption
apply (erule ch2ch_MF2L)
apply assumption
apply (rule allI)
apply (rule chainE)
apply (rule ch2ch_MF2R, erule spec)
apply assumption
done

lemma lub_MF2_mono: 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo)); 
   !f. monofun(MF2(f)::('b::po=>'c::cpo)); 
        chain(F)|] ==>  
        monofun(% x. lub(range(% j. MF2 (F j) (x))))"
apply (rule monofunI [rule_format])
apply (rule lub_mono)
apply (erule ch2ch_MF2L)
apply assumption
apply (erule ch2ch_MF2L)
apply assumption
apply (rule allI)
apply (rule monofunE [rule_format], erule spec)
apply assumption
done

lemma ex_lubMF2: 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo)); 
   !f. monofun(MF2(f)::('b::po=>'c::cpo)); 
        chain(F); chain(Y)|] ==>  
                lub(range(%j. lub(range(%i. MF2(F j) (Y i))))) = 
                lub(range(%i. lub(range(%j. MF2(F j) (Y i)))))"
apply (rule antisym_less)
apply (rule is_lub_thelub[OF _ ub_rangeI])
apply (erule ch2ch_lubMF2R)
apply (assumption+)
apply (rule lub_mono)
apply (rule ch2ch_MF2R, erule spec)
apply assumption
apply (erule ch2ch_lubMF2L)
apply (assumption+)
apply (rule allI)
apply (rule is_ub_thelub)
apply (erule ch2ch_MF2L)
apply assumption
apply (rule is_lub_thelub[OF _ ub_rangeI])
apply (erule ch2ch_lubMF2L)
apply (assumption+)
apply (rule lub_mono)
apply (erule ch2ch_MF2L)
apply assumption
apply (erule ch2ch_lubMF2R)
apply (assumption+)
apply (rule allI)
apply (rule is_ub_thelub)
apply (rule ch2ch_MF2R, erule spec)
apply assumption
done

lemma diag_lubMF2_1: 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo)); 
   !f. monofun(MF2(f)::('b::po=>'c::cpo)); 
   chain(FY);chain(TY)|] ==> 
  lub(range(%i. lub(range(%j. MF2(FY(j))(TY(i)))))) = 
  lub(range(%i. MF2(FY(i))(TY(i))))"
apply (rule antisym_less)
apply (rule is_lub_thelub[OF _ ub_rangeI])
apply (erule ch2ch_lubMF2L)
apply (assumption+)
apply (rule lub_mono3)
apply (erule ch2ch_MF2L)
apply (assumption+)
apply (erule ch2ch_MF2LR)
apply (assumption+)
apply (rule allI)
apply (rule_tac m = "i" and n = "ia" in nat_less_cases)
apply (rule_tac x = "ia" in exI)
apply (rule chain_mono)
apply (erule allE)
apply (erule ch2ch_MF2R)
apply (assumption+)
apply (erule ssubst)
apply (rule_tac x = "ia" in exI)
apply (rule refl_less)
apply (rule_tac x = "i" in exI)
apply (rule chain_mono)
apply (erule ch2ch_MF2L)
apply (assumption+)
apply (rule lub_mono)
apply (erule ch2ch_MF2LR)
apply (assumption+)
apply (erule ch2ch_lubMF2L)
apply (assumption+)
apply (rule allI)
apply (rule is_ub_thelub)
apply (erule ch2ch_MF2L)
apply assumption
done

lemma diag_lubMF2_2: 
"[|monofun(MF2::('a::po=>'b::po=>'c::cpo)); 
   !f. monofun(MF2(f)::('b::po=>'c::cpo)); 
   chain(FY);chain(TY)|] ==> 
  lub(range(%j. lub(range(%i. MF2(FY(j))(TY(i)))))) = 
  lub(range(%i. MF2(FY(i))(TY(i))))"
apply (rule trans)
apply (rule ex_lubMF2)
apply (assumption+)
apply (erule diag_lubMF2_1)
apply (assumption+)
done

text {*
  The following results are about a curried function that is continuous
  in both arguments
*}

lemma contlub_CF2:
assumes prem1: "cont(CF2)"
assumes prem2: "!f. cont(CF2(f))"
assumes prem3: "chain(FY)"
assumes prem4: "chain(TY)"
shows "CF2(lub(range(FY)))(lub(range(TY))) = lub(range(%i. CF2(FY(i))(TY(i))))"
apply (subst prem1 [THEN cont2contlub, THEN contlubE, THEN spec, THEN mp])
apply assumption
apply (subst thelub_fun)
apply (rule prem1 [THEN cont2mono [THEN ch2ch_monofun]])
apply assumption
apply (rule trans)
apply (rule prem2 [THEN spec, THEN cont2contlub, THEN contlubE, THEN spec, THEN mp, THEN ext, THEN arg_cong, THEN arg_cong])
apply (rule prem4)
apply (rule diag_lubMF2_2)
apply (auto simp add: cont2mono prems)
done

text {*
  The following results are about application for functions in @{typ "'a=>'b"}
*}

lemma monofun_fun_fun: "f1 << f2 ==> f1(x) << f2(x)"
by (erule less_fun [THEN iffD1, THEN spec])

lemma monofun_fun_arg: "[|monofun(f); x1 << x2|] ==> f(x1) << f(x2)"
by (erule monofunE [THEN spec, THEN spec, THEN mp])

lemma monofun_fun: "[|monofun(f1); monofun(f2); f1 << f2; x1 << x2|] ==> f1(x1) << f2(x2)"
apply (rule trans_less)
apply (erule monofun_fun_arg)
apply assumption
apply (erule monofun_fun_fun)
done

text {*
  The following results are about the propagation of monotonicity and
  continuity
*}

lemma mono2mono_MF1L: "[|monofun(c1)|] ==> monofun(%x. c1 x y)"
apply (rule monofunI [rule_format])
apply (erule monofun_fun_arg [THEN monofun_fun_fun])
apply assumption
done

lemma cont2cont_CF1L: "[|cont(c1)|] ==> cont(%x. c1 x y)"
apply (rule monocontlub2cont)
apply (erule cont2mono [THEN mono2mono_MF1L])
apply (rule contlubI [rule_format])
apply (frule asm_rl)
apply (erule cont2contlub [THEN contlubE, THEN spec, THEN mp, THEN ssubst])
apply assumption
apply (subst thelub_fun)
apply (rule ch2ch_monofun)
apply (erule cont2mono)
apply assumption
apply (rule refl)
done

(*********  Note "(%x.%y.c1 x y) = c1" ***********)

lemma mono2mono_MF1L_rev: "!y. monofun(%x. c1 x y) ==> monofun(c1)"
apply (rule monofunI [rule_format])
apply (rule less_fun [THEN iffD2])
apply (blast dest: monofunE)
done

lemma cont2cont_CF1L_rev: "!y. cont(%x. c1 x y) ==> cont(c1)"
apply (rule monocontlub2cont)
apply (rule cont2mono [THEN allI, THEN mono2mono_MF1L_rev])
apply (erule spec)
apply (rule contlubI [rule_format])
apply (rule ext)
apply (subst thelub_fun)
apply (rule cont2mono [THEN allI, THEN mono2mono_MF1L_rev, THEN ch2ch_monofun])
apply (erule spec)
apply assumption
apply (blast dest: cont2contlub [THEN contlubE])
done

text {*
  What D.A.Schmidt calls continuity of abstraction
  never used here
*}

lemma contlub_abstraction: 
"[|chain(Y::nat=>'a);!y. cont(%x.(c::'a::cpo=>'b::cpo=>'c::cpo) x y)|] ==> 
  (%y. lub(range(%i. c (Y i) y))) = (lub(range(%i.%y. c (Y i) y)))"
apply (rule trans)
prefer 2 apply (rule cont2contlub [THEN contlubE, THEN spec, THEN mp])
prefer 2 apply (assumption)
apply (erule cont2cont_CF1L_rev)
apply (rule ext)
apply (rule cont2contlub [THEN contlubE, THEN spec, THEN mp, symmetric])
apply (erule spec)
apply assumption
done

lemma mono2mono_app: "[|monofun(ft);!x. monofun(ft(x));monofun(tt)|] ==> 
         monofun(%x.(ft(x))(tt(x)))"
apply (rule monofunI [rule_format])
apply (rule_tac ?f1.0 = "ft(x)" and ?f2.0 = "ft(y)" in monofun_fun)
apply (erule spec)
apply (erule spec)
apply (erule monofunE [rule_format])
apply assumption
apply (erule monofunE [rule_format])
apply assumption
done

lemma cont2contlub_app: "[|cont(ft);!x. cont(ft(x));cont(tt)|] ==> contlub(%x.(ft(x))(tt(x)))"
apply (rule contlubI [rule_format])
apply (rule_tac f3 = "tt" in contlubE [THEN spec, THEN mp, THEN ssubst])
apply (erule cont2contlub)
apply assumption
apply (rule contlub_CF2)
apply (assumption+)
apply (erule cont2mono [THEN ch2ch_monofun])
apply assumption
done

lemma cont2cont_app: "[|cont(ft); !x. cont(ft(x)); cont(tt)|] ==> cont(%x.(ft(x))(tt(x)))"
apply (blast intro: monocontlub2cont mono2mono_app cont2mono cont2contlub_app)
done

lemmas cont2cont_app2 = cont2cont_app[OF _ allI]
(*  [| cont ?ft; !!x. cont (?ft x); cont ?tt |] ==> *)
(*        cont (%x. ?ft x (?tt x))                    *)


text {* The identity function is continuous *}

lemma cont_id: "cont(% x. x)"
apply (rule contI [rule_format])
apply (erule thelubE)
apply (rule refl)
done

text {* constant functions are continuous *}

lemma cont_const: "cont(%x. c)"
apply (rule contI [rule_format])
apply (blast intro: is_lubI ub_rangeI dest: ub_rangeD)
done

lemma cont2cont_app3: "[|cont(f); cont(t) |] ==> cont(%x. f(t(x)))"
by (best intro: cont2cont_app2 cont_const)

text {* A non-emptiness result for Cfun *}

lemma CfunI: "?x:Collect cont"
apply (rule CollectI)
apply (rule cont_const)
done

text {* some properties of flat *}

lemma flatdom2monofun: "f UU = UU ==> monofun (f::'a::flat=>'b::pcpo)"
apply (rule monofunI [rule_format])
apply (drule ax_flat [rule_format])
apply auto
done

declare range_composition [simp del]

lemma chfindom_monofun2cont: "monofun f ==> cont(f::'a::chfin=>'b::pcpo)"
apply (rule monocontlub2cont)
apply assumption
apply (rule contlubI [rule_format])
apply (frule chfin2finch)
apply (rule antisym_less)
apply (clarsimp simp add: finite_chain_def maxinch_is_thelub)
apply (rule is_ub_thelub)
apply (erule ch2ch_monofun)
apply assumption
apply (drule monofun_finch2finch[COMP swap_prems_rl])
apply assumption
apply (simp add: finite_chain_def)
apply (erule conjE)
apply (erule exE)
apply (simp add: maxinch_is_thelub)
apply (erule monofunE [THEN spec, THEN spec, THEN mp])
apply (erule is_ub_thelub)
done

lemmas flatdom_strict2cont = flatdom2monofun [THEN chfindom_monofun2cont, standard]
(* f UU = UU ==> cont (f::'a=>'b::pcpo)" *)

end
