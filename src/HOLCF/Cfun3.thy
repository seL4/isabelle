(*  Title:      HOLCF/Cfun3.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class instance of  -> for class pcpo

*)

theory Cfun3 = Cfun2:

instance "->" :: (cpo,cpo)cpo
by (intro_classes, rule cpo_cfun)

instance "->" :: (cpo,pcpo)pcpo
by (intro_classes, rule least_cfun)

defaultsort pcpo

consts  
        Istrictify   :: "('a->'b)=>'a=>'b"
        strictify    :: "('a->'b)->'a->'b"
defs

Istrictify_def:  "Istrictify f x == if x=UU then UU else f$x"    
strictify_def:   "strictify == (LAM f x. Istrictify f x)"

consts
        ID      :: "('a::cpo) -> 'a"
        cfcomp  :: "('b->'c)->(('a::cpo)->('b::cpo))->'a->('c::cpo)"

syntax  "@oo"   :: "('b->'c)=>('a->'b)=>'a->'c" ("_ oo _" [101,100] 100)
     
translations    "f1 oo f2" == "cfcomp$f1$f2"

defs

  ID_def:        "ID ==(LAM x. x)"
  oo_def:        "cfcomp == (LAM f g x. f$(g$x))" 

(*  Title:      HOLCF/Cfun3
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class instance of  -> for class pcpo
*)

(* for compatibility with old HOLCF-Version *)
lemma inst_cfun_pcpo: "UU = Abs_CFun(%x. UU)"
apply (simp add: UU_def UU_cfun_def)
done

(* ------------------------------------------------------------------------ *)
(* the contlub property for Rep_CFun its 'first' argument                       *)
(* ------------------------------------------------------------------------ *)

lemma contlub_Rep_CFun1: "contlub(Rep_CFun)"
apply (rule contlubI)
apply (intro strip)
apply (rule expand_fun_eq [THEN iffD2])
apply (intro strip)
apply (subst thelub_cfun)
apply assumption
apply (subst Cfunapp2)
apply (erule cont_lubcfun)
apply (subst thelub_fun)
apply (erule monofun_Rep_CFun1 [THEN ch2ch_monofun])
apply (rule refl)
done


(* ------------------------------------------------------------------------ *)
(* the cont property for Rep_CFun in its first argument                        *)
(* ------------------------------------------------------------------------ *)

lemma cont_Rep_CFun1: "cont(Rep_CFun)"
apply (rule monocontlub2cont)
apply (rule monofun_Rep_CFun1)
apply (rule contlub_Rep_CFun1)
done


(* ------------------------------------------------------------------------ *)
(* contlub, cont properties of Rep_CFun in its first argument in mixfix _[_]   *)
(* ------------------------------------------------------------------------ *)

lemma contlub_cfun_fun: 
"chain(FY) ==> 
  lub(range FY)$x = lub(range (%i. FY(i)$x))"
apply (rule trans)
apply (erule contlub_Rep_CFun1 [THEN contlubE, THEN spec, THEN mp, THEN fun_cong])
apply (subst thelub_fun)
apply (erule monofun_Rep_CFun1 [THEN ch2ch_monofun])
apply (rule refl)
done


lemma cont_cfun_fun: 
"chain(FY) ==> 
  range(%i. FY(i)$x) <<| lub(range FY)$x"
apply (rule thelubE)
apply (erule ch2ch_Rep_CFunL)
apply (erule contlub_cfun_fun [symmetric])
done


(* ------------------------------------------------------------------------ *)
(* contlub, cont  properties of Rep_CFun in both argument in mixfix _[_]       *)
(* ------------------------------------------------------------------------ *)

lemma contlub_cfun: 
"[|chain(FY);chain(TY)|] ==> 
  (lub(range FY))$(lub(range TY)) = lub(range(%i. FY(i)$(TY i)))"
apply (rule contlub_CF2)
apply (rule cont_Rep_CFun1)
apply (rule allI)
apply (rule cont_Rep_CFun2)
apply assumption
apply assumption
done

lemma cont_cfun: 
"[|chain(FY);chain(TY)|] ==> 
  range(%i.(FY i)$(TY i)) <<| (lub (range FY))$(lub(range TY))"
apply (rule thelubE)
apply (rule monofun_Rep_CFun1 [THEN ch2ch_MF2LR])
apply (rule allI)
apply (rule monofun_Rep_CFun2)
apply assumption
apply assumption
apply (erule contlub_cfun [symmetric])
apply assumption
done


(* ------------------------------------------------------------------------ *)
(* cont2cont lemma for Rep_CFun                                               *)
(* ------------------------------------------------------------------------ *)

lemma cont2cont_Rep_CFun: "[|cont(%x. ft x);cont(%x. tt x)|] ==> cont(%x. (ft x)$(tt x))"
apply (best intro: cont2cont_app2 cont_const cont_Rep_CFun1 cont_Rep_CFun2)
done



(* ------------------------------------------------------------------------ *)
(* cont2mono Lemma for %x. LAM y. c1(x)(y)                                  *)
(* ------------------------------------------------------------------------ *)

lemma cont2mono_LAM:
assumes p1: "!!x. cont(c1 x)"
assumes p2: "!!y. monofun(%x. c1 x y)"
shows "monofun(%x. LAM y. c1 x y)"
apply (rule monofunI)
apply (intro strip)
apply (subst less_cfun)
apply (subst less_fun)
apply (rule allI)
apply (subst beta_cfun)
apply (rule p1)
apply (subst beta_cfun)
apply (rule p1)
apply (erule p2 [THEN monofunE, THEN spec, THEN spec, THEN mp])
done

(* ------------------------------------------------------------------------ *)
(* cont2cont Lemma for %x. LAM y. c1 x y)                                 *)
(* ------------------------------------------------------------------------ *)

lemma cont2cont_LAM:
assumes p1: "!!x. cont(c1 x)"
assumes p2: "!!y. cont(%x. c1 x y)"
shows "cont(%x. LAM y. c1 x y)"
apply (rule monocontlub2cont)
apply (rule p1 [THEN cont2mono_LAM])
apply (rule p2 [THEN cont2mono])
apply (rule contlubI)
apply (intro strip)
apply (subst thelub_cfun)
apply (rule p1 [THEN cont2mono_LAM, THEN ch2ch_monofun])
apply (rule p2 [THEN cont2mono])
apply assumption
apply (rule_tac f = "Abs_CFun" in arg_cong)
apply (rule ext)
apply (subst p1 [THEN beta_cfun, THEN ext])
apply (erule p2 [THEN cont2contlub, THEN contlubE, THEN spec, THEN mp])
done

(* ------------------------------------------------------------------------ *)
(* cont2cont tactic                                                       *)
(* ------------------------------------------------------------------------ *)

lemmas cont_lemmas1 = cont_const cont_id cont_Rep_CFun2
                    cont2cont_Rep_CFun cont2cont_LAM

declare cont_lemmas1 [simp]

(* HINT: cont_tac is now installed in simplifier in Lift.ML ! *)

(*val cont_tac = (fn i => (resolve_tac cont_lemmas i));*)
(*val cont_tacR = (fn i => (REPEAT (cont_tac i)));*)

(* ------------------------------------------------------------------------ *)
(* function application _[_]  is strict in its first arguments              *)
(* ------------------------------------------------------------------------ *)

lemma strict_Rep_CFun1: "(UU::'a::cpo->'b)$x = (UU::'b)"
apply (subst inst_cfun_pcpo)
apply (subst beta_cfun)
apply (simp (no_asm))
apply (rule refl)
done


(* ------------------------------------------------------------------------ *)
(* results about strictify                                                  *)
(* ------------------------------------------------------------------------ *)

lemma Istrictify1: 
        "Istrictify(f)(UU)= (UU)"
apply (unfold Istrictify_def)
apply (simp (no_asm))
done

lemma Istrictify2: 
        "~x=UU ==> Istrictify(f)(x)=f$x"
apply (unfold Istrictify_def)
apply (simp (no_asm_simp))
done

lemma monofun_Istrictify1: "monofun(Istrictify)"
apply (rule monofunI)
apply (intro strip)
apply (rule less_fun [THEN iffD2])
apply (intro strip)
apply (rule_tac Q = "xa=UU" in excluded_middle [THEN disjE])
apply (subst Istrictify2)
apply assumption
apply (subst Istrictify2)
apply assumption
apply (rule monofun_cfun_fun)
apply assumption
apply (erule ssubst)
apply (subst Istrictify1)
apply (subst Istrictify1)
apply (rule refl_less)
done

lemma monofun_Istrictify2: "monofun(Istrictify(f))"
apply (rule monofunI)
apply (intro strip)
apply (rule_tac Q = "x=UU" in excluded_middle [THEN disjE])
apply (simplesubst Istrictify2)
apply (erule notUU_I)
apply assumption
apply (subst Istrictify2)
apply assumption
apply (rule monofun_cfun_arg)
apply assumption
apply (erule ssubst)
apply (subst Istrictify1)
apply (rule minimal)
done


lemma contlub_Istrictify1: "contlub(Istrictify)"
apply (rule contlubI)
apply (intro strip)
apply (rule expand_fun_eq [THEN iffD2])
apply (intro strip)
apply (subst thelub_fun)
apply (erule monofun_Istrictify1 [THEN ch2ch_monofun])
apply (rule_tac Q = "x=UU" in excluded_middle [THEN disjE])
apply (subst Istrictify2)
apply assumption
apply (subst Istrictify2 [THEN ext])
apply assumption
apply (subst thelub_cfun)
apply assumption
apply (subst beta_cfun)
apply (rule cont_lubcfun)
apply assumption
apply (rule refl)
apply (erule ssubst)
apply (subst Istrictify1)
apply (subst Istrictify1 [THEN ext])
apply (rule chain_UU_I_inverse [symmetric])
apply (rule refl [THEN allI])
done

lemma contlub_Istrictify2: "contlub(Istrictify(f::'a -> 'b))"
apply (rule contlubI)
apply (intro strip)
apply (case_tac "lub (range (Y))= (UU::'a) ")
apply (simp (no_asm_simp) add: Istrictify1 chain_UU_I_inverse chain_UU_I Istrictify1)
apply (subst Istrictify2)
apply assumption
apply (rule_tac s = "lub (range (%i. f$ (Y i))) " in trans)
apply (rule contlub_cfun_arg)
apply assumption
apply (rule lub_equal2)
prefer 3 apply (best intro: ch2ch_monofun monofun_Istrictify2)
prefer 2 apply (best intro: ch2ch_monofun monofun_Rep_CFun2)
apply (rule chain_mono2 [THEN exE])
prefer 2 apply (assumption)
apply (erule chain_UU_I_inverse2)
apply (blast intro: Istrictify2 [symmetric])
done


lemmas cont_Istrictify1 = contlub_Istrictify1 [THEN monofun_Istrictify1 [THEN monocontlub2cont], standard]

lemmas cont_Istrictify2 = contlub_Istrictify2 [THEN monofun_Istrictify2 [THEN monocontlub2cont], standard]


lemma strictify1: "strictify$f$UU=UU"
apply (unfold strictify_def)
apply (subst beta_cfun)
apply (simp (no_asm) add: cont_Istrictify2 cont_Istrictify1 cont2cont_CF1L)
apply (subst beta_cfun)
apply (rule cont_Istrictify2)
apply (rule Istrictify1)
done

lemma strictify2: "~x=UU ==> strictify$f$x=f$x"
apply (unfold strictify_def)
apply (subst beta_cfun)
apply (simp (no_asm) add: cont_Istrictify2 cont_Istrictify1 cont2cont_CF1L)
apply (subst beta_cfun)
apply (rule cont_Istrictify2)
apply (erule Istrictify2)
done


(* ------------------------------------------------------------------------ *)
(* Instantiate the simplifier                                               *)
(* ------------------------------------------------------------------------ *)

declare minimal [simp] refl_less [simp] beta_cfun [simp] strict_Rep_CFun1 [simp] strictify1 [simp] strictify2 [simp]


(* ------------------------------------------------------------------------ *)
(* use cont_tac as autotac.                                                *)
(* ------------------------------------------------------------------------ *)

(* HINT: cont_tac is now installed in simplifier in Lift.ML ! *)
(*simpset_ref() := simpset() addsolver (K (DEPTH_SOLVE_1 o cont_tac));*)

(* ------------------------------------------------------------------------ *)
(* some lemmata for functions with flat/chfin domain/range types	    *)
(* ------------------------------------------------------------------------ *)

lemma chfin_Rep_CFunR: "chain (Y::nat => 'a::cpo->'b::chfin)  
      ==> !s. ? n. lub(range(Y))$s = Y n$s"
apply (rule allI)
apply (subst contlub_cfun_fun)
apply assumption
apply (fast intro!: thelubI chfin lub_finch2 chfin2finch ch2ch_Rep_CFunL)
done

(* ------------------------------------------------------------------------ *)
(* continuous isomorphisms are strict                                       *)
(* a prove for embedding projection pairs is similar                        *)
(* ------------------------------------------------------------------------ *)

lemma iso_strict: 
"!!f g.[|!y. f$(g$y)=(y::'b) ; !x. g$(f$x)=(x::'a) |]  
  ==> f$UU=UU & g$UU=UU"
apply (rule conjI)
apply (rule UU_I)
apply (rule_tac s = "f$ (g$ (UU::'b))" and t = "UU::'b" in subst)
apply (erule spec)
apply (rule minimal [THEN monofun_cfun_arg])
apply (rule UU_I)
apply (rule_tac s = "g$ (f$ (UU::'a))" and t = "UU::'a" in subst)
apply (erule spec)
apply (rule minimal [THEN monofun_cfun_arg])
done


lemma isorep_defined: "[|!x. rep$(ab$x)=x;!y. ab$(rep$y)=y; z~=UU|] ==> rep$z ~= UU"
apply (erule contrapos_nn)
apply (drule_tac f = "ab" in cfun_arg_cong)
apply (erule box_equals)
apply fast
apply (erule iso_strict [THEN conjunct1])
apply assumption
done

lemma isoabs_defined: "[|!x. rep$(ab$x) = x;!y. ab$(rep$y)=y ; z~=UU|] ==> ab$z ~= UU"
apply (erule contrapos_nn)
apply (drule_tac f = "rep" in cfun_arg_cong)
apply (erule box_equals)
apply fast
apply (erule iso_strict [THEN conjunct2])
apply assumption
done

(* ------------------------------------------------------------------------ *)
(* propagation of flatness and chainfiniteness by continuous isomorphisms   *)
(* ------------------------------------------------------------------------ *)

lemma chfin2chfin: "!!f g.[|! Y::nat=>'a. chain Y --> (? n. max_in_chain n Y);  
  !y. f$(g$y)=(y::'b) ; !x. g$(f$x)=(x::'a::chfin) |]  
  ==> ! Y::nat=>'b. chain Y --> (? n. max_in_chain n Y)"
apply (unfold max_in_chain_def)
apply (intro strip)
apply (rule exE)
apply (rule_tac P = "chain (%i. g$ (Y i))" in mp)
apply (erule spec)
apply (erule ch2ch_Rep_CFunR)
apply (rule exI)
apply (intro strip)
apply (rule_tac s = "f$ (g$ (Y x))" and t = "Y (x) " in subst)
apply (erule spec)
apply (rule_tac s = "f$ (g$ (Y j))" and t = "Y (j) " in subst)
apply (erule spec)
apply (rule cfun_arg_cong)
apply (rule mp)
apply (erule spec)
apply assumption
done


lemma flat2flat: "!!f g.[|!x y::'a. x<<y --> x=UU | x=y;  
  !y. f$(g$y)=(y::'b); !x. g$(f$x)=(x::'a)|] ==> !x y::'b. x<<y --> x=UU | x=y"
apply (intro strip)
apply (rule disjE)
apply (rule_tac P = "g$x<<g$y" in mp)
apply (erule_tac [2] monofun_cfun_arg)
apply (drule spec)
apply (erule spec)
apply (rule disjI1)
apply (rule trans)
apply (rule_tac s = "f$ (g$x) " and t = "x" in subst)
apply (erule spec)
apply (erule cfun_arg_cong)
apply (rule iso_strict [THEN conjunct1])
apply assumption
apply assumption
apply (rule disjI2)
apply (rule_tac s = "f$ (g$x) " and t = "x" in subst)
apply (erule spec)
apply (rule_tac s = "f$ (g$y) " and t = "y" in subst)
apply (erule spec)
apply (erule cfun_arg_cong)
done

(* ------------------------------------------------------------------------- *)
(* a result about functions with flat codomain                               *)
(* ------------------------------------------------------------------------- *)

lemma flat_codom: "f$(x::'a)=(c::'b::flat) ==> f$(UU::'a)=(UU::'b) | (!z. f$(z::'a)=c)"
apply (case_tac "f$ (x::'a) = (UU::'b) ")
apply (rule disjI1)
apply (rule UU_I)
apply (rule_tac s = "f$ (x) " and t = "UU::'b" in subst)
apply assumption
apply (rule minimal [THEN monofun_cfun_arg])
apply (case_tac "f$ (UU::'a) = (UU::'b) ")
apply (erule disjI1)
apply (rule disjI2)
apply (rule allI)
apply (erule subst)
apply (rule_tac a = "f$ (UU::'a) " in refl [THEN box_equals])
apply (rule_tac fo5 = "f" in minimal [THEN monofun_cfun_arg, THEN ax_flat [THEN spec, THEN spec, THEN mp], THEN disjE])
apply simp
apply assumption
apply (rule_tac fo5 = "f" in minimal [THEN monofun_cfun_arg, THEN ax_flat [THEN spec, THEN spec, THEN mp], THEN disjE])
apply simp
apply assumption
done


(* ------------------------------------------------------------------------ *)
(* Access to definitions                                                    *)
(* ------------------------------------------------------------------------ *)


lemma ID1: "ID$x=x"
apply (unfold ID_def)
apply (subst beta_cfun)
apply (rule cont_id)
apply (rule refl)
done

lemma cfcomp1: "(f oo g)=(LAM x. f$(g$x))"
apply (unfold oo_def)
apply (subst beta_cfun)
apply (simp (no_asm))
apply (subst beta_cfun)
apply (simp (no_asm))
apply (rule refl)
done

lemma cfcomp2: "(f oo g)$x=f$(g$x)"
apply (subst cfcomp1)
apply (subst beta_cfun)
apply (simp (no_asm))
apply (rule refl)
done


(* ------------------------------------------------------------------------ *)
(* Show that interpretation of (pcpo,_->_) is a category                    *)
(* The class of objects is interpretation of syntactical class pcpo         *)
(* The class of arrows  between objects 'a and 'b is interpret. of 'a -> 'b *)
(* The identity arrow is interpretation of ID                               *)
(* The composition of f and g is interpretation of oo                       *)
(* ------------------------------------------------------------------------ *)


lemma ID2: "f oo ID = f "
apply (rule ext_cfun)
apply (subst cfcomp2)
apply (subst ID1)
apply (rule refl)
done

lemma ID3: "ID oo f = f "
apply (rule ext_cfun)
apply (subst cfcomp2)
apply (subst ID1)
apply (rule refl)
done


lemma assoc_oo: "f oo (g oo h) = (f oo g) oo h"
apply (rule ext_cfun)
apply (rule_tac s = "f$ (g$ (h$x))" in trans)
apply (subst cfcomp2)
apply (subst cfcomp2)
apply (rule refl)
apply (subst cfcomp2)
apply (subst cfcomp2)
apply (rule refl)
done

(* ------------------------------------------------------------------------ *)
(* Merge the different rewrite rules for the simplifier                     *)
(* ------------------------------------------------------------------------ *)

declare  ID1[simp] ID2[simp] ID3[simp] cfcomp2[simp]

end
