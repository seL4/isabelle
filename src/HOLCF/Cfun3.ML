(*  Title:      HOLCF/cfun3.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen
*)

open Cfun3;

(* for compatibility with old HOLCF-Version *)
qed_goal "inst_cfun_pcpo" thy "UU = fabs(%x. UU)"
 (fn prems => 
        [
        (simp_tac (HOL_ss addsimps [UU_def,UU_cfun_def]) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* the contlub property for fapp its 'first' argument                       *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_fapp1" thy "contlub(fapp)"
(fn prems =>
        [
        (rtac contlubI 1),
        (strip_tac 1),
        (rtac (expand_fun_eq RS iffD2) 1),
        (strip_tac 1),
        (stac thelub_cfun 1),
        (atac 1),
        (stac Cfunapp2 1),
        (etac cont_lubcfun 1),
        (stac thelub_fun 1),
        (etac (monofun_fapp1 RS ch2ch_monofun) 1),
        (rtac refl 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* the cont property for fapp in its first argument                        *)
(* ------------------------------------------------------------------------ *)

qed_goal "cont_fapp1" thy "cont(fapp)"
(fn prems =>
        [
        (rtac monocontlub2cont 1),
        (rtac monofun_fapp1 1),
        (rtac contlub_fapp1 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* contlub, cont properties of fapp in its first argument in mixfix _[_]   *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_cfun_fun" thy 
"is_chain(FY) ==>\
\ lub(range FY)`x = lub(range (%i. FY(i)`x))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac trans 1),
        (etac (contlub_fapp1 RS contlubE RS spec RS mp RS fun_cong) 1),
        (stac thelub_fun 1),
        (etac (monofun_fapp1 RS ch2ch_monofun) 1),
        (rtac refl 1)
        ]);


qed_goal "cont_cfun_fun" thy 
"is_chain(FY) ==>\
\ range(%i. FY(i)`x) <<| lub(range FY)`x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac thelubE 1),
        (etac ch2ch_fappL 1),
        (etac (contlub_cfun_fun RS sym) 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* contlub, cont  properties of fapp in both argument in mixfix _[_]       *)
(* ------------------------------------------------------------------------ *)

qed_goal "contlub_cfun" thy 
"[|is_chain(FY);is_chain(TY)|] ==>\
\ (lub(range FY))`(lub(range TY)) = lub(range(%i. FY(i)`(TY i)))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac contlub_CF2 1),
        (rtac cont_fapp1 1),
        (rtac allI 1),
        (rtac cont_fapp2 1),
        (atac 1),
        (atac 1)
        ]);

qed_goal "cont_cfun" thy 
"[|is_chain(FY);is_chain(TY)|] ==>\
\ range(%i.(FY i)`(TY i)) <<| (lub (range FY))`(lub(range TY))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac thelubE 1),
        (rtac (monofun_fapp1 RS ch2ch_MF2LR) 1),
        (rtac allI 1),
        (rtac monofun_fapp2 1),
        (atac 1),
        (atac 1),
        (etac (contlub_cfun RS sym) 1),
        (atac 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* cont2cont lemma for fapp                                               *)
(* ------------------------------------------------------------------------ *)

qed_goal "cont2cont_fapp" thy 
        "[|cont(%x. ft x);cont(%x. tt x)|] ==> cont(%x. (ft x)`(tt x))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac cont2cont_app2 1),
        (rtac cont2cont_app2 1),
        (rtac cont_const 1),
        (rtac cont_fapp1 1),
        (atac 1),
        (rtac cont_fapp2 1),
        (atac 1)
        ]);



(* ------------------------------------------------------------------------ *)
(* cont2mono Lemma for %x. LAM y. c1(x)(y)                                  *)
(* ------------------------------------------------------------------------ *)

qed_goal "cont2mono_LAM" thy 
 "[| !!x. cont(c1 x); !!y. monofun(%x. c1 x y)|] ==> monofun(%x. LAM y. c1 x y)"
(fn [p1,p2] =>
        [
        (rtac monofunI 1),
        (strip_tac 1),
        (stac less_cfun 1),
        (stac less_fun 1),
        (rtac allI 1),
        (stac beta_cfun 1),
	(rtac p1 1),
        (stac beta_cfun 1),
	(rtac p1 1),
        (etac (p2 RS monofunE RS spec RS spec RS mp) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* cont2cont Lemma for %x. LAM y. c1 x y)                                 *)
(* ------------------------------------------------------------------------ *)

qed_goal "cont2cont_LAM" thy 
 "[| !!x. cont(c1 x); !!y. cont(%x. c1 x y) |] ==> cont(%x. LAM y. c1 x y)"
(fn [p1,p2] =>
        [
        (rtac monocontlub2cont 1),
        (rtac (p1 RS cont2mono_LAM) 1),
        (rtac (p2 RS cont2mono) 1),
        (rtac contlubI 1),
        (strip_tac 1),
        (stac thelub_cfun 1),
        (rtac (p1 RS cont2mono_LAM RS ch2ch_monofun) 1),
        (rtac (p2 RS cont2mono) 1),
        (atac 1),
        (res_inst_tac [("f","fabs")] arg_cong 1),
        (rtac ext 1),
        (stac (p1 RS beta_cfun RS ext) 1),
        (etac (p2 RS cont2contlub RS contlubE RS spec RS mp) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* cont2cont tactic                                                       *)
(* ------------------------------------------------------------------------ *)

val cont_lemmas1 = [cont_const, cont_id, cont_fapp2,
                    cont2cont_fapp,cont2cont_LAM];

Addsimps cont_lemmas1;

(* HINT: cont_tac is now installed in simplifier in Lift.ML ! *)

(*val cont_tac = (fn i => (resolve_tac cont_lemmas i));*)
(*val cont_tacR = (fn i => (REPEAT (cont_tac i)));*)

(* ------------------------------------------------------------------------ *)
(* function application _[_]  is strict in its first arguments              *)
(* ------------------------------------------------------------------------ *)

qed_goal "strict_fapp1" thy "(UU::'a::cpo->'b)`x = (UU::'b)"
 (fn prems =>
        [
        (stac inst_cfun_pcpo 1),
        (stac beta_cfun 1),
        (Simp_tac 1),
        (rtac refl 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* results about strictify                                                  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "Istrictify1" thy [Istrictify_def]
        "Istrictify(f)(UU)= (UU)"
 (fn prems =>
        [
        (Simp_tac 1)
        ]);

qed_goalw "Istrictify2" thy [Istrictify_def]
        "~x=UU ==> Istrictify(f)(x)=f`x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (Asm_simp_tac 1)
        ]);

qed_goal "monofun_Istrictify1" thy "monofun(Istrictify)"
 (fn prems =>
        [
        (rtac monofunI 1),
        (strip_tac 1),
        (rtac (less_fun RS iffD2) 1),
        (strip_tac 1),
        (res_inst_tac [("Q","xa=UU")] (excluded_middle RS disjE) 1),
        (stac Istrictify2 1),
        (atac 1),
        (stac Istrictify2 1),
        (atac 1),
        (rtac monofun_cfun_fun 1),
        (atac 1),
        (hyp_subst_tac 1),
        (stac Istrictify1 1),
        (stac Istrictify1 1),
        (rtac refl_less 1)
        ]);

qed_goal "monofun_Istrictify2" thy "monofun(Istrictify(f))"
 (fn prems =>
        [
        (rtac monofunI 1),
        (strip_tac 1),
        (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1),
        (stac Istrictify2 1),
        (etac notUU_I 1),
        (atac 1),
        (stac Istrictify2 1),
        (atac 1),
        (rtac monofun_cfun_arg 1),
        (atac 1),
        (hyp_subst_tac 1),
        (stac Istrictify1 1),
        (rtac minimal 1)
        ]);


qed_goal "contlub_Istrictify1" thy "contlub(Istrictify)"
 (fn prems =>
        [
        (rtac contlubI 1),
        (strip_tac 1),
        (rtac (expand_fun_eq RS iffD2) 1),
        (strip_tac 1),
        (stac thelub_fun 1),
        (etac (monofun_Istrictify1 RS ch2ch_monofun) 1),
        (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1),
        (stac Istrictify2 1),
        (atac 1),
        (stac (Istrictify2 RS ext) 1),
        (atac 1),
        (stac thelub_cfun 1),
        (atac 1),
        (stac beta_cfun 1),
        (rtac cont_lubcfun 1),
        (atac 1),
        (rtac refl 1),
        (hyp_subst_tac 1),
        (stac Istrictify1 1),
        (stac (Istrictify1 RS ext) 1),
        (rtac (chain_UU_I_inverse RS sym) 1),
        (rtac (refl RS allI) 1)
        ]);

qed_goal "contlub_Istrictify2" thy "contlub(Istrictify(f::'a -> 'b))"
 (fn prems =>
        [
        (rtac contlubI 1),
        (strip_tac 1),
        (case_tac "lub(range(Y))=(UU::'a)" 1),
        (res_inst_tac [("t","lub(range(Y))")] subst 1),
        (rtac sym 1),
        (atac 1),
        (stac Istrictify1 1),
        (rtac sym 1),
        (rtac chain_UU_I_inverse 1),
        (strip_tac 1),
        (res_inst_tac [("t","Y(i)"),("s","UU::'a")] subst 1),
        (rtac sym 1),
        (rtac (chain_UU_I RS spec) 1),
        (atac 1),
        (atac 1),
        (rtac Istrictify1 1),
        (stac Istrictify2 1),
        (atac 1),
        (res_inst_tac [("s","lub(range(%i. f`(Y i)))")] trans 1),
        (rtac contlub_cfun_arg 1),
        (atac 1),
        (rtac lub_equal2 1),
        (rtac (chain_mono2 RS exE) 1),
        (atac 2),
        (rtac chain_UU_I_inverse2 1),
        (atac 1),
        (rtac exI 1),
        (strip_tac 1),
        (rtac (Istrictify2 RS sym) 1),
        (fast_tac HOL_cs 1),
        (rtac ch2ch_monofun 1),
        (rtac monofun_fapp2 1),
        (atac 1),
        (rtac ch2ch_monofun 1),
        (rtac monofun_Istrictify2 1),
        (atac 1)
        ]);


bind_thm ("cont_Istrictify1", contlub_Istrictify1 RS 
        (monofun_Istrictify1 RS monocontlub2cont)); 

bind_thm ("cont_Istrictify2", contlub_Istrictify2 RS 
        (monofun_Istrictify2 RS monocontlub2cont)); 


qed_goalw "strictify1" thy [strictify_def] "strictify`f`UU=UU" (fn _ => [
        (stac beta_cfun 1),
         (simp_tac (simpset() addsimps [cont_Istrictify2,cont_Istrictify1,
					cont2cont_CF1L]) 1),
        (stac beta_cfun 1),
        (rtac cont_Istrictify2 1),
        (rtac Istrictify1 1)
        ]);

qed_goalw "strictify2" thy [strictify_def]
        "~x=UU ==> strictify`f`x=f`x"  (fn prems => [
        (stac beta_cfun 1),
         (simp_tac (simpset() addsimps [cont_Istrictify2,cont_Istrictify1,
					cont2cont_CF1L]) 1),
        (stac beta_cfun 1),
        (rtac cont_Istrictify2 1),
        (rtac Istrictify2 1),
        (resolve_tac prems 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Instantiate the simplifier                                               *)
(* ------------------------------------------------------------------------ *)

Addsimps [minimal,refl_less,beta_cfun,strict_fapp1,strictify1, strictify2];


(* ------------------------------------------------------------------------ *)
(* use cont_tac as autotac.                                                *)
(* ------------------------------------------------------------------------ *)

(* HINT: cont_tac is now installed in simplifier in Lift.ML ! *)
(*simpset_ref() := simpset() addsolver (K (DEPTH_SOLVE_1 o cont_tac));*)

(* ------------------------------------------------------------------------ *)
(* some lemmata for functions with flat/chain_finite domain/range types	    *)
(* ------------------------------------------------------------------------ *)

qed_goal "chfin_fappR" thy 
    "is_chain (Y::nat => 'a::cpo->'b::chfin)==> !s. ? n. lub(range(Y))`s = Y n`s" 
(fn prems => 
	[
	cut_facts_tac prems 1,
	rtac allI 1,
	stac contlub_cfun_fun 1,
	 atac 1,
	fast_tac (HOL_cs addSIs [thelubI,chfin,lub_finch2,chfin2finch,ch2ch_fappL])1
	]);

(* ------------------------------------------------------------------------ *)
(* continuous isomorphisms are strict                                       *)
(* a prove for embedding projection pairs is similar                        *)
(* ------------------------------------------------------------------------ *)

qed_goal "iso_strict"  thy  
"!!f g.[|!y. f`(g`y)=(y::'b) ; !x. g`(f`x)=(x::'a) |] \
\ ==> f`UU=UU & g`UU=UU"
 (fn prems =>
        [
        (rtac conjI 1),
        (rtac UU_I 1),
        (res_inst_tac [("s","f`(g`(UU::'b))"),("t","UU::'b")] subst 1),
        (etac spec 1),
        (rtac (minimal RS monofun_cfun_arg) 1),
        (rtac UU_I 1),
        (res_inst_tac [("s","g`(f`(UU::'a))"),("t","UU::'a")] subst 1),
        (etac spec 1),
        (rtac (minimal RS monofun_cfun_arg) 1)
        ]);


qed_goal "isorep_defined" thy 
        "[|!x. rep`(abs`x)=x;!y. abs`(rep`y)=y; z~=UU|] ==> rep`z ~= UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac swap 1),
        (dtac notnotD 1),
        (dres_inst_tac [("f","abs")] cfun_arg_cong 1),
        (etac box_equals 1),
        (fast_tac HOL_cs 1),
        (etac (iso_strict RS conjunct1) 1),
        (atac 1)
        ]);

qed_goal "isoabs_defined" thy 
        "[|!x. rep`(abs`x) = x;!y. abs`(rep`y)=y ; z~=UU|] ==> abs`z ~= UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac swap 1),
        (dtac notnotD 1),
        (dres_inst_tac [("f","rep")] cfun_arg_cong 1),
        (etac box_equals 1),
        (fast_tac HOL_cs 1),
        (etac (iso_strict RS conjunct2) 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* propagation of flatness and chainfiniteness by continuous isomorphisms   *)
(* ------------------------------------------------------------------------ *)

qed_goal "chfin2chfin" thy "!!f g.[|! Y::nat=>'a. is_chain Y --> (? n. max_in_chain n Y); \
\ !y. f`(g`y)=(y::'b) ; !x. g`(f`x)=(x::'a::chfin) |] \
\ ==> ! Y::nat=>'b. is_chain Y --> (? n. max_in_chain n Y)"
 (fn prems =>
        [
        (rewtac max_in_chain_def),
        (strip_tac 1),
        (rtac exE 1),
        (res_inst_tac [("P","is_chain(%i. g`(Y i))")] mp 1),
        (etac spec 1),
        (etac ch2ch_fappR 1),
        (rtac exI 1),
        (strip_tac 1),
        (res_inst_tac [("s","f`(g`(Y x))"),("t","Y(x)")] subst 1),
        (etac spec 1),
        (res_inst_tac [("s","f`(g`(Y j))"),("t","Y(j)")] subst 1),
        (etac spec 1),
        (rtac cfun_arg_cong 1),
        (rtac mp 1),
        (etac spec 1),
        (atac 1)
        ]);


qed_goal "flat2flat" thy "!!f g.[|!x y::'a. x<<y --> x=UU | x=y; \
\ !y. f`(g`y)=(y::'b); !x. g`(f`x)=(x::'a)|] ==> !x y::'b. x<<y --> x=UU | x=y"
 (fn prems =>
        [
        (strip_tac 1),
        (rtac disjE 1),
        (res_inst_tac [("P","g`x<<g`y")] mp 1),
        (etac monofun_cfun_arg 2),
        (dtac spec 1),
        (etac spec 1),
        (rtac disjI1 1),
        (rtac trans 1),
        (res_inst_tac [("s","f`(g`x)"),("t","x")] subst 1),
        (etac spec 1),
        (etac cfun_arg_cong 1),
        (rtac (iso_strict RS conjunct1) 1),
        (atac 1),
        (atac 1),
        (rtac disjI2 1),
        (res_inst_tac [("s","f`(g`x)"),("t","x")] subst 1),
        (etac spec 1),
        (res_inst_tac [("s","f`(g`y)"),("t","y")] subst 1),
        (etac spec 1),
        (etac cfun_arg_cong 1)
        ]);

(* ------------------------------------------------------------------------- *)
(* a result about functions with flat codomain                               *)
(* ------------------------------------------------------------------------- *)

qed_goal "flat_codom" thy 
"f`(x::'a)=(c::'b::flat) ==> f`(UU::'a)=(UU::'b) | (!z. f`(z::'a)=c)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (case_tac "f`(x::'a)=(UU::'b)" 1),
        (rtac disjI1 1),
        (rtac UU_I 1),
        (res_inst_tac [("s","f`(x)"),("t","UU::'b")] subst 1),
        (atac 1),
        (rtac (minimal RS monofun_cfun_arg) 1),
        (case_tac "f`(UU::'a)=(UU::'b)" 1),
        (etac disjI1 1),
        (rtac disjI2 1),
        (rtac allI 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("a","f`(UU::'a)")] (refl RS box_equals) 1),
        (res_inst_tac [("fo5","f")] ((minimal RS monofun_cfun_arg) RS 
		(ax_flat RS spec RS spec RS mp) RS disjE) 1),
	(contr_tac 1),(atac 1),
        (res_inst_tac [("fo5","f")] ((minimal RS monofun_cfun_arg) RS 
		(ax_flat RS spec RS spec RS mp) RS disjE) 1),
	(contr_tac 1),(atac 1)
]);


(* ------------------------------------------------------------------------ *)
(* Access to definitions                                                    *)
(* ------------------------------------------------------------------------ *)


qed_goalw "ID1" thy [ID_def] "ID`x=x"
 (fn prems =>
        [
        (stac beta_cfun 1),
        (rtac cont_id 1),
        (rtac refl 1)
        ]);

qed_goalw "cfcomp1" thy [oo_def] "(f oo g)=(LAM x. f`(g`x))" (fn _ => [
        (stac beta_cfun 1),
        (Simp_tac 1),
        (stac beta_cfun 1),
        (Simp_tac 1),
	(rtac refl 1)
        ]);

qed_goal "cfcomp2" thy  "(f oo g)`x=f`(g`x)" (fn _ => [
        (stac cfcomp1 1),
        (stac beta_cfun 1),
        (Simp_tac 1),
	(rtac refl 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Show that interpretation of (pcpo,_->_) is a category                    *)
(* The class of objects is interpretation of syntactical class pcpo         *)
(* The class of arrows  between objects 'a and 'b is interpret. of 'a -> 'b *)
(* The identity arrow is interpretation of ID                               *)
(* The composition of f and g is interpretation of oo                       *)
(* ------------------------------------------------------------------------ *)


qed_goal "ID2" thy "f oo ID = f "
 (fn prems =>
        [
        (rtac ext_cfun 1),
        (stac cfcomp2 1),
        (stac ID1 1),
        (rtac refl 1)
        ]);

qed_goal "ID3" thy "ID oo f = f "
 (fn prems =>
        [
        (rtac ext_cfun 1),
        (stac cfcomp2 1),
        (stac ID1 1),
        (rtac refl 1)
        ]);


qed_goal "assoc_oo" thy "f oo (g oo h) = (f oo g) oo h"
 (fn prems =>
        [
        (rtac ext_cfun 1),
        (res_inst_tac [("s","f`(g`(h`x))")] trans  1),
        (stac cfcomp2 1),
        (stac cfcomp2 1),
        (rtac refl 1),
        (stac cfcomp2 1),
        (stac cfcomp2 1),
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Merge the different rewrite rules for the simplifier                     *)
(* ------------------------------------------------------------------------ *)

Addsimps ([ID1,ID2,ID3,cfcomp2]);


