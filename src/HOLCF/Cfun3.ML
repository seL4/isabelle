(*  Title:      HOLCF/Cfun3
    ID:         $Id$
    Author:     Franz Regensburger

Class instance of  -> for class pcpo
*)

(* for compatibility with old HOLCF-Version *)
Goal "UU = Abs_CFun(%x. UU)";
by (simp_tac (HOL_ss addsimps [UU_def,UU_cfun_def]) 1);
qed "inst_cfun_pcpo";

(* ------------------------------------------------------------------------ *)
(* the contlub property for Rep_CFun its 'first' argument                       *)
(* ------------------------------------------------------------------------ *)

Goal "contlub(Rep_CFun)";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac (expand_fun_eq RS iffD2) 1);
by (strip_tac 1);
by (stac thelub_cfun 1);
by (atac 1);
by (stac Cfunapp2 1);
by (etac cont_lubcfun 1);
by (stac thelub_fun 1);
by (etac (monofun_Rep_CFun1 RS ch2ch_monofun) 1);
by (rtac refl 1);
qed "contlub_Rep_CFun1";


(* ------------------------------------------------------------------------ *)
(* the cont property for Rep_CFun in its first argument                        *)
(* ------------------------------------------------------------------------ *)

Goal "cont(Rep_CFun)";
by (rtac monocontlub2cont 1);
by (rtac monofun_Rep_CFun1 1);
by (rtac contlub_Rep_CFun1 1);
qed "cont_Rep_CFun1";


(* ------------------------------------------------------------------------ *)
(* contlub, cont properties of Rep_CFun in its first argument in mixfix _[_]   *)
(* ------------------------------------------------------------------------ *)

Goal 
"chain(FY) ==>\
\ lub(range FY)$x = lub(range (%i. FY(i)$x))";
by (rtac trans 1);
by (etac (contlub_Rep_CFun1 RS contlubE RS spec RS mp RS fun_cong) 1);
by (stac thelub_fun 1);
by (etac (monofun_Rep_CFun1 RS ch2ch_monofun) 1);
by (rtac refl 1);
qed "contlub_cfun_fun";


Goal 
"chain(FY) ==>\
\ range(%i. FY(i)$x) <<| lub(range FY)$x";
by (rtac thelubE 1);
by (etac ch2ch_Rep_CFunL 1);
by (etac (contlub_cfun_fun RS sym) 1);
qed "cont_cfun_fun";


(* ------------------------------------------------------------------------ *)
(* contlub, cont  properties of Rep_CFun in both argument in mixfix _[_]       *)
(* ------------------------------------------------------------------------ *)

Goal 
"[|chain(FY);chain(TY)|] ==>\
\ (lub(range FY))$(lub(range TY)) = lub(range(%i. FY(i)$(TY i)))";
by (rtac contlub_CF2 1);
by (rtac cont_Rep_CFun1 1);
by (rtac allI 1);
by (rtac cont_Rep_CFun2 1);
by (atac 1);
by (atac 1);
qed "contlub_cfun";

Goal 
"[|chain(FY);chain(TY)|] ==>\
\ range(%i.(FY i)$(TY i)) <<| (lub (range FY))$(lub(range TY))";
by (rtac thelubE 1);
by (rtac (monofun_Rep_CFun1 RS ch2ch_MF2LR) 1);
by (rtac allI 1);
by (rtac monofun_Rep_CFun2 1);
by (atac 1);
by (atac 1);
by (etac (contlub_cfun RS sym) 1);
by (atac 1);
qed "cont_cfun";


(* ------------------------------------------------------------------------ *)
(* cont2cont lemma for Rep_CFun                                               *)
(* ------------------------------------------------------------------------ *)

Goal "[|cont(%x. ft x);cont(%x. tt x)|] ==> cont(%x. (ft x)$(tt x))";
by (best_tac (claset() addIs [cont2cont_app2, cont_const, cont_Rep_CFun1,
	                      cont_Rep_CFun2]) 1);
qed "cont2cont_Rep_CFun";



(* ------------------------------------------------------------------------ *)
(* cont2mono Lemma for %x. LAM y. c1(x)(y)                                  *)
(* ------------------------------------------------------------------------ *)

val [p1,p2] = Goal  
 "[| !!x. cont(c1 x); !!y. monofun(%x. c1 x y)|] ==> monofun(%x. LAM y. c1 x y)";
by (rtac monofunI 1);
by (strip_tac 1);
by (stac less_cfun 1);
by (stac less_fun 1);
by (rtac allI 1);
by (stac beta_cfun 1);
by (rtac p1 1);
by (stac beta_cfun 1);
by (rtac p1 1);
by (etac (p2 RS monofunE RS spec RS spec RS mp) 1);
qed "cont2mono_LAM";

(* ------------------------------------------------------------------------ *)
(* cont2cont Lemma for %x. LAM y. c1 x y)                                 *)
(* ------------------------------------------------------------------------ *)

val [p1,p2] = Goal  
 "[| !!x. cont(c1 x); !!y. cont(%x. c1 x y) |] ==> cont(%x. LAM y. c1 x y)";
by (rtac monocontlub2cont 1);
by (rtac (p1 RS cont2mono_LAM) 1);
by (rtac (p2 RS cont2mono) 1);
by (rtac contlubI 1);
by (strip_tac 1);
by (stac thelub_cfun 1);
by (rtac (p1 RS cont2mono_LAM RS ch2ch_monofun) 1);
by (rtac (p2 RS cont2mono) 1);
by (atac 1);
by (res_inst_tac [("f","Abs_CFun")] arg_cong 1);
by (rtac ext 1);
by (stac (p1 RS beta_cfun RS ext) 1);
by (etac (p2 RS cont2contlub RS contlubE RS spec RS mp) 1);
qed "cont2cont_LAM";

(* ------------------------------------------------------------------------ *)
(* cont2cont tactic                                                       *)
(* ------------------------------------------------------------------------ *)

val cont_lemmas1 = [cont_const, cont_id, cont_Rep_CFun2,
                    cont2cont_Rep_CFun,cont2cont_LAM];

Addsimps cont_lemmas1;

(* HINT: cont_tac is now installed in simplifier in Lift.ML ! *)

(*val cont_tac = (fn i => (resolve_tac cont_lemmas i));*)
(*val cont_tacR = (fn i => (REPEAT (cont_tac i)));*)

(* ------------------------------------------------------------------------ *)
(* function application _[_]  is strict in its first arguments              *)
(* ------------------------------------------------------------------------ *)

Goal "(UU::'a::cpo->'b)$x = (UU::'b)";
by (stac inst_cfun_pcpo 1);
by (stac beta_cfun 1);
by (Simp_tac 1);
by (rtac refl 1);
qed "strict_Rep_CFun1";


(* ------------------------------------------------------------------------ *)
(* results about strictify                                                  *)
(* ------------------------------------------------------------------------ *)

Goalw [Istrictify_def]
        "Istrictify(f)(UU)= (UU)";
by (Simp_tac 1);
qed "Istrictify1";

Goalw [Istrictify_def]
        "~x=UU ==> Istrictify(f)(x)=f$x";
by (Asm_simp_tac 1);
qed "Istrictify2";

Goal "monofun(Istrictify)";
by (rtac monofunI 1);
by (strip_tac 1);
by (rtac (less_fun RS iffD2) 1);
by (strip_tac 1);
by (res_inst_tac [("Q","xa=UU")] (excluded_middle RS disjE) 1);
by (stac Istrictify2 1);
by (atac 1);
by (stac Istrictify2 1);
by (atac 1);
by (rtac monofun_cfun_fun 1);
by (atac 1);
by (hyp_subst_tac 1);
by (stac Istrictify1 1);
by (stac Istrictify1 1);
by (rtac refl_less 1);
qed "monofun_Istrictify1";

Goal "monofun(Istrictify(f))";
by (rtac monofunI 1);
by (strip_tac 1);
by (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1);
by (stac Istrictify2 1);
by (etac notUU_I 1);
by (atac 1);
by (stac Istrictify2 1);
by (atac 1);
by (rtac monofun_cfun_arg 1);
by (atac 1);
by (hyp_subst_tac 1);
by (stac Istrictify1 1);
by (rtac minimal 1);
qed "monofun_Istrictify2";


Goal "contlub(Istrictify)";
by (rtac contlubI 1);
by (strip_tac 1);
by (rtac (expand_fun_eq RS iffD2) 1);
by (strip_tac 1);
by (stac thelub_fun 1);
by (etac (monofun_Istrictify1 RS ch2ch_monofun) 1);
by (res_inst_tac [("Q","x=UU")] (excluded_middle RS disjE) 1);
by (stac Istrictify2 1);
by (atac 1);
by (stac (Istrictify2 RS ext) 1);
by (atac 1);
by (stac thelub_cfun 1);
by (atac 1);
by (stac beta_cfun 1);
by (rtac cont_lubcfun 1);
by (atac 1);
by (rtac refl 1);
by (hyp_subst_tac 1);
by (stac Istrictify1 1);
by (stac (Istrictify1 RS ext) 1);
by (rtac (chain_UU_I_inverse RS sym) 1);
by (rtac (refl RS allI) 1);
qed "contlub_Istrictify1";

Goal "contlub(Istrictify(f::'a -> 'b))";
by (rtac contlubI 1);
by (strip_tac 1);
by (case_tac "lub(range(Y))=(UU::'a)" 1);
by (asm_simp_tac (simpset() addsimps [Istrictify1, chain_UU_I_inverse, chain_UU_I, Istrictify1]) 1);
by (stac Istrictify2 1);
by (atac 1);
by (res_inst_tac [("s","lub(range(%i. f$(Y i)))")] trans 1);
by (rtac contlub_cfun_arg 1);
by (atac 1);
by (rtac lub_equal2 1);
by (best_tac (claset() addIs [ch2ch_monofun, monofun_Istrictify2]) 3);
by (best_tac (claset() addIs [ch2ch_monofun, monofun_Rep_CFun2]) 2);
by (rtac (chain_mono2 RS exE) 1);
by (atac 2);
by (etac chain_UU_I_inverse2 1);
by (blast_tac (claset() addIs [Istrictify2 RS sym]) 1);
qed "contlub_Istrictify2";


bind_thm ("cont_Istrictify1", contlub_Istrictify1 RS 
        (monofun_Istrictify1 RS monocontlub2cont)); 

bind_thm ("cont_Istrictify2", contlub_Istrictify2 RS 
        (monofun_Istrictify2 RS monocontlub2cont)); 


Goalw [strictify_def] "strictify$f$UU=UU";
by (stac beta_cfun 1);
by (simp_tac (simpset() addsimps [cont_Istrictify2,cont_Istrictify1, cont2cont_CF1L]) 1);
by (stac beta_cfun 1);
by (rtac cont_Istrictify2 1);
by (rtac Istrictify1 1);
qed "strictify1";

Goalw [strictify_def] "~x=UU ==> strictify$f$x=f$x";
by (stac beta_cfun 1);
by (simp_tac (simpset() addsimps [cont_Istrictify2,cont_Istrictify1, cont2cont_CF1L]) 1);
by (stac beta_cfun 1);
by (rtac cont_Istrictify2 1);
by (etac Istrictify2 1);
qed "strictify2";


(* ------------------------------------------------------------------------ *)
(* Instantiate the simplifier                                               *)
(* ------------------------------------------------------------------------ *)

Addsimps [minimal,refl_less,beta_cfun,strict_Rep_CFun1,strictify1, strictify2];


(* ------------------------------------------------------------------------ *)
(* use cont_tac as autotac.                                                *)
(* ------------------------------------------------------------------------ *)

(* HINT: cont_tac is now installed in simplifier in Lift.ML ! *)
(*simpset_ref() := simpset() addsolver (K (DEPTH_SOLVE_1 o cont_tac));*)

(* ------------------------------------------------------------------------ *)
(* some lemmata for functions with flat/chfin domain/range types	    *)
(* ------------------------------------------------------------------------ *)

Goal "chain (Y::nat => 'a::cpo->'b::chfin) \
\     ==> !s. ? n. lub(range(Y))$s = Y n$s";
by (rtac allI 1);
by (stac contlub_cfun_fun 1);
by (atac 1);
by (fast_tac (HOL_cs addSIs [thelubI,chfin,lub_finch2,chfin2finch,ch2ch_Rep_CFunL])1);
qed "chfin_Rep_CFunR";

(* ------------------------------------------------------------------------ *)
(* continuous isomorphisms are strict                                       *)
(* a prove for embedding projection pairs is similar                        *)
(* ------------------------------------------------------------------------ *)

Goal  
"!!f g.[|!y. f$(g$y)=(y::'b) ; !x. g$(f$x)=(x::'a) |] \
\ ==> f$UU=UU & g$UU=UU";
by (rtac conjI 1);
by (rtac UU_I 1);
by (res_inst_tac [("s","f$(g$(UU::'b))"),("t","UU::'b")] subst 1);
by (etac spec 1);
by (rtac (minimal RS monofun_cfun_arg) 1);
by (rtac UU_I 1);
by (res_inst_tac [("s","g$(f$(UU::'a))"),("t","UU::'a")] subst 1);
by (etac spec 1);
by (rtac (minimal RS monofun_cfun_arg) 1);
qed "iso_strict";


Goal "[|!x. rep$(ab$x)=x;!y. ab$(rep$y)=y; z~=UU|] ==> rep$z ~= UU";
by (etac contrapos_nn 1);
by (dres_inst_tac [("f","ab")] cfun_arg_cong 1);
by (etac box_equals 1);
by (fast_tac HOL_cs 1);
by (etac (iso_strict RS conjunct1) 1);
by (atac 1);
qed "isorep_defined";

Goal "[|!x. rep$(ab$x) = x;!y. ab$(rep$y)=y ; z~=UU|] ==> ab$z ~= UU";
by (etac contrapos_nn 1);
by (dres_inst_tac [("f","rep")] cfun_arg_cong 1);
by (etac box_equals 1);
by (fast_tac HOL_cs 1);
by (etac (iso_strict RS conjunct2) 1);
by (atac 1);
qed "isoabs_defined";

(* ------------------------------------------------------------------------ *)
(* propagation of flatness and chainfiniteness by continuous isomorphisms   *)
(* ------------------------------------------------------------------------ *)

Goal "!!f g.[|! Y::nat=>'a. chain Y --> (? n. max_in_chain n Y); \
\ !y. f$(g$y)=(y::'b) ; !x. g$(f$x)=(x::'a::chfin) |] \
\ ==> ! Y::nat=>'b. chain Y --> (? n. max_in_chain n Y)";
by (rewtac max_in_chain_def);
by (strip_tac 1);
by (rtac exE 1);
by (res_inst_tac [("P","chain(%i. g$(Y i))")] mp 1);
by (etac spec 1);
by (etac ch2ch_Rep_CFunR 1);
by (rtac exI 1);
by (strip_tac 1);
by (res_inst_tac [("s","f$(g$(Y x))"),("t","Y(x)")] subst 1);
by (etac spec 1);
by (res_inst_tac [("s","f$(g$(Y j))"),("t","Y(j)")] subst 1);
by (etac spec 1);
by (rtac cfun_arg_cong 1);
by (rtac mp 1);
by (etac spec 1);
by (atac 1);
qed "chfin2chfin";


Goal "!!f g.[|!x y::'a. x<<y --> x=UU | x=y; \
\ !y. f$(g$y)=(y::'b); !x. g$(f$x)=(x::'a)|] ==> !x y::'b. x<<y --> x=UU | x=y";
by (strip_tac 1);
by (rtac disjE 1);
by (res_inst_tac [("P","g$x<<g$y")] mp 1);
by (etac monofun_cfun_arg 2);
by (dtac spec 1);
by (etac spec 1);
by (rtac disjI1 1);
by (rtac trans 1);
by (res_inst_tac [("s","f$(g$x)"),("t","x")] subst 1);
by (etac spec 1);
by (etac cfun_arg_cong 1);
by (rtac (iso_strict RS conjunct1) 1);
by (atac 1);
by (atac 1);
by (rtac disjI2 1);
by (res_inst_tac [("s","f$(g$x)"),("t","x")] subst 1);
by (etac spec 1);
by (res_inst_tac [("s","f$(g$y)"),("t","y")] subst 1);
by (etac spec 1);
by (etac cfun_arg_cong 1);
qed "flat2flat";

(* ------------------------------------------------------------------------- *)
(* a result about functions with flat codomain                               *)
(* ------------------------------------------------------------------------- *)

Goal "f$(x::'a)=(c::'b::flat) ==> f$(UU::'a)=(UU::'b) | (!z. f$(z::'a)=c)";
by (case_tac "f$(x::'a)=(UU::'b)" 1);
by (rtac disjI1 1);
by (rtac UU_I 1);
by (res_inst_tac [("s","f$(x)"),("t","UU::'b")] subst 1);
by (atac 1);
by (rtac (minimal RS monofun_cfun_arg) 1);
by (case_tac "f$(UU::'a)=(UU::'b)" 1);
by (etac disjI1 1);
by (rtac disjI2 1);
by (rtac allI 1);
by (hyp_subst_tac 1);
by (res_inst_tac [("a","f$(UU::'a)")] (refl RS box_equals) 1);
by (res_inst_tac [("fo5","f")] ((minimal RS monofun_cfun_arg) RS (ax_flat RS spec RS spec RS mp) RS disjE) 1);
by (contr_tac 1);
by (atac 1);
by (res_inst_tac [("fo5","f")] ((minimal RS monofun_cfun_arg) RS (ax_flat RS spec RS spec RS mp) RS disjE) 1);
by (contr_tac 1);
by (atac 1);
qed "flat_codom";


(* ------------------------------------------------------------------------ *)
(* Access to definitions                                                    *)
(* ------------------------------------------------------------------------ *)


Goalw [ID_def] "ID$x=x";
by (stac beta_cfun 1);
by (rtac cont_id 1);
by (rtac refl 1);
qed "ID1";

Goalw [oo_def] "(f oo g)=(LAM x. f$(g$x))";
by (stac beta_cfun 1);
by (Simp_tac 1);
by (stac beta_cfun 1);
by (Simp_tac 1);
by (rtac refl 1);
qed "cfcomp1";

Goal  "(f oo g)$x=f$(g$x)";
by (stac cfcomp1 1);
by (stac beta_cfun 1);
by (Simp_tac 1);
by (rtac refl 1);
qed "cfcomp2";


(* ------------------------------------------------------------------------ *)
(* Show that interpretation of (pcpo,_->_) is a category                    *)
(* The class of objects is interpretation of syntactical class pcpo         *)
(* The class of arrows  between objects 'a and 'b is interpret. of 'a -> 'b *)
(* The identity arrow is interpretation of ID                               *)
(* The composition of f and g is interpretation of oo                       *)
(* ------------------------------------------------------------------------ *)


Goal "f oo ID = f ";
by (rtac ext_cfun 1);
by (stac cfcomp2 1);
by (stac ID1 1);
by (rtac refl 1);
qed "ID2";

Goal "ID oo f = f ";
by (rtac ext_cfun 1);
by (stac cfcomp2 1);
by (stac ID1 1);
by (rtac refl 1);
qed "ID3";


Goal "f oo (g oo h) = (f oo g) oo h";
by (rtac ext_cfun 1);
by (res_inst_tac [("s","f$(g$(h$x))")] trans  1);
by (stac cfcomp2 1);
by (stac cfcomp2 1);
by (rtac refl 1);
by (stac cfcomp2 1);
by (stac cfcomp2 1);
by (rtac refl 1);
qed "assoc_oo";

(* ------------------------------------------------------------------------ *)
(* Merge the different rewrite rules for the simplifier                     *)
(* ------------------------------------------------------------------------ *)

Addsimps ([ID1,ID2,ID3,cfcomp2]);


