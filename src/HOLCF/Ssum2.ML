(*  Title:      HOLCF/Ssum2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for Ssum2.thy
*)

open Ssum2;

(* for compatibility with old HOLCF-Version *)
qed_goal "inst_ssum_po" thy "(op <<)=(%s1 s2.@z.\
\         (! u x. s1=Isinl u & s2=Isinl x --> z = u << x)\
\        &(! v y. s1=Isinr v & s2=Isinr y --> z = v << y)\
\        &(! u y. s1=Isinl u & s2=Isinr y --> z = (u = UU))\
\        &(! v x. s1=Isinr v & s2=Isinl x --> z = (v = UU)))"
 (fn prems => 
        [
        (fold_goals_tac [less_ssum_def]),
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* access to less_ssum in class po                                          *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_ssum3a" thy "Isinl x << Isinl y = x << y"
 (fn prems =>
        [
        (simp_tac (simpset() addsimps [less_ssum2a]) 1)
        ]);

qed_goal "less_ssum3b" thy "Isinr x << Isinr y = x << y"
 (fn prems =>
        [
        (simp_tac (simpset() addsimps [less_ssum2b]) 1)
        ]);

qed_goal "less_ssum3c" thy "Isinl x << Isinr y = (x = UU)"
 (fn prems =>
        [
        (simp_tac (simpset() addsimps [less_ssum2c]) 1)
        ]);

qed_goal "less_ssum3d" thy "Isinr x << Isinl y = (x = UU)"
 (fn prems =>
        [
        (simp_tac (simpset() addsimps [less_ssum2d]) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* type ssum ++ is pointed                                                  *)
(* ------------------------------------------------------------------------ *)

qed_goal "minimal_ssum" thy "Isinl UU << s"
 (fn prems =>
        [
        (res_inst_tac [("p","s")] IssumE2 1),
        (hyp_subst_tac 1),
        (rtac (less_ssum3a RS iffD2) 1),
        (rtac minimal 1),
        (hyp_subst_tac 1),
        (stac strict_IsinlIsinr 1),
        (rtac (less_ssum3b RS iffD2) 1),
        (rtac minimal 1)
        ]);

bind_thm ("UU_ssum_def",minimal_ssum RS minimal2UU RS sym);

qed_goal "least_ssum" thy "? x::'a++'b.!y. x<<y"
(fn prems =>
        [
        (res_inst_tac [("x","Isinl UU")] exI 1),
        (rtac (minimal_ssum RS allI) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Isinl, Isinr are monotone                                                *)
(* ------------------------------------------------------------------------ *)

qed_goalw "monofun_Isinl" thy [monofun] "monofun(Isinl)"
 (fn prems =>
        [
        (strip_tac 1),
        (etac (less_ssum3a RS iffD2) 1)
        ]);

qed_goalw "monofun_Isinr" thy [monofun] "monofun(Isinr)"
 (fn prems =>
        [
        (strip_tac 1),
        (etac (less_ssum3b RS iffD2) 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* Iwhen is monotone in all arguments                                       *)
(* ------------------------------------------------------------------------ *)


qed_goalw "monofun_Iwhen1" thy [monofun] "monofun(Iwhen)"
 (fn prems =>
        [
        (strip_tac 1),
        (rtac (less_fun RS iffD2) 1),
        (strip_tac 1),
        (rtac (less_fun RS iffD2) 1),
        (strip_tac 1),
        (res_inst_tac [("p","xb")] IssumE 1),
        (hyp_subst_tac 1),
        (asm_simp_tac Ssum0_ss 1),
        (asm_simp_tac Ssum0_ss 1),
        (etac monofun_cfun_fun 1),
        (asm_simp_tac Ssum0_ss 1)
        ]);

qed_goalw "monofun_Iwhen2" thy [monofun] "monofun(Iwhen(f))"
 (fn prems =>
        [
        (strip_tac 1),
        (rtac (less_fun RS iffD2) 1),
        (strip_tac 1),
        (res_inst_tac [("p","xa")] IssumE 1),
        (hyp_subst_tac 1),
        (asm_simp_tac Ssum0_ss 1),
        (asm_simp_tac Ssum0_ss 1),
        (asm_simp_tac Ssum0_ss 1),
        (etac monofun_cfun_fun 1)
        ]);

qed_goalw "monofun_Iwhen3" thy [monofun] "monofun(Iwhen(f)(g))"
 (fn prems =>
        [
        (strip_tac 1),
        (res_inst_tac [("p","x")] IssumE 1),
        (hyp_subst_tac 1),
        (asm_simp_tac Ssum0_ss 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","y")] IssumE 1),
        (hyp_subst_tac 1),
        (asm_simp_tac Ssum0_ss 1),
        (res_inst_tac  [("P","xa=UU")] notE 1),
        (atac 1),
        (rtac UU_I 1),
        (rtac (less_ssum3a  RS iffD1) 1),
        (atac 1),
        (hyp_subst_tac 1),
        (asm_simp_tac Ssum0_ss 1),
        (rtac monofun_cfun_arg 1),
        (etac (less_ssum3a  RS iffD1) 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("s","UU"),("t","xa")] subst 1),
        (etac (less_ssum3c  RS iffD1 RS sym) 1),
        (asm_simp_tac Ssum0_ss 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("p","y")] IssumE 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("s","UU"),("t","ya")] subst 1),
        (etac (less_ssum3d  RS iffD1 RS sym) 1),
        (asm_simp_tac Ssum0_ss 1),
        (hyp_subst_tac 1),
        (res_inst_tac [("s","UU"),("t","ya")] subst 1),
        (etac (less_ssum3d  RS iffD1 RS sym) 1),
        (asm_simp_tac Ssum0_ss 1),
        (hyp_subst_tac 1),
        (asm_simp_tac Ssum0_ss 1),
        (rtac monofun_cfun_arg 1),
        (etac (less_ssum3b  RS iffD1) 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* some kind of exhaustion rules for chains in 'a ++ 'b                     *)
(* ------------------------------------------------------------------------ *)

qed_goal "ssum_lemma1" thy 
"[|~(!i.? x. Y(i::nat)=Isinl(x))|] ==> (? i.! x. Y(i)~=Isinl(x))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (fast_tac HOL_cs 1)
        ]);

qed_goal "ssum_lemma2" thy 
"[|(? i.!x.(Y::nat => 'a++'b)(i::nat)~=Isinl(x::'a))|] ==>\
\   (? i y. (Y::nat => 'a++'b)(i::nat)=Isinr(y::'b) & y~=UU)"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac exE 1),
        (res_inst_tac [("p","Y(i)")] IssumE 1),
        (dtac spec 1),
        (contr_tac 1),
        (dtac spec 1),
        (contr_tac 1),
        (fast_tac HOL_cs 1)
        ]);


qed_goal "ssum_lemma3" thy 
"[|chain(Y);(? i x. Y(i)=Isinr(x::'b) & (x::'b)~=UU)|] ==>\
\ (!i.? y. Y(i)=Isinr(y))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (etac exE 1),
        (etac exE 1),
        (rtac allI 1),
        (res_inst_tac [("p","Y(ia)")] IssumE 1),
        (rtac exI 1),
        (rtac trans 1),
        (rtac strict_IsinlIsinr 2),
        (atac 1),
        (etac exI 2),
        (etac conjE 1),
        (res_inst_tac [("m","i"),("n","ia")] nat_less_cases 1),
        (hyp_subst_tac 2),
        (etac exI 2),
        (eres_inst_tac [("P","x=UU")] notE 1),
        (rtac (less_ssum3d RS iffD1) 1),
        (eres_inst_tac [("s","Y(i)"),("t","Isinr(x)::'a++'b")] subst 1),
        (eres_inst_tac [("s","Y(ia)"),("t","Isinl(xa)::'a++'b")] subst 1),
        (etac (chain_mono RS mp) 1),
        (atac 1),
        (eres_inst_tac [("P","xa=UU")] notE 1),
        (rtac (less_ssum3c RS iffD1) 1),
        (eres_inst_tac [("s","Y(i)"),("t","Isinr(x)::'a++'b")] subst 1),
        (eres_inst_tac [("s","Y(ia)"),("t","Isinl(xa)::'a++'b")] subst 1),
        (etac (chain_mono RS mp) 1),
        (atac 1)
        ]);

qed_goal "ssum_lemma4" thy 
"chain(Y) ==> (!i.? x. Y(i)=Isinl(x))|(!i.? y. Y(i)=Isinr(y))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac case_split_thm 1),
        (etac disjI1 1),
        (rtac disjI2 1),
        (etac ssum_lemma3 1),
        (rtac ssum_lemma2 1),
        (etac ssum_lemma1 1)
        ]);


(* ------------------------------------------------------------------------ *)
(* restricted surjectivity of Isinl                                         *)
(* ------------------------------------------------------------------------ *)

qed_goal "ssum_lemma5" thy 
"z=Isinl(x)==> Isinl((Iwhen (LAM x. x) (LAM y. UU))(z)) = z"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (hyp_subst_tac 1),
        (case_tac "x=UU" 1),
        (asm_simp_tac Ssum0_ss 1),
        (asm_simp_tac Ssum0_ss 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* restricted surjectivity of Isinr                                         *)
(* ------------------------------------------------------------------------ *)

qed_goal "ssum_lemma6" thy 
"z=Isinr(x)==> Isinr((Iwhen (LAM y. UU) (LAM x. x))(z)) = z"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (hyp_subst_tac 1),
        (case_tac "x=UU" 1),
        (asm_simp_tac Ssum0_ss 1),
        (asm_simp_tac Ssum0_ss 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* technical lemmas                                                         *)
(* ------------------------------------------------------------------------ *)

qed_goal "ssum_lemma7" thy 
"[|Isinl(x) << z; x~=UU|] ==> ? y. z=Isinl(y) & y~=UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("p","z")] IssumE 1),
        (hyp_subst_tac 1),
        (etac notE 1),
        (rtac antisym_less 1),
        (etac (less_ssum3a RS iffD1) 1),
        (rtac minimal 1),
        (fast_tac HOL_cs 1),
        (hyp_subst_tac 1),
        (rtac notE 1),
        (etac (less_ssum3c RS iffD1) 2),
        (atac 1)
        ]);

qed_goal "ssum_lemma8" thy 
"[|Isinr(x) << z; x~=UU|] ==> ? y. z=Isinr(y) & y~=UU"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (res_inst_tac [("p","z")] IssumE 1),
        (hyp_subst_tac 1),
        (etac notE 1),
        (etac (less_ssum3d RS iffD1) 1),
        (hyp_subst_tac 1),
        (rtac notE 1),
        (etac (less_ssum3d RS iffD1) 2),
        (atac 1),
        (fast_tac HOL_cs 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* the type 'a ++ 'b is a cpo in three steps                                *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_ssum1a" thy 
"[|chain(Y);(!i.? x. Y(i)=Isinl(x))|] ==>\
\ range(Y) <<|\
\ Isinl(lub(range(%i.(Iwhen (LAM x. x) (LAM y. UU))(Y i))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),
        (rtac allI 1),
        (etac allE 1),
        (etac exE 1),
        (res_inst_tac [("t","Y(i)")] (ssum_lemma5 RS subst) 1),
        (atac 1),
        (rtac (monofun_Isinl RS monofunE RS spec RS spec RS mp) 1),
        (rtac is_ub_thelub 1),
        (etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
        (strip_tac 1),
        (res_inst_tac [("p","u")] IssumE2 1),
        (res_inst_tac [("t","u")] (ssum_lemma5 RS subst) 1),
        (atac 1),
        (rtac (monofun_Isinl RS monofunE RS spec RS spec RS mp) 1),
        (rtac is_lub_thelub 1),
        (etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
        (etac (monofun_Iwhen3 RS ub2ub_monofun) 1),
        (hyp_subst_tac 1),
        (rtac (less_ssum3c RS iffD2) 1),
        (rtac chain_UU_I_inverse 1),
        (rtac allI 1),
        (res_inst_tac [("p","Y(i)")] IssumE 1),
        (asm_simp_tac Ssum0_ss 1),
        (asm_simp_tac Ssum0_ss 2),
        (etac notE 1),
        (rtac (less_ssum3c RS iffD1) 1),
        (res_inst_tac [("t","Isinl(x)")] subst 1),
        (atac 1),
        (etac (ub_rangeE RS spec) 1)
        ]);


qed_goal "lub_ssum1b" thy 
"[|chain(Y);(!i.? x. Y(i)=Isinr(x))|] ==>\
\ range(Y) <<|\
\ Isinr(lub(range(%i.(Iwhen (LAM y. UU) (LAM x. x))(Y i))))"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),
        (rtac allI 1),
        (etac allE 1),
        (etac exE 1),
        (res_inst_tac [("t","Y(i)")] (ssum_lemma6 RS subst) 1),
        (atac 1),
        (rtac (monofun_Isinr RS monofunE RS spec RS spec RS mp) 1),
        (rtac is_ub_thelub 1),
        (etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
        (strip_tac 1),
        (res_inst_tac [("p","u")] IssumE2 1),
        (hyp_subst_tac 1),
        (rtac (less_ssum3d RS iffD2) 1),
        (rtac chain_UU_I_inverse 1),
        (rtac allI 1),
        (res_inst_tac [("p","Y(i)")] IssumE 1),
        (asm_simp_tac Ssum0_ss 1),
        (asm_simp_tac Ssum0_ss 1),
        (etac notE 1),
        (rtac (less_ssum3d RS iffD1) 1),
        (res_inst_tac [("t","Isinr(y)")] subst 1),
        (atac 1),
        (etac (ub_rangeE RS spec) 1),
        (res_inst_tac [("t","u")] (ssum_lemma6 RS subst) 1),
        (atac 1),
        (rtac (monofun_Isinr RS monofunE RS spec RS spec RS mp) 1),
        (rtac is_lub_thelub 1),
        (etac (monofun_Iwhen3 RS ch2ch_monofun) 1),
        (etac (monofun_Iwhen3 RS ub2ub_monofun) 1)
        ]);


bind_thm ("thelub_ssum1a", lub_ssum1a RS thelubI);
(*
[| chain ?Y1; ! i. ? x. ?Y1 i = Isinl x |] ==>
 lub (range ?Y1) = Isinl
 (lub (range (%i. Iwhen (LAM x. x) (LAM y. UU) (?Y1 i))))
*)

bind_thm ("thelub_ssum1b", lub_ssum1b RS thelubI);
(*
[| chain ?Y1; ! i. ? x. ?Y1 i = Isinr x |] ==>
 lub (range ?Y1) = Isinr
 (lub (range (%i. Iwhen (LAM y. UU) (LAM x. x) (?Y1 i))))
*)

qed_goal "cpo_ssum" thy 
        "chain(Y::nat=>'a ++'b) ==> ? x. range(Y) <<|x"
 (fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac (ssum_lemma4 RS disjE) 1),
        (atac 1),
        (rtac exI 1),
        (etac lub_ssum1a 1),
        (atac 1),
        (rtac exI 1),
        (etac lub_ssum1b 1),
        (atac 1)
        ]);

