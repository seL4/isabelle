(*  Title:      HOLCF/Ssum2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance ++::(pcpo,pcpo)po
*)

(* for compatibility with old HOLCF-Version *)
Goal "(op <<)=(%s1 s2.@z.\
\         (! u x. s1=Isinl u & s2=Isinl x --> z = u << x)\
\        &(! v y. s1=Isinr v & s2=Isinr y --> z = v << y)\
\        &(! u y. s1=Isinl u & s2=Isinr y --> z = (u = UU))\
\        &(! v x. s1=Isinr v & s2=Isinl x --> z = (v = UU)))";
by (fold_goals_tac [less_ssum_def]);
by (rtac refl 1);
qed "inst_ssum_po";

(* ------------------------------------------------------------------------ *)
(* access to less_ssum in class po                                          *)
(* ------------------------------------------------------------------------ *)

Goal "Isinl x << Isinl y = x << y";
by (simp_tac (simpset() addsimps [less_ssum2a]) 1);
qed "less_ssum3a";

Goal "Isinr x << Isinr y = x << y";
by (simp_tac (simpset() addsimps [less_ssum2b]) 1);
qed "less_ssum3b";

Goal "Isinl x << Isinr y = (x = UU)";
by (simp_tac (simpset() addsimps [less_ssum2c]) 1);
qed "less_ssum3c";

Goal "Isinr x << Isinl y = (x = UU)";
by (simp_tac (simpset() addsimps [less_ssum2d]) 1);
qed "less_ssum3d";

(* ------------------------------------------------------------------------ *)
(* type ssum ++ is pointed                                                  *)
(* ------------------------------------------------------------------------ *)

Goal "Isinl UU << s";
by (res_inst_tac [("p","s")] IssumE2 1);
by (hyp_subst_tac 1);
by (rtac (less_ssum3a RS iffD2) 1);
by (rtac minimal 1);
by (hyp_subst_tac 1);
by (stac strict_IsinlIsinr 1);
by (rtac (less_ssum3b RS iffD2) 1);
by (rtac minimal 1);
qed "minimal_ssum";

bind_thm ("UU_ssum_def",minimal_ssum RS minimal2UU RS sym);

Goal "? x::'a++'b.!y. x<<y";
by (res_inst_tac [("x","Isinl UU")] exI 1);
by (rtac (minimal_ssum RS allI) 1);
qed "least_ssum";

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

Goal "[|~(!i.? x. Y(i::nat)=Isinl(x))|] ==> (? i.! x. Y(i)~=Isinl(x))";
by (fast_tac HOL_cs 1);
qed "ssum_lemma1";

Goal "[|(? i.!x.(Y::nat => 'a++'b)(i::nat)~=Isinl(x::'a))|]  \
\     ==> (? i y. (Y::nat => 'a++'b)(i::nat)=Isinr(y::'b) & y~=UU)";
by (etac exE 1);
by (res_inst_tac [("p","Y(i)")] IssumE 1);
by (dtac spec 1);
by (contr_tac 1);
by (dtac spec 1);
by (contr_tac 1);
by (fast_tac HOL_cs 1);
qed "ssum_lemma2";


Goal "[|chain(Y);(? i x. Y(i)=Isinr(x::'b) & (x::'b)~=UU)|] \
\     ==> (!i.? y. Y(i)=Isinr(y))";
by (etac exE 1);
by (etac exE 1);
by (rtac allI 1);
by (res_inst_tac [("p","Y(ia)")] IssumE 1);
by (rtac exI 1);
by (rtac trans 1);
by (rtac strict_IsinlIsinr 2);
by (atac 1);
by (etac exI 2);
by (etac conjE 1);
by (res_inst_tac [("m","i"),("n","ia")] nat_less_cases 1);
by (hyp_subst_tac 2);
by (etac exI 2);
by (eres_inst_tac [("P","x=UU")] notE 1);
by (rtac (less_ssum3d RS iffD1) 1);
by (eres_inst_tac [("s","Y(i)"),("t","Isinr(x)::'a++'b")] subst 1);
by (eres_inst_tac [("s","Y(ia)"),("t","Isinl(xa)::'a++'b")] subst 1);
by (etac (chain_mono RS mp) 1);
by (atac 1);
by (eres_inst_tac [("P","xa=UU")] notE 1);
by (rtac (less_ssum3c RS iffD1) 1);
by (eres_inst_tac [("s","Y(i)"),("t","Isinr(x)::'a++'b")] subst 1);
by (eres_inst_tac [("s","Y(ia)"),("t","Isinl(xa)::'a++'b")] subst 1);
by (etac (chain_mono RS mp) 1);
by (atac 1);
qed "ssum_lemma3";

Goal "chain(Y) ==> (!i.? x. Y(i)=Isinl(x))|(!i.? y. Y(i)=Isinr(y))";
by (rtac case_split_thm 1);
by (etac disjI1 1);
by (rtac disjI2 1);
by (etac ssum_lemma3 1);
by (rtac ssum_lemma2 1);
by (etac ssum_lemma1 1);
qed "ssum_lemma4";


(* ------------------------------------------------------------------------ *)
(* restricted surjectivity of Isinl                                         *)
(* ------------------------------------------------------------------------ *)

Goal "z=Isinl(x)==> Isinl((Iwhen (LAM x. x) (LAM y. UU))(z)) = z";
by (hyp_subst_tac 1);
by (case_tac "x=UU" 1);
by (asm_simp_tac Ssum0_ss 1);
by (asm_simp_tac Ssum0_ss 1);
qed "ssum_lemma5";

(* ------------------------------------------------------------------------ *)
(* restricted surjectivity of Isinr                                         *)
(* ------------------------------------------------------------------------ *)

Goal "z=Isinr(x)==> Isinr((Iwhen (LAM y. UU) (LAM x. x))(z)) = z";
by (hyp_subst_tac 1);
by (case_tac "x=UU" 1);
by (asm_simp_tac Ssum0_ss 1);
by (asm_simp_tac Ssum0_ss 1);
qed "ssum_lemma6";

(* ------------------------------------------------------------------------ *)
(* technical lemmas                                                         *)
(* ------------------------------------------------------------------------ *)

Goal "[|Isinl(x) << z; x~=UU|] ==> ? y. z=Isinl(y) & y~=UU";
by (res_inst_tac [("p","z")] IssumE 1);
by (hyp_subst_tac 1);
by (etac notE 1);
by (rtac antisym_less 1);
by (etac (less_ssum3a RS iffD1) 1);
by (rtac minimal 1);
by (fast_tac HOL_cs 1);
by (hyp_subst_tac 1);
by (rtac notE 1);
by (etac (less_ssum3c RS iffD1) 2);
by (atac 1);
qed "ssum_lemma7";

Goal "[|Isinr(x) << z; x~=UU|] ==> ? y. z=Isinr(y) & y~=UU";
by (res_inst_tac [("p","z")] IssumE 1);
by (hyp_subst_tac 1);
by (etac notE 1);
by (etac (less_ssum3d RS iffD1) 1);
by (hyp_subst_tac 1);
by (rtac notE 1);
by (etac (less_ssum3d RS iffD1) 2);
by (atac 1);
by (fast_tac HOL_cs 1);
qed "ssum_lemma8";

(* ------------------------------------------------------------------------ *)
(* the type 'a ++ 'b is a cpo in three steps                                *)
(* ------------------------------------------------------------------------ *)

Goal "[|chain(Y);(!i.? x. Y(i)=Isinl(x))|] ==>\
\     range(Y) <<| Isinl(lub(range(%i.(Iwhen (LAM x. x) (LAM y. UU))(Y i))))";
by (rtac is_lubI 1);
by (rtac conjI 1);
by (rtac ub_rangeI 1);
by (rtac allI 1);
by (etac allE 1);
by (etac exE 1);
by (res_inst_tac [("t","Y(i)")] (ssum_lemma5 RS subst) 1);
by (atac 1);
by (rtac (monofun_Isinl RS monofunE RS spec RS spec RS mp) 1);
by (rtac is_ub_thelub 1);
by (etac (monofun_Iwhen3 RS ch2ch_monofun) 1);
by (strip_tac 1);
by (res_inst_tac [("p","u")] IssumE2 1);
by (res_inst_tac [("t","u")] (ssum_lemma5 RS subst) 1);
by (atac 1);
by (rtac (monofun_Isinl RS monofunE RS spec RS spec RS mp) 1);
by (rtac is_lub_thelub 1);
by (etac (monofun_Iwhen3 RS ch2ch_monofun) 1);
by (etac (monofun_Iwhen3 RS ub2ub_monofun) 1);
by (hyp_subst_tac 1);
by (rtac (less_ssum3c RS iffD2) 1);
by (rtac chain_UU_I_inverse 1);
by (rtac allI 1);
by (res_inst_tac [("p","Y(i)")] IssumE 1);
by (asm_simp_tac Ssum0_ss 1);
by (asm_simp_tac Ssum0_ss 2);
by (etac notE 1);
by (rtac (less_ssum3c RS iffD1) 1);
by (res_inst_tac [("t","Isinl(x)")] subst 1);
by (atac 1);
by (etac (ub_rangeE RS spec) 1);
qed "lub_ssum1a";


Goal "[|chain(Y);(!i.? x. Y(i)=Isinr(x))|] ==>\
\     range(Y) <<| Isinr(lub(range(%i.(Iwhen (LAM y. UU) (LAM x. x))(Y i))))";
by (rtac is_lubI 1);
by (rtac conjI 1);
by (rtac ub_rangeI 1);
by (rtac allI 1);
by (etac allE 1);
by (etac exE 1);
by (res_inst_tac [("t","Y(i)")] (ssum_lemma6 RS subst) 1);
by (atac 1);
by (rtac (monofun_Isinr RS monofunE RS spec RS spec RS mp) 1);
by (rtac is_ub_thelub 1);
by (etac (monofun_Iwhen3 RS ch2ch_monofun) 1);
by (strip_tac 1);
by (res_inst_tac [("p","u")] IssumE2 1);
by (hyp_subst_tac 1);
by (rtac (less_ssum3d RS iffD2) 1);
by (rtac chain_UU_I_inverse 1);
by (rtac allI 1);
by (res_inst_tac [("p","Y(i)")] IssumE 1);
by (asm_simp_tac Ssum0_ss 1);
by (asm_simp_tac Ssum0_ss 1);
by (etac notE 1);
by (rtac (less_ssum3d RS iffD1) 1);
by (res_inst_tac [("t","Isinr(y)")] subst 1);
by (atac 1);
by (etac (ub_rangeE RS spec) 1);
by (res_inst_tac [("t","u")] (ssum_lemma6 RS subst) 1);
by (atac 1);
by (rtac (monofun_Isinr RS monofunE RS spec RS spec RS mp) 1);
by (rtac is_lub_thelub 1);
by (etac (monofun_Iwhen3 RS ch2ch_monofun) 1);
by (etac (monofun_Iwhen3 RS ub2ub_monofun) 1);
qed "lub_ssum1b";


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

Goal "chain(Y::nat=>'a ++'b) ==> ? x. range(Y) <<|x";
by (rtac (ssum_lemma4 RS disjE) 1);
by (atac 1);
by (rtac exI 1);
by (etac lub_ssum1a 1);
by (atac 1);
by (rtac exI 1);
by (etac lub_ssum1b 1);
by (atac 1);
qed "cpo_ssum";

