(*  Title:      HOLCF/Up2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Class Instance u::(pcpo)po
*)

(* for compatibility with old HOLCF-Version *)
Goal "(op <<)=(%x1 x2. case Rep_Up(x1) of \               
\               Inl(y1) => True \
\             | Inr(y2) => (case Rep_Up(x2) of Inl(z1) => False \
\                                            | Inr(z2) => y2<<z2))";
by (fold_goals_tac [less_up_def]);
by (rtac refl 1);
qed "inst_up_po";

(* -------------------------------------------------------------------------*)
(* type ('a)u is pointed                                                    *)
(* ------------------------------------------------------------------------ *)

Goal "Abs_Up(Inl ()) << z";
by (simp_tac (simpset() addsimps [less_up1a]) 1);
qed "minimal_up";

bind_thm ("UU_up_def",minimal_up RS minimal2UU RS sym);

Goal "EX x::'a u. ALL y. x<<y";
by (res_inst_tac [("x","Abs_Up(Inl ())")] exI 1);
by (rtac (minimal_up RS allI) 1);
qed "least_up";

(* -------------------------------------------------------------------------*)
(* access to less_up in class po                                          *)
(* ------------------------------------------------------------------------ *)

Goal "~ Iup(x) << Abs_Up(Inl ())";
by (simp_tac (simpset() addsimps [less_up1b]) 1);
qed "less_up2b";

Goal "(Iup(x)<<Iup(y)) = (x<<y)";
by (simp_tac (simpset() addsimps [less_up1c]) 1);
qed "less_up2c";

(* ------------------------------------------------------------------------ *)
(* Iup and Ifup are monotone                                               *)
(* ------------------------------------------------------------------------ *)

Goalw [monofun]  "monofun(Iup)";
by (strip_tac 1);
by (etac (less_up2c RS iffD2) 1);
qed "monofun_Iup";

Goalw [monofun]  "monofun(Ifup)";
by (strip_tac 1);
by (rtac (less_fun RS iffD2) 1);
by (strip_tac 1);
by (res_inst_tac [("p","xa")] upE 1);
by (asm_simp_tac Up0_ss 1);
by (asm_simp_tac Up0_ss 1);
by (etac monofun_cfun_fun 1);
qed "monofun_Ifup1";

Goalw [monofun]  "monofun(Ifup(f))";
by (strip_tac 1);
by (res_inst_tac [("p","x")] upE 1);
by (asm_simp_tac Up0_ss 1);
by (asm_simp_tac Up0_ss 1);
by (res_inst_tac [("p","y")] upE 1);
by (hyp_subst_tac 1);
by (rtac notE 1);
by (rtac less_up2b 1);
by (atac 1);
by (asm_simp_tac Up0_ss 1);
by (rtac monofun_cfun_arg 1);
by (hyp_subst_tac 1);
by (etac (less_up2c  RS iffD1) 1);
qed "monofun_Ifup2";

(* ------------------------------------------------------------------------ *)
(* Some kind of surjectivity lemma                                          *)
(* ------------------------------------------------------------------------ *)

Goal  "z=Iup(x) ==> Iup(Ifup(LAM x. x)(z)) = z";
by (asm_simp_tac Up0_ss 1);
qed "up_lemma1";

(* ------------------------------------------------------------------------ *)
(* ('a)u is a cpo                                                           *)
(* ------------------------------------------------------------------------ *)

Goal "[|chain(Y);EX i x. Y(i)=Iup(x)|] \
\     ==> range(Y) <<| Iup(lub(range(%i.(Ifup (LAM x. x) (Y(i))))))";
by (rtac is_lubI 1);
by (rtac ub_rangeI 1);
by (res_inst_tac [("p","Y(i)")] upE 1);
by (res_inst_tac [("s","Abs_Up (Inl ())"),("t","Y(i)")] subst 1);
by (etac sym 1);
by (rtac minimal_up 1);
by (res_inst_tac [("t","Y(i)")] (up_lemma1 RS subst) 1);
by (atac 1);
by (rtac (less_up2c RS iffD2) 1);
by (rtac is_ub_thelub 1);
by (etac (monofun_Ifup2 RS ch2ch_monofun) 1);
by (strip_tac 1);
by (res_inst_tac [("p","u")] upE 1);
by (etac exE 1);
by (etac exE 1);
by (res_inst_tac [("P","Y(i)<<Abs_Up (Inl ())")] notE 1);
by (res_inst_tac [("s","Iup(x)"),("t","Y(i)")] ssubst 1);
by (atac 1);
by (rtac less_up2b 1);
by (hyp_subst_tac 1);
by (etac ub_rangeD 1);
by (res_inst_tac [("t","u")] (up_lemma1 RS subst) 1);
by (atac 1);
by (rtac (less_up2c RS iffD2) 1);
by (rtac is_lub_thelub 1);
by (etac (monofun_Ifup2 RS ch2ch_monofun) 1);
by (etac (monofun_Ifup2 RS ub2ub_monofun) 1);
qed "lub_up1a";

Goal "[|chain(Y); ALL i x. Y(i)~=Iup(x)|] ==> range(Y) <<| Abs_Up (Inl ())";
by (rtac is_lubI 1);
by (rtac ub_rangeI 1);
by (res_inst_tac [("p","Y(i)")] upE 1);
by (res_inst_tac [("s","Abs_Up (Inl ())"),("t","Y(i)")] ssubst 1);
by (atac 1);
by (rtac refl_less 1);
by (rtac notE 1);
by (dtac spec 1);
by (dtac spec 1);
by (atac 1);
by (atac 1);
by (strip_tac 1);
by (rtac minimal_up 1);
qed "lub_up1b";

bind_thm ("thelub_up1a", lub_up1a RS thelubI);
(*
[| chain ?Y1; EX i x. ?Y1 i = Iup x |] ==>
 lub (range ?Y1) = Iup (lub (range (%i. Iup (LAM x. x) (?Y1 i))))
*)

bind_thm ("thelub_up1b", lub_up1b RS thelubI);
(*
[| chain ?Y1; ! i x. ?Y1 i ~= Iup x |] ==>
 lub (range ?Y1) = UU_up
*)

Goal "chain(Y::nat=>('a)u) ==> EX x. range(Y) <<|x";
by (rtac disjE 1);
by (rtac exI 2);
by (etac lub_up1a 2);
by (atac 2);
by (rtac exI 2);
by (etac lub_up1b 2);
by (atac 2);
by (fast_tac HOL_cs 1);
qed "cpo_up";

