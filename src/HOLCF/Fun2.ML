(*  Title:      HOLCF/Fun2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

(* for compatibility with old HOLCF-Version *)
Goal "(op <<)=(%f g.!x. f x << g x)";
by (fold_goals_tac [less_fun_def]);
by (rtac refl 1);
qed "inst_fun_po";

(* ------------------------------------------------------------------------ *)
(* Type 'a::type => 'b::pcpo is pointed                                     *)
(* ------------------------------------------------------------------------ *)

Goal "(%z. UU) << x";
by (simp_tac (simpset() addsimps [inst_fun_po,minimal]) 1);
qed "minimal_fun";

bind_thm ("UU_fun_def",minimal_fun RS minimal2UU RS sym);

Goal "? x::'a=>'b::pcpo.!y. x<<y";
by (res_inst_tac [("x","(%z. UU)")] exI 1);
by (rtac (minimal_fun RS allI) 1);
qed "least_fun";

(* ------------------------------------------------------------------------ *)
(* make the symbol << accessible for type fun                               *)
(* ------------------------------------------------------------------------ *)

Goal "(f1 << f2) = (! x. f1(x) << f2(x))";
by (stac inst_fun_po 1);
by (rtac refl 1);
qed "less_fun";

(* ------------------------------------------------------------------------ *)
(* chains of functions yield chains in the po range                         *)
(* ------------------------------------------------------------------------ *)

Goalw [chain_def] "chain (S::nat=>('a=>'b::po)) ==> chain (%i. S i x)";
by (asm_full_simp_tac (simpset() addsimps [less_fun]) 1);
qed "ch2ch_fun";

(* ------------------------------------------------------------------------ *)
(* upper bounds of function chains yield upper bound in the po range        *)
(* ------------------------------------------------------------------------ *)

Goal "range(S::nat=>('a::type => 'b::po)) <| u ==> range(%i. S i x) <| u(x)";
by (rtac ub_rangeI 1);
by (dtac ub_rangeD 1);
by (asm_full_simp_tac (simpset() addsimps [less_fun]) 1);
by Auto_tac; 	
qed "ub2ub_fun";

(* ------------------------------------------------------------------------ *)
(* Type 'a::type => 'b::pcpo is chain complete                              *)
(* ------------------------------------------------------------------------ *)

Goal "chain(S::nat=>('a::type => 'b::cpo)) ==> \
\        range(S) <<| (% x. lub(range(% i. S(i)(x))))";
by (rtac is_lubI 1);
by (rtac ub_rangeI 1);
by (stac less_fun 1);
by (rtac allI 1);
by (rtac is_ub_thelub 1);
by (etac ch2ch_fun 1);
by (strip_tac 1);
by (stac less_fun 1);
by (rtac allI 1);
by (rtac is_lub_thelub 1);
by (etac ch2ch_fun 1);
by (etac ub2ub_fun 1);
qed "lub_fun";

bind_thm ("thelub_fun", lub_fun RS thelubI);
(* chain ?S1 ==> lub (range ?S1) = (%x. lub (range (%i. ?S1 i x))) *)

Goal "chain(S::nat=>('a::type => 'b::cpo)) ==> ? x. range(S) <<| x";
by (rtac exI 1);
by (etac lub_fun 1);
qed "cpo_fun";
