(*  Title:      HOLCF/Fun2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Class Instance =>::(term,po)po
*)

(* for compatibility with old HOLCF-Version *)
val prems = goal thy "(op <<)=(%f g.!x. f x << g x)";
by (fold_goals_tac [less_fun_def]);
by (rtac refl 1);
qed "inst_fun_po";

(* ------------------------------------------------------------------------ *)
(* Type 'a::term => 'b::pcpo is pointed                                     *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy "(%z. UU) << x";
by (simp_tac (simpset() addsimps [inst_fun_po,minimal]) 1);
qed "minimal_fun";

bind_thm ("UU_fun_def",minimal_fun RS minimal2UU RS sym);

val prems = goal thy "? x::'a=>'b::pcpo.!y. x<<y";
by (res_inst_tac [("x","(%z. UU)")] exI 1);
by (rtac (minimal_fun RS allI) 1);
qed "least_fun";

(* ------------------------------------------------------------------------ *)
(* make the symbol << accessible for type fun                               *)
(* ------------------------------------------------------------------------ *)

val prems = goal thy "(f1 << f2) = (! x. f1(x) << f2(x))";
by (stac inst_fun_po 1);
by (rtac refl 1);
qed "less_fun";

(* ------------------------------------------------------------------------ *)
(* chains of functions yield chains in the po range                         *)
(* ------------------------------------------------------------------------ *)

Goalw [chain] "chain(S::nat=>('a=>'b::po)) ==> chain(% i. S(i)(x))";
by (asm_full_simp_tac (simpset() addsimps [less_fun]) 1);
qed "ch2ch_fun";

(* ------------------------------------------------------------------------ *)
(* upper bounds of function chains yield upper bound in the po range        *)
(* ------------------------------------------------------------------------ *)

val prems = goal Fun2.thy 
   " range(S::nat=>('a::term => 'b::po)) <| u ==> range(%i. S i x) <| u(x)";
by (cut_facts_tac prems 1);
by (rtac ub_rangeI 1);
by (rtac allI 1);
by (rtac allE 1);
by (rtac (less_fun RS subst) 1);
by (etac (ub_rangeE RS spec) 1);
by (atac 1);
qed "ub2ub_fun";

(* ------------------------------------------------------------------------ *)
(* Type 'a::term => 'b::pcpo is chain complete                              *)
(* ------------------------------------------------------------------------ *)

val prems = goal  Fun2.thy
        "chain(S::nat=>('a::term => 'b::cpo)) ==> \
\        range(S) <<| (% x. lub(range(% i. S(i)(x))))";
by (cut_facts_tac prems 1);
by (rtac is_lubI 1);
by (rtac conjI 1);
by (rtac ub_rangeI 1);
by (rtac allI 1);
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

val prems = goal  Fun2.thy
        "chain(S::nat=>('a::term => 'b::cpo)) ==> ? x. range(S) <<| x";
by (cut_facts_tac prems 1);
by (rtac exI 1);
by (etac lub_fun 1);
qed "cpo_fun";
