(*  Title:      HOLCF/fun2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    Copyright   1993 Technische Universitaet Muenchen

Lemmas for fun2.thy 
*)

open Fun2;

(* for compatibility with old HOLCF-Version *)
qed_goal "inst_fun_po" thy "(op <<)=(%f g.!x.f x << g x)"
 (fn prems => 
        [
	(fold_goals_tac [po_def,less_fun_def]),
	(rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Type 'a::term => 'b::pcpo is pointed                                     *)
(* ------------------------------------------------------------------------ *)

qed_goal "minimal_fun" thy "(%z.UU) << x"
(fn prems =>
        [
        (simp_tac (!simpset addsimps [inst_fun_po,minimal]) 1)
        ]);

bind_thm ("UU_fun_def",minimal_fun RS minimal2UU RS sym);

qed_goal "least_fun" thy "? x::'a=>'b::pcpo.!y.x<<y"
(fn prems =>
        [
        (res_inst_tac [("x","(%z.UU)")] exI 1),
        (rtac (minimal_fun RS allI) 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* make the symbol << accessible for type fun                               *)
(* ------------------------------------------------------------------------ *)

qed_goal "less_fun" thy "(f1 << f2) = (! x. f1(x) << f2(x))"
(fn prems =>
        [
        (stac inst_fun_po 1),
        (fold_goals_tac [less_fun_def]),
        (rtac refl 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* chains of functions yield chains in the po range                         *)
(* ------------------------------------------------------------------------ *)

qed_goal "ch2ch_fun" thy 
        "is_chain(S::nat=>('a=>'b::po)) ==> is_chain(% i.S(i)(x))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rewtac is_chain),
        (rtac allI 1),
        (rtac spec 1),
        (rtac (less_fun RS subst) 1),
        (etac allE 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* upper bounds of function chains yield upper bound in the po range        *)
(* ------------------------------------------------------------------------ *)

qed_goal "ub2ub_fun" Fun2.thy 
   " range(S::nat=>('a::term => 'b::po)) <| u ==> range(%i. S i x) <| u(x)"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac ub_rangeI 1),
        (rtac allI 1),
        (rtac allE 1),
        (rtac (less_fun RS subst) 1),
        (etac (ub_rangeE RS spec) 1),
        (atac 1)
        ]);

(* ------------------------------------------------------------------------ *)
(* Type 'a::term => 'b::pcpo is chain complete                              *)
(* ------------------------------------------------------------------------ *)

qed_goal "lub_fun"  Fun2.thy
        "is_chain(S::nat=>('a::term => 'b::cpo)) ==> \
\        range(S) <<| (% x.lub(range(% i.S(i)(x))))"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac is_lubI 1),
        (rtac conjI 1),
        (rtac ub_rangeI 1),
        (rtac allI 1),
        (stac less_fun 1),
        (rtac allI 1),
        (rtac is_ub_thelub 1),
        (etac ch2ch_fun 1),
        (strip_tac 1),
        (stac less_fun 1),
        (rtac allI 1),
        (rtac is_lub_thelub 1),
        (etac ch2ch_fun 1),
        (etac ub2ub_fun 1)
        ]);

bind_thm ("thelub_fun", lub_fun RS thelubI);
(* is_chain ?S1 ==> lub (range ?S1) = (%x. lub (range (%i. ?S1 i x))) *)

qed_goal "cpo_fun"  Fun2.thy
        "is_chain(S::nat=>('a::term => 'b::cpo)) ==> ? x. range(S) <<| x"
(fn prems =>
        [
        (cut_facts_tac prems 1),
        (rtac exI 1),
        (etac lub_fun 1)
        ]);
