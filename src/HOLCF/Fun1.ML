(*  Title: 	HOLCF/fun1.ML
    ID:         $Id$
    Author: 	Franz Regensburger
    Copyright   1993  Technische Universitaet Muenchen

Lemmas for fun1.thy 
*)

open Fun1;

(* ------------------------------------------------------------------------ *)
(* less_fun is a partial order on 'a => 'b                                  *)
(* ------------------------------------------------------------------------ *)

qed_goalw "refl_less_fun" Fun1.thy [less_fun_def] "less_fun f f"
(fn prems =>
	[
	(fast_tac (HOL_cs addSIs [refl_less]) 1)
	]);

qed_goalw "antisym_less_fun" Fun1.thy [less_fun_def] 
	"[|less_fun f1 f2; less_fun f2 f1|] ==> f1 = f2"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(rtac (expand_fun_eq RS ssubst) 1),
	(fast_tac (HOL_cs addSIs [antisym_less]) 1)
	]);

qed_goalw "trans_less_fun" Fun1.thy [less_fun_def] 
	"[|less_fun f1 f2; less_fun f2 f3 |] ==> less_fun f1 f3"
(fn prems =>
	[
	(cut_facts_tac prems 1),
	(strip_tac 1),
	(rtac trans_less 1),
	(etac allE 1),
	(atac 1),
	((etac allE 1) THEN (atac 1))
	]);

(* 
 -------------------------------------------------------------------------- 
   Since less_fun :: "['a::term=>'b::po,'a::term=>'b::po] => bool" the
   lemmas refl_less_fun, antisym_less_fun, trans_less_fun justify
   the class arity fun::(term,po)po !!
 -------------------------------------------------------------------------- 
*)

