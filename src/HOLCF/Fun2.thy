(*  Title:      HOLCF/Fun2.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

theory Fun2 = Fun1:

(* default class is still type!*)

instance fun  :: (type, po) po
apply (intro_classes)
apply (rule refl_less_fun)
apply (rule antisym_less_fun, assumption+)
apply (rule trans_less_fun, assumption+)
done

(*  Title:      HOLCF/Fun2.ML
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

(* for compatibility with old HOLCF-Version *)
lemma inst_fun_po: "(op <<)=(%f g.!x. f x << g x)"
apply (fold less_fun_def)
apply (rule refl)
done

(* ------------------------------------------------------------------------ *)
(* Type 'a::type => 'b::pcpo is pointed                                     *)
(* ------------------------------------------------------------------------ *)

lemma minimal_fun: "(%z. UU) << x"
apply (simp (no_asm) add: inst_fun_po minimal)
done

lemmas UU_fun_def = minimal_fun [THEN minimal2UU, symmetric, standard]

lemma least_fun: "? x::'a=>'b::pcpo.!y. x<<y"
apply (rule_tac x = " (%z. UU) " in exI)
apply (rule minimal_fun [THEN allI])
done

(* ------------------------------------------------------------------------ *)
(* make the symbol << accessible for type fun                               *)
(* ------------------------------------------------------------------------ *)

lemma less_fun: "(f1 << f2) = (! x. f1(x) << f2(x))"
apply (subst inst_fun_po)
apply (rule refl)
done

(* ------------------------------------------------------------------------ *)
(* chains of functions yield chains in the po range                         *)
(* ------------------------------------------------------------------------ *)

lemma ch2ch_fun: "chain (S::nat=>('a=>'b::po)) ==> chain (%i. S i x)"

apply (unfold chain_def)
apply (simp add: less_fun)
done

(* ------------------------------------------------------------------------ *)
(* upper bounds of function chains yield upper bound in the po range        *)
(* ------------------------------------------------------------------------ *)

lemma ub2ub_fun: "range(S::nat=>('a::type => 'b::po)) <| u ==> range(%i. S i x) <| u(x)"
apply (rule ub_rangeI)
apply (drule ub_rangeD)
apply (simp add: less_fun)
apply auto
done

(* ------------------------------------------------------------------------ *)
(* Type 'a::type => 'b::pcpo is chain complete                              *)
(* ------------------------------------------------------------------------ *)

lemma lub_fun: "chain(S::nat=>('a::type => 'b::cpo)) ==>  
         range(S) <<| (% x. lub(range(% i. S(i)(x))))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (subst less_fun)
apply (rule allI)
apply (rule is_ub_thelub)
apply (erule ch2ch_fun)
(* apply (intro strip) *)
apply (subst less_fun)
apply (rule allI)
apply (rule is_lub_thelub)
apply (erule ch2ch_fun)
apply (erule ub2ub_fun)
done

lemmas thelub_fun = lub_fun [THEN thelubI, standard]
(* chain ?S1 ==> lub (range ?S1) = (%x. lub (range (%i. ?S1 i x))) *)

lemma cpo_fun: "chain(S::nat=>('a::type => 'b::cpo)) ==> ? x. range(S) <<| x"
apply (rule exI)
apply (erule lub_fun)
done

end








