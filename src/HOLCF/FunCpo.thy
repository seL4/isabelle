(*  Title:      HOLCF/FunCpo.thy
    ID:         $Id$
    Author:     Franz Regensburger
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Definition of the partial ordering for the type of all functions => (fun)

REMARK: The ordering on 'a => 'b is only defined if 'b is in class po !!

Class instance of  => (fun) for class pcpo
*)

header {* Class instances for the type of all functions *}

theory FunCpo
imports Pcpo
begin

subsection {* Type @{typ "'a => 'b"} is a partial order *}

instance fun  :: (type, sq_ord) sq_ord ..

defs (overloaded)
  less_fun_def: "(op <<) == (%f1 f2.!x. f1 x << f2 x)"  

lemma refl_less_fun: "(f::'a::type =>'b::po) << f"
apply (unfold less_fun_def)
apply (fast intro!: refl_less)
done

lemma antisym_less_fun:
        "[|(f1::'a::type =>'b::po) << f2; f2 << f1|] ==> f1 = f2"
apply (unfold less_fun_def)
apply (rule ext)
apply (fast intro!: antisym_less)
done

lemma trans_less_fun:
        "[|(f1::'a::type =>'b::po) << f2; f2 << f3 |] ==> f1 << f3"
apply (unfold less_fun_def)
apply clarify
apply (rule trans_less)
apply (erule allE, assumption)
apply (erule allE, assumption)
done

text {* default class is still type! *}

instance fun  :: (type, po) po
by intro_classes
  (assumption | rule refl_less_fun antisym_less_fun trans_less_fun)+

text {* for compatibility with old HOLCF-Version *}
lemma inst_fun_po: "(op <<)=(%f g.!x. f x << g x)"
apply (fold less_fun_def)
apply (rule refl)
done

text {* make the symbol @{text "<<"} accessible for type fun *}

lemma less_fun: "(f1 << f2) = (! x. f1(x) << f2(x))"
apply (subst inst_fun_po)
apply (rule refl)
done

subsection {* Type @{typ "'a::type => 'b::pcpo"} is pointed *}

lemma minimal_fun: "(%z. UU) << x"
apply (simp (no_asm) add: inst_fun_po minimal)
done

lemmas UU_fun_def = minimal_fun [THEN minimal2UU, symmetric, standard]

lemma least_fun: "? x::'a=>'b::pcpo.!y. x<<y"
apply (rule_tac x = " (%z. UU) " in exI)
apply (rule minimal_fun [THEN allI])
done

subsection {* Type @{typ "'a::type => 'b::pcpo"} is chain complete *}

text {* chains of functions yield chains in the po range *}

lemma ch2ch_fun: "chain (S::nat=>('a=>'b::po)) ==> chain (%i. S i x)"
apply (unfold chain_def)
apply (simp add: less_fun)
done

text {* upper bounds of function chains yield upper bound in the po range *}

lemma ub2ub_fun: "range(S::nat=>('a::type => 'b::po)) <| u ==> range(%i. S i x) <| u(x)"
apply (rule ub_rangeI)
apply (drule ub_rangeD)
apply (simp add: less_fun)
apply auto
done

text {* Type @{typ "'a::type => 'b::pcpo"} is chain complete *}

lemma lub_fun: "chain(S::nat=>('a::type => 'b::cpo)) ==>  
         range(S) <<| (% x. lub(range(% i. S(i)(x))))"
apply (rule is_lubI)
apply (rule ub_rangeI)
apply (subst less_fun)
apply (rule allI)
apply (rule is_ub_thelub)
apply (erule ch2ch_fun)
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

text {* default class is still type *}

instance fun  :: (type, cpo) cpo
by intro_classes (rule cpo_fun)

instance fun  :: (type, pcpo) pcpo
by intro_classes (rule least_fun)

text {* for compatibility with old HOLCF-Version *}
lemma inst_fun_pcpo: "UU = (%x. UU)"
by (simp add: UU_def UU_fun_def)

end

