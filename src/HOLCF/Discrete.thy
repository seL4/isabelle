(*  Title:      HOLCF/Discrete.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Discrete CPOs.
*)

theory Discrete
imports Cont Datatype
begin

datatype 'a discr = Discr "'a :: type"

instance discr :: (type) sq_ord ..

defs (overloaded)
less_discr_def: "((op <<)::('a::type)discr=>'a discr=>bool)  ==  op ="

lemma discr_less_eq [iff]: "((x::('a::type)discr) << y) = (x = y)"
apply (unfold less_discr_def)
apply (rule refl)
done

instance discr :: (type) po
proof
  fix x y z :: "'a discr"
  show "x << x" by simp
  { assume "x << y" and "y << x" thus "x = y" by simp }
  { assume "x << y" and "y << z" thus "x << z" by simp }
qed

lemma discr_chain0: 
 "!!S::nat=>('a::type)discr. chain S ==> S i = S 0"
apply (unfold chain_def)
apply (induct_tac "i")
apply (rule refl)
apply (erule subst)
apply (rule sym)
apply fast
done

lemma discr_chain_range0: 
 "!!S::nat=>('a::type)discr. chain(S) ==> range(S) = {S 0}"
apply (fast elim: discr_chain0)
done
declare discr_chain_range0 [simp]

lemma discr_cpo: 
 "!!S. chain S ==> ? x::('a::type)discr. range(S) <<| x"
apply (unfold is_lub_def is_ub_def)
apply (simp (no_asm_simp))
done

instance discr :: (type)cpo
by (intro_classes, rule discr_cpo)

constdefs
   undiscr :: "('a::type)discr => 'a"
  "undiscr x == (case x of Discr y => y)"

lemma undiscr_Discr [simp]: "undiscr(Discr x) = x"
apply (unfold undiscr_def)
apply (simp (no_asm))
done

lemma discr_chain_f_range0:
 "!!S::nat=>('a::type)discr. chain(S) ==> range(%i. f(S i)) = {f(S 0)}"
apply (fast dest: discr_chain0 elim: arg_cong)
done

lemma cont_discr [iff]: "cont(%x::('a::type)discr. f x)"
apply (unfold cont is_lub_def is_ub_def)
apply (simp (no_asm) add: discr_chain_f_range0)
done

end
