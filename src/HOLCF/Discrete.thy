(*  Title:      HOLCF/Discrete.thy
    ID:         $Id$
    Author:     Tobias Nipkow

Discrete CPOs.
*)

header {* Discrete cpo types *}

theory Discrete
imports Cont
begin

datatype 'a discr = Discr "'a :: type"

subsection {* Type @{typ "'a discr"} is a partial order *}

instance discr :: (type) sq_ord ..

defs (overloaded)
less_discr_def: "((op <<)::('a::type)discr=>'a discr=>bool)  ==  op ="

lemma discr_less_eq [iff]: "((x::('a::type)discr) << y) = (x = y)"
by (unfold less_discr_def) (rule refl)

instance discr :: (type) po
proof
  fix x y z :: "'a discr"
  show "x << x" by simp
  { assume "x << y" and "y << x" thus "x = y" by simp }
  { assume "x << y" and "y << z" thus "x << z" by simp }
qed

subsection {* Type @{typ "'a discr"} is a cpo *}

lemma discr_chain0: 
 "!!S::nat=>('a::type)discr. chain S ==> S i = S 0"
apply (unfold chain_def)
apply (induct_tac "i")
apply (rule refl)
apply (erule subst)
apply (rule sym)
apply fast
done

lemma discr_chain_range0 [simp]: 
 "!!S::nat=>('a::type)discr. chain(S) ==> range(S) = {S 0}"
by (fast elim: discr_chain0)

lemma discr_directed_lemma:
  fixes S :: "'a::type discr set"
  assumes S: "directed S"
  shows "\<exists>x. S = {x}"
proof -
  obtain x where x: "x \<in> S"
    using S by (rule directedE1)
  hence "S = {x}"
  proof (safe)
    fix y assume y: "y \<in> S"
    obtain z where "x \<sqsubseteq> z" "y \<sqsubseteq> z"
      using S x y by (rule directedE2)
    thus "y = x" by simp
  qed
  thus "\<exists>x. S = {x}" ..
qed

instance discr :: (type) dcpo
proof
  fix S :: "'a discr set"
  assume "directed S"
  hence "\<exists>x. S = {x}" by (rule discr_directed_lemma)
  thus "\<exists>x. S <<| x" by (fast intro: is_lub_singleton)
qed

instance discr :: (finite) finite_po
proof
  have "finite (Discr ` (UNIV :: 'a set))"
    by (rule finite_imageI [OF finite])
  also have "(Discr ` (UNIV :: 'a set)) = UNIV"
    by (auto, case_tac x, auto)
  finally show "finite (UNIV :: 'a discr set)" .
qed

instance discr :: (type) chfin
apply (intro_classes, clarify)
apply (rule_tac x=0 in exI)
apply (unfold max_in_chain_def)
apply (clarify, erule discr_chain0 [symmetric])
done

subsection {* @{term undiscr} *}

definition
  undiscr :: "('a::type)discr => 'a" where
  "undiscr x = (case x of Discr y => y)"

lemma undiscr_Discr [simp]: "undiscr(Discr x) = x"
by (simp add: undiscr_def)

lemma discr_chain_f_range0:
 "!!S::nat=>('a::type)discr. chain(S) ==> range(%i. f(S i)) = {f(S 0)}"
by (fast dest: discr_chain0 elim: arg_cong)

lemma cont_discr [iff]: "cont (%x::('a::type)discr. f x)"
apply (rule chfindom_monofun2cont)
apply (rule monofunI, simp)
done

end
