(*  Title:      HOL/Lex/RegSet.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1998 TUM

Regular sets
*)

theory RegSet = Main:

constdefs
 conc :: "'a list set => 'a list set => 'a list set"
"conc A B == {xs@ys | xs ys. xs:A & ys:B}"

consts star :: "'a list set => 'a list set"
inductive "star A"
intros
  NilI[iff]:   "[] : star A"
  ConsI[intro,simp]:  "[| a:A; as : star A |] ==> a@as : star A"

lemma concat_in_star: "!xs: set xss. xs:S ==> concat xss : star S"
by (induct "xss") simp_all

lemma in_star:
 "w : star U = (? us. (!u : set(us). u : U) & (w = concat us))"
apply (rule iffI)
 apply (erule star.induct)
  apply (rule_tac x = "[]" in exI)
  apply simp
 apply clarify
 apply (rule_tac x = "a#us" in exI)
 apply simp
apply clarify
apply (simp add: concat_in_star)
done

end
