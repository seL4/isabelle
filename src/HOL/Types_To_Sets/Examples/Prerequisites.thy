(*  Title:      HOL/Types_To_Sets/Examples/Prerequisites.thy
    Author:     Ondřej Kunčar, TU München
*)

theory Prerequisites
  imports Main
begin

context
  fixes Rep Abs A T
  assumes type: "type_definition Rep Abs A"
  assumes T_def: "T \<equiv> (\<lambda>(x::'a) (y::'b). x = Rep y)"
begin

lemma type_definition_Domainp: "Domainp T = (\<lambda>x. x \<in> A)"
proof -
  interpret type_definition Rep Abs A by(rule type)
  show ?thesis
    unfolding Domainp_iff[abs_def] T_def fun_eq_iff
    by (metis Abs_inverse Rep)
qed

end

end
