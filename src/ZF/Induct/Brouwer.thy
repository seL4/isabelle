(*  Title:      ZF/Induct/Brouwer.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1994  University of Cambridge
*)

header {* Infinite branching datatype definitions *}

theory Brouwer = Main_ZFC:

subsection {* The Brouwer ordinals *}

consts
  brouwer :: i

datatype \<subseteq> "Vfrom(0, csucc(nat))"
    "brouwer" = Zero | Suc ("b \<in> brouwer") | Lim ("h \<in> nat -> brouwer")
  monos Pi_mono
  type_intros inf_datatype_intrs

lemma brouwer_unfold: "brouwer = {0} + brouwer + (nat -> brouwer)"
  by (fast intro!: brouwer.intros [unfolded brouwer.con_defs]
    elim: brouwer.cases [unfolded brouwer.con_defs])

lemma brouwer_induct2:
  "[| b \<in> brouwer;
      P(Zero);
      !!b. [| b \<in> brouwer;  P(b) |] ==> P(Suc(b));
      !!h. [| h \<in> nat -> brouwer;  \<forall>i \<in> nat. P(h`i)
           |] ==> P(Lim(h))
   |] ==> P(b)"
  -- {* A nicer induction rule than the standard one. *}
proof -
  case rule_context
  assume "b \<in> brouwer"
  thus ?thesis
    apply induct
    apply (assumption | rule rule_context)+
     apply (fast elim: fun_weaken_type)
    apply (fast dest: apply_type)
    done
qed


subsection {* The Martin-Löf wellordering type *}

consts
  Well :: "[i, i => i] => i"

datatype \<subseteq> "Vfrom(A \<union> (\<Union>x \<in> A. B(x)), csucc(nat \<union> |\<Union>x \<in> A. B(x)|))"
    -- {* The union with @{text nat} ensures that the cardinal is infinite. *}
  "Well(A, B)" = Sup ("a \<in> A", "f \<in> B(a) -> Well(A, B)")
  monos Pi_mono
  type_intros le_trans [OF UN_upper_cardinal le_nat_Un_cardinal] inf_datatype_intrs

lemma Well_unfold: "Well(A, B) = (\<Sigma>x \<in> A. B(x) -> Well(A, B))"
  by (fast intro!: Well.intros [unfolded Well.con_defs]
    elim: Well.cases [unfolded Well.con_defs])


lemma Well_induct2:
  "[| w \<in> Well(A, B);
      !!a f. [| a \<in> A;  f \<in> B(a) -> Well(A,B);  \<forall>y \<in> B(a). P(f`y)
           |] ==> P(Sup(a,f))
   |] ==> P(w)"
  -- {* A nicer induction rule than the standard one. *}
proof -
  case rule_context
  assume "w \<in> Well(A, B)"
  thus ?thesis
    apply induct
    apply (assumption | rule rule_context)+
     apply (fast elim: fun_weaken_type)
    apply (fast dest: apply_type)
    done
qed

lemma Well_bool_unfold: "Well(bool, \<lambda>x. x) = 1 + (1 -> Well(bool, \<lambda>x. x))"
  -- {* In fact it's isomorphic to @{text nat}, but we need a recursion operator *}
  -- {* for @{text Well} to prove this. *}
  apply (rule Well_unfold [THEN trans])
  apply (simp add: Sigma_bool Pi_empty1 succ_def)
  done

end
