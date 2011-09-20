(* Author: Tobias Nipkow *)

theory Def_Ass_Sound_Big imports Def_Ass Def_Ass_Big
begin


subsection "Soundness wrt Big Steps"

text{* Note the special form of the induction because one of the arguments
of the inductive predicate is not a variable but the term @{term"Some s"}: *}

theorem Sound:
  "\<lbrakk> (c,Some s) \<Rightarrow> s';  D A c A';  A \<subseteq> dom s \<rbrakk>
  \<Longrightarrow> \<exists> t. s' = Some t \<and> A' \<subseteq> dom t"
proof (induction c "Some s" s' arbitrary: s A A' rule:big_step_induct)
  case AssignNone thus ?case
    by auto (metis aval_Some option.simps(3) subset_trans)
next
  case Semi thus ?case by auto metis
next
  case IfTrue thus ?case by auto blast
next
  case IfFalse thus ?case by auto blast
next
  case IfNone thus ?case
    by auto (metis bval_Some option.simps(3) order_trans)
next
  case WhileNone thus ?case
    by auto (metis bval_Some option.simps(3) order_trans)
next
  case (WhileTrue b s c s' s'')
  from `D A (WHILE b DO c) A'` obtain A' where "D A c A'" by blast
  then obtain t' where "s' = Some t'" "A \<subseteq> dom t'"
    by (metis D_incr WhileTrue(3,7) subset_trans)
  from WhileTrue(5)[OF this(1) WhileTrue(6) this(2)] show ?case .
qed auto

corollary sound: "\<lbrakk>  D (dom s) c A';  (c,Some s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> s' \<noteq> None"
by (metis Sound not_Some_eq subset_refl)

end
