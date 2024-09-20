(* Author: Tobias Nipkow *)

theory Def_Init_Big
imports Def_Init_Exp Def_Init
begin

subsection "Initialization-Sensitive Big Step Semantics"

inductive
  big_step :: "(com \<times> state option) \<Rightarrow> state option \<Rightarrow> bool" (infix \<open>\<Rightarrow>\<close> 55)
where
None: "(c,None) \<Rightarrow> None" |
Skip: "(SKIP,s) \<Rightarrow> s" |
AssignNone: "aval a s = None \<Longrightarrow> (x ::= a, Some s) \<Rightarrow> None" |
Assign: "aval a s = Some i \<Longrightarrow> (x ::= a, Some s) \<Rightarrow> Some(s(x := Some i))" |
Seq:    "(c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2 \<Longrightarrow> (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s\<^sub>1) \<Rightarrow> s\<^sub>3" |

IfNone:  "bval b s = None \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,Some s) \<Rightarrow> None" |
IfTrue:  "\<lbrakk> bval b s = Some True;  (c\<^sub>1,Some s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow>
  (IF b THEN c\<^sub>1 ELSE c\<^sub>2,Some s) \<Rightarrow> s'" |
IfFalse: "\<lbrakk> bval b s = Some False;  (c\<^sub>2,Some s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow>
  (IF b THEN c\<^sub>1 ELSE c\<^sub>2,Some s) \<Rightarrow> s'" |

WhileNone: "bval b s = None \<Longrightarrow> (WHILE b DO c,Some s) \<Rightarrow> None" |
WhileFalse: "bval b s = Some False \<Longrightarrow> (WHILE b DO c,Some s) \<Rightarrow> Some s" |
WhileTrue:
  "\<lbrakk> bval b s = Some True;  (c,Some s) \<Rightarrow> s';  (WHILE b DO c,s') \<Rightarrow> s'' \<rbrakk> \<Longrightarrow>
  (WHILE b DO c,Some s) \<Rightarrow> s''"

lemmas big_step_induct = big_step.induct[split_format(complete)]


subsection "Soundness wrt Big Steps"

text\<open>Note the special form of the induction because one of the arguments
of the inductive predicate is not a variable but the term \<^term>\<open>Some s\<close>:\<close>

theorem Sound:
  "\<lbrakk> (c,Some s) \<Rightarrow> s';  D A c A';  A \<subseteq> dom s \<rbrakk>
  \<Longrightarrow> \<exists> t. s' = Some t \<and> A' \<subseteq> dom t"
proof (induction c "Some s" s' arbitrary: s A A' rule:big_step_induct)
  case AssignNone thus ?case
    by auto (metis aval_Some option.simps(3) subset_trans)
next
  case Seq thus ?case by auto metis
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
  from \<open>D A (WHILE b DO c) A'\<close> obtain A' where "D A c A'" by blast
  then obtain t' where "s' = Some t'" "A \<subseteq> dom t'"
    by (metis D_incr WhileTrue(3,7) subset_trans)
  from WhileTrue(5)[OF this(1) WhileTrue(6) this(2)] show ?case .
qed auto

corollary sound: "\<lbrakk>  D (dom s) c A';  (c,Some s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow> s' \<noteq> None"
by (metis Sound not_Some_eq subset_refl)

end

