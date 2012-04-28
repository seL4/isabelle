(* Author: Tobias Nipkow *)

theory Def_Ass_Big imports Com Def_Ass_Exp
begin

subsection "Initialization-Sensitive Big Step Semantics"

inductive
  big_step :: "(com \<times> state option) \<Rightarrow> state option \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
None: "(c,None) \<Rightarrow> None" |
Skip: "(SKIP,s) \<Rightarrow> s" |
AssignNone: "aval a s = None \<Longrightarrow> (x ::= a, Some s) \<Rightarrow> None" |
Assign: "aval a s = Some i \<Longrightarrow> (x ::= a, Some s) \<Rightarrow> Some(s(x := Some i))" |
Seq:    "(c\<^isub>1,s\<^isub>1) \<Rightarrow> s\<^isub>2 \<Longrightarrow> (c\<^isub>2,s\<^isub>2) \<Rightarrow> s\<^isub>3 \<Longrightarrow> (c\<^isub>1;c\<^isub>2,s\<^isub>1) \<Rightarrow> s\<^isub>3" |

IfNone:  "bval b s = None \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,Some s) \<Rightarrow> None" |
IfTrue:  "\<lbrakk> bval b s = Some True;  (c\<^isub>1,Some s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow>
  (IF b THEN c\<^isub>1 ELSE c\<^isub>2,Some s) \<Rightarrow> s'" |
IfFalse: "\<lbrakk> bval b s = Some False;  (c\<^isub>2,Some s) \<Rightarrow> s' \<rbrakk> \<Longrightarrow>
  (IF b THEN c\<^isub>1 ELSE c\<^isub>2,Some s) \<Rightarrow> s'" |

WhileNone: "bval b s = None \<Longrightarrow> (WHILE b DO c,Some s) \<Rightarrow> None" |
WhileFalse: "bval b s = Some False \<Longrightarrow> (WHILE b DO c,Some s) \<Rightarrow> Some s" |
WhileTrue:
  "\<lbrakk> bval b s = Some True;  (c,Some s) \<Rightarrow> s';  (WHILE b DO c,s') \<Rightarrow> s'' \<rbrakk> \<Longrightarrow>
  (WHILE b DO c,Some s) \<Rightarrow> s''"

lemmas big_step_induct = big_step.induct[split_format(complete)]

end
