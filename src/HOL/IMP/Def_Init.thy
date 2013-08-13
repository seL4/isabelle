theory Def_Init
imports Vars Com
begin

subsection "Definite Initialization Analysis"

inductive D :: "vname set \<Rightarrow> com \<Rightarrow> vname set \<Rightarrow> bool" where
Skip: "D A SKIP A" |
Assign: "vars a \<subseteq> A \<Longrightarrow> D A (x ::= a) (insert x A)" |
Seq: "\<lbrakk> D A\<^sub>1 c\<^sub>1 A\<^sub>2;  D A\<^sub>2 c\<^sub>2 A\<^sub>3 \<rbrakk> \<Longrightarrow> D A\<^sub>1 (c\<^sub>1;; c\<^sub>2) A\<^sub>3" |
If: "\<lbrakk> vars b \<subseteq> A;  D A c\<^sub>1 A\<^sub>1;  D A c\<^sub>2 A\<^sub>2 \<rbrakk> \<Longrightarrow>
  D A (IF b THEN c\<^sub>1 ELSE c\<^sub>2) (A\<^sub>1 Int A\<^sub>2)" |
While: "\<lbrakk> vars b \<subseteq> A;  D A c A' \<rbrakk> \<Longrightarrow> D A (WHILE b DO c) A"

inductive_cases [elim!]:
"D A SKIP A'"
"D A (x ::= a) A'"
"D A (c1;;c2) A'"
"D A (IF b THEN c1 ELSE c2) A'"
"D A (WHILE b DO c) A'"

lemma D_incr: 
  "D A c A' \<Longrightarrow> A \<subseteq> A'"
by (induct rule: D.induct) auto

end
