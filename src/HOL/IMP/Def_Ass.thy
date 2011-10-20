theory Def_Ass imports Vars Com
begin

subsection "Definite Assignment Analysis"

inductive D :: "vname set \<Rightarrow> com \<Rightarrow> vname set \<Rightarrow> bool" where
Skip: "D A SKIP A" |
Assign: "vars a \<subseteq> A \<Longrightarrow> D A (x ::= a) (insert x A)" |
Semi: "\<lbrakk> D A\<^isub>1 c\<^isub>1 A\<^isub>2;  D A\<^isub>2 c\<^isub>2 A\<^isub>3 \<rbrakk> \<Longrightarrow> D A\<^isub>1 (c\<^isub>1; c\<^isub>2) A\<^isub>3" |
If: "\<lbrakk> vars b \<subseteq> A;  D A c\<^isub>1 A\<^isub>1;  D A c\<^isub>2 A\<^isub>2 \<rbrakk> \<Longrightarrow>
  D A (IF b THEN c\<^isub>1 ELSE c\<^isub>2) (A\<^isub>1 Int A\<^isub>2)" |
While: "\<lbrakk> vars b \<subseteq> A;  D A c A' \<rbrakk> \<Longrightarrow> D A (WHILE b DO c) A"

inductive_cases [elim!]:
"D A SKIP A'"
"D A (x ::= a) A'"
"D A (c1;c2) A'"
"D A (IF b THEN c1 ELSE c2) A'"
"D A (WHILE b DO c) A'"

lemma D_incr: 
  "D A c A' \<Longrightarrow> A \<subseteq> A'"
by (induct rule: D.induct) auto

end
