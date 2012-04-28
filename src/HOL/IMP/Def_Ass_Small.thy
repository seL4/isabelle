(* Author: Tobias Nipkow *)

theory Def_Ass_Small imports Star Com Def_Ass_Exp
begin

subsection "Initialization-Sensitive Small Step Semantics"

inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "aval a s = Some i \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := Some i))" |

Seq1:   "(SKIP;c,s) \<rightarrow> (c,s)" |
Seq2:   "(c\<^isub>1,s) \<rightarrow> (c\<^isub>1',s') \<Longrightarrow> (c\<^isub>1;c\<^isub>2,s) \<rightarrow> (c\<^isub>1';c\<^isub>2,s')" |

IfTrue:  "bval b s = Some True \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,s) \<rightarrow> (c\<^isub>1,s)" |
IfFalse: "bval b s = Some False \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,s) \<rightarrow> (c\<^isub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

end
