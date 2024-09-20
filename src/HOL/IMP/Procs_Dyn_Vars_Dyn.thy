theory Procs_Dyn_Vars_Dyn imports Procs
begin

subsubsection "Dynamic Scoping of Procedures and Variables"

type_synonym penv = "pname \<Rightarrow> com"

inductive
  big_step :: "penv \<Rightarrow> com \<times> state \<Rightarrow> state \<Rightarrow> bool" (\<open>_ \<turnstile> _ \<Rightarrow> _\<close> [60,0,60] 55)
where
Skip:    "pe \<turnstile> (SKIP,s) \<Rightarrow> s" |
Assign:  "pe \<turnstile> (x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Seq:     "\<lbrakk> pe \<turnstile> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  pe \<turnstile> (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow>
          pe \<turnstile> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |

IfTrue:  "\<lbrakk> bval b s;  pe \<turnstile> (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
         pe \<turnstile> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  pe \<turnstile> (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
         pe \<turnstile> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |

WhileFalse: "\<not>bval b s \<Longrightarrow> pe \<turnstile> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
  "\<lbrakk> bval b s\<^sub>1;  pe \<turnstile> (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;  pe \<turnstile> (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow>
   pe \<turnstile> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |

Var: "pe \<turnstile> (c,s) \<Rightarrow> t  \<Longrightarrow>  pe \<turnstile> ({VAR x; c}, s) \<Rightarrow> t(x := s x)" |

Call: "pe \<turnstile> (pe p, s) \<Rightarrow> t  \<Longrightarrow>  pe \<turnstile> (CALL p, s) \<Rightarrow> t" |

Proc: "pe(p := cp) \<turnstile> (c,s) \<Rightarrow> t  \<Longrightarrow>  pe \<turnstile> ({PROC p = cp; c}, s) \<Rightarrow> t"

code_pred big_step .

values "{map t [''x'',''y''] |t. (\<lambda>p. SKIP) \<turnstile> (test_com, <>) \<Rightarrow> t}"

end
