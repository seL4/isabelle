theory Procs_Stat_Vars_Stat imports Procs
begin

subsubsection "Static Scoping of Procedures and Variables"

type_synonym addr = nat
type_synonym venv = "vname \<Rightarrow> addr"
type_synonym store = "addr \<Rightarrow> val"
type_synonym penv = "(pname \<times> com \<times> venv) list"

fun venv :: "penv \<times> venv \<times> nat \<Rightarrow> venv" where
"venv(_,ve,_) = ve"

inductive
  big_step :: "penv \<times> venv \<times> nat \<Rightarrow> com \<times> store \<Rightarrow> store \<Rightarrow> bool"
  (\<open>_ \<turnstile> _ \<Rightarrow> _\<close> [60,0,60] 55)
where
Skip:    "e \<turnstile> (SKIP,s) \<Rightarrow> s" |
Assign:  "(pe,ve,f) \<turnstile> (x ::= a,s) \<Rightarrow> s(ve x := aval a (s o ve))" |
Seq:     "\<lbrakk> e \<turnstile> (c\<^sub>1,s\<^sub>1) \<Rightarrow> s\<^sub>2;  e \<turnstile> (c\<^sub>2,s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow>
          e \<turnstile> (c\<^sub>1;;c\<^sub>2, s\<^sub>1) \<Rightarrow> s\<^sub>3" |

IfTrue:  "\<lbrakk> bval b (s \<circ> venv e);  e \<turnstile> (c\<^sub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
         e \<turnstile> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b (s \<circ> venv e);  e \<turnstile> (c\<^sub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
         e \<turnstile> (IF b THEN c\<^sub>1 ELSE c\<^sub>2, s) \<Rightarrow> t" |

WhileFalse: "\<not>bval b (s \<circ> venv e) \<Longrightarrow> e \<turnstile> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
  "\<lbrakk> bval b (s\<^sub>1 \<circ> venv e);  e \<turnstile> (c,s\<^sub>1) \<Rightarrow> s\<^sub>2;
     e \<turnstile> (WHILE b DO c, s\<^sub>2) \<Rightarrow> s\<^sub>3 \<rbrakk> \<Longrightarrow>
   e \<turnstile> (WHILE b DO c, s\<^sub>1) \<Rightarrow> s\<^sub>3" |

Var: "(pe,ve(x:=f),f+1) \<turnstile> (c,s) \<Rightarrow> t  \<Longrightarrow>
      (pe,ve,f) \<turnstile> ({VAR x; c}, s) \<Rightarrow> t" |

Call1: "((p,c,ve)#pe,ve,f) \<turnstile> (c, s) \<Rightarrow> t  \<Longrightarrow>
        ((p,c,ve)#pe,ve',f) \<turnstile> (CALL p, s) \<Rightarrow> t" |
Call2: "\<lbrakk> p' \<noteq> p;  (pe,ve,f) \<turnstile> (CALL p, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
       ((p',c,ve')#pe,ve,f) \<turnstile> (CALL p, s) \<Rightarrow> t" |

Proc: "((p,cp,ve)#pe,ve,f) \<turnstile> (c,s) \<Rightarrow> t
      \<Longrightarrow>  (pe,ve,f) \<turnstile> ({PROC p = cp; c}, s) \<Rightarrow> t"

code_pred big_step .


values "{map t [10,11] |t.
  ([], <''x'' := 10, ''y'' := 11>, 12)
  \<turnstile> (test_com, <>) \<Rightarrow> t}"

end
