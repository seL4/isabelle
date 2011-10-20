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
  ("_ \<turnstile> _ \<Rightarrow> _" [60,0,60] 55)
where
Skip:    "e \<turnstile> (SKIP,s) \<Rightarrow> s" |
Assign:  "(pe,ve,f) \<turnstile> (x ::= a,s) \<Rightarrow> s(ve x := aval a (s o ve))" |
Semi:    "\<lbrakk> e \<turnstile> (c\<^isub>1,s\<^isub>1) \<Rightarrow> s\<^isub>2;  e \<turnstile> (c\<^isub>2,s\<^isub>2) \<Rightarrow> s\<^isub>3 \<rbrakk> \<Longrightarrow>
          e \<turnstile> (c\<^isub>1;c\<^isub>2, s\<^isub>1) \<Rightarrow> s\<^isub>3" |

IfTrue:  "\<lbrakk> bval b (s \<circ> venv e);  e \<turnstile> (c\<^isub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
         e \<turnstile> (IF b THEN c\<^isub>1 ELSE c\<^isub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b (s \<circ> venv e);  e \<turnstile> (c\<^isub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
         e \<turnstile> (IF b THEN c\<^isub>1 ELSE c\<^isub>2, s) \<Rightarrow> t" |

WhileFalse: "\<not>bval b (s \<circ> venv e) \<Longrightarrow> e \<turnstile> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:
  "\<lbrakk> bval b (s\<^isub>1 \<circ> venv e);  e \<turnstile> (c,s\<^isub>1) \<Rightarrow> s\<^isub>2;
     e \<turnstile> (WHILE b DO c, s\<^isub>2) \<Rightarrow> s\<^isub>3 \<rbrakk> \<Longrightarrow>
   e \<turnstile> (WHILE b DO c, s\<^isub>1) \<Rightarrow> s\<^isub>3" |

Var: "(pe,ve(x:=f),f+1) \<turnstile> (c,s) \<Rightarrow> t  \<Longrightarrow>
      (pe,ve,f) \<turnstile> ({VAR x;; c}, s) \<Rightarrow> t(f := s f)" |

Call1: "((p,c,ve)#pe,ve,f) \<turnstile> (c, s) \<Rightarrow> t  \<Longrightarrow>
        ((p,c,ve)#pe,ve',f) \<turnstile> (CALL p, s) \<Rightarrow> t" |
Call2: "\<lbrakk> p' \<noteq> p;  (pe,ve,f) \<turnstile> (CALL p, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
       ((p',c,ve')#pe,ve,f) \<turnstile> (CALL p, s) \<Rightarrow> t" |

Proc: "((p,cp,ve)#pe,ve,f) \<turnstile> (c,s) \<Rightarrow> t
      \<Longrightarrow>  (pe,ve,f) \<turnstile> ({PROC p = cp;; c}, s) \<Rightarrow> t"

code_pred big_step .


values "{map t [0,1] |t. ([], <>, 0) \<turnstile> (CALL ''p'', nth [42, 43]) \<Rightarrow> t}"

values "{map t [0, 1, 2] |t.
  ([], <''x'' := 0, ''y'' := 1,''z'' := 2>, 0)
  \<turnstile> (test_com, <>) \<Rightarrow> t}"

end
