(* Author: Tobias Nipkow *)

header "A Compiler for IMP"

theory Compiler imports Big_Step
begin

subsection "Instructions and Stack Machine"

datatype instr = 
  LOADI int | LOAD string | ADD |
  STORE string |
  JMPF nat |
  JMPB nat |
  JMPFLESS nat |
  JMPFGE nat

type_synonym stack = "int list"
type_synonym config = "nat\<times>state\<times>stack"

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

inductive exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
    ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [50,0,0] 50)
  for P :: "instr list"
where
"\<lbrakk> i < size P;  P!i = LOADI n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s, n#stk)" |
"\<lbrakk> i < size P;  P!i = LOAD x \<rbrakk> \<Longrightarrow> 
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s, s x # stk)" |
"\<lbrakk> i < size P;  P!i = ADD \<rbrakk> \<Longrightarrow> 
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s, (hd2 stk + hd stk) # tl2 stk)" |
"\<lbrakk> i < size P;  P!i = STORE n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s(n := hd stk),tl stk)" |
"\<lbrakk> i < size P;  P!i = JMPF n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1+n,s,stk)" |
"\<lbrakk> i < size P;  P!i = JMPB n;  n \<le> i+1 \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1-n,s,stk)" |
"\<lbrakk> i < size P;  P!i = JMPFLESS n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (if hd2 stk < hd stk then i+1+n else i+1,s,tl2 stk)" |
"\<lbrakk> i < size P;  P!i = JMPFGE n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (if hd2 stk >= hd stk then i+1+n else i+1,s,tl2 stk)"

code_pred exec1 .

declare exec1.intros[intro]

inductive exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("_/ \<turnstile> (_ \<rightarrow>*/ _)" 50)
where
refl: "P \<turnstile> c \<rightarrow>* c" |
step: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P \<turnstile> c' \<rightarrow>* c'' \<Longrightarrow> P \<turnstile> c \<rightarrow>* c''"

declare exec.intros[intro]

lemmas exec_induct = exec.induct[split_format(complete)]

code_pred exec .

values
  "{(i,map t [''x'',''y''],stk) | i t stk.
    [LOAD ''y'', STORE ''x''] \<turnstile>
    (0, [''x'' \<rightarrow> 3, ''y'' \<rightarrow> 4], []) \<rightarrow>* (i,t,stk)}"


subsection{* Verification infrastructure *}

lemma exec_trans: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P \<turnstile> c' \<rightarrow>* c'' \<Longrightarrow> P \<turnstile> c \<rightarrow>* c''"
apply(induct rule: exec.induct)
 apply blast
by (metis exec.step)

lemma exec1_subst: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> c' = c'' \<Longrightarrow> P \<turnstile> c \<rightarrow> c''"
by auto

lemmas exec1_simps = exec1.intros[THEN exec1_subst]

text{* Below we need to argue about the execution of code that is embedded in
larger programs. For this purpose we show that execution is preserved by
appending code to the left or right of a program. *}

lemma exec1_appendR: assumes "P \<turnstile> c \<rightarrow> c'" shows "P@P' \<turnstile> c \<rightarrow> c'"
proof-
  from assms show ?thesis
  by cases (simp_all add: exec1_simps nth_append)
  -- "All cases proved with the final simp-all"
qed

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow>* c'"
apply(induct rule: exec.induct)
 apply blast
by (metis exec1_appendR exec.step)

lemma exec1_appendL:
assumes "P \<turnstile> (i,s,stk) \<rightarrow> (i',s',stk')"
shows "P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow> (size(P')+i',s',stk')"
proof-
  from assms show ?thesis
  by cases (simp_all add: exec1_simps)
qed

lemma exec_appendL:
 "P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')  \<Longrightarrow>
  P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow>* (size(P')+i',s',stk')"
apply(induct rule: exec_induct)
 apply blast
by (blast intro: exec1_appendL exec.step)

text{* Now we specialise the above lemmas to enable automatic proofs of
@{prop "P \<turnstile> c \<rightarrow>* c'"} where @{text P} is a mixture of concrete instructions and
pieces of code that we already know how they execute (by induction), combined
by @{text "@"} and @{text "#"}. Backward jumps are not supported.
The details should be skipped on a first reading.

If the pc points beyond the first instruction or part of the program, drop it: *}

lemma exec_Cons_Suc[intro]:
  "P \<turnstile> (i,s,stk) \<rightarrow>* (j,t,stk') \<Longrightarrow>
  instr#P \<turnstile> (Suc i,s,stk) \<rightarrow>* (Suc j,t,stk')"
apply(drule exec_appendL[where P'="[instr]"])
apply simp
done

lemma exec_appendL_if[intro]:
 "size P' <= i
  \<Longrightarrow> P \<turnstile> (i - size P',s,stk) \<rightarrow>* (i',s',stk')
  \<Longrightarrow> P' @ P \<turnstile> (i,s,stk) \<rightarrow>* (size P' + i',s',stk')"
apply(drule exec_appendL[where P'=P'])
apply simp
done

text{* Split the execution of a compound program up into the excution of its
parts: *}

lemma exec_append_trans[intro]:
"P \<turnstile> (0,s,stk) \<rightarrow>* (i',s',stk') \<Longrightarrow>
 size P \<le> i' \<Longrightarrow>
 P' \<turnstile>  (i' - size P,s',stk') \<rightarrow>* (i'',s'',stk'') \<Longrightarrow>
 j'' = size P + i''
 \<Longrightarrow>
 P @ P' \<turnstile> (0,s,stk) \<rightarrow>* (j'',s'',stk'')"
by(metis exec_trans[OF  exec_appendR exec_appendL_if])


declare Let_def[simp] eval_nat_numeral[simp]


subsection "Compilation"

fun acomp :: "aexp \<Rightarrow> instr list" where
"acomp (N n) = [LOADI n]" |
"acomp (V x) = [LOAD x]" |
"acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"

lemma acomp_correct[intro]:
  "acomp a \<turnstile> (0,s,stk) \<rightarrow>* (size(acomp a),s,aval a s#stk)"
apply(induct a arbitrary: stk)
apply(fastsimp)+
done

fun bcomp :: "bexp \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> instr list" where
"bcomp (B bv) c n = (if bv=c then [JMPF n] else [])" |
"bcomp (Not b) c n = bcomp b (\<not>c) n" |
"bcomp (And b1 b2) c n =
 (let cb2 = bcomp b2 c n;
      m = (if c then size cb2 else size cb2+n);
      cb1 = bcomp b1 False m
  in cb1 @ cb2)" |
"bcomp (Less a1 a2) c n =
 acomp a1 @ acomp a2 @ (if c then [JMPFLESS n] else [JMPFGE n])"

value
  "bcomp (And (Less (V ''x'') (V ''y'')) (Not(Less (V ''u'') (V ''v''))))
     False 3"

lemma bcomp_correct[intro]:
 "bcomp b c n \<turnstile>
 (0,s,stk)  \<rightarrow>*  (size(bcomp b c n) + (if c = bval b s then n else 0),s,stk)"
proof(induct b arbitrary: c n m)
  case Not
  from Not[of "~c"] show ?case by fastsimp
next
  case (And b1 b2)
  from And(1)[of "False"] And(2)[of "c"] show ?case by fastsimp
qed fastsimp+


fun ccomp :: "com \<Rightarrow> instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c\<^isub>1;c\<^isub>2) = ccomp c\<^isub>1 @ ccomp c\<^isub>2" |
"ccomp (IF b THEN c\<^isub>1 ELSE c\<^isub>2) =
  (let cc\<^isub>1 = ccomp c\<^isub>1; cc\<^isub>2 = ccomp c\<^isub>2; cb = bcomp b False (size cc\<^isub>1 + 1)
   in cb @ cc\<^isub>1 @ JMPF(size cc\<^isub>2) # cc\<^isub>2)" |
"ccomp (WHILE b DO c) =
 (let cc = ccomp c; cb = bcomp b False (size cc + 1)
  in cb @ cc @ [JMPB (size cb + size cc + 1)])"

value "ccomp
 (IF Less (V ''u'') (N 1) THEN ''u'' ::= Plus (V ''u'') (N 1)
  ELSE ''v'' ::= V ''u'')"

value "ccomp (WHILE Less (V ''u'') (N 1) DO (''u'' ::= Plus (V ''u'') (N 1)))"


subsection "Preservation of sematics"

lemma ccomp_correct:
  "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)"
proof(induct arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastsimp simp:fun_upd_def)
next
  case (Semi c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp c1"  let ?cc2 = "ccomp c2"
  have "?cc1 @ ?cc2 \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cc1,s2,stk)"
    using Semi.hyps(2) by (fastsimp)
  moreover
  have "?cc1 @ ?cc2 \<turnstile> (size ?cc1,s2,stk) \<rightarrow>* (size(?cc1 @ ?cc2),s3,stk)"
    using Semi.hyps(4) by (fastsimp)
  ultimately show ?case by simp (blast intro: exec_trans)
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b False (size ?cc + 1)"
  let ?cw = "ccomp(WHILE b DO c)"
  have "?cw \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cb + size ?cc,s2,stk)"
    using WhileTrue(1,3) by fastsimp
  moreover
  have "?cw \<turnstile> (size ?cb + size ?cc,s2,stk) \<rightarrow>* (0,s2,stk)"
    by (fastsimp)
  moreover
  have "?cw \<turnstile> (0,s2,stk) \<rightarrow>* (size ?cw,s3,stk)" by(rule WhileTrue(5))
  ultimately show ?case by(blast intro: exec_trans)
qed fastsimp+

end
