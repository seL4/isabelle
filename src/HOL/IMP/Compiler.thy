(* Author: Tobias Nipkow and Gerwin Klein *)

section "Compiler for IMP"

theory Compiler imports Big_Step Star
begin

subsection "List setup"

text \<open>
  In the following, we use the length of lists as integers 
  instead of natural numbers. Instead of converting \<^typ>\<open>nat\<close>
  to \<^typ>\<open>int\<close> explicitly, we tell Isabelle to coerce \<^typ>\<open>nat\<close>
  automatically when necessary.
\<close>
declare [[coercion_enabled]] 
declare [[coercion "int :: nat \<Rightarrow> int"]]

text \<open>
  Similarly, we will want to access the ith element of a list, 
  where \<^term>\<open>i\<close> is an \<^typ>\<open>int\<close>.
\<close>
fun inth :: "'a list \<Rightarrow> int \<Rightarrow> 'a" (infixl \<open>!!\<close> 100) where
"(x # xs) !! i = (if i = 0 then x else xs !! (i - 1))"

text \<open>
  The only additional lemma we need about this function 
  is indexing over append:
\<close>
lemma inth_append [simp]:
  "0 \<le> i \<Longrightarrow>
  (xs @ ys) !! i = (if i < size xs then xs !! i else ys !! (i - size xs))"
by (induction xs arbitrary: i) (auto simp: algebra_simps)

text\<open>We hide coercion \<^const>\<open>int\<close> applied to \<^const>\<open>length\<close>:\<close>

abbreviation (output)
  "isize xs == int (length xs)"

notation isize (\<open>size\<close>)


subsection "Instructions and Stack Machine"

text_raw\<open>\snip{instrdef}{0}{1}{%\<close>
datatype instr = 
  LOADI int | LOAD vname | ADD | STORE vname |
  JMP int | JMPLESS int | JMPGE int
text_raw\<open>}%endsnip\<close>

type_synonym stack = "val list"
type_synonym config = "int \<times> state \<times> stack"

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

fun iexec :: "instr \<Rightarrow> config \<Rightarrow> config" where
"iexec instr (i,s,stk) = (case instr of
  LOADI n \<Rightarrow> (i+1,s, n#stk) |
  LOAD x \<Rightarrow> (i+1,s, s x # stk) |
  ADD \<Rightarrow> (i+1,s, (hd2 stk + hd stk) # tl2 stk) |
  STORE x \<Rightarrow> (i+1,s(x := hd stk),tl stk) |
  JMP n \<Rightarrow>  (i+1+n,s,stk) |
  JMPLESS n \<Rightarrow> (if hd2 stk < hd stk then i+1+n else i+1,s,tl2 stk) |
  JMPGE n \<Rightarrow> (if hd2 stk >= hd stk then i+1+n else i+1,s,tl2 stk))"

definition
  exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
     (\<open>(_/ \<turnstile> (_ \<rightarrow>/ _))\<close> [59,0,59] 60) 
where
  "P \<turnstile> c \<rightarrow> c' = 
  (\<exists>i s stk. c = (i,s,stk) \<and> c' = iexec(P!!i) (i,s,stk) \<and> 0 \<le> i \<and> i < size P)"

lemma exec1I [intro, code_pred_intro]:
  "c' = iexec (P!!i) (i,s,stk) \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < size P
  \<Longrightarrow> P \<turnstile> (i,s,stk) \<rightarrow> c'"
by (simp add: exec1_def)

abbreviation 
  exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" (\<open>(_/ \<turnstile> (_ \<rightarrow>*/ _))\<close> 50)
where
  "exec P \<equiv> star (exec1 P)"

lemmas exec_induct = star.induct [of "exec1 P", split_format(complete)]

code_pred exec1 by (metis exec1_def)

values
  "{(i,map t [''x'',''y''],stk) | i t stk.
    [LOAD ''y'', STORE ''x''] \<turnstile>
    (0, <''x'' := 3, ''y'' := 4>, []) \<rightarrow>* (i,t,stk)}"


subsection\<open>Verification infrastructure\<close>

text\<open>Below we need to argue about the execution of code that is embedded in
larger programs. For this purpose we show that execution is preserved by
appending code to the left or right of a program.\<close>

lemma iexec_shift [simp]: 
  "((n+i',s',stk') = iexec x (n+i,s,stk)) = ((i',s',stk') = iexec x (i,s,stk))"
by(auto split:instr.split)

lemma exec1_appendR: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow> c'"
by (auto simp: exec1_def)

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow>* c'"
by (induction rule: star.induct) (fastforce intro: star.step exec1_appendR)+

lemma exec1_appendL:
  fixes i i' :: int 
  shows
  "P \<turnstile> (i,s,stk) \<rightarrow> (i',s',stk') \<Longrightarrow>
   P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow> (size(P')+i',s',stk')"
  unfolding exec1_def
  by (auto simp del: iexec.simps)

lemma exec_appendL:
  fixes i i' :: int 
  shows
 "P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')  \<Longrightarrow>
  P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow>* (size(P')+i',s',stk')"
  by (induction rule: exec_induct) (blast intro: star.step exec1_appendL)+

text\<open>Now we specialise the above lemmas to enable automatic proofs of
\<^prop>\<open>P \<turnstile> c \<rightarrow>* c'\<close> where \<open>P\<close> is a mixture of concrete instructions and
pieces of code that we already know how they execute (by induction), combined
by \<open>@\<close> and \<open>#\<close>. Backward jumps are not supported.
The details should be skipped on a first reading.

If we have just executed the first instruction of the program, drop it:\<close>

lemma exec_Cons_1 [intro]:
  "P \<turnstile> (0,s,stk) \<rightarrow>* (j,t,stk') \<Longrightarrow>
  instr#P \<turnstile> (1,s,stk) \<rightarrow>* (1+j,t,stk')"
by (drule exec_appendL[where P'="[instr]"]) simp

lemma exec_appendL_if[intro]:
  fixes i i' j :: int
  shows
  "size P' <= i
   \<Longrightarrow> P \<turnstile> (i - size P',s,stk) \<rightarrow>* (j,s',stk')
   \<Longrightarrow> i' = size P' + j
   \<Longrightarrow> P' @ P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')"
by (drule exec_appendL[where P'=P']) simp

text\<open>Split the execution of a compound program up into the execution of its
parts:\<close>

lemma exec_append_trans[intro]:
  fixes i' i'' j'' :: int
  shows
"P \<turnstile> (0,s,stk) \<rightarrow>* (i',s',stk') \<Longrightarrow>
 size P \<le> i' \<Longrightarrow>
 P' \<turnstile>  (i' - size P,s',stk') \<rightarrow>* (i'',s'',stk'') \<Longrightarrow>
 j'' = size P + i''
 \<Longrightarrow>
 P @ P' \<turnstile> (0,s,stk) \<rightarrow>* (j'',s'',stk'')"
by(metis star_trans[OF exec_appendR exec_appendL_if])


declare Let_def[simp]


subsection "Compilation"

fun acomp :: "aexp \<Rightarrow> instr list" where
"acomp (N n) = [LOADI n]" |
"acomp (V x) = [LOAD x]" |
"acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"

lemma acomp_correct[intro]:
  "acomp a \<turnstile> (0,s,stk) \<rightarrow>* (size(acomp a),s,aval a s#stk)"
by (induction a arbitrary: stk) fastforce+

fun bcomp :: "bexp \<Rightarrow> bool \<Rightarrow> int \<Rightarrow> instr list" where
"bcomp (Bc v) f n = (if v=f then [JMP n] else [])" |
"bcomp (Not b) f n = bcomp b (\<not>f) n" |
"bcomp (And b1 b2) f n =
 (let cb2 = bcomp b2 f n;
        m = if f then size cb2 else (size cb2)+n;
      cb1 = bcomp b1 False m
  in cb1 @ cb2)" |
"bcomp (Less a1 a2) f n =
 acomp a1 @ acomp a2 @ (if f then [JMPLESS n] else [JMPGE n])"

value
  "bcomp (And (Less (V ''x'') (V ''y'')) (Not(Less (V ''u'') (V ''v''))))
     False 3"

lemma bcomp_correct[intro]:
  fixes n :: int
  shows
  "0 \<le> n \<Longrightarrow>
  bcomp b f n \<turnstile>
 (0,s,stk)  \<rightarrow>*  (size(bcomp b f n) + (if f = bval b s then n else 0),s,stk)"
proof(induction b arbitrary: f n)
  case Not
  from Not(1)[where f="~f"] Not(2) show ?case by fastforce
next
  case (And b1 b2)
  from And(1)[of "if f then size(bcomp b2 f n) else size(bcomp b2 f n) + n" 
                 "False"] 
       And(2)[of n f] And(3) 
  show ?case by fastforce
qed fastforce+

fun ccomp :: "com \<Rightarrow> instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c\<^sub>1;;c\<^sub>2) = ccomp c\<^sub>1 @ ccomp c\<^sub>2" |
"ccomp (IF b THEN c\<^sub>1 ELSE c\<^sub>2) =
  (let cc\<^sub>1 = ccomp c\<^sub>1; cc\<^sub>2 = ccomp c\<^sub>2; cb = bcomp b False (size cc\<^sub>1 + 1)
   in cb @ cc\<^sub>1 @ JMP (size cc\<^sub>2) # cc\<^sub>2)" |
"ccomp (WHILE b DO c) =
 (let cc = ccomp c; cb = bcomp b False (size cc + 1)
  in cb @ cc @ [JMP (-(size cb + size cc + 1))])"


value "ccomp
 (IF Less (V ''u'') (N 1) THEN ''u'' ::= Plus (V ''u'') (N 1)
  ELSE ''v'' ::= V ''u'')"

value "ccomp (WHILE Less (V ''u'') (N 1) DO (''u'' ::= Plus (V ''u'') (N 1)))"


subsection "Preservation of semantics"

lemma ccomp_bigstep:
  "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)"
proof(induction arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastforce simp:fun_upd_def cong: if_cong)
next
  case (Seq c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp c1"  let ?cc2 = "ccomp c2"
  have "?cc1 @ ?cc2 \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cc1,s2,stk)"
    using Seq.IH(1) by fastforce
  moreover
  have "?cc1 @ ?cc2 \<turnstile> (size ?cc1,s2,stk) \<rightarrow>* (size(?cc1 @ ?cc2),s3,stk)"
    using Seq.IH(2) by fastforce
  ultimately show ?case by simp (blast intro: star_trans)
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b False (size ?cc + 1)"
  let ?cw = "ccomp(WHILE b DO c)"
  have "?cw \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cb,s1,stk)"
    using \<open>bval b s1\<close> by fastforce
  moreover
  have "?cw \<turnstile> (size ?cb,s1,stk) \<rightarrow>* (size ?cb + size ?cc,s2,stk)"
    using WhileTrue.IH(1) by fastforce
  moreover
  have "?cw \<turnstile> (size ?cb + size ?cc,s2,stk) \<rightarrow>* (0,s2,stk)"
    by fastforce
  moreover
  have "?cw \<turnstile> (0,s2,stk) \<rightarrow>* (size ?cw,s3,stk)" by(rule WhileTrue.IH(2))
  ultimately show ?case by(blast intro: star_trans)
qed fastforce+

end
