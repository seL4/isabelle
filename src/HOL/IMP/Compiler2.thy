(* Author: Gerwin Klein *)

section \<open>Compiler Correctness, Reverse Direction\<close>

theory Compiler2
imports Compiler
begin

text \<open>
The preservation of the source code semantics is already shown in the 
parent theory \<open>Compiler\<close>. This here shows the second direction.
\<close>

subsection \<open>Definitions\<close>

text \<open>Execution in \<^term>\<open>n\<close> steps for simpler induction\<close>
primrec 
  exec_n :: "instr list \<Rightarrow> config \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> bool" 
  (\<open>_/ \<turnstile> (_ \<rightarrow>^_/ _)\<close> [65,0,1000,55] 55)
where 
  "P \<turnstile> c \<rightarrow>^0 c' = (c'=c)" |
  "P \<turnstile> c \<rightarrow>^(Suc n) c'' = (\<exists>c'. (P \<turnstile> c \<rightarrow> c') \<and> P \<turnstile> c' \<rightarrow>^n c'')"

text \<open>The possible successor PCs of an instruction at position \<^term>\<open>n\<close>\<close>
text_raw\<open>\snip{isuccsdef}{0}{1}{%\<close>
definition isuccs :: "instr \<Rightarrow> int \<Rightarrow> int set" where
"isuccs i n = (case i of
  JMP j \<Rightarrow> {n + 1 + j} |
  JMPLESS j \<Rightarrow> {n + 1 + j, n + 1} |
  JMPGE j \<Rightarrow> {n + 1 + j, n + 1} |
  _ \<Rightarrow> {n +1})"
text_raw\<open>}%endsnip\<close>

text \<open>The possible successors PCs of an instruction list\<close>
definition succs :: "instr list \<Rightarrow> int \<Rightarrow> int set" where
"succs P n = {s. \<exists>i::int. 0 \<le> i \<and> i < size P \<and> s \<in> isuccs (P!!i) (n+i)}" 

text \<open>Possible exit PCs of a program\<close>
definition exits :: "instr list \<Rightarrow> int set" where
"exits P = succs P 0 - {0..< size P}"

  
subsection \<open>Basic properties of \<^term>\<open>exec_n\<close>\<close>

lemma exec_n_exec:
  "P \<turnstile> c \<rightarrow>^n c' \<Longrightarrow> P \<turnstile> c \<rightarrow>* c'"
  by (induct n arbitrary: c) (auto intro: star.step)

lemma exec_0 [intro!]: "P \<turnstile> c \<rightarrow>^0 c" by simp

lemma exec_Suc:
  "\<lbrakk> P \<turnstile> c \<rightarrow> c'; P \<turnstile> c' \<rightarrow>^n c'' \<rbrakk> \<Longrightarrow> P \<turnstile> c \<rightarrow>^(Suc n) c''" 
  by (fastforce simp del: split_paired_Ex)

lemma exec_exec_n:
  "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> \<exists>n. P \<turnstile> c \<rightarrow>^n c'"
  by (induct rule: star.induct) (auto intro: exec_Suc)
    
lemma exec_eq_exec_n:
  "(P \<turnstile> c \<rightarrow>* c') = (\<exists>n. P \<turnstile> c \<rightarrow>^n c')"
  by (blast intro: exec_exec_n exec_n_exec)

lemma exec_n_Nil [simp]:
  "[] \<turnstile> c \<rightarrow>^k c' = (c' = c \<and> k = 0)"
  by (induct k) (auto simp: exec1_def)

lemma exec1_exec_n [intro!]:
  "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P \<turnstile> c \<rightarrow>^1 c'"
  by (cases c') simp


subsection \<open>Concrete symbolic execution steps\<close>

lemma exec_n_step:
  "n \<noteq> n' \<Longrightarrow> 
  P \<turnstile> (n,stk,s) \<rightarrow>^k (n',stk',s') = 
  (\<exists>c. P \<turnstile> (n,stk,s) \<rightarrow> c \<and> P \<turnstile> c \<rightarrow>^(k - 1) (n',stk',s') \<and> 0 < k)"
  by (cases k) auto

lemma exec1_end:
  "size P <= fst c \<Longrightarrow> \<not> P \<turnstile> c \<rightarrow> c'"
  by (auto simp: exec1_def)

lemma exec_n_end:
  "size P <= (n::int) \<Longrightarrow> 
  P \<turnstile> (n,s,stk) \<rightarrow>^k (n',s',stk') = (n' = n \<and> stk'=stk \<and> s'=s \<and> k =0)"
  by (cases k) (auto simp: exec1_end)

lemmas exec_n_simps = exec_n_step exec_n_end


subsection \<open>Basic properties of \<^term>\<open>succs\<close>\<close>

lemma succs_simps [simp]: 
  "succs [ADD] n = {n + 1}"
  "succs [LOADI v] n = {n + 1}"
  "succs [LOAD x] n = {n + 1}"
  "succs [STORE x] n = {n + 1}"
  "succs [JMP i] n = {n + 1 + i}"
  "succs [JMPGE i] n = {n + 1 + i, n + 1}"
  "succs [JMPLESS i] n = {n + 1 + i, n + 1}"
  by (auto simp: succs_def isuccs_def)

lemma succs_empty [iff]: "succs [] n = {}"
  by (simp add: succs_def)

lemma succs_Cons:
  "succs (x#xs) n = isuccs x n \<union> succs xs (1+n)" (is "_ = ?x \<union> ?xs")
proof 
  let ?isuccs = "\<lambda>p P n i::int. 0 \<le> i \<and> i < size P \<and> p \<in> isuccs (P!!i) (n+i)"
  have "p \<in> ?x \<union> ?xs" if assm: "p \<in> succs (x#xs) n" for p
  proof -
    from assm obtain i::int where isuccs: "?isuccs p (x#xs) n i"
      unfolding succs_def by auto     
    show ?thesis
    proof cases
      assume "i = 0" with isuccs show ?thesis by simp
    next
      assume "i \<noteq> 0" 
      with isuccs 
      have "?isuccs p xs (1+n) (i - 1)" by auto
      hence "p \<in> ?xs" unfolding succs_def by blast
      thus ?thesis .. 
    qed
  qed
  thus "succs (x#xs) n \<subseteq> ?x \<union> ?xs" ..

  have "p \<in> succs (x#xs) n" if assm: "p \<in> ?x \<or> p \<in> ?xs" for p
  proof -
    from assm show ?thesis
    proof
      assume "p \<in> ?x" thus ?thesis by (fastforce simp: succs_def)
    next
      assume "p \<in> ?xs"
      then obtain i where "?isuccs p xs (1+n) i"
        unfolding succs_def by auto
      hence "?isuccs p (x#xs) n (1+i)"
        by (simp add: algebra_simps)
      thus ?thesis unfolding succs_def by blast
    qed
  qed
  thus "?x \<union> ?xs \<subseteq> succs (x#xs) n" by blast
qed

lemma succs_iexec1:
  assumes "c' = iexec (P!!i) (i,s,stk)" "0 \<le> i" "i < size P"
  shows "fst c' \<in> succs P 0"
  using assms by (auto simp: succs_def isuccs_def split: instr.split)

lemma succs_shift:
  "(p - n \<in> succs P 0) = (p \<in> succs P n)" 
  by (fastforce simp: succs_def isuccs_def split: instr.split)
  
lemma inj_op_plus [simp]:
  "inj ((+) (i::int))"
  by (metis add_minus_cancel inj_on_inverseI)

lemma succs_set_shift [simp]:
  "(+) i ` succs xs 0 = succs xs i"
  by (force simp: succs_shift [where n=i, symmetric] intro: set_eqI)

lemma succs_append [simp]:
  "succs (xs @ ys) n = succs xs n \<union> succs ys (n + size xs)"
  by (induct xs arbitrary: n) (auto simp: succs_Cons algebra_simps)


lemma exits_append [simp]:
  "exits (xs @ ys) = exits xs \<union> ((+) (size xs)) ` exits ys - 
                     {0..<size xs + size ys}" 
  by (auto simp: exits_def image_set_diff)
  
lemma exits_single:
  "exits [x] = isuccs x 0 - {0}"
  by (auto simp: exits_def succs_def)
  
lemma exits_Cons:
  "exits (x # xs) = (isuccs x 0 - {0}) \<union> ((+) 1) ` exits xs - 
                     {0..<1 + size xs}" 
  using exits_append [of "[x]" xs]
  by (simp add: exits_single)

lemma exits_empty [iff]: "exits [] = {}" by (simp add: exits_def)

lemma exits_simps [simp]:
  "exits [ADD] = {1}"
  "exits [LOADI v] = {1}"
  "exits [LOAD x] = {1}"
  "exits [STORE x] = {1}"
  "i \<noteq> -1 \<Longrightarrow> exits [JMP i] = {1 + i}"
  "i \<noteq> -1 \<Longrightarrow> exits [JMPGE i] = {1 + i, 1}"
  "i \<noteq> -1 \<Longrightarrow> exits [JMPLESS i] = {1 + i, 1}"
  by (auto simp: exits_def)

lemma acomp_succs [simp]:
  "succs (acomp a) n = {n + 1 .. n + size (acomp a)}"
  by (induct a arbitrary: n) auto
 
lemma acomp_exits [simp]:
  "exits (acomp a) = {size (acomp a)}"
proof -
  have "Suc 0 \<le> length (acomp a)" 
    by (induct a) auto
  then show ?thesis
    by (auto simp add: exits_def)
qed

lemma bcomp_succs:
  "0 \<le> i \<Longrightarrow>
  succs (bcomp b f i) n \<subseteq> {n .. n + size (bcomp b f i)}
                           \<union> {n + i + size (bcomp b f i)}" 
proof (induction b arbitrary: f i n)
  case (And b1 b2)
  from And.prems
  show ?case 
    by (cases f)
       (auto dest: And.IH(1) [THEN subsetD, rotated] 
                   And.IH(2) [THEN subsetD, rotated])
qed auto

lemmas bcomp_succsD [dest!] = bcomp_succs [THEN subsetD, rotated]

lemma bcomp_exits:
  fixes i :: int
  shows
  "0 \<le> i \<Longrightarrow>
  exits (bcomp b f i) \<subseteq> {size (bcomp b f i), i + size (bcomp b f i)}" 
  by (auto simp: exits_def)
  
lemma bcomp_exitsD [dest!]:
  "p \<in> exits (bcomp b f i) \<Longrightarrow> 0 \<le> i \<Longrightarrow> 
  p = size (bcomp b f i) \<or> p = i + size (bcomp b f i)"
  using bcomp_exits by auto

lemma ccomp_succs:
  "succs (ccomp c) n \<subseteq> {n..n + size (ccomp c)}"
proof (induction c arbitrary: n)
  case SKIP thus ?case by simp
next
  case Assign thus ?case by simp
next
  case (Seq c1 c2)
  from Seq.prems
  show ?case 
    by (fastforce dest: Seq.IH [THEN subsetD])
next
  case (If b c1 c2)
  from If.prems
  show ?case
    by (auto dest!: If.IH [THEN subsetD] simp: isuccs_def succs_Cons)
next
  case (While b c)
  from While.prems
  show ?case by (auto dest!: While.IH [THEN subsetD])
qed

lemma ccomp_exits:
  "exits (ccomp c) \<subseteq> {size (ccomp c)}"
  using ccomp_succs [of c 0] by (auto simp: exits_def)

lemma ccomp_exitsD [dest!]:
  "p \<in> exits (ccomp c) \<Longrightarrow> p = size (ccomp c)"
  using ccomp_exits by auto


subsection \<open>Splitting up machine executions\<close>

lemma exec1_split:
  fixes i j :: int
  shows
  "P @ c @ P' \<turnstile> (size P + i, s) \<rightarrow> (j,s') \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < size c \<Longrightarrow> 
  c \<turnstile> (i,s) \<rightarrow> (j - size P, s')"
  by (auto split: instr.splits simp: exec1_def)

lemma exec_n_split:
  fixes i j :: int
  assumes "P @ c @ P' \<turnstile> (size P + i, s) \<rightarrow>^n (j, s')"
          "0 \<le> i" "i < size c" 
          "j \<notin> {size P ..< size P + size c}"
  shows "\<exists>s'' (i'::int) k m. 
                   c \<turnstile> (i, s) \<rightarrow>^k (i', s'') \<and>
                   i' \<in> exits c \<and> 
                   P @ c @ P' \<turnstile> (size P + i', s'') \<rightarrow>^m (j, s') \<and>
                   n = k + m" 
using assms proof (induction n arbitrary: i j s)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have i: "0 \<le> i" "i < size c" by fact+
  from Suc.prems
  have j: "\<not> (size P \<le> j \<and> j < size P + size c)" by simp
  from Suc.prems 
  obtain i0 s0 where
    step: "P @ c @ P' \<turnstile> (size P + i, s) \<rightarrow> (i0,s0)" and
    rest: "P @ c @ P' \<turnstile> (i0,s0) \<rightarrow>^n (j, s')"
    by clarsimp

  from step i
  have c: "c \<turnstile> (i,s) \<rightarrow> (i0 - size P, s0)" by (rule exec1_split)

  have "i0 = size P + (i0 - size P) " by simp
  then obtain j0::int where j0: "i0 = size P + j0"  ..

  note split_paired_Ex [simp del]

  have ?case if assm: "j0 \<in> {0 ..< size c}"
  proof -
    from assm j0 j rest c show ?case
      by (fastforce dest!: Suc.IH intro!: exec_Suc)
  qed
  moreover
  have ?case if assm: "j0 \<notin> {0 ..< size c}"
  proof -
    from c j0 have "j0 \<in> succs c 0"
      by (auto dest: succs_iexec1 simp: exec1_def simp del: iexec.simps)
    with assm have "j0 \<in> exits c" by (simp add: exits_def)
    with c j0 rest show ?case by fastforce
  qed
  ultimately
  show ?case by cases
qed

lemma exec_n_drop_right:
  fixes j :: int
  assumes "c @ P' \<turnstile> (0, s) \<rightarrow>^n (j, s')" "j \<notin> {0..<size c}"
  shows "\<exists>s'' i' k m. 
          (if c = [] then s'' = s \<and> i' = 0 \<and> k = 0
           else c \<turnstile> (0, s) \<rightarrow>^k (i', s'') \<and>
           i' \<in> exits c) \<and> 
           c @ P' \<turnstile> (i', s'') \<rightarrow>^m (j, s') \<and>
           n = k + m"
  using assms
  by (cases "c = []")
     (auto dest: exec_n_split [where P="[]", simplified])
  

text \<open>
  Dropping the left context of a potentially incomplete execution of \<^term>\<open>c\<close>.
\<close>

lemma exec1_drop_left:
  fixes i n :: int
  assumes "P1 @ P2 \<turnstile> (i, s, stk) \<rightarrow> (n, s', stk')" and "size P1 \<le> i"
  shows "P2 \<turnstile> (i - size P1, s, stk) \<rightarrow> (n - size P1, s', stk')"
proof -
  have "i = size P1 + (i - size P1)" by simp 
  then obtain i' :: int where "i = size P1 + i'" ..
  moreover
  have "n = size P1 + (n - size P1)" by simp 
  then obtain n' :: int where "n = size P1 + n'" ..
  ultimately 
  show ?thesis using assms 
    by (clarsimp simp: exec1_def simp del: iexec.simps)
qed

lemma exec_n_drop_left:
  fixes i n :: int
  assumes "P @ P' \<turnstile> (i, s, stk) \<rightarrow>^k (n, s', stk')"
          "size P \<le> i" "exits P' \<subseteq> {0..}"
  shows "P' \<turnstile> (i - size P, s, stk) \<rightarrow>^k (n - size P, s', stk')"
using assms proof (induction k arbitrary: i s stk)
  case 0 thus ?case by simp
next
  case (Suc k)
  from Suc.prems
  obtain i' s'' stk'' where
    step: "P @ P' \<turnstile> (i, s, stk) \<rightarrow> (i', s'', stk'')" and
    rest: "P @ P' \<turnstile> (i', s'', stk'') \<rightarrow>^k (n, s', stk')"
    by auto
  from step \<open>size P \<le> i\<close>
  have *: "P' \<turnstile> (i - size P, s, stk) \<rightarrow> (i' - size P, s'', stk'')" 
    by (rule exec1_drop_left)
  then have "i' - size P \<in> succs P' 0"
    by (fastforce dest!: succs_iexec1 simp: exec1_def simp del: iexec.simps)
  with \<open>exits P' \<subseteq> {0..}\<close>
  have "size P \<le> i'" by (auto simp: exits_def)
  from rest this \<open>exits P' \<subseteq> {0..}\<close>     
  have "P' \<turnstile> (i' - size P, s'', stk'') \<rightarrow>^k (n - size P, s', stk')"
    by (rule Suc.IH)
  with * show ?case by auto
qed

lemmas exec_n_drop_Cons = 
  exec_n_drop_left [where P="[instr]", simplified] for instr

definition
  "closed P \<longleftrightarrow> exits P \<subseteq> {size P}" 

lemma ccomp_closed [simp, intro!]: "closed (ccomp c)"
  using ccomp_exits by (auto simp: closed_def)

lemma acomp_closed [simp, intro!]: "closed (acomp c)"
  by (simp add: closed_def)

lemma exec_n_split_full:
  fixes j :: int
  assumes exec: "P @ P' \<turnstile> (0,s,stk) \<rightarrow>^k (j, s', stk')"
  assumes P: "size P \<le> j" 
  assumes closed: "closed P"
  assumes exits: "exits P' \<subseteq> {0..}"
  shows "\<exists>k1 k2 s'' stk''. P \<turnstile> (0,s,stk) \<rightarrow>^k1 (size P, s'', stk'') \<and> 
                           P' \<turnstile> (0,s'',stk'') \<rightarrow>^k2 (j - size P, s', stk')"
proof (cases "P")
  case Nil with exec
  show ?thesis by fastforce
next
  case Cons
  hence "0 < size P" by simp
  with exec P closed
  obtain k1 k2 s'' stk'' where
    1: "P \<turnstile> (0,s,stk) \<rightarrow>^k1 (size P, s'', stk'')" and
    2: "P @ P' \<turnstile> (size P,s'',stk'') \<rightarrow>^k2 (j, s', stk')"
    by (auto dest!: exec_n_split [where P="[]" and i=0, simplified] 
             simp: closed_def)
  moreover
  have "j = size P + (j - size P)" by simp
  then obtain j0 :: int where "j = size P + j0" ..
  ultimately
  show ?thesis using exits
    by (fastforce dest: exec_n_drop_left)
qed


subsection \<open>Correctness theorem\<close>

lemma acomp_neq_Nil [simp]:
  "acomp a \<noteq> []"
  by (induct a) auto

lemma acomp_exec_n [dest!]:
  "acomp a \<turnstile> (0,s,stk) \<rightarrow>^n (size (acomp a),s',stk') \<Longrightarrow> 
  s' = s \<and> stk' = aval a s#stk"
proof (induction a arbitrary: n s' stk stk')
  case (Plus a1 a2)
  let ?sz = "size (acomp a1) + (size (acomp a2) + 1)"
  from Plus.prems
  have "acomp a1 @ acomp a2 @ [ADD] \<turnstile> (0,s,stk) \<rightarrow>^n (?sz, s', stk')" 
    by (simp add: algebra_simps)
      
  then obtain n1 s1 stk1 n2 s2 stk2 n3 where 
    "acomp a1 \<turnstile> (0,s,stk) \<rightarrow>^n1 (size (acomp a1), s1, stk1)"
    "acomp a2 \<turnstile> (0,s1,stk1) \<rightarrow>^n2 (size (acomp a2), s2, stk2)" 
       "[ADD] \<turnstile> (0,s2,stk2) \<rightarrow>^n3 (1, s', stk')"
    by (auto dest!: exec_n_split_full)

  thus ?case by (fastforce dest: Plus.IH simp: exec_n_simps exec1_def)
qed (auto simp: exec_n_simps exec1_def)

lemma bcomp_split:
  fixes i j :: int
  assumes "bcomp b f i @ P' \<turnstile> (0, s, stk) \<rightarrow>^n (j, s', stk')" 
          "j \<notin> {0..<size (bcomp b f i)}" "0 \<le> i"
  shows "\<exists>s'' stk'' (i'::int) k m. 
           bcomp b f i \<turnstile> (0, s, stk) \<rightarrow>^k (i', s'', stk'') \<and>
           (i' = size (bcomp b f i) \<or> i' = i + size (bcomp b f i)) \<and>
           bcomp b f i @ P' \<turnstile> (i', s'', stk'') \<rightarrow>^m (j, s', stk') \<and>
           n = k + m"
  using assms by (cases "bcomp b f i = []") (fastforce dest!: exec_n_drop_right)+

lemma bcomp_exec_n [dest]:
  fixes i j :: int
  assumes "bcomp b f j \<turnstile> (0, s, stk) \<rightarrow>^n (i, s', stk')"
          "size (bcomp b f j) \<le> i" "0 \<le> j"
  shows "i = size(bcomp b f j) + (if f = bval b s then j else 0) \<and>
         s' = s \<and> stk' = stk"
using assms proof (induction b arbitrary: f j i n s' stk')
  case Bc thus ?case 
    by (simp split: if_split_asm add: exec_n_simps exec1_def)
next
  case (Not b) 
  from Not.prems show ?case
    by (fastforce dest!: Not.IH) 
next
  case (And b1 b2)
  
  let ?b2 = "bcomp b2 f j" 
  let ?m  = "if f then size ?b2 else size ?b2 + j"
  let ?b1 = "bcomp b1 False ?m" 

  have j: "size (bcomp (And b1 b2) f j) \<le> i" "0 \<le> j" by fact+
  
  from And.prems
  obtain s'' stk'' and i'::int and k m where 
    b1: "?b1 \<turnstile> (0, s, stk) \<rightarrow>^k (i', s'', stk'')"
        "i' = size ?b1 \<or> i' = ?m + size ?b1" and
    b2: "?b2 \<turnstile> (i' - size ?b1, s'', stk'') \<rightarrow>^m (i - size ?b1, s', stk')"
    by (auto dest!: bcomp_split dest: exec_n_drop_left)
  from b1 j
  have "i' = size ?b1 + (if \<not>bval b1 s then ?m else 0) \<and> s'' = s \<and> stk'' = stk"
    by (auto dest!: And.IH)
  with b2 j
  show ?case 
    by (fastforce dest!: And.IH simp: exec_n_end split: if_split_asm)
next
  case Less
  thus ?case by (auto dest!: exec_n_split_full simp: exec_n_simps exec1_def) (* takes time *) 
qed

lemma ccomp_empty [elim!]:
  "ccomp c = [] \<Longrightarrow> (c,s) \<Rightarrow> s"
  by (induct c) auto

declare assign_simp [simp]

lemma ccomp_exec_n:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>^n (size(ccomp c),t,stk')
  \<Longrightarrow> (c,s) \<Rightarrow> t \<and> stk'=stk"
proof (induction c arbitrary: s t stk stk' n)
  case SKIP
  thus ?case by auto
next
  case (Assign x a)
  thus ?case
    by simp (fastforce dest!: exec_n_split_full simp: exec_n_simps exec1_def)
next
  case (Seq c1 c2)
  thus ?case by (fastforce dest!: exec_n_split_full)
next
  case (If b c1 c2)
  note If.IH [dest!]

  let ?if = "IF b THEN c1 ELSE c2"
  let ?cs = "ccomp ?if"
  let ?bcomp = "bcomp b False (size (ccomp c1) + 1)"
  
  from \<open>?cs \<turnstile> (0,s,stk) \<rightarrow>^n (size ?cs,t,stk')\<close>
  obtain i' :: int and k m s'' stk'' where
    cs: "?cs \<turnstile> (i',s'',stk'') \<rightarrow>^m (size ?cs,t,stk')" and
        "?bcomp \<turnstile> (0,s,stk) \<rightarrow>^k (i', s'', stk'')" 
        "i' = size ?bcomp \<or> i' = size ?bcomp + size (ccomp c1) + 1"
    by (auto dest!: bcomp_split)

  hence i':
    "s''=s" "stk'' = stk" 
    "i' = (if bval b s then size ?bcomp else size ?bcomp+size(ccomp c1)+1)"
    by auto
  
  with cs have cs':
    "ccomp c1@JMP (size (ccomp c2))#ccomp c2 \<turnstile> 
       (if bval b s then 0 else size (ccomp c1)+1, s, stk) \<rightarrow>^m
       (1 + size (ccomp c1) + size (ccomp c2), t, stk')"
    by (fastforce dest: exec_n_drop_left simp: exits_Cons isuccs_def algebra_simps)
     
  show ?case
  proof (cases "bval b s")
    case True with cs'
    show ?thesis
      by simp
         (fastforce dest: exec_n_drop_right 
                   split: if_split_asm
                   simp: exec_n_simps exec1_def)
  next
    case False with cs'
    show ?thesis
      by (auto dest!: exec_n_drop_Cons exec_n_drop_left 
               simp: exits_Cons isuccs_def)
  qed
next
  case (While b c)

  from While.prems
  show ?case
  proof (induction n arbitrary: s rule: nat_less_induct)
    case (1 n)

    have ?case if assm: "\<not> bval b s"
    proof -
      from assm "1.prems"
      show ?case
        by simp (fastforce dest!: bcomp_split simp: exec_n_simps)
    qed
    moreover
    have ?case if b: "bval b s"
    proof -
      let ?c0 = "WHILE b DO c"
      let ?cs = "ccomp ?c0"
      let ?bs = "bcomp b False (size (ccomp c) + 1)"
      let ?jmp = "[JMP (-((size ?bs + size (ccomp c) + 1)))]"
      
      from "1.prems" b
      obtain k where
        cs: "?cs \<turnstile> (size ?bs, s, stk) \<rightarrow>^k (size ?cs, t, stk')" and
        k:  "k \<le> n"
        by (fastforce dest!: bcomp_split)
      
      show ?case
      proof cases
        assume "ccomp c = []"
        with cs k
        obtain m where
          "?cs \<turnstile> (0,s,stk) \<rightarrow>^m (size (ccomp ?c0), t, stk')"
          "m < n"
          by (auto simp: exec_n_step [where k=k] exec1_def)
        with "1.IH"
        show ?case by blast
      next
        assume "ccomp c \<noteq> []"
        with cs
        obtain m m' s'' stk'' where
          c: "ccomp c \<turnstile> (0, s, stk) \<rightarrow>^m' (size (ccomp c), s'', stk'')" and 
          rest: "?cs \<turnstile> (size ?bs + size (ccomp c), s'', stk'') \<rightarrow>^m 
                       (size ?cs, t, stk')" and
          m: "k = m + m'"
          by (auto dest: exec_n_split [where i=0, simplified])
        from c
        have "(c,s) \<Rightarrow> s''" and stk: "stk'' = stk"
          by (auto dest!: While.IH)
        moreover
        from rest m k stk
        obtain k' where
          "?cs \<turnstile> (0, s'', stk) \<rightarrow>^k' (size ?cs, t, stk')"
          "k' < n"
          by (auto simp: exec_n_step [where k=m] exec1_def)
        with "1.IH"
        have "(?c0, s'') \<Rightarrow> t \<and> stk' = stk" by blast
        ultimately
        show ?case using b by blast
      qed
    qed
    ultimately show ?case by cases
  qed
qed

theorem ccomp_exec:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk') \<Longrightarrow> (c,s) \<Rightarrow> t"
  by (auto dest: exec_exec_n ccomp_exec_n)

corollary ccomp_sound:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)  \<longleftrightarrow>  (c,s) \<Rightarrow> t"
  by (blast intro!: ccomp_exec ccomp_bigstep)

end
