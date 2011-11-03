theory Comp_Rev
imports Compiler
begin

section {* Compiler Correctness, 2nd direction *}

subsection {* Definitions *}

text {* Execution in @{term n} steps for simpler induction *}
primrec 
  exec_n :: "instr list \<Rightarrow> config \<Rightarrow> nat \<Rightarrow> config \<Rightarrow> bool" 
  ("_/ \<turnstile> (_ \<rightarrow>^_/ _)" [65,0,1000,55] 55)
where 
  "P \<turnstile> c \<rightarrow>^0 c' = (c'=c)" |
  "P \<turnstile> c \<rightarrow>^(Suc n) c'' = (\<exists>c'. (P \<turnstile> c \<rightarrow> c') \<and> P \<turnstile> c' \<rightarrow>^n c'')"

text {* The possible successor pc's of an instruction at position @{term n} *}
definition
  "isuccs i n \<equiv> case i of 
     JMP j \<Rightarrow> {n + 1 + j}
   | JMPLESS j \<Rightarrow> {n + 1 + j, n + 1}
   | JMPGE j \<Rightarrow> {n + 1 + j, n + 1}
   | _ \<Rightarrow> {n +1}"

text {* The possible successors pc's of an instruction list *}
definition
  "succs P n = {s. \<exists>i. 0 \<le> i \<and> i < isize P \<and> s \<in> isuccs (P!!i) (n+i)}" 

text {* Possible exit pc's of a program *}
definition
  "exits P = succs P 0 - {0..< isize P}"

  
subsection {* Basic properties of @{term exec_n} *}

lemma exec_n_exec:
  "P \<turnstile> c \<rightarrow>^n c' \<Longrightarrow> P \<turnstile> c \<rightarrow>* c'"
  by (induct n arbitrary: c) auto

lemma exec_0 [intro!]: "P \<turnstile> c \<rightarrow>^0 c" by simp

lemma exec_Suc:
  "\<lbrakk> P \<turnstile> c \<rightarrow> c'; P \<turnstile> c' \<rightarrow>^n c'' \<rbrakk> \<Longrightarrow> P \<turnstile> c \<rightarrow>^(Suc n) c''" 
  by (fastforce simp del: split_paired_Ex)

lemma exec_exec_n:
  "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> \<exists>n. P \<turnstile> c \<rightarrow>^n c'"
  by (induct rule: exec.induct) (auto intro: exec_Suc)
    
lemma exec_eq_exec_n:
  "(P \<turnstile> c \<rightarrow>* c') = (\<exists>n. P \<turnstile> c \<rightarrow>^n c')"
  by (blast intro: exec_exec_n exec_n_exec)

lemma exec_n_Nil [simp]:
  "[] \<turnstile> c \<rightarrow>^k c' = (c' = c \<and> k = 0)"
  by (induct k) auto

lemma exec1_exec_n [intro!]:
  "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P \<turnstile> c \<rightarrow>^1 c'"
  by (cases c') simp


subsection {* Concrete symbolic execution steps *}

lemma exec_n_step:
  "n \<noteq> n' \<Longrightarrow> 
  P \<turnstile> (n,stk,s) \<rightarrow>^k (n',stk',s') = 
  (\<exists>c. P \<turnstile> (n,stk,s) \<rightarrow> c \<and> P \<turnstile> c \<rightarrow>^(k - 1) (n',stk',s') \<and> 0 < k)"
  by (cases k) auto

lemma exec1_end:
  "isize P <= fst c \<Longrightarrow> \<not> P \<turnstile> c \<rightarrow> c'"
  by auto

lemma exec_n_end:
  "isize P <= n \<Longrightarrow> 
  P \<turnstile> (n,s,stk) \<rightarrow>^k (n',s',stk') = (n' = n \<and> stk'=stk \<and> s'=s \<and> k =0)"
  by (cases k) (auto simp: exec1_end)

lemmas exec_n_simps = exec_n_step exec_n_end


subsection {* Basic properties of @{term succs} *}

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
  let ?isuccs = "\<lambda>p P n i. 0 \<le> i \<and> i < isize P \<and> p \<in> isuccs (P!!i) (n+i)"
  { fix p assume "p \<in> succs (x#xs) n"
    then obtain i where isuccs: "?isuccs p (x#xs) n i"
      unfolding succs_def by auto     
    have "p \<in> ?x \<union> ?xs" 
    proof cases
      assume "i = 0" with isuccs show ?thesis by simp
    next
      assume "i \<noteq> 0" 
      with isuccs 
      have "?isuccs p xs (1+n) (i - 1)" by auto
      hence "p \<in> ?xs" unfolding succs_def by blast
      thus ?thesis .. 
    qed
  } 
  thus "succs (x#xs) n \<subseteq> ?x \<union> ?xs" ..
  
  { fix p assume "p \<in> ?x \<or> p \<in> ?xs"
    hence "p \<in> succs (x#xs) n"
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
  }  
  thus "?x \<union> ?xs \<subseteq> succs (x#xs) n" by blast
qed

lemma succs_iexec1:
  assumes "P!!i \<turnstile>i (i,s,stk) \<rightarrow> c'" "0 \<le> i" "i < isize P"
  shows "fst c' \<in> succs P 0"
  using assms by (auto elim!: iexec1.cases simp: succs_def isuccs_def)

lemma succs_shift:
  "(p - n \<in> succs P 0) = (p \<in> succs P n)" 
  by (fastforce simp: succs_def isuccs_def split: instr.split)
  
lemma inj_op_plus [simp]:
  "inj (op + (i::int))"
  by (metis add_minus_cancel inj_on_inverseI)

lemma succs_set_shift [simp]:
  "op + i ` succs xs 0 = succs xs i"
  by (force simp: succs_shift [where n=i, symmetric] intro: set_eqI)

lemma succs_append [simp]:
  "succs (xs @ ys) n = succs xs n \<union> succs ys (n + isize xs)"
  by (induct xs arbitrary: n) (auto simp: succs_Cons algebra_simps)


lemma exits_append [simp]:
  "exits (xs @ ys) = exits xs \<union> (op + (isize xs)) ` exits ys - 
                     {0..<isize xs + isize ys}" 
  by (auto simp: exits_def image_set_diff)
  
lemma exits_single:
  "exits [x] = isuccs x 0 - {0}"
  by (auto simp: exits_def succs_def)
  
lemma exits_Cons:
  "exits (x # xs) = (isuccs x 0 - {0}) \<union> (op + 1) ` exits xs - 
                     {0..<1 + isize xs}" 
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
  "succs (acomp a) n = {n + 1 .. n + isize (acomp a)}"
  by (induct a arbitrary: n) auto

lemma acomp_size:
  "1 \<le> isize (acomp a)"
  by (induct a) auto

lemma acomp_exits [simp]:
  "exits (acomp a) = {isize (acomp a)}"
  by (auto simp: exits_def acomp_size)

lemma bcomp_succs:
  "0 \<le> i \<Longrightarrow>
  succs (bcomp b c i) n \<subseteq> {n .. n + isize (bcomp b c i)}
                           \<union> {n + i + isize (bcomp b c i)}" 
proof (induction b arbitrary: c i n)
  case (And b1 b2)
  from And.prems
  show ?case 
    by (cases c)
       (auto dest: And.IH(1) [THEN subsetD, rotated] 
                   And.IH(2) [THEN subsetD, rotated])
qed auto

lemmas bcomp_succsD [dest!] = bcomp_succs [THEN subsetD, rotated]

lemma bcomp_exits:
  "0 \<le> i \<Longrightarrow>
  exits (bcomp b c i) \<subseteq> {isize (bcomp b c i), i + isize (bcomp b c i)}" 
  by (auto simp: exits_def)
  
lemma bcomp_exitsD [dest!]:
  "p \<in> exits (bcomp b c i) \<Longrightarrow> 0 \<le> i \<Longrightarrow> 
  p = isize (bcomp b c i) \<or> p = i + isize (bcomp b c i)"
  using bcomp_exits by auto

lemma ccomp_succs:
  "succs (ccomp c) n \<subseteq> {n..n + isize (ccomp c)}"
proof (induction c arbitrary: n)
  case SKIP thus ?case by simp
next
  case Assign thus ?case by simp
next
  case (Semi c1 c2)
  from Semi.prems
  show ?case 
    by (fastforce dest: Semi.IH [THEN subsetD])
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
  "exits (ccomp c) \<subseteq> {isize (ccomp c)}"
  using ccomp_succs [of c 0] by (auto simp: exits_def)

lemma ccomp_exitsD [dest!]:
  "p \<in> exits (ccomp c) \<Longrightarrow> p = isize (ccomp c)"
  using ccomp_exits by auto


subsection {* Splitting up machine executions *}

lemma exec1_split:
  "P @ c @ P' \<turnstile> (isize P + i, s) \<rightarrow> (j,s') \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < isize c \<Longrightarrow> 
  c \<turnstile> (i,s) \<rightarrow> (j - isize P, s')"
  by (auto elim!: iexec1.cases)

lemma exec_n_split:
  assumes "P @ c @ P' \<turnstile> (isize P + i, s) \<rightarrow>^n (j, s')"
          "0 \<le> i" "i < isize c" 
          "j \<notin> {isize P ..< isize P + isize c}"
  shows "\<exists>s'' i' k m. 
                   c \<turnstile> (i, s) \<rightarrow>^k (i', s'') \<and>
                   i' \<in> exits c \<and> 
                   P @ c @ P' \<turnstile> (isize P + i', s'') \<rightarrow>^m (j, s') \<and>
                   n = k + m" 
using assms proof (induction n arbitrary: i j s)
  case 0
  thus ?case by simp
next
  case (Suc n)
  have i: "0 \<le> i" "i < isize c" by fact+
  from Suc.prems
  have j: "\<not> (isize P \<le> j \<and> j < isize P + isize c)" by simp
  from Suc.prems 
  obtain i0 s0 where
    step: "P @ c @ P' \<turnstile> (isize P + i, s) \<rightarrow> (i0,s0)" and
    rest: "P @ c @ P' \<turnstile> (i0,s0) \<rightarrow>^n (j, s')"
    by clarsimp

  from step i
  have c: "c \<turnstile> (i,s) \<rightarrow> (i0 - isize P, s0)" by (rule exec1_split)

  have "i0 = isize P + (i0 - isize P) " by simp
  then obtain j0 where j0: "i0 = isize P + j0"  ..

  note split_paired_Ex [simp del]

  { assume "j0 \<in> {0 ..< isize c}"
    with j0 j rest c
    have ?case
      by (fastforce dest!: Suc.IH intro!: exec_Suc)
  } moreover {
    assume "j0 \<notin> {0 ..< isize c}"
    moreover
    from c j0 have "j0 \<in> succs c 0"
      by (auto dest: succs_iexec1)
    ultimately
    have "j0 \<in> exits c" by (simp add: exits_def)
    with c j0 rest
    have ?case by fastforce
  }
  ultimately
  show ?case by cases
qed

lemma exec_n_drop_right:
  assumes "c @ P' \<turnstile> (0, s) \<rightarrow>^n (j, s')" "j \<notin> {0..<isize c}"
  shows "\<exists>s'' i' k m. 
          (if c = [] then s'' = s \<and> i' = 0 \<and> k = 0
           else c \<turnstile> (0, s) \<rightarrow>^k (i', s'') \<and>
           i' \<in> exits c) \<and> 
           c @ P' \<turnstile> (i', s'') \<rightarrow>^m (j, s') \<and>
           n = k + m"
  using assms
  by (cases "c = []")
     (auto dest: exec_n_split [where P="[]", simplified])
  

text {*
  Dropping the left context of a potentially incomplete execution of @{term c}.
*}

lemma exec1_drop_left:
  assumes "P1 @ P2 \<turnstile> (i, s, stk) \<rightarrow> (n, s', stk')" and "isize P1 \<le> i"
  shows "P2 \<turnstile> (i - isize P1, s, stk) \<rightarrow> (n - isize P1, s', stk')"
proof -
  have "i = isize P1 + (i - isize P1)" by simp 
  then obtain i' where "i = isize P1 + i'" ..
  moreover
  have "n = isize P1 + (n - isize P1)" by simp 
  then obtain n' where "n = isize P1 + n'" ..
  ultimately 
  show ?thesis using assms by clarsimp
qed

lemma exec_n_drop_left:
  assumes "P @ P' \<turnstile> (i, s, stk) \<rightarrow>^k (n, s', stk')"
          "isize P \<le> i" "exits P' \<subseteq> {0..}"
  shows "P' \<turnstile> (i - isize P, s, stk) \<rightarrow>^k (n - isize P, s', stk')"
using assms proof (induction k arbitrary: i s stk)
  case 0 thus ?case by simp
next
  case (Suc k)
  from Suc.prems
  obtain i' s'' stk'' where
    step: "P @ P' \<turnstile> (i, s, stk) \<rightarrow> (i', s'', stk'')" and
    rest: "P @ P' \<turnstile> (i', s'', stk'') \<rightarrow>^k (n, s', stk')"
    by auto
  from step `isize P \<le> i`
  have "P' \<turnstile> (i - isize P, s, stk) \<rightarrow> (i' - isize P, s'', stk'')" 
    by (rule exec1_drop_left)
  moreover
  then have "i' - isize P \<in> succs P' 0"
    by (fastforce dest!: succs_iexec1)
  with `exits P' \<subseteq> {0..}`
  have "isize P \<le> i'" by (auto simp: exits_def)
  from rest this `exits P' \<subseteq> {0..}`     
  have "P' \<turnstile> (i' - isize P, s'', stk'') \<rightarrow>^k (n - isize P, s', stk')"
    by (rule Suc.IH)
  ultimately
  show ?case by auto
qed

lemmas exec_n_drop_Cons = 
  exec_n_drop_left [where P="[instr]", simplified, standard]

definition
  "closed P \<longleftrightarrow> exits P \<subseteq> {isize P}" 

lemma ccomp_closed [simp, intro!]: "closed (ccomp c)"
  using ccomp_exits by (auto simp: closed_def)

lemma acomp_closed [simp, intro!]: "closed (acomp c)"
  by (simp add: closed_def)

lemma exec_n_split_full:
  assumes exec: "P @ P' \<turnstile> (0,s,stk) \<rightarrow>^k (j, s', stk')"
  assumes P: "isize P \<le> j" 
  assumes closed: "closed P"
  assumes exits: "exits P' \<subseteq> {0..}"
  shows "\<exists>k1 k2 s'' stk''. P \<turnstile> (0,s,stk) \<rightarrow>^k1 (isize P, s'', stk'') \<and> 
                           P' \<turnstile> (0,s'',stk'') \<rightarrow>^k2 (j - isize P, s', stk')"
proof (cases "P")
  case Nil with exec
  show ?thesis by fastforce
next
  case Cons
  hence "0 < isize P" by simp
  with exec P closed
  obtain k1 k2 s'' stk'' where
    1: "P \<turnstile> (0,s,stk) \<rightarrow>^k1 (isize P, s'', stk'')" and
    2: "P @ P' \<turnstile> (isize P,s'',stk'') \<rightarrow>^k2 (j, s', stk')"
    by (auto dest!: exec_n_split [where P="[]" and i=0, simplified] 
             simp: closed_def)
  moreover
  have "j = isize P + (j - isize P)" by simp
  then obtain j0 where "j = isize P + j0" ..
  ultimately
  show ?thesis using exits
    by (fastforce dest: exec_n_drop_left)
qed


subsection {* Correctness theorem *}

lemma acomp_neq_Nil [simp]:
  "acomp a \<noteq> []"
  by (induct a) auto

lemma acomp_exec_n [dest!]:
  "acomp a \<turnstile> (0,s,stk) \<rightarrow>^n (isize (acomp a),s',stk') \<Longrightarrow> 
  s' = s \<and> stk' = aval a s#stk"
proof (induction a arbitrary: n s' stk stk')
  case (Plus a1 a2)
  let ?sz = "isize (acomp a1) + (isize (acomp a2) + 1)"
  from Plus.prems
  have "acomp a1 @ acomp a2 @ [ADD] \<turnstile> (0,s,stk) \<rightarrow>^n (?sz, s', stk')" 
    by (simp add: algebra_simps)
      
  then obtain n1 s1 stk1 n2 s2 stk2 n3 where 
    "acomp a1 \<turnstile> (0,s,stk) \<rightarrow>^n1 (isize (acomp a1), s1, stk1)"
    "acomp a2 \<turnstile> (0,s1,stk1) \<rightarrow>^n2 (isize (acomp a2), s2, stk2)" 
       "[ADD] \<turnstile> (0,s2,stk2) \<rightarrow>^n3 (1, s', stk')"
    by (auto dest!: exec_n_split_full)

  thus ?case by (fastforce dest: Plus.IH simp: exec_n_simps)
qed (auto simp: exec_n_simps)

lemma bcomp_split:
  assumes "bcomp b c i @ P' \<turnstile> (0, s, stk) \<rightarrow>^n (j, s', stk')" 
          "j \<notin> {0..<isize (bcomp b c i)}" "0 \<le> i"
  shows "\<exists>s'' stk'' i' k m. 
           bcomp b c i \<turnstile> (0, s, stk) \<rightarrow>^k (i', s'', stk'') \<and>
           (i' = isize (bcomp b c i) \<or> i' = i + isize (bcomp b c i)) \<and>
           bcomp b c i @ P' \<turnstile> (i', s'', stk'') \<rightarrow>^m (j, s', stk') \<and>
           n = k + m"
  using assms by (cases "bcomp b c i = []") (fastforce dest!: exec_n_drop_right)+

lemma bcomp_exec_n [dest]:
  assumes "bcomp b c j \<turnstile> (0, s, stk) \<rightarrow>^n (i, s', stk')"
          "isize (bcomp b c j) \<le> i" "0 \<le> j"
  shows "i = isize(bcomp b c j) + (if c = bval b s then j else 0) \<and>
         s' = s \<and> stk' = stk"
using assms proof (induction b arbitrary: c j i n s' stk')
  case Bc thus ?case 
    by (simp split: split_if_asm add: exec_n_simps)
next
  case (Not b) 
  from Not.prems show ?case
    by (fastforce dest!: Not.IH) 
next
  case (And b1 b2)
  
  let ?b2 = "bcomp b2 c j" 
  let ?m  = "if c then isize ?b2 else isize ?b2 + j"
  let ?b1 = "bcomp b1 False ?m" 

  have j: "isize (bcomp (And b1 b2) c j) \<le> i" "0 \<le> j" by fact+
  
  from And.prems
  obtain s'' stk'' i' k m where 
    b1: "?b1 \<turnstile> (0, s, stk) \<rightarrow>^k (i', s'', stk'')"
        "i' = isize ?b1 \<or> i' = ?m + isize ?b1" and
    b2: "?b2 \<turnstile> (i' - isize ?b1, s'', stk'') \<rightarrow>^m (i - isize ?b1, s', stk')"
    by (auto dest!: bcomp_split dest: exec_n_drop_left)
  from b1 j
  have "i' = isize ?b1 + (if \<not>bval b1 s then ?m else 0) \<and> s'' = s \<and> stk'' = stk"
    by (auto dest!: And.IH)
  with b2 j
  show ?case 
    by (fastforce dest!: And.IH simp: exec_n_end split: split_if_asm)
next
  case Less
  thus ?case by (auto dest!: exec_n_split_full simp: exec_n_simps) (* takes time *) 
qed

lemma ccomp_empty [elim!]:
  "ccomp c = [] \<Longrightarrow> (c,s) \<Rightarrow> s"
  by (induct c) auto

declare assign_simp [simp]

lemma ccomp_exec_n:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>^n (isize(ccomp c),t,stk')
  \<Longrightarrow> (c,s) \<Rightarrow> t \<and> stk'=stk"
proof (induction c arbitrary: s t stk stk' n)
  case SKIP
  thus ?case by auto
next
  case (Assign x a)
  thus ?case
    by simp (fastforce dest!: exec_n_split_full simp: exec_n_simps)
next
  case (Semi c1 c2)
  thus ?case by (fastforce dest!: exec_n_split_full)
next
  case (If b c1 c2)
  note If.IH [dest!]

  let ?if = "IF b THEN c1 ELSE c2"
  let ?cs = "ccomp ?if"
  let ?bcomp = "bcomp b False (isize (ccomp c1) + 1)"
  
  from `?cs \<turnstile> (0,s,stk) \<rightarrow>^n (isize ?cs,t,stk')`
  obtain i' k m s'' stk'' where
    cs: "?cs \<turnstile> (i',s'',stk'') \<rightarrow>^m (isize ?cs,t,stk')" and
        "?bcomp \<turnstile> (0,s,stk) \<rightarrow>^k (i', s'', stk'')" 
        "i' = isize ?bcomp \<or> i' = isize ?bcomp + isize (ccomp c1) + 1"
    by (auto dest!: bcomp_split)

  hence i':
    "s''=s" "stk'' = stk" 
    "i' = (if bval b s then isize ?bcomp else isize ?bcomp+isize(ccomp c1)+1)"
    by auto
  
  with cs have cs':
    "ccomp c1@JMP (isize (ccomp c2))#ccomp c2 \<turnstile> 
       (if bval b s then 0 else isize (ccomp c1)+1, s, stk) \<rightarrow>^m
       (1 + isize (ccomp c1) + isize (ccomp c2), t, stk')"
    by (fastforce dest: exec_n_drop_left simp: exits_Cons isuccs_def algebra_simps)
     
  show ?case
  proof (cases "bval b s")
    case True with cs'
    show ?thesis
      by simp
         (fastforce dest: exec_n_drop_right 
                   split: split_if_asm simp: exec_n_simps)
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
    
    { assume "\<not> bval b s"
      with "1.prems"
      have ?case
        by simp
           (fastforce dest!: bcomp_exec_n bcomp_split 
                     simp: exec_n_simps)
    } moreover {
      assume b: "bval b s"
      let ?c0 = "WHILE b DO c"
      let ?cs = "ccomp ?c0"
      let ?bs = "bcomp b False (isize (ccomp c) + 1)"
      let ?jmp = "[JMP (-((isize ?bs + isize (ccomp c) + 1)))]"
      
      from "1.prems" b
      obtain k where
        cs: "?cs \<turnstile> (isize ?bs, s, stk) \<rightarrow>^k (isize ?cs, t, stk')" and
        k:  "k \<le> n"
        by (fastforce dest!: bcomp_split)
      
      have ?case
      proof cases
        assume "ccomp c = []"
        with cs k
        obtain m where
          "?cs \<turnstile> (0,s,stk) \<rightarrow>^m (isize (ccomp ?c0), t, stk')"
          "m < n"
          by (auto simp: exec_n_step [where k=k])
        with "1.IH"
        show ?case by blast
      next
        assume "ccomp c \<noteq> []"
        with cs
        obtain m m' s'' stk'' where
          c: "ccomp c \<turnstile> (0, s, stk) \<rightarrow>^m' (isize (ccomp c), s'', stk'')" and 
          rest: "?cs \<turnstile> (isize ?bs + isize (ccomp c), s'', stk'') \<rightarrow>^m 
                       (isize ?cs, t, stk')" and
          m: "k = m + m'"
          by (auto dest: exec_n_split [where i=0, simplified])
        from c
        have "(c,s) \<Rightarrow> s''" and stk: "stk'' = stk"
          by (auto dest!: While.IH)
        moreover
        from rest m k stk
        obtain k' where
          "?cs \<turnstile> (0, s'', stk) \<rightarrow>^k' (isize ?cs, t, stk')"
          "k' < n"
          by (auto simp: exec_n_step [where k=m])
        with "1.IH"
        have "(?c0, s'') \<Rightarrow> t \<and> stk' = stk" by blast
        ultimately
        show ?case using b by blast
      qed
    }
    ultimately show ?case by cases
  qed
qed

theorem ccomp_exec:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (isize(ccomp c),t,stk') \<Longrightarrow> (c,s) \<Rightarrow> t"
  by (auto dest: exec_exec_n ccomp_exec_n)

corollary ccomp_sound:
  "ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (isize(ccomp c),t,stk)  \<longleftrightarrow>  (c,s) \<Rightarrow> t"
  by (blast intro!: ccomp_exec ccomp_bigstep)

end
