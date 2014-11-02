(* Author: Tobias Nipkow *)

section "Live Variable Analysis"

theory Live imports Vars Big_Step
begin

subsection "Liveness Analysis"

fun L :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"L SKIP X = X" |
"L (x ::= a) X = vars a \<union> (X - {x})" |
"L (c\<^sub>1;; c\<^sub>2) X = L c\<^sub>1 (L c\<^sub>2 X)" |
"L (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = vars b \<union> L c\<^sub>1 X \<union> L c\<^sub>2 X" |
"L (WHILE b DO c) X = vars b \<union> X \<union> L c X"

value "show (L (''y'' ::= V ''z'';; ''x'' ::= Plus (V ''y'') (V ''z'')) {''x''})"

value "show (L (WHILE Less (V ''x'') (V ''x'') DO ''y'' ::= V ''z'') {''x''})"

fun "kill" :: "com \<Rightarrow> vname set" where
"kill SKIP = {}" |
"kill (x ::= a) = {x}" |
"kill (c\<^sub>1;; c\<^sub>2) = kill c\<^sub>1 \<union> kill c\<^sub>2" |
"kill (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = kill c\<^sub>1 \<inter> kill c\<^sub>2" |
"kill (WHILE b DO c) = {}"

fun gen :: "com \<Rightarrow> vname set" where
"gen SKIP = {}" |
"gen (x ::= a) = vars a" |
"gen (c\<^sub>1;; c\<^sub>2) = gen c\<^sub>1 \<union> (gen c\<^sub>2 - kill c\<^sub>1)" |
"gen (IF b THEN c\<^sub>1 ELSE c\<^sub>2) = vars b \<union> gen c\<^sub>1 \<union> gen c\<^sub>2" |
"gen (WHILE b DO c) = vars b \<union> gen c"

lemma L_gen_kill: "L c X = gen c \<union> (X - kill c)"
by(induct c arbitrary:X) auto

lemma L_While_pfp: "L c (L (WHILE b DO c) X) \<subseteq> L (WHILE b DO c) X"
by(auto simp add:L_gen_kill)

lemma L_While_lpfp:
  "vars b \<union> X \<union> L c P \<subseteq> P \<Longrightarrow> L (WHILE b DO c) X \<subseteq> P"
by(simp add: L_gen_kill)

lemma L_While_vars: "vars b \<subseteq> L (WHILE b DO c) X"
by auto

lemma L_While_X: "X \<subseteq> L (WHILE b DO c) X"
by auto

text{* Disable L WHILE equation and reason only with L WHILE constraints *}
declare L.simps(5)[simp del]

subsection "Correctness"

theorem L_correct:
  "(c,s) \<Rightarrow> s'  \<Longrightarrow> s = t on L c X \<Longrightarrow>
  \<exists> t'. (c,t) \<Rightarrow> t' & s' = t' on X"
proof (induction arbitrary: X t rule: big_step_induct)
  case Skip then show ?case by auto
next
  case Assign then show ?case
    by (auto simp: ball_Un)
next
  case (Seq c1 s1 s2 c2 s3 X t1)
  from Seq.IH(1) Seq.prems obtain t2 where
    t12: "(c1, t1) \<Rightarrow> t2" and s2t2: "s2 = t2 on L c2 X"
    by simp blast
  from Seq.IH(2)[OF s2t2] obtain t3 where
    t23: "(c2, t2) \<Rightarrow> t3" and s3t3: "s3 = t3 on X"
    by auto
  show ?case using t12 t23 s3t3 by auto
next
  case (IfTrue b s c1 s' c2)
  hence "s = t on vars b" "s = t on L c1 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfTrue(1) have "bval b t" by simp
  from IfTrue.IH[OF `s = t on L c1 X`] obtain t' where
    "(c1, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using `bval b t` by auto
next
  case (IfFalse b s c2 s' c1)
  hence "s = t on vars b" "s = t on L c2 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfFalse(1) have "~bval b t" by simp
  from IfFalse.IH[OF `s = t on L c2 X`] obtain t' where
    "(c2, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using `~bval b t` by auto
next
  case (WhileFalse b s c)
  hence "~ bval b t"
    by (metis L_While_vars bval_eq_if_eq_on_vars set_mp)
  thus ?case by(metis WhileFalse.prems L_While_X big_step.WhileFalse set_mp)
next
  case (WhileTrue b s1 c s2 s3 X t1)
  let ?w = "WHILE b DO c"
  from `bval b s1` WhileTrue.prems have "bval b t1"
    by (metis L_While_vars bval_eq_if_eq_on_vars set_mp)
  have "s1 = t1 on L c (L ?w X)" using L_While_pfp WhileTrue.prems
    by (blast)
  from WhileTrue.IH(1)[OF this] obtain t2 where
    "(c, t1) \<Rightarrow> t2" "s2 = t2 on L ?w X" by auto
  from WhileTrue.IH(2)[OF this(2)] obtain t3 where "(?w,t2) \<Rightarrow> t3" "s3 = t3 on X"
    by auto
  with `bval b t1` `(c, t1) \<Rightarrow> t2` show ?case by auto
qed


subsection "Program Optimization"

text{* Burying assignments to dead variables: *}
fun bury :: "com \<Rightarrow> vname set \<Rightarrow> com" where
"bury SKIP X = SKIP" |
"bury (x ::= a) X = (if x \<in> X then x ::= a else SKIP)" |
"bury (c\<^sub>1;; c\<^sub>2) X = (bury c\<^sub>1 (L c\<^sub>2 X);; bury c\<^sub>2 X)" |
"bury (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = IF b THEN bury c\<^sub>1 X ELSE bury c\<^sub>2 X" |
"bury (WHILE b DO c) X = WHILE b DO bury c (L (WHILE b DO c) X)"

text{* We could prove the analogous lemma to @{thm[source]L_correct}, and the
proof would be very similar. However, we phrase it as a semantics
preservation property: *}

theorem bury_correct:
  "(c,s) \<Rightarrow> s'  \<Longrightarrow> s = t on L c X \<Longrightarrow>
  \<exists> t'. (bury c X,t) \<Rightarrow> t' & s' = t' on X"
proof (induction arbitrary: X t rule: big_step_induct)
  case Skip then show ?case by auto
next
  case Assign then show ?case
    by (auto simp: ball_Un)
next
  case (Seq c1 s1 s2 c2 s3 X t1)
  from Seq.IH(1) Seq.prems obtain t2 where
    t12: "(bury c1 (L c2 X), t1) \<Rightarrow> t2" and s2t2: "s2 = t2 on L c2 X"
    by simp blast
  from Seq.IH(2)[OF s2t2] obtain t3 where
    t23: "(bury c2 X, t2) \<Rightarrow> t3" and s3t3: "s3 = t3 on X"
    by auto
  show ?case using t12 t23 s3t3 by auto
next
  case (IfTrue b s c1 s' c2)
  hence "s = t on vars b" "s = t on L c1 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfTrue(1) have "bval b t" by simp
  from IfTrue.IH[OF `s = t on L c1 X`] obtain t' where
    "(bury c1 X, t) \<Rightarrow> t'" "s' =t' on X" by auto
  thus ?case using `bval b t` by auto
next
  case (IfFalse b s c2 s' c1)
  hence "s = t on vars b" "s = t on L c2 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfFalse(1) have "~bval b t" by simp
  from IfFalse.IH[OF `s = t on L c2 X`] obtain t' where
    "(bury c2 X, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using `~bval b t` by auto
next
  case (WhileFalse b s c)
  hence "~ bval b t" by (metis L_While_vars bval_eq_if_eq_on_vars set_mp)
  thus ?case
    by simp (metis L_While_X WhileFalse.prems big_step.WhileFalse set_mp)
next
  case (WhileTrue b s1 c s2 s3 X t1)
  let ?w = "WHILE b DO c"
  from `bval b s1` WhileTrue.prems have "bval b t1"
    by (metis L_While_vars bval_eq_if_eq_on_vars set_mp)
  have "s1 = t1 on L c (L ?w X)"
    using L_While_pfp WhileTrue.prems by blast
  from WhileTrue.IH(1)[OF this] obtain t2 where
    "(bury c (L ?w X), t1) \<Rightarrow> t2" "s2 = t2 on L ?w X" by auto
  from WhileTrue.IH(2)[OF this(2)] obtain t3
    where "(bury ?w X,t2) \<Rightarrow> t3" "s3 = t3 on X"
    by auto
  with `bval b t1` `(bury c (L ?w X), t1) \<Rightarrow> t2` show ?case by auto
qed

corollary final_bury_correct: "(c,s) \<Rightarrow> s' \<Longrightarrow> (bury c UNIV,s) \<Rightarrow> s'"
using bury_correct[of c s s' UNIV]
by (auto simp: fun_eq_iff[symmetric])

text{* Now the opposite direction. *}

lemma SKIP_bury[simp]:
  "SKIP = bury c X \<longleftrightarrow> c = SKIP | (EX x a. c = x::=a & x \<notin> X)"
by (cases c) auto

lemma Assign_bury[simp]: "x::=a = bury c X \<longleftrightarrow> c = x::=a & x : X"
by (cases c) auto

lemma Seq_bury[simp]: "bc\<^sub>1;;bc\<^sub>2 = bury c X \<longleftrightarrow>
  (EX c\<^sub>1 c\<^sub>2. c = c\<^sub>1;;c\<^sub>2 & bc\<^sub>2 = bury c\<^sub>2 X & bc\<^sub>1 = bury c\<^sub>1 (L c\<^sub>2 X))"
by (cases c) auto

lemma If_bury[simp]: "IF b THEN bc1 ELSE bc2 = bury c X \<longleftrightarrow>
  (EX c1 c2. c = IF b THEN c1 ELSE c2 &
     bc1 = bury c1 X & bc2 = bury c2 X)"
by (cases c) auto

lemma While_bury[simp]: "WHILE b DO bc' = bury c X \<longleftrightarrow>
  (EX c'. c = WHILE b DO c' & bc' = bury c' (L (WHILE b DO c') X))"
by (cases c) auto

theorem bury_correct2:
  "(bury c X,s) \<Rightarrow> s'  \<Longrightarrow> s = t on L c X \<Longrightarrow>
  \<exists> t'. (c,t) \<Rightarrow> t' & s' = t' on X"
proof (induction "bury c X" s s' arbitrary: c X t rule: big_step_induct)
  case Skip then show ?case by auto
next
  case Assign then show ?case
    by (auto simp: ball_Un)
next
  case (Seq bc1 s1 s2 bc2 s3 c X t1)
  then obtain c1 c2 where c: "c = c1;;c2"
    and bc2: "bc2 = bury c2 X" and bc1: "bc1 = bury c1 (L c2 X)" by auto
  note IH = Seq.hyps(2,4)
  from IH(1)[OF bc1, of t1] Seq.prems c obtain t2 where
    t12: "(c1, t1) \<Rightarrow> t2" and s2t2: "s2 = t2 on L c2 X" by auto
  from IH(2)[OF bc2 s2t2] obtain t3 where
    t23: "(c2, t2) \<Rightarrow> t3" and s3t3: "s3 = t3 on X"
    by auto
  show ?case using c t12 t23 s3t3 by auto
next
  case (IfTrue b s bc1 s' bc2)
  then obtain c1 c2 where c: "c = IF b THEN c1 ELSE c2"
    and bc1: "bc1 = bury c1 X" and bc2: "bc2 = bury c2 X" by auto
  have "s = t on vars b" "s = t on L c1 X" using IfTrue.prems c by auto
  from bval_eq_if_eq_on_vars[OF this(1)] IfTrue(1) have "bval b t" by simp
  note IH = IfTrue.hyps(3)
  from IH[OF bc1 `s = t on L c1 X`] obtain t' where
    "(c1, t) \<Rightarrow> t'" "s' =t' on X" by auto
  thus ?case using c `bval b t` by auto
next
  case (IfFalse b s bc2 s' bc1)
  then obtain c1 c2 where c: "c = IF b THEN c1 ELSE c2"
    and bc1: "bc1 = bury c1 X" and bc2: "bc2 = bury c2 X" by auto
  have "s = t on vars b" "s = t on L c2 X" using IfFalse.prems c by auto
  from bval_eq_if_eq_on_vars[OF this(1)] IfFalse(1) have "~bval b t" by simp
  note IH = IfFalse.hyps(3)
  from IH[OF bc2 `s = t on L c2 X`] obtain t' where
    "(c2, t) \<Rightarrow> t'" "s' =t' on X" by auto
  thus ?case using c `~bval b t` by auto
next
  case (WhileFalse b s c)
  hence "~ bval b t"
    by auto (metis L_While_vars bval_eq_if_eq_on_vars set_rev_mp)
  thus ?case using WhileFalse
    by auto (metis L_While_X big_step.WhileFalse set_mp)
next
  case (WhileTrue b s1 bc' s2 s3 w X t1)
  then obtain c' where w: "w = WHILE b DO c'"
    and bc': "bc' = bury c' (L (WHILE b DO c') X)" by auto
  from `bval b s1` WhileTrue.prems w have "bval b t1"
    by auto (metis L_While_vars bval_eq_if_eq_on_vars set_mp)
  note IH = WhileTrue.hyps(3,5)
  have "s1 = t1 on L c' (L w X)"
    using L_While_pfp WhileTrue.prems w by blast
  with IH(1)[OF bc', of t1] w obtain t2 where
    "(c', t1) \<Rightarrow> t2" "s2 = t2 on L w X" by auto
  from IH(2)[OF WhileTrue.hyps(6), of t2] w this(2) obtain t3
    where "(w,t2) \<Rightarrow> t3" "s3 = t3 on X"
    by auto
  with `bval b t1` `(c', t1) \<Rightarrow> t2` w show ?case by auto
qed

corollary final_bury_correct2: "(bury c UNIV,s) \<Rightarrow> s' \<Longrightarrow> (c,s) \<Rightarrow> s'"
using bury_correct2[of c UNIV]
by (auto simp: fun_eq_iff[symmetric])

corollary bury_sim: "bury c UNIV \<sim> c"
by(metis final_bury_correct final_bury_correct2)

end
