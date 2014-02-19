theory Fold imports Sem_Equiv Vars begin

subsection "Simple folding of arithmetic expressions"

type_synonym
  tab = "vname \<Rightarrow> val option"

fun afold :: "aexp \<Rightarrow> tab \<Rightarrow> aexp" where
"afold (N n) _ = N n" |
"afold (V x) t = (case t x of None \<Rightarrow> V x | Some k \<Rightarrow> N k)" |
"afold (Plus e1 e2) t = (case (afold e1 t, afold e2 t) of
  (N n1, N n2) \<Rightarrow> N(n1+n2) | (e1',e2') \<Rightarrow> Plus e1' e2')"

definition "approx t s \<longleftrightarrow> (ALL x k. t x = Some k \<longrightarrow> s x = k)"

theorem aval_afold[simp]:
assumes "approx t s"
shows "aval (afold a t) s = aval a s"
  using assms
  by (induct a) (auto simp: approx_def split: aexp.split option.split)

theorem aval_afold_N:
assumes "approx t s"
shows "afold a t = N n \<Longrightarrow> aval a s = n"
  by (metis assms aval.simps(1) aval_afold)

definition
  "merge t1 t2 = (\<lambda>m. if t1 m = t2 m then t1 m else None)"

primrec "defs" :: "com \<Rightarrow> tab \<Rightarrow> tab" where
"defs SKIP t = t" |
"defs (x ::= a) t =
  (case afold a t of N k \<Rightarrow> t(x \<mapsto> k) | _ \<Rightarrow> t(x:=None))" |
"defs (c1;;c2) t = (defs c2 o defs c1) t" |
"defs (IF b THEN c1 ELSE c2) t = merge (defs c1 t) (defs c2 t)" |
"defs (WHILE b DO c) t = t |` (-lvars c)"

primrec fold where
"fold SKIP _ = SKIP" |
"fold (x ::= a) t = (x ::= (afold a t))" |
"fold (c1;;c2) t = (fold c1 t;; fold c2 (defs c1 t))" |
"fold (IF b THEN c1 ELSE c2) t = IF b THEN fold c1 t ELSE fold c2 t" |
"fold (WHILE b DO c) t = WHILE b DO fold c (t |` (-lvars c))"

lemma approx_merge:
  "approx t1 s \<or> approx t2 s \<Longrightarrow> approx (merge t1 t2) s"
  by (fastforce simp: merge_def approx_def)

lemma approx_map_le:
  "approx t2 s \<Longrightarrow> t1 \<subseteq>\<^sub>m t2 \<Longrightarrow> approx t1 s"
  by (clarsimp simp: approx_def map_le_def dom_def)

lemma restrict_map_le [intro!, simp]: "t |` S \<subseteq>\<^sub>m t"
  by (clarsimp simp: restrict_map_def map_le_def)

lemma merge_restrict:
  assumes "t1 |` S = t |` S"
  assumes "t2 |` S = t |` S"
  shows "merge t1 t2 |` S = t |` S"
proof -
  from assms
  have "\<forall>x. (t1 |` S) x = (t |` S) x"
   and "\<forall>x. (t2 |` S) x = (t |` S) x" by auto
  thus ?thesis
    by (auto simp: merge_def restrict_map_def
             split: if_splits)
qed


lemma defs_restrict:
  "defs c t |` (- lvars c) = t |` (- lvars c)"
proof (induction c arbitrary: t)
  case (Seq c1 c2)
  hence "defs c1 t |` (- lvars c1) = t |` (- lvars c1)"
    by simp
  hence "defs c1 t |` (- lvars c1) |` (-lvars c2) =
         t |` (- lvars c1) |` (-lvars c2)" by simp
  moreover
  from Seq
  have "defs c2 (defs c1 t) |` (- lvars c2) =
        defs c1 t |` (- lvars c2)"
    by simp
  hence "defs c2 (defs c1 t) |` (- lvars c2) |` (- lvars c1) =
         defs c1 t |` (- lvars c2) |` (- lvars c1)"
    by simp
  ultimately
  show ?case by (clarsimp simp: Int_commute)
next
  case (If b c1 c2)
  hence "defs c1 t |` (- lvars c1) = t |` (- lvars c1)" by simp
  hence "defs c1 t |` (- lvars c1) |` (-lvars c2) =
         t |` (- lvars c1) |` (-lvars c2)" by simp
  moreover
  from If
  have "defs c2 t |` (- lvars c2) = t |` (- lvars c2)" by simp
  hence "defs c2 t |` (- lvars c2) |` (-lvars c1) =
         t |` (- lvars c2) |` (-lvars c1)" by simp
  ultimately
  show ?case by (auto simp: Int_commute intro: merge_restrict)
qed (auto split: aexp.split)


lemma big_step_pres_approx:
  "(c,s) \<Rightarrow> s' \<Longrightarrow> approx t s \<Longrightarrow> approx (defs c t) s'"
proof (induction arbitrary: t rule: big_step_induct)
  case Skip thus ?case by simp
next
  case Assign
  thus ?case
    by (clarsimp simp: aval_afold_N approx_def split: aexp.split)
next
  case (Seq c1 s1 s2 c2 s3)
  have "approx (defs c1 t) s2" by (rule Seq.IH(1)[OF Seq.prems])
  hence "approx (defs c2 (defs c1 t)) s3" by (rule Seq.IH(2))
  thus ?case by simp
next
  case (IfTrue b s c1 s')
  hence "approx (defs c1 t) s'" by simp
  thus ?case by (simp add: approx_merge)
next
  case (IfFalse b s c2 s')
  hence "approx (defs c2 t) s'" by simp
  thus ?case by (simp add: approx_merge)
next
  case WhileFalse
  thus ?case by (simp add: approx_def restrict_map_def)
next
  case (WhileTrue b s1 c s2 s3)
  hence "approx (defs c t) s2" by simp
  with WhileTrue
  have "approx (defs c t |` (-lvars c)) s3" by simp
  thus ?case by (simp add: defs_restrict)
qed


lemma big_step_pres_approx_restrict:
  "(c,s) \<Rightarrow> s' \<Longrightarrow> approx (t |` (-lvars c)) s \<Longrightarrow> approx (t |` (-lvars c)) s'"
proof (induction arbitrary: t rule: big_step_induct)
  case Assign
  thus ?case by (clarsimp simp: approx_def)
next
  case (Seq c1 s1 s2 c2 s3)
  hence "approx (t |` (-lvars c2) |` (-lvars c1)) s1"
    by (simp add: Int_commute)
  hence "approx (t |` (-lvars c2) |` (-lvars c1)) s2"
    by (rule Seq)
  hence "approx (t |` (-lvars c1) |` (-lvars c2)) s2"
    by (simp add: Int_commute)
  hence "approx (t |` (-lvars c1) |` (-lvars c2)) s3"
    by (rule Seq)
  thus ?case by simp
next
  case (IfTrue b s c1 s' c2)
  hence "approx (t |` (-lvars c2) |` (-lvars c1)) s"
    by (simp add: Int_commute)
  hence "approx (t |` (-lvars c2) |` (-lvars c1)) s'"
    by (rule IfTrue)
  thus ?case by (simp add: Int_commute)
next
  case (IfFalse b s c2 s' c1)
  hence "approx (t |` (-lvars c1) |` (-lvars c2)) s"
    by simp
  hence "approx (t |` (-lvars c1) |` (-lvars c2)) s'"
    by (rule IfFalse)
  thus ?case by simp
qed auto


declare assign_simp [simp]

lemma approx_eq:
  "approx t \<Turnstile> c \<sim> fold c t"
proof (induction c arbitrary: t)
  case SKIP show ?case by simp
next
  case Assign
  show ?case by (simp add: equiv_up_to_def)
next
  case Seq
  thus ?case by (auto intro!: equiv_up_to_seq big_step_pres_approx)
next
  case If
  thus ?case by (auto intro!: equiv_up_to_if_weak)
next
  case (While b c)
  hence "approx (t |` (- lvars c)) \<Turnstile>
         WHILE b DO c \<sim> WHILE b DO fold c (t |` (- lvars c))"
    by (auto intro: equiv_up_to_while_weak big_step_pres_approx_restrict)
  thus ?case
    by (auto intro: equiv_up_to_weaken approx_map_le)
qed


lemma approx_empty [simp]:
  "approx empty = (\<lambda>_. True)"
  by (auto simp: approx_def)


theorem constant_folding_equiv:
  "fold c empty \<sim> c"
  using approx_eq [of empty c]
  by (simp add: equiv_up_to_True sim_sym)


end
