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



subsection {* More ambitious folding including boolean expressions *}


fun bfold :: "bexp \<Rightarrow> tab \<Rightarrow> bexp" where
"bfold (Less a1 a2) t = less (afold a1 t) (afold a2 t)" |
"bfold (And b1 b2) t = and (bfold b1 t) (bfold b2 t)" |
"bfold (Not b) t = not(bfold b t)" |
"bfold (Bc bc) _ = Bc bc"

theorem bval_bfold [simp]:
  assumes "approx t s"
  shows "bval (bfold b t) s = bval b s"
  using assms by (induct b) auto

lemma not_Bc [simp]: "not (Bc v) = Bc (\<not>v)"
  by (cases v) auto

lemma not_Bc_eq [simp]: "(not b = Bc v) = (b = Bc (\<not>v))"
  by (cases b) auto

lemma and_Bc_eq:
  "(and a b = Bc v) =
   (a = Bc False \<and> \<not>v  \<or>  b = Bc False \<and> \<not>v \<or>
    (\<exists>v1 v2. a = Bc v1 \<and> b = Bc v2 \<and> v = v1 \<and> v2))"
  by (rule and.induct) auto

lemma less_Bc_eq [simp]:
  "(less a b = Bc v) = (\<exists>n1 n2. a = N n1 \<and> b = N n2 \<and> v = (n1 < n2))"
  by (rule less.induct) auto

theorem bval_bfold_Bc:
assumes "approx t s"
shows "bfold b t = Bc v \<Longrightarrow> bval b s = v"
  using assms
  by (induct b arbitrary: v)
     (auto simp: approx_def and_Bc_eq aval_afold_N
           split: bexp.splits bool.splits)


primrec "bdefs" :: "com \<Rightarrow> tab \<Rightarrow> tab" where
"bdefs SKIP t = t" |
"bdefs (x ::= a) t =
  (case afold a t of N k \<Rightarrow> t(x \<mapsto> k) | _ \<Rightarrow> t(x:=None))" |
"bdefs (c1;;c2) t = (bdefs c2 o bdefs c1) t" |
"bdefs (IF b THEN c1 ELSE c2) t = (case bfold b t of
    Bc True \<Rightarrow> bdefs c1 t
  | Bc False \<Rightarrow> bdefs c2 t
  | _ \<Rightarrow> merge (bdefs c1 t) (bdefs c2 t))" |
"bdefs (WHILE b DO c) t = t |` (-lvars c)"


primrec fold' where
"fold' SKIP _ = SKIP" |
"fold' (x ::= a) t = (x ::= (afold a t))" |
"fold' (c1;;c2) t = (fold' c1 t;; fold' c2 (bdefs c1 t))" |
"fold' (IF b THEN c1 ELSE c2) t = (case bfold b t of
    Bc True \<Rightarrow> fold' c1 t
  | Bc False \<Rightarrow> fold' c2 t
  | _ \<Rightarrow> IF bfold b t THEN fold' c1 t ELSE fold' c2 t)" |
"fold' (WHILE b DO c) t = (case bfold b t of
    Bc False \<Rightarrow> SKIP
  | _ \<Rightarrow> WHILE bfold b (t |` (-lvars c)) DO fold' c (t |` (-lvars c)))"


lemma bdefs_restrict:
  "bdefs c t |` (- lvars c) = t |` (- lvars c)"
proof (induction c arbitrary: t)
  case (Seq c1 c2)
  hence "bdefs c1 t |` (- lvars c1) = t |` (- lvars c1)"
    by simp
  hence "bdefs c1 t |` (- lvars c1) |` (-lvars c2) =
         t |` (- lvars c1) |` (-lvars c2)" by simp
  moreover
  from Seq
  have "bdefs c2 (bdefs c1 t) |` (- lvars c2) =
        bdefs c1 t |` (- lvars c2)"
    by simp
  hence "bdefs c2 (bdefs c1 t) |` (- lvars c2) |` (- lvars c1) =
         bdefs c1 t |` (- lvars c2) |` (- lvars c1)"
    by simp
  ultimately
  show ?case by (clarsimp simp: Int_commute)
next
  case (If b c1 c2)
  hence "bdefs c1 t |` (- lvars c1) = t |` (- lvars c1)" by simp
  hence "bdefs c1 t |` (- lvars c1) |` (-lvars c2) =
         t |` (- lvars c1) |` (-lvars c2)" by simp
  moreover
  from If
  have "bdefs c2 t |` (- lvars c2) = t |` (- lvars c2)" by simp
  hence "bdefs c2 t |` (- lvars c2) |` (-lvars c1) =
         t |` (- lvars c2) |` (-lvars c1)" by simp
  ultimately
  show ?case
    by (auto simp: Int_commute intro: merge_restrict
             split: bexp.splits bool.splits)
qed (auto split: aexp.split bexp.split bool.split)


lemma big_step_pres_approx_b:
  "(c,s) \<Rightarrow> s' \<Longrightarrow> approx t s \<Longrightarrow> approx (bdefs c t) s'"
proof (induction arbitrary: t rule: big_step_induct)
  case Skip thus ?case by simp
next
  case Assign
  thus ?case
    by (clarsimp simp: aval_afold_N approx_def split: aexp.split)
next
  case (Seq c1 s1 s2 c2 s3)
  have "approx (bdefs c1 t) s2" by (rule Seq.IH(1)[OF Seq.prems])
  hence "approx (bdefs c2 (bdefs c1 t)) s3" by (rule Seq.IH(2))
  thus ?case by simp
next
  case (IfTrue b s c1 s')
  hence "approx (bdefs c1 t) s'" by simp
  thus ?case using `bval b s` `approx t s`
    by (clarsimp simp: approx_merge bval_bfold_Bc
                 split: bexp.splits bool.splits)
next
  case (IfFalse b s c2 s')
  hence "approx (bdefs c2 t) s'" by simp
  thus ?case using `\<not>bval b s` `approx t s`
    by (clarsimp simp: approx_merge bval_bfold_Bc
                 split: bexp.splits bool.splits)
next
  case WhileFalse
  thus ?case
    by (clarsimp simp: bval_bfold_Bc approx_def restrict_map_def
                 split: bexp.splits bool.splits)
next
  case (WhileTrue b s1 c s2 s3)
  hence "approx (bdefs c t) s2" by simp
  with WhileTrue
  have "approx (bdefs c t |` (- lvars c)) s3"
    by simp
  thus ?case
    by (simp add: bdefs_restrict)
qed

lemma fold'_equiv:
  "approx t \<Turnstile> c \<sim> fold' c t"
proof (induction c arbitrary: t)
  case SKIP show ?case by simp
next
  case Assign
  thus ?case by (simp add: equiv_up_to_def)
next
  case Seq
  thus ?case by (auto intro!: equiv_up_to_seq big_step_pres_approx_b)
next
  case (If b c1 c2)
  hence "approx t \<Turnstile> IF b THEN c1 ELSE c2 \<sim>
                   IF bfold b t THEN fold' c1 t ELSE fold' c2 t"
    by (auto intro: equiv_up_to_if_weak simp: bequiv_up_to_def)
  thus ?case using If
    by (fastforce simp: bval_bfold_Bc split: bexp.splits bool.splits
                 intro: equiv_up_to_trans)
  next
  case (While b c)
  hence "approx (t |` (- lvars c)) \<Turnstile>
                   WHILE b DO c \<sim>
                   WHILE bfold b (t |` (- lvars c))
                      DO fold' c (t |` (- lvars c))" (is "_ \<Turnstile> ?W \<sim> ?W'")
    by (auto intro: equiv_up_to_while_weak big_step_pres_approx_restrict
             simp: bequiv_up_to_def)
  hence "approx t \<Turnstile> ?W \<sim> ?W'"
    by (auto intro: equiv_up_to_weaken approx_map_le)
  thus ?case
    by (auto split: bexp.splits bool.splits
             intro: equiv_up_to_while_False
             simp: bval_bfold_Bc)
qed


theorem constant_folding_equiv':
  "fold' c empty \<sim> c"
  using fold'_equiv [of empty c]
  by (simp add: equiv_up_to_True sim_sym)


end
