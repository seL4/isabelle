theory Sec_TypingT imports Sec_Type_Expr
begin

subsection "A Termination-Sensitive Syntax Directed System"

inductive sec_type :: "nat \<Rightarrow> com \<Rightarrow> bool" ("(_/ \<turnstile> _)" [0,0] 50) where
Skip:
  "l \<turnstile> SKIP"  |
Assign:
  "\<lbrakk> sec x \<ge> sec_aexp a;  sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile> x ::= a"  |
Seq:
  "l \<turnstile> c\<^isub>1 \<Longrightarrow> l \<turnstile> c\<^isub>2 \<Longrightarrow> l \<turnstile> c\<^isub>1;c\<^isub>2"  |
If:
  "\<lbrakk> max (sec_bexp b) l \<turnstile> c\<^isub>1;  max (sec_bexp b) l \<turnstile> c\<^isub>2 \<rbrakk>
   \<Longrightarrow> l \<turnstile> IF b THEN c\<^isub>1 ELSE c\<^isub>2"  |
While:
  "sec_bexp b = 0 \<Longrightarrow> 0 \<turnstile> c \<Longrightarrow> 0 \<turnstile> WHILE b DO c"

code_pred (expected_modes: i => i => bool) sec_type .

inductive_cases [elim!]:
  "l \<turnstile> x ::= a"  "l \<turnstile> c\<^isub>1;c\<^isub>2"  "l \<turnstile> IF b THEN c\<^isub>1 ELSE c\<^isub>2"  "l \<turnstile> WHILE b DO c"


lemma anti_mono: "l \<turnstile> c \<Longrightarrow> l' \<le> l \<Longrightarrow> l' \<turnstile> c"
apply(induction arbitrary: l' rule: sec_type.induct)
apply (metis sec_type.intros(1))
apply (metis le_trans sec_type.intros(2))
apply (metis sec_type.intros(3))
apply (metis If le_refl sup_mono sup_nat_def)
by (metis While le_0_eq)


lemma confinement: "(c,s) \<Rightarrow> t \<Longrightarrow> l \<turnstile> c \<Longrightarrow> s = t (< l)"
proof(induction rule: big_step_induct)
  case Skip thus ?case by simp
next
  case Assign thus ?case by auto
next
  case Seq thus ?case by auto
next
  case (IfTrue b s c1)
  hence "max (sec_bexp b) l \<turnstile> c1" by auto
  hence "l \<turnstile> c1" by (metis le_maxI2 anti_mono)
  thus ?case using IfTrue.IH by metis
next
  case (IfFalse b s c2)
  hence "max (sec_bexp b) l \<turnstile> c2" by auto
  hence "l \<turnstile> c2" by (metis le_maxI2 anti_mono)
  thus ?case using IfFalse.IH by metis
next
  case WhileFalse thus ?case by auto
next
  case (WhileTrue b s1 c)
  hence "l \<turnstile> c" by auto
  thus ?case using WhileTrue by metis
qed

lemma termi_if_non0: "l \<turnstile> c \<Longrightarrow> l \<noteq> 0 \<Longrightarrow> \<exists> t. (c,s) \<Rightarrow> t"
apply(induction arbitrary: s rule: sec_type.induct)
apply (metis big_step.Skip)
apply (metis big_step.Assign)
apply (metis big_step.Seq)
apply (metis IfFalse IfTrue le0 le_antisym le_maxI2)
apply simp
done

theorem noninterference: "(c,s) \<Rightarrow> s' \<Longrightarrow> 0 \<turnstile> c \<Longrightarrow>  s = t (\<le> l)
  \<Longrightarrow> \<exists> t'. (c,t) \<Rightarrow> t' \<and> s' = t' (\<le> l)"
proof(induction arbitrary: t rule: big_step_induct)
  case Skip thus ?case by auto
next
  case (Assign x a s)
  have "sec x >= sec_aexp a" using `0 \<turnstile> x ::= a` by auto
  have "(x ::= a,t) \<Rightarrow> t(x := aval a t)" by auto
  moreover
  have "s(x := aval a s) = t(x := aval a t) (\<le> l)"
  proof auto
    assume "sec x \<le> l"
    with `sec x \<ge> sec_aexp a` have "sec_aexp a \<le> l" by arith
    thus "aval a s = aval a t"
      by (rule aval_eq_if_eq_le[OF `s = t (\<le> l)`])
  next
    fix y assume "y \<noteq> x" "sec y \<le> l"
    thus "s y = t y" using `s = t (\<le> l)` by simp
  qed
  ultimately show ?case by blast
next
  case Seq thus ?case by blast
next
  case (IfTrue b s c1 s' c2)
  have "sec_bexp b \<turnstile> c1" "sec_bexp b \<turnstile> c2" using IfTrue.prems by auto
  obtain t' where t': "(c1, t) \<Rightarrow> t'" "s' = t' (\<le> l)"
    using IfTrue(3)[OF anti_mono[OF `sec_bexp b \<turnstile> c1`] IfTrue.prems(2)] by blast
  show ?case
  proof cases
    assume "sec_bexp b \<le> l"
    hence "s = t (\<le> sec_bexp b)" using `s = t (\<le> l)` by auto
    hence "bval b t" using `bval b s` by(simp add: bval_eq_if_eq_le)
    thus ?thesis by (metis t' big_step.IfTrue)
  next
    assume "\<not> sec_bexp b \<le> l"
    hence 0: "sec_bexp b \<noteq> 0" by arith
    have 1: "sec_bexp b \<turnstile> IF b THEN c1 ELSE c2"
      by(rule sec_type.intros)(simp_all add: `sec_bexp b \<turnstile> c1` `sec_bexp b \<turnstile> c2`)
    from confinement[OF big_step.IfTrue[OF IfTrue(1,2)] 1] `\<not> sec_bexp b \<le> l`
    have "s = s' (\<le> l)" by auto
    moreover
    from termi_if_non0[OF 1 0, of t] obtain t' where
      "(IF b THEN c1 ELSE c2,t) \<Rightarrow> t'" ..
    moreover
    from confinement[OF this 1] `\<not> sec_bexp b \<le> l`
    have "t = t' (\<le> l)" by auto
    ultimately
    show ?case using `s = t (\<le> l)` by auto
  qed
next
  case (IfFalse b s c2 s' c1)
  have "sec_bexp b \<turnstile> c1" "sec_bexp b \<turnstile> c2" using IfFalse.prems by auto
  obtain t' where t': "(c2, t) \<Rightarrow> t'" "s' = t' (\<le> l)"
    using IfFalse(3)[OF anti_mono[OF `sec_bexp b \<turnstile> c2`] IfFalse.prems(2)] by blast
  show ?case
  proof cases
    assume "sec_bexp b \<le> l"
    hence "s = t (\<le> sec_bexp b)" using `s = t (\<le> l)` by auto
    hence "\<not> bval b t" using `\<not> bval b s` by(simp add: bval_eq_if_eq_le)
    thus ?thesis by (metis t' big_step.IfFalse)
  next
    assume "\<not> sec_bexp b \<le> l"
    hence 0: "sec_bexp b \<noteq> 0" by arith
    have 1: "sec_bexp b \<turnstile> IF b THEN c1 ELSE c2"
      by(rule sec_type.intros)(simp_all add: `sec_bexp b \<turnstile> c1` `sec_bexp b \<turnstile> c2`)
    from confinement[OF big_step.IfFalse[OF IfFalse(1,2)] 1] `\<not> sec_bexp b \<le> l`
    have "s = s' (\<le> l)" by auto
    moreover
    from termi_if_non0[OF 1 0, of t] obtain t' where
      "(IF b THEN c1 ELSE c2,t) \<Rightarrow> t'" ..
    moreover
    from confinement[OF this 1] `\<not> sec_bexp b \<le> l`
    have "t = t' (\<le> l)" by auto
    ultimately
    show ?case using `s = t (\<le> l)` by auto
  qed
next
  case (WhileFalse b s c)
  hence [simp]: "sec_bexp b = 0" by auto
  have "s = t (\<le> sec_bexp b)" using `s = t (\<le> l)` by auto
  hence "\<not> bval b t" using `\<not> bval b s` by (metis bval_eq_if_eq_le le_refl)
  with WhileFalse.prems(2) show ?case by auto
next
  case (WhileTrue b s c s'' s')
  let ?w = "WHILE b DO c"
  from `0 \<turnstile> ?w` have [simp]: "sec_bexp b = 0" by auto
  have "0 \<turnstile> c" using WhileTrue.prems(1) by auto
  from WhileTrue.IH(1)[OF this WhileTrue.prems(2)]
  obtain t'' where "(c,t) \<Rightarrow> t''" and "s'' = t'' (\<le>l)" by blast
  from WhileTrue.IH(2)[OF `0 \<turnstile> ?w` this(2)]
  obtain t' where "(?w,t'') \<Rightarrow> t'" and "s' = t' (\<le>l)" by blast
  from `bval b s` have "bval b t"
    using bval_eq_if_eq_le[OF `s = t (\<le>l)`] by auto
  show ?case
    using big_step.WhileTrue[OF `bval b t` `(c,t) \<Rightarrow> t''` `(?w,t'') \<Rightarrow> t'`]
    by (metis `s' = t' (\<le> l)`)
qed

subsection "The Standard Termination-Sensitive System"

text{* The predicate @{prop"l \<turnstile> c"} is nicely intuitive and executable. The
standard formulation, however, is slightly different, replacing the maximum
computation by an antimonotonicity rule. We introduce the standard system now
and show the equivalence with our formulation. *}

inductive sec_type' :: "nat \<Rightarrow> com \<Rightarrow> bool" ("(_/ \<turnstile>'' _)" [0,0] 50) where
Skip':
  "l \<turnstile>' SKIP"  |
Assign':
  "\<lbrakk> sec x \<ge> sec_aexp a;  sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile>' x ::= a"  |
Seq':
  "l \<turnstile>' c\<^isub>1 \<Longrightarrow> l \<turnstile>' c\<^isub>2 \<Longrightarrow> l \<turnstile>' c\<^isub>1;c\<^isub>2"  |
If':
  "\<lbrakk> sec_bexp b \<le> l;  l \<turnstile>' c\<^isub>1;  l \<turnstile>' c\<^isub>2 \<rbrakk> \<Longrightarrow> l \<turnstile>' IF b THEN c\<^isub>1 ELSE c\<^isub>2"  |
While':
  "\<lbrakk> sec_bexp b = 0;  0 \<turnstile>' c \<rbrakk> \<Longrightarrow> 0 \<turnstile>' WHILE b DO c"  |
anti_mono':
  "\<lbrakk> l \<turnstile>' c;  l' \<le> l \<rbrakk> \<Longrightarrow> l' \<turnstile>' c"

lemma "l \<turnstile> c \<Longrightarrow> l \<turnstile>' c"
apply(induction rule: sec_type.induct)
apply (metis Skip')
apply (metis Assign')
apply (metis Seq')
apply (metis min_max.inf_sup_ord(3) min_max.sup_absorb2 nat_le_linear If' anti_mono')
by (metis While')


lemma "l \<turnstile>' c \<Longrightarrow> l \<turnstile> c"
apply(induction rule: sec_type'.induct)
apply (metis Skip)
apply (metis Assign)
apply (metis Seq)
apply (metis min_max.sup_absorb2 If)
apply (metis While)
by (metis anti_mono)

end
