subsection "Termination-Sensitive Systems"

theory Sec_TypingT imports Sec_Type_Expr
begin

subsubsection "A Syntax Directed System"

inductive sec_type :: "nat \<Rightarrow> com \<Rightarrow> bool" (\<open>(_/ \<turnstile> _)\<close> [0,0] 50) where
Skip:
  "l \<turnstile> SKIP"  |
Assign:
  "\<lbrakk> sec x \<ge> sec a;  sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile> x ::= a"  |
Seq:
  "l \<turnstile> c\<^sub>1 \<Longrightarrow> l \<turnstile> c\<^sub>2 \<Longrightarrow> l \<turnstile> c\<^sub>1;;c\<^sub>2"  |
If:
  "\<lbrakk> max (sec b) l \<turnstile> c\<^sub>1;  max (sec b) l \<turnstile> c\<^sub>2 \<rbrakk>
   \<Longrightarrow> l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"  |
While:
  "sec b = 0 \<Longrightarrow> 0 \<turnstile> c \<Longrightarrow> 0 \<turnstile> WHILE b DO c"

code_pred (expected_modes: i => i => bool) sec_type .

inductive_cases [elim!]:
  "l \<turnstile> x ::= a"  "l \<turnstile> c\<^sub>1;;c\<^sub>2"  "l \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"  "l \<turnstile> WHILE b DO c"


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
  hence "max (sec b) l \<turnstile> c1" by auto
  hence "l \<turnstile> c1" by (metis max.cobounded2 anti_mono)
  thus ?case using IfTrue.IH by metis
next
  case (IfFalse b s c2)
  hence "max (sec b) l \<turnstile> c2" by auto
  hence "l \<turnstile> c2" by (metis max.cobounded2 anti_mono)
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
apply (metis IfFalse IfTrue le0 le_antisym max.cobounded2)
apply simp
done

theorem noninterference: "(c,s) \<Rightarrow> s' \<Longrightarrow> 0 \<turnstile> c \<Longrightarrow>  s = t (\<le> l)
  \<Longrightarrow> \<exists> t'. (c,t) \<Rightarrow> t' \<and> s' = t' (\<le> l)"
proof(induction arbitrary: t rule: big_step_induct)
  case Skip thus ?case by auto
next
  case (Assign x a s)
  have "sec x >= sec a" using \<open>0 \<turnstile> x ::= a\<close> by auto
  have "(x ::= a,t) \<Rightarrow> t(x := aval a t)" by auto
  moreover
  have "s(x := aval a s) = t(x := aval a t) (\<le> l)"
  proof auto
    assume "sec x \<le> l"
    with \<open>sec x \<ge> sec a\<close> have "sec a \<le> l" by arith
    thus "aval a s = aval a t"
      by (rule aval_eq_if_eq_le[OF \<open>s = t (\<le> l)\<close>])
  next
    fix y assume "y \<noteq> x" "sec y \<le> l"
    thus "s y = t y" using \<open>s = t (\<le> l)\<close> by simp
  qed
  ultimately show ?case by blast
next
  case Seq thus ?case by blast
next
  case (IfTrue b s c1 s' c2)
  have "sec b \<turnstile> c1" "sec b \<turnstile> c2" using \<open>0 \<turnstile> IF b THEN c1 ELSE c2\<close> by auto
  obtain t' where t': "(c1, t) \<Rightarrow> t'" "s' = t' (\<le> l)"
    using IfTrue.IH[OF anti_mono[OF \<open>sec b \<turnstile> c1\<close>] \<open>s = t (\<le> l)\<close>] by blast
  show ?case
  proof cases
    assume "sec b \<le> l"
    hence "s = t (\<le> sec b)" using \<open>s = t (\<le> l)\<close> by auto
    hence "bval b t" using \<open>bval b s\<close> by(simp add: bval_eq_if_eq_le)
    thus ?thesis by (metis t' big_step.IfTrue)
  next
    assume "\<not> sec b \<le> l"
    hence 0: "sec b \<noteq> 0" by arith
    have 1: "sec b \<turnstile> IF b THEN c1 ELSE c2"
      by(rule sec_type.intros)(simp_all add: \<open>sec b \<turnstile> c1\<close> \<open>sec b \<turnstile> c2\<close>)
    from confinement[OF big_step.IfTrue[OF IfTrue(1,2)] 1] \<open>\<not> sec b \<le> l\<close>
    have "s = s' (\<le> l)" by auto
    moreover
    from termi_if_non0[OF 1 0, of t] obtain t' where
      t': "(IF b THEN c1 ELSE c2,t) \<Rightarrow> t'" ..
    moreover
    from confinement[OF t' 1] \<open>\<not> sec b \<le> l\<close>
    have "t = t' (\<le> l)" by auto
    ultimately
    show ?case using \<open>s = t (\<le> l)\<close> by auto
  qed
next
  case (IfFalse b s c2 s' c1)
  have "sec b \<turnstile> c1" "sec b \<turnstile> c2" using \<open>0 \<turnstile> IF b THEN c1 ELSE c2\<close> by auto
  obtain t' where t': "(c2, t) \<Rightarrow> t'" "s' = t' (\<le> l)"
    using IfFalse.IH[OF anti_mono[OF \<open>sec b \<turnstile> c2\<close>] \<open>s = t (\<le> l)\<close>] by blast
  show ?case
  proof cases
    assume "sec b \<le> l"
    hence "s = t (\<le> sec b)" using \<open>s = t (\<le> l)\<close> by auto
    hence "\<not> bval b t" using \<open>\<not> bval b s\<close> by(simp add: bval_eq_if_eq_le)
    thus ?thesis by (metis t' big_step.IfFalse)
  next
    assume "\<not> sec b \<le> l"
    hence 0: "sec b \<noteq> 0" by arith
    have 1: "sec b \<turnstile> IF b THEN c1 ELSE c2"
      by(rule sec_type.intros)(simp_all add: \<open>sec b \<turnstile> c1\<close> \<open>sec b \<turnstile> c2\<close>)
    from confinement[OF big_step.IfFalse[OF IfFalse(1,2)] 1] \<open>\<not> sec b \<le> l\<close>
    have "s = s' (\<le> l)" by auto
    moreover
    from termi_if_non0[OF 1 0, of t] obtain t' where
      t': "(IF b THEN c1 ELSE c2,t) \<Rightarrow> t'" ..
    moreover
    from confinement[OF t' 1] \<open>\<not> sec b \<le> l\<close>
    have "t = t' (\<le> l)" by auto
    ultimately
    show ?case using \<open>s = t (\<le> l)\<close> by auto
  qed
next
  case (WhileFalse b s c)
  hence [simp]: "sec b = 0" by auto
  have "s = t (\<le> sec b)" using \<open>s = t (\<le> l)\<close> by auto
  hence "\<not> bval b t" using \<open>\<not> bval b s\<close> by (metis bval_eq_if_eq_le le_refl)
  with WhileFalse.prems(2) show ?case by auto
next
  case (WhileTrue b s c s'' s')
  let ?w = "WHILE b DO c"
  from \<open>0 \<turnstile> ?w\<close> have [simp]: "sec b = 0" by auto
  have "0 \<turnstile> c" using \<open>0 \<turnstile> WHILE b DO c\<close> by auto
  from WhileTrue.IH(1)[OF this \<open>s = t (\<le> l)\<close>]
  obtain t'' where "(c,t) \<Rightarrow> t''" and "s'' = t'' (\<le>l)" by blast
  from WhileTrue.IH(2)[OF \<open>0 \<turnstile> ?w\<close> this(2)]
  obtain t' where "(?w,t'') \<Rightarrow> t'" and "s' = t' (\<le>l)" by blast
  from \<open>bval b s\<close> have "bval b t"
    using bval_eq_if_eq_le[OF \<open>s = t (\<le>l)\<close>] by auto
  show ?case
    using big_step.WhileTrue[OF \<open>bval b t\<close> \<open>(c,t) \<Rightarrow> t''\<close> \<open>(?w,t'') \<Rightarrow> t'\<close>]
    by (metis \<open>s' = t' (\<le> l)\<close>)
qed

subsubsection "The Standard System"

text\<open>The predicate \<^prop>\<open>l \<turnstile> c\<close> is nicely intuitive and executable. The
standard formulation, however, is slightly different, replacing the maximum
computation by an antimonotonicity rule. We introduce the standard system now
and show the equivalence with our formulation.\<close>

inductive sec_type' :: "nat \<Rightarrow> com \<Rightarrow> bool" (\<open>(_/ \<turnstile>'' _)\<close> [0,0] 50) where
Skip':
  "l \<turnstile>' SKIP"  |
Assign':
  "\<lbrakk> sec x \<ge> sec a;  sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile>' x ::= a"  |
Seq':
  "l \<turnstile>' c\<^sub>1 \<Longrightarrow> l \<turnstile>' c\<^sub>2 \<Longrightarrow> l \<turnstile>' c\<^sub>1;;c\<^sub>2"  |
If':
  "\<lbrakk> sec b \<le> l;  l \<turnstile>' c\<^sub>1;  l \<turnstile>' c\<^sub>2 \<rbrakk> \<Longrightarrow> l \<turnstile>' IF b THEN c\<^sub>1 ELSE c\<^sub>2"  |
While':
  "\<lbrakk> sec b = 0;  0 \<turnstile>' c \<rbrakk> \<Longrightarrow> 0 \<turnstile>' WHILE b DO c"  |
anti_mono':
  "\<lbrakk> l \<turnstile>' c;  l' \<le> l \<rbrakk> \<Longrightarrow> l' \<turnstile>' c"

lemma sec_type_sec_type': 
  "l \<turnstile> c \<Longrightarrow> l \<turnstile>' c"
apply(induction rule: sec_type.induct)
apply (metis Skip')
apply (metis Assign')
apply (metis Seq')
apply (metis max.commute max.absorb_iff2 nat_le_linear If' anti_mono')
by (metis While')


lemma sec_type'_sec_type:
  "l \<turnstile>' c \<Longrightarrow> l \<turnstile> c"
apply(induction rule: sec_type'.induct)
apply (metis Skip)
apply (metis Assign)
apply (metis Seq)
apply (metis max.absorb2 If)
apply (metis While)
by (metis anti_mono)

corollary sec_type_eq: "l \<turnstile> c \<longleftrightarrow> l \<turnstile>' c"
by (metis sec_type'_sec_type sec_type_sec_type')

end
