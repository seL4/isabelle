(* Author: Tobias Nipkow *)

theory Sec_Typing imports Sec_Type_Expr
begin

subsection "Syntax Directed Typing"

inductive sec_type :: "nat \<Rightarrow> com \<Rightarrow> bool" ("(_/ \<turnstile> _)" [0,0] 50) where
Skip:
  "l \<turnstile> SKIP" |
Assign:
  "\<lbrakk> sec x \<ge> sec_aexp a;  sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile> x ::= a" |
Semi:
  "\<lbrakk> l \<turnstile> c\<^isub>1;  l \<turnstile> c\<^isub>2 \<rbrakk> \<Longrightarrow> l \<turnstile> c\<^isub>1;c\<^isub>2" |
If:
  "\<lbrakk> max (sec_bexp b) l \<turnstile> c\<^isub>1;  max (sec_bexp b) l \<turnstile> c\<^isub>2 \<rbrakk> \<Longrightarrow> l \<turnstile> IF b THEN c\<^isub>1 ELSE c\<^isub>2" |
While:
  "max (sec_bexp b) l \<turnstile> c \<Longrightarrow> l \<turnstile> WHILE b DO c"

code_pred (expected_modes: i => i => bool) sec_type .

value "0 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x1'' ::= N 0 ELSE SKIP"
value "1 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x''  ::= N 0 ELSE SKIP"
value "2 \<turnstile> IF Less (V ''x1'') (V ''x'') THEN ''x1'' ::= N 0 ELSE SKIP"

inductive_cases [elim!]:
  "l \<turnstile> x ::= a"  "l \<turnstile> c\<^isub>1;c\<^isub>2"  "l \<turnstile> IF b THEN c\<^isub>1 ELSE c\<^isub>2"  "l \<turnstile> WHILE b DO c"


text{* An important property: anti-monotonicity. *}

lemma anti_mono: "\<lbrakk> l \<turnstile> c;  l' \<le> l \<rbrakk> \<Longrightarrow> l' \<turnstile> c"
apply(induction arbitrary: l' rule: sec_type.induct)
apply (metis sec_type.intros(1))
apply (metis le_trans sec_type.intros(2))
apply (metis sec_type.intros(3))
apply (metis If le_refl sup_mono sup_nat_def)
apply (metis While le_refl sup_mono sup_nat_def)
done

lemma confinement: "\<lbrakk> (c,s) \<Rightarrow> t;  l \<turnstile> c \<rbrakk> \<Longrightarrow> s = t (< l)"
proof(induction rule: big_step_induct)
  case Skip thus ?case by simp
next
  case Assign thus ?case by auto
next
  case Semi thus ?case by auto
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
  hence "max (sec_bexp b) l \<turnstile> c" by auto
  hence "l \<turnstile> c" by (metis le_maxI2 anti_mono)
  thus ?case using WhileTrue by metis
qed


theorem noninterference:
  "\<lbrakk> (c,s) \<Rightarrow> s'; (c,t) \<Rightarrow> t';  0 \<turnstile> c;  s = t (\<le> l) \<rbrakk>
   \<Longrightarrow> s' = t' (\<le> l)"
proof(induction arbitrary: t t' rule: big_step_induct)
  case Skip thus ?case by auto
next
  case (Assign x a s)
  have [simp]: "t' = t(x := aval a t)" using Assign by auto
  have "sec x >= sec_aexp a" using `0 \<turnstile> x ::= a` by auto
  show ?case
  proof auto
    assume "sec x \<le> l"
    with `sec x >= sec_aexp a` have "sec_aexp a \<le> l" by arith
    thus "aval a s = aval a t"
      by (rule aval_eq_if_eq_le[OF `s = t (\<le> l)`])
  next
    fix y assume "y \<noteq> x" "sec y \<le> l"
    thus "s y = t y" using `s = t (\<le> l)` by simp
  qed
next
  case Semi thus ?case by blast
next
  case (IfTrue b s c1 s' c2)
  have "sec_bexp b \<turnstile> c1" "sec_bexp b \<turnstile> c2" using IfTrue.prems(2) by auto
  show ?case
  proof cases
    assume "sec_bexp b \<le> l"
    hence "s = t (\<le> sec_bexp b)" using `s = t (\<le> l)` by auto
    hence "bval b t" using `bval b s` by(simp add: bval_eq_if_eq_le)
    with IfTrue.IH IfTrue.prems(1,3) `sec_bexp b \<turnstile> c1`  anti_mono
    show ?thesis by auto
  next
    assume "\<not> sec_bexp b \<le> l"
    have 1: "sec_bexp b \<turnstile> IF b THEN c1 ELSE c2"
      by(rule sec_type.intros)(simp_all add: `sec_bexp b \<turnstile> c1` `sec_bexp b \<turnstile> c2`)
    from confinement[OF IfTrue.hyps(2) `sec_bexp b \<turnstile> c1`] `\<not> sec_bexp b \<le> l`
    have "s = s' (\<le> l)" by auto
    moreover
    from confinement[OF IfTrue.prems(1) 1] `\<not> sec_bexp b \<le> l`
    have "t = t' (\<le> l)" by auto
    ultimately show "s' = t' (\<le> l)" using `s = t (\<le> l)` by auto
  qed
next
  case (IfFalse b s c2 s' c1)
  have "sec_bexp b \<turnstile> c1" "sec_bexp b \<turnstile> c2" using IfFalse.prems(2) by auto
  show ?case
  proof cases
    assume "sec_bexp b \<le> l"
    hence "s = t (\<le> sec_bexp b)" using `s = t (\<le> l)` by auto
    hence "\<not> bval b t" using `\<not> bval b s` by(simp add: bval_eq_if_eq_le)
    with IfFalse.IH IfFalse.prems(1,3) `sec_bexp b \<turnstile> c2` anti_mono
    show ?thesis by auto
  next
    assume "\<not> sec_bexp b \<le> l"
    have 1: "sec_bexp b \<turnstile> IF b THEN c1 ELSE c2"
      by(rule sec_type.intros)(simp_all add: `sec_bexp b \<turnstile> c1` `sec_bexp b \<turnstile> c2`)
    from confinement[OF big_step.IfFalse[OF IfFalse(1,2)] 1] `\<not> sec_bexp b \<le> l`
    have "s = s' (\<le> l)" by auto
    moreover
    from confinement[OF IfFalse.prems(1) 1] `\<not> sec_bexp b \<le> l`
    have "t = t' (\<le> l)" by auto
    ultimately show "s' = t' (\<le> l)" using `s = t (\<le> l)` by auto
  qed
next
  case (WhileFalse b s c)
  have "sec_bexp b \<turnstile> c" using WhileFalse.prems(2) by auto
  show ?case
  proof cases
    assume "sec_bexp b \<le> l"
    hence "s = t (\<le> sec_bexp b)" using `s = t (\<le> l)` by auto
    hence "\<not> bval b t" using `\<not> bval b s` by(simp add: bval_eq_if_eq_le)
    with WhileFalse.prems(1,3) show ?thesis by auto
  next
    assume "\<not> sec_bexp b \<le> l"
    have 1: "sec_bexp b \<turnstile> WHILE b DO c"
      by(rule sec_type.intros)(simp_all add: `sec_bexp b \<turnstile> c`)
    from confinement[OF WhileFalse.prems(1) 1] `\<not> sec_bexp b \<le> l`
    have "t = t' (\<le> l)" by auto
    thus "s = t' (\<le> l)" using `s = t (\<le> l)` by auto
  qed
next
  case (WhileTrue b s1 c s2 s3 t1 t3)
  let ?w = "WHILE b DO c"
  have "sec_bexp b \<turnstile> c" using WhileTrue.prems(2) by auto
  show ?case
  proof cases
    assume "sec_bexp b \<le> l"
    hence "s1 = t1 (\<le> sec_bexp b)" using `s1 = t1 (\<le> l)` by auto
    hence "bval b t1"
      using `bval b s1` by(simp add: bval_eq_if_eq_le)
    then obtain t2 where "(c,t1) \<Rightarrow> t2" "(?w,t2) \<Rightarrow> t3"
      using `(?w,t1) \<Rightarrow> t3` by auto
    from WhileTrue.IH(2)[OF `(?w,t2) \<Rightarrow> t3` `0 \<turnstile> ?w`
      WhileTrue.IH(1)[OF `(c,t1) \<Rightarrow> t2` anti_mono[OF `sec_bexp b \<turnstile> c`]
        `s1 = t1 (\<le> l)`]]
    show ?thesis by simp
  next
    assume "\<not> sec_bexp b \<le> l"
    have 1: "sec_bexp b \<turnstile> ?w" by(rule sec_type.intros)(simp_all add: `sec_bexp b \<turnstile> c`)
    from confinement[OF big_step.WhileTrue[OF WhileTrue.hyps] 1] `\<not> sec_bexp b \<le> l`
    have "s1 = s3 (\<le> l)" by auto
    moreover
    from confinement[OF WhileTrue.prems(1) 1] `\<not> sec_bexp b \<le> l`
    have "t1 = t3 (\<le> l)" by auto
    ultimately show "s3 = t3 (\<le> l)" using `s1 = t1 (\<le> l)` by auto
  qed
qed


subsection "The Standard Typing System"

text{* The predicate @{prop"l \<turnstile> c"} is nicely intuitive and executable. The
standard formulation, however, is slightly different, replacing the maximum
computation by an antimonotonicity rule. We introduce the standard system now
and show the equivalence with our formulation. *}

inductive sec_type' :: "nat \<Rightarrow> com \<Rightarrow> bool" ("(_/ \<turnstile>'' _)" [0,0] 50) where
Skip':
  "l \<turnstile>' SKIP" |
Assign':
  "\<lbrakk> sec x \<ge> sec_aexp a; sec x \<ge> l \<rbrakk> \<Longrightarrow> l \<turnstile>' x ::= a" |
Semi':
  "\<lbrakk> l \<turnstile>' c\<^isub>1;  l \<turnstile>' c\<^isub>2 \<rbrakk> \<Longrightarrow> l \<turnstile>' c\<^isub>1;c\<^isub>2" |
If':
  "\<lbrakk> sec_bexp b \<le> l;  l \<turnstile>' c\<^isub>1;  l \<turnstile>' c\<^isub>2 \<rbrakk> \<Longrightarrow> l \<turnstile>' IF b THEN c\<^isub>1 ELSE c\<^isub>2" |
While':
  "\<lbrakk> sec_bexp b \<le> l;  l \<turnstile>' c \<rbrakk> \<Longrightarrow> l \<turnstile>' WHILE b DO c" |
anti_mono':
  "\<lbrakk> l \<turnstile>' c;  l' \<le> l \<rbrakk> \<Longrightarrow> l' \<turnstile>' c"

lemma sec_type_sec_type': "l \<turnstile> c \<Longrightarrow> l \<turnstile>' c"
apply(induction rule: sec_type.induct)
apply (metis Skip')
apply (metis Assign')
apply (metis Semi')
apply (metis min_max.inf_sup_ord(3) min_max.sup_absorb2 nat_le_linear If' anti_mono')
by (metis less_or_eq_imp_le min_max.sup_absorb1 min_max.sup_absorb2 nat_le_linear While' anti_mono')


lemma sec_type'_sec_type: "l \<turnstile>' c \<Longrightarrow> l \<turnstile> c"
apply(induction rule: sec_type'.induct)
apply (metis Skip)
apply (metis Assign)
apply (metis Semi)
apply (metis min_max.sup_absorb2 If)
apply (metis min_max.sup_absorb2 While)
by (metis anti_mono)

subsection "A Bottom-Up Typing System"

inductive sec_type2 :: "com \<Rightarrow> level \<Rightarrow> bool" ("(\<turnstile> _ : _)" [0,0] 50) where
Skip2:
  "\<turnstile> SKIP : l" |
Assign2:
  "sec x \<ge> sec_aexp a \<Longrightarrow> \<turnstile> x ::= a : sec x" |
Semi2:
  "\<lbrakk> \<turnstile> c\<^isub>1 : l\<^isub>1;  \<turnstile> c\<^isub>2 : l\<^isub>2 \<rbrakk> \<Longrightarrow> \<turnstile> c\<^isub>1;c\<^isub>2 : min l\<^isub>1 l\<^isub>2 " |
If2:
  "\<lbrakk> sec_bexp b \<le> min l\<^isub>1 l\<^isub>2;  \<turnstile> c\<^isub>1 : l\<^isub>1;  \<turnstile> c\<^isub>2 : l\<^isub>2 \<rbrakk>
  \<Longrightarrow> \<turnstile> IF b THEN c\<^isub>1 ELSE c\<^isub>2 : min l\<^isub>1 l\<^isub>2" |
While2:
  "\<lbrakk> sec_bexp b \<le> l;  \<turnstile> c : l \<rbrakk> \<Longrightarrow> \<turnstile> WHILE b DO c : l"


lemma sec_type2_sec_type': "\<turnstile> c : l \<Longrightarrow> l \<turnstile>' c"
apply(induction rule: sec_type2.induct)
apply (metis Skip')
apply (metis Assign' eq_imp_le)
apply (metis Semi' anti_mono' min_max.inf.commute min_max.inf_le2)
apply (metis If' anti_mono' min_max.inf_absorb2 min_max.le_iff_inf nat_le_linear)
by (metis While')

lemma sec_type'_sec_type2: "l \<turnstile>' c \<Longrightarrow> \<exists> l' \<ge> l. \<turnstile> c : l'"
apply(induction rule: sec_type'.induct)
apply (metis Skip2 le_refl)
apply (metis Assign2)
apply (metis Semi2 min_max.inf_greatest)
apply (metis If2 inf_greatest inf_nat_def le_trans)
apply (metis While2 le_trans)
by (metis le_trans)

end
