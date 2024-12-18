(* Author: Tobias Nipkow *)

subsection "True Liveness Analysis"

theory Live_True
imports "HOL-Library.While_Combinator" Vars Big_Step
begin

subsubsection "Analysis"

fun L :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"L SKIP X = X" |
"L (x ::= a) X = (if x \<in> X then vars a \<union> (X - {x}) else X)" |
"L (c\<^sub>1;; c\<^sub>2) X = L c\<^sub>1 (L c\<^sub>2 X)" |
"L (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = vars b \<union> L c\<^sub>1 X \<union> L c\<^sub>2 X" |
"L (WHILE b DO c) X = lfp(\<lambda>Y. vars b \<union> X \<union> L c Y)"

lemma L_mono: "mono (L c)"
proof-
  have "X \<subseteq> Y \<Longrightarrow> L c X \<subseteq> L c Y" for X Y
  proof(induction c arbitrary: X Y)
    case (While b c)
    show ?case
    proof(simp, rule lfp_mono)
      fix Z show "vars b \<union> X \<union> L c Z \<subseteq> vars b \<union> Y \<union> L c Z"
        using While by auto
    qed
  next
    case If thus ?case by(auto simp: subset_iff)
  qed auto
  thus ?thesis by(rule monoI)
qed

lemma mono_union_L:
  "mono (\<lambda>Y. X \<union> L c Y)"
using L_mono unfolding mono_def by (metis (no_types) order_eq_iff set_eq_subset sup_mono)

lemma L_While_unfold:
  "L (WHILE b DO c) X = vars b \<union> X \<union> L c (L (WHILE b DO c) X)"
by(metis lfp_unfold[OF mono_union_L] L.simps(5))

lemma L_While_pfp: "L c (L (WHILE b DO c) X) \<subseteq> L (WHILE b DO c) X"
using L_While_unfold by blast

lemma L_While_vars: "vars b \<subseteq> L (WHILE b DO c) X"
using L_While_unfold by blast

lemma L_While_X: "X \<subseteq> L (WHILE b DO c) X"
using L_While_unfold by blast

text\<open>Disable \<open>L WHILE\<close> equation and reason only with \<open>L WHILE\<close> constraints:\<close>
declare L.simps(5)[simp del]


subsubsection "Correctness"

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
  hence "s = t on vars b" and "s = t on L c1 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfTrue(1) have "bval b t" by simp
  from IfTrue.IH[OF \<open>s = t on L c1 X\<close>] obtain t' where
    "(c1, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using \<open>bval b t\<close> by auto
next
  case (IfFalse b s c2 s' c1)
  hence "s = t on vars b" "s = t on L c2 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfFalse(1) have "~bval b t" by simp
  from IfFalse.IH[OF \<open>s = t on L c2 X\<close>] obtain t' where
    "(c2, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using \<open>~bval b t\<close> by auto
next
  case (WhileFalse b s c)
  hence "~ bval b t"
    by (metis L_While_vars bval_eq_if_eq_on_vars subsetD)
  thus ?case using WhileFalse.prems L_While_X[of X b c] by auto
next
  case (WhileTrue b s1 c s2 s3 X t1)
  let ?w = "WHILE b DO c"
  from \<open>bval b s1\<close> WhileTrue.prems have "bval b t1"
    by (metis L_While_vars bval_eq_if_eq_on_vars subsetD)
  have "s1 = t1 on L c (L ?w X)" using  L_While_pfp WhileTrue.prems
    by (blast)
  from WhileTrue.IH(1)[OF this] obtain t2 where
    "(c, t1) \<Rightarrow> t2" "s2 = t2 on L ?w X" by auto
  from WhileTrue.IH(2)[OF this(2)] obtain t3 where "(?w,t2) \<Rightarrow> t3" "s3 = t3 on X"
    by auto
  with \<open>bval b t1\<close> \<open>(c, t1) \<Rightarrow> t2\<close> show ?case by auto
qed


subsubsection "Executability"

lemma L_subset_vars: "L c X \<subseteq> rvars c \<union> X"
proof(induction c arbitrary: X)
  case (While b c)
  have "lfp(\<lambda>Y. vars b \<union> X \<union> L c Y) \<subseteq> vars b \<union> rvars c \<union> X"
    using While.IH[of "vars b \<union> rvars c \<union> X"]
    by (auto intro!: lfp_lowerbound)
  thus ?case by (simp add: L.simps(5))
qed auto

text\<open>Make \<^const>\<open>L\<close> executable by replacing \<^const>\<open>lfp\<close> with the \<^const>\<open>while\<close> combinator from theory \<^theory>\<open>HOL-Library.While_Combinator\<close>. The \<^const>\<open>while\<close>
combinator obeys the recursion equation
@{thm[display] While_Combinator.while_unfold[no_vars]}
and is thus executable.\<close>

lemma L_While: fixes b c X
assumes "finite X" defines "f == \<lambda>Y. vars b \<union> X \<union> L c Y"
shows "L (WHILE b DO c) X = while (\<lambda>Y. f Y \<noteq> Y) f {}" (is "_ = ?r")
proof -
  let ?V = "vars b \<union> rvars c \<union> X"
  have "lfp f = ?r"
  proof(rule lfp_while[where C = "?V"])
    show "mono f" by(simp add: f_def mono_union_L)
  next
    fix Y show "Y \<subseteq> ?V \<Longrightarrow> f Y \<subseteq> ?V"
      unfolding f_def using L_subset_vars[of c] by blast
  next
    show "finite ?V" using \<open>finite X\<close> by simp
  qed
  thus ?thesis by (simp add: f_def L.simps(5))
qed

lemma L_While_let: "finite X \<Longrightarrow> L (WHILE b DO c) X =
  (let f = (\<lambda>Y. vars b \<union> X \<union> L c Y)
   in while (\<lambda>Y. f Y \<noteq> Y) f {})"
by(simp add: L_While)

lemma L_While_set: "L (WHILE b DO c) (set xs) =
  (let f = (\<lambda>Y. vars b \<union> set xs \<union> L c Y)
   in while (\<lambda>Y. f Y \<noteq> Y) f {})"
by(rule L_While_let, simp)

text\<open>Replace the equation for \<open>L (WHILE \<dots>)\<close> by the executable @{thm[source] L_While_set}:\<close>
lemmas [code] = L.simps(1-4) L_While_set
text\<open>Sorry, this syntax is odd.\<close>

text\<open>A test:\<close>
lemma "(let b = Less (N 0) (V ''y''); c = ''y'' ::= V ''x'';; ''x'' ::= V ''z''
  in L (WHILE b DO c) {''y''}) = {''x'', ''y'', ''z''}"
by eval


subsubsection "Limiting the number of iterations"

text\<open>The final parameter is the default value:\<close>

fun iter :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
"iter f 0 p d = d" |
"iter f (Suc n) p d = (if f p = p then p else iter f n (f p) d)"

text\<open>A version of \<^const>\<open>L\<close> with a bounded number of iterations (here: 2)
in the WHILE case:\<close>

fun Lb :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"Lb SKIP X = X" |
"Lb (x ::= a) X = (if x \<in> X then X - {x} \<union> vars a else X)" |
"Lb (c\<^sub>1;; c\<^sub>2) X = (Lb c\<^sub>1 \<circ> Lb c\<^sub>2) X" |
"Lb (IF b THEN c\<^sub>1 ELSE c\<^sub>2) X = vars b \<union> Lb c\<^sub>1 X \<union> Lb c\<^sub>2 X" |
"Lb (WHILE b DO c) X = iter (\<lambda>A. vars b \<union> X \<union> Lb c A) 2 {} (vars b \<union> rvars c \<union> X)"

text\<open>\<^const>\<open>Lb\<close> (and \<^const>\<open>iter\<close>) is not monotone!\<close>
lemma "let w = WHILE Bc False DO (''x'' ::= V ''y'';; ''z'' ::= V ''x'')
  in \<not> (Lb w {''z''} \<subseteq> Lb w {''y'',''z''})"
by eval

lemma lfp_subset_iter:
  "\<lbrakk> mono f; !!X. f X \<subseteq> f' X; lfp f \<subseteq> D \<rbrakk> \<Longrightarrow> lfp f \<subseteq> iter f' n A D"
proof(induction n arbitrary: A)
  case 0 thus ?case by simp
next
  case Suc thus ?case by simp (metis lfp_lowerbound)
qed

lemma "L c X \<subseteq> Lb c X"
proof(induction c arbitrary: X)
  case (While b c)
  let ?f  = "\<lambda>A. vars b \<union> X \<union> L  c A"
  let ?fb = "\<lambda>A. vars b \<union> X \<union> Lb c A"
  show ?case
  proof (simp add: L.simps(5), rule lfp_subset_iter[OF mono_union_L])
    show "!!X. ?f X \<subseteq> ?fb X" using While.IH by blast
    show "lfp ?f \<subseteq> vars b \<union> rvars c \<union> X"
      by (metis (full_types) L.simps(5) L_subset_vars rvars.simps(5))
  qed
next
  case Seq thus ?case by simp (metis (full_types) L_mono monoD subset_trans)
qed auto

end
