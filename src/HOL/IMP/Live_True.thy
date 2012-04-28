(* Author: Tobias Nipkow *)

theory Live_True
imports "~~/src/HOL/Library/While_Combinator" Vars Big_Step
begin

subsection "True Liveness Analysis"

fun L :: "com \<Rightarrow> vname set \<Rightarrow> vname set" where
"L SKIP X = X" |
"L (x ::= a) X = (if x:X then X-{x} \<union> vars a else X)" |
"L (c\<^isub>1; c\<^isub>2) X = (L c\<^isub>1 \<circ> L c\<^isub>2) X" |
"L (IF b THEN c\<^isub>1 ELSE c\<^isub>2) X = vars b \<union> L c\<^isub>1 X \<union> L c\<^isub>2 X" |
"L (WHILE b DO c) X = lfp(%Y. vars b \<union> X \<union> L c Y)"

lemma L_mono: "mono (L c)"
proof-
  { fix X Y have "X \<subseteq> Y \<Longrightarrow> L c X \<subseteq> L c Y"
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
  } thus ?thesis by(rule monoI)
qed

lemma mono_union_L:
  "mono (%Y. X \<union> L c Y)"
by (metis (no_types) L_mono mono_def order_eq_iff set_eq_subset sup_mono)

lemma L_While_unfold:
  "L (WHILE b DO c) X = vars b \<union> X \<union> L c (L (WHILE b DO c) X)"
by(metis lfp_unfold[OF mono_union_L] L.simps(5))


subsection "Soundness"

theorem L_sound:
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
  from IfTrue(3)[OF `s = t on L c1 X`] obtain t' where
    "(c1, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using `bval b t` by auto
next
  case (IfFalse b s c2 s' c1)
  hence "s = t on vars b" "s = t on L c2 X" by auto
  from  bval_eq_if_eq_on_vars[OF this(1)] IfFalse(1) have "~bval b t" by simp
  from IfFalse(3)[OF `s = t on L c2 X`] obtain t' where
    "(c2, t) \<Rightarrow> t'" "s' = t' on X" by auto
  thus ?case using `~bval b t` by auto
next
  case (WhileFalse b s c)
  hence "~ bval b t"
    by (metis L_While_unfold UnI1 bval_eq_if_eq_on_vars)
  thus ?case using WhileFalse.prems L_While_unfold[of b c X] by auto
next
  case (WhileTrue b s1 c s2 s3 X t1)
  let ?w = "WHILE b DO c"
  from `bval b s1` WhileTrue.prems have "bval b t1"
    by (metis L_While_unfold UnI1 bval_eq_if_eq_on_vars)
  have "s1 = t1 on L c (L ?w X)" using  L_While_unfold WhileTrue.prems
    by (blast)
  from WhileTrue.IH(1)[OF this] obtain t2 where
    "(c, t1) \<Rightarrow> t2" "s2 = t2 on L ?w X" by auto
  from WhileTrue.IH(2)[OF this(2)] obtain t3 where "(?w,t2) \<Rightarrow> t3" "s3 = t3 on X"
    by auto
  with `bval b t1` `(c, t1) \<Rightarrow> t2` show ?case by auto
qed


instantiation com :: vars
begin

fun vars_com :: "com \<Rightarrow> vname set" where
"vars SKIP = {}" |
"vars (x::=e) = vars e" |
"vars (c\<^isub>1; c\<^isub>2) = vars c\<^isub>1 \<union> vars c\<^isub>2" |
"vars (IF b THEN c\<^isub>1 ELSE c\<^isub>2) = vars b \<union> vars c\<^isub>1 \<union> vars c\<^isub>2" |
"vars (WHILE b DO c) = vars b \<union> vars c"

instance ..

end

lemma L_subset_vars: "L c X \<subseteq> vars c \<union> X"
proof(induction c arbitrary: X)
  case (While b c)
  have "lfp(%Y. vars b \<union> X \<union> L c Y) \<subseteq> vars b \<union> vars c \<union> X"
    using While.IH[of "vars b \<union> vars c \<union> X"]
    by (auto intro!: lfp_lowerbound)
  thus ?case by simp
qed auto

lemma afinite[simp]: "finite(vars(a::aexp))"
by (induction a) auto

lemma bfinite[simp]: "finite(vars(b::bexp))"
by (induction b) auto

lemma cfinite[simp]: "finite(vars(c::com))"
by (induction c) auto

(* move to Inductive; call Kleene? *)
lemma lfp_finite_iter: assumes "mono f" and "(f^^Suc k) bot = (f^^k) bot"
shows "lfp f = (f^^k) bot"
proof(rule antisym)
  show "lfp f \<le> (f^^k) bot"
  proof(rule lfp_lowerbound)
    show "f ((f^^k) bot) \<le> (f^^k) bot" using assms(2) by simp
  qed
next
  show "(f^^k) bot \<le> lfp f"
  proof(induction k)
    case 0 show ?case by simp
  next
    case Suc
    from monoD[OF assms(1) Suc] lfp_unfold[OF assms(1)]
    show ?case by simp
  qed
qed

(* move to While_Combinator *)
lemma while_option_stop2:
 "while_option b c s = Some t \<Longrightarrow> EX k. t = (c^^k) s \<and> \<not> b t"
apply(simp add: while_option_def split: if_splits)
by (metis (lifting) LeastI_ex)
(* move to While_Combinator *)
lemma while_option_finite_subset_Some: fixes C :: "'a set"
  assumes "mono f" and "!!X. X \<subseteq> C \<Longrightarrow> f X \<subseteq> C" and "finite C"
  shows "\<exists>P. while_option (\<lambda>A. f A \<noteq> A) f {} = Some P"
proof(rule measure_while_option_Some[where
    f= "%A::'a set. card C - card A" and P= "%A. A \<subseteq> C \<and> A \<subseteq> f A" and s= "{}"])
  fix A assume A: "A \<subseteq> C \<and> A \<subseteq> f A" "f A \<noteq> A"
  show "(f A \<subseteq> C \<and> f A \<subseteq> f (f A)) \<and> card C - card (f A) < card C - card A"
    (is "?L \<and> ?R")
  proof
    show ?L by(metis A(1) assms(2) monoD[OF `mono f`])
    show ?R by (metis A assms(2,3) card_seteq diff_less_mono2 equalityI linorder_le_less_linear rev_finite_subset)
  qed
qed simp
(* move to While_Combinator *)
lemma lfp_eq_while_option:
  assumes "mono f" and "!!X. X \<subseteq> C \<Longrightarrow> f X \<subseteq> C" and "finite C"
  shows "lfp f = the(while_option (\<lambda>A. f A \<noteq> A) f {})"
proof-
  obtain P where "while_option (\<lambda>A. f A \<noteq> A) f {} = Some P"
    using while_option_finite_subset_Some[OF assms] by blast
  with while_option_stop2[OF this] lfp_finite_iter[OF assms(1)]
  show ?thesis by auto
qed

text{* For code generation: *}
lemma L_While: fixes b c X
assumes "finite X" defines "f == \<lambda>A. vars b \<union> X \<union> L c A"
shows "L (WHILE b DO c) X = the(while_option (\<lambda>A. f A \<noteq> A) f {})" (is "_ = ?r")
proof -
  let ?V = "vars b \<union> vars c \<union> X"
  have "lfp f = ?r"
  proof(rule lfp_eq_while_option[where C = "?V"])
    show "mono f" by(simp add: f_def mono_union_L)
  next
    fix Y show "Y \<subseteq> ?V \<Longrightarrow> f Y \<subseteq> ?V"
      unfolding f_def using L_subset_vars[of c] by blast
  next
    show "finite ?V" using `finite X` by simp
  qed
  thus ?thesis by (simp add: f_def)
qed

text{* An approximate computation of the WHILE-case: *}

fun iter :: "('a \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
where
"iter f 0 p d = d" |
"iter f (Suc n) p d = (if f p = p then p else iter f n (f p) d)"

lemma iter_pfp:
  "f d \<le> d \<Longrightarrow> mono f \<Longrightarrow> x \<le> f x \<Longrightarrow> f(iter f i x d) \<le> iter f i x d"
apply(induction i arbitrary: x)
 apply simp
apply (simp add: mono_def)
done

lemma iter_While_pfp:
fixes b c X W k f
defines "f == \<lambda>A. vars b \<union> X \<union> L c A" and "W == vars b \<union> vars c \<union> X"
and "P == iter f k {} W"
shows "f P \<subseteq> P"
proof-
  have "f W \<subseteq> W" unfolding f_def W_def using L_subset_vars[of c] by blast
  have "mono f" by(simp add: f_def mono_union_L)
  from iter_pfp[of f, OF `f W \<subseteq> W` `mono f` empty_subsetI]
  show ?thesis by(simp add: P_def)
qed

end
