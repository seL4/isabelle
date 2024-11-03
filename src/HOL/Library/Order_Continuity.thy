(*  Title:      HOL/Library/Order_Continuity.thy
    Author:     David von Oheimb, TU München
    Author:     Johannes Hölzl, TU München
*)

section \<open>Continuity and iterations\<close>

theory Order_Continuity
imports Complex_Main Countable_Complete_Lattices
begin

(* TODO: Generalize theory to chain-complete partial orders *)

lemma SUP_nat_binary:
  "(sup A (SUP x\<in>Collect ((<) (0::nat)). B)) = (sup A B::'a::countable_complete_lattice)"
  apply (subst image_constant)
   apply auto
  done

lemma INF_nat_binary:
  "inf A (INF x\<in>Collect ((<) (0::nat)). B) = (inf A B::'a::countable_complete_lattice)"
  apply (subst image_constant)
   apply auto
  done

text \<open>
  The name \<open>continuous\<close> is already taken in \<open>Complex_Main\<close>, so we use
  \<open>sup_continuous\<close> and \<open>inf_continuous\<close>. These names appear sometimes in literature
  and have the advantage that these names are duals.
\<close>

named_theorems order_continuous_intros

subsection \<open>Continuity for complete lattices\<close>

definition
  sup_continuous :: "('a::countable_complete_lattice \<Rightarrow> 'b::countable_complete_lattice) \<Rightarrow> bool"
where
  "sup_continuous F \<longleftrightarrow> (\<forall>M::nat \<Rightarrow> 'a. mono M \<longrightarrow> F (SUP i. M i) = (SUP i. F (M i)))"

lemma sup_continuousD: "sup_continuous F \<Longrightarrow> mono M \<Longrightarrow> F (SUP i::nat. M i) = (SUP i. F (M i))"
  by (auto simp: sup_continuous_def)

lemma sup_continuous_mono:
  "mono F" if "sup_continuous F"
proof
  fix A B :: "'a"
  assume "A \<le> B"
  let ?f = "\<lambda>n::nat. if n = 0 then A else B"
  from \<open>A \<le> B\<close> have "incseq ?f"
    by (auto intro: monoI)
  with \<open>sup_continuous F\<close> have *: "F (SUP i. ?f i) = (SUP i. F (?f i))"
    by (auto dest: sup_continuousD)
  from \<open>A \<le> B\<close> have "B = sup A B"
    by (simp add: le_iff_sup)
  then have "F B = F (sup A B)"
    by simp
  also have "\<dots> = sup (F A) (F B)"
    using * by (simp add: if_distrib SUP_nat_binary cong del: SUP_cong)
  finally show "F A \<le> F B"
    by (simp add: le_iff_sup)
qed

lemma [order_continuous_intros]:
  shows sup_continuous_const: "sup_continuous (\<lambda>x. c)"
    and sup_continuous_id: "sup_continuous (\<lambda>x. x)"
    and sup_continuous_apply: "sup_continuous (\<lambda>f. f x)"
    and sup_continuous_fun: "(\<And>s. sup_continuous (\<lambda>x. P x s)) \<Longrightarrow> sup_continuous P"
    and sup_continuous_If: "sup_continuous F \<Longrightarrow> sup_continuous G \<Longrightarrow> sup_continuous (\<lambda>f. if C then F f else G f)"
  by (auto simp: sup_continuous_def image_comp)

lemma sup_continuous_compose:
  assumes f: "sup_continuous f" and g: "sup_continuous g"
  shows "sup_continuous (\<lambda>x. f (g x))"
  unfolding sup_continuous_def
proof safe
  fix M :: "nat \<Rightarrow> 'c"
  assume M: "mono M"
  then have "mono (\<lambda>i. g (M i))"
    using sup_continuous_mono[OF g] by (auto simp: mono_def)
  with M show "f (g (Sup (M ` UNIV))) = (SUP i. f (g (M i)))"
    by (auto simp: sup_continuous_def g[THEN sup_continuousD] f[THEN sup_continuousD])
qed

lemma sup_continuous_sup[order_continuous_intros]:
  "sup_continuous f \<Longrightarrow> sup_continuous g \<Longrightarrow> sup_continuous (\<lambda>x. sup (f x) (g x))"
  by (simp add: sup_continuous_def ccSUP_sup_distrib)

lemma sup_continuous_inf[order_continuous_intros]:
  fixes P Q :: "'a :: countable_complete_lattice \<Rightarrow> 'b :: countable_complete_distrib_lattice"
  assumes P: "sup_continuous P" and Q: "sup_continuous Q"
  shows "sup_continuous (\<lambda>x. inf (P x) (Q x))"
  unfolding sup_continuous_def
proof (safe intro!: antisym)
  fix M :: "nat \<Rightarrow> 'a" assume M: "incseq M"
  have "inf (P (SUP i. M i)) (Q (SUP i. M i)) \<le> (SUP j i. inf (P (M i)) (Q (M j)))"
    by (simp add: sup_continuousD[OF P M] sup_continuousD[OF Q M] inf_ccSUP ccSUP_inf)
  also have "\<dots> \<le> (SUP i. inf (P (M i)) (Q (M i)))"
  proof (intro ccSUP_least)
    fix i j from M assms[THEN sup_continuous_mono] show "inf (P (M i)) (Q (M j)) \<le> (SUP i. inf (P (M i)) (Q (M i)))"
      by (intro ccSUP_upper2[of _ "sup i j"] inf_mono) (auto simp: mono_def)
  qed auto
  finally show "inf (P (SUP i. M i)) (Q (SUP i. M i)) \<le> (SUP i. inf (P (M i)) (Q (M i)))" .

  show "(SUP i. inf (P (M i)) (Q (M i))) \<le> inf (P (SUP i. M i)) (Q (SUP i. M i))"
    unfolding sup_continuousD[OF P M] sup_continuousD[OF Q M] by (intro ccSUP_least inf_mono ccSUP_upper) auto
qed

lemma sup_continuous_and[order_continuous_intros]:
  "sup_continuous P \<Longrightarrow> sup_continuous Q \<Longrightarrow> sup_continuous (\<lambda>x. P x \<and> Q x)"
  using sup_continuous_inf[of P Q] by simp

lemma sup_continuous_or[order_continuous_intros]:
  "sup_continuous P \<Longrightarrow> sup_continuous Q \<Longrightarrow> sup_continuous (\<lambda>x. P x \<or> Q x)"
  by (auto simp: sup_continuous_def)

lemma sup_continuous_lfp:
  assumes "sup_continuous F" shows "lfp F = (SUP i. (F ^^ i) bot)" (is "lfp F = ?U")
proof (rule antisym)
  note mono = sup_continuous_mono[OF \<open>sup_continuous F\<close>]
  show "?U \<le> lfp F"
  proof (rule SUP_least)
    fix i show "(F ^^ i) bot \<le> lfp F"
    proof (induct i)
      case (Suc i)
      have "(F ^^ Suc i) bot = F ((F ^^ i) bot)" by simp
      also have "\<dots> \<le> F (lfp F)" by (rule monoD[OF mono Suc])
      also have "\<dots> = lfp F" by (simp add: lfp_fixpoint[OF mono])
      finally show ?case .
    qed simp
  qed
  show "lfp F \<le> ?U"
  proof (rule lfp_lowerbound)
    have "mono (\<lambda>i::nat. (F ^^ i) bot)"
    proof -
      have "(F ^^ i) bot \<le> (F ^^ (Suc i)) bot" for i::nat
      proof (induct i)
        case 0 show ?case by simp
      next
        case Suc thus ?case using monoD[OF mono Suc] by auto
      qed
      thus ?thesis by (auto simp add: mono_iff_le_Suc)
    qed
    hence "F ?U = (SUP i. (F ^^ Suc i) bot)"
      using \<open>sup_continuous F\<close> by (simp add: sup_continuous_def)
    also have "\<dots> \<le> ?U"
      by (fast intro: SUP_least SUP_upper)
    finally show "F ?U \<le> ?U" .
  qed
qed

lemma lfp_transfer_bounded:
  assumes P: "P bot" "\<And>x. P x \<Longrightarrow> P (f x)" "\<And>M. (\<And>i. P (M i)) \<Longrightarrow> P (SUP i::nat. M i)"
  assumes \<alpha>: "\<And>M. mono M \<Longrightarrow> (\<And>i::nat. P (M i)) \<Longrightarrow> \<alpha> (SUP i. M i) = (SUP i. \<alpha> (M i))"
  assumes f: "sup_continuous f" and g: "sup_continuous g"
  assumes [simp]: "\<And>x. P x \<Longrightarrow> x \<le> lfp f \<Longrightarrow> \<alpha> (f x) = g (\<alpha> x)"
  assumes g_bound: "\<And>x. \<alpha> bot \<le> g x"
  shows "\<alpha> (lfp f) = lfp g"
proof (rule antisym)
  note mono_g = sup_continuous_mono[OF g]
  note mono_f = sup_continuous_mono[OF f]
  have lfp_bound: "\<alpha> bot \<le> lfp g"
    by (subst lfp_unfold[OF mono_g]) (rule g_bound)

  have P_pow: "P ((f ^^ i) bot)" for i
    by (induction i) (auto intro!: P)
  have incseq_pow: "mono (\<lambda>i. (f ^^ i) bot)"
    unfolding mono_iff_le_Suc
  proof
    fix i show "(f ^^ i) bot \<le> (f ^^ (Suc i)) bot"
    proof (induct i)
      case Suc thus ?case using monoD[OF sup_continuous_mono[OF f] Suc] by auto
    qed (simp add: le_fun_def)
  qed
  have P_lfp: "P (lfp f)"
    using P_pow unfolding sup_continuous_lfp[OF f] by (auto intro!: P)

  have iter_le_lfp: "(f ^^ n) bot \<le> lfp f" for n
    apply (induction n)
    apply simp
    apply (subst lfp_unfold[OF mono_f])
    apply (auto intro!: monoD[OF mono_f])
    done

  have "\<alpha> (lfp f) = (SUP i. \<alpha> ((f^^i) bot))"
    unfolding sup_continuous_lfp[OF f] using incseq_pow P_pow by (rule \<alpha>)
  also have "\<dots> \<le> lfp g"
  proof (rule SUP_least)
    fix i show "\<alpha> ((f^^i) bot) \<le> lfp g"
    proof (induction i)
      case (Suc n) then show ?case
        by (subst lfp_unfold[OF mono_g]) (simp add: monoD[OF mono_g] P_pow iter_le_lfp)
    qed (simp add: lfp_bound)
  qed
  finally show "\<alpha> (lfp f) \<le> lfp g" .

  show "lfp g \<le> \<alpha> (lfp f)"
  proof (induction rule: lfp_ordinal_induct[OF mono_g])
    case (1 S) then show ?case
      by (subst lfp_unfold[OF sup_continuous_mono[OF f]])
         (simp add: monoD[OF mono_g] P_lfp)
  qed (auto intro: Sup_least)
qed

lemma lfp_transfer:
  "sup_continuous \<alpha> \<Longrightarrow> sup_continuous f \<Longrightarrow> sup_continuous g \<Longrightarrow>
    (\<And>x. \<alpha> bot \<le> g x) \<Longrightarrow> (\<And>x. x \<le> lfp f \<Longrightarrow> \<alpha> (f x) = g (\<alpha> x)) \<Longrightarrow> \<alpha> (lfp f) = lfp g"
  by (rule lfp_transfer_bounded[where P=top]) (auto dest: sup_continuousD)

definition
  inf_continuous :: "('a::countable_complete_lattice \<Rightarrow> 'b::countable_complete_lattice) \<Rightarrow> bool"
where
  "inf_continuous F \<longleftrightarrow> (\<forall>M::nat \<Rightarrow> 'a. antimono M \<longrightarrow> F (INF i. M i) = (INF i. F (M i)))"

lemma inf_continuousD: "inf_continuous F \<Longrightarrow> antimono M \<Longrightarrow> F (INF i::nat. M i) = (INF i. F (M i))"
  by (auto simp: inf_continuous_def)

lemma inf_continuous_mono:
  "mono F" if "inf_continuous F"
proof
  fix A B :: "'a"
  assume "A \<le> B"
  let ?f = "\<lambda>n::nat. if n = 0 then B else A"
  from \<open>A \<le> B\<close> have "decseq ?f"
    by (auto intro: antimonoI)
  with \<open>inf_continuous F\<close> have *: "F (INF i. ?f i) = (INF i. F (?f i))"
    by (auto dest: inf_continuousD)
  from \<open>A \<le> B\<close> have "A = inf B A"
    by (simp add: inf.absorb_iff2)
  then have "F A = F (inf B A)"
    by simp
  also have "\<dots> = inf (F B) (F A)"
    using * by (simp add: if_distrib INF_nat_binary cong del: INF_cong)
  finally show "F A \<le> F B"
    by (simp add: inf.absorb_iff2)
qed

lemma [order_continuous_intros]:
  shows inf_continuous_const: "inf_continuous (\<lambda>x. c)"
    and inf_continuous_id: "inf_continuous (\<lambda>x. x)"
    and inf_continuous_apply: "inf_continuous (\<lambda>f. f x)"
    and inf_continuous_fun: "(\<And>s. inf_continuous (\<lambda>x. P x s)) \<Longrightarrow> inf_continuous P"
    and inf_continuous_If: "inf_continuous F \<Longrightarrow> inf_continuous G \<Longrightarrow> inf_continuous (\<lambda>f. if C then F f else G f)"
  by (auto simp: inf_continuous_def image_comp)

lemma inf_continuous_inf[order_continuous_intros]:
  "inf_continuous f \<Longrightarrow> inf_continuous g \<Longrightarrow> inf_continuous (\<lambda>x. inf (f x) (g x))"
  by (simp add: inf_continuous_def ccINF_inf_distrib)

lemma inf_continuous_sup[order_continuous_intros]:
  fixes P Q :: "'a :: countable_complete_lattice \<Rightarrow> 'b :: countable_complete_distrib_lattice"
  assumes P: "inf_continuous P" and Q: "inf_continuous Q"
  shows "inf_continuous (\<lambda>x. sup (P x) (Q x))"
  unfolding inf_continuous_def
proof (safe intro!: antisym)
  fix M :: "nat \<Rightarrow> 'a" assume M: "decseq M"
  show "sup (P (INF i. M i)) (Q (INF i. M i)) \<le> (INF i. sup (P (M i)) (Q (M i)))"
    unfolding inf_continuousD[OF P M] inf_continuousD[OF Q M] by (intro ccINF_greatest sup_mono ccINF_lower) auto

  have "(INF i. sup (P (M i)) (Q (M i))) \<le> (INF j i. sup (P (M i)) (Q (M j)))"
  proof (intro ccINF_greatest)
    fix i j from M assms[THEN inf_continuous_mono] show "sup (P (M i)) (Q (M j)) \<ge> (INF i. sup (P (M i)) (Q (M i)))"
      by (intro ccINF_lower2[of _ "sup i j"] sup_mono) (auto simp: mono_def antimono_def)
  qed auto
  also have "\<dots> \<le> sup (P (INF i. M i)) (Q (INF i. M i))"
    by (simp add: inf_continuousD[OF P M] inf_continuousD[OF Q M] ccINF_sup sup_ccINF)
  finally show "sup (P (INF i. M i)) (Q (INF i. M i)) \<ge> (INF i. sup (P (M i)) (Q (M i)))" .
qed

lemma inf_continuous_and[order_continuous_intros]:
  "inf_continuous P \<Longrightarrow> inf_continuous Q \<Longrightarrow> inf_continuous (\<lambda>x. P x \<and> Q x)"
  using inf_continuous_inf[of P Q] by simp

lemma inf_continuous_or[order_continuous_intros]:
  "inf_continuous P \<Longrightarrow> inf_continuous Q \<Longrightarrow> inf_continuous (\<lambda>x. P x \<or> Q x)"
  using inf_continuous_sup[of P Q] by simp

lemma inf_continuous_compose:
  assumes f: "inf_continuous f" and g: "inf_continuous g"
  shows "inf_continuous (\<lambda>x. f (g x))"
  unfolding inf_continuous_def
proof safe
  fix M :: "nat \<Rightarrow> 'c"
  assume M: "antimono M"
  then have "antimono (\<lambda>i. g (M i))"
    using inf_continuous_mono[OF g] by (auto simp: mono_def antimono_def)
  with M show "f (g (Inf (M ` UNIV))) = (INF i. f (g (M i)))"
    by (auto simp: inf_continuous_def g[THEN inf_continuousD] f[THEN inf_continuousD])
qed

lemma inf_continuous_gfp:
  assumes "inf_continuous F" shows "gfp F = (INF i. (F ^^ i) top)" (is "gfp F = ?U")
proof (rule antisym)
  note mono = inf_continuous_mono[OF \<open>inf_continuous F\<close>]
  show "gfp F \<le> ?U"
  proof (rule INF_greatest)
    fix i show "gfp F \<le> (F ^^ i) top"
    proof (induct i)
      case (Suc i)
      have "gfp F = F (gfp F)" by (simp add: gfp_fixpoint[OF mono])
      also have "\<dots> \<le> F ((F ^^ i) top)" by (rule monoD[OF mono Suc])
      also have "\<dots> = (F ^^ Suc i) top" by simp
      finally show ?case .
    qed simp
  qed
  show "?U \<le> gfp F"
  proof (rule gfp_upperbound)
    have *: "antimono (\<lambda>i::nat. (F ^^ i) top)"
    proof -
      have "(F ^^ Suc i) top \<le> (F ^^ i) top" for i::nat
      proof (induct i)
        case 0
        show ?case by simp
      next
        case Suc
        thus ?case using monoD[OF mono Suc] by auto
      qed
      thus ?thesis by (auto simp add: antimono_iff_le_Suc)
    qed
    have "?U \<le> (INF i. (F ^^ Suc i) top)"
      by (fast intro: INF_greatest INF_lower)
    also have "\<dots> \<le> F ?U"
      by (simp add: inf_continuousD \<open>inf_continuous F\<close> *)
    finally show "?U \<le> F ?U" .
  qed
qed

lemma gfp_transfer:
  assumes \<alpha>: "inf_continuous \<alpha>" and f: "inf_continuous f" and g: "inf_continuous g"
  assumes [simp]: "\<alpha> top = top" "\<And>x. \<alpha> (f x) = g (\<alpha> x)"
  shows "\<alpha> (gfp f) = gfp g"
proof -
  have "\<alpha> (gfp f) = (INF i. \<alpha> ((f^^i) top))"
    unfolding inf_continuous_gfp[OF f] by (intro f \<alpha> inf_continuousD antimono_funpow inf_continuous_mono)
  moreover have "\<alpha> ((f^^i) top) = (g^^i) top" for i
    by (induction i; simp)
  ultimately show ?thesis
    unfolding inf_continuous_gfp[OF g] by simp
qed

lemma gfp_transfer_bounded:
  assumes P: "P (f top)" "\<And>x. P x \<Longrightarrow> P (f x)" "\<And>M. antimono M \<Longrightarrow> (\<And>i. P (M i)) \<Longrightarrow> P (INF i::nat. M i)"
  assumes \<alpha>: "\<And>M. antimono M \<Longrightarrow> (\<And>i::nat. P (M i)) \<Longrightarrow> \<alpha> (INF i. M i) = (INF i. \<alpha> (M i))"
  assumes f: "inf_continuous f" and g: "inf_continuous g"
  assumes [simp]: "\<And>x. P x \<Longrightarrow> \<alpha> (f x) = g (\<alpha> x)"
  assumes g_bound: "\<And>x. g x \<le> \<alpha> (f top)"
  shows "\<alpha> (gfp f) = gfp g"
proof (rule antisym)
  note mono_g = inf_continuous_mono[OF g]

  have P_pow: "P ((f ^^ i) (f top))" for i
    by (induction i) (auto intro!: P)

  have antimono_pow: "antimono (\<lambda>i. (f ^^ i) top)"
    unfolding antimono_iff_le_Suc
  proof
    fix i show "(f ^^ Suc i) top \<le> (f ^^ i) top"
    proof (induct i)
      case Suc thus ?case using monoD[OF inf_continuous_mono[OF f] Suc] by auto
    qed (simp add: le_fun_def)
  qed
  have antimono_pow2: "antimono (\<lambda>i. (f ^^ i) (f top))"
  proof
    show "x \<le> y \<Longrightarrow> (f ^^ y) (f top) \<le> (f ^^ x) (f top)" for x y
      using antimono_pow[THEN antimonoD, of "Suc x" "Suc y"]
      unfolding funpow_Suc_right by simp
  qed

  have gfp_f: "gfp f = (INF i. (f ^^ i) (f top))"
    unfolding inf_continuous_gfp[OF f]
  proof (rule INF_eq)
    show "\<exists>j\<in>UNIV. (f ^^ j) (f top) \<le> (f ^^ i) top" for i
      by (intro bexI[of _ "i - 1"]) (auto simp: diff_Suc funpow_Suc_right simp del: funpow.simps(2) split: nat.split)
    show "\<exists>j\<in>UNIV. (f ^^ j) top \<le> (f ^^ i) (f top)" for i
      by (intro bexI[of _ "Suc i"]) (auto simp: funpow_Suc_right simp del: funpow.simps(2))
  qed

  have P_lfp: "P (gfp f)"
    unfolding gfp_f by (auto intro!: P P_pow antimono_pow2)

  have "\<alpha> (gfp f) = (INF i. \<alpha> ((f^^i) (f top)))"
    unfolding gfp_f by (rule \<alpha>) (auto intro!: P_pow antimono_pow2)
  also have "\<dots> \<ge> gfp g"
  proof (rule INF_greatest)
    fix i show "gfp g \<le> \<alpha> ((f^^i) (f top))"
    proof (induction i)
      case (Suc n) then show ?case
        by (subst gfp_unfold[OF mono_g]) (simp add: monoD[OF mono_g] P_pow)
    next
      case 0
      have "gfp g \<le> \<alpha> (f top)"
        by (subst gfp_unfold[OF mono_g]) (rule g_bound)
      then show ?case
        by simp
    qed
  qed
  finally show "gfp g \<le> \<alpha> (gfp f)" .

  show "\<alpha> (gfp f) \<le> gfp g"
  proof (induction rule: gfp_ordinal_induct[OF mono_g])
    case (1 S) then show ?case
      by (subst gfp_unfold[OF inf_continuous_mono[OF f]])
         (simp add: monoD[OF mono_g] P_lfp)
  qed (auto intro: Inf_greatest)
qed

subsubsection \<open>Least fixed points in countable complete lattices\<close>

definition (in countable_complete_lattice) cclfp :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "cclfp f = (SUP i. (f ^^ i) bot)"

lemma cclfp_unfold:
  assumes "sup_continuous F" shows "cclfp F = F (cclfp F)"
proof -
  have "cclfp F = (SUP i. F ((F ^^ i) bot))"
    unfolding cclfp_def
    by (subst UNIV_nat_eq) (simp add: image_comp)
  also have "\<dots> = F (cclfp F)"
    unfolding cclfp_def
    by (intro sup_continuousD[symmetric] assms mono_funpow sup_continuous_mono)
  finally show ?thesis .
qed

lemma cclfp_lowerbound: assumes f: "mono f" and A: "f A \<le> A" shows "cclfp f \<le> A"
  unfolding cclfp_def
proof (intro ccSUP_least)
  fix i show "(f ^^ i) bot \<le> A"
  proof (induction i)
    case (Suc i) from monoD[OF f this] A show ?case
      by auto
  qed simp
qed simp

lemma cclfp_transfer:
  assumes "sup_continuous \<alpha>" "mono f"
  assumes "\<alpha> bot = bot" "\<And>x. \<alpha> (f x) = g (\<alpha> x)"
  shows "\<alpha> (cclfp f) = cclfp g"
proof -
  have "\<alpha> (cclfp f) = (SUP i. \<alpha> ((f ^^ i) bot))"
    unfolding cclfp_def by (intro sup_continuousD assms mono_funpow sup_continuous_mono)
  moreover have "\<alpha> ((f ^^ i) bot) = (g ^^ i) bot" for i
    by (induction i) (simp_all add: assms)
  ultimately show ?thesis
    by (simp add: cclfp_def)
qed

end
