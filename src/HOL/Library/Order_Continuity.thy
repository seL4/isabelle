(*  Title:      HOL/Library/Order_Continuity.thy
    Author:     David von Oheimb, TU Muenchen
*)

section \<open>Continuity and iterations (of set transformers)\<close>

theory Order_Continuity
imports Main
begin

(* TODO: Generalize theory to chain-complete partial orders *)

lemma SUP_nat_binary:
  "(SUP n::nat. if n = 0 then A else B) = (sup A B::'a::complete_lattice)"
  apply (auto intro!: antisym SUP_least)
  apply (rule SUP_upper2[where i=0])
  apply simp_all
  apply (rule SUP_upper2[where i=1])
  apply simp_all
  done

lemma INF_nat_binary:
  "(INF n::nat. if n = 0 then A else B) = (inf A B::'a::complete_lattice)"
  apply (auto intro!: antisym INF_greatest)
  apply (rule INF_lower2[where i=0])
  apply simp_all
  apply (rule INF_lower2[where i=1])
  apply simp_all
  done

text \<open>
  The name @{text continuous} is already taken in @{text "Complex_Main"}, so we use
  @{text "sup_continuous"} and @{text "inf_continuous"}. These names appear sometimes in literature
  and have the advantage that these names are duals.
\<close>

subsection \<open>Continuity for complete lattices\<close>

definition
  sup_continuous :: "('a::complete_lattice \<Rightarrow> 'a::complete_lattice) \<Rightarrow> bool" where
  "sup_continuous F \<longleftrightarrow> (\<forall>M::nat \<Rightarrow> 'a. mono M \<longrightarrow> F (SUP i. M i) = (SUP i. F (M i)))"

lemma sup_continuousD: "sup_continuous F \<Longrightarrow> mono M \<Longrightarrow> F (SUP i::nat. M i) = (SUP i. F (M i))"
  by (auto simp: sup_continuous_def)

lemma sup_continuous_mono:
  fixes F :: "'a::complete_lattice \<Rightarrow> 'a::complete_lattice"
  assumes [simp]: "sup_continuous F" shows "mono F"
proof
  fix A B :: "'a" assume [simp]: "A \<le> B"
  have "F B = F (SUP n::nat. if n = 0 then A else B)"
    by (simp add: sup_absorb2 SUP_nat_binary)
  also have "\<dots> = (SUP n::nat. if n = 0 then F A else F B)"
    by (auto simp: sup_continuousD mono_def intro!: SUP_cong)
  finally show "F A \<le> F B"
    by (simp add: SUP_nat_binary le_iff_sup)
qed

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
      also have "\<dots> = lfp F" by (simp add: lfp_unfold[OF mono, symmetric])
      finally show ?case .
    qed simp
  qed
  show "lfp F \<le> ?U"
  proof (rule lfp_lowerbound)
    have "mono (\<lambda>i::nat. (F ^^ i) bot)"
    proof -
      { fix i::nat have "(F ^^ i) bot \<le> (F ^^ (Suc i)) bot"
        proof (induct i)
          case 0 show ?case by simp
        next
          case Suc thus ?case using monoD[OF mono Suc] by auto
        qed }
      thus ?thesis by (auto simp add: mono_iff_le_Suc)
    qed
    hence "F ?U = (SUP i. (F ^^ Suc i) bot)"
      using \<open>sup_continuous F\<close> by (simp add: sup_continuous_def)
    also have "\<dots> \<le> ?U"
      by (fast intro: SUP_least SUP_upper)
    finally show "F ?U \<le> ?U" .
  qed
qed

lemma lfp_transfer:
  assumes \<alpha>: "sup_continuous \<alpha>" and f: "sup_continuous f" and g: "sup_continuous g"
  assumes [simp]: "\<alpha> bot = bot" "\<And>x. \<alpha> (f x) = g (\<alpha> x)"
  shows "\<alpha> (lfp f) = lfp g"
proof -
  have "\<alpha> (lfp f) = (SUP i. \<alpha> ((f^^i) bot))"
    unfolding sup_continuous_lfp[OF f] by (intro f \<alpha> sup_continuousD mono_funpow sup_continuous_mono)
  moreover have "\<alpha> ((f^^i) bot) = (g^^i) bot" for i
    by (induction i; simp)
  ultimately show ?thesis
    unfolding sup_continuous_lfp[OF g] by simp
qed

definition
  inf_continuous :: "('a::complete_lattice \<Rightarrow> 'a::complete_lattice) \<Rightarrow> bool" where
  "inf_continuous F \<longleftrightarrow> (\<forall>M::nat \<Rightarrow> 'a. antimono M \<longrightarrow> F (INF i. M i) = (INF i. F (M i)))"

lemma inf_continuousD: "inf_continuous F \<Longrightarrow> antimono M \<Longrightarrow> F (INF i::nat. M i) = (INF i. F (M i))"
  by (auto simp: inf_continuous_def)

lemma inf_continuous_mono:
  fixes F :: "'a::complete_lattice \<Rightarrow> 'a::complete_lattice"
  assumes [simp]: "inf_continuous F" shows "mono F"
proof
  fix A B :: "'a" assume [simp]: "A \<le> B"
  have "F A = F (INF n::nat. if n = 0 then B else A)"
    by (simp add: inf_absorb2 INF_nat_binary)
  also have "\<dots> = (INF n::nat. if n = 0 then F B else F A)"
    by (auto simp: inf_continuousD antimono_def intro!: INF_cong)
  finally show "F A \<le> F B"
    by (simp add: INF_nat_binary le_iff_inf inf_commute)
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
      have "gfp F = F (gfp F)" by (simp add: gfp_unfold[OF mono, symmetric])
      also have "\<dots> \<le> F ((F ^^ i) top)" by (rule monoD[OF mono Suc])
      also have "\<dots> = (F ^^ Suc i) top" by simp
      finally show ?case .
    qed simp
  qed
  show "?U \<le> gfp F"
  proof (rule gfp_upperbound)
    have *: "antimono (\<lambda>i::nat. (F ^^ i) top)"
    proof -
      { fix i::nat have "(F ^^ Suc i) top \<le> (F ^^ i) top"
        proof (induct i)
          case 0 show ?case by simp
        next
          case Suc thus ?case using monoD[OF mono Suc] by auto
        qed }
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

end
