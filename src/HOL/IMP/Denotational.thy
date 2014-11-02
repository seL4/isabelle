(* Authors: Heiko Loetzbeyer, Robert Sandner, Tobias Nipkow *)

section "Denotational Semantics of Commands"

theory Denotational imports Big_Step begin

type_synonym com_den = "(state \<times> state) set"

definition W :: "(state \<Rightarrow> bool) \<Rightarrow> com_den \<Rightarrow> (com_den \<Rightarrow> com_den)" where
"W db dc = (\<lambda>dw. {(s,t). if db s then (s,t) \<in> dc O dw else s=t})"

fun D :: "com \<Rightarrow> com_den" where
"D SKIP   = Id" |
"D (x ::= a) = {(s,t). t = s(x := aval a s)}" |
"D (c1;;c2)  = D(c1) O D(c2)" |
"D (IF b THEN c1 ELSE c2)
 = {(s,t). if bval b s then (s,t) \<in> D c1 else (s,t) \<in> D c2}" |
"D (WHILE b DO c) = lfp (W (bval b) (D c))"

lemma W_mono: "mono (W b r)"
by (unfold W_def mono_def) auto

lemma D_While_If:
  "D(WHILE b DO c) = D(IF b THEN c;;WHILE b DO c ELSE SKIP)"
proof-
  let ?w = "WHILE b DO c" let ?f = "W (bval b) (D c)"
  have "D ?w = lfp ?f" by simp
  also have "\<dots> = ?f (lfp ?f)" by(rule lfp_unfold [OF W_mono])
  also have "\<dots> = D(IF b THEN c;;?w ELSE SKIP)" by (simp add: W_def)
  finally show ?thesis .
qed

text{* Equivalence of denotational and big-step semantics: *}

lemma D_if_big_step:  "(c,s) \<Rightarrow> t \<Longrightarrow> (s,t) \<in> D(c)"
proof (induction rule: big_step_induct)
  case WhileFalse
  with D_While_If show ?case by auto
next
  case WhileTrue
  show ?case unfolding D_While_If using WhileTrue by auto
qed auto

abbreviation Big_step :: "com \<Rightarrow> com_den" where
"Big_step c \<equiv> {(s,t). (c,s) \<Rightarrow> t}"

lemma Big_step_if_D:  "(s,t) \<in> D(c) \<Longrightarrow> (s,t) : Big_step c"
proof (induction c arbitrary: s t)
  case Seq thus ?case by fastforce
next
  case (While b c)
  let ?B = "Big_step (WHILE b DO c)" let ?f = "W (bval b) (D c)"
  have "?f ?B \<subseteq> ?B" using While.IH by (auto simp: W_def)
  from lfp_lowerbound[where ?f = "?f", OF this] While.prems
  show ?case by auto
qed (auto split: if_splits)

theorem denotational_is_big_step:
  "(s,t) \<in> D(c)  =  ((c,s) \<Rightarrow> t)"
by (metis D_if_big_step Big_step_if_D[simplified])

corollary equiv_c_iff_equal_D: "(c1 \<sim> c2) \<longleftrightarrow> D c1 = D c2"
by(simp add: denotational_is_big_step[symmetric] set_eq_iff)


subsection "Continuity"

definition chain :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool" where
"chain S = (\<forall>i. S i \<subseteq> S(Suc i))"

lemma chain_total: "chain S \<Longrightarrow> S i \<le> S j \<or> S j \<le> S i"
by (metis chain_def le_cases lift_Suc_mono_le)

definition cont :: "('a set \<Rightarrow> 'b set) \<Rightarrow> bool" where
"cont f = (\<forall>S. chain S \<longrightarrow> f(UN n. S n) = (UN n. f(S n)))"

lemma mono_if_cont: fixes f :: "'a set \<Rightarrow> 'b set"
  assumes "cont f" shows "mono f"
proof
  fix a b :: "'a set" assume "a \<subseteq> b"
  let ?S = "\<lambda>n::nat. if n=0 then a else b"
  have "chain ?S" using `a \<subseteq> b` by(auto simp: chain_def)
  hence "f(UN n. ?S n) = (UN n. f(?S n))"
    using assms by(simp add: cont_def)
  moreover have "(UN n. ?S n) = b" using `a \<subseteq> b` by (auto split: if_splits)
  moreover have "(UN n. f(?S n)) = f a \<union> f b" by (auto split: if_splits)
  ultimately show "f a \<subseteq> f b" by (metis Un_upper1)
qed

lemma chain_iterates: fixes f :: "'a set \<Rightarrow> 'a set"
  assumes "mono f" shows "chain(\<lambda>n. (f^^n) {})"
proof-
  { fix n have "(f ^^ n) {} \<subseteq> (f ^^ Suc n) {}" using assms
    by(induction n) (auto simp: mono_def) }
  thus ?thesis by(auto simp: chain_def)
qed

theorem lfp_if_cont:
  assumes "cont f" shows "lfp f = (UN n. (f^^n) {})" (is "_ = ?U")
proof
  show "lfp f \<subseteq> ?U"
  proof (rule lfp_lowerbound)
    have "f ?U = (UN n. (f^^Suc n){})"
      using chain_iterates[OF mono_if_cont[OF assms]] assms
      by(simp add: cont_def)
    also have "\<dots> = (f^^0){} \<union> \<dots>" by simp
    also have "\<dots> = ?U"
      by(auto simp del: funpow.simps) (metis not0_implies_Suc)
    finally show "f ?U \<subseteq> ?U" by simp
  qed
next
  { fix n p assume "f p \<subseteq> p"
    have "(f^^n){} \<subseteq> p"
    proof(induction n)
      case 0 show ?case by simp
    next
      case Suc
      from monoD[OF mono_if_cont[OF assms] Suc] `f p \<subseteq> p`
      show ?case by simp
    qed
  }
  thus "?U \<subseteq> lfp f" by(auto simp: lfp_def)
qed

lemma cont_W: "cont(W b r)"
by(auto simp: cont_def W_def)


subsection{*The denotational semantics is deterministic*}

lemma single_valued_UN_chain:
  assumes "chain S" "(\<And>n. single_valued (S n))"
  shows "single_valued(UN n. S n)"
proof(auto simp: single_valued_def)
  fix m n x y z assume "(x, y) \<in> S m" "(x, z) \<in> S n"
  with chain_total[OF assms(1), of m n] assms(2)
  show "y = z" by (auto simp: single_valued_def)
qed

lemma single_valued_lfp: fixes f :: "com_den \<Rightarrow> com_den"
assumes "cont f" "\<And>r. single_valued r \<Longrightarrow> single_valued (f r)"
shows "single_valued(lfp f)"
unfolding lfp_if_cont[OF assms(1)]
proof(rule single_valued_UN_chain[OF chain_iterates[OF mono_if_cont[OF assms(1)]]])
  fix n show "single_valued ((f ^^ n) {})"
  by(induction n)(auto simp: assms(2))
qed

lemma single_valued_D: "single_valued (D c)"
proof(induction c)
  case Seq thus ?case by(simp add: single_valued_relcomp)
next
  case (While b c)
  let ?f = "W (bval b) (D c)"
  have "single_valued (lfp ?f)"
  proof(rule single_valued_lfp[OF cont_W])
    show "\<And>r. single_valued r \<Longrightarrow> single_valued (?f r)"
      using While.IH by(force simp: single_valued_def W_def)
  qed
  thus ?case by simp
qed (auto simp add: single_valued_def)

end
