(*  Title:      HOL/Infnite_Set.thy
    ID:         $Id$
    Author:     Stefan Merz 
*)

header {* Infnite Sets and Related Concepts*}

theory Infinite_Set = Hilbert_Choice + Finite_Set + SetInterval:

subsection "Infinite Sets"

text {* Some elementary facts about infinite sets, by Stefan Merz. *}

syntax
  infinite :: "'a set \<Rightarrow> bool"
translations
  "infinite S" == "S \<notin> Finites"

text {*
  Infinite sets are non-empty, and if we remove some elements
  from an infinite set, the result is still infinite.
*}

lemma infinite_nonempty:
  "\<not> (infinite {})"
by simp

lemma infinite_remove:
  "infinite S \<Longrightarrow> infinite (S - {a})"
by simp

lemma Diff_infinite_finite:
  assumes T: "finite T" and S: "infinite S"
  shows "infinite (S-T)"
using T
proof (induct)
  from S
  show "infinite (S - {})" by auto
next
  fix T x
  assume ih: "infinite (S-T)"
  have "S - (insert x T) = (S-T) - {x}"
    by (rule Diff_insert)
  with ih
  show "infinite (S - (insert x T))"
    by (simp add: infinite_remove)
qed

lemma Un_infinite:
  "infinite S \<Longrightarrow> infinite (S \<union> T)"
by simp

lemma infinite_super:
  assumes T: "S \<subseteq> T" and S: "infinite S"
  shows "infinite T"
proof (rule ccontr)
  assume "\<not>(infinite T)"
  with T
  have "finite S" by (simp add: finite_subset)
  with S
  show False by simp
qed

text {*
  As a concrete example, we prove that the set of natural
  numbers is infinite.
*}

lemma finite_nat_bounded:
  assumes S: "finite (S::nat set)"
  shows "\<exists>k. S \<subseteq> {..k(}" (is "\<exists>k. ?bounded S k")
using S
proof (induct)
  have "?bounded {} 0" by simp
  thus "\<exists>k. ?bounded {} k" ..
next
  fix S x
  assume "\<exists>k. ?bounded S k"
  then obtain k where k: "?bounded S k" ..
  show "\<exists>k. ?bounded (insert x S) k"
  proof (cases "x<k")
    case True
    with k show ?thesis by auto
  next
    case False
    with k have "?bounded S (Suc x)" by auto
    thus ?thesis by auto
  qed
qed

lemma finite_nat_iff_bounded:
  "finite (S::nat set) = (\<exists>k. S \<subseteq> {..k(})" (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs by (rule finite_nat_bounded)
next
  assume ?rhs
  then obtain k where "S \<subseteq> {..k(}" ..
  thus "finite S"
    by (rule finite_subset, simp)
qed

lemma finite_nat_iff_bounded_le:
  "finite (S::nat set) = (\<exists>k. S \<subseteq> {..k})" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain k where "S \<subseteq> {..k(}" 
    by (blast dest: finite_nat_bounded)
  hence "S \<subseteq> {..k}" by auto
  thus ?rhs ..
next
  assume ?rhs
  then obtain k where "S \<subseteq> {..k}" ..
  thus "finite S"
    by (rule finite_subset, simp)
qed

lemma infinite_nat_iff_unbounded:
  "infinite (S::nat set) = (\<forall>m. \<exists>n. m<n \<and> n\<in>S)"
  (is "?lhs = ?rhs")
proof
  assume inf: ?lhs
  show ?rhs
  proof (rule ccontr)
    assume "\<not> ?rhs"
    then obtain m where m: "\<forall>n. m<n \<longrightarrow> n\<notin>S" by blast
    hence "S \<subseteq> {..m}"
      by (auto simp add: sym[OF not_less_iff_le])
    with inf show "False" 
      by (simp add: finite_nat_iff_bounded_le)
  qed
next
  assume unbounded: ?rhs
  show ?lhs
  proof
    assume "finite S"
    then obtain m where "S \<subseteq> {..m}"
      by (auto simp add: finite_nat_iff_bounded_le)
    hence "\<forall>n. m<n \<longrightarrow> n\<notin>S" by auto
    with unbounded show "False" by blast
  qed
qed

lemma infinite_nat_iff_unbounded_le:
  "infinite (S::nat set) = (\<forall>m. \<exists>n. m\<le>n \<and> n\<in>S)"
  (is "?lhs = ?rhs")
proof
  assume inf: ?lhs
  show ?rhs
  proof
    fix m
    from inf obtain n where "m<n \<and> n\<in>S"
      by (auto simp add: infinite_nat_iff_unbounded)
    hence "m\<le>n \<and> n\<in>S" by auto
    thus "\<exists>n. m \<le> n \<and> n \<in> S" ..
  qed
next
  assume unbounded: ?rhs
  show ?lhs
  proof (auto simp add: infinite_nat_iff_unbounded)
    fix m
    from unbounded obtain n where "(Suc m)\<le>n \<and> n\<in>S"
      by blast
    hence "m<n \<and> n\<in>S" by auto
    thus "\<exists>n. m < n \<and> n \<in> S" ..
  qed
qed

text {*
  For a set of natural numbers to be infinite, it is enough
  to know that for any number larger than some $k$, there
  is some larger number that is an element of the set.
*}

lemma unbounded_k_infinite:
  assumes k: "\<forall>m. k<m \<longrightarrow> (\<exists>n. m<n \<and> n\<in>S)"
  shows "infinite (S::nat set)"
proof (auto simp add: infinite_nat_iff_unbounded)
  fix m show "\<exists>n. m<n \<and> n\<in>S"
  proof (cases "k<m")
    case True
    with k show ?thesis by blast
  next
    case False
    from k obtain n where "Suc k < n \<and> n\<in>S" by auto
    with False have "m<n \<and> n\<in>S" by auto
    thus ?thesis ..
  qed
qed

theorem nat_infinite [simp]:
  "infinite (UNIV :: nat set)"
by (auto simp add: infinite_nat_iff_unbounded)

theorem nat_not_finite [elim]:
  "finite (UNIV::nat set) \<Longrightarrow> R"
by simp

text {*
  Every infinite set contains a countable subset. More precisely
  we show that a set $S$ is infinite if and only if there exists 
  an injective function from the naturals into $S$.
*}

lemma range_inj_infinite:
  "inj (f::nat \<Rightarrow> 'a) \<Longrightarrow> infinite (range f)"
proof
  assume "inj f"
    and  "finite (range f)"
  hence "finite (UNIV::nat set)"
    by (auto intro: finite_imageD simp del: nat_infinite)
  thus "False" by simp
qed

text {*
  The ``only if'' direction is harder because it requires the
  construction of a sequence of pairwise different elements of
  an infinite set $S$. The idea is to construct a sequence of
  non-empty and infinite subsets of $S$ obtained by successively
  removing elements of $S$.
*}

lemma linorder_injI:
  assumes hyp: "\<forall>x y. x < (y::'a::linorder) \<longrightarrow> f x \<noteq> f y"
  shows "inj f"
proof (rule inj_onI)
  fix x y
  assume f_eq: "f x = f y"
  show "x = y"
  proof (rule linorder_cases)
    assume "x < y"
    with hyp have "f x \<noteq> f y" by blast
    with f_eq show ?thesis by simp
  next
    assume "x = y"
    thus ?thesis .
  next
    assume "y < x"
    with hyp have "f y \<noteq> f x" by blast
    with f_eq show ?thesis by simp
  qed
qed

lemma infinite_countable_subset:
  assumes inf: "infinite (S::'a set)"
  shows "\<exists>f. inj (f::nat \<Rightarrow> 'a) \<and> range f \<subseteq> S"
proof -
  def Sseq \<equiv> "nat_rec S (\<lambda>n T. T - {\<epsilon> e. e \<in> T})"
  def pick \<equiv> "\<lambda>n. (\<epsilon> e. e \<in> Sseq n)"
  have Sseq_inf: "\<And>n. infinite (Sseq n)"
  proof -
    fix n
    show "infinite (Sseq n)"
    proof (induct n)
      from inf show "infinite (Sseq 0)"
	by (simp add: Sseq_def)
    next
      fix n
      assume "infinite (Sseq n)" thus "infinite (Sseq (Suc n))"
	by (simp add: Sseq_def infinite_remove)
    qed
  qed
  have Sseq_S: "\<And>n. Sseq n \<subseteq> S"
  proof -
    fix n
    show "Sseq n \<subseteq> S"
      by (induct n, auto simp add: Sseq_def)
  qed
  have Sseq_pick: "\<And>n. pick n \<in> Sseq n"
  proof -
    fix n
    show "pick n \<in> Sseq n"
    proof (unfold pick_def, rule someI_ex)
      from Sseq_inf have "infinite (Sseq n)" .
      hence "Sseq n \<noteq> {}" by auto
      thus "\<exists>x. x \<in> Sseq n" by auto
    qed
  qed
  with Sseq_S have rng: "range pick \<subseteq> S"
    by auto
  have pick_Sseq_gt: "\<And>n m. pick n \<notin> Sseq (n + Suc m)"
  proof -
    fix n m
    show "pick n \<notin> Sseq (n + Suc m)"
      by (induct m, auto simp add: Sseq_def pick_def)
  qed
  have pick_pick: "\<And>n m. pick n \<noteq> pick (n + Suc m)"
  proof -
    fix n m
    from Sseq_pick have "pick (n + Suc m) \<in> Sseq (n + Suc m)" .
    moreover from pick_Sseq_gt
    have "pick n \<notin> Sseq (n + Suc m)" .
    ultimately show "pick n \<noteq> pick (n + Suc m)"
      by auto
  qed
  have inj: "inj pick"
  proof (rule linorder_injI)
    show "\<forall>i j. i<(j::nat) \<longrightarrow> pick i \<noteq> pick j"
    proof (clarify)
      fix i j
      assume ij: "i<(j::nat)"
	and eq: "pick i = pick j"
      from ij obtain k where "j = i + (Suc k)"
	by (auto simp add: less_iff_Suc_add)
      with pick_pick have "pick i \<noteq> pick j" by simp
      with eq show "False" by simp
    qed
  qed
  from rng inj show ?thesis by auto
qed

theorem infinite_iff_countable_subset:
  "infinite S = (\<exists>f. inj (f::nat \<Rightarrow> 'a) \<and> range f \<subseteq> S)"
  (is "?lhs = ?rhs")
by (auto simp add: infinite_countable_subset
                   range_inj_infinite infinite_super)

text {*
  For any function with infinite domain and finite range
  there is some element that is the image of infinitely
  many domain elements. In particular, any infinite sequence
  of elements from a finite set contains some element that
  occurs infinitely often.
*}

theorem inf_img_fin_dom:
  assumes img: "finite (f`A)" and dom: "infinite A"
  shows "\<exists>y \<in> f`A. infinite (f -` {y})"
proof (rule ccontr)
  assume "\<not> (\<exists>y\<in>f ` A. infinite (f -` {y}))"
  with img have "finite (UN y:f`A. f -` {y})"
    by (blast intro: finite_UN_I)
  moreover have "A \<subseteq> (UN y:f`A. f -` {y})" by auto
  moreover note dom
  ultimately show "False"
    by (simp add: infinite_super)
qed

theorems inf_img_fin_domE = inf_img_fin_dom[THEN bexE]


subsection "Infinitely Many and Almost All"

text {*
  We often need to reason about the existence of infinitely many
  (resp., all but finitely many) objects satisfying some predicate,
  so we introduce corresponding binders and their proof rules.
*}

consts
  Inf_many :: "('a \<Rightarrow> bool) \<Rightarrow> bool"      (binder "INF " 10)
  Alm_all  :: "('a \<Rightarrow> bool) \<Rightarrow> bool"      (binder "MOST " 10)

defs
  INF_def:  "Inf_many P \<equiv> infinite {x. P x}"
  MOST_def: "Alm_all P \<equiv> \<not>(INF x. \<not> P x)"

syntax (xsymbols)
  "MOST " :: "[idts, bool] \<Rightarrow> bool"       ("(3\<forall>\<^sub>\<infinity>_./ _)" [0,10] 10)
  "INF "    :: "[idts, bool] \<Rightarrow> bool"     ("(3\<exists>\<^sub>\<infinity>_./ _)" [0,10] 10)

syntax (HTML output)
  "MOST " :: "[idts, bool] \<Rightarrow> bool"       ("(3\<forall>\<^sub>\<infinity>_./ _)" [0,10] 10)
  "INF "    :: "[idts, bool] \<Rightarrow> bool"     ("(3\<exists>\<^sub>\<infinity>_./ _)" [0,10] 10)

lemma INF_EX:
  "(\<exists>\<^sub>\<infinity>x. P x) \<Longrightarrow> (\<exists>x. P x)"
proof (unfold INF_def, rule ccontr)
  assume inf: "infinite {x. P x}"
    and notP: "\<not>(\<exists>x. P x)"
  from notP have "{x. P x} = {}" by simp
  hence "finite {x. P x}" by simp
  with inf show "False" by simp
qed

lemma MOST_iff_finiteNeg:
  "(\<forall>\<^sub>\<infinity>x. P x) = finite {x. \<not> P x}"
by (simp add: MOST_def INF_def)

lemma ALL_MOST:
  "\<forall>x. P x \<Longrightarrow> \<forall>\<^sub>\<infinity>x. P x"
by (simp add: MOST_iff_finiteNeg)

lemma INF_mono:
  assumes inf: "\<exists>\<^sub>\<infinity>x. P x" and q: "\<And>x. P x \<Longrightarrow> Q x"
  shows "\<exists>\<^sub>\<infinity>x. Q x"
proof -
  from inf have "infinite {x. P x}" by (unfold INF_def)
  moreover from q have "{x. P x} \<subseteq> {x. Q x}" by auto
  ultimately show ?thesis
    by (simp add: INF_def infinite_super)
qed

lemma MOST_mono:
  "\<lbrakk> \<forall>\<^sub>\<infinity>x. P x; \<And>x. P x \<Longrightarrow> Q x \<rbrakk> \<Longrightarrow> \<forall>\<^sub>\<infinity>x. Q x"
by (unfold MOST_def, blast intro: INF_mono)

lemma INF_nat: "(\<exists>\<^sub>\<infinity>n. P (n::nat)) = (\<forall>m. \<exists>n. m<n \<and> P n)"
by (simp add: INF_def infinite_nat_iff_unbounded)

lemma INF_nat_le: "(\<exists>\<^sub>\<infinity>n. P (n::nat)) = (\<forall>m. \<exists>n. m\<le>n \<and> P n)"
by (simp add: INF_def infinite_nat_iff_unbounded_le)

lemma MOST_nat: "(\<forall>\<^sub>\<infinity>n. P (n::nat)) = (\<exists>m. \<forall>n. m<n \<longrightarrow> P n)"
by (simp add: MOST_def INF_nat)

lemma MOST_nat_le: "(\<forall>\<^sub>\<infinity>n. P (n::nat)) = (\<exists>m. \<forall>n. m\<le>n \<longrightarrow> P n)"
by (simp add: MOST_def INF_nat_le)


subsection "Miscellaneous"

text {*
  A few trivial lemmas about sets that contain at most one element.
  These simplify the reasoning about deterministic automata.
*}

constdefs
  atmost_one :: "'a set \<Rightarrow> bool"
  "atmost_one S \<equiv> \<forall>x y. x\<in>S \<and> y\<in>S \<longrightarrow> x=y"

lemma atmost_one_empty: "S={} \<Longrightarrow> atmost_one S"
by (simp add: atmost_one_def)

lemma atmost_one_singleton: "S = {x} \<Longrightarrow> atmost_one S"
by (simp add: atmost_one_def)

lemma atmost_one_unique [elim]: "\<lbrakk> atmost_one S; x \<in> S; y \<in> S \<rbrakk> \<Longrightarrow> y=x"
by (simp add: atmost_one_def)

end
