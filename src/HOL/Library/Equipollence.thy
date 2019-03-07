section \<open>Equipollence and Other Relations Connected with Cardinality\<close>

theory "Equipollence"
  imports FuncSet
begin

subsection\<open>Eqpoll\<close>

definition eqpoll :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infixl "\<approx>" 50)
  where "eqpoll A B \<equiv> \<exists>f. bij_betw f A B"

definition lepoll :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infixl "\<lesssim>" 50)
  where "lepoll A B \<equiv> \<exists>f. inj_on f A \<and> f ` A \<subseteq> B"

definition lesspoll :: "'a set \<Rightarrow> 'b set \<Rightarrow> bool" (infixl \<open>\<prec>\<close> 50)
  where "A \<prec> B == A \<lesssim> B \<and> ~(A \<approx> B)"

lemma lepoll_empty_iff_empty [simp]: "A \<lesssim> {} \<longleftrightarrow> A = {}"
  by (auto simp: lepoll_def)

lemma eqpoll_iff_card_of_ordIso: "A \<approx> B \<longleftrightarrow> ordIso2 (card_of A) (card_of B)"
  by (simp add: card_of_ordIso eqpoll_def)

lemma eqpoll_finite_iff: "A \<approx> B \<Longrightarrow> finite A \<longleftrightarrow> finite B"
  by (meson bij_betw_finite eqpoll_def)

lemma eqpoll_iff_card:
  assumes "finite A" "finite B"
  shows  "A \<approx> B \<longleftrightarrow> card A = card B"
  using assms by (auto simp: bij_betw_iff_card eqpoll_def)

lemma lepoll_antisym:
  assumes "A \<lesssim> B" "B \<lesssim> A" shows "A \<approx> B"
  using assms unfolding eqpoll_def lepoll_def by (metis Schroeder_Bernstein)

lemma lepoll_trans [trans]: "\<lbrakk>A \<lesssim> B; B \<lesssim> C\<rbrakk> \<Longrightarrow> A \<lesssim> C"
  apply (clarsimp simp: lepoll_def)
  apply (rename_tac f g)
  apply (rule_tac x="g \<circ> f" in exI)
  apply (auto simp: image_subset_iff inj_on_def)
  done

lemma lepoll_trans1 [trans]: "\<lbrakk>A \<approx> B; B \<lesssim> C\<rbrakk> \<Longrightarrow> A \<lesssim> C"
  by (meson card_of_ordLeq eqpoll_iff_card_of_ordIso lepoll_def lepoll_trans ordIso_iff_ordLeq)

lemma lepoll_trans2 [trans]: "\<lbrakk>A \<lesssim> B; B \<approx> C\<rbrakk> \<Longrightarrow> A \<lesssim> C"
  apply (clarsimp simp: eqpoll_def lepoll_def bij_betw_def)
  apply (rename_tac f g)
  apply (rule_tac x="g \<circ> f" in exI)
  apply (auto simp: image_subset_iff inj_on_def)
  done

lemma eqpoll_sym: "A \<approx> B \<Longrightarrow> B \<approx> A"
  unfolding eqpoll_def
  using bij_betw_the_inv_into by auto

lemma eqpoll_trans [trans]: "\<lbrakk>A \<approx> B; B \<approx> C\<rbrakk> \<Longrightarrow> A \<approx> C"
  unfolding eqpoll_def using bij_betw_trans by blast

lemma eqpoll_imp_lepoll: "A \<approx> B \<Longrightarrow> A \<lesssim> B"
  unfolding eqpoll_def lepoll_def by (metis bij_betw_def order_refl)

lemma subset_imp_lepoll: "A \<subseteq> B \<Longrightarrow> A \<lesssim> B"
  by (force simp: lepoll_def)

lemma lepoll_iff: "A \<lesssim> B \<longleftrightarrow> (\<exists>g. A \<subseteq> g ` B)"
  unfolding lepoll_def
proof safe
  fix g assume "A \<subseteq> g ` B"
  then show "\<exists>f. inj_on f A \<and> f ` A \<subseteq> B"
    by (rule_tac x="inv_into B g" in exI) (auto simp: inv_into_into inj_on_inv_into)
qed (metis image_mono the_inv_into_onto)

lemma subset_image_lepoll: "B \<subseteq> f ` A \<Longrightarrow> B \<lesssim> A"
  by (auto simp: lepoll_iff)

lemma image_lepoll: "f ` A \<lesssim> A"
  by (auto simp: lepoll_iff)

lemma infinite_le_lepoll: "infinite A \<longleftrightarrow> (UNIV::nat set) \<lesssim> A"
apply (auto simp: lepoll_def)
  apply (simp add: infinite_countable_subset)
  using infinite_iff_countable_subset by blast

lemma bij_betw_iff_bijections:
  "bij_betw f A B \<longleftrightarrow> (\<exists>g. (\<forall>x \<in> A. f x \<in> B \<and> g(f x) = x) \<and> (\<forall>y \<in> B. g y \<in> A \<and> f(g y) = y))"
  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then show ?rhs
    apply (rule_tac x="the_inv_into A f" in exI)
    apply (auto simp: bij_betw_def f_the_inv_into_f the_inv_into_f_f the_inv_into_into)
    done
next
  assume ?rhs
  then show ?lhs
    by (auto simp: bij_betw_def inj_on_def image_def; metis)
qed

lemma eqpoll_iff_bijections:
   "A \<approx> B \<longleftrightarrow> (\<exists>f g. (\<forall>x \<in> A. f x \<in> B \<and> g(f x) = x) \<and> (\<forall>y \<in> B. g y \<in> A \<and> f(g y) = y))"
    by (auto simp: eqpoll_def bij_betw_iff_bijections)

lemma lepoll_restricted_funspace:
   "{f. f ` A \<subseteq> B \<and> {x. f x \<noteq> k x} \<subseteq> A \<and> finite {x. f x \<noteq> k x}} \<lesssim> Fpow (A \<times> B)"
proof -
  have *: "\<exists>U \<in> Fpow (A \<times> B). f = (\<lambda>x. if \<exists>y. (x, y) \<in> U then SOME y. (x,y) \<in> U else k x)"
    if "f ` A \<subseteq> B" "{x. f x \<noteq> k x} \<subseteq> A" "finite {x. f x \<noteq> k x}" for f
    apply (rule_tac x="(\<lambda>x. (x, f x)) ` {x. f x \<noteq> k x}" in bexI)
    using that by (auto simp: image_def Fpow_def)
  show ?thesis
    apply (rule subset_image_lepoll [where f = "\<lambda>U x. if \<exists>y. (x,y) \<in> U then @y. (x,y) \<in> U else k x"])
    using * by (auto simp: image_def)
qed

lemma singleton_lepoll: "{x} \<lesssim> insert y A"
  by (force simp: lepoll_def)

lemma singleton_eqpoll: "{x} \<approx> {y}"
  by (blast intro: lepoll_antisym singleton_lepoll)

lemma subset_singleton_iff_lepoll: "(\<exists>x. S \<subseteq> {x}) \<longleftrightarrow> S \<lesssim> {()}"
proof safe
  show "S \<lesssim> {()}" if "S \<subseteq> {x}" for x
    using subset_imp_lepoll [OF that] by (simp add: singleton_eqpoll lepoll_trans2)
  show "\<exists>x. S \<subseteq> {x}" if "S \<lesssim> {()}"
  by (metis (no_types, hide_lams) image_empty image_insert lepoll_iff that)
qed


subsection\<open>The strict relation\<close>

lemma lesspoll_not_refl [iff]: "~ (i \<prec> i)"
  by (simp add: lepoll_antisym lesspoll_def)

lemma lesspoll_imp_lepoll: "A \<prec> B ==> A \<lesssim> B"
by (unfold lesspoll_def, blast)

lemma lepoll_iff_leqpoll: "A \<lesssim> B \<longleftrightarrow> A \<prec> B | A \<approx> B"
  using eqpoll_imp_lepoll lesspoll_def by blast

lemma lesspoll_trans [trans]: "\<lbrakk>X \<prec> Y; Y \<prec> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  by (meson eqpoll_sym lepoll_antisym lepoll_trans lepoll_trans1 lesspoll_def)

lemma lesspoll_trans1 [trans]: "\<lbrakk>X \<lesssim> Y; Y \<prec> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  by (meson eqpoll_sym lepoll_antisym lepoll_trans lepoll_trans1 lesspoll_def)

lemma lesspoll_trans2 [trans]: "\<lbrakk>X \<prec> Y; Y \<lesssim> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  by (meson eqpoll_imp_lepoll eqpoll_sym lepoll_antisym lepoll_trans lesspoll_def)

lemma eq_lesspoll_trans [trans]: "\<lbrakk>X \<approx> Y; Y \<prec> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  using eqpoll_imp_lepoll lesspoll_trans1 by blast

lemma lesspoll_eq_trans [trans]: "\<lbrakk>X \<prec> Y; Y \<approx> Z\<rbrakk> \<Longrightarrow> X \<prec> Z"
  using eqpoll_imp_lepoll lesspoll_trans2 by blast

subsection\<open>Cartesian products\<close>

lemma PiE_sing_eqpoll_self: "({a} \<rightarrow>\<^sub>E B) \<approx> B"
proof -
  have 1: "x = y"
    if "x \<in> {a} \<rightarrow>\<^sub>E B" "y \<in> {a} \<rightarrow>\<^sub>E B" "x a = y a" for x y
    by (metis IntD2 PiE_def extensionalityI singletonD that)
  have 2: "x \<in> (\<lambda>h. h a) ` ({a} \<rightarrow>\<^sub>E B)" if "x \<in> B" for x
    using that by (rule_tac x="\<lambda>z\<in>{a}. x" in image_eqI) auto
  show ?thesis
  unfolding eqpoll_def bij_betw_def inj_on_def
  by (force intro: 1 2)
qed

lemma lepoll_funcset_right:
   "B \<lesssim> B' \<Longrightarrow> A \<rightarrow>\<^sub>E B \<lesssim> A \<rightarrow>\<^sub>E B'"
  apply (auto simp: lepoll_def inj_on_def)
  apply (rule_tac x = "\<lambda>g. \<lambda>z \<in> A. f(g z)" in exI)
  apply (auto simp: fun_eq_iff)
  apply (metis PiE_E)
  by blast

lemma lepoll_funcset_left:
  assumes "B \<noteq> {}" "A \<lesssim> A'"
  shows "A \<rightarrow>\<^sub>E B \<lesssim> A' \<rightarrow>\<^sub>E B"
proof -
  obtain b where "b \<in> B"
    using assms by blast
  obtain f where "inj_on f A" and fim: "f ` A \<subseteq> A'"
    using assms by (auto simp: lepoll_def)
  then obtain h where h: "\<And>x. x \<in> A \<Longrightarrow> h (f x) = x"
    using the_inv_into_f_f by fastforce
  let ?F = "\<lambda>g. \<lambda>u \<in> A'. if h u \<in> A then g(h u) else b"
  show ?thesis
    unfolding lepoll_def inj_on_def
  proof (intro exI conjI ballI impI ext)
    fix k l x
    assume k: "k \<in> A \<rightarrow>\<^sub>E B" and l: "l \<in> A \<rightarrow>\<^sub>E B" and "?F k = ?F l"
    then have "?F k (f x) = ?F l (f x)"
      by simp
    then show "k x = l x"
      apply (auto simp: h split: if_split_asm)
      apply (metis PiE_arb h k l)
      apply (metis (full_types) PiE_E h k l)
      using fim k l by fastforce
  next
    show "?F ` (A \<rightarrow>\<^sub>E B) \<subseteq> A' \<rightarrow>\<^sub>E B"
      using \<open>b \<in> B\<close> by force
  qed
qed

lemma lepoll_funcset:
   "\<lbrakk>B \<noteq> {}; A \<lesssim> A'; B \<lesssim> B'\<rbrakk> \<Longrightarrow> A \<rightarrow>\<^sub>E B \<lesssim> A' \<rightarrow>\<^sub>E B'"
  by (rule lepoll_trans [OF lepoll_funcset_right lepoll_funcset_left]) auto

lemma lepoll_PiE:
  assumes "\<And>i. i \<in> A \<Longrightarrow> B i \<lesssim> C i"
  shows "PiE A B \<lesssim> PiE A C"
proof -
  obtain f where f: "\<And>i. i \<in> A \<Longrightarrow> inj_on (f i) (B i) \<and> (f i) ` B i \<subseteq> C i"
    using assms unfolding lepoll_def by metis
  then show ?thesis
    unfolding lepoll_def
    apply (rule_tac x = "\<lambda>g. \<lambda>i \<in> A. f i (g i)" in exI)
    apply (auto simp: inj_on_def)
     apply (rule PiE_ext, auto)
     apply (metis (full_types) PiE_mem restrict_apply')
    by blast
qed


lemma card_le_PiE_subindex:
  assumes "A \<subseteq> A'" "Pi\<^sub>E A' B \<noteq> {}"
  shows "PiE A B \<lesssim> PiE A' B"
proof -
  have "\<And>x. x \<in> A' \<Longrightarrow> \<exists>y. y \<in> B x"
    using assms by blast
  then obtain g where g: "\<And>x. x \<in> A' \<Longrightarrow> g x \<in> B x"
    by metis
  let ?F = "\<lambda>f x. if x \<in> A then f x else if x \<in> A' then g x else undefined"
  have "Pi\<^sub>E A B \<subseteq> (\<lambda>f. restrict f A) ` Pi\<^sub>E A' B"
  proof
    show "f \<in> Pi\<^sub>E A B \<Longrightarrow> f \<in> (\<lambda>f. restrict f A) ` Pi\<^sub>E A' B" for f
      using \<open>A \<subseteq> A'\<close>
      by (rule_tac x="?F f" in image_eqI) (auto simp: g fun_eq_iff)
  qed
  then have "Pi\<^sub>E A B \<lesssim> (\<lambda>f. \<lambda>i \<in> A. f i) ` Pi\<^sub>E A' B"
    by (simp add: subset_imp_lepoll)
  also have "\<dots> \<lesssim> PiE A' B"
    by (rule image_lepoll)
  finally show ?thesis .
qed


lemma finite_restricted_funspace:
  assumes "finite A" "finite B"
  shows "finite {f. f ` A \<subseteq> B \<and> {x. f x \<noteq> k x} \<subseteq> A}" (is "finite ?F")
proof (rule finite_subset)
  show "finite ((\<lambda>U x. if \<exists>y. (x,y) \<in> U then @y. (x,y) \<in> U else k x) ` Pow(A \<times> B))" (is "finite ?G")
    using assms by auto
  show "?F \<subseteq> ?G"
  proof
    fix f
    assume "f \<in> ?F"
    then show "f \<in> ?G"
      by (rule_tac x="(\<lambda>x. (x,f x)) ` {x. f x \<noteq> k x}" in image_eqI) (auto simp: fun_eq_iff image_def)
  qed
qed


proposition finite_PiE_iff:
   "finite(PiE I S) \<longleftrightarrow> PiE I S = {} \<or> finite {i \<in> I. ~(\<exists>a. S i \<subseteq> {a})} \<and> (\<forall>i \<in> I. finite(S i))"
 (is "?lhs = ?rhs")
proof (cases "PiE I S = {}")
  case False
  define J where "J \<equiv> {i \<in> I. \<nexists>a. S i \<subseteq> {a}}"
  show ?thesis
  proof
    assume L: ?lhs
    have "infinite (Pi\<^sub>E I S)" if "infinite J"
    proof -
      have "(UNIV::nat set) \<lesssim> (UNIV::(nat\<Rightarrow>bool) set)"
      proof -
        have "\<forall>N::nat set. inj_on (=) N"
          by (simp add: inj_on_def)
        then show ?thesis
          by (meson infinite_iff_countable_subset infinite_le_lepoll top.extremum)
      qed
      also have "\<dots> = (UNIV::nat set) \<rightarrow>\<^sub>E (UNIV::bool set)"
        by auto
      also have "\<dots> \<lesssim> J \<rightarrow>\<^sub>E (UNIV::bool set)"
        apply (rule lepoll_funcset_left)
        using infinite_le_lepoll that by auto
      also have "\<dots> \<lesssim> Pi\<^sub>E J S"
      proof -
        have *: "(UNIV::bool set) \<lesssim> S i" if "i \<in> I" and "\<forall>a. \<not> S i \<subseteq> {a}" for i
        proof -
          obtain a b where "{a,b} \<subseteq> S i" "a \<noteq> b"
            by (metis \<open>\<forall>a. \<not> S i \<subseteq> {a}\<close> all_not_in_conv empty_subsetI insertCI insert_subset set_eq_subset subsetI)
          then show ?thesis
            apply (clarsimp simp: lepoll_def inj_on_def)
            apply (rule_tac x="\<lambda>x. if x then a else b" in exI, auto)
            done
        qed
        show ?thesis
          by (auto simp: * J_def intro: lepoll_PiE)
      qed
      also have "\<dots> \<lesssim> Pi\<^sub>E I S"
        using False by (auto simp: J_def intro: card_le_PiE_subindex)
      finally have "(UNIV::nat set) \<lesssim> Pi\<^sub>E I S" .
      then show ?thesis
        by (simp add: infinite_le_lepoll)
    qed
    moreover have "finite (S i)" if "i \<in> I" for i
    proof (rule finite_subset)
      obtain f where f: "f \<in> PiE I S"
        using False by blast
      show "S i \<subseteq> (\<lambda>f. f i) ` Pi\<^sub>E I S"
      proof
        show "s \<in> (\<lambda>f. f i) ` Pi\<^sub>E I S" if "s \<in> S i" for s
          using that f \<open>i \<in> I\<close>
          by (rule_tac x="\<lambda>j. if j = i then s else f j" in image_eqI) auto
      qed
    next
      show "finite ((\<lambda>x. x i) ` Pi\<^sub>E I S)"
        using L by blast
    qed
    ultimately show ?rhs
      using L
      by (auto simp: J_def False)
  next
    assume R: ?rhs
    have "\<forall>i \<in> I - J. \<exists>a. S i = {a}"
      using False J_def by blast
    then obtain a where a: "\<forall>i \<in> I - J. S i = {a i}"
      by metis
    let ?F = "{f. f ` J \<subseteq> (\<Union>i \<in> J. S i) \<and> {i. f i \<noteq> (if i \<in> I then a i else undefined)} \<subseteq> J}"
    have *: "finite (Pi\<^sub>E I S)"
      if "finite J" and "\<forall>i\<in>I. finite (S i)"
    proof (rule finite_subset)
      show "Pi\<^sub>E I S \<subseteq> ?F"
        apply safe
        using J_def apply blast
        by (metis DiffI PiE_E a singletonD)
      show "finite ?F"
      proof (rule finite_restricted_funspace [OF \<open>finite J\<close>])
        show "finite (\<Union> (S ` J))"
          using that J_def by blast
      qed
  qed
  show ?lhs
      using R by (auto simp: * J_def)
  qed
qed auto


corollary finite_funcset_iff:
  "finite(I \<rightarrow>\<^sub>E S) \<longleftrightarrow> (\<exists>a. S \<subseteq> {a}) \<or> I = {} \<or> finite I \<and> finite S"
  apply (auto simp: finite_PiE_iff PiE_eq_empty_iff dest: not_finite_existsD)
  using finite.simps by auto

end
