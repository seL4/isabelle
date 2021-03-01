(*  Title:      HOL/Library/FuncSet.thy
    Author:     Florian Kammueller and Lawrence C Paulson, Lukas Bulwahn
*)

section \<open>Pi and Function Sets\<close>

theory FuncSet
  imports Main
  abbrevs PiE = "Pi\<^sub>E"
    and PIE = "\<Pi>\<^sub>E"
begin

definition Pi :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "Pi A B = {f. \<forall>x. x \<in> A \<longrightarrow> f x \<in> B x}"

definition extensional :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "extensional A = {f. \<forall>x. x \<notin> A \<longrightarrow> f x = undefined}"

definition "restrict" :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b"
  where "restrict f A = (\<lambda>x. if x \<in> A then f x else undefined)"

abbreviation funcset :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  (infixr "\<rightarrow>" 60)
  where "A \<rightarrow> B \<equiv> Pi A (\<lambda>_. B)"

syntax
  "_Pi" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  ("(3\<Pi> _\<in>_./ _)"   10)
  "_lam" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)
translations
  "\<Pi> x\<in>A. B" \<rightleftharpoons> "CONST Pi A (\<lambda>x. B)"
  "\<lambda>x\<in>A. f" \<rightleftharpoons> "CONST restrict (\<lambda>x. f) A"

definition "compose" :: "'a set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'c)"
  where "compose A g f = (\<lambda>x\<in>A. g (f x))"


subsection \<open>Basic Properties of \<^term>\<open>Pi\<close>\<close>

lemma Pi_I[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B x) \<Longrightarrow> f \<in> Pi A B"
  by (simp add: Pi_def)

lemma Pi_I'[simp]: "(\<And>x. x \<in> A \<longrightarrow> f x \<in> B x) \<Longrightarrow> f \<in> Pi A B"
  by (simp add:Pi_def)

lemma funcsetI: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> f \<in> A \<rightarrow> B"
  by (simp add: Pi_def)

lemma Pi_mem: "f \<in> Pi A B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B x"
  by (simp add: Pi_def)

lemma Pi_iff: "f \<in> Pi I X \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> X i)"
  unfolding Pi_def by auto

lemma PiE [elim]: "f \<in> Pi A B \<Longrightarrow> (f x \<in> B x \<Longrightarrow> Q) \<Longrightarrow> (x \<notin> A \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (auto simp: Pi_def)

lemma Pi_cong: "(\<And>w. w \<in> A \<Longrightarrow> f w = g w) \<Longrightarrow> f \<in> Pi A B \<longleftrightarrow> g \<in> Pi A B"
  by (auto simp: Pi_def)

lemma funcset_id [simp]: "(\<lambda>x. x) \<in> A \<rightarrow> A"
  by auto

lemma funcset_mem: "f \<in> A \<rightarrow> B \<Longrightarrow> x \<in> A \<Longrightarrow> f x \<in> B"
  by (simp add: Pi_def)

lemma funcset_image: "f \<in> A \<rightarrow> B \<Longrightarrow> f ` A \<subseteq> B"
  by auto

lemma image_subset_iff_funcset: "F ` A \<subseteq> B \<longleftrightarrow> F \<in> A \<rightarrow> B"
  by auto

lemma funcset_to_empty_iff: "A \<rightarrow> {} = (if A={} then UNIV else {})"
  by auto

lemma Pi_eq_empty[simp]: "(\<Pi> x \<in> A. B x) = {} \<longleftrightarrow> (\<exists>x\<in>A. B x = {})"
proof -
  have "\<exists>x\<in>A. B x = {}" if "\<And>f. \<exists>y. y \<in> A \<and> f y \<notin> B y" 
    using that [of "\<lambda>u. SOME y. y \<in> B u"] some_in_eq by blast
  then show ?thesis
    by force
qed

lemma Pi_empty [simp]: "Pi {} B = UNIV"
  by (simp add: Pi_def)

lemma Pi_Int: "Pi I E \<inter> Pi I F = (\<Pi> i\<in>I. E i \<inter> F i)"
  by auto

lemma Pi_UN:
  fixes A :: "nat \<Rightarrow> 'i \<Rightarrow> 'a set"
  assumes "finite I"
    and mono: "\<And>i n m. i \<in> I \<Longrightarrow> n \<le> m \<Longrightarrow> A n i \<subseteq> A m i"
  shows "(\<Union>n. Pi I (A n)) = (\<Pi> i\<in>I. \<Union>n. A n i)"
proof (intro set_eqI iffI)
  fix f
  assume "f \<in> (\<Pi> i\<in>I. \<Union>n. A n i)"
  then have "\<forall>i\<in>I. \<exists>n. f i \<in> A n i"
    by auto
  from bchoice[OF this] obtain n where n: "f i \<in> A (n i) i" if "i \<in> I" for i
    by auto
  obtain k where k: "n i \<le> k" if "i \<in> I" for i
    using \<open>finite I\<close> finite_nat_set_iff_bounded_le[of "n`I"] by auto
  have "f \<in> Pi I (A k)"
  proof (intro Pi_I)
    fix i
    assume "i \<in> I"
    from mono[OF this, of "n i" k] k[OF this] n[OF this]
    show "f i \<in> A k i" by auto
  qed
  then show "f \<in> (\<Union>n. Pi I (A n))"
    by auto
qed auto

lemma Pi_UNIV [simp]: "A \<rightarrow> UNIV = UNIV"
  by (simp add: Pi_def)

text \<open>Covariance of Pi-sets in their second argument\<close>
lemma Pi_mono: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x) \<Longrightarrow> Pi A B \<subseteq> Pi A C"
  by auto

text \<open>Contravariance of Pi-sets in their first argument\<close>
lemma Pi_anti_mono: "A' \<subseteq> A \<Longrightarrow> Pi A B \<subseteq> Pi A' B"
  by auto

lemma prod_final:
  assumes 1: "fst \<circ> f \<in> Pi A B"
    and 2: "snd \<circ> f \<in> Pi A C"
  shows "f \<in> (\<Pi> z \<in> A. B z \<times> C z)"
proof (rule Pi_I)
  fix z
  assume z: "z \<in> A"
  have "f z = (fst (f z), snd (f z))"
    by simp
  also have "\<dots> \<in> B z \<times> C z"
    by (metis SigmaI PiE o_apply 1 2 z)
  finally show "f z \<in> B z \<times> C z" .
qed

lemma Pi_split_domain[simp]: "x \<in> Pi (I \<union> J) X \<longleftrightarrow> x \<in> Pi I X \<and> x \<in> Pi J X"
  by (auto simp: Pi_def)

lemma Pi_split_insert_domain[simp]: "x \<in> Pi (insert i I) X \<longleftrightarrow> x \<in> Pi I X \<and> x i \<in> X i"
  by (auto simp: Pi_def)

lemma Pi_cancel_fupd_range[simp]: "i \<notin> I \<Longrightarrow> x \<in> Pi I (B(i := b)) \<longleftrightarrow> x \<in> Pi I B"
  by (auto simp: Pi_def)

lemma Pi_cancel_fupd[simp]: "i \<notin> I \<Longrightarrow> x(i := a) \<in> Pi I B \<longleftrightarrow> x \<in> Pi I B"
  by (auto simp: Pi_def)

lemma Pi_fupd_iff: "i \<in> I \<Longrightarrow> f \<in> Pi I (B(i := A)) \<longleftrightarrow> f \<in> Pi (I - {i}) B \<and> f i \<in> A"
  apply auto
  apply (metis PiE fun_upd_apply)
  by force


subsection \<open>Composition With a Restricted Domain: \<^term>\<open>compose\<close>\<close>

lemma funcset_compose: "f \<in> A \<rightarrow> B \<Longrightarrow> g \<in> B \<rightarrow> C \<Longrightarrow> compose A g f \<in> A \<rightarrow> C"
  by (simp add: Pi_def compose_def restrict_def)

lemma compose_assoc:
  assumes "f \<in> A \<rightarrow> B"
  shows "compose A h (compose A g f) = compose A (compose B h g) f"
  using assms by (simp add: fun_eq_iff Pi_def compose_def restrict_def)

lemma compose_eq: "x \<in> A \<Longrightarrow> compose A g f x = g (f x)"
  by (simp add: compose_def restrict_def)

lemma surj_compose: "f ` A = B \<Longrightarrow> g ` B = C \<Longrightarrow> compose A g f ` A = C"
  by (auto simp add: image_def compose_eq)


subsection \<open>Bounded Abstraction: \<^term>\<open>restrict\<close>\<close>

lemma restrict_cong: "I = J \<Longrightarrow> (\<And>i. i \<in> J =simp=> f i = g i) \<Longrightarrow> restrict f I = restrict g J"
  by (auto simp: restrict_def fun_eq_iff simp_implies_def)

lemma restrictI[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B x) \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> Pi A B"
  by (simp add: Pi_def restrict_def)

lemma restrict_apply[simp]: "(\<lambda>y\<in>A. f y) x = (if x \<in> A then f x else undefined)"
  by (simp add: restrict_def)

lemma restrict_apply': "x \<in> A \<Longrightarrow> (\<lambda>y\<in>A. f y) x = f x"
  by simp

lemma restrict_ext: "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)"
  by (simp add: fun_eq_iff Pi_def restrict_def)

lemma restrict_UNIV: "restrict f UNIV = f"
  by (simp add: restrict_def)

lemma inj_on_restrict_eq [simp]: "inj_on (restrict f A) A = inj_on f A"
  by (simp add: inj_on_def restrict_def)

lemma Id_compose: "f \<in> A \<rightarrow> B \<Longrightarrow> f \<in> extensional A \<Longrightarrow> compose A (\<lambda>y\<in>B. y) f = f"
  by (auto simp add: fun_eq_iff compose_def extensional_def Pi_def)

lemma compose_Id: "g \<in> A \<rightarrow> B \<Longrightarrow> g \<in> extensional A \<Longrightarrow> compose A g (\<lambda>x\<in>A. x) = g"
  by (auto simp add: fun_eq_iff compose_def extensional_def Pi_def)

lemma image_restrict_eq [simp]: "(restrict f A) ` A = f ` A"
  by (auto simp add: restrict_def)

lemma restrict_restrict[simp]: "restrict (restrict f A) B = restrict f (A \<inter> B)"
  unfolding restrict_def by (simp add: fun_eq_iff)

lemma restrict_fupd[simp]: "i \<notin> I \<Longrightarrow> restrict (f (i := x)) I = restrict f I"
  by (auto simp: restrict_def)

lemma restrict_upd[simp]: "i \<notin> I \<Longrightarrow> (restrict f I)(i := y) = restrict (f(i := y)) (insert i I)"
  by (auto simp: fun_eq_iff)

lemma restrict_Pi_cancel: "restrict x I \<in> Pi I A \<longleftrightarrow> x \<in> Pi I A"
  by (auto simp: restrict_def Pi_def)

lemma sum_restrict' [simp]: "sum' (\<lambda>i\<in>I. g i) I = sum' (\<lambda>i. g i) I"
  by (simp add: sum.G_def conj_commute cong: conj_cong)

lemma prod_restrict' [simp]: "prod' (\<lambda>i\<in>I. g i) I = prod' (\<lambda>i. g i) I"
  by (simp add: prod.G_def conj_commute cong: conj_cong)


subsection \<open>Bijections Between Sets\<close>

text \<open>The definition of \<^const>\<open>bij_betw\<close> is in \<open>Fun.thy\<close>, but most of
the theorems belong here, or need at least \<^term>\<open>Hilbert_Choice\<close>.\<close>

lemma bij_betwI:
  assumes "f \<in> A \<rightarrow> B"
    and "g \<in> B \<rightarrow> A"
    and g_f: "\<And>x. x\<in>A \<Longrightarrow> g (f x) = x"
    and f_g: "\<And>y. y\<in>B \<Longrightarrow> f (g y) = y"
  shows "bij_betw f A B"
  unfolding bij_betw_def
proof
  show "inj_on f A"
    by (metis g_f inj_on_def)
  have "f ` A \<subseteq> B"
    using \<open>f \<in> A \<rightarrow> B\<close> by auto
  moreover
  have "B \<subseteq> f ` A"
    by auto (metis Pi_mem \<open>g \<in> B \<rightarrow> A\<close> f_g image_iff)
  ultimately show "f ` A = B"
    by blast
qed

lemma bij_betw_imp_funcset: "bij_betw f A B \<Longrightarrow> f \<in> A \<rightarrow> B"
  by (auto simp add: bij_betw_def)

lemma inj_on_compose: "bij_betw f A B \<Longrightarrow> inj_on g B \<Longrightarrow> inj_on (compose A g f) A"
  by (auto simp add: bij_betw_def inj_on_def compose_eq)

lemma bij_betw_compose: "bij_betw f A B \<Longrightarrow> bij_betw g B C \<Longrightarrow> bij_betw (compose A g f) A C"
  apply (simp add: bij_betw_def compose_eq inj_on_compose)
  apply (auto simp add: compose_def image_def)
  done

lemma bij_betw_restrict_eq [simp]: "bij_betw (restrict f A) A B = bij_betw f A B"
  by (simp add: bij_betw_def)


subsection \<open>Extensionality\<close>

lemma extensional_empty[simp]: "extensional {} = {\<lambda>x. undefined}"
  unfolding extensional_def by auto

lemma extensional_arb: "f \<in> extensional A \<Longrightarrow> x \<notin> A \<Longrightarrow> f x = undefined"
  by (simp add: extensional_def)

lemma restrict_extensional [simp]: "restrict f A \<in> extensional A"
  by (simp add: restrict_def extensional_def)

lemma compose_extensional [simp]: "compose A f g \<in> extensional A"
  by (simp add: compose_def)

lemma extensionalityI:
  assumes "f \<in> extensional A"
    and "g \<in> extensional A"
    and "\<And>x. x \<in> A \<Longrightarrow> f x = g x"
  shows "f = g"
  using assms by (force simp add: fun_eq_iff extensional_def)

lemma extensional_restrict:  "f \<in> extensional A \<Longrightarrow> restrict f A = f"
  by (rule extensionalityI[OF restrict_extensional]) auto

lemma extensional_subset: "f \<in> extensional A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f \<in> extensional B"
  unfolding extensional_def by auto

lemma inv_into_funcset: "f ` A = B \<Longrightarrow> (\<lambda>x\<in>B. inv_into A f x) \<in> B \<rightarrow> A"
  by (unfold inv_into_def) (fast intro: someI2)

lemma compose_inv_into_id: "bij_betw f A B \<Longrightarrow> compose A (\<lambda>y\<in>B. inv_into A f y) f = (\<lambda>x\<in>A. x)"
  apply (simp add: bij_betw_def compose_def)
  apply (rule restrict_ext, auto)
  done

lemma compose_id_inv_into: "f ` A = B \<Longrightarrow> compose B f (\<lambda>y\<in>B. inv_into A f y) = (\<lambda>x\<in>B. x)"
  apply (simp add: compose_def)
  apply (rule restrict_ext)
  apply (simp add: f_inv_into_f)
  done

lemma extensional_insert[intro, simp]:
  assumes "a \<in> extensional (insert i I)"
  shows "a(i := b) \<in> extensional (insert i I)"
  using assms unfolding extensional_def by auto

lemma extensional_Int[simp]: "extensional I \<inter> extensional I' = extensional (I \<inter> I')"
  unfolding extensional_def by auto

lemma extensional_UNIV[simp]: "extensional UNIV = UNIV"
  by (auto simp: extensional_def)

lemma restrict_extensional_sub[intro]: "A \<subseteq> B \<Longrightarrow> restrict f A \<in> extensional B"
  unfolding restrict_def extensional_def by auto

lemma extensional_insert_undefined[intro, simp]:
  "a \<in> extensional (insert i I) \<Longrightarrow> a(i := undefined) \<in> extensional I"
  unfolding extensional_def by auto

lemma extensional_insert_cancel[intro, simp]:
  "a \<in> extensional I \<Longrightarrow> a \<in> extensional (insert i I)"
  unfolding extensional_def by auto


subsection \<open>Cardinality\<close>

lemma card_inj: "f \<in> A \<rightarrow> B \<Longrightarrow> inj_on f A \<Longrightarrow> finite B \<Longrightarrow> card A \<le> card B"
  by (rule card_inj_on_le) auto

lemma card_bij:
  assumes "f \<in> A \<rightarrow> B" "inj_on f A"
    and "g \<in> B \<rightarrow> A" "inj_on g B"
    and "finite A" "finite B"
  shows "card A = card B"
  using assms by (blast intro: card_inj order_antisym)


subsection \<open>Extensional Function Spaces\<close>

definition PiE :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set"
  where "PiE S T = Pi S T \<inter> extensional S"

abbreviation "Pi\<^sub>E A B \<equiv> PiE A B"

syntax
  "_PiE" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set"  ("(3\<Pi>\<^sub>E _\<in>_./ _)" 10)
translations
  "\<Pi>\<^sub>E x\<in>A. B" \<rightleftharpoons> "CONST Pi\<^sub>E A (\<lambda>x. B)"

abbreviation extensional_funcset :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "\<rightarrow>\<^sub>E" 60)
  where "A \<rightarrow>\<^sub>E B \<equiv> (\<Pi>\<^sub>E i\<in>A. B)"

lemma extensional_funcset_def: "extensional_funcset S T = (S \<rightarrow> T) \<inter> extensional S"
  by (simp add: PiE_def)

lemma PiE_empty_domain[simp]: "Pi\<^sub>E {} T = {\<lambda>x. undefined}"
  unfolding PiE_def by simp

lemma PiE_UNIV_domain: "Pi\<^sub>E UNIV T = Pi UNIV T"
  unfolding PiE_def by simp

lemma PiE_empty_range[simp]: "i \<in> I \<Longrightarrow> F i = {} \<Longrightarrow> (\<Pi>\<^sub>E i\<in>I. F i) = {}"
  unfolding PiE_def by auto

lemma PiE_eq_empty_iff: "Pi\<^sub>E I F = {} \<longleftrightarrow> (\<exists>i\<in>I. F i = {})"
proof
  assume "Pi\<^sub>E I F = {}"
  show "\<exists>i\<in>I. F i = {}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "\<forall>i. \<exists>y. (i \<in> I \<longrightarrow> y \<in> F i) \<and> (i \<notin> I \<longrightarrow> y = undefined)"
      by auto
    from choice[OF this]
    obtain f where " \<forall>x. (x \<in> I \<longrightarrow> f x \<in> F x) \<and> (x \<notin> I \<longrightarrow> f x = undefined)" ..
    then have "f \<in> Pi\<^sub>E I F"
      by (auto simp: extensional_def PiE_def)
    with \<open>Pi\<^sub>E I F = {}\<close> show False
      by auto
  qed
qed (auto simp: PiE_def)

lemma PiE_arb: "f \<in> Pi\<^sub>E S T \<Longrightarrow> x \<notin> S \<Longrightarrow> f x = undefined"
  unfolding PiE_def by auto (auto dest!: extensional_arb)

lemma PiE_mem: "f \<in> Pi\<^sub>E S T \<Longrightarrow> x \<in> S \<Longrightarrow> f x \<in> T x"
  unfolding PiE_def by auto

lemma PiE_fun_upd: "y \<in> T x \<Longrightarrow> f \<in> Pi\<^sub>E S T \<Longrightarrow> f(x := y) \<in> Pi\<^sub>E (insert x S) T"
  unfolding PiE_def extensional_def by auto

lemma fun_upd_in_PiE: "x \<notin> S \<Longrightarrow> f \<in> Pi\<^sub>E (insert x S) T \<Longrightarrow> f(x := undefined) \<in> Pi\<^sub>E S T"
  unfolding PiE_def extensional_def by auto

lemma PiE_insert_eq: "Pi\<^sub>E (insert x S) T = (\<lambda>(y, g). g(x := y)) ` (T x \<times> Pi\<^sub>E S T)"
proof -
  {
    fix f assume "f \<in> Pi\<^sub>E (insert x S) T" "x \<notin> S"
    then have "f \<in> (\<lambda>(y, g). g(x := y)) ` (T x \<times> Pi\<^sub>E S T)"
      by (auto intro!: image_eqI[where x="(f x, f(x := undefined))"] intro: fun_upd_in_PiE PiE_mem)
  }
  moreover
  {
    fix f assume "f \<in> Pi\<^sub>E (insert x S) T" "x \<in> S"
    then have "f \<in> (\<lambda>(y, g). g(x := y)) ` (T x \<times> Pi\<^sub>E S T)"
      by (auto intro!: image_eqI[where x="(f x, f)"] intro: fun_upd_in_PiE PiE_mem simp: insert_absorb)
  }
  ultimately show ?thesis
    by (auto intro: PiE_fun_upd)
qed

lemma PiE_Int: "Pi\<^sub>E I A \<inter> Pi\<^sub>E I B = Pi\<^sub>E I (\<lambda>x. A x \<inter> B x)"
  by (auto simp: PiE_def)

lemma PiE_cong: "(\<And>i. i\<in>I \<Longrightarrow> A i = B i) \<Longrightarrow> Pi\<^sub>E I A = Pi\<^sub>E I B"
  unfolding PiE_def by (auto simp: Pi_cong)

lemma PiE_E [elim]:
  assumes "f \<in> Pi\<^sub>E A B"
  obtains "x \<in> A" and "f x \<in> B x"
    | "x \<notin> A" and "f x = undefined"
  using assms by (auto simp: Pi_def PiE_def extensional_def)

lemma PiE_I[intro!]:
  "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B x) \<Longrightarrow> (\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> f \<in> Pi\<^sub>E A B"
  by (simp add: PiE_def extensional_def)

lemma PiE_mono: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x) \<Longrightarrow> Pi\<^sub>E A B \<subseteq> Pi\<^sub>E A C"
  by auto

lemma PiE_iff: "f \<in> Pi\<^sub>E I X \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> X i) \<and> f \<in> extensional I"
  by (simp add: PiE_def Pi_iff)

lemma restrict_PiE_iff [simp]: "restrict f I \<in> Pi\<^sub>E I X \<longleftrightarrow> (\<forall>i \<in> I. f i \<in> X i)"
  by (simp add: PiE_iff)

lemma ext_funcset_to_sing_iff [simp]: "A \<rightarrow>\<^sub>E {a} = {\<lambda>x\<in>A. a}"
  by (auto simp: PiE_def Pi_iff extensionalityI)

lemma PiE_restrict[simp]:  "f \<in> Pi\<^sub>E A B \<Longrightarrow> restrict f A = f"
  by (simp add: extensional_restrict PiE_def)

lemma restrict_PiE[simp]: "restrict f I \<in> Pi\<^sub>E I S \<longleftrightarrow> f \<in> Pi I S"
  by (auto simp: PiE_iff)

lemma PiE_eq_subset:
  assumes ne: "\<And>i. i \<in> I \<Longrightarrow> F i \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow> F' i \<noteq> {}"
    and eq: "Pi\<^sub>E I F = Pi\<^sub>E I F'"
    and "i \<in> I"
  shows "F i \<subseteq> F' i"
proof
  fix x
  assume "x \<in> F i"
  with ne have "\<forall>j. \<exists>y. (j \<in> I \<longrightarrow> y \<in> F j \<and> (i = j \<longrightarrow> x = y)) \<and> (j \<notin> I \<longrightarrow> y = undefined)"
    by auto
  from choice[OF this] obtain f
    where f: " \<forall>j. (j \<in> I \<longrightarrow> f j \<in> F j \<and> (i = j \<longrightarrow> x = f j)) \<and> (j \<notin> I \<longrightarrow> f j = undefined)" ..
  then have "f \<in> Pi\<^sub>E I F"
    by (auto simp: extensional_def PiE_def)
  then have "f \<in> Pi\<^sub>E I F'"
    using assms by simp
  then show "x \<in> F' i"
    using f \<open>i \<in> I\<close> by (auto simp: PiE_def)
qed

lemma PiE_eq_iff_not_empty:
  assumes ne: "\<And>i. i \<in> I \<Longrightarrow> F i \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow> F' i \<noteq> {}"
  shows "Pi\<^sub>E I F = Pi\<^sub>E I F' \<longleftrightarrow> (\<forall>i\<in>I. F i = F' i)"
proof (intro iffI ballI)
  fix i
  assume eq: "Pi\<^sub>E I F = Pi\<^sub>E I F'"
  assume i: "i \<in> I"
  show "F i = F' i"
    using PiE_eq_subset[of I F F', OF ne eq i]
    using PiE_eq_subset[of I F' F, OF ne(2,1) eq[symmetric] i]
    by auto
qed (auto simp: PiE_def)

lemma PiE_eq_iff:
  "Pi\<^sub>E I F = Pi\<^sub>E I F' \<longleftrightarrow> (\<forall>i\<in>I. F i = F' i) \<or> ((\<exists>i\<in>I. F i = {}) \<and> (\<exists>i\<in>I. F' i = {}))"
proof (intro iffI disjCI)
  assume eq[simp]: "Pi\<^sub>E I F = Pi\<^sub>E I F'"
  assume "\<not> ((\<exists>i\<in>I. F i = {}) \<and> (\<exists>i\<in>I. F' i = {}))"
  then have "(\<forall>i\<in>I. F i \<noteq> {}) \<and> (\<forall>i\<in>I. F' i \<noteq> {})"
    using PiE_eq_empty_iff[of I F] PiE_eq_empty_iff[of I F'] by auto
  with PiE_eq_iff_not_empty[of I F F'] show "\<forall>i\<in>I. F i = F' i"
    by auto
next
  assume "(\<forall>i\<in>I. F i = F' i) \<or> (\<exists>i\<in>I. F i = {}) \<and> (\<exists>i\<in>I. F' i = {})"
  then show "Pi\<^sub>E I F = Pi\<^sub>E I F'"
    using PiE_eq_empty_iff[of I F] PiE_eq_empty_iff[of I F'] by (auto simp: PiE_def)
qed

lemma extensional_funcset_fun_upd_restricts_rangeI:
  "\<forall>y \<in> S. f x \<noteq> f y \<Longrightarrow> f \<in> (insert x S) \<rightarrow>\<^sub>E T \<Longrightarrow> f(x := undefined) \<in> S \<rightarrow>\<^sub>E (T - {f x})"
  unfolding extensional_funcset_def extensional_def
  by (auto split: if_split_asm)

lemma extensional_funcset_fun_upd_extends_rangeI:
  assumes "a \<in> T" "f \<in> S \<rightarrow>\<^sub>E (T - {a})"
  shows "f(x := a) \<in> insert x S \<rightarrow>\<^sub>E  T"
  using assms unfolding extensional_funcset_def extensional_def by auto

lemma subset_PiE:
   "PiE I S \<subseteq> PiE I T \<longleftrightarrow> PiE I S = {} \<or> (\<forall>i \<in> I. S i \<subseteq> T i)" (is "?lhs \<longleftrightarrow> _ \<or> ?rhs")
proof (cases "PiE I S = {}")
  case False
  moreover have "?lhs = ?rhs"
  proof
    assume L: ?lhs
    have "\<And>i. i\<in>I \<Longrightarrow> S i \<noteq> {}"
      using False PiE_eq_empty_iff by blast
    with L show ?rhs
      by (simp add: PiE_Int PiE_eq_iff inf.absorb_iff2)
  qed auto
  ultimately show ?thesis
    by simp
qed simp

lemma PiE_eq:
   "PiE I S = PiE I T \<longleftrightarrow> PiE I S = {} \<and> PiE I T = {} \<or> (\<forall>i \<in> I. S i = T i)"
  by (auto simp: PiE_eq_iff PiE_eq_empty_iff)

lemma PiE_UNIV [simp]: "PiE UNIV (\<lambda>i. UNIV) = UNIV"
  by blast

lemma image_projection_PiE:
  "(\<lambda>f. f i) ` (PiE I S) = (if PiE I S = {} then {} else if i \<in> I then S i else {undefined})"
proof -
  have "(\<lambda>f. f i) ` Pi\<^sub>E I S = S i" if "i \<in> I" "f \<in> PiE I S" for f
    using that apply auto
    by (rule_tac x="(\<lambda>k. if k=i then x else f k)" in image_eqI) auto
  moreover have "(\<lambda>f. f i) ` Pi\<^sub>E I S = {undefined}" if "f \<in> PiE I S" "i \<notin> I" for f
    using that by (blast intro: PiE_arb [OF that, symmetric])
  ultimately show ?thesis
    by auto
qed

lemma PiE_singleton: 
  assumes "f \<in> extensional A"
  shows   "PiE A (\<lambda>x. {f x}) = {f}"
proof -
  {
    fix g assume "g \<in> PiE A (\<lambda>x. {f x})"
    hence "g x = f x" for x
      using assms by (cases "x \<in> A") (auto simp: extensional_def)
    hence "g = f" by (simp add: fun_eq_iff)
  }
  thus ?thesis using assms by (auto simp: extensional_def)
qed

lemma PiE_eq_singleton: "(\<Pi>\<^sub>E i\<in>I. S i) = {\<lambda>i\<in>I. f i} \<longleftrightarrow> (\<forall>i\<in>I. S i = {f i})"
  by (metis (mono_tags, lifting) PiE_eq PiE_singleton insert_not_empty restrict_apply' restrict_extensional)

lemma PiE_over_singleton_iff: "(\<Pi>\<^sub>E x\<in>{a}. B x) = (\<Union>b \<in> B a. {\<lambda>x \<in> {a}. b})"
  apply (auto simp: PiE_iff split: if_split_asm)
  apply (metis (no_types, lifting) extensionalityI restrict_apply' restrict_extensional singletonD)
  done

lemma all_PiE_elements:
   "(\<forall>z \<in> PiE I S. \<forall>i \<in> I. P i (z i)) \<longleftrightarrow> PiE I S = {} \<or> (\<forall>i \<in> I. \<forall>x \<in> S i. P i x)" (is "?lhs = ?rhs")
proof (cases "PiE I S = {}")
  case False
  then obtain f where f: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> S i"
    by fastforce
  show ?thesis
  proof
    assume L: ?lhs
    have "P i x"
      if "i \<in> I" "x \<in> S i" for i x
    proof -
      have "(\<lambda>j \<in> I. if j=i then x else f j) \<in> PiE I S"
        by (simp add: f that(2))
      then have "P i ((\<lambda>j \<in> I. if j=i then x else f j) i)"
        using L that(1) by blast
      with that show ?thesis
        by simp
    qed
    then show ?rhs
      by (simp add: False)
  qed fastforce
qed simp

lemma PiE_ext: "\<lbrakk>x \<in> PiE k s; y \<in> PiE k s; \<And>i. i \<in> k \<Longrightarrow> x i = y i\<rbrakk> \<Longrightarrow> x = y"
  by (metis ext PiE_E)


subsubsection \<open>Injective Extensional Function Spaces\<close>

lemma extensional_funcset_fun_upd_inj_onI:
  assumes "f \<in> S \<rightarrow>\<^sub>E (T - {a})"
    and "inj_on f S"
  shows "inj_on (f(x := a)) S"
  using assms
  unfolding extensional_funcset_def by (auto intro!: inj_on_fun_updI)

lemma extensional_funcset_extend_domain_inj_on_eq:
  assumes "x \<notin> S"
  shows "{f. f \<in> (insert x S) \<rightarrow>\<^sub>E T \<and> inj_on f (insert x S)} =
    (\<lambda>(y, g). g(x:=y)) ` {(y, g). y \<in> T \<and> g \<in> S \<rightarrow>\<^sub>E (T - {y}) \<and> inj_on g S}"
  using assms
  apply (auto del: PiE_I PiE_E)
  apply (auto intro: extensional_funcset_fun_upd_inj_onI
    extensional_funcset_fun_upd_extends_rangeI del: PiE_I PiE_E)
  apply (auto simp add: image_iff inj_on_def)
  apply (rule_tac x="xa x" in exI)
  apply (auto intro: PiE_mem del: PiE_I PiE_E)
  apply (rule_tac x="xa(x := undefined)" in exI)
  apply (auto intro!: extensional_funcset_fun_upd_restricts_rangeI)
  apply (auto dest!: PiE_mem split: if_split_asm)
  done

lemma extensional_funcset_extend_domain_inj_onI:
  assumes "x \<notin> S"
  shows "inj_on (\<lambda>(y, g). g(x := y)) {(y, g). y \<in> T \<and> g \<in> S \<rightarrow>\<^sub>E (T - {y}) \<and> inj_on g S}"
  using assms
  apply (auto intro!: inj_onI)
  apply (metis fun_upd_same)
  apply (metis assms PiE_arb fun_upd_triv fun_upd_upd)
  done


subsubsection \<open>Misc properties of functions, composition and restriction from HOL Light\<close>

lemma function_factors_left_gen:
  "(\<forall>x y. P x \<and> P y \<and> g x = g y \<longrightarrow> f x = f y) \<longleftrightarrow> (\<exists>h. \<forall>x. P x \<longrightarrow> f x = h(g x))"
  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then show ?rhs
    apply (rule_tac x="f \<circ> inv_into (Collect P) g" in exI)
    unfolding o_def
    by (metis (mono_tags, hide_lams) f_inv_into_f imageI inv_into_into mem_Collect_eq)
qed auto

lemma function_factors_left:
  "(\<forall>x y. (g x = g y) \<longrightarrow> (f x = f y)) \<longleftrightarrow> (\<exists>h. f = h \<circ> g)"
  using function_factors_left_gen [of "\<lambda>x. True" g f] unfolding o_def by blast

lemma function_factors_right_gen:
  "(\<forall>x. P x \<longrightarrow> (\<exists>y. g y = f x)) \<longleftrightarrow> (\<exists>h. \<forall>x. P x \<longrightarrow> f x = g(h x))"
  by metis

lemma function_factors_right:
  "(\<forall>x. \<exists>y. g y = f x) \<longleftrightarrow> (\<exists>h. f = g \<circ> h)"
  unfolding o_def by metis

lemma restrict_compose_right:
   "restrict (g \<circ> restrict f S) S = restrict (g \<circ> f) S"
  by auto

lemma restrict_compose_left:
   "f ` S \<subseteq> T \<Longrightarrow> restrict (restrict g T \<circ> f) S = restrict (g \<circ> f) S"
  by fastforce


subsubsection \<open>Cardinality\<close>

lemma finite_PiE: "finite S \<Longrightarrow> (\<And>i. i \<in> S \<Longrightarrow> finite (T i)) \<Longrightarrow> finite (\<Pi>\<^sub>E i \<in> S. T i)"
  by (induct S arbitrary: T rule: finite_induct) (simp_all add: PiE_insert_eq)

lemma inj_combinator: "x \<notin> S \<Longrightarrow> inj_on (\<lambda>(y, g). g(x := y)) (T x \<times> Pi\<^sub>E S T)"
proof (safe intro!: inj_onI ext)
  fix f y g z
  assume "x \<notin> S"
  assume fg: "f \<in> Pi\<^sub>E S T" "g \<in> Pi\<^sub>E S T"
  assume "f(x := y) = g(x := z)"
  then have *: "\<And>i. (f(x := y)) i = (g(x := z)) i"
    unfolding fun_eq_iff by auto
  from this[of x] show "y = z" by simp
  fix i from *[of i] \<open>x \<notin> S\<close> fg show "f i = g i"
    by (auto split: if_split_asm simp: PiE_def extensional_def)
qed

lemma card_PiE: "finite S \<Longrightarrow> card (\<Pi>\<^sub>E i \<in> S. T i) = (\<Prod> i\<in>S. card (T i))"
proof (induct rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert x S)
  then show ?case
    by (simp add: PiE_insert_eq inj_combinator card_image card_cartesian_product)
qed

subsection \<open>The pigeonhole principle\<close>

text \<open>
  An alternative formulation of this is that for a function mapping a finite set \<open>A\<close> of
  cardinality \<open>m\<close> to a finite set \<open>B\<close> of cardinality \<open>n\<close>, there exists an element \<open>y \<in> B\<close> that
  is hit at least $\lceil \frac{m}{n}\rceil$ times. However, since we do not have real numbers
  or rounding yet, we state it in the following equivalent form:
\<close>
lemma pigeonhole_card:
  assumes "f \<in> A \<rightarrow> B" "finite A" "finite B" "B \<noteq> {}"
  shows   "\<exists>y\<in>B. card (f -` {y} \<inter> A) * card B \<ge> card A"
proof -
  from assms have "card B > 0"
    by auto
  define M where "M = Max ((\<lambda>y. card (f -` {y} \<inter> A)) ` B)"
  have "A = (\<Union>y\<in>B. f -` {y} \<inter> A)"
    using assms by auto
  also have "card \<dots> = (\<Sum>i\<in>B. card (f -` {i} \<inter> A))"
    using assms by (subst card_UN_disjoint) auto
  also have "\<dots> \<le> (\<Sum>i\<in>B. M)"
    unfolding M_def using assms by (intro sum_mono Max.coboundedI) auto
  also have "\<dots> = card B * M"
    by simp
  finally have "M * card B \<ge> card A"
    by (simp add: mult_ac)
  moreover have "M \<in> (\<lambda>y. card (f -` {y} \<inter> A)) ` B"
    unfolding M_def using assms \<open>B \<noteq> {}\<close> by (intro Max_in) auto
  ultimately show ?thesis
    by blast
qed

end
