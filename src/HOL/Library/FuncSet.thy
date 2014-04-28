(*  Title:      HOL/Library/FuncSet.thy
    Author:     Florian Kammueller and Lawrence C Paulson, Lukas Bulwahn
*)

header {* Pi and Function Sets *}

theory FuncSet
imports Hilbert_Choice Main
begin

definition
  Pi :: "['a set, 'a => 'b set] => ('a => 'b) set" where
  "Pi A B = {f. \<forall>x. x \<in> A --> f x \<in> B x}"

definition
  extensional :: "'a set => ('a => 'b) set" where
  "extensional A = {f. \<forall>x. x~:A --> f x = undefined}"

definition
  "restrict" :: "['a => 'b, 'a set] => ('a => 'b)" where
  "restrict f A = (%x. if x \<in> A then f x else undefined)"

abbreviation
  funcset :: "['a set, 'b set] => ('a => 'b) set"
    (infixr "->" 60) where
  "A -> B \<equiv> Pi A (%_. B)"

notation (xsymbols)
  funcset  (infixr "\<rightarrow>" 60)

syntax
  "_Pi"  :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3PI _:_./ _)" 10)
  "_lam" :: "[pttrn, 'a set, 'a => 'b] => ('a=>'b)"  ("(3%_:_./ _)" [0,0,3] 3)

syntax (xsymbols)
  "_Pi" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi> _\<in>_./ _)"   10)
  "_lam" :: "[pttrn, 'a set, 'a => 'b] => ('a=>'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)

syntax (HTML output)
  "_Pi" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi> _\<in>_./ _)"   10)
  "_lam" :: "[pttrn, 'a set, 'a => 'b] => ('a=>'b)"  ("(3\<lambda>_\<in>_./ _)" [0,0,3] 3)

translations
  "PI x:A. B" \<rightleftharpoons> "CONST Pi A (%x. B)"
  "%x:A. f" \<rightleftharpoons> "CONST restrict (%x. f) A"

definition
  "compose" :: "['a set, 'b => 'c, 'a => 'b] => ('a => 'c)" where
  "compose A g f = (\<lambda>x\<in>A. g (f x))"


subsection{*Basic Properties of @{term Pi}*}

lemma Pi_I[intro!]: "(!!x. x \<in> A ==> f x \<in> B x) ==> f \<in> Pi A B"
  by (simp add: Pi_def)

lemma Pi_I'[simp]: "(!!x. x : A --> f x : B x) ==> f : Pi A B"
by(simp add:Pi_def)

lemma funcsetI: "(!!x. x \<in> A ==> f x \<in> B) ==> f \<in> A -> B"
  by (simp add: Pi_def)

lemma Pi_mem: "[|f: Pi A B; x \<in> A|] ==> f x \<in> B x"
  by (simp add: Pi_def)

lemma Pi_iff: "f \<in> Pi I X \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> X i)"
  unfolding Pi_def by auto

lemma PiE [elim]:
  "f : Pi A B ==> (f x : B x ==> Q) ==> (x ~: A ==> Q) ==> Q"
by(auto simp: Pi_def)

lemma Pi_cong:
  "(\<And> w. w \<in> A \<Longrightarrow> f w = g w) \<Longrightarrow> f \<in> Pi A B \<longleftrightarrow> g \<in> Pi A B"
  by (auto simp: Pi_def)

lemma funcset_id [simp]: "(\<lambda>x. x) \<in> A \<rightarrow> A"
  by auto

lemma funcset_mem: "[|f \<in> A -> B; x \<in> A|] ==> f x \<in> B"
  by (simp add: Pi_def)

lemma funcset_image: "f \<in> A\<rightarrow>B ==> f ` A \<subseteq> B"
  by auto

lemma image_subset_iff_funcset: "F ` A \<subseteq> B \<longleftrightarrow> F \<in> A \<rightarrow> B"
  by auto

lemma Pi_eq_empty[simp]: "((PI x: A. B x) = {}) = (\<exists>x\<in>A. B x = {})"
apply (simp add: Pi_def, auto)
txt{*Converse direction requires Axiom of Choice to exhibit a function
picking an element from each non-empty @{term "B x"}*}
apply (drule_tac x = "%u. SOME y. y \<in> B u" in spec, auto)
apply (cut_tac P= "%y. y \<in> B x" in some_eq_ex, auto)
done

lemma Pi_empty [simp]: "Pi {} B = UNIV"
by (simp add: Pi_def)

lemma Pi_Int: "Pi I E \<inter> Pi I F = (\<Pi> i\<in>I. E i \<inter> F i)"
  by auto

lemma Pi_UN:
  fixes A :: "nat \<Rightarrow> 'i \<Rightarrow> 'a set"
  assumes "finite I" and mono: "\<And>i n m. i \<in> I \<Longrightarrow> n \<le> m \<Longrightarrow> A n i \<subseteq> A m i"
  shows "(\<Union>n. Pi I (A n)) = (\<Pi> i\<in>I. \<Union>n. A n i)"
proof (intro set_eqI iffI)
  fix f assume "f \<in> (\<Pi> i\<in>I. \<Union>n. A n i)"
  then have "\<forall>i\<in>I. \<exists>n. f i \<in> A n i" by auto
  from bchoice[OF this] obtain n where n: "\<And>i. i \<in> I \<Longrightarrow> f i \<in> (A (n i) i)" by auto
  obtain k where k: "\<And>i. i \<in> I \<Longrightarrow> n i \<le> k"
    using `finite I` finite_nat_set_iff_bounded_le[of "n`I"] by auto
  have "f \<in> Pi I (A k)"
  proof (intro Pi_I)
    fix i assume "i \<in> I"
    from mono[OF this, of "n i" k] k[OF this] n[OF this]
    show "f i \<in> A k i" by auto
  qed
  then show "f \<in> (\<Union>n. Pi I (A n))" by auto
qed auto

lemma Pi_UNIV [simp]: "A -> UNIV = UNIV"
by (simp add: Pi_def)

text{*Covariance of Pi-sets in their second argument*}
lemma Pi_mono: "(!!x. x \<in> A ==> B x <= C x) ==> Pi A B <= Pi A C"
by auto

text{*Contravariance of Pi-sets in their first argument*}
lemma Pi_anti_mono: "A' <= A ==> Pi A B <= Pi A' B"
by auto

lemma prod_final:
  assumes 1: "fst \<circ> f \<in> Pi A B" and 2: "snd \<circ> f \<in> Pi A C"
  shows "f \<in> (\<Pi> z \<in> A. B z \<times> C z)"
proof (rule Pi_I) 
  fix z
  assume z: "z \<in> A" 
  have "f z = (fst (f z), snd (f z))" 
    by simp
  also have "...  \<in> B z \<times> C z"
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
  apply (drule_tac x=x in Pi_mem)
  apply (simp_all split: split_if_asm)
  apply (drule_tac x=i in Pi_mem)
  apply (auto dest!: Pi_mem)
  done

subsection{*Composition With a Restricted Domain: @{term compose}*}

lemma funcset_compose:
  "[| f \<in> A -> B; g \<in> B -> C |]==> compose A g f \<in> A -> C"
by (simp add: Pi_def compose_def restrict_def)

lemma compose_assoc:
    "[| f \<in> A -> B; g \<in> B -> C; h \<in> C -> D |]
      ==> compose A h (compose A g f) = compose A (compose B h g) f"
by (simp add: fun_eq_iff Pi_def compose_def restrict_def)

lemma compose_eq: "x \<in> A ==> compose A g f x = g(f(x))"
by (simp add: compose_def restrict_def)

lemma surj_compose: "[| f ` A = B; g ` B = C |] ==> compose A g f ` A = C"
  by (auto simp add: image_def compose_eq)


subsection{*Bounded Abstraction: @{term restrict}*}

lemma restrict_in_funcset: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> A \<rightarrow> B"
  by (simp add: Pi_def restrict_def)

lemma restrictI[intro!]: "(\<And>x. x \<in> A \<Longrightarrow> f x \<in> B x) \<Longrightarrow> (\<lambda>x\<in>A. f x) \<in> Pi A B"
  by (simp add: Pi_def restrict_def)

lemma restrict_apply[simp]: "(\<lambda>y\<in>A. f y) x = (if x \<in> A then f x else undefined)"
  by (simp add: restrict_def)

lemma restrict_apply': "x \<in> A \<Longrightarrow> (\<lambda>y\<in>A. f y) x = f x"
  by simp

lemma restrict_ext:
    "(\<And>x. x \<in> A \<Longrightarrow> f x = g x) \<Longrightarrow> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)"
  by (simp add: fun_eq_iff Pi_def restrict_def)

lemma inj_on_restrict_eq [simp]: "inj_on (restrict f A) A = inj_on f A"
  by (simp add: inj_on_def restrict_def)

lemma Id_compose:
    "[|f \<in> A -> B;  f \<in> extensional A|] ==> compose A (\<lambda>y\<in>B. y) f = f"
  by (auto simp add: fun_eq_iff compose_def extensional_def Pi_def)

lemma compose_Id:
    "[|g \<in> A -> B;  g \<in> extensional A|] ==> compose A g (\<lambda>x\<in>A. x) = g"
  by (auto simp add: fun_eq_iff compose_def extensional_def Pi_def)

lemma image_restrict_eq [simp]: "(restrict f A) ` A = f ` A"
  by (auto simp add: restrict_def)

lemma restrict_restrict[simp]: "restrict (restrict f A) B = restrict f (A \<inter> B)"
  unfolding restrict_def by (simp add: fun_eq_iff)

lemma restrict_fupd[simp]: "i \<notin> I \<Longrightarrow> restrict (f (i := x)) I = restrict f I"
  by (auto simp: restrict_def)

lemma restrict_upd[simp]:
  "i \<notin> I \<Longrightarrow> (restrict f I)(i := y) = restrict (f(i := y)) (insert i I)"
  by (auto simp: fun_eq_iff)

lemma restrict_Pi_cancel: "restrict x I \<in> Pi I A \<longleftrightarrow> x \<in> Pi I A"
  by (auto simp: restrict_def Pi_def)


subsection{*Bijections Between Sets*}

text{*The definition of @{const bij_betw} is in @{text "Fun.thy"}, but most of
the theorems belong here, or need at least @{term Hilbert_Choice}.*}

lemma bij_betwI:
assumes "f \<in> A \<rightarrow> B" and "g \<in> B \<rightarrow> A"
    and g_f: "\<And>x. x\<in>A \<Longrightarrow> g (f x) = x" and f_g: "\<And>y. y\<in>B \<Longrightarrow> f (g y) = y"
shows "bij_betw f A B"
unfolding bij_betw_def
proof
  show "inj_on f A" by (metis g_f inj_on_def)
next
  have "f ` A \<subseteq> B" using `f \<in> A \<rightarrow> B` by auto
  moreover
  have "B \<subseteq> f ` A" by auto (metis Pi_mem `g \<in> B \<rightarrow> A` f_g image_iff)
  ultimately show "f ` A = B" by blast
qed

lemma bij_betw_imp_funcset: "bij_betw f A B \<Longrightarrow> f \<in> A \<rightarrow> B"
by (auto simp add: bij_betw_def)

lemma inj_on_compose:
  "[| bij_betw f A B; inj_on g B |] ==> inj_on (compose A g f) A"
by (auto simp add: bij_betw_def inj_on_def compose_eq)

lemma bij_betw_compose:
  "[| bij_betw f A B; bij_betw g B C |] ==> bij_betw (compose A g f) A C"
apply (simp add: bij_betw_def compose_eq inj_on_compose)
apply (auto simp add: compose_def image_def)
done

lemma bij_betw_restrict_eq [simp]:
  "bij_betw (restrict f A) A B = bij_betw f A B"
by (simp add: bij_betw_def)


subsection{*Extensionality*}

lemma extensional_empty[simp]: "extensional {} = {\<lambda>x. undefined}"
  unfolding extensional_def by auto

lemma extensional_arb: "[|f \<in> extensional A; x\<notin> A|] ==> f x = undefined"
by (simp add: extensional_def)

lemma restrict_extensional [simp]: "restrict f A \<in> extensional A"
by (simp add: restrict_def extensional_def)

lemma compose_extensional [simp]: "compose A f g \<in> extensional A"
by (simp add: compose_def)

lemma extensionalityI:
  "[| f \<in> extensional A; g \<in> extensional A;
      !!x. x\<in>A ==> f x = g x |] ==> f = g"
by (force simp add: fun_eq_iff extensional_def)

lemma extensional_restrict:  "f \<in> extensional A \<Longrightarrow> restrict f A = f"
by(rule extensionalityI[OF restrict_extensional]) auto

lemma extensional_subset: "f \<in> extensional A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f \<in> extensional B"
  unfolding extensional_def by auto

lemma inv_into_funcset: "f ` A = B ==> (\<lambda>x\<in>B. inv_into A f x) : B -> A"
by (unfold inv_into_def) (fast intro: someI2)

lemma compose_inv_into_id:
  "bij_betw f A B ==> compose A (\<lambda>y\<in>B. inv_into A f y) f = (\<lambda>x\<in>A. x)"
apply (simp add: bij_betw_def compose_def)
apply (rule restrict_ext, auto)
done

lemma compose_id_inv_into:
  "f ` A = B ==> compose B f (\<lambda>y\<in>B. inv_into A f y) = (\<lambda>x\<in>B. x)"
apply (simp add: compose_def)
apply (rule restrict_ext)
apply (simp add: f_inv_into_f)
done

lemma extensional_insert[intro, simp]:
  assumes "a \<in> extensional (insert i I)"
  shows "a(i := b) \<in> extensional (insert i I)"
  using assms unfolding extensional_def by auto

lemma extensional_Int[simp]:
  "extensional I \<inter> extensional I' = extensional (I \<inter> I')"
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


subsection{*Cardinality*}

lemma card_inj: "[|f \<in> A\<rightarrow>B; inj_on f A; finite B|] ==> card(A) \<le> card(B)"
by (rule card_inj_on_le) auto

lemma card_bij:
  "[|f \<in> A\<rightarrow>B; inj_on f A;
     g \<in> B\<rightarrow>A; inj_on g B; finite A; finite B|] ==> card(A) = card(B)"
by (blast intro: card_inj order_antisym)

subsection {* Extensional Function Spaces *} 

definition PiE :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "PiE S T = Pi S T \<inter> extensional S"

abbreviation "Pi\<^sub>E A B \<equiv> PiE A B"

syntax "_PiE"  :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3PIE _:_./ _)" 10)

syntax (xsymbols) "_PiE" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi>\<^sub>E _\<in>_./ _)" 10)

syntax (HTML output) "_PiE" :: "[pttrn, 'a set, 'b set] => ('a => 'b) set"  ("(3\<Pi>\<^sub>E _\<in>_./ _)" 10)

translations "PIE x:A. B" \<rightleftharpoons> "CONST Pi\<^sub>E A (%x. B)"

abbreviation extensional_funcset :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "->\<^sub>E" 60) where
  "A ->\<^sub>E B \<equiv> (\<Pi>\<^sub>E i\<in>A. B)"

notation (xsymbols)
  extensional_funcset  (infixr "\<rightarrow>\<^sub>E" 60)

lemma extensional_funcset_def: "extensional_funcset S T = (S -> T) \<inter> extensional S"
  by (simp add: PiE_def)

lemma PiE_empty_domain[simp]: "PiE {} T = {%x. undefined}"
  unfolding PiE_def by simp

lemma PiE_UNIV_domain: "PiE UNIV T = Pi UNIV T"
  unfolding PiE_def by simp

lemma PiE_empty_range[simp]: "i \<in> I \<Longrightarrow> F i = {} \<Longrightarrow> (PIE i:I. F i) = {}"
  unfolding PiE_def by auto

lemma PiE_eq_empty_iff:
  "Pi\<^sub>E I F = {} \<longleftrightarrow> (\<exists>i\<in>I. F i = {})"
proof
  assume "Pi\<^sub>E I F = {}"
  show "\<exists>i\<in>I. F i = {}"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then have "\<forall>i. \<exists>y. (i \<in> I \<longrightarrow> y \<in> F i) \<and> (i \<notin> I \<longrightarrow> y = undefined)" by auto
    from choice[OF this]
    obtain f where " \<forall>x. (x \<in> I \<longrightarrow> f x \<in> F x) \<and> (x \<notin> I \<longrightarrow> f x = undefined)" ..
    then have "f \<in> Pi\<^sub>E I F" by (auto simp: extensional_def PiE_def)
    with `Pi\<^sub>E I F = {}` show False by auto
  qed
qed (auto simp: PiE_def)

lemma PiE_arb: "f \<in> PiE S T \<Longrightarrow> x \<notin> S \<Longrightarrow> f x = undefined"
  unfolding PiE_def by auto (auto dest!: extensional_arb)

lemma PiE_mem: "f \<in> PiE S T \<Longrightarrow> x \<in> S \<Longrightarrow> f x \<in> T x"
  unfolding PiE_def by auto

lemma PiE_fun_upd: "y \<in> T x \<Longrightarrow> f \<in> PiE S T \<Longrightarrow> f(x := y) \<in> PiE (insert x S) T"
  unfolding PiE_def extensional_def by auto

lemma fun_upd_in_PiE: "x \<notin> S \<Longrightarrow> f \<in> PiE (insert x S) T \<Longrightarrow> f(x := undefined) \<in> PiE S T"
  unfolding PiE_def extensional_def by auto

lemma PiE_insert_eq:
  assumes "x \<notin> S"
  shows "PiE (insert x S) T = (\<lambda>(y, g). g(x := y)) ` (T x \<times> PiE S T)"
proof -
  {
    fix f assume "f \<in> PiE (insert x S) T"
    with assms have "f \<in> (\<lambda>(y, g). g(x := y)) ` (T x \<times> PiE S T)"
      by (auto intro!: image_eqI[where x="(f x, f(x := undefined))"] intro: fun_upd_in_PiE PiE_mem)
  }
  then show ?thesis using assms by (auto intro: PiE_fun_upd)
qed

lemma PiE_Int: "(Pi\<^sub>E I A) \<inter> (Pi\<^sub>E I B) = Pi\<^sub>E I (\<lambda>x. A x \<inter> B x)"
  by (auto simp: PiE_def)

lemma PiE_cong:
  "(\<And>i. i\<in>I \<Longrightarrow> A i = B i) \<Longrightarrow> Pi\<^sub>E I A = Pi\<^sub>E I B"
  unfolding PiE_def by (auto simp: Pi_cong)

lemma PiE_E [elim]:
  "f \<in> PiE A B \<Longrightarrow> (x \<in> A \<Longrightarrow> f x \<in> B x \<Longrightarrow> Q) \<Longrightarrow> (x \<notin> A \<Longrightarrow> f x = undefined \<Longrightarrow> Q) \<Longrightarrow> Q"
by(auto simp: Pi_def PiE_def extensional_def)

lemma PiE_I[intro!]: "(\<And>x. x \<in> A ==> f x \<in> B x) \<Longrightarrow> (\<And>x. x \<notin> A \<Longrightarrow> f x = undefined) \<Longrightarrow> f \<in> PiE A B"
  by (simp add: PiE_def extensional_def)

lemma PiE_mono: "(\<And>x. x \<in> A \<Longrightarrow> B x \<subseteq> C x) \<Longrightarrow> PiE A B \<subseteq> PiE A C"
  by auto

lemma PiE_iff: "f \<in> PiE I X \<longleftrightarrow> (\<forall>i\<in>I. f i \<in> X i) \<and> f \<in> extensional I"
  by (simp add: PiE_def Pi_iff)

lemma PiE_restrict[simp]:  "f \<in> PiE A B \<Longrightarrow> restrict f A = f"
  by (simp add: extensional_restrict PiE_def)

lemma restrict_PiE[simp]: "restrict f I \<in> PiE I S \<longleftrightarrow> f \<in> Pi I S"
  by (auto simp: PiE_iff)

lemma PiE_eq_subset:
  assumes ne: "\<And>i. i \<in> I \<Longrightarrow> F i \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow> F' i \<noteq> {}"
  assumes eq: "Pi\<^sub>E I F = Pi\<^sub>E I F'" and "i \<in> I"
  shows "F i \<subseteq> F' i"
proof
  fix x assume "x \<in> F i"
  with ne have "\<forall>j. \<exists>y. ((j \<in> I \<longrightarrow> y \<in> F j \<and> (i = j \<longrightarrow> x = y)) \<and> (j \<notin> I \<longrightarrow> y = undefined))"
    by auto
  from choice[OF this] obtain f
    where f: " \<forall>j. (j \<in> I \<longrightarrow> f j \<in> F j \<and> (i = j \<longrightarrow> x = f j)) \<and> (j \<notin> I \<longrightarrow> f j = undefined)" ..
  then have "f \<in> Pi\<^sub>E I F" by (auto simp: extensional_def PiE_def)
  then have "f \<in> Pi\<^sub>E I F'" using assms by simp
  then show "x \<in> F' i" using f `i \<in> I` by (auto simp: PiE_def)
qed

lemma PiE_eq_iff_not_empty:
  assumes ne: "\<And>i. i \<in> I \<Longrightarrow> F i \<noteq> {}" "\<And>i. i \<in> I \<Longrightarrow> F' i \<noteq> {}"
  shows "Pi\<^sub>E I F = Pi\<^sub>E I F' \<longleftrightarrow> (\<forall>i\<in>I. F i = F' i)"
proof (intro iffI ballI)
  fix i assume eq: "Pi\<^sub>E I F = Pi\<^sub>E I F'" and i: "i \<in> I"
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
  with PiE_eq_iff_not_empty[of I F F'] show "\<forall>i\<in>I. F i = F' i" by auto
next
  assume "(\<forall>i\<in>I. F i = F' i) \<or> (\<exists>i\<in>I. F i = {}) \<and> (\<exists>i\<in>I. F' i = {})"
  then show "Pi\<^sub>E I F = Pi\<^sub>E I F'"
    using PiE_eq_empty_iff[of I F] PiE_eq_empty_iff[of I F'] by (auto simp: PiE_def)
qed

lemma extensional_funcset_fun_upd_restricts_rangeI: 
  "\<forall>y \<in> S. f x \<noteq> f y \<Longrightarrow> f : (insert x S) \<rightarrow>\<^sub>E T ==> f(x := undefined) : S \<rightarrow>\<^sub>E (T - {f x})"
  unfolding extensional_funcset_def extensional_def
  apply auto
  apply (case_tac "x = xa")
  apply auto
  done

lemma extensional_funcset_fun_upd_extends_rangeI:
  assumes "a \<in> T" "f \<in> S \<rightarrow>\<^sub>E (T - {a})"
  shows "f(x := a) \<in> (insert x S) \<rightarrow>\<^sub>E  T"
  using assms unfolding extensional_funcset_def extensional_def by auto

subsubsection {* Injective Extensional Function Spaces *}

lemma extensional_funcset_fun_upd_inj_onI:
  assumes "f \<in> S \<rightarrow>\<^sub>E (T - {a})" "inj_on f S"
  shows "inj_on (f(x := a)) S"
  using assms unfolding extensional_funcset_def by (auto intro!: inj_on_fun_updI)

lemma extensional_funcset_extend_domain_inj_on_eq:
  assumes "x \<notin> S"
  shows"{f. f \<in> (insert x S) \<rightarrow>\<^sub>E T \<and> inj_on f (insert x S)} =
    (%(y, g). g(x:=y)) ` {(y, g). y \<in> T \<and> g \<in> S \<rightarrow>\<^sub>E (T - {y}) \<and> inj_on g S}"
proof -
  from assms show ?thesis
    apply (auto del: PiE_I PiE_E)
    apply (auto intro: extensional_funcset_fun_upd_inj_onI extensional_funcset_fun_upd_extends_rangeI del: PiE_I PiE_E)
    apply (auto simp add: image_iff inj_on_def)
    apply (rule_tac x="xa x" in exI)
    apply (auto intro: PiE_mem del: PiE_I PiE_E)
    apply (rule_tac x="xa(x := undefined)" in exI)
    apply (auto intro!: extensional_funcset_fun_upd_restricts_rangeI)
    apply (auto dest!: PiE_mem split: split_if_asm)
    done
qed

lemma extensional_funcset_extend_domain_inj_onI:
  assumes "x \<notin> S"
  shows "inj_on (\<lambda>(y, g). g(x := y)) {(y, g). y \<in> T \<and> g \<in> S \<rightarrow>\<^sub>E (T - {y}) \<and> inj_on g S}"
proof -
  from assms show ?thesis
    apply (auto intro!: inj_onI)
    apply (metis fun_upd_same)
    by (metis assms PiE_arb fun_upd_triv fun_upd_upd)
qed
  

subsubsection {* Cardinality *}

lemma finite_PiE: "finite S \<Longrightarrow> (\<And>i. i \<in> S \<Longrightarrow> finite (T i)) \<Longrightarrow> finite (PIE i : S. T i)"
  by (induct S arbitrary: T rule: finite_induct) (simp_all add: PiE_insert_eq)

lemma inj_combinator: "x \<notin> S \<Longrightarrow> inj_on (\<lambda>(y, g). g(x := y)) (T x \<times> Pi\<^sub>E S T)"
proof (safe intro!: inj_onI ext)
  fix f y g z assume "x \<notin> S" and fg: "f \<in> Pi\<^sub>E S T" "g \<in> Pi\<^sub>E S T"
  assume "f(x := y) = g(x := z)"
  then have *: "\<And>i. (f(x := y)) i = (g(x := z)) i"
    unfolding fun_eq_iff by auto
  from this[of x] show "y = z" by simp
  fix i from *[of i] `x \<notin> S` fg show "f i = g i"
    by (auto split: split_if_asm simp: PiE_def extensional_def)
qed

lemma card_PiE:
  "finite S \<Longrightarrow> card (PIE i : S. T i) = (\<Prod> i\<in>S. card (T i))"
proof (induct rule: finite_induct)
  case empty then show ?case by auto
next
  case (insert x S) then show ?case
    by (simp add: PiE_insert_eq inj_combinator card_image card_cartesian_product)
qed

end
