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
  "A -> B == Pi A (%_. B)"

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
  "PI x:A. B" == "CONST Pi A (%x. B)"
  "%x:A. f" == "CONST restrict (%x. f) A"

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

lemma Pi_eq_empty[simp]: "((PI x: A. B x) = {}) = (\<exists>x\<in>A. B(x) = {})"
apply (simp add: Pi_def, auto)
txt{*Converse direction requires Axiom of Choice to exhibit a function
picking an element from each non-empty @{term "B x"}*}
apply (drule_tac x = "%u. SOME y. y \<in> B u" in spec, auto)
apply (cut_tac P= "%y. y \<in> B x" in some_eq_ex, auto)
done

lemma Pi_empty [simp]: "Pi {} B = UNIV"
by (simp add: Pi_def)

lemma Pi_UNIV [simp]: "A -> UNIV = UNIV"
by (simp add: Pi_def)
(*
lemma funcset_id [simp]: "(%x. x): A -> A"
  by (simp add: Pi_def)
*)
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

lemma restrict_in_funcset: "(!!x. x \<in> A ==> f x \<in> B) ==> (\<lambda>x\<in>A. f x) \<in> A -> B"
  by (simp add: Pi_def restrict_def)

lemma restrictI[intro!]: "(!!x. x \<in> A ==> f x \<in> B x) ==> (\<lambda>x\<in>A. f x) \<in> Pi A B"
  by (simp add: Pi_def restrict_def)

lemma restrict_apply [simp]:
    "(\<lambda>y\<in>A. f y) x = (if x \<in> A then f x else undefined)"
  by (simp add: restrict_def)

lemma restrict_ext:
    "(!!x. x \<in> A ==> f x = g x) ==> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)"
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


subsection{*Cardinality*}

lemma card_inj: "[|f \<in> A\<rightarrow>B; inj_on f A; finite B|] ==> card(A) \<le> card(B)"
by (rule card_inj_on_le) auto

lemma card_bij:
  "[|f \<in> A\<rightarrow>B; inj_on f A;
     g \<in> B\<rightarrow>A; inj_on g B; finite A; finite B|] ==> card(A) = card(B)"
by (blast intro: card_inj order_antisym)

subsection {* Extensional Function Spaces *} 

definition extensional_funcset
where "extensional_funcset S T = (S -> T) \<inter> (extensional S)"

lemma extensional_empty[simp]: "extensional {} = {%x. undefined}"
unfolding extensional_def by auto

lemma extensional_funcset_empty_domain: "extensional_funcset {} T = {%x. undefined}"
unfolding extensional_funcset_def by simp

lemma extensional_funcset_empty_range:
  assumes "S \<noteq> {}"
  shows "extensional_funcset S {} = {}"
using assms unfolding extensional_funcset_def by auto

lemma extensional_funcset_arb:
  assumes "f \<in> extensional_funcset S T" "x \<notin> S"
  shows "f x = undefined"
using assms
unfolding extensional_funcset_def by auto (auto dest!: extensional_arb)

lemma extensional_funcset_mem: "f \<in> extensional_funcset S T \<Longrightarrow> x \<in> S \<Longrightarrow> f x \<in> T"
unfolding extensional_funcset_def by auto

lemma extensional_subset: "f : extensional A ==> A <= B ==> f : extensional B"
unfolding extensional_def by auto

lemma extensional_funcset_extend_domainI: "\<lbrakk> y \<in> T; f \<in> extensional_funcset S T\<rbrakk> \<Longrightarrow> f(x := y) \<in> extensional_funcset (insert x S) T"
unfolding extensional_funcset_def extensional_def by auto

lemma extensional_funcset_restrict_domain:
  "x \<notin> S \<Longrightarrow> f \<in> extensional_funcset (insert x S) T \<Longrightarrow> f(x := undefined) \<in> extensional_funcset S T"
unfolding extensional_funcset_def extensional_def by auto

lemma extensional_funcset_extend_domain_eq:
  assumes "x \<notin> S"
  shows
    "extensional_funcset (insert x S) T = (\<lambda>(y, g). g(x := y)) ` {(y, g). y \<in> T \<and> g \<in> extensional_funcset S T}"
  using assms
proof -
  {
    fix f
    assume "f : extensional_funcset (insert x S) T"
    from this assms have "f : (%(y, g). g(x := y)) ` (T <*> extensional_funcset S T)"
      unfolding image_iff
      apply (rule_tac x="(f x, f(x := undefined))" in bexI)
    apply (auto intro: extensional_funcset_extend_domainI extensional_funcset_restrict_domain extensional_funcset_mem) done 
  }
  moreover
  {
    fix f
    assume "f : (%(y, g). g(x := y)) ` (T <*> extensional_funcset S T)"
    from this assms have "f : extensional_funcset (insert x S) T"
      by (auto intro: extensional_funcset_extend_domainI)
  }
  ultimately show ?thesis by auto
qed

lemma extensional_funcset_fun_upd_restricts_rangeI:  "\<forall> y \<in> S. f x \<noteq> f y ==> f : extensional_funcset (insert x S) T ==> f(x := undefined) : extensional_funcset S (T - {f x})"
unfolding extensional_funcset_def extensional_def
apply auto
apply (case_tac "x = xa")
apply auto done

lemma extensional_funcset_fun_upd_extends_rangeI:
  assumes "a \<in> T" "f : extensional_funcset S (T - {a})"
  shows "f(x := a) : extensional_funcset (insert x S) T"
  using assms unfolding extensional_funcset_def extensional_def by auto

subsubsection {* Injective Extensional Function Spaces *}

lemma extensional_funcset_fun_upd_inj_onI:
  assumes "f \<in> extensional_funcset S (T - {a})" "inj_on f S"
  shows "inj_on (f(x := a)) S"
  using assms unfolding extensional_funcset_def by (auto intro!: inj_on_fun_updI)

lemma extensional_funcset_extend_domain_inj_on_eq:
  assumes "x \<notin> S"
  shows"{f. f \<in> extensional_funcset (insert x S) T \<and> inj_on f (insert x S)} =
    (%(y, g). g(x:=y)) ` {(y, g). y \<in> T \<and> g \<in> extensional_funcset S (T - {y}) \<and> inj_on g S}"
proof -
  from assms show ?thesis
    apply auto
    apply (auto intro: extensional_funcset_fun_upd_inj_onI extensional_funcset_fun_upd_extends_rangeI)
    apply (auto simp add: image_iff inj_on_def)
    apply (rule_tac x="xa x" in exI)
    apply (auto intro: extensional_funcset_mem)
    apply (rule_tac x="xa(x := undefined)" in exI)
    apply (auto intro!: extensional_funcset_fun_upd_restricts_rangeI)
    apply (auto dest!: extensional_funcset_mem split: split_if_asm)
    done
qed

lemma extensional_funcset_extend_domain_inj_onI:
  assumes "x \<notin> S"
  shows "inj_on (\<lambda>(y, g). g(x := y)) {(y, g). y \<in> T \<and> g \<in> extensional_funcset S (T - {y}) \<and> inj_on g S}"
proof -
  from assms show ?thesis
    apply (auto intro!: inj_onI)
    apply (metis fun_upd_same)
    by (metis assms extensional_funcset_arb fun_upd_triv fun_upd_upd)
qed
  

subsubsection {* Cardinality *}

lemma card_extensional_funcset:
  assumes "finite S"
  shows "card (extensional_funcset S T) = (card T) ^ (card S)"
using assms
proof (induct rule: finite_induct)
  case empty
  show ?case
    by (auto simp add: extensional_funcset_empty_domain)
next
  case (insert x S)
  {
    fix g g' y y'
    assume assms: "g \<in> extensional_funcset S T"
      "g' \<in> extensional_funcset S T"
      "y \<in> T" "y' \<in> T"
      "g(x := y) = g'(x := y')"
    from this have "y = y'"
      by (metis fun_upd_same)
    have "g = g'"
      by (metis assms(1) assms(2) assms(5) extensional_funcset_arb fun_upd_triv fun_upd_upd insert(2))
  from `y = y'` `g = g'` have "y = y' & g = g'" by simp
  }
  from this have "inj_on (\<lambda>(y, g). g (x := y)) (T \<times> extensional_funcset S T)"
    by (auto intro: inj_onI)
  from this insert.hyps show ?case
    by (simp add: extensional_funcset_extend_domain_eq card_image card_cartesian_product)
qed

lemma finite_extensional_funcset:
  assumes "finite S" "finite T"
  shows "finite (extensional_funcset S T)"
proof -
  from card_extensional_funcset[OF assms(1), of T] assms(2)
  have "(card (extensional_funcset S T) \<noteq> 0) \<or> (S \<noteq> {} \<and> T = {})"
    by auto
  from this show ?thesis
  proof
    assume "card (extensional_funcset S T) \<noteq> 0"
    from this show ?thesis
      by (auto intro: card_ge_0_finite)
  next
    assume "S \<noteq> {} \<and> T = {}"
    from this show ?thesis
      by (auto simp add: extensional_funcset_empty_range)
  qed
qed

end
