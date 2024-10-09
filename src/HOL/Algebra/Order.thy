(*  Title:      HOL/Algebra/Order.thy
    Author:     Clemens Ballarin, started 7 November 2003
    Copyright:  Clemens Ballarin

Most congruence rules by Stephan Hohe.
With additional contributions from Alasdair Armstrong and Simon Foster.
*)

theory Order
  imports
    Congruence
begin

section \<open>Orders\<close>

subsection \<open>Partial Orders\<close>

record 'a gorder = "'a eq_object" +
  le :: "['a, 'a] => bool" (infixl \<open>\<sqsubseteq>\<index>\<close> 50)

abbreviation inv_gorder :: "_ \<Rightarrow> 'a gorder" where
  "inv_gorder L \<equiv>
   \<lparr> carrier = carrier L,
     eq = (.=\<^bsub>L\<^esub>),
     le = (\<lambda> x y. y \<sqsubseteq>\<^bsub>L \<^esub>x) \<rparr>"

lemma inv_gorder_inv:
  "inv_gorder (inv_gorder L) = L"
  by simp

locale weak_partial_order = equivalence L for L (structure) +
  assumes le_refl [intro, simp]:
      "x \<in> carrier L \<Longrightarrow> x \<sqsubseteq> x"
    and weak_le_antisym [intro]:
      "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier L; y \<in> carrier L\<rbrakk> \<Longrightarrow> x .= y"
    and le_trans [trans]:
      "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
    and le_cong:
      "\<lbrakk>x .= y; z .= w; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L; w \<in> carrier L\<rbrakk> \<Longrightarrow>
      x \<sqsubseteq> z \<longleftrightarrow> y \<sqsubseteq> w"

definition
  lless :: "[_, 'a, 'a] => bool" (infixl \<open>\<sqsubset>\<index>\<close> 50)
  where "x \<sqsubset>\<^bsub>L\<^esub> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>L\<^esub> y \<and> x .\<noteq>\<^bsub>L\<^esub> y"

subsubsection \<open>The order relation\<close>

context weak_partial_order
begin

lemma le_cong_l [intro, trans]:
  "\<lbrakk>x .= y; y \<sqsubseteq> z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  by (auto intro: le_cong [THEN iffD2])

lemma le_cong_r [intro, trans]:
  "\<lbrakk>x \<sqsubseteq> y; y .= z; x \<in> carrier L; y \<in> carrier L; z \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"
  by (auto intro: le_cong [THEN iffD1])

lemma weak_refl [intro, simp]: "\<lbrakk>x .= y; x \<in> carrier L; y \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y"
  by (simp add: le_cong_l)

end

lemma weak_llessI:
  fixes R (structure)
  assumes "x \<sqsubseteq> y" and "\<not>(x .= y)"
  shows "x \<sqsubset> y"
  using assms unfolding lless_def by simp

lemma lless_imp_le:
  fixes R (structure)
  assumes "x \<sqsubset> y"
  shows "x \<sqsubseteq> y"
  using assms unfolding lless_def by simp

lemma weak_lless_imp_not_eq:
  fixes R (structure)
  assumes "x \<sqsubset> y"
  shows "\<not> (x .= y)"
  using assms unfolding lless_def by simp

lemma weak_llessE:
  fixes R (structure)
  assumes p: "x \<sqsubset> y" and e: "\<lbrakk>x \<sqsubseteq> y; \<not> (x .= y)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using p by (blast dest: lless_imp_le weak_lless_imp_not_eq e)

lemma (in weak_partial_order) lless_cong_l [trans]:
  assumes xx': "x .= x'"
    and xy: "x' \<sqsubset> y"
    and carr: "x \<in> carrier L" "x' \<in> carrier L" "y \<in> carrier L"
  shows "x \<sqsubset> y"
  using assms unfolding lless_def by (auto intro: trans sym)

lemma (in weak_partial_order) lless_cong_r [trans]:
  assumes xy: "x \<sqsubset> y"
    and  yy': "y .= y'"
    and carr: "x \<in> carrier L" "y \<in> carrier L" "y' \<in> carrier L"
  shows "x \<sqsubset> y'"
  using assms unfolding lless_def by (auto intro: trans sym)  (*slow*)


lemma (in weak_partial_order) lless_antisym:
  assumes "a \<in> carrier L" "b \<in> carrier L"
    and "a \<sqsubset> b" "b \<sqsubset> a"
  shows "P"
  using assms
  by (elim weak_llessE) auto

lemma (in weak_partial_order) lless_trans [trans]:
  assumes "a \<sqsubset> b" "b \<sqsubset> c"
    and carr[simp]: "a \<in> carrier L" "b \<in> carrier L" "c \<in> carrier L"
  shows "a \<sqsubset> c"
  using assms unfolding lless_def by (blast dest: le_trans intro: sym)

lemma weak_partial_order_subset:
  assumes "weak_partial_order L" "A \<subseteq> carrier L"
  shows "weak_partial_order (L\<lparr> carrier := A \<rparr>)"
proof -
  interpret L: weak_partial_order L
    by (simp add: assms)
  interpret equivalence "(L\<lparr> carrier := A \<rparr>)"
    by (simp add: L.equivalence_axioms assms(2) equivalence_subset)
  show ?thesis
    apply (unfold_locales, simp_all)
    using assms(2) apply auto[1]
    using assms(2) apply auto[1]
    apply (meson L.le_trans assms(2) contra_subsetD)
    apply (meson L.le_cong assms(2) subsetCE)
  done
qed


subsubsection \<open>Upper and lower bounds of a set\<close>

definition
  Upper :: "[_, 'a set] => 'a set"
  where "Upper L A = {u. (\<forall>x. x \<in> A \<inter> carrier L \<longrightarrow> x \<sqsubseteq>\<^bsub>L\<^esub> u)} \<inter> carrier L"

definition
  Lower :: "[_, 'a set] => 'a set"
  where "Lower L A = {l. (\<forall>x. x \<in> A \<inter> carrier L \<longrightarrow> l \<sqsubseteq>\<^bsub>L\<^esub> x)} \<inter> carrier L"

lemma Lower_dual [simp]:
  "Lower (inv_gorder L) A = Upper L A"
  by (simp add:Upper_def Lower_def)

lemma Upper_dual [simp]:
  "Upper (inv_gorder L) A = Lower L A"
  by (simp add:Upper_def Lower_def)

lemma (in weak_partial_order) equivalence_dual: "equivalence (inv_gorder L)"
  by (rule equivalence.intro) (auto simp: intro: sym trans)

lemma  (in weak_partial_order) dual_weak_order: "weak_partial_order (inv_gorder L)"
  by intro_locales (auto simp add: weak_partial_order_axioms_def le_cong intro: equivalence_dual le_trans)

lemma (in weak_partial_order) dual_eq_iff [simp]: "A {.=}\<^bsub>inv_gorder L\<^esub> A' \<longleftrightarrow> A {.=} A'"
  by (auto simp: set_eq_def elem_def)

lemma dual_weak_order_iff:
  "weak_partial_order (inv_gorder A) \<longleftrightarrow> weak_partial_order A"
proof
  assume "weak_partial_order (inv_gorder A)"
  then interpret dpo: weak_partial_order "inv_gorder A"
  rewrites "carrier (inv_gorder A) = carrier A"
  and   "le (inv_gorder A)      = (\<lambda> x y. le A y x)"
  and   "eq (inv_gorder A)      = eq A"
    by (simp_all)
  show "weak_partial_order A"
    by (unfold_locales, auto intro: dpo.sym dpo.trans dpo.le_trans)
next
  assume "weak_partial_order A"
  thus "weak_partial_order (inv_gorder A)"
    by (metis weak_partial_order.dual_weak_order)
qed

lemma Upper_closed [iff]:
  "Upper L A \<subseteq> carrier L"
  by (unfold Upper_def) clarify

lemma Upper_memD [dest]:
  fixes L (structure)
  shows "\<lbrakk>u \<in> Upper L A; x \<in> A; A \<subseteq> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> u \<and> u \<in> carrier L"
  by (unfold Upper_def) blast

lemma (in weak_partial_order) Upper_elemD [dest]:
  "\<lbrakk>u .\<in> Upper L A; u \<in> carrier L; x \<in> A; A \<subseteq> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> u"
  unfolding Upper_def elem_def
  by (blast dest: sym)

lemma Upper_memI:
  fixes L (structure)
  shows "\<lbrakk>!! y. y \<in> A \<Longrightarrow> y \<sqsubseteq> x; x \<in> carrier L\<rbrakk> \<Longrightarrow> x \<in> Upper L A"
  by (unfold Upper_def) blast

lemma (in weak_partial_order) Upper_elemI:
  "\<lbrakk>!! y. y \<in> A \<Longrightarrow> y \<sqsubseteq> x; x \<in> carrier L\<rbrakk> \<Longrightarrow> x .\<in> Upper L A"
  unfolding Upper_def by blast

lemma Upper_antimono:
  "A \<subseteq> B \<Longrightarrow> Upper L B \<subseteq> Upper L A"
  by (unfold Upper_def) blast

lemma (in weak_partial_order) Upper_is_closed [simp]:
  "A \<subseteq> carrier L \<Longrightarrow> is_closed (Upper L A)"
  by (rule is_closedI) (blast intro: Upper_memI)+

lemma (in weak_partial_order) Upper_mem_cong:
  assumes  "a' \<in> carrier L" "A \<subseteq> carrier L" "a .= a'" "a \<in> Upper L A"
  shows "a' \<in> Upper L A"
  by (metis assms Upper_closed Upper_is_closed closure_of_eq complete_classes)

lemma (in weak_partial_order) Upper_semi_cong:
  assumes "A \<subseteq> carrier L" "A {.=} A'"
  shows "Upper L A \<subseteq> Upper L A'"
  unfolding Upper_def
   by clarsimp (meson assms equivalence.refl equivalence_axioms le_cong set_eqD2 subset_eq)

lemma (in weak_partial_order) Upper_cong:
  assumes "A \<subseteq> carrier L" "A' \<subseteq> carrier L" "A {.=} A'"
  shows "Upper L A = Upper L A'"
  using assms by (simp add: Upper_semi_cong set_eq_sym subset_antisym)

lemma Lower_closed [intro!, simp]:
  "Lower L A \<subseteq> carrier L"
  by (unfold Lower_def) clarify

lemma Lower_memD [dest]:
  fixes L (structure)
  shows "\<lbrakk>l \<in> Lower L A; x \<in> A; A \<subseteq> carrier L\<rbrakk> \<Longrightarrow> l \<sqsubseteq> x \<and> l \<in> carrier L"
  by (unfold Lower_def) blast

lemma Lower_memI:
  fixes L (structure)
  shows "\<lbrakk>!! y. y \<in> A \<Longrightarrow> x \<sqsubseteq> y; x \<in> carrier L\<rbrakk> \<Longrightarrow> x \<in> Lower L A"
  by (unfold Lower_def) blast

lemma Lower_antimono:
  "A \<subseteq> B \<Longrightarrow> Lower L B \<subseteq> Lower L A"
  by (unfold Lower_def) blast

lemma (in weak_partial_order) Lower_is_closed [simp]:
  "A \<subseteq> carrier L \<Longrightarrow> is_closed (Lower L A)"
  by (rule is_closedI) (blast intro: Lower_memI dest: sym)+

lemma (in weak_partial_order) Lower_mem_cong:
  assumes "a' \<in> carrier L"  "A \<subseteq> carrier L" "a .= a'" "a \<in> Lower L A"
  shows "a' \<in> Lower L A"
  by (meson assms Lower_closed Lower_is_closed is_closed_eq subsetCE)

lemma (in weak_partial_order) Lower_cong:
  assumes "A \<subseteq> carrier L" "A' \<subseteq> carrier L" "A {.=} A'"
  shows "Lower L A = Lower L A'"
  unfolding Upper_dual [symmetric]
  by (rule weak_partial_order.Upper_cong [OF dual_weak_order]) (simp_all add: assms)

text \<open>Jacobson: Theorem 8.1\<close>

lemma Lower_empty [simp]:
  "Lower L {} = carrier L"
  by (unfold Lower_def) simp

lemma Upper_empty [simp]:
  "Upper L {} = carrier L"
  by (unfold Upper_def) simp


subsubsection \<open>Least and greatest, as predicate\<close>

definition
  least :: "[_, 'a, 'a set] => bool"
  where "least L l A \<longleftrightarrow> A \<subseteq> carrier L \<and> l \<in> A \<and> (\<forall>x\<in>A. l \<sqsubseteq>\<^bsub>L\<^esub> x)"

definition
  greatest :: "[_, 'a, 'a set] => bool"
  where "greatest L g A \<longleftrightarrow> A \<subseteq> carrier L \<and> g \<in> A \<and> (\<forall>x\<in>A. x \<sqsubseteq>\<^bsub>L\<^esub> g)"

text (in weak_partial_order) \<open>Could weaken these to \<^term>\<open>l \<in> carrier L \<and> l .\<in> A\<close> and \<^term>\<open>g \<in> carrier L \<and> g .\<in> A\<close>.\<close>

lemma least_dual [simp]:
  "least (inv_gorder L) x A = greatest L x A"
  by (simp add:least_def greatest_def)

lemma greatest_dual [simp]:
  "greatest (inv_gorder L) x A = least L x A"
  by (simp add:least_def greatest_def)

lemma least_closed [intro, simp]:
  "least L l A \<Longrightarrow> l \<in> carrier L"
  by (unfold least_def) fast

lemma least_mem:
  "least L l A \<Longrightarrow> l \<in> A"
  by (unfold least_def) fast

lemma (in weak_partial_order) weak_least_unique:
  "\<lbrakk>least L x A; least L y A\<rbrakk> \<Longrightarrow> x .= y"
  by (unfold least_def) blast

lemma least_le:
  fixes L (structure)
  shows "\<lbrakk>least L x A; a \<in> A\<rbrakk> \<Longrightarrow> x \<sqsubseteq> a"
  by (unfold least_def) fast

lemma (in weak_partial_order) least_cong:
  "\<lbrakk>x .= x'; x \<in> carrier L; x' \<in> carrier L; is_closed A\<rbrakk> \<Longrightarrow> least L x A = least L x' A"
  unfolding least_def
  by (meson is_closed_eq is_closed_eq_rev le_cong local.refl subset_iff)

abbreviation is_lub :: "[_, 'a, 'a set] => bool"
where "is_lub L x A \<equiv> least L x (Upper L A)"

text (in weak_partial_order) \<open>\<^const>\<open>least\<close> is not congruent in the second parameter for
  \<^term>\<open>A {.=} A'\<close>\<close>

lemma (in weak_partial_order) least_Upper_cong_l:
  assumes "x .= x'"
    and "x \<in> carrier L" "x' \<in> carrier L"
    and "A \<subseteq> carrier L"
  shows "least L x (Upper L A) = least L x' (Upper L A)"
  apply (rule least_cong) using assms by auto

lemma (in weak_partial_order) least_Upper_cong_r:
  assumes "A \<subseteq> carrier L" "A' \<subseteq> carrier L" "A {.=} A'"
  shows "least L x (Upper L A) = least L x (Upper L A')"
  using Upper_cong assms by auto

lemma least_UpperI:
  fixes L (structure)
  assumes above: "!! x. x \<in> A \<Longrightarrow> x \<sqsubseteq> s"
    and below: "!! y. y \<in> Upper L A \<Longrightarrow> s \<sqsubseteq> y"
    and L: "A \<subseteq> carrier L"  "s \<in> carrier L"
  shows "least L s (Upper L A)"
proof -
  have "Upper L A \<subseteq> carrier L" by simp
  moreover from above L have "s \<in> Upper L A" by (simp add: Upper_def)
  moreover from below have "\<forall>x \<in> Upper L A. s \<sqsubseteq> x" by fast
  ultimately show ?thesis by (simp add: least_def)
qed

lemma least_Upper_above:
  fixes L (structure)
  shows "\<lbrakk>least L s (Upper L A); x \<in> A; A \<subseteq> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> s"
  by (unfold least_def) blast

lemma greatest_closed [intro, simp]:
  "greatest L l A \<Longrightarrow> l \<in> carrier L"
  by (unfold greatest_def) fast

lemma greatest_mem:
  "greatest L l A \<Longrightarrow> l \<in> A"
  by (unfold greatest_def) fast

lemma (in weak_partial_order) weak_greatest_unique:
  "\<lbrakk>greatest L x A; greatest L y A\<rbrakk> \<Longrightarrow> x .= y"
  by (unfold greatest_def) blast

lemma greatest_le:
  fixes L (structure)
  shows "\<lbrakk>greatest L x A; a \<in> A\<rbrakk> \<Longrightarrow> a \<sqsubseteq> x"
  by (unfold greatest_def) fast

lemma (in weak_partial_order) greatest_cong:
  "\<lbrakk>x .= x'; x \<in> carrier L; x' \<in> carrier L; is_closed A\<rbrakk> \<Longrightarrow>
  greatest L x A = greatest L x' A"
  unfolding greatest_def
  by (meson is_closed_eq_rev le_cong_r local.sym subset_eq)

abbreviation is_glb :: "[_, 'a, 'a set] => bool"
where "is_glb L x A \<equiv> greatest L x (Lower L A)"

text (in weak_partial_order) \<open>\<^const>\<open>greatest\<close> is not congruent in the second parameter for
  \<^term>\<open>A {.=} A'\<close> \<close>

lemma (in weak_partial_order) greatest_Lower_cong_l:
  assumes "x .= x'"
    and "x \<in> carrier L" "x' \<in> carrier L"
  shows "greatest L x (Lower L A) = greatest L x' (Lower L A)"
proof -
  have "\<forall>A. is_closed (Lower L (A \<inter> carrier L))"
    by simp
  then show ?thesis
    by (simp add: Lower_def assms greatest_cong)
qed

lemma (in weak_partial_order) greatest_Lower_cong_r:
  assumes "A \<subseteq> carrier L" "A' \<subseteq> carrier L" "A {.=} A'"
  shows "greatest L x (Lower L A) = greatest L x (Lower L A')"
  using Lower_cong assms by auto

lemma greatest_LowerI:
  fixes L (structure)
  assumes below: "!! x. x \<in> A \<Longrightarrow> i \<sqsubseteq> x"
    and above: "!! y. y \<in> Lower L A \<Longrightarrow> y \<sqsubseteq> i"
    and L: "A \<subseteq> carrier L"  "i \<in> carrier L"
  shows "greatest L i (Lower L A)"
proof -
  have "Lower L A \<subseteq> carrier L" by simp
  moreover from below L have "i \<in> Lower L A" by (simp add: Lower_def)
  moreover from above have "\<forall>x \<in> Lower L A. x \<sqsubseteq> i" by fast
  ultimately show ?thesis by (simp add: greatest_def)
qed

lemma greatest_Lower_below:
  fixes L (structure)
  shows "\<lbrakk>greatest L i (Lower L A); x \<in> A; A \<subseteq> carrier L\<rbrakk> \<Longrightarrow> i \<sqsubseteq> x"
  by (unfold greatest_def) blast


subsubsection \<open>Intervals\<close>

definition
  at_least_at_most :: "('a, 'c) gorder_scheme \<Rightarrow> 'a => 'a => 'a set"
    (\<open>(\<open>indent=1 notation=\<open>mixfix interval\<close>\<close>\<lbrace>_.._\<rbrace>\<index>)\<close>)
  where "\<lbrace>l..u\<rbrace>\<^bsub>A\<^esub> = {x \<in> carrier A. l \<sqsubseteq>\<^bsub>A\<^esub> x \<and> x \<sqsubseteq>\<^bsub>A\<^esub> u}"

context weak_partial_order
begin
  
  lemma at_least_at_most_upper [dest]:
    "x \<in> \<lbrace>a..b\<rbrace> \<Longrightarrow> x \<sqsubseteq> b"
    by (simp add: at_least_at_most_def)

  lemma at_least_at_most_lower [dest]:
    "x \<in> \<lbrace>a..b\<rbrace> \<Longrightarrow> a \<sqsubseteq> x"
    by (simp add: at_least_at_most_def)

  lemma at_least_at_most_closed: "\<lbrace>a..b\<rbrace> \<subseteq> carrier L"
    by (auto simp add: at_least_at_most_def)

  lemma at_least_at_most_member [intro]: 
    "\<lbrakk>x \<in> carrier L; a \<sqsubseteq> x; x \<sqsubseteq> b\<rbrakk> \<Longrightarrow> x \<in> \<lbrace>a..b\<rbrace>"
    by (simp add: at_least_at_most_def)

end


subsubsection \<open>Isotone functions\<close>

definition isotone :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
  "isotone A B f \<equiv>
   weak_partial_order A \<and> weak_partial_order B \<and>
   (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. x \<sqsubseteq>\<^bsub>A\<^esub> y \<longrightarrow> f x \<sqsubseteq>\<^bsub>B\<^esub> f y)"

lemma isotoneI [intro?]:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "weak_partial_order L1"
          "weak_partial_order L2"
          "(\<And>x y. \<lbrakk>x \<in> carrier L1; y \<in> carrier L1; x \<sqsubseteq>\<^bsub>L1\<^esub> y\<rbrakk> 
                   \<Longrightarrow> f x \<sqsubseteq>\<^bsub>L2\<^esub> f y)"
  shows "isotone L1 L2 f"
  using assms by (auto simp add:isotone_def)

abbreviation Monotone :: "('a, 'b) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
    (\<open>(\<open>open_block notation=\<open>prefix Mono\<close>\<close>Mono\<index>)\<close>)
  where "Mono\<^bsub>L\<^esub> f \<equiv> isotone L L f"

lemma use_iso1:
  "\<lbrakk>isotone A A f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow>
   f x \<sqsubseteq>\<^bsub>A\<^esub> f y"
  by (simp add: isotone_def)

lemma use_iso2:
  "\<lbrakk>isotone A B f; x \<in> carrier A; y \<in> carrier A; x \<sqsubseteq>\<^bsub>A\<^esub> y\<rbrakk> \<Longrightarrow>
   f x \<sqsubseteq>\<^bsub>B\<^esub> f y"
  by (simp add: isotone_def)

lemma iso_compose:
  "\<lbrakk>f \<in> carrier A \<rightarrow> carrier B; isotone A B f; g \<in> carrier B \<rightarrow> carrier C; isotone B C g\<rbrakk> \<Longrightarrow>
   isotone A C (g \<circ> f)"
  by (simp add: isotone_def, safe, metis Pi_iff)

lemma (in weak_partial_order) inv_isotone [simp]: 
  "isotone (inv_gorder A) (inv_gorder B) f = isotone A B f"
  by (auto simp add:isotone_def dual_weak_order dual_weak_order_iff)


subsubsection \<open>Idempotent functions\<close>

definition idempotent :: 
  "('a, 'b) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
    (\<open>(\<open>open_block notation=\<open>prefix Idem\<close>\<close>Idem\<index>)\<close>)
  where "Idem\<^bsub>L\<^esub> f \<equiv> \<forall>x\<in>carrier L. f (f x) .=\<^bsub>L\<^esub> f x"

lemma (in weak_partial_order) idempotent:
  "\<lbrakk>Idem f; x \<in> carrier L\<rbrakk> \<Longrightarrow> f (f x) .= f x"
  by (auto simp add: idempotent_def)


subsubsection \<open>Order embeddings\<close>

definition order_emb :: "('a, 'c) gorder_scheme \<Rightarrow> ('b, 'd) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where
  "order_emb A B f \<equiv> weak_partial_order A 
                   \<and> weak_partial_order B 
                   \<and> (\<forall>x\<in>carrier A. \<forall>y\<in>carrier A. f x \<sqsubseteq>\<^bsub>B\<^esub> f y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>A\<^esub> y )"

lemma order_emb_isotone: "order_emb A B f \<Longrightarrow> isotone A B f"
  by (auto simp add: isotone_def order_emb_def)


subsubsection \<open>Commuting functions\<close>
    
definition commuting :: "('a, 'c) gorder_scheme \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
"commuting A f g = (\<forall>x\<in>carrier A. (f \<circ> g) x .=\<^bsub>A\<^esub> (g \<circ> f) x)"

subsection \<open>Partial orders where \<open>eq\<close> is the Equality\<close>

locale partial_order = weak_partial_order +
  assumes eq_is_equal: "(.=) = (=)"
begin

declare weak_le_antisym [rule del]

lemma le_antisym [intro]:
  "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x; x \<in> carrier L; y \<in> carrier L\<rbrakk> \<Longrightarrow> x = y"
  using weak_le_antisym unfolding eq_is_equal .

lemma lless_eq:
  "x \<sqsubset> y \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<noteq> y"
  unfolding lless_def by (simp add: eq_is_equal)

lemma set_eq_is_eq: "A {.=} B \<longleftrightarrow> A = B"
  by (auto simp add: set_eq_def elem_def eq_is_equal)

end

lemma (in partial_order) dual_order:
  "partial_order (inv_gorder L)"
proof -
  interpret dwo: weak_partial_order "inv_gorder L"
    by (metis dual_weak_order)
  show ?thesis
    by (unfold_locales, simp add:eq_is_equal)
qed

lemma dual_order_iff:
  "partial_order (inv_gorder A) \<longleftrightarrow> partial_order A"
proof
  assume assm:"partial_order (inv_gorder A)"
  then interpret po: partial_order "inv_gorder A"
  rewrites "carrier (inv_gorder A) = carrier A"
  and   "le (inv_gorder A)      = (\<lambda> x y. le A y x)"
  and   "eq (inv_gorder A)      = eq A"
    by (simp_all)
  show "partial_order A"
    apply (unfold_locales, simp_all add: po.sym)
    apply (metis po.trans)
    apply (metis po.weak_le_antisym, metis po.le_trans)
    apply (metis (full_types) po.eq_is_equal, metis po.eq_is_equal)
  done
next
  assume "partial_order A"
  thus "partial_order (inv_gorder A)"
    by (metis partial_order.dual_order)
qed

text \<open>Least and greatest, as predicate\<close>

lemma (in partial_order) least_unique:
  "\<lbrakk>least L x A; least L y A\<rbrakk> \<Longrightarrow> x = y"
  using weak_least_unique unfolding eq_is_equal .

lemma (in partial_order) greatest_unique:
  "\<lbrakk>greatest L x A; greatest L y A\<rbrakk> \<Longrightarrow> x = y"
  using weak_greatest_unique unfolding eq_is_equal .


subsection \<open>Bounded Orders\<close>

definition
  top :: "_ => 'a" (\<open>\<top>\<index>\<close>) where
  "\<top>\<^bsub>L\<^esub> = (SOME x. greatest L x (carrier L))"

definition
  bottom :: "_ => 'a" (\<open>\<bottom>\<index>\<close>) where
  "\<bottom>\<^bsub>L\<^esub> = (SOME x. least L x (carrier L))"

locale weak_partial_order_bottom = weak_partial_order L for L (structure) +
  assumes bottom_exists: "\<exists> x. least L x (carrier L)"
begin

lemma bottom_least: "least L \<bottom> (carrier L)"
proof -
  obtain x where "least L x (carrier L)"
    by (metis bottom_exists)

  thus ?thesis
    by (auto intro:someI2 simp add: bottom_def)
qed

lemma bottom_closed [simp, intro]:
  "\<bottom> \<in> carrier L"
  by (metis bottom_least least_mem)

lemma bottom_lower [simp, intro]:
  "x \<in> carrier L \<Longrightarrow> \<bottom> \<sqsubseteq> x"
  by (metis bottom_least least_le)

end

locale weak_partial_order_top = weak_partial_order L for L (structure) +
  assumes top_exists: "\<exists> x. greatest L x (carrier L)"
begin

lemma top_greatest: "greatest L \<top> (carrier L)"
proof -
  obtain x where "greatest L x (carrier L)"
    by (metis top_exists)

  thus ?thesis
    by (auto intro:someI2 simp add: top_def)
qed

lemma top_closed [simp, intro]:
  "\<top> \<in> carrier L"
  by (metis greatest_mem top_greatest)

lemma top_higher [simp, intro]:
  "x \<in> carrier L \<Longrightarrow> x \<sqsubseteq> \<top>"
  by (metis greatest_le top_greatest)

end


subsection \<open>Total Orders\<close>

locale weak_total_order = weak_partial_order +
  assumes total: "\<lbrakk>x \<in> carrier L; y \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

text \<open>Introduction rule: the usual definition of total order\<close>

lemma (in weak_partial_order) weak_total_orderI:
  assumes total: "!!x y. \<lbrakk>x \<in> carrier L; y \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
  shows "weak_total_order L"
  by unfold_locales (rule total)


subsection \<open>Total orders where \<open>eq\<close> is the Equality\<close>

locale total_order = partial_order +
  assumes total_order_total: "\<lbrakk>x \<in> carrier L; y \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

sublocale total_order < weak?: weak_total_order
  by unfold_locales (rule total_order_total)

text \<open>Introduction rule: the usual definition of total order\<close>

lemma (in partial_order) total_orderI:
  assumes total: "!!x y. \<lbrakk>x \<in> carrier L; y \<in> carrier L\<rbrakk> \<Longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
  shows "total_order L"
  by unfold_locales (rule total)

end
