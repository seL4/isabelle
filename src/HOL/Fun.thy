(*  Title:      HOL/Fun.thy
    Author:     Tobias Nipkow, Cambridge University Computer Laboratory
    Author:     Andrei Popescu, TU Muenchen
    Copyright   1994, 2012
*)

section \<open>Notions about functions\<close>

theory Fun
  imports Set
  keywords "functor" :: thy_goal
begin

lemma apply_inverse: "f x = u \<Longrightarrow> (\<And>x. P x \<Longrightarrow> g (f x) = x) \<Longrightarrow> P x \<Longrightarrow> x = g u"
  by auto

text \<open>Uniqueness, so NOT the axiom of choice.\<close>
lemma uniq_choice: "\<forall>x. \<exists>!y. Q x y \<Longrightarrow> \<exists>f. \<forall>x. Q x (f x)"
  by (force intro: theI')

lemma b_uniq_choice: "\<forall>x\<in>S. \<exists>!y. Q x y \<Longrightarrow> \<exists>f. \<forall>x\<in>S. Q x (f x)"
  by (force intro: theI')


subsection \<open>The Identity Function \<open>id\<close>\<close>

definition id :: "'a \<Rightarrow> 'a"
  where "id = (\<lambda>x. x)"

lemma id_apply [simp]: "id x = x"
  by (simp add: id_def)

lemma image_id [simp]: "image id = id"
  by (simp add: id_def fun_eq_iff)

lemma vimage_id [simp]: "vimage id = id"
  by (simp add: id_def fun_eq_iff)

lemma eq_id_iff: "(\<forall>x. f x = x) \<longleftrightarrow> f = id"
  by auto

code_printing
  constant id \<rightharpoonup> (Haskell) "id"


subsection \<open>The Composition Operator \<open>f \<circ> g\<close>\<close>

definition comp :: "('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c"  (infixl "\<circ>" 55)
  where "f \<circ> g = (\<lambda>x. f (g x))"

notation (ASCII)
  comp  (infixl "o" 55)

lemma comp_apply [simp]: "(f \<circ> g) x = f (g x)"
  by (simp add: comp_def)

lemma comp_assoc: "(f \<circ> g) \<circ> h = f \<circ> (g \<circ> h)"
  by (simp add: fun_eq_iff)

lemma id_comp [simp]: "id \<circ> g = g"
  by (simp add: fun_eq_iff)

lemma comp_id [simp]: "f \<circ> id = f"
  by (simp add: fun_eq_iff)

lemma comp_eq_dest: "a \<circ> b = c \<circ> d \<Longrightarrow> a (b v) = c (d v)"
  by (simp add: fun_eq_iff)

lemma comp_eq_elim: "a \<circ> b = c \<circ> d \<Longrightarrow> ((\<And>v. a (b v) = c (d v)) \<Longrightarrow> R) \<Longrightarrow> R"
  by (simp add: fun_eq_iff)

lemma comp_eq_dest_lhs: "a \<circ> b = c \<Longrightarrow> a (b v) = c v"
  by clarsimp

lemma comp_eq_id_dest: "a \<circ> b = id \<circ> c \<Longrightarrow> a (b v) = c v"
  by clarsimp

lemma image_comp: "f ` (g ` r) = (f \<circ> g) ` r"
  by auto

lemma vimage_comp: "f -` (g -` x) = (g \<circ> f) -` x"
  by auto

lemma image_eq_imp_comp: "f ` A = g ` B \<Longrightarrow> (h \<circ> f) ` A = (h \<circ> g) ` B"
  by (auto simp: comp_def elim!: equalityE)

lemma image_bind: "f ` (Set.bind A g) = Set.bind A ((`) f \<circ> g)"
  by (auto simp add: Set.bind_def)

lemma bind_image: "Set.bind (f ` A) g = Set.bind A (g \<circ> f)"
  by (auto simp add: Set.bind_def)

lemma (in group_add) minus_comp_minus [simp]: "uminus \<circ> uminus = id"
  by (simp add: fun_eq_iff)

lemma (in boolean_algebra) minus_comp_minus [simp]: "uminus \<circ> uminus = id"
  by (simp add: fun_eq_iff)

code_printing
  constant comp \<rightharpoonup> (SML) infixl 5 "o" and (Haskell) infixr 9 "."


subsection \<open>The Forward Composition Operator \<open>fcomp\<close>\<close>

definition fcomp :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'a \<Rightarrow> 'c"  (infixl "\<circ>>" 60)
  where "f \<circ>> g = (\<lambda>x. g (f x))"

lemma fcomp_apply [simp]:  "(f \<circ>> g) x = g (f x)"
  by (simp add: fcomp_def)

lemma fcomp_assoc: "(f \<circ>> g) \<circ>> h = f \<circ>> (g \<circ>> h)"
  by (simp add: fcomp_def)

lemma id_fcomp [simp]: "id \<circ>> g = g"
  by (simp add: fcomp_def)

lemma fcomp_id [simp]: "f \<circ>> id = f"
  by (simp add: fcomp_def)

lemma fcomp_comp: "fcomp f g = comp g f"
  by (simp add: ext)

code_printing
  constant fcomp \<rightharpoonup> (Eval) infixl 1 "#>"

no_notation fcomp (infixl "\<circ>>" 60)


subsection \<open>Mapping functions\<close>

definition map_fun :: "('c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'd) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'd"
  where "map_fun f g h = g \<circ> h \<circ> f"

lemma map_fun_apply [simp]: "map_fun f g h x = g (h (f x))"
  by (simp add: map_fun_def)


subsection \<open>Injectivity and Bijectivity\<close>

definition inj_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> bool"  \<comment> \<open>injective\<close>
  where "inj_on f A \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y\<in>A. f x = f y \<longrightarrow> x = y)"

definition bij_betw :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool"  \<comment> \<open>bijective\<close>
  where "bij_betw f A B \<longleftrightarrow> inj_on f A \<and> f ` A = B"

text \<open>
  A common special case: functions injective, surjective or bijective over
  the entire domain type.
\<close>

abbreviation inj :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "inj f \<equiv> inj_on f UNIV"

abbreviation surj :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "surj f \<equiv> range f = UNIV"

translations \<comment> \<open>The negated case:\<close>
  "\<not> CONST surj f" \<leftharpoondown> "CONST range f \<noteq> CONST UNIV"

abbreviation bij :: "('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "bij f \<equiv> bij_betw f UNIV UNIV"

lemma inj_def: "inj f \<longleftrightarrow> (\<forall>x y. f x = f y \<longrightarrow> x = y)"
  unfolding inj_on_def by blast

lemma injI: "(\<And>x y. f x = f y \<Longrightarrow> x = y) \<Longrightarrow> inj f"
  unfolding inj_def by blast

theorem range_ex1_eq: "inj f \<Longrightarrow> b \<in> range f \<longleftrightarrow> (\<exists>!x. b = f x)"
  unfolding inj_def by blast

lemma injD: "inj f \<Longrightarrow> f x = f y \<Longrightarrow> x = y"
  by (simp add: inj_def)

lemma inj_on_eq_iff: "inj_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x = f y \<longleftrightarrow> x = y"
  by (auto simp: inj_on_def)

lemma inj_on_cong: "(\<And>a. a \<in> A \<Longrightarrow> f a = g a) \<Longrightarrow> inj_on f A \<longleftrightarrow> inj_on g A"
  by (auto simp: inj_on_def)

lemma inj_on_strict_subset: "inj_on f B \<Longrightarrow> A \<subset> B \<Longrightarrow> f ` A \<subset> f ` B"
  unfolding inj_on_def by blast

lemma inj_compose: "inj f \<Longrightarrow> inj g \<Longrightarrow> inj (f \<circ> g)"
  by (simp add: inj_def)

lemma inj_fun: "inj f \<Longrightarrow> inj (\<lambda>x y. f x)"
  by (simp add: inj_def fun_eq_iff)

lemma inj_eq: "inj f \<Longrightarrow> f x = f y \<longleftrightarrow> x = y"
  by (simp add: inj_on_eq_iff)

lemma inj_on_id[simp]: "inj_on id A"
  by (simp add: inj_on_def)

lemma inj_on_id2[simp]: "inj_on (\<lambda>x. x) A"
  by (simp add: inj_on_def)

lemma inj_on_Int: "inj_on f A \<or> inj_on f B \<Longrightarrow> inj_on f (A \<inter> B)"
  unfolding inj_on_def by blast

lemma surj_id: "surj id"
  by simp

lemma bij_id[simp]: "bij id"
  by (simp add: bij_betw_def)

lemma bij_uminus: "bij (uminus :: 'a \<Rightarrow> 'a::ab_group_add)"
  unfolding bij_betw_def inj_on_def
  by (force intro: minus_minus [symmetric])

lemma inj_onI [intro?]: "(\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x = f y \<Longrightarrow> x = y) \<Longrightarrow> inj_on f A"
  by (simp add: inj_on_def)

lemma inj_on_inverseI: "(\<And>x. x \<in> A \<Longrightarrow> g (f x) = x) \<Longrightarrow> inj_on f A"
  by (auto dest: arg_cong [of concl: g] simp add: inj_on_def)

lemma inj_onD: "inj_on f A \<Longrightarrow> f x = f y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> x = y"
  unfolding inj_on_def by blast

lemma inj_on_subset:
  assumes "inj_on f A"
    and "B \<subseteq> A"
  shows "inj_on f B"
proof (rule inj_onI)
  fix a b
  assume "a \<in> B" and "b \<in> B"
  with assms have "a \<in> A" and "b \<in> A"
    by auto
  moreover assume "f a = f b"
  ultimately show "a = b"
    using assms by (auto dest: inj_onD)
qed

lemma comp_inj_on: "inj_on f A \<Longrightarrow> inj_on g (f ` A) \<Longrightarrow> inj_on (g \<circ> f) A"
  by (simp add: comp_def inj_on_def)

lemma inj_on_imageI: "inj_on (g \<circ> f) A \<Longrightarrow> inj_on g (f ` A)"
  by (auto simp add: inj_on_def)

lemma inj_on_image_iff:
  "\<forall>x\<in>A. \<forall>y\<in>A. g (f x) = g (f y) \<longleftrightarrow> g x = g y \<Longrightarrow> inj_on f A \<Longrightarrow> inj_on g (f ` A) \<longleftrightarrow> inj_on g A"
  unfolding inj_on_def by blast

lemma inj_on_contraD: "inj_on f A \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> f x \<noteq> f y"
  unfolding inj_on_def by blast

lemma inj_singleton [simp]: "inj_on (\<lambda>x. {x}) A"
  by (simp add: inj_on_def)

lemma inj_on_empty[iff]: "inj_on f {}"
  by (simp add: inj_on_def)

lemma subset_inj_on: "inj_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> inj_on f A"
  unfolding inj_on_def by blast

lemma inj_on_Un: "inj_on f (A \<union> B) \<longleftrightarrow> inj_on f A \<and> inj_on f B \<and> f ` (A - B) \<inter> f ` (B - A) = {}"
  unfolding inj_on_def by (blast intro: sym)

lemma inj_on_insert [iff]: "inj_on f (insert a A) \<longleftrightarrow> inj_on f A \<and> f a \<notin> f ` (A - {a})"
  unfolding inj_on_def by (blast intro: sym)

lemma inj_on_diff: "inj_on f A \<Longrightarrow> inj_on f (A - B)"
  unfolding inj_on_def by blast

lemma comp_inj_on_iff: "inj_on f A \<Longrightarrow> inj_on f' (f ` A) \<longleftrightarrow> inj_on (f' \<circ> f) A"
  by (auto simp: comp_inj_on inj_on_def)

lemma inj_on_imageI2: "inj_on (f' \<circ> f) A \<Longrightarrow> inj_on f A"
  by (auto simp: comp_inj_on inj_on_def)

lemma inj_img_insertE:
  assumes "inj_on f A"
  assumes "x \<notin> B"
    and "insert x B = f ` A"
  obtains x' A' where "x' \<notin> A'" and "A = insert x' A'" and "x = f x'" and "B = f ` A'"
proof -
  from assms have "x \<in> f ` A" by auto
  then obtain x' where *: "x' \<in> A" "x = f x'" by auto
  then have A: "A = insert x' (A - {x'})" by auto
  with assms * have B: "B = f ` (A - {x'})" by (auto dest: inj_on_contraD)
  have "x' \<notin> A - {x'}" by simp
  from this A \<open>x = f x'\<close> B show ?thesis ..
qed

lemma linorder_injI:
  assumes "\<And>x y::'a::linorder. x < y \<Longrightarrow> f x \<noteq> f y"
  shows "inj f"
  \<comment> \<open>Courtesy of Stephan Merz\<close>
proof (rule inj_onI)
  show "x = y" if "f x = f y" for x y
   by (rule linorder_cases) (auto dest: assms simp: that)
qed


lemma inj_on_image_Pow: "inj_on f A \<Longrightarrow>inj_on (image f) (Pow A)"
  unfolding Pow_def inj_on_def by blast

lemma bij_betw_image_Pow: "bij_betw f A B \<Longrightarrow> bij_betw (image f) (Pow A) (Pow B)"
  by (auto simp add: bij_betw_def inj_on_image_Pow image_Pow_surj)

lemma surj_def: "surj f \<longleftrightarrow> (\<forall>y. \<exists>x. y = f x)"
  by auto

lemma surjI:
  assumes "\<And>x. g (f x) = x"
  shows "surj g"
  using assms [symmetric] by auto

lemma surjD: "surj f \<Longrightarrow> \<exists>x. y = f x"
  by (simp add: surj_def)

lemma surjE: "surj f \<Longrightarrow> (\<And>x. y = f x \<Longrightarrow> C) \<Longrightarrow> C"
  by (simp add: surj_def) blast

lemma comp_surj: "surj f \<Longrightarrow> surj g \<Longrightarrow> surj (g \<circ> f)"
  by (simp add: image_comp [symmetric])

lemma bij_betw_imageI: "inj_on f A \<Longrightarrow> f ` A = B \<Longrightarrow> bij_betw f A B"
  unfolding bij_betw_def by clarify

lemma bij_betw_imp_surj_on: "bij_betw f A B \<Longrightarrow> f ` A = B"
  unfolding bij_betw_def by clarify

lemma bij_betw_imp_surj: "bij_betw f A UNIV \<Longrightarrow> surj f"
  unfolding bij_betw_def by auto

lemma bij_betw_empty1: "bij_betw f {} A \<Longrightarrow> A = {}"
  unfolding bij_betw_def by blast

lemma bij_betw_empty2: "bij_betw f A {} \<Longrightarrow> A = {}"
  unfolding bij_betw_def by blast

lemma inj_on_imp_bij_betw: "inj_on f A \<Longrightarrow> bij_betw f A (f ` A)"
  unfolding bij_betw_def by simp

lemma bij_def: "bij f \<longleftrightarrow> inj f \<and> surj f"
  by (rule bij_betw_def)

lemma bijI: "inj f \<Longrightarrow> surj f \<Longrightarrow> bij f"
  by (rule bij_betw_imageI)

lemma bij_is_inj: "bij f \<Longrightarrow> inj f"
  by (simp add: bij_def)

lemma bij_is_surj: "bij f \<Longrightarrow> surj f"
  by (simp add: bij_def)

lemma bij_betw_imp_inj_on: "bij_betw f A B \<Longrightarrow> inj_on f A"
  by (simp add: bij_betw_def)

lemma bij_betw_trans: "bij_betw f A B \<Longrightarrow> bij_betw g B C \<Longrightarrow> bij_betw (g \<circ> f) A C"
  by (auto simp add:bij_betw_def comp_inj_on)

lemma bij_comp: "bij f \<Longrightarrow> bij g \<Longrightarrow> bij (g \<circ> f)"
  by (rule bij_betw_trans)

lemma bij_betw_comp_iff: "bij_betw f A A' \<Longrightarrow> bij_betw f' A' A'' \<longleftrightarrow> bij_betw (f' \<circ> f) A A''"
  by (auto simp add: bij_betw_def inj_on_def)

lemma bij_betw_comp_iff2:
  assumes bij: "bij_betw f' A' A''"
    and img: "f ` A \<le> A'"
  shows "bij_betw f A A' \<longleftrightarrow> bij_betw (f' \<circ> f) A A''"
  using assms
proof (auto simp add: bij_betw_comp_iff)
  assume *: "bij_betw (f' \<circ> f) A A''"
  then show "bij_betw f A A'"
    using img
  proof (auto simp add: bij_betw_def)
    assume "inj_on (f' \<circ> f) A"
    then show "inj_on f A"
      using inj_on_imageI2 by blast
  next
    fix a'
    assume **: "a' \<in> A'"
    with bij have "f' a' \<in> A''"
      unfolding bij_betw_def by auto
    with * obtain a where 1: "a \<in> A \<and> f' (f a) = f' a'"
      unfolding bij_betw_def by force
    with img have "f a \<in> A'" by auto
    with bij ** 1 have "f a = a'"
      unfolding bij_betw_def inj_on_def by auto
    with 1 show "a' \<in> f ` A" by auto
  qed
qed

lemma bij_betw_inv:
  assumes "bij_betw f A B"
  shows "\<exists>g. bij_betw g B A"
proof -
  have i: "inj_on f A" and s: "f ` A = B"
    using assms by (auto simp: bij_betw_def)
  let ?P = "\<lambda>b a. a \<in> A \<and> f a = b"
  let ?g = "\<lambda>b. The (?P b)"
  have g: "?g b = a" if P: "?P b a" for a b
  proof -
    from that s have ex1: "\<exists>a. ?P b a" by blast
    then have uex1: "\<exists>!a. ?P b a" by (blast dest:inj_onD[OF i])
    then show ?thesis
      using the1_equality[OF uex1, OF P] P by simp
  qed
  have "inj_on ?g B"
  proof (rule inj_onI)
    fix x y
    assume "x \<in> B" "y \<in> B" "?g x = ?g y"
    from s \<open>x \<in> B\<close> obtain a1 where a1: "?P x a1" by blast
    from s \<open>y \<in> B\<close> obtain a2 where a2: "?P y a2" by blast
    from g [OF a1] a1 g [OF a2] a2 \<open>?g x = ?g y\<close> show "x = y" by simp
  qed
  moreover have "?g ` B = A"
  proof (auto simp: image_def)
    fix b
    assume "b \<in> B"
    with s obtain a where P: "?P b a" by blast
    with g[OF P] show "?g b \<in> A" by auto
  next
    fix a
    assume "a \<in> A"
    with s obtain b where P: "?P b a" by blast
    with s have "b \<in> B" by blast
    with g[OF P] show "\<exists>b\<in>B. a = ?g b" by blast
  qed
  ultimately show ?thesis
    by (auto simp: bij_betw_def)
qed

lemma bij_betw_cong: "(\<And>a. a \<in> A \<Longrightarrow> f a = g a) \<Longrightarrow> bij_betw f A A' = bij_betw g A A'"
  unfolding bij_betw_def inj_on_def by safe force+  (* somewhat slow *)

lemma bij_betw_id[intro, simp]: "bij_betw id A A"
  unfolding bij_betw_def id_def by auto

lemma bij_betw_id_iff: "bij_betw id A B \<longleftrightarrow> A = B"
  by (auto simp add: bij_betw_def)

lemma bij_betw_combine:
  "bij_betw f A B \<Longrightarrow> bij_betw f C D \<Longrightarrow> B \<inter> D = {} \<Longrightarrow> bij_betw f (A \<union> C) (B \<union> D)"
  unfolding bij_betw_def inj_on_Un image_Un by auto

lemma bij_betw_subset: "bij_betw f A A' \<Longrightarrow> B \<subseteq> A \<Longrightarrow> f ` B = B' \<Longrightarrow> bij_betw f B B'"
  by (auto simp add: bij_betw_def inj_on_def)

lemma bij_pointE:
  assumes "bij f"
  obtains x where "y = f x" and "\<And>x'. y = f x' \<Longrightarrow> x' = x"
proof -
  from assms have "inj f" by (rule bij_is_inj)
  moreover from assms have "surj f" by (rule bij_is_surj)
  then have "y \<in> range f" by simp
  ultimately have "\<exists>!x. y = f x" by (simp add: range_ex1_eq)
  with that show thesis by blast
qed

lemma surj_image_vimage_eq: "surj f \<Longrightarrow> f ` (f -` A) = A"
  by simp

lemma surj_vimage_empty:
  assumes "surj f"
  shows "f -` A = {} \<longleftrightarrow> A = {}"
  using surj_image_vimage_eq [OF \<open>surj f\<close>, of A]
  by (intro iffI) fastforce+

lemma inj_vimage_image_eq: "inj f \<Longrightarrow> f -` (f ` A) = A"
  unfolding inj_def by blast

lemma vimage_subsetD: "surj f \<Longrightarrow> f -` B \<subseteq> A \<Longrightarrow> B \<subseteq> f ` A"
  by (blast intro: sym)

lemma vimage_subsetI: "inj f \<Longrightarrow> B \<subseteq> f ` A \<Longrightarrow> f -` B \<subseteq> A"
  unfolding inj_def by blast

lemma vimage_subset_eq: "bij f \<Longrightarrow> f -` B \<subseteq> A \<longleftrightarrow> B \<subseteq> f ` A"
  unfolding bij_def by (blast del: subsetI intro: vimage_subsetI vimage_subsetD)

lemma inj_on_image_eq_iff: "inj_on f C \<Longrightarrow> A \<subseteq> C \<Longrightarrow> B \<subseteq> C \<Longrightarrow> f ` A = f ` B \<longleftrightarrow> A = B"
  by (fastforce simp: inj_on_def)

lemma inj_on_Un_image_eq_iff: "inj_on f (A \<union> B) \<Longrightarrow> f ` A = f ` B \<longleftrightarrow> A = B"
  by (erule inj_on_image_eq_iff) simp_all

lemma inj_on_image_Int: "inj_on f C \<Longrightarrow> A \<subseteq> C \<Longrightarrow> B \<subseteq> C \<Longrightarrow> f ` (A \<inter> B) = f ` A \<inter> f ` B"
  unfolding inj_on_def by blast

lemma inj_on_image_set_diff: "inj_on f C \<Longrightarrow> A - B \<subseteq> C \<Longrightarrow> B \<subseteq> C \<Longrightarrow> f ` (A - B) = f ` A - f ` B"
  unfolding inj_on_def by blast

lemma image_Int: "inj f \<Longrightarrow> f ` (A \<inter> B) = f ` A \<inter> f ` B"
  unfolding inj_def by blast

lemma image_set_diff: "inj f \<Longrightarrow> f ` (A - B) = f ` A - f ` B"
  unfolding inj_def by blast

lemma inj_on_image_mem_iff: "inj_on f B \<Longrightarrow> a \<in> B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f a \<in> f ` A \<longleftrightarrow> a \<in> A"
  by (auto simp: inj_on_def)

(*FIXME DELETE*)
lemma inj_on_image_mem_iff_alt: "inj_on f B \<Longrightarrow> A \<subseteq> B \<Longrightarrow> f a \<in> f ` A \<Longrightarrow> a \<in> B \<Longrightarrow> a \<in> A"
  by (blast dest: inj_onD)

lemma inj_image_mem_iff: "inj f \<Longrightarrow> f a \<in> f ` A \<longleftrightarrow> a \<in> A"
  by (blast dest: injD)

lemma inj_image_subset_iff: "inj f \<Longrightarrow> f ` A \<subseteq> f ` B \<longleftrightarrow> A \<subseteq> B"
  by (blast dest: injD)

lemma inj_image_eq_iff: "inj f \<Longrightarrow> f ` A = f ` B \<longleftrightarrow> A = B"
  by (blast dest: injD)

lemma surj_Compl_image_subset: "surj f \<Longrightarrow> - (f ` A) \<subseteq> f ` (- A)"
  by auto

lemma inj_image_Compl_subset: "inj f \<Longrightarrow> f ` (- A) \<subseteq> - (f ` A)"
  by (auto simp: inj_def)

lemma bij_image_Compl_eq: "bij f \<Longrightarrow> f ` (- A) = - (f ` A)"
  by (simp add: bij_def inj_image_Compl_subset surj_Compl_image_subset equalityI)

lemma inj_vimage_singleton: "inj f \<Longrightarrow> f -` {a} \<subseteq> {THE x. f x = a}"
  \<comment> \<open>The inverse image of a singleton under an injective function is included in a singleton.\<close>
  by (simp add: inj_def) (blast intro: the_equality [symmetric])

lemma inj_on_vimage_singleton: "inj_on f A \<Longrightarrow> f -` {a} \<inter> A \<subseteq> {THE x. x \<in> A \<and> f x = a}"
  by (auto simp add: inj_on_def intro: the_equality [symmetric])

lemma (in ordered_ab_group_add) inj_uminus[simp, intro]: "inj_on uminus A"
  by (auto intro!: inj_onI)

lemma (in linorder) strict_mono_imp_inj_on: "strict_mono f \<Longrightarrow> inj_on f A"
  by (auto intro!: inj_onI dest: strict_mono_eq)

lemma bij_betw_byWitness:
  assumes left: "\<forall>a \<in> A. f' (f a) = a"
    and right: "\<forall>a' \<in> A'. f (f' a') = a'"
    and "f ` A \<subseteq> A'"
    and img2: "f' ` A' \<subseteq> A"
  shows "bij_betw f A A'"
  using assms
  unfolding bij_betw_def inj_on_def
proof safe
  fix a b
  assume "a \<in> A" "b \<in> A"
  with left have "a = f' (f a) \<and> b = f' (f b)" by simp
  moreover assume "f a = f b"
  ultimately show "a = b" by simp
next
  fix a' assume *: "a' \<in> A'"
  with img2 have "f' a' \<in> A" by blast
  moreover from * right have "a' = f (f' a')" by simp
  ultimately show "a' \<in> f ` A" by blast
qed

corollary notIn_Un_bij_betw:
  assumes "b \<notin> A"
    and "f b \<notin> A'"
    and "bij_betw f A A'"
  shows "bij_betw f (A \<union> {b}) (A' \<union> {f b})"
proof -
  have "bij_betw f {b} {f b}"
    unfolding bij_betw_def inj_on_def by simp
  with assms show ?thesis
    using bij_betw_combine[of f A A' "{b}" "{f b}"] by blast
qed

lemma notIn_Un_bij_betw3:
  assumes "b \<notin> A"
    and "f b \<notin> A'"
  shows "bij_betw f A A' = bij_betw f (A \<union> {b}) (A' \<union> {f b})"
proof
  assume "bij_betw f A A'"
  then show "bij_betw f (A \<union> {b}) (A' \<union> {f b})"
    using assms notIn_Un_bij_betw [of b A f A'] by blast
next
  assume *: "bij_betw f (A \<union> {b}) (A' \<union> {f b})"
  have "f ` A = A'"
  proof auto
    fix a
    assume **: "a \<in> A"
    then have "f a \<in> A' \<union> {f b}"
      using * unfolding bij_betw_def by blast
    moreover
    have False if "f a = f b"
    proof -
      have "a = b"
        using * ** that unfolding bij_betw_def inj_on_def by blast
      with \<open>b \<notin> A\<close> ** show ?thesis by blast
    qed
    ultimately show "f a \<in> A'" by blast
  next
    fix a'
    assume **: "a' \<in> A'"
    then have "a' \<in> f ` (A \<union> {b})"
      using * by (auto simp add: bij_betw_def)
    then obtain a where 1: "a \<in> A \<union> {b} \<and> f a = a'" by blast
    moreover
    have False if "a = b" using 1 ** \<open>f b \<notin> A'\<close> that by blast
    ultimately have "a \<in> A" by blast
    with 1 show "a' \<in> f ` A" by blast
  qed
  then show "bij_betw f A A'"
    using * bij_betw_subset[of f "A \<union> {b}" _ A] by blast
qed

text \<open>Important examples\<close>

context cancel_semigroup_add
begin

lemma inj_on_add [simp]:
  "inj_on ((+) a) A"
  by (rule inj_onI) simp

lemma inj_add_left:
  \<open>inj ((+) a)\<close>
  by simp

lemma inj_on_add' [simp]:
  "inj_on (\<lambda>b. b + a) A"
  by (rule inj_onI) simp

lemma bij_betw_add [simp]:
  "bij_betw ((+) a) A B \<longleftrightarrow> (+) a ` A = B"
  by (simp add: bij_betw_def)

end

context ab_group_add
begin

lemma surj_plus [simp]:
  "surj ((+) a)"
  by (auto intro: range_eqI [of b "(+) a" "b - a" for b] simp add: algebra_simps)

lemma inj_diff_right [simp]:
  \<open>inj (\<lambda>b. b - a)\<close>
proof -
  have \<open>inj ((+) (- a))\<close>
    by (fact inj_add_left)
  also have \<open>(+) (- a) = (\<lambda>b. b - a)\<close>
    by (simp add: fun_eq_iff)
  finally show ?thesis .
qed

lemma surj_diff_right [simp]:
  "surj (\<lambda>x. x - a)"
  using surj_plus [of "- a"] by (simp cong: image_cong_simp)

lemma translation_Compl:
  "(+) a ` (- t) = - ((+) a ` t)"
proof (rule set_eqI)
  fix b
  show "b \<in> (+) a ` (- t) \<longleftrightarrow> b \<in> - (+) a ` t"
    by (auto simp: image_iff algebra_simps intro!: bexI [of _ "b - a"])
qed

lemma translation_subtract_Compl:
  "(\<lambda>x. x - a) ` (- t) = - ((\<lambda>x. x - a) ` t)"
  using translation_Compl [of "- a" t] by (simp cong: image_cong_simp)

lemma translation_diff:
  "(+) a ` (s - t) = ((+) a ` s) - ((+) a ` t)"
  by auto

lemma translation_subtract_diff:
  "(\<lambda>x. x - a) ` (s - t) = ((\<lambda>x. x - a) ` s) - ((\<lambda>x. x - a) ` t)"
  using translation_diff [of "- a"] by (simp cong: image_cong_simp)

lemma translation_Int:
  "(+) a ` (s \<inter> t) = ((+) a ` s) \<inter> ((+) a ` t)"
  by auto

lemma translation_subtract_Int:
  "(\<lambda>x. x - a) ` (s \<inter> t) = ((\<lambda>x. x - a) ` s) \<inter> ((\<lambda>x. x - a) ` t)"
  using translation_Int [of " -a"] by (simp cong: image_cong_simp)

end


subsection \<open>Function Updating\<close>

definition fun_upd :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "fun_upd f a b = (\<lambda>x. if x = a then b else f x)"

nonterminal updbinds and updbind

syntax
  "_updbind" :: "'a \<Rightarrow> 'a \<Rightarrow> updbind"             ("(2_ :=/ _)")
  ""         :: "updbind \<Rightarrow> updbinds"             ("_")
  "_updbinds":: "updbind \<Rightarrow> updbinds \<Rightarrow> updbinds" ("_,/ _")
  "_Update"  :: "'a \<Rightarrow> updbinds \<Rightarrow> 'a"            ("_/'((_)')" [1000, 0] 900)

translations
  "_Update f (_updbinds b bs)" \<rightleftharpoons> "_Update (_Update f b) bs"
  "f(x:=y)" \<rightleftharpoons> "CONST fun_upd f x y"

(* Hint: to define the sum of two functions (or maps), use case_sum.
         A nice infix syntax could be defined by
notation
  case_sum  (infixr "'(+')"80)
*)

lemma fun_upd_idem_iff: "f(x:=y) = f \<longleftrightarrow> f x = y"
  unfolding fun_upd_def
  apply safe
   apply (erule subst)
   apply (rule_tac [2] ext)
   apply auto
  done

lemma fun_upd_idem: "f x = y \<Longrightarrow> f(x := y) = f"
  by (simp only: fun_upd_idem_iff)

lemma fun_upd_triv [iff]: "f(x := f x) = f"
  by (simp only: fun_upd_idem)

lemma fun_upd_apply [simp]: "(f(x := y)) z = (if z = x then y else f z)"
  by (simp add: fun_upd_def)

(* fun_upd_apply supersedes these two, but they are useful
   if fun_upd_apply is intentionally removed from the simpset *)
lemma fun_upd_same: "(f(x := y)) x = y"
  by simp

lemma fun_upd_other: "z \<noteq> x \<Longrightarrow> (f(x := y)) z = f z"
  by simp

lemma fun_upd_upd [simp]: "f(x := y, x := z) = f(x := z)"
  by (simp add: fun_eq_iff)

lemma fun_upd_twist: "a \<noteq> c \<Longrightarrow> (m(a := b))(c := d) = (m(c := d))(a := b)"
  by (rule ext) auto

lemma inj_on_fun_updI: "inj_on f A \<Longrightarrow> y \<notin> f ` A \<Longrightarrow> inj_on (f(x := y)) A"
  by (auto simp: inj_on_def)

lemma fun_upd_image: "f(x := y) ` A = (if x \<in> A then insert y (f ` (A - {x})) else f ` A)"
  by auto

lemma fun_upd_comp: "f \<circ> (g(x := y)) = (f \<circ> g)(x := f y)"
  by auto

lemma fun_upd_eqD: "f(x := y) = g(x := z) \<Longrightarrow> y = z"
  by (simp add: fun_eq_iff split: if_split_asm)


subsection \<open>\<open>override_on\<close>\<close>

definition override_on :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'b"
  where "override_on f g A = (\<lambda>a. if a \<in> A then g a else f a)"

lemma override_on_emptyset[simp]: "override_on f g {} = f"
  by (simp add: override_on_def)

lemma override_on_apply_notin[simp]: "a \<notin> A \<Longrightarrow> (override_on f g A) a = f a"
  by (simp add: override_on_def)

lemma override_on_apply_in[simp]: "a \<in> A \<Longrightarrow> (override_on f g A) a = g a"
  by (simp add: override_on_def)

lemma override_on_insert: "override_on f g (insert x X) = (override_on f g X)(x:=g x)"
  by (simp add: override_on_def fun_eq_iff)

lemma override_on_insert': "override_on f g (insert x X) = (override_on (f(x:=g x)) g X)"
  by (simp add: override_on_def fun_eq_iff)


subsection \<open>\<open>swap\<close>\<close>

definition swap :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where "swap a b f = f (a := f b, b:= f a)"

lemma swap_apply [simp]:
  "swap a b f a = f b"
  "swap a b f b = f a"
  "c \<noteq> a \<Longrightarrow> c \<noteq> b \<Longrightarrow> swap a b f c = f c"
  by (simp_all add: swap_def)

lemma swap_self [simp]: "swap a a f = f"
  by (simp add: swap_def)

lemma swap_commute: "swap a b f = swap b a f"
  by (simp add: fun_upd_def swap_def fun_eq_iff)

lemma swap_nilpotent [simp]: "swap a b (swap a b f) = f"
  by (rule ext) (simp add: fun_upd_def swap_def)

lemma swap_comp_involutory [simp]: "swap a b \<circ> swap a b = id"
  by (rule ext) simp

lemma swap_triple:
  assumes "a \<noteq> c" and "b \<noteq> c"
  shows "swap a b (swap b c (swap a b f)) = swap a c f"
  using assms by (simp add: fun_eq_iff swap_def)

lemma comp_swap: "f \<circ> swap a b g = swap a b (f \<circ> g)"
  by (rule ext) (simp add: fun_upd_def swap_def)

lemma swap_image_eq [simp]:
  assumes "a \<in> A" "b \<in> A"
  shows "swap a b f ` A = f ` A"
proof -
  have subset: "\<And>f. swap a b f ` A \<subseteq> f ` A"
    using assms by (auto simp: image_iff swap_def)
  then have "swap a b (swap a b f) ` A \<subseteq> (swap a b f) ` A" .
  with subset[of f] show ?thesis by auto
qed

lemma inj_on_imp_inj_on_swap: "inj_on f A \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> inj_on (swap a b f) A"
  by (auto simp add: inj_on_def swap_def)

lemma inj_on_swap_iff [simp]:
  assumes A: "a \<in> A" "b \<in> A"
  shows "inj_on (swap a b f) A \<longleftrightarrow> inj_on f A"
proof
  assume "inj_on (swap a b f) A"
  with A have "inj_on (swap a b (swap a b f)) A"
    by (iprover intro: inj_on_imp_inj_on_swap)
  then show "inj_on f A" by simp
next
  assume "inj_on f A"
  with A show "inj_on (swap a b f) A"
    by (iprover intro: inj_on_imp_inj_on_swap)
qed

lemma surj_imp_surj_swap: "surj f \<Longrightarrow> surj (swap a b f)"
  by simp

lemma surj_swap_iff [simp]: "surj (swap a b f) \<longleftrightarrow> surj f"
  by simp

lemma bij_betw_swap_iff [simp]: "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> bij_betw (swap x y f) A B \<longleftrightarrow> bij_betw f A B"
  by (auto simp: bij_betw_def)

lemma bij_swap_iff [simp]: "bij (swap a b f) \<longleftrightarrow> bij f"
  by simp

hide_const (open) swap


subsection \<open>Inversion of injective functions\<close>

definition the_inv_into :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)"
  where "the_inv_into A f = (\<lambda>x. THE y. y \<in> A \<and> f y = x)"

lemma the_inv_into_f_f: "inj_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> the_inv_into A f (f x) = x"
  unfolding the_inv_into_def inj_on_def by blast

lemma f_the_inv_into_f: "inj_on f A \<Longrightarrow> y \<in> f ` A  \<Longrightarrow> f (the_inv_into A f y) = y"
  apply (simp add: the_inv_into_def)
  apply (rule the1I2)
   apply (blast dest: inj_onD)
  apply blast
  done

lemma the_inv_into_into: "inj_on f A \<Longrightarrow> x \<in> f ` A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> the_inv_into A f x \<in> B"
  apply (simp add: the_inv_into_def)
  apply (rule the1I2)
   apply (blast dest: inj_onD)
  apply blast
  done

lemma the_inv_into_onto [simp]: "inj_on f A \<Longrightarrow> the_inv_into A f ` (f ` A) = A"
  by (fast intro: the_inv_into_into the_inv_into_f_f [symmetric])

lemma the_inv_into_f_eq: "inj_on f A \<Longrightarrow> f x = y \<Longrightarrow> x \<in> A \<Longrightarrow> the_inv_into A f y = x"
  apply (erule subst)
  apply (erule the_inv_into_f_f)
  apply assumption
  done

lemma the_inv_into_comp:
  "inj_on f (g ` A) \<Longrightarrow> inj_on g A \<Longrightarrow> x \<in> f ` g ` A \<Longrightarrow>
    the_inv_into A (f \<circ> g) x = (the_inv_into A g \<circ> the_inv_into (g ` A) f) x"
  apply (rule the_inv_into_f_eq)
    apply (fast intro: comp_inj_on)
   apply (simp add: f_the_inv_into_f the_inv_into_into)
  apply (simp add: the_inv_into_into)
  done

lemma inj_on_the_inv_into: "inj_on f A \<Longrightarrow> inj_on (the_inv_into A f) (f ` A)"
  by (auto intro: inj_onI simp: the_inv_into_f_f)

lemma bij_betw_the_inv_into: "bij_betw f A B \<Longrightarrow> bij_betw (the_inv_into A f) B A"
  by (auto simp add: bij_betw_def inj_on_the_inv_into the_inv_into_into)

abbreviation the_inv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)"
  where "the_inv f \<equiv> the_inv_into UNIV f"

lemma the_inv_f_f: "the_inv f (f x) = x" if "inj f"
  using that UNIV_I by (rule the_inv_into_f_f)


subsection \<open>Cantor's Paradox\<close>

theorem Cantors_paradox: "\<nexists>f. f ` A = Pow A"
proof
  assume "\<exists>f. f ` A = Pow A"
  then obtain f where f: "f ` A = Pow A" ..
  let ?X = "{a \<in> A. a \<notin> f a}"
  have "?X \<in> Pow A" by blast
  then have "?X \<in> f ` A" by (simp only: f)
  then obtain x where "x \<in> A" and "f x = ?X" by blast
  then show False by blast
qed


subsection \<open>Setup\<close>

subsubsection \<open>Proof tools\<close>

text \<open>Simplify terms of the form \<open>f(\<dots>,x:=y,\<dots>,x:=z,\<dots>)\<close> to \<open>f(\<dots>,x:=z,\<dots>)\<close>\<close>

simproc_setup fun_upd2 ("f(v := w, x := y)") = \<open>fn _ =>
  let
    fun gen_fun_upd NONE T _ _ = NONE
      | gen_fun_upd (SOME f) T x y = SOME (Const (\<^const_name>\<open>fun_upd\<close>, T) $ f $ x $ y)
    fun dest_fun_T1 (Type (_, T :: Ts)) = T
    fun find_double (t as Const (\<^const_name>\<open>fun_upd\<close>,T) $ f $ x $ y) =
      let
        fun find (Const (\<^const_name>\<open>fun_upd\<close>,T) $ g $ v $ w) =
              if v aconv x then SOME g else gen_fun_upd (find g) T v w
          | find t = NONE
      in (dest_fun_T1 T, gen_fun_upd (find f) T x y) end

    val ss = simpset_of \<^context>

    fun proc ctxt ct =
      let
        val t = Thm.term_of ct
      in
        (case find_double t of
          (T, NONE) => NONE
        | (T, SOME rhs) =>
            SOME (Goal.prove ctxt [] [] (Logic.mk_equals (t, rhs))
              (fn _ =>
                resolve_tac ctxt [eq_reflection] 1 THEN
                resolve_tac ctxt @{thms ext} 1 THEN
                simp_tac (put_simpset ss ctxt) 1)))
      end
  in proc end
\<close>


subsubsection \<open>Functorial structure of types\<close>

ML_file \<open>Tools/functor.ML\<close>

functor map_fun: map_fun
  by (simp_all add: fun_eq_iff)

functor vimage
  by (simp_all add: fun_eq_iff vimage_comp)


text \<open>Legacy theorem names\<close>

lemmas o_def = comp_def
lemmas o_apply = comp_apply
lemmas o_assoc = comp_assoc [symmetric]
lemmas id_o = id_comp
lemmas o_id = comp_id
lemmas o_eq_dest = comp_eq_dest
lemmas o_eq_elim = comp_eq_elim
lemmas o_eq_dest_lhs = comp_eq_dest_lhs
lemmas o_eq_id_dest = comp_eq_id_dest

end
