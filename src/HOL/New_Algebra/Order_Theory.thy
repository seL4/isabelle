section \<open>Partial orders, lattices and complete lattices\<close>

theory Order_Theory
  imports Set_Theory
begin

text \<open>This theory uses no arithmetic; suppress HOL's \<open>+\<close>/\<open>-\<close> notation (as \<open>Ring_Theory\<close> does) so that
  it composes without ambiguity when imported alongside the ring/group developments, which rebind
  those tokens to their locale operations.\<close>
no_notation plus (infixl \<open>+\<close> 65)
no_notation minus (infixl \<open>-\<close> 65)
unbundle no uminus_syntax

text \<open>Carrier-set order theory in the locale idiom of \<open>Group_Theory\<close>: a
  @{term Partial_Order} fixes a carrier \<open>L\<close> and an order relation \<open>\<sqsubseteq>\<close> (a binary predicate, with the
  reflexive / antisymmetric / transitive axioms restricted to \<open>L\<close>).  On top of this we build binary
  lattices (least upper and greatest lower bounds of pairs) and complete lattices (of arbitrary
  subsets).  Unlike HOL-Algebra's record-based \<open>weak_partial_order\<close> over an equivalence, we fix the
  relation directly, which keeps the statements close to the type-class order they specialise.\<close>

subsection \<open>Partial orders\<close>

locale Partial_Order =
  fixes L :: "'a set" and le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix \<open>\<sqsubseteq>\<close> 50)
  assumes reflexive [intro, simp]: "a \<in> L \<Longrightarrow> a \<sqsubseteq> a"
    and antisymmetric: "\<lbrakk> a \<in> L; b \<in> L; a \<sqsubseteq> b; b \<sqsubseteq> a \<rbrakk> \<Longrightarrow> a = b"
    and transitive [trans]: "\<lbrakk> a \<in> L; b \<in> L; c \<in> L; a \<sqsubseteq> b; b \<sqsubseteq> c \<rbrakk> \<Longrightarrow> a \<sqsubseteq> c"
begin

subsubsection \<open>Bounds\<close>

text \<open>\<open>x\<close> is an upper bound of \<open>A\<close> (a subset of the carrier) if it dominates every element of \<open>A\<close>.\<close>
definition upper_bound :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "upper_bound x A \<longleftrightarrow> x \<in> L \<and> (\<forall>a\<in>A. a \<sqsubseteq> x)"

definition lower_bound :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "lower_bound x A \<longleftrightarrow> x \<in> L \<and> (\<forall>a\<in>A. x \<sqsubseteq> a)"

lemma upper_boundI:
  "\<lbrakk> x \<in> L; \<And>a. a \<in> A \<Longrightarrow> a \<sqsubseteq> x \<rbrakk> \<Longrightarrow> upper_bound x A"
  unfolding upper_bound_def by blast

lemma upper_boundD: "\<lbrakk> upper_bound x A; a \<in> A \<rbrakk> \<Longrightarrow> a \<sqsubseteq> x"
  unfolding upper_bound_def by blast

lemma upper_bound_closed: "upper_bound x A \<Longrightarrow> x \<in> L"
  unfolding upper_bound_def by blast

lemma lower_boundI:
  "\<lbrakk> x \<in> L; \<And>a. a \<in> A \<Longrightarrow> x \<sqsubseteq> a \<rbrakk> \<Longrightarrow> lower_bound x A"
  unfolding lower_bound_def by blast

lemma lower_boundD: "\<lbrakk> lower_bound x A; a \<in> A \<rbrakk> \<Longrightarrow> x \<sqsubseteq> a"
  unfolding lower_bound_def by blast

lemma lower_bound_closed: "lower_bound x A \<Longrightarrow> x \<in> L"
  unfolding lower_bound_def by blast

subsubsection \<open>Suprema and infima\<close>

text \<open>\<open>s\<close> is a least upper bound (supremum) of \<open>A\<close>: an upper bound below every upper bound.\<close>
definition is_sup :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "is_sup s A \<longleftrightarrow> upper_bound s A \<and> (\<forall>x. upper_bound x A \<longrightarrow> s \<sqsubseteq> x)"

definition is_inf :: "'a \<Rightarrow> 'a set \<Rightarrow> bool"
  where "is_inf i A \<longleftrightarrow> lower_bound i A \<and> (\<forall>x. lower_bound x A \<longrightarrow> x \<sqsubseteq> i)"

lemma is_supI:
  "\<lbrakk> upper_bound s A; \<And>x. upper_bound x A \<Longrightarrow> s \<sqsubseteq> x \<rbrakk> \<Longrightarrow> is_sup s A"
  unfolding is_sup_def by blast

lemma is_sup_upper: "is_sup s A \<Longrightarrow> upper_bound s A"
  unfolding is_sup_def by blast

lemma is_sup_least: "\<lbrakk> is_sup s A; upper_bound x A \<rbrakk> \<Longrightarrow> s \<sqsubseteq> x"
  unfolding is_sup_def by blast

lemma is_infI:
  "\<lbrakk> lower_bound i A; \<And>x. lower_bound x A \<Longrightarrow> x \<sqsubseteq> i \<rbrakk> \<Longrightarrow> is_inf i A"
  unfolding is_inf_def by blast

lemma is_inf_lower: "is_inf i A \<Longrightarrow> lower_bound i A"
  unfolding is_inf_def by blast

lemma is_inf_greatest: "\<lbrakk> is_inf i A; lower_bound x A \<rbrakk> \<Longrightarrow> x \<sqsubseteq> i"
  unfolding is_inf_def by blast

text \<open>Suprema and infima are unique when they exist (antisymmetry).\<close>
lemma is_sup_unique:
  assumes "is_sup s A" and "is_sup s' A"
  shows "s = s'"
proof (rule antisymmetric)
  show "s \<in> L" using assms(1) is_sup_upper upper_bound_closed by blast
  show "s' \<in> L" using assms(2) is_sup_upper upper_bound_closed by blast
  show "s \<sqsubseteq> s'" using assms by (blast dest: is_sup_least is_sup_upper)
  show "s' \<sqsubseteq> s" using assms by (blast dest: is_sup_least is_sup_upper)
qed

lemma is_inf_unique:
  assumes "is_inf i A" and "is_inf i' A"
  shows "i = i'"
proof (rule antisymmetric)
  show "i \<in> L" using assms(1) is_inf_lower lower_bound_closed by blast
  show "i' \<in> L" using assms(2) is_inf_lower lower_bound_closed by blast
  show "i \<sqsubseteq> i'" using assms by (blast dest: is_inf_greatest is_inf_lower)
  show "i' \<sqsubseteq> i" using assms by (blast dest: is_inf_greatest is_inf_lower)
qed

end


subsection \<open>Lattices\<close>

text \<open>A lattice is a partial order in which every pair of elements has a supremum (join) and an
  infimum (meet).\<close>
locale Lattice = Partial_Order +
  assumes ex_sup: "\<lbrakk> a \<in> L; b \<in> L \<rbrakk> \<Longrightarrow> \<exists>s. is_sup s {a, b}"
    and ex_inf: "\<lbrakk> a \<in> L; b \<in> L \<rbrakk> \<Longrightarrow> \<exists>i. is_inf i {a, b}"
begin

definition join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl \<open>\<squnion>\<close> 65)
  where "a \<squnion> b = (THE s. is_sup s {a, b})"

definition meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl \<open>\<sqinter>\<close> 70)
  where "a \<sqinter> b = (THE i. is_inf i {a, b})"

lemma is_sup_join:
  assumes "a \<in> L" "b \<in> L" shows "is_sup (a \<squnion> b) {a, b}"
  unfolding join_def by (rule theI') (use ex_sup[OF assms] is_sup_unique in blast)

lemma is_inf_meet:
  assumes "a \<in> L" "b \<in> L" shows "is_inf (a \<sqinter> b) {a, b}"
  unfolding meet_def by (rule theI') (use ex_inf[OF assms] is_inf_unique in blast)

lemma join_closed [intro, simp]: "\<lbrakk> a \<in> L; b \<in> L \<rbrakk> \<Longrightarrow> a \<squnion> b \<in> L"
  using upper_bound_closed[OF is_sup_upper[OF is_sup_join]] .

lemma meet_closed [intro, simp]: "\<lbrakk> a \<in> L; b \<in> L \<rbrakk> \<Longrightarrow> a \<sqinter> b \<in> L"
  using lower_bound_closed[OF is_inf_lower[OF is_inf_meet]] .

text \<open>The join dominates its arguments and is least among common upper bounds.\<close>
lemma join_upper1: "\<lbrakk> a \<in> L; b \<in> L \<rbrakk> \<Longrightarrow> a \<sqsubseteq> a \<squnion> b"
  using is_sup_join is_sup_upper by (blast dest: upper_boundD)

lemma join_upper2: "\<lbrakk> a \<in> L; b \<in> L \<rbrakk> \<Longrightarrow> b \<sqsubseteq> a \<squnion> b"
  using is_sup_join is_sup_upper by (blast dest: upper_boundD)

lemma join_least: "\<lbrakk> a \<in> L; b \<in> L; a \<sqsubseteq> c; b \<sqsubseteq> c; c \<in> L \<rbrakk> \<Longrightarrow> a \<squnion> b \<sqsubseteq> c"
  using is_sup_join by (blast intro: is_sup_least upper_boundI)

lemma meet_lower1: "\<lbrakk> a \<in> L; b \<in> L \<rbrakk> \<Longrightarrow> a \<sqinter> b \<sqsubseteq> a"
  using is_inf_meet is_inf_lower by (blast dest: lower_boundD)

lemma meet_lower2: "\<lbrakk> a \<in> L; b \<in> L \<rbrakk> \<Longrightarrow> a \<sqinter> b \<sqsubseteq> b"
  using is_inf_meet is_inf_lower by (blast dest: lower_boundD)

lemma meet_greatest: "\<lbrakk> a \<in> L; b \<in> L; c \<sqsubseteq> a; c \<sqsubseteq> b; c \<in> L \<rbrakk> \<Longrightarrow> c \<sqsubseteq> a \<sqinter> b"
  using is_inf_meet by (blast intro: is_inf_greatest lower_boundI)

subsubsection \<open>Lattice laws\<close>

lemma join_commutative:
  assumes "a \<in> L" "b \<in> L" shows "a \<squnion> b = b \<squnion> a"
proof (rule is_sup_unique[OF is_sup_join[OF assms]])
  show "is_sup (b \<squnion> a) {a, b}" using is_sup_join[OF assms(2,1)] by (simp add: insert_commute)
qed

lemma meet_commutative:
  assumes "a \<in> L" "b \<in> L" shows "a \<sqinter> b = b \<sqinter> a"
proof (rule is_inf_unique[OF is_inf_meet[OF assms]])
  show "is_inf (b \<sqinter> a) {a, b}" using is_inf_meet[OF assms(2,1)] by (simp add: insert_commute)
qed

lemma join_idempotent [simp]: "a \<in> L \<Longrightarrow> a \<squnion> a = a"
  by (rule antisymmetric) (auto simp: join_upper1 join_least)

lemma meet_idempotent [simp]: "a \<in> L \<Longrightarrow> a \<sqinter> a = a"
  by (rule antisymmetric) (auto simp: meet_lower1 meet_greatest)

text \<open>Absorption laws.\<close>
lemma join_absorb: "\<lbrakk> a \<in> L; b \<in> L \<rbrakk> \<Longrightarrow> a \<squnion> (a \<sqinter> b) = a"
  by (rule antisymmetric) (auto simp: join_upper1 join_least meet_lower1)

lemma meet_absorb: "\<lbrakk> a \<in> L; b \<in> L \<rbrakk> \<Longrightarrow> a \<sqinter> (a \<squnion> b) = a"
  by (rule antisymmetric) (auto simp: meet_lower1 meet_greatest join_upper1)

text \<open>The order is recovered from the join (equivalently the meet).\<close>
lemma le_iff_join:
  assumes a: "a \<in> L" and b: "b \<in> L" shows "(a \<sqsubseteq> b) = (a \<squnion> b = b)"
proof
  assume ab: "a \<sqsubseteq> b"
  show "a \<squnion> b = b"
  proof (rule antisymmetric)
    show "a \<squnion> b \<in> L" using a b by simp
    show "b \<in> L" by (rule b)
    show "a \<squnion> b \<sqsubseteq> b" using join_least[OF a b ab] b by simp
    show "b \<sqsubseteq> a \<squnion> b" by (rule join_upper2[OF a b])
  qed
next
  assume "a \<squnion> b = b"
  then show "a \<sqsubseteq> b" using join_upper1[OF a b] by simp
qed

end


subsection \<open>Complete lattices\<close>

text \<open>A complete lattice: every subset of the carrier has a supremum and an infimum.\<close>
locale Complete_Lattice = Partial_Order +
  assumes ex_Sup: "A \<subseteq> L \<Longrightarrow> \<exists>s. is_sup s A"
    and ex_Inf: "A \<subseteq> L \<Longrightarrow> \<exists>i. is_inf i A"
begin

definition Sup :: "'a set \<Rightarrow> 'a" (\<open>\<Squnion>\<close>)
  where "\<Squnion> A = (THE s. is_sup s A)"

definition Inf :: "'a set \<Rightarrow> 'a" (\<open>\<Sqinter>\<close>)
  where "\<Sqinter> A = (THE i. is_inf i A)"

lemma is_sup_Sup: "A \<subseteq> L \<Longrightarrow> is_sup (\<Squnion> A) A"
  unfolding Sup_def by (rule theI') (use ex_Sup is_sup_unique in blast)

lemma is_inf_Inf: "A \<subseteq> L \<Longrightarrow> is_inf (\<Sqinter> A) A"
  unfolding Inf_def by (rule theI') (use ex_Inf is_inf_unique in blast)

lemma Sup_closed [intro, simp]: "A \<subseteq> L \<Longrightarrow> \<Squnion> A \<in> L"
  using is_sup_Sup is_sup_upper upper_bound_closed by blast

lemma Inf_closed [intro, simp]: "A \<subseteq> L \<Longrightarrow> \<Sqinter> A \<in> L"
  using is_inf_Inf is_inf_lower lower_bound_closed by blast

lemma Sup_upper: "\<lbrakk> A \<subseteq> L; a \<in> A \<rbrakk> \<Longrightarrow> a \<sqsubseteq> \<Squnion> A"
  using is_sup_Sup is_sup_upper by (blast dest: upper_boundD)

lemma Sup_least: "\<lbrakk> A \<subseteq> L; upper_bound x A \<rbrakk> \<Longrightarrow> \<Squnion> A \<sqsubseteq> x"
  using is_sup_Sup by (blast dest: is_sup_least)

lemma Inf_lower: "\<lbrakk> A \<subseteq> L; a \<in> A \<rbrakk> \<Longrightarrow> \<Sqinter> A \<sqsubseteq> a"
  using is_inf_Inf is_inf_lower by (blast dest: lower_boundD)

lemma Inf_greatest: "\<lbrakk> A \<subseteq> L; lower_bound x A \<rbrakk> \<Longrightarrow> x \<sqsubseteq> \<Sqinter> A"
  using is_inf_Inf by (blast dest: is_inf_greatest)

text \<open>Top and bottom: the sup and inf of the whole carrier.\<close>
definition top :: 'a (\<open>\<top>\<close>) where "\<top> = \<Squnion> L"
definition bottom :: 'a (\<open>\<bottom>\<close>) where "\<bottom> = \<Sqinter> L"

lemma top_closed [intro, simp]: "\<top> \<in> L" unfolding top_def by simp
lemma bottom_closed [intro, simp]: "\<bottom> \<in> L" unfolding bottom_def by simp

lemma top_greatest: "a \<in> L \<Longrightarrow> a \<sqsubseteq> \<top>"
  unfolding top_def using Sup_upper by blast

lemma bottom_least: "a \<in> L \<Longrightarrow> \<bottom> \<sqsubseteq> a"
  unfolding bottom_def using Inf_lower by blast

text \<open>A complete lattice is a lattice (binary sup/inf are the two-element cases).\<close>
sublocale Lattice
proof
  fix a b assume "a \<in> L" "b \<in> L"
  then have "{a, b} \<subseteq> L" by simp
  then show "\<exists>s. is_sup s {a, b}" and "\<exists>i. is_inf i {a, b}"
    using ex_Sup ex_Inf by blast+
qed

end


subsection \<open>Isotone maps\<close>

text \<open>An isotone (order-preserving, monotone) map between two partial orders.\<close>
definition isotone :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'b set \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"
  where "isotone LX leX LY leY f \<longleftrightarrow>
    f \<in> LX \<rightarrow> LY \<and> (\<forall>x\<in>LX. \<forall>y\<in>LX. leX x y \<longrightarrow> leY (f x) (f y))"

lemma isotoneI:
  "\<lbrakk> f \<in> LX \<rightarrow> LY; \<And>x y. \<lbrakk> x \<in> LX; y \<in> LX; leX x y \<rbrakk> \<Longrightarrow> leY (f x) (f y) \<rbrakk>
     \<Longrightarrow> isotone LX leX LY leY f"
  unfolding isotone_def by blast

lemma isotone_closed: "\<lbrakk> isotone LX leX LY leY f; x \<in> LX \<rbrakk> \<Longrightarrow> f x \<in> LY"
  unfolding isotone_def by blast

lemma isotone_le: "\<lbrakk> isotone LX leX LY leY f; x \<in> LX; y \<in> LX; leX x y \<rbrakk> \<Longrightarrow> leY (f x) (f y)"
  unfolding isotone_def by blast


subsection \<open>Galois connections\<close>

text \<open>A (monotone) Galois connection between two partial orders \<open>X\<close> and \<open>Y\<close>: a lower adjoint
  \<open>f : X \<rightarrow> Y\<close> and an upper adjoint \<open>g : Y \<rightarrow> X\<close> linked by the defining adjunction
  \<open>f x \<sqsubseteq>\<^bsub>Y\<^esub> y \<longleftrightarrow> x \<sqsubseteq>\<^bsub>X\<^esub> g y\<close>.  This is the abstract backbone of correspondences such as the Galois
  correspondence between subgroups and intermediate fields.\<close>
locale Galois_Connection =
  X: Partial_Order LX leX + Y: Partial_Order LY leY
  for LX and leX (infix \<open>\<sqsubseteq>\<^sub>X\<close> 50) and LY and leY (infix \<open>\<sqsubseteq>\<^sub>Y\<close> 50) +
  fixes f :: "'a \<Rightarrow> 'b" and g :: "'b \<Rightarrow> 'a"
  assumes f_closed: "f \<in> LX \<rightarrow> LY"
    and g_closed: "g \<in> LY \<rightarrow> LX"
    and galois: "\<lbrakk> x \<in> LX; y \<in> LY \<rbrakk> \<Longrightarrow> f x \<sqsubseteq>\<^sub>Y y \<longleftrightarrow> x \<sqsubseteq>\<^sub>X g y"
begin

lemma f_in: "x \<in> LX \<Longrightarrow> f x \<in> LY" using f_closed by auto
lemma g_in: "y \<in> LY \<Longrightarrow> g y \<in> LX" using g_closed by auto

text \<open>Unit and counit of the adjunction: \<open>x \<sqsubseteq> g (f x)\<close> and \<open>f (g y) \<sqsubseteq> y\<close>.\<close>
lemma unit: "x \<in> LX \<Longrightarrow> x \<sqsubseteq>\<^sub>X g (f x)"
  using galois[of x "f x"] f_in by simp

lemma counit: "y \<in> LY \<Longrightarrow> f (g y) \<sqsubseteq>\<^sub>Y y"
  using galois[of "g y" y] g_in by simp

text \<open>Both adjoints are isotone.\<close>
lemma lower_isotone: "isotone LX leX LY leY f"
proof (rule isotoneI[OF f_closed])
  fix x x' assume x: "x \<in> LX" and x': "x' \<in> LX" and le: "x \<sqsubseteq>\<^sub>X x'"
  \<comment> \<open>\<open>x \<sqsubseteq> x' \<sqsubseteq> g (f x')\<close>, so by the adjunction \<open>f x \<sqsubseteq> f x'\<close>.\<close>
  have "x \<sqsubseteq>\<^sub>X g (f x')"
    using le unit[OF x'] x x' g_in f_in by (blast intro: X.transitive)
  then show "f x \<sqsubseteq>\<^sub>Y f x'" using galois[OF x f_in[OF x']] by simp
qed

lemma upper_isotone: "isotone LY leY LX leX g"
proof (rule isotoneI[OF g_closed])
  fix y y' assume y: "y \<in> LY" and y': "y' \<in> LY" and le: "y \<sqsubseteq>\<^sub>Y y'"
  \<comment> \<open>\<open>f (g y) \<sqsubseteq> y \<sqsubseteq> y'\<close>, so by the adjunction \<open>g y \<sqsubseteq> g y'\<close>.\<close>
  have "f (g y) \<sqsubseteq>\<^sub>Y y'"
    using le counit[OF y] y y' f_in g_in by (blast intro: Y.transitive)
  then show "g y \<sqsubseteq>\<^sub>X g y'" using galois[OF g_in[OF y] y'] by simp
qed

text \<open>The composite \<open>g \<circ> f\<close> is a closure operator on \<open>X\<close>: expansive (@{thm unit}), isotone, and
  idempotent.  Dually \<open>f \<circ> g\<close> is a kernel (interior) operator on \<open>Y\<close>.  The two \<^emph>\<open>semi-inverse\<close>
  identities below --- \<open>f (g (f x)) = f x\<close> and \<open>g (f (g y)) = g y\<close> --- underlie idempotence.\<close>
lemma lower_semi_inverse: "x \<in> LX \<Longrightarrow> f (g (f x)) = f x"
proof (rule Y.antisymmetric)
  assume x: "x \<in> LX"
  show "f (g (f x)) \<in> LY" using x f_in g_in by blast
  show "f x \<in> LY" using x f_in by blast
  show "f (g (f x)) \<sqsubseteq>\<^sub>Y f x" using counit[OF f_in[OF x]] .
  \<comment> \<open>\<open>f x \<sqsubseteq> f (g (f x))\<close> by applying the lower adjoint's isotonicity to the unit \<open>x \<sqsubseteq> g (f x)\<close>.\<close>
  have gfx: "g (f x) \<in> LX" using x f_in g_in by blast
  show "f x \<sqsubseteq>\<^sub>Y f (g (f x))"
    by (rule isotone_le[OF lower_isotone x gfx unit[OF x]])
qed

lemma upper_semi_inverse: "y \<in> LY \<Longrightarrow> g (f (g y)) = g y"
proof (rule X.antisymmetric)
  assume y: "y \<in> LY"
  show "g (f (g y)) \<in> LX" using y g_in f_in by blast
  show "g y \<in> LX" using y g_in by blast
  show "g y \<sqsubseteq>\<^sub>X g (f (g y))" using unit[OF g_in[OF y]] .
  have fgy: "f (g y) \<in> LY" using y g_in f_in by blast
  show "g (f (g y)) \<sqsubseteq>\<^sub>X g y"
    by (rule isotone_le[OF upper_isotone fgy y counit[OF y]])
qed

text \<open>Idempotence of the closure operator \<open>g \<circ> f\<close> on \<open>X\<close>.\<close>
lemma closure_idempotent: "x \<in> LX \<Longrightarrow> g (f (g (f x))) = g (f x)"
  using upper_semi_inverse[OF f_in] by simp

text \<open>Idempotence of the kernel operator \<open>f \<circ> g\<close> on \<open>Y\<close>.\<close>
lemma kernel_idempotent: "y \<in> LY \<Longrightarrow> f (g (f (g y))) = f (g y)"
  using lower_semi_inverse[OF g_in] by simp

end

end
