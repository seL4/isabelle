(*  Title:      HOL/Lattices.thy
    Author:     Tobias Nipkow
*)

section {* Abstract lattices *}

theory Lattices
imports Groups
begin

subsection {* Abstract semilattice *}

text {*
  These locales provide a basic structure for interpretation into
  bigger structures;  extensions require careful thinking, otherwise
  undesired effects may occur due to interpretation.
*}

no_notation times (infixl "*" 70)
no_notation Groups.one ("1")

locale semilattice = abel_semigroup +
  assumes idem [simp]: "a * a = a"
begin

lemma left_idem [simp]: "a * (a * b) = a * b"
by (simp add: assoc [symmetric])

lemma right_idem [simp]: "(a * b) * b = a * b"
by (simp add: assoc)

end

locale semilattice_neutr = semilattice + comm_monoid

locale semilattice_order = semilattice +
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<preceq>" 50)
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<prec>" 50)
  assumes order_iff: "a \<preceq> b \<longleftrightarrow> a = a * b"
    and semilattice_strict_iff_order: "a \<prec> b \<longleftrightarrow> a \<preceq> b \<and> a \<noteq> b"
begin

lemma orderI:
  "a = a * b \<Longrightarrow> a \<preceq> b"
  by (simp add: order_iff)

lemma orderE:
  assumes "a \<preceq> b"
  obtains "a = a * b"
  using assms by (unfold order_iff)

sublocale ordering less_eq less
proof
  fix a b
  show "a \<prec> b \<longleftrightarrow> a \<preceq> b \<and> a \<noteq> b"
    by (fact semilattice_strict_iff_order)
next
  fix a
  show "a \<preceq> a"
    by (simp add: order_iff)
next
  fix a b
  assume "a \<preceq> b" "b \<preceq> a"
  then have "a = a * b" "a * b = b"
    by (simp_all add: order_iff commute)
  then show "a = b" by simp
next
  fix a b c
  assume "a \<preceq> b" "b \<preceq> c"
  then have "a = a * b" "b = b * c"
    by (simp_all add: order_iff commute)
  then have "a = a * (b * c)"
    by simp
  then have "a = (a * b) * c"
    by (simp add: assoc)
  with `a = a * b` [symmetric] have "a = a * c" by simp
  then show "a \<preceq> c" by (rule orderI)
qed

lemma cobounded1 [simp]:
  "a * b \<preceq> a"
  by (simp add: order_iff commute)  

lemma cobounded2 [simp]:
  "a * b \<preceq> b"
  by (simp add: order_iff)

lemma boundedI:
  assumes "a \<preceq> b" and "a \<preceq> c"
  shows "a \<preceq> b * c"
proof (rule orderI)
  from assms obtain "a * b = a" and "a * c = a" by (auto elim!: orderE)
  then show "a = a * (b * c)" by (simp add: assoc [symmetric])
qed

lemma boundedE:
  assumes "a \<preceq> b * c"
  obtains "a \<preceq> b" and "a \<preceq> c"
  using assms by (blast intro: trans cobounded1 cobounded2)

lemma bounded_iff [simp]:
  "a \<preceq> b * c \<longleftrightarrow> a \<preceq> b \<and> a \<preceq> c"
  by (blast intro: boundedI elim: boundedE)

lemma strict_boundedE:
  assumes "a \<prec> b * c"
  obtains "a \<prec> b" and "a \<prec> c"
  using assms by (auto simp add: commute strict_iff_order elim: orderE intro!: that)+

lemma coboundedI1:
  "a \<preceq> c \<Longrightarrow> a * b \<preceq> c"
  by (rule trans) auto

lemma coboundedI2:
  "b \<preceq> c \<Longrightarrow> a * b \<preceq> c"
  by (rule trans) auto

lemma strict_coboundedI1:
  "a \<prec> c \<Longrightarrow> a * b \<prec> c"
  using irrefl
    by (auto intro: not_eq_order_implies_strict coboundedI1 strict_implies_order elim: strict_boundedE)

lemma strict_coboundedI2:
  "b \<prec> c \<Longrightarrow> a * b \<prec> c"
  using strict_coboundedI1 [of b c a] by (simp add: commute)

lemma mono: "a \<preceq> c \<Longrightarrow> b \<preceq> d \<Longrightarrow> a * b \<preceq> c * d"
  by (blast intro: boundedI coboundedI1 coboundedI2)

lemma absorb1: "a \<preceq> b \<Longrightarrow> a * b = a"
  by (rule antisym) (auto simp add: refl)

lemma absorb2: "b \<preceq> a \<Longrightarrow> a * b = b"
  by (rule antisym) (auto simp add: refl)

lemma absorb_iff1: "a \<preceq> b \<longleftrightarrow> a * b = a"
  using order_iff by auto

lemma absorb_iff2: "b \<preceq> a \<longleftrightarrow> a * b = b"
  using order_iff by (auto simp add: commute)

end

locale semilattice_neutr_order = semilattice_neutr + semilattice_order
begin

sublocale ordering_top less_eq less 1
  by default (simp add: order_iff)

end

notation times (infixl "*" 70)
notation Groups.one ("1")


subsection {* Syntactic infimum and supremum operations *}

class inf =
  fixes inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)

class sup = 
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)


subsection {* Concrete lattices *}

notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less  (infix "\<sqsubset>" 50)

class semilattice_inf =  order + inf +
  assumes inf_le1 [simp]: "x \<sqinter> y \<sqsubseteq> x"
  and inf_le2 [simp]: "x \<sqinter> y \<sqsubseteq> y"
  and inf_greatest: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<sqinter> z"

class semilattice_sup = order + sup +
  assumes sup_ge1 [simp]: "x \<sqsubseteq> x \<squnion> y"
  and sup_ge2 [simp]: "y \<sqsubseteq> x \<squnion> y"
  and sup_least: "y \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> x \<Longrightarrow> y \<squnion> z \<sqsubseteq> x"
begin

text {* Dual lattice *}

lemma dual_semilattice:
  "class.semilattice_inf sup greater_eq greater"
by (rule class.semilattice_inf.intro, rule dual_order)
  (unfold_locales, simp_all add: sup_least)

end

class lattice = semilattice_inf + semilattice_sup


subsubsection {* Intro and elim rules*}

context semilattice_inf
begin

lemma le_infI1:
  "a \<sqsubseteq> x \<Longrightarrow> a \<sqinter> b \<sqsubseteq> x"
  by (rule order_trans) auto

lemma le_infI2:
  "b \<sqsubseteq> x \<Longrightarrow> a \<sqinter> b \<sqsubseteq> x"
  by (rule order_trans) auto

lemma le_infI: "x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> b \<Longrightarrow> x \<sqsubseteq> a \<sqinter> b"
  by (fact inf_greatest) (* FIXME: duplicate lemma *)

lemma le_infE: "x \<sqsubseteq> a \<sqinter> b \<Longrightarrow> (x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> b \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast intro: order_trans inf_le1 inf_le2)

lemma le_inf_iff:
  "x \<sqsubseteq> y \<sqinter> z \<longleftrightarrow> x \<sqsubseteq> y \<and> x \<sqsubseteq> z"
  by (blast intro: le_infI elim: le_infE)

lemma le_iff_inf:
  "x \<sqsubseteq> y \<longleftrightarrow> x \<sqinter> y = x"
  by (auto intro: le_infI1 antisym dest: eq_iff [THEN iffD1] simp add: le_inf_iff)

lemma inf_mono: "a \<sqsubseteq> c \<Longrightarrow> b \<sqsubseteq> d \<Longrightarrow> a \<sqinter> b \<sqsubseteq> c \<sqinter> d"
  by (fast intro: inf_greatest le_infI1 le_infI2)

lemma mono_inf:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>semilattice_inf"
  shows "mono f \<Longrightarrow> f (A \<sqinter> B) \<sqsubseteq> f A \<sqinter> f B"
  by (auto simp add: mono_def intro: Lattices.inf_greatest)

end

context semilattice_sup
begin

lemma le_supI1:
  "x \<sqsubseteq> a \<Longrightarrow> x \<sqsubseteq> a \<squnion> b"
  by (rule order_trans) auto

lemma le_supI2:
  "x \<sqsubseteq> b \<Longrightarrow> x \<sqsubseteq> a \<squnion> b"
  by (rule order_trans) auto 

lemma le_supI:
  "a \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> x \<Longrightarrow> a \<squnion> b \<sqsubseteq> x"
  by (fact sup_least) (* FIXME: duplicate lemma *)

lemma le_supE:
  "a \<squnion> b \<sqsubseteq> x \<Longrightarrow> (a \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> x \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast intro: order_trans sup_ge1 sup_ge2)

lemma le_sup_iff:
  "x \<squnion> y \<sqsubseteq> z \<longleftrightarrow> x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  by (blast intro: le_supI elim: le_supE)

lemma le_iff_sup:
  "x \<sqsubseteq> y \<longleftrightarrow> x \<squnion> y = y"
  by (auto intro: le_supI2 antisym dest: eq_iff [THEN iffD1] simp add: le_sup_iff)

lemma sup_mono: "a \<sqsubseteq> c \<Longrightarrow> b \<sqsubseteq> d \<Longrightarrow> a \<squnion> b \<sqsubseteq> c \<squnion> d"
  by (fast intro: sup_least le_supI1 le_supI2)

lemma mono_sup:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>semilattice_sup"
  shows "mono f \<Longrightarrow> f A \<squnion> f B \<sqsubseteq> f (A \<squnion> B)"
  by (auto simp add: mono_def intro: Lattices.sup_least)

end


subsubsection {* Equational laws *}

context semilattice_inf
begin

sublocale inf!: semilattice inf
proof
  fix a b c
  show "(a \<sqinter> b) \<sqinter> c = a \<sqinter> (b \<sqinter> c)"
    by (rule antisym) (auto intro: le_infI1 le_infI2 simp add: le_inf_iff)
  show "a \<sqinter> b = b \<sqinter> a"
    by (rule antisym) (auto simp add: le_inf_iff)
  show "a \<sqinter> a = a"
    by (rule antisym) (auto simp add: le_inf_iff)
qed

sublocale inf!: semilattice_order inf less_eq less
  by default (auto simp add: le_iff_inf less_le)

lemma inf_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
  by (fact inf.assoc)

lemma inf_commute: "(x \<sqinter> y) = (y \<sqinter> x)"
  by (fact inf.commute)

lemma inf_left_commute: "x \<sqinter> (y \<sqinter> z) = y \<sqinter> (x \<sqinter> z)"
  by (fact inf.left_commute)

lemma inf_idem: "x \<sqinter> x = x"
  by (fact inf.idem) (* already simp *)

lemma inf_left_idem: "x \<sqinter> (x \<sqinter> y) = x \<sqinter> y"
  by (fact inf.left_idem) (* already simp *)

lemma inf_right_idem: "(x \<sqinter> y) \<sqinter> y = x \<sqinter> y"
  by (fact inf.right_idem) (* already simp *)

lemma inf_absorb1: "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> y = x"
  by (rule antisym) auto

lemma inf_absorb2: "y \<sqsubseteq> x \<Longrightarrow> x \<sqinter> y = y"
  by (rule antisym) auto
 
lemmas inf_aci = inf_commute inf_assoc inf_left_commute inf_left_idem

end

context semilattice_sup
begin

sublocale sup!: semilattice sup
proof
  fix a b c
  show "(a \<squnion> b) \<squnion> c = a \<squnion> (b \<squnion> c)"
    by (rule antisym) (auto intro: le_supI1 le_supI2 simp add: le_sup_iff)
  show "a \<squnion> b = b \<squnion> a"
    by (rule antisym) (auto simp add: le_sup_iff)
  show "a \<squnion> a = a"
    by (rule antisym) (auto simp add: le_sup_iff)
qed

sublocale sup!: semilattice_order sup greater_eq greater
  by default (auto simp add: le_iff_sup sup.commute less_le)

lemma sup_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  by (fact sup.assoc)

lemma sup_commute: "(x \<squnion> y) = (y \<squnion> x)"
  by (fact sup.commute)

lemma sup_left_commute: "x \<squnion> (y \<squnion> z) = y \<squnion> (x \<squnion> z)"
  by (fact sup.left_commute)

lemma sup_idem: "x \<squnion> x = x"
  by (fact sup.idem) (* already simp *)

lemma sup_left_idem [simp]: "x \<squnion> (x \<squnion> y) = x \<squnion> y"
  by (fact sup.left_idem)

lemma sup_absorb1: "y \<sqsubseteq> x \<Longrightarrow> x \<squnion> y = x"
  by (rule antisym) auto

lemma sup_absorb2: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
  by (rule antisym) auto

lemmas sup_aci = sup_commute sup_assoc sup_left_commute sup_left_idem

end

context lattice
begin

lemma dual_lattice:
  "class.lattice sup (op \<ge>) (op >) inf"
  by (rule class.lattice.intro, rule dual_semilattice, rule class.semilattice_sup.intro, rule dual_order)
    (unfold_locales, auto)

lemma inf_sup_absorb [simp]: "x \<sqinter> (x \<squnion> y) = x"
  by (blast intro: antisym inf_le1 inf_greatest sup_ge1)

lemma sup_inf_absorb [simp]: "x \<squnion> (x \<sqinter> y) = x"
  by (blast intro: antisym sup_ge1 sup_least inf_le1)

lemmas inf_sup_aci = inf_aci sup_aci

lemmas inf_sup_ord = inf_le1 inf_le2 sup_ge1 sup_ge2

text{* Towards distributivity *}

lemma distrib_sup_le: "x \<squnion> (y \<sqinter> z) \<sqsubseteq> (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  by (auto intro: le_infI1 le_infI2 le_supI1 le_supI2)

lemma distrib_inf_le: "(x \<sqinter> y) \<squnion> (x \<sqinter> z) \<sqsubseteq> x \<sqinter> (y \<squnion> z)"
  by (auto intro: le_infI1 le_infI2 le_supI1 le_supI2)

text{* If you have one of them, you have them all. *}

lemma distrib_imp1:
assumes D: "!!x y z. x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
shows "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
proof-
  have "x \<squnion> (y \<sqinter> z) = (x \<squnion> (x \<sqinter> z)) \<squnion> (y \<sqinter> z)" by simp
  also have "\<dots> = x \<squnion> (z \<sqinter> (x \<squnion> y))"
    by (simp add: D inf_commute sup_assoc del: sup_inf_absorb)
  also have "\<dots> = ((x \<squnion> y) \<sqinter> x) \<squnion> ((x \<squnion> y) \<sqinter> z)"
    by(simp add: inf_commute)
  also have "\<dots> = (x \<squnion> y) \<sqinter> (x \<squnion> z)" by(simp add:D)
  finally show ?thesis .
qed

lemma distrib_imp2:
assumes D: "!!x y z. x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
shows "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
proof-
  have "x \<sqinter> (y \<squnion> z) = (x \<sqinter> (x \<squnion> z)) \<sqinter> (y \<squnion> z)" by simp
  also have "\<dots> = x \<sqinter> (z \<squnion> (x \<sqinter> y))"
    by (simp add: D sup_commute inf_assoc del: inf_sup_absorb)
  also have "\<dots> = ((x \<sqinter> y) \<squnion> x) \<sqinter> ((x \<sqinter> y) \<squnion> z)"
    by(simp add: sup_commute)
  also have "\<dots> = (x \<sqinter> y) \<squnion> (x \<sqinter> z)" by(simp add:D)
  finally show ?thesis .
qed

end

subsubsection {* Strict order *}

context semilattice_inf
begin

lemma less_infI1:
  "a \<sqsubset> x \<Longrightarrow> a \<sqinter> b \<sqsubset> x"
  by (auto simp add: less_le inf_absorb1 intro: le_infI1)

lemma less_infI2:
  "b \<sqsubset> x \<Longrightarrow> a \<sqinter> b \<sqsubset> x"
  by (auto simp add: less_le inf_absorb2 intro: le_infI2)

end

context semilattice_sup
begin

lemma less_supI1:
  "x \<sqsubset> a \<Longrightarrow> x \<sqsubset> a \<squnion> b"
  using dual_semilattice
  by (rule semilattice_inf.less_infI1)

lemma less_supI2:
  "x \<sqsubset> b \<Longrightarrow> x \<sqsubset> a \<squnion> b"
  using dual_semilattice
  by (rule semilattice_inf.less_infI2)

end


subsection {* Distributive lattices *}

class distrib_lattice = lattice +
  assumes sup_inf_distrib1: "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"

context distrib_lattice
begin

lemma sup_inf_distrib2:
  "(y \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
  by (simp add: sup_commute sup_inf_distrib1)

lemma inf_sup_distrib1:
  "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
  by (rule distrib_imp2 [OF sup_inf_distrib1])

lemma inf_sup_distrib2:
  "(y \<squnion> z) \<sqinter> x = (y \<sqinter> x) \<squnion> (z \<sqinter> x)"
  by (simp add: inf_commute inf_sup_distrib1)

lemma dual_distrib_lattice:
  "class.distrib_lattice sup (op \<ge>) (op >) inf"
  by (rule class.distrib_lattice.intro, rule dual_lattice)
    (unfold_locales, fact inf_sup_distrib1)

lemmas sup_inf_distrib =
  sup_inf_distrib1 sup_inf_distrib2

lemmas inf_sup_distrib =
  inf_sup_distrib1 inf_sup_distrib2

lemmas distrib =
  sup_inf_distrib1 sup_inf_distrib2 inf_sup_distrib1 inf_sup_distrib2

end


subsection {* Bounded lattices and boolean algebras *}

class bounded_semilattice_inf_top = semilattice_inf + order_top
begin

sublocale inf_top!: semilattice_neutr inf top
  + inf_top!: semilattice_neutr_order inf top less_eq less
proof
  fix x
  show "x \<sqinter> \<top> = x"
    by (rule inf_absorb1) simp
qed

end

class bounded_semilattice_sup_bot = semilattice_sup + order_bot
begin

sublocale sup_bot!: semilattice_neutr sup bot
  + sup_bot!: semilattice_neutr_order sup bot greater_eq greater
proof
  fix x
  show "x \<squnion> \<bottom> = x"
    by (rule sup_absorb1) simp
qed

end

class bounded_lattice_bot = lattice + order_bot
begin

subclass bounded_semilattice_sup_bot ..

lemma inf_bot_left [simp]:
  "\<bottom> \<sqinter> x = \<bottom>"
  by (rule inf_absorb1) simp

lemma inf_bot_right [simp]:
  "x \<sqinter> \<bottom> = \<bottom>"
  by (rule inf_absorb2) simp

lemma sup_bot_left:
  "\<bottom> \<squnion> x = x"
  by (fact sup_bot.left_neutral)

lemma sup_bot_right:
  "x \<squnion> \<bottom> = x"
  by (fact sup_bot.right_neutral)

lemma sup_eq_bot_iff [simp]:
  "x \<squnion> y = \<bottom> \<longleftrightarrow> x = \<bottom> \<and> y = \<bottom>"
  by (simp add: eq_iff)

lemma bot_eq_sup_iff [simp]:
  "\<bottom> = x \<squnion> y \<longleftrightarrow> x = \<bottom> \<and> y = \<bottom>"
  by (simp add: eq_iff)

end

class bounded_lattice_top = lattice + order_top
begin

subclass bounded_semilattice_inf_top ..

lemma sup_top_left [simp]:
  "\<top> \<squnion> x = \<top>"
  by (rule sup_absorb1) simp

lemma sup_top_right [simp]:
  "x \<squnion> \<top> = \<top>"
  by (rule sup_absorb2) simp

lemma inf_top_left:
  "\<top> \<sqinter> x = x"
  by (fact inf_top.left_neutral)

lemma inf_top_right:
  "x \<sqinter> \<top> = x"
  by (fact inf_top.right_neutral)

lemma inf_eq_top_iff [simp]:
  "x \<sqinter> y = \<top> \<longleftrightarrow> x = \<top> \<and> y = \<top>"
  by (simp add: eq_iff)

end

class bounded_lattice = lattice + order_bot + order_top
begin

subclass bounded_lattice_bot ..
subclass bounded_lattice_top ..

lemma dual_bounded_lattice:
  "class.bounded_lattice sup greater_eq greater inf \<top> \<bottom>"
  by unfold_locales (auto simp add: less_le_not_le)

end

class boolean_algebra = distrib_lattice + bounded_lattice + minus + uminus +
  assumes inf_compl_bot: "x \<sqinter> - x = \<bottom>"
    and sup_compl_top: "x \<squnion> - x = \<top>"
  assumes diff_eq: "x - y = x \<sqinter> - y"
begin

lemma dual_boolean_algebra:
  "class.boolean_algebra (\<lambda>x y. x \<squnion> - y) uminus sup greater_eq greater inf \<top> \<bottom>"
  by (rule class.boolean_algebra.intro, rule dual_bounded_lattice, rule dual_distrib_lattice)
    (unfold_locales, auto simp add: inf_compl_bot sup_compl_top diff_eq)

lemma compl_inf_bot [simp]:
  "- x \<sqinter> x = \<bottom>"
  by (simp add: inf_commute inf_compl_bot)

lemma compl_sup_top [simp]:
  "- x \<squnion> x = \<top>"
  by (simp add: sup_commute sup_compl_top)

lemma compl_unique:
  assumes "x \<sqinter> y = \<bottom>"
    and "x \<squnion> y = \<top>"
  shows "- x = y"
proof -
  have "(x \<sqinter> - x) \<squnion> (- x \<sqinter> y) = (x \<sqinter> y) \<squnion> (- x \<sqinter> y)"
    using inf_compl_bot assms(1) by simp
  then have "(- x \<sqinter> x) \<squnion> (- x \<sqinter> y) = (y \<sqinter> x) \<squnion> (y \<sqinter> - x)"
    by (simp add: inf_commute)
  then have "- x \<sqinter> (x \<squnion> y) = y \<sqinter> (x \<squnion> - x)"
    by (simp add: inf_sup_distrib1)
  then have "- x \<sqinter> \<top> = y \<sqinter> \<top>"
    using sup_compl_top assms(2) by simp
  then show "- x = y" by simp
qed

lemma double_compl [simp]:
  "- (- x) = x"
  using compl_inf_bot compl_sup_top by (rule compl_unique)

lemma compl_eq_compl_iff [simp]:
  "- x = - y \<longleftrightarrow> x = y"
proof
  assume "- x = - y"
  then have "- (- x) = - (- y)" by (rule arg_cong)
  then show "x = y" by simp
next
  assume "x = y"
  then show "- x = - y" by simp
qed

lemma compl_bot_eq [simp]:
  "- \<bottom> = \<top>"
proof -
  from sup_compl_top have "\<bottom> \<squnion> - \<bottom> = \<top>" .
  then show ?thesis by simp
qed

lemma compl_top_eq [simp]:
  "- \<top> = \<bottom>"
proof -
  from inf_compl_bot have "\<top> \<sqinter> - \<top> = \<bottom>" .
  then show ?thesis by simp
qed

lemma compl_inf [simp]:
  "- (x \<sqinter> y) = - x \<squnion> - y"
proof (rule compl_unique)
  have "(x \<sqinter> y) \<sqinter> (- x \<squnion> - y) = (y \<sqinter> (x \<sqinter> - x)) \<squnion> (x \<sqinter> (y \<sqinter> - y))"
    by (simp only: inf_sup_distrib inf_aci)
  then show "(x \<sqinter> y) \<sqinter> (- x \<squnion> - y) = \<bottom>"
    by (simp add: inf_compl_bot)
next
  have "(x \<sqinter> y) \<squnion> (- x \<squnion> - y) = (- y \<squnion> (x \<squnion> - x)) \<sqinter> (- x \<squnion> (y \<squnion> - y))"
    by (simp only: sup_inf_distrib sup_aci)
  then show "(x \<sqinter> y) \<squnion> (- x \<squnion> - y) = \<top>"
    by (simp add: sup_compl_top)
qed

lemma compl_sup [simp]:
  "- (x \<squnion> y) = - x \<sqinter> - y"
  using dual_boolean_algebra
  by (rule boolean_algebra.compl_inf)

lemma compl_mono:
  "x \<sqsubseteq> y \<Longrightarrow> - y \<sqsubseteq> - x"
proof -
  assume "x \<sqsubseteq> y"
  then have "x \<squnion> y = y" by (simp only: le_iff_sup)
  then have "- (x \<squnion> y) = - y" by simp
  then have "- x \<sqinter> - y = - y" by simp
  then have "- y \<sqinter> - x = - y" by (simp only: inf_commute)
  then show "- y \<sqsubseteq> - x" by (simp only: le_iff_inf)
qed

lemma compl_le_compl_iff [simp]:
  "- x \<sqsubseteq> - y \<longleftrightarrow> y \<sqsubseteq> x"
  by (auto dest: compl_mono)

lemma compl_le_swap1:
  assumes "y \<sqsubseteq> - x" shows "x \<sqsubseteq> -y"
proof -
  from assms have "- (- x) \<sqsubseteq> - y" by (simp only: compl_le_compl_iff)
  then show ?thesis by simp
qed

lemma compl_le_swap2:
  assumes "- y \<sqsubseteq> x" shows "- x \<sqsubseteq> y"
proof -
  from assms have "- x \<sqsubseteq> - (- y)" by (simp only: compl_le_compl_iff)
  then show ?thesis by simp
qed

lemma compl_less_compl_iff: (* TODO: declare [simp] ? *)
  "- x \<sqsubset> - y \<longleftrightarrow> y \<sqsubset> x"
  by (auto simp add: less_le)

lemma compl_less_swap1:
  assumes "y \<sqsubset> - x" shows "x \<sqsubset> - y"
proof -
  from assms have "- (- x) \<sqsubset> - y" by (simp only: compl_less_compl_iff)
  then show ?thesis by simp
qed

lemma compl_less_swap2:
  assumes "- y \<sqsubset> x" shows "- x \<sqsubset> y"
proof -
  from assms have "- x \<sqsubset> - (- y)" by (simp only: compl_less_compl_iff)
  then show ?thesis by simp
qed

end


subsection {* @{text "min/max"} as special case of lattice *}

context linorder
begin

sublocale min!: semilattice_order min less_eq less
  + max!: semilattice_order max greater_eq greater
  by default (auto simp add: min_def max_def)

lemma min_le_iff_disj:
  "min x y \<le> z \<longleftrightarrow> x \<le> z \<or> y \<le> z"
  unfolding min_def using linear by (auto intro: order_trans)

lemma le_max_iff_disj:
  "z \<le> max x y \<longleftrightarrow> z \<le> x \<or> z \<le> y"
  unfolding max_def using linear by (auto intro: order_trans)

lemma min_less_iff_disj:
  "min x y < z \<longleftrightarrow> x < z \<or> y < z"
  unfolding min_def le_less using less_linear by (auto intro: less_trans)

lemma less_max_iff_disj:
  "z < max x y \<longleftrightarrow> z < x \<or> z < y"
  unfolding max_def le_less using less_linear by (auto intro: less_trans)

lemma min_less_iff_conj [simp]:
  "z < min x y \<longleftrightarrow> z < x \<and> z < y"
  unfolding min_def le_less using less_linear by (auto intro: less_trans)

lemma max_less_iff_conj [simp]:
  "max x y < z \<longleftrightarrow> x < z \<and> y < z"
  unfolding max_def le_less using less_linear by (auto intro: less_trans)

lemma min_max_distrib1:
  "min (max b c) a = max (min b a) (min c a)"
  by (auto simp add: min_def max_def not_le dest: le_less_trans less_trans intro: antisym)

lemma min_max_distrib2:
  "min a (max b c) = max (min a b) (min a c)"
  by (auto simp add: min_def max_def not_le dest: le_less_trans less_trans intro: antisym)

lemma max_min_distrib1:
  "max (min b c) a = min (max b a) (max c a)"
  by (auto simp add: min_def max_def not_le dest: le_less_trans less_trans intro: antisym)

lemma max_min_distrib2:
  "max a (min b c) = min (max a b) (max a c)"
  by (auto simp add: min_def max_def not_le dest: le_less_trans less_trans intro: antisym)

lemmas min_max_distribs = min_max_distrib1 min_max_distrib2 max_min_distrib1 max_min_distrib2

lemma split_min [no_atp]:
  "P (min i j) \<longleftrightarrow> (i \<le> j \<longrightarrow> P i) \<and> (\<not> i \<le> j \<longrightarrow> P j)"
  by (simp add: min_def)

lemma split_max [no_atp]:
  "P (max i j) \<longleftrightarrow> (i \<le> j \<longrightarrow> P j) \<and> (\<not> i \<le> j \<longrightarrow> P i)"
  by (simp add: max_def)

lemma min_of_mono:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>linorder"
  shows "mono f \<Longrightarrow> min (f m) (f n) = f (min m n)"
  by (auto simp: mono_def Orderings.min_def min_def intro: Orderings.antisym)

lemma max_of_mono:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>linorder"
  shows "mono f \<Longrightarrow> max (f m) (f n) = f (max m n)"
  by (auto simp: mono_def Orderings.max_def max_def intro: Orderings.antisym)

end

lemma inf_min: "inf = (min \<Colon> 'a\<Colon>{semilattice_inf, linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (auto intro: antisym simp add: min_def fun_eq_iff)

lemma sup_max: "sup = (max \<Colon> 'a\<Colon>{semilattice_sup, linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (auto intro: antisym simp add: max_def fun_eq_iff)


subsection {* Uniqueness of inf and sup *}

lemma (in semilattice_inf) inf_unique:
  fixes f (infixl "\<triangle>" 70)
  assumes le1: "\<And>x y. x \<triangle> y \<sqsubseteq> x" and le2: "\<And>x y. x \<triangle> y \<sqsubseteq> y"
  and greatest: "\<And>x y z. x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<triangle> z"
  shows "x \<sqinter> y = x \<triangle> y"
proof (rule antisym)
  show "x \<triangle> y \<sqsubseteq> x \<sqinter> y" by (rule le_infI) (rule le1, rule le2)
next
  have leI: "\<And>x y z. x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<triangle> z" by (blast intro: greatest)
  show "x \<sqinter> y \<sqsubseteq> x \<triangle> y" by (rule leI) simp_all
qed

lemma (in semilattice_sup) sup_unique:
  fixes f (infixl "\<nabla>" 70)
  assumes ge1 [simp]: "\<And>x y. x \<sqsubseteq> x \<nabla> y" and ge2: "\<And>x y. y \<sqsubseteq> x \<nabla> y"
  and least: "\<And>x y z. y \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> x \<Longrightarrow> y \<nabla> z \<sqsubseteq> x"
  shows "x \<squnion> y = x \<nabla> y"
proof (rule antisym)
  show "x \<squnion> y \<sqsubseteq> x \<nabla> y" by (rule le_supI) (rule ge1, rule ge2)
next
  have leI: "\<And>x y z. x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<nabla> y \<sqsubseteq> z" by (blast intro: least)
  show "x \<nabla> y \<sqsubseteq> x \<squnion> y" by (rule leI) simp_all
qed


subsection {* Lattice on @{typ bool} *}

instantiation bool :: boolean_algebra
begin

definition
  bool_Compl_def [simp]: "uminus = Not"

definition
  bool_diff_def [simp]: "A - B \<longleftrightarrow> A \<and> \<not> B"

definition
  [simp]: "P \<sqinter> Q \<longleftrightarrow> P \<and> Q"

definition
  [simp]: "P \<squnion> Q \<longleftrightarrow> P \<or> Q"

instance proof
qed auto

end

lemma sup_boolI1:
  "P \<Longrightarrow> P \<squnion> Q"
  by simp

lemma sup_boolI2:
  "Q \<Longrightarrow> P \<squnion> Q"
  by simp

lemma sup_boolE:
  "P \<squnion> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R"
  by auto


subsection {* Lattice on @{typ "_ \<Rightarrow> _"} *}

instantiation "fun" :: (type, semilattice_sup) semilattice_sup
begin

definition
  "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)"

lemma sup_apply [simp, code]:
  "(f \<squnion> g) x = f x \<squnion> g x"
  by (simp add: sup_fun_def)

instance proof
qed (simp_all add: le_fun_def)

end

instantiation "fun" :: (type, semilattice_inf) semilattice_inf
begin

definition
  "f \<sqinter> g = (\<lambda>x. f x \<sqinter> g x)"

lemma inf_apply [simp, code]:
  "(f \<sqinter> g) x = f x \<sqinter> g x"
  by (simp add: inf_fun_def)

instance proof
qed (simp_all add: le_fun_def)

end

instance "fun" :: (type, lattice) lattice ..

instance "fun" :: (type, distrib_lattice) distrib_lattice proof
qed (rule ext, simp add: sup_inf_distrib1)

instance "fun" :: (type, bounded_lattice) bounded_lattice ..

instantiation "fun" :: (type, uminus) uminus
begin

definition
  fun_Compl_def: "- A = (\<lambda>x. - A x)"

lemma uminus_apply [simp, code]:
  "(- A) x = - (A x)"
  by (simp add: fun_Compl_def)

instance ..

end

instantiation "fun" :: (type, minus) minus
begin

definition
  fun_diff_def: "A - B = (\<lambda>x. A x - B x)"

lemma minus_apply [simp, code]:
  "(A - B) x = A x - B x"
  by (simp add: fun_diff_def)

instance ..

end

instance "fun" :: (type, boolean_algebra) boolean_algebra proof
qed (rule ext, simp_all add: inf_compl_bot sup_compl_top diff_eq)+


subsection {* Lattice on unary and binary predicates *}

lemma inf1I: "A x \<Longrightarrow> B x \<Longrightarrow> (A \<sqinter> B) x"
  by (simp add: inf_fun_def)

lemma inf2I: "A x y \<Longrightarrow> B x y \<Longrightarrow> (A \<sqinter> B) x y"
  by (simp add: inf_fun_def)

lemma inf1E: "(A \<sqinter> B) x \<Longrightarrow> (A x \<Longrightarrow> B x \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: inf_fun_def)

lemma inf2E: "(A \<sqinter> B) x y \<Longrightarrow> (A x y \<Longrightarrow> B x y \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: inf_fun_def)

lemma inf1D1: "(A \<sqinter> B) x \<Longrightarrow> A x"
  by (rule inf1E)

lemma inf2D1: "(A \<sqinter> B) x y \<Longrightarrow> A x y"
  by (rule inf2E)

lemma inf1D2: "(A \<sqinter> B) x \<Longrightarrow> B x"
  by (rule inf1E)

lemma inf2D2: "(A \<sqinter> B) x y \<Longrightarrow> B x y"
  by (rule inf2E)

lemma sup1I1: "A x \<Longrightarrow> (A \<squnion> B) x"
  by (simp add: sup_fun_def)

lemma sup2I1: "A x y \<Longrightarrow> (A \<squnion> B) x y"
  by (simp add: sup_fun_def)

lemma sup1I2: "B x \<Longrightarrow> (A \<squnion> B) x"
  by (simp add: sup_fun_def)

lemma sup2I2: "B x y \<Longrightarrow> (A \<squnion> B) x y"
  by (simp add: sup_fun_def)

lemma sup1E: "(A \<squnion> B) x \<Longrightarrow> (A x \<Longrightarrow> P) \<Longrightarrow> (B x \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: sup_fun_def) iprover

lemma sup2E: "(A \<squnion> B) x y \<Longrightarrow> (A x y \<Longrightarrow> P) \<Longrightarrow> (B x y \<Longrightarrow> P) \<Longrightarrow> P"
  by (simp add: sup_fun_def) iprover

text {*
  \medskip Classical introduction rule: no commitment to @{text A} vs
  @{text B}.
*}

lemma sup1CI: "(\<not> B x \<Longrightarrow> A x) \<Longrightarrow> (A \<squnion> B) x"
  by (auto simp add: sup_fun_def)

lemma sup2CI: "(\<not> B x y \<Longrightarrow> A x y) \<Longrightarrow> (A \<squnion> B) x y"
  by (auto simp add: sup_fun_def)


no_notation
  less_eq (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50)

end

