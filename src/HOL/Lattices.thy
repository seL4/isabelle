(*  Title:      HOL/Lattices.thy
    Author:     Tobias Nipkow
*)

section \<open>Abstract lattices\<close>

theory Lattices
imports Groups
begin

subsection \<open>Abstract semilattice\<close>

text \<open>
  These locales provide a basic structure for interpretation into
  bigger structures;  extensions require careful thinking, otherwise
  undesired effects may occur due to interpretation.
\<close>

locale semilattice = abel_semigroup +
  assumes idem [simp]: "a \<^bold>* a = a"
begin

lemma left_idem [simp]: "a \<^bold>* (a \<^bold>* b) = a \<^bold>* b"
  by (simp add: assoc [symmetric])

lemma right_idem [simp]: "(a \<^bold>* b) \<^bold>* b = a \<^bold>* b"
  by (simp add: assoc)

end

locale semilattice_neutr = semilattice + comm_monoid

locale semilattice_order = semilattice +
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<^bold>\<le>" 50)
    and less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infix "\<^bold><" 50)
  assumes order_iff: "a \<^bold>\<le> b \<longleftrightarrow> a = a \<^bold>* b"
    and strict_order_iff: "a \<^bold>< b \<longleftrightarrow> a = a \<^bold>* b \<and> a \<noteq> b"
begin

lemma orderI: "a = a \<^bold>* b \<Longrightarrow> a \<^bold>\<le> b"
  by (simp add: order_iff)

lemma orderE:
  assumes "a \<^bold>\<le> b"
  obtains "a = a \<^bold>* b"
  using assms by (unfold order_iff)

sublocale ordering less_eq less
proof
  show "a \<^bold>< b \<longleftrightarrow> a \<^bold>\<le> b \<and> a \<noteq> b" for a b
    by (simp add: order_iff strict_order_iff)
next
  show "a \<^bold>\<le> a" for a
    by (simp add: order_iff)
next
  fix a b
  assume "a \<^bold>\<le> b" "b \<^bold>\<le> a"
  then have "a = a \<^bold>* b" "a \<^bold>* b = b"
    by (simp_all add: order_iff commute)
  then show "a = b" by simp
next
  fix a b c
  assume "a \<^bold>\<le> b" "b \<^bold>\<le> c"
  then have "a = a \<^bold>* b" "b = b \<^bold>* c"
    by (simp_all add: order_iff commute)
  then have "a = a \<^bold>* (b \<^bold>* c)"
    by simp
  then have "a = (a \<^bold>* b) \<^bold>* c"
    by (simp add: assoc)
  with \<open>a = a \<^bold>* b\<close> [symmetric] have "a = a \<^bold>* c" by simp
  then show "a \<^bold>\<le> c" by (rule orderI)
qed

lemma cobounded1 [simp]: "a \<^bold>* b \<^bold>\<le> a"
  by (simp add: order_iff commute)

lemma cobounded2 [simp]: "a \<^bold>* b \<^bold>\<le> b"
  by (simp add: order_iff)

lemma boundedI:
  assumes "a \<^bold>\<le> b" and "a \<^bold>\<le> c"
  shows "a \<^bold>\<le> b \<^bold>* c"
proof (rule orderI)
  from assms obtain "a \<^bold>* b = a" and "a \<^bold>* c = a"
    by (auto elim!: orderE)
  then show "a = a \<^bold>* (b \<^bold>* c)"
    by (simp add: assoc [symmetric])
qed

lemma boundedE:
  assumes "a \<^bold>\<le> b \<^bold>* c"
  obtains "a \<^bold>\<le> b" and "a \<^bold>\<le> c"
  using assms by (blast intro: trans cobounded1 cobounded2)

lemma bounded_iff [simp]: "a \<^bold>\<le> b \<^bold>* c \<longleftrightarrow> a \<^bold>\<le> b \<and> a \<^bold>\<le> c"
  by (blast intro: boundedI elim: boundedE)

lemma strict_boundedE:
  assumes "a \<^bold>< b \<^bold>* c"
  obtains "a \<^bold>< b" and "a \<^bold>< c"
  using assms by (auto simp add: commute strict_iff_order elim: orderE intro!: that)+

lemma coboundedI1: "a \<^bold>\<le> c \<Longrightarrow> a \<^bold>* b \<^bold>\<le> c"
  by (rule trans) auto

lemma coboundedI2: "b \<^bold>\<le> c \<Longrightarrow> a \<^bold>* b \<^bold>\<le> c"
  by (rule trans) auto

lemma strict_coboundedI1: "a \<^bold>< c \<Longrightarrow> a \<^bold>* b \<^bold>< c"
  using irrefl
  by (auto intro: not_eq_order_implies_strict coboundedI1 strict_implies_order
      elim: strict_boundedE)

lemma strict_coboundedI2: "b \<^bold>< c \<Longrightarrow> a \<^bold>* b \<^bold>< c"
  using strict_coboundedI1 [of b c a] by (simp add: commute)

lemma mono: "a \<^bold>\<le> c \<Longrightarrow> b \<^bold>\<le> d \<Longrightarrow> a \<^bold>* b \<^bold>\<le> c \<^bold>* d"
  by (blast intro: boundedI coboundedI1 coboundedI2)

lemma absorb1: "a \<^bold>\<le> b \<Longrightarrow> a \<^bold>* b = a"
  by (rule antisym) (auto simp: refl)

lemma absorb2: "b \<^bold>\<le> a \<Longrightarrow> a \<^bold>* b = b"
  by (rule antisym) (auto simp: refl)

lemma absorb3: "a \<^bold>< b \<Longrightarrow> a \<^bold>* b = a"
  by (rule absorb1) (rule strict_implies_order)

lemma absorb4: "b \<^bold>< a \<Longrightarrow> a \<^bold>* b = b"
  by (rule absorb2) (rule strict_implies_order)

lemma absorb_iff1: "a \<^bold>\<le> b \<longleftrightarrow> a \<^bold>* b = a"
  using order_iff by auto

lemma absorb_iff2: "b \<^bold>\<le> a \<longleftrightarrow> a \<^bold>* b = b"
  using order_iff by (auto simp add: commute)

end

locale semilattice_neutr_order = semilattice_neutr + semilattice_order
begin

sublocale ordering_top less_eq less "\<^bold>1"
  by standard (simp add: order_iff)

lemma eq_neutr_iff [simp]: \<open>a \<^bold>* b = \<^bold>1 \<longleftrightarrow> a = \<^bold>1 \<and> b = \<^bold>1\<close>
  by (simp add: eq_iff)

lemma neutr_eq_iff [simp]: \<open>\<^bold>1 = a \<^bold>* b \<longleftrightarrow> a = \<^bold>1 \<and> b = \<^bold>1\<close>
  by (simp add: eq_iff)

end

text \<open>Interpretations for boolean operators\<close>

interpretation conj: semilattice_neutr \<open>(\<and>)\<close> True
  by standard auto

interpretation disj: semilattice_neutr \<open>(\<or>)\<close> False
  by standard auto

declare conj_assoc [ac_simps del] disj_assoc [ac_simps del] \<comment> \<open>already simp by default\<close>


subsection \<open>Syntactic infimum and supremum operations\<close>

class inf =
  fixes inf :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 70)

class sup =
  fixes sup :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<squnion>" 65)


subsection \<open>Concrete lattices\<close>

class semilattice_inf = order + inf +
  assumes inf_le1 [simp]: "x \<sqinter> y \<le> x"
  and inf_le2 [simp]: "x \<sqinter> y \<le> y"
  and inf_greatest: "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"

class semilattice_sup = order + sup +
  assumes sup_ge1 [simp]: "x \<le> x \<squnion> y"
  and sup_ge2 [simp]: "y \<le> x \<squnion> y"
  and sup_least: "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
begin

text \<open>Dual lattice.\<close>
lemma dual_semilattice: "class.semilattice_inf sup greater_eq greater"
  by (rule class.semilattice_inf.intro, rule dual_order)
    (unfold_locales, simp_all add: sup_least)

end

class lattice = semilattice_inf + semilattice_sup


subsubsection \<open>Intro and elim rules\<close>

context semilattice_inf
begin

lemma le_infI1: "a \<le> x \<Longrightarrow> a \<sqinter> b \<le> x"
  by (rule order_trans) auto

lemma le_infI2: "b \<le> x \<Longrightarrow> a \<sqinter> b \<le> x"
  by (rule order_trans) auto

lemma le_infI: "x \<le> a \<Longrightarrow> x \<le> b \<Longrightarrow> x \<le> a \<sqinter> b"
  by (fact inf_greatest) (* FIXME: duplicate lemma *)

lemma le_infE: "x \<le> a \<sqinter> b \<Longrightarrow> (x \<le> a \<Longrightarrow> x \<le> b \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast intro: order_trans inf_le1 inf_le2)

lemma le_inf_iff: "x \<le> y \<sqinter> z \<longleftrightarrow> x \<le> y \<and> x \<le> z"
  by (blast intro: le_infI elim: le_infE)

lemma le_iff_inf: "x \<le> y \<longleftrightarrow> x \<sqinter> y = x"
  by (auto intro: le_infI1 order.antisym dest: order.eq_iff [THEN iffD1] simp add: le_inf_iff)

lemma inf_mono: "a \<le> c \<Longrightarrow> b \<le> d \<Longrightarrow> a \<sqinter> b \<le> c \<sqinter> d"
  by (fast intro: inf_greatest le_infI1 le_infI2)

lemma mono_inf: "mono f \<Longrightarrow> f (A \<sqinter> B) \<le> f A \<sqinter> f B" for f :: "'a \<Rightarrow> 'b::semilattice_inf"
  by (auto simp add: mono_def intro: Lattices.inf_greatest)

end

context semilattice_sup
begin

lemma le_supI1: "x \<le> a \<Longrightarrow> x \<le> a \<squnion> b"
  by (rule order_trans) auto

lemma le_supI2: "x \<le> b \<Longrightarrow> x \<le> a \<squnion> b"
  by (rule order_trans) auto

lemma le_supI: "a \<le> x \<Longrightarrow> b \<le> x \<Longrightarrow> a \<squnion> b \<le> x"
  by (fact sup_least) (* FIXME: duplicate lemma *)

lemma le_supE: "a \<squnion> b \<le> x \<Longrightarrow> (a \<le> x \<Longrightarrow> b \<le> x \<Longrightarrow> P) \<Longrightarrow> P"
  by (blast intro: order_trans sup_ge1 sup_ge2)

lemma le_sup_iff: "x \<squnion> y \<le> z \<longleftrightarrow> x \<le> z \<and> y \<le> z"
  by (blast intro: le_supI elim: le_supE)

lemma le_iff_sup: "x \<le> y \<longleftrightarrow> x \<squnion> y = y"
  by (auto intro: le_supI2 order.antisym dest: order.eq_iff [THEN iffD1] simp add: le_sup_iff)

lemma sup_mono: "a \<le> c \<Longrightarrow> b \<le> d \<Longrightarrow> a \<squnion> b \<le> c \<squnion> d"
  by (fast intro: sup_least le_supI1 le_supI2)

lemma mono_sup: "mono f \<Longrightarrow> f A \<squnion> f B \<le> f (A \<squnion> B)" for f :: "'a \<Rightarrow> 'b::semilattice_sup"
  by (auto simp add: mono_def intro: Lattices.sup_least)

end


subsubsection \<open>Equational laws\<close>

context semilattice_inf
begin

sublocale inf: semilattice inf
proof
  fix a b c
  show "(a \<sqinter> b) \<sqinter> c = a \<sqinter> (b \<sqinter> c)"
    by (rule order.antisym) (auto intro: le_infI1 le_infI2 simp add: le_inf_iff)
  show "a \<sqinter> b = b \<sqinter> a"
    by (rule order.antisym) (auto simp add: le_inf_iff)
  show "a \<sqinter> a = a"
    by (rule order.antisym) (auto simp add: le_inf_iff)
qed

sublocale inf: semilattice_order inf less_eq less
  by standard (auto simp add: le_iff_inf less_le)

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

lemma inf_absorb1: "x \<le> y \<Longrightarrow> x \<sqinter> y = x"
  by (rule order.antisym) auto

lemma inf_absorb2: "y \<le> x \<Longrightarrow> x \<sqinter> y = y"
  by (rule order.antisym) auto

lemmas inf_aci = inf_commute inf_assoc inf_left_commute inf_left_idem

end

context semilattice_sup
begin

sublocale sup: semilattice sup
proof
  fix a b c
  show "(a \<squnion> b) \<squnion> c = a \<squnion> (b \<squnion> c)"
    by (rule order.antisym) (auto intro: le_supI1 le_supI2 simp add: le_sup_iff)
  show "a \<squnion> b = b \<squnion> a"
    by (rule order.antisym) (auto simp add: le_sup_iff)
  show "a \<squnion> a = a"
    by (rule order.antisym) (auto simp add: le_sup_iff)
qed

sublocale sup: semilattice_order sup greater_eq greater
  by standard (auto simp add: le_iff_sup sup.commute less_le)

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

lemma sup_absorb1: "y \<le> x \<Longrightarrow> x \<squnion> y = x"
  by (rule order.antisym) auto

lemma sup_absorb2: "x \<le> y \<Longrightarrow> x \<squnion> y = y"
  by (rule order.antisym) auto

lemmas sup_aci = sup_commute sup_assoc sup_left_commute sup_left_idem

end

context lattice
begin

lemma dual_lattice: "class.lattice sup (\<ge>) (>) inf"
  by (rule class.lattice.intro,
      rule dual_semilattice,
      rule class.semilattice_sup.intro,
      rule dual_order)
    (unfold_locales, auto)

lemma inf_sup_absorb [simp]: "x \<sqinter> (x \<squnion> y) = x"
  by (blast intro: order.antisym inf_le1 inf_greatest sup_ge1)

lemma sup_inf_absorb [simp]: "x \<squnion> (x \<sqinter> y) = x"
  by (blast intro: order.antisym sup_ge1 sup_least inf_le1)

lemmas inf_sup_aci = inf_aci sup_aci

lemmas inf_sup_ord = inf_le1 inf_le2 sup_ge1 sup_ge2

text \<open>Towards distributivity.\<close>

lemma distrib_sup_le: "x \<squnion> (y \<sqinter> z) \<le> (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  by (auto intro: le_infI1 le_infI2 le_supI1 le_supI2)

lemma distrib_inf_le: "(x \<sqinter> y) \<squnion> (x \<sqinter> z) \<le> x \<sqinter> (y \<squnion> z)"
  by (auto intro: le_infI1 le_infI2 le_supI1 le_supI2)

text \<open>If you have one of them, you have them all.\<close>

lemma distrib_imp1:
  assumes distrib: "\<And>x y z. x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
  shows "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
proof-
  have "x \<squnion> (y \<sqinter> z) = (x \<squnion> (x \<sqinter> z)) \<squnion> (y \<sqinter> z)"
    by simp
  also have "\<dots> = x \<squnion> (z \<sqinter> (x \<squnion> y))"
    by (simp add: distrib inf_commute sup_assoc del: sup_inf_absorb)
  also have "\<dots> = ((x \<squnion> y) \<sqinter> x) \<squnion> ((x \<squnion> y) \<sqinter> z)"
    by (simp add: inf_commute)
  also have "\<dots> = (x \<squnion> y) \<sqinter> (x \<squnion> z)" by(simp add:distrib)
  finally show ?thesis .
qed

lemma distrib_imp2:
  assumes distrib: "\<And>x y z. x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
  shows "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
proof-
  have "x \<sqinter> (y \<squnion> z) = (x \<sqinter> (x \<squnion> z)) \<sqinter> (y \<squnion> z)"
    by simp
  also have "\<dots> = x \<sqinter> (z \<squnion> (x \<sqinter> y))"
    by (simp add: distrib sup_commute inf_assoc del: inf_sup_absorb)
  also have "\<dots> = ((x \<sqinter> y) \<squnion> x) \<sqinter> ((x \<sqinter> y) \<squnion> z)"
    by (simp add: sup_commute)
  also have "\<dots> = (x \<sqinter> y) \<squnion> (x \<sqinter> z)" by (simp add:distrib)
  finally show ?thesis .
qed

end


subsubsection \<open>Strict order\<close>

context semilattice_inf
begin

lemma less_infI1: "a < x \<Longrightarrow> a \<sqinter> b < x"
  by (auto simp add: less_le inf_absorb1 intro: le_infI1)

lemma less_infI2: "b < x \<Longrightarrow> a \<sqinter> b < x"
  by (auto simp add: less_le inf_absorb2 intro: le_infI2)

end

context semilattice_sup
begin

lemma less_supI1: "x < a \<Longrightarrow> x < a \<squnion> b"
  using dual_semilattice
  by (rule semilattice_inf.less_infI1)

lemma less_supI2: "x < b \<Longrightarrow> x < a \<squnion> b"
  using dual_semilattice
  by (rule semilattice_inf.less_infI2)

end


subsection \<open>Distributive lattices\<close>

class distrib_lattice = lattice +
  assumes sup_inf_distrib1: "x \<squnion> (y \<sqinter> z) = (x \<squnion> y) \<sqinter> (x \<squnion> z)"

context distrib_lattice
begin

lemma sup_inf_distrib2: "(y \<sqinter> z) \<squnion> x = (y \<squnion> x) \<sqinter> (z \<squnion> x)"
  by (simp add: sup_commute sup_inf_distrib1)

lemma inf_sup_distrib1: "x \<sqinter> (y \<squnion> z) = (x \<sqinter> y) \<squnion> (x \<sqinter> z)"
  by (rule distrib_imp2 [OF sup_inf_distrib1])

lemma inf_sup_distrib2: "(y \<squnion> z) \<sqinter> x = (y \<sqinter> x) \<squnion> (z \<sqinter> x)"
  by (simp add: inf_commute inf_sup_distrib1)

lemma dual_distrib_lattice: "class.distrib_lattice sup (\<ge>) (>) inf"
  by (rule class.distrib_lattice.intro, rule dual_lattice)
    (unfold_locales, fact inf_sup_distrib1)

lemmas sup_inf_distrib = sup_inf_distrib1 sup_inf_distrib2

lemmas inf_sup_distrib = inf_sup_distrib1 inf_sup_distrib2

lemmas distrib = sup_inf_distrib1 sup_inf_distrib2 inf_sup_distrib1 inf_sup_distrib2

end


subsection \<open>Bounded lattices\<close>

class bounded_semilattice_inf_top = semilattice_inf + order_top
begin

sublocale inf_top: semilattice_neutr inf top
  + inf_top: semilattice_neutr_order inf top less_eq less
proof
  show "x \<sqinter> \<top> = x" for x
    by (rule inf_absorb1) simp
qed

lemma inf_top_left: "\<top> \<sqinter> x = x"
  by (fact inf_top.left_neutral)

lemma inf_top_right: "x \<sqinter> \<top> = x"
  by (fact inf_top.right_neutral)

lemma inf_eq_top_iff: "x \<sqinter> y = \<top> \<longleftrightarrow> x = \<top> \<and> y = \<top>"
  by (fact inf_top.eq_neutr_iff)

lemma top_eq_inf_iff: "\<top> = x \<sqinter> y \<longleftrightarrow> x = \<top> \<and> y = \<top>"
  by (fact inf_top.neutr_eq_iff)

end

class bounded_semilattice_sup_bot = semilattice_sup + order_bot
begin

sublocale sup_bot: semilattice_neutr sup bot
  + sup_bot: semilattice_neutr_order sup bot greater_eq greater
proof
  show "x \<squnion> \<bottom> = x" for x
    by (rule sup_absorb1) simp
qed

lemma sup_bot_left: "\<bottom> \<squnion> x = x"
  by (fact sup_bot.left_neutral)

lemma sup_bot_right: "x \<squnion> \<bottom> = x"
  by (fact sup_bot.right_neutral)

lemma sup_eq_bot_iff: "x \<squnion> y = \<bottom> \<longleftrightarrow> x = \<bottom> \<and> y = \<bottom>"
  by (fact sup_bot.eq_neutr_iff)

lemma bot_eq_sup_iff: "\<bottom> = x \<squnion> y \<longleftrightarrow> x = \<bottom> \<and> y = \<bottom>"
  by (fact sup_bot.neutr_eq_iff)

end

class bounded_lattice_bot = lattice + order_bot
begin

subclass bounded_semilattice_sup_bot ..

lemma inf_bot_left [simp]: "\<bottom> \<sqinter> x = \<bottom>"
  by (rule inf_absorb1) simp

lemma inf_bot_right [simp]: "x \<sqinter> \<bottom> = \<bottom>"
  by (rule inf_absorb2) simp

end

class bounded_lattice_top = lattice + order_top
begin

subclass bounded_semilattice_inf_top ..

lemma sup_top_left [simp]: "\<top> \<squnion> x = \<top>"
  by (rule sup_absorb1) simp

lemma sup_top_right [simp]: "x \<squnion> \<top> = \<top>"
  by (rule sup_absorb2) simp

end

class bounded_lattice = lattice + order_bot + order_top
begin

subclass bounded_lattice_bot ..
subclass bounded_lattice_top ..

lemma dual_bounded_lattice: "class.bounded_lattice sup greater_eq greater inf \<top> \<bottom>"
  by unfold_locales (auto simp add: less_le_not_le)

end


subsection \<open>\<open>min/max\<close> as special case of lattice\<close>

context linorder
begin

sublocale min: semilattice_order min less_eq less
  + max: semilattice_order max greater_eq greater
  by standard (auto simp add: min_def max_def)

declare min.absorb1 [simp] min.absorb2 [simp]
  min.absorb3 [simp] min.absorb4 [simp]
  max.absorb1 [simp] max.absorb2 [simp]
  max.absorb3 [simp] max.absorb4 [simp]

lemma min_le_iff_disj: "min x y \<le> z \<longleftrightarrow> x \<le> z \<or> y \<le> z"
  unfolding min_def using linear by (auto intro: order_trans)

lemma le_max_iff_disj: "z \<le> max x y \<longleftrightarrow> z \<le> x \<or> z \<le> y"
  unfolding max_def using linear by (auto intro: order_trans)

lemma min_less_iff_disj: "min x y < z \<longleftrightarrow> x < z \<or> y < z"
  unfolding min_def le_less using less_linear by (auto intro: less_trans)

lemma less_max_iff_disj: "z < max x y \<longleftrightarrow> z < x \<or> z < y"
  unfolding max_def le_less using less_linear by (auto intro: less_trans)

lemma min_less_iff_conj [simp]: "z < min x y \<longleftrightarrow> z < x \<and> z < y"
  unfolding min_def le_less using less_linear by (auto intro: less_trans)

lemma max_less_iff_conj [simp]: "max x y < z \<longleftrightarrow> x < z \<and> y < z"
  unfolding max_def le_less using less_linear by (auto intro: less_trans)

lemma min_max_distrib1: "min (max b c) a = max (min b a) (min c a)"
  by (auto simp add: min_def max_def not_le dest: le_less_trans less_trans intro: antisym)

lemma min_max_distrib2: "min a (max b c) = max (min a b) (min a c)"
  by (auto simp add: min_def max_def not_le dest: le_less_trans less_trans intro: antisym)

lemma max_min_distrib1: "max (min b c) a = min (max b a) (max c a)"
  by (auto simp add: min_def max_def not_le dest: le_less_trans less_trans intro: antisym)

lemma max_min_distrib2: "max a (min b c) = min (max a b) (max a c)"
  by (auto simp add: min_def max_def not_le dest: le_less_trans less_trans intro: antisym)

lemmas min_max_distribs = min_max_distrib1 min_max_distrib2 max_min_distrib1 max_min_distrib2

lemma split_min [no_atp]: "P (min i j) \<longleftrightarrow> (i \<le> j \<longrightarrow> P i) \<and> (\<not> i \<le> j \<longrightarrow> P j)"
  by (simp add: min_def)

lemma split_max [no_atp]: "P (max i j) \<longleftrightarrow> (i \<le> j \<longrightarrow> P j) \<and> (\<not> i \<le> j \<longrightarrow> P i)"
  by (simp add: max_def)

lemma split_min_lin [no_atp]:
  \<open>P (min a b) \<longleftrightarrow> (b = a \<longrightarrow> P a) \<and> (a < b \<longrightarrow> P a) \<and> (b < a \<longrightarrow> P b)\<close>
  by (cases a b rule: linorder_cases) auto

lemma split_max_lin [no_atp]:
  \<open>P (max a b) \<longleftrightarrow> (b = a \<longrightarrow> P a) \<and> (a < b \<longrightarrow> P b) \<and> (b < a \<longrightarrow> P a)\<close>
  by (cases a b rule: linorder_cases) auto

lemma min_of_mono: "mono f \<Longrightarrow> min (f m) (f n) = f (min m n)" for f :: "'a \<Rightarrow> 'b::linorder"
  by (auto simp: mono_def Orderings.min_def min_def intro: Orderings.antisym)

lemma max_of_mono: "mono f \<Longrightarrow> max (f m) (f n) = f (max m n)" for f :: "'a \<Rightarrow> 'b::linorder"
  by (auto simp: mono_def Orderings.max_def max_def intro: Orderings.antisym)

end

lemma max_of_antimono: "antimono f \<Longrightarrow> max (f x) (f y) = f (min x y)"
  and min_of_antimono: "antimono f \<Longrightarrow> min (f x) (f y) = f (max x y)"
  for f::"'a::linorder \<Rightarrow> 'b::linorder"
  by (auto simp: antimono_def Orderings.max_def min_def intro!: antisym)

lemma inf_min: "inf = (min :: 'a::{semilattice_inf,linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (auto intro: antisym simp add: min_def fun_eq_iff)

lemma sup_max: "sup = (max :: 'a::{semilattice_sup,linorder} \<Rightarrow> 'a \<Rightarrow> 'a)"
  by (auto intro: antisym simp add: max_def fun_eq_iff)


subsection \<open>Uniqueness of inf and sup\<close>

lemma (in semilattice_inf) inf_unique:
  fixes f  (infixl "\<triangle>" 70)
  assumes le1: "\<And>x y. x \<triangle> y \<le> x"
    and le2: "\<And>x y. x \<triangle> y \<le> y"
    and greatest: "\<And>x y z. x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<triangle> z"
  shows "x \<sqinter> y = x \<triangle> y"
proof (rule order.antisym)
  show "x \<triangle> y \<le> x \<sqinter> y"
    by (rule le_infI) (rule le1, rule le2)
  have leI: "\<And>x y z. x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<triangle> z"
    by (blast intro: greatest)
  show "x \<sqinter> y \<le> x \<triangle> y"
    by (rule leI) simp_all
qed

lemma (in semilattice_sup) sup_unique:
  fixes f  (infixl "\<nabla>" 70)
  assumes ge1 [simp]: "\<And>x y. x \<le> x \<nabla> y"
    and ge2: "\<And>x y. y \<le> x \<nabla> y"
    and least: "\<And>x y z. y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<nabla> z \<le> x"
  shows "x \<squnion> y = x \<nabla> y"
proof (rule order.antisym)
  show "x \<squnion> y \<le> x \<nabla> y"
    by (rule le_supI) (rule ge1, rule ge2)
  have leI: "\<And>x y z. x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> x \<nabla> y \<le> z"
    by (blast intro: least)
  show "x \<nabla> y \<le> x \<squnion> y"
    by (rule leI) simp_all
qed


subsection \<open>Lattice on \<^typ>\<open>_ \<Rightarrow> _\<close>\<close>

instantiation "fun" :: (type, semilattice_sup) semilattice_sup
begin

definition "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)"

lemma sup_apply [simp, code]: "(f \<squnion> g) x = f x \<squnion> g x"
  by (simp add: sup_fun_def)

instance
  by standard (simp_all add: le_fun_def)

end

instantiation "fun" :: (type, semilattice_inf) semilattice_inf
begin

definition "f \<sqinter> g = (\<lambda>x. f x \<sqinter> g x)"

lemma inf_apply [simp, code]: "(f \<sqinter> g) x = f x \<sqinter> g x"
  by (simp add: inf_fun_def)

instance by standard (simp_all add: le_fun_def)

end

instance "fun" :: (type, lattice) lattice ..

instance "fun" :: (type, distrib_lattice) distrib_lattice
  by standard (rule ext, simp add: sup_inf_distrib1)

instance "fun" :: (type, bounded_lattice) bounded_lattice ..

instantiation "fun" :: (type, uminus) uminus
begin

definition fun_Compl_def: "- A = (\<lambda>x. - A x)"

lemma uminus_apply [simp, code]: "(- A) x = - (A x)"
  by (simp add: fun_Compl_def)

instance ..

end

instantiation "fun" :: (type, minus) minus
begin

definition fun_diff_def: "A - B = (\<lambda>x. A x - B x)"

lemma minus_apply [simp, code]: "(A - B) x = A x - B x"
  by (simp add: fun_diff_def)

instance ..

end

end
