(*  Author:     Tobias Nipkow, TU München

A theory of types extended with a greatest and a least element.
Oriented towards numeric types, hence "\<infinity>" and "-\<infinity>".
*)

theory Extended
  imports Simps_Case_Conv
begin

datatype 'a extended = Fin 'a | Pinf (\<open>\<infinity>\<close>) | Minf (\<open>-\<infinity>\<close>)


instantiation extended :: (order)order
begin

fun less_eq_extended :: "'a extended \<Rightarrow> 'a extended \<Rightarrow> bool" where
"Fin x \<le> Fin y = (x \<le> y)" |
"_     \<le> Pinf  = True" |
"Minf  \<le> _     = True" |
"(_::'a extended) \<le> _     = False"

case_of_simps less_eq_extended_case: less_eq_extended.simps

definition less_extended :: "'a extended \<Rightarrow> 'a extended \<Rightarrow> bool" where
"((x::'a extended) < y) = (x \<le> y \<and> \<not> y \<le> x)"

instance
  by intro_classes (auto simp: less_extended_def less_eq_extended_case split: extended.splits)

end

instance extended :: (linorder)linorder
  by intro_classes (auto simp: less_eq_extended_case split:extended.splits)

lemma Minf_le[simp]: "Minf \<le> y"
by(cases y) auto
lemma le_Pinf[simp]: "x \<le> Pinf"
by(cases x) auto
lemma le_Minf[simp]: "x \<le> Minf \<longleftrightarrow> x = Minf"
by(cases x) auto
lemma Pinf_le[simp]: "Pinf \<le> x \<longleftrightarrow> x = Pinf"
by(cases x) auto

lemma less_extended_simps[simp]:
  "Fin x < Fin y = (x < y)"
  "Fin x < Pinf  = True"
  "Fin x < Minf  = False"
  "Pinf < h      = False"
  "Minf < Fin x  = True"
  "Minf < Pinf   = True"
  "l    < Minf   = False"
by (auto simp add: less_extended_def)

lemma min_extended_simps[simp]:
  "min (Fin x) (Fin y) = Fin(min x y)"
  "min xx      Pinf    = xx"
  "min xx      Minf    = Minf"
  "min Pinf    yy      = yy"
  "min Minf    yy      = Minf"
by (auto simp add: min_def)

lemma max_extended_simps[simp]:
  "max (Fin x) (Fin y) = Fin(max x y)"
  "max xx      Pinf    = Pinf"
  "max xx      Minf    = xx"
  "max Pinf    yy      = Pinf"
  "max Minf    yy      = yy"
by (auto simp add: max_def)


instantiation extended :: (zero)zero
begin
definition "0 = Fin(0::'a)"
instance ..
end

declare zero_extended_def[symmetric, code_post]

instantiation extended :: (one)one
begin
definition "1 = Fin(1::'a)"
instance ..
end

declare one_extended_def[symmetric, code_post]

instantiation extended :: (plus)plus
begin

text \<open>The following definition of of addition is totalized
to make it asociative and commutative. Normally the sum of plus and minus infinity is undefined.\<close>

fun plus_extended where
"Fin x + Fin y = Fin(x+y)" |
"Fin x + Pinf  = Pinf" |
"Pinf  + Fin x = Pinf" |
"Pinf  + Pinf  = Pinf" |
"Minf  + Fin y = Minf" |
"Fin x + Minf  = Minf" |
"Minf  + Minf  = Minf" |
"Minf  + Pinf  = Pinf" |
"Pinf  + Minf  = Pinf"

case_of_simps plus_case: plus_extended.simps

instance ..

end



instance extended :: (ab_semigroup_add)ab_semigroup_add
  by intro_classes (simp_all add: ac_simps plus_case split: extended.splits)

instance extended :: (ordered_ab_semigroup_add)ordered_ab_semigroup_add
  by intro_classes (auto simp: add_left_mono plus_case split: extended.splits)

instance extended :: (comm_monoid_add)comm_monoid_add
proof
  fix x :: "'a extended" show "0 + x = x" unfolding zero_extended_def by(cases x)auto
qed

instantiation extended :: (uminus)uminus
begin

fun uminus_extended where
"- (Fin x) = Fin (- x)" |
"- Pinf    = Minf" |
"- Minf    = Pinf"

instance ..

end


instantiation extended :: (ab_group_add)minus
begin
definition "x - y = x + -(y::'a extended)"
instance ..
end

lemma minus_extended_simps[simp]:
  "Fin x - Fin y = Fin(x - y)"
  "Fin x - Pinf  = Minf"
  "Fin x - Minf  = Pinf"
  "Pinf  - Fin y = Pinf"
  "Pinf  - Minf  = Pinf"
  "Minf  - Fin y = Minf"
  "Minf  - Pinf  = Minf"
  "Minf  - Minf  = Pinf"
  "Pinf  - Pinf  = Pinf"
by (simp_all add: minus_extended_def)


text\<open>Numerals:\<close>

instance extended :: ("{ab_semigroup_add,one}")numeral ..

lemma Fin_numeral[code_post]: "Fin(numeral w) = numeral w"
  apply (induct w rule: num_induct)
  apply (simp only: numeral_One one_extended_def)
  apply (simp only: numeral_inc one_extended_def plus_extended.simps(1)[symmetric])
  done

lemma Fin_neg_numeral[code_post]: "Fin (- numeral w) = - numeral w"
by (simp only: Fin_numeral uminus_extended.simps[symmetric])


instantiation extended :: (lattice)bounded_lattice
begin

definition "bot = Minf"
definition "top = Pinf"

fun inf_extended :: "'a extended \<Rightarrow> 'a extended \<Rightarrow> 'a extended" where
"inf_extended (Fin i) (Fin j) = Fin (inf i j)" |
"inf_extended a Minf = Minf" |
"inf_extended Minf a = Minf" |
"inf_extended Pinf a = a" |
"inf_extended a Pinf = a"

fun sup_extended :: "'a extended \<Rightarrow> 'a extended \<Rightarrow> 'a extended" where
"sup_extended (Fin i) (Fin j) = Fin (sup i j)" |
"sup_extended a Pinf = Pinf" |
"sup_extended Pinf a = Pinf" |
"sup_extended Minf a = a" |
"sup_extended a Minf = a"

case_of_simps inf_extended_case: inf_extended.simps
case_of_simps sup_extended_case: sup_extended.simps

instance
  by (intro_classes) (auto simp: inf_extended_case sup_extended_case less_eq_extended_case
    bot_extended_def top_extended_def split: extended.splits)
end

end

