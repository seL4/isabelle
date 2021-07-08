(*  Title:      HOL/Algebra/Group.thy
    Author:     Clemens Ballarin, started 4 February 2003

Based on work by Florian Kammueller, L C Paulson and Markus Wenzel.
With additional contributions from Martin Baillon and Paulo Emílio de Vilhena.
*)

theory Group
imports Complete_Lattice "HOL-Library.FuncSet"
begin

section \<open>Monoids and Groups\<close>

subsection \<open>Definitions\<close>

text \<open>
  Definitions follow @{cite "Jacobson:1985"}.
\<close>

record 'a monoid =  "'a partial_object" +
  mult    :: "['a, 'a] \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 70)
  one     :: 'a ("\<one>\<index>")

definition
  m_inv :: "('a, 'b) monoid_scheme => 'a => 'a" ("inv\<index> _" [81] 80)
  where "inv\<^bsub>G\<^esub> x = (THE y. y \<in> carrier G \<and> x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub> \<and> y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>)"

definition
  Units :: "_ => 'a set"
  \<comment> \<open>The set of invertible elements\<close>
  where "Units G = {y. y \<in> carrier G \<and> (\<exists>x \<in> carrier G. x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub> \<and> y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>)}"

locale monoid =
  fixes G (structure)
  assumes m_closed [intro, simp]:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier G"
      and m_assoc:
         "\<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk>
          \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
      and one_closed [intro, simp]: "\<one> \<in> carrier G"
      and l_one [simp]: "x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x"
      and r_one [simp]: "x \<in> carrier G \<Longrightarrow> x \<otimes> \<one> = x"

lemma monoidI:
  fixes G (structure)
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and r_one: "!!x. x \<in> carrier G ==> x \<otimes> \<one> = x"
  shows "monoid G"
  by (fast intro!: monoid.intro intro: assms)

lemma (in monoid) Units_closed [dest]:
  "x \<in> Units G ==> x \<in> carrier G"
  by (unfold Units_def) fast

lemma (in monoid) one_unique:
  assumes "u \<in> carrier G"
    and "\<And>x. x \<in> carrier G \<Longrightarrow> u \<otimes> x = x"
  shows "u = \<one>"
  using assms(2)[OF one_closed] r_one[OF assms(1)] by simp

lemma (in monoid) inv_unique:
  assumes eq: "y \<otimes> x = \<one>"  "x \<otimes> y' = \<one>"
    and G: "x \<in> carrier G"  "y \<in> carrier G"  "y' \<in> carrier G"
  shows "y = y'"
proof -
  from G eq have "y = y \<otimes> (x \<otimes> y')" by simp
  also from G have "... = (y \<otimes> x) \<otimes> y'" by (simp add: m_assoc)
  also from G eq have "... = y'" by simp
  finally show ?thesis .
qed

lemma (in monoid) Units_m_closed [simp, intro]:
  assumes x: "x \<in> Units G" and y: "y \<in> Units G"
  shows "x \<otimes> y \<in> Units G"
proof -
  from x obtain x' where x: "x \<in> carrier G" "x' \<in> carrier G" and xinv: "x \<otimes> x' = \<one>" "x' \<otimes> x = \<one>"
    unfolding Units_def by fast
  from y obtain y' where y: "y \<in> carrier G" "y' \<in> carrier G" and yinv: "y \<otimes> y' = \<one>" "y' \<otimes> y = \<one>"
    unfolding Units_def by fast
  from x y xinv yinv have "y' \<otimes> (x' \<otimes> x) \<otimes> y = \<one>" by simp
  moreover from x y xinv yinv have "x \<otimes> (y \<otimes> y') \<otimes> x' = \<one>" by simp
  moreover note x y
  ultimately show ?thesis unfolding Units_def
    by simp (metis m_assoc m_closed)
qed

lemma (in monoid) Units_one_closed [intro, simp]:
  "\<one> \<in> Units G"
  by (unfold Units_def) auto

lemma (in monoid) Units_inv_closed [intro, simp]:
  "x \<in> Units G ==> inv x \<in> carrier G"
  apply (simp add: Units_def m_inv_def)
  by (metis (mono_tags, lifting) inv_unique the_equality)

lemma (in monoid) Units_l_inv_ex:
  "x \<in> Units G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  by (unfold Units_def) auto

lemma (in monoid) Units_r_inv_ex:
  "x \<in> Units G ==> \<exists>y \<in> carrier G. x \<otimes> y = \<one>"
  by (unfold Units_def) auto

lemma (in monoid) Units_l_inv [simp]:
  "x \<in> Units G ==> inv x \<otimes> x = \<one>"
  apply (unfold Units_def m_inv_def, simp)
  by (metis (mono_tags, lifting) inv_unique the_equality)

lemma (in monoid) Units_r_inv [simp]:
  "x \<in> Units G ==> x \<otimes> inv x = \<one>"
  by (metis (full_types) Units_closed Units_inv_closed Units_l_inv Units_r_inv_ex inv_unique)

lemma (in monoid) inv_one [simp]:
  "inv \<one> = \<one>"
  by (metis Units_one_closed Units_r_inv l_one monoid.Units_inv_closed monoid_axioms)

lemma (in monoid) Units_inv_Units [intro, simp]:
  "x \<in> Units G ==> inv x \<in> Units G"
proof -
  assume x: "x \<in> Units G"
  show "inv x \<in> Units G"
    by (auto simp add: Units_def
      intro: Units_l_inv Units_r_inv x Units_closed [OF x])
qed

lemma (in monoid) Units_l_cancel [simp]:
  "[| x \<in> Units G; y \<in> carrier G; z \<in> carrier G |] ==>
   (x \<otimes> y = x \<otimes> z) = (y = z)"
proof
  assume eq: "x \<otimes> y = x \<otimes> z"
    and G: "x \<in> Units G"  "y \<in> carrier G"  "z \<in> carrier G"
  then have "(inv x \<otimes> x) \<otimes> y = (inv x \<otimes> x) \<otimes> z"
    by (simp add: m_assoc Units_closed del: Units_l_inv)
  with G show "y = z" by simp
next
  assume eq: "y = z"
    and G: "x \<in> Units G"  "y \<in> carrier G"  "z \<in> carrier G"
  then show "x \<otimes> y = x \<otimes> z" by simp
qed

lemma (in monoid) Units_inv_inv [simp]:
  "x \<in> Units G ==> inv (inv x) = x"
proof -
  assume x: "x \<in> Units G"
  then have "inv x \<otimes> inv (inv x) = inv x \<otimes> x" by simp
  with x show ?thesis by (simp add: Units_closed del: Units_l_inv Units_r_inv)
qed

lemma (in monoid) inv_inj_on_Units:
  "inj_on (m_inv G) (Units G)"
proof (rule inj_onI)
  fix x y
  assume G: "x \<in> Units G"  "y \<in> Units G" and eq: "inv x = inv y"
  then have "inv (inv x) = inv (inv y)" by simp
  with G show "x = y" by simp
qed

lemma (in monoid) Units_inv_comm:
  assumes inv: "x \<otimes> y = \<one>"
    and G: "x \<in> Units G"  "y \<in> Units G"
  shows "y \<otimes> x = \<one>"
proof -
  from G have "x \<otimes> y \<otimes> x = x \<otimes> \<one>" by (auto simp add: inv Units_closed)
  with G show ?thesis by (simp del: r_one add: m_assoc Units_closed)
qed

lemma (in monoid) carrier_not_empty: "carrier G \<noteq> {}"
by auto

(* Jacobson defines submonoid here. *)
(* Jacobson defines the order of a monoid here. *)


subsection \<open>Groups\<close>

text \<open>
  A group is a monoid all of whose elements are invertible.
\<close>

locale group = monoid +
  assumes Units: "carrier G <= Units G"

lemma (in group) is_group [iff]: "group G" by (rule group_axioms)

lemma (in group) is_monoid [iff]: "monoid G"
  by (rule monoid_axioms)

theorem groupI:
  fixes G (structure)
  assumes m_closed [simp]:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed [simp]: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one [simp]: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and l_inv_ex: "!!x. x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  shows "group G"
proof -
  have l_cancel [simp]:
    "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
    (x \<otimes> y = x \<otimes> z) = (y = z)"
  proof
    fix x y z
    assume eq: "x \<otimes> y = x \<otimes> z"
      and G: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
    with l_inv_ex obtain x_inv where xG: "x_inv \<in> carrier G"
      and l_inv: "x_inv \<otimes> x = \<one>" by fast
    from G eq xG have "(x_inv \<otimes> x) \<otimes> y = (x_inv \<otimes> x) \<otimes> z"
      by (simp add: m_assoc)
    with G show "y = z" by (simp add: l_inv)
  next
    fix x y z
    assume eq: "y = z"
      and G: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
    then show "x \<otimes> y = x \<otimes> z" by simp
  qed
  have r_one:
    "!!x. x \<in> carrier G ==> x \<otimes> \<one> = x"
  proof -
    fix x
    assume x: "x \<in> carrier G"
    with l_inv_ex obtain x_inv where xG: "x_inv \<in> carrier G"
      and l_inv: "x_inv \<otimes> x = \<one>" by fast
    from x xG have "x_inv \<otimes> (x \<otimes> \<one>) = x_inv \<otimes> x"
      by (simp add: m_assoc [symmetric] l_inv)
    with x xG show "x \<otimes> \<one> = x" by simp
  qed
  have inv_ex:
    "\<And>x. x \<in> carrier G \<Longrightarrow> \<exists>y \<in> carrier G. y \<otimes> x = \<one> \<and> x \<otimes> y = \<one>"
  proof -
    fix x
    assume x: "x \<in> carrier G"
    with l_inv_ex obtain y where y: "y \<in> carrier G"
      and l_inv: "y \<otimes> x = \<one>" by fast
    from x y have "y \<otimes> (x \<otimes> y) = y \<otimes> \<one>"
      by (simp add: m_assoc [symmetric] l_inv r_one)
    with x y have r_inv: "x \<otimes> y = \<one>"
      by simp
    from x y show "\<exists>y \<in> carrier G. y \<otimes> x = \<one> \<and> x \<otimes> y = \<one>"
      by (fast intro: l_inv r_inv)
  qed
  then have carrier_subset_Units: "carrier G \<subseteq> Units G"
    by (unfold Units_def) fast
  show ?thesis
    by standard (auto simp: r_one m_assoc carrier_subset_Units)
qed

lemma (in monoid) group_l_invI:
  assumes l_inv_ex:
    "!!x. x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  shows "group G"
  by (rule groupI) (auto intro: m_assoc l_inv_ex)

lemma (in group) Units_eq [simp]:
  "Units G = carrier G"
proof
  show "Units G \<subseteq> carrier G" by fast
next
  show "carrier G \<subseteq> Units G" by (rule Units)
qed

lemma (in group) inv_closed [intro, simp]:
  "x \<in> carrier G ==> inv x \<in> carrier G"
  using Units_inv_closed by simp

lemma (in group) l_inv_ex [simp]:
  "x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  using Units_l_inv_ex by simp

lemma (in group) r_inv_ex [simp]:
  "x \<in> carrier G ==> \<exists>y \<in> carrier G. x \<otimes> y = \<one>"
  using Units_r_inv_ex by simp

lemma (in group) l_inv [simp]:
  "x \<in> carrier G ==> inv x \<otimes> x = \<one>"
  by simp


subsection \<open>Cancellation Laws and Basic Properties\<close>

lemma (in group) inv_eq_1_iff [simp]:
  assumes "x \<in> carrier G" shows "inv\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub> \<longleftrightarrow> x = \<one>\<^bsub>G\<^esub>"
proof -
  have "x = \<one>" if "inv x = \<one>"
  proof -
    have "inv x \<otimes> x = \<one>"
      using assms l_inv by blast
    then show "x = \<one>"
      using that assms by simp
  qed
  then show ?thesis
    by auto
qed

lemma (in group) r_inv [simp]:
  "x \<in> carrier G ==> x \<otimes> inv x = \<one>"
  by simp

lemma (in group) right_cancel [simp]:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   (y \<otimes> x = z \<otimes> x) = (y = z)"
  by (metis inv_closed m_assoc r_inv r_one)

lemma (in group) inv_inv [simp]:
  "x \<in> carrier G ==> inv (inv x) = x"
  using Units_inv_inv by simp

lemma (in group) inv_inj:
  "inj_on (m_inv G) (carrier G)"
  using inv_inj_on_Units by simp

lemma (in group) inv_mult_group:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> inv (x \<otimes> y) = inv y \<otimes> inv x"
proof -
  assume G: "x \<in> carrier G"  "y \<in> carrier G"
  then have "inv (x \<otimes> y) \<otimes> (x \<otimes> y) = (inv y \<otimes> inv x) \<otimes> (x \<otimes> y)"
    by (simp add: m_assoc) (simp add: m_assoc [symmetric])
  with G show ?thesis by (simp del: l_inv Units_l_inv)
qed

lemma (in group) inv_comm:
  "[| x \<otimes> y = \<one>; x \<in> carrier G; y \<in> carrier G |] ==> y \<otimes> x = \<one>"
  by (rule Units_inv_comm) auto

lemma (in group) inv_equality:
     "[|y \<otimes> x = \<one>; x \<in> carrier G; y \<in> carrier G|] ==> inv x = y"
  using inv_unique r_inv by blast

lemma (in group) inv_solve_left:
  "\<lbrakk> a \<in> carrier G; b \<in> carrier G; c \<in> carrier G \<rbrakk> \<Longrightarrow> a = inv b \<otimes> c \<longleftrightarrow> c = b \<otimes> a"
  by (metis inv_equality l_inv_ex l_one m_assoc r_inv)

lemma (in group) inv_solve_left':
  "\<lbrakk> a \<in> carrier G; b \<in> carrier G; c \<in> carrier G \<rbrakk> \<Longrightarrow> inv b \<otimes> c = a \<longleftrightarrow> c = b \<otimes> a"
  by (metis inv_equality l_inv_ex l_one m_assoc r_inv)

lemma (in group) inv_solve_right:
  "\<lbrakk> a \<in> carrier G; b \<in> carrier G; c \<in> carrier G \<rbrakk> \<Longrightarrow> a = b \<otimes> inv c \<longleftrightarrow> b = a \<otimes> c"
  by (metis inv_equality l_inv_ex l_one m_assoc r_inv)

lemma (in group) inv_solve_right':
  "\<lbrakk>a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> b \<otimes> inv c = a \<longleftrightarrow> b = a \<otimes> c"
  by (auto simp: m_assoc)
  

subsection \<open>Power\<close>

consts
  pow :: "[('a, 'm) monoid_scheme, 'a, 'b::semiring_1] => 'a"  (infixr "[^]\<index>" 75)

overloading nat_pow == "pow :: [_, 'a, nat] => 'a"
begin
  definition "nat_pow G a n = rec_nat \<one>\<^bsub>G\<^esub> (%u b. b \<otimes>\<^bsub>G\<^esub> a) n"
end

lemma (in monoid) nat_pow_closed [intro, simp]:
  "x \<in> carrier G ==> x [^] (n::nat) \<in> carrier G"
  by (induct n) (simp_all add: nat_pow_def)

lemma (in monoid) nat_pow_0 [simp]:
  "x [^] (0::nat) = \<one>"
  by (simp add: nat_pow_def)

lemma (in monoid) nat_pow_Suc [simp]:
  "x [^] (Suc n) = x [^] n \<otimes> x"
  by (simp add: nat_pow_def)

lemma (in monoid) nat_pow_one [simp]:
  "\<one> [^] (n::nat) = \<one>"
  by (induct n) simp_all

lemma (in monoid) nat_pow_mult:
  "x \<in> carrier G ==> x [^] (n::nat) \<otimes> x [^] m = x [^] (n + m)"
  by (induct m) (simp_all add: m_assoc [THEN sym])

lemma (in monoid) nat_pow_comm:
  "x \<in> carrier G \<Longrightarrow> (x [^] (n::nat)) \<otimes> (x [^] (m :: nat)) = (x [^] m) \<otimes> (x [^] n)"
  using nat_pow_mult[of x n m] nat_pow_mult[of x m n] by (simp add: add.commute)

lemma (in monoid) nat_pow_Suc2:
  "x \<in> carrier G \<Longrightarrow> x [^] (Suc n) = x \<otimes> (x [^] n)"
  using nat_pow_mult[of x 1 n] Suc_eq_plus1[of n]
  by (metis One_nat_def Suc_eq_plus1_left l_one nat.rec(1) nat_pow_Suc nat_pow_def)

lemma (in monoid) nat_pow_pow:
  "x \<in> carrier G ==> (x [^] n) [^] m = x [^] (n * m::nat)"
  by (induct m) (simp, simp add: nat_pow_mult add.commute)

lemma (in monoid) nat_pow_consistent:
  "x [^] (n :: nat) = x [^]\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> n"
  unfolding nat_pow_def by simp

lemma nat_pow_0 [simp]: "x [^]\<^bsub>G\<^esub> (0::nat) = \<one>\<^bsub>G\<^esub>"
  by (simp add: nat_pow_def)

lemma nat_pow_Suc [simp]: "x [^]\<^bsub>G\<^esub> (Suc n) = (x [^]\<^bsub>G\<^esub> n)\<otimes>\<^bsub>G\<^esub> x"
  by (simp add: nat_pow_def)

lemma (in group) nat_pow_inv:
  assumes "x \<in> carrier G" shows "(inv x) [^] (i :: nat) = inv (x [^] i)"
proof (induction i)
  case 0 thus ?case by simp
next
  case (Suc i)
  have "(inv x) [^] Suc i = ((inv x) [^] i) \<otimes> inv x"
    by simp
  also have " ... = (inv (x [^] i)) \<otimes> inv x"
    by (simp add: Suc.IH Suc.prems)
  also have " ... = inv (x \<otimes> (x [^] i))"
    by (simp add: assms inv_mult_group)
  also have " ... = inv (x [^] (Suc i))"
    using assms nat_pow_Suc2 by auto
  finally show ?case .
qed

overloading int_pow == "pow :: [_, 'a, int] => 'a"
begin
  definition "int_pow G a z =
   (let p = rec_nat \<one>\<^bsub>G\<^esub> (%u b. b \<otimes>\<^bsub>G\<^esub> a)
    in if z < 0 then inv\<^bsub>G\<^esub> (p (nat (-z))) else p (nat z))"
end

lemma int_pow_int: "x [^]\<^bsub>G\<^esub> (int n) = x [^]\<^bsub>G\<^esub> n"
  by(simp add: int_pow_def nat_pow_def)

lemma pow_nat:
  assumes "i\<ge>0"
  shows "x [^]\<^bsub>G\<^esub> nat i = x [^]\<^bsub>G\<^esub> i"
proof (cases i rule: int_cases)
  case (nonneg n)
  then show ?thesis
    by (simp add: int_pow_int)
next
  case (neg n)
  then show ?thesis
    using assms by linarith
qed

lemma int_pow_0 [simp]: "x [^]\<^bsub>G\<^esub> (0::int) = \<one>\<^bsub>G\<^esub>"
  by (simp add: int_pow_def)

lemma int_pow_def2: "a [^]\<^bsub>G\<^esub> z =
   (if z < 0 then inv\<^bsub>G\<^esub> (a [^]\<^bsub>G\<^esub> (nat (-z))) else a [^]\<^bsub>G\<^esub> (nat z))"
  by (simp add: int_pow_def nat_pow_def)

lemma (in group) int_pow_one [simp]:
  "\<one> [^] (z::int) = \<one>"
  by (simp add: int_pow_def2)

lemma (in group) int_pow_closed [intro, simp]:
  "x \<in> carrier G ==> x [^] (i::int) \<in> carrier G"
  by (simp add: int_pow_def2)

lemma (in group) int_pow_1 [simp]:
  "x \<in> carrier G \<Longrightarrow> x [^] (1::int) = x"
  by (simp add: int_pow_def2)

lemma (in group) int_pow_neg:
  "x \<in> carrier G \<Longrightarrow> x [^] (-i::int) = inv (x [^] i)"
  by (simp add: int_pow_def2)

lemma (in group) int_pow_neg_int: "x \<in> carrier G \<Longrightarrow> x [^] -(int n) = inv (x [^] n)"
  by (simp add: int_pow_neg int_pow_int)

lemma (in group) int_pow_mult:
  assumes "x \<in> carrier G" shows "x [^] (i + j::int) = x [^] i \<otimes> x [^] j"
proof -
  have [simp]: "-i - j = -j - i" by simp
  show ?thesis
    by (auto simp: assms int_pow_def2 inv_solve_left inv_solve_right nat_add_distrib [symmetric] nat_pow_mult)
qed

lemma (in group) int_pow_inv:
  "x \<in> carrier G \<Longrightarrow> (inv x) [^] (i :: int) = inv (x [^] i)"
  by (metis int_pow_def2 nat_pow_inv)

lemma (in group) int_pow_pow:
  assumes "x \<in> carrier G"
  shows "(x [^] (n :: int)) [^] (m :: int) = x [^] (n * m :: int)"
proof (cases)
  assume n_ge: "n \<ge> 0" thus ?thesis
  proof (cases)
    assume m_ge: "m \<ge> 0" thus ?thesis
      using n_ge nat_pow_pow[OF assms, of "nat n" "nat m"] int_pow_def2 [where G=G]
      by (simp add: mult_less_0_iff nat_mult_distrib)
  next
    assume m_lt: "\<not> m \<ge> 0" 
    with n_ge show ?thesis
      apply (simp add: int_pow_def2 mult_less_0_iff)
      by (metis assms mult_minus_right n_ge nat_mult_distrib nat_pow_pow)
  qed
next
  assume n_lt: "\<not> n \<ge> 0" thus ?thesis
  proof (cases)
    assume m_ge: "m \<ge> 0" 
    have "inv x [^] (nat m * nat (- n)) = inv x [^] nat (- (m * n))"
      by (metis (full_types) m_ge mult_minus_right nat_mult_distrib)
    with m_ge n_lt show ?thesis
      by (simp add: int_pow_def2 mult_less_0_iff assms mult.commute nat_pow_inv nat_pow_pow)
  next
    assume m_lt: "\<not> m \<ge> 0" thus ?thesis
      using n_lt by (auto simp: int_pow_def2 mult_less_0_iff assms nat_mult_distrib_neg nat_pow_inv nat_pow_pow)
  qed
qed

lemma (in group) int_pow_diff:
  "x \<in> carrier G \<Longrightarrow> x [^] (n - m :: int) = x [^] n \<otimes> inv (x [^] m)"
  by(simp only: diff_conv_add_uminus int_pow_mult int_pow_neg)

lemma (in group) inj_on_multc: "c \<in> carrier G \<Longrightarrow> inj_on (\<lambda>x. x \<otimes> c) (carrier G)"
  by(simp add: inj_on_def)

lemma (in group) inj_on_cmult: "c \<in> carrier G \<Longrightarrow> inj_on (\<lambda>x. c \<otimes> x) (carrier G)"
  by(simp add: inj_on_def)


lemma (in monoid) group_commutes_pow:
  fixes n::nat
  shows "\<lbrakk>x \<otimes> y = y \<otimes> x; x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x [^] n \<otimes> y = y \<otimes> x [^] n"
  apply (induction n, auto)
  by (metis m_assoc nat_pow_closed)

lemma (in monoid) pow_mult_distrib:
  assumes eq: "x \<otimes> y = y \<otimes> x" and xy: "x \<in> carrier G" "y \<in> carrier G"
  shows "(x \<otimes> y) [^] (n::nat) = x [^] n \<otimes> y [^] n"
proof (induct n)
  case (Suc n)
  have "x \<otimes> (y [^] n \<otimes> y) = y [^] n \<otimes> x \<otimes> y"
    by (simp add: eq group_commutes_pow m_assoc xy)
  then show ?case
    using assms Suc.hyps m_assoc by auto
qed auto

lemma (in group) int_pow_mult_distrib:
  assumes eq: "x \<otimes> y = y \<otimes> x" and xy: "x \<in> carrier G" "y \<in> carrier G"
  shows "(x \<otimes> y) [^] (i::int) = x [^] i \<otimes> y [^] i"
proof (cases i rule: int_cases)
  case (nonneg n)
  then show ?thesis
    by (metis eq int_pow_int pow_mult_distrib xy)
next
  case (neg n)
  then show ?thesis
    unfolding neg
    apply (simp add: xy int_pow_neg_int del: of_nat_Suc)
    by (metis eq inv_mult_group local.nat_pow_Suc nat_pow_closed pow_mult_distrib xy)
qed

lemma (in group) pow_eq_div2:
  fixes m n :: nat
  assumes x_car: "x \<in> carrier G"
  assumes pow_eq: "x [^] m = x [^] n"
  shows "x [^] (m - n) = \<one>"
proof (cases "m < n")
  case False
  have "\<one> \<otimes> x [^] m = x [^] m" by (simp add: x_car)
  also have "\<dots> = x [^] (m - n) \<otimes> x [^] n"
    using False by (simp add: nat_pow_mult x_car)
  also have "\<dots> = x [^] (m - n) \<otimes> x [^] m"
    by (simp add: pow_eq)
  finally show ?thesis
    by (metis nat_pow_closed one_closed right_cancel x_car)
qed simp

subsection \<open>Submonoids\<close>

locale submonoid = \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  fixes H and G (structure)
  assumes subset: "H \<subseteq> carrier G"
    and m_closed [intro, simp]: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> H"
    and one_closed [simp]: "\<one> \<in> H"

lemma (in submonoid) is_submonoid: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  "submonoid H G" by (rule submonoid_axioms)

lemma (in submonoid) mem_carrier [simp]: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  "x \<in> H \<Longrightarrow> x \<in> carrier G"
  using subset by blast

lemma (in submonoid) submonoid_is_monoid [intro]: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "monoid G"
  shows "monoid (G\<lparr>carrier := H\<rparr>)"
proof -
  interpret monoid G by fact
  show ?thesis
    by (simp add: monoid_def m_assoc)
qed

lemma submonoid_nonempty: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  "~ submonoid {} G"
  by (blast dest: submonoid.one_closed)

lemma (in submonoid) finite_monoid_imp_card_positive: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  "finite (carrier G) ==> 0 < card H"
proof (rule classical)
  assume "finite (carrier G)" and a: "~ 0 < card H"
  then have "finite H" by (blast intro: finite_subset [OF subset])
  with is_submonoid a have "submonoid {} G" by simp
  with submonoid_nonempty show ?thesis by contradiction
qed


lemma (in monoid) monoid_incl_imp_submonoid : \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "H \<subseteq> carrier G"
and "monoid (G\<lparr>carrier := H\<rparr>)"
shows "submonoid H G"
proof (intro submonoid.intro[OF assms(1)])
  have ab_eq : "\<And> a b. a \<in> H \<Longrightarrow> b \<in> H \<Longrightarrow> a \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> b = a \<otimes> b" using assms by simp
  have "\<And>a b. a \<in> H \<Longrightarrow> b \<in> H \<Longrightarrow> a \<otimes> b \<in> carrier (G\<lparr>carrier := H\<rparr>) "
    using assms ab_eq unfolding group_def using monoid.m_closed by fastforce
  thus "\<And>a b. a \<in> H \<Longrightarrow> b \<in> H \<Longrightarrow> a \<otimes> b \<in> H" by simp
  show "\<one> \<in> H " using monoid.one_closed[OF assms(2)] assms by simp
qed

lemma (in monoid) inv_unique': \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "x \<in> carrier G" "y \<in> carrier G"
  shows "\<lbrakk> x \<otimes> y = \<one>; y \<otimes> x = \<one> \<rbrakk> \<Longrightarrow> y = inv x"
proof -
  assume "x \<otimes> y = \<one>" and l_inv: "y \<otimes> x = \<one>"
  hence unit: "x \<in> Units G"
    using assms unfolding Units_def by auto
  show "y = inv x"
    using inv_unique[OF l_inv Units_r_inv[OF unit] assms Units_inv_closed[OF unit]] .
qed

lemma (in monoid) m_inv_monoid_consistent: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "x \<in> Units (G \<lparr> carrier := H \<rparr>)" and "submonoid H G"
  shows "inv\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> x = inv x"
proof -
  have monoid: "monoid (G \<lparr> carrier := H \<rparr>)"
    using submonoid.submonoid_is_monoid[OF assms(2) monoid_axioms] .
  obtain y where y: "y \<in> H" "x \<otimes> y = \<one>" "y \<otimes> x = \<one>"
    using assms(1) unfolding Units_def by auto
  have x: "x \<in> H" and in_carrier: "x \<in> carrier G" "y \<in> carrier G"
    using y(1) submonoid.subset[OF assms(2)] assms(1) unfolding Units_def by auto
  show ?thesis
    using monoid.inv_unique'[OF monoid, of x y] x y
    using inv_unique'[OF in_carrier y(2-3)] by auto
qed

subsection \<open>Subgroups\<close>

locale subgroup =
  fixes H and G (structure)
  assumes subset: "H \<subseteq> carrier G"
    and m_closed [intro, simp]: "\<lbrakk>x \<in> H; y \<in> H\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> H"
    and one_closed [simp]: "\<one> \<in> H"
    and m_inv_closed [intro,simp]: "x \<in> H \<Longrightarrow> inv x \<in> H"

lemma (in subgroup) is_subgroup:
  "subgroup H G" by (rule subgroup_axioms)

declare (in subgroup) group.intro [intro]

lemma (in subgroup) mem_carrier [simp]:
  "x \<in> H \<Longrightarrow> x \<in> carrier G"
  using subset by blast

lemma (in subgroup) subgroup_is_group [intro]:
  assumes "group G"
  shows "group (G\<lparr>carrier := H\<rparr>)"
proof -
  interpret group G by fact
  have "Group.monoid (G\<lparr>carrier := H\<rparr>)"
    by (simp add: monoid_axioms submonoid.intro submonoid.submonoid_is_monoid subset)
  then show ?thesis
    by (rule monoid.group_l_invI) (auto intro: l_inv mem_carrier)
qed

lemma subgroup_is_submonoid:
  assumes "subgroup H G" shows "submonoid H G"
  using assms by (auto intro: submonoid.intro simp add: subgroup_def)

lemma (in group) subgroup_Units:
  assumes "subgroup H G" shows "H \<subseteq> Units (G \<lparr> carrier := H \<rparr>)"
  using group.Units[OF subgroup.subgroup_is_group[OF assms group_axioms]] by simp

lemma (in group) m_inv_consistent [simp]:
  assumes "subgroup H G" "x \<in> H"
  shows "inv\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> x = inv x"
  using assms m_inv_monoid_consistent[OF _ subgroup_is_submonoid] subgroup_Units[of H] by auto

lemma (in group) int_pow_consistent: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "subgroup H G" "x \<in> H"
  shows "x [^] (n :: int) = x [^]\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> n"
proof (cases)
  assume ge: "n \<ge> 0"
  hence "x [^] n = x [^] (nat n)"
    using int_pow_def2 [of G] by auto
  also have " ... = x [^]\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> (nat n)"
    using nat_pow_consistent by simp
  also have " ... = x [^]\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> n"
    by (metis ge int_nat_eq int_pow_int)
  finally show ?thesis .
next
  assume "\<not> n \<ge> 0" hence lt: "n < 0" by simp
  hence "x [^] n = inv (x [^] (nat (- n)))"
    using int_pow_def2 [of G] by auto
  also have " ... = (inv x) [^] (nat (- n))"
    by (metis assms nat_pow_inv subgroup.mem_carrier)
  also have " ... = (inv\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> x) [^]\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> (nat (- n))"
    using m_inv_consistent[OF assms] nat_pow_consistent by auto
  also have " ... = inv\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> (x [^]\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> (nat (- n)))"
    using group.nat_pow_inv[OF subgroup.subgroup_is_group[OF assms(1) is_group]] assms(2) by auto
  also have " ... = x [^]\<^bsub>(G \<lparr> carrier := H \<rparr>)\<^esub> n"
    by (simp add: int_pow_def2 lt)
  finally show ?thesis .
qed

text \<open>
  Since \<^term>\<open>H\<close> is nonempty, it contains some element \<^term>\<open>x\<close>.  Since
  it is closed under inverse, it contains \<open>inv x\<close>.  Since
  it is closed under product, it contains \<open>x \<otimes> inv x = \<one>\<close>.
\<close>

lemma (in group) one_in_subset:
  "[| H \<subseteq> carrier G; H \<noteq> {}; \<forall>a \<in> H. inv a \<in> H; \<forall>a\<in>H. \<forall>b\<in>H. a \<otimes> b \<in> H |]
   ==> \<one> \<in> H"
by force

text \<open>A characterization of subgroups: closed, non-empty subset.\<close>

lemma (in group) subgroupI:
  assumes subset: "H \<subseteq> carrier G" and non_empty: "H \<noteq> {}"
    and inv: "!!a. a \<in> H \<Longrightarrow> inv a \<in> H"
    and mult: "!!a b. \<lbrakk>a \<in> H; b \<in> H\<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
  shows "subgroup H G"
proof (simp add: subgroup_def assms)
  show "\<one> \<in> H" by (rule one_in_subset) (auto simp only: assms)
qed

lemma (in group) subgroupE:
  assumes "subgroup H G"
  shows "H \<subseteq> carrier G"
    and "H \<noteq> {}"
    and "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
    and "\<And>a b. \<lbrakk> a \<in> H; b \<in> H \<rbrakk> \<Longrightarrow> a \<otimes> b \<in> H"
  using assms unfolding subgroup_def[of H G] by auto

declare monoid.one_closed [iff] group.inv_closed [simp]
  monoid.l_one [simp] monoid.r_one [simp] group.inv_inv [simp]

lemma subgroup_nonempty:
  "\<not> subgroup {} G"
  by (blast dest: subgroup.one_closed)

lemma (in subgroup) finite_imp_card_positive: "finite (carrier G) \<Longrightarrow> 0 < card H"
  using subset one_closed card_gt_0_iff finite_subset by blast

lemma (in subgroup) subgroup_is_submonoid : \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  "submonoid H G"
  by (simp add: submonoid.intro subset)

lemma (in group) submonoid_subgroupI : \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "submonoid H G"
    and "\<And>a. a \<in> H \<Longrightarrow> inv a \<in> H"
  shows "subgroup H G"
  by (metis assms subgroup_def submonoid_def)

lemma (in group) group_incl_imp_subgroup: \<^marker>\<open>contributor \<open>Martin Baillon\<close>\<close>
  assumes "H \<subseteq> carrier G"
    and "group (G\<lparr>carrier := H\<rparr>)"
  shows "subgroup H G"
proof (intro submonoid_subgroupI[OF monoid_incl_imp_submonoid[OF assms(1)]])
  show "monoid (G\<lparr>carrier := H\<rparr>)" using group_def assms by blast
  have ab_eq : "\<And> a b. a \<in> H \<Longrightarrow> b \<in> H \<Longrightarrow> a \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> b = a \<otimes> b" using assms by simp
  fix a  assume aH : "a \<in> H"
  have " inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> a \<in> carrier G"
    using assms aH group.inv_closed[OF assms(2)] by auto
  moreover have "\<one>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> = \<one>" using assms monoid.one_closed ab_eq one_def by simp
  hence "a \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> a= \<one>"
    using assms ab_eq aH  group.r_inv[OF assms(2)] by simp
  hence "a \<otimes> inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> a= \<one>"
    using aH assms group.inv_closed[OF assms(2)] ab_eq by simp
  ultimately have "inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> a = inv a"
    by (metis aH assms(1) contra_subsetD group.inv_inv is_group local.inv_equality)
  moreover have "inv\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> a \<in> H" 
    using aH group.inv_closed[OF assms(2)] by auto
  ultimately show "inv a \<in> H" by auto
qed


subsection \<open>Direct Products\<close>

definition
  DirProd :: "_ \<Rightarrow> _ \<Rightarrow> ('a \<times> 'b) monoid" (infixr "\<times>\<times>" 80) where
  "G \<times>\<times> H =
    \<lparr>carrier = carrier G \<times> carrier H,
     mult = (\<lambda>(g, h) (g', h'). (g \<otimes>\<^bsub>G\<^esub> g', h \<otimes>\<^bsub>H\<^esub> h')),
     one = (\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>)\<rparr>"

lemma DirProd_monoid:
  assumes "monoid G" and "monoid H"
  shows "monoid (G \<times>\<times> H)"
proof -
  interpret G: monoid G by fact
  interpret H: monoid H by fact
  from assms
  show ?thesis by (unfold monoid_def DirProd_def, auto)
qed


text\<open>Does not use the previous result because it's easier just to use auto.\<close>
lemma DirProd_group:
  assumes "group G" and "group H"
  shows "group (G \<times>\<times> H)"
proof -
  interpret G: group G by fact
  interpret H: group H by fact
  show ?thesis by (rule groupI)
     (auto intro: G.m_assoc H.m_assoc G.l_inv H.l_inv
           simp add: DirProd_def)
qed

lemma carrier_DirProd [simp]: "carrier (G \<times>\<times> H) = carrier G \<times> carrier H"
  by (simp add: DirProd_def)

lemma one_DirProd [simp]: "\<one>\<^bsub>G \<times>\<times> H\<^esub> = (\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>)"
  by (simp add: DirProd_def)

lemma mult_DirProd [simp]: "(g, h) \<otimes>\<^bsub>(G \<times>\<times> H)\<^esub> (g', h') = (g \<otimes>\<^bsub>G\<^esub> g', h \<otimes>\<^bsub>H\<^esub> h')"
  by (simp add: DirProd_def)

lemma mult_DirProd': "x \<otimes>\<^bsub>(G \<times>\<times> H)\<^esub> y = (fst x \<otimes>\<^bsub>G\<^esub> fst y, snd x \<otimes>\<^bsub>H\<^esub> snd y)"
  by (subst mult_DirProd [symmetric]) simp

lemma DirProd_assoc: "(G \<times>\<times> H \<times>\<times> I) = (G \<times>\<times> (H \<times>\<times> I))"
  by auto

lemma inv_DirProd [simp]:
  assumes "group G" and "group H"
  assumes g: "g \<in> carrier G"
      and h: "h \<in> carrier H"
  shows "m_inv (G \<times>\<times> H) (g, h) = (inv\<^bsub>G\<^esub> g, inv\<^bsub>H\<^esub> h)"
proof -
  interpret G: group G by fact
  interpret H: group H by fact
  interpret Prod: group "G \<times>\<times> H"
    by (auto intro: DirProd_group group.intro group.axioms assms)
  show ?thesis by (simp add: Prod.inv_equality g h)
qed

lemma DirProd_subgroups :
  assumes "group G"
    and "subgroup H G"
    and "group K"
    and "subgroup I K"
  shows "subgroup (H \<times> I) (G \<times>\<times> K)"
proof (intro group.group_incl_imp_subgroup[OF DirProd_group[OF assms(1)assms(3)]])
  have "H \<subseteq> carrier G" "I \<subseteq> carrier K" using subgroup.subset assms by blast+
  thus "(H \<times> I) \<subseteq> carrier (G \<times>\<times> K)" unfolding DirProd_def by auto
  have "Group.group ((G\<lparr>carrier := H\<rparr>) \<times>\<times> (K\<lparr>carrier := I\<rparr>))"
    using DirProd_group[OF subgroup.subgroup_is_group[OF assms(2)assms(1)]
        subgroup.subgroup_is_group[OF assms(4)assms(3)]].
  moreover have "((G\<lparr>carrier := H\<rparr>) \<times>\<times> (K\<lparr>carrier := I\<rparr>)) = ((G \<times>\<times> K)\<lparr>carrier := H \<times> I\<rparr>)"
    unfolding DirProd_def using assms by simp
  ultimately show "Group.group ((G \<times>\<times> K)\<lparr>carrier := H \<times> I\<rparr>)" by simp
qed

subsection \<open>Homomorphisms (mono and epi) and Isomorphisms\<close>

definition
  hom :: "_ => _ => ('a => 'b) set" where
  "hom G H =
    {h. h \<in> carrier G \<rightarrow> carrier H \<and>
      (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y)}"

lemma homI:
  "\<lbrakk>\<And>x. x \<in> carrier G \<Longrightarrow> h x \<in> carrier H;
    \<And>x y. \<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y\<rbrakk> \<Longrightarrow> h \<in> hom G H"
  by (auto simp: hom_def)

lemma hom_carrier: "h \<in> hom G H \<Longrightarrow> h ` carrier G \<subseteq> carrier H"
  by (auto simp: hom_def)

lemma hom_in_carrier: "\<lbrakk>h \<in> hom G H; x \<in> carrier G\<rbrakk> \<Longrightarrow> h x \<in> carrier H"
  by (auto simp: hom_def)

lemma hom_compose:
  "\<lbrakk> f \<in> hom G H; g \<in> hom H I \<rbrakk> \<Longrightarrow> g \<circ> f \<in> hom G I"
  unfolding hom_def by (auto simp add: Pi_iff)

lemma (in group) hom_restrict:
  assumes "h \<in> hom G H" and "\<And>g. g \<in> carrier G \<Longrightarrow> h g = t g" shows "t \<in> hom G H"
  using assms unfolding hom_def by (auto simp add: Pi_iff)

lemma (in group) hom_compose:
  "[|h \<in> hom G H; i \<in> hom H I|] ==> compose (carrier G) i h \<in> hom G I"
by (fastforce simp add: hom_def compose_def)

lemma (in group) restrict_hom_iff [simp]:
  "(\<lambda>x. if x \<in> carrier G then f x else g x) \<in> hom G H \<longleftrightarrow> f \<in> hom G H"
  by (simp add: hom_def Pi_iff)

definition iso :: "_ => _ => ('a => 'b) set"
  where "iso G H = {h. h \<in> hom G H \<and> bij_betw h (carrier G) (carrier H)}"

definition is_iso :: "_ \<Rightarrow> _ \<Rightarrow> bool" (infixr "\<cong>" 60)
  where "G \<cong> H = (iso G H  \<noteq> {})"

definition mon where "mon G H = {f \<in> hom G H. inj_on f (carrier G)}"

definition epi where "epi G H = {f \<in> hom G H. f ` (carrier G) = carrier H}"

lemma isoI:
  "\<lbrakk>h \<in> hom G H; bij_betw h (carrier G) (carrier H)\<rbrakk> \<Longrightarrow> h \<in> iso G H"
  by (auto simp: iso_def)

lemma is_isoI: "h \<in> iso G H \<Longrightarrow> G \<cong> H"
  using is_iso_def by auto

lemma epi_iff_subset:
   "f \<in> epi G G' \<longleftrightarrow> f \<in> hom G G' \<and> carrier G' \<subseteq> f ` carrier G"
  by (auto simp: epi_def hom_def)

lemma iso_iff_mon_epi: "f \<in> iso G H \<longleftrightarrow> f \<in> mon G H \<and> f \<in> epi G H"
  by (auto simp: iso_def mon_def epi_def bij_betw_def)

lemma iso_set_refl: "(\<lambda>x. x) \<in> iso G G"
  by (simp add: iso_def hom_def inj_on_def bij_betw_def Pi_def)

lemma id_iso: "id \<in> iso G G"
  by (simp add: iso_def hom_def inj_on_def bij_betw_def Pi_def)

corollary iso_refl [simp]: "G \<cong> G"
  using iso_set_refl unfolding is_iso_def by auto

lemma iso_iff:
   "h \<in> iso G H \<longleftrightarrow> h \<in> hom G H \<and> h ` (carrier G) = carrier H \<and> inj_on h (carrier G)"
  by (auto simp: iso_def hom_def bij_betw_def)

lemma iso_imp_homomorphism:
   "h \<in> iso G H \<Longrightarrow> h \<in> hom G H"
  by (simp add: iso_iff)

lemma trivial_hom:
   "group H \<Longrightarrow> (\<lambda>x. one H) \<in> hom G H"
  by (auto simp: hom_def Group.group_def)

lemma (in group) hom_eq:
  assumes "f \<in> hom G H" "\<And>x. x \<in> carrier G \<Longrightarrow> f' x = f x"
  shows "f' \<in> hom G H"
  using assms by (auto simp: hom_def)

lemma (in group) iso_eq:
  assumes "f \<in> iso G H" "\<And>x. x \<in> carrier G \<Longrightarrow> f' x = f x"
  shows "f' \<in> iso G H"
  using assms  by (fastforce simp: iso_def inj_on_def bij_betw_def hom_eq image_iff)

lemma (in group) iso_set_sym:
  assumes "h \<in> iso G H"
  shows "inv_into (carrier G) h \<in> iso H G"
proof -
  have h: "h \<in> hom G H" "bij_betw h (carrier G) (carrier H)"
    using assms by (auto simp add: iso_def bij_betw_inv_into)
  then have HG: "bij_betw (inv_into (carrier G) h) (carrier H) (carrier G)"
    by (simp add: bij_betw_inv_into)
  have "inv_into (carrier G) h \<in> hom H G"
    unfolding hom_def
  proof safe
    show *: "\<And>x. x \<in> carrier H \<Longrightarrow> inv_into (carrier G) h x \<in> carrier G"
      by (meson HG bij_betwE)
    show "inv_into (carrier G) h (x \<otimes>\<^bsub>H\<^esub> y) = inv_into (carrier G) h x \<otimes> inv_into (carrier G) h y"
      if "x \<in> carrier H" "y \<in> carrier H" for x y
    proof (rule inv_into_f_eq)
      show "inj_on h (carrier G)"
        using bij_betw_def h(2) by blast
      show "inv_into (carrier G) h x \<otimes> inv_into (carrier G) h y \<in> carrier G"
        by (simp add: * that)
      show "h (inv_into (carrier G) h x \<otimes> inv_into (carrier G) h y) = x \<otimes>\<^bsub>H\<^esub> y"
        using h bij_betw_inv_into_right [of h] unfolding hom_def by (simp add: "*" that)
    qed
  qed
  then show ?thesis
    by (simp add: Group.iso_def bij_betw_inv_into h)
qed

corollary (in group) iso_sym: "G \<cong> H \<Longrightarrow> H \<cong> G"
  using iso_set_sym unfolding is_iso_def by auto

lemma iso_set_trans:
  "\<lbrakk>h \<in> Group.iso G H; i \<in> Group.iso H I\<rbrakk> \<Longrightarrow> i \<circ> h \<in> Group.iso G I"
  by (force simp: iso_def hom_compose intro: bij_betw_trans)

corollary iso_trans [trans]: "\<lbrakk>G \<cong> H ; H \<cong> I\<rbrakk> \<Longrightarrow> G \<cong> I"
  using iso_set_trans unfolding is_iso_def by blast

lemma iso_same_card: "G \<cong> H \<Longrightarrow> card (carrier G) = card (carrier H)"
  using bij_betw_same_card  unfolding is_iso_def iso_def by auto

lemma iso_finite: "G \<cong> H \<Longrightarrow> finite(carrier G) \<longleftrightarrow> finite(carrier H)"
  by (auto simp: is_iso_def iso_def bij_betw_finite)

lemma mon_compose:
   "\<lbrakk>f \<in> mon G H; g \<in> mon H K\<rbrakk> \<Longrightarrow> (g \<circ> f) \<in> mon G K"
  by (auto simp: mon_def intro: hom_compose comp_inj_on inj_on_subset [OF _ hom_carrier])

lemma mon_compose_rev:
   "\<lbrakk>f \<in> hom G H; g \<in> hom H K; (g \<circ> f) \<in> mon G K\<rbrakk> \<Longrightarrow> f \<in> mon G H"
  using inj_on_imageI2 by (auto simp: mon_def)

lemma epi_compose:
   "\<lbrakk>f \<in> epi G H; g \<in> epi H K\<rbrakk> \<Longrightarrow> (g \<circ> f) \<in> epi G K"
  using hom_compose by (force simp: epi_def hom_compose simp flip: image_image)

lemma epi_compose_rev:
   "\<lbrakk>f \<in> hom G H; g \<in> hom H K; (g \<circ> f) \<in> epi G K\<rbrakk> \<Longrightarrow> g \<in> epi H K"
  by (fastforce simp: epi_def hom_def Pi_iff image_def set_eq_iff)

lemma iso_compose_rev:
   "\<lbrakk>f \<in> hom G H; g \<in> hom H K; (g \<circ> f) \<in> iso G K\<rbrakk> \<Longrightarrow> f \<in> mon G H \<and> g \<in> epi H K"
  unfolding iso_iff_mon_epi using mon_compose_rev epi_compose_rev by blast

lemma epi_iso_compose_rev:
  assumes "f \<in> epi G H" "g \<in> hom H K" "(g \<circ> f) \<in> iso G K"
  shows "f \<in> iso G H \<and> g \<in> iso H K"
proof
  show "f \<in> iso G H"
    by (metis (no_types, lifting) assms epi_def iso_compose_rev iso_iff_mon_epi mem_Collect_eq)
  then have "f \<in> hom G H \<and> bij_betw f (carrier G) (carrier H)"
    using Group.iso_def \<open>f \<in> Group.iso G H\<close> by blast
  then have "bij_betw g (carrier H) (carrier K)"
    using Group.iso_def assms(3) bij_betw_comp_iff by blast
  then show "g \<in> iso H K"
    using Group.iso_def assms(2) by blast
qed

lemma mon_left_invertible:
   "\<lbrakk>f \<in> hom G H; \<And>x. x \<in> carrier G \<Longrightarrow> g(f x) = x\<rbrakk> \<Longrightarrow> f \<in> mon G H"
  by (simp add: mon_def inj_on_def) metis

lemma epi_right_invertible:
   "\<lbrakk>g \<in> hom H G; f \<in> carrier G \<rightarrow> carrier H; \<And>x. x \<in> carrier G \<Longrightarrow> g(f x) = x\<rbrakk> \<Longrightarrow> g \<in> epi H G"
  by (force simp: Pi_iff epi_iff_subset image_subset_iff_funcset subset_iff)

lemma (in monoid) hom_imp_img_monoid: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> hom G H"
  shows "monoid (H \<lparr> carrier := h ` (carrier G), one := h \<one>\<^bsub>G\<^esub> \<rparr>)" (is "monoid ?h_img")
proof (rule monoidI)
  show "\<one>\<^bsub>?h_img\<^esub> \<in> carrier ?h_img"
    by auto
next
  fix x y z assume "x \<in> carrier ?h_img" "y \<in> carrier ?h_img" "z \<in> carrier ?h_img"
  then obtain g1 g2 g3
    where g1: "g1 \<in> carrier G" "x = h g1"
      and g2: "g2 \<in> carrier G" "y = h g2"
      and g3: "g3 \<in> carrier G" "z = h g3"
    using image_iff[where ?f = h and ?A = "carrier G"] by auto
  have aux_lemma:
    "\<And>a b. \<lbrakk> a \<in> carrier G; b \<in> carrier G \<rbrakk> \<Longrightarrow> h a \<otimes>\<^bsub>(?h_img)\<^esub> h b = h (a \<otimes> b)"
    using assms unfolding hom_def by auto

  show "x \<otimes>\<^bsub>(?h_img)\<^esub> \<one>\<^bsub>(?h_img)\<^esub> = x"
    using aux_lemma[OF g1(1) one_closed] g1(2) r_one[OF g1(1)] by simp

  show "\<one>\<^bsub>(?h_img)\<^esub> \<otimes>\<^bsub>(?h_img)\<^esub> x = x"
    using aux_lemma[OF one_closed g1(1)] g1(2) l_one[OF g1(1)] by simp

  have "x \<otimes>\<^bsub>(?h_img)\<^esub> y = h (g1 \<otimes> g2)"
    using aux_lemma g1 g2 by auto
  thus "x \<otimes>\<^bsub>(?h_img)\<^esub> y \<in> carrier ?h_img"
    using g1(1) g2(1) by simp

  have "(x \<otimes>\<^bsub>(?h_img)\<^esub> y) \<otimes>\<^bsub>(?h_img)\<^esub> z = h ((g1 \<otimes> g2) \<otimes> g3)"
    using aux_lemma g1 g2 g3 by auto
  also have " ... = h (g1 \<otimes> (g2 \<otimes> g3))"
    using m_assoc[OF g1(1) g2(1) g3(1)] by simp
  also have " ... = x \<otimes>\<^bsub>(?h_img)\<^esub> (y \<otimes>\<^bsub>(?h_img)\<^esub> z)"
    using aux_lemma g1 g2 g3 by auto
  finally show "(x \<otimes>\<^bsub>(?h_img)\<^esub> y) \<otimes>\<^bsub>(?h_img)\<^esub> z = x \<otimes>\<^bsub>(?h_img)\<^esub> (y \<otimes>\<^bsub>(?h_img)\<^esub> z)" .
qed

lemma (in group) hom_imp_img_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> hom G H"
  shows "group (H \<lparr> carrier := h ` (carrier G), one := h \<one>\<^bsub>G\<^esub> \<rparr>)" (is "group ?h_img")
proof -
  interpret monoid ?h_img
    using hom_imp_img_monoid[OF assms] .

  show ?thesis
  proof (unfold_locales)
    show "carrier ?h_img \<subseteq> Units ?h_img"
    proof (auto simp add: Units_def)
      have aux_lemma:
        "\<And>g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow> h g1 \<otimes>\<^bsub>H\<^esub> h g2 = h (g1 \<otimes> g2)"
        using assms unfolding hom_def by auto

      fix g1 assume g1: "g1 \<in> carrier G"
      thus "\<exists>g2 \<in> carrier G. (h g2) \<otimes>\<^bsub>H\<^esub> (h g1) = h \<one> \<and> (h g1) \<otimes>\<^bsub>H\<^esub> (h g2) = h \<one>"
        using aux_lemma[OF g1 inv_closed[OF g1]]
              aux_lemma[OF inv_closed[OF g1] g1]
              inv_closed by auto
    qed
  qed
qed

lemma (in group) iso_imp_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "G \<cong> H" and "monoid H"
  shows "group H"
proof -
  obtain \<phi> where phi: "\<phi> \<in> iso G H" "inv_into (carrier G) \<phi> \<in> iso H G"
    using iso_set_sym assms unfolding is_iso_def by blast
  define \<psi> where psi_def: "\<psi> = inv_into (carrier G) \<phi>"

  have surj: "\<phi> ` (carrier G) = (carrier H)" "\<psi> ` (carrier H) = (carrier G)"
   and inj: "inj_on \<phi> (carrier G)" "inj_on \<psi> (carrier H)"
   and phi_hom: "\<And>g1 g2. \<lbrakk> g1 \<in> carrier G; g2 \<in> carrier G \<rbrakk> \<Longrightarrow> \<phi> (g1 \<otimes> g2) = (\<phi> g1) \<otimes>\<^bsub>H\<^esub> (\<phi> g2)"
   and psi_hom: "\<And>h1 h2. \<lbrakk> h1 \<in> carrier H; h2 \<in> carrier H \<rbrakk> \<Longrightarrow> \<psi> (h1 \<otimes>\<^bsub>H\<^esub> h2) = (\<psi> h1) \<otimes> (\<psi> h2)"
   using phi psi_def unfolding iso_def bij_betw_def hom_def by auto

  have phi_one: "\<phi> \<one> = \<one>\<^bsub>H\<^esub>"
  proof -
    have "(\<phi> \<one>) \<otimes>\<^bsub>H\<^esub> \<one>\<^bsub>H\<^esub> = (\<phi> \<one>) \<otimes>\<^bsub>H\<^esub> (\<phi> \<one>)"
      by (metis assms(2) image_eqI monoid.r_one one_closed phi_hom r_one surj(1))
    thus ?thesis
      by (metis (no_types, opaque_lifting) Units_eq Units_one_closed assms(2) f_inv_into_f imageI
          monoid.l_one monoid.one_closed phi_hom psi_def r_one surj)
  qed

  have "carrier H \<subseteq> Units H"
  proof
    fix h assume h: "h \<in> carrier H"
    let ?inv_h = "\<phi> (inv (\<psi> h))"
    have "h \<otimes>\<^bsub>H\<^esub> ?inv_h = \<phi> (\<psi> h) \<otimes>\<^bsub>H\<^esub> ?inv_h"
      by (simp add: f_inv_into_f h psi_def surj(1))
    also have " ... = \<phi> ((\<psi> h) \<otimes> inv (\<psi> h))"
      by (metis h imageI inv_closed phi_hom surj(2))
    also have " ... = \<phi> \<one>"
      by (simp add: h inv_into_into psi_def surj(1))
    finally have 1: "h \<otimes>\<^bsub>H\<^esub> ?inv_h = \<one>\<^bsub>H\<^esub>"
      using phi_one by simp

    have "?inv_h \<otimes>\<^bsub>H\<^esub> h = ?inv_h \<otimes>\<^bsub>H\<^esub> \<phi> (\<psi> h)"
      by (simp add: f_inv_into_f h psi_def surj(1))
    also have " ... = \<phi> (inv (\<psi> h) \<otimes> (\<psi> h))"
      by (metis h imageI inv_closed phi_hom surj(2))
    also have " ... = \<phi> \<one>"
      by (simp add: h inv_into_into psi_def surj(1))
    finally have 2: "?inv_h \<otimes>\<^bsub>H\<^esub> h = \<one>\<^bsub>H\<^esub>"
      using phi_one by simp

    thus "h \<in> Units H" unfolding Units_def using 1 2 h surj by fastforce
  qed
  thus ?thesis unfolding group_def group_axioms_def using assms(2) by simp
qed

corollary (in group) iso_imp_img_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> iso G H"
  shows "group (H \<lparr> one := h \<one> \<rparr>)"
proof -
  let ?h_img = "H \<lparr> carrier := h ` (carrier G), one := h \<one> \<rparr>"
  have "h \<in> iso G ?h_img"
    using assms unfolding iso_def hom_def bij_betw_def by auto
  hence "G \<cong> ?h_img"
    unfolding is_iso_def by auto
  hence "group ?h_img"
    using iso_imp_group[of ?h_img] hom_imp_img_monoid[of h H] assms unfolding iso_def by simp
  moreover have "carrier H = carrier ?h_img"
    using assms unfolding iso_def bij_betw_def by simp
  hence "H \<lparr> one := h \<one> \<rparr> = ?h_img"
    by simp
  ultimately show ?thesis by simp
qed

subsubsection \<open>HOL Light's concept of an isomorphism pair\<close>

definition group_isomorphisms
  where
 "group_isomorphisms G H f g \<equiv>
        f \<in> hom G H \<and> g \<in> hom H G \<and>
        (\<forall>x \<in> carrier G. g(f x) = x) \<and>
        (\<forall>y \<in> carrier H. f(g y) = y)"

lemma group_isomorphisms_sym: "group_isomorphisms G H f g \<Longrightarrow> group_isomorphisms H G g f"
  by (auto simp: group_isomorphisms_def)

lemma group_isomorphisms_imp_iso: "group_isomorphisms G H f g \<Longrightarrow> f \<in> iso G H"
by (auto simp: iso_def inj_on_def image_def group_isomorphisms_def hom_def bij_betw_def Pi_iff, metis+)

lemma (in group) iso_iff_group_isomorphisms:
  "f \<in> iso G H \<longleftrightarrow> (\<exists>g. group_isomorphisms G H f g)"
proof safe
  show "\<exists>g. group_isomorphisms G H f g" if "f \<in> Group.iso G H"
    unfolding group_isomorphisms_def
  proof (intro exI conjI)
    let ?g = "inv_into (carrier G) f"
    show "\<forall>x\<in>carrier G. ?g (f x) = x"
      by (metis (no_types, lifting) Group.iso_def bij_betw_inv_into_left mem_Collect_eq that)
    show "\<forall>y\<in>carrier H. f (?g y) = y"
      by (metis (no_types, lifting) Group.iso_def bij_betw_inv_into_right mem_Collect_eq that)
  qed (use Group.iso_def iso_set_sym that in \<open>blast+\<close>)
next
  fix g
  assume "group_isomorphisms G H f g"
  then show "f \<in> Group.iso G H"
    by (auto simp: iso_def group_isomorphisms_def hom_in_carrier intro: bij_betw_byWitness)
qed


subsubsection \<open>Involving direct products\<close>

lemma DirProd_commute_iso_set:
  shows "(\<lambda>(x,y). (y,x)) \<in> iso (G \<times>\<times> H) (H \<times>\<times> G)"
  by (auto simp add: iso_def hom_def inj_on_def bij_betw_def)

corollary DirProd_commute_iso :
"(G \<times>\<times> H) \<cong> (H \<times>\<times> G)"
  using DirProd_commute_iso_set unfolding is_iso_def by blast

lemma DirProd_assoc_iso_set:
  shows "(\<lambda>(x,y,z). (x,(y,z))) \<in> iso (G \<times>\<times> H \<times>\<times> I) (G \<times>\<times> (H \<times>\<times> I))"
by (auto simp add: iso_def hom_def inj_on_def bij_betw_def)

lemma (in group) DirProd_iso_set_trans:
  assumes "g \<in> iso G G2"
    and "h \<in> iso H I"
  shows "(\<lambda>(x,y). (g x, h y)) \<in> iso (G \<times>\<times> H) (G2 \<times>\<times> I)"
proof-
  have "(\<lambda>(x,y). (g x, h y)) \<in> hom (G \<times>\<times> H) (G2 \<times>\<times> I)"
    using assms unfolding iso_def hom_def by auto
  moreover have " inj_on (\<lambda>(x,y). (g x, h y)) (carrier (G \<times>\<times> H))"
    using assms unfolding iso_def DirProd_def bij_betw_def inj_on_def by auto
  moreover have "(\<lambda>(x, y). (g x, h y)) ` carrier (G \<times>\<times> H) = carrier (G2 \<times>\<times> I)"
    using assms unfolding iso_def bij_betw_def image_def DirProd_def by fastforce
  ultimately show "(\<lambda>(x,y). (g x, h y)) \<in> iso (G \<times>\<times> H) (G2 \<times>\<times> I)"
    unfolding iso_def bij_betw_def by auto
qed

corollary (in group) DirProd_iso_trans :
  assumes "G \<cong> G2" and "H \<cong> I"
  shows "G \<times>\<times> H \<cong> G2 \<times>\<times> I"
  using DirProd_iso_set_trans assms unfolding is_iso_def by blast

lemma hom_pairwise: "f \<in> hom G (DirProd H K) \<longleftrightarrow> (fst \<circ> f) \<in> hom G H \<and> (snd \<circ> f) \<in> hom G K"
  apply (auto simp: hom_def mult_DirProd' dest: Pi_mem)
   apply (metis Product_Type.mem_Times_iff comp_eq_dest_lhs funcset_mem)
  by (metis mult_DirProd prod.collapse)

lemma hom_paired:
   "(\<lambda>x. (f x,g x)) \<in> hom G (DirProd H K) \<longleftrightarrow> f \<in> hom G H \<and> g \<in> hom G K"
  by (simp add: hom_pairwise o_def)

lemma hom_paired2:
  assumes "group G" "group H"
  shows "(\<lambda>(x,y). (f x,g y)) \<in> hom (DirProd G H) (DirProd G' H') \<longleftrightarrow> f \<in> hom G G' \<and> g \<in> hom H H'"
  using assms
  by (fastforce simp: hom_def Pi_def dest!: group.is_monoid)

lemma iso_paired2:
  assumes "group G" "group H"
  shows "(\<lambda>(x,y). (f x,g y)) \<in> iso (DirProd G H) (DirProd G' H') \<longleftrightarrow> f \<in> iso G G' \<and> g \<in> iso H H'"
  using assms
  by (fastforce simp add: iso_def inj_on_def bij_betw_def hom_paired2 image_paired_Times
      times_eq_iff group_def monoid.carrier_not_empty)

lemma hom_of_fst:
  assumes "group H"
  shows "(f \<circ> fst) \<in> hom (DirProd G H) K \<longleftrightarrow> f \<in> hom G K"
proof -
  interpret group H
    by (rule assms)
  show ?thesis
    using one_closed by (auto simp: hom_def Pi_def)
qed

lemma hom_of_snd:
  assumes "group G"
  shows "(f \<circ> snd) \<in> hom (DirProd G H) K \<longleftrightarrow> f \<in> hom H K"
proof -
  interpret group G
    by (rule assms)
  show ?thesis
    using one_closed by (auto simp: hom_def Pi_def)
qed


subsection\<open>The locale for a homomorphism between two groups\<close>

text\<open>Basis for homomorphism proofs: we assume two groups \<^term>\<open>G\<close> and
  \<^term>\<open>H\<close>, with a homomorphism \<^term>\<open>h\<close> between them\<close>
locale group_hom = G?: group G + H?: group H for G (structure) and H (structure) +
  fixes h
  assumes homh [simp]: "h \<in> hom G H"

declare group_hom.homh [simp]

lemma (in group_hom) hom_mult [simp]:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y"
proof -
  assume "x \<in> carrier G" "y \<in> carrier G"
  with homh [unfolded hom_def] show ?thesis by simp
qed

lemma (in group_hom) hom_closed [simp]:
  "x \<in> carrier G ==> h x \<in> carrier H"
proof -
  assume "x \<in> carrier G"
  with homh [unfolded hom_def] show ?thesis by auto
qed

lemma (in group_hom) one_closed: "h \<one> \<in> carrier H"
  by simp

lemma (in group_hom) hom_one [simp]: "h \<one> = \<one>\<^bsub>H\<^esub>"
proof -
  have "h \<one> \<otimes>\<^bsub>H\<^esub> \<one>\<^bsub>H\<^esub> = h \<one> \<otimes>\<^bsub>H\<^esub> h \<one>"
    by (simp add: hom_mult [symmetric] del: hom_mult)
  then show ?thesis
    by (metis H.Units_eq H.Units_l_cancel H.one_closed local.one_closed)
qed

lemma hom_one:
  assumes "h \<in> hom G H" "group G" "group H"
  shows "h (one G) = one H"
  apply (rule group_hom.hom_one)
  by (simp add: assms group_hom_axioms_def group_hom_def)

lemma hom_mult:
  "\<lbrakk>h \<in> hom G H; x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y"
  by (auto simp: hom_def)

lemma (in group_hom) inv_closed [simp]:
  "x \<in> carrier G ==> h (inv x) \<in> carrier H"
  by simp

lemma (in group_hom) hom_inv [simp]:
  assumes "x \<in> carrier G" shows "h (inv x) = inv\<^bsub>H\<^esub> (h x)"
proof -
  have "h x \<otimes>\<^bsub>H\<^esub> h (inv x) = h x \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h x)" 
    using assms by (simp flip: hom_mult)
  with assms show ?thesis by (simp del: H.r_inv H.Units_r_inv)
qed

lemma (in group) int_pow_is_hom: \<^marker>\<open>contributor \<open>Joachim Breitner\<close>\<close>
  "x \<in> carrier G \<Longrightarrow> (([^]) x) \<in> hom \<lparr> carrier = UNIV, mult = (+), one = 0::int \<rparr> G "
  unfolding hom_def by (simp add: int_pow_mult)

lemma (in group_hom) img_is_subgroup: "subgroup (h ` (carrier G)) H" \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  apply (rule subgroupI)
  apply (auto simp add: image_subsetI)
  apply (metis G.inv_closed hom_inv image_iff)
  by (metis G.monoid_axioms hom_mult image_eqI monoid.m_closed)

lemma (in group_hom) subgroup_img_is_subgroup: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "subgroup I G"
  shows "subgroup (h ` I) H"
proof -
  have "h \<in> hom (G \<lparr> carrier := I \<rparr>) H"
    using G.subgroupE[OF assms] subgroup.mem_carrier[OF assms] homh
    unfolding hom_def by auto
  hence "group_hom (G \<lparr> carrier := I \<rparr>) H h"
    using subgroup.subgroup_is_group[OF assms G.is_group] is_group
    unfolding group_hom_def group_hom_axioms_def by simp
  thus ?thesis
    using group_hom.img_is_subgroup[of "G \<lparr> carrier := I \<rparr>" H h] by simp
qed

lemma (in group_hom) induced_group_hom: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "subgroup I G"
  shows "group_hom (G \<lparr> carrier := I \<rparr>) (H \<lparr> carrier := h ` I \<rparr>) h"
proof -
  have "h \<in> hom (G \<lparr> carrier := I \<rparr>) (H \<lparr> carrier := h ` I \<rparr>)"
    using homh subgroup.mem_carrier[OF assms] unfolding hom_def by auto
  thus ?thesis
    unfolding group_hom_def group_hom_axioms_def
    using subgroup.subgroup_is_group[OF assms G.is_group]
          subgroup.subgroup_is_group[OF subgroup_img_is_subgroup[OF assms] is_group] by simp
qed

lemma (in group) canonical_inj_is_hom: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "subgroup H G"
  shows "group_hom (G \<lparr> carrier := H \<rparr>) G id"
  unfolding group_hom_def group_hom_axioms_def hom_def
  using subgroup.subgroup_is_group[OF assms is_group]
        is_group subgroup.subset[OF assms] by auto

lemma (in group_hom) hom_nat_pow: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  "x \<in> carrier G \<Longrightarrow> h (x [^] (n :: nat)) = (h x) [^]\<^bsub>H\<^esub> n"
  by (induction n) auto

lemma (in group_hom) hom_int_pow: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  "x \<in> carrier G \<Longrightarrow> h (x [^] (n :: int)) = (h x) [^]\<^bsub>H\<^esub> n"
  using hom_nat_pow by (simp add: int_pow_def2)

lemma hom_nat_pow:
  "\<lbrakk>h \<in> hom G H; x \<in> carrier G; group G; group H\<rbrakk> \<Longrightarrow> h (x [^]\<^bsub>G\<^esub> (n :: nat)) = (h x) [^]\<^bsub>H\<^esub> n"
  by (simp add: group_hom.hom_nat_pow group_hom_axioms_def group_hom_def)

lemma hom_int_pow:
  "\<lbrakk>h \<in> hom G H; x \<in> carrier G; group G; group H\<rbrakk> \<Longrightarrow> h (x [^]\<^bsub>G\<^esub> (n :: int)) = (h x) [^]\<^bsub>H\<^esub> n"
  by (simp add: group_hom.hom_int_pow group_hom_axioms.intro group_hom_def)

subsection \<open>Commutative Structures\<close>

text \<open>
  Naming convention: multiplicative structures that are commutative
  are called \emph{commutative}, additive structures are called
  \emph{Abelian}.
\<close>

locale comm_monoid = monoid +
  assumes m_comm: "\<lbrakk>x \<in> carrier G; y \<in> carrier G\<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"

lemma (in comm_monoid) m_lcomm:
  "\<lbrakk>x \<in> carrier G; y \<in> carrier G; z \<in> carrier G\<rbrakk> \<Longrightarrow>
   x \<otimes> (y \<otimes> z) = y \<otimes> (x \<otimes> z)"
proof -
  assume xyz: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
  from xyz have "x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z" by (simp add: m_assoc)
  also from xyz have "... = (y \<otimes> x) \<otimes> z" by (simp add: m_comm)
  also from xyz have "... = y \<otimes> (x \<otimes> z)" by (simp add: m_assoc)
  finally show ?thesis .
qed

lemmas (in comm_monoid) m_ac = m_assoc m_comm m_lcomm

lemma comm_monoidI:
  fixes G (structure)
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
  shows "comm_monoid G"
  using l_one
    by (auto intro!: comm_monoid.intro comm_monoid_axioms.intro monoid.intro
             intro: assms simp: m_closed one_closed m_comm)

lemma (in monoid) monoid_comm_monoidI:
  assumes m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
  shows "comm_monoid G"
  by (rule comm_monoidI) (auto intro: m_assoc m_comm)

lemma (in comm_monoid) submonoid_is_comm_monoid :
  assumes "submonoid H G"
  shows "comm_monoid (G\<lparr>carrier := H\<rparr>)"
proof (intro monoid.monoid_comm_monoidI)
  show "monoid (G\<lparr>carrier := H\<rparr>)"
    using submonoid.submonoid_is_monoid assms comm_monoid_axioms comm_monoid_def by blast
  show "\<And>x y. x \<in> carrier (G\<lparr>carrier := H\<rparr>) \<Longrightarrow> y \<in> carrier (G\<lparr>carrier := H\<rparr>)
        \<Longrightarrow> x \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> y = y \<otimes>\<^bsub>G\<lparr>carrier := H\<rparr>\<^esub> x" 
    by simp (meson assms m_comm submonoid.mem_carrier)
qed

locale comm_group = comm_monoid + group

lemma (in group) group_comm_groupI:
  assumes m_comm: "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
  shows "comm_group G"
  by standard (simp_all add: m_comm)

lemma comm_groupI:
  fixes G (structure)
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and l_inv_ex: "!!x. x \<in> carrier G ==> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  shows "comm_group G"
  by (fast intro: group.group_comm_groupI groupI assms)

lemma comm_groupE:
  fixes G (structure)
  assumes "comm_group G"
  shows "\<And>x y. \<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes> y \<in> carrier G"
    and "\<one> \<in> carrier G"
    and "\<And>x y z. \<lbrakk> x \<in> carrier G; y \<in> carrier G; z \<in> carrier G \<rbrakk> \<Longrightarrow> (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and "\<And>x y. \<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> x \<otimes> y = y \<otimes> x"
    and "\<And>x. x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x"
    and "\<And>x. x \<in> carrier G \<Longrightarrow> \<exists>y \<in> carrier G. y \<otimes> x = \<one>"
  apply (simp_all add: group.axioms assms comm_group.axioms comm_monoid.m_comm comm_monoid.m_ac(1))
  by (simp_all add: Group.group.axioms(1) assms comm_group.axioms(2) monoid.m_closed group.r_inv_ex)

lemma (in comm_group) inv_mult:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> inv (x \<otimes> y) = inv x \<otimes> inv y"
  by (simp add: m_ac inv_mult_group)

lemma (in comm_monoid) nat_pow_distrib:
  fixes n::nat
  assumes "x \<in> carrier G" "y \<in> carrier G"
  shows "(x \<otimes> y) [^] n = x [^] n \<otimes> y [^] n"
  by (simp add: assms pow_mult_distrib m_comm)

lemma (in comm_group) int_pow_distrib:
  assumes "x \<in> carrier G" "y \<in> carrier G"
  shows "(x \<otimes> y) [^] (i::int) = x [^] i \<otimes> y [^] i"
  by (simp add: assms int_pow_mult_distrib m_comm)

lemma (in comm_monoid) hom_imp_img_comm_monoid: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> hom G H"
  shows "comm_monoid (H \<lparr> carrier := h ` (carrier G), one := h \<one>\<^bsub>G\<^esub> \<rparr>)" (is "comm_monoid ?h_img")
proof (rule monoid.monoid_comm_monoidI)
  show "monoid ?h_img"
    using hom_imp_img_monoid[OF assms] .
next
  fix x y assume "x \<in> carrier ?h_img" "y \<in> carrier ?h_img"
  then obtain g1 g2
    where g1: "g1 \<in> carrier G" "x = h g1"
      and g2: "g2 \<in> carrier G" "y = h g2"
    by auto
  have "x \<otimes>\<^bsub>(?h_img)\<^esub> y = h (g1 \<otimes> g2)"
    using g1 g2 assms unfolding hom_def by auto
  also have " ... = h (g2 \<otimes> g1)"
    using m_comm[OF g1(1) g2(1)] by simp
  also have " ... = y \<otimes>\<^bsub>(?h_img)\<^esub> x"
    using g1 g2 assms unfolding hom_def by auto
  finally show "x \<otimes>\<^bsub>(?h_img)\<^esub> y = y \<otimes>\<^bsub>(?h_img)\<^esub> x" .
qed

lemma (in comm_group) hom_group_mult:
  assumes "f \<in> hom H G" "g \<in> hom H G"
 shows "(\<lambda>x. f x \<otimes>\<^bsub>G\<^esub> g x) \<in> hom H G"
    using assms by (auto simp: hom_def Pi_def m_ac)

lemma (in comm_group) hom_imp_img_comm_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> hom G H"
  shows "comm_group (H \<lparr> carrier := h ` (carrier G), one := h \<one>\<^bsub>G\<^esub> \<rparr>)"
  unfolding comm_group_def
  using hom_imp_img_group[OF assms] hom_imp_img_comm_monoid[OF assms] by simp

lemma (in comm_group) iso_imp_img_comm_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "h \<in> iso G H"
  shows "comm_group (H \<lparr> one := h \<one>\<^bsub>G\<^esub> \<rparr>)"
proof -
  let ?h_img = "H \<lparr> carrier := h ` (carrier G), one := h \<one> \<rparr>"
  have "comm_group ?h_img"
    using hom_imp_img_comm_group[of h H] assms unfolding iso_def by auto
  moreover have "carrier H = carrier ?h_img"
    using assms unfolding iso_def bij_betw_def by simp
  hence "H \<lparr> one := h \<one> \<rparr> = ?h_img"
    by simp
  ultimately show ?thesis by simp
qed

lemma (in comm_group) iso_imp_comm_group: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "G \<cong> H" "monoid H"
  shows "comm_group H"
proof -
  obtain h where h: "h \<in> iso G H"
    using assms(1) unfolding is_iso_def by auto
  hence comm_gr: "comm_group (H \<lparr> one := h \<one> \<rparr>)"
    using iso_imp_img_comm_group[of h H] by simp
  hence "\<And>x. x \<in> carrier H \<Longrightarrow> h \<one> \<otimes>\<^bsub>H\<^esub> x = x"
    using monoid.l_one[of "H \<lparr> one := h \<one> \<rparr>"] unfolding comm_group_def comm_monoid_def by simp
  moreover have "h \<one> \<in> carrier H"
    using h one_closed unfolding iso_def hom_def by auto
  ultimately have "h \<one> = \<one>\<^bsub>H\<^esub>"
    using monoid.one_unique[OF assms(2), of "h \<one>"] by simp
  hence "H = H \<lparr> one := h \<one> \<rparr>"
    by simp
  thus ?thesis
    using comm_gr by simp
qed

(*A subgroup of a subgroup is a subgroup of the group*)
lemma (in group) incl_subgroup:
  assumes "subgroup J G"
    and "subgroup I (G\<lparr>carrier:=J\<rparr>)"
  shows "subgroup I G" unfolding subgroup_def
proof
  have H1: "I \<subseteq> carrier (G\<lparr>carrier:=J\<rparr>)" using assms(2) subgroup.subset by blast
  also have H2: "...\<subseteq>J" by simp
  also  have "...\<subseteq>(carrier G)"  by (simp add: assms(1) subgroup.subset)
  finally have H: "I \<subseteq> carrier G" by simp
  have "(\<And>x y. \<lbrakk>x \<in> I ; y \<in> I\<rbrakk> \<Longrightarrow> x \<otimes> y \<in> I)" using assms(2) by (auto simp add: subgroup_def)
  thus  "I \<subseteq> carrier G \<and> (\<forall>x y. x \<in> I \<longrightarrow> y \<in> I \<longrightarrow> x \<otimes> y \<in> I)"  using H by blast
  have K: "\<one> \<in> I" using assms(2) by (auto simp add: subgroup_def)
  have "(\<And>x. x \<in> I \<Longrightarrow> inv x \<in> I)" using assms  subgroup.m_inv_closed H
    by (metis H1 H2 m_inv_consistent subsetCE)
  thus "\<one> \<in> I \<and> (\<forall>x. x \<in> I \<longrightarrow> inv x \<in> I)" using K by blast
qed

(*A subgroup included in another subgroup is a subgroup of the subgroup*)
lemma (in group) subgroup_incl:
  assumes "subgroup I G" and "subgroup J G" and "I \<subseteq> J"
  shows "subgroup I (G \<lparr> carrier := J \<rparr>)"
  using group.group_incl_imp_subgroup[of "G \<lparr> carrier := J \<rparr>" I]
        assms(1-2)[THEN subgroup.subgroup_is_group[OF _ group_axioms]] assms(3) by auto


subsection \<open>The Lattice of Subgroups of a Group\<close>

text_raw \<open>\label{sec:subgroup-lattice}\<close>

theorem (in group) subgroups_partial_order:
  "partial_order \<lparr>carrier = {H. subgroup H G}, eq = (=), le = (\<subseteq>)\<rparr>"
  by standard simp_all

lemma (in group) subgroup_self:
  "subgroup (carrier G) G"
  by (rule subgroupI) auto

lemma (in group) subgroup_imp_group:
  "subgroup H G ==> group (G\<lparr>carrier := H\<rparr>)"
  by (erule subgroup.subgroup_is_group) (rule group_axioms)

lemma (in group) subgroup_mult_equality:
  "\<lbrakk> subgroup H G; h1 \<in> H; h2 \<in> H \<rbrakk> \<Longrightarrow>  h1 \<otimes>\<^bsub>G \<lparr> carrier := H \<rparr>\<^esub> h2 = h1 \<otimes> h2"
  unfolding subgroup_def by simp

theorem (in group) subgroups_Inter:
  assumes subgr: "(\<And>H. H \<in> A \<Longrightarrow> subgroup H G)"
    and not_empty: "A \<noteq> {}"
  shows "subgroup (\<Inter>A) G"
proof (rule subgroupI)
  from subgr [THEN subgroup.subset] and not_empty
  show "\<Inter>A \<subseteq> carrier G" by blast
next
  from subgr [THEN subgroup.one_closed]
  show "\<Inter>A \<noteq> {}" by blast
next
  fix x assume "x \<in> \<Inter>A"
  with subgr [THEN subgroup.m_inv_closed]
  show "inv x \<in> \<Inter>A" by blast
next
  fix x y assume "x \<in> \<Inter>A" "y \<in> \<Inter>A"
  with subgr [THEN subgroup.m_closed]
  show "x \<otimes> y \<in> \<Inter>A" by blast
qed

lemma (in group) subgroups_Inter_pair :
  assumes  "subgroup I G"
    and  "subgroup J G"
  shows "subgroup (I\<inter>J) G" using subgroups_Inter[ where ?A = "{I,J}"] assms by auto

theorem (in group) subgroups_complete_lattice:
  "complete_lattice \<lparr>carrier = {H. subgroup H G}, eq = (=), le = (\<subseteq>)\<rparr>"
    (is "complete_lattice ?L")
proof (rule partial_order.complete_lattice_criterion1)
  show "partial_order ?L" by (rule subgroups_partial_order)
next
  have "greatest ?L (carrier G) (carrier ?L)"
    by (unfold greatest_def) (simp add: subgroup.subset subgroup_self)
  then show "\<exists>G. greatest ?L G (carrier ?L)" ..
next
  fix A
  assume L: "A \<subseteq> carrier ?L" and non_empty: "A \<noteq> {}"
  then have Int_subgroup: "subgroup (\<Inter>A) G"
    by (fastforce intro: subgroups_Inter)
  have "greatest ?L (\<Inter>A) (Lower ?L A)" (is "greatest _ ?Int _")
  proof (rule greatest_LowerI)
    fix H
    assume H: "H \<in> A"
    with L have subgroupH: "subgroup H G" by auto
    from subgroupH have groupH: "group (G \<lparr>carrier := H\<rparr>)" (is "group ?H")
      by (rule subgroup_imp_group)
    from groupH have monoidH: "monoid ?H"
      by (rule group.is_monoid)
    from H have Int_subset: "?Int \<subseteq> H" by fastforce
    then show "le ?L ?Int H" by simp
  next
    fix H
    assume H: "H \<in> Lower ?L A"
    with L Int_subgroup show "le ?L H ?Int"
      by (fastforce simp: Lower_def intro: Inter_greatest)
  next
    show "A \<subseteq> carrier ?L" by (rule L)
  next
    show "?Int \<in> carrier ?L" by simp (rule Int_subgroup)
  qed
  then show "\<exists>I. greatest ?L I (Lower ?L A)" ..
qed

subsection\<open>The units in any monoid give rise to a group\<close>

text \<open>Thanks to Jeremy Avigad. The file Residues.thy provides some infrastructure to use
  facts about the unit group within the ring locale.
\<close>

definition units_of :: "('a, 'b) monoid_scheme \<Rightarrow> 'a monoid"
  where "units_of G =
    \<lparr>carrier = Units G, Group.monoid.mult = Group.monoid.mult G, one  = one G\<rparr>"

lemma (in monoid) units_group: "group (units_of G)"
proof -
  have "\<And>x y z. \<lbrakk>x \<in> Units G; y \<in> Units G; z \<in> Units G\<rbrakk> \<Longrightarrow> x \<otimes> y \<otimes> z = x \<otimes> (y \<otimes> z)"
    by (simp add: Units_closed m_assoc)
  moreover have "\<And>x. x \<in> Units G \<Longrightarrow> \<exists>y\<in>Units G. y \<otimes> x = \<one>"
    using Units_l_inv by blast
  ultimately show ?thesis
    unfolding units_of_def
    by (force intro!: groupI)
qed

lemma (in comm_monoid) units_comm_group: "comm_group (units_of G)"
proof -
  have "\<And>x y. \<lbrakk>x \<in> carrier (units_of G); y \<in> carrier (units_of G)\<rbrakk>
              \<Longrightarrow> x \<otimes>\<^bsub>units_of G\<^esub> y = y \<otimes>\<^bsub>units_of G\<^esub> x"
    by (simp add: Units_closed m_comm units_of_def)
  then show ?thesis
    by (rule group.group_comm_groupI [OF units_group]) auto
qed

lemma units_of_carrier: "carrier (units_of G) = Units G"
  by (auto simp: units_of_def)

lemma units_of_mult: "mult (units_of G) = mult G"
  by (auto simp: units_of_def)

lemma units_of_one: "one (units_of G) = one G"
  by (auto simp: units_of_def)

lemma (in monoid) units_of_inv:
  assumes "x \<in> Units G"
  shows "m_inv (units_of G) x = m_inv G x"
  by (simp add: assms group.inv_equality units_group units_of_carrier units_of_mult units_of_one)

lemma units_of_units [simp] : "Units (units_of G) = Units G"
  unfolding units_of_def Units_def by force

lemma (in group) surj_const_mult: "a \<in> carrier G \<Longrightarrow> (\<lambda>x. a \<otimes> x) ` carrier G = carrier G"
  apply (auto simp add: image_def)
  by (metis inv_closed inv_solve_left m_closed)

lemma (in group) l_cancel_one [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> x \<otimes> a = x \<longleftrightarrow> a = one G"
  by (metis Units_eq Units_l_cancel monoid.r_one monoid_axioms one_closed)

lemma (in group) r_cancel_one [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> a \<otimes> x = x \<longleftrightarrow> a = one G"
  by (metis monoid.l_one monoid_axioms one_closed right_cancel)

lemma (in group) l_cancel_one' [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> x = x \<otimes> a \<longleftrightarrow> a = one G"
  using l_cancel_one by fastforce

lemma (in group) r_cancel_one' [simp]: "x \<in> carrier G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> x = a \<otimes> x \<longleftrightarrow> a = one G"
  using r_cancel_one by fastforce

declare pow_nat [simp] (*causes looping if added above, especially with int_pow_def2*)

end
