(*
  Title:  HOL/Algebra/Group.thy
  Id:     $Id$
  Author: Clemens Ballarin, started 4 February 2003

Based on work by Florian Kammueller, L C Paulson and Markus Wenzel.
*)

header {* Groups *}

theory Group = FuncSet + Lattice:

section {* From Magmas to Groups *}

text {*
  Definitions follow \cite{Jacobson:1985}; with the exception of
  \emph{magma} which, following Bourbaki, is a set together with a
  binary, closed operation.
*}

subsection {* Definitions *}

record 'a semigroup = "'a partial_object" +
  mult :: "['a, 'a] => 'a" (infixl "\<otimes>\<index>" 70)

record 'a monoid = "'a semigroup" +
  one :: 'a ("\<one>\<index>")

constdefs (structure G)
  m_inv :: "_ => 'a => 'a" ("inv\<index> _" [81] 80)
  "inv x == (THE y. y \<in> carrier G & x \<otimes> y = \<one> & y \<otimes> x = \<one>)"

  Units :: "_ => 'a set"
  "Units G == {y. y \<in> carrier G & (EX x : carrier G. x \<otimes> y = \<one> & y \<otimes> x = \<one>)}"

consts
  pow :: "[('a, 'm) monoid_scheme, 'a, 'b::number] => 'a" (infixr "'(^')\<index>" 75)

defs (overloaded)
  nat_pow_def: "pow G a n == nat_rec \<one>\<^bsub>G\<^esub> (%u b. b \<otimes>\<^bsub>G\<^esub> a) n"
  int_pow_def: "pow G a z ==
    let p = nat_rec \<one>\<^bsub>G\<^esub> (%u b. b \<otimes>\<^bsub>G\<^esub> a)
    in if neg z then inv\<^bsub>G\<^esub> (p (nat (-z))) else p (nat z)"

locale magma = struct G +
  assumes m_closed [intro, simp]:
    "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"

locale semigroup = magma +
  assumes m_assoc:
    "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
    (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"

locale monoid = semigroup +
  assumes one_closed [intro, simp]: "\<one> \<in> carrier G"
    and l_one [simp]: "x \<in> carrier G ==> \<one> \<otimes> x = x"
    and r_one [simp]: "x \<in> carrier G ==> x \<otimes> \<one> = x"

lemma monoidI:
  includes struct G
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and r_one: "!!x. x \<in> carrier G ==> x \<otimes> \<one> = x"
  shows "monoid G"
  by (fast intro!: monoid.intro magma.intro semigroup_axioms.intro
    semigroup.intro monoid_axioms.intro
    intro: prems)

lemma (in monoid) Units_closed [dest]:
  "x \<in> Units G ==> x \<in> carrier G"
  by (unfold Units_def) fast

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

lemma (in monoid) Units_one_closed [intro, simp]:
  "\<one> \<in> Units G"
  by (unfold Units_def) auto

lemma (in monoid) Units_inv_closed [intro, simp]:
  "x \<in> Units G ==> inv x \<in> carrier G"
  apply (unfold Units_def m_inv_def, auto)
  apply (rule theI2, fast)
   apply (fast intro: inv_unique, fast)
  done

lemma (in monoid) Units_l_inv:
  "x \<in> Units G ==> inv x \<otimes> x = \<one>"
  apply (unfold Units_def m_inv_def, auto)
  apply (rule theI2, fast)
   apply (fast intro: inv_unique, fast)
  done

lemma (in monoid) Units_r_inv:
  "x \<in> Units G ==> x \<otimes> inv x = \<one>"
  apply (unfold Units_def m_inv_def, auto)
  apply (rule theI2, fast)
   apply (fast intro: inv_unique, fast)
  done

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
    by (simp add: m_assoc Units_closed)
  with G show "y = z" by (simp add: Units_l_inv)
next
  assume eq: "y = z"
    and G: "x \<in> Units G"  "y \<in> carrier G"  "z \<in> carrier G"
  then show "x \<otimes> y = x \<otimes> z" by simp
qed

lemma (in monoid) Units_inv_inv [simp]:
  "x \<in> Units G ==> inv (inv x) = x"
proof -
  assume x: "x \<in> Units G"
  then have "inv x \<otimes> inv (inv x) = inv x \<otimes> x"
    by (simp add: Units_l_inv Units_r_inv)
  with x show ?thesis by (simp add: Units_closed)
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

text {* Power *}

lemma (in monoid) nat_pow_closed [intro, simp]:
  "x \<in> carrier G ==> x (^) (n::nat) \<in> carrier G"
  by (induct n) (simp_all add: nat_pow_def)

lemma (in monoid) nat_pow_0 [simp]:
  "x (^) (0::nat) = \<one>"
  by (simp add: nat_pow_def)

lemma (in monoid) nat_pow_Suc [simp]:
  "x (^) (Suc n) = x (^) n \<otimes> x"
  by (simp add: nat_pow_def)

lemma (in monoid) nat_pow_one [simp]:
  "\<one> (^) (n::nat) = \<one>"
  by (induct n) simp_all

lemma (in monoid) nat_pow_mult:
  "x \<in> carrier G ==> x (^) (n::nat) \<otimes> x (^) m = x (^) (n + m)"
  by (induct m) (simp_all add: m_assoc [THEN sym])

lemma (in monoid) nat_pow_pow:
  "x \<in> carrier G ==> (x (^) n) (^) m = x (^) (n * m::nat)"
  by (induct m) (simp, simp add: nat_pow_mult add_commute)

text {*
  A group is a monoid all of whose elements are invertible.
*}

locale group = monoid +
  assumes Units: "carrier G <= Units G"

theorem groupI:
  includes struct G
  assumes m_closed [simp]:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed [simp]: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and l_one [simp]: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and l_inv_ex: "!!x. x \<in> carrier G ==> EX y : carrier G. y \<otimes> x = \<one>"
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
    "!!x. x \<in> carrier G ==> EX y : carrier G. y \<otimes> x = \<one> & x \<otimes> y = \<one>"
  proof -
    fix x
    assume x: "x \<in> carrier G"
    with l_inv_ex obtain y where y: "y \<in> carrier G"
      and l_inv: "y \<otimes> x = \<one>" by fast
    from x y have "y \<otimes> (x \<otimes> y) = y \<otimes> \<one>"
      by (simp add: m_assoc [symmetric] l_inv r_one)
    with x y have r_inv: "x \<otimes> y = \<one>"
      by simp
    from x y show "EX y : carrier G. y \<otimes> x = \<one> & x \<otimes> y = \<one>"
      by (fast intro: l_inv r_inv)
  qed
  then have carrier_subset_Units: "carrier G <= Units G"
    by (unfold Units_def) fast
  show ?thesis
    by (fast intro!: group.intro magma.intro semigroup_axioms.intro
      semigroup.intro monoid_axioms.intro group_axioms.intro
      carrier_subset_Units intro: prems r_one)
qed

lemma (in monoid) monoid_groupI:
  assumes l_inv_ex:
    "!!x. x \<in> carrier G ==> EX y : carrier G. y \<otimes> x = \<one>"
  shows "group G"
  by (rule groupI) (auto intro: m_assoc l_inv_ex)

lemma (in group) Units_eq [simp]:
  "Units G = carrier G"
proof
  show "Units G <= carrier G" by fast
next
  show "carrier G <= Units G" by (rule Units)
qed

lemma (in group) inv_closed [intro, simp]:
  "x \<in> carrier G ==> inv x \<in> carrier G"
  using Units_inv_closed by simp

lemma (in group) l_inv:
  "x \<in> carrier G ==> inv x \<otimes> x = \<one>"
  using Units_l_inv by simp

subsection {* Cancellation Laws and Basic Properties *}

lemma (in group) l_cancel [simp]:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   (x \<otimes> y = x \<otimes> z) = (y = z)"
  using Units_l_inv by simp

lemma (in group) r_inv:
  "x \<in> carrier G ==> x \<otimes> inv x = \<one>"
proof -
  assume x: "x \<in> carrier G"
  then have "inv x \<otimes> (x \<otimes> inv x) = inv x \<otimes> \<one>"
    by (simp add: m_assoc [symmetric] l_inv)
  with x show ?thesis by (simp del: r_one)
qed

lemma (in group) r_cancel [simp]:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   (y \<otimes> x = z \<otimes> x) = (y = z)"
proof
  assume eq: "y \<otimes> x = z \<otimes> x"
    and G: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
  then have "y \<otimes> (x \<otimes> inv x) = z \<otimes> (x \<otimes> inv x)"
    by (simp add: m_assoc [symmetric])
  with G show "y = z" by (simp add: r_inv)
next
  assume eq: "y = z"
    and G: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
  then show "y \<otimes> x = z \<otimes> x" by simp
qed

lemma (in group) inv_one [simp]:
  "inv \<one> = \<one>"
proof -
  have "inv \<one> = \<one> \<otimes> (inv \<one>)" by simp
  moreover have "... = \<one>" by (simp add: r_inv)
  finally show ?thesis .
qed

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
    by (simp add: m_assoc l_inv) (simp add: m_assoc [symmetric] l_inv)
  with G show ?thesis by simp
qed

lemma (in group) inv_comm:
  "[| x \<otimes> y = \<one>; x \<in> carrier G; y \<in> carrier G |] ==> y \<otimes> x = \<one>"
  by (rule Units_inv_comm) auto

lemma (in group) inv_equality:
     "[|y \<otimes> x = \<one>; x \<in> carrier G; y \<in> carrier G|] ==> inv x = y"
apply (simp add: m_inv_def)
apply (rule the_equality)
 apply (simp add: inv_comm [of y x])
apply (rule r_cancel [THEN iffD1], auto)
done

text {* Power *}

lemma (in group) int_pow_def2:
  "a (^) (z::int) = (if neg z then inv (a (^) (nat (-z))) else a (^) (nat z))"
  by (simp add: int_pow_def nat_pow_def Let_def)

lemma (in group) int_pow_0 [simp]:
  "x (^) (0::int) = \<one>"
  by (simp add: int_pow_def2)

lemma (in group) int_pow_one [simp]:
  "\<one> (^) (z::int) = \<one>"
  by (simp add: int_pow_def2)

subsection {* Substructures *}

locale submagma = var H + struct G +
  assumes subset [intro, simp]: "H \<subseteq> carrier G"
    and m_closed [intro, simp]: "[| x \<in> H; y \<in> H |] ==> x \<otimes> y \<in> H"

declare (in submagma) magma.intro [intro] semigroup.intro [intro]
  semigroup_axioms.intro [intro]

lemma submagma_imp_subset:
  "submagma H G ==> H \<subseteq> carrier G"
  by (rule submagma.subset)

lemma (in submagma) subsetD [dest, simp]:
  "x \<in> H ==> x \<in> carrier G"
  using subset by blast

lemma (in submagma) magmaI [intro]:
  includes magma G
  shows "magma (G(| carrier := H |))"
  by rule simp

lemma (in submagma) semigroup_axiomsI [intro]:
  includes semigroup G
  shows "semigroup_axioms (G(| carrier := H |))"
    by rule (simp add: m_assoc)

lemma (in submagma) semigroupI [intro]:
  includes semigroup G
  shows "semigroup (G(| carrier := H |))"
  using prems by fast


locale subgroup = submagma H G +
  assumes one_closed [intro, simp]: "\<one> \<in> H"
    and m_inv_closed [intro, simp]: "x \<in> H ==> inv x \<in> H"

declare (in subgroup) group.intro [intro]

lemma (in subgroup) group_axiomsI [intro]:
  includes group G
  shows "group_axioms (G(| carrier := H |))"
  by (rule group_axioms.intro) (auto intro: l_inv r_inv simp add: Units_def)

lemma (in subgroup) groupI [intro]:
  includes group G
  shows "group (G(| carrier := H |))"
  by (rule groupI) (auto intro: m_assoc l_inv)

text {*
  Since @{term H} is nonempty, it contains some element @{term x}.  Since
  it is closed under inverse, it contains @{text "inv x"}.  Since
  it is closed under product, it contains @{text "x \<otimes> inv x = \<one>"}.
*}

lemma (in group) one_in_subset:
  "[| H \<subseteq> carrier G; H \<noteq> {}; \<forall>a \<in> H. inv a \<in> H; \<forall>a\<in>H. \<forall>b\<in>H. a \<otimes> b \<in> H |]
   ==> \<one> \<in> H"
by (force simp add: l_inv)

text {* A characterization of subgroups: closed, non-empty subset. *}

lemma (in group) subgroupI:
  assumes subset: "H \<subseteq> carrier G" and non_empty: "H \<noteq> {}"
    and inv: "!!a. a \<in> H ==> inv a \<in> H"
    and mult: "!!a b. [|a \<in> H; b \<in> H|] ==> a \<otimes> b \<in> H"
  shows "subgroup H G"
proof (rule subgroup.intro)
  from subset and mult show "submagma H G" by (rule submagma.intro)
next
  have "\<one> \<in> H" by (rule one_in_subset) (auto simp only: prems)
  with inv show "subgroup_axioms H G"
    by (intro subgroup_axioms.intro) simp_all
qed

text {*
  Repeat facts of submagmas for subgroups.  Necessary???
*}

lemma (in subgroup) subset:
  "H \<subseteq> carrier G"
  ..

lemma (in subgroup) m_closed:
  "[| x \<in> H; y \<in> H |] ==> x \<otimes> y \<in> H"
  ..

declare magma.m_closed [simp]

declare monoid.one_closed [iff] group.inv_closed [simp]
  monoid.l_one [simp] monoid.r_one [simp] group.inv_inv [simp]

lemma subgroup_nonempty:
  "~ subgroup {} G"
  by (blast dest: subgroup.one_closed)

lemma (in subgroup) finite_imp_card_positive:
  "finite (carrier G) ==> 0 < card H"
proof (rule classical)
  have sub: "subgroup H G" using prems by (rule subgroup.intro)
  assume fin: "finite (carrier G)"
    and zero: "~ 0 < card H"
  then have "finite H" by (blast intro: finite_subset dest: subset)
  with zero sub have "subgroup {} G" by simp
  with subgroup_nonempty show ?thesis by contradiction
qed

(*
lemma (in monoid) Units_subgroup:
  "subgroup (Units G) G"
*)

subsection {* Direct Products *}

constdefs (structure G and H)
  DirProdSemigroup :: "_ => _ => ('a \<times> 'b) semigroup"  (infixr "\<times>\<^sub>s" 80)
  "G \<times>\<^sub>s H == (| carrier = carrier G \<times> carrier H,
    mult = (%(g, h) (g', h'). (g \<otimes>\<^bsub>G\<^esub> g', h \<otimes>\<^bsub>H\<^esub> h')) |)"

  DirProdGroup :: "_ => _ => ('a \<times> 'b) monoid"  (infixr "\<times>\<^sub>g" 80)
  "G \<times>\<^sub>g H == semigroup.extend (G \<times>\<^sub>s H) (| one = (\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>) |)"

lemma DirProdSemigroup_magma:
  includes magma G + magma H
  shows "magma (G \<times>\<^sub>s H)"
  by (rule magma.intro) (auto simp add: DirProdSemigroup_def)

lemma DirProdSemigroup_semigroup_axioms:
  includes semigroup G + semigroup H
  shows "semigroup_axioms (G \<times>\<^sub>s H)"
  by (rule semigroup_axioms.intro)
    (auto simp add: DirProdSemigroup_def G.m_assoc H.m_assoc)

lemma DirProdSemigroup_semigroup:
  includes semigroup G + semigroup H
  shows "semigroup (G \<times>\<^sub>s H)"
  using prems
  by (fast intro: semigroup.intro
    DirProdSemigroup_magma DirProdSemigroup_semigroup_axioms)

lemma DirProdGroup_magma:
  includes magma G + magma H
  shows "magma (G \<times>\<^sub>g H)"
  by (rule magma.intro)
    (auto simp add: DirProdGroup_def DirProdSemigroup_def semigroup.defs)

lemma DirProdGroup_semigroup_axioms:
  includes semigroup G + semigroup H
  shows "semigroup_axioms (G \<times>\<^sub>g H)"
  by (rule semigroup_axioms.intro)
    (auto simp add: DirProdGroup_def DirProdSemigroup_def semigroup.defs
      G.m_assoc H.m_assoc)

lemma DirProdGroup_semigroup:
  includes semigroup G + semigroup H
  shows "semigroup (G \<times>\<^sub>g H)"
  using prems
  by (fast intro: semigroup.intro
    DirProdGroup_magma DirProdGroup_semigroup_axioms)

text {* \dots\ and further lemmas for group \dots *}

lemma DirProdGroup_group:
  includes group G + group H
  shows "group (G \<times>\<^sub>g H)"
  by (rule groupI)
    (auto intro: G.m_assoc H.m_assoc G.l_inv H.l_inv
      simp add: DirProdGroup_def DirProdSemigroup_def semigroup.defs)

lemma carrier_DirProdGroup [simp]:
     "carrier (G \<times>\<^sub>g H) = carrier G \<times> carrier H"
  by (simp add: DirProdGroup_def DirProdSemigroup_def semigroup.defs)

lemma one_DirProdGroup [simp]:
     "\<one>\<^bsub>(G \<times>\<^sub>g H)\<^esub> = (\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>)"
  by (simp add: DirProdGroup_def DirProdSemigroup_def semigroup.defs)

lemma mult_DirProdGroup [simp]:
     "(g, h) \<otimes>\<^bsub>(G \<times>\<^sub>g H)\<^esub> (g', h') = (g \<otimes>\<^bsub>G\<^esub> g', h \<otimes>\<^bsub>H\<^esub> h')"
  by (simp add: DirProdGroup_def DirProdSemigroup_def semigroup.defs)

lemma inv_DirProdGroup [simp]:
  includes group G + group H
  assumes g: "g \<in> carrier G"
      and h: "h \<in> carrier H"
  shows "m_inv (G \<times>\<^sub>g H) (g, h) = (inv\<^bsub>G\<^esub> g, inv\<^bsub>H\<^esub> h)"
  apply (rule group.inv_equality [OF DirProdGroup_group])
  apply (simp_all add: prems group_def group.l_inv)
  done

subsection {* Homomorphisms *}

constdefs (structure G and H)
  hom :: "_ => _ => ('a => 'b) set"
  "hom G H ==
    {h. h \<in> carrier G -> carrier H &
      (\<forall>x \<in> carrier G. \<forall>y \<in> carrier G. h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y)}"

lemma (in semigroup) hom:
  includes semigroup G
  shows "semigroup (| carrier = hom G G, mult = op o |)"
proof (rule semigroup.intro)
  show "magma (| carrier = hom G G, mult = op o |)"
    by (rule magma.intro) (simp add: Pi_def hom_def)
next
  show "semigroup_axioms (| carrier = hom G G, mult = op o |)"
    by (rule semigroup_axioms.intro) (simp add: o_assoc)
qed

lemma hom_mult:
  "[| h \<in> hom G H; x \<in> carrier G; y \<in> carrier G |]
   ==> h (x \<otimes>\<^bsub>G\<^esub> y) = h x \<otimes>\<^bsub>H\<^esub> h y"
  by (simp add: hom_def)

lemma hom_closed:
  "[| h \<in> hom G H; x \<in> carrier G |] ==> h x \<in> carrier H"
  by (auto simp add: hom_def funcset_mem)

lemma compose_hom:
     "[|group G; h \<in> hom G G; h' \<in> hom G G; h' \<in> carrier G -> carrier G|]
      ==> compose (carrier G) h h' \<in> hom G G"
apply (simp (no_asm_simp) add: hom_def)
apply (intro conjI)
 apply (force simp add: funcset_compose hom_def)
apply (simp add: compose_def group.axioms hom_mult funcset_mem)
done

locale group_hom = group G + group H + var h +
  assumes homh: "h \<in> hom G H"
  notes hom_mult [simp] = hom_mult [OF homh]
    and hom_closed [simp] = hom_closed [OF homh]

lemma (in group_hom) one_closed [simp]:
  "h \<one> \<in> carrier H"
  by simp

lemma (in group_hom) hom_one [simp]:
  "h \<one> = \<one>\<^bsub>H\<^esub>"
proof -
  have "h \<one> \<otimes>\<^bsub>H\<^esub> \<one>\<^bsub>H\<^esub> = h \<one> \<otimes>\<^sub>2 h \<one>"
    by (simp add: hom_mult [symmetric] del: hom_mult)
  then show ?thesis by (simp del: r_one)
qed

lemma (in group_hom) inv_closed [simp]:
  "x \<in> carrier G ==> h (inv x) \<in> carrier H"
  by simp

lemma (in group_hom) hom_inv [simp]:
  "x \<in> carrier G ==> h (inv x) = inv\<^bsub>H\<^esub> (h x)"
proof -
  assume x: "x \<in> carrier G"
  then have "h x \<otimes>\<^bsub>H\<^esub> h (inv x) = \<one>\<^bsub>H\<^esub>"
    by (simp add: hom_mult [symmetric] G.r_inv del: hom_mult)
  also from x have "... = h x \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h x)"
    by (simp add: hom_mult [symmetric] H.r_inv del: hom_mult)
  finally have "h x \<otimes>\<^bsub>H\<^esub> h (inv x) = h x \<otimes>\<^bsub>H\<^esub> inv\<^bsub>H\<^esub> (h x)" .
  with x show ?thesis by simp
qed

subsection {* Commutative Structures *}

text {*
  Naming convention: multiplicative structures that are commutative
  are called \emph{commutative}, additive structures are called
  \emph{Abelian}.
*}

subsection {* Definition *}

locale comm_semigroup = semigroup +
  assumes m_comm: "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"

lemma (in comm_semigroup) m_lcomm:
  "[| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
   x \<otimes> (y \<otimes> z) = y \<otimes> (x \<otimes> z)"
proof -
  assume xyz: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
  from xyz have "x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z" by (simp add: m_assoc)
  also from xyz have "... = (y \<otimes> x) \<otimes> z" by (simp add: m_comm)
  also from xyz have "... = y \<otimes> (x \<otimes> z)" by (simp add: m_assoc)
  finally show ?thesis .
qed

lemmas (in comm_semigroup) m_ac = m_assoc m_comm m_lcomm

locale comm_monoid = comm_semigroup + monoid

lemma comm_monoidI:
  includes struct G
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
  by (auto intro!: comm_monoid.intro magma.intro semigroup_axioms.intro
    comm_semigroup_axioms.intro monoid_axioms.intro
    intro: prems simp: m_closed one_closed m_comm)

lemma (in monoid) monoid_comm_monoidI:
  assumes m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
  shows "comm_monoid G"
  by (rule comm_monoidI) (auto intro: m_assoc m_comm)
(*lemma (in comm_monoid) r_one [simp]:
  "x \<in> carrier G ==> x \<otimes> \<one> = x"
proof -
  assume G: "x \<in> carrier G"
  then have "x \<otimes> \<one> = \<one> \<otimes> x" by (simp add: m_comm)
  also from G have "... = x" by simp
  finally show ?thesis .
qed*)
lemma (in comm_monoid) nat_pow_distr:
  "[| x \<in> carrier G; y \<in> carrier G |] ==>
  (x \<otimes> y) (^) (n::nat) = x (^) n \<otimes> y (^) n"
  by (induct n) (simp, simp add: m_ac)

locale comm_group = comm_monoid + group

lemma (in group) group_comm_groupI:
  assumes m_comm: "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==>
      x \<otimes> y = y \<otimes> x"
  shows "comm_group G"
  by (fast intro: comm_group.intro comm_semigroup_axioms.intro
    group.axioms prems)

lemma comm_groupI:
  includes struct G
  assumes m_closed:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y \<in> carrier G"
    and one_closed: "\<one> \<in> carrier G"
    and m_assoc:
      "!!x y z. [| x \<in> carrier G; y \<in> carrier G; z \<in> carrier G |] ==>
      (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and m_comm:
      "!!x y. [| x \<in> carrier G; y \<in> carrier G |] ==> x \<otimes> y = y \<otimes> x"
    and l_one: "!!x. x \<in> carrier G ==> \<one> \<otimes> x = x"
    and l_inv_ex: "!!x. x \<in> carrier G ==> EX y : carrier G. y \<otimes> x = \<one>"
  shows "comm_group G"
  by (fast intro: group.group_comm_groupI groupI prems)

lemma (in comm_group) inv_mult:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> inv (x \<otimes> y) = inv x \<otimes> inv y"
  by (simp add: m_ac inv_mult_group)

subsection {* Lattice of subgroups of a group *}

text_raw {* \label{sec:subgroup-lattice} *}

theorem (in group) subgroups_partial_order:
  "partial_order (| carrier = {H. subgroup H G}, le = op \<subseteq> |)"
  by (rule partial_order.intro) simp_all

lemma (in group) subgroup_self:
  "subgroup (carrier G) G"
  by (rule subgroupI) auto

lemma (in group) subgroup_imp_group:
  "subgroup H G ==> group (G(| carrier := H |))"
  using subgroup.groupI [OF _ group.intro] .

lemma (in group) is_monoid [intro, simp]:
  "monoid G"
  by (rule monoid.intro)

lemma (in group) subgroup_inv_equality:
  "[| subgroup H G; x \<in> H |] ==> m_inv (G (| carrier := H |)) x = inv x"
apply (rule_tac inv_equality [THEN sym])
  apply (rule group.l_inv [OF subgroup_imp_group, simplified])
   apply assumption+
 apply (rule subsetD [OF subgroup.subset])
  apply assumption+
apply (rule subsetD [OF subgroup.subset])
 apply assumption
apply (rule_tac group.inv_closed [OF subgroup_imp_group, simplified])
  apply assumption+
done

theorem (in group) subgroups_Inter:
  assumes subgr: "(!!H. H \<in> A ==> subgroup H G)"
    and not_empty: "A ~= {}"
  shows "subgroup (\<Inter>A) G"
proof (rule subgroupI)
  from subgr [THEN subgroup.subset] and not_empty
  show "\<Inter>A \<subseteq> carrier G" by blast
next
  from subgr [THEN subgroup.one_closed]
  show "\<Inter>A ~= {}" by blast
next
  fix x assume "x \<in> \<Inter>A"
  with subgr [THEN subgroup.m_inv_closed]
  show "inv x \<in> \<Inter>A" by blast
next
  fix x y assume "x \<in> \<Inter>A" "y \<in> \<Inter>A"
  with subgr [THEN subgroup.m_closed]
  show "x \<otimes> y \<in> \<Inter>A" by blast
qed

theorem (in group) subgroups_complete_lattice:
  "complete_lattice (| carrier = {H. subgroup H G}, le = op \<subseteq> |)"
    (is "complete_lattice ?L")
proof (rule partial_order.complete_lattice_criterion1)
  show "partial_order ?L" by (rule subgroups_partial_order)
next
  have "greatest ?L (carrier G) (carrier ?L)"
    by (unfold greatest_def) (simp add: subgroup.subset subgroup_self)
  then show "EX G. greatest ?L G (carrier ?L)" ..
next
  fix A
  assume L: "A \<subseteq> carrier ?L" and non_empty: "A ~= {}"
  then have Int_subgroup: "subgroup (\<Inter>A) G"
    by (fastsimp intro: subgroups_Inter)
  have "greatest ?L (\<Inter>A) (Lower ?L A)"
    (is "greatest ?L ?Int _")
  proof (rule greatest_LowerI)
    fix H
    assume H: "H \<in> A"
    with L have subgroupH: "subgroup H G" by auto
    from subgroupH have submagmaH: "submagma H G" by (rule subgroup.axioms)
    from subgroupH have groupH: "group (G (| carrier := H |))" (is "group ?H")
      by (rule subgroup_imp_group)
    from groupH have monoidH: "monoid ?H"
      by (rule group.is_monoid)
    from H have Int_subset: "?Int \<subseteq> H" by fastsimp
    then show "le ?L ?Int H" by simp
  next
    fix H
    assume H: "H \<in> Lower ?L A"
    with L Int_subgroup show "le ?L H ?Int" by (fastsimp intro: Inter_greatest)
  next
    show "A \<subseteq> carrier ?L" by (rule L)
  next
    show "?Int \<in> carrier ?L" by simp (rule Int_subgroup)
  qed
  then show "EX I. greatest ?L I (Lower ?L A)" ..
qed

end
