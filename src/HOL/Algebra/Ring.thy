(*  Title:      HOL/Algebra/Ring.thy
    Author:     Clemens Ballarin, started 9 December 1996

With contributions by Martin Baillon.
*)

theory Ring
imports FiniteProduct
begin

section \<open>The Algebraic Hierarchy of Rings\<close>

subsection \<open>Abelian Groups\<close>

record 'a ring = "'a monoid" +
  zero :: 'a (\<open>\<zero>\<index>\<close>)
  add :: "['a, 'a] \<Rightarrow> 'a" (infixl \<open>\<oplus>\<index>\<close> 65)

abbreviation
  add_monoid :: "('a, 'm) ring_scheme \<Rightarrow> ('a, 'm) monoid_scheme"
  where "add_monoid R \<equiv> \<lparr> carrier = carrier R, mult = add R, one = zero R, \<dots> = (undefined :: 'm) \<rparr>"

text \<open>Derived operations.\<close>

definition
  a_inv :: "[('a, 'm) ring_scheme, 'a ] \<Rightarrow> 'a" (\<open>(\<open>open_block notation=\<open>prefix \<ominus>\<close>\<close>\<ominus>\<index> _)\<close> [81] 80)
  where "a_inv R = m_inv (add_monoid R)"

definition
  a_minus :: "[('a, 'm) ring_scheme, 'a, 'a] => 'a" (\<open>(\<open>notation=\<open>infix \<ominus>\<close>\<close>_ \<ominus>\<index> _)\<close> [65,66] 65)
  where "x \<ominus>\<^bsub>R\<^esub> y = x \<oplus>\<^bsub>R\<^esub> (\<ominus>\<^bsub>R\<^esub> y)"

definition
  add_pow :: "[_, ('b :: semiring_1), 'a] \<Rightarrow> 'a"
    (\<open>(\<open>open_block notation=\<open>mixfix \<cdot>\<close>\<close>[_] \<cdot>\<index> _)\<close> [81, 81] 80)
  where "[k] \<cdot>\<^bsub>R\<^esub> a = pow (add_monoid R) a k"

locale abelian_monoid =
  fixes G (structure)
  assumes a_comm_monoid:
     "comm_monoid (add_monoid G)"

definition
  finsum :: "[('b, 'm) ring_scheme, 'a \<Rightarrow> 'b, 'a set] \<Rightarrow> 'b" where
  "finsum G = finprod (add_monoid G)"

syntax
  "_finsum" :: "index \<Rightarrow> idt \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"
    (\<open>(\<open>indent=3 notation=\<open>binder \<Oplus>\<close>\<close>\<Oplus>__\<in>_. _)\<close> [1000, 0, 51, 10] 10)
syntax_consts
  "_finsum" \<rightleftharpoons> finsum
translations
  "\<Oplus>\<^bsub>G\<^esub>i\<in>A. b" \<rightleftharpoons> "CONST finsum G (\<lambda>i. b) A"
  \<comment> \<open>Beware of argument permutation!\<close>


locale abelian_group = abelian_monoid +
  assumes a_comm_group:
     "comm_group (add_monoid G)"


subsection \<open>Basic Properties\<close>

lemma abelian_monoidI:
  fixes R (structure)
  assumes "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> x \<oplus> y \<in> carrier R"
      and "\<zero> \<in> carrier R"
      and "\<And>x y z. \<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
      and "\<And>x. x \<in> carrier R \<Longrightarrow> \<zero> \<oplus> x = x"
      and "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> x \<oplus> y = y \<oplus> x"
  shows "abelian_monoid R"
  by (auto intro!: abelian_monoid.intro comm_monoidI intro: assms)

lemma abelian_monoidE:
  fixes R (structure)
  assumes "abelian_monoid R"
  shows "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> x \<oplus> y \<in> carrier R"
    and "\<zero> \<in> carrier R"
    and "\<And>x y z. \<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
    and "\<And>x. x \<in> carrier R \<Longrightarrow> \<zero> \<oplus> x = x"
    and "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> x \<oplus> y = y \<oplus> x"
  using assms unfolding abelian_monoid_def comm_monoid_def comm_monoid_axioms_def monoid_def by auto

lemma abelian_groupI:
  fixes R (structure)
  assumes "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> x \<oplus> y \<in> carrier R"
      and "\<zero> \<in> carrier R"
      and "\<And>x y z. \<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
      and "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> x \<oplus> y = y \<oplus> x"
      and "\<And>x. x \<in> carrier R \<Longrightarrow> \<zero> \<oplus> x = x"
      and "\<And>x. x \<in> carrier R \<Longrightarrow> \<exists>y \<in> carrier R. y \<oplus> x = \<zero>"
  shows "abelian_group R"
  by (auto intro!: abelian_group.intro abelian_monoidI
      abelian_group_axioms.intro comm_monoidI comm_groupI
    intro: assms)

lemma abelian_groupE:
  fixes R (structure)
  assumes "abelian_group R"
  shows "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> x \<oplus> y \<in> carrier R"
    and "\<zero> \<in> carrier R"
    and "\<And>x y z. \<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<oplus> y) \<oplus> z = x \<oplus> (y \<oplus> z)"
    and "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> x \<oplus> y = y \<oplus> x"
    and "\<And>x. x \<in> carrier R \<Longrightarrow> \<zero> \<oplus> x = x"
    and "\<And>x. x \<in> carrier R \<Longrightarrow> \<exists>y \<in> carrier R. y \<oplus> x = \<zero>"
  using abelian_group.a_comm_group assms comm_groupE by fastforce+

lemma (in abelian_monoid) a_monoid:
  "monoid (add_monoid G)"
by (rule comm_monoid.axioms, rule a_comm_monoid)

lemma (in abelian_group) a_group:
  "group (add_monoid G)"
  by (simp add: group_def a_monoid)
    (simp add: comm_group.axioms group.axioms a_comm_group)

lemmas monoid_record_simps = partial_object.simps monoid.simps

text \<open>Transfer facts from multiplicative structures via interpretation.\<close>

sublocale abelian_monoid <
       add: monoid "(add_monoid G)"
  rewrites "carrier (add_monoid G) = carrier G"
       and "mult    (add_monoid G) = add G"
       and "one     (add_monoid G) = zero G"
       and "(\<lambda>a k. pow (add_monoid G) a k) = (\<lambda>a k. add_pow G k a)"
  by (rule a_monoid) (auto simp add: add_pow_def)

context abelian_monoid
begin

lemmas a_closed = add.m_closed
lemmas zero_closed = add.one_closed
lemmas a_assoc = add.m_assoc
lemmas l_zero = add.l_one
lemmas r_zero = add.r_one
lemmas minus_unique = add.inv_unique

end

sublocale abelian_monoid <
  add: comm_monoid "(add_monoid G)"
  rewrites "carrier (add_monoid G) = carrier G"
       and "mult    (add_monoid G) = add G"
       and "one     (add_monoid G) = zero G"
       and "finprod (add_monoid G) = finsum G"
       and "pow     (add_monoid G) = (\<lambda>a k. add_pow G k a)"
  by (rule a_comm_monoid) (auto simp: finsum_def add_pow_def)

context abelian_monoid begin

lemmas a_comm = add.m_comm
lemmas a_lcomm = add.m_lcomm
lemmas a_ac = a_assoc a_comm a_lcomm

lemmas finsum_empty = add.finprod_empty
lemmas finsum_insert = add.finprod_insert
lemmas finsum_zero = add.finprod_one
lemmas finsum_closed = add.finprod_closed
lemmas finsum_Un_Int = add.finprod_Un_Int
lemmas finsum_Un_disjoint = add.finprod_Un_disjoint
lemmas finsum_addf = add.finprod_multf
lemmas finsum_cong' = add.finprod_cong'
lemmas finsum_0 = add.finprod_0
lemmas finsum_Suc = add.finprod_Suc
lemmas finsum_Suc2 = add.finprod_Suc2
lemmas finsum_infinite = add.finprod_infinite

lemmas finsum_cong = add.finprod_cong
text \<open>Usually, if this rule causes a failed congruence proof error,
   the reason is that the premise \<open>g \<in> B \<rightarrow> carrier G\<close> cannot be shown.
   Adding @{thm [source] Pi_def} to the simpset is often useful.\<close>

lemmas finsum_reindex = add.finprod_reindex

(* The following would be wrong.  Needed is the equivalent of [^] for addition,
  or indeed the canonical embedding from Nat into the monoid.

lemma finsum_const:
  assumes fin [simp]: "finite A"
      and a [simp]: "a : carrier G"
    shows "finsum G (%x. a) A = a [^] card A"
  using fin apply induct
  apply force
  apply (subst finsum_insert)
  apply auto
  apply (force simp add: Pi_def)
  apply (subst m_comm)
  apply auto
done
*)

lemmas finsum_singleton = add.finprod_singleton

end

sublocale abelian_group <
        add: group "(add_monoid G)"
  rewrites "carrier (add_monoid G) = carrier G"
       and "mult    (add_monoid G) = add G"
       and "one     (add_monoid G) = zero G"
       and "m_inv   (add_monoid G) = a_inv G"
       and "pow     (add_monoid G) = (\<lambda>a k. add_pow G k a)"
  by (rule a_group) (auto simp: m_inv_def a_inv_def add_pow_def)

context abelian_group
begin

lemmas a_inv_closed = add.inv_closed

lemma minus_closed [intro, simp]:
  "[| x \<in> carrier G; y \<in> carrier G |] ==> x \<ominus> y \<in> carrier G"
  by (simp add: a_minus_def)

lemmas l_neg = add.l_inv [simp del]
lemmas r_neg = add.r_inv [simp del]
lemmas minus_minus = add.inv_inv
lemmas a_inv_inj = add.inv_inj
lemmas minus_equality = add.inv_equality

end

sublocale abelian_group <
   add: comm_group "(add_monoid G)"
  rewrites "carrier (add_monoid G) = carrier G"
       and "mult    (add_monoid G) = add G"
       and "one     (add_monoid G) = zero G"
       and "m_inv   (add_monoid G) = a_inv G"
       and "finprod (add_monoid G) = finsum G"
       and "pow     (add_monoid G) = (\<lambda>a k. add_pow G k a)"
  by (rule a_comm_group) (auto simp: m_inv_def a_inv_def finsum_def add_pow_def)

lemmas (in abelian_group) minus_add = add.inv_mult

text \<open>Derive an \<open>abelian_group\<close> from a \<open>comm_group\<close>\<close>

lemma comm_group_abelian_groupI:
  fixes G (structure)
  assumes cg: "comm_group (add_monoid G)"
  shows "abelian_group G"
proof -
  interpret comm_group "(add_monoid G)"
    by (rule cg)
  show "abelian_group G" ..
qed


subsection \<open>Rings: Basic Definitions\<close>

locale semiring = abelian_monoid (* for add *) R + monoid (* for mult *) R for R (structure) +
  assumes l_distr: "\<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
      and r_distr: "\<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y"
      and l_null[simp]: "x \<in> carrier R \<Longrightarrow> \<zero> \<otimes> x = \<zero>"
      and r_null[simp]: "x \<in> carrier R \<Longrightarrow> x \<otimes> \<zero> = \<zero>"

locale ring = abelian_group (* for add *) R + monoid (* for mult *) R for R (structure) +
  assumes "\<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
      and "\<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y"

locale cring = ring + comm_monoid (* for mult *) R

locale "domain" = cring +
  assumes one_not_zero [simp]: "\<one> \<noteq> \<zero>"
      and integral: "\<lbrakk> a \<otimes> b = \<zero>; a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow> a = \<zero> \<or> b = \<zero>"

locale field = "domain" +
  assumes field_Units: "Units R = carrier R - {\<zero>}"


subsection \<open>Rings\<close>

lemma ringI:
  fixes R (structure)
  assumes "abelian_group R"
      and "monoid R"
      and "\<And>x y z. \<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
      and "\<And>x y z. \<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y"
  shows "ring R"
  by (auto intro: ring.intro
    abelian_group.axioms ring_axioms.intro assms)

lemma ringE:
  fixes R (structure)
  assumes "ring R"
  shows "abelian_group R"
    and "monoid R"
    and "\<And>x y z. \<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
    and "\<And>x y z. \<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y"
  using assms unfolding ring_def ring_axioms_def by auto

context ring begin

lemma is_abelian_group: "abelian_group R" ..

lemma is_monoid: "monoid R"
  by (auto intro!: monoidI m_assoc)

end

thm monoid_record_simps
lemmas ring_record_simps = monoid_record_simps ring.simps

lemma cringI:
  fixes R (structure)
  assumes abelian_group: "abelian_group R"
    and comm_monoid: "comm_monoid R"
    and l_distr: "\<And>x y z. \<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow>
                            (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
  shows "cring R"
proof (intro cring.intro ring.intro)
  show "ring_axioms R"
    \<comment> \<open>Right-distributivity follows from left-distributivity and
          commutativity.\<close>
  proof (rule ring_axioms.intro)
    fix x y z
    assume R: "x \<in> carrier R" "y \<in> carrier R" "z \<in> carrier R"
    note [simp] = comm_monoid.axioms [OF comm_monoid]
      abelian_group.axioms [OF abelian_group]
      abelian_monoid.a_closed

    from R have "z \<otimes> (x \<oplus> y) = (x \<oplus> y) \<otimes> z"
      by (simp add: comm_monoid.m_comm [OF comm_monoid.intro])
    also from R have "... = x \<otimes> z \<oplus> y \<otimes> z" by (simp add: l_distr)
    also from R have "... = z \<otimes> x \<oplus> z \<otimes> y"
      by (simp add: comm_monoid.m_comm [OF comm_monoid.intro])
    finally show "z \<otimes> (x \<oplus> y) = z \<otimes> x \<oplus> z \<otimes> y" .
  qed (rule l_distr)
qed (auto intro: cring.intro
  abelian_group.axioms comm_monoid.axioms ring_axioms.intro assms)

lemma cringE:
  fixes R (structure)
  assumes "cring R"
  shows "comm_monoid R"
    and "\<And>x y z. \<lbrakk> x \<in> carrier R; y \<in> carrier R; z \<in> carrier R \<rbrakk> \<Longrightarrow> (x \<oplus> y) \<otimes> z = x \<otimes> z \<oplus> y \<otimes> z"
  using assms cring_def by auto (simp add: assms cring.axioms(1) ringE(3))

lemma (in cring) is_cring:
  "cring R" by (rule cring_axioms)

lemma (in ring) minus_zero [simp]: "\<ominus> \<zero> = \<zero>"
  by (simp add: a_inv_def)

subsubsection \<open>Normaliser for Rings\<close>

lemma (in abelian_group) r_neg1:
  "\<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> (\<ominus> x) \<oplus> (x \<oplus> y) = y"
proof -
  assume G: "x \<in> carrier G" "y \<in> carrier G"
  then have "(\<ominus> x \<oplus> x) \<oplus> y = y"
    by (simp only: l_neg l_zero)
  with G show ?thesis by (simp add: a_ac)
qed

lemma (in abelian_group) r_neg2:
  "\<lbrakk> x \<in> carrier G; y \<in> carrier G \<rbrakk> \<Longrightarrow> x \<oplus> ((\<ominus> x) \<oplus> y) = y"
proof -
  assume G: "x \<in> carrier G" "y \<in> carrier G"
  then have "(x \<oplus> \<ominus> x) \<oplus> y = y"
    by (simp only: r_neg l_zero)
  with G show ?thesis
    by (simp add: a_ac)
qed

context ring begin

text \<open>
  The following proofs are from Jacobson, Basic Algebra I, pp.~88--89.
\<close>

sublocale semiring
proof -
  note [simp] = ring_axioms[unfolded ring_def ring_axioms_def]
  show "semiring R"
  proof (unfold_locales)
    fix x
    assume R: "x \<in> carrier R"
    then have "\<zero> \<otimes> x \<oplus> \<zero> \<otimes> x = (\<zero> \<oplus> \<zero>) \<otimes> x"
      by (simp del: l_zero r_zero)
    also from R have "... = \<zero> \<otimes> x \<oplus> \<zero>" by simp
    finally have "\<zero> \<otimes> x \<oplus> \<zero> \<otimes> x = \<zero> \<otimes> x \<oplus> \<zero>" .
    with R show "\<zero> \<otimes> x = \<zero>" by (simp del: r_zero)
    from R have "x \<otimes> \<zero> \<oplus> x \<otimes> \<zero> = x \<otimes> (\<zero> \<oplus> \<zero>)"
      by (simp del: l_zero r_zero)
    also from R have "... = x \<otimes> \<zero> \<oplus> \<zero>" by simp
    finally have "x \<otimes> \<zero> \<oplus> x \<otimes> \<zero> = x \<otimes> \<zero> \<oplus> \<zero>" .
    with R show "x \<otimes> \<zero> = \<zero>" by (simp del: r_zero)
  qed auto
qed

lemma l_minus:
  "\<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> (\<ominus> x) \<otimes> y = \<ominus> (x \<otimes> y)"
proof -
  assume R: "x \<in> carrier R" "y \<in> carrier R"
  then have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = (\<ominus> x \<oplus> x) \<otimes> y" by (simp add: l_distr)
  also from R have "... = \<zero>" by (simp add: l_neg)
  finally have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y = \<zero>" .
  with R have "(\<ominus> x) \<otimes> y \<oplus> x \<otimes> y \<oplus> \<ominus> (x \<otimes> y) = \<zero> \<oplus> \<ominus> (x \<otimes> y)" by simp
  with R show ?thesis by (simp add: a_assoc r_neg)
qed

lemma r_minus:
  "\<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> x \<otimes> (\<ominus> y) = \<ominus> (x \<otimes> y)"
proof -
  assume R: "x \<in> carrier R" "y \<in> carrier R"
  then have "x \<otimes> (\<ominus> y) \<oplus> x \<otimes> y = x \<otimes> (\<ominus> y \<oplus> y)" by (simp add: r_distr)
  also from R have "... = \<zero>" by (simp add: l_neg)
  finally have "x \<otimes> (\<ominus> y) \<oplus> x \<otimes> y = \<zero>" .
  with R have "x \<otimes> (\<ominus> y) \<oplus> x \<otimes> y \<oplus> \<ominus> (x \<otimes> y) = \<zero> \<oplus> \<ominus> (x \<otimes> y)" by simp
  with R show ?thesis by (simp add: a_assoc r_neg )
qed

end

lemma (in abelian_group) minus_eq: "x \<ominus> y = x \<oplus> (\<ominus> y)"
  by (rule a_minus_def)

text \<open>Setup algebra method:
  compute distributive normal form in locale contexts\<close>


ML_file \<open>ringsimp.ML\<close>

attribute_setup algebra = \<open>
  Scan.lift ((Args.add >> K true || Args.del >> K false) --| Args.colon || Scan.succeed true)
    -- Scan.lift Args.name -- Scan.repeat Args.term
    >> (fn ((b, n), ts) => if b then Ringsimp.add_struct (n, ts) else Ringsimp.del_struct (n, ts))
\<close> "theorems controlling algebra method"

method_setup algebra = \<open>
  Scan.succeed (SIMPLE_METHOD' o Ringsimp.algebra_tac)
\<close> "normalisation of algebraic structure"

lemmas (in semiring) semiring_simprules
  [algebra ring "zero R" "add R" "a_inv R" "a_minus R" "one R" "mult R"] =
  a_closed zero_closed  m_closed one_closed
  a_assoc l_zero  a_comm m_assoc l_one l_distr r_zero
  a_lcomm r_distr l_null r_null

lemmas (in ring) ring_simprules
  [algebra ring "zero R" "add R" "a_inv R" "a_minus R" "one R" "mult R"] =
  a_closed zero_closed a_inv_closed minus_closed m_closed one_closed
  a_assoc l_zero l_neg a_comm m_assoc l_one l_distr minus_eq
  r_zero r_neg r_neg2 r_neg1 minus_add minus_minus minus_zero
  a_lcomm r_distr l_null r_null l_minus r_minus

lemmas (in cring)
  [algebra del: ring "zero R" "add R" "a_inv R" "a_minus R" "one R" "mult R"] =
  _

lemmas (in cring) cring_simprules
  [algebra add: cring "zero R" "add R" "a_inv R" "a_minus R" "one R" "mult R"] =
  a_closed zero_closed a_inv_closed minus_closed m_closed one_closed
  a_assoc l_zero l_neg a_comm m_assoc l_one l_distr m_comm minus_eq
  r_zero r_neg r_neg2 r_neg1 minus_add minus_minus minus_zero
  a_lcomm m_lcomm r_distr l_null r_null l_minus r_minus

lemma (in semiring) nat_pow_zero:
  "(n::nat) \<noteq> 0 \<Longrightarrow> \<zero> [^] n = \<zero>"
  by (induct n) simp_all

context semiring begin

lemma one_zeroD:
  assumes onezero: "\<one> = \<zero>"
  shows "carrier R = {\<zero>}"
proof (rule, rule)
  fix x
  assume xcarr: "x \<in> carrier R"
  from xcarr have "x = x \<otimes> \<one>" by simp
  with onezero have "x = x \<otimes> \<zero>" by simp
  with xcarr have "x = \<zero>" by simp
  then show "x \<in> {\<zero>}" by fast
qed fast

lemma one_zeroI:
  assumes carrzero: "carrier R = {\<zero>}"
  shows "\<one> = \<zero>"
proof -
  from one_closed and carrzero
      show "\<one> = \<zero>" by simp
qed

lemma carrier_one_zero: "(carrier R = {\<zero>}) = (\<one> = \<zero>)"
  using one_zeroD by blast

lemma carrier_one_not_zero: "(carrier R \<noteq> {\<zero>}) = (\<one> \<noteq> \<zero>)"
  by (simp add: carrier_one_zero)

end

text \<open>Two examples for use of method algebra\<close>

lemma
  fixes R (structure) and S (structure)
  assumes "ring R" "cring S"
  assumes RS: "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier S" "d \<in> carrier S"
  shows "a \<oplus> (\<ominus> (a \<oplus> (\<ominus> b))) = b \<and> c \<otimes>\<^bsub>S\<^esub> d = d \<otimes>\<^bsub>S\<^esub> c"
proof -
  interpret ring R by fact
  interpret cring S by fact
  from RS show ?thesis by algebra
qed

lemma
  fixes R (structure)
  assumes "ring R"
  assumes R: "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<ominus> (a \<ominus> b) = b"
proof -
  interpret ring R by fact
  from R show ?thesis by algebra
qed


subsubsection \<open>Sums over Finite Sets\<close>

lemma (in semiring) finsum_ldistr:
  "\<lbrakk> finite A; a \<in> carrier R; f: A \<rightarrow> carrier R \<rbrakk> \<Longrightarrow>
    (\<Oplus> i \<in> A. (f i)) \<otimes> a = (\<Oplus> i \<in> A. ((f i) \<otimes> a))"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert x F) then show ?case by (simp add: Pi_def l_distr)
qed

lemma (in semiring) finsum_rdistr:
  "\<lbrakk> finite A; a \<in> carrier R; f: A \<rightarrow> carrier R \<rbrakk> \<Longrightarrow>
   a \<otimes> (\<Oplus> i \<in> A. (f i)) = (\<Oplus> i \<in> A. (a \<otimes> (f i)))"
proof (induct set: finite)
  case empty then show ?case by simp
next
  case (insert x F) then show ?case by (simp add: Pi_def r_distr)
qed


text \<open>A quick detour\<close>

lemma add_pow_int_ge: "(k :: int) \<ge> 0 \<Longrightarrow> [ k ] \<cdot>\<^bsub>R\<^esub> a = [ nat k ] \<cdot>\<^bsub>R\<^esub> a" \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  by (simp add: add_pow_def int_pow_def nat_pow_def)

lemma add_pow_int_lt: "(k :: int) < 0 \<Longrightarrow> [ k ] \<cdot>\<^bsub>R\<^esub> a = \<ominus>\<^bsub>R\<^esub> ([ nat (- k) ] \<cdot>\<^bsub>R\<^esub> a)" \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  by (simp add: int_pow_def nat_pow_def a_inv_def add_pow_def)

corollary (in semiring) add_pow_ldistr: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "([(k :: nat)] \<cdot> a) \<otimes> b = [k] \<cdot> (a \<otimes> b)"
proof -
  have "([k] \<cdot> a) \<otimes> b = (\<Oplus> i \<in> {..< k}. a) \<otimes> b"
    using add.finprod_const[OF assms(1), of "{..<k}"] by simp
  also have " ... = (\<Oplus> i \<in> {..< k}. (a \<otimes> b))"
    using finsum_ldistr[of "{..<k}" b "\<lambda>x. a"] assms by simp
  also have " ... = [k] \<cdot> (a \<otimes> b)"
    using add.finprod_const[of "a \<otimes> b" "{..<k}"] assms by simp
  finally show ?thesis .
qed

corollary (in semiring) add_pow_rdistr: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<otimes> ([(k :: nat)] \<cdot> b) = [k] \<cdot> (a \<otimes> b)"
proof -
  have "a \<otimes> ([k] \<cdot> b) = a \<otimes> (\<Oplus> i \<in> {..< k}. b)"
    using add.finprod_const[OF assms(2), of "{..<k}"] by simp
  also have " ... = (\<Oplus> i \<in> {..< k}. (a \<otimes> b))"
    using finsum_rdistr[of "{..<k}" a "\<lambda>x. b"] assms by simp
  also have " ... = [k] \<cdot> (a \<otimes> b)"
    using add.finprod_const[of "a \<otimes> b" "{..<k}"] assms by simp
  finally show ?thesis .
qed

(* For integers, we need the uniqueness of the additive inverse *)
lemma (in ring) add_pow_ldistr_int: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "([(k :: int)] \<cdot> a) \<otimes> b = [k] \<cdot> (a \<otimes> b)"
proof (cases "k \<ge> 0")
  case True thus ?thesis
    using add_pow_int_ge[of k R] add_pow_ldistr[OF assms] by auto
next
  case False thus ?thesis
    using add_pow_int_lt[of k R a] add_pow_int_lt[of k R "a \<otimes> b"]
          add_pow_ldistr[OF assms, of "nat (- k)"] assms l_minus by auto
qed

lemma (in ring) add_pow_rdistr_int: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "a \<in> carrier R" "b \<in> carrier R"
  shows "a \<otimes> ([(k :: int)] \<cdot> b) = [k] \<cdot> (a \<otimes> b)"
proof (cases "k \<ge> 0")
  case True thus ?thesis
    using add_pow_int_ge[of k R] add_pow_rdistr[OF assms] by auto
next
  case False thus ?thesis
    using add_pow_int_lt[of k R b] add_pow_int_lt[of k R "a \<otimes> b"]
          add_pow_rdistr[OF assms, of "nat (- k)"] assms r_minus by auto
qed


subsection \<open>Integral Domains\<close>

context "domain" begin

lemma zero_not_one [simp]: "\<zero> \<noteq> \<one>"
  by (rule not_sym) simp

lemma integral_iff: (* not by default a simp rule! *)
  "\<lbrakk> a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow> (a \<otimes> b = \<zero>) = (a = \<zero> \<or> b = \<zero>)"
proof
  assume "a \<in> carrier R" "b \<in> carrier R" "a \<otimes> b = \<zero>"
  then show "a = \<zero> \<or> b = \<zero>" by (simp add: integral)
next
  assume "a \<in> carrier R" "b \<in> carrier R" "a = \<zero> \<or> b = \<zero>"
  then show "a \<otimes> b = \<zero>" by auto
qed

lemma m_lcancel:
  assumes prem: "a \<noteq> \<zero>"
    and R: "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows "(a \<otimes> b = a \<otimes> c) = (b = c)"
proof
  assume eq: "a \<otimes> b = a \<otimes> c"
  with R have "a \<otimes> (b \<ominus> c) = \<zero>" by algebra
  with R have "a = \<zero> \<or> (b \<ominus> c) = \<zero>" by (simp add: integral_iff)
  with prem and R have "b \<ominus> c = \<zero>" by auto
  with R have "b = b \<ominus> (b \<ominus> c)" by algebra
  also from R have "b \<ominus> (b \<ominus> c) = c" by algebra
  finally show "b = c" .
next
  assume "b = c" then show "a \<otimes> b = a \<otimes> c" by simp
qed

lemma m_rcancel:
  assumes prem: "a \<noteq> \<zero>"
    and R: "a \<in> carrier R" "b \<in> carrier R" "c \<in> carrier R"
  shows conc: "(b \<otimes> a = c \<otimes> a) = (b = c)"
proof -
  from prem and R have "(a \<otimes> b = a \<otimes> c) = (b = c)" by (rule m_lcancel)
  with R show ?thesis by algebra
qed

end


subsection \<open>Fields\<close>

text \<open>Field would not need to be derived from domain, the properties
  for domain follow from the assumptions of field\<close>

lemma (in field) is_ring: "ring R"
  using ring_axioms .

lemma fieldE :
  fixes R (structure)
  assumes "field R"
  shows "cring R"
    and one_not_zero : "\<one> \<noteq> \<zero>"
    and integral: "\<And>a b. \<lbrakk> a \<otimes> b = \<zero>; a \<in> carrier R; b \<in> carrier R \<rbrakk> \<Longrightarrow> a = \<zero> \<or> b = \<zero>"
  and field_Units: "Units R = carrier R - {\<zero>}"
  using assms unfolding field_def field_axioms_def domain_def domain_axioms_def by simp_all

lemma (in cring) cring_fieldI:
  assumes field_Units: "Units R = carrier R - {\<zero>}"
  shows "field R"
proof
  from field_Units have "\<zero> \<notin> Units R" by fast
  moreover have "\<one> \<in> Units R" by fast
  ultimately show "\<one> \<noteq> \<zero>" by force
next
  fix a b
  assume acarr: "a \<in> carrier R"
    and bcarr: "b \<in> carrier R"
    and ab: "a \<otimes> b = \<zero>"
  show "a = \<zero> \<or> b = \<zero>"
  proof (cases "a = \<zero>", simp)
    assume "a \<noteq> \<zero>"
    with field_Units and acarr have aUnit: "a \<in> Units R" by fast
    from bcarr have "b = \<one> \<otimes> b" by algebra
    also from aUnit acarr have "... = (inv a \<otimes> a) \<otimes> b" by simp
    also from acarr bcarr aUnit[THEN Units_inv_closed]
    have "... = (inv a) \<otimes> (a \<otimes> b)" by algebra
    also from ab and acarr bcarr aUnit have "... = (inv a) \<otimes> \<zero>" by simp
    also from aUnit[THEN Units_inv_closed] have "... = \<zero>" by algebra
    finally have "b = \<zero>" .
    then show "a = \<zero> \<or> b = \<zero>" by simp
  qed
qed (rule field_Units)

text \<open>Another variant to show that something is a field\<close>
lemma (in cring) cring_fieldI2:
  assumes notzero: "\<zero> \<noteq> \<one>"
    and invex: "\<And>a. \<lbrakk>a \<in> carrier R; a \<noteq> \<zero>\<rbrakk> \<Longrightarrow> \<exists>b\<in>carrier R. a \<otimes> b = \<one>"
  shows "field R"
proof -
  have *: "carrier R - {\<zero>} \<subseteq> {y \<in> carrier R. \<exists>x\<in>carrier R. x \<otimes> y = \<one> \<and> y \<otimes> x = \<one>}"
  proof (clarsimp)
    fix x
    assume xcarr: "x \<in> carrier R" and "x \<noteq> \<zero>"
    obtain y where ycarr: "y \<in> carrier R" and xy: "x \<otimes> y = \<one>"
      using \<open>x \<noteq> \<zero>\<close> invex xcarr by blast 
    with ycarr and xy show "\<exists>y\<in>carrier R. y \<otimes> x = \<one> \<and> x \<otimes> y = \<one>"
      using m_comm xcarr by fastforce 
  qed
  show ?thesis
    apply (rule cring_fieldI, simp add: Units_def)
    using *
    using group_l_invI notzero set_diff_eq by auto
qed


subsection \<open>Morphisms\<close>

definition
  ring_hom :: "[('a, 'm) ring_scheme, ('b, 'n) ring_scheme] => ('a => 'b) set"
  where "ring_hom R S =
    {h. h \<in> carrier R \<rightarrow> carrier S \<and>
      (\<forall>x y. x \<in> carrier R \<and> y \<in> carrier R \<longrightarrow>
        h (x \<otimes>\<^bsub>R\<^esub> y) = h x \<otimes>\<^bsub>S\<^esub> h y \<and> h (x \<oplus>\<^bsub>R\<^esub> y) = h x \<oplus>\<^bsub>S\<^esub> h y) \<and>
      h \<one>\<^bsub>R\<^esub> = \<one>\<^bsub>S\<^esub>}"

lemma ring_hom_memI:
  fixes R (structure) and S (structure)
  assumes "\<And>x. x \<in> carrier R \<Longrightarrow> h x \<in> carrier S"
      and "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> h (x \<otimes> y) = h x \<otimes>\<^bsub>S\<^esub> h y"
      and "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> h (x \<oplus> y) = h x \<oplus>\<^bsub>S\<^esub> h y"
      and "h \<one> = \<one>\<^bsub>S\<^esub>"
  shows "h \<in> ring_hom R S"
  by (auto simp add: ring_hom_def assms Pi_def)

lemma ring_hom_memE:
  fixes R (structure) and S (structure)
  assumes "h \<in> ring_hom R S"
  shows "\<And>x. x \<in> carrier R \<Longrightarrow> h x \<in> carrier S"
    and "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> h (x \<otimes> y) = h x \<otimes>\<^bsub>S\<^esub> h y"
    and "\<And>x y. \<lbrakk> x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> h (x \<oplus> y) = h x \<oplus>\<^bsub>S\<^esub> h y"
    and "h \<one> = \<one>\<^bsub>S\<^esub>"
  using assms unfolding ring_hom_def by auto

lemma ring_hom_closed:
  "\<lbrakk> h \<in> ring_hom R S; x \<in> carrier R \<rbrakk> \<Longrightarrow> h x \<in> carrier S"
  by (auto simp add: ring_hom_def funcset_mem)

lemma ring_hom_mult:
  fixes R (structure) and S (structure)
  shows "\<lbrakk> h \<in> ring_hom R S; x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> h (x \<otimes> y) = h x \<otimes>\<^bsub>S\<^esub> h y"
    by (simp add: ring_hom_def)

lemma ring_hom_add:
  fixes R (structure) and S (structure)
  shows "\<lbrakk> h \<in> ring_hom R S; x \<in> carrier R; y \<in> carrier R \<rbrakk> \<Longrightarrow> h (x \<oplus> y) = h x \<oplus>\<^bsub>S\<^esub> h y"
    by (simp add: ring_hom_def)

lemma ring_hom_one:
  fixes R (structure) and S (structure)
  shows "h \<in> ring_hom R S \<Longrightarrow> h \<one> = \<one>\<^bsub>S\<^esub>"
  by (simp add: ring_hom_def)

lemma ring_hom_zero:
  fixes R (structure) and S (structure)
  assumes "h \<in> ring_hom R S" "ring R" "ring S"
  shows "h \<zero> = \<zero>\<^bsub>S\<^esub>"
proof -
  have "h \<zero> = h \<zero> \<oplus>\<^bsub>S\<^esub> h \<zero>"
    using ring_hom_add[OF assms(1), of \<zero> \<zero>] assms(2)
    by (simp add: ring.ring_simprules(2) ring.ring_simprules(15))
  thus ?thesis
    by (metis abelian_group.l_neg assms ring.is_abelian_group ring.ring_simprules(18) ring.ring_simprules(2) ring_hom_closed)
qed

locale ring_hom_cring =
  R?: cring R + S?: cring S for R (structure) and S (structure) + fixes h
  assumes homh [simp, intro]: "h \<in> ring_hom R S"
  notes hom_closed [simp, intro] = ring_hom_closed [OF homh]
    and hom_mult [simp] = ring_hom_mult [OF homh]
    and hom_add [simp] = ring_hom_add [OF homh]
    and hom_one [simp] = ring_hom_one [OF homh]

lemma (in ring_hom_cring) hom_zero [simp]: "h \<zero> = \<zero>\<^bsub>S\<^esub>"
proof -
  have "h \<zero> \<oplus>\<^bsub>S\<^esub> h \<zero> = h \<zero> \<oplus>\<^bsub>S\<^esub> \<zero>\<^bsub>S\<^esub>"
    by (simp add: hom_add [symmetric] del: hom_add)
  then show ?thesis by (simp del: S.r_zero)
qed

lemma (in ring_hom_cring) hom_a_inv [simp]:
  "x \<in> carrier R \<Longrightarrow> h (\<ominus> x) = \<ominus>\<^bsub>S\<^esub> h x"
proof -
  assume R: "x \<in> carrier R"
  then have "h x \<oplus>\<^bsub>S\<^esub> h (\<ominus> x) = h x \<oplus>\<^bsub>S\<^esub> (\<ominus>\<^bsub>S\<^esub> h x)"
    by (simp add: hom_add [symmetric] R.r_neg S.r_neg del: hom_add)
  with R show ?thesis by simp
qed

lemma (in ring_hom_cring) hom_finsum [simp]:
  assumes "f: A \<rightarrow> carrier R"
  shows "h (\<Oplus> i \<in> A. f i) = (\<Oplus>\<^bsub>S\<^esub> i \<in> A. (h o f) i)"
  using assms by (induct A rule: infinite_finite_induct, auto simp: Pi_def)

lemma (in ring_hom_cring) hom_finprod:
  assumes "f: A \<rightarrow> carrier R"
  shows "h (\<Otimes> i \<in> A. f i) = (\<Otimes>\<^bsub>S\<^esub> i \<in> A. (h o f) i)"
  using assms by (induct A rule: infinite_finite_induct, auto simp: Pi_def)

declare ring_hom_cring.hom_finprod [simp]

lemma id_ring_hom [simp]: "id \<in> ring_hom R R"
  by (auto intro!: ring_hom_memI)

lemma ring_hom_trans: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  "\<lbrakk> f \<in> ring_hom R S; g \<in> ring_hom S T \<rbrakk> \<Longrightarrow> g \<circ> f \<in> ring_hom R T"
  by (rule ring_hom_memI) (auto simp add: ring_hom_closed ring_hom_mult ring_hom_add ring_hom_one)

subsection\<open>Jeremy Avigad's \<open>More_Finite_Product\<close> material\<close>

(* need better simplification rules for rings *)
(* the next one holds more generally for abelian groups *)

lemma (in cring) sum_zero_eq_neg: "x \<in> carrier R \<Longrightarrow> y \<in> carrier R \<Longrightarrow> x \<oplus> y = \<zero> \<Longrightarrow> x = \<ominus> y"
  by (metis minus_equality)

lemma (in domain) square_eq_one:
  fixes x
  assumes [simp]: "x \<in> carrier R"
    and "x \<otimes> x = \<one>"
  shows "x = \<one> \<or> x = \<ominus>\<one>"
proof -
  have "(x \<oplus> \<one>) \<otimes> (x \<oplus> \<ominus> \<one>) = x \<otimes> x \<oplus> \<ominus> \<one>"
    by (simp add: ring_simprules)
  also from \<open>x \<otimes> x = \<one>\<close> have "\<dots> = \<zero>"
    by (simp add: ring_simprules)
  finally have "(x \<oplus> \<one>) \<otimes> (x \<oplus> \<ominus> \<one>) = \<zero>" .
  then have "(x \<oplus> \<one>) = \<zero> \<or> (x \<oplus> \<ominus> \<one>) = \<zero>"
    by (intro integral) auto
  then show ?thesis
    by (metis add.inv_closed add.inv_solve_right assms(1) l_zero one_closed zero_closed)
qed

lemma (in domain) inv_eq_self: "x \<in> Units R \<Longrightarrow> x = inv x \<Longrightarrow> x = \<one> \<or> x = \<ominus>\<one>"
  by (metis Units_closed Units_l_inv square_eq_one)


text \<open>
  The following translates theorems about groups to the facts about
  the units of a ring. (The list should be expanded as more things are
  needed.)
\<close>

lemma (in ring) finite_ring_finite_units [intro]: "finite (carrier R) \<Longrightarrow> finite (Units R)"
  by (rule finite_subset) auto

lemma (in monoid) units_of_pow:
  fixes n :: nat
  shows "x \<in> Units G \<Longrightarrow> x [^]\<^bsub>units_of G\<^esub> n = x [^]\<^bsub>G\<^esub> n"
  apply (induct n)
  apply (auto simp add: units_group group.is_monoid
    monoid.nat_pow_0 monoid.nat_pow_Suc units_of_one units_of_mult)
  done

lemma (in cring) units_power_order_eq_one:
  "finite (Units R) \<Longrightarrow> a \<in> Units R \<Longrightarrow> a [^] card(Units R) = \<one>"
  by (metis comm_group.power_order_eq_one units_comm_group units_of_carrier units_of_one units_of_pow)

subsection\<open>Jeremy Avigad's \<open>More_Ring\<close> material\<close>

lemma (in cring) field_intro2: 
  assumes "\<zero>\<^bsub>R\<^esub> \<noteq> \<one>\<^bsub>R\<^esub>" and un: "\<And>x. x \<in> carrier R - {\<zero>\<^bsub>R\<^esub>} \<Longrightarrow> x \<in> Units R"
  shows "field R"
proof unfold_locales
  show "\<one> \<noteq> \<zero>" using assms by auto
  show "\<lbrakk>a \<otimes> b = \<zero>; a \<in> carrier R;
            b \<in> carrier R\<rbrakk>
           \<Longrightarrow> a = \<zero> \<or> b = \<zero>" for a b
    by (metis un Units_l_cancel insert_Diff_single insert_iff r_null zero_closed)
qed (use assms in \<open>auto simp: Units_def\<close>)

lemma (in monoid) inv_char:
  assumes "x \<in> carrier G" "y \<in> carrier G" "x \<otimes> y = \<one>" "y \<otimes> x = \<one>" 
  shows "inv x = y"
  using assms inv_unique' by auto

lemma (in comm_monoid) comm_inv_char: "x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> x \<otimes> y = \<one> \<Longrightarrow> inv x = y"
  by (simp add: inv_char m_comm)

lemma (in ring) inv_neg_one [simp]: "inv (\<ominus> \<one>) = \<ominus> \<one>"
  by (simp add: inv_char local.ring_axioms ring.r_minus)

lemma (in monoid) inv_eq_imp_eq [dest!]: "inv x = inv y \<Longrightarrow> x \<in> Units G \<Longrightarrow> y \<in> Units G \<Longrightarrow> x = y"
  by (metis Units_inv_inv)

lemma (in ring) Units_minus_one_closed [intro]: "\<ominus> \<one> \<in> Units R"
  by (simp add: Units_def) (metis add.l_inv_ex local.minus_minus minus_equality one_closed r_minus r_one)

lemma (in ring) inv_eq_neg_one_eq: "x \<in> Units R \<Longrightarrow> inv x = \<ominus> \<one> \<longleftrightarrow> x = \<ominus> \<one>"
  by (metis Units_inv_inv inv_neg_one)

lemma (in monoid) inv_eq_one_eq: "x \<in> Units G \<Longrightarrow> inv x = \<one> \<longleftrightarrow> x = \<one>"
  by (metis Units_inv_inv inv_one)

end
