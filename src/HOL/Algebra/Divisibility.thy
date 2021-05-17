(*  Title:      HOL/Algebra/Divisibility.thy
    Author:     Clemens Ballarin
    Author:     Stephan Hohe
*)

section \<open>Divisibility in monoids and rings\<close>

theory Divisibility
  imports "HOL-Combinatorics.List_Permutation" Coset Group
begin

section \<open>Factorial Monoids\<close>

subsection \<open>Monoids with Cancellation Law\<close>

locale monoid_cancel = monoid +
  assumes l_cancel: "\<lbrakk>c \<otimes> a = c \<otimes> b; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> a = b"
    and r_cancel: "\<lbrakk>a \<otimes> c = b \<otimes> c; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> a = b"

lemma (in monoid) monoid_cancelI:
  assumes l_cancel: "\<And>a b c. \<lbrakk>c \<otimes> a = c \<otimes> b; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> a = b"
    and r_cancel: "\<And>a b c. \<lbrakk>a \<otimes> c = b \<otimes> c; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> a = b"
  shows "monoid_cancel G"
    by standard fact+

lemma (in monoid_cancel) is_monoid_cancel: "monoid_cancel G" ..

sublocale group \<subseteq> monoid_cancel
  by standard simp_all


locale comm_monoid_cancel = monoid_cancel + comm_monoid

lemma comm_monoid_cancelI:
  fixes G (structure)
  assumes "comm_monoid G"
  assumes cancel: "\<And>a b c. \<lbrakk>a \<otimes> c = b \<otimes> c; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> a = b"
  shows "comm_monoid_cancel G"
proof -
  interpret comm_monoid G by fact
  show "comm_monoid_cancel G"
    by unfold_locales (metis assms(2) m_ac(2))+
qed

lemma (in comm_monoid_cancel) is_comm_monoid_cancel: "comm_monoid_cancel G"
  by intro_locales

sublocale comm_group \<subseteq> comm_monoid_cancel ..


subsection \<open>Products of Units in Monoids\<close>

lemma (in monoid) prod_unit_l:
  assumes abunit[simp]: "a \<otimes> b \<in> Units G"
    and aunit[simp]: "a \<in> Units G"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "b \<in> Units G"
proof -
  have c: "inv (a \<otimes> b) \<otimes> a \<in> carrier G" by simp

  have "(inv (a \<otimes> b) \<otimes> a) \<otimes> b = inv (a \<otimes> b) \<otimes> (a \<otimes> b)"
    by (simp add: m_assoc)
  also have "\<dots> = \<one>" by simp
  finally have li: "(inv (a \<otimes> b) \<otimes> a) \<otimes> b = \<one>" .

  have "\<one> = inv a \<otimes> a" by (simp add: Units_l_inv[symmetric])
  also have "\<dots> = inv a \<otimes> \<one> \<otimes> a" by simp
  also have "\<dots> = inv a \<otimes> ((a \<otimes> b) \<otimes> inv (a \<otimes> b)) \<otimes> a"
    by (simp add: Units_r_inv[OF abunit, symmetric] del: Units_r_inv)
  also have "\<dots> = ((inv a \<otimes> a) \<otimes> b) \<otimes> inv (a \<otimes> b) \<otimes> a"
    by (simp add: m_assoc del: Units_l_inv)
  also have "\<dots> = b \<otimes> inv (a \<otimes> b) \<otimes> a" by simp
  also have "\<dots> = b \<otimes> (inv (a \<otimes> b) \<otimes> a)" by (simp add: m_assoc)
  finally have ri: "b \<otimes> (inv (a \<otimes> b) \<otimes> a) = \<one> " by simp

  from c li ri show "b \<in> Units G" by (auto simp: Units_def)
qed

lemma (in monoid) prod_unit_r:
  assumes abunit[simp]: "a \<otimes> b \<in> Units G"
    and bunit[simp]: "b \<in> Units G"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "a \<in> Units G"
proof -
  have c: "b \<otimes> inv (a \<otimes> b) \<in> carrier G" by simp

  have "a \<otimes> (b \<otimes> inv (a \<otimes> b)) = (a \<otimes> b) \<otimes> inv (a \<otimes> b)"
    by (simp add: m_assoc del: Units_r_inv)
  also have "\<dots> = \<one>" by simp
  finally have li: "a \<otimes> (b \<otimes> inv (a \<otimes> b)) = \<one>" .

  have "\<one> = b \<otimes> inv b" by (simp add: Units_r_inv[symmetric])
  also have "\<dots> = b \<otimes> \<one> \<otimes> inv b" by simp
  also have "\<dots> = b \<otimes> (inv (a \<otimes> b) \<otimes> (a \<otimes> b)) \<otimes> inv b"
    by (simp add: Units_l_inv[OF abunit, symmetric] del: Units_l_inv)
  also have "\<dots> = (b \<otimes> inv (a \<otimes> b) \<otimes> a) \<otimes> (b \<otimes> inv b)"
    by (simp add: m_assoc del: Units_l_inv)
  also have "\<dots> = b \<otimes> inv (a \<otimes> b) \<otimes> a" by simp
  finally have ri: "(b \<otimes> inv (a \<otimes> b)) \<otimes> a = \<one> " by simp

  from c li ri show "a \<in> Units G" by (auto simp: Units_def)
qed

lemma (in comm_monoid) unit_factor:
  assumes abunit: "a \<otimes> b \<in> Units G"
    and [simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "a \<in> Units G"
  using abunit[simplified Units_def]
proof clarsimp
  fix i
  assume [simp]: "i \<in> carrier G"

  have carr': "b \<otimes> i \<in> carrier G" by simp

  have "(b \<otimes> i) \<otimes> a = (i \<otimes> b) \<otimes> a" by (simp add: m_comm)
  also have "\<dots> = i \<otimes> (b \<otimes> a)" by (simp add: m_assoc)
  also have "\<dots> = i \<otimes> (a \<otimes> b)" by (simp add: m_comm)
  also assume "i \<otimes> (a \<otimes> b) = \<one>"
  finally have li': "(b \<otimes> i) \<otimes> a = \<one>" .

  have "a \<otimes> (b \<otimes> i) = a \<otimes> b \<otimes> i" by (simp add: m_assoc)
  also assume "a \<otimes> b \<otimes> i = \<one>"
  finally have ri': "a \<otimes> (b \<otimes> i) = \<one>" .

  from carr' li' ri'
  show "a \<in> Units G" by (simp add: Units_def, fast)
qed


subsection \<open>Divisibility and Association\<close>

subsubsection \<open>Function definitions\<close>

definition factor :: "[_, 'a, 'a] \<Rightarrow> bool" (infix "divides\<index>" 65)
  where "a divides\<^bsub>G\<^esub> b \<longleftrightarrow> (\<exists>c\<in>carrier G. b = a \<otimes>\<^bsub>G\<^esub> c)"

definition associated :: "[_, 'a, 'a] \<Rightarrow> bool" (infix "\<sim>\<index>" 55)
  where "a \<sim>\<^bsub>G\<^esub> b \<longleftrightarrow> a divides\<^bsub>G\<^esub> b \<and> b divides\<^bsub>G\<^esub> a"

abbreviation "division_rel G \<equiv> \<lparr>carrier = carrier G, eq = (\<sim>\<^bsub>G\<^esub>), le = (divides\<^bsub>G\<^esub>)\<rparr>"

definition properfactor :: "[_, 'a, 'a] \<Rightarrow> bool"
  where "properfactor G a b \<longleftrightarrow> a divides\<^bsub>G\<^esub> b \<and> \<not>(b divides\<^bsub>G\<^esub> a)"

definition irreducible :: "[_, 'a] \<Rightarrow> bool"
  where "irreducible G a \<longleftrightarrow> a \<notin> Units G \<and> (\<forall>b\<in>carrier G. properfactor G b a \<longrightarrow> b \<in> Units G)"

definition prime :: "[_, 'a] \<Rightarrow> bool"
  where "prime G p \<longleftrightarrow>
    p \<notin> Units G \<and>
    (\<forall>a\<in>carrier G. \<forall>b\<in>carrier G. p divides\<^bsub>G\<^esub> (a \<otimes>\<^bsub>G\<^esub> b) \<longrightarrow> p divides\<^bsub>G\<^esub> a \<or> p divides\<^bsub>G\<^esub> b)"


subsubsection \<open>Divisibility\<close>

lemma dividesI:
  fixes G (structure)
  assumes carr: "c \<in> carrier G"
    and p: "b = a \<otimes> c"
  shows "a divides b"
  unfolding factor_def using assms by fast

lemma dividesI' [intro]:
  fixes G (structure)
  assumes p: "b = a \<otimes> c"
    and carr: "c \<in> carrier G"
  shows "a divides b"
  using assms by (fast intro: dividesI)

lemma dividesD:
  fixes G (structure)
  assumes "a divides b"
  shows "\<exists>c\<in>carrier G. b = a \<otimes> c"
  using assms unfolding factor_def by fast

lemma dividesE [elim]:
  fixes G (structure)
  assumes d: "a divides b"
    and elim: "\<And>c. \<lbrakk>b = a \<otimes> c; c \<in> carrier G\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from dividesD[OF d] obtain c where "c \<in> carrier G" and "b = a \<otimes> c" by auto
  then show P by (elim elim)
qed

lemma (in monoid) divides_refl[simp, intro!]:
  assumes carr: "a \<in> carrier G"
  shows "a divides a"
  by (intro dividesI[of "\<one>"]) (simp_all add: carr)

lemma (in monoid) divides_trans [trans]:
  assumes dvds: "a divides b" "b divides c"
    and acarr: "a \<in> carrier G"
  shows "a divides c"
  using dvds[THEN dividesD] by (blast intro: dividesI m_assoc acarr)

lemma (in monoid) divides_mult_lI [intro]:
  assumes  "a divides b" "a \<in> carrier G" "c \<in> carrier G"
  shows "(c \<otimes> a) divides (c \<otimes> b)"
  by (metis assms factor_def m_assoc)

lemma (in monoid_cancel) divides_mult_l [simp]:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "(c \<otimes> a) divides (c \<otimes> b) = a divides b"
proof
  show "c \<otimes> a divides c \<otimes> b \<Longrightarrow> a divides b"
    using carr monoid.m_assoc monoid_axioms monoid_cancel.l_cancel monoid_cancel_axioms by fastforce
  show "a divides b \<Longrightarrow> c \<otimes> a divides c \<otimes> b"
  using carr(1) carr(3) by blast
qed

lemma (in comm_monoid) divides_mult_rI [intro]:
  assumes ab: "a divides b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "(a \<otimes> c) divides (b \<otimes> c)"
  using carr ab by (metis divides_mult_lI m_comm)

lemma (in comm_monoid_cancel) divides_mult_r [simp]:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "(a \<otimes> c) divides (b \<otimes> c) = a divides b"
  using carr by (simp add: m_comm[of a c] m_comm[of b c])

lemma (in monoid) divides_prod_r:
  assumes ab: "a divides b"
    and carr: "a \<in> carrier G" "c \<in> carrier G"
  shows "a divides (b \<otimes> c)"
  using ab carr by (fast intro: m_assoc)

lemma (in comm_monoid) divides_prod_l:
  assumes "a \<in> carrier G" "b \<in> carrier G" "c \<in> carrier G" "a divides b"
  shows "a divides (c \<otimes> b)"
  using assms  by (simp add: divides_prod_r m_comm)

lemma (in monoid) unit_divides:
  assumes uunit: "u \<in> Units G"
    and acarr: "a \<in> carrier G"
  shows "u divides a"
proof (intro dividesI[of "(inv u) \<otimes> a"], fast intro: uunit acarr)
  from uunit acarr have xcarr: "inv u \<otimes> a \<in> carrier G" by fast
  from uunit acarr have "u \<otimes> (inv u \<otimes> a) = (u \<otimes> inv u) \<otimes> a"
    by (fast intro: m_assoc[symmetric])
  also have "\<dots> = \<one> \<otimes> a" by (simp add: Units_r_inv[OF uunit])
  also from acarr have "\<dots> = a" by simp
  finally show "a = u \<otimes> (inv u \<otimes> a)" ..
qed

lemma (in comm_monoid) divides_unit:
  assumes udvd: "a divides u"
    and  carr: "a \<in> carrier G"  "u \<in> Units G"
  shows "a \<in> Units G"
  using udvd carr by (blast intro: unit_factor)

lemma (in comm_monoid) Unit_eq_dividesone:
  assumes ucarr: "u \<in> carrier G"
  shows "u \<in> Units G = u divides \<one>"
  using ucarr by (fast dest: divides_unit intro: unit_divides)


subsubsection \<open>Association\<close>

lemma associatedI:
  fixes G (structure)
  assumes "a divides b" "b divides a"
  shows "a \<sim> b"
  using assms by (simp add: associated_def)

lemma (in monoid) associatedI2:
  assumes uunit[simp]: "u \<in> Units G"
    and a: "a = b \<otimes> u"
    and bcarr: "b \<in> carrier G"
  shows "a \<sim> b"
  using uunit bcarr
  unfolding a
  apply (intro associatedI)
  apply (metis Units_closed divides_mult_lI one_closed r_one unit_divides)
  by blast

lemma (in monoid) associatedI2':
  assumes "a = b \<otimes> u"
    and "u \<in> Units G"
    and "b \<in> carrier G"
  shows "a \<sim> b"
  using assms by (intro associatedI2)

lemma associatedD:
  fixes G (structure)
  assumes "a \<sim> b"
  shows "a divides b"
  using assms by (simp add: associated_def)

lemma (in monoid_cancel) associatedD2:
  assumes assoc: "a \<sim> b"
    and carr: "a \<in> carrier G" "b \<in> carrier G"
  shows "\<exists>u\<in>Units G. a = b \<otimes> u"
  using assoc
  unfolding associated_def
proof clarify
  assume "b divides a"
  then obtain u where ucarr: "u \<in> carrier G" and a: "a = b \<otimes> u"
    by (rule dividesE)

  assume "a divides b"
  then obtain u' where u'carr: "u' \<in> carrier G" and b: "b = a \<otimes> u'"
    by (rule dividesE)
  note carr = carr ucarr u'carr

  from carr have "a \<otimes> \<one> = a" by simp
  also have "\<dots> = b \<otimes> u" by (simp add: a)
  also have "\<dots> = a \<otimes> u' \<otimes> u" by (simp add: b)
  also from carr have "\<dots> = a \<otimes> (u' \<otimes> u)" by (simp add: m_assoc)
  finally have "a \<otimes> \<one> = a \<otimes> (u' \<otimes> u)" .
  with carr have u1: "\<one> = u' \<otimes> u" by (fast dest: l_cancel)

  from carr have "b \<otimes> \<one> = b" by simp
  also have "\<dots> = a \<otimes> u'" by (simp add: b)
  also have "\<dots> = b \<otimes> u \<otimes> u'" by (simp add: a)
  also from carr have "\<dots> = b \<otimes> (u \<otimes> u')" by (simp add: m_assoc)
  finally have "b \<otimes> \<one> = b \<otimes> (u \<otimes> u')" .
  with carr have u2: "\<one> = u \<otimes> u'" by (fast dest: l_cancel)

  from u'carr u1[symmetric] u2[symmetric] have "\<exists>u'\<in>carrier G. u' \<otimes> u = \<one> \<and> u \<otimes> u' = \<one>"
    by fast
  then have "u \<in> Units G"
    by (simp add: Units_def ucarr)
  with ucarr a show "\<exists>u\<in>Units G. a = b \<otimes> u" by fast
qed

lemma associatedE:
  fixes G (structure)
  assumes assoc: "a \<sim> b"
    and e: "\<lbrakk>a divides b; b divides a\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from assoc have "a divides b" "b divides a"
    by (simp_all add: associated_def)
  then show P by (elim e)
qed

lemma (in monoid_cancel) associatedE2:
  assumes assoc: "a \<sim> b"
    and e: "\<And>u. \<lbrakk>a = b \<otimes> u; u \<in> Units G\<rbrakk> \<Longrightarrow> P"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "P"
proof -
  from assoc and carr have "\<exists>u\<in>Units G. a = b \<otimes> u"
    by (rule associatedD2)
  then obtain u where "u \<in> Units G"  "a = b \<otimes> u"
    by auto
  then show P by (elim e)
qed

lemma (in monoid) associated_refl [simp, intro!]:
  assumes "a \<in> carrier G"
  shows "a \<sim> a"
  using assms by (fast intro: associatedI)

lemma (in monoid) associated_sym [sym]:
  assumes "a \<sim> b"
  shows "b \<sim> a"
  using assms by (iprover intro: associatedI elim: associatedE)

lemma (in monoid) associated_trans [trans]:
  assumes "a \<sim> b"  "b \<sim> c"
    and "a \<in> carrier G" "c \<in> carrier G"
  shows "a \<sim> c"
  using assms by (iprover intro: associatedI divides_trans elim: associatedE)

lemma (in monoid) division_equiv [intro, simp]: "equivalence (division_rel G)"
  apply unfold_locales
    apply simp_all
   apply (metis associated_def)
  apply (iprover intro: associated_trans)
  done


subsubsection \<open>Division and associativity\<close>

lemmas divides_antisym = associatedI

lemma (in monoid) divides_cong_l [trans]:
  assumes "x \<sim> x'" "x' divides y" "x \<in> carrier G" 
  shows "x divides y"
  by (meson assms associatedD divides_trans)

lemma (in monoid) divides_cong_r [trans]:
  assumes "x divides y" "y \<sim> y'" "x \<in> carrier G" 
  shows "x divides y'"
  by (meson assms associatedD divides_trans)

lemma (in monoid) division_weak_partial_order [simp, intro!]:
  "weak_partial_order (division_rel G)"
  apply unfold_locales
      apply (simp_all add: associated_sym divides_antisym)
     apply (metis associated_trans)
   apply (metis divides_trans)
  by (meson associated_def divides_trans)


subsubsection \<open>Multiplication and associativity\<close>

lemma (in monoid) mult_cong_r:
  assumes "b \<sim> b'" "a \<in> carrier G"  "b \<in> carrier G"  "b' \<in> carrier G"
  shows "a \<otimes> b \<sim> a \<otimes> b'"
  by (meson assms associated_def divides_mult_lI)

lemma (in comm_monoid) mult_cong_l:
  assumes "a \<sim> a'" "a \<in> carrier G"  "a' \<in> carrier G"  "b \<in> carrier G"
  shows "a \<otimes> b \<sim> a' \<otimes> b"
  using assms m_comm mult_cong_r by auto

lemma (in monoid_cancel) assoc_l_cancel:
  assumes "a \<in> carrier G"  "b \<in> carrier G"  "b' \<in> carrier G" "a \<otimes> b \<sim> a \<otimes> b'"
  shows "b \<sim> b'"
  by (meson assms associated_def divides_mult_l)

lemma (in comm_monoid_cancel) assoc_r_cancel:
  assumes "a \<otimes> b \<sim> a' \<otimes> b" "a \<in> carrier G"  "a' \<in> carrier G"  "b \<in> carrier G"
  shows "a \<sim> a'"
  using assms assoc_l_cancel m_comm by presburger


subsubsection \<open>Units\<close>

lemma (in monoid_cancel) assoc_unit_l [trans]:
  assumes "a \<sim> b"
    and "b \<in> Units G"
    and "a \<in> carrier G"
  shows "a \<in> Units G"
  using assms by (fast elim: associatedE2)

lemma (in monoid_cancel) assoc_unit_r [trans]:
  assumes aunit: "a \<in> Units G"
    and asc: "a \<sim> b"
    and bcarr: "b \<in> carrier G"
  shows "b \<in> Units G"
  using aunit bcarr associated_sym[OF asc] by (blast intro: assoc_unit_l)

lemma (in comm_monoid) Units_cong:
  assumes aunit: "a \<in> Units G" and asc: "a \<sim> b"
    and bcarr: "b \<in> carrier G"
  shows "b \<in> Units G"
  using assms by (blast intro: divides_unit elim: associatedE)

lemma (in monoid) Units_assoc:
  assumes units: "a \<in> Units G"  "b \<in> Units G"
  shows "a \<sim> b"
  using units by (fast intro: associatedI unit_divides)

lemma (in monoid) Units_are_ones: "Units G {.=}\<^bsub>(division_rel G)\<^esub> {\<one>}"
proof -
  have "a .\<in>\<^bsub>division_rel G\<^esub> {\<one>}" if "a \<in> Units G" for a
  proof -
    have "a \<sim> \<one>"
      by (rule associatedI) (simp_all add: Units_closed that unit_divides)
    then show ?thesis
      by (simp add: elem_def)
  qed
  moreover have "\<one> .\<in>\<^bsub>division_rel G\<^esub> Units G"
    by (simp add: equivalence.mem_imp_elem)
  ultimately show ?thesis
    by (auto simp: set_eq_def)
qed

lemma (in comm_monoid) Units_Lower: "Units G = Lower (division_rel G) (carrier G)"
  apply (auto simp add: Units_def Lower_def)
   apply (metis Units_one_closed unit_divides unit_factor)
  apply (metis Unit_eq_dividesone Units_r_inv_ex m_ac(2) one_closed)
  done

lemma (in monoid_cancel) associated_iff:
  assumes "a \<in> carrier G" "b \<in> carrier G"
  shows "a \<sim> b \<longleftrightarrow> (\<exists>c \<in> Units G. a = b \<otimes> c)"
  using assms associatedI2' associatedD2 by auto


subsubsection \<open>Proper factors\<close>

lemma properfactorI:
  fixes G (structure)
  assumes "a divides b"
    and "\<not>(b divides a)"
  shows "properfactor G a b"
  using assms unfolding properfactor_def by simp

lemma properfactorI2:
  fixes G (structure)
  assumes advdb: "a divides b"
    and neq: "\<not>(a \<sim> b)"
  shows "properfactor G a b"
proof (rule properfactorI, rule advdb, rule notI)
  assume "b divides a"
  with advdb have "a \<sim> b" by (rule associatedI)
  with neq show "False" by fast
qed

lemma (in comm_monoid_cancel) properfactorI3:
  assumes p: "p = a \<otimes> b"
    and nunit: "b \<notin> Units G"
    and carr: "a \<in> carrier G"  "b \<in> carrier G" 
  shows "properfactor G a p"
  unfolding p
  using carr
  apply (intro properfactorI, fast)
proof (clarsimp, elim dividesE)
  fix c
  assume ccarr: "c \<in> carrier G"
  note [simp] = carr ccarr

  have "a \<otimes> \<one> = a" by simp
  also assume "a = a \<otimes> b \<otimes> c"
  also have "\<dots> = a \<otimes> (b \<otimes> c)" by (simp add: m_assoc)
  finally have "a \<otimes> \<one> = a \<otimes> (b \<otimes> c)" .

  then have rinv: "\<one> = b \<otimes> c" by (intro l_cancel[of "a" "\<one>" "b \<otimes> c"], simp+)
  also have "\<dots> = c \<otimes> b" by (simp add: m_comm)
  finally have linv: "\<one> = c \<otimes> b" .

  from ccarr linv[symmetric] rinv[symmetric] have "b \<in> Units G"
    unfolding Units_def by fastforce
  with nunit show False ..
qed

lemma properfactorE:
  fixes G (structure)
  assumes pf: "properfactor G a b"
    and r: "\<lbrakk>a divides b; \<not>(b divides a)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using pf unfolding properfactor_def by (fast intro: r)

lemma properfactorE2:
  fixes G (structure)
  assumes pf: "properfactor G a b"
    and elim: "\<lbrakk>a divides b; \<not>(a \<sim> b)\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using pf unfolding properfactor_def by (fast elim: elim associatedE)

lemma (in monoid) properfactor_unitE:
  assumes uunit: "u \<in> Units G"
    and pf: "properfactor G a u"
    and acarr: "a \<in> carrier G"
  shows "P"
  using pf unit_divides[OF uunit acarr] by (fast elim: properfactorE)

lemma (in monoid) properfactor_divides:
  assumes pf: "properfactor G a b"
  shows "a divides b"
  using pf by (elim properfactorE)

lemma (in monoid) properfactor_trans1 [trans]:
  assumes "a divides b"  "properfactor G b c" "a \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G a c"
  by (meson divides_trans properfactorE properfactorI assms)

lemma (in monoid) properfactor_trans2 [trans]:
  assumes "properfactor G a b"  "b divides c" "a \<in> carrier G"  "b \<in> carrier G"
  shows "properfactor G a c"
  by (meson divides_trans properfactorE properfactorI assms)

lemma properfactor_lless:
  fixes G (structure)
  shows "properfactor G = lless (division_rel G)"
  by (force simp: lless_def properfactor_def associated_def)

lemma (in monoid) properfactor_cong_l [trans]:
  assumes x'x: "x' \<sim> x"
    and pf: "properfactor G x y"
    and carr: "x \<in> carrier G"  "x' \<in> carrier G"  "y \<in> carrier G"
  shows "properfactor G x' y"
  using pf
  unfolding properfactor_lless
proof -
  interpret weak_partial_order "division_rel G" ..
  from x'x have "x' .=\<^bsub>division_rel G\<^esub> x" by simp
  also assume "x \<sqsubset>\<^bsub>division_rel G\<^esub> y"
  finally show "x' \<sqsubset>\<^bsub>division_rel G\<^esub> y" by (simp add: carr)
qed

lemma (in monoid) properfactor_cong_r [trans]:
  assumes pf: "properfactor G x y"
    and yy': "y \<sim> y'"
    and carr: "x \<in> carrier G"  "y \<in> carrier G"  "y' \<in> carrier G"
  shows "properfactor G x y'"
  using pf
  unfolding properfactor_lless
proof -
  interpret weak_partial_order "division_rel G" ..
  assume "x \<sqsubset>\<^bsub>division_rel G\<^esub> y"
  also from yy'
  have "y .=\<^bsub>division_rel G\<^esub> y'" by simp
  finally show "x \<sqsubset>\<^bsub>division_rel G\<^esub> y'" by (simp add: carr)
qed

lemma (in monoid_cancel) properfactor_mult_lI [intro]:
  assumes ab: "properfactor G a b"
    and carr: "a \<in> carrier G" "c \<in> carrier G"
  shows "properfactor G (c \<otimes> a) (c \<otimes> b)"
  using ab carr by (fastforce elim: properfactorE intro: properfactorI)

lemma (in monoid_cancel) properfactor_mult_l [simp]:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G (c \<otimes> a) (c \<otimes> b) = properfactor G a b"
  using carr by (fastforce elim: properfactorE intro: properfactorI)

lemma (in comm_monoid_cancel) properfactor_mult_rI [intro]:
  assumes ab: "properfactor G a b"
    and carr: "a \<in> carrier G" "c \<in> carrier G"
  shows "properfactor G (a \<otimes> c) (b \<otimes> c)"
  using ab carr by (fastforce elim: properfactorE intro: properfactorI)

lemma (in comm_monoid_cancel) properfactor_mult_r [simp]:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G (a \<otimes> c) (b \<otimes> c) = properfactor G a b"
  using carr by (fastforce elim: properfactorE intro: properfactorI)

lemma (in monoid) properfactor_prod_r:
  assumes ab: "properfactor G a b"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G a (b \<otimes> c)"
  by (intro properfactor_trans2[OF ab] divides_prod_r) simp_all

lemma (in comm_monoid) properfactor_prod_l:
  assumes ab: "properfactor G a b"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G a (c \<otimes> b)"
  by (intro properfactor_trans2[OF ab] divides_prod_l) simp_all


subsection \<open>Irreducible Elements and Primes\<close>

subsubsection \<open>Irreducible elements\<close>

lemma irreducibleI:
  fixes G (structure)
  assumes "a \<notin> Units G"
    and "\<And>b. \<lbrakk>b \<in> carrier G; properfactor G b a\<rbrakk> \<Longrightarrow> b \<in> Units G"
  shows "irreducible G a"
  using assms unfolding irreducible_def by blast

lemma irreducibleE:
  fixes G (structure)
  assumes irr: "irreducible G a"
    and elim: "\<lbrakk>a \<notin> Units G; \<forall>b. b \<in> carrier G \<and> properfactor G b a \<longrightarrow> b \<in> Units G\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using assms unfolding irreducible_def by blast

lemma irreducibleD:
  fixes G (structure)
  assumes irr: "irreducible G a"
    and pf: "properfactor G b a"
    and bcarr: "b \<in> carrier G"
  shows "b \<in> Units G"
  using assms by (fast elim: irreducibleE)

lemma (in monoid_cancel) irreducible_cong [trans]:
  assumes "irreducible G a" "a \<sim> a'" "a \<in> carrier G"  "a' \<in> carrier G"
  shows "irreducible G a'"
proof -
  have "a' divides a"
    by (meson \<open>a \<sim> a'\<close> associated_def)
  then show ?thesis
    by (metis (no_types) assms assoc_unit_l irreducibleE irreducibleI monoid.properfactor_trans2 monoid_axioms)
qed

lemma (in monoid) irreducible_prod_rI:
  assumes "irreducible G a" "b \<in> Units G" "a \<in> carrier G"  "b \<in> carrier G"
  shows "irreducible G (a \<otimes> b)"
  using assms
  by (metis (no_types, lifting) associatedI2' irreducible_def monoid.m_closed monoid_axioms prod_unit_r properfactor_cong_r)

lemma (in comm_monoid) irreducible_prod_lI:
  assumes birr: "irreducible G b"
    and aunit: "a \<in> Units G"
    and carr [simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "irreducible G (a \<otimes> b)"
  by (metis aunit birr carr irreducible_prod_rI m_comm)

lemma (in comm_monoid_cancel) irreducible_prodE [elim]:
  assumes irr: "irreducible G (a \<otimes> b)"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"
    and e1: "\<lbrakk>irreducible G a; b \<in> Units G\<rbrakk> \<Longrightarrow> P"
    and e2: "\<lbrakk>a \<in> Units G; irreducible G b\<rbrakk> \<Longrightarrow> P"
  shows P
  using irr
proof (elim irreducibleE)
  assume abnunit: "a \<otimes> b \<notin> Units G"
    and isunit[rule_format]: "\<forall>ba. ba \<in> carrier G \<and> properfactor G ba (a \<otimes> b) \<longrightarrow> ba \<in> Units G"
  show P
  proof (cases "a \<in> Units G")
    case aunit: True
    have "irreducible G b"
    proof (rule irreducibleI, rule notI)
      assume "b \<in> Units G"
      with aunit have "(a \<otimes> b) \<in> Units G" by fast
      with abnunit show "False" ..
    next
      fix c
      assume ccarr: "c \<in> carrier G"
        and "properfactor G c b"
      then have "properfactor G c (a \<otimes> b)" by (simp add: properfactor_prod_l[of c b a])
      with ccarr show "c \<in> Units G" by (fast intro: isunit)
    qed
    with aunit show "P" by (rule e2)
  next
    case anunit: False
    with carr have "properfactor G b (b \<otimes> a)" by (fast intro: properfactorI3)
    then have bf: "properfactor G b (a \<otimes> b)" by (subst m_comm[of a b], simp+)
    then have bunit: "b \<in> Units G" by (intro isunit, simp)

    have "irreducible G a"
    proof (rule irreducibleI, rule notI)
      assume "a \<in> Units G"
      with bunit have "(a \<otimes> b) \<in> Units G" by fast
      with abnunit show "False" ..
    next
      fix c
      assume ccarr: "c \<in> carrier G"
        and "properfactor G c a"
      then have "properfactor G c (a \<otimes> b)"
        by (simp add: properfactor_prod_r[of c a b])
      with ccarr show "c \<in> Units G" by (fast intro: isunit)
    qed
    from this bunit show "P" by (rule e1)
  qed
qed

lemma divides_irreducible_condition:
  assumes "irreducible G r" and "a \<in> carrier G"
  shows "a divides\<^bsub>G\<^esub> r \<Longrightarrow> a \<in> Units G \<or> a \<sim>\<^bsub>G\<^esub> r"
  using assms unfolding irreducible_def properfactor_def associated_def
  by (cases "r divides\<^bsub>G\<^esub> a", auto)

subsubsection \<open>Prime elements\<close>

lemma primeI:
  fixes G (structure)
  assumes "p \<notin> Units G"
    and "\<And>a b. \<lbrakk>a \<in> carrier G; b \<in> carrier G; p divides (a \<otimes> b)\<rbrakk> \<Longrightarrow> p divides a \<or> p divides b"
  shows "prime G p"
  using assms unfolding prime_def by blast

lemma primeE:
  fixes G (structure)
  assumes pprime: "prime G p"
    and e: "\<lbrakk>p \<notin> Units G; \<forall>a\<in>carrier G. \<forall>b\<in>carrier G.
      p divides a \<otimes> b \<longrightarrow> p divides a \<or> p divides b\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using pprime unfolding prime_def by (blast dest: e)

lemma (in comm_monoid_cancel) prime_divides:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"
    and pprime: "prime G p"
    and pdvd: "p divides a \<otimes> b"
  shows "p divides a \<or> p divides b"
  using assms by (blast elim: primeE)

lemma (in monoid_cancel) prime_cong [trans]:
  assumes "prime G p"
    and pp': "p \<sim> p'" "p \<in> carrier G"  "p' \<in> carrier G"
  shows "prime G p'"
  using assms
  by (auto simp: prime_def assoc_unit_l) (metis pp' associated_sym divides_cong_l)

lemma (in comm_monoid_cancel) prime_irreducible: \<^marker>\<open>contributor \<open>Paulo Emílio de Vilhena\<close>\<close>
  assumes "prime G p"
  shows "irreducible G p"
proof (rule irreducibleI)
  show "p \<notin> Units G"
    using assms unfolding prime_def by simp
next
  fix b assume A: "b \<in> carrier G" "properfactor G b p"
  then obtain c where c: "c \<in> carrier G" "p = b \<otimes> c"
    unfolding properfactor_def factor_def by auto
  hence "p divides c"
    using A assms unfolding prime_def properfactor_def by auto
  then obtain b' where b': "b' \<in> carrier G" "c = p \<otimes> b'"
    unfolding factor_def by auto
  hence "\<one> = b \<otimes> b'"
    by (metis A(1) l_cancel m_closed m_lcomm one_closed r_one c)
  thus "b \<in> Units G"
    using A(1) Units_one_closed b'(1) unit_factor by presburger
qed

lemma (in comm_monoid_cancel) prime_pow_divides_iff:
  assumes "p \<in> carrier G" "a \<in> carrier G" "b \<in> carrier G" and "prime G p" and "\<not> (p divides a)"
  shows "(p [^] (n :: nat)) divides (a \<otimes> b) \<longleftrightarrow> (p [^] n) divides b"
proof
  assume "(p [^] n) divides b" thus "(p [^] n) divides (a \<otimes> b)"
    using divides_prod_l[of "p [^] n" b a] assms by simp  
next
  assume "(p [^] n) divides (a \<otimes> b)" thus "(p [^] n) divides b"
  proof (induction n)
    case 0 with \<open>b \<in> carrier G\<close> show ?case
      by (simp add: unit_divides)
  next
    case (Suc n)
    hence "(p [^] n) divides (a \<otimes> b)" and "(p [^] n) divides b"
      using assms(1) divides_prod_r by auto
    with \<open>(p [^] (Suc n)) divides (a \<otimes> b)\<close> obtain c d
      where c: "c \<in> carrier G" and "b = (p [^] n) \<otimes> c"
        and d: "d \<in> carrier G" and "a \<otimes> b = (p [^] (Suc n)) \<otimes> d"
      using assms by blast
    hence "(p [^] n) \<otimes> (a \<otimes> c) = (p [^] n) \<otimes> (p \<otimes> d)"
      using assms by (simp add: m_assoc m_lcomm)
    hence "a \<otimes> c = p \<otimes> d"
      using c d assms(1) assms(2) l_cancel by blast
    with \<open>\<not> (p divides a)\<close> and \<open>prime G p\<close> have "p divides c"
      by (metis assms(2) c d dividesI' prime_divides)
    with \<open>b = (p [^] n) \<otimes> c\<close> show ?case
      using assms(1) c by simp
  qed
qed


subsection \<open>Factorization and Factorial Monoids\<close>

subsubsection \<open>Function definitions\<close>

definition factors :: "('a, _) monoid_scheme \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool"
  where "factors G fs a \<longleftrightarrow> (\<forall>x \<in> (set fs). irreducible G x) \<and> foldr (\<otimes>\<^bsub>G\<^esub>) fs \<one>\<^bsub>G\<^esub> = a"

definition wfactors ::"('a, _) monoid_scheme \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> bool"
  where "wfactors G fs a \<longleftrightarrow> (\<forall>x \<in> (set fs). irreducible G x) \<and> foldr (\<otimes>\<^bsub>G\<^esub>) fs \<one>\<^bsub>G\<^esub> \<sim>\<^bsub>G\<^esub> a"

abbreviation list_assoc :: "('a, _) monoid_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "[\<sim>]\<index>" 44)
  where "list_assoc G \<equiv> list_all2 (\<sim>\<^bsub>G\<^esub>)"

definition essentially_equal :: "('a, _) monoid_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "essentially_equal G fs1 fs2 \<longleftrightarrow> (\<exists>fs1'. fs1 <~~> fs1' \<and> fs1' [\<sim>]\<^bsub>G\<^esub> fs2)"


locale factorial_monoid = comm_monoid_cancel +
  assumes factors_exist: "\<lbrakk>a \<in> carrier G; a \<notin> Units G\<rbrakk> \<Longrightarrow> \<exists>fs. set fs \<subseteq> carrier G \<and> factors G fs a"
    and factors_unique:
      "\<lbrakk>factors G fs a; factors G fs' a; a \<in> carrier G; a \<notin> Units G;
        set fs \<subseteq> carrier G; set fs' \<subseteq> carrier G\<rbrakk> \<Longrightarrow> essentially_equal G fs fs'"


subsubsection \<open>Comparing lists of elements\<close>

text \<open>Association on lists\<close>

lemma (in monoid) listassoc_refl [simp, intro]:
  assumes "set as \<subseteq> carrier G"
  shows "as [\<sim>] as"
  using assms by (induct as) simp_all

lemma (in monoid) listassoc_sym [sym]:
  assumes "as [\<sim>] bs"
    and "set as \<subseteq> carrier G"
    and "set bs \<subseteq> carrier G"
  shows "bs [\<sim>] as"
  using assms
proof (induction as arbitrary: bs)
  case Cons
  then show ?case
    by (induction bs) (use associated_sym in auto)
qed auto

lemma (in monoid) listassoc_trans [trans]:
  assumes "as [\<sim>] bs" and "bs [\<sim>] cs"
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G" and "set cs \<subseteq> carrier G"
  shows "as [\<sim>] cs"
  using assms
  apply (simp add: list_all2_conv_all_nth set_conv_nth, safe)
  by (metis (mono_tags, lifting) associated_trans nth_mem subsetCE)

lemma (in monoid_cancel) irrlist_listassoc_cong:
  assumes "\<forall>a\<in>set as. irreducible G a"
    and "as [\<sim>] bs"
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "\<forall>a\<in>set bs. irreducible G a"
  using assms
  by (fastforce simp add: list_all2_conv_all_nth set_conv_nth intro: irreducible_cong)


text \<open>Permutations\<close>

lemma perm_map [intro]:
  assumes p: "a <~~> b"
  shows "map f a <~~> map f b"
  using p by simp

lemma perm_map_switch:
  assumes m: "map f a = map f b" and p: "b <~~> c"
  shows "\<exists>d. a <~~> d \<and> map f d = map f c"
proof -
  from m have \<open>length a = length b\<close>
    by (rule map_eq_imp_length_eq)
  from p have \<open>mset c = mset b\<close>
    by simp
  then obtain p where \<open>p permutes {..<length b}\<close> \<open>permute_list p b = c\<close>
    by (rule mset_eq_permutation)
  with \<open>length a = length b\<close> have \<open>p permutes {..<length a}\<close>
    by simp
  moreover define d where \<open>d = permute_list p a\<close>
  ultimately have \<open>mset a = mset d\<close> \<open>map f d = map f c\<close>
    using m \<open>p permutes {..<length b}\<close> \<open>permute_list p b = c\<close>
    by (auto simp flip: permute_list_map)
  then show ?thesis
    by auto
qed

lemma (in monoid) perm_assoc_switch:
  assumes a:"as [\<sim>] bs" and p: "bs <~~> cs"
  shows "\<exists>bs'. as <~~> bs' \<and> bs' [\<sim>] cs"
proof -
  from p have \<open>mset cs = mset bs\<close>
    by simp
  then obtain p where \<open>p permutes {..<length bs}\<close> \<open>permute_list p bs = cs\<close>
    by (rule mset_eq_permutation)
  moreover define bs' where \<open>bs' = permute_list p as\<close>
  ultimately have \<open>as <~~> bs'\<close> and \<open>bs' [\<sim>] cs\<close>
    using a by (auto simp add: list_all2_permute_list_iff list_all2_lengthD)
  then show ?thesis by blast
qed

lemma (in monoid) perm_assoc_switch_r:
  assumes p: "as <~~> bs" and a:"bs [\<sim>] cs"
  shows "\<exists>bs'. as [\<sim>] bs' \<and> bs' <~~> cs"
  using a p by (rule list_all2_reorder_left_invariance)

declare perm_sym [sym]

lemma perm_setP:
  assumes perm: "as <~~> bs"
    and as: "P (set as)"
  shows "P (set bs)"
  using assms by (metis set_mset_mset)

lemmas (in monoid) perm_closed = perm_setP[of _ _ "\<lambda>as. as \<subseteq> carrier G"]

lemmas (in monoid) irrlist_perm_cong = perm_setP[of _ _ "\<lambda>as. \<forall>a\<in>as. irreducible G a"]


text \<open>Essentially equal factorizations\<close>

lemma (in monoid) essentially_equalI:
  assumes ex: "fs1 <~~> fs1'"  "fs1' [\<sim>] fs2"
  shows "essentially_equal G fs1 fs2"
  using ex unfolding essentially_equal_def by fast

lemma (in monoid) essentially_equalE:
  assumes ee: "essentially_equal G fs1 fs2"
    and e: "\<And>fs1'. \<lbrakk>fs1 <~~> fs1'; fs1' [\<sim>] fs2\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using ee unfolding essentially_equal_def by (fast intro: e)

lemma (in monoid) ee_refl [simp,intro]:
  assumes carr: "set as \<subseteq> carrier G"
  shows "essentially_equal G as as"
  using carr by (fast intro: essentially_equalI)

lemma (in monoid) ee_sym [sym]:
  assumes ee: "essentially_equal G as bs"
    and carr: "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"
  shows "essentially_equal G bs as"
  using ee
proof (elim essentially_equalE)
  fix fs
  assume "as <~~> fs"  "fs [\<sim>] bs"
  from perm_assoc_switch_r [OF this] obtain fs' where a: "as [\<sim>] fs'" and p: "fs' <~~> bs"
    by blast
  from p have "bs <~~> fs'" by (rule perm_sym)
  with a[symmetric] carr show ?thesis
    by (iprover intro: essentially_equalI perm_closed)
qed

lemma (in monoid) ee_trans [trans]:
  assumes ab: "essentially_equal G as bs" and bc: "essentially_equal G bs cs"
    and ascarr: "set as \<subseteq> carrier G"
    and bscarr: "set bs \<subseteq> carrier G"
    and cscarr: "set cs \<subseteq> carrier G"
  shows "essentially_equal G as cs"
  using ab bc
proof (elim essentially_equalE)
  fix abs bcs
  assume "abs [\<sim>] bs" and pb: "bs <~~> bcs"
  from perm_assoc_switch [OF this] obtain bs' where p: "abs <~~> bs'" and a: "bs' [\<sim>] bcs"
    by blast
  assume "as <~~> abs"
  with p have pp: "as <~~> bs'" by simp
  from pp ascarr have c1: "set bs' \<subseteq> carrier G" by (rule perm_closed)
  from pb bscarr have c2: "set bcs \<subseteq> carrier G" by (rule perm_closed)
  assume "bcs [\<sim>] cs"
  then have "bs' [\<sim>] cs"
    using a c1 c2 cscarr listassoc_trans by blast
  with pp show ?thesis
    by (rule essentially_equalI)
qed


subsubsection \<open>Properties of lists of elements\<close>

text \<open>Multiplication of factors in a list\<close>

lemma (in monoid) multlist_closed [simp, intro]:
  assumes ascarr: "set fs \<subseteq> carrier G"
  shows "foldr (\<otimes>) fs \<one> \<in> carrier G"
  using ascarr by (induct fs) simp_all

lemma  (in comm_monoid) multlist_dividesI:
  assumes "f \<in> set fs" and "set fs \<subseteq> carrier G"
  shows "f divides (foldr (\<otimes>) fs \<one>)"
  using assms
proof (induction fs)
  case (Cons a fs)
  then have f: "f \<in> carrier G"
    by blast
  show ?case
    using Cons.IH Cons.prems(1) Cons.prems(2) divides_prod_l f by auto
qed auto

lemma (in comm_monoid_cancel) multlist_listassoc_cong:
  assumes "fs [\<sim>] fs'"
    and "set fs \<subseteq> carrier G" and "set fs' \<subseteq> carrier G"
  shows "foldr (\<otimes>) fs \<one> \<sim> foldr (\<otimes>) fs' \<one>"
  using assms
proof (induct fs arbitrary: fs')
  case (Cons a as fs')
  then show ?case
  proof (induction fs')
    case (Cons b bs)
    then have p: "a \<otimes> foldr (\<otimes>) as \<one> \<sim> b \<otimes> foldr (\<otimes>) as \<one>"
      by (simp add: mult_cong_l)
    then have "foldr (\<otimes>) as \<one> \<sim> foldr (\<otimes>) bs \<one>"
      using Cons by auto
    with Cons have "b \<otimes> foldr (\<otimes>) as \<one> \<sim> b \<otimes> foldr (\<otimes>) bs \<one>"
      by (simp add: mult_cong_r)
    then show ?case
      using Cons.prems(3) Cons.prems(4) monoid.associated_trans monoid_axioms p by force
  qed auto
qed auto

lemma (in comm_monoid) multlist_perm_cong:
  assumes prm: "as <~~> bs"
    and ascarr: "set as \<subseteq> carrier G"
  shows "foldr (\<otimes>) as \<one> = foldr (\<otimes>) bs \<one>"
proof -
  from prm have \<open>mset (rev as) = mset (rev bs)\<close>
    by simp
  moreover note one_closed
  ultimately have \<open>fold (\<otimes>) (rev as) \<one> = fold (\<otimes>) (rev bs) \<one>\<close>
    by (rule fold_permuted_eq) (use ascarr in \<open>auto intro: m_lcomm\<close>)
  then show ?thesis
    by (simp add: foldr_conv_fold)
qed

lemma (in comm_monoid_cancel) multlist_ee_cong:
  assumes "essentially_equal G fs fs'"
    and "set fs \<subseteq> carrier G" and "set fs' \<subseteq> carrier G"
  shows "foldr (\<otimes>) fs \<one> \<sim> foldr (\<otimes>) fs' \<one>"
  using assms
  by (metis essentially_equal_def multlist_listassoc_cong multlist_perm_cong perm_closed)


subsubsection \<open>Factorization in irreducible elements\<close>

lemma wfactorsI:
  fixes G (structure)
  assumes "\<forall>f\<in>set fs. irreducible G f"
    and "foldr (\<otimes>) fs \<one> \<sim> a"
  shows "wfactors G fs a"
  using assms unfolding wfactors_def by simp

lemma wfactorsE:
  fixes G (structure)
  assumes wf: "wfactors G fs a"
    and e: "\<lbrakk>\<forall>f\<in>set fs. irreducible G f; foldr (\<otimes>) fs \<one> \<sim> a\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using wf unfolding wfactors_def by (fast dest: e)

lemma (in monoid) factorsI:
  assumes "\<forall>f\<in>set fs. irreducible G f"
    and "foldr (\<otimes>) fs \<one> = a"
  shows "factors G fs a"
  using assms unfolding factors_def by simp

lemma factorsE:
  fixes G (structure)
  assumes f: "factors G fs a"
    and e: "\<lbrakk>\<forall>f\<in>set fs. irreducible G f; foldr (\<otimes>) fs \<one> = a\<rbrakk> \<Longrightarrow> P"
  shows "P"
  using f unfolding factors_def by (simp add: e)

lemma (in monoid) factors_wfactors:
  assumes "factors G as a" and "set as \<subseteq> carrier G"
  shows "wfactors G as a"
  using assms by (blast elim: factorsE intro: wfactorsI)

lemma (in monoid) wfactors_factors:
  assumes "wfactors G as a" and "set as \<subseteq> carrier G"
  shows "\<exists>a'. factors G as a' \<and> a' \<sim> a"
  using assms by (blast elim: wfactorsE intro: factorsI)

lemma (in monoid) factors_closed [dest]:
  assumes "factors G fs a" and "set fs \<subseteq> carrier G"
  shows "a \<in> carrier G"
  using assms by (elim factorsE, clarsimp)

lemma (in monoid) nunit_factors:
  assumes anunit: "a \<notin> Units G"
    and fs: "factors G as a"
  shows "length as > 0"
proof -
  from anunit Units_one_closed have "a \<noteq> \<one>" by auto
  with fs show ?thesis by (auto elim: factorsE)
qed

lemma (in monoid) unit_wfactors [simp]:
  assumes aunit: "a \<in> Units G"
  shows "wfactors G [] a"
  using aunit by (intro wfactorsI) (simp, simp add: Units_assoc)

lemma (in comm_monoid_cancel) unit_wfactors_empty:
  assumes aunit: "a \<in> Units G"
    and wf: "wfactors G fs a"
    and carr[simp]: "set fs \<subseteq> carrier G"
  shows "fs = []"
proof (cases fs)
  case fs: (Cons f fs')
  from carr have fcarr[simp]: "f \<in> carrier G" and carr'[simp]: "set fs' \<subseteq> carrier G"
    by (simp_all add: fs)

  from fs wf have "irreducible G f" by (simp add: wfactors_def)
  then have fnunit: "f \<notin> Units G" by (fast elim: irreducibleE)

  from fs wf have a: "f \<otimes> foldr (\<otimes>) fs' \<one> \<sim> a" by (simp add: wfactors_def)

  note aunit
  also from fs wf
  have a: "f \<otimes> foldr (\<otimes>) fs' \<one> \<sim> a" by (simp add: wfactors_def)
  have "a \<sim> f \<otimes> foldr (\<otimes>) fs' \<one>"
    by (simp add: Units_closed[OF aunit] a[symmetric])
  finally have "f \<otimes> foldr (\<otimes>) fs' \<one> \<in> Units G" by simp
  then have "f \<in> Units G" by (intro unit_factor[of f], simp+)
  with fnunit show ?thesis by contradiction
qed


text \<open>Comparing wfactors\<close>

lemma (in comm_monoid_cancel) wfactors_listassoc_cong_l:
  assumes fact: "wfactors G fs a"
    and asc: "fs [\<sim>] fs'"
    and carr: "a \<in> carrier G"  "set fs \<subseteq> carrier G"  "set fs' \<subseteq> carrier G"
  shows "wfactors G fs' a"
proof -
  { from asc[symmetric] have "foldr (\<otimes>) fs' \<one> \<sim> foldr (\<otimes>) fs \<one>"
      by (simp add: multlist_listassoc_cong carr)
    also assume "foldr (\<otimes>) fs \<one> \<sim> a"
    finally have "foldr (\<otimes>) fs' \<one> \<sim> a" by (simp add: carr) }
  then show ?thesis
  using fact
  by (meson asc carr(2) carr(3) irrlist_listassoc_cong wfactors_def)
qed

lemma (in comm_monoid) wfactors_perm_cong_l:
  assumes "wfactors G fs a"
    and "fs <~~> fs'"
    and "set fs \<subseteq> carrier G"
  shows "wfactors G fs' a"
  using assms irrlist_perm_cong multlist_perm_cong wfactors_def by fastforce

lemma (in comm_monoid_cancel) wfactors_ee_cong_l [trans]:
  assumes ee: "essentially_equal G as bs"
    and bfs: "wfactors G bs b"
    and carr: "b \<in> carrier G"  "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"
  shows "wfactors G as b"
  using ee
proof (elim essentially_equalE)
  fix fs
  assume prm: "as <~~> fs"
  with carr have fscarr: "set fs \<subseteq> carrier G"
    using perm_closed by blast

  note bfs
  also assume [symmetric]: "fs [\<sim>] bs"
  also (wfactors_listassoc_cong_l)
  have \<open>mset fs = mset as\<close> using prm by simp
  finally (wfactors_perm_cong_l)
  show "wfactors G as b" by (simp add: carr fscarr)
qed

lemma (in monoid) wfactors_cong_r [trans]:
  assumes fac: "wfactors G fs a" and aa': "a \<sim> a'"
    and carr[simp]: "a \<in> carrier G"  "a' \<in> carrier G"  "set fs \<subseteq> carrier G"
  shows "wfactors G fs a'"
  using fac
proof (elim wfactorsE, intro wfactorsI)
  assume "foldr (\<otimes>) fs \<one> \<sim> a" also note aa'
  finally show "foldr (\<otimes>) fs \<one> \<sim> a'" by simp
qed


subsubsection \<open>Essentially equal factorizations\<close>

lemma (in comm_monoid_cancel) unitfactor_ee:
  assumes uunit: "u \<in> Units G"
    and carr: "set as \<subseteq> carrier G"
  shows "essentially_equal G (as[0 := (as!0 \<otimes> u)]) as"
    (is "essentially_equal G ?as' as")
proof -
  have "as[0 := as ! 0 \<otimes> u] [\<sim>] as"
  proof (cases as)
    case (Cons a as')
    then show ?thesis
      using associatedI2 carr uunit by auto
  qed auto
  then show ?thesis
    using essentially_equal_def by blast
qed

lemma (in comm_monoid_cancel) factors_cong_unit:
  assumes u: "u \<in> Units G"
    and a: "a \<notin> Units G"
    and afs: "factors G as a"
    and ascarr: "set as \<subseteq> carrier G"
  shows "factors G (as[0 := (as!0 \<otimes> u)]) (a \<otimes> u)"
    (is "factors G ?as' ?a'")
proof (cases as)
  case Nil
  then show ?thesis
    using afs a nunit_factors by auto
next
  case (Cons b bs)
  have *: "\<forall>f\<in>set as. irreducible G f" "foldr (\<otimes>) as \<one> = a"
    using afs  by (auto simp: factors_def)
  show ?thesis
  proof (intro factorsI)
    show "foldr (\<otimes>) (as[0 := as ! 0 \<otimes> u]) \<one> = a \<otimes> u"
      using Cons u ascarr * by (auto simp add: m_ac Units_closed)
    show "\<forall>f\<in>set (as[0 := as ! 0 \<otimes> u]). irreducible G f"
      using Cons u ascarr * by (force intro: irreducible_prod_rI)
  qed 
qed

lemma (in comm_monoid) perm_wfactorsD:
  assumes prm: "as <~~> bs"
    and afs: "wfactors G as a"
    and bfs: "wfactors G bs b"
    and [simp]: "a \<in> carrier G"  "b \<in> carrier G"
    and ascarr [simp]: "set as \<subseteq> carrier G"
  shows "a \<sim> b"
  using afs bfs
proof (elim wfactorsE)
  from prm have [simp]: "set bs \<subseteq> carrier G" by (simp add: perm_closed)
  assume "foldr (\<otimes>) as \<one> \<sim> a"
  then have "a \<sim> foldr (\<otimes>) as \<one>"
    by (simp add: associated_sym)
  also from prm
  have "foldr (\<otimes>) as \<one> = foldr (\<otimes>) bs \<one>" by (rule multlist_perm_cong, simp)
  also assume "foldr (\<otimes>) bs \<one> \<sim> b"
  finally show "a \<sim> b" by simp
qed

lemma (in comm_monoid_cancel) listassoc_wfactorsD:
  assumes assoc: "as [\<sim>] bs"
    and afs: "wfactors G as a"
    and bfs: "wfactors G bs b"
    and [simp]: "a \<in> carrier G"  "b \<in> carrier G"
    and [simp]: "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"
  shows "a \<sim> b"
  using afs bfs
proof (elim wfactorsE)
  assume "foldr (\<otimes>) as \<one> \<sim> a"
  then have "a \<sim> foldr (\<otimes>) as \<one>" by (simp add: associated_sym)
  also from assoc
  have "foldr (\<otimes>) as \<one> \<sim> foldr (\<otimes>) bs \<one>" by (rule multlist_listassoc_cong, simp+)
  also assume "foldr (\<otimes>) bs \<one> \<sim> b"
  finally show "a \<sim> b" by simp
qed

lemma (in comm_monoid_cancel) ee_wfactorsD:
  assumes ee: "essentially_equal G as bs"
    and afs: "wfactors G as a" and bfs: "wfactors G bs b"
    and [simp]: "a \<in> carrier G"  "b \<in> carrier G"
    and ascarr[simp]: "set as \<subseteq> carrier G" and bscarr[simp]: "set bs \<subseteq> carrier G"
  shows "a \<sim> b"
  using ee
proof (elim essentially_equalE)
  fix fs
  assume prm: "as <~~> fs"
  then have as'carr[simp]: "set fs \<subseteq> carrier G"
    by (simp add: perm_closed)
  from afs prm have afs': "wfactors G fs a"
    by (rule wfactors_perm_cong_l) simp
  assume "fs [\<sim>] bs"
  from this afs' bfs show "a \<sim> b"
    by (rule listassoc_wfactorsD) simp_all
qed

lemma (in comm_monoid_cancel) ee_factorsD:
  assumes ee: "essentially_equal G as bs"
    and afs: "factors G as a" and bfs:"factors G bs b"
    and "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"
  shows "a \<sim> b"
  using assms by (blast intro: factors_wfactors dest: ee_wfactorsD)

lemma (in factorial_monoid) ee_factorsI:
  assumes ab: "a \<sim> b"
    and afs: "factors G as a" and anunit: "a \<notin> Units G"
    and bfs: "factors G bs b" and bnunit: "b \<notin> Units G"
    and ascarr: "set as \<subseteq> carrier G" and bscarr: "set bs \<subseteq> carrier G"
  shows "essentially_equal G as bs"
proof -
  note carr[simp] = factors_closed[OF afs ascarr] ascarr[THEN subsetD]
    factors_closed[OF bfs bscarr] bscarr[THEN subsetD]

  from ab carr obtain u where uunit: "u \<in> Units G" and a: "a = b \<otimes> u"
    by (elim associatedE2)

  from uunit bscarr have ee: "essentially_equal G (bs[0 := (bs!0 \<otimes> u)]) bs"
    (is "essentially_equal G ?bs' bs")
    by (rule unitfactor_ee)

  from bscarr uunit have bs'carr: "set ?bs' \<subseteq> carrier G"
    by (cases bs) (simp_all add: Units_closed)

  from uunit bnunit bfs bscarr have fac: "factors G ?bs' (b \<otimes> u)"
    by (rule factors_cong_unit)

  from afs fac[simplified a[symmetric]] ascarr bs'carr anunit
  have "essentially_equal G as ?bs'"
    by (blast intro: factors_unique)
  also note ee
  finally show "essentially_equal G as bs"
    by (simp add: ascarr bscarr bs'carr)
qed

lemma (in factorial_monoid) ee_wfactorsI:
  assumes asc: "a \<sim> b"
    and asf: "wfactors G as a" and bsf: "wfactors G bs b"
    and acarr[simp]: "a \<in> carrier G" and bcarr[simp]: "b \<in> carrier G"
    and ascarr[simp]: "set as \<subseteq> carrier G" and bscarr[simp]: "set bs \<subseteq> carrier G"
  shows "essentially_equal G as bs"
  using assms
proof (cases "a \<in> Units G")
  case aunit: True
  also note asc
  finally have bunit: "b \<in> Units G" by simp

  from aunit asf ascarr have e: "as = []"
    by (rule unit_wfactors_empty)
  from bunit bsf bscarr have e': "bs = []"
    by (rule unit_wfactors_empty)

  have "essentially_equal G [] []"
    by (fast intro: essentially_equalI)
  then show ?thesis
    by (simp add: e e')
next
  case anunit: False
  have bnunit: "b \<notin> Units G"
  proof clarify
    assume "b \<in> Units G"
    also note asc[symmetric]
    finally have "a \<in> Units G" by simp
    with anunit show False ..
  qed

  from wfactors_factors[OF asf ascarr] obtain a' where fa': "factors G as a'" and a': "a' \<sim> a"
    by blast
  from fa' ascarr have a'carr[simp]: "a' \<in> carrier G"
    by fast

  have a'nunit: "a' \<notin> Units G"
  proof clarify
    assume "a' \<in> Units G"
    also note a'
    finally have "a \<in> Units G" by simp
    with anunit
    show "False" ..
  qed

  from wfactors_factors[OF bsf bscarr] obtain b' where fb': "factors G bs b'" and b': "b' \<sim> b"
    by blast
  from fb' bscarr have b'carr[simp]: "b' \<in> carrier G"
    by fast

  have b'nunit: "b' \<notin> Units G"
  proof clarify
    assume "b' \<in> Units G"
    also note b'
    finally have "b \<in> Units G" by simp
    with bnunit show False ..
  qed

  note a'
  also note asc
  also note b'[symmetric]
  finally have "a' \<sim> b'" by simp
  from this fa' a'nunit fb' b'nunit ascarr bscarr show "essentially_equal G as bs"
    by (rule ee_factorsI)
qed

lemma (in factorial_monoid) ee_wfactors:
  assumes asf: "wfactors G as a"
    and bsf: "wfactors G bs b"
    and acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G"
    and ascarr: "set as \<subseteq> carrier G" and bscarr: "set bs \<subseteq> carrier G"
  shows asc: "a \<sim> b = essentially_equal G as bs"
  using assms by (fast intro: ee_wfactorsI ee_wfactorsD)

lemma (in factorial_monoid) wfactors_exist [intro, simp]:
  assumes acarr[simp]: "a \<in> carrier G"
  shows "\<exists>fs. set fs \<subseteq> carrier G \<and> wfactors G fs a"
proof (cases "a \<in> Units G")
  case True
  then have "wfactors G [] a" by (rule unit_wfactors)
  then show ?thesis by (intro exI) force
next
  case False
  with factors_exist [OF acarr] obtain fs where fscarr: "set fs \<subseteq> carrier G" and f: "factors G fs a"
    by blast
  from f have "wfactors G fs a" by (rule factors_wfactors) fact
  with fscarr show ?thesis by fast
qed

lemma (in monoid) wfactors_prod_exists [intro, simp]:
  assumes "\<forall>a \<in> set as. irreducible G a" and "set as \<subseteq> carrier G"
  shows "\<exists>a. a \<in> carrier G \<and> wfactors G as a"
  unfolding wfactors_def using assms by blast

lemma (in factorial_monoid) wfactors_unique:
  assumes "wfactors G fs a"
    and "wfactors G fs' a"
    and "a \<in> carrier G"
    and "set fs \<subseteq> carrier G"
    and "set fs' \<subseteq> carrier G"
  shows "essentially_equal G fs fs'"
  using assms by (fast intro: ee_wfactorsI[of a a])

lemma (in monoid) factors_mult_single:
  assumes "irreducible G a" and "factors G fb b" and "a \<in> carrier G"
  shows "factors G (a # fb) (a \<otimes> b)"
  using assms unfolding factors_def by simp

lemma (in monoid_cancel) wfactors_mult_single:
  assumes f: "irreducible G a"  "wfactors G fb b"
    "a \<in> carrier G"  "b \<in> carrier G"  "set fb \<subseteq> carrier G"
  shows "wfactors G (a # fb) (a \<otimes> b)"
  using assms unfolding wfactors_def by (simp add: mult_cong_r)

lemma (in monoid) factors_mult:
  assumes factors: "factors G fa a"  "factors G fb b"
    and ascarr: "set fa \<subseteq> carrier G"
    and bscarr: "set fb \<subseteq> carrier G"
  shows "factors G (fa @ fb) (a \<otimes> b)"
proof -
  have "foldr (\<otimes>) (fa @ fb) \<one> = foldr (\<otimes>) fa \<one> \<otimes> foldr (\<otimes>) fb \<one>" if "set fa \<subseteq> carrier G" 
    "Ball (set fa) (irreducible G)"
    using that bscarr by (induct fa) (simp_all add: m_assoc)
  then show ?thesis
    using assms unfolding factors_def by force
qed

lemma (in comm_monoid_cancel) wfactors_mult [intro]:
  assumes asf: "wfactors G as a" and bsf:"wfactors G bs b"
    and acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G"
    and ascarr: "set as \<subseteq> carrier G" and bscarr:"set bs \<subseteq> carrier G"
  shows "wfactors G (as @ bs) (a \<otimes> b)"
  using wfactors_factors[OF asf ascarr] and wfactors_factors[OF bsf bscarr]
proof clarsimp
  fix a' b'
  assume asf': "factors G as a'" and a'a: "a' \<sim> a"
    and bsf': "factors G bs b'" and b'b: "b' \<sim> b"
  from asf' have a'carr: "a' \<in> carrier G" by (rule factors_closed) fact
  from bsf' have b'carr: "b' \<in> carrier G" by (rule factors_closed) fact

  note carr = acarr bcarr a'carr b'carr ascarr bscarr

  from asf' bsf' have "factors G (as @ bs) (a' \<otimes> b')"
    by (rule factors_mult) fact+

  with carr have abf': "wfactors G (as @ bs) (a' \<otimes> b')"
    by (intro factors_wfactors) simp_all
  also from b'b carr have trb: "a' \<otimes> b' \<sim> a' \<otimes> b"
    by (intro mult_cong_r)
  also from a'a carr have tra: "a' \<otimes> b \<sim> a \<otimes> b"
    by (intro mult_cong_l)
  finally show "wfactors G (as @ bs) (a \<otimes> b)"
    by (simp add: carr)
qed

lemma (in comm_monoid) factors_dividesI:
  assumes "factors G fs a"
    and "f \<in> set fs"
    and "set fs \<subseteq> carrier G"
  shows "f divides a"
  using assms by (fast elim: factorsE intro: multlist_dividesI)

lemma (in comm_monoid) wfactors_dividesI:
  assumes p: "wfactors G fs a"
    and fscarr: "set fs \<subseteq> carrier G" and acarr: "a \<in> carrier G"
    and f: "f \<in> set fs"
  shows "f divides a"
  using wfactors_factors[OF p fscarr]
proof clarsimp
  fix a'
  assume fsa': "factors G fs a'" and a'a: "a' \<sim> a"
  with fscarr have a'carr: "a' \<in> carrier G"
    by (simp add: factors_closed)

  from fsa' fscarr f have "f divides a'"
    by (fast intro: factors_dividesI)
  also note a'a
  finally show "f divides a"
    by (simp add: f fscarr[THEN subsetD] acarr a'carr)
qed


subsubsection \<open>Factorial monoids and wfactors\<close>

lemma (in comm_monoid_cancel) factorial_monoidI:
  assumes wfactors_exists: "\<And>a. \<lbrakk> a \<in> carrier G; a \<notin> Units G \<rbrakk> \<Longrightarrow> \<exists>fs. set fs \<subseteq> carrier G \<and> wfactors G fs a"
    and wfactors_unique:
      "\<And>a fs fs'. \<lbrakk>a \<in> carrier G; set fs \<subseteq> carrier G; set fs' \<subseteq> carrier G;
        wfactors G fs a; wfactors G fs' a\<rbrakk> \<Longrightarrow> essentially_equal G fs fs'"
  shows "factorial_monoid G"
proof
  fix a
  assume acarr: "a \<in> carrier G" and anunit: "a \<notin> Units G"
  from wfactors_exists[OF acarr anunit]
  obtain as where ascarr: "set as \<subseteq> carrier G" and afs: "wfactors G as a"
    by blast
  from wfactors_factors [OF afs ascarr] obtain a' where afs': "factors G as a'" and a'a: "a' \<sim> a"
    by blast
  from afs' ascarr have a'carr: "a' \<in> carrier G"
    by fast
  have a'nunit: "a' \<notin> Units G"
  proof clarify
    assume "a' \<in> Units G"
    also note a'a
    finally have "a \<in> Units G" by (simp add: acarr)
    with anunit show False ..
  qed

  from a'carr acarr a'a obtain u where uunit: "u \<in> Units G" and a': "a' = a \<otimes> u"
    by (blast elim: associatedE2)

  note [simp] = acarr Units_closed[OF uunit] Units_inv_closed[OF uunit]
  have "a = a \<otimes> \<one>" by simp
  also have "\<dots> = a \<otimes> (u \<otimes> inv u)" by (simp add: uunit)
  also have "\<dots> = a' \<otimes> inv u" by (simp add: m_assoc[symmetric] a'[symmetric])
  finally have a: "a = a' \<otimes> inv u" .

  from ascarr uunit have cr: "set (as[0:=(as!0 \<otimes> inv u)]) \<subseteq> carrier G"
    by (cases as) auto
  from afs' uunit a'nunit acarr ascarr have "factors G (as[0:=(as!0 \<otimes> inv u)]) a"
    by (simp add: a factors_cong_unit)
  with cr show "\<exists>fs. set fs \<subseteq> carrier G \<and> factors G fs a"
    by fast
qed (blast intro: factors_wfactors wfactors_unique)


subsection \<open>Factorizations as Multisets\<close>

text \<open>Gives useful operations like intersection\<close>

(* FIXME: use class_of x instead of closure_of {x} *)

abbreviation "assocs G x \<equiv> eq_closure_of (division_rel G) {x}"

definition "fmset G as = mset (map (assocs G) as)"


text \<open>Helper lemmas\<close>

lemma (in monoid) assocs_repr_independence:
  assumes "y \<in> assocs G x" "x \<in> carrier G"
  shows "assocs G x = assocs G y"
  using assms
  by (simp add: eq_closure_of_def elem_def) (use associated_sym associated_trans in \<open>blast+\<close>)

lemma (in monoid) assocs_self:
  assumes "x \<in> carrier G"
  shows "x \<in> assocs G x"
  using assms by (fastforce intro: closure_ofI2)

lemma (in monoid) assocs_repr_independenceD:
  assumes repr: "assocs G x = assocs G y" and ycarr: "y \<in> carrier G"
  shows "y \<in> assocs G x"
  unfolding repr using ycarr by (intro assocs_self)

lemma (in comm_monoid) assocs_assoc:
  assumes "a \<in> assocs G b" "b \<in> carrier G"
  shows "a \<sim> b"
  using assms by (elim closure_ofE2) simp

lemmas (in comm_monoid) assocs_eqD = assocs_repr_independenceD[THEN assocs_assoc]


subsubsection \<open>Comparing multisets\<close>

lemma (in monoid) fmset_perm_cong:
  assumes prm: "as <~~> bs"
  shows "fmset G as = fmset G bs"
  using perm_map[OF prm] unfolding fmset_def by blast

lemma (in comm_monoid_cancel) eqc_listassoc_cong:
  assumes "as [\<sim>] bs" and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "map (assocs G) as = map (assocs G) bs"
  using assms
proof (induction as arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case
  proof (clarsimp simp add: Cons_eq_map_conv list_all2_Cons1)
    fix z zs 
    assume zzs: "a \<in> carrier G" "set as \<subseteq> carrier G" "bs = z # zs" "a \<sim> z"
      "as [\<sim>] zs" "z \<in> carrier G" "set zs \<subseteq> carrier G"
    then show "assocs G a = assocs G z"
      apply (simp add: eq_closure_of_def elem_def)
      using \<open>a \<in> carrier G\<close> \<open>z \<in> carrier G\<close> \<open>a \<sim> z\<close> associated_sym associated_trans by blast+
  qed
qed

lemma (in comm_monoid_cancel) fmset_listassoc_cong:
  assumes "as [\<sim>] bs"
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "fmset G as = fmset G bs"
  using assms unfolding fmset_def by (simp add: eqc_listassoc_cong)

lemma (in comm_monoid_cancel) ee_fmset:
  assumes ee: "essentially_equal G as bs"
    and ascarr: "set as \<subseteq> carrier G" and bscarr: "set bs \<subseteq> carrier G"
  shows "fmset G as = fmset G bs"
  using ee
  thm essentially_equal_def
proof (elim essentially_equalE)
  fix as'
  assume prm: "as <~~> as'"
  from prm ascarr have as'carr: "set as' \<subseteq> carrier G"
    by (rule perm_closed)
  from prm have "fmset G as = fmset G as'"
    by (rule fmset_perm_cong)
  also assume "as' [\<sim>] bs"
  with as'carr bscarr have "fmset G as' = fmset G bs"
    by (simp add: fmset_listassoc_cong)
  finally show "fmset G as = fmset G bs" .
qed

lemma (in comm_monoid_cancel) fmset_ee:
  assumes mset: "fmset G as = fmset G bs"
    and ascarr: "set as \<subseteq> carrier G" and bscarr: "set bs \<subseteq> carrier G"
  shows "essentially_equal G as bs"
proof -
  from mset have "mset (map (assocs G) bs) = mset (map (assocs G) as)"
    by (simp add: fmset_def)
  then obtain p where \<open>p permutes {..<length (map (assocs G) as)}\<close>
    \<open>permute_list p (map (assocs G) as) = map (assocs G) bs\<close>
    by (rule mset_eq_permutation)
  then have \<open>p permutes {..<length as}\<close>
    \<open>map (assocs G) (permute_list p as) = map (assocs G) bs\<close>
    by (simp_all add: permute_list_map) 
  moreover define as' where \<open>as' = permute_list p as\<close>
  ultimately have tp: "as <~~> as'" and tm: "map (assocs G) as' = map (assocs G) bs"
    by simp_all
  from tp show ?thesis
  proof (rule essentially_equalI)
    from tm tp ascarr have as'carr: "set as' \<subseteq> carrier G"
      using perm_closed by blast
    from tm as'carr[THEN subsetD] bscarr[THEN subsetD] show "as' [\<sim>] bs"
      by (induct as' arbitrary: bs) (simp, fastforce dest: assocs_eqD[THEN associated_sym])
  qed
qed

lemma (in comm_monoid_cancel) ee_is_fmset:
  assumes "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "essentially_equal G as bs = (fmset G as = fmset G bs)"
  using assms by (fast intro: ee_fmset fmset_ee)


subsubsection \<open>Interpreting multisets as factorizations\<close>

lemma (in monoid) mset_fmsetEx:
  assumes elems: "\<And>X. X \<in> set_mset Cs \<Longrightarrow> \<exists>x. P x \<and> X = assocs G x"
  shows "\<exists>cs. (\<forall>c \<in> set cs. P c) \<and> fmset G cs = Cs"
proof -
  from surjE[OF surj_mset] obtain Cs' where Cs: "Cs = mset Cs'"
    by blast
  have "\<exists>cs. (\<forall>c \<in> set cs. P c) \<and> mset (map (assocs G) cs) = Cs"
    using elems unfolding Cs
  proof (induction Cs')
    case (Cons a Cs')
    then obtain c cs where csP: "\<forall>x\<in>set cs. P x" and mset: "mset (map (assocs G) cs) = mset Cs'"
            and cP: "P c" and a: "a = assocs G c"
      by force
    then have tP: "\<forall>x\<in>set (c#cs). P x"
      by simp
    show ?case
      using tP mset a by fastforce
  qed auto
  then show ?thesis by (simp add: fmset_def)
qed

lemma (in monoid) mset_wfactorsEx:
  assumes elems: "\<And>X. X \<in> set_mset Cs \<Longrightarrow> \<exists>x. (x \<in> carrier G \<and> irreducible G x) \<and> X = assocs G x"
  shows "\<exists>c cs. c \<in> carrier G \<and> set cs \<subseteq> carrier G \<and> wfactors G cs c \<and> fmset G cs = Cs"
proof -
  have "\<exists>cs. (\<forall>c\<in>set cs. c \<in> carrier G \<and> irreducible G c) \<and> fmset G cs = Cs"
    by (intro mset_fmsetEx, rule elems)
  then obtain cs where p[rule_format]: "\<forall>c\<in>set cs. c \<in> carrier G \<and> irreducible G c"
    and Cs[symmetric]: "fmset G cs = Cs" by auto
  from p have cscarr: "set cs \<subseteq> carrier G" by fast
  from p have "\<exists>c. c \<in> carrier G \<and> wfactors G cs c"
    by (intro wfactors_prod_exists) auto
  then obtain c where ccarr: "c \<in> carrier G" and cfs: "wfactors G cs c" by auto
  with cscarr Cs show ?thesis by fast
qed


subsubsection \<open>Multiplication on multisets\<close>

lemma (in factorial_monoid) mult_wfactors_fmset:
  assumes afs: "wfactors G as a"
    and bfs: "wfactors G bs b"
    and cfs: "wfactors G cs (a \<otimes> b)"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"
              "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"  "set cs \<subseteq> carrier G"
  shows "fmset G cs = fmset G as + fmset G bs"
proof -
  from assms have "wfactors G (as @ bs) (a \<otimes> b)"
    by (intro wfactors_mult)
  with carr cfs have "essentially_equal G cs (as@bs)"
    by (intro ee_wfactorsI[of "a\<otimes>b" "a\<otimes>b"]) simp_all
  with carr have "fmset G cs = fmset G (as@bs)"
    by (intro ee_fmset) simp_all
  also have "fmset G (as@bs) = fmset G as + fmset G bs"
    by (simp add: fmset_def)
  finally show "fmset G cs = fmset G as + fmset G bs" .
qed

lemma (in factorial_monoid) mult_factors_fmset:
  assumes afs: "factors G as a"
    and bfs: "factors G bs b"
    and cfs: "factors G cs (a \<otimes> b)"
    and "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"  "set cs \<subseteq> carrier G"
  shows "fmset G cs = fmset G as + fmset G bs"
  using assms by (blast intro: factors_wfactors mult_wfactors_fmset)

lemma (in comm_monoid_cancel) fmset_wfactors_mult:
  assumes mset: "fmset G cs = fmset G as + fmset G bs"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
      "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"  "set cs \<subseteq> carrier G"
    and fs: "wfactors G as a"  "wfactors G bs b"  "wfactors G cs c"
  shows "c \<sim> a \<otimes> b"
proof -
  from carr fs have m: "wfactors G (as @ bs) (a \<otimes> b)"
    by (intro wfactors_mult)

  from mset have "fmset G cs = fmset G (as@bs)"
    by (simp add: fmset_def)
  then have "essentially_equal G cs (as@bs)"
    by (rule fmset_ee) (simp_all add: carr)
  then show "c \<sim> a \<otimes> b"
    by (rule ee_wfactorsD[of "cs" "as@bs"]) (simp_all add: assms m)
qed


subsubsection \<open>Divisibility on multisets\<close>

lemma (in factorial_monoid) divides_fmsubset:
  assumes ab: "a divides b"
    and afs: "wfactors G as a"
    and bfs: "wfactors G bs b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"
  shows "fmset G as \<subseteq># fmset G bs"
  using ab
proof (elim dividesE)
  fix c
  assume ccarr: "c \<in> carrier G"
  from wfactors_exist [OF this]
  obtain cs where cscarr: "set cs \<subseteq> carrier G" and cfs: "wfactors G cs c"
    by blast
  note carr = carr ccarr cscarr

  assume "b = a \<otimes> c"
  with afs bfs cfs carr have "fmset G bs = fmset G as + fmset G cs"
    by (intro mult_wfactors_fmset[OF afs cfs]) simp_all
  then show ?thesis by simp
qed

lemma (in comm_monoid_cancel) fmsubset_divides:
  assumes msubset: "fmset G as \<subseteq># fmset G bs"
    and afs: "wfactors G as a"
    and bfs: "wfactors G bs b"
    and acarr: "a \<in> carrier G"
    and bcarr: "b \<in> carrier G"
    and ascarr: "set as \<subseteq> carrier G"
    and bscarr: "set bs \<subseteq> carrier G"
  shows "a divides b"
proof -
  from afs have airr: "\<forall>a \<in> set as. irreducible G a" by (fast elim: wfactorsE)
  from bfs have birr: "\<forall>b \<in> set bs. irreducible G b" by (fast elim: wfactorsE)

  have "\<exists>c cs. c \<in> carrier G \<and> set cs \<subseteq> carrier G \<and> wfactors G cs c \<and> fmset G cs = fmset G bs - fmset G as"
  proof (intro mset_wfactorsEx, simp)
    fix X
    assume "X \<in># fmset G bs - fmset G as"
    then have "X \<in># fmset G bs" by (rule in_diffD)
    then have "X \<in> set (map (assocs G) bs)" by (simp add: fmset_def)
    then have "\<exists>x. x \<in> set bs \<and> X = assocs G x" by (induct bs) auto
    then obtain x where xbs: "x \<in> set bs" and X: "X = assocs G x" by auto
    with bscarr have xcarr: "x \<in> carrier G" by fast
    from xbs birr have xirr: "irreducible G x" by simp

    from xcarr and xirr and X show "\<exists>x. x \<in> carrier G \<and> irreducible G x \<and> X = assocs G x"
      by fast
  qed
  then obtain c cs
    where ccarr: "c \<in> carrier G"
      and cscarr: "set cs \<subseteq> carrier G"
      and csf: "wfactors G cs c"
      and csmset: "fmset G cs = fmset G bs - fmset G as" by auto

  from csmset msubset
  have "fmset G bs = fmset G as + fmset G cs"
    by (simp add: multiset_eq_iff subseteq_mset_def)
  then have basc: "b \<sim> a \<otimes> c"
    by (rule fmset_wfactors_mult) fact+
  then show ?thesis
  proof (elim associatedE2)
    fix u
    assume "u \<in> Units G"  "b = a \<otimes> c \<otimes> u"
    with acarr ccarr show "a divides b"
      by (fast intro: dividesI[of "c \<otimes> u"] m_assoc)
  qed (simp_all add: acarr bcarr ccarr)
qed

lemma (in factorial_monoid) divides_as_fmsubset:
  assumes "wfactors G as a"
    and "wfactors G bs b"
    and "a \<in> carrier G"
    and "b \<in> carrier G"
    and "set as \<subseteq> carrier G"
    and "set bs \<subseteq> carrier G"
  shows "a divides b = (fmset G as \<subseteq># fmset G bs)"
  using assms
  by (blast intro: divides_fmsubset fmsubset_divides)


text \<open>Proper factors on multisets\<close>

lemma (in factorial_monoid) fmset_properfactor:
  assumes asubb: "fmset G as \<subseteq># fmset G bs"
    and anb: "fmset G as \<noteq> fmset G bs"
    and "wfactors G as a"
    and "wfactors G bs b"
    and "a \<in> carrier G"
    and "b \<in> carrier G"
    and "set as \<subseteq> carrier G"
    and "set bs \<subseteq> carrier G"
  shows "properfactor G a b"
proof (rule properfactorI)
  show "a divides b"
    using assms asubb fmsubset_divides by blast
  show "\<not> b divides a"
    by (meson anb assms asubb factorial_monoid.divides_fmsubset factorial_monoid_axioms subset_mset.antisym)
qed

lemma (in factorial_monoid) properfactor_fmset:
  assumes "properfactor G a b"
    and "wfactors G as a"
    and "wfactors G bs b"
    and "a \<in> carrier G"
    and "b \<in> carrier G"
    and "set as \<subseteq> carrier G"
    and "set bs \<subseteq> carrier G"
  shows "fmset G as \<subseteq># fmset G bs"
  using assms
  by (meson divides_as_fmsubset properfactor_divides)

lemma (in factorial_monoid) properfactor_fmset_ne:
  assumes pf: "properfactor G a b"
    and "wfactors G as a"
    and "wfactors G bs b"
    and "a \<in> carrier G"
    and "b \<in> carrier G"
    and "set as \<subseteq> carrier G"
    and "set bs \<subseteq> carrier G"
  shows "fmset G as \<noteq> fmset G bs"
  using properfactorE [OF pf] assms divides_as_fmsubset by force

subsection \<open>Irreducible Elements are Prime\<close>

lemma (in factorial_monoid) irreducible_prime:
  assumes pirr: "irreducible G p" and pcarr: "p \<in> carrier G"
  shows "prime G p"
  using pirr
proof (elim irreducibleE, intro primeI)
  fix a b
  assume acarr: "a \<in> carrier G"  and bcarr: "b \<in> carrier G"
    and pdvdab: "p divides (a \<otimes> b)"
    and pnunit: "p \<notin> Units G"
  assume irreduc[rule_format]:
    "\<forall>b. b \<in> carrier G \<and> properfactor G b p \<longrightarrow> b \<in> Units G"
  from pdvdab obtain c where ccarr: "c \<in> carrier G" and abpc: "a \<otimes> b = p \<otimes> c"
    by (rule dividesE)
  obtain as where ascarr: "set as \<subseteq> carrier G" and afs: "wfactors G as a"
    using wfactors_exist [OF acarr] by blast
  obtain bs where bscarr: "set bs \<subseteq> carrier G" and bfs: "wfactors G bs b"
    using wfactors_exist [OF bcarr] by blast
  obtain cs where cscarr: "set cs \<subseteq> carrier G" and cfs: "wfactors G cs c"
    using wfactors_exist [OF ccarr] by blast
  note carr[simp] = pcarr acarr bcarr ccarr ascarr bscarr cscarr
  from pirr cfs  abpc have "wfactors G (p # cs) (a \<otimes> b)"
    by (simp add: wfactors_mult_single)
  moreover have  "wfactors G (as @ bs) (a \<otimes> b)"
    by (rule wfactors_mult [OF afs bfs]) fact+
  ultimately have "essentially_equal G (p # cs) (as @ bs)"
    by (rule wfactors_unique) simp+
  then obtain ds where "p # cs <~~> ds" and dsassoc: "ds [\<sim>] (as @ bs)"
    by (fast elim: essentially_equalE)
  then have "p \<in> set ds"
    by (metis \<open>mset (p # cs) = mset ds\<close> insert_iff list.set(2) perm_set_eq) 
  with dsassoc obtain p' where "p' \<in> set (as@bs)" and pp': "p \<sim> p'"
    unfolding list_all2_conv_all_nth set_conv_nth by force
  then consider "p' \<in> set as" | "p' \<in> set bs" by auto
  then show "p divides a \<or> p divides b"
    using afs bfs divides_cong_l pp' wfactors_dividesI
    by (meson acarr ascarr bcarr bscarr pcarr)
qed


\<comment> \<open>A version using \<^const>\<open>factors\<close>, more complicated\<close>
lemma (in factorial_monoid) factors_irreducible_prime:
  assumes pirr: "irreducible G p" and pcarr: "p \<in> carrier G"
  shows "prime G p"
proof (rule primeI)
  show "p \<notin> Units G"
    by (meson irreducibleE pirr)
  have irreduc: "\<And>b. \<lbrakk>b \<in> carrier G; properfactor G b p\<rbrakk> \<Longrightarrow> b \<in> Units G"
    using pirr by (auto simp: irreducible_def)
  show "p divides a \<or> p divides b" 
    if acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G" and pdvdab: "p divides (a \<otimes> b)" for a b
  proof -
    from pdvdab obtain c where ccarr: "c \<in> carrier G" and abpc: "a \<otimes> b = p \<otimes> c"
      by (rule dividesE)
    note [simp] = pcarr acarr bcarr ccarr

    show "p divides a \<or> p divides b"
    proof (cases "a \<in> Units G")
      case True
      then have "p divides b"
        by (metis acarr associatedI2' associated_def bcarr divides_trans m_comm pcarr pdvdab) 
      then show ?thesis ..
    next
      case anunit: False
      show ?thesis
      proof (cases "b \<in> Units G")
        case True 
        then have "p divides a"
          by (meson acarr bcarr divides_unit irreducible_prime pcarr pdvdab pirr prime_def)
        then show ?thesis ..
      next
        case bnunit: False
        then have cnunit: "c \<notin> Units G"
          by (metis abpc acarr anunit bcarr ccarr irreducible_prodE irreducible_prod_rI pcarr pirr)
        then have abnunit: "a \<otimes> b \<notin> Units G"
          using acarr anunit bcarr unit_factor by blast
        obtain as where ascarr: "set as \<subseteq> carrier G" and afac: "factors G as a"
          using factors_exist [OF acarr anunit] by blast
        obtain bs where bscarr: "set bs \<subseteq> carrier G" and bfac: "factors G bs b"
          using factors_exist [OF bcarr bnunit] by blast
        obtain cs where cscarr: "set cs \<subseteq> carrier G" and cfac: "factors G cs c"
          using factors_exist [OF ccarr cnunit] by auto
        note [simp] = ascarr bscarr cscarr
        from pirr cfac abpc have abfac': "factors G (p # cs) (a \<otimes> b)"
          by (simp add: factors_mult_single)
        from afac and bfac have "factors G (as @ bs) (a \<otimes> b)"
          by (rule factors_mult) fact+
        with abfac' have "essentially_equal G (p # cs) (as @ bs)"
          using abnunit factors_unique by auto
        then obtain ds where "p # cs <~~> ds" and dsassoc: "ds [\<sim>] (as @ bs)"
          by (fast elim: essentially_equalE)
        then have "p \<in> set ds"
          by (metis list.set_intros(1) set_mset_mset)
        with dsassoc obtain p' where "p' \<in> set (as@bs)" and pp': "p \<sim> p'"
          unfolding list_all2_conv_all_nth set_conv_nth by force
        then consider "p' \<in> set as" | "p' \<in> set bs" by auto
        then show "p divides a \<or> p divides b"
          by (meson afac bfac divides_cong_l factors_dividesI pp' ascarr bscarr pcarr)
      qed
    qed
  qed
qed


subsection \<open>Greatest Common Divisors and Lowest Common Multiples\<close>

subsubsection \<open>Definitions\<close>

definition isgcd :: "[('a,_) monoid_scheme, 'a, 'a, 'a] \<Rightarrow> bool"  ("(_ gcdof\<index> _ _)" [81,81,81] 80)
  where "x gcdof\<^bsub>G\<^esub> a b \<longleftrightarrow> x divides\<^bsub>G\<^esub> a \<and> x divides\<^bsub>G\<^esub> b \<and>
    (\<forall>y\<in>carrier G. (y divides\<^bsub>G\<^esub> a \<and> y divides\<^bsub>G\<^esub> b \<longrightarrow> y divides\<^bsub>G\<^esub> x))"

definition islcm :: "[_, 'a, 'a, 'a] \<Rightarrow> bool"  ("(_ lcmof\<index> _ _)" [81,81,81] 80)
  where "x lcmof\<^bsub>G\<^esub> a b \<longleftrightarrow> a divides\<^bsub>G\<^esub> x \<and> b divides\<^bsub>G\<^esub> x \<and>
    (\<forall>y\<in>carrier G. (a divides\<^bsub>G\<^esub> y \<and> b divides\<^bsub>G\<^esub> y \<longrightarrow> x divides\<^bsub>G\<^esub> y))"

definition somegcd :: "('a,_) monoid_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "somegcd G a b = (SOME x. x \<in> carrier G \<and> x gcdof\<^bsub>G\<^esub> a b)"

definition somelcm :: "('a,_) monoid_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "somelcm G a b = (SOME x. x \<in> carrier G \<and> x lcmof\<^bsub>G\<^esub> a b)"

definition "SomeGcd G A = Lattice.inf (division_rel G) A"


locale gcd_condition_monoid = comm_monoid_cancel +
  assumes gcdof_exists: "\<lbrakk>a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> \<exists>c. c \<in> carrier G \<and> c gcdof a b"

locale primeness_condition_monoid = comm_monoid_cancel +
  assumes irreducible_prime: "\<lbrakk>a \<in> carrier G; irreducible G a\<rbrakk> \<Longrightarrow> prime G a"

locale divisor_chain_condition_monoid = comm_monoid_cancel +
  assumes division_wellfounded: "wf {(x, y). x \<in> carrier G \<and> y \<in> carrier G \<and> properfactor G x y}"


subsubsection \<open>Connections to \texttt{Lattice.thy}\<close>

lemma gcdof_greatestLower:
  fixes G (structure)
  assumes carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "(x \<in> carrier G \<and> x gcdof a b) = greatest (division_rel G) x (Lower (division_rel G) {a, b})"
  by (auto simp: isgcd_def greatest_def Lower_def elem_def)

lemma lcmof_leastUpper:
  fixes G (structure)
  assumes carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "(x \<in> carrier G \<and> x lcmof a b) = least (division_rel G) x (Upper (division_rel G) {a, b})"
  by (auto simp: islcm_def least_def Upper_def elem_def)

lemma somegcd_meet:
  fixes G (structure)
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "somegcd G a b = meet (division_rel G) a b"
  by (simp add: somegcd_def meet_def inf_def gcdof_greatestLower[OF carr])

lemma (in monoid) isgcd_divides_l:
  assumes "a divides b"
    and "a \<in> carrier G"  "b \<in> carrier G"
  shows "a gcdof a b"
  using assms unfolding isgcd_def by fast

lemma (in monoid) isgcd_divides_r:
  assumes "b divides a"
    and "a \<in> carrier G"  "b \<in> carrier G"
  shows "b gcdof a b"
  using assms unfolding isgcd_def by fast


subsubsection \<open>Existence of gcd and lcm\<close>

lemma (in factorial_monoid) gcdof_exists:
  assumes acarr: "a \<in> carrier G"
    and bcarr: "b \<in> carrier G"
  shows "\<exists>c. c \<in> carrier G \<and> c gcdof a b"
proof -
  from wfactors_exist [OF acarr]
  obtain as where ascarr: "set as \<subseteq> carrier G" and afs: "wfactors G as a"
    by blast
  from afs have airr: "\<forall>a \<in> set as. irreducible G a"
    by (fast elim: wfactorsE)

  from wfactors_exist [OF bcarr]
  obtain bs where bscarr: "set bs \<subseteq> carrier G" and bfs: "wfactors G bs b"
    by blast
  from bfs have birr: "\<forall>b \<in> set bs. irreducible G b"
    by (fast elim: wfactorsE)

  have "\<exists>c cs. c \<in> carrier G \<and> set cs \<subseteq> carrier G \<and> wfactors G cs c \<and>
    fmset G cs = fmset G as \<inter># fmset G bs"
  proof (intro mset_wfactorsEx)
    fix X
    assume "X \<in># fmset G as \<inter># fmset G bs"
    then have "X \<in># fmset G as" by simp
    then have "X \<in> set (map (assocs G) as)"
      by (simp add: fmset_def)
    then have "\<exists>x. X = assocs G x \<and> x \<in> set as"
      by (induct as) auto
    then obtain x where X: "X = assocs G x" and xas: "x \<in> set as"
      by blast
    with ascarr have xcarr: "x \<in> carrier G"
      by blast
    from xas airr have xirr: "irreducible G x"
      by simp
    from xcarr and xirr and X show "\<exists>x. (x \<in> carrier G \<and> irreducible G x) \<and> X = assocs G x"
      by blast
  qed
  then obtain c cs
    where ccarr: "c \<in> carrier G"
      and cscarr: "set cs \<subseteq> carrier G"
      and csirr: "wfactors G cs c"
      and csmset: "fmset G cs = fmset G as \<inter># fmset G bs"
    by auto

  have "c gcdof a b"
  proof (simp add: isgcd_def, safe)
    from csmset
    have "fmset G cs \<subseteq># fmset G as"
      by simp
    then show "c divides a" by (rule fmsubset_divides) fact+
  next
    from csmset have "fmset G cs \<subseteq># fmset G bs"
      by simp
    then show "c divides b"
      by (rule fmsubset_divides) fact+
  next
    fix y
    assume "y \<in> carrier G"
    from wfactors_exist [OF this]
    obtain ys where yscarr: "set ys \<subseteq> carrier G" and yfs: "wfactors G ys y"
      by blast

    assume "y divides a"
    then have ya: "fmset G ys \<subseteq># fmset G as"
      by (rule divides_fmsubset) fact+

    assume "y divides b"
    then have yb: "fmset G ys \<subseteq># fmset G bs"
      by (rule divides_fmsubset) fact+

    from ya yb csmset have "fmset G ys \<subseteq># fmset G cs"
      by (simp add: subset_mset_def)
    then show "y divides c"
      by (rule fmsubset_divides) fact+
  qed
  with ccarr show "\<exists>c. c \<in> carrier G \<and> c gcdof a b"
    by fast
qed

lemma (in factorial_monoid) lcmof_exists:
  assumes acarr: "a \<in> carrier G"
    and bcarr: "b \<in> carrier G"
  shows "\<exists>c. c \<in> carrier G \<and> c lcmof a b"
proof -
  from wfactors_exist [OF acarr]
  obtain as where ascarr: "set as \<subseteq> carrier G" and afs: "wfactors G as a"
    by blast
  from afs have airr: "\<forall>a \<in> set as. irreducible G a"
    by (fast elim: wfactorsE)

  from wfactors_exist [OF bcarr]
  obtain bs where bscarr: "set bs \<subseteq> carrier G" and bfs: "wfactors G bs b"
    by blast
  from bfs have birr: "\<forall>b \<in> set bs. irreducible G b"
    by (fast elim: wfactorsE)

  have "\<exists>c cs. c \<in> carrier G \<and> set cs \<subseteq> carrier G \<and> wfactors G cs c \<and>
    fmset G cs = (fmset G as - fmset G bs) + fmset G bs"
  proof (intro mset_wfactorsEx)
    fix X
    assume "X \<in># (fmset G as - fmset G bs) + fmset G bs"
    then have "X \<in># fmset G as \<or> X \<in># fmset G bs"
      by (auto dest: in_diffD)
    then consider "X \<in> set_mset (fmset G as)" | "X \<in> set_mset (fmset G bs)"
      by fast
    then show "\<exists>x. (x \<in> carrier G \<and> irreducible G x) \<and> X = assocs G x"
    proof cases
      case 1
      then have "X \<in> set (map (assocs G) as)" by (simp add: fmset_def)
      then have "\<exists>x. x \<in> set as \<and> X = assocs G x" by (induct as) auto
      then obtain x where xas: "x \<in> set as" and X: "X = assocs G x" by auto
      with ascarr have xcarr: "x \<in> carrier G" by fast
      from xas airr have xirr: "irreducible G x" by simp
      from xcarr and xirr and X show ?thesis by fast
    next
      case 2
      then have "X \<in> set (map (assocs G) bs)" by (simp add: fmset_def)
      then have "\<exists>x. x \<in> set bs \<and> X = assocs G x" by (induct as) auto
      then obtain x where xbs: "x \<in> set bs" and X: "X = assocs G x" by auto
      with bscarr have xcarr: "x \<in> carrier G" by fast
      from xbs birr have xirr: "irreducible G x" by simp
      from xcarr and xirr and X show ?thesis by fast
    qed
  qed
  then obtain c cs
    where ccarr: "c \<in> carrier G"
      and cscarr: "set cs \<subseteq> carrier G"
      and csirr: "wfactors G cs c"
      and csmset: "fmset G cs = fmset G as - fmset G bs + fmset G bs"
    by auto

  have "c lcmof a b"
  proof (simp add: islcm_def, safe)
    from csmset have "fmset G as \<subseteq># fmset G cs"
      by (simp add: subseteq_mset_def, force)
    then show "a divides c"
      by (rule fmsubset_divides) fact+
  next
    from csmset have "fmset G bs \<subseteq># fmset G cs"
      by (simp add: subset_mset_def)
    then show "b divides c"
      by (rule fmsubset_divides) fact+
  next
    fix y
    assume "y \<in> carrier G"
    from wfactors_exist [OF this]
    obtain ys where yscarr: "set ys \<subseteq> carrier G" and yfs: "wfactors G ys y"
      by blast

    assume "a divides y"
    then have ya: "fmset G as \<subseteq># fmset G ys"
      by (rule divides_fmsubset) fact+

    assume "b divides y"
    then have yb: "fmset G bs \<subseteq># fmset G ys"
      by (rule divides_fmsubset) fact+

    from ya yb csmset have "fmset G cs \<subseteq># fmset G ys"
      using subset_eq_diff_conv subset_mset.le_diff_conv2 by fastforce
    then show "c divides y"
      by (rule fmsubset_divides) fact+
  qed
  with ccarr show "\<exists>c. c \<in> carrier G \<and> c lcmof a b"
    by fast
qed


subsection \<open>Conditions for Factoriality\<close>

subsubsection \<open>Gcd condition\<close>

lemma (in gcd_condition_monoid) division_weak_lower_semilattice [simp]:
  "weak_lower_semilattice (division_rel G)"
proof -
  interpret weak_partial_order "division_rel G" ..
  show ?thesis
  proof (unfold_locales, simp_all)
    fix x y
    assume carr: "x \<in> carrier G"  "y \<in> carrier G"
    from gcdof_exists [OF this] obtain z where zcarr: "z \<in> carrier G" and isgcd: "z gcdof x y"
      by blast
    with carr have "greatest (division_rel G) z (Lower (division_rel G) {x, y})"
      by (subst gcdof_greatestLower[symmetric], simp+)
    then show "\<exists>z. greatest (division_rel G) z (Lower (division_rel G) {x, y})"
      by fast
  qed
qed

lemma (in gcd_condition_monoid) gcdof_cong_l:
  assumes "a' \<sim> a" "a gcdof b c" "a' \<in> carrier G" and carr': "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "a' gcdof b c"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  have "is_glb (division_rel G) a' {b, c}"
    by (subst greatest_Lower_cong_l[of _ a]) (simp_all add: assms gcdof_greatestLower[symmetric])
  then have "a' \<in> carrier G \<and> a' gcdof b c"
    by (simp add: gcdof_greatestLower carr')
  then show ?thesis ..
qed

lemma (in gcd_condition_monoid) gcd_closed [simp]:
  assumes "a \<in> carrier G" "b \<in> carrier G"
  shows "somegcd G a b \<in> carrier G"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
  using  assms meet_closed by (simp add: somegcd_meet)
qed

lemma (in gcd_condition_monoid) gcd_isgcd:
  assumes "a \<in> carrier G"  "b \<in> carrier G"
  shows "(somegcd G a b) gcdof a b"
proof -
  interpret weak_lower_semilattice "division_rel G"
    by simp
  from assms have "somegcd G a b \<in> carrier G \<and> (somegcd G a b) gcdof a b"
    by (simp add: gcdof_greatestLower inf_of_two_greatest meet_def somegcd_meet)
  then show "(somegcd G a b) gcdof a b"
    by simp
qed

lemma (in gcd_condition_monoid) gcd_exists:
  assumes "a \<in> carrier G"  "b \<in> carrier G"
  shows "\<exists>x\<in>carrier G. x = somegcd G a b"
proof -
  interpret weak_lower_semilattice "division_rel G"
    by simp
  show ?thesis
    by (metis assms gcd_closed)
qed

lemma (in gcd_condition_monoid) gcd_divides_l:
  assumes "a \<in> carrier G" "b \<in> carrier G"
  shows "(somegcd G a b) divides a"
proof -
  interpret weak_lower_semilattice "division_rel G"
    by simp
  show ?thesis
    by (metis assms gcd_isgcd isgcd_def)
qed

lemma (in gcd_condition_monoid) gcd_divides_r:
  assumes "a \<in> carrier G"  "b \<in> carrier G"
  shows "(somegcd G a b) divides b"
proof -
  interpret weak_lower_semilattice "division_rel G"
    by simp
  show ?thesis
    by (metis assms gcd_isgcd isgcd_def)
qed

lemma (in gcd_condition_monoid) gcd_divides:
  assumes "z divides x" "z divides y"
    and L: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
  shows "z divides (somegcd G x y)"
proof -
  interpret weak_lower_semilattice "division_rel G"
    by simp
  show ?thesis
    by (metis gcd_isgcd isgcd_def assms)
qed

lemma (in gcd_condition_monoid) gcd_cong_l:
  assumes "x \<sim> x'" "x \<in> carrier G"  "x' \<in> carrier G"  "y \<in> carrier G"
  shows "somegcd G x y \<sim> somegcd G x' y"
proof -
  interpret weak_lower_semilattice "division_rel G"
    by simp
  show ?thesis
    using somegcd_meet assms
    by (metis eq_object.select_convs(1) meet_cong_l partial_object.select_convs(1))
qed

lemma (in gcd_condition_monoid) gcd_cong_r:
  assumes "y \<sim> y'" "x \<in> carrier G"  "y \<in> carrier G" "y' \<in> carrier G"
  shows "somegcd G x y \<sim> somegcd G x y'"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
    by (meson associated_def assms gcd_closed gcd_divides gcd_divides_l gcd_divides_r monoid.divides_trans monoid_axioms)
qed

lemma (in gcd_condition_monoid) gcdI:
  assumes dvd: "a divides b"  "a divides c"
    and others: "\<And>y. \<lbrakk>y\<in>carrier G; y divides b; y divides c\<rbrakk> \<Longrightarrow> y divides a"
    and acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G" and ccarr: "c \<in> carrier G"
  shows "a \<sim> somegcd G b c"
proof -
  have "\<exists>a. a \<in> carrier G \<and> a gcdof b c"
    by (simp add: bcarr ccarr gcdof_exists)
  moreover have "\<And>x. x \<in> carrier G \<and> x gcdof b c \<Longrightarrow> a \<sim> x"
    by (simp add: acarr associated_def dvd isgcd_def others)
  ultimately show ?thesis
    unfolding somegcd_def by (blast intro: someI2_ex)
qed

lemma (in gcd_condition_monoid) gcdI2:
  assumes "a gcdof b c" and "a \<in> carrier G" and "b \<in> carrier G" and "c \<in> carrier G"
  shows "a \<sim> somegcd G b c"
  using assms unfolding isgcd_def
  by (simp add: gcdI)

lemma (in gcd_condition_monoid) SomeGcd_ex:
  assumes "finite A"  "A \<subseteq> carrier G"  "A \<noteq> {}"
  shows "\<exists>x \<in> carrier G. x = SomeGcd G A"
proof -
  interpret weak_lower_semilattice "division_rel G"
    by simp
  show ?thesis
    using finite_inf_closed by (simp add: assms SomeGcd_def)
qed

lemma (in gcd_condition_monoid) gcd_assoc:
  assumes "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "somegcd G (somegcd G a b) c \<sim> somegcd G a (somegcd G b c)"
proof -
  interpret weak_lower_semilattice "division_rel G"
    by simp
  show ?thesis
    unfolding associated_def
    by (meson assms divides_trans gcd_divides gcd_divides_l gcd_divides_r gcd_exists)
qed

lemma (in gcd_condition_monoid) gcd_mult:
  assumes acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G" and ccarr: "c \<in> carrier G"
  shows "c \<otimes> somegcd G a b \<sim> somegcd G (c \<otimes> a) (c \<otimes> b)"
proof - (* following Jacobson, Basic Algebra, p.140 *)
  let ?d = "somegcd G a b"
  let ?e = "somegcd G (c \<otimes> a) (c \<otimes> b)"
  note carr[simp] = acarr bcarr ccarr
  have dcarr: "?d \<in> carrier G" by simp
  have ecarr: "?e \<in> carrier G" by simp
  note carr = carr dcarr ecarr

  have "?d divides a" by (simp add: gcd_divides_l)
  then have cd'ca: "c \<otimes> ?d divides (c \<otimes> a)" by (simp add: divides_mult_lI)

  have "?d divides b" by (simp add: gcd_divides_r)
  then have cd'cb: "c \<otimes> ?d divides (c \<otimes> b)" by (simp add: divides_mult_lI)

  from cd'ca cd'cb have cd'e: "c \<otimes> ?d divides ?e"
    by (rule gcd_divides) simp_all
  then obtain u where ucarr[simp]: "u \<in> carrier G" and e_cdu: "?e = c \<otimes> ?d \<otimes> u"
    by blast

  note carr = carr ucarr

  have "?e divides c \<otimes> a" by (rule gcd_divides_l) simp_all
  then obtain x where xcarr: "x \<in> carrier G" and ca_ex: "c \<otimes> a = ?e \<otimes> x"
    by blast
  with e_cdu have ca_cdux: "c \<otimes> a = c \<otimes> ?d \<otimes> u \<otimes> x"
    by simp

  from ca_cdux xcarr have "c \<otimes> a = c \<otimes> (?d \<otimes> u \<otimes> x)"
    by (simp add: m_assoc)
  then have "a = ?d \<otimes> u \<otimes> x"
    by (rule l_cancel[of c a]) (simp add: xcarr)+
  then have du'a: "?d \<otimes> u divides a"
    by (rule dividesI[OF xcarr])

  have "?e divides c \<otimes> b" by (intro gcd_divides_r) simp_all
  then obtain x where xcarr: "x \<in> carrier G" and cb_ex: "c \<otimes> b = ?e \<otimes> x"
    by blast
  with e_cdu have cb_cdux: "c \<otimes> b = c \<otimes> ?d \<otimes> u \<otimes> x"
    by simp

  from cb_cdux xcarr have "c \<otimes> b = c \<otimes> (?d \<otimes> u \<otimes> x)"
    by (simp add: m_assoc)
  with xcarr have "b = ?d \<otimes> u \<otimes> x"
    by (intro l_cancel[of c b]) simp_all
  then have du'b: "?d \<otimes> u divides b"
    by (intro dividesI[OF xcarr])

  from du'a du'b carr have du'd: "?d \<otimes> u divides ?d"
    by (intro gcd_divides) simp_all
  then have uunit: "u \<in> Units G"
  proof (elim dividesE)
    fix v
    assume vcarr[simp]: "v \<in> carrier G"
    assume d: "?d = ?d \<otimes> u \<otimes> v"
    have "?d \<otimes> \<one> = ?d \<otimes> u \<otimes> v" by simp fact
    also have "?d \<otimes> u \<otimes> v = ?d \<otimes> (u \<otimes> v)" by (simp add: m_assoc)
    finally have "?d \<otimes> \<one> = ?d \<otimes> (u \<otimes> v)" .
    then have i2: "\<one> = u \<otimes> v" by (rule l_cancel) simp_all
    then have i1: "\<one> = v \<otimes> u" by (simp add: m_comm)
    from vcarr i1[symmetric] i2[symmetric] show "u \<in> Units G"
      by (auto simp: Units_def)
  qed

  from e_cdu uunit have "somegcd G (c \<otimes> a) (c \<otimes> b) \<sim> c \<otimes> somegcd G a b"
    by (intro associatedI2[of u]) simp_all
  from this[symmetric] show "c \<otimes> somegcd G a b \<sim> somegcd G (c \<otimes> a) (c \<otimes> b)"
    by simp
qed

lemma (in monoid) assoc_subst:
  assumes ab: "a \<sim> b"
    and cP: "\<forall>a b. a \<in> carrier G \<and> b \<in> carrier G \<and> a \<sim> b
      \<longrightarrow> f a \<in> carrier G \<and> f b \<in> carrier G \<and> f a \<sim> f b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "f a \<sim> f b"
  using assms by auto

lemma (in gcd_condition_monoid) relprime_mult:
  assumes abrelprime: "somegcd G a b \<sim> \<one>"
    and acrelprime: "somegcd G a c \<sim> \<one>"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "somegcd G a (b \<otimes> c) \<sim> \<one>"
proof -
  have "c = c \<otimes> \<one>" by simp
  also from abrelprime[symmetric]
  have "\<dots> \<sim> c \<otimes> somegcd G a b"
    by (rule assoc_subst) (simp add: mult_cong_r)+
  also have "\<dots> \<sim> somegcd G (c \<otimes> a) (c \<otimes> b)"
    by (rule gcd_mult) fact+
  finally have c: "c \<sim> somegcd G (c \<otimes> a) (c \<otimes> b)"
    by simp

  from carr have a: "a \<sim> somegcd G a (c \<otimes> a)"
    by (fast intro: gcdI divides_prod_l)

  have "somegcd G a (b \<otimes> c) \<sim> somegcd G a (c \<otimes> b)"
    by (simp add: m_comm)
  also from a have "\<dots> \<sim> somegcd G (somegcd G a (c \<otimes> a)) (c \<otimes> b)"
    by (rule assoc_subst) (simp add: gcd_cong_l)+
  also from gcd_assoc have "\<dots> \<sim> somegcd G a (somegcd G (c \<otimes> a) (c \<otimes> b))"
    by (rule assoc_subst) simp+
  also from c[symmetric] have "\<dots> \<sim> somegcd G a c"
    by (rule assoc_subst) (simp add: gcd_cong_r)+
  also note acrelprime
  finally show "somegcd G a (b \<otimes> c) \<sim> \<one>"
    by simp
qed

lemma (in gcd_condition_monoid) primeness_condition: "primeness_condition_monoid G"
proof -
  have *: "p divides a \<or> p divides b"
    if pcarr[simp]: "p \<in> carrier G" and acarr[simp]: "a \<in> carrier G" and bcarr[simp]: "b \<in> carrier G"
      and pirr: "irreducible G p" and pdvdab: "p divides a \<otimes> b"
    for p a b
  proof -
    from pirr have pnunit: "p \<notin> Units G"
      and r: "\<And>b. \<lbrakk>b \<in> carrier G; properfactor G b p\<rbrakk> \<Longrightarrow> b \<in> Units G"
      by (fast elim: irreducibleE)+
    show "p divides a \<or> p divides b"
    proof (rule ccontr, clarsimp)
      assume npdvda: "\<not> p divides a" and npdvdb: "\<not> p divides b"
      have "\<one> \<sim> somegcd G p a"
      proof (intro gcdI unit_divides)
        show "\<And>y. \<lbrakk>y \<in> carrier G; y divides p; y divides a\<rbrakk> \<Longrightarrow> y \<in> Units G"
          by (meson divides_trans npdvda pcarr properfactorI r)
      qed auto
      with pcarr acarr have pa: "somegcd G p a \<sim> \<one>"
        by (fast intro: associated_sym[of "\<one>"] gcd_closed)
      have "\<one> \<sim> somegcd G p b"
      proof (intro gcdI unit_divides)
        show "\<And>y. \<lbrakk>y \<in> carrier G; y divides p; y divides b\<rbrakk> \<Longrightarrow> y \<in> Units G"
          by (meson divides_trans npdvdb pcarr properfactorI r)
      qed auto
      with pcarr bcarr have pb: "somegcd G p b \<sim> \<one>"
        by (fast intro: associated_sym[of "\<one>"] gcd_closed)
      have "p \<sim> somegcd G p (a \<otimes> b)"
        using pdvdab by (simp add: gcdI2 isgcd_divides_l)
      also from pa pb pcarr acarr bcarr have "somegcd G p (a \<otimes> b) \<sim> \<one>"
        by (rule relprime_mult)
      finally have "p \<sim> \<one>"
        by simp
      with pcarr have "p \<in> Units G"
        by (fast intro: assoc_unit_l)
      with pnunit show False ..
    qed
  qed
  show ?thesis
    by unfold_locales (metis * primeI irreducibleE)
qed    


sublocale gcd_condition_monoid \<subseteq> primeness_condition_monoid
  by (rule primeness_condition)


subsubsection \<open>Divisor chain condition\<close>

lemma (in divisor_chain_condition_monoid) wfactors_exist:
  assumes acarr: "a \<in> carrier G"
  shows "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a"
proof -
  have r: "a \<in> carrier G \<Longrightarrow> (\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a)"
    using division_wellfounded
  proof (induction rule: wf_induct_rule)
    case (less x)
    then have xcarr: "x \<in> carrier G"
      by auto
    show ?case
    proof (cases "x \<in> Units G")
      case True
      then show ?thesis
        by (metis bot.extremum list.set(1) unit_wfactors)
    next
      case xnunit: False
      show ?thesis
      proof (cases "irreducible G x")
        case True
        then show ?thesis
          by (rule_tac x="[x]" in exI) (simp add: wfactors_def xcarr)
      next
        case False
        then obtain y where ycarr: "y \<in> carrier G" and ynunit: "y \<notin> Units G" and pfyx: "properfactor G y x"
          by (meson irreducible_def xnunit)
        obtain ys where yscarr: "set ys \<subseteq> carrier G" and yfs: "wfactors G ys y"
          using less ycarr pfyx by blast
        then obtain z where zcarr: "z \<in> carrier G" and x: "x = y \<otimes> z"
          by (meson dividesE pfyx properfactorE2)
        from zcarr ycarr have "properfactor G z x"
          using m_comm properfactorI3 x ynunit by blast
        with less zcarr obtain zs where zscarr: "set zs \<subseteq> carrier G" and zfs: "wfactors G zs z"
          by blast
        from yscarr zscarr have xscarr: "set (ys@zs) \<subseteq> carrier G"
          by simp
        have "wfactors G (ys@zs) (y\<otimes>z)"
          using xscarr ycarr yfs zcarr zfs by auto
        then have "wfactors G (ys@zs) x"
          by (simp add: x)
        with xscarr show "\<exists>xs. set xs \<subseteq> carrier G \<and> wfactors G xs x"
          by fast
      qed
    qed
  qed
  from acarr show ?thesis by (rule r)
qed


subsubsection \<open>Primeness condition\<close>

lemma (in comm_monoid_cancel) multlist_prime_pos:
  assumes aprime: "prime G a" and carr: "a \<in> carrier G" 
     and as: "set as \<subseteq> carrier G" "a divides (foldr (\<otimes>) as \<one>)"
   shows "\<exists>i<length as. a divides (as!i)"
  using as
proof (induction as)
  case Nil
  then show ?case
    by simp (meson Units_one_closed aprime carr divides_unit primeE)
next
  case (Cons x as)
  then have "x \<in> carrier G"  "set as \<subseteq> carrier G" and "a divides x \<otimes> foldr (\<otimes>) as \<one>"
    by (auto simp: )
  with carr aprime have "a divides x \<or> a divides foldr (\<otimes>) as \<one>"
    by (intro prime_divides) simp+
  then show ?case
    using Cons.IH Cons.prems(1) by force
qed

proposition (in primeness_condition_monoid) wfactors_unique:
  assumes "wfactors G as a"  "wfactors G as' a"
    and "a \<in> carrier G"  "set as \<subseteq> carrier G"  "set as' \<subseteq> carrier G"
  shows "essentially_equal G as as'"
  using assms
proof (induct as arbitrary: a as')
  case Nil
  then have "a \<sim> \<one>"
    by (simp add: perm_wfactorsD) 
  then have "as' = []"
    using Nil.prems assoc_unit_l unit_wfactors_empty by blast
  then show ?case
    by auto
next
  case (Cons ah as)
  then have ahdvda: "ah divides a"
    using wfactors_dividesI by auto
    then obtain a' where a'carr: "a' \<in> carrier G" and a: "a = ah \<otimes> a'"
      by blast
    have carr_ah: "ah \<in> carrier G" "set as \<subseteq> carrier G"
      using Cons.prems by fastforce+
    have "ah \<otimes> foldr (\<otimes>) as \<one> \<sim> a"
      by (rule wfactorsE[OF \<open>wfactors G (ah # as) a\<close>]) auto
    then have "foldr (\<otimes>) as \<one> \<sim> a'"
      by (metis Cons.prems(4) a a'carr assoc_l_cancel insert_subset list.set(2) monoid.multlist_closed monoid_axioms)
    then
    have a'fs: "wfactors G as a'"
      by (meson Cons.prems(1) set_subset_Cons subset_iff wfactorsE wfactorsI)
    then have ahirr: "irreducible G ah"
      by (meson Cons.prems(1) list.set_intros(1) wfactorsE)
    with Cons have ahprime: "prime G ah"
      by (simp add: irreducible_prime)
    note ahdvda
    also have "a divides (foldr (\<otimes>) as' \<one>)"
      by (meson Cons.prems(2) associatedE wfactorsE)
    finally have "ah divides (foldr (\<otimes>) as' \<one>)"
      using Cons.prems(4) by auto
    with ahprime have "\<exists>i<length as'. ah divides as'!i"
      by (intro multlist_prime_pos) (use Cons.prems in auto)
    then obtain i where len: "i<length as'" and ahdvd: "ah divides as'!i"
      by blast
    then obtain x where "x \<in> carrier G" and asi: "as'!i = ah \<otimes> x"
      by blast
    have irrasi: "irreducible G (as'!i)"
      using nth_mem[OF len] wfactorsE
      by (metis Cons.prems(2))
    have asicarr[simp]: "as'!i \<in> carrier G"
      using len \<open>set as' \<subseteq> carrier G\<close> nth_mem by blast
    have asiah: "as'!i \<sim> ah"
      by (metis \<open>ah \<in> carrier G\<close> \<open>x \<in> carrier G\<close> asi irrasi ahprime associatedI2 irreducible_prodE primeE)
    note setparts = set_take_subset[of i as'] set_drop_subset[of "Suc i" as']
    have "\<exists>aa_1. aa_1 \<in> carrier G \<and> wfactors G (take i as') aa_1"
      using Cons
      by (metis setparts(1) subset_trans in_set_takeD wfactorsE wfactors_prod_exists)
    then obtain aa_1 where aa1carr [simp]: "aa_1 \<in> carrier G" and aa1fs: "wfactors G (take i as') aa_1"
      by auto
    obtain aa_2 where aa2carr [simp]: "aa_2 \<in> carrier G"
      and aa2fs: "wfactors G (drop (Suc i) as') aa_2"
      by (metis Cons.prems(2) Cons.prems(5) subset_code(1) in_set_dropD wfactors_def wfactors_prod_exists)

    have set_drop: "set (drop (Suc i) as') \<subseteq> carrier G"
      using Cons.prems(5) setparts(2) by blast
    moreover have set_take: "set (take i as') \<subseteq> carrier G"
      using  Cons.prems(5) setparts by auto
    moreover have v1: "wfactors G (take i as' @ drop (Suc i) as') (aa_1 \<otimes> aa_2)"
      using aa1fs aa2fs \<open>set as' \<subseteq> carrier G\<close> by (force simp add: dest: in_set_takeD in_set_dropD)
    ultimately have v1': "wfactors G (as'!i # take i as' @ drop (Suc i) as') (as'!i \<otimes> (aa_1 \<otimes> aa_2))"
      using irrasi wfactors_mult_single
        by (simp add: irrasi v1 wfactors_mult_single)      
    have "wfactors G (as'!i # drop (Suc i) as') (as'!i \<otimes> aa_2)"
      by (simp add: aa2fs irrasi set_drop wfactors_mult_single)
    with len  aa1carr aa2carr aa1fs
    have v2: "wfactors G (take i as' @ as'!i # drop (Suc i) as') (aa_1 \<otimes> (as'!i \<otimes> aa_2))"
      using wfactors_mult  by (simp add: set_take set_drop) 
    from len have as': "as' = (take i as' @ as'!i # drop (Suc i) as')"
      by (simp add: Cons_nth_drop_Suc)
    have eer: "essentially_equal G (take i as' @ as'!i # drop (Suc i) as') as'"
      using Cons.prems(5) as' by auto
    with v2 aa1carr aa2carr nth_mem[OF len] have "aa_1 \<otimes> (as'!i \<otimes> aa_2) \<sim> a"
      using Cons.prems as' comm_monoid_cancel.ee_wfactorsD is_comm_monoid_cancel by fastforce
    then have t1: "as'!i \<otimes> (aa_1 \<otimes> aa_2) \<sim> a"
      by (metis aa1carr aa2carr asicarr m_lcomm)
    from asiah have "ah \<otimes> (aa_1 \<otimes> aa_2) \<sim> as'!i \<otimes> (aa_1 \<otimes> aa_2)"
      by (simp add: \<open>ah \<in> carrier G\<close> associated_sym mult_cong_l)
    also note t1
    finally have "ah \<otimes> (aa_1 \<otimes> aa_2) \<sim> a"
      using Cons.prems(3) carr_ah aa1carr aa2carr by blast
    with aa1carr aa2carr a'carr nth_mem[OF len] have a': "aa_1 \<otimes> aa_2 \<sim> a'"
      using a assoc_l_cancel carr_ah(1) by blast
    note v1
    also note a'
    finally have "wfactors G (take i as' @ drop (Suc i) as') a'"
      by (simp add: a'carr set_drop set_take)
    from a'fs this have "essentially_equal G as (take i as' @ drop (Suc i) as')"
      using Cons.hyps a'carr carr_ah(2) set_drop set_take by auto
    then obtain bs where \<open>mset as = mset bs\<close> \<open>bs [\<sim>] take i as' @ drop (Suc i) as'\<close>
      by (auto simp add: essentially_equal_def)
    with carr_ah have \<open>mset (ah # as) = mset (ah # bs)\<close> \<open>ah # bs [\<sim>] ah # take i as' @ drop (Suc i) as'\<close>
      by simp_all
    then have ee1: "essentially_equal G (ah # as) (ah # take i as' @ drop (Suc i) as')"
      unfolding essentially_equal_def by blast
    have ee2: "essentially_equal G (ah # take i as' @ drop (Suc i) as')
      (as' ! i # take i as' @ drop (Suc i) as')"
    proof (intro essentially_equalI)
      show "ah # take i as' @ drop (Suc i) as' <~~> ah # take i as' @ drop (Suc i) as'"
        by simp
    next
      show "ah # take i as' @ drop (Suc i) as' [\<sim>] as' ! i # take i as' @ drop (Suc i) as'"
        by (simp add: asiah associated_sym set_drop set_take)
    qed

    note ee1
    also note ee2
    also have "essentially_equal G (as' ! i # take i as' @ drop (Suc i) as')
                                   (take i as' @ as' ! i # drop (Suc i) as')"
      by (metis Cons.prems(5) as' essentially_equalI listassoc_refl perm_append_Cons)
    finally have "essentially_equal G (ah # as) (take i as' @ as' ! i # drop (Suc i) as')"
      using Cons.prems(4) set_drop set_take by auto
    then show ?case
      using as' by auto
qed


subsubsection \<open>Application to factorial monoids\<close>

text \<open>Number of factors for wellfoundedness\<close>

definition factorcount :: "_ \<Rightarrow> 'a \<Rightarrow> nat"
  where "factorcount G a =
    (THE c. \<forall>as. set as \<subseteq> carrier G \<and> wfactors G as a \<longrightarrow> c = length as)"

lemma (in monoid) ee_length:
  assumes ee: "essentially_equal G as bs"
  shows "length as = length bs"
  by (rule essentially_equalE[OF ee]) (metis list_all2_conv_all_nth perm_length)

lemma (in factorial_monoid) factorcount_exists:
  assumes carr[simp]: "a \<in> carrier G"
  shows "\<exists>c. \<forall>as. set as \<subseteq> carrier G \<and> wfactors G as a \<longrightarrow> c = length as"
proof -
  have "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a"
    by (intro wfactors_exist) simp
  then obtain as where ascarr[simp]: "set as \<subseteq> carrier G" and afs: "wfactors G as a"
    by (auto simp del: carr)
  have "\<forall>as'. set as' \<subseteq> carrier G \<and> wfactors G as' a \<longrightarrow> length as = length as'"
    by (metis afs ascarr assms ee_length wfactors_unique)
  then show "\<exists>c. \<forall>as'. set as' \<subseteq> carrier G \<and> wfactors G as' a \<longrightarrow> c = length as'" ..
qed

lemma (in factorial_monoid) factorcount_unique:
  assumes afs: "wfactors G as a"
    and acarr[simp]: "a \<in> carrier G" and ascarr: "set as \<subseteq> carrier G"
  shows "factorcount G a = length as"
proof -
  have "\<exists>ac. \<forall>as. set as \<subseteq> carrier G \<and> wfactors G as a \<longrightarrow> ac = length as"
    by (rule factorcount_exists) simp
  then obtain ac where alen: "\<forall>as. set as \<subseteq> carrier G \<and> wfactors G as a \<longrightarrow> ac = length as"
    by auto
  then have ac: "ac = factorcount G a"
    unfolding factorcount_def using ascarr by (blast intro: theI2 afs)
  from ascarr afs have "ac = length as"
    by (simp add: alen)
  with ac show ?thesis
    by simp
qed

lemma (in factorial_monoid) divides_fcount:
  assumes dvd: "a divides b"
    and acarr: "a \<in> carrier G"
    and bcarr:"b \<in> carrier G"
  shows "factorcount G a \<le> factorcount G b"
proof (rule dividesE[OF dvd])
  fix c
  from assms have "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a"
    by blast
  then obtain as where ascarr: "set as \<subseteq> carrier G" and afs: "wfactors G as a"
    by blast
  with acarr have fca: "factorcount G a = length as"
    by (intro factorcount_unique)

  assume ccarr: "c \<in> carrier G"
  then have "\<exists>cs. set cs \<subseteq> carrier G \<and> wfactors G cs c"
    by blast
  then obtain cs where cscarr: "set cs \<subseteq> carrier G" and cfs: "wfactors G cs c"
    by blast

  note [simp] = acarr bcarr ccarr ascarr cscarr
  assume b: "b = a \<otimes> c"
  from afs cfs have "wfactors G (as@cs) (a \<otimes> c)"
    by (intro wfactors_mult) simp_all
  with b have "wfactors G (as@cs) b"
    by simp
  then have "factorcount G b = length (as@cs)"
    by (intro factorcount_unique) simp_all
  then have "factorcount G b = length as + length cs"
    by simp
  with fca show ?thesis
    by simp
qed

lemma (in factorial_monoid) associated_fcount:
  assumes acarr: "a \<in> carrier G"
    and bcarr: "b \<in> carrier G"
    and asc: "a \<sim> b"
  shows "factorcount G a = factorcount G b"
  using assms
  by (auto simp: associated_def factorial_monoid.divides_fcount factorial_monoid_axioms le_antisym)

lemma (in factorial_monoid) properfactor_fcount:
  assumes acarr: "a \<in> carrier G" and bcarr:"b \<in> carrier G"
    and pf: "properfactor G a b"
  shows "factorcount G a < factorcount G b"
proof (rule properfactorE[OF pf], elim dividesE)
  fix c
  from assms have "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a"
    by blast
  then obtain as where ascarr: "set as \<subseteq> carrier G" and afs: "wfactors G as a"
    by blast
  with acarr have fca: "factorcount G a = length as"
    by (intro factorcount_unique)

  assume ccarr: "c \<in> carrier G"
  then have "\<exists>cs. set cs \<subseteq> carrier G \<and> wfactors G cs c"
    by blast
  then obtain cs where cscarr: "set cs \<subseteq> carrier G" and cfs: "wfactors G cs c"
    by blast

  assume b: "b = a \<otimes> c"

  have "wfactors G (as@cs) (a \<otimes> c)"
    by (rule wfactors_mult) fact+
  with b have "wfactors G (as@cs) b"
    by simp
  with ascarr cscarr bcarr have "factorcount G b = length (as@cs)"
    by (simp add: factorcount_unique)
  then have fcb: "factorcount G b = length as + length cs"
    by simp

  assume nbdvda: "\<not> b divides a"
  have "c \<notin> Units G"
  proof
    assume cunit:"c \<in> Units G"
    have "b \<otimes> inv c = a \<otimes> c \<otimes> inv c"
      by (simp add: b)
    also from ccarr acarr cunit have "\<dots> = a \<otimes> (c \<otimes> inv c)"
      by (fast intro: m_assoc)
    also from ccarr cunit have "\<dots> = a \<otimes> \<one>" by simp
    also from acarr have "\<dots> = a" by simp
    finally have "a = b \<otimes> inv c" by simp
    with ccarr cunit have "b divides a"
      by (fast intro: dividesI[of "inv c"])
    with nbdvda show False by simp
  qed
  with cfs have "length cs > 0"
    by (metis Units_one_closed assoc_unit_r ccarr foldr.simps(1) id_apply length_greater_0_conv wfactors_def)
  with fca fcb show ?thesis
    by simp
qed

sublocale factorial_monoid \<subseteq> divisor_chain_condition_monoid
  apply unfold_locales
  apply (rule wfUNIVI)
  apply (rule measure_induct[of "factorcount G"])
  using properfactor_fcount by auto

sublocale factorial_monoid \<subseteq> primeness_condition_monoid
  by standard (rule irreducible_prime)


lemma (in factorial_monoid) primeness_condition: "primeness_condition_monoid G" ..

lemma (in factorial_monoid) gcd_condition [simp]: "gcd_condition_monoid G"
  by standard (rule gcdof_exists)

sublocale factorial_monoid \<subseteq> gcd_condition_monoid
  by standard (rule gcdof_exists)

lemma (in factorial_monoid) division_weak_lattice [simp]: "weak_lattice (division_rel G)"
proof -
  interpret weak_lower_semilattice "division_rel G"
    by simp
  show "weak_lattice (division_rel G)"
  proof (unfold_locales, simp_all)
    fix x y
    assume carr: "x \<in> carrier G"  "y \<in> carrier G"
    from lcmof_exists [OF this] obtain z where zcarr: "z \<in> carrier G" and isgcd: "z lcmof x y"
      by blast
    with carr have "least (division_rel G) z (Upper (division_rel G) {x, y})"
      by (simp add: lcmof_leastUpper[symmetric])
    then show "\<exists>z. least (division_rel G) z (Upper (division_rel G) {x, y})"
      by blast
  qed
qed


subsection \<open>Factoriality Theorems\<close>

theorem factorial_condition_one: (* Jacobson theorem 2.21 *)
  "divisor_chain_condition_monoid G \<and> primeness_condition_monoid G \<longleftrightarrow> factorial_monoid G"
proof (rule iffI, clarify)
  assume dcc: "divisor_chain_condition_monoid G"
    and pc: "primeness_condition_monoid G"
  interpret divisor_chain_condition_monoid "G" by (rule dcc)
  interpret primeness_condition_monoid "G" by (rule pc)
  show "factorial_monoid G"
    by (fast intro: factorial_monoidI wfactors_exist wfactors_unique)
next
  assume "factorial_monoid G"
  then interpret factorial_monoid "G" .
  show "divisor_chain_condition_monoid G \<and> primeness_condition_monoid G"
    by rule unfold_locales
qed

theorem factorial_condition_two: (* Jacobson theorem 2.22 *)
  "divisor_chain_condition_monoid G \<and> gcd_condition_monoid G \<longleftrightarrow> factorial_monoid G"
proof (rule iffI, clarify)
  assume dcc: "divisor_chain_condition_monoid G"
    and gc: "gcd_condition_monoid G"
  interpret divisor_chain_condition_monoid "G" by (rule dcc)
  interpret gcd_condition_monoid "G" by (rule gc)
  show "factorial_monoid G"
    by (simp add: factorial_condition_one[symmetric], rule, unfold_locales)
next
  assume "factorial_monoid G"
  then interpret factorial_monoid "G" .
  show "divisor_chain_condition_monoid G \<and> gcd_condition_monoid G"
    by rule unfold_locales
qed

end
