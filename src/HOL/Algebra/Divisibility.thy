(*  Title:      HOL/Algebra/Divisibility.thy
    Author:     Clemens Ballarin
    Author:     Stephan Hohe
*)

header {* Divisibility in monoids and rings *}

theory Divisibility
imports "~~/src/HOL/Library/Permutation" Coset Group
begin

section {* Factorial Monoids *}

subsection {* Monoids with Cancellation Law *}

locale monoid_cancel = monoid +
  assumes l_cancel: 
          "\<lbrakk>c \<otimes> a = c \<otimes> b; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> a = b"
      and r_cancel: 
          "\<lbrakk>a \<otimes> c = b \<otimes> c; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> a = b"

lemma (in monoid) monoid_cancelI:
  assumes l_cancel: 
          "\<And>a b c. \<lbrakk>c \<otimes> a = c \<otimes> b; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> a = b"
      and r_cancel: 
          "\<And>a b c. \<lbrakk>a \<otimes> c = b \<otimes> c; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> a = b"
  shows "monoid_cancel G"
    by default fact+

lemma (in monoid_cancel) is_monoid_cancel:
  "monoid_cancel G"
  ..

sublocale group \<subseteq> monoid_cancel
  by default simp_all


locale comm_monoid_cancel = monoid_cancel + comm_monoid

lemma comm_monoid_cancelI:
  fixes G (structure)
  assumes "comm_monoid G"
  assumes cancel: 
          "\<And>a b c. \<lbrakk>a \<otimes> c = b \<otimes> c; a \<in> carrier G; b \<in> carrier G; c \<in> carrier G\<rbrakk> \<Longrightarrow> a = b"
  shows "comm_monoid_cancel G"
proof -
  interpret comm_monoid G by fact
  show "comm_monoid_cancel G"
    by unfold_locales (metis assms(2) m_ac(2))+
qed

lemma (in comm_monoid_cancel) is_comm_monoid_cancel:
  "comm_monoid_cancel G"
  by intro_locales

sublocale comm_group \<subseteq> comm_monoid_cancel
  ..


subsection {* Products of Units in Monoids *}

lemma (in monoid) Units_m_closed[simp, intro]:
  assumes h1unit: "h1 \<in> Units G" and h2unit: "h2 \<in> Units G"
  shows "h1 \<otimes> h2 \<in> Units G"
unfolding Units_def
using assms
by auto (metis Units_inv_closed Units_l_inv Units_m_closed Units_r_inv)

lemma (in monoid) prod_unit_l:
  assumes abunit[simp]: "a \<otimes> b \<in> Units G" and aunit[simp]: "a \<in> Units G"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "b \<in> Units G"
proof -
  have c: "inv (a \<otimes> b) \<otimes> a \<in> carrier G" by simp

  have "(inv (a \<otimes> b) \<otimes> a) \<otimes> b = inv (a \<otimes> b) \<otimes> (a \<otimes> b)" by (simp add: m_assoc)
  also have "\<dots> = \<one>" by (simp add: Units_l_inv)
  finally have li: "(inv (a \<otimes> b) \<otimes> a) \<otimes> b = \<one>" .

  have "\<one> = inv a \<otimes> a" by (simp add: Units_l_inv[symmetric])
  also have "\<dots> = inv a \<otimes> \<one> \<otimes> a" by simp
  also have "\<dots> = inv a \<otimes> ((a \<otimes> b) \<otimes> inv (a \<otimes> b)) \<otimes> a"
       by (simp add: Units_r_inv[OF abunit, symmetric] del: Units_r_inv)
  also have "\<dots> = ((inv a \<otimes> a) \<otimes> b) \<otimes> inv (a \<otimes> b) \<otimes> a"
    by (simp add: m_assoc del: Units_l_inv)
  also have "\<dots> = b \<otimes> inv (a \<otimes> b) \<otimes> a" by (simp add: Units_l_inv)
  also have "\<dots> = b \<otimes> (inv (a \<otimes> b) \<otimes> a)" by (simp add: m_assoc)
  finally have ri: "b \<otimes> (inv (a \<otimes> b) \<otimes> a) = \<one> " by simp

  from c li ri
      show "b \<in> Units G" by (simp add: Units_def, fast)
qed

lemma (in monoid) prod_unit_r:
  assumes abunit[simp]: "a \<otimes> b \<in> Units G" and bunit[simp]: "b \<in> Units G"
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

  from c li ri
      show "a \<in> Units G" by (simp add: Units_def, fast)
qed

lemma (in comm_monoid) unit_factor:
  assumes abunit: "a \<otimes> b \<in> Units G"
    and [simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "a \<in> Units G"
using abunit[simplified Units_def]
proof clarsimp
  fix i
  assume [simp]: "i \<in> carrier G"
    and li: "i \<otimes> (a \<otimes> b) = \<one>"
    and ri: "a \<otimes> b \<otimes> i = \<one>"

  have carr': "b \<otimes> i \<in> carrier G" by simp

  have "(b \<otimes> i) \<otimes> a = (i \<otimes> b) \<otimes> a" by (simp add: m_comm)
  also have "\<dots> = i \<otimes> (b \<otimes> a)" by (simp add: m_assoc)
  also have "\<dots> = i \<otimes> (a \<otimes> b)" by (simp add: m_comm)
  also note li
  finally have li': "(b \<otimes> i) \<otimes> a = \<one>" .

  have "a \<otimes> (b \<otimes> i) = a \<otimes> b \<otimes> i" by (simp add: m_assoc)
  also note ri
  finally have ri': "a \<otimes> (b \<otimes> i) = \<one>" .

  from carr' li' ri'
      show "a \<in> Units G" by (simp add: Units_def, fast)
qed


subsection {* Divisibility and Association *}

subsubsection {* Function definitions *}

definition
  factor :: "[_, 'a, 'a] \<Rightarrow> bool" (infix "divides\<index>" 65)
  where "a divides\<^bsub>G\<^esub> b \<longleftrightarrow> (\<exists>c\<in>carrier G. b = a \<otimes>\<^bsub>G\<^esub> c)"

definition
  associated :: "[_, 'a, 'a] => bool" (infix "\<sim>\<index>" 55)
  where "a \<sim>\<^bsub>G\<^esub> b \<longleftrightarrow> a divides\<^bsub>G\<^esub> b \<and> b divides\<^bsub>G\<^esub> a"

abbreviation
  "division_rel G == \<lparr>carrier = carrier G, eq = op \<sim>\<^bsub>G\<^esub>, le = op divides\<^bsub>G\<^esub>\<rparr>"

definition
  properfactor :: "[_, 'a, 'a] \<Rightarrow> bool"
  where "properfactor G a b \<longleftrightarrow> a divides\<^bsub>G\<^esub> b \<and> \<not>(b divides\<^bsub>G\<^esub> a)"

definition
  irreducible :: "[_, 'a] \<Rightarrow> bool"
  where "irreducible G a \<longleftrightarrow> a \<notin> Units G \<and> (\<forall>b\<in>carrier G. properfactor G b a \<longrightarrow> b \<in> Units G)"

definition
  prime :: "[_, 'a] \<Rightarrow> bool" where
  "prime G p \<longleftrightarrow>
    p \<notin> Units G \<and> 
    (\<forall>a\<in>carrier G. \<forall>b\<in>carrier G. p divides\<^bsub>G\<^esub> (a \<otimes>\<^bsub>G\<^esub> b) \<longrightarrow> p divides\<^bsub>G\<^esub> a \<or> p divides\<^bsub>G\<^esub> b)"


subsubsection {* Divisibility *}

lemma dividesI:
  fixes G (structure)
  assumes carr: "c \<in> carrier G"
    and p: "b = a \<otimes> c"
  shows "a divides b"
unfolding factor_def
using assms by fast

lemma dividesI' [intro]:
   fixes G (structure)
  assumes p: "b = a \<otimes> c"
    and carr: "c \<in> carrier G"
  shows "a divides b"
using assms
by (fast intro: dividesI)

lemma dividesD:
  fixes G (structure)
  assumes "a divides b"
  shows "\<exists>c\<in>carrier G. b = a \<otimes> c"
using assms
unfolding factor_def
by fast

lemma dividesE [elim]:
  fixes G (structure)
  assumes d: "a divides b"
    and elim: "\<And>c. \<lbrakk>b = a \<otimes> c; c \<in> carrier G\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from dividesD[OF d]
      obtain c
      where "c\<in>carrier G"
      and "b = a \<otimes> c"
      by auto
  thus "P" by (elim elim)
qed

lemma (in monoid) divides_refl[simp, intro!]:
  assumes carr: "a \<in> carrier G"
  shows "a divides a"
apply (intro dividesI[of "\<one>"])
apply (simp, simp add: carr)
done

lemma (in monoid) divides_trans [trans]:
  assumes dvds: "a divides b"  "b divides c"
    and acarr: "a \<in> carrier G"
  shows "a divides c"
using dvds[THEN dividesD]
by (blast intro: dividesI m_assoc acarr)

lemma (in monoid) divides_mult_lI [intro]:
  assumes ab: "a divides b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "(c \<otimes> a) divides (c \<otimes> b)"
using ab
apply (elim dividesE, simp add: m_assoc[symmetric] carr)
apply (fast intro: dividesI)
done

lemma (in monoid_cancel) divides_mult_l [simp]:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "(c \<otimes> a) divides (c \<otimes> b) = a divides b"
apply safe
 apply (elim dividesE, intro dividesI, assumption)
 apply (rule l_cancel[of c])
    apply (simp add: m_assoc carr)+
apply (fast intro: divides_mult_lI carr)
done

lemma (in comm_monoid) divides_mult_rI [intro]:
  assumes ab: "a divides b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "(a \<otimes> c) divides (b \<otimes> c)"
using carr ab
apply (simp add: m_comm[of a c] m_comm[of b c])
apply (rule divides_mult_lI, assumption+)
done

lemma (in comm_monoid_cancel) divides_mult_r [simp]:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "(a \<otimes> c) divides (b \<otimes> c) = a divides b"
using carr
by (simp add: m_comm[of a c] m_comm[of b c])

lemma (in monoid) divides_prod_r:
  assumes ab: "a divides b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "a divides (b \<otimes> c)"
using ab carr
by (fast intro: m_assoc)

lemma (in comm_monoid) divides_prod_l:
  assumes carr[intro]: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
    and ab: "a divides b"
  shows "a divides (c \<otimes> b)"
using ab carr
apply (simp add: m_comm[of c b])
apply (fast intro: divides_prod_r)
done

lemma (in monoid) unit_divides:
  assumes uunit: "u \<in> Units G"
      and acarr: "a \<in> carrier G"
  shows "u divides a"
proof (intro dividesI[of "(inv u) \<otimes> a"], fast intro: uunit acarr)
  from uunit acarr
      have xcarr: "inv u \<otimes> a \<in> carrier G" by fast

  from uunit acarr
       have "u \<otimes> (inv u \<otimes> a) = (u \<otimes> inv u) \<otimes> a" by (fast intro: m_assoc[symmetric])
  also have "\<dots> = \<one> \<otimes> a" by (simp add: Units_r_inv[OF uunit])
  also from acarr 
       have "\<dots> = a" by simp
  finally
       show "a = u \<otimes> (inv u \<otimes> a)" ..
qed

lemma (in comm_monoid) divides_unit:
  assumes udvd: "a divides u"
      and  carr: "a \<in> carrier G"  "u \<in> Units G"
  shows "a \<in> Units G"
using udvd carr
by (blast intro: unit_factor)

lemma (in comm_monoid) Unit_eq_dividesone:
  assumes ucarr: "u \<in> carrier G"
  shows "u \<in> Units G = u divides \<one>"
using ucarr
by (fast dest: divides_unit intro: unit_divides)


subsubsection {* Association *}

lemma associatedI:
  fixes G (structure)
  assumes "a divides b"  "b divides a"
  shows "a \<sim> b"
using assms
by (simp add: associated_def)

lemma (in monoid) associatedI2:
  assumes uunit[simp]: "u \<in> Units G"
    and a: "a = b \<otimes> u"
    and bcarr[simp]: "b \<in> carrier G"
  shows "a \<sim> b"
using uunit bcarr
unfolding a
apply (intro associatedI)
 apply (rule dividesI[of "inv u"], simp)
 apply (simp add: m_assoc Units_closed Units_r_inv)
apply fast
done

lemma (in monoid) associatedI2':
  assumes a: "a = b \<otimes> u"
    and uunit: "u \<in> Units G"
    and bcarr: "b \<in> carrier G"
  shows "a \<sim> b"
using assms by (intro associatedI2)

lemma associatedD:
  fixes G (structure)
  assumes "a \<sim> b"
  shows "a divides b"
using assms by (simp add: associated_def)

lemma (in monoid_cancel) associatedD2:
  assumes assoc: "a \<sim> b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "\<exists>u\<in>Units G. a = b \<otimes> u"
using assoc
unfolding associated_def
proof clarify
  assume "b divides a"
  hence "\<exists>u\<in>carrier G. a = b \<otimes> u" by (rule dividesD)
  from this obtain u
      where ucarr: "u \<in> carrier G" and a: "a = b \<otimes> u"
      by auto

  assume "a divides b"
  hence "\<exists>u'\<in>carrier G. b = a \<otimes> u'" by (rule dividesD)
  from this obtain u'
      where u'carr: "u' \<in> carrier G" and b: "b = a \<otimes> u'"
      by auto
  note carr = carr ucarr u'carr

  from carr
       have "a \<otimes> \<one> = a" by simp
  also have "\<dots> = b \<otimes> u" by (simp add: a)
  also have "\<dots> = a \<otimes> u' \<otimes> u" by (simp add: b)
  also from carr
       have "\<dots> = a \<otimes> (u' \<otimes> u)" by (simp add: m_assoc)
  finally
       have "a \<otimes> \<one> = a \<otimes> (u' \<otimes> u)" .
  with carr
      have u1: "\<one> = u' \<otimes> u" by (fast dest: l_cancel)

  from carr
       have "b \<otimes> \<one> = b" by simp
  also have "\<dots> = a \<otimes> u'" by (simp add: b)
  also have "\<dots> = b \<otimes> u \<otimes> u'" by (simp add: a)
  also from carr
       have "\<dots> = b \<otimes> (u \<otimes> u')" by (simp add: m_assoc)
  finally
       have "b \<otimes> \<one> = b \<otimes> (u \<otimes> u')" .
  with carr
      have u2: "\<one> = u \<otimes> u'" by (fast dest: l_cancel)

  from u'carr u1[symmetric] u2[symmetric]
      have "\<exists>u'\<in>carrier G. u' \<otimes> u = \<one> \<and> u \<otimes> u' = \<one>" by fast
  hence "u \<in> Units G" by (simp add: Units_def ucarr)

  from ucarr this a
      show "\<exists>u\<in>Units G. a = b \<otimes> u" by fast
qed

lemma associatedE:
  fixes G (structure)
  assumes assoc: "a \<sim> b"
    and e: "\<lbrakk>a divides b; b divides a\<rbrakk> \<Longrightarrow> P"
  shows "P"
proof -
  from assoc
      have "a divides b"  "b divides a"
      by (simp add: associated_def)+
  thus "P" by (elim e)
qed

lemma (in monoid_cancel) associatedE2:
  assumes assoc: "a \<sim> b"
    and e: "\<And>u. \<lbrakk>a = b \<otimes> u; u \<in> Units G\<rbrakk> \<Longrightarrow> P"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "P"
proof -
  from assoc and carr
      have "\<exists>u\<in>Units G. a = b \<otimes> u" by (rule associatedD2)
  from this obtain u
      where "u \<in> Units G"  "a = b \<otimes> u"
      by auto
  thus "P" by (elim e)
qed

lemma (in monoid) associated_refl [simp, intro!]:
  assumes "a \<in> carrier G"
  shows "a \<sim> a"
using assms
by (fast intro: associatedI)

lemma (in monoid) associated_sym [sym]:
  assumes "a \<sim> b"
    and "a \<in> carrier G"  "b \<in> carrier G"
  shows "b \<sim> a"
using assms
by (iprover intro: associatedI elim: associatedE)

lemma (in monoid) associated_trans [trans]:
  assumes "a \<sim> b"  "b \<sim> c"
    and "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "a \<sim> c"
using assms
by (iprover intro: associatedI divides_trans elim: associatedE)

lemma (in monoid) division_equiv [intro, simp]:
  "equivalence (division_rel G)"
  apply unfold_locales
  apply simp_all
  apply (metis associated_def)
  apply (iprover intro: associated_trans)
  done


subsubsection {* Division and associativity *}

lemma divides_antisym:
  fixes G (structure)
  assumes "a divides b"  "b divides a"
    and "a \<in> carrier G"  "b \<in> carrier G"
  shows "a \<sim> b"
using assms
by (fast intro: associatedI)

lemma (in monoid) divides_cong_l [trans]:
  assumes xx': "x \<sim> x'"
    and xdvdy: "x' divides y"
    and carr [simp]: "x \<in> carrier G"  "x' \<in> carrier G"  "y \<in> carrier G"
  shows "x divides y"
proof -
  from xx'
       have "x divides x'" by (simp add: associatedD)
  also note xdvdy
  finally
       show "x divides y" by simp
qed

lemma (in monoid) divides_cong_r [trans]:
  assumes xdvdy: "x divides y"
    and yy': "y \<sim> y'"
    and carr[simp]: "x \<in> carrier G"  "y \<in> carrier G"  "y' \<in> carrier G"
  shows "x divides y'"
proof -
  note xdvdy
  also from yy'
       have "y divides y'" by (simp add: associatedD)
  finally
       show "x divides y'" by simp
qed

lemma (in monoid) division_weak_partial_order [simp, intro!]:
  "weak_partial_order (division_rel G)"
  apply unfold_locales
  apply simp_all
  apply (simp add: associated_sym)
  apply (blast intro: associated_trans)
  apply (simp add: divides_antisym)
  apply (blast intro: divides_trans)
  apply (blast intro: divides_cong_l divides_cong_r associated_sym)
  done

    
subsubsection {* Multiplication and associativity *}

lemma (in monoid_cancel) mult_cong_r:
  assumes "b \<sim> b'"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "b' \<in> carrier G"
  shows "a \<otimes> b \<sim> a \<otimes> b'"
using assms
apply (elim associatedE2, intro associatedI2)
apply (auto intro: m_assoc[symmetric])
done

lemma (in comm_monoid_cancel) mult_cong_l:
  assumes "a \<sim> a'"
    and carr: "a \<in> carrier G"  "a' \<in> carrier G"  "b \<in> carrier G"
  shows "a \<otimes> b \<sim> a' \<otimes> b"
using assms
apply (elim associatedE2, intro associatedI2)
    apply assumption
   apply (simp add: m_assoc Units_closed)
   apply (simp add: m_comm Units_closed)
  apply simp+
done

lemma (in monoid_cancel) assoc_l_cancel:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"  "b' \<in> carrier G"
    and "a \<otimes> b \<sim> a \<otimes> b'"
  shows "b \<sim> b'"
using assms
apply (elim associatedE2, intro associatedI2)
    apply assumption
   apply (rule l_cancel[of a])
      apply (simp add: m_assoc Units_closed)
     apply fast+
done

lemma (in comm_monoid_cancel) assoc_r_cancel:
  assumes "a \<otimes> b \<sim> a' \<otimes> b"
    and carr: "a \<in> carrier G"  "a' \<in> carrier G"  "b \<in> carrier G"
  shows "a \<sim> a'"
using assms
apply (elim associatedE2, intro associatedI2)
    apply assumption
   apply (rule r_cancel[of a b])
      apply (metis Units_closed assms(3) assms(4) m_ac)
     apply fast+
done


subsubsection {* Units *}

lemma (in monoid_cancel) assoc_unit_l [trans]:
  assumes asc: "a \<sim> b" and bunit: "b \<in> Units G"
    and carr: "a \<in> carrier G" 
  shows "a \<in> Units G"
using assms
by (fast elim: associatedE2)

lemma (in monoid_cancel) assoc_unit_r [trans]:
  assumes aunit: "a \<in> Units G" and asc: "a \<sim> b"
    and bcarr: "b \<in> carrier G"
  shows "b \<in> Units G"
using aunit bcarr associated_sym[OF asc]
by (blast intro: assoc_unit_l)

lemma (in comm_monoid) Units_cong:
  assumes aunit: "a \<in> Units G" and asc: "a \<sim> b"
    and bcarr: "b \<in> carrier G"
  shows "b \<in> Units G"
using assms
by (blast intro: divides_unit elim: associatedE)

lemma (in monoid) Units_assoc:
  assumes units: "a \<in> Units G"  "b \<in> Units G"
  shows "a \<sim> b"
using units
by (fast intro: associatedI unit_divides)

lemma (in monoid) Units_are_ones:
  "Units G {.=}\<^bsub>(division_rel G)\<^esub> {\<one>}"
apply (simp add: set_eq_def elem_def, rule, simp_all)
proof clarsimp
  fix a
  assume aunit: "a \<in> Units G"
  show "a \<sim> \<one>"
  apply (rule associatedI)
   apply (fast intro: dividesI[of "inv a"] aunit Units_r_inv[symmetric])
  apply (fast intro: dividesI[of "a"] l_one[symmetric] Units_closed[OF aunit])
  done
next
  have "\<one> \<in> Units G" by simp
  moreover have "\<one> \<sim> \<one>" by simp
  ultimately show "\<exists>a \<in> Units G. \<one> \<sim> a" by fast
qed

lemma (in comm_monoid) Units_Lower:
  "Units G = Lower (division_rel G) (carrier G)"
apply (simp add: Units_def Lower_def)
apply (rule, rule)
 apply clarsimp
  apply (rule unit_divides)
   apply (unfold Units_def, fast)
  apply assumption
apply clarsimp
apply (metis Unit_eq_dividesone Units_r_inv_ex m_ac(2) one_closed)
done


subsubsection {* Proper factors *}

lemma properfactorI:
  fixes G (structure)
  assumes "a divides b"
    and "\<not>(b divides a)"
  shows "properfactor G a b"
using assms
unfolding properfactor_def
by simp

lemma properfactorI2:
  fixes G (structure)
  assumes advdb: "a divides b"
    and neq: "\<not>(a \<sim> b)"
  shows "properfactor G a b"
apply (rule properfactorI, rule advdb)
proof (rule ccontr, simp)
  assume "b divides a"
  with advdb have "a \<sim> b" by (rule associatedI)
  with neq show "False" by fast
qed

lemma (in comm_monoid_cancel) properfactorI3:
  assumes p: "p = a \<otimes> b"
    and nunit: "b \<notin> Units G"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "p \<in> carrier G"
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

  hence rinv: "\<one> = b \<otimes> c" by (intro l_cancel[of "a" "\<one>" "b \<otimes> c"], simp+)
  also have "\<dots> = c \<otimes> b" by (simp add: m_comm)
  finally have linv: "\<one> = c \<otimes> b" .

  from ccarr linv[symmetric] rinv[symmetric]
  have "b \<in> Units G" unfolding Units_def by fastforce
  with nunit
      show "False" ..
qed

lemma properfactorE:
  fixes G (structure)
  assumes pf: "properfactor G a b"
    and r: "\<lbrakk>a divides b; \<not>(b divides a)\<rbrakk> \<Longrightarrow> P"
  shows "P"
using pf
unfolding properfactor_def
by (fast intro: r)

lemma properfactorE2:
  fixes G (structure)
  assumes pf: "properfactor G a b"
    and elim: "\<lbrakk>a divides b; \<not>(a \<sim> b)\<rbrakk> \<Longrightarrow> P"
  shows "P"
using pf
unfolding properfactor_def
by (fast elim: elim associatedE)

lemma (in monoid) properfactor_unitE:
  assumes uunit: "u \<in> Units G"
    and pf: "properfactor G a u"
    and acarr: "a \<in> carrier G"
  shows "P"
using pf unit_divides[OF uunit acarr]
by (fast elim: properfactorE)


lemma (in monoid) properfactor_divides:
  assumes pf: "properfactor G a b"
  shows "a divides b"
using pf
by (elim properfactorE)

lemma (in monoid) properfactor_trans1 [trans]:
  assumes dvds: "a divides b"  "properfactor G b c"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G a c"
using dvds carr
apply (elim properfactorE, intro properfactorI)
 apply (iprover intro: divides_trans)+
done

lemma (in monoid) properfactor_trans2 [trans]:
  assumes dvds: "properfactor G a b"  "b divides c"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G a c"
using dvds carr
apply (elim properfactorE, intro properfactorI)
 apply (iprover intro: divides_trans)+
done

lemma properfactor_lless:
  fixes G (structure)
  shows "properfactor G = lless (division_rel G)"
apply (rule ext) apply (rule ext) apply rule
 apply (fastforce elim: properfactorE2 intro: weak_llessI)
apply (fastforce elim: weak_llessE intro: properfactorI2)
done

lemma (in monoid) properfactor_cong_l [trans]:
  assumes x'x: "x' \<sim> x"
    and pf: "properfactor G x y"
    and carr: "x \<in> carrier G"  "x' \<in> carrier G"  "y \<in> carrier G"
  shows "properfactor G x' y"
using pf
unfolding properfactor_lless
proof -
  interpret weak_partial_order "division_rel G" ..
  from x'x
       have "x' .=\<^bsub>division_rel G\<^esub> x" by simp
  also assume "x \<sqsubset>\<^bsub>division_rel G\<^esub> y"
  finally
       show "x' \<sqsubset>\<^bsub>division_rel G\<^esub> y" by (simp add: carr)
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
  finally
       show "x \<sqsubset>\<^bsub>division_rel G\<^esub> y'" by (simp add: carr)
qed

lemma (in monoid_cancel) properfactor_mult_lI [intro]:
  assumes ab: "properfactor G a b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G (c \<otimes> a) (c \<otimes> b)"
using ab carr
by (fastforce elim: properfactorE intro: properfactorI)

lemma (in monoid_cancel) properfactor_mult_l [simp]:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G (c \<otimes> a) (c \<otimes> b) = properfactor G a b"
using carr
by (fastforce elim: properfactorE intro: properfactorI)

lemma (in comm_monoid_cancel) properfactor_mult_rI [intro]:
  assumes ab: "properfactor G a b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G (a \<otimes> c) (b \<otimes> c)"
using ab carr
by (fastforce elim: properfactorE intro: properfactorI)

lemma (in comm_monoid_cancel) properfactor_mult_r [simp]:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G (a \<otimes> c) (b \<otimes> c) = properfactor G a b"
using carr
by (fastforce elim: properfactorE intro: properfactorI)

lemma (in monoid) properfactor_prod_r:
  assumes ab: "properfactor G a b"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G a (b \<otimes> c)"
by (intro properfactor_trans2[OF ab] divides_prod_r, simp+)

lemma (in comm_monoid) properfactor_prod_l:
  assumes ab: "properfactor G a b"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "properfactor G a (c \<otimes> b)"
by (intro properfactor_trans2[OF ab] divides_prod_l, simp+)


subsection {* Irreducible Elements and Primes *}

subsubsection {* Irreducible elements *}

lemma irreducibleI:
  fixes G (structure)
  assumes "a \<notin> Units G"
    and "\<And>b. \<lbrakk>b \<in> carrier G; properfactor G b a\<rbrakk> \<Longrightarrow> b \<in> Units G"
  shows "irreducible G a"
using assms 
unfolding irreducible_def
by blast

lemma irreducibleE:
  fixes G (structure)
  assumes irr: "irreducible G a"
     and elim: "\<lbrakk>a \<notin> Units G; \<forall>b. b \<in> carrier G \<and> properfactor G b a \<longrightarrow> b \<in> Units G\<rbrakk> \<Longrightarrow> P"
  shows "P"
using assms
unfolding irreducible_def
by blast

lemma irreducibleD:
  fixes G (structure)
  assumes irr: "irreducible G a"
     and pf: "properfactor G b a"
     and bcarr: "b \<in> carrier G"
  shows "b \<in> Units G"
using assms
by (fast elim: irreducibleE)

lemma (in monoid_cancel) irreducible_cong [trans]:
  assumes irred: "irreducible G a"
    and aa': "a \<sim> a'"
    and carr[simp]: "a \<in> carrier G"  "a' \<in> carrier G"
  shows "irreducible G a'"
using assms
apply (elim irreducibleE, intro irreducibleI)
apply simp_all
apply (metis assms(2) assms(3) assoc_unit_l)
apply (metis assms(2) assms(3) assms(4) associated_sym properfactor_cong_r)
done

lemma (in monoid) irreducible_prod_rI:
  assumes airr: "irreducible G a"
    and bunit: "b \<in> Units G"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "irreducible G (a \<otimes> b)"
using airr carr bunit
apply (elim irreducibleE, intro irreducibleI, clarify)
 apply (subgoal_tac "a \<in> Units G", simp)
 apply (intro prod_unit_r[of a b] carr bunit, assumption)
apply (metis assms associatedI2 m_closed properfactor_cong_r)
done

lemma (in comm_monoid) irreducible_prod_lI:
  assumes birr: "irreducible G b"
    and aunit: "a \<in> Units G"
    and carr [simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "irreducible G (a \<otimes> b)"
apply (subst m_comm, simp+)
apply (intro irreducible_prod_rI assms)
done

lemma (in comm_monoid_cancel) irreducible_prodE [elim]:
  assumes irr: "irreducible G (a \<otimes> b)"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"
    and e1: "\<lbrakk>irreducible G a; b \<in> Units G\<rbrakk> \<Longrightarrow> P"
    and e2: "\<lbrakk>a \<in> Units G; irreducible G b\<rbrakk> \<Longrightarrow> P"
  shows "P"
using irr
proof (elim irreducibleE)
  assume abnunit: "a \<otimes> b \<notin> Units G"
    and isunit[rule_format]: "\<forall>ba. ba \<in> carrier G \<and> properfactor G ba (a \<otimes> b) \<longrightarrow> ba \<in> Units G"

  show "P"
  proof (cases "a \<in> Units G")
    assume aunit: "a \<in>  Units G"
    have "irreducible G b"
    apply (rule irreducibleI)
    proof (rule ccontr, simp)
      assume "b \<in> Units G"
      with aunit have "(a \<otimes> b) \<in> Units G" by fast
      with abnunit show "False" ..
    next
      fix c
      assume ccarr: "c \<in> carrier G"
        and "properfactor G c b"
      hence "properfactor G c (a \<otimes> b)" by (simp add: properfactor_prod_l[of c b a])
      from ccarr this show "c \<in> Units G" by (fast intro: isunit)
    qed

    from aunit this show "P" by (rule e2)
  next
    assume anunit: "a \<notin> Units G"
    with carr have "properfactor G b (b \<otimes> a)" by (fast intro: properfactorI3)
    hence bf: "properfactor G b (a \<otimes> b)" by (subst m_comm[of a b], simp+)
    hence bunit: "b \<in> Units G" by (intro isunit, simp)

    have "irreducible G a"
    apply (rule irreducibleI)
    proof (rule ccontr, simp)
      assume "a \<in> Units G"
      with bunit have "(a \<otimes> b) \<in> Units G" by fast
      with abnunit show "False" ..
    next
      fix c
      assume ccarr: "c \<in> carrier G"
        and "properfactor G c a"
      hence "properfactor G c (a \<otimes> b)" by (simp add: properfactor_prod_r[of c a b])
      from ccarr this show "c \<in> Units G" by (fast intro: isunit)
    qed

    from this bunit show "P" by (rule e1)
  qed
qed


subsubsection {* Prime elements *}

lemma primeI:
  fixes G (structure)
  assumes "p \<notin> Units G"
    and "\<And>a b. \<lbrakk>a \<in> carrier G; b \<in> carrier G; p divides (a \<otimes> b)\<rbrakk> \<Longrightarrow> p divides a \<or> p divides b"
  shows "prime G p"
using assms
unfolding prime_def
by blast

lemma primeE:
  fixes G (structure)
  assumes pprime: "prime G p"
    and e: "\<lbrakk>p \<notin> Units G; \<forall>a\<in>carrier G. \<forall>b\<in>carrier G.
                          p divides a \<otimes> b \<longrightarrow> p divides a \<or> p divides b\<rbrakk> \<Longrightarrow> P"
  shows "P"
using pprime
unfolding prime_def
by (blast dest: e)

lemma (in comm_monoid_cancel) prime_divides:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"
    and pprime: "prime G p"
    and pdvd: "p divides a \<otimes> b"
  shows "p divides a \<or> p divides b"
using assms
by (blast elim: primeE)

lemma (in monoid_cancel) prime_cong [trans]:
  assumes pprime: "prime G p"
    and pp': "p \<sim> p'"
    and carr[simp]: "p \<in> carrier G"  "p' \<in> carrier G"
  shows "prime G p'"
using pprime
apply (elim primeE, intro primeI)
apply (metis assms(2) assms(3) assoc_unit_l)
apply (metis assms(2) assms(3) assms(4) associated_sym divides_cong_l m_closed)
done

subsection {* Factorization and Factorial Monoids *}

subsubsection {* Function definitions *}

definition
  factors :: "[_, 'a list, 'a] \<Rightarrow> bool"
  where "factors G fs a \<longleftrightarrow> (\<forall>x \<in> (set fs). irreducible G x) \<and> foldr (op \<otimes>\<^bsub>G\<^esub>) fs \<one>\<^bsub>G\<^esub> = a"

definition
  wfactors ::"[_, 'a list, 'a] \<Rightarrow> bool"
  where "wfactors G fs a \<longleftrightarrow> (\<forall>x \<in> (set fs). irreducible G x) \<and> foldr (op \<otimes>\<^bsub>G\<^esub>) fs \<one>\<^bsub>G\<^esub> \<sim>\<^bsub>G\<^esub> a"

abbreviation
  list_assoc :: "('a,_) monoid_scheme \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" (infix "[\<sim>]\<index>" 44)
  where "list_assoc G == list_all2 (op \<sim>\<^bsub>G\<^esub>)"

definition
  essentially_equal :: "[_, 'a list, 'a list] \<Rightarrow> bool"
  where "essentially_equal G fs1 fs2 \<longleftrightarrow> (\<exists>fs1'. fs1 <~~> fs1' \<and> fs1' [\<sim>]\<^bsub>G\<^esub> fs2)"


locale factorial_monoid = comm_monoid_cancel +
  assumes factors_exist: 
          "\<lbrakk>a \<in> carrier G; a \<notin> Units G\<rbrakk> \<Longrightarrow> \<exists>fs. set fs \<subseteq> carrier G \<and> factors G fs a"
      and factors_unique: 
          "\<lbrakk>factors G fs a; factors G fs' a; a \<in> carrier G; a \<notin> Units G; 
            set fs \<subseteq> carrier G; set fs' \<subseteq> carrier G\<rbrakk> \<Longrightarrow> essentially_equal G fs fs'"


subsubsection {* Comparing lists of elements *}

text {* Association on lists *}

lemma (in monoid) listassoc_refl [simp, intro]:
  assumes "set as \<subseteq> carrier G"
  shows "as [\<sim>] as"
using assms
by (induct as) simp+

lemma (in monoid) listassoc_sym [sym]:
  assumes "as [\<sim>] bs"
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "bs [\<sim>] as"
using assms
proof (induct as arbitrary: bs, simp)
  case Cons
  thus ?case
    apply (induct bs, simp)
    apply clarsimp
    apply (iprover intro: associated_sym)
  done
qed

lemma (in monoid) listassoc_trans [trans]:
  assumes "as [\<sim>] bs" and "bs [\<sim>] cs"
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G" and "set cs \<subseteq> carrier G"
  shows "as [\<sim>] cs"
using assms
apply (simp add: list_all2_conv_all_nth set_conv_nth, safe)
apply (rule associated_trans)
    apply (subgoal_tac "as ! i \<sim> bs ! i", assumption)
    apply (simp, simp)
  apply blast+
done

lemma (in monoid_cancel) irrlist_listassoc_cong:
  assumes "\<forall>a\<in>set as. irreducible G a"
    and "as [\<sim>] bs"
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "\<forall>a\<in>set bs. irreducible G a"
using assms
apply (clarsimp simp add: list_all2_conv_all_nth set_conv_nth)
apply (blast intro: irreducible_cong)
done


text {* Permutations *}

lemma perm_map [intro]:
  assumes p: "a <~~> b"
  shows "map f a <~~> map f b"
using p
by induct auto

lemma perm_map_switch:
  assumes m: "map f a = map f b" and p: "b <~~> c"
  shows "\<exists>d. a <~~> d \<and> map f d = map f c"
using p m
by (induct arbitrary: a) (simp, force, force, blast)

lemma (in monoid) perm_assoc_switch:
   assumes a:"as [\<sim>] bs" and p: "bs <~~> cs"
   shows "\<exists>bs'. as <~~> bs' \<and> bs' [\<sim>] cs"
using p a
apply (induct bs cs arbitrary: as, simp)
  apply (clarsimp simp add: list_all2_Cons2, blast)
 apply (clarsimp simp add: list_all2_Cons2)
 apply blast
apply blast
done

lemma (in monoid) perm_assoc_switch_r:
   assumes p: "as <~~> bs" and a:"bs [\<sim>] cs"
   shows "\<exists>bs'. as [\<sim>] bs' \<and> bs' <~~> cs"
using p a
apply (induct as bs arbitrary: cs, simp)
  apply (clarsimp simp add: list_all2_Cons1, blast)
 apply (clarsimp simp add: list_all2_Cons1)
 apply blast
apply blast
done

declare perm_sym [sym]

lemma perm_setP:
  assumes perm: "as <~~> bs"
    and as: "P (set as)"
  shows "P (set bs)"
proof -
  from perm
      have "multiset_of as = multiset_of bs"
      by (simp add: multiset_of_eq_perm)
  hence "set as = set bs" by (rule multiset_of_eq_setD)
  with as
      show "P (set bs)" by simp
qed

lemmas (in monoid) perm_closed =
    perm_setP[of _ _ "\<lambda>as. as \<subseteq> carrier G"]

lemmas (in monoid) irrlist_perm_cong =
    perm_setP[of _ _ "\<lambda>as. \<forall>a\<in>as. irreducible G a"]


text {* Essentially equal factorizations *}

lemma (in monoid) essentially_equalI:
  assumes ex: "fs1 <~~> fs1'"  "fs1' [\<sim>] fs2"
  shows "essentially_equal G fs1 fs2"
using ex
unfolding essentially_equal_def
by fast

lemma (in monoid) essentially_equalE:
  assumes ee: "essentially_equal G fs1 fs2"
    and e: "\<And>fs1'. \<lbrakk>fs1 <~~> fs1'; fs1' [\<sim>] fs2\<rbrakk> \<Longrightarrow> P"
  shows "P"
using ee
unfolding essentially_equal_def
by (fast intro: e)

lemma (in monoid) ee_refl [simp,intro]:
  assumes carr: "set as \<subseteq> carrier G"
  shows "essentially_equal G as as"
using carr
by (fast intro: essentially_equalI)

lemma (in monoid) ee_sym [sym]:
  assumes ee: "essentially_equal G as bs"
    and carr: "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"
  shows "essentially_equal G bs as"
using ee
proof (elim essentially_equalE)
  fix fs
  assume "as <~~> fs"  "fs [\<sim>] bs"
  hence "\<exists>fs'. as [\<sim>] fs' \<and> fs' <~~> bs" by (rule perm_assoc_switch_r)
  from this obtain fs'
      where a: "as [\<sim>] fs'" and p: "fs' <~~> bs"
      by auto
  from p have "bs <~~> fs'" by (rule perm_sym)
  with a[symmetric] carr
      show ?thesis
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
  assume  "abs [\<sim>] bs" and pb: "bs <~~> bcs"
  hence "\<exists>bs'. abs <~~> bs' \<and> bs' [\<sim>] bcs" by (rule perm_assoc_switch)
  from this obtain bs'
      where p: "abs <~~> bs'" and a: "bs' [\<sim>] bcs"
      by auto

  assume "as <~~> abs"
  with p
      have pp: "as <~~> bs'" by fast

  from pp ascarr have c1: "set bs' \<subseteq> carrier G" by (rule perm_closed)
  from pb bscarr have c2: "set bcs \<subseteq> carrier G" by (rule perm_closed)
  note a
  also assume "bcs [\<sim>] cs"
  finally (listassoc_trans) have"bs' [\<sim>] cs" by (simp add: c1 c2 cscarr)

  with pp
      show ?thesis
      by (rule essentially_equalI)
qed


subsubsection {* Properties of lists of elements *}

text {* Multiplication of factors in a list *}

lemma (in monoid) multlist_closed [simp, intro]:
  assumes ascarr: "set fs \<subseteq> carrier G"
  shows "foldr (op \<otimes>) fs \<one> \<in> carrier G"
by (insert ascarr, induct fs, simp+)

lemma  (in comm_monoid) multlist_dividesI (*[intro]*):
  assumes "f \<in> set fs" and "f \<in> carrier G" and "set fs \<subseteq> carrier G"
  shows "f divides (foldr (op \<otimes>) fs \<one>)"
using assms
apply (induct fs)
 apply simp
apply (case_tac "f = a", simp)
 apply (fast intro: dividesI)
apply clarsimp
apply (metis assms(2) divides_prod_l multlist_closed)
done

lemma (in comm_monoid_cancel) multlist_listassoc_cong:
  assumes "fs [\<sim>] fs'"
    and "set fs \<subseteq> carrier G" and "set fs' \<subseteq> carrier G"
  shows "foldr (op \<otimes>) fs \<one> \<sim> foldr (op \<otimes>) fs' \<one>"
using assms
proof (induct fs arbitrary: fs', simp)
  case (Cons a as fs')
  thus ?case
  apply (induct fs', simp)
  proof clarsimp
    fix b bs
    assume "a \<sim> b" 
      and acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G"
      and ascarr: "set as \<subseteq> carrier G"
    hence p: "a \<otimes> foldr op \<otimes> as \<one> \<sim> b \<otimes> foldr op \<otimes> as \<one>"
        by (fast intro: mult_cong_l)
    also
      assume "as [\<sim>] bs"
         and bscarr: "set bs \<subseteq> carrier G"
         and "\<And>fs'. \<lbrakk>as [\<sim>] fs'; set fs' \<subseteq> carrier G\<rbrakk> \<Longrightarrow> foldr op \<otimes> as \<one> \<sim> foldr op \<otimes> fs' \<one>"
      hence "foldr op \<otimes> as \<one> \<sim> foldr op \<otimes> bs \<one>" by simp
      with ascarr bscarr bcarr
          have "b \<otimes> foldr op \<otimes> as \<one> \<sim> b \<otimes> foldr op \<otimes> bs \<one>"
          by (fast intro: mult_cong_r)
   finally
       show "a \<otimes> foldr op \<otimes> as \<one> \<sim> b \<otimes> foldr op \<otimes> bs \<one>"
       by (simp add: ascarr bscarr acarr bcarr)
  qed
qed

lemma (in comm_monoid) multlist_perm_cong:
  assumes prm: "as <~~> bs"
    and ascarr: "set as \<subseteq> carrier G"
  shows "foldr (op \<otimes>) as \<one> = foldr (op \<otimes>) bs \<one>"
using prm ascarr
apply (induct, simp, clarsimp simp add: m_ac, clarsimp)
proof clarsimp
  fix xs ys zs
  assume "xs <~~> ys"  "set xs \<subseteq> carrier G"
  hence "set ys \<subseteq> carrier G" by (rule perm_closed)
  moreover assume "set ys \<subseteq> carrier G \<Longrightarrow> foldr op \<otimes> ys \<one> = foldr op \<otimes> zs \<one>"
  ultimately show "foldr op \<otimes> ys \<one> = foldr op \<otimes> zs \<one>" by simp
qed

lemma (in comm_monoid_cancel) multlist_ee_cong:
  assumes "essentially_equal G fs fs'"
    and "set fs \<subseteq> carrier G" and "set fs' \<subseteq> carrier G"
  shows "foldr (op \<otimes>) fs \<one> \<sim> foldr (op \<otimes>) fs' \<one>"
using assms
apply (elim essentially_equalE)
apply (simp add: multlist_perm_cong multlist_listassoc_cong perm_closed)
done


subsubsection {* Factorization in irreducible elements *}

lemma wfactorsI:
  fixes G (structure)
  assumes "\<forall>f\<in>set fs. irreducible G f"
    and "foldr (op \<otimes>) fs \<one> \<sim> a"
  shows "wfactors G fs a"
using assms
unfolding wfactors_def
by simp

lemma wfactorsE:
  fixes G (structure)
  assumes wf: "wfactors G fs a"
    and e: "\<lbrakk>\<forall>f\<in>set fs. irreducible G f; foldr (op \<otimes>) fs \<one> \<sim> a\<rbrakk> \<Longrightarrow> P"
  shows "P"
using wf
unfolding wfactors_def
by (fast dest: e)

lemma (in monoid) factorsI:
  assumes "\<forall>f\<in>set fs. irreducible G f"
    and "foldr (op \<otimes>) fs \<one> = a"
  shows "factors G fs a"
using assms
unfolding factors_def
by simp

lemma factorsE:
  fixes G (structure)
  assumes f: "factors G fs a"
    and e: "\<lbrakk>\<forall>f\<in>set fs. irreducible G f; foldr (op \<otimes>) fs \<one> = a\<rbrakk> \<Longrightarrow> P"
  shows "P"
using f
unfolding factors_def
by (simp add: e)

lemma (in monoid) factors_wfactors:
  assumes "factors G as a" and "set as \<subseteq> carrier G"
  shows "wfactors G as a"
using assms
by (blast elim: factorsE intro: wfactorsI)

lemma (in monoid) wfactors_factors:
  assumes "wfactors G as a" and "set as \<subseteq> carrier G"
  shows "\<exists>a'. factors G as a' \<and> a' \<sim> a"
using assms
by (blast elim: wfactorsE intro: factorsI)

lemma (in monoid) factors_closed [dest]:
  assumes "factors G fs a" and "set fs \<subseteq> carrier G"
  shows "a \<in> carrier G"
using assms
by (elim factorsE, clarsimp)

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
using aunit
by (intro wfactorsI) (simp, simp add: Units_assoc)

lemma (in comm_monoid_cancel) unit_wfactors_empty:
  assumes aunit: "a \<in> Units G"
    and wf: "wfactors G fs a"
    and carr[simp]: "set fs \<subseteq> carrier G"
  shows "fs = []"
proof (rule ccontr, cases fs, simp)
  fix f fs'
  assume fs: "fs = f # fs'"

  from carr
      have fcarr[simp]: "f \<in> carrier G"
      and carr'[simp]: "set fs' \<subseteq> carrier G"
      by (simp add: fs)+

  from fs wf
      have "irreducible G f" by (simp add: wfactors_def)
  hence fnunit: "f \<notin> Units G" by (fast elim: irreducibleE)

  from fs wf
      have a: "f \<otimes> foldr (op \<otimes>) fs' \<one> \<sim> a" by (simp add: wfactors_def)

  note aunit
  also from fs wf
       have a: "f \<otimes> foldr (op \<otimes>) fs' \<one> \<sim> a" by (simp add: wfactors_def)
       have "a \<sim> f \<otimes> foldr (op \<otimes>) fs' \<one>" 
       by (simp add: Units_closed[OF aunit] a[symmetric])
  finally
       have "f \<otimes> foldr (op \<otimes>) fs' \<one> \<in> Units G" by simp
  hence "f \<in> Units G" by (intro unit_factor[of f], simp+)

  with fnunit show "False" by simp
qed


text {* Comparing wfactors *}

lemma (in comm_monoid_cancel) wfactors_listassoc_cong_l:
  assumes fact: "wfactors G fs a"
    and asc: "fs [\<sim>] fs'"
    and carr: "a \<in> carrier G"  "set fs \<subseteq> carrier G"  "set fs' \<subseteq> carrier G"
  shows "wfactors G fs' a"
using fact
apply (elim wfactorsE, intro wfactorsI)
apply (metis assms(2) assms(4) assms(5) irrlist_listassoc_cong)
proof -
  from asc[symmetric]
       have "foldr op \<otimes> fs' \<one> \<sim> foldr op \<otimes> fs \<one>" 
       by (simp add: multlist_listassoc_cong carr)
  also assume "foldr op \<otimes> fs \<one> \<sim> a"
  finally
       show "foldr op \<otimes> fs' \<one> \<sim> a" by (simp add: carr)
qed

lemma (in comm_monoid) wfactors_perm_cong_l:
  assumes "wfactors G fs a"
    and "fs <~~> fs'"
    and "set fs \<subseteq> carrier G"
  shows "wfactors G fs' a"
using assms
apply (elim wfactorsE, intro wfactorsI)
 apply (rule irrlist_perm_cong, assumption+)
apply (simp add: multlist_perm_cong[symmetric])
done

lemma (in comm_monoid_cancel) wfactors_ee_cong_l [trans]:
  assumes ee: "essentially_equal G as bs"
    and bfs: "wfactors G bs b"
    and carr: "b \<in> carrier G"  "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"
  shows "wfactors G as b"
using ee
proof (elim essentially_equalE)
  fix fs
  assume prm: "as <~~> fs"
  with carr
       have fscarr: "set fs \<subseteq> carrier G" by (simp add: perm_closed)

  note bfs
  also assume [symmetric]: "fs [\<sim>] bs"
  also (wfactors_listassoc_cong_l)
       note prm[symmetric]
  finally (wfactors_perm_cong_l)
       show "wfactors G as b" by (simp add: carr fscarr)
qed

lemma (in monoid) wfactors_cong_r [trans]:
  assumes fac: "wfactors G fs a" and aa': "a \<sim> a'"
    and carr[simp]: "a \<in> carrier G"  "a' \<in> carrier G"  "set fs \<subseteq> carrier G"
  shows "wfactors G fs a'"
using fac
proof (elim wfactorsE, intro wfactorsI)
  assume "foldr op \<otimes> fs \<one> \<sim> a" also note aa'
  finally show "foldr op \<otimes> fs \<one> \<sim> a'" by simp
qed


subsubsection {* Essentially equal factorizations *}

lemma (in comm_monoid_cancel) unitfactor_ee:
  assumes uunit: "u \<in> Units G"
    and carr: "set as \<subseteq> carrier G"
  shows "essentially_equal G (as[0 := (as!0 \<otimes> u)]) as" (is "essentially_equal G ?as' as")
using assms
apply (intro essentially_equalI[of _ ?as'], simp)
apply (cases as, simp)
apply (clarsimp, fast intro: associatedI2[of u])
done

lemma (in comm_monoid_cancel) factors_cong_unit:
  assumes uunit: "u \<in> Units G" and anunit: "a \<notin> Units G"
    and afs: "factors G as a"
    and ascarr: "set as \<subseteq> carrier G"
  shows "factors G (as[0 := (as!0 \<otimes> u)]) (a \<otimes> u)" (is "factors G ?as' ?a'")
using assms
apply (elim factorsE, clarify)
apply (cases as)
 apply (simp add: nunit_factors)
apply clarsimp
apply (elim factorsE, intro factorsI)
 apply (clarsimp, fast intro: irreducible_prod_rI)
apply (simp add: m_ac Units_closed)
done

lemma (in comm_monoid) perm_wfactorsD:
  assumes prm: "as <~~> bs"
    and afs: "wfactors G as a" and bfs: "wfactors G bs b"
    and [simp]: "a \<in> carrier G"  "b \<in> carrier G"
    and ascarr[simp]: "set as \<subseteq> carrier G"
  shows "a \<sim> b"
using afs bfs
proof (elim wfactorsE)
  from prm have [simp]: "set bs \<subseteq> carrier G" by (simp add: perm_closed)
  assume "foldr op \<otimes> as \<one> \<sim> a"
  hence "a \<sim> foldr op \<otimes> as \<one>" by (rule associated_sym, simp+)
  also from prm
       have "foldr op \<otimes> as \<one> = foldr op \<otimes> bs \<one>" by (rule multlist_perm_cong, simp)
  also assume "foldr op \<otimes> bs \<one> \<sim> b"
  finally
       show "a \<sim> b" by simp
qed

lemma (in comm_monoid_cancel) listassoc_wfactorsD:
  assumes assoc: "as [\<sim>] bs"
    and afs: "wfactors G as a" and bfs: "wfactors G bs b"
    and [simp]: "a \<in> carrier G"  "b \<in> carrier G"
    and [simp]: "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"
  shows "a \<sim> b"
using afs bfs
proof (elim wfactorsE)
  assume "foldr op \<otimes> as \<one> \<sim> a"
  hence "a \<sim> foldr op \<otimes> as \<one>" by (rule associated_sym, simp+)
  also from assoc
       have "foldr op \<otimes> as \<one> \<sim> foldr op \<otimes> bs \<one>" by (rule multlist_listassoc_cong, simp+)
  also assume "foldr op \<otimes> bs \<one> \<sim> b"
  finally
       show "a \<sim> b" by simp
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
  hence as'carr[simp]: "set fs \<subseteq> carrier G" by (simp add: perm_closed)
  from afs prm
      have afs': "wfactors G fs a" by (rule wfactors_perm_cong_l, simp)
  assume "fs [\<sim>] bs"
  from this afs' bfs
      show "a \<sim> b" by (rule listassoc_wfactorsD, simp+)
qed

lemma (in comm_monoid_cancel) ee_factorsD:
  assumes ee: "essentially_equal G as bs"
    and afs: "factors G as a" and bfs:"factors G bs b"
    and "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"
  shows "a \<sim> b"
using assms
by (blast intro: factors_wfactors dest: ee_wfactorsD)

lemma (in factorial_monoid) ee_factorsI:
  assumes ab: "a \<sim> b"
    and afs: "factors G as a" and anunit: "a \<notin> Units G"
    and bfs: "factors G bs b" and bnunit: "b \<notin> Units G"
    and ascarr: "set as \<subseteq> carrier G" and bscarr: "set bs \<subseteq> carrier G"
  shows "essentially_equal G as bs"
proof -
  note carr[simp] = factors_closed[OF afs ascarr] ascarr[THEN subsetD]
                    factors_closed[OF bfs bscarr] bscarr[THEN subsetD]

  from ab carr
      have "\<exists>u\<in>Units G. a = b \<otimes> u" by (fast elim: associatedE2)
  from this obtain u
      where uunit: "u \<in> Units G"
      and a: "a = b \<otimes> u" by auto

  from uunit bscarr
      have ee: "essentially_equal G (bs[0 := (bs!0 \<otimes> u)]) bs" 
                (is "essentially_equal G ?bs' bs")
      by (rule unitfactor_ee)

  from bscarr uunit
      have bs'carr: "set ?bs' \<subseteq> carrier G"
      by (cases bs) (simp add: Units_closed)+

  from uunit bnunit bfs bscarr
      have fac: "factors G ?bs' (b \<otimes> u)"
      by (rule factors_cong_unit)

  from afs fac[simplified a[symmetric]] ascarr bs'carr anunit
       have "essentially_equal G as ?bs'"
       by (blast intro: factors_unique)
  also note ee
  finally
      show "essentially_equal G as bs" by (simp add: ascarr bscarr bs'carr)
qed

lemma (in factorial_monoid) ee_wfactorsI:
  assumes asc: "a \<sim> b"
    and asf: "wfactors G as a" and bsf: "wfactors G bs b"
    and acarr[simp]: "a \<in> carrier G" and bcarr[simp]: "b \<in> carrier G"
    and ascarr[simp]: "set as \<subseteq> carrier G" and bscarr[simp]: "set bs \<subseteq> carrier G"
  shows "essentially_equal G as bs"
using assms
proof (cases "a \<in> Units G")
  assume aunit: "a \<in> Units G"
  also note asc
  finally have bunit: "b \<in> Units G" by simp

  from aunit asf ascarr
      have e: "as = []" by (rule unit_wfactors_empty)
  from bunit bsf bscarr
      have e': "bs = []" by (rule unit_wfactors_empty)

  have "essentially_equal G [] []"
      by (fast intro: essentially_equalI)
  thus ?thesis by (simp add: e e')
next
  assume anunit: "a \<notin> Units G"
  have bnunit: "b \<notin> Units G"
  proof clarify
    assume "b \<in> Units G"
    also note asc[symmetric]
    finally have "a \<in> Units G" by simp
    with anunit
         show "False" ..
  qed

  have "\<exists>a'. factors G as a' \<and> a' \<sim> a" by (rule wfactors_factors[OF asf ascarr])
  from this obtain a'
      where fa': "factors G as a'"
      and a': "a' \<sim> a"
      by auto
  from fa' ascarr
      have a'carr[simp]: "a' \<in> carrier G" by fast

  have a'nunit: "a' \<notin> Units G"
  proof (clarify)
    assume "a' \<in> Units G"
    also note a'
    finally have "a \<in> Units G" by simp
    with anunit
         show "False" ..
  qed

  have "\<exists>b'. factors G bs b' \<and> b' \<sim> b" by (rule wfactors_factors[OF bsf bscarr])
  from this obtain b'
      where fb': "factors G bs b'"
      and b': "b' \<sim> b"
      by auto
  from fb' bscarr
      have b'carr[simp]: "b' \<in> carrier G" by fast

  have b'nunit: "b' \<notin> Units G"
  proof (clarify)
    assume "b' \<in> Units G"
    also note b'
    finally have "b \<in> Units G" by simp
    with bnunit
        show "False" ..
  qed

  note a'
  also note asc
  also note b'[symmetric]
  finally
       have "a' \<sim> b'" by simp

  from this fa' a'nunit fb' b'nunit ascarr bscarr
  show "essentially_equal G as bs"
      by (rule ee_factorsI)
qed

lemma (in factorial_monoid) ee_wfactors:
  assumes asf: "wfactors G as a"
    and bsf: "wfactors G bs b"
    and acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G"
    and ascarr: "set as \<subseteq> carrier G" and bscarr: "set bs \<subseteq> carrier G"
  shows asc: "a \<sim> b = essentially_equal G as bs"
using assms
by (fast intro: ee_wfactorsI ee_wfactorsD)

lemma (in factorial_monoid) wfactors_exist [intro, simp]:
  assumes acarr[simp]: "a \<in> carrier G"
  shows "\<exists>fs. set fs \<subseteq> carrier G \<and> wfactors G fs a"
proof (cases "a \<in> Units G")
  assume "a \<in> Units G"
  hence "wfactors G [] a" by (rule unit_wfactors)
  thus ?thesis by (intro exI) force
next
  assume "a \<notin> Units G"
  hence "\<exists>fs. set fs \<subseteq> carrier G \<and> factors G fs a" by (intro factors_exist acarr)
  from this obtain fs
      where fscarr: "set fs \<subseteq> carrier G"
      and f: "factors G fs a"
      by auto
  from f have "wfactors G fs a" by (rule factors_wfactors) fact
  from fscarr this
      show ?thesis by fast
qed

lemma (in monoid) wfactors_prod_exists [intro, simp]:
  assumes "\<forall>a \<in> set as. irreducible G a" and "set as \<subseteq> carrier G"
  shows "\<exists>a. a \<in> carrier G \<and> wfactors G as a"
unfolding wfactors_def
using assms
by blast

lemma (in factorial_monoid) wfactors_unique:
  assumes "wfactors G fs a" and "wfactors G fs' a"
    and "a \<in> carrier G"
    and "set fs \<subseteq> carrier G" and "set fs' \<subseteq> carrier G"
  shows "essentially_equal G fs fs'"
using assms
by (fast intro: ee_wfactorsI[of a a])

lemma (in monoid) factors_mult_single:
  assumes "irreducible G a" and "factors G fb b" and "a \<in> carrier G"
  shows "factors G (a # fb) (a \<otimes> b)"
using assms
unfolding factors_def
by simp

lemma (in monoid_cancel) wfactors_mult_single:
  assumes f: "irreducible G a"  "wfactors G fb b"
        "a \<in> carrier G"  "b \<in> carrier G"  "set fb \<subseteq> carrier G"
  shows "wfactors G (a # fb) (a \<otimes> b)"
using assms
unfolding wfactors_def
by (simp add: mult_cong_r)

lemma (in monoid) factors_mult:
  assumes factors: "factors G fa a"  "factors G fb b"
    and ascarr: "set fa \<subseteq> carrier G" and bscarr:"set fb \<subseteq> carrier G"
  shows "factors G (fa @ fb) (a \<otimes> b)"
using assms
unfolding factors_def
apply (safe, force)
apply (induct fa)
 apply simp
apply (simp add: m_assoc)
done

lemma (in comm_monoid_cancel) wfactors_mult [intro]:
  assumes asf: "wfactors G as a" and bsf:"wfactors G bs b"
    and acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G"
    and ascarr: "set as \<subseteq> carrier G" and bscarr:"set bs \<subseteq> carrier G"
  shows "wfactors G (as @ bs) (a \<otimes> b)"
apply (insert wfactors_factors[OF asf ascarr])
apply (insert wfactors_factors[OF bsf bscarr])
proof (clarsimp)
  fix a' b'
  assume asf': "factors G as a'" and a'a: "a' \<sim> a"
     and bsf': "factors G bs b'" and b'b: "b' \<sim> b"
  from asf' have a'carr: "a' \<in> carrier G" by (rule factors_closed) fact
  from bsf' have b'carr: "b' \<in> carrier G" by (rule factors_closed) fact

  note carr = acarr bcarr a'carr b'carr ascarr bscarr

  from asf' bsf'
      have "factors G (as @ bs) (a' \<otimes> b')" by (rule factors_mult) fact+

  with carr
       have abf': "wfactors G (as @ bs) (a' \<otimes> b')" by (intro factors_wfactors) simp+
  also from b'b carr
       have trb: "a' \<otimes> b' \<sim> a' \<otimes> b" by (intro mult_cong_r)
  also from a'a carr
       have tra: "a' \<otimes> b \<sim> a \<otimes> b" by (intro mult_cong_l)
  finally
       show "wfactors G (as @ bs) (a \<otimes> b)"
       by (simp add: carr)
qed

lemma (in comm_monoid) factors_dividesI:
  assumes "factors G fs a" and "f \<in> set fs"
    and "set fs \<subseteq> carrier G"
  shows "f divides a"
using assms
by (fast elim: factorsE intro: multlist_dividesI)

lemma (in comm_monoid) wfactors_dividesI:
  assumes p: "wfactors G fs a"
    and fscarr: "set fs \<subseteq> carrier G" and acarr: "a \<in> carrier G"
    and f: "f \<in> set fs"
  shows "f divides a"
apply (insert wfactors_factors[OF p fscarr], clarsimp)
proof -
  fix a'
  assume fsa': "factors G fs a'"
    and a'a: "a' \<sim> a"
  with fscarr
      have a'carr: "a' \<in> carrier G" by (simp add: factors_closed)

  from fsa' fscarr f
       have "f divides a'" by (fast intro: factors_dividesI)
  also note a'a
  finally
       show "f divides a" by (simp add: f fscarr[THEN subsetD] acarr a'carr)
qed


subsubsection {* Factorial monoids and wfactors *}

lemma (in comm_monoid_cancel) factorial_monoidI:
  assumes wfactors_exists: 
          "\<And>a. a \<in> carrier G \<Longrightarrow> \<exists>fs. set fs \<subseteq> carrier G \<and> wfactors G fs a"
      and wfactors_unique: 
          "\<And>a fs fs'. \<lbrakk>a \<in> carrier G; set fs \<subseteq> carrier G; set fs' \<subseteq> carrier G; 
                       wfactors G fs a; wfactors G fs' a\<rbrakk> \<Longrightarrow> essentially_equal G fs fs'"
  shows "factorial_monoid G"
proof
  fix a
  assume acarr: "a \<in> carrier G" and anunit: "a \<notin> Units G"

  from wfactors_exists[OF acarr]
  obtain as
      where ascarr: "set as \<subseteq> carrier G"
      and afs: "wfactors G as a"
      by auto
  from afs ascarr
      have "\<exists>a'. factors G as a' \<and> a' \<sim> a" by (rule wfactors_factors)
  from this obtain a'
      where afs': "factors G as a'"
      and a'a: "a' \<sim> a"
      by auto
  from afs' ascarr
      have a'carr: "a' \<in> carrier G" by fast
  have a'nunit: "a' \<notin> Units G"
  proof clarify
    assume "a' \<in> Units G"
    also note a'a
    finally have "a \<in> Units G" by (simp add: acarr)
    with anunit
        show "False" ..
  qed

  from a'carr acarr a'a
      have "\<exists>u. u \<in> Units G \<and> a' = a \<otimes> u" by (blast elim: associatedE2)
  from this obtain  u
      where uunit: "u \<in> Units G"
      and a': "a' = a \<otimes> u"
      by auto

  note [simp] = acarr Units_closed[OF uunit] Units_inv_closed[OF uunit]

  have "a = a \<otimes> \<one>" by simp
  also have "\<dots> = a \<otimes> (u \<otimes> inv u)" by (simp add: Units_r_inv uunit)
  also have "\<dots> = a' \<otimes> inv u" by (simp add: m_assoc[symmetric] a'[symmetric])
  finally
       have a: "a = a' \<otimes> inv u" .

  from ascarr uunit
      have cr: "set (as[0:=(as!0 \<otimes> inv u)]) \<subseteq> carrier G"
      by (cases as, clarsimp+)

  from afs' uunit a'nunit acarr ascarr
      have "factors G (as[0:=(as!0 \<otimes> inv u)]) a"
      by (simp add: a factors_cong_unit)

  with cr
      show "\<exists>fs. set fs \<subseteq> carrier G \<and> factors G fs a" by fast
qed (blast intro: factors_wfactors wfactors_unique)


subsection {* Factorizations as Multisets *}

text {* Gives useful operations like intersection *}

(* FIXME: use class_of x instead of closure_of {x} *)

abbreviation
  "assocs G x == eq_closure_of (division_rel G) {x}"

definition
  "fmset G as = multiset_of (map (\<lambda>a. assocs G a) as)"


text {* Helper lemmas *}

lemma (in monoid) assocs_repr_independence:
  assumes "y \<in> assocs G x"
    and "x \<in> carrier G"
  shows "assocs G x = assocs G y"
using assms
apply safe
 apply (elim closure_ofE2, intro closure_ofI2[of _ _ y])
   apply (clarsimp, iprover intro: associated_trans associated_sym, simp+)
apply (elim closure_ofE2, intro closure_ofI2[of _ _ x])
  apply (clarsimp, iprover intro: associated_trans, simp+)
done

lemma (in monoid) assocs_self:
  assumes "x \<in> carrier G"
  shows "x \<in> assocs G x"
using assms
by (fastforce intro: closure_ofI2)

lemma (in monoid) assocs_repr_independenceD:
  assumes repr: "assocs G x = assocs G y"
    and ycarr: "y \<in> carrier G"
  shows "y \<in> assocs G x"
unfolding repr
using ycarr
by (intro assocs_self)

lemma (in comm_monoid) assocs_assoc:
  assumes "a \<in> assocs G b"
    and "b \<in> carrier G"
  shows "a \<sim> b"
using assms
by (elim closure_ofE2, simp)

lemmas (in comm_monoid) assocs_eqD =
    assocs_repr_independenceD[THEN assocs_assoc]


subsubsection {* Comparing multisets *}

lemma (in monoid) fmset_perm_cong:
  assumes prm: "as <~~> bs"
  shows "fmset G as = fmset G bs"
using perm_map[OF prm]
by (simp add: multiset_of_eq_perm fmset_def)

lemma (in comm_monoid_cancel) eqc_listassoc_cong:
  assumes "as [\<sim>] bs"
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "map (assocs G) as = map (assocs G) bs"
using assms
apply (induct as arbitrary: bs, simp)
apply (clarsimp simp add: Cons_eq_map_conv list_all2_Cons1, safe)
 apply (clarsimp elim!: closure_ofE2) defer 1
 apply (clarsimp elim!: closure_ofE2) defer 1
proof -
  fix a x z
  assume carr[simp]: "a \<in> carrier G"  "x \<in> carrier G"  "z \<in> carrier G"
  assume "x \<sim> a"
  also assume "a \<sim> z"
  finally have "x \<sim> z" by simp
  with carr
      show "x \<in> assocs G z"
      by (intro closure_ofI2) simp+
next
  fix a x z
  assume carr[simp]: "a \<in> carrier G"  "x \<in> carrier G"  "z \<in> carrier G"
  assume "x \<sim> z"
  also assume [symmetric]: "a \<sim> z"
  finally have "x \<sim> a" by simp
  with carr
      show "x \<in> assocs G a"
      by (intro closure_ofI2) simp+
qed

lemma (in comm_monoid_cancel) fmset_listassoc_cong:
  assumes "as [\<sim>] bs" 
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "fmset G as = fmset G bs"
using assms
unfolding fmset_def
by (simp add: eqc_listassoc_cong)

lemma (in comm_monoid_cancel) ee_fmset:
  assumes ee: "essentially_equal G as bs" 
    and ascarr: "set as \<subseteq> carrier G" and bscarr: "set bs \<subseteq> carrier G"
  shows "fmset G as = fmset G bs"
using ee
proof (elim essentially_equalE)
  fix as'
  assume prm: "as <~~> as'"
  from prm ascarr
      have as'carr: "set as' \<subseteq> carrier G" by (rule perm_closed)

  from prm
       have "fmset G as = fmset G as'" by (rule fmset_perm_cong)
  also assume "as' [\<sim>] bs"
       with as'carr bscarr
       have "fmset G as' = fmset G bs" by (simp add: fmset_listassoc_cong)
  finally
       show "fmset G as = fmset G bs" .
qed

lemma (in monoid_cancel) fmset_ee__hlp_induct:
  assumes prm: "cas <~~> cbs"
    and cdef: "cas = map (assocs G) as"  "cbs = map (assocs G) bs"
  shows "\<forall>as bs. (cas <~~> cbs \<and> cas = map (assocs G) as \<and> 
                 cbs = map (assocs G) bs) \<longrightarrow> (\<exists>as'. as <~~> as' \<and> map (assocs G) as' = cbs)"
apply (rule perm.induct[of cas cbs], rule prm)
apply safe apply simp_all
  apply (simp add: map_eq_Cons_conv, blast)
 apply force
proof -
  fix ys as bs
  assume p1: "map (assocs G) as <~~> ys"
    and r1[rule_format]:
        "\<forall>asa bs. map (assocs G) as = map (assocs G) asa \<and>
                  ys = map (assocs G) bs
                  \<longrightarrow> (\<exists>as'. asa <~~> as' \<and> map (assocs G) as' = map (assocs G) bs)"
    and p2: "ys <~~> map (assocs G) bs"
    and r2[rule_format]:
        "\<forall>as bsa. ys = map (assocs G) as \<and>
                  map (assocs G) bs = map (assocs G) bsa
                  \<longrightarrow> (\<exists>as'. as <~~> as' \<and> map (assocs G) as' = map (assocs G) bsa)"
    and p3: "map (assocs G) as <~~> map (assocs G) bs"

  from p1
      have "multiset_of (map (assocs G) as) = multiset_of ys"
      by (simp add: multiset_of_eq_perm)
  hence setys: "set (map (assocs G) as) = set ys" by (rule multiset_of_eq_setD)

  have "set (map (assocs G) as) = { assocs G x | x. x \<in> set as}" by clarsimp fast
  with setys have "set ys \<subseteq> { assocs G x | x. x \<in> set as}" by simp
  hence "\<exists>yy. ys = map (assocs G) yy"
    apply (induct ys, simp, clarsimp)
  proof -
    fix yy x
    show "\<exists>yya. (assocs G x) # map (assocs G) yy =
                map (assocs G) yya"
    by (rule exI[of _ "x#yy"], simp)
  qed
  from this obtain yy
      where ys: "ys = map (assocs G) yy"
      by auto

  from p1 ys
      have "\<exists>as'. as <~~> as' \<and> map (assocs G) as' = map (assocs G) yy"
      by (intro r1, simp)
  from this obtain as'
      where asas': "as <~~> as'"
      and as'yy: "map (assocs G) as' = map (assocs G) yy"
      by auto

  from p2 ys
      have "\<exists>as'. yy <~~> as' \<and> map (assocs G) as' = map (assocs G) bs"
      by (intro r2, simp)
  from this obtain as''
      where yyas'': "yy <~~> as''"
      and as''bs: "map (assocs G) as'' = map (assocs G) bs"
      by auto

  from as'yy and yyas''
      have "\<exists>cs. as' <~~> cs \<and> map (assocs G) cs = map (assocs G) as''"
      by (rule perm_map_switch)
  from this obtain cs
      where as'cs: "as' <~~> cs"
      and csas'': "map (assocs G) cs = map (assocs G) as''"
      by auto

  from asas' and as'cs
      have ascs: "as <~~> cs" by fast
  from csas'' and as''bs
      have "map (assocs G) cs = map (assocs G) bs" by simp
  from ascs and this
  show "\<exists>as'. as <~~> as' \<and> map (assocs G) as' = map (assocs G) bs" by fast
qed

lemma (in comm_monoid_cancel) fmset_ee:
  assumes mset: "fmset G as = fmset G bs"
    and ascarr: "set as \<subseteq> carrier G" and bscarr: "set bs \<subseteq> carrier G"
  shows "essentially_equal G as bs"
proof -
  from mset
      have mpp: "map (assocs G) as <~~> map (assocs G) bs"
      by (simp add: fmset_def multiset_of_eq_perm)

  have "\<exists>cas. cas = map (assocs G) as" by simp
  from this obtain cas where cas: "cas = map (assocs G) as" by simp

  have "\<exists>cbs. cbs = map (assocs G) bs" by simp
  from this obtain cbs where cbs: "cbs = map (assocs G) bs" by simp

  from cas cbs mpp
      have [rule_format]:
           "\<forall>as bs. (cas <~~> cbs \<and> cas = map (assocs G) as \<and> 
                     cbs = map (assocs G) bs) 
                     \<longrightarrow> (\<exists>as'. as <~~> as' \<and> map (assocs G) as' = cbs)"
      by (intro fmset_ee__hlp_induct, simp+)
  with mpp cas cbs
      have "\<exists>as'. as <~~> as' \<and> map (assocs G) as' = map (assocs G) bs"
      by simp

  from this obtain as'
      where tp: "as <~~> as'"
      and tm: "map (assocs G) as' = map (assocs G) bs"
      by auto
  from tm have lene: "length as' = length bs" by (rule map_eq_imp_length_eq)
  from tp have "set as = set as'" by (simp add: multiset_of_eq_perm multiset_of_eq_setD)
  with ascarr
      have as'carr: "set as' \<subseteq> carrier G" by simp

  from tm as'carr[THEN subsetD] bscarr[THEN subsetD]
  have "as' [\<sim>] bs"
    by (induct as' arbitrary: bs) (simp, fastforce dest: assocs_eqD[THEN associated_sym])

  from tp and this
    show "essentially_equal G as bs" by (fast intro: essentially_equalI)
qed

lemma (in comm_monoid_cancel) ee_is_fmset:
  assumes "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "essentially_equal G as bs = (fmset G as = fmset G bs)"
using assms
by (fast intro: ee_fmset fmset_ee)


subsubsection {* Interpreting multisets as factorizations *}

lemma (in monoid) mset_fmsetEx:
  assumes elems: "\<And>X. X \<in> set_of Cs \<Longrightarrow> \<exists>x. P x \<and> X = assocs G x"
  shows "\<exists>cs. (\<forall>c \<in> set cs. P c) \<and> fmset G cs = Cs"
proof -
  have "\<exists>Cs'. Cs = multiset_of Cs'"
      by (rule surjE[OF surj_multiset_of], fast)
  from this obtain Cs'
      where Cs: "Cs = multiset_of Cs'"
      by auto

  have "\<exists>cs. (\<forall>c \<in> set cs. P c) \<and> multiset_of (map (assocs G) cs) = Cs"
  using elems
  unfolding Cs
    apply (induct Cs', simp)
    apply clarsimp
    apply (subgoal_tac "\<exists>cs. (\<forall>x\<in>set cs. P x) \<and> 
                             multiset_of (map (assocs G) cs) = multiset_of Cs'")
  proof clarsimp
    fix a Cs' cs 
    assume ih: "\<And>X. X = a \<or> X \<in> set Cs' \<Longrightarrow> \<exists>x. P x \<and> X = assocs G x"
      and csP: "\<forall>x\<in>set cs. P x"
      and mset: "multiset_of (map (assocs G) cs) = multiset_of Cs'"
    from ih
        have "\<exists>x. P x \<and> a = assocs G x" by fast
    from this obtain c
        where cP: "P c"
        and a: "a = assocs G c"
        by auto
    from cP csP
        have tP: "\<forall>x\<in>set (c#cs). P x" by simp
    from mset a
    have "multiset_of (map (assocs G) (c#cs)) = multiset_of Cs' + {#a#}" by simp
    from tP this
    show "\<exists>cs. (\<forall>x\<in>set cs. P x) \<and>
               multiset_of (map (assocs G) cs) =
               multiset_of Cs' + {#a#}" by fast
  qed simp
  thus ?thesis by (simp add: fmset_def)
qed

lemma (in monoid) mset_wfactorsEx:
  assumes elems: "\<And>X. X \<in> set_of Cs 
                      \<Longrightarrow> \<exists>x. (x \<in> carrier G \<and> irreducible G x) \<and> X = assocs G x"
  shows "\<exists>c cs. c \<in> carrier G \<and> set cs \<subseteq> carrier G \<and> wfactors G cs c \<and> fmset G cs = Cs"
proof -
  have "\<exists>cs. (\<forall>c\<in>set cs. c \<in> carrier G \<and> irreducible G c) \<and> fmset G cs = Cs"
      by (intro mset_fmsetEx, rule elems)
  from this obtain cs
      where p[rule_format]: "\<forall>c\<in>set cs. c \<in> carrier G \<and> irreducible G c"
      and Cs[symmetric]: "fmset G cs = Cs"
      by auto

  from p
      have cscarr: "set cs \<subseteq> carrier G" by fast

  from p
      have "\<exists>c. c \<in> carrier G \<and> wfactors G cs c"
      by (intro wfactors_prod_exists) fast+
  from this obtain c
      where ccarr: "c \<in> carrier G"
      and cfs: "wfactors G cs c"
      by auto

  with cscarr Cs
      show ?thesis by fast
qed


subsubsection {* Multiplication on multisets *}

lemma (in factorial_monoid) mult_wfactors_fmset:
  assumes afs: "wfactors G as a" and bfs: "wfactors G bs b" and cfs: "wfactors G cs (a \<otimes> b)"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"
              "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"  "set cs \<subseteq> carrier G"
  shows "fmset G cs = fmset G as + fmset G bs"
proof -
  from assms
       have "wfactors G (as @ bs) (a \<otimes> b)" by (intro wfactors_mult)
  with carr cfs
       have "essentially_equal G cs (as@bs)" by (intro ee_wfactorsI[of "a\<otimes>b" "a\<otimes>b"], simp+)
  with carr
       have "fmset G cs = fmset G (as@bs)" by (intro ee_fmset, simp+)
  also have "fmset G (as@bs) = fmset G as + fmset G bs" by (simp add: fmset_def)
  finally show "fmset G cs = fmset G as + fmset G bs" .
qed

lemma (in factorial_monoid) mult_factors_fmset:
  assumes afs: "factors G as a" and bfs: "factors G bs b" and cfs: "factors G cs (a \<otimes> b)"
    and "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"  "set cs \<subseteq> carrier G"
  shows "fmset G cs = fmset G as + fmset G bs"
using assms
by (blast intro: factors_wfactors mult_wfactors_fmset)

lemma (in comm_monoid_cancel) fmset_wfactors_mult:
  assumes mset: "fmset G cs = fmset G as + fmset G bs"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
          "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"  "set cs \<subseteq> carrier G"
    and fs: "wfactors G as a"  "wfactors G bs b"  "wfactors G cs c"
  shows "c \<sim> a \<otimes> b"
proof -
  from carr fs
       have m: "wfactors G (as @ bs) (a \<otimes> b)" by (intro wfactors_mult)

  from mset
       have "fmset G cs = fmset G (as@bs)" by (simp add: fmset_def)
  then have "essentially_equal G cs (as@bs)" by (rule fmset_ee) (simp add: carr)+
  then show "c \<sim> a \<otimes> b" by (rule ee_wfactorsD[of "cs" "as@bs"]) (simp add: assms m)+
qed


subsubsection {* Divisibility on multisets *}

lemma (in factorial_monoid) divides_fmsubset:
  assumes ab: "a divides b"
    and afs: "wfactors G as a" and bfs: "wfactors G bs b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"  "set as \<subseteq> carrier G"  "set bs \<subseteq> carrier G"
  shows "fmset G as \<le> fmset G bs"
using ab
proof (elim dividesE)
  fix c
  assume ccarr: "c \<in> carrier G"
  hence "\<exists>cs. set cs \<subseteq> carrier G \<and> wfactors G cs c" by (rule wfactors_exist)
  from this obtain cs 
      where cscarr: "set cs \<subseteq> carrier G"
      and cfs: "wfactors G cs c" by auto
  note carr = carr ccarr cscarr

  assume "b = a \<otimes> c"
  with afs bfs cfs carr
      have "fmset G bs = fmset G as + fmset G cs"
      by (intro mult_wfactors_fmset[OF afs cfs]) simp+

  thus ?thesis by simp
qed

lemma (in comm_monoid_cancel) fmsubset_divides:
  assumes msubset: "fmset G as \<le> fmset G bs"
    and afs: "wfactors G as a" and bfs: "wfactors G bs b"
    and acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G"
    and ascarr: "set as \<subseteq> carrier G" and bscarr: "set bs \<subseteq> carrier G"
  shows "a divides b"
proof -
  from afs have airr: "\<forall>a \<in> set as. irreducible G a" by (fast elim: wfactorsE)
  from bfs have birr: "\<forall>b \<in> set bs. irreducible G b" by (fast elim: wfactorsE)

  have "\<exists>c cs. c \<in> carrier G \<and> set cs \<subseteq> carrier G \<and> wfactors G cs c \<and> fmset G cs = fmset G bs - fmset G as"
  proof (intro mset_wfactorsEx, simp)
    fix X
    assume "count (fmset G as) X < count (fmset G bs) X"
    hence "0 < count (fmset G bs) X" by simp
    hence "X \<in> set_of (fmset G bs)" by simp
    hence "X \<in> set (map (assocs G) bs)" by (simp add: fmset_def)
    hence "\<exists>x. x \<in> set bs \<and> X = assocs G x" by (induct bs) auto
    from this obtain x
        where xbs: "x \<in> set bs"
        and X: "X = assocs G x"
        by auto

    with bscarr have xcarr: "x \<in> carrier G" by fast
    from xbs birr have xirr: "irreducible G x" by simp

    from xcarr and xirr and X
        show "\<exists>x. x \<in> carrier G \<and> irreducible G x \<and> X = assocs G x" by fast
  qed
  from this obtain c cs
      where ccarr: "c \<in> carrier G"
      and cscarr: "set cs \<subseteq> carrier G" 
      and csf: "wfactors G cs c"
      and csmset: "fmset G cs = fmset G bs - fmset G as" by auto

  from csmset msubset
      have "fmset G bs = fmset G as + fmset G cs"
      by (simp add: multiset_eq_iff mset_le_def)
  hence basc: "b \<sim> a \<otimes> c"
      by (rule fmset_wfactors_mult) fact+

  thus ?thesis
  proof (elim associatedE2)
    fix u
    assume "u \<in> Units G"  "b = a \<otimes> c \<otimes> u"
    with acarr ccarr
        show "a divides b" by (fast intro: dividesI[of "c \<otimes> u"] m_assoc)
  qed (simp add: acarr bcarr ccarr)+
qed

lemma (in factorial_monoid) divides_as_fmsubset:
  assumes "wfactors G as a" and "wfactors G bs b"
    and "a \<in> carrier G" and "b \<in> carrier G" 
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "a divides b = (fmset G as \<le> fmset G bs)"
using assms
by (blast intro: divides_fmsubset fmsubset_divides)


text {* Proper factors on multisets *}

lemma (in factorial_monoid) fmset_properfactor:
  assumes asubb: "fmset G as \<le> fmset G bs"
    and anb: "fmset G as \<noteq> fmset G bs"
    and "wfactors G as a" and "wfactors G bs b"
    and "a \<in> carrier G" and "b \<in> carrier G"
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "properfactor G a b"
apply (rule properfactorI)
apply (rule fmsubset_divides[of as bs], fact+)
proof
  assume "b divides a"
  hence "fmset G bs \<le> fmset G as"
      by (rule divides_fmsubset) fact+
  with asubb
      have "fmset G as = fmset G bs" by (rule order_antisym)
  with anb
      show "False" ..
qed

lemma (in factorial_monoid) properfactor_fmset:
  assumes pf: "properfactor G a b"
    and "wfactors G as a" and "wfactors G bs b"
    and "a \<in> carrier G" and "b \<in> carrier G"
    and "set as \<subseteq> carrier G" and "set bs \<subseteq> carrier G"
  shows "fmset G as \<le> fmset G bs \<and> fmset G as \<noteq> fmset G bs"
using pf
apply (elim properfactorE)
apply rule
 apply (intro divides_fmsubset, assumption)
  apply (rule assms)+
apply (metis assms divides_fmsubset fmsubset_divides)
done

subsection {* Irreducible Elements are Prime *}

lemma (in factorial_monoid) irreducible_is_prime:
  assumes pirr: "irreducible G p"
    and pcarr: "p \<in> carrier G"
  shows "prime G p"
using pirr
proof (elim irreducibleE, intro primeI)
  fix a b
  assume acarr: "a \<in> carrier G"  and bcarr: "b \<in> carrier G"
    and pdvdab: "p divides (a \<otimes> b)"
    and pnunit: "p \<notin> Units G"
  assume irreduc[rule_format]:
         "\<forall>b. b \<in> carrier G \<and> properfactor G b p \<longrightarrow> b \<in> Units G"
  from pdvdab
      have "\<exists>c\<in>carrier G. a \<otimes> b = p \<otimes> c" by (rule dividesD)
  from this obtain c
      where ccarr: "c \<in> carrier G"
      and abpc: "a \<otimes> b = p \<otimes> c"
      by auto

  from acarr have "\<exists>fs. set fs \<subseteq> carrier G \<and> wfactors G fs a" by (rule wfactors_exist)
  from this obtain as where ascarr: "set as \<subseteq> carrier G" and afs: "wfactors G as a" by auto

  from bcarr have "\<exists>fs. set fs \<subseteq> carrier G \<and> wfactors G fs b" by (rule wfactors_exist)
  from this obtain bs where bscarr: "set bs \<subseteq> carrier G" and bfs: "wfactors G bs b" by auto

  from ccarr have "\<exists>fs. set fs \<subseteq> carrier G \<and> wfactors G fs c" by (rule wfactors_exist)
  from this obtain cs where cscarr: "set cs \<subseteq> carrier G" and cfs: "wfactors G cs c" by auto

  note carr[simp] = pcarr acarr bcarr ccarr ascarr bscarr cscarr

  from afs and bfs
      have abfs: "wfactors G (as @ bs) (a \<otimes> b)" by (rule wfactors_mult) fact+

  from pirr cfs
      have pcfs: "wfactors G (p # cs) (p \<otimes> c)" by (rule wfactors_mult_single) fact+
  with abpc
      have abfs': "wfactors G (p # cs) (a \<otimes> b)" by simp

  from abfs' abfs
      have "essentially_equal G (p # cs) (as @ bs)"
      by (rule wfactors_unique) simp+

  hence "\<exists>ds. p # cs <~~> ds \<and> ds [\<sim>] (as @ bs)"
      by (fast elim: essentially_equalE)
  from this obtain ds
      where "p # cs <~~> ds"
      and dsassoc: "ds [\<sim>] (as @ bs)"
      by auto

  then have "p \<in> set ds"
       by (simp add: perm_set_eq[symmetric])
  with dsassoc
       have "\<exists>p'. p' \<in> set (as@bs) \<and> p \<sim> p'"
       unfolding list_all2_conv_all_nth set_conv_nth
       by force

  from this obtain p'
       where "p' \<in> set (as@bs)"
       and pp': "p \<sim> p'"
       by auto

  hence "p' \<in> set as \<or> p' \<in> set bs" by simp
  moreover
  {
    assume p'elem: "p' \<in> set as"
    with ascarr have [simp]: "p' \<in> carrier G" by fast

    note pp'
    also from afs
         have "p' divides a" by (rule wfactors_dividesI) fact+
    finally
         have "p divides a" by simp
  }
  moreover
  {
    assume p'elem: "p' \<in> set bs"
    with bscarr have [simp]: "p' \<in> carrier G" by fast

    note pp'
    also from bfs
         have "p' divides b" by (rule wfactors_dividesI) fact+
    finally
         have "p divides b" by simp
  }
  ultimately
      show "p divides a \<or> p divides b" by fast
qed


--"A version using @{const factors}, more complicated"
lemma (in factorial_monoid) factors_irreducible_is_prime:
  assumes pirr: "irreducible G p"
    and pcarr: "p \<in> carrier G"
  shows "prime G p"
using pirr
apply (elim irreducibleE, intro primeI)
 apply assumption
proof -
  fix a b
  assume acarr: "a \<in> carrier G" 
    and bcarr: "b \<in> carrier G"
    and pdvdab: "p divides (a \<otimes> b)"
  assume irreduc[rule_format]:
         "\<forall>b. b \<in> carrier G \<and> properfactor G b p \<longrightarrow> b \<in> Units G"
  from pdvdab
      have "\<exists>c\<in>carrier G. a \<otimes> b = p \<otimes> c" by (rule dividesD)
  from this obtain c
      where ccarr: "c \<in> carrier G"
      and abpc: "a \<otimes> b = p \<otimes> c"
      by auto
  note [simp] = pcarr acarr bcarr ccarr

  show "p divides a \<or> p divides b"
  proof (cases "a \<in> Units G")
    assume aunit: "a \<in> Units G"

    note pdvdab
    also have "a \<otimes> b = b \<otimes> a" by (simp add: m_comm)
    also from aunit
         have bab: "b \<otimes> a \<sim> b"
         by (intro associatedI2[of "a"], simp+)
    finally
         have "p divides b" by simp
    thus "p divides a \<or> p divides b" ..
  next
    assume anunit: "a \<notin> Units G"

    show "p divides a \<or> p divides b"
    proof (cases "b \<in> Units G")
      assume bunit: "b \<in> Units G"

      note pdvdab
      also from bunit
           have baa: "a \<otimes> b \<sim> a"
           by (intro associatedI2[of "b"], simp+)
      finally
           have "p divides a" by simp
      thus "p divides a \<or> p divides b" ..
    next
      assume bnunit: "b \<notin> Units G"

      have cnunit: "c \<notin> Units G"
      proof (rule ccontr, simp)
        assume cunit: "c \<in> Units G"
        from bnunit
             have "properfactor G a (a \<otimes> b)"
             by (intro properfactorI3[of _ _ b], simp+)
        also note abpc
        also from cunit
             have "p \<otimes> c \<sim> p"
             by (intro associatedI2[of c], simp+)
        finally
             have "properfactor G a p" by simp

        with acarr
             have "a \<in> Units G" by (fast intro: irreduc)
        with anunit
             show "False" ..
      qed

      have abnunit: "a \<otimes> b \<notin> Units G"
      proof clarsimp
        assume abunit: "a \<otimes> b \<in> Units G"
        hence "a \<in> Units G" by (rule unit_factor) fact+
        with anunit
             show "False" ..
      qed

      from acarr anunit have "\<exists>fs. set fs \<subseteq> carrier G \<and> factors G fs a" by (rule factors_exist)
      then obtain as where ascarr: "set as \<subseteq> carrier G" and afac: "factors G as a" by auto

      from bcarr bnunit have "\<exists>fs. set fs \<subseteq> carrier G \<and> factors G fs b" by (rule factors_exist)
      then obtain bs where bscarr: "set bs \<subseteq> carrier G" and bfac: "factors G bs b" by auto

      from ccarr cnunit have "\<exists>fs. set fs \<subseteq> carrier G \<and> factors G fs c" by (rule factors_exist)
      then obtain cs where cscarr: "set cs \<subseteq> carrier G" and cfac: "factors G cs c" by auto

      note [simp] = ascarr bscarr cscarr

      from afac and bfac
          have abfac: "factors G (as @ bs) (a \<otimes> b)" by (rule factors_mult) fact+

      from pirr cfac
          have pcfac: "factors G (p # cs) (p \<otimes> c)" by (rule factors_mult_single) fact+
      with abpc
          have abfac': "factors G (p # cs) (a \<otimes> b)" by simp

      from abfac' abfac
          have "essentially_equal G (p # cs) (as @ bs)"
          by (rule factors_unique) (fact | simp)+

      hence "\<exists>ds. p # cs <~~> ds \<and> ds [\<sim>] (as @ bs)"
          by (fast elim: essentially_equalE)
      from this obtain ds
          where "p # cs <~~> ds"
          and dsassoc: "ds [\<sim>] (as @ bs)"
          by auto

      then have "p \<in> set ds"
           by (simp add: perm_set_eq[symmetric])
      with dsassoc
           have "\<exists>p'. p' \<in> set (as@bs) \<and> p \<sim> p'"
           unfolding list_all2_conv_all_nth set_conv_nth
           by force

      from this obtain p'
          where "p' \<in> set (as@bs)"
          and pp': "p \<sim> p'" by auto

      hence "p' \<in> set as \<or> p' \<in> set bs" by simp
      moreover
      {
        assume p'elem: "p' \<in> set as"
        with ascarr have [simp]: "p' \<in> carrier G" by fast

        note pp'
        also from afac p'elem
             have "p' divides a" by (rule factors_dividesI) fact+
        finally
             have "p divides a" by simp
      }
      moreover
      {
        assume p'elem: "p' \<in> set bs"
        with bscarr have [simp]: "p' \<in> carrier G" by fast

        note pp'
        also from bfac
             have "p' divides b" by (rule factors_dividesI) fact+
        finally have "p divides b" by simp
      }
      ultimately
          show "p divides a \<or> p divides b" by fast
    qed
  qed
qed


subsection {* Greatest Common Divisors and Lowest Common Multiples *}

subsubsection {* Definitions *}

definition
  isgcd :: "[('a,_) monoid_scheme, 'a, 'a, 'a] \<Rightarrow> bool"  ("(_ gcdof\<index> _ _)" [81,81,81] 80)
  where "x gcdof\<^bsub>G\<^esub> a b \<longleftrightarrow> x divides\<^bsub>G\<^esub> a \<and> x divides\<^bsub>G\<^esub> b \<and>
    (\<forall>y\<in>carrier G. (y divides\<^bsub>G\<^esub> a \<and> y divides\<^bsub>G\<^esub> b \<longrightarrow> y divides\<^bsub>G\<^esub> x))"

definition
  islcm :: "[_, 'a, 'a, 'a] \<Rightarrow> bool"  ("(_ lcmof\<index> _ _)" [81,81,81] 80)
  where "x lcmof\<^bsub>G\<^esub> a b \<longleftrightarrow> a divides\<^bsub>G\<^esub> x \<and> b divides\<^bsub>G\<^esub> x \<and>
    (\<forall>y\<in>carrier G. (a divides\<^bsub>G\<^esub> y \<and> b divides\<^bsub>G\<^esub> y \<longrightarrow> x divides\<^bsub>G\<^esub> y))"

definition
  somegcd :: "('a,_) monoid_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "somegcd G a b = (SOME x. x \<in> carrier G \<and> x gcdof\<^bsub>G\<^esub> a b)"

definition
  somelcm :: "('a,_) monoid_scheme \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
  where "somelcm G a b = (SOME x. x \<in> carrier G \<and> x lcmof\<^bsub>G\<^esub> a b)"

definition
  "SomeGcd G A = inf (division_rel G) A"


locale gcd_condition_monoid = comm_monoid_cancel +
  assumes gcdof_exists:
          "\<lbrakk>a \<in> carrier G; b \<in> carrier G\<rbrakk> \<Longrightarrow> \<exists>c. c \<in> carrier G \<and> c gcdof a b"

locale primeness_condition_monoid = comm_monoid_cancel +
  assumes irreducible_prime:
          "\<lbrakk>a \<in> carrier G; irreducible G a\<rbrakk> \<Longrightarrow> prime G a"

locale divisor_chain_condition_monoid = comm_monoid_cancel +
  assumes division_wellfounded:
          "wf {(x, y). x \<in> carrier G \<and> y \<in> carrier G \<and> properfactor G x y}"


subsubsection {* Connections to \texttt{Lattice.thy} *}

lemma gcdof_greatestLower:
  fixes G (structure)
  assumes carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "(x \<in> carrier G \<and> x gcdof a b) =
         greatest (division_rel G) x (Lower (division_rel G) {a, b})"
unfolding isgcd_def greatest_def Lower_def elem_def
by auto

lemma lcmof_leastUpper:
  fixes G (structure)
  assumes carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"
  shows "(x \<in> carrier G \<and> x lcmof a b) =
         least (division_rel G) x (Upper (division_rel G) {a, b})"
unfolding islcm_def least_def Upper_def elem_def
by auto

lemma somegcd_meet:
  fixes G (structure)
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "somegcd G a b = meet (division_rel G) a b"
unfolding somegcd_def meet_def inf_def
by (simp add: gcdof_greatestLower[OF carr])

lemma (in monoid) isgcd_divides_l:
  assumes "a divides b"
    and "a \<in> carrier G"  "b \<in> carrier G"
  shows "a gcdof a b"
using assms
unfolding isgcd_def
by fast

lemma (in monoid) isgcd_divides_r:
  assumes "b divides a"
    and "a \<in> carrier G"  "b \<in> carrier G"
  shows "b gcdof a b"
using assms
unfolding isgcd_def
by fast


subsubsection {* Existence of gcd and lcm *}

lemma (in factorial_monoid) gcdof_exists:
  assumes acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G"
  shows "\<exists>c. c \<in> carrier G \<and> c gcdof a b"
proof -
  from acarr have "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a" by (rule wfactors_exist)
  from this obtain as
      where ascarr: "set as \<subseteq> carrier G"
      and afs: "wfactors G as a"
      by auto
  from afs have airr: "\<forall>a \<in> set as. irreducible G a" by (fast elim: wfactorsE)

  from bcarr have "\<exists>bs. set bs \<subseteq> carrier G \<and> wfactors G bs b" by (rule wfactors_exist)
  from this obtain bs
      where bscarr: "set bs \<subseteq> carrier G"
      and bfs: "wfactors G bs b"
      by auto
  from bfs have birr: "\<forall>b \<in> set bs. irreducible G b" by (fast elim: wfactorsE)

  have "\<exists>c cs. c \<in> carrier G \<and> set cs \<subseteq> carrier G \<and> wfactors G cs c \<and> 
               fmset G cs = fmset G as #\<inter> fmset G bs"
  proof (intro mset_wfactorsEx)
    fix X
    assume "X \<in> set_of (fmset G as #\<inter> fmset G bs)"
    hence "X \<in> set_of (fmset G as)" by (simp add: multiset_inter_def)
    hence "X \<in> set (map (assocs G) as)" by (simp add: fmset_def)
    hence "\<exists>x. X = assocs G x \<and> x \<in> set as" by (induct as) auto
    from this obtain x
        where X: "X = assocs G x"
        and xas: "x \<in> set as"
        by auto
    with ascarr have xcarr: "x \<in> carrier G" by fast
    from xas airr have xirr: "irreducible G x" by simp
 
    from xcarr and xirr and X
        show "\<exists>x. (x \<in> carrier G \<and> irreducible G x) \<and> X = assocs G x" by fast
  qed

  from this obtain c cs
      where ccarr: "c \<in> carrier G"
      and cscarr: "set cs \<subseteq> carrier G" 
      and csirr: "wfactors G cs c"
      and csmset: "fmset G cs = fmset G as #\<inter> fmset G bs" by auto

  have "c gcdof a b"
  proof (simp add: isgcd_def, safe)
    from csmset
        have "fmset G cs \<le> fmset G as"
        by (simp add: multiset_inter_def mset_le_def)
    thus "c divides a" by (rule fmsubset_divides) fact+
  next
    from csmset
        have "fmset G cs \<le> fmset G bs"
        by (simp add: multiset_inter_def mset_le_def, force)
    thus "c divides b" by (rule fmsubset_divides) fact+
  next
    fix y
    assume ycarr: "y \<in> carrier G"
    hence "\<exists>ys. set ys \<subseteq> carrier G \<and> wfactors G ys y" by (rule wfactors_exist)
    from this obtain ys
        where yscarr: "set ys \<subseteq> carrier G"
        and yfs: "wfactors G ys y"
        by auto

    assume "y divides a"
    hence ya: "fmset G ys \<le> fmset G as" by (rule divides_fmsubset) fact+

    assume "y divides b"
    hence yb: "fmset G ys \<le> fmset G bs" by (rule divides_fmsubset) fact+

    from ya yb csmset
    have "fmset G ys \<le> fmset G cs" by (simp add: mset_le_def multiset_inter_count)
    thus "y divides c" by (rule fmsubset_divides) fact+
  qed

  with ccarr
      show "\<exists>c. c \<in> carrier G \<and> c gcdof a b" by fast
qed

lemma (in factorial_monoid) lcmof_exists:
  assumes acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G"
  shows "\<exists>c. c \<in> carrier G \<and> c lcmof a b"
proof -
  from acarr have "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a" by (rule wfactors_exist)
  from this obtain as
      where ascarr: "set as \<subseteq> carrier G"
      and afs: "wfactors G as a"
      by auto
  from afs have airr: "\<forall>a \<in> set as. irreducible G a" by (fast elim: wfactorsE)

  from bcarr have "\<exists>bs. set bs \<subseteq> carrier G \<and> wfactors G bs b" by (rule wfactors_exist)
  from this obtain bs
      where bscarr: "set bs \<subseteq> carrier G"
      and bfs: "wfactors G bs b"
      by auto
  from bfs have birr: "\<forall>b \<in> set bs. irreducible G b" by (fast elim: wfactorsE)

  have "\<exists>c cs. c \<in> carrier G \<and> set cs \<subseteq> carrier G \<and> wfactors G cs c \<and> 
               fmset G cs = (fmset G as - fmset G bs) + fmset G bs"
  proof (intro mset_wfactorsEx)
    fix X
    assume "X \<in> set_of ((fmset G as - fmset G bs) + fmset G bs)"
    hence "X \<in> set_of (fmset G as) \<or> X \<in> set_of (fmset G bs)"
       by (cases "X :# fmset G bs", simp, simp)
    moreover
    {
      assume "X \<in> set_of (fmset G as)"
      hence "X \<in> set (map (assocs G) as)" by (simp add: fmset_def)
      hence "\<exists>x. x \<in> set as \<and> X = assocs G x" by (induct as) auto
      from this obtain x
          where xas: "x \<in> set as"
          and X: "X = assocs G x" by auto

      with ascarr have xcarr: "x \<in> carrier G" by fast
      from xas airr have xirr: "irreducible G x" by simp

      from xcarr and xirr and X
          have "\<exists>x. (x \<in> carrier G \<and> irreducible G x) \<and> X = assocs G x" by fast
    }
    moreover
    {
      assume "X \<in> set_of (fmset G bs)"
      hence "X \<in> set (map (assocs G) bs)" by (simp add: fmset_def)
      hence "\<exists>x. x \<in> set bs \<and> X = assocs G x" by (induct as) auto
      from this obtain x
          where xbs: "x \<in> set bs"
          and X: "X = assocs G x" by auto

      with bscarr have xcarr: "x \<in> carrier G" by fast
      from xbs birr have xirr: "irreducible G x" by simp

      from xcarr and xirr and X
          have "\<exists>x. (x \<in> carrier G \<and> irreducible G x) \<and> X = assocs G x" by fast
    }
    ultimately
    show "\<exists>x. (x \<in> carrier G \<and> irreducible G x) \<and> X = assocs G x" by fast
  qed

  from this obtain c cs
      where ccarr: "c \<in> carrier G"
      and cscarr: "set cs \<subseteq> carrier G" 
      and csirr: "wfactors G cs c"
      and csmset: "fmset G cs = fmset G as - fmset G bs + fmset G bs" by auto

  have "c lcmof a b"
  proof (simp add: islcm_def, safe)
    from csmset have "fmset G as \<le> fmset G cs" by (simp add: mset_le_def, force)
    thus "a divides c" by (rule fmsubset_divides) fact+
  next
    from csmset have "fmset G bs \<le> fmset G cs" by (simp add: mset_le_def)
    thus "b divides c" by (rule fmsubset_divides) fact+
  next
    fix y
    assume ycarr: "y \<in> carrier G"
    hence "\<exists>ys. set ys \<subseteq> carrier G \<and> wfactors G ys y" by (rule wfactors_exist)
    from this obtain ys
        where yscarr: "set ys \<subseteq> carrier G"
        and yfs: "wfactors G ys y"
        by auto

    assume "a divides y"
    hence ya: "fmset G as \<le> fmset G ys" by (rule divides_fmsubset) fact+

    assume "b divides y"
    hence yb: "fmset G bs \<le> fmset G ys" by (rule divides_fmsubset) fact+

    from ya yb csmset
    have "fmset G cs \<le> fmset G ys"
      apply (simp add: mset_le_def, clarify)
      apply (case_tac "count (fmset G as) a < count (fmset G bs) a")
       apply simp
      apply simp
    done
    thus "c divides y" by (rule fmsubset_divides) fact+
  qed

  with ccarr
      show "\<exists>c. c \<in> carrier G \<and> c lcmof a b" by fast
qed


subsection {* Conditions for Factoriality *}

subsubsection {* Gcd condition *}

lemma (in gcd_condition_monoid) division_weak_lower_semilattice [simp]:
  shows "weak_lower_semilattice (division_rel G)"
proof -
  interpret weak_partial_order "division_rel G" ..
  show ?thesis
  apply (unfold_locales, simp_all)
  proof -
    fix x y
    assume carr: "x \<in> carrier G"  "y \<in> carrier G"
    hence "\<exists>z. z \<in> carrier G \<and> z gcdof x y" by (rule gcdof_exists)
    from this obtain z
        where zcarr: "z \<in> carrier G"
        and isgcd: "z gcdof x y"
        by auto
    with carr
    have "greatest (division_rel G) z (Lower (division_rel G) {x, y})"
        by (subst gcdof_greatestLower[symmetric], simp+)
    thus "\<exists>z. greatest (division_rel G) z (Lower (division_rel G) {x, y})" by fast
  qed
qed

lemma (in gcd_condition_monoid) gcdof_cong_l:
  assumes a'a: "a' \<sim> a"
    and agcd: "a gcdof b c"
    and a'carr: "a' \<in> carrier G" and carr': "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "a' gcdof b c"
proof -
  note carr = a'carr carr'
  interpret weak_lower_semilattice "division_rel G" by simp
  have "a' \<in> carrier G \<and> a' gcdof b c"
    apply (simp add: gcdof_greatestLower carr')
    apply (subst greatest_Lower_cong_l[of _ a])
       apply (simp add: a'a)
      apply (simp add: carr)
     apply (simp add: carr)
    apply (simp add: carr)
    apply (simp add: gcdof_greatestLower[symmetric] agcd carr)
  done
  thus ?thesis ..
qed

lemma (in gcd_condition_monoid) gcd_closed [simp]:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "somegcd G a b \<in> carrier G"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
    apply (simp add: somegcd_meet[OF carr])
    apply (rule meet_closed[simplified], fact+)
  done
qed

lemma (in gcd_condition_monoid) gcd_isgcd:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "(somegcd G a b) gcdof a b"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  from carr
  have "somegcd G a b \<in> carrier G \<and> (somegcd G a b) gcdof a b"
    apply (subst gcdof_greatestLower, simp, simp)
    apply (simp add: somegcd_meet[OF carr] meet_def)
    apply (rule inf_of_two_greatest[simplified], assumption+)
  done
  thus "(somegcd G a b) gcdof a b" by simp
qed

lemma (in gcd_condition_monoid) gcd_exists:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "\<exists>x\<in>carrier G. x = somegcd G a b"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
    apply (simp add: somegcd_meet[OF carr])
    apply (rule meet_closed[simplified], fact+)
  done
qed

lemma (in gcd_condition_monoid) gcd_divides_l:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "(somegcd G a b) divides a"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
    apply (simp add: somegcd_meet[OF carr])
    apply (rule meet_left[simplified], fact+)
  done
qed

lemma (in gcd_condition_monoid) gcd_divides_r:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "(somegcd G a b) divides b"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
    apply (simp add: somegcd_meet[OF carr])
    apply (rule meet_right[simplified], fact+)
  done
qed

lemma (in gcd_condition_monoid) gcd_divides:
  assumes sub: "z divides x"  "z divides y"
    and L: "x \<in> carrier G"  "y \<in> carrier G"  "z \<in> carrier G"
  shows "z divides (somegcd G x y)"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
    apply (simp add: somegcd_meet L)
    apply (rule meet_le[simplified], fact+)
  done
qed

lemma (in gcd_condition_monoid) gcd_cong_l:
  assumes xx': "x \<sim> x'"
    and carr: "x \<in> carrier G"  "x' \<in> carrier G"  "y \<in> carrier G"
  shows "somegcd G x y \<sim> somegcd G x' y"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
    apply (simp add: somegcd_meet carr)
    apply (rule meet_cong_l[simplified], fact+)
  done
qed

lemma (in gcd_condition_monoid) gcd_cong_r:
  assumes carr: "x \<in> carrier G"  "y \<in> carrier G"  "y' \<in> carrier G"
    and yy': "y \<sim> y'"
  shows "somegcd G x y \<sim> somegcd G x y'"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
    apply (simp add: somegcd_meet carr)
    apply (rule meet_cong_r[simplified], fact+)
  done
qed

(*
lemma (in gcd_condition_monoid) asc_cong_gcd_l [intro]:
  assumes carr: "b \<in> carrier G"
  shows "asc_cong (\<lambda>a. somegcd G a b)"
using carr
unfolding CONG_def
by clarsimp (blast intro: gcd_cong_l)

lemma (in gcd_condition_monoid) asc_cong_gcd_r [intro]:
  assumes carr: "a \<in> carrier G"
  shows "asc_cong (\<lambda>b. somegcd G a b)"
using carr
unfolding CONG_def
by clarsimp (blast intro: gcd_cong_r)

lemmas (in gcd_condition_monoid) asc_cong_gcd_split [simp] = 
    assoc_split[OF _ asc_cong_gcd_l] assoc_split[OF _ asc_cong_gcd_r]
*)

lemma (in gcd_condition_monoid) gcdI:
  assumes dvd: "a divides b"  "a divides c"
    and others: "\<forall>y\<in>carrier G. y divides b \<and> y divides c \<longrightarrow> y divides a"
    and acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G" and ccarr: "c \<in> carrier G"
  shows "a \<sim> somegcd G b c"
apply (simp add: somegcd_def)
apply (rule someI2_ex)
 apply (rule exI[of _ a], simp add: isgcd_def)
 apply (simp add: assms)
apply (simp add: isgcd_def assms, clarify)
apply (insert assms, blast intro: associatedI)
done

lemma (in gcd_condition_monoid) gcdI2:
  assumes "a gcdof b c"
    and "a \<in> carrier G" and bcarr: "b \<in> carrier G" and ccarr: "c \<in> carrier G"
  shows "a \<sim> somegcd G b c"
using assms
unfolding isgcd_def
by (blast intro: gcdI)

lemma (in gcd_condition_monoid) SomeGcd_ex:
  assumes "finite A"  "A \<subseteq> carrier G"  "A \<noteq> {}"
  shows "\<exists>x\<in> carrier G. x = SomeGcd G A"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
    apply (simp add: SomeGcd_def)
    apply (rule finite_inf_closed[simplified], fact+)
  done
qed

lemma (in gcd_condition_monoid) gcd_assoc:
  assumes carr: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "somegcd G (somegcd G a b) c \<sim> somegcd G a (somegcd G b c)"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp
  show ?thesis
    apply (subst (2 3) somegcd_meet, (simp add: carr)+)
    apply (simp add: somegcd_meet carr)
    apply (rule weak_meet_assoc[simplified], fact+)
  done
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
  hence cd'ca: "c \<otimes> ?d divides (c \<otimes> a)" by (simp add: divides_mult_lI)

  have "?d divides b" by (simp add: gcd_divides_r)
  hence cd'cb: "c \<otimes> ?d divides (c \<otimes> b)" by (simp add: divides_mult_lI)
  
  from cd'ca cd'cb
      have cd'e: "c \<otimes> ?d divides ?e"
      by (rule gcd_divides) simp+

  hence "\<exists>u. u \<in> carrier G \<and> ?e = c \<otimes> ?d \<otimes> u"
      by (elim dividesE, fast)
  from this obtain u
      where ucarr[simp]: "u \<in> carrier G"
      and e_cdu: "?e = c \<otimes> ?d \<otimes> u"
      by auto

  note carr = carr ucarr

  have "?e divides c \<otimes> a" by (rule gcd_divides_l) simp+
  hence "\<exists>x. x \<in> carrier G \<and> c \<otimes> a = ?e \<otimes> x"
      by (elim dividesE, fast)
  from this obtain x
      where xcarr: "x \<in> carrier G"
      and ca_ex: "c \<otimes> a = ?e \<otimes> x"
      by auto
  with e_cdu
      have ca_cdux: "c \<otimes> a = c \<otimes> ?d \<otimes> u \<otimes> x" by simp

  from ca_cdux xcarr
       have "c \<otimes> a = c \<otimes> (?d \<otimes> u \<otimes> x)" by (simp add: m_assoc)
  then have "a = ?d \<otimes> u \<otimes> x" by (rule l_cancel[of c a]) (simp add: xcarr)+
  hence du'a: "?d \<otimes> u divides a" by (rule dividesI[OF xcarr])

  have "?e divides c \<otimes> b" by (intro gcd_divides_r, simp+)
  hence "\<exists>x. x \<in> carrier G \<and> c \<otimes> b = ?e \<otimes> x"
      by (elim dividesE, fast)
  from this obtain x
      where xcarr: "x \<in> carrier G"
      and cb_ex: "c \<otimes> b = ?e \<otimes> x"
      by auto
  with e_cdu
      have cb_cdux: "c \<otimes> b = c \<otimes> ?d \<otimes> u \<otimes> x" by simp

  from cb_cdux xcarr
      have "c \<otimes> b = c \<otimes> (?d \<otimes> u \<otimes> x)" by (simp add: m_assoc)
  with xcarr
      have "b = ?d \<otimes> u \<otimes> x" by (intro l_cancel[of c b], simp+)
  hence du'b: "?d \<otimes> u divides b" by (intro dividesI[OF xcarr])

  from du'a du'b carr
      have du'd: "?d \<otimes> u divides ?d"
      by (intro gcd_divides, simp+)
  hence uunit: "u \<in> Units G"
  proof (elim dividesE)
    fix v
    assume vcarr[simp]: "v \<in> carrier G"
    assume d: "?d = ?d \<otimes> u \<otimes> v"
    have "?d \<otimes> \<one> = ?d \<otimes> u \<otimes> v" by simp fact
    also have "?d \<otimes> u \<otimes> v = ?d \<otimes> (u \<otimes> v)" by (simp add: m_assoc)
    finally have "?d \<otimes> \<one> = ?d \<otimes> (u \<otimes> v)" .
    hence i2: "\<one> = u \<otimes> v" by (rule l_cancel) simp+
    hence i1: "\<one> = v \<otimes> u" by (simp add: m_comm)
    from vcarr i1[symmetric] i2[symmetric]
        show "u \<in> Units G"
        by (unfold Units_def, simp, fast)
  qed

  from e_cdu uunit
      have "somegcd G (c \<otimes> a) (c \<otimes> b) \<sim> c \<otimes> somegcd G a b"
      by (intro associatedI2[of u], simp+)
  from this[symmetric]
      show "c \<otimes> somegcd G a b \<sim> somegcd G (c \<otimes> a) (c \<otimes> b)" by simp
qed

lemma (in monoid) assoc_subst:
  assumes ab: "a \<sim> b"
    and cP: "ALL a b. a : carrier G & b : carrier G & a \<sim> b
      --> f a : carrier G & f b : carrier G & f a \<sim> f b"
    and carr: "a \<in> carrier G"  "b \<in> carrier G"
  shows "f a \<sim> f b"
  using assms by auto

lemma (in gcd_condition_monoid) relprime_mult:
  assumes abrelprime: "somegcd G a b \<sim> \<one>" and acrelprime: "somegcd G a c \<sim> \<one>"
    and carr[simp]: "a \<in> carrier G"  "b \<in> carrier G"  "c \<in> carrier G"
  shows "somegcd G a (b \<otimes> c) \<sim> \<one>"
proof -
  have "c = c \<otimes> \<one>" by simp
  also from abrelprime[symmetric]
       have "\<dots> \<sim> c \<otimes> somegcd G a b"
         by (rule assoc_subst) (simp add: mult_cong_r)+
  also have "\<dots> \<sim> somegcd G (c \<otimes> a) (c \<otimes> b)" by (rule gcd_mult) fact+
  finally
       have c: "c \<sim> somegcd G (c \<otimes> a) (c \<otimes> b)" by simp

  from carr
       have a: "a \<sim> somegcd G a (c \<otimes> a)"
       by (fast intro: gcdI divides_prod_l)

  have "somegcd G a (b \<otimes> c) \<sim> somegcd G a (c \<otimes> b)" by (simp add: m_comm)
  also from a
       have "\<dots> \<sim> somegcd G (somegcd G a (c \<otimes> a)) (c \<otimes> b)"
         by (rule assoc_subst) (simp add: gcd_cong_l)+
  also from gcd_assoc
       have "\<dots> \<sim> somegcd G a (somegcd G (c \<otimes> a) (c \<otimes> b))"
       by (rule assoc_subst) simp+
  also from c[symmetric]
       have "\<dots> \<sim> somegcd G a c"
         by (rule assoc_subst) (simp add: gcd_cong_r)+
  also note acrelprime
  finally
       show "somegcd G a (b \<otimes> c) \<sim> \<one>" by simp
qed

lemma (in gcd_condition_monoid) primeness_condition:
  "primeness_condition_monoid G"
apply unfold_locales
apply (rule primeI)
 apply (elim irreducibleE, assumption)
proof -
  fix p a b
  assume pcarr: "p \<in> carrier G" and acarr: "a \<in> carrier G" and bcarr: "b \<in> carrier G"
    and pirr: "irreducible G p"
    and pdvdab: "p divides a \<otimes> b"
  from pirr
      have pnunit: "p \<notin> Units G"
      and r[rule_format]: "\<forall>b. b \<in> carrier G \<and> properfactor G b p \<longrightarrow> b \<in> Units G"
      by - (fast elim: irreducibleE)+

  show "p divides a \<or> p divides b"
  proof (rule ccontr, clarsimp)
    assume npdvda: "\<not> p divides a"
    with pcarr acarr
    have "\<one> \<sim> somegcd G p a"
    apply (intro gcdI, simp, simp, simp)
      apply (fast intro: unit_divides)
     apply (fast intro: unit_divides)
    apply (clarsimp simp add: Unit_eq_dividesone[symmetric])
    apply (rule r, rule, assumption)
    apply (rule properfactorI, assumption)
    proof (rule ccontr, simp)
      fix y
      assume ycarr: "y \<in> carrier G"
      assume "p divides y"
      also assume "y divides a"
      finally
          have "p divides a" by (simp add: pcarr ycarr acarr)
      with npdvda
          show "False" ..
    qed simp+
    with pcarr acarr
        have pa: "somegcd G p a \<sim> \<one>" by (fast intro: associated_sym[of "\<one>"] gcd_closed)

    assume npdvdb: "\<not> p divides b"
    with pcarr bcarr
    have "\<one> \<sim> somegcd G p b"
    apply (intro gcdI, simp, simp, simp)
      apply (fast intro: unit_divides)
     apply (fast intro: unit_divides)
    apply (clarsimp simp add: Unit_eq_dividesone[symmetric])
    apply (rule r, rule, assumption)
    apply (rule properfactorI, assumption)
    proof (rule ccontr, simp)
      fix y
      assume ycarr: "y \<in> carrier G"
      assume "p divides y"
      also assume "y divides b"
      finally have "p divides b" by (simp add: pcarr ycarr bcarr)
      with npdvdb
          show "False" ..
    qed simp+
    with pcarr bcarr
        have pb: "somegcd G p b \<sim> \<one>" by (fast intro: associated_sym[of "\<one>"] gcd_closed)

    from pcarr acarr bcarr pdvdab
        have "p gcdof p (a \<otimes> b)" by (fast intro: isgcd_divides_l)

    with pcarr acarr bcarr
         have "p \<sim> somegcd G p (a \<otimes> b)" by (fast intro: gcdI2)
    also from pa pb pcarr acarr bcarr
         have "somegcd G p (a \<otimes> b) \<sim> \<one>" by (rule relprime_mult)
    finally have "p \<sim> \<one>" by (simp add: pcarr acarr bcarr)

    with pcarr
        have "p \<in> Units G" by (fast intro: assoc_unit_l)
    with pnunit
        show "False" ..
  qed
qed

sublocale gcd_condition_monoid \<subseteq> primeness_condition_monoid
  by (rule primeness_condition)


subsubsection {* Divisor chain condition *}

lemma (in divisor_chain_condition_monoid) wfactors_exist:
  assumes acarr: "a \<in> carrier G"
  shows "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a"
proof -
  have r[rule_format]: "a \<in> carrier G \<longrightarrow> (\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a)"
    apply (rule wf_induct[OF division_wellfounded])
  proof -
    fix x
    assume ih: "\<forall>y. (y, x) \<in> {(x, y). x \<in> carrier G \<and> y \<in> carrier G \<and> properfactor G x y}
                    \<longrightarrow> y \<in> carrier G \<longrightarrow> (\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as y)"

    show "x \<in> carrier G \<longrightarrow> (\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as x)"
    apply clarify
    apply (cases "x \<in> Units G")
     apply (rule exI[of _ "[]"], simp)
    apply (cases "irreducible G x")
     apply (rule exI[of _ "[x]"], simp add: wfactors_def)
    proof -
      assume xcarr: "x \<in> carrier G"
        and xnunit: "x \<notin> Units G"
        and xnirr: "\<not> irreducible G x"
      hence "\<exists>y. y \<in> carrier G \<and> properfactor G y x \<and> y \<notin> Units G"
        apply - apply (rule ccontr, simp)
        apply (subgoal_tac "irreducible G x", simp)
        apply (rule irreducibleI, simp, simp)
      done
      from this obtain y
          where ycarr: "y \<in> carrier G"
          and ynunit: "y \<notin> Units G"
          and pfyx: "properfactor G y x"
          by auto

      have ih':
           "\<And>y. \<lbrakk>y \<in> carrier G; properfactor G y x\<rbrakk>
                \<Longrightarrow> \<exists>as. set as \<subseteq> carrier G \<and> wfactors G as y"
          by (rule ih[rule_format, simplified]) (simp add: xcarr)+

      from ycarr pfyx
          have "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as y"
          by (rule ih')
      from this obtain ys
          where yscarr: "set ys \<subseteq> carrier G"
          and yfs: "wfactors G ys y"
          by auto

      from pfyx
          have "y divides x"
          and nyx: "\<not> y \<sim> x"
          by - (fast elim: properfactorE2)+
      hence "\<exists>z. z \<in> carrier G \<and> x = y \<otimes> z"
          by (fast elim: dividesE)

      from this obtain z
          where zcarr: "z \<in> carrier G"
          and x: "x = y \<otimes> z"
          by auto

      from zcarr ycarr
      have "properfactor G z x"
        apply (subst x)
        apply (intro properfactorI3[of _ _ y])
         apply (simp add: m_comm)
        apply (simp add: ynunit)+
      done
      with zcarr
          have "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as z"
          by (rule ih')
      from this obtain zs
          where zscarr: "set zs \<subseteq> carrier G"
          and zfs: "wfactors G zs z"
          by auto

      from yscarr zscarr
          have xscarr: "set (ys@zs) \<subseteq> carrier G" by simp
      from yfs zfs ycarr zcarr yscarr zscarr
          have "wfactors G (ys@zs) (y\<otimes>z)" by (rule wfactors_mult)
      hence "wfactors G (ys@zs) x" by (simp add: x)

      from xscarr this
          show "\<exists>xs. set xs \<subseteq> carrier G \<and> wfactors G xs x" by fast
    qed
  qed

  from acarr
      show ?thesis by (rule r)
qed


subsubsection {* Primeness condition *}

lemma (in comm_monoid_cancel) multlist_prime_pos:
  assumes carr: "a \<in> carrier G"  "set as \<subseteq> carrier G"
    and aprime: "prime G a"
    and "a divides (foldr (op \<otimes>) as \<one>)"
  shows "\<exists>i<length as. a divides (as!i)"
proof -
  have r[rule_format]:
       "set as \<subseteq> carrier G \<and> a divides (foldr (op \<otimes>) as \<one>)
        \<longrightarrow> (\<exists>i. i < length as \<and> a divides (as!i))"
    apply (induct as)
     apply clarsimp defer 1
     apply clarsimp defer 1
  proof -
    assume "a divides \<one>"
    with carr
        have "a \<in> Units G"
        by (fast intro: divides_unit[of a \<one>])
    with aprime
        show "False" by (elim primeE, simp)
  next
    fix aa as
    assume ih[rule_format]: "a divides foldr op \<otimes> as \<one> \<longrightarrow> (\<exists>i<length as. a divides as ! i)"
      and carr': "aa \<in> carrier G"  "set as \<subseteq> carrier G"
      and "a divides aa \<otimes> foldr op \<otimes> as \<one>"
    with carr aprime
        have "a divides aa \<or> a divides foldr op \<otimes> as \<one>"
        by (intro prime_divides) simp+
    moreover {
      assume "a divides aa"
      hence p1: "a divides (aa#as)!0" by simp
      have "0 < Suc (length as)" by simp
      with p1 have "\<exists>i<Suc (length as). a divides (aa # as) ! i" by fast
    }
    moreover {
      assume "a divides foldr op \<otimes> as \<one>"
      hence "\<exists>i. i < length as \<and> a divides as ! i" by (rule ih)
      from this obtain i where "a divides as ! i" and len: "i < length as" by auto
      hence p1: "a divides (aa#as) ! (Suc i)" by simp
      from len have "Suc i < Suc (length as)" by simp
      with p1 have "\<exists>i<Suc (length as). a divides (aa # as) ! i" by force
   }
   ultimately
      show "\<exists>i<Suc (length as). a divides (aa # as) ! i" by fast
  qed

  from assms
      show ?thesis
      by (intro r, safe)
qed

lemma (in primeness_condition_monoid) wfactors_unique__hlp_induct:
  "\<forall>a as'. a \<in> carrier G \<and> set as \<subseteq> carrier G \<and> set as' \<subseteq> carrier G \<and> 
           wfactors G as a \<and> wfactors G as' a \<longrightarrow> essentially_equal G as as'"
proof (induct as)
  case Nil show ?case apply auto
  proof -
    fix a as'
    assume a: "a \<in> carrier G"
    assume "wfactors G [] a"
    then obtain "\<one> \<sim> a" by (auto elim: wfactorsE)
    with a have "a \<in> Units G" by (auto intro: assoc_unit_r)
    moreover assume "wfactors G as' a"
    moreover assume "set as' \<subseteq> carrier G"
    ultimately have "as' = []" by (rule unit_wfactors_empty)
    then show "essentially_equal G [] as'" by simp
  qed
next
  case (Cons ah as) then show ?case apply clarsimp 
  proof -
    fix a as'
    assume ih [rule_format]: 
      "\<forall>a as'. a \<in> carrier G \<and> set as' \<subseteq> carrier G \<and> wfactors G as a \<and>
        wfactors G as' a \<longrightarrow> essentially_equal G as as'"
      and acarr: "a \<in> carrier G" and ahcarr: "ah \<in> carrier G"
      and ascarr: "set as \<subseteq> carrier G" and as'carr: "set as' \<subseteq> carrier G"
      and afs: "wfactors G (ah # as) a"
      and afs': "wfactors G as' a"
    hence ahdvda: "ah divides a"
      by (intro wfactors_dividesI[of "ah#as" "a"], simp+)
    hence "\<exists>a'\<in> carrier G. a = ah \<otimes> a'" by (fast elim: dividesE)
    from this obtain a'
      where a'carr: "a' \<in> carrier G"
      and a: "a = ah \<otimes> a'"
      by auto
    have a'fs: "wfactors G as a'"
      apply (rule wfactorsE[OF afs], rule wfactorsI, simp)
      apply (simp add: a, insert ascarr a'carr)
      apply (intro assoc_l_cancel[of ah _ a'] multlist_closed ahcarr, assumption+)
      done
    from afs have ahirr: "irreducible G ah" by (elim wfactorsE, simp)
    with ascarr have ahprime: "prime G ah" by (intro irreducible_prime ahcarr)

    note carr [simp] = acarr ahcarr ascarr as'carr a'carr

    note ahdvda
    also from afs'
      have "a divides (foldr (op \<otimes>) as' \<one>)"
      by (elim wfactorsE associatedE, simp)
    finally have "ah divides (foldr (op \<otimes>) as' \<one>)" by simp

    with ahprime
      have "\<exists>i<length as'. ah divides as'!i"
      by (intro multlist_prime_pos, simp+)
    from this obtain i
      where len: "i<length as'" and ahdvd: "ah divides as'!i"
      by auto
    from afs' carr have irrasi: "irreducible G (as'!i)"
      by (fast intro: nth_mem[OF len] elim: wfactorsE)
    from len carr
      have asicarr[simp]: "as'!i \<in> carrier G" by (unfold set_conv_nth, force)
    note carr = carr asicarr

    from ahdvd have "\<exists>x \<in> carrier G. as'!i = ah \<otimes> x" by (fast elim: dividesE)
    from this obtain x where "x \<in> carrier G" and asi: "as'!i = ah \<otimes> x" by auto

    with carr irrasi[simplified asi]
      have asiah: "as'!i \<sim> ah" apply -
      apply (elim irreducible_prodE[of "ah" "x"], assumption+)
       apply (rule associatedI2[of x], assumption+)
      apply (rule irreducibleE[OF ahirr], simp)
      done

    note setparts = set_take_subset[of i as'] set_drop_subset[of "Suc i" as']
    note partscarr [simp] = setparts[THEN subset_trans[OF _ as'carr]]
    note carr = carr partscarr

    have "\<exists>aa_1. aa_1 \<in> carrier G \<and> wfactors G (take i as') aa_1"
      apply (intro wfactors_prod_exists)
      using setparts afs' by (fast elim: wfactorsE, simp)
    from this obtain aa_1
        where aa1carr: "aa_1 \<in> carrier G"
        and aa1fs: "wfactors G (take i as') aa_1"
        by auto

    have "\<exists>aa_2. aa_2 \<in> carrier G \<and> wfactors G (drop (Suc i) as') aa_2"
      apply (intro wfactors_prod_exists)
      using setparts afs' by (fast elim: wfactorsE, simp)
    from this obtain aa_2
        where aa2carr: "aa_2 \<in> carrier G"
        and aa2fs: "wfactors G (drop (Suc i) as') aa_2"
        by auto

    note carr = carr aa1carr[simp] aa2carr[simp]

    from aa1fs aa2fs
      have v1: "wfactors G (take i as' @ drop (Suc i) as') (aa_1 \<otimes> aa_2)"
      by (intro wfactors_mult, simp+)
    hence v1': "wfactors G (as'!i # take i as' @ drop (Suc i) as') (as'!i \<otimes> (aa_1 \<otimes> aa_2))"
      apply (intro wfactors_mult_single)
      using setparts afs'
      by (fast intro: nth_mem[OF len] elim: wfactorsE, simp+)

    from aa2carr carr aa1fs aa2fs
      have "wfactors G (as'!i # drop (Suc i) as') (as'!i \<otimes> aa_2)"
      apply (intro wfactors_mult_single)
          apply (rule wfactorsE[OF afs'], fast intro: nth_mem[OF len])
         apply (fast intro: nth_mem[OF len])
        apply fast
       apply fast
      apply assumption
    done
    with len carr aa1carr aa2carr aa1fs
      have v2: "wfactors G (take i as' @ as'!i # drop (Suc i) as') (aa_1 \<otimes> (as'!i \<otimes> aa_2))"
      apply (intro wfactors_mult)
           apply fast
          apply (simp, (fast intro: nth_mem[OF len])?)+
    done

    from len
      have as': "as' = (take i as' @ as'!i # drop (Suc i) as')"
      by (simp add: drop_Suc_conv_tl)
    with carr
      have eer: "essentially_equal G (take i as' @ as'!i # drop (Suc i) as') as'"
      by simp

    with v2 afs' carr aa1carr aa2carr nth_mem[OF len]
      have "aa_1 \<otimes> (as'!i \<otimes> aa_2) \<sim> a"
      apply (intro ee_wfactorsD[of "take i as' @ as'!i # drop (Suc i) as'"  "as'"])
            apply fast+
          apply (simp, fast)
    done
    then
    have t1: "as'!i \<otimes> (aa_1 \<otimes> aa_2) \<sim> a"
      apply (simp add: m_assoc[symmetric])
      apply (simp add: m_comm)
    done
    from carr asiah
    have "ah \<otimes> (aa_1 \<otimes> aa_2) \<sim> as'!i \<otimes> (aa_1 \<otimes> aa_2)"
      apply (intro mult_cong_l)
      apply (fast intro: associated_sym, simp+)
    done
    also note t1
    finally
      have "ah \<otimes> (aa_1 \<otimes> aa_2) \<sim> a" by simp

    with carr aa1carr aa2carr a'carr nth_mem[OF len]
      have a': "aa_1 \<otimes> aa_2 \<sim> a'"
      by (simp add: a, fast intro: assoc_l_cancel[of ah _ a'])

    note v1
    also note a'
    finally have "wfactors G (take i as' @ drop (Suc i) as') a'" by simp

    from a'fs this carr
      have "essentially_equal G as (take i as' @ drop (Suc i) as')"
      by (intro ih[of a']) simp

    hence ee1: "essentially_equal G (ah # as) (ah # take i as' @ drop (Suc i) as')"
      apply (elim essentially_equalE) apply (fastforce intro: essentially_equalI)
    done

    from carr
    have ee2: "essentially_equal G (ah # take i as' @ drop (Suc i) as')
      (as' ! i # take i as' @ drop (Suc i) as')"
    proof (intro essentially_equalI)
      show "ah # take i as' @ drop (Suc i) as' <~~> ah # take i as' @ drop (Suc i) as'"
        by simp
    next
      show "ah # take i as' @ drop (Suc i) as' [\<sim>] as' ! i # take i as' @ drop (Suc i) as'"
      apply (simp add: list_all2_append)
      apply (simp add: asiah[symmetric] ahcarr asicarr)
      done
    qed

    note ee1
    also note ee2
    also have "essentially_equal G (as' ! i # take i as' @ drop (Suc i) as')
      (take i as' @ as' ! i # drop (Suc i) as')"
      apply (intro essentially_equalI)
      apply (subgoal_tac "as' ! i # take i as' @ drop (Suc i) as' <~~> 
        take i as' @ as' ! i # drop (Suc i) as'")
  apply simp
       apply (rule perm_append_Cons)
      apply simp
    done
    finally
      have "essentially_equal G (ah # as) (take i as' @ as' ! i # drop (Suc i) as')" by simp
    then show "essentially_equal G (ah # as) as'" by (subst as', assumption)
  qed
qed

lemma (in primeness_condition_monoid) wfactors_unique:
  assumes "wfactors G as a"  "wfactors G as' a"
    and "a \<in> carrier G"  "set as \<subseteq> carrier G"  "set as' \<subseteq> carrier G"
  shows "essentially_equal G as as'"
apply (rule wfactors_unique__hlp_induct[rule_format, of a])
apply (simp add: assms)
done


subsubsection {* Application to factorial monoids *}

text {* Number of factors for wellfoundedness *}

definition
  factorcount :: "_ \<Rightarrow> 'a \<Rightarrow> nat" where
  "factorcount G a =
    (THE c. (ALL as. set as \<subseteq> carrier G \<and> wfactors G as a \<longrightarrow> c = length as))"

lemma (in monoid) ee_length:
  assumes ee: "essentially_equal G as bs"
  shows "length as = length bs"
apply (rule essentially_equalE[OF ee])
apply (metis list_all2_conv_all_nth perm_length)
done

lemma (in factorial_monoid) factorcount_exists:
  assumes carr[simp]: "a \<in> carrier G"
  shows "EX c. ALL as. set as \<subseteq> carrier G \<and> wfactors G as a \<longrightarrow> c = length as"
proof -
  have "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a" by (intro wfactors_exist, simp)
  from this obtain as
      where ascarr[simp]: "set as \<subseteq> carrier G"
      and afs: "wfactors G as a"
      by (auto simp del: carr)

  have "ALL as'. set as' \<subseteq> carrier G \<and> wfactors G as' a \<longrightarrow> length as = length as'"
    by (metis afs ascarr assms ee_length wfactors_unique)
  thus "EX c. ALL as'. set as' \<subseteq> carrier G \<and> wfactors G as' a \<longrightarrow> c = length as'" ..
qed

lemma (in factorial_monoid) factorcount_unique:
  assumes afs: "wfactors G as a"
    and acarr[simp]: "a \<in> carrier G" and ascarr[simp]: "set as \<subseteq> carrier G"
  shows "factorcount G a = length as"
proof -
  have "EX ac. ALL as. set as \<subseteq> carrier G \<and> wfactors G as a \<longrightarrow> ac = length as" by (rule factorcount_exists, simp)
  from this obtain ac where
      alen: "ALL as. set as \<subseteq> carrier G \<and> wfactors G as a \<longrightarrow> ac = length as"
      by auto
  have ac: "ac = factorcount G a"
    apply (simp add: factorcount_def)
    apply (rule theI2)
      apply (rule alen)
     apply (elim allE[of _ "as"], rule allE[OF alen, of "as"], simp add: ascarr afs)
    apply (elim allE[of _ "as"], rule allE[OF alen, of "as"], simp add: ascarr afs)
  done

  from ascarr afs have "ac = length as" by (iprover intro: alen[rule_format])
  with ac show ?thesis by simp
qed

lemma (in factorial_monoid) divides_fcount:
  assumes dvd: "a divides b"
    and acarr: "a \<in> carrier G" and bcarr:"b \<in> carrier G"
  shows "factorcount G a <= factorcount G b"
apply (rule dividesE[OF dvd])
proof -
  fix c
  from assms
      have "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a" by fast
  from this obtain as
      where ascarr: "set as \<subseteq> carrier G"
      and afs: "wfactors G as a"
      by auto
  with acarr have fca: "factorcount G a = length as" by (intro factorcount_unique)

  assume ccarr: "c \<in> carrier G"
  hence "\<exists>cs. set cs \<subseteq> carrier G \<and> wfactors G cs c" by fast
  from this obtain cs
      where cscarr: "set cs \<subseteq> carrier G"
      and cfs: "wfactors G cs c"
      by auto

  note [simp] = acarr bcarr ccarr ascarr cscarr

  assume b: "b = a \<otimes> c"
  from afs cfs
      have "wfactors G (as@cs) (a \<otimes> c)" by (intro wfactors_mult, simp+)
  with b have "wfactors G (as@cs) b" by simp
  hence "factorcount G b = length (as@cs)" by (intro factorcount_unique, simp+)
  hence "factorcount G b = length as + length cs" by simp
  with fca show ?thesis by simp
qed

lemma (in factorial_monoid) associated_fcount:
  assumes acarr: "a \<in> carrier G" and bcarr:"b \<in> carrier G"
    and asc: "a \<sim> b"
  shows "factorcount G a = factorcount G b"
apply (rule associatedE[OF asc])
apply (drule divides_fcount[OF _ acarr bcarr])
apply (drule divides_fcount[OF _ bcarr acarr])
apply simp
done

lemma (in factorial_monoid) properfactor_fcount:
  assumes acarr: "a \<in> carrier G" and bcarr:"b \<in> carrier G"
    and pf: "properfactor G a b"
  shows "factorcount G a < factorcount G b"
apply (rule properfactorE[OF pf], elim dividesE)
proof -
  fix c
  from assms
  have "\<exists>as. set as \<subseteq> carrier G \<and> wfactors G as a" by fast
  from this obtain as
      where ascarr: "set as \<subseteq> carrier G"
      and afs: "wfactors G as a"
      by auto
  with acarr have fca: "factorcount G a = length as" by (intro factorcount_unique)

  assume ccarr: "c \<in> carrier G"
  hence "\<exists>cs. set cs \<subseteq> carrier G \<and> wfactors G cs c" by fast
  from this obtain cs
      where cscarr: "set cs \<subseteq> carrier G"
      and cfs: "wfactors G cs c"
      by auto

  assume b: "b = a \<otimes> c"

  have "wfactors G (as@cs) (a \<otimes> c)" by (rule wfactors_mult) fact+
  with b
      have "wfactors G (as@cs) b" by simp
  with ascarr cscarr bcarr
      have "factorcount G b = length (as@cs)" by (simp add: factorcount_unique)
  hence fcb: "factorcount G b = length as + length cs" by simp

  assume nbdvda: "\<not> b divides a"
  have "c \<notin> Units G"
  proof (rule ccontr, simp)
    assume cunit:"c \<in> Units G"

    have "b \<otimes> inv c = a \<otimes> c \<otimes> inv c" by (simp add: b)
    also with ccarr acarr cunit
        have "\<dots> = a \<otimes> (c \<otimes> inv c)" by (fast intro: m_assoc)
    also with ccarr cunit
        have "\<dots> = a \<otimes> \<one>" by (simp add: Units_r_inv)
    also with acarr
        have "\<dots> = a" by simp
    finally have "a = b \<otimes> inv c" by simp
    with ccarr cunit
    have "b divides a" by (fast intro: dividesI[of "inv c"])
    with nbdvda show False by simp
  qed

  with cfs have "length cs > 0"
    apply -
    apply (rule ccontr, simp)
    apply (metis Units_one_closed ccarr cscarr l_one one_closed properfactorI3 properfactor_fmset unit_wfactors)
    done
  with fca fcb show ?thesis by simp
qed

sublocale factorial_monoid \<subseteq> divisor_chain_condition_monoid
apply unfold_locales
apply (rule wfUNIVI)
apply (rule measure_induct[of "factorcount G"])
apply simp
apply (metis properfactor_fcount)
done

sublocale factorial_monoid \<subseteq> primeness_condition_monoid
  by default (rule irreducible_is_prime)


lemma (in factorial_monoid) primeness_condition:
  shows "primeness_condition_monoid G"
  ..

lemma (in factorial_monoid) gcd_condition [simp]:
  shows "gcd_condition_monoid G"
  by default (rule gcdof_exists)

sublocale factorial_monoid \<subseteq> gcd_condition_monoid
  by default (rule gcdof_exists)

lemma (in factorial_monoid) division_weak_lattice [simp]:
  shows "weak_lattice (division_rel G)"
proof -
  interpret weak_lower_semilattice "division_rel G" by simp

  show "weak_lattice (division_rel G)"
  apply (unfold_locales, simp_all)
  proof -
    fix x y
    assume carr: "x \<in> carrier G"  "y \<in> carrier G"

    hence "\<exists>z. z \<in> carrier G \<and> z lcmof x y" by (rule lcmof_exists)
    from this obtain z
        where zcarr: "z \<in> carrier G"
        and isgcd: "z lcmof x y"
        by auto
    with carr
    have "least (division_rel G) z (Upper (division_rel G) {x, y})"
        by (simp add: lcmof_leastUpper[symmetric])
    thus "\<exists>z. least (division_rel G) z (Upper (division_rel G) {x, y})" by fast
  qed
qed


subsection {* Factoriality Theorems *}

theorem factorial_condition_one: (* Jacobson theorem 2.21 *)
  shows "(divisor_chain_condition_monoid G \<and> primeness_condition_monoid G) = 
         factorial_monoid G"
apply rule
proof clarify
  assume dcc: "divisor_chain_condition_monoid G"
     and pc: "primeness_condition_monoid G"
  interpret divisor_chain_condition_monoid "G" by (rule dcc)
  interpret primeness_condition_monoid "G" by (rule pc)

  show "factorial_monoid G"
      by (fast intro: factorial_monoidI wfactors_exist wfactors_unique)
next
  assume fm: "factorial_monoid G"
  interpret factorial_monoid "G" by (rule fm)
  show "divisor_chain_condition_monoid G \<and> primeness_condition_monoid G"
      by rule unfold_locales
qed

theorem factorial_condition_two: (* Jacobson theorem 2.22 *)
  shows "(divisor_chain_condition_monoid G \<and> gcd_condition_monoid G) = factorial_monoid G"
apply rule
proof clarify
    assume dcc: "divisor_chain_condition_monoid G"
     and gc: "gcd_condition_monoid G"
  interpret divisor_chain_condition_monoid "G" by (rule dcc)
  interpret gcd_condition_monoid "G" by (rule gc)
  show "factorial_monoid G"
      by (simp add: factorial_condition_one[symmetric], rule, unfold_locales)
next
  assume fm: "factorial_monoid G"
  interpret factorial_monoid "G" by (rule fm)
  show "divisor_chain_condition_monoid G \<and> gcd_condition_monoid G"
      by rule unfold_locales
qed

end
