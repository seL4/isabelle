(*  Title:      HOL/Library/Nat_Infinity.thy
    Author:     David von Oheimb, TU Muenchen;  Florian Haftmann, TU Muenchen
*)

header {* Natural numbers with infinity *}

theory Nat_Infinity
imports Main
begin

subsection {* Type definition *}

text {*
  We extend the standard natural numbers by a special value indicating
  infinity.
*}

datatype inat = Fin nat | Infty

notation (xsymbols)
  Infty  ("\<infinity>")

notation (HTML output)
  Infty  ("\<infinity>")


lemma not_Infty_eq[iff]: "(x ~= Infty) = (EX i. x = Fin i)"
by (cases x) auto

lemma not_Fin_eq [iff]: "(ALL y. x ~= Fin y) = (x = Infty)"
by (cases x) auto


subsection {* Constructors and numbers *}

instantiation inat :: "{zero, one, number}"
begin

definition
  "0 = Fin 0"

definition
  [code_unfold]: "1 = Fin 1"

definition
  [code_unfold, code del]: "number_of k = Fin (number_of k)"

instance ..

end

definition iSuc :: "inat \<Rightarrow> inat" where
  "iSuc i = (case i of Fin n \<Rightarrow> Fin (Suc n) | \<infinity> \<Rightarrow> \<infinity>)"

lemma Fin_0: "Fin 0 = 0"
  by (simp add: zero_inat_def)

lemma Fin_1: "Fin 1 = 1"
  by (simp add: one_inat_def)

lemma Fin_number: "Fin (number_of k) = number_of k"
  by (simp add: number_of_inat_def)

lemma one_iSuc: "1 = iSuc 0"
  by (simp add: zero_inat_def one_inat_def iSuc_def)

lemma Infty_ne_i0 [simp]: "\<infinity> \<noteq> 0"
  by (simp add: zero_inat_def)

lemma i0_ne_Infty [simp]: "0 \<noteq> \<infinity>"
  by (simp add: zero_inat_def)

lemma zero_inat_eq [simp]:
  "number_of k = (0\<Colon>inat) \<longleftrightarrow> number_of k = (0\<Colon>nat)"
  "(0\<Colon>inat) = number_of k \<longleftrightarrow> number_of k = (0\<Colon>nat)"
  unfolding zero_inat_def number_of_inat_def by simp_all

lemma one_inat_eq [simp]:
  "number_of k = (1\<Colon>inat) \<longleftrightarrow> number_of k = (1\<Colon>nat)"
  "(1\<Colon>inat) = number_of k \<longleftrightarrow> number_of k = (1\<Colon>nat)"
  unfolding one_inat_def number_of_inat_def by simp_all

lemma zero_one_inat_neq [simp]:
  "\<not> 0 = (1\<Colon>inat)"
  "\<not> 1 = (0\<Colon>inat)"
  unfolding zero_inat_def one_inat_def by simp_all

lemma Infty_ne_i1 [simp]: "\<infinity> \<noteq> 1"
  by (simp add: one_inat_def)

lemma i1_ne_Infty [simp]: "1 \<noteq> \<infinity>"
  by (simp add: one_inat_def)

lemma Infty_ne_number [simp]: "\<infinity> \<noteq> number_of k"
  by (simp add: number_of_inat_def)

lemma number_ne_Infty [simp]: "number_of k \<noteq> \<infinity>"
  by (simp add: number_of_inat_def)

lemma iSuc_Fin: "iSuc (Fin n) = Fin (Suc n)"
  by (simp add: iSuc_def)

lemma iSuc_number_of: "iSuc (number_of k) = Fin (Suc (number_of k))"
  by (simp add: iSuc_Fin number_of_inat_def)

lemma iSuc_Infty [simp]: "iSuc \<infinity> = \<infinity>"
  by (simp add: iSuc_def)

lemma iSuc_ne_0 [simp]: "iSuc n \<noteq> 0"
  by (simp add: iSuc_def zero_inat_def split: inat.splits)

lemma zero_ne_iSuc [simp]: "0 \<noteq> iSuc n"
  by (rule iSuc_ne_0 [symmetric])

lemma iSuc_inject [simp]: "iSuc m = iSuc n \<longleftrightarrow> m = n"
  by (simp add: iSuc_def split: inat.splits)

lemma number_of_inat_inject [simp]:
  "(number_of k \<Colon> inat) = number_of l \<longleftrightarrow> (number_of k \<Colon> nat) = number_of l"
  by (simp add: number_of_inat_def)


subsection {* Addition *}

instantiation inat :: comm_monoid_add
begin

definition
  [code del]: "m + n = (case m of \<infinity> \<Rightarrow> \<infinity> | Fin m \<Rightarrow> (case n of \<infinity> \<Rightarrow> \<infinity> | Fin n \<Rightarrow> Fin (m + n)))"

lemma plus_inat_simps [simp, code]:
  "Fin m + Fin n = Fin (m + n)"
  "\<infinity> + q = \<infinity>"
  "q + \<infinity> = \<infinity>"
  by (simp_all add: plus_inat_def split: inat.splits)

instance proof
  fix n m q :: inat
  show "n + m + q = n + (m + q)"
    by (cases n, auto, cases m, auto, cases q, auto)
  show "n + m = m + n"
    by (cases n, auto, cases m, auto)
  show "0 + n = n"
    by (cases n) (simp_all add: zero_inat_def)
qed

end

lemma plus_inat_0 [simp]:
  "0 + (q\<Colon>inat) = q"
  "(q\<Colon>inat) + 0 = q"
  by (simp_all add: plus_inat_def zero_inat_def split: inat.splits)

lemma plus_inat_number [simp]:
  "(number_of k \<Colon> inat) + number_of l = (if k < Int.Pls then number_of l
    else if l < Int.Pls then number_of k else number_of (k + l))"
  unfolding number_of_inat_def plus_inat_simps nat_arith(1) if_distrib [symmetric, of _ Fin] ..

lemma iSuc_number [simp]:
  "iSuc (number_of k) = (if neg (number_of k \<Colon> int) then 1 else number_of (Int.succ k))"
  unfolding iSuc_number_of
  unfolding one_inat_def number_of_inat_def Suc_nat_number_of if_distrib [symmetric] ..

lemma iSuc_plus_1:
  "iSuc n = n + 1"
  by (cases n) (simp_all add: iSuc_Fin one_inat_def)
  
lemma plus_1_iSuc:
  "1 + q = iSuc q"
  "q + 1 = iSuc q"
  unfolding iSuc_plus_1 by (simp_all add: add_ac)


subsection {* Multiplication *}

instantiation inat :: comm_semiring_1
begin

definition
  times_inat_def [code del]:
  "m * n = (case m of \<infinity> \<Rightarrow> if n = 0 then 0 else \<infinity> | Fin m \<Rightarrow>
    (case n of \<infinity> \<Rightarrow> if m = 0 then 0 else \<infinity> | Fin n \<Rightarrow> Fin (m * n)))"

lemma times_inat_simps [simp, code]:
  "Fin m * Fin n = Fin (m * n)"
  "\<infinity> * \<infinity> = \<infinity>"
  "\<infinity> * Fin n = (if n = 0 then 0 else \<infinity>)"
  "Fin m * \<infinity> = (if m = 0 then 0 else \<infinity>)"
  unfolding times_inat_def zero_inat_def
  by (simp_all split: inat.split)

instance proof
  fix a b c :: inat
  show "(a * b) * c = a * (b * c)"
    unfolding times_inat_def zero_inat_def
    by (simp split: inat.split)
  show "a * b = b * a"
    unfolding times_inat_def zero_inat_def
    by (simp split: inat.split)
  show "1 * a = a"
    unfolding times_inat_def zero_inat_def one_inat_def
    by (simp split: inat.split)
  show "(a + b) * c = a * c + b * c"
    unfolding times_inat_def zero_inat_def
    by (simp split: inat.split add: left_distrib)
  show "0 * a = 0"
    unfolding times_inat_def zero_inat_def
    by (simp split: inat.split)
  show "a * 0 = 0"
    unfolding times_inat_def zero_inat_def
    by (simp split: inat.split)
  show "(0::inat) \<noteq> 1"
    unfolding zero_inat_def one_inat_def
    by simp
qed

end

lemma mult_iSuc: "iSuc m * n = n + m * n"
  unfolding iSuc_plus_1 by (simp add: algebra_simps)

lemma mult_iSuc_right: "m * iSuc n = m + m * n"
  unfolding iSuc_plus_1 by (simp add: algebra_simps)

lemma of_nat_eq_Fin: "of_nat n = Fin n"
  apply (induct n)
  apply (simp add: Fin_0)
  apply (simp add: plus_1_iSuc iSuc_Fin)
  done

instance inat :: semiring_char_0
  by default (simp add: of_nat_eq_Fin)


subsection {* Ordering *}

instantiation inat :: ordered_ab_semigroup_add
begin

definition
  [code del]: "m \<le> n = (case n of Fin n1 \<Rightarrow> (case m of Fin m1 \<Rightarrow> m1 \<le> n1 | \<infinity> \<Rightarrow> False)
    | \<infinity> \<Rightarrow> True)"

definition
  [code del]: "m < n = (case m of Fin m1 \<Rightarrow> (case n of Fin n1 \<Rightarrow> m1 < n1 | \<infinity> \<Rightarrow> True)
    | \<infinity> \<Rightarrow> False)"

lemma inat_ord_simps [simp]:
  "Fin m \<le> Fin n \<longleftrightarrow> m \<le> n"
  "Fin m < Fin n \<longleftrightarrow> m < n"
  "q \<le> \<infinity>"
  "q < \<infinity> \<longleftrightarrow> q \<noteq> \<infinity>"
  "\<infinity> \<le> q \<longleftrightarrow> q = \<infinity>"
  "\<infinity> < q \<longleftrightarrow> False"
  by (simp_all add: less_eq_inat_def less_inat_def split: inat.splits)

lemma inat_ord_code [code]:
  "Fin m \<le> Fin n \<longleftrightarrow> m \<le> n"
  "Fin m < Fin n \<longleftrightarrow> m < n"
  "q \<le> \<infinity> \<longleftrightarrow> True"
  "Fin m < \<infinity> \<longleftrightarrow> True"
  "\<infinity> \<le> Fin n \<longleftrightarrow> False"
  "\<infinity> < q \<longleftrightarrow> False"
  by simp_all

instance by default
  (auto simp add: less_eq_inat_def less_inat_def plus_inat_def split: inat.splits)

end

instance inat :: pordered_comm_semiring
proof
  fix a b c :: inat
  assume "a \<le> b" and "0 \<le> c"
  thus "c * a \<le> c * b"
    unfolding times_inat_def less_eq_inat_def zero_inat_def
    by (simp split: inat.splits)
qed

lemma inat_ord_number [simp]:
  "(number_of m \<Colon> inat) \<le> number_of n \<longleftrightarrow> (number_of m \<Colon> nat) \<le> number_of n"
  "(number_of m \<Colon> inat) < number_of n \<longleftrightarrow> (number_of m \<Colon> nat) < number_of n"
  by (simp_all add: number_of_inat_def)

lemma i0_lb [simp]: "(0\<Colon>inat) \<le> n"
  by (simp add: zero_inat_def less_eq_inat_def split: inat.splits)

lemma i0_neq [simp]: "n \<le> (0\<Colon>inat) \<longleftrightarrow> n = 0"
  by (simp add: zero_inat_def less_eq_inat_def split: inat.splits)

lemma Infty_ileE [elim!]: "\<infinity> \<le> Fin m \<Longrightarrow> R"
  by (simp add: zero_inat_def less_eq_inat_def split: inat.splits)

lemma Infty_ilessE [elim!]: "\<infinity> < Fin m \<Longrightarrow> R"
  by simp

lemma not_ilessi0 [simp]: "\<not> n < (0\<Colon>inat)"
  by (simp add: zero_inat_def less_inat_def split: inat.splits)

lemma i0_eq [simp]: "(0\<Colon>inat) < n \<longleftrightarrow> n \<noteq> 0"
  by (simp add: zero_inat_def less_inat_def split: inat.splits)

lemma iSuc_ile_mono [simp]: "iSuc n \<le> iSuc m \<longleftrightarrow> n \<le> m"
  by (simp add: iSuc_def less_eq_inat_def split: inat.splits)
 
lemma iSuc_mono [simp]: "iSuc n < iSuc m \<longleftrightarrow> n < m"
  by (simp add: iSuc_def less_inat_def split: inat.splits)

lemma ile_iSuc [simp]: "n \<le> iSuc n"
  by (simp add: iSuc_def less_eq_inat_def split: inat.splits)

lemma not_iSuc_ilei0 [simp]: "\<not> iSuc n \<le> 0"
  by (simp add: zero_inat_def iSuc_def less_eq_inat_def split: inat.splits)

lemma i0_iless_iSuc [simp]: "0 < iSuc n"
  by (simp add: zero_inat_def iSuc_def less_inat_def split: inat.splits)

lemma ileI1: "m < n \<Longrightarrow> iSuc m \<le> n"
  by (simp add: iSuc_def less_eq_inat_def less_inat_def split: inat.splits)

lemma Suc_ile_eq: "Fin (Suc m) \<le> n \<longleftrightarrow> Fin m < n"
  by (cases n) auto

lemma iless_Suc_eq [simp]: "Fin m < iSuc n \<longleftrightarrow> Fin m \<le> n"
  by (auto simp add: iSuc_def less_inat_def split: inat.splits)

lemma min_inat_simps [simp]:
  "min (Fin m) (Fin n) = Fin (min m n)"
  "min q 0 = 0"
  "min 0 q = 0"
  "min q \<infinity> = q"
  "min \<infinity> q = q"
  by (auto simp add: min_def)

lemma max_inat_simps [simp]:
  "max (Fin m) (Fin n) = Fin (max m n)"
  "max q 0 = q"
  "max 0 q = q"
  "max q \<infinity> = \<infinity>"
  "max \<infinity> q = \<infinity>"
  by (simp_all add: max_def)

lemma Fin_ile: "n \<le> Fin m \<Longrightarrow> \<exists>k. n = Fin k"
  by (cases n) simp_all

lemma Fin_iless: "n < Fin m \<Longrightarrow> \<exists>k. n = Fin k"
  by (cases n) simp_all

lemma chain_incr: "\<forall>i. \<exists>j. Y i < Y j ==> \<exists>j. Fin k < Y j"
apply (induct_tac k)
 apply (simp (no_asm) only: Fin_0)
 apply (fast intro: le_less_trans [OF i0_lb])
apply (erule exE)
apply (drule spec)
apply (erule exE)
apply (drule ileI1)
apply (rule iSuc_Fin [THEN subst])
apply (rule exI)
apply (erule (1) le_less_trans)
done

instantiation inat :: "{bot, top}"
begin

definition bot_inat :: inat where
  "bot_inat = 0"

definition top_inat :: inat where
  "top_inat = \<infinity>"

instance proof
qed (simp_all add: bot_inat_def top_inat_def)

end


subsection {* Well-ordering *}

lemma less_FinE:
  "[| n < Fin m; !!k. n = Fin k ==> k < m ==> P |] ==> P"
by (induct n) auto

lemma less_InftyE:
  "[| n < Infty; !!k. n = Fin k ==> P |] ==> P"
by (induct n) auto

lemma inat_less_induct:
  assumes prem: "!!n. \<forall>m::inat. m < n --> P m ==> P n" shows "P n"
proof -
  have P_Fin: "!!k. P (Fin k)"
    apply (rule nat_less_induct)
    apply (rule prem, clarify)
    apply (erule less_FinE, simp)
    done
  show ?thesis
  proof (induct n)
    fix nat
    show "P (Fin nat)" by (rule P_Fin)
  next
    show "P Infty"
      apply (rule prem, clarify)
      apply (erule less_InftyE)
      apply (simp add: P_Fin)
      done
  qed
qed

instance inat :: wellorder
proof
  fix P and n
  assume hyp: "(\<And>n\<Colon>inat. (\<And>m\<Colon>inat. m < n \<Longrightarrow> P m) \<Longrightarrow> P n)"
  show "P n" by (blast intro: inat_less_induct hyp)
qed


subsection {* Traditional theorem names *}

lemmas inat_defs = zero_inat_def one_inat_def number_of_inat_def iSuc_def
  plus_inat_def less_eq_inat_def less_inat_def

lemmas inat_splits = inat.splits

end
