(*  Title:      HOLCF/NatIso.thy
    ID:         $Id$
    Author:     Brian Huffman
*)

header {* Isomorphisms of the Natural Numbers *}

theory NatIso
imports Parity
begin

subsection {* Isomorphism between naturals and sums of naturals *}

primrec
  sum2nat  :: "nat + nat \<Rightarrow> nat"
where
  "sum2nat (Inl a) = a + a"
| "sum2nat (Inr b) = Suc (b + b)"

primrec
  nat2sum  :: "nat \<Rightarrow> nat + nat"
where
  "nat2sum 0 = Inl 0"
| "nat2sum (Suc n) = (case nat2sum n of
    Inl a \<Rightarrow> Inr a | Inr b \<Rightarrow> Inl (Suc b))"

lemma nat2sum_sum2nat [simp]: "nat2sum (sum2nat x) = x"
by (induct x, rule_tac [!] nat.induct, simp_all)

lemma sum2nat_nat2sum [simp]: "sum2nat (nat2sum n) = n"
by (induct n, auto split: sum.split)

lemma inj_sum2nat: "inj sum2nat"
by (rule inj_on_inverseI, rule nat2sum_sum2nat)

lemma sum2nat_eq_iff [simp]: "sum2nat x = sum2nat y \<longleftrightarrow> x = y"
by (rule inj_sum2nat [THEN inj_eq])

lemma inj_nat2sum: "inj nat2sum"
by (rule inj_on_inverseI, rule sum2nat_nat2sum)

lemma nat2sum_eq_iff [simp]: "nat2sum x = nat2sum y \<longleftrightarrow> x = y"
by (rule inj_nat2sum [THEN inj_eq])

declare sum2nat.simps [simp del]
declare nat2sum.simps [simp del]


subsection {* Isomorphism between naturals and pairs of naturals *}

function
  prod2nat :: "nat \<times> nat \<Rightarrow> nat"
where
  "prod2nat (0, 0) = 0"
| "prod2nat (0, Suc n) = Suc (prod2nat (n, 0))"
| "prod2nat (Suc m, n) = Suc (prod2nat (m, Suc n))"
by pat_completeness auto

termination by (relation
  "inv_image (measure id <*lex*> measure id) (\<lambda>(x, y). (x+y, x))") auto

primrec
  nat2prod :: "nat \<Rightarrow> nat \<times> nat"
where
  "nat2prod 0 = (0, 0)"
| "nat2prod (Suc x) =
    (case nat2prod x of (m, n) \<Rightarrow>
      (case n of 0 \<Rightarrow> (0, Suc m) | Suc n \<Rightarrow> (Suc m, n)))"

lemma nat2prod_prod2nat [simp]: "nat2prod (prod2nat x) = x"
by (induct x, rule prod2nat.induct, simp_all)

lemma prod2nat_nat2prod [simp]: "prod2nat (nat2prod n) = n"
by (induct n, auto split: prod.split nat.split)

lemma inj_prod2nat: "inj prod2nat"
by (rule inj_on_inverseI, rule nat2prod_prod2nat)

lemma prod2nat_eq_iff [simp]: "prod2nat x = prod2nat y \<longleftrightarrow> x = y"
by (rule inj_prod2nat [THEN inj_eq])

lemma inj_nat2prod: "inj nat2prod"
by (rule inj_on_inverseI, rule prod2nat_nat2prod)

lemma nat2prod_eq_iff [simp]: "nat2prod x = nat2prod y \<longleftrightarrow> x = y"
by (rule inj_nat2prod [THEN inj_eq])

subsubsection {* Ordering properties *}

lemma fst_snd_le_prod2nat: "fst x \<le> prod2nat x \<and> snd x \<le> prod2nat x"
by (induct x rule: prod2nat.induct) auto

lemma fst_le_prod2nat: "fst x \<le> prod2nat x"
by (rule fst_snd_le_prod2nat [THEN conjunct1])

lemma snd_le_prod2nat: "snd x \<le> prod2nat x"
by (rule fst_snd_le_prod2nat [THEN conjunct2])

lemma le_prod2nat_1: "a \<le> prod2nat (a, b)"
using fst_le_prod2nat [where x="(a, b)"] by simp

lemma le_prod2nat_2: "b \<le> prod2nat (a, b)"
using snd_le_prod2nat [where x="(a, b)"] by simp

declare prod2nat.simps [simp del]
declare nat2prod.simps [simp del]


subsection {* Isomorphism between naturals and finite sets of naturals *}

subsubsection {* Preliminaries *}

lemma finite_vimage_Suc_iff: "finite (Suc -` F) \<longleftrightarrow> finite F"
apply (safe intro!: finite_vimageI inj_Suc)
apply (rule finite_subset [where B="insert 0 (Suc ` Suc -` F)"])
apply (rule subsetI, case_tac x, simp, simp)
apply (rule finite_insert [THEN iffD2])
apply (erule finite_imageI)
done

lemma vimage_Suc_insert_0: "Suc -` insert 0 A = Suc -` A"
by auto

lemma vimage_Suc_insert_Suc:
  "Suc -` insert (Suc n) A = insert n (Suc -` A)"
by auto

lemma even_nat_Suc_div_2: "even x \<Longrightarrow> Suc x div 2 = x div 2"
by (simp only: numeral_2_eq_2 even_nat_plus_one_div_two)

lemma div2_even_ext_nat:
  "\<lbrakk>x div 2 = y div 2; even x = even y\<rbrakk> \<Longrightarrow> (x::nat) = y"
apply (rule mod_div_equality [of x 2, THEN subst])
apply (rule mod_div_equality [of y 2, THEN subst])
apply (case_tac "even x")
apply (simp add: numeral_2_eq_2 even_nat_equiv_def)
apply (simp add: numeral_2_eq_2 odd_nat_equiv_def)
done

subsubsection {* From sets to naturals *}

definition
  set2nat :: "nat set \<Rightarrow> nat" where
  "set2nat = setsum (op ^ 2)"

lemma set2nat_empty [simp]: "set2nat {} = 0"
by (simp add: set2nat_def)

lemma set2nat_insert [simp]:
  "\<lbrakk>finite A; n \<notin> A\<rbrakk> \<Longrightarrow> set2nat (insert n A) = 2^n + set2nat A"
by (simp add: set2nat_def)

lemma even_set2nat_iff: "finite A \<Longrightarrow> even (set2nat A) = (0 \<notin> A)"
by (unfold set2nat_def, erule finite_induct, auto)

lemma set2nat_vimage_Suc: "set2nat (Suc -` A) = set2nat A div 2"
apply (case_tac "finite A")
apply (erule finite_induct, simp)
apply (case_tac x)
apply (simp add: even_nat_Suc_div_2 even_set2nat_iff vimage_Suc_insert_0)
apply (simp add: finite_vimageI add_commute vimage_Suc_insert_Suc)
apply (simp add: set2nat_def finite_vimage_Suc_iff)
done

lemmas set2nat_div_2 = set2nat_vimage_Suc [symmetric]

subsubsection {* From naturals to sets *}

definition
  nat2set :: "nat \<Rightarrow> nat set" where
  "nat2set x = {n. odd (x div 2 ^ n)}"

lemma nat2set_0 [simp]: "0 \<in> nat2set x \<longleftrightarrow> odd x"
by (simp add: nat2set_def)

lemma nat2set_Suc [simp]:
  "Suc n \<in> nat2set x \<longleftrightarrow> n \<in> nat2set (x div 2)"
by (simp add: nat2set_def div_mult2_eq)

lemma nat2set_zero [simp]: "nat2set 0 = {}"
by (simp add: nat2set_def)

lemma nat2set_div_2: "nat2set (x div 2) = Suc -` nat2set x"
by auto

lemma nat2set_plus_power_2:
  "n \<notin> nat2set z \<Longrightarrow> nat2set (2 ^ n + z) = insert n (nat2set z)"
 apply (induct n arbitrary: z, simp_all)
  apply (rule set_ext, induct_tac x, simp, simp add: even_nat_Suc_div_2)
 apply (rule set_ext, induct_tac x, simp, simp add: add_commute)
done

lemma finite_nat2set [simp]: "finite (nat2set n)"
apply (induct n rule: nat_less_induct)
apply (case_tac "n = 0", simp)
apply (drule_tac x="n div 2" in spec, simp)
apply (simp add: nat2set_div_2)
apply (simp add: finite_vimage_Suc_iff)
done

subsubsection {* Proof of isomorphism *}

lemma set2nat_nat2set [simp]: "set2nat (nat2set n) = n"
apply (induct n rule: nat_less_induct)
apply (case_tac "n = 0", simp)
apply (drule_tac x="n div 2" in spec, simp)
apply (simp add: nat2set_div_2 set2nat_vimage_Suc)
apply (erule div2_even_ext_nat)
apply (simp add: even_set2nat_iff)
done

lemma nat2set_set2nat [simp]: "finite A \<Longrightarrow> nat2set (set2nat A) = A"
apply (erule finite_induct, simp_all)
apply (simp add: nat2set_plus_power_2)
done

lemma inj_nat2set: "inj nat2set"
by (rule inj_on_inverseI, rule set2nat_nat2set)

lemma nat2set_eq_iff [simp]: "nat2set x = nat2set y \<longleftrightarrow> x = y"
by (rule inj_eq [OF inj_nat2set])

lemma inj_on_set2nat: "inj_on set2nat (Collect finite)"
by (rule inj_on_inverseI [where g="nat2set"], simp)

lemma set2nat_eq_iff [simp]:
  "\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow> set2nat A = set2nat B \<longleftrightarrow> A = B"
by (rule iffI, simp add: inj_onD [OF inj_on_set2nat], simp)

subsubsection {* Ordering properties *}

lemma nat_less_power2: "n < 2^n"
by (induct n) simp_all

lemma less_set2nat: "\<lbrakk>finite A; x \<in> A\<rbrakk> \<Longrightarrow> x < set2nat A"
unfolding set2nat_def
apply (rule order_less_le_trans [where y="setsum (op ^ 2) {x}"])
apply (simp add: nat_less_power2)
apply (erule setsum_mono2, simp, simp)
done

end