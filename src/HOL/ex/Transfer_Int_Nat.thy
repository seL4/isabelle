(*  Title:      HOL/ex/Transfer_Int_Nat.thy
    Author:     Brian Huffman, TU Muenchen
*)

header {* Using the transfer method between nat and int *}

theory Transfer_Int_Nat
imports GCD "~~/src/HOL/Library/Quotient_List"
begin

subsection {* Correspondence relation *}

definition ZN :: "int \<Rightarrow> nat \<Rightarrow> bool"
  where "ZN = (\<lambda>z n. z = of_nat n)"

subsection {* Transfer rules *}

lemma bi_unique_ZN [transfer_rule]: "bi_unique ZN"
  unfolding ZN_def bi_unique_def by simp

lemma right_total_ZN [transfer_rule]: "right_total ZN"
  unfolding ZN_def right_total_def by simp

lemma ZN_0 [transfer_rule]: "ZN 0 0"
  unfolding ZN_def by simp

lemma ZN_1 [transfer_rule]: "ZN 1 1"
  unfolding ZN_def by simp

lemma ZN_add [transfer_rule]: "(ZN ===> ZN ===> ZN) (op +) (op +)"
  unfolding fun_rel_def ZN_def by simp

lemma ZN_mult [transfer_rule]: "(ZN ===> ZN ===> ZN) (op *) (op *)"
  unfolding fun_rel_def ZN_def by (simp add: int_mult)

lemma ZN_diff [transfer_rule]: "(ZN ===> ZN ===> ZN) tsub (op -)"
  unfolding fun_rel_def ZN_def tsub_def by (simp add: zdiff_int)

lemma ZN_power [transfer_rule]: "(ZN ===> op = ===> ZN) (op ^) (op ^)"
  unfolding fun_rel_def ZN_def by (simp add: int_power)

lemma ZN_nat_id [transfer_rule]: "(ZN ===> op =) nat id"
  unfolding fun_rel_def ZN_def by simp

lemma ZN_id_int [transfer_rule]: "(ZN ===> op =) id int"
  unfolding fun_rel_def ZN_def by simp

lemma ZN_All [transfer_rule]:
  "((ZN ===> op =) ===> op =) (Ball {0..}) All"
  unfolding fun_rel_def ZN_def by (auto dest: zero_le_imp_eq_int)

lemma ZN_transfer_forall [transfer_rule]:
  "((ZN ===> op =) ===> op =) (transfer_bforall (\<lambda>x. 0 \<le> x)) transfer_forall"
  unfolding transfer_forall_def transfer_bforall_def
  unfolding fun_rel_def ZN_def by (auto dest: zero_le_imp_eq_int)

lemma ZN_Ex [transfer_rule]: "((ZN ===> op =) ===> op =) (Bex {0..}) Ex"
  unfolding fun_rel_def ZN_def Bex_def atLeast_iff
  by (metis zero_le_imp_eq_int zero_zle_int)

lemma ZN_le [transfer_rule]: "(ZN ===> ZN ===> op =) (op \<le>) (op \<le>)"
  unfolding fun_rel_def ZN_def by simp

lemma ZN_less [transfer_rule]: "(ZN ===> ZN ===> op =) (op <) (op <)"
  unfolding fun_rel_def ZN_def by simp

lemma ZN_eq [transfer_rule]: "(ZN ===> ZN ===> op =) (op =) (op =)"
  unfolding fun_rel_def ZN_def by simp

lemma ZN_Suc [transfer_rule]: "(ZN ===> ZN) (\<lambda>x. x + 1) Suc"
  unfolding fun_rel_def ZN_def by simp

lemma ZN_numeral [transfer_rule]:
  "(op = ===> ZN) numeral numeral"
  unfolding fun_rel_def ZN_def by simp

lemma ZN_dvd [transfer_rule]: "(ZN ===> ZN ===> op =) (op dvd) (op dvd)"
  unfolding fun_rel_def ZN_def by (simp add: zdvd_int)

lemma ZN_div [transfer_rule]: "(ZN ===> ZN ===> ZN) (op div) (op div)"
  unfolding fun_rel_def ZN_def by (simp add: zdiv_int)

lemma ZN_mod [transfer_rule]: "(ZN ===> ZN ===> ZN) (op mod) (op mod)"
  unfolding fun_rel_def ZN_def by (simp add: zmod_int)

lemma ZN_gcd [transfer_rule]: "(ZN ===> ZN ===> ZN) gcd gcd"
  unfolding fun_rel_def ZN_def by (simp add: transfer_int_nat_gcd)

text {* For derived operations, we can use the @{text "transfer_prover"}
  method to help generate transfer rules. *}

lemma ZN_listsum [transfer_rule]: "(list_all2 ZN ===> ZN) listsum listsum"
  unfolding listsum_def [abs_def] by transfer_prover

subsection {* Transfer examples *}

lemma
  assumes "\<And>i::int. 0 \<le> i \<Longrightarrow> i + 0 = i"
  shows "\<And>i::nat. i + 0 = i"
apply transfer
apply fact
done

lemma
  assumes "\<And>i k::int. \<lbrakk>0 \<le> i; 0 \<le> k; i < k\<rbrakk> \<Longrightarrow> \<exists>j\<in>{0..}. i + j = k"
  shows "\<And>i k::nat. i < k \<Longrightarrow> \<exists>j. i + j = k"
apply transfer
apply fact
done

lemma
  assumes "\<forall>x\<in>{0::int..}. \<forall>y\<in>{0..}. x * y div y = x"
  shows "\<forall>x y :: nat. x * y div y = x"
apply transfer
apply fact
done

lemma
  assumes "\<And>m n::int. \<lbrakk>0 \<le> m; 0 \<le> n; m * n = 0\<rbrakk> \<Longrightarrow> m = 0 \<or> n = 0"
  shows "m * n = (0::nat) \<Longrightarrow> m = 0 \<or> n = 0"
apply transfer
apply fact
done

lemma
  assumes "\<forall>x\<in>{0::int..}. \<exists>y\<in>{0..}. \<exists>z\<in>{0..}. x + 3 * y = 5 * z"
  shows "\<forall>x::nat. \<exists>y z. x + 3 * y = 5 * z"
apply transfer
apply fact
done

text {* The @{text "fixing"} option prevents generalization over the free
  variable @{text "n"}, allowing the local transfer rule to be used. *}

lemma
  assumes [transfer_rule]: "ZN x n"
  assumes "\<forall>i\<in>{0..}. i < x \<longrightarrow> 2 * i < 3 * x"
  shows "\<forall>i. i < n \<longrightarrow> 2 * i < 3 * n"
apply (transfer fixing: n)
apply fact
done

lemma
  assumes "gcd (2^i) (3^j) = (1::int)"
  shows "gcd (2^i) (3^j) = (1::nat)"
apply (transfer fixing: i j)
apply fact
done

lemma
  assumes "\<And>x y z::int. \<lbrakk>0 \<le> x; 0 \<le> y; 0 \<le> z\<rbrakk> \<Longrightarrow> 
    listsum [x, y, z] = 0 \<longleftrightarrow> list_all (\<lambda>x. x = 0) [x, y, z]"
  shows "listsum [x, y, z] = (0::nat) \<longleftrightarrow> list_all (\<lambda>x. x = 0) [x, y, z]"
apply transfer
apply fact
done

text {* Quantifiers over higher types (e.g. @{text "nat list"}) may
  generate @{text "Domainp"} assumptions when transferred. *}

lemma
  assumes "\<And>xs::int list. Domainp (list_all2 ZN) xs \<Longrightarrow>
    (listsum xs = 0) = list_all (\<lambda>x. x = 0) xs"
  shows "listsum xs = (0::nat) \<longleftrightarrow> list_all (\<lambda>x. x = 0) xs"
apply transfer
apply fact
done

text {* Equality on a higher type can be transferred if the relations
  involved are bi-unique. *}

lemma
  assumes "\<And>xs\<Colon>int list. \<lbrakk>Domainp (list_all2 ZN) xs; xs \<noteq> []\<rbrakk> \<Longrightarrow>
    listsum xs < listsum (map (\<lambda>x. x + 1) xs)"
  shows "xs \<noteq> [] \<Longrightarrow> listsum xs < listsum (map Suc xs)"
apply transfer
apply fact
done

end
