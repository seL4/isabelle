(*  Title:      HOL/ex/Transfer_Int_Nat.thy
    Author:     Brian Huffman, TU Muenchen
*)

section \<open>Using the transfer method between nat and int\<close>

theory Transfer_Int_Nat
imports Main
begin

subsection \<open>Correspondence relation\<close>

definition ZN :: "int \<Rightarrow> nat \<Rightarrow> bool"
  where "ZN = (\<lambda>z n. z = of_nat n)"

subsection \<open>Transfer domain rules\<close>

lemma Domainp_ZN [transfer_domain_rule]: "Domainp ZN = (\<lambda>x. x \<ge> 0)"
  unfolding ZN_def Domainp_iff[abs_def] by (auto intro: zero_le_imp_eq_int)

subsection \<open>Transfer rules\<close>

context includes lifting_syntax
begin

lemma bi_unique_ZN [transfer_rule]: "bi_unique ZN"
  unfolding ZN_def bi_unique_def by simp

lemma right_total_ZN [transfer_rule]: "right_total ZN"
  unfolding ZN_def right_total_def by simp

lemma ZN_0 [transfer_rule]: "ZN 0 0"
  unfolding ZN_def by simp

lemma ZN_1 [transfer_rule]: "ZN 1 1"
  unfolding ZN_def by simp

lemma ZN_add [transfer_rule]: "(ZN ===> ZN ===> ZN) (+) (+)"
  unfolding rel_fun_def ZN_def by simp

lemma ZN_mult [transfer_rule]: "(ZN ===> ZN ===> ZN) (( * )) (( * ))"
  unfolding rel_fun_def ZN_def by simp

definition tsub :: "int \<Rightarrow> int \<Rightarrow> int"
  where "tsub k l = max 0 (k - l)"

lemma ZN_diff [transfer_rule]: "(ZN ===> ZN ===> ZN) tsub (-)"
  unfolding rel_fun_def ZN_def by (auto simp add: of_nat_diff tsub_def)

lemma ZN_power [transfer_rule]: "(ZN ===> (=) ===> ZN) (^) (^)"
  unfolding rel_fun_def ZN_def by simp

lemma ZN_nat_id [transfer_rule]: "(ZN ===> (=)) nat id"
  unfolding rel_fun_def ZN_def by simp

lemma ZN_id_int [transfer_rule]: "(ZN ===> (=)) id int"
  unfolding rel_fun_def ZN_def by simp

lemma ZN_All [transfer_rule]:
  "((ZN ===> (=)) ===> (=)) (Ball {0..}) All"
  unfolding rel_fun_def ZN_def by (auto dest: zero_le_imp_eq_int)

lemma ZN_transfer_forall [transfer_rule]:
  "((ZN ===> (=)) ===> (=)) (transfer_bforall (\<lambda>x. 0 \<le> x)) transfer_forall"
  unfolding transfer_forall_def transfer_bforall_def
  unfolding rel_fun_def ZN_def by (auto dest: zero_le_imp_eq_int)

lemma ZN_Ex [transfer_rule]: "((ZN ===> (=)) ===> (=)) (Bex {0..}) Ex"
  unfolding rel_fun_def ZN_def Bex_def atLeast_iff
  by (metis zero_le_imp_eq_int of_nat_0_le_iff)

lemma ZN_le [transfer_rule]: "(ZN ===> ZN ===> (=)) (\<le>) (\<le>)"
  unfolding rel_fun_def ZN_def by simp

lemma ZN_less [transfer_rule]: "(ZN ===> ZN ===> (=)) (<) (<)"
  unfolding rel_fun_def ZN_def by simp

lemma ZN_eq [transfer_rule]: "(ZN ===> ZN ===> (=)) (=) (=)"
  unfolding rel_fun_def ZN_def by simp

lemma ZN_Suc [transfer_rule]: "(ZN ===> ZN) (\<lambda>x. x + 1) Suc"
  unfolding rel_fun_def ZN_def by simp

lemma ZN_numeral [transfer_rule]:
  "((=) ===> ZN) numeral numeral"
  unfolding rel_fun_def ZN_def by simp

lemma ZN_dvd [transfer_rule]: "(ZN ===> ZN ===> (=)) (dvd) (dvd)"
  unfolding rel_fun_def ZN_def by simp

lemma ZN_div [transfer_rule]: "(ZN ===> ZN ===> ZN) (div) (div)"
  unfolding rel_fun_def ZN_def by (simp add: zdiv_int)

lemma ZN_mod [transfer_rule]: "(ZN ===> ZN ===> ZN) (mod) (mod)"
  unfolding rel_fun_def ZN_def by (simp add: zmod_int)

lemma ZN_gcd [transfer_rule]: "(ZN ===> ZN ===> ZN) gcd gcd"
  unfolding rel_fun_def ZN_def by (simp add: gcd_int_def)

lemma ZN_atMost [transfer_rule]:
  "(ZN ===> rel_set ZN) (atLeastAtMost 0) atMost"
  unfolding rel_fun_def ZN_def rel_set_def
  by (clarsimp simp add: Bex_def, arith)

lemma ZN_atLeastAtMost [transfer_rule]:
  "(ZN ===> ZN ===> rel_set ZN) atLeastAtMost atLeastAtMost"
  unfolding rel_fun_def ZN_def rel_set_def
  by (clarsimp simp add: Bex_def, arith)

lemma ZN_sum [transfer_rule]:
  "bi_unique A \<Longrightarrow> ((A ===> ZN) ===> rel_set A ===> ZN) sum sum"
  apply (intro rel_funI)
  apply (erule (1) bi_unique_rel_set_lemma)
  apply (simp add: sum.reindex int_sum ZN_def rel_fun_def)
  apply (rule sum.cong)
  apply simp_all
  done

text \<open>For derived operations, we can use the \<open>transfer_prover\<close>
  method to help generate transfer rules.\<close>

lemma ZN_sum_list [transfer_rule]: "(list_all2 ZN ===> ZN) sum_list sum_list"
  by transfer_prover

end

subsection \<open>Transfer examples\<close>

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

text \<open>The \<open>fixing\<close> option prevents generalization over the free
  variable \<open>n\<close>, allowing the local transfer rule to be used.\<close>

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
    sum_list [x, y, z] = 0 \<longleftrightarrow> list_all (\<lambda>x. x = 0) [x, y, z]"
  shows "sum_list [x, y, z] = (0::nat) \<longleftrightarrow> list_all (\<lambda>x. x = 0) [x, y, z]"
apply transfer
apply fact
done

text \<open>Quantifiers over higher types (e.g. \<open>nat list\<close>) are
  transferred to a readable formula thanks to the transfer domain rule @{thm Domainp_ZN}\<close>

lemma
  assumes "\<And>xs::int list. list_all (\<lambda>x. x \<ge> 0) xs \<Longrightarrow>
    (sum_list xs = 0) = list_all (\<lambda>x. x = 0) xs"
  shows "sum_list xs = (0::nat) \<longleftrightarrow> list_all (\<lambda>x. x = 0) xs"
apply transfer
apply fact
done

text \<open>Equality on a higher type can be transferred if the relations
  involved are bi-unique.\<close>

lemma
  assumes "\<And>xs::int list. \<lbrakk>list_all (\<lambda>x. x \<ge> 0) xs; xs \<noteq> []\<rbrakk> \<Longrightarrow>
    sum_list xs < sum_list (map (\<lambda>x. x + 1) xs)"
  shows "xs \<noteq> [] \<Longrightarrow> sum_list xs < sum_list (map Suc xs)"
apply transfer
apply fact
done

end
