(*  Title       : HyperNat.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 1998  University of Cambridge

Converted to Isar and polished by lcp    
*)

header{*Hypernatural numbers*}

theory HyperNat
imports StarDef
begin

types hypnat = "nat star"

abbreviation
  hypnat_of_nat :: "nat => nat star" where
  "hypnat_of_nat == star_of"

definition
  hSuc :: "hypnat => hypnat" where
  hSuc_def [transfer_unfold, code del]: "hSuc = *f* Suc"

subsection{*Properties Transferred from Naturals*}

lemma hSuc_not_zero [iff]: "\<And>m. hSuc m \<noteq> 0"
by transfer (rule Suc_not_Zero)

lemma zero_not_hSuc [iff]: "\<And>m. 0 \<noteq> hSuc m"
by transfer (rule Zero_not_Suc)

lemma hSuc_hSuc_eq [iff]: "\<And>m n. (hSuc m = hSuc n) = (m = n)"
by transfer (rule nat.inject)

lemma zero_less_hSuc [iff]: "\<And>n. 0 < hSuc n"
by transfer (rule zero_less_Suc)

lemma hypnat_minus_zero [simp]: "!!z. z - z = (0::hypnat)"
by transfer (rule diff_self_eq_0)

lemma hypnat_diff_0_eq_0 [simp]: "!!n. (0::hypnat) - n = 0"
by transfer (rule diff_0_eq_0)

lemma hypnat_add_is_0 [iff]: "!!m n. (m+n = (0::hypnat)) = (m=0 & n=0)"
by transfer (rule add_is_0)

lemma hypnat_diff_diff_left: "!!i j k. (i::hypnat) - j - k = i - (j+k)"
by transfer (rule diff_diff_left)

lemma hypnat_diff_commute: "!!i j k. (i::hypnat) - j - k = i-k-j"
by transfer (rule diff_commute)

lemma hypnat_diff_add_inverse [simp]: "!!m n. ((n::hypnat) + m) - n = m"
by transfer (rule diff_add_inverse)

lemma hypnat_diff_add_inverse2 [simp]:  "!!m n. ((m::hypnat) + n) - n = m"
by transfer (rule diff_add_inverse2)

lemma hypnat_diff_cancel [simp]: "!!k m n. ((k::hypnat) + m) - (k+n) = m - n"
by transfer (rule diff_cancel)

lemma hypnat_diff_cancel2 [simp]: "!!k m n. ((m::hypnat) + k) - (n+k) = m - n"
by transfer (rule diff_cancel2)

lemma hypnat_diff_add_0 [simp]: "!!m n. (n::hypnat) - (n+m) = (0::hypnat)"
by transfer (rule diff_add_0)

lemma hypnat_diff_mult_distrib: "!!k m n. ((m::hypnat) - n) * k = (m * k) - (n * k)"
by transfer (rule diff_mult_distrib)

lemma hypnat_diff_mult_distrib2: "!!k m n. (k::hypnat) * (m - n) = (k * m) - (k * n)"
by transfer (rule diff_mult_distrib2)

lemma hypnat_le_zero_cancel [iff]: "!!n. (n \<le> (0::hypnat)) = (n = 0)"
by transfer (rule le_0_eq)

lemma hypnat_mult_is_0 [simp]: "!!m n. (m*n = (0::hypnat)) = (m=0 | n=0)"
by transfer (rule mult_is_0)

lemma hypnat_diff_is_0_eq [simp]: "!!m n. ((m::hypnat) - n = 0) = (m \<le> n)"
by transfer (rule diff_is_0_eq)

lemma hypnat_not_less0 [iff]: "!!n. ~ n < (0::hypnat)"
by transfer (rule not_less0)

lemma hypnat_less_one [iff]:
      "!!n. (n < (1::hypnat)) = (n=0)"
by transfer (rule less_one)

lemma hypnat_add_diff_inverse: "!!m n. ~ m<n ==> n+(m-n) = (m::hypnat)"
by transfer (rule add_diff_inverse)

lemma hypnat_le_add_diff_inverse [simp]: "!!m n. n \<le> m ==> n+(m-n) = (m::hypnat)"
by transfer (rule le_add_diff_inverse)

lemma hypnat_le_add_diff_inverse2 [simp]: "!!m n. n\<le>m ==> (m-n)+n = (m::hypnat)"
by transfer (rule le_add_diff_inverse2)

declare hypnat_le_add_diff_inverse2 [OF order_less_imp_le]

lemma hypnat_le0 [iff]: "!!n. (0::hypnat) \<le> n"
by transfer (rule le0)

lemma hypnat_le_add1 [simp]: "!!x n. (x::hypnat) \<le> x + n"
by transfer (rule le_add1)

lemma hypnat_add_self_le [simp]: "!!x n. (x::hypnat) \<le> n + x"
by transfer (rule le_add2)

lemma hypnat_add_one_self_less [simp]: "(x::hypnat) < x + (1::hypnat)"
by (insert add_strict_left_mono [OF zero_less_one], auto)

lemma hypnat_neq0_conv [iff]: "!!n. (n \<noteq> 0) = (0 < (n::hypnat))"
by transfer (rule neq0_conv)

lemma hypnat_gt_zero_iff: "((0::hypnat) < n) = ((1::hypnat) \<le> n)"
by (auto simp add: linorder_not_less [symmetric])

lemma hypnat_gt_zero_iff2: "(0 < n) = (\<exists>m. n = m + (1::hypnat))"
apply safe
 apply (rule_tac x = "n - (1::hypnat) " in exI)
 apply (simp add: hypnat_gt_zero_iff) 
apply (insert add_le_less_mono [OF _ zero_less_one, of 0], auto) 
done

lemma hypnat_add_self_not_less: "~ (x + y < (x::hypnat))"
by (simp add: linorder_not_le [symmetric] add_commute [of x]) 

lemma hypnat_diff_split:
    "P(a - b::hypnat) = ((a<b --> P 0) & (ALL d. a = b + d --> P d))"
    -- {* elimination of @{text -} on @{text hypnat} *}
proof (cases "a<b" rule: case_split)
  case True
    thus ?thesis
      by (auto simp add: hypnat_add_self_not_less order_less_imp_le 
                         hypnat_diff_is_0_eq [THEN iffD2])
next
  case False
    thus ?thesis
      by (auto simp add: linorder_not_less dest: order_le_less_trans) 
qed

subsection{*Properties of the set of embedded natural numbers*}

lemma of_nat_eq_star_of [simp]: "of_nat = star_of"
proof
  fix n :: nat
  show "of_nat n = star_of n" by transfer simp
qed

lemma Nats_eq_Standard: "(Nats :: nat star set) = Standard"
by (auto simp add: Nats_def Standard_def)

lemma hypnat_of_nat_mem_Nats [simp]: "hypnat_of_nat n \<in> Nats"
by (simp add: Nats_eq_Standard)

lemma hypnat_of_nat_one [simp]: "hypnat_of_nat (Suc 0) = (1::hypnat)"
by transfer simp

lemma hypnat_of_nat_Suc [simp]:
     "hypnat_of_nat (Suc n) = hypnat_of_nat n + (1::hypnat)"
by transfer simp

lemma of_nat_eq_add [rule_format]:
     "\<forall>d::hypnat. of_nat m = of_nat n + d --> d \<in> range of_nat"
apply (induct n) 
apply (auto simp add: add_assoc) 
apply (case_tac x) 
apply (auto simp add: add_commute [of 1]) 
done

lemma Nats_diff [simp]: "[|a \<in> Nats; b \<in> Nats|] ==> (a-b :: hypnat) \<in> Nats"
by (simp add: Nats_eq_Standard)


subsection{*Infinite Hypernatural Numbers -- @{term HNatInfinite}*}

definition
  (* the set of infinite hypernatural numbers *)
  HNatInfinite :: "hypnat set" where
  "HNatInfinite = {n. n \<notin> Nats}"

lemma Nats_not_HNatInfinite_iff: "(x \<in> Nats) = (x \<notin> HNatInfinite)"
by (simp add: HNatInfinite_def)

lemma HNatInfinite_not_Nats_iff: "(x \<in> HNatInfinite) = (x \<notin> Nats)"
by (simp add: HNatInfinite_def)

lemma star_of_neq_HNatInfinite: "N \<in> HNatInfinite \<Longrightarrow> star_of n \<noteq> N"
by (auto simp add: HNatInfinite_def Nats_eq_Standard)

lemma star_of_Suc_lessI:
  "\<And>N. \<lbrakk>star_of n < N; star_of (Suc n) \<noteq> N\<rbrakk> \<Longrightarrow> star_of (Suc n) < N"
by transfer (rule Suc_lessI)

lemma star_of_less_HNatInfinite:
  assumes N: "N \<in> HNatInfinite"
  shows "star_of n < N"
proof (induct n)
  case 0
  from N have "star_of 0 \<noteq> N" by (rule star_of_neq_HNatInfinite)
  thus "star_of 0 < N" by simp
next
  case (Suc n)
  from N have "star_of (Suc n) \<noteq> N" by (rule star_of_neq_HNatInfinite)
  with Suc show "star_of (Suc n) < N" by (rule star_of_Suc_lessI)
qed

lemma star_of_le_HNatInfinite: "N \<in> HNatInfinite \<Longrightarrow> star_of n \<le> N"
by (rule star_of_less_HNatInfinite [THEN order_less_imp_le])

subsubsection {* Closure Rules *}

lemma Nats_less_HNatInfinite: "\<lbrakk>x \<in> Nats; y \<in> HNatInfinite\<rbrakk> \<Longrightarrow> x < y"
by (auto simp add: Nats_def star_of_less_HNatInfinite)

lemma Nats_le_HNatInfinite: "\<lbrakk>x \<in> Nats; y \<in> HNatInfinite\<rbrakk> \<Longrightarrow> x \<le> y"
by (rule Nats_less_HNatInfinite [THEN order_less_imp_le])

lemma zero_less_HNatInfinite: "x \<in> HNatInfinite \<Longrightarrow> 0 < x"
by (simp add: Nats_less_HNatInfinite)

lemma one_less_HNatInfinite: "x \<in> HNatInfinite \<Longrightarrow> 1 < x"
by (simp add: Nats_less_HNatInfinite)

lemma one_le_HNatInfinite: "x \<in> HNatInfinite \<Longrightarrow> 1 \<le> x"
by (simp add: Nats_le_HNatInfinite)

lemma zero_not_mem_HNatInfinite [simp]: "0 \<notin> HNatInfinite"
by (simp add: HNatInfinite_def)

lemma Nats_downward_closed:
  "\<lbrakk>x \<in> Nats; (y::hypnat) \<le> x\<rbrakk> \<Longrightarrow> y \<in> Nats"
apply (simp only: linorder_not_less [symmetric])
apply (erule contrapos_np)
apply (drule HNatInfinite_not_Nats_iff [THEN iffD2])
apply (erule (1) Nats_less_HNatInfinite)
done

lemma HNatInfinite_upward_closed:
  "\<lbrakk>x \<in> HNatInfinite; x \<le> y\<rbrakk> \<Longrightarrow> y \<in> HNatInfinite"
apply (simp only: HNatInfinite_not_Nats_iff)
apply (erule contrapos_nn)
apply (erule (1) Nats_downward_closed)
done

lemma HNatInfinite_add: "x \<in> HNatInfinite \<Longrightarrow> x + y \<in> HNatInfinite"
apply (erule HNatInfinite_upward_closed)
apply (rule hypnat_le_add1)
done

lemma HNatInfinite_add_one: "x \<in> HNatInfinite \<Longrightarrow> x + 1 \<in> HNatInfinite"
by (rule HNatInfinite_add)

lemma HNatInfinite_diff:
  "\<lbrakk>x \<in> HNatInfinite; y \<in> Nats\<rbrakk> \<Longrightarrow> x - y \<in> HNatInfinite"
apply (frule (1) Nats_le_HNatInfinite)
apply (simp only: HNatInfinite_not_Nats_iff)
apply (erule contrapos_nn)
apply (drule (1) Nats_add, simp)
done

lemma HNatInfinite_is_Suc: "x \<in> HNatInfinite ==> \<exists>y. x = y + (1::hypnat)"
apply (rule_tac x = "x - (1::hypnat) " in exI)
apply (simp add: Nats_le_HNatInfinite)
done


subsection{*Existence of an infinite hypernatural number*}

definition
  (* omega is in fact an infinite hypernatural number = [<1,2,3,...>] *)
  whn :: hypnat where
  hypnat_omega_def: "whn = star_n (%n::nat. n)"

lemma hypnat_of_nat_neq_whn: "hypnat_of_nat n \<noteq> whn"
by (simp add: hypnat_omega_def star_of_def star_n_eq_iff)

lemma whn_neq_hypnat_of_nat: "whn \<noteq> hypnat_of_nat n"
by (simp add: hypnat_omega_def star_of_def star_n_eq_iff)

lemma whn_not_Nats [simp]: "whn \<notin> Nats"
by (simp add: Nats_def image_def whn_neq_hypnat_of_nat)

lemma HNatInfinite_whn [simp]: "whn \<in> HNatInfinite"
by (simp add: HNatInfinite_def)

lemma lemma_unbounded_set [simp]: "{n::nat. m < n} \<in> FreeUltrafilterNat"
apply (insert finite_atMost [of m])
apply (drule FreeUltrafilterNat.finite)
apply (drule FreeUltrafilterNat.not_memD)
apply (simp add: Collect_neg_eq [symmetric] linorder_not_le atMost_def)
done

lemma Compl_Collect_le: "- {n::nat. N \<le> n} = {n. n < N}"
by (simp add: Collect_neg_eq [symmetric] linorder_not_le) 

lemma hypnat_of_nat_eq:
     "hypnat_of_nat m  = star_n (%n::nat. m)"
by (simp add: star_of_def)

lemma SHNat_eq: "Nats = {n. \<exists>N. n = hypnat_of_nat N}"
by (simp add: Nats_def image_def)

lemma Nats_less_whn: "n \<in> Nats \<Longrightarrow> n < whn"
by (simp add: Nats_less_HNatInfinite)

lemma Nats_le_whn: "n \<in> Nats \<Longrightarrow> n \<le> whn"
by (simp add: Nats_le_HNatInfinite)

lemma hypnat_of_nat_less_whn [simp]: "hypnat_of_nat n < whn"
by (simp add: Nats_less_whn)

lemma hypnat_of_nat_le_whn [simp]: "hypnat_of_nat n \<le> whn"
by (simp add: Nats_le_whn)

lemma hypnat_zero_less_hypnat_omega [simp]: "0 < whn"
by (simp add: Nats_less_whn)

lemma hypnat_one_less_hypnat_omega [simp]: "1 < whn"
by (simp add: Nats_less_whn)


subsubsection{*Alternative characterization of the set of infinite hypernaturals*}

text{* @{term "HNatInfinite = {N. \<forall>n \<in> Nats. n < N}"}*}

(*??delete? similar reasoning in hypnat_omega_gt_SHNat above*)
lemma HNatInfinite_FreeUltrafilterNat_lemma:
  assumes "\<forall>N::nat. {n. f n \<noteq> N} \<in> FreeUltrafilterNat"
  shows "{n. N < f n} \<in> FreeUltrafilterNat"
apply (induct N)
using assms
apply (drule_tac x = 0 in spec, simp)
using assms
apply (drule_tac x = "Suc N" in spec)
apply (elim ultra, auto)
done

lemma HNatInfinite_iff: "HNatInfinite = {N. \<forall>n \<in> Nats. n < N}"
apply (safe intro!: Nats_less_HNatInfinite)
apply (auto simp add: HNatInfinite_def)
done


subsubsection{*Alternative Characterization of @{term HNatInfinite} using 
Free Ultrafilter*}

lemma HNatInfinite_FreeUltrafilterNat:
     "star_n X \<in> HNatInfinite ==> \<forall>u. {n. u < X n}:  FreeUltrafilterNat"
apply (auto simp add: HNatInfinite_iff SHNat_eq)
apply (drule_tac x="star_of u" in spec, simp)
apply (simp add: star_of_def star_less_def starP2_star_n)
done

lemma FreeUltrafilterNat_HNatInfinite:
     "\<forall>u. {n. u < X n}:  FreeUltrafilterNat ==> star_n X \<in> HNatInfinite"
by (auto simp add: star_less_def starP2_star_n HNatInfinite_iff SHNat_eq hypnat_of_nat_eq)

lemma HNatInfinite_FreeUltrafilterNat_iff:
     "(star_n X \<in> HNatInfinite) = (\<forall>u. {n. u < X n}:  FreeUltrafilterNat)"
by (rule iffI [OF HNatInfinite_FreeUltrafilterNat 
                 FreeUltrafilterNat_HNatInfinite])

subsection {* Embedding of the Hypernaturals into other types *}

definition
  of_hypnat :: "hypnat \<Rightarrow> 'a::semiring_1_cancel star" where
  of_hypnat_def [transfer_unfold, code del]: "of_hypnat = *f* of_nat"

lemma of_hypnat_0 [simp]: "of_hypnat 0 = 0"
by transfer (rule of_nat_0)

lemma of_hypnat_1 [simp]: "of_hypnat 1 = 1"
by transfer (rule of_nat_1)

lemma of_hypnat_hSuc: "\<And>m. of_hypnat (hSuc m) = 1 + of_hypnat m"
by transfer (rule of_nat_Suc)

lemma of_hypnat_add [simp]:
  "\<And>m n. of_hypnat (m + n) = of_hypnat m + of_hypnat n"
by transfer (rule of_nat_add)

lemma of_hypnat_mult [simp]:
  "\<And>m n. of_hypnat (m * n) = of_hypnat m * of_hypnat n"
by transfer (rule of_nat_mult)

lemma of_hypnat_less_iff [simp]:
  "\<And>m n. (of_hypnat m < (of_hypnat n::'a::ordered_semidom star)) = (m < n)"
by transfer (rule of_nat_less_iff)

lemma of_hypnat_0_less_iff [simp]:
  "\<And>n. (0 < (of_hypnat n::'a::ordered_semidom star)) = (0 < n)"
by transfer (rule of_nat_0_less_iff)

lemma of_hypnat_less_0_iff [simp]:
  "\<And>m. \<not> (of_hypnat m::'a::ordered_semidom star) < 0"
by transfer (rule of_nat_less_0_iff)

lemma of_hypnat_le_iff [simp]:
  "\<And>m n. (of_hypnat m \<le> (of_hypnat n::'a::ordered_semidom star)) = (m \<le> n)"
by transfer (rule of_nat_le_iff)

lemma of_hypnat_0_le_iff [simp]:
  "\<And>n. 0 \<le> (of_hypnat n::'a::ordered_semidom star)"
by transfer (rule of_nat_0_le_iff)

lemma of_hypnat_le_0_iff [simp]:
  "\<And>m. ((of_hypnat m::'a::ordered_semidom star) \<le> 0) = (m = 0)"
by transfer (rule of_nat_le_0_iff)

lemma of_hypnat_eq_iff [simp]:
  "\<And>m n. (of_hypnat m = (of_hypnat n::'a::ordered_semidom star)) = (m = n)"
by transfer (rule of_nat_eq_iff)

lemma of_hypnat_eq_0_iff [simp]:
  "\<And>m. ((of_hypnat m::'a::ordered_semidom star) = 0) = (m = 0)"
by transfer (rule of_nat_eq_0_iff)

lemma HNatInfinite_of_hypnat_gt_zero:
  "N \<in> HNatInfinite \<Longrightarrow> (0::'a::ordered_semidom star) < of_hypnat N"
by (rule ccontr, simp add: linorder_not_less)

end
