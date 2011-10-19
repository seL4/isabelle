(*  Title:      HOL/Proofs/Extraction/Greatest_Common_Divisor.thy
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Helmut Schwichtenberg, LMU Muenchen
*)

header {* Greatest common divisor *}

theory Greatest_Common_Divisor
imports QuotRem
begin

theorem greatest_common_divisor:
  "\<And>n::nat. Suc m < n \<Longrightarrow> \<exists>k n1 m1. k * n1 = n \<and> k * m1 = Suc m \<and>
     (\<forall>l l1 l2. l * l1 = n \<longrightarrow> l * l2 = Suc m \<longrightarrow> l \<le> k)"
proof (induct m rule: nat_wf_ind)
  case (1 m n)
  from division obtain r q where h1: "n = Suc m * q + r" and h2: "r \<le> m"
    by iprover
  show ?case
  proof (cases r)
    case 0
    with h1 have "Suc m * q = n" by simp
    moreover have "Suc m * 1 = Suc m" by simp
    moreover {
      fix l2 have "\<And>l l1. l * l1 = n \<Longrightarrow> l * l2 = Suc m \<Longrightarrow> l \<le> Suc m"
        by (cases l2) simp_all }
    ultimately show ?thesis by iprover
  next
    case (Suc nat)
    with h2 have h: "nat < m" by simp
    moreover from h have "Suc nat < Suc m" by simp
    ultimately have "\<exists>k m1 r1. k * m1 = Suc m \<and> k * r1 = Suc nat \<and>
      (\<forall>l l1 l2. l * l1 = Suc m \<longrightarrow> l * l2 = Suc nat \<longrightarrow> l \<le> k)"
      by (rule 1)
    then obtain k m1 r1 where
      h1': "k * m1 = Suc m"
      and h2': "k * r1 = Suc nat"
      and h3': "\<And>l l1 l2. l * l1 = Suc m \<Longrightarrow> l * l2 = Suc nat \<Longrightarrow> l \<le> k"
      by iprover
    have mn: "Suc m < n" by (rule 1)
    from h1 h1' h2' Suc have "k * (m1 * q + r1) = n" 
      by (simp add: add_mult_distrib2 nat_mult_assoc [symmetric])
    moreover have "\<And>l l1 l2. l * l1 = n \<Longrightarrow> l * l2 = Suc m \<Longrightarrow> l \<le> k"
    proof -
      fix l l1 l2
      assume ll1n: "l * l1 = n"
      assume ll2m: "l * l2 = Suc m"
      moreover have "l * (l1 - l2 * q) = Suc nat"
        by (simp add: diff_mult_distrib2 h1 Suc [symmetric] mn ll1n ll2m [symmetric])
      ultimately show "l \<le> k" by (rule h3')
    qed
    ultimately show ?thesis using h1' by iprover
  qed
qed

extract greatest_common_divisor

text {*
The extracted program for computing the greatest common divisor is
@{thm [display] greatest_common_divisor_def}
*}

instantiation nat :: default
begin

definition "default = (0::nat)"

instance ..

end

instantiation prod :: (default, default) default
begin

definition "default = (default, default)"

instance ..

end

instantiation "fun" :: (type, default) default
begin

definition "default = (\<lambda>x. default)"

instance ..

end

lemma "greatest_common_divisor 7 12 = (4, 3, 2)" by eval

end
