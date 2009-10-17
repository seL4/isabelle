(*  Title:      HOL/Nat_Int_Bij.thy
    Author:     Stefan Richter, Tobias Nipkow
*)

header{* Bijections $\mathbb{N}\to\mathbb{N}^2$ and $\mathbb{N}\to\mathbb{Z}$*}

theory Nat_Int_Bij
imports Main
begin

subsection{*  A bijection between @{text "\<nat>"} and @{text "\<nat>\<twosuperior>"} *}

text{* Definition and proofs are from \cite[page 85]{Oberschelp:1993}. *}

definition nat2_to_nat:: "(nat * nat) \<Rightarrow> nat" where
"nat2_to_nat pair = (let (n,m) = pair in (n+m) * Suc (n+m) div 2 + n)"
definition nat_to_nat2::  "nat \<Rightarrow> (nat * nat)" where
"nat_to_nat2 = inv nat2_to_nat"

lemma dvd2_a_x_suc_a: "2 dvd a * (Suc a)"
proof (cases "2 dvd a")
  case True
  then show ?thesis by (rule dvd_mult2)
next
  case False
  then have "Suc (a mod 2) = 2" by (simp add: dvd_eq_mod_eq_0)
  then have "Suc a mod 2 = 0" by (simp add: mod_Suc)
  then have "2 dvd Suc a" by (simp only:dvd_eq_mod_eq_0)
  then show ?thesis by (rule dvd_mult)
qed

lemma
  assumes eq: "nat2_to_nat (u,v) = nat2_to_nat (x,y)"
  shows nat2_to_nat_help: "u+v \<le> x+y"
proof (rule classical)
  assume "\<not> ?thesis"
  then have contrapos: "x+y < u+v"
    by simp
  have "nat2_to_nat (x,y) < (x+y) * Suc (x+y) div 2 + Suc (x + y)"
    by (unfold nat2_to_nat_def) (simp add: Let_def)
  also have "\<dots> = (x+y)*Suc(x+y) div 2 + 2 * Suc(x+y) div 2"
    by (simp only: div_mult_self1_is_m)
  also have "\<dots> = (x+y)*Suc(x+y) div 2 + 2 * Suc(x+y) div 2
    + ((x+y)*Suc(x+y) mod 2 + 2 * Suc(x+y) mod 2) div 2"
  proof -
    have "2 dvd (x+y)*Suc(x+y)"
      by (rule dvd2_a_x_suc_a)
    then have "(x+y)*Suc(x+y) mod 2 = 0"
      by (simp only: dvd_eq_mod_eq_0)
    also
    have "2 * Suc(x+y) mod 2 = 0"
      by (rule mod_mult_self1_is_0)
    ultimately have
      "((x+y)*Suc(x+y) mod 2 + 2 * Suc(x+y) mod 2) div 2 = 0"
      by simp
    then show ?thesis
      by simp
  qed
  also have "\<dots> = ((x+y)*Suc(x+y) + 2*Suc(x+y)) div 2"
    by (rule div_add1_eq [symmetric])
  also have "\<dots> = ((x+y+2)*Suc(x+y)) div 2"
    by (simp only: add_mult_distrib [symmetric])
  also from contrapos have "\<dots> \<le> ((Suc(u+v))*(u+v)) div 2"
    by (simp only: mult_le_mono div_le_mono)
  also have "\<dots> \<le> nat2_to_nat (u,v)"
    by (unfold nat2_to_nat_def) (simp add: Let_def)
  finally show ?thesis
    by (simp only: eq)
qed

theorem nat2_to_nat_inj: "inj nat2_to_nat"
proof -
  {
    fix u v x y
    assume eq1: "nat2_to_nat (u,v) = nat2_to_nat (x,y)"
    then have "u+v \<le> x+y" by (rule nat2_to_nat_help)
    also from eq1 [symmetric] have "x+y \<le> u+v"
      by (rule nat2_to_nat_help)
    finally have eq2: "u+v = x+y" .
    with eq1 have ux: "u=x"
      by (simp add: nat2_to_nat_def Let_def)
    with eq2 have vy: "v=y" by simp
    with ux have "(u,v) = (x,y)" by simp
  }
  then have "\<And>x y. nat2_to_nat x = nat2_to_nat y \<Longrightarrow> x=y" by fast
  then show ?thesis unfolding inj_on_def by simp
qed

lemma nat_to_nat2_surj: "surj nat_to_nat2"
by (simp only: nat_to_nat2_def nat2_to_nat_inj inj_imp_surj_inv)


lemma gauss_sum_nat_upto: "2 * (\<Sum>i\<le>n::nat. i) = n * (n + 1)"
using gauss_sum[where 'a = nat]
by (simp add:atLeast0AtMost setsum_shift_lb_Suc0_0 numeral_2_eq_2)

lemma nat2_to_nat_surj: "surj nat2_to_nat"
proof (unfold surj_def)
  {
    fix z::nat 
    def r \<equiv> "Max {r. (\<Sum>i\<le>r. i) \<le> z}" 
    def x \<equiv> "z - (\<Sum>i\<le>r. i)"

    hence "finite  {r. (\<Sum>i\<le>r. i) \<le> z}"
      by (simp add: lessThan_Suc_atMost[symmetric] lessThan_Suc finite_less_ub)
    also have "0 \<in> {r. (\<Sum>i\<le>r. i) \<le> z}"  by simp
    hence "{r::nat. (\<Sum>i\<le>r. i) \<le> z} \<noteq> {}"  by fast
    ultimately have a: "r \<in> {r. (\<Sum>i\<le>r. i) \<le> z} \<and> (\<forall>s \<in> {r. (\<Sum>i\<le>r. i) \<le> z}. s \<le> r)"
      by (simp add: r_def del:mem_Collect_eq)
    {
      assume "r<x"
      hence "r+1\<le>x"  by simp
      hence "(\<Sum>i\<le>r. i)+(r+1)\<le>z"  using x_def by arith
      hence "(r+1) \<in>  {r. (\<Sum>i\<le>r. i) \<le> z}"  by simp
      with a have "(r+1)\<le>r"  by simp
    }
    hence b: "x\<le>r"  by force
    
    def y \<equiv> "r-x"
    have "2*z=2*(\<Sum>i\<le>r. i)+2*x"  using x_def a by simp arith
    also have "\<dots> = r * (r+1) + 2*x"   using gauss_sum_nat_upto by simp
    also have "\<dots> = (x+y)*(x+y+1)+2*x" using y_def b by simp
    also { have "2 dvd ((x+y)*(x+y+1))" using dvd2_a_x_suc_a by simp }
    hence "\<dots> = 2 * nat2_to_nat(x,y)"
      using nat2_to_nat_def by (simp add: Let_def dvd_mult_div_cancel)
    finally have "z=nat2_to_nat (x, y)"  by simp
  }
  thus "\<forall>y. \<exists>x. y = nat2_to_nat x"  by fast
qed

lemma nat_to_nat2_inj: "inj nat_to_nat2"
  by (simp add: nat_to_nat2_def surj_imp_inj_inv nat2_to_nat_surj) 


subsection{*  A bijection between @{text "\<nat>"} and @{text "\<int>"} *}

definition nat_to_int_bij :: "nat \<Rightarrow> int" where
"nat_to_int_bij n = (if 2 dvd n then int(n div 2) else -int(Suc n div 2))"

definition int_to_nat_bij :: "int \<Rightarrow> nat" where
"int_to_nat_bij i = (if 0<=i then 2*nat(i) else 2*nat(-i) - 1)"

lemma  i2n_n2i_id: "int_to_nat_bij (nat_to_int_bij n) = n"
by (simp add: int_to_nat_bij_def nat_to_int_bij_def) presburger

lemma n2i_i2n_id: "nat_to_int_bij(int_to_nat_bij i) = i"
proof -
  have "ALL m n::nat. m>0 \<longrightarrow> 2 * m - Suc 0 \<noteq> 2 * n" by presburger
  thus ?thesis
    by(simp add: nat_to_int_bij_def int_to_nat_bij_def, simp add:dvd_def)
qed

lemma inv_nat_to_int_bij: "inv nat_to_int_bij = int_to_nat_bij"
by (simp add: i2n_n2i_id inv_equality n2i_i2n_id)

lemma inv_int_to_nat_bij: "inv int_to_nat_bij = nat_to_int_bij"
by (simp add: i2n_n2i_id inv_equality n2i_i2n_id)

lemma surj_nat_to_int_bij: "surj nat_to_int_bij"
by (blast intro: n2i_i2n_id surjI)

lemma surj_int_to_nat_bij: "surj int_to_nat_bij"
by (blast intro: i2n_n2i_id surjI)

lemma inj_nat_to_int_bij: "inj nat_to_int_bij"
by(simp add:inv_int_to_nat_bij[symmetric] surj_int_to_nat_bij surj_imp_inj_inv)

lemma inj_int_to_nat_bij: "inj int_to_nat_bij"
by(simp add:inv_nat_to_int_bij[symmetric] surj_nat_to_int_bij surj_imp_inj_inv)

lemma bij_nat_to_int_bij: "bij nat_to_int_bij"
by(simp add:bij_def inj_nat_to_int_bij surj_nat_to_int_bij)

lemma bij_int_to_nat_bij: "bij int_to_nat_bij"
by(simp add:bij_def inj_int_to_nat_bij surj_int_to_nat_bij)


end
