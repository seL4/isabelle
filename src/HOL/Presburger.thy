(* Title:      HOL/Presburger.thy
   Author:     Amine Chaieb, TU Muenchen
*)

header {* Decision Procedure for Presburger Arithmetic *}

theory Presburger
imports Groebner_Basis Set_Interval
begin

ML_file "Tools/Qelim/qelim.ML"
ML_file "Tools/Qelim/cooper_procedure.ML"

subsection{* The @{text "-\<infinity>"} and @{text "+\<infinity>"} Properties *}

lemma minf:
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x<z. P x = P' x; \<exists>z.\<forall>x<z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x<z. (P x \<and> Q x) = (P' x \<and> Q' x)"
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x<z. P x = P' x; \<exists>z.\<forall>x<z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x<z. (P x \<or> Q x) = (P' x \<or> Q' x)"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x = t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x \<noteq> t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x < t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x \<le> t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x > t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x<z.(x \<ge> t) = False"
  "\<exists>z.\<forall>(x::'b::{linorder,plus,Rings.dvd})<z. (d dvd x + s) = (d dvd x + s)"
  "\<exists>z.\<forall>(x::'b::{linorder,plus,Rings.dvd})<z. (\<not> d dvd x + s) = (\<not> d dvd x + s)"
  "\<exists>z.\<forall>x<z. F = F"
  by ((erule exE, erule exE,rule_tac x="min z za" in exI,simp)+, (rule_tac x="t" in exI,fastforce)+) simp_all

lemma pinf:
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x>z. P x = P' x; \<exists>z.\<forall>x>z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x>z. (P x \<and> Q x) = (P' x \<and> Q' x)"
  "\<lbrakk>\<exists>(z ::'a::linorder).\<forall>x>z. P x = P' x; \<exists>z.\<forall>x>z. Q x = Q' x\<rbrakk> 
     \<Longrightarrow> \<exists>z.\<forall>x>z. (P x \<or> Q x) = (P' x \<or> Q' x)"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x = t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x \<noteq> t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x < t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x \<le> t) = False"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x > t) = True"
  "\<exists>(z ::'a::{linorder}).\<forall>x>z.(x \<ge> t) = True"
  "\<exists>z.\<forall>(x::'b::{linorder,plus,Rings.dvd})>z. (d dvd x + s) = (d dvd x + s)"
  "\<exists>z.\<forall>(x::'b::{linorder,plus,Rings.dvd})>z. (\<not> d dvd x + s) = (\<not> d dvd x + s)"
  "\<exists>z.\<forall>x>z. F = F"
  by ((erule exE, erule exE,rule_tac x="max z za" in exI,simp)+,(rule_tac x="t" in exI,fastforce)+) simp_all

lemma inf_period:
  "\<lbrakk>\<forall>x k. P x = P (x - k*D); \<forall>x k. Q x = Q (x - k*D)\<rbrakk> 
    \<Longrightarrow> \<forall>x k. (P x \<and> Q x) = (P (x - k*D) \<and> Q (x - k*D))"
  "\<lbrakk>\<forall>x k. P x = P (x - k*D); \<forall>x k. Q x = Q (x - k*D)\<rbrakk> 
    \<Longrightarrow> \<forall>x k. (P x \<or> Q x) = (P (x - k*D) \<or> Q (x - k*D))"
  "(d::'a::{comm_ring,Rings.dvd}) dvd D \<Longrightarrow> \<forall>x k. (d dvd x + t) = (d dvd (x - k*D) + t)"
  "(d::'a::{comm_ring,Rings.dvd}) dvd D \<Longrightarrow> \<forall>x k. (\<not>d dvd x + t) = (\<not>d dvd (x - k*D) + t)"
  "\<forall>x k. F = F"
apply (auto elim!: dvdE simp add: algebra_simps)
unfolding mult_assoc [symmetric] left_distrib [symmetric] left_diff_distrib [symmetric]
unfolding dvd_def mult_commute [of d] 
by auto

subsection{* The A and B sets *}
lemma bset:
  "\<lbrakk>\<forall>x.(\<forall>j \<in> {1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> P x \<longrightarrow> P(x - D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> Q x \<longrightarrow> Q(x - D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j) \<longrightarrow> (P x \<and> Q x) \<longrightarrow> (P(x - D) \<and> Q (x - D))"
  "\<lbrakk>\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> P x \<longrightarrow> P(x - D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> Q x \<longrightarrow> Q(x - D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (P x \<or> Q x) \<longrightarrow> (P(x - D) \<or> Q (x - D))"
  "\<lbrakk>D>0; t - 1\<in> B\<rbrakk> \<Longrightarrow> (\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x = t) \<longrightarrow> (x - D = t))"
  "\<lbrakk>D>0 ; t \<in> B\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x - D \<noteq> t))"
  "D>0 \<Longrightarrow> (\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x < t) \<longrightarrow> (x - D < t))"
  "D>0 \<Longrightarrow> (\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x - D \<le> t))"
  "\<lbrakk>D>0 ; t \<in> B\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x > t) \<longrightarrow> (x - D > t))"
  "\<lbrakk>D>0 ; t - 1 \<in> B\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x - D \<ge> t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x - D) + t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not> d dvd (x - D) + t))"
  "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j) \<longrightarrow> F \<longrightarrow> F"
proof (blast, blast)
  assume dp: "D > 0" and tB: "t - 1\<in> B"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x = t) \<longrightarrow> (x - D = t))" 
    apply (rule allI, rule impI,erule ballE[where x="1"],erule ballE[where x="t - 1"]) 
    apply algebra using dp tB by simp_all
next
  assume dp: "D > 0" and tB: "t \<in> B"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x - D \<noteq> t))" 
    apply (rule allI, rule impI,erule ballE[where x="D"],erule ballE[where x="t"])
    apply algebra
    using dp tB by simp_all
next
  assume dp: "D > 0" thus "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x < t) \<longrightarrow> (x - D < t))" by arith
next
  assume dp: "D > 0" thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x - D \<le> t)" by arith
next
  assume dp: "D > 0" and tB:"t \<in> B"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j" and g: "x > t" and ng: "\<not> (x - D) > t"
    hence "x -t \<le> D" and "1 \<le> x - t" by simp+
      hence "\<exists>j \<in> {1 .. D}. x - t = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = t + j" by (simp add: algebra_simps)
      with nob tB have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x > t) \<longrightarrow> (x - D > t)" by blast
next
  assume dp: "D > 0" and tB:"t - 1\<in> B"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j" and g: "x \<ge> t" and ng: "\<not> (x - D) \<ge> t"
    hence "x - (t - 1) \<le> D" and "1 \<le> x - (t - 1)" by simp+
      hence "\<exists>j \<in> {1 .. D}. x - (t - 1) = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = (t - 1) + j" by (simp add: algebra_simps)
      with nob tB have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x - D \<ge> t)" by blast
next
  assume d: "d dvd D"
  {fix x assume H: "d dvd x + t" with d have "d dvd (x - D) + t" by algebra}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x - D) + t)" by simp
next
  assume d: "d dvd D"
  {fix x assume H: "\<not>(d dvd x + t)" with d have "\<not> d dvd (x - D) + t"
      by (clarsimp simp add: dvd_def,erule_tac x= "ka + k" in allE,simp add: algebra_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>B. x \<noteq> b + j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not>d dvd (x - D) + t)" by auto
qed blast

lemma aset:
  "\<lbrakk>\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> P x \<longrightarrow> P(x + D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> Q x \<longrightarrow> Q(x + D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j) \<longrightarrow> (P x \<and> Q x) \<longrightarrow> (P(x + D) \<and> Q (x + D))"
  "\<lbrakk>\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> P x \<longrightarrow> P(x + D) ;
     \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> Q x \<longrightarrow> Q(x + D)\<rbrakk> \<Longrightarrow> 
  \<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (P x \<or> Q x) \<longrightarrow> (P(x + D) \<or> Q (x + D))"
  "\<lbrakk>D>0; t + 1\<in> A\<rbrakk> \<Longrightarrow> (\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x = t) \<longrightarrow> (x + D = t))"
  "\<lbrakk>D>0 ; t \<in> A\<rbrakk> \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x + D \<noteq> t))"
  "\<lbrakk>D>0; t\<in> A\<rbrakk> \<Longrightarrow>(\<forall>(x::int). (\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x < t) \<longrightarrow> (x + D < t))"
  "\<lbrakk>D>0; t + 1 \<in> A\<rbrakk> \<Longrightarrow> (\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x + D \<le> t))"
  "D>0 \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x > t) \<longrightarrow> (x + D > t))"
  "D>0 \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x + D \<ge> t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x + D) + t))"
  "d dvd D \<Longrightarrow>(\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not> d dvd (x + D) + t))"
  "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j) \<longrightarrow> F \<longrightarrow> F"
proof (blast, blast)
  assume dp: "D > 0" and tA: "t + 1 \<in> A"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x = t) \<longrightarrow> (x + D = t))" 
    apply (rule allI, rule impI,erule ballE[where x="1"],erule ballE[where x="t + 1"])
    using dp tA by simp_all
next
  assume dp: "D > 0" and tA: "t \<in> A"
  show "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<noteq> t) \<longrightarrow> (x + D \<noteq> t))" 
    apply (rule allI, rule impI,erule ballE[where x="D"],erule ballE[where x="t"])
    using dp tA by simp_all
next
  assume dp: "D > 0" thus "(\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x > t) \<longrightarrow> (x + D > t))" by arith
next
  assume dp: "D > 0" thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<ge> t) \<longrightarrow> (x + D \<ge> t)" by arith
next
  assume dp: "D > 0" and tA:"t \<in> A"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j" and g: "x < t" and ng: "\<not> (x + D) < t"
    hence "t - x \<le> D" and "1 \<le> t - x" by simp+
      hence "\<exists>j \<in> {1 .. D}. t - x = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = t - j" by (auto simp add: algebra_simps) 
      with nob tA have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x < t) \<longrightarrow> (x + D < t)" by blast
next
  assume dp: "D > 0" and tA:"t + 1\<in> A"
  {fix x assume nob: "\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j" and g: "x \<le> t" and ng: "\<not> (x + D) \<le> t"
    hence "(t + 1) - x \<le> D" and "1 \<le> (t + 1) - x" by (simp_all add: algebra_simps)
      hence "\<exists>j \<in> {1 .. D}. (t + 1) - x = j" by auto
      hence "\<exists>j \<in> {1 .. D}. x = (t + 1) - j" by (auto simp add: algebra_simps)
      with nob tA have "False" by simp}
  thus "\<forall>x.(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (x \<le> t) \<longrightarrow> (x + D \<le> t)" by blast
next
  assume d: "d dvd D"
  {fix x assume H: "d dvd x + t" with d have "d dvd (x + D) + t"
      by (clarsimp simp add: dvd_def,rule_tac x= "ka + k" in exI,simp add: algebra_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x + D) + t)" by simp
next
  assume d: "d dvd D"
  {fix x assume H: "\<not>(d dvd x + t)" with d have "\<not>d dvd (x + D) + t"
      by (clarsimp simp add: dvd_def,erule_tac x= "ka - k" in allE,simp add: algebra_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not>d dvd (x + D) + t)" by auto
qed blast

subsection{* Cooper's Theorem @{text "-\<infinity>"} and @{text "+\<infinity>"} Version *}

subsubsection{* First some trivial facts about periodic sets or predicates *}
lemma periodic_finite_ex:
  assumes dpos: "(0::int) < d" and modd: "ALL x k. P x = P(x - k*d)"
  shows "(EX x. P x) = (EX j : {1..d}. P j)"
  (is "?LHS = ?RHS")
proof
  assume ?LHS
  then obtain x where P: "P x" ..
  have "x mod d = x - (x div d)*d" by(simp add:zmod_zdiv_equality mult_ac eq_diff_eq)
  hence Pmod: "P x = P(x mod d)" using modd by simp
  show ?RHS
  proof (cases)
    assume "x mod d = 0"
    hence "P 0" using P Pmod by simp
    moreover have "P 0 = P(0 - (-1)*d)" using modd by blast
    ultimately have "P d" by simp
    moreover have "d : {1..d}" using dpos by simp
    ultimately show ?RHS ..
  next
    assume not0: "x mod d \<noteq> 0"
    have "P(x mod d)" using dpos P Pmod by simp
    moreover have "x mod d : {1..d}"
    proof -
      from dpos have "0 \<le> x mod d" by(rule pos_mod_sign)
      moreover from dpos have "x mod d < d" by(rule pos_mod_bound)
      ultimately show ?thesis using not0 by simp
    qed
    ultimately show ?RHS ..
  qed
qed auto

subsubsection{* The @{text "-\<infinity>"} Version*}

lemma decr_lemma: "0 < (d::int) \<Longrightarrow> x - (abs(x-z)+1) * d < z"
by(induct rule: int_gr_induct,simp_all add:int_distrib)

lemma incr_lemma: "0 < (d::int) \<Longrightarrow> z < x + (abs(x-z)+1) * d"
by(induct rule: int_gr_induct, simp_all add:int_distrib)

lemma decr_mult_lemma:
  assumes dpos: "(0::int) < d" and minus: "\<forall>x. P x \<longrightarrow> P(x - d)" and knneg: "0 <= k"
  shows "ALL x. P x \<longrightarrow> P(x - k*d)"
using knneg
proof (induct rule:int_ge_induct)
  case base thus ?case by simp
next
  case (step i)
  {fix x
    have "P x \<longrightarrow> P (x - i * d)" using step.hyps by blast
    also have "\<dots> \<longrightarrow> P(x - (i + 1) * d)" using minus[THEN spec, of "x - i * d"]
      by (simp add: algebra_simps)
    ultimately have "P x \<longrightarrow> P(x - (i + 1) * d)" by blast}
  thus ?case ..
qed

lemma  minusinfinity:
  assumes dpos: "0 < d" and
    P1eqP1: "ALL x k. P1 x = P1(x - k*d)" and ePeqP1: "EX z::int. ALL x. x < z \<longrightarrow> (P x = P1 x)"
  shows "(EX x. P1 x) \<longrightarrow> (EX x. P x)"
proof
  assume eP1: "EX x. P1 x"
  then obtain x where P1: "P1 x" ..
  from ePeqP1 obtain z where P1eqP: "ALL x. x < z \<longrightarrow> (P x = P1 x)" ..
  let ?w = "x - (abs(x-z)+1) * d"
  from dpos have w: "?w < z" by(rule decr_lemma)
  have "P1 x = P1 ?w" using P1eqP1 by blast
  also have "\<dots> = P(?w)" using w P1eqP by blast
  finally have "P ?w" using P1 by blast
  thus "EX x. P x" ..
qed

lemma cpmi: 
  assumes dp: "0 < D" and p1:"\<exists>z. \<forall> x< z. P x = P' x"
  and nb:"\<forall>x.(\<forall> j\<in> {1..D}. \<forall>(b::int) \<in> B. x \<noteq> b+j) --> P (x) --> P (x - D)"
  and pd: "\<forall> x k. P' x = P' (x-k*D)"
  shows "(\<exists>x. P x) = ((\<exists> j\<in> {1..D} . P' j) | (\<exists> j \<in> {1..D}.\<exists> b\<in> B. P (b+j)))" 
         (is "?L = (?R1 \<or> ?R2)")
proof-
 {assume "?R2" hence "?L"  by blast}
 moreover
 {assume H:"?R1" hence "?L" using minusinfinity[OF dp pd p1] periodic_finite_ex[OF dp pd] by simp}
 moreover 
 { fix x
   assume P: "P x" and H: "\<not> ?R2"
   {fix y assume "\<not> (\<exists>j\<in>{1..D}. \<exists>b\<in>B. P (b + j))" and P: "P y"
     hence "~(EX (j::int) : {1..D}. EX (b::int) : B. y = b+j)" by auto
     with nb P  have "P (y - D)" by auto }
   hence "ALL x.~(EX (j::int) : {1..D}. EX (b::int) : B. P(b+j)) --> P (x) --> P (x - D)" by blast
   with H P have th: " \<forall>x. P x \<longrightarrow> P (x - D)" by auto
   from p1 obtain z where z: "ALL x. x < z --> (P x = P' x)" by blast
   let ?y = "x - (\<bar>x - z\<bar> + 1)*D"
   have zp: "0 <= (\<bar>x - z\<bar> + 1)" by arith
   from dp have yz: "?y < z" using decr_lemma[OF dp] by simp   
   from z[rule_format, OF yz] decr_mult_lemma[OF dp th zp, rule_format, OF P] have th2: " P' ?y" by auto
   with periodic_finite_ex[OF dp pd]
   have "?R1" by blast}
 ultimately show ?thesis by blast
qed

subsubsection {* The @{text "+\<infinity>"} Version*}

lemma  plusinfinity:
  assumes dpos: "(0::int) < d" and
    P1eqP1: "\<forall>x k. P' x = P'(x - k*d)" and ePeqP1: "\<exists> z. \<forall> x>z. P x = P' x"
  shows "(\<exists> x. P' x) \<longrightarrow> (\<exists> x. P x)"
proof
  assume eP1: "EX x. P' x"
  then obtain x where P1: "P' x" ..
  from ePeqP1 obtain z where P1eqP: "\<forall>x>z. P x = P' x" ..
  let ?w' = "x + (abs(x-z)+1) * d"
  let ?w = "x - (-(abs(x-z) + 1))*d"
  have ww'[simp]: "?w = ?w'" by (simp add: algebra_simps)
  from dpos have w: "?w > z" by(simp only: ww' incr_lemma)
  hence "P' x = P' ?w" using P1eqP1 by blast
  also have "\<dots> = P(?w)" using w P1eqP by blast
  finally have "P ?w" using P1 by blast
  thus "EX x. P x" ..
qed

lemma incr_mult_lemma:
  assumes dpos: "(0::int) < d" and plus: "ALL x::int. P x \<longrightarrow> P(x + d)" and knneg: "0 <= k"
  shows "ALL x. P x \<longrightarrow> P(x + k*d)"
using knneg
proof (induct rule:int_ge_induct)
  case base thus ?case by simp
next
  case (step i)
  {fix x
    have "P x \<longrightarrow> P (x + i * d)" using step.hyps by blast
    also have "\<dots> \<longrightarrow> P(x + (i + 1) * d)" using plus[THEN spec, of "x + i * d"]
      by (simp add:int_distrib add_ac)
    ultimately have "P x \<longrightarrow> P(x + (i + 1) * d)" by blast}
  thus ?case ..
qed

lemma cppi: 
  assumes dp: "0 < D" and p1:"\<exists>z. \<forall> x> z. P x = P' x"
  and nb:"\<forall>x.(\<forall> j\<in> {1..D}. \<forall>(b::int) \<in> A. x \<noteq> b - j) --> P (x) --> P (x + D)"
  and pd: "\<forall> x k. P' x= P' (x-k*D)"
  shows "(\<exists>x. P x) = ((\<exists> j\<in> {1..D} . P' j) | (\<exists> j \<in> {1..D}.\<exists> b\<in> A. P (b - j)))" (is "?L = (?R1 \<or> ?R2)")
proof-
 {assume "?R2" hence "?L"  by blast}
 moreover
 {assume H:"?R1" hence "?L" using plusinfinity[OF dp pd p1] periodic_finite_ex[OF dp pd] by simp}
 moreover 
 { fix x
   assume P: "P x" and H: "\<not> ?R2"
   {fix y assume "\<not> (\<exists>j\<in>{1..D}. \<exists>b\<in>A. P (b - j))" and P: "P y"
     hence "~(EX (j::int) : {1..D}. EX (b::int) : A. y = b - j)" by auto
     with nb P  have "P (y + D)" by auto }
   hence "ALL x.~(EX (j::int) : {1..D}. EX (b::int) : A. P(b-j)) --> P (x) --> P (x + D)" by blast
   with H P have th: " \<forall>x. P x \<longrightarrow> P (x + D)" by auto
   from p1 obtain z where z: "ALL x. x > z --> (P x = P' x)" by blast
   let ?y = "x + (\<bar>x - z\<bar> + 1)*D"
   have zp: "0 <= (\<bar>x - z\<bar> + 1)" by arith
   from dp have yz: "?y > z" using incr_lemma[OF dp] by simp
   from z[rule_format, OF yz] incr_mult_lemma[OF dp th zp, rule_format, OF P] have th2: " P' ?y" by auto
   with periodic_finite_ex[OF dp pd]
   have "?R1" by blast}
 ultimately show ?thesis by blast
qed

lemma simp_from_to: "{i..j::int} = (if j < i then {} else insert i {i+1..j})"
apply(simp add:atLeastAtMost_def atLeast_def atMost_def)
apply(fastforce)
done

theorem unity_coeff_ex: "(\<exists>(x::'a::{semiring_0,Rings.dvd}). P (l * x)) \<equiv> (\<exists>x. l dvd (x + 0) \<and> P x)"
  apply (rule eq_reflection [symmetric])
  apply (rule iffI)
  defer
  apply (erule exE)
  apply (rule_tac x = "l * x" in exI)
  apply (simp add: dvd_def)
  apply (rule_tac x = x in exI, simp)
  apply (erule exE)
  apply (erule conjE)
  apply simp
  apply (erule dvdE)
  apply (rule_tac x = k in exI)
  apply simp
  done

lemma zdvd_mono: assumes not0: "(k::int) \<noteq> 0"
shows "((m::int) dvd t) \<equiv> (k*m dvd k*t)" 
  using not0 by (simp add: dvd_def)

lemma uminus_dvd_conv: "(d dvd (t::int)) \<equiv> (-d dvd t)" "(d dvd (t::int)) \<equiv> (d dvd -t)"
  by simp_all

text {* \bigskip Theorems for transforming predicates on nat to predicates on @{text int}*}

lemma zdiff_int_split: "P (int (x - y)) =
  ((y \<le> x \<longrightarrow> P (int x - int y)) \<and> (x < y \<longrightarrow> P 0))"
  by (cases "y \<le> x") (simp_all add: zdiff_int)

text {*
  \medskip Specific instances of congruence rules, to prevent
  simplifier from looping. *}

theorem imp_le_cong:
  "\<lbrakk>x = x'; 0 \<le> x' \<Longrightarrow> P = P'\<rbrakk> \<Longrightarrow> (0 \<le> (x::int) \<longrightarrow> P) = (0 \<le> x' \<longrightarrow> P')"
  by simp

theorem conj_le_cong:
  "\<lbrakk>x = x'; 0 \<le> x' \<Longrightarrow> P = P'\<rbrakk> \<Longrightarrow> (0 \<le> (x::int) \<and> P) = (0 \<le> x' \<and> P')"
  by (simp cong: conj_cong)

ML_file "Tools/Qelim/cooper.ML"
setup Cooper.setup

method_setup presburger = {*
  let
    fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ()
    fun simple_keyword k = Scan.lift (Args.$$$ k) >> K ()
    val addN = "add"
    val delN = "del"
    val elimN = "elim"
    val any_keyword = keyword addN || keyword delN || simple_keyword elimN
    val thms = Scan.repeat (Scan.unless any_keyword Attrib.multi_thm) >> flat;
  in
    Scan.optional (simple_keyword elimN >> K false) true --
    Scan.optional (keyword addN |-- thms) [] --
    Scan.optional (keyword delN |-- thms) [] >>
    (fn ((elim, add_ths), del_ths) => fn ctxt =>
      SIMPLE_METHOD' (Cooper.tac elim add_ths del_ths ctxt))
  end
*} "Cooper's algorithm for Presburger arithmetic"

declare dvd_eq_mod_eq_0[symmetric, presburger]
declare mod_1[presburger] 
declare mod_0[presburger]
declare mod_by_1[presburger]
declare mod_self[presburger]
declare mod_by_0[presburger]
declare mod_div_trivial[presburger]
declare div_mod_equality2[presburger]
declare div_mod_equality[presburger]
declare mod_div_equality2[presburger]
declare mod_div_equality[presburger]
declare mod_mult_self1[presburger]
declare mod_mult_self2[presburger]
declare div_mod_equality[presburger]
declare div_mod_equality2[presburger]
declare mod2_Suc_Suc[presburger]
lemma [presburger]: "(a::int) div 0 = 0" and [presburger]: "a mod 0 = a"
by simp_all

lemma [presburger, algebra]: "m mod 2 = (1::nat) \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger, algebra]: "m mod 2 = Suc 0 \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger, algebra]: "m mod (Suc (Suc 0)) = (1::nat) \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger, algebra]: "m mod (Suc (Suc 0)) = Suc 0 \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger, algebra]: "m mod 2 = (1::int) \<longleftrightarrow> \<not> 2 dvd m " by presburger

end
