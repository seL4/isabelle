(* Title:      HOL/Presburger.thy
   Author:     Amine Chaieb, TU Muenchen
*)

section \<open>Decision Procedure for Presburger Arithmetic\<close>

theory Presburger
imports Groebner_Basis Set_Interval
begin

ML_file \<open>Tools/Qelim/qelim.ML\<close>
ML_file \<open>Tools/Qelim/cooper_procedure.ML\<close>

subsection\<open>The \<open>-\<infinity>\<close> and \<open>+\<infinity>\<close> Properties\<close>

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
proof safe
  fix z1 z2
  assume "\<forall>x<z1. P x = P' x" and "\<forall>x<z2. Q x = Q' x"
  then have "\<forall>x < min z1 z2. (P x \<and> Q x) = (P' x \<and> Q' x)"
    by simp
  then show "\<exists>z. \<forall>x<z. (P x \<and> Q x) = (P' x \<and> Q' x)"
    by blast
next
  fix z1 z2
  assume "\<forall>x<z1. P x = P' x" and "\<forall>x<z2. Q x = Q' x"
  then have "\<forall>x < min z1 z2. (P x \<or> Q x) = (P' x \<or> Q' x)"
    by simp
  then show "\<exists>z. \<forall>x<z. (P x \<or> Q x) = (P' x \<or> Q' x)"
    by blast
next
  have "\<forall>x<t. x \<le> t"
    by fastforce
  then show "\<exists>z. \<forall>x<z. (x \<le> t) = True"
    by auto
next
  have "\<forall>x<t. \<not> t < x"
    by fastforce
  then show "\<exists>z. \<forall>x<z. (t < x) = False"
    by auto
next
  have "\<forall>x<t. \<not> t \<le> x"
    by fastforce
  then show "\<exists>z. \<forall>x<z. (t \<le> x) = False"
    by auto
qed auto

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
proof safe
  fix z1 z2
  assume "\<forall>x>z1. P x = P' x" and "\<forall>x>z2. Q x = Q' x"
  then have "\<forall>x > max z1 z2. (P x \<and> Q x) = (P' x \<and> Q' x)"
    by simp
  then show "\<exists>z. \<forall>x>z. (P x \<and> Q x) = (P' x \<and> Q' x)"
    by blast
next
  fix z1 z2
  assume "\<forall>x>z1. P x = P' x" and "\<forall>x>z2. Q x = Q' x"
  then have "\<forall>x > max z1 z2. (P x \<or> Q x) = (P' x \<or> Q' x)"
    by simp
  then show "\<exists>z. \<forall>x>z. (P x \<or> Q x) = (P' x \<or> Q' x)"
    by blast
next
  have "\<forall>x>t. \<not> x < t"
    by fastforce
  then show "\<exists>z. \<forall>x>z. x < t = False"
    by blast
next
  have "\<forall>x>t. \<not> x \<le> t"
    by fastforce
  then show "\<exists>z. \<forall>x>z. x \<le> t = False"
    by blast
next
  have "\<forall>x>t. t \<le> x"
    by fastforce
  then show "\<exists>z. \<forall>x>z. t \<le> x = True"
    by blast
qed auto

lemma inf_period:
  "\<lbrakk>\<forall>x k. P x = P (x - k*D); \<forall>x k. Q x = Q (x - k*D)\<rbrakk> 
    \<Longrightarrow> \<forall>x k. (P x \<and> Q x) = (P (x - k*D) \<and> Q (x - k*D))"
  "\<lbrakk>\<forall>x k. P x = P (x - k*D); \<forall>x k. Q x = Q (x - k*D)\<rbrakk> 
    \<Longrightarrow> \<forall>x k. (P x \<or> Q x) = (P (x - k*D) \<or> Q (x - k*D))"
  "(d::'a::{comm_ring,Rings.dvd}) dvd D \<Longrightarrow> \<forall>x k. (d dvd x + t) = (d dvd (x - k*D) + t)"
  "(d::'a::{comm_ring,Rings.dvd}) dvd D \<Longrightarrow> \<forall>x k. (\<not>d dvd x + t) = (\<not>d dvd (x - k*D) + t)"
  "\<forall>x k. F = F"
apply (auto elim!: dvdE simp add: algebra_simps)
unfolding mult.assoc [symmetric] distrib_right [symmetric] left_diff_distrib [symmetric]
unfolding dvd_def mult.commute [of d] 
by auto

subsection\<open>The A and B sets\<close>
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
  have "\<And>x. d dvd x + t \<Longrightarrow> d dvd x + D + t"
  proof -
    fix x
    assume H: "d dvd x + t"
    then obtain ka where "x + t = d * ka"
      unfolding dvd_def by blast
    moreover from d obtain k where *:"D = d * k"
      unfolding dvd_def by blast
    ultimately have "x + d * k + t = d * (ka + k)"
      by (simp add: algebra_simps)
    then show "d dvd (x + D) + t"
      using * unfolding dvd_def by blast
  qed
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (d dvd x+t) \<longrightarrow> (d dvd (x + D) + t)" by simp
next
  assume d: "d dvd D"
  {fix x assume H: "\<not>(d dvd x + t)" with d have "\<not>d dvd (x + D) + t"
      using dvd_add_left_iff[OF d, of "x+t"] by (simp add: algebra_simps)}
  thus "\<forall>(x::int).(\<forall>j\<in>{1 .. D}. \<forall>b\<in>A. x \<noteq> b - j)\<longrightarrow> (\<not>d dvd x+t) \<longrightarrow> (\<not>d dvd (x + D) + t)" by auto
qed blast

subsection\<open>Cooper's Theorem \<open>-\<infinity>\<close> and \<open>+\<infinity>\<close> Version\<close>

subsubsection\<open>First some trivial facts about periodic sets or predicates\<close>
lemma periodic_finite_ex:
  assumes dpos: "(0::int) < d" and modd: "\<forall>x k. P x = P(x - k*d)"
  shows "(\<exists>x. P x) = (\<exists>j \<in> {1..d}. P j)"
  (is "?LHS = ?RHS")
proof
  assume ?LHS
  then obtain x where P: "P x" ..
  have "x mod d = x - (x div d)*d" by(simp add:mult_div_mod_eq [symmetric] ac_simps eq_diff_eq)
  hence Pmod: "P x = P(x mod d)" using modd by simp
  show ?RHS
  proof (cases)
    assume "x mod d = 0"
    hence "P 0" using P Pmod by simp
    moreover have "P 0 = P(0 - (-1)*d)" using modd by blast
    ultimately have "P d" by simp
    moreover have "d \<in> {1..d}" using dpos by simp
    ultimately show ?RHS ..
  next
    assume not0: "x mod d \<noteq> 0"
    have "P(x mod d)" using dpos P Pmod by simp
    moreover have "x mod d \<in> {1..d}"
    proof -
      from dpos have "0 \<le> x mod d" by(rule pos_mod_sign)
      moreover from dpos have "x mod d < d" by(rule pos_mod_bound)
      ultimately show ?thesis using not0 by simp
    qed
    ultimately show ?RHS ..
  qed
qed auto

subsubsection\<open>The \<open>-\<infinity>\<close> Version\<close>

lemma decr_lemma: "0 < (d::int) \<Longrightarrow> x - (\<bar>x - z\<bar> + 1) * d < z"
  by (induct rule: int_gr_induct) (simp_all add: int_distrib)

lemma incr_lemma: "0 < (d::int) \<Longrightarrow> z < x + (\<bar>x - z\<bar> + 1) * d"
  by (induct rule: int_gr_induct) (simp_all add: int_distrib)

lemma decr_mult_lemma:
  assumes dpos: "(0::int) < d" and minus: "\<forall>x. P x \<longrightarrow> P(x - d)" and knneg: "0 <= k"
  shows "\<forall>x. P x \<longrightarrow> P(x - k*d)"
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
    P1eqP1: "\<forall>x k. P1 x = P1(x - k*d)" and ePeqP1: "\<exists>z::int. \<forall>x. x < z \<longrightarrow> (P x = P1 x)"
  shows "(\<exists>x. P1 x) \<longrightarrow> (\<exists>x. P x)"
proof
  assume eP1: "\<exists>x. P1 x"
  then obtain x where P1: "P1 x" ..
  from ePeqP1 obtain z where P1eqP: "\<forall>x. x < z \<longrightarrow> (P x = P1 x)" ..
  let ?w = "x - (\<bar>x - z\<bar> + 1) * d"
  from dpos have w: "?w < z" by(rule decr_lemma)
  have "P1 x = P1 ?w" using P1eqP1 by blast
  also have "\<dots> = P(?w)" using w P1eqP by blast
  finally have "P ?w" using P1 by blast
  thus "\<exists>x. P x" ..
qed

lemma cpmi: 
  assumes dp: "0 < D" and p1:"\<exists>z. \<forall> x< z. P x = P' x"
  and nb:"\<forall>x.(\<forall> j\<in> {1..D}. \<forall>(b::int) \<in> B. x \<noteq> b+j) \<longrightarrow> P (x) \<longrightarrow> P (x - D)"
  and pd: "\<forall> x k. P' x = P' (x-k*D)"
  shows "(\<exists>x. P x) = ((\<exists>j \<in> {1..D} . P' j) \<or> (\<exists>j \<in> {1..D}. \<exists> b \<in> B. P (b+j)))"
         (is "?L = (?R1 \<or> ?R2)")
proof-
 {assume "?R2" hence "?L"  by blast}
 moreover
 {assume H:"?R1" hence "?L" using minusinfinity[OF dp pd p1] periodic_finite_ex[OF dp pd] by simp}
 moreover 
 { fix x
   assume P: "P x" and H: "\<not> ?R2"
   {fix y assume "\<not> (\<exists>j\<in>{1..D}. \<exists>b\<in>B. P (b + j))" and P: "P y"
     hence "\<not>(\<exists>(j::int) \<in> {1..D}. \<exists>(b::int) \<in> B. y = b+j)" by auto
     with nb P  have "P (y - D)" by auto }
   hence "\<forall>x. \<not>(\<exists>(j::int) \<in> {1..D}. \<exists>(b::int) \<in> B. P(b+j)) \<longrightarrow> P (x) \<longrightarrow> P (x - D)" by blast
   with H P have th: " \<forall>x. P x \<longrightarrow> P (x - D)" by auto
   from p1 obtain z where z: "\<forall>x. x < z \<longrightarrow> (P x = P' x)" by blast
   let ?y = "x - (\<bar>x - z\<bar> + 1)*D"
   have zp: "0 <= (\<bar>x - z\<bar> + 1)" by arith
   from dp have yz: "?y < z" using decr_lemma[OF dp] by simp   
   from z[rule_format, OF yz] decr_mult_lemma[OF dp th zp, rule_format, OF P] have th2: " P' ?y" by auto
   with periodic_finite_ex[OF dp pd]
   have "?R1" by blast}
 ultimately show ?thesis by blast
qed

subsubsection \<open>The \<open>+\<infinity>\<close> Version\<close>

lemma  plusinfinity:
  assumes dpos: "(0::int) < d" and
    P1eqP1: "\<forall>x k. P' x = P'(x - k*d)" and ePeqP1: "\<exists> z. \<forall> x>z. P x = P' x"
  shows "(\<exists> x. P' x) \<longrightarrow> (\<exists> x. P x)"
proof
  assume eP1: "\<exists>x. P' x"
  then obtain x where P1: "P' x" ..
  from ePeqP1 obtain z where P1eqP: "\<forall>x>z. P x = P' x" ..
  let ?w' = "x + (\<bar>x - z\<bar> + 1) * d"
  let ?w = "x - (- (\<bar>x - z\<bar> + 1)) * d"
  have ww'[simp]: "?w = ?w'" by (simp add: algebra_simps)
  from dpos have w: "?w > z" by(simp only: ww' incr_lemma)
  hence "P' x = P' ?w" using P1eqP1 by blast
  also have "\<dots> = P(?w)" using w P1eqP by blast
  finally have "P ?w" using P1 by blast
  thus "\<exists>x. P x" ..
qed

lemma incr_mult_lemma:
  assumes dpos: "(0::int) < d" and plus: "\<forall>x::int. P x \<longrightarrow> P(x + d)" and knneg: "0 <= k"
  shows "\<forall>x. P x \<longrightarrow> P(x + k*d)"
using knneg
proof (induct rule:int_ge_induct)
  case base thus ?case by simp
next
  case (step i)
  {fix x
    have "P x \<longrightarrow> P (x + i * d)" using step.hyps by blast
    also have "\<dots> \<longrightarrow> P(x + (i + 1) * d)" using plus[THEN spec, of "x + i * d"]
      by (simp add:int_distrib ac_simps)
    ultimately have "P x \<longrightarrow> P(x + (i + 1) * d)" by blast}
  thus ?case ..
qed

lemma cppi: 
  assumes dp: "0 < D" and p1:"\<exists>z. \<forall> x> z. P x = P' x"
  and nb:"\<forall>x.(\<forall> j\<in> {1..D}. \<forall>(b::int) \<in> A. x \<noteq> b - j) \<longrightarrow> P (x) \<longrightarrow> P (x + D)"
  and pd: "\<forall> x k. P' x= P' (x-k*D)"
  shows "(\<exists>x. P x) = ((\<exists>j \<in> {1..D} . P' j) \<or> (\<exists> j \<in> {1..D}. \<exists> b\<in> A. P (b - j)))" (is "?L = (?R1 \<or> ?R2)")
proof-
 {assume "?R2" hence "?L"  by blast}
 moreover
 {assume H:"?R1" hence "?L" using plusinfinity[OF dp pd p1] periodic_finite_ex[OF dp pd] by simp}
 moreover 
 { fix x
   assume P: "P x" and H: "\<not> ?R2"
   {fix y assume "\<not> (\<exists>j\<in>{1..D}. \<exists>b\<in>A. P (b - j))" and P: "P y"
     hence "\<not>(\<exists>(j::int) \<in> {1..D}. \<exists>(b::int) \<in> A. y = b - j)" by auto
     with nb P  have "P (y + D)" by auto }
   hence "\<forall>x. \<not>(\<exists>(j::int) \<in> {1..D}. \<exists>(b::int) \<in> A. P(b-j)) \<longrightarrow> P (x) \<longrightarrow> P (x + D)" by blast
   with H P have th: " \<forall>x. P x \<longrightarrow> P (x + D)" by auto
   from p1 obtain z where z: "\<forall>x. x > z \<longrightarrow> (P x = P' x)" by blast
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
  unfolding dvd_def by (rule eq_reflection, rule iffI) auto

lemma zdvd_mono:
  fixes k m t :: int
  assumes "k \<noteq> 0"
  shows "m dvd t \<equiv> k * m dvd k * t" 
  using assms by simp

lemma uminus_dvd_conv:
  fixes d t :: int
  shows "d dvd t \<equiv> - d dvd t" and "d dvd t \<equiv> d dvd - t"
  by simp_all

text \<open>\bigskip Theorems for transforming predicates on nat to predicates on \<open>int\<close>\<close>

lemma zdiff_int_split: "P (int (x - y)) =
  ((y \<le> x \<longrightarrow> P (int x - int y)) \<and> (x < y \<longrightarrow> P 0))"
  by (cases "y \<le> x") (simp_all add: of_nat_diff)

text \<open>
  \medskip Specific instances of congruence rules, to prevent
  simplifier from looping.\<close>

theorem imp_le_cong:
  "\<lbrakk>x = x'; 0 \<le> x' \<Longrightarrow> P = P'\<rbrakk> \<Longrightarrow> (0 \<le> (x::int) \<longrightarrow> P) = (0 \<le> x' \<longrightarrow> P')"
  by simp

theorem conj_le_cong:
  "\<lbrakk>x = x'; 0 \<le> x' \<Longrightarrow> P = P'\<rbrakk> \<Longrightarrow> (0 \<le> (x::int) \<and> P) = (0 \<le> x' \<and> P')"
  by (simp cong: conj_cong)

ML_file \<open>Tools/Qelim/cooper.ML\<close>

method_setup presburger = \<open>
  let
    fun keyword k = Scan.lift (Args.$$$ k -- Args.colon) >> K ()
    fun simple_keyword k = Scan.lift (Args.$$$ k) >> K ()
    val addN = "add"
    val delN = "del"
    val elimN = "elim"
    val any_keyword = keyword addN || keyword delN || simple_keyword elimN
    val thms = Scan.repeats (Scan.unless any_keyword Attrib.multi_thm)
  in
    Scan.optional (simple_keyword elimN >> K false) true --
    Scan.optional (keyword addN |-- thms) [] --
    Scan.optional (keyword delN |-- thms) [] >>
    (fn ((elim, add_ths), del_ths) => fn ctxt =>
      SIMPLE_METHOD' (Cooper.tac elim add_ths del_ths ctxt))
  end
\<close> "Cooper's algorithm for Presburger arithmetic"

declare mod_eq_0_iff_dvd [presburger]
declare mod_by_Suc_0 [presburger] 
declare mod_0 [presburger]
declare mod_by_1 [presburger]
declare mod_self [presburger]
declare div_by_0 [presburger]
declare mod_by_0 [presburger]
declare mod_div_trivial [presburger]
declare mult_div_mod_eq [presburger]
declare div_mult_mod_eq [presburger]
declare mod_mult_self1 [presburger]
declare mod_mult_self2 [presburger]
declare mod2_Suc_Suc [presburger]
declare not_mod_2_eq_0_eq_1 [presburger] 
declare nat_zero_less_power_iff [presburger]

lemma [presburger, algebra]: "m mod 2 = (1::nat) \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger, algebra]: "m mod 2 = Suc 0 \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger, algebra]: "m mod (Suc (Suc 0)) = (1::nat) \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger, algebra]: "m mod (Suc (Suc 0)) = Suc 0 \<longleftrightarrow> \<not> 2 dvd m " by presburger
lemma [presburger, algebra]: "m mod 2 = (1::int) \<longleftrightarrow> \<not> 2 dvd m " by presburger

context semiring_parity
begin

declare even_mult_iff [presburger]

declare even_power [presburger]

lemma [presburger]:
  "even (a + b) \<longleftrightarrow> even a \<and> even b \<or> odd a \<and> odd b"
  by auto

end

context ring_parity
begin

declare even_minus [presburger]

end

context linordered_idom
begin

declare zero_le_power_eq [presburger]

declare zero_less_power_eq [presburger]

declare power_less_zero_eq [presburger]
  
declare power_le_zero_eq [presburger]

end

declare even_Suc [presburger]

lemma [presburger]:
  "Suc n div Suc (Suc 0) = n div Suc (Suc 0) \<longleftrightarrow> even n"
  by presburger

declare even_diff_nat [presburger]

lemma [presburger]:
  fixes k :: int
  shows "(k + 1) div 2 = k div 2 \<longleftrightarrow> even k"
  by presburger

lemma [presburger]:
  fixes k :: int
  shows "(k + 1) div 2 = k div 2 + 1 \<longleftrightarrow> odd k"
  by presburger

lemma [presburger]:
  "even n \<longleftrightarrow> even (int n)"
  by simp
  

subsection \<open>Nice facts about division by \<^term>\<open>4\<close>\<close>  

lemma even_even_mod_4_iff:
  "even (n::nat) \<longleftrightarrow> even (n mod 4)"
  by presburger

lemma odd_mod_4_div_2:
  "n mod 4 = (3::nat) \<Longrightarrow> odd ((n - Suc 0) div 2)"
  by presburger

lemma even_mod_4_div_2:
  "n mod 4 = Suc 0 \<Longrightarrow> even ((n - Suc 0) div 2)"
  by presburger

end
