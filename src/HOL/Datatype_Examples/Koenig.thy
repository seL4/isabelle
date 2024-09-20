(*  Title:      HOL/Datatype_Examples/Koenig.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Koenig's lemma.
*)

section \<open>Koenig's Lemma\<close>

theory Koenig
imports TreeFI "HOL-Library.Stream"
begin

(* infinite trees: *)
coinductive infiniteTr where
"\<lbrakk>tr' \<in> set (sub tr); infiniteTr tr'\<rbrakk> \<Longrightarrow> infiniteTr tr"

lemma infiniteTr_strong_coind[consumes 1, case_names sub]:
assumes *: "phi tr" and
**: "\<And> tr. phi tr \<Longrightarrow> \<exists> tr' \<in> set (sub tr). phi tr' \<or> infiniteTr tr'"
shows "infiniteTr tr"
using assms by (elim infiniteTr.coinduct) blast

lemma infiniteTr_coind[consumes 1, case_names sub, induct pred: infiniteTr]:
assumes *: "phi tr" and
**: "\<And> tr. phi tr \<Longrightarrow> \<exists> tr' \<in> set (sub tr). phi tr'"
shows "infiniteTr tr"
using assms by (elim infiniteTr.coinduct) blast

lemma infiniteTr_sub[simp]:
"infiniteTr tr \<Longrightarrow> (\<exists> tr' \<in> set (sub tr). infiniteTr tr')"
by (erule infiniteTr.cases) blast

primcorec konigPath where
  "shd (konigPath t) = lab t"
| "stl (konigPath t) = konigPath (SOME tr. tr \<in> set (sub t) \<and> infiniteTr tr)"

(* proper paths in trees: *)
coinductive properPath where
"\<lbrakk>shd as = lab tr; tr' \<in> set (sub tr); properPath (stl as) tr'\<rbrakk> \<Longrightarrow>
 properPath as tr"

lemma properPath_strong_coind[consumes 1, case_names shd_lab sub]:
assumes *: "phi as tr" and
**: "\<And> as tr. phi as tr \<Longrightarrow> shd as = lab tr" and
***: "\<And> as tr.
         phi as tr \<Longrightarrow>
         \<exists> tr' \<in> set (sub tr). phi (stl as) tr' \<or> properPath (stl as) tr'"
shows "properPath as tr"
using assms by (elim properPath.coinduct) blast

lemma properPath_coind[consumes 1, case_names shd_lab sub, induct pred: properPath]:
assumes *: "phi as tr" and
**: "\<And> as tr. phi as tr \<Longrightarrow> shd as = lab tr" and
***: "\<And> as tr.
         phi as tr \<Longrightarrow>
         \<exists> tr' \<in> set (sub tr). phi (stl as) tr'"
shows "properPath as tr"
using properPath_strong_coind[of phi, OF * **] *** by blast

lemma properPath_shd_lab:
"properPath as tr \<Longrightarrow> shd as = lab tr"
by (erule properPath.cases) blast

lemma properPath_sub:
"properPath as tr \<Longrightarrow>
 \<exists> tr' \<in> set (sub tr). phi (stl as) tr' \<or> properPath (stl as) tr'"
by (erule properPath.cases) blast

(* prove the following by coinduction *)
theorem Konig:
  assumes "infiniteTr tr"
  shows "properPath (konigPath tr) tr"
proof-
  {fix as
   assume "infiniteTr tr \<and> as = konigPath tr" hence "properPath as tr"
   proof (coinduction arbitrary: tr as rule: properPath_coind)
     case (sub tr as)
     let ?t = "SOME t'. t' \<in> set (sub tr) \<and> infiniteTr t'"
     from sub have "\<exists>t' \<in> set (sub tr). infiniteTr t'" by simp
     then have "\<exists>t'. t' \<in> set (sub tr) \<and> infiniteTr t'" by blast
     then have "?t \<in> set (sub tr) \<and> infiniteTr ?t" by (rule someI_ex)
     moreover have "stl (konigPath tr) = konigPath ?t" by simp
     ultimately show ?case using sub by blast
   qed simp
  }
  thus ?thesis using assms by blast
qed

(* some more stream theorems *)

primcorec plus :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infixr \<open>\<oplus>\<close> 66) where
  "shd (plus xs ys) = shd xs + shd ys"
| "stl (plus xs ys) = plus (stl xs) (stl ys)"

definition scalar :: "nat \<Rightarrow> nat stream \<Rightarrow> nat stream" (infixr \<open>\<cdot>\<close> 68) where
  [simp]: "scalar n = smap (\<lambda>x. n * x)"

primcorec ones :: "nat stream" where "ones = 1 ## ones"
primcorec twos :: "nat stream" where "twos = 2 ## twos"
definition ns :: "nat \<Rightarrow> nat stream" where [simp]: "ns n = scalar n ones"

lemma "ones \<oplus> ones = twos"
  by coinduction simp

lemma "n \<cdot> twos = ns (2 * n)"
  by coinduction simp

lemma prod_scalar: "(n * m) \<cdot> xs = n \<cdot> m \<cdot> xs"
  by (coinduction arbitrary: xs) auto

lemma scalar_plus: "n \<cdot> (xs \<oplus> ys) = n \<cdot> xs \<oplus> n \<cdot> ys"
  by (coinduction arbitrary: xs ys) (auto simp: add_mult_distrib2)

lemma plus_comm: "xs \<oplus> ys = ys \<oplus> xs"
  by (coinduction arbitrary: xs ys) auto

lemma plus_assoc: "(xs \<oplus> ys) \<oplus> zs = xs \<oplus> ys \<oplus> zs"
  by (coinduction arbitrary: xs ys zs) auto

end
