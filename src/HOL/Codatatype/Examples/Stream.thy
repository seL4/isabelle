(*  Title:      Codatatype_Examples/Stream.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Infinite streams.
*)

header {* Infinite Streams *}

theory Stream
imports TreeFI
begin

codata_raw stream: 's = "'a \<times> 's"

(* selectors for streams *)
definition "hdd as \<equiv> fst (stream_unf as)"
definition "tll as \<equiv> snd (stream_unf as)"

lemma coiter_pair_fun_hdd[simp]: "hdd (stream_unf_coiter (f \<odot> g) t) = f t"
unfolding hdd_def pair_fun_def stream.unf_coiter by simp

lemma coiter_pair_fun_tll[simp]: "tll (stream_unf_coiter (f \<odot> g) t) =
 stream_unf_coiter (f \<odot> g) (g t)"
unfolding tll_def pair_fun_def stream.unf_coiter by simp

(* infinite trees: *)
coinductive infiniteTr where
"\<lbrakk>tr' \<in> listF_set (sub tr); infiniteTr tr'\<rbrakk> \<Longrightarrow> infiniteTr tr"

lemma infiniteTr_coind_upto[consumes 1, case_names sub]:
assumes *: "phi tr" and
**: "\<And> tr. phi tr \<Longrightarrow> \<exists> tr' \<in> listF_set (sub tr). phi tr' \<or> infiniteTr tr'"
shows "infiniteTr tr"
using assms by (elim infiniteTr.coinduct) blast

lemma infiniteTr_coind[consumes 1, case_names sub, induct pred: infiniteTr]:
assumes *: "phi tr" and
**: "\<And> tr. phi tr \<Longrightarrow> \<exists> tr' \<in> listF_set (sub tr). phi tr'"
shows "infiniteTr tr"
using assms by (elim infiniteTr.coinduct) blast

lemma infiniteTr_sub[simp]:
"infiniteTr tr \<Longrightarrow> (\<exists> tr' \<in> listF_set (sub tr). infiniteTr tr')"
by (erule infiniteTr.cases) blast

definition "konigPath \<equiv> stream_unf_coiter
  (lab \<odot> (\<lambda>tr. SOME tr'. tr' \<in> listF_set (sub tr) \<and> infiniteTr tr'))"

lemma hdd_simps1[simp]: "hdd (konigPath t) = lab t"
unfolding konigPath_def by simp

lemma tll_simps2[simp]: "tll (konigPath t) =
  konigPath (SOME tr. tr \<in> listF_set (sub t) \<and> infiniteTr tr)"
unfolding konigPath_def by simp

(* proper paths in trees: *)
coinductive properPath where
"\<lbrakk>hdd as = lab tr; tr' \<in> listF_set (sub tr); properPath (tll as) tr'\<rbrakk> \<Longrightarrow>
 properPath as tr"

lemma properPath_coind_upto[consumes 1, case_names hdd_lab sub]:
assumes *: "phi as tr" and
**: "\<And> as tr. phi as tr \<Longrightarrow> hdd as = lab tr" and
***: "\<And> as tr.
         phi as tr \<Longrightarrow>
         \<exists> tr' \<in> listF_set (sub tr). phi (tll as) tr' \<or> properPath (tll as) tr'"
shows "properPath as tr"
using assms by (elim properPath.coinduct) blast

lemma properPath_coind[consumes 1, case_names hdd_lab sub, induct pred: properPath]:
assumes *: "phi as tr" and
**: "\<And> as tr. phi as tr \<Longrightarrow> hdd as = lab tr" and
***: "\<And> as tr.
         phi as tr \<Longrightarrow>
         \<exists> tr' \<in> listF_set (sub tr). phi (tll as) tr'"
shows "properPath as tr"
using properPath_coind_upto[of phi, OF * **] *** by blast

lemma properPath_hdd_lab:
"properPath as tr \<Longrightarrow> hdd as = lab tr"
by (erule properPath.cases) blast

lemma properPath_sub:
"properPath as tr \<Longrightarrow>
 \<exists> tr' \<in> listF_set (sub tr). phi (tll as) tr' \<or> properPath (tll as) tr'"
by (erule properPath.cases) blast

(* prove the following by coinduction *)
theorem Konig:
  assumes "infiniteTr tr"
  shows "properPath (konigPath tr) tr"
proof-
  {fix as
   assume "infiniteTr tr \<and> as = konigPath tr" hence "properPath as tr"
   proof (induct rule: properPath_coind, safe)
     fix t
     let ?t = "SOME t'. t' \<in> listF_set (sub t) \<and> infiniteTr t'"
     assume "infiniteTr t"
     hence "\<exists>t' \<in> listF_set (sub t). infiniteTr t'" by simp
     hence "\<exists>t'. t' \<in> listF_set (sub t) \<and> infiniteTr t'" by blast
     hence "?t \<in> listF_set (sub t) \<and> infiniteTr ?t" by (elim someI_ex)
     moreover have "tll (konigPath t) = konigPath ?t" by simp
     ultimately show "\<exists>t' \<in> listF_set (sub t).
             infiniteTr t' \<and> tll (konigPath t) = konigPath t'" by blast
   qed simp
  }
  thus ?thesis using assms by blast
qed

(* some more stream theorems *)

lemma stream_map[simp]: "stream_map f = stream_unf_coiter (f o hdd \<odot> tll)"
unfolding stream_map_def pair_fun_def hdd_def[abs_def] tll_def[abs_def]
  map_pair_def o_def prod_case_beta by simp

lemma streamBNF_pred[simp]: "streamBNF_pred \<phi>1 \<phi>2 a b = (\<phi>1 (fst a) (fst b) \<and> \<phi>2 (snd a) (snd b))"
by (auto simp: streamBNF.pred_unfold)

lemmas stream_coind = mp[OF stream.pred_coinduct, unfolded streamBNF_pred[abs_def],
  folded hdd_def tll_def]

definition plus :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infixr "\<oplus>" 66) where
  [simp]: "plus xs ys =
    stream_unf_coiter ((%(xs, ys). hdd xs + hdd ys) \<odot> (%(xs, ys). (tll xs, tll ys))) (xs, ys)"

definition scalar :: "nat \<Rightarrow> nat stream \<Rightarrow> nat stream" (infixr "\<cdot>" 68) where
  [simp]: "scalar n = stream_map (\<lambda>x. n * x)"

definition ones :: "nat stream" where [simp]: "ones = stream_unf_coiter ((%x. 1) \<odot> id) ()"
definition twos :: "nat stream" where [simp]: "twos = stream_unf_coiter ((%x. 2) \<odot> id) ()"
definition ns :: "nat \<Rightarrow> nat stream" where [simp]: "ns n = scalar n ones"

lemma "ones \<oplus> ones = twos"
by (intro stream_coind[where phi="%x1 x2. \<exists>x. x1 = ones \<oplus> ones \<and> x2 = twos"])
   auto

lemma "n \<cdot> twos = ns (2 * n)"
by (intro stream_coind[where phi="%x1 x2. \<exists>n. x1 = n \<cdot> twos \<and> x2 = ns (2 * n)"])
   force+

lemma prod_scalar: "(n * m) \<cdot> xs = n \<cdot> m \<cdot> xs"
by (intro stream_coind[where phi="%x1 x2. \<exists>n m xs. x1 = (n * m) \<cdot> xs \<and> x2 = n \<cdot> m \<cdot> xs"])
   force+

lemma scalar_plus: "n \<cdot> (xs \<oplus> ys) = n \<cdot> xs \<oplus> n \<cdot> ys"
by (intro stream_coind[where phi="%x1 x2. \<exists>n xs ys. x1 = n \<cdot> (xs \<oplus> ys) \<and> x2 = n \<cdot> xs \<oplus> n \<cdot> ys"])
   (force simp: add_mult_distrib2)+

lemma plus_comm: "xs \<oplus> ys = ys \<oplus> xs"
by (intro stream_coind[where phi="%x1 x2. \<exists>xs ys. x1 = xs \<oplus> ys \<and> x2 = ys \<oplus> xs"])
   force+

lemma plus_assoc: "(xs \<oplus> ys) \<oplus> zs = xs \<oplus> ys \<oplus> zs"
by (intro stream_coind[where phi="%x1 x2. \<exists>xs ys zs. x1 = (xs \<oplus> ys) \<oplus> zs \<and> x2 = xs \<oplus> ys \<oplus> zs"])
   force+

end
