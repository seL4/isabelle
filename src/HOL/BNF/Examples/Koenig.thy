(*  Title:      HOL/BNF/Examples/Koenig.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Koenig's lemma.
*)

header {* Koenig's lemma *}

theory Koenig
imports TreeFI Stream
begin

(* selectors for streams *)
lemma shd_def': "shd as = fst (stream_dtor as)"
apply (case_tac as)
apply (auto simp add: shd_def)
by (simp add: Stream_def stream.dtor_ctor)

lemma stl_def': "stl as = snd (stream_dtor as)"
apply (case_tac as)
apply (auto simp add: stl_def)
by (simp add: Stream_def stream.dtor_ctor)

lemma unfold_pair_fun_shd[simp]: "shd (stream_dtor_unfold (f \<odot> g) t) = f t"
unfolding shd_def' pair_fun_def stream.dtor_unfold by simp

lemma unfold_pair_fun_stl[simp]: "stl (stream_dtor_unfold (f \<odot> g) t) =
 stream_dtor_unfold (f \<odot> g) (g t)"
unfolding stl_def' pair_fun_def stream.dtor_unfold by simp

(* infinite trees: *)
coinductive infiniteTr where
"\<lbrakk>tr' \<in> listF_set (sub tr); infiniteTr tr'\<rbrakk> \<Longrightarrow> infiniteTr tr"

lemma infiniteTr_strong_coind[consumes 1, case_names sub]:
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

definition "konigPath \<equiv> stream_dtor_unfold
  (lab \<odot> (\<lambda>tr. SOME tr'. tr' \<in> listF_set (sub tr) \<and> infiniteTr tr'))"

lemma konigPath_simps[simp]:
"shd (konigPath t) = lab t"
"stl (konigPath t) = konigPath (SOME tr. tr \<in> listF_set (sub t) \<and> infiniteTr tr)"
unfolding konigPath_def by simp+

(* proper paths in trees: *)
coinductive properPath where
"\<lbrakk>shd as = lab tr; tr' \<in> listF_set (sub tr); properPath (stl as) tr'\<rbrakk> \<Longrightarrow>
 properPath as tr"

lemma properPath_strong_coind[consumes 1, case_names shd_lab sub]:
assumes *: "phi as tr" and
**: "\<And> as tr. phi as tr \<Longrightarrow> shd as = lab tr" and
***: "\<And> as tr.
         phi as tr \<Longrightarrow>
         \<exists> tr' \<in> listF_set (sub tr). phi (stl as) tr' \<or> properPath (stl as) tr'"
shows "properPath as tr"
using assms by (elim properPath.coinduct) blast

lemma properPath_coind[consumes 1, case_names shd_lab sub, induct pred: properPath]:
assumes *: "phi as tr" and
**: "\<And> as tr. phi as tr \<Longrightarrow> shd as = lab tr" and
***: "\<And> as tr.
         phi as tr \<Longrightarrow>
         \<exists> tr' \<in> listF_set (sub tr). phi (stl as) tr'"
shows "properPath as tr"
using properPath_strong_coind[of phi, OF * **] *** by blast

lemma properPath_shd_lab:
"properPath as tr \<Longrightarrow> shd as = lab tr"
by (erule properPath.cases) blast

lemma properPath_sub:
"properPath as tr \<Longrightarrow>
 \<exists> tr' \<in> listF_set (sub tr). phi (stl as) tr' \<or> properPath (stl as) tr'"
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
     moreover have "stl (konigPath t) = konigPath ?t" by simp
     ultimately show "\<exists>t' \<in> listF_set (sub t).
             infiniteTr t' \<and> stl (konigPath t) = konigPath t'" by blast
   qed simp
  }
  thus ?thesis using assms by blast
qed

(* some more stream theorems *)

lemma stream_map[simp]: "smap f = stream_dtor_unfold (f o shd \<odot> stl)"
unfolding smap_def pair_fun_def shd_def'[abs_def] stl_def'[abs_def]
  map_pair_def o_def prod_case_beta by simp

definition plus :: "nat stream \<Rightarrow> nat stream \<Rightarrow> nat stream" (infixr "\<oplus>" 66) where
  [simp]: "plus xs ys =
    stream_dtor_unfold ((%(xs, ys). shd xs + shd ys) \<odot> (%(xs, ys). (stl xs, stl ys))) (xs, ys)"

definition scalar :: "nat \<Rightarrow> nat stream \<Rightarrow> nat stream" (infixr "\<cdot>" 68) where
  [simp]: "scalar n = smap (\<lambda>x. n * x)"

definition ones :: "nat stream" where [simp]: "ones = stream_dtor_unfold ((%x. 1) \<odot> id) ()"
definition twos :: "nat stream" where [simp]: "twos = stream_dtor_unfold ((%x. 2) \<odot> id) ()"
definition ns :: "nat \<Rightarrow> nat stream" where [simp]: "ns n = scalar n ones"

lemma "ones \<oplus> ones = twos"
by (rule stream.coinduct[of "%x1 x2. \<exists>x. x1 = ones \<oplus> ones \<and> x2 = twos"]) auto

lemma "n \<cdot> twos = ns (2 * n)"
by (rule stream.coinduct[of "%x1 x2. \<exists>n. x1 = n \<cdot> twos \<and> x2 = ns (2 * n)"]) force+

lemma prod_scalar: "(n * m) \<cdot> xs = n \<cdot> m \<cdot> xs"
by (rule stream.coinduct[of "%x1 x2. \<exists>n m xs. x1 = (n * m) \<cdot> xs \<and> x2 = n \<cdot> m \<cdot> xs"]) force+

lemma scalar_plus: "n \<cdot> (xs \<oplus> ys) = n \<cdot> xs \<oplus> n \<cdot> ys"
by (rule stream.coinduct[of "%x1 x2. \<exists>n xs ys. x1 = n \<cdot> (xs \<oplus> ys) \<and> x2 = n \<cdot> xs \<oplus> n \<cdot> ys"])
   (force simp: add_mult_distrib2)+

lemma plus_comm: "xs \<oplus> ys = ys \<oplus> xs"
by (rule stream.coinduct[of "%x1 x2. \<exists>xs ys. x1 = xs \<oplus> ys \<and> x2 = ys \<oplus> xs"]) force+

lemma plus_assoc: "(xs \<oplus> ys) \<oplus> zs = xs \<oplus> ys \<oplus> zs"
by (rule stream.coinduct[of "%x1 x2. \<exists>xs ys zs. x1 = (xs \<oplus> ys) \<oplus> zs \<and> x2 = xs \<oplus> ys \<oplus> zs"]) force+

end
