(*  Title:      HOL/BNF/Examples/Stream.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012

Infinite streams.
*)

header {* Infinite Streams *}

theory Stream
imports "../BNF"
begin

codata 'a stream = Stream (shd: 'a) (stl: "'a stream")

(* TODO: Provide by the package*)
theorem stream_set_induct:
   "\<lbrakk>\<And>s. P (shd s) s; \<And>s y. \<lbrakk>y \<in> stream_set (stl s); P y (stl s)\<rbrakk> \<Longrightarrow> P y s\<rbrakk> \<Longrightarrow>
   \<forall>y \<in> stream_set s. P y s"
by (rule stream.dtor_set_induct)
   (auto simp add:  shd_def stl_def stream_case_def fsts_def snds_def split_beta)

theorem shd_stream_set: "shd s \<in> stream_set s"
by (auto simp add: shd_def stl_def stream_case_def fsts_def snds_def split_beta)
   (metis UnCI fsts_def insertI1 stream.dtor_set)

theorem stl_stream_set: "y \<in> stream_set (stl s) \<Longrightarrow> y \<in> stream_set s"
by (auto simp add: shd_def stl_def stream_case_def fsts_def snds_def split_beta)
   (metis insertI1 set_mp snds_def stream.dtor_set_set_incl)

(* only for the non-mutual case: *)
theorem stream_set_induct1[consumes 1, case_names shd stl, induct set: "stream_set"]:
  assumes "y \<in> stream_set s" and "\<And>s. P (shd s) s"
  and "\<And>s y. \<lbrakk>y \<in> stream_set (stl s); P y (stl s)\<rbrakk> \<Longrightarrow> P y s"
  shows "P y s"
using assms stream_set_induct by blast
(* end TODO *)


subsection {* prepend list to stream *}

primrec shift :: "'a list \<Rightarrow> 'a stream \<Rightarrow> 'a stream" (infixr "@-" 65) where
  "shift [] s = s"
| "shift (x # xs) s = Stream x (shift xs s)"

lemma shift_append[simp]: "(xs @ ys) @- s = xs @- ys @- s"
by (induct xs) auto

lemma shift_simps[simp]:
   "shd (xs @- s) = (if xs = [] then shd s else hd xs)"
   "stl (xs @- s) = (if xs = [] then stl s else tl xs @- s)"
by (induct xs) auto


subsection {* recurring stream out of a list *}

definition cycle :: "'a list \<Rightarrow> 'a stream" where
  "cycle = stream_unfold hd (\<lambda>xs. tl xs @ [hd xs])"

lemma cycle_simps[simp]:
  "shd (cycle u) = hd u"
  "stl (cycle u) = cycle (tl u @ [hd u])"
by (auto simp: cycle_def)


lemma cycle_decomp: "u \<noteq> [] \<Longrightarrow> cycle u = u @- cycle u"
proof (coinduct rule: stream.coinduct[of "\<lambda>s1 s2. \<exists>u. s1 = cycle u \<and> s2 = u @- cycle u \<and> u \<noteq> []"])
  case (2 s1 s2)
  then obtain u where "s1 = cycle u \<and> s2 = u @- cycle u \<and> u \<noteq> []" by blast
  thus ?case using stream.unfold[of hd "\<lambda>xs. tl xs @ [hd xs]" u] by (auto simp: cycle_def)
qed auto

lemma cycle_Cons: "cycle (x # xs) = Stream x (cycle (xs @ [x]))"
proof (coinduct rule: stream.coinduct[of "\<lambda>s1 s2. \<exists>x xs. s1 = cycle (x # xs) \<and> s2 = Stream x (cycle (xs @ [x]))"])
  case (2 s1 s2)
  then obtain x xs where "s1 = cycle (x # xs) \<and> s2 = Stream x (cycle (xs @ [x]))" by blast
  thus ?case
    by (auto simp: cycle_def intro!: exI[of _ "hd (xs @ [x])"] exI[of _ "tl (xs @ [x])"] stream.unfold)
qed auto

coinductive_set
  streams :: "'a set => 'a stream set"
  for A :: "'a set"
where
  Stream[intro!, simp, no_atp]: "\<lbrakk>a \<in> A; s \<in> streams A\<rbrakk> \<Longrightarrow> Stream a s \<in> streams A"

lemma shift_streams: "\<lbrakk>w \<in> lists A; s \<in> streams A\<rbrakk> \<Longrightarrow> w @- s \<in> streams A"
by (induct w) auto

lemma stream_set_streams:
  assumes "stream_set s \<subseteq> A"
  shows "s \<in> streams A"
proof (coinduct rule: streams.coinduct[of "\<lambda>s'. \<exists>a s. s' = Stream a s \<and> a \<in> A \<and> stream_set s \<subseteq> A"])
  case streams from assms show ?case by (cases s) auto
next
  fix s' assume "\<exists>a s. s' = Stream a s \<and> a \<in> A \<and> stream_set s \<subseteq> A"
  then guess a s by (elim exE)
  with assms show "\<exists>a l. s' = Stream a l \<and>
    a \<in> A \<and> ((\<exists>a s. l = Stream a s \<and> a \<in> A \<and> stream_set s \<subseteq> A) \<or> l \<in> streams A)"
    by (cases s) auto
qed


subsection {* flatten a stream of lists *}

definition flat where
  "flat \<equiv> stream_unfold (hd o shd) (\<lambda>s. if tl (shd s) = [] then stl s else Stream (tl (shd s)) (stl s))"

lemma flat_simps[simp]:
  "shd (flat ws) = hd (shd ws)"
  "stl (flat ws) = flat (if tl (shd ws) = [] then stl ws else Stream (tl (shd ws)) (stl ws))"
unfolding flat_def by auto

lemma flat_Cons[simp]: "flat (Stream (x#xs) w) = Stream x (flat (if xs = [] then w else Stream xs w))"
unfolding flat_def using stream.unfold[of "hd o shd" _ "Stream (x#xs) w"] by auto

lemma flat_Stream[simp]: "xs \<noteq> [] \<Longrightarrow> flat (Stream xs ws) = xs @- flat ws"
by (induct xs) auto

lemma flat_unfold: "shd ws \<noteq> [] \<Longrightarrow> flat ws = shd ws @- flat (stl ws)"
by (cases ws) auto


subsection {* take, drop, nth for streams *}

primrec stake :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a list" where
  "stake 0 s = []"
| "stake (Suc n) s = shd s # stake n (stl s)"

primrec sdrop :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "sdrop 0 s = s"
| "sdrop (Suc n) s = sdrop n (stl s)"

primrec snth :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a" where
  "snth 0 s = shd s"
| "snth (Suc n) s = snth n (stl s)"

lemma stake_sdrop: "stake n s @- sdrop n s = s"
by (induct n arbitrary: s) auto

lemma stake_empty: "stake n s = [] \<longleftrightarrow> n = 0"
by (cases n) auto

lemma sdrop_shift: "\<lbrakk>s = w @- s'; length w = n\<rbrakk> \<Longrightarrow> sdrop n s = s'"
by (induct n arbitrary: w s) auto

lemma stake_shift: "\<lbrakk>s = w @- s'; length w = n\<rbrakk> \<Longrightarrow> stake n s = w"
by (induct n arbitrary: w s) auto

lemma stake_add[simp]: "stake m s @ stake n (sdrop m s) = stake (m + n) s"
by (induct m arbitrary: s) auto

lemma sdrop_add[simp]: "sdrop n (sdrop m s) = sdrop (m + n) s"
by (induct m arbitrary: s) auto

lemma cycle_rotated: "\<lbrakk>v \<noteq> []; cycle u = v @- s\<rbrakk> \<Longrightarrow> cycle (tl u @ [hd u]) = tl v @- s"
by (auto dest: arg_cong[of _ _ stl])

lemma stake_append: "stake n (u @- s) = take (min (length u) n) u @ stake (n - length u) s"
proof (induct n arbitrary: u)
  case (Suc n) thus ?case by (cases u) auto
qed auto

lemma stake_cycle_le[simp]:
  assumes "u \<noteq> []" "n < length u"
  shows "stake n (cycle u) = take n u"
using min_absorb2[OF less_imp_le_nat[OF assms(2)]]
by (subst cycle_decomp[OF assms(1)], subst stake_append) auto

lemma stake_cycle_eq[simp]: "u \<noteq> [] \<Longrightarrow> stake (length u) (cycle u) = u"
by (metis cycle_decomp stake_shift)

lemma sdrop_cycle_eq[simp]: "u \<noteq> [] \<Longrightarrow> sdrop (length u) (cycle u) = cycle u"
by (metis cycle_decomp sdrop_shift)

lemma stake_cycle_eq_mod_0[simp]: "\<lbrakk>u \<noteq> []; n mod length u = 0\<rbrakk> \<Longrightarrow>
   stake n (cycle u) = concat (replicate (n div length u) u)"
by (induct "n div length u" arbitrary: n u) (auto simp: stake_add[symmetric])

lemma sdrop_cycle_eq_mod_0[simp]: "\<lbrakk>u \<noteq> []; n mod length u = 0\<rbrakk> \<Longrightarrow>
   sdrop n (cycle u) = cycle u"
by (induct "n div length u" arbitrary: n u) (auto simp: sdrop_add[symmetric])

lemma stake_cycle: "u \<noteq> [] \<Longrightarrow>
   stake n (cycle u) = concat (replicate (n div length u) u) @ take (n mod length u) u"
by (subst mod_div_equality[of n "length u", symmetric], unfold stake_add[symmetric]) auto

lemma sdrop_cycle: "u \<noteq> [] \<Longrightarrow> sdrop n (cycle u) = cycle (rotate (n mod length u) u)"
by (induct n arbitrary: u) (auto simp: rotate1_rotate_swap rotate1_hd_tl rotate_conv_mod[symmetric])

end
