(*  Title:      HOL/Library/Stream.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012, 2013

Infinite streams.
*)

section \<open>Infinite Streams\<close>

theory Stream
  imports Nat_Bijection
begin

codatatype (sset: 'a) stream =
  SCons (shd: 'a) (stl: "'a stream") (infixr \<open>##\<close> 65)
for
  map: smap
  rel: stream_all2

context
begin

\<comment> \<open>for code generation only\<close>
qualified definition smember :: "'a \<Rightarrow> 'a stream \<Rightarrow> bool" where
  [code_abbrev]: "smember x s \<longleftrightarrow> x \<in> sset s"

lemma smember_code[code, simp]: "smember x (y ## s) = (if x = y then True else smember x s)"
  unfolding smember_def by auto

end

lemmas smap_simps[simp] = stream.map_sel
lemmas shd_sset = stream.set_sel(1)
lemmas stl_sset = stream.set_sel(2)

theorem sset_induct[consumes 1, case_names shd stl, induct set: sset]:
  assumes "y \<in> sset s" and "\<And>s. P (shd s) s" and "\<And>s y. \<lbrakk>y \<in> sset (stl s); P y (stl s)\<rbrakk> \<Longrightarrow> P y s"
  shows "P y s"
using assms by induct (metis stream.sel(1), auto)

lemma smap_ctr: "smap f s = x ## s' \<longleftrightarrow> f (shd s) = x \<and> smap f (stl s) = s'"
  by (cases s) simp

subsection \<open>prepend list to stream\<close>

primrec shift :: "'a list \<Rightarrow> 'a stream \<Rightarrow> 'a stream" (infixr \<open>@-\<close> 65) where
  "shift [] s = s"
| "shift (x # xs) s = x ## shift xs s"

lemma smap_shift[simp]: "smap f (xs @- s) = map f xs @- smap f s"
  by (induct xs) auto

lemma shift_append[simp]: "(xs @ ys) @- s = xs @- ys @- s"
  by (induct xs) auto

lemma shift_simps[simp]:
   "shd (xs @- s) = (if xs = [] then shd s else hd xs)"
   "stl (xs @- s) = (if xs = [] then stl s else tl xs @- s)"
  by (induct xs) auto

lemma sset_shift[simp]: "sset (xs @- s) = set xs \<union> sset s"
  by (induct xs) auto

lemma shift_left_inj[simp]: "xs @- s1 = xs @- s2 \<longleftrightarrow> s1 = s2"
  by (induct xs) auto


subsection \<open>set of streams with elements in some fixed set\<close>

context
  notes [[inductive_internals]]
begin

coinductive_set
  streams :: "'a set \<Rightarrow> 'a stream set"
  for A :: "'a set"
where
  Stream[intro!, simp, no_atp]: "\<lbrakk>a \<in> A; s \<in> streams A\<rbrakk> \<Longrightarrow> a ## s \<in> streams A"

end

lemma in_streams: "stl s \<in> streams S \<Longrightarrow> shd s \<in> S \<Longrightarrow> s \<in> streams S"
  by (cases s) auto

lemma streamsE: "s \<in> streams A \<Longrightarrow> (shd s \<in> A \<Longrightarrow> stl s \<in> streams A \<Longrightarrow> P) \<Longrightarrow> P"
  by (erule streams.cases) simp_all

lemma Stream_image: "x ## y \<in> ((##) x') ` Y \<longleftrightarrow> x = x' \<and> y \<in> Y"
  by auto

lemma shift_streams: "\<lbrakk>w \<in> lists A; s \<in> streams A\<rbrakk> \<Longrightarrow> w @- s \<in> streams A"
  by (induct w) auto

lemma streams_Stream: "x ## s \<in> streams A \<longleftrightarrow> x \<in> A \<and> s \<in> streams A"
  by (auto elim: streams.cases)

lemma streams_stl: "s \<in> streams A \<Longrightarrow> stl s \<in> streams A"
  by (cases s) (auto simp: streams_Stream)

lemma streams_shd: "s \<in> streams A \<Longrightarrow> shd s \<in> A"
  by (cases s) (auto simp: streams_Stream)

lemma sset_streams:
  assumes "sset s \<subseteq> A"
  shows "s \<in> streams A"
using assms proof (coinduction arbitrary: s)
  case streams then show ?case by (cases s) simp
qed

lemma streams_sset:
  assumes "s \<in> streams A"
  shows "sset s \<subseteq> A"
proof
  fix x assume "x \<in> sset s" from this \<open>s \<in> streams A\<close> show "x \<in> A"
    by (induct s) (auto intro: streams_shd streams_stl)
qed

lemma streams_iff_sset: "s \<in> streams A \<longleftrightarrow> sset s \<subseteq> A"
  by (metis sset_streams streams_sset)

lemma streams_mono:  "s \<in> streams A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> s \<in> streams B"
  unfolding streams_iff_sset by auto

lemma streams_mono2: "S \<subseteq> T \<Longrightarrow> streams S \<subseteq> streams T"
  by (auto intro: streams_mono)

lemma smap_streams: "s \<in> streams A \<Longrightarrow> (\<And>x. x \<in> A \<Longrightarrow> f x \<in> B) \<Longrightarrow> smap f s \<in> streams B"
  unfolding streams_iff_sset stream.set_map by auto

lemma streams_empty: "streams {} = {}"
  by (auto elim: streams.cases)

lemma streams_UNIV[simp]: "streams UNIV = UNIV"
  by (auto simp: streams_iff_sset)

subsection \<open>nth, take, drop for streams\<close>

primrec snth :: "'a stream \<Rightarrow> nat \<Rightarrow> 'a" (infixl \<open>!!\<close> 100) where
  "s !! 0 = shd s"
| "s !! Suc n = stl s !! n"

lemma snth_Stream: "(x ## s) !! Suc i = s !! i"
  by simp

lemma snth_smap[simp]: "smap f s !! n = f (s !! n)"
  by (induct n arbitrary: s) auto

lemma shift_snth_less[simp]: "p < length xs \<Longrightarrow> (xs @- s) !! p = xs ! p"
  by (induct p arbitrary: xs) (auto simp: hd_conv_nth nth_tl)

lemma shift_snth_ge[simp]: "p \<ge> length xs \<Longrightarrow> (xs @- s) !! p = s !! (p - length xs)"
  by (induct p arbitrary: xs) (auto simp: Suc_diff_eq_diff_pred)

lemma shift_snth: "(xs @- s) !! n = (if n < length xs then xs ! n else s !! (n - length xs))"
  by auto

lemma snth_sset[simp]: "s !! n \<in> sset s"
  by (induct n arbitrary: s) (auto intro: shd_sset stl_sset)

lemma sset_range: "sset s = range (snth s)"
proof (intro equalityI subsetI)
  fix x assume "x \<in> sset s"
  thus "x \<in> range (snth s)"
  proof (induct s)
    case (stl s x)
    then obtain n where "x = stl s !! n" by auto
    thus ?case by (auto intro: range_eqI[of _ _ "Suc n"])
  qed (auto intro: range_eqI[of _ _ 0])
qed auto

lemma streams_iff_snth: "s \<in> streams X \<longleftrightarrow> (\<forall>n. s !! n \<in> X)"
  by (force simp: streams_iff_sset sset_range)

lemma snth_in: "s \<in> streams X \<Longrightarrow> s !! n \<in> X"
  by (simp add: streams_iff_snth)

primrec stake :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a list" where
  "stake 0 s = []"
| "stake (Suc n) s = shd s # stake n (stl s)"

lemma length_stake[simp]: "length (stake n s) = n"
  by (induct n arbitrary: s) auto

lemma stake_smap[simp]: "stake n (smap f s) = map f (stake n s)"
  by (induct n arbitrary: s) auto

lemma take_stake: "take n (stake m s) = stake (min n m) s"
proof (induct m arbitrary: s n)
  case (Suc m) thus ?case by (cases n) auto
qed simp

primrec sdrop :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "sdrop 0 s = s"
| "sdrop (Suc n) s = sdrop n (stl s)"

lemma sdrop_simps[simp]:
  "shd (sdrop n s) = s !! n" "stl (sdrop n s) = sdrop (Suc n) s"
  by (induct n arbitrary: s)  auto

lemma sdrop_smap[simp]: "sdrop n (smap f s) = smap f (sdrop n s)"
  by (induct n arbitrary: s) auto

lemma sdrop_stl: "sdrop n (stl s) = stl (sdrop n s)"
  by (induct n) auto

lemma drop_stake: "drop n (stake m s) = stake (m - n) (sdrop n s)"
proof (induct m arbitrary: s n)
  case (Suc m) thus ?case by (cases n) auto
qed simp

lemma stake_sdrop: "stake n s @- sdrop n s = s"
  by (induct n arbitrary: s) auto

lemma id_stake_snth_sdrop:
  "s = stake i s @- s !! i ## sdrop (Suc i) s"
  by (subst stake_sdrop[symmetric, of _ i]) (metis sdrop_simps stream.collapse)

lemma smap_alt: "smap f s = s' \<longleftrightarrow> (\<forall>n. f (s !! n) = s' !! n)" (is "?L = ?R")
proof
  assume ?R
  then have "\<And>n. smap f (sdrop n s) = sdrop n s'"
    by coinduction (auto intro: exI[of _ 0] simp del: sdrop.simps(2))
  then show ?L using sdrop.simps(1) by metis
qed auto

lemma stake_invert_Nil[iff]: "stake n s = [] \<longleftrightarrow> n = 0"
  by (induct n) auto

lemma sdrop_shift: "sdrop i (w @- s) = drop i w @- sdrop (i - length w) s"
  by (induct i arbitrary: w s) (auto simp: drop_tl drop_Suc neq_Nil_conv)

lemma stake_shift: "stake i (w @- s) = take i w @ stake (i - length w) s"
  by (induct i arbitrary: w s) (auto simp: neq_Nil_conv)

lemma stake_add[simp]: "stake m s @ stake n (sdrop m s) = stake (m + n) s"
  by (induct m arbitrary: s) auto

lemma sdrop_add[simp]: "sdrop n (sdrop m s) = sdrop (m + n) s"
  by (induct m arbitrary: s) auto

lemma sdrop_snth: "sdrop n s !! m = s !! (n + m)"
  by (induct n arbitrary: m s) auto

partial_function (tailrec) sdrop_while :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  "sdrop_while P s = (if P (shd s) then sdrop_while P (stl s) else s)"

lemma sdrop_while_SCons[code]:
  "sdrop_while P (a ## s) = (if P a then sdrop_while P s else a ## s)"
  by (subst sdrop_while.simps) simp

lemma sdrop_while_sdrop_LEAST:
  assumes "\<exists>n. P (s !! n)"
  shows "sdrop_while (Not \<circ> P) s = sdrop (LEAST n. P (s !! n)) s"
proof -
  from assms obtain m where "P (s !! m)" "\<And>n. P (s !! n) \<Longrightarrow> m \<le> n"
    and *: "(LEAST n. P (s !! n)) = m" by atomize_elim (auto intro: LeastI Least_le)
  thus ?thesis unfolding *
  proof (induct m arbitrary: s)
    case (Suc m)
    hence "sdrop_while (Not \<circ> P) (stl s) = sdrop m (stl s)"
      by (metis (full_types) not_less_eq_eq snth.simps(2))
    moreover from Suc(3) have "\<not> (P (s !! 0))" by blast
    ultimately show ?case by (subst sdrop_while.simps) simp
  qed (metis comp_apply sdrop.simps(1) sdrop_while.simps snth.simps(1))
qed

primcorec sfilter where
  "shd (sfilter P s) = shd (sdrop_while (Not \<circ> P) s)"
| "stl (sfilter P s) = sfilter P (stl (sdrop_while (Not \<circ> P) s))"

lemma sfilter_Stream: "sfilter P (x ## s) = (if P x then x ## sfilter P s else sfilter P s)"
proof (cases "P x")
  case True thus ?thesis by (subst sfilter.ctr) (simp add: sdrop_while_SCons)
next
  case False thus ?thesis by (subst (1 2) sfilter.ctr) (simp add: sdrop_while_SCons)
qed


subsection \<open>unary predicates lifted to streams\<close>

definition "stream_all P s = (\<forall>p. P (s !! p))"

lemma stream_all_iff[iff]: "stream_all P s \<longleftrightarrow> Ball (sset s) P"
  unfolding stream_all_def sset_range by auto

lemma stream_all_shift[simp]: "stream_all P (xs @- s) = (list_all P xs \<and> stream_all P s)"
  unfolding stream_all_iff list_all_iff by auto

lemma stream_all_Stream: "stream_all P (x ## X) \<longleftrightarrow> P x \<and> stream_all P X"
  by simp


subsection \<open>recurring stream out of a list\<close>

primcorec cycle :: "'a list \<Rightarrow> 'a stream" where
  "shd (cycle xs) = hd xs"
| "stl (cycle xs) = cycle (tl xs @ [hd xs])"

lemma cycle_decomp: "u \<noteq> [] \<Longrightarrow> cycle u = u @- cycle u"
proof (coinduction arbitrary: u)
  case Eq_stream then show ?case using stream.collapse[of "cycle u"]
    by (auto intro!: exI[of _ "tl u @ [hd u]"])
qed

lemma cycle_Cons[code]: "cycle (x # xs) = x ## cycle (xs @ [x])"
  by (subst cycle.ctr) simp

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
  by (subst cycle_decomp) (auto simp: stake_shift)

lemma sdrop_cycle_eq[simp]: "u \<noteq> [] \<Longrightarrow> sdrop (length u) (cycle u) = cycle u"
  by (subst cycle_decomp) (auto simp: sdrop_shift)

lemma stake_cycle_eq_mod_0[simp]: "\<lbrakk>u \<noteq> []; n mod length u = 0\<rbrakk> \<Longrightarrow>
   stake n (cycle u) = concat (replicate (n div length u) u)"
  by (induct "n div length u" arbitrary: n u)
    (auto simp: stake_add [symmetric] mod_eq_0_iff_dvd elim!: dvdE)

lemma sdrop_cycle_eq_mod_0[simp]: "\<lbrakk>u \<noteq> []; n mod length u = 0\<rbrakk> \<Longrightarrow>
   sdrop n (cycle u) = cycle u"
  by (induct "n div length u" arbitrary: n u)
    (auto simp: sdrop_add [symmetric] mod_eq_0_iff_dvd elim!: dvdE)

lemma stake_cycle: "u \<noteq> [] \<Longrightarrow>
   stake n (cycle u) = concat (replicate (n div length u) u) @ take (n mod length u) u"
  by (subst div_mult_mod_eq[of n "length u", symmetric], unfold stake_add[symmetric]) auto

lemma sdrop_cycle: "u \<noteq> [] \<Longrightarrow> sdrop n (cycle u) = cycle (rotate (n mod length u) u)"
  by (induct n arbitrary: u) (auto simp: rotate1_rotate_swap rotate1_hd_tl rotate_conv_mod[symmetric])

lemma sset_cycle[simp]:
  assumes "xs \<noteq> []"
  shows "sset (cycle xs) = set xs"
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> sset (cycle xs)"
  then show "x \<in> set xs" using assms
    by (induction "cycle xs" arbitrary: xs rule: sset_induct) (fastforce simp: neq_Nil_conv)+
qed (metis assms UnI1 cycle_decomp sset_shift)


subsection \<open>iterated application of a function\<close>

primcorec siterate where
  "shd (siterate f x) = x"
| "stl (siterate f x) = siterate f (f x)"

lemma stake_Suc: "stake (Suc n) s = stake n s @ [s !! n]"
  by (induct n arbitrary: s) auto

lemma snth_siterate[simp]: "siterate f x !! n = (f^^n) x"
  by (induct n arbitrary: x) (auto simp: funpow_swap1)

lemma sdrop_siterate[simp]: "sdrop n (siterate f x) = siterate f ((f^^n) x)"
  by (induct n arbitrary: x) (auto simp: funpow_swap1)

lemma stake_siterate[simp]: "stake n (siterate f x) = map (\<lambda>n. (f^^n) x) [0 ..< n]"
  by (induct n arbitrary: x) (auto simp del: stake.simps(2) simp: stake_Suc)

lemma sset_siterate: "sset (siterate f x) = {(f^^n) x | n. True}"
  by (auto simp: sset_range)

lemma smap_siterate: "smap f (siterate f x) = siterate f (f x)"
  by (coinduction arbitrary: x) auto


subsection \<open>stream repeating a single element\<close>

abbreviation "sconst \<equiv> siterate id"

lemma shift_replicate_sconst[simp]: "replicate n x @- sconst x = sconst x"
  by (subst (3) stake_sdrop[symmetric]) (simp add: map_replicate_trivial)

lemma sset_sconst[simp]: "sset (sconst x) = {x}"
  by (simp add: sset_siterate)

lemma sconst_alt: "s = sconst x \<longleftrightarrow> sset s = {x}"
proof
  assume "sset s = {x}"
  then show "s = sconst x"
  proof (coinduction arbitrary: s)
    case Eq_stream
    then have "shd s = x" "sset (stl s) \<subseteq> {x}" by (cases s; auto)+
    then have "sset (stl s) = {x}" by (cases "stl s") auto
    with \<open>shd s = x\<close> show ?case by auto
  qed
qed simp

lemma sconst_cycle: "sconst x = cycle [x]"
  by coinduction auto

lemma smap_sconst: "smap f (sconst x) = sconst (f x)"
  by coinduction auto

lemma sconst_streams: "x \<in> A \<Longrightarrow> sconst x \<in> streams A"
  by (simp add: streams_iff_sset)

lemma streams_empty_iff: "streams S = {} \<longleftrightarrow> S = {}"
proof safe
  fix x assume "x \<in> S" "streams S = {}"
  then have "sconst x \<in> streams S"
    by (intro sconst_streams)
  then show "x \<in> {}"
    unfolding \<open>streams S = {}\<close> by simp
qed (auto simp: streams_empty)

subsection \<open>stream of natural numbers\<close>

abbreviation "fromN \<equiv> siterate Suc"

abbreviation "nats \<equiv> fromN 0"

lemma sset_fromN[simp]: "sset (fromN n) = {n ..}"
  by (auto simp add: sset_siterate le_iff_add)

lemma stream_smap_fromN: "s = smap (\<lambda>j. let i = j - n in s !! i) (fromN n)"
  by (coinduction arbitrary: s n)
    (force simp: neq_Nil_conv Let_def Suc_diff_Suc simp flip: snth.simps(2)
      intro: stream.map_cong split: if_splits)

lemma stream_smap_nats: "s = smap (snth s) nats"
  using stream_smap_fromN[where n = 0] by simp


subsection \<open>flatten a stream of lists\<close>

primcorec flat where
  "shd (flat ws) = hd (shd ws)"
| "stl (flat ws) = flat (if tl (shd ws) = [] then stl ws else tl (shd ws) ## stl ws)"

lemma flat_Cons[simp, code]: "flat ((x # xs) ## ws) = x ## flat (if xs = [] then ws else xs ## ws)"
  by (subst flat.ctr) simp

lemma flat_Stream[simp]: "xs \<noteq> [] \<Longrightarrow> flat (xs ## ws) = xs @- flat ws"
  by (induct xs) auto

lemma flat_unfold: "shd ws \<noteq> [] \<Longrightarrow> flat ws = shd ws @- flat (stl ws)"
  by (cases ws) auto

lemma flat_snth: "\<forall>xs \<in> sset s. xs \<noteq> [] \<Longrightarrow> flat s !! n = (if n < length (shd s) then
  shd s ! n else flat (stl s) !! (n - length (shd s)))"
  by (metis flat_unfold not_less shd_sset shift_snth_ge shift_snth_less)

lemma sset_flat[simp]: "\<forall>xs \<in> sset s. xs \<noteq> [] \<Longrightarrow>
  sset (flat s) = (\<Union>xs \<in> sset s. set xs)" (is "?P \<Longrightarrow> ?L = ?R")
proof safe
  fix x assume ?P "x \<in> ?L"
  then obtain m where "x = flat s !! m" by (metis image_iff sset_range)
  with \<open>?P\<close> obtain n m' where "x = s !! n ! m'" "m' < length (s !! n)"
  proof (atomize_elim, induct m arbitrary: s rule: less_induct)
    case (less y)
    thus ?case
    proof (cases "y < length (shd s)")
      case True thus ?thesis by (metis flat_snth less(2,3) snth.simps(1))
    next
      case False
      hence "x = flat (stl s) !! (y - length (shd s))" by (metis less(2,3) flat_snth)
      moreover have "y - length (shd s) < y"
      proof -
        from less(2) have *: "length (shd s) > 0" by (cases s) simp_all
        with False have "y > 0" by (cases y) simp_all
        with * show ?thesis by simp
      qed
      moreover have "\<forall>xs \<in> sset (stl s). xs \<noteq> []" using less(2) by (cases s) auto
      ultimately have "\<exists>n m'. x = stl s !! n ! m' \<and> m' < length (stl s !! n)" by (intro less(1)) auto
      thus ?thesis by (metis snth.simps(2))
    qed
  qed
  thus "x \<in> ?R" by (auto simp: sset_range dest!: nth_mem)
next
  fix x xs
  assume "xs \<in> sset s" ?P "x \<in> set xs"
  thus "x \<in> ?L"
    by (induct rule: sset_induct)
      (metis UnI1 flat_unfold shift.simps(1) sset_shift,
       metis UnI2 flat_unfold shd_sset stl_sset sset_shift)
qed


subsection \<open>merge a stream of streams\<close>

definition smerge :: "'a stream stream \<Rightarrow> 'a stream" where
  "smerge ss = flat (smap (\<lambda>n. map (\<lambda>s. s !! n) (stake (Suc n) ss) @ stake n (ss !! n)) nats)"

lemma stake_nth[simp]: "m < n \<Longrightarrow> stake n s ! m = s !! m"
  by (induct n arbitrary: s m) (auto simp: nth_Cons', metis Suc_pred snth.simps(2))

lemma snth_sset_smerge: "ss !! n !! m \<in> sset (smerge ss)"
proof (cases "n \<le> m")
  case False thus ?thesis unfolding smerge_def
    by (subst sset_flat)
      (auto simp: stream.set_map in_set_conv_nth simp del: stake.simps
        intro!: exI[of _ n, OF disjI2] exI[of _ m, OF mp])
next
  case True thus ?thesis unfolding smerge_def
    by (subst sset_flat)
      (auto simp: stream.set_map in_set_conv_nth image_iff simp del: stake.simps snth.simps
        intro!: exI[of _ m, OF disjI1] bexI[of _ "ss !! n"] exI[of _ n, OF mp])
qed

lemma sset_smerge: "sset (smerge ss) = \<Union>(sset ` (sset ss))"
proof safe
  fix x assume "x \<in> sset (smerge ss)"
  thus "x \<in> \<Union>(sset ` (sset ss))"
    unfolding smerge_def by (subst (asm) sset_flat)
      (auto simp: stream.set_map in_set_conv_nth sset_range simp del: stake.simps, fast+)
next
  fix s x assume "s \<in> sset ss" "x \<in> sset s"
  thus "x \<in> sset (smerge ss)" using snth_sset_smerge by (auto simp: sset_range)
qed


subsection \<open>product of two streams\<close>

definition sproduct :: "'a stream \<Rightarrow> 'b stream \<Rightarrow> ('a \<times> 'b) stream" where
  "sproduct s1 s2 = smerge (smap (\<lambda>x. smap (Pair x) s2) s1)"

lemma sset_sproduct: "sset (sproduct s1 s2) = sset s1 \<times> sset s2"
  unfolding sproduct_def sset_smerge by (auto simp: stream.set_map)


subsection \<open>interleave two streams\<close>

primcorec sinterleave where
  "shd (sinterleave s1 s2) = shd s1"
| "stl (sinterleave s1 s2) = sinterleave s2 (stl s1)"

lemma sinterleave_code[code]:
  "sinterleave (x ## s1) s2 = x ## sinterleave s2 s1"
  by (subst sinterleave.ctr) simp

lemma sinterleave_snth[simp]:
  "even n \<Longrightarrow> sinterleave s1 s2 !! n = s1 !! (n div 2)"
  "odd n \<Longrightarrow> sinterleave s1 s2 !! n = s2 !! (n div 2)"
  by (induct n arbitrary: s1 s2) simp_all

lemma sset_sinterleave: "sset (sinterleave s1 s2) = sset s1 \<union> sset s2"
proof (intro equalityI subsetI)
  fix x assume "x \<in> sset (sinterleave s1 s2)"
  then obtain n where "x = sinterleave s1 s2 !! n" unfolding sset_range by blast
  thus "x \<in> sset s1 \<union> sset s2" by (cases "even n") auto
next
  fix x assume "x \<in> sset s1 \<union> sset s2"
  thus "x \<in> sset (sinterleave s1 s2)"
  proof
    assume "x \<in> sset s1"
    then obtain n where "x = s1 !! n" unfolding sset_range by blast
    hence "sinterleave s1 s2 !! (2 * n) = x" by simp
    thus ?thesis unfolding sset_range by blast
  next
    assume "x \<in> sset s2"
    then obtain n where "x = s2 !! n" unfolding sset_range by blast
    hence "sinterleave s1 s2 !! (2 * n + 1) = x" by simp
    thus ?thesis unfolding sset_range by blast
  qed
qed


subsection \<open>zip\<close>

primcorec szip where
  "shd (szip s1 s2) = (shd s1, shd s2)"
| "stl (szip s1 s2) = szip (stl s1) (stl s2)"

lemma szip_unfold[code]: "szip (a ## s1) (b ## s2) = (a, b) ## (szip s1 s2)"
  by (subst szip.ctr) simp

lemma snth_szip[simp]: "szip s1 s2 !! n = (s1 !! n, s2 !! n)"
  by (induct n arbitrary: s1 s2) auto

lemma stake_szip[simp]:
  "stake n (szip s1 s2) = zip (stake n s1) (stake n s2)"
  by (induct n arbitrary: s1 s2) auto

lemma sdrop_szip[simp]: "sdrop n (szip s1 s2) = szip (sdrop n s1) (sdrop n s2)"
  by (induct n arbitrary: s1 s2) auto

lemma smap_szip_fst:
  "smap (\<lambda>x. f (fst x)) (szip s1 s2) = smap f s1"
  by (coinduction arbitrary: s1 s2) auto

lemma smap_szip_snd:
  "smap (\<lambda>x. g (snd x)) (szip s1 s2) = smap g s2"
  by (coinduction arbitrary: s1 s2) auto


subsection \<open>zip via function\<close>

primcorec smap2 where
  "shd (smap2 f s1 s2) = f (shd s1) (shd s2)"
| "stl (smap2 f s1 s2) = smap2 f (stl s1) (stl s2)"

lemma smap2_unfold[code]:
  "smap2 f (a ## s1) (b ## s2) = f a b ## (smap2 f s1 s2)"
  by (subst smap2.ctr) simp

lemma smap2_szip:
  "smap2 f s1 s2 = smap (case_prod f) (szip s1 s2)"
  by (coinduction arbitrary: s1 s2) auto

lemma smap_smap2[simp]:
  "smap f (smap2 g s1 s2) = smap2 (\<lambda>x y. f (g x y)) s1 s2"
  unfolding smap2_szip stream.map_comp o_def split_def ..

lemma smap2_alt:
  "(smap2 f s1 s2 = s) = (\<forall>n. f (s1 !! n) (s2 !! n) = s !! n)"
  unfolding smap2_szip smap_alt by auto

lemma snth_smap2[simp]:
  "smap2 f s1 s2 !! n = f (s1 !! n) (s2 !! n)"
  by (induct n arbitrary: s1 s2) auto

lemma stake_smap2[simp]:
  "stake n (smap2 f s1 s2) = map (case_prod f) (zip (stake n s1) (stake n s2))"
  by (induct n arbitrary: s1 s2) auto

lemma sdrop_smap2[simp]:
  "sdrop n (smap2 f s1 s2) = smap2 f (sdrop n s1) (sdrop n s2)"
  by (induct n arbitrary: s1 s2) auto

end
