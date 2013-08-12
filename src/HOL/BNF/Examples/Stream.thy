(*  Title:      HOL/BNF/Examples/Stream.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2012, 2013

Infinite streams.
*)

header {* Infinite Streams *}

theory Stream
imports "../BNF"
begin

codatatype (sset: 'a) stream (map: smap rel: stream_all2) =
  Stream (shd: 'a) (stl: "'a stream") (infixr "##" 65)

declaration {*
  Nitpick_HOL.register_codatatype
    @{typ "'stream_element_type stream"} @{const_name stream_case} [dest_Const @{term Stream}]
    (*FIXME: long type variable name required to reduce the probability of
        a name clash of Nitpick in context. E.g.:
        context
        fixes x :: 'stream_element_type
        begin

        lemma "sset s = {}"
        nitpick
        oops

        end
    *)
*}

code_datatype Stream
lemmas [code] = stream.sels stream.sets stream.case

lemma stream_case_cert:
  assumes "CASE \<equiv> stream_case c"
  shows "CASE (a ## s) \<equiv> c a s"
  using assms by simp_all

setup {*
  Code.add_case @{thm stream_case_cert}
*}

(*for code generation only*)
definition smember :: "'a \<Rightarrow> 'a stream \<Rightarrow> bool" where
  [code_abbrev]: "smember x s \<longleftrightarrow> x \<in> sset s"

lemma smember_code[code, simp]: "smember x (Stream y s) = (if x = y then True else smember x s)"
  unfolding smember_def by auto

hide_const (open) smember

(* TODO: Provide by the package*)
theorem sset_induct:
  "\<lbrakk>\<And>s. P (shd s) s; \<And>s y. \<lbrakk>y \<in> sset (stl s); P y (stl s)\<rbrakk> \<Longrightarrow> P y s\<rbrakk> \<Longrightarrow>
    \<forall>y \<in> sset s. P y s"
  by (rule stream.dtor_set_induct)
    (auto simp add:  shd_def stl_def stream_case_def fsts_def snds_def split_beta)

lemma smap_simps[simp]:
  "shd (smap f s) = f (shd s)" "stl (smap f s) = smap f (stl s)"
  unfolding shd_def stl_def stream_case_def smap_def stream.dtor_unfold
  by (case_tac [!] s) (auto simp: Stream_def stream.dtor_ctor)

declare stream.map[code]

theorem shd_sset: "shd s \<in> sset s"
  sorry
(*
  by (auto simp add: shd_def stl_def stream_case_def fsts_def snds_def split_beta)
    (metis UnCI fsts_def insertI1 stream.dtor_set)
*)

theorem stl_sset: "y \<in> sset (stl s) \<Longrightarrow> y \<in> sset s"
  sorry
(*
  by (auto simp add: shd_def stl_def stream_case_def fsts_def snds_def split_beta)
    (metis insertI1 set_mp snds_def stream.dtor_set_set_incl)
*)

(* only for the non-mutual case: *)
theorem sset_induct1[consumes 1, case_names shd stl, induct set: "sset"]:
  assumes "y \<in> sset s" and "\<And>s. P (shd s) s"
  and "\<And>s y. \<lbrakk>y \<in> sset (stl s); P y (stl s)\<rbrakk> \<Longrightarrow> P y s"
  shows "P y s"
  using assms sset_induct by blast
(* end TODO *)


subsection {* prepend list to stream *}

primrec shift :: "'a list \<Rightarrow> 'a stream \<Rightarrow> 'a stream" (infixr "@-" 65) where
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


subsection {* set of streams with elements in some fixes set *}

coinductive_set
  streams :: "'a set => 'a stream set"
  for A :: "'a set"
where
  Stream[intro!, simp, no_atp]: "\<lbrakk>a \<in> A; s \<in> streams A\<rbrakk> \<Longrightarrow> a ## s \<in> streams A"

lemma shift_streams: "\<lbrakk>w \<in> lists A; s \<in> streams A\<rbrakk> \<Longrightarrow> w @- s \<in> streams A"
  by (induct w) auto

lemma sset_streams:
  assumes "sset s \<subseteq> A"
  shows "s \<in> streams A"
proof (coinduct rule: streams.coinduct[of "\<lambda>s'. \<exists>a s. s' = a ## s \<and> a \<in> A \<and> sset s \<subseteq> A"])
  case streams from assms show ?case by (cases s) auto
next
  fix s' assume "\<exists>a s. s' = a ## s \<and> a \<in> A \<and> sset s \<subseteq> A"
  then guess a s by (elim exE)
  with assms show "\<exists>a l. s' = a ## l \<and>
    a \<in> A \<and> ((\<exists>a s. l = a ## s \<and> a \<in> A \<and> sset s \<subseteq> A) \<or> l \<in> streams A)"
    by (cases s) auto
qed


subsection {* nth, take, drop for streams *}

primrec snth :: "'a stream \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!!" 100) where
  "s !! 0 = shd s"
| "s !! Suc n = stl s !! n"

lemma snth_smap[simp]: "smap f s !! n = f (s !! n)"
  by (induct n arbitrary: s) auto

lemma shift_snth_less[simp]: "p < length xs \<Longrightarrow> (xs @- s) !! p = xs ! p"
  by (induct p arbitrary: xs) (auto simp: hd_conv_nth nth_tl)

lemma shift_snth_ge[simp]: "p \<ge> length xs \<Longrightarrow> (xs @- s) !! p = s !! (p - length xs)"
  by (induct p arbitrary: xs) (auto simp: Suc_diff_eq_diff_pred)

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

primrec stake :: "nat \<Rightarrow> 'a stream \<Rightarrow> 'a list" where
  "stake 0 s = []"
| "stake (Suc n) s = shd s # stake n (stl s)"

lemma length_stake[simp]: "length (stake n s) = n"
  by (induct n arbitrary: s) auto

lemma stake_smap[simp]: "stake n (smap f s) = map f (stake n s)"
  by (induct n arbitrary: s) auto

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

lemma stake_sdrop: "stake n s @- sdrop n s = s"
  by (induct n arbitrary: s) auto

lemma id_stake_snth_sdrop:
  "s = stake i s @- s !! i ## sdrop (Suc i) s"
  by (subst stake_sdrop[symmetric, of _ i]) (metis sdrop_simps stream.collapse)

lemma smap_alt: "smap f s = s' \<longleftrightarrow> (\<forall>n. f (s !! n) = s' !! n)" (is "?L = ?R")
proof
  assume ?R
  thus ?L 
    by (coinduct rule: stream.coinduct[of "\<lambda>s1 s2. \<exists>n. s1 = smap f (sdrop n s) \<and> s2 = sdrop n s'", consumes 0])
      (auto intro: exI[of _ 0] simp del: sdrop.simps(2))
qed auto

lemma stake_invert_Nil[iff]: "stake n s = [] \<longleftrightarrow> n = 0"
  by (induct n) auto

lemma sdrop_shift: "\<lbrakk>s = w @- s'; length w = n\<rbrakk> \<Longrightarrow> sdrop n s = s'"
  by (induct n arbitrary: w s) auto

lemma stake_shift: "\<lbrakk>s = w @- s'; length w = n\<rbrakk> \<Longrightarrow> stake n s = w"
  by (induct n arbitrary: w s) auto

lemma stake_add[simp]: "stake m s @ stake n (sdrop m s) = stake (m + n) s"
  by (induct m arbitrary: s) auto

lemma sdrop_add[simp]: "sdrop n (sdrop m s) = sdrop (m + n) s"
  by (induct m arbitrary: s) auto

partial_function (tailrec) sdrop_while :: "('a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where 
  "sdrop_while P s = (if P (shd s) then sdrop_while P (stl s) else s)"

lemma sdrop_while_Stream[code]:
  "sdrop_while P (Stream a s) = (if P a then sdrop_while P s else Stream a s)"
  by (subst sdrop_while.simps) simp

lemma sdrop_while_sdrop_LEAST:
  assumes "\<exists>n. P (s !! n)"
  shows "sdrop_while (Not o P) s = sdrop (LEAST n. P (s !! n)) s"
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

definition "sfilter P = stream_unfold (shd o sdrop_while (Not o P)) (stl o sdrop_while (Not o P))"

lemma sfilter_Stream: "sfilter P (x ## s) = (if P x then x ## sfilter P s else sfilter P s)"
proof (cases "P x")
  case True thus ?thesis unfolding sfilter_def
    by (subst stream.unfold) (simp add: sdrop_while_Stream)
next
  case False thus ?thesis unfolding sfilter_def
    by (subst (1 2) stream.unfold) (simp add: sdrop_while_Stream)
qed


subsection {* unary predicates lifted to streams *}

definition "stream_all P s = (\<forall>p. P (s !! p))"

lemma stream_all_iff[iff]: "stream_all P s \<longleftrightarrow> Ball (sset s) P"
  unfolding stream_all_def sset_range by auto

lemma stream_all_shift[simp]: "stream_all P (xs @- s) = (list_all P xs \<and> stream_all P s)"
  unfolding stream_all_iff list_all_iff by auto


subsection {* recurring stream out of a list *}

definition cycle :: "'a list \<Rightarrow> 'a stream" where
  "cycle = stream_unfold hd (\<lambda>xs. tl xs @ [hd xs])"

lemma cycle_simps[simp]:
  "shd (cycle u) = hd u"
  "stl (cycle u) = cycle (tl u @ [hd u])"
  by (auto simp: cycle_def)

lemma cycle_decomp: "u \<noteq> [] \<Longrightarrow> cycle u = u @- cycle u"
proof (coinduct rule: stream.coinduct[of "\<lambda>s1 s2. \<exists>u. s1 = cycle u \<and> s2 = u @- cycle u \<and> u \<noteq> []", consumes 0, case_names _ Eq_stream])
  case (Eq_stream s1 s2)
  then obtain u where "s1 = cycle u \<and> s2 = u @- cycle u \<and> u \<noteq> []" by blast
  thus ?case using stream.unfold[of hd "\<lambda>xs. tl xs @ [hd xs]" u] by (auto simp: cycle_def)
qed auto

lemma cycle_Cons[code]: "cycle (x # xs) = x ## cycle (xs @ [x])"
proof (coinduct rule: stream.coinduct[of "\<lambda>s1 s2. \<exists>x xs. s1 = cycle (x # xs) \<and> s2 = x ## cycle (xs @ [x])", consumes 0, case_names _ Eq_stream])
  case (Eq_stream s1 s2)
  then obtain x xs where "s1 = cycle (x # xs) \<and> s2 = x ## cycle (xs @ [x])" by blast
  thus ?case
    by (auto simp: cycle_def intro!: exI[of _ "hd (xs @ [x])"] exI[of _ "tl (xs @ [x])"] stream.unfold)
qed auto

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


subsection {* stream repeating a single element *}

definition "same x = stream_unfold (\<lambda>_. x) id ()"

lemma same_simps[simp]: "shd (same x) = x" "stl (same x) = same x"
  unfolding same_def by auto

lemma same_unfold[code]: "same x = x ## same x"
  by (metis same_simps stream.collapse)

lemma snth_same[simp]: "same x !! n = x"
  unfolding same_def by (induct n) auto

lemma stake_same[simp]: "stake n (same x) = replicate n x"
  unfolding same_def by (induct n) (auto simp: upt_rec)

lemma sdrop_same[simp]: "sdrop n (same x) = same x"
  unfolding same_def by (induct n) auto

lemma shift_replicate_same[simp]: "replicate n x @- same x = same x"
  by (metis sdrop_same stake_same stake_sdrop)

lemma stream_all_same[simp]: "stream_all P (same x) \<longleftrightarrow> P x"
  unfolding stream_all_def by auto

lemma same_cycle: "same x = cycle [x]"
  by (coinduct rule: stream.coinduct[of "\<lambda>s1 s2. s1 = same x \<and> s2 = cycle [x]"]) auto


subsection {* stream of natural numbers *}

definition "fromN n = stream_unfold id Suc n"

lemma fromN_simps[simp]: "shd (fromN n) = n" "stl (fromN n) = fromN (Suc n)"
  unfolding fromN_def by auto

lemma fromN_unfold[code]: "fromN n = n ## fromN (Suc n)"
  unfolding fromN_def by (metis id_def stream.unfold)

lemma snth_fromN[simp]: "fromN n !! m = n + m"
  unfolding fromN_def by (induct m arbitrary: n) auto

lemma stake_fromN[simp]: "stake m (fromN n) = [n ..< m + n]"
  unfolding fromN_def by (induct m arbitrary: n) (auto simp: upt_rec)

lemma sdrop_fromN[simp]: "sdrop m (fromN n) = fromN (n + m)"
  unfolding fromN_def by (induct m arbitrary: n) auto

lemma sset_fromN[simp]: "sset (fromN n) = {n ..}" (is "?L = ?R")
proof safe
  fix m assume "m : ?L"
  moreover
  { fix s assume "m \<in> sset s" "\<exists>n'\<ge>n. s = fromN n'"
    hence "n \<le> m" by (induct arbitrary: n rule: sset_induct1) fastforce+
  }
  ultimately show "n \<le> m" by blast
next
  fix m assume "n \<le> m" thus "m \<in> ?L" by (metis le_iff_add snth_fromN snth_sset)
qed

abbreviation "nats \<equiv> fromN 0"


subsection {* flatten a stream of lists *}

definition flat where
  "flat \<equiv> stream_unfold (hd o shd) (\<lambda>s. if tl (shd s) = [] then stl s else tl (shd s) ## stl s)"

lemma flat_simps[simp]:
  "shd (flat ws) = hd (shd ws)"
  "stl (flat ws) = flat (if tl (shd ws) = [] then stl ws else tl (shd ws) ## stl ws)"
  unfolding flat_def by auto

lemma flat_Cons[simp, code]: "flat ((x # xs) ## ws) = x ## flat (if xs = [] then ws else xs ## ws)"
  unfolding flat_def using stream.unfold[of "hd o shd" _ "(x # xs) ## ws"] by auto

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
  fix x assume ?P "x : ?L"
  then obtain m where "x = flat s !! m" by (metis image_iff sset_range)
  with `?P` obtain n m' where "x = s !! n ! m'" "m' < length (s !! n)"
  proof (atomize_elim, induct m arbitrary: s rule: less_induct)
    case (less y)
    thus ?case
    proof (cases "y < length (shd s)")
      case True thus ?thesis by (metis flat_snth less(2,3) snth.simps(1))
    next
      case False
      hence "x = flat (stl s) !! (y - length (shd s))" by (metis less(2,3) flat_snth)
      moreover
      { from less(2) have "length (shd s) > 0" by (cases s) simp_all
        moreover with False have "y > 0" by (cases y) simp_all
        ultimately have "y - length (shd s) < y" by simp
      }
      moreover have "\<forall>xs \<in> sset (stl s). xs \<noteq> []" using less(2) by (cases s) auto
      ultimately have "\<exists>n m'. x = stl s !! n ! m' \<and> m' < length (stl s !! n)" by (intro less(1)) auto
      thus ?thesis by (metis snth.simps(2))
    qed
  qed
  thus "x \<in> ?R" by (auto simp: sset_range dest!: nth_mem)
next
  fix x xs assume "xs \<in> sset s" ?P "x \<in> set xs" thus "x \<in> ?L"
    by (induct rule: sset_induct1)
      (metis UnI1 flat_unfold shift.simps(1) sset_shift,
       metis UnI2 flat_unfold shd_sset stl_sset sset_shift)
qed


subsection {* merge a stream of streams *}

definition smerge :: "'a stream stream \<Rightarrow> 'a stream" where
  "smerge ss = flat (smap (\<lambda>n. map (\<lambda>s. s !! n) (stake (Suc n) ss) @ stake n (ss !! n)) nats)"

lemma stake_nth[simp]: "m < n \<Longrightarrow> stake n s ! m = s !! m"
  by (induct n arbitrary: s m) (auto simp: nth_Cons', metis Suc_pred snth.simps(2))

lemma snth_sset_smerge: "ss !! n !! m \<in> sset (smerge ss)"
proof (cases "n \<le> m")
  case False thus ?thesis unfolding smerge_def
    by (subst sset_flat)
      (auto simp: stream.set_map' in_set_conv_nth simp del: stake.simps
        intro!: exI[of _ n, OF disjI2] exI[of _ m, OF mp])
next
  case True thus ?thesis unfolding smerge_def
    by (subst sset_flat)
      (auto simp: stream.set_map' in_set_conv_nth image_iff simp del: stake.simps snth.simps
        intro!: exI[of _ m, OF disjI1] bexI[of _ "ss !! n"] exI[of _ n, OF mp])
qed

lemma sset_smerge: "sset (smerge ss) = UNION (sset ss) sset"
proof safe
  fix x assume "x \<in> sset (smerge ss)"
  thus "x \<in> UNION (sset ss) sset"
    unfolding smerge_def by (subst (asm) sset_flat)
      (auto simp: stream.set_map' in_set_conv_nth sset_range simp del: stake.simps, fast+)
next
  fix s x assume "s \<in> sset ss" "x \<in> sset s"
  thus "x \<in> sset (smerge ss)" using snth_sset_smerge by (auto simp: sset_range)
qed


subsection {* product of two streams *}

definition sproduct :: "'a stream \<Rightarrow> 'b stream \<Rightarrow> ('a \<times> 'b) stream" where
  "sproduct s1 s2 = smerge (smap (\<lambda>x. smap (Pair x) s2) s1)"

lemma sset_sproduct: "sset (sproduct s1 s2) = sset s1 \<times> sset s2"
  unfolding sproduct_def sset_smerge by (auto simp: stream.set_map')


subsection {* interleave two streams *}

definition sinterleave :: "'a stream \<Rightarrow> 'a stream \<Rightarrow> 'a stream" where
  [code del]: "sinterleave s1 s2 =
    stream_unfold (\<lambda>(s1, s2). shd s1) (\<lambda>(s1, s2). (s2, stl s1)) (s1, s2)"

lemma sinterleave_simps[simp]:
  "shd (sinterleave s1 s2) = shd s1" "stl (sinterleave s1 s2) = sinterleave s2 (stl s1)"
  unfolding sinterleave_def by auto

lemma sinterleave_code[code]:
  "sinterleave (x ## s1) s2 = x ## sinterleave s2 s1"
  by (metis sinterleave_simps stream.exhaust stream.sels)

lemma sinterleave_snth[simp]:
  "even n \<Longrightarrow> sinterleave s1 s2 !! n = s1 !! (n div 2)"
   "odd n \<Longrightarrow> sinterleave s1 s2 !! n = s2 !! (n div 2)"
  by (induct n arbitrary: s1 s2)
    (auto dest: even_nat_Suc_div_2 odd_nat_plus_one_div_two[folded nat_2])

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


subsection {* zip *}

definition "szip s1 s2 =
  stream_unfold (map_pair shd shd) (map_pair stl stl) (s1, s2)"

lemma szip_simps[simp]:
  "shd (szip s1 s2) = (shd s1, shd s2)" "stl (szip s1 s2) = szip (stl s1) (stl s2)"
  unfolding szip_def by auto

lemma szip_unfold[code]: "szip (Stream a s1) (Stream b s2) = Stream (a, b) (szip s1 s2)"
  unfolding szip_def by (subst stream.unfold) simp

lemma snth_szip[simp]: "szip s1 s2 !! n = (s1 !! n, s2 !! n)"
  by (induct n arbitrary: s1 s2) auto


subsection {* zip via function *}

definition "smap2 f s1 s2 =
  stream_unfold (\<lambda>(s1,s2). f (shd s1) (shd s2)) (map_pair stl stl) (s1, s2)"

lemma smap2_simps[simp]:
  "shd (smap2 f s1 s2) = f (shd s1) (shd s2)"
  "stl (smap2 f s1 s2) = smap2 f (stl s1) (stl s2)"
  unfolding smap2_def by auto

lemma smap2_unfold[code]:
  "smap2 f (Stream a s1) (Stream b s2) = Stream (f a b) (smap2 f s1 s2)"
  unfolding smap2_def by (subst stream.unfold) simp

lemma smap2_szip:
  "smap2 f s1 s2 = smap (split f) (szip s1 s2)"
  by (coinduct rule: stream.coinduct[of
    "\<lambda>s1 s2. \<exists>s1' s2'. s1 = smap2 f s1' s2' \<and> s2 = smap (split f) (szip s1' s2')"])
    fastforce+


subsection {* iterated application of a function *}

definition siterate :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'a stream" where
  "siterate f x = x ## stream_unfold f f x"

lemma siterate_simps[simp]: "shd (siterate f x) = x" "stl (siterate f x) = siterate f (f x)"
  unfolding siterate_def by (auto intro: stream.unfold)

lemma siterate_code[code]: "siterate f x = x ## siterate f (f x)"
  by (metis siterate_def stream.unfold)

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

end
