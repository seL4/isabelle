(*  Title:      HOL/Library/Linear_Temporal_Logic_on_Streams.thy
    Author:     Andrei Popescu, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen
*)

section {* Linear Temporal Logic on Streams *}

theory Linear_Temporal_Logic_on_Streams
  imports Stream Sublist
begin

section{* Preliminaries *}

lemma shift_prefix:
assumes "xl @- xs = yl @- ys" and "length xl \<le> length yl"
shows "prefixeq xl yl"
using assms proof(induct xl arbitrary: yl xs ys)
  case (Cons x xl yl xs ys)
  thus ?case by (cases yl) auto
qed auto

lemma shift_prefix_cases:
assumes "xl @- xs = yl @- ys"
shows "prefixeq xl yl \<or> prefixeq yl xl"
using shift_prefix[OF assms] apply(cases "length xl \<le> length yl")
by (metis, metis assms nat_le_linear shift_prefix)


section{* Linear temporal logic *}

(* Propositional connectives: *)
abbreviation (input) IMPL (infix "impl" 60)
where "\<phi> impl \<psi> \<equiv> \<lambda> xs. \<phi> xs \<longrightarrow> \<psi> xs"

abbreviation (input) OR (infix "or" 60)
where "\<phi> or \<psi> \<equiv> \<lambda> xs. \<phi> xs \<or> \<psi> xs"

abbreviation (input) AND (infix "aand" 60)
where "\<phi> aand \<psi> \<equiv> \<lambda> xs. \<phi> xs \<and> \<psi> xs"

abbreviation (input) "not \<phi> \<equiv> \<lambda> xs. \<not> \<phi> xs"

abbreviation (input) "true \<equiv> \<lambda> xs. True"

abbreviation (input) "false \<equiv> \<lambda> xs. False"

lemma impl_not_or: "\<phi> impl \<psi> = (not \<phi>) or \<psi>"
by blast

lemma not_or: "not (\<phi> or \<psi>) = (not \<phi>) aand (not \<psi>)"
by blast

lemma not_aand: "not (\<phi> aand \<psi>) = (not \<phi>) or (not \<psi>)"
by blast

lemma non_not[simp]: "not (not \<phi>) = \<phi>" by simp

(* Temporal (LTL) connectives: *)
fun holds where "holds P xs \<longleftrightarrow> P (shd xs)"
fun nxt where "nxt \<phi> xs = \<phi> (stl xs)"

inductive ev for \<phi> where
base: "\<phi> xs \<Longrightarrow> ev \<phi> xs"
|
step: "ev \<phi> (stl xs) \<Longrightarrow> ev \<phi> xs"

coinductive alw for \<phi> where
alw: "\<lbrakk>\<phi> xs; alw \<phi> (stl xs)\<rbrakk> \<Longrightarrow> alw \<phi> xs"

(* weak until: *)
coinductive UNTIL (infix "until" 60) for \<phi> \<psi> where
base: "\<psi> xs \<Longrightarrow> (\<phi> until \<psi>) xs"
|
step: "\<lbrakk>\<phi> xs; (\<phi> until \<psi>) (stl xs)\<rbrakk> \<Longrightarrow> (\<phi> until \<psi>) xs"

lemma holds_mono:
assumes holds: "holds P xs" and 0: "\<And> x. P x \<Longrightarrow> Q x"
shows "holds Q xs"
using assms by auto

lemma holds_aand:
"(holds P aand holds Q) steps \<longleftrightarrow> holds (\<lambda> step. P step \<and> Q step) steps" by auto

lemma nxt_mono:
assumes nxt: "nxt \<phi> xs" and 0: "\<And> xs. \<phi> xs \<Longrightarrow> \<psi> xs"
shows "nxt \<psi> xs"
using assms by auto

lemma ev_mono:
assumes ev: "ev \<phi> xs" and 0: "\<And> xs. \<phi> xs \<Longrightarrow> \<psi> xs"
shows "ev \<psi> xs"
using ev by induct (auto intro: ev.intros simp: 0)

lemma alw_mono:
assumes alw: "alw \<phi> xs" and 0: "\<And> xs. \<phi> xs \<Longrightarrow> \<psi> xs"
shows "alw \<psi> xs"
using alw by coinduct (auto elim: alw.cases simp: 0)

lemma until_monoL:
assumes until: "(\<phi>1 until \<psi>) xs" and 0: "\<And> xs. \<phi>1 xs \<Longrightarrow> \<phi>2 xs"
shows "(\<phi>2 until \<psi>) xs"
using until by coinduct (auto elim: UNTIL.cases simp: 0)

lemma until_monoR:
assumes until: "(\<phi> until \<psi>1) xs" and 0: "\<And> xs. \<psi>1 xs \<Longrightarrow> \<psi>2 xs"
shows "(\<phi> until \<psi>2) xs"
using until by coinduct (auto elim: UNTIL.cases simp: 0)

lemma until_mono:
assumes until: "(\<phi>1 until \<psi>1) xs" and
0: "\<And> xs. \<phi>1 xs \<Longrightarrow> \<phi>2 xs" "\<And> xs. \<psi>1 xs \<Longrightarrow> \<psi>2 xs"
shows "(\<phi>2 until \<psi>2) xs"
using until by coinduct (auto elim: UNTIL.cases simp: 0)

lemma until_false: "\<phi> until false = alw \<phi>"
proof-
  {fix xs assume "(\<phi> until false) xs" hence "alw \<phi> xs"
   apply coinduct by (auto elim: UNTIL.cases)
  }
  moreover
  {fix xs assume "alw \<phi> xs" hence "(\<phi> until false) xs"
   apply coinduct by (auto elim: alw.cases)
  }
  ultimately show ?thesis by blast
qed

lemma ev_nxt: "ev \<phi> = (\<phi> or nxt (ev \<phi>))"
apply(rule ext) by (metis ev.simps nxt.simps)

lemma alw_nxt: "alw \<phi> = (\<phi> aand nxt (alw \<phi>))"
apply(rule ext) by (metis alw.simps nxt.simps)

lemma ev_ev[simp]: "ev (ev \<phi>) = ev \<phi>"
proof-
  {fix xs
   assume "ev (ev \<phi>) xs" hence "ev \<phi> xs"
   by induct (auto intro: ev.intros)
  }
  thus ?thesis by (auto intro: ev.intros)
qed

lemma alw_alw[simp]: "alw (alw \<phi>) = alw \<phi>"
proof-
  {fix xs
   assume "alw \<phi> xs" hence "alw (alw \<phi>) xs"
   by coinduct (auto elim: alw.cases)
  }
  thus ?thesis by (auto elim: alw.cases)
qed

lemma ev_shift:
assumes "ev \<phi> xs"
shows "ev \<phi> (xl @- xs)"
using assms by (induct xl) (auto intro: ev.intros)

lemma ev_imp_shift:
assumes "ev \<phi> xs"  shows "\<exists> xl xs2. xs = xl @- xs2 \<and> \<phi> xs2"
using assms by induct (metis shift.simps(1), metis shift.simps(2) stream.collapse)+

lemma alw_ev_shift: "alw \<phi> xs1 \<Longrightarrow> ev (alw \<phi>) (xl @- xs1)"
by (auto intro: ev_shift ev.intros)

lemma alw_shift:
assumes "alw \<phi> (xl @- xs)"
shows "alw \<phi> xs"
using assms by (induct xl) (auto elim: alw.cases)

lemma ev_ex_nxt:
assumes "ev \<phi> xs"
shows "\<exists> n. (nxt ^^ n) \<phi> xs"
using assms proof induct
  case (base xs) thus ?case by (intro exI[of _ 0]) auto
next
  case (step xs)
  then obtain n where "(nxt ^^ n) \<phi> (stl xs)" by blast
  thus ?case by (intro exI[of _ "Suc n"]) (metis funpow.simps(2) nxt.simps o_def)
qed

lemma alw_sdrop:
assumes "alw \<phi> xs"  shows "alw \<phi> (sdrop n xs)"
by (metis alw_shift assms stake_sdrop)

lemma nxt_sdrop: "(nxt ^^ n) \<phi> xs \<longleftrightarrow> \<phi> (sdrop n xs)"
by (induct n arbitrary: xs) auto

definition "wait \<phi> xs \<equiv> LEAST n. (nxt ^^ n) \<phi> xs"

lemma nxt_wait:
assumes "ev \<phi> xs"  shows "(nxt ^^ (wait \<phi> xs)) \<phi> xs"
unfolding wait_def using ev_ex_nxt[OF assms] by(rule LeastI_ex)

lemma nxt_wait_least:
assumes ev: "ev \<phi> xs" and nxt: "(nxt ^^ n) \<phi> xs"  shows "wait \<phi> xs \<le> n"
unfolding wait_def using ev_ex_nxt[OF ev] by (metis Least_le nxt)

lemma sdrop_wait:
assumes "ev \<phi> xs"  shows "\<phi> (sdrop (wait \<phi> xs) xs)"
using nxt_wait[OF assms] unfolding nxt_sdrop .

lemma sdrop_wait_least:
assumes ev: "ev \<phi> xs" and nxt: "\<phi> (sdrop n xs)"  shows "wait \<phi> xs \<le> n"
using assms nxt_wait_least unfolding nxt_sdrop by auto

lemma nxt_ev: "(nxt ^^ n) \<phi> xs \<Longrightarrow> ev \<phi> xs"
by (induct n arbitrary: xs) (auto intro: ev.intros)

lemma not_ev: "not (ev \<phi>) = alw (not \<phi>)"
proof(rule ext, safe)
  fix xs assume "not (ev \<phi>) xs" thus "alw (not \<phi>) xs"
  by (coinduct) (auto intro: ev.intros)
next
  fix xs assume "ev \<phi> xs" and "alw (not \<phi>) xs" thus False
  by (induct) (auto elim: alw.cases)
qed

lemma not_alw: "not (alw \<phi>) = ev (not \<phi>)"
proof-
  have "not (alw \<phi>) = not (alw (not (not \<phi>)))" by simp
  also have "... = ev (not \<phi>)" unfolding not_ev[symmetric] by simp
  finally show ?thesis .
qed

lemma not_ev_not[simp]: "not (ev (not \<phi>)) = alw \<phi>"
unfolding not_ev by simp

lemma not_alw_not[simp]: "not (alw (not \<phi>)) = ev \<phi>"
unfolding not_alw by simp

lemma alw_ev_sdrop:
assumes "alw (ev \<phi>) (sdrop m xs)"
shows "alw (ev \<phi>) xs"
using assms
by coinduct (metis alw_nxt ev_shift funpow_swap1 nxt.simps nxt_sdrop stake_sdrop)

lemma ev_alw_imp_alw_ev:
assumes "ev (alw \<phi>) xs"  shows "alw (ev \<phi>) xs"
using assms apply induct
  apply (metis (full_types) alw_mono ev.base)
  by (metis alw alw_nxt ev.step)

lemma alw_aand: "alw (\<phi> aand \<psi>) = alw \<phi> aand alw \<psi>"
proof-
  {fix xs assume "alw (\<phi> aand \<psi>) xs" hence "(alw \<phi> aand alw \<psi>) xs"
   by (auto elim: alw_mono)
  }
  moreover
  {fix xs assume "(alw \<phi> aand alw \<psi>) xs" hence "alw (\<phi> aand \<psi>) xs"
   by coinduct (auto elim: alw.cases)
  }
  ultimately show ?thesis by blast
qed

lemma ev_or: "ev (\<phi> or \<psi>) = ev \<phi> or ev \<psi>"
proof-
  {fix xs assume "(ev \<phi> or ev \<psi>) xs" hence "ev (\<phi> or \<psi>) xs"
   by (auto elim: ev_mono)
  }
  moreover
  {fix xs assume "ev (\<phi> or \<psi>) xs" hence "(ev \<phi> or ev \<psi>) xs"
   by induct (auto intro: ev.intros)
  }
  ultimately show ?thesis by blast
qed

lemma ev_alw_aand:
assumes \<phi>: "ev (alw \<phi>) xs" and \<psi>: "ev (alw \<psi>) xs"
shows "ev (alw (\<phi> aand \<psi>)) xs"
proof-
  obtain xl xs1 where xs1: "xs = xl @- xs1" and \<phi>\<phi>: "alw \<phi> xs1"
  using \<phi> by (metis ev_imp_shift)
  moreover obtain yl ys1 where xs2: "xs = yl @- ys1" and \<psi>\<psi>: "alw \<psi> ys1"
  using \<psi> by (metis ev_imp_shift)
  ultimately have 0: "xl @- xs1 = yl @- ys1" by auto
  hence "prefixeq xl yl \<or> prefixeq yl xl" using shift_prefix_cases by auto
  thus ?thesis proof
    assume "prefixeq xl yl"
    then obtain yl1 where yl: "yl = xl @ yl1" by (elim prefixeqE)
    have xs1': "xs1 = yl1 @- ys1" using 0 unfolding yl by simp
    have "alw \<phi> ys1" using \<phi>\<phi> unfolding xs1' by (metis alw_shift)
    hence "alw (\<phi> aand \<psi>) ys1" using \<psi>\<psi> unfolding alw_aand by auto
    thus ?thesis unfolding xs2 by (auto intro: alw_ev_shift)
  next
    assume "prefixeq yl xl"
    then obtain xl1 where xl: "xl = yl @ xl1" by (elim prefixeqE)
    have ys1': "ys1 = xl1 @- xs1" using 0 unfolding xl by simp
    have "alw \<psi> xs1" using \<psi>\<psi> unfolding ys1' by (metis alw_shift)
    hence "alw (\<phi> aand \<psi>) xs1" using \<phi>\<phi> unfolding alw_aand by auto
    thus ?thesis unfolding xs1 by (auto intro: alw_ev_shift)
  qed
qed

lemma ev_alw_alw_impl:
assumes "ev (alw \<phi>) xs" and "alw (alw \<phi> impl ev \<psi>) xs"
shows "ev \<psi> xs"
using assms by induct (auto intro: ev.intros elim: alw.cases)

lemma ev_alw_stl[simp]: "ev (alw \<phi>) (stl x) \<longleftrightarrow> ev (alw \<phi>) x"
by (metis (full_types) alw_nxt ev_nxt nxt.simps)

lemma alw_alw_impl_ev:
"alw (alw \<phi> impl ev \<psi>) = (ev (alw \<phi>) impl alw (ev \<psi>))" (is "?A = ?B")
proof-
  {fix xs assume "?A xs \<and> ev (alw \<phi>) xs" hence "alw (ev \<psi>) xs"
   apply coinduct using ev_nxt by (auto elim: ev_alw_alw_impl alw.cases intro: ev.intros)
  }
  moreover
  {fix xs assume "?B xs" hence "?A xs"
   apply coinduct by (auto elim: alw.cases intro: ev.intros)
  }
  ultimately show ?thesis by blast
qed

lemma ev_alw_impl:
assumes "ev \<phi> xs" and "alw (\<phi> impl \<psi>) xs"  shows "ev \<psi> xs"
using assms by induct (auto intro: ev.intros elim: alw.cases)

lemma ev_alw_impl_ev:
assumes "ev \<phi> xs" and "alw (\<phi> impl ev \<psi>) xs"  shows "ev \<psi> xs"
using ev_alw_impl[OF assms] by simp

lemma alw_mp:
assumes "alw \<phi> xs" and "alw (\<phi> impl \<psi>) xs"
shows "alw \<psi> xs"
proof-
  {assume "alw \<phi> xs \<and> alw (\<phi> impl \<psi>) xs" hence ?thesis
   apply coinduct by (auto elim: alw.cases)
  }
  thus ?thesis using assms by auto
qed

lemma all_imp_alw:
assumes "\<And> xs. \<phi> xs"  shows "alw \<phi> xs"
proof-
  {assume "\<forall> xs. \<phi> xs"
   hence ?thesis by coinduct auto
  }
  thus ?thesis using assms by auto
qed

lemma alw_impl_ev_alw:
assumes "alw (\<phi> impl ev \<psi>) xs"
shows "alw (ev \<phi> impl ev \<psi>) xs"
using assms by coinduct (auto elim: alw.cases dest: ev_alw_impl intro: ev.intros)

lemma ev_holds_sset:
"ev (holds P) xs \<longleftrightarrow> (\<exists> x \<in> sset xs. P x)" (is "?L \<longleftrightarrow> ?R")
proof safe
  assume ?L thus ?R by induct (metis holds.simps stream.set_sel(1), metis stl_sset)
next
  fix x assume "x \<in> sset xs" "P x"
  thus ?L by (induct rule: sset_induct) (simp_all add: ev.base ev.step)
qed

(* LTL as a program logic: *)
lemma alw_invar:
assumes "\<phi> xs" and "alw (\<phi> impl nxt \<phi>) xs"
shows "alw \<phi> xs"
proof-
  {assume "\<phi> xs \<and> alw (\<phi> impl nxt \<phi>) xs" hence ?thesis
   apply coinduct by(auto elim: alw.cases)
  }
  thus ?thesis using assms by auto
qed

lemma variance:
assumes 1: "\<phi> xs" and 2: "alw (\<phi> impl (\<psi> or nxt \<phi>)) xs"
shows "(alw \<phi> or ev \<psi>) xs"
proof-
  {assume "\<not> ev \<psi> xs" hence "alw (not \<psi>) xs" unfolding not_ev[symmetric] .
   moreover have "alw (not \<psi> impl (\<phi> impl nxt \<phi>)) xs"
   using 2 by coinduct (auto elim: alw.cases)
   ultimately have "alw (\<phi> impl nxt \<phi>) xs" by(auto dest: alw_mp)
   with 1 have "alw \<phi> xs" by(rule alw_invar)
  }
  thus ?thesis by blast
qed

lemma ev_alw_imp_nxt:
assumes e: "ev \<phi> xs" and a: "alw (\<phi> impl (nxt \<phi>)) xs"
shows "ev (alw \<phi>) xs"
proof-
  obtain xl xs1 where xs: "xs = xl @- xs1" and \<phi>: "\<phi> xs1"
  using e by (metis ev_imp_shift)
  have "\<phi> xs1 \<and> alw (\<phi> impl (nxt \<phi>)) xs1" using a \<phi> unfolding xs by (metis alw_shift)
  hence "alw \<phi> xs1" by(coinduct xs1 rule: alw.coinduct) (auto elim: alw.cases)
  thus ?thesis unfolding xs by (auto intro: alw_ev_shift)
qed



end