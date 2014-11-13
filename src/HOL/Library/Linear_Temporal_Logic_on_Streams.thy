(*  Title:      HOL/Library/Linear_Temporal_Logic_on_Streams.thy
    Author:     Andrei Popescu, TU Muenchen
    Author:     Dmitriy Traytel, TU Muenchen
*)

section {* Linear Temporal Logic on Streams *}

theory Linear_Temporal_Logic_on_Streams
  imports Stream Sublist Extended_Nat Infinite_Set
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

definition "HLD s = holds (\<lambda>x. x \<in> s)"

abbreviation HLD_nxt (infixr "\<cdot>" 65) where
  "s \<cdot> P \<equiv> HLD s aand nxt P"

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

lemma HLD_iff: "HLD s \<omega> \<longleftrightarrow> shd \<omega> \<in> s"
  by (simp add: HLD_def)

lemma HLD_Stream[simp]: "HLD X (x ## \<omega>) \<longleftrightarrow> x \<in> X"
  by (simp add: HLD_iff)

lemma nxt_mono:
assumes nxt: "nxt \<phi> xs" and 0: "\<And> xs. \<phi> xs \<Longrightarrow> \<psi> xs"
shows "nxt \<psi> xs"
using assms by auto

declare ev.intros[intro]
declare alw.cases[elim]

lemma ev_induct_strong[consumes 1, case_names base step]:
  "ev \<phi> x \<Longrightarrow> (\<And>xs. \<phi> xs \<Longrightarrow> P xs) \<Longrightarrow> (\<And>xs. ev \<phi> (stl xs) \<Longrightarrow> \<not> \<phi> xs \<Longrightarrow> P (stl xs) \<Longrightarrow> P xs) \<Longrightarrow> P x"
  by (induct rule: ev.induct) auto

lemma alw_coinduct[consumes 1, case_names alw stl]:
  "X x \<Longrightarrow> (\<And>x. X x \<Longrightarrow> \<phi> x) \<Longrightarrow> (\<And>x. X x \<Longrightarrow> \<not> alw \<phi> (stl x) \<Longrightarrow> X (stl x)) \<Longrightarrow> alw \<phi> x"
  using alw.coinduct[of X x \<phi>] by auto

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


inductive ev_at :: "('a stream \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a stream \<Rightarrow> bool" for P :: "'a stream \<Rightarrow> bool" where
  base: "P \<omega> \<Longrightarrow> ev_at P 0 \<omega>"
| step:"\<not> P \<omega> \<Longrightarrow> ev_at P n (stl \<omega>) \<Longrightarrow> ev_at P (Suc n) \<omega>"

inductive_simps ev_at_0[simp]: "ev_at P 0 \<omega>"
inductive_simps ev_at_Suc[simp]: "ev_at P (Suc n) \<omega>"

lemma ev_at_imp_snth: "ev_at P n \<omega> \<Longrightarrow> P (sdrop n \<omega>)"
  by (induction n arbitrary: \<omega>) auto

lemma ev_at_HLD_imp_snth: "ev_at (HLD X) n \<omega> \<Longrightarrow> \<omega> !! n \<in> X"
  by (auto dest!: ev_at_imp_snth simp: HLD_iff)

lemma ev_at_HLD_single_imp_snth: "ev_at (HLD {x}) n \<omega> \<Longrightarrow> \<omega> !! n = x"
  by (drule ev_at_HLD_imp_snth) simp

lemma ev_at_unique: "ev_at P n \<omega> \<Longrightarrow> ev_at P m \<omega> \<Longrightarrow> n = m"
proof (induction arbitrary: m rule: ev_at.induct)
  case (base \<omega>) then show ?case
    by (simp add: ev_at.simps[of _ _ \<omega>])
next
  case (step \<omega> n) from step.prems step.hyps step.IH[of "m - 1"] show ?case
    by (auto simp add: ev_at.simps[of _ _ \<omega>])
qed

lemma ev_iff_ev_at: "ev P \<omega> \<longleftrightarrow> (\<exists>n. ev_at P n \<omega>)"
proof
  assume "ev P \<omega>" then show "\<exists>n. ev_at P n \<omega>"
    by (induction rule: ev_induct_strong) (auto intro: ev_at.intros)
next
  assume "\<exists>n. ev_at P n \<omega>"
  then obtain n where "ev_at P n \<omega>"
    by auto
  then show "ev P \<omega>"
    by induction auto
qed

lemma ev_at_shift: "ev_at (HLD X) i (stake (Suc i) \<omega> @- \<omega>' :: 's stream) \<longleftrightarrow> ev_at (HLD X) i \<omega>"
  by (induction i arbitrary: \<omega>) (auto simp: HLD_iff)

lemma ev_iff_ev_at_unqiue: "ev P \<omega> \<longleftrightarrow> (\<exists>!n. ev_at P n \<omega>)"
  by (auto intro: ev_at_unique simp: ev_iff_ev_at)

lemma alw_HLD_iff_streams: "alw (HLD X) \<omega> \<longleftrightarrow> \<omega> \<in> streams X"
proof
  assume "alw (HLD X) \<omega>" then show "\<omega> \<in> streams X"
  proof (coinduction arbitrary: \<omega>)
    case (streams \<omega>) then show ?case by (cases \<omega>) auto
  qed
next
  assume "\<omega> \<in> streams X" then show "alw (HLD X) \<omega>"
  proof (coinduction arbitrary: \<omega>)
    case (alw \<omega>) then show ?case by (cases \<omega>) auto
  qed
qed

lemma not_HLD: "not (HLD X) = HLD (- X)"
  by (auto simp: HLD_iff)

lemma not_alw_iff: "\<not> (alw P \<omega>) \<longleftrightarrow> ev (not P) \<omega>"
  using not_alw[of P] by (simp add: fun_eq_iff)

lemma not_ev_iff: "\<not> (ev P \<omega>) \<longleftrightarrow> alw (not P) \<omega>"
  using not_alw_iff[of "not P" \<omega>, symmetric]  by simp

lemma ev_Stream: "ev P (x ## s) \<longleftrightarrow> P (x ## s) \<or> ev P s"
  by (auto elim: ev.cases)

lemma alw_ev_imp_ev_alw:
  assumes "alw (ev P) \<omega>" shows "ev (P aand alw (ev P)) \<omega>"
proof -
  have "ev P \<omega>" using assms by auto
  from this assms show ?thesis
    by induct auto
qed

lemma ev_False: "ev (\<lambda>x. False) \<omega> \<longleftrightarrow> False"
proof
  assume "ev (\<lambda>x. False) \<omega>" then show False
    by induct auto
qed auto

lemma alw_False: "alw (\<lambda>x. False) \<omega> \<longleftrightarrow> False"
  by auto

lemma ev_iff_sdrop: "ev P \<omega> \<longleftrightarrow> (\<exists>m. P (sdrop m \<omega>))"
proof safe
  assume "ev P \<omega>" then show "\<exists>m. P (sdrop m \<omega>)"
    by (induct rule: ev_induct_strong) (auto intro: exI[of _ 0] exI[of _ "Suc n" for n])
next
  fix m assume "P (sdrop m \<omega>)" then show "ev P \<omega>"
    by (induct m arbitrary: \<omega>) auto
qed

lemma alw_iff_sdrop: "alw P \<omega> \<longleftrightarrow> (\<forall>m. P (sdrop m \<omega>))"
proof safe
  fix m assume "alw P \<omega>" then show "P (sdrop m \<omega>)"
    by (induct m arbitrary: \<omega>) auto
next
  assume "\<forall>m. P (sdrop m \<omega>)" then show "alw P \<omega>"
    by (coinduction arbitrary: \<omega>) (auto elim: allE[of _ 0] allE[of _ "Suc n" for n])
qed

lemma infinite_iff_alw_ev: "infinite {m. P (sdrop m \<omega>)} \<longleftrightarrow> alw (ev P) \<omega>"
  unfolding infinite_nat_iff_unbounded_le alw_iff_sdrop ev_iff_sdrop
  by simp (metis le_Suc_ex le_add1)

lemma alw_inv:
  assumes stl: "\<And>s. f (stl s) = stl (f s)"
  shows "alw P (f s) \<longleftrightarrow> alw (\<lambda>x. P (f x)) s"
proof
  assume "alw P (f s)" then show "alw (\<lambda>x. P (f x)) s"
    by (coinduction arbitrary: s rule: alw_coinduct)
       (auto simp: stl)
next
  assume "alw (\<lambda>x. P (f x)) s" then show "alw P (f s)"
    by (coinduction arbitrary: s rule: alw_coinduct) (auto simp: stl[symmetric])
qed

lemma ev_inv:
  assumes stl: "\<And>s. f (stl s) = stl (f s)"
  shows "ev P (f s) \<longleftrightarrow> ev (\<lambda>x. P (f x)) s"
proof
  assume "ev P (f s)" then show "ev (\<lambda>x. P (f x)) s"
    by (induction "f s" arbitrary: s) (auto simp: stl)
next
  assume "ev (\<lambda>x. P (f x)) s" then show "ev P (f s)"
    by induction (auto simp: stl[symmetric])
qed

lemma alw_smap: "alw P (smap f s) \<longleftrightarrow> alw (\<lambda>x. P (smap f x)) s"
  by (rule alw_inv) simp

lemma ev_smap: "ev P (smap f s) \<longleftrightarrow> ev (\<lambda>x. P (smap f x)) s"
  by (rule ev_inv) simp

lemma alw_cong:
  assumes P: "alw P \<omega>" and eq: "\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<longleftrightarrow> Q2 \<omega>"
  shows "alw Q1 \<omega> \<longleftrightarrow> alw Q2 \<omega>"
proof -
  from eq have "(alw P aand Q1) = (alw P aand Q2)" by auto
  then have "alw (alw P aand Q1) \<omega> = alw (alw P aand Q2) \<omega>" by auto
  with P show "alw Q1 \<omega> \<longleftrightarrow> alw Q2 \<omega>"
    by (simp add: alw_aand)
qed

lemma ev_cong:
  assumes P: "alw P \<omega>" and eq: "\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<longleftrightarrow> Q2 \<omega>"
  shows "ev Q1 \<omega> \<longleftrightarrow> ev Q2 \<omega>"
proof -
  from P have "alw (\<lambda>xs. Q1 xs \<longrightarrow> Q2 xs) \<omega>" by (rule alw_mono) (simp add: eq)
  moreover from P have "alw (\<lambda>xs. Q2 xs \<longrightarrow> Q1 xs) \<omega>" by (rule alw_mono) (simp add: eq)
  moreover note ev_alw_impl[of Q1 \<omega> Q2] ev_alw_impl[of Q2 \<omega> Q1]
  ultimately show "ev Q1 \<omega> \<longleftrightarrow> ev Q2 \<omega>"
    by auto
qed

lemma alwD: "alw P x \<Longrightarrow> P x"
  by auto

lemma alw_alwD: "alw P \<omega> \<Longrightarrow> alw (alw P) \<omega>"
  by simp

lemma alw_ev_stl: "alw (ev P) (stl \<omega>) \<longleftrightarrow> alw (ev P) \<omega>"
  by (auto intro: alw.intros)

lemma holds_Stream: "holds P (x ## s) \<longleftrightarrow> P x"
  by simp

lemma holds_eq1[simp]: "holds (op = x) = HLD {x}"
  by rule (auto simp: HLD_iff)

lemma holds_eq2[simp]: "holds (\<lambda>y. y = x) = HLD {x}"
  by rule (auto simp: HLD_iff)

lemma not_holds_eq[simp]: "holds (- op = x) = not (HLD {x})"
  by rule (auto simp: HLD_iff)

text {* Strong until *}

inductive suntil (infix "suntil" 60) for \<phi> \<psi> where
  base: "\<psi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>"
| step: "\<phi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) (stl \<omega>) \<Longrightarrow> (\<phi> suntil \<psi>) \<omega>"

inductive_simps suntil_Stream: "(\<phi> suntil \<psi>) (x ## s)"

lemma suntil_induct_strong[consumes 1, case_names base step]:
  "(\<phi> suntil \<psi>) x \<Longrightarrow>
    (\<And>\<omega>. \<psi> \<omega> \<Longrightarrow> P \<omega>) \<Longrightarrow>
    (\<And>\<omega>. \<phi> \<omega> \<Longrightarrow> \<not> \<psi> \<omega> \<Longrightarrow> (\<phi> suntil \<psi>) (stl \<omega>) \<Longrightarrow> P (stl \<omega>) \<Longrightarrow> P \<omega>) \<Longrightarrow> P x"
  using suntil.induct[of \<phi> \<psi> x P] by blast

lemma ev_suntil: "(\<phi> suntil \<psi>) \<omega> \<Longrightarrow> ev \<psi> \<omega>"
  by (induct rule: suntil.induct) (auto intro: ev.intros)

lemma suntil_inv:
  assumes stl: "\<And>s. f (stl s) = stl (f s)"
  shows "(P suntil Q) (f s) \<longleftrightarrow> ((\<lambda>x. P (f x)) suntil (\<lambda>x. Q (f x))) s"
proof
  assume "(P suntil Q) (f s)" then show "((\<lambda>x. P (f x)) suntil (\<lambda>x. Q (f x))) s"
    by (induction "f s" arbitrary: s) (auto simp: stl intro: suntil.intros)
next
  assume "((\<lambda>x. P (f x)) suntil (\<lambda>x. Q (f x))) s" then show "(P suntil Q) (f s)"
    by induction (auto simp: stl[symmetric] intro: suntil.intros)
qed

lemma suntil_smap: "(P suntil Q) (smap f s) \<longleftrightarrow> ((\<lambda>x. P (smap f x)) suntil (\<lambda>x. Q (smap f x))) s"
  by (rule suntil_inv) simp

lemma hld_smap: "HLD x (smap f s) = holds (\<lambda>y. f y \<in> x) s"
  by (simp add: HLD_def)

lemma suntil_mono:
  assumes eq: "\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<Longrightarrow> Q2 \<omega>" "\<And>\<omega>. P \<omega> \<Longrightarrow> R1 \<omega> \<Longrightarrow> R2 \<omega>"
  assumes *: "(Q1 suntil R1) \<omega>" "alw P \<omega>" shows "(Q2 suntil R2) \<omega>"
  using * by induct (auto intro: eq suntil.intros)

lemma suntil_cong:
  "alw P \<omega> \<Longrightarrow> (\<And>\<omega>. P \<omega> \<Longrightarrow> Q1 \<omega> \<longleftrightarrow> Q2 \<omega>) \<Longrightarrow> (\<And>\<omega>. P \<omega> \<Longrightarrow> R1 \<omega> \<longleftrightarrow> R2 \<omega>) \<Longrightarrow>
    (Q1 suntil R1) \<omega> \<longleftrightarrow> (Q2 suntil R2) \<omega>"
  using suntil_mono[of P Q1 Q2 R1 R2 \<omega>] suntil_mono[of P Q2 Q1 R2 R1 \<omega>] by auto

lemma ev_suntil_iff: "ev (P suntil Q) \<omega> \<longleftrightarrow> ev Q \<omega>"
proof
  assume "ev (P suntil Q) \<omega>" then show "ev Q \<omega>"
   by induct (auto dest: ev_suntil)
next
  assume "ev Q \<omega>" then show "ev (P suntil Q) \<omega>"
    by induct (auto intro: suntil.intros)
qed

lemma true_suntil: "((\<lambda>_. True) suntil P) = ev P"
  by (simp add: suntil_def ev_def)

lemma suntil_lfp: "(\<phi> suntil \<psi>) = lfp (\<lambda>P s. \<psi> s \<or> (\<phi> s \<and> P (stl s)))"
  by (simp add: suntil_def)

lemma sfilter_P[simp]: "P (shd s) \<Longrightarrow> sfilter P s = shd s ## sfilter P (stl s)"
  using sfilter_Stream[of P "shd s" "stl s"] by simp

lemma sfilter_not_P[simp]: "\<not> P (shd s) \<Longrightarrow> sfilter P s = sfilter P (stl s)"
  using sfilter_Stream[of P "shd s" "stl s"] by simp

lemma sfilter_eq: 
  assumes "ev (holds P) s"
  shows "sfilter P s = x ## s' \<longleftrightarrow>
    P x \<and> (not (holds P) suntil (HLD {x} aand nxt (\<lambda>s. sfilter P s = s'))) s"
  using assms
  by (induct rule: ev_induct_strong)
     (auto simp add: HLD_iff intro: suntil.intros elim: suntil.cases)

lemma sfilter_streams:
  "alw (ev (holds P)) \<omega> \<Longrightarrow> \<omega> \<in> streams A \<Longrightarrow> sfilter P \<omega> \<in> streams {x\<in>A. P x}"
proof (coinduction arbitrary: \<omega>)
  case (streams \<omega>)
  then have "ev (holds P) \<omega>" by blast
  from this streams show ?case
    by (induct rule: ev_induct_strong) (auto elim: streamsE)
qed

lemma alw_sfilter:
  assumes *: "alw (ev (holds P)) s"
  shows "alw Q (sfilter P s) \<longleftrightarrow> alw (\<lambda>x. Q (sfilter P x)) s"
proof
  assume "alw Q (sfilter P s)" with * show "alw (\<lambda>x. Q (sfilter P x)) s"
  proof (coinduction arbitrary: s rule: alw_coinduct)
    case (stl s) 
    then have "ev (holds P) s"
      by blast
    from this stl show ?case
      by (induct rule: ev_induct_strong) auto
  qed auto
next
  assume "alw (\<lambda>x. Q (sfilter P x)) s" with * show "alw Q (sfilter P s)"
  proof (coinduction arbitrary: s rule: alw_coinduct)
    case (stl s) 
    then have "ev (holds P) s"
      by blast
    from this stl show ?case
      by (induct rule: ev_induct_strong) auto
  qed auto
qed

lemma ev_sfilter:
  assumes *: "alw (ev (holds P)) s"
  shows "ev Q (sfilter P s) \<longleftrightarrow> ev (\<lambda>x. Q (sfilter P x)) s"
proof
  assume "ev Q (sfilter P s)" from this * show "ev (\<lambda>x. Q (sfilter P x)) s"
  proof (induction "sfilter P s" arbitrary: s rule: ev_induct_strong)
    case (step s)
    then have "ev (holds P) s"
      by blast
    from this step show ?case
      by (induct rule: ev_induct_strong) auto
  qed auto
next
  assume "ev (\<lambda>x. Q (sfilter P x)) s" then show "ev Q (sfilter P s)"
  proof (induction rule: ev_induct_strong)
    case (step s) then show ?case
      by (cases "P (shd s)") auto
  qed auto
qed

lemma holds_sfilter:
  assumes "ev (holds Q) s" shows "holds P (sfilter Q s) \<longleftrightarrow> (not (holds Q) suntil (holds (Q aand P))) s"
proof
  assume "holds P (sfilter Q s)" with assms show "(not (holds Q) suntil (holds (Q aand P))) s"
    by (induct rule: ev_induct_strong) (auto intro: suntil.intros)
next
  assume "(not (holds Q) suntil (holds (Q aand P))) s" then show "holds P (sfilter Q s)"
    by induct auto
qed

lemma suntil_aand_nxt:
  "(\<phi> suntil (\<phi> aand nxt \<psi>)) \<omega> \<longleftrightarrow> (\<phi> aand nxt (\<phi> suntil \<psi>)) \<omega>"
proof
  assume "(\<phi> suntil (\<phi> aand nxt \<psi>)) \<omega>" then show "(\<phi> aand nxt (\<phi> suntil \<psi>)) \<omega>"
    by induction (auto intro: suntil.intros)
next
  assume "(\<phi> aand nxt (\<phi> suntil \<psi>)) \<omega>"
  then have "(\<phi> suntil \<psi>) (stl \<omega>)" "\<phi> \<omega>"
    by auto
  then show "(\<phi> suntil (\<phi> aand nxt \<psi>)) \<omega>"
    by (induction "stl \<omega>" arbitrary: \<omega>)
       (auto elim: suntil.cases intro: suntil.intros)
qed

lemma alw_sconst: "alw P (sconst x) \<longleftrightarrow> P (sconst x)"
proof
  assume "P (sconst x)" then show "alw P (sconst x)"
    by coinduction auto
qed auto

lemma ev_sconst: "ev P (sconst x) \<longleftrightarrow> P (sconst x)"
proof
  assume "ev P (sconst x)" then show "P (sconst x)"
    by (induction "sconst x") auto
qed auto

lemma suntil_sconst: "(\<phi> suntil \<psi>) (sconst x) \<longleftrightarrow> \<psi> (sconst x)"
proof
  assume "(\<phi> suntil \<psi>) (sconst x)" then show "\<psi> (sconst x)"
    by (induction "sconst x") auto
qed (auto intro: suntil.intros)

lemma hld_smap': "HLD x (smap f s) = HLD (f -` x) s"
  by (simp add: HLD_def)

end