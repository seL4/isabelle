(*  Author:     Bernhard Haeupler

This theory is about of the relative completeness of the ring
method.  As long as the reified atomic polynomials of type pol are
in normal form, the ring method is complete.
*)

section \<open>Proof of the relative completeness of method comm-ring\<close>

theory Commutative_Ring_Complete
  imports Commutative_Ring
begin

text \<open>Formalization of normal form\<close>
fun isnorm :: "pol \<Rightarrow> bool"
  where
    "isnorm (Pc c) \<longleftrightarrow> True"
  | "isnorm (Pinj i (Pc c)) \<longleftrightarrow> False"
  | "isnorm (Pinj i (Pinj j Q)) \<longleftrightarrow> False"
  | "isnorm (Pinj 0 P) \<longleftrightarrow> False"
  | "isnorm (Pinj i (PX Q1 j Q2)) \<longleftrightarrow> isnorm (PX Q1 j Q2)"
  | "isnorm (PX P 0 Q) \<longleftrightarrow> False"
  | "isnorm (PX (Pc c) i Q) \<longleftrightarrow> c \<noteq> 0 \<and> isnorm Q"
  | "isnorm (PX (PX P1 j (Pc c)) i Q) \<longleftrightarrow> c \<noteq> 0 \<and> isnorm (PX P1 j (Pc c)) \<and> isnorm Q"
  | "isnorm (PX P i Q) \<longleftrightarrow> isnorm P \<and> isnorm Q"


subsection \<open>Some helpful lemmas\<close>

lemma norm_Pinj_0_False: "isnorm (Pinj 0 P) = False"
  by (cases P) auto

lemma norm_PX_0_False: "isnorm (PX (Pc 0) i Q) = False"
  by (cases i) auto

lemma norm_Pinj: "isnorm (Pinj i Q) \<Longrightarrow> isnorm Q"
  using isnorm.elims(2) by fastforce

lemma norm_PX2: "isnorm (PX P i Q) \<Longrightarrow> isnorm Q"
  using isnorm.elims(1) by auto

lemma norm_PX1: assumes "isnorm (PX P i Q)" shows "isnorm P"
proof (cases P)
  case (Pc x1)
  then show ?thesis
    by auto 
qed (use assms isnorm.elims(1) in auto)

lemma mkPinj_cn:
  assumes "y \<noteq> 0" and "isnorm Q" 
  shows "isnorm (mkPinj y Q)"
proof (cases Q)
  case Pc
  with assms show ?thesis
    by (simp add: mkPinj_def)
next
  case Pinj
  with assms show ?thesis
    using isnorm.elims(2) isnorm.simps(5) mkPinj_def by fastforce
next
  case PX
  with assms show ?thesis
  using isnorm.elims(1) mkPinj_def by auto
qed

lemma norm_PXtrans:
  assumes "isnorm (PX P x Q)" and "isnorm Q2"
  shows "isnorm (PX P x Q2)"
  using assms isnorm.elims(3) by fastforce


lemma norm_PXtrans2:
  assumes "isnorm (PX P x Q)"
    and "isnorm Q2"
  shows "isnorm (PX P (Suc (n + x)) Q2)"
proof (cases P)
  case (PX p1 y p2)
  with assms show ?thesis
  using isnorm.elims(2) by fastforce
next
  case Pc
  with assms show ?thesis
    by (cases x) auto
next
  case Pinj
  with assms show ?thesis
    by (cases x) auto
qed

text \<open>\<open>mkPX\<close> preserves the normal property (\<open>_cn\<close>)\<close>
lemma mkPX_cn:
  assumes "x \<noteq> 0"
    and "isnorm P"
    and "isnorm Q"
  shows "isnorm (mkPX P x Q)"
proof (cases P)
  case (Pc c)
  with assms show ?thesis
    by (cases x) (auto simp add: mkPinj_cn mkPX_def)
next
  case (Pinj i Q)
  with assms show ?thesis
    by (cases x) (auto simp add: mkPinj_cn mkPX_def)
next
  case (PX P1 y P2)
  with assms have Y0: "y > 0"
    by (cases y) auto
  from assms PX have "isnorm P1" "isnorm P2"
    by (auto simp add: norm_PX1[of P1 y P2] norm_PX2[of P1 y P2])
  from assms PX Y0 show ?thesis
  proof (cases P2)
    case (Pc x1)
    then show ?thesis
      using assms gr0_conv_Suc PX by (auto simp add: mkPX_def norm_PXtrans2)
  next
    case (Pinj x21 x22)
    with assms gr0_conv_Suc PX show ?thesis
      by (auto simp: mkPX_def)
  next
    case (PX x31 x32 x33)
    with assms gr0_conv_Suc \<open>P = PX P1 y P2\<close>
    show ?thesis
      using assms PX by (auto simp add: mkPX_def norm_PXtrans2)
  qed
qed

text \<open>\<open>add\<close> preserves the normal property\<close>
lemma add_cn: "isnorm P \<Longrightarrow> isnorm Q \<Longrightarrow> isnorm (P \<langle>+\<rangle> Q)"
proof (induct P Q rule: add.induct)
  case 1
  then show ?case by simp
next
  case (2 c i P2)
  then show ?case
    using isnorm.elims(2) by fastforce
next
  case (3 i P2 c)
  then show ?case
    using isnorm.elims(2) by fastforce
next
  case (4 c P2 i Q2)
  then have "isnorm P2" "isnorm Q2"
    by (auto simp only: norm_PX1[of P2 i Q2] norm_PX2[of P2 i Q2])
  with 4 show ?case
    using isnorm.elims(2) by fastforce
next
  case (5 P2 i Q2 c)
  then have "isnorm P2" "isnorm Q2"
    by (auto simp only: norm_PX1[of P2 i Q2] norm_PX2[of P2 i Q2])
  with 5 show ?case
    using isnorm.elims(2) by fastforce
next
  case (6 x P2 y Q2)
  then have Y0: "y > 0"
    by (cases y) (auto simp add: norm_Pinj_0_False)
  with 6 have X0: "x > 0"
    by (cases x) (auto simp add: norm_Pinj_0_False)
  consider "x < y" | "x = y" | "x > y" by arith
  then show ?case
  proof cases
    case xy: 1
    then obtain d where y: "y = d + x"
      by atomize_elim arith
    from 6 have *: "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    from 6 xy y have "isnorm (Pinj d Q2)"
      by (cases d, simp, cases Q2, auto)
    with 6 X0 y * show ?thesis
      by (simp add: mkPinj_cn)
  next
    case xy: 2
    from 6 have "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    with xy 6 Y0 show ?thesis
      by (simp add: mkPinj_cn)
  next
    case xy: 3
    then obtain d where x: "x = d + y"
      by atomize_elim arith
    from 6 have *: "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    from 6 xy x have "isnorm (Pinj d P2)"
      by (cases d) (simp, cases P2, auto)
    with xy 6 Y0 * x show ?thesis by (simp add: mkPinj_cn)
  qed
next
  case (7 x P2 Q2 y R)
  consider "x = 0" | "x = 1" | d where "x = Suc (Suc d)"
    by atomize_elim arith
  then show ?case
  proof cases
    case 1
    with 7 show ?thesis
      by (auto simp add: norm_Pinj_0_False)
  next
    case x: 2
    from 7 have "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 7 x have "isnorm (R \<langle>+\<rangle> P2)"
      by simp
    with 7 x show ?thesis
      by (simp add: norm_PXtrans[of Q2 y _])
  next
    case x: 3
    with 7 have NR: "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 7 x have "isnorm (Pinj (x - 1) P2)"
      by (cases P2) auto
    with 7 x NR have "isnorm (R \<langle>+\<rangle> Pinj (x - 1) P2)"
      by simp
    with \<open>isnorm (PX Q2 y R)\<close> x show ?thesis
      by (simp add: norm_PXtrans[of Q2 y _])
  qed
next
  case (8 Q2 y R x P2)
  consider "x = 0" | "x = 1" | "x > 1"
    by arith
  then show ?case
  proof cases
    case 1
    with 8 show ?thesis
      by (auto simp add: norm_Pinj_0_False)
  next
    case x: 2
    with 8 have "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 8 x have "isnorm (R \<langle>+\<rangle> P2)"
      by simp
    with 8 x show ?thesis
      by (simp add: norm_PXtrans[of Q2 y _])
  next
    case x: 3
    then obtain d where x: "x = Suc (Suc d)" by atomize_elim arith
    with 8 have NR: "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 8 x have "isnorm (Pinj (x - 1) P2)"
      by (cases P2) auto
    with 8 x NR have "isnorm (R \<langle>+\<rangle> Pinj (x - 1) P2)"
      by simp
    with \<open>isnorm (PX Q2 y R)\<close> x show ?thesis
      by (simp add: norm_PXtrans[of Q2 y _])
  qed
next
  case (9 P1 x P2 Q1 y Q2)
  then have Y0: "y > 0" by (cases y) auto
  with 9 have X0: "x > 0" by (cases x) auto
  with 9 have NP1: "isnorm P1" and NP2: "isnorm P2"
    by (auto simp add: norm_PX1[of P1 _ P2] norm_PX2[of P1 _ P2])
  with 9 have NQ1: "isnorm Q1" and NQ2: "isnorm Q2"
    by (auto simp add: norm_PX1[of Q1 _ Q2] norm_PX2[of Q1 _ Q2])
  consider "y < x" | "x = y" | "x < y" by arith
  then show ?case
  proof cases
    case xy: 1
    then obtain d where x: "x = d + y"
      by atomize_elim arith
    have "isnorm (PX P1 d (Pc 0))"
    proof (cases P1)
      case (PX p1 y p2)
      with 9 xy x show ?thesis
        by (cases d) (simp, cases p2, auto)
    next
      case Pc
      with 9 xy x show ?thesis
        by (cases d) auto
    next
      case Pinj
      with 9 xy x show ?thesis
        by (cases d) auto
    qed
    with 9 NQ1 NP1 NP2 NQ2 xy x have "isnorm (P2 \<langle>+\<rangle> Q2)" "isnorm (PX P1 (x - y) (Pc 0) \<langle>+\<rangle> Q1)"
      by auto
    with Y0 xy x show ?thesis
      by (simp add: mkPX_cn)
  next
    case xy: 2
    with 9 NP1 NP2 NQ1 NQ2 have "isnorm (P2 \<langle>+\<rangle> Q2)" "isnorm (P1 \<langle>+\<rangle> Q1)"
      by auto
    with xy Y0 show ?thesis
      by (simp add: mkPX_cn)
  next
    case xy: 3
    then obtain d where y: "y = d + x"
      by atomize_elim arith
    have "isnorm (PX Q1 d (Pc 0))"
    proof (cases Q1)
      case (PX p1 y p2)
      with 9 xy y show ?thesis
        by (cases d) (simp, cases p2, auto)
    next
      case Pc
      with 9 xy y show ?thesis
        by (cases d) auto
    next
      case Pinj
      with 9 xy y show ?thesis
        by (cases d) auto
    qed
    with 9 NQ1 NP1 NP2 NQ2 xy y have "isnorm (P2 \<langle>+\<rangle> Q2)" "isnorm (PX Q1 (y - x) (Pc 0) \<langle>+\<rangle> P1)"
      by auto
    with X0 xy y show ?thesis
      by (simp add: mkPX_cn)
  qed
qed

text \<open>\<open>mul\<close> concerves normalizedness\<close>
lemma mul_cn: "isnorm P \<Longrightarrow> isnorm Q \<Longrightarrow> isnorm (P \<langle>*\<rangle> Q)"
proof (induct P Q rule: mul.induct)
  case 1
  then show ?case by simp
next
  case (2 c i P2)
  then show ?case
    by (metis mkPinj_cn mul.simps(2) norm_Pinj norm_Pinj_0_False)
next
  case (3 i P2 c)
  then show ?case
    by (metis mkPinj_cn mul.simps(3) norm_Pinj norm_Pinj_0_False)
next
  case (4 c P2 i Q2)
  then show ?case
    by (metis isnorm.simps(6) mkPX_cn mul.simps(4) norm_PX1 norm_PX2)
next
  case (5 P2 i Q2 c)
  then show ?case
    by (metis isnorm.simps(6) mkPX_cn mul.simps(5) norm_PX1 norm_PX2)
next
  case (6 x P2 y Q2)
  consider "x < y" | "x = y" | "x > y" by arith
  then show ?case
  proof cases
    case xy: 1
    then obtain d where y: "y = d + x"
      by atomize_elim arith
    from 6 have *: "x > 0"
      by (cases x) (auto simp add: norm_Pinj_0_False)
    from 6 have **: "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    from 6 xy y have "isnorm (Pinj d Q2)"
      apply simp
      by (smt (verit, ccfv_SIG) "**"(2) Suc_pred isnorm.elims(1) isnorm.simps(2) isnorm.simps(3) isnorm.simps(5))
    with 6 * ** y show ?thesis
      by (simp add: mkPinj_cn)
  next
    case xy: 2
    from 6 have *: "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    from 6 have **: "y > 0"
      by (cases y) (auto simp add: norm_Pinj_0_False)
    with 6 xy * ** show ?thesis
      by (simp add: mkPinj_cn)
  next
    case xy: 3
    then obtain d where x: "x = d + y"
      by atomize_elim arith
    from 6 have *: "y > 0"
      by (cases y) (auto simp add: norm_Pinj_0_False)
    from 6 have **: "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    with 6 xy x have "isnorm (Pinj d P2)"
      apply simp
      by (smt (verit, ccfv_SIG) Suc_pred isnorm.elims(1) isnorm.simps(2) isnorm.simps(3) isnorm.simps(5))
    with 6 xy * ** x show ?thesis
      by (simp add: mkPinj_cn)
  qed
next
  case (7 x P2 Q2 y R)
  then have Y0: "y > 0" by (cases y) auto
  consider "x = 0" | "x = 1" | d where "x = Suc (Suc d)"
    by atomize_elim arith
  then show ?case
  proof cases
    case 1
    with 7 show ?thesis
      by (auto simp add: norm_Pinj_0_False)
  next
    case x: 2
    from 7 have "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 7 x have "isnorm (R \<langle>*\<rangle> P2)" "isnorm Q2"
      by (auto simp add: norm_PX1[of Q2 y R])
    with 7 x Y0 show ?thesis
      by (simp add: mkPX_cn)
  next
    case x: 3
    from 7 have *: "isnorm R" "isnorm Q2"
      by (auto simp add: norm_PX2[of Q2 y R] norm_PX1[of Q2 y R])
    from 7 x have "isnorm (Pinj (x - 1) P2)"
      by (cases P2) auto
    with 7 x * have "isnorm (R \<langle>*\<rangle> Pinj (x - 1) P2)" "isnorm (Pinj x P2 \<langle>*\<rangle> Q2)"
      by auto
    with Y0 x show ?thesis
      by (simp add: mkPX_cn)
  qed
next
  case (8 Q2 y R x P2)
  then have Y0: "y > 0"
    by (cases y) auto
  consider "x = 0" | "x = 1" | d where "x = Suc (Suc d)"
    by atomize_elim arith
  then show ?case
  proof cases
    case 1
    with 8 show ?thesis
      by (auto simp add: norm_Pinj_0_False)
  next
    case x: 2
    from 8 have "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 8 x have "isnorm (R \<langle>*\<rangle> P2)" "isnorm Q2"
      by (auto simp add: norm_PX1[of Q2 y R])
    with 8 x Y0 show ?thesis
      by (simp add: mkPX_cn)
  next
    case x: 3
    from 8 have *: "isnorm R" "isnorm Q2"
      by (auto simp add: norm_PX2[of Q2 y R] norm_PX1[of Q2 y R])
    from 8 x have "isnorm (Pinj (x - 1) P2)"
      by (cases P2) auto
    with 8 x * have "isnorm (R \<langle>*\<rangle> Pinj (x - 1) P2)" "isnorm (Pinj x P2 \<langle>*\<rangle> Q2)"
      by auto
    with Y0 x show ?thesis
      by (simp add: mkPX_cn)
  qed
next
  case (9 P1 x P2 Q1 y Q2)
  from 9 have X0: "x > 0" by (cases x) auto
  from 9 have Y0: "y > 0" by (cases y) auto
  from 9 have *: "isnorm P1" "isnorm P2"
    by (auto simp add: norm_PX1[of P1 x P2] norm_PX2[of P1 x P2])
  from 9 have "isnorm Q1" "isnorm Q2"
    by (auto simp add: norm_PX1[of Q1 y Q2] norm_PX2[of Q1 y Q2])
  with 9 * have "isnorm (P1 \<langle>*\<rangle> Q1)" "isnorm (P2 \<langle>*\<rangle> Q2)"
    "isnorm (P1 \<langle>*\<rangle> mkPinj 1 Q2)" "isnorm (Q1 \<langle>*\<rangle> mkPinj 1 P2)"
    by (auto simp add: mkPinj_cn)
  with 9 X0 Y0 have
    "isnorm (mkPX (P1 \<langle>*\<rangle> Q1) (x + y) (P2 \<langle>*\<rangle> Q2))"
    "isnorm (mkPX (P1 \<langle>*\<rangle> mkPinj (Suc 0) Q2) x (Pc 0))"
    "isnorm (mkPX (Q1 \<langle>*\<rangle> mkPinj (Suc 0) P2) y (Pc 0))"
    by (auto simp add: mkPX_cn)
  then show ?case
    by (simp add: add_cn)
qed

text \<open>neg preserves the normal property\<close>
lemma neg_cn: "isnorm P \<Longrightarrow> isnorm (neg P)"
proof (induct P)
  case Pc
  then show ?case by simp
next
  case (Pinj i P2)
  then have "isnorm P2"
    by (simp add: norm_Pinj[of i P2])
  with Pinj show ?case
    by (cases P2) (auto, cases i, auto)
next
  case (PX P1 x P2) note PX1 = this
  from PX have "isnorm P2" "isnorm P1"
    by (auto simp add: norm_PX1[of P1 x P2] norm_PX2[of P1 x P2])
  with PX show ?case
  proof (cases P1)
    case (PX p1 y p2)
    with PX1 show ?thesis
      by (cases x) (auto, cases p2, auto)
  next
    case Pinj
    with PX1 show ?thesis
      by (cases x) auto
  qed (cases x, auto)
qed

text \<open>sub preserves the normal property\<close>
lemma sub_cn: "isnorm p \<Longrightarrow> isnorm q \<Longrightarrow> isnorm (p \<langle>-\<rangle> q)"
  by (simp add: sub_def add_cn neg_cn)

text \<open>sqr conserves normalizizedness\<close>
lemma sqr_cn: "isnorm P \<Longrightarrow> isnorm (sqr P)"
proof (induct P)
  case Pc
  then show ?case by simp
next
  case (Pinj i Q)
  then show ?case
    by (metis Commutative_Ring.sqr.simps(2) mkPinj_cn norm_Pinj norm_Pinj_0_False)
next
  case (PX P1 x P2)
  then have "x + x \<noteq> 0" "isnorm P2" "isnorm P1"
    by (cases x) (use PX in \<open>auto simp add: norm_PX1[of P1 x P2] norm_PX2[of P1 x P2]\<close>)
  with PX have "isnorm (mkPX (Pc (1 + 1) \<langle>*\<rangle> P1 \<langle>*\<rangle> mkPinj (Suc 0) P2) x (Pc 0))"
    and "isnorm (mkPX (sqr P1) (x + x) (sqr P2))"
    by (auto simp add: add_cn mkPX_cn mkPinj_cn mul_cn)
  then show ?case
    by (auto simp add: add_cn mkPX_cn mkPinj_cn mul_cn)
qed

text \<open>\<open>pow\<close> preserves the normal property\<close>
lemma pow_cn: "isnorm P \<Longrightarrow> isnorm (pow n P)"
proof (induct n arbitrary: P rule: less_induct)
  case (less k)
  show ?case
  proof (cases "k = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then have K2: "k div 2 < k"
      by (cases k) auto
    from less have "isnorm (sqr P)"
      by (simp add: sqr_cn)
    with less False K2 show ?thesis
      by (cases "even k") (auto simp add: mul_cn elim: evenE oddE)
  qed
qed

end
