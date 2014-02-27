(*  Author:     Bernhard Haeupler

This theory is about of the relative completeness of method comm-ring
method.  As long as the reified atomic polynomials of type 'a pol are
in normal form, the cring method is complete.
*)

header {* Proof of the relative completeness of method comm-ring *}

theory Commutative_Ring_Complete
imports Commutative_Ring
begin

text {* Formalization of normal form *}
fun isnorm :: "'a::comm_ring pol \<Rightarrow> bool"
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

(* Some helpful lemmas *)
lemma norm_Pinj_0_False: "isnorm (Pinj 0 P) = False"
  by (cases P) auto

lemma norm_PX_0_False: "isnorm (PX (Pc 0) i Q) = False"
  by (cases i) auto

lemma norm_Pinj: "isnorm (Pinj i Q) \<Longrightarrow> isnorm Q"
  by (cases i) (simp add: norm_Pinj_0_False norm_PX_0_False, cases Q, auto)

lemma norm_PX2: "isnorm (PX P i Q) \<Longrightarrow> isnorm Q"
  apply (cases i)
  apply auto
  apply (cases P)
  apply auto
  apply (case_tac pol2)
  apply auto
  done

lemma norm_PX1: "isnorm (PX P i Q) \<Longrightarrow> isnorm P"
  apply (cases i)
  apply auto
  apply (cases P)
  apply auto
  apply (case_tac pol2)
  apply auto
  done

lemma mkPinj_cn: "y \<noteq> 0 \<Longrightarrow> isnorm Q \<Longrightarrow> isnorm (mkPinj y Q)"
  apply (auto simp add: mkPinj_def norm_Pinj_0_False split: pol.split)
  apply (case_tac nat, auto simp add: norm_Pinj_0_False)
  apply (case_tac pol, auto)
  apply (case_tac y, auto)
  done

lemma norm_PXtrans:
  assumes A: "isnorm (PX P x Q)"
    and "isnorm Q2"
  shows "isnorm (PX P x Q2)"
proof (cases P)
  case (PX p1 y p2)
  with assms show ?thesis
    apply (cases x)
    apply auto
    apply (cases p2)
    apply auto
    done
next
  case Pc
  with assms show ?thesis by (cases x) auto
next
  case Pinj
  with assms show ?thesis by (cases x) auto
qed

lemma norm_PXtrans2:
  assumes "isnorm (PX P x Q)"
    and "isnorm Q2"
  shows "isnorm (PX P (Suc (n + x)) Q2)"
proof (cases P)
  case (PX p1 y p2)
  with assms show ?thesis
    apply (cases x)
    apply auto
    apply (cases p2)
    apply auto
    done
next
  case Pc
  with assms show ?thesis
    by (cases x) auto
next
  case Pinj
  with assms show ?thesis
    by (cases x) auto
qed

text {* mkPX conserves normalizedness (@{text "_cn"}) *}
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
    by (cases x) (auto simp add: mkPX_def norm_PXtrans2[of P1 y _ Q _], cases P2, auto)
qed

text {* add conserves normalizedness *}
lemma add_cn: "isnorm P \<Longrightarrow> isnorm Q \<Longrightarrow> isnorm (P \<oplus> Q)"
proof (induct P Q rule: add.induct)
  case (2 c i P2)
  then show ?case
    by (cases P2) (simp_all, cases i, simp_all)
next
  case (3 i P2 c)
  then show ?case
    by (cases P2) (simp_all, cases i, simp_all)
next
  case (4 c P2 i Q2)
  then have "isnorm P2" "isnorm Q2"
    by (auto simp only: norm_PX1[of P2 i Q2] norm_PX2[of P2 i Q2])
  with 4 show ?case
    by (cases i) (simp, cases P2, auto, case_tac pol2, auto)
next
  case (5 P2 i Q2 c)
  then have "isnorm P2" "isnorm Q2"
    by (auto simp only: norm_PX1[of P2 i Q2] norm_PX2[of P2 i Q2])
  with 5 show ?case
    by (cases i) (simp, cases P2, auto, case_tac pol2, auto)
next
  case (6 x P2 y Q2)
  then have Y0: "y > 0"
    by (cases y) (auto simp add: norm_Pinj_0_False)
  with 6 have X0: "x > 0"
    by (cases x) (auto simp add: norm_Pinj_0_False)
  have "x < y \<or> x = y \<or> x > y" by arith
  moreover {
    assume "x < y"
    then have "\<exists>d. y = d + x" by arith
    then obtain d where y: "y = d + x" ..
    moreover
    note 6 X0
    moreover
    from 6 have "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    from 6 `x < y` y have "isnorm (Pinj d Q2)"
      by (cases d, simp, cases Q2, auto)
    ultimately have ?case by (simp add: mkPinj_cn)
  }
  moreover {
    assume "x = y"
    moreover
    from 6 have "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    note 6 Y0
    ultimately have ?case by (simp add: mkPinj_cn)
  }
  moreover {
    assume "x > y"
    then have "\<exists>d. x = d + y"
      by arith
    then obtain d where x: "x = d + y" ..
    moreover
    note 6 Y0
    moreover
    from 6 have "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    from 6 `x > y` x have "isnorm (Pinj d P2)"
      by (cases d) (simp, cases P2, auto)
    ultimately have ?case by (simp add: mkPinj_cn)
  }
  ultimately show ?case by blast
next
  case (7 x P2 Q2 y R)
  have "x = 0 \<or> x = 1 \<or> x > 1" by arith
  moreover {
    assume "x = 0"
    with 7 have ?case by (auto simp add: norm_Pinj_0_False)
  }
  moreover {
    assume "x = 1"
    from 7 have "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 7 `x = 1` have "isnorm (R \<oplus> P2)" by simp
    with 7 `x = 1` have ?case
      by (simp add: norm_PXtrans[of Q2 y _])
  }
  moreover {
    assume "x > 1" then have "\<exists>d. x=Suc (Suc d)" by arith
    then obtain d where X: "x=Suc (Suc d)" ..
    with 7 have NR: "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 7 X have "isnorm (Pinj (x - 1) P2)" by (cases P2) auto
    with 7 X NR have "isnorm (R \<oplus> Pinj (x - 1) P2)" by simp
    with `isnorm (PX Q2 y R)` X have ?case
      by (simp add: norm_PXtrans[of Q2 y _])
  }
  ultimately show ?case by blast
next
  case (8 Q2 y R x P2)
  have "x = 0 \<or> x = 1 \<or> x > 1" by arith
  moreover {
    assume "x = 0"
    with 8 have ?case
      by (auto simp add: norm_Pinj_0_False)
  }
  moreover {
    assume "x = 1"
    with 8 have "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 8 `x = 1` have "isnorm (R \<oplus> P2)"
      by simp
    with 8 `x = 1` have ?case
      by (simp add: norm_PXtrans[of Q2 y _])
  }
  moreover {
    assume "x > 1"
    then have "\<exists>d. x = Suc (Suc d)" by arith
    then obtain d where X: "x = Suc (Suc d)" ..
    with 8 have NR: "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 8 X have "isnorm (Pinj (x - 1) P2)"
      by (cases P2) auto
    with 8 `x > 1` NR have "isnorm (R \<oplus> Pinj (x - 1) P2)"
      by simp
    with `isnorm (PX Q2 y R)` X have ?case
      by (simp add: norm_PXtrans[of Q2 y _])
  }
  ultimately show ?case by blast
next
  case (9 P1 x P2 Q1 y Q2)
  then have Y0: "y > 0" by (cases y) auto
  with 9 have X0: "x > 0" by (cases x) auto
  with 9 have NP1: "isnorm P1" and NP2: "isnorm P2"
    by (auto simp add: norm_PX1[of P1 _ P2] norm_PX2[of P1 _ P2])
  with 9 have NQ1: "isnorm Q1" and NQ2: "isnorm Q2"
    by (auto simp add: norm_PX1[of Q1 _ Q2] norm_PX2[of Q1 _ Q2])
  have "y < x \<or> x = y \<or> x < y" by arith
  moreover {
    assume sm1: "y < x"
    then have "\<exists>d. x = d + y" by arith
    then obtain d where sm2: "x = d + y" ..
    note 9 NQ1 NP1 NP2 NQ2 sm1 sm2
    moreover
    have "isnorm (PX P1 d (Pc 0))"
    proof (cases P1)
      case (PX p1 y p2)
      with 9 sm1 sm2 show ?thesis
        by (cases d) (simp, cases p2, auto)
    next
      case Pc
      with 9 sm1 sm2 show ?thesis
        by (cases d) auto
    next
      case Pinj
      with 9 sm1 sm2 show ?thesis
        by (cases d) auto
    qed
    ultimately have "isnorm (P2 \<oplus> Q2)" "isnorm (PX P1 (x - y) (Pc 0) \<oplus> Q1)"
      by auto
    with Y0 sm1 sm2 have ?case
      by (simp add: mkPX_cn)
  }
  moreover {
    assume "x = y"
    with 9 NP1 NP2 NQ1 NQ2 have "isnorm (P2 \<oplus> Q2)" "isnorm (P1 \<oplus> Q1)"
      by auto
    with `x = y` Y0 have ?case
      by (simp add: mkPX_cn)
  }
  moreover {
    assume sm1: "x < y"
    then have "\<exists>d. y = d + x" by arith
    then obtain d where sm2: "y = d + x" ..
    note 9 NQ1 NP1 NP2 NQ2 sm1 sm2
    moreover
    have "isnorm (PX Q1 d (Pc 0))"
    proof (cases Q1)
      case (PX p1 y p2)
      with 9 sm1 sm2 show ?thesis
        by (cases d) (simp, cases p2, auto)
    next
      case Pc
      with 9 sm1 sm2 show ?thesis
        by (cases d) auto
    next
      case Pinj
      with 9 sm1 sm2 show ?thesis
        by (cases d) auto
    qed
    ultimately have "isnorm (P2 \<oplus> Q2)" "isnorm (PX Q1 (y - x) (Pc 0) \<oplus> P1)"
      by auto
    with X0 sm1 sm2 have ?case
      by (simp add: mkPX_cn)
  }
  ultimately show ?case by blast
qed simp

text {* mul concerves normalizedness *}
lemma mul_cn: "isnorm P \<Longrightarrow> isnorm Q \<Longrightarrow> isnorm (P \<otimes> Q)"
proof (induct P Q rule: mul.induct)
  case (2 c i P2)
  then show ?case
    by (cases P2) (simp_all, cases i, simp_all add: mkPinj_cn)
next
  case (3 i P2 c)
  then show ?case
    by (cases P2) (simp_all, cases i, simp_all add: mkPinj_cn)
next
  case (4 c P2 i Q2)
  then have "isnorm P2" "isnorm Q2"
    by (auto simp only: norm_PX1[of P2 i Q2] norm_PX2[of P2 i Q2])
  with 4 show ?case
    by (cases "c = 0") (simp_all, cases "i = 0", simp_all add: mkPX_cn)
next
  case (5 P2 i Q2 c)
  then have "isnorm P2" "isnorm Q2"
    by (auto simp only: norm_PX1[of P2 i Q2] norm_PX2[of P2 i Q2])
  with 5 show ?case
    by (cases "c = 0") (simp_all, cases "i = 0", simp_all add: mkPX_cn)
next
  case (6 x P2 y Q2)
  have "x < y \<or> x = y \<or> x > y" by arith
  moreover {
    assume "x < y"
    then have "\<exists>d. y = d + x" by arith
    then obtain d where y: "y = d + x" ..
    moreover
    note 6
    moreover
    from 6 have "x > 0"
      by (cases x) (auto simp add: norm_Pinj_0_False)
    moreover
    from 6 have "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    from 6 `x < y` y have "isnorm (Pinj d Q2)"
      by (cases d) (simp, cases Q2, auto)
    ultimately have ?case by (simp add: mkPinj_cn)
  }
  moreover {
    assume "x = y"
    moreover
    from 6 have "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    from 6 have "y>0"
      by (cases y) (auto simp add: norm_Pinj_0_False)
    moreover
    note 6
    ultimately have ?case by (simp add: mkPinj_cn)
  }
  moreover {
    assume "x > y"
    then have "\<exists>d. x = d + y" by arith
    then obtain d where x: "x = d + y" ..
    moreover
    note 6
    moreover
    from 6 have "y > 0"
      by (cases y) (auto simp add: norm_Pinj_0_False)
    moreover
    from 6 have "isnorm P2" "isnorm Q2"
      by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    from 6 `x > y` x have "isnorm (Pinj d P2)"
      by (cases d) (simp, cases P2, auto)
    ultimately have ?case by (simp add: mkPinj_cn)
  }
  ultimately show ?case by blast
next
  case (7 x P2 Q2 y R)
  then have Y0: "y > 0" by (cases y) auto
  have "x = 0 \<or> x = 1 \<or> x > 1" by arith
  moreover {
    assume "x = 0"
    with 7 have ?case
      by (auto simp add: norm_Pinj_0_False)
  }
  moreover {
    assume "x = 1"
    from 7 have "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 7 `x = 1` have "isnorm (R \<otimes> P2)" "isnorm Q2"
      by (auto simp add: norm_PX1[of Q2 y R])
    with 7 `x = 1` Y0 have ?case
      by (simp add: mkPX_cn)
  }
  moreover {
    assume "x > 1"
    then have "\<exists>d. x = Suc (Suc d)"
      by arith
    then obtain d where X: "x = Suc (Suc d)" ..
    from 7 have NR: "isnorm R" "isnorm Q2"
      by (auto simp add: norm_PX2[of Q2 y R] norm_PX1[of Q2 y R])
    moreover
    from 7 X have "isnorm (Pinj (x - 1) P2)"
      by (cases P2) auto
    moreover
    from 7 have "isnorm (Pinj x P2)"
      by (cases P2) auto
    moreover
    note 7 X
    ultimately have "isnorm (R \<otimes> Pinj (x - 1) P2)" "isnorm (Pinj x P2 \<otimes> Q2)"
      by auto
    with Y0 X have ?case
      by (simp add: mkPX_cn)
  }
  ultimately show ?case by blast
next
  case (8 Q2 y R x P2)
  then have Y0: "y > 0"
    by (cases y) auto
  have "x = 0 \<or> x = 1 \<or> x > 1" by arith
  moreover {
    assume "x = 0"
    with 8 have ?case
      by (auto simp add: norm_Pinj_0_False)
  }
  moreover {
    assume "x = 1"
    from 8 have "isnorm R" "isnorm P2"
      by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with 8 `x = 1` have "isnorm (R \<otimes> P2)" "isnorm Q2"
      by (auto simp add: norm_PX1[of Q2 y R])
    with 8 `x = 1` Y0 have ?case
      by (simp add: mkPX_cn)
  }
  moreover {
    assume "x > 1"
    then have "\<exists>d. x = Suc (Suc d)" by arith
    then obtain d where X: "x = Suc (Suc d)" ..
    from 8 have NR: "isnorm R" "isnorm Q2"
      by (auto simp add: norm_PX2[of Q2 y R] norm_PX1[of Q2 y R])
    moreover
    from 8 X have "isnorm (Pinj (x - 1) P2)"
      by (cases P2) auto
    moreover
    from 8 X have "isnorm (Pinj x P2)"
      by (cases P2) auto
    moreover
    note 8 X
    ultimately have "isnorm (R \<otimes> Pinj (x - 1) P2)" "isnorm (Pinj x P2 \<otimes> Q2)"
      by auto
    with Y0 X have ?case by (simp add: mkPX_cn)
  }
  ultimately show ?case by blast
next
  case (9 P1 x P2 Q1 y Q2)
  from 9 have X0: "x > 0" by (cases x) auto
  from 9 have Y0: "y > 0" by (cases y) auto
  note 9
  moreover
  from 9 have "isnorm P1" "isnorm P2"
    by (auto simp add: norm_PX1[of P1 x P2] norm_PX2[of P1 x P2])
  moreover
  from 9 have "isnorm Q1" "isnorm Q2"
    by (auto simp add: norm_PX1[of Q1 y Q2] norm_PX2[of Q1 y Q2])
  ultimately have "isnorm (P1 \<otimes> Q1)" "isnorm (P2 \<otimes> Q2)"
    "isnorm (P1 \<otimes> mkPinj 1 Q2)" "isnorm (Q1 \<otimes> mkPinj 1 P2)"
    by (auto simp add: mkPinj_cn)
  with 9 X0 Y0 have
    "isnorm (mkPX (P1 \<otimes> Q1) (x + y) (P2 \<otimes> Q2))"
    "isnorm (mkPX (P1 \<otimes> mkPinj (Suc 0) Q2) x (Pc 0))"
    "isnorm (mkPX (Q1 \<otimes> mkPinj (Suc 0) P2) y (Pc 0))"
    by (auto simp add: mkPX_cn)
  then show ?case by (simp add: add_cn)
qed simp

text {* neg conserves normalizedness *}
lemma neg_cn: "isnorm P \<Longrightarrow> isnorm (neg P)"
proof (induct P)
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
qed simp

text {* sub conserves normalizedness *}
lemma sub_cn: "isnorm p \<Longrightarrow> isnorm q \<Longrightarrow> isnorm (p \<ominus> q)"
  by (simp add: sub_def add_cn neg_cn)

text {* sqr conserves normalizizedness *}
lemma sqr_cn: "isnorm P \<Longrightarrow> isnorm (sqr P)"
proof (induct P)
  case Pc
  then show ?case by simp
next
  case (Pinj i Q)
  then show ?case
    by (cases Q) (auto simp add: mkPX_cn mkPinj_cn, cases i, auto simp add: mkPX_cn mkPinj_cn)
next
  case (PX P1 x P2)
  then have "x + x \<noteq> 0" "isnorm P2" "isnorm P1"
    by (cases x, auto simp add: norm_PX1[of P1 x P2] norm_PX2[of P1 x P2])
  with PX have "isnorm (mkPX (Pc (1 + 1) \<otimes> P1 \<otimes> mkPinj (Suc 0) P2) x (Pc 0))"
      and "isnorm (mkPX (sqr P1) (x + x) (sqr P2))"
    by (auto simp add: add_cn mkPX_cn mkPinj_cn mul_cn)
  then show ?case
    by (auto simp add: add_cn mkPX_cn mkPinj_cn mul_cn)
qed

text {* pow conserves normalizedness *}
lemma pow_cn: "isnorm P \<Longrightarrow> isnorm (pow n P)"
proof (induct n arbitrary: P rule: less_induct)
  case (less k)
  show ?case
  proof (cases "k = 0")
    case True
    then show ?thesis by simp
  next
    case False
    then have K2: "k div 2 < k" by (cases k) auto
    from less have "isnorm (sqr P)" by (simp add: sqr_cn)
    with less False K2 show ?thesis
      by (simp add: allE[of _ "(k div 2)" _] allE[of _ "(sqr P)" _], cases k, auto simp add: mul_cn)
  qed
qed

end
