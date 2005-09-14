(*  ID:         $Id$
    Author:     Bernhard Haeupler

This theory is about of the relative completeness of method comm-ring
method.  As long as the reified atomic polynomials of type 'a pol are
in normal form, the cring method is complete.
*)

header {* Proof of the relative completeness of method comm-ring *}

theory Commutative_Ring_Complete
imports Main
begin
	
  (* Fromalization of normal form *)
consts isnorm :: "('a::{comm_ring,recpower}) pol \<Rightarrow> bool"
recdef isnorm "measure size"
  "isnorm (Pc c) = True"
  "isnorm (Pinj i (Pc c)) = False"
  "isnorm (Pinj i (Pinj j Q)) = False"
  "isnorm (Pinj 0 P) = False"
  "isnorm (Pinj i (PX Q1 j Q2)) = isnorm (PX Q1 j Q2)"
  "isnorm (PX P 0 Q) = False"
  "isnorm (PX (Pc c) i Q) = (c \<noteq> 0 & isnorm Q)"
  "isnorm (PX (PX P1 j (Pc c)) i Q) = (c\<noteq>0 \<and> isnorm(PX P1 j (Pc c))\<and>isnorm Q)"
  "isnorm (PX P i Q) = (isnorm P \<and> isnorm Q)"

(* Some helpful lemmas *)
lemma norm_Pinj_0_False:"isnorm (Pinj 0 P) = False"
by(cases P, auto)

lemma norm_PX_0_False:"isnorm (PX (Pc 0) i Q) = False"
by(cases i, auto)

lemma norm_Pinj:"isnorm (Pinj i Q) \<Longrightarrow> isnorm Q"
by(cases i,simp add: norm_Pinj_0_False norm_PX_0_False,cases Q) auto

lemma norm_PX2:"isnorm (PX P i Q) \<Longrightarrow> isnorm Q"
by(cases i, auto, cases P, auto, case_tac pol2, auto)

lemma norm_PX1:"isnorm (PX P i Q) \<Longrightarrow> isnorm P"
by(cases i, auto, cases P, auto, case_tac pol2, auto)

lemma mkPinj_cn:"\<lbrakk>y~=0; isnorm Q\<rbrakk> \<Longrightarrow> isnorm (mkPinj y Q)" 
apply(auto simp add: mkPinj_def norm_Pinj_0_False split: pol.split)
apply(case_tac nat, auto simp add: norm_Pinj_0_False)
by(case_tac pol, auto) (case_tac y, auto)

lemma norm_PXtrans: 
  assumes A:"isnorm (PX P x Q)" and "isnorm Q2" 
  shows "isnorm (PX P x Q2)"
proof(cases P)
  case (PX p1 y p2) from prems show ?thesis by(cases x, auto, cases p2, auto)
next
  case Pc from prems show ?thesis by(cases x, auto)
next
  case Pinj from prems show ?thesis by(cases x, auto)
qed
 

lemma norm_PXtrans2: assumes A:"isnorm (PX P x Q)" and "isnorm Q2" shows "isnorm (PX P (Suc (n+x)) Q2)"
proof(cases P)
  case (PX p1 y p2)
  from prems show ?thesis by(cases x, auto, cases p2, auto)
next
  case Pc
  from prems show ?thesis by(cases x, auto)
next
  case Pinj
  from prems show ?thesis by(cases x, auto)
qed

    (* mkPX conserves normalizedness (_cn)*)
lemma mkPX_cn: 
  assumes "x \<noteq> 0" and "isnorm P" and "isnorm Q" 
  shows "isnorm (mkPX P x Q)"
proof(cases P)
  case (Pc c)
  from prems show ?thesis by (cases x) (auto simp add: mkPinj_cn mkPX_def)
next
  case (Pinj i Q)
  from prems show ?thesis by (cases x) (auto simp add: mkPinj_cn mkPX_def)
next
  case (PX P1 y P2)
  from prems have Y0:"y>0" by(cases y, auto)
  from prems have "isnorm P1" "isnorm P2" by (auto simp add: norm_PX1[of P1 y P2] norm_PX2[of P1 y P2])
  with prems Y0 show ?thesis by (cases x, auto simp add: mkPX_def norm_PXtrans2[of P1 y _ Q _], cases P2, auto)
qed

    (* add conserves normalizedness *)
lemma add_cn:"\<lbrakk>isnorm P; (isnorm Q)\<rbrakk> \<Longrightarrow> isnorm (add (P, Q))"
proof(induct P Q rule: add.induct)
  case (2 c i P2) thus ?case by (cases P2, simp_all, cases i, simp_all)
next
  case (3 i P2 c) thus ?case by (cases P2, simp_all, cases i, simp_all)
next
  case (4 c P2 i Q2)
  from prems have "isnorm P2" "isnorm Q2" by (auto simp only: norm_PX1[of P2 i Q2] norm_PX2[of P2 i Q2])
  with prems show ?case by(cases i, simp, cases P2, auto, case_tac pol2, auto)
next
  case (5 P2 i Q2 c)
  from prems have "isnorm P2" "isnorm Q2" by (auto simp only: norm_PX1[of P2 i Q2] norm_PX2[of P2 i Q2])
  with prems show ?case by(cases i, simp, cases P2, auto, case_tac pol2, auto)
next
  case (6 x P2 y Q2)
  from prems have Y0:"y>0" by (cases y, auto simp add: norm_Pinj_0_False) 
  from prems have X0:"x>0" by (cases x, auto simp add: norm_Pinj_0_False) 
  have "x < y \<or> x = y \<or> x > y" by arith
  moreover
  { assume "x<y" hence "EX d. y=d+x" by arith
    then obtain d where "y=d+x"..
    moreover
    note prems X0
    moreover
    from prems have "isnorm P2" "isnorm Q2" by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    with prems have "isnorm (Pinj d Q2)" by (cases d, simp, cases Q2, auto)
    ultimately have ?case by (simp add: mkPinj_cn)}
  moreover
  { assume "x=y"
    moreover
    from prems have "isnorm P2" "isnorm Q2" by(auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    note prems Y0
    moreover
    ultimately have ?case by (simp add: mkPinj_cn) }
  moreover
  { assume "x>y" hence "EX d. x=d+y" by arith
    then obtain d where "x=d+y"..
    moreover
    note prems Y0
    moreover
    from prems have "isnorm P2" "isnorm Q2" by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    with prems have "isnorm (Pinj d P2)" by (cases d, simp, cases P2, auto)
    ultimately have ?case by (simp add: mkPinj_cn)}
  ultimately show ?case by blast
next
  case (7 x P2 Q2 y R)
  have "x=0 \<or> (x = 1) \<or> (x > 1)" by arith
  moreover
  { assume "x=0" with prems have ?case by (auto simp add: norm_Pinj_0_False)}
  moreover
  { assume "x=1"
    from prems have "isnorm R" "isnorm P2" by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with prems have "isnorm (add (R, P2))" by simp
    with prems have ?case by (simp add: norm_PXtrans[of Q2 y _]) }
  moreover
  { assume "x > 1" hence "EX d. x=Suc (Suc d)" by arith
    then obtain d where X:"x=Suc (Suc d)" ..
    from prems have NR:"isnorm R" "isnorm P2" by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with prems have "isnorm (Pinj (x - 1) P2)" by(cases P2, auto)
    with prems NR have "isnorm( add (R, Pinj (x - 1) P2))" "isnorm(PX Q2 y R)" by simp
    with X have ?case by (simp add: norm_PXtrans[of Q2 y _]) }
  ultimately show ?case by blast
next
  case (8 Q2 y R x P2)
  have "x=0 \<or> (x = 1) \<or> (x > 1)" by arith
  moreover
  { assume "x=0" with prems have ?case by (auto simp add: norm_Pinj_0_False)}
  moreover
  { assume "x=1"
    from prems have "isnorm R" "isnorm P2" by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with prems have "isnorm (add (R, P2))" by simp
    with prems have ?case by (simp add: norm_PXtrans[of Q2 y _]) }
  moreover
  { assume "x > 1" hence "EX d. x=Suc (Suc d)" by arith
    then obtain d where X:"x=Suc (Suc d)" ..
    from prems have NR:"isnorm R" "isnorm P2" by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with prems have "isnorm (Pinj (x - 1) P2)" by(cases P2, auto)
    with prems NR have "isnorm( add (R, Pinj (x - 1) P2))" "isnorm(PX Q2 y R)" by simp
    with X have ?case by (simp add: norm_PXtrans[of Q2 y _]) }
  ultimately show ?case by blast
next
  case (9 P1 x P2 Q1 y Q2)
  from prems have Y0:"y>0" by(cases y, auto)
  from prems have X0:"x>0" by(cases x, auto)
  from prems have NP1:"isnorm P1" and NP2:"isnorm P2" by (auto simp add: norm_PX1[of P1 _ P2] norm_PX2[of P1 _ P2])
  from prems have NQ1:"isnorm Q1" and NQ2:"isnorm Q2" by (auto simp add: norm_PX1[of Q1 _ Q2] norm_PX2[of Q1 _ Q2])
  have "y < x \<or> x = y \<or> x < y" by arith
  moreover
  {assume sm1:"y < x" hence "EX d. x=d+y" by arith
    then obtain d where sm2:"x=d+y"..
    note prems NQ1 NP1 NP2 NQ2 sm1 sm2
    moreover
    have "isnorm (PX P1 d (Pc 0))" 
    proof(cases P1)
      case (PX p1 y p2)
      with prems show ?thesis by(cases d, simp,cases p2, auto)
    next case Pc   from prems show ?thesis by(cases d, auto)
    next case Pinj from prems show ?thesis by(cases d, auto)
    qed
    ultimately have "isnorm (add (P2, Q2))" "isnorm (add (PX P1 (x - y) (Pc 0), Q1))" by auto
    with Y0 sm1 sm2 have ?case by (simp add: mkPX_cn)}
  moreover
  {assume "x=y"
    from prems NP1 NP2 NQ1 NQ2 have "isnorm (add (P2, Q2))" "isnorm (add (P1, Q1))" by auto
    with Y0 prems have ?case by (simp add: mkPX_cn) }
  moreover
  {assume sm1:"x<y" hence "EX d. y=d+x" by arith
    then obtain d where sm2:"y=d+x"..
    note prems NQ1 NP1 NP2 NQ2 sm1 sm2
    moreover
    have "isnorm (PX Q1 d (Pc 0))" 
    proof(cases Q1)
      case (PX p1 y p2)
      with prems show ?thesis by(cases d, simp,cases p2, auto)
    next case Pc   from prems show ?thesis by(cases d, auto)
    next case Pinj from prems show ?thesis by(cases d, auto)
    qed
    ultimately have "isnorm (add (P2, Q2))" "isnorm (add (PX Q1 (y - x) (Pc 0), P1))" by auto
    with X0 sm1 sm2 have ?case by (simp add: mkPX_cn)}
  ultimately show ?case by blast
qed(simp)

    (* mul concerves normalizedness *)
lemma mul_cn :"\<lbrakk>isnorm P; (isnorm Q)\<rbrakk> \<Longrightarrow> isnorm (mul (P, Q))"
proof(induct P Q rule: mul.induct)
  case (2 c i P2) thus ?case 
    by (cases P2, simp_all) (cases "i",simp_all add: mkPinj_cn)
next
  case (3 i P2 c) thus ?case 
    by (cases P2, simp_all) (cases "i",simp_all add: mkPinj_cn)
next
  case (4 c P2 i Q2)
  from prems have "isnorm P2" "isnorm Q2" by (auto simp only: norm_PX1[of P2 i Q2] norm_PX2[of P2 i Q2])
  with prems show ?case 
    by - (case_tac "c=0",simp_all,case_tac "i=0",simp_all add: mkPX_cn)
next
  case (5 P2 i Q2 c)
  from prems have "isnorm P2" "isnorm Q2" by (auto simp only: norm_PX1[of P2 i Q2] norm_PX2[of P2 i Q2])
  with prems show ?case
    by - (case_tac "c=0",simp_all,case_tac "i=0",simp_all add: mkPX_cn)
next
  case (6 x P2 y Q2)
  have "x < y \<or> x = y \<or> x > y" by arith
  moreover
  { assume "x<y" hence "EX d. y=d+x" by arith
    then obtain d where "y=d+x"..
    moreover
    note prems
    moreover
    from prems have "x>0" by (cases x, auto simp add: norm_Pinj_0_False) 
    moreover
    from prems have "isnorm P2" "isnorm Q2" by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    with prems have "isnorm (Pinj d Q2)" by (cases d, simp, cases Q2, auto) 
    ultimately have ?case by (simp add: mkPinj_cn)}
  moreover
  { assume "x=y"
    moreover
    from prems have "isnorm P2" "isnorm Q2" by(auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    with prems have "y>0" by (cases y, auto simp add: norm_Pinj_0_False)
    moreover
    note prems
    moreover
    ultimately have ?case by (simp add: mkPinj_cn) }
  moreover
  { assume "x>y" hence "EX d. x=d+y" by arith
    then obtain d where "x=d+y"..
    moreover
    note prems
    moreover
    from prems have "y>0" by (cases y, auto simp add: norm_Pinj_0_False) 
    moreover
    from prems have "isnorm P2" "isnorm Q2" by (auto simp add: norm_Pinj[of _ P2] norm_Pinj[of _ Q2])
    moreover
    with prems have "isnorm (Pinj d P2)"  by (cases d, simp, cases P2, auto)
    ultimately have ?case by (simp add: mkPinj_cn) }
  ultimately show ?case by blast
next
  case (7 x P2 Q2 y R)
  from prems have Y0:"y>0" by(cases y, auto)
  have "x=0 \<or> (x = 1) \<or> (x > 1)" by arith
  moreover
  { assume "x=0" with prems have ?case by (auto simp add: norm_Pinj_0_False)}
  moreover
  { assume "x=1"
    from prems have "isnorm R" "isnorm P2" by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with prems have "isnorm (mul (R, P2))" "isnorm Q2" by (auto simp add: norm_PX1[of Q2 y R])
    with Y0 prems have ?case by (simp add: mkPX_cn)}
  moreover
  { assume "x > 1" hence "EX d. x=Suc (Suc d)" by arith
    then obtain d where X:"x=Suc (Suc d)" ..
    from prems have NR:"isnorm R" "isnorm Q2" by (auto simp add: norm_PX2[of Q2 y R] norm_PX1[of Q2 y R])
    moreover
    from prems have "isnorm (Pinj (x - 1) P2)" by(cases P2, auto)
    moreover
    from prems have "isnorm (Pinj x P2)" by(cases P2, auto)
    moreover
    note prems
    ultimately have "isnorm (mul (R, Pinj (x - 1) P2))" "isnorm (mul (Pinj x P2, Q2))" by auto
    with Y0 X have ?case by (simp add: mkPX_cn)}
  ultimately show ?case by blast
next
  case (8 Q2 y R x P2)
  from prems have Y0:"y>0" by(cases y, auto)
  have "x=0 \<or> (x = 1) \<or> (x > 1)" by arith
  moreover
  { assume "x=0" with prems have ?case by (auto simp add: norm_Pinj_0_False)}
  moreover
  { assume "x=1"
    from prems have "isnorm R" "isnorm P2" by (auto simp add: norm_Pinj[of _ P2] norm_PX2[of Q2 y R])
    with prems have "isnorm (mul (R, P2))" "isnorm Q2" by (auto simp add: norm_PX1[of Q2 y R])
    with Y0 prems have ?case by (simp add: mkPX_cn) }
  moreover
  { assume "x > 1" hence "EX d. x=Suc (Suc d)" by arith
    then obtain d where X:"x=Suc (Suc d)" ..
    from prems have NR:"isnorm R" "isnorm Q2" by (auto simp add: norm_PX2[of Q2 y R] norm_PX1[of Q2 y R])
    moreover
    from prems have "isnorm (Pinj (x - 1) P2)" by(cases P2, auto)
    moreover
    from prems have "isnorm (Pinj x P2)" by(cases P2, auto)
    moreover
    note prems
    ultimately have "isnorm (mul (R, Pinj (x - 1) P2))" "isnorm (mul (Pinj x P2, Q2))" by auto
    with Y0 X have ?case by (simp add: mkPX_cn) }
  ultimately show ?case by blast
next
  case (9 P1 x P2 Q1 y Q2)
  from prems have X0:"x>0" by(cases x, auto)
  from prems have Y0:"y>0" by(cases y, auto)
  note prems
  moreover
  from prems have "isnorm P1" "isnorm P2" by (auto simp add: norm_PX1[of P1 x P2] norm_PX2[of P1 x P2])
  moreover 
  from prems have "isnorm Q1" "isnorm Q2" by (auto simp add: norm_PX1[of Q1 y Q2] norm_PX2[of Q1 y Q2])
  ultimately have "isnorm (mul (P1, Q1))" "isnorm (mul (P2, Q2))" "isnorm (mul (P1, mkPinj 1 Q2))" "isnorm (mul (Q1, mkPinj 1 P2))" 
    by (auto simp add: mkPinj_cn)
  with prems X0 Y0 have "isnorm (mkPX (mul (P1, Q1)) (x + y) (mul (P2, Q2)))" "isnorm (mkPX (mul (P1, mkPinj (Suc 0) Q2)) x (Pc 0))"  
    "isnorm (mkPX (mul (Q1, mkPinj (Suc 0) P2)) y (Pc 0))" 
    by (auto simp add: mkPX_cn)
  thus ?case by (simp add: add_cn)
qed(simp)

    (* neg conserves normalizedness *)
lemma neg_cn: "isnorm P \<Longrightarrow> isnorm (neg P)"
proof(induct P rule: neg.induct)
  case (Pinj i P2)
  from prems have "isnorm P2" by (simp add: norm_Pinj[of i P2])
  with prems show ?case by(cases P2, auto, cases i, auto)
next
  case (PX P1 x P2)
  from prems have "isnorm P2" "isnorm P1" by (auto simp add: norm_PX1[of P1 x P2] norm_PX2[of P1 x P2])
  with prems show ?case
  proof(cases P1)
    case (PX p1 y p2)
    with prems show ?thesis by(cases x, auto, cases p2, auto)
  next
    case Pinj
    with prems show ?thesis by(cases x, auto)
  qed(cases x, auto)
qed(simp)

    (* sub conserves normalizedness *)
lemma sub_cn:"\<lbrakk>isnorm p; isnorm q\<rbrakk> \<Longrightarrow> isnorm (sub p q)"
by (simp add: sub_def add_cn neg_cn)

  (* sqr conserves normalizizedness *)
lemma sqr_cn:"isnorm P \<Longrightarrow> isnorm (sqr P)"
proof(induct P)
  case (Pinj i Q)
  from prems show ?case by(cases Q, auto simp add: mkPX_cn mkPinj_cn, cases i, auto simp add: mkPX_cn mkPinj_cn)
next 
  case (PX P1 x P2)
  from prems have "x+x~=0" "isnorm P2" "isnorm P1" by (cases x,  auto simp add: norm_PX1[of P1 x P2] norm_PX2[of P1 x P2])
  with prems have "isnorm (mkPX (mul (mul (Pc ((1\<Colon>'a) + (1\<Colon>'a)), P1), mkPinj (Suc 0) P2)) x (Pc (0\<Colon>'a)))"
              and "isnorm (mkPX (sqr P1) (x + x) (sqr P2))" by( auto simp add: add_cn mkPX_cn mkPinj_cn mul_cn)
  thus ?case by( auto simp add: add_cn mkPX_cn mkPinj_cn mul_cn)
qed(simp)


    (* pow conserves normalizedness  *)
lemma pow_cn:"!! P. \<lbrakk>isnorm P\<rbrakk> \<Longrightarrow> isnorm (pow (P, n))"
proof(induct n rule: nat_less_induct)
  case (1 k)
  show ?case 
  proof(cases "k=0")
    case False
    hence K2:"k div 2 < k" by (cases k, auto)
    from prems have "isnorm (sqr P)" by (simp add: sqr_cn)
    with prems K2 show ?thesis by(simp add: allE[of _ "(k div 2)" _] allE[of _ "(sqr P)" _], cases k, auto simp add: mul_cn)
  qed(simp)
qed

end
