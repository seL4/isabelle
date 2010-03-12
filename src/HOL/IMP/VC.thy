(*  Title:      HOL/IMP/VC.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TUM

acom: annotated commands
vc:   verification-conditions
awp:   weakest (liberal) precondition
*)

header "Verification Conditions"

theory VC imports Hoare_Op begin

datatype  acom = Askip
               | Aass   loc aexp
               | Asemi  acom acom
               | Aif    bexp acom acom
               | Awhile bexp assn acom

primrec awp :: "acom => assn => assn"
where
  "awp Askip Q = Q"
| "awp (Aass x a) Q = (\<lambda>s. Q(s[x\<mapsto>a s]))"
| "awp (Asemi c d) Q = awp c (awp d Q)"
| "awp (Aif b c d) Q = (\<lambda>s. (b s-->awp c Q s) & (~b s-->awp d Q s))"
| "awp (Awhile b I c) Q = I"

primrec vc :: "acom => assn => assn"
where
  "vc Askip Q = (\<lambda>s. True)"
| "vc (Aass x a) Q = (\<lambda>s. True)"
| "vc (Asemi c d) Q = (\<lambda>s. vc c (awp d Q) s & vc d Q s)"
| "vc (Aif b c d) Q = (\<lambda>s. vc c Q s & vc d Q s)"
| "vc (Awhile b I c) Q = (\<lambda>s. (I s & ~b s --> Q s) &
                              (I s & b s --> awp c I s) & vc c I s)"

primrec astrip :: "acom => com"
where
  "astrip Askip = SKIP"
| "astrip (Aass x a) = (x:==a)"
| "astrip (Asemi c d) = (astrip c;astrip d)"
| "astrip (Aif b c d) = (\<IF> b \<THEN> astrip c \<ELSE> astrip d)"
| "astrip (Awhile b I c) = (\<WHILE> b \<DO> astrip c)"

(* simultaneous computation of vc and awp: *)
primrec vcawp :: "acom => assn => assn \<times> assn"
where
  "vcawp Askip Q = (\<lambda>s. True, Q)"
| "vcawp (Aass x a) Q = (\<lambda>s. True, \<lambda>s. Q(s[x\<mapsto>a s]))"
| "vcawp (Asemi c d) Q = (let (vcd,wpd) = vcawp d Q;
                              (vcc,wpc) = vcawp c wpd
                          in (\<lambda>s. vcc s & vcd s, wpc))"
| "vcawp (Aif b c d) Q = (let (vcd,wpd) = vcawp d Q;
                              (vcc,wpc) = vcawp c Q
                          in (\<lambda>s. vcc s & vcd s,
                              \<lambda>s.(b s --> wpc s) & (~b s --> wpd s)))"
| "vcawp (Awhile b I c) Q = (let (vcc,wpc) = vcawp c I
                             in (\<lambda>s. (I s & ~b s --> Q s) &
                                     (I s & b s --> wpc s) & vcc s, I))"

(*
Soundness and completeness of vc
*)

declare hoare.conseq [intro]


lemma vc_sound: "(ALL s. vc c Q s) \<Longrightarrow> |- {awp c Q} astrip c {Q}"
proof(induct c arbitrary: Q)
  case (Awhile b I c)
  show ?case
  proof(simp, rule While')
    from `\<forall>s. vc (Awhile b I c) Q s`
    have vc: "ALL s. vc c I s" and IQ: "ALL s. I s \<and> \<not> b s \<longrightarrow> Q s" and
         awp: "ALL s. I s & b s --> awp c I s" by simp_all
    from vc have "|- {awp c I} astrip c {I}" using Awhile.hyps by blast
    with awp show "|- {\<lambda>s. I s \<and> b s} astrip c {I}"
      by(rule strengthen_pre)
    show "\<forall>s. I s \<and> \<not> b s \<longrightarrow> Q s" by(rule IQ)
  qed
qed auto


lemma awp_mono:
  "(!s. P s --> Q s) ==> awp c P s ==> awp c Q s"
proof (induct c arbitrary: P Q s)
  case Asemi thus ?case by simp metis
qed simp_all

lemma vc_mono:
  "(!s. P s --> Q s) ==> vc c P s ==> vc c Q s"
proof(induct c arbitrary: P Q)
  case Asemi thus ?case by simp (metis awp_mono)
qed simp_all

lemma vc_complete: assumes der: "|- {P}c{Q}"
  shows "(\<exists>ac. astrip ac = c & (\<forall>s. vc ac Q s) & (\<forall>s. P s --> awp ac Q s))"
  (is "? ac. ?Eq P c Q ac")
using der
proof induct
  case skip
  show ?case (is "? ac. ?C ac")
  proof show "?C Askip" by simp qed
next
  case (ass P x a)
  show ?case (is "? ac. ?C ac")
  proof show "?C(Aass x a)" by simp qed
next
  case (semi P c1 Q c2 R)
  from semi.hyps obtain ac1 where ih1: "?Eq P c1 Q ac1" by fast
  from semi.hyps obtain ac2 where ih2: "?Eq Q c2 R ac2" by fast
  show ?case (is "? ac. ?C ac")
  proof
    show "?C(Asemi ac1 ac2)"
      using ih1 ih2 by simp (fast elim!: awp_mono vc_mono)
  qed
next
  case (If P b c1 Q c2)
  from If.hyps obtain ac1 where ih1: "?Eq (%s. P s & b s) c1 Q ac1" by fast
  from If.hyps obtain ac2 where ih2: "?Eq (%s. P s & ~b s) c2 Q ac2" by fast
  show ?case (is "? ac. ?C ac")
  proof
    show "?C(Aif b ac1 ac2)"
      using ih1 ih2 by simp
  qed
next
  case (While P b c)
  from While.hyps obtain ac where ih: "?Eq (%s. P s & b s) c P ac" by fast
  show ?case (is "? ac. ?C ac")
  proof show "?C(Awhile b P ac)" using ih by simp qed
next
  case conseq thus ?case by(fast elim!: awp_mono vc_mono)
qed

lemma vcawp_vc_awp: "vcawp c Q = (vc c Q, awp c Q)"
  by (induct c arbitrary: Q) (simp_all add: Let_def)

end
