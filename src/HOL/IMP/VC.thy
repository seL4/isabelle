(*  Title:      HOL/IMP/VC.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TUM

acom: annotated commands
vc:   verification-conditions
wp:   weakest (liberal) precondition
*)

VC  =  Hoare +

datatype  acom = Askip
               | Aass   loc aexp
               | Asemi  acom acom
               | Aif    bexp acom acom
               | Awhile bexp assn acom

consts
  vc,wp :: acom => assn => assn
  vcwp :: "acom => assn => assn * assn"
  astrip :: acom => com

primrec wp acom
  "wp Askip Q = Q"
  "wp (Aass x a) Q = (%s.Q(s[a s/x]))"
  "wp (Asemi c d) Q = wp c (wp d Q)"
  "wp (Aif b c d) Q = (%s. (b s-->wp c Q s) & (~b s-->wp d Q s))" 
  "wp (Awhile b I c) Q = I"

primrec vc acom
  "vc Askip Q = (%s.True)"
  "vc (Aass x a) Q = (%s.True)"
  "vc (Asemi c d) Q = (%s. vc c (wp d Q) s & vc d Q s)"
  "vc (Aif b c d) Q = (%s. vc c Q s & vc d Q s)" 
  "vc (Awhile b I c) Q = (%s. (I s & ~b s --> Q s) &
                              (I s & b s --> wp c I s) & vc c I s)"

primrec astrip acom
  "astrip Askip = SKIP"
  "astrip (Aass x a) = (x:=a)"
  "astrip (Asemi c d) = (astrip c;astrip d)"
  "astrip (Aif b c d) = (IF b THEN astrip c ELSE astrip d)"
  "astrip (Awhile b I c) = (WHILE b DO astrip c)"

(* simultaneous computation of vc and wp: *)
primrec vcwp acom
  "vcwp Askip Q = (%s.True, Q)"
  "vcwp (Aass x a) Q = (%s.True, %s.Q(s[a s/x]))"
  "vcwp (Asemi c d) Q = (let (vcd,wpd) = vcwp d Q;
                            (vcc,wpc) = vcwp c wpd
                         in (%s. vcc s & vcd s, wpc))"
  "vcwp (Aif b c d) Q = (let (vcd,wpd) = vcwp d Q;
                            (vcc,wpc) = vcwp c Q
                         in (%s. vcc s & vcd s,
                             %s.(b s-->wpc s) & (~b s-->wpd s)))"
  "vcwp (Awhile b I c) Q = (let (vcc,wpc) = vcwp c I
                            in (%s. (I s & ~b s --> Q s) &
                                    (I s & b s --> wpc s) & vcc s, I))"

end
