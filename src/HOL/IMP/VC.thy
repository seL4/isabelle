(*  Title:      HOL/IMP/VC.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TUM

acom: annotated commands
vc:   verification-conditions
awp:   weakest (liberal) precondition
*)

VC  =  Hoare +

datatype  acom = Askip
               | Aass   loc aexp
               | Asemi  acom acom
               | Aif    bexp acom acom
               | Awhile bexp assn acom

consts
  vc,awp :: acom => assn => assn
  vcawp :: "acom => assn => assn * assn"
  astrip :: acom => com

primrec awp acom
  "awp Askip Q = Q"
  "awp (Aass x a) Q = (%s. Q(s[x:=a s]))"
  "awp (Asemi c d) Q = awp c (awp d Q)"
  "awp (Aif b c d) Q = (%s. (b s-->awp c Q s) & (~b s-->awp d Q s))" 
  "awp (Awhile b I c) Q = I"

primrec vc acom
  "vc Askip Q = (%s. True)"
  "vc (Aass x a) Q = (%s. True)"
  "vc (Asemi c d) Q = (%s. vc c (awp d Q) s & vc d Q s)"
  "vc (Aif b c d) Q = (%s. vc c Q s & vc d Q s)" 
  "vc (Awhile b I c) Q = (%s. (I s & ~b s --> Q s) &
                              (I s & b s --> awp c I s) & vc c I s)"

primrec astrip acom
  "astrip Askip = SKIP"
  "astrip (Aass x a) = (x:=a)"
  "astrip (Asemi c d) = (astrip c;astrip d)"
  "astrip (Aif b c d) = (IF b THEN astrip c ELSE astrip d)"
  "astrip (Awhile b I c) = (WHILE b DO astrip c)"

(* simultaneous computation of vc and awp: *)
primrec vcawp acom
  "vcawp Askip Q = (%s. True, Q)"
  "vcawp (Aass x a) Q = (%s. True, %s. Q(s[x:=a s]))"
  "vcawp (Asemi c d) Q = (let (vcd,wpd) = vcawp d Q;
                              (vcc,wpc) = vcawp c wpd
                          in (%s. vcc s & vcd s, wpc))"
  "vcawp (Aif b c d) Q = (let (vcd,wpd) = vcawp d Q;
                              (vcc,wpc) = vcawp c Q
                          in (%s. vcc s & vcd s,
                              %s.(b s --> wpc s) & (~b s --> wpd s)))"
  "vcawp (Awhile b I c) Q = (let (vcc,wpc) = vcawp c I
                             in (%s. (I s & ~b s --> Q s) &
                                     (I s & b s --> wpc s) & vcc s, I))"

end
