(*  Title: 	HOL/IMP/VC.thy
    ID:         $Id$
    Author: 	Tobias Nipkow
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
  astrip :: acom => com

primrec wp acom
  wp_Askip  "wp Askip Q = Q"
  wp_Aass   "wp (Aass x a) Q = (%s.Q(s[A a s/x]))"
  wp_Asemi  "wp (Asemi c d) Q = wp c (wp d Q)"
  wp_Aif    "wp (Aif b c d) Q = (%s. (B b s-->wp c Q s)&(~B b s-->wp d Q s))" 
  wp_Awhile "wp (Awhile b I c) Q = I"

primrec vc acom
  vc_Askip  "vc Askip Q = (%s.True)"
  vc_Aass   "vc (Aass x a) Q = (%s.True)"
  vc_Asemi  "vc (Asemi c d) Q = (%s. vc c (wp d Q) s & vc d Q s)"
  vc_Aif    "vc (Aif b c d) Q = (%s. vc c Q s & vc d Q s)" 
  vc_Awhile "vc (Awhile b I c) Q = (%s. (I s & ~B b s --> Q s) &
                              (I s & B b s --> wp c I s) & vc c I s)"

primrec astrip acom
  astrip_Askip  "astrip Askip = skip"
  astrip_Aass   "astrip (Aass x a) = (x:=a)"
  astrip_Asemi  "astrip (Asemi c d) = (astrip c;astrip d)"
  astrip_Aif    "astrip (Aif b c d) = ifC b (astrip c) (astrip d)"
  astrip_Awhile "astrip (Awhile b I c) = whileC b (astrip c)"
  
end
