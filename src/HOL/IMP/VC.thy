(*  Title:      HOL/IMP/VC.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1996 TUM

acom: annotated commands
vc:   verification-conditions
awp:   weakest (liberal) precondition
*)

header "Verification Conditions"

theory VC = Hoare:

datatype  acom = Askip
               | Aass   loc aexp
               | Asemi  acom acom
               | Aif    bexp acom acom
               | Awhile bexp assn acom

consts
  vc :: "acom => assn => assn"
  awp :: "acom => assn => assn"
  vcawp :: "acom => assn => assn \<times> assn"
  astrip :: "acom => com"

primrec
  "awp Askip Q = Q"
  "awp (Aass x a) Q = (\<lambda>s. Q(s[x\<mapsto>a s]))"
  "awp (Asemi c d) Q = awp c (awp d Q)"
  "awp (Aif b c d) Q = (\<lambda>s. (b s-->awp c Q s) & (~b s-->awp d Q s))" 
  "awp (Awhile b I c) Q = I"

primrec
  "vc Askip Q = (\<lambda>s. True)"
  "vc (Aass x a) Q = (\<lambda>s. True)"
  "vc (Asemi c d) Q = (\<lambda>s. vc c (awp d Q) s & vc d Q s)"
  "vc (Aif b c d) Q = (\<lambda>s. vc c Q s & vc d Q s)" 
  "vc (Awhile b I c) Q = (\<lambda>s. (I s & ~b s --> Q s) &
                              (I s & b s --> awp c I s) & vc c I s)"

primrec
  "astrip Askip = SKIP"
  "astrip (Aass x a) = (x:==a)"
  "astrip (Asemi c d) = (astrip c;astrip d)"
  "astrip (Aif b c d) = (\<IF> b \<THEN> astrip c \<ELSE> astrip d)"
  "astrip (Awhile b I c) = (\<WHILE> b \<DO> astrip c)"

(* simultaneous computation of vc and awp: *)
primrec
  "vcawp Askip Q = (\<lambda>s. True, Q)"
  "vcawp (Aass x a) Q = (\<lambda>s. True, \<lambda>s. Q(s[x\<mapsto>a s]))"
  "vcawp (Asemi c d) Q = (let (vcd,wpd) = vcawp d Q;
                              (vcc,wpc) = vcawp c wpd
                          in (\<lambda>s. vcc s & vcd s, wpc))"
  "vcawp (Aif b c d) Q = (let (vcd,wpd) = vcawp d Q;
                              (vcc,wpc) = vcawp c Q
                          in (\<lambda>s. vcc s & vcd s,
                              \<lambda>s.(b s --> wpc s) & (~b s --> wpd s)))"
  "vcawp (Awhile b I c) Q = (let (vcc,wpc) = vcawp c I
                             in (\<lambda>s. (I s & ~b s --> Q s) &
                                     (I s & b s --> wpc s) & vcc s, I))"

(*
Soundness and completeness of vc
*)

declare hoare.intros [intro]

lemma l: "!s. P s --> P s" by fast

lemma vc_sound: "!Q. (!s. vc c Q s) --> |- {awp c Q} astrip c {Q}"
apply (induct_tac "c")
    apply (simp_all (no_asm))
    apply fast
   apply fast
  apply fast
 (* if *)
 apply (tactic "Deepen_tac 4 1")
(* while *)
apply (intro allI impI) 
apply (rule conseq)
  apply (rule l)
 apply (rule While)
 defer
 apply fast
apply (rule_tac P="awp acom fun2" in conseq)
  apply fast
 apply fast
apply fast
done

lemma awp_mono [rule_format (no_asm)]: "!P Q. (!s. P s --> Q s) --> (!s. awp c P s --> awp c Q s)"
apply (induct_tac "c")
    apply (simp_all (no_asm_simp))
apply (rule allI, rule allI, rule impI)
apply (erule allE, erule allE, erule mp)
apply (erule allE, erule allE, erule mp, assumption)
done


lemma vc_mono [rule_format (no_asm)]: "!P Q. (!s. P s --> Q s) --> (!s. vc c P s --> vc c Q s)"
apply (induct_tac "c")
    apply (simp_all (no_asm_simp))
apply safe
apply (erule allE,erule allE,erule impE,erule_tac [2] allE,erule_tac [2] mp) 
prefer 2 apply assumption
apply (fast elim: awp_mono)
done

lemma vc_complete: "|- {P}c{Q} ==>  
   (? ac. astrip ac = c & (!s. vc ac Q s) & (!s. P s --> awp ac Q s))"
apply (erule hoare.induct)
     apply (rule_tac x = "Askip" in exI)
     apply (simp (no_asm))
    apply (rule_tac x = "Aass x a" in exI)
    apply (simp (no_asm))
   apply clarify
   apply (rule_tac x = "Asemi ac aca" in exI)
   apply (simp (no_asm_simp))
   apply (fast elim!: awp_mono vc_mono)
  apply clarify
  apply (rule_tac x = "Aif b ac aca" in exI)
  apply (simp (no_asm_simp))
 apply clarify
 apply (rule_tac x = "Awhile b P ac" in exI)
 apply (simp (no_asm_simp))
apply safe
apply (rule_tac x = "ac" in exI)
apply (simp (no_asm_simp))
apply (fast elim!: awp_mono vc_mono)
done

lemma vcawp_vc_awp: "!Q. vcawp c Q = (vc c Q, awp c Q)"
apply (induct_tac "c")
apply (simp_all (no_asm_simp) add: Let_def)
done

end
