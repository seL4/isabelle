(*  Title:      HOL/IMP/Hoare.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1995 TUM
*)

header "Inductive Definition of Hoare Logic"

theory Hoare = Denotation:

types assn = "state => bool"

constdefs hoare_valid :: "[assn,com,assn] => bool" ("|= {(1_)}/ (_)/ {(1_)}" 50)
          "|= {P}c{Q} == !s t. (s,t) : C(c) --> P s --> Q t"

consts hoare :: "(assn * com * assn) set"
syntax "@hoare" :: "[bool,com,bool] => bool" ("|- ({(1_)}/ (_)/ {(1_)})" 50)
translations "|- {P}c{Q}" == "(P,c,Q) : hoare"

inductive hoare
intros
  skip: "|- {P}\<SKIP>{P}"
  ass:  "|- {%s. P(s[x\<mapsto>a s])} x:==a {P}"
  semi: "[| |- {P}c{Q}; |- {Q}d{R} |] ==> |- {P} c;d {R}"
  If: "[| |- {%s. P s & b s}c{Q}; |- {%s. P s & ~b s}d{Q} |] ==>
      |- {P} \<IF> b \<THEN> c \<ELSE> d {Q}"
  While: "|- {%s. P s & b s} c {P} ==>
         |- {P} \<WHILE> b \<DO> c {%s. P s & ~b s}"
  conseq: "[| !s. P' s --> P s; |- {P}c{Q}; !s. Q s --> Q' s |] ==>
          |- {P'}c{Q'}"

constdefs wp :: "com => assn => assn"
          "wp c Q == (%s. !t. (s,t) : C(c) --> Q t)"

(*  
Soundness (and part of) relative completeness of Hoare rules
wrt denotational semantics
*)

lemma hoare_conseq1: "[| !s. P' s --> P s; |- {P}c{Q} |] ==> |- {P'}c{Q}"
apply (erule hoare.conseq)
apply  assumption
apply fast
done

lemma hoare_conseq2: "[| |- {P}c{Q}; !s. Q s --> Q' s |] ==> |- {P}c{Q'}"
apply (rule hoare.conseq)
prefer 2 apply    (assumption)
apply fast
apply fast
done

lemma hoare_sound: "|- {P}c{Q} ==> |= {P}c{Q}"
apply (unfold hoare_valid_def)
apply (erule hoare.induct)
     apply (simp_all (no_asm_simp))
  apply fast
 apply fast
apply (rule allI, rule allI, rule impI)
apply (erule lfp_induct2)
 apply (rule Gamma_mono)
apply (unfold Gamma_def)
apply fast
done

lemma wp_SKIP: "wp \<SKIP> Q = Q"
apply (unfold wp_def)
apply (simp (no_asm))
done

lemma wp_Ass: "wp (x:==a) Q = (%s. Q(s[x\<mapsto>a s]))"
apply (unfold wp_def)
apply (simp (no_asm))
done

lemma wp_Semi: "wp (c;d) Q = wp c (wp d Q)"
apply (unfold wp_def)
apply (simp (no_asm))
apply (rule ext)
apply fast
done

lemma wp_If: 
 "wp (\<IF> b \<THEN> c \<ELSE> d) Q = (%s. (b s --> wp c Q s) &  (~b s --> wp d Q s))"
apply (unfold wp_def)
apply (simp (no_asm))
apply (rule ext)
apply fast
done

lemma wp_While_True: 
  "b s ==> wp (\<WHILE> b \<DO> c) Q s = wp (c;\<WHILE> b \<DO> c) Q s"
apply (unfold wp_def)
apply (subst C_While_If)
apply (simp (no_asm_simp))
done

lemma wp_While_False: "~b s ==> wp (\<WHILE> b \<DO> c) Q s = Q s"
apply (unfold wp_def)
apply (subst C_While_If)
apply (simp (no_asm_simp))
done

lemmas [simp] = wp_SKIP wp_Ass wp_Semi wp_If wp_While_True wp_While_False

(*Not suitable for rewriting: LOOPS!*)
lemma wp_While_if: 
  "wp (\<WHILE> b \<DO> c) Q s = (if b s then wp (c;\<WHILE> b \<DO> c) Q s else Q s)"
apply (simp (no_asm))
done

lemma wp_While: "wp (\<WHILE> b \<DO> c) Q s =  
   (s : gfp(%S.{s. if b s then wp c (%s. s:S) s else Q s}))"
apply (simp (no_asm))
apply (rule iffI)
 apply (rule weak_coinduct)
  apply (erule CollectI)
 apply safe
  apply (rotate_tac -1)
  apply simp
 apply (rotate_tac -1)
 apply simp
apply (simp add: wp_def Gamma_def)
apply (intro strip)
apply (rule mp)
 prefer 2 apply (assumption)
apply (erule lfp_induct2)
apply (fast intro!: monoI)
apply (subst gfp_unfold)
 apply (fast intro!: monoI)
apply fast
done

declare C_while [simp del]

lemmas [intro!] = hoare.skip hoare.ass hoare.semi hoare.If 

lemma wp_is_pre [rule_format (no_asm)]: "!Q. |- {wp c Q} c {Q}"
apply (induct_tac "c")
    apply (simp_all (no_asm))
    apply fast+
 apply (blast intro: hoare_conseq1)
apply safe
apply (rule hoare_conseq2)
 apply (rule hoare.While)
 apply (rule hoare_conseq1)
  prefer 2 apply (fast)
  apply safe
 apply (rotate_tac -1, simp)
apply (rotate_tac -1, simp)
done

lemma hoare_relative_complete: "|= {P}c{Q} ==> |- {P}c{Q}"
apply (rule hoare_conseq1 [OF _ wp_is_pre])
apply (unfold hoare_valid_def wp_def)
apply fast
done

end
