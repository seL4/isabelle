(*  Title:      HOL/IMP/Examples.thy
    ID:         $Id$
    Author:     David von Oheimb, TUM
    Copyright   2000 TUM
*)

header "Examples"

theory Examples imports Natural begin

constdefs
  factorial :: "loc => loc => com"
  "factorial a b == b :== (%s. 1);
                    \<WHILE> (%s. s a ~= 0) \<DO>
                    (b :== (%s. s b * s a); a :== (%s. s a - 1))"

declare update_def [simp]

subsection "An example due to Tony Hoare"

lemma lemma1:
  assumes 1: "!x. P x \<longrightarrow> Q x"
    and 2: "\<langle>w,s\<rangle> \<longrightarrow>\<^sub>c t"
  shows "w = While P c \<Longrightarrow> \<langle>While Q c,t\<rangle> \<longrightarrow>\<^sub>c u \<Longrightarrow> \<langle>While Q c,s\<rangle> \<longrightarrow>\<^sub>c u"
  using 2 apply induct
  using 1 apply auto
  done

lemma lemma2 [rule_format (no_asm)]:
  "[| !x. P x \<longrightarrow> Q x; \<langle>w,s\<rangle> \<longrightarrow>\<^sub>c u |] ==>
  !c. w = While Q c \<longrightarrow> \<langle>While P c; While Q c,s\<rangle> \<longrightarrow>\<^sub>c u"
apply (erule evalc.induct)
apply (simp_all (no_asm_simp))
apply blast
apply (case_tac "P s")
apply auto
done

lemma Hoare_example: "!x. P x \<longrightarrow> Q x ==>
  (\<langle>While P c; While Q c, s\<rangle> \<longrightarrow>\<^sub>c t) = (\<langle>While Q c, s\<rangle> \<longrightarrow>\<^sub>c t)"
  by (blast intro: lemma1 lemma2 dest: semi [THEN iffD1])


subsection "Factorial"

lemma factorial_3: "a~=b ==>
    \<langle>factorial a b, Mem(a:=3)\<rangle> \<longrightarrow>\<^sub>c Mem(b:=6, a:=0)"
  by (simp add: factorial_def)

text {* the same in single step mode: *}
lemmas [simp del] = evalc_cases
lemma  "a~=b \<Longrightarrow> \<langle>factorial a b, Mem(a:=3)\<rangle> \<longrightarrow>\<^sub>c Mem(b:=6, a:=0)"
apply (unfold factorial_def)
apply (frule not_sym)
apply (rule evalc.intros)
apply  (rule evalc.intros)
apply simp
apply (rule evalc.intros)
apply   simp
apply  (rule evalc.intros)
apply   (rule evalc.intros)
apply  simp
apply  (rule evalc.intros)
apply simp
apply (rule evalc.intros)
apply   simp
apply  (rule evalc.intros)
apply   (rule evalc.intros)
apply  simp
apply  (rule evalc.intros)
apply simp
apply (rule evalc.intros)
apply   simp
apply  (rule evalc.intros)
apply   (rule evalc.intros)
apply  simp
apply  (rule evalc.intros)
apply simp
apply (rule evalc.intros)
apply simp
done

end
