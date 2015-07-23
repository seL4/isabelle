(*  Title:      ZF/IMP/Equiv.thy
    Author:     Heiko Loetzbeyer and Robert Sandner, TU München
*)

section \<open>Equivalence\<close>

theory Equiv imports Denotation Com begin

lemma aexp_iff [rule_format]:
  "[| a \<in> aexp; sigma: loc -> nat |] 
    ==> \<forall>n. <a,sigma> -a-> n \<longleftrightarrow> A(a,sigma) = n"
  apply (erule aexp.induct)
     apply (force intro!: evala.intros)+
  done

declare aexp_iff [THEN iffD1, simp]
        aexp_iff [THEN iffD2, intro!]

inductive_cases [elim!]:
  "<true,sigma> -b-> x"
  "<false,sigma> -b-> x"
  "<ROp(f,a0,a1),sigma> -b-> x"
  "<noti(b),sigma> -b-> x"
  "<b0 andi b1,sigma> -b-> x"
  "<b0 ori b1,sigma> -b-> x"


lemma bexp_iff [rule_format]:
  "[| b \<in> bexp; sigma: loc -> nat |] 
    ==> \<forall>w. <b,sigma> -b-> w \<longleftrightarrow> B(b,sigma) = w"
  apply (erule bexp.induct) 
  apply (auto intro!: evalb.intros)
  done

declare bexp_iff [THEN iffD1, simp]
        bexp_iff [THEN iffD2, intro!]

lemma com1: "<c,sigma> -c-> sigma' ==> <sigma,sigma'> \<in> C(c)"
  apply (erule evalc.induct)
        apply (simp_all (no_asm_simp))
     txt \<open>@{text assign}\<close>
     apply (simp add: update_type)
    txt \<open>@{text comp}\<close>
    apply fast
   txt \<open>@{text while}\<close>
   apply (erule Gamma_bnd_mono [THEN lfp_unfold, THEN ssubst, OF C_subset])
   apply (simp add: Gamma_def)
  txt \<open>recursive case of @{text while}\<close>
  apply (erule Gamma_bnd_mono [THEN lfp_unfold, THEN ssubst, OF C_subset])
  apply (auto simp add: Gamma_def)
  done

declare B_type [intro!] A_type [intro!]
declare evalc.intros [intro]


lemma com2 [rule_format]: "c \<in> com ==> \<forall>x \<in> C(c). <c,fst(x)> -c-> snd(x)"
  apply (erule com.induct)
      txt \<open>@{text skip}\<close>
      apply force
     txt \<open>@{text assign}\<close>
     apply force
    txt \<open>@{text comp}\<close>
    apply force
   txt \<open>@{text while}\<close>
   apply safe
   apply simp_all
   apply (frule Gamma_bnd_mono [OF C_subset], erule Fixedpt.induct, assumption)
   apply (unfold Gamma_def)
   apply force
  txt \<open>@{text "if"}\<close>
  apply auto
  done


subsection \<open>Main theorem\<close>

theorem com_equivalence:
    "c \<in> com ==> C(c) = {io \<in> (loc->nat) \<times> (loc->nat). <c,fst(io)> -c-> snd(io)}"
  by (force intro: C_subset [THEN subsetD] elim: com2 dest: com1)

end

