(*  Title:      ZF/IMP/Equiv.thy
    Author:     Heiko Loetzbeyer and Robert Sandner, TU München
*)

section \<open>Equivalence\<close>

theory Equiv imports Denotation Com begin

lemma aexp_iff [rule_format]:
  "\<lbrakk>a \<in> aexp; sigma: loc -> nat\<rbrakk> 
    \<Longrightarrow> \<forall>n. \<langle>a,sigma\<rangle> -a-> n \<longleftrightarrow> A(a,sigma) = n"
  apply (erule aexp.induct)
     apply (force intro!: evala.intros)+
  done

declare aexp_iff [THEN iffD1, simp]
        aexp_iff [THEN iffD2, intro!]

inductive_cases [elim!]:
  "\<langle>true,sigma\<rangle> -b-> x"
  "\<langle>false,sigma\<rangle> -b-> x"
  "<ROp(f,a0,a1),sigma> -b-> x"
  "<noti(b),sigma> -b-> x"
  "<b0 andi b1,sigma> -b-> x"
  "<b0 ori b1,sigma> -b-> x"


lemma bexp_iff [rule_format]:
  "\<lbrakk>b \<in> bexp; sigma: loc -> nat\<rbrakk> 
    \<Longrightarrow> \<forall>w. \<langle>b,sigma\<rangle> -b-> w \<longleftrightarrow> B(b,sigma) = w"
  apply (erule bexp.induct) 
  apply (auto intro!: evalb.intros)
  done

declare bexp_iff [THEN iffD1, simp]
        bexp_iff [THEN iffD2, intro!]

lemma com1: "\<langle>c,sigma\<rangle> -c-> sigma' \<Longrightarrow> <sigma,sigma'> \<in> C(c)"
  apply (erule evalc.induct)
        apply (simp_all (no_asm_simp))
     txt \<open>\<open>assign\<close>\<close>
     apply (simp add: update_type)
    txt \<open>\<open>comp\<close>\<close>
    apply fast
   txt \<open>\<open>while\<close>\<close>
   apply (erule Gamma_bnd_mono [THEN lfp_unfold, THEN ssubst, OF C_subset])
   apply (simp add: Gamma_def)
  txt \<open>recursive case of \<open>while\<close>\<close>
  apply (erule Gamma_bnd_mono [THEN lfp_unfold, THEN ssubst, OF C_subset])
  apply (auto simp add: Gamma_def)
  done

declare B_type [intro!] A_type [intro!]
declare evalc.intros [intro]


lemma com2 [rule_format]: "c \<in> com \<Longrightarrow> \<forall>x \<in> C(c). <c,fst(x)> -c-> snd(x)"
  apply (erule com.induct)
      txt \<open>\<open>skip\<close>\<close>
      apply force
     txt \<open>\<open>assign\<close>\<close>
     apply force
    txt \<open>\<open>comp\<close>\<close>
    apply force
   txt \<open>\<open>while\<close>\<close>
   apply safe
   apply simp_all
   apply (frule Gamma_bnd_mono [OF C_subset], erule Fixedpt.induct, assumption)
     unfolding Gamma_def
   apply force
  txt \<open>\<open>if\<close>\<close>
  apply auto
  done


subsection \<open>Main theorem\<close>

theorem com_equivalence:
    "c \<in> com \<Longrightarrow> C(c) = {io \<in> (loc->nat) \<times> (loc->nat). <c,fst(io)> -c-> snd(io)}"
  by (force intro: C_subset [THEN subsetD] elim: com2 dest: com1)

end

