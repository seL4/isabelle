(*  Title:      ZF/IMP/Equiv.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer and Robert Sandner, TU München
*)

header {* Equivalence *}

theory Equiv = Denotation + Com:

lemma aexp_iff [rule_format]:
  "[| a \<in> aexp; sigma: loc -> nat |] 
    ==> ALL n. <a,sigma> -a-> n <-> A(a,sigma) = n"
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
    ==> ALL w. <b,sigma> -b-> w <-> B(b,sigma) = w"
  apply (erule bexp.induct) 
  apply (auto intro!: evalb.intros)
  done

declare bexp_iff [THEN iffD1, simp]
        bexp_iff [THEN iffD2, intro!]

lemma com1: "<c,sigma> -c-> sigma' ==> <sigma,sigma'> \<in> C(c)"
  apply (erule evalc.induct)
        apply (simp_all (no_asm_simp))
     txt {* @{text assign} *}
     apply (simp add: update_type)
    txt {* @{text comp} *}
    apply fast
   txt {* @{text while} *}
   apply (erule Gamma_bnd_mono [THEN lfp_unfold, THEN ssubst, OF C_subset])
   apply (simp add: Gamma_def)
  txt {* recursive case of @{text while} *}
  apply (erule Gamma_bnd_mono [THEN lfp_unfold, THEN ssubst, OF C_subset])
  apply (auto simp add: Gamma_def)
  done

declare B_type [intro!] A_type [intro!]
declare evalc.intros [intro]


lemma com2 [rule_format]: "c \<in> com ==> \<forall>x \<in> C(c). <c,fst(x)> -c-> snd(x)"
  apply (erule com.induct)
      txt {* @{text skip} *}
      apply force
     txt {* @{text assign} *}
     apply force
    txt {* @{text comp} *}
    apply force
   txt {* @{text while} *}
   apply safe
   apply simp_all
   apply (frule Gamma_bnd_mono [OF C_subset], erule Fixedpt.induct, assumption)
   apply (unfold Gamma_def)
   apply force
  txt {* @{text if} *}
  apply auto
  done


subsection {* Main theorem *}

theorem com_equivalence:
    "c \<in> com ==> C(c) = {io \<in> (loc->nat) \<times> (loc->nat). <c,fst(io)> -c-> snd(io)}"
  by (force intro: C_subset [THEN subsetD] elim: com2 dest: com1)

end

