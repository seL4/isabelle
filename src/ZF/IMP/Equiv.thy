(*  Title:      ZF/IMP/Equiv.thy
    ID:         $Id$
    Author:     Heiko Loetzbeyer & Robert Sandner, TUM
    Copyright   1994 TUM
*)

theory Equiv = Denotation + Com:

lemma aexp_iff [rule_format]:
     "[| a \<in> aexp; sigma: loc -> nat |] 
      ==> ALL n. <a,sigma> -a-> n <-> A(a,sigma) = n"
apply (erule aexp.induct) 
apply (force intro!: evala.intros)+
done

declare aexp_iff [THEN iffD1, simp]
        aexp_iff [THEN iffD2, intro!]

inductive_cases [elim!]: "<true,sigma> -b-> x"
inductive_cases [elim!]: "<false,sigma> -b-> x"
inductive_cases [elim!]: "<ROp(f,a0,a1),sigma> -b-> x"
inductive_cases [elim!]: "<noti(b),sigma> -b-> x"
inductive_cases [elim!]: "<b0 andi b1,sigma> -b-> x"
inductive_cases [elim!]: "<b0 ori b1,sigma> -b-> x"


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
apply simp_all
(* skip *)
apply fast
(* assign *)
apply (simp add: update_type)
(* comp *)
apply fast
(* while *)
apply (erule Gamma_bnd_mono [THEN lfp_unfold, THEN ssubst, OF C_subset])
apply (simp add: Gamma_def)
apply (force ) 
(* recursive case of while *)
apply (erule Gamma_bnd_mono [THEN lfp_unfold, THEN ssubst, OF C_subset])
apply (simp add: Gamma_def)
apply auto
done


declare B_type [intro!] A_type [intro!]
declare evalc.intros [intro]


lemma com2 [rule_format]: "c \<in> com ==> \<forall>x \<in> C(c). <c,fst(x)> -c-> snd(x)"
apply (erule com.induct)
(* skip *)
apply force
(* assign *)
apply force
(* comp *)
apply force
(* while *)
apply safe
apply simp_all
apply (frule Gamma_bnd_mono [OF C_subset], erule Fixedpt.induct, assumption)
apply (unfold Gamma_def)
apply force
(* if *)
apply auto
done


(**** Proof of Equivalence ****)

lemma com_equivalence:
     "\<forall>c \<in> com. C(c) = {io:(loc->nat)*(loc->nat). <c,fst(io)> -c-> snd(io)}"
by (force intro: C_subset [THEN subsetD] elim: com2 dest: com1)

end

