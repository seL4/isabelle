(*  Title:      HOLCF/IMP/Denotational.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Robert Sandner, TUM
    Copyright   1996 TUM
*)

header "Denotational Semantics of Commands in HOLCF"

theory Denotational = HOLCF + Natural:

subsection "Definition"

constdefs
   dlift :: "(('a::type) discr -> 'b::pcpo) => ('a lift -> 'b)"
  "dlift f == (LAM x. case x of UU => UU | Def(y) => f$(Discr y))"

consts D :: "com => state discr -> state lift"

primrec
  "D(\<SKIP>) = (LAM s. Def(undiscr s))"
  "D(X :== a) = (LAM s. Def((undiscr s)[X \<mapsto> a(undiscr s)]))"
  "D(c0 ; c1) = (dlift(D c1) oo (D c0))"
  "D(\<IF> b \<THEN> c1 \<ELSE> c2) =
	(LAM s. if b(undiscr s) then (D c1)$s else (D c2)$s)"
  "D(\<WHILE> b \<DO> c) =
	fix$(LAM w s. if b(undiscr s) then (dlift w)$((D c)$s)
                      else Def(undiscr s))"

subsection
  "Equivalence of Denotational Semantics in HOLCF and Evaluation Semantics in HOL"

lemma dlift_Def: "dlift f$(Def x) = f$(Discr x)"
apply (unfold dlift_def)
apply (simp (no_asm))
done
declare dlift_Def [simp]

lemma cont_dlift: "cont(%f. dlift f)"
apply (unfold dlift_def)
apply (simp (no_asm))
done
declare cont_dlift [iff]

lemma dlift_is_Def: 
 "(dlift f$l = Def y) = (? x. l = Def x & f$(Discr x) = Def y)"
apply (unfold dlift_def)
apply (simp (no_asm) split add: lift.split)
done
declare dlift_is_Def [simp]

lemma eval_implies_D [rule_format (no_asm)]: 
  "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t ==> D c$(Discr s) = (Def t)"
apply (erule evalc.induct)
      apply (simp_all (no_asm_simp))
 apply (subst fix_eq)
 apply simp
apply (subst fix_eq)
apply simp
done

lemma D_implies_eval [rule_format (no_asm)]: 
  "!s t. D c$(Discr s) = (Def t) --> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"
apply (induct_tac "c")
    apply force
   apply force
  apply force
 apply (simp (no_asm))
 apply force
apply (simp (no_asm))
apply (rule fix_ind)
  apply (fast intro!: adm_lemmas adm_chfindom ax_flat)
 apply (simp (no_asm))
apply (simp (no_asm))
apply safe
apply fast
done

lemma D_is_eval: "(D c$(Discr s) = (Def t)) = (\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t)"
  by (fast elim!: D_implies_eval eval_implies_D)

end
