(*  Title:      HOLCF/IMP/Denotational.thy
    ID:         $Id$
    Author:     Tobias Nipkow and Robert Sandner, TUM
    Copyright   1996 TUM
*)

header "Denotational Semantics of Commands in HOLCF"

theory Denotational = HOLCF + Natural:

subsection "Definition"

constdefs
  dlift :: "(('a::type) discr -> 'b::pcpo) => ('a lift -> 'b)"
  "dlift f == (LAM x. case x of UU => UU | Def y => f\<cdot>(Discr y))"

consts D :: "com => state discr -> state lift"

primrec
  "D(\<SKIP>) = (LAM s. Def(undiscr s))"
  "D(X :== a) = (LAM s. Def((undiscr s)[X \<mapsto> a(undiscr s)]))"
  "D(c0 ; c1) = (dlift(D c1) oo (D c0))"
  "D(\<IF> b \<THEN> c1 \<ELSE> c2) =
        (LAM s. if b (undiscr s) then (D c1)\<cdot>s else (D c2)\<cdot>s)"
  "D(\<WHILE> b \<DO> c) =
        fix\<cdot>(LAM w s. if b (undiscr s) then (dlift w)\<cdot>((D c)\<cdot>s)
                      else Def(undiscr s))"

subsection
  "Equivalence of Denotational Semantics in HOLCF and Evaluation Semantics in HOL"

lemma dlift_Def [simp]: "dlift f\<cdot>(Def x) = f\<cdot>(Discr x)"
  by (simp add: dlift_def)

lemma cont_dlift [iff]: "cont (%f. dlift f)"
  by (simp add: dlift_def)

lemma dlift_is_Def [simp]:
    "(dlift f\<cdot>l = Def y) = (\<exists>x. l = Def x \<and> f\<cdot>(Discr x) = Def y)"
  by (simp add: dlift_def split: lift.split)

lemma eval_implies_D: "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t ==> D c\<cdot>(Discr s) = (Def t)"
  apply (induct set: evalc)
        apply simp_all
   apply (subst fix_eq)
   apply simp
  apply (subst fix_eq)
  apply simp
  done

lemma D_implies_eval: "!s t. D c\<cdot>(Discr s) = (Def t) --> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"
  apply (induct c)
      apply simp
     apply simp
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

theorem D_is_eval: "(D c\<cdot>(Discr s) = (Def t)) = (\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t)"
  by (fast elim!: D_implies_eval [rule_format] eval_implies_D)

end
