(*  Title:      HOL/HOLCF/Sfun.thy
    Author:     Brian Huffman
*)

header {* The Strict Function Type *}

theory Sfun
imports Cfun
begin

pcpodef ('a, 'b) sfun (infixr "->!" 0)
  = "{f :: 'a \<rightarrow> 'b. f\<cdot>\<bottom> = \<bottom>}"
by simp_all

type_notation (xsymbols)
  sfun  (infixr "\<rightarrow>!" 0)

text {* TODO: Define nice syntax for abstraction, application. *}

definition
  sfun_abs :: "('a \<rightarrow> 'b) \<rightarrow> ('a \<rightarrow>! 'b)"
where
  "sfun_abs = (\<Lambda> f. Abs_sfun (strictify\<cdot>f))"

definition
  sfun_rep :: "('a \<rightarrow>! 'b) \<rightarrow> 'a \<rightarrow> 'b"
where
  "sfun_rep = (\<Lambda> f. Rep_sfun f)"

lemma sfun_rep_beta: "sfun_rep\<cdot>f = Rep_sfun f"
  unfolding sfun_rep_def by (simp add: cont_Rep_sfun)

lemma sfun_rep_strict1 [simp]: "sfun_rep\<cdot>\<bottom> = \<bottom>"
  unfolding sfun_rep_beta by (rule Rep_sfun_strict)

lemma sfun_rep_strict2 [simp]: "sfun_rep\<cdot>f\<cdot>\<bottom> = \<bottom>"
  unfolding sfun_rep_beta by (rule Rep_sfun [simplified])

lemma strictify_cancel: "f\<cdot>\<bottom> = \<bottom> \<Longrightarrow> strictify\<cdot>f = f"
  by (simp add: cfun_eq_iff strictify_conv_if)

lemma sfun_abs_sfun_rep [simp]: "sfun_abs\<cdot>(sfun_rep\<cdot>f) = f"
  unfolding sfun_abs_def sfun_rep_def
  apply (simp add: cont_Abs_sfun cont_Rep_sfun)
  apply (simp add: Rep_sfun_inject [symmetric] Abs_sfun_inverse)
  apply (simp add: cfun_eq_iff strictify_conv_if)
  apply (simp add: Rep_sfun [simplified])
  done

lemma sfun_rep_sfun_abs [simp]: "sfun_rep\<cdot>(sfun_abs\<cdot>f) = strictify\<cdot>f"
  unfolding sfun_abs_def sfun_rep_def
  apply (simp add: cont_Abs_sfun cont_Rep_sfun)
  apply (simp add: Abs_sfun_inverse)
  done

lemma sfun_eq_iff: "f = g \<longleftrightarrow> sfun_rep\<cdot>f = sfun_rep\<cdot>g"
by (simp add: sfun_rep_def cont_Rep_sfun Rep_sfun_inject)

lemma sfun_below_iff: "f \<sqsubseteq> g \<longleftrightarrow> sfun_rep\<cdot>f \<sqsubseteq> sfun_rep\<cdot>g"
by (simp add: sfun_rep_def cont_Rep_sfun below_sfun_def)

end
