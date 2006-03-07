(*  Title:      HOL/ZF/Helper.thy
    ID:         $Id$
    Author:     Steven Obua

    Some helpful lemmas that probably will end up elsewhere. 
*)

theory Helper 
imports Main
begin

lemma theI2' : "?! x. P x \<Longrightarrow> (!! x. P x \<Longrightarrow> Q x) \<Longrightarrow> Q (THE x. P x)"
  apply auto
  apply (subgoal_tac "P (THE x. P x)")
  apply blast
  apply (rule theI)
  apply auto
  done

lemma in_range_superfluous: "(z \<in> range f & z \<in> (f ` x)) = (z \<in> f ` x)" 
  by auto

lemma f_x_in_range_f: "f x \<in> range f"
  by (blast intro: image_eqI)

lemma comp_inj: "inj f \<Longrightarrow> inj g \<Longrightarrow> inj (g o f)"
  by (blast intro: comp_inj_on subset_inj_on)

lemma comp_image_eq: "(g o f) ` x = g ` f ` x"
  by auto
  
end