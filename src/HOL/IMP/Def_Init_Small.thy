(* Author: Tobias Nipkow *)

theory Def_Init_Small
imports Star Def_Init_Exp Def_Init
begin

subsection "Initialization-Sensitive Small Step Semantics"

inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix \<open>\<rightarrow>\<close> 55)
where
Assign:  "aval a s = Some i \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := Some i))" |

Seq1:   "(SKIP;;c,s) \<rightarrow> (c,s)" |
Seq2:   "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "bval b s = Some True \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "bval b s = Some False \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c;; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

abbreviation small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix \<open>\<rightarrow>*\<close> 55)
where "x \<rightarrow>* y == star small_step x y"


subsection "Soundness wrt Small Steps"

theorem progress:
  "D (dom s) c A' \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
proof (induction c arbitrary: s A')
  case Assign thus ?case by auto (metis aval_Some small_step.Assign)
next
  case (If b c1 c2)
  then obtain bv where "bval b s = Some bv" by (auto dest!:bval_Some)
  then show ?case
    by(cases bv)(auto intro: small_step.IfTrue small_step.IfFalse)
qed (fastforce intro: small_step.intros)+

lemma D_mono:  "D A c M \<Longrightarrow> A \<subseteq> A' \<Longrightarrow> \<exists>M'. D A' c M' & M <= M'"
proof (induction c arbitrary: A A' M)
  case Seq thus ?case by auto (metis D.intros(3))
next
  case (If b c1 c2)
  then obtain M1 M2 where "vars b \<subseteq> A" "D A c1 M1" "D A c2 M2" "M = M1 \<inter> M2"
    by auto
  with If.IH \<open>A \<subseteq> A'\<close> obtain M1' M2'
    where "D A' c1 M1'" "D A' c2 M2'" and "M1 \<subseteq> M1'" "M2 \<subseteq> M2'" by metis
  hence "D A' (IF b THEN c1 ELSE c2) (M1' \<inter> M2')" and "M \<subseteq> M1' \<inter> M2'"
    using \<open>vars b \<subseteq> A\<close> \<open>A \<subseteq> A'\<close> \<open>M = M1 \<inter> M2\<close> by(fastforce intro: D.intros)+
  thus ?case by metis
next
  case While thus ?case by auto (metis D.intros(5) subset_trans)
qed (auto intro: D.intros)

theorem D_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> D (dom s) c A \<Longrightarrow> \<exists>A'. D (dom s') c' A' & A <= A'"
proof (induction arbitrary: A rule: small_step_induct)
  case (While b c s)
  then obtain A' where A': "vars b \<subseteq> dom s" "A = dom s" "D (dom s) c A'" by blast
  then obtain A'' where "D A' c A''" by (metis D_incr D_mono)
  with A' have "D (dom s) (IF b THEN c;; WHILE b DO c ELSE SKIP) (dom s)"
    by (metis D.If[OF \<open>vars b \<subseteq> dom s\<close> D.Seq[OF \<open>D (dom s) c A'\<close> D.While[OF _ \<open>D A' c A''\<close>]] D.Skip] D_incr Int_absorb1 subset_trans)
  thus ?case by (metis D_incr \<open>A = dom s\<close>)
next
  case Seq2 thus ?case by auto (metis D_mono D.intros(3))
qed (auto intro: D.intros)

theorem D_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> D (dom s) c A'
   \<Longrightarrow> (\<exists>cs''. (c',s') \<rightarrow> cs'') \<or> c' = SKIP"
apply(induction arbitrary: A' rule:star_induct)
apply (metis progress)
by (metis D_preservation)

end
