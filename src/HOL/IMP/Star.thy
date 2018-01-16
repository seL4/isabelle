theory Star imports Main
begin

inductive
  star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

hide_fact (open) refl step  \<comment> \<open>names too generic\<close>

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
proof(induction rule: star.induct)
  case refl thus ?case .
next
  case step thus ?case by (metis star.step)
qed

lemmas star_induct =
  star.induct[of "r:: 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> bool", split_format(complete)]

declare star.refl[simp,intro]

lemma star_step1[simp, intro]: "r x y \<Longrightarrow> star r x y"
by(metis star.refl star.step)

code_pred star .

end
