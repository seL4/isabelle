section \<open>Radical extensions and solvability by radicals\<close>

theory Radical_Extension
  imports Simple_Extension
begin

text \<open>This theory begins the \<^emph>\<open>forward\<close> Abel--Ruffini direction (phase R1: the definitions).  It
  fixes the notion of \<^emph>\<open>solvability by radicals\<close> over a base field, on the same generic
  @{typ "'a :: field"}/@{const generate_field} foundation used for the quintic.  Later phases will
  connect it to solvability of the Galois group (via the Galois correspondence, cyclotomic and
  Kummer theory).  Here we only make the target statement expressible.\<close>

subsection \<open>Radical steps and towers\<close>

text \<open>A single \<^emph>\<open>radical step\<close> from @{term F} to @{term F'} adjoins an element @{term a} some power
  of which already lies in @{term F}: @{term "F' = generate_field (F \<union> {a})"} with
  @{term "a ^ n \<in> F"} for some @{term "n > 0"}.\<close>
definition radical_step :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "radical_step F F' \<equiv> (\<exists>a n. n > 0 \<and> a ^ n \<in> F \<and> F' = generate_field (F \<union> {a}))"

text \<open>A \<^emph>\<open>radical tower\<close> is a list of fields, each obtained from the previous by a radical step.
  @{term "radical_tower F Fs"} says the tower starting at @{term F} and following @{term Fs} is
  valid (each consecutive pair is a radical step).\<close>
fun radical_tower :: "'a :: field set \<Rightarrow> 'a set list \<Rightarrow> bool" where
  "radical_tower F [] \<longleftrightarrow> True"
| "radical_tower F (G # Gs) \<longleftrightarrow> radical_step F G \<and> radical_tower G Gs"

text \<open>The top field of a tower (the last field, or the base if the tower is empty).\<close>
definition tower_top :: "'a :: field set \<Rightarrow> 'a set list \<Rightarrow> 'a set"
  where "tower_top F Fs = last (F # Fs)"

lemma tower_top_Nil [simp]: "tower_top F [] = F"
  by (simp add: tower_top_def)

lemma tower_top_Cons [simp]: "tower_top F (G # Gs) = tower_top G Gs"
  by (simp add: tower_top_def)

subsection \<open>Solvability by radicals\<close>

text \<open>A set @{term S} (typically the roots of a polynomial, together with the base field) is
  \<^emph>\<open>solvable by radicals\<close> over @{term F} when there is a radical tower over @{term F} whose top field
  contains @{term S}.\<close>
definition solvable_by_radicals :: "'a :: field set \<Rightarrow> 'a set \<Rightarrow> bool"
  where "solvable_by_radicals F S \<longleftrightarrow> (\<exists>Fs. radical_tower F Fs \<and> S \<subseteq> tower_top F Fs)"

text \<open>The base field itself is trivially solvable by radicals (the empty tower).\<close>
lemma solvable_by_radicals_base:
  assumes "S \<subseteq> F" shows "solvable_by_radicals F S"
  unfolding solvable_by_radicals_def  
  using assms by (auto intro!: exI[of _ "[]"])

text \<open>A single radical step gives a one-element tower.\<close>
lemma solvable_by_radicals_step:
  assumes "n > 0" and "a ^ n \<in> F" and "S \<subseteq> generate_field (F \<union> {a})"
  shows "solvable_by_radicals F S"
  unfolding solvable_by_radicals_def
proof (intro exI[of _ "[generate_field (F \<union> {a})]"] conjI)
  show "radical_tower F [generate_field (F \<union> {a})]"
    using assms by (auto simp: radical_step_def)
  show "S \<subseteq> tower_top F [generate_field (F \<union> {a})]" using assms(3) by simp
qed

subsection \<open>Concatenation of radical towers\<close>

text \<open>The top of a concatenated tower is the top of the second part (or of the first, if the second is
  empty).\<close>
lemma tower_top_append:
  "tower_top F (Fs @ Gs) = tower_top (tower_top F Fs) Gs"
  by (simp add: tower_top_def last_append)

text \<open>\<^emph>\<open>Radical towers concatenate.\<close>  A radical tower over @{term F} followed by a radical tower over its
  top field @{term "tower_top F Fs"} yields a radical tower over @{term F} along the appended list.
  This is the splicing primitive used to build a compositum of radical extensions into a single tower.\<close>
lemma radical_tower_append:
  "radical_tower F Fs \<Longrightarrow> radical_tower (tower_top F Fs) Gs \<Longrightarrow> radical_tower F (Fs @ Gs)"
  by (induction Fs arbitrary: F) auto

text \<open>\<^emph>\<open>Iterated concatenation.\<close>  Given a list of towers, each valid over the top reached so far, their
  concatenation is a single radical tower.  We phrase validity of a list of towers recursively.\<close>
fun radical_tower_list :: "'a :: field set \<Rightarrow> 'a set list list \<Rightarrow> bool" where
  "radical_tower_list F [] \<longleftrightarrow> True"
| "radical_tower_list F (Ts # Tss) \<longleftrightarrow>
     radical_tower F Ts \<and> radical_tower_list (tower_top F Ts) Tss"

lemma radical_tower_concat:
  "radical_tower_list F Tss \<Longrightarrow> radical_tower F (concat Tss)"
  by (induction Tss arbitrary: F) (auto simp: radical_tower_append)

lemma tower_top_concat:
  "radical_tower_list F Tss \<Longrightarrow> tower_top F (concat Tss) = foldl tower_top F Tss"
  by (induction Tss arbitrary: F) (auto simp: tower_top_append)

subsection \<open>Base change: lifting a radical tower to a larger base\<close>

text \<open>Adjoining a fixed set @{term E} to every field of a radical tower over @{term F} yields a radical
  tower over @{term "generate_field (E \<union> F)"}: each step \<open>H \<leadsto> generate_field (H \<union> {a})\<close> becomes
  \<open>generate_field (E \<union> H) \<leadsto> generate_field (E \<union> generate_field (H \<union> {a}))\<close>, which by the collapse
  lemmas is @{term "generate_field (generate_field (E \<union> H) \<union> {a})"} with the same radical @{term a}
  (its power \<open>a\<^sup>n \<in> H \<subseteq> generate_field (E \<union> H)\<close>).  This is what lets conjugate towers, each
  based at @{term F}, be spliced onto a growing compositum.\<close>
lemma radical_step_basechange:
  assumes "radical_step F G"
  shows "radical_step (generate_field (E \<union> F)) (generate_field (E \<union> G))"
proof -
  obtain a n where n: "n > 0" and anF: "a ^ n \<in> F" and Gdef: "G = generate_field (F \<union> {a})"
    using assms by (auto simp: radical_step_def)
  have "a ^ n \<in> generate_field (E \<union> F)" using anF subset_generate_field by blast
  moreover have "generate_field (E \<union> G) = generate_field (generate_field (E \<union> F) \<union> {a})"
    by (metis Gdef Un_commute generate_field_Un_collapse2 sup.assoc)
  ultimately show ?thesis unfolding radical_step_def using n by blast
qed

text \<open>Hence base change of a whole radical tower: mapping each field @{term H} to
  @{term "generate_field (E \<union> H)"} sends a radical tower over @{term F} to a radical tower over
  @{term "generate_field (E \<union> F)"}.\<close>
lemma radical_tower_basechange:
  "radical_tower F Fs \<Longrightarrow> radical_tower (generate_field (E \<union> F)) (map (\<lambda>H. generate_field (E \<union> H)) Fs)"
  by (induction Fs arbitrary: F) (auto simp: radical_step_basechange)

end
