theory Example_Metric
  imports "HOL-Analysis.Metric_Arith" "HOL-Eisbach.Eisbach_Tools"
begin

method dist_refl_sym = simp only: simp_thms dist_commute dist_self

method lin_real_arith uses thms = argo thms

method pre_arith uses argo_thms =
  (simp only: metric_pre_arith)?;
  lin_real_arith thms: argo_thms

method elim_sup =
  (simp only: image_insert image_empty)?;
  dist_refl_sym?;
  (simp only: algebra_simps simp_thms)?;
  (simp only: simp_thms Sup_insert_insert cSup_singleton)?;
  (simp only: simp_thms real_abs_dist)?

method ball_simp = simp only: Set.ball_simps(5,7)

lemmas maxdist_thm = maxdist_thm\<comment> \<open>normalizes indexnames\<close>

method rewr_maxdist for ps::"'a::metric_space set" uses pos_thms =
  match conclusion in
    "?P (dist x y)" (cut) for x y::'a \<Rightarrow> \<open>
    simp only: maxdist_thm[where s=ps and x=x and y=y]
      simp_thms finite.emptyI finite_insert empty_iff insert_iff;
    rewr_maxdist ps pos_thms: pos_thms zero_le_dist[of x y]\<close>
  \<bar> _ \<Rightarrow> \<open>
    ball_simp?;
    dist_refl_sym?;
    elim_sup?;
    pre_arith argo_thms: pos_thms\<close>

lemmas metric_eq_thm = metric_eq_thm\<comment> \<open>normalizes indexnames\<close>
method rewr_metric_eq for ps::"'a::metric_space set" =
  match conclusion in
    "?P (x = y)" (cut) for x y::'a \<Rightarrow> \<open>
    simp only: metric_eq_thm[where s=ps and x=x and y=y] simp_thms empty_iff insert_iff;
    rewr_metric_eq ps\<close>
  \<bar> _ \<Rightarrow> \<open>-\<close>

method find_points for ps::"'a::metric_space set" and t::bool =
  match (t) in
    "Q p" (cut) for p::'a and Q::"'a\<Rightarrow>bool" \<Rightarrow> \<open>
    find_points \<open>insert p ps\<close> \<open>\<forall>p. Q p\<close>\<close>
  \<bar> _ \<Rightarrow> \<open>
    rewr_metric_eq ps;
    rewr_maxdist ps\<close>

method basic_metric_arith for p::"'a::metric_space" =
  dist_refl_sym?;
  match conclusion in
    "Q q" (cut) for q::'a and Q \<Rightarrow> \<open>
    find_points \<open>{q}\<close> \<open>\<forall>p. Q p\<close>\<close>
  \<bar> _ \<Rightarrow> \<open>
    rewr_metric_eq \<open>{}::'a set\<close>;
    rewr_maxdist \<open>{}::'a set\<close>\<close>

method elim_exists_loop for p::"'a::metric_space" =
  match conclusion in
    "\<exists>q::'a. ?P q r" for r::'a \<Rightarrow> \<open>
    print_term r;
    rule exI[of _ r];
    elim_exists_loop p\<close>
  \<bar> "\<forall>x. ?P x" (cut) \<Rightarrow> \<open>
    rule allI;
    elim_exists_loop p\<close>
  \<bar> _ \<Rightarrow> \<open>-\<close>

method elim_exists for p::"'a::metric_space" =
  elim_exists_loop p;
  basic_metric_arith p

method find_type =
  match conclusion in
  (* exists in front *)
    "\<exists>x::'a::metric_space. ?P x" \<Rightarrow> \<open>
      match conclusion in
        "?Q x" (cut) for x::"'a::metric_space" \<Rightarrow> \<open>elim_exists x\<close>
      \<bar> _ \<Rightarrow> \<open>
        rule exI;
        match conclusion in "?Q x" (cut) for x::"'a::metric_space" \<Rightarrow> \<open>elim_exists x\<close>\<close>\<close>
  (* no exists *)
  \<bar> "?P (\<lambda>y. (dist x y))" (cut) for x::"'a::metric_space" \<Rightarrow> \<open>elim_exists x\<close>
  \<bar> "?P (\<lambda>x. (dist x y))" (cut) for y::"'a::metric_space" \<Rightarrow> \<open>elim_exists y\<close>
  \<bar> "?P (\<lambda>y. (x = y))" (cut) for x::"'a::metric_space" \<Rightarrow> \<open>elim_exists x\<close>
  \<bar> "?P (\<lambda>x. (x = y))" (cut) for y::"'a::metric_space" \<Rightarrow> \<open>elim_exists y\<close>
  \<bar> _ \<Rightarrow> \<open>
    rule exI;
    find_type\<close>

method metric_eisbach =
  (simp only: metric_unfold)?;
  (atomize (full))?;
  (simp only: metric_prenex)?;
  (simp only: metric_nnf)?;
  ((rule allI)+)?;
  match conclusion in _ \<Rightarrow> find_type

subsection \<open>examples\<close>

lemma "\<exists>x::'a::metric_space. x=x"
  by metric_eisbach

lemma "\<forall>(x::'a::metric_space). \<exists>y. x = y"
  by metric_eisbach

lemma "\<exists>x y. dist x y = 0"
  by metric_eisbach

lemma "\<exists>y. dist x y = 0"
  by metric_eisbach

lemma "0 = dist x y \<Longrightarrow> x = y"
  by metric_eisbach

lemma "x \<noteq> y \<Longrightarrow> dist x y \<noteq> 0"
  by metric_eisbach

lemma "\<exists>y. dist x y \<noteq> 1"
  by metric_eisbach

lemma "x = y \<longleftrightarrow> dist x x = dist y x \<and> dist x y = dist y y"
  by metric_eisbach

lemma "dist a b \<noteq> dist a c \<Longrightarrow> b \<noteq> c"
  by metric_eisbach

lemma "dist y x + c \<ge> c"
  by metric_eisbach

lemma "dist x y + dist x z \<ge> 0"
  by metric_eisbach

lemma "dist x y \<ge> v \<Longrightarrow> dist x y + dist (a::'a) b \<ge> v" for x::"('a::metric_space)"
  by metric_eisbach

lemma "dist x y < 0 \<longrightarrow> P"
  by metric_eisbach

text \<open>reasoning with the triangle inequality\<close>

lemma "dist a d \<le> dist a b + dist b c + dist c d"
  by metric_eisbach

lemma "dist a e \<le> dist a b + dist b c + dist c d + dist d e"
  by metric_eisbach

lemma "max (dist x y) \<bar>dist x z - dist z y\<bar> = dist x y"
  by metric_eisbach

lemma
  "dist w x < e/3 \<Longrightarrow> dist x y < e/3 \<Longrightarrow> dist y z < e/3 \<Longrightarrow> dist w x < e"
  by metric_eisbach

lemma "dist w x < e/4 \<Longrightarrow> dist x y < e/4 \<Longrightarrow> dist y z < e/2 \<Longrightarrow> dist w z < e"
  by metric_eisbach

lemma "dist x y = r / 2 \<Longrightarrow> (\<forall>z. dist x z < r / 4 \<longrightarrow> dist y z \<le> 3 * r / 4)"
  by metric_eisbach

lemma "\<exists>x. \<forall>r\<le>0. \<exists>z. dist x z \<ge> r"
  by metric_eisbach

lemma "\<And>a r x y. dist x a + dist a y = r \<Longrightarrow> \<forall>z. r \<le> dist x z + dist z y \<Longrightarrow> dist x y = r"
  by metric_eisbach

end