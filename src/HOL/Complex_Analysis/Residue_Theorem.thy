section \<open>The Residue Theorem, the Argument Principle and Rouch\'{e}'s Theorem\<close>
theory Residue_Theorem
  imports Complex_Residues "HOL-Library.Landau_Symbols"
begin

text \<open>Several theorems that could be moved up, 
  IF there were a previous theory importing both Landau Symbols and Elementary Metric Spaces\<close>

lemma continuous_bounded_at_infinity_imp_bounded:
  fixes f :: "real \<Rightarrow> 'a :: real_normed_field"
  assumes "f \<in> O[at_bot](\<lambda>_. 1)"
  assumes "f \<in> O[at_top](\<lambda>_. 1)"
  assumes cf: "continuous_on UNIV f"
  shows   "bounded (range f)"
proof -
  obtain c1 c2 
    where "eventually (\<lambda>x. norm (f x) \<le> c1) at_bot" "eventually (\<lambda>x. norm (f x) \<le> c2) at_top"
    using assms by (auto elim!: landau_o.bigE)
  then obtain x1 x2 where x1: "\<And>x. x \<le> x1 \<Longrightarrow> norm (f x) \<le> c1" and x2: "\<And>x. x \<ge> x2 \<Longrightarrow> norm (f x) \<le> c2"
    by (auto simp: eventually_at_bot_linorder eventually_at_top_linorder)
  have "compact (f ` {x1..x2})"
    by (intro compact_continuous_image continuous_on_subset[OF cf]) auto
  hence "bounded (f ` {x1..x2})"
    by (rule compact_imp_bounded)
  then obtain c3 where c3: "\<And>x. x \<in> {x1..x2} \<Longrightarrow> norm (f x) \<le> c3"
    unfolding bounded_iff by fast
  have "norm (f x) \<le> Max {c1, c2, c3}" for x
    by (cases "x \<le> x1"; cases "x \<ge> x2") (use x1 x2 c3 in \<open>auto simp: le_max_iff_disj\<close>)
  thus ?thesis
    unfolding bounded_iff by blast
qed

lemma holomorphic_on_extend:
  assumes "f holomorphic_on S - {\<xi>}" "\<xi> \<in> interior S" "f \<in> O[at \<xi>](\<lambda>_. 1)"
  shows   "(\<exists>g. g holomorphic_on S \<and> (\<forall>z\<in>S - {\<xi>}. g z = f z))"
  by (subst holomorphic_on_extend_bounded) (insert assms, auto elim!: landau_o.bigE)

lemma removable_singularities:
  assumes "finite X" "X \<subseteq> interior S" "f holomorphic_on (S - X)"
  assumes "\<And>z. z \<in> X \<Longrightarrow> f \<in> O[at z](\<lambda>_. 1)"
  shows   "\<exists>g. g holomorphic_on S \<and> (\<forall>z\<in>S-X. g z = f z)"
  using assms
proof (induction arbitrary: f rule: finite_induct)
  case empty
  thus ?case by auto
next
  case (insert z0 X f)
  from insert.prems and insert.hyps have z0: "z0 \<in> interior (S - X)"
    by (auto simp: interior_diff finite_imp_closed)
  hence "\<exists>g. g holomorphic_on (S - X) \<and> (\<forall>z\<in>S - X - {z0}. g z = f z)"
    using insert.prems insert.hyps by (intro holomorphic_on_extend) auto
  then obtain g where g: "g holomorphic_on (S - X)" "\<forall>z\<in>S - X - {z0}. g z = f z" by blast
  have "\<exists>h. h holomorphic_on S \<and> (\<forall>z\<in>S - X. h z = g z)"
  proof (rule insert.IH)
    fix z0' assume z0': "z0' \<in> X"
    hence "eventually (\<lambda>z. z \<in> interior S - (X - {z0'}) - {z0}) (nhds z0')"
      using insert.prems insert.hyps
      by (intro eventually_nhds_in_open open_Diff finite_imp_closed) auto
    hence ev: "eventually (\<lambda>z. z \<in> S - X - {z0}) (at z0')"
      unfolding eventually_at_filter 
      by eventually_elim (insert z0' insert.hyps interior_subset[of S], auto)
    have "g \<in> \<Theta>[at z0'](f)"
      by (intro bigthetaI_cong eventually_mono[OF ev]) (insert g, auto)
    also have "f \<in> O[at z0'](\<lambda>_. 1)"
      using z0' by (intro insert.prems) auto
    finally show "g \<in> \<dots>" .
  qed (use insert.prems g in auto)
  then obtain h where "h holomorphic_on S" "\<forall>z\<in>S - X. h z = g z" by blast
  with g have "h holomorphic_on S" "\<forall>z\<in>S - insert z0 X. h z = f z" by auto
  thus ?case by blast
qed

lemma continuous_imp_bigo_1:
  assumes "continuous (at x within A) f"
  shows   "f \<in> O[at x within A](\<lambda>_. 1)"
proof (rule bigoI_tendsto)
  from assms show "((\<lambda>x. f x / 1) \<longlongrightarrow> f x) (at x within A)"
    by (auto simp: continuous_within)
qed auto

lemma taylor_bigo_linear:
  assumes "f field_differentiable at x0 within A"
  shows   "(\<lambda>x. f x - f x0) \<in> O[at x0 within A](\<lambda>x. x - x0)"
proof -
  from assms obtain f' where "(f has_field_derivative f') (at x0 within A)"
    by (auto simp: field_differentiable_def)
  hence "((\<lambda>x. (f x - f x0) / (x - x0)) \<longlongrightarrow> f') (at x0 within A)"
    by (auto simp: has_field_derivative_iff)
  thus ?thesis by (intro bigoI_tendsto[where c = f']) (auto simp: eventually_at_filter)
qed


subsection \<open>Cauchy's residue theorem\<close>

lemma get_integrable_path:
  assumes "open S" "connected (S-pts)" "finite pts" "f holomorphic_on (S-pts) " "a\<in>S-pts" "b\<in>S-pts"
  obtains g where "valid_path g" "pathstart g = a" "pathfinish g = b"
    "path_image g \<subseteq> S-pts" "f contour_integrable_on g" using assms
proof (induct arbitrary:S thesis a rule:finite_induct[OF \<open>finite pts\<close>])
  case 1
  obtain g where "valid_path g" "path_image g \<subseteq> S" "pathstart g = a" "pathfinish g = b"
    using connected_open_polynomial_connected[OF \<open>open S\<close>,of a b ] \<open>connected (S - {})\<close>
      valid_path_polynomial_function "1.prems"(6) "1.prems"(7) by auto
  moreover have "f contour_integrable_on g"
    using contour_integrable_holomorphic_simple[OF _ \<open>open S\<close> \<open>valid_path g\<close> \<open>path_image g \<subseteq> S\<close>,of f]
      \<open>f holomorphic_on S - {}\<close>
    by auto
  ultimately show ?case using "1"(1)[of g] by auto
next
  case idt:(2 p pts)
  obtain e where "e>0" and e:"\<forall>w\<in>ball a e. w \<in> S \<and> (w \<noteq> a \<longrightarrow> w \<notin> insert p pts)"
    using finite_ball_avoid[OF \<open>open S\<close> \<open>finite (insert p pts)\<close>, of a]
      \<open>a \<in> S - insert p pts\<close>
    by auto
  define a' where "a' \<equiv> a+e/2"
  have "a'\<in>S-{p} -pts"  using e[rule_format,of "a+e/2"] \<open>e>0\<close>
    by (auto simp add:dist_complex_def a'_def)
  then obtain g' where g'[simp]:"valid_path g'" "pathstart g' = a'" "pathfinish g' = b"
    "path_image g' \<subseteq> S - {p} - pts" "f contour_integrable_on g'"
    using idt.hyps(3)[of a' "S-{p}"] idt.prems idt.hyps(1)
    by (metis Diff_insert2 open_delete)
  define g where "g \<equiv> linepath a a' +++ g'"
  have "valid_path g" unfolding g_def by (auto intro: valid_path_join)
  moreover have "pathstart g = a" and  "pathfinish g = b" unfolding g_def by auto
  moreover have "path_image g \<subseteq> S - insert p pts" 
    unfolding g_def
  proof (rule subset_path_image_join)
    have "closed_segment a a' \<subseteq> ball a e" using \<open>e>0\<close>
      by (auto dest!:segment_bound1 simp:a'_def dist_complex_def norm_minus_commute)
    then show "path_image (linepath a a') \<subseteq> S - insert p pts" using e idt(9)
      by auto
  next
    show "path_image g' \<subseteq> S - insert p pts" using g'(4) by blast
  qed
  moreover have "f contour_integrable_on g"
  proof -
    have "closed_segment a a' \<subseteq> ball a e" using \<open>e>0\<close>
      by (auto dest!:segment_bound1 simp:a'_def dist_complex_def norm_minus_commute)
    then have "closed_segment a a' \<subseteq> S - insert p pts"
      using e idt.prems(6) by auto
    then have "continuous_on (closed_segment a a') f"
      using holomorphic_on_imp_continuous_on holomorphic_on_subset idt.prems(5) by presburger
    then show ?thesis 
      using contour_integrable_continuous_linepath by (simp add: g_def)
  qed
  ultimately show ?case using idt.prems(1)[of g] by auto
qed

lemma Cauchy_theorem_aux:
  assumes "open S" "connected (S-pts)" "finite pts" "pts \<subseteq> S" "f holomorphic_on S-pts"
          "valid_path g" "pathfinish g = pathstart g" "path_image g \<subseteq> S-pts"
          "\<forall>z. (z \<notin> S) \<longrightarrow> winding_number g z  = 0"
          "\<forall>p\<in>S. h p>0 \<and> (\<forall>w\<in>cball p (h p). w\<in>S \<and> (w\<noteq>p \<longrightarrow> w \<notin> pts))"
  shows "contour_integral g f = (\<Sum>p\<in>pts. winding_number g p * contour_integral (circlepath p (h p)) f)"
    using assms
proof (induct arbitrary:S g rule:finite_induct[OF \<open>finite pts\<close>])
  case 1
  then show ?case by (simp add: Cauchy_theorem_global contour_integral_unique)
next
  case (2 p pts)
  note fin[simp] = \<open>finite (insert p pts)\<close>
    and connected = \<open>connected (S - insert p pts)\<close>
    and valid[simp] = \<open>valid_path g\<close>
    and g_loop[simp] = \<open>pathfinish g = pathstart g\<close>
    and holo[simp]= \<open>f holomorphic_on S - insert p pts\<close>
    and path_img = \<open>path_image g \<subseteq> S - insert p pts\<close>
    and winding = \<open>\<forall>z. z \<notin> S \<longrightarrow> winding_number g z = 0\<close>
    and h = \<open>\<forall>pa\<in>S. 0 < h pa \<and> (\<forall>w\<in>cball pa (h pa). w \<in> S \<and> (w \<noteq> pa \<longrightarrow> w \<notin> insert p pts))\<close>
  have "h p>0" and "p\<in>S"
    and h_p: "\<forall>w\<in>cball p (h p). w \<in> S \<and> (w \<noteq> p \<longrightarrow> w \<notin> insert p pts)"
    using h \<open>insert p pts \<subseteq> S\<close> by auto
  obtain pg where pg[simp]: "valid_path pg" "pathstart pg = pathstart g" "pathfinish pg=p+h p"
    "path_image pg \<subseteq> S-insert p pts" "f contour_integrable_on pg"
  proof -
    have "p + h p\<in>cball p (h p)" using h[rule_format,of p]
      by (simp add: \<open>p \<in> S\<close> dist_norm)
    then have "p + h p \<in> S - insert p pts" using h[rule_format,of p] \<open>insert p pts \<subseteq> S\<close>
      by fastforce
    moreover have "pathstart g \<in> S - insert p pts " using path_img by auto
    ultimately show ?thesis
      using get_integrable_path[OF \<open>open S\<close> connected fin holo,of "pathstart g" "p+h p"] that
      by blast
  qed
  obtain n::int where "n=winding_number g p"
    using integer_winding_number[OF _ g_loop,of p] valid path_img
    by (metis DiffD2 Ints_cases insertI1 subset_eq valid_path_imp_path)
  define p_circ where "p_circ \<equiv> circlepath p (h p)"
  define p_circ_pt where "p_circ_pt \<equiv> linepath (p+h p) (p+h p)"
  define n_circ where "n_circ \<equiv> \<lambda>n. ((+++) p_circ ^^ n) p_circ_pt"
  define cp where "cp \<equiv> if n\<ge>0 then reversepath (n_circ (nat n)) else n_circ (nat (- n))"

  have n_circ:"valid_path (n_circ k)"
      "winding_number (n_circ k) p = k"
      "pathstart (n_circ k) = p + h p" "pathfinish (n_circ k) = p + h p"
      "path_image (n_circ k) =  (if k=0 then {p + h p} else sphere p (h p))"
      "p \<notin> path_image (n_circ k)"
      "\<And>p'. p'\<notin>S - pts \<Longrightarrow> winding_number (n_circ k) p'=0 \<and> p'\<notin>path_image (n_circ k)"
      "f contour_integrable_on (n_circ k)"
      "contour_integral (n_circ k) f = k *  contour_integral p_circ f"
      for k
    proof (induct k)
      case 0
      show "valid_path (n_circ 0)"
        and "path_image (n_circ 0) =  (if 0=0 then {p + h p} else sphere p (h p))"
        and "winding_number (n_circ 0) p = of_nat 0"
        and "pathstart (n_circ 0) = p + h p"
        and "pathfinish (n_circ 0) = p + h p"
        and "p \<notin> path_image (n_circ 0)"
        unfolding n_circ_def p_circ_pt_def using \<open>h p > 0\<close>
        by (auto simp add: dist_norm)
      show "winding_number (n_circ 0) p'=0 \<and> p'\<notin>path_image (n_circ 0)" when "p'\<notin>S- pts" for p'
        unfolding n_circ_def p_circ_pt_def
        apply (auto intro!:winding_number_trivial)
        by (metis Diff_iff pathfinish_in_path_image pg(3) pg(4) subsetCE subset_insertI that)+
      show "f contour_integrable_on (n_circ 0)"
        unfolding n_circ_def p_circ_pt_def
        by (auto intro!:contour_integrable_continuous_linepath simp add:continuous_on_sing)
      show "contour_integral (n_circ 0) f = of_nat 0  *  contour_integral p_circ f"
        unfolding n_circ_def p_circ_pt_def by auto
    next
      case (Suc k)
      have n_Suc:"n_circ (Suc k) = p_circ +++ n_circ k" unfolding n_circ_def by auto
      have pcirc:"p \<notin> path_image p_circ" "valid_path p_circ" "pathfinish p_circ = pathstart (n_circ k)"
        using Suc(3) unfolding p_circ_def using \<open>h p > 0\<close> by (auto simp add: p_circ_def)
      have pcirc_image:"path_image p_circ \<subseteq> S - insert p pts"
        proof -
          have "path_image p_circ \<subseteq> cball p (h p)" using \<open>0 < h p\<close> p_circ_def by auto
          then show ?thesis using h_p pcirc(1) by auto
        qed
      have pcirc_integrable:"f contour_integrable_on p_circ"
        by (auto simp add:p_circ_def intro!: pcirc_image[unfolded p_circ_def]
          contour_integrable_continuous_circlepath holomorphic_on_imp_continuous_on
          holomorphic_on_subset[OF holo])
      show "valid_path (n_circ (Suc k))"
        using valid_path_join[OF pcirc(2) Suc(1) pcirc(3)] unfolding n_circ_def by auto
      show "path_image (n_circ (Suc k))
          = (if Suc k = 0 then {p + complex_of_real (h p)} else sphere p (h p))"
        proof -
          have "path_image p_circ = sphere p (h p)"
            unfolding p_circ_def using \<open>0 < h p\<close> by auto
          then show ?thesis unfolding n_Suc  using Suc.hyps(5)  \<open>h p>0\<close>
            by (auto simp add:  path_image_join[OF pcirc(3)]  dist_norm)
        qed
      then show "p \<notin> path_image (n_circ (Suc k))" using \<open>h p>0\<close> by auto
      show "winding_number (n_circ (Suc k)) p = of_nat (Suc k)"
        proof -
          have "winding_number p_circ p = 1"
            by (simp add: \<open>h p > 0\<close> p_circ_def winding_number_circlepath_centre)
          moreover have "p \<notin> path_image (n_circ k)" using Suc(5) \<open>h p>0\<close> by auto
          then have "winding_number (p_circ +++ n_circ k) p
              = winding_number p_circ p + winding_number (n_circ k) p"
            using  valid_path_imp_path Suc.hyps(1) Suc.hyps(2) pcirc
            apply (intro winding_number_join)
            by auto
          ultimately show ?thesis using Suc(2) unfolding n_circ_def
            by auto
        qed
      show "pathstart (n_circ (Suc k)) = p + h p"
        by (simp add: n_circ_def p_circ_def)
      show "pathfinish (n_circ (Suc k)) = p + h p"
        using Suc(4) unfolding n_circ_def by auto
      show "winding_number (n_circ (Suc k)) p'=0 \<and>  p'\<notin>path_image (n_circ (Suc k))" when "p'\<notin>S-pts" for p'
        proof -
          have " p' \<notin> path_image p_circ" using \<open>p \<in> S\<close> h p_circ_def that using pcirc_image by blast
          moreover have "p' \<notin> path_image (n_circ k)"
            using Suc.hyps(7) that by blast
          moreover have "winding_number p_circ p' = 0"
            proof -
              have "path_image p_circ \<subseteq> cball p (h p)"
                using h unfolding p_circ_def using \<open>p \<in> S\<close> by fastforce
              moreover have "p'\<notin>cball p (h p)" using \<open>p \<in> S\<close> h that "2.hyps"(2) by fastforce
              ultimately show ?thesis 
                unfolding p_circ_def
                by (intro winding_number_zero_outside) auto
            qed
          ultimately show ?thesis
            unfolding n_Suc using Suc.hyps pcirc
            by (metis add.right_neutral not_in_path_image_join that valid_path_imp_path winding_number_join)
        qed
      show "f contour_integrable_on (n_circ (Suc k))"
        unfolding n_Suc
        by (rule contour_integrable_joinI[OF pcirc_integrable Suc(8) pcirc(2) Suc(1)])
      show "contour_integral (n_circ (Suc k)) f = (Suc k) *  contour_integral p_circ f"
        by (simp add: Rings.ring_distribs(2) Suc.hyps n_Suc pcirc pcirc_integrable)
    qed
  have cp[simp]:"pathstart cp = p + h p"  "pathfinish cp = p + h p"
         "valid_path cp" "path_image cp \<subseteq> S - insert p pts"
         "winding_number cp p = - n"
         "\<And>p'. p'\<notin>S - pts \<Longrightarrow> winding_number cp p'=0 \<and> p' \<notin> path_image cp"
         "f contour_integrable_on cp"
         "contour_integral cp f = - n * contour_integral p_circ f"
    proof -
      show "pathstart cp = p + h p" and "pathfinish cp = p + h p" and "valid_path cp"
        using n_circ unfolding cp_def by auto
    next
      have "sphere p (h p) \<subseteq>  S - insert p pts"
        using h[rule_format,of p] \<open>insert p pts \<subseteq> S\<close> by force
      moreover  have "p + complex_of_real (h p) \<in> S - insert p pts"
        using pg(3) pg(4) by (metis pathfinish_in_path_image subsetCE)
      ultimately show "path_image cp \<subseteq>  S - insert p pts" unfolding cp_def
        using n_circ(5)  by auto
    next
      show "winding_number cp p = - n"
        unfolding cp_def using winding_number_reversepath n_circ \<open>h p>0\<close>
        by (auto simp: valid_path_imp_path)
    next
      show "winding_number cp p'=0 \<and> p' \<notin> path_image cp" when "p'\<notin>S - pts" for p'
      proof -
        have "winding_number (reversepath (n_circ (nat n))) p' = 0"
          using n_circ that
          by (metis add.inverse_neutral valid_path_imp_path winding_number_reversepath)
        then show ?thesis
          using cp_def n_circ(7) that by force
      qed
    next
      show "f contour_integrable_on cp" unfolding cp_def
        using contour_integrable_reversepath_eq n_circ(1,8) by auto
    next
      show "contour_integral cp f = - n * contour_integral p_circ f"
        unfolding cp_def using contour_integral_reversepath[OF n_circ(1)] n_circ(9)
        by auto
    qed
  define g' where "g' \<equiv> g +++ pg +++ cp +++ (reversepath pg)"
  have "contour_integral g' f = (\<Sum>p\<in>pts. winding_number g' p * contour_integral (circlepath p (h p)) f)"
    proof (rule "2.hyps"(3)[of "S-{p}" "g'",OF _ _ \<open>finite pts\<close> ])
      show "connected (S - {p} - pts)" using connected by (metis Diff_insert2)
      show "open (S - {p})" using \<open>open S\<close> by auto
      show " pts \<subseteq> S - {p}" using \<open>insert p pts \<subseteq> S\<close> \<open> p \<notin> pts\<close>  by blast
      show "f holomorphic_on S - {p} - pts" using holo \<open>p \<notin> pts\<close> by (metis Diff_insert2)
      show "valid_path g'"
        unfolding g'_def cp_def using n_circ valid pg g_loop
        by (auto intro!:valid_path_join)
      show "pathfinish g' = pathstart g'"
        unfolding g'_def cp_def using pg(2) by simp
      show "path_image g' \<subseteq> S - {p} - pts"
        proof -
          define s' where "s' \<equiv> S - {p} - pts"
          have s':"s' = S-insert p pts " unfolding s'_def by auto
          then show ?thesis using path_img pg(4) cp(4)
            by (simp add: g'_def s'_def subset_path_image_join)
        qed
      note path_join_imp[simp]
      show "\<forall>z. z \<notin> S - {p} \<longrightarrow> winding_number g' z = 0"
        proof clarify
          fix z assume z:"z\<notin>S - {p}"
          have z_notin_cp: "z \<notin> path_image cp"
            using cp(6) cp_def n_circ(6) z by auto
          have z_notin_pg: "z \<notin> path_image pg"
            by (metis Diff_iff Diff_insert2 pg(4) subsetD z)
          have "winding_number (g +++ pg +++ cp +++ reversepath pg) z = winding_number g z
              + winding_number (pg +++ cp +++ (reversepath pg)) z"
            proof (rule winding_number_join)
              show "path g" using \<open>valid_path g\<close> by (simp add: valid_path_imp_path)
              show "z \<notin> path_image g" using z path_img by auto
              show "path (pg +++ cp +++ reversepath pg)" using pg(3) cp
                by (simp add: valid_path_imp_path)
            next
              have "path_image (pg +++ cp +++ reversepath pg) \<subseteq> S - insert p pts"
                using pg(4) cp(4) by (auto simp:subset_path_image_join)
              then show "z \<notin> path_image (pg +++ cp +++ reversepath pg)" using z by auto
            next
              show "pathfinish g = pathstart (pg +++ cp +++ reversepath pg)" using g_loop by auto
            qed
          also have "\<dots> = winding_number g z + (winding_number pg z
              + winding_number (cp +++ (reversepath pg)) z)"
            proof (subst add_left_cancel,rule winding_number_join)
              show "path pg" and "path (cp +++ reversepath pg)"
               and "pathfinish pg = pathstart (cp +++ reversepath pg)"
                by (auto simp add: valid_path_imp_path)
              show "z \<notin> path_image pg" using pg(4) z by blast
              show "z \<notin> path_image (cp +++ reversepath pg)" using z
                by (metis Diff_iff \<open>z \<notin> path_image pg\<close> contra_subsetD cp(4) insertI1
                  not_in_path_image_join path_image_reversepath singletonD)
            qed
          also have "\<dots> = winding_number g z + (winding_number pg z
              + (winding_number cp z + winding_number (reversepath pg) z))"
            by (simp add: valid_path_imp_path winding_number_join z_notin_cp z_notin_pg)
          also have "\<dots> = winding_number g z + winding_number cp z"
            by (simp add: valid_path_imp_path winding_number_reversepath z_notin_pg)
          finally have "winding_number g' z = winding_number g z + winding_number cp z"
            unfolding g'_def .
          moreover have "winding_number g z + winding_number cp z = 0"
            using winding z \<open>n=winding_number g p\<close> by auto
          ultimately show "winding_number g' z = 0" unfolding g'_def by auto
        qed
      show "\<forall>pa \<in> S - {p}. 0 < h pa \<and> (\<forall>w\<in>cball pa (h pa). w \<in> S - {p} \<and> (w \<noteq> pa \<longrightarrow> w \<notin> pts))"
        using h by fastforce
    qed
  moreover have "contour_integral g' f = contour_integral g f
      - winding_number g p * contour_integral p_circ f"
  proof -
    have *: "f contour_integrable_on g" "f contour_integrable_on pg" "f contour_integrable_on cp"
        by (auto simp add: open_Diff[OF \<open>open S\<close>,OF finite_imp_closed[OF fin]]
                 intro!: contour_integrable_holomorphic_simple[OF holo _ _ path_img])
      have "contour_integral g' f = contour_integral g f + contour_integral pg f
          + contour_integral cp f + contour_integral (reversepath pg) f"
        using * by (simp add: g'_def contour_integrable_reversepath_eq)
      also have "\<dots> = contour_integral g f + contour_integral cp f"
        using contour_integral_reversepath
        by (auto simp add:contour_integrable_reversepath)
      also have "\<dots> = contour_integral g f - winding_number g p * contour_integral p_circ f"
        using \<open>n=winding_number g p\<close> by auto
      finally show ?thesis .
    qed
  moreover have "winding_number g' p' = winding_number g p'" when "p'\<in>pts" for p'
    proof -
      obtain [simp]: "p' \<notin> path_image g" "p' \<notin> path_image pg" "p'\<notin>path_image cp"
        using "2.prems"(8) that by (metis Diff_iff Diff_insert2 \<open>p' \<in> pts\<close> cp(4) pg(4) subsetD)
      have "winding_number g' p' = winding_number g p' + winding_number pg p'
          + winding_number (cp +++ reversepath pg) p'"
        by (simp add: g'_def not_in_path_image_join valid_path_imp_path winding_number_join)
      also have "\<dots> = winding_number g p'" using that
        by (simp add: valid_path_imp_path winding_number_join winding_number_reversepath)
      finally show ?thesis .
    qed
  ultimately show ?case unfolding p_circ_def
    apply (subst (asm) sum.cong[OF refl,
        of pts _ "\<lambda>p. winding_number g p * contour_integral (circlepath p (h p)) f"])
    by (auto simp: sum.insert[OF \<open>finite pts\<close> \<open>p\<notin>pts\<close>] algebra_simps)
qed

lemma Cauchy_theorem_singularities:
  assumes "open S" "connected S" "finite pts" and
          holo: "f holomorphic_on S-pts" and
          "valid_path g" and
          loop:"pathfinish g = pathstart g" and
          "path_image g \<subseteq> S-pts" and
          homo:"\<forall>z. (z \<notin> S) \<longrightarrow> winding_number g z  = 0" and
          avoid:"\<forall>p\<in>S. h p>0 \<and> (\<forall>w\<in>cball p (h p). w\<in>S \<and> (w\<noteq>p \<longrightarrow> w \<notin> pts))"
  shows "contour_integral g f = (\<Sum>p\<in>pts. winding_number g p * contour_integral (circlepath p (h p)) f)"
    (is "?L=?R")
proof -
  define circ where "circ \<equiv> \<lambda>p. winding_number g p * contour_integral (circlepath p (h p)) f"
  define pts1 where "pts1 \<equiv> pts \<inter> S"
  define pts2 where "pts2 \<equiv> pts - pts1"
  have "pts=pts1 \<union> pts2" "pts1 \<inter> pts2 = {}" "pts2 \<inter> S={}" "pts1\<subseteq>S"
    unfolding pts1_def pts2_def by auto
  have "contour_integral g f =  (\<Sum>p\<in>pts1. circ p)" unfolding circ_def
    proof (rule Cauchy_theorem_aux[OF \<open>open S\<close> _ _ \<open>pts1\<subseteq>S\<close> _ \<open>valid_path g\<close> loop _ homo])
      have "finite pts1" unfolding pts1_def using \<open>finite pts\<close> by auto
      then show "connected (S - pts1)"
        using \<open>open S\<close> \<open>connected S\<close> connected_open_delete_finite[of S] by auto
    next
      show "finite pts1" using \<open>pts = pts1 \<union> pts2\<close> assms(3) by auto
      show "f holomorphic_on S - pts1" by (metis Diff_Int2 Int_absorb holo pts1_def)
      show "path_image g \<subseteq> S - pts1" using assms(7) pts1_def by auto
      show "\<forall>p\<in>S. 0 < h p \<and> (\<forall>w\<in>cball p (h p). w \<in> S \<and> (w \<noteq> p \<longrightarrow> w \<notin> pts1))"
        by (simp add: avoid pts1_def)
    qed
  moreover have "sum circ pts2 = 0"
    by (metis \<open>pts2 \<inter> S = {}\<close> circ_def disjoint_iff_not_equal homo mult_zero_left sum.neutral)
  moreover have "?R=sum circ pts1 + sum circ pts2"
    unfolding circ_def
    using sum.union_disjoint[OF _ _ \<open>pts1 \<inter> pts2 = {}\<close>] \<open>finite pts\<close> \<open>pts=pts1 \<union> pts2\<close>
    by blast
  ultimately show ?thesis
    by simp
qed

theorem Residue_theorem:
  fixes S pts::"complex set" and f::"complex \<Rightarrow> complex"
    and g::"real \<Rightarrow> complex"
  assumes "open S" "connected S" "finite pts" and
          holo:"f holomorphic_on S-pts" and
          "valid_path g" and
          loop:"pathfinish g = pathstart g" and
          "path_image g \<subseteq> S-pts" and
          homo:"\<forall>z. (z \<notin> S) \<longrightarrow> winding_number g z  = 0"
  shows "contour_integral g f = 2 * pi * \<i> *(\<Sum>p\<in>pts. winding_number g p * residue f p)"
proof -
  define c where "c \<equiv>  2 * pi * \<i>"
  obtain h where avoid:"\<forall>p\<in>S. h p>0 \<and> (\<forall>w\<in>cball p (h p). w\<in>S \<and> (w\<noteq>p \<longrightarrow> w \<notin> pts))"
    using finite_cball_avoid[OF \<open>open S\<close> \<open>finite pts\<close>] by metis
  have "contour_integral g f
      = (\<Sum>p\<in>pts. winding_number g p * contour_integral (circlepath p (h p)) f)"
    using Cauchy_theorem_singularities[OF assms avoid] .
  also have "\<dots> = (\<Sum>p\<in>pts.  c * winding_number g p * residue f p)"
    proof (intro sum.cong)
      show "pts = pts" by simp
    next
      fix x assume "x \<in> pts"
      show "winding_number g x * contour_integral (circlepath x (h x)) f
          = c * winding_number g x * residue f x"
        proof (cases "x\<in>S")
          case False
          then have "winding_number g x=0" using homo by auto
          thus ?thesis by auto
        next
          case True
          have "contour_integral (circlepath x (h x)) f = c* residue f x"
            using \<open>x\<in>pts\<close> \<open>finite pts\<close> avoid[rule_format, OF True]
            apply (intro base_residue[of "S-(pts-{x})",THEN contour_integral_unique,folded c_def])
            by (auto intro:holomorphic_on_subset[OF holo] open_Diff[OF \<open>open S\<close> finite_imp_closed])
          then show ?thesis by auto
        qed
    qed
  also have "\<dots> = c * (\<Sum>p\<in>pts. winding_number g p * residue f p)"
    by (simp add: sum_distrib_left algebra_simps)
  finally show ?thesis unfolding c_def .
qed

subsection \<open>The argument principle\<close>

theorem argument_principle:
  fixes f::"complex \<Rightarrow> complex" and poles S:: "complex set"
  defines "pz \<equiv> {w\<in>S. f w = 0 \<or> w \<in> poles}" \<comment> \<open>\<^term>\<open>pz\<close> is the set of poles and zeros\<close>
  assumes "open S" "connected S" and
          f_holo:"f holomorphic_on S-poles" and
          h_holo:"h holomorphic_on S" and
          "valid_path g" and
          loop:"pathfinish g = pathstart g" and
          path_img:"path_image g \<subseteq> S - pz" and
          homo:"\<forall>z. (z \<notin> S) \<longrightarrow> winding_number g z = 0" and
          finite:"finite pz" and
          poles:"\<forall>p\<in>S\<inter>poles. is_pole f p"
  shows "contour_integral g (\<lambda>x. deriv f x * h x / f x) = 2 * pi * \<i> *
          (\<Sum>p\<in>pz. winding_number g p * h p * zorder f p)"
    (is "?L=?R")
proof -
  define c where "c \<equiv> 2 * complex_of_real pi * \<i> "
  define ff where "ff \<equiv> (\<lambda>x. deriv f x * h x / f x)"
  define cont where "cont \<equiv> \<lambda>ff p e. (ff has_contour_integral c * zorder f p * h p ) (circlepath p e)"
  define avoid where "avoid \<equiv> \<lambda>p e. \<forall>w\<in>cball p e. w \<in> S \<and> (w \<noteq> p \<longrightarrow> w \<notin> pz)"

  have "\<exists>e>0. avoid p e \<and> (p\<in>pz \<longrightarrow> cont ff p e)" when "p\<in>S" for p
  proof -
    obtain e1 where "e1>0" and e1_avoid:"avoid p e1"
      using finite_cball_avoid[OF \<open>open S\<close> finite] \<open>p\<in>S\<close> unfolding avoid_def by auto
    have "\<exists>e2>0. cball p e2 \<subseteq> ball p e1 \<and> cont ff p e2" when "p\<in>pz"
    proof -
      define po where "po \<equiv> zorder f p"
      define pp where "pp \<equiv> zor_poly f p"
      define f' where "f' \<equiv> \<lambda>w. pp w * (w - p) powi po"
      define ff' where "ff' \<equiv> (\<lambda>x. deriv f' x * h x / f' x)"
      obtain r where "pp p\<noteq>0" "r>0" and
          "r<e1" and
          pp_holo:"pp holomorphic_on cball p r" and
          pp_po:"(\<forall>w\<in>cball p r-{p}. f w = pp w * (w - p) powi po \<and> pp w \<noteq> 0)"
      proof -
        have "isolated_singularity_at f p"
        proof -
          have "ball p e1 - {p} \<subseteq> S - poles"
            using avoid_def e1_avoid pz_def by fastforce
          then have "f holomorphic_on ball p e1 - {p}"
            by (intro holomorphic_on_subset[OF f_holo])
          then show ?thesis unfolding isolated_singularity_at_def
            using \<open>e1>0\<close> analytic_on_open open_delete by blast
        qed
        moreover have "not_essential f p"
        proof (cases "is_pole f p")
          case True
          then show ?thesis unfolding not_essential_def by auto
        next
          case False
          then have "p\<in>S-poles" using \<open>p\<in>S\<close> poles unfolding pz_def by auto
          moreover have "open (S-poles)"
          proof -
            have "closed (S \<inter> poles)"
              using finite by (simp add: pz_def finite_imp_closed rev_finite_subset subset_eq)
            then show ?thesis
              by (metis Diff_Compl Diff_Diff_Int Diff_eq \<open>open S\<close> open_Diff) 
          qed
          ultimately have "isCont f p"
            using holomorphic_on_imp_continuous_on[OF f_holo] continuous_on_eq_continuous_at
            by auto
          then show ?thesis unfolding isCont_def not_essential_def by auto
        qed
        moreover have "\<exists>\<^sub>F w in at p. f w \<noteq> 0 "
        proof (rule ccontr)
          assume "\<not> (\<exists>\<^sub>F w in at p. f w \<noteq> 0)"
          then have "\<forall>\<^sub>F w in at p. f w= 0" unfolding frequently_def by auto
          then obtain r1 where "r1>0" and r1:"\<forall>w\<in>ball p r1 - {p}. f w =0"
            unfolding eventually_at by (auto simp add:dist_commute)
          obtain r2 where "r2>0" and r2: "ball p r2 \<subseteq> S"
            using \<open>p\<in>S\<close> \<open>open S\<close> openE by blast
          define rr where "rr=min r1 r2"

          from r1 r2
          have "ball p rr - {p} \<subseteq> {w\<in> S \<inter> ball p rr-{p}. f w=0}"
            unfolding rr_def by auto
          moreover have "infinite (ball p rr - {p})" 
            using \<open>r1>0\<close> \<open>r2>0\<close> finite_imp_not_open 
            unfolding rr_def by fastforce
          ultimately have "infinite {w\<in>S \<inter> ball p rr-{p}. f w=0}" using infinite_super by blast
          then have "infinite pz"
            unfolding pz_def by (smt (verit) infinite_super Collect_mono_iff DiffE Int_iff)
          then show False using \<open>finite pz\<close> by auto
        qed
        ultimately obtain r where "pp p \<noteq> 0" and r:"r>0" "pp holomorphic_on cball p r"
                  "(\<forall>w\<in>cball p r - {p}. f w = pp w * (w - p) powi po \<and> pp w \<noteq> 0)"
          using zorder_exist[of f p,folded po_def pp_def] by auto
        define r1 where "r1=min r e1 / 2"
        have "r1<e1" unfolding r1_def using \<open>e1>0\<close> \<open>r>0\<close> by auto
        moreover have "r1>0" "pp holomorphic_on cball p r1"
                  "(\<forall>w\<in>cball p r1 - {p}. f w = pp w * (w - p) powi po \<and> pp w \<noteq> 0)"
          unfolding r1_def using \<open>e1>0\<close> r by auto
        ultimately show ?thesis using that \<open>pp p\<noteq>0\<close> by auto
      qed

      define e2 where "e2 \<equiv> r/2"
      have "e2>0" using \<open>r>0\<close> unfolding e2_def by auto
      define anal where "anal \<equiv> \<lambda>w. deriv pp w * h w / pp w"
      define prin where "prin \<equiv> \<lambda>w. po * h w / (w - p)"
      have "((\<lambda>w.  prin w + anal w) has_contour_integral c * po * h p) (circlepath p e2)"
      proof (rule has_contour_integral_add[of _ _ _ _ 0,simplified])
        have "ball p r \<subseteq> S"
          using \<open>r<e1\<close> avoid_def ball_subset_cball e1_avoid by (simp add: subset_eq)
        then have "cball p e2 \<subseteq> S"
          using \<open>r>0\<close> unfolding e2_def by auto
        then have "(\<lambda>w. po * h w) holomorphic_on cball p e2"
          using h_holo by (auto intro!: holomorphic_intros)
        then show "(prin has_contour_integral c * po * h p ) (circlepath p e2)"
          using Cauchy_integral_circlepath_simple[folded c_def, of "\<lambda>w. po * h w"] \<open>e2>0\<close>
          unfolding prin_def by (auto simp add: mult.assoc)
        have "anal holomorphic_on ball p r" unfolding anal_def
          using pp_holo h_holo pp_po \<open>ball p r \<subseteq> S\<close> \<open>pp p\<noteq>0\<close>
          by (auto intro!: holomorphic_intros)
        then show "(anal has_contour_integral 0) (circlepath p e2)"
          using e2_def \<open>r>0\<close>
          by (auto elim!: Cauchy_theorem_disc_simple)
      qed
      then have "cont ff' p e2" unfolding cont_def po_def
      proof (elim has_contour_integral_eq)
        fix w assume "w \<in> path_image (circlepath p e2)"
        then have "w\<in>ball p r" and "w\<noteq>p" unfolding e2_def using \<open>r>0\<close> by auto
        define wp where "wp \<equiv> w-p"
        have "wp\<noteq>0" and "pp w \<noteq>0"
          unfolding wp_def using \<open>w\<noteq>p\<close> \<open>w\<in>ball p r\<close> pp_po by auto
        moreover have der_f':"deriv f' w = po * pp w * (w-p) powi (po - 1) + deriv pp w * (w-p) powi po"
        proof (rule DERIV_imp_deriv)
          have "(pp has_field_derivative (deriv pp w)) (at w)"
            using DERIV_deriv_iff_has_field_derivative pp_holo \<open>w\<noteq>p\<close>
            by (meson open_ball \<open>w \<in> ball p r\<close> ball_subset_cball holomorphic_derivI holomorphic_on_subset)
          then show " (f' has_field_derivative of_int po * pp w * (w - p) powi (po - 1)
                  + deriv pp w * (w - p) powi po) (at w)"
            unfolding f'_def using \<open>w\<noteq>p\<close>
            by (auto intro!: derivative_eq_intros DERIV_cong[OF has_field_derivative_powr_of_int])
        qed
        ultimately show "prin w + anal w = ff' w"
          unfolding f'_def ff'_def prin_def anal_def
          apply (simp add: field_simps flip: wp_def)
          by (metis (no_types, lifting) mult.commute power_int_minus_mult)
      qed
      then have "cont ff p e2" unfolding cont_def
      proof (elim has_contour_integral_eq)
        fix w assume "w \<in> path_image (circlepath p e2)"
        then have "w\<in>ball p r" and "w\<noteq>p" unfolding e2_def using \<open>r>0\<close> by auto
        have "deriv f' w =  deriv f w"
        proof (rule complex_derivative_transform_within_open[where s="ball p r - {p}"])
          show "f' holomorphic_on ball p r - {p}" unfolding f'_def using pp_holo
            by (auto intro!: holomorphic_intros)
        next
          have "ball p e1 - {p} \<subseteq> S - poles"
            using ball_subset_cball e1_avoid[unfolded avoid_def] unfolding pz_def
            by auto
          then have "ball p r - {p} \<subseteq> S - poles"
            using \<open>r<e1\<close> by force
          then show "f holomorphic_on ball p r - {p}" using f_holo
            by auto
        next
          show "open (ball p r - {p})" by auto
          show "w \<in> ball p r - {p}" using \<open>w\<in>ball p r\<close> \<open>w\<noteq>p\<close> by auto
        next
          fix x assume "x \<in> ball p r - {p}"
          then show "f' x = f x"
            using pp_po unfolding f'_def by auto
        qed
        moreover have " f' w  =  f w "
          using \<open>w \<in> ball p r\<close> ball_subset_cball subset_iff pp_po \<open>w\<noteq>p\<close>
          unfolding f'_def by auto
        ultimately show "ff' w = ff w"
          unfolding ff'_def ff_def by simp
      qed
      moreover have "cball p e2 \<subseteq> ball p e1"
        using \<open>0 < r\<close> \<open>r<e1\<close> e2_def by auto
      ultimately show ?thesis using \<open>e2>0\<close> by auto
    qed
    then obtain e2 where e2:"p\<in>pz \<longrightarrow> e2>0 \<and> cball p e2 \<subseteq> ball p e1 \<and> cont ff p e2"
      by auto
    define e4 where "e4 \<equiv> if p\<in>pz then e2 else  e1"
    have "e4>0" using e2 \<open>e1>0\<close> unfolding e4_def by auto
    moreover have "avoid p e4" using e2 \<open>e1>0\<close> e1_avoid unfolding e4_def avoid_def by auto
    moreover have "p\<in>pz \<longrightarrow> cont ff p e4"
      by (auto simp add: e2 e4_def)
    ultimately show ?thesis by auto
  qed
  then obtain get_e where get_e:"\<forall>p\<in>S. get_e p>0 \<and> avoid p (get_e p)
      \<and> (p\<in>pz \<longrightarrow> cont ff p (get_e p))"
    by metis
  define ci where "ci \<equiv> \<lambda>p. contour_integral (circlepath p (get_e p)) ff"
  define w where "w \<equiv> \<lambda>p. winding_number g p"
  have "contour_integral g ff = (\<Sum>p\<in>pz. w p * ci p)" unfolding ci_def w_def
  proof (rule Cauchy_theorem_singularities[OF \<open>open S\<close> \<open>connected S\<close> finite _ \<open>valid_path g\<close> loop
        path_img homo])
    have "open (S - pz)" using open_Diff[OF _ finite_imp_closed[OF finite]] \<open>open S\<close> by auto
    then show "ff holomorphic_on S - pz" unfolding ff_def using f_holo h_holo
      by (auto intro!: holomorphic_intros simp add:pz_def)
  next
    show "\<forall>p\<in>S. 0 < get_e p \<and> (\<forall>w\<in>cball p (get_e p). w \<in> S \<and> (w \<noteq> p \<longrightarrow> w \<notin> pz))"
      using get_e using avoid_def by blast
  qed
  also have "\<dots> = (\<Sum>p\<in>pz. c * w p * h p * zorder f p)"
  proof (rule sum.cong[of pz pz,simplified])
    fix p assume "p \<in> pz"
    show "w p * ci p = c * w p * h p * (zorder f p)"
    proof (cases "p\<in>S")
      assume "p \<in> S"
      have "ci p = c * h p * (zorder f p)" 
        unfolding ci_def
        using \<open>p \<in> S\<close> \<open>p \<in> pz\<close> cont_def contour_integral_unique get_e by fastforce
      thus ?thesis by auto
    next
      assume "p\<notin>S"
      then have "w p=0" using homo unfolding w_def by auto
      then show ?thesis by auto
    qed
  qed
  also have "\<dots> = c*(\<Sum>p\<in>pz. w p * h p * zorder f p)"
    unfolding sum_distrib_left by (simp add:algebra_simps)
  finally have "contour_integral g ff = c * (\<Sum>p\<in>pz. w p * h p * of_int (zorder f p))" .
  then show ?thesis unfolding ff_def c_def w_def by simp
qed


subsection \<open>Coefficient asymptotics for generating functions\<close>

text \<open>
  For a formal power series that has a meromorphic continuation on some disc in the
  context plane, we can use the Residue Theorem to extract precise asymptotic information
  from the residues at the poles. This can be used to derive the asymptotic behaviour
  of the coefficients (\<open>a\<^sub>n \<sim> \<dots>\<close>). If the function is meromorphic on the entire 
  complex plane, one can even derive a full asymptotic expansion.

  We will first show the relationship between the coefficients and the sum over the residues
  with an explicit remainder term (the contour integral along the circle used in the
  Residue theorem).
\<close>
theorem
  fixes f :: "complex \<Rightarrow> complex" and n :: nat and r :: real
  defines "g \<equiv> (\<lambda>w. f w / w ^ Suc n)" and "\<gamma> \<equiv> circlepath 0 r"
  assumes "open A" "connected A" "cball 0 r \<subseteq> A" "r > 0" 
  assumes "f holomorphic_on A - S" "S \<subseteq> ball 0 r" "finite S" "0 \<notin> S"
  shows   fps_coeff_conv_residues:
            "(deriv ^^ n) f 0 / fact n = 
                contour_integral \<gamma> g / (2 * pi * \<i>) - (\<Sum>z\<in>S. residue g z)" (is ?thesis1)
    and   fps_coeff_residues_bound:
            "(\<And>z. norm z = r \<Longrightarrow> z \<notin> k \<Longrightarrow> norm (f z) \<le> C) \<Longrightarrow> C \<ge> 0 \<Longrightarrow> finite k \<Longrightarrow>
               norm ((deriv ^^ n) f 0 / fact n + (\<Sum>z\<in>S. residue g z)) \<le> C / r ^ n"
proof -
  have holo: "g holomorphic_on A - insert 0 S"
    unfolding g_def using assms by (auto intro!: holomorphic_intros)
  have "contour_integral \<gamma> g = 2 * pi * \<i> * (\<Sum>z\<in>insert 0 S. winding_number \<gamma> z * residue g z)"
  proof (rule Residue_theorem)
    show "g holomorphic_on A - insert 0 S" by fact
    from assms show "\<forall>z. z \<notin> A \<longrightarrow> winding_number \<gamma> z = 0"
      unfolding \<gamma>_def by (intro allI impI winding_number_zero_outside[of _ "cball 0 r"]) auto
  qed (insert assms, auto simp: \<gamma>_def)
  also have "winding_number \<gamma> z = 1" if "z \<in> insert 0 S" for z
    unfolding \<gamma>_def using assms that by (intro winding_number_circlepath) auto
  hence "(\<Sum>z\<in>insert 0 S. winding_number \<gamma> z * residue g z) = (\<Sum>z\<in>insert 0 S. residue g z)"
    by (intro sum.cong) simp_all
  also have "\<dots> = residue g 0 + (\<Sum>z\<in>S. residue g z)" 
    using \<open>0 \<notin> S\<close> and \<open>finite S\<close> by (subst sum.insert) auto
  also from \<open>r > 0\<close> have "0 \<in> cball 0 r" by simp
  with assms have "0 \<in> A - S" by blast
  with assms have "residue g 0 = (deriv ^^ n) f 0 / fact n"
    unfolding g_def by (subst residue_holomorphic_over_power'[of "A - S"])
                       (auto simp: finite_imp_closed)
  finally show ?thesis1
    by (simp add: field_simps)

  assume C: "\<And>z. norm z = r \<Longrightarrow> z \<notin> k \<Longrightarrow> norm (f z) \<le> C" "C \<ge> 0" and k: "finite k"
  have "(deriv ^^ n) f 0 / fact n + (\<Sum>z\<in>S. residue g z) = contour_integral \<gamma> g / (2 * pi * \<i>)"
    using \<open>?thesis1\<close> by (simp add: algebra_simps)
  also have "norm \<dots> = norm (contour_integral \<gamma> g) / (2 * pi)"
    by (simp add: norm_divide norm_mult)
  also have "norm (contour_integral \<gamma> g) \<le> C / r ^ Suc n * (2 * pi * r)"
  proof (rule has_contour_integral_bound_circlepath_strong)
    from \<open>open A\<close> and \<open>finite S\<close> have "open (A - insert 0 S)"
      by (blast intro: finite_imp_closed)
    with assms show "(g has_contour_integral contour_integral \<gamma> g) (circlepath 0 r)"
      unfolding \<gamma>_def
      by (intro has_contour_integral_integral contour_integrable_holomorphic_simple [OF holo]) auto
  next
    fix z assume z: "norm (z - 0) = r" "z \<notin> k"
    hence "norm (g z) = norm (f z) / r ^ Suc n"
      by (simp add: norm_divide g_def norm_mult norm_power)
    also have "\<dots> \<le> C / r ^ Suc n" 
      using k and \<open>r > 0\<close> and z by (intro divide_right_mono C zero_le_power) auto
    finally show "norm (g z) \<le> C / r ^ Suc n" .
  qed (insert C(2) k \<open>r > 0\<close>, auto)
  also from \<open>r > 0\<close> have "C / r ^ Suc n * (2 * pi * r) / (2 * pi) = C / r ^ n"
    by simp
  finally show "norm ((deriv ^^ n) f 0 / fact n + (\<Sum>z\<in>S. residue g z)) \<le> \<dots>"
    by - (simp_all add: divide_right_mono)
qed

text \<open>
  Since the circle is fixed, we can get an upper bound on the values of the generating
  function on the circle and therefore show that the integral is $O(r^{-n})$.
\<close>
corollary fps_coeff_residues_bigo:
  fixes f :: "complex \<Rightarrow> complex" and r :: real
  assumes "open A" "connected A" "cball 0 r \<subseteq> A" "r > 0" 
  assumes "f holomorphic_on A - S" "S \<subseteq> ball 0 r" "finite S" "0 \<notin> S"
  assumes g: "eventually (\<lambda>n. g n = -(\<Sum>z\<in>S. residue (\<lambda>z. f z / z ^ Suc n) z)) sequentially"
                (is "eventually (\<lambda>n. _ = -?g' n) _")
  shows   "(\<lambda>n. (deriv ^^ n) f 0 / fact n - g n) \<in> O(\<lambda>n. 1 / r ^ n)" (is "(\<lambda>n. ?c n - _) \<in> O(_)")
proof -
  from assms have "compact (f ` sphere 0 r)"
    by (intro compact_continuous_image holomorphic_on_imp_continuous_on
              holomorphic_on_subset[OF \<open>f holomorphic_on A - S\<close>]) auto
  hence "bounded (f ` sphere 0 r)" by (rule compact_imp_bounded)
  then obtain C where C: "\<And>z. z \<in> sphere 0 r \<Longrightarrow> norm (f z) \<le> C"
    by (auto simp: bounded_iff sphere_def)
  have "0 \<le> norm (f (of_real r))" by simp
  also from C[of "of_real r"] and \<open>r > 0\<close> have "\<dots> \<le> C" by simp
  finally have C_nonneg: "C \<ge> 0" .

  have "(\<lambda>n. ?c n + ?g' n) \<in> O(\<lambda>n. of_real (1 / r ^ n))"
  proof (intro bigoI[of _ C] always_eventually allI )
    fix n :: nat
    from assms and C and C_nonneg have "norm (?c n + ?g' n) \<le> C / r ^ n"
      by (intro fps_coeff_residues_bound[where A = A and k = "{}"]) auto
    also have "\<dots> = C * norm (complex_of_real (1 / r ^ n))" 
      using \<open>r > 0\<close> by (simp add: norm_divide norm_power)
    finally show "norm (?c n + ?g' n) \<le> \<dots>" .
  qed
  also have "?this \<longleftrightarrow> (\<lambda>n. ?c n - g n) \<in> O(\<lambda>n. of_real (1 / r ^ n))"
    by (intro landau_o.big.in_cong eventually_mono[OF g]) simp_all
  finally show ?thesis .
qed

corollary fps_coeff_residues_bigo':
  fixes f :: "complex \<Rightarrow> complex" and r :: real
  assumes exp: "f has_fps_expansion F"
  assumes "open A" "connected A" "cball 0 r \<subseteq> A" "r > 0" 
  assumes "f holomorphic_on A - S" "S \<subseteq> ball 0 r" "finite S" "0 \<notin> S"
  assumes "eventually (\<lambda>n. g n = -(\<Sum>z\<in>S. residue (\<lambda>z. f z / z ^ Suc n) z)) sequentially"
             (is "eventually (\<lambda>n. _ = -?g' n) _")
  shows   "(\<lambda>n. fps_nth F n - g n) \<in> O(\<lambda>n. 1 / r ^ n)" (is "(\<lambda>n. ?c n - _) \<in> O(_)")
proof -
  have "fps_nth F = (\<lambda>n. (deriv ^^ n) f 0 / fact n)"
    using fps_nth_fps_expansion[OF exp] by (intro ext) simp_all
  with fps_coeff_residues_bigo[OF assms(2-)] show ?thesis by simp
qed

subsection \<open>Rouche's theorem \<close>

theorem Rouche_theorem:
  fixes f g::"complex \<Rightarrow> complex" and s:: "complex set"
  defines "fg\<equiv>(\<lambda>p. f p + g p)"
  defines "zeros_fg\<equiv>{p\<in>s. fg p = 0}" and "zeros_f\<equiv>{p\<in>s. f p = 0}"
  assumes
    "open s" and "connected s" and
    "finite zeros_fg" and
    "finite zeros_f" and
    f_holo:"f holomorphic_on s" and
    g_holo:"g holomorphic_on s" and
    "valid_path \<gamma>" and
    loop:"pathfinish \<gamma> = pathstart \<gamma>" and
    path_img:"path_image \<gamma> \<subseteq> s " and
    path_less:"\<forall>z\<in>path_image \<gamma>. cmod(f z) > cmod(g z)" and
    homo:"\<forall>z. (z \<notin> s) \<longrightarrow> winding_number \<gamma> z = 0"
  shows "(\<Sum>p\<in>zeros_fg. winding_number \<gamma> p * zorder fg p)
          = (\<Sum>p\<in>zeros_f. winding_number \<gamma> p * zorder f p)"
proof -
  have path_fg:"path_image \<gamma> \<subseteq> s - zeros_fg"
  proof -
    have False when "z\<in>path_image \<gamma>" and "f z + g z=0" for z
    proof -
      have "cmod (f z) > cmod (g z)" using \<open>z\<in>path_image \<gamma>\<close> path_less by auto
      moreover have "f z = - g z"  using \<open>f z + g z =0\<close> by (simp add: eq_neg_iff_add_eq_0)
      then have "cmod (f z) = cmod (g z)" by auto
      ultimately show False by auto
    qed
    then show ?thesis unfolding zeros_fg_def fg_def using path_img by auto
  qed
  have path_f:"path_image \<gamma> \<subseteq> s - zeros_f"
  proof -
    have False when "z\<in>path_image \<gamma>" and "f z =0" for z
    proof -
      have "cmod (g z) < cmod (f z) " using \<open>z\<in>path_image \<gamma>\<close> path_less by auto
      then have "cmod (g z) < 0" using \<open>f z=0\<close> by auto
      then show False by auto
    qed
    then show ?thesis unfolding zeros_f_def using path_img by auto
  qed
  define w where "w \<equiv> \<lambda>p. winding_number \<gamma> p"
  define c where "c \<equiv> 2 * complex_of_real pi * \<i>"
  define h where "h \<equiv> \<lambda>p. g p / f p + 1"
  obtain spikes
    where "finite spikes" and spikes: "\<forall>x\<in>{0..1} - spikes. \<gamma> differentiable at x"
    using \<open>valid_path \<gamma>\<close>
    by (auto simp: valid_path_def piecewise_C1_differentiable_on_def C1_differentiable_on_eq)
  have h_contour:"((\<lambda>x. deriv h x / h x) has_contour_integral 0) \<gamma>"
  proof -
    have outside_img:"0 \<in> outside (path_image (h o \<gamma>))"
    proof -
      have "h p \<in> ball 1 1" when "p\<in>path_image \<gamma>" for p
      proof -
        have "cmod (g p/f p) <1"
          by (smt (verit) divide_less_eq_1_pos norm_divide norm_ge_zero path_less that)
        then show ?thesis 
          unfolding h_def by (auto simp add:dist_complex_def)
      qed
      then have "path_image (h o \<gamma>) \<subseteq> ball 1 1"
        by (simp add: image_subset_iff path_image_compose)
      moreover have " (0::complex) \<notin> ball 1 1" by (simp add: dist_norm)
      ultimately show "?thesis"
        using  convex_in_outside[of "ball 1 1" 0] outside_mono by blast
    qed
    have valid_h:"valid_path (h \<circ> \<gamma>)"
    proof (rule valid_path_compose_holomorphic[OF \<open>valid_path \<gamma>\<close> _ _ path_f])
      show "h holomorphic_on s - zeros_f"
        unfolding h_def using f_holo g_holo
        by (auto intro!: holomorphic_intros simp add:zeros_f_def)
    next
      show "open (s - zeros_f)" using \<open>finite zeros_f\<close> \<open>open s\<close> finite_imp_closed
        by auto
    qed
    have "((\<lambda>z. 1/z) has_contour_integral 0) (h \<circ> \<gamma>)"
    proof -
      have "0 \<notin> path_image (h \<circ> \<gamma>)" using outside_img by (simp add: outside_def)
      then have "((\<lambda>z. 1/z) has_contour_integral c * winding_number (h \<circ> \<gamma>) 0) (h \<circ> \<gamma>)"
        using has_contour_integral_winding_number[of "h o \<gamma>" 0,simplified] valid_h
        unfolding c_def by auto
      moreover have "winding_number (h o \<gamma>) 0 = 0"
      proof -
        have "0 \<in> outside (path_image (h \<circ> \<gamma>))" using outside_img .
        moreover have "path (h o \<gamma>)"
          using valid_h  by (simp add: valid_path_imp_path)
        moreover have "pathfinish (h o \<gamma>) = pathstart (h o \<gamma>)"
          by (simp add: loop pathfinish_compose pathstart_compose)
        ultimately show ?thesis using winding_number_zero_in_outside by auto
      qed
      ultimately show ?thesis by auto
    qed
    moreover have "vector_derivative (h \<circ> \<gamma>) (at x) = vector_derivative \<gamma> (at x) * deriv h (\<gamma> x)"
      when "x\<in>{0..1} - spikes" for x
    proof (rule vector_derivative_chain_at_general)
      show "\<gamma> differentiable at x" using that \<open>valid_path \<gamma>\<close> spikes by auto
    next
      define der where "der \<equiv> \<lambda>p. (deriv g p * f p - g p * deriv f p)/(f p * f p)"
      define t where "t \<equiv> \<gamma> x"
      have "f t\<noteq>0" unfolding zeros_f_def t_def
        by (metis DiffD1 image_eqI norm_not_less_zero norm_zero path_defs(4) path_less that)
      moreover have "t\<in>s"
        using contra_subsetD path_image_def path_fg t_def that by fastforce
      ultimately have "(h has_field_derivative der t) (at t)"
        unfolding h_def der_def using g_holo f_holo \<open>open s\<close>
        by (auto intro!: holomorphic_derivI derivative_eq_intros)
      then show "h field_differentiable at (\<gamma> x)"
        unfolding t_def field_differentiable_def by blast
    qed
    then have " ((/) 1 has_contour_integral 0) (h \<circ> \<gamma>)
                  = ((\<lambda>x. deriv h x / h x) has_contour_integral 0) \<gamma>"
      unfolding has_contour_integral
      by (force intro!: has_integral_spike_eq[OF negligible_finite, OF \<open>finite spikes\<close>])
    ultimately show ?thesis by auto
  qed
  then have "contour_integral \<gamma> (\<lambda>x. deriv h x / h x) = 0"
    using  contour_integral_unique by simp
  moreover have "contour_integral \<gamma> (\<lambda>x. deriv fg x / fg x) = contour_integral \<gamma> (\<lambda>x. deriv f x / f x)
      + contour_integral \<gamma> (\<lambda>p. deriv h p / h p)"
  proof -
    have "(\<lambda>p. deriv f p / f p) contour_integrable_on \<gamma>"
    proof (rule contour_integrable_holomorphic_simple[OF _ _ \<open>valid_path \<gamma>\<close> path_f])
      show "open (s - zeros_f)" 
        using finite_imp_closed[OF \<open>finite zeros_f\<close>] \<open>open s\<close> by auto
      then show "(\<lambda>p. deriv f p / f p) holomorphic_on s - zeros_f"
        using f_holo
        by (auto intro!: holomorphic_intros simp add:zeros_f_def)
    qed
    moreover have "(\<lambda>p. deriv h p / h p) contour_integrable_on \<gamma>"
      using h_contour
      by (simp add: has_contour_integral_integrable)
    ultimately have "contour_integral \<gamma> (\<lambda>x. deriv f x / f x + deriv h x / h x) =
                        contour_integral \<gamma> (\<lambda>p. deriv f p / f p) + contour_integral \<gamma> (\<lambda>p. deriv h p / h p)"
      using contour_integral_add[of "(\<lambda>p. deriv f p / f p)" \<gamma> "(\<lambda>p. deriv h p / h p)" ]
      by auto
    moreover have "deriv fg p / fg p =  deriv f p / f p + deriv h p / h p"
                      when "p\<in> path_image \<gamma>" for p
    proof -
      have "fg p \<noteq> 0" and "f p \<noteq> 0" 
          using path_f path_fg that unfolding zeros_f_def zeros_fg_def by auto
      have "h p \<noteq> 0"
      proof (rule ccontr)
        assume "\<not> h p \<noteq> 0"
        then have "cmod (g p/f p) = 1"
          by (simp add: add_eq_0_iff2 h_def)
        then show False
          by (smt (verit) divide_eq_1_iff norm_divide path_less that)
      qed
      have der_fg:"deriv fg p =  deriv f p + deriv g p" unfolding fg_def
        using f_holo g_holo holomorphic_on_imp_differentiable_at[OF _  \<open>open s\<close>] path_img that
        by auto
      have der_h:"deriv h p = (deriv g p * f p - g p * deriv f p)/(f p * f p)"
      proof -
        define der where "der \<equiv> \<lambda>p. (deriv g p * f p - g p * deriv f p)/(f p * f p)"
        have "p\<in>s" using path_img that by auto
        then have "(h has_field_derivative der p) (at p)"
          unfolding h_def der_def using g_holo f_holo \<open>open s\<close> \<open>f p\<noteq>0\<close>
          by (auto intro!: derivative_eq_intros holomorphic_derivI)
        then show ?thesis unfolding der_def using DERIV_imp_deriv by auto
      qed
      show ?thesis
        using \<open>h p\<noteq>0\<close> \<open>f p\<noteq>0\<close> \<open>fg p\<noteq>0\<close>
       unfolding der_fg der_h
        apply (simp add: divide_simps h_def fg_def)
       by (simp add: mult.commute mult.left_commute ring_class.ring_distribs(1))
    qed
    then have "contour_integral \<gamma> (\<lambda>p. deriv fg p / fg p)
                  = contour_integral \<gamma> (\<lambda>p. deriv f p / f p + deriv h p / h p)"
      by (elim contour_integral_eq)
    ultimately show ?thesis by auto
  qed
  moreover have "contour_integral \<gamma> (\<lambda>x. deriv fg x / fg x) = c * (\<Sum>p\<in>zeros_fg. w p * zorder fg p)"
  proof -
    have "fg holomorphic_on s" 
      unfolding fg_def using f_holo g_holo holomorphic_on_add by auto
    moreover
    have "path_image \<gamma> \<subseteq> s - {p\<in>s. fg p = 0}" 
      using path_fg unfolding zeros_fg_def .
    moreover
    have " finite {p\<in>s. fg p = 0}" 
      using \<open>finite zeros_fg\<close> unfolding zeros_fg_def .
    ultimately show ?thesis
      unfolding c_def zeros_fg_def w_def
      using argument_principle[OF \<open>open s\<close> \<open>connected s\<close> _ _ \<open>valid_path \<gamma>\<close> loop _ homo, of _ "{}" "\<lambda>_. 1"]
      by simp
  qed
  moreover have "contour_integral \<gamma> (\<lambda>x. deriv f x / f x) = c * (\<Sum>p\<in>zeros_f. w p * zorder f p)"
    unfolding c_def zeros_f_def w_def
  proof (rule argument_principle[OF \<open>open s\<close> \<open>connected s\<close> _ _ \<open>valid_path \<gamma>\<close> loop _ homo
        , of _ "{}" "\<lambda>_. 1",simplified])
    show "f holomorphic_on s" 
      using f_holo g_holo holomorphic_on_add by auto
    show "path_image \<gamma> \<subseteq> s - {p\<in>s. f p = 0}" 
      using path_f unfolding zeros_f_def .
    show " finite {p\<in>s. f p = 0}" 
      using \<open>finite zeros_f\<close> unfolding zeros_f_def .
  qed
  ultimately have " c* (\<Sum>p\<in>zeros_fg. w p * (zorder fg p)) = c* (\<Sum>p\<in>zeros_f. w p * (zorder f p))"
    by auto
  then show ?thesis unfolding c_def using w_def by auto
qed

end