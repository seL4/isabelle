(*  Title:      HOL/Real/HahnBanach/HahnBanach.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* The Hahn-Banach Theorem *}

theory HahnBanach = HahnBanachLemmas:

text {*
  We present the proof of two different versions of the Hahn-Banach
  Theorem, closely following \cite[\S36]{Heuser:1986}.
*}

subsection {* The Hahn-Banach Theorem for vector spaces *}

text {*
  \textbf{Hahn-Banach Theorem.} Let @{text F} be a subspace of a real
  vector space @{text E}, let @{text p} be a semi-norm on @{text E},
  and @{text f} be a linear form defined on @{text F} such that @{text
  f} is bounded by @{text p}, i.e.  @{text "\<forall>x \<in> F. f x \<le> p x"}.  Then
  @{text f} can be extended to a linear form @{text h} on @{text E}
  such that @{text h} is norm-preserving, i.e. @{text h} is also
  bounded by @{text p}.

  \bigskip
  \textbf{Proof Sketch.}
  \begin{enumerate}

  \item Define @{text M} as the set of norm-preserving extensions of
  @{text f} to subspaces of @{text E}. The linear forms in @{text M}
  are ordered by domain extension.

  \item We show that every non-empty chain in @{text M} has an upper
  bound in @{text M}.

  \item With Zorn's Lemma we conclude that there is a maximal function
  @{text g} in @{text M}.

  \item The domain @{text H} of @{text g} is the whole space @{text
  E}, as shown by classical contradiction:

  \begin{itemize}

  \item Assuming @{text g} is not defined on whole @{text E}, it can
  still be extended in a norm-preserving way to a super-space @{text
  H'} of @{text H}.

  \item Thus @{text g} can not be maximal. Contradiction!

  \end{itemize}
  \end{enumerate}
*}

theorem HahnBanach:
  includes vectorspace E + subspace F E + seminorm E p + linearform F f
  assumes fp: "\<forall>x \<in> F. f x \<le> p x"
  shows "\<exists>h. linearform E h \<and> (\<forall>x \<in> F. h x = f x) \<and> (\<forall>x \<in> E. h x \<le> p x)"
    -- {* Let @{text E} be a vector space, @{text F} a subspace of @{text E}, @{text p} a seminorm on @{text E}, *}
    -- {* and @{text f} a linear form on @{text F} such that @{text f} is bounded by @{text p}, *}
    -- {* then @{text f} can be extended to a linear form @{text h} on @{text E} in a norm-preserving way. \skp *}
proof -
  def M \<equiv> "norm_pres_extensions E p F f"
  hence M: "M = \<dots>" by (simp only:)
  have E: "vectorspace E" .
  have F: "vectorspace F" ..
  {
    fix c assume cM: "c \<in> chain M" and ex: "\<exists>x. x \<in> c"
    have "\<Union>c \<in> M"
      -- {* Show that every non-empty chain @{text c} of @{text M} has an upper bound in @{text M}: *}
      -- {* @{text "\<Union>c"} is greater than any element of the chain @{text c}, so it suffices to show @{text "\<Union>c \<in> M"}. *}
    proof (unfold M_def, rule norm_pres_extensionI)
      let ?H = "domain (\<Union>c)"
      let ?h = "funct (\<Union>c)"

      have a: "graph ?H ?h = \<Union>c"
      proof (rule graph_domain_funct)
        fix x y z assume "(x, y) \<in> \<Union>c" and "(x, z) \<in> \<Union>c"
        with M_def cM show "z = y" by (rule sup_definite)
      qed
      moreover from M cM a have "linearform ?H ?h"
        by (rule sup_lf)
      moreover from a M cM ex have "?H \<unlhd> E"
        by (rule sup_subE)
      moreover from a M cM ex have "F \<unlhd> ?H"
        by (rule sup_supF)
      moreover from a M cM ex have "graph F f \<subseteq> graph ?H ?h"
        by (rule sup_ext)
      moreover from a M cM have "\<forall>x \<in> ?H. ?h x \<le> p x"
        by (rule sup_norm_pres)
      ultimately show "\<exists>H h. \<Union>c = graph H h
          \<and> linearform H h
          \<and> H \<unlhd> E
          \<and> F \<unlhd> H
          \<and> graph F f \<subseteq> graph H h
          \<and> (\<forall>x \<in> H. h x \<le> p x)" by blast
    qed
  }
  hence "\<exists>g \<in> M. \<forall>x \<in> M. g \<subseteq> x \<longrightarrow> g = x"
  -- {* With Zorn's Lemma we can conclude that there is a maximal element in @{text M}. \skp *}
  proof (rule Zorn's_Lemma)
      -- {* We show that @{text M} is non-empty: *}
    show "graph F f \<in> M"
    proof (unfold M_def, rule norm_pres_extensionI2)
      show "linearform F f" .
      show "F \<unlhd> E" .
      from F show "F \<unlhd> F" by (rule vectorspace.subspace_refl)
      show "graph F f \<subseteq> graph F f" ..
      show "\<forall>x\<in>F. f x \<le> p x" .
    qed
  qed
  then obtain g where gM: "g \<in> M" and "\<forall>x \<in> M. g \<subseteq> x \<longrightarrow> g = x"
    by blast
  from gM [unfolded M_def] obtain H h where
      g_rep: "g = graph H h"
    and linearform: "linearform H h"
    and HE: "H \<unlhd> E" and FH: "F \<unlhd> H"
    and graphs: "graph F f \<subseteq> graph H h"
    and hp: "\<forall>x \<in> H. h x \<le> p x" ..
      -- {* @{text g} is a norm-preserving extension of @{text f}, in other words: *}
      -- {* @{text g} is the graph of some linear form @{text h} defined on a subspace @{text H} of @{text E}, *}
      -- {* and @{text h} is an extension of @{text f} that is again bounded by @{text p}. \skp *}
  from HE have H: "vectorspace H"
    by (rule subspace.vectorspace)

  have HE_eq: "H = E"
    -- {* We show that @{text h} is defined on whole @{text E} by classical contradiction. \skp *}
  proof (rule classical)
    assume neq: "H \<noteq> E"
      -- {* Assume @{text h} is not defined on whole @{text E}. Then show that @{text h} can be extended *}
      -- {* in a norm-preserving way to a function @{text h'} with the graph @{text g'}. \skp *}
    have "\<exists>g' \<in> M. g \<subseteq> g' \<and> g \<noteq> g'"
    proof -
      from HE have "H \<subseteq> E" ..
      with neq obtain x' where x'E: "x' \<in> E" and "x' \<notin> H" by blast
      obtain x': "x' \<noteq> 0"
      proof
        show "x' \<noteq> 0"
        proof
          assume "x' = 0"
          with H have "x' \<in> H" by (simp only: vectorspace.zero)
          then show False by contradiction
        qed
      qed

      def H' \<equiv> "H + lin x'"
        -- {* Define @{text H'} as the direct sum of @{text H} and the linear closure of @{text x'}. \skp *}
      have HH': "H \<unlhd> H'"
      proof (unfold H'_def)
        have "vectorspace (lin x')" ..
        with H show "H \<unlhd> H + lin x'" ..
      qed

      obtain xi where
        "\<forall>y \<in> H. - p (y + x') - h y \<le> xi
          \<and> xi \<le> p (y + x') - h y"
        -- {* Pick a real number @{text \<xi>} that fulfills certain inequations; this will *}
        -- {* be used to establish that @{text h'} is a norm-preserving extension of @{text h}.
           \label{ex-xi-use}\skp *}
      proof -
        from H have "\<exists>xi. \<forall>y \<in> H. - p (y + x') - h y \<le> xi
            \<and> xi \<le> p (y + x') - h y"
        proof (rule ex_xi)
          fix u v assume u: "u \<in> H" and v: "v \<in> H"
          with HE have uE: "u \<in> E" and vE: "v \<in> E" by auto
          from H u v linearform have "h v - h u = h (v - u)"
            by (simp add: linearform.diff)
          also from hp and H u v have "\<dots> \<le> p (v - u)"
            by (simp only: vectorspace.diff_closed)
          also from x'E uE vE have "v - u = x' + - x' + v + - u"
            by (simp add: diff_eq1)
          also from x'E uE vE have "\<dots> = v + x' + - (u + x')"
            by (simp add: add_ac)
          also from x'E uE vE have "\<dots> = (v + x') - (u + x')"
            by (simp add: diff_eq1)
          also from x'E uE vE E have "p \<dots> \<le> p (v + x') + p (u + x')"
            by (simp add: diff_subadditive)
          finally have "h v - h u \<le> p (v + x') + p (u + x')" .
          then show "- p (u + x') - h u \<le> p (v + x') - h v" by simp
        qed
        then show ?thesis ..
      qed

      def h' \<equiv> "\<lambda>x. let (y, a) =
          SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H in h y + a * xi"
        -- {* Define the extension @{text h'} of @{text h} to @{text H'} using @{text \<xi>}. \skp *}

      have "g \<subseteq> graph H' h' \<and> g \<noteq> graph H' h'"
        -- {* @{text h'} is an extension of @{text h} \dots \skp *}
      proof
        show "g \<subseteq> graph H' h'"
        proof -
          have  "graph H h \<subseteq> graph H' h'"
          proof (rule graph_extI)
            fix t assume t: "t \<in> H"
            have "(SOME (y, a). t = y + a \<cdot> x' \<and> y \<in> H) = (t, 0)"
              by (rule decomp_H'_H)
            with h'_def show "h t = h' t" by (simp add: Let_def)
          next
            from HH' show "H \<subseteq> H'" ..
          qed
          with g_rep show ?thesis by (simp only:)
        qed

        show "g \<noteq> graph H' h'"
        proof -
          have "graph H h \<noteq> graph H' h'"
          proof
            assume eq: "graph H h = graph H' h'"
            have "x' \<in> H'"
            proof (unfold H'_def, rule)
              from H show "0 \<in> H" by (rule vectorspace.zero)
              from x'E show "x' \<in> lin x'" by (rule x_lin_x)
              from x'E show "x' = 0 + x'" by simp
            qed
            hence "(x', h' x') \<in> graph H' h'" ..
            with eq have "(x', h' x') \<in> graph H h" by (simp only:)
            hence "x' \<in> H" ..
            thus False by contradiction
          qed
          with g_rep show ?thesis by simp
        qed
      qed
      moreover have "graph H' h' \<in> M"
        -- {* and @{text h'} is norm-preserving. \skp *}
      proof (unfold M_def)
        show "graph H' h' \<in> norm_pres_extensions E p F f"
        proof (rule norm_pres_extensionI2)
          show "linearform H' h'" by (rule h'_lf)
          show "H' \<unlhd> E"
          proof (unfold H'_def, rule)
            show "H \<unlhd> E" .
            show "vectorspace E" .
            from x'E show "lin x' \<unlhd> E" ..
          qed
          have "F \<unlhd> H" .
          from H this HH' show FH': "F \<unlhd> H'"
            by (rule vectorspace.subspace_trans)
          show "graph F f \<subseteq> graph H' h'"
          proof (rule graph_extI)
            fix x assume x: "x \<in> F"
            with graphs have "f x = h x" ..
            also have "\<dots> = h x + 0 * xi" by simp
            also have "\<dots> = (let (y, a) = (x, 0) in h y + a * xi)"
              by (simp add: Let_def)
            also have "(x, 0) =
                (SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H)"
            proof (rule decomp_H'_H [symmetric])
              from FH x show "x \<in> H" ..
              from x' show "x' \<noteq> 0" .
            qed
            also have
              "(let (y, a) = (SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H)
              in h y + a * xi) = h' x" by (simp only: h'_def)
            finally show "f x = h' x" .
          next
            from FH' show "F \<subseteq> H'" ..
          qed
          show "\<forall>x \<in> H'. h' x \<le> p x" by (rule h'_norm_pres)
        qed
      qed
      ultimately show ?thesis ..
    qed
    hence "\<not> (\<forall>x \<in> M. g \<subseteq> x \<longrightarrow> g = x)" by simp
      -- {* So the graph @{text g} of @{text h} cannot be maximal. Contradiction! \skp *}
    then show "H = E" by contradiction
  qed

  from HE_eq and linearform have "linearform E h"
    by (simp only:)
  moreover have "\<forall>x \<in> F. h x = f x"
  proof
    fix x assume "x \<in> F"
    with graphs have "f x = h x" ..
    then show "h x = f x" ..
  qed
  moreover from HE_eq and hp have "\<forall>x \<in> E. h x \<le> p x"
    by (simp only:)
  ultimately show ?thesis by blast
qed


subsection  {* Alternative formulation *}

text {*
  The following alternative formulation of the Hahn-Banach
  Theorem\label{abs-HahnBanach} uses the fact that for a real linear
  form @{text f} and a seminorm @{text p} the following inequations
  are equivalent:\footnote{This was shown in lemma @{thm [source]
  abs_ineq_iff} (see page \pageref{abs-ineq-iff}).}
  \begin{center}
  \begin{tabular}{lll}
  @{text "\<forall>x \<in> H. \<bar>h x\<bar> \<le> p x"} & and &
  @{text "\<forall>x \<in> H. h x \<le> p x"} \\
  \end{tabular}
  \end{center}
*}

theorem abs_HahnBanach:
  includes vectorspace E + subspace F E + linearform F f + seminorm E p
  assumes fp: "\<forall>x \<in> F. \<bar>f x\<bar> \<le> p x"
  shows "\<exists>g. linearform E g
    \<and> (\<forall>x \<in> F. g x = f x)
    \<and> (\<forall>x \<in> E. \<bar>g x\<bar> \<le> p x)"
proof -
  have "\<exists>g. linearform E g \<and> (\<forall>x \<in> F. g x = f x)
    \<and> (\<forall>x \<in> E. g x \<le> p x)"
  proof (rule HahnBanach)
    show "\<forall>x \<in> F. f x \<le> p x"
      by (rule abs_ineq_iff [THEN iffD1])
  qed
  then obtain g where * : "linearform E g"  "\<forall>x \<in> F. g x = f x"
      and "\<forall>x \<in> E. g x \<le> p x" by blast
  have "\<forall>x \<in> E. \<bar>g x\<bar> \<le> p x"
  proof (rule abs_ineq_iff [THEN iffD2])
    show "E \<unlhd> E" ..
  qed
  with * show ?thesis by blast
qed


subsection {* The Hahn-Banach Theorem for normed spaces *}

text {*
  Every continuous linear form @{text f} on a subspace @{text F} of a
  norm space @{text E}, can be extended to a continuous linear form
  @{text g} on @{text E} such that @{text "\<parallel>f\<parallel> = \<parallel>g\<parallel>"}.
*}

theorem norm_HahnBanach:
  includes normed_vectorspace E + subspace F E + linearform F f + fn_norm + continuous F norm f
  shows "\<exists>g. linearform E g
     \<and> continuous E norm g
     \<and> (\<forall>x \<in> F. g x = f x)
     \<and> \<parallel>g\<parallel>\<hyphen>E = \<parallel>f\<parallel>\<hyphen>F"
proof -
  have E: "vectorspace E" .
  have E_norm: "normed_vectorspace E norm" ..
  have FE: "F \<unlhd> E" .
  have F: "vectorspace F" ..
  have linearform: "linearform F f" .
  have F_norm: "normed_vectorspace F norm"
    by (rule subspace_normed_vs [OF _ _ norm.intro])
  have ge_zero: "0 \<le> \<parallel>f\<parallel>\<hyphen>F"
    by (rule normed_vectorspace.fn_norm_ge_zero
      [OF F_norm _ continuous.intro, folded B_def fn_norm_def])

  txt {* We define a function @{text p} on @{text E} as follows:
    @{text "p x = \<parallel>f\<parallel> \<cdot> \<parallel>x\<parallel>"} *}
  def p \<equiv> "\<lambda>x. \<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel>"

  txt {* @{text p} is a seminorm on @{text E}: *}
  have q: "seminorm E p"
  proof
    fix x y a assume x: "x \<in> E" and y: "y \<in> E"

    txt {* @{text p} is positive definite: *}
      have "0 \<le> \<parallel>f\<parallel>\<hyphen>F" by (rule ge_zero)
      moreover from x have "0 \<le> \<parallel>x\<parallel>" ..
    ultimately show "0 \<le> p x"  
      by (simp add: p_def zero_le_mult_iff)

    txt {* @{text p} is absolutely homogenous: *}

    show "p (a \<cdot> x) = \<bar>a\<bar> * p x"
    proof -
      have "p (a \<cdot> x) = \<parallel>f\<parallel>\<hyphen>F * \<parallel>a \<cdot> x\<parallel>" by (simp only: p_def)
      also from x have "\<parallel>a \<cdot> x\<parallel> = \<bar>a\<bar> * \<parallel>x\<parallel>" by (rule abs_homogenous)
      also have "\<parallel>f\<parallel>\<hyphen>F * (\<bar>a\<bar> * \<parallel>x\<parallel>) = \<bar>a\<bar> * (\<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel>)" by simp
      also have "\<dots> = \<bar>a\<bar> * p x" by (simp only: p_def)
      finally show ?thesis .
    qed

    txt {* Furthermore, @{text p} is subadditive: *}

    show "p (x + y) \<le> p x + p y"
    proof -
      have "p (x + y) = \<parallel>f\<parallel>\<hyphen>F * \<parallel>x + y\<parallel>" by (simp only: p_def)
      also have a: "0 \<le> \<parallel>f\<parallel>\<hyphen>F" by (rule ge_zero)
      from x y have "\<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>" ..
      with a have " \<parallel>f\<parallel>\<hyphen>F * \<parallel>x + y\<parallel> \<le> \<parallel>f\<parallel>\<hyphen>F * (\<parallel>x\<parallel> + \<parallel>y\<parallel>)"
        by (simp add: mult_left_mono)
      also have "\<dots> = \<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel> + \<parallel>f\<parallel>\<hyphen>F * \<parallel>y\<parallel>" by (simp only: right_distrib)
      also have "\<dots> = p x + p y" by (simp only: p_def)
      finally show ?thesis .
    qed
  qed

  txt {* @{text f} is bounded by @{text p}. *}

  have "\<forall>x \<in> F. \<bar>f x\<bar> \<le> p x"
  proof
    fix x assume "x \<in> F"
    show "\<bar>f x\<bar> \<le> p x"
      by (unfold p_def) (rule normed_vectorspace.fn_norm_le_cong
        [OF F_norm _ continuous.intro, folded B_def fn_norm_def])
  qed

  txt {* Using the fact that @{text p} is a seminorm and @{text f} is bounded
    by @{text p} we can apply the Hahn-Banach Theorem for real vector
    spaces. So @{text f} can be extended in a norm-preserving way to
    some function @{text g} on the whole vector space @{text E}. *}

  with E FE linearform q obtain g where
        linearformE: "linearform E g"
      and a: "\<forall>x \<in> F. g x = f x"
      and b: "\<forall>x \<in> E. \<bar>g x\<bar> \<le> p x"
    by (rule abs_HahnBanach [elim_format]) rules

  txt {* We furthermore have to show that @{text g} is also continuous: *}

  have g_cont: "continuous E norm g" using linearformE
  proof
    fix x assume "x \<in> E"
    with b show "\<bar>g x\<bar> \<le> \<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel>"
      by (simp only: p_def)
  qed

  txt {* To complete the proof, we show that @{text "\<parallel>g\<parallel> = \<parallel>f\<parallel>"}. *}

  have "\<parallel>g\<parallel>\<hyphen>E = \<parallel>f\<parallel>\<hyphen>F"
  proof (rule order_antisym)
    txt {*
      First we show @{text "\<parallel>g\<parallel> \<le> \<parallel>f\<parallel>"}.  The function norm @{text
      "\<parallel>g\<parallel>"} is defined as the smallest @{text "c \<in> \<real>"} such that
      \begin{center}
      \begin{tabular}{l}
      @{text "\<forall>x \<in> E. \<bar>g x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>"}
      \end{tabular}
      \end{center}
      \noindent Furthermore holds
      \begin{center}
      \begin{tabular}{l}
      @{text "\<forall>x \<in> E. \<bar>g x\<bar> \<le> \<parallel>f\<parallel> \<cdot> \<parallel>x\<parallel>"}
      \end{tabular}
      \end{center}
    *}

    have "\<forall>x \<in> E. \<bar>g x\<bar> \<le> \<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel>"
    proof
      fix x assume "x \<in> E"
      with b show "\<bar>g x\<bar> \<le> \<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel>"
        by (simp only: p_def)
    qed
    from linearformE g_cont this ge_zero
    show "\<parallel>g\<parallel>\<hyphen>E \<le> \<parallel>f\<parallel>\<hyphen>F"
      by (rule fn_norm_least [of g, folded B_def fn_norm_def])

    txt {* The other direction is achieved by a similar argument. *}

    show "\<parallel>f\<parallel>\<hyphen>F \<le> \<parallel>g\<parallel>\<hyphen>E"
    proof (rule normed_vectorspace.fn_norm_least [OF F_norm, folded B_def fn_norm_def])
      show "\<forall>x \<in> F. \<bar>f x\<bar> \<le> \<parallel>g\<parallel>\<hyphen>E * \<parallel>x\<parallel>"
      proof
	fix x assume x: "x \<in> F"
	from a have "g x = f x" ..
	hence "\<bar>f x\<bar> = \<bar>g x\<bar>" by (simp only:)
	also from linearformE g_cont
	have "\<dots> \<le> \<parallel>g\<parallel>\<hyphen>E * \<parallel>x\<parallel>"
	proof (rule fn_norm_le_cong [of g, folded B_def fn_norm_def])
	  from FE x show "x \<in> E" ..
	qed
	finally show "\<bar>f x\<bar> \<le> \<parallel>g\<parallel>\<hyphen>E * \<parallel>x\<parallel>" .
      qed
      show "0 \<le> \<parallel>g\<parallel>\<hyphen>E"
	using linearformE g_cont
	by (rule fn_norm_ge_zero [of g, folded B_def fn_norm_def])
    next
      show "continuous F norm f" by (rule continuous.intro)
    qed
  qed
  with linearformE a g_cont show ?thesis by blast
qed

end
