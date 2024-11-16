(*  Title:      HOL/Hahn_Banach/Hahn_Banach.thy
    Author:     Gertrud Bauer, TU Munich
*)

section \<open>The Hahn-Banach Theorem\<close>

theory Hahn_Banach
imports Hahn_Banach_Lemmas
begin

text \<open>
  We present the proof of two different versions of the Hahn-Banach Theorem,
  closely following \<^cite>\<open>\<open>\S36\<close> in "Heuser:1986"\<close>.
\<close>


subsection \<open>The Hahn-Banach Theorem for vector spaces\<close>

paragraph \<open>Hahn-Banach Theorem.\<close>
text \<open>
  Let \<open>F\<close> be a subspace of a real vector space \<open>E\<close>, let \<open>p\<close> be a semi-norm on
  \<open>E\<close>, and \<open>f\<close> be a linear form defined on \<open>F\<close> such that \<open>f\<close> is bounded by
  \<open>p\<close>, i.e. \<open>\<forall>x \<in> F. f x \<le> p x\<close>. Then \<open>f\<close> can be extended to a linear form \<open>h\<close>
  on \<open>E\<close> such that \<open>h\<close> is norm-preserving, i.e. \<open>h\<close> is also bounded by \<open>p\<close>.
\<close>

paragraph \<open>Proof Sketch.\<close>
text \<open>
  \<^enum> Define \<open>M\<close> as the set of norm-preserving extensions of \<open>f\<close> to subspaces of
  \<open>E\<close>. The linear forms in \<open>M\<close> are ordered by domain extension.

  \<^enum> We show that every non-empty chain in \<open>M\<close> has an upper bound in \<open>M\<close>.

  \<^enum> With Zorn's Lemma we conclude that there is a maximal function \<open>g\<close> in \<open>M\<close>.

  \<^enum> The domain \<open>H\<close> of \<open>g\<close> is the whole space \<open>E\<close>, as shown by classical
  contradiction:

    \<^item> Assuming \<open>g\<close> is not defined on whole \<open>E\<close>, it can still be extended in a
    norm-preserving way to a super-space \<open>H'\<close> of \<open>H\<close>.

    \<^item> Thus \<open>g\<close> can not be maximal. Contradiction!
\<close>

theorem Hahn_Banach:
  assumes E: "vectorspace E" and "subspace F E"
    and "seminorm E p" and "linearform F f"
  assumes fp: "\<forall>x \<in> F. f x \<le> p x"
  shows "\<exists>h. linearform E h \<and> (\<forall>x \<in> F. h x = f x) \<and> (\<forall>x \<in> E. h x \<le> p x)"
    \<comment> \<open>Let \<open>E\<close> be a vector space, \<open>F\<close> a subspace of \<open>E\<close>, \<open>p\<close> a seminorm on \<open>E\<close>,\<close>
    \<comment> \<open>and \<open>f\<close> a linear form on \<open>F\<close> such that \<open>f\<close> is bounded by \<open>p\<close>,\<close>
    \<comment> \<open>then \<open>f\<close> can be extended to a linear form \<open>h\<close> on \<open>E\<close> in a norm-preserving way. \<^smallskip>\<close>
proof -
  interpret vectorspace E by fact
  interpret subspace F E by fact
  interpret seminorm E p by fact
  interpret linearform F f by fact
  define M where "M = norm_pres_extensions E p F f"
  then have M: "M = \<dots>" by (simp only:)
  from E have F: "vectorspace F" ..
  note FE = \<open>F \<unlhd> E\<close>
  have "\<Union>c \<in> M" if cM: "c \<in> chains M" and ex: "\<exists>x. x \<in> c" for c
    \<comment> \<open>Show that every non-empty chain \<open>c\<close> of \<open>M\<close> has an upper bound in \<open>M\<close>:\<close>
    \<comment> \<open>\<open>\<Union>c\<close> is greater than any element of the chain \<open>c\<close>, so it suffices to show \<open>\<Union>c \<in> M\<close>.\<close>
    unfolding M_def
  proof (rule norm_pres_extensionI)
    let ?H = "domain (\<Union>c)"
    let ?h = "funct (\<Union>c)"

    have a: "graph ?H ?h = \<Union>c"
    proof (rule graph_domain_funct)
      fix x y z assume "(x, y) \<in> \<Union>c" and "(x, z) \<in> \<Union>c"
      with M_def cM show "z = y" by (rule sup_definite)
    qed
    moreover from M cM a have "linearform ?H ?h"
      by (rule sup_lf)
    moreover from a M cM ex FE E have "?H \<unlhd> E"
      by (rule sup_subE)
    moreover from a M cM ex FE have "F \<unlhd> ?H"
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
  then have "\<exists>g \<in> M. \<forall>x \<in> M. g \<subseteq> x \<longrightarrow> x = g"
  \<comment> \<open>With Zorn's Lemma we can conclude that there is a maximal element in \<open>M\<close>. \<^smallskip>\<close>
  proof (rule Zorn's_Lemma)
      \<comment> \<open>We show that \<open>M\<close> is non-empty:\<close>
    show "graph F f \<in> M"
      unfolding M_def
    proof (rule norm_pres_extensionI2)
      show "linearform F f" by fact
      show "F \<unlhd> E" by fact
      from F show "F \<unlhd> F" by (rule vectorspace.subspace_refl)
      show "graph F f \<subseteq> graph F f" ..
      show "\<forall>x\<in>F. f x \<le> p x" by fact
    qed
  qed
  then obtain g where gM: "g \<in> M" and gx: "\<forall>x \<in> M. g \<subseteq> x \<longrightarrow> g = x"
    by blast
  from gM obtain H h where
      g_rep: "g = graph H h"
    and linearform: "linearform H h"
    and HE: "H \<unlhd> E" and FH: "F \<unlhd> H"
    and graphs: "graph F f \<subseteq> graph H h"
    and hp: "\<forall>x \<in> H. h x \<le> p x" unfolding M_def ..
      \<comment> \<open>\<open>g\<close> is a norm-preserving extension of \<open>f\<close>, in other words:\<close>
      \<comment> \<open>\<open>g\<close> is the graph of some linear form \<open>h\<close> defined on a subspace \<open>H\<close> of \<open>E\<close>,\<close>
      \<comment> \<open>and \<open>h\<close> is an extension of \<open>f\<close> that is again bounded by \<open>p\<close>. \<^smallskip>\<close>
  from HE E have H: "vectorspace H"
    by (rule subspace.vectorspace)

  have HE_eq: "H = E"
    \<comment> \<open>We show that \<open>h\<close> is defined on whole \<open>E\<close> by classical contradiction. \<^smallskip>\<close>
  proof (rule classical)
    assume neq: "H \<noteq> E"
      \<comment> \<open>Assume \<open>h\<close> is not defined on whole \<open>E\<close>. Then show that \<open>h\<close> can be extended\<close>
      \<comment> \<open>in a norm-preserving way to a function \<open>h'\<close> with the graph \<open>g'\<close>. \<^smallskip>\<close>
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
          with \<open>x' \<notin> H\<close> show False by contradiction
        qed
      qed

      define H' where "H' = H + lin x'"
        \<comment> \<open>Define \<open>H'\<close> as the direct sum of \<open>H\<close> and the linear closure of \<open>x'\<close>. \<^smallskip>\<close>
      have HH': "H \<unlhd> H'"
      proof (unfold H'_def)
        from x'E have "vectorspace (lin x')" ..
        with H show "H \<unlhd> H + lin x'" ..
      qed

      obtain xi where
        xi: "\<forall>y \<in> H. - p (y + x') - h y \<le> xi
          \<and> xi \<le> p (y + x') - h y"
        \<comment> \<open>Pick a real number \<open>\<xi>\<close> that fulfills certain inequality; this will\<close>
        \<comment> \<open>be used to establish that \<open>h'\<close> is a norm-preserving extension of \<open>h\<close>.
           \label{ex-xi-use}\<^smallskip>\<close>
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
        then show thesis by (blast intro: that)
      qed

      define h' where "h' x = (let (y, a) =
          SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H in h y + a * xi)" for x
        \<comment> \<open>Define the extension \<open>h'\<close> of \<open>h\<close> to \<open>H'\<close> using \<open>\<xi>\<close>. \<^smallskip>\<close>

      have "g \<subseteq> graph H' h' \<and> g \<noteq> graph H' h'"
        \<comment> \<open>\<open>h'\<close> is an extension of \<open>h\<close> \dots \<^smallskip>\<close>
      proof
        show "g \<subseteq> graph H' h'"
        proof -
          have "graph H h \<subseteq> graph H' h'"
          proof (rule graph_extI)
            fix t assume t: "t \<in> H"
            from E HE t have "(SOME (y, a). t = y + a \<cdot> x' \<and> y \<in> H) = (t, 0)"
              using \<open>x' \<notin> H\<close> \<open>x' \<in> E\<close> \<open>x' \<noteq> 0\<close> by (rule decomp_H'_H)
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
              unfolding H'_def
            proof
              from H show "0 \<in> H" by (rule vectorspace.zero)
              from x'E show "x' \<in> lin x'" by (rule x_lin_x)
              from x'E show "x' = 0 + x'" by simp
            qed
            then have "(x', h' x') \<in> graph H' h'" ..
            with eq have "(x', h' x') \<in> graph H h" by (simp only:)
            then have "x' \<in> H" ..
            with \<open>x' \<notin> H\<close> show False by contradiction
          qed
          with g_rep show ?thesis by simp
        qed
      qed
      moreover have "graph H' h' \<in> M"
        \<comment> \<open>and \<open>h'\<close> is norm-preserving. \<^smallskip>\<close>
      proof (unfold M_def)
        show "graph H' h' \<in> norm_pres_extensions E p F f"
        proof (rule norm_pres_extensionI2)
          show "linearform H' h'"
            using h'_def H'_def HE linearform \<open>x' \<notin> H\<close> \<open>x' \<in> E\<close> \<open>x' \<noteq> 0\<close> E
            by (rule h'_lf)
          show "H' \<unlhd> E"
          unfolding H'_def
          proof
            show "H \<unlhd> E" by fact
            show "vectorspace E" by fact
            from x'E show "lin x' \<unlhd> E" ..
          qed
          from H \<open>F \<unlhd> H\<close> HH' show FH': "F \<unlhd> H'"
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
              using E HE
            proof (rule decomp_H'_H [symmetric])
              from FH x show "x \<in> H" ..
              from x' show "x' \<noteq> 0" .
              show "x' \<notin> H" by fact
              show "x' \<in> E" by fact
            qed
            also have
              "(let (y, a) = (SOME (y, a). x = y + a \<cdot> x' \<and> y \<in> H)
              in h y + a * xi) = h' x" by (simp only: h'_def)
            finally show "f x = h' x" .
          next
            from FH' show "F \<subseteq> H'" ..
          qed
          show "\<forall>x \<in> H'. h' x \<le> p x"
            using h'_def H'_def \<open>x' \<notin> H\<close> \<open>x' \<in> E\<close> \<open>x' \<noteq> 0\<close> E HE
              \<open>seminorm E p\<close> linearform and hp xi
            by (rule h'_norm_pres)
        qed
      qed
      ultimately show ?thesis ..
    qed
    then have "\<not> (\<forall>x \<in> M. g \<subseteq> x \<longrightarrow> g = x)" by simp
      \<comment> \<open>So the graph \<open>g\<close> of \<open>h\<close> cannot be maximal. Contradiction! \<^smallskip>\<close>
    with gx show "H = E" by contradiction
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


subsection \<open>Alternative formulation\<close>

text \<open>
  The following alternative formulation of the Hahn-Banach
  Theorem\label{abs-Hahn-Banach} uses the fact that for a real linear form \<open>f\<close>
  and a seminorm \<open>p\<close> the following inequality are equivalent:\footnote{This
  was shown in lemma @{thm [source] abs_ineq_iff} (see page
  \pageref{abs-ineq-iff}).}
  \begin{center}
  \begin{tabular}{lll}
  \<open>\<forall>x \<in> H. \<bar>h x\<bar> \<le> p x\<close> & and & \<open>\<forall>x \<in> H. h x \<le> p x\<close> \\
  \end{tabular}
  \end{center}
\<close>

theorem abs_Hahn_Banach:
  assumes E: "vectorspace E" and FE: "subspace F E"
    and lf: "linearform F f" and sn: "seminorm E p"
  assumes fp: "\<forall>x \<in> F. \<bar>f x\<bar> \<le> p x"
  shows "\<exists>g. linearform E g
    \<and> (\<forall>x \<in> F. g x = f x)
    \<and> (\<forall>x \<in> E. \<bar>g x\<bar> \<le> p x)"
proof -
  interpret vectorspace E by fact
  interpret subspace F E by fact
  interpret linearform F f by fact
  interpret seminorm E p by fact
  have "\<exists>g. linearform E g \<and> (\<forall>x \<in> F. g x = f x) \<and> (\<forall>x \<in> E. g x \<le> p x)"
    using E FE sn lf
  proof (rule Hahn_Banach)
    show "\<forall>x \<in> F. f x \<le> p x"
      using FE E sn lf and fp by (rule abs_ineq_iff [THEN iffD1])
  qed
  then obtain g where lg: "linearform E g" and *: "\<forall>x \<in> F. g x = f x"
      and **: "\<forall>x \<in> E. g x \<le> p x" by blast
  have "\<forall>x \<in> E. \<bar>g x\<bar> \<le> p x"
    using _ E sn lg **
  proof (rule abs_ineq_iff [THEN iffD2])
    show "E \<unlhd> E" ..
  qed
  with lg * show ?thesis by blast
qed


subsection \<open>The Hahn-Banach Theorem for normed spaces\<close>

text \<open>
  Every continuous linear form \<open>f\<close> on a subspace \<open>F\<close> of a norm space \<open>E\<close>, can
  be extended to a continuous linear form \<open>g\<close> on \<open>E\<close> such that \<open>\<parallel>f\<parallel> = \<parallel>g\<parallel>\<close>.
\<close>

theorem norm_Hahn_Banach:
  fixes V and norm (\<open>\<parallel>_\<parallel>\<close>)
  fixes B defines "\<And>V f. B V f \<equiv> {0} \<union> {\<bar>f x\<bar> / \<parallel>x\<parallel> | x. x \<noteq> 0 \<and> x \<in> V}"
  fixes fn_norm (\<open>\<parallel>_\<parallel>\<hyphen>_\<close> [0, 1000] 999)
  defines "\<And>V f. \<parallel>f\<parallel>\<hyphen>V \<equiv> \<Squnion>(B V f)"
  assumes E_norm: "normed_vectorspace E norm" and FE: "subspace F E"
    and linearform: "linearform F f" and "continuous F f norm"
  shows "\<exists>g. linearform E g
     \<and> continuous E g norm
     \<and> (\<forall>x \<in> F. g x = f x)
     \<and> \<parallel>g\<parallel>\<hyphen>E = \<parallel>f\<parallel>\<hyphen>F"
proof -
  interpret normed_vectorspace E norm by fact
  interpret normed_vectorspace_with_fn_norm E norm B fn_norm
    by (auto simp: B_def fn_norm_def) intro_locales
  interpret subspace F E by fact
  interpret linearform F f by fact
  interpret continuous F f norm by fact
  have E: "vectorspace E" by intro_locales
  have F: "vectorspace F" by rule intro_locales
  have F_norm: "normed_vectorspace F norm"
    using FE E_norm by (rule subspace_normed_vs)
  have ge_zero: "0 \<le> \<parallel>f\<parallel>\<hyphen>F"
    by (rule normed_vectorspace_with_fn_norm.fn_norm_ge_zero
      [OF normed_vectorspace_with_fn_norm.intro,
       OF F_norm \<open>continuous F f norm\<close> , folded B_def fn_norm_def])
  txt \<open>We define a function \<open>p\<close> on \<open>E\<close> as follows:
    \<open>p x = \<parallel>f\<parallel> \<cdot> \<parallel>x\<parallel>\<close>\<close>
  define p where "p x = \<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel>" for x

  txt \<open>\<open>p\<close> is a seminorm on \<open>E\<close>:\<close>
  have q: "seminorm E p"
  proof
    fix x y a assume x: "x \<in> E" and y: "y \<in> E"

    txt \<open>\<open>p\<close> is positive definite:\<close>
    have "0 \<le> \<parallel>f\<parallel>\<hyphen>F" by (rule ge_zero)
    moreover from x have "0 \<le> \<parallel>x\<parallel>" ..
    ultimately show "0 \<le> p x"
      by (simp add: p_def zero_le_mult_iff)

    txt \<open>\<open>p\<close> is absolutely homogeneous:\<close>

    show "p (a \<cdot> x) = \<bar>a\<bar> * p x"
    proof -
      have "p (a \<cdot> x) = \<parallel>f\<parallel>\<hyphen>F * \<parallel>a \<cdot> x\<parallel>" by (simp only: p_def)
      also from x have "\<parallel>a \<cdot> x\<parallel> = \<bar>a\<bar> * \<parallel>x\<parallel>" by (rule abs_homogenous)
      also have "\<parallel>f\<parallel>\<hyphen>F * (\<bar>a\<bar> * \<parallel>x\<parallel>) = \<bar>a\<bar> * (\<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel>)" by simp
      also have "\<dots> = \<bar>a\<bar> * p x" by (simp only: p_def)
      finally show ?thesis .
    qed

    txt \<open>Furthermore, \<open>p\<close> is subadditive:\<close>

    show "p (x + y) \<le> p x + p y"
    proof -
      have "p (x + y) = \<parallel>f\<parallel>\<hyphen>F * \<parallel>x + y\<parallel>" by (simp only: p_def)
      also have a: "0 \<le> \<parallel>f\<parallel>\<hyphen>F" by (rule ge_zero)
      from x y have "\<parallel>x + y\<parallel> \<le> \<parallel>x\<parallel> + \<parallel>y\<parallel>" ..
      with a have " \<parallel>f\<parallel>\<hyphen>F * \<parallel>x + y\<parallel> \<le> \<parallel>f\<parallel>\<hyphen>F * (\<parallel>x\<parallel> + \<parallel>y\<parallel>)"
        by (simp add: mult_left_mono)
      also have "\<dots> = \<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel> + \<parallel>f\<parallel>\<hyphen>F * \<parallel>y\<parallel>" by (simp only: distrib_left)
      also have "\<dots> = p x + p y" by (simp only: p_def)
      finally show ?thesis .
    qed
  qed

  txt \<open>\<open>f\<close> is bounded by \<open>p\<close>.\<close>

  have "\<forall>x \<in> F. \<bar>f x\<bar> \<le> p x"
  proof
    fix x assume "x \<in> F"
    with \<open>continuous F f norm\<close> and linearform
    show "\<bar>f x\<bar> \<le> p x"
      unfolding p_def by (rule normed_vectorspace_with_fn_norm.fn_norm_le_cong
        [OF normed_vectorspace_with_fn_norm.intro,
         OF F_norm, folded B_def fn_norm_def])
  qed

  txt \<open>Using the fact that \<open>p\<close> is a seminorm and \<open>f\<close> is bounded by \<open>p\<close> we can
    apply the Hahn-Banach Theorem for real vector spaces. So \<open>f\<close> can be
    extended in a norm-preserving way to some function \<open>g\<close> on the whole vector
    space \<open>E\<close>.\<close>

  with E FE linearform q obtain g where
      linearformE: "linearform E g"
    and a: "\<forall>x \<in> F. g x = f x"
    and b: "\<forall>x \<in> E. \<bar>g x\<bar> \<le> p x"
    by (rule abs_Hahn_Banach [elim_format]) iprover

  txt \<open>We furthermore have to show that \<open>g\<close> is also continuous:\<close>

  have g_cont: "continuous E g norm" using linearformE
  proof
    fix x assume "x \<in> E"
    with b show "\<bar>g x\<bar> \<le> \<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel>"
      by (simp only: p_def)
  qed

  txt \<open>To complete the proof, we show that \<open>\<parallel>g\<parallel> = \<parallel>f\<parallel>\<close>.\<close>

  have "\<parallel>g\<parallel>\<hyphen>E = \<parallel>f\<parallel>\<hyphen>F"
  proof (rule order_antisym)
    txt \<open>
      First we show \<open>\<parallel>g\<parallel> \<le> \<parallel>f\<parallel>\<close>. The function norm \<open>\<parallel>g\<parallel>\<close> is defined as the
      smallest \<open>c \<in> \<real>\<close> such that
      \begin{center}
      \begin{tabular}{l}
      \<open>\<forall>x \<in> E. \<bar>g x\<bar> \<le> c \<cdot> \<parallel>x\<parallel>\<close>
      \end{tabular}
      \end{center}
      \<^noindent> Furthermore holds
      \begin{center}
      \begin{tabular}{l}
      \<open>\<forall>x \<in> E. \<bar>g x\<bar> \<le> \<parallel>f\<parallel> \<cdot> \<parallel>x\<parallel>\<close>
      \end{tabular}
      \end{center}
    \<close>

    from g_cont _ ge_zero
    show "\<parallel>g\<parallel>\<hyphen>E \<le> \<parallel>f\<parallel>\<hyphen>F"
    proof
      fix x assume "x \<in> E"
      with b show "\<bar>g x\<bar> \<le> \<parallel>f\<parallel>\<hyphen>F * \<parallel>x\<parallel>"
        by (simp only: p_def)
    qed

    txt \<open>The other direction is achieved by a similar argument.\<close>

    show "\<parallel>f\<parallel>\<hyphen>F \<le> \<parallel>g\<parallel>\<hyphen>E"
    proof (rule normed_vectorspace_with_fn_norm.fn_norm_least
        [OF normed_vectorspace_with_fn_norm.intro,
         OF F_norm, folded B_def fn_norm_def])
      fix x assume x: "x \<in> F"
      show "\<bar>f x\<bar> \<le> \<parallel>g\<parallel>\<hyphen>E * \<parallel>x\<parallel>"
      proof -
        from a x have "g x = f x" ..
        then have "\<bar>f x\<bar> = \<bar>g x\<bar>" by (simp only:)
        also from g_cont have "\<dots> \<le> \<parallel>g\<parallel>\<hyphen>E * \<parallel>x\<parallel>"
        proof (rule fn_norm_le_cong [OF _ linearformE, folded B_def fn_norm_def])
          from FE x show "x \<in> E" ..
        qed
        finally show ?thesis .
      qed
    next
      show "0 \<le> \<parallel>g\<parallel>\<hyphen>E"
        using g_cont by (rule fn_norm_ge_zero [of g, folded B_def fn_norm_def])
      show "continuous F f norm" by fact
    qed
  qed
  with linearformE a g_cont show ?thesis by blast
qed

end
