(*  Title:      HOL/Hahn_Banach/Hahn_Banach_Ext_Lemmas.thy
    Author:     Gertrud Bauer, TU Munich
*)

section \<open>Extending non-maximal functions\<close>

theory Hahn_Banach_Ext_Lemmas
imports Function_Norm
begin

text \<open>
  In this section the following context is presumed. Let \<open>E\<close> be a real vector
  space with a seminorm \<open>q\<close> on \<open>E\<close>. \<open>F\<close> is a subspace of \<open>E\<close> and \<open>f\<close> a linear
  function on \<open>F\<close>. We consider a subspace \<open>H\<close> of \<open>E\<close> that is a superspace of
  \<open>F\<close> and a linear form \<open>h\<close> on \<open>H\<close>. \<open>H\<close> is a not equal to \<open>E\<close> and \<open>x\<^sub>0\<close> is an
  element in \<open>E - H\<close>. \<open>H\<close> is extended to the direct sum \<open>H' = H + lin x\<^sub>0\<close>, so
  for any \<open>x \<in> H'\<close> the decomposition of \<open>x = y + a \<cdot> x\<close> with \<open>y \<in> H\<close> is
  unique. \<open>h'\<close> is defined on \<open>H'\<close> by \<open>h' x = h y + a \<cdot> \<xi>\<close> for a certain \<open>\<xi>\<close>.

  Subsequently we show some properties of this extension \<open>h'\<close> of \<open>h\<close>.

  \<^medskip>
  This lemma will be used to show the existence of a linear extension of \<open>f\<close>
  (see page \pageref{ex-xi-use}). It is a consequence of the completeness of
  \<open>\<real>\<close>. To show
  \begin{center}
  \begin{tabular}{l}
  \<open>\<exists>\<xi>. \<forall>y \<in> F. a y \<le> \<xi> \<and> \<xi> \<le> b y\<close>
  \end{tabular}
  \end{center}
  \<^noindent> it suffices to show that
  \begin{center}
  \begin{tabular}{l}
  \<open>\<forall>u \<in> F. \<forall>v \<in> F. a u \<le> b v\<close>
  \end{tabular}
  \end{center}
\<close>

lemma ex_xi:
  assumes "vectorspace F"
  assumes r: "\<And>u v. u \<in> F \<Longrightarrow> v \<in> F \<Longrightarrow> a u \<le> b v"
  shows "\<exists>xi::real. \<forall>y \<in> F. a y \<le> xi \<and> xi \<le> b y"
proof -
  interpret vectorspace F by fact
  txt \<open>From the completeness of the reals follows:
    The set \<open>S = {a u. u \<in> F}\<close> has a supremum, if it is
    non-empty and has an upper bound.\<close>

  let ?S = "{a u | u. u \<in> F}"
  have "\<exists>xi. lub ?S xi"
  proof (rule real_complete)
    have "a 0 \<in> ?S" by blast
    then show "\<exists>X. X \<in> ?S" ..
    have "\<forall>y \<in> ?S. y \<le> b 0"
    proof
      fix y assume y: "y \<in> ?S"
      then obtain u where u: "u \<in> F" and y: "y = a u" by blast
      from u and zero have "a u \<le> b 0" by (rule r)
      with y show "y \<le> b 0" by (simp only:)
    qed
    then show "\<exists>u. \<forall>y \<in> ?S. y \<le> u" ..
  qed
  then obtain xi where xi: "lub ?S xi" ..
  have "a y \<le> xi" if "y \<in> F" for y
  proof -
    from that have "a y \<in> ?S" by blast
    with xi show ?thesis by (rule lub.upper)
  qed
  moreover have "xi \<le> b y" if y: "y \<in> F" for y
  proof -
    from xi
    show ?thesis
    proof (rule lub.least)
      fix au assume "au \<in> ?S"
      then obtain u where u: "u \<in> F" and au: "au = a u" by blast
      from u y have "a u \<le> b y" by (rule r)
      with au show "au \<le> b y" by (simp only:)
    qed
  qed
  ultimately show "\<exists>xi. \<forall>y \<in> F. a y \<le> xi \<and> xi \<le> b y" by blast
qed

text \<open>
  \<^medskip>
  The function \<open>h'\<close> is defined as a \<open>h' x = h y + a \<cdot> \<xi>\<close> where \<open>x = y + a \<cdot> \<xi>\<close>
  is a linear extension of \<open>h\<close> to \<open>H'\<close>.
\<close>

lemma h'_lf:
  assumes h'_def: "\<And>x. h' x = (let (y, a) =
      SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H in h y + a * xi)"
    and H'_def: "H' = H + lin x0"
    and HE: "H \<unlhd> E"
  assumes "linearform H h"
  assumes x0: "x0 \<notin> H"  "x0 \<in> E"  "x0 \<noteq> 0"
  assumes E: "vectorspace E"
  shows "linearform H' h'"
proof -
  interpret linearform H h by fact
  interpret vectorspace E by fact
  show ?thesis
  proof
    note E = \<open>vectorspace E\<close>
    have H': "vectorspace H'"
    proof (unfold H'_def)
      from \<open>x0 \<in> E\<close>
      have "lin x0 \<unlhd> E" ..
      with HE show "vectorspace (H + lin x0)" using E ..
    qed
    show "h' (x1 + x2) = h' x1 + h' x2" if x1: "x1 \<in> H'" and x2: "x2 \<in> H'" for x1 x2
    proof -
      from H' x1 x2 have "x1 + x2 \<in> H'"
        by (rule vectorspace.add_closed)
      with x1 x2 obtain y y1 y2 a a1 a2 where
        x1x2: "x1 + x2 = y + a \<cdot> x0" and y: "y \<in> H"
        and x1_rep: "x1 = y1 + a1 \<cdot> x0" and y1: "y1 \<in> H"
        and x2_rep: "x2 = y2 + a2 \<cdot> x0" and y2: "y2 \<in> H"
        unfolding H'_def sum_def lin_def by blast

      have ya: "y1 + y2 = y \<and> a1 + a2 = a" using E HE _ y x0
      proof (rule decomp_H') text_raw \<open>\label{decomp-H-use}\<close>
        from HE y1 y2 show "y1 + y2 \<in> H"
          by (rule subspace.add_closed)
        from x0 and HE y y1 y2
        have "x0 \<in> E"  "y \<in> E"  "y1 \<in> E"  "y2 \<in> E" by auto
        with x1_rep x2_rep have "(y1 + y2) + (a1 + a2) \<cdot> x0 = x1 + x2"
          by (simp add: add_ac add_mult_distrib2)
        also note x1x2
        finally show "(y1 + y2) + (a1 + a2) \<cdot> x0 = y + a \<cdot> x0" .
      qed

      from h'_def x1x2 E HE y x0
      have "h' (x1 + x2) = h y + a * xi"
        by (rule h'_definite)
      also have "\<dots> = h (y1 + y2) + (a1 + a2) * xi"
        by (simp only: ya)
      also from y1 y2 have "h (y1 + y2) = h y1 + h y2"
        by simp
      also have "\<dots> + (a1 + a2) * xi = (h y1 + a1 * xi) + (h y2 + a2 * xi)"
        by (simp add: distrib_right)
      also from h'_def x1_rep E HE y1 x0
      have "h y1 + a1 * xi = h' x1"
        by (rule h'_definite [symmetric])
      also from h'_def x2_rep E HE y2 x0
      have "h y2 + a2 * xi = h' x2"
        by (rule h'_definite [symmetric])
      finally show ?thesis .
    qed
    show "h' (c \<cdot> x1) = c * (h' x1)" if x1: "x1 \<in> H'" for x1 c
    proof -
      from H' x1 have ax1: "c \<cdot> x1 \<in> H'"
        by (rule vectorspace.mult_closed)
      with x1 obtain y a y1 a1 where
          cx1_rep: "c \<cdot> x1 = y + a \<cdot> x0" and y: "y \<in> H"
        and x1_rep: "x1 = y1 + a1 \<cdot> x0" and y1: "y1 \<in> H"
        unfolding H'_def sum_def lin_def by blast

      have ya: "c \<cdot> y1 = y \<and> c * a1 = a" using E HE _ y x0
      proof (rule decomp_H')
        from HE y1 show "c \<cdot> y1 \<in> H"
          by (rule subspace.mult_closed)
        from x0 and HE y y1
        have "x0 \<in> E"  "y \<in> E"  "y1 \<in> E" by auto
        with x1_rep have "c \<cdot> y1 + (c * a1) \<cdot> x0 = c \<cdot> x1"
          by (simp add: mult_assoc add_mult_distrib1)
        also note cx1_rep
        finally show "c \<cdot> y1 + (c * a1) \<cdot> x0 = y + a \<cdot> x0" .
      qed

      from h'_def cx1_rep E HE y x0 have "h' (c \<cdot> x1) = h y + a * xi"
        by (rule h'_definite)
      also have "\<dots> = h (c \<cdot> y1) + (c * a1) * xi"
        by (simp only: ya)
      also from y1 have "h (c \<cdot> y1) = c * h y1"
        by simp
      also have "\<dots> + (c * a1) * xi = c * (h y1 + a1 * xi)"
        by (simp only: distrib_left)
      also from h'_def x1_rep E HE y1 x0 have "h y1 + a1 * xi = h' x1"
        by (rule h'_definite [symmetric])
      finally show ?thesis .
    qed
  qed
qed

text \<open>
  \<^medskip>
  The linear extension \<open>h'\<close> of \<open>h\<close> is bounded by the seminorm \<open>p\<close>.
\<close>

lemma h'_norm_pres:
  assumes h'_def: "\<And>x. h' x = (let (y, a) =
      SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H in h y + a * xi)"
    and H'_def: "H' = H + lin x0"
    and x0: "x0 \<notin> H"  "x0 \<in> E"  "x0 \<noteq> 0"
  assumes E: "vectorspace E" and HE: "subspace H E"
    and "seminorm E p" and "linearform H h"
  assumes a: "\<forall>y \<in> H. h y \<le> p y"
    and a': "\<forall>y \<in> H. - p (y + x0) - h y \<le> xi \<and> xi \<le> p (y + x0) - h y"
  shows "\<forall>x \<in> H'. h' x \<le> p x"
proof -
  interpret vectorspace E by fact
  interpret subspace H E by fact
  interpret seminorm E p by fact
  interpret linearform H h by fact
  show ?thesis
  proof
    fix x assume x': "x \<in> H'"
    show "h' x \<le> p x"
    proof -
      from a' have a1: "\<forall>ya \<in> H. - p (ya + x0) - h ya \<le> xi"
        and a2: "\<forall>ya \<in> H. xi \<le> p (ya + x0) - h ya" by auto
      from x' obtain y a where
          x_rep: "x = y + a \<cdot> x0" and y: "y \<in> H"
        unfolding H'_def sum_def lin_def by blast
      from y have y': "y \<in> E" ..
      from y have ay: "inverse a \<cdot> y \<in> H" by simp

      from h'_def x_rep E HE y x0 have "h' x = h y + a * xi"
        by (rule h'_definite)
      also have "\<dots> \<le> p (y + a \<cdot> x0)"
      proof (rule linorder_cases)
        assume z: "a = 0"
        then have "h y + a * xi = h y" by simp
        also from a y have "\<dots> \<le> p y" ..
        also from x0 y' z have "p y = p (y + a \<cdot> x0)" by simp
        finally show ?thesis .
      next
        txt \<open>In the case \<open>a < 0\<close>, we use \<open>a\<^sub>1\<close>
          with \<open>ya\<close> taken as \<open>y / a\<close>:\<close>
        assume lz: "a < 0" then have nz: "a \<noteq> 0" by simp
        from a1 ay
        have "- p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y) \<le> xi" ..
        with lz have "a * xi \<le>
          a * (- p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y))"
          by (simp add: mult_left_mono_neg order_less_imp_le)

        also have "\<dots> =
          - a * (p (inverse a \<cdot> y + x0)) - a * (h (inverse a \<cdot> y))"
          by (simp add: right_diff_distrib)
        also from lz x0 y' have "- a * (p (inverse a \<cdot> y + x0)) =
          p (a \<cdot> (inverse a \<cdot> y + x0))"
          by (simp add: abs_homogenous)
        also from nz x0 y' have "\<dots> = p (y + a \<cdot> x0)"
          by (simp add: add_mult_distrib1 mult_assoc [symmetric])
        also from nz y have "a * (h (inverse a \<cdot> y)) =  h y"
          by simp
        finally have "a * xi \<le> p (y + a \<cdot> x0) - h y" .
        then show ?thesis by simp
      next
        txt \<open>In the case \<open>a > 0\<close>, we use \<open>a\<^sub>2\<close>
          with \<open>ya\<close> taken as \<open>y / a\<close>:\<close>
        assume gz: "0 < a" then have nz: "a \<noteq> 0" by simp
        from a2 ay
        have "xi \<le> p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y)" ..
        with gz have "a * xi \<le>
          a * (p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y))"
          by simp
        also have "\<dots> = a * p (inverse a \<cdot> y + x0) - a * h (inverse a \<cdot> y)"
          by (simp add: right_diff_distrib)
        also from gz x0 y'
        have "a * p (inverse a \<cdot> y + x0) = p (a \<cdot> (inverse a \<cdot> y + x0))"
          by (simp add: abs_homogenous)
        also from nz x0 y' have "\<dots> = p (y + a \<cdot> x0)"
          by (simp add: add_mult_distrib1 mult_assoc [symmetric])
        also from nz y have "a * h (inverse a \<cdot> y) = h y"
          by simp
        finally have "a * xi \<le> p (y + a \<cdot> x0) - h y" .
        then show ?thesis by simp
      qed
      also from x_rep have "\<dots> = p x" by (simp only:)
      finally show ?thesis .
    qed
  qed
qed

end
