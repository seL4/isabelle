(*  Title:      HOL/Real/HahnBanach/HahnBanachExtLemmas.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* Extending non-maximal functions *}

theory HahnBanachExtLemmas = FunctionNorm:

text {*
  In this section the following context is presumed.  Let @{text E} be
  a real vector space with a seminorm @{text q} on @{text E}. @{text
  F} is a subspace of @{text E} and @{text f} a linear function on
  @{text F}. We consider a subspace @{text H} of @{text E} that is a
  superspace of @{text F} and a linear form @{text h} on @{text
  H}. @{text H} is a not equal to @{text E} and @{text "x\<^sub>0"} is
  an element in @{text "E - H"}.  @{text H} is extended to the direct
  sum @{text "H' = H + lin x\<^sub>0"}, so for any @{text "x \<in> H'"}
  the decomposition of @{text "x = y + a \<cdot> x"} with @{text "y \<in> H"} is
  unique. @{text h'} is defined on @{text H'} by @{text "h' x = h y +
  a \<cdot> \<xi>"} for a certain @{text \<xi>}.

  Subsequently we show some properties of this extension @{text h'} of
  @{text h}.

  \medskip This lemma will be used to show the existence of a linear
  extension of @{text f} (see page \pageref{ex-xi-use}). It is a
  consequence of the completeness of @{text \<real>}. To show
  \begin{center}
  \begin{tabular}{l}
  @{text "\<exists>\<xi>. \<forall>y \<in> F. a y \<le> \<xi> \<and> \<xi> \<le> b y"}
  \end{tabular}
  \end{center}
  \noindent it suffices to show that
  \begin{center}
  \begin{tabular}{l}
  @{text "\<forall>u \<in> F. \<forall>v \<in> F. a u \<le> b v"}
  \end{tabular}
  \end{center}
*}

lemma ex_xi:
  includes vectorspace F
  assumes r: "\<And>u v. u \<in> F \<Longrightarrow> v \<in> F \<Longrightarrow> a u \<le> b v"
  shows "\<exists>xi::real. \<forall>y \<in> F. a y \<le> xi \<and> xi \<le> b y"
proof -
  txt {* From the completeness of the reals follows:
    The set @{text "S = {a u. u \<in> F}"} has a supremum, if it is
    non-empty and has an upper bound. *}

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
  {
    fix y assume "y \<in> F"
    then have "a y \<in> ?S" by blast
    with xi have "a y \<le> xi" by (rule lub.upper)
  } moreover {
    fix y assume y: "y \<in> F"
    from xi have "xi \<le> b y"
    proof (rule lub.least)
      fix au assume "au \<in> ?S"
      then obtain u where u: "u \<in> F" and au: "au = a u" by blast
      from u y have "a u \<le> b y" by (rule r)
      with au show "au \<le> b y" by (simp only:)
    qed
  } ultimately show "\<exists>xi. \<forall>y \<in> F. a y \<le> xi \<and> xi \<le> b y" by blast
qed

text {*
  \medskip The function @{text h'} is defined as a @{text "h' x = h y
  + a \<cdot> \<xi>"} where @{text "x = y + a \<cdot> \<xi>"} is a linear extension of
  @{text h} to @{text H'}.
*}

lemma h'_lf:
  includes var H + var h + var E
  assumes h'_def: "h' \<equiv> \<lambda>x. let (y, a) =
      SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H in h y + a * xi"
    and H'_def: "H' \<equiv> H + lin x0"
    and HE: "H \<unlhd> E"
  includes linearform H h
  assumes x0: "x0 \<notin> H"  "x0 \<in> E"  "x0 \<noteq> 0"
  includes vectorspace E
  shows "linearform H' h'"
proof
  have H': "vectorspace H'"
  proof (unfold H'_def)
    have "x0 \<in> E" .
    then have "lin x0 \<unlhd> E" ..
    with HE show "vectorspace (H + lin x0)" ..
  qed
  {
    fix x1 x2 assume x1: "x1 \<in> H'" and x2: "x2 \<in> H'"
    show "h' (x1 + x2) = h' x1 + h' x2"
    proof -
      from H' x1 x2 have "x1 + x2 \<in> H'"
        by (rule vectorspace.add_closed)
      with x1 x2 obtain y y1 y2 a a1 a2 where
            x1x2: "x1 + x2 = y + a \<cdot> x0" and y: "y \<in> H"
          and x1_rep: "x1 = y1 + a1 \<cdot> x0" and y1: "y1 \<in> H"
          and x2_rep: "x2 = y2 + a2 \<cdot> x0" and y2: "y2 \<in> H"
        by (unfold H'_def sum_def lin_def) blast

      have ya: "y1 + y2 = y \<and> a1 + a2 = a" using _ HE _ y x0
      proof (rule decomp_H') txt_raw {* \label{decomp-H-use} *}
        from HE y1 y2 show "y1 + y2 \<in> H"
          by (rule subspace.add_closed)
        from x0 and HE y y1 y2
        have "x0 \<in> E"  "y \<in> E"  "y1 \<in> E"  "y2 \<in> E" by auto
        with x1_rep x2_rep have "(y1 + y2) + (a1 + a2) \<cdot> x0 = x1 + x2"
          by (simp add: add_ac add_mult_distrib2)
        also note x1x2
        finally show "(y1 + y2) + (a1 + a2) \<cdot> x0 = y + a \<cdot> x0" .
      qed

      from h'_def x1x2 _ HE y x0
      have "h' (x1 + x2) = h y + a * xi"
        by (rule h'_definite)
      also have "\<dots> = h (y1 + y2) + (a1 + a2) * xi"
        by (simp only: ya)
      also from y1 y2 have "h (y1 + y2) = h y1 + h y2"
        by simp
      also have "\<dots> + (a1 + a2) * xi = (h y1 + a1 * xi) + (h y2 + a2 * xi)"
        by (simp add: left_distrib)
      also from h'_def x1_rep _ HE y1 x0
      have "h y1 + a1 * xi = h' x1"
        by (rule h'_definite [symmetric])
      also from h'_def x2_rep _ HE y2 x0
      have "h y2 + a2 * xi = h' x2"
        by (rule h'_definite [symmetric])
      finally show ?thesis .
    qed
  next
    fix x1 c assume x1: "x1 \<in> H'"
    show "h' (c \<cdot> x1) = c * (h' x1)"
    proof -
      from H' x1 have ax1: "c \<cdot> x1 \<in> H'"
        by (rule vectorspace.mult_closed)
      with x1 obtain y a y1 a1 where
            cx1_rep: "c \<cdot> x1 = y + a \<cdot> x0" and y: "y \<in> H"
          and x1_rep: "x1 = y1 + a1 \<cdot> x0" and y1: "y1 \<in> H"
        by (unfold H'_def sum_def lin_def) blast

      have ya: "c \<cdot> y1 = y \<and> c * a1 = a" using _ HE _ y x0
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

      from h'_def cx1_rep _ HE y x0 have "h' (c \<cdot> x1) = h y + a * xi"
        by (rule h'_definite)
      also have "\<dots> = h (c \<cdot> y1) + (c * a1) * xi"
        by (simp only: ya)
      also from y1 have "h (c \<cdot> y1) = c * h y1"
        by simp
      also have "\<dots> + (c * a1) * xi = c * (h y1 + a1 * xi)"
        by (simp only: right_distrib)
      also from h'_def x1_rep _ HE y1 x0 have "h y1 + a1 * xi = h' x1"
        by (rule h'_definite [symmetric])
      finally show ?thesis .
    qed
  }
qed

text {* \medskip The linear extension @{text h'} of @{text h}
  is bounded by the seminorm @{text p}. *}

lemma h'_norm_pres:
  includes var H + var h + var E
  assumes h'_def: "h' \<equiv> \<lambda>x. let (y, a) =
      SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H in h y + a * xi"
    and H'_def: "H' \<equiv> H + lin x0"
    and x0: "x0 \<notin> H"  "x0 \<in> E"  "x0 \<noteq> 0"
  includes vectorspace E + subspace H E + seminorm E p + linearform H h
  assumes a: "\<forall>y \<in> H. h y \<le> p y"
    and a': "\<forall>y \<in> H. - p (y + x0) - h y \<le> xi \<and> xi \<le> p (y + x0) - h y"
  shows "\<forall>x \<in> H'. h' x \<le> p x"
proof
  fix x assume x': "x \<in> H'"
  show "h' x \<le> p x"
  proof -
    from a' have a1: "\<forall>ya \<in> H. - p (ya + x0) - h ya \<le> xi"
      and a2: "\<forall>ya \<in> H. xi \<le> p (ya + x0) - h ya" by auto
    from x' obtain y a where
        x_rep: "x = y + a \<cdot> x0" and y: "y \<in> H"
      by (unfold H'_def sum_def lin_def) blast
    from y have y': "y \<in> E" ..
    from y have ay: "inverse a \<cdot> y \<in> H" by simp

    from h'_def x_rep _ _ y x0 have "h' x = h y + a * xi"
      by (rule h'_definite)
    also have "\<dots> \<le> p (y + a \<cdot> x0)"
    proof (rule linorder_cases)
      assume z: "a = 0"
      then have "h y + a * xi = h y" by simp
      also from a y have "\<dots> \<le> p y" ..
      also from x0 y' z have "p y = p (y + a \<cdot> x0)" by simp
      finally show ?thesis .
    next
      txt {* In the case @{text "a < 0"}, we use @{text "a\<^sub>1"}
        with @{text ya} taken as @{text "y / a"}: *}
      assume lz: "a < 0" hence nz: "a \<noteq> 0" by simp
      from a1 ay
      have "- p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y) \<le> xi" ..
      with lz have "a * xi \<le>
          a * (- p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y))"
        by (rule real_mult_less_le_anti)
      also have "\<dots> =
          - a * (p (inverse a \<cdot> y + x0)) - a * (h (inverse a \<cdot> y))"
        by (rule real_mult_diff_distrib)
      also from lz x0 y' have "- a * (p (inverse a \<cdot> y + x0)) =
          p (a \<cdot> (inverse a \<cdot> y + x0))"
        by (simp add: abs_homogenous abs_minus_eqI2)
      also from nz x0 y' have "\<dots> = p (y + a \<cdot> x0)"
        by (simp add: add_mult_distrib1 mult_assoc [symmetric])
      also from nz y have "a * (h (inverse a \<cdot> y)) =  h y"
        by simp
      finally have "a * xi \<le> p (y + a \<cdot> x0) - h y" .
      then show ?thesis by simp
    next
      txt {* In the case @{text "a > 0"}, we use @{text "a\<^sub>2"}
        with @{text ya} taken as @{text "y / a"}: *}
      assume gz: "0 < a" hence nz: "a \<noteq> 0" by simp
      from a2 ay
      have "xi \<le> p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y)" ..
      with gz have "a * xi \<le>
          a * (p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y))"
        by (rule real_mult_less_le_mono)
      also have "... = a * p (inverse a \<cdot> y + x0) - a * h (inverse a \<cdot> y)"
        by (rule real_mult_diff_distrib2)
      also from gz x0 y'
      have "a * p (inverse a \<cdot> y + x0) = p (a \<cdot> (inverse a \<cdot> y + x0))"
        by (simp add: abs_homogenous abs_eqI2)
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

end
