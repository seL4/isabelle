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
  unique. @{text h'} is defined on @{text H'} by
  @{text "h' x = h y + a \<cdot> \<xi>"} for a certain @{text \<xi>}.

  Subsequently we show some properties of this extension @{text h'} of
  @{text h}.
*}

text {*
  This lemma will be used to show the existence of a linear extension
  of @{text f} (see page \pageref{ex-xi-use}). It is a consequence of
  the completeness of @{text \<real>}. To show
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
  "is_vectorspace F \<Longrightarrow> (\<And>u v. u \<in> F \<Longrightarrow> v \<in> F \<Longrightarrow> a u \<le> b v)
  \<Longrightarrow> \<exists>xi::real. \<forall>y \<in> F. a y \<le> xi \<and> xi \<le> b y"
proof -
  assume vs: "is_vectorspace F"
  assume r: "(\<And>u v. u \<in> F \<Longrightarrow> v \<in> F \<Longrightarrow> a u \<le> (b v::real))"

  txt {* From the completeness of the reals follows:
  The set @{text "S = {a u. u \<in> F}"} has a supremum, if
  it is non-empty and has an upper bound. *}

  let ?S = "{a u :: real | u. u \<in> F}"

  have "\<exists>xi. isLub UNIV ?S xi"
  proof (rule reals_complete)

    txt {* The set @{text S} is non-empty, since @{text "a 0 \<in> S"}: *}

    from vs have "a 0 \<in> ?S" by blast
    thus "\<exists>X. X \<in> ?S" ..

    txt {* @{text "b 0"} is an upper bound of @{text S}: *}

    show "\<exists>Y. isUb UNIV ?S Y"
    proof
      show "isUb UNIV ?S (b 0)"
      proof (intro isUbI setleI ballI)
        show "b 0 \<in> UNIV" ..
      next

        txt {* Every element @{text "y \<in> S"} is less than @{text "b 0"}: *}

        fix y assume y: "y \<in> ?S"
        from y have "\<exists>u \<in> F. y = a u" by fast
        thus "y \<le> b 0"
        proof
          fix u assume "u \<in> F"
          assume "y = a u"
          also have "a u \<le> b 0" by (rule r) (simp!)+
          finally show ?thesis .
        qed
      qed
    qed
  qed

  thus "\<exists>xi. \<forall>y \<in> F. a y \<le> xi \<and> xi \<le> b y"
  proof (elim exE)
    fix xi assume "isLub UNIV ?S xi"
    show ?thesis
    proof (intro exI conjI ballI)

      txt {* For all @{text "y \<in> F"} holds @{text "a y \<le> \<xi>"}: *}

      fix y assume y: "y \<in> F"
      show "a y \<le> xi"
      proof (rule isUbD)
        show "isUb UNIV ?S xi" ..
      qed (blast!)
    next

      txt {* For all @{text "y \<in> F"} holds @{text "\<xi> \<le> b y"}: *}

      fix y assume "y \<in> F"
      show "xi \<le> b y"
      proof (intro isLub_le_isUb isUbI setleI)
        show "b y \<in> UNIV" ..
        show "\<forall>ya \<in> ?S. ya \<le> b y"
        proof
          fix au assume au: "au \<in> ?S "
          hence "\<exists>u \<in> F. au = a u" by fast
          thus "au \<le> b y"
          proof
            fix u assume "u \<in> F" assume "au = a u"
            also have "... \<le> b y" by (rule r)
            finally show ?thesis .
          qed
        qed
      qed
    qed
  qed
qed

text {*
  \medskip The function @{text h'} is defined as a
  @{text "h' x = h y + a \<cdot> \<xi>"} where @{text "x = y + a \<cdot> \<xi>"} is a
  linear extension of @{text h} to @{text H'}. *}

lemma h'_lf:
  "h' \<equiv> \<lambda>x. let (y, a) = SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H in h y + a * xi
  \<Longrightarrow> H' \<equiv> H + lin x0 \<Longrightarrow> is_subspace H E \<Longrightarrow> is_linearform H h \<Longrightarrow> x0 \<notin> H
  \<Longrightarrow> x0 \<in> E \<Longrightarrow> x0 \<noteq> 0 \<Longrightarrow> is_vectorspace E
  \<Longrightarrow> is_linearform H' h'"
proof -
  assume h'_def:
    "h' \<equiv> (\<lambda>x. let (y, a) = SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H
               in h y + a * xi)"
    and H'_def: "H' \<equiv> H + lin x0"
    and vs: "is_subspace H E"  "is_linearform H h"  "x0 \<notin> H"
      "x0 \<noteq> 0"  "x0 \<in> E"  "is_vectorspace E"

  have h': "is_vectorspace H'"
  proof (unfold H'_def, rule vs_sum_vs)
    show "is_subspace (lin x0) E" ..
  qed

  show ?thesis
  proof
    fix x1 x2 assume x1: "x1 \<in> H'" and x2: "x2 \<in> H'"

    txt {* We now have to show that @{text h'} is additive, i.~e.\
      @{text "h' (x\<^sub>1 + x\<^sub>2) = h' x\<^sub>1 + h' x\<^sub>2"} for
      @{text "x\<^sub>1, x\<^sub>2 \<in> H"}. *}

    have x1x2: "x1 + x2 \<in> H'"
      by (rule vs_add_closed, rule h')
    from x1
    have ex_x1: "\<exists>y1 a1. x1 = y1 + a1 \<cdot> x0  \<and> y1 \<in> H"
      by (unfold H'_def vs_sum_def lin_def) fast
    from x2
    have ex_x2: "\<exists>y2 a2. x2 = y2 + a2 \<cdot> x0 \<and> y2 \<in> H"
      by (unfold H'_def vs_sum_def lin_def) fast
    from x1x2
    have ex_x1x2: "\<exists>y a. x1 + x2 = y + a \<cdot> x0 \<and> y \<in> H"
      by (unfold H'_def vs_sum_def lin_def) fast

    from ex_x1 ex_x2 ex_x1x2
    show "h' (x1 + x2) = h' x1 + h' x2"
    proof (elim exE conjE)
      fix y1 y2 y a1 a2 a
      assume y1: "x1 = y1 + a1 \<cdot> x0"     and y1': "y1 \<in> H"
         and y2: "x2 = y2 + a2 \<cdot> x0"     and y2': "y2 \<in> H"
         and y: "x1 + x2 = y + a \<cdot> x0"   and y':  "y  \<in> H"
      txt {* \label{decomp-H-use}*}
      have ya: "y1 + y2 = y \<and> a1 + a2 = a"
      proof (rule decomp_H')
        show "y1 + y2 + (a1 + a2) \<cdot> x0 = y + a \<cdot> x0"
          by (simp! add: vs_add_mult_distrib2 [of E])
        show "y1 + y2 \<in> H" ..
      qed

      have "h' (x1 + x2) = h y + a * xi"
        by (rule h'_definite)
      also have "... = h (y1 + y2) + (a1 + a2) * xi"
        by (simp add: ya)
      also from vs y1' y2'
      have "... = h y1 + h y2 + a1 * xi + a2 * xi"
        by (simp add: linearform_add [of H]
                      real_add_mult_distrib)
      also have "... = (h y1 + a1 * xi) + (h y2 + a2 * xi)"
        by simp
      also have "h y1 + a1 * xi = h' x1"
        by (rule h'_definite [symmetric])
      also have "h y2 + a2 * xi = h' x2"
        by (rule h'_definite [symmetric])
      finally show ?thesis .
    qed

    txt {* We further have to show that @{text h'} is multiplicative,
    i.~e.\ @{text "h' (c \<cdot> x\<^sub>1) = c \<cdot> h' x\<^sub>1"} for @{text "x \<in> H"}
    and @{text "c \<in> \<real>"}. *}

  next
    fix c x1 assume x1: "x1 \<in> H'"
    have ax1: "c \<cdot> x1 \<in> H'"
      by (rule vs_mult_closed, rule h')
    from x1
    have ex_x: "\<And>x. x\<in> H' \<Longrightarrow> \<exists>y a. x = y + a \<cdot> x0 \<and> y \<in> H"
      by (unfold H'_def vs_sum_def lin_def) fast

    from x1 have ex_x1: "\<exists>y1 a1. x1 = y1 + a1 \<cdot> x0 \<and> y1 \<in> H"
      by (unfold H'_def vs_sum_def lin_def) fast
    with ex_x [of "c \<cdot> x1", OF ax1]
    show "h' (c \<cdot> x1) = c * (h' x1)"
    proof (elim exE conjE)
      fix y1 y a1 a
      assume y1: "x1 = y1 + a1 \<cdot> x0"     and y1': "y1 \<in> H"
        and y: "c \<cdot> x1 = y  + a \<cdot> x0"    and y': "y \<in> H"

      have ya: "c \<cdot> y1 = y \<and> c * a1 = a"
      proof (rule decomp_H')
        show "c \<cdot> y1 + (c * a1) \<cdot> x0 = y + a \<cdot> x0"
          by (simp! add: vs_add_mult_distrib1)
        show "c \<cdot> y1 \<in> H" ..
      qed

      have "h' (c \<cdot> x1) = h y + a * xi"
        by (rule h'_definite)
      also have "... = h (c \<cdot> y1) + (c * a1) * xi"
        by (simp add: ya)
      also from vs y1' have "... = c * h y1 + c * a1 * xi"
        by (simp add: linearform_mult [of H])
      also from vs y1' have "... = c * (h y1 + a1 * xi)"
        by (simp add: real_add_mult_distrib2 real_mult_assoc)
      also have "h y1 + a1 * xi = h' x1"
        by (rule h'_definite [symmetric])
      finally show ?thesis .
    qed
  qed
qed

text {* \medskip The linear extension @{text h'} of @{text h}
is bounded by the seminorm @{text p}. *}

lemma h'_norm_pres:
  "h' \<equiv> \<lambda>x. let (y, a) = SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H in h y + a * xi
  \<Longrightarrow> H' \<equiv> H + lin x0 \<Longrightarrow> x0 \<notin> H \<Longrightarrow> x0 \<in> E \<Longrightarrow> x0 \<noteq> 0 \<Longrightarrow> is_vectorspace E
  \<Longrightarrow> is_subspace H E \<Longrightarrow> is_seminorm E p \<Longrightarrow> is_linearform H h
  \<Longrightarrow> \<forall>y \<in> H. h y \<le> p y
  \<Longrightarrow> \<forall>y \<in> H. - p (y + x0) - h y \<le> xi \<and> xi \<le> p (y + x0) - h y
  \<Longrightarrow> \<forall>x \<in> H'. h' x \<le> p x"
proof
  assume h'_def:
    "h' \<equiv> (\<lambda>x. let (y, a) = SOME (y, a). x = y + a \<cdot> x0 \<and> y \<in> H
               in (h y) + a * xi)"
    and H'_def: "H' \<equiv> H + lin x0"
    and vs: "x0 \<notin> H"  "x0 \<in> E"  "x0 \<noteq> 0"  "is_vectorspace E"
            "is_subspace H E"  "is_seminorm E p"  "is_linearform H h"
    and a: "\<forall>y \<in> H. h y \<le> p y"
  presume a1: "\<forall>ya \<in> H. - p (ya + x0) - h ya \<le> xi"
  presume a2: "\<forall>ya \<in> H. xi \<le> p (ya + x0) - h ya"
  fix x assume "x \<in> H'"
  have ex_x:
    "\<And>x. x \<in> H' \<Longrightarrow> \<exists>y a. x = y + a \<cdot> x0 \<and> y \<in> H"
    by (unfold H'_def vs_sum_def lin_def) fast
  have "\<exists>y a. x = y + a \<cdot> x0 \<and> y \<in> H"
    by (rule ex_x)
  thus "h' x \<le> p x"
  proof (elim exE conjE)
    fix y a assume x: "x = y + a \<cdot> x0" and y: "y \<in> H"
    have "h' x = h y + a * xi"
      by (rule h'_definite)

    txt {* Now we show @{text "h y + a \<cdot> \<xi> \<le> p (y + a \<cdot> x\<^sub>0)"}
    by case analysis on @{text a}. *}

    also have "... \<le> p (y + a \<cdot> x0)"
    proof (rule linorder_cases)

      assume z: "a = #0"
      with vs y a show ?thesis by simp

    txt {* In the case @{text "a < 0"}, we use @{text "a\<^sub>1"}
    with @{text ya} taken as @{text "y / a"}: *}

    next
      assume lz: "a < #0" hence nz: "a \<noteq> #0" by simp
      from a1
      have "- p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y) \<le> xi"
        by (rule bspec) (simp!)

      txt {* The thesis for this case now follows by a short
      calculation. *}
      hence "a * xi \<le> a * (- p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y))"
        by (rule real_mult_less_le_anti [OF lz])
      also
      have "... = - a * (p (inverse a \<cdot> y + x0)) - a * (h (inverse a \<cdot> y))"
        by (rule real_mult_diff_distrib)
      also from lz vs y
      have "- a * (p (inverse a \<cdot> y + x0)) = p (a \<cdot> (inverse a \<cdot> y + x0))"
        by (simp add: seminorm_abs_homogenous abs_minus_eqI2)
      also from nz vs y have "... = p (y + a \<cdot> x0)"
        by (simp add: vs_add_mult_distrib1)
      also from nz vs y have "a * (h (inverse a \<cdot> y)) =  h y"
        by (simp add: linearform_mult [symmetric])
      finally have "a * xi \<le> p (y + a \<cdot> x0) - h y" .

      hence "h y + a * xi \<le> h y + p (y + a \<cdot> x0) - h y"
        by (simp add: real_add_left_cancel_le)
      thus ?thesis by simp

      txt {* In the case @{text "a > 0"}, we use @{text "a\<^sub>2"}
        with @{text ya} taken as @{text "y / a"}: *}

    next
      assume gz: "#0 < a" hence nz: "a \<noteq> #0" by simp
      from a2 have "xi \<le> p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y)"
        by (rule bspec) (simp!)

      txt {* The thesis for this case follows by a short
      calculation: *}

      with gz
      have "a * xi \<le> a * (p (inverse a \<cdot> y + x0) - h (inverse a \<cdot> y))"
        by (rule real_mult_less_le_mono)
      also have "... = a * p (inverse a \<cdot> y + x0) - a * h (inverse a \<cdot> y)"
        by (rule real_mult_diff_distrib2)
      also from gz vs y
      have "a * p (inverse a \<cdot> y + x0) = p (a \<cdot> (inverse a \<cdot> y + x0))"
        by (simp add: seminorm_abs_homogenous abs_eqI2)
      also from nz vs y have "... = p (y + a \<cdot> x0)"
        by (simp add: vs_add_mult_distrib1)
      also from nz vs y have "a * h (inverse a \<cdot> y) = h y"
        by (simp add: linearform_mult [symmetric])
      finally have "a * xi \<le> p (y + a \<cdot> x0) - h y" .

      hence "h y + a * xi \<le> h y + (p (y + a \<cdot> x0) - h y)"
        by (simp add: real_add_left_cancel_le)
      thus ?thesis by simp
    qed
    also from x have "... = p x" by simp
    finally show ?thesis .
  qed
qed blast+

end
