(*  Title:      HOL/Real/HahnBanach/HahnBanachSupLemmas.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* The supremum w.r.t.~the function order *}

theory HahnBanachSupLemmas = FunctionNorm + ZornLemma:

text {*
  This section contains some lemmas that will be used in the proof of
  the Hahn-Banach Theorem.  In this section the following context is
  presumed.  Let @{text E} be a real vector space with a seminorm
  @{text p} on @{text E}.  @{text F} is a subspace of @{text E} and
  @{text f} a linear form on @{text F}. We consider a chain @{text c}
  of norm-preserving extensions of @{text f}, such that @{text "\<Union>c =
  graph H h"}.  We will show some properties about the limit function
  @{text h}, i.e.\ the supremum of the chain @{text c}.

  \medskip Let @{text c} be a chain of norm-preserving extensions of
  the function @{text f} and let @{text "graph H h"} be the supremum
  of @{text c}.  Every element in @{text H} is member of one of the
  elements of the chain.
*}

lemma some_H'h't:
  assumes M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chain M"
    and u: "graph H h = \<Union>c"
    and x: "x \<in> H"
  shows "\<exists>H' h'. graph H' h' \<in> c
    \<and> (x, h x) \<in> graph H' h'
    \<and> linearform H' h' \<and> H' \<unlhd> E
    \<and> F \<unlhd> H' \<and> graph F f \<subseteq> graph H' h'
    \<and> (\<forall>x \<in> H'. h' x \<le> p x)"
proof -
  from x have "(x, h x) \<in> graph H h" ..
  also from u have "\<dots> = \<Union>c" .
  finally obtain g where gc: "g \<in> c" and gh: "(x, h x) \<in> g" by blast

  from cM have "c \<subseteq> M" ..
  with gc have "g \<in> M" ..
  also from M have "\<dots> = norm_pres_extensions E p F f" .
  finally obtain H' and h' where g: "g = graph H' h'"
    and * : "linearform H' h'"  "H' \<unlhd> E"  "F \<unlhd> H'"
      "graph F f \<subseteq> graph H' h'"  "\<forall>x \<in> H'. h' x \<le> p x" ..

  from gc and g have "graph H' h' \<in> c" by (simp only:)
  moreover from gh and g have "(x, h x) \<in> graph H' h'" by (simp only:)
  ultimately show ?thesis using * by blast
qed

text {*
  \medskip Let @{text c} be a chain of norm-preserving extensions of
  the function @{text f} and let @{text "graph H h"} be the supremum
  of @{text c}.  Every element in the domain @{text H} of the supremum
  function is member of the domain @{text H'} of some function @{text
  h'}, such that @{text h} extends @{text h'}.
*}

lemma some_H'h':
  assumes M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chain M"
    and u: "graph H h = \<Union>c"
    and x: "x \<in> H"
  shows "\<exists>H' h'. x \<in> H' \<and> graph H' h' \<subseteq> graph H h
    \<and> linearform H' h' \<and> H' \<unlhd> E \<and> F \<unlhd> H'
    \<and> graph F f \<subseteq> graph H' h' \<and> (\<forall>x \<in> H'. h' x \<le> p x)"
proof -
  from M cM u x obtain H' h' where
      x_hx: "(x, h x) \<in> graph H' h'"
    and c: "graph H' h' \<in> c"
    and * : "linearform H' h'"  "H' \<unlhd> E"  "F \<unlhd> H'"
      "graph F f \<subseteq> graph H' h'"  "\<forall>x \<in> H'. h' x \<le> p x"
    by (rule some_H'h't [elim_format]) blast
  from x_hx have "x \<in> H'" ..
  moreover from cM u c have "graph H' h' \<subseteq> graph H h"
    by (simp only: chain_ball_Union_upper)
  ultimately show ?thesis using * by blast
qed

text {*
  \medskip Any two elements @{text x} and @{text y} in the domain
  @{text H} of the supremum function @{text h} are both in the domain
  @{text H'} of some function @{text h'}, such that @{text h} extends
  @{text h'}.
*}

lemma some_H'h'2:
  assumes M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chain M"
    and u: "graph H h = \<Union>c"
    and x: "x \<in> H"
    and y: "y \<in> H"
  shows "\<exists>H' h'. x \<in> H' \<and> y \<in> H'
    \<and> graph H' h' \<subseteq> graph H h
    \<and> linearform H' h' \<and> H' \<unlhd> E \<and> F \<unlhd> H'
    \<and> graph F f \<subseteq> graph H' h' \<and> (\<forall>x \<in> H'. h' x \<le> p x)"
proof -
  txt {* @{text y} is in the domain @{text H''} of some function @{text h''},
  such that @{text h} extends @{text h''}. *}

  from M cM u and y obtain H' h' where
      y_hy: "(y, h y) \<in> graph H' h'"
    and c': "graph H' h' \<in> c"
    and * :
      "linearform H' h'"  "H' \<unlhd> E"  "F \<unlhd> H'"
      "graph F f \<subseteq> graph H' h'"  "\<forall>x \<in> H'. h' x \<le> p x"
    by (rule some_H'h't [elim_format]) blast

  txt {* @{text x} is in the domain @{text H'} of some function @{text h'},
    such that @{text h} extends @{text h'}. *}

  from M cM u and x obtain H'' h'' where
      x_hx: "(x, h x) \<in> graph H'' h''"
    and c'': "graph H'' h'' \<in> c"
    and ** :
      "linearform H'' h''"  "H'' \<unlhd> E"  "F \<unlhd> H''"
      "graph F f \<subseteq> graph H'' h''"  "\<forall>x \<in> H''. h'' x \<le> p x"
    by (rule some_H'h't [elim_format]) blast

  txt {* Since both @{text h'} and @{text h''} are elements of the chain,
    @{text h''} is an extension of @{text h'} or vice versa. Thus both
    @{text x} and @{text y} are contained in the greater
    one. \label{cases1}*}

  from cM have "graph H'' h'' \<subseteq> graph H' h' \<or> graph H' h' \<subseteq> graph H'' h''"
    (is "?case1 \<or> ?case2") ..
  then show ?thesis
  proof
    assume ?case1
    have "(x, h x) \<in> graph H'' h''" .
    also have "... \<subseteq> graph H' h'" .
    finally have xh:"(x, h x) \<in> graph H' h'" .
    then have "x \<in> H'" ..
    moreover from y_hy have "y \<in> H'" ..
    moreover from cM u and c' have "graph H' h' \<subseteq> graph H h"
      by (simp only: chain_ball_Union_upper)
    ultimately show ?thesis using * by blast
  next
    assume ?case2
    from x_hx have "x \<in> H''" ..
    moreover {
      from y_hy have "(y, h y) \<in> graph H' h'" .
      also have "\<dots> \<subseteq> graph H'' h''" .
      finally have "(y, h y) \<in> graph H'' h''" .
    } then have "y \<in> H''" ..
    moreover from cM u and c'' have "graph H'' h'' \<subseteq> graph H h"
      by (simp only: chain_ball_Union_upper)
    ultimately show ?thesis using ** by blast
  qed
qed

text {*
  \medskip The relation induced by the graph of the supremum of a
  chain @{text c} is definite, i.~e.~t is the graph of a function.
*}

lemma sup_definite:
  assumes M_def: "M \<equiv> norm_pres_extensions E p F f"
    and cM: "c \<in> chain M"
    and xy: "(x, y) \<in> \<Union>c"
    and xz: "(x, z) \<in> \<Union>c"
  shows "z = y"
proof -
  from cM have c: "c \<subseteq> M" ..
  from xy obtain G1 where xy': "(x, y) \<in> G1" and G1: "G1 \<in> c" ..
  from xz obtain G2 where xz': "(x, z) \<in> G2" and G2: "G2 \<in> c" ..

  from G1 c have "G1 \<in> M" ..
  then obtain H1 h1 where G1_rep: "G1 = graph H1 h1"
    by (unfold M_def) blast

  from G2 c have "G2 \<in> M" ..
  then obtain H2 h2 where G2_rep: "G2 = graph H2 h2"
    by (unfold M_def) blast

  txt {* @{text "G\<^sub>1"} is contained in @{text "G\<^sub>2"}
    or vice versa, since both @{text "G\<^sub>1"} and @{text
    "G\<^sub>2"} are members of @{text c}. \label{cases2}*}

  from cM G1 G2 have "G1 \<subseteq> G2 \<or> G2 \<subseteq> G1" (is "?case1 \<or> ?case2") ..
  then show ?thesis
  proof
    assume ?case1
    with xy' G2_rep have "(x, y) \<in> graph H2 h2" by blast
    hence "y = h2 x" ..
    also
    from xz' G2_rep have "(x, z) \<in> graph H2 h2" by (simp only:)
    hence "z = h2 x" ..
    finally show ?thesis .
  next
    assume ?case2
    with xz' G1_rep have "(x, z) \<in> graph H1 h1" by blast
    hence "z = h1 x" ..
    also
    from xy' G1_rep have "(x, y) \<in> graph H1 h1" by (simp only:)
    hence "y = h1 x" ..
    finally show ?thesis ..
  qed
qed

text {*
  \medskip The limit function @{text h} is linear. Every element
  @{text x} in the domain of @{text h} is in the domain of a function
  @{text h'} in the chain of norm preserving extensions.  Furthermore,
  @{text h} is an extension of @{text h'} so the function values of
  @{text x} are identical for @{text h'} and @{text h}.  Finally, the
  function @{text h'} is linear by construction of @{text M}.
*}

lemma sup_lf:
  assumes M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chain M"
    and u: "graph H h = \<Union>c"
  shows "linearform H h"
proof
  fix x y assume x: "x \<in> H" and y: "y \<in> H"
  with M cM u obtain H' h' where
        x': "x \<in> H'" and y': "y \<in> H'"
      and b: "graph H' h' \<subseteq> graph H h"
      and linearform: "linearform H' h'"
      and subspace: "H' \<unlhd> E"
    by (rule some_H'h'2 [elim_format]) blast

  show "h (x + y) = h x + h y"
  proof -
    from linearform x' y' have "h' (x + y) = h' x + h' y"
      by (rule linearform.add)
    also from b x' have "h' x = h x" ..
    also from b y' have "h' y = h y" ..
    also from subspace x' y' have "x + y \<in> H'"
      by (rule subspace.add_closed)
    with b have "h' (x + y) = h (x + y)" ..
    finally show ?thesis .
  qed
next
  fix x a assume x: "x \<in> H"
  with M cM u obtain H' h' where
        x': "x \<in> H'"
      and b: "graph H' h' \<subseteq> graph H h"
      and linearform: "linearform H' h'"
      and subspace: "H' \<unlhd> E"
    by (rule some_H'h' [elim_format]) blast

  show "h (a \<cdot> x) = a * h x"
  proof -
    from linearform x' have "h' (a \<cdot> x) = a * h' x"
      by (rule linearform.mult)
    also from b x' have "h' x = h x" ..
    also from subspace x' have "a \<cdot> x \<in> H'"
      by (rule subspace.mult_closed)
    with b have "h' (a \<cdot> x) = h (a \<cdot> x)" ..
    finally show ?thesis .
  qed
qed

text {*
  \medskip The limit of a non-empty chain of norm preserving
  extensions of @{text f} is an extension of @{text f}, since every
  element of the chain is an extension of @{text f} and the supremum
  is an extension for every element of the chain.
*}

lemma sup_ext:
  assumes graph: "graph H h = \<Union>c"
    and M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chain M"
    and ex: "\<exists>x. x \<in> c"
  shows "graph F f \<subseteq> graph H h"
proof -
  from ex obtain x where xc: "x \<in> c" ..
  from cM have "c \<subseteq> M" ..
  with xc have "x \<in> M" ..
  with M have "x \<in> norm_pres_extensions E p F f"
    by (simp only:)
  then obtain G g where "x = graph G g" and "graph F f \<subseteq> graph G g" ..
  then have "graph F f \<subseteq> x" by (simp only:)
  also from xc have "\<dots> \<subseteq> \<Union>c" by blast
  also from graph have "\<dots> = graph H h" ..
  finally show ?thesis .
qed

text {*
  \medskip The domain @{text H} of the limit function is a superspace
  of @{text F}, since @{text F} is a subset of @{text H}. The
  existence of the @{text 0} element in @{text F} and the closure
  properties follow from the fact that @{text F} is a vector space.
*}

lemma sup_supF:
  assumes graph: "graph H h = \<Union>c"
    and M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chain M"
    and ex: "\<exists>x. x \<in> c"
    and FE: "F \<unlhd> E"
  shows "F \<unlhd> H"
proof
  from FE show "F \<noteq> {}" by (rule subspace.non_empty)
  from graph M cM ex have "graph F f \<subseteq> graph H h" by (rule sup_ext)
  then show "F \<subseteq> H" ..
  fix x y assume "x \<in> F" and "y \<in> F"
  with FE show "x + y \<in> F" by (rule subspace.add_closed)
next
  fix x a assume "x \<in> F"
  with FE show "a \<cdot> x \<in> F" by (rule subspace.mult_closed)
qed

text {*
  \medskip The domain @{text H} of the limit function is a subspace of
  @{text E}.
*}

lemma sup_subE:
  assumes graph: "graph H h = \<Union>c"
    and M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chain M"
    and ex: "\<exists>x. x \<in> c"
    and FE: "F \<unlhd> E"
    and E: "vectorspace E"
  shows "H \<unlhd> E"
proof
  show "H \<noteq> {}"
  proof -
    from FE E have "0 \<in> F" by (rule subvectorspace.zero)
    also from graph M cM ex FE have "F \<unlhd> H" by (rule sup_supF)
    then have "F \<subseteq> H" ..
    finally show ?thesis by blast
  qed
  show "H \<subseteq> E"
  proof
    fix x assume "x \<in> H"
    with M cM graph
    obtain H' h' where x: "x \<in> H'" and H'E: "H' \<unlhd> E"
      by (rule some_H'h' [elim_format]) blast
    from H'E have "H' \<subseteq> E" ..
    with x show "x \<in> E" ..
  qed
  fix x y assume x: "x \<in> H" and y: "y \<in> H"
  show "x + y \<in> H"
  proof -
    from M cM graph x y obtain H' h' where
          x': "x \<in> H'" and y': "y \<in> H'" and H'E: "H' \<unlhd> E"
        and graphs: "graph H' h' \<subseteq> graph H h"
      by (rule some_H'h'2 [elim_format]) blast
    from H'E x' y' have "x + y \<in> H'"
      by (rule subspace.add_closed)
    also from graphs have "H' \<subseteq> H" ..
    finally show ?thesis .
  qed
next
  fix x a assume x: "x \<in> H"
  show "a \<cdot> x \<in> H"
  proof -
    from M cM graph x
    obtain H' h' where x': "x \<in> H'" and H'E: "H' \<unlhd> E"
        and graphs: "graph H' h' \<subseteq> graph H h"
      by (rule some_H'h' [elim_format]) blast
    from H'E x' have "a \<cdot> x \<in> H'" by (rule subspace.mult_closed)
    also from graphs have "H' \<subseteq> H" ..
    finally show ?thesis .
  qed
qed

text {*
  \medskip The limit function is bounded by the norm @{text p} as
  well, since all elements in the chain are bounded by @{text p}.
*}

lemma sup_norm_pres:
  assumes graph: "graph H h = \<Union>c"
    and M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chain M"
  shows "\<forall>x \<in> H. h x \<le> p x"
proof
  fix x assume "x \<in> H"
  with M cM graph obtain H' h' where x': "x \<in> H'"
      and graphs: "graph H' h' \<subseteq> graph H h"
      and a: "\<forall>x \<in> H'. h' x \<le> p x"
    by (rule some_H'h' [elim_format]) blast
  from graphs x' have [symmetric]: "h' x = h x" ..
  also from a x' have "h' x \<le> p x " ..
  finally show "h x \<le> p x" .
qed

text {*
  \medskip The following lemma is a property of linear forms on real
  vector spaces. It will be used for the lemma @{text abs_HahnBanach}
  (see page \pageref{abs-HahnBanach}). \label{abs-ineq-iff} For real
  vector spaces the following inequations are equivalent:
  \begin{center}
  \begin{tabular}{lll}
  @{text "\<forall>x \<in> H. \<bar>h x\<bar> \<le> p x"} & and &
  @{text "\<forall>x \<in> H. h x \<le> p x"} \\
  \end{tabular}
  \end{center}
*}

lemma abs_ineq_iff:
  includes subvectorspace H E + seminorm E p + linearform H h
  shows "(\<forall>x \<in> H. \<bar>h x\<bar> \<le> p x) = (\<forall>x \<in> H. h x \<le> p x)" (is "?L = ?R")
proof
  have h: "vectorspace H" by (rule vectorspace)
  {
    assume l: ?L
    show ?R
    proof
      fix x assume x: "x \<in> H"
      have "h x \<le> \<bar>h x\<bar>" by arith
      also from l x have "\<dots> \<le> p x" ..
      finally show "h x \<le> p x" .
    qed
  next
    assume r: ?R
    show ?L
    proof
      fix x assume x: "x \<in> H"
      show "\<And>a b :: real. - a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> \<bar>b\<bar> \<le> a"
        by arith
      show "- p x \<le> h x"
      proof (rule real_minus_le)
        have "linearform H h" .
        from h this x have "- h x = h (- x)"
          by (rule vectorspace_linearform.neg [symmetric])
        also from r x have "\<dots> \<le> p (- x)" by simp
        also have "\<dots> = p x"
        proof (rule seminorm_vectorspace.minus)
          show "x \<in> E" ..
        qed
        finally show "- h x \<le> p x" .
      qed
      from r x show "h x \<le> p x" ..
    qed
  }
qed

end
