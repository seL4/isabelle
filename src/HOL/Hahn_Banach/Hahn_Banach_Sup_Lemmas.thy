(*  Title:      HOL/Hahn_Banach/Hahn_Banach_Sup_Lemmas.thy
    Author:     Gertrud Bauer, TU Munich
*)

section \<open>The supremum wrt.\ the function order\<close>

theory Hahn_Banach_Sup_Lemmas
imports Function_Norm Zorn_Lemma
begin

text \<open>
  This section contains some lemmas that will be used in the proof of the
  Hahn-Banach Theorem. In this section the following context is presumed. Let
  \<open>E\<close> be a real vector space with a seminorm \<open>p\<close> on \<open>E\<close>. \<open>F\<close> is a subspace of
  \<open>E\<close> and \<open>f\<close> a linear form on \<open>F\<close>. We consider a chain \<open>c\<close> of norm-preserving
  extensions of \<open>f\<close>, such that \<open>\<Union>c = graph H h\<close>. We will show some properties
  about the limit function \<open>h\<close>, i.e.\ the supremum of the chain \<open>c\<close>.

  \<^medskip>
  Let \<open>c\<close> be a chain of norm-preserving extensions of the function \<open>f\<close> and let
  \<open>graph H h\<close> be the supremum of \<open>c\<close>. Every element in \<open>H\<close> is member of one of
  the elements of the chain.
\<close>

lemmas [dest?] = chainsD
lemmas chainsE2 [elim?] = chainsD2 [elim_format]

lemma some_H'h't:
  assumes M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chains M"
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

text \<open>
  \<^medskip>
  Let \<open>c\<close> be a chain of norm-preserving extensions of the function \<open>f\<close> and let
  \<open>graph H h\<close> be the supremum of \<open>c\<close>. Every element in the domain \<open>H\<close> of the
  supremum function is member of the domain \<open>H'\<close> of some function \<open>h'\<close>, such
  that \<open>h\<close> extends \<open>h'\<close>.
\<close>

lemma some_H'h':
  assumes M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chains M"
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
  moreover from cM u c have "graph H' h' \<subseteq> graph H h" by blast
  ultimately show ?thesis using * by blast
qed

text \<open>
  \<^medskip>
  Any two elements \<open>x\<close> and \<open>y\<close> in the domain \<open>H\<close> of the supremum function \<open>h\<close>
  are both in the domain \<open>H'\<close> of some function \<open>h'\<close>, such that \<open>h\<close> extends
  \<open>h'\<close>.
\<close>

lemma some_H'h'2:
  assumes M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chains M"
    and u: "graph H h = \<Union>c"
    and x: "x \<in> H"
    and y: "y \<in> H"
  shows "\<exists>H' h'. x \<in> H' \<and> y \<in> H'
    \<and> graph H' h' \<subseteq> graph H h
    \<and> linearform H' h' \<and> H' \<unlhd> E \<and> F \<unlhd> H'
    \<and> graph F f \<subseteq> graph H' h' \<and> (\<forall>x \<in> H'. h' x \<le> p x)"
proof -
  txt \<open>\<open>y\<close> is in the domain \<open>H''\<close> of some function \<open>h''\<close>, such that \<open>h\<close>
    extends \<open>h''\<close>.\<close>

  from M cM u and y obtain H' h' where
      y_hy: "(y, h y) \<in> graph H' h'"
    and c': "graph H' h' \<in> c"
    and * :
      "linearform H' h'"  "H' \<unlhd> E"  "F \<unlhd> H'"
      "graph F f \<subseteq> graph H' h'"  "\<forall>x \<in> H'. h' x \<le> p x"
    by (rule some_H'h't [elim_format]) blast

  txt \<open>\<open>x\<close> is in the domain \<open>H'\<close> of some function \<open>h'\<close>,
    such that \<open>h\<close> extends \<open>h'\<close>.\<close>

  from M cM u and x obtain H'' h'' where
      x_hx: "(x, h x) \<in> graph H'' h''"
    and c'': "graph H'' h'' \<in> c"
    and ** :
      "linearform H'' h''"  "H'' \<unlhd> E"  "F \<unlhd> H''"
      "graph F f \<subseteq> graph H'' h''"  "\<forall>x \<in> H''. h'' x \<le> p x"
    by (rule some_H'h't [elim_format]) blast

  txt \<open>Since both \<open>h'\<close> and \<open>h''\<close> are elements of the chain, \<open>h''\<close> is an
    extension of \<open>h'\<close> or vice versa. Thus both \<open>x\<close> and \<open>y\<close> are contained in
    the greater one. \label{cases1}\<close>

  from cM c'' c' consider "graph H'' h'' \<subseteq> graph H' h'" | "graph H' h' \<subseteq> graph H'' h''"
    by (blast dest: chainsD)
  then show ?thesis
  proof cases
    case 1
    have "(x, h x) \<in> graph H'' h''" by fact
    also have "\<dots> \<subseteq> graph H' h'" by fact
    finally have xh:"(x, h x) \<in> graph H' h'" .
    then have "x \<in> H'" ..
    moreover from y_hy have "y \<in> H'" ..
    moreover from cM u and c' have "graph H' h' \<subseteq> graph H h" by blast
    ultimately show ?thesis using * by blast
  next
    case 2
    from x_hx have "x \<in> H''" ..
    moreover have "y \<in> H''"
    proof -
      have "(y, h y) \<in> graph H' h'" by (rule y_hy)
      also have "\<dots> \<subseteq> graph H'' h''" by fact
      finally have "(y, h y) \<in> graph H'' h''" .
      then show ?thesis ..
    qed
    moreover from u c'' have "graph H'' h'' \<subseteq> graph H h" by blast
    ultimately show ?thesis using ** by blast
  qed
qed

text \<open>
  \<^medskip>
  The relation induced by the graph of the supremum of a chain \<open>c\<close> is
  definite, i.e.\ it is the graph of a function.
\<close>

lemma sup_definite:
  assumes M_def: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chains M"
    and xy: "(x, y) \<in> \<Union>c"
    and xz: "(x, z) \<in> \<Union>c"
  shows "z = y"
proof -
  from cM have c: "c \<subseteq> M" ..
  from xy obtain G1 where xy': "(x, y) \<in> G1" and G1: "G1 \<in> c" ..
  from xz obtain G2 where xz': "(x, z) \<in> G2" and G2: "G2 \<in> c" ..

  from G1 c have "G1 \<in> M" ..
  then obtain H1 h1 where G1_rep: "G1 = graph H1 h1"
    unfolding M_def by blast

  from G2 c have "G2 \<in> M" ..
  then obtain H2 h2 where G2_rep: "G2 = graph H2 h2"
    unfolding M_def by blast

  txt \<open>\<open>G\<^sub>1\<close> is contained in \<open>G\<^sub>2\<close> or vice versa, since both \<open>G\<^sub>1\<close> and \<open>G\<^sub>2\<close>
    are members of \<open>c\<close>. \label{cases2}\<close>

  from cM G1 G2 consider "G1 \<subseteq> G2" | "G2 \<subseteq> G1"
    by (blast dest: chainsD)
  then show ?thesis
  proof cases
    case 1
    with xy' G2_rep have "(x, y) \<in> graph H2 h2" by blast
    then have "y = h2 x" ..
    also
    from xz' G2_rep have "(x, z) \<in> graph H2 h2" by (simp only:)
    then have "z = h2 x" ..
    finally show ?thesis .
  next
    case 2
    with xz' G1_rep have "(x, z) \<in> graph H1 h1" by blast
    then have "z = h1 x" ..
    also
    from xy' G1_rep have "(x, y) \<in> graph H1 h1" by (simp only:)
    then have "y = h1 x" ..
    finally show ?thesis ..
  qed
qed

text \<open>
  \<^medskip>
  The limit function \<open>h\<close> is linear. Every element \<open>x\<close> in the domain of \<open>h\<close> is
  in the domain of a function \<open>h'\<close> in the chain of norm preserving extensions.
  Furthermore, \<open>h\<close> is an extension of \<open>h'\<close> so the function values of \<open>x\<close> are
  identical for \<open>h'\<close> and \<open>h\<close>. Finally, the function \<open>h'\<close> is linear by
  construction of \<open>M\<close>.
\<close>

lemma sup_lf:
  assumes M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chains M"
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

text \<open>
  \<^medskip>
  The limit of a non-empty chain of norm preserving extensions of \<open>f\<close> is an
  extension of \<open>f\<close>, since every element of the chain is an extension of \<open>f\<close>
  and the supremum is an extension for every element of the chain.
\<close>

lemma sup_ext:
  assumes graph: "graph H h = \<Union>c"
    and M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chains M"
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

text \<open>
  \<^medskip>
  The domain \<open>H\<close> of the limit function is a superspace of \<open>F\<close>, since \<open>F\<close> is a
  subset of \<open>H\<close>. The existence of the \<open>0\<close> element in \<open>F\<close> and the closure
  properties follow from the fact that \<open>F\<close> is a vector space.
\<close>

lemma sup_supF:
  assumes graph: "graph H h = \<Union>c"
    and M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chains M"
    and ex: "\<exists>x. x \<in> c"
    and FE: "F \<unlhd> E"
  shows "F \<unlhd> H"
proof
  from FE show "F \<noteq> {}" by (rule subspace.non_empty)
  from graph M cM ex have "graph F f \<subseteq> graph H h" by (rule sup_ext)
  then show "F \<subseteq> H" ..
  show "x + y \<in> F" if "x \<in> F" and "y \<in> F" for x y
    using FE that by (rule subspace.add_closed)
  show "a \<cdot> x \<in> F" if "x \<in> F" for x a
    using FE that by (rule subspace.mult_closed)
qed

text \<open>
  \<^medskip>
  The domain \<open>H\<close> of the limit function is a subspace of \<open>E\<close>.
\<close>

lemma sup_subE:
  assumes graph: "graph H h = \<Union>c"
    and M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chains M"
    and ex: "\<exists>x. x \<in> c"
    and FE: "F \<unlhd> E"
    and E: "vectorspace E"
  shows "H \<unlhd> E"
proof
  show "H \<noteq> {}"
  proof -
    from FE E have "0 \<in> F" by (rule subspace.zero)
    also from graph M cM ex FE have "F \<unlhd> H" by (rule sup_supF)
    then have "F \<subseteq> H" ..
    finally show ?thesis by blast
  qed
  show "H \<subseteq> E"
  proof
    fix x assume "x \<in> H"
    with M cM graph
    obtain H' where x: "x \<in> H'" and H'E: "H' \<unlhd> E"
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

text \<open>
  \<^medskip>
  The limit function is bounded by the norm \<open>p\<close> as well, since all elements in
  the chain are bounded by \<open>p\<close>.
\<close>

lemma sup_norm_pres:
  assumes graph: "graph H h = \<Union>c"
    and M: "M = norm_pres_extensions E p F f"
    and cM: "c \<in> chains M"
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

text \<open>
  \<^medskip>
  The following lemma is a property of linear forms on real vector spaces. It
  will be used for the lemma \<open>abs_Hahn_Banach\<close> (see page
  \pageref{abs-Hahn-Banach}). \label{abs-ineq-iff} For real vector spaces the
  following inequality are equivalent:
  \begin{center}
  \begin{tabular}{lll}
  \<open>\<forall>x \<in> H. \<bar>h x\<bar> \<le> p x\<close> & and &
  \<open>\<forall>x \<in> H. h x \<le> p x\<close> \\
  \end{tabular}
  \end{center}
\<close>

lemma abs_ineq_iff:
  assumes "subspace H E" and "vectorspace E" and "seminorm E p"
    and "linearform H h"
  shows "(\<forall>x \<in> H. \<bar>h x\<bar> \<le> p x) = (\<forall>x \<in> H. h x \<le> p x)" (is "?L = ?R")
proof
  interpret subspace H E by fact
  interpret vectorspace E by fact
  interpret seminorm E p by fact
  interpret linearform H h by fact
  have H: "vectorspace H" using \<open>vectorspace E\<close> ..
  show ?R if l: ?L
  proof
    fix x assume x: "x \<in> H"
    have "h x \<le> \<bar>h x\<bar>" by arith
    also from l x have "\<dots> \<le> p x" ..
    finally show "h x \<le> p x" .
  qed
  show ?L if r: ?R
  proof
    fix x assume x: "x \<in> H"
    show "\<bar>b\<bar> \<le> a" when "- a \<le> b" "b \<le> a" for a b :: real
      using that by arith
    from \<open>linearform H h\<close> and H x
    have "- h x = h (- x)" by (rule linearform.neg [symmetric])
    also
    from H x have "- x \<in> H" by (rule vectorspace.neg_closed)
    with r have "h (- x) \<le> p (- x)" ..
    also have "\<dots> = p x"
      using \<open>seminorm E p\<close> \<open>vectorspace E\<close>
    proof (rule seminorm.minus)
      from x show "x \<in> E" ..
    qed
    finally have "- h x \<le> p x" .
    then show "- p x \<le> h x" by simp
    from r x show "h x \<le> p x" ..
  qed
qed

end
