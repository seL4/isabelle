(*  Title:      HOL/Lattice/Lattice.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Lattices\<close>

theory Lattice imports Bounds begin

subsection \<open>Lattice operations\<close>

text \<open>
  A \emph{lattice} is a partial order with infimum and supremum of any
  two elements (thus any \emph{finite} number of elements have bounds
  as well).
\<close>

class lattice =
  assumes ex_inf: "\<exists>inf. is_inf x y inf"
  assumes ex_sup: "\<exists>sup. is_sup x y sup"

text \<open>
  The \<open>\<sqinter>\<close> (meet) and \<open>\<squnion>\<close> (join) operations select such
  infimum and supremum elements.
\<close>

definition
  meet :: "'a::lattice \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>\<sqinter>\<close> 70) where
  "x \<sqinter> y = (THE inf. is_inf x y inf)"
definition
  join :: "'a::lattice \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl \<open>\<squnion>\<close> 65) where
  "x \<squnion> y = (THE sup. is_sup x y sup)"

text \<open>
  Due to unique existence of bounds, the lattice operations may be
  exhibited as follows.
\<close>

lemma meet_equality [elim?]: "is_inf x y inf \<Longrightarrow> x \<sqinter> y = inf"
proof (unfold meet_def)
  assume "is_inf x y inf"
  then show "(THE inf. is_inf x y inf) = inf"
    by (rule the_equality) (rule is_inf_uniq [OF _ \<open>is_inf x y inf\<close>])
qed

lemma meetI [intro?]:
    "inf \<sqsubseteq> x \<Longrightarrow> inf \<sqsubseteq> y \<Longrightarrow> (\<And>z. z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> inf) \<Longrightarrow> x \<sqinter> y = inf"
  by (rule meet_equality, rule is_infI) blast+

lemma join_equality [elim?]: "is_sup x y sup \<Longrightarrow> x \<squnion> y = sup"
proof (unfold join_def)
  assume "is_sup x y sup"
  then show "(THE sup. is_sup x y sup) = sup"
    by (rule the_equality) (rule is_sup_uniq [OF _ \<open>is_sup x y sup\<close>])
qed

lemma joinI [intro?]: "x \<sqsubseteq> sup \<Longrightarrow> y \<sqsubseteq> sup \<Longrightarrow>
    (\<And>z. x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> sup \<sqsubseteq> z) \<Longrightarrow> x \<squnion> y = sup"
  by (rule join_equality, rule is_supI) blast+


text \<open>
  \medskip The \<open>\<sqinter>\<close> and \<open>\<squnion>\<close> operations indeed determine
  bounds on a lattice structure.
\<close>

lemma is_inf_meet [intro?]: "is_inf x y (x \<sqinter> y)"
proof (unfold meet_def)
  from ex_inf obtain inf where "is_inf x y inf" ..
  then show "is_inf x y (THE inf. is_inf x y inf)"
    by (rule theI) (rule is_inf_uniq [OF _ \<open>is_inf x y inf\<close>])
qed

lemma meet_greatest [intro?]: "z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> x \<sqinter> y"
  by (rule is_inf_greatest) (rule is_inf_meet)

lemma meet_lower1 [intro?]: "x \<sqinter> y \<sqsubseteq> x"
  by (rule is_inf_lower) (rule is_inf_meet)

lemma meet_lower2 [intro?]: "x \<sqinter> y \<sqsubseteq> y"
  by (rule is_inf_lower) (rule is_inf_meet)


lemma is_sup_join [intro?]: "is_sup x y (x \<squnion> y)"
proof (unfold join_def)
  from ex_sup obtain sup where "is_sup x y sup" ..
  then show "is_sup x y (THE sup. is_sup x y sup)"
    by (rule theI) (rule is_sup_uniq [OF _ \<open>is_sup x y sup\<close>])
qed

lemma join_least [intro?]: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<squnion> y \<sqsubseteq> z"
  by (rule is_sup_least) (rule is_sup_join)

lemma join_upper1 [intro?]: "x \<sqsubseteq> x \<squnion> y"
  by (rule is_sup_upper) (rule is_sup_join)

lemma join_upper2 [intro?]: "y \<sqsubseteq> x \<squnion> y"
  by (rule is_sup_upper) (rule is_sup_join)


subsection \<open>Duality\<close>

text \<open>
  The class of lattices is closed under formation of dual structures.
  This means that for any theorem of lattice theory, the dualized
  statement holds as well; this important fact simplifies many proofs
  of lattice theory.
\<close>

instance dual :: (lattice) lattice
proof
  fix x' y' :: "'a::lattice dual"
  show "\<exists>inf'. is_inf x' y' inf'"
  proof -
    have "\<exists>sup. is_sup (undual x') (undual y') sup" by (rule ex_sup)
    then have "\<exists>sup. is_inf (dual (undual x')) (dual (undual y')) (dual sup)"
      by (simp only: dual_inf)
    then show ?thesis by (simp add: dual_ex [symmetric])
  qed
  show "\<exists>sup'. is_sup x' y' sup'"
  proof -
    have "\<exists>inf. is_inf (undual x') (undual y') inf" by (rule ex_inf)
    then have "\<exists>inf. is_sup (dual (undual x')) (dual (undual y')) (dual inf)"
      by (simp only: dual_sup)
    then show ?thesis by (simp add: dual_ex [symmetric])
  qed
qed

text \<open>
  Apparently, the \<open>\<sqinter>\<close> and \<open>\<squnion>\<close> operations are dual to each
  other.
\<close>

theorem dual_meet [intro?]: "dual (x \<sqinter> y) = dual x \<squnion> dual y"
proof -
  from is_inf_meet have "is_sup (dual x) (dual y) (dual (x \<sqinter> y))" ..
  then have "dual x \<squnion> dual y = dual (x \<sqinter> y)" ..
  then show ?thesis ..
qed

theorem dual_join [intro?]: "dual (x \<squnion> y) = dual x \<sqinter> dual y"
proof -
  from is_sup_join have "is_inf (dual x) (dual y) (dual (x \<squnion> y))" ..
  then have "dual x \<sqinter> dual y = dual (x \<squnion> y)" ..
  then show ?thesis ..
qed


subsection \<open>Algebraic properties \label{sec:lattice-algebra}\<close>

text \<open>
  The \<open>\<sqinter>\<close> and \<open>\<squnion>\<close> operations have the following
  characteristic algebraic properties: associative (A), commutative
  (C), and absorptive (AB).
\<close>

theorem meet_assoc: "(x \<sqinter> y) \<sqinter> z = x \<sqinter> (y \<sqinter> z)"
proof
  show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> x \<sqinter> y"
  proof
    show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> x" ..
    show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> y"
    proof -
      have "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> y \<sqinter> z" ..
      also have "\<dots> \<sqsubseteq> y" ..
      finally show ?thesis .
    qed
  qed
  show "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> z"
  proof -
    have "x \<sqinter> (y \<sqinter> z) \<sqsubseteq> y \<sqinter> z" ..
    also have "\<dots> \<sqsubseteq> z" ..
    finally show ?thesis .
  qed
  fix w assume "w \<sqsubseteq> x \<sqinter> y" and "w \<sqsubseteq> z"
  show "w \<sqsubseteq> x \<sqinter> (y \<sqinter> z)"
  proof
    show "w \<sqsubseteq> x"
    proof -
      have "w \<sqsubseteq> x \<sqinter> y" by fact
      also have "\<dots> \<sqsubseteq> x" ..
      finally show ?thesis .
    qed
    show "w \<sqsubseteq> y \<sqinter> z"
    proof
      show "w \<sqsubseteq> y"
      proof -
        have "w \<sqsubseteq> x \<sqinter> y" by fact
        also have "\<dots> \<sqsubseteq> y" ..
        finally show ?thesis .
      qed
      show "w \<sqsubseteq> z" by fact
    qed
  qed
qed

theorem join_assoc: "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
proof -
  have "dual ((x \<squnion> y) \<squnion> z) = (dual x \<sqinter> dual y) \<sqinter> dual z"
    by (simp only: dual_join)
  also have "\<dots> = dual x \<sqinter> (dual y \<sqinter> dual z)"
    by (rule meet_assoc)
  also have "\<dots> = dual (x \<squnion> (y \<squnion> z))"
    by (simp only: dual_join)
  finally show ?thesis ..
qed

theorem meet_commute: "x \<sqinter> y = y \<sqinter> x"
proof
  show "y \<sqinter> x \<sqsubseteq> x" ..
  show "y \<sqinter> x \<sqsubseteq> y" ..
  fix z assume "z \<sqsubseteq> y" and "z \<sqsubseteq> x"
  then show "z \<sqsubseteq> y \<sqinter> x" ..
qed

theorem join_commute: "x \<squnion> y = y \<squnion> x"
proof -
  have "dual (x \<squnion> y) = dual x \<sqinter> dual y" ..
  also have "\<dots> = dual y \<sqinter> dual x"
    by (rule meet_commute)
  also have "\<dots> = dual (y \<squnion> x)"
    by (simp only: dual_join)
  finally show ?thesis ..
qed

theorem meet_join_absorb: "x \<sqinter> (x \<squnion> y) = x"
proof
  show "x \<sqsubseteq> x" ..
  show "x \<sqsubseteq> x \<squnion> y" ..
  fix z assume "z \<sqsubseteq> x" and "z \<sqsubseteq> x \<squnion> y"
  show "z \<sqsubseteq> x" by fact
qed

theorem join_meet_absorb: "x \<squnion> (x \<sqinter> y) = x"
proof -
  have "dual x \<sqinter> (dual x \<squnion> dual y) = dual x"
    by (rule meet_join_absorb)
  then have "dual (x \<squnion> (x \<sqinter> y)) = dual x"
    by (simp only: dual_meet dual_join)
  then show ?thesis ..
qed

text \<open>
  \medskip Some further algebraic properties hold as well.  The
  property idempotent (I) is a basic algebraic consequence of (AB).
\<close>

theorem meet_idem: "x \<sqinter> x = x"
proof -
  have "x \<sqinter> (x \<squnion> (x \<sqinter> x)) = x" by (rule meet_join_absorb)
  also have "x \<squnion> (x \<sqinter> x) = x" by (rule join_meet_absorb)
  finally show ?thesis .
qed

theorem join_idem: "x \<squnion> x = x"
proof -
  have "dual x \<sqinter> dual x = dual x"
    by (rule meet_idem)
  then have "dual (x \<squnion> x) = dual x"
    by (simp only: dual_join)
  then show ?thesis ..
qed

text \<open>
  Meet and join are trivial for related elements.
\<close>

theorem meet_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> x \<sqinter> y = x"
proof
  assume "x \<sqsubseteq> y"
  show "x \<sqsubseteq> x" ..
  show "x \<sqsubseteq> y" by fact
  fix z assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
  show "z \<sqsubseteq> x" by fact
qed

theorem join_related [elim?]: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
proof -
  assume "x \<sqsubseteq> y" then have "dual y \<sqsubseteq> dual x" ..
  then have "dual y \<sqinter> dual x = dual y" by (rule meet_related)
  also have "dual y \<sqinter> dual x = dual (y \<squnion> x)" by (simp only: dual_join)
  also have "y \<squnion> x = x \<squnion> y" by (rule join_commute)
  finally show ?thesis ..
qed


subsection \<open>Order versus algebraic structure\<close>

text \<open>
  The \<open>\<sqinter>\<close> and \<open>\<squnion>\<close> operations are connected with the
  underlying \<open>\<sqsubseteq>\<close> relation in a canonical manner.
\<close>

theorem meet_connection: "(x \<sqsubseteq> y) = (x \<sqinter> y = x)"
proof
  assume "x \<sqsubseteq> y"
  then have "is_inf x y x" ..
  then show "x \<sqinter> y = x" ..
next
  have "x \<sqinter> y \<sqsubseteq> y" ..
  also assume "x \<sqinter> y = x"
  finally show "x \<sqsubseteq> y" .
qed

theorem join_connection: "(x \<sqsubseteq> y) = (x \<squnion> y = y)"
proof
  assume "x \<sqsubseteq> y"
  then have "is_sup x y y" ..
  then show "x \<squnion> y = y" ..
next
  have "x \<sqsubseteq> x \<squnion> y" ..
  also assume "x \<squnion> y = y"
  finally show "x \<sqsubseteq> y" .
qed

text \<open>
  \medskip The most fundamental result of the meta-theory of lattices
  is as follows (we do not prove it here).

  Given a structure with binary operations \<open>\<sqinter>\<close> and \<open>\<squnion>\<close>
  such that (A), (C), and (AB) hold (cf.\
  \S\ref{sec:lattice-algebra}).  This structure represents a lattice,
  if the relation \<^term>\<open>x \<sqsubseteq> y\<close> is defined as \<^term>\<open>x \<sqinter> y = x\<close>
  (alternatively as \<^term>\<open>x \<squnion> y = y\<close>).  Furthermore, infimum and
  supremum with respect to this ordering coincide with the original
  \<open>\<sqinter>\<close> and \<open>\<squnion>\<close> operations.
\<close>


subsection \<open>Example instances\<close>

subsubsection \<open>Linear orders\<close>

text \<open>
  Linear orders with \<^term>\<open>minimum\<close> and \<^term>\<open>maximum\<close> operations
  are a (degenerate) example of lattice structures.
\<close>

definition
  minimum :: "'a::linear_order \<Rightarrow> 'a \<Rightarrow> 'a" where
  "minimum x y = (if x \<sqsubseteq> y then x else y)"
definition
  maximum :: "'a::linear_order \<Rightarrow> 'a \<Rightarrow> 'a" where
  "maximum x y = (if x \<sqsubseteq> y then y else x)"

lemma is_inf_minimum: "is_inf x y (minimum x y)"
proof
  let ?min = "minimum x y"
  from leq_linear show "?min \<sqsubseteq> x" by (auto simp add: minimum_def)
  from leq_linear show "?min \<sqsubseteq> y" by (auto simp add: minimum_def)
  fix z assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
  with leq_linear show "z \<sqsubseteq> ?min" by (auto simp add: minimum_def)
qed

lemma is_sup_maximum: "is_sup x y (maximum x y)"      (* FIXME dualize!? *)
proof
  let ?max = "maximum x y"
  from leq_linear show "x \<sqsubseteq> ?max" by (auto simp add: maximum_def)
  from leq_linear show "y \<sqsubseteq> ?max" by (auto simp add: maximum_def)
  fix z assume "x \<sqsubseteq> z" and "y \<sqsubseteq> z"
  with leq_linear show "?max \<sqsubseteq> z" by (auto simp add: maximum_def)
qed

instance linear_order \<subseteq> lattice
proof
  fix x y :: "'a::linear_order"
  from is_inf_minimum show "\<exists>inf. is_inf x y inf" ..
  from is_sup_maximum show "\<exists>sup. is_sup x y sup" ..
qed

text \<open>
  The lattice operations on linear orders indeed coincide with \<^term>\<open>minimum\<close> and \<^term>\<open>maximum\<close>.
\<close>

theorem meet_mimimum: "x \<sqinter> y = minimum x y"
  by (rule meet_equality) (rule is_inf_minimum)

theorem meet_maximum: "x \<squnion> y = maximum x y"
  by (rule join_equality) (rule is_sup_maximum)



subsubsection \<open>Binary products\<close>

text \<open>
  The class of lattices is closed under direct binary products (cf.\
  \S\ref{sec:prod-order}).
\<close>

lemma is_inf_prod: "is_inf p q (fst p \<sqinter> fst q, snd p \<sqinter> snd q)"
proof
  show "(fst p \<sqinter> fst q, snd p \<sqinter> snd q) \<sqsubseteq> p"
  proof -
    have "fst p \<sqinter> fst q \<sqsubseteq> fst p" ..
    moreover have "snd p \<sqinter> snd q \<sqsubseteq> snd p" ..
    ultimately show ?thesis by (simp add: leq_prod_def)
  qed
  show "(fst p \<sqinter> fst q, snd p \<sqinter> snd q) \<sqsubseteq> q"
  proof -
    have "fst p \<sqinter> fst q \<sqsubseteq> fst q" ..
    moreover have "snd p \<sqinter> snd q \<sqsubseteq> snd q" ..
    ultimately show ?thesis by (simp add: leq_prod_def)
  qed
  fix r assume rp: "r \<sqsubseteq> p" and rq: "r \<sqsubseteq> q"
  show "r \<sqsubseteq> (fst p \<sqinter> fst q, snd p \<sqinter> snd q)"
  proof -
    have "fst r \<sqsubseteq> fst p \<sqinter> fst q"
    proof
      from rp show "fst r \<sqsubseteq> fst p" by (simp add: leq_prod_def)
      from rq show "fst r \<sqsubseteq> fst q" by (simp add: leq_prod_def)
    qed
    moreover have "snd r \<sqsubseteq> snd p \<sqinter> snd q"
    proof
      from rp show "snd r \<sqsubseteq> snd p" by (simp add: leq_prod_def)
      from rq show "snd r \<sqsubseteq> snd q" by (simp add: leq_prod_def)
    qed
    ultimately show ?thesis by (simp add: leq_prod_def)
  qed
qed

lemma is_sup_prod: "is_sup p q (fst p \<squnion> fst q, snd p \<squnion> snd q)"  (* FIXME dualize!? *)
proof
  show "p \<sqsubseteq> (fst p \<squnion> fst q, snd p \<squnion> snd q)"
  proof -
    have "fst p \<sqsubseteq> fst p \<squnion> fst q" ..
    moreover have "snd p \<sqsubseteq> snd p \<squnion> snd q" ..
    ultimately show ?thesis by (simp add: leq_prod_def)
  qed
  show "q \<sqsubseteq> (fst p \<squnion> fst q, snd p \<squnion> snd q)"
  proof -
    have "fst q \<sqsubseteq> fst p \<squnion> fst q" ..
    moreover have "snd q \<sqsubseteq> snd p \<squnion> snd q" ..
    ultimately show ?thesis by (simp add: leq_prod_def)
  qed
  fix r assume "pr": "p \<sqsubseteq> r" and qr: "q \<sqsubseteq> r"
  show "(fst p \<squnion> fst q, snd p \<squnion> snd q) \<sqsubseteq> r"
  proof -
    have "fst p \<squnion> fst q \<sqsubseteq> fst r"
    proof
      from "pr" show "fst p \<sqsubseteq> fst r" by (simp add: leq_prod_def)
      from qr show "fst q \<sqsubseteq> fst r" by (simp add: leq_prod_def)
    qed
    moreover have "snd p \<squnion> snd q \<sqsubseteq> snd r"
    proof
      from "pr" show "snd p \<sqsubseteq> snd r" by (simp add: leq_prod_def)
      from qr show "snd q \<sqsubseteq> snd r" by (simp add: leq_prod_def)
    qed
    ultimately show ?thesis by (simp add: leq_prod_def)
  qed
qed

instance prod :: (lattice, lattice) lattice
proof
  fix p q :: "'a::lattice \<times> 'b::lattice"
  from is_inf_prod show "\<exists>inf. is_inf p q inf" ..
  from is_sup_prod show "\<exists>sup. is_sup p q sup" ..
qed

text \<open>
  The lattice operations on a binary product structure indeed coincide
  with the products of the original ones.
\<close>

theorem meet_prod: "p \<sqinter> q = (fst p \<sqinter> fst q, snd p \<sqinter> snd q)"
  by (rule meet_equality) (rule is_inf_prod)

theorem join_prod: "p \<squnion> q = (fst p \<squnion> fst q, snd p \<squnion> snd q)"
  by (rule join_equality) (rule is_sup_prod)


subsubsection \<open>General products\<close>

text \<open>
  The class of lattices is closed under general products (function
  spaces) as well (cf.\ \S\ref{sec:fun-order}).
\<close>

lemma is_inf_fun: "is_inf f g (\<lambda>x. f x \<sqinter> g x)"
proof
  show "(\<lambda>x. f x \<sqinter> g x) \<sqsubseteq> f"
  proof
    fix x show "f x \<sqinter> g x \<sqsubseteq> f x" ..
  qed
  show "(\<lambda>x. f x \<sqinter> g x) \<sqsubseteq> g"
  proof
    fix x show "f x \<sqinter> g x \<sqsubseteq> g x" ..
  qed
  fix h assume hf: "h \<sqsubseteq> f" and hg: "h \<sqsubseteq> g"
  show "h \<sqsubseteq> (\<lambda>x. f x \<sqinter> g x)"
  proof
    fix x
    show "h x \<sqsubseteq> f x \<sqinter> g x"
    proof
      from hf show "h x \<sqsubseteq> f x" ..
      from hg show "h x \<sqsubseteq> g x" ..
    qed
  qed
qed

lemma is_sup_fun: "is_sup f g (\<lambda>x. f x \<squnion> g x)"   (* FIXME dualize!? *)
proof
  show "f \<sqsubseteq> (\<lambda>x. f x \<squnion> g x)"
  proof
    fix x show "f x \<sqsubseteq> f x \<squnion> g x" ..
  qed
  show "g \<sqsubseteq> (\<lambda>x. f x \<squnion> g x)"
  proof
    fix x show "g x \<sqsubseteq> f x \<squnion> g x" ..
  qed
  fix h assume fh: "f \<sqsubseteq> h" and gh: "g \<sqsubseteq> h"
  show "(\<lambda>x. f x \<squnion> g x) \<sqsubseteq> h"
  proof
    fix x
    show "f x \<squnion> g x \<sqsubseteq> h x"
    proof
      from fh show "f x \<sqsubseteq> h x" ..
      from gh show "g x \<sqsubseteq> h x" ..
    qed
  qed
qed

instance "fun" :: (type, lattice) lattice
proof
  fix f g :: "'a \<Rightarrow> 'b::lattice"
  show "\<exists>inf. is_inf f g inf" by rule (rule is_inf_fun) (* FIXME @{text "from \<dots> show \<dots> .."} does not work!? unification incompleteness!? *)
  show "\<exists>sup. is_sup f g sup" by rule (rule is_sup_fun)
qed

text \<open>
  The lattice operations on a general product structure (function
  space) indeed emerge by point-wise lifting of the original ones.
\<close>

theorem meet_fun: "f \<sqinter> g = (\<lambda>x. f x \<sqinter> g x)"
  by (rule meet_equality) (rule is_inf_fun)

theorem join_fun: "f \<squnion> g = (\<lambda>x. f x \<squnion> g x)"
  by (rule join_equality) (rule is_sup_fun)


subsection \<open>Monotonicity and semi-morphisms\<close>

text \<open>
  The lattice operations are monotone in both argument positions.  In
  fact, monotonicity of the second position is trivial due to
  commutativity.
\<close>

theorem meet_mono: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> w \<Longrightarrow> x \<sqinter> y \<sqsubseteq> z \<sqinter> w"
proof -
  {
    fix a b c :: "'a::lattice"
    assume "a \<sqsubseteq> c" have "a \<sqinter> b \<sqsubseteq> c \<sqinter> b"
    proof
      have "a \<sqinter> b \<sqsubseteq> a" ..
      also have "\<dots> \<sqsubseteq> c" by fact
      finally show "a \<sqinter> b \<sqsubseteq> c" .
      show "a \<sqinter> b \<sqsubseteq> b" ..
    qed
  } note this [elim?]
  assume "x \<sqsubseteq> z" then have "x \<sqinter> y \<sqsubseteq> z \<sqinter> y" ..
  also have "\<dots> = y \<sqinter> z" by (rule meet_commute)
  also assume "y \<sqsubseteq> w" then have "y \<sqinter> z \<sqsubseteq> w \<sqinter> z" ..
  also have "\<dots> = z \<sqinter> w" by (rule meet_commute)
  finally show ?thesis .
qed

theorem join_mono: "x \<sqsubseteq> z \<Longrightarrow> y \<sqsubseteq> w \<Longrightarrow> x \<squnion> y \<sqsubseteq> z \<squnion> w"
proof -
  assume "x \<sqsubseteq> z" then have "dual z \<sqsubseteq> dual x" ..
  moreover assume "y \<sqsubseteq> w" then have "dual w \<sqsubseteq> dual y" ..
  ultimately have "dual z \<sqinter> dual w \<sqsubseteq> dual x \<sqinter> dual y"
    by (rule meet_mono)
  then have "dual (z \<squnion> w) \<sqsubseteq> dual (x \<squnion> y)"
    by (simp only: dual_join)
  then show ?thesis ..
qed

text \<open>
  \medskip A semi-morphisms is a function \<open>f\<close> that preserves the
  lattice operations in the following manner: \<^term>\<open>f (x \<sqinter> y) \<sqsubseteq> f x
  \<sqinter> f y\<close> and \<^term>\<open>f x \<squnion> f y \<sqsubseteq> f (x \<squnion> y)\<close>, respectively.  Any of
  these properties is equivalent with monotonicity.
\<close>

theorem meet_semimorph:
  "(\<And>x y. f (x \<sqinter> y) \<sqsubseteq> f x \<sqinter> f y) \<equiv> (\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y)"
proof
  assume morph: "\<And>x y. f (x \<sqinter> y) \<sqsubseteq> f x \<sqinter> f y"
  fix x y :: "'a::lattice"
  assume "x \<sqsubseteq> y"
  then have "x \<sqinter> y = x" ..
  then have "x = x \<sqinter> y" ..
  also have "f \<dots> \<sqsubseteq> f x \<sqinter> f y" by (rule morph)
  also have "\<dots> \<sqsubseteq> f y" ..
  finally show "f x \<sqsubseteq> f y" .
next
  assume mono: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  show "\<And>x y. f (x \<sqinter> y) \<sqsubseteq> f x \<sqinter> f y"
  proof -
    fix x y
    show "f (x \<sqinter> y) \<sqsubseteq> f x \<sqinter> f y"
    proof
      have "x \<sqinter> y \<sqsubseteq> x" .. then show "f (x \<sqinter> y) \<sqsubseteq> f x" by (rule mono)
      have "x \<sqinter> y \<sqsubseteq> y" .. then show "f (x \<sqinter> y) \<sqsubseteq> f y" by (rule mono)
    qed
  qed
qed

lemma join_semimorph:
  "(\<And>x y. f x \<squnion> f y \<sqsubseteq> f (x \<squnion> y)) \<equiv> (\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y)"
proof
  assume morph: "\<And>x y. f x \<squnion> f y \<sqsubseteq> f (x \<squnion> y)"
  fix x y :: "'a::lattice"
  assume "x \<sqsubseteq> y" then have "x \<squnion> y = y" ..
  have "f x \<sqsubseteq> f x \<squnion> f y" ..
  also have "\<dots> \<sqsubseteq> f (x \<squnion> y)" by (rule morph)
  also from \<open>x \<sqsubseteq> y\<close> have "x \<squnion> y = y" ..
  finally show "f x \<sqsubseteq> f y" .
next
  assume mono: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  show "\<And>x y. f x \<squnion> f y \<sqsubseteq> f (x \<squnion> y)"
  proof -
    fix x y
    show "f x \<squnion> f y \<sqsubseteq> f (x \<squnion> y)"
    proof
      have "x \<sqsubseteq> x \<squnion> y" .. then show "f x \<sqsubseteq> f (x \<squnion> y)" by (rule mono)
      have "y \<sqsubseteq> x \<squnion> y" .. then show "f y \<sqsubseteq> f (x \<squnion> y)" by (rule mono)
    qed
  qed
qed

end
