(*  Title:      HOL/Lattice/Orders.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Orders\<close>

theory Orders imports Main begin

subsection \<open>Ordered structures\<close>

text \<open>
  We define several classes of ordered structures over some type \<^typ>\<open>'a\<close> with relation \<open>\<sqsubseteq> :: 'a \<Rightarrow> 'a \<Rightarrow> bool\<close>.  For a
  \emph{quasi-order} that relation is required to be reflexive and
  transitive, for a \emph{partial order} it also has to be
  anti-symmetric, while for a \emph{linear order} all elements are
  required to be related (in either direction).
\<close>

class leq =
  fixes leq :: "'a \<Rightarrow> 'a \<Rightarrow> bool"  (infixl \<open>\<sqsubseteq>\<close> 50)

class quasi_order = leq +
  assumes leq_refl [intro?]: "x \<sqsubseteq> x"
  assumes leq_trans [trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z"

class partial_order = quasi_order +
  assumes leq_antisym [trans]: "x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y"

class linear_order = partial_order +
  assumes leq_linear: "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"

lemma linear_order_cases:
    "((x::'a::linear_order) \<sqsubseteq> y \<Longrightarrow> C) \<Longrightarrow> (y \<sqsubseteq> x \<Longrightarrow> C) \<Longrightarrow> C"
  by (insert leq_linear) blast


subsection \<open>Duality\<close>

text \<open>
  The \emph{dual} of an ordered structure is an isomorphic copy of the
  underlying type, with the \<open>\<sqsubseteq>\<close> relation defined as the inverse
  of the original one.
\<close>

datatype 'a dual = dual 'a

primrec undual :: "'a dual \<Rightarrow> 'a" where
  undual_dual: "undual (dual x) = x"

instantiation dual :: (leq) leq
begin

definition
  leq_dual_def: "x' \<sqsubseteq> y' \<equiv> undual y' \<sqsubseteq> undual x'"

instance ..

end

lemma undual_leq [iff?]: "(undual x' \<sqsubseteq> undual y') = (y' \<sqsubseteq> x')"
  by (simp add: leq_dual_def)

lemma dual_leq [iff?]: "(dual x \<sqsubseteq> dual y) = (y \<sqsubseteq> x)"
  by (simp add: leq_dual_def)

text \<open>
  \medskip Functions \<^term>\<open>dual\<close> and \<^term>\<open>undual\<close> are inverse to
  each other; this entails the following fundamental properties.
\<close>

lemma dual_undual [simp]: "dual (undual x') = x'"
  by (cases x') simp

lemma undual_dual_id [simp]: "undual o dual = id"
  by (rule ext) simp

lemma dual_undual_id [simp]: "dual o undual = id"
  by (rule ext) simp

text \<open>
  \medskip Since \<^term>\<open>dual\<close> (and \<^term>\<open>undual\<close>) are both injective
  and surjective, the basic logical connectives (equality,
  quantification etc.) are transferred as follows.
\<close>

lemma undual_equality [iff?]: "(undual x' = undual y') = (x' = y')"
  by (cases x', cases y') simp

lemma dual_equality [iff?]: "(dual x = dual y) = (x = y)"
  by simp

lemma dual_ball [iff?]: "(\<forall>x \<in> A. P (dual x)) = (\<forall>x' \<in> dual ` A. P x')"
proof
  assume a: "\<forall>x \<in> A. P (dual x)"
  show "\<forall>x' \<in> dual ` A. P x'"
  proof
    fix x' assume x': "x' \<in> dual ` A"
    have "undual x' \<in> A"
    proof -
      from x' have "undual x' \<in> undual ` dual ` A" by simp
      thus "undual x' \<in> A" by (simp add: image_comp)
    qed
    with a have "P (dual (undual x'))" ..
    also have "\<dots> = x'" by simp
    finally show "P x'" .
  qed
next
  assume a: "\<forall>x' \<in> dual ` A. P x'"
  show "\<forall>x \<in> A. P (dual x)"
  proof
    fix x assume "x \<in> A"
    hence "dual x \<in> dual ` A" by simp
    with a show "P (dual x)" ..
  qed
qed

lemma range_dual [simp]: "surj dual"
proof -
  have "\<And>x'. dual (undual x') = x'" by simp
  thus "surj dual" by (rule surjI)
qed

lemma dual_all [iff?]: "(\<forall>x. P (dual x)) = (\<forall>x'. P x')"
proof -
  have "(\<forall>x \<in> UNIV. P (dual x)) = (\<forall>x' \<in> dual ` UNIV. P x')"
    by (rule dual_ball)
  thus ?thesis by simp
qed

lemma dual_ex: "(\<exists>x. P (dual x)) = (\<exists>x'. P x')"
proof -
  have "(\<forall>x. \<not> P (dual x)) = (\<forall>x'. \<not> P x')"
    by (rule dual_all)
  thus ?thesis by blast
qed

lemma dual_Collect: "{dual x| x. P (dual x)} = {x'. P x'}"
proof -
  have "{dual x| x. P (dual x)} = {x'. \<exists>x''. x' = x'' \<and> P x''}"
    by (simp only: dual_ex [symmetric])
  thus ?thesis by blast
qed


subsection \<open>Transforming orders\<close>

subsubsection \<open>Duals\<close>

text \<open>
  The classes of quasi, partial, and linear orders are all closed
  under formation of dual structures.
\<close>

instance dual :: (quasi_order) quasi_order
proof
  fix x' y' z' :: "'a::quasi_order dual"
  have "undual x' \<sqsubseteq> undual x'" .. thus "x' \<sqsubseteq> x'" ..
  assume "y' \<sqsubseteq> z'" hence "undual z' \<sqsubseteq> undual y'" ..
  also assume "x' \<sqsubseteq> y'" hence "undual y' \<sqsubseteq> undual x'" ..
  finally show "x' \<sqsubseteq> z'" ..
qed

instance dual :: (partial_order) partial_order
proof
  fix x' y' :: "'a::partial_order dual"
  assume "y' \<sqsubseteq> x'" hence "undual x' \<sqsubseteq> undual y'" ..
  also assume "x' \<sqsubseteq> y'" hence "undual y' \<sqsubseteq> undual x'" ..
  finally show "x' = y'" ..
qed

instance dual :: (linear_order) linear_order
proof
  fix x' y' :: "'a::linear_order dual"
  show "x' \<sqsubseteq> y' \<or> y' \<sqsubseteq> x'"
  proof (rule linear_order_cases)
    assume "undual y' \<sqsubseteq> undual x'"
    hence "x' \<sqsubseteq> y'" .. thus ?thesis ..
  next
    assume "undual x' \<sqsubseteq> undual y'"
    hence "y' \<sqsubseteq> x'" .. thus ?thesis ..
  qed
qed


subsubsection \<open>Binary products \label{sec:prod-order}\<close>

text \<open>
  The classes of quasi and partial orders are closed under binary
  products.  Note that the direct product of linear orders need
  \emph{not} be linear in general.
\<close>

instantiation prod :: (leq, leq) leq
begin

definition
  leq_prod_def: "p \<sqsubseteq> q \<equiv> fst p \<sqsubseteq> fst q \<and> snd p \<sqsubseteq> snd q"

instance ..

end

lemma leq_prodI [intro?]:
    "fst p \<sqsubseteq> fst q \<Longrightarrow> snd p \<sqsubseteq> snd q \<Longrightarrow> p \<sqsubseteq> q"
  by (unfold leq_prod_def) blast

lemma leq_prodE [elim?]:
    "p \<sqsubseteq> q \<Longrightarrow> (fst p \<sqsubseteq> fst q \<Longrightarrow> snd p \<sqsubseteq> snd q \<Longrightarrow> C) \<Longrightarrow> C"
  by (unfold leq_prod_def) blast

instance prod :: (quasi_order, quasi_order) quasi_order
proof
  fix p q r :: "'a::quasi_order \<times> 'b::quasi_order"
  show "p \<sqsubseteq> p"
  proof
    show "fst p \<sqsubseteq> fst p" ..
    show "snd p \<sqsubseteq> snd p" ..
  qed
  assume pq: "p \<sqsubseteq> q" and qr: "q \<sqsubseteq> r"
  show "p \<sqsubseteq> r"
  proof
    from pq have "fst p \<sqsubseteq> fst q" ..
    also from qr have "\<dots> \<sqsubseteq> fst r" ..
    finally show "fst p \<sqsubseteq> fst r" .
    from pq have "snd p \<sqsubseteq> snd q" ..
    also from qr have "\<dots> \<sqsubseteq> snd r" ..
    finally show "snd p \<sqsubseteq> snd r" .
  qed
qed

instance prod :: (partial_order, partial_order) partial_order
proof
  fix p q :: "'a::partial_order \<times> 'b::partial_order"
  assume pq: "p \<sqsubseteq> q" and qp: "q \<sqsubseteq> p"
  show "p = q"
  proof
    from pq have "fst p \<sqsubseteq> fst q" ..
    also from qp have "\<dots> \<sqsubseteq> fst p" ..
    finally show "fst p = fst q" .
    from pq have "snd p \<sqsubseteq> snd q" ..
    also from qp have "\<dots> \<sqsubseteq> snd p" ..
    finally show "snd p = snd q" .
  qed
qed


subsubsection \<open>General products \label{sec:fun-order}\<close>

text \<open>
  The classes of quasi and partial orders are closed under general
  products (function spaces).  Note that the direct product of linear
  orders need \emph{not} be linear in general.
\<close>

instantiation "fun" :: (type, leq) leq
begin

definition
  leq_fun_def: "f \<sqsubseteq> g \<equiv> \<forall>x. f x \<sqsubseteq> g x"

instance ..

end

lemma leq_funI [intro?]: "(\<And>x. f x \<sqsubseteq> g x) \<Longrightarrow> f \<sqsubseteq> g"
  by (unfold leq_fun_def) blast

lemma leq_funD [dest?]: "f \<sqsubseteq> g \<Longrightarrow> f x \<sqsubseteq> g x"
  by (unfold leq_fun_def) blast

instance "fun" :: (type, quasi_order) quasi_order
proof
  fix f g h :: "'a \<Rightarrow> 'b::quasi_order"
  show "f \<sqsubseteq> f"
  proof
    fix x show "f x \<sqsubseteq> f x" ..
  qed
  assume fg: "f \<sqsubseteq> g" and gh: "g \<sqsubseteq> h"
  show "f \<sqsubseteq> h"
  proof
    fix x from fg have "f x \<sqsubseteq> g x" ..
    also from gh have "\<dots> \<sqsubseteq> h x" ..
    finally show "f x \<sqsubseteq> h x" .
  qed
qed

instance "fun" :: (type, partial_order) partial_order
proof
  fix f g :: "'a \<Rightarrow> 'b::partial_order"
  assume fg: "f \<sqsubseteq> g" and gf: "g \<sqsubseteq> f"
  show "f = g"
  proof
    fix x from fg have "f x \<sqsubseteq> g x" ..
    also from gf have "\<dots> \<sqsubseteq> f x" ..
    finally show "f x = g x" .
  qed
qed

end
