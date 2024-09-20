(*  Title:      HOL/Lattice/CompleteLattice.thy
    Author:     Markus Wenzel, TU Muenchen
*)

section \<open>Complete lattices\<close>

theory CompleteLattice imports Lattice begin

subsection \<open>Complete lattice operations\<close>

text \<open>
  A \emph{complete lattice} is a partial order with general
  (infinitary) infimum of any set of elements.  General supremum
  exists as well, as a consequence of the connection of infinitary
  bounds (see \S\ref{sec:connect-bounds}).
\<close>

class complete_lattice =
  assumes ex_Inf: "\<exists>inf. is_Inf A inf"

theorem ex_Sup: "\<exists>sup::'a::complete_lattice. is_Sup A sup"
proof -
  from ex_Inf obtain sup where "is_Inf {b. \<forall>a\<in>A. a \<sqsubseteq> b} sup" by blast
  then have "is_Sup A sup" by (rule Inf_Sup)
  then show ?thesis ..
qed

text \<open>
  The general \<open>\<Sqinter>\<close> (meet) and \<open>\<Squnion>\<close> (join) operations select
  such infimum and supremum elements.
\<close>

definition
  Meet :: "'a::complete_lattice set \<Rightarrow> 'a"  (\<open>\<Sqinter>_\<close> [90] 90) where
  "\<Sqinter>A = (THE inf. is_Inf A inf)"
definition
  Join :: "'a::complete_lattice set \<Rightarrow> 'a"  (\<open>\<Squnion>_\<close> [90] 90) where
  "\<Squnion>A = (THE sup. is_Sup A sup)"

text \<open>
  Due to unique existence of bounds, the complete lattice operations
  may be exhibited as follows.
\<close>

lemma Meet_equality [elim?]: "is_Inf A inf \<Longrightarrow> \<Sqinter>A = inf"
proof (unfold Meet_def)
  assume "is_Inf A inf"
  then show "(THE inf. is_Inf A inf) = inf"
    by (rule the_equality) (rule is_Inf_uniq [OF _ \<open>is_Inf A inf\<close>])
qed

lemma MeetI [intro?]:
  "(\<And>a. a \<in> A \<Longrightarrow> inf \<sqsubseteq> a) \<Longrightarrow>
    (\<And>b. \<forall>a \<in> A. b \<sqsubseteq> a \<Longrightarrow> b \<sqsubseteq> inf) \<Longrightarrow>
    \<Sqinter>A = inf"
  by (rule Meet_equality, rule is_InfI) blast+

lemma Join_equality [elim?]: "is_Sup A sup \<Longrightarrow> \<Squnion>A = sup"
proof (unfold Join_def)
  assume "is_Sup A sup"
  then show "(THE sup. is_Sup A sup) = sup"
    by (rule the_equality) (rule is_Sup_uniq [OF _ \<open>is_Sup A sup\<close>])
qed

lemma JoinI [intro?]:
  "(\<And>a. a \<in> A \<Longrightarrow> a \<sqsubseteq> sup) \<Longrightarrow>
    (\<And>b. \<forall>a \<in> A. a \<sqsubseteq> b \<Longrightarrow> sup \<sqsubseteq> b) \<Longrightarrow>
    \<Squnion>A = sup"
  by (rule Join_equality, rule is_SupI) blast+


text \<open>
  \medskip The \<open>\<Sqinter>\<close> and \<open>\<Squnion>\<close> operations indeed determine
  bounds on a complete lattice structure.
\<close>

lemma is_Inf_Meet [intro?]: "is_Inf A (\<Sqinter>A)"
proof (unfold Meet_def)
  from ex_Inf obtain inf where "is_Inf A inf" ..
  then show "is_Inf A (THE inf. is_Inf A inf)"
    by (rule theI) (rule is_Inf_uniq [OF _ \<open>is_Inf A inf\<close>])
qed

lemma Meet_greatest [intro?]: "(\<And>a. a \<in> A \<Longrightarrow> x \<sqsubseteq> a) \<Longrightarrow> x \<sqsubseteq> \<Sqinter>A"
  by (rule is_Inf_greatest, rule is_Inf_Meet) blast

lemma Meet_lower [intro?]: "a \<in> A \<Longrightarrow> \<Sqinter>A \<sqsubseteq> a"
  by (rule is_Inf_lower) (rule is_Inf_Meet)


lemma is_Sup_Join [intro?]: "is_Sup A (\<Squnion>A)"
proof (unfold Join_def)
  from ex_Sup obtain sup where "is_Sup A sup" ..
  then show "is_Sup A (THE sup. is_Sup A sup)"
    by (rule theI) (rule is_Sup_uniq [OF _ \<open>is_Sup A sup\<close>])
qed

lemma Join_least [intro?]: "(\<And>a. a \<in> A \<Longrightarrow> a \<sqsubseteq> x) \<Longrightarrow> \<Squnion>A \<sqsubseteq> x"
  by (rule is_Sup_least, rule is_Sup_Join) blast
lemma Join_lower [intro?]: "a \<in> A \<Longrightarrow> a \<sqsubseteq> \<Squnion>A"
  by (rule is_Sup_upper) (rule is_Sup_Join)


subsection \<open>The Knaster-Tarski Theorem\<close>

text \<open>
  The Knaster-Tarski Theorem (in its simplest formulation) states that
  any monotone function on a complete lattice has a least fixed-point
  (see \<^cite>\<open>\<open>pages 93--94\<close> in "Davey-Priestley:1990"\<close> for example).  This
  is a consequence of the basic boundary properties of the complete
  lattice operations.
\<close>

theorem Knaster_Tarski:
  assumes mono: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  obtains a :: "'a::complete_lattice" where
    "f a = a" and "\<And>a'. f a' = a' \<Longrightarrow> a \<sqsubseteq> a'"
proof
  let ?H = "{u. f u \<sqsubseteq> u}"
  let ?a = "\<Sqinter>?H"
  show "f ?a = ?a"
  proof -
    have ge: "f ?a \<sqsubseteq> ?a"
    proof
      fix x assume x: "x \<in> ?H"
      then have "?a \<sqsubseteq> x" ..
      then have "f ?a \<sqsubseteq> f x" by (rule mono)
      also from x have "... \<sqsubseteq> x" ..
      finally show "f ?a \<sqsubseteq> x" .
    qed
    also have "?a \<sqsubseteq> f ?a"
    proof
      from ge have "f (f ?a) \<sqsubseteq> f ?a" by (rule mono)
      then show "f ?a \<in> ?H" ..
    qed
    finally show ?thesis .
  qed

  fix a'
  assume "f a' = a'"
  then have "f a' \<sqsubseteq> a'" by (simp only: leq_refl)
  then have "a' \<in> ?H" ..
  then show "?a \<sqsubseteq> a'" ..
qed

theorem Knaster_Tarski_dual:
  assumes mono: "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  obtains a :: "'a::complete_lattice" where
    "f a = a" and "\<And>a'. f a' = a' \<Longrightarrow> a' \<sqsubseteq> a"
proof
  let ?H = "{u. u \<sqsubseteq> f u}"
  let ?a = "\<Squnion>?H"
  show "f ?a = ?a"
  proof -
    have le: "?a \<sqsubseteq> f ?a"
    proof
      fix x assume x: "x \<in> ?H"
      then have "x \<sqsubseteq> f x" ..
      also from x have "x \<sqsubseteq> ?a" ..
      then have "f x \<sqsubseteq> f ?a" by (rule mono)
      finally show "x \<sqsubseteq> f ?a" .
    qed
    have "f ?a \<sqsubseteq> ?a"
    proof
      from le have "f ?a \<sqsubseteq> f (f ?a)" by (rule mono)
      then show "f ?a \<in> ?H" ..
    qed
    from this and le show ?thesis by (rule leq_antisym)
  qed

  fix a'
  assume "f a' = a'"
  then have "a' \<sqsubseteq> f a'" by (simp only: leq_refl)
  then have "a' \<in> ?H" ..
  then show "a' \<sqsubseteq> ?a" ..
qed


subsection \<open>Bottom and top elements\<close>

text \<open>
  With general bounds available, complete lattices also have least and
  greatest elements.
\<close>

definition
  bottom :: "'a::complete_lattice"  (\<open>\<bottom>\<close>) where
  "\<bottom> = \<Sqinter>UNIV"

definition
  top :: "'a::complete_lattice"  (\<open>\<top>\<close>) where
  "\<top> = \<Squnion>UNIV"

lemma bottom_least [intro?]: "\<bottom> \<sqsubseteq> x"
proof (unfold bottom_def)
  have "x \<in> UNIV" ..
  then show "\<Sqinter>UNIV \<sqsubseteq> x" ..
qed

lemma bottomI [intro?]: "(\<And>a. x \<sqsubseteq> a) \<Longrightarrow> \<bottom> = x"
proof (unfold bottom_def)
  assume "\<And>a. x \<sqsubseteq> a"
  show "\<Sqinter>UNIV = x"
  proof
    fix a show "x \<sqsubseteq> a" by fact
  next
    fix b :: "'a::complete_lattice"
    assume b: "\<forall>a \<in> UNIV. b \<sqsubseteq> a"
    have "x \<in> UNIV" ..
    with b show "b \<sqsubseteq> x" ..
  qed
qed

lemma top_greatest [intro?]: "x \<sqsubseteq> \<top>"
proof (unfold top_def)
  have "x \<in> UNIV" ..
  then show "x \<sqsubseteq> \<Squnion>UNIV" ..
qed

lemma topI [intro?]: "(\<And>a. a \<sqsubseteq> x) \<Longrightarrow> \<top> = x"
proof (unfold top_def)
  assume "\<And>a. a \<sqsubseteq> x"
  show "\<Squnion>UNIV = x"
  proof
    fix a show "a \<sqsubseteq> x" by fact
  next
    fix b :: "'a::complete_lattice"
    assume b: "\<forall>a \<in> UNIV. a \<sqsubseteq> b"
    have "x \<in> UNIV" ..
    with b show "x \<sqsubseteq> b" ..
  qed
qed


subsection \<open>Duality\<close>

text \<open>
  The class of complete lattices is closed under formation of dual
  structures.
\<close>

instance dual :: (complete_lattice) complete_lattice
proof
  fix A' :: "'a::complete_lattice dual set"
  show "\<exists>inf'. is_Inf A' inf'"
  proof -
    have "\<exists>sup. is_Sup (undual ` A') sup" by (rule ex_Sup)
    then have "\<exists>sup. is_Inf (dual ` undual ` A') (dual sup)" by (simp only: dual_Inf)
    then show ?thesis by (simp add: dual_ex [symmetric] image_comp)
  qed
qed

text \<open>
  Apparently, the \<open>\<Sqinter>\<close> and \<open>\<Squnion>\<close> operations are dual to each
  other.
\<close>

theorem dual_Meet [intro?]: "dual (\<Sqinter>A) = \<Squnion>(dual ` A)"
proof -
  from is_Inf_Meet have "is_Sup (dual ` A) (dual (\<Sqinter>A))" ..
  then have "\<Squnion>(dual ` A) = dual (\<Sqinter>A)" ..
  then show ?thesis ..
qed

theorem dual_Join [intro?]: "dual (\<Squnion>A) = \<Sqinter>(dual ` A)"
proof -
  from is_Sup_Join have "is_Inf (dual ` A) (dual (\<Squnion>A))" ..
  then have "\<Sqinter>(dual ` A) = dual (\<Squnion>A)" ..
  then show ?thesis ..
qed

text \<open>
  Likewise are \<open>\<bottom>\<close> and \<open>\<top>\<close> duals of each other.
\<close>

theorem dual_bottom [intro?]: "dual \<bottom> = \<top>"
proof -
  have "\<top> = dual \<bottom>"
  proof
    fix a' have "\<bottom> \<sqsubseteq> undual a'" ..
    then have "dual (undual a') \<sqsubseteq> dual \<bottom>" ..
    then show "a' \<sqsubseteq> dual \<bottom>" by simp
  qed
  then show ?thesis ..
qed

theorem dual_top [intro?]: "dual \<top> = \<bottom>"
proof -
  have "\<bottom> = dual \<top>"
  proof
    fix a' have "undual a' \<sqsubseteq> \<top>" ..
    then have "dual \<top> \<sqsubseteq> dual (undual a')" ..
    then show "dual \<top> \<sqsubseteq> a'" by simp
  qed
  then show ?thesis ..
qed


subsection \<open>Complete lattices are lattices\<close>

text \<open>
  Complete lattices (with general bounds available) are indeed plain
  lattices as well.  This holds due to the connection of general
  versus binary bounds that has been formally established in
  \S\ref{sec:gen-bin-bounds}.
\<close>

lemma is_inf_binary: "is_inf x y (\<Sqinter>{x, y})"
proof -
  have "is_Inf {x, y} (\<Sqinter>{x, y})" ..
  then show ?thesis by (simp only: is_Inf_binary)
qed

lemma is_sup_binary: "is_sup x y (\<Squnion>{x, y})"
proof -
  have "is_Sup {x, y} (\<Squnion>{x, y})" ..
  then show ?thesis by (simp only: is_Sup_binary)
qed

instance complete_lattice \<subseteq> lattice
proof
  fix x y :: "'a::complete_lattice"
  from is_inf_binary show "\<exists>inf. is_inf x y inf" ..
  from is_sup_binary show "\<exists>sup. is_sup x y sup" ..
qed

theorem meet_binary: "x \<sqinter> y = \<Sqinter>{x, y}"
  by (rule meet_equality) (rule is_inf_binary)

theorem join_binary: "x \<squnion> y = \<Squnion>{x, y}"
  by (rule join_equality) (rule is_sup_binary)


subsection \<open>Complete lattices and set-theory operations\<close>

text \<open>
  The complete lattice operations are (anti) monotone wrt.\ set
  inclusion.
\<close>

theorem Meet_subset_antimono: "A \<subseteq> B \<Longrightarrow> \<Sqinter>B \<sqsubseteq> \<Sqinter>A"
proof (rule Meet_greatest)
  fix a assume "a \<in> A"
  also assume "A \<subseteq> B"
  finally have "a \<in> B" .
  then show "\<Sqinter>B \<sqsubseteq> a" ..
qed

theorem Join_subset_mono: "A \<subseteq> B \<Longrightarrow> \<Squnion>A \<sqsubseteq> \<Squnion>B"
proof -
  assume "A \<subseteq> B"
  then have "dual ` A \<subseteq> dual ` B" by blast
  then have "\<Sqinter>(dual ` B) \<sqsubseteq> \<Sqinter>(dual ` A)" by (rule Meet_subset_antimono)
  then have "dual (\<Squnion>B) \<sqsubseteq> dual (\<Squnion>A)" by (simp only: dual_Join)
  then show ?thesis by (simp only: dual_leq)
qed

text \<open>
  Bounds over unions of sets may be obtained separately.
\<close>

theorem Meet_Un: "\<Sqinter>(A \<union> B) = \<Sqinter>A \<sqinter> \<Sqinter>B"
proof
  fix a assume "a \<in> A \<union> B"
  then show "\<Sqinter>A \<sqinter> \<Sqinter>B \<sqsubseteq> a"
  proof
    assume a: "a \<in> A"
    have "\<Sqinter>A \<sqinter> \<Sqinter>B \<sqsubseteq> \<Sqinter>A" ..
    also from a have "\<dots> \<sqsubseteq> a" ..
    finally show ?thesis .
  next
    assume a: "a \<in> B"
    have "\<Sqinter>A \<sqinter> \<Sqinter>B \<sqsubseteq> \<Sqinter>B" ..
    also from a have "\<dots> \<sqsubseteq> a" ..
    finally show ?thesis .
  qed
next
  fix b assume b: "\<forall>a \<in> A \<union> B. b \<sqsubseteq> a"
  show "b \<sqsubseteq> \<Sqinter>A \<sqinter> \<Sqinter>B"
  proof
    show "b \<sqsubseteq> \<Sqinter>A"
    proof
      fix a assume "a \<in> A"
      then have "a \<in>  A \<union> B" ..
      with b show "b \<sqsubseteq> a" ..
    qed
    show "b \<sqsubseteq> \<Sqinter>B"
    proof
      fix a assume "a \<in> B"
      then have "a \<in>  A \<union> B" ..
      with b show "b \<sqsubseteq> a" ..
    qed
  qed
qed

theorem Join_Un: "\<Squnion>(A \<union> B) = \<Squnion>A \<squnion> \<Squnion>B"
proof -
  have "dual (\<Squnion>(A \<union> B)) = \<Sqinter>(dual ` A \<union> dual ` B)"
    by (simp only: dual_Join image_Un)
  also have "\<dots> = \<Sqinter>(dual ` A) \<sqinter> \<Sqinter>(dual ` B)"
    by (rule Meet_Un)
  also have "\<dots> = dual (\<Squnion>A \<squnion> \<Squnion>B)"
    by (simp only: dual_join dual_Join)
  finally show ?thesis ..
qed

text \<open>
  Bounds over singleton sets are trivial.
\<close>

theorem Meet_singleton: "\<Sqinter>{x} = x"
proof
  fix a assume "a \<in> {x}"
  then have "a = x" by simp
  then show "x \<sqsubseteq> a" by (simp only: leq_refl)
next
  fix b assume "\<forall>a \<in> {x}. b \<sqsubseteq> a"
  then show "b \<sqsubseteq> x" by simp
qed

theorem Join_singleton: "\<Squnion>{x} = x"
proof -
  have "dual (\<Squnion>{x}) = \<Sqinter>{dual x}" by (simp add: dual_Join)
  also have "\<dots> = dual x" by (rule Meet_singleton)
  finally show ?thesis ..
qed

text \<open>
  Bounds over the empty and universal set correspond to each other.
\<close>

theorem Meet_empty: "\<Sqinter>{} = \<Squnion>UNIV"
proof
  fix a :: "'a::complete_lattice"
  assume "a \<in> {}"
  then have False by simp
  then show "\<Squnion>UNIV \<sqsubseteq> a" ..
next
  fix b :: "'a::complete_lattice"
  have "b \<in> UNIV" ..
  then show "b \<sqsubseteq> \<Squnion>UNIV" ..
qed

theorem Join_empty: "\<Squnion>{} = \<Sqinter>UNIV"
proof -
  have "dual (\<Squnion>{}) = \<Sqinter>{}" by (simp add: dual_Join)
  also have "\<dots> = \<Squnion>UNIV" by (rule Meet_empty)
  also have "\<dots> = dual (\<Sqinter>UNIV)" by (simp add: dual_Meet)
  finally show ?thesis ..
qed

end
