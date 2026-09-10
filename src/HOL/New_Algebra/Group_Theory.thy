(*
  Derived from the AFP entry Jacobson_Basic_Algebra, by Clemens Ballarin
*)

theory Group_Theory 
  imports Set_Theory 

begin

section \<open>Monoids and Groups\<close>

subsection \<open>Monoids of Transformations and Abstract Monoids\<close>

locale Monoid =
  fixes M and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
  assumes composition_closed [intro, simp]: "\<lbrakk> a \<in> M; b \<in> M \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> M"
    and unit_closed [intro, simp]: "\<one> \<in> M"
    and associative [intro]: "\<lbrakk> a \<in> M; b \<in> M; c \<in> M \<rbrakk> \<Longrightarrow> (a \<cdot> b) \<cdot> c = a \<cdot> (b \<cdot> c)"
    and left_unit [intro, simp]: "a \<in> M \<Longrightarrow> \<one> \<cdot> a = a"
    and right_unit [intro, simp]: "a \<in> M \<Longrightarrow> a \<cdot> \<one> = a"

text \<open>p 29, ll 27--28\<close>
locale Submonoid = Monoid M "(\<cdot>)" \<one>
  for N and M and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  assumes subset: "N \<subseteq> M"
    and sub_composition_closed: "\<lbrakk> a \<in> N; b \<in> N \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> N"
    and sub_unit_closed: "\<one> \<in> N"
begin

text \<open>p 29, ll 27--28\<close>
lemma sub [intro, simp]:
  "a \<in> N \<Longrightarrow> a \<in> M"
  using subset by blast

text \<open>p 29, ll 32--33\<close>
sublocale sub: Monoid N "(\<cdot>)" \<one>
proof qed (auto simp: sub_composition_closed sub_unit_closed)

end (* submonoid *)

text \<open>p 29, ll 33--34\<close>
theorem submonoid_transitive:
  assumes "Submonoid K N composition unit"
    and "Submonoid N M composition unit"
  shows "Submonoid K M composition unit"
proof -
  interpret K: Submonoid K N composition unit by fact
  interpret M: Submonoid N M composition unit by fact
  show ?thesis by unfold_locales auto
qed

text \<open>p 28, l 23\<close>
locale transformations =
  fixes S :: "'a set"

(*  assumes non_vacuous: "S \<noteq> {}" *) (* Jacobson requires this but we don't need it, strange. *)

text \<open>Monoid of all transformations\<close>
text \<open>p 28, ll 23--24\<close>
sublocale transformations \<subseteq> Monoid "S \<rightarrow>\<^sub>E S" "compose S" "identity S"
  by unfold_locales (auto simp: PiE_def compose_eq compose_assoc Id_compose compose_Id)

text \<open>@{term N} is a Monoid of transformations of the set @{term S}.\<close>
text \<open>p 29, ll 34--36\<close>
locale transformation_monoid =
  transformations S + Submonoid M "S \<rightarrow>\<^sub>E S" "compose S" "identity S" for M and S
begin

text \<open>p 29, ll 34--36\<close>
lemma transformation_closed [intro, simp]:
  "\<lbrakk> \<alpha> \<in> M; x \<in> S \<rbrakk> \<Longrightarrow> \<alpha> x \<in> S"
  by (metis PiE_iff sub)

text \<open>p 29, ll 34--36\<close>
lemma transformation_undefined [intro, simp]:
  "\<lbrakk> \<alpha> \<in> M; x \<notin> S \<rbrakk> \<Longrightarrow> \<alpha> x = undefined"
  by (metis PiE_arb sub)

end (* transformation_monoid *)


subsection \<open>Groups of Transformations and Abstract Groups\<close>

context Monoid begin

text \<open>Invertible elements\<close>

text \<open>p 31, ll 3--5\<close>
definition invertible where "invertible u \<equiv> (\<exists>v \<in> M. u \<cdot> v = \<one> \<and> v \<cdot> u = \<one>)"

text \<open>p 31, ll 3--5\<close>
lemma invertibleI [intro]:
  "\<lbrakk> u \<cdot> v = \<one>; v \<cdot> u = \<one>; v \<in> M \<rbrakk> \<Longrightarrow> invertible u"
  unfolding invertible_def by fast

text \<open>p 31, ll 3--5\<close>
lemma invertibleE [elim]:
  "\<lbrakk> invertible u; \<And>v. \<lbrakk> u \<cdot> v = \<one> \<and> v \<cdot> u = \<one>; v \<in> M \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding invertible_def by fast

text \<open>p 31, ll 6--7\<close>
theorem inverse_unique:
  "\<lbrakk> u \<cdot> v' = \<one>; v \<cdot> u = \<one>; u \<in> M;  v \<in> M; v' \<in> M \<rbrakk> \<Longrightarrow> v = v'"
  by (metis associative left_unit right_unit)

text \<open>p 31, l 7\<close>
definition inverse where "inverse \<equiv> (\<lambda>u \<in> M. THE v. v \<in> M \<and> u \<cdot> v = \<one> \<and> v \<cdot> u = \<one>)"

text \<open>p 31, l 7\<close>
theorem inverse_equality:
  "\<lbrakk> u \<cdot> v = \<one>; v \<cdot> u = \<one>; u \<in> M; v \<in> M \<rbrakk> \<Longrightarrow> inverse u = v"
  using inverse_def local.inverse_unique by auto

text \<open>p 31, l 7\<close>
lemma invertible_inverse_closed [intro, simp]:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> inverse u \<in> M"
  using inverse_equality by auto

text \<open>p 31, l 7\<close>
lemma inverse_undefined [intro, simp]:
  "u \<notin> M \<Longrightarrow> inverse u = undefined"
  by (metis (lifting) inverse_def restrict_apply)

text \<open>p 31, l 7\<close>
lemma invertible_left_inverse [simp]:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> inverse u \<cdot> u = \<one>"
  using inverse_equality by auto

text \<open>p 31, l 7\<close>
lemma invertible_right_inverse [simp]:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> u \<cdot> inverse u = \<one>"
  using inverse_equality by auto

text \<open>p 31, l 7\<close>
lemma invertible_left_cancel [simp]:
  "\<lbrakk> invertible x; x \<in> M; y \<in> M; z \<in> M \<rbrakk> \<Longrightarrow> x \<cdot> y = x \<cdot> z \<longleftrightarrow> y = z"
  by (metis associative invertible_def left_unit)

text \<open>p 31, l 7\<close>
lemma invertible_right_cancel [simp]:
  "\<lbrakk> invertible x; x \<in> M; y \<in> M; z \<in> M \<rbrakk> \<Longrightarrow> y \<cdot> x = z \<cdot> x \<longleftrightarrow> y = z"
  by (metis associative invertible_def right_unit)

text \<open>p 31, l 7\<close>
lemma inverse_unit [simp]: "inverse \<one> = \<one>"
  using inverse_equality by blast

text \<open>p 31, ll 7--8\<close>
theorem invertible_inverse_invertible [intro, simp]:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> invertible (inverse u)"
  using invertible_left_inverse invertible_right_inverse by blast

text \<open>p 31, l 8\<close>
theorem invertible_inverse_inverse [simp]:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> inverse (inverse u) = u"
  by (simp add: inverse_equality)

end (* Monoid *)

context Submonoid begin

text \<open>Reasoning about @{term invertible} and @{term inverse} in submonoids.\<close>

text \<open>p 31, l 7\<close>
lemma submonoid_invertible [intro, simp]:
  "\<lbrakk> sub.invertible u; u \<in> N \<rbrakk> \<Longrightarrow> invertible u"
  using invertibleI by blast

text \<open>p 31, l 7\<close>
lemma submonoid_inverse_closed [intro, simp]:
  "\<lbrakk> sub.invertible u; u \<in> N \<rbrakk> \<Longrightarrow> inverse u \<in> N"
  using inverse_equality by auto

end (* submonoid *)

text \<open>Def 1.2\<close>
text \<open>p 31, ll 9--10\<close>
locale Group =
  Monoid G "(\<cdot>)" \<one> for G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  assumes invertible [simp, intro]: "u \<in> G \<Longrightarrow> invertible u"

text \<open>A self-contained introduction rule for groups: the monoid laws together with the
  existence of a two-sided inverse for every element (stated directly, without reference
  to the @{const Monoid.invertible} predicate, which would otherwise require a separate
  monoid interpretation).\<close>
lemma GroupI:
  fixes G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
  assumes "\<And>a b. \<lbrakk> a \<in> G; b \<in> G \<rbrakk> \<Longrightarrow> a \<cdot> b \<in> G"
    and "\<one> \<in> G"
    and "\<And>a b c. \<lbrakk> a \<in> G; b \<in> G; c \<in> G \<rbrakk> \<Longrightarrow> (a \<cdot> b) \<cdot> c = a \<cdot> (b \<cdot> c)"
    and "\<And>a. a \<in> G \<Longrightarrow> \<one> \<cdot> a = a"
    and "\<And>a. a \<in> G \<Longrightarrow> a \<cdot> \<one> = a"
    and inv: "\<And>u. u \<in> G \<Longrightarrow> \<exists>v \<in> G. u \<cdot> v = \<one> \<and> v \<cdot> u = \<one>"
  shows "Group G (\<cdot>) \<one>"
proof -
  interpret Monoid G "(\<cdot>)" \<one>
    using assms(1-5) by unfold_locales blast+
  show ?thesis
  proof unfold_locales
    fix u assume "u \<in> G"
    then obtain v where "v \<in> G" "u \<cdot> v = \<one>" "v \<cdot> u = \<one>" using inv by blast
    then show "invertible u" using invertibleI by blast
  qed
qed

text \<open>p 31, ll 11--12\<close>
text \<open>The first parameter @{term H} is the \<^emph>\<open>subgroup\<close> and @{term G} the ambient
  group, mirroring the parameter order of @{locale Submonoid}.  At all use sites one
  writes \<open>subgroup H G\<close> (subgroup then ambient); the later locales
  \<open>subgroup_of_group\<close> and \<open>normal_subgroup\<close> take their parameters in the same order.\<close>
locale Subgroup = Submonoid H G "(\<cdot>)" \<one> + sub: Group H "(\<cdot>)" \<one>
  for H and G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
begin

text \<open>Reasoning about @{term invertible} and @{term inverse} in subgroups.\<close>

text \<open>p 31, ll 11--12\<close>
lemma subgroup_inverse_equality [simp]:
  "u \<in> H \<Longrightarrow> inverse u = sub.inverse u"
  by (simp add: inverse_equality)

text \<open>p 31, ll 11--12\<close>
lemma subgroup_inverse_iff [simp]:
  "\<lbrakk> invertible x; x \<in> G \<rbrakk> \<Longrightarrow> inverse x \<in> H \<longleftrightarrow> x \<in> H"
  using invertible_inverse_inverse sub.invertible_inverse_closed by fastforce

end (* subgroup *)

text \<open>A subgroup is in particular a group in its own right.\<close>
lemma subgroup_imp_Group:
  assumes "Subgroup H M composition unit"
  shows "Group H composition unit"
  using assms Subgroup.axioms(2) by fastforce


text \<open>p 31, ll 11--12\<close>
lemma subgroup_transitive [trans]:
  assumes "Subgroup K H composition unit"
    and "Subgroup H G composition unit"
  shows "Subgroup K G composition unit"
proof -
  interpret K: Subgroup K H composition unit by fact
  interpret H: Subgroup H G composition unit by fact
  show ?thesis by unfold_locales auto
qed

lemma subgroup_restrict:
  assumes I: "Subgroup I G composition unit"
    and H: "Subgroup H G composition unit"
    and "I \<subseteq> H"
  shows "Subgroup I H composition unit"
proof -
  interpret I: Subgroup I G composition unit by fact
  interpret H: Subgroup H G composition unit by fact
  have "Submonoid I H composition unit"
  proof (rule Submonoid.intro[OF H.sub.Monoid_axioms], rule Submonoid_axioms.intro)
    show "I \<subseteq> H" by fact
    show "\<And>a b. \<lbrakk>a \<in> I; b \<in> I\<rbrakk> \<Longrightarrow> composition a b \<in> I"
      by (rule I.sub_composition_closed)
    show "unit \<in> I" by (rule I.sub_unit_closed)
  qed
  then show ?thesis
    by (rule Subgroup.intro) (rule I.sub.Group_axioms)
qed

context Monoid begin

text \<open>Jacobson states both directions, but the other one is trivial.\<close>
text \<open>p 31, ll 12--15\<close>
theorem subgroupI:
  fixes G
  assumes subset [THEN subsetD, intro]: "G \<subseteq> M"
    and [intro]: "\<one> \<in> G"
    and [intro]: "\<And>g h. \<lbrakk> g \<in> G; h \<in> G \<rbrakk> \<Longrightarrow> g \<cdot> h \<in> G"
    and [intro]: "\<And>g. g \<in> G \<Longrightarrow> invertible g"
    and [intro]: "\<And>g. g \<in> G \<Longrightarrow> inverse g \<in> G"
  shows "Subgroup G M (\<cdot>) \<one>"
proof -
  interpret sub: Monoid G "(\<cdot>)" \<one> by unfold_locales auto
  show ?thesis
  proof unfold_locales
    fix u assume [intro]: "u \<in> G" show "sub.invertible u"
    using invertible_left_inverse invertible_right_inverse by blast
  qed auto
qed

text \<open>p 31, l 16\<close>
definition "Units = {u \<in> M. invertible u}"

text \<open>p 31, l 16\<close>
lemma mem_UnitsI:
  "\<lbrakk> invertible u; u \<in> M \<rbrakk> \<Longrightarrow> u \<in> Units"
  unfolding Units_def by clarify

text \<open>p 31, l 16\<close>
lemma mem_UnitsD:
  "\<lbrakk> u \<in> Units \<rbrakk> \<Longrightarrow> invertible u \<and> u \<in> M"
  unfolding Units_def by clarify

text \<open>p 31, ll 16--21\<close>
interpretation units: Subgroup Units M
proof (rule subgroupI)
  fix u1 u2
  assume Units [THEN mem_UnitsD, simp]: "u1 \<in> Units" "u2 \<in> Units"
  have "(u1 \<cdot> u2) \<cdot> (inverse u2 \<cdot> inverse u1) = (u1 \<cdot> (u2 \<cdot> inverse u2)) \<cdot> inverse u1"
    by (simp add: associative del: invertible_left_inverse invertible_right_inverse)
  also have "\<dots> = \<one>" by simp
  finally have inv1: "(u1 \<cdot> u2) \<cdot> (inverse u2 \<cdot> inverse u1) = \<one>" by simp  \<comment> \<open>ll 16--18\<close>
  have "(inverse u2 \<cdot> inverse u1) \<cdot> (u1 \<cdot> u2) = (inverse u2 \<cdot> (inverse u1 \<cdot> u1)) \<cdot> u2"
    by (simp add: associative del: invertible_left_inverse invertible_right_inverse)
  also have "\<dots> = \<one>" by simp
  finally have inv2: "(inverse u2 \<cdot> inverse u1) \<cdot> (u1 \<cdot> u2) = \<one>" by simp  \<comment> \<open>l 9, ``and similarly''\<close>
  show "u1 \<cdot> u2 \<in> Units" using inv1 inv2 invertibleI mem_UnitsI by auto
qed (auto simp: Units_def)

text \<open>p 31, ll 21--22\<close>
theorem group_of_Units [intro, simp]:
  "Group Units (\<cdot>) \<one>"
  ..

text \<open>p 31, l 19\<close>
lemma composition_invertible [simp, intro]:
  "\<lbrakk> invertible x; invertible y; x \<in> M; y \<in> M \<rbrakk> \<Longrightarrow> invertible (x \<cdot> y)"
  using mem_UnitsD mem_UnitsI by blast

text \<open>p 31, l 20\<close>
lemma unit_invertible:
  "invertible \<one>"
  by fast

text \<open>Useful simplification rules\<close>
text \<open>p 31, l 22\<close>
lemma invertible_right_inverse2:
  "\<lbrakk> invertible u; u \<in> M; v \<in> M \<rbrakk> \<Longrightarrow> u \<cdot> (inverse u \<cdot> v) = v"
  by (simp add: associative [THEN sym])

text \<open>p 31, l 22\<close>
lemma invertible_left_inverse2:
  "\<lbrakk> invertible u; u \<in> M; v \<in> M \<rbrakk> \<Longrightarrow> inverse u \<cdot> (u \<cdot> v) = v"
  by (simp add: associative [THEN sym])

text \<open>p 31, l 22\<close>
lemma inverse_composition_commute:
  assumes [simp]: "invertible x" "invertible y" "x \<in> M" "y \<in> M"
  shows "inverse (x \<cdot> y) = inverse y \<cdot> inverse x"
proof -
  have "inverse (x \<cdot> y) \<cdot> (x \<cdot> y) = (inverse y \<cdot> inverse x) \<cdot> (x \<cdot> y)"
  by (simp add: invertible_left_inverse2 associative)
  then show ?thesis by (simp del: invertible_left_inverse)
qed

lemma conjugate_composition:
  assumes "invertible g" "g \<in> M" "a \<in> M" "b \<in> M"
  shows "inverse g \<cdot> (a \<cdot> b) \<cdot> g =
         (inverse g \<cdot> a \<cdot> g) \<cdot> (inverse g \<cdot> b \<cdot> g)"
proof -
  have invg: "inverse g \<in> M"
    by (rule invertible_inverse_closed[OF assms(1,2)])
  have ab: "a \<cdot> b \<in> M" by (rule composition_closed[OF assms(3,4)])
  have bg: "b \<cdot> g \<in> M" by (rule composition_closed[OF assms(4,2)])
  have ia: "inverse g \<cdot> a \<in> M" by (rule composition_closed[OF invg assms(3)])
  have ib: "inverse g \<cdot> b \<in> M" by (rule composition_closed[OF invg assms(4)])
  have ibg: "inverse g \<cdot> b \<cdot> g \<in> M"
    by (rule composition_closed[OF ib assms(2)])
  have cancel: "g \<cdot> (inverse g \<cdot> (b \<cdot> g)) = b \<cdot> g"
    by (rule invertible_right_inverse2[OF assms(1,2) bg])
  have left:
    "inverse g \<cdot> (a \<cdot> b) \<cdot> g = inverse g \<cdot> (a \<cdot> (b \<cdot> g))"
  proof -
    have "inverse g \<cdot> (a \<cdot> b) \<cdot> g = inverse g \<cdot> ((a \<cdot> b) \<cdot> g)"
      by (rule associative[OF invg ab assms(2)])
    also have "\<dots> = inverse g \<cdot> (a \<cdot> (b \<cdot> g))"
      by (simp only: associative[OF assms(3,4,2)])
    finally show ?thesis .
  qed
  have right:
    "(inverse g \<cdot> a \<cdot> g) \<cdot> (inverse g \<cdot> b \<cdot> g) =
     inverse g \<cdot> (a \<cdot> (b \<cdot> g))"
  proof -
    have "(inverse g \<cdot> a \<cdot> g) \<cdot> (inverse g \<cdot> b \<cdot> g) =
          (inverse g \<cdot> a) \<cdot> (g \<cdot> (inverse g \<cdot> b \<cdot> g))"
      by (rule associative[OF ia assms(2) ibg])
    also have "\<dots> = (inverse g \<cdot> a) \<cdot> (g \<cdot> (inverse g \<cdot> (b \<cdot> g)))"
      by (simp only: associative[OF invg assms(4,2)])
    also have "\<dots> = (inverse g \<cdot> a) \<cdot> (b \<cdot> g)"
      by (simp only: cancel)
    also have "\<dots> = inverse g \<cdot> (a \<cdot> (b \<cdot> g))"
      by (rule associative[OF invg assms(3) bg])
    finally show ?thesis .
  qed
  show ?thesis by (rule trans[OF left right[symmetric]])
qed

end (* Monoid *)

context Group begin

text \<open>The whole group is a subgroup of itself.\<close>
lemma group_self_subgroup: "Subgroup G G (\<cdot>) \<one>"
  by (rule subgroupI) auto

text \<open>The trivial subgroup, consisting of the unit alone.\<close>
lemma trivial_subgroup: "Subgroup {\<one>} G (\<cdot>) \<one>"
  by (rule subgroupI) auto


subsection \<open>The subgroup generated by a set\<close>

text \<open>
  The subgroup generated by a set @{term S} of elements of a group, defined
  inductively as the smallest set containing @{term "S \<inter> G"} and closed under the
  group operations.  This basic construction underlies commutators, the derived
  series, and solvability.
\<close>

inductive_set generate :: "'a set \<Rightarrow> 'a set" for S :: "'a set"
  where
    unit:  "\<one> \<in> generate S"
  | incl:  "x \<in> S \<inter> G \<Longrightarrow> x \<in> generate S"
  | comp:  "\<lbrakk> x \<in> generate S; y \<in> generate S \<rbrakk> \<Longrightarrow> x \<cdot> y \<in> generate S"
  | inv:   "x \<in> generate S \<Longrightarrow> inverse x \<in> generate S"

definition Gen :: "'a set \<Rightarrow> 'a set" (\<open>\<langle>_\<rangle>\<close>)
  where "\<langle>S\<rangle> \<equiv> generate (S \<inter> G)"

text \<open>Everything generated lies in the carrier.\<close>
lemma generate_subset_carrier: "generate S \<subseteq> G"
proof
  fix x assume "x \<in> generate S"
  then show "x \<in> G"
  proof induction
    case unit then show ?case by simp
  next
    case (incl x) then show ?case by simp
  next
    case (comp x y) then show ?case by simp
  next
    case (inv x) then show ?case by simp
  qed
qed

lemma Gen_subset_carrier: "\<langle>S\<rangle> \<subseteq> G"
  unfolding Gen_def by (rule generate_subset_carrier)

text \<open>The generated set is a subgroup.\<close>
lemma generate_is_subgroup: "Subgroup (generate S) G (\<cdot>) \<one>"
proof (rule subgroupI)
  show "generate S \<subseteq> G" by (rule generate_subset_carrier)
next
  show "\<one> \<in> generate S" by (rule generate.unit)
next
  fix g h assume "g \<in> generate S" "h \<in> generate S"
  then show "g \<cdot> h \<in> generate S" by (rule generate.comp)
next
  fix g assume "g \<in> generate S"
  then have "g \<in> G" using generate_subset_carrier by auto
  then show "invertible g" by simp
next
  fix g assume "g \<in> generate S"
  then show "inverse g \<in> generate S" by (rule generate.inv)
qed

lemma Gen_is_subgroup: "Subgroup \<langle>S\<rangle> G (\<cdot>) \<one>"
  unfolding Gen_def by (rule generate_is_subgroup)

text \<open>The generating set is included (intersected with the carrier).\<close>
lemma generate_incl: "S \<inter> G \<subseteq> generate S"
  using generate.incl by auto

lemma Gen_incl: "S \<inter> G \<subseteq> \<langle>S\<rangle>"
  unfolding Gen_def using generate.incl by auto

text \<open>@{term "generate S"} is the smallest subgroup containing @{term "S \<inter> G"}.\<close>
lemma generate_minimal:
  assumes "Subgroup H G (\<cdot>) \<one>" and "S \<inter> G \<subseteq> H"
  shows "generate S \<subseteq> H"
proof
  interpret H: Subgroup H G "(\<cdot>)" \<one> by (rule assms(1))
  fix x assume "x \<in> generate S"
  then show "x \<in> H"
  proof induction
    case unit then show ?case by (rule H.sub_unit_closed)
  next
    case (incl x) then show ?case using assms(2) by auto
  next
    case (comp x y)
    then show ?case using H.sub_composition_closed by blast
  next
    case (inv x)
    then show ?case using H.submonoid_inverse_closed H.sub.invertible by auto
  qed
qed

lemma Gen_minimal:
  assumes "Subgroup H G (\<cdot>) \<one>" and "S \<inter> G \<subseteq> H"
  shows "\<langle>S\<rangle> \<subseteq> H"
  unfolding Gen_def using assms by (intro generate_minimal) auto

text \<open>Monotonicity.\<close>
lemma generate_mono:
  assumes "S \<subseteq> T"
  shows "generate S \<subseteq> generate T"
proof (rule generate_minimal)
  show "Subgroup (generate T) G (\<cdot>) \<one>" by (rule generate_is_subgroup)
  show "S \<inter> G \<subseteq> generate T" using assms generate_incl by auto
qed

lemma Gen_mono:
  assumes "S \<subseteq> T"
  shows "\<langle>S\<rangle> \<subseteq> \<langle>T\<rangle>"
  unfolding Gen_def using assms by (intro generate_mono) (auto)

text \<open>A subgroup generates itself.\<close>
lemma generate_subgroup_eq:
  assumes "Subgroup H G (\<cdot>) \<one>" and "H \<subseteq> G"
  shows "generate H = H"
proof
  show "generate H \<subseteq> H" using assms by (intro generate_minimal) auto
  show "H \<subseteq> generate H" using assms generate_incl by auto
qed

lemma Gen_subgroup_eq:
  assumes "Subgroup H G (\<cdot>) \<one>"
  shows "\<langle>H\<rangle> = H"
proof -
  interpret H: Subgroup H G "(\<cdot>)" \<one> by (rule assms)
  have "H \<subseteq> G" by auto
  then show ?thesis unfolding Gen_def using assms
    by (simp add: Int_absorb2 generate_subgroup_eq)
qed

text \<open>Idempotence.\<close>
lemma Gen_idem: "\<langle>\<langle>S\<rangle>\<rangle> = \<langle>S\<rangle>"
  using Gen_is_subgroup by (rule Gen_subgroup_eq)

text \<open>The intersection characterisation: @{term "\<langle>S\<rangle>"} is the intersection of all
  subgroups containing @{term "S \<inter> G"}.\<close>
lemma Gen_eq_Inter:
  "\<langle>S\<rangle> = \<Inter>{H. Subgroup H G (\<cdot>) \<one> \<and> S \<inter> G \<subseteq> H}"
proof
  show "\<langle>S\<rangle> \<subseteq> \<Inter>{H. Subgroup H G (\<cdot>) \<one> \<and> S \<inter> G \<subseteq> H}"
    using Gen_minimal by auto
next
  have "\<langle>S\<rangle> \<in> {H. Subgroup H G (\<cdot>) \<one> \<and> S \<inter> G \<subseteq> H}"
    using Gen_is_subgroup Gen_incl by auto
  then show "\<Inter>{H. Subgroup H G (\<cdot>) \<one> \<and> S \<inter> G \<subseteq> H} \<subseteq> \<langle>S\<rangle>"
    by (rule Inter_lower)
qed

text \<open>The set generated inside a subgroup (with the restricted operation) is contained
  in the set generated in the ambient group.  A locality property of @{const generate}.\<close>
lemma generate_subgroup_subset:
  assumes H: "Subgroup H G (\<cdot>) \<one>"
  shows "Group.generate H (\<cdot>) \<one> S \<subseteq> generate S"
proof
  interpret S: Subgroup H G "(\<cdot>)" \<one> by (rule H)
  fix x assume "x \<in> Group.generate H (\<cdot>) \<one> S"
  then show "x \<in> generate S"
  proof induction
    case unit
    then show ?case by (rule generate.unit)
  next
    case (incl x)
    then have "x \<in> S \<inter> G" using S.sub by auto
    then show ?case by (rule generate.incl)
  next
    case (comp x y)
    then show ?case using generate.comp by blast
  next
    case (inv x)
    have "x \<in> H" using inv.hyps S.sub.generate_subset_carrier by auto
    then have "S.sub.inverse x = inverse x" by (simp add: S.subgroup_inverse_equality)
    then show ?case using inv.IH generate.inv by simp
  qed
qed

end (* Group *)

text \<open>p 31, l 24\<close>
context transformations begin

text \<open>p 31, ll 25--26\<close>
theorem invertible_is_bijective:
  assumes dom: "\<alpha> \<in> S \<rightarrow>\<^sub>E S"
  shows "invertible \<alpha> \<longleftrightarrow> bij_betw \<alpha> S S"
  using bij_betw_iff_has_inverse dom invertible_def by auto

text \<open>p 31, ll 26--27\<close>
theorem Units_bijective:
  "Units = {\<alpha> \<in> S \<rightarrow>\<^sub>E S. bij_betw \<alpha> S S}"
  unfolding Units_def by (auto simp add: invertible_is_bijective)

text \<open>p 31, ll 26--27\<close>
lemma Units_bij_betwI [intro, simp]:
  "\<alpha> \<in> Units \<Longrightarrow> bij_betw \<alpha> S S"
  by (simp add: Units_bijective)

text \<open>p 31, ll 26--27\<close>
lemma Units_bij_betwD [dest, simp]:
  "\<lbrakk> \<alpha> \<in> S \<rightarrow>\<^sub>E S; bij_betw \<alpha> S S \<rbrakk> \<Longrightarrow> \<alpha> \<in> Units"
  unfolding Units_bijective by simp

text \<open>p 31, ll 28--29\<close>
abbreviation "Sym \<equiv> Units"

text \<open>p 31, ll 26--28\<close>
sublocale symmetric: Group "Sym" "compose S" "identity S"
  by (fact group_of_Units)

end (* transformations *)

text \<open>p 32, ll 18--19\<close>
locale transformation_group =
  transformations S + symmetric: Subgroup G Sym "compose S" "identity S" for G and S
begin

text \<open>p 32, ll 18--19\<close>
lemma transformation_group_closed [intro, simp]:
  "\<lbrakk> \<alpha> \<in> G; x \<in> S \<rbrakk> \<Longrightarrow> \<alpha> x \<in> S"
  using bij_betwE by blast

text \<open>p 32, ll 18--19\<close>
lemma transformation_group_undefined [intro, simp]:
  "\<lbrakk> \<alpha> \<in> G; x \<notin> S \<rbrakk> \<Longrightarrow> \<alpha> x = undefined"
  by (metis compose_def symmetric.sub.right_unit restrict_apply)

end (* transformation_group *)


subsection \<open>Isomorphisms.  Cayley's Theorem\<close>

text \<open>Def 1.3\<close>
text \<open>p 37, ll 7--11\<close>
locale Monoid_isomorphism =
  bijective_map \<eta> M M'  + source: Monoid M "(\<cdot>)" \<one> + target: Monoid M' "(\<cdot>')" "\<one>'"
  for \<eta> and M and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
        and M' and composition' (infixl \<open>\<cdot>''\<close> 70) and unit' (\<open>\<one>''\<close>) +
  assumes commutes_with_composition: "\<lbrakk> x \<in> M; y \<in> M \<rbrakk> \<Longrightarrow> \<eta> x \<cdot>' \<eta> y = \<eta> (x \<cdot> y)"
    and commutes_with_unit: "\<eta> \<one> = \<one>'"

text \<open>p 37, l 10\<close>
definition isomorphic_as_monoids (infixl \<open>\<cong>\<^sub>M\<close> 50)
  where "\<M> \<cong>\<^sub>M \<M>' \<longleftrightarrow> (let (M, composition, unit) = \<M>; (M', composition', unit') = \<M>' in
  (\<exists>\<eta>. Monoid_isomorphism \<eta> M composition unit M' composition' unit'))"

text \<open>p 37, ll 11--12\<close>
locale Monoid_isomorphism' =
  bijective_map \<eta> M M'  + source: Monoid M "(\<cdot>)" \<one> + target: Monoid M' "(\<cdot>')" "\<one>'"
  for \<eta> and M and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
    and M' and composition' (infixl \<open>\<cdot>''\<close> 70) and unit' (\<open>\<one>''\<close>) +
  assumes commutes_with_composition: "\<lbrakk> x \<in> M; y \<in> M \<rbrakk> \<Longrightarrow> \<eta> x \<cdot>' \<eta> y = \<eta> (x \<cdot> y)"

text \<open>p 37, ll 11--12\<close>
sublocale Monoid_isomorphism \<subseteq> Monoid_isomorphism'
  by unfold_locales (use commutes_with_composition in auto)

text \<open>Both definitions are equivalent.\<close>
text \<open>p 37, ll 12--15\<close>
sublocale Monoid_isomorphism' \<subseteq> Monoid_isomorphism
proof 
  {
    fix y assume "y \<in> M'"
    then obtain x where "\<eta> x = y" "x \<in> M"
      using bij_betw_imp_surj_on by blast
    then have "y \<cdot>' \<eta> \<one> = y" using commutes_with_composition by auto
  }
  then show "\<eta> \<one> = \<one>'"
    using bij_betwE by fastforce
qed (auto simp: commutes_with_composition)

context Monoid_isomorphism 
begin

text \<open>p 37, ll 30--33\<close>
theorem inverse_monoid_isomorphism:
  "Monoid_isomorphism (restrict (inv_into M \<eta>) M') M' (\<cdot>') \<one>' M (\<cdot>) \<one>"
proof -
  have "\<And>x y. \<lbrakk>x \<in> M'; y \<in> M'\<rbrakk>
           \<Longrightarrow> inv_into M \<eta> x \<cdot> inv_into M \<eta> y = inv_into M \<eta> (x \<cdot>' y)"
    using commutes_with_composition surjective by fastforce
  with bij_betw_inv_into bij_betw_inv_into_left commutes_with_unit target.unit_closed 
  show ?thesis
  proof unfold_locales qed fastforce+
qed

end (* Monoid_isomorphism *)

text \<open>We only need that @{term \<eta>} is symmetric.\<close>
text \<open>p 37, ll 28--29\<close>
theorem isomorphic_as_monoids_symmetric:
  "(M, composition, unit) \<cong>\<^sub>M (M', composition', unit') \<Longrightarrow> (M', composition', unit') \<cong>\<^sub>M (M, composition, unit)"
  by (simp add: isomorphic_as_monoids_def) (meson Monoid_isomorphism.inverse_monoid_isomorphism)

text \<open>p 38, l 4\<close>
locale left_translations_of_monoid = Monoid begin

(*
  We take the liberty of omitting "left_" from the name of the translation operation.  The derived
  transformation Monoid and Group won't be qualified with "left" either.  This avoids qualifications
  such as "left.left_...".  In contexts where left and right translations are used simultaneously,
  notably subgroup_of_group, qualifiers are needed.
*)

text \<open>p 38, ll 5--7\<close>
definition translation (\<open>'(_')\<^sub>L\<close>) where "translation = (\<lambda>a \<in> M. \<lambda>x \<in> M. a \<cdot> x)"

text \<open>p 38, ll 5--7\<close>
lemma translation_map [intro, simp]:
  "a \<in> M \<Longrightarrow> (a)\<^sub>L \<in> M \<rightarrow>\<^sub>E M"
  unfolding translation_def by simp

text \<open>p 38, ll 5--7\<close>
lemma Translations_maps [intro, simp]:
  "translation ` M \<subseteq> M \<rightarrow>\<^sub>E M"
  by (simp add: image_subsetI)

text \<open>p 38, ll 5--7\<close>
lemma translation_apply:
  "\<lbrakk> a \<in> M; b \<in> M \<rbrakk> \<Longrightarrow> (a)\<^sub>L b = a \<cdot> b"
  unfolding translation_def by auto

text \<open>p 38, ll 5--7\<close>
lemma translation_exist:
  "f \<in> translation ` M \<Longrightarrow> \<exists>a \<in> M. f = (a)\<^sub>L"
  by auto

text \<open>p 38, ll 5--7\<close>
lemmas Translations_E [elim] = translation_exist [THEN bexE]

text \<open>p 38, l 10\<close>
theorem translation_unit_eq [simp]:
  "identity M = (\<one>)\<^sub>L"
  unfolding translation_def
  by (metis left_unit restrict_apply' restrict_ext unit_closed)

text \<open>p 38, ll 10--11\<close>
theorem translation_composition_eq [simp]:
  assumes [simp]: "a \<in> M" "b \<in> M"
  shows "compose M (a)\<^sub>L (b)\<^sub>L = (a \<cdot> b)\<^sub>L"
  by (auto simp: associative compose_def translation_def)

(* Activate @{locale Monoid} to simplify subsequent proof. *)
text \<open>p 38, ll 7--9\<close>
sublocale transformation: transformations M .

text \<open>p 38, ll 7--9\<close>
theorem Translations_transformation_monoid:
  "transformation_monoid (translation ` M) M"
  by unfold_locales auto

text \<open>p 38, ll 7--9\<close>
sublocale transformation: transformation_monoid "translation ` M" M
  by (fact Translations_transformation_monoid)

text \<open>p 38, l 12\<close>
lemma translation_is_map: "translation \<in> M \<rightarrow>\<^sub>E (translation ` M)"
  using translation_def by force

text \<open>p 38, ll 12--16\<close>
theorem translation_isomorphism [intro]:
  "Monoid_isomorphism translation M (\<cdot>) \<one> (translation ` M) (compose M) (identity M)"
proof 
  have "inj_on translation M"
  proof (rule inj_onI)
    fix a b
    assume [simp]: "a \<in> M" "b \<in> M" "(a)\<^sub>L = (b)\<^sub>L"
    have "(a)\<^sub>L \<one> = (b)\<^sub>L \<one>" by simp
    then show "a = b" by (simp add: translation_def)
  qed
  then show "bij_betw translation M (translation ` M)"
    by (simp add: inj_on_imp_bij_betw)
  show "translation \<in> M \<rightarrow>\<^sub>E translation ` M"
    using translation_is_map by auto
qed simp_all

text \<open>p 38, ll 12--16\<close>
sublocale Monoid_isomorphism translation M "(\<cdot>)" \<one> "translation ` M" "compose M" "identity M" ..

end (* left_translations_of_monoid *)

context Monoid begin

text \<open>p 38, ll 1--2\<close>
interpretation left_translations_of_monoid ..

text \<open>p 38, ll 1--2\<close>
theorem cayley_monoid:
  "\<exists>M' composition' unit'. transformation_monoid M' M \<and> (M, (\<cdot>), \<one>) \<cong>\<^sub>M (M', composition', unit')"
  by (simp add: isomorphic_as_monoids_def) (fast intro: Translations_transformation_monoid)

end (* Monoid *)

text \<open>p 38, l 17\<close>
locale left_translations_of_group = Group begin

text \<open>p 38, ll 17--18\<close>
sublocale left_translations_of_monoid where M = G ..

text \<open>p 38, ll 17--18\<close>
notation translation (\<open>'(_')\<^sub>L\<close>)

text \<open>
  The Group of left translations is a subgroup of the symmetric Group,
  hence @{term transformation.sub.invertible}.
\<close>
text \<open>p 38, ll 20--22\<close>
theorem translation_invertible [intro, simp]:
  assumes [simp]: "a \<in> G"
  shows "transformation.sub.invertible (a)\<^sub>L"
proof
  show "compose G (a)\<^sub>L (inverse a)\<^sub>L = identity G" by simp
next
  show "compose G (inverse a)\<^sub>L (a)\<^sub>L = identity G" by simp
qed auto

text \<open>p 38, ll 19--20\<close>
theorem translation_bijective [intro, simp]:
  "a \<in> G \<Longrightarrow> bij_betw (a)\<^sub>L G G"
  by (blast intro: transformation.invertible_is_bijective [THEN iffD1])

text \<open>p 38, ll 18--20\<close>
theorem Translations_transformation_group:
  "transformation_group (translation ` G) G"
proof unfold_locales
  show "(translation ` G) \<subseteq> transformation.Sym"
    unfolding transformation.Units_bijective by auto
next
  fix \<alpha>
  assume \<alpha>: "\<alpha> \<in> translation ` G"
  then obtain a where a: "a \<in> G" and eq: "\<alpha> = (a)\<^sub>L" ..
  with translation_invertible show "transformation.sub.invertible \<alpha>" by simp
qed auto

text \<open>p 38, ll 18--20\<close>
sublocale transformation: transformation_group "translation ` G" G
  by (fact Translations_transformation_group)

end (* left_translations_of_group *)

context Group begin

text \<open>p 38, ll 2--3\<close>
interpretation left_translations_of_group ..

text \<open>p 38, ll 2--3\<close>
theorem cayley_group:
  "\<exists>G' composition' unit'. transformation_group G' G \<and> (G, (\<cdot>), \<one>) \<cong>\<^sub>M (G', composition', unit')"
  by (simp add: isomorphic_as_monoids_def) (fast intro: Translations_transformation_group)

end (* Group *)

text \<open>Exercise 3\<close>

text \<open>p 39, ll 9--10\<close>
locale right_translations_of_group = Group begin

text \<open>p 39, ll 9--10\<close>
definition translation (\<open>'(_')\<^sub>R\<close>) where "translation = (\<lambda>a \<in> G. \<lambda>x \<in> G. x \<cdot> a)"

text \<open>p 39, ll 9--10\<close>
abbreviation "Translations \<equiv> translation ` G"

text \<open>The isomorphism that will be established is a map different from @{term translation}.\<close>
text \<open>p 39, ll 9--10\<close>
lemma "translation \<in> G \<rightarrow>\<^sub>E Translations"
  by (simp add: translation_def)

text \<open>p 39, ll 9--10\<close>
lemma translation_map [intro, simp]:
  "a \<in> G \<Longrightarrow> (a)\<^sub>R \<in> G \<rightarrow>\<^sub>E G"
  unfolding translation_def by simp

text \<open>p 39, ll 9--10\<close>
lemma Translation_maps [intro, simp]:
  "Translations \<subseteq> G \<rightarrow>\<^sub>E G"
  by (simp add: image_subsetI)

text \<open>p 39, ll 9--10\<close>
lemma translation_apply:
  "\<lbrakk> a \<in> G; b \<in> G \<rbrakk> \<Longrightarrow> (a)\<^sub>R b = b \<cdot> a"
  unfolding translation_def by auto

text \<open>p 39, ll 9--10\<close>
lemma translation_exist:
  "f \<in> Translations \<Longrightarrow> \<exists>a \<in> G. f = (a)\<^sub>R"
  by auto

text \<open>p 39, ll 9--10\<close>
lemmas Translations_E [elim] = translation_exist [THEN bexE]

text \<open>p 39, ll 9--10\<close>
lemma translation_unit_eq [simp]:
  "identity G = (\<one>)\<^sub>R"
  unfolding translation_def by auto

text \<open>p 39, ll 10--11\<close>
lemma translation_composition_eq [simp]:
  assumes [simp]: "a \<in> G" "b \<in> G"
  shows "compose G (a)\<^sub>R (b)\<^sub>R = (b \<cdot> a)\<^sub>R"
  unfolding translation_def by rule (simp add: associative compose_def)

text \<open>p 39, ll 10--11\<close>
sublocale transformation: transformations G .

text \<open>p 39, ll 10--11\<close>
lemma Translations_transformation_monoid:
  "transformation_monoid Translations G"
  by unfold_locales auto

text \<open>p 39, ll 10--11\<close>
sublocale transformation: transformation_monoid Translations G
  by (fact Translations_transformation_monoid)

text \<open>p 39, ll 10--11\<close>
lemma translation_invertible [intro, simp]:
  assumes [simp]: "a \<in> G"
  shows "transformation.sub.invertible (a)\<^sub>R"
proof
  show "compose G (a)\<^sub>R (inverse a)\<^sub>R = identity G" by simp
next
  show "compose G (inverse a)\<^sub>R (a)\<^sub>R = identity G" by simp
qed auto

text \<open>p 39, ll 10--11\<close>
lemma translation_bijective [intro, simp]:
  "a \<in> G \<Longrightarrow> bij_betw (a)\<^sub>R G G"
  by (blast intro: transformation.invertible_is_bijective [THEN iffD1])

text \<open>p 39, ll 10--11\<close>
theorem Translations_transformation_group:
  "transformation_group Translations G"
proof unfold_locales
  show "Translations \<subseteq> transformation.Sym"
  unfolding transformation.Units_bijective by auto
next
  fix \<alpha>
  assume \<alpha>: "\<alpha> \<in> Translations"
  then obtain a where a: "a \<in> G" and eq: "\<alpha> = (a)\<^sub>R" ..
  with translation_invertible show "transformation.sub.invertible \<alpha>" by simp
qed auto

text \<open>p 39, ll 10--11\<close>
sublocale transformation: transformation_group Translations G
  by (rule Translations_transformation_group)

text \<open>p 39, ll 10--11\<close>
lemma translation_inverse_eq [simp]:
  assumes [simp]: "a \<in> G"
  shows "transformation.sub.inverse (a)\<^sub>R = (inverse a)\<^sub>R"
proof (rule transformation.sub.inverse_equality)
  show "compose G (a)\<^sub>R (inverse a)\<^sub>R = identity G" by simp
next
  show "compose G (inverse a)\<^sub>R (a)\<^sub>R = identity G" by simp
qed auto

text \<open>p 39, ll 10--11\<close>
theorem translation_inverse_monoid_isomorphism [intro]:
  "Monoid_isomorphism (\<lambda>a\<in>G. transformation.symmetric.inverse (a)\<^sub>R) G (\<cdot>) \<one> Translations (compose G) (identity G)"
  (is "Monoid_isomorphism ?inv _ _ _ _ _ _")
proof 
  note bij_betw_compose [trans]
  have "bij_betw inverse G G"
    by (rule bij_betwI [where g = inverse]) auto
  also have "bij_betw translation G Translations"
    by (rule bij_betwI [where g = "\<lambda>\<alpha>\<in>Translations. \<alpha> \<one>"]) (auto simp: translation_apply)
  finally show "bij_betw ?inv G Translations"
    by (simp cong: bij_betw_cong add: compose_eq del: translation_unit_eq)
  show "?inv \<one> = identity G"
    using transformation.symmetric.inverse_unit by auto
  show "?inv \<in> G \<rightarrow>\<^sub>E Translations"
    using transformation.symmetric.submonoid_inverse_closed
      transformation.symmetric.sub.invertible by auto
next
  fix x and y
  assume [simp]: "x \<in> G" "y \<in> G"
  show "compose G (?inv x) (?inv y) = (?inv (x \<cdot> y))" by (simp add: inverse_composition_commute del: translation_unit_eq)
qed

text \<open>p 39, ll 10--11\<close>
sublocale Monoid_isomorphism
  "\<lambda>a\<in>G. transformation.symmetric.inverse (a)\<^sub>R" G "(\<cdot>)" \<one> Translations "compose G" "identity G" ..

end (* right_translations_of_group *)


subsection \<open>Generalized Associativity.  Commutativity\<close>

text \<open>p 40, l 27; p 41, ll 1--2\<close>
locale commutative_monoid = Monoid +
  assumes commutative: "\<lbrakk> x \<in> M; y \<in> M \<rbrakk> \<Longrightarrow> x \<cdot> y = y \<cdot> x"
begin

text \<open>The left-commutativity law: together with @{thm associative} and @{thm commutative} it forms a
  confluent rewrite system for normalising products.  We bundle the three as @{text ac} so a proof
  can request full associative-commutative normalisation on demand via @{text "simp add: ac"}, rather
  than making them global @{attribute simp} rules (which would change the simplifier's normal form
  throughout the development).\<close>
lemma left_commutative:
  assumes "x \<in> M" "y \<in> M" "z \<in> M"
  shows "x \<cdot> (y \<cdot> z) = y \<cdot> (x \<cdot> z)"
proof -
  have "x \<cdot> (y \<cdot> z) = (x \<cdot> y) \<cdot> z" using assms by (simp add: associative)
  also have "\<dots> = (y \<cdot> x) \<cdot> z" using assms by (simp add: commutative)
  also have "\<dots> = y \<cdot> (x \<cdot> z)" using assms by (simp add: associative)
  finally show ?thesis .
qed

lemmas ac = associative commutative left_commutative

end

text \<open>p 41, l 2\<close>
locale Abelian_Group = Group + commutative_monoid G "(\<cdot>)" \<one>


subsection \<open>Orbits.  Cosets of a Subgroup\<close>

context transformation_group begin

text \<open>p 51, ll 18--20\<close>
definition Orbit_Relation
  where "Orbit_Relation = {(x, y). x \<in> S \<and> y \<in> S \<and> (\<exists>\<alpha> \<in> G. y = \<alpha> x)}"

text \<open>p 51, ll 18--20\<close>
lemma Orbit_Relation_memI [intro]:
  "\<lbrakk> y = \<alpha> x; \<alpha> \<in> G; x \<in> S \<rbrakk> \<Longrightarrow> (x, y) \<in> Orbit_Relation"
  unfolding Orbit_Relation_def by auto

text \<open>p 51, ll 18--20\<close>
lemma Orbit_Relation_memE [elim]:
  "\<lbrakk> (x, y) \<in> Orbit_Relation; \<And>\<alpha>. \<lbrakk> \<alpha> \<in> G; x \<in> S; y = \<alpha> x \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  unfolding Orbit_Relation_def by auto

text \<open>p 51, ll 20--23, 26--27\<close>
sublocale orbit: Equivalence S Orbit_Relation
proof (intro equivalenceI)
  show "Orbit_Relation \<subseteq> S \<times> S"
    by (auto simp: Orbit_Relation_def)
next
  fix a
  assume "a \<in> S"
  then show "(a, a) \<in> Orbit_Relation"
    using Orbit_Relation_memI by fastforce
next
  fix a b
  assume "(a, b) \<in> Orbit_Relation"
  then show "(b, a) \<in> Orbit_Relation"
    by (metis Orbit_Relation_memE Orbit_Relation_memI compose_eq restrict_apply' symmetric.sub.invertible
        symmetric.sub.invertible_def transformation_group_closed)
next
  fix a b c
  assume "(a, b) \<in> Orbit_Relation" and "(b, c) \<in> Orbit_Relation"
  then have "\<exists>\<alpha>\<in>G. c = \<alpha> a"
    by (metis Orbit_Relation_memE compose_eq symmetric.sub_composition_closed)
  then show "(a, c) \<in> Orbit_Relation"
    using \<open>(a, b) \<in> Orbit_Relation\<close> by blast
qed


text \<open>p 51, ll 23--24\<close>
theorem orbit_equality:
  "x \<in> S \<Longrightarrow> orbit.Class x = {\<alpha> x | \<alpha>. \<alpha> \<in> G}"
by (simp add: orbit.Class_def) (blast intro: orbit.symmetric dest: orbit.symmetric)

end (* transformation_group *)

context Monoid_isomorphism begin

text \<open>p 52, ll 16--17\<close>
theorem image_subgroup:
  assumes "Subgroup G M (\<cdot>) \<one>"
  shows "Subgroup (\<eta> ` G) M' (\<cdot>') \<one>'"
proof -
  interpret Subgroup G M "(\<cdot>)" \<one> by fact
  interpret image: Monoid "\<eta> ` G" "(\<cdot>')" "\<one>'"
    by unfold_locales (auto simp: commutes_with_composition sub.associative simp flip: commutes_with_unit)
  show ?thesis
  proof
    show "\<eta> ` G \<subseteq> M'"
      using bij_betw_imp_surj_on by blast
  next
    fix u :: 'b
    assume "u \<in> \<eta> ` G"
    then show "image.invertible u"
      using commutes_with_composition commutes_with_unit sub.invertible_def image.invertible_def by fastforce
  qed auto
qed

end (* Monoid_isomorphism *)

text \<open>
  Technical device to achieve Jacobson's notation for @{text Right_Coset} and @{text Left_Coset}.  The
  definitions are pulled out of @{text subgroup_of_group} to a context where @{text H} is not a parameter.
\<close>
text \<open>p 52, l 20\<close>
locale coset_notation = fixes composition (infixl \<open>\<cdot>\<close> 70)  begin

text \<open>Equation 23\<close>
text \<open>p 52, l 20\<close>
definition Right_Coset (infixl \<open>|\<cdot>\<close> 70) where "H |\<cdot> x \<equiv> (\<lambda>h. h \<cdot> x) ` H"

text \<open>p 53, ll 8--9\<close>
definition Left_Coset (infixl \<open>\<cdot>|\<close> 70) where "x \<cdot>| H \<equiv> (\<lambda>h. x \<cdot> h) ` H"

text \<open>p 52, l 20\<close>
lemma Right_Coset_memI [intro]:
  "h \<in> H \<Longrightarrow> h \<cdot> x \<in> H |\<cdot> x"
  unfolding Right_Coset_def by blast

text \<open>p 52, l 20\<close>
lemma Right_Coset_memE [elim]:
  "\<lbrakk> a \<in> H |\<cdot> x; \<And>h. \<lbrakk> h \<in> H; a = h \<cdot> x \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding Right_Coset_def by blast

text \<open>p 53, ll 8--9\<close>
lemma Left_Coset_memI [intro]:
  "h \<in> H \<Longrightarrow> x \<cdot> h \<in> x \<cdot>| H"
  unfolding Left_Coset_def by blast

text \<open>p 53, ll 8--9\<close>
lemma Left_Coset_memE [elim]:
  "\<lbrakk> a \<in> x \<cdot>| H; \<And>h. \<lbrakk> h \<in> H; a = x \<cdot> h \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding Left_Coset_def by blast

end (* coset_notation *)

text \<open>p 52, l 12\<close>
locale subgroup_of_group = Subgroup H G "(\<cdot>)" \<one> + coset_notation "(\<cdot>)" + Group G "(\<cdot>)" \<one>
  for H and G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
begin

text \<open>p 52, ll 12--14\<close>
interpretation left: left_translations_of_group ..
interpretation right: right_translations_of_group ..

text \<open>
  @{term "left.translation ` H"} denotes Jacobson's @{text "H\<^sub>L(G)"} and
  @{term "left.translation ` G"} denotes Jacobson's @{text "G\<^sub>L"}.
\<close>

text \<open>p 52, ll 16--18\<close>
theorem left_translations_of_subgroup_are_transformation_group [intro]:
  "transformation_group (left.translation ` H) G"
proof -
  have "Subgroup (left.translation ` H) (left.translation ` G) (compose G) (identity G)"
    by (rule left.image_subgroup) unfold_locales
  also have "Subgroup (left.translation ` G) left.transformation.Sym (compose G) (identity G)" ..
  finally interpret right_coset: Subgroup "left.translation ` H" left.transformation.Sym "compose G" "identity G" .
  show ?thesis ..
qed

text \<open>p 52, l 18\<close>
interpretation transformation_group "left.translation ` H" G ..

text \<open>p 52, ll 19--20\<close>
theorem Right_Coset_is_orbit:
  "x \<in> G \<Longrightarrow> H |\<cdot> x = orbit.Class x"
  using left.translation_apply by (auto simp: orbit_equality Right_Coset_def) (metis imageI sub)

text \<open>p 52, ll 24--25\<close>
theorem Right_Coset_Union:
  "(\<Union>x\<in>G. H |\<cdot> x) = G"
  by (simp add: Right_Coset_is_orbit)

text \<open>p 52, l 26\<close>
theorem Right_Coset_bij:
  assumes G [simp]: "x \<in> G" "y \<in> G"
  shows "bij_betw (inverse x \<cdot> y)\<^sub>R (H |\<cdot> x) (H |\<cdot> y)"
proof (rule bij_betw_imageI)
  show "inj_on (inverse x \<cdot> y)\<^sub>R (H |\<cdot> x)"
    unfolding inj_on_def
    by (smt (verit) Right_Coset_memE assms  associative composition_closed in_mono invertible
        invertible_inverse_closed invertible_right_inverse right.translation_apply right_unit subset)
next
  show "(inverse x \<cdot> y)\<^sub>R ` (H |\<cdot> x) = H |\<cdot> y"
    by (force simp add: right.translation_apply associative invertible_right_inverse2)
qed

text \<open>p 52, ll 25--26\<close>
theorem Right_Cosets_cardinality:
  "\<lbrakk> x \<in> G; y \<in> G \<rbrakk> \<Longrightarrow> card (H |\<cdot> x) = card (H |\<cdot> y)"
  by (fast intro: bij_betw_same_card Right_Coset_bij)

text \<open>p 52, l 27\<close>
theorem Right_Coset_unit:
  "H |\<cdot> \<one> = H"
  by (force simp add: Right_Coset_def)

text \<open>p 52, l 27\<close>
theorem Right_Coset_cardinality:
  "x \<in> G \<Longrightarrow> card (H |\<cdot> x) = card H"
  using Right_Coset_unit Right_Cosets_cardinality unit_closed by presburger

text \<open>p 52, ll 31--32\<close>
definition "index = card orbit.Partition"

text \<open>Theorem 1.5\<close>
text \<open>p 52, ll 33--35; p 53, ll 1--2\<close>
theorem lagrange:
  assumes "finite G"
  shows "card G = card H * index"
  unfolding index_def
proof (subst card_partition)
  fix c :: "'a set"
  assume "c \<in> orbit.Partition"
  then show "card c = card H"
    using Right_Coset_cardinality Right_Coset_is_orbit orbit.Partition_def
    by auto
next
  fix c1 c2
  assume "c1 \<in> orbit.Partition" and "c2 \<in> orbit.Partition"
    and "c1 \<noteq> c2"
  then show "c1 \<inter> c2 = {}"
    using orbit.not_disjoint_implies_equal
    by (auto simp: image_iff orbit.Partition_def)
qed (use assms in \<open>auto simp: orbit.Partition_def\<close>)

end (* subgroup_of_group *)

lemma subgroup_of_groupI:
  assumes "Subgroup H G composition unit" and "Group G composition unit"
  shows "subgroup_of_group H G composition unit"
proof -
  interpret H: Subgroup H G composition unit by fact
  interpret G: Group G composition unit by fact
  show ?thesis by unfold_locales
qed

text \<open>Left cosets\<close>

context Subgroup begin

text \<open>p 31, ll 11--12\<close>

lemma image_of_inverse [intro, simp]:
  "x \<in> H \<Longrightarrow> x \<in> inverse ` H"
  by (smt (verit) imageI inverse_equality sub sub.invertible sub.invertibleE)

lemma image_of_inverse_iff:
  "x \<in> inverse ` H \<longleftrightarrow> x \<in> H"
  by blast

end (* subgroup *)

context Group begin

text \<open>p 53, ll 6--7\<close>
lemma inverse_subgroupI:
  assumes sub: "Subgroup H G (\<cdot>) \<one>"
  shows "Subgroup (inverse ` H) G (\<cdot>) \<one>"
proof -
  from sub interpret Subgroup H G "(\<cdot>)" \<one> .
  interpret inv: Monoid "inverse ` H" "(\<cdot>)" \<one>
    by unfold_locales (auto simp del: subgroup_inverse_equality)
  interpret inv: Group "inverse ` H" "(\<cdot>)" \<one>
    by unfold_locales (force simp del: subgroup_inverse_equality)
  show ?thesis
    by unfold_locales (auto simp del: subgroup_inverse_equality)
qed

text \<open>p 53, ll 6--7\<close>
lemma inverse_subgroupD:
  assumes sub: "Subgroup (inverse ` H) G (\<cdot>) \<one>"
    and inv: "H \<subseteq> Units"
  shows "Subgroup H G (\<cdot>) \<one>"
proof -
  from sub have "Subgroup (inverse ` inverse ` H) G (\<cdot>) \<one>" by (rule inverse_subgroupI)
  moreover from inv [THEN subsetD, simplified Units_def] have "inverse ` inverse ` H = H"
    by (simp cong: image_cong add: image_comp)
  ultimately show ?thesis by simp
qed

text \<open>Intersections are the basic way of restricting subgroups and normal
  subgroups to a smaller ambient group.\<close>

lemma subgroup_intersection:
  assumes "Subgroup H G (\<cdot>) \<one>" "Subgroup K G (\<cdot>) \<one>"
  shows "Subgroup (H \<inter> K) G (\<cdot>) \<one>"
proof -
  interpret H: Subgroup H G "(\<cdot>)" \<one> by fact
  interpret K: Subgroup K G "(\<cdot>)" \<one> by fact
  interpret HK: Monoid "H \<inter> K" "(\<cdot>)" \<one>
    by unfold_locales auto
  show ?thesis
  proof
    fix u
    assume u: "u \<in> H \<inter> K"
    have inv_H: "local.inverse u \<in> H"
      by (rule H.submonoid_inverse_closed) (use u in auto)
    have inv_K: "local.inverse u \<in> K"
      by (rule K.submonoid_inverse_closed) (use u in auto)
    have right: "u \<cdot> local.inverse u = \<one>"
      using u by simp
    have left: "local.inverse u \<cdot> u = \<one>"
      using u by simp
    show "HK.invertible u"
      unfolding HK.invertible_def
      using inv_H inv_K left right by blast
  qed auto
qed

lemma commute_iff_inverse:
  assumes "g \<in> G" "h \<in> G"
  shows "(g \<cdot> h = h \<cdot> g) \<longleftrightarrow> (g \<cdot> h \<cdot> local.inverse g = h)"
proof -
  have "g \<cdot> h \<in> G"
    using assms by simp
  then have "g \<cdot> h \<cdot> local.inverse g \<cdot> g = g \<cdot> h \<cdot> (local.inverse g \<cdot> g)"
    using assms by blast
  then show ?thesis
    using assms by auto
qed

end (* Group *)

context subgroup_of_group begin

text \<open>p 53, l 6\<close>
interpretation right_translations_of_group ..

text \<open>
  @{term "translation ` H"} denotes Jacobson's @{text "H\<^sub>R(G)"} and
  @{term "Translations"} denotes Jacobson's @{text "G\<^sub>R"}.
\<close>

text \<open>p 53, ll 6--7\<close>
theorem right_translations_of_subgroup_are_transformation_group [intro]:
  "transformation_group (translation ` H) G"
proof -
  have "Subgroup ((\<lambda>a\<in>G. transformation.symmetric.inverse (a)\<^sub>R) ` H) Translations (compose G) (identity G)"
    by (rule image_subgroup) unfold_locales
  also have "Subgroup Translations transformation.Sym (compose G) (identity G)" ..
  finally interpret left_coset: Subgroup "translation ` H" transformation.Sym "compose G" "identity G"
    by (auto intro: transformation.symmetric.inverse_subgroupD cong: image_cong
      simp: image_image transformation.symmetric.Units_def simp del: translation_unit_eq)
  show ?thesis ..
qed

text \<open>p 53, ll 6--7\<close>
interpretation transformation_group "translation ` H" G ..

text \<open>Equation 23 for left cosets\<close>
text \<open>p 53, ll 7--8\<close>
theorem Left_Coset_is_orbit:
  "x \<in> G \<Longrightarrow> x \<cdot>| H = orbit.Class x"
  using translation_apply
  by (auto simp: orbit_equality Left_Coset_def) (metis imageI sub)

end (* subgroup_of_group *)


subsection \<open>Congruences.  Quotient Monoids and Groups\<close>

text \<open>Def 1.4\<close>
text \<open>p 54, ll 19--22\<close>
locale Monoid_congruence = Monoid + Equivalence where S = M +
  assumes cong: "\<lbrakk> (a, a') \<in> E; (b, b') \<in> E \<rbrakk> \<Longrightarrow> (a \<cdot> b, a' \<cdot> b') \<in> E"
begin

text \<open>p 54, ll 26--28\<close>
theorem Class_cong:
  "\<lbrakk> Class a = Class a'; Class b = Class b'; a \<in> M; a' \<in> M; b \<in> M; b' \<in> M \<rbrakk> \<Longrightarrow> Class (a \<cdot> b) = Class (a' \<cdot> b')"
  by (simp add: Class_equivalence cong)

text \<open>p 54, ll 28--30\<close>
definition quotient_composition (infixl \<open>[\<cdot>]\<close> 70)
  where "quotient_composition = (\<lambda>A \<in> M / E. \<lambda>B \<in> M / E. THE C. \<exists>a \<in> A. \<exists>b \<in> B. C = Class (a \<cdot> b))"

text \<open>p 54, ll 28--30\<close>
theorem Class_commutes_with_composition:
  "\<lbrakk> a \<in> M; b \<in> M \<rbrakk> \<Longrightarrow> Class a [\<cdot>] Class b = Class (a \<cdot> b)"
  by (auto simp: quotient_composition_def intro: Class_cong [OF Class_eq Class_eq] del: equalityI)

text \<open>p 54, ll 30--31\<close>
theorem quotient_composition_closed [intro, simp]:
  "\<lbrakk> A \<in> M / E; B \<in> M / E \<rbrakk> \<Longrightarrow> A [\<cdot>] B \<in> M / E"
  using Class_commutes_with_composition Partition_def by auto

text \<open>p 54, l 32; p 55, ll 1--3\<close>
sublocale quotient: Monoid "M / E" "([\<cdot>])" "Class \<one>"
  by unfold_locales (auto simp: Class_commutes_with_composition associative elim!: quotient_ClassE)

end (* Monoid_congruence *)

text \<open>p 55, ll 16--17\<close>
locale group_congruence = Group + Monoid_congruence where M = G begin

text \<open>p 55, ll 16--17\<close>
notation quotient_composition (infixl \<open>[\<cdot>]\<close> 70)

text \<open>p 55, l 18\<close>
theorem Class_right_inverse:
  "a \<in> G \<Longrightarrow> Class a [\<cdot>] Class (inverse a) = Class \<one>"
  by (simp add: Class_commutes_with_composition)

text \<open>p 55, l 18\<close>
theorem Class_left_inverse:
  "a \<in> G \<Longrightarrow> Class (inverse a) [\<cdot>] Class a = Class \<one>"
  by (simp add: Class_commutes_with_composition)

text \<open>p 55, l 18\<close>
theorem Class_invertible:
  "a \<in> G \<Longrightarrow> quotient.invertible (Class a)"
  by (blast intro!: Class_right_inverse Class_left_inverse)+

text \<open>p 55, l 18\<close>
theorem Class_commutes_with_inverse:
  "a \<in> G \<Longrightarrow> quotient.inverse (Class a) = Class (inverse a)"
  by (rule quotient.inverse_equality) (auto simp: Class_right_inverse Class_left_inverse)

text \<open>p 55, l 17\<close>
sublocale quotient: Group "G / E" "([\<cdot>])" "Class \<one>"
  by unfold_locales (metis Class_invertible quotient_ClassE)

end (* group_congruence *)

text \<open>Def 1.5\<close>
text \<open>p 55, ll 22--25\<close>
locale normal_subgroup =
  subgroup_of_group K G "(\<cdot>)" \<one> for K and G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  assumes normal: "\<lbrakk> g \<in> G; k \<in> K \<rbrakk> \<Longrightarrow> inverse g \<cdot> k \<cdot> g \<in> K"

context Group begin

text \<open>The trivial subgroup is normal in every group.\<close>
lemma trivial_normal_subgroup:
  "normal_subgroup {\<one>} G (\<cdot>) \<one>"
proof (intro normal_subgroup.intro subgroup_of_group.intro)
  show "Subgroup {\<one>} G (\<cdot>) \<one>" by (rule trivial_subgroup)
  show "Group G (\<cdot>) \<one>" by (rule Group_axioms)
  show "normal_subgroup_axioms {\<one>} G (\<cdot>) \<one>"
  proof
    fix g k
    assume "g \<in> G" "k \<in> {\<one>}"
    then show "inverse g \<cdot> k \<cdot> g \<in> {\<one>}" by simp
  qed
qed

end

text \<open>Lemmas from the proof of Thm 1.6\<close>

context subgroup_of_group begin

text \<open>We use @{term H} for @{term K}.\<close>
text \<open>p 56, ll 14--16\<close>
theorem Left_equals_Right_coset_implies_normality:
  assumes [simp]: "\<And>g. g \<in> G \<Longrightarrow> g \<cdot>| H = H |\<cdot> g"
  shows "normal_subgroup H G (\<cdot>) \<one>"
proof
  fix g k
  assume [simp]: "g \<in> G" "k \<in> H"
  have "k \<cdot> g \<in> g \<cdot>| H" by auto
  then obtain k' where "k \<cdot> g = g \<cdot> k'" and "k' \<in> H" by blast
  then show "inverse g \<cdot> k \<cdot> g \<in> H" by (simp add: associative invertible_left_inverse2)
qed

end (* subgroup_of_group *)

text \<open>Thm 1.6, first part\<close>

context group_congruence begin

text \<open>Jacobson's $K$\<close>
text \<open>p 56, l 29\<close>
definition "Normal = Class \<one>"

text \<open>p 56, ll 3--6\<close>
interpretation Subgroup "Normal" G "(\<cdot>)" \<one>
  unfolding Normal_def
proof (rule subgroupI)
  fix k1 and k2
  assume K: "k1 \<in> Class \<one>" "k2 \<in> Class \<one>"
  then have "k1 \<cdot> k2 \<in> Class (k1 \<cdot> k2)" by blast
  also have "\<dots> = Class k1 [\<cdot>] Class k2" using K by (auto simp add: Class_commutes_with_composition Class_closed)
  also have "\<dots> = Class \<one> [\<cdot>] Class \<one>" using K by (metis ClassD Class_eq unit_closed)
  also have "\<dots> = Class \<one>" by simp
  finally show "k1 \<cdot> k2 \<in> Class \<one>" .
next
  fix k
  assume K: "k \<in> Class \<one>"
  then have "inverse k \<in> Class (inverse k)" 
    by blast
  also have "\<dots> = quotient.inverse (Class k)" 
    using Class_commutes_with_inverse K by blast
  also have "\<dots> = quotient.inverse (Class \<one>)"
    by (metis Class_eq K Equivalence.ClassD Equivalence_axioms unit_closed)
  also have "\<dots> = Class \<one>" using quotient.inverse_unit by blast
  finally show "inverse k \<in> Class \<one>" .
qed auto

text \<open>Coset notation\<close>
text \<open>p 56, ll 5--6\<close>
interpretation subgroup_of_group "Normal" G "(\<cdot>)" \<one> ..

text \<open>Equation 25 for right cosets\<close>
text \<open>p 55, ll 29--30; p 56, ll 6--11\<close>
theorem Right_Coset_Class_unit:
  assumes g: "g \<in> G" shows "Normal |\<cdot> g = Class g"
  unfolding Normal_def
proof auto
  fix a  \<comment> \<open>ll 6--8\<close>
  assume a: "a \<in> Class g"
  then have \<section>: "a \<cdot> inverse g \<in> Class \<one> \<Longrightarrow> \<exists>h. a = h \<cdot> g \<and> h \<in> Class \<one>"
    by (metis Class_closed associative g inverse_equality invertible invertible_def right_unit)
  from a g have "a \<cdot> inverse g \<in> Class (a \<cdot> inverse g)" by blast
  also from a g have "\<dots> = Class a [\<cdot>] Class (inverse g)"
    using Class_closed Class_commutes_with_composition invertible
      invertible_inverse_closed by presburger
  also from a g have "\<dots> = Class g [\<cdot>] quotient.inverse (Class g)"
    by (metis Class_commutes_with_inverse Class_eq ClassD)
  also from g have "\<dots> = Class \<one>" by simp
  finally show "a \<in> Class \<one> |\<cdot> g"
    using \<section> by (auto simp: Right_Coset_def)
next
  fix a  \<comment> \<open>ll 8--9\<close>
  assume a: "a \<in> Class \<one> |\<cdot> g"
  then obtain k where eq: "a = k \<cdot> g" and k: "k \<in> Class \<one>" 
    by blast
  with g have "Class a = Class k [\<cdot>] Class g" 
    using Class_commutes_with_composition by auto
  also from k have "\<dots> = Class \<one> [\<cdot>] Class g"
    by (metis ClassD Class_eq unit_closed)
  also from g have "\<dots> = Class g" by simp
  finally show "a \<in> Class g" using g eq k composition_closed quotient.unit_closed by blast
qed

text \<open>Equation 25 for left cosets\<close>
text \<open>p 55, ll 29--30; p 56, ll 6--11\<close>
theorem Left_Coset_Class_unit:
  assumes g: "g \<in> G" shows "g \<cdot>| Normal = Class g"
  unfolding Normal_def
proof auto
  fix a  \<comment> \<open>ll 6--8\<close>
  assume a: "a \<in> Class g"
  then have \<section>: "inverse g \<cdot> a \<in> Class \<one> \<Longrightarrow> \<exists>h. a = g \<cdot> h \<and> h \<in> Class \<one>"
    by (metis Class_closed associative g inverse_equality invertible invertible_def right_unit)
  from a g have "inverse g \<cdot> a \<in> Class (inverse g \<cdot> a)" by blast
  also from a g have "\<dots> = Class (inverse g) [\<cdot>] Class a"
    using Class_closed Class_commutes_with_composition invertible
      invertible_inverse_closed by presburger
  also from a g have "\<dots> = quotient.inverse (Class g) [\<cdot>] Class g"
    by (metis ClassD Class_commutes_with_inverse Class_eq)
  also from g have "\<dots> = Class \<one>" by simp
  finally show "a \<in> g \<cdot>| Class \<one>"
    using \<section> by (auto simp: Left_Coset_def)
next
  fix a  \<comment> \<open>ll 8--9, ``the same thing holds''\<close>
  assume a: "a \<in> g \<cdot>| Class \<one>"
  then obtain k where eq: "a = g \<cdot> k" and k: "k \<in> Class \<one>" 
    by blast
  with g have "Class a = Class g [\<cdot>] Class k" 
    using Class_commutes_with_composition by auto
  also from k have "\<dots> = Class g [\<cdot>] Class \<one>"
    by (metis ClassD Class_eq unit_closed)
  also from g have "\<dots> = Class g" by simp
  finally show "a \<in> Class g" using g eq k composition_closed quotient.unit_closed by blast
qed

text \<open>Thm 1.6, statement of first part\<close>
text \<open>p 55, ll 28--29; p 56, ll 12--16\<close>
theorem Class_unit_is_normal:
  "normal_subgroup Normal G (\<cdot>) \<one>"
proof -
  {
    fix g
    assume "g \<in> G"
    then have "g \<cdot>| Normal = Normal |\<cdot> g" by (simp add: Right_Coset_Class_unit Left_Coset_Class_unit)
  }
  then show ?thesis by (rule Left_equals_Right_coset_implies_normality)
qed

sublocale normal: normal_subgroup Normal G "(\<cdot>)" \<one>
  by (fact Class_unit_is_normal)

end (* group_congruence *)

context normal_subgroup begin

text \<open>p 56, ll 16--19\<close>
theorem Left_equals_Right_coset:
  "g \<in> G \<Longrightarrow> g \<cdot>| K = K |\<cdot> g"
proof
  assume [simp]: "g \<in> G"
  show "K |\<cdot> g \<subseteq> g \<cdot>| K"
  proof
    fix x
    assume x: "x \<in> K |\<cdot> g"
    then obtain k where "x = k \<cdot> g" and [simp]: "k \<in> K" by (auto simp add: Right_Coset_def)
    then have "x = g \<cdot> (inverse g \<cdot> k \<cdot> g)" by (simp add: associative invertible_right_inverse2)
    also from normal have "\<dots> \<in> g \<cdot>| K" by (auto simp add: Left_Coset_def)
    finally show "x \<in> g \<cdot>| K" .
  qed
next
  assume [simp]: "g \<in> G"
  show "g \<cdot>| K \<subseteq> K |\<cdot> g"
  proof
    fix x
    assume x: "x \<in> g \<cdot>| K"
    then obtain k where "x = g \<cdot> k" and [simp]: "k \<in> K" by (auto simp add: Left_Coset_def)
    then have "x = (inverse (inverse g) \<cdot> k \<cdot> inverse g) \<cdot> g" by (simp add: associative del: invertible_right_inverse)
    also from normal [where g = "inverse g"] have "\<dots> \<in> K |\<cdot> g" by (auto simp add: Right_Coset_def)
    finally show "x \<in> K |\<cdot> g" .
  qed
qed

text \<open>Thm 1.6, second part\<close>

text \<open>p 55, ll 31--32; p 56, ll 20--21\<close>
definition "Congruence = {(a, b). a \<in> G \<and> b \<in> G \<and> inverse a \<cdot> b \<in> K}"

text \<open>p 56, ll 21--22\<close>
interpretation right_translations_of_group ..

text \<open>p 56, ll 21--22\<close>
interpretation transformation_group "translation ` K" G rewrites "Orbit_Relation = Congruence"
proof -
  interpret transformation_group "translation ` K" G ..
  show "Orbit_Relation = Congruence"
    unfolding Orbit_Relation_def Congruence_def
    by (force simp: invertible_left_inverse2 invertible_right_inverse2 translation_apply simp del: restrict_apply)
qed rule

text \<open>p 56, ll 20--21\<close>
lemma CongruenceI: "\<lbrakk> a = b \<cdot> k; a \<in> G; b \<in> G; k \<in> K \<rbrakk> \<Longrightarrow> (a, b) \<in> Congruence"
  by (clarsimp simp: Congruence_def associative inverse_composition_commute)

text \<open>p 56, ll 20--21\<close>
lemma CongruenceD: "(a, b) \<in> Congruence \<Longrightarrow> \<exists>k\<in>K. a = b \<cdot> k"
  by (drule orbit.symmetric) (force simp: Congruence_def invertible_right_inverse2)

text \<open>
  ``We showed in the last section that the relation we are considering is an equivalence relation in
  @{term G} for any subgroup @{term K} of @{term G}.  We now proceed to show that normality of @{term K}
  ensures that [...] $a \equiv b \pmod{K}$ is a congruence.''
\<close>
text \<open>p 55, ll 30--32; p 56, ll 1, 22--28\<close>
sublocale group_congruence where E = Congruence rewrites "Normal = K"
proof -
  show "group_congruence G (\<cdot>) \<one> Congruence"
  proof unfold_locales
    note CongruenceI [intro] CongruenceD [dest]
    fix a g b h
    assume 1: "(a, g) \<in> Congruence" and 2: "(b, h) \<in> Congruence"
    then have G: "a \<in> G" "g \<in> G" "b \<in> G" "h \<in> G" unfolding Congruence_def by clarify+
    from 1 obtain k1 where a: "a = g \<cdot> k1" and k1: "k1 \<in> K" by blast
    from 2 obtain k2 where b: "b = h \<cdot> k2" and k2: "k2 \<in> K" by blast
    from G Left_equals_Right_coset have "K |\<cdot> h = h \<cdot>| K" by blast
    with k1 obtain k3 where c: "k1 \<cdot> h = h \<cdot> k3" and k3: "k3 \<in> K"
      unfolding Left_Coset_def Right_Coset_def by blast
    from G k1 k2 a b have "a \<cdot> b = g \<cdot> k1 \<cdot> h \<cdot> k2" by (simp add: associative)
    also from G k1 k3 c have "\<dots> = g \<cdot> h \<cdot> k3 \<cdot> k2" by (simp add: associative)
    also have "\<dots> = (g \<cdot> h) \<cdot> (k3 \<cdot> k2)" using G k2 k3 by (simp add: associative)
    finally show "(a \<cdot> b, g \<cdot> h) \<in> Congruence" using G k2 k3 by blast
  qed
  then interpret group_congruence where E = Congruence .
  show "Normal = K"
    unfolding Normal_def orbit.Class_def unfolding Congruence_def
    using invertible_inverse_inverse submonoid_inverse_closed by fastforce 
qed

lemma set_prod_commute:
  assumes "S \<subseteq> G"
  shows "(case_prod(\<cdot>)) ` (S \<times> K) = (case_prod(\<cdot>)) ` (K \<times> S)"
proof -
  have "\<exists>x\<in>K. \<exists>y\<in>S. a \<cdot> b = x \<cdot> y" if "a \<in> S" "b \<in> K" for a b
    using that assms
    by (metis Left_equals_Right_coset Right_Coset_memE coset_notation.Left_Coset_memI
        subsetD)
  moreover have "\<exists>x\<in>S. \<exists>y\<in>K. a \<cdot> b = x \<cdot> y" if "a \<in> K" "b \<in> S" for a b
    using that
    by (metis Left_Coset_memE Left_equals_Right_coset assms coset_notation.Right_Coset_memI
        subsetD)
  ultimately show ?thesis
    by (auto simp add: image_iff subset_iff)
qed

text \<open>p 56, ll 31--32; no infix syntax because it leads to many problems\<close>
abbreviation Factor_Group (* == Partition!*)
  where "Factor_Group \<equiv> G / (normal_subgroup.Congruence K G (\<cdot>) \<one>)"

end (* normal_subgroup *)  (* deletes translations and orbits, recovers Class for congruence class *)

context Group begin

lemma normal_subgroup_intersection:
  assumes K: "normal_subgroup K G (\<cdot>) \<one>"
    and H: "Subgroup H G (\<cdot>) \<one>"
  shows "normal_subgroup (H \<inter> K) H (\<cdot>) \<one>"
proof -
  interpret H: Subgroup H G "(\<cdot>)" \<one> by fact
  interpret K: normal_subgroup K G "(\<cdot>)" \<one> by fact
  have HK_G: "Subgroup (H \<inter> K) G (\<cdot>) \<one>"
    by (rule subgroup_intersection[OF H K.Subgroup_axioms])
  interpret HK: Subgroup "H \<inter> K" H "(\<cdot>)" \<one>
    by (rule subgroup_restrict[OF HK_G H]) auto
  show ?thesis
  proof
    fix h k
    assume h: "h \<in> H" and k: "k \<in> H \<inter> K"
    then show "H.sub.inverse h \<cdot> k \<cdot> h \<in> H \<inter> K"
      by (metis H.sub H.sub.invertible H.sub_composition_closed
          H.subgroup_inverse_equality H.submonoid_inverse_closed Int_iff K.normal)
  qed
qed

end (* Group *)

context normal_subgroup begin

text \<open>p 56, ll 28--29\<close>
theorem Class_unit_normal_subgroup: "Class \<one> = K"
  unfolding Class_def unfolding Congruence_def
  using invertible_inverse_inverse submonoid_inverse_closed by fastforce

text \<open>The quotient by a normal subgroup is trivial exactly when that
  subgroup is the whole carrier.  Keeping the representative argument here
  avoids repeating it for each client that packages a quotient group.\<close>
lemma Factor_Group_eq_singleton_iff:
  "Factor_Group = {Class \<one>} \<longleftrightarrow> K = G"
proof
  assume factor_group: "Factor_Group = {Class \<one>}"
  show "K = G"
  proof (rule equalityI)
    show "K \<subseteq> G" by (rule subset)
    show "G \<subseteq> K"
    proof
      fix x
      assume x: "x \<in> G"
      have class_mem: "Class x \<in> Factor_Group"
        by (rule Class_in_Partition[OF x])
      have class_eq: "Class x = Class \<one>"
        using class_mem factor_group by simp
      have "x \<in> Class x" by (rule Class_self[OF x])
      then have "x \<in> Class \<one>" using class_eq by simp
      then show "x \<in> K" using Class_unit_normal_subgroup by simp
    qed
  qed
next
  assume KG: "K = G"
  show "Factor_Group = {Class \<one>}"
  proof (rule equalityI)
    show "Factor_Group \<subseteq> {Class \<one>}"
    proof
      fix A
      assume A: "A \<in> Factor_Group"
      then obtain x where x: "x \<in> G" and A_eq: "A = Class x"
        using representant_exists by auto
      have xK: "x \<in> K" using KG x by simp
      have class_eq: "Class x = Class \<one>"
      proof (rule Class_eq)
        show "(x, \<one>) \<in> Congruence"
        proof (rule CongruenceI)
          show "x = \<one> \<cdot> x" by (rule left_unit[OF x, symmetric])
          show "x \<in> G" by fact
          show "\<one> \<in> G" by (rule unit_closed)
          show "x \<in> K" by fact
        qed
      qed
      show "A \<in> {Class \<one>}" using A_eq class_eq by simp
    qed
    show "{Class \<one>} \<subseteq> Factor_Group"
      using Class_in_Partition[OF unit_closed] by simp
  qed
qed

text \<open>p 56, ll 1--2; p 56, l 29\<close>
theorem Class_is_Left_Coset:
  "g \<in> G \<Longrightarrow> Class g = g \<cdot>| K"
  using Left_Coset_Class_unit Class_unit_normal_subgroup by simp

text \<open>p 56, l 29\<close>
lemma Left_CosetE: "\<lbrakk> A \<in> Factor_Group; \<And>a. a \<in> G \<Longrightarrow> P (a \<cdot>| K) \<rbrakk> \<Longrightarrow> P A"
  by (metis Class_is_Left_Coset quotient_ClassE)

text \<open>Equation 26\<close>
text \<open>p 56, ll 32--34\<close>
theorem factor_composition [simp]:
  "\<lbrakk> g \<in> G; h \<in> G \<rbrakk> \<Longrightarrow> (g \<cdot>| K) [\<cdot>] (h \<cdot>| K) = g \<cdot> h \<cdot>| K"
  using Class_commutes_with_composition Class_is_Left_Coset by auto

text \<open>p 56, l 35\<close>
theorem factor_unit:
  "K = \<one> \<cdot>| K"
  using Class_is_Left_Coset Class_unit_normal_subgroup by blast

text \<open>p 56, l 35\<close>
theorem factor_inverse [simp]:
  "g \<in> G \<Longrightarrow> quotient.inverse (g \<cdot>| K) = (inverse g \<cdot>| K)"
  using Class_commutes_with_inverse Class_is_Left_Coset by auto

lemma Factor_Group_eq_Left_Cosets:
  "Factor_Group = (\<lambda>g. g \<cdot>| K) ` G"
proof (rule set_eqI)
  fix A
  show "A \<in> Factor_Group \<longleftrightarrow> A \<in> (\<lambda>g. g \<cdot>| K) ` G"
  proof
    assume "A \<in> Factor_Group"
    then obtain g where "g \<in> G" "A = Class g"
      using quotient_ClassE by (metis representant_exists)
    then show "A \<in> (\<lambda>g. g \<cdot>| K) ` G"
      using Class_is_Left_Coset by blast
  next
    assume "A \<in> (\<lambda>g. g \<cdot>| K) ` G"
    then obtain g where "g \<in> G" "A = g \<cdot>| K" by blast
    then have "A = Class g" using Class_is_Left_Coset by simp
    then show "A \<in> Factor_Group"
      using Class_in_Partition \<open>g \<in> G\<close> by simp
  qed
qed

lemma Factor_Group_eq_Right_Cosets:
  "Factor_Group = (\<lambda>g. K |\<cdot> g) ` G"
  by (simp add: Right_Coset_Class_unit natural.surjective)

lemma Class_cardinality:
  assumes "g \<in> G"
  shows "card (Class g) = card K"
proof -
  have "Class g = g \<cdot>| K" using Class_is_Left_Coset assms by simp
  also have "\<dots> = K |\<cdot> g" using Left_equals_Right_coset assms by simp
  finally show ?thesis using Right_Coset_cardinality assms by simp
qed

lemma card_Factor_Group:
  assumes "finite G"
  shows "card (Factor_Group) = index"
proof -
  have fin_class: "finite p" if "p \<in> Partition" for p
    by (metis Class_closed2 assms finite_subset representant_exists that)
  have card_class: "card p = card K" if "p \<in> Partition" for p
    using Class_cardinality representant_exists that by blast
  have "card G = (\<Sum>p\<in>Partition. card p)"
    using product_partition [OF partition fin_class] by simp
  also have "\<dots> = (\<Sum>p\<in>Partition. card K)"
    using card_class by simp
  also have "\<dots> = card K * card Partition"
    by simp
  finally have "card G = card K * card Partition" .
  moreover have "card G = card K * index"
    using lagrange assms by simp
  moreover have "card K > 0"
    by (metis Normal_def card_eq_0_iff emptyE fin_class gr0I natural.map_closed sub
        sub_unit_closed)
  ultimately have "card K * card Partition = card K * index" by simp
  with \<open>card K > 0\<close> have "card Partition = index"
    using nat_mult_eq_cancel1 by simp
  then show ?thesis by simp
qed

lemma quotient_composition_PiE:
  "quotient_composition \<in> Factor_Group \<rightarrow>\<^sub>E Factor_Group \<rightarrow>\<^sub>E Factor_Group"
proof -
  have "quotient_composition A B \<in> Factor_Group" if "A \<in> Factor_Group" "B \<in> Factor_Group" for A B
    using that by simp
  then show ?thesis
    unfolding quotient_composition_def by (auto simp: restrict_PiE_iff)
qed

end (* normal_subgroup *)


text \<open>p 57, ll 4--5\<close>
locale subgroup_of_abelian_group = subgroup_of_group H G "(\<cdot>)" \<one> + Abelian_Group G "(\<cdot>)" \<one>
  for H and G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)

text \<open>p 57, ll 4--5\<close>
sublocale subgroup_of_abelian_group \<subseteq> normal_subgroup H G "(\<cdot>)" \<one>
  using commutative invertible_right_inverse2 by unfold_locales auto

context subgroup_of_abelian_group begin

lemma quotient_abelian: "Abelian_Group Factor_Group quotient_composition (Class \<one>)"
proof -
  have comm: "quotient_composition X Y = quotient_composition Y X"
    if XF: "X \<in> Factor_Group" and YF: "Y \<in> Factor_Group" for X Y
  proof -
    obtain a where aG: "a \<in> G" and Xa: "X = Class a"
      using representant_exists XF by blast
    obtain b where bG: "b \<in> G" and Yb: "Y = Class b"
      using representant_exists YF by blast
    have "X [\<cdot>] Y = Class (a \<cdot> b)"
      using aG bG by (simp add: Xa Yb Class_commutes_with_composition)
    also have "\<dots> = Class (b \<cdot> a)"
      using commutative aG bG by presburger
    also have "\<dots> = Y [\<cdot>] X"
      using aG bG by (simp add: Xa Yb Class_commutes_with_composition)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding Abelian_Group_def commutative_monoid_def commutative_monoid_axioms_def
    using quotient.Group_axioms quotient.Monoid_axioms comm by auto
qed

end

subsection \<open>Homomorphisms\<close>

text \<open>Def 1.6\<close>
text \<open>p 58, l 33; p 59, ll 1--2\<close>
locale Monoid_homomorphism =
  map \<eta> M M'  + source: Monoid M "(\<cdot>)" \<one> + target: Monoid M' "(\<cdot>')" "\<one>'"
  for \<eta> and M and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
    and M' and composition' (infixl \<open>\<cdot>''\<close> 70) and unit' (\<open>\<one>''\<close>) +
  assumes commutes_with_composition: "\<lbrakk> x \<in> M; y \<in> M \<rbrakk> \<Longrightarrow> \<eta> (x \<cdot> y) = \<eta> x \<cdot>' \<eta> y"
    and commutes_with_unit: "\<eta> \<one> = \<one>'"
begin

text \<open>Jacobson notes that @{thm [source] commutes_with_unit} is not necessary for groups, but doesn't make use of that later.\<close>

text \<open>p 58, l 33; p 59, ll 1--2\<close>
notation source.invertible (\<open>invertible _\<close> [100] 100)
notation source.inverse (\<open>inverse _\<close> [100] 100)
notation target.invertible (\<open>invertible'' _\<close> [100] 100)
notation target.inverse (\<open>inverse'' _\<close> [100] 100)

end (* Monoid_homomorphism *)

text \<open>p 59, ll 29--30\<close>
locale Monoid_epimorphism = Monoid_homomorphism + surjective_map \<eta> M M'

text \<open>p 59, l 30\<close>
locale Monoid_monomorphism = Monoid_homomorphism + injective_map \<eta> M M'

text \<open>p 59, ll 30--31\<close>
sublocale Monoid_isomorphism \<subseteq> Monoid_epimorphism
  by unfold_locales (auto simp: commutes_with_composition commutes_with_unit)

text \<open>p 59, ll 30--31\<close>
sublocale Monoid_isomorphism \<subseteq> Monoid_monomorphism
  by unfold_locales (auto simp: commutes_with_composition commutes_with_unit)

context Monoid_homomorphism begin

text \<open>p 59, ll 33--34\<close>
theorem invertible_image_lemma:
  assumes "invertible a" "a \<in> M"
  shows "\<eta> a \<cdot>' \<eta> (inverse a) = \<one>'" and "\<eta> (inverse a) \<cdot>' \<eta> a = \<one>'"
  using assms commutes_with_composition commutes_with_unit source.inverse_equality
  by auto (metis source.invertible_inverse_closed source.invertible_left_inverse)

text \<open>p 59, l 34; p 60, l 1\<close>
theorem invertible_target_invertible [intro, simp]:
  "\<lbrakk> invertible a; a \<in> M \<rbrakk> \<Longrightarrow> invertible' (\<eta> a)"
  using invertible_image_lemma by blast

text \<open>p 60, l 1\<close>
theorem invertible_commutes_with_inverse:
  "\<lbrakk> invertible a; a \<in> M \<rbrakk> \<Longrightarrow> \<eta> (inverse a) = inverse' (\<eta> a)"
  by (metis invertible_image_lemma map_closed
      source.invertible_inverse_closed target.inverse_equality)

end (* Monoid_homomorphism *)

text \<open>p 60, ll 32--34; p 61, l 1\<close>
sublocale Monoid_congruence 
  \<subseteq> natural: Monoid_homomorphism "Class" M "(\<cdot>)" \<one> "M / E" "([\<cdot>])" "Class \<one>"
proof
qed (auto simp add: Class_commutes_with_composition)

text \<open>Fundamental Theorem of Homomorphisms of Monoids\<close>

text \<open>p 61, ll 5, 14--16\<close>
sublocale Monoid_homomorphism \<subseteq> image: Submonoid "\<eta> ` M" M' "(\<cdot>')" "\<one>'"
  by unfold_locales (auto simp: commutes_with_composition [symmetric] commutes_with_unit [symmetric])

text \<open>p 61, l 4\<close>
locale Monoid_homomorphism_fundamental = Monoid_homomorphism 
begin

text \<open>p 61, ll 17--18\<close>
sublocale fiber_relation \<eta> M M' ..
notation Fiber_Relation (\<open>E'(_')\<close>)

text \<open>p 61, ll 6--7, 18--20\<close>
sublocale Monoid_congruence where E = "E(\<eta>)"
  using Class_eq
  by unfold_locales (rule Class_equivalence [THEN iffD1],
    auto simp: left_closed right_closed commutes_with_composition Fiber_equality)

text \<open>p 61, ll 7--9\<close>
text \<open>
  @{term induced} denotes Jacobson's $\bar{\eta}$.  We have the commutativity of the diagram, where
  @{term induced} is unique: @{thm [display] factorization} @{thm [display] uniqueness}.
\<close>

text \<open>p 61, l 20\<close>
notation quotient_composition (infixl \<open>[\<cdot>]\<close> 70)

text \<open>p 61, ll 7--8, 22--25\<close>
sublocale induced: Monoid_homomorphism induced "M / E(\<eta>)" "([\<cdot>])" "Class \<one>" "M'" "(\<cdot>')" "\<one>'"
proof
  fix x y
  assume "x \<in> Partition" and "y \<in> Partition"
  then show "induced (x [\<cdot>] y) = induced x \<cdot>' induced y"
    by (metis commutes_with_composition induced_Fiber_simp
        natural.commutes_with_composition representant_exists
        source.composition_closed)
next
  show "induced (Class \<one>) = \<one>'"
    by (simp add: commutes_with_unit)
qed

text \<open>p 61, ll 9, 26\<close>
sublocale natural: Monoid_epimorphism Class M "(\<cdot>)" \<one> "M / E(\<eta>)" "([\<cdot>])" "Class \<one>" ..

text \<open>p 61, ll 9, 26--27\<close>
sublocale induced: Monoid_monomorphism induced "M / E(\<eta>)" "([\<cdot>])" "Class \<one>" "M'" "(\<cdot>')" "\<one>'" ..

end (* Monoid_homomorphism_fundamental *)

text \<open>p 62, ll 12--13\<close>
locale group_homomorphism =
  Monoid_homomorphism \<eta> G "(\<cdot>)" \<one> G' "(\<cdot>')" "\<one>'" +
  source: Group G "(\<cdot>)" \<one> + target: Group G' "(\<cdot>')" "\<one>'"
  for \<eta> and G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
    and G' and composition' (infixl \<open>\<cdot>''\<close> 70) and unit' (\<open>\<one>''\<close>)
begin

text \<open>p 62, l 13\<close>
sublocale image: Subgroup "\<eta> ` G" G' "(\<cdot>')" "\<one>'"
  using invertible_image_lemma by unfold_locales auto

text \<open>p 62, ll 13--14\<close>
definition "Ker = \<eta> -` {\<one>'} \<inter> G"

text \<open>p 62, ll 13--14\<close>
lemma Ker_equality:
  "Ker = {a | a. a \<in> G \<and> \<eta> a = \<one>'}"
  unfolding Ker_def by auto

text \<open>p 62, ll 13--14\<close>
lemma Ker_closed [intro, simp]:
  "a \<in> Ker \<Longrightarrow> a \<in> G"
  unfolding Ker_def by simp

text \<open>p 62, ll 13--14\<close>
lemma Ker_image [intro]: (* loops as a simprule *)
  "a \<in> Ker \<Longrightarrow> \<eta> a = \<one>'"
  unfolding Ker_def by simp

text \<open>p 62, ll 13--14\<close>
lemma Ker_memI [intro]: (* loops as a simprule *)
  "\<lbrakk> \<eta> a = \<one>'; a \<in> G \<rbrakk> \<Longrightarrow> a \<in> Ker"
  unfolding Ker_def by simp

text \<open>p 62, ll 15--16\<close>
sublocale kernel: normal_subgroup Ker G
proof -
  interpret kernel: Submonoid Ker G
    unfolding Ker_def by unfold_locales (auto simp: commutes_with_composition commutes_with_unit)
  interpret kernel: Subgroup Ker G
    by unfold_locales (force intro: source.invertible_right_inverse simp: Ker_image invertible_commutes_with_inverse)
  show "normal_subgroup Ker G (\<cdot>) \<one>"
    apply unfold_locales
    unfolding Ker_def
    by (auto simp: commutes_with_composition invertible_image_lemma(2))
qed

text \<open>p 62, ll 17--20\<close>
theorem injective_iff_kernel_unit:
  "inj_on \<eta> G \<longleftrightarrow> Ker = {\<one>}"
proof (rule Not_eq_iff [THEN iffD1, OF iffI])
  assume "Ker \<noteq> {\<one>}"
  then obtain b where b: "b \<in> Ker" "b \<noteq> \<one>" by blast
  then have "\<eta> b = \<eta> \<one>" by (simp add: Ker_image)
  with b show "\<not> inj_on \<eta> G"  by (meson inj_onD kernel.sub source.unit_closed)
next
  assume "\<not> inj_on \<eta> G"
  then obtain a b where "a \<noteq> b" and ab: "a \<in> G" "b \<in> G" "\<eta> a = \<eta> b" by (meson inj_onI)
  then have "inverse a \<cdot> b \<noteq> \<one>" "\<eta> (inverse a \<cdot> b) = \<one>'"
    using ab source.invertible_right_inverse2
    by force (metis ab commutes_with_composition invertible_image_lemma(2) source.invertible source.invertible_inverse_closed)
  then have "inverse a \<cdot> b \<in> Ker" using Ker_memI ab by blast
  then show "Ker \<noteq> {\<one>}" using \<open>inverse a \<cdot> b \<noteq> \<one>\<close> by blast
qed

end (* group_homomorphism *)

text \<open>p 62, l 24\<close>
locale group_epimorphism = group_homomorphism + Monoid_epimorphism \<eta> G "(\<cdot>)" \<one> G' "(\<cdot>')" "\<one>'"

text \<open>p 62, l 21\<close>
locale normal_subgroup_in_kernel =
  group_homomorphism + contained: normal_subgroup L G "(\<cdot>)" \<one> for L +
  assumes subset: "L \<subseteq> Ker"
begin

text \<open>p 62, l 21\<close>
notation contained.quotient_composition (infixl \<open>[\<cdot>]\<close> 70)

text \<open>"homomorphism onto $G/L$"\<close>
text \<open>p 62, ll 23--24\<close>
sublocale natural: group_epimorphism contained.Class G "(\<cdot>)" \<one> "contained.Factor_Group" "([\<cdot>])" "contained.Class \<one>" ..

text \<open>p 62, ll 25--26\<close>
theorem left_coset_equality:
  assumes eq: "a \<cdot>| L = b \<cdot>| L" and [simp]: "a \<in> G" and b: "b \<in> G"
  shows "\<eta> a = \<eta> b"
proof -
  obtain l where l: "b = a \<cdot> l" "l \<in> L"
    by (metis b contained.Class_is_Left_Coset contained.Class_self eq kernel.Left_Coset_memE)
  then have "\<eta> a = \<eta> a \<cdot>' \<eta> l" using Ker_image Monoid_homomorphism.commutes_with_composition subset by auto
  also have "\<dots> = \<eta> b" by (simp add: commutes_with_composition l)
  finally show ?thesis .
qed

text \<open>$\bar{\eta}$\<close>
text \<open>p 62, ll 26--27\<close>
definition "induced = (\<lambda>A \<in> contained.Factor_Group. THE b. \<exists>a \<in> G. a \<cdot>| L = A \<and> b = \<eta> a)"

text \<open>p 62, ll 26--27\<close>
lemma induced_closed [intro, simp]:
  assumes [simp]: "A \<in> contained.Factor_Group" shows "induced A \<in> G'"
proof -
  obtain a where a: "a \<in> G" "a \<cdot>| L = A" using contained.Class_is_Left_Coset contained.Partition_def assms by auto
  have "(THE b. \<exists>a \<in> G. a \<cdot>| L = A \<and> b = \<eta> a) \<in> G'"
    apply (rule theI2)
    using a by (auto intro: left_coset_equality)
  then show ?thesis unfolding induced_def by simp
qed

text \<open>p 62, ll 26--27\<close>
lemma induced_undefined [intro, simp]:
  "A \<notin> contained.Factor_Group \<Longrightarrow> induced A = undefined"
  unfolding induced_def by simp

text \<open>p 62, ll 26--27\<close>
theorem induced_left_coset_closed [intro, simp]:
  "a \<in> G \<Longrightarrow> induced (a \<cdot>| L) \<in> G'"
  using contained.Class_is_Left_Coset contained.Class_in_Partition by auto 

text \<open>p 62, ll 26--27\<close>
theorem induced_left_coset_equality [simp]:
  assumes [simp]: "a \<in> G" shows "induced (a \<cdot>| L) = \<eta> a"
proof -
  have "(THE b. \<exists>a' \<in> G. a' \<cdot>| L = a \<cdot>| L \<and> b = \<eta> a') = \<eta> a"
    by (rule the_equality) (auto intro: left_coset_equality)
  then show ?thesis unfolding induced_def
    using contained.Class_is_Left_Coset contained.Class_in_Partition by auto 
qed

text \<open>p 62, l 27\<close>
theorem induced_Left_Coset_commutes_with_composition [simp]:
  "\<lbrakk> a \<in> G; b \<in> G \<rbrakk> \<Longrightarrow> induced ((a \<cdot>| L) [\<cdot>] (b \<cdot>| L)) = induced (a \<cdot>| L) \<cdot>' induced (b \<cdot>| L)"
  by (simp add: commutes_with_composition)

text \<open>p 62, ll 27--28\<close>
theorem induced_group_homomorphism:
  "group_homomorphism induced contained.Factor_Group ([\<cdot>]) (contained.Class \<one>) G' (\<cdot>') \<one>'"
  apply unfold_locales
    apply (auto elim!: contained.Left_CosetE simp: commutes_with_composition commutes_with_unit)
  using contained.factor_unit induced_left_coset_equality apply (fastforce simp: contained.Class_unit_normal_subgroup)
  done

text \<open>p 62, l 28\<close>
sublocale induced: group_homomorphism induced "contained.Factor_Group" "([\<cdot>])" "contained.Class \<one>" G' "(\<cdot>')" "\<one>'"
  by (fact induced_group_homomorphism)

text \<open>p 62, ll 28--29\<close>
theorem factorization_lemma: "a \<in> G \<Longrightarrow> compose G induced contained.Class a = \<eta> a"
  unfolding compose_def by (simp add: contained.Class_is_Left_Coset)

text \<open>p 62, ll 29--30\<close>
theorem factorization [simp]: "compose G induced contained.Class = \<eta>"
  by rule (simp add: compose_def contained.Class_is_Left_Coset map_undefined)

text \<open>
  Jacobson does not state the uniqueness of @{term induced} explicitly but he uses it later,
  for rings, on p 107.
\<close>
text \<open>p 62, l 30\<close>
theorem uniqueness:
  assumes map: "\<beta> \<in> contained.Factor_Group \<rightarrow>\<^sub>E G'"
    and factorization: "compose G \<beta> contained.Class = \<eta>"
  shows "\<beta> = induced"
proof
  fix A
  show "\<beta> A = induced A"
  proof (cases "A \<in> contained.Factor_Group")
    case True
    then obtain a where [simp]: "A = contained.Class a" "a \<in> G"
      by (meson contained.representant_exists)
    then have "\<beta> (contained.Class a) = \<eta> a" by (metis compose_eq factorization)
    also have "\<dots> = induced (contained.Class a)" by (simp add: contained.Class_is_Left_Coset)
    finally show ?thesis by simp
  qed (simp add: induced_def PiE_arb [OF map])
qed

text \<open>p 62, l 31\<close>
theorem induced_image:
  "induced ` contained.Factor_Group = \<eta> ` G"
  by (metis factorization contained.natural.surjective surj_compose)

text \<open>p 62, l 33\<close>
interpretation L: normal_subgroup L Ker
  by unfold_locales (auto simp: subset, metis kernel.sub kernel.subgroup_inverse_equality contained.normal)

text \<open>p 62, ll 31--33\<close>
theorem induced_kernel:
  "induced.Ker = Ker / L.Congruence" (* Ker // L is apparently not the right thing *)
proof -
  have "induced.Ker = { a \<cdot>| L | a. a \<in> G \<and> a \<in> Ker }"
    unfolding induced.Ker_equality
    by simp (metis (opaque_lifting) contained.Class_is_Left_Coset Ker_image Ker_memI
        induced_left_coset_equality contained.Class_in_Partition contained.representant_exists)
  also have "\<dots> = Ker / L.Congruence"
    using L.Class_is_Left_Coset L.Class_in_Partition
    by auto (metis L.Class_is_Left_Coset L.representant_exists kernel.sub)
  finally show ?thesis .
qed

text \<open>p 62, ll 34--35\<close>
theorem induced_inj_on:
  "inj_on induced contained.Factor_Group \<longleftrightarrow> L = Ker"
proof -
  have "L = Ker"
    if "L.Partition = {L}"
    using that L.Class_Union L.natural.map_closed by auto
  moreover have "L.Partition \<subseteq> {Ker}" if "L = Ker"
    by (metis L.ClassD L.Class_eq L.Normal_def L.representant_exists
        contained.sub_unit_closed insert_iff subsetI that)
  moreover have "{Ker} \<subseteq> L.Partition" if "L = Ker"
    using that L.Normal_def L.quotient.unit_closed by auto
  ultimately show ?thesis
    by (auto simp add: induced.injective_iff_kernel_unit induced_kernel contained.Class_unit_normal_subgroup)
qed

end (* normal_subgroup_in_kernel *)

text \<open>Fundamental Theorem of Homomorphisms of Groups\<close>

text \<open>p 63, l 1\<close>
locale group_homomorphism_fundamental = group_homomorphism begin

text \<open>p 63, l 1\<close>
notation kernel.quotient_composition (infixl \<open>[\<cdot>]\<close> 70)

text \<open>p 63, l 1\<close>
sublocale normal_subgroup_in_kernel where L = Ker by unfold_locales rule

text \<open>p 62, ll 36--37; p 63, l 1\<close>
text \<open>
  @{term induced} denotes Jacobson's $\bar{\eta}$.  We have the commutativity of the diagram, where
  @{term induced} is unique: @{thm [display] factorization} @{thm [display] uniqueness}
\<close>

end (* group_homomorphism_fundamental *)

text \<open>p 63, l 5\<close>
locale group_isomorphism = group_homomorphism + bijective_map \<eta> G G' begin

text \<open>p 63, l 5\<close>
sublocale Monoid_isomorphism \<eta> G "(\<cdot>)" \<one> G' "(\<cdot>')" "\<one>'" 
  by unfold_locales (auto simp: commutes_with_composition)

text \<open>p 63, l 6\<close>
lemma inverse_group_isomorphism:
  "group_isomorphism (restrict (inv_into G \<eta>) G') G' (\<cdot>') \<one>' G (\<cdot>) \<one>"
proof
qed (use commutes_with_composition commutes_with_unit bij_betw_inverse surjective in auto)

end (* group_isomorphism *)

text \<open>p 63, l 6\<close>
definition isomorphic_as_groups (infixl \<open>\<cong>\<^sub>G\<close> 50)
  where "\<G> \<cong>\<^sub>G \<G>' \<longleftrightarrow> (let (G, composition, unit) = \<G>; (G', composition', unit') = \<G>' in
  (\<exists>\<eta>. group_isomorphism \<eta> G composition unit G' composition' unit'))"

text \<open>p 63, l 6\<close>
lemma isomorphic_as_groups_symmetric:
  "(G, composition, unit) \<cong>\<^sub>G (G', composition', unit') \<Longrightarrow> (G', composition', unit') \<cong>\<^sub>G (G, composition, unit)"
  by (simp add: isomorphic_as_groups_def) (meson group_isomorphism.inverse_group_isomorphism)

lemma isomorphic_as_groups_transitive:
  assumes "(G, composition, unit) \<cong>\<^sub>G (G', composition', unit')"
    and "(G', composition', unit') \<cong>\<^sub>G (G'', composition'', unit'')"
  shows "(G, composition, unit) \<cong>\<^sub>G (G'', composition'', unit'')"
proof -
  obtain \<eta> where first:
    "group_isomorphism \<eta> G composition unit G' composition' unit'"
    using assms(1) unfolding isomorphic_as_groups_def by auto
  obtain \<theta> where second:
    "group_isomorphism \<theta> G' composition' unit' G'' composition'' unit''"
    using assms(2) unfolding isomorphic_as_groups_def by auto
  interpret first: group_isomorphism \<eta> G composition unit G' composition' unit' by fact
  interpret second: group_isomorphism \<theta> G' composition' unit' G'' composition'' unit'' by fact
  have composite:
    "group_isomorphism (restrict (\<theta> \<circ> \<eta>) G)
      G composition unit G'' composition'' unit''"
  proof
    show "restrict (\<theta> \<circ> \<eta>) G \<in> G \<rightarrow>\<^sub>E G''"
      using first.graph second.graph by auto
    show "restrict (\<theta> \<circ> \<eta>) G (composition x y) =
          composition'' (restrict (\<theta> \<circ> \<eta>) G x)
            (restrict (\<theta> \<circ> \<eta>) G y)"
      if "x \<in> G" "y \<in> G" for x y
      using that first.commutes_with_composition second.commutes_with_composition
        first.source.composition_closed by auto
    show "restrict (\<theta> \<circ> \<eta>) G unit = unit''"
      using first.commutes_with_unit second.commutes_with_unit first.source.unit_closed by simp
    have "bij_betw (\<theta> \<circ> \<eta>) G G''"
      using first.bijective second.bijective by (rule bij_betw_trans)
    then show "bij_betw (restrict (\<theta> \<circ> \<eta>) G) G G''"
      by (simp add: bij_betw_restrict_eq)
  qed
  show ?thesis unfolding isomorphic_as_groups_def using composite by auto
qed

text \<open>p 63, l 1\<close>
sublocale group_isomorphism \<subseteq> group_epimorphism ..

text \<open>p 63, l 1\<close>
locale group_epimorphism_fundamental = group_homomorphism_fundamental + group_epimorphism begin

text \<open>p 63, ll 1--2\<close>
interpretation image: group_homomorphism induced "kernel.Factor_Group" "([\<cdot>])" "kernel.Class \<one>" "(\<eta> ` G)" "(\<cdot>')" "\<one>'"
  by (simp add: surjective group_homomorphism_fundamental.intro induced_group_homomorphism)

text \<open>p 63, ll 1--2\<close>
sublocale image: group_isomorphism induced "kernel.Factor_Group" "([\<cdot>])" "kernel.Class \<one>" "(\<eta> ` G)" "(\<cdot>')" "\<one>'"
  using induced_group_homomorphism
  by unfold_locales (auto simp: bij_betw_def induced_image induced_inj_on induced.commutes_with_composition)

end (* group_epimorphism_fundamental *)

context group_homomorphism begin

text \<open>p 63, ll 5--7\<close>
theorem image_isomorphic_to_factor_group:
  "\<exists>K composition unit. normal_subgroup K G (\<cdot>) \<one> \<and> (\<eta> ` G, (\<cdot>'), \<one>') \<cong>\<^sub>G (G / (normal_subgroup.Congruence K G (\<cdot>) \<one>), composition, unit)"
proof -
  interpret image: group_epimorphism_fundamental where G' = "\<eta> ` G"
    by unfold_locales (auto simp: commutes_with_composition)
  have "group_isomorphism image.induced kernel.Factor_Group ([\<cdot>]) (kernel.Class \<one>) (\<eta> ` G) (\<cdot>') \<one>'" ..
  then have "(\<eta> ` G, (\<cdot>'), \<one>') \<cong>\<^sub>G (kernel.Factor_Group, ([\<cdot>]), kernel.Class \<one>)"
    by (simp add: isomorphic_as_groups_def) (meson group_isomorphism.inverse_group_isomorphism)
  moreover have "normal_subgroup Ker G (\<cdot>) \<one>" ..
  ultimately show ?thesis by blast
qed

text \<open>p 65\<close>
text \<open>The First Isomorphism Theorem states that for any group homomorphism @{text "\<eta> : G \<rightarrow> G'"},
  the quotient @{text "G/ker(\<eta>)"} is isomorphic to the image @{text "im(\<eta>)"}. The isomorphism is
  given by the induced map @{text "gK \<mapsto> \<eta>(g)"}, which is well-defined because elements in the same
  coset of @{text "ker(\<eta>)"} have the same image under @{text "\<eta>"}.\<close>

theorem first_isomorphism:
  "(kernel.Factor_Group, kernel.quotient_composition, kernel.Class \<one>) \<cong>\<^sub>G (\<eta> ` G, (\<cdot>'), \<one>')"
proof -
  \<comment> \<open>Restrict the codomain to the image to obtain a surjection.\<close>
  interpret image: group_epimorphism_fundamental \<eta> G "(\<cdot>)" \<one> "\<eta> ` G" "(\<cdot>')" "\<one>'"
    by unfold_locales (auto simp: commutes_with_composition)
  \<comment> \<open>The induced map is an isomorphism from @{text "G/ker(\<eta>)"} to @{text "im(\<eta>)"}.\<close>
  have "group_isomorphism image.induced kernel.Factor_Group kernel.quotient_composition
    (kernel.Class \<one>) (\<eta> ` G) (\<cdot>') \<one>'" ..
  then show ?thesis
    by (auto simp: isomorphic_as_groups_def)
qed

end (* group_homomorphism *)

subsection \<open>Correspondence Theorem and Third Isomorphism Theorem\<close>
text \<open>p 65\<close>

text \<open>The proofs in this section, in their initial form, were generated by Claude Opus 4.6
through Dominic Mulligan's Isabelle Assistant. Then simplified and tidied by LCP.\<close>

text \<open>
  Let @{term K} be a normal subgroup of @{term G} and @{term H} a subgroup of @{term G} containing
  @{term K}. Then @{text "H/K"} is a subgroup of @{text "G/K"}, the map @{text "H \<mapsto> H/K"} is a
  bijection between subgroups of @{term G} containing @{term K} and subgroups of @{text "G/K"},
  @{term H} is normal in @{term G} if and only if @{text "H/K"} is normal in @{text "G/K"}, and
  @{text "G/H \<cong> (G/K)/(H/K)"}.
\<close>

locale normal_subgroup_in_subgroup =
  K: normal_subgroup K G "(\<cdot>)" \<one> +
  H: subgroup_of_group H G "(\<cdot>)" \<one>
  for K and H and G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>) +
  assumes K_contained: "K \<subseteq> H"
begin

interpretation K_subgroup_H: Subgroup K H "(\<cdot>)" \<one>
proof qed (use K_contained in auto)

text \<open>@{term K} is a normal subgroup of @{term H}.\<close>
interpretation K_in_H: normal_subgroup K H "(\<cdot>)" \<one>
proof
  show "\<And>g k. \<lbrakk>g \<in> H; k \<in> K\<rbrakk> \<Longrightarrow> H.sub.inverse g \<cdot> k \<cdot> g \<in> K"
    by (metis K.normal H.sub H.subgroup_inverse_equality)
qed

notation K.quotient_composition (infixl \<open>[\<cdot>]\<close> 70)

text \<open>@{text "H/K"} as a subset of @{text "G/K"}, defined as the image of @{term H} under the
  canonical projection.\<close>

definition "Fract_H_K = K.Class ` H"

text \<open>One might expect the quotient $H/K$ to be @{term "K.Factor_Group"} with @{term H} in place of
  @{term G}. However, @{term K.Factor_Group} always forms the congruence of @{term K}
  relative to @{term G} (not @{term H}), so substituting @{term H} for the carrier would give
  @{term "Equivalence.Partition H K.Congruence"}. Since @{term K.Congruence} is an equivalence on
  @{term G} rather than @{term H}, the conditional defining equation of @{const Equivalence.Partition}
  cannot be applied, leaving the term opaque.

  The correct formalisation of $H/K$ is @{term K_in_H.Partition}, the partition of @{term H} under
  @{term K_in_H.Congruence}---the congruence of @{term K} viewed as a normal subgroup of @{term H}.
  The proof that @{term Fract_H_K} equals @{term K_in_H.Partition} follows from the fact that @{term K.Class}
  and @{term K_in_H.Class} agree on elements of @{term H}: both map $h \in H$ to the left coset
  $hK$, by @{thm [source] K.Class_is_Left_Coset} and @{thm [source] K_in_H.Class_is_Left_Coset}.\<close>

lemma H_Class_eq: "h \<in> H \<Longrightarrow> K_in_H.Class h = K.Class h"
  using K.Left_Coset_Class_unit K_in_H.Left_Coset_Class_unit by force

lemma Fract_H_K_is_quotient: "Fract_H_K = K_in_H.Partition"
  by (auto simp: Fract_H_K_def K_in_H.Partition_def H_Class_eq)

lemma Fract_H_K_subset: "Fract_H_K \<subseteq> K.Factor_Group"
  unfolding Fract_H_K_def by blast

lemma Class_H_closed [intro, simp]:
  "h \<in> H \<Longrightarrow> K.Class h \<in> Fract_H_K"
  unfolding Fract_H_K_def by auto

lemma Fract_H_K_unit_closed [intro, simp]:
  "K.Class \<one> \<in> Fract_H_K"
  using H.sub_unit_closed by auto

lemma Fract_H_K_memE [elim]:
  "\<lbrakk> A \<in> Fract_H_K; \<And>h. \<lbrakk> h \<in> H; A = K.Class h \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding Fract_H_K_def by auto

text \<open>@{text "H/K"} is a subgroup of @{text "G/K"}.\<close>

lemma Fract_H_K_into_subset_H: "h \<in> Fract_H_K \<Longrightarrow> h \<subseteq> H"
  using Fract_H_K_is_quotient K_in_H.natural.surjective by blast

theorem Fract_H_K_subgroup: "Subgroup Fract_H_K K.Factor_Group ([\<cdot>]) (K.Class \<one>)"
proof (rule K.quotient.subgroupI)
  show "Fract_H_K \<subseteq> K.Factor_Group" by (rule Fract_H_K_subset)
next
  fix A
  assume "A \<in> Fract_H_K"
  then obtain a where a: "a \<in> H" "A = K.Class a" by auto
  then show "K.quotient.invertible A"
    using K.Class_invertible H.sub by auto
  show "K.quotient.inverse A \<in> Fract_H_K"
    using a by (simp add: K.Class_commutes_with_inverse)
qed (use K.Class_commutes_with_composition in fastforce)+

sublocale Fract_H_K: subgroup_of_group Fract_H_K "K.Factor_Group" "([\<cdot>])" "K.Class \<one>"
  by (simp add: Fract_H_K_subgroup K.quotient.Group_axioms subgroup_of_group_def)

text \<open>@{term H} is normal in @{term G} if and only if $H/K$ is normal in $G/K$.\<close>
theorem normal_iff:
  "normal_subgroup H G (\<cdot>) \<one> \<longleftrightarrow> normal_subgroup Fract_H_K K.Factor_Group ([\<cdot>]) (K.Class \<one>)"
proof
  assume "normal_subgroup H G (\<cdot>) \<one>"
  then interpret H_normal: normal_subgroup H G "(\<cdot>)" \<one> .
  show "normal_subgroup Fract_H_K K.Factor_Group ([\<cdot>]) (K.Class \<one>)"
  proof 
    fix A B
    assume A: "A \<in> K.Factor_Group" and B: "B \<in> Fract_H_K"
    then obtain g h where g: "g \<in> G" "A = K.Class g"
                      and h: "h \<in> H" "B = K.Class h" 
         by (meson K.representant_exists Fract_H_K_memE)
    have "K.quotient.inverse A = K.Class (K.inverse g)"
      using g K.Class_commutes_with_inverse by auto
    then have eq: "K.quotient.inverse A [\<cdot>] B [\<cdot>] A = K.Class (K.inverse g \<cdot> h \<cdot> g)"
      using g h K.Class_commutes_with_composition by force
    have "K.inverse g \<cdot> h \<cdot> g \<in> H" using H_normal.normal g h by auto
    then show "K.quotient.inverse A [\<cdot>] B [\<cdot>] A \<in> Fract_H_K"
      unfolding eq by auto
  qed
next
  assume Fract_H_K_normal: "normal_subgroup Fract_H_K K.Factor_Group ([\<cdot>]) (K.Class \<one>)"
  then interpret Fract_H_K_normal: normal_subgroup Fract_H_K "K.Factor_Group" "([\<cdot>])" "K.Class \<one>" .
  show "normal_subgroup H G (\<cdot>) \<one>"
  proof 
    fix g h
    assume g: "g \<in> G" and h: "h \<in> H"
    then have A: "K.Class g \<in> K.Factor_Group" and B: "K.Class h \<in> Fract_H_K" by auto
    have "K.quotient.inverse (K.Class g) [\<cdot>] K.Class h [\<cdot>] K.Class g
        = K.Class (K.inverse g \<cdot> h \<cdot> g)"
      using K.Class_commutes_with_inverse K.natural.commutes_with_composition g h by auto
    with Fract_H_K_normal.normal [OF A B] 
    obtain h' where h': "h' \<in> H" "K.Class (K.inverse g \<cdot> h \<cdot> g) = K.Class h'"
      by (metis Fract_H_K_memE)
    then have "(K.inverse g \<cdot> h \<cdot> g, h') \<in> K.Congruence"
      using g h H.sub K.Class_equivalence by auto
    then obtain k where k: "k \<in> K" "K.inverse g \<cdot> h \<cdot> g = h' \<cdot> k"
      using K.CongruenceD by auto
    show "K.inverse g \<cdot> h \<cdot> g \<in> H"
      using k h' K_contained H.sub_composition_closed by auto
  qed
qed

text \<open>Third Isomorphism Theorem: @{text "G/H \<cong> (G/K)/(H/K)"}\<close>

text \<open>We assume @{term H} is normal in @{term G} and construct a surjective group homomorphism
  from @{text "G/K"} to @{text "G/H"} whose kernel is @{text "H/K"}.\<close>

theorem third_isomorphism:
  assumes H_normal: "normal_subgroup H G (\<cdot>) \<one>"
  defines "CongH \<equiv> normal_subgroup.Congruence H G (\<cdot>) \<one>"
    and "CongHK \<equiv> normal_subgroup.Congruence Fract_H_K K.Factor_Group K.quotient_composition (K.Class \<one>)"
  shows "(G / CongH,
          Monoid_congruence.quotient_composition G (\<cdot>) CongH,
          Equivalence.Class G CongH \<one>) \<cong>\<^sub>G
         (K.Factor_Group / CongHK,
          Monoid_congruence.quotient_composition K.Factor_Group K.quotient_composition CongHK,
          Equivalence.Class K.Factor_Group CongHK (K.Class \<one>))"
proof -
  interpret Hn: normal_subgroup H G "(\<cdot>)" \<one> 
    by (rule H_normal)

  \<comment> \<open>The canonical map, sending \<open>K.Class g\<close> to \<open>Hn.Class g\<close>; the
      description operator is discharged by well-definedness below.\<close>
  define \<phi> where "\<phi> = (\<lambda>A \<in> K.Factor_Group. THE B. \<exists>g \<in> G. A = K.Class g \<and> B = Hn.Class g)"

  have \<phi>_eq: "\<phi> (K.Class g) = Hn.Class g" if g: "g \<in> G" for g
    proof -
    have unfold: "\<phi> (K.Class g) = (THE B. \<exists>g'\<in>G. K.Class g = K.Class g' \<and> B = Hn.Class g')"
      unfolding \<phi>_def using g by simp
    \<comment> \<open>Well defined because \<open>K \<subseteq> H\<close>: elements in one \<open>K\<close>-coset lie in one
        \<open>H\<close>-coset.\<close>
    have well_def: "(THE B. \<exists>g'\<in>G. K.Class g = K.Class g' \<and> B = Hn.Class g') = Hn.Class g"
    proof (rule the_equality)
      fix B assume "\<exists>g'\<in>G. K.Class g = K.Class g' \<and> B = Hn.Class g'"
      with g obtain g' k where g': "g' \<in> G" and eq: "K.Class g = K.Class g'" and B: "B = Hn.Class g'"
        and "(g, g') \<in> K.Congruence" and "g = g' \<cdot> k" and "k \<in> K"
        by (meson K.CongruenceD K.Class_equivalence)
      then have "(g, g') \<in> Hn.Congruence"
        using g g' K_contained by (auto intro: Hn.CongruenceI)
      with B show "B = Hn.Class g"
        using Hn.Class_eq by presburger
    qed (use g in blast)
    show "\<phi> (K.Class g) = Hn.Class g"
      by (simp add: unfold well_def)
  qed

  interpret gh: group_homomorphism \<phi> "K.Factor_Group" "([\<cdot>])" "K.Class \<one>" "Hn.Factor_Group" "Hn.quotient_composition" "Hn.Class \<one>"
  proof 
    show "\<phi> \<in> K.Partition \<rightarrow>\<^sub>E Hn.Partition"
    proof (rule PiE_I)
      fix A assume "A \<in> K.Partition"
      then show "\<phi> A \<in> Hn.Partition"
        by (metis Hn.natural.map_closed \<phi>_eq K.representant_exists)
    qed (auto simp: \<phi>_def)
  next
    fix A B assume A: "A \<in> K.Partition" and B: "B \<in> K.Partition"
    then obtain a b where a: "a \<in> G" and A_eq: "A = K.Class a" 
      and b: "b \<in> G" and B_eq: "B = K.Class b"
        using K.representant_exists by meson
      have "\<phi> (A [\<cdot>] B) = \<phi> (K.Class (a \<cdot> b))"
        by (simp add: A_eq B_eq a b K.Class_commutes_with_composition)
      also have "\<dots> = Hn.Class (a \<cdot> b)"
        using a b by (simp add: \<phi>_eq)
      also have "\<dots> = Hn.quotient_composition (\<phi> A) (\<phi> B)"
        using A_eq B_eq Hn.natural.commutes_with_composition \<phi>_eq a b by presburger
      finally show "\<phi> (A [\<cdot>] B) = Hn.quotient_composition (\<phi> A) (\<phi> B)" .
  next
    show "\<phi> (K.Class \<one>) = Hn.Class \<one>"
      by (simp add: \<phi>_eq)
  qed

  have \<phi>_surj: "\<phi> ` K.Factor_Group = Hn.Factor_Group"
    using Hn.representant_exists \<phi>_eq by blast

  have \<phi>_ker: "gh.Ker = Fract_H_K"
  proof (intro equalityI subsetI)
    fix A assume A_ker: "A \<in> gh.Ker"
    then have "A \<in> K.Factor_Group" and \<phi>_A: "\<phi> A = Hn.Class \<one>"
      by (auto simp: gh.Ker_def)
    then obtain g where g: "g \<in> G" and A_eq: "A = K.Class g"
      by (meson K.representant_exists)
    then have "(g, \<one>) \<in> Hn.Congruence"
      using g Hn.Class_equivalence \<phi>_A \<phi>_eq by force
    then show "A \<in> Fract_H_K"
      using A_eq Hn.CongruenceD by blast
  next
    fix A assume "A \<in> Fract_H_K"
    then obtain h where h: "h \<in> H" and A_eq: "A = K.Class h"
      by auto
    then have "(h, \<one>) \<in> Hn.Congruence"
      using Hn.Normal_def h by blast
    then have "\<phi> A = Hn.Class \<one>"
      by (simp add: A_eq Hn.Class_eq \<phi>_eq h)
    then show "A \<in> gh.Ker"
      using \<open>A \<in> Fract_H_K\<close> by blast
  qed
  show ?thesis
    unfolding CongHK_def CongH_def
    by (metis \<phi>_ker \<phi>_surj gh.first_isomorphism isomorphic_as_groups_symmetric)
qed

end (* normal_subgroup_in_subgroup *)

text \<open>
  The product of a subgroup and a normal subgroup is again a subgroup.  We keep
  the construction set-based, in keeping with the rest of this development,
  and package its closure facts in a locale so that later isomorphism theorems
  can use the product as an ambient group in its own right.
\<close>
locale normal_subgroup_product =
  K: normal_subgroup K G "(\<cdot>)" \<one> +
  H: subgroup_of_group H G "(\<cdot>)" \<one>
  for K and H and G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
begin

definition HK where "HK \<equiv> (case_prod(\<cdot>)) ` (H \<times> K)"

lemma HK_memI:
  "\<lbrakk>h \<in> H; k \<in> K\<rbrakk> \<Longrightarrow> h \<cdot> k \<in> HK"
  unfolding HK_def by blast

lemma HK_memE:
  assumes "x \<in> HK"
  obtains h k where "h \<in> H" "k \<in> K" "x = h \<cdot> k"
proof -
  from assms obtain p where p: "p \<in> H \<times> K" "x = case_prod (\<cdot>) p"
    unfolding HK_def by blast
  obtain h k where "p = (h,k)" by (cases p)
  then have "h \<in> H" "k \<in> K" "x = h \<cdot> k"
    using p by simp_all
  then show thesis by (rule that)
qed

lemma HK_eq_KH: "HK = (case_prod(\<cdot>)) ` (K \<times> H)"
  using H.subset HK_def K.set_prod_commute by presburger

interpretation HK_mon: Monoid HK
proof
  fix a b
  assume "a \<in> HK" and "b \<in> HK"
  then have "\<exists>hb kb. h \<cdot> k \<cdot> (ha \<cdot> ka) = hb \<cdot> kb \<and> hb \<in> H \<and> kb \<in> K"
    if "h \<in> H" "k \<in> K" "ha \<in> H" "ka \<in> K" for h ha k ka
  proof -
    have hG: "h \<in> G" and haG: "ha \<in> G" using that H.sub by auto
    have kG: "k \<in> G" and kaG: "ka \<in> G" using that K.sub by auto
    have "k \<cdot> ha \<in> (case_prod(\<cdot>)) ` (K \<times> H)"
      using that by auto
    then have "k \<cdot> ha \<in> HK"
      using HK_eq_KH by simp
    then obtain h' k' where hk': "k \<cdot> ha = h' \<cdot> k'" "h' \<in> H" "k' \<in> K"
      by (auto simp: HK_def)
    have "h \<cdot> k \<cdot> (ha \<cdot> ka) = h \<cdot> (k \<cdot> ha) \<cdot> ka"
      by (simp add: K.associative hG haG kG kaG)
    also have "\<dots> = (h \<cdot> h') \<cdot> (k' \<cdot> ka)"
      using \<open>k \<cdot> ha = h' \<cdot> k'\<close> by (simp add: K.associative hG hk' kaG)
    finally have eq: "h \<cdot> k \<cdot> (ha \<cdot> ka) = (h \<cdot> h') \<cdot> (k' \<cdot> ka)" .
    then show ?thesis
      using hk' \<open>h \<in> H\<close> \<open>ka \<in> K\<close> by blast
  qed
  then show "a \<cdot> b \<in> HK"
    using HK_def \<open>a \<in> HK\<close> \<open>b \<in> HK\<close> by force
qed (force simp: HK_def)+

interpretation HK_sub: Subgroup HK G
proof
  fix a assume a: "a \<in> HK"
  then show "\<And>b. b \<in> HK \<Longrightarrow> a \<cdot> b \<in> HK"
    by blast
  obtain h k where hk: "h \<in> H" "k \<in> K" "a = k\<cdot>h"
    using HK_eq_KH a by auto
  define a' where "a' \<equiv> H.sub.inverse h \<cdot> K.sub.inverse k"
  have "a' \<in> HK"
    using HK_def a'_def hk by auto
  have "a \<cdot> a' = \<one>"
    using hk unfolding a'_def
    by (metis H.sub H.subgroup_inverse_equality K.composition_closed K.inverse_composition_commute
        K.invertible K.invertible_right_inverse K.sub K.subgroup_inverse_equality)
  moreover have "a' \<cdot> a = \<one>"
    unfolding \<open>a = k\<cdot>h\<close> a'_def
    by (metis H.sub H.subgroup_inverse_equality K.composition_closed K.inverse_composition_commute
        K.invertible K.invertible_left_inverse K.sub K.subgroup_inverse_equality hk)
  moreover have "a' \<in> HK"
    using hk by (auto simp: a'_def HK_def)
  ultimately show "Monoid.invertible HK (\<cdot>) \<one> a"
    using HK_mon.invertibleI by blast
qed (force simp: HK_def)+

lemma HK_subgroup: "Subgroup HK G (\<cdot>) \<one>"
  ..

lemma H_subset_HK: "H \<subseteq> HK"
  unfolding HK_def
  using K.sub_unit_closed H.sub by force

lemma K_subset_HK: "K \<subseteq> HK"
  unfolding HK_def
  using H.sub_unit_closed K.sub by force

end (* normal_subgroup_product *)

locale second_iso_theorem = normal_subgroup_product K H G "(\<cdot>)" \<one>
  for K and H and G and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
begin

interpretation HIntK_Mon: Monoid "H \<inter> K" 
proof qed auto

interpretation HIntKn: normal_subgroup "H \<inter> K" H
proof
  fix u :: 'a
  assume "u \<in> H \<inter> K"
  then have uH: "u \<in> H" and uK: "u \<in> K" by auto
  then have inv_H: "H.sub.inverse u \<in> H"
    using H.sub.invertible H.sub.invertible_inverse_closed by auto
  have "H.sub.inverse u = K.sub.inverse u"
    by (metis H.subgroup_inverse_equality K.subgroup_inverse_equality uH uK)
  then show "Monoid.invertible (H \<inter> K) (\<cdot>) \<one> u"
    using inv_H uK by force
  fix g 
  assume "g \<in> H" 
  then show "H.sub.inverse g \<cdot> u \<cdot> g \<in> H \<inter> K"
    by (metis H.sub H.sub.invertible H.sub_composition_closed H.subgroup_inverse_equality
        H.submonoid_inverse_closed Int_iff K.normal uH uK)
qed auto

text \<open>Defining the quotient groups as sets of equivalence classes\<close>
definition "Fract_HK_K \<equiv> K.Class ` HK"
definition "Fract_H_HIntK \<equiv> HIntKn.Class ` H"
definition \<phi> where "\<phi> \<equiv> (\<lambda>A \<in> Fract_HK_K. THE B. \<exists>g \<in> HK. A = K.Class g \<and> B = HIntKn.Class g)"


theorem second_isomorphism: 
  shows "(Fract_HK_K, K.quotient_composition, K.Class \<one>) \<cong>\<^sub>G
         (Fract_H_HIntK, HIntKn.quotient_composition, HIntKn.Class \<one>)"
proof -
  define \<eta> where "\<eta> = (\<lambda>h \<in> H. K.Class h)"

  interpret gh: group_homomorphism \<eta> H "(\<cdot>)" \<one> "K.Factor_Group" K.quotient_composition "K.Class \<one>"
  proof
    show "\<eta> \<in> H \<rightarrow>\<^sub>E K.Partition"
      by (simp add: \<eta>_def)
  next
    fix x y assume xy: "x \<in> H" "y \<in> H"
    then show "\<eta> (x \<cdot> y) = K.quotient_composition (\<eta> x) (\<eta> y)"
      by (simp add: K.natural.commutes_with_composition \<eta>_def)
  next
    show "\<eta> \<one> = K.Class \<one>"
      unfolding \<eta>_def using H.sub_unit_closed by simp
  qed

  have image_eq: "\<eta> ` H = Fract_HK_K"
  proof (intro equalityI subsetI)
    fix A assume "A \<in> \<eta> ` H"
    then obtain h where h: "h \<in> H" "A = \<eta> h" by auto
    then have "A = K.Class h" unfolding \<eta>_def by simp
    moreover have "h \<in> HK"
      unfolding HK_def using h(1) K.sub_unit_closed H.sub
      by (force intro: image_eqI[where x="(h, \<one>)"])
    ultimately show "A \<in> Fract_HK_K"
      unfolding Fract_HK_K_def by auto
  next
    fix A assume "A \<in> Fract_HK_K"
    then obtain a where a: "a \<in> HK" "A = K.Class a"
      unfolding Fract_HK_K_def by auto
    then obtain h k where hk: "h \<in> H" "k \<in> K" "a = h \<cdot> k"
      unfolding HK_def by auto
    have "K.Class a = K.Class h"
      using hk H.sub K.sub
      by (meson K.Class_eq K.CongruenceI K.composition_closed)
    then have "A = \<eta> h" using a hk unfolding \<eta>_def by simp
    then show "A \<in> \<eta> ` H" using hk(1) by auto
  qed

  have ker_eq: "gh.Ker = H \<inter> K"
  proof (intro equalityI subsetI)
    fix h assume "h \<in> gh.Ker"
    then have hH: "h \<in> H" and "\<eta> h = K.Class \<one>"
      using \<open>h \<in> gh.Ker\<close> gh.Ker_image by blast+
    then have "K.Class h = K.Class \<one>"
      unfolding \<eta>_def by simp
    then have "(h, \<one>) \<in> K.Congruence"
      using hH H.sub K.Class_equivalence by simp
    then have "h \<in> K"
      using K.CongruenceD by blast
    with hH show "h \<in> H \<inter> K" by auto
  next
    fix h assume "h \<in> H \<inter> K"
    then have hH: "h \<in> H" and hK: "h \<in> K" by auto
    have "\<eta> h = K.Class h" unfolding \<eta>_def using hH by simp
    also have "\<dots> = K.Class \<one>"
      by (metis K.Class_eq K.CongruenceI K.left_unit K.sub K.unit_closed hK)
    finally show "h \<in> gh.Ker" 
      using hH by blast
  qed

  \<comment> \<open>The kernel's congruence and quotient agree with HIntKn's.\<close>
  \<comment> \<open>Apply the first isomorphism theorem.\<close>
  have "(gh.kernel.Partition, gh.kernel.quotient_composition, gh.kernel.Class \<one>) \<cong>\<^sub>G
        (\<eta> ` H, K.quotient_composition, K.Class \<one>)"
    using gh.first_isomorphism by simp
  then have "(Fract_H_HIntK, HIntKn.quotient_composition, HIntKn.Class \<one>) \<cong>\<^sub>G
             (Fract_HK_K, K.quotient_composition, K.Class \<one>)"
    unfolding image_eq Fract_H_HIntK_def ker_eq by (simp add: HIntKn.Partition_def)
  then show ?thesis
    by (rule isomorphic_as_groups_symmetric)
qed


end (*first_iso_theorem*)

subsection \<open>Dropping from elements of a partition to representatives\<close>

text \<open>This prevents a change of type for inductive proofs that involve quotienting.\<close>

locale class_representatives =
  fixes A:: "'a set" and P and composition (infixl \<open>\<cdot>\<close> 70) and unit (\<open>\<one>\<close>)
  assumes P: "partition_on A P"
  assumes comp: "(\<cdot>) \<in> P \<rightarrow>\<^sub>E P \<rightarrow>\<^sub>E P"
  assumes unit: "\<one> \<in> P "
begin

definition the_part :: "'a \<Rightarrow> 'a set" where
  "the_part x \<equiv> THE X. X \<in> P \<and> x \<in> X"

definition rep_comp :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "rep_comp \<equiv> \<lambda>x\<in>A. \<lambda>y\<in>A. some_elem ((the_part x) \<cdot> (the_part y))"

lemma some_elem_typing: "X \<in> P \<Longrightarrow> some_elem X \<in> A"
  by (metis P UnionI partition_on_def some_elem_nonempty)

lemma the_part_works:
  assumes "x \<in> A" shows "x \<in> the_part x" "the_part x \<in> P"
proof -
  obtain X where X: "x \<in> X" "X \<in> P"
    using P assms by (metis UnionE partition_on_def)
  moreover have "Y = X" if "x \<in> Y" "Y \<in> P" for Y
    using P X
    by (metis (no_types, lifting) IntI disjoint_def emptyE partition_on_def that)
  ultimately have "x \<in> the_part x \<and> the_part x \<in> P"
    by (metis (mono_tags, lifting) theI_unique the_part_def)
  then show "x \<in> the_part x" "the_part x \<in> P"
    by auto
qed

lemma typing: "\<lbrakk>x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> some_elem (the_part x \<cdot> the_part y) \<in> A"
  by (metis some_elem_typing PiE_E comp the_part_works(2))

lemma unit_typing: "some_elem \<one> \<in> A"
  by (simp add: some_elem_typing unit)

lemma rep_comp_typing: "rep_comp \<in> A \<rightarrow>\<^sub>E (A \<rightarrow>\<^sub>E A)"
  by (simp add: rep_comp_def typing)

lemma the_part_some_elem [simp]:
  assumes "X \<in> P"
  shows "the_part (some_elem X) = X"
proof -
  have "disjoint P"
    using P partition_on_def by blast
  moreover
  have "X \<noteq> {}"
    using assms P partition_on_def by blast
  ultimately show ?thesis
    using assms by (simp add: pairwise_disjnt_iff some_elem_nonempty the1_equality' the_part_def)
qed

lemma rep_comp: "\<lbrakk>X \<in> P; Y \<in> P\<rbrakk> \<Longrightarrow> rep_comp (some_elem X) (some_elem Y) = some_elem (X \<cdot> Y)"
  by (simp add: rep_comp_def some_elem_typing)

lemma Monoid_class_reps:
  assumes "Monoid P (\<cdot>) \<one>"
  shows "Monoid (some_elem ` P) rep_comp (some_elem \<one>)"
proof -
  interpret Monoid P
    by (simp add: assms)
  show ?thesis
  proof  qed (use rep_comp associative in auto)
qed

lemma Group_class_reps:
  assumes "Group P (\<cdot>) \<one>"
  shows "Group (some_elem ` P) rep_comp (some_elem \<one>)"
proof -
  interpret Group P
    by (simp add: assms)
  interpret Mr: Monoid "some_elem ` P" rep_comp "some_elem \<one>"
    by (simp add: Monoid_axioms Monoid_class_reps)
  have "\<And>x. x \<in> P \<Longrightarrow> Mr.invertible (some_elem x)"
    by (metis Mr.invertible_def image_eqI invertible invertible_def
        rep_comp)
  then show ?thesis
  proof unfold_locales qed auto
qed

lemma some_elem_inj_on: "inj_on some_elem P"
  by (rule inj_on_inverseI [where g = the_part]) simp

lemma some_elem_bij_betw: "bij_betw some_elem P (some_elem ` P)"
  using some_elem_inj_on by (simp add: bij_betw_def)

lemma Monoid_iso_class_reps:
  assumes "Monoid P (\<cdot>) \<one>"
  shows "Monoid_isomorphism (restrict some_elem P) P (\<cdot>) \<one> (some_elem ` P) rep_comp (some_elem \<one>)"
proof -
  interpret Monoid P
    by (simp add: assms)
  show ?thesis
    by unfold_locales
      (auto simp: Monoid_class_reps assms some_elem_bij_betw some_elem_typing rep_comp associative
        bij_betw_restrict_eq)
qed

lemma group_iso_class_reps:
  assumes "Group P (\<cdot>) \<one>"
  shows "group_isomorphism (restrict some_elem P) P (\<cdot>) \<one> (some_elem ` P) rep_comp (some_elem \<one>)"
proof -
  interpret Monoid_isomorphism "restrict some_elem P" P "(\<cdot>)" \<one> "some_elem ` P" rep_comp "some_elem \<one>"
    by (rule Monoid_iso_class_reps) (simp add: assms Group.axioms)
  show ?thesis
  proof
    show "\<And>u. u \<in> P \<Longrightarrow> invertible u"
      by (simp add: Group.invertible assms)
    show "\<And>u. u \<in> some_elem ` P \<Longrightarrow> invertible' u"
      by (meson Group.invertible Group_class_reps assms)
  qed
qed

lemma abelian_group_class_reps:
  assumes "Abelian_Group P (\<cdot>) \<one>"
  shows "Abelian_Group (some_elem ` P) rep_comp (some_elem \<one>)"
proof -
  interpret Abelian_Group P "(\<cdot>)" \<one> by (rule assms)
  have comm: "rep_comp (some_elem X) (some_elem Y) = rep_comp (some_elem Y) (some_elem X)"
    if "X \<in> P" "Y \<in> P" for X Y
    using that by (simp add: rep_comp commutative)
  show ?thesis
    unfolding Abelian_Group_def commutative_monoid_def commutative_monoid_axioms_def
    using Group_class_reps[OF Group_axioms] Group.axioms comm by auto
qed

end



context normal_subgroup begin

interpretation reps: class_representatives G Factor_Group quotient_composition "Class \<one>"
proof 
  show "partition_on G Factor_Group"
    by (rule partition)
  show "quotient_composition \<in> Factor_Group \<rightarrow>\<^sub>E Factor_Group \<rightarrow>\<^sub>E Factor_Group"
    by (rule quotient_composition_PiE)
  show "Class \<one> \<in> Factor_Group"
    by simp
qed

theorem group_isomorphism_Factor_Group_class_reps:
  "group_isomorphism
    (restrict some_elem Factor_Group) Factor_Group quotient_composition (Class \<one>)
    (some_elem ` Factor_Group) reps.rep_comp (some_elem (Class \<one>))"
  by (rule reps.group_iso_class_reps) (rule quotient.Group_axioms)

lemma card_class_reps:
  "card (some_elem ` Factor_Group) = card Factor_Group"
  using reps.some_elem_inj_on card_image by blast

lemma class_reps_subset: "some_elem ` Factor_Group \<subseteq> G"
  using reps.some_elem_typing by auto

lemma abelian_class_reps:
  assumes "Abelian_Group Factor_Group quotient_composition (Class \<one>)"
  shows "Abelian_Group (some_elem ` Factor_Group) reps.rep_comp (some_elem (Class \<one>))"
  using reps.abelian_group_class_reps[OF assms] .


end (* normal_subgroup *)



subsection \<open>Abstract type of monoids\<close>

lemma trivial_Monoid: "Monoid {undefined} (\<lambda>x y. undefined) undefined"
  by (auto simp: Monoid_def)

lemma trivial_Monoid_invertible: 
  "Monoid.invertible {undefined} (\<lambda>x y. undefined) undefined undefined"
  by (simp add: Monoid.unit_invertible trivial_Monoid)

lemma trivial_Group: "Group {undefined} (\<lambda>x y. undefined) undefined"
  by (simp add: Group_axioms_def Group_def trivial_Monoid
      trivial_Monoid_invertible)

typedef 'a monoid = "{(M::'a set,f,e). Monoid M f e}"
  morphisms "dest_monoid" "monoid"
  using trivial_Monoid  by blast

declare dest_monoid_inverse [simp]

definition "trivial_monoid \<equiv> monoid ({undefined}, (\<lambda>x y. undefined), undefined)"

definition mcarrier where "mcarrier m \<equiv> fst (dest_monoid m)"

definition mmult where "mmult m \<equiv> fst (snd (dest_monoid m))"

definition munit where "munit m \<equiv> snd (snd (dest_monoid m))"

lemma monoid_is_Monoid [iff]: "Monoid (mcarrier m) (mmult m) (munit m)"
  by (metis Product_Type.Collect_case_prodD dest_monoid mcarrier_def
      mem_Collect_eq munit_def mmult_def)

lemma mmult_assoc [simp]:
  "\<lbrakk> a \<in> mcarrier m; b \<in> mcarrier m; c \<in> mcarrier m \<rbrakk> \<Longrightarrow> mmult m (mmult m a b) c = mmult m a (mmult m b c)"
  by (meson Monoid.associative monoid_is_Monoid)

lemma m_left_unit: "a \<in> mcarrier m \<Longrightarrow> mmult m (munit m) a = a"
  by (meson Monoid.left_unit monoid_is_Monoid)

lemma m_right_unit: "a \<in> mcarrier m \<Longrightarrow> mmult m a (munit m) = a"
  by (meson Monoid.right_unit monoid_is_Monoid)

lemma (in Monoid) mcarrier_monoid[simp]: 
  "mcarrier (monoid (M, (\<cdot>), \<one>)) = M"
  by (simp add: mcarrier_def Monoid_axioms monoid_inverse)

lemma (in Monoid) mmult_monoid[simp]: 
  "mmult (monoid (M, (\<cdot>), \<one>)) = (\<cdot>)"
  by (simp add: mmult_def Monoid_axioms monoid_inverse)

lemma (in Monoid) munit_monoid[simp]: 
  "munit (monoid (M, (\<cdot>), \<one>)) = \<one>"
  by (simp add: munit_def Monoid_axioms monoid_inverse)

lemma monoid_collapse [simp]: "monoid (mcarrier m, mmult m, munit m) = m"
  by (simp add: mcarrier_def mmult_def munit_def)

text \<open>Allows reference to the current monoid space within the locale as a value\<close>
definition (in Monoid) "Self \<equiv> monoid (M, (\<cdot>), \<one>)"

lemma (in Monoid) mcarrier_Self [simp]: "mcarrier Self = M"
  by (simp add: Self_def)

lemma (in Monoid) mmult_Self [simp]: "mmult Self = (\<cdot>)"
  by (simp add: Self_def)

lemma (in Monoid) munit_Self [simp]: "munit Self = \<one>"
  by (simp add: Self_def)


end
