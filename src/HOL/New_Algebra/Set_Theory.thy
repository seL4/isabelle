(*
  Derived from the AFP entry Jacobson_Basic_Algebra, by Clemens Ballarin
*)

theory Set_Theory 
  imports "HOL-Library.FuncSet" "HOL-Library.Disjoint_Sets"

begin

no_notation divide (infixl \<open>'/\<close> 70)
no_notation inverse_divide (infixl \<open>'/\<close> 70)
no_notation quotient (infixl \<open>'/'/\<close> 90)

abbreviation "identity S \<equiv> (\<lambda>x \<in> S. x)"

theorem bij_betw_iff_has_inverse:
  assumes "\<alpha> \<in> S \<rightarrow>\<^sub>E T"
  shows "bij_betw \<alpha> S T \<longleftrightarrow> (\<exists>\<beta> \<in> T \<rightarrow>\<^sub>E S. compose S \<beta> \<alpha> = identity S \<and> compose T \<alpha> \<beta> = identity T)"
    (is "_ \<longleftrightarrow> (\<exists>\<beta> \<in> T \<rightarrow>\<^sub>E S. ?INV \<beta>)")
proof
  assume "bij_betw \<alpha> S T"
  then have "?INV (restrict (inv_into S \<alpha>) T)" 
    by (simp add: bij_betw_imp_surj_on compose_id_inv_into compose_inv_into_id)
  then show "\<exists>\<beta> \<in> T \<rightarrow>\<^sub>E S. ?INV \<beta>"
    by (metis \<open>bij_betw \<alpha> S T\<close> bij_betw_imp_surj_on inv_into_funcset restrict_PiE
        restrict_Pi_cancel) 
next
  assume "\<exists>\<beta> \<in> T \<rightarrow>\<^sub>E S. ?INV \<beta>"
  then obtain \<beta> where "\<alpha> \<in> S \<rightarrow> T" "\<beta> \<in> T \<rightarrow> S" "\<And>x. x \<in> S \<Longrightarrow> \<beta> (\<alpha> x) = x" "\<And>y. y \<in> T \<Longrightarrow> \<alpha> (\<beta> y) = y"
    by (metis Int_iff PiE_def assms compose_eq restrict_apply')
  then show "bij_betw \<alpha> S T" by (rule bij_betwI) 
qed

subsection \<open>Compatibility with Ballarin's original development\<close>

text \<open>Maps as extensional HOL functions\<close>
text \<open>p 5, ll 21--25\<close>
locale map =
  fixes \<alpha> and S and T
  assumes graph [intro, simp]: "\<alpha> \<in> S \<rightarrow>\<^sub>E T"
begin

text \<open>p 5, ll 21--25\<close>
lemma map_closed [intro, simp]:
  "a \<in> S \<Longrightarrow> \<alpha> a \<in> T"
using graph by fast
  
text \<open>p 5, ll 21--25\<close>
lemma map_undefined [intro]:
  "a \<notin> S \<Longrightarrow> \<alpha> a = undefined"
using graph by fast

end (* map *)

text \<open>p 7, ll 7--8\<close>
locale surjective_map = map + 
  assumes surjective [intro]: "\<alpha> ` S = T"

text \<open>p 7, ll 8--9\<close>
locale injective_map = map + 
  assumes injective [intro, simp]: "inj_on \<alpha> S"

locale bijective_map = map + 
  assumes bijective [intro, simp]: "bij_betw \<alpha> S T"

begin

text \<open>p 7, ll 9--10\<close>
sublocale surjective_map by unfold_locales (simp add: bij_betw_imp_surj_on)

text \<open>p 7, ll 9--10\<close>
sublocale injective_map using bij_betw_def by unfold_locales fast

text \<open>p 9, ll 12--13\<close>
sublocale inverse: map "restrict (inv_into S \<alpha>) T" T S
proof qed (simp add: inv_into_into surjective)

text \<open>p 9, ll 12--13\<close>
lemma bij_betw_inverse: "bij_betw (restrict (inv_into S \<alpha>) T) T S"
  by (simp add: bij_betw_inv_into)

end (* bijective_map *)


locale Equivalence =
  fixes S and E
  assumes eqv: "equiv S E"
begin

lemma closed [intro, simp]: "E \<subseteq> S \<times> S"
  by (simp add: equiv_type eqv)

lemma reflexive [intro, simp]: "a \<in> S \<Longrightarrow> (a, a) \<in> E"
  by (metis eq_equiv_class_iff2 eqv)

lemma symmetric [sym]: "(a, b) \<in> E \<Longrightarrow> (b, a) \<in> E"
  by (meson equivE eqv symD)

lemma transitive [trans]: "\<lbrakk> (a, b) \<in> E; (b, c) \<in> E \<rbrakk> \<Longrightarrow> (a, c) \<in> E"
  by (meson equiv_def eqv transE)

lemma left_closed [intro]: 
  "(a, b) \<in> E \<Longrightarrow> a \<in> S"
  using closed by blast
  
text \<open>p 11, ll 6--11\<close>
lemma right_closed [intro]: 
  "(a, b) \<in> E \<Longrightarrow> b \<in> S"
  using closed by blast

text \<open>Equivalence classes\<close>
definition "Class \<equiv> (\<lambda>a \<in> S. E``{a})"

text \<open>p 11, ll 24--26\<close>
lemma Class_closed [dest]:
  "\<lbrakk> a \<in> Class b; b \<in> S \<rbrakk> \<Longrightarrow> a \<in> S"
  unfolding Class_def by auto

text \<open>p 11, ll 24--26\<close>
lemma Class_closed2 [intro, simp]:
  "a \<in> S \<Longrightarrow> Class a \<subseteq> S"
  unfolding Class_def by auto

text \<open>p 11, ll 24--26\<close>
lemma Class_undefined [intro, simp]:
  "a \<notin> S \<Longrightarrow> Class a = undefined"
  unfolding Class_def by simp

text \<open>p 11, ll 24--26\<close>
lemma ClassI [intro, simp]:
  "(a, b) \<in> E \<Longrightarrow> a \<in> Class b"
  by (simp add: Class_def local.symmetric right_closed)
  
text \<open>p 11, ll 24--26\<close>
lemma Class_revI [intro, simp]:
  "(a, b) \<in> E \<Longrightarrow> b \<in> Class a"
  by (blast intro: symmetric)

text \<open>p 11, ll 24--26\<close>
lemma ClassD [dest]:
  "\<lbrakk> b \<in> Class a; a \<in> S \<rbrakk> \<Longrightarrow> (b, a) \<in> E"
  by (simp add: Class_def local.symmetric)

text \<open>p 11, ll 30--31\<close>
theorem Class_self [intro, simp]:
  "a \<in> S \<Longrightarrow> a \<in> Class a"
  unfolding Class_def by simp

text \<open>p 11, l 31; p 12, l 1\<close>
theorem Class_Union [simp]:
  "(\<Union>a\<in>S. Class a) = S"
  by blast

text \<open>p 11, ll 2--3\<close>
theorem Class_subset:
  "(a, b) \<in> E \<Longrightarrow> Class a \<subseteq> Class b"
proof
  fix a and b and c
  assume "(a, b) \<in> E" and "c \<in> Class a"
  then have "(c, a) \<in> E" by auto
  also note \<open>(a, b) \<in> E\<close>
  finally have "(c, b) \<in> E" by simp
  then show "c \<in> Class b" by auto
qed

text \<open>p 11, ll 3--4\<close>
theorem Class_eq:
  "(a, b) \<in> E \<Longrightarrow> Class a = Class b"
  by (auto intro!: Class_subset intro: symmetric)

text \<open>p 12, ll 1--5\<close>
theorem Class_equivalence:
  "\<lbrakk> a \<in> S; b \<in> S \<rbrakk> \<Longrightarrow> Class a = Class b \<longleftrightarrow> (a, b) \<in> E"
proof
  fix a and b
  assume "a \<in> S" "b \<in> S" "Class a = Class b"
  then have "a \<in> Class a" by auto
  also note \<open>Class a = Class b\<close>
  finally show "(a, b) \<in> E" by (fast intro: \<open>b \<in> S\<close>)
qed (rule Class_eq)

text \<open>p 12, ll 5--7\<close>
theorem not_disjoint_implies_equal:
  assumes "Class a \<inter> Class b \<noteq> {}"
  assumes "a \<in> S" "b \<in> S"
  shows "Class a = Class b"
  by (metis ClassD Class_eq assms disjoint_iff_not_equal)

definition "Partition = Class ` S"
notation Equivalence.Partition (infixl \<open>'/\<close> 75)

text \<open>p 12, ll 7--8\<close>
lemma Class_in_Partition [intro, simp]:
  "a \<in> S \<Longrightarrow> Class a \<in> Partition"
  unfolding Partition_def by fast

text \<open>p 12, ll 7--8\<close>
theorem partition:
  "partition_on S Partition"
proof (intro partition_onI)
  fix p q
  assume "p \<in> Partition" "q \<in> Partition" "p \<noteq> q"
  with not_disjoint_implies_equal show "disjnt p q"
    by (auto simp: Partition_def disjnt_iff)
qed (force simp add: Partition_def)+

end


context Equivalence
begin

text \<open>p 12, ll 18--20\<close>
lemma representant_exists: "A \<in> S / E \<Longrightarrow> \<exists>a\<in>S. a \<in> A \<and> A = Class a"
  using Class_self Partition_def image_iff by auto

text \<open>p 12, ll 18--20\<close>
lemma quotient_ClassE: "A \<in> S / E \<Longrightarrow> (\<And>a. a \<in> S \<Longrightarrow> P (Class a)) \<Longrightarrow> P A"
  using representant_exists by auto

end (* equivalence *)

lemma equivalenceI:
  assumes closed: "E \<subseteq> S \<times> S"
    and reflexive: "\<And>a. a \<in> S \<Longrightarrow> (a, a) \<in> E"
    and symmetric: "\<And>a b. (a, b) \<in> E \<Longrightarrow> (b, a) \<in> E"
    and transitive: "\<And>a b c. \<lbrakk> (a, b) \<in> E; (b, c) \<in> E \<rbrakk> \<Longrightarrow> (a, c) \<in> E"
  shows "Equivalence S E"
  using assms Equivalence_def equiv_def refl_on_def sym_def trans_def
  by metis


text \<open>p 12, ll 21--23\<close>
sublocale Equivalence \<subseteq> natural: surjective_map Class S "S / E"
proof qed (auto simp: Partition_def)

text \<open>Technical device to achieve Jacobson's syntax; context where @{text \<alpha>} is not a parameter.\<close>
text \<open>p 12, ll 25--26\<close>
locale fiber_relation_notation = fixes S :: "'a set" begin

text \<open>p 12, ll 25--26\<close>
definition Fiber_Relation (\<open>E'(_')\<close>) where "Fiber_Relation \<alpha> = {(x, y). x \<in> S \<and> y \<in> S \<and> \<alpha> x = \<alpha> y}"

end (* fiber_relation_notation *)

text \<open>
  Context where classes and the induced map are defined through the fiber relation.
  This will be the case for monoid homomorphisms but not group homomorphisms.
\<close>
text \<open>Avoids infinite interpretation chain.\<close>
text \<open>p 12, ll 25--26\<close>
locale fiber_relation = map begin

text \<open>Install syntax\<close>
text \<open>p 12, ll 25--26\<close>
sublocale fiber_relation_notation .

text \<open>p 12, ll 26--27\<close>
sublocale Equivalence where E = "E(\<alpha>)"
  unfolding Fiber_Relation_def
  by (force intro: equivalenceI)

text \<open>``define $\bar{\alpha}$ by $\bar{\alpha}(\bar{a}) = \alpha(a)$''\<close>
text \<open>p 13, ll 8--9\<close>
definition "induced = (\<lambda>A \<in> S / E(\<alpha>). THE b. \<exists>a \<in> A. b = \<alpha> a)"

text \<open>p 13, l 10\<close>
theorem Fiber_equality:
  "\<lbrakk> a \<in> S; b \<in> S \<rbrakk> \<Longrightarrow> Class a = Class b \<longleftrightarrow> \<alpha> a = \<alpha> b"
  unfolding Class_equivalence unfolding Fiber_Relation_def by simp

text \<open>p 13, ll 8--9\<close>
theorem induced_Fiber_simp [simp]:
  assumes [intro, simp]: "a \<in> S" 
  shows "induced (Class a) = \<alpha> a"
proof -
  have "\<And>b. \<exists>x\<in>Class a. b = \<alpha> x \<Longrightarrow> b = \<alpha> a"
    by (metis ClassD Class_closed Class_eq Fiber_equality assms)
  then have "(THE b. \<exists>a\<in>Class a. b = \<alpha> a) = \<alpha> a"
    by blast
  then show ?thesis unfolding induced_def by simp
qed

text \<open>p 13, ll 10--11\<close>
interpretation induced: map induced "S / E(\<alpha>)" T
proof (unfold_locales, rule)
  fix A
  assume [intro, simp]: "A \<in> S / E(\<alpha>)"
  obtain a where a: "a \<in> S" "a \<in> A"
    using representant_exists by blast
  have "(THE b. \<exists>a\<in>A. b = \<alpha> a) \<in> T"
    by (metis (no_types, lifting) \<open>A \<in> Partition\<close> induced_Fiber_simp
        induced_def map_closed representant_exists restrict_apply')
  then show "induced A \<in> T" unfolding induced_def by simp
qed (simp add: induced_def)

text \<open>p 13, ll 12--13\<close>
sublocale induced: injective_map induced "S / E(\<alpha>)" T
proof
  show "inj_on induced Partition"
    unfolding inj_on_def
    by (metis Fiber_equality induced_Fiber_simp representant_exists)
qed

text \<open>p 13, ll 16--19\<close>
theorem factorization_lemma:
  "a \<in> S \<Longrightarrow> compose S induced Class a = \<alpha> a"
  by (simp add: compose_eq)

text \<open>p 13, ll 16--19\<close>
theorem factorization [simp]: "compose S induced Class = \<alpha>"
  by (rule ext) (simp add: compose_def map_undefined)

text \<open>p 14, ll 2--4\<close>
theorem uniqueness:
  assumes map: "\<beta> \<in> S / E(\<alpha>) \<rightarrow>\<^sub>E T"
    and factorization: "compose S \<beta> Class = \<alpha>"
  shows "\<beta> = induced"
proof
  fix A
  show "\<beta> A = induced A"
  proof (cases "A \<in> S / E(\<alpha>)")
    case True
    then obtain a where [simp]: "A = Class a" "a \<in> S"
      using representant_exists by auto
    then have "\<beta> (Class a) = \<alpha> a" by (metis compose_eq factorization)
    also have "\<dots> = induced (Class a)" by simp
    finally show ?thesis by simp
  qed (simp add: induced_def PiE_arb [OF map])
qed

end (* fiber_relation *)

hide_const (open) map

end
