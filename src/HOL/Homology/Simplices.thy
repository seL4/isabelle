section\<open>Homology, I: Simplices\<close>

theory "Simplices"
  imports
    "HOL-Analysis.Function_Metric"
    "HOL-Analysis.Abstract_Euclidean_Space"
    "HOL-Algebra.Free_Abelian_Groups"
begin

subsection\<open>Standard simplices, all of which are topological subspaces of @{text"R^n"}.      \<close>

type_synonym 'a chain = "((nat \<Rightarrow> real) \<Rightarrow> 'a) \<Rightarrow>\<^sub>0 int"

definition standard_simplex :: "nat \<Rightarrow> (nat \<Rightarrow> real) set" where
  "standard_simplex p \<equiv>
    {x. (\<forall>i. 0 \<le> x i \<and> x i \<le> 1) \<and> (\<forall>i>p. x i = 0) \<and> (\<Sum>i\<le>p. x i) = 1}"

lemma topspace_standard_simplex:
  "topspace(subtopology (powertop_real UNIV) (standard_simplex p))
    = standard_simplex p"
  by simp

lemma basis_in_standard_simplex [simp]:
   "(\<lambda>j. if j = i then 1 else 0) \<in> standard_simplex p \<longleftrightarrow> i \<le> p"
  by (auto simp: standard_simplex_def)

lemma nonempty_standard_simplex: "standard_simplex p \<noteq> {}"
  using basis_in_standard_simplex by blast

lemma standard_simplex_0: "standard_simplex 0 = {(\<lambda>j. if j = 0 then 1 else 0)}"
  by (auto simp: standard_simplex_def)

lemma standard_simplex_mono:
  assumes "p \<le> q"
  shows "standard_simplex p \<subseteq> standard_simplex q"
  using assms
proof (clarsimp simp: standard_simplex_def)
  fix x :: "nat \<Rightarrow> real"
  assume "\<forall>i. 0 \<le> x i \<and> x i \<le> 1" and "\<forall>i>p. x i = 0" and "sum x {..p} = 1"
  then show "sum x {..q} = 1"
    using sum.mono_neutral_left [of "{..q}" "{..p}" x] assms by auto
qed

lemma closedin_standard_simplex:
   "closedin (powertop_real UNIV) (standard_simplex p)"
    (is "closedin ?X ?S")
proof -
  have eq: "standard_simplex p =
              (\<Inter>i. {x. x \<in> topspace ?X \<and> x i \<in> {0..1}}) \<inter>
              (\<Inter>i \<in> {p<..}. {x \<in> topspace ?X. x i \<in> {0}}) \<inter>
              {x \<in> topspace ?X. (\<Sum>i\<le>p. x i) \<in> {1}}"
    by (auto simp: standard_simplex_def topspace_product_topology)
  show ?thesis
    unfolding eq
    by (rule closedin_Int closedin_Inter continuous_map_sum
             continuous_map_product_projection closedin_continuous_map_preimage | force | clarify)+
qed

lemma standard_simplex_01: "standard_simplex p \<subseteq> UNIV \<rightarrow>\<^sub>E {0..1}"
  using standard_simplex_def by auto

lemma compactin_standard_simplex:
   "compactin (powertop_real UNIV) (standard_simplex p)"
proof (rule closed_compactin)
  show "compactin (powertop_real UNIV) (UNIV \<rightarrow>\<^sub>E {0..1})"
    by (simp add: compactin_PiE)
  show "standard_simplex p \<subseteq> UNIV \<rightarrow>\<^sub>E {0..1}"
    by (simp add: standard_simplex_01)
  show "closedin (powertop_real UNIV) (standard_simplex p)"
    by (simp add: closedin_standard_simplex)
qed

lemma convex_standard_simplex:
   "\<lbrakk>x \<in> standard_simplex p; y \<in> standard_simplex p;
     0 \<le> u; u \<le> 1\<rbrakk>
    \<Longrightarrow> (\<lambda>i. (1 - u) * x i + u * y i) \<in> standard_simplex p"
  by (simp add: standard_simplex_def sum.distrib convex_bound_le flip: sum_distrib_left)

lemma path_connectedin_standard_simplex:
   "path_connectedin (powertop_real UNIV) (standard_simplex p)"
proof -
  define g where "g \<equiv> \<lambda>x y::nat\<Rightarrow>real. \<lambda>u i. (1 - u) * x i + u * y i"
  have "continuous_map
                (subtopology euclideanreal {0..1}) (powertop_real UNIV)
                (g x y)"
    if "x \<in> standard_simplex p" "y \<in> standard_simplex p" for x y
    unfolding g_def continuous_map_componentwise
    by (force intro: continuous_intros)
  moreover
  have "g x y ` {0..1} \<subseteq> standard_simplex p" "g x y 0 = x" "g x y 1 = y"
    if "x \<in> standard_simplex p" "y \<in> standard_simplex p" for x y
    using that by (auto simp: convex_standard_simplex g_def)
  ultimately
  show ?thesis
    unfolding path_connectedin_def path_connected_space_def pathin_def
    by (metis continuous_map_in_subtopology euclidean_product_topology top_greatest topspace_euclidean topspace_euclidean_subtopology)
qed

lemma connectedin_standard_simplex:
   "connectedin (powertop_real UNIV) (standard_simplex p)"
  by (simp add: path_connectedin_imp_connectedin path_connectedin_standard_simplex)

subsection\<open>Face map\<close>

definition simplical_face :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a::comm_monoid_add" where
   "simplical_face k x \<equiv> \<lambda>i. if i < k then x i else if i = k then 0 else x(i -1)"

lemma simplical_face_in_standard_simplex:
  assumes "1 \<le> p" "k \<le> p" "x \<in> standard_simplex (p - Suc 0)"
  shows "(simplical_face k x) \<in> standard_simplex p"
proof -
  have x01: "\<And>i. 0 \<le> x i \<and> x i \<le> 1" and sumx: "sum x {..p - Suc 0} = 1"
    using assms by (auto simp: standard_simplex_def simplical_face_def)
  have gg: "\<And>g. sum g {..p} = sum g {..<k} + sum g {k..p}"
    using \<open>k \<le> p\<close> sum.union_disjoint [of "{..<k}" "{k..p}"]
    by (force simp: ivl_disj_un ivl_disj_int)
  have eq: "(\<Sum>i\<le>p. if i < k then x i else if i = k then 0 else x (i -1))
         = (\<Sum>i < k. x i) + (\<Sum>i \<in> {k..p}. if i = k then 0 else x (i -1))"
    by (simp add: gg)
  consider "k \<le> p - Suc 0" | "k = p"
    using \<open>k \<le> p\<close> by linarith
  then have "(\<Sum>i\<le>p. if i < k then x i else if i = k then 0 else x (i -1)) = 1"
  proof cases
    case 1
    have [simp]: "Suc (p - Suc 0) = p"
      using \<open>1 \<le> p\<close> by auto
    have "(\<Sum>i = k..p. if i = k then 0 else x (i -1)) = (\<Sum>i = k+1..p. if i = k then 0 else x (i -1))"
      by (rule sum.mono_neutral_right) auto
    also have "\<dots> = (\<Sum>i = k+1..p. x (i -1))"
      by simp
    also have "\<dots> = (\<Sum>i = k..p-1. x i)"
      using sum.atLeastAtMost_reindex [of Suc k "p-1" "\<lambda>i. x (i - Suc 0)"] 1 by simp
    finally have eq2: "(\<Sum>i = k..p. if i = k then 0 else x (i -1)) = (\<Sum>i = k..p-1. x i)" .
    with 1 show ?thesis 
      by (metis (no_types, lifting) One_nat_def eq finite_atLeastAtMost finite_lessThan ivl_disj_int(4) ivl_disj_un(10) sum.union_disjoint sumx)
  next
    case 2
    have [simp]: "({..p} \<inter> {x. x < p}) = {..p - Suc 0}"
      using assms by auto
    have "(\<Sum>i\<le>p. if i < p then x i else if i = k then 0 else x (i -1)) = (\<Sum>i\<le>p. if i < p then x i else 0)"
      by (rule sum.cong) (auto simp: 2)
    also have "\<dots> = sum x {..p-1}"
      by (simp add: sum.If_cases)
    also have "\<dots> = 1"
      by (simp add: sumx)
    finally show ?thesis
      using 2 by simp
  qed
  then show ?thesis
    using assms by (auto simp: standard_simplex_def simplical_face_def)
qed

subsection\<open>Singular simplices, forcing canonicity outside the intended domain\<close>

definition singular_simplex :: "nat \<Rightarrow> 'a topology \<Rightarrow> ((nat \<Rightarrow> real) \<Rightarrow> 'a) \<Rightarrow> bool" where
 "singular_simplex p X f \<equiv>
      continuous_map(subtopology (powertop_real UNIV) (standard_simplex p)) X f
    \<and> f \<in> extensional (standard_simplex p)"

abbreviation singular_simplex_set :: "nat \<Rightarrow> 'a topology \<Rightarrow> ((nat \<Rightarrow> real) \<Rightarrow> 'a) set" where
 "singular_simplex_set p X \<equiv> Collect (singular_simplex p X)"

lemma singular_simplex_empty:
   "topspace X = {} \<Longrightarrow> \<not> singular_simplex p X f"
  by (simp add: singular_simplex_def continuous_map nonempty_standard_simplex)

lemma singular_simplex_mono:
   "\<lbrakk>singular_simplex p (subtopology X T) f; T \<subseteq> S\<rbrakk> \<Longrightarrow> singular_simplex p (subtopology X S) f"
  by (auto simp: singular_simplex_def continuous_map_in_subtopology)

lemma singular_simplex_subtopology:
   "singular_simplex p (subtopology X S) f \<longleftrightarrow>
        singular_simplex p X f \<and> f ` (standard_simplex p) \<subseteq> S"
  by (auto simp: singular_simplex_def continuous_map_in_subtopology)

subsubsection\<open>Singular face\<close>

definition singular_face :: "nat \<Rightarrow> nat \<Rightarrow> ((nat \<Rightarrow> real) \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 'a"
  where "singular_face p k f \<equiv> restrict (f \<circ> simplical_face k) (standard_simplex (p - Suc 0))"

lemma singular_simplex_singular_face:
  assumes f: "singular_simplex p X f" and "1 \<le> p" "k \<le> p"
  shows "singular_simplex (p - Suc 0) X (singular_face p k f)"
proof -
  let ?PT = "(powertop_real UNIV)"
  have 0: "simplical_face k ` standard_simplex (p - Suc 0) \<subseteq> standard_simplex p"
    using assms simplical_face_in_standard_simplex by auto
  have 1: "continuous_map (subtopology ?PT (standard_simplex (p - Suc 0)))
                          (subtopology ?PT (standard_simplex p))
                          (simplical_face k)"
  proof (clarsimp simp add: continuous_map_in_subtopology simplical_face_in_standard_simplex continuous_map_componentwise 0)
    fix i
    have "continuous_map ?PT euclideanreal (\<lambda>x. if i < k then x i else if i = k then 0 else x (i -1))"
      by (auto intro: continuous_map_product_projection)
    then show "continuous_map (subtopology ?PT (standard_simplex (p - Suc 0))) euclideanreal
                              (\<lambda>x. simplical_face k x i)"
      by (simp add: simplical_face_def continuous_map_from_subtopology)
  qed
  have 2: "continuous_map (subtopology ?PT (standard_simplex p)) X f"
    using assms(1) singular_simplex_def by blast
  show ?thesis
    by (simp add: singular_simplex_def singular_face_def continuous_map_compose [OF 1 2])
qed


subsection\<open>Singular chains\<close>

definition singular_chain :: "[nat, 'a topology, 'a chain] \<Rightarrow> bool"
  where "singular_chain p X c \<equiv> Poly_Mapping.keys c \<subseteq> singular_simplex_set p X"

abbreviation singular_chain_set :: "[nat, 'a topology] \<Rightarrow> ('a chain) set"
  where "singular_chain_set p X \<equiv> Collect (singular_chain p X)"

lemma singular_chain_empty:
   "topspace X = {} \<Longrightarrow> singular_chain p X c \<longleftrightarrow> c = 0"
  by (auto simp: singular_chain_def singular_simplex_empty subset_eq poly_mapping_eqI)

lemma singular_chain_mono:
   "\<lbrakk>singular_chain p (subtopology X T) c;  T \<subseteq> S\<rbrakk>
        \<Longrightarrow> singular_chain p (subtopology X S) c"
  unfolding singular_chain_def using singular_simplex_mono by blast

lemma singular_chain_subtopology:
   "singular_chain p (subtopology X S) c \<longleftrightarrow>
        singular_chain p X c \<and> (\<forall>f \<in> Poly_Mapping.keys c. f ` (standard_simplex p) \<subseteq> S)"
  unfolding singular_chain_def
  by (fastforce simp add: singular_simplex_subtopology subset_eq)

lemma singular_chain_0 [iff]: "singular_chain p X 0"
  by (auto simp: singular_chain_def)

lemma singular_chain_of:
   "singular_chain p X (frag_of c) \<longleftrightarrow> singular_simplex p X c"
  by (auto simp: singular_chain_def)

lemma singular_chain_cmul:
   "singular_chain p X c \<Longrightarrow> singular_chain p X (frag_cmul a c)"
  by (auto simp: singular_chain_def)

lemma singular_chain_minus:
   "singular_chain p X (-c) \<longleftrightarrow> singular_chain p X c"
  by (auto simp: singular_chain_def)

lemma singular_chain_add:
   "\<lbrakk>singular_chain p X a; singular_chain p X b\<rbrakk> \<Longrightarrow> singular_chain p X (a+b)"
  unfolding singular_chain_def
  using keys_add [of a b] by blast

lemma singular_chain_diff:
   "\<lbrakk>singular_chain p X a; singular_chain p X b\<rbrakk> \<Longrightarrow> singular_chain p X (a-b)"
  unfolding singular_chain_def
  using keys_diff [of a b] by blast

lemma singular_chain_sum:
   "(\<And>i. i \<in> I \<Longrightarrow> singular_chain p X (f i)) \<Longrightarrow> singular_chain p X (\<Sum>i\<in>I. f i)"
  unfolding singular_chain_def
  using keys_sum [of f I] by blast

lemma singular_chain_extend:
   "(\<And>c. c \<in> Poly_Mapping.keys x \<Longrightarrow> singular_chain p X (f c))
        \<Longrightarrow> singular_chain p X (frag_extend f x)"
  by (simp add: frag_extend_def singular_chain_cmul singular_chain_sum)

subsection\<open>Boundary homomorphism for singular chains\<close>

definition chain_boundary :: "nat \<Rightarrow> ('a chain) \<Rightarrow> 'a chain"
  where "chain_boundary p c \<equiv>
          (if p = 0 then 0 else
           frag_extend (\<lambda>f. (\<Sum>k\<le>p. frag_cmul ((-1) ^ k) (frag_of(singular_face p k f)))) c)"

lemma singular_chain_boundary:
  assumes "singular_chain p X c"
  shows "singular_chain (p - Suc 0) X (chain_boundary p c)"
  unfolding chain_boundary_def
proof (clarsimp intro!: singular_chain_extend singular_chain_sum singular_chain_cmul)
  show "\<And>d k. \<lbrakk>0 < p; d \<in> Poly_Mapping.keys c; k \<le> p\<rbrakk>
       \<Longrightarrow> singular_chain (p - Suc 0) X (frag_of (singular_face p k d))"
    using assms by (auto simp: singular_chain_def intro: singular_simplex_singular_face)
qed

lemma singular_chain_boundary_alt:
   "singular_chain (Suc p) X c \<Longrightarrow> singular_chain p X (chain_boundary (Suc p) c)"
  using singular_chain_boundary by force

lemma chain_boundary_0 [simp]: "chain_boundary p 0 = 0"
  by (simp add: chain_boundary_def)

lemma chain_boundary_cmul:
   "chain_boundary p (frag_cmul k c) = frag_cmul k (chain_boundary p c)"
  by (auto simp: chain_boundary_def frag_extend_cmul)

lemma chain_boundary_minus:
   "chain_boundary p (- c) = - (chain_boundary p c)"
  by (metis chain_boundary_cmul frag_cmul_minus_one)

lemma chain_boundary_add:
   "chain_boundary p (a+b) = chain_boundary p a + chain_boundary p b"
  by (simp add: chain_boundary_def frag_extend_add)

lemma chain_boundary_diff:
   "chain_boundary p (a-b) = chain_boundary p a - chain_boundary p b"
  using chain_boundary_add [of p a "-b"]
  by (simp add: chain_boundary_minus)

lemma chain_boundary_sum:
   "chain_boundary p (sum g I) = sum (chain_boundary p \<circ> g) I"
  by (induction I rule: infinite_finite_induct) (simp_all add: chain_boundary_add)

lemma chain_boundary_sum':
   "finite I \<Longrightarrow> chain_boundary p (sum' g I) = sum' (chain_boundary p \<circ> g) I"
  by (induction I rule: finite_induct) (simp_all add: chain_boundary_add)

lemma chain_boundary_of:
   "chain_boundary p (frag_of f) =
        (if p = 0 then 0
         else (\<Sum>k\<le>p. frag_cmul ((-1) ^ k) (frag_of(singular_face p k f))))"
  by (simp add: chain_boundary_def)

subsection\<open>Factoring out chains in a subtopology for relative homology\<close>

definition mod_subset
  where "mod_subset p X \<equiv> {(a,b). singular_chain p X (a - b)}"

lemma mod_subset_empty [simp]:
   "(a,b) \<in> (mod_subset p (subtopology X {})) \<longleftrightarrow> a = b"
  by (simp add: mod_subset_def singular_chain_empty)

lemma mod_subset_refl [simp]: "(c,c) \<in> mod_subset p X"
  by (auto simp: mod_subset_def)

lemma mod_subset_cmul:
  assumes "(a,b) \<in> mod_subset p X"
  shows "(frag_cmul k a, frag_cmul k b) \<in> mod_subset p X"
  using assms
  by (simp add: mod_subset_def) (metis (no_types, lifting) add_diff_cancel diff_add_cancel frag_cmul_distrib2 singular_chain_cmul)

lemma mod_subset_add:
   "\<lbrakk>(c1,c2) \<in> mod_subset p X; (d1,d2) \<in> mod_subset p X\<rbrakk> \<Longrightarrow> (c1+d1, c2+d2) \<in> mod_subset p X"
  by (simp add: mod_subset_def add_diff_add singular_chain_add)

subsection\<open>Relative cycles $Z_pX (S)$ where $X$ is a topology and $S$ a subset \<close>

definition singular_relcycle :: "nat \<Rightarrow> 'a topology \<Rightarrow> 'a set \<Rightarrow> ('a chain) \<Rightarrow> bool"
  where "singular_relcycle p X S \<equiv>
        \<lambda>c. singular_chain p X c \<and> (chain_boundary p c, 0) \<in> mod_subset (p-1) (subtopology X S)"

abbreviation singular_relcycle_set
  where "singular_relcycle_set p X S \<equiv> Collect (singular_relcycle p X S)"

lemma singular_relcycle_restrict [simp]:
   "singular_relcycle p X (topspace X \<inter> S) = singular_relcycle p X S"
proof -
  have eq: "subtopology X (topspace X \<inter> S) = subtopology X S"
    by (metis subtopology_subtopology subtopology_topspace)
  show ?thesis
    by (force simp: singular_relcycle_def eq)
qed

lemma singular_relcycle:
   "singular_relcycle p X S c \<longleftrightarrow>
    singular_chain p X c \<and> singular_chain (p-1) (subtopology X S) (chain_boundary p c)"
  by (simp add: singular_relcycle_def mod_subset_def)

lemma singular_relcycle_0 [simp]: "singular_relcycle p X S 0"
  by (auto simp: singular_relcycle_def)

lemma singular_relcycle_cmul:
   "singular_relcycle p X S c \<Longrightarrow> singular_relcycle p X S (frag_cmul k c)"
  by (auto simp: singular_relcycle_def chain_boundary_cmul dest: singular_chain_cmul mod_subset_cmul)

lemma singular_relcycle_minus:
   "singular_relcycle p X S (-c) \<longleftrightarrow> singular_relcycle p X S c"
  by (simp add: chain_boundary_minus singular_chain_minus singular_relcycle)

lemma singular_relcycle_add:
   "\<lbrakk>singular_relcycle p X S a; singular_relcycle p X S b\<rbrakk>
        \<Longrightarrow> singular_relcycle p X S (a+b)"
  by (simp add: singular_relcycle_def chain_boundary_add mod_subset_def singular_chain_add)

lemma singular_relcycle_sum:
   "\<lbrakk>\<And>i. i \<in> I \<Longrightarrow> singular_relcycle p X S (f i)\<rbrakk>
        \<Longrightarrow> singular_relcycle p X S (sum f I)"
  by (induction I rule: infinite_finite_induct) (auto simp: singular_relcycle_add)

lemma singular_relcycle_diff:
   "\<lbrakk>singular_relcycle p X S a; singular_relcycle p X S b\<rbrakk>
        \<Longrightarrow> singular_relcycle p X S (a-b)"
  by (metis singular_relcycle_add singular_relcycle_minus uminus_add_conv_diff)

lemma singular_cycle:
   "singular_relcycle p X {} c \<longleftrightarrow> singular_chain p X c \<and> chain_boundary p c = 0"
  by (simp add: singular_relcycle_def)

lemma singular_cycle_mono:
   "\<lbrakk>singular_relcycle p (subtopology X T) {} c; T \<subseteq> S\<rbrakk>
        \<Longrightarrow> singular_relcycle p (subtopology X S) {} c"
  by (auto simp: singular_cycle elim: singular_chain_mono)


subsection\<open>Relative boundaries $B_p X S$, where $X$ is a topology and $S$ a subset.\<close>

definition singular_relboundary :: "nat \<Rightarrow> 'a topology \<Rightarrow> 'a set \<Rightarrow> ('a chain) \<Rightarrow> bool"
  where
  "singular_relboundary p X S \<equiv>
    \<lambda>c. \<exists>d. singular_chain (Suc p) X d \<and> (chain_boundary (Suc p) d, c) \<in> (mod_subset p (subtopology X S))"

abbreviation singular_relboundary_set :: "nat \<Rightarrow> 'a topology \<Rightarrow> 'a set \<Rightarrow> ('a chain) set"
  where "singular_relboundary_set p X S \<equiv> Collect (singular_relboundary p X S)"

lemma singular_relboundary_restrict [simp]:
   "singular_relboundary p X (topspace X \<inter> S) = singular_relboundary p X S"
  unfolding singular_relboundary_def
  by (metis (no_types, hide_lams) subtopology_subtopology subtopology_topspace)

lemma singular_relboundary_alt:
   "singular_relboundary p X S c \<longleftrightarrow>
    (\<exists>d e. singular_chain (Suc p) X d \<and> singular_chain p (subtopology X S) e \<and>
           chain_boundary (Suc p) d = c + e)"
  unfolding singular_relboundary_def mod_subset_def by fastforce

lemma singular_relboundary:
   "singular_relboundary p X S c \<longleftrightarrow>
    (\<exists>d e. singular_chain (Suc p) X d \<and> singular_chain p (subtopology X S) e \<and>
              (chain_boundary (Suc p) d) + e = c)"
  using singular_chain_minus
  by (fastforce simp add: singular_relboundary_alt)

lemma singular_boundary:
   "singular_relboundary p X {} c \<longleftrightarrow>
    (\<exists>d. singular_chain (Suc p) X d \<and> chain_boundary (Suc p) d = c)"
  by (simp add: singular_relboundary_def)

lemma singular_boundary_imp_chain:
   "singular_relboundary p X {} c \<Longrightarrow> singular_chain p X c"
  by (auto simp: singular_relboundary singular_chain_boundary_alt singular_chain_empty topspace_subtopology)

lemma singular_boundary_mono:
   "\<lbrakk>T \<subseteq> S; singular_relboundary p (subtopology X T) {} c\<rbrakk>
        \<Longrightarrow> singular_relboundary p (subtopology X S) {} c"
  by (metis mod_subset_empty singular_chain_mono singular_relboundary_def)

lemma singular_relboundary_imp_chain:
   "singular_relboundary p X S c \<Longrightarrow> singular_chain p X c"
  unfolding singular_relboundary singular_chain_subtopology
  by (blast intro: singular_chain_add singular_chain_boundary_alt)

lemma singular_chain_imp_relboundary:
   "singular_chain p (subtopology X S) c \<Longrightarrow> singular_relboundary p X S c"
  unfolding singular_relboundary_def
  using mod_subset_def singular_chain_minus by fastforce

lemma singular_relboundary_0 [simp]: "singular_relboundary p X S 0"
  unfolding singular_relboundary_def
  by (rule_tac x=0 in exI) auto

lemma singular_relboundary_cmul:
   "singular_relboundary p X S c \<Longrightarrow> singular_relboundary p X S (frag_cmul a c)"
  unfolding singular_relboundary_def
  by (metis chain_boundary_cmul mod_subset_cmul singular_chain_cmul)

lemma singular_relboundary_minus:
   "singular_relboundary p X S (-c) \<longleftrightarrow> singular_relboundary p X S c"
  using singular_relboundary_cmul
  by (metis add.inverse_inverse frag_cmul_minus_one)

lemma singular_relboundary_add:
   "\<lbrakk>singular_relboundary p X S a; singular_relboundary p X S b\<rbrakk> \<Longrightarrow> singular_relboundary p X S (a+b)"
  unfolding singular_relboundary_def
  by (metis chain_boundary_add mod_subset_add singular_chain_add)

lemma singular_relboundary_diff:
   "\<lbrakk>singular_relboundary p X S a; singular_relboundary p X S b\<rbrakk> \<Longrightarrow> singular_relboundary p X S (a-b)"
  by (metis uminus_add_conv_diff singular_relboundary_minus singular_relboundary_add)

subsection\<open>The (relative) homology relation\<close>

definition homologous_rel :: "[nat,'a topology,'a set,'a chain,'a chain] \<Rightarrow> bool"
  where "homologous_rel p X S \<equiv> \<lambda>a b. singular_relboundary p X S (a-b)"

abbreviation homologous_rel_set
  where "homologous_rel_set p X S a \<equiv> Collect (homologous_rel p X S a)"

lemma homologous_rel_restrict [simp]:
   "homologous_rel p X (topspace X \<inter> S) = homologous_rel p X S"
  unfolding homologous_rel_def by (metis singular_relboundary_restrict)

lemma homologous_rel_refl [simp]: "homologous_rel p X S c c"
  unfolding homologous_rel_def by auto

lemma homologous_rel_sym:
   "homologous_rel p X S a b = homologous_rel p X S b a"
  unfolding homologous_rel_def
  using singular_relboundary_minus by fastforce

lemma homologous_rel_trans:
  assumes "homologous_rel p X S b c" "homologous_rel p X S a b"
  shows "homologous_rel p X S a c"
  using homologous_rel_def
proof -
  have "singular_relboundary p X S (b - c)"
    using assms unfolding homologous_rel_def by blast
  moreover have "singular_relboundary p X S (b - a)"
    using assms by (meson homologous_rel_def homologous_rel_sym)
  ultimately have "singular_relboundary p X S (c - a)"
    using singular_relboundary_diff by fastforce
  then show ?thesis
    by (meson homologous_rel_def homologous_rel_sym)
qed

lemma homologous_rel_eq:
   "homologous_rel p X S a = homologous_rel p X S b \<longleftrightarrow>
    homologous_rel p X S a b"
  using homologous_rel_sym homologous_rel_trans by fastforce

lemma homologous_rel_set_eq:
   "homologous_rel_set p X S a = homologous_rel_set p X S b \<longleftrightarrow>
    homologous_rel p X S a b"
  by (metis homologous_rel_eq mem_Collect_eq)

lemma homologous_rel_singular_chain:
  "homologous_rel p X S a b \<Longrightarrow> (singular_chain p X a \<longleftrightarrow> singular_chain p X b)"
  unfolding homologous_rel_def
  using singular_chain_diff singular_chain_add
  by (fastforce dest: singular_relboundary_imp_chain)

lemma homologous_rel_add:
   "\<lbrakk>homologous_rel p X S a a'; homologous_rel p X S b b'\<rbrakk>
        \<Longrightarrow> homologous_rel p X S (a+b) (a'+b')"
  unfolding homologous_rel_def
  by (simp add: add_diff_add singular_relboundary_add)

lemma homologous_rel_diff:
  assumes "homologous_rel p X S a a'" "homologous_rel p X S b b'"
  shows "homologous_rel p X S (a - b) (a' - b')"
proof -
  have "singular_relboundary p X S ((a - a') - (b - b'))"
    using assms singular_relboundary_diff unfolding homologous_rel_def by blast
  then show ?thesis
    by (simp add: homologous_rel_def algebra_simps)
qed

lemma homologous_rel_sum:
  assumes f: "finite {i \<in> I. f i \<noteq> 0}" and g: "finite {i \<in> I. g i \<noteq> 0}"
    and h: "\<And>i. i \<in> I \<Longrightarrow> homologous_rel p X S (f i) (g i)"
  shows "homologous_rel p X S (sum f I) (sum g I)"
proof (cases "finite I")
  case True
  let ?L = "{i \<in> I. f i \<noteq> 0} \<union> {i \<in> I. g i \<noteq> 0}"
  have L: "finite ?L" "?L \<subseteq> I"
    using f g by blast+
  have "sum f I = sum f ?L"
    by (rule comm_monoid_add_class.sum.mono_neutral_right [OF True]) auto
  moreover have "sum g I = sum g ?L"
    by (rule comm_monoid_add_class.sum.mono_neutral_right [OF True]) auto
  moreover have *: "homologous_rel p X S (f i) (g i)" if "i \<in> ?L" for i
    using h that by auto
  have "homologous_rel p X S (sum f ?L) (sum g ?L)"
    using L
  proof induction
    case (insert j J)
    then show ?case
      by (simp add: h homologous_rel_add)
  qed auto
  ultimately show ?thesis
    by simp
qed auto


lemma chain_homotopic_imp_homologous_rel:
  assumes
   "\<And>c. singular_chain p X c \<Longrightarrow> singular_chain (Suc p) X' (h c)"
   "\<And>c. singular_chain (p -1) (subtopology X S) c \<Longrightarrow> singular_chain p (subtopology X' T) (h' c)"
   "\<And>c. singular_chain p X c
             \<Longrightarrow> (chain_boundary (Suc p) (h c)) + (h'(chain_boundary p c)) = f c - g c"
    "singular_relcycle p X S c"
  shows "homologous_rel p X' T (f c) (g c)"
proof -
  have "singular_chain p (subtopology X' T) (chain_boundary (Suc p) (h c) - (f c - g c))"
    using assms
    by (metis (no_types, lifting) add_diff_cancel_left' minus_diff_eq singular_chain_minus singular_relcycle)
  then show ?thesis
  using assms
    by (metis homologous_rel_def singular_relboundary singular_relcycle)
qed


subsection\<open>Show that all boundaries are cycles, the key "chain complex" property.\<close>

lemma chain_boundary_boundary:
  assumes "singular_chain p X c"
  shows "chain_boundary (p - Suc 0) (chain_boundary p c) = 0"
proof (cases "p -1 = 0")
  case False
  then have "2 \<le> p"
    by auto
  show ?thesis
    using assms
    unfolding singular_chain_def
  proof (induction rule: frag_induction)
    case (one g)
    then have ss: "singular_simplex p X g"
      by simp
    have eql: "{..p} \<times> {..p - Suc 0} \<inter> {(x, y). y < x} = (\<lambda>(j,i). (Suc i, j)) ` {(i,j). i \<le> j \<and> j \<le> p -1}"
      using False
      by (auto simp: image_def) (metis One_nat_def diff_Suc_1 diff_le_mono le_refl lessE less_imp_le_nat)
    have eqr: "{..p} \<times> {..p - Suc 0} - {(x, y). y < x} = {(i,j). i \<le> j \<and> j \<le> p -1}"
      by auto
    have eqf: "singular_face (p - Suc 0) i (singular_face p (Suc j) g) =
               singular_face (p - Suc 0) j (singular_face p i g)" if "i \<le> j" "j \<le> p - Suc 0" for i j
    proof (rule ext)
      fix t
      show "singular_face (p - Suc 0) i (singular_face p (Suc j) g) t =
            singular_face (p - Suc 0) j (singular_face p i g) t"
      proof (cases "t \<in> standard_simplex (p -1 -1)")
        case True
        have fi: "simplical_face i t \<in> standard_simplex (p - Suc 0)"
          using False True simplical_face_in_standard_simplex that by force
        have fj: "simplical_face j t \<in> standard_simplex (p - Suc 0)"
          by (metis False One_nat_def True simplical_face_in_standard_simplex less_one not_less that(2))
        have eq: "simplical_face (Suc j) (simplical_face i t) = simplical_face i (simplical_face j t)"
          using True that ss
          unfolding standard_simplex_def simplical_face_def by fastforce
        show ?thesis by (simp add: singular_face_def fi fj eq)
      qed (simp add: singular_face_def)
    qed
    show ?case
    proof (cases "p = 1")
      case False
      have eq0: "frag_cmul (-1) a = b \<Longrightarrow> a + b = 0" for a b
        by (simp add: neg_eq_iff_add_eq_0)
      have *: "(\<Sum>x\<le>p. \<Sum>i\<le>p - Suc 0.
                 frag_cmul ((-1) ^ (x + i)) (frag_of (singular_face (p - Suc 0) i (singular_face p x g))))
              = 0"
        apply (simp add: sum.cartesian_product sum.Int_Diff [of "_ \<times> _" _ "{(x,y). y < x}"])
        apply (rule eq0)
        unfolding frag_cmul_sum prod.case_distrib [of "frag_cmul (-1)"] frag_cmul_cmul eql eqr 
        apply (force simp: inj_on_def sum.reindex add.commute eqf intro: sum.cong)
        done
      show ?thesis
        using False by (simp add: chain_boundary_of chain_boundary_sum chain_boundary_cmul frag_cmul_sum * flip: power_add)
    qed (simp add: chain_boundary_def)
  next
    case (diff a b)
    then show ?case
      by (simp add: chain_boundary_diff)
  qed auto
qed (simp add: chain_boundary_def)


lemma chain_boundary_boundary_alt:
   "singular_chain (Suc p) X c \<Longrightarrow> chain_boundary p (chain_boundary (Suc p) c) = 0"
  using chain_boundary_boundary by force

lemma singular_relboundary_imp_relcycle:
  assumes "singular_relboundary p X S c"
  shows "singular_relcycle p X S c"
proof -
  obtain d e where d: "singular_chain (Suc p) X d"
               and e: "singular_chain p (subtopology X S) e"
               and c: "c = chain_boundary (Suc p) d + e"
    using assms by (auto simp: singular_relboundary singular_relcycle)
  have 1: "singular_chain (p - Suc 0) (subtopology X S) (chain_boundary p (chain_boundary (Suc p) d))"
    using d chain_boundary_boundary_alt by fastforce
  have 2: "singular_chain (p - Suc 0) (subtopology X S) (chain_boundary p e)"
    using \<open>singular_chain p (subtopology X S) e\<close> singular_chain_boundary by auto
  have "singular_chain p X c"
    using assms singular_relboundary_imp_chain by auto
  moreover have "singular_chain (p - Suc 0) (subtopology X S) (chain_boundary p c)"
    by (simp add: c chain_boundary_add singular_chain_add 1 2)
  ultimately show ?thesis
    by (simp add: singular_relcycle)
qed

lemma homologous_rel_singular_relcycle_1:
  assumes "homologous_rel p X S c1 c2" "singular_relcycle p X S c1"
  shows "singular_relcycle p X S c2"
  using assms
  by (metis diff_add_cancel homologous_rel_def homologous_rel_sym singular_relboundary_imp_relcycle singular_relcycle_add)

lemma homologous_rel_singular_relcycle:
  assumes "homologous_rel p X S c1 c2"
  shows "singular_relcycle p X S c1 = singular_relcycle p X S c2"
  using assms homologous_rel_singular_relcycle_1
  using homologous_rel_sym by blast


subsection\<open>Operations induced by a continuous map g between topological spaces\<close>

definition simplex_map :: "nat \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> ((nat \<Rightarrow> real) \<Rightarrow> 'b) \<Rightarrow> (nat \<Rightarrow> real) \<Rightarrow> 'a"
  where "simplex_map p g c \<equiv> restrict (g \<circ> c) (standard_simplex p)"

lemma singular_simplex_simplex_map:
   "\<lbrakk>singular_simplex p X f; continuous_map X X' g\<rbrakk>
        \<Longrightarrow> singular_simplex p X' (simplex_map p g f)"
  unfolding singular_simplex_def simplex_map_def
  by (auto simp: continuous_map_compose)

lemma simplex_map_eq:
   "\<lbrakk>singular_simplex p X c;
     \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk>
    \<Longrightarrow> simplex_map p f c = simplex_map p g c"
  by (auto simp: singular_simplex_def simplex_map_def continuous_map_def)

lemma simplex_map_id_gen:
   "\<lbrakk>singular_simplex p X c;
     \<And>x. x \<in> topspace X \<Longrightarrow> f x = x\<rbrakk>
    \<Longrightarrow> simplex_map p f c = c"
  unfolding singular_simplex_def simplex_map_def continuous_map_def
  using extensional_arb by fastforce

lemma simplex_map_id [simp]:
   "simplex_map p id = (\<lambda>c. restrict c (standard_simplex p))"
  by (auto simp: simplex_map_def)

lemma simplex_map_compose:
   "simplex_map p (h \<circ> g) = simplex_map p h \<circ> simplex_map p g"
  unfolding simplex_map_def by force

lemma singular_face_simplex_map:
   "\<lbrakk>1 \<le> p; k \<le> p\<rbrakk>
        \<Longrightarrow> singular_face p k (simplex_map p f c) = simplex_map (p - Suc 0) f (c \<circ> simplical_face k)"
  unfolding simplex_map_def singular_face_def
  by (force simp: simplical_face_in_standard_simplex)

lemma singular_face_restrict [simp]:
  assumes "p > 0" "i \<le> p"
  shows "singular_face p i (restrict f (standard_simplex p)) = singular_face p i f"
  by (metis assms One_nat_def Suc_leI simplex_map_id singular_face_def singular_face_simplex_map)


definition chain_map :: "nat \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> (((nat \<Rightarrow> real) \<Rightarrow> 'b) \<Rightarrow>\<^sub>0 int) \<Rightarrow> 'a chain"
  where "chain_map p g c \<equiv> frag_extend (frag_of \<circ> simplex_map p g) c"

lemma singular_chain_chain_map:
   "\<lbrakk>singular_chain p X c; continuous_map X X' g\<rbrakk> \<Longrightarrow> singular_chain p X' (chain_map p g c)"
  unfolding chain_map_def
  by (force simp add: singular_chain_def subset_iff 
      intro!: singular_chain_extend singular_simplex_simplex_map)

lemma chain_map_0 [simp]: "chain_map p g 0 = 0"
  by (auto simp: chain_map_def)

lemma chain_map_of [simp]: "chain_map p g (frag_of f) = frag_of (simplex_map p g f)"
  by (simp add: chain_map_def)

lemma chain_map_cmul [simp]:
   "chain_map p g (frag_cmul a c) = frag_cmul a (chain_map p g c)"
  by (simp add: frag_extend_cmul chain_map_def)

lemma chain_map_minus: "chain_map p g (-c) = - (chain_map p g c)"
  by (simp add: frag_extend_minus chain_map_def)

lemma chain_map_add:
   "chain_map p g (a+b) = chain_map p g a + chain_map p g b"
  by (simp add: frag_extend_add chain_map_def)

lemma chain_map_diff:
   "chain_map p g (a-b) = chain_map p g a - chain_map p g b"
  by (simp add: frag_extend_diff chain_map_def)

lemma chain_map_sum:
   "finite I \<Longrightarrow> chain_map p g (sum f I) = sum (chain_map p g \<circ> f) I"
  by (simp add: frag_extend_sum chain_map_def)

lemma chain_map_eq:
   "\<lbrakk>singular_chain p X c; \<And>x. x \<in> topspace X \<Longrightarrow> f x = g x\<rbrakk>
    \<Longrightarrow> chain_map p f c = chain_map p g c"
  unfolding singular_chain_def
proof (induction rule: frag_induction)
  case (one x)
  then show ?case
    by (metis (no_types, lifting) chain_map_of mem_Collect_eq simplex_map_eq)
qed (auto simp: chain_map_diff)

lemma chain_map_id_gen:
   "\<lbrakk>singular_chain p X c; \<And>x. x \<in> topspace X \<Longrightarrow> f x = x\<rbrakk>
    \<Longrightarrow>  chain_map p f c = c"
  unfolding singular_chain_def
  by (erule frag_induction) (auto simp: chain_map_diff simplex_map_id_gen)

lemma chain_map_ident:
   "singular_chain p X c \<Longrightarrow> chain_map p id c = c"
  by (simp add: chain_map_id_gen)

lemma chain_map_id:
   "chain_map p id = frag_extend (frag_of \<circ> (\<lambda>f. restrict f (standard_simplex p)))"
  by (auto simp: chain_map_def)

lemma chain_map_compose:
   "chain_map p (h \<circ> g) = chain_map p h \<circ> chain_map p g"
proof
  show "chain_map p (h \<circ> g) c = (chain_map p h \<circ> chain_map p g) c" for c
    using subset_UNIV
  proof (induction c rule: frag_induction)
    case (one x)
    then show ?case
      by simp (metis (mono_tags, lifting) comp_eq_dest_lhs restrict_apply simplex_map_def)
  next
    case (diff a b)
    then show ?case
      by (simp add: chain_map_diff)
  qed auto
qed

lemma singular_simplex_chain_map_id:
  assumes "singular_simplex p X f"
  shows "chain_map p f (frag_of (restrict id (standard_simplex p))) = frag_of f"
proof -
  have "(restrict (f \<circ> restrict id (standard_simplex p)) (standard_simplex p)) = f"
    by (rule ext) (metis assms comp_apply extensional_arb id_apply restrict_apply singular_simplex_def)
  then show ?thesis
    by (simp add: simplex_map_def)
qed

lemma chain_boundary_chain_map:
  assumes "singular_chain p X c"
  shows "chain_boundary p (chain_map p g c) = chain_map (p - Suc 0) g (chain_boundary p c)"
  using assms unfolding singular_chain_def
proof (induction c rule: frag_induction)
  case (one x)
  then have "singular_face p i (simplex_map p g x) = simplex_map (p - Suc 0) g (singular_face p i x)"
    if "0 \<le> i" "i \<le> p" "p \<noteq> 0" for i
    using that
    by (fastforce simp add: singular_face_def simplex_map_def simplical_face_in_standard_simplex)
  then show ?case
    by (auto simp: chain_boundary_of chain_map_sum)
next
  case (diff a b)
  then show ?case
    by (simp add: chain_boundary_diff chain_map_diff)
qed auto

lemma singular_relcycle_chain_map:
  assumes "singular_relcycle p X S c" "continuous_map X X' g" "g ` S \<subseteq> T"
  shows "singular_relcycle p X' T (chain_map p g c)"
proof -
  have "continuous_map (subtopology X S) (subtopology X' T) g"
    using assms
    using continuous_map_from_subtopology continuous_map_in_subtopology topspace_subtopology by fastforce
  then show ?thesis
    using chain_boundary_chain_map [of p X c g]
    by (metis One_nat_def assms(1) assms(2) singular_chain_chain_map singular_relcycle)
qed

lemma singular_relboundary_chain_map:
  assumes "singular_relboundary p X S c" "continuous_map X X' g" "g ` S \<subseteq> T"
  shows "singular_relboundary p X' T (chain_map p g c)"
proof -
  obtain d e where d: "singular_chain (Suc p) X d"
    and e: "singular_chain p (subtopology X S) e" and c: "c = chain_boundary (Suc p) d + e"
    using assms by (auto simp: singular_relboundary)
  have "singular_chain (Suc p) X' (chain_map (Suc p) g d)"
    using assms(2) d singular_chain_chain_map by blast
  moreover have "singular_chain p (subtopology X' T) (chain_map p g e)"
  proof -
    have "\<forall>t. g ` topspace (subtopology t S) \<subseteq> T"
      by (metis assms(3) closure_of_subset_subtopology closure_of_topspace dual_order.trans image_mono)
    then show ?thesis
      by (meson assms(2) continuous_map_from_subtopology continuous_map_in_subtopology e singular_chain_chain_map)
  qed
  moreover have "chain_boundary (Suc p) (chain_map (Suc p) g d) + chain_map p g e =
                 chain_map p g (chain_boundary (Suc p) d + e)"
    by (metis One_nat_def chain_boundary_chain_map chain_map_add d diff_Suc_1)
  ultimately show ?thesis
    unfolding singular_relboundary
    using c by blast
qed


subsection\<open>Homology of one-point spaces degenerates except for $p = 0$.\<close>

lemma singular_simplex_singleton:
  assumes "topspace X = {a}"
  shows "singular_simplex p X f \<longleftrightarrow> f = restrict (\<lambda>x. a) (standard_simplex p)" (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  then show ?rhs
  proof -
    have "continuous_map (subtopology (product_topology (\<lambda>n. euclideanreal) UNIV) (standard_simplex p)) X f"
      using \<open>singular_simplex p X f\<close> singular_simplex_def by blast
    then have "\<And>c. c \<notin> standard_simplex p \<or> f c = a"
      by (simp add: assms continuous_map_def)
    then show ?thesis
      by (metis (no_types) L extensional_restrict restrict_ext singular_simplex_def)
  qed
next
  assume ?rhs
  with assms show ?lhs
    by (auto simp: singular_simplex_def topspace_subtopology)
qed

lemma singular_chain_singleton:
  assumes "topspace X = {a}"
  shows "singular_chain p X c \<longleftrightarrow>
         (\<exists>b. c = frag_cmul b (frag_of(restrict (\<lambda>x. a) (standard_simplex p))))"
    (is "?lhs = ?rhs")
proof
  let ?f = "restrict (\<lambda>x. a) (standard_simplex p)"
  assume L: ?lhs
  with assms have "Poly_Mapping.keys c \<subseteq> {?f}"
    by (auto simp: singular_chain_def singular_simplex_singleton)
  then consider "Poly_Mapping.keys c = {}" | "Poly_Mapping.keys c = {?f}"
    by blast
  then show ?rhs
  proof cases
    case 1
    with L show ?thesis
      by (metis frag_cmul_zero keys_eq_empty)
  next
    case 2
    then have "\<exists>b. frag_extend frag_of c = frag_cmul b (frag_of (\<lambda>x\<in>standard_simplex p. a))"
      by (force simp: frag_extend_def)
    then show ?thesis
      by (metis frag_expansion)
  qed
next
  assume ?rhs
  with assms show ?lhs
    by (auto simp: singular_chain_def singular_simplex_singleton)
qed

lemma chain_boundary_of_singleton:
  assumes tX: "topspace X = {a}" and sc: "singular_chain p X c"
  shows "chain_boundary p c =
         (if p = 0 \<or> odd p then 0
          else frag_extend (\<lambda>f. frag_of(restrict (\<lambda>x. a) (standard_simplex (p -1)))) c)"
    (is "?lhs = ?rhs")
proof (cases "p = 0")
  case False
  have "?lhs = frag_extend (\<lambda>f. if odd p then 0 else frag_of(restrict (\<lambda>x. a) (standard_simplex (p -1)))) c"
  proof (simp only: chain_boundary_def False if_False, rule frag_extend_eq)
    fix f
    assume "f \<in> Poly_Mapping.keys c"
    with assms have "singular_simplex p X f"
      by (auto simp: singular_chain_def)
    then have *: "\<And>k. k \<le> p \<Longrightarrow> singular_face p k f = (\<lambda>x\<in>standard_simplex (p -1). a)"
      using False singular_simplex_singular_face 
      by (fastforce simp flip: singular_simplex_singleton [OF tX])
    define c where "c \<equiv> frag_of (\<lambda>x\<in>standard_simplex (p -1). a)"
    have "(\<Sum>k\<le>p. frag_cmul ((-1) ^ k) (frag_of (singular_face p k f)))
        = (\<Sum>k\<le>p. frag_cmul ((-1) ^ k) c)"
      by (auto simp: c_def * intro: sum.cong)
    also have "\<dots> = (if odd p then 0 else c)"
      by (induction p) (auto simp: c_def restrict_def)
    finally show "(\<Sum>k\<le>p. frag_cmul ((-1) ^ k) (frag_of (singular_face p k f)))
                = (if odd p then 0 else frag_of (\<lambda>x\<in>standard_simplex (p -1). a))"
      unfolding c_def .
  qed
  also have "\<dots> = ?rhs"
    by (auto simp: False frag_extend_eq_0)
  finally show ?thesis .
qed (simp add: chain_boundary_def)


lemma singular_cycle_singleton:
  assumes "topspace X = {a}"
  shows "singular_relcycle p X {} c \<longleftrightarrow> singular_chain p X c \<and> (p = 0 \<or> odd p \<or> c = 0)"
proof -
  have "c = 0" if "singular_chain p X c" and "chain_boundary p c = 0" and "even p" and "p \<noteq> 0"
    using that assms singular_chain_singleton [of X a p c] chain_boundary_of_singleton [OF assms]
    by (auto simp: frag_extend_cmul)
  moreover
  have "chain_boundary p c = 0" if sc: "singular_chain p X c" and "odd p"
    by (simp add: chain_boundary_of_singleton [OF assms sc] that)
  moreover have "chain_boundary 0 c = 0" if "singular_chain 0 X c" and "p = 0"
    by (simp add: chain_boundary_def)
  ultimately show ?thesis
  using assms by (auto simp: singular_cycle)
qed


lemma singular_boundary_singleton:
  assumes "topspace X = {a}"
  shows "singular_relboundary p X {} c \<longleftrightarrow> singular_chain p X c \<and> (odd p \<or> c = 0)"
proof (cases "singular_chain p X c")
  case True
  have "\<exists>d. singular_chain (Suc p) X d \<and> chain_boundary (Suc p) d = c"
    if "singular_chain p X c" and "odd p"
  proof -
    obtain b where b: "c = frag_cmul b (frag_of(restrict (\<lambda>x. a) (standard_simplex p)))"
      by (metis True assms singular_chain_singleton)
    let ?d = "frag_cmul b (frag_of (\<lambda>x\<in>standard_simplex (Suc p). a))"
    have scd: "singular_chain (Suc p) X ?d"
      by (metis assms singular_chain_singleton)
    moreover have "chain_boundary (Suc p) ?d = c"
      by (simp add: assms scd chain_boundary_of_singleton [of X a "Suc p"] b frag_extend_cmul \<open>odd p\<close>)
    ultimately show ?thesis
      by metis
  qed
  with True assms show ?thesis
    by (auto simp: singular_boundary chain_boundary_of_singleton)
next
  case False
  with assms singular_boundary_imp_chain show ?thesis
    by metis
qed


lemma singular_boundary_eq_cycle_singleton:
  assumes "topspace X = {a}" "1 \<le> p"
  shows "singular_relboundary p X {} c \<longleftrightarrow> singular_relcycle p X {} c" (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs"
    by (simp add: singular_relboundary_imp_relcycle)
  show "?rhs \<Longrightarrow> ?lhs"
    by (metis assms not_one_le_zero singular_boundary_singleton singular_cycle_singleton)
qed

lemma singular_boundary_set_eq_cycle_singleton:
  assumes "topspace X = {a}" "1 \<le> p"
  shows "singular_relboundary_set p X {} = singular_relcycle_set p X {}"
  using singular_boundary_eq_cycle_singleton [OF assms]
  by blast

subsection\<open>Simplicial chains\<close>

text\<open>Simplicial chains, effectively those resulting from linear maps.
 We still allow the map to be singular, so the name is questionable.
These are intended as building-blocks for singular subdivision, rather  than as a axis
for 1 simplicial homology.\<close>

definition oriented_simplex
  where "oriented_simplex p l \<equiv> (\<lambda>x\<in>standard_simplex p. \<lambda>i. (\<Sum>j\<le>p. l j i * x j))"

definition simplicial_simplex
  where
 "simplicial_simplex p S f \<equiv>
        singular_simplex p (subtopology (powertop_real UNIV) S) f \<and>
        (\<exists>l. f = oriented_simplex p l)"

lemma simplicial_simplex:
  "simplicial_simplex p S f \<longleftrightarrow> f ` (standard_simplex p) \<subseteq> S \<and> (\<exists>l. f = oriented_simplex p l)"
  (is "?lhs = ?rhs")
proof
  assume R: ?rhs  
  have "continuous_map (subtopology (powertop_real UNIV) (standard_simplex p))
                (powertop_real UNIV) (\<lambda>x i. \<Sum>j\<le>p. l j i * x j)" for l :: " nat \<Rightarrow> 'a \<Rightarrow> real"
    unfolding continuous_map_componentwise
    by (force intro: continuous_intros continuous_map_from_subtopology continuous_map_product_projection)
  with R show ?lhs
    unfolding simplicial_simplex_def singular_simplex_subtopology
    by (auto simp add: singular_simplex_def oriented_simplex_def)
qed (simp add: simplicial_simplex_def singular_simplex_subtopology)

lemma simplicial_simplex_empty [simp]: "\<not> simplicial_simplex p {} f"
  by (simp add: nonempty_standard_simplex simplicial_simplex)

definition simplicial_chain
  where "simplicial_chain p S c \<equiv> Poly_Mapping.keys c \<subseteq> Collect (simplicial_simplex p S)"

lemma simplicial_chain_0 [simp]: "simplicial_chain p S 0"
  by (simp add: simplicial_chain_def)

lemma simplicial_chain_of [simp]:
   "simplicial_chain p S (frag_of c) \<longleftrightarrow> simplicial_simplex p S c"
  by (simp add: simplicial_chain_def)

lemma simplicial_chain_cmul:
   "simplicial_chain p S c \<Longrightarrow> simplicial_chain p S (frag_cmul a c)"
  by (auto simp: simplicial_chain_def)

lemma simplicial_chain_diff:
   "\<lbrakk>simplicial_chain p S c1; simplicial_chain p S c2\<rbrakk> \<Longrightarrow> simplicial_chain p S (c1 - c2)"
  unfolding simplicial_chain_def  by (meson UnE keys_diff subset_iff)

lemma simplicial_chain_sum:
   "(\<And>i. i \<in> I \<Longrightarrow> simplicial_chain p S (f i)) \<Longrightarrow> simplicial_chain p S (sum f I)"
  unfolding simplicial_chain_def
  using order_trans [OF keys_sum [of f I]]
  by (simp add: UN_least)

lemma simplicial_simplex_oriented_simplex:
   "simplicial_simplex p S (oriented_simplex p l)
    \<longleftrightarrow> ((\<lambda>x i. \<Sum>j\<le>p. l j i * x j) ` standard_simplex p \<subseteq> S)"
  by (auto simp: simplicial_simplex oriented_simplex_def)

lemma simplicial_imp_singular_simplex:
   "simplicial_simplex p S f
      \<Longrightarrow> singular_simplex p (subtopology (powertop_real UNIV) S) f"
  by (simp add: simplicial_simplex_def)

lemma simplicial_imp_singular_chain:
   "simplicial_chain p S c
      \<Longrightarrow> singular_chain p (subtopology (powertop_real UNIV) S) c"
  unfolding simplicial_chain_def singular_chain_def
  by (auto intro: simplicial_imp_singular_simplex)

lemma oriented_simplex_eq:
  "oriented_simplex p l = oriented_simplex p l' \<longleftrightarrow> (\<forall>i. i \<le> p \<longrightarrow> l i = l' i)"
  (is "?lhs = ?rhs")
proof
  assume L: ?lhs
  show ?rhs
  proof clarify
    fix i
    assume "i \<le> p"
    let ?fi = "(\<lambda>j. if j = i then 1 else 0)"
    have "(\<Sum>j\<le>p. l j k * ?fi j) = (\<Sum>j\<le>p. l' j k * ?fi j)" for k
      using L \<open>i \<le> p\<close>
      by (simp add: fun_eq_iff oriented_simplex_def split: if_split_asm)
    with \<open>i \<le> p\<close> show "l i = l' i"
      by (simp add: if_distrib ext cong: if_cong)
  qed
qed (auto simp: oriented_simplex_def)

lemma singular_face_oriented_simplex:
  assumes "1 \<le> p" "k \<le> p"
  shows "singular_face p k (oriented_simplex p l) =
         oriented_simplex (p -1) (\<lambda>j. if j < k then l j else l (Suc j))"
proof -
  have "(\<Sum>j\<le>p. l j i * simplical_face k x j)
      = (\<Sum>j\<le>p - Suc 0. (if j < k then l j else l (Suc j)) i * x j)"
    if "x \<in> standard_simplex (p - Suc 0)" for i x
  proof -
    show ?thesis
      unfolding simplical_face_def
      using sum.zero_middle [OF assms, where 'a=real, symmetric]
      by (simp add: if_distrib [of "\<lambda>x. _ * x"] if_distrib [of "\<lambda>f. f i * _"] atLeast0AtMost cong: if_cong)
  qed
  then show ?thesis
    using simplical_face_in_standard_simplex assms
    by (auto simp: singular_face_def oriented_simplex_def restrict_def)
qed

lemma simplicial_simplex_singular_face:
  fixes f :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real"
  assumes ss: "simplicial_simplex p S f" and p: "1 \<le> p" "k \<le> p"
  shows "simplicial_simplex (p - Suc 0) S (singular_face p k f)"
proof -
  let ?X = "subtopology (powertop_real UNIV) S"
  obtain m where l: "singular_simplex p ?X (oriented_simplex p m)"
       and feq: "f = oriented_simplex p m"
    using assms by (force simp: simplicial_simplex_def)
  moreover   
  have "singular_face p k f = oriented_simplex (p - Suc 0) (\<lambda>i. if i < k then m i else m (Suc i))"
    unfolding feq singular_face_def oriented_simplex_def
    apply (simp add: simplical_face_in_standard_simplex [OF p] restrict_compose_left subset_eq)
    using sum.zero_middle [OF p, where 'a=real, symmetric]  unfolding simplical_face_def o_def
    apply (simp add: if_distrib [of "\<lambda>x. _ * x"] if_distrib [of "\<lambda>f. f _ * _"] atLeast0AtMost cong: if_cong)
    done
  ultimately
  show ?thesis
    using p simplicial_simplex_def singular_simplex_singular_face by blast
qed

lemma simplicial_chain_boundary:
   "simplicial_chain p S c \<Longrightarrow> simplicial_chain (p -1) S (chain_boundary p c)"
  unfolding simplicial_chain_def
proof (induction rule: frag_induction)
  case (one f)
  then have "simplicial_simplex p S f"
    by simp
  have "simplicial_chain (p - Suc 0) S (frag_of (singular_face p i f))"
    if "0 < p" "i \<le> p" for i
    using that one
    by (force simp: simplicial_simplex_def singular_simplex_singular_face singular_face_oriented_simplex)
  then have "simplicial_chain (p - Suc 0) S (chain_boundary p (frag_of f))"
    unfolding chain_boundary_def frag_extend_of
    by (auto intro!: simplicial_chain_cmul simplicial_chain_sum)
  then show ?case
    by (simp add: simplicial_chain_def [symmetric])
next
  case (diff a b)
  then show ?case
    by (metis chain_boundary_diff simplicial_chain_def simplicial_chain_diff)
qed auto


subsection\<open>The cone construction on simplicial simplices.\<close>

consts simplex_cone :: "[nat, nat \<Rightarrow> real, [nat \<Rightarrow> real, nat] \<Rightarrow> real, nat \<Rightarrow> real, nat] \<Rightarrow> real"
specification (simplex_cone)
  simplex_cone:
    "\<And>p v l. simplex_cone p v (oriented_simplex p l) =
          oriented_simplex (Suc p) (\<lambda>i. if i = 0 then v else l(i -1))"
proof -
  have *: "\<And>x. \<exists>y. \<forall>v. (\<lambda>l. oriented_simplex (Suc x) (\<lambda>i. if i = 0 then v else l (i -1)))
                  = (y v \<circ> (oriented_simplex x))"
    apply (subst choice_iff [symmetric])
    by (simp add: oriented_simplex_eq  choice_iff [symmetric] function_factors_left [symmetric])
  then show ?thesis
    unfolding o_def by (metis(no_types))
qed

lemma simplicial_simplex_simplex_cone:
  assumes f: "simplicial_simplex p S f"
    and T: "\<And>x u. \<lbrakk>0 \<le> u; u \<le> 1; x \<in> S\<rbrakk> \<Longrightarrow> (\<lambda>i. (1 - u) * v i + u * x i) \<in> T"
  shows "simplicial_simplex (Suc p) T (simplex_cone p v f)"
proof -
  obtain l where l: "\<And>x. x \<in> standard_simplex p \<Longrightarrow> oriented_simplex p l x \<in> S"
    and feq: "f = oriented_simplex p l"
    using f by (auto simp: simplicial_simplex)
  have "oriented_simplex p l x \<in> S" if "x \<in> standard_simplex p" for x
    using f that by (auto simp: simplicial_simplex feq)
  then have S: "\<And>x. \<lbrakk>\<And>i. 0 \<le> x i \<and> x i \<le> 1; \<And>i. i>p \<Longrightarrow> x i = 0; sum x {..p} = 1\<rbrakk>
                 \<Longrightarrow> (\<lambda>i. \<Sum>j\<le>p. l j i * x j) \<in> S"
    by (simp add: oriented_simplex_def standard_simplex_def)
  have "oriented_simplex (Suc p) (\<lambda>i. if i = 0 then v else l (i -1)) x \<in> T"
    if "x \<in> standard_simplex (Suc p)" for x
  proof (simp add: that oriented_simplex_def sum.atMost_Suc_shift del: sum.atMost_Suc)
    have x01: "\<And>i. 0 \<le> x i \<and> x i \<le> 1" and x0: "\<And>i. i > Suc p \<Longrightarrow> x i = 0" and x1: "sum x {..Suc p} = 1"
      using that by (auto simp: oriented_simplex_def standard_simplex_def)
    obtain a where "a \<in> S"
      using f by force
    show "(\<lambda>i. v i * x 0 + (\<Sum>j\<le>p. l j i * x (Suc j))) \<in> T"
    proof (cases "x 0 = 1")
      case True
      then have "sum x {Suc 0..Suc p} = 0"
        using x1 by (simp add: atMost_atLeast0 sum.atLeast_Suc_atMost)
      then have [simp]: "x (Suc j) = 0" if "j\<le>p" for j
        unfolding sum.atLeast_Suc_atMost_Suc_shift
        using x01 that by (simp add: sum_nonneg_eq_0_iff)
      then show ?thesis
        using T [of 0 a] \<open>a \<in> S\<close> by (auto simp: True)
    next
      case False
      then have "(\<lambda>i. v i * x 0 + (\<Sum>j\<le>p. l j i * x (Suc j))) = (\<lambda>i. (1 - (1 - x 0)) * v i + (1 - x 0) * (inverse (1 - x 0) * (\<Sum>j\<le>p. l j i * x (Suc j))))"
        by (force simp: field_simps)
      also have "\<dots> \<in> T"
      proof (rule T)
        have "x 0 < 1"
          by (simp add: False less_le x01)
        have xle: "x (Suc i) \<le> (1 - x 0)" for i
        proof (cases "i \<le> p")
          case True
          have "sum x {0, Suc i} \<le> sum x {..Suc p}"
            by (rule sum_mono2) (auto simp: True x01)
          then show ?thesis
           using x1 x01 by (simp add: algebra_simps not_less)
        qed (simp add: x0 x01)
        have "(\<lambda>i. (\<Sum>j\<le>p. l j i * (x (Suc j) * inverse (1 - x 0)))) \<in> S"
        proof (rule S)
          have "x 0 + (\<Sum>j\<le>p. x (Suc j)) = sum x {..Suc p}"
            by (metis sum.atMost_Suc_shift)
          with x1 have "(\<Sum>j\<le>p. x (Suc j)) = 1 - x 0"
            by simp
          with False show "(\<Sum>j\<le>p. x (Suc j) * inverse (1 - x 0)) = 1"
            by (metis add_diff_cancel_left' diff_diff_eq2 diff_zero right_inverse sum_distrib_right)
      qed (use x01 x0 xle \<open>x 0 < 1\<close> in \<open>auto simp: field_split_simps\<close>)
      then show "(\<lambda>i. inverse (1 - x 0) * (\<Sum>j\<le>p. l j i * x (Suc j))) \<in> S"
        by (simp add: field_simps sum_divide_distrib)
    qed (use x01 in auto)
    finally show ?thesis .
  qed
qed
  then show ?thesis
    by (auto simp: simplicial_simplex feq  simplex_cone)
qed

definition simplicial_cone
  where "simplicial_cone p v \<equiv> frag_extend (frag_of \<circ> simplex_cone p v)"

lemma simplicial_chain_simplicial_cone:
  assumes c: "simplicial_chain p S c"
    and T: "\<And>x u. \<lbrakk>0 \<le> u; u \<le> 1; x \<in> S\<rbrakk> \<Longrightarrow> (\<lambda>i. (1 - u) * v i + u * x i) \<in> T"
  shows "simplicial_chain (Suc p) T (simplicial_cone p v c)"
  using c unfolding simplicial_chain_def simplicial_cone_def
proof (induction rule: frag_induction)
  case (one x)
  then show ?case
    by (simp add: T simplicial_simplex_simplex_cone)
next
  case (diff a b)
  then show ?case
    by (metis frag_extend_diff simplicial_chain_def simplicial_chain_diff)
qed auto


lemma chain_boundary_simplicial_cone_of':
  assumes "f = oriented_simplex p l"
  shows "chain_boundary (Suc p) (simplicial_cone p v (frag_of f)) =
         frag_of f
         - (if p = 0 then frag_of (\<lambda>u\<in>standard_simplex p. v)
            else simplicial_cone (p -1) v (chain_boundary p (frag_of f)))"
proof (simp, intro impI conjI)
  assume "p = 0"
  have eq: "(oriented_simplex 0 (\<lambda>j. if j = 0 then v else l j)) = (\<lambda>u\<in>standard_simplex 0. v)"
    by (force simp: oriented_simplex_def standard_simplex_def)
  show "chain_boundary (Suc 0) (simplicial_cone 0 v (frag_of f))
        = frag_of f - frag_of (\<lambda>u\<in>standard_simplex 0. v)"
    by (simp add: assms simplicial_cone_def chain_boundary_of \<open>p = 0\<close> simplex_cone singular_face_oriented_simplex eq cong: if_cong)
next
  assume "0 < p"
  have 0: "simplex_cone (p - Suc 0) v (singular_face p x (oriented_simplex p l))
         = oriented_simplex p
              (\<lambda>j. if j < Suc x
                   then if j = 0 then v else l (j -1)
                   else if Suc j = 0 then v else l (Suc j -1))" if "x \<le> p" for x
    using \<open>0 < p\<close> that
    by (auto simp: Suc_leI singular_face_oriented_simplex simplex_cone oriented_simplex_eq)
  have 1: "frag_extend (frag_of \<circ> simplex_cone (p - Suc 0) v)
                     (\<Sum>k = 0..p. frag_cmul ((-1) ^ k) (frag_of (singular_face p k (oriented_simplex p l))))
         = - (\<Sum>k = Suc 0..Suc p. frag_cmul ((-1) ^ k)
               (frag_of (singular_face (Suc p) k (simplex_cone p v (oriented_simplex p l)))))"
    unfolding sum.atLeast_Suc_atMost_Suc_shift
    by (auto simp: 0 simplex_cone singular_face_oriented_simplex frag_extend_sum frag_extend_cmul simp flip: sum_negf)
  moreover have 2: "singular_face (Suc p) 0 (simplex_cone p v (oriented_simplex p l))
                    = oriented_simplex p l"
    by (simp add: simplex_cone singular_face_oriented_simplex)
  show "chain_boundary (Suc p) (simplicial_cone p v (frag_of f))
        = frag_of f - simplicial_cone (p - Suc 0) v (chain_boundary p (frag_of f))"
    using \<open>p > 0\<close>
    apply (simp add: assms simplicial_cone_def chain_boundary_of atMost_atLeast0 del: sum.atMost_Suc)
    apply (subst sum.atLeast_Suc_atMost [of 0])
     apply (simp_all add: 1 2 del: sum.atMost_Suc)
    done
qed

lemma chain_boundary_simplicial_cone_of:
  assumes "simplicial_simplex p S f"
  shows "chain_boundary (Suc p) (simplicial_cone p v (frag_of f)) =
         frag_of f
         - (if p = 0 then frag_of (\<lambda>u\<in>standard_simplex p. v)
            else simplicial_cone (p -1) v (chain_boundary p (frag_of f)))"
  using chain_boundary_simplicial_cone_of' assms unfolding simplicial_simplex_def
  by blast

lemma chain_boundary_simplicial_cone:
  "simplicial_chain p S c
   \<Longrightarrow> chain_boundary (Suc p) (simplicial_cone p v c) =
       c - (if p = 0 then frag_extend (\<lambda>f. frag_of (\<lambda>u\<in>standard_simplex p. v)) c
            else simplicial_cone (p -1) v (chain_boundary p c))"
  unfolding simplicial_chain_def
proof (induction rule: frag_induction)
  case (one x)
  then show ?case
    by (auto simp: chain_boundary_simplicial_cone_of)
qed (auto simp: chain_boundary_diff simplicial_cone_def frag_extend_diff)

lemma simplex_map_oriented_simplex:
  assumes l: "simplicial_simplex p (standard_simplex q) (oriented_simplex p l)"
    and g: "simplicial_simplex r S g" and "q \<le> r"
  shows "simplex_map p g (oriented_simplex p l) = oriented_simplex p (g \<circ> l)"
proof -
  obtain m where geq: "g = oriented_simplex r m"
    using g by (auto simp: simplicial_simplex_def)
  have "g (\<lambda>i. \<Sum>j\<le>p. l j i * x j) i = (\<Sum>j\<le>p. g (l j) i * x j)"
    if "x \<in> standard_simplex p" for x i
  proof -
    have ssr: "(\<lambda>i. \<Sum>j\<le>p. l j i * x j) \<in> standard_simplex r"
      using l that standard_simplex_mono [OF \<open>q \<le> r\<close>]
      unfolding simplicial_simplex_oriented_simplex by auto
    have lss: "l j \<in> standard_simplex r" if "j\<le>p" for j
    proof -
      have q: "(\<lambda>x i. \<Sum>j\<le>p. l j i * x j) ` standard_simplex p \<subseteq> standard_simplex q"
        using l by (simp add: simplicial_simplex_oriented_simplex)
      let ?x = "(\<lambda>i. if i = j then 1 else 0)"
      have p: "l j \<in> (\<lambda>x i. \<Sum>j\<le>p. l j i * x j) ` standard_simplex p"
      proof
        show "l j = (\<lambda>i. \<Sum>j\<le>p. l j i * ?x j)"
          using \<open>j\<le>p\<close> by (force simp: if_distrib cong: if_cong)
        show "?x \<in> standard_simplex p"
          by (simp add: that)
      qed
      show ?thesis
        using standard_simplex_mono [OF \<open>q \<le> r\<close>] q p
        by blast
    qed
    have "g (\<lambda>i. \<Sum>j\<le>p. l j i * x j) i = (\<Sum>j\<le>r. \<Sum>n\<le>p. m j i * (l n j * x n))"
      by (simp add: geq oriented_simplex_def sum_distrib_left ssr)
    also have "... =  (\<Sum>j\<le>p. \<Sum>n\<le>r. m n i * (l j n * x j))"
      by (rule sum.swap)
    also have "... = (\<Sum>j\<le>p. g (l j) i * x j)"
      by (simp add: geq oriented_simplex_def sum_distrib_right mult.assoc lss)
    finally show ?thesis .
  qed
  then show ?thesis
    by (force simp: oriented_simplex_def simplex_map_def o_def)
qed


lemma chain_map_simplicial_cone:
  assumes g: "simplicial_simplex r S g"
      and c: "simplicial_chain p (standard_simplex q) c"
      and v: "v \<in> standard_simplex q" and "q \<le> r"
  shows "chain_map (Suc p) g (simplicial_cone p v c) = simplicial_cone p (g v) (chain_map p g c)"
proof -
  have *: "simplex_map (Suc p) g (simplex_cone p v f) = simplex_cone p (g v) (simplex_map p g f)"
    if "f \<in> Poly_Mapping.keys c" for f
  proof -
    have "simplicial_simplex p (standard_simplex q) f"
      using c that by (auto simp: simplicial_chain_def)
    then obtain m where feq: "f = oriented_simplex p m"
      by (auto simp: simplicial_simplex)
    have 0: "simplicial_simplex p (standard_simplex q) (oriented_simplex p m)"
      using \<open>simplicial_simplex p (standard_simplex q) f\<close> feq by blast
    then have 1: "simplicial_simplex (Suc p) (standard_simplex q)
                      (oriented_simplex (Suc p) (\<lambda>i. if i = 0 then v else m (i -1)))"
      using convex_standard_simplex v
      by (simp flip: simplex_cone add: simplicial_simplex_simplex_cone)
    show ?thesis
      using simplex_map_oriented_simplex [OF 1 g \<open>q \<le> r\<close>]
            simplex_map_oriented_simplex [of p q m r S g, OF 0 g \<open>q \<le> r\<close>]
      by (simp add: feq oriented_simplex_eq simplex_cone)
  qed
  show ?thesis
    by (auto simp: chain_map_def simplicial_cone_def frag_extend_compose * intro: frag_extend_eq)
qed


subsection\<open>Barycentric subdivision of a linear ("simplicial") simplex's image\<close>

definition simplicial_vertex
  where "simplicial_vertex i f = f(\<lambda>j. if j = i then 1 else 0)"

lemma simplicial_vertex_oriented_simplex:
   "simplicial_vertex i (oriented_simplex p l) = (if i \<le> p then l i else undefined)"
  by (simp add: simplicial_vertex_def oriented_simplex_def if_distrib cong: if_cong)


primrec simplicial_subdivision
where
  "simplicial_subdivision 0 = id"
| "simplicial_subdivision (Suc p) =
     frag_extend
      (\<lambda>f. simplicial_cone p
            (\<lambda>i. (\<Sum>j\<le>Suc p. simplicial_vertex j f i) / (p + 2))
            (simplicial_subdivision p (chain_boundary (Suc p) (frag_of f))))"


lemma simplicial_subdivision_0 [simp]:
   "simplicial_subdivision p 0 = 0"
  by (induction p) auto

lemma simplicial_subdivision_diff:
   "simplicial_subdivision p (c1-c2) = simplicial_subdivision p c1 - simplicial_subdivision p c2"
  by (induction p) (auto simp: frag_extend_diff)

lemma simplicial_subdivision_of:
   "simplicial_subdivision p (frag_of f) =
         (if p = 0 then frag_of f
         else simplicial_cone (p -1)
               (\<lambda>i. (\<Sum>j\<le>p. simplicial_vertex j f i) / (Suc p))
               (simplicial_subdivision (p -1) (chain_boundary p (frag_of f))))"
  by (induction p) (auto simp: add.commute)


lemma simplicial_chain_simplicial_subdivision:
   "simplicial_chain p S c
           \<Longrightarrow> simplicial_chain p S (simplicial_subdivision p c)"
proof (induction p arbitrary: S c)
  case (Suc p)
  show ?case
    using Suc.prems [unfolded simplicial_chain_def]
  proof (induction c rule: frag_induction)
    case (one f)
    then have f: "simplicial_simplex (Suc p) S f"
      by auto
    then have "simplicial_chain p (f ` standard_simplex (Suc p))
                 (simplicial_subdivision p (chain_boundary (Suc p) (frag_of f)))"
      by (metis Suc.IH diff_Suc_1 simplicial_chain_boundary simplicial_chain_of simplicial_simplex subsetI)
    moreover
    obtain l where l: "\<And>x. x \<in> standard_simplex (Suc p) \<Longrightarrow> (\<lambda>i. (\<Sum>j\<le>Suc p. l j i * x j)) \<in> S"
      and feq: "f = oriented_simplex (Suc p) l"
      using f by (fastforce simp: simplicial_simplex oriented_simplex_def simp del: sum.atMost_Suc)
    have "(\<lambda>i. (1 - u) * ((\<Sum>j\<le>Suc p. simplicial_vertex j f i) / (real p + 2)) + u * y i) \<in> S"
      if "0 \<le> u" "u \<le> 1" and y: "y \<in> f ` standard_simplex (Suc p)" for y u
    proof -
      obtain x where x: "x \<in> standard_simplex (Suc p)" and yeq: "y = oriented_simplex (Suc p) l x"
        using y feq by blast
      have "(\<lambda>i. \<Sum>j\<le>Suc p. l j i * ((if j \<le> Suc p then (1 - u) * inverse (p + 2) + u * x j else 0))) \<in> S"
      proof (rule l)
        have "inverse (2 + real p) \<le> 1" "(2 + real p) * ((1 - u) * inverse (2 + real p)) + u = 1"
          by (auto simp add: field_split_simps)
        then show "(\<lambda>j. if j \<le> Suc p then (1 - u) * inverse (real (p + 2)) + u * x j else 0) \<in> standard_simplex (Suc p)"
          using x \<open>0 \<le> u\<close> \<open>u \<le> 1\<close>
          by (simp add: sum.distrib standard_simplex_def linepath_le_1 flip: sum_distrib_left del: sum.atMost_Suc)
      qed
      moreover have "(\<lambda>i. \<Sum>j\<le>Suc p. l j i * ((1 - u) * inverse (2 + real p) + u * x j))
                   = (\<lambda>i. (1 - u) * (\<Sum>j\<le>Suc p. l j i) / (real p + 2) + u * (\<Sum>j\<le>Suc p. l j i * x j))"
      proof
        fix i
        have "(\<Sum>j\<le>Suc p. l j i * ((1 - u) * inverse (2 + real p) + u * x j))
            = (\<Sum>j\<le>Suc p. (1 - u) * l j i / (real p + 2) + u * l j i * x j)" (is "?lhs = _")
          by (simp add: field_simps cong: sum.cong)
        also have "\<dots> = (1 - u) * (\<Sum>j\<le>Suc p. l j i) / (real p + 2) + u * (\<Sum>j\<le>Suc p. l j i * x j)" (is "_ = ?rhs")
          by (simp add: sum_distrib_left sum.distrib sum_divide_distrib mult.assoc del: sum.atMost_Suc)
        finally show "?lhs = ?rhs" .
      qed
      ultimately show ?thesis
        using feq x yeq
        by (simp add: simplicial_vertex_oriented_simplex) (simp add: oriented_simplex_def)
    qed
    ultimately show ?case
      by (simp add: simplicial_chain_simplicial_cone)
  next
    case (diff a b)
    then show ?case
      by (metis simplicial_chain_diff simplicial_subdivision_diff)
  qed auto
qed auto

lemma chain_boundary_simplicial_subdivision:
   "simplicial_chain p S c
    \<Longrightarrow> chain_boundary p (simplicial_subdivision p c) = simplicial_subdivision (p -1) (chain_boundary p c)"
proof (induction p arbitrary: c)
  case (Suc p)
  show ?case
    using Suc.prems [unfolded simplicial_chain_def]
  proof (induction c rule: frag_induction)
    case (one f)
    then have f: "simplicial_simplex (Suc p) S f"
      by simp
    then have "simplicial_chain p S (simplicial_subdivision p (chain_boundary (Suc p) (frag_of f)))"
      by (metis diff_Suc_1 simplicial_chain_boundary simplicial_chain_of simplicial_chain_simplicial_subdivision)
    moreover have "simplicial_chain p S (chain_boundary (Suc p) (frag_of f))"
      using one simplicial_chain_boundary simplicial_chain_of by fastforce
    moreover have "simplicial_subdivision (p - Suc 0) (chain_boundary p (chain_boundary (Suc p) (frag_of f))) = 0"
      by (metis f chain_boundary_boundary_alt simplicial_simplex_def simplicial_subdivision_0 singular_chain_of)
    ultimately show ?case
      using chain_boundary_simplicial_cone Suc
      by (auto simp: chain_boundary_of frag_extend_diff simplicial_cone_def)
  next
    case (diff a b)
    then show ?case
      by (simp add: simplicial_subdivision_diff chain_boundary_diff frag_extend_diff)
  qed auto
qed auto


text \<open>A MESS AND USED ONLY ONCE\<close>
lemma simplicial_subdivision_shrinks:
   "\<lbrakk>simplicial_chain p S c;
     \<And>f x y. \<lbrakk>f \<in> Poly_Mapping.keys c; x \<in> standard_simplex p; y \<in> standard_simplex p\<rbrakk> \<Longrightarrow> \<bar>f x k - f y k\<bar> \<le> d;
     f \<in> Poly_Mapping.keys(simplicial_subdivision p c);
     x \<in> standard_simplex p; y \<in> standard_simplex p\<rbrakk>
    \<Longrightarrow> \<bar>f x k - f y k\<bar> \<le> (p / (Suc p)) * d"
proof (induction p arbitrary: d c f x y)
  case (Suc p)
  define Sigp where "Sigp \<equiv> \<lambda>f:: (nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real. \<lambda>i. (\<Sum>j\<le>Suc p. simplicial_vertex j f i) / real (p + 2)"
  let ?CB = "\<lambda>f. chain_boundary (Suc p) (frag_of f)"
  have *: "Poly_Mapping.keys
             (simplicial_cone p (Sigp f)
               (simplicial_subdivision p (?CB f)))
           \<subseteq> {f. \<forall>x\<in>standard_simplex (Suc p). \<forall>y\<in>standard_simplex (Suc p).
                      \<bar>f x k - f y k\<bar> \<le> real (Suc p) / (real p + 2) * d}" (is "?lhs \<subseteq> ?rhs")
    if f: "f \<in> Poly_Mapping.keys c" for f
  proof -
    have ssf: "simplicial_simplex (Suc p) S f"
      using Suc.prems(1) simplicial_chain_def that by auto
    have 2: "\<And>x y. \<lbrakk>x \<in> standard_simplex (Suc p); y \<in> standard_simplex (Suc p)\<rbrakk> \<Longrightarrow> \<bar>f x k - f y k\<bar> \<le> d"
      by (meson Suc.prems(2) f subsetD le_Suc_eq order_refl standard_simplex_mono)
    have sub: "Poly_Mapping.keys ((frag_of \<circ> simplex_cone p (Sigp f)) g) \<subseteq> ?rhs"
      if "g \<in> Poly_Mapping.keys (simplicial_subdivision p (?CB f))" for g
    proof -
      have 1: "simplicial_chain p S (?CB f)"
        using ssf simplicial_chain_boundary simplicial_chain_of by fastforce
      have "simplicial_chain (Suc p) (f ` standard_simplex(Suc p)) (frag_of f)"
        by (metis simplicial_chain_of simplicial_simplex ssf subset_refl)
      then have sc_sub: "Poly_Mapping.keys (?CB f)
                         \<subseteq> Collect (simplicial_simplex p (f ` standard_simplex (Suc p)))"
        by (metis diff_Suc_1 simplicial_chain_boundary simplicial_chain_def)
      have led: "\<And>h x y. \<lbrakk>h \<in> Poly_Mapping.keys (chain_boundary (Suc p) (frag_of f));
                          x \<in> standard_simplex p; y \<in> standard_simplex p\<rbrakk> \<Longrightarrow> \<bar>h x k - h y k\<bar> \<le> d"
        using Suc.prems(2) f sc_sub
        by (simp add: simplicial_simplex subset_iff image_iff) metis
      have "\<And>f' x y. \<lbrakk>f' \<in> Poly_Mapping.keys (simplicial_subdivision p (?CB f)); x \<in> standard_simplex p; y \<in> standard_simplex p\<rbrakk>
            \<Longrightarrow> \<bar>f' x k - f' y k\<bar> \<le> (p / (Suc p)) * d"
        by (blast intro: led Suc.IH [of "chain_boundary (Suc p) (frag_of f)", OF 1])
      then have g: "\<And>x y. \<lbrakk>x \<in> standard_simplex p; y \<in> standard_simplex p\<rbrakk> \<Longrightarrow> \<bar>g x k - g y k\<bar> \<le> (p / (Suc p)) * d"
        using that by blast
      have "d \<ge> 0"
        using Suc.prems(2)[OF f] \<open>x \<in> standard_simplex (Suc p)\<close> by force
      have 3: "simplex_cone p (Sigp f) g \<in> ?rhs"
      proof -
        have "simplicial_simplex p (f ` standard_simplex(Suc p)) g"
          by (metis (mono_tags, hide_lams) sc_sub mem_Collect_eq simplicial_chain_def simplicial_chain_simplicial_subdivision subsetD that)
        then obtain m where m: "g ` standard_simplex p \<subseteq> f ` standard_simplex (Suc p)"
          and geq: "g = oriented_simplex p m"
          using ssf by (auto simp: simplicial_simplex)
        have m_in_gim: "m i \<in> g ` standard_simplex p" if "i \<le> p" for i
        proof 
          show "m i = g (\<lambda>j. if j = i then 1 else 0)"
            by (simp add: geq oriented_simplex_def that if_distrib cong: if_cong)
          show "(\<lambda>j. if j = i then 1 else 0) \<in> standard_simplex p"
            by (simp add: oriented_simplex_def that)
        qed
        obtain l where l: "f ` standard_simplex (Suc p) \<subseteq> S"
          and feq: "f = oriented_simplex (Suc p) l"
          using ssf by (auto simp: simplicial_simplex)
        show ?thesis
        proof (clarsimp simp add: geq simp del: sum.atMost_Suc)
          fix x y
          assume x: "x \<in> standard_simplex (Suc p)" and y: "y \<in> standard_simplex (Suc p)"
          then have x': "(\<forall>i. 0 \<le> x i \<and> x i \<le> 1) \<and> (\<forall>i>Suc p. x i = 0) \<and> (\<Sum>i\<le>Suc p. x i) = 1"
            and y': "(\<forall>i. 0 \<le> y i \<and> y i \<le> 1) \<and> (\<forall>i>Suc p. y i = 0) \<and> (\<Sum>i\<le>Suc p. y i) = 1"
            by (auto simp: standard_simplex_def)
          have "\<bar>(\<Sum>j\<le>Suc p. (if j = 0 then \<lambda>i. (\<Sum>j\<le>Suc p. l j i) / (2 + real p) else m (j -1)) k * x j) -
                 (\<Sum>j\<le>Suc p. (if j = 0 then \<lambda>i. (\<Sum>j\<le>Suc p. l j i) / (2 + real p) else m (j -1)) k * y j)\<bar>
                \<le> (1 + real p) * d / (2 + real p)"
          proof -
            have zero: "\<bar>m (s - Suc 0) k - (\<Sum>j\<le>Suc p. l j k) / (2 + real p)\<bar> \<le> (1 + real p) * d / (2 + real p)"
              if "0 < s" and "s \<le> Suc p" for s
            proof -
              have "m (s - Suc 0) \<in> f ` standard_simplex (Suc p)"
                using m m_in_gim that(2) by auto
              then obtain z where eq: "m (s - Suc 0) = (\<lambda>i. \<Sum>j\<le>Suc p. l j i * z j)" and z: "z \<in> standard_simplex (Suc p)"
                using feq unfolding oriented_simplex_def by auto
              show ?thesis
                unfolding eq
              proof (rule convex_sum_bound_le)
                fix i
                assume i: "i \<in> {..Suc p}"
                then have [simp]: "card ({..Suc p} - {i}) = Suc p"
                  by (simp add: card_Suc_Diff1)
                have "(\<Sum>j\<le>Suc p. \<bar>l i k / (p + 2) - l j k / (p + 2)\<bar>) = (\<Sum>j\<le>Suc p. \<bar>l i k - l j k\<bar> / (p + 2))"
                  by (rule sum.cong) (simp_all add: flip: diff_divide_distrib)
                also have "\<dots> = (\<Sum>j \<in> {..Suc p} - {i}. \<bar>l i k - l j k\<bar> / (p + 2))"
                  by (rule sum.mono_neutral_right) auto
                also have "\<dots> \<le> (1 + real p) * d / (p + 2)"
                proof (rule sum_bounded_above_divide)
                  fix i' :: "nat"
                  assume i': "i' \<in> {..Suc p} - {i}"
                  have lf: "l r \<in> f ` standard_simplex(Suc p)" if "r \<le> Suc p" for r
                  proof
                    show "l r = f (\<lambda>j. if j = r then 1 else 0)"
                      using that by (simp add: feq oriented_simplex_def if_distrib cong: if_cong)
                    show "(\<lambda>j. if j = r then 1 else 0) \<in> standard_simplex (Suc p)"
                      by (auto simp: oriented_simplex_def that)
                  qed
                  show "\<bar>l i k - l i' k\<bar> / real (p + 2) \<le> (1 + real p) * d / real (p + 2) / real (card ({..Suc p} - {i}))"
                    using i i' lf [of i] lf [of i'] 2
                    by (auto simp: image_iff divide_simps)
                qed auto
                finally have "(\<Sum>j\<le>Suc p. \<bar>l i k / (p + 2) - l j k / (p + 2)\<bar>) \<le> (1 + real p) * d / (p + 2)" .
                then have "\<bar>\<Sum>j\<le>Suc p. l i k / (p + 2) - l j k / (p + 2)\<bar> \<le> (1 + real p) * d / (p + 2)"
                  by (rule order_trans [OF sum_abs])
                then show "\<bar>l i k - (\<Sum>j\<le>Suc p. l j k) / (2 + real p)\<bar> \<le> (1 + real p) * d / (2 + real p)"
                  by (simp add: sum_subtractf sum_divide_distrib del: sum.atMost_Suc)
              qed (use standard_simplex_def z in auto)
            qed
            have nonz: "\<bar>m (s - Suc 0) k - m (r - Suc 0) k\<bar> \<le> (1 + real p) * d / (2 + real p)" (is "?lhs \<le> ?rhs")
              if "r < s" and "0 < r" and "r \<le> Suc p" and "s \<le> Suc p" for r s
            proof -
              have "?lhs \<le> (p / (Suc p)) * d"
                using m_in_gim [of "r - Suc 0"] m_in_gim [of "s - Suc 0"] that g by fastforce
              also have "\<dots> \<le> ?rhs"
                by (simp add: field_simps \<open>0 \<le> d\<close>)
              finally show ?thesis .
            qed
            have jj: "j \<le> Suc p \<and> j' \<le> Suc p
                \<longrightarrow> \<bar>(if j' = 0 then \<lambda>i. (\<Sum>j\<le>Suc p. l j i) / (2 + real p) else m (j' -1)) k -
                     (if j = 0 then \<lambda>i. (\<Sum>j\<le>Suc p. l j i) / (2 + real p) else m (j -1)) k\<bar>
                     \<le> (1 + real p) * d / (2 + real p)" for j j'
              using \<open>0 \<le> d\<close> 
              by (rule_tac a=j and b = "j'" in linorder_less_wlog; force simp: zero nonz simp del: sum.atMost_Suc)
            show ?thesis
              apply (rule convex_sum_bound_le)
              using x' apply blast
              using x' apply blast
              apply (subst abs_minus_commute)
              apply (rule convex_sum_bound_le)
              using y' apply blast
              using y' apply blast
              using jj by blast
          qed
          then show "\<bar>simplex_cone p (Sigp f) (oriented_simplex p m) x k - simplex_cone p (Sigp f) (oriented_simplex p m) y k\<bar>
                \<le> (1 + real p) * d / (real p + 2)"
            apply (simp add: feq Sigp_def simplicial_vertex_oriented_simplex simplex_cone del: sum.atMost_Suc)
            apply (simp add: oriented_simplex_def algebra_simps x y del: sum.atMost_Suc)
            done
        qed
      qed
      show ?thesis
        using Suc.IH [OF 1, where f=g] 2 3 by simp
    qed
    then show ?thesis
      unfolding simplicial_chain_def simplicial_cone_def
      by (simp add: order_trans [OF keys_frag_extend] sub UN_subset_iff)
  qed
  show ?case
    using Suc
    apply (simp del: sum.atMost_Suc)
    apply (drule subsetD [OF keys_frag_extend])
    apply (simp del: sum.atMost_Suc)
    apply clarify (*OBTAIN?*)
    apply (rename_tac FFF)
    using *
    apply (simp add: add.commute Sigp_def subset_iff)
    done
qed (auto simp: standard_simplex_0)


subsection\<open>Singular subdivision\<close>

definition singular_subdivision
  where "singular_subdivision p \<equiv>
        frag_extend
           (\<lambda>f. chain_map p f
                  (simplicial_subdivision p
                         (frag_of(restrict id (standard_simplex p)))))"

lemma singular_subdivision_0 [simp]: "singular_subdivision p 0 = 0"
  by (simp add: singular_subdivision_def)

lemma singular_subdivision_add:
   "singular_subdivision p (a + b) = singular_subdivision p a + singular_subdivision p b"
  by (simp add: singular_subdivision_def frag_extend_add)

lemma singular_subdivision_diff:
   "singular_subdivision p (a - b) = singular_subdivision p a - singular_subdivision p b"
  by (simp add: singular_subdivision_def frag_extend_diff)

lemma simplicial_simplex_id [simp]:
   "simplicial_simplex p S (restrict id (standard_simplex p)) \<longleftrightarrow> standard_simplex p \<subseteq> S"
    (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    by (simp add: simplicial_simplex_def singular_simplex_def continuous_map_in_subtopology set_mp)
next
  assume R: ?rhs
  then have cm: "continuous_map
                 (subtopology (powertop_real UNIV) (standard_simplex p))
                 (subtopology (powertop_real UNIV) S) id"
    using continuous_map_from_subtopology_mono continuous_map_id by blast
  moreover have "\<exists>l. restrict id (standard_simplex p) = oriented_simplex p l"
    apply (rule_tac x="\<lambda>i j. if i = j then 1 else 0" in exI)
    apply (force simp: oriented_simplex_def standard_simplex_def if_distrib [of "\<lambda>u. u * _"] cong: if_cong)
    done
  ultimately show ?lhs
    by (simp add: simplicial_simplex_def singular_simplex_def)
qed

lemma singular_chain_singular_subdivision:
   "singular_chain p X c
        \<Longrightarrow> singular_chain p X (singular_subdivision p c)"
  unfolding singular_subdivision_def
  apply (rule singular_chain_extend)
  apply (rule singular_chain_chain_map [where X = "subtopology (powertop_real UNIV)
                          (standard_simplex p)"])
  apply (simp add: simplicial_chain_simplicial_subdivision simplicial_imp_singular_chain)
  by (simp add: singular_chain_def singular_simplex_def subset_iff)

lemma naturality_singular_subdivision:
   "singular_chain p X c
    \<Longrightarrow> singular_subdivision p (chain_map p g c) = chain_map p g (singular_subdivision p c)"
  unfolding singular_chain_def
proof (induction rule: frag_induction)
  case (one f)
  then have "singular_simplex p X f"
    by auto
  have "\<lbrakk>simplicial_chain p (standard_simplex p) d\<rbrakk>
    \<Longrightarrow> chain_map p (simplex_map p g f) d = chain_map p g (chain_map p f d)" for d
    unfolding simplicial_chain_def
  proof (induction rule: frag_induction)
    case (one x)
    then have "simplex_map p (simplex_map p g f) x = simplex_map p g (simplex_map p f x)"
      by (force simp: simplex_map_def restrict_compose_left simplicial_simplex)
    then show ?case
      by auto
  qed (auto simp: chain_map_diff)
  then show ?case
    using simplicial_chain_simplicial_subdivision [of p "standard_simplex p" "frag_of (restrict id (standard_simplex p))"]
    by (simp add: singular_subdivision_def)
next
  case (diff a b)
  then show ?case
    by (simp add: chain_map_diff singular_subdivision_diff)
qed auto

lemma simplicial_chain_chain_map:
  assumes f: "simplicial_simplex q X f" and c: "simplicial_chain p (standard_simplex q) c"
  shows "simplicial_chain p X (chain_map p f c)"
  using c unfolding simplicial_chain_def
proof (induction c rule: frag_induction)
  case (one g)
  have "\<exists>n. simplex_map p (oriented_simplex q l)
                 (oriented_simplex p m) = oriented_simplex p n"
    if m: "singular_simplex p
                (subtopology (powertop_real UNIV) (standard_simplex q)) (oriented_simplex p m)"
    for l m
  proof -
    have "(\<lambda>i. \<Sum>j\<le>p. m j i * x j) \<in> standard_simplex q"
      if "x \<in> standard_simplex p" for x
      using that m unfolding oriented_simplex_def singular_simplex_def
      by (auto simp: continuous_map_in_subtopology image_subset_iff)
    then show ?thesis
      unfolding oriented_simplex_def simplex_map_def
      apply (rule_tac x="\<lambda>j k. (\<Sum>i\<le>q. l i k * m j i)" in exI)
      apply (force simp: sum_distrib_left sum_distrib_right mult.assoc intro: sum.swap)
      done
  qed
  then show ?case
    using f one
    apply (auto simp: simplicial_simplex_def)
    apply (rule singular_simplex_simplex_map
        [where X = "subtopology (powertop_real UNIV) (standard_simplex q)"])
    unfolding singular_simplex_def apply (fastforce simp add:)+
    done
next
  case (diff a b)
  then show ?case
    by (metis chain_map_diff simplicial_chain_def simplicial_chain_diff)
qed auto


lemma singular_subdivision_simplicial_simplex:
   "simplicial_chain p S c
           \<Longrightarrow> singular_subdivision p c = simplicial_subdivision p c"
proof (induction p arbitrary: S c)
  case 0
  then show ?case
    unfolding simplicial_chain_def
  proof (induction rule: frag_induction)
    case (one x)
    then show ?case
      using singular_simplex_chain_map_id simplicial_imp_singular_simplex
      by (fastforce simp: singular_subdivision_def simplicial_subdivision_def)
  qed (auto simp: singular_subdivision_diff)
next
  case (Suc p)
  show ?case
    using Suc.prems unfolding simplicial_chain_def
  proof (induction rule: frag_induction)
    case (one f)
    then have ssf: "simplicial_simplex (Suc p) S f"
      by (auto simp: simplicial_simplex)
    then have 1: "simplicial_chain p (standard_simplex (Suc p))
                   (simplicial_subdivision p
                     (chain_boundary (Suc p)
                       (frag_of (restrict id (standard_simplex (Suc p))))))"
      by (metis diff_Suc_1 order_refl simplicial_chain_boundary simplicial_chain_of simplicial_chain_simplicial_subdivision simplicial_simplex_id)
    have 2: "(\<lambda>i. (\<Sum>j\<le>Suc p. simplicial_vertex j (restrict id (standard_simplex (Suc p))) i) / (real p + 2))
                  \<in> standard_simplex (Suc p)"
      by (simp add: simplicial_vertex_def standard_simplex_def del: sum.atMost_Suc)
    have ss_Sp: "(\<lambda>i. (if i \<le> Suc p then 1 else 0) / (real p + 2)) \<in> standard_simplex (Suc p)"
      by (simp add: standard_simplex_def field_split_simps)
    obtain l where feq: "f = oriented_simplex (Suc p) l"
      using one unfolding simplicial_simplex by blast
    then have 3: "f (\<lambda>i. (\<Sum>j\<le>Suc p. simplicial_vertex j (restrict id (standard_simplex (Suc p))) i) / (real p + 2))
                = (\<lambda>i. (\<Sum>j\<le>Suc p. simplicial_vertex j f i) / (real p + 2))"
      unfolding simplicial_vertex_def oriented_simplex_def
      by (simp add: ss_Sp if_distrib [of "\<lambda>x. _ * x"] sum_divide_distrib del: sum.atMost_Suc cong: if_cong)
    have scp: "singular_chain (Suc p)
                 (subtopology (powertop_real UNIV) (standard_simplex (Suc p)))
                 (frag_of (restrict id (standard_simplex (Suc p))))"
      by (simp add: simplicial_imp_singular_chain)
    have scps: "simplicial_chain p (standard_simplex (Suc p))
                  (chain_boundary (Suc p) (frag_of (restrict id (standard_simplex (Suc p)))))"
      by (metis diff_Suc_1 order_refl simplicial_chain_boundary simplicial_chain_of simplicial_simplex_id)
    have scpf: "simplicial_chain p S
                 (chain_map p f
                   (chain_boundary (Suc p) (frag_of (restrict id (standard_simplex (Suc p))))))"
      using scps simplicial_chain_chain_map ssf by blast
    have 4: "chain_map p f
                (simplicial_subdivision p
                   (chain_boundary (Suc p) (frag_of (restrict id (standard_simplex (Suc p))))))
           = simplicial_subdivision p (chain_boundary (Suc p) (frag_of f))"
      apply (simp add: chain_boundary_chain_map [OF scp] del: chain_map_of
          flip: singular_simplex_chain_map_id [OF simplicial_imp_singular_simplex [OF ssf]])
      by (metis (no_types) scp singular_chain_boundary_alt Suc.IH [OF scps] Suc.IH [OF scpf] naturality_singular_subdivision)
    show ?case
      apply (simp add: singular_subdivision_def del: sum.atMost_Suc)
      apply (simp only: ssf 1 2 3 4 chain_map_simplicial_cone [of "Suc p" S _ p "Suc p"])
      done
  qed (auto simp: frag_extend_diff singular_subdivision_diff)
qed


lemma naturality_simplicial_subdivision:
   "\<lbrakk>simplicial_chain p (standard_simplex q) c; simplicial_simplex q S g\<rbrakk>
    \<Longrightarrow> simplicial_subdivision p (chain_map p g c) = chain_map p g (simplicial_subdivision p c)"
apply (simp flip: singular_subdivision_simplicial_simplex)
  by (metis naturality_singular_subdivision simplicial_chain_chain_map simplicial_imp_singular_chain singular_subdivision_simplicial_simplex)

lemma chain_boundary_singular_subdivision:
   "singular_chain p X c
        \<Longrightarrow> chain_boundary p (singular_subdivision p c) =
            singular_subdivision (p - Suc 0) (chain_boundary p c)"
  unfolding singular_chain_def
proof (induction rule: frag_induction)
  case (one f)
    then have ssf: "singular_simplex p X f"
      by (auto simp: singular_simplex_def)
    then have scp: "simplicial_chain p (standard_simplex p) (frag_of (restrict id (standard_simplex p)))"
      by simp
    have scp1: "simplicial_chain (p - Suc 0) (standard_simplex p)
                  (chain_boundary p (frag_of (restrict id (standard_simplex p))))"
      using simplicial_chain_boundary by force
    have sgp1: "singular_chain (p - Suc 0)
                   (subtopology (powertop_real UNIV) (standard_simplex p))
                   (chain_boundary p (frag_of (restrict id (standard_simplex p))))"
      using scp1 simplicial_imp_singular_chain by blast
    have scpp: "singular_chain p (subtopology (powertop_real UNIV) (standard_simplex p))
                  (frag_of (restrict id (standard_simplex p)))"
      using scp simplicial_imp_singular_chain by blast
    then show ?case
      unfolding singular_subdivision_def
      using chain_boundary_chain_map [of p "subtopology (powertop_real UNIV)
                              (standard_simplex p)" _ f]
      apply (simp add: simplicial_chain_simplicial_subdivision
          simplicial_imp_singular_chain chain_boundary_simplicial_subdivision [OF scp]
          flip: singular_subdivision_simplicial_simplex [OF scp1] naturality_singular_subdivision [OF sgp1])
      by (metis (full_types)   singular_subdivision_def  chain_boundary_chain_map [OF scpp] singular_simplex_chain_map_id [OF ssf])
qed (auto simp: singular_subdivision_def frag_extend_diff chain_boundary_diff)

lemma singular_subdivision_zero:
  "singular_chain 0 X c \<Longrightarrow> singular_subdivision 0 c = c"
  unfolding singular_chain_def
proof (induction rule: frag_induction)
  case (one f)
  then have "restrict (f \<circ> restrict id (standard_simplex 0)) (standard_simplex 0) = f"
    by (simp add: extensional_restrict restrict_compose_right singular_simplex_def)
  then show ?case
    by (auto simp: singular_subdivision_def simplex_map_def)
qed (auto simp: singular_subdivision_def frag_extend_diff)


primrec subd where
  "subd 0 = (\<lambda>x. 0)"
| "subd (Suc p) =
      frag_extend
       (\<lambda>f. simplicial_cone (Suc p) (\<lambda>i. (\<Sum>j\<le>Suc p. simplicial_vertex j f i) / real (Suc p + 1))
               (simplicial_subdivision (Suc p) (frag_of f) - frag_of f -
                subd p (chain_boundary (Suc p) (frag_of f))))"

lemma subd_0 [simp]: "subd p 0 = 0"
  by (induction p) auto

lemma subd_diff [simp]: "subd p (c1 - c2) = subd p c1 - subd p c2"
  by (induction p) (auto simp: frag_extend_diff)

lemma subd_uminus [simp]: "subd p (-c) = - subd p c"
  by (metis diff_0 subd_0 subd_diff)

lemma subd_power_uminus: "subd p (frag_cmul ((-1) ^ k) c) = frag_cmul ((-1) ^ k) (subd p c)"
  apply (induction k, simp_all)
  by (metis minus_frag_cmul subd_uminus)

lemma subd_power_sum: "subd p (sum f I) = sum (subd p \<circ> f) I"
  apply (induction I rule: infinite_finite_induct)
  by auto (metis add_diff_cancel_left' diff_add_cancel subd_diff)

lemma subd: "simplicial_chain p (standard_simplex s) c
     \<Longrightarrow> (\<forall>r g. simplicial_simplex s (standard_simplex r) g \<longrightarrow> chain_map (Suc p) g (subd p c) = subd p (chain_map p g c))
         \<and> simplicial_chain (Suc p) (standard_simplex s) (subd p c)
         \<and> (chain_boundary (Suc p) (subd p c)) + (subd (p - Suc 0) (chain_boundary p c)) = (simplicial_subdivision p c) - c"
proof (induction p arbitrary: c)
  case (Suc p)
  show ?case
    using Suc.prems [unfolded simplicial_chain_def]
  proof (induction rule: frag_induction)
    case (one f)
    then obtain l where l: "(\<lambda>x i. \<Sum>j\<le>Suc p. l j i * x j) ` standard_simplex (Suc p) \<subseteq> standard_simplex s"
                  and feq: "f = oriented_simplex (Suc p) l"
      by (metis (mono_tags) mem_Collect_eq simplicial_simplex simplicial_simplex_oriented_simplex)
    have scf: "simplicial_chain (Suc p) (standard_simplex s) (frag_of f)"
      using one by simp
    have lss: "l i \<in> standard_simplex s" if "i \<le> Suc p" for i
    proof -
      have "(\<lambda>i'. \<Sum>j\<le>Suc p. l j i' * (if j = i then 1 else 0)) \<in> standard_simplex s"
        using subsetD [OF l] basis_in_standard_simplex that by blast
      moreover have "(\<lambda>i'. \<Sum>j\<le>Suc p. l j i' * (if j = i then 1 else 0)) = l i"
        using that by (simp add: if_distrib [of "\<lambda>x. _ * x"] del: sum.atMost_Suc cong: if_cong)
      ultimately show ?thesis
        by simp
    qed
    have *: "(\<And>i. i \<le> n \<Longrightarrow> l i \<in> standard_simplex s)
     \<Longrightarrow> (\<lambda>i. (\<Sum>j\<le>n. l j i) / (Suc n)) \<in> standard_simplex s" for n
    proof (induction n)
      case (Suc n)
      let ?x = "\<lambda>i. (1 - inverse (n + 2)) * ((\<Sum>j\<le>n. l j i) / (Suc n)) + inverse (n + 2) * l (Suc n) i"
      have "?x \<in> standard_simplex s"
      proof (rule convex_standard_simplex)
        show "(\<lambda>i. (\<Sum>j\<le>n. l j i) / real (Suc n)) \<in> standard_simplex s"
          using Suc by simp
      qed (auto simp: lss Suc inverse_le_1_iff)
      moreover have "?x = (\<lambda>i. (\<Sum>j\<le>Suc n. l j i) / real (Suc (Suc n)))"
        by (force simp: divide_simps)
      ultimately show ?case
        by simp
    qed auto
    have **: "(\<lambda>i. (\<Sum>j\<le>Suc p. simplicial_vertex j f i) / (2 + real p)) \<in> standard_simplex s"
      using * [of "Suc p"] lss by (simp add: simplicial_vertex_oriented_simplex feq)
    show ?case
    proof (intro conjI impI allI)
      fix r g
      assume g: "simplicial_simplex s (standard_simplex r) g"
      then obtain m where geq: "g = oriented_simplex s m"
        using simplicial_simplex by blast
      have 1: "simplicial_chain (Suc p) (standard_simplex s) (simplicial_subdivision (Suc p) (frag_of f))"
        by (metis mem_Collect_eq one.hyps simplicial_chain_of simplicial_chain_simplicial_subdivision)
      have 2: "(\<Sum>j\<le>Suc p. \<Sum>i\<le>s. m i k * simplicial_vertex j f i)
             = (\<Sum>j\<le>Suc p. simplicial_vertex j
                                (simplex_map (Suc p) (oriented_simplex s m) f) k)" for k
      proof (rule sum.cong [OF refl])
        fix j
        assume j: "j \<in> {..Suc p}"
        have eq: "simplex_map (Suc p) (oriented_simplex s m) (oriented_simplex (Suc p) l)
                = oriented_simplex (Suc p) (oriented_simplex s m \<circ> l)"
        proof (rule simplex_map_oriented_simplex)
          show "simplicial_simplex (Suc p) (standard_simplex s) (oriented_simplex (Suc p) l)"
            using one by (simp add: feq flip: oriented_simplex_def)
          show "simplicial_simplex s (standard_simplex r) (oriented_simplex s m)"
            using g by (simp add: geq)
        qed auto
        show "(\<Sum>i\<le>s. m i k * simplicial_vertex j f i)
            = simplicial_vertex j (simplex_map (Suc p) (oriented_simplex s m) f) k"
          using one j
          apply (simp add: feq eq simplicial_vertex_oriented_simplex simplicial_simplex_oriented_simplex image_subset_iff)
          apply (drule_tac x="(\<lambda>i. if i = j then 1 else 0)" in bspec)
           apply (auto simp: oriented_simplex_def lss)
          done
      qed
      have 4: "chain_map (Suc p) g (subd p (chain_boundary (Suc p) (frag_of f)))
             = subd p (chain_boundary (Suc p) (frag_of (simplex_map (Suc p) g f)))"
        by (metis (no_types) One_nat_def scf Suc.IH chain_boundary_chain_map chain_map_of diff_Suc_Suc diff_zero g simplicial_chain_boundary simplicial_imp_singular_chain)
      show "chain_map (Suc (Suc p)) g (subd (Suc p) (frag_of f)) = subd (Suc p) (chain_map (Suc p) g (frag_of f))"
        using g
        apply (simp only: subd.simps frag_extend_of)
        apply (subst chain_map_simplicial_cone [of s "standard_simplex r" _ "Suc p" s], assumption)
           apply (intro simplicial_chain_diff)
        using "1" apply auto[1]
        using one.hyps apply auto[1]
        apply (metis Suc.IH diff_Suc_1 mem_Collect_eq one.hyps simplicial_chain_boundary simplicial_chain_of)
        using "**" apply auto[1]
         apply (rule order_refl)
         apply (simp only: chain_map_of frag_extend_of)
        apply (rule arg_cong2 [where f = "simplicial_cone (Suc p)"])
         apply (simp add: geq sum_distrib_left oriented_simplex_def ** del: sum.atMost_Suc flip: sum_divide_distrib)
        using 2  apply (simp only: oriented_simplex_def sum.swap [where A = "{..s}"])
        using naturality_simplicial_subdivision scf apply (fastforce simp add: 4 chain_map_diff)
        done
    next
      have sc: "simplicial_chain (Suc p) (standard_simplex s)
               (simplicial_cone p
                 (\<lambda>i. (\<Sum>j\<le>Suc p. simplicial_vertex j f i) / (Suc (Suc p)))
                 (simplicial_subdivision p
                   (chain_boundary (Suc p) (frag_of f))))"
          by (metis diff_Suc_1 nat.simps(3) simplicial_subdivision_of scf simplicial_chain_simplicial_subdivision)
      have ff: "simplicial_chain (Suc p) (standard_simplex s) (subd p (chain_boundary (Suc p) (frag_of f)))"
        by (metis (no_types) Suc.IH diff_Suc_1 scf simplicial_chain_boundary)
      show "simplicial_chain (Suc (Suc p)) (standard_simplex s) (subd (Suc p) (frag_of f))"
        using one
        apply (simp only: subd.simps frag_extend_of)
        apply (rule_tac S="standard_simplex s" in simplicial_chain_simplicial_cone)
         apply (intro simplicial_chain_diff ff)
        using sc apply (simp add: algebra_simps)
        using "**" convex_standard_simplex  apply force+
        done
      have "simplicial_chain p (standard_simplex s) (chain_boundary (Suc p) (frag_of f))"
        using scf simplicial_chain_boundary by fastforce
      then have "chain_boundary (Suc p) (simplicial_subdivision (Suc p) (frag_of f) - frag_of f
                                         - subd p (chain_boundary (Suc p) (frag_of f))) = 0"
        apply (simp only: chain_boundary_diff)
        using Suc.IH chain_boundary_boundary [of "Suc p" "subtopology (powertop_real UNIV)
                                (standard_simplex s)" "frag_of f"]
        by (metis One_nat_def add_diff_cancel_left' subd_0 chain_boundary_simplicial_subdivision plus_1_eq_Suc scf simplicial_imp_singular_chain)
      then show "chain_boundary (Suc (Suc p)) (subd (Suc p) (frag_of f))
          + subd (Suc p - Suc 0) (chain_boundary (Suc p) (frag_of f))
          = simplicial_subdivision (Suc p) (frag_of f) - frag_of f"
        apply (simp only: subd.simps frag_extend_of)
        apply (subst chain_boundary_simplicial_cone [of "Suc p" "standard_simplex s"])
         apply (meson ff scf simplicial_chain_diff simplicial_chain_simplicial_subdivision)
        apply (simp add: simplicial_cone_def del: sum.atMost_Suc simplicial_subdivision.simps)
        done
    qed
  next
    case (diff a b)
    then show ?case
      apply safe
        apply (metis chain_map_diff subd_diff)
       apply (metis simplicial_chain_diff subd_diff)
      apply (auto simp:  simplicial_subdivision_diff chain_boundary_diff
          simp del: simplicial_subdivision.simps subd.simps)
      by (metis (no_types, lifting) add_diff_add add_uminus_conv_diff diff_0 diff_diff_add)
  qed auto
qed simp

lemma chain_homotopic_simplicial_subdivision1:
  "\<lbrakk>simplicial_chain p (standard_simplex q) c; simplicial_simplex q (standard_simplex r) g\<rbrakk>
       \<Longrightarrow> chain_map (Suc p) g (subd p c) = subd p (chain_map p g c)"
  by (simp add: subd)

lemma chain_homotopic_simplicial_subdivision2:
  "simplicial_chain p (standard_simplex q) c
       \<Longrightarrow> simplicial_chain (Suc p) (standard_simplex q) (subd p c)"
  by (simp add: subd)

lemma chain_homotopic_simplicial_subdivision3:
  "simplicial_chain p (standard_simplex q) c
   \<Longrightarrow> chain_boundary (Suc p) (subd p c) = (simplicial_subdivision p c) - c - subd (p - Suc 0) (chain_boundary p c)"
  by (simp add: subd algebra_simps)

lemma chain_homotopic_simplicial_subdivision:
  "\<exists>h. (\<forall>p. h p 0 = 0) \<and>
       (\<forall>p c1 c2. h p (c1-c2) = h p c1 - h p c2) \<and>
       (\<forall>p q r g c.
                simplicial_chain p (standard_simplex q) c
                \<longrightarrow> simplicial_simplex q (standard_simplex r) g
                \<longrightarrow> chain_map (Suc p) g (h p c) = h p (chain_map p g c)) \<and>
       (\<forall>p q c. simplicial_chain p (standard_simplex q) c
                \<longrightarrow> simplicial_chain (Suc p) (standard_simplex q) (h p c)) \<and>
       (\<forall>p q c. simplicial_chain p (standard_simplex q) c
                \<longrightarrow> chain_boundary (Suc p) (h p c) + h (p - Suc 0) (chain_boundary p c)
                  = (simplicial_subdivision p c) - c)"
  by (rule_tac x=subd in exI) (fastforce simp: subd)

lemma chain_homotopic_singular_subdivision:
  obtains h where
        "\<And>p. h p 0 = 0"
        "\<And>p c1 c2. h p (c1-c2) = h p c1 - h p c2"
        "\<And>p X c. singular_chain p X c \<Longrightarrow> singular_chain (Suc p) X (h p c)"
        "\<And>p X c. singular_chain p X c
                 \<Longrightarrow> chain_boundary (Suc p) (h p c) + h (p - Suc 0) (chain_boundary p c) = singular_subdivision p c - c"
proof -
  define k where "k \<equiv> \<lambda>p. frag_extend (\<lambda>f:: (nat \<Rightarrow> real) \<Rightarrow> 'a. chain_map (Suc p) f (subd p (frag_of(restrict id (standard_simplex p)))))"
  show ?thesis
  proof
    fix p X and c :: "'a chain"
    assume c: "singular_chain p X c"
    have "singular_chain (Suc p) X (k p c) \<and>
               chain_boundary (Suc p) (k p c) + k (p - Suc 0) (chain_boundary p c) = singular_subdivision p c - c"
      using c [unfolded singular_chain_def]
    proof (induction rule: frag_induction)
      case (one f)
      let ?X = "subtopology (powertop_real UNIV) (standard_simplex p)"
      show ?case
      proof (simp add: k_def, intro conjI)
        show "singular_chain (Suc p) X (chain_map (Suc p) f (subd p (frag_of (restrict id (standard_simplex p)))))"
        proof (rule singular_chain_chain_map)
          show "singular_chain (Suc p) ?X  (subd p (frag_of (restrict id (standard_simplex p))))"
            by (simp add: chain_homotopic_simplicial_subdivision2 simplicial_imp_singular_chain)
          show "continuous_map ?X X f"
            using one.hyps singular_simplex_def by auto
        qed
      next
        have scp: "singular_chain (Suc p) ?X (subd p (frag_of (restrict id (standard_simplex p))))"
          by (simp add: chain_homotopic_simplicial_subdivision2 simplicial_imp_singular_chain)
        have feqf: "frag_of (simplex_map p f (restrict id (standard_simplex p))) = frag_of f"
          using one.hyps singular_simplex_chain_map_id by auto
        have *: "chain_map p f
                   (subd (p - Suc 0)
                     (\<Sum>k\<le>p. frag_cmul ((-1) ^ k) (frag_of (singular_face p k id))))
              = (\<Sum>x\<le>p. frag_cmul ((-1) ^ x)
                         (chain_map p (singular_face p x f)
                           (subd (p - Suc 0) (frag_of (restrict id (standard_simplex (p - Suc 0)))))))"
                  (is "?lhs = ?rhs")
                  if "p > 0"
        proof -
          have eqc: "subd (p - Suc 0) (frag_of (singular_face p i id))
                   = chain_map p (singular_face p i id)
                                 (subd (p - Suc 0) (frag_of (restrict id (standard_simplex (p - Suc 0)))))"
            if "i \<le> p" for i
          proof -
            have 1: "simplicial_chain (p - Suc 0) (standard_simplex (p - Suc 0))
                       (frag_of (restrict id (standard_simplex (p - Suc 0))))"
              by simp
            have 2: "simplicial_simplex (p - Suc 0) (standard_simplex p) (singular_face p i id)"
              by (metis One_nat_def Suc_leI \<open>0 < p\<close> simplicial_simplex_id simplicial_simplex_singular_face singular_face_restrict subsetI that)
            have 3: "simplex_map (p - Suc 0) (singular_face p i id) (restrict id (standard_simplex (p - Suc 0)))
                   = singular_face p i id"
              by (force simp: simplex_map_def singular_face_def)
            show ?thesis
              using chain_homotopic_simplicial_subdivision1 [OF 1 2]
                that \<open>p > 0\<close>  by (simp add: 3)
          qed
          have xx: "simplicial_chain p (standard_simplex(p - Suc 0))
                    (subd (p - Suc 0) (frag_of (restrict id (standard_simplex (p - Suc 0)))))"
            by (metis Suc_pred chain_homotopic_simplicial_subdivision2 order_refl simplicial_chain_of simplicial_simplex_id that)
          have yy: "\<And>k. k \<le> p \<Longrightarrow>
                 chain_map p f
                  (chain_map p (singular_face p k id) h) = chain_map p (singular_face p k f) h"
            if "simplicial_chain p (standard_simplex(p - Suc 0)) h" for h
            using that unfolding simplicial_chain_def
          proof (induction h rule: frag_induction)
            case (one x)
            then show ?case
                using one
              apply (simp add: chain_map_of singular_simplex_def simplicial_simplex_def, auto)
                apply (rule_tac f=frag_of in arg_cong, rule)
                apply (simp add: simplex_map_def)
                by (simp add: continuous_map_in_subtopology image_subset_iff singular_face_def)
          qed (auto simp: chain_map_diff)
          have "?lhs
                = chain_map p f
                      (\<Sum>k\<le>p. frag_cmul ((-1) ^ k)
                          (chain_map p (singular_face p k id)
                           (subd (p - Suc 0) (frag_of (restrict id (standard_simplex (p - Suc 0)))))))"
            by (simp add: subd_power_sum subd_power_uminus eqc)
          also have "\<dots> = ?rhs"
            by (simp add: chain_map_sum xx yy)
          finally show ?thesis .
      qed
        have "chain_map p f
                   (simplicial_subdivision p (frag_of (restrict id (standard_simplex p)))
                   - subd (p - Suc 0) (chain_boundary p (frag_of (restrict id (standard_simplex p)))))
              = singular_subdivision p (frag_of f)
              - frag_extend
                   (\<lambda>f. chain_map (Suc (p - Suc 0)) f
                         (subd (p - Suc 0) (frag_of (restrict id (standard_simplex (p - Suc 0))))))
                   (chain_boundary p (frag_of f))"
          apply (simp add: singular_subdivision_def chain_map_diff)
          apply (clarsimp simp add: chain_boundary_def)
          apply (simp add: frag_extend_sum frag_extend_cmul *)
          done
        then show "chain_boundary (Suc p) (chain_map (Suc p) f (subd p (frag_of (restrict id (standard_simplex p)))))
                 + frag_extend
                   (\<lambda>f. chain_map (Suc (p - Suc 0)) f
                         (subd (p - Suc 0) (frag_of (restrict id (standard_simplex (p - Suc 0))))))
                   (chain_boundary p (frag_of f))
                 = singular_subdivision p (frag_of f) - frag_of f"
          by (simp add: chain_boundary_chain_map [OF scp] chain_homotopic_simplicial_subdivision3 [where q=p] chain_map_diff feqf)
      qed
    next
      case (diff a b)
      then show ?case
        apply (simp only: k_def singular_chain_diff chain_boundary_diff frag_extend_diff singular_subdivision_diff)
        by (metis (no_types, lifting) add_diff_add diff_add_cancel)
    qed (auto simp: k_def)
    then show "singular_chain (Suc p) X (k p c)" "chain_boundary (Suc p) (k p c) + k (p - Suc 0) (chain_boundary p c) = singular_subdivision p c - c"
        by auto
  qed (auto simp: k_def frag_extend_diff)
qed


lemma homologous_rel_singular_subdivision:
  assumes "singular_relcycle p X T c"
  shows "homologous_rel p X T (singular_subdivision p c) c"
proof (cases "p = 0")
  case True
  with assms show ?thesis
    by (auto simp: singular_relcycle_def singular_subdivision_zero)
next
  case False
  with assms show ?thesis
    unfolding homologous_rel_def singular_relboundary singular_relcycle
    by (metis One_nat_def Suc_diff_1 chain_homotopic_singular_subdivision gr_zeroI)
qed


subsection\<open>Excision argument that we keep doing singular subdivision\<close>

lemma singular_subdivision_power_0 [simp]: "(singular_subdivision p ^^ n) 0 = 0"
  by (induction n) auto

lemma singular_subdivision_power_diff:
  "(singular_subdivision p ^^ n) (a - b) = (singular_subdivision p ^^ n) a - (singular_subdivision p ^^ n) b"
  by (induction n) (auto simp: singular_subdivision_diff)

lemma iterated_singular_subdivision:
   "singular_chain p X c
        \<Longrightarrow> (singular_subdivision p ^^ n) c =
            frag_extend
             (\<lambda>f. chain_map p f
                       ((simplicial_subdivision p ^^ n)
                         (frag_of(restrict id (standard_simplex p))))) c"
proof (induction n arbitrary: c)
  case 0
  then show ?case
    unfolding singular_chain_def
  proof (induction c rule: frag_induction)
    case (one f)
    then have "restrict f (standard_simplex p) = f"
      by (simp add: extensional_restrict singular_simplex_def)
    then show ?case
      by (auto simp: simplex_map_def cong: restrict_cong)
  qed (auto simp: frag_extend_diff)
next
  case (Suc n)
  show ?case
    using Suc.prems unfolding singular_chain_def
  proof (induction c rule: frag_induction)
    case (one f)
    then have "singular_simplex p X f"
      by simp
    have scp: "simplicial_chain p (standard_simplex p)
                 ((simplicial_subdivision p ^^ n) (frag_of (restrict id (standard_simplex p))))"
    proof (induction n)
      case 0
      then show ?case
        by (metis funpow_0 order_refl simplicial_chain_of simplicial_simplex_id)
    next
      case (Suc n)
      then show ?case
        by (simp add: simplicial_chain_simplicial_subdivision)
    qed
    have scnp: "simplicial_chain p (standard_simplex p)
                  ((simplicial_subdivision p ^^ n) (frag_of (\<lambda>x\<in>standard_simplex p. x)))"
    proof (induction n)
      case 0
      then show ?case
        by (metis eq_id_iff funpow_0 order_refl simplicial_chain_of simplicial_simplex_id)
    next
      case (Suc n)
      then show ?case
        by (simp add: simplicial_chain_simplicial_subdivision)
    qed
    have sff: "singular_chain p X (frag_of f)"
      by (simp add: \<open>singular_simplex p X f\<close> singular_chain_of)
    then show ?case
      using Suc.IH [OF sff] naturality_singular_subdivision [OF simplicial_imp_singular_chain [OF scp], of f] singular_subdivision_simplicial_simplex [OF scnp]
      by (simp add: singular_chain_of id_def del: restrict_apply)
  qed (auto simp: singular_subdivision_power_diff singular_subdivision_diff frag_extend_diff)
qed


lemma chain_homotopic_iterated_singular_subdivision:
  obtains h where
        "\<And>p. h p 0 = (0 :: 'a chain)"
        "\<And>p c1 c2. h p (c1-c2) = h p c1 - h p c2"
        "\<And>p X c. singular_chain p X c \<Longrightarrow> singular_chain (Suc p) X (h p c)"
        "\<And>p X c. singular_chain p X c
                 \<Longrightarrow> chain_boundary (Suc p) (h p c) + h (p - Suc 0) (chain_boundary p c)
                   = (singular_subdivision p ^^ n) c - c"
proof (induction n arbitrary: thesis)
  case 0
  show ?case
    by (rule 0 [of "(\<lambda>p x. 0)"]) auto
next
  case (Suc n)
  then obtain k where k:
        "\<And>p. k p 0 = (0 :: 'a chain)"
        "\<And>p c1 c2. k p (c1-c2) = k p c1 - k p c2"
        "\<And>p X c. singular_chain p X c \<Longrightarrow> singular_chain (Suc p) X (k p c)"
        "\<And>p X c. singular_chain p X c
                 \<Longrightarrow> chain_boundary (Suc p) (k p c) + k (p - Suc 0) (chain_boundary p c)
                     = (singular_subdivision p ^^ n) c - c"
    by metis
  obtain h where h:
        "\<And>p. h p 0 = (0 :: 'a chain)"
        "\<And>p c1 c2. h p (c1-c2) = h p c1 - h p c2"
        "\<And>p X c. singular_chain p X c \<Longrightarrow> singular_chain (Suc p) X (h p c)"
        "\<And>p X c. singular_chain p X c
                 \<Longrightarrow> chain_boundary (Suc p) (h p c) + h (p - Suc 0) (chain_boundary p c) = singular_subdivision p c - c"
    by (blast intro: chain_homotopic_singular_subdivision)
  let ?h = "(\<lambda>p c. singular_subdivision (Suc p) (k p c) + h p c)"
  show ?case
  proof (rule Suc.prems)
    fix p X and c :: "'a chain"
    assume "singular_chain p X c"
    then show "singular_chain (Suc p) X (?h p c)"
      by (simp add: h k singular_chain_add singular_chain_singular_subdivision)
  next
    fix p :: "nat" and X :: "'a topology" and c :: "'a chain"
    assume sc: "singular_chain p X c"
    have f5: "chain_boundary (Suc p) (singular_subdivision (Suc p) (k p c)) = singular_subdivision p (chain_boundary (Suc p) (k p c))"
      using chain_boundary_singular_subdivision k(3) sc by fastforce
    have [simp]: "singular_subdivision (Suc (p - Suc 0)) (k (p - Suc 0) (chain_boundary p c)) =
                  singular_subdivision p (k (p - Suc 0) (chain_boundary p c))"
    proof (cases p)
      case 0
      then show ?thesis
        by (simp add: k chain_boundary_def)
    qed auto
    show "chain_boundary (Suc p) (?h p c) + ?h (p - Suc 0) (chain_boundary p c) = (singular_subdivision p ^^ Suc n) c - c"
      using chain_boundary_singular_subdivision [of "Suc p" X]
      apply (simp add: chain_boundary_add f5 h k algebra_simps)
      apply (smt (verit, ccfv_threshold) add.commute add_diff_eq diff_add_cancel diff_diff_eq2 h(4) k(4) sc singular_subdivision_add)
      done
  qed (auto simp: k h singular_subdivision_diff)
qed

lemma llemma:
  assumes p: "standard_simplex p \<subseteq> \<Union>\<C>"
      and \<C>: "\<And>U. U \<in> \<C> \<Longrightarrow> openin (powertop_real UNIV) U"
  obtains d where "0 < d"
                  "\<And>K. \<lbrakk>K \<subseteq> standard_simplex p;
                        \<And>x y i. \<lbrakk>i \<le> p; x \<in> K; y \<in> K\<rbrakk> \<Longrightarrow> \<bar>x i - y i\<bar> \<le> d\<rbrakk>
                       \<Longrightarrow> \<exists>U. U \<in> \<C> \<and> K \<subseteq> U"
proof -
  have "\<exists>e U. 0 < e \<and> U \<in> \<C> \<and> x \<in> U \<and>
                (\<forall>y. (\<forall>i\<le>p. \<bar>y i - x i\<bar> \<le> 2 * e) \<and> (\<forall>i>p. y i = 0) \<longrightarrow> y \<in> U)"
    if x: "x \<in> standard_simplex p" for x
  proof-
    obtain U where U: "U \<in> \<C>" "x \<in> U"
      using x p by blast
    then obtain V where finV: "finite {i. V i \<noteq> UNIV}" and openV: "\<And>i. open (V i)"
                  and xV: "x \<in> Pi\<^sub>E UNIV V" and UV: "Pi\<^sub>E UNIV V \<subseteq> U"
      using \<C> unfolding openin_product_topology_alt by force
    have xVi: "x i \<in> V i" for i
      using PiE_mem [OF xV] by simp
    have "\<And>i. \<exists>e>0. \<forall>x'. \<bar>x' - x i\<bar> < e \<longrightarrow> x' \<in> V i"
      by (rule openV [unfolded open_real, rule_format, OF xVi])
    then obtain d where d: "\<And>i. d i > 0" and dV: "\<And>i x'. \<bar>x' - x i\<bar> < d i \<Longrightarrow> x' \<in> V i"
      by metis
    define e where "e \<equiv> Inf (insert 1 (d ` {i. V i \<noteq> UNIV})) / 3"
    have ed3: "e \<le> d i / 3" if "V i \<noteq> UNIV" for i
      using that finV by (auto simp: e_def intro: cInf_le_finite)
    show "\<exists>e U. 0 < e \<and> U \<in> \<C> \<and> x \<in> U \<and>
                (\<forall>y. (\<forall>i\<le>p. \<bar>y i - x i\<bar> \<le> 2 * e) \<and> (\<forall>i>p. y i = 0) \<longrightarrow> y \<in> U)"
    proof (intro exI conjI allI impI)
      show "e > 0"
        using d finV by (simp add: e_def finite_less_Inf_iff)
      fix y assume y: "(\<forall>i\<le>p. \<bar>y i - x i\<bar> \<le> 2 * e) \<and> (\<forall>i>p. y i = 0)"
      have "y \<in> Pi\<^sub>E UNIV V"
      proof
        show "y i \<in> V i" for i
        proof (cases "p < i")
          case True
          then show ?thesis
            by (metis (mono_tags, lifting) y x mem_Collect_eq standard_simplex_def xVi)
        next
          case False show ?thesis
          proof (cases "V i = UNIV")
            case False show ?thesis
            proof (rule dV)
              have "\<bar>y i - x i\<bar> \<le> 2 * e"
                using y \<open>\<not> p < i\<close> by simp
              also have "\<dots> < d i"
                using ed3 [OF False] \<open>e > 0\<close> by simp
              finally show "\<bar>y i - x i\<bar> < d i" .
            qed
          qed auto
        qed
      qed auto
      with UV show "y \<in> U"
        by blast
    qed (use U in auto)
  qed
  then obtain e U where
      eU: "\<And>x. x \<in> standard_simplex p \<Longrightarrow>
                0 < e x \<and> U x \<in> \<C> \<and> x \<in> U x"
      and  UI: "\<And>x y. \<lbrakk>x \<in> standard_simplex p;  \<And>i. i \<le> p \<Longrightarrow> \<bar>y i - x i\<bar> \<le> 2 * e x; \<And>i. i > p \<Longrightarrow> y i = 0\<rbrakk>
                       \<Longrightarrow> y \<in> U x"
    by metis
  define F where "F \<equiv> \<lambda>x. Pi\<^sub>E UNIV (\<lambda>i. if i \<le> p then {x i - e x<..<x i + e x} else UNIV)"
  have "\<forall>S \<in> F ` standard_simplex p. openin (powertop_real UNIV) S"
    by (simp add: F_def openin_PiE_gen)
  moreover have pF: "standard_simplex p \<subseteq> \<Union>(F ` standard_simplex p)"
    by (force simp: F_def PiE_iff eU)
  ultimately have "\<exists>\<F>. finite \<F> \<and> \<F> \<subseteq> F ` standard_simplex p \<and> standard_simplex p \<subseteq> \<Union>\<F>"
    using compactin_standard_simplex [of p]
    unfolding compactin_def by force
  then obtain S where "finite S" and ssp: "S \<subseteq> standard_simplex p" "standard_simplex p \<subseteq> \<Union>(F ` S)"
    unfolding ex_finite_subset_image by (auto simp: ex_finite_subset_image)
  then have "S \<noteq> {}"
    by (auto simp: nonempty_standard_simplex)
  show ?thesis
  proof
    show "Inf (e ` S) > 0"
      using \<open>finite S\<close> \<open>S \<noteq> {}\<close> ssp eU by (auto simp: finite_less_Inf_iff)
    fix k :: "(nat \<Rightarrow> real) set"
    assume k: "k \<subseteq> standard_simplex p"
         and kle: "\<And>x y i. \<lbrakk>i \<le> p; x \<in> k; y \<in> k\<rbrakk> \<Longrightarrow> \<bar>x i - y i\<bar> \<le> Inf (e ` S)"
    show "\<exists>U. U \<in> \<C> \<and> k \<subseteq> U"
    proof (cases "k = {}")
      case True
      then show ?thesis
        using \<open>S \<noteq> {}\<close> eU equals0I ssp(1) subset_eq p by auto
    next
      case False
      with k ssp obtain x a where "x \<in> k" "x \<in> standard_simplex p"
                            and a: "a \<in> S" and Fa: "x \<in> F a"
        by blast
      then have le_ea: "\<And>i. i \<le> p \<Longrightarrow> abs (x i - a i) < e a"
        by (simp add: F_def PiE_iff if_distrib abs_diff_less_iff cong: if_cong)
      show ?thesis
      proof (intro exI conjI)
        show "U a \<in> \<C>"
          using a eU ssp(1) by auto
        show "k \<subseteq> U a"
        proof clarify
          fix y assume "y \<in> k"
          with k have y: "y \<in> standard_simplex p"
            by blast
          show "y \<in> U a"
          proof (rule UI)
            show "a \<in> standard_simplex p"
              using a ssp(1) by auto
            fix i :: "nat"
            assume "i \<le> p"
            then have "\<bar>x i - y i\<bar> \<le> e a"
              by (meson kle [OF \<open>i \<le> p\<close>] a \<open>finite S\<close> \<open>x \<in> k\<close> \<open>y \<in> k\<close> cInf_le_finite finite_imageI imageI order_trans)
            then show "\<bar>y i - a i\<bar> \<le> 2 * e a"
              using le_ea [OF \<open>i \<le> p\<close>] by linarith
          next
            fix i assume "p < i"
            then show "y i = 0"
              using standard_simplex_def y by auto
          qed
        qed
      qed
    qed
  qed
qed


proposition sufficient_iterated_singular_subdivision_exists:
  assumes \<C>: "\<And>U. U \<in> \<C> \<Longrightarrow> openin X U"
      and X: "topspace X \<subseteq> \<Union>\<C>"
      and p: "singular_chain p X c"
  obtains n where "\<And>m f. \<lbrakk>n \<le> m; f \<in> Poly_Mapping.keys ((singular_subdivision p ^^ m) c)\<rbrakk>
                      \<Longrightarrow> \<exists>V \<in> \<C>. f ` (standard_simplex p) \<subseteq> V"
proof (cases "c = 0")
  case False
  then show ?thesis
  proof (cases "topspace X = {}")
    case True
    show ?thesis
      using p that by (force simp: singular_chain_empty True)
  next
    case False
    show ?thesis
    proof (cases "\<C> = {}")
      case True
      then show ?thesis
        using False X by blast
    next
      case False
      have "\<exists>e. 0 < e \<and>
                (\<forall>K. K \<subseteq> standard_simplex p \<longrightarrow> (\<forall>x y i. x \<in> K \<and> y \<in> K \<and> i \<le> p \<longrightarrow> \<bar>x i - y i\<bar> \<le> e)
                     \<longrightarrow> (\<exists>V. V \<in> \<C> \<and> f ` K \<subseteq> V))"
        if f: "f \<in> Poly_Mapping.keys c" for f
      proof -
        have ssf: "singular_simplex p X f"
          using f p by (auto simp: singular_chain_def)
        then have fp: "\<And>x. x \<in> standard_simplex p \<Longrightarrow> f x \<in> topspace X"
          by (auto simp: singular_simplex_def image_subset_iff dest: continuous_map_image_subset_topspace)
        have "\<exists>T. openin (powertop_real UNIV) T \<and>
                    standard_simplex p \<inter> f -` V = T \<inter> standard_simplex p"
          if V: "V \<in> \<C>" for V
        proof -
          have "singular_simplex p X f"
            using p f unfolding singular_chain_def by blast
          then have "openin (subtopology (powertop_real UNIV) (standard_simplex p))
                            {x \<in> standard_simplex p. f x \<in> V}"
            using \<C> [OF \<open>V \<in> \<C>\<close>] by (simp add: singular_simplex_def continuous_map_def)
          moreover have "standard_simplex p \<inter> f -` V = {x \<in> standard_simplex p. f x \<in> V}"
            by blast
          ultimately show ?thesis
            by (simp add: openin_subtopology)
        qed
        then obtain g where gope: "\<And>V. V \<in> \<C> \<Longrightarrow> openin (powertop_real UNIV) (g V)"
                and geq: "\<And>V. V \<in> \<C> \<Longrightarrow> standard_simplex p \<inter> f -` V = g V \<inter> standard_simplex p"
          by metis
        obtain d where "0 < d"
              and d: "\<And>K. \<lbrakk>K \<subseteq> standard_simplex p; \<And>x y i. \<lbrakk>i \<le> p; x \<in> K; y \<in> K\<rbrakk> \<Longrightarrow> \<bar>x i - y i\<bar> \<le> d\<rbrakk>
                       \<Longrightarrow> \<exists>U. U \<in> g ` \<C> \<and> K \<subseteq> U"
        proof (rule llemma [of p "g ` \<C>"])
          show "standard_simplex p \<subseteq> \<Union>(g ` \<C>)"
            using geq X fp by (fastforce simp add:)
          show "openin (powertop_real UNIV) U" if "U \<in> g ` \<C>" for U :: "(nat \<Rightarrow> real) set"
            using gope that by blast
        qed auto
        show ?thesis
        proof (rule exI, intro allI conjI impI)
          fix K :: "(nat \<Rightarrow> real) set"
          assume K: "K \<subseteq> standard_simplex p"
             and Kd: "\<forall>x y i. x \<in> K \<and> y \<in> K \<and> i \<le> p \<longrightarrow> \<bar>x i - y i\<bar> \<le> d"
          then have "\<exists>U. U \<in> g ` \<C> \<and> K \<subseteq> U"
            using d [OF K] by auto
          then show "\<exists>V. V \<in> \<C> \<and> f ` K \<subseteq> V"
            using K geq by fastforce
        qed (rule \<open>d > 0\<close>)
      qed
      then obtain \<psi> where epos: "\<forall>f \<in> Poly_Mapping.keys c. 0 < \<psi> f"
                 and e: "\<And>f K. \<lbrakk>f \<in> Poly_Mapping.keys c; K \<subseteq> standard_simplex p;
                                \<And>x y i. x \<in> K \<and> y \<in> K \<and> i \<le> p \<Longrightarrow> \<bar>x i - y i\<bar> \<le> \<psi> f\<rbrakk>
                               \<Longrightarrow> \<exists>V. V \<in> \<C> \<and> f ` K \<subseteq> V"
        by metis
      obtain d where "0 < d"
               and d: "\<And>f K. \<lbrakk>f \<in> Poly_Mapping.keys c; K \<subseteq> standard_simplex p;
                              \<And>x y i. \<lbrakk>x \<in> K; y \<in> K; i \<le> p\<rbrakk> \<Longrightarrow> \<bar>x i - y i\<bar> \<le> d\<rbrakk>
                              \<Longrightarrow> \<exists>V. V \<in> \<C> \<and> f ` K \<subseteq> V"
      proof
        show "Inf (\<psi> ` Poly_Mapping.keys c) > 0"
          by (simp add: finite_less_Inf_iff \<open>c \<noteq> 0\<close> epos)
        fix f K
        assume fK: "f \<in> Poly_Mapping.keys c" "K \<subseteq> standard_simplex p"
          and le: "\<And>x y i. \<lbrakk>x \<in> K; y \<in> K; i \<le> p\<rbrakk> \<Longrightarrow> \<bar>x i - y i\<bar> \<le> Inf (\<psi> ` Poly_Mapping.keys c)"
        then have lef: "Inf (\<psi> ` Poly_Mapping.keys c) \<le> \<psi> f"
          by (auto intro: cInf_le_finite)
        show "\<exists>V. V \<in> \<C> \<and> f ` K \<subseteq> V"
          using le lef by (blast intro: dual_order.trans e [OF fK])
      qed
      let ?d = "\<lambda>m. (simplicial_subdivision p ^^ m) (frag_of (restrict id (standard_simplex p)))"
      obtain n where n: "(p / (Suc p)) ^ n < d"
        using real_arch_pow_inv \<open>0 < d\<close> by fastforce
      show ?thesis
      proof
        fix m h
        assume "n \<le> m" and "h \<in> Poly_Mapping.keys ((singular_subdivision p ^^ m) c)"
        then obtain f where "f \<in> Poly_Mapping.keys c" "h \<in> Poly_Mapping.keys (chain_map p f (?d m))"
          using subsetD [OF keys_frag_extend] iterated_singular_subdivision [OF p, of m] by force
        then obtain g where g: "g \<in> Poly_Mapping.keys (?d m)" and heq: "h = restrict (f \<circ> g) (standard_simplex p)"
          using keys_frag_extend by (force simp: chain_map_def simplex_map_def)
        have xx: "simplicial_chain p (standard_simplex p) (?d n) \<and>
                  (\<forall>f \<in> Poly_Mapping.keys(?d n). \<forall>x \<in> standard_simplex p. \<forall>y \<in> standard_simplex p.
                       \<bar>f x i - f y i\<bar> \<le> (p / (Suc p)) ^ n)"
          for n i
        proof (induction n)
          case 0
          have "simplicial_simplex p (standard_simplex p) (\<lambda>a\<in>standard_simplex p. a)"
            by (metis eq_id_iff order_refl simplicial_simplex_id)
          moreover have "(\<forall>x\<in>standard_simplex p. \<forall>y\<in>standard_simplex p. \<bar>x i - y i\<bar> \<le> 1)"
            unfolding standard_simplex_def
            by (auto simp: abs_if dest!: spec [where x=i])
          ultimately show ?case
            unfolding power_0 funpow_0 by simp
        next
          case (Suc n)
          show ?case
            unfolding power_Suc funpow.simps o_def
          proof (intro conjI ballI)
            show "simplicial_chain p (standard_simplex p) (simplicial_subdivision p (?d n))"
              by (simp add: Suc simplicial_chain_simplicial_subdivision)
            show "\<bar>f x i - f y i\<bar> \<le> real p / real (Suc p) * (real p / real (Suc p)) ^ n"
              if "f \<in> Poly_Mapping.keys (simplicial_subdivision p (?d n))"
                and "x \<in> standard_simplex p" and "y \<in> standard_simplex p" for f x y
              using Suc that by (blast intro: simplicial_subdivision_shrinks)
          qed
        qed
        have "g ` standard_simplex p \<subseteq> standard_simplex p"
          using g xx [of m] unfolding simplicial_chain_def simplicial_simplex by auto
        moreover
        have "\<bar>g x i - g y i\<bar> \<le> d" if "i \<le> p" "x \<in> standard_simplex p" "y \<in> standard_simplex p" for x y i
        proof -
          have "\<bar>g x i - g y i\<bar> \<le> (p / (Suc p)) ^ m"
            using g xx [of m] that by blast
          also have "\<dots> \<le> (p / (Suc p)) ^ n"
            by (auto intro: power_decreasing [OF \<open>n \<le> m\<close>])
          finally show ?thesis using n by simp
        qed
        then have "\<bar>x i - y i\<bar> \<le> d"
          if "x \<in> g ` (standard_simplex p)" "y \<in> g ` (standard_simplex p)" "i \<le> p" for i x y
          using that by blast
        ultimately show "\<exists>V\<in>\<C>. h ` standard_simplex p \<subseteq> V"
          using \<open>f \<in> Poly_Mapping.keys c\<close> d [of f "g ` standard_simplex p"]
          by (simp add: Bex_def heq image_image)
      qed
    qed
  qed
qed force


lemma small_homologous_rel_relcycle_exists:
  assumes \<C>: "\<And>U. U \<in> \<C> \<Longrightarrow> openin X U"
      and X: "topspace X \<subseteq> \<Union>\<C>"
      and p: "singular_relcycle p X S c"
    obtains c' where "singular_relcycle p X S c'" "homologous_rel p X S c c'"
                      "\<And>f. f \<in> Poly_Mapping.keys c' \<Longrightarrow> \<exists>V \<in> \<C>. f ` (standard_simplex p) \<subseteq> V"
proof -
  have "singular_chain p X c"
       "(chain_boundary p c, 0) \<in> (mod_subset (p - Suc 0) (subtopology X S))"
    using p unfolding singular_relcycle_def by auto
  then obtain n where n: "\<And>m f. \<lbrakk>n \<le> m; f \<in> Poly_Mapping.keys ((singular_subdivision p ^^ m) c)\<rbrakk>
                            \<Longrightarrow> \<exists>V \<in> \<C>. f ` (standard_simplex p) \<subseteq> V"
    by (blast intro: sufficient_iterated_singular_subdivision_exists [OF \<C> X])
  let ?c' = "(singular_subdivision p ^^ n) c"
  show ?thesis
  proof
    show "homologous_rel p X S c ?c'"
      apply (induction n, simp_all)
      by (metis p homologous_rel_singular_subdivision homologous_rel_singular_relcycle homologous_rel_trans homologous_rel_sym)
    then show "singular_relcycle p X S ?c'"
      by (metis homologous_rel_singular_relcycle p)
  next
    fix f :: "(nat \<Rightarrow> real) \<Rightarrow> 'a"
    assume "f \<in> Poly_Mapping.keys ?c'"
    then show "\<exists>V\<in>\<C>. f ` standard_simplex p \<subseteq> V"
      by (rule n [OF order_refl])
  qed
qed

lemma excised_chain_exists:
  fixes S :: "'a set"
  assumes "X closure_of U \<subseteq> X interior_of T" "T \<subseteq> S" "singular_chain p (subtopology X S) c"
  obtains n d e where "singular_chain p (subtopology X (S - U)) d"
                      "singular_chain p (subtopology X T) e"
                      "(singular_subdivision p ^^ n) c = d + e"
proof -
  have *: "\<exists>n d e. singular_chain p (subtopology X (S - U)) d \<and>
                  singular_chain p (subtopology X T) e \<and>
                  (singular_subdivision p ^^ n) c = d + e"
    if c: "singular_chain p (subtopology X S) c"
       and X: "X closure_of U \<subseteq> X interior_of T" "U \<subseteq> topspace X" and S: "T \<subseteq> S" "S \<subseteq> topspace X"
       for p X c S and T U :: "'a set"
  proof -
    obtain n where n: "\<And>m f. \<lbrakk>n \<le> m; f \<in> Poly_Mapping.keys ((singular_subdivision p ^^ m) c)\<rbrakk>
                             \<Longrightarrow> \<exists>V \<in> {S \<inter> X interior_of T, S - X closure_of U}. f ` standard_simplex p \<subseteq> V"
      apply (rule sufficient_iterated_singular_subdivision_exists
                   [of "{S \<inter> X interior_of T, S - X closure_of U}"])
      using X S c
      by (auto simp: topspace_subtopology openin_subtopology_Int2 openin_subtopology_diff_closed)
    let ?c' = "\<lambda>n. (singular_subdivision p ^^ n) c"
    have "singular_chain p (subtopology X S) (?c' m)" for m
      by (induction m) (auto simp: singular_chain_singular_subdivision c)
    then have scp: "singular_chain p (subtopology X S) (?c' n)" .

    have SS: "Poly_Mapping.keys (?c' n) \<subseteq> singular_simplex_set p (subtopology X (S - U))
                              \<union> singular_simplex_set p (subtopology X T)"
    proof (clarsimp)
      fix f
      assume f: "f \<in> Poly_Mapping.keys ((singular_subdivision p ^^ n) c)"
         and non: "\<not> singular_simplex p (subtopology X T) f"
      show "singular_simplex p (subtopology X (S - U)) f"
        using n [OF order_refl f] scp f non closure_of_subset [OF \<open>U \<subseteq> topspace X\<close>] interior_of_subset [of X T]
        by (fastforce simp: image_subset_iff singular_simplex_subtopology singular_chain_def)
    qed
    show ?thesis
       unfolding singular_chain_def using frag_split [OF SS] by metis
  qed
  have "(subtopology X (topspace X \<inter> S)) = (subtopology X S)"
    by (metis subtopology_subtopology subtopology_topspace)
  with assms have c: "singular_chain p (subtopology X (topspace X \<inter> S)) c"
    by simp
  have Xsub: "X closure_of (topspace X \<inter> U) \<subseteq> X interior_of (topspace X \<inter> T)"
    using assms closure_of_restrict interior_of_restrict by fastforce
  obtain n d e where
    d: "singular_chain p (subtopology X (topspace X \<inter> S - topspace X \<inter> U)) d"
    and e: "singular_chain p (subtopology X (topspace X \<inter> T)) e"
    and de: "(singular_subdivision p ^^ n) c = d + e"
    using *[OF c Xsub, simplified] assms by force
  show thesis
  proof
    show "singular_chain p (subtopology X (S - U)) d"
      by (metis d Diff_Int_distrib inf.cobounded2 singular_chain_mono)
    show "singular_chain p (subtopology X T) e"
      by (metis e inf.cobounded2 singular_chain_mono)
    show "(singular_subdivision p ^^ n) c = d + e"
      by (rule de)
  qed
qed


lemma excised_relcycle_exists:
  fixes S :: "'a set"
  assumes X: "X closure_of U \<subseteq> X interior_of T" and "T \<subseteq> S"
      and c: "singular_relcycle p (subtopology X S) T c"
  obtains c' where "singular_relcycle p (subtopology X (S - U)) (T - U) c'"
                   "homologous_rel p (subtopology X S) T c c'"
proof -
  have [simp]: "(S - U) \<inter> (T - U) = T - U" "S \<inter> T = T"
    using \<open>T \<subseteq> S\<close> by auto
  have scc: "singular_chain p (subtopology X S) c"
    and scp1: "singular_chain (p - Suc 0) (subtopology X T) (chain_boundary p c)"
    using c by (auto simp: singular_relcycle_def mod_subset_def subtopology_subtopology)
  obtain n d e where d: "singular_chain p (subtopology X (S - U)) d"
    and e: "singular_chain p (subtopology X T) e"
    and de: "(singular_subdivision p ^^ n) c = d + e"
    using excised_chain_exists [OF X \<open>T \<subseteq> S\<close> scc] .
  have scSUd: "singular_chain (p - Suc 0) (subtopology X (S - U)) (chain_boundary p d)"
    by (simp add: singular_chain_boundary d)
  have sccn: "singular_chain p (subtopology X S) ((singular_subdivision p ^^ n) c)" for n
    by (induction n) (auto simp: singular_chain_singular_subdivision scc)
  have "singular_chain (p - Suc 0) (subtopology X T) (chain_boundary p ((singular_subdivision p ^^ n) c))"
  proof (induction n)
    case (Suc n)
    then show ?case
      by (simp add: singular_chain_singular_subdivision chain_boundary_singular_subdivision [OF sccn])
  qed (auto simp: scp1)
  then have "singular_chain (p - Suc 0) (subtopology X T) (chain_boundary p ((singular_subdivision p ^^ n) c - e))"
    by (simp add: chain_boundary_diff singular_chain_diff singular_chain_boundary e)
  with de have scTd: "singular_chain (p - Suc 0) (subtopology X T) (chain_boundary p d)"
    by simp
  show thesis
  proof
    have "singular_chain (p - Suc 0) X (chain_boundary p d)"
      using scTd singular_chain_subtopology by blast
    with scSUd scTd have "singular_chain (p - Suc 0) (subtopology X (T - U)) (chain_boundary p d)"
      by (fastforce simp add: singular_chain_subtopology)
    then show "singular_relcycle p (subtopology X (S - U)) (T - U) d"
      by (auto simp: singular_relcycle_def mod_subset_def subtopology_subtopology d)
    have "homologous_rel p (subtopology X S) T (c-0) ((singular_subdivision p ^^ n) c - e)"
    proof (rule homologous_rel_diff)
      show "homologous_rel p (subtopology X S) T c ((singular_subdivision p ^^ n) c)"
      proof (induction n)
        case (Suc n)
        then show ?case
          apply simp
          apply (rule homologous_rel_trans)
          using c homologous_rel_singular_relcycle_1 homologous_rel_singular_subdivision homologous_rel_sym by blast
      qed auto
      show "homologous_rel p (subtopology X S) T 0 e"
        unfolding homologous_rel_def using e
        by (intro singular_relboundary_diff singular_chain_imp_relboundary; simp add: subtopology_subtopology)
    qed
    with de show "homologous_rel p (subtopology X S) T c d"
      by simp
  qed
qed


subsection\<open>Homotopy invariance\<close>

theorem homotopic_imp_homologous_rel_chain_maps:
  assumes hom: "homotopic_with (\<lambda>h. h ` T \<subseteq> V) S U f g" and c: "singular_relcycle p S T c"
  shows "homologous_rel p U V (chain_map p f c) (chain_map p g c)"
proof -
  note sum.atMost_Suc [simp del]
  have contf: "continuous_map S U f" and contg: "continuous_map S U g"
    using homotopic_with_imp_continuous_maps [OF hom] by metis+
  obtain h where conth: "continuous_map (prod_topology (top_of_set {0..1::real}) S) U h"
    and h0: "\<And>x. h(0, x) = f x"
    and h1: "\<And>x. h(1, x) = g x"
    and hV: "\<And>t x. \<lbrakk>0 \<le> t; t \<le> 1; x \<in> T\<rbrakk> \<Longrightarrow> h(t,x) \<in> V"
    using hom by (fastforce simp: homotopic_with_def)
  define vv where "vv \<equiv> \<lambda>j i. if i = Suc j then 1 else (0::real)"
  define ww where "ww \<equiv> \<lambda>j i. if i=0 \<or> i = Suc j then 1 else (0::real)"
  define simp where "simp \<equiv> \<lambda>q i. oriented_simplex (Suc q) (\<lambda>j. if j \<le> i then vv j else ww(j -1))"
  define pr where "pr \<equiv> \<lambda>q c. \<Sum>i\<le>q. frag_cmul ((-1) ^ i)
                                        (frag_of (simplex_map (Suc q) (\<lambda>z. h(z 0, c(z \<circ> Suc))) (simp q i)))"
  have ss_ss: "simplicial_simplex (Suc q) ({x. x 0 \<in> {0..1} \<and> (x \<circ> Suc) \<in> standard_simplex q}) (simp q i)"
    if "i \<le> q" for q i
  proof -
    have "(\<Sum>j\<le>Suc q. (if j \<le> i then vv j 0 else ww (j -1) 0) * x j) \<in> {0..1}"
      if "x \<in> standard_simplex (Suc q)" for x
    proof -
      have "(\<Sum>j\<le>Suc q. if j \<le> i then 0 else x j) \<le> sum x {..Suc q}"
        using that unfolding standard_simplex_def
        by (force intro!: sum_mono)
      with \<open>i \<le> q\<close> that show ?thesis
        by (simp add: vv_def ww_def standard_simplex_def if_distrib [of "\<lambda>u. u * _"] sum_nonneg cong: if_cong)
    qed
    moreover
    have "(\<lambda>k. \<Sum>j\<le>Suc q. (if j \<le> i then vv j k else ww (j -1) k) * x j) \<circ> Suc \<in> standard_simplex q"
      if "x \<in> standard_simplex (Suc q)" for x
    proof -
      have card: "({..q} \<inter> {k. Suc k = j}) = {j-1}" if "0 < j" "j \<le> Suc q" for j
        using that by auto
      have eq: "(\<Sum>j\<le>Suc q. \<Sum>k\<le>q. if j \<le> i then if k = j then x j else 0 else if Suc k = j then x j else 0)
              = (\<Sum>j\<le>Suc q. x j)"
        by (rule sum.cong [OF refl]) (use \<open>i \<le> q\<close> in \<open>simp add: sum.If_cases card\<close>)
      have "(\<Sum>j\<le>Suc q. if j \<le> i then if k = j then x j else 0 else if Suc k = j then x j else 0)
            \<le> sum x {..Suc q}" for k
        using that unfolding standard_simplex_def
        by (force intro!: sum_mono)
      then show ?thesis
        using \<open>i \<le> q\<close> that
        by (simp add: vv_def ww_def standard_simplex_def if_distrib [of "\<lambda>u. u * _"] sum_nonneg
            sum.swap [where A = "atMost q"] eq cong: if_cong)
    qed
    ultimately show ?thesis
      by (simp add: that simplicial_simplex_oriented_simplex simp_def image_subset_iff if_distribR)
  qed
  obtain prism where prism: "\<And>q. prism q 0 = 0"
    "\<And>q c. singular_chain q S c \<Longrightarrow> singular_chain (Suc q) U (prism q c)"
    "\<And>q c. singular_chain q (subtopology S T) c
                           \<Longrightarrow> singular_chain (Suc q) (subtopology U V) (prism q c)"
    "\<And>q c. singular_chain q S c
                           \<Longrightarrow> chain_boundary (Suc q) (prism q c) =
                               chain_map q g c - chain_map q f c - prism (q -1) (chain_boundary q c)"
  proof
    show "(frag_extend \<circ> pr) q 0 = 0" for q
      by (simp add: pr_def)
  next
    show "singular_chain (Suc q) U ((frag_extend \<circ> pr) q c)"
      if "singular_chain q S c" for q c
      using that [unfolded singular_chain_def]
    proof (induction c rule: frag_induction)
      case (one m)
      show ?case
      proof (simp add: pr_def, intro singular_chain_cmul singular_chain_sum)
        fix i :: "nat"
        assume "i \<in> {..q}"
        define X where "X = subtopology (powertop_real UNIV) {x. x 0 \<in> {0..1} \<and> (x \<circ> Suc) \<in> standard_simplex q}"
        show "singular_chain (Suc q) U
                 (frag_of (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i)))"
          unfolding singular_chain_of
        proof (rule singular_simplex_simplex_map)
          show "singular_simplex (Suc q) X (simp q i)"
            unfolding X_def using \<open>i \<in> {..q}\<close> simplicial_imp_singular_simplex ss_ss by blast
          have 0: "continuous_map X (top_of_set {0..1}) (\<lambda>x. x 0)"
            unfolding continuous_map_in_subtopology topspace_subtopology X_def
            by (auto intro: continuous_map_product_projection continuous_map_from_subtopology)
          have 1: "continuous_map X S (m \<circ> (\<lambda>x j. x (Suc j)))"
          proof (rule continuous_map_compose)
            have "continuous_map (powertop_real UNIV) (powertop_real UNIV) (\<lambda>x j. x (Suc j))"
              by (auto intro: continuous_map_product_projection)
            then show "continuous_map X (subtopology (powertop_real UNIV) (standard_simplex q)) (\<lambda>x j. x (Suc j))"
              unfolding X_def o_def
              by (auto simp: continuous_map_in_subtopology intro: continuous_map_from_subtopology continuous_map_product_projection)
          qed (use one in \<open>simp add: singular_simplex_def\<close>)
          show "continuous_map X U (\<lambda>z. h (z 0, m (z \<circ> Suc)))"
            apply (rule continuous_map_compose [unfolded o_def, OF _ conth])
            using 0 1 by (simp add: continuous_map_pairwise o_def)
        qed
      qed
    next
      case (diff a b)
      then show ?case
        apply (simp add: frag_extend_diff keys_diff)
        using singular_chain_def singular_chain_diff by blast
    qed auto
  next
    show "singular_chain (Suc q) (subtopology U V) ((frag_extend \<circ> pr) q c)"
      if "singular_chain q (subtopology S T) c" for q c
      using that [unfolded singular_chain_def]
    proof (induction c rule: frag_induction)
      case (one m)
      show ?case
      proof (simp add: pr_def, intro singular_chain_cmul singular_chain_sum)
        fix i :: "nat"
        assume "i \<in> {..q}"
        define X where "X = subtopology (powertop_real UNIV) {x. x 0 \<in> {0..1} \<and> (x \<circ> Suc) \<in> standard_simplex q}"
        show "singular_chain (Suc q) (subtopology U V)
                 (frag_of (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i)))"
          unfolding singular_chain_of
        proof (rule singular_simplex_simplex_map)
          show "singular_simplex (Suc q) X (simp q i)"
            unfolding X_def using \<open>i \<in> {..q}\<close> simplicial_imp_singular_simplex ss_ss by blast
          have 0: "continuous_map X (top_of_set {0..1}) (\<lambda>x. x 0)"
            unfolding continuous_map_in_subtopology topspace_subtopology X_def
            by (auto intro: continuous_map_product_projection continuous_map_from_subtopology)
          have 1: "continuous_map X (subtopology S T) (m \<circ> (\<lambda>x j. x (Suc j)))"
          proof (rule continuous_map_compose)
            have "continuous_map (powertop_real UNIV) (powertop_real UNIV) (\<lambda>x j. x (Suc j))"
              by (auto intro: continuous_map_product_projection)
            then show "continuous_map X (subtopology (powertop_real UNIV) (standard_simplex q)) (\<lambda>x j. x (Suc j))"
              unfolding X_def o_def
              by (auto simp: continuous_map_in_subtopology intro: continuous_map_from_subtopology continuous_map_product_projection)
            show "continuous_map (subtopology (powertop_real UNIV) (standard_simplex q)) (subtopology S T) m"
              using one continuous_map_into_fulltopology by (auto simp: singular_simplex_def)
          qed
          have "continuous_map X (subtopology U V) (h \<circ> (\<lambda>z. (z 0, m (z \<circ> Suc))))"
          proof (rule continuous_map_compose)
            show "continuous_map X (prod_topology (top_of_set {0..1::real}) (subtopology S T)) (\<lambda>z. (z 0, m (z \<circ> Suc)))"
              using 0 1 by (simp add: continuous_map_pairwise o_def)
            have "continuous_map (subtopology (prod_topology euclideanreal S) ({0..1} \<times> T)) U h"
              by (metis conth continuous_map_from_subtopology subtopology_Times subtopology_topspace)
            with hV show "continuous_map (prod_topology (top_of_set {0..1::real}) (subtopology S T)) (subtopology U V) h"
              by (force simp: topspace_subtopology continuous_map_in_subtopology subtopology_restrict subtopology_Times)
          qed
          then show "continuous_map X (subtopology U V) (\<lambda>z. h (z 0, m (z \<circ> Suc)))"
            by (simp add: o_def)
        qed
      qed
    next
      case (diff a b)
      then show ?case
        by (metis comp_apply frag_extend_diff singular_chain_diff)
    qed auto
  next
    show "chain_boundary (Suc q) ((frag_extend \<circ> pr) q c) =
        chain_map q g c - chain_map q f c - (frag_extend \<circ> pr) (q -1) (chain_boundary q c)"
      if "singular_chain q S c" for q c
      using that [unfolded singular_chain_def]
    proof (induction c rule: frag_induction)
      case (one m)
      have eq2: "Sigma S T = (\<lambda>i. (i,i)) ` {i \<in> S. i \<in> T i} \<union> (Sigma S (\<lambda>i. T i - {i}))" for S :: "nat set" and T
        by force
      have 1: "(\<Sum>(i,j)\<in>(\<lambda>i. (i, i)) ` {i. i \<le> q \<and> i \<le> Suc q}.
                   frag_cmul (((-1) ^ i) * (-1) ^ j)
                      (frag_of
                        (singular_face (Suc q) j
                          (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i)))))
             + (\<Sum>(i,j)\<in>(\<lambda>i. (i, i)) ` {i. i \<le> q}.
                     frag_cmul (- ((-1) ^ i * (-1) ^ j))
                        (frag_of
                          (singular_face (Suc q) (Suc j)
                            (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i)))))
             = frag_of (simplex_map q g m) - frag_of (simplex_map q f m)"
      proof -
        have "restrict ((\<lambda>z. h (z 0, m (z \<circ> Suc))) \<circ> (simp q 0 \<circ> simplical_face 0)) (standard_simplex q)
          = restrict (g \<circ> m) (standard_simplex q)"
        proof (rule restrict_ext)
          fix x
          assume x: "x \<in> standard_simplex q"
          have "(\<Sum>j\<le>Suc q. if j = 0 then 0 else x (j - Suc 0)) = (\<Sum>j\<le>q. x j)"
            by (simp add: sum.atMost_Suc_shift)
          with x have "simp q 0 (simplical_face 0 x) 0 = 1"
            apply (simp add: oriented_simplex_def simp_def simplical_face_in_standard_simplex)
            apply (simp add: simplical_face_def if_distrib ww_def standard_simplex_def cong: if_cong)
            done
          moreover
          have "(\<lambda>n. if n \<le> q then x n else 0) = x"
            using standard_simplex_def x by auto
          then have "(\<lambda>n. simp q 0 (simplical_face 0 x) (Suc n)) = x"
            unfolding oriented_simplex_def simp_def ww_def using x
            apply (simp add: simplical_face_in_standard_simplex)
            apply (simp add: simplical_face_def if_distrib)
            apply (simp add: if_distribR if_distrib cong: if_cong)
            done
          ultimately show "((\<lambda>z. h (z 0, m (z \<circ> Suc))) \<circ> (simp q 0 \<circ> simplical_face 0)) x = (g \<circ> m) x"
            by (simp add: o_def h1)
        qed
        then have a: "frag_of (singular_face (Suc q) 0 (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q 0)))
             = frag_of (simplex_map q g m)"
          by (simp add: singular_face_simplex_map) (simp add: simplex_map_def)
        have "restrict ((\<lambda>z. h (z 0, m (z \<circ> Suc))) \<circ> (simp q q \<circ> simplical_face (Suc q))) (standard_simplex q)
          = restrict (f \<circ> m) (standard_simplex q)"
        proof (rule restrict_ext)
          fix x
          assume x: "x \<in> standard_simplex q"
          then have "simp q q (simplical_face (Suc q) x) 0 = 0"
            unfolding oriented_simplex_def simp_def
            by (simp add: simplical_face_in_standard_simplex sum.atMost_Suc) (simp add: simplical_face_def vv_def)
          moreover have "(\<lambda>n. simp q q (simplical_face (Suc q) x) (Suc n)) = x"
            unfolding oriented_simplex_def simp_def vv_def using x
            apply (simp add: simplical_face_in_standard_simplex)
            apply (force simp: standard_simplex_def simplical_face_def if_distribR if_distrib [of "\<lambda>x. x * _"] sum.atMost_Suc cong: if_cong)
            done
          ultimately show "((\<lambda>z. h (z 0, m (z \<circ> Suc))) \<circ> (simp q q \<circ> simplical_face (Suc q))) x = (f \<circ> m) x"
            by (simp add: o_def h0)
        qed
        then have b: "frag_of (singular_face (Suc q) (Suc q)
                     (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q q)))
          = frag_of (simplex_map q f m)"
          by (simp add: singular_face_simplex_map) (simp add: simplex_map_def)
        have sfeq: "simplex_map q (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q (Suc i) \<circ> simplical_face (Suc i))
                = simplex_map q (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i \<circ> simplical_face (Suc i))"
          if "i < q" for i
          unfolding simplex_map_def
        proof (rule restrict_ext)
          fix x
          assume "x \<in> standard_simplex q"
          then have "(simp q (Suc i) \<circ> simplical_face (Suc i)) x = (simp q i \<circ> simplical_face (Suc i)) x"
            unfolding oriented_simplex_def simp_def simplical_face_def
            by (force intro: sum.cong)
          then show "((\<lambda>z. h (z 0, m (z \<circ> Suc))) \<circ> (simp q (Suc i) \<circ> simplical_face (Suc i))) x
                 = ((\<lambda>z. h (z 0, m (z \<circ> Suc))) \<circ> (simp q i \<circ> simplical_face (Suc i))) x"
            by simp
        qed
        have eqq: "{i. i \<le> q \<and> i \<le> Suc q} = {..q}"
          by force
        have qeq: "{..q} = insert 0 ((\<lambda>i. Suc i) ` {i. i < q})" "{i. i \<le> q} = insert q {i. i < q}"
          using le_imp_less_Suc less_Suc_eq_0_disj by auto
        show ?thesis
          using a b
          apply (simp add: sum.reindex inj_on_def eqq)
          apply (simp add: qeq sum.insert_if sum.reindex sum_negf singular_face_simplex_map sfeq)
          done
      qed
      have 2: "(\<Sum>(i,j)\<in>(SIGMA i:{..q}. {0..min (Suc q) i} - {i}).
                     frag_cmul ((-1) ^ i * (-1) ^ j)
                      (frag_of
                        (singular_face (Suc q) j
                          (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i)))))
             + (\<Sum>(i,j)\<in>(SIGMA i:{..q}. {i..q} - {i}).
                 frag_cmul (- ((-1) ^ i * (-1) ^ j))
                  (frag_of
                    (singular_face (Suc q) (Suc j)
                      (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i)))))
             = - frag_extend (pr (q - Suc 0)) (chain_boundary q (frag_of m))"
      proof (cases "q=0")
        case True
        then show ?thesis
          by (simp add: chain_boundary_def flip: sum.Sigma)
      next
        case False
        have eq: "{..q - Suc 0} \<times> {..q} = Sigma {..q - Suc 0} (\<lambda>i. {0..min q i}) \<union> Sigma {..q} (\<lambda>i. {i<..q})"
          by force
        have I: "(\<Sum>(i,j)\<in>(SIGMA i:{..q}. {0..min (Suc q) i} - {i}).
                    frag_cmul ((-1) ^ (i + j))
                      (frag_of
                        (singular_face (Suc q) j
                          (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i)))))
               = (\<Sum>(i,j)\<in>(SIGMA i:{..q - Suc 0}. {0..min q i}).
                   frag_cmul (- ((-1) ^ (j + i)))
                    (frag_of
                      (simplex_map q (\<lambda>z. h (z 0, singular_face q j m (z \<circ> Suc)))
                        (simp (q - Suc 0) i))))"
        proof -
          have seq: "simplex_map q (\<lambda>z. h (z 0, singular_face q j m (z \<circ> Suc)))
                       (simp (q - Suc 0) (i - Suc 0))
                   = simplex_map q (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i \<circ> simplical_face j)"
            if ij: "i \<le> q" "j \<noteq> i" "j \<le> i" for i j
            unfolding simplex_map_def
          proof (rule restrict_ext)
            fix x
            assume x: "x \<in> standard_simplex q"
            have "i > 0"
              using that by force
            then have iq: "i - Suc 0 \<le> q - Suc 0"
              using \<open>i \<le> q\<close> False by simp
            have q0_eq: "{..Suc q} = insert 0 (Suc ` {..q})"
              by (auto simp: image_def gr0_conv_Suc)
            have \<alpha>: "simp (q - Suc 0) (i - Suc 0) x 0 = simp q i (simplical_face j x) 0"
              using False x ij
              unfolding oriented_simplex_def simp_def vv_def ww_def
              apply (simp add: simplical_face_in_standard_simplex)
              apply (force simp: simplical_face_def q0_eq sum.reindex intro!: sum.cong)
              done
            have \<beta>: "simplical_face j (simp (q - Suc 0) (i - Suc 0) x \<circ> Suc) = simp q i (simplical_face j x) \<circ> Suc"
            proof
              fix k
              show "simplical_face j (simp (q - Suc 0) (i - Suc 0) x \<circ> Suc) k
                  = (simp q i (simplical_face j x) \<circ> Suc) k"
                using False x ij
                unfolding oriented_simplex_def simp_def o_def vv_def ww_def
                apply (simp add: simplical_face_in_standard_simplex if_distribR)
                apply (simp add: simplical_face_def if_distrib [of "\<lambda>u. u * _"] cong: if_cong)
                apply (intro impI conjI)
                 apply (force simp: sum.atMost_Suc intro: sum.cong)
                apply (force simp: q0_eq sum.reindex intro!: sum.cong)
                done
            qed
            have "simp (q - Suc 0) (i - Suc 0) x \<circ> Suc \<in> standard_simplex (q - Suc 0)"
              using ss_ss [OF iq] \<open>i \<le> q\<close> False \<open>i > 0\<close>
              apply (simp add: simplicial_simplex image_subset_iff)
              using \<open>x \<in> standard_simplex q\<close> by blast
            then show "((\<lambda>z. h (z 0, singular_face q j m (z \<circ> Suc))) \<circ> simp (q - Suc 0) (i - Suc 0)) x
                = ((\<lambda>z. h (z 0, m (z \<circ> Suc))) \<circ> (simp q i \<circ> simplical_face j)) x"
              by (simp add: singular_face_def \<alpha> \<beta>)
          qed
          have [simp]: "(-1::int) ^ (i + j - Suc 0) = - ((-1) ^ (i + j))" if "i \<noteq> j" for i j::nat
          proof -
            have "i + j > 0"
              using that by blast
            then show ?thesis
              by (metis (no_types, hide_lams) One_nat_def Suc_diff_1 add.inverse_inverse mult.left_neutral mult_minus_left power_Suc)
          qed
          show ?thesis
            apply (rule sum.eq_general_inverses [where h = "\<lambda>(a,b). (a-1,b)" and k = "\<lambda>(a,b). (Suc a,b)"])
            using False apply (auto simp: singular_face_simplex_map seq add.commute)
            done
        qed
        have *: "singular_face (Suc q) (Suc j) (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i))
               = simplex_map q (\<lambda>z. h (z 0, singular_face q j m (z \<circ> Suc))) (simp (q - Suc 0) i)"
          if ij: "i < j" "j \<le> q" for i j
        proof -
          have iq: "i \<le> q - Suc 0"
            using that by auto
          have sf_eqh: "singular_face (Suc q) (Suc j)
                           (\<lambda>x. if x \<in> standard_simplex (Suc q)
                                then ((\<lambda>z. h (z 0, m (z \<circ> Suc))) \<circ> simp q i) x else undefined) x
                      = h (simp (q - Suc 0) i x 0,
                           singular_face q j m (\<lambda>xa. simp (q - Suc 0) i x (Suc xa)))"
            if x: "x \<in> standard_simplex q" for x
          proof -
            let ?f = "\<lambda>k. \<Sum>j\<le>q. if j \<le> i then if k = j then x j else 0
                               else if Suc k = j then x j else 0"
            have fm: "simplical_face (Suc j) x \<in> standard_simplex (Suc q)"
              using ss_ss [OF iq] that ij
              by (simp add: simplical_face_in_standard_simplex)
            have ss: "?f \<in> standard_simplex (q - Suc 0)"
              unfolding standard_simplex_def
            proof (intro CollectI conjI impI allI)
              fix k
              show "0 \<le> ?f k"
                using that by (simp add: sum_nonneg standard_simplex_def)
              show "?f k \<le> 1"
                using x sum_le_included [of "{..q}" "{..q}" x "id"]
                by (simp add: standard_simplex_def)
              assume k: "q - Suc 0 < k"
              show "?f k = 0"
                by (rule sum.neutral) (use that x iq k standard_simplex_def in auto)
            next
              have "(\<Sum>k\<le>q - Suc 0. ?f k)
                  = (\<Sum>(k,j) \<in> ({..q - Suc 0} \<times> {..q}) \<inter> {(k,j). if j \<le> i then k = j else Suc k = j}. x j)"
                apply (simp add: sum.Sigma)
                by (rule sum.mono_neutral_cong) (auto simp: split: if_split_asm)
              also have "\<dots> = sum x {..q}"
                apply (rule sum.eq_general_inverses
                    [where h = "\<lambda>(k,j). if j\<le>i \<and> k=j \<or> j>i \<and> Suc k = j then j else Suc q"
                      and k = "\<lambda>j. if j \<le> i then (j,j) else (j - Suc 0, j)"])
                using ij by auto
              also have "\<dots> = 1"
                using x by (simp add: standard_simplex_def)
              finally show "(\<Sum>k\<le>q - Suc 0. ?f k) = 1"
                by (simp add: standard_simplex_def)
            qed
            let ?g = "\<lambda>k. if k \<le> i then 0
                              else if k < Suc j then x k
                                   else if k = Suc j then 0 else x (k - Suc 0)"
            have eq: "{..Suc q} = {..j} \<union> {Suc j} \<union> Suc`{j<..q}" "{..q} = {..j} \<union> {j<..q}"
              using ij image_iff less_Suc_eq_0_disj less_Suc_eq_le
              by (force simp: image_iff)+
            then have "(\<Sum>k\<le>Suc q. ?g k) = (\<Sum>k\<in>{..j} \<union> {Suc j} \<union> Suc`{j<..q}. ?g k)"
              by simp
            also have "\<dots> = (\<Sum>k\<in>{..j} \<union> Suc`{j<..q}. ?g k)"
              by (rule sum.mono_neutral_right) auto
            also have "\<dots> = (\<Sum>k\<in>{..j}. ?g k) + (\<Sum>k\<in>Suc`{j<..q}. ?g k)"
              by (rule sum.union_disjoint) auto
            also have "\<dots> = (\<Sum>k\<in>{..j}. ?g k) + (\<Sum>k\<in>{j<..q}. ?g (Suc k))"
              by (auto simp: sum.reindex)
            also have "\<dots> = (\<Sum>k\<in>{..j}. if k \<le> i then 0 else x k)
                           + (\<Sum>k\<in>{j<..q}. if k \<le> i then 0 else x k)"
              by (intro sum.cong arg_cong2 [of concl: "(+)"]) (use ij in auto)
            also have "\<dots> = (\<Sum>k\<le>q. if k \<le> i then 0 else x k)"
              unfolding eq by (subst sum.union_disjoint) auto
            finally have "(\<Sum>k\<le>Suc q. ?g k) = (\<Sum>k\<le>q. if k \<le> i then 0 else x k)" .
            then have QQ: "(\<Sum>l\<le>Suc q. if l \<le> i then 0 else simplical_face (Suc j) x l) = (\<Sum>j\<le>q. if j \<le> i then 0 else x j)"
              by (simp add: simplical_face_def cong: if_cong)
            have WW: "(\<lambda>k. \<Sum>l\<le>Suc q. if l \<le> i
                                    then if k = l then simplical_face (Suc j) x l else 0
                                    else if Suc k = l then simplical_face (Suc j) x l
                                    else 0)
                = simplical_face j
                   (\<lambda>k. \<Sum>j\<le>q. if j \<le> i then if k = j then x j else 0
                                else if Suc k = j then x j else 0)"
            proof -
              have *: "(\<Sum>l\<le>q. if l \<le> i then 0 else if Suc k = l then x (l - Suc 0) else 0)
                    = (\<Sum>l\<le>q. if l \<le> i then if k - Suc 0 = l then x l else 0 else if k = l then x l else 0)"
                (is "?lhs = ?rhs")
                if "k \<noteq> q" "k > j" for k
              proof (cases "k \<le> q")
                case True
                have "?lhs = sum (\<lambda>l. x (l - Suc 0)) {Suc k}" "?rhs = sum x {k}"
                  by (rule sum.mono_neutral_cong_right; use True ij that in auto)+
                then show ?thesis
                  by simp
              next
                case False
                have "?lhs = 0" "?rhs = 0"
                  by (rule sum.neutral; use False ij in auto)+
                then show ?thesis
                  by simp
              qed
              show ?thesis
                apply (rule ext)
                unfolding simplical_face_def using ij
                apply (auto simp: sum.atMost_Suc cong: if_cong)
                 apply (force simp flip: ivl_disj_un(2) intro: sum.neutral)
                 apply (auto simp: *)
                done
            qed
            show ?thesis
              using False that iq
              unfolding oriented_simplex_def simp_def vv_def ww_def
              apply (simp add: if_distribR cong: if_cong)
              apply (simp add: simplical_face_def if_distrib [of "\<lambda>u. u * _"] o_def cong: if_cong)
              apply (simp add: singular_face_def fm ss QQ WW)
              done
          qed
          show ?thesis
            unfolding simplex_map_def restrict_def
            apply (simp add: simplicial_simplex image_subset_iff o_def sf_eqh fun_eq_iff)
            apply (simp add: singular_face_def)
            done
        qed
        have sgeq: "(SIGMA i:{..q}. {i..q} - {i})  = (SIGMA i:{..q}. {i<..q})"
          by force
        have II: "(\<Sum>(i,j)\<in>(SIGMA i:{..q}. {i..q} - {i}).
                     frag_cmul (- ((-1) ^ (i + j)))
                      (frag_of
                        (singular_face (Suc q) (Suc j)
                          (simplex_map (Suc q) (\<lambda>z. h (z 0, m (z \<circ> Suc))) (simp q i))))) =
                  (\<Sum>(i,j)\<in>(SIGMA i:{..q}. {i<..q}).
                     frag_cmul (- ((-1) ^ (j + i)))
                      (frag_of
                        (simplex_map q (\<lambda>z. h (z 0, singular_face q j m (z \<circ> Suc)))
                          (simp (q - Suc 0) i))))"
          by (force simp: * sgeq add.commute intro: sum.cong)
        show ?thesis
          using False
          apply (simp add: chain_boundary_def frag_extend_sum frag_extend_cmul frag_cmul_sum pr_def flip: sum_negf power_add)
          apply (subst sum.swap [where A = "{..q}"])
          apply (simp add: sum.cartesian_product eq sum.union_disjoint disjoint_iff_not_equal I II)
          done
      qed
      have *: "\<lbrakk>a+b = w; c+d = -z\<rbrakk> \<Longrightarrow> (a + c) + (b+d) = w-z" for a b w c d z :: "'c \<Rightarrow>\<^sub>0 int"
        by (auto simp: algebra_simps)
      have eq: "{..q} \<times> {..Suc q} =
                Sigma {..q} (\<lambda>i. {0..min (Suc q) i})
              \<union> Sigma {..q} (\<lambda>i. {Suc i..Suc q})"
        by force
      show ?case
        apply (subst pr_def)
        apply (simp add: chain_boundary_sum chain_boundary_cmul)
        apply (subst chain_boundary_def)
        apply simp
        apply (simp add: frag_cmul_sum sum.cartesian_product eq sum.union_disjoint disjoint_iff_not_equal
          sum.atLeast_Suc_atMost_Suc_shift del: sum.cl_ivl_Suc min.absorb2 min.absorb4
          flip: comm_monoid_add_class.sum.Sigma)
        apply (simp add: sum.Sigma eq2 [of _ "\<lambda>i. {_ i.._ i}"]
          del: min.absorb2 min.absorb4)
        apply (simp add: sum.union_disjoint disjoint_iff_not_equal * [OF 1 2])
        done
    next
      case (diff a b)
      then show ?case
        by (simp add: chain_boundary_diff frag_extend_diff chain_map_diff)
    qed auto
  qed
  have *: "singular_chain p (subtopology U V) (prism (p - Suc 0) (chain_boundary p c))"
    if "singular_chain p S c" "singular_chain (p - Suc 0) (subtopology S T) (chain_boundary p c)"
  proof (cases "p")
    case 0 then show ?thesis by (simp add: chain_boundary_def prism)
  next
    case (Suc p')
    with prism that show ?thesis by auto
  qed
  then show ?thesis
    using c
    unfolding singular_relcycle_def homologous_rel_def singular_relboundary_def mod_subset_def
    apply (rule_tac x="- prism p c" in exI)
    by (simp add: chain_boundary_minus prism(2) prism(4) singular_chain_minus)
qed

end

