(*  Title:      HOL/Vector_Spaces.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Author:     Johannes Hölzl, VU Amsterdam
    Author:     Fabian Immler, TUM
*)

section \<open>Vector Spaces\<close>

theory Vector_Spaces
  imports Modules
begin

lemma isomorphism_expand:
  "f \<circ> g = id \<and> g \<circ> f = id \<longleftrightarrow> (\<forall>x. f (g x) = x) \<and> (\<forall>x. g (f x) = x)"
  by (simp add: fun_eq_iff o_def id_def)

lemma left_right_inverse_eq:
  assumes fg: "f \<circ> g = id"
    and gh: "g \<circ> h = id"
  shows "f = h"
proof -
  have "f = f \<circ> (g \<circ> h)"
    unfolding gh by simp
  also have "\<dots> = (f \<circ> g) \<circ> h"
    by (simp add: o_assoc)
  finally show "f = h"
    unfolding fg by simp
qed

lemma ordLeq3_finite_infinite:
  assumes A: "finite A" and B: "infinite B" shows "ordLeq3 (card_of A) (card_of B)"
proof -
  have \<open>ordLeq3 (card_of A) (card_of B) \<or> ordLeq3 (card_of B) (card_of A)\<close>
    by (intro ordLeq_total card_of_Well_order)
  moreover have "\<not> ordLeq3 (card_of B) (card_of A)"
    using B A card_of_ordLeq_finite[of B A] by auto
  ultimately show ?thesis by auto
qed

locale vector_space =
  fixes scale :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr "*s" 75)
  assumes vector_space_assms:\<comment> \<open>re-stating the assumptions of \<open>module\<close> instead of extending \<open>module\<close>
   allows us to rewrite in the sublocale.\<close>
    "a *s (x + y) = a *s x + a *s y"
    "(a + b) *s x = a *s x + b *s x"
    "a *s (b *s x) = (a * b) *s x"
    "1 *s x = x"

lemma module_iff_vector_space: "module s \<longleftrightarrow> vector_space s"
  unfolding module_def vector_space_def ..

locale linear = vs1: vector_space s1 + vs2: vector_space s2 + module_hom s1 s2 f
  for s1 :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr "*a" 75)
  and s2 :: "'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c" (infixr "*b" 75)
  and f :: "'b \<Rightarrow> 'c"

lemma module_hom_iff_linear: "module_hom s1 s2 f \<longleftrightarrow> linear s1 s2 f"
  unfolding module_hom_def linear_def module_iff_vector_space by auto
lemmas module_hom_eq_linear = module_hom_iff_linear[abs_def, THEN meta_eq_to_obj_eq]
lemmas linear_iff_module_hom = module_hom_iff_linear[symmetric]
lemmas linear_module_homI = module_hom_iff_linear[THEN iffD1]
  and module_hom_linearI = module_hom_iff_linear[THEN iffD2]

context vector_space begin

sublocale module scale rewrites "module_hom = linear"
  by unfold_locales (fact vector_space_assms module_hom_eq_linear)+

lemmas\<comment> \<open>from \<open>module\<close>\<close>
      linear_id = module_hom_id
  and linear_ident = module_hom_ident
  and linear_scale_self = module_hom_scale_self
  and linear_scale_left = module_hom_scale_left
  and linear_uminus = module_hom_uminus

lemma linear_imp_scale:
  fixes D::"'a \<Rightarrow> 'b"
  assumes "linear (*) scale D"
  obtains d where "D = (\<lambda>x. scale x d)"
proof -
  interpret linear "(*)" scale D by fact
  show ?thesis
    by (metis mult.commute mult.left_neutral scale that)
qed

lemma scale_eq_0_iff [simp]: "scale a x = 0 \<longleftrightarrow> a = 0 \<or> x = 0"
  by (metis scale_left_commute right_inverse scale_one scale_scale scale_zero_left)

lemma scale_left_imp_eq:
  assumes nonzero: "a \<noteq> 0"
    and scale: "scale a x = scale a y"
  shows "x = y"
proof -
  from scale have "scale a (x - y) = 0"
     by (simp add: scale_right_diff_distrib)
  with nonzero have "x - y = 0" by simp
  then show "x = y" by (simp only: right_minus_eq)
qed

lemma scale_right_imp_eq:
  assumes nonzero: "x \<noteq> 0"
    and scale: "scale a x = scale b x"
  shows "a = b"
proof -
  from scale have "scale (a - b) x = 0"
     by (simp add: scale_left_diff_distrib)
  with nonzero have "a - b = 0" by simp
  then show "a = b" by (simp only: right_minus_eq)
qed

lemma scale_cancel_left [simp]: "scale a x = scale a y \<longleftrightarrow> x = y \<or> a = 0"
  by (auto intro: scale_left_imp_eq)

lemma scale_cancel_right [simp]: "scale a x = scale b x \<longleftrightarrow> a = b \<or> x = 0"
  by (auto intro: scale_right_imp_eq)

lemma injective_scale: "c \<noteq> 0 \<Longrightarrow> inj (\<lambda>x. scale c x)"
  by (simp add: inj_on_def)

lemma dependent_def: "dependent P \<longleftrightarrow> (\<exists>a \<in> P. a \<in> span (P - {a}))"
  unfolding dependent_explicit
proof safe
  fix a assume aP: "a \<in> P" and "a \<in> span (P - {a})"
  then obtain a S u
    where aP: "a \<in> P" and fS: "finite S" and SP: "S \<subseteq> P" "a \<notin> S" and ua: "(\<Sum>v\<in>S. u v *s v) = a"
    unfolding span_explicit by blast
  let ?S = "insert a S"
  let ?u = "\<lambda>y. if y = a then - 1 else u y"
  from fS SP have "(\<Sum>v\<in>?S. ?u v *s v) = 0"
    by (simp add: if_distrib[of "\<lambda>r. r *s a" for a] sum.If_cases field_simps Diff_eq[symmetric] ua)
  moreover have "finite ?S" "?S \<subseteq> P" "a \<in> ?S" "?u a \<noteq> 0"
    using fS SP aP by auto
  ultimately show "\<exists>t u. finite t \<and> t \<subseteq> P \<and> (\<Sum>v\<in>t. u v *s v) = 0 \<and> (\<exists>v\<in>t. u v \<noteq> 0)" by fast
next
  fix S u v
  assume fS: "finite S" and SP: "S \<subseteq> P" and vS: "v \<in> S"
   and uv: "u v \<noteq> 0" and u: "(\<Sum>v\<in>S. u v *s v) = 0"
  let ?a = v
  let ?S = "S - {v}"
  let ?u = "\<lambda>i. (- u i) / u v"
  have th0: "?a \<in> P" "finite ?S" "?S \<subseteq> P"
    using fS SP vS by auto
  have "(\<Sum>v\<in>?S. ?u v *s v) = (\<Sum>v\<in>S. (- (inverse (u ?a))) *s (u v *s v)) - ?u v *s v"
    using fS vS uv by (simp add: sum_diff1 field_simps)
  also have "\<dots> = ?a"
    unfolding scale_sum_right[symmetric] u using uv by simp
  finally have "(\<Sum>v\<in>?S. ?u v *s v) = ?a" .
  with th0 show "\<exists>a \<in> P. a \<in> span (P - {a})"
    unfolding span_explicit by (auto intro!: bexI[where x="?a"] exI[where x="?S"] exI[where x="?u"])
qed

lemma dependent_single[simp]: "dependent {x} \<longleftrightarrow> x = 0"
  unfolding dependent_def by auto

lemma in_span_insert:
  assumes a: "a \<in> span (insert b S)"
    and na: "a \<notin> span S"
  shows "b \<in> span (insert a S)"
proof -
  from span_breakdown[of b "insert b S" a, OF insertI1 a]
  obtain k where k: "a - k *s b \<in> span (S - {b})" by auto
  have "k \<noteq> 0"
  proof
    assume "k = 0"
    with k span_mono[of "S - {b}" S] have "a \<in> span S" by auto
    with na show False by blast  
  qed
  then have eq: "b = (1/k) *s a - (1/k) *s (a - k *s b)"
    by (simp add: algebra_simps)

  from k have "(1/k) *s (a - k *s b) \<in> span (S - {b})"
    by (rule span_scale)
  also have "... \<subseteq> span (insert a S)"
    by (rule span_mono) auto
  finally show ?thesis
    using k by (subst eq) (blast intro: span_diff span_scale span_base)
qed

lemma dependent_insertD: assumes a: "a \<notin> span S" and S: "dependent (insert a S)" shows "dependent S"
proof -
  have "a \<notin> S" using a by (auto dest: span_base)
  obtain b where b: "b = a \<or> b \<in> S" "b \<in> span (insert a S - {b})"
    using S unfolding dependent_def by blast
  have "b \<noteq> a" "b \<in> S"
    using b \<open>a \<notin> S\<close> a by auto
  with b have *: "b \<in> span (insert a (S - {b}))"
    by (auto simp: insert_Diff_if)
  show "dependent S"
  proof cases
    assume "b \<in> span (S - {b})" with \<open>b \<in> S\<close> show ?thesis
      by (auto simp add: dependent_def)
  next
    assume "b \<notin> span (S - {b})"
    with * have "a \<in> span (insert b (S - {b}))" by (rule in_span_insert)
    with a show ?thesis
      using \<open>b \<in> S\<close> by (auto simp: insert_absorb)
  qed
qed

lemma independent_insertI: "a \<notin> span S \<Longrightarrow> independent S \<Longrightarrow> independent (insert a S)"
  by (auto dest: dependent_insertD)

lemma independent_insert:
  "independent (insert a S) \<longleftrightarrow> (if a \<in> S then independent S else independent S \<and> a \<notin> span S)"
proof -
  have "a \<notin> S \<Longrightarrow> a \<in> span S \<Longrightarrow> dependent (insert a S)"
    by (auto simp: dependent_def)
  then show ?thesis
    by (auto intro: dependent_mono simp: independent_insertI)
qed

lemma maximal_independent_subset_extend:
  assumes "S \<subseteq> V" "independent S"
  obtains B where "S \<subseteq> B" "B \<subseteq> V" "independent B" "V \<subseteq> span B"
proof -
  let ?C = "{B. S \<subseteq> B \<and> independent B \<and> B \<subseteq> V}"
  have "\<exists>M\<in>?C. \<forall>X\<in>?C. M \<subseteq> X \<longrightarrow> X = M"
  proof (rule subset_Zorn)
    fix C :: "'b set set" assume "subset.chain ?C C"
    then have C: "\<And>c. c \<in> C \<Longrightarrow> c \<subseteq> V" "\<And>c. c \<in> C \<Longrightarrow> S \<subseteq> c" "\<And>c. c \<in> C \<Longrightarrow> independent c"
      "\<And>c d. c \<in> C \<Longrightarrow> d \<in> C \<Longrightarrow> c \<subseteq> d \<or> d \<subseteq> c"
      unfolding subset.chain_def by blast+

    show "\<exists>U\<in>?C. \<forall>X\<in>C. X \<subseteq> U"
    proof cases
      assume "C = {}" with assms show ?thesis
        by (auto intro!: exI[of _ S])
    next
      assume "C \<noteq> {}"
      with C(2) have "S \<subseteq> \<Union>C"
        by auto
      moreover have "independent (\<Union>C)"
        by (intro independent_Union_directed C)
      moreover have "\<Union>C \<subseteq> V"
        using C by auto
      ultimately show ?thesis
        by auto
    qed
  qed
  then obtain B where B: "independent B" "B \<subseteq> V" "S \<subseteq> B"
    and max: "\<And>S. independent S \<Longrightarrow> S \<subseteq> V \<Longrightarrow> B \<subseteq> S \<Longrightarrow> S = B"
    by auto
  moreover
  { assume "\<not> V \<subseteq> span B"
    then obtain v where "v \<in> V" "v \<notin> span B"
      by auto
    with B have "independent (insert v B)" by (auto intro: dependent_insertD)
    from max[OF this] \<open>v \<in> V\<close> \<open>B \<subseteq> V\<close>
    have "v \<in> B"
      by auto
    with \<open>v \<notin> span B\<close> have False
      by (auto intro: span_base) }
  ultimately show ?thesis
    by (meson that)
qed

lemma maximal_independent_subset:
  obtains B where "B \<subseteq> V" "independent B" "V \<subseteq> span B"
  by (metis maximal_independent_subset_extend[of "{}"] empty_subsetI independent_empty)

text \<open>Extends a basis from B to a basis of the entire space.\<close>
definition extend_basis :: "'b set \<Rightarrow> 'b set"
  where "extend_basis B = (SOME B'. B \<subseteq> B' \<and> independent B' \<and> span B' = UNIV)"

lemma
  assumes B: "independent B"
  shows extend_basis_superset: "B \<subseteq> extend_basis B"
    and independent_extend_basis: "independent (extend_basis B)"
    and span_extend_basis[simp]: "span (extend_basis B) = UNIV"
proof -
  define p where "p B' \<equiv> B \<subseteq> B' \<and> independent B' \<and> span B' = UNIV" for B'
  obtain B' where "p B'"
    using maximal_independent_subset_extend[OF subset_UNIV B]
    by (metis top.extremum_uniqueI p_def)
  then have "p (extend_basis B)"
    unfolding extend_basis_def p_def[symmetric] by (rule someI)
  then show "B \<subseteq> extend_basis B" "independent (extend_basis B)" "span (extend_basis B) = UNIV"
    by (auto simp: p_def)
qed

lemma in_span_delete:
  assumes a: "a \<in> span S" and na: "a \<notin> span (S - {b})"
  shows "b \<in> span (insert a (S - {b}))"
  by (metis Diff_empty Diff_insert0 a in_span_insert insert_Diff na)

lemma span_redundant: "x \<in> span S \<Longrightarrow> span (insert x S) = span S"
  unfolding span_def by (rule hull_redundant)

lemma span_trans: "x \<in> span S \<Longrightarrow> y \<in> span (insert x S) \<Longrightarrow> y \<in> span S"
  by (simp only: span_redundant)

lemma span_insert_0[simp]: "span (insert 0 S) = span S"
  by (metis span_zero span_redundant)

lemma span_delete_0 [simp]: "span(S - {0}) = span S"
proof
  show "span (S - {0}) \<subseteq> span S"
    by (blast intro!: span_mono)
next
  have "span S \<subseteq> span(insert 0 (S - {0}))"
    by (blast intro!: span_mono)
  also have "... \<subseteq> span(S - {0})"
    using span_insert_0 by blast
  finally show "span S \<subseteq> span (S - {0})" .
qed

lemma span_image_scale:
  assumes "finite S" and nz: "\<And>x. x \<in> S \<Longrightarrow> c x \<noteq> 0"
    shows "span ((\<lambda>x. c x *s x) ` S) = span S"
using assms
proof (induction S arbitrary: c)
  case (empty c) show ?case by simp
next
  case (insert x F c)
  show ?case
  proof (intro set_eqI iffI)
    fix y
      assume "y \<in> span ((\<lambda>x. c x *s x) ` insert x F)"
      then show "y \<in> span (insert x F)"
        using insert by (force simp: span_breakdown_eq)
  next
    fix y
      assume "y \<in> span (insert x F)"
      then show "y \<in> span ((\<lambda>x. c x *s x) ` insert x F)"
        using insert
        apply (clarsimp simp: span_breakdown_eq)
        apply (rule_tac x="k / c x" in exI)
        by simp
  qed
qed

lemma exchange_lemma:
  assumes f: "finite T"
    and i: "independent S"
    and sp: "S \<subseteq> span T"
  shows "\<exists>t'. card t' = card T \<and> finite t' \<and> S \<subseteq> t' \<and> t' \<subseteq> S \<union> T \<and> S \<subseteq> span t'"
  using f i sp
proof (induct "card (T - S)" arbitrary: S T rule: less_induct)
  case less
  note ft = \<open>finite T\<close> and S = \<open>independent S\<close> and sp = \<open>S \<subseteq> span T\<close>
  let ?P = "\<lambda>t'. card t' = card T \<and> finite t' \<and> S \<subseteq> t' \<and> t' \<subseteq> S \<union> T \<and> S \<subseteq> span t'"
  show ?case
  proof (cases "S \<subseteq> T \<or> T \<subseteq> S")
    case True
    then show ?thesis
    proof
      assume "S \<subseteq> T" then show ?thesis
        by (metis ft Un_commute sp sup_ge1)
    next
      assume "T \<subseteq> S" then show ?thesis
        by (metis Un_absorb sp spanning_subset_independent[OF _ S sp] ft)
    qed
  next
    case False
    then have st: "\<not> S \<subseteq> T" "\<not> T \<subseteq> S"
      by auto
    from st(2) obtain b where b: "b \<in> T" "b \<notin> S"
      by blast
    from b have "T - {b} - S \<subset> T - S"
      by blast
    then have cardlt: "card (T - {b} - S) < card (T - S)"
      using ft by (auto intro: psubset_card_mono)
    from b ft have ct0: "card T \<noteq> 0"
      by auto
    show ?thesis
    proof (cases "S \<subseteq> span (T - {b})")
      case True
      from ft have ftb: "finite (T - {b})"
        by auto
      from less(1)[OF cardlt ftb S True]
      obtain U where U: "card U = card (T - {b})" "S \<subseteq> U" "U \<subseteq> S \<union> (T - {b})" "S \<subseteq> span U"
        and fu: "finite U" by blast
      let ?w = "insert b U"
      have th0: "S \<subseteq> insert b U"
        using U by blast
      have th1: "insert b U \<subseteq> S \<union> T"
        using U b by blast
      have bu: "b \<notin> U"
        using b U by blast
      from U(1) ft b have "card U = (card T - 1)"
        by auto
      then have th2: "card (insert b U) = card T"
        using card_insert_disjoint[OF fu bu] ct0 by auto
      from U(4) have "S \<subseteq> span U" .
      also have "\<dots> \<subseteq> span (insert b U)"
        by (rule span_mono) blast
      finally have th3: "S \<subseteq> span (insert b U)" .
      from th0 th1 th2 th3 fu have th: "?P ?w"
        by blast
      from th show ?thesis by blast
    next
      case False
      then obtain a where a: "a \<in> S" "a \<notin> span (T - {b})"
        by blast
      have ab: "a \<noteq> b"
        using a b by blast
      have at: "a \<notin> T"
        using a ab span_base[of a "T- {b}"] by auto
      have mlt: "card ((insert a (T - {b})) - S) < card (T - S)"
        using cardlt ft a b by auto
      have ft': "finite (insert a (T - {b}))"
        using ft by auto
      have sp': "S \<subseteq> span (insert a (T - {b}))"
      proof
        fix x
        assume xs: "x \<in> S"
        have T: "T \<subseteq> insert b (insert a (T - {b}))"
          using b by auto
        have bs: "b \<in> span (insert a (T - {b}))"
          by (rule in_span_delete) (use a sp in auto)
        from xs sp have "x \<in> span T"
          by blast
        with span_mono[OF T] have x: "x \<in> span (insert b (insert a (T - {b})))" ..
        from span_trans[OF bs x] show "x \<in> span (insert a (T - {b}))" .
      qed
      from less(1)[OF mlt ft' S sp'] obtain U where U:
        "card U = card (insert a (T - {b}))"
        "finite U" "S \<subseteq> U" "U \<subseteq> S \<union> insert a (T - {b})"
        "S \<subseteq> span U" by blast
      from U a b ft at ct0 have "?P U"
        by auto
      then show ?thesis by blast
    qed
  qed
qed

lemma independent_span_bound:
  assumes f: "finite T"
    and i: "independent S"
    and sp: "S \<subseteq> span T"
  shows "finite S \<and> card S \<le> card T"
  by (metis exchange_lemma[OF f i sp] finite_subset card_mono)

lemma independent_explicit_finite_subsets:
  "independent A \<longleftrightarrow> (\<forall>S \<subseteq> A. finite S \<longrightarrow> (\<forall>u. (\<Sum>v\<in>S. u v *s v) = 0 \<longrightarrow> (\<forall>v\<in>S. u v = 0)))"
  unfolding dependent_explicit [of A] by (simp add: disj_not2)

lemma independent_if_scalars_zero:
  assumes fin_A: "finite A"
  and sum: "\<And>f x. (\<Sum>x\<in>A. f x *s x) = 0 \<Longrightarrow> x \<in> A \<Longrightarrow> f x = 0"
  shows "independent A"
proof (unfold independent_explicit_finite_subsets, clarify)
  fix S v and u :: "'b \<Rightarrow> 'a"
  assume S: "S \<subseteq> A" and v: "v \<in> S"
  let ?g = "\<lambda>x. if x \<in> S then u x else 0"
  have "(\<Sum>v\<in>A. ?g v *s v) = (\<Sum>v\<in>S. u v *s v)"
    using S fin_A by (auto intro!: sum.mono_neutral_cong_right)
  also assume "(\<Sum>v\<in>S. u v *s v) = 0"
  finally have "?g v = 0" using v S sum by force
  thus "u v = 0"  unfolding if_P[OF v] .
qed

lemma bij_if_span_eq_span_bases:
  assumes B: "independent B" and C: "independent C"
    and eq: "span B = span C"
  shows "\<exists>f. bij_betw f B C"
proof cases
  assume "finite B \<or> finite C"
  then have "finite B \<and> finite C \<and> card C = card B"
    using independent_span_bound[of B C] independent_span_bound[of C B] assms
      span_superset[of B] span_superset[of C]
    by auto
  then show ?thesis
    by (auto intro!: finite_same_card_bij)
next
  assume "\<not> (finite B \<or> finite C)"
  then have "infinite B" "infinite C" by auto
  { fix B C assume  B: "independent B" and C: "independent C" and "infinite B" "infinite C" and eq: "span B = span C"
    let ?R = "representation B" and ?R' = "representation C" let ?U = "\<lambda>c. {v. ?R c v \<noteq> 0}"
    have in_span_C [simp, intro]: \<open>b \<in> B \<Longrightarrow> b \<in> span C\<close> for b unfolding eq[symmetric] by (rule span_base) 
    have in_span_B [simp, intro]: \<open>c \<in> C \<Longrightarrow> c \<in> span B\<close> for c unfolding eq by (rule span_base) 
    have \<open>B \<subseteq> (\<Union>c\<in>C. ?U c)\<close>
    proof
      fix b assume \<open>b \<in> B\<close>
      have \<open>b \<in> span C\<close>
        using \<open>b \<in> B\<close> unfolding eq[symmetric] by (rule span_base)
      have \<open>(\<Sum>v | ?R' b v \<noteq> 0. \<Sum>w | ?R v w \<noteq> 0. (?R' b v * ?R v w) *s w) =
           (\<Sum>v | ?R' b v \<noteq> 0. ?R' b v *s (\<Sum>w | ?R v w \<noteq> 0. ?R v w *s w))\<close>
        by (simp add: scale_sum_right)
      also have \<open>\<dots> = (\<Sum>v | ?R' b v \<noteq> 0. ?R' b v *s v)\<close>
        by (auto simp: sum_nonzero_representation_eq B eq span_base representation_ne_zero)
      also have \<open>\<dots> = b\<close>
        by (rule sum_nonzero_representation_eq[OF C \<open>b \<in> span C\<close>])
      finally have "?R b b = ?R (\<Sum>v | ?R' b v \<noteq> 0. \<Sum>w | ?R v w \<noteq> 0. (?R' b v * ?R v w) *s w) b"
        by simp
      also have "... = (\<Sum>i\<in>{v. ?R' b v \<noteq> 0}. ?R (\<Sum>w | ?R i w \<noteq> 0. (?R' b i * ?R i w) *s w) b)"
        by (subst representation_sum[OF B])  (auto intro: span_sum span_scale span_base representation_ne_zero)
      also have "... = (\<Sum>i\<in>{v. ?R' b v \<noteq> 0}.
           \<Sum>j \<in> {w. ?R i w \<noteq> 0}. ?R ((?R' b i * ?R i j ) *s  j ) b)"
        by (subst representation_sum[OF B]) (auto simp add: span_sum span_scale span_base representation_ne_zero)
      also have \<open>\<dots> = (\<Sum>v | ?R' b v \<noteq> 0. \<Sum>w | ?R v w \<noteq> 0. ?R' b v * ?R v w * ?R w b)\<close>
        using B \<open>b \<in> B\<close> by (simp add: representation_scale[OF B] span_base representation_ne_zero)
      finally have "(\<Sum>v | ?R' b v \<noteq> 0. \<Sum>w | ?R v w \<noteq> 0. ?R' b v * ?R v w * ?R w b) \<noteq> 0"
        using representation_basis[OF B \<open>b \<in> B\<close>] by auto
      then obtain v w where bv: "?R' b v \<noteq> 0" and vw: "?R v w \<noteq> 0" and "?R' b v * ?R v w * ?R w b \<noteq> 0"
        by (blast elim: sum.not_neutral_contains_not_neutral)
      with representation_basis[OF B, of w] vw[THEN representation_ne_zero]
      have \<open>?R' b v \<noteq> 0\<close> \<open>?R v b \<noteq> 0\<close> by (auto split: if_splits)
      then show \<open>b \<in> (\<Union>c\<in>C. ?U c)\<close>
        by (auto dest: representation_ne_zero)
    qed
    then have B_eq: \<open>B = (\<Union>c\<in>C. ?U c)\<close>
      by (auto intro: span_base representation_ne_zero eq)
    have "ordLeq3 (card_of B) (card_of C)"
    proof (subst B_eq, rule card_of_UNION_ordLeq_infinite[OF \<open>infinite C\<close>])
      show "ordLeq3 (card_of C) (card_of C)"
        by (intro ordLeq_refl card_of_Card_order)
      show "\<forall>c\<in>C. ordLeq3 (card_of {v. ?R c v \<noteq> 0}) (card_of C)"
        by (intro ballI ordLeq3_finite_infinite \<open>infinite C\<close> finite_representation)
    qed }
  from this[of B C] this[of C B] B C eq \<open>infinite C\<close> \<open>infinite B\<close>
  show ?thesis by (auto simp add: ordIso_iff_ordLeq card_of_ordIso)
qed

definition dim :: "'b set \<Rightarrow> nat"
  where "dim V = (if \<exists>b. independent b \<and> span b = span V then
    card (SOME b. independent b \<and> span b = span V) else 0)"

lemma dim_eq_card:
  assumes BV: "span B = span V" and B: "independent B"
  shows "dim V = card B"
proof -
  define p where "p b \<equiv> independent b \<and> span b = span V" for b
  have "p (SOME B. p B)"
    using assms by (intro someI[of p B]) (auto simp: p_def)
  then have "\<exists>f. bij_betw f B (SOME B. p B)"
    by (subst (asm) p_def, intro bij_if_span_eq_span_bases[OF B]) (simp_all add: BV)
  then have "card B = card (SOME B. p B)"
    by (auto intro: bij_betw_same_card)
  then show ?thesis
    using BV B
    by (auto simp add: dim_def p_def)
qed

lemma basis_card_eq_dim: "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> card B = dim V"
  using dim_eq_card[of B V] span_mono[of B V] span_minimal[OF _ subspace_span, of V B] by auto

lemma basis_exists:
  obtains B where "B \<subseteq> V" "independent B" "V \<subseteq> span B" "card B = dim V"
  by (meson basis_card_eq_dim empty_subsetI independent_empty maximal_independent_subset_extend)

lemma dim_eq_card_independent: "independent B \<Longrightarrow> dim B = card B"
  by (rule dim_eq_card[OF refl])

lemma dim_span[simp]: "dim (span S) = dim S"
  by (auto simp add: dim_def span_span)

lemma dim_span_eq_card_independent: "independent B \<Longrightarrow> dim (span B) = card B"
  by (simp add: dim_eq_card)

lemma dim_le_card: assumes "V \<subseteq> span W" "finite W" shows "dim V \<le> card W"
proof -
  obtain A where "independent A" "A \<subseteq> V" "V \<subseteq> span A"
    using maximal_independent_subset[of V] by force
  with assms independent_span_bound[of W A] basis_card_eq_dim[of A V]
  show ?thesis by auto
qed

lemma span_eq_dim: "span S = span T \<Longrightarrow> dim S = dim T"
  by (metis dim_span)

corollary dim_le_card':
  "finite s \<Longrightarrow> dim s \<le> card s"
  by (metis basis_exists card_mono)

lemma span_card_ge_dim:
  "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> finite B \<Longrightarrow> dim V \<le> card B"
  by (simp add: dim_le_card)

lemma dim_unique:
  "B \<subseteq> V \<Longrightarrow> V \<subseteq> span B \<Longrightarrow> independent B \<Longrightarrow> card B = n \<Longrightarrow> dim V = n"
  by (metis basis_card_eq_dim)

lemma subspace_sums: "\<lbrakk>subspace S; subspace T\<rbrakk> \<Longrightarrow> subspace {x + y|x y. x \<in> S \<and> y \<in> T}"
  apply (simp add: subspace_def)
  apply (intro conjI impI allI; clarsimp simp: algebra_simps)
  using add.left_neutral apply blast
   apply (metis add.assoc)
  using scale_right_distrib by blast

end

lemma linear_iff: "linear s1 s2 f \<longleftrightarrow>
  (vector_space s1 \<and> vector_space s2 \<and> (\<forall>x y. f (x + y) = f x + f y) \<and> (\<forall>c x. f (s1 c x) = s2 c (f x)))"
  unfolding linear_def module_hom_iff vector_space_def module_def by auto

context begin
qualified lemma linear_compose: "linear s1 s2 f \<Longrightarrow> linear s2 s3 g \<Longrightarrow> linear s1 s3 (g o f)"
  unfolding module_hom_iff_linear[symmetric]
  by (rule module_hom_compose)
end

locale vector_space_pair = vs1: vector_space s1 + vs2: vector_space s2
  for s1 :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr "*a" 75)
  and s2 :: "'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c" (infixr "*b" 75)
begin

context fixes f assumes "linear s1 s2 f" begin
interpretation linear s1 s2 f by fact
lemmas\<comment> \<open>from locale \<open>module_hom\<close>\<close>
      linear_0 = zero
  and linear_add = add
  and linear_scale = scale
  and linear_neg = neg
  and linear_diff = diff
  and linear_sum = sum
  and linear_inj_on_iff_eq_0 = inj_on_iff_eq_0
  and linear_inj_iff_eq_0 = inj_iff_eq_0
  and linear_subspace_image = subspace_image
  and linear_subspace_vimage = subspace_vimage
  and linear_subspace_kernel = subspace_kernel
  and linear_span_image = span_image
  and linear_dependent_inj_imageD = dependent_inj_imageD
  and linear_eq_0_on_span = eq_0_on_span
  and linear_independent_injective_image = independent_injective_image
  and linear_inj_on_span_independent_image = inj_on_span_independent_image
  and linear_inj_on_span_iff_independent_image = inj_on_span_iff_independent_image
  and linear_subspace_linear_preimage = subspace_linear_preimage
  and linear_spans_image = spans_image
  and linear_spanning_surjective_image = spanning_surjective_image
end

sublocale module_pair
  rewrites "module_hom = linear"
  by unfold_locales (fact module_hom_eq_linear)

lemmas\<comment> \<open>from locale \<open>module_pair\<close>\<close>
      linear_eq_on_span = module_hom_eq_on_span
  and linear_compose_scale_right = module_hom_scale
  and linear_compose_add = module_hom_add
  and linear_zero = module_hom_zero
  and linear_compose_sub = module_hom_sub
  and linear_compose_neg = module_hom_neg
  and linear_compose_scale = module_hom_compose_scale

lemma linear_indep_image_lemma:
  assumes lf: "linear s1 s2 f"
    and fB: "finite B"
    and ifB: "vs2.independent (f ` B)"
    and fi: "inj_on f B"
    and xsB: "x \<in> vs1.span B"
    and fx: "f x = 0"
  shows "x = 0"
  using fB ifB fi xsB fx
proof (induction B arbitrary: x rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert a b x)
  have th0: "f ` b \<subseteq> f ` (insert a b)"
    by (simp add: subset_insertI)
  have ifb: "vs2.independent (f ` b)"
    using vs2.independent_mono insert.prems(1) th0 by blast
  have fib: "inj_on f b"
    using insert.prems(2) by blast
  from vs1.span_breakdown[of a "insert a b", simplified, OF insert.prems(3)]
  obtain k where k: "x - k *a a \<in> vs1.span (b - {a})"
    by blast
  have "f (x - k *a a) \<in> vs2.span (f ` b)"
    unfolding linear_span_image[OF lf]
    using "insert.hyps"(2) k by auto
  then have "f x - k *b f a \<in> vs2.span (f ` b)"
    by (simp add: linear_diff linear_scale lf)
  then have th: "-k *b f a \<in> vs2.span (f ` b)"
    using insert.prems(4) by simp
  have xsb: "x \<in> vs1.span b"
  proof (cases "k = 0")
    case True
    with k have "x \<in> vs1.span (b - {a})" by simp
    then show ?thesis using vs1.span_mono[of "b - {a}" b]
      by blast
  next
    case False
    from inj_on_image_set_diff[OF insert.prems(2), of "insert a b " "{a}", symmetric]
    have "f ` insert a b - f ` {a} = f ` (insert a b - {a})" by blast
    then have "f a \<notin> vs2.span (f ` b)" 
      using vs2.dependent_def insert.hyps(2) insert.prems(1) by fastforce
    moreover have "f a \<in> vs2.span (f ` b)"
      using False vs2.span_scale[OF th, of "- 1/ k"] by auto
    ultimately have False
      by blast
    then show ?thesis by blast
  qed
  show "x = 0"
    using ifb fib xsb insert.IH insert.prems(4) by blast
qed

lemma linear_eq_on:
  assumes l: "linear s1 s2 f" "linear s1 s2 g"
  assumes x: "x \<in> vs1.span B" and eq: "\<And>b. b \<in> B \<Longrightarrow> f b = g b"
  shows "f x = g x"
proof -
  interpret d: linear s1 s2 "\<lambda>x. f x - g x"
    using l by (intro linear_compose_sub) (auto simp: module_hom_iff_linear)
  have "f x - g x = 0"
    by (rule d.eq_0_on_span[OF _ x]) (auto simp: eq)
  then show ?thesis by auto
qed

definition construct :: "'b set \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c)"
  where "construct B g v = (\<Sum>b | vs1.representation (vs1.extend_basis B) v b \<noteq> 0.
      vs1.representation (vs1.extend_basis B) v b *b (if b \<in> B then g b else 0))"

lemma construct_cong: "(\<And>b. b \<in> B \<Longrightarrow> f b = g b) \<Longrightarrow> construct B f = construct B g"
  unfolding construct_def by (rule ext, auto intro!: sum.cong)

lemma linear_construct:
  assumes B[simp]: "vs1.independent B"
  shows "linear s1 s2 (construct B f)"
  unfolding module_hom_iff_linear linear_iff
proof safe
  have eB[simp]: "vs1.independent (vs1.extend_basis B)"
    using vs1.independent_extend_basis[OF B] .
  let ?R = "vs1.representation (vs1.extend_basis B)"
  fix c x y
  have "construct B f (x + y) =
    (\<Sum>b\<in>{b. ?R x b \<noteq> 0} \<union> {b. ?R y b \<noteq> 0}. ?R (x + y) b *b (if b \<in> B then f b else 0))"
    by (auto intro!: sum.mono_neutral_cong_left simp: vs1.finite_representation vs1.representation_add construct_def)
  also have "\<dots> = construct B f x + construct B f y"
    by (auto simp: construct_def vs1.representation_add vs2.scale_left_distrib sum.distrib
      intro!: arg_cong2[where f="(+)"] sum.mono_neutral_cong_right vs1.finite_representation)
  finally show "construct B f (x + y) = construct B f x + construct B f y" .

  show "construct B f (c *a x) = c *b construct B f x"
    by (auto simp del: vs2.scale_scale intro!: sum.mono_neutral_cong_left vs1.finite_representation
      simp add: construct_def vs2.scale_scale[symmetric] vs1.representation_scale vs2.scale_sum_right)
qed intro_locales

lemma construct_basis:
  assumes B[simp]: "vs1.independent B" and b: "b \<in> B"
  shows "construct B f b = f b"
proof -
  have *: "vs1.representation (vs1.extend_basis B) b = (\<lambda>v. if v = b then 1 else 0)"
    using vs1.extend_basis_superset[OF B] b
    by (intro vs1.representation_basis vs1.independent_extend_basis) auto
  then have "{v. vs1.representation (vs1.extend_basis B) b v \<noteq> 0} = {b}"
    by auto
  then show ?thesis
    unfolding construct_def by (simp add: * b)
qed

lemma construct_outside:
  assumes B: "vs1.independent B" and v: "v \<in> vs1.span (vs1.extend_basis B - B)"
  shows "construct B f v = 0"
  unfolding construct_def
proof (clarsimp intro!: sum.neutral simp del: vs2.scale_eq_0_iff)
  fix b assume "b \<in> B"
  then have "vs1.representation (vs1.extend_basis B - B) v b = 0"
    using vs1.representation_ne_zero[of "vs1.extend_basis B - B" v b] by auto
  moreover have "vs1.representation (vs1.extend_basis B) v = vs1.representation (vs1.extend_basis B - B) v"
    using vs1.representation_extend[OF vs1.independent_extend_basis[OF B] v] by auto
  ultimately show "vs1.representation (vs1.extend_basis B) v b *b f b = 0"
    by simp
qed

lemma construct_add:
  assumes B[simp]: "vs1.independent B"
  shows "construct B (\<lambda>x. f x + g x) v = construct B f v + construct B g v"
proof (rule linear_eq_on)
  show "v \<in> vs1.span (vs1.extend_basis B)" by simp
  show "b \<in> vs1.extend_basis B \<Longrightarrow> construct B (\<lambda>x. f x + g x) b = construct B f b + construct B g b" for b
    using construct_outside[OF B vs1.span_base, of b] by (cases "b \<in> B") (auto simp: construct_basis)
qed (intro linear_compose_add linear_construct B)+

lemma construct_scale:
  assumes B[simp]: "vs1.independent B"
  shows "construct B (\<lambda>x. c *b f x) v = c *b construct B f v"
proof (rule linear_eq_on)
  show "v \<in> vs1.span (vs1.extend_basis B)" by simp
  show "b \<in> vs1.extend_basis B \<Longrightarrow> construct B (\<lambda>x. c *b f x) b = c *b construct B f b" for b
    using construct_outside[OF B vs1.span_base, of b] by (cases "b \<in> B") (auto simp: construct_basis)
qed (intro linear_construct module_hom_scale B)+

lemma construct_in_span:
  assumes B[simp]: "vs1.independent B"
  shows "construct B f v \<in> vs2.span (f ` B)"
proof -
  interpret c: linear s1 s2 "construct B f" by (rule linear_construct) fact
  let ?R = "vs1.representation B"
  have "v \<in> vs1.span ((vs1.extend_basis B - B) \<union> B)"
    by (auto simp: Un_absorb2 vs1.extend_basis_superset)
  then obtain x y where "v = x + y" "x \<in> vs1.span (vs1.extend_basis B - B)" "y \<in> vs1.span B"
    unfolding vs1.span_Un by auto
  moreover have "construct B f (\<Sum>b | ?R y b \<noteq> 0. ?R y b *a b) \<in> vs2.span (f ` B)"
    by (auto simp add: c.sum c.scale construct_basis vs1.representation_ne_zero
      intro!: vs2.span_sum vs2.span_scale intro: vs2.span_base )
  ultimately show "construct B f v \<in> vs2.span (f ` B)"
    by (auto simp add: c.add construct_outside vs1.sum_nonzero_representation_eq)
qed

lemma linear_compose_sum:
  assumes lS: "\<forall>a \<in> S. linear s1 s2 (f a)"
  shows "linear s1 s2 (\<lambda>x. sum (\<lambda>a. f a x) S)"
proof (cases "finite S")
  case True
  then show ?thesis
    using lS by induct (simp_all add: linear_zero linear_compose_add)
next
  case False
  then show ?thesis
    by (simp add: linear_zero)
qed

lemma in_span_in_range_construct:
  "x \<in> range (construct B f)" if i: "vs1.independent B" and x: "x \<in> vs2.span (f ` B)"
proof -
  interpret linear "(*a)" "(*b)" "construct B f"
    using i by (rule linear_construct)
  obtain bb :: "('b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'b set \<Rightarrow> 'b" where
    "\<forall>x0 x1 x2. (\<exists>v4. v4 \<in> x2 \<and> x1 v4 \<noteq> x0 v4) = (bb x0 x1 x2 \<in> x2 \<and> x1 (bb x0 x1 x2) \<noteq> x0 (bb x0 x1 x2))"
    by moura
  then have f2: "\<forall>B Ba f fa. (B \<noteq> Ba \<or> bb fa f Ba \<in> Ba \<and> f (bb fa f Ba) \<noteq> fa (bb fa f Ba)) \<or> f ` B = fa ` Ba"
    by (meson image_cong)
  have "vs1.span B \<subseteq> vs1.span (vs1.extend_basis B)"
    by (simp add: vs1.extend_basis_superset[OF i] vs1.span_mono)
  then show "x \<in> range (construct B f)"
    using f2 x by (metis (no_types) construct_basis[OF i, of _ f]
        vs1.span_extend_basis[OF i] subsetD span_image spans_image)
qed

lemma range_construct_eq_span:
  "range (construct B f) = vs2.span (f ` B)"
  if "vs1.independent B"
  by (auto simp: that construct_in_span in_span_in_range_construct)

lemma linear_independent_extend_subspace:
  \<comment> \<open>legacy: use \<^term>\<open>construct\<close> instead\<close>
  assumes "vs1.independent B"
  shows "\<exists>g. linear s1 s2 g \<and> (\<forall>x\<in>B. g x = f x) \<and> range g = vs2.span (f`B)"
  by (rule exI[where x="construct B f"])
    (auto simp: linear_construct assms construct_basis range_construct_eq_span)

lemma linear_independent_extend:
  "vs1.independent B \<Longrightarrow> \<exists>g. linear s1 s2 g \<and> (\<forall>x\<in>B. g x = f x)"
  using linear_independent_extend_subspace[of B f] by auto

lemma linear_exists_left_inverse_on:
  assumes lf: "linear s1 s2 f"
  assumes V: "vs1.subspace V" and f: "inj_on f V"
  shows "\<exists>g. g ` UNIV \<subseteq> V \<and> linear s2 s1 g \<and> (\<forall>v\<in>V. g (f v) = v)"
proof -
  interpret linear s1 s2 f by fact
  obtain B where V_eq: "V = vs1.span B" and B: "vs1.independent B"
    using vs1.maximal_independent_subset[of V] vs1.span_minimal[OF _ \<open>vs1.subspace V\<close>]
    by (metis antisym_conv)
  have f: "inj_on f (vs1.span B)"
    using f unfolding V_eq .
  show ?thesis
  proof (intro exI ballI conjI)
    interpret p: vector_space_pair s2 s1 by unfold_locales
    have fB: "vs2.independent (f ` B)"
      using independent_injective_image[OF B f] .
    let ?g = "p.construct (f ` B) (the_inv_into B f)"
    show "linear (*b) (*a) ?g"
      by (rule p.linear_construct[OF fB])
    have "?g b \<in> vs1.span (the_inv_into B f ` f ` B)" for b
      by (intro p.construct_in_span fB)
    moreover have "the_inv_into B f ` f ` B = B"
      by (auto simp: image_comp comp_def the_inv_into_f_f inj_on_subset[OF f vs1.span_superset]
          cong: image_cong)
    ultimately show "?g ` UNIV \<subseteq> V"
      by (auto simp: V_eq)
    have "(?g \<circ> f) v = id v" if "v \<in> vs1.span B" for v
    proof (rule vector_space_pair.linear_eq_on[where x=v])
      show "vector_space_pair (*a) (*a)" by unfold_locales
      show "linear (*a) (*a) (?g \<circ> f)"
      proof (rule Vector_Spaces.linear_compose[of _ "(*b)"])
        show "linear (*a) (*b) f"
          by unfold_locales
      qed fact
      show "linear (*a) (*a) id" by (rule vs1.linear_id)
      show "v \<in> vs1.span B" by fact
      show "b \<in> B \<Longrightarrow> (p.construct (f ` B) (the_inv_into B f) \<circ> f) b = id b" for b
        by (simp add: p.construct_basis fB the_inv_into_f_f inj_on_subset[OF f vs1.span_superset])
    qed
    then show "v \<in> V \<Longrightarrow> ?g (f v) = v" for v by (auto simp: comp_def id_def V_eq)
  qed
qed

lemma linear_exists_right_inverse_on:
  assumes lf: "linear s1 s2 f"
  assumes "vs1.subspace V"
  shows "\<exists>g. g ` UNIV \<subseteq> V \<and> linear s2 s1 g \<and> (\<forall>v\<in>f ` V. f (g v) = v)"
proof -
  obtain B where V_eq: "V = vs1.span B" and B: "vs1.independent B"
    using vs1.maximal_independent_subset[of V] vs1.span_minimal[OF _ \<open>vs1.subspace V\<close>]
    by (metis antisym_conv)
  obtain C where C: "vs2.independent C" and fB_C: "f ` B \<subseteq> vs2.span C" "C \<subseteq> f ` B"
    using vs2.maximal_independent_subset[of "f ` B"] by metis
  then have "\<forall>v\<in>C. \<exists>b\<in>B. v = f b" by auto
  then obtain g where g: "\<And>v. v \<in> C \<Longrightarrow> g v \<in> B" "\<And>v. v \<in> C \<Longrightarrow> f (g v) = v" by metis
  show ?thesis
  proof (intro exI ballI conjI)
    interpret p: vector_space_pair s2 s1 by unfold_locales
    let ?g = "p.construct C g"
    show "linear (*b) (*a) ?g"
      by (rule p.linear_construct[OF C])
    have "?g v \<in> vs1.span (g ` C)" for v
      by (rule p.construct_in_span[OF C])
    also have "\<dots> \<subseteq> V" unfolding V_eq using g by (intro vs1.span_mono) auto
    finally show "?g ` UNIV \<subseteq> V" by auto
    have "(f \<circ> ?g) v = id v" if v: "v \<in> f ` V" for v
    proof (rule vector_space_pair.linear_eq_on[where x=v])
      show "vector_space_pair (*b) (*b)" by unfold_locales
      show "linear (*b) (*b) (f \<circ> ?g)"
        by (rule Vector_Spaces.linear_compose[of _ "(*a)"]) fact+
      show "linear (*b) (*b) id" by (rule vs2.linear_id)
      have "vs2.span (f ` B) = vs2.span C"
        using fB_C vs2.span_mono[of C "f ` B"] vs2.span_minimal[of "f`B" "vs2.span C"]
        by auto
      then show "v \<in> vs2.span C"
        using v linear_span_image[OF lf, of B] by (simp add: V_eq)
      show "(f \<circ> p.construct C g) b = id b" if b: "b \<in> C" for b
        by (auto simp: p.construct_basis g C b)
    qed
    then show "v \<in> f ` V \<Longrightarrow> f (?g v) = v" for v by (auto simp: comp_def id_def)
  qed
qed

lemma linear_inj_on_left_inverse:
  assumes lf: "linear s1 s2 f"
  assumes fi: "inj_on f (vs1.span S)"
  shows "\<exists>g. range g \<subseteq> vs1.span S \<and> linear s2 s1 g \<and> (\<forall>x\<in>vs1.span S. g (f x) = x)"
  using linear_exists_left_inverse_on[OF lf vs1.subspace_span fi]
  by (auto simp: linear_iff_module_hom)

lemma linear_injective_left_inverse: "linear s1 s2 f \<Longrightarrow> inj f \<Longrightarrow> \<exists>g. linear s2 s1 g \<and> g \<circ> f = id"
  using linear_inj_on_left_inverse[of f UNIV]
  by force

lemma linear_surj_right_inverse:
  assumes lf: "linear s1 s2 f"
  assumes sf: "vs2.span T \<subseteq> f`vs1.span S"
  shows "\<exists>g. range g \<subseteq> vs1.span S \<and> linear s2 s1 g \<and> (\<forall>x\<in>vs2.span T. f (g x) = x)"
  using linear_exists_right_inverse_on[OF lf vs1.subspace_span, of S] sf
  by (force simp: linear_iff_module_hom)

lemma linear_surjective_right_inverse: "linear s1 s2 f \<Longrightarrow> surj f \<Longrightarrow> \<exists>g. linear s2 s1 g \<and> f \<circ> g = id"
  using linear_surj_right_inverse[of f UNIV UNIV]
  by (auto simp: fun_eq_iff)

lemma finite_basis_to_basis_subspace_isomorphism:
  assumes s: "vs1.subspace S"
    and t: "vs2.subspace T"
    and d: "vs1.dim S = vs2.dim T"
    and fB: "finite B"
    and B: "B \<subseteq> S" "vs1.independent B" "S \<subseteq> vs1.span B" "card B = vs1.dim S"
    and fC: "finite C"
    and C: "C \<subseteq> T" "vs2.independent C" "T \<subseteq> vs2.span C" "card C = vs2.dim T"
  shows "\<exists>f. linear s1 s2 f \<and> f ` B = C \<and> f ` S = T \<and> inj_on f S"
proof -
  from B(4) C(4) card_le_inj[of B C] d obtain f where
    f: "f ` B \<subseteq> C" "inj_on f B" using \<open>finite B\<close> \<open>finite C\<close> by auto
  from linear_independent_extend[OF B(2)] obtain g where
    g: "linear s1 s2 g" "\<forall>x \<in> B. g x = f x" by blast
  interpret g: linear s1 s2 g by fact
  from inj_on_iff_eq_card[OF fB, of f] f(2)
  have "card (f ` B) = card B" by simp
  with B(4) C(4) have ceq: "card (f ` B) = card C" using d
    by simp
  have "g ` B = f ` B" using g(2)
    by (auto simp add: image_iff)
  also have "\<dots> = C" using card_subset_eq[OF fC f(1) ceq] .
  finally have gBC: "g ` B = C" .
  have gi: "inj_on g B" using f(2) g(2)
    by (auto simp add: inj_on_def)
  note g0 = linear_indep_image_lemma[OF g(1) fB, unfolded gBC, OF C(2) gi]
  {
    fix x y
    assume x: "x \<in> S" and y: "y \<in> S" and gxy: "g x = g y"
    from B(3) x y have x': "x \<in> vs1.span B" and y': "y \<in> vs1.span B"
      by blast+
    from gxy have th0: "g (x - y) = 0"
      by (simp add: g.diff)
    have th1: "x - y \<in> vs1.span B" using x' y'
      by (metis vs1.span_diff)
    have "x = y" using g0[OF th1 th0] by simp
  }
  then have giS: "inj_on g S" unfolding inj_on_def by blast
  from vs1.span_subspace[OF B(1,3) s]
  have "g ` S = vs2.span (g ` B)"
    by (simp add: g.span_image)
  also have "\<dots> = vs2.span C"
    unfolding gBC ..
  also have "\<dots> = T"
    using vs2.span_subspace[OF C(1,3) t] .
  finally have gS: "g ` S = T" .
  from g(1) gS giS gBC show ?thesis
    by blast
qed

end


locale finite_dimensional_vector_space = vector_space +
  fixes Basis :: "'b set"
  assumes finite_Basis: "finite Basis"
  and independent_Basis: "independent Basis"
  and span_Basis: "span Basis = UNIV"
begin

definition "dimension = card Basis"

lemma finiteI_independent: "independent B \<Longrightarrow> finite B"
  using independent_span_bound[OF finite_Basis, of B] by (auto simp: span_Basis)

lemma dim_empty [simp]: "dim {} = 0"
  by (rule dim_unique[OF order_refl]) (auto simp: dependent_def)

lemma dim_insert:
  "dim (insert x S) = (if x \<in> span S then dim S else dim S + 1)"
proof -
  show ?thesis
  proof (cases "x \<in> span S")
    case True then show ?thesis
      by (metis dim_span span_redundant)
  next
    case False
    obtain B where B: "B \<subseteq> span S" "independent B" "span S \<subseteq> span B" "card B = dim (span S)"
      using basis_exists [of "span S"] by blast
    have "dim (span (insert x S)) = Suc (dim S)"
    proof (rule dim_unique)
      show "insert x B \<subseteq> span (insert x S)"
        by (meson B(1) insertI1 insert_subset order_trans span_base span_mono subset_insertI)
      show "span (insert x S) \<subseteq> span (insert x B)"
        by (metis \<open>B \<subseteq> span S\<close> \<open>span S \<subseteq> span B\<close> span_breakdown_eq span_subspace subsetI subspace_span)
      show "independent (insert x B)"
        by (metis B(1-3) independent_insert span_subspace subspace_span False)
      show "card (insert x B) = Suc (dim S)"
        using B False finiteI_independent by force
    qed
    then show ?thesis
      by (metis False Suc_eq_plus1 dim_span)
  qed
qed

lemma dim_singleton [simp]: "dim{x} = (if x = 0 then 0 else 1)"
  by (simp add: dim_insert)

proposition choose_subspace_of_subspace:
  assumes "n \<le> dim S"
  obtains T where "subspace T" "T \<subseteq> span S" "dim T = n"
proof -
  have "\<exists>T. subspace T \<and> T \<subseteq> span S \<and> dim T = n"
  using assms
  proof (induction n)
    case 0 then show ?case by (auto intro!: exI[where x="{0}"] span_zero)
  next
    case (Suc n)
    then obtain T where "subspace T" "T \<subseteq> span S" "dim T = n"
      by force
    then show ?case
    proof (cases "span S \<subseteq> span T")
      case True
      have "span T \<subseteq> span S"
        by (simp add: \<open>T \<subseteq> span S\<close> span_minimal)
      then have "dim S = dim T"
        by (rule span_eq_dim [OF subset_antisym [OF True]])
      then show ?thesis
        using Suc.prems \<open>dim T = n\<close> by linarith
    next
      case False
      then obtain y where y: "y \<in> S" "y \<notin> T"
        by (meson span_mono subsetI)
      then have "span (insert y T) \<subseteq> span S"
        by (metis (no_types) \<open>T \<subseteq> span S\<close> subsetD insert_subset span_superset span_mono span_span)
      with \<open>dim T = n\<close>  \<open>subspace T\<close> y show ?thesis
        apply (rule_tac x="span(insert y T)" in exI)
        using span_eq_iff by (fastforce simp: dim_insert)
    qed
  qed
  with that show ?thesis by blast
qed

lemma basis_subspace_exists:
  assumes "subspace S"
  obtains B where "finite B" "B \<subseteq> S" "independent B" "span B = S" "card B = dim S"
  by (metis assms span_subspace basis_exists finiteI_independent)

lemma dim_mono: assumes "V \<subseteq> span W" shows "dim V \<le> dim W"
proof -
  obtain B where "independent B" "B \<subseteq> W" "W \<subseteq> span B"
    using maximal_independent_subset[of W] by force
  with dim_le_card[of V B] assms independent_span_bound[of Basis B] basis_card_eq_dim[of B W]
    span_mono[of B W] span_minimal[OF _ subspace_span, of W B]
  show ?thesis
    by (auto simp: finite_Basis span_Basis)
qed

lemma dim_subset: "S \<subseteq> T \<Longrightarrow> dim S \<le> dim T"
  using dim_mono[of S T] by (auto intro: span_base)

lemma dim_eq_0 [simp]:
  "dim S = 0 \<longleftrightarrow> S \<subseteq> {0}"
  by (metis basis_exists card_eq_0_iff dim_span finiteI_independent span_empty subset_empty subset_singletonD)

lemma dim_UNIV[simp]: "dim UNIV = card Basis"
  using dim_eq_card[of Basis UNIV] by (simp add: independent_Basis span_Basis)

lemma independent_card_le_dim: assumes "B \<subseteq> V" and "independent B" shows "card B \<le> dim V"
  by (subst dim_eq_card[symmetric, OF refl \<open>independent B\<close>]) (rule dim_subset[OF \<open>B \<subseteq> V\<close>])

lemma dim_subset_UNIV: "dim S \<le> dimension"
  by (metis dim_subset subset_UNIV dim_UNIV dimension_def)

lemma card_ge_dim_independent:
  assumes BV: "B \<subseteq> V"
    and iB: "independent B"
    and dVB: "dim V \<le> card B"
  shows "V \<subseteq> span B"
proof
  fix a
  assume aV: "a \<in> V"
  {
    assume aB: "a \<notin> span B"
    then have iaB: "independent (insert a B)"
      using iB aV BV by (simp add: independent_insert)
    from aV BV have th0: "insert a B \<subseteq> V"
      by blast
    from aB have "a \<notin>B"
      by (auto simp add: span_base)
    with independent_card_le_dim[OF th0 iaB] dVB finiteI_independent[OF iB]
    have False by auto
  }
  then show "a \<in> span B" by blast
qed

lemma card_le_dim_spanning:
  assumes BV: "B \<subseteq> V"
    and VB: "V \<subseteq> span B"
    and fB: "finite B"
    and dVB: "dim V \<ge> card B"
  shows "independent B"
proof -
  {
    fix a
    assume a: "a \<in> B" "a \<in> span (B - {a})"
    from a fB have c0: "card B \<noteq> 0"
      by auto
    from a fB have cb: "card (B - {a}) = card B - 1"
      by auto
    {
      fix x
      assume x: "x \<in> V"
      from a have eq: "insert a (B - {a}) = B"
        by blast
      from x VB have x': "x \<in> span B"
        by blast
      from span_trans[OF a(2), unfolded eq, OF x']
      have "x \<in> span (B - {a})" .
    }
    then have th1: "V \<subseteq> span (B - {a})"
      by blast
    have th2: "finite (B - {a})"
      using fB by auto
    from dim_le_card[OF th1 th2]
    have c: "dim V \<le> card (B - {a})" .
    from c c0 dVB cb have False by simp
  }
  then show ?thesis
    unfolding dependent_def by blast
qed

lemma card_eq_dim: "B \<subseteq> V \<Longrightarrow> card B = dim V \<Longrightarrow> finite B \<Longrightarrow> independent B \<longleftrightarrow> V \<subseteq> span B"
  by (metis order_eq_iff card_le_dim_spanning card_ge_dim_independent)

lemma subspace_dim_equal:
  assumes "subspace S"
    and "subspace T"
    and "S \<subseteq> T"
    and "dim S \<ge> dim T"
  shows "S = T"
proof -
  obtain B where B: "B \<le> S" "independent B \<and> S \<subseteq> span B" "card B = dim S"
    using basis_exists[of S] by metis
  then have "span B \<subseteq> S"
    using span_mono[of B S] span_eq_iff[of S] assms by metis
  then have "span B = S"
    using B by auto
  have "dim S = dim T"
    using assms dim_subset[of S T] by auto
  then have "T \<subseteq> span B"
    using card_eq_dim[of B T] B finiteI_independent assms by auto
  then show ?thesis
    using assms \<open>span B = S\<close> by auto
qed

corollary dim_eq_span:
  shows "\<lbrakk>S \<subseteq> T; dim T \<le> dim S\<rbrakk> \<Longrightarrow> span S = span T"
  by (simp add: span_mono subspace_dim_equal)

lemma dim_psubset:
  "span S \<subset> span T \<Longrightarrow> dim S < dim T"
  by (metis (no_types, opaque_lifting) dim_span less_le not_le subspace_dim_equal subspace_span)

lemma dim_eq_full:
  shows "dim S = dimension \<longleftrightarrow> span S = UNIV"
  by (metis dim_eq_span dim_subset_UNIV span_Basis span_span subset_UNIV
        dim_UNIV dim_span dimension_def)

lemma indep_card_eq_dim_span:
  assumes "independent B"
  shows "finite B \<and> card B = dim (span B)"
  using dim_span_eq_card_independent[OF assms] finiteI_independent[OF assms] by auto

text \<open>More general size bound lemmas.\<close>

lemma independent_bound_general:
  "independent S \<Longrightarrow> finite S \<and> card S \<le> dim S"
  by (simp add: dim_eq_card_independent finiteI_independent)

lemma independent_explicit:
  shows "independent B \<longleftrightarrow> finite B \<and> (\<forall>c. (\<Sum>v\<in>B. c v *s v) = 0 \<longrightarrow> (\<forall>v \<in> B. c v = 0))"
  using independent_bound_general
  by (fastforce simp: dependent_finite)

proposition dim_sums_Int:
  assumes "subspace S" "subspace T"
  shows "dim {x + y |x y. x \<in> S \<and> y \<in> T} + dim(S \<inter> T) = dim S + dim T" (is "dim ?ST + _ = _")
proof -
  obtain B where B: "B \<subseteq> S \<inter> T" "S \<inter> T \<subseteq> span B"
             and indB: "independent B"
             and cardB: "card B = dim (S \<inter> T)"
    using basis_exists by metis
  then obtain C D where "B \<subseteq> C" "C \<subseteq> S" "independent C" "S \<subseteq> span C"
                    and "B \<subseteq> D" "D \<subseteq> T" "independent D" "T \<subseteq> span D"
    using maximal_independent_subset_extend
    by (metis Int_subset_iff \<open>B \<subseteq> S \<inter> T\<close> indB)
  then have "finite B" "finite C" "finite D"
    by (simp_all add: finiteI_independent indB independent_bound_general)
  have Beq: "B = C \<inter> D"
  proof (rule spanning_subset_independent [symmetric])
    show "independent (C \<inter> D)"
      by (meson \<open>independent C\<close> independent_mono inf.cobounded1)
  qed (use B \<open>C \<subseteq> S\<close> \<open>D \<subseteq> T\<close> \<open>B \<subseteq> C\<close> \<open>B \<subseteq> D\<close> in auto)
  then have Deq: "D = B \<union> (D - C)"
    by blast
  have CUD: "C \<union> D \<subseteq> ?ST"
  proof (simp, intro conjI)
    show "C \<subseteq> ?ST"
      using span_zero span_minimal [OF _ \<open>subspace T\<close>] \<open>C \<subseteq> S\<close> by force
    show "D \<subseteq> ?ST"
      using span_zero span_minimal [OF _ \<open>subspace S\<close>] \<open>D \<subseteq> T\<close> by force
  qed
  have "a v = 0" if 0: "(\<Sum>v\<in>C. a v *s v) + (\<Sum>v\<in>D - C. a v *s v) = 0"
                 and v: "v \<in> C \<union> (D-C)" for a v
  proof -
    have CsS: "\<And>x. x \<in> C \<Longrightarrow> a x *s x \<in> S"
      using \<open>C \<subseteq> S\<close> \<open>subspace S\<close> subspace_scale by auto
    have eq: "(\<Sum>v\<in>D - C. a v *s v) = - (\<Sum>v\<in>C. a v *s v)"
      using that add_eq_0_iff by blast
    have "(\<Sum>v\<in>D - C. a v *s v) \<in> S"
      by (simp add: eq CsS \<open>subspace S\<close> subspace_neg subspace_sum)
    moreover have "(\<Sum>v\<in>D - C. a v *s v) \<in> T"
      apply (rule subspace_sum [OF \<open>subspace T\<close>])
      by (meson DiffD1 \<open>D \<subseteq> T\<close> \<open>subspace T\<close> subset_eq subspace_def)
    ultimately have "(\<Sum>v \<in> D-C. a v *s v) \<in> span B"
      using B by blast
    then obtain e where e: "(\<Sum>v\<in>B. e v *s v) = (\<Sum>v \<in> D-C. a v *s v)"
      using span_finite [OF \<open>finite B\<close>] by force
    have "\<And>c v. \<lbrakk>(\<Sum>v\<in>C. c v *s v) = 0; v \<in> C\<rbrakk> \<Longrightarrow> c v = 0"
      using \<open>finite C\<close> \<open>independent C\<close> independentD by blast
    define cc where "cc x = (if x \<in> B then a x + e x else a x)" for x
    have [simp]: "C \<inter> B = B" "D \<inter> B = B" "C \<inter> - B = C-D" "B \<inter> (D - C) = {}"
      using \<open>B \<subseteq> C\<close> \<open>B \<subseteq> D\<close> Beq by blast+
    have f2: "(\<Sum>v\<in>C \<inter> D. e v *s v) = (\<Sum>v\<in>D - C. a v *s v)"
      using Beq e by presburger
    have f3: "(\<Sum>v\<in>C \<union> D. a v *s v) = (\<Sum>v\<in>C - D. a v *s v) + (\<Sum>v\<in>D - C. a v *s v) + (\<Sum>v\<in>C \<inter> D. a v *s v)"
      using \<open>finite C\<close> \<open>finite D\<close> sum.union_diff2 by blast
    have f4: "(\<Sum>v\<in>C \<union> (D - C). a v *s v) = (\<Sum>v\<in>C. a v *s v) + (\<Sum>v\<in>D - C. a v *s v)"
      by (meson Diff_disjoint \<open>finite C\<close> \<open>finite D\<close> finite_Diff sum.union_disjoint)
    have "(\<Sum>v\<in>C. cc v *s v) = 0"
      using 0 f2 f3 f4
      apply (simp add: cc_def Beq \<open>finite C\<close> sum.If_cases algebra_simps sum.distrib
          if_distrib if_distribR)
      apply (simp add: add.commute add.left_commute diff_eq)
      done
    then have "\<And>v. v \<in> C \<Longrightarrow> cc v = 0"
      using independent_explicit \<open>independent C\<close> \<open>finite C\<close> by blast
    then have C0: "\<And>v. v \<in> C - B \<Longrightarrow> a v = 0"
      by (simp add: cc_def Beq) meson
    then have [simp]: "(\<Sum>x\<in>C - B. a x *s x) = 0"
      by simp
    have "(\<Sum>x\<in>C. a x *s x) = (\<Sum>x\<in>B. a x *s x)"
    proof -
      have "C - D = C - B"
        using Beq by blast
      then show ?thesis
        using Beq \<open>(\<Sum>x\<in>C - B. a x *s x) = 0\<close> f3 f4 by auto
    qed
    with 0 have Dcc0: "(\<Sum>v\<in>D. a v *s v) = 0"
      by (subst Deq) (simp add: \<open>finite B\<close> \<open>finite D\<close> sum_Un)
    then have D0: "\<And>v. v \<in> D \<Longrightarrow> a v = 0"
      using independent_explicit \<open>independent D\<close> \<open>finite D\<close> by blast
    show ?thesis
      using v C0 D0 Beq by blast
  qed
  then have "independent (C \<union> (D - C))"
    unfolding independent_explicit
    using independent_explicit
    by (simp add: independent_explicit \<open>finite C\<close> \<open>finite D\<close> sum_Un del: Un_Diff_cancel)
  then have indCUD: "independent (C \<union> D)" by simp
  have "dim (S \<inter> T) = card B"
    by (rule dim_unique [OF B indB refl])
  moreover have "dim S = card C"
    by (metis \<open>C \<subseteq> S\<close> \<open>independent C\<close> \<open>S \<subseteq> span C\<close> basis_card_eq_dim)
  moreover have "dim T = card D"
    by (metis \<open>D \<subseteq> T\<close> \<open>independent D\<close> \<open>T \<subseteq> span D\<close> basis_card_eq_dim)
  moreover have "dim ?ST = card(C \<union> D)"
  proof -
    have *: "\<And>x y. \<lbrakk>x \<in> S; y \<in> T\<rbrakk> \<Longrightarrow> x + y \<in> span (C \<union> D)"
      by (meson \<open>S \<subseteq> span C\<close> \<open>T \<subseteq> span D\<close> span_add span_mono subsetCE sup.cobounded1 sup.cobounded2)
    show ?thesis
      by (auto intro: * dim_unique [OF CUD _ indCUD refl])
  qed
  ultimately show ?thesis
    using \<open>B = C \<inter> D\<close> [symmetric]
    by (simp add:  \<open>independent C\<close> \<open>independent D\<close> card_Un_Int finiteI_independent)
qed

lemma dependent_biggerset_general:
  "(finite S \<Longrightarrow> card S > dim S) \<Longrightarrow> dependent S"
  using independent_bound_general[of S] by (metis linorder_not_le)

lemma subset_le_dim:
  "S \<subseteq> span T \<Longrightarrow> dim S \<le> dim T"
  by (metis dim_span dim_subset)

lemma linear_inj_imp_surj:
  assumes lf: "linear scale scale f"
    and fi: "inj f"
  shows "surj f"
proof -
  interpret lf: linear scale scale f by fact
  from basis_exists[of UNIV] obtain B
    where B: "B \<subseteq> UNIV" "independent B" "UNIV \<subseteq> span B" "card B = dim UNIV"
    by blast
  from B(4) have d: "dim UNIV = card B"
    by simp
  have "UNIV \<subseteq> span (f ` B)"
  proof (rule card_ge_dim_independent)
    show "independent (f ` B)"
      by (simp add: B(2) fi lf.independent_inj_image)
    have "card (f ` B) = dim UNIV"
      by (metis B(1) card_image d fi inj_on_subset)
    then show "dim UNIV \<le> card (f ` B)"
      by simp
  qed blast
  then show ?thesis
    unfolding lf.span_image surj_def
    using B(3) by blast
qed

end

locale finite_dimensional_vector_space_pair_1 =
  vs1: finite_dimensional_vector_space s1 B1 + vs2: vector_space s2
  for s1 :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr "*a" 75)
  and B1 :: "'b set"
  and s2 :: "'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c" (infixr "*b" 75)
begin

sublocale vector_space_pair s1 s2 by unfold_locales

lemma dim_image_eq:
  assumes lf: "linear s1 s2 f"
    and fi: "inj_on f (vs1.span S)"
  shows "vs2.dim (f ` S) = vs1.dim S"
proof -
  interpret lf: linear by fact
  obtain B where B: "B \<subseteq> S" "vs1.independent B" "S \<subseteq> vs1.span B" "card B = vs1.dim S"
    using vs1.basis_exists[of S] by auto
  then have "vs1.span S = vs1.span B"
    using vs1.span_mono[of B S] vs1.span_mono[of S "vs1.span B"] vs1.span_span[of B] by auto
  moreover have "card (f ` B) = card B"
    using assms card_image[of f B] subset_inj_on[of f "vs1.span S" B] B vs1.span_superset by auto
  moreover have "(f ` B) \<subseteq> (f ` S)"
    using B by auto
  ultimately show ?thesis
    by (metis B(2) B(4) fi lf.dependent_inj_imageD lf.span_image vs2.dim_eq_card_independent vs2.dim_span)
qed

lemma dim_image_le:
  assumes lf: "linear s1 s2 f"
  shows "vs2.dim (f ` S) \<le> vs1.dim (S)"
proof -
  from vs1.basis_exists[of S] obtain B where
    B: "B \<subseteq> S" "vs1.independent B" "S \<subseteq> vs1.span B" "card B = vs1.dim S" by blast
  from B have fB: "finite B" "card B = vs1.dim S"
    using vs1.independent_bound_general by blast+
  have "vs2.dim (f ` S) \<le> card (f ` B)"
    apply (rule vs2.span_card_ge_dim)
    using lf B fB
      apply (auto simp add: module_hom.span_image module_hom.spans_image subset_image_iff
        linear_iff_module_hom)
    done
  also have "\<dots> \<le> vs1.dim S"
    using card_image_le[OF fB(1)] fB by simp
  finally show ?thesis .
qed

end

locale finite_dimensional_vector_space_pair =
  vs1: finite_dimensional_vector_space s1 B1 + vs2: finite_dimensional_vector_space s2 B2
  for s1 :: "'a::field \<Rightarrow> 'b::ab_group_add \<Rightarrow> 'b" (infixr "*a" 75)
  and B1 :: "'b set"
  and s2 :: "'a::field \<Rightarrow> 'c::ab_group_add \<Rightarrow> 'c" (infixr "*b" 75)
  and B2 :: "'c set"
begin

sublocale finite_dimensional_vector_space_pair_1 ..

lemma linear_surjective_imp_injective:
  assumes lf: "linear s1 s2 f" and sf: "surj f" and eq: "vs2.dim UNIV = vs1.dim UNIV"
    shows "inj f"
proof -
  interpret linear s1 s2 f by fact
  have *: "card (f ` B1) \<le> vs2.dim UNIV"
    using vs1.finite_Basis vs1.dim_eq_card[of B1 UNIV] sf
    by (auto simp: vs1.span_Basis vs1.independent_Basis eq
        simp del: vs2.dim_UNIV
        intro!: card_image_le)
  have indep_fB: "vs2.independent (f ` B1)"
    using vs1.finite_Basis vs1.dim_eq_card[of B1 UNIV] sf *
    by (intro vs2.card_le_dim_spanning[of "f ` B1" UNIV]) (auto simp: span_image vs1.span_Basis )
  have "vs2.dim UNIV \<le> card (f ` B1)"
    unfolding eq sf[symmetric] vs2.dim_span_eq_card_independent[symmetric, OF indep_fB]
      vs2.dim_span
    by (intro vs2.dim_mono) (auto simp: span_image vs1.span_Basis)
  with * have "card (f ` B1) = vs2.dim UNIV" by auto
  also have "... = card B1"
    unfolding eq vs1.dim_UNIV ..
  finally have "inj_on f B1"
    by (subst inj_on_iff_eq_card[OF vs1.finite_Basis])
  then show "inj f"
    using inj_on_span_iff_independent_image[OF indep_fB] vs1.span_Basis by auto
qed

lemma linear_injective_imp_surjective:
  assumes lf: "linear s1 s2 f" and sf: "inj f" and eq: "vs2.dim UNIV = vs1.dim UNIV"
    shows "surj f"
proof -
  interpret linear s1 s2 f by fact
  have *: False if b: "b \<notin> vs2.span (f ` B1)" for b
  proof -
    have *: "vs2.independent (f ` B1)"
      using vs1.independent_Basis by (intro independent_injective_image inj_on_subset[OF sf]) auto
    have **: "vs2.independent (insert b (f ` B1))"
      using b * by (rule vs2.independent_insertI)

    have "b \<notin> f ` B1" using vs2.span_base[of b "f ` B1"] b by auto
    then have "Suc (card B1) = card (insert b (f ` B1))"
      using sf[THEN inj_on_subset, of B1] by (subst card.insert_remove) (auto intro: vs1.finite_Basis simp: card_image)
    also have "\<dots> = vs2.dim (insert b (f ` B1))"
      using vs2.dim_eq_card_independent[OF **] by simp
    also have "vs2.dim (insert b (f ` B1)) \<le> vs2.dim B2"
      by (rule vs2.dim_mono) (auto simp: vs2.span_Basis)
    also have "\<dots> = card B1"
      using vs1.dim_span[of B1] vs2.dim_span[of B2] unfolding vs1.span_Basis vs2.span_Basis eq 
        vs1.dim_eq_card_independent[OF vs1.independent_Basis] by simp
    finally show False by simp
  qed
  have "f ` UNIV = f ` vs1.span B1" unfolding vs1.span_Basis ..
  also have "\<dots> = vs2.span (f ` B1)" unfolding span_image ..
  also have "\<dots> = UNIV" using * by blast
  finally show ?thesis .
qed

lemma linear_injective_isomorphism:
  assumes lf: "linear s1 s2 f"
    and fi: "inj f"
    and dims: "vs2.dim UNIV = vs1.dim UNIV"
  shows "\<exists>f'. linear s2 s1 f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
  unfolding isomorphism_expand[symmetric]
  using linear_injective_imp_surjective[OF lf fi dims]
  using fi left_right_inverse_eq lf linear_injective_left_inverse linear_surjective_right_inverse by blast

lemma linear_surjective_isomorphism:
  assumes lf: "linear s1 s2 f"
    and sf: "surj f"
    and dims: "vs2.dim UNIV = vs1.dim UNIV"
  shows "\<exists>f'. linear s2 s1 f' \<and> (\<forall>x. f' (f x) = x) \<and> (\<forall>x. f (f' x) = x)"
  using linear_surjective_imp_injective[OF lf sf dims] sf
    linear_exists_right_inverse_on[OF lf vs1.subspace_UNIV]
    linear_exists_left_inverse_on[OF lf vs1.subspace_UNIV]
    dims lf linear_injective_isomorphism by auto

lemma basis_to_basis_subspace_isomorphism:
  assumes s: "vs1.subspace S"
    and t: "vs2.subspace T"
    and d: "vs1.dim S = vs2.dim T"
    and B: "B \<subseteq> S" "vs1.independent B" "S \<subseteq> vs1.span B" "card B = vs1.dim S"
    and C: "C \<subseteq> T" "vs2.independent C" "T \<subseteq> vs2.span C" "card C = vs2.dim T"
  shows "\<exists>f. linear s1 s2 f \<and> f ` B = C \<and> f ` S = T \<and> inj_on f S"
proof -
  from B have fB: "finite B"
    by (simp add: vs1.finiteI_independent)
  from C have fC: "finite C"
    by (simp add: vs2.finiteI_independent)
  from finite_basis_to_basis_subspace_isomorphism[OF s t d fB B fC C] show ?thesis .
qed

end

context finite_dimensional_vector_space begin

lemma linear_surj_imp_inj:
  assumes lf: "linear scale scale f" and sf: "surj f"
  shows "inj f"
proof -
  interpret finite_dimensional_vector_space_pair scale Basis scale Basis by unfold_locales
  let ?U = "UNIV :: 'b set"
  from basis_exists[of ?U] obtain B
    where B: "B \<subseteq> ?U" "independent B" "?U \<subseteq> span B" and d: "card B = dim ?U"
    by blast
  {
    fix x
    assume x: "x \<in> span B" and fx: "f x = 0"
    from B(2) have fB: "finite B"
      using finiteI_independent by auto
    have Uspan: "UNIV \<subseteq> span (f ` B)"
      by (simp add: B(3) lf linear_spanning_surjective_image sf)
    have fBi: "independent (f ` B)"
    proof (rule card_le_dim_spanning)
      show "card (f ` B) \<le> dim ?U"
        using card_image_le d fB by fastforce
    qed (use fB Uspan in auto)
    have th0: "dim ?U \<le> card (f ` B)"
      by (rule span_card_ge_dim) (use Uspan fB in auto)
    moreover have "card (f ` B) \<le> card B"
      by (rule card_image_le, rule fB)
    ultimately have th1: "card B = card (f ` B)"
      unfolding d by arith
    have fiB: "inj_on f B"
      by (simp add: eq_card_imp_inj_on fB th1)
    from linear_indep_image_lemma[OF lf fB fBi fiB x] fx
    have "x = 0" by blast
  }
  then show ?thesis
    unfolding linear_inj_iff_eq_0[OF lf] using B(3) by blast
qed

lemma linear_inverse_left:
  assumes lf: "linear scale scale f"
    and lf': "linear scale scale f'"
  shows "f \<circ> f' = id \<longleftrightarrow> f' \<circ> f = id"
proof -
  {
    fix f f':: "'b \<Rightarrow> 'b"
    assume lf: "linear scale scale f" "linear scale scale f'"
    assume f: "f \<circ> f' = id"
    from f have sf: "surj f"
      by (auto simp add: o_def id_def surj_def) metis
    interpret finite_dimensional_vector_space_pair scale Basis scale Basis by unfold_locales
    from linear_surjective_isomorphism[OF lf(1) sf] lf f
    have "f' \<circ> f = id"
      unfolding fun_eq_iff o_def id_def by metis
  }
  then show ?thesis
    using lf lf' by metis
qed

lemma left_inverse_linear:
  assumes lf: "linear scale scale f"
    and gf: "g \<circ> f = id"
  shows "linear scale scale g"
proof -
  from gf have fi: "inj f"
    by (auto simp add: inj_on_def o_def id_def fun_eq_iff) metis
  interpret finite_dimensional_vector_space_pair scale Basis scale Basis by unfold_locales
  from linear_injective_isomorphism[OF lf fi]
  obtain h :: "'b \<Rightarrow> 'b" where "linear scale scale h" and h: "\<forall>x. h (f x) = x" "\<forall>x. f (h x) = x"
    by blast
  have "h = g"
    by (metis gf h isomorphism_expand left_right_inverse_eq)
  with \<open>linear scale scale h\<close> show ?thesis by blast
qed

lemma inj_linear_imp_inv_linear:
  assumes "linear scale scale f" "inj f" shows "linear scale scale (inv f)"
  using assms inj_iff left_inverse_linear by blast

lemma right_inverse_linear:
  assumes lf: "linear scale scale f"
    and gf: "f \<circ> g = id"
  shows "linear scale scale g"
proof -
  from gf have fi: "surj f"
    by (auto simp add: surj_def o_def id_def) metis
  interpret finite_dimensional_vector_space_pair scale Basis scale Basis by unfold_locales
  from linear_surjective_isomorphism[OF lf fi]
  obtain h:: "'b \<Rightarrow> 'b" where h: "linear scale scale h" "\<forall>x. h (f x) = x" "\<forall>x. f (h x) = x"
    by blast
  then have "h = g"
    by (metis gf isomorphism_expand left_right_inverse_eq)
  with h(1) show ?thesis by blast
qed

end

context finite_dimensional_vector_space_pair begin

lemma subspace_isomorphism:
  assumes s: "vs1.subspace S"
    and t: "vs2.subspace T"
    and d: "vs1.dim S = vs2.dim T"
  shows "\<exists>f. linear s1 s2 f \<and> f ` S = T \<and> inj_on f S"
proof -
  from vs1.basis_exists[of S] vs1.finiteI_independent
  obtain B where B: "B \<subseteq> S" "vs1.independent B" "S \<subseteq> vs1.span B" "card B = vs1.dim S" and fB: "finite B"
    by metis
  from vs2.basis_exists[of T] vs2.finiteI_independent
  obtain C where C: "C \<subseteq> T" "vs2.independent C" "T \<subseteq> vs2.span C" "card C = vs2.dim T" and fC: "finite C"
    by metis
  from B(4) C(4) card_le_inj[of B C] d
  obtain f where f: "f ` B \<subseteq> C" "inj_on f B" using \<open>finite B\<close> \<open>finite C\<close>
    by auto
  from linear_independent_extend[OF B(2)]
  obtain g where g: "linear s1 s2 g" "\<forall>x\<in> B. g x = f x"
    by blast
  interpret g: linear s1 s2 g by fact
  from inj_on_iff_eq_card[OF fB, of f] f(2) have "card (f ` B) = card B"
    by simp
  with B(4) C(4) have ceq: "card (f ` B) = card C"
    using d by simp
  have "g ` B = f ` B"
    using g(2) by (auto simp add: image_iff)
  also have "\<dots> = C" using card_subset_eq[OF fC f(1) ceq] .
  finally have gBC: "g ` B = C" .
  have gi: "inj_on g B"
    using f(2) g(2) by (auto simp add: inj_on_def)
  note g0 = linear_indep_image_lemma[OF g(1) fB, unfolded gBC, OF C(2) gi]
  {
    fix x y
    assume x: "x \<in> S" and y: "y \<in> S" and gxy: "g x = g y"
    from B(3) x y have x': "x \<in> vs1.span B" and y': "y \<in> vs1.span B"
      by blast+
    from gxy have th0: "g (x - y) = 0"
      by (simp add: linear_diff g)
    have th1: "x - y \<in> vs1.span B"
      using x' y' by (metis vs1.span_diff)
    have "x = y"
      using g0[OF th1 th0] by simp
  }
  then have giS: "inj_on g S"
    unfolding inj_on_def by blast
  from vs1.span_subspace[OF B(1,3) s] have "g ` S = vs2.span (g ` B)"
    by (simp add: module_hom.span_image[OF g(1)[unfolded linear_iff_module_hom]])
  also have "\<dots> = vs2.span C" unfolding gBC ..
  also have "\<dots> = T" using vs2.span_subspace[OF C(1,3) t] .
  finally have gS: "g ` S = T" .
  from g(1) gS giS show ?thesis
    by blast
qed

end

hide_const (open) linear

end