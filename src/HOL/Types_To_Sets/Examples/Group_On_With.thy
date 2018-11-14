(*  Title:      HOL/Types_To_Sets/Examples/Group_On_With.thy
    Author:     Fabian Immler, TU München
*)
theory Group_On_With
imports
  Prerequisites
  Types_To_Sets
begin

subsection \<open>\<^emph>\<open>on\<close> carrier set \<^emph>\<open>with\<close> explicit group operations\<close>

locale semigroup_add_on_with =
  fixes S::"'a set" and pls::"'a\<Rightarrow>'a\<Rightarrow>'a"
  assumes add_assoc: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> c \<in> S \<Longrightarrow> pls (pls a b) c = pls a (pls b c)"
  assumes add_mem: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> pls a b \<in> S"

locale ab_semigroup_add_on_with = semigroup_add_on_with +
  assumes add_commute: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> pls a b = pls b a"

locale comm_monoid_add_on_with = ab_semigroup_add_on_with +
  fixes z
  assumes add_zero: "a \<in> S \<Longrightarrow> pls z a = a"
  assumes zero_mem: "z \<in> S"
begin

lemma carrier_ne: "S \<noteq> {}" using zero_mem by auto

end

definition "sum_with pls z f S =
  (if \<exists>C. f ` S \<subseteq> C \<and> comm_monoid_add_on_with C pls z then
    Finite_Set.fold (pls o f) z S else z)"

lemma sum_with_empty[simp]: "sum_with pls z f {} = z"
  by (auto simp: sum_with_def)

lemma sum_with_cases[case_names comm zero]:
  "P (sum_with pls z f S)"
  if "\<And>C. f ` S \<subseteq> C \<Longrightarrow> comm_monoid_add_on_with C pls z \<Longrightarrow> P (Finite_Set.fold (pls o f) z S)"
    "(\<And>C. comm_monoid_add_on_with C pls z \<Longrightarrow> (\<exists>s\<in>S. f s \<notin> C)) \<Longrightarrow> P z"
  using that
  by (auto simp: sum_with_def)

context comm_monoid_add_on_with begin

lemma sum_with_infinite: "infinite A \<Longrightarrow> sum_with pls z g A = z"
  by (induction rule: sum_with_cases) auto

context begin

private abbreviation "pls' \<equiv> \<lambda>x y. pls (if x \<in> S then x else z) (if y \<in> S then y else z)"

lemma fold_pls'_mem: "Finite_Set.fold (pls' \<circ> g) z A \<in> S"
  if "g ` A \<subseteq> S"
proof cases
  assume A: "finite A"
  interpret comp_fun_commute "pls' o g"
    using that
    using add_assoc add_commute add_mem zero_mem
    by unfold_locales auto
  from fold_graph_fold[OF A] have "fold_graph (pls' \<circ> g) z A (Finite_Set.fold (pls' \<circ> g) z A)" .
  from fold_graph_closed_lemma[OF this, of S "pls' \<circ> g"]
    add_assoc add_commute add_mem zero_mem
  show ?thesis
    by auto
qed (use add_assoc add_commute add_mem zero_mem in simp)

lemma fold_pls'_eq: "Finite_Set.fold (pls' \<circ> g) z A = Finite_Set.fold (pls \<circ> g) z A"
  if "g ` A \<subseteq> S"
  using add_assoc add_commute add_mem zero_mem that
  by (intro fold_closed_eq[where B=S]) auto

lemma sum_with_mem: "sum_with pls z g A \<in> S" if "g ` A \<subseteq> S"
proof -
  interpret comp_fun_commute "pls' o g"
    using add_assoc add_commute add_mem zero_mem that
    by unfold_locales auto
  have "\<exists>C. g ` A \<subseteq> C \<and> comm_monoid_add_on_with C pls z"
    using that comm_monoid_add_on_with_axioms by auto
  then show ?thesis
    using fold_pls'_mem[OF that]
    by (simp add: sum_with_def fold_pls'_eq that)
qed

lemma sum_with_insert:
  "sum_with pls z g (insert x A) = pls (g x) (sum_with pls z g A)"
  if g_into: "g x \<in> S" "g ` A \<subseteq> S"
    and A: "finite A" and x: "x \<notin> A"
proof -
  interpret comp_fun_commute "pls' o g"
    using add_assoc add_commute add_mem zero_mem g_into
    by unfold_locales auto
  have "Finite_Set.fold (pls \<circ> g) z (insert x A) = Finite_Set.fold (pls' \<circ> g) z (insert x A)"
    using g_into
    by (subst fold_pls'_eq) auto
  also have "\<dots> = pls' (g x) (Finite_Set.fold (pls' \<circ> g) z A)"
    unfolding fold_insert[OF A x]
    by (auto simp: o_def)
  also have "\<dots> = pls (g x) (Finite_Set.fold (pls' \<circ> g) z A)"
  proof -
    from fold_graph_fold[OF A] have "fold_graph (pls' \<circ> g) z A (Finite_Set.fold (pls' \<circ> g) z A)" .
    from fold_graph_closed_lemma[OF this, of S "pls' \<circ> g"] add_assoc add_commute add_mem zero_mem
    have "Finite_Set.fold (pls' \<circ> g) z A \<in> S"
      by auto
    then show ?thesis
      using g_into by auto
  qed
  also have "Finite_Set.fold (pls' \<circ> g) z A = Finite_Set.fold (pls \<circ> g) z A"
    using g_into
    by (subst fold_pls'_eq) auto
  finally
  have "Finite_Set.fold (pls \<circ> g) z (insert x A) = pls (g x) (Finite_Set.fold (pls \<circ> g) z A)" .
  moreover
  have "\<exists>C. g ` insert x A \<subseteq> C \<and> comm_monoid_add_on_with C pls z"
    "\<exists>C. g ` A \<subseteq> C \<and> comm_monoid_add_on_with C pls z"
    using that (1,2) comm_monoid_add_on_with_axioms by auto
  ultimately show ?thesis
    by (simp add: sum_with_def)
qed

end

end

locale ab_group_add_on_with = comm_monoid_add_on_with +
  fixes mns um
  assumes ab_left_minus: "a \<in> S \<Longrightarrow> pls (um a) a = z"
  assumes ab_diff_conv_add_uminus: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> mns a b = pls a (um b)"
  assumes uminus_mem: "a \<in> S \<Longrightarrow> um a \<in> S"


subsection \<open>obvious instances (by type class constraints)\<close>

lemma semigroup_add_on_with[simp]: "semigroup_add_on_with (UNIV::'a::semigroup_add set) (+)"
  by (auto simp: semigroup_add_on_with_def ac_simps)

lemma semigroup_add_on_with_Ball_def: "semigroup_add_on_with S pls \<longleftrightarrow>
  (\<forall>a\<in>S. \<forall>b\<in>S. \<forall>c\<in>S. pls (pls a b) c = pls a (pls b c)) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. pls a b \<in> S)"
  by (auto simp: semigroup_add_on_with_def)

lemma ab_semigroup_add_on_with_Ball_def:
  "ab_semigroup_add_on_with S pls \<longleftrightarrow> semigroup_add_on_with S pls \<and> (\<forall>a\<in>S. \<forall>b\<in>S. pls a b = pls b a)"
  by (auto simp: ab_semigroup_add_on_with_def ab_semigroup_add_on_with_axioms_def)

lemma ab_semigroup_add_on_with[simp]: "ab_semigroup_add_on_with (UNIV::'a::ab_semigroup_add set) (+)"
  by (auto simp: ab_semigroup_add_on_with_Ball_def ac_simps)

lemma comm_monoid_add_on_with_Ball_def:
  "comm_monoid_add_on_with S pls z \<longleftrightarrow> ab_semigroup_add_on_with S pls \<and> (\<forall>a\<in>S. pls z a = a) \<and> z \<in> S"
  by (auto simp: comm_monoid_add_on_with_def comm_monoid_add_on_with_axioms_def)

lemma comm_monoid_add_on_with[simp]: "comm_monoid_add_on_with UNIV (+) (0::'a::comm_monoid_add)"
  by (auto simp: comm_monoid_add_on_with_Ball_def ab_semigroup_add_on_with_Ball_def
      semigroup_add_on_with_Ball_def ac_simps)

lemma ab_group_add_on_with_Ball_def:
  "ab_group_add_on_with S pls z mns um \<longleftrightarrow> comm_monoid_add_on_with S pls z \<and>
    (\<forall>a\<in>S. pls (um a) a = z) \<and> (\<forall>a\<in>S. \<forall>b\<in>S. mns a b = pls a (um b)) \<and> (\<forall>a\<in>S. um a \<in> S)"
  by (auto simp: ab_group_add_on_with_def ab_group_add_on_with_axioms_def)

lemma ab_group_add_on_with[simp]: "ab_group_add_on_with (UNIV::'a::ab_group_add set) (+) 0 (-) uminus"
  by (auto simp: ab_group_add_on_with_Ball_def)

lemma sum_with: "sum f S = sum_with (+) 0 f S"
proof (induction rule: sum_with_cases)
  case (comm C)
  then show ?case
    unfolding sum.eq_fold
    by simp
next
  case zero
  from zero[OF comm_monoid_add_on_with]
  show ?case by simp
qed


subsection \<open>transfer rules\<close>

lemma semigroup_add_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique A"
  shows "(rel_set A ===> (A ===> A ===> A) ===> (=)) semigroup_add_on_with semigroup_add_on_with"
  unfolding semigroup_add_on_with_Ball_def
  by transfer_prover

lemma Domainp_applyI:
  includes lifting_syntax
  shows "(A ===> B) f g \<Longrightarrow> A x y \<Longrightarrow> Domainp B (f x)"
  by (auto simp: rel_fun_def)

lemma Domainp_apply2I:
  includes lifting_syntax
  shows "(A ===> B ===> C) f g \<Longrightarrow> A x y \<Longrightarrow> B x' y' \<Longrightarrow> Domainp C (f x x')"
  by (force simp: rel_fun_def)

lemma right_total_semigroup_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows "((A ===> A ===> A) ===> (=)) (semigroup_add_on_with (Collect (Domainp A))) class.semigroup_add"
proof (intro rel_funI)
  fix x y assume xy[transfer_rule]: "(A ===> A ===> A) x y"
  show "semigroup_add_on_with (Collect (Domainp A)) x = class.semigroup_add y"
    unfolding semigroup_add_on_with_def class.semigroup_add_def
    by transfer (auto intro!: Domainp_apply2I[OF xy])
qed

lemma ab_semigroup_add_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique A"
  shows
    "(rel_set A ===> (A ===> A ===> A) ===> (=)) ab_semigroup_add_on_with ab_semigroup_add_on_with"
  unfolding ab_semigroup_add_on_with_Ball_def by transfer_prover

lemma right_total_ab_semigroup_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows
    "((A ===> A ===> A) ===> (=)) (ab_semigroup_add_on_with (Collect (Domainp A))) class.ab_semigroup_add"
  unfolding class.ab_semigroup_add_def class.ab_semigroup_add_axioms_def ab_semigroup_add_on_with_Ball_def
  by transfer_prover

lemma comm_monoid_add_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "bi_unique A"
  shows
    "(rel_set A ===> (A ===> A ===> A) ===> A ===> (=)) comm_monoid_add_on_with comm_monoid_add_on_with"
  unfolding comm_monoid_add_on_with_Ball_def
  by transfer_prover

lemma right_total_comm_monoid_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows
    "((A ===> A ===> A) ===> A ===> (=))
      (comm_monoid_add_on_with (Collect (Domainp A))) class.comm_monoid_add"
proof (intro rel_funI)
  fix p p' z z'
  assume [transfer_rule]: "(A ===> A ===> A) p p'" "A z z'"
  show "comm_monoid_add_on_with (Collect (Domainp A)) p z = class.comm_monoid_add p' z'"
    unfolding class.comm_monoid_add_def class.comm_monoid_add_axioms_def comm_monoid_add_on_with_Ball_def
    apply transfer
    using \<open>A z z'\<close>
    by auto
qed

lemma ab_group_add_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows "((A ===> A ===> A) ===> A  ===> (A ===> A ===> A) ===> (A ===> A)===> (=))
      (ab_group_add_on_with (Collect (Domainp A))) class.ab_group_add"
proof (intro rel_funI)
  fix p p' z z' m m' um um'
  assume [transfer_rule]:
    "(A ===> A ===> A) p p'" "A z z'" "(A ===> A ===> A) m m'"
    and um[transfer_rule]: "(A ===> A) um um'"
  show "ab_group_add_on_with (Collect (Domainp A)) p z m um = class.ab_group_add p' z' m' um'"
    unfolding class.ab_group_add_def class.ab_group_add_axioms_def ab_group_add_on_with_Ball_def
    by transfer (use um in \<open>auto simp: rel_fun_def\<close>)
qed

lemma ab_group_add_on_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A"
  shows
    "(rel_set A ===> (A ===> A ===> A) ===> A  ===> (A ===> A ===> A) ===> (A ===> A)===> (=))
      ab_group_add_on_with ab_group_add_on_with"
  unfolding class.ab_group_add_def class.ab_group_add_axioms_def ab_group_add_on_with_Ball_def
  by transfer_prover

lemma ex_comm_monoid_add_around_imageE:
  includes lifting_syntax
  assumes ex_comm: "\<exists>C. f ` S \<subseteq> C \<and> comm_monoid_add_on_with C pls zero"
  assumes transfers: "(A ===> A ===> A) pls pls'" "A zero zero'" "Domainp (rel_set B) S"
    and in_dom: "\<And>x. x \<in> S \<Longrightarrow> Domainp A (f x)"
  obtains C where "comm_monoid_add_on_with C pls zero" "f ` S \<subseteq> C" "Domainp (rel_set A) C"
proof -
  from ex_comm obtain C0 where C0: "f ` S \<subseteq> C0" and comm: "comm_monoid_add_on_with C0 pls zero"
    by auto
  define C where "C = C0 \<inter> Collect (Domainp A)"
  have "comm_monoid_add_on_with C pls zero"
    using comm Domainp_apply2I[OF \<open>(A ===> A ===> A) pls pls'\<close>] \<open>A zero zero'\<close>
    by (auto simp: comm_monoid_add_on_with_Ball_def ab_semigroup_add_on_with_Ball_def
        semigroup_add_on_with_def C_def)
  moreover have "f ` S \<subseteq> C" using C0
    by (auto simp: C_def in_dom)
  moreover have "Domainp (rel_set A) C" by (auto simp: C_def Domainp_set)
  ultimately show ?thesis ..
qed

lemma sum_with_transfer[transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total A" "bi_unique A" "bi_unique B"
  shows "((A ===> A ===> A) ===> A ===> (B ===> A) ===> rel_set B ===> A)
    sum_with sum_with"
proof (safe intro!: rel_funI)
  fix pls pls' zero zero' f g S T
  assume transfer_pls[transfer_rule]: "(A ===> A ===> A) pls pls'"
    and transfer_zero[transfer_rule]: "A zero zero'"
  assume transfer_g[transfer_rule]: "(B ===> A) f g"
    and transfer_T[transfer_rule]: "rel_set B S T"
  show "A (sum_with pls zero f S) (sum_with pls' zero' g T)"
  proof cases
    assume ex_comm: "\<exists>C. f ` S \<subseteq> C \<and> comm_monoid_add_on_with C pls zero"
    have Domains: "Domainp (rel_set B) S" "(\<And>x. x \<in> S \<Longrightarrow> Domainp A (f x))"
      using transfer_T transfer_g
      by auto (meson Domainp_applyI rel_set_def)
    from ex_comm_monoid_add_around_imageE[OF ex_comm transfer_pls transfer_zero Domains]
    obtain C where comm: "comm_monoid_add_on_with C pls zero"
      and C: "f ` S \<subseteq> C"
      and "Domainp (rel_set A) C"
      by auto
    then obtain C' where [transfer_rule]: "rel_set A C C'" by auto
    interpret comm: comm_monoid_add_on_with C pls zero by fact
    have C': "g ` T \<subseteq> C'"
      by transfer (rule C)
    have comm': "comm_monoid_add_on_with C' pls' zero'"
      by transfer (rule comm)
    then interpret comm': comm_monoid_add_on_with C' pls' zero' .
    from C' comm' have ex_comm': "\<exists>C. g ` T \<subseteq> C \<and> comm_monoid_add_on_with C pls' zero'" by auto
    show ?thesis
      using transfer_T C C'
    proof (induction S arbitrary: T rule: infinite_finite_induct)
      case (infinite S)
      note [transfer_rule] = infinite.prems
      from infinite.hyps have "infinite T" by transfer
      then show ?case by (simp add: sum_with_def infinite.hyps \<open>A zero zero'\<close>)
    next
      case [transfer_rule]: empty
      have "T = {}" by transfer rule
      then show ?case by (simp add: sum_with_def \<open>A zero zero'\<close>)
    next
      case (insert x F)
      note [transfer_rule] = insert.prems(1)
      have [simp]: "finite T"
        by transfer (simp add: insert.hyps)
      obtain y where [transfer_rule]: "B x y" and y: "y \<in> T"
        by (meson insert.prems insertI1 rel_setD1)
      define T' where "T' = T - {y}"
      have T_def: "T = insert y T'"
        by (auto simp: T'_def y)
      define sF where "sF = sum_with pls zero f F"
      define sT where "sT = sum_with pls' zero' g T'"
      have [simp]: "y \<notin> T'" "finite T'"
        by (auto simp: y T'_def)
      have "rel_set B (insert x F - {x}) T'"
        unfolding T'_def
        by transfer_prover
      then have transfer_T'[transfer_rule]: "rel_set B F T'"
        using insert.hyps
        by simp
      from insert.prems have "f ` F \<subseteq> C" "g ` T' \<subseteq> C'"
        by (auto simp: T'_def)
      from insert.IH[OF transfer_T' this] have [transfer_rule]: "A sF sT" by (auto simp: sF_def sT_def o_def)
      have rew: "(sum_with pls zero f (insert x F)) = pls (f x) (sum_with pls zero f F)"
        apply (subst comm.sum_with_insert)
        subgoal using insert.prems by auto
        subgoal using insert.prems by auto
        subgoal by fact
        subgoal by fact
        subgoal by auto
        done
      have rew': "(sum_with pls' zero' g (insert y T')) = pls' (g y) (sum_with pls' zero' g T')"
        apply (subst comm'.sum_with_insert)
        subgoal
          apply transfer
          using insert.prems by auto
        subgoal
          apply transfer
          using insert.prems by auto
        subgoal by fact
        subgoal by fact
        subgoal by auto
        done
      have "A (sum_with pls zero f (insert x F)) (sum_with pls' zero' g (insert y T'))"
        unfolding sT_def[symmetric] sF_def[symmetric] rew rew'
        by transfer_prover
      then show ?case
        by (simp add: T_def)
    qed
  next
    assume *: "\<nexists>C. f ` S \<subseteq> C \<and> comm_monoid_add_on_with C pls zero"
    then have **: "\<nexists>C'. g ` T \<subseteq> C' \<and> comm_monoid_add_on_with C' pls' zero'"
      by transfer simp
    show ?thesis
      by (simp add: sum_with_def * ** \<open>A zero zero'\<close>)
  qed
qed


subsection \<open>Rewrite rules to make \<open>ab_group_add\<close> operations explicit\<close>

named_theorems explicit_ab_group_add

lemmas [explicit_ab_group_add] = sum_with


subsection \<open>Locale defining \<open>ab_group_add\<close>-Operations in a local type\<close>

locale local_typedef_ab_group_add_on_with = local_typedef S s +
  ab_group_add_on_with S
  for S ::"'b set" and s::"'s itself"
begin

lemma mem_minus_lt: "x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> mns x y \<in> S"
  using ab_diff_conv_add_uminus[of x y] add_mem[of x "um y"] uminus_mem[of y]
  by auto

context includes lifting_syntax begin

definition plus_S::"'s \<Rightarrow> 's \<Rightarrow> 's" where "plus_S = (rep ---> rep ---> Abs) pls"
definition minus_S::"'s \<Rightarrow> 's \<Rightarrow> 's" where "minus_S = (rep ---> rep ---> Abs) mns"
definition uminus_S::"'s \<Rightarrow> 's" where "uminus_S = (rep ---> Abs) um"
definition zero_S::"'s" where "zero_S = Abs z"

lemma plus_S_transfer[transfer_rule]: "(cr_S ===> cr_S ===> cr_S) pls plus_S"
  unfolding plus_S_def
  by (auto simp: cr_S_def add_mem intro!: rel_funI)

lemma minus_S_transfer[transfer_rule]: "(cr_S ===> cr_S ===> cr_S) mns minus_S"
  unfolding minus_S_def
  by (auto simp: cr_S_def mem_minus_lt intro!: rel_funI)

lemma uminus_S_transfer[transfer_rule]: "(cr_S ===> cr_S) um uminus_S"
  unfolding uminus_S_def
  by (auto simp: cr_S_def uminus_mem intro!: rel_funI)

lemma zero_S_transfer[transfer_rule]: "cr_S z zero_S"
  unfolding zero_S_def
  by (auto simp: cr_S_def zero_mem intro!: rel_funI)

end

sublocale type: ab_group_add plus_S "zero_S::'s" minus_S uminus_S
  apply unfold_locales
  subgoal by transfer (rule add_assoc)
  subgoal by transfer (rule add_commute)
  subgoal by transfer (rule add_zero)
  subgoal by transfer (rule ab_left_minus)
  subgoal by transfer (rule ab_diff_conv_add_uminus)
  done

context includes lifting_syntax begin

lemma sum_transfer[transfer_rule]:
  "((A===>cr_S) ===> rel_set A ===> cr_S) (sum_with pls z) type.sum"
  if [transfer_rule]: "bi_unique A"
proof (safe intro!: rel_funI)
  fix f g I J
  assume fg[transfer_rule]: "(A ===> cr_S) f g" and rel_set: "rel_set A I J"
  show "cr_S (sum_with pls z f I) (type.sum g J)"
    using rel_set
  proof (induction I arbitrary: J rule: infinite_finite_induct)
    case (infinite I)
    note [transfer_rule] = infinite.prems
    from infinite.hyps have "infinite J" by transfer
    with infinite.hyps show ?case
      by (simp add: zero_S_transfer sum_with_infinite)
  next
    case [transfer_rule]: empty
    have "J = {}" by transfer rule
    then show ?case by (simp add: zero_S_transfer)
  next
    case (insert x F)
    note [transfer_rule] = insert.prems
    have [simp]: "finite J"
      by transfer (simp add: insert.hyps)
    obtain y where [transfer_rule]: "A x y" and y: "y \<in> J"
      by (meson insert.prems insertI1 rel_setD1)
    define J' where "J' = J - {y}"
    have T_def: "J = insert y J'"
      by (auto simp: J'_def y)
    define sF where "sF = sum_with pls z f F"
    define sT where "sT = type.sum g J'"
    have [simp]: "y \<notin> J'" "finite J'"
      by (auto simp: y J'_def)
    have "rel_set A (insert x F - {x}) J'"
      unfolding J'_def
      by transfer_prover
    then have "rel_set A F J'"
      using insert.hyps
      by simp
    from insert.IH[OF this] have [transfer_rule]: "cr_S sF sT" by (auto simp: sF_def sT_def)
    have f_S: "f x \<in> S" "f ` F \<subseteq> S"
      using \<open>A x y\<close> fg insert.prems
      by (auto simp: rel_fun_def cr_S_def rel_set_def)
    have "cr_S (pls (f x) sF) (plus_S (g y) sT)" by transfer_prover
    then have "cr_S (sum_with pls z f (insert x F)) (type.sum g (insert y J'))"
      by (simp add: sum_with_insert insert.hyps type.sum.insert_remove sF_def[symmetric]
          sT_def[symmetric] f_S)
    then show ?case
      by (simp add: T_def)
  qed
qed

end

end


subsection \<open>transfer theorems from \<^term>\<open>class.ab_group_add\<close> to \<^term>\<open>ab_group_add_on_with\<close>\<close>

context ab_group_add_on_with begin

context includes lifting_syntax assumes ltd: "\<exists>(Rep::'s \<Rightarrow> 'a) (Abs::'a \<Rightarrow> 's). type_definition Rep Abs S" begin

interpretation local_typedef_ab_group_add_on_with pls z mns um S "TYPE('s)" by unfold_locales fact

text\<open>Get theorem names:\<close>
print_locale! ab_group_add

lemmas lt_sum_mono_neutral_cong_left = sum.mono_neutral_cong_left
  [var_simplified explicit_ab_group_add,
    unoverload_type 'c,
    OF type.comm_monoid_add_axioms,
    untransferred]

end

lemmas sum_mono_neutral_cong_left =
  lt_sum_mono_neutral_cong_left
    [cancel_type_definition,
    OF carrier_ne,
    simplified pred_fun_def, simplified]

end

end