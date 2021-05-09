(*  Title:      HOL/Analysis/Determinants.thy
    Author:     Amine Chaieb, University of Cambridge; proofs reworked by LCP
*)

section \<open>Traces and Determinants of Square Matrices\<close>

theory Determinants
imports
  "HOL-Combinatorics.Permutations"
  Cartesian_Space
begin

subsection  \<open>Trace\<close>

definition\<^marker>\<open>tag important\<close>  trace :: "'a::semiring_1^'n^'n \<Rightarrow> 'a"
  where "trace A = sum (\<lambda>i. ((A$i)$i)) (UNIV::'n set)"

lemma  trace_0: "trace (mat 0) = 0"
  by (simp add: trace_def mat_def)

lemma  trace_I: "trace (mat 1 :: 'a::semiring_1^'n^'n) = of_nat(CARD('n))"
  by (simp add: trace_def mat_def)

lemma  trace_add: "trace ((A::'a::comm_semiring_1^'n^'n) + B) = trace A + trace B"
  by (simp add: trace_def sum.distrib)

lemma  trace_sub: "trace ((A::'a::comm_ring_1^'n^'n) - B) = trace A - trace B"
  by (simp add: trace_def sum_subtractf)

lemma  trace_mul_sym: "trace ((A::'a::comm_semiring_1^'n^'m) ** B) = trace (B**A)"
  apply (simp add: trace_def matrix_matrix_mult_def)
  apply (subst sum.swap)
  apply (simp add: mult.commute)
  done

subsubsection\<^marker>\<open>tag important\<close>  \<open>Definition of determinant\<close>

definition\<^marker>\<open>tag important\<close>  det:: "'a::comm_ring_1^'n^'n \<Rightarrow> 'a" where
  "det A =
    sum (\<lambda>p. of_int (sign p) * prod (\<lambda>i. A$i$p i) (UNIV :: 'n set))
      {p. p permutes (UNIV :: 'n set)}"

text \<open>Basic determinant properties\<close>

lemma  det_transpose [simp]: "det (transpose A) = det (A::'a::comm_ring_1 ^'n^'n)"
proof -
  let ?di = "\<lambda>A i j. A$i$j"
  let ?U = "(UNIV :: 'n set)"
  have fU: "finite ?U" by simp
  {
    fix p
    assume p: "p \<in> {p. p permutes ?U}"
    from p have pU: "p permutes ?U"
      by blast
    have sth: "sign (inv p) = sign p"
      by (metis sign_inverse fU p mem_Collect_eq permutation_permutes)
    from permutes_inj[OF pU]
    have pi: "inj_on p ?U"
      by (blast intro: subset_inj_on)
    from permutes_image[OF pU]
    have "prod (\<lambda>i. ?di (transpose A) i (inv p i)) ?U =
      prod (\<lambda>i. ?di (transpose A) i (inv p i)) (p ` ?U)"
      by simp
    also have "\<dots> = prod ((\<lambda>i. ?di (transpose A) i (inv p i)) \<circ> p) ?U"
      unfolding prod.reindex[OF pi] ..
    also have "\<dots> = prod (\<lambda>i. ?di A i (p i)) ?U"
    proof -
      have "((\<lambda>i. ?di (transpose A) i (inv p i)) \<circ> p) i = ?di A i (p i)" if "i \<in> ?U" for i
        using that permutes_inv_o[OF pU] permutes_in_image[OF pU]
        unfolding transpose_def by (simp add: fun_eq_iff)
      then show "prod ((\<lambda>i. ?di (transpose A) i (inv p i)) \<circ> p) ?U = prod (\<lambda>i. ?di A i (p i)) ?U"
        by (auto intro: prod.cong)
    qed
    finally have "of_int (sign (inv p)) * (prod (\<lambda>i. ?di (transpose A) i (inv p i)) ?U) =
      of_int (sign p) * (prod (\<lambda>i. ?di A i (p i)) ?U)"
      using sth by simp
  }
  then show ?thesis
    unfolding det_def
    by (subst sum_permutations_inverse) (blast intro: sum.cong)
qed

lemma  det_lowerdiagonal:
  fixes A :: "'a::comm_ring_1^('n::{finite,wellorder})^('n::{finite,wellorder})"
  assumes ld: "\<And>i j. i < j \<Longrightarrow> A$i$j = 0"
  shows "det A = prod (\<lambda>i. A$i$i) (UNIV:: 'n set)"
proof -
  let ?U = "UNIV:: 'n set"
  let ?PU = "{p. p permutes ?U}"
  let ?pp = "\<lambda>p. of_int (sign p) * prod (\<lambda>i. A$i$p i) (UNIV :: 'n set)"
  have fU: "finite ?U"
    by simp
  have id0: "{id} \<subseteq> ?PU"
    by (auto simp: permutes_id)
  have p0: "\<forall>p \<in> ?PU - {id}. ?pp p = 0"
  proof
    fix p
    assume "p \<in> ?PU - {id}"
    then obtain i where i: "p i > i"
      by clarify (meson leI permutes_natset_le)
    from ld[OF i] have "\<exists>i \<in> ?U. A$i$p i = 0"
      by blast
    with prod_zero[OF fU] show "?pp p = 0"
      by force
  qed
  from sum.mono_neutral_cong_left[OF finite_permutations[OF fU] id0 p0] show ?thesis
    unfolding det_def by (simp add: sign_id)
qed

lemma  det_upperdiagonal:
  fixes A :: "'a::comm_ring_1^'n::{finite,wellorder}^'n::{finite,wellorder}"
  assumes ld: "\<And>i j. i > j \<Longrightarrow> A$i$j = 0"
  shows "det A = prod (\<lambda>i. A$i$i) (UNIV:: 'n set)"
proof -
  let ?U = "UNIV:: 'n set"
  let ?PU = "{p. p permutes ?U}"
  let ?pp = "(\<lambda>p. of_int (sign p) * prod (\<lambda>i. A$i$p i) (UNIV :: 'n set))"
  have fU: "finite ?U"
    by simp
  have id0: "{id} \<subseteq> ?PU"
    by (auto simp: permutes_id)
  have p0: "\<forall>p \<in> ?PU -{id}. ?pp p = 0"
  proof
    fix p
    assume p: "p \<in> ?PU - {id}"
    then obtain i where i: "p i < i"
      by clarify (meson leI permutes_natset_ge)
    from ld[OF i] have "\<exists>i \<in> ?U. A$i$p i = 0"
      by blast
    with prod_zero[OF fU]  show "?pp p = 0"
      by force
  qed
  from sum.mono_neutral_cong_left[OF finite_permutations[OF fU] id0 p0] show ?thesis
    unfolding det_def by (simp add: sign_id)
qed

proposition  det_diagonal:
  fixes A :: "'a::comm_ring_1^'n^'n"
  assumes ld: "\<And>i j. i \<noteq> j \<Longrightarrow> A$i$j = 0"
  shows "det A = prod (\<lambda>i. A$i$i) (UNIV::'n set)"
proof -
  let ?U = "UNIV:: 'n set"
  let ?PU = "{p. p permutes ?U}"
  let ?pp = "\<lambda>p. of_int (sign p) * prod (\<lambda>i. A$i$p i) (UNIV :: 'n set)"
  have fU: "finite ?U" by simp
  from finite_permutations[OF fU] have fPU: "finite ?PU" .
  have id0: "{id} \<subseteq> ?PU"
    by (auto simp: permutes_id)
  have p0: "\<forall>p \<in> ?PU - {id}. ?pp p = 0"
  proof
    fix p
    assume p: "p \<in> ?PU - {id}"
    then obtain i where i: "p i \<noteq> i"
      by fastforce
    with ld have "\<exists>i \<in> ?U. A$i$p i = 0"
      by (metis UNIV_I)
    with prod_zero [OF fU] show "?pp p = 0"
      by force
  qed
  from sum.mono_neutral_cong_left[OF fPU id0 p0] show ?thesis
    unfolding det_def by (simp add: sign_id)
qed

lemma  det_I [simp]: "det (mat 1 :: 'a::comm_ring_1^'n^'n) = 1"
  by (simp add: det_diagonal mat_def)

lemma  det_0 [simp]: "det (mat 0 :: 'a::comm_ring_1^'n^'n) = 0"
  by (simp add: det_def prod_zero power_0_left)

lemma  det_permute_rows:
  fixes A :: "'a::comm_ring_1^'n^'n"
  assumes p: "p permutes (UNIV :: 'n::finite set)"
  shows "det (\<chi> i. A$p i :: 'a^'n^'n) = of_int (sign p) * det A"
proof -
  let ?U = "UNIV :: 'n set"
  let ?PU = "{p. p permutes ?U}"
  have *: "(\<Sum>q\<in>?PU. of_int (sign (q \<circ> p)) * (\<Prod>i\<in>?U. A $ p i $ (q \<circ> p) i)) =
           (\<Sum>n\<in>?PU. of_int (sign p) * of_int (sign n) * (\<Prod>i\<in>?U. A $ i $ n i))"
  proof (rule sum.cong)
    fix q
    assume qPU: "q \<in> ?PU"
    have fU: "finite ?U"
      by simp
    from qPU have q: "q permutes ?U"
      by blast
    have "prod (\<lambda>i. A$p i$ (q \<circ> p) i) ?U = prod ((\<lambda>i. A$p i$(q \<circ> p) i) \<circ> inv p) ?U"
      by (simp only: prod.permute[OF permutes_inv[OF p], symmetric])
    also have "\<dots> = prod (\<lambda>i. A $ (p \<circ> inv p) i $ (q \<circ> (p \<circ> inv p)) i) ?U"
      by (simp only: o_def)
    also have "\<dots> = prod (\<lambda>i. A$i$q i) ?U"
      by (simp only: o_def permutes_inverses[OF p])
    finally have thp: "prod (\<lambda>i. A$p i$ (q \<circ> p) i) ?U = prod (\<lambda>i. A$i$q i) ?U"
      by blast
    from p q have pp: "permutation p" and qp: "permutation q"
      by (metis fU permutation_permutes)+
    show "of_int (sign (q \<circ> p)) * prod (\<lambda>i. A$ p i$ (q \<circ> p) i) ?U =
          of_int (sign p) * of_int (sign q) * prod (\<lambda>i. A$i$q i) ?U"
      by (simp only: thp sign_compose[OF qp pp] mult.commute of_int_mult)
  qed auto
  show ?thesis
    apply (simp add: det_def sum_distrib_left mult.assoc[symmetric])
    apply (subst sum_permutations_compose_right[OF p])
    apply (rule *)
    done
qed

lemma  det_permute_columns:
  fixes A :: "'a::comm_ring_1^'n^'n"
  assumes p: "p permutes (UNIV :: 'n set)"
  shows "det(\<chi> i j. A$i$ p j :: 'a^'n^'n) = of_int (sign p) * det A"
proof -
  let ?Ap = "\<chi> i j. A$i$ p j :: 'a^'n^'n"
  let ?At = "transpose A"
  have "of_int (sign p) * det A = det (transpose (\<chi> i. transpose A $ p i))"
    unfolding det_permute_rows[OF p, of ?At] det_transpose ..
  moreover
  have "?Ap = transpose (\<chi> i. transpose A $ p i)"
    by (simp add: transpose_def vec_eq_iff)
  ultimately show ?thesis
    by simp
qed

lemma  det_identical_columns:
  fixes A :: "'a::comm_ring_1^'n^'n"
  assumes jk: "j \<noteq> k"
    and r: "column j A = column k A"
  shows "det A = 0"
proof -
  let ?U="UNIV::'n set"
  let ?t_jk="Transposition.transpose j k"
  let ?PU="{p. p permutes ?U}"
  let ?S1="{p. p\<in>?PU \<and> evenperm p}"
  let ?S2="{(?t_jk \<circ> p) |p. p \<in>?S1}"
  let ?f="\<lambda>p. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i)"
  let ?g="\<lambda>p. ?t_jk \<circ> p"
  have g_S1: "?S2 = ?g` ?S1" by auto
  have inj_g: "inj_on ?g ?S1"
  proof (unfold inj_on_def, auto)
    fix x y assume x: "x permutes ?U" and even_x: "evenperm x"
      and y: "y permutes ?U" and even_y: "evenperm y" and eq: "?t_jk \<circ> x = ?t_jk \<circ> y"
    show "x = y" by (metis (hide_lams, no_types) comp_assoc eq id_comp swap_id_idempotent)
  qed
  have tjk_permutes: "?t_jk permutes ?U"
    by (auto simp add: permutes_def dest: transpose_eq_imp_eq) (meson transpose_involutory)
  have tjk_eq: "\<forall>i l. A $ i $ ?t_jk l  =  A $ i $ l"
    using r jk
    unfolding column_def vec_eq_iff by (simp add: Transposition.transpose_def) 
  have sign_tjk: "sign ?t_jk = -1" using sign_swap_id[of j k] jk by auto
  {fix x
    assume x: "x\<in> ?S1"
    have "sign (?t_jk \<circ> x) = sign (?t_jk) * sign x"
      by (metis (lifting) finite_class.finite_UNIV mem_Collect_eq
          permutation_permutes permutation_swap_id sign_compose x)
    also have "\<dots> = - sign x" using sign_tjk by simp
    also have "\<dots> \<noteq> sign x" unfolding sign_def by simp
    finally have "sign (?t_jk \<circ> x) \<noteq> sign x" and "(?t_jk \<circ> x) \<in> ?S2"
      using x by force+
  }
  hence disjoint: "?S1 \<inter> ?S2 = {}"
    by (force simp: sign_def)
  have PU_decomposition: "?PU = ?S1 \<union> ?S2"
  proof (auto)
    fix x
    assume x: "x permutes ?U" and "\<forall>p. p permutes ?U \<longrightarrow> x = Transposition.transpose j k \<circ> p \<longrightarrow> \<not> evenperm p"
    then obtain p where p: "p permutes UNIV" and x_eq: "x = Transposition.transpose j k \<circ> p"
      and odd_p: "\<not> evenperm p"
      by (metis (mono_tags) id_o o_assoc permutes_compose swap_id_idempotent tjk_permutes)
    thus "evenperm x"
      by (meson evenperm_comp evenperm_swap finite_class.finite_UNIV
          jk permutation_permutes permutation_swap_id)
  next
    fix p assume p: "p permutes ?U"
    show "Transposition.transpose j k \<circ> p permutes UNIV" by (metis p permutes_compose tjk_permutes)
  qed
  have "sum ?f ?S2 = sum ((\<lambda>p. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i))
  \<circ> (\<circ>) (Transposition.transpose j k)) {p \<in> {p. p permutes UNIV}. evenperm p}"
    unfolding g_S1 by (rule sum.reindex[OF inj_g])
  also have "\<dots> = sum (\<lambda>p. of_int (sign (?t_jk \<circ> p)) * (\<Prod>i\<in>UNIV. A $ i $ p i)) ?S1"
    unfolding o_def by (rule sum.cong, auto simp: tjk_eq)
  also have "\<dots> = sum (\<lambda>p. - ?f p) ?S1"
  proof (rule sum.cong, auto)
    fix x assume x: "x permutes ?U"
      and even_x: "evenperm x"
    hence perm_x: "permutation x" and perm_tjk: "permutation ?t_jk"
      using permutation_permutes[of x] permutation_permutes[of ?t_jk] permutation_swap_id
      by (metis finite_code)+
    have "(sign (?t_jk \<circ> x)) = - (sign x)"
      unfolding sign_compose[OF perm_tjk perm_x] sign_tjk by auto
    thus "of_int (sign (?t_jk \<circ> x)) * (\<Prod>i\<in>UNIV. A $ i $ x i)
      = - (of_int (sign x) * (\<Prod>i\<in>UNIV. A $ i $ x i))"
      by auto
  qed
  also have "\<dots>= - sum ?f ?S1" unfolding sum_negf ..
  finally have *: "sum ?f ?S2 = - sum ?f ?S1" .
  have "det A = (\<Sum>p | p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. A $ i $ p i))"
    unfolding det_def ..
  also have "\<dots>= sum ?f ?S1 + sum ?f ?S2"
    by (subst PU_decomposition, rule sum.union_disjoint[OF _ _ disjoint], auto)
  also have "\<dots>= sum ?f ?S1 - sum ?f ?S1 " unfolding * by auto
  also have "\<dots>= 0" by simp
  finally show "det A = 0" by simp
qed

lemma  det_identical_rows:
  fixes A :: "'a::comm_ring_1^'n^'n"
  assumes ij: "i \<noteq> j" and r: "row i A = row j A"
  shows "det A = 0"
  by (metis column_transpose det_identical_columns det_transpose ij r)

lemma  det_zero_row:
  fixes A :: "'a::{idom, ring_char_0}^'n^'n" and F :: "'b::{field}^'m^'m"
  shows "row i A = 0 \<Longrightarrow> det A = 0" and "row j F = 0 \<Longrightarrow> det F = 0"
  by (force simp: row_def det_def vec_eq_iff sign_nz intro!: sum.neutral)+

lemma  det_zero_column:
  fixes A :: "'a::{idom, ring_char_0}^'n^'n" and F :: "'b::{field}^'m^'m"
  shows "column i A = 0 \<Longrightarrow> det A = 0" and "column j F = 0 \<Longrightarrow> det F = 0"
  unfolding atomize_conj atomize_imp
  by (metis det_transpose det_zero_row row_transpose)

lemma  det_row_add:
  fixes a b c :: "'n::finite \<Rightarrow> _ ^ 'n"
  shows "det((\<chi> i. if i = k then a i + b i else c i)::'a::comm_ring_1^'n^'n) =
    det((\<chi> i. if i = k then a i else c i)::'a::comm_ring_1^'n^'n) +
    det((\<chi> i. if i = k then b i else c i)::'a::comm_ring_1^'n^'n)"
  unfolding det_def vec_lambda_beta sum.distrib[symmetric]
proof (rule sum.cong)
  let ?U = "UNIV :: 'n set"
  let ?pU = "{p. p permutes ?U}"
  let ?f = "(\<lambda>i. if i = k then a i + b i else c i)::'n \<Rightarrow> 'a::comm_ring_1^'n"
  let ?g = "(\<lambda> i. if i = k then a i else c i)::'n \<Rightarrow> 'a::comm_ring_1^'n"
  let ?h = "(\<lambda> i. if i = k then b i else c i)::'n \<Rightarrow> 'a::comm_ring_1^'n"
  fix p
  assume p: "p \<in> ?pU"
  let ?Uk = "?U - {k}"
  from p have pU: "p permutes ?U"
    by blast
  have kU: "?U = insert k ?Uk"
    by blast
  have eq: "prod (\<lambda>i. ?f i $ p i) ?Uk = prod (\<lambda>i. ?g i $ p i) ?Uk"
           "prod (\<lambda>i. ?f i $ p i) ?Uk = prod (\<lambda>i. ?h i $ p i) ?Uk"
    by auto
  have Uk: "finite ?Uk" "k \<notin> ?Uk"
    by auto
  have "prod (\<lambda>i. ?f i $ p i) ?U = prod (\<lambda>i. ?f i $ p i) (insert k ?Uk)"
    unfolding kU[symmetric] ..
  also have "\<dots> = ?f k $ p k * prod (\<lambda>i. ?f i $ p i) ?Uk"
    by (rule prod.insert) auto
  also have "\<dots> = (a k $ p k * prod (\<lambda>i. ?f i $ p i) ?Uk) + (b k$ p k * prod (\<lambda>i. ?f i $ p i) ?Uk)"
    by (simp add: field_simps)
  also have "\<dots> = (a k $ p k * prod (\<lambda>i. ?g i $ p i) ?Uk) + (b k$ p k * prod (\<lambda>i. ?h i $ p i) ?Uk)"
    by (metis eq)
  also have "\<dots> = prod (\<lambda>i. ?g i $ p i) (insert k ?Uk) + prod (\<lambda>i. ?h i $ p i) (insert k ?Uk)"
    unfolding  prod.insert[OF Uk] by simp
  finally have "prod (\<lambda>i. ?f i $ p i) ?U = prod (\<lambda>i. ?g i $ p i) ?U + prod (\<lambda>i. ?h i $ p i) ?U"
    unfolding kU[symmetric] .
  then show "of_int (sign p) * prod (\<lambda>i. ?f i $ p i) ?U =
    of_int (sign p) * prod (\<lambda>i. ?g i $ p i) ?U + of_int (sign p) * prod (\<lambda>i. ?h i $ p i) ?U"
    by (simp add: field_simps)
qed auto

lemma  det_row_mul:
  fixes a b :: "'n::finite \<Rightarrow> _ ^ 'n"
  shows "det((\<chi> i. if i = k then c *s a i else b i)::'a::comm_ring_1^'n^'n) =
    c * det((\<chi> i. if i = k then a i else b i)::'a::comm_ring_1^'n^'n)"
  unfolding det_def vec_lambda_beta sum_distrib_left
proof (rule sum.cong)
  let ?U = "UNIV :: 'n set"
  let ?pU = "{p. p permutes ?U}"
  let ?f = "(\<lambda>i. if i = k then c*s a i else b i)::'n \<Rightarrow> 'a::comm_ring_1^'n"
  let ?g = "(\<lambda> i. if i = k then a i else b i)::'n \<Rightarrow> 'a::comm_ring_1^'n"
  fix p
  assume p: "p \<in> ?pU"
  let ?Uk = "?U - {k}"
  from p have pU: "p permutes ?U"
    by blast
  have kU: "?U = insert k ?Uk"
    by blast
  have eq: "prod (\<lambda>i. ?f i $ p i) ?Uk = prod (\<lambda>i. ?g i $ p i) ?Uk"
    by auto
  have Uk: "finite ?Uk" "k \<notin> ?Uk"
    by auto
  have "prod (\<lambda>i. ?f i $ p i) ?U = prod (\<lambda>i. ?f i $ p i) (insert k ?Uk)"
    unfolding kU[symmetric] ..
  also have "\<dots> = ?f k $ p k  * prod (\<lambda>i. ?f i $ p i) ?Uk"
    by (rule prod.insert) auto
  also have "\<dots> = (c*s a k) $ p k * prod (\<lambda>i. ?f i $ p i) ?Uk"
    by (simp add: field_simps)
  also have "\<dots> = c* (a k $ p k * prod (\<lambda>i. ?g i $ p i) ?Uk)"
    unfolding eq by (simp add: ac_simps)
  also have "\<dots> = c* (prod (\<lambda>i. ?g i $ p i) (insert k ?Uk))"
    unfolding prod.insert[OF Uk] by simp
  finally have "prod (\<lambda>i. ?f i $ p i) ?U = c* (prod (\<lambda>i. ?g i $ p i) ?U)"
    unfolding kU[symmetric] .
  then show "of_int (sign p) * prod (\<lambda>i. ?f i $ p i) ?U = c * (of_int (sign p) * prod (\<lambda>i. ?g i $ p i) ?U)"
    by (simp add: field_simps)
qed auto

lemma  det_row_0:
  fixes b :: "'n::finite \<Rightarrow> _ ^ 'n"
  shows "det((\<chi> i. if i = k then 0 else b i)::'a::comm_ring_1^'n^'n) = 0"
  using det_row_mul[of k 0 "\<lambda>i. 1" b]
  apply simp
  apply (simp only: vector_smult_lzero)
  done

lemma  det_row_operation:
  fixes A :: "'a::{comm_ring_1}^'n^'n"
  assumes ij: "i \<noteq> j"
  shows "det (\<chi> k. if k = i then row i A + c *s row j A else row k A) = det A"
proof -
  let ?Z = "(\<chi> k. if k = i then row j A else row k A) :: 'a ^'n^'n"
  have th: "row i ?Z = row j ?Z" by (vector row_def)
  have th2: "((\<chi> k. if k = i then row i A else row k A) :: 'a^'n^'n) = A"
    by (vector row_def)
  show ?thesis
    unfolding det_row_add [of i] det_row_mul[of i] det_identical_rows[OF ij th] th2
    by simp
qed

lemma  det_row_span:
  fixes A :: "'a::{field}^'n^'n"
  assumes x: "x \<in> vec.span {row j A |j. j \<noteq> i}"
  shows "det (\<chi> k. if k = i then row i A + x else row k A) = det A"
  using x
proof (induction rule: vec.span_induct_alt)
  case base
  have "(if k = i then row i A + 0 else row k A) = row k A" for k
    by simp
  then show ?case
    by (simp add: row_def)
next
  case (step c z y)
  then obtain j where j: "z = row j A" "i \<noteq> j"
    by blast
  let ?w = "row i A + y"
  have th0: "row i A + (c*s z + y) = ?w + c*s z"
    by vector
  let ?d = "\<lambda>x. det (\<chi> k. if k = i then x else row k A)"
  have thz: "?d z = 0"
    apply (rule det_identical_rows[OF j(2)])
    using j
    apply (vector row_def)
    done
  have "?d (row i A + (c*s z + y)) = ?d (?w + c*s z)"
    unfolding th0 ..
  then have "?d (row i A + (c*s z + y)) = det A"
    unfolding thz step.IH det_row_mul[of i] det_row_add[of i] by simp
  then show ?case
    unfolding scalar_mult_eq_scaleR .
qed

lemma  matrix_id [simp]: "det (matrix id) = 1"
  by (simp add: matrix_id_mat_1)

proposition  det_matrix_scaleR [simp]: "det (matrix (((*\<^sub>R) r)) :: real^'n^'n) = r ^ CARD('n::finite)"
  apply (subst det_diagonal)
   apply (auto simp: matrix_def mat_def)
  apply (simp add: cart_eq_inner_axis inner_axis_axis)
  done

text \<open>
  May as well do this, though it's a bit unsatisfactory since it ignores
  exact duplicates by considering the rows/columns as a set.
\<close>

lemma  det_dependent_rows:
  fixes A:: "'a::{field}^'n^'n"
  assumes d: "vec.dependent (rows A)"
  shows "det A = 0"
proof -
  let ?U = "UNIV :: 'n set"
  from d obtain i where i: "row i A \<in> vec.span (rows A - {row i A})"
    unfolding vec.dependent_def rows_def by blast
  show ?thesis
  proof (cases "\<forall>i j. i \<noteq> j \<longrightarrow> row i A \<noteq> row j A")
    case True
    with i have "vec.span (rows A - {row i A}) \<subseteq> vec.span {row j A |j. j \<noteq> i}"
      by (auto simp: rows_def intro!: vec.span_mono)
    then have "- row i A \<in> vec.span {row j A|j. j \<noteq> i}"
      by (meson i subsetCE vec.span_neg)
    from det_row_span[OF this]
    have "det A = det (\<chi> k. if k = i then 0 *s 1 else row k A)"
      unfolding right_minus vector_smult_lzero ..
    with det_row_mul[of i 0 "\<lambda>i. 1"]
    show ?thesis by simp
  next
    case False
    then obtain j k where jk: "j \<noteq> k" "row j A = row k A"
      by auto
    from det_identical_rows[OF jk] show ?thesis .
  qed
qed

lemma  det_dependent_columns:
  assumes d: "vec.dependent (columns (A::real^'n^'n))"
  shows "det A = 0"
  by (metis d det_dependent_rows rows_transpose det_transpose)

text \<open>Multilinearity and the multiplication formula\<close>

lemma  Cart_lambda_cong: "(\<And>x. f x = g x) \<Longrightarrow> (vec_lambda f::'a^'n) = (vec_lambda g :: 'a^'n)"
  by auto

lemma  det_linear_row_sum:
  assumes fS: "finite S"
  shows "det ((\<chi> i. if i = k then sum (a i) S else c i)::'a::comm_ring_1^'n^'n) =
    sum (\<lambda>j. det ((\<chi> i. if i = k then a  i j else c i)::'a^'n^'n)) S"
  using fS  by (induct rule: finite_induct; simp add: det_row_0 det_row_add cong: if_cong)

lemma  finite_bounded_functions:
  assumes fS: "finite S"
  shows "finite {f. (\<forall>i \<in> {1.. (k::nat)}. f i \<in> S) \<and> (\<forall>i. i \<notin> {1 .. k} \<longrightarrow> f i = i)}"
proof (induct k)
  case 0
  have *: "{f. \<forall>i. f i = i} = {id}"
    by auto
  show ?case
    by (auto simp: *)
next
  case (Suc k)
  let ?f = "\<lambda>(y::nat,g) i. if i = Suc k then y else g i"
  let ?S = "?f ` (S \<times> {f. (\<forall>i\<in>{1..k}. f i \<in> S) \<and> (\<forall>i. i \<notin> {1..k} \<longrightarrow> f i = i)})"
  have "?S = {f. (\<forall>i\<in>{1.. Suc k}. f i \<in> S) \<and> (\<forall>i. i \<notin> {1.. Suc k} \<longrightarrow> f i = i)}"
    apply (auto simp: image_iff)
    apply (rename_tac f)
    apply (rule_tac x="f (Suc k)" in bexI)
    apply (rule_tac x = "\<lambda>i. if i = Suc k then i else f i" in exI, auto)
    done
  with finite_imageI[OF finite_cartesian_product[OF fS Suc.hyps(1)], of ?f]
  show ?case
    by metis
qed


lemma  det_linear_rows_sum_lemma:
  assumes fS: "finite S"
    and fT: "finite T"
  shows "det ((\<chi> i. if i \<in> T then sum (a i) S else c i):: 'a::comm_ring_1^'n^'n) =
    sum (\<lambda>f. det((\<chi> i. if i \<in> T then a i (f i) else c i)::'a^'n^'n))
      {f. (\<forall>i \<in> T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = i)}"
  using fT
proof (induct T arbitrary: a c set: finite)
  case empty
  have th0: "\<And>x y. (\<chi> i. if i \<in> {} then x i else y i) = (\<chi> i. y i)"
    by vector
  from empty.prems show ?case
    unfolding th0 by (simp add: eq_id_iff)
next
  case (insert z T a c)
  let ?F = "\<lambda>T. {f. (\<forall>i \<in> T. f i \<in> S) \<and> (\<forall>i. i \<notin> T \<longrightarrow> f i = i)}"
  let ?h = "\<lambda>(y,g) i. if i = z then y else g i"
  let ?k = "\<lambda>h. (h(z),(\<lambda>i. if i = z then i else h i))"
  let ?s = "\<lambda> k a c f. det((\<chi> i. if i \<in> T then a i (f i) else c i)::'a^'n^'n)"
  let ?c = "\<lambda>j i. if i = z then a i j else c i"
  have thif: "\<And>a b c d. (if a \<or> b then c else d) = (if a then c else if b then c else d)"
    by simp
  have thif2: "\<And>a b c d e. (if a then b else if c then d else e) =
     (if c then (if a then b else d) else (if a then b else e))"
    by simp
  from \<open>z \<notin> T\<close> have nz: "\<And>i. i \<in> T \<Longrightarrow> i \<noteq> z"
    by auto
  have "det (\<chi> i. if i \<in> insert z T then sum (a i) S else c i) =
    det (\<chi> i. if i = z then sum (a i) S else if i \<in> T then sum (a i) S else c i)"
    unfolding insert_iff thif ..
  also have "\<dots> = (\<Sum>j\<in>S. det (\<chi> i. if i \<in> T then sum (a i) S else if i = z then a i j else c i))"
    unfolding det_linear_row_sum[OF fS]
    by (subst thif2) (simp add: nz cong: if_cong)
  finally have tha:
    "det (\<chi> i. if i \<in> insert z T then sum (a i) S else c i) =
     (\<Sum>(j, f)\<in>S \<times> ?F T. det (\<chi> i. if i \<in> T then a i (f i)
                                else if i = z then a i j
                                else c i))"
    unfolding insert.hyps unfolding sum.cartesian_product by blast
  show ?case unfolding tha
    using \<open>z \<notin> T\<close>
    by (intro sum.reindex_bij_witness[where i="?k" and j="?h"])
       (auto intro!: cong[OF refl[of det]] simp: vec_eq_iff)
qed

lemma  det_linear_rows_sum:
  fixes S :: "'n::finite set"
  assumes fS: "finite S"
  shows "det (\<chi> i. sum (a i) S) =
    sum (\<lambda>f. det (\<chi> i. a i (f i) :: 'a::comm_ring_1 ^ 'n^'n)) {f. \<forall>i. f i \<in> S}"
proof -
  have th0: "\<And>x y. ((\<chi> i. if i \<in> (UNIV:: 'n set) then x i else y i) :: 'a^'n^'n) = (\<chi> i. x i)"
    by vector
  from det_linear_rows_sum_lemma[OF fS, of "UNIV :: 'n set" a, unfolded th0, OF finite]
  show ?thesis by simp
qed

lemma  matrix_mul_sum_alt:
  fixes A B :: "'a::comm_ring_1^'n^'n"
  shows "A ** B = (\<chi> i. sum (\<lambda>k. A$i$k *s B $ k) (UNIV :: 'n set))"
  by (vector matrix_matrix_mult_def sum_component)

lemma  det_rows_mul:
  "det((\<chi> i. c i *s a i)::'a::comm_ring_1^'n^'n) =
    prod (\<lambda>i. c i) (UNIV:: 'n set) * det((\<chi> i. a i)::'a^'n^'n)"
proof (simp add: det_def sum_distrib_left cong add: prod.cong, rule sum.cong)
  let ?U = "UNIV :: 'n set"
  let ?PU = "{p. p permutes ?U}"
  fix p
  assume pU: "p \<in> ?PU"
  let ?s = "of_int (sign p)"
  from pU have p: "p permutes ?U"
    by blast
  have "prod (\<lambda>i. c i * a i $ p i) ?U = prod c ?U * prod (\<lambda>i. a i $ p i) ?U"
    unfolding prod.distrib ..
  then show "?s * (\<Prod>xa\<in>?U. c xa * a xa $ p xa) =
    prod c ?U * (?s* (\<Prod>xa\<in>?U. a xa $ p xa))"
    by (simp add: field_simps)
qed rule

proposition  det_mul:
  fixes A B :: "'a::comm_ring_1^'n^'n"
  shows "det (A ** B) = det A * det B"
proof -
  let ?U = "UNIV :: 'n set"
  let ?F = "{f. (\<forall>i \<in> ?U. f i \<in> ?U) \<and> (\<forall>i. i \<notin> ?U \<longrightarrow> f i = i)}"
  let ?PU = "{p. p permutes ?U}"
  have "p \<in> ?F" if "p permutes ?U" for p
    by simp
  then have PUF: "?PU \<subseteq> ?F" by blast
  {
    fix f
    assume fPU: "f \<in> ?F - ?PU"
    have fUU: "f ` ?U \<subseteq> ?U"
      using fPU by auto
    from fPU have f: "\<forall>i \<in> ?U. f i \<in> ?U" "\<forall>i. i \<notin> ?U \<longrightarrow> f i = i" "\<not>(\<forall>y. \<exists>!x. f x = y)"
      unfolding permutes_def by auto

    let ?A = "(\<chi> i. A$i$f i *s B$f i) :: 'a^'n^'n"
    let ?B = "(\<chi> i. B$f i) :: 'a^'n^'n"
    {
      assume fni: "\<not> inj_on f ?U"
      then obtain i j where ij: "f i = f j" "i \<noteq> j"
        unfolding inj_on_def by blast
      then have "row i ?B = row j ?B"
        by (vector row_def)
      with det_identical_rows[OF ij(2)]
      have "det (\<chi> i. A$i$f i *s B$f i) = 0"
        unfolding det_rows_mul by force
    }
    moreover
    {
      assume fi: "inj_on f ?U"
      from f fi have fith: "\<And>i j. f i = f j \<Longrightarrow> i = j"
        unfolding inj_on_def by metis
      note fs = fi[unfolded surjective_iff_injective_gen[OF finite finite refl fUU, symmetric]]
      have "\<exists>!x. f x = y" for y
        using fith fs by blast
      with f(3) have "det (\<chi> i. A$i$f i *s B$f i) = 0"
        by blast
    }
    ultimately have "det (\<chi> i. A$i$f i *s B$f i) = 0"
      by blast
  }
  then have zth: "\<forall> f\<in> ?F - ?PU. det (\<chi> i. A$i$f i *s B$f i) = 0"
    by simp
  {
    fix p
    assume pU: "p \<in> ?PU"
    from pU have p: "p permutes ?U"
      by blast
    let ?s = "\<lambda>p. of_int (sign p)"
    let ?f = "\<lambda>q. ?s p * (\<Prod>i\<in> ?U. A $ i $ p i) * (?s q * (\<Prod>i\<in> ?U. B $ i $ q i))"
    have "(sum (\<lambda>q. ?s q *
        (\<Prod>i\<in> ?U. (\<chi> i. A $ i $ p i *s B $ p i :: 'a^'n^'n) $ i $ q i)) ?PU) =
      (sum (\<lambda>q. ?s p * (\<Prod>i\<in> ?U. A $ i $ p i) * (?s q * (\<Prod>i\<in> ?U. B $ i $ q i))) ?PU)"
      unfolding sum_permutations_compose_right[OF permutes_inv[OF p], of ?f]
    proof (rule sum.cong)
      fix q
      assume qU: "q \<in> ?PU"
      then have q: "q permutes ?U"
        by blast
      from p q have pp: "permutation p" and pq: "permutation q"
        unfolding permutation_permutes by auto
      have th00: "of_int (sign p) * of_int (sign p) = (1::'a)"
        "\<And>a. of_int (sign p) * (of_int (sign p) * a) = a"
        unfolding mult.assoc[symmetric]
        unfolding of_int_mult[symmetric]
        by (simp_all add: sign_idempotent)
      have ths: "?s q = ?s p * ?s (q \<circ> inv p)"
        using pp pq permutation_inverse[OF pp] sign_inverse[OF pp]
        by (simp add: th00 ac_simps sign_idempotent sign_compose)
      have th001: "prod (\<lambda>i. B$i$ q (inv p i)) ?U = prod ((\<lambda>i. B$i$ q (inv p i)) \<circ> p) ?U"
        by (rule prod.permute[OF p])
      have thp: "prod (\<lambda>i. (\<chi> i. A$i$p i *s B$p i :: 'a^'n^'n) $i $ q i) ?U =
        prod (\<lambda>i. A$i$p i) ?U * prod (\<lambda>i. B$i$ q (inv p i)) ?U"
        unfolding th001 prod.distrib[symmetric] o_def permutes_inverses[OF p]
        apply (rule prod.cong[OF refl])
        using permutes_in_image[OF q]
        apply vector
        done
      show "?s q * prod (\<lambda>i. (((\<chi> i. A$i$p i *s B$p i) :: 'a^'n^'n)$i$q i)) ?U =
        ?s p * (prod (\<lambda>i. A$i$p i) ?U) * (?s (q \<circ> inv p) * prod (\<lambda>i. B$i$(q \<circ> inv p) i) ?U)"
        using ths thp pp pq permutation_inverse[OF pp] sign_inverse[OF pp]
        by (simp add: sign_nz th00 field_simps sign_idempotent sign_compose)
    qed rule
  }
  then have th2: "sum (\<lambda>f. det (\<chi> i. A$i$f i *s B$f i)) ?PU = det A * det B"
    unfolding det_def sum_product
    by (rule sum.cong [OF refl])
  have "det (A**B) = sum (\<lambda>f.  det (\<chi> i. A $ i $ f i *s B $ f i)) ?F"
    unfolding matrix_mul_sum_alt det_linear_rows_sum[OF finite]
    by simp
  also have "\<dots> = sum (\<lambda>f. det (\<chi> i. A$i$f i *s B$f i)) ?PU"
    using sum.mono_neutral_cong_left[OF finite PUF zth, symmetric]
    unfolding det_rows_mul by auto
  finally show ?thesis unfolding th2 .
qed


subsection \<open>Relation to invertibility\<close>

proposition  invertible_det_nz:
  fixes A::"'a::{field}^'n^'n"
  shows "invertible A \<longleftrightarrow> det A \<noteq> 0"
proof (cases "invertible A")
  case True
  then obtain B :: "'a^'n^'n" where B: "A ** B = mat 1"
    unfolding invertible_right_inverse by blast
  then have "det (A ** B) = det (mat 1 :: 'a^'n^'n)"
    by simp
  then show ?thesis
    by (metis True det_I det_mul mult_zero_left one_neq_zero)
next
  case False
  let ?U = "UNIV :: 'n set"
  have fU: "finite ?U"
    by simp
  from False obtain c i where c: "sum (\<lambda>i. c i *s row i A) ?U = 0" and iU: "i \<in> ?U" and ci: "c i \<noteq> 0"
    unfolding invertible_right_inverse matrix_right_invertible_independent_rows
    by blast
  have thr0: "- row i A = sum (\<lambda>j. (1/ c i) *s (c j *s row j A)) (?U - {i})"
    unfolding sum_cmul  using c ci
    by (auto simp: sum.remove[OF fU iU] eq_vector_fraction_iff add_eq_0_iff)
  have thr: "- row i A \<in> vec.span {row j A| j. j \<noteq> i}"
    unfolding thr0 by (auto intro: vec.span_base vec.span_scale vec.span_sum)
  let ?B = "(\<chi> k. if k = i then 0 else row k A) :: 'a^'n^'n"
  have thrb: "row i ?B = 0" using iU by (vector row_def)
  have "det A = 0"
    unfolding det_row_span[OF thr, symmetric] right_minus
    unfolding det_zero_row(2)[OF thrb] ..
  then show ?thesis
    by (simp add: False)
qed


lemma  det_nz_iff_inj_gen:
  fixes f :: "'a::field^'n \<Rightarrow> 'a::field^'n"
  assumes "Vector_Spaces.linear (*s) (*s) f"
  shows "det (matrix f) \<noteq> 0 \<longleftrightarrow> inj f"
proof
  assume "det (matrix f) \<noteq> 0"
  then show "inj f"
    using assms invertible_det_nz inj_matrix_vector_mult by force
next
  assume "inj f"
  show "det (matrix f) \<noteq> 0"
    using vec.linear_injective_left_inverse [OF assms \<open>inj f\<close>]
    by (metis assms invertible_det_nz invertible_left_inverse matrix_compose_gen matrix_id_mat_1)
qed

lemma  det_nz_iff_inj:
  fixes f :: "real^'n \<Rightarrow> real^'n"
  assumes "linear f"
  shows "det (matrix f) \<noteq> 0 \<longleftrightarrow> inj f"
  using det_nz_iff_inj_gen[of f] assms
  unfolding linear_matrix_vector_mul_eq .

lemma  det_eq_0_rank:
  fixes A :: "real^'n^'n"
  shows "det A = 0 \<longleftrightarrow> rank A < CARD('n)"
  using invertible_det_nz [of A]
  by (auto simp: matrix_left_invertible_injective invertible_left_inverse less_rank_noninjective)

subsubsection\<^marker>\<open>tag important\<close>  \<open>Invertibility of matrices and corresponding linear functions\<close>

lemma  matrix_left_invertible_gen:
  fixes f :: "'a::field^'m \<Rightarrow> 'a::field^'n"
  assumes "Vector_Spaces.linear (*s) (*s) f"
  shows "((\<exists>B. B ** matrix f = mat 1) \<longleftrightarrow> (\<exists>g. Vector_Spaces.linear (*s) (*s) g \<and> g \<circ> f = id))"
proof safe
  fix B
  assume 1: "B ** matrix f = mat 1"
  show "\<exists>g. Vector_Spaces.linear (*s) (*s) g \<and> g \<circ> f = id"
  proof (intro exI conjI)
    show "Vector_Spaces.linear (*s) (*s) (\<lambda>y. B *v y)"
      by simp
    show "((*v) B) \<circ> f = id"
      unfolding o_def
      by (metis assms 1 eq_id_iff matrix_vector_mul(1) matrix_vector_mul_assoc matrix_vector_mul_lid)
  qed
next
  fix g
  assume "Vector_Spaces.linear (*s) (*s) g" "g \<circ> f = id"
  then have "matrix g ** matrix f = mat 1"
    by (metis assms matrix_compose_gen matrix_id_mat_1)
  then show "\<exists>B. B ** matrix f = mat 1" ..
qed

lemma  matrix_left_invertible:
  "linear f \<Longrightarrow> ((\<exists>B. B ** matrix f = mat 1) \<longleftrightarrow> (\<exists>g. linear g \<and> g \<circ> f = id))" for f::"real^'m \<Rightarrow> real^'n"
  using matrix_left_invertible_gen[of f]
  by (auto simp: linear_matrix_vector_mul_eq)

lemma  matrix_right_invertible_gen:
  fixes f :: "'a::field^'m \<Rightarrow> 'a^'n"
  assumes "Vector_Spaces.linear (*s) (*s) f"
  shows "((\<exists>B. matrix f ** B = mat 1) \<longleftrightarrow> (\<exists>g. Vector_Spaces.linear (*s) (*s) g \<and> f \<circ> g = id))"
proof safe
  fix B
  assume 1: "matrix f ** B = mat 1"
  show "\<exists>g. Vector_Spaces.linear (*s) (*s) g \<and> f \<circ> g = id"
  proof (intro exI conjI)
    show "Vector_Spaces.linear (*s) (*s) ((*v) B)"
      by simp
    show "f \<circ> (*v) B = id"
      using 1 assms comp_apply eq_id_iff vec.linear_id matrix_id_mat_1 matrix_vector_mul_assoc matrix_works
      by (metis (no_types, hide_lams))
  qed
next
  fix g
  assume "Vector_Spaces.linear (*s) (*s) g" and "f \<circ> g = id"
  then have "matrix f ** matrix g = mat 1"
    by (metis assms matrix_compose_gen matrix_id_mat_1)
  then show "\<exists>B. matrix f ** B = mat 1" ..
qed

lemma  matrix_right_invertible:
  "linear f \<Longrightarrow> ((\<exists>B. matrix f ** B = mat 1) \<longleftrightarrow> (\<exists>g. linear g \<and> f \<circ> g = id))" for f::"real^'m \<Rightarrow> real^'n"
  using matrix_right_invertible_gen[of f]
  by (auto simp: linear_matrix_vector_mul_eq)

lemma  matrix_invertible_gen:
  fixes f :: "'a::field^'m \<Rightarrow> 'a::field^'n"
  assumes "Vector_Spaces.linear (*s) (*s) f"
  shows  "invertible (matrix f) \<longleftrightarrow> (\<exists>g. Vector_Spaces.linear (*s) (*s) g \<and> f \<circ> g = id \<and> g \<circ> f = id)"
    (is "?lhs = ?rhs")
proof
  assume ?lhs then show ?rhs
    by (metis assms invertible_def left_right_inverse_eq matrix_left_invertible_gen matrix_right_invertible_gen)
next
  assume ?rhs then show ?lhs
    by (metis assms invertible_def matrix_compose_gen matrix_id_mat_1)
qed

lemma  matrix_invertible:
  "linear f \<Longrightarrow> invertible (matrix f) \<longleftrightarrow> (\<exists>g. linear g \<and> f \<circ> g = id \<and> g \<circ> f = id)"
  for f::"real^'m \<Rightarrow> real^'n"
  using matrix_invertible_gen[of f]
  by (auto simp: linear_matrix_vector_mul_eq)

lemma  invertible_eq_bij:
  fixes m :: "'a::field^'m^'n"
  shows "invertible m \<longleftrightarrow> bij ((*v) m)"
  using matrix_invertible_gen[OF matrix_vector_mul_linear_gen, of m, simplified matrix_of_matrix_vector_mul]
  by (metis bij_betw_def left_right_inverse_eq matrix_vector_mul_linear_gen o_bij
      vec.linear_injective_left_inverse vec.linear_surjective_right_inverse)


subsection \<open>Cramer's rule\<close>

lemma  cramer_lemma_transpose:
  fixes A:: "'a::{field}^'n^'n"
    and x :: "'a::{field}^'n"
  shows "det ((\<chi> i. if i = k then sum (\<lambda>i. x$i *s row i A) (UNIV::'n set)
                             else row i A)::'a::{field}^'n^'n) = x$k * det A"
  (is "?lhs = ?rhs")
proof -
  let ?U = "UNIV :: 'n set"
  let ?Uk = "?U - {k}"
  have U: "?U = insert k ?Uk"
    by blast
  have kUk: "k \<notin> ?Uk"
    by simp
  have th00: "\<And>k s. x$k *s row k A + s = (x$k - 1) *s row k A + row k A + s"
    by (vector field_simps)
  have th001: "\<And>f k . (\<lambda>x. if x = k then f k else f x) = f"
    by auto
  have "(\<chi> i. row i A) = A" by (vector row_def)
  then have thd1: "det (\<chi> i. row i A) = det A"
    by simp
  have thd0: "det (\<chi> i. if i = k then row k A + (\<Sum>i \<in> ?Uk. x $ i *s row i A) else row i A) = det A"
    by (force intro: det_row_span vec.span_sum vec.span_scale vec.span_base)
  show "?lhs = x$k * det A"
    apply (subst U)
    unfolding sum.insert[OF finite kUk]
    apply (subst th00)
    unfolding add.assoc
    apply (subst det_row_add)
    unfolding thd0
    unfolding det_row_mul
    unfolding th001[of k "\<lambda>i. row i A"]
    unfolding thd1
    apply (simp add: field_simps)
    done
qed

proposition  cramer_lemma:
  fixes A :: "'a::{field}^'n^'n"
  shows "det((\<chi> i j. if j = k then (A *v x)$i else A$i$j):: 'a::{field}^'n^'n) = x$k * det A"
proof -
  let ?U = "UNIV :: 'n set"
  have *: "\<And>c. sum (\<lambda>i. c i *s row i (transpose A)) ?U = sum (\<lambda>i. c i *s column i A) ?U"
    by (auto intro: sum.cong)
  show ?thesis
    unfolding matrix_mult_sum
    unfolding cramer_lemma_transpose[of k x "transpose A", unfolded det_transpose, symmetric]
    unfolding *[of "\<lambda>i. x$i"]
    apply (subst det_transpose[symmetric])
    apply (rule cong[OF refl[of det]])
    apply (vector transpose_def column_def row_def)
    done
qed

proposition  cramer:
  fixes A ::"'a::{field}^'n^'n"
  assumes d0: "det A \<noteq> 0"
  shows "A *v x = b \<longleftrightarrow> x = (\<chi> k. det(\<chi> i j. if j=k then b$i else A$i$j) / det A)"
proof -
  from d0 obtain B where B: "A ** B = mat 1" "B ** A = mat 1"
    unfolding invertible_det_nz[symmetric] invertible_def
    by blast
  have "(A ** B) *v b = b"
    by (simp add: B)
  then have "A *v (B *v b) = b"
    by (simp add: matrix_vector_mul_assoc)
  then have xe: "\<exists>x. A *v x = b"
    by blast
  {
    fix x
    assume x: "A *v x = b"
    have "x = (\<chi> k. det(\<chi> i j. if j=k then b$i else A$i$j) / det A)"
      unfolding x[symmetric]
      using d0 by (simp add: vec_eq_iff cramer_lemma field_simps)
  }
  with xe show ?thesis
    by auto
qed

lemma  det_1: "det (A::'a::comm_ring_1^1^1) = A$1$1"
  by (simp add: det_def sign_id)

lemma  det_2: "det (A::'a::comm_ring_1^2^2) = A$1$1 * A$2$2 - A$1$2 * A$2$1"
proof -
  have f12: "finite {2::2}" "1 \<notin> {2::2}" by auto
  show ?thesis
    unfolding det_def UNIV_2
    unfolding sum_over_permutations_insert[OF f12]
    unfolding permutes_sing
    by (simp add: sign_swap_id sign_id swap_id_eq)
qed

lemma  det_3:
  "det (A::'a::comm_ring_1^3^3) =
    A$1$1 * A$2$2 * A$3$3 +
    A$1$2 * A$2$3 * A$3$1 +
    A$1$3 * A$2$1 * A$3$2 -
    A$1$1 * A$2$3 * A$3$2 -
    A$1$2 * A$2$1 * A$3$3 -
    A$1$3 * A$2$2 * A$3$1"
proof -
  have f123: "finite {2::3, 3}" "1 \<notin> {2::3, 3}"
    by auto
  have f23: "finite {3::3}" "2 \<notin> {3::3}"
    by auto

  show ?thesis
    unfolding det_def UNIV_3
    unfolding sum_over_permutations_insert[OF f123]
    unfolding sum_over_permutations_insert[OF f23]
    unfolding permutes_sing
    by (simp add: sign_swap_id permutation_swap_id sign_compose sign_id swap_id_eq)
qed

proposition  det_orthogonal_matrix:
  fixes Q:: "'a::linordered_idom^'n^'n"
  assumes oQ: "orthogonal_matrix Q"
  shows "det Q = 1 \<or> det Q = - 1"
proof -
  have "Q ** transpose Q = mat 1"
    by (metis oQ orthogonal_matrix_def)
  then have "det (Q ** transpose Q) = det (mat 1:: 'a^'n^'n)"
    by simp
  then have "det Q * det Q = 1"
    by (simp add: det_mul)
  then show ?thesis
    by (simp add: square_eq_1_iff)
qed

proposition  orthogonal_transformation_det [simp]:
  fixes f :: "real^'n \<Rightarrow> real^'n"
  shows "orthogonal_transformation f \<Longrightarrow> \<bar>det (matrix f)\<bar> = 1"
  using det_orthogonal_matrix orthogonal_transformation_matrix by fastforce

subsection  \<open>Rotation, reflection, rotoinversion\<close>

definition\<^marker>\<open>tag important\<close>  "rotation_matrix Q \<longleftrightarrow> orthogonal_matrix Q \<and> det Q = 1"
definition\<^marker>\<open>tag important\<close>  "rotoinversion_matrix Q \<longleftrightarrow> orthogonal_matrix Q \<and> det Q = - 1"

lemma  orthogonal_rotation_or_rotoinversion:
  fixes Q :: "'a::linordered_idom^'n^'n"
  shows " orthogonal_matrix Q \<longleftrightarrow> rotation_matrix Q \<or> rotoinversion_matrix Q"
  by (metis rotoinversion_matrix_def rotation_matrix_def det_orthogonal_matrix)

text\<open> Slightly stronger results giving rotation, but only in two or more dimensions\<close>

lemma  rotation_matrix_exists_basis:
  fixes a :: "real^'n"
  assumes 2: "2 \<le> CARD('n)" and "norm a = 1"
  obtains A where "rotation_matrix A" "A *v (axis k 1) = a"
proof -
  obtain A where "orthogonal_matrix A" and A: "A *v (axis k 1) = a"
    using orthogonal_matrix_exists_basis assms by metis
  with orthogonal_rotation_or_rotoinversion
  consider "rotation_matrix A" | "rotoinversion_matrix A"
    by metis
  then show thesis
  proof cases
    assume "rotation_matrix A"
    then show ?thesis
      using \<open>A *v axis k 1 = a\<close> that by auto
  next
    from ex_card[OF 2] obtain h i::'n where "h \<noteq> i"
      by (auto simp add: eval_nat_numeral card_Suc_eq)
    then obtain j where "j \<noteq> k"
      by (metis (full_types))
    let ?TA = "transpose A"
    let ?A = "\<chi> i. if i = j then - 1 *\<^sub>R (?TA $ i) else ?TA $i"
    assume "rotoinversion_matrix A"
    then have [simp]: "det A = -1"
      by (simp add: rotoinversion_matrix_def)
    show ?thesis
    proof
      have [simp]: "row i (\<chi> i. if i = j then - 1 *\<^sub>R ?TA $ i else ?TA $ i) = (if i = j then - row i ?TA else row i ?TA)" for i
        by (auto simp: row_def)
      have "orthogonal_matrix ?A"
        unfolding orthogonal_matrix_orthonormal_rows
        using \<open>orthogonal_matrix A\<close> by (auto simp: orthogonal_matrix_orthonormal_columns orthogonal_clauses)
      then show "rotation_matrix (transpose ?A)"
        unfolding rotation_matrix_def
        by (simp add: det_row_mul[of j _ "\<lambda>i. ?TA $ i", unfolded scalar_mult_eq_scaleR])
      show "transpose ?A *v axis k 1 = a"
        using \<open>j \<noteq> k\<close> A by (simp add: matrix_vector_column axis_def scalar_mult_eq_scaleR if_distrib [of "\<lambda>z. z *\<^sub>R c" for c] cong: if_cong)
    qed
  qed
qed

lemma  rotation_exists_1:
  fixes a :: "real^'n"
  assumes "2 \<le> CARD('n)" "norm a = 1" "norm b = 1"
  obtains f where "orthogonal_transformation f" "det(matrix f) = 1" "f a = b"
proof -
  obtain k::'n where True
    by simp
  obtain A B where AB: "rotation_matrix A" "rotation_matrix B"
               and eq: "A *v (axis k 1) = a" "B *v (axis k 1) = b"
    using rotation_matrix_exists_basis assms by metis
  let ?f = "\<lambda>x. (B ** transpose A) *v x"
  show thesis
  proof
    show "orthogonal_transformation ?f"
      using AB orthogonal_matrix_mul orthogonal_transformation_matrix rotation_matrix_def matrix_vector_mul_linear by force
    show "det (matrix ?f) = 1"
      using AB by (auto simp: det_mul rotation_matrix_def)
    show "?f a = b"
      using AB unfolding orthogonal_matrix_def rotation_matrix_def
      by (metis eq matrix_mul_rid matrix_vector_mul_assoc)
  qed
qed

lemma  rotation_exists:
  fixes a :: "real^'n"
  assumes 2: "2 \<le> CARD('n)" and eq: "norm a = norm b"
  obtains f where "orthogonal_transformation f" "det(matrix f) = 1" "f a = b"
proof (cases "a = 0 \<or> b = 0")
  case True
  with assms have "a = 0" "b = 0"
    by auto
  then show ?thesis
    by (metis eq_id_iff matrix_id orthogonal_transformation_id that)
next
  case False
  then obtain f where f: "orthogonal_transformation f" "det (matrix f) = 1"
    and f': "f (a /\<^sub>R norm a) = b /\<^sub>R norm b"
    using rotation_exists_1 [of "a /\<^sub>R norm a" "b /\<^sub>R norm b", OF 2] by auto
  then interpret linear f by (simp add: orthogonal_transformation)
  have "f a = b"
    using f' False
    by (simp add: eq scale)
  with f show thesis ..
qed

lemma  rotation_rightward_line:
  fixes a :: "real^'n"
  obtains f where "orthogonal_transformation f" "2 \<le> CARD('n) \<Longrightarrow> det(matrix f) = 1"
                  "f(norm a *\<^sub>R axis k 1) = a"
proof (cases "CARD('n) = 1")
  case True
  obtain f where "orthogonal_transformation f" "f (norm a *\<^sub>R axis k (1::real)) = a"
  proof (rule orthogonal_transformation_exists)
    show "norm (norm a *\<^sub>R axis k (1::real)) = norm a"
      by simp
  qed auto
  then show thesis
    using True that by auto
next
  case False
  obtain f where "orthogonal_transformation f" "det(matrix f) = 1" "f (norm a *\<^sub>R axis k 1) = a"
  proof (rule rotation_exists)
    show "2 \<le> CARD('n)"
      using False one_le_card_finite [where 'a='n] by linarith
    show "norm (norm a *\<^sub>R axis k (1::real)) = norm a"
      by simp
  qed auto
  then show thesis
    using that by blast
qed

end
