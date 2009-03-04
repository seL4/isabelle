(* Title:      Determinants
   ID:         $Id: 
   Author:     Amine Chaieb, University of Cambridge
*)

header {* Traces, Determinant of square matrices and some properties *}

theory Determinants
  imports Euclidean_Space Permutations
begin

subsection{* First some facts about products*}
lemma setprod_insert_eq: "finite A \<Longrightarrow> setprod f (insert a A) = (if a \<in> A then setprod f A else f a * setprod f A)"
apply clarsimp
by(subgoal_tac "insert a A = A", auto)

lemma setprod_add_split:
  assumes mn: "(m::nat) <= n + 1"
  shows "setprod f {m.. n+p} = setprod f {m .. n} * setprod f {n+1..n+p}"
proof-
  let ?A = "{m .. n+p}"
  let ?B = "{m .. n}"
  let ?C = "{n+1..n+p}"
  from mn have un: "?B \<union> ?C = ?A" by auto
  from mn have dj: "?B \<inter> ?C = {}" by auto
  have f: "finite ?B" "finite ?C" by simp_all
  from setprod_Un_disjoint[OF f dj, of f, unfolded un] show ?thesis .
qed


lemma setprod_offset: "setprod f {(m::nat) + p .. n + p} = setprod (\<lambda>i. f (i + p)) {m..n}"
apply (rule setprod_reindex_cong[where f="op + p"])
apply (auto simp add: image_iff Bex_def inj_on_def)
apply arith
apply (rule ext)
apply (simp add: add_commute)
done

lemma setprod_singleton: "setprod f {x} = f x" by simp

lemma setprod_singleton_nat_seg: "setprod f {n..n} = f (n::'a::order)" by simp

lemma setprod_numseg: "setprod f {m..0} = (if m=0 then f 0 else 1)"
  "setprod f {m .. Suc n} = (if m \<le> Suc n then f (Suc n) * setprod f {m..n} 
                             else setprod f {m..n})"
  by (auto simp add: atLeastAtMostSuc_conv)

lemma setprod_le: assumes fS: "finite S" and fg: "\<forall>x\<in>S. f x \<ge> 0 \<and> f x \<le> (g x :: 'a::ordered_idom)"
  shows "setprod f S \<le> setprod g S"
using fS fg
apply(induct S)
apply simp
apply auto
apply (rule mult_mono)
apply (auto intro: setprod_nonneg)
done

  (* FIXME: In Finite_Set there is a useless further assumption *)
lemma setprod_inversef: "finite A ==> setprod (inverse \<circ> f) A = (inverse (setprod f A) :: 'a:: {division_by_zero, field})"
  apply (erule finite_induct)
  apply (simp)
  apply simp
  done

lemma setprod_le_1: assumes fS: "finite S" and f: "\<forall>x\<in>S. f x \<ge> 0 \<and> f x \<le> (1::'a::ordered_idom)"
  shows "setprod f S \<le> 1"
using setprod_le[OF fS f] unfolding setprod_1 .

subsection{* Trace *}

definition trace :: "'a::semiring_1^'n^'n \<Rightarrow> 'a" where
  "trace A = setsum (\<lambda>i. ((A$i)$i)) {1..dimindex(UNIV::'n set)}"

lemma trace_0: "trace(mat 0) = 0"
  by (simp add: trace_def mat_def Cart_lambda_beta setsum_0)

lemma trace_I: "trace(mat 1 :: 'a::semiring_1^'n^'n) = of_nat(dimindex(UNIV::'n set))"
  by (simp add: trace_def mat_def Cart_lambda_beta)

lemma trace_add: "trace ((A::'a::comm_semiring_1^'n^'n) + B) = trace A + trace B"
  by (simp add: trace_def setsum_addf Cart_lambda_beta vector_component)

lemma trace_sub: "trace ((A::'a::comm_ring_1^'n^'n) - B) = trace A - trace B"
  by (simp add: trace_def setsum_subtractf Cart_lambda_beta vector_component)

lemma trace_mul_sym:"trace ((A::'a::comm_semiring_1^'n^'n) ** B) = trace (B**A)"
  apply (simp add: trace_def matrix_matrix_mult_def Cart_lambda_beta)
  apply (subst setsum_commute)
  by (simp add: mult_commute)

(* ------------------------------------------------------------------------- *)
(* Definition of determinant.                                                *)
(* ------------------------------------------------------------------------- *)

definition det:: "'a::comm_ring_1^'n^'n \<Rightarrow> 'a" where
  "det A = setsum (\<lambda>p. of_int (sign p) * setprod (\<lambda>i. A$i$p i) {1 .. dimindex(UNIV :: 'n set)}) {p. p permutes {1 .. dimindex(UNIV :: 'n set)}}"

(* ------------------------------------------------------------------------- *)
(* A few general lemmas we need below.                                       *)
(* ------------------------------------------------------------------------- *)

lemma Cart_lambda_beta_perm: assumes p: "p permutes {1..dimindex(UNIV::'n set)}" 
  and i: "i \<in> {1..dimindex(UNIV::'n set)}" 
  shows "Cart_nth (Cart_lambda g ::'a^'n) (p i) = g(p i)"
  using permutes_in_image[OF p] i
  by (simp add:  Cart_lambda_beta permutes_in_image[OF p])

lemma setprod_permute:
  assumes p: "p permutes S" 
  shows "setprod f S = setprod (f o p) S"
proof-
  {assume "\<not> finite S" hence ?thesis by simp}
  moreover
  {assume fS: "finite S"
    then have ?thesis 
      apply (simp add: setprod_def)
      apply (rule ab_semigroup_mult.fold_image_permute)
      apply (auto simp add: p)
      apply unfold_locales
      done}
  ultimately show ?thesis by blast
qed

lemma setproduct_permute_nat_interval: "p permutes {m::nat .. n} ==> setprod f {m..n} = setprod (f o p) {m..n}"
  by (auto intro: setprod_permute)

(* ------------------------------------------------------------------------- *)
(* Basic determinant properties.                                             *)
(* ------------------------------------------------------------------------- *)

lemma det_transp: "det (transp A) = det (A::'a::comm_ring_1 ^'n^'n)"
proof-
  let ?di = "\<lambda>A i j. A$i$j"
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  have fU: "finite ?U" by blast
  {fix p assume p: "p \<in> {p. p permutes ?U}"
    from p have pU: "p permutes ?U" by blast
    have sth: "sign (inv p) = sign p" 
      by (metis sign_inverse fU p mem_def Collect_def permutation_permutes)
    from permutes_inj[OF pU] 
    have pi: "inj_on p ?U" by (blast intro: subset_inj_on)
    from permutes_image[OF pU]
    have "setprod (\<lambda>i. ?di (transp A) i (inv p i)) ?U = setprod (\<lambda>i. ?di (transp A) i (inv p i)) (p ` ?U)" by simp
    also have "\<dots> = setprod ((\<lambda>i. ?di (transp A) i (inv p i)) o p) ?U"
      unfolding setprod_reindex[OF pi] ..
    also have "\<dots> = setprod (\<lambda>i. ?di A i (p i)) ?U"
    proof-
      {fix i assume i: "i \<in> ?U"
	from i permutes_inv_o[OF pU] permutes_in_image[OF pU]
	have "((\<lambda>i. ?di (transp A) i (inv p i)) o p) i = ?di A i (p i)"
	  unfolding transp_def by (simp add: Cart_lambda_beta expand_fun_eq)}
      then show "setprod ((\<lambda>i. ?di (transp A) i (inv p i)) o p) ?U = setprod (\<lambda>i. ?di A i (p i)) ?U" by (auto intro: setprod_cong)  
    qed
    finally have "of_int (sign (inv p)) * (setprod (\<lambda>i. ?di (transp A) i (inv p i)) ?U) = of_int (sign p) * (setprod (\<lambda>i. ?di A i (p i)) ?U)" using sth
      by simp}
  then show ?thesis unfolding det_def apply (subst setsum_permutations_inverse)
  apply (rule setsum_cong2) by blast
qed

lemma det_lowerdiagonal: 
  fixes A :: "'a::comm_ring_1^'n^'n"
  assumes ld: "\<And>i j. i \<in> {1 .. dimindex (UNIV:: 'n set)} \<Longrightarrow> j \<in> {1 .. dimindex(UNIV:: 'n set)} \<Longrightarrow> i < j \<Longrightarrow> A$i$j = 0"
  shows "det A = setprod (\<lambda>i. A$i$i) {1..dimindex(UNIV:: 'n set)}"
proof-
  let ?U = "{1..dimindex(UNIV:: 'n set)}"
  let ?PU = "{p. p permutes ?U}"
  let ?pp = "\<lambda>p. of_int (sign p) * setprod (\<lambda>i. A$i$p i) {1 .. dimindex(UNIV :: 'n set)}"
  have fU: "finite ?U" by blast
  from finite_permutations[OF fU] have fPU: "finite ?PU" .
  have id0: "{id} \<subseteq> ?PU" by (auto simp add: permutes_id)
  {fix p assume p: "p \<in> ?PU -{id}"
    from p have pU: "p permutes ?U" and pid: "p \<noteq> id" by blast+
    from permutes_natset_le[OF pU] pid obtain i where
      i: "i \<in> ?U" "p i > i" by (metis not_le)
    from permutes_in_image[OF pU] i(1) have piU: "p i \<in> ?U" by blast
    from ld[OF i(1) piU i(2)] i(1) have ex:"\<exists>i \<in> ?U. A$i$p i = 0" by blast
    from setprod_zero[OF fU ex] have "?pp p = 0" by simp}
  then have p0: "\<forall>p \<in> ?PU -{id}. ?pp p = 0"  by blast
  from setsum_superset[OF fPU id0 p0] show ?thesis
    unfolding det_def by (simp add: sign_id)
qed

lemma det_upperdiagonal: 
  fixes A :: "'a::comm_ring_1^'n^'n"
  assumes ld: "\<And>i j. i \<in> {1 .. dimindex (UNIV:: 'n set)} \<Longrightarrow> j \<in> {1 .. dimindex(UNIV:: 'n set)} \<Longrightarrow> i > j \<Longrightarrow> A$i$j = 0"
  shows "det A = setprod (\<lambda>i. A$i$i) {1..dimindex(UNIV:: 'n set)}"
proof-
  let ?U = "{1..dimindex(UNIV:: 'n set)}"
  let ?PU = "{p. p permutes ?U}"
  let ?pp = "(\<lambda>p. of_int (sign p) * setprod (\<lambda>i. A$i$p i) {1 .. dimindex(UNIV :: 'n set)})"
  have fU: "finite ?U" by blast
  from finite_permutations[OF fU] have fPU: "finite ?PU" .
  have id0: "{id} \<subseteq> ?PU" by (auto simp add: permutes_id)
  {fix p assume p: "p \<in> ?PU -{id}"
    from p have pU: "p permutes ?U" and pid: "p \<noteq> id" by blast+
    from permutes_natset_ge[OF pU] pid obtain i where
      i: "i \<in> ?U" "p i < i" by (metis not_le)
    from permutes_in_image[OF pU] i(1) have piU: "p i \<in> ?U" by blast
    from ld[OF i(1) piU i(2)] i(1) have ex:"\<exists>i \<in> ?U. A$i$p i = 0" by blast
    from setprod_zero[OF fU ex] have "?pp p = 0" by simp}
  then have p0: "\<forall>p \<in> ?PU -{id}. ?pp p = 0"  by blast
  from setsum_superset[OF fPU id0 p0] show ?thesis
    unfolding det_def by (simp add: sign_id)
qed

lemma det_I: "det (mat 1 :: 'a::comm_ring_1^'n^'n) = 1"
proof-
  let ?A = "mat 1 :: 'a::comm_ring_1^'n^'n"
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  let ?f = "\<lambda>i j. ?A$i$j"
  {fix i assume i: "i \<in> ?U"
    have "?f i i = 1" using i by (vector mat_def)}
  hence th: "setprod (\<lambda>i. ?f i i) ?U = setprod (\<lambda>x. 1) ?U"
    by (auto intro: setprod_cong)
  {fix i j assume i: "i \<in> ?U" and j: "j \<in> ?U" and ij: "i < j"
    have "?f i j = 0" using i j ij by (vector mat_def) }
  then have "det ?A = setprod (\<lambda>i. ?f i i) ?U" using det_lowerdiagonal
    by blast
  also have "\<dots> = 1" unfolding th setprod_1 ..
  finally show ?thesis . 
qed

lemma det_0: "det (mat 0 :: 'a::comm_ring_1^'n^'n) = 0"
proof-
  let ?A = "mat 0 :: 'a::comm_ring_1^'n^'n"
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  let ?f = "\<lambda>i j. ?A$i$j"
  have th:"setprod (\<lambda>i. ?f i i) ?U = 0"
    apply (rule setprod_zero)
    apply simp
    apply (rule bexI[where x=1])
    using dimindex_ge_1[of "UNIV :: 'n set"]
    by (simp_all add: mat_def Cart_lambda_beta)
  {fix i j assume i: "i \<in> ?U" and j: "j \<in> ?U" and ij: "i < j"
    have "?f i j = 0" using i j ij by (vector mat_def) }
  then have "det ?A = setprod (\<lambda>i. ?f i i) ?U" using det_lowerdiagonal
    by blast
  also have "\<dots> = 0" unfolding th  ..
  finally show ?thesis . 
qed

lemma det_permute_rows:
  fixes A :: "'a::comm_ring_1^'n^'n"
  assumes p: "p permutes {1 .. dimindex (UNIV :: 'n set)}"
  shows "det(\<chi> i. A$p i :: 'a^'n^'n) = of_int (sign p) * det A"
  apply (simp add: det_def setsum_right_distrib mult_assoc[symmetric] del: One_nat_def)
  apply (subst sum_permutations_compose_right[OF p])  
proof(rule setsum_cong2)
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  let ?PU = "{p. p permutes ?U}"
  let ?Ap = "(\<chi> i. A$p i :: 'a^'n^'n)"
  fix q assume qPU: "q \<in> ?PU"
  have fU: "finite ?U" by blast
  from qPU have q: "q permutes ?U" by blast
  from p q have pp: "permutation p" and qp: "permutation q"
    by (metis fU permutation_permutes)+
  from permutes_inv[OF p] have ip: "inv p permutes ?U" .
    {fix i assume i: "i \<in> ?U"
      from Cart_lambda_beta[rule_format, OF i, of "\<lambda>i. A$ p i"]
      have "?Ap$i$ (q o p) i = A $ p i $ (q o p) i " by simp}
    hence "setprod (\<lambda>i. ?Ap$i$ (q o p) i) ?U = setprod (\<lambda>i. A$p i$(q o p) i) ?U"
      by (auto intro: setprod_cong)
    also have "\<dots> = setprod ((\<lambda>i. A$p i$(q o p) i) o inv p) ?U" 
      by (simp only: setprod_permute[OF ip, symmetric])
    also have "\<dots> = setprod (\<lambda>i. A $ (p o inv p) i $ (q o (p o inv p)) i) ?U"
      by (simp only: o_def)
    also have "\<dots> = setprod (\<lambda>i. A$i$q i) ?U" by (simp only: o_def permutes_inverses[OF p])
    finally   have thp: "setprod (\<lambda>i. ?Ap$i$ (q o p) i) ?U = setprod (\<lambda>i. A$i$q i) ?U" 
      by blast
  show "of_int (sign (q o p)) * setprod (\<lambda>i. ?Ap$i$ (q o p) i) ?U = of_int (sign p) * of_int (sign q) * setprod (\<lambda>i. A$i$q i) ?U" 
    by (simp only: thp sign_compose[OF qp pp] mult_commute of_int_mult)
qed

lemma det_permute_columns:
  fixes A :: "'a::comm_ring_1^'n^'n"
  assumes p: "p permutes {1 .. dimindex (UNIV :: 'n set)}"
  shows "det(\<chi> i j. A$i$ p j :: 'a^'n^'n) = of_int (sign p) * det A"
proof-
  let ?Ap = "\<chi> i j. A$i$ p j :: 'a^'n^'n"
  let ?At = "transp A"
  have "of_int (sign p) * det A = det (transp (\<chi> i. transp A $ p i))"
    unfolding det_permute_rows[OF p, of ?At] det_transp ..
  moreover
  have "?Ap = transp (\<chi> i. transp A $ p i)"
    by (simp add: transp_def Cart_eq Cart_lambda_beta Cart_lambda_beta_perm[OF p])
  ultimately show ?thesis by simp 
qed

lemma det_identical_rows:
  fixes A :: "'a::ordered_idom^'n^'n"
  assumes i: "i\<in>{1 .. dimindex (UNIV :: 'n set)}" 
  and j: "j\<in>{1 .. dimindex (UNIV :: 'n set)}"
  and ij: "i \<noteq> j"
  and r: "row i A = row j A"
  shows	"det A = 0"
proof-
  have tha: "\<And>(a::'a) b. a = b ==> b = - a ==> a = 0" 
    by simp
  have th1: "of_int (-1) = - 1" by (metis of_int_1 of_int_minus number_of_Min)
  let ?p = "Fun.swap i j id"
  let ?A = "\<chi> i. A $ ?p i"
  from r have "A = ?A" by (simp add: Cart_eq Cart_lambda_beta Cart_lambda_beta_perm[OF permutes_swap_id[OF i j]] row_def swap_def)
  hence "det A = det ?A" by simp
  moreover have "det A = - det ?A"
    by (simp add: det_permute_rows[OF permutes_swap_id[OF i j]] sign_swap_id ij th1)
  ultimately show "det A = 0" by (metis tha) 
qed

lemma det_identical_columns:
  fixes A :: "'a::ordered_idom^'n^'n"
  assumes i: "i\<in>{1 .. dimindex (UNIV :: 'n set)}" 
  and j: "j\<in>{1 .. dimindex (UNIV :: 'n set)}"
  and ij: "i \<noteq> j"
  and r: "column i A = column j A"
  shows	"det A = 0"
apply (subst det_transp[symmetric])
apply (rule det_identical_rows[OF i j ij])
by (metis row_transp i j r)

lemma det_zero_row: 
  fixes A :: "'a::{idom, ring_char_0}^'n^'n"
  assumes i: "i\<in>{1 .. dimindex (UNIV :: 'n set)}" 
  and r: "row i A = 0"
  shows "det A = 0"
using i r
apply (simp add: row_def det_def Cart_lambda_beta Cart_eq vector_component del: One_nat_def)
apply (rule setsum_0')
apply (clarsimp simp add: sign_nz simp del: One_nat_def)
apply (rule setprod_zero)
apply simp
apply (rule bexI[where x=i])
apply (erule_tac x="a i" in ballE)
apply (subgoal_tac "(0\<Colon>'a ^ 'n) $ a i = 0")
apply simp
apply (rule zero_index)
apply (drule permutes_in_image[of _ _ i]) 
apply simp
apply (drule permutes_in_image[of _ _ i]) 
apply simp
apply simp
done

lemma det_zero_column:
  fixes A :: "'a::{idom,ring_char_0}^'n^'n"
  assumes i: "i\<in>{1 .. dimindex (UNIV :: 'n set)}" 
  and r: "column i A = 0"
  shows "det A = 0"
  apply (subst det_transp[symmetric])
  apply (rule det_zero_row[OF i])
  by (metis row_transp r i)

lemma setsum_lambda_beta[simp]: "setsum (\<lambda>i. ((\<chi> i. g i) :: 'a::{comm_monoid_add}^'n) $ i ) {1 .. dimindex (UNIV :: 'n set)} = setsum g {1 .. dimindex (UNIV :: 'n set)}"
  by (simp add: Cart_lambda_beta)

lemma setprod_lambda_beta[simp]: "setprod (\<lambda>i. ((\<chi> i. g i) :: 'a::{comm_monoid_mult}^'n) $ i ) {1 .. dimindex (UNIV :: 'n set)} = setprod g {1 .. dimindex (UNIV :: 'n set)}"
  apply (rule setprod_cong)
  apply simp
  apply (simp add: Cart_lambda_beta')
  done

lemma setprod_lambda_beta2[simp]: "setprod (\<lambda>i. ((\<chi> i. g i) :: 'a::{comm_monoid_mult}^'n^'n) $ i$ f i ) {1 .. dimindex (UNIV :: 'n set)} = setprod (\<lambda>i. g i $ f i) {1 .. dimindex (UNIV :: 'n set)}"
proof(rule setprod_cong[OF refl])
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  fix i assume i: "i \<in> ?U"
  from Cart_lambda_beta'[OF i, of g] have 
    "((\<chi> i. g i) :: 'a^'n^'n) $ i = g i" .
  hence "((\<chi> i. g i) :: 'a^'n^'n) $ i $ f i = g i $ f i" by simp
  then
  show "((\<chi> i. g i):: 'a^'n^'n) $ i $ f i = g i $ f i"   .
qed

lemma det_row_add:
  assumes k: "k \<in> {1 .. dimindex (UNIV :: 'n set)}" 
  shows "det((\<chi> i. if i = k then a i + b i else c i)::'a::comm_ring_1^'n^'n) =
             det((\<chi> i. if i = k then a i else c i)::'a::comm_ring_1^'n^'n) +
             det((\<chi> i. if i = k then b i else c i)::'a::comm_ring_1^'n^'n)"
unfolding det_def setprod_lambda_beta2 setsum_addf[symmetric]
proof (rule setsum_cong2)
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  let ?pU = "{p. p permutes ?U}"
  let ?f = "(\<lambda>i. if i = k then a i + b i else c i)::nat \<Rightarrow> 'a::comm_ring_1^'n"
  let ?g = "(\<lambda> i. if i = k then a i else c i)::nat \<Rightarrow> 'a::comm_ring_1^'n"
  let ?h = "(\<lambda> i. if i = k then b i else c i)::nat \<Rightarrow> 'a::comm_ring_1^'n"
  fix p assume p: "p \<in> ?pU"
  let ?Uk = "?U - {k}"
  from p have pU: "p permutes ?U" by blast
  from k have pkU: "p k \<in> ?U" by (simp only: permutes_in_image[OF pU])
  note pin[simp] = permutes_in_image[OF pU]
  have kU: "?U = insert k ?Uk" using k by blast
  {fix j assume j: "j \<in> ?Uk"
    from j have "?f j $ p j = ?g j $ p j" and "?f j $ p j= ?h j $ p j" 
      by simp_all}
  then have th1: "setprod (\<lambda>i. ?f i $ p i) ?Uk = setprod (\<lambda>i. ?g i $ p i) ?Uk"
    and th2: "setprod (\<lambda>i. ?f i $ p i) ?Uk = setprod (\<lambda>i. ?h i $ p i) ?Uk"
    apply -
    apply (rule setprod_cong, simp_all)+
    done
  have th3: "finite ?Uk" "k \<notin> ?Uk" using k by auto
  have "setprod (\<lambda>i. ?f i $ p i) ?U = setprod (\<lambda>i. ?f i $ p i) (insert k ?Uk)"
    unfolding kU[symmetric] ..
  also have "\<dots> = ?f k $ p k  * setprod (\<lambda>i. ?f i $ p i) ?Uk"
    apply (rule setprod_insert)
    apply simp
    using k by blast
  also have "\<dots> = (a k $ p k * setprod (\<lambda>i. ?f i $ p i) ?Uk) + (b k$ p k * setprod (\<lambda>i. ?f i $ p i) ?Uk)" using pkU by (simp add: ring_simps vector_component)
  also have "\<dots> = (a k $ p k * setprod (\<lambda>i. ?g i $ p i) ?Uk) + (b k$ p k * setprod (\<lambda>i. ?h i $ p i) ?Uk)" by (metis th1 th2)
  also have "\<dots> = setprod (\<lambda>i. ?g i $ p i) (insert k ?Uk) + setprod (\<lambda>i. ?h i $ p i) (insert k ?Uk)"
    unfolding  setprod_insert[OF th3] by simp
  finally have "setprod (\<lambda>i. ?f i $ p i) ?U = setprod (\<lambda>i. ?g i $ p i) ?U + setprod (\<lambda>i. ?h i $ p i) ?U" unfolding kU[symmetric] .
  then show "of_int (sign p) * setprod (\<lambda>i. ?f i $ p i) ?U = of_int (sign p) * setprod (\<lambda>i. ?g i $ p i) ?U + of_int (sign p) * setprod (\<lambda>i. ?h i $ p i) ?U"
    by (simp add: ring_simps)
qed

lemma det_row_mul:
  assumes k: "k \<in> {1 .. dimindex (UNIV :: 'n set)}" 
  shows "det((\<chi> i. if i = k then c *s a i else b i)::'a::comm_ring_1^'n^'n) =
             c* det((\<chi> i. if i = k then a i else b i)::'a::comm_ring_1^'n^'n)"

unfolding det_def setprod_lambda_beta2 setsum_right_distrib
proof (rule setsum_cong2)
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  let ?pU = "{p. p permutes ?U}"
  let ?f = "(\<lambda>i. if i = k then c*s a i else b i)::nat \<Rightarrow> 'a::comm_ring_1^'n"
  let ?g = "(\<lambda> i. if i = k then a i else b i)::nat \<Rightarrow> 'a::comm_ring_1^'n"
  fix p assume p: "p \<in> ?pU"
  let ?Uk = "?U - {k}"
  from p have pU: "p permutes ?U" by blast
  from k have pkU: "p k \<in> ?U" by (simp only: permutes_in_image[OF pU])
  note pin[simp] = permutes_in_image[OF pU]
  have kU: "?U = insert k ?Uk" using k by blast
  {fix j assume j: "j \<in> ?Uk"
    from j have "?f j $ p j = ?g j $ p j" by simp}
  then have th1: "setprod (\<lambda>i. ?f i $ p i) ?Uk = setprod (\<lambda>i. ?g i $ p i) ?Uk"
    apply -
    apply (rule setprod_cong, simp_all)
    done
  have th3: "finite ?Uk" "k \<notin> ?Uk" using k by auto
  have "setprod (\<lambda>i. ?f i $ p i) ?U = setprod (\<lambda>i. ?f i $ p i) (insert k ?Uk)"
    unfolding kU[symmetric] ..
  also have "\<dots> = ?f k $ p k  * setprod (\<lambda>i. ?f i $ p i) ?Uk"
    apply (rule setprod_insert)
    apply simp
    using k by blast
  also have "\<dots> = (c*s a k) $ p k * setprod (\<lambda>i. ?f i $ p i) ?Uk" using pkU by (simp add: ring_simps vector_component)
  also have "\<dots> = c* (a k $ p k * setprod (\<lambda>i. ?g i $ p i) ?Uk)"
    unfolding th1 using pkU by (simp add: vector_component mult_ac)
  also have "\<dots> = c* (setprod (\<lambda>i. ?g i $ p i) (insert k ?Uk))"
    unfolding  setprod_insert[OF th3] by simp
  finally have "setprod (\<lambda>i. ?f i $ p i) ?U = c* (setprod (\<lambda>i. ?g i $ p i) ?U)" unfolding kU[symmetric] .
  then show "of_int (sign p) * setprod (\<lambda>i. ?f i $ p i) ?U = c * (of_int (sign p) * setprod (\<lambda>i. ?g i $ p i) ?U)"
    by (simp add: ring_simps)
qed

lemma det_row_0:
  assumes k: "k \<in> {1 .. dimindex (UNIV :: 'n set)}" 
  shows "det((\<chi> i. if i = k then 0 else b i)::'a::comm_ring_1^'n^'n) = 0"
using det_row_mul[OF k, of 0 "\<lambda>i. 1" b]
apply (simp)
  unfolding vector_smult_lzero .

lemma det_row_operation:
  fixes A :: "'a::ordered_idom^'n^'n"
  assumes i: "i \<in> {1 .. dimindex(UNIV :: 'n set)}"
  and j: "j \<in> {1 .. dimindex(UNIV :: 'n set)}"
  and ij: "i \<noteq> j"
  shows "det (\<chi> k. if k = i then row i A + c *s row j A else row k A) = det A"
proof-
  let ?Z = "(\<chi> k. if k = i then row j A else row k A) :: 'a ^'n^'n"
  have th: "row i ?Z = row j ?Z" using i j by (vector row_def)
  have th2: "((\<chi> k. if k = i then row i A else row k A) :: 'a^'n^'n) = A"
    using i j by (vector row_def)
  show ?thesis
    unfolding det_row_add [OF i] det_row_mul[OF i] det_identical_rows[OF i j ij th] th2
    by simp
qed

lemma det_row_span:
  fixes A :: "'a:: ordered_idom^'n^'n"
  assumes i: "i \<in> {1 .. dimindex(UNIV :: 'n set)}"
  and x: "x \<in> span {row j A |j. j\<in> {1 .. dimindex(UNIV :: 'n set)} \<and> j\<noteq> i}"
  shows "det (\<chi> k. if k = i then row i A + x else row k A) = det A"
proof-
  let ?U = "{1 .. dimindex(UNIV :: 'n set)}"
  let ?S = "{row j A |j. j\<in> ?U \<and> j\<noteq> i}"
  let ?d = "\<lambda>x. det (\<chi> k. if k = i then x else row k A)"
  let ?P = "\<lambda>x. ?d (row i A + x) = det A"
  {fix k 
    
    have "(if k = i then row i A + 0 else row k A) = row k A" by simp}
  then have P0: "?P 0"
    apply -
    apply (rule cong[of det, OF refl])
    using i by (vector row_def)
  moreover
  {fix c z y assume zS: "z \<in> ?S" and Py: "?P y"
    from zS obtain j where j: "z = row j A" "j \<in> ?U" "i \<noteq> j" by blast
    let ?w = "row i A + y"
    have th0: "row i A + (c*s z + y) = ?w + c*s z" by vector
    have thz: "?d z = 0"
      apply (rule det_identical_rows[OF i j(2,3)])
      using i j by (vector row_def)
    have "?d (row i A + (c*s z + y)) = ?d (?w + c*s z)" unfolding th0 ..
    then have "?P (c*s z + y)" unfolding thz Py det_row_mul[OF i] det_row_add[OF i] 
      by simp }

  ultimately show ?thesis 
    apply -
    apply (rule span_induct_alt[of ?P ?S, OF P0])
    apply blast
    apply (rule x)
    done
qed

(* ------------------------------------------------------------------------- *)
(* May as well do this, though it's a bit unsatisfactory since it ignores    *)
(* exact duplicates by considering the rows/columns as a set.                *)
(* ------------------------------------------------------------------------- *)

lemma det_dependent_rows:
  fixes A:: "'a::ordered_idom^'n^'n"
  assumes d: "dependent (rows A)"
  shows "det A = 0"
proof-
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  from d obtain i where i: "i \<in> ?U" "row i A \<in> span (rows A - {row i A})"
    unfolding dependent_def rows_def by blast
  {fix j k assume j: "j \<in>?U" and k: "k \<in> ?U" and jk: "j \<noteq> k"
    and c: "row j A = row k A" 
    from det_identical_rows[OF j k jk c] have ?thesis .}
  moreover
  {assume H: "\<And> i j. i\<in> ?U \<Longrightarrow> j \<in> ?U \<Longrightarrow> i \<noteq> j \<Longrightarrow> row i A \<noteq> row j A"
    have th0: "- row i A \<in> span {row j A|j. j \<in> ?U \<and> j \<noteq> i}"
      apply (rule span_neg)
      apply (rule set_rev_mp)
      apply (rule i(2))
      apply (rule span_mono)
      using H i by (auto simp add: rows_def)
    from det_row_span[OF i(1) th0]
    have "det A = det (\<chi> k. if k = i then 0 *s 1 else row k A)"
      unfolding right_minus vector_smult_lzero ..
    with det_row_mul[OF i(1), of "0::'a" "\<lambda>i. 1"] 
    have "det A = 0" by simp}
  ultimately show ?thesis by blast
qed

lemma det_dependent_columns: assumes d: "dependent(columns (A::'a::ordered_idom^'n^'n))" shows "det A = 0"
by (metis d det_dependent_rows rows_transp det_transp)

(* ------------------------------------------------------------------------- *)
(* Multilinearity and the multiplication formula.                            *)
(* ------------------------------------------------------------------------- *)

lemma Cart_lambda_cong: "(\<And>x. x \<in> {1 .. dimindex (UNIV :: 'n set)} \<Longrightarrow> f x = g x) \<Longrightarrow> (Cart_lambda f::'a^'n) = (Cart_lambda g :: 'a^'n)"
  apply (rule iffD1[OF Cart_lambda_unique]) by vector

lemma det_linear_row_setsum: 
  assumes fS: "finite S" and k: "k \<in> {1 .. dimindex (UNIV :: 'n set)}"
  shows "det ((\<chi> i. if i = k then setsum (a i) S else c i)::'a::comm_ring_1^'n^'n) = setsum (\<lambda>j. det ((\<chi> i. if i = k then a  i j else c i)::'a^'n^'n)) S"
  using k
proof(induct rule: finite_induct[OF fS])
  case 1 thus ?case apply simp  unfolding setsum_empty det_row_0[OF k] ..
next
  case (2 x F)
  then  show ?case by (simp add: det_row_add cong del: if_weak_cong)
qed

lemma finite_bounded_functions:
  assumes fS: "finite S"
  shows "finite {f. (\<forall>i \<in> {1.. (k::nat)}. f i \<in> S) \<and> (\<forall>i. i \<notin> {1 .. k} \<longrightarrow> f i = i)}"
proof(induct k)
  case 0 
  have th: "{f. \<forall>i. f i = i} = {id}" by (auto intro: ext)
  show ?case by (auto simp add: th)
next
  case (Suc k)
  let ?f = "\<lambda>(y::nat,g) i. if i = Suc k then y else g i"
  let ?S = "?f ` (S \<times> {f. (\<forall>i\<in>{1..k}. f i \<in> S) \<and> (\<forall>i. i \<notin> {1..k} \<longrightarrow> f i = i)})"
  have "?S = {f. (\<forall>i\<in>{1.. Suc k}. f i \<in> S) \<and> (\<forall>i. i \<notin> {1.. Suc k} \<longrightarrow> f i = i)}"
    apply (auto simp add: image_iff)
    apply (rule_tac x="x (Suc k)" in bexI)
    apply (rule_tac x = "\<lambda>i. if i = Suc k then i else x i" in exI)
    apply (auto intro: ext)
    done
  with finite_imageI[OF finite_cartesian_product[OF fS Suc.hyps(1)], of ?f]
  show ?case by metis 
qed


lemma eq_id_iff[simp]: "(\<forall>x. f x = x) = (f = id)" by (auto intro: ext)

lemma det_linear_rows_setsum_lemma:
  assumes fS: "finite S" and k: "k \<le> dimindex (UNIV :: 'n set)"
  shows "det((\<chi> i. if i <= k then setsum (a i) S else c i):: 'a::comm_ring_1^'n^'n) =
             setsum (\<lambda>f. det((\<chi> i. if i <= k then a i (f i) else c i)::'a^'n^'n))
                 {f. (\<forall>i \<in> {1 .. k}. f i \<in> S) \<and> (\<forall>i. i \<notin> {1..k} \<longrightarrow> f i = i)}"
using k
proof(induct k arbitrary: a c)
  case 0
  have th0: "\<And>x y. (\<chi> i. if i <= 0 then x i else y i) = (\<chi> i. y i)" by vector
  from "0.prems"  show ?case unfolding th0 by simp
next
  case (Suc k a c)
  let ?F = "\<lambda>k. {f. (\<forall>i \<in> {1 .. k}. f i \<in> S) \<and> (\<forall>i. i \<notin> {1..k} \<longrightarrow> f i = i)}"
  let ?h = "\<lambda>(y::nat,g) i. if i = Suc k then y else g i"
  let ?k = "\<lambda>h. (h(Suc k),(\<lambda>i. if i = Suc k then i else h i))"
  let ?s = "\<lambda> k a c f. det((\<chi> i. if i <= k then a i (f i) else c i)::'a^'n^'n)"
  let ?c = "\<lambda>i. if i = Suc k then a i j else c i"
  from Suc.prems have Sk: "Suc k \<in> {1 .. dimindex (UNIV :: 'n set)}" by simp
  from Suc.prems have k': "k \<le> dimindex (UNIV :: 'n set)" by arith
  have thif: "\<And>a b c d. (if b \<or> a then c else d) = (if a then c else if b then c else d)" by simp
  have thif2: "\<And>a b c d e. (if a then b else if c then d else e) =
     (if c then (if a then b else d) else (if a then b else e))" by simp 
  have "det (\<chi> i. if i \<le> Suc k then setsum (a i) S else c i) = 
        det (\<chi> i. if i = Suc k then setsum (a i) S 
                 else if i \<le> k then setsum (a i) S else c i)"
    unfolding le_Suc_eq thif  ..
  also have "\<dots> = (\<Sum>j\<in>S. det (\<chi> i. if i \<le> k then setsum (a i) S
                    else if i = Suc k then a i j else c i))"
    unfolding det_linear_row_setsum[OF fS Sk]
    apply (subst thif2)
    by (simp cong del: if_weak_cong cong add: if_cong)
  finally have tha: 
    "det (\<chi> i. if i \<le> Suc k then setsum (a i) S else c i) = 
     (\<Sum>(j, f)\<in>S \<times> ?F k. det (\<chi> i. if i \<le> k then a i (f i)
                                else if i = Suc k then a i j
                                else c i))" 
    unfolding  Suc.hyps[OF k'] unfolding setsum_cartesian_product by blast
  show ?case unfolding tha
    apply(rule setsum_eq_general_reverses[where h= "?h" and k= "?k"], 
      blast intro: finite_cartesian_product fS finite_bounded_functions[OF fS],
      blast intro: finite_cartesian_product fS finite_bounded_functions[OF fS], auto intro: ext)
    apply (rule cong[OF refl[of det]])
    by vector
qed

lemma det_linear_rows_setsum:
  assumes fS: "finite S"
  shows "det (\<chi> i. setsum (a i) S) = setsum (\<lambda>f. det (\<chi> i. a i (f i) :: 'a::comm_ring_1 ^ 'n^'n)) {f. (\<forall>i \<in> {1 .. dimindex (UNIV :: 'n set)}. f i \<in> S) \<and> (\<forall>i. i \<notin> {1.. dimindex (UNIV :: 'n set)} \<longrightarrow> f i = i)}"
proof-
  have th0: "\<And>x y. ((\<chi> i. if i <= dimindex(UNIV:: 'n set) then x i else y i) :: 'a^'n^'n) = (\<chi> i. x i)" by vector
  
  from det_linear_rows_setsum_lemma[OF fS, of "dimindex (UNIV :: 'n set)" a, unfolded th0, OF order_refl] show ?thesis by blast
qed

lemma matrix_mul_setsum_alt:
  fixes A B :: "'a::comm_ring_1^'n^'n"
  shows "A ** B = (\<chi> i. setsum (\<lambda>k. A$i$k *s B $ k) {1 .. dimindex (UNIV :: 'n set)})"
  by (vector matrix_matrix_mult_def setsum_component)

lemma det_rows_mul:
  "det((\<chi> i. c i *s a i)::'a::comm_ring_1^'n^'n) =
  setprod (\<lambda>i. c i) {1..dimindex(UNIV:: 'n set)} * det((\<chi> i. a i)::'a^'n^'n)"
proof (simp add: det_def Cart_lambda_beta' setsum_right_distrib vector_component cong add: setprod_cong del: One_nat_def, rule setsum_cong2)
  let ?U = "{1 .. dimindex(UNIV :: 'n set)}"
  let ?PU = "{p. p permutes ?U}"
  fix p assume pU: "p \<in> ?PU"
  let ?s = "of_int (sign p)"
  from pU have p: "p permutes ?U" by blast
  have "setprod (\<lambda>i. (c i *s a i) $ p i) ?U = setprod (\<lambda>i. c i * a i $ p i) ?U"
    apply (rule setprod_cong, blast)
    by (auto simp only: permutes_in_image[OF p] intro: vector_smult_component)
  also have "\<dots> = setprod c ?U * setprod (\<lambda>i. a i $ p i) ?U"
    unfolding setprod_timesf ..
  finally show "?s * (\<Prod>xa\<in>?U. (c xa *s a xa) $ p xa) =
        setprod c ?U * (?s* (\<Prod>xa\<in>?U. a xa $ p xa))" by (simp add: ring_simps)
qed

lemma det_mul:
  fixes A B :: "'a::ordered_idom^'n^'n"
  shows "det (A ** B) = det A * det B"
proof-
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  let ?F = "{f. (\<forall>i\<in> ?U. f i \<in> ?U) \<and> (\<forall>i. i \<notin> ?U \<longrightarrow> f i = i)}"
  let ?PU = "{p. p permutes ?U}"
  have fU: "finite ?U" by simp
  have fF: "finite ?F"  using finite_bounded_functions[OF fU] .
  {fix p assume p: "p permutes ?U"
    
    have "p \<in> ?F" unfolding mem_Collect_eq permutes_in_image[OF p]
      using p[unfolded permutes_def] by simp}
  then have PUF: "?PU \<subseteq> ?F"  by blast 
  {fix f assume fPU: "f \<in> ?F - ?PU"
    have fUU: "f ` ?U \<subseteq> ?U" using fPU by auto
    from fPU have f: "\<forall>i \<in> ?U. f i \<in> ?U"
      "\<forall>i. i \<notin> ?U \<longrightarrow> f i = i" "\<not>(\<forall>y. \<exists>!x. f x = y)" unfolding permutes_def 
      by auto
    
    let ?A = "(\<chi> i. A$i$f i *s B$f i) :: 'a^'n^'n"
    let ?B = "(\<chi> i. B$f i) :: 'a^'n^'n"
    {assume fni: "\<not> inj_on f ?U"
      then obtain i j where ij: "i \<in> ?U" "j \<in> ?U" "f i = f j" "i \<noteq> j"
	unfolding inj_on_def by blast
      from ij 
      have rth: "row i ?B = row j ?B" by (vector row_def)
      from det_identical_rows[OF ij(1,2,4) rth] 
      have "det (\<chi> i. A$i$f i *s B$f i) = 0" 
	unfolding det_rows_mul by simp}
    moreover
    {assume fi: "inj_on f ?U"
      from f fi have fith: "\<And>i j. f i = f j \<Longrightarrow> i = j"
	unfolding inj_on_def
	apply (case_tac "i \<in> ?U")
	apply (case_tac "j \<in> ?U") by metis+
      note fs = fi[unfolded surjective_iff_injective_gen[OF fU fU refl fUU, symmetric]]
      
      {fix y
	from fs f have "\<exists>x. f x = y" by (cases "y \<in> ?U") blast+
	then obtain x where x: "f x = y" by blast
	{fix z assume z: "f z = y" from fith x z have "z = x" by metis}
	with x have "\<exists>!x. f x = y" by blast}
      with f(3) have "det (\<chi> i. A$i$f i *s B$f i) = 0" by blast}
    ultimately have "det (\<chi> i. A$i$f i *s B$f i) = 0" by blast}
  hence zth: "\<forall> f\<in> ?F - ?PU. det (\<chi> i. A$i$f i *s B$f i) = 0" by simp
  {fix p assume pU: "p \<in> ?PU"
    from pU have p: "p permutes ?U" by blast
    let ?s = "\<lambda>p. of_int (sign p)"
    let ?f = "\<lambda>q. ?s p * (\<Prod>i\<in> ?U. A $ i $ p i) *
               (?s q * (\<Prod>i\<in> ?U. B $ i $ q i))"
    have "(setsum (\<lambda>q. ?s q *
            (\<Prod>i\<in> ?U. (\<chi> i. A $ i $ p i *s B $ p i :: 'a^'n^'n) $ i $ q i)) ?PU) =
        (setsum (\<lambda>q. ?s p * (\<Prod>i\<in> ?U. A $ i $ p i) *
               (?s q * (\<Prod>i\<in> ?U. B $ i $ q i))) ?PU)"
      unfolding sum_permutations_compose_right[OF permutes_inv[OF p], of ?f]
    proof(rule setsum_cong2)
      fix q assume qU: "q \<in> ?PU"
      hence q: "q permutes ?U" by blast
      from p q have pp: "permutation p" and pq: "permutation q"
	unfolding permutation_permutes by auto 
      have th00: "of_int (sign p) * of_int (sign p) = (1::'a)" 
	"\<And>a. of_int (sign p) * (of_int (sign p) * a) = a" 
	unfolding mult_assoc[symmetric]	unfolding of_int_mult[symmetric] 
	by (simp_all add: sign_idempotent)
      have ths: "?s q = ?s p * ?s (q o inv p)"
	using pp pq permutation_inverse[OF pp] sign_inverse[OF pp]
	by (simp add:  th00 mult_ac sign_idempotent sign_compose)
      have th001: "setprod (\<lambda>i. B$i$ q (inv p i)) ?U = setprod ((\<lambda>i. B$i$ q (inv p i)) o p) ?U"
	by (rule setprod_permute[OF p])
      have thp: "setprod (\<lambda>i. (\<chi> i. A$i$p i *s B$p i :: 'a^'n^'n) $i $ q i) ?U = setprod (\<lambda>i. A$i$p i) ?U * setprod (\<lambda>i. B$i$ q (inv p i)) ?U" 
	unfolding th001 setprod_timesf[symmetric] o_def permutes_inverses[OF p]
	apply (rule setprod_cong[OF refl])
	using permutes_in_image[OF q] by vector
      show "?s q * setprod (\<lambda>i. (((\<chi> i. A$i$p i *s B$p i) :: 'a^'n^'n)$i$q i)) ?U = ?s p * (setprod (\<lambda>i. A$i$p i) ?U) * (?s (q o inv p) * setprod (\<lambda>i. B$i$(q o inv p) i) ?U)"
	using ths thp pp pq permutation_inverse[OF pp] sign_inverse[OF pp]
	by (simp add: sign_nz th00 ring_simps sign_idempotent sign_compose)
    qed
  }
  then have th2: "setsum (\<lambda>f. det (\<chi> i. A$i$f i *s B$f i)) ?PU = det A * det B" 
    unfolding det_def setsum_product
    by (rule setsum_cong2) 
  have "det (A**B) = setsum (\<lambda>f.  det (\<chi> i. A $ i $ f i *s B $ f i)) ?F"
    unfolding matrix_mul_setsum_alt det_linear_rows_setsum[OF fU] .. 
  also have "\<dots> = setsum (\<lambda>f. det (\<chi> i. A$i$f i *s B$f i)) ?PU"
    unfolding setsum_superset[OF fF PUF zth, symmetric] 
    unfolding det_rows_mul ..
  finally show ?thesis unfolding th2 .
qed  

(* ------------------------------------------------------------------------- *)
(* Relation to invertibility.                                                *)
(* ------------------------------------------------------------------------- *)

lemma invertible_left_inverse:
  fixes A :: "real^'n^'n"
  shows "invertible A \<longleftrightarrow> (\<exists>(B::real^'n^'n). B** A = mat 1)"
  by (metis invertible_def matrix_left_right_inverse)

lemma invertible_righ_inverse:
  fixes A :: "real^'n^'n"
  shows "invertible A \<longleftrightarrow> (\<exists>(B::real^'n^'n). A** B = mat 1)"
  by (metis invertible_def matrix_left_right_inverse)

lemma invertible_det_nz: 
  fixes A::"real ^'n^'n"
  shows "invertible A \<longleftrightarrow> det A \<noteq> 0"
proof-
  {assume "invertible A"
    then obtain B :: "real ^'n^'n" where B: "A ** B = mat 1"
      unfolding invertible_righ_inverse by blast
    hence "det (A ** B) = det (mat 1 :: real ^'n^'n)" by simp
    hence "det A \<noteq> 0"
      apply (simp add: det_mul det_I) by algebra }
  moreover
  {assume H: "\<not> invertible A"
    let ?U = "{1 .. dimindex(UNIV :: 'n set)}"
    have fU: "finite ?U" by simp
    from H obtain c i where c: "setsum (\<lambda>i. c i *s row i A) ?U = 0" 
      and iU: "i \<in> ?U" and ci: "c i \<noteq> 0"
      unfolding invertible_righ_inverse
      unfolding matrix_right_invertible_independent_rows by blast
    have stupid: "\<And>(a::real^'n) b. a + b = 0 \<Longrightarrow> -a = b"
      apply (drule_tac f="op + (- a)" in cong[OF refl])
      apply (simp only: ab_left_minus add_assoc[symmetric])
      apply simp
      done
    from c ci 
    have thr0: "- row i A = setsum (\<lambda>j. (1/ c i) *s c j *s row j A) (?U - {i})"
      unfolding setsum_diff1'[OF fU iU] setsum_cmul 
      apply (simp add: field_simps)
      apply (rule vector_mul_lcancel_imp[OF ci])
      apply (auto simp add: vector_smult_assoc vector_smult_rneg field_simps)
      unfolding stupid ..
    have thr: "- row i A \<in> span {row j A| j. j\<in> ?U \<and> j \<noteq> i}" 
      unfolding thr0
      apply (rule span_setsum)
      apply simp
      apply (rule ballI)
      apply (rule span_mul)+
      apply (rule span_superset)
      apply auto
      done
    let ?B = "(\<chi> k. if k = i then 0 else row k A) :: real ^'n^'n"
    have thrb: "row i ?B = 0" using iU by (vector row_def) 
    have "det A = 0" 
      unfolding det_row_span[OF iU thr, symmetric] right_minus
      unfolding  det_zero_row[OF iU thrb]  ..}
  ultimately show ?thesis by blast
qed

(* ------------------------------------------------------------------------- *)
(* Cramer's rule.                                                            *)
(* ------------------------------------------------------------------------- *)

lemma cramer_lemma_transp:
  fixes A:: "'a::ordered_idom^'n^'n" and x :: "'a ^'n"
  assumes k: "k \<in> {1 .. dimindex(UNIV ::'n set)}"
  shows "det ((\<chi> i. if i = k then setsum (\<lambda>i. x$i *s row i A) {1 .. dimindex(UNIV::'n set)}
                           else row i A)::'a^'n^'n) = x$k * det A" 
  (is "?lhs = ?rhs") 
proof-
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  let ?Uk = "?U - {k}"
  have U: "?U = insert k ?Uk" using k by blast
  have fUk: "finite ?Uk" by simp
  have kUk: "k \<notin> ?Uk" by simp
  have th00: "\<And>k s. x$k *s row k A + s = (x$k - 1) *s row k A + row k A + s"
    by (vector ring_simps)
  have th001: "\<And>f k . (\<lambda>x. if x = k then f k else f x) = f" by (auto intro: ext)
  have "(\<chi> i. row i A) = A" by (vector row_def)
  then have thd1: "det (\<chi> i. row i A) = det A"  by simp 
  have thd0: "det (\<chi> i. if i = k then row k A + (\<Sum>i \<in> ?Uk. x $ i *s row i A) else row i A) = det A"
    apply (rule det_row_span[OF k])
    apply (rule span_setsum[OF fUk])
    apply (rule ballI)
    apply (rule span_mul)
    apply (rule span_superset)
    apply auto
    done
  show "?lhs = x$k * det A"
    apply (subst U)
    unfolding setsum_insert[OF fUk kUk] 
    apply (subst th00)
    unfolding add_assoc
    apply (subst det_row_add[OF k])
    unfolding thd0
    unfolding det_row_mul[OF k]
    unfolding th001[of k "\<lambda>i. row i A"]
    unfolding thd1  by (simp add: ring_simps)
qed

lemma cramer_lemma:
  fixes A :: "'a::ordered_idom ^'n^'n"
  assumes k: "k \<in> {1 .. dimindex (UNIV :: 'n set)}" (is " _ \<in> ?U")
  shows "det((\<chi> i j. if j = k then (A *v x)$i else A$i$j):: 'a^'n^'n) = x$k * det A"
proof-
  have stupid: "\<And>c. setsum (\<lambda>i. c i *s row i (transp A)) ?U = setsum (\<lambda>i. c i *s column i A) ?U"
    by (auto simp add: row_transp intro: setsum_cong2)
  show ?thesis 
  unfolding matrix_mult_vsum 
  unfolding cramer_lemma_transp[OF k, of x "transp A", unfolded det_transp, symmetric]
  unfolding stupid[of "\<lambda>i. x$i"]
  apply (subst det_transp[symmetric])
  apply (rule cong[OF refl[of det]]) by (vector transp_def column_def row_def)
qed

lemma cramer:
  fixes A ::"real^'n^'n"
  assumes d0: "det A \<noteq> 0" 
  shows "A *v x = b \<longleftrightarrow> x = (\<chi> k. det(\<chi> i j. if j=k then b$i else A$i$j :: real^'n^'n) / det A)"
proof-
  from d0 obtain B where B: "A ** B = mat 1" "B ** A = mat 1"  
    unfolding invertible_det_nz[symmetric] invertible_def by blast
  have "(A ** B) *v b = b" by (simp add: B matrix_vector_mul_lid)
  hence "A *v (B *v b) = b" by (simp add: matrix_vector_mul_assoc)
  then have xe: "\<exists>x. A*v x = b" by blast
  {fix x assume x: "A *v x = b"
  have "x = (\<chi> k. det(\<chi> i j. if j=k then b$i else A$i$j :: real^'n^'n) / det A)"
    unfolding x[symmetric]
    using d0 by (simp add: Cart_eq Cart_lambda_beta' cramer_lemma field_simps)}
  with xe show ?thesis by auto
qed

(* ------------------------------------------------------------------------- *)
(* Orthogonality of a transformation and matrix.                             *)
(* ------------------------------------------------------------------------- *)

definition "orthogonal_transformation f \<longleftrightarrow> linear f \<and> (\<forall>v w. f v \<bullet> f w = v \<bullet> w)"

lemma orthogonal_transformation: "orthogonal_transformation f \<longleftrightarrow> linear f \<and> (\<forall>(v::real ^'n). norm (f v) = norm v)"
  unfolding orthogonal_transformation_def
  apply auto 
  apply (erule_tac x=v in allE)+
  apply (simp add: real_vector_norm_def)
  by (simp add: dot_norm  linear_add[symmetric]) 

definition "orthogonal_matrix (Q::'a::semiring_1^'n^'n) \<longleftrightarrow> transp Q ** Q = mat 1 \<and> Q ** transp Q = mat 1"

lemma orthogonal_matrix: "orthogonal_matrix (Q:: real ^'n^'n)  \<longleftrightarrow> transp Q ** Q = mat 1"
  by (metis matrix_left_right_inverse orthogonal_matrix_def)

lemma orthogonal_matrix_id: "orthogonal_matrix (mat 1)"
  by (simp add: orthogonal_matrix_def transp_mat matrix_mul_lid)

lemma orthogonal_matrix_mul: 
  fixes A :: "real ^'n^'n"
  assumes oA : "orthogonal_matrix A"
  and oB: "orthogonal_matrix B" 
  shows "orthogonal_matrix(A ** B)"
  using oA oB 
  unfolding orthogonal_matrix matrix_transp_mul
  apply (subst matrix_mul_assoc)
  apply (subst matrix_mul_assoc[symmetric])
  by (simp add: matrix_mul_rid)

lemma orthogonal_transformation_matrix:
  fixes f:: "real^'n \<Rightarrow> real^'n"
  shows "orthogonal_transformation f \<longleftrightarrow> linear f \<and> orthogonal_matrix(matrix f)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof-
  let ?mf = "matrix f"
  let ?ot = "orthogonal_transformation f"
  let ?U = "{1 .. dimindex (UNIV :: 'n set)}"
  have fU: "finite ?U" by simp
  let ?m1 = "mat 1 :: real ^'n^'n"
  {assume ot: ?ot
    from ot have lf: "linear f" and fd: "\<forall>v w. f v \<bullet> f w = v \<bullet> w"
      unfolding  orthogonal_transformation_def orthogonal_matrix by blast+
    {fix i j assume i: "i \<in> ?U" and j: "j \<in> ?U"
      let ?A = "transp ?mf ** ?mf"
      have th0: "\<And>b (x::'a::comm_ring_1). (if b then 1 else 0)*x = (if b then x else 0)"
	"\<And>b (x::'a::comm_ring_1). x*(if b then 1 else 0) = (if b then x else 0)"
	by simp_all
      from fd[rule_format, of "basis i" "basis j", unfolded matrix_works[OF lf, symmetric] dot_matrix_vector_mul] i j
      have "?A$i$j = ?m1 $ i $ j" 
	by (simp add: Cart_lambda_beta' dot_def matrix_matrix_mult_def columnvector_def rowvector_def basis_def th0 setsum_delta[OF fU] mat_def del: One_nat_def)}
    hence "orthogonal_matrix ?mf" unfolding orthogonal_matrix by vector
    with lf have ?rhs by blast}
  moreover
  {assume lf: "linear f" and om: "orthogonal_matrix ?mf"
    from lf om have ?lhs
      unfolding orthogonal_matrix_def norm_eq orthogonal_transformation
      unfolding matrix_works[OF lf, symmetric]
      apply (subst dot_matrix_vector_mul)
      by (simp add: dot_matrix_product matrix_mul_lid del: One_nat_def)}
  ultimately show ?thesis by blast
qed

lemma det_orthogonal_matrix: 
  fixes Q:: "'a::ordered_idom^'n^'n"
  assumes oQ: "orthogonal_matrix Q"
  shows "det Q = 1 \<or> det Q = - 1"
proof-
  
  have th: "\<And>x::'a. x = 1 \<or> x = - 1 \<longleftrightarrow> x*x = 1" (is "\<And>x::'a. ?ths x") 
  proof- 
    fix x:: 'a
    have th0: "x*x - 1 = (x - 1)*(x + 1)" by (simp add: ring_simps)
    have th1: "\<And>(x::'a) y. x = - y \<longleftrightarrow> x + y = 0" 
      apply (subst eq_iff_diff_eq_0) by simp
    have "x*x = 1 \<longleftrightarrow> x*x - 1 = 0" by simp
    also have "\<dots> \<longleftrightarrow> x = 1 \<or> x = - 1" unfolding th0 th1 by simp
    finally show "?ths x" ..
  qed
  from oQ have "Q ** transp Q = mat 1" by (metis orthogonal_matrix_def)
  hence "det (Q ** transp Q) = det (mat 1:: 'a^'n^'n)" by simp
  hence "det Q * det Q = 1" by (simp add: det_mul det_I det_transp)
  then show ?thesis unfolding th . 
qed

(* ------------------------------------------------------------------------- *)
(* Linearity of scaling, and hence isometry, that preserves origin.          *)
(* ------------------------------------------------------------------------- *)
lemma scaling_linear: 
  fixes f :: "real ^'n \<Rightarrow> real ^'n"
  assumes f0: "f 0 = 0" and fd: "\<forall>x y. dist (f x) (f y) = c * dist x y"
  shows "linear f"
proof-
  {fix v w 
    {fix x note fd[rule_format, of x 0, unfolded dist_def f0 diff_0_right] }
    note th0 = this
    have "f v \<bullet> f w = c^2 * (v \<bullet> w)" 
      unfolding dot_norm_neg dist_def[symmetric]
      unfolding th0 fd[rule_format] by (simp add: power2_eq_square field_simps)}
  note fc = this
  show ?thesis unfolding linear_def vector_eq
    by (simp add: dot_lmult dot_ladd dot_rmult dot_radd fc ring_simps)
qed    

lemma isometry_linear:
  "f (0:: real^'n) = (0:: real^'n) \<Longrightarrow> \<forall>x y. dist(f x) (f y) = dist x y
        \<Longrightarrow> linear f"
by (rule scaling_linear[where c=1]) simp_all

(* ------------------------------------------------------------------------- *)
(* Hence another formulation of orthogonal transformation.                   *)
(* ------------------------------------------------------------------------- *)

lemma orthogonal_transformation_isometry:
  "orthogonal_transformation f \<longleftrightarrow> f(0::real^'n) = (0::real^'n) \<and> (\<forall>x y. dist(f x) (f y) = dist x y)"
  unfolding orthogonal_transformation 
  apply (rule iffI)
  apply clarify
  apply (clarsimp simp add: linear_0 linear_sub[symmetric] dist_def)
  apply (rule conjI)
  apply (rule isometry_linear)
  apply simp
  apply simp
  apply clarify
  apply (erule_tac x=v in allE)
  apply (erule_tac x=0 in allE)
  by (simp add: dist_def)

(* ------------------------------------------------------------------------- *)
(* Can extend an isometry from unit sphere.                                  *)
(* ------------------------------------------------------------------------- *)

lemma isometry_sphere_extend:
  fixes f:: "real ^'n \<Rightarrow> real ^'n"
  assumes f1: "\<forall>x. norm x = 1 \<longrightarrow> norm (f x) = 1"
  and fd1: "\<forall> x y. norm x = 1 \<longrightarrow> norm y = 1 \<longrightarrow> dist (f x) (f y) = dist x y"
  shows "\<exists>g. orthogonal_transformation g \<and> (\<forall>x. norm x = 1 \<longrightarrow> g x = f x)"
proof-
  {fix x y x' y' x0 y0 x0' y0' :: "real ^'n" 
    assume H: "x = norm x *s x0" "y = norm y *s y0"
    "x' = norm x *s x0'" "y' = norm y *s y0'" 
    "norm x0 = 1" "norm x0' = 1" "norm y0 = 1" "norm y0' = 1"
    "norm(x0' - y0') = norm(x0 - y0)"
    
    have "norm(x' - y') = norm(x - y)"
      apply (subst H(1))
      apply (subst H(2))
      apply (subst H(3))
      apply (subst H(4))
      using H(5-9)
      apply (simp add: norm_eq norm_eq_1)
      apply (simp add: dot_lsub dot_rsub dot_lmult dot_rmult)
      apply (simp add: ring_simps)
      by (simp only: right_distrib[symmetric])}
  note th0 = this
  let ?g = "\<lambda>x. if x = 0 then 0 else norm x *s f (inverse (norm x) *s x)"
  {fix x:: "real ^'n" assume nx: "norm x = 1"
    have "?g x = f x" using nx by auto}
  hence thfg: "\<forall>x. norm x = 1 \<longrightarrow> ?g x = f x" by blast
  have g0: "?g 0 = 0" by simp
  {fix x y :: "real ^'n"
    {assume "x = 0" "y = 0"
      then have "dist (?g x) (?g y) = dist x y" by simp }
    moreover
    {assume "x = 0" "y \<noteq> 0"
      then have "dist (?g x) (?g y) = dist x y" 
	apply (simp add: dist_def norm_mul)
	apply (rule f1[rule_format])
	by(simp add: norm_mul field_simps)}
    moreover
    {assume "x \<noteq> 0" "y = 0"
      then have "dist (?g x) (?g y) = dist x y" 
	apply (simp add: dist_def norm_mul)
	apply (rule f1[rule_format])
	by(simp add: norm_mul field_simps)}
    moreover
    {assume z: "x \<noteq> 0" "y \<noteq> 0"
      have th00: "x = norm x *s inverse (norm x) *s x" "y = norm y *s inverse (norm y) *s y" "norm x *s f (inverse (norm x) *s x) = norm x *s f (inverse (norm x) *s x)"
	"norm y *s f (inverse (norm y) *s y) = norm y *s f (inverse (norm y) *s y)"
	"norm (inverse (norm x) *s x) = 1"
	"norm (f (inverse (norm x) *s x)) = 1"
	"norm (inverse (norm y) *s y) = 1"
	"norm (f (inverse (norm y) *s y)) = 1"
	"norm (f (inverse (norm x) *s x) - f (inverse (norm y) *s y)) =
	norm (inverse (norm x) *s x - inverse (norm y) *s y)"
	using z
	by (auto simp add: vector_smult_assoc field_simps norm_mul intro: f1[rule_format] fd1[rule_format, unfolded dist_def])
      from z th0[OF th00] have "dist (?g x) (?g y) = dist x y" 
	by (simp add: dist_def)}
    ultimately have "dist (?g x) (?g y) = dist x y" by blast}
  note thd = this
    show ?thesis 
    apply (rule exI[where x= ?g])
    unfolding orthogonal_transformation_isometry
      using  g0 thfg thd by metis 
qed

(* ------------------------------------------------------------------------- *)
(* Rotation, reflection, rotoinversion.                                      *)
(* ------------------------------------------------------------------------- *)

definition "rotation_matrix Q \<longleftrightarrow> orthogonal_matrix Q \<and> det Q = 1"
definition "rotoinversion_matrix Q \<longleftrightarrow> orthogonal_matrix Q \<and> det Q = - 1"

lemma orthogonal_rotation_or_rotoinversion: 
  fixes Q :: "'a::ordered_idom^'n^'n"
  shows " orthogonal_matrix Q \<longleftrightarrow> rotation_matrix Q \<or> rotoinversion_matrix Q"
  by (metis rotoinversion_matrix_def rotation_matrix_def det_orthogonal_matrix)
(* ------------------------------------------------------------------------- *)
(* Explicit formulas for low dimensions.                                     *)
(* ------------------------------------------------------------------------- *)

lemma setprod_1: "setprod f {(1::nat)..1} = f 1" by simp

lemma setprod_2: "setprod f {(1::nat)..2} = f 1 * f 2" 
  by (simp add: nat_number setprod_numseg mult_commute)
lemma setprod_3: "setprod f {(1::nat)..3} = f 1 * f 2 * f 3" 
  by (simp add: nat_number setprod_numseg mult_commute)

lemma det_1: "det (A::'a::comm_ring_1^1^1) = A$1$1"
  by (simp add: det_def dimindex_def permutes_sing sign_id del: One_nat_def)

lemma det_2: "det (A::'a::comm_ring_1^2^2) = A$1$1 * A$2$2 - A$1$2 * A$2$1"
proof-
  have f12: "finite {2::nat}" "1 \<notin> {2::nat}" by auto
  have th12: "{1 .. 2} = insert (1::nat) {2}" by auto
  show ?thesis 
  apply (simp add: det_def dimindex_def th12 del: One_nat_def)
  unfolding setsum_over_permutations_insert[OF f12]
  unfolding permutes_sing
  apply (simp add: sign_swap_id sign_id swap_id_eq del: One_nat_def)
  by (simp add: arith_simps(31)[symmetric] of_int_minus of_int_1 del: arith_simps(31))
qed

lemma det_3: "det (A::'a::comm_ring_1^3^3) = 
  A$1$1 * A$2$2 * A$3$3 +
  A$1$2 * A$2$3 * A$3$1 +
  A$1$3 * A$2$1 * A$3$2 -
  A$1$1 * A$2$3 * A$3$2 -
  A$1$2 * A$2$1 * A$3$3 -
  A$1$3 * A$2$2 * A$3$1"
proof-
  have f123: "finite {(2::nat), 3}" "1 \<notin> {(2::nat), 3}" by auto
  have f23: "finite {(3::nat)}" "2 \<notin> {(3::nat)}" by auto
  have th12: "{1 .. 3} = insert (1::nat) (insert 2 {3})" by auto

  show ?thesis 
  apply (simp add: det_def dimindex_def th12 del: One_nat_def)
  unfolding setsum_over_permutations_insert[OF f123]
  unfolding setsum_over_permutations_insert[OF f23]

  unfolding permutes_sing
  apply (simp add: sign_swap_id permutation_swap_id sign_compose sign_id swap_id_eq del: One_nat_def)
  apply (simp add: arith_simps(31)[symmetric] of_int_minus of_int_1 del: arith_simps(31) One_nat_def)
  by (simp add: ring_simps)
qed

end
