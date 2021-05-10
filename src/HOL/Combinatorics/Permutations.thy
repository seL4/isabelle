(*  Author:     Amine Chaieb, University of Cambridge
*)

section \<open>Permutations, both general and specifically on finite sets.\<close>

theory Permutations
  imports
    "HOL-Library.Multiset"
    "HOL-Library.Disjoint_Sets"
    Transposition
begin

subsection \<open>Auxiliary\<close>

abbreviation (input) fixpoints :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> 'a set\<close>
  where \<open>fixpoints f \<equiv> {x. f x = x}\<close>

lemma inj_on_fixpoints:
  \<open>inj_on f (fixpoints f)\<close>
  by (rule inj_onI) simp

lemma bij_betw_fixpoints:
  \<open>bij_betw f (fixpoints f) (fixpoints f)\<close>
  using inj_on_fixpoints by (auto simp add: bij_betw_def)


subsection \<open>Basic definition and consequences\<close>

definition permutes :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> 'a set \<Rightarrow> bool\<close>  (infixr \<open>permutes\<close> 41)
  where \<open>p permutes S \<longleftrightarrow> (\<forall>x. x \<notin> S \<longrightarrow> p x = x) \<and> (\<forall>y. \<exists>!x. p x = y)\<close>

lemma bij_imp_permutes:
  \<open>p permutes S\<close> if \<open>bij_betw p S S\<close> and stable: \<open>\<And>x. x \<notin> S \<Longrightarrow> p x = x\<close>
proof -
  note \<open>bij_betw p S S\<close>
  moreover have \<open>bij_betw p (- S) (- S)\<close>
    by (auto simp add: stable intro!: bij_betw_imageI inj_onI)
  ultimately have \<open>bij_betw p (S \<union> - S) (S \<union> - S)\<close>
    by (rule bij_betw_combine) simp
  then have \<open>\<exists>!x. p x = y\<close> for y
    by (simp add: bij_iff)
  with stable show ?thesis
    by (simp add: permutes_def)
qed

context
  fixes p :: \<open>'a \<Rightarrow> 'a\<close> and S :: \<open>'a set\<close>
  assumes perm: \<open>p permutes S\<close>
begin

lemma permutes_inj:
  \<open>inj p\<close>
  using perm by (auto simp: permutes_def inj_on_def)

lemma permutes_image:
  \<open>p ` S = S\<close>
proof (rule set_eqI)
  fix x
  show \<open>x \<in> p ` S \<longleftrightarrow> x \<in> S\<close>
  proof
    assume \<open>x \<in> p ` S\<close>
    then obtain y where \<open>y \<in> S\<close> \<open>p y = x\<close>
      by blast
    with perm show \<open>x \<in> S\<close>
      by (cases \<open>y = x\<close>) (auto simp add: permutes_def)
  next
    assume \<open>x \<in> S\<close>
    with perm obtain y where \<open>y \<in> S\<close> \<open>p y = x\<close>
      by (metis permutes_def)
    then show \<open>x \<in> p ` S\<close>
      by blast
  qed
qed

lemma permutes_not_in:
  \<open>x \<notin> S \<Longrightarrow> p x = x\<close>
  using perm by (auto simp: permutes_def)

lemma permutes_image_complement:
  \<open>p ` (- S) = - S\<close>
  by (auto simp add: permutes_not_in)

lemma permutes_in_image:
  \<open>p x \<in> S \<longleftrightarrow> x \<in> S\<close>
  using permutes_image permutes_inj by (auto dest: inj_image_mem_iff)

lemma permutes_surj:
  \<open>surj p\<close>
proof -
  have \<open>p ` (S \<union> - S) = p ` S \<union> p ` (- S)\<close>
    by (rule image_Un)
  then show ?thesis
    by (simp add: permutes_image permutes_image_complement)
qed

lemma permutes_inv_o:
  shows "p \<circ> inv p = id"
    and "inv p \<circ> p = id"
  using permutes_inj permutes_surj
  unfolding inj_iff [symmetric] surj_iff [symmetric] by auto

lemma permutes_inverses:
  shows "p (inv p x) = x"
    and "inv p (p x) = x"
  using permutes_inv_o [unfolded fun_eq_iff o_def] by auto

lemma permutes_inv_eq:
  \<open>inv p y = x \<longleftrightarrow> p x = y\<close>
  by (auto simp add: permutes_inverses)

lemma permutes_inj_on:
  \<open>inj_on p A\<close>
  by (rule inj_on_subset [of _ UNIV]) (auto intro: permutes_inj)

lemma permutes_bij:
  \<open>bij p\<close>
  unfolding bij_def by (metis permutes_inj permutes_surj)

lemma permutes_imp_bij:
  \<open>bij_betw p S S\<close>
  by (simp add: bij_betw_def permutes_image permutes_inj_on)

lemma permutes_subset:
  \<open>p permutes T\<close> if \<open>S \<subseteq> T\<close>
proof (rule bij_imp_permutes)
  define R where \<open>R = T - S\<close>
  with that have \<open>T = R \<union> S\<close> \<open>R \<inter> S = {}\<close>
    by auto
  then have \<open>p x = x\<close> if \<open>x \<in> R\<close> for x
    using that by (auto intro: permutes_not_in)
  then have \<open>p ` R = R\<close>
    by simp
  with \<open>T = R \<union> S\<close> show \<open>bij_betw p T T\<close>
    by (simp add: bij_betw_def permutes_inj_on image_Un permutes_image)
  fix x
  assume \<open>x \<notin> T\<close>
  with \<open>T = R \<union> S\<close> show \<open>p x = x\<close>
    by (simp add: permutes_not_in)
qed

lemma permutes_imp_permutes_insert:
  \<open>p permutes insert x S\<close>
  by (rule permutes_subset) auto

end

lemma permutes_id [simp]:
  \<open>id permutes S\<close>
  by (auto intro: bij_imp_permutes)

lemma permutes_empty [simp]:
  \<open>p permutes {} \<longleftrightarrow> p = id\<close>
proof
  assume \<open>p permutes {}\<close>
  then show \<open>p = id\<close>
    by (auto simp add: fun_eq_iff permutes_not_in)
next
  assume \<open>p = id\<close>
  then show \<open>p permutes {}\<close>
    by simp
qed

lemma permutes_sing [simp]:
  \<open>p permutes {a} \<longleftrightarrow> p = id\<close>
proof
  assume perm: \<open>p permutes {a}\<close>
  show \<open>p = id\<close>
  proof
    fix x
    from perm have \<open>p ` {a} = {a}\<close>
      by (rule permutes_image)
    with perm show \<open>p x = id x\<close>
      by (cases \<open>x = a\<close>) (auto simp add: permutes_not_in)
  qed
next
  assume \<open>p = id\<close>
  then show \<open>p permutes {a}\<close>
    by simp
qed

lemma permutes_univ: "p permutes UNIV \<longleftrightarrow> (\<forall>y. \<exists>!x. p x = y)"
  by (simp add: permutes_def)

lemma permutes_swap_id: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> transpose a b permutes S"
  by (rule bij_imp_permutes) (auto intro: transpose_apply_other)

lemma permutes_superset:
  \<open>p permutes T\<close> if \<open>p permutes S\<close> \<open>\<And>x. x \<in> S - T \<Longrightarrow> p x = x\<close>
proof -
  define R U where \<open>R = T \<inter> S\<close> and \<open>U = S - T\<close>
  then have \<open>T = R \<union> (T - S)\<close> \<open>S = R \<union> U\<close> \<open>R \<inter> U = {}\<close>
    by auto
  from that \<open>U = S - T\<close> have \<open>p ` U = U\<close>
    by simp
  from \<open>p permutes S\<close> have \<open>bij_betw p (R \<union> U) (R \<union> U)\<close>
    by (simp add: permutes_imp_bij \<open>S = R \<union> U\<close>)
  moreover have \<open>bij_betw p U U\<close>
    using that \<open>U = S - T\<close> by (simp add: bij_betw_def permutes_inj_on)
  ultimately have \<open>bij_betw p R R\<close>
    using \<open>R \<inter> U = {}\<close> \<open>R \<inter> U = {}\<close> by (rule bij_betw_partition)
  then have \<open>p permutes R\<close>
  proof (rule bij_imp_permutes)
    fix x
    assume \<open>x \<notin> R\<close>
    with \<open>R = T \<inter> S\<close> \<open>p permutes S\<close> show \<open>p x = x\<close>
      by (cases \<open>x \<in> S\<close>) (auto simp add: permutes_not_in that(2))
  qed
  then have \<open>p permutes R \<union> (T - S)\<close>
    by (rule permutes_subset) simp
  with \<open>T = R \<union> (T - S)\<close> show ?thesis
    by simp
qed

lemma permutes_bij_inv_into: \<^marker>\<open>contributor \<open>Lukas Bulwahn\<close>\<close>
  fixes A :: "'a set"
    and B :: "'b set"
  assumes "p permutes A"
    and "bij_betw f A B"
  shows "(\<lambda>x. if x \<in> B then f (p (inv_into A f x)) else x) permutes B"
proof (rule bij_imp_permutes)
  from assms have "bij_betw p A A" "bij_betw f A B" "bij_betw (inv_into A f) B A"
    by (auto simp add: permutes_imp_bij bij_betw_inv_into)
  then have "bij_betw (f \<circ> p \<circ> inv_into A f) B B"
    by (simp add: bij_betw_trans)
  then show "bij_betw (\<lambda>x. if x \<in> B then f (p (inv_into A f x)) else x) B B"
    by (subst bij_betw_cong[where g="f \<circ> p \<circ> inv_into A f"]) auto
next
  fix x
  assume "x \<notin> B"
  then show "(if x \<in> B then f (p (inv_into A f x)) else x) = x" by auto
qed

lemma permutes_image_mset: \<^marker>\<open>contributor \<open>Lukas Bulwahn\<close>\<close>
  assumes "p permutes A"
  shows "image_mset p (mset_set A) = mset_set A"
  using assms by (metis image_mset_mset_set bij_betw_imp_inj_on permutes_imp_bij permutes_image)

lemma permutes_implies_image_mset_eq: \<^marker>\<open>contributor \<open>Lukas Bulwahn\<close>\<close>
  assumes "p permutes A" "\<And>x. x \<in> A \<Longrightarrow> f x = f' (p x)"
  shows "image_mset f' (mset_set A) = image_mset f (mset_set A)"
proof -
  have "f x = f' (p x)" if "x \<in># mset_set A" for x
    using assms(2)[of x] that by (cases "finite A") auto
  with assms have "image_mset f (mset_set A) = image_mset (f' \<circ> p) (mset_set A)"
    by (auto intro!: image_mset_cong)
  also have "\<dots> = image_mset f' (image_mset p (mset_set A))"
    by (simp add: image_mset.compositionality)
  also have "\<dots> = image_mset f' (mset_set A)"
  proof -
    from assms permutes_image_mset have "image_mset p (mset_set A) = mset_set A"
      by blast
    then show ?thesis by simp
  qed
  finally show ?thesis ..
qed


subsection \<open>Group properties\<close>

lemma permutes_compose: "p permutes S \<Longrightarrow> q permutes S \<Longrightarrow> q \<circ> p permutes S"
  unfolding permutes_def o_def by metis

lemma permutes_inv:
  assumes "p permutes S"
  shows "inv p permutes S"
  using assms unfolding permutes_def permutes_inv_eq[OF assms] by metis

lemma permutes_inv_inv:
  assumes "p permutes S"
  shows "inv (inv p) = p"
  unfolding fun_eq_iff permutes_inv_eq[OF assms] permutes_inv_eq[OF permutes_inv[OF assms]]
  by blast

lemma permutes_invI:
  assumes perm: "p permutes S"
    and inv: "\<And>x. x \<in> S \<Longrightarrow> p' (p x) = x"
    and outside: "\<And>x. x \<notin> S \<Longrightarrow> p' x = x"
  shows "inv p = p'"
proof
  show "inv p x = p' x" for x
  proof (cases "x \<in> S")
    case True
    from assms have "p' x = p' (p (inv p x))"
      by (simp add: permutes_inverses)
    also from permutes_inv[OF perm] True have "\<dots> = inv p x"
      by (subst inv) (simp_all add: permutes_in_image)
    finally show ?thesis ..
  next
    case False
    with permutes_inv[OF perm] show ?thesis
      by (simp_all add: outside permutes_not_in)
  qed
qed

lemma permutes_vimage: "f permutes A \<Longrightarrow> f -` A = A"
  by (simp add: bij_vimage_eq_inv_image permutes_bij permutes_image[OF permutes_inv])


subsection \<open>Mapping permutations with bijections\<close>

lemma bij_betw_permutations:
  assumes "bij_betw f A B"
  shows   "bij_betw (\<lambda>\<pi> x. if x \<in> B then f (\<pi> (inv_into A f x)) else x) 
             {\<pi>. \<pi> permutes A} {\<pi>. \<pi> permutes B}" (is "bij_betw ?f _ _")
proof -
  let ?g = "(\<lambda>\<pi> x. if x \<in> A then inv_into A f (\<pi> (f x)) else x)"
  show ?thesis
  proof (rule bij_betw_byWitness [of _ ?g], goal_cases)
    case 3
    show ?case using permutes_bij_inv_into[OF _ assms] by auto
  next
    case 4
    have bij_inv: "bij_betw (inv_into A f) B A" by (intro bij_betw_inv_into assms)
    {
      fix \<pi> assume "\<pi> permutes B"
      from permutes_bij_inv_into[OF this bij_inv] and assms
        have "(\<lambda>x. if x \<in> A then inv_into A f (\<pi> (f x)) else x) permutes A"
        by (simp add: inv_into_inv_into_eq cong: if_cong)
    }
    from this show ?case by (auto simp: permutes_inv)
  next
    case 1
    thus ?case using assms
      by (auto simp: fun_eq_iff permutes_not_in permutes_in_image bij_betw_inv_into_left
               dest: bij_betwE)
  next
    case 2
    moreover have "bij_betw (inv_into A f) B A"
      by (intro bij_betw_inv_into assms)
    ultimately show ?case using assms
      by (auto simp: fun_eq_iff permutes_not_in permutes_in_image bij_betw_inv_into_right 
               dest: bij_betwE)
  qed
qed

lemma bij_betw_derangements:
  assumes "bij_betw f A B"
  shows   "bij_betw (\<lambda>\<pi> x. if x \<in> B then f (\<pi> (inv_into A f x)) else x) 
             {\<pi>. \<pi> permutes A \<and> (\<forall>x\<in>A. \<pi> x \<noteq> x)} {\<pi>. \<pi> permutes B \<and> (\<forall>x\<in>B. \<pi> x \<noteq> x)}" 
           (is "bij_betw ?f _ _")
proof -
  let ?g = "(\<lambda>\<pi> x. if x \<in> A then inv_into A f (\<pi> (f x)) else x)"
  show ?thesis
  proof (rule bij_betw_byWitness [of _ ?g], goal_cases)
    case 3
    have "?f \<pi> x \<noteq> x" if "\<pi> permutes A" "\<And>x. x \<in> A \<Longrightarrow> \<pi> x \<noteq> x" "x \<in> B" for \<pi> x
      using that and assms by (metis bij_betwE bij_betw_imp_inj_on bij_betw_imp_surj_on
                                     inv_into_f_f inv_into_into permutes_imp_bij)
    with permutes_bij_inv_into[OF _ assms] show ?case by auto
  next
    case 4
    have bij_inv: "bij_betw (inv_into A f) B A" by (intro bij_betw_inv_into assms)
    have "?g \<pi> permutes A" if "\<pi> permutes B" for \<pi>
      using permutes_bij_inv_into[OF that bij_inv] and assms
      by (simp add: inv_into_inv_into_eq cong: if_cong)
    moreover have "?g \<pi> x \<noteq> x" if "\<pi> permutes B" "\<And>x. x \<in> B \<Longrightarrow> \<pi> x \<noteq> x" "x \<in> A" for \<pi> x
      using that and assms by (metis bij_betwE bij_betw_imp_surj_on f_inv_into_f permutes_imp_bij)
    ultimately show ?case by auto
  next
    case 1
    thus ?case using assms
      by (force simp: fun_eq_iff permutes_not_in permutes_in_image bij_betw_inv_into_left
                dest: bij_betwE)
  next
    case 2
    moreover have "bij_betw (inv_into A f) B A"
      by (intro bij_betw_inv_into assms)
    ultimately show ?case using assms
      by (force simp: fun_eq_iff permutes_not_in permutes_in_image bij_betw_inv_into_right 
                dest: bij_betwE)
  qed
qed


subsection \<open>The number of permutations on a finite set\<close>

lemma permutes_insert_lemma:
  assumes "p permutes (insert a S)"
  shows "transpose a (p a) \<circ> p permutes S"
  apply (rule permutes_superset[where S = "insert a S"])
  apply (rule permutes_compose[OF assms])
  apply (rule permutes_swap_id, simp)
  using permutes_in_image[OF assms, of a]
  apply simp
  apply (auto simp add: Ball_def)
  done

lemma permutes_insert: "{p. p permutes (insert a S)} =
  (\<lambda>(b, p). transpose a b \<circ> p) ` {(b, p). b \<in> insert a S \<and> p \<in> {p. p permutes S}}"
proof -
  have "p permutes insert a S \<longleftrightarrow>
    (\<exists>b q. p = transpose a b \<circ> q \<and> b \<in> insert a S \<and> q permutes S)" for p
  proof -
    have "\<exists>b q. p = transpose a b \<circ> q \<and> b \<in> insert a S \<and> q permutes S"
      if p: "p permutes insert a S"
    proof -
      let ?b = "p a"
      let ?q = "transpose a (p a) \<circ> p"
      have *: "p = transpose a ?b \<circ> ?q"
        by (simp add: fun_eq_iff o_assoc)
      have **: "?b \<in> insert a S"
        unfolding permutes_in_image[OF p] by simp
      from permutes_insert_lemma[OF p] * ** show ?thesis
        by blast
    qed
    moreover have "p permutes insert a S"
      if bq: "p = transpose a b \<circ> q" "b \<in> insert a S" "q permutes S" for b q
    proof -
      from permutes_subset[OF bq(3), of "insert a S"] have q: "q permutes insert a S"
        by auto
      have a: "a \<in> insert a S"
        by simp
      from bq(1) permutes_compose[OF q permutes_swap_id[OF a bq(2)]] show ?thesis
        by simp
    qed
    ultimately show ?thesis by blast
  qed
  then show ?thesis by auto
qed

lemma card_permutations:
  assumes "card S = n"
    and "finite S"
  shows "card {p. p permutes S} = fact n"
  using assms(2,1)
proof (induct arbitrary: n)
  case empty
  then show ?case by simp
next
  case (insert x F)
  {
    fix n
    assume card_insert: "card (insert x F) = n"
    let ?xF = "{p. p permutes insert x F}"
    let ?pF = "{p. p permutes F}"
    let ?pF' = "{(b, p). b \<in> insert x F \<and> p \<in> ?pF}"
    let ?g = "(\<lambda>(b, p). transpose x b \<circ> p)"
    have xfgpF': "?xF = ?g ` ?pF'"
      by (rule permutes_insert[of x F])
    from \<open>x \<notin> F\<close> \<open>finite F\<close> card_insert have Fs: "card F = n - 1"
      by auto
    from \<open>finite F\<close> insert.hyps Fs have pFs: "card ?pF = fact (n - 1)"
      by auto
    then have "finite ?pF"
      by (auto intro: card_ge_0_finite)
    with \<open>finite F\<close> card.insert_remove have pF'f: "finite ?pF'"
      apply (simp only: Collect_case_prod Collect_mem_eq)
      apply (rule finite_cartesian_product)
      apply simp_all
      done

    have ginj: "inj_on ?g ?pF'"
    proof -
      {
        fix b p c q
        assume bp: "(b, p) \<in> ?pF'"
        assume cq: "(c, q) \<in> ?pF'"
        assume eq: "?g (b, p) = ?g (c, q)"
        from bp cq have pF: "p permutes F" and qF: "q permutes F"
          by auto
        from pF \<open>x \<notin> F\<close> eq have "b = ?g (b, p) x"
          by (auto simp: permutes_def fun_upd_def fun_eq_iff)
        also from qF \<open>x \<notin> F\<close> eq have "\<dots> = ?g (c, q) x"
          by (auto simp: fun_upd_def fun_eq_iff)
        also from qF \<open>x \<notin> F\<close> have "\<dots> = c"
          by (auto simp: permutes_def fun_upd_def fun_eq_iff)
        finally have "b = c" .
        then have "transpose x b = transpose x c"
          by simp
        with eq have "transpose x b \<circ> p = transpose x b \<circ> q"
          by simp
        then have "transpose x b \<circ> (transpose x b \<circ> p) = transpose x b \<circ> (transpose x b \<circ> q)"
          by simp
        then have "p = q"
          by (simp add: o_assoc)
        with \<open>b = c\<close> have "(b, p) = (c, q)"
          by simp
      }
      then show ?thesis
        unfolding inj_on_def by blast
    qed
    from \<open>x \<notin> F\<close> \<open>finite F\<close> card_insert have "n \<noteq> 0"
      by auto
    then have "\<exists>m. n = Suc m"
      by presburger
    then obtain m where n: "n = Suc m"
      by blast
    from pFs card_insert have *: "card ?xF = fact n"
      unfolding xfgpF' card_image[OF ginj]
      using \<open>finite F\<close> \<open>finite ?pF\<close>
      by (simp only: Collect_case_prod Collect_mem_eq card_cartesian_product) (simp add: n)
    from finite_imageI[OF pF'f, of ?g] have xFf: "finite ?xF"
      by (simp add: xfgpF' n)
    from * have "card ?xF = fact n"
      unfolding xFf by blast
  }
  with insert show ?case by simp
qed

lemma finite_permutations:
  assumes "finite S"
  shows "finite {p. p permutes S}"
  using card_permutations[OF refl assms] by (auto intro: card_ge_0_finite)


subsection \<open>Hence a sort of induction principle composing by swaps\<close>

lemma permutes_induct [consumes 2, case_names id swap]:
  \<open>P p\<close> if \<open>p permutes S\<close> \<open>finite S\<close>
  and id: \<open>P id\<close>
  and swap: \<open>\<And>a b p. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> p permutes S \<Longrightarrow> P p \<Longrightarrow> P (transpose a b \<circ> p)\<close>
using \<open>finite S\<close> \<open>p permutes S\<close> swap proof (induction S arbitrary: p)
  case empty
  with id show ?case
    by (simp only: permutes_empty)
next
  case (insert x S p)
  define q where \<open>q = transpose x (p x) \<circ> p\<close>
  then have swap_q: \<open>transpose x (p x) \<circ> q = p\<close>
    by (simp add: o_assoc)
  from \<open>p permutes insert x S\<close> have \<open>q permutes S\<close>
    by (simp add: q_def permutes_insert_lemma)
  then have \<open>q permutes insert x S\<close>
    by (simp add: permutes_imp_permutes_insert)
  from \<open>q permutes S\<close> have \<open>P q\<close>
    by (auto intro: insert.IH insert.prems(2) permutes_imp_permutes_insert)
  have \<open>x \<in> insert x S\<close>
    by simp
  moreover from \<open>p permutes insert x S\<close> have \<open>p x \<in> insert x S\<close>
    using permutes_in_image [of p \<open>insert x S\<close> x] by simp
  ultimately have \<open>P (transpose x (p x) \<circ> q)\<close>
    using \<open>q permutes insert x S\<close> \<open>P q\<close>
    by (rule insert.prems(2))
  then show ?case
    by (simp add: swap_q)
qed

lemma permutes_rev_induct [consumes 2, case_names id swap]:
  \<open>P p\<close> if \<open>p permutes S\<close> \<open>finite S\<close>
  and id': \<open>P id\<close>
  and swap': \<open>\<And>a b p. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> p permutes S \<Longrightarrow> P p \<Longrightarrow> P (p \<circ> transpose a b)\<close>
using \<open>p permutes S\<close> \<open>finite S\<close> proof (induction rule: permutes_induct)
  case id
  from id' show ?case .
next
  case (swap a b p)
  then have \<open>bij p\<close>
    using permutes_bij by blast
  have \<open>P (p \<circ> transpose (inv p a) (inv p b))\<close>
    by (rule swap') (auto simp add: swap permutes_in_image permutes_inv)
  also have \<open>p \<circ> transpose (inv p a) (inv p b) = transpose a b \<circ> p\<close>
    using \<open>bij p\<close> by (rule transpose_comp_eq [symmetric])
  finally show ?case .
qed


subsection \<open>Permutations of index set for iterated operations\<close>

lemma (in comm_monoid_set) permute:
  assumes "p permutes S"
  shows "F g S = F (g \<circ> p) S"
proof -
  from \<open>p permutes S\<close> have "inj p"
    by (rule permutes_inj)
  then have "inj_on p S"
    by (auto intro: subset_inj_on)
  then have "F g (p ` S) = F (g \<circ> p) S"
    by (rule reindex)
  moreover from \<open>p permutes S\<close> have "p ` S = S"
    by (rule permutes_image)
  ultimately show ?thesis
    by simp
qed


subsection \<open>Permutations as transposition sequences\<close>

inductive swapidseq :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where
    id[simp]: "swapidseq 0 id"
  | comp_Suc: "swapidseq n p \<Longrightarrow> a \<noteq> b \<Longrightarrow> swapidseq (Suc n) (transpose a b \<circ> p)"

declare id[unfolded id_def, simp]

definition "permutation p \<longleftrightarrow> (\<exists>n. swapidseq n p)"


subsection \<open>Some closure properties of the set of permutations, with lengths\<close>

lemma permutation_id[simp]: "permutation id"
  unfolding permutation_def by (rule exI[where x=0]) simp

declare permutation_id[unfolded id_def, simp]

lemma swapidseq_swap: "swapidseq (if a = b then 0 else 1) (transpose a b)"
  apply clarsimp
  using comp_Suc[of 0 id a b]
  apply simp
  done

lemma permutation_swap_id: "permutation (transpose a b)"
proof (cases "a = b")
  case True
  then show ?thesis by simp
next
  case False
  then show ?thesis
    unfolding permutation_def
    using swapidseq_swap[of a b] by blast
qed


lemma swapidseq_comp_add: "swapidseq n p \<Longrightarrow> swapidseq m q \<Longrightarrow> swapidseq (n + m) (p \<circ> q)"
proof (induct n p arbitrary: m q rule: swapidseq.induct)
  case (id m q)
  then show ?case by simp
next
  case (comp_Suc n p a b m q)
  have eq: "Suc n + m = Suc (n + m)"
    by arith
  show ?case
    apply (simp only: eq comp_assoc)
    apply (rule swapidseq.comp_Suc)
    using comp_Suc.hyps(2)[OF comp_Suc.prems] comp_Suc.hyps(3)
     apply blast+
    done
qed

lemma permutation_compose: "permutation p \<Longrightarrow> permutation q \<Longrightarrow> permutation (p \<circ> q)"
  unfolding permutation_def using swapidseq_comp_add[of _ p _ q] by metis

lemma swapidseq_endswap: "swapidseq n p \<Longrightarrow> a \<noteq> b \<Longrightarrow> swapidseq (Suc n) (p \<circ> transpose a b)"
  by (induct n p rule: swapidseq.induct)
    (use swapidseq_swap[of a b] in \<open>auto simp add: comp_assoc intro: swapidseq.comp_Suc\<close>)

lemma swapidseq_inverse_exists: "swapidseq n p \<Longrightarrow> \<exists>q. swapidseq n q \<and> p \<circ> q = id \<and> q \<circ> p = id"
proof (induct n p rule: swapidseq.induct)
  case id
  then show ?case
    by (rule exI[where x=id]) simp
next
  case (comp_Suc n p a b)
  from comp_Suc.hyps obtain q where q: "swapidseq n q" "p \<circ> q = id" "q \<circ> p = id"
    by blast
  let ?q = "q \<circ> transpose a b"
  note H = comp_Suc.hyps
  from swapidseq_swap[of a b] H(3) have *: "swapidseq 1 (transpose a b)"
    by simp
  from swapidseq_comp_add[OF q(1) *] have **: "swapidseq (Suc n) ?q"
    by simp
  have "transpose a b \<circ> p \<circ> ?q = transpose a b \<circ> (p \<circ> q) \<circ> transpose a b"
    by (simp add: o_assoc)
  also have "\<dots> = id"
    by (simp add: q(2))
  finally have ***: "transpose a b \<circ> p \<circ> ?q = id" .
  have "?q \<circ> (transpose a b \<circ> p) = q \<circ> (transpose a b \<circ> transpose a b) \<circ> p"
    by (simp only: o_assoc)
  then have "?q \<circ> (transpose a b \<circ> p) = id"
    by (simp add: q(3))
  with ** *** show ?case
    by blast
qed

lemma swapidseq_inverse:
  assumes "swapidseq n p"
  shows "swapidseq n (inv p)"
  using swapidseq_inverse_exists[OF assms] inv_unique_comp[of p] by auto

lemma permutation_inverse: "permutation p \<Longrightarrow> permutation (inv p)"
  using permutation_def swapidseq_inverse by blast



subsection \<open>Various combinations of transpositions with 2, 1 and 0 common elements\<close>

lemma swap_id_common:" a \<noteq> c \<Longrightarrow> b \<noteq> c \<Longrightarrow>
  transpose a b \<circ> transpose a c = transpose b c \<circ> transpose a b"
  by (simp add: fun_eq_iff transpose_def)

lemma swap_id_common': "a \<noteq> b \<Longrightarrow> a \<noteq> c \<Longrightarrow>
  transpose a c \<circ> transpose b c = transpose b c \<circ> transpose a b"
  by (simp add: fun_eq_iff transpose_def)

lemma swap_id_independent: "a \<noteq> c \<Longrightarrow> a \<noteq> d \<Longrightarrow> b \<noteq> c \<Longrightarrow> b \<noteq> d \<Longrightarrow>
  transpose a b \<circ> transpose c d = transpose c d \<circ> transpose a b"
  by (simp add: fun_eq_iff transpose_def)


subsection \<open>The identity map only has even transposition sequences\<close>

lemma symmetry_lemma:
  assumes "\<And>a b c d. P a b c d \<Longrightarrow> P a b d c"
    and "\<And>a b c d. a \<noteq> b \<Longrightarrow> c \<noteq> d \<Longrightarrow>
      a = c \<and> b = d \<or> a = c \<and> b \<noteq> d \<or> a \<noteq> c \<and> b = d \<or> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<Longrightarrow>
      P a b c d"
  shows "\<And>a b c d. a \<noteq> b \<longrightarrow> c \<noteq> d \<longrightarrow>  P a b c d"
  using assms by metis

lemma swap_general: "a \<noteq> b \<Longrightarrow> c \<noteq> d \<Longrightarrow>
  transpose a b \<circ> transpose c d = id \<or>
  (\<exists>x y z. x \<noteq> a \<and> y \<noteq> a \<and> z \<noteq> a \<and> x \<noteq> y \<and>
    transpose a b \<circ> transpose c d = transpose x y \<circ> transpose a z)"
proof -
  assume neq: "a \<noteq> b" "c \<noteq> d"
  have "a \<noteq> b \<longrightarrow> c \<noteq> d \<longrightarrow>
    (transpose a b \<circ> transpose c d = id \<or>
      (\<exists>x y z. x \<noteq> a \<and> y \<noteq> a \<and> z \<noteq> a \<and> x \<noteq> y \<and>
        transpose a b \<circ> transpose c d = transpose x y \<circ> transpose a z))"
    apply (rule symmetry_lemma[where a=a and b=b and c=c and d=d])
     apply (simp_all only: ac_simps)
    apply (metis id_comp swap_id_common swap_id_common' swap_id_independent transpose_comp_involutory)
    done
  with neq show ?thesis by metis
qed

lemma swapidseq_id_iff[simp]: "swapidseq 0 p \<longleftrightarrow> p = id"
  using swapidseq.cases[of 0 p "p = id"] by auto

lemma swapidseq_cases: "swapidseq n p \<longleftrightarrow>
    n = 0 \<and> p = id \<or> (\<exists>a b q m. n = Suc m \<and> p = transpose a b \<circ> q \<and> swapidseq m q \<and> a \<noteq> b)"
  apply (rule iffI)
   apply (erule swapidseq.cases[of n p])
    apply simp
   apply (rule disjI2)
   apply (rule_tac x= "a" in exI)
   apply (rule_tac x= "b" in exI)
   apply (rule_tac x= "pa" in exI)
   apply (rule_tac x= "na" in exI)
   apply simp
  apply auto
  apply (rule comp_Suc, simp_all)
  done

lemma fixing_swapidseq_decrease:
  assumes "swapidseq n p"
    and "a \<noteq> b"
    and "(transpose a b \<circ> p) a = a"
  shows "n \<noteq> 0 \<and> swapidseq (n - 1) (transpose a b \<circ> p)"
  using assms
proof (induct n arbitrary: p a b)
  case 0
  then show ?case
    by (auto simp add: fun_upd_def)
next
  case (Suc n p a b)
  from Suc.prems(1) swapidseq_cases[of "Suc n" p]
  obtain c d q m where
    cdqm: "Suc n = Suc m" "p = transpose c d \<circ> q" "swapidseq m q" "c \<noteq> d" "n = m"
    by auto
  consider "transpose a b \<circ> transpose c d = id"
    | x y z where "x \<noteq> a" "y \<noteq> a" "z \<noteq> a" "x \<noteq> y"
      "transpose a b \<circ> transpose c d = transpose x y \<circ> transpose a z"
    using swap_general[OF Suc.prems(2) cdqm(4)] by metis
  then show ?case
  proof cases
    case 1
    then show ?thesis
      by (simp only: cdqm o_assoc) (simp add: cdqm)
  next
    case prems: 2
    then have az: "a \<noteq> z"
      by simp
    from prems have *: "(transpose x y \<circ> h) a = a \<longleftrightarrow> h a = a" for h
      by (simp add: transpose_def)
    from cdqm(2) have "transpose a b \<circ> p = transpose a b \<circ> (transpose c d \<circ> q)"
      by simp
    then have "transpose a b \<circ> p = transpose x y \<circ> (transpose a z \<circ> q)"
      by (simp add: o_assoc prems)
    then have "(transpose a b \<circ> p) a = (transpose x y \<circ> (transpose a z \<circ> q)) a"
      by simp
    then have "(transpose x y \<circ> (transpose a z \<circ> q)) a = a"
      unfolding Suc by metis
    then have "(transpose a z \<circ> q) a = a"
      by (simp only: *)
    from Suc.hyps[OF cdqm(3)[ unfolded cdqm(5)[symmetric]] az this]
    have **: "swapidseq (n - 1) (transpose a z \<circ> q)" "n \<noteq> 0"
      by blast+
    from \<open>n \<noteq> 0\<close> have ***: "Suc n - 1 = Suc (n - 1)"
      by auto
    show ?thesis
      apply (simp only: cdqm(2) prems o_assoc ***)
      apply (simp only: Suc_not_Zero simp_thms comp_assoc)
      apply (rule comp_Suc)
      using ** prems
       apply blast+
      done
  qed
qed

lemma swapidseq_identity_even:
  assumes "swapidseq n (id :: 'a \<Rightarrow> 'a)"
  shows "even n"
  using \<open>swapidseq n id\<close>
proof (induct n rule: nat_less_induct)
  case H: (1 n)
  consider "n = 0"
    | a b :: 'a and q m where "n = Suc m" "id = transpose a b \<circ> q" "swapidseq m q" "a \<noteq> b"
    using H(2)[unfolded swapidseq_cases[of n id]] by auto
  then show ?case
  proof cases
    case 1
    then show ?thesis by presburger
  next
    case h: 2
    from fixing_swapidseq_decrease[OF h(3,4), unfolded h(2)[symmetric]]
    have m: "m \<noteq> 0" "swapidseq (m - 1) (id :: 'a \<Rightarrow> 'a)"
      by auto
    from h m have mn: "m - 1 < n"
      by arith
    from H(1)[rule_format, OF mn m(2)] h(1) m(1) show ?thesis
      by presburger
  qed
qed


subsection \<open>Therefore we have a welldefined notion of parity\<close>

definition "evenperm p = even (SOME n. swapidseq n p)"

lemma swapidseq_even_even:
  assumes m: "swapidseq m p"
    and n: "swapidseq n p"
  shows "even m \<longleftrightarrow> even n"
proof -
  from swapidseq_inverse_exists[OF n] obtain q where q: "swapidseq n q" "p \<circ> q = id" "q \<circ> p = id"
    by blast
  from swapidseq_identity_even[OF swapidseq_comp_add[OF m q(1), unfolded q]] show ?thesis
    by arith
qed

lemma evenperm_unique:
  assumes p: "swapidseq n p"
    and n:"even n = b"
  shows "evenperm p = b"
  unfolding n[symmetric] evenperm_def
  apply (rule swapidseq_even_even[where p = p])
   apply (rule someI[where x = n])
  using p
   apply blast+
  done


subsection \<open>And it has the expected composition properties\<close>

lemma evenperm_id[simp]: "evenperm id = True"
  by (rule evenperm_unique[where n = 0]) simp_all

lemma evenperm_identity [simp]:
  \<open>evenperm (\<lambda>x. x)\<close>
  using evenperm_id by (simp add: id_def [abs_def])

lemma evenperm_swap: "evenperm (transpose a b) = (a = b)"
  by (rule evenperm_unique[where n="if a = b then 0 else 1"]) (simp_all add: swapidseq_swap)

lemma evenperm_comp:
  assumes "permutation p" "permutation q"
  shows "evenperm (p \<circ> q) \<longleftrightarrow> evenperm p = evenperm q"
proof -
  from assms obtain n m where n: "swapidseq n p" and m: "swapidseq m q"
    unfolding permutation_def by blast
  have "even (n + m) \<longleftrightarrow> (even n \<longleftrightarrow> even m)"
    by arith
  from evenperm_unique[OF n refl] evenperm_unique[OF m refl]
    and evenperm_unique[OF swapidseq_comp_add[OF n m] this] show ?thesis
    by blast
qed

lemma evenperm_inv:
  assumes "permutation p"
  shows "evenperm (inv p) = evenperm p"
proof -
  from assms obtain n where n: "swapidseq n p"
    unfolding permutation_def by blast
  show ?thesis
    by (rule evenperm_unique[OF swapidseq_inverse[OF n] evenperm_unique[OF n refl, symmetric]])
qed


subsection \<open>A more abstract characterization of permutations\<close>

lemma permutation_bijective:
  assumes "permutation p"
  shows "bij p"
proof -
  from assms obtain n where n: "swapidseq n p"
    unfolding permutation_def by blast
  from swapidseq_inverse_exists[OF n] obtain q where q: "swapidseq n q" "p \<circ> q = id" "q \<circ> p = id"
    by blast
  then show ?thesis
    unfolding bij_iff
    apply (auto simp add: fun_eq_iff)
    apply metis
    done
qed

lemma permutation_finite_support:
  assumes "permutation p"
  shows "finite {x. p x \<noteq> x}"
proof -
  from assms obtain n where "swapidseq n p"
    unfolding permutation_def by blast
  then show ?thesis
  proof (induct n p rule: swapidseq.induct)
    case id
    then show ?case by simp
  next
    case (comp_Suc n p a b)
    let ?S = "insert a (insert b {x. p x \<noteq> x})"
    from comp_Suc.hyps(2) have *: "finite ?S"
      by simp
    from \<open>a \<noteq> b\<close> have **: "{x. (transpose a b \<circ> p) x \<noteq> x} \<subseteq> ?S"
      by auto
    show ?case
      by (rule finite_subset[OF ** *])
  qed
qed

lemma permutation_lemma:
  assumes "finite S"
    and "bij p"
    and "\<forall>x. x \<notin> S \<longrightarrow> p x = x"
  shows "permutation p"
  using assms
proof (induct S arbitrary: p rule: finite_induct)
  case empty
  then show ?case
    by simp
next
  case (insert a F p)
  let ?r = "transpose a (p a) \<circ> p"
  let ?q = "transpose a (p a) \<circ> ?r"
  have *: "?r a = a"
    by simp
  from insert * have **: "\<forall>x. x \<notin> F \<longrightarrow> ?r x = x"
    by (metis bij_pointE comp_apply id_apply insert_iff swap_apply(3))
  have "bij ?r"
    using insert by (simp add: bij_comp)
  have "permutation ?r"
    by (rule insert(3)[OF \<open>bij ?r\<close> **])
  then have "permutation ?q"
    by (simp add: permutation_compose permutation_swap_id)
  then show ?case
    by (simp add: o_assoc)
qed

lemma permutation: "permutation p \<longleftrightarrow> bij p \<and> finite {x. p x \<noteq> x}"
  (is "?lhs \<longleftrightarrow> ?b \<and> ?f")
proof
  assume ?lhs
  with permutation_bijective permutation_finite_support show "?b \<and> ?f"
    by auto
next
  assume "?b \<and> ?f"
  then have "?f" "?b" by blast+
  from permutation_lemma[OF this] show ?lhs
    by blast
qed

lemma permutation_inverse_works:
  assumes "permutation p"
  shows "inv p \<circ> p = id"
    and "p \<circ> inv p = id"
  using permutation_bijective [OF assms] by (auto simp: bij_def inj_iff surj_iff)

lemma permutation_inverse_compose:
  assumes p: "permutation p"
    and q: "permutation q"
  shows "inv (p \<circ> q) = inv q \<circ> inv p"
proof -
  note ps = permutation_inverse_works[OF p]
  note qs = permutation_inverse_works[OF q]
  have "p \<circ> q \<circ> (inv q \<circ> inv p) = p \<circ> (q \<circ> inv q) \<circ> inv p"
    by (simp add: o_assoc)
  also have "\<dots> = id"
    by (simp add: ps qs)
  finally have *: "p \<circ> q \<circ> (inv q \<circ> inv p) = id" .
  have "inv q \<circ> inv p \<circ> (p \<circ> q) = inv q \<circ> (inv p \<circ> p) \<circ> q"
    by (simp add: o_assoc)
  also have "\<dots> = id"
    by (simp add: ps qs)
  finally have **: "inv q \<circ> inv p \<circ> (p \<circ> q) = id" .
  show ?thesis
    by (rule inv_unique_comp[OF * **])
qed


subsection \<open>Relation to \<open>permutes\<close>\<close>

lemma permutes_imp_permutation:
  \<open>permutation p\<close> if \<open>finite S\<close> \<open>p permutes S\<close>
proof -
  from \<open>p permutes S\<close> have \<open>{x. p x \<noteq> x} \<subseteq> S\<close>
    by (auto dest: permutes_not_in)
  then have \<open>finite {x. p x \<noteq> x}\<close>
    using \<open>finite S\<close> by (rule finite_subset)
  moreover from \<open>p permutes S\<close> have \<open>bij p\<close>
    by (auto dest: permutes_bij)
  ultimately show ?thesis
    by (simp add: permutation)
qed

lemma permutation_permutesE:
  assumes \<open>permutation p\<close>
  obtains S where \<open>finite S\<close> \<open>p permutes S\<close>
proof -
  from assms have fin: \<open>finite {x. p x \<noteq> x}\<close>
    by (simp add: permutation)
  from assms have \<open>bij p\<close>
    by (simp add: permutation)
  also have \<open>UNIV = {x. p x \<noteq> x} \<union> {x. p x = x}\<close>
    by auto
  finally have \<open>bij_betw p {x. p x \<noteq> x} {x. p x \<noteq> x}\<close>
    by (rule bij_betw_partition) (auto simp add: bij_betw_fixpoints)
  then have \<open>p permutes {x. p x \<noteq> x}\<close>
    by (auto intro: bij_imp_permutes)
  with fin show thesis ..
qed

lemma permutation_permutes: "permutation p \<longleftrightarrow> (\<exists>S. finite S \<and> p permutes S)"
  by (auto elim: permutation_permutesE intro: permutes_imp_permutation)


subsection \<open>Sign of a permutation as a real number\<close>

definition sign :: \<open>('a \<Rightarrow> 'a) \<Rightarrow> int\<close> \<comment> \<open>TODO: prefer less generic name\<close>
  where \<open>sign p = (if evenperm p then 1 else - 1)\<close>

lemma sign_cases [case_names even odd]:
  obtains \<open>sign p = 1\<close> | \<open>sign p = - 1\<close>
  by (cases \<open>evenperm p\<close>) (simp_all add: sign_def)

lemma sign_nz [simp]: "sign p \<noteq> 0"
  by (cases p rule: sign_cases) simp_all

lemma sign_id [simp]: "sign id = 1"
  by (simp add: sign_def)

lemma sign_identity [simp]:
  \<open>sign (\<lambda>x. x) = 1\<close>
  by (simp add: sign_def)

lemma sign_inverse: "permutation p \<Longrightarrow> sign (inv p) = sign p"
  by (simp add: sign_def evenperm_inv)

lemma sign_compose: "permutation p \<Longrightarrow> permutation q \<Longrightarrow> sign (p \<circ> q) = sign p * sign q"
  by (simp add: sign_def evenperm_comp)

lemma sign_swap_id: "sign (transpose a b) = (if a = b then 1 else - 1)"
  by (simp add: sign_def evenperm_swap)

lemma sign_idempotent [simp]: "sign p * sign p = 1"
  by (simp add: sign_def)

lemma sign_left_idempotent [simp]:
  \<open>sign p * (sign p * sign q) = sign q\<close>
  by (simp add: sign_def)

term "(bij, bij_betw, permutation)"


subsection \<open>Permuting a list\<close>

text \<open>This function permutes a list by applying a permutation to the indices.\<close>

definition permute_list :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "permute_list f xs = map (\<lambda>i. xs ! (f i)) [0..<length xs]"

lemma permute_list_map:
  assumes "f permutes {..<length xs}"
  shows "permute_list f (map g xs) = map g (permute_list f xs)"
  using permutes_in_image[OF assms] by (auto simp: permute_list_def)

lemma permute_list_nth:
  assumes "f permutes {..<length xs}" "i < length xs"
  shows "permute_list f xs ! i = xs ! f i"
  using permutes_in_image[OF assms(1)] assms(2)
  by (simp add: permute_list_def)

lemma permute_list_Nil [simp]: "permute_list f [] = []"
  by (simp add: permute_list_def)

lemma length_permute_list [simp]: "length (permute_list f xs) = length xs"
  by (simp add: permute_list_def)

lemma permute_list_compose:
  assumes "g permutes {..<length xs}"
  shows "permute_list (f \<circ> g) xs = permute_list g (permute_list f xs)"
  using assms[THEN permutes_in_image] by (auto simp add: permute_list_def)

lemma permute_list_ident [simp]: "permute_list (\<lambda>x. x) xs = xs"
  by (simp add: permute_list_def map_nth)

lemma permute_list_id [simp]: "permute_list id xs = xs"
  by (simp add: id_def)

lemma mset_permute_list [simp]:
  fixes xs :: "'a list"
  assumes "f permutes {..<length xs}"
  shows "mset (permute_list f xs) = mset xs"
proof (rule multiset_eqI)
  fix y :: 'a
  from assms have [simp]: "f x < length xs \<longleftrightarrow> x < length xs" for x
    using permutes_in_image[OF assms] by auto
  have "count (mset (permute_list f xs)) y = card ((\<lambda>i. xs ! f i) -` {y} \<inter> {..<length xs})"
    by (simp add: permute_list_def count_image_mset atLeast0LessThan)
  also have "(\<lambda>i. xs ! f i) -` {y} \<inter> {..<length xs} = f -` {i. i < length xs \<and> y = xs ! i}"
    by auto
  also from assms have "card \<dots> = card {i. i < length xs \<and> y = xs ! i}"
    by (intro card_vimage_inj) (auto simp: permutes_inj permutes_surj)
  also have "\<dots> = count (mset xs) y"
    by (simp add: count_mset length_filter_conv_card)
  finally show "count (mset (permute_list f xs)) y = count (mset xs) y"
    by simp
qed

lemma set_permute_list [simp]:
  assumes "f permutes {..<length xs}"
  shows "set (permute_list f xs) = set xs"
  by (rule mset_eq_setD[OF mset_permute_list]) fact

lemma distinct_permute_list [simp]:
  assumes "f permutes {..<length xs}"
  shows "distinct (permute_list f xs) = distinct xs"
  by (simp add: distinct_count_atmost_1 assms)

lemma permute_list_zip:
  assumes "f permutes A" "A = {..<length xs}"
  assumes [simp]: "length xs = length ys"
  shows "permute_list f (zip xs ys) = zip (permute_list f xs) (permute_list f ys)"
proof -
  from permutes_in_image[OF assms(1)] assms(2) have *: "f i < length ys \<longleftrightarrow> i < length ys" for i
    by simp
  have "permute_list f (zip xs ys) = map (\<lambda>i. zip xs ys ! f i) [0..<length ys]"
    by (simp_all add: permute_list_def zip_map_map)
  also have "\<dots> = map (\<lambda>(x, y). (xs ! f x, ys ! f y)) (zip [0..<length ys] [0..<length ys])"
    by (intro nth_equalityI) (simp_all add: *)
  also have "\<dots> = zip (permute_list f xs) (permute_list f ys)"
    by (simp_all add: permute_list_def zip_map_map)
  finally show ?thesis .
qed

lemma map_of_permute:
  assumes "\<sigma> permutes fst ` set xs"
  shows "map_of xs \<circ> \<sigma> = map_of (map (\<lambda>(x,y). (inv \<sigma> x, y)) xs)"
    (is "_ = map_of (map ?f _)")
proof
  from assms have "inj \<sigma>" "surj \<sigma>"
    by (simp_all add: permutes_inj permutes_surj)
  then show "(map_of xs \<circ> \<sigma>) x = map_of (map ?f xs) x" for x
    by (induct xs) (auto simp: inv_f_f surj_f_inv_f)
qed


subsection \<open>More lemmas about permutations\<close>

lemma permutes_in_funpow_image: \<^marker>\<open>contributor \<open>Lars Noschinski\<close>\<close>
  assumes "f permutes S" "x \<in> S"
  shows "(f ^^ n) x \<in> S"
  using assms by (induction n) (auto simp: permutes_in_image)

lemma permutation_self: \<^marker>\<open>contributor \<open>Lars Noschinski\<close>\<close>
  assumes \<open>permutation p\<close>
  obtains n where \<open>n > 0\<close> \<open>(p ^^ n) x = x\<close>
proof (cases \<open>p x = x\<close>)
  case True
  with that [of 1] show thesis by simp
next
  case False
  from \<open>permutation p\<close> have \<open>inj p\<close>
    by (intro permutation_bijective bij_is_inj)
  moreover from \<open>p x \<noteq> x\<close> have \<open>(p ^^ Suc n) x \<noteq> (p ^^ n) x\<close> for n
  proof (induction n arbitrary: x)
    case 0 then show ?case by simp
  next
    case (Suc n)
    have "p (p x) \<noteq> p x"
    proof (rule notI)
      assume "p (p x) = p x"
      then show False using \<open>p x \<noteq> x\<close> \<open>inj p\<close> by (simp add: inj_eq)
    qed
    have "(p ^^ Suc (Suc n)) x = (p ^^ Suc n) (p x)"
      by (simp add: funpow_swap1)
    also have "\<dots> \<noteq> (p ^^ n) (p x)"
      by (rule Suc) fact
    also have "(p ^^ n) (p x) = (p ^^ Suc n) x"
      by (simp add: funpow_swap1)
    finally show ?case by simp
  qed
  then have "{y. \<exists>n. y = (p ^^ n) x} \<subseteq> {x. p x \<noteq> x}"
    by auto
  then have "finite {y. \<exists>n. y = (p ^^ n) x}"
    using permutation_finite_support[OF assms] by (rule finite_subset)
  ultimately obtain n where \<open>n > 0\<close> \<open>(p ^^ n) x = x\<close>
    by (rule funpow_inj_finite)
  with that [of n] show thesis by blast
qed

text \<open>The following few lemmas were contributed by Lukas Bulwahn.\<close>

lemma count_image_mset_eq_card_vimage:
  assumes "finite A"
  shows "count (image_mset f (mset_set A)) b = card {a \<in> A. f a = b}"
  using assms
proof (induct A)
  case empty
  show ?case by simp
next
  case (insert x F)
  show ?case
  proof (cases "f x = b")
    case True
    with insert.hyps
    have "count (image_mset f (mset_set (insert x F))) b = Suc (card {a \<in> F. f a = f x})"
      by auto
    also from insert.hyps(1,2) have "\<dots> = card (insert x {a \<in> F. f a = f x})"
      by simp
    also from \<open>f x = b\<close> have "card (insert x {a \<in> F. f a = f x}) = card {a \<in> insert x F. f a = b}"
      by (auto intro: arg_cong[where f="card"])
    finally show ?thesis
      using insert by auto
  next
    case False
    then have "{a \<in> F. f a = b} = {a \<in> insert x F. f a = b}"
      by auto
    with insert False show ?thesis
      by simp
  qed
qed

\<comment> \<open>Prove \<open>image_mset_eq_implies_permutes\<close> ...\<close>
lemma image_mset_eq_implies_permutes:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "finite A"
    and mset_eq: "image_mset f (mset_set A) = image_mset f' (mset_set A)"
  obtains p where "p permutes A" and "\<forall>x\<in>A. f x = f' (p x)"
proof -
  from \<open>finite A\<close> have [simp]: "finite {a \<in> A. f a = (b::'b)}" for f b by auto
  have "f ` A = f' ` A"
  proof -
    from \<open>finite A\<close> have "f ` A = f ` (set_mset (mset_set A))"
      by simp
    also have "\<dots> = f' ` set_mset (mset_set A)"
      by (metis mset_eq multiset.set_map)
    also from \<open>finite A\<close> have "\<dots> = f' ` A"
      by simp
    finally show ?thesis .
  qed
  have "\<forall>b\<in>(f ` A). \<exists>p. bij_betw p {a \<in> A. f a = b} {a \<in> A. f' a = b}"
  proof
    fix b
    from mset_eq have "count (image_mset f (mset_set A)) b = count (image_mset f' (mset_set A)) b"
      by simp
    with \<open>finite A\<close> have "card {a \<in> A. f a = b} = card {a \<in> A. f' a = b}"
      by (simp add: count_image_mset_eq_card_vimage)
    then show "\<exists>p. bij_betw p {a\<in>A. f a = b} {a \<in> A. f' a = b}"
      by (intro finite_same_card_bij) simp_all
  qed
  then have "\<exists>p. \<forall>b\<in>f ` A. bij_betw (p b) {a \<in> A. f a = b} {a \<in> A. f' a = b}"
    by (rule bchoice)
  then obtain p where p: "\<forall>b\<in>f ` A. bij_betw (p b) {a \<in> A. f a = b} {a \<in> A. f' a = b}" ..
  define p' where "p' = (\<lambda>a. if a \<in> A then p (f a) a else a)"
  have "p' permutes A"
  proof (rule bij_imp_permutes)
    have "disjoint_family_on (\<lambda>i. {a \<in> A. f' a = i}) (f ` A)"
      by (auto simp: disjoint_family_on_def)
    moreover
    have "bij_betw (\<lambda>a. p (f a) a) {a \<in> A. f a = b} {a \<in> A. f' a = b}" if "b \<in> f ` A" for b
      using p that by (subst bij_betw_cong[where g="p b"]) auto
    ultimately
    have "bij_betw (\<lambda>a. p (f a) a) (\<Union>b\<in>f ` A. {a \<in> A. f a = b}) (\<Union>b\<in>f ` A. {a \<in> A. f' a = b})"
      by (rule bij_betw_UNION_disjoint)
    moreover have "(\<Union>b\<in>f ` A. {a \<in> A. f a = b}) = A"
      by auto
    moreover from \<open>f ` A = f' ` A\<close> have "(\<Union>b\<in>f ` A. {a \<in> A. f' a = b}) = A"
      by auto
    ultimately show "bij_betw p' A A"
      unfolding p'_def by (subst bij_betw_cong[where g="(\<lambda>a. p (f a) a)"]) auto
  next
    show "\<And>x. x \<notin> A \<Longrightarrow> p' x = x"
      by (simp add: p'_def)
  qed
  moreover from p have "\<forall>x\<in>A. f x = f' (p' x)"
    unfolding p'_def using bij_betwE by fastforce
  ultimately show ?thesis ..
qed

\<comment> \<open>... and derive the existing property:\<close>
lemma mset_eq_permutation:
  fixes xs ys :: "'a list"
  assumes mset_eq: "mset xs = mset ys"
  obtains p where "p permutes {..<length ys}" "permute_list p ys = xs"
proof -
  from mset_eq have length_eq: "length xs = length ys"
    by (rule mset_eq_length)
  have "mset_set {..<length ys} = mset [0..<length ys]"
    by (rule mset_set_upto_eq_mset_upto)
  with mset_eq length_eq have "image_mset (\<lambda>i. xs ! i) (mset_set {..<length ys}) =
    image_mset (\<lambda>i. ys ! i) (mset_set {..<length ys})"
    by (metis map_nth mset_map)
  from image_mset_eq_implies_permutes[OF _ this]
  obtain p where p: "p permutes {..<length ys}" and "\<forall>i\<in>{..<length ys}. xs ! i = ys ! (p i)"
    by auto
  with length_eq have "permute_list p ys = xs"
    by (auto intro!: nth_equalityI simp: permute_list_nth)
  with p show thesis ..
qed

lemma permutes_natset_le:
  fixes S :: "'a::wellorder set"
  assumes "p permutes S"
    and "\<forall>i \<in> S. p i \<le> i"
  shows "p = id"
proof -
  have "p n = n" for n
    using assms
  proof (induct n arbitrary: S rule: less_induct)
    case (less n)
    show ?case
    proof (cases "n \<in> S")
      case False
      with less(2) show ?thesis
        unfolding permutes_def by metis
    next
      case True
      with less(3) have "p n < n \<or> p n = n"
        by auto
      then show ?thesis
      proof
        assume "p n < n"
        with less have "p (p n) = p n"
          by metis
        with permutes_inj[OF less(2)] have "p n = n"
          unfolding inj_def by blast
        with \<open>p n < n\<close> have False
          by simp
        then show ?thesis ..
      qed
    qed
  qed
  then show ?thesis by (auto simp: fun_eq_iff)
qed

lemma permutes_natset_ge:
  fixes S :: "'a::wellorder set"
  assumes p: "p permutes S"
    and le: "\<forall>i \<in> S. p i \<ge> i"
  shows "p = id"
proof -
  have "i \<ge> inv p i" if "i \<in> S" for i
  proof -
    from that permutes_in_image[OF permutes_inv[OF p]] have "inv p i \<in> S"
      by simp
    with le have "p (inv p i) \<ge> inv p i"
      by blast
    with permutes_inverses[OF p] show ?thesis
      by simp
  qed
  then have "\<forall>i\<in>S. inv p i \<le> i"
    by blast
  from permutes_natset_le[OF permutes_inv[OF p] this] have "inv p = inv id"
    by simp
  then show ?thesis
    apply (subst permutes_inv_inv[OF p, symmetric])
    apply (rule inv_unique_comp)
     apply simp_all
    done
qed

lemma image_inverse_permutations: "{inv p |p. p permutes S} = {p. p permutes S}"
  apply (rule set_eqI)
  apply auto
  using permutes_inv_inv permutes_inv
   apply auto
  apply (rule_tac x="inv x" in exI)
  apply auto
  done

lemma image_compose_permutations_left:
  assumes "q permutes S"
  shows "{q \<circ> p |p. p permutes S} = {p. p permutes S}"
  apply (rule set_eqI)
  apply auto
   apply (rule permutes_compose)
  using assms
    apply auto
  apply (rule_tac x = "inv q \<circ> x" in exI)
  apply (simp add: o_assoc permutes_inv permutes_compose permutes_inv_o)
  done

lemma image_compose_permutations_right:
  assumes "q permutes S"
  shows "{p \<circ> q | p. p permutes S} = {p . p permutes S}"
  apply (rule set_eqI)
  apply auto
   apply (rule permutes_compose)
  using assms
    apply auto
  apply (rule_tac x = "x \<circ> inv q" in exI)
  apply (simp add: o_assoc permutes_inv permutes_compose permutes_inv_o comp_assoc)
  done

lemma permutes_in_seg: "p permutes {1 ..n} \<Longrightarrow> i \<in> {1..n} \<Longrightarrow> 1 \<le> p i \<and> p i \<le> n"
  by (simp add: permutes_def) metis

lemma sum_permutations_inverse: "sum f {p. p permutes S} = sum (\<lambda>p. f(inv p)) {p. p permutes S}"
  (is "?lhs = ?rhs")
proof -
  let ?S = "{p . p permutes S}"
  have *: "inj_on inv ?S"
  proof (auto simp add: inj_on_def)
    fix q r
    assume q: "q permutes S"
      and r: "r permutes S"
      and qr: "inv q = inv r"
    then have "inv (inv q) = inv (inv r)"
      by simp
    with permutes_inv_inv[OF q] permutes_inv_inv[OF r] show "q = r"
      by metis
  qed
  have **: "inv ` ?S = ?S"
    using image_inverse_permutations by blast
  have ***: "?rhs = sum (f \<circ> inv) ?S"
    by (simp add: o_def)
  from sum.reindex[OF *, of f] show ?thesis
    by (simp only: ** ***)
qed

lemma setum_permutations_compose_left:
  assumes q: "q permutes S"
  shows "sum f {p. p permutes S} = sum (\<lambda>p. f(q \<circ> p)) {p. p permutes S}"
  (is "?lhs = ?rhs")
proof -
  let ?S = "{p. p permutes S}"
  have *: "?rhs = sum (f \<circ> ((\<circ>) q)) ?S"
    by (simp add: o_def)
  have **: "inj_on ((\<circ>) q) ?S"
  proof (auto simp add: inj_on_def)
    fix p r
    assume "p permutes S"
      and r: "r permutes S"
      and rp: "q \<circ> p = q \<circ> r"
    then have "inv q \<circ> q \<circ> p = inv q \<circ> q \<circ> r"
      by (simp add: comp_assoc)
    with permutes_inj[OF q, unfolded inj_iff] show "p = r"
      by simp
  qed
  have "((\<circ>) q) ` ?S = ?S"
    using image_compose_permutations_left[OF q] by auto
  with * sum.reindex[OF **, of f] show ?thesis
    by (simp only:)
qed

lemma sum_permutations_compose_right:
  assumes q: "q permutes S"
  shows "sum f {p. p permutes S} = sum (\<lambda>p. f(p \<circ> q)) {p. p permutes S}"
  (is "?lhs = ?rhs")
proof -
  let ?S = "{p. p permutes S}"
  have *: "?rhs = sum (f \<circ> (\<lambda>p. p \<circ> q)) ?S"
    by (simp add: o_def)
  have **: "inj_on (\<lambda>p. p \<circ> q) ?S"
  proof (auto simp add: inj_on_def)
    fix p r
    assume "p permutes S"
      and r: "r permutes S"
      and rp: "p \<circ> q = r \<circ> q"
    then have "p \<circ> (q \<circ> inv q) = r \<circ> (q \<circ> inv q)"
      by (simp add: o_assoc)
    with permutes_surj[OF q, unfolded surj_iff] show "p = r"
      by simp
  qed
  from image_compose_permutations_right[OF q] have "(\<lambda>p. p \<circ> q) ` ?S = ?S"
    by auto
  with * sum.reindex[OF **, of f] show ?thesis
    by (simp only:)
qed

lemma inv_inj_on_permutes:
  \<open>inj_on inv {p. p permutes S}\<close>
proof (intro inj_onI, unfold mem_Collect_eq)
  fix p q
  assume p: "p permutes S" and q: "q permutes S" and eq: "inv p = inv q"
  have "inv (inv p) = inv (inv q)" using eq by simp
  thus "p = q"
    using inv_inv_eq[OF permutes_bij] p q by metis
qed

lemma permutes_pair_eq:
  \<open>{(p s, s) |s. s \<in> S} = {(s, inv p s) |s. s \<in> S}\<close> (is \<open>?L = ?R\<close>) if \<open>p permutes S\<close>
proof
  show "?L \<subseteq> ?R"
  proof
    fix x assume "x \<in> ?L"
    then obtain s where x: "x = (p s, s)" and s: "s \<in> S" by auto
    note x
    also have "(p s, s) = (p s, Hilbert_Choice.inv p (p s))"
      using permutes_inj [OF that] inv_f_f by auto
    also have "... \<in> ?R" using s permutes_in_image[OF that] by auto
    finally show "x \<in> ?R".
  qed
  show "?R \<subseteq> ?L"
  proof
    fix x assume "x \<in> ?R"
    then obtain s
      where x: "x = (s, Hilbert_Choice.inv p s)" (is "_ = (s, ?ips)")
        and s: "s \<in> S" by auto
    note x
    also have "(s, ?ips) = (p ?ips, ?ips)"
      using inv_f_f[OF permutes_inj[OF permutes_inv[OF that]]]
      using inv_inv_eq[OF permutes_bij[OF that]] by auto
    also have "... \<in> ?L"
      using s permutes_in_image[OF permutes_inv[OF that]] by auto
    finally show "x \<in> ?L".
  qed
qed

context
  fixes p and n i :: nat
  assumes p: \<open>p permutes {0..<n}\<close> and i: \<open>i < n\<close>
begin

lemma permutes_nat_less:
  \<open>p i < n\<close>
proof -
  have \<open>?thesis \<longleftrightarrow> p i \<in> {0..<n}\<close>
    by simp
  also from p have \<open>p i \<in> {0..<n} \<longleftrightarrow> i \<in> {0..<n}\<close>
    by (rule permutes_in_image)
  finally show ?thesis
    using i by simp
qed

lemma permutes_nat_inv_less:
  \<open>inv p i < n\<close>
proof -
  from p have \<open>inv p permutes {0..<n}\<close>
    by (rule permutes_inv)
  then show ?thesis
    using i by (rule Permutations.permutes_nat_less)
qed

end

context comm_monoid_set
begin

lemma permutes_inv:
  \<open>F (\<lambda>s. g (p s) s) S = F (\<lambda>s. g s (inv p s)) S\<close> (is \<open>?l = ?r\<close>)
  if \<open>p permutes S\<close>
proof -
  let ?g = "\<lambda>(x, y). g x y"
  let ?ps = "\<lambda>s. (p s, s)"
  let ?ips = "\<lambda>s. (s, inv p s)"
  have inj1: "inj_on ?ps S" by (rule inj_onI) auto
  have inj2: "inj_on ?ips S" by (rule inj_onI) auto
  have "?l = F ?g (?ps ` S)"
    using reindex [OF inj1, of ?g] by simp
  also have "?ps ` S = {(p s, s) |s. s \<in> S}" by auto
  also have "... = {(s, inv p s) |s. s \<in> S}"
    unfolding permutes_pair_eq [OF that] by simp
  also have "... = ?ips ` S" by auto
  also have "F ?g ... = ?r"
    using reindex [OF inj2, of ?g] by simp
  finally show ?thesis.
qed

end


subsection \<open>Sum over a set of permutations (could generalize to iteration)\<close>

lemma sum_over_permutations_insert:
  assumes fS: "finite S"
    and aS: "a \<notin> S"
  shows "sum f {p. p permutes (insert a S)} =
    sum (\<lambda>b. sum (\<lambda>q. f (transpose a b \<circ> q)) {p. p permutes S}) (insert a S)"
proof -
  have *: "\<And>f a b. (\<lambda>(b, p). f (transpose a b \<circ> p)) = f \<circ> (\<lambda>(b,p). transpose a b \<circ> p)"
    by (simp add: fun_eq_iff)
  have **: "\<And>P Q. {(a, b). a \<in> P \<and> b \<in> Q} = P \<times> Q"
    by blast
  show ?thesis
    unfolding * ** sum.cartesian_product permutes_insert
  proof (rule sum.reindex)
    let ?f = "(\<lambda>(b, y). transpose a b \<circ> y)"
    let ?P = "{p. p permutes S}"
    {
      fix b c p q
      assume b: "b \<in> insert a S"
      assume c: "c \<in> insert a S"
      assume p: "p permutes S"
      assume q: "q permutes S"
      assume eq: "transpose a b \<circ> p = transpose a c \<circ> q"
      from p q aS have pa: "p a = a" and qa: "q a = a"
        unfolding permutes_def by metis+
      from eq have "(transpose a b \<circ> p) a  = (transpose a c \<circ> q) a"
        by simp
      then have bc: "b = c"
        by (simp add: permutes_def pa qa o_def fun_upd_def id_def
            cong del: if_weak_cong split: if_split_asm)
      from eq[unfolded bc] have "(\<lambda>p. transpose a c \<circ> p) (transpose a c \<circ> p) =
        (\<lambda>p. transpose a c \<circ> p) (transpose a c \<circ> q)" by simp
      then have "p = q"
        unfolding o_assoc swap_id_idempotent by simp
      with bc have "b = c \<and> p = q"
        by blast
    }
    then show "inj_on ?f (insert a S \<times> ?P)"
      unfolding inj_on_def by clarify metis
  qed
qed


subsection \<open>Constructing permutations from association lists\<close>

definition list_permutes :: "('a \<times> 'a) list \<Rightarrow> 'a set \<Rightarrow> bool"
  where "list_permutes xs A \<longleftrightarrow>
    set (map fst xs) \<subseteq> A \<and>
    set (map snd xs) = set (map fst xs) \<and>
    distinct (map fst xs) \<and>
    distinct (map snd xs)"

lemma list_permutesI [simp]:
  assumes "set (map fst xs) \<subseteq> A" "set (map snd xs) = set (map fst xs)" "distinct (map fst xs)"
  shows "list_permutes xs A"
proof -
  from assms(2,3) have "distinct (map snd xs)"
    by (intro card_distinct) (simp_all add: distinct_card del: set_map)
  with assms show ?thesis
    by (simp add: list_permutes_def)
qed

definition permutation_of_list :: "('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a"
  where "permutation_of_list xs x = (case map_of xs x of None \<Rightarrow> x | Some y \<Rightarrow> y)"

lemma permutation_of_list_Cons:
  "permutation_of_list ((x, y) # xs) x' = (if x = x' then y else permutation_of_list xs x')"
  by (simp add: permutation_of_list_def)

fun inverse_permutation_of_list :: "('a \<times> 'a) list \<Rightarrow> 'a \<Rightarrow> 'a"
  where
    "inverse_permutation_of_list [] x = x"
  | "inverse_permutation_of_list ((y, x') # xs) x =
      (if x = x' then y else inverse_permutation_of_list xs x)"

declare inverse_permutation_of_list.simps [simp del]

lemma inj_on_map_of:
  assumes "distinct (map snd xs)"
  shows "inj_on (map_of xs) (set (map fst xs))"
proof (rule inj_onI)
  fix x y
  assume xy: "x \<in> set (map fst xs)" "y \<in> set (map fst xs)"
  assume eq: "map_of xs x = map_of xs y"
  from xy obtain x' y' where x'y': "map_of xs x = Some x'" "map_of xs y = Some y'"
    by (cases "map_of xs x"; cases "map_of xs y") (simp_all add: map_of_eq_None_iff)
  moreover from x'y' have *: "(x, x') \<in> set xs" "(y, y') \<in> set xs"
    by (force dest: map_of_SomeD)+
  moreover from * eq x'y' have "x' = y'"
    by simp
  ultimately show "x = y"
    using assms by (force simp: distinct_map dest: inj_onD[of _ _ "(x,x')" "(y,y')"])
qed

lemma inj_on_the: "None \<notin> A \<Longrightarrow> inj_on the A"
  by (auto simp: inj_on_def option.the_def split: option.splits)

lemma inj_on_map_of':
  assumes "distinct (map snd xs)"
  shows "inj_on (the \<circ> map_of xs) (set (map fst xs))"
  by (intro comp_inj_on inj_on_map_of assms inj_on_the)
    (force simp: eq_commute[of None] map_of_eq_None_iff)

lemma image_map_of:
  assumes "distinct (map fst xs)"
  shows "map_of xs ` set (map fst xs) = Some ` set (map snd xs)"
  using assms by (auto simp: rev_image_eqI)

lemma the_Some_image [simp]: "the ` Some ` A = A"
  by (subst image_image) simp

lemma image_map_of':
  assumes "distinct (map fst xs)"
  shows "(the \<circ> map_of xs) ` set (map fst xs) = set (map snd xs)"
  by (simp only: image_comp [symmetric] image_map_of assms the_Some_image)

lemma permutation_of_list_permutes [simp]:
  assumes "list_permutes xs A"
  shows "permutation_of_list xs permutes A"
    (is "?f permutes _")
proof (rule permutes_subset[OF bij_imp_permutes])
  from assms show "set (map fst xs) \<subseteq> A"
    by (simp add: list_permutes_def)
  from assms have "inj_on (the \<circ> map_of xs) (set (map fst xs))" (is ?P)
    by (intro inj_on_map_of') (simp_all add: list_permutes_def)
  also have "?P \<longleftrightarrow> inj_on ?f (set (map fst xs))"
    by (intro inj_on_cong)
      (auto simp: permutation_of_list_def map_of_eq_None_iff split: option.splits)
  finally have "bij_betw ?f (set (map fst xs)) (?f ` set (map fst xs))"
    by (rule inj_on_imp_bij_betw)
  also from assms have "?f ` set (map fst xs) = (the \<circ> map_of xs) ` set (map fst xs)"
    by (intro image_cong refl)
      (auto simp: permutation_of_list_def map_of_eq_None_iff split: option.splits)
  also from assms have "\<dots> = set (map fst xs)"
    by (subst image_map_of') (simp_all add: list_permutes_def)
  finally show "bij_betw ?f (set (map fst xs)) (set (map fst xs))" .
qed (force simp: permutation_of_list_def dest!: map_of_SomeD split: option.splits)+

lemma eval_permutation_of_list [simp]:
  "permutation_of_list [] x = x"
  "x = x' \<Longrightarrow> permutation_of_list ((x',y)#xs) x = y"
  "x \<noteq> x' \<Longrightarrow> permutation_of_list ((x',y')#xs) x = permutation_of_list xs x"
  by (simp_all add: permutation_of_list_def)

lemma eval_inverse_permutation_of_list [simp]:
  "inverse_permutation_of_list [] x = x"
  "x = x' \<Longrightarrow> inverse_permutation_of_list ((y,x')#xs) x = y"
  "x \<noteq> x' \<Longrightarrow> inverse_permutation_of_list ((y',x')#xs) x = inverse_permutation_of_list xs x"
  by (simp_all add: inverse_permutation_of_list.simps)

lemma permutation_of_list_id: "x \<notin> set (map fst xs) \<Longrightarrow> permutation_of_list xs x = x"
  by (induct xs) (auto simp: permutation_of_list_Cons)

lemma permutation_of_list_unique':
  "distinct (map fst xs) \<Longrightarrow> (x, y) \<in> set xs \<Longrightarrow> permutation_of_list xs x = y"
  by (induct xs) (force simp: permutation_of_list_Cons)+

lemma permutation_of_list_unique:
  "list_permutes xs A \<Longrightarrow> (x, y) \<in> set xs \<Longrightarrow> permutation_of_list xs x = y"
  by (intro permutation_of_list_unique') (simp_all add: list_permutes_def)

lemma inverse_permutation_of_list_id:
  "x \<notin> set (map snd xs) \<Longrightarrow> inverse_permutation_of_list xs x = x"
  by (induct xs) auto

lemma inverse_permutation_of_list_unique':
  "distinct (map snd xs) \<Longrightarrow> (x, y) \<in> set xs \<Longrightarrow> inverse_permutation_of_list xs y = x"
  by (induct xs) (force simp: inverse_permutation_of_list.simps(2))+

lemma inverse_permutation_of_list_unique:
  "list_permutes xs A \<Longrightarrow> (x,y) \<in> set xs \<Longrightarrow> inverse_permutation_of_list xs y = x"
  by (intro inverse_permutation_of_list_unique') (simp_all add: list_permutes_def)

lemma inverse_permutation_of_list_correct:
  fixes A :: "'a set"
  assumes "list_permutes xs A"
  shows "inverse_permutation_of_list xs = inv (permutation_of_list xs)"
proof (rule ext, rule sym, subst permutes_inv_eq)
  from assms show "permutation_of_list xs permutes A"
    by simp
  show "permutation_of_list xs (inverse_permutation_of_list xs x) = x" for x
  proof (cases "x \<in> set (map snd xs)")
    case True
    then obtain y where "(y, x) \<in> set xs" by auto
    with assms show ?thesis
      by (simp add: inverse_permutation_of_list_unique permutation_of_list_unique)
  next
    case False
    with assms show ?thesis
      by (auto simp: list_permutes_def inverse_permutation_of_list_id permutation_of_list_id)
  qed
qed

end
