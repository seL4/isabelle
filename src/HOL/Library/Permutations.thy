(*  Title:      HOL/Library/Permutations.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header {* Permutations, both general and specifically on finite sets.*}

theory Permutations
imports Parity Fact
begin

subsection {* Transpositions *}

lemma swap_id_idempotent [simp]:
  "Fun.swap a b id \<circ> Fun.swap a b id = id"
  by (rule ext, auto simp add: Fun.swap_def)

lemma inv_swap_id:
  "inv (Fun.swap a b id) = Fun.swap a b id"
  by (rule inv_unique_comp) simp_all

lemma swap_id_eq:
  "Fun.swap a b id x = (if x = a then b else if x = b then a else x)"
  by (simp add: Fun.swap_def)


subsection {* Basic consequences of the definition *}

definition permutes  (infixr "permutes" 41)
  where "(p permutes S) \<longleftrightarrow> (\<forall>x. x \<notin> S \<longrightarrow> p x = x) \<and> (\<forall>y. \<exists>!x. p x = y)"

lemma permutes_in_image: "p permutes S \<Longrightarrow> p x \<in> S \<longleftrightarrow> x \<in> S"
  unfolding permutes_def by metis

lemma permutes_image: "p permutes S \<Longrightarrow> p ` S = S"
  unfolding permutes_def
  apply (rule set_eqI)
  apply (simp add: image_iff)
  apply metis
  done

lemma permutes_inj: "p permutes S \<Longrightarrow> inj p"
  unfolding permutes_def inj_on_def by blast

lemma permutes_surj: "p permutes s \<Longrightarrow> surj p"
  unfolding permutes_def surj_def by metis

lemma permutes_inv_o:
  assumes pS: "p permutes S"
  shows "p \<circ> inv p = id"
    and "inv p \<circ> p = id"
  using permutes_inj[OF pS] permutes_surj[OF pS]
  unfolding inj_iff[symmetric] surj_iff[symmetric] by blast+

lemma permutes_inverses:
  fixes p :: "'a \<Rightarrow> 'a"
  assumes pS: "p permutes S"
  shows "p (inv p x) = x"
    and "inv p (p x) = x"
  using permutes_inv_o[OF pS, unfolded fun_eq_iff o_def] by auto

lemma permutes_subset: "p permutes S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> p permutes T"
  unfolding permutes_def by blast

lemma permutes_empty[simp]: "p permutes {} \<longleftrightarrow> p = id"
  unfolding fun_eq_iff permutes_def by simp metis

lemma permutes_sing[simp]: "p permutes {a} \<longleftrightarrow> p = id"
  unfolding fun_eq_iff permutes_def by simp metis

lemma permutes_univ: "p permutes UNIV \<longleftrightarrow> (\<forall>y. \<exists>!x. p x = y)"
  unfolding permutes_def by simp

lemma permutes_inv_eq: "p permutes S \<Longrightarrow> inv p y = x \<longleftrightarrow> p x = y"
  unfolding permutes_def inv_def
  apply auto
  apply (erule allE[where x=y])
  apply (erule allE[where x=y])
  apply (rule someI_ex)
  apply blast
  apply (rule some1_equality)
  apply blast
  apply blast
  done

lemma permutes_swap_id: "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> Fun.swap a b id permutes S"
  unfolding permutes_def Fun.swap_def fun_upd_def by auto metis

lemma permutes_superset: "p permutes S \<Longrightarrow> (\<forall>x \<in> S - T. p x = x) \<Longrightarrow> p permutes T"
  by (simp add: Ball_def permutes_def) metis


subsection {* Group properties *}

lemma permutes_id: "id permutes S"
  unfolding permutes_def by simp

lemma permutes_compose: "p permutes S \<Longrightarrow> q permutes S \<Longrightarrow> q \<circ> p permutes S"
  unfolding permutes_def o_def by metis

lemma permutes_inv:
  assumes pS: "p permutes S"
  shows "inv p permutes S"
  using pS unfolding permutes_def permutes_inv_eq[OF pS] by metis

lemma permutes_inv_inv:
  assumes pS: "p permutes S"
  shows "inv (inv p) = p"
  unfolding fun_eq_iff permutes_inv_eq[OF pS] permutes_inv_eq[OF permutes_inv[OF pS]]
  by blast


subsection {* The number of permutations on a finite set *}

lemma permutes_insert_lemma:
  assumes pS: "p permutes (insert a S)"
  shows "Fun.swap a (p a) id \<circ> p permutes S"
  apply (rule permutes_superset[where S = "insert a S"])
  apply (rule permutes_compose[OF pS])
  apply (rule permutes_swap_id, simp)
  using permutes_in_image[OF pS, of a]
  apply simp
  apply (auto simp add: Ball_def Fun.swap_def)
  done

lemma permutes_insert: "{p. p permutes (insert a S)} =
  (\<lambda>(b,p). Fun.swap a b id \<circ> p) ` {(b,p). b \<in> insert a S \<and> p \<in> {p. p permutes S}}"
proof -
  {
    fix p
    {
      assume pS: "p permutes insert a S"
      let ?b = "p a"
      let ?q = "Fun.swap a (p a) id \<circ> p"
      have th0: "p = Fun.swap a ?b id \<circ> ?q"
        unfolding fun_eq_iff o_assoc by simp
      have th1: "?b \<in> insert a S"
        unfolding permutes_in_image[OF pS] by simp
      from permutes_insert_lemma[OF pS] th0 th1
      have "\<exists>b q. p = Fun.swap a b id \<circ> q \<and> b \<in> insert a S \<and> q permutes S" by blast
    }
    moreover
    {
      fix b q
      assume bq: "p = Fun.swap a b id \<circ> q" "b \<in> insert a S" "q permutes S"
      from permutes_subset[OF bq(3), of "insert a S"]
      have qS: "q permutes insert a S"
        by auto
      have aS: "a \<in> insert a S"
        by simp
      from bq(1) permutes_compose[OF qS permutes_swap_id[OF aS bq(2)]]
      have "p permutes insert a S"
        by simp
    }
    ultimately have "p permutes insert a S \<longleftrightarrow>
        (\<exists>b q. p = Fun.swap a b id \<circ> q \<and> b \<in> insert a S \<and> q permutes S)"
      by blast
  }
  then show ?thesis
    by auto
qed

lemma card_permutations:
  assumes Sn: "card S = n"
    and fS: "finite S"
  shows "card {p. p permutes S} = fact n"
  using fS Sn
proof (induct arbitrary: n)
  case empty
  then show ?case by simp
next
  case (insert x F)
  {
    fix n
    assume H0: "card (insert x F) = n"
    let ?xF = "{p. p permutes insert x F}"
    let ?pF = "{p. p permutes F}"
    let ?pF' = "{(b, p). b \<in> insert x F \<and> p \<in> ?pF}"
    let ?g = "(\<lambda>(b, p). Fun.swap x b id \<circ> p)"
    from permutes_insert[of x F]
    have xfgpF': "?xF = ?g ` ?pF'" .
    have Fs: "card F = n - 1"
      using `x \<notin> F` H0 `finite F` by auto
    from insert.hyps Fs have pFs: "card ?pF = fact (n - 1)"
      using `finite F` by auto
    then have "finite ?pF"
      using fact_gt_zero_nat by (auto intro: card_ge_0_finite)
    then have pF'f: "finite ?pF'"
      using H0 `finite F`
      apply (simp only: Collect_split Collect_mem_eq)
      apply (rule finite_cartesian_product)
      apply simp_all
      done

    have ginj: "inj_on ?g ?pF'"
    proof -
      {
        fix b p c q
        assume bp: "(b,p) \<in> ?pF'"
        assume cq: "(c,q) \<in> ?pF'"
        assume eq: "?g (b,p) = ?g (c,q)"
        from bp cq have ths: "b \<in> insert x F" "c \<in> insert x F" "x \<in> insert x F"
          "p permutes F" "q permutes F"
          by auto
        from ths(4) `x \<notin> F` eq have "b = ?g (b,p) x"
          unfolding permutes_def
          by (auto simp add: Fun.swap_def fun_upd_def fun_eq_iff)
        also have "\<dots> = ?g (c,q) x"
          using ths(5) `x \<notin> F` eq
          by (auto simp add: swap_def fun_upd_def fun_eq_iff)
        also have "\<dots> = c"
          using ths(5) `x \<notin> F`
          unfolding permutes_def
          by (auto simp add: Fun.swap_def fun_upd_def fun_eq_iff)
        finally have bc: "b = c" .
        then have "Fun.swap x b id = Fun.swap x c id"
          by simp
        with eq have "Fun.swap x b id \<circ> p = Fun.swap x b id \<circ> q"
          by simp
        then have "Fun.swap x b id \<circ> (Fun.swap x b id \<circ> p) =
          Fun.swap x b id \<circ> (Fun.swap x b id \<circ> q)"
          by simp
        then have "p = q"
          by (simp add: o_assoc)
        with bc have "(b, p) = (c, q)"
          by simp
      }
      then show ?thesis
        unfolding inj_on_def by blast
    qed
    from `x \<notin> F` H0 have n0: "n \<noteq> 0"
      using `finite F` by auto
    then have "\<exists>m. n = Suc m"
      by presburger
    then obtain m where n[simp]: "n = Suc m"
      by blast
    from pFs H0 have xFc: "card ?xF = fact n"
      unfolding xfgpF' card_image[OF ginj]
      using `finite F` `finite ?pF`
      apply (simp only: Collect_split Collect_mem_eq card_cartesian_product)
      apply simp
      done
    from finite_imageI[OF pF'f, of ?g] have xFf: "finite ?xF"
      unfolding xfgpF' by simp
    have "card ?xF = fact n"
      using xFf xFc unfolding xFf by blast
  }
  then show ?case
    using insert by simp
qed

lemma finite_permutations:
  assumes fS: "finite S"
  shows "finite {p. p permutes S}"
  using card_permutations[OF refl fS] fact_gt_zero_nat
  by (auto intro: card_ge_0_finite)


subsection {* Permutations of index set for iterated operations *}

lemma (in comm_monoid_set) permute:
  assumes "p permutes S"
  shows "F g S = F (g \<circ> p) S"
proof -
  from `p permutes S` have "inj p"
    by (rule permutes_inj)
  then have "inj_on p S"
    by (auto intro: subset_inj_on)
  then have "F g (p ` S) = F (g \<circ> p) S"
    by (rule reindex)
  moreover from `p permutes S` have "p ` S = S"
    by (rule permutes_image)
  ultimately show ?thesis
    by simp
qed

lemma setsum_permute:
  assumes "p permutes S"
  shows "setsum f S = setsum (f \<circ> p) S"
  using assms by (fact setsum.permute)

lemma setsum_permute_natseg:
  assumes pS: "p permutes {m .. n}"
  shows "setsum f {m .. n} = setsum (f \<circ> p) {m .. n}"
  using setsum_permute [OF pS, of f ] pS by blast

lemma setprod_permute:
  assumes "p permutes S"
  shows "setprod f S = setprod (f \<circ> p) S"
  using assms by (fact setprod.permute)

lemma setprod_permute_natseg:
  assumes pS: "p permutes {m .. n}"
  shows "setprod f {m .. n} = setprod (f \<circ> p) {m .. n}"
  using setprod_permute [OF pS, of f ] pS by blast


subsection {* Various combinations of transpositions with 2, 1 and 0 common elements *}

lemma swap_id_common:" a \<noteq> c \<Longrightarrow> b \<noteq> c \<Longrightarrow>
  Fun.swap a b id \<circ> Fun.swap a c id = Fun.swap b c id \<circ> Fun.swap a b id"
  by (simp add: fun_eq_iff Fun.swap_def)

lemma swap_id_common': "a \<noteq> b \<Longrightarrow> a \<noteq> c \<Longrightarrow>
  Fun.swap a c id \<circ> Fun.swap b c id = Fun.swap b c id \<circ> Fun.swap a b id"
  by (simp add: fun_eq_iff Fun.swap_def)

lemma swap_id_independent: "a \<noteq> c \<Longrightarrow> a \<noteq> d \<Longrightarrow> b \<noteq> c \<Longrightarrow> b \<noteq> d \<Longrightarrow>
  Fun.swap a b id \<circ> Fun.swap c d id = Fun.swap c d id \<circ> Fun.swap a b id"
  by (simp add: fun_eq_iff Fun.swap_def)


subsection {* Permutations as transposition sequences *}

inductive swapidseq :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  id[simp]: "swapidseq 0 id"
| comp_Suc: "swapidseq n p \<Longrightarrow> a \<noteq> b \<Longrightarrow> swapidseq (Suc n) (Fun.swap a b id \<circ> p)"

declare id[unfolded id_def, simp]

definition "permutation p \<longleftrightarrow> (\<exists>n. swapidseq n p)"


subsection {* Some closure properties of the set of permutations, with lengths *}

lemma permutation_id[simp]: "permutation id"
  unfolding permutation_def by (rule exI[where x=0]) simp

declare permutation_id[unfolded id_def, simp]

lemma swapidseq_swap: "swapidseq (if a = b then 0 else 1) (Fun.swap a b id)"
  apply clarsimp
  using comp_Suc[of 0 id a b]
  apply simp
  done

lemma permutation_swap_id: "permutation (Fun.swap a b id)"
  apply (cases "a = b")
  apply simp_all
  unfolding permutation_def
  using swapidseq_swap[of a b]
  apply blast
  done

lemma swapidseq_comp_add: "swapidseq n p \<Longrightarrow> swapidseq m q \<Longrightarrow> swapidseq (n + m) (p \<circ> q)"
proof (induct n p arbitrary: m q rule: swapidseq.induct)
  case (id m q)
  then show ?case by simp
next
  case (comp_Suc n p a b m q)
  have th: "Suc n + m = Suc (n + m)"
    by arith
  show ?case
    unfolding th comp_assoc
    apply (rule swapidseq.comp_Suc)
    using comp_Suc.hyps(2)[OF comp_Suc.prems] comp_Suc.hyps(3)
    apply blast+
    done
qed

lemma permutation_compose: "permutation p \<Longrightarrow> permutation q \<Longrightarrow> permutation (p \<circ> q)"
  unfolding permutation_def using swapidseq_comp_add[of _ p _ q] by metis

lemma swapidseq_endswap: "swapidseq n p \<Longrightarrow> a \<noteq> b \<Longrightarrow> swapidseq (Suc n) (p \<circ> Fun.swap a b id)"
  apply (induct n p rule: swapidseq.induct)
  using swapidseq_swap[of a b]
  apply (auto simp add: comp_assoc intro: swapidseq.comp_Suc)
  done

lemma swapidseq_inverse_exists: "swapidseq n p \<Longrightarrow> \<exists>q. swapidseq n q \<and> p \<circ> q = id \<and> q \<circ> p = id"
proof (induct n p rule: swapidseq.induct)
  case id
  then show ?case
    by (rule exI[where x=id]) simp
next
  case (comp_Suc n p a b)
  from comp_Suc.hyps obtain q where q: "swapidseq n q" "p \<circ> q = id" "q \<circ> p = id"
    by blast
  let ?q = "q \<circ> Fun.swap a b id"
  note H = comp_Suc.hyps
  from swapidseq_swap[of a b] H(3) have th0: "swapidseq 1 (Fun.swap a b id)"
    by simp
  from swapidseq_comp_add[OF q(1) th0] have th1: "swapidseq (Suc n) ?q"
    by simp
  have "Fun.swap a b id \<circ> p \<circ> ?q = Fun.swap a b id \<circ> (p \<circ> q) \<circ> Fun.swap a b id"
    by (simp add: o_assoc)
  also have "\<dots> = id"
    by (simp add: q(2))
  finally have th2: "Fun.swap a b id \<circ> p \<circ> ?q = id" .
  have "?q \<circ> (Fun.swap a b id \<circ> p) = q \<circ> (Fun.swap a b id \<circ> Fun.swap a b id) \<circ> p"
    by (simp only: o_assoc)
  then have "?q \<circ> (Fun.swap a b id \<circ> p) = id"
    by (simp add: q(3))
  with th1 th2 show ?case
    by blast
qed

lemma swapidseq_inverse:
  assumes H: "swapidseq n p"
  shows "swapidseq n (inv p)"
  using swapidseq_inverse_exists[OF H] inv_unique_comp[of p] by auto

lemma permutation_inverse: "permutation p \<Longrightarrow> permutation (inv p)"
  using permutation_def swapidseq_inverse by blast


subsection {* The identity map only has even transposition sequences *}

lemma symmetry_lemma:
  assumes "\<And>a b c d. P a b c d \<Longrightarrow> P a b d c"
    and "\<And>a b c d. a \<noteq> b \<Longrightarrow> c \<noteq> d \<Longrightarrow>
      a = c \<and> b = d \<or> a = c \<and> b \<noteq> d \<or> a \<noteq> c \<and> b = d \<or> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d \<Longrightarrow>
      P a b c d"
  shows "\<And>a b c d. a \<noteq> b \<longrightarrow> c \<noteq> d \<longrightarrow>  P a b c d"
  using assms by metis

lemma swap_general: "a \<noteq> b \<Longrightarrow> c \<noteq> d \<Longrightarrow>
  Fun.swap a b id \<circ> Fun.swap c d id = id \<or>
  (\<exists>x y z. x \<noteq> a \<and> y \<noteq> a \<and> z \<noteq> a \<and> x \<noteq> y \<and>
    Fun.swap a b id \<circ> Fun.swap c d id = Fun.swap x y id \<circ> Fun.swap a z id)"
proof -
  assume H: "a \<noteq> b" "c \<noteq> d"
  have "a \<noteq> b \<longrightarrow> c \<noteq> d \<longrightarrow>
    (Fun.swap a b id \<circ> Fun.swap c d id = id \<or>
      (\<exists>x y z. x \<noteq> a \<and> y \<noteq> a \<and> z \<noteq> a \<and> x \<noteq> y \<and>
        Fun.swap a b id \<circ> Fun.swap c d id = Fun.swap x y id \<circ> Fun.swap a z id))"
    apply (rule symmetry_lemma[where a=a and b=b and c=c and d=d])
    apply (simp_all only: swap_commute)
    apply (case_tac "a = c \<and> b = d")
    apply (clarsimp simp only: swap_commute swap_id_idempotent)
    apply (case_tac "a = c \<and> b \<noteq> d")
    apply (rule disjI2)
    apply (rule_tac x="b" in exI)
    apply (rule_tac x="d" in exI)
    apply (rule_tac x="b" in exI)
    apply (clarsimp simp add: fun_eq_iff Fun.swap_def)
    apply (case_tac "a \<noteq> c \<and> b = d")
    apply (rule disjI2)
    apply (rule_tac x="c" in exI)
    apply (rule_tac x="d" in exI)
    apply (rule_tac x="c" in exI)
    apply (clarsimp simp add: fun_eq_iff Fun.swap_def)
    apply (rule disjI2)
    apply (rule_tac x="c" in exI)
    apply (rule_tac x="d" in exI)
    apply (rule_tac x="b" in exI)
    apply (clarsimp simp add: fun_eq_iff Fun.swap_def)
    done
  with H show ?thesis by metis
qed

lemma swapidseq_id_iff[simp]: "swapidseq 0 p \<longleftrightarrow> p = id"
  using swapidseq.cases[of 0 p "p = id"]
  by auto

lemma swapidseq_cases: "swapidseq n p \<longleftrightarrow>
  n = 0 \<and> p = id \<or> (\<exists>a b q m. n = Suc m \<and> p = Fun.swap a b id \<circ> q \<and> swapidseq m q \<and> a \<noteq> b)"
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
  assumes spn: "swapidseq n p"
    and ab: "a \<noteq> b"
    and pa: "(Fun.swap a b id \<circ> p) a = a"
  shows "n \<noteq> 0 \<and> swapidseq (n - 1) (Fun.swap a b id \<circ> p)"
  using spn ab pa
proof (induct n arbitrary: p a b)
  case 0
  then show ?case
    by (auto simp add: Fun.swap_def fun_upd_def)
next
  case (Suc n p a b)
  from Suc.prems(1) swapidseq_cases[of "Suc n" p]
  obtain c d q m where
    cdqm: "Suc n = Suc m" "p = Fun.swap c d id \<circ> q" "swapidseq m q" "c \<noteq> d" "n = m"
    by auto
  {
    assume H: "Fun.swap a b id \<circ> Fun.swap c d id = id"
    have ?case by (simp only: cdqm o_assoc H) (simp add: cdqm)
  }
  moreover
  {
    fix x y z
    assume H: "x \<noteq> a" "y \<noteq> a" "z \<noteq> a" "x \<noteq> y"
      "Fun.swap a b id \<circ> Fun.swap c d id = Fun.swap x y id \<circ> Fun.swap a z id"
    from H have az: "a \<noteq> z"
      by simp

    {
      fix h
      have "(Fun.swap x y id \<circ> h) a = a \<longleftrightarrow> h a = a"
        using H by (simp add: Fun.swap_def)
    }
    note th3 = this
    from cdqm(2) have "Fun.swap a b id \<circ> p = Fun.swap a b id \<circ> (Fun.swap c d id \<circ> q)"
      by simp
    then have "Fun.swap a b id \<circ> p = Fun.swap x y id \<circ> (Fun.swap a z id \<circ> q)"
      by (simp add: o_assoc H)
    then have "(Fun.swap a b id \<circ> p) a = (Fun.swap x y id \<circ> (Fun.swap a z id \<circ> q)) a"
      by simp
    then have "(Fun.swap x y id \<circ> (Fun.swap a z id \<circ> q)) a = a"
      unfolding Suc by metis
    then have th1: "(Fun.swap a z id \<circ> q) a = a"
      unfolding th3 .
    from Suc.hyps[OF cdqm(3)[ unfolded cdqm(5)[symmetric]] az th1]
    have th2: "swapidseq (n - 1) (Fun.swap a z id \<circ> q)" "n \<noteq> 0"
      by blast+
    have th: "Suc n - 1 = Suc (n - 1)"
      using th2(2) by auto
    have ?case
      unfolding cdqm(2) H o_assoc th
      apply (simp only: Suc_not_Zero simp_thms comp_assoc)
      apply (rule comp_Suc)
      using th2 H
      apply blast+
      done
  }
  ultimately show ?case
    using swap_general[OF Suc.prems(2) cdqm(4)] by metis
qed

lemma swapidseq_identity_even:
  assumes "swapidseq n (id :: 'a \<Rightarrow> 'a)"
  shows "even n"
  using `swapidseq n id`
proof (induct n rule: nat_less_induct)
  fix n
  assume H: "\<forall>m<n. swapidseq m (id::'a \<Rightarrow> 'a) \<longrightarrow> even m" "swapidseq n (id :: 'a \<Rightarrow> 'a)"
  {
    assume "n = 0"
    then have "even n" by presburger
  }
  moreover
  {
    fix a b :: 'a and q m
    assume h: "n = Suc m" "(id :: 'a \<Rightarrow> 'a) = Fun.swap a b id \<circ> q" "swapidseq m q" "a \<noteq> b"
    from fixing_swapidseq_decrease[OF h(3,4), unfolded h(2)[symmetric]]
    have m: "m \<noteq> 0" "swapidseq (m - 1) (id :: 'a \<Rightarrow> 'a)"
      by auto
    from h m have mn: "m - 1 < n"
      by arith
    from H(1)[rule_format, OF mn m(2)] h(1) m(1) have "even n"
      by presburger
  }
  ultimately show "even n"
    using H(2)[unfolded swapidseq_cases[of n id]] by auto
qed


subsection {* Therefore we have a welldefined notion of parity *}

definition "evenperm p = even (SOME n. swapidseq n p)"

lemma swapidseq_even_even:
  assumes m: "swapidseq m p"
    and n: "swapidseq n p"
  shows "even m \<longleftrightarrow> even n"
proof -
  from swapidseq_inverse_exists[OF n]
  obtain q where q: "swapidseq n q" "p \<circ> q = id" "q \<circ> p = id"
    by blast
  from swapidseq_identity_even[OF swapidseq_comp_add[OF m q(1), unfolded q]]
  show ?thesis
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


subsection {* And it has the expected composition properties *}

lemma evenperm_id[simp]: "evenperm id = True"
  by (rule evenperm_unique[where n = 0]) simp_all

lemma evenperm_swap: "evenperm (Fun.swap a b id) = (a = b)"
  by (rule evenperm_unique[where n="if a = b then 0 else 1"]) (simp_all add: swapidseq_swap)

lemma evenperm_comp:
  assumes p: "permutation p"
    and q:"permutation q"
  shows "evenperm (p \<circ> q) = (evenperm p = evenperm q)"
proof -
  from p q obtain n m where n: "swapidseq n p" and m: "swapidseq m q"
    unfolding permutation_def by blast
  note nm =  swapidseq_comp_add[OF n m]
  have th: "even (n + m) = (even n \<longleftrightarrow> even m)"
    by arith
  from evenperm_unique[OF n refl] evenperm_unique[OF m refl]
    evenperm_unique[OF nm th]
  show ?thesis
    by blast
qed

lemma evenperm_inv:
  assumes p: "permutation p"
  shows "evenperm (inv p) = evenperm p"
proof -
  from p obtain n where n: "swapidseq n p"
    unfolding permutation_def by blast
  from evenperm_unique[OF swapidseq_inverse[OF n] evenperm_unique[OF n refl, symmetric]]
  show ?thesis .
qed


subsection {* A more abstract characterization of permutations *}

lemma bij_iff: "bij f \<longleftrightarrow> (\<forall>x. \<exists>!y. f y = x)"
  unfolding bij_def inj_on_def surj_def
  apply auto
  apply metis
  apply metis
  done

lemma permutation_bijective:
  assumes p: "permutation p"
  shows "bij p"
proof -
  from p obtain n where n: "swapidseq n p"
    unfolding permutation_def by blast
  from swapidseq_inverse_exists[OF n]
  obtain q where q: "swapidseq n q" "p \<circ> q = id" "q \<circ> p = id"
    by blast
  then show ?thesis unfolding bij_iff
    apply (auto simp add: fun_eq_iff)
    apply metis
    done
qed

lemma permutation_finite_support:
  assumes p: "permutation p"
  shows "finite {x. p x \<noteq> x}"
proof -
  from p obtain n where n: "swapidseq n p"
    unfolding permutation_def by blast
  from n show ?thesis
  proof (induct n p rule: swapidseq.induct)
    case id
    then show ?case by simp
  next
    case (comp_Suc n p a b)
    let ?S = "insert a (insert b {x. p x \<noteq> x})"
    from comp_Suc.hyps(2) have fS: "finite ?S"
      by simp
    from `a \<noteq> b` have th: "{x. (Fun.swap a b id \<circ> p) x \<noteq> x} \<subseteq> ?S"
      by (auto simp add: Fun.swap_def)
    from finite_subset[OF th fS] show ?case  .
  qed
qed

lemma bij_inv_eq_iff: "bij p \<Longrightarrow> x = inv p y \<longleftrightarrow> p x = y"
  using surj_f_inv_f[of p] by (auto simp add: bij_def)

lemma bij_swap_comp:
  assumes bp: "bij p"
  shows "Fun.swap a b id \<circ> p = Fun.swap (inv p a) (inv p b) p"
  using surj_f_inv_f[OF bij_is_surj[OF bp]]
  by (simp add: fun_eq_iff Fun.swap_def bij_inv_eq_iff[OF bp])

lemma bij_swap_ompose_bij: "bij p \<Longrightarrow> bij (Fun.swap a b id \<circ> p)"
proof -
  assume H: "bij p"
  show ?thesis
    unfolding bij_swap_comp[OF H] bij_swap_iff
    using H .
qed

lemma permutation_lemma:
  assumes fS: "finite S"
    and p: "bij p"
    and pS: "\<forall>x. x\<notin> S \<longrightarrow> p x = x"
  shows "permutation p"
  using fS p pS
proof (induct S arbitrary: p rule: finite_induct)
  case (empty p)
  then show ?case by simp
next
  case (insert a F p)
  let ?r = "Fun.swap a (p a) id \<circ> p"
  let ?q = "Fun.swap a (p a) id \<circ> ?r"
  have raa: "?r a = a"
    by (simp add: Fun.swap_def)
  from bij_swap_ompose_bij[OF insert(4)]
  have br: "bij ?r"  .

  from insert raa have th: "\<forall>x. x \<notin> F \<longrightarrow> ?r x = x"
    apply (clarsimp simp add: Fun.swap_def)
    apply (erule_tac x="x" in allE)
    apply auto
    unfolding bij_iff
    apply metis
    done
  from insert(3)[OF br th]
  have rp: "permutation ?r" .
  have "permutation ?q"
    by (simp add: permutation_compose permutation_swap_id rp)
  then show ?case
    by (simp add: o_assoc)
qed

lemma permutation: "permutation p \<longleftrightarrow> bij p \<and> finite {x. p x \<noteq> x}"
  (is "?lhs \<longleftrightarrow> ?b \<and> ?f")
proof
  assume p: ?lhs
  from p permutation_bijective permutation_finite_support show "?b \<and> ?f"
    by auto
next
  assume "?b \<and> ?f"
  then have "?f" "?b" by blast+
  from permutation_lemma[OF this] show ?lhs
    by blast
qed

lemma permutation_inverse_works:
  assumes p: "permutation p"
  shows "inv p \<circ> p = id"
    and "p \<circ> inv p = id"
  using permutation_bijective [OF p]
  unfolding bij_def inj_iff surj_iff by auto

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
  finally have th0: "p \<circ> q \<circ> (inv q \<circ> inv p) = id" .
  have "inv q \<circ> inv p \<circ> (p \<circ> q) = inv q \<circ> (inv p \<circ> p) \<circ> q"
    by (simp add: o_assoc)
  also have "\<dots> = id"
    by (simp add: ps qs)
  finally have th1: "inv q \<circ> inv p \<circ> (p \<circ> q) = id" .
  from inv_unique_comp[OF th0 th1] show ?thesis .
qed


subsection {* Relation to "permutes" *}

lemma permutation_permutes: "permutation p \<longleftrightarrow> (\<exists>S. finite S \<and> p permutes S)"
  unfolding permutation permutes_def bij_iff[symmetric]
  apply (rule iffI, clarify)
  apply (rule exI[where x="{x. p x \<noteq> x}"])
  apply simp
  apply clarsimp
  apply (rule_tac B="S" in finite_subset)
  apply auto
  done


subsection {* Hence a sort of induction principle composing by swaps *}

lemma permutes_induct: "finite S \<Longrightarrow> P id \<Longrightarrow>
  (\<And> a b p. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> P p \<Longrightarrow> P p \<Longrightarrow> permutation p \<Longrightarrow> P (Fun.swap a b id \<circ> p)) \<Longrightarrow>
  (\<And>p. p permutes S \<Longrightarrow> P p)"
proof (induct S rule: finite_induct)
  case empty
  then show ?case by auto
next
  case (insert x F p)
  let ?r = "Fun.swap x (p x) id \<circ> p"
  let ?q = "Fun.swap x (p x) id \<circ> ?r"
  have qp: "?q = p"
    by (simp add: o_assoc)
  from permutes_insert_lemma[OF insert.prems(3)] insert have Pr: "P ?r"
    by blast
  from permutes_in_image[OF insert.prems(3), of x]
  have pxF: "p x \<in> insert x F"
    by simp
  have xF: "x \<in> insert x F"
    by simp
  have rp: "permutation ?r"
    unfolding permutation_permutes using insert.hyps(1)
      permutes_insert_lemma[OF insert.prems(3)]
    by blast
  from insert.prems(2)[OF xF pxF Pr Pr rp]
  show ?case
    unfolding qp .
qed


subsection {* Sign of a permutation as a real number *}

definition "sign p = (if evenperm p then (1::int) else -1)"

lemma sign_nz: "sign p \<noteq> 0"
  by (simp add: sign_def)

lemma sign_id: "sign id = 1"
  by (simp add: sign_def)

lemma sign_inverse: "permutation p \<Longrightarrow> sign (inv p) = sign p"
  by (simp add: sign_def evenperm_inv)

lemma sign_compose: "permutation p \<Longrightarrow> permutation q \<Longrightarrow> sign (p \<circ> q) = sign p * sign q"
  by (simp add: sign_def evenperm_comp)

lemma sign_swap_id: "sign (Fun.swap a b id) = (if a = b then 1 else -1)"
  by (simp add: sign_def evenperm_swap)

lemma sign_idempotent: "sign p * sign p = 1"
  by (simp add: sign_def)


subsection {* More lemmas about permutations *}

lemma permutes_natset_le:
  fixes S :: "'a::wellorder set"
  assumes p: "p permutes S"
    and le: "\<forall>i \<in> S. p i \<le> i"
  shows "p = id"
proof -
  {
    fix n
    have "p n = n"
      using p le
    proof (induct n arbitrary: S rule: less_induct)
      fix n S
      assume H:
        "\<And>m S. m < n \<Longrightarrow> p permutes S \<Longrightarrow> \<forall>i\<in>S. p i \<le> i \<Longrightarrow> p m = m"
        "p permutes S" "\<forall>i \<in>S. p i \<le> i"
      {
        assume "n \<notin> S"
        with H(2) have "p n = n"
          unfolding permutes_def by metis
      }
      moreover
      {
        assume ns: "n \<in> S"
        from H(3)  ns have "p n < n \<or> p n = n"
          by auto
        moreover {
          assume h: "p n < n"
          from H h have "p (p n) = p n"
            by metis
          with permutes_inj[OF H(2)] have "p n = n"
            unfolding inj_on_def by blast
          with h have False
            by simp
        }
        ultimately have "p n = n"
          by blast
      }
      ultimately show "p n = n"
        by blast
    qed
  }
  then show ?thesis
    by (auto simp add: fun_eq_iff)
qed

lemma permutes_natset_ge:
  fixes S :: "'a::wellorder set"
  assumes p: "p permutes S"
    and le: "\<forall>i \<in> S. p i \<ge> i"
  shows "p = id"
proof -
  {
    fix i
    assume i: "i \<in> S"
    from i permutes_in_image[OF permutes_inv[OF p]] have "inv p i \<in> S"
      by simp
    with le have "p (inv p i) \<ge> inv p i"
      by blast
    with permutes_inverses[OF p] have "i \<ge> inv p i"
      by simp
  }
  then have th: "\<forall>i\<in>S. inv p i \<le> i"
    by blast
  from permutes_natset_le[OF permutes_inv[OF p] th]
  have "inv p = inv id"
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
  assumes q: "q permutes S"
  shows "{q \<circ> p | p. p permutes S} = {p . p permutes S}"
  apply (rule set_eqI)
  apply auto
  apply (rule permutes_compose)
  using q
  apply auto
  apply (rule_tac x = "inv q \<circ> x" in exI)
  apply (simp add: o_assoc permutes_inv permutes_compose permutes_inv_o)
  done

lemma image_compose_permutations_right:
  assumes q: "q permutes S"
  shows "{p \<circ> q | p. p permutes S} = {p . p permutes S}"
  apply (rule set_eqI)
  apply auto
  apply (rule permutes_compose)
  using q
  apply auto
  apply (rule_tac x = "x \<circ> inv q" in exI)
  apply (simp add: o_assoc permutes_inv permutes_compose permutes_inv_o comp_assoc)
  done

lemma permutes_in_seg: "p permutes {1 ..n} \<Longrightarrow> i \<in> {1..n} \<Longrightarrow> 1 \<le> p i \<and> p i \<le> n"
  by (simp add: permutes_def) metis

lemma setsum_permutations_inverse:
  "setsum f {p. p permutes S} = setsum (\<lambda>p. f(inv p)) {p. p permutes S}"
  (is "?lhs = ?rhs")
proof -
  let ?S = "{p . p permutes S}"
  have th0: "inj_on inv ?S"
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
  have th1: "inv ` ?S = ?S"
    using image_inverse_permutations by blast
  have th2: "?rhs = setsum (f \<circ> inv) ?S"
    by (simp add: o_def)
  from setsum_reindex[OF th0, of f] show ?thesis unfolding th1 th2 .
qed

lemma setum_permutations_compose_left:
  assumes q: "q permutes S"
  shows "setsum f {p. p permutes S} = setsum (\<lambda>p. f(q \<circ> p)) {p. p permutes S}"
  (is "?lhs = ?rhs")
proof -
  let ?S = "{p. p permutes S}"
  have th0: "?rhs = setsum (f \<circ> (op \<circ> q)) ?S"
    by (simp add: o_def)
  have th1: "inj_on (op \<circ> q) ?S"
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
  have th3: "(op \<circ> q) ` ?S = ?S"
    using image_compose_permutations_left[OF q] by auto
  from setsum_reindex[OF th1, of f] show ?thesis unfolding th0 th1 th3 .
qed

lemma sum_permutations_compose_right:
  assumes q: "q permutes S"
  shows "setsum f {p. p permutes S} = setsum (\<lambda>p. f(p \<circ> q)) {p. p permutes S}"
  (is "?lhs = ?rhs")
proof -
  let ?S = "{p. p permutes S}"
  have th0: "?rhs = setsum (f \<circ> (\<lambda>p. p \<circ> q)) ?S"
    by (simp add: o_def)
  have th1: "inj_on (\<lambda>p. p \<circ> q) ?S"
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
  have th3: "(\<lambda>p. p \<circ> q) ` ?S = ?S"
    using image_compose_permutations_right[OF q] by auto
  from setsum_reindex[OF th1, of f]
  show ?thesis unfolding th0 th1 th3 .
qed


subsection {* Sum over a set of permutations (could generalize to iteration) *}

lemma setsum_over_permutations_insert:
  assumes fS: "finite S"
    and aS: "a \<notin> S"
  shows "setsum f {p. p permutes (insert a S)} =
    setsum (\<lambda>b. setsum (\<lambda>q. f (Fun.swap a b id \<circ> q)) {p. p permutes S}) (insert a S)"
proof -
  have th0: "\<And>f a b. (\<lambda>(b,p). f (Fun.swap a b id \<circ> p)) = f \<circ> (\<lambda>(b,p). Fun.swap a b id \<circ> p)"
    by (simp add: fun_eq_iff)
  have th1: "\<And>P Q. P \<times> Q = {(a,b). a \<in> P \<and> b \<in> Q}"
    by blast
  have th2: "\<And>P Q. P \<Longrightarrow> (P \<Longrightarrow> Q) \<Longrightarrow> P \<and> Q"
    by blast
  show ?thesis
    unfolding permutes_insert
    unfolding setsum_cartesian_product
    unfolding th1[symmetric]
    unfolding th0
  proof (rule setsum_reindex)
    let ?f = "(\<lambda>(b, y). Fun.swap a b id \<circ> y)"
    let ?P = "{p. p permutes S}"
    {
      fix b c p q
      assume b: "b \<in> insert a S"
      assume c: "c \<in> insert a S"
      assume p: "p permutes S"
      assume q: "q permutes S"
      assume eq: "Fun.swap a b id \<circ> p = Fun.swap a c id \<circ> q"
      from p q aS have pa: "p a = a" and qa: "q a = a"
        unfolding permutes_def by metis+
      from eq have "(Fun.swap a b id \<circ> p) a  = (Fun.swap a c id \<circ> q) a"
        by simp
      then have bc: "b = c"
        by (simp add: permutes_def pa qa o_def fun_upd_def Fun.swap_def id_def
            cong del: if_weak_cong split: split_if_asm)
      from eq[unfolded bc] have "(\<lambda>p. Fun.swap a c id \<circ> p) (Fun.swap a c id \<circ> p) =
        (\<lambda>p. Fun.swap a c id \<circ> p) (Fun.swap a c id \<circ> q)" by simp
      then have "p = q"
        unfolding o_assoc swap_id_idempotent
        by (simp add: o_def)
      with bc have "b = c \<and> p = q"
        by blast
    }
    then show "inj_on ?f (insert a S \<times> ?P)"
      unfolding inj_on_def by clarify metis
  qed
qed

end

