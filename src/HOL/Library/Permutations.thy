(*  Title:      HOL/Library/Permutations.thy
    Author:     Amine Chaieb, University of Cambridge
*)

section \<open>Permutations, both general and specifically on finite sets.\<close>

theory Permutations
imports Binomial Multiset Disjoint_Sets
begin

subsection \<open>Transpositions\<close>

lemma swap_id_idempotent [simp]:
  "Fun.swap a b id \<circ> Fun.swap a b id = id"
  by (rule ext, auto simp add: Fun.swap_def)

lemma inv_swap_id:
  "inv (Fun.swap a b id) = Fun.swap a b id"
  by (rule inv_unique_comp) simp_all

lemma swap_id_eq:
  "Fun.swap a b id x = (if x = a then b else if x = b then a else x)"
  by (simp add: Fun.swap_def)


subsection \<open>Basic consequences of the definition\<close>

definition permutes  (infixr "permutes" 41)
  where "(p permutes S) \<longleftrightarrow> (\<forall>x. x \<notin> S \<longrightarrow> p x = x) \<and> (\<forall>y. \<exists>!x. p x = y)"

lemma permutes_in_image: "p permutes S \<Longrightarrow> p x \<in> S \<longleftrightarrow> x \<in> S"
  unfolding permutes_def by metis
  
lemma permutes_not_in:
  assumes "f permutes S" "x \<notin> S" shows "f x = x"
  using assms by (auto simp: permutes_def)

lemma permutes_image: "p permutes S \<Longrightarrow> p ` S = S"
  unfolding permutes_def
  apply (rule set_eqI)
  apply (simp add: image_iff)
  apply metis
  done

lemma permutes_inj: "p permutes S \<Longrightarrow> inj p"
  unfolding permutes_def inj_on_def by blast

lemma permutes_inj_on: "f permutes S \<Longrightarrow> inj_on f A"
  unfolding permutes_def inj_on_def by auto

lemma permutes_surj: "p permutes s \<Longrightarrow> surj p"
  unfolding permutes_def surj_def by metis

lemma permutes_bij: "p permutes s \<Longrightarrow> bij p"
unfolding bij_def by (metis permutes_inj permutes_surj)

lemma permutes_imp_bij: "p permutes S \<Longrightarrow> bij_betw p S S"
by (metis UNIV_I bij_betw_subset permutes_bij permutes_image subsetI)

lemma bij_imp_permutes: "bij_betw p S S \<Longrightarrow> (\<And>x. x \<notin> S \<Longrightarrow> p x = x) \<Longrightarrow> p permutes S"
  unfolding permutes_def bij_betw_def inj_on_def
  by auto (metis image_iff)+

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


subsection \<open>Group properties\<close>

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

lemma permutes_invI: 
  assumes perm: "p permutes S"
      and inv:  "\<And>x. x \<in> S \<Longrightarrow> p' (p x) = x" 
      and outside: "\<And>x. x \<notin> S \<Longrightarrow> p' x = x"
  shows   "inv p = p'"
proof
  fix x show "inv p x = p' x"
  proof (cases "x \<in> S")
    assume [simp]: "x \<in> S"
    from assms have "p' x = p' (p (inv p x))" by (simp add: permutes_inverses)
    also from permutes_inv[OF perm] 
      have "\<dots> = inv p x" by (subst inv) (simp_all add: permutes_in_image)
    finally show "inv p x = p' x" ..
  qed (insert permutes_inv[OF perm], simp_all add: outside permutes_not_in)
qed

lemma permutes_vimage: "f permutes A \<Longrightarrow> f -` A = A"
  by (simp add: bij_vimage_eq_inv_image permutes_bij permutes_image[OF permutes_inv])  


subsection \<open>The number of permutations on a finite set\<close>

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
      using \<open>x \<notin> F\<close> H0 \<open>finite F\<close> by auto
    from insert.hyps Fs have pFs: "card ?pF = fact (n - 1)"
      using \<open>finite F\<close> by auto
    then have "finite ?pF"
      by (auto intro: card_ge_0_finite)
    then have pF'f: "finite ?pF'"
      using H0 \<open>finite F\<close>
      apply (simp only: Collect_case_prod Collect_mem_eq)
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
        from ths(4) \<open>x \<notin> F\<close> eq have "b = ?g (b,p) x"
          unfolding permutes_def
          by (auto simp add: Fun.swap_def fun_upd_def fun_eq_iff)
        also have "\<dots> = ?g (c,q) x"
          using ths(5) \<open>x \<notin> F\<close> eq
          by (auto simp add: swap_def fun_upd_def fun_eq_iff)
        also have "\<dots> = c"
          using ths(5) \<open>x \<notin> F\<close>
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
    from \<open>x \<notin> F\<close> H0 have n0: "n \<noteq> 0"
      using \<open>finite F\<close> by auto
    then have "\<exists>m. n = Suc m"
      by presburger
    then obtain m where n[simp]: "n = Suc m"
      by blast
    from pFs H0 have xFc: "card ?xF = fact n"
      unfolding xfgpF' card_image[OF ginj]
      using \<open>finite F\<close> \<open>finite ?pF\<close>
      apply (simp only: Collect_case_prod Collect_mem_eq card_cartesian_product)
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
  using card_permutations[OF refl fS] 
  by (auto intro: card_ge_0_finite)


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


subsection \<open>Various combinations of transpositions with 2, 1 and 0 common elements\<close>

lemma swap_id_common:" a \<noteq> c \<Longrightarrow> b \<noteq> c \<Longrightarrow>
  Fun.swap a b id \<circ> Fun.swap a c id = Fun.swap b c id \<circ> Fun.swap a b id"
  by (simp add: fun_eq_iff Fun.swap_def)

lemma swap_id_common': "a \<noteq> b \<Longrightarrow> a \<noteq> c \<Longrightarrow>
  Fun.swap a c id \<circ> Fun.swap b c id = Fun.swap b c id \<circ> Fun.swap a b id"
  by (simp add: fun_eq_iff Fun.swap_def)

lemma swap_id_independent: "a \<noteq> c \<Longrightarrow> a \<noteq> d \<Longrightarrow> b \<noteq> c \<Longrightarrow> b \<noteq> d \<Longrightarrow>
  Fun.swap a b id \<circ> Fun.swap c d id = Fun.swap c d id \<circ> Fun.swap a b id"
  by (simp add: fun_eq_iff Fun.swap_def)


subsection \<open>Permutations as transposition sequences\<close>

inductive swapidseq :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
where
  id[simp]: "swapidseq 0 id"
| comp_Suc: "swapidseq n p \<Longrightarrow> a \<noteq> b \<Longrightarrow> swapidseq (Suc n) (Fun.swap a b id \<circ> p)"

declare id[unfolded id_def, simp]

definition "permutation p \<longleftrightarrow> (\<exists>n. swapidseq n p)"


subsection \<open>Some closure properties of the set of permutations, with lengths\<close>

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


subsection \<open>The identity map only has even transposition sequences\<close>

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
  using \<open>swapidseq n id\<close>
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


subsection \<open>Therefore we have a welldefined notion of parity\<close>

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


subsection \<open>And it has the expected composition properties\<close>

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


subsection \<open>A more abstract characterization of permutations\<close>

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
    from \<open>a \<noteq> b\<close> have th: "{x. (Fun.swap a b id \<circ> p) x \<noteq> x} \<subseteq> ?S"
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


subsection \<open>Relation to "permutes"\<close>

lemma permutation_permutes: "permutation p \<longleftrightarrow> (\<exists>S. finite S \<and> p permutes S)"
  unfolding permutation permutes_def bij_iff[symmetric]
  apply (rule iffI, clarify)
  apply (rule exI[where x="{x. p x \<noteq> x}"])
  apply simp
  apply clarsimp
  apply (rule_tac B="S" in finite_subset)
  apply auto
  done


subsection \<open>Hence a sort of induction principle composing by swaps\<close>

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


subsection \<open>Sign of a permutation as a real number\<close>

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

 
subsection \<open>Permuting a list\<close>

text \<open>This function permutes a list by applying a permutation to the indices.\<close>

definition permute_list :: "(nat \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "permute_list f xs = map (\<lambda>i. xs ! (f i)) [0..<length xs]"

lemma permute_list_map: 
  assumes "f permutes {..<length xs}"
  shows   "permute_list f (map g xs) = map g (permute_list f xs)"
  using permutes_in_image[OF assms] by (auto simp: permute_list_def)

lemma permute_list_nth:
  assumes "f permutes {..<length xs}" "i < length xs"
  shows   "permute_list f xs ! i = xs ! f i"
  using permutes_in_image[OF assms(1)] assms(2) 
  by (simp add: permute_list_def)

lemma permute_list_Nil [simp]: "permute_list f [] = []"
  by (simp add: permute_list_def)

lemma length_permute_list [simp]: "length (permute_list f xs) = length xs"
  by (simp add: permute_list_def)

lemma permute_list_compose: 
  assumes "g permutes {..<length xs}"
  shows   "permute_list (f \<circ> g) xs = permute_list g (permute_list f xs)"
  using assms[THEN permutes_in_image] by (auto simp add: permute_list_def)

lemma permute_list_ident [simp]: "permute_list (\<lambda>x. x) xs = xs"
  by (simp add: permute_list_def map_nth)

lemma permute_list_id [simp]: "permute_list id xs = xs"
  by (simp add: id_def)

lemma mset_permute_list [simp]:
  assumes "f permutes {..<length (xs :: 'a list)}"
  shows   "mset (permute_list f xs) = mset xs"
proof (rule multiset_eqI)
  fix y :: 'a
  from assms have [simp]: "f x < length xs \<longleftrightarrow> x < length xs" for x
    using permutes_in_image[OF assms] by auto
  have "count (mset (permute_list f xs)) y = 
          card ((\<lambda>i. xs ! f i) -` {y} \<inter> {..<length xs})"
    by (simp add: permute_list_def mset_map count_image_mset atLeast0LessThan)
  also have "(\<lambda>i. xs ! f i) -` {y} \<inter> {..<length xs} = f -` {i. i < length xs \<and> y = xs ! i}"
    by auto
  also from assms have "card \<dots> = card {i. i < length xs \<and> y = xs ! i}"
    by (intro card_vimage_inj) (auto simp: permutes_inj permutes_surj)
  also have "\<dots> = count (mset xs) y" by (simp add: count_mset length_filter_conv_card)
  finally show "count (mset (permute_list f xs)) y = count (mset xs) y" by simp
qed

lemma set_permute_list [simp]:
  assumes "f permutes {..<length xs}"
  shows   "set (permute_list f xs) = set xs"
  by (rule mset_eq_setD[OF mset_permute_list]) fact

lemma distinct_permute_list [simp]:
  assumes "f permutes {..<length xs}"
  shows   "distinct (permute_list f xs) = distinct xs"
  by (simp add: distinct_count_atmost_1 assms)

lemma permute_list_zip: 
  assumes "f permutes A" "A = {..<length xs}"
  assumes [simp]: "length xs = length ys"
  shows   "permute_list f (zip xs ys) = zip (permute_list f xs) (permute_list f ys)"
proof -
  from permutes_in_image[OF assms(1)] assms(2)
    have [simp]: "f i < length ys \<longleftrightarrow> i < length ys" for i by simp
  have "permute_list f (zip xs ys) = map (\<lambda>i. zip xs ys ! f i) [0..<length ys]"
    by (simp_all add: permute_list_def zip_map_map)
  also have "\<dots> = map (\<lambda>(x, y). (xs ! f x, ys ! f y)) (zip [0..<length ys] [0..<length ys])"
    by (intro nth_equalityI) simp_all
  also have "\<dots> = zip (permute_list f xs) (permute_list f ys)"
    by (simp_all add: permute_list_def zip_map_map)
  finally show ?thesis .
qed

lemma map_of_permute: 
  assumes "\<sigma> permutes fst ` set xs"
  shows   "map_of xs \<circ> \<sigma> = map_of (map (\<lambda>(x,y). (inv \<sigma> x, y)) xs)" (is "_ = map_of (map ?f _)")
proof
  fix x
  from assms have "inj \<sigma>" "surj \<sigma>" by (simp_all add: permutes_inj permutes_surj)
  thus "(map_of xs \<circ> \<sigma>) x = map_of (map ?f xs) x"
    by (induction xs) (auto simp: inv_f_f surj_f_inv_f)
qed


subsection \<open>More lemmas about permutations\<close>

text \<open>
  If two lists correspond to the same multiset, there exists a permutation 
  on the list indices that maps one to the other.
\<close>
lemma mset_eq_permutation:
  assumes mset_eq: "mset (xs::'a list) = mset ys"
  defines [simp]: "n \<equiv> length xs"
  obtains f where "f permutes {..<length ys}" "permute_list f ys = xs"
proof -
  from mset_eq have [simp]: "length xs = length ys"
    by (rule mset_eq_length)
  def indices_of \<equiv> "\<lambda>(x::'a) xs. {i. i < length xs \<and> x = xs ! i}"
  have indices_of_subset: "indices_of x xs \<subseteq> {..<length xs}" for x xs
    unfolding indices_of_def by blast
  have [simp]: "finite (indices_of x xs)" for x xs
    by (rule finite_subset[OF indices_of_subset]) simp_all

  have "\<forall>x\<in>set xs. \<exists>f. bij_betw f (indices_of x xs) (indices_of x ys)"
  proof
    fix x
    from mset_eq have "count (mset xs) x = count (mset ys) x" by simp
    hence "card (indices_of x xs) = card (indices_of x ys)"
      by (simp add: count_mset length_filter_conv_card indices_of_def)
    thus "\<exists>f. bij_betw f (indices_of x xs) (indices_of x ys)"
      by (intro finite_same_card_bij) simp_all
  qed
  hence "\<exists>f. \<forall>x\<in>set xs. bij_betw (f x) (indices_of x xs) (indices_of x ys)"
    by (rule bchoice)
  then guess f .. note f = this
  def g \<equiv> "\<lambda>i. if i < n then f (xs ! i) i else i"

  have bij_f: "bij_betw (\<lambda>i. f (xs ! i) i) (indices_of x xs) (indices_of x ys)"
    if x: "x \<in> set xs" for x
  proof (subst bij_betw_cong)
    from f x show "bij_betw (f x) (indices_of x xs) (indices_of x ys)" by blast
    fix i assume "i \<in> indices_of x xs"
    thus "f (xs ! i) i = f x i" by (simp add: indices_of_def)
  qed

  hence "bij_betw (\<lambda>i. f (xs ! i) i) (\<Union>x\<in>set xs. indices_of x xs) (\<Union>x\<in>set xs. indices_of x ys)"
    by (intro bij_betw_UNION_disjoint) (auto simp add: disjoint_family_on_def indices_of_def)
  also have "(\<Union>x\<in>set xs. indices_of x xs) = {..<n}" by (auto simp: indices_of_def)
  also from mset_eq have "set xs = set ys" by (rule mset_eq_setD) 
  also have "(\<Union>x\<in>set ys. indices_of x ys) = {..<n}"
    by (auto simp: indices_of_def set_conv_nth)
  also have "bij_betw (\<lambda>i. f (xs ! i) i) {..<n} {..<n} \<longleftrightarrow> bij_betw g {..<n} {..<n}"
    by (intro bij_betw_cong) (simp_all add: g_def)
  finally have "g permutes {..<length ys}"
    by (intro bij_imp_permutes refl) (simp_all add: g_def)

  moreover have "permute_list g ys = xs" 
  proof (rule sym, intro nth_equalityI allI impI)
    fix i assume i: "i < length xs"
    from i have "permute_list g ys ! i = ys ! f (xs ! i) i"
      by (simp add: permute_list_def g_def)
    also from i have "i \<in> indices_of (xs ! i) xs" by (simp add: indices_of_def)
    with bij_f[of "xs ! i"] i have "f (xs ! i) i \<in> indices_of (xs ! i) ys"
      by (auto simp: bij_betw_def)
    hence "ys ! f (xs ! i) i = xs ! i" by (simp add: indices_of_def)
    finally show "xs ! i = permute_list g ys ! i" ..
  qed simp_all

  ultimately show ?thesis by (rule that)
qed

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
  from setsum.reindex[OF th0, of f] show ?thesis unfolding th1 th2 .
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
  from setsum.reindex[OF th1, of f] show ?thesis unfolding th0 th1 th3 .
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
  from setsum.reindex[OF th1, of f]
  show ?thesis unfolding th0 th1 th3 .
qed


subsection \<open>Sum over a set of permutations (could generalize to iteration)\<close>

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
    unfolding setsum.cartesian_product
    unfolding th1[symmetric]
    unfolding th0
  proof (rule setsum.reindex)
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
            cong del: if_weak_cong split: if_split_asm)
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


subsection \<open>Constructing permutations from association lists\<close>

definition list_permutes where
  "list_permutes xs A \<longleftrightarrow> set (map fst xs) \<subseteq> A \<and> set (map snd xs) = set (map fst xs) \<and> 
     distinct (map fst xs) \<and> distinct (map snd xs)"

lemma list_permutesI [simp]:
  assumes "set (map fst xs) \<subseteq> A" "set (map snd xs) = set (map fst xs)" "distinct (map fst xs)"
  shows   "list_permutes xs A"
proof -
  from assms(2,3) have "distinct (map snd xs)"
    by (intro card_distinct) (simp_all add: distinct_card del: set_map)
  with assms show ?thesis by (simp add: list_permutes_def)
qed

definition permutation_of_list where
  "permutation_of_list xs x = (case map_of xs x of None \<Rightarrow> x | Some y \<Rightarrow> y)"

lemma permutation_of_list_Cons:
  "permutation_of_list ((x,y) # xs) x' = (if x = x' then y else permutation_of_list xs x')"
  by (simp add: permutation_of_list_def)

fun inverse_permutation_of_list where
  "inverse_permutation_of_list [] x = x"
| "inverse_permutation_of_list ((y,x')#xs) x =
     (if x = x' then y else inverse_permutation_of_list xs x)"

declare inverse_permutation_of_list.simps [simp del]

lemma inj_on_map_of:
  assumes "distinct (map snd xs)"
  shows   "inj_on (map_of xs) (set (map fst xs))"
proof (rule inj_onI)
  fix x y assume xy: "x \<in> set (map fst xs)" "y \<in> set (map fst xs)"
  assume eq: "map_of xs x = map_of xs y"
  from xy obtain x' y' 
    where x'y': "map_of xs x = Some x'" "map_of xs y = Some y'" 
    by (cases "map_of xs x"; cases "map_of xs y")
       (simp_all add: map_of_eq_None_iff)
  moreover from this x'y' have "(x,x') \<in> set xs" "(y,y') \<in> set xs"
    by (force dest: map_of_SomeD)+
  moreover from this eq x'y' have "x' = y'" by simp
  ultimately show "x = y" using assms
    by (force simp: distinct_map dest: inj_onD[of _ _ "(x,x')" "(y,y')"])
qed

lemma inj_on_the: "None \<notin> A \<Longrightarrow> inj_on the A"
  by (auto simp: inj_on_def option.the_def split: option.splits)

lemma inj_on_map_of':
  assumes "distinct (map snd xs)"
  shows   "inj_on (the \<circ> map_of xs) (set (map fst xs))"
  by (intro comp_inj_on inj_on_map_of assms inj_on_the)
     (force simp: eq_commute[of None] map_of_eq_None_iff)

lemma image_map_of:
  assumes "distinct (map fst xs)"
  shows   "map_of xs ` set (map fst xs) = Some ` set (map snd xs)"
  using assms by (auto simp: rev_image_eqI)

lemma the_Some_image [simp]: "the ` Some ` A = A"
  by (subst image_image) simp

lemma image_map_of':
  assumes "distinct (map fst xs)"
  shows   "(the \<circ> map_of xs) ` set (map fst xs) = set (map snd xs)"
  by (simp only: image_comp [symmetric] image_map_of assms the_Some_image)

lemma permutation_of_list_permutes [simp]:
  assumes "list_permutes xs A"
  shows   "permutation_of_list xs permutes A" (is "?f permutes _")
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

lemma permutation_of_list_id:
  assumes "x \<notin> set (map fst xs)"
  shows   "permutation_of_list xs x = x"
  using assms by (induction xs) (auto simp: permutation_of_list_Cons)

lemma permutation_of_list_unique':
  assumes "distinct (map fst xs)" "(x, y) \<in> set xs"
  shows   "permutation_of_list xs x = y"
  using assms by (induction xs) (force simp: permutation_of_list_Cons)+

lemma permutation_of_list_unique:
  assumes "list_permutes xs A" "(x,y) \<in> set xs"
  shows   "permutation_of_list xs x = y"
  using assms by (intro permutation_of_list_unique') (simp_all add: list_permutes_def)

lemma inverse_permutation_of_list_id:
  assumes "x \<notin> set (map snd xs)"
  shows   "inverse_permutation_of_list xs x = x"
  using assms by (induction xs) auto

lemma inverse_permutation_of_list_unique':
  assumes "distinct (map snd xs)" "(x, y) \<in> set xs"
  shows   "inverse_permutation_of_list xs y = x"
  using assms by (induction xs) (force simp: inverse_permutation_of_list.simps)+

lemma inverse_permutation_of_list_unique:
  assumes "list_permutes xs A" "(x,y) \<in> set xs"
  shows   "inverse_permutation_of_list xs y = x"
  using assms by (intro inverse_permutation_of_list_unique') (simp_all add: list_permutes_def)

lemma inverse_permutation_of_list_correct:
  assumes "list_permutes xs (A :: 'a set)"
  shows   "inverse_permutation_of_list xs = inv (permutation_of_list xs)"
proof (rule ext, rule sym, subst permutes_inv_eq)
  from assms show "permutation_of_list xs permutes A" by simp
next
  fix x
  show "permutation_of_list xs (inverse_permutation_of_list xs x) = x"
  proof (cases "x \<in> set (map snd xs)")
    case True
    then obtain y where "(y, x) \<in> set xs" by force
    with assms show ?thesis
      by (simp add: inverse_permutation_of_list_unique permutation_of_list_unique)
  qed (insert assms, auto simp: list_permutes_def
         inverse_permutation_of_list_id permutation_of_list_id)
qed

end

