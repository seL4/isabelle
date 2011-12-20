(*  Title:      HOL/Library/Permutations.thy
    Author:     Amine Chaieb, University of Cambridge
*)

header {* Permutations, both general and specifically on finite sets.*}

theory Permutations
imports Parity Fact
begin

definition permutes (infixr "permutes" 41) where
  "(p permutes S) \<longleftrightarrow> (\<forall>x. x \<notin> S \<longrightarrow> p x = x) \<and> (\<forall>y. \<exists>!x. p x = y)"

(* ------------------------------------------------------------------------- *)
(* Transpositions.                                                           *)
(* ------------------------------------------------------------------------- *)

lemma swapid_sym: "Fun.swap a b id = Fun.swap b a id"
  by (auto simp add: fun_eq_iff swap_def fun_upd_def)
lemma swap_id_refl: "Fun.swap a a id = id" by simp
lemma swap_id_sym: "Fun.swap a b id = Fun.swap b a id"
  by (rule ext, simp add: swap_def)
lemma swap_id_idempotent[simp]: "Fun.swap a b id o Fun.swap a b id = id"
  by (rule ext, auto simp add: swap_def)

lemma inv_unique_comp: assumes fg: "f o g = id" and gf: "g o f = id"
  shows "inv f = g"
  using fg gf inv_equality[of g f] by (auto simp add: fun_eq_iff)

lemma inverse_swap_id: "inv (Fun.swap a b id) = Fun.swap a b id"
  by (rule inv_unique_comp, simp_all)

lemma swap_id_eq: "Fun.swap a b id x = (if x = a then b else if x = b then a else x)"
  by (simp add: swap_def)

(* ------------------------------------------------------------------------- *)
(* Basic consequences of the definition.                                     *)
(* ------------------------------------------------------------------------- *)

lemma permutes_in_image: "p permutes S \<Longrightarrow> p x \<in> S \<longleftrightarrow> x \<in> S"
  unfolding permutes_def by metis

lemma permutes_image: assumes pS: "p permutes S" shows "p ` S = S"
  using pS
  unfolding permutes_def
  apply -
  apply (rule set_eqI)
  apply (simp add: image_iff)
  apply metis
  done

lemma permutes_inj: "p permutes S ==> inj p "
  unfolding permutes_def inj_on_def by blast

lemma permutes_surj: "p permutes s ==> surj p"
  unfolding permutes_def surj_def by metis

lemma permutes_inv_o: assumes pS: "p permutes S"
  shows " p o inv p = id"
  and "inv p o p = id"
  using permutes_inj[OF pS] permutes_surj[OF pS]
  unfolding inj_iff[symmetric] surj_iff[symmetric] by blast+


lemma permutes_inverses:
  fixes p :: "'a \<Rightarrow> 'a"
  assumes pS: "p permutes S"
  shows "p (inv p x) = x"
  and "inv p (p x) = x"
  using permutes_inv_o[OF pS, unfolded fun_eq_iff o_def] by auto

lemma permutes_subset: "p permutes S \<Longrightarrow> S \<subseteq> T ==> p permutes T"
  unfolding permutes_def by blast

lemma permutes_empty[simp]: "p permutes {} \<longleftrightarrow> p = id"
  unfolding fun_eq_iff permutes_def apply simp by metis

lemma permutes_sing[simp]: "p permutes {a} \<longleftrightarrow> p = id"
  unfolding fun_eq_iff permutes_def apply simp by metis

lemma permutes_univ: "p permutes UNIV \<longleftrightarrow> (\<forall>y. \<exists>!x. p x = y)"
  unfolding permutes_def by simp

lemma permutes_inv_eq: "p permutes S ==> inv p y = x \<longleftrightarrow> p x = y"
  unfolding permutes_def inv_def apply auto
  apply (erule allE[where x=y])
  apply (erule allE[where x=y])
  apply (rule someI_ex) apply blast
  apply (rule some1_equality)
  apply blast
  apply blast
  done

lemma permutes_swap_id: "a \<in> S \<Longrightarrow> b \<in> S ==> Fun.swap a b id permutes S"
  unfolding permutes_def swap_def fun_upd_def  by auto metis

lemma permutes_superset:
  "p permutes S \<Longrightarrow> (\<forall>x \<in> S - T. p x = x) \<Longrightarrow> p permutes T"
by (simp add: Ball_def permutes_def) metis

(* ------------------------------------------------------------------------- *)
(* Group properties.                                                         *)
(* ------------------------------------------------------------------------- *)

lemma permutes_id: "id permutes S" unfolding permutes_def by simp

lemma permutes_compose: "p permutes S \<Longrightarrow> q permutes S ==> q o p permutes S"
  unfolding permutes_def o_def by metis

lemma permutes_inv: assumes pS: "p permutes S" shows "inv p permutes S"
  using pS unfolding permutes_def permutes_inv_eq[OF pS] by metis

lemma permutes_inv_inv: assumes pS: "p permutes S" shows "inv (inv p) = p"
  unfolding fun_eq_iff permutes_inv_eq[OF pS] permutes_inv_eq[OF permutes_inv[OF pS]]
  by blast

(* ------------------------------------------------------------------------- *)
(* The number of permutations on a finite set.                               *)
(* ------------------------------------------------------------------------- *)

lemma permutes_insert_lemma:
  assumes pS: "p permutes (insert a S)"
  shows "Fun.swap a (p a) id o p permutes S"
  apply (rule permutes_superset[where S = "insert a S"])
  apply (rule permutes_compose[OF pS])
  apply (rule permutes_swap_id, simp)
  using permutes_in_image[OF pS, of a] apply simp
  apply (auto simp add: Ball_def swap_def)
  done

lemma permutes_insert: "{p. p permutes (insert a S)} =
        (\<lambda>(b,p). Fun.swap a b id o p) ` {(b,p). b \<in> insert a S \<and> p \<in> {p. p permutes S}}"
proof-

  {fix p
    {assume pS: "p permutes insert a S"
      let ?b = "p a"
      let ?q = "Fun.swap a (p a) id o p"
      have th0: "p = Fun.swap a ?b id o ?q" unfolding fun_eq_iff o_assoc by simp
      have th1: "?b \<in> insert a S " unfolding permutes_in_image[OF pS] by simp
      from permutes_insert_lemma[OF pS] th0 th1
      have "\<exists> b q. p = Fun.swap a b id o q \<and> b \<in> insert a S \<and> q permutes S" by blast}
    moreover
    {fix b q assume bq: "p = Fun.swap a b id o q" "b \<in> insert a S" "q permutes S"
      from permutes_subset[OF bq(3), of "insert a S"]
      have qS: "q permutes insert a S" by auto
      have aS: "a \<in> insert a S" by simp
      from bq(1) permutes_compose[OF qS permutes_swap_id[OF aS bq(2)]]
      have "p permutes insert a S"  by simp }
    ultimately have "p permutes insert a S \<longleftrightarrow> (\<exists> b q. p = Fun.swap a b id o q \<and> b \<in> insert a S \<and> q permutes S)" by blast}
  thus ?thesis by auto
qed

lemma card_permutations: assumes Sn: "card S = n" and fS: "finite S"
  shows "card {p. p permutes S} = fact n"
using fS Sn proof (induct arbitrary: n)
  case empty thus ?case by simp
next
  case (insert x F)
  { fix n assume H0: "card (insert x F) = n"
    let ?xF = "{p. p permutes insert x F}"
    let ?pF = "{p. p permutes F}"
    let ?pF' = "{(b, p). b \<in> insert x F \<and> p \<in> ?pF}"
    let ?g = "(\<lambda>(b, p). Fun.swap x b id \<circ> p)"
    from permutes_insert[of x F]
    have xfgpF': "?xF = ?g ` ?pF'" .
    have Fs: "card F = n - 1" using `x \<notin> F` H0 `finite F` by auto
    from insert.hyps Fs have pFs: "card ?pF = fact (n - 1)" using `finite F` by auto
    moreover hence "finite ?pF" using fact_gt_zero_nat by (auto intro: card_ge_0_finite)
    ultimately have pF'f: "finite ?pF'" using H0 `finite F`
      apply (simp only: Collect_split Collect_mem_eq)
      apply (rule finite_cartesian_product)
      apply simp_all
      done

    have ginj: "inj_on ?g ?pF'"
    proof-
      {
        fix b p c q assume bp: "(b,p) \<in> ?pF'" and cq: "(c,q) \<in> ?pF'"
          and eq: "?g (b,p) = ?g (c,q)"
        from bp cq have ths: "b \<in> insert x F" "c \<in> insert x F" "x \<in> insert x F" "p permutes F" "q permutes F" by auto
        from ths(4) `x \<notin> F` eq have "b = ?g (b,p) x" unfolding permutes_def
          by (auto simp add: swap_def fun_upd_def fun_eq_iff)
        also have "\<dots> = ?g (c,q) x" using ths(5) `x \<notin> F` eq
          by (auto simp add: swap_def fun_upd_def fun_eq_iff)
        also have "\<dots> = c"using ths(5) `x \<notin> F` unfolding permutes_def
          by (auto simp add: swap_def fun_upd_def fun_eq_iff)
        finally have bc: "b = c" .
        hence "Fun.swap x b id = Fun.swap x c id" by simp
        with eq have "Fun.swap x b id o p = Fun.swap x b id o q" by simp
        hence "Fun.swap x b id o (Fun.swap x b id o p) = Fun.swap x b id o (Fun.swap x b id o q)" by simp
        hence "p = q" by (simp add: o_assoc)
        with bc have "(b,p) = (c,q)" by simp
      }
      thus ?thesis  unfolding inj_on_def by blast
    qed
    from `x \<notin> F` H0 have n0: "n \<noteq> 0 " using `finite F` by auto
    hence "\<exists>m. n = Suc m" by arith
    then obtain m where n[simp]: "n = Suc m" by blast
    from pFs H0 have xFc: "card ?xF = fact n"
      unfolding xfgpF' card_image[OF ginj] using `finite F` `finite ?pF`
      apply (simp only: Collect_split Collect_mem_eq card_cartesian_product)
      by simp
    from finite_imageI[OF pF'f, of ?g] have xFf: "finite ?xF" unfolding xfgpF' by simp
    have "card ?xF = fact n"
      using xFf xFc unfolding xFf by blast
  }
  thus ?case using insert by simp
qed

lemma finite_permutations: assumes fS: "finite S" shows "finite {p. p permutes S}"
  using card_permutations[OF refl fS] fact_gt_zero_nat
  by (auto intro: card_ge_0_finite)

(* ------------------------------------------------------------------------- *)
(* Permutations of index set for iterated operations.                        *)
(* ------------------------------------------------------------------------- *)

lemma (in ab_semigroup_mult) fold_image_permute: assumes fS: "finite S" and pS: "p permutes S"
  shows "fold_image times f z S = fold_image times (f o p) z S"
  using fold_image_reindex[OF fS subset_inj_on[OF permutes_inj[OF pS], of S, simplified], of f z]
  unfolding permutes_image[OF pS] .
lemma (in ab_semigroup_add) fold_image_permute: assumes fS: "finite S" and pS: "p permutes S"
  shows "fold_image plus f z S = fold_image plus (f o p) z S"
proof-
  interpret ab_semigroup_mult plus apply unfold_locales apply (simp add: add_assoc)
    apply (simp add: add_commute) done
  from fold_image_reindex[OF fS subset_inj_on[OF permutes_inj[OF pS], of S, simplified], of f z]
  show ?thesis
  unfolding permutes_image[OF pS] .
qed

lemma setsum_permute: assumes pS: "p permutes S"
  shows "setsum f S = setsum (f o p) S"
  unfolding setsum_def using fold_image_permute[of S p f 0] pS by clarsimp

lemma setsum_permute_natseg:assumes pS: "p permutes {m .. n}"
  shows "setsum f {m .. n} = setsum (f o p) {m .. n}"
  using setsum_permute[OF pS, of f ] pS by blast

lemma setprod_permute: assumes pS: "p permutes S"
  shows "setprod f S = setprod (f o p) S"
  unfolding setprod_def
  using ab_semigroup_mult_class.fold_image_permute[of S p f 1] pS by clarsimp

lemma setprod_permute_natseg:assumes pS: "p permutes {m .. n}"
  shows "setprod f {m .. n} = setprod (f o p) {m .. n}"
  using setprod_permute[OF pS, of f ] pS by blast

(* ------------------------------------------------------------------------- *)
(* Various combinations of transpositions with 2, 1 and 0 common elements.   *)
(* ------------------------------------------------------------------------- *)

lemma swap_id_common:" a \<noteq> c \<Longrightarrow> b \<noteq> c \<Longrightarrow>  Fun.swap a b id o Fun.swap a c id = Fun.swap b c id o Fun.swap a b id" by (simp add: fun_eq_iff swap_def)

lemma swap_id_common': "~(a = b) \<Longrightarrow> ~(a = c) \<Longrightarrow> Fun.swap a c id o Fun.swap b c id = Fun.swap b c id o Fun.swap a b id" by (simp add: fun_eq_iff swap_def)

lemma swap_id_independent: "~(a = c) \<Longrightarrow> ~(a = d) \<Longrightarrow> ~(b = c) \<Longrightarrow> ~(b = d) ==> Fun.swap a b id o Fun.swap c d id = Fun.swap c d id o Fun.swap a b id"
  by (simp add: swap_def fun_eq_iff)

(* ------------------------------------------------------------------------- *)
(* Permutations as transposition sequences.                                  *)
(* ------------------------------------------------------------------------- *)


inductive swapidseq :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool" where
  id[simp]: "swapidseq 0 id"
| comp_Suc: "swapidseq n p \<Longrightarrow> a \<noteq> b \<Longrightarrow> swapidseq (Suc n) (Fun.swap a b id o p)"

declare id[unfolded id_def, simp]
definition "permutation p \<longleftrightarrow> (\<exists>n. swapidseq n p)"

(* ------------------------------------------------------------------------- *)
(* Some closure properties of the set of permutations, with lengths.         *)
(* ------------------------------------------------------------------------- *)

lemma permutation_id[simp]: "permutation id"unfolding permutation_def
  by (rule exI[where x=0], simp)
declare permutation_id[unfolded id_def, simp]

lemma swapidseq_swap: "swapidseq (if a = b then 0 else 1) (Fun.swap a b id)"
  apply clarsimp
  using comp_Suc[of 0 id a b] by simp

lemma permutation_swap_id: "permutation (Fun.swap a b id)"
  apply (cases "a=b", simp_all)
  unfolding permutation_def using swapidseq_swap[of a b] by blast

lemma swapidseq_comp_add: "swapidseq n p \<Longrightarrow> swapidseq m q ==> swapidseq (n + m) (p o q)"
  proof (induct n p arbitrary: m q rule: swapidseq.induct)
    case (id m q) thus ?case by simp
  next
    case (comp_Suc n p a b m q)
    have th: "Suc n + m = Suc (n + m)" by arith
    show ?case unfolding th o_assoc[symmetric]
      apply (rule swapidseq.comp_Suc) using comp_Suc.hyps(2)[OF comp_Suc.prems]  comp_Suc.hyps(3) by blast+
qed

lemma permutation_compose: "permutation p \<Longrightarrow> permutation q ==> permutation(p o q)"
  unfolding permutation_def using swapidseq_comp_add[of _ p _ q] by metis

lemma swapidseq_endswap: "swapidseq n p \<Longrightarrow> a \<noteq> b ==> swapidseq (Suc n) (p o Fun.swap a b id)"
  apply (induct n p rule: swapidseq.induct)
  using swapidseq_swap[of a b]
  by (auto simp add: o_assoc[symmetric] intro: swapidseq.comp_Suc)

lemma swapidseq_inverse_exists: "swapidseq n p ==> \<exists>q. swapidseq n q \<and> p o q = id \<and> q o p = id"
proof(induct n p rule: swapidseq.induct)
  case id  thus ?case by (rule exI[where x=id], simp)
next
  case (comp_Suc n p a b)
  from comp_Suc.hyps obtain q where q: "swapidseq n q" "p \<circ> q = id" "q \<circ> p = id" by blast
  let ?q = "q o Fun.swap a b id"
  note H = comp_Suc.hyps
  from swapidseq_swap[of a b] H(3)  have th0: "swapidseq 1 (Fun.swap a b id)" by simp
  from swapidseq_comp_add[OF q(1) th0] have th1:"swapidseq (Suc n) ?q" by simp
  have "Fun.swap a b id o p o ?q = Fun.swap a b id o (p o q) o Fun.swap a b id" by (simp add: o_assoc)
  also have "\<dots> = id" by (simp add: q(2))
  finally have th2: "Fun.swap a b id o p o ?q = id" .
  have "?q \<circ> (Fun.swap a b id \<circ> p) = q \<circ> (Fun.swap a b id o Fun.swap a b id) \<circ> p" by (simp only: o_assoc)
  hence "?q \<circ> (Fun.swap a b id \<circ> p) = id" by (simp add: q(3))
  with th1 th2 show ?case by blast
qed


lemma swapidseq_inverse: assumes H: "swapidseq n p" shows "swapidseq n (inv p)"
  using swapidseq_inverse_exists[OF H] inv_unique_comp[of p] by auto

lemma permutation_inverse: "permutation p ==> permutation (inv p)"
  using permutation_def swapidseq_inverse by blast

(* ------------------------------------------------------------------------- *)
(* The identity map only has even transposition sequences.                   *)
(* ------------------------------------------------------------------------- *)

lemma symmetry_lemma:"(\<And>a b c d. P a b c d ==> P a b d c) \<Longrightarrow>
   (\<And>a b c d. a \<noteq> b \<Longrightarrow> c \<noteq> d \<Longrightarrow> (a = c \<and> b = d \<or>  a = c \<and> b \<noteq> d \<or> a \<noteq> c \<and> b = d \<or> a \<noteq> c \<and> a \<noteq> d \<and> b \<noteq> c \<and> b \<noteq> d) ==> P a b c d)
   ==> (\<And>a b c d. a \<noteq> b --> c \<noteq> d \<longrightarrow>  P a b c d)" by metis

lemma swap_general: "a \<noteq> b \<Longrightarrow> c \<noteq> d \<Longrightarrow> Fun.swap a b id o Fun.swap c d id = id \<or>
  (\<exists>x y z. x \<noteq> a \<and> y \<noteq> a \<and> z \<noteq> a \<and> x \<noteq> y \<and> Fun.swap a b id o Fun.swap c d id = Fun.swap x y id o Fun.swap a z id)"
proof-
  assume H: "a\<noteq>b" "c\<noteq>d"
have "a \<noteq> b \<longrightarrow> c \<noteq> d \<longrightarrow>
(  Fun.swap a b id o Fun.swap c d id = id \<or>
  (\<exists>x y z. x \<noteq> a \<and> y \<noteq> a \<and> z \<noteq> a \<and> x \<noteq> y \<and> Fun.swap a b id o Fun.swap c d id = Fun.swap x y id o Fun.swap a z id))"
  apply (rule symmetry_lemma[where a=a and b=b and c=c and d=d])
  apply (simp_all only: swapid_sym)
  apply (case_tac "a = c \<and> b = d", clarsimp simp only: swapid_sym swap_id_idempotent)
  apply (case_tac "a = c \<and> b \<noteq> d")
  apply (rule disjI2)
  apply (rule_tac x="b" in exI)
  apply (rule_tac x="d" in exI)
  apply (rule_tac x="b" in exI)
  apply (clarsimp simp add: fun_eq_iff swap_def)
  apply (case_tac "a \<noteq> c \<and> b = d")
  apply (rule disjI2)
  apply (rule_tac x="c" in exI)
  apply (rule_tac x="d" in exI)
  apply (rule_tac x="c" in exI)
  apply (clarsimp simp add: fun_eq_iff swap_def)
  apply (rule disjI2)
  apply (rule_tac x="c" in exI)
  apply (rule_tac x="d" in exI)
  apply (rule_tac x="b" in exI)
  apply (clarsimp simp add: fun_eq_iff swap_def)
  done
with H show ?thesis by metis
qed

lemma swapidseq_id_iff[simp]: "swapidseq 0 p \<longleftrightarrow> p = id"
  using swapidseq.cases[of 0 p "p = id"]
  by auto

lemma swapidseq_cases: "swapidseq n p \<longleftrightarrow> (n=0 \<and> p = id \<or> (\<exists>a b q m. n = Suc m \<and> p = Fun.swap a b id o q \<and> swapidseq m q \<and> a\<noteq> b))"
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
  assumes spn: "swapidseq n p" and ab: "a\<noteq>b" and pa: "(Fun.swap a b id o p) a = a"
  shows "n \<noteq> 0 \<and> swapidseq (n - 1) (Fun.swap a b id o p)"
  using spn ab pa
proof(induct n arbitrary: p a b)
  case 0 thus ?case by (auto simp add: swap_def fun_upd_def)
next
  case (Suc n p a b)
  from Suc.prems(1) swapidseq_cases[of "Suc n" p] obtain
    c d q m where cdqm: "Suc n = Suc m" "p = Fun.swap c d id o q" "swapidseq m q" "c \<noteq> d" "n = m"
    by auto
  {assume H: "Fun.swap a b id o Fun.swap c d id = id"

    have ?case apply (simp only: cdqm o_assoc H)
      by (simp add: cdqm)}
  moreover
  { fix x y z
    assume H: "x\<noteq>a" "y\<noteq>a" "z \<noteq>a" "x \<noteq>y"
      "Fun.swap a b id o Fun.swap c d id = Fun.swap x y id o Fun.swap a z id"
    from H have az: "a \<noteq> z" by simp

    {fix h have "(Fun.swap x y id o h) a = a \<longleftrightarrow> h a = a"
      using H by (simp add: swap_def)}
    note th3 = this
    from cdqm(2) have "Fun.swap a b id o p = Fun.swap a b id o (Fun.swap c d id o q)" by simp
    hence "Fun.swap a b id o p = Fun.swap x y id o (Fun.swap a z id o q)" by (simp add: o_assoc H)
    hence "(Fun.swap a b id o p) a = (Fun.swap x y id o (Fun.swap a z id o q)) a" by simp
    hence "(Fun.swap x y id o (Fun.swap a z id o q)) a  = a" unfolding Suc by metis
    hence th1: "(Fun.swap a z id o q) a = a" unfolding th3 .
    from Suc.hyps[OF cdqm(3)[ unfolded cdqm(5)[symmetric]] az th1]
    have th2: "swapidseq (n - 1) (Fun.swap a z id o q)" "n \<noteq> 0" by blast+
    have th: "Suc n - 1 = Suc (n - 1)" using th2(2) by auto
    have ?case unfolding cdqm(2) H o_assoc th
      apply (simp only: Suc_not_Zero simp_thms o_assoc[symmetric])
      apply (rule comp_Suc)
      using th2 H apply blast+
      done}
  ultimately show ?case using swap_general[OF Suc.prems(2) cdqm(4)] by metis
qed

lemma swapidseq_identity_even:
  assumes "swapidseq n (id :: 'a \<Rightarrow> 'a)" shows "even n"
  using `swapidseq n id`
proof(induct n rule: nat_less_induct)
  fix n
  assume H: "\<forall>m<n. swapidseq m (id::'a \<Rightarrow> 'a) \<longrightarrow> even m" "swapidseq n (id :: 'a \<Rightarrow> 'a)"
  {assume "n = 0" hence "even n" by arith}
  moreover
  {fix a b :: 'a and q m
    assume h: "n = Suc m" "(id :: 'a \<Rightarrow> 'a) = Fun.swap a b id \<circ> q" "swapidseq m q" "a \<noteq> b"
    from fixing_swapidseq_decrease[OF h(3,4), unfolded h(2)[symmetric]]
    have m: "m \<noteq> 0" "swapidseq (m - 1) (id :: 'a \<Rightarrow> 'a)" by auto
    from h m have mn: "m - 1 < n" by arith
    from H(1)[rule_format, OF mn m(2)] h(1) m(1) have "even n" apply arith done}
  ultimately show "even n" using H(2)[unfolded swapidseq_cases[of n id]] by auto
qed

(* ------------------------------------------------------------------------- *)
(* Therefore we have a welldefined notion of parity.                         *)
(* ------------------------------------------------------------------------- *)

definition "evenperm p = even (SOME n. swapidseq n p)"

lemma swapidseq_even_even: assumes
  m: "swapidseq m p" and n: "swapidseq n p"
  shows "even m \<longleftrightarrow> even n"
proof-
  from swapidseq_inverse_exists[OF n]
  obtain q where q: "swapidseq n q" "p \<circ> q = id" "q \<circ> p = id" by blast

  from swapidseq_identity_even[OF swapidseq_comp_add[OF m q(1), unfolded q]]
  show ?thesis by arith
qed

lemma evenperm_unique: assumes p: "swapidseq n p" and n:"even n = b"
  shows "evenperm p = b"
  unfolding n[symmetric] evenperm_def
  apply (rule swapidseq_even_even[where p = p])
  apply (rule someI[where x = n])
  using p by blast+

(* ------------------------------------------------------------------------- *)
(* And it has the expected composition properties.                           *)
(* ------------------------------------------------------------------------- *)

lemma evenperm_id[simp]: "evenperm id = True"
  apply (rule evenperm_unique[where n = 0]) by simp_all

lemma evenperm_swap: "evenperm (Fun.swap a b id) = (a = b)"
apply (rule evenperm_unique[where n="if a = b then 0 else 1"])
by (simp_all add: swapidseq_swap)

lemma evenperm_comp:
  assumes p: "permutation p" and q:"permutation q"
  shows "evenperm (p o q) = (evenperm p = evenperm q)"
proof-
  from p q obtain
    n m where n: "swapidseq n p" and m: "swapidseq m q"
    unfolding permutation_def by blast
  note nm =  swapidseq_comp_add[OF n m]
  have th: "even (n + m) = (even n \<longleftrightarrow> even m)" by arith
  from evenperm_unique[OF n refl] evenperm_unique[OF m refl]
    evenperm_unique[OF nm th]
  show ?thesis by blast
qed

lemma evenperm_inv: assumes p: "permutation p"
  shows "evenperm (inv p) = evenperm p"
proof-
  from p obtain n where n: "swapidseq n p" unfolding permutation_def by blast
  from evenperm_unique[OF swapidseq_inverse[OF n] evenperm_unique[OF n refl, symmetric]]
  show ?thesis .
qed

(* ------------------------------------------------------------------------- *)
(* A more abstract characterization of permutations.                         *)
(* ------------------------------------------------------------------------- *)


lemma bij_iff: "bij f \<longleftrightarrow> (\<forall>x. \<exists>!y. f y = x)"
  unfolding bij_def inj_on_def surj_def
  apply auto
  apply metis
  apply metis
  done

lemma permutation_bijective:
  assumes p: "permutation p"
  shows "bij p"
proof-
  from p obtain n where n: "swapidseq n p" unfolding permutation_def by blast
  from swapidseq_inverse_exists[OF n] obtain q where
    q: "swapidseq n q" "p \<circ> q = id" "q \<circ> p = id" by blast
  thus ?thesis unfolding bij_iff  apply (auto simp add: fun_eq_iff) apply metis done
qed

lemma permutation_finite_support: assumes p: "permutation p"
  shows "finite {x. p x \<noteq> x}"
proof-
  from p obtain n where n: "swapidseq n p" unfolding permutation_def by blast
  from n show ?thesis
  proof(induct n p rule: swapidseq.induct)
    case id thus ?case by simp
  next
    case (comp_Suc n p a b)
    let ?S = "insert a (insert b {x. p x \<noteq> x})"
    from comp_Suc.hyps(2) have fS: "finite ?S" by simp
    from `a \<noteq> b` have th: "{x. (Fun.swap a b id o p) x \<noteq> x} \<subseteq> ?S"
      by (auto simp add: swap_def)
    from finite_subset[OF th fS] show ?case  .
qed
qed

lemma bij_inv_eq_iff: "bij p ==> x = inv p y \<longleftrightarrow> p x = y"
  using surj_f_inv_f[of p] inv_f_f[of f] by (auto simp add: bij_def)

lemma bij_swap_comp:
  assumes bp: "bij p" shows "Fun.swap a b id o p = Fun.swap (inv p a) (inv p b) p"
  using surj_f_inv_f[OF bij_is_surj[OF bp]]
  by (simp add: fun_eq_iff swap_def bij_inv_eq_iff[OF bp])

lemma bij_swap_ompose_bij: "bij p \<Longrightarrow> bij (Fun.swap a b id o p)"
proof-
  assume H: "bij p"
  show ?thesis
    unfolding bij_swap_comp[OF H] bij_swap_iff
    using H .
qed

lemma permutation_lemma:
  assumes fS: "finite S" and p: "bij p" and pS: "\<forall>x. x\<notin> S \<longrightarrow> p x = x"
  shows "permutation p"
using fS p pS
proof(induct S arbitrary: p rule: finite_induct)
  case (empty p) thus ?case by simp
next
  case (insert a F p)
  let ?r = "Fun.swap a (p a) id o p"
  let ?q = "Fun.swap a (p a) id o ?r "
  have raa: "?r a = a" by (simp add: swap_def)
  from bij_swap_ompose_bij[OF insert(4)]
  have br: "bij ?r"  .

  from insert raa have th: "\<forall>x. x \<notin> F \<longrightarrow> ?r x = x"
    apply (clarsimp simp add: swap_def)
    apply (erule_tac x="x" in allE)
    apply auto
    unfolding bij_iff apply metis
    done
  from insert(3)[OF br th]
  have rp: "permutation ?r" .
  have "permutation ?q" by (simp add: permutation_compose permutation_swap_id rp)
  thus ?case by (simp add: o_assoc)
qed

lemma permutation: "permutation p \<longleftrightarrow> bij p \<and> finite {x. p x \<noteq> x}"
  (is "?lhs \<longleftrightarrow> ?b \<and> ?f")
proof
  assume p: ?lhs
  from p permutation_bijective permutation_finite_support show "?b \<and> ?f" by auto
next
  assume bf: "?b \<and> ?f"
  hence bf: "?f" "?b" by blast+
  from permutation_lemma[OF bf] show ?lhs by blast
qed

lemma permutation_inverse_works: assumes p: "permutation p"
  shows "inv p o p = id" "p o inv p = id"
  using permutation_bijective [OF p]
  unfolding bij_def inj_iff surj_iff by auto

lemma permutation_inverse_compose:
  assumes p: "permutation p" and q: "permutation q"
  shows "inv (p o q) = inv q o inv p"
proof-
  note ps = permutation_inverse_works[OF p]
  note qs = permutation_inverse_works[OF q]
  have "p o q o (inv q o inv p) = p o (q o inv q) o inv p" by (simp add: o_assoc)
  also have "\<dots> = id" by (simp add: ps qs)
  finally have th0: "p o q o (inv q o inv p) = id" .
  have "inv q o inv p o (p o q) = inv q o (inv p o p) o q" by (simp add: o_assoc)
  also have "\<dots> = id" by (simp add: ps qs)
  finally have th1: "inv q o inv p o (p o q) = id" .
  from inv_unique_comp[OF th0 th1] show ?thesis .
qed

(* ------------------------------------------------------------------------- *)
(* Relation to "permutes".                                                   *)
(* ------------------------------------------------------------------------- *)

lemma permutation_permutes: "permutation p \<longleftrightarrow> (\<exists>S. finite S \<and> p permutes S)"
unfolding permutation permutes_def bij_iff[symmetric]
apply (rule iffI, clarify)
apply (rule exI[where x="{x. p x \<noteq> x}"])
apply simp
apply clarsimp
apply (rule_tac B="S" in finite_subset)
apply auto
done

(* ------------------------------------------------------------------------- *)
(* Hence a sort of induction principle composing by swaps.                   *)
(* ------------------------------------------------------------------------- *)

lemma permutes_induct: "finite S \<Longrightarrow>  P id  \<Longrightarrow> (\<And> a b p. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> P p \<Longrightarrow> P p \<Longrightarrow> permutation p ==> P (Fun.swap a b id o p))
         ==> (\<And>p. p permutes S ==> P p)"
proof(induct S rule: finite_induct)
  case empty thus ?case by auto
next
  case (insert x F p)
  let ?r = "Fun.swap x (p x) id o p"
  let ?q = "Fun.swap x (p x) id o ?r"
  have qp: "?q = p" by (simp add: o_assoc)
  from permutes_insert_lemma[OF insert.prems(3)] insert have Pr: "P ?r" by blast
  from permutes_in_image[OF insert.prems(3), of x]
  have pxF: "p x \<in> insert x F" by simp
  have xF: "x \<in> insert x F" by simp
  have rp: "permutation ?r"
    unfolding permutation_permutes using insert.hyps(1)
      permutes_insert_lemma[OF insert.prems(3)] by blast
  from insert.prems(2)[OF xF pxF Pr Pr rp]
  show ?case  unfolding qp .
qed

(* ------------------------------------------------------------------------- *)
(* Sign of a permutation as a real number.                                   *)
(* ------------------------------------------------------------------------- *)

definition "sign p = (if evenperm p then (1::int) else -1)"

lemma sign_nz: "sign p \<noteq> 0" by (simp add: sign_def)
lemma sign_id: "sign id = 1" by (simp add: sign_def)
lemma sign_inverse: "permutation p ==> sign (inv p) = sign p"
  by (simp add: sign_def evenperm_inv)
lemma sign_compose: "permutation p \<Longrightarrow> permutation q ==> sign (p o q) = sign(p) * sign(q)" by (simp add: sign_def evenperm_comp)
lemma sign_swap_id: "sign (Fun.swap a b id) = (if a = b then 1 else -1)"
  by (simp add: sign_def evenperm_swap)
lemma sign_idempotent: "sign p * sign p = 1" by (simp add: sign_def)

(* ------------------------------------------------------------------------- *)
(* More lemmas about permutations.                                           *)
(* ------------------------------------------------------------------------- *)

lemma permutes_natset_le:
  assumes p: "p permutes (S::'a::wellorder set)" and le: "\<forall>i \<in> S.  p i <= i" shows "p = id"
proof-
  {fix n
    have "p n = n"
      using p le
    proof(induct n arbitrary: S rule: less_induct)
      fix n S assume H: "\<And>m S. \<lbrakk>m < n; p permutes S; \<forall>i\<in>S. p i \<le> i\<rbrakk> \<Longrightarrow> p m = m"
        "p permutes S" "\<forall>i \<in>S. p i \<le> i"
      {assume "n \<notin> S"
        with H(2) have "p n = n" unfolding permutes_def by metis}
      moreover
      {assume ns: "n \<in> S"
        from H(3)  ns have "p n < n \<or> p n = n" by auto
        moreover{assume h: "p n < n"
          from H h have "p (p n) = p n" by metis
          with permutes_inj[OF H(2)] have "p n = n" unfolding inj_on_def by blast
          with h have False by simp}
        ultimately have "p n = n" by blast }
      ultimately show "p n = n"  by blast
    qed}
  thus ?thesis by (auto simp add: fun_eq_iff)
qed

lemma permutes_natset_ge:
  assumes p: "p permutes (S::'a::wellorder set)" and le: "\<forall>i \<in> S.  p i \<ge> i" shows "p = id"
proof-
  {fix i assume i: "i \<in> S"
    from i permutes_in_image[OF permutes_inv[OF p]] have "inv p i \<in> S" by simp
    with le have "p (inv p i) \<ge> inv p i" by blast
    with permutes_inverses[OF p] have "i \<ge> inv p i" by simp}
  then have th: "\<forall>i\<in>S. inv p i \<le> i"  by blast
  from permutes_natset_le[OF permutes_inv[OF p] th]
  have "inv p = inv id" by simp
  then show ?thesis
    apply (subst permutes_inv_inv[OF p, symmetric])
    apply (rule inv_unique_comp)
    apply simp_all
    done
qed

lemma image_inverse_permutations: "{inv p |p. p permutes S} = {p. p permutes S}"
apply (rule set_eqI)
apply auto
  using permutes_inv_inv permutes_inv apply auto
  apply (rule_tac x="inv x" in exI)
  apply auto
  done

lemma image_compose_permutations_left:
  assumes q: "q permutes S" shows "{q o p | p. p permutes S} = {p . p permutes S}"
apply (rule set_eqI)
apply auto
apply (rule permutes_compose)
using q apply auto
apply (rule_tac x = "inv q o x" in exI)
by (simp add: o_assoc permutes_inv permutes_compose permutes_inv_o)

lemma image_compose_permutations_right:
  assumes q: "q permutes S"
  shows "{p o q | p. p permutes S} = {p . p permutes S}"
apply (rule set_eqI)
apply auto
apply (rule permutes_compose)
using q apply auto
apply (rule_tac x = "x o inv q" in exI)
by (simp add: o_assoc permutes_inv permutes_compose permutes_inv_o o_assoc[symmetric])

lemma permutes_in_seg: "p permutes {1 ..n} \<Longrightarrow> i \<in> {1..n} ==> 1 <= p i \<and> p i <= n"

apply (simp add: permutes_def)
apply metis
done

lemma setsum_permutations_inverse: "setsum f {p. p permutes S} = setsum (\<lambda>p. f(inv p)) {p. p permutes S}" (is "?lhs = ?rhs")
proof-
  let ?S = "{p . p permutes S}"
have th0: "inj_on inv ?S"
proof(auto simp add: inj_on_def)
  fix q r
  assume q: "q permutes S" and r: "r permutes S" and qr: "inv q = inv r"
  hence "inv (inv q) = inv (inv r)" by simp
  with permutes_inv_inv[OF q] permutes_inv_inv[OF r]
  show "q = r" by metis
qed
  have th1: "inv ` ?S = ?S" using image_inverse_permutations by blast
  have th2: "?rhs = setsum (f o inv) ?S" by (simp add: o_def)
  from setsum_reindex[OF th0, of f]  show ?thesis unfolding th1 th2 .
qed

lemma setum_permutations_compose_left:
  assumes q: "q permutes S"
  shows "setsum f {p. p permutes S} =
            setsum (\<lambda>p. f(q o p)) {p. p permutes S}" (is "?lhs = ?rhs")
proof-
  let ?S = "{p. p permutes S}"
  have th0: "?rhs = setsum (f o (op o q)) ?S" by (simp add: o_def)
  have th1: "inj_on (op o q) ?S"
    apply (auto simp add: inj_on_def)
  proof-
    fix p r
    assume "p permutes S" and r:"r permutes S" and rp: "q \<circ> p = q \<circ> r"
    hence "inv q o q o p = inv q o q o r" by (simp add: o_assoc[symmetric])
    with permutes_inj[OF q, unfolded inj_iff]

    show "p = r" by simp
  qed
  have th3: "(op o q) ` ?S = ?S" using image_compose_permutations_left[OF q] by auto
  from setsum_reindex[OF th1, of f]
  show ?thesis unfolding th0 th1 th3 .
qed

lemma sum_permutations_compose_right:
  assumes q: "q permutes S"
  shows "setsum f {p. p permutes S} =
            setsum (\<lambda>p. f(p o q)) {p. p permutes S}" (is "?lhs = ?rhs")
proof-
  let ?S = "{p. p permutes S}"
  have th0: "?rhs = setsum (f o (\<lambda>p. p o q)) ?S" by (simp add: o_def)
  have th1: "inj_on (\<lambda>p. p o q) ?S"
    apply (auto simp add: inj_on_def)
  proof-
    fix p r
    assume "p permutes S" and r:"r permutes S" and rp: "p o q = r o q"
    hence "p o (q o inv q)  = r o (q o inv q)" by (simp add: o_assoc)
    with permutes_surj[OF q, unfolded surj_iff]

    show "p = r" by simp
  qed
  have th3: "(\<lambda>p. p o q) ` ?S = ?S" using image_compose_permutations_right[OF q] by auto
  from setsum_reindex[OF th1, of f]
  show ?thesis unfolding th0 th1 th3 .
qed

(* ------------------------------------------------------------------------- *)
(* Sum over a set of permutations (could generalize to iteration).           *)
(* ------------------------------------------------------------------------- *)

lemma setsum_over_permutations_insert:
  assumes fS: "finite S" and aS: "a \<notin> S"
  shows "setsum f {p. p permutes (insert a S)} = setsum (\<lambda>b. setsum (\<lambda>q. f (Fun.swap a b id o q)) {p. p permutes S}) (insert a S)"
proof-
  have th0: "\<And>f a b. (\<lambda>(b,p). f (Fun.swap a b id o p)) = f o (\<lambda>(b,p). Fun.swap a b id o p)"
    by (simp add: fun_eq_iff)
  have th1: "\<And>P Q. P \<times> Q = {(a,b). a \<in> P \<and> b \<in> Q}" by blast
  have th2: "\<And>P Q. P \<Longrightarrow> (P \<Longrightarrow> Q) \<Longrightarrow> P \<and> Q" by blast
  show ?thesis
    unfolding permutes_insert
    unfolding setsum_cartesian_product
    unfolding  th1[symmetric]
    unfolding th0
  proof(rule setsum_reindex)
    let ?f = "(\<lambda>(b, y). Fun.swap a b id \<circ> y)"
    let ?P = "{p. p permutes S}"
    {fix b c p q assume b: "b \<in> insert a S" and c: "c \<in> insert a S"
      and p: "p permutes S" and q: "q permutes S"
      and eq: "Fun.swap a b id o p = Fun.swap a c id o q"
      from p q aS have pa: "p a = a" and qa: "q a = a"
        unfolding permutes_def by metis+
      from eq have "(Fun.swap a b id o p) a  = (Fun.swap a c id o q) a" by simp
      hence bc: "b = c"
        by (simp add: permutes_def pa qa o_def fun_upd_def swap_def id_def cong del: if_weak_cong split: split_if_asm)
      from eq[unfolded bc] have "(\<lambda>p. Fun.swap a c id o p) (Fun.swap a c id o p) = (\<lambda>p. Fun.swap a c id o p) (Fun.swap a c id o q)" by simp
      hence "p = q" unfolding o_assoc swap_id_idempotent
        by (simp add: o_def)
      with bc have "b = c \<and> p = q" by blast
    }

    then show "inj_on ?f (insert a S \<times> ?P)"
      unfolding inj_on_def
      apply clarify by metis
  qed
qed

end
