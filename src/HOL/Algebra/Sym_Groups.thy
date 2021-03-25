(*  Title:      HOL/Algebra/Sym_Groups.thy
    Author:     Paulo Emílio de Vilhena
*)

theory Sym_Groups
  imports
    "HOL-Combinatorics.Cycles"
    Solvable_Groups
begin

section \<open>Symmetric Groups\<close>

subsection \<open>Definitions\<close>

abbreviation inv' :: "('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)"
  where "inv' f \<equiv> Hilbert_Choice.inv f"
  
definition sym_group :: "nat \<Rightarrow> (nat \<Rightarrow> nat) monoid"
  where "sym_group n = \<lparr> carrier = { p. p permutes {1..n} }, mult = (\<circ>), one = id \<rparr>"

definition alt_group :: "nat \<Rightarrow> (nat \<Rightarrow> nat) monoid"
  where "alt_group n = (sym_group n) \<lparr> carrier := { p. p permutes {1..n} \<and> evenperm p } \<rparr>"

definition sign_img :: "int monoid"
  where "sign_img = \<lparr> carrier = { -1, 1 }, mult = (*), one = 1 \<rparr>"


subsection \<open>Basic Properties\<close>

lemma sym_group_carrier: "p \<in> carrier (sym_group n) \<longleftrightarrow> p permutes {1..n}"
  unfolding sym_group_def by simp

lemma sym_group_mult: "mult (sym_group n) = (\<circ>)"
  unfolding sym_group_def by simp

lemma sym_group_one: "one (sym_group n) = id"
  unfolding sym_group_def by simp

lemma sym_group_carrier': "p \<in> carrier (sym_group n) \<Longrightarrow> permutation p"
  unfolding sym_group_carrier permutation_permutes by auto

lemma alt_group_carrier: "p \<in> carrier (alt_group n) \<longleftrightarrow> p permutes {1..n} \<and> evenperm p"
  unfolding alt_group_def by auto

lemma alt_group_mult: "mult (alt_group n) = (\<circ>)"
  unfolding alt_group_def using sym_group_mult by simp

lemma alt_group_one: "one (alt_group n) = id"
  unfolding alt_group_def using sym_group_one by simp

lemma alt_group_carrier': "p \<in> carrier (alt_group n) \<Longrightarrow> permutation p"
  unfolding alt_group_carrier permutation_permutes by auto

lemma sym_group_is_group: "group (sym_group n)"
  using permutes_inv permutes_inv_o(2)
  by (auto intro!: groupI
         simp add: sym_group_def permutes_compose
                   permutes_id comp_assoc, blast)

lemma sign_img_is_group: "group sign_img"
  unfolding sign_img_def by (unfold_locales, auto simp add: Units_def)

lemma sym_group_inv_closed:
  assumes "p \<in> carrier (sym_group n)" shows "inv' p \<in> carrier (sym_group n)"
  using assms permutes_inv sym_group_def by auto

lemma alt_group_inv_closed:
  assumes "p \<in> carrier (alt_group n)" shows "inv' p \<in> carrier (alt_group n)"
  using evenperm_inv[OF alt_group_carrier'] permutes_inv assms alt_group_carrier by auto

lemma sym_group_inv_equality [simp]:
  assumes "p \<in> carrier (sym_group n)" shows "inv\<^bsub>(sym_group n)\<^esub> p = inv' p"
proof -
  have "inv' p \<circ> p = id"
    using assms permutes_inv_o(2) sym_group_def by auto
  hence "(inv' p) \<otimes>\<^bsub>(sym_group n)\<^esub> p = one (sym_group n)"
    by (simp add: sym_group_def)
  thus ?thesis  using group.inv_equality[OF sym_group_is_group]
    by (simp add: assms sym_group_inv_closed)
qed

lemma sign_is_hom: "sign \<in> hom (sym_group n) sign_img"
  unfolding hom_def sign_img_def sym_group_mult using sym_group_carrier'[of _ n]
  by (auto simp add: sign_compose, meson sign_def)

lemma sign_group_hom: "group_hom (sym_group n) sign_img sign"
  using group_hom.intro[OF sym_group_is_group sign_img_is_group] sign_is_hom
  by (simp add: group_hom_axioms_def)

lemma sign_is_surj:
  assumes "n \<ge> 2" shows "sign ` (carrier (sym_group n)) = carrier sign_img"
proof -
  have "swapidseq (Suc 0) (Fun.swap (1 :: nat) 2 id)"
    using comp_Suc[OF id, of "1 :: nat" "2"] by auto
  hence "sign (Fun.swap (1 :: nat) 2 id) = (-1 :: int)"
    by (simp add: sign_swap_id)
  moreover have "Fun.swap (1 :: nat) 2 id \<in> carrier (sym_group n)" and "id \<in> carrier (sym_group n)"
    using assms permutes_swap_id[of "1 :: nat" "{1..n}" 2] permutes_id
    unfolding sym_group_carrier by auto
  ultimately have "carrier sign_img \<subseteq> sign ` (carrier (sym_group n))"
    using sign_id mk_disjoint_insert unfolding sign_img_def by fastforce
  moreover have "sign ` (carrier (sym_group n)) \<subseteq> carrier sign_img"
    using sign_is_hom unfolding hom_def by auto
  ultimately show ?thesis
    by blast
qed 

lemma alt_group_is_sign_kernel:
  "carrier (alt_group n) = kernel (sym_group n) sign_img sign"
  unfolding alt_group_def sym_group_def sign_img_def kernel_def sign_def by auto

lemma alt_group_is_subgroup: "subgroup (carrier (alt_group n)) (sym_group n)"
  using group_hom.subgroup_kernel[OF sign_group_hom]
  unfolding alt_group_is_sign_kernel by blast

lemma alt_group_is_group: "group (alt_group n)"
  using group.subgroup_imp_group[OF sym_group_is_group alt_group_is_subgroup]
  by (simp add: alt_group_def)

lemma sign_iso:
  assumes "n \<ge> 2" shows "(sym_group n) Mod (carrier (alt_group n)) \<cong> sign_img"
  using group_hom.FactGroup_iso[OF sign_group_hom sign_is_surj[OF assms]]
  unfolding alt_group_is_sign_kernel .

lemma alt_group_inv_equality:
  assumes "p \<in> carrier (alt_group n)" shows "inv\<^bsub>(alt_group n)\<^esub> p = inv' p"
proof -
  have "inv' p \<circ> p = id"
    using assms permutes_inv_o(2) alt_group_def by auto
  hence "(inv' p) \<otimes>\<^bsub>(alt_group n)\<^esub> p = one (alt_group n)"
    by (simp add: alt_group_def sym_group_def)
  thus ?thesis  using group.inv_equality[OF alt_group_is_group]
    by (simp add: assms alt_group_inv_closed)
qed

lemma sym_group_card_carrier: "card (carrier (sym_group n)) = fact n"
  using card_permutations[of "{1..n}" n] unfolding sym_group_def by simp

lemma alt_group_card_carrier:
  assumes "n \<ge> 2" shows "2 * card (carrier (alt_group n)) = fact n"
proof -
  have "card (rcosets\<^bsub>sym_group n\<^esub> (carrier (alt_group n))) = 2"
    using iso_same_card[OF sign_iso[OF assms]] unfolding FactGroup_def sign_img_def by auto
  thus ?thesis
    using group.lagrange[OF sym_group_is_group alt_group_is_subgroup, of n]
    unfolding order_def sym_group_card_carrier by simp
qed


subsection \<open>Transposition Sequences\<close>

text \<open>In order to prove that the Alternating Group can be generated by 3-cycles, we need
      a stronger decomposition of permutations as transposition sequences than the one 
      proposed at Permutations.thy. \<close>

inductive swapidseq_ext :: "'a set \<Rightarrow> nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
  where
    empty:  "swapidseq_ext {} 0 id"
  | single: "\<lbrakk> swapidseq_ext S n p; a \<notin> S \<rbrakk> \<Longrightarrow> swapidseq_ext (insert a S) n p"
  | comp:   "\<lbrakk> swapidseq_ext S n p; a \<noteq> b \<rbrakk> \<Longrightarrow>
               swapidseq_ext (insert a (insert b S)) (Suc n) ((Fun.swap a b id) \<circ> p)"


lemma swapidseq_ext_finite:
  assumes "swapidseq_ext S n p" shows "finite S"
  using assms by (induction) (auto)

lemma swapidseq_ext_zero:
  assumes "finite S" shows "swapidseq_ext S 0 id"
  using assms empty by (induct set: "finite", fastforce, simp add: single)

lemma swapidseq_ext_imp_swapidseq:
  \<open>swapidseq n p\<close> if \<open>swapidseq_ext S n p\<close>
using that proof induction
  case empty
  then show ?case
    by (simp add: fun_eq_iff)
next
  case (single S n p a)
  then show ?case by simp
next
  case (comp S n p a b)
  then have \<open>swapidseq (Suc n) (Fun.swap a b id \<circ> p)\<close>
    by (simp add: comp_Suc)
  then show ?case by (simp add: comp_def)
qed

lemma swapidseq_ext_zero_imp_id:
  assumes "swapidseq_ext S 0 p" shows "p = id"
proof -
  have "\<lbrakk> swapidseq_ext S n p; n = 0 \<rbrakk> \<Longrightarrow> p = id" for n
    by (induction rule: swapidseq_ext.induct, auto)
  thus ?thesis
    using assms by simp
qed

lemma swapidseq_ext_finite_expansion:
  assumes "finite B" and "swapidseq_ext A n p" shows "swapidseq_ext (A \<union> B) n p"
  using assms
proof (induct set: "finite", simp)
  case (insert b B) show ?case
    using insert single[OF insert(3), of b] by (metis Un_insert_right insert_absorb)
qed

lemma swapidseq_ext_backwards:
  assumes "swapidseq_ext A (Suc n) p"
  shows "\<exists>a b A' p'. a \<noteq> b \<and> A = (insert a (insert b A')) \<and>
                     swapidseq_ext A' n p' \<and> p = (Fun.swap a b id) \<circ> p'"
proof -
  { fix A n k and p :: "'a \<Rightarrow> 'a"
    assume "swapidseq_ext A n p" "n = Suc k"
    hence "\<exists>a b A' p'. a \<noteq> b \<and> A = (insert a (insert b A')) \<and>
                       swapidseq_ext A' k p' \<and> p = (Fun.swap a b id) \<circ> p'"
    proof (induction, simp)
      case single thus ?case
        by (metis Un_insert_right insert_iff insert_is_Un swapidseq_ext.single)
    next
      case comp thus ?case
        by blast 
    qed }
  thus ?thesis
    using assms by simp
qed

lemma swapidseq_ext_backwards':
  assumes "swapidseq_ext A (Suc n) p"
  shows "\<exists>a b A' p'. a \<in> A \<and> b \<in> A \<and> a \<noteq> b \<and> swapidseq_ext A n p' \<and> p = (Fun.swap a b id) \<circ> p'"
  using swapidseq_ext_backwards[OF assms] swapidseq_ext_finite_expansion
  by (metis Un_insert_left assms insertI1 sup.idem sup_commute swapidseq_ext_finite)

lemma swapidseq_ext_endswap:
  assumes "swapidseq_ext S n p" "a \<noteq> b"
  shows "swapidseq_ext (insert a (insert b S)) (Suc n) (p \<circ> (Fun.swap a b id))"
  using assms
proof (induction n arbitrary: S p a b)
  case 0 hence "p = id"
    using swapidseq_ext_zero_imp_id by blast
  thus ?case
    using 0 by (metis comp_id id_comp swapidseq_ext.comp) 
next
  case (Suc n)
  then obtain c d S' and p' :: "'a \<Rightarrow> 'a"
    where cd: "c \<noteq> d" and S: "S = (insert c (insert d S'))" "swapidseq_ext S' n p'"
      and p: "p = (Fun.swap c d id) \<circ> p'"
    using swapidseq_ext_backwards[OF Suc(2)] by blast
  hence "swapidseq_ext (insert a (insert b S')) (Suc n) (p' \<circ> (Fun.swap a b id))"
    by (simp add: Suc.IH Suc.prems(2))
  hence "swapidseq_ext (insert c (insert d (insert a (insert b S')))) (Suc (Suc n))
                 ((Fun.swap c d id) \<circ> p' \<circ> (Fun.swap a b id))"
    by (metis cd fun.map_comp swapidseq_ext.comp)
  thus ?case
    by (metis S(1) p insert_commute) 
qed

lemma swapidseq_ext_extension:
  assumes "swapidseq_ext A n p" and "swapidseq_ext B m q" and "A \<inter> B = {}"
  shows "swapidseq_ext (A \<union> B) (n + m) (p \<circ> q)"
  using assms(1,3)
proof (induction, simp add: assms(2))
  case single show ?case
    using swapidseq_ext.single[OF single(3)] single(2,4) by auto
next
  case comp show ?case
    using swapidseq_ext.comp[OF comp(3,2)] comp(4)
    by (metis Un_insert_left add_Suc insert_disjoint(1) o_assoc)
qed

lemma swapidseq_ext_of_cycles:
  assumes "cycle cs" shows "swapidseq_ext (set cs) (length cs - 1) (cycle_of_list cs)"
  using assms
proof (induct cs rule: cycle_of_list.induct)
  case (1 i j cs) show ?case
    using comp[OF 1(1), of i j] 1(2) by (simp add: o_def)  
next
  case "2_1" show ?case
    by (simp, metis eq_id_iff empty)
next
  case ("2_2" v) show ?case
    using single[OF empty, of v] by (simp, metis eq_id_iff)
qed

lemma cycle_decomp_imp_swapidseq_ext:
  assumes "cycle_decomp S p" shows "\<exists>n. swapidseq_ext S n p"
  using assms
proof (induction)
  case empty show ?case
    using swapidseq_ext.empty by blast
next
  case (comp I p cs)
  then obtain m where m: "swapidseq_ext I m p" by blast
  hence "swapidseq_ext (set cs) (length cs - 1) (cycle_of_list cs)"
    using comp.hyps(2) swapidseq_ext_of_cycles by blast
  thus ?case using swapidseq_ext_extension m
    using comp.hyps(3) by blast
qed

lemma swapidseq_ext_of_permutation:
  assumes "p permutes S" and "finite S" shows "\<exists>n. swapidseq_ext S n p"
  using cycle_decomp_imp_swapidseq_ext[OF cycle_decomposition[OF assms]] .

lemma split_swapidseq_ext:
  assumes "k \<le> n" and "swapidseq_ext S n p"
  obtains q r U V where "swapidseq_ext U (n - k) q" and "swapidseq_ext V k r" and "p = q \<circ> r" and "U \<union> V = S"
proof -
  from assms
  have "\<exists>q r U V. swapidseq_ext U (n - k) q \<and> swapidseq_ext V k r \<and> p = q \<circ> r \<and> U \<union> V = S"
   (is "\<exists>q r U V. ?split k q r U V")
  proof (induct k rule: inc_induct)
    case base thus ?case
      by (metis diff_self_eq_0 id_o sup_bot.left_neutral empty)
  next
    case (step m)
    then obtain q r U V
      where q: "swapidseq_ext U (n - Suc m) q" and r: "swapidseq_ext V (Suc m) r"
        and p: "p = q \<circ> r" and S: "U \<union> V = S"
      by blast
    obtain a b r' V' 
      where "a \<noteq> b" and r': "V = (insert a (insert b V'))" "swapidseq_ext V' m r'" "r = (Fun.swap a b id) \<circ> r'"
      using swapidseq_ext_backwards[OF r] by blast
    have "swapidseq_ext (insert a (insert b U)) (n - m) (q \<circ> (Fun.swap a b id))"
      using swapidseq_ext_endswap[OF q \<open>a \<noteq> b\<close>] step(2) by (metis Suc_diff_Suc)
    hence "?split m (q \<circ> (Fun.swap a b id)) r' (insert a (insert b U)) V'"
      using r' S unfolding p by fastforce 
    thus ?case by blast
  qed
  thus ?thesis
    using that by blast
qed


subsection \<open>Unsolvability of Symmetric Groups\<close>

text \<open>We show that symmetric groups (\<^term>\<open>sym_group n\<close>) are unsolvable for \<^term>\<open>n \<ge> 5\<close>.\<close>

abbreviation three_cycles :: "nat \<Rightarrow> (nat \<Rightarrow> nat) set"
  where "three_cycles n \<equiv>
           { cycle_of_list cs | cs. cycle cs \<and> length cs = 3 \<and> set cs \<subseteq> {1..n} }"


lemma stupid_lemma:
  assumes "length cs = 3" shows "cs = [ (cs ! 0), (cs ! 1), (cs ! 2) ]"
  using assms by (auto intro!: nth_equalityI)
    (metis Suc_lessI less_2_cases not_less_eq nth_Cons_0
           nth_Cons_Suc numeral_2_eq_2 numeral_3_eq_3)

lemma three_cycles_incl: "three_cycles n \<subseteq> carrier (alt_group n)"
proof
  fix p assume "p \<in> three_cycles n"
  then obtain cs where cs: "p = cycle_of_list cs" "cycle cs" "length cs = 3" "set cs \<subseteq> {1..n}"
    by auto
  obtain a b c where cs_def: "cs = [ a, b, c ]"
    using stupid_lemma[OF cs(3)] by auto
  have "swapidseq (Suc (Suc 0)) ((Fun.swap a b id) \<circ> (Fun.swap b c id))"
    using comp_Suc[OF comp_Suc[OF id], of b c a b] cs(2) unfolding cs_def by simp
  hence "evenperm p"
    using cs(1) unfolding cs_def by (simp add: evenperm_unique)
  thus "p \<in> carrier (alt_group n)"
    using permutes_subset[OF cycle_permutes cs(4)]
    unfolding alt_group_carrier cs(1) by simp
qed

lemma alt_group_carrier_as_three_cycles:
  "carrier (alt_group n) = generate (alt_group n) (three_cycles n)"
proof -
  interpret A: group "alt_group n"
    using alt_group_is_group by simp

  show ?thesis
  proof
    show "generate (alt_group n) (three_cycles n) \<subseteq> carrier (alt_group n)"
      using A.generate_subgroup_incl[OF three_cycles_incl A.subgroup_self] .
  next
    show "carrier (alt_group n) \<subseteq> generate (alt_group n) (three_cycles n)"
    proof
      { fix q :: "nat \<Rightarrow> nat" and a b c
        assume "a \<noteq> b" "b \<noteq> c" "{ a, b, c } \<subseteq> {1..n}" 
        have "cycle_of_list [a, b, c] \<in> generate (alt_group n) (three_cycles n)"
        proof (cases)
          assume "c = a"
          hence "cycle_of_list [ a, b, c ] = id"
            by (simp add: swap_commute)
          thus "cycle_of_list [ a, b, c ] \<in> generate (alt_group n) (three_cycles n)"
            using one[of "alt_group n"] unfolding alt_group_one by simp
        next
          assume "c \<noteq> a"
          have "distinct [a, b, c]"
            using \<open>a \<noteq> b\<close> and \<open>b \<noteq> c\<close> and \<open>c \<noteq> a\<close> by auto
          with \<open>{ a, b, c } \<subseteq> {1..n}\<close>
          show "cycle_of_list [ a, b, c ] \<in> generate (alt_group n) (three_cycles n)"
            by (intro incl, fastforce)
        qed } note aux_lemma1 = this
    
      { fix S :: "nat set" and q :: "nat \<Rightarrow> nat"
        assume seq: "swapidseq_ext S (Suc (Suc 0)) q" and S: "S \<subseteq> {1..n}"
        have "q \<in> generate (alt_group n) (three_cycles n)"
        proof -
          obtain a b q' where ab: "a \<noteq> b" "a \<in> S" "b \<in> S"
            and q': "swapidseq_ext S (Suc 0) q'" "q = (Fun.swap a b id) \<circ> q'"
            using swapidseq_ext_backwards'[OF seq] by auto 
          obtain c d where cd: "c \<noteq> d" "c \<in> S" "d \<in> S"
            and q: "q = (Fun.swap a b id) \<circ> (Fun.swap c d id)"
            using swapidseq_ext_backwards'[OF q'(1)]
                  swapidseq_ext_zero_imp_id
            unfolding q'(2)
            by fastforce

          consider (eq) "b = c" | (ineq) "b \<noteq> c" by auto
          thus ?thesis
          proof cases
            case eq then have "q = cycle_of_list [ a, b, d ]"
              unfolding q by simp
            moreover have "{ a, b, d } \<subseteq> {1..n}"
              using ab cd S by blast
            ultimately show ?thesis
              using aux_lemma1[OF ab(1)] cd(1) eq by simp
          next
            case ineq
            hence "q = cycle_of_list [ a, b, c ] \<circ> cycle_of_list [ b, c, d ]"
              unfolding q by (simp add: comp_swap)
            moreover have "{ a, b, c } \<subseteq> {1..n}" and "{ b, c, d } \<subseteq> {1..n}"
              using ab cd S by blast+
            ultimately show ?thesis
              using eng[OF aux_lemma1[OF ab(1) ineq] aux_lemma1[OF ineq cd(1)]]
              unfolding alt_group_mult by simp
          qed
        qed } note aux_lemma2 = this
      
      fix p assume "p \<in> carrier (alt_group n)" then have p: "p permutes {1..n}" "evenperm p"
        unfolding alt_group_carrier by auto
      obtain m where m: "swapidseq_ext {1..n} m p"
        using swapidseq_ext_of_permutation[OF p(1)] by auto
      have "even m"
        using swapidseq_ext_imp_swapidseq[OF m] p(2) evenperm_unique by blast
      then obtain k where k: "m = 2 * k"
        by auto
      show "p \<in> generate (alt_group n) (three_cycles n)"
        using m unfolding k
      proof (induct k arbitrary: p)
        case 0 then have "p = id"
          using swapidseq_ext_zero_imp_id by simp
        show ?case
          using generate.one[of "alt_group n" "three_cycles n"]
          unfolding alt_group_one \<open>p = id\<close> .
      next
        case (Suc m)
        have arith: "2 * (Suc m) - (Suc (Suc 0)) = 2 * m" and "Suc (Suc 0) \<le> 2 * Suc m"
          by auto
        then obtain q r U V
          where q: "swapidseq_ext U (2 * m) q" and r: "swapidseq_ext V (Suc (Suc 0)) r"
            and p: "p = q \<circ> r" and UV: "U \<union> V = {1..n}"
          using split_swapidseq_ext[OF _ Suc(2), of "Suc (Suc 0)"] unfolding arith by metis
        have "swapidseq_ext {1..n} (2 * m) q"
          using UV q swapidseq_ext_finite_expansion[OF swapidseq_ext_finite[OF r] q] by simp
        thus ?case
          using eng[OF Suc(1) aux_lemma2[OF r], of q] UV unfolding alt_group_mult p by blast
      qed
    qed
  qed
qed

theorem derived_alt_group_const:
  assumes "n \<ge> 5" shows "derived (alt_group n) (carrier (alt_group n)) = carrier (alt_group n)"
proof
  show "derived (alt_group n) (carrier (alt_group n)) \<subseteq> carrier (alt_group n)"
    using group.derived_in_carrier[OF alt_group_is_group] by simp
next
  { fix p assume "p \<in> three_cycles n" have "p \<in> derived (alt_group n) (carrier (alt_group n))"
    proof -
      obtain cs where cs: "p = cycle_of_list cs" "cycle cs" "length cs = 3" "set cs \<subseteq> {1..n}"
        using \<open>p \<in> three_cycles n\<close> by auto
      then obtain a b c where cs_def: "cs = [ a, b, c ]"
        using stupid_lemma[OF cs(3)] by blast
      have "card (set cs) = 3"
        using cs(2-3)
        by (simp add: distinct_card)

      have "set cs \<noteq> {1..n}"
        using assms cs(3) unfolding sym[OF distinct_card[OF cs(2)]] by auto
      then obtain d where d: "d \<notin> set cs" "d \<in> {1..n}"
        using cs(4) by blast

      hence "cycle (d # cs)" and "length (d # cs) = 4" and "card {1..n} = n"
        using cs(2-3) by auto 
      hence "set (d # cs) \<noteq> {1..n}"
        using assms unfolding sym[OF distinct_card[OF \<open>cycle (d # cs)\<close>]]
        by (metis Suc_n_not_le_n eval_nat_numeral(3)) 
      then obtain e where e: "e \<notin> set (d # cs)" "e \<in> {1..n}"
        using d cs(4) by (metis insert_subset list.simps(15) subsetI subset_antisym) 

      define q where "q = (Fun.swap d e id) \<circ> (Fun.swap b c id)"
      hence "bij q"
        by (simp add: bij_comp)
      moreover have "q b = c" and "q c = b"
        using d(1) e(1) unfolding q_def cs_def by simp+
      moreover have "q a = a"
        using d(1) e(1) cs(2) unfolding q_def cs_def by auto
      ultimately have "q \<circ> p \<circ> (inv' q) = cycle_of_list [ a, c, b ]"
        using conjugation_of_cycle[OF cs(2), of q]
        unfolding sym[OF cs(1)] unfolding cs_def by simp
      also have " ... = p \<circ> p"
        using cs(2) unfolding cs(1) cs_def
        by (auto, metis comp_id comp_swap swap_commute swap_triple)
      finally have "q \<circ> p \<circ> (inv' q) = p \<circ> p" .
      moreover have "bij p"
        unfolding cs(1) cs_def by (simp add: bij_comp)
      ultimately have p: "q \<circ> p \<circ> (inv' q) \<circ> (inv' p) = p"
        by (simp add: bijection.intro bijection.inv_comp_right comp_assoc)

      have "swapidseq (Suc (Suc 0)) q"
        using comp_Suc[OF comp_Suc[OF id], of b c d e] e(1) cs(2)  unfolding q_def cs_def by auto
      hence "evenperm q"
        using even_Suc_Suc_iff evenperm_unique by blast
      moreover have "q permutes { d, e, b, c }"
        unfolding q_def by (simp add: permutes_compose permutes_swap_id)
      hence "q permutes {1..n}"
        using cs(4) d(2) e(2) permutes_subset unfolding cs_def by fastforce
      ultimately have "q \<in> carrier (alt_group n)"
        unfolding alt_group_carrier by simp
      moreover have "p \<in> carrier (alt_group n)"
        using \<open>p \<in> three_cycles n\<close> three_cycles_incl by blast
      ultimately have "p \<in> derived_set (alt_group n) (carrier (alt_group n))"
        using p alt_group_inv_equality unfolding alt_group_mult
        by (metis (no_types, lifting) UN_iff singletonI)
      thus "p \<in> derived (alt_group n) (carrier (alt_group n))"
        unfolding derived_def by (rule incl)
    qed } note aux_lemma = this

  interpret A: group "alt_group n"
    using alt_group_is_group .

  have "generate (alt_group n) (three_cycles n) \<subseteq> derived (alt_group n) (carrier (alt_group n))"
    using A.generate_subgroup_incl[OF _ A.derived_is_subgroup] aux_lemma by (meson subsetI) 
  thus "carrier (alt_group n) \<subseteq> derived (alt_group n) (carrier (alt_group n))"
    using alt_group_carrier_as_three_cycles by simp
qed

corollary alt_group_is_unsolvable:
  assumes "n \<ge> 5" shows "\<not> solvable (alt_group n)"
proof (rule ccontr)
  assume "\<not> \<not> solvable (alt_group n)"
  then obtain m where "(derived (alt_group n) ^^ m) (carrier (alt_group n)) = { id }"
    using group.solvable_iff_trivial_derived_seq[OF alt_group_is_group] unfolding alt_group_one by blast
  moreover have "(derived (alt_group n) ^^ m) (carrier (alt_group n)) = carrier (alt_group n)"
    using derived_alt_group_const[OF assms] by (induct m) (auto)
  ultimately have card_eq_1: "card (carrier (alt_group n)) = 1"
    by simp
  have ge_2: "n \<ge> 2"
    using assms by simp
  moreover have "2 = fact n"
    using alt_group_card_carrier[OF ge_2] unfolding card_eq_1
    by (metis fact_2 mult.right_neutral of_nat_fact)
  ultimately have "n = 2"
      by (metis antisym_conv fact_ge_self)
  thus False
    using assms by simp
qed

corollary sym_group_is_unsolvable:
  assumes "n \<ge> 5" shows "\<not> solvable (sym_group n)"
proof -
  interpret Id: group_hom "alt_group n" "sym_group n" id
    using group.canonical_inj_is_hom[OF sym_group_is_group alt_group_is_subgroup] alt_group_def by simp
  show ?thesis
    using Id.inj_hom_imp_solvable alt_group_is_unsolvable[OF assms] by auto
qed

end