theory Ordered_Euclidean_Space
imports
  Topology_Euclidean_Space
  "~~/src/HOL/Library/Product_Order"
begin

subsection {* An ordering on euclidean spaces that will allow us to talk about intervals *}

class ordered_euclidean_space = ord + inf + sup + abs + Inf + Sup + euclidean_space +
  assumes eucl_le: "x \<le> y \<longleftrightarrow> (\<forall>i\<in>Basis. x \<bullet> i \<le> y \<bullet> i)"
  assumes eucl_less_le_not_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
  assumes eucl_inf: "inf x y = (\<Sum>i\<in>Basis. inf (x \<bullet> i) (y \<bullet> i) *\<^sub>R i)"
  assumes eucl_sup: "sup x y = (\<Sum>i\<in>Basis. sup (x \<bullet> i) (y \<bullet> i) *\<^sub>R i)"
  assumes eucl_Inf: "Inf X = (\<Sum>i\<in>Basis. (INF x:X. x \<bullet> i) *\<^sub>R i)"
  assumes eucl_Sup: "Sup X = (\<Sum>i\<in>Basis. (SUP x:X. x \<bullet> i) *\<^sub>R i)"
  assumes eucl_abs: "abs x = (\<Sum>i\<in>Basis. abs (x \<bullet> i) *\<^sub>R i)"
begin

subclass order
  by default
    (auto simp: eucl_le eucl_less_le_not_le intro!: euclidean_eqI antisym intro: order.trans)

subclass ordered_ab_group_add_abs
  by default (auto simp: eucl_le inner_add_left eucl_abs abs_leI)

subclass ordered_real_vector
  by default (auto simp: eucl_le intro!: mult_left_mono mult_right_mono)

subclass lattice
  by default (auto simp: eucl_inf eucl_sup eucl_le)

subclass distrib_lattice
  by default (auto simp: eucl_inf eucl_sup sup_inf_distrib1 intro!: euclidean_eqI)

subclass conditionally_complete_lattice
proof
  fix z::'a and X::"'a set"
  assume "X \<noteq> {}"
  hence "\<And>i. (\<lambda>x. x \<bullet> i) ` X \<noteq> {}" by simp
  thus "(\<And>x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> z \<le> Inf X" "(\<And>x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> Sup X \<le> z"
    by (auto simp: eucl_Inf eucl_Sup eucl_le Inf_class.INF_def Sup_class.SUP_def
      simp del: Inf_class.Inf_image_eq Sup_class.Sup_image_eq
      intro!: cInf_greatest cSup_least)
qed (force intro!: cInf_lower cSup_upper
      simp: bdd_below_def bdd_above_def preorder_class.bdd_below_def preorder_class.bdd_above_def
        eucl_Inf eucl_Sup eucl_le Inf_class.INF_def Sup_class.SUP_def
      simp del: Inf_class.Inf_image_eq Sup_class.Sup_image_eq)+

lemma inner_Basis_inf_left: "i \<in> Basis \<Longrightarrow> inf x y \<bullet> i = inf (x \<bullet> i) (y \<bullet> i)"
  and inner_Basis_sup_left: "i \<in> Basis \<Longrightarrow> sup x y \<bullet> i = sup (x \<bullet> i) (y \<bullet> i)"
  by (simp_all add: eucl_inf eucl_sup inner_setsum_left inner_Basis if_distrib setsum_delta
      cong: if_cong)

lemma inner_Basis_INF_left: "i \<in> Basis \<Longrightarrow> (INF x:X. f x) \<bullet> i = (INF x:X. f x \<bullet> i)"
  and inner_Basis_SUP_left: "i \<in> Basis \<Longrightarrow> (SUP x:X. f x) \<bullet> i = (SUP x:X. f x \<bullet> i)"
  using eucl_Sup [of "f ` X"] eucl_Inf [of "f ` X"] by (simp_all add: comp_def)

lemma abs_inner: "i \<in> Basis \<Longrightarrow> abs x \<bullet> i = abs (x \<bullet> i)"
  by (auto simp: eucl_abs)

lemma
  abs_scaleR: "\<bar>a *\<^sub>R b\<bar> = \<bar>a\<bar> *\<^sub>R \<bar>b\<bar>"
  by (auto simp: eucl_abs abs_mult intro!: euclidean_eqI)

lemma interval_inner_leI:
  assumes "x \<in> {a .. b}" "0 \<le> i"
  shows "a\<bullet>i \<le> x\<bullet>i" "x\<bullet>i \<le> b\<bullet>i"
  using assms
  unfolding euclidean_inner[of a i] euclidean_inner[of x i] euclidean_inner[of b i]
  by (auto intro!: setsum_mono mult_right_mono simp: eucl_le)

lemma inner_nonneg_nonneg:
  shows "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow> 0 \<le> a \<bullet> b"
  using interval_inner_leI[of a 0 a b]
  by auto

lemma inner_Basis_mono:
  shows "a \<le> b \<Longrightarrow> c \<in> Basis  \<Longrightarrow> a \<bullet> c \<le> b \<bullet> c"
  by (simp add: eucl_le)

lemma Basis_nonneg[intro, simp]: "i \<in> Basis \<Longrightarrow> 0 \<le> i"
  by (auto simp: eucl_le inner_Basis)

lemma Sup_eq_maximum_componentwise:
  fixes s::"'a set"
  assumes i: "\<And>b. b \<in> Basis \<Longrightarrow> X \<bullet> b = i b \<bullet> b"
  assumes sup: "\<And>b x. b \<in> Basis \<Longrightarrow> x \<in> s \<Longrightarrow> x \<bullet> b \<le> X \<bullet> b"
  assumes i_s: "\<And>b. b \<in> Basis \<Longrightarrow> (i b \<bullet> b) \<in> (\<lambda>x. x \<bullet> b) ` s"
  shows "Sup s = X"
  using assms
  unfolding eucl_Sup euclidean_representation_setsum
  by (auto simp: Sup_class.SUP_def simp del: Sup_class.Sup_image_eq intro!: conditionally_complete_lattice_class.cSup_eq_maximum)

lemma Inf_eq_minimum_componentwise:
  assumes i: "\<And>b. b \<in> Basis \<Longrightarrow> X \<bullet> b = i b \<bullet> b"
  assumes sup: "\<And>b x. b \<in> Basis \<Longrightarrow> x \<in> s \<Longrightarrow> X \<bullet> b \<le> x \<bullet> b"
  assumes i_s: "\<And>b. b \<in> Basis \<Longrightarrow> (i b \<bullet> b) \<in> (\<lambda>x. x \<bullet> b) ` s"
  shows "Inf s = X"
  using assms
  unfolding eucl_Inf euclidean_representation_setsum
  by (auto simp: Inf_class.INF_def simp del: Inf_class.Inf_image_eq intro!: conditionally_complete_lattice_class.cInf_eq_minimum)

end

lemma
  compact_attains_Inf_componentwise:
  fixes b::"'a::ordered_euclidean_space"
  assumes "b \<in> Basis" assumes "X \<noteq> {}" "compact X"
  obtains x where "x \<in> X" "x \<bullet> b = Inf X \<bullet> b" "\<And>y. y \<in> X \<Longrightarrow> x \<bullet> b \<le> y \<bullet> b"
proof atomize_elim
  let ?proj = "(\<lambda>x. x \<bullet> b) ` X"
  from assms have "compact ?proj" "?proj \<noteq> {}"
    by (auto intro!: compact_continuous_image continuous_on_intros)
  from compact_attains_inf[OF this]
  obtain s x
    where s: "s\<in>(\<lambda>x. x \<bullet> b) ` X" "\<And>t. t\<in>(\<lambda>x. x \<bullet> b) ` X \<Longrightarrow> s \<le> t"
      and x: "x \<in> X" "s = x \<bullet> b" "\<And>y. y \<in> X \<Longrightarrow> x \<bullet> b \<le> y \<bullet> b"
    by auto
  hence "Inf ?proj = x \<bullet> b"
    by (auto intro!: conditionally_complete_lattice_class.cInf_eq_minimum simp del: Inf_class.Inf_image_eq)
  hence "x \<bullet> b = Inf X \<bullet> b"
    by (auto simp: eucl_Inf Inf_class.INF_def inner_setsum_left inner_Basis if_distrib `b \<in> Basis` setsum_delta
      simp del: Inf_class.Inf_image_eq
      cong: if_cong)
  with x show "\<exists>x. x \<in> X \<and> x \<bullet> b = Inf X \<bullet> b \<and> (\<forall>y. y \<in> X \<longrightarrow> x \<bullet> b \<le> y \<bullet> b)" by blast
qed

lemma
  compact_attains_Sup_componentwise:
  fixes b::"'a::ordered_euclidean_space"
  assumes "b \<in> Basis" assumes "X \<noteq> {}" "compact X"
  obtains x where "x \<in> X" "x \<bullet> b = Sup X \<bullet> b" "\<And>y. y \<in> X \<Longrightarrow> y \<bullet> b \<le> x \<bullet> b"
proof atomize_elim
  let ?proj = "(\<lambda>x. x \<bullet> b) ` X"
  from assms have "compact ?proj" "?proj \<noteq> {}"
    by (auto intro!: compact_continuous_image continuous_on_intros)
  from compact_attains_sup[OF this]
  obtain s x
    where s: "s\<in>(\<lambda>x. x \<bullet> b) ` X" "\<And>t. t\<in>(\<lambda>x. x \<bullet> b) ` X \<Longrightarrow> t \<le> s"
      and x: "x \<in> X" "s = x \<bullet> b" "\<And>y. y \<in> X \<Longrightarrow> y \<bullet> b \<le> x \<bullet> b"
    by auto
  hence "Sup ?proj = x \<bullet> b"
    by (auto intro!: cSup_eq_maximum simp del: Sup_image_eq)
  hence "x \<bullet> b = Sup X \<bullet> b"
    by (auto simp: eucl_Sup[where 'a='a] SUP_def inner_setsum_left inner_Basis if_distrib `b \<in> Basis` setsum_delta
      simp del: Sup_image_eq cong: if_cong)
  with x show "\<exists>x. x \<in> X \<and> x \<bullet> b = Sup X \<bullet> b \<and> (\<forall>y. y \<in> X \<longrightarrow> y \<bullet> b \<le> x \<bullet> b)" by blast
qed

lemma (in order) atLeastatMost_empty'[simp]:
  "(~ a <= b) \<Longrightarrow> {a..b} = {}"
  by (auto)

instance real :: ordered_euclidean_space
  by default (auto simp: INF_def SUP_def)

lemma in_Basis_prod_iff:
  fixes i::"'a::euclidean_space*'b::euclidean_space"
  shows "i \<in> Basis \<longleftrightarrow> fst i = 0 \<and> snd i \<in> Basis \<or> snd i = 0 \<and> fst i \<in> Basis"
  by (cases i) (auto simp: Basis_prod_def)

instantiation prod::(abs, abs) abs
begin

definition "abs x = (abs (fst x), abs (snd x))"

instance proof qed
end

instance prod :: (ordered_euclidean_space, ordered_euclidean_space) ordered_euclidean_space
  by default
    (auto intro!: add_mono simp add: euclidean_representation_setsum'  Ball_def inner_prod_def
      in_Basis_prod_iff inner_Basis_inf_left inner_Basis_sup_left inner_Basis_INF_left Inf_prod_def
      inner_Basis_SUP_left Sup_prod_def less_prod_def less_eq_prod_def eucl_le[where 'a='a]
      eucl_le[where 'a='b] abs_prod_def abs_inner)


subsection {* Boxes *}

lemma box:
  fixes a :: "'a::euclidean_space"
  shows "box a b = {x::'a. \<forall>i\<in>Basis. a\<bullet>i < x\<bullet>i \<and> x\<bullet>i < b\<bullet>i}"
    and "cbox a b = {x::'a. \<forall>i\<in>Basis. a\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> b\<bullet>i}"
  by (auto simp add:set_eq_iff box_def cbox_def)

lemma mem_box:
  fixes a :: "'a::euclidean_space"
  shows "x \<in> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < x\<bullet>i \<and> x\<bullet>i < b\<bullet>i)"
    and "x \<in> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> b\<bullet>i)"
  using box[of a b]
  by auto

lemma box_eq_empty:
  fixes a :: "'a::euclidean_space"
  shows "(box a b = {} \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i \<le> a\<bullet>i))" (is ?th1)
    and "(cbox a b = {} \<longleftrightarrow> (\<exists>i\<in>Basis. b\<bullet>i < a\<bullet>i))" (is ?th2)
proof -
  {
    fix i x
    assume i: "i\<in>Basis" and as:"b\<bullet>i \<le> a\<bullet>i" and x:"x\<in>box a b"
    then have "a \<bullet> i < x \<bullet> i \<and> x \<bullet> i < b \<bullet> i"
      unfolding mem_box by (auto simp: box_def)
    then have "a\<bullet>i < b\<bullet>i" by auto
    then have False using as by auto
  }
  moreover
  {
    assume as: "\<forall>i\<in>Basis. \<not> (b\<bullet>i \<le> a\<bullet>i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    {
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "a\<bullet>i < b\<bullet>i"
        using as[THEN bspec[where x=i]] i by auto
      then have "a\<bullet>i < ((1/2) *\<^sub>R (a+b)) \<bullet> i" "((1/2) *\<^sub>R (a+b)) \<bullet> i < b\<bullet>i"
        by (auto simp: inner_add_left)
    }
    then have "box a b \<noteq> {}"
      using mem_box(1)[of "?x" a b] by auto
  }
  ultimately show ?th1 by blast

  {
    fix i x
    assume i: "i \<in> Basis" and as:"b\<bullet>i < a\<bullet>i" and x:"x\<in>cbox a b"
    then have "a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i"
      unfolding mem_box by auto
    then have "a\<bullet>i \<le> b\<bullet>i" by auto
    then have False using as by auto
  }
  moreover
  {
    assume as:"\<forall>i\<in>Basis. \<not> (b\<bullet>i < a\<bullet>i)"
    let ?x = "(1/2) *\<^sub>R (a + b)"
    {
      fix i :: 'a
      assume i:"i \<in> Basis"
      have "a\<bullet>i \<le> b\<bullet>i"
        using as[THEN bspec[where x=i]] i by auto
      then have "a\<bullet>i \<le> ((1/2) *\<^sub>R (a+b)) \<bullet> i" "((1/2) *\<^sub>R (a+b)) \<bullet> i \<le> b\<bullet>i"
        by (auto simp: inner_add_left)
    }
    then have "cbox a b \<noteq> {}"
      using mem_box(2)[of "?x" a b] by auto
  }
  ultimately show ?th2 by blast
qed

lemma box_ne_empty:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<noteq> {} \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i \<le> b\<bullet>i)"
  and "box a b \<noteq> {} \<longleftrightarrow> (\<forall>i\<in>Basis. a\<bullet>i < b\<bullet>i)"
  unfolding box_eq_empty[of a b] by fastforce+

lemma
  fixes a :: "'a::euclidean_space"
  shows cbox_sing: "cbox a a = {a}"
    and box_sing: "box a a = {}"
  unfolding set_eq_iff mem_box eq_iff [symmetric]
  by (auto intro!: euclidean_eqI[where 'a='a])
     (metis all_not_in_conv nonempty_Basis)

lemma subset_box_imp:
  fixes a :: "'a::euclidean_space"
  shows "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> cbox c d \<subseteq> cbox a b"
    and "(\<forall>i\<in>Basis. a\<bullet>i < c\<bullet>i \<and> d\<bullet>i < b\<bullet>i) \<Longrightarrow> cbox c d \<subseteq> box a b"
    and "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> box c d \<subseteq> cbox a b"
     and "(\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i) \<Longrightarrow> box c d \<subseteq> box a b"
  unfolding subset_eq[unfolded Ball_def] unfolding mem_box
   by (best intro: order_trans less_le_trans le_less_trans less_imp_le)+

lemma box_subset_cbox:
  fixes a :: "'a::euclidean_space"
  shows "box a b \<subseteq> cbox a b"
  unfolding subset_eq [unfolded Ball_def] mem_box
  by (fast intro: less_imp_le)

lemma subset_box:
  fixes a :: "'a::euclidean_space"
  shows "cbox c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i \<le> d\<bullet>i) --> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th1)
    and "cbox c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i \<le> d\<bullet>i) --> (\<forall>i\<in>Basis. a\<bullet>i < c\<bullet>i \<and> d\<bullet>i < b\<bullet>i)" (is ?th2)
    and "box c d \<subseteq> cbox a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i) --> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th3)
    and "box c d \<subseteq> box a b \<longleftrightarrow> (\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i) --> (\<forall>i\<in>Basis. a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i)" (is ?th4)
proof -
  show ?th1
    unfolding subset_eq and Ball_def and mem_box
    by (auto intro: order_trans)
  show ?th2
    unfolding subset_eq and Ball_def and mem_box
    by (auto intro: le_less_trans less_le_trans order_trans less_imp_le)
  {
    assume as: "box c d \<subseteq> cbox a b" "\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i"
    then have "box c d \<noteq> {}"
      unfolding box_eq_empty by auto
    fix i :: 'a
    assume i: "i \<in> Basis"
    (** TODO combine the following two parts as done in the HOL_light version. **)
    {
      let ?x = "(\<Sum>j\<in>Basis. (if j=i then ((min (a\<bullet>j) (d\<bullet>j))+c\<bullet>j)/2 else (c\<bullet>j+d\<bullet>j)/2) *\<^sub>R j)::'a"
      assume as2: "a\<bullet>i > c\<bullet>i"
      {
        fix j :: 'a
        assume j: "j \<in> Basis"
        then have "c \<bullet> j < ?x \<bullet> j \<and> ?x \<bullet> j < d \<bullet> j"
          apply (cases "j = i")
          using as(2)[THEN bspec[where x=j]] i
          apply (auto simp add: as2)
          done
      }
      then have "?x\<in>box c d"
        using i unfolding mem_box by auto
      moreover
      have "?x \<notin> cbox a b"
        unfolding mem_box
        apply auto
        apply (rule_tac x=i in bexI)
        using as(2)[THEN bspec[where x=i]] and as2 i
        apply auto
        done
      ultimately have False using as by auto
    }
    then have "a\<bullet>i \<le> c\<bullet>i" by (rule ccontr) auto
    moreover
    {
      let ?x = "(\<Sum>j\<in>Basis. (if j=i then ((max (b\<bullet>j) (c\<bullet>j))+d\<bullet>j)/2 else (c\<bullet>j+d\<bullet>j)/2) *\<^sub>R j)::'a"
      assume as2: "b\<bullet>i < d\<bullet>i"
      {
        fix j :: 'a
        assume "j\<in>Basis"
        then have "d \<bullet> j > ?x \<bullet> j \<and> ?x \<bullet> j > c \<bullet> j"
          apply (cases "j = i")
          using as(2)[THEN bspec[where x=j]]
          apply (auto simp add: as2)
          done
      }
      then have "?x\<in>box c d"
        unfolding mem_box by auto
      moreover
      have "?x\<notin>cbox a b"
        unfolding mem_box
        apply auto
        apply (rule_tac x=i in bexI)
        using as(2)[THEN bspec[where x=i]] and as2 using i
        apply auto
        done
      ultimately have False using as by auto
    }
    then have "b\<bullet>i \<ge> d\<bullet>i" by (rule ccontr) auto
    ultimately
    have "a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i" by auto
  } note part1 = this
  show ?th3
    unfolding subset_eq and Ball_def and mem_box
    apply (rule, rule, rule, rule)
    apply (rule part1)
    unfolding subset_eq and Ball_def and mem_box
    prefer 4
    apply auto
    apply (erule_tac x=xa in allE, erule_tac x=xa in allE, fastforce)+
    done
  {
    assume as: "box c d \<subseteq> box a b" "\<forall>i\<in>Basis. c\<bullet>i < d\<bullet>i"
    fix i :: 'a
    assume i:"i\<in>Basis"
    from as(1) have "box c d \<subseteq> cbox a b"
      using box_subset_cbox[of a b] by auto
    then have "a\<bullet>i \<le> c\<bullet>i \<and> d\<bullet>i \<le> b\<bullet>i"
      using part1 and as(2) using i by auto
  } note * = this
  show ?th4
    unfolding subset_eq and Ball_def and mem_box
    apply (rule, rule, rule, rule)
    apply (rule *)
    unfolding subset_eq and Ball_def and mem_box
    prefer 4
    apply auto
    apply (erule_tac x=xa in allE, simp)+
    done
qed

lemma inter_interval:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<inter> cbox c d =
    cbox (\<Sum>i\<in>Basis. max (a\<bullet>i) (c\<bullet>i) *\<^sub>R i) (\<Sum>i\<in>Basis. min (b\<bullet>i) (d\<bullet>i) *\<^sub>R i)"
  unfolding set_eq_iff and Int_iff and mem_box
  by auto

lemma disjoint_interval:
  fixes a::"'a::euclidean_space"
  shows "cbox a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i < a\<bullet>i \<or> d\<bullet>i < c\<bullet>i \<or> b\<bullet>i < c\<bullet>i \<or> d\<bullet>i < a\<bullet>i))" (is ?th1)
    and "cbox a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i < a\<bullet>i \<or> d\<bullet>i \<le> c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th2)
    and "box a b \<inter> cbox c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i \<le> a\<bullet>i \<or> d\<bullet>i < c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th3)
    and "box a b \<inter> box c d = {} \<longleftrightarrow> (\<exists>i\<in>Basis. (b\<bullet>i \<le> a\<bullet>i \<or> d\<bullet>i \<le> c\<bullet>i \<or> b\<bullet>i \<le> c\<bullet>i \<or> d\<bullet>i \<le> a\<bullet>i))" (is ?th4)
proof -
  let ?z = "(\<Sum>i\<in>Basis. (((max (a\<bullet>i) (c\<bullet>i)) + (min (b\<bullet>i) (d\<bullet>i))) / 2) *\<^sub>R i)::'a"
  have **: "\<And>P Q. (\<And>i :: 'a. i \<in> Basis \<Longrightarrow> Q ?z i \<Longrightarrow> P i) \<Longrightarrow>
      (\<And>i x :: 'a. i \<in> Basis \<Longrightarrow> P i \<Longrightarrow> Q x i) \<Longrightarrow> (\<forall>x. \<exists>i\<in>Basis. Q x i) \<longleftrightarrow> (\<exists>i\<in>Basis. P i)"
    by blast
  note * = set_eq_iff Int_iff empty_iff mem_box ball_conj_distrib[symmetric] eq_False ball_simps(10)
  show ?th1 unfolding * by (intro **) auto
  show ?th2 unfolding * by (intro **) auto
  show ?th3 unfolding * by (intro **) auto
  show ?th4 unfolding * by (intro **) auto
qed

(* Moved box_subset_cbox a bit upwards *)

lemma open_box[intro]:
  fixes a b :: "'a::euclidean_space"
  shows "open (box a b)"
proof -
  have "open (\<Inter>i\<in>Basis. (\<lambda>x. x\<bullet>i) -` {a\<bullet>i<..<b\<bullet>i})"
    by (intro open_INT finite_lessThan ballI continuous_open_vimage allI
      linear_continuous_at open_real_greaterThanLessThan finite_Basis bounded_linear_inner_left)
  also have "(\<Inter>i\<in>Basis. (\<lambda>x. x\<bullet>i) -` {a\<bullet>i<..<b\<bullet>i}) = box a b"
    by (auto simp add: box)
  finally show "open (box a b)" .
qed

lemma closed_cbox[intro]:
  fixes a b :: "'a::euclidean_space"
  shows "closed (cbox a b)"
proof -
  have "closed (\<Inter>i\<in>Basis. (\<lambda>x. x\<bullet>i) -` {a\<bullet>i .. b\<bullet>i})"
    by (intro closed_INT ballI continuous_closed_vimage allI
      linear_continuous_at closed_real_atLeastAtMost finite_Basis bounded_linear_inner_left)
  also have "(\<Inter>i\<in>Basis. (\<lambda>x. x\<bullet>i) -` {a\<bullet>i .. b\<bullet>i}) = cbox a b"
    by (auto simp add: cbox_def)
  finally show "closed (cbox a b)" .
qed

lemma interior_cbox [intro]:
  fixes a b :: "'a::euclidean_space"
  shows "interior (cbox a b) = box a b" (is "?L = ?R")
proof(rule subset_antisym)
  show "?R \<subseteq> ?L"
    using box_subset_cbox open_box
    by (rule interior_maximal)
  {
    fix x
    assume "x \<in> interior (cbox a b)"
    then obtain s where s: "open s" "x \<in> s" "s \<subseteq> cbox a b" ..
    then obtain e where "e>0" and e:"\<forall>x'. dist x' x < e \<longrightarrow> x' \<in> cbox a b"
      unfolding open_dist and subset_eq by auto
    {
      fix i :: 'a
      assume i: "i \<in> Basis"
      have "dist (x - (e / 2) *\<^sub>R i) x < e"
        and "dist (x + (e / 2) *\<^sub>R i) x < e"
        unfolding dist_norm
        apply auto
        unfolding norm_minus_cancel
        using norm_Basis[OF i] `e>0`
        apply auto
        done
      then have "a \<bullet> i \<le> (x - (e / 2) *\<^sub>R i) \<bullet> i" and "(x + (e / 2) *\<^sub>R i) \<bullet> i \<le> b \<bullet> i"
        using e[THEN spec[where x="x - (e/2) *\<^sub>R i"]]
          and e[THEN spec[where x="x + (e/2) *\<^sub>R i"]]
        unfolding mem_box
        using i
        by blast+
      then have "a \<bullet> i < x \<bullet> i" and "x \<bullet> i < b \<bullet> i"
        using `e>0` i
        by (auto simp: inner_diff_left inner_Basis inner_add_left)
    }
    then have "x \<in> box a b"
      unfolding mem_box by auto
  }
  then show "?L \<subseteq> ?R" ..
qed

lemma bounded_cbox:
  fixes a :: "'a::euclidean_space"
  shows "bounded (cbox a b)"
proof -
  let ?b = "\<Sum>i\<in>Basis. \<bar>a\<bullet>i\<bar> + \<bar>b\<bullet>i\<bar>"
  {
    fix x :: "'a"
    assume x: "\<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i"
    {
      fix i :: 'a
      assume "i \<in> Basis"
      then have "\<bar>x\<bullet>i\<bar> \<le> \<bar>a\<bullet>i\<bar> + \<bar>b\<bullet>i\<bar>"
        using x[THEN bspec[where x=i]] by auto
    }
    then have "(\<Sum>i\<in>Basis. \<bar>x \<bullet> i\<bar>) \<le> ?b"
      apply -
      apply (rule setsum_mono)
      apply auto
      done
    then have "norm x \<le> ?b"
      using norm_le_l1[of x] by auto
  }
  then show ?thesis
    unfolding box and bounded_iff by auto
qed

lemma bounded_interval:
  fixes a :: "'a::euclidean_space"
  shows "bounded (cbox a b) \<and> bounded (box a b)"
  using bounded_cbox[of a b]
  using box_subset_cbox[of a b]
  using bounded_subset[of "cbox a b" "box a b"]
  by simp

lemma not_interval_univ:
  fixes a :: "'a::euclidean_space"
  shows "cbox a b \<noteq> UNIV \<and> box a b \<noteq> UNIV"
  using bounded_interval[of a b] by auto

lemma compact_cbox:
  fixes a :: "'a::euclidean_space"
  shows "compact (cbox a b)"
  using bounded_closed_imp_seq_compact[of "cbox a b"] using bounded_interval[of a b]
  by (auto simp: compact_eq_seq_compact_metric)

lemma open_interval_midpoint:
  fixes a :: "'a::euclidean_space"
  assumes "box a b \<noteq> {}"
  shows "((1/2) *\<^sub>R (a + b)) \<in> box a b"
proof -
  {
    fix i :: 'a
    assume "i \<in> Basis"
    then have "a \<bullet> i < ((1 / 2) *\<^sub>R (a + b)) \<bullet> i \<and> ((1 / 2) *\<^sub>R (a + b)) \<bullet> i < b \<bullet> i"
      using assms[unfolded box_ne_empty, THEN bspec[where x=i]] by (auto simp: inner_add_left)
  }
  then show ?thesis unfolding mem_box by auto
qed

lemma open_closed_interval_convex:
  fixes x :: "'a::euclidean_space"
  assumes x: "x \<in> box a b"
    and y: "y \<in> cbox a b"
    and e: "0 < e" "e \<le> 1"
  shows "(e *\<^sub>R x + (1 - e) *\<^sub>R y) \<in> box a b"
proof -
  {
    fix i :: 'a
    assume i: "i \<in> Basis"
    have "a \<bullet> i = e * (a \<bullet> i) + (1 - e) * (a \<bullet> i)"
      unfolding left_diff_distrib by simp
    also have "\<dots> < e * (x \<bullet> i) + (1 - e) * (y \<bullet> i)"
      apply (rule add_less_le_mono)
      using e unfolding mult_less_cancel_left and mult_le_cancel_left
      apply simp_all
      using x unfolding mem_box using i
      apply simp
      using y unfolding mem_box using i
      apply simp
      done
    finally have "a \<bullet> i < (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i"
      unfolding inner_simps by auto
    moreover
    {
      have "b \<bullet> i = e * (b\<bullet>i) + (1 - e) * (b\<bullet>i)"
        unfolding left_diff_distrib by simp
      also have "\<dots> > e * (x \<bullet> i) + (1 - e) * (y \<bullet> i)"
        apply (rule add_less_le_mono)
        using e unfolding mult_less_cancel_left and mult_le_cancel_left
        apply simp_all
        using x
        unfolding mem_box
        using i
        apply simp
        using y
        unfolding mem_box
        using i
        apply simp
        done
      finally have "(e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i < b \<bullet> i"
        unfolding inner_simps by auto
    }
    ultimately have "a \<bullet> i < (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i \<and> (e *\<^sub>R x + (1 - e) *\<^sub>R y) \<bullet> i < b \<bullet> i"
      by auto
  }
  then show ?thesis
    unfolding mem_box by auto
qed

notation
  eucl_less (infix "<e" 50)

lemma closure_open_interval:
  fixes a :: "'a::euclidean_space"
   assumes "box a b \<noteq> {}"
  shows "closure (box a b) = cbox a b"
proof -
  have ab: "a <e b"
    using assms by (simp add: eucl_less_def box_ne_empty)
  let ?c = "(1 / 2) *\<^sub>R (a + b)"
  {
    fix x
    assume as:"x \<in> cbox a b"
    def f \<equiv> "\<lambda>n::nat. x + (inverse (real n + 1)) *\<^sub>R (?c - x)"
    {
      fix n
      assume fn: "f n <e b \<longrightarrow> a <e f n \<longrightarrow> f n = x" and xc: "x \<noteq> ?c"
      have *: "0 < inverse (real n + 1)" "inverse (real n + 1) \<le> 1"
        unfolding inverse_le_1_iff by auto
      have "(inverse (real n + 1)) *\<^sub>R ((1 / 2) *\<^sub>R (a + b)) + (1 - inverse (real n + 1)) *\<^sub>R x =
        x + (inverse (real n + 1)) *\<^sub>R (((1 / 2) *\<^sub>R (a + b)) - x)"
        by (auto simp add: algebra_simps)
      then have "f n <e b" and "a <e f n"
        using open_closed_interval_convex[OF open_interval_midpoint[OF assms] as *]
        unfolding f_def by (auto simp: box eucl_less_def)
      then have False
        using fn unfolding f_def using xc by auto
    }
    moreover
    {
      assume "\<not> (f ---> x) sequentially"
      {
        fix e :: real
        assume "e > 0"
        then have "\<exists>N::nat. inverse (real (N + 1)) < e"
          using real_arch_inv[of e]
          apply (auto simp add: Suc_pred')
          apply (rule_tac x="n - 1" in exI)
          apply auto
          done
        then obtain N :: nat where "inverse (real (N + 1)) < e"
          by auto
        then have "\<forall>n\<ge>N. inverse (real n + 1) < e"
          apply auto
          apply (metis Suc_le_mono le_SucE less_imp_inverse_less nat_le_real_less order_less_trans
            real_of_nat_Suc real_of_nat_Suc_gt_zero)
          done
        then have "\<exists>N::nat. \<forall>n\<ge>N. inverse (real n + 1) < e" by auto
      }
      then have "((\<lambda>n. inverse (real n + 1)) ---> 0) sequentially"
        unfolding LIMSEQ_def by(auto simp add: dist_norm)
      then have "(f ---> x) sequentially"
        unfolding f_def
        using tendsto_add[OF tendsto_const, of "\<lambda>n::nat. (inverse (real n + 1)) *\<^sub>R ((1 / 2) *\<^sub>R (a + b) - x)" 0 sequentially x]
        using tendsto_scaleR [OF _ tendsto_const, of "\<lambda>n::nat. inverse (real n + 1)" 0 sequentially "((1 / 2) *\<^sub>R (a + b) - x)"]
        by auto
    }
    ultimately have "x \<in> closure (box a b)"
      using as and open_interval_midpoint[OF assms]
      unfolding closure_def
      unfolding islimpt_sequential
      by (cases "x=?c") (auto simp: in_box_eucl_less)
  }
  then show ?thesis
    using closure_minimal[OF box_subset_cbox, of a b] by blast
qed

lemma bounded_subset_open_interval_symmetric:
  fixes s::"('a::euclidean_space) set"
  assumes "bounded s"
  shows "\<exists>a. s \<subseteq> box (-a) a"
proof -
  obtain b where "b>0" and b: "\<forall>x\<in>s. norm x \<le> b"
    using assms[unfolded bounded_pos] by auto
  def a \<equiv> "(\<Sum>i\<in>Basis. (b + 1) *\<^sub>R i)::'a"
  {
    fix x
    assume "x \<in> s"
    fix i :: 'a
    assume i: "i \<in> Basis"
    then have "(-a)\<bullet>i < x\<bullet>i" and "x\<bullet>i < a\<bullet>i"
      using b[THEN bspec[where x=x], OF `x\<in>s`]
      using Basis_le_norm[OF i, of x]
      unfolding inner_simps and a_def
      by auto
  }
  then show ?thesis
    by (auto intro: exI[where x=a] simp add: box)
qed

lemma bounded_subset_open_interval:
  fixes s :: "('a::euclidean_space) set"
  shows "bounded s \<Longrightarrow> (\<exists>a b. s \<subseteq> box a b)"
  by (auto dest!: bounded_subset_open_interval_symmetric)

lemma bounded_subset_cbox_symmetric:
  fixes s :: "('a::euclidean_space) set"
   assumes "bounded s"
  shows "\<exists>a. s \<subseteq> cbox (-a) a"
proof -
  obtain a where "s \<subseteq> box (-a) a"
    using bounded_subset_open_interval_symmetric[OF assms] by auto
  then show ?thesis
    using box_subset_cbox[of "-a" a] by auto
qed

lemma bounded_subset_cbox:
  fixes s :: "('a::euclidean_space) set"
  shows "bounded s \<Longrightarrow> \<exists>a b. s \<subseteq> cbox a b"
  using bounded_subset_cbox_symmetric[of s] by auto

lemma frontier_closed_interval:
  fixes a b :: "'a::euclidean_space"
  shows "frontier (cbox a b) = cbox a b - box a b"
  unfolding frontier_def unfolding interior_cbox and closure_closed[OF closed_cbox] ..

lemma frontier_open_interval:
  fixes a b :: "'a::euclidean_space"
  shows "frontier (box a b) = (if box a b = {} then {} else cbox a b - box a b)"
proof (cases "box a b = {}")
  case True
  then show ?thesis
    using frontier_empty by auto
next
  case False
  then show ?thesis
    unfolding frontier_def and closure_open_interval[OF False] and interior_open[OF open_box]
    by auto
qed

lemma inter_interval_mixed_eq_empty:
  fixes a :: "'a::euclidean_space"
   assumes "box c d \<noteq> {}"
  shows "box a b \<inter> cbox c d = {} \<longleftrightarrow> box a b \<inter> box c d = {}"
  unfolding closure_open_interval[OF assms, symmetric]
  unfolding open_inter_closure_eq_empty[OF open_box] ..

lemma diameter_closed_interval:
  fixes a b::"'a::ordered_euclidean_space"
  shows "a \<le> b \<Longrightarrow> diameter {a..b} = dist a b"
  by (force simp add: diameter_def SUP_def simp del: Sup_image_eq intro!: cSup_eq_maximum setL2_mono
     simp: euclidean_dist_l2[where 'a='a] eucl_le[where 'a='a] dist_norm)

text {* Intervals in general, including infinite and mixtures of open and closed. *}

definition "is_interval (s::('a::euclidean_space) set) \<longleftrightarrow>
  (\<forall>a\<in>s. \<forall>b\<in>s. \<forall>x. (\<forall>i\<in>Basis. ((a\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> b\<bullet>i) \<or> (b\<bullet>i \<le> x\<bullet>i \<and> x\<bullet>i \<le> a\<bullet>i))) \<longrightarrow> x \<in> s)"

lemma is_interval_interval: "is_interval (cbox a (b::'a::euclidean_space))" (is ?th1)
  "is_interval (box a b)" (is ?th2) proof -
  show ?th1 ?th2  unfolding is_interval_def mem_box Ball_def atLeastAtMost_iff
    by(meson order_trans le_less_trans less_le_trans less_trans)+ qed

lemma is_interval_empty:
 "is_interval {}"
  unfolding is_interval_def
  by simp

lemma is_interval_univ:
 "is_interval UNIV"
  unfolding is_interval_def
  by simp

lemma mem_is_intervalI:
  assumes "is_interval s"
  assumes "a \<in> s" "b \<in> s"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> a \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> b \<bullet> i \<or> b \<bullet> i \<le> x \<bullet> i \<and> x \<bullet> i \<le> a \<bullet> i"
  shows "x \<in> s"
  by (rule assms(1)[simplified is_interval_def, rule_format, OF assms(2,3,4)])

lemma interval_subst:
  fixes S::"'a::ordered_euclidean_space set"
  assumes "is_interval S"
  assumes "x \<in> S" "y j \<in> S"
  assumes "j \<in> Basis"
  shows "(\<Sum>i\<in>Basis. (if i = j then y i \<bullet> i else x \<bullet> i) *\<^sub>R i) \<in> S"
  by (rule mem_is_intervalI[OF assms(1,2)]) (auto simp: assms)

lemma mem_box_componentwiseI:
  fixes S::"'a::ordered_euclidean_space set"
  assumes "is_interval S"
  assumes "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i \<in> ((\<lambda>x. x \<bullet> i) ` S)"
  shows "x \<in> S"
proof -
  from assms have "\<forall>i \<in> Basis. \<exists>s \<in> S. x \<bullet> i = s \<bullet> i"
    by auto
  with finite_Basis obtain s and bs::"'a list" where
    s: "\<And>i. i \<in> Basis \<Longrightarrow> x \<bullet> i = s i \<bullet> i" "\<And>i. i \<in> Basis \<Longrightarrow> s i \<in> S" and
    bs: "set bs = Basis" "distinct bs"
    by (metis finite_distinct_list)
  from nonempty_Basis s obtain j where j: "j \<in> Basis" "s j \<in> S" by blast
  def y \<equiv> "rec_list
    (s j)
    (\<lambda>j _ Y. (\<Sum>i\<in>Basis. (if i = j then s i \<bullet> i else Y \<bullet> i) *\<^sub>R i))"
  have "x = (\<Sum>i\<in>Basis. (if i \<in> set bs then s i \<bullet> i else s j \<bullet> i) *\<^sub>R i)"
    using bs by (auto simp add: s(1)[symmetric] euclidean_representation)
  also have [symmetric]: "y bs = \<dots>"
    using bs(2) bs(1)[THEN equalityD1]
    by (induct bs) (auto simp: y_def euclidean_representation intro!: euclidean_eqI[where 'a='a])
  also have "y bs \<in> S"
    using bs(1)[THEN equalityD1]
    apply (induct bs)
    apply (auto simp: y_def j)
    apply (rule interval_subst[OF assms(1)])
    apply (auto simp: s)
    done
  finally show ?thesis .
qed

lemma eucl_less_eq_halfspaces:
  fixes a :: "'a\<Colon>euclidean_space"
  shows "{x. x <e a} = (\<Inter>i\<in>Basis. {x. x \<bullet> i < a \<bullet> i})"
    "{x. a <e x} = (\<Inter>i\<in>Basis. {x. a \<bullet> i < x \<bullet> i})"
  by (auto simp: eucl_less_def)

lemma eucl_le_eq_halfspaces:
  fixes a :: "'a\<Colon>euclidean_space"
  shows "{x. \<forall>i\<in>Basis. x \<bullet> i \<le> a \<bullet> i} = (\<Inter>i\<in>Basis. {x. x \<bullet> i \<le> a \<bullet> i})"
    "{x. \<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i} = (\<Inter>i\<in>Basis. {x. a \<bullet> i \<le> x \<bullet> i})"
  by auto

lemma open_Collect_eucl_less[simp, intro]:
  fixes a :: "'a\<Colon>euclidean_space"
  shows "open {x. x <e a}"
    "open {x. a <e x}"
  by (auto simp: eucl_less_eq_halfspaces open_halfspace_component_lt open_halfspace_component_gt)

lemma closed_Collect_eucl_le[simp, intro]:
  fixes a :: "'a\<Colon>euclidean_space"
  shows "closed {x. \<forall>i\<in>Basis. a \<bullet> i \<le> x \<bullet> i}"
    "closed {x. \<forall>i\<in>Basis. x \<bullet> i \<le> a \<bullet> i}"
  unfolding eucl_le_eq_halfspaces
  by (simp_all add: closed_INT closed_Collect_le)

lemma image_affinity_cbox: fixes m::real
  fixes a b c :: "'a::euclidean_space"
  shows "(\<lambda>x. m *\<^sub>R x + c) ` cbox a b =
    (if cbox a b = {} then {}
     else (if 0 \<le> m then cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c)
     else cbox (m *\<^sub>R b + c) (m *\<^sub>R a + c)))"
proof (cases "m = 0")
  case True
  {
    fix x
    assume "\<forall>i\<in>Basis. x \<bullet> i \<le> c \<bullet> i" "\<forall>i\<in>Basis. c \<bullet> i \<le> x \<bullet> i"
    then have "x = c"
      apply -
      apply (subst euclidean_eq_iff)
      apply (auto intro: order_antisym)
      done
  }
  moreover have "c \<in> cbox (m *\<^sub>R a + c) (m *\<^sub>R b + c)"
    unfolding True by (auto simp add: cbox_sing)
  ultimately show ?thesis using True by (auto simp: cbox_def)
next
  case False
  {
    fix y
    assume "\<forall>i\<in>Basis. a \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> b \<bullet> i" "m > 0"
    then have "\<forall>i\<in>Basis. (m *\<^sub>R a + c) \<bullet> i \<le> (m *\<^sub>R y + c) \<bullet> i" and "\<forall>i\<in>Basis. (m *\<^sub>R y + c) \<bullet> i \<le> (m *\<^sub>R b + c) \<bullet> i"
      by (auto simp: inner_distrib)
  }
  moreover
  {
    fix y
    assume "\<forall>i\<in>Basis. a \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> b \<bullet> i" "m < 0"
    then have "\<forall>i\<in>Basis. (m *\<^sub>R b + c) \<bullet> i \<le> (m *\<^sub>R y + c) \<bullet> i" and "\<forall>i\<in>Basis. (m *\<^sub>R y + c) \<bullet> i \<le> (m *\<^sub>R a + c) \<bullet> i"
      by (auto simp add: mult_left_mono_neg inner_distrib)
  }
  moreover
  {
    fix y
    assume "m > 0" and "\<forall>i\<in>Basis. (m *\<^sub>R a + c) \<bullet> i \<le> y \<bullet> i" and "\<forall>i\<in>Basis. y \<bullet> i \<le> (m *\<^sub>R b + c) \<bullet> i"
    then have "y \<in> (\<lambda>x. m *\<^sub>R x + c) ` cbox a b"
      unfolding image_iff Bex_def mem_box
      apply (intro exI[where x="(1 / m) *\<^sub>R (y - c)"])
      apply (auto simp add: pos_le_divide_eq pos_divide_le_eq mult_commute diff_le_iff inner_distrib inner_diff_left)
      done
  }
  moreover
  {
    fix y
    assume "\<forall>i\<in>Basis. (m *\<^sub>R b + c) \<bullet> i \<le> y \<bullet> i" "\<forall>i\<in>Basis. y \<bullet> i \<le> (m *\<^sub>R a + c) \<bullet> i" "m < 0"
    then have "y \<in> (\<lambda>x. m *\<^sub>R x + c) ` cbox a b"
      unfolding image_iff Bex_def mem_box
      apply (intro exI[where x="(1 / m) *\<^sub>R (y - c)"])
      apply (auto simp add: neg_le_divide_eq neg_divide_le_eq mult_commute diff_le_iff inner_distrib inner_diff_left)
      done
  }
  ultimately show ?thesis using False by (auto simp: cbox_def)
qed

lemma image_smult_cbox:"(\<lambda>x. m *\<^sub>R (x::_::euclidean_space)) ` cbox a b =
  (if cbox a b = {} then {} else if 0 \<le> m then cbox (m *\<^sub>R a) (m *\<^sub>R b) else cbox (m *\<^sub>R b) (m *\<^sub>R a))"
  using image_affinity_cbox[of m 0 a b] by auto

text{* Instantiation for intervals on @{text ordered_euclidean_space} *}

lemma
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows cbox_interval: "cbox a b = {a..b}"
    and interval_cbox: "{a..b} = cbox a b"
    and eucl_le_atMost: "{x. \<forall>i\<in>Basis. x \<bullet> i <= a \<bullet> i} = {..a}"
    and eucl_le_atLeast: "{x. \<forall>i\<in>Basis. a \<bullet> i <= x \<bullet> i} = {a..}"
    by (auto simp: eucl_le[where 'a='a] eucl_less_def box_def cbox_def)

lemma closed_eucl_atLeastAtMost[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "closed {a..b}"
  by (simp add: cbox_interval[symmetric] closed_cbox)

lemma closed_eucl_atMost[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "closed {..a}"
  by (simp add: eucl_le_atMost[symmetric])

lemma closed_eucl_atLeast[simp, intro]:
  fixes a :: "'a\<Colon>ordered_euclidean_space"
  shows "closed {a..}"
  by (simp add: eucl_le_atLeast[symmetric])

lemma image_affinity_interval: fixes m::real
  fixes a b c :: "'a::ordered_euclidean_space"
  shows "(\<lambda>x. m *\<^sub>R x + c) ` {a..b} =
    (if {a..b} = {} then {}
     else (if 0 \<le> m then {m *\<^sub>R a + c .. m *\<^sub>R b + c}
     else {m *\<^sub>R b + c .. m *\<^sub>R a + c}))"
  using image_affinity_cbox[of m c a b]
  by (simp add: cbox_interval)

lemma image_smult_interval:"(\<lambda>x. m *\<^sub>R (x::_::ordered_euclidean_space)) ` {a .. b} =
  (if {a .. b} = {} then {} else if 0 \<le> m then {m *\<^sub>R a .. m *\<^sub>R b} else {m *\<^sub>R b .. m *\<^sub>R a})"
  using image_smult_cbox[of m a b]
  by (simp add: cbox_interval)

no_notation
  eucl_less (infix "<e" 50)

end
