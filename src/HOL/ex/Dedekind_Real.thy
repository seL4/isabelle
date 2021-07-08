section \<open>The Reals as Dedekind Sections of Positive Rationals\<close>

text \<open>Fundamentals of Abstract Analysis [Gleason- p. 121] provides some of the definitions.\<close>

(*  Title:      HOL/ex/Dedekind_Real.thy
    Author:     Jacques D. Fleuriot, University of Cambridge
    Conversion to Isar and new proofs by Lawrence C Paulson, 2003/4; 2019
*)

theory Dedekind_Real
imports Complex_Main 
begin

text\<open>Could be moved to \<open>Groups\<close>\<close>
lemma add_eq_exists: "\<exists>x. a+x = (b::'a::ab_group_add)"
  by (rule_tac x="b-a" in exI, simp)

subsection \<open>Dedekind cuts or sections\<close>

definition
  cut :: "rat set \<Rightarrow> bool" where
  "cut A \<equiv> {} \<subset> A \<and> A \<subset> {0<..} \<and>
            (\<forall>y \<in> A. ((\<forall>z. 0<z \<and> z < y \<longrightarrow> z \<in> A) \<and> (\<exists>u \<in> A. y < u)))"

lemma cut_of_rat: 
  assumes q: "0 < q" shows "cut {r::rat. 0 < r \<and> r < q}" (is "cut ?A")
proof -
  from q have pos: "?A \<subset> {0<..}" by force
  have nonempty: "{} \<subset> ?A"
  proof
    show "{} \<subseteq> ?A" by simp
    show "{} \<noteq> ?A"
      using field_lbound_gt_zero q by auto
  qed
  show ?thesis
    by (simp add: cut_def pos nonempty,
        blast dest: dense intro: order_less_trans)
qed


typedef preal = "Collect cut"
  by (blast intro: cut_of_rat [OF zero_less_one])

lemma Abs_preal_induct [induct type: preal]:
  "(\<And>x. cut x \<Longrightarrow> P (Abs_preal x)) \<Longrightarrow> P x"
  using Abs_preal_induct [of P x] by simp

lemma cut_Rep_preal [simp]: "cut (Rep_preal x)"
  using Rep_preal [of x] by simp

definition
  psup :: "preal set \<Rightarrow> preal" where
  "psup P = Abs_preal (\<Union>X \<in> P. Rep_preal X)"

definition
  add_set :: "[rat set,rat set] \<Rightarrow> rat set" where
  "add_set A B = {w. \<exists>x \<in> A. \<exists>y \<in> B. w = x + y}"

definition
  diff_set :: "[rat set,rat set] \<Rightarrow> rat set" where
  "diff_set A B = {w. \<exists>x. 0 < w \<and> 0 < x \<and> x \<notin> B \<and> x + w \<in> A}"

definition
  mult_set :: "[rat set,rat set] \<Rightarrow> rat set" where
  "mult_set A B = {w. \<exists>x \<in> A. \<exists>y \<in> B. w = x * y}"

definition
  inverse_set :: "rat set \<Rightarrow> rat set" where
  "inverse_set A \<equiv> {x. \<exists>y. 0 < x \<and> x < y \<and> inverse y \<notin> A}"

instantiation preal :: "{ord, plus, minus, times, inverse, one}"
begin

definition
  preal_less_def:
    "r < s \<equiv> Rep_preal r < Rep_preal s"

definition
  preal_le_def:
    "r \<le> s \<equiv> Rep_preal r \<subseteq> Rep_preal s"

definition
  preal_add_def:
    "r + s \<equiv> Abs_preal (add_set (Rep_preal r) (Rep_preal s))"

definition
  preal_diff_def:
    "r - s \<equiv> Abs_preal (diff_set (Rep_preal r) (Rep_preal s))"

definition
  preal_mult_def:
    "r * s \<equiv> Abs_preal (mult_set (Rep_preal r) (Rep_preal s))"

definition
  preal_inverse_def:
    "inverse r \<equiv> Abs_preal (inverse_set (Rep_preal r))"

definition "r div s = r * inverse (s::preal)"

definition
  preal_one_def:
    "1 \<equiv> Abs_preal {x. 0 < x \<and> x < 1}"

instance ..

end


text\<open>Reduces equality on abstractions to equality on representatives\<close>
declare Abs_preal_inject [simp]
declare Abs_preal_inverse [simp]

lemma rat_mem_preal: "0 < q \<Longrightarrow> cut {r::rat. 0 < r \<and> r < q}"
by (simp add: cut_of_rat)

lemma preal_nonempty: "cut A \<Longrightarrow> \<exists>x\<in>A. 0 < x"
  unfolding cut_def [abs_def] by blast

lemma preal_Ex_mem: "cut A \<Longrightarrow> \<exists>x. x \<in> A"
  using preal_nonempty by blast

lemma preal_exists_bound: "cut A \<Longrightarrow> \<exists>x. 0 < x \<and> x \<notin> A"
  using Dedekind_Real.cut_def by fastforce

lemma preal_exists_greater: "\<lbrakk>cut A; y \<in> A\<rbrakk> \<Longrightarrow> \<exists>u \<in> A. y < u"
  unfolding cut_def [abs_def] by blast

lemma preal_downwards_closed: "\<lbrakk>cut A; y \<in> A; 0 < z; z < y\<rbrakk> \<Longrightarrow> z \<in> A"
  unfolding cut_def [abs_def] by blast

text\<open>Relaxing the final premise\<close>
lemma preal_downwards_closed': "\<lbrakk>cut A; y \<in> A; 0 < z; z \<le> y\<rbrakk> \<Longrightarrow> z \<in> A"
  using less_eq_rat_def preal_downwards_closed by blast

text\<open>A positive fraction not in a positive real is an upper bound.
 Gleason p. 122 - Remark (1)\<close>

lemma not_in_preal_ub:
  assumes A: "cut A"
    and notx: "x \<notin> A"
    and y: "y \<in> A"
    and pos: "0 < x"
  shows "y < x"
proof (cases rule: linorder_cases)
  assume "x<y"
  with notx show ?thesis
    by (simp add:  preal_downwards_closed [OF A y] pos)
next
  assume "x=y"
  with notx and y show ?thesis by simp
next
  assume "y<x"
  thus ?thesis .
qed

text \<open>preal lemmas instantiated to \<^term>\<open>Rep_preal X\<close>\<close>

lemma mem_Rep_preal_Ex: "\<exists>x. x \<in> Rep_preal X"
thm preal_Ex_mem
by (rule preal_Ex_mem [OF cut_Rep_preal])

lemma Rep_preal_exists_bound: "\<exists>x>0. x \<notin> Rep_preal X"
by (rule preal_exists_bound [OF cut_Rep_preal])

lemmas not_in_Rep_preal_ub = not_in_preal_ub [OF cut_Rep_preal]


subsection\<open>Properties of Ordering\<close>

instance preal :: order
proof
  fix w :: preal
  show "w \<le> w" by (simp add: preal_le_def)
next
  fix i j k :: preal
  assume "i \<le> j" and "j \<le> k"
  then show "i \<le> k" by (simp add: preal_le_def)
next
  fix z w :: preal
  assume "z \<le> w" and "w \<le> z"
  then show "z = w" by (simp add: preal_le_def Rep_preal_inject)
next
  fix z w :: preal
  show "z < w \<longleftrightarrow> z \<le> w \<and> \<not> w \<le> z"
  by (auto simp: preal_le_def preal_less_def Rep_preal_inject)
qed  

lemma preal_imp_pos: "\<lbrakk>cut A; r \<in> A\<rbrakk> \<Longrightarrow> 0 < r"
  by (auto simp: cut_def)

instance preal :: linorder
proof
  fix x y :: preal
  show "x \<le> y \<or> y \<le> x"
    unfolding preal_le_def
    by (meson cut_Rep_preal not_in_preal_ub preal_downwards_closed preal_imp_pos subsetI)
qed

instantiation preal :: distrib_lattice
begin

definition
  "(inf :: preal \<Rightarrow> preal \<Rightarrow> preal) = min"

definition
  "(sup :: preal \<Rightarrow> preal \<Rightarrow> preal) = max"

instance
  by intro_classes
    (auto simp: inf_preal_def sup_preal_def max_min_distrib2)

end

subsection\<open>Properties of Addition\<close>

lemma preal_add_commute: "(x::preal) + y = y + x"
  unfolding preal_add_def add_set_def
  by (metis (no_types, opaque_lifting) add.commute)

text\<open>Lemmas for proving that addition of two positive reals gives
 a positive real\<close>

lemma mem_add_set:
  assumes "cut A" "cut B"
  shows "cut (add_set A B)"
proof -
  have "{} \<subset> add_set A B"
    using assms by (force simp: add_set_def dest: preal_nonempty)
  moreover
  obtain q where "q > 0" "q \<notin> add_set A B"
  proof -
    obtain a b where "a > 0" "a \<notin> A" "b > 0" "b \<notin> B" "\<And>x. x \<in> A \<Longrightarrow> x < a" "\<And>y. y \<in> B \<Longrightarrow> y < b"
      by (meson assms preal_exists_bound not_in_preal_ub)
    with assms have "a+b \<notin> add_set A B"
      by (fastforce simp add: add_set_def)
    then show thesis
      using \<open>0 < a\<close> \<open>0 < b\<close> add_pos_pos that by blast
  qed
  then have "add_set A B \<subset> {0<..}"
    unfolding add_set_def
    using preal_imp_pos [OF \<open>cut A\<close>] preal_imp_pos [OF \<open>cut B\<close>]  by fastforce
  moreover have "z \<in> add_set A B" 
    if u: "u \<in> add_set A B" and "0 < z" "z < u" for u z
    using u unfolding add_set_def
  proof (clarify)
    fix x::rat and y::rat
    assume ueq: "u = x + y" and x: "x \<in> A" and y:"y \<in> B"
    have xpos [simp]: "x > 0" and ypos [simp]: "y > 0"
      using assms preal_imp_pos x y by blast+
    have xypos [simp]: "x+y > 0" by (simp add: pos_add_strict)
    let ?f = "z/(x+y)"
    have fless: "?f < 1"
      using divide_less_eq_1_pos \<open>z < u\<close> ueq xypos by blast
    show "\<exists>x' \<in> A. \<exists>y'\<in>B. z = x' + y'"
    proof (intro bexI)
      show "z = x*?f + y*?f"
        by (simp add: distrib_right [symmetric] divide_inverse ac_simps order_less_imp_not_eq2)
    next
      show "y * ?f \<in> B"
      proof (rule preal_downwards_closed [OF \<open>cut B\<close> y])
        show "0 < y * ?f"
          by (simp add: \<open>0 < z\<close>)
      next
        show "y * ?f < y"
          by (insert mult_strict_left_mono [OF fless ypos], simp)
      qed
    next
      show "x * ?f \<in> A"
      proof (rule preal_downwards_closed [OF \<open>cut A\<close> x])
        show "0 < x * ?f"
          by (simp add: \<open>0 < z\<close>)
      next
        show "x * ?f < x"
          by (insert mult_strict_left_mono [OF fless xpos], simp)
      qed
    qed
  qed
  moreover
  have "\<And>y. y \<in> add_set A B \<Longrightarrow> \<exists>u \<in> add_set A B. y < u"
    unfolding add_set_def using preal_exists_greater assms by fastforce
  ultimately show ?thesis
    by (simp add: Dedekind_Real.cut_def)
qed

lemma preal_add_assoc: "((x::preal) + y) + z = x + (y + z)"
  apply (simp add: preal_add_def mem_add_set)
  apply (force simp: add_set_def ac_simps)
  done

instance preal :: ab_semigroup_add
proof
  fix a b c :: preal
  show "(a + b) + c = a + (b + c)" by (rule preal_add_assoc)
  show "a + b = b + a" by (rule preal_add_commute)
qed


subsection\<open>Properties of Multiplication\<close>

text\<open>Proofs essentially same as for addition\<close>

lemma preal_mult_commute: "(x::preal) * y = y * x"
  unfolding preal_mult_def mult_set_def
  by (metis (no_types, opaque_lifting) mult.commute)

text\<open>Multiplication of two positive reals gives a positive real.\<close>

lemma mem_mult_set:
  assumes "cut A" "cut B"
  shows "cut (mult_set A B)"
proof -
  have "{} \<subset> mult_set A B"
    using assms
      by (force simp: mult_set_def dest: preal_nonempty)
    moreover
    obtain q where "q > 0" "q \<notin> mult_set A B"
    proof -
      obtain x y where x [simp]: "0 < x" "x \<notin> A" and y [simp]: "0 < y" "y \<notin> B"
        using preal_exists_bound assms by blast
      show thesis
      proof 
        show "0 < x*y" by simp
        show "x * y \<notin> mult_set A B"
        proof -
          {
            fix u::rat and v::rat
            assume u: "u \<in> A" and v: "v \<in> B" and xy: "x*y = u*v"
            moreover have "u<x" and "v<y" using assms x y u v by (blast dest: not_in_preal_ub)+
            moreover have "0\<le>v"
              using less_imp_le preal_imp_pos assms x y u v by blast
            moreover have "u*v < x*y"
                using assms x \<open>u < x\<close> \<open>v < y\<close> \<open>0 \<le> v\<close> by (blast intro: mult_strict_mono)
            ultimately have False by force
          }
          thus ?thesis by (auto simp: mult_set_def)
        qed
      qed
    qed
  then have "mult_set A B \<subset> {0<..}"
    unfolding mult_set_def
    using preal_imp_pos [OF \<open>cut A\<close>] preal_imp_pos [OF \<open>cut B\<close>]  by fastforce
  moreover have "z \<in> mult_set A B"
    if u: "u \<in> mult_set A B" and "0 < z" "z < u" for u z
    using u unfolding mult_set_def
  proof (clarify)
    fix x::rat and y::rat
    assume ueq: "u = x * y" and x: "x \<in> A" and y: "y \<in> B"  
    have [simp]: "y > 0"
      using \<open>cut B\<close> preal_imp_pos y by blast
    show "\<exists>x' \<in> A. \<exists>y' \<in> B. z = x' * y'"
    proof
      have "z = (z/y)*y"
          by (simp add: divide_inverse mult.commute [of y] mult.assoc order_less_imp_not_eq2)
      then show "\<exists>y'\<in>B. z = (z/y) * y'"
        using y by blast
    next
      show "z/y \<in> A"
      proof (rule preal_downwards_closed [OF \<open>cut A\<close> x])
        show "0 < z/y"
          by (simp add: \<open>0 < z\<close>)
        show "z/y < x"
          using \<open>0 < y\<close> pos_divide_less_eq \<open>z < u\<close> ueq by blast  
      qed
    qed
  qed
  moreover have "\<And>y. y \<in> mult_set A B \<Longrightarrow> \<exists>u \<in> mult_set A B. y < u"
    apply (simp add: mult_set_def)
    by (metis preal_exists_greater mult_strict_right_mono preal_imp_pos assms)
  ultimately show ?thesis
    by (simp add: Dedekind_Real.cut_def)
qed

lemma preal_mult_assoc: "((x::preal) * y) * z = x * (y * z)"
  apply (simp add: preal_mult_def mem_mult_set Rep_preal)
  apply (simp add: mult_set_def)
  apply (metis (no_types, opaque_lifting) ab_semigroup_mult_class.mult_ac(1))
  done

instance preal :: ab_semigroup_mult
proof
  fix a b c :: preal
  show "(a * b) * c = a * (b * c)" by (rule preal_mult_assoc)
  show "a * b = b * a" by (rule preal_mult_commute)
qed


text\<open>Positive real 1 is the multiplicative identity element\<close>

lemma preal_mult_1: "(1::preal) * z = z"
proof (induct z)
  fix A :: "rat set"
  assume A: "cut A"
  have "{w. \<exists>u. 0 < u \<and> u < 1 \<and> (\<exists>v \<in> A. w = u * v)} = A" (is "?lhs = A")
  proof
    show "?lhs \<subseteq> A"
    proof clarify
      fix x::rat and u::rat and v::rat
      assume upos: "0<u" and "u<1" and v: "v \<in> A"
      have vpos: "0<v" by (rule preal_imp_pos [OF A v])
      hence "u*v < 1*v" by (simp only: mult_strict_right_mono upos \<open>u < 1\<close> v)
      thus "u * v \<in> A"
        by (force intro: preal_downwards_closed [OF A v] mult_pos_pos  upos vpos)
    qed
  next
    show "A \<subseteq> ?lhs"
    proof clarify
      fix x::rat
      assume x: "x \<in> A"
      have xpos: "0<x" by (rule preal_imp_pos [OF A x])
      from preal_exists_greater [OF A x]
      obtain v where v: "v \<in> A" and xlessv: "x < v" ..
      have vpos: "0<v" by (rule preal_imp_pos [OF A v])
      show "\<exists>u. 0 < u \<and> u < 1 \<and> (\<exists>v\<in>A. x = u * v)"
      proof (intro exI conjI)
        show "0 < x/v"
          by (simp add: zero_less_divide_iff xpos vpos)
        show "x / v < 1"
          by (simp add: pos_divide_less_eq vpos xlessv)
        have "x = (x/v)*v"
            by (simp add: divide_inverse mult.assoc vpos order_less_imp_not_eq2)
        then show "\<exists>v'\<in>A. x = (x / v) * v'"
          using v by blast
      qed
    qed
  qed
  thus "1 * Abs_preal A = Abs_preal A"
    by (simp add: preal_one_def preal_mult_def mult_set_def rat_mem_preal A)
qed

instance preal :: comm_monoid_mult
  by intro_classes (rule preal_mult_1)


subsection\<open>Distribution of Multiplication across Addition\<close>

lemma mem_Rep_preal_add_iff:
  "(z \<in> Rep_preal(r+s)) = (\<exists>x \<in> Rep_preal r. \<exists>y \<in> Rep_preal s. z = x + y)"
  apply (simp add: preal_add_def mem_add_set Rep_preal)
  apply (simp add: add_set_def) 
  done

lemma mem_Rep_preal_mult_iff:
  "(z \<in> Rep_preal(r*s)) = (\<exists>x \<in> Rep_preal r. \<exists>y \<in> Rep_preal s. z = x * y)"
  apply (simp add: preal_mult_def mem_mult_set Rep_preal)
  apply (simp add: mult_set_def) 
  done

lemma distrib_subset1:
  "Rep_preal (w * (x + y)) \<subseteq> Rep_preal (w * x + w * y)"
  by (force simp: Bex_def mem_Rep_preal_add_iff mem_Rep_preal_mult_iff distrib_left)

lemma preal_add_mult_distrib_mean:
  assumes a: "a \<in> Rep_preal w"
    and b: "b \<in> Rep_preal w"
    and d: "d \<in> Rep_preal x"
    and e: "e \<in> Rep_preal y"
  shows "\<exists>c \<in> Rep_preal w. a * d + b * e = c * (d + e)"
proof
  let ?c = "(a*d + b*e)/(d+e)"
  have [simp]: "0<a" "0<b" "0<d" "0<e" "0<d+e"
    by (blast intro: preal_imp_pos [OF cut_Rep_preal] a b d e pos_add_strict)+
  have cpos: "0 < ?c"
    by (simp add: zero_less_divide_iff zero_less_mult_iff pos_add_strict)
  show "a * d + b * e = ?c * (d + e)"
    by (simp add: divide_inverse mult.assoc order_less_imp_not_eq2)
  show "?c \<in> Rep_preal w"
  proof (cases rule: linorder_le_cases)
    assume "a \<le> b"
    hence "?c \<le> b"
      by (simp add: pos_divide_le_eq distrib_left mult_right_mono
                    order_less_imp_le)
    thus ?thesis by (rule preal_downwards_closed' [OF cut_Rep_preal b cpos])
  next
    assume "b \<le> a"
    hence "?c \<le> a"
      by (simp add: pos_divide_le_eq distrib_left mult_right_mono
                    order_less_imp_le)
    thus ?thesis by (rule preal_downwards_closed' [OF cut_Rep_preal a cpos])
  qed
qed

lemma distrib_subset2:
  "Rep_preal (w * x + w * y) \<subseteq> Rep_preal (w * (x + y))"
  apply (clarsimp simp: mem_Rep_preal_add_iff mem_Rep_preal_mult_iff)
  using mem_Rep_preal_add_iff preal_add_mult_distrib_mean by blast

lemma preal_add_mult_distrib2: "(w * ((x::preal) + y)) = (w * x) + (w * y)"
  by (metis Rep_preal_inverse distrib_subset1 distrib_subset2 subset_antisym)

lemma preal_add_mult_distrib: "(((x::preal) + y) * w) = (x * w) + (y * w)"
  by (simp add: preal_mult_commute preal_add_mult_distrib2)

instance preal :: comm_semiring
  by intro_classes (rule preal_add_mult_distrib)


subsection\<open>Existence of Inverse, a Positive Real\<close>

lemma mem_inverse_set:
  assumes "cut A" shows "cut (inverse_set A)"
proof -
  have "\<exists>x y. 0 < x \<and> x < y \<and> inverse y \<notin> A"
  proof -
    from preal_exists_bound [OF \<open>cut A\<close>]
    obtain x where [simp]: "0<x" "x \<notin> A" by blast
    show ?thesis
    proof (intro exI conjI)
      show "0 < inverse (x+1)"
        by (simp add: order_less_trans [OF _ less_add_one]) 
      show "inverse(x+1) < inverse x"
        by (simp add: less_imp_inverse_less less_add_one)
      show "inverse (inverse x) \<notin> A"
        by (simp add: order_less_imp_not_eq2)
    qed
  qed
  then have "{} \<subset> inverse_set A"
    using inverse_set_def by fastforce
  moreover obtain q where "q > 0" "q \<notin> inverse_set A"
  proof -
    from preal_nonempty [OF \<open>cut A\<close>]
    obtain x where x: "x \<in> A" and  xpos [simp]: "0<x" ..
    show ?thesis
    proof 
      show "0 < inverse x" by simp
      show "inverse x \<notin> inverse_set A"
      proof -
        { fix y::rat 
          assume ygt: "inverse x < y"
          have [simp]: "0 < y" by (simp add: order_less_trans [OF _ ygt])
          have iyless: "inverse y < x" 
            by (simp add: inverse_less_imp_less [of x] ygt)
          have "inverse y \<in> A"
            by (simp add: preal_downwards_closed [OF \<open>cut A\<close> x] iyless)}
        thus ?thesis by (auto simp: inverse_set_def)
      qed
    qed
  qed
  moreover have "inverse_set A \<subset> {0<..}"
    using calculation inverse_set_def by blast
  moreover have "z \<in> inverse_set A"
    if u: "u \<in> inverse_set A" and "0 < z" "z < u" for u z
    using u that less_trans unfolding inverse_set_def by auto
  moreover have "\<And>y. y \<in> inverse_set A \<Longrightarrow> \<exists>u \<in> inverse_set A. y < u"
    by (simp add: inverse_set_def) (meson dense less_trans)
  ultimately show ?thesis
    by (simp add: Dedekind_Real.cut_def)
qed


subsection\<open>Gleason's Lemma 9-3.4, page 122\<close>

lemma Gleason9_34_exists:
  assumes A: "cut A"
    and "\<forall>x\<in>A. x + u \<in> A"
    and "0 \<le> z"
  shows "\<exists>b\<in>A. b + (of_int z) * u \<in> A"
proof (cases z rule: int_cases)
  case (nonneg n)
  show ?thesis
  proof (simp add: nonneg, induct n)
    case 0
    from preal_nonempty [OF A]
    show ?case  by force 
  next
    case (Suc k)
    then obtain b where b: "b \<in> A" "b + of_nat k * u \<in> A" ..
    hence "b + of_int (int k)*u + u \<in> A" by (simp add: assms)
    thus ?case by (force simp: algebra_simps b)
  qed
next
  case (neg n)
  with assms show ?thesis by simp
qed

lemma Gleason9_34_contra:
  assumes A: "cut A"
    shows "\<lbrakk>\<forall>x\<in>A. x + u \<in> A; 0 < u; 0 < y; y \<notin> A\<rbrakk> \<Longrightarrow> False"
proof (induct u, induct y)
  fix a::int and b::int
  fix c::int and d::int
  assume bpos [simp]: "0 < b"
    and dpos [simp]: "0 < d"
    and closed: "\<forall>x\<in>A. x + (Fract c d) \<in> A"
    and upos: "0 < Fract c d"
    and ypos: "0 < Fract a b"
    and notin: "Fract a b \<notin> A"
  have cpos [simp]: "0 < c" 
    by (simp add: zero_less_Fract_iff [OF dpos, symmetric] upos) 
  have apos [simp]: "0 < a" 
    by (simp add: zero_less_Fract_iff [OF bpos, symmetric] ypos) 
  let ?k = "a*d"
  have frle: "Fract a b \<le> Fract ?k 1 * (Fract c d)" 
  proof -
    have "?thesis = ((a * d * b * d) \<le> c * b * (a * d * b * d))"
      by (simp add: order_less_imp_not_eq2 ac_simps) 
    moreover
    have "(1 * (a * d * b * d)) \<le> c * b * (a * d * b * d)"
      by (rule mult_mono, 
          simp_all add: int_one_le_iff_zero_less zero_less_mult_iff 
                        order_less_imp_le)
    ultimately
    show ?thesis by simp
  qed
  have k: "0 \<le> ?k" by (simp add: order_less_imp_le zero_less_mult_iff)  
  from Gleason9_34_exists [OF A closed k]
  obtain z where z: "z \<in> A" 
             and mem: "z + of_int ?k * Fract c d \<in> A" ..
  have less: "z + of_int ?k * Fract c d < Fract a b"
    by (rule not_in_preal_ub [OF A notin mem ypos])
  have "0<z" by (rule preal_imp_pos [OF A z])
  with frle and less show False by (simp add: Fract_of_int_eq) 
qed


lemma Gleason9_34:
  assumes "cut A" "0 < u"
  shows "\<exists>r \<in> A. r + u \<notin> A"
  using assms Gleason9_34_contra preal_exists_bound by blast



subsection\<open>Gleason's Lemma 9-3.6\<close>

lemma lemma_gleason9_36:
  assumes A: "cut A"
    and x: "1 < x"
  shows "\<exists>r \<in> A. r*x \<notin> A"
proof -
  from preal_nonempty [OF A]
  obtain y where y: "y \<in> A" and  ypos: "0<y" ..
  show ?thesis 
  proof (rule classical)
    assume "~(\<exists>r\<in>A. r * x \<notin> A)"
    with y have ymem: "y * x \<in> A" by blast 
    from ypos mult_strict_left_mono [OF x]
    have yless: "y < y*x" by simp 
    let ?d = "y*x - y"
    from yless have dpos: "0 < ?d" and eq: "y + ?d = y*x" by auto
    from Gleason9_34 [OF A dpos]
    obtain r where r: "r\<in>A" and notin: "r + ?d \<notin> A" ..
    have rpos: "0<r" by (rule preal_imp_pos [OF A r])
    with dpos have rdpos: "0 < r + ?d" by arith
    have "~ (r + ?d \<le> y + ?d)"
    proof
      assume le: "r + ?d \<le> y + ?d" 
      from ymem have yd: "y + ?d \<in> A" by (simp add: eq)
      have "r + ?d \<in> A" by (rule preal_downwards_closed' [OF A yd rdpos le])
      with notin show False by simp
    qed
    hence "y < r" by simp
    with ypos have  dless: "?d < (r * ?d)/y"
      using dpos less_divide_eq_1 by fastforce
    have "r + ?d < r*x"
    proof -
      have "r + ?d < r + (r * ?d)/y" by (simp add: dless)
      also from ypos have "\<dots> = (r/y) * (y + ?d)"
        by (simp only: algebra_simps divide_inverse, simp)
      also have "\<dots> = r*x" using ypos
        by simp
      finally show "r + ?d < r*x" .
    qed
    with r notin rdpos
    show "\<exists>r\<in>A. r * x \<notin> A" by (blast dest:  preal_downwards_closed [OF A])
  qed  
qed

subsection\<open>Existence of Inverse: Part 2\<close>

lemma mem_Rep_preal_inverse_iff:
  "(z \<in> Rep_preal(inverse r)) \<longleftrightarrow> (0 < z \<and> (\<exists>y. z < y \<and> inverse y \<notin> Rep_preal r))"
  apply (simp add: preal_inverse_def mem_inverse_set Rep_preal)
  apply (simp add: inverse_set_def) 
  done

lemma Rep_preal_one:
     "Rep_preal 1 = {x. 0 < x \<and> x < 1}"
by (simp add: preal_one_def rat_mem_preal)

lemma subset_inverse_mult_lemma:
  assumes xpos: "0 < x" and xless: "x < 1"
  shows "\<exists>v u y. 0 < v \<and> v < y \<and> inverse y \<notin> Rep_preal R \<and> 
    u \<in> Rep_preal R \<and> x = v * u"
proof -
  from xpos and xless have "1 < inverse x" by (simp add: one_less_inverse_iff)
  from lemma_gleason9_36 [OF cut_Rep_preal this]
  obtain t where t: "t \<in> Rep_preal R" 
             and notin: "t * (inverse x) \<notin> Rep_preal R" ..
  have rpos: "0<t" by (rule preal_imp_pos [OF cut_Rep_preal t])
  from preal_exists_greater [OF cut_Rep_preal t]
  obtain u where u: "u \<in> Rep_preal R" and rless: "t < u" ..
  have upos: "0<u" by (rule preal_imp_pos [OF cut_Rep_preal u])
  show ?thesis
  proof (intro exI conjI)
    show "0 < x/u" using xpos upos
      by (simp add: zero_less_divide_iff)  
    show "x/u < x/t" using xpos upos rpos
      by (simp add: divide_inverse mult_less_cancel_left rless) 
    show "inverse (x / t) \<notin> Rep_preal R" using notin
      by (simp add: divide_inverse mult.commute) 
    show "u \<in> Rep_preal R" by (rule u) 
    show "x = x / u * u" using upos 
      by (simp add: divide_inverse mult.commute) 
  qed
qed

lemma subset_inverse_mult: 
     "Rep_preal 1 \<subseteq> Rep_preal(inverse r * r)"
  by (force simp: Rep_preal_one mem_Rep_preal_inverse_iff mem_Rep_preal_mult_iff dest: subset_inverse_mult_lemma)

lemma inverse_mult_subset: "Rep_preal(inverse r * r) \<subseteq> Rep_preal 1"
  proof -
  have "0 < u * v" if "v \<in> Rep_preal r" "0 < u" "u < t" for u v t :: rat
    using that by (simp add: zero_less_mult_iff preal_imp_pos [OF cut_Rep_preal]) 
  moreover have "t * q < 1"
    if "q \<in> Rep_preal r" "0 < t" "t < y" "inverse y \<notin> Rep_preal r"
    for t q y :: rat
  proof -
    have "q < inverse y"
      using not_in_Rep_preal_ub that by auto 
    hence "t * q < t/y" 
      using that by (simp add: divide_inverse mult_less_cancel_left)
    also have "\<dots> \<le> 1" 
      using that by (simp add: pos_divide_le_eq)
    finally show ?thesis .
  qed
  ultimately show ?thesis
    by (auto simp: Rep_preal_one mem_Rep_preal_inverse_iff mem_Rep_preal_mult_iff)
qed 

lemma preal_mult_inverse: "inverse r * r = (1::preal)"
  by (meson Rep_preal_inject inverse_mult_subset subset_antisym subset_inverse_mult)

lemma preal_mult_inverse_right: "r * inverse r = (1::preal)"
  using preal_mult_commute preal_mult_inverse by auto


text\<open>Theorems needing \<open>Gleason9_34\<close>\<close>

lemma Rep_preal_self_subset: "Rep_preal (r) \<subseteq> Rep_preal(r + s)"
proof 
  fix x
  assume x: "x \<in> Rep_preal r"
  obtain y where y: "y \<in> Rep_preal s" and "y > 0"
    using Rep_preal preal_nonempty by blast
  have ry: "x+y \<in> Rep_preal(r + s)" using x y
    by (auto simp: mem_Rep_preal_add_iff)
  then show "x \<in> Rep_preal(r + s)"
    by (meson \<open>0 < y\<close> add_less_same_cancel1 not_in_Rep_preal_ub order.asym preal_imp_pos [OF cut_Rep_preal x])
qed

lemma Rep_preal_sum_not_subset: "~ Rep_preal (r + s) \<subseteq> Rep_preal(r)"
proof -
  obtain y where y: "y \<in> Rep_preal s" and "y > 0"
    using Rep_preal preal_nonempty by blast
  obtain x where "x \<in> Rep_preal r" and notin: "x + y \<notin> Rep_preal r"
    using Dedekind_Real.Rep_preal Gleason9_34 \<open>0 < y\<close> by blast 
  then have "x + y \<in> Rep_preal (r + s)" using y
    by (auto simp: mem_Rep_preal_add_iff)
  thus ?thesis using notin by blast
qed

text\<open>at last, Gleason prop. 9-3.5(iii) page 123\<close>
proposition preal_self_less_add_left: "(r::preal) < r + s"
  by (meson Rep_preal_sum_not_subset not_less preal_le_def)


subsection\<open>Subtraction for Positive Reals\<close>

text\<open>gleason prop. 9-3.5(iv), page 123: proving \<^prop>\<open>a < b \<Longrightarrow> \<exists>d. a + d = b\<close>. 
We define the claimed \<^term>\<open>D\<close> and show that it is a positive real\<close>

lemma mem_diff_set:
  assumes "r < s"
  shows "cut (diff_set (Rep_preal s) (Rep_preal r))"
proof -
  obtain p where "Rep_preal r \<subseteq> Rep_preal s" "p \<in> Rep_preal s" "p \<notin> Rep_preal r"
    using assms unfolding preal_less_def by auto
  then have "{} \<subset> diff_set (Rep_preal s) (Rep_preal r)"
    apply (simp add: diff_set_def psubset_eq)
    by (metis cut_Rep_preal add_eq_exists less_add_same_cancel1 preal_exists_greater preal_imp_pos)
  moreover
  obtain q where "q > 0" "q \<notin> Rep_preal s"
    using Rep_preal_exists_bound by blast
  then have qnot: "q \<notin> diff_set (Rep_preal s) (Rep_preal r)"
    by (auto simp: diff_set_def dest: cut_Rep_preal [THEN preal_downwards_closed])
  moreover have "diff_set (Rep_preal s) (Rep_preal r) \<subset> {0<..}" (is "?lhs < ?rhs")
    using \<open>0 < q\<close> diff_set_def qnot by blast
  moreover have "z \<in> diff_set (Rep_preal s) (Rep_preal r)"
    if u: "u \<in> diff_set (Rep_preal s) (Rep_preal r)" and "0 < z" "z < u" for u z
    using u that less_trans Rep_preal unfolding diff_set_def Dedekind_Real.cut_def by auto
  moreover have "\<exists>u \<in> diff_set (Rep_preal s) (Rep_preal r). y < u"
    if y: "y \<in> diff_set (Rep_preal s) (Rep_preal r)" for y
  proof -
    obtain a b where "0 < a" "0 < b" "a \<notin> Rep_preal r" "a + y + b \<in> Rep_preal s"
      using y
      by (simp add: diff_set_def) (metis cut_Rep_preal add_eq_exists less_add_same_cancel1 preal_exists_greater) 
    then have "a + (y + b) \<in> Rep_preal s"
      by (simp add: add.assoc)
    then have "y + b \<in> diff_set (Rep_preal s) (Rep_preal r)"
      using \<open>0 < a\<close> \<open>0 < b\<close> \<open>a \<notin> Rep_preal r\<close> y
      by (auto simp: diff_set_def)
    then show ?thesis
      using \<open>0 < b\<close> less_add_same_cancel1 by blast
  qed
  ultimately show ?thesis
    by (simp add: Dedekind_Real.cut_def)
qed

lemma mem_Rep_preal_diff_iff:
  "r < s \<Longrightarrow>
       (z \<in> Rep_preal (s - r)) \<longleftrightarrow> 
       (\<exists>x. 0 < x \<and> 0 < z \<and> x \<notin> Rep_preal r \<and> x + z \<in> Rep_preal s)"
  apply (simp add: preal_diff_def mem_diff_set Rep_preal)
  apply (force simp: diff_set_def) 
  done

proposition less_add_left:
  fixes r::preal 
  assumes "r < s"
  shows "r + (s-r) = s"
proof -
  have "a + b \<in> Rep_preal s"
    if "a \<in> Rep_preal r" "c + b \<in> Rep_preal s" "c \<notin> Rep_preal r"
    and "0 < b" "0 < c" for a b c
    by (meson cut_Rep_preal add_less_imp_less_right add_pos_pos not_in_Rep_preal_ub preal_downwards_closed preal_imp_pos that)
  then have "r + (s-r) \<le> s"
    using assms mem_Rep_preal_add_iff mem_Rep_preal_diff_iff preal_le_def by auto
  have "x \<in> Rep_preal (r + (s - r))" if "x \<in> Rep_preal s" for x
  proof (cases "x \<in> Rep_preal r")
    case True
    then show ?thesis
      using Rep_preal_self_subset by blast
  next
    case False
    have "\<exists>u v z. 0 < v \<and> 0 < z \<and> u \<in> Rep_preal r \<and> z \<notin> Rep_preal r \<and> z + v \<in> Rep_preal s \<and> x = u + v"
      if x: "x \<in> Rep_preal s"
    proof -
      have xpos: "x > 0"
        using Rep_preal preal_imp_pos that by blast 
      obtain e where epos: "0 < e" and xe: "x + e \<in> Rep_preal s"
        by (metis cut_Rep_preal x add_eq_exists less_add_same_cancel1 preal_exists_greater)
      from  Gleason9_34 [OF cut_Rep_preal epos]
      obtain u where r: "u \<in> Rep_preal r" and notin: "u + e \<notin> Rep_preal r" ..
      with x False xpos have rless: "u < x" by (blast intro: not_in_Rep_preal_ub)
      from add_eq_exists [of u x]
      obtain y where eq: "x = u+y" by auto
      show ?thesis 
      proof (intro exI conjI)
        show "u + e \<notin> Rep_preal r" by (rule notin)
        show "u + e + y \<in> Rep_preal s" using xe eq by (simp add: ac_simps)
        show "0 < u + e" 
          using epos preal_imp_pos [OF cut_Rep_preal r] by simp
      qed (use r rless eq in auto)
    qed
    then show ?thesis
      using assms mem_Rep_preal_add_iff mem_Rep_preal_diff_iff that by blast
  qed
  then have "s \<le> r + (s-r)"
    by (auto simp: preal_le_def)
  then show ?thesis
    by (simp add: \<open>r + (s - r) \<le> s\<close> antisym)
qed

lemma preal_add_less2_mono1: "r < (s::preal) \<Longrightarrow> r + t < s + t"
  by (metis add.assoc add.commute less_add_left preal_self_less_add_left)

lemma preal_add_less2_mono2: "r < (s::preal) \<Longrightarrow> t + r < t + s"
  by (auto intro: preal_add_less2_mono1 simp add: preal_add_commute [of t])

lemma preal_add_right_less_cancel: "r + t < s + t \<Longrightarrow> r < (s::preal)"
  by (metis linorder_cases order.asym preal_add_less2_mono1)

lemma preal_add_left_less_cancel: "t + r < t + s \<Longrightarrow> r < (s::preal)"
  by (auto elim: preal_add_right_less_cancel simp add: preal_add_commute [of t])

lemma preal_add_less_cancel_left [simp]: "(t + (r::preal) < t + s) \<longleftrightarrow> (r < s)"
  by (blast intro: preal_add_less2_mono2 preal_add_left_less_cancel)

lemma preal_add_less_cancel_right [simp]: "((r::preal) + t < s + t) = (r < s)"
  using preal_add_less_cancel_left [symmetric, of r s t] by (simp add: ac_simps)

lemma preal_add_le_cancel_left [simp]: "(t + (r::preal) \<le> t + s) = (r \<le> s)"
  by (simp add: linorder_not_less [symmetric]) 

lemma preal_add_le_cancel_right [simp]: "((r::preal) + t \<le> s + t) = (r \<le> s)"
  using preal_add_le_cancel_left [symmetric, of r s t] by (simp add: ac_simps)

lemma preal_add_right_cancel: "(r::preal) + t = s + t \<Longrightarrow> r = s"
  by (metis less_irrefl linorder_cases preal_add_less_cancel_right)

lemma preal_add_left_cancel: "c + a = c + b \<Longrightarrow> a = (b::preal)"
  by (auto intro: preal_add_right_cancel simp add: preal_add_commute)

instance preal :: linordered_ab_semigroup_add
proof
  fix a b c :: preal
  show "a \<le> b \<Longrightarrow> c + a \<le> c + b" by (simp only: preal_add_le_cancel_left)
qed


subsection\<open>Completeness of type \<^typ>\<open>preal\<close>\<close>

text\<open>Prove that supremum is a cut\<close>

text\<open>Part 1 of Dedekind sections definition\<close>

lemma preal_sup:
  assumes le: "\<And>X. X \<in> P \<Longrightarrow> X \<le> Y" and "P \<noteq> {}" 
  shows "cut (\<Union>X \<in> P. Rep_preal(X))"
proof -
  have "{} \<subset> (\<Union>X \<in> P. Rep_preal(X))"
    using \<open>P \<noteq> {}\<close> mem_Rep_preal_Ex by fastforce
  moreover
  obtain q where "q > 0" and "q \<notin> (\<Union>X \<in> P. Rep_preal(X))"
    using Rep_preal_exists_bound [of Y] le by (auto simp: preal_le_def)
  then have "(\<Union>X \<in> P. Rep_preal(X)) \<subset> {0<..}"
    using cut_Rep_preal preal_imp_pos by force
  moreover
  have "\<And>u z. \<lbrakk>u \<in> (\<Union>X \<in> P. Rep_preal(X)); 0 < z; z < u\<rbrakk> \<Longrightarrow> z \<in> (\<Union>X \<in> P. Rep_preal(X))"
    by (auto elim: cut_Rep_preal [THEN preal_downwards_closed])
  moreover
  have "\<And>y. y \<in> (\<Union>X \<in> P. Rep_preal(X)) \<Longrightarrow> \<exists>u \<in> (\<Union>X \<in> P. Rep_preal(X)). y < u"
    by (blast dest: cut_Rep_preal [THEN preal_exists_greater])
  ultimately show ?thesis
    by (simp add: Dedekind_Real.cut_def)
qed

lemma preal_psup_le:
     "\<lbrakk>\<And>X. X \<in> P \<Longrightarrow> X \<le> Y;  x \<in> P\<rbrakk> \<Longrightarrow> x \<le> psup P"
  using preal_sup [of P Y] unfolding preal_le_def psup_def by fastforce 

lemma psup_le_ub: "\<lbrakk>\<And>X. X \<in> P \<Longrightarrow> X \<le> Y; P \<noteq> {}\<rbrakk> \<Longrightarrow> psup P \<le> Y"
  using preal_sup [of P Y] by (simp add: SUP_least preal_le_def psup_def) 

text\<open>Supremum property\<close>
proposition preal_complete:
  assumes le: "\<And>X. X \<in> P \<Longrightarrow> X \<le> Y" and "P \<noteq> {}" 
  shows "(\<exists>X \<in> P. Z < X) \<longleftrightarrow> (Z < psup P)" (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs
    using preal_sup [OF assms] preal_less_def psup_def by auto
next
  assume ?rhs
  then show ?lhs
    by (meson \<open>P \<noteq> {}\<close> not_less psup_le_ub) 
qed

subsection \<open>Defining the Reals from the Positive Reals\<close>

text \<open>Here we do quotients the old-fashioned way\<close>

definition
  realrel   ::  "((preal * preal) * (preal * preal)) set" where
  "realrel = {p. \<exists>x1 y1 x2 y2. p = ((x1,y1),(x2,y2)) \<and> x1+y2 = x2+y1}"

definition "Real = UNIV//realrel"

typedef real = Real
  morphisms Rep_Real Abs_Real
  unfolding Real_def by (auto simp: quotient_def)

text \<open>This doesn't involve the overloaded "real" function: users don't see it\<close>
definition
  real_of_preal :: "preal \<Rightarrow> real" where
  "real_of_preal m = Abs_Real (realrel `` {(m + 1, 1)})"

instantiation real :: "{zero, one, plus, minus, uminus, times, inverse, ord, abs, sgn}"
begin

definition
  real_zero_def: "0 = Abs_Real(realrel``{(1, 1)})"

definition
  real_one_def: "1 = Abs_Real(realrel``{(1 + 1, 1)})"

definition
  real_add_def: "z + w =
       the_elem (\<Union>(x,y) \<in> Rep_Real(z). \<Union>(u,v) \<in> Rep_Real(w).
                 { Abs_Real(realrel``{(x+u, y+v)}) })"

definition
  real_minus_def: "- r =  the_elem (\<Union>(x,y) \<in> Rep_Real(r). { Abs_Real(realrel``{(y,x)}) })"

definition
  real_diff_def: "r - (s::real) = r + - s"

definition
  real_mult_def:
    "z * w =
       the_elem (\<Union>(x,y) \<in> Rep_Real(z). \<Union>(u,v) \<in> Rep_Real(w).
                 { Abs_Real(realrel``{(x*u + y*v, x*v + y*u)}) })"

definition
  real_inverse_def: "inverse (r::real) = (THE s. (r = 0 \<and> s = 0) \<or> s * r = 1)"

definition
  real_divide_def: "r div (s::real) = r * inverse s"

definition
  real_le_def: "z \<le> (w::real) \<longleftrightarrow>
    (\<exists>x y u v. x+v \<le> u+y \<and> (x,y) \<in> Rep_Real z \<and> (u,v) \<in> Rep_Real w)"

definition
  real_less_def: "x < (y::real) \<longleftrightarrow> x \<le> y \<and> x \<noteq> y"

definition
  real_abs_def: "\<bar>r::real\<bar> = (if r < 0 then - r else r)"

definition
  real_sgn_def: "sgn (x::real) = (if x=0 then 0 else if 0<x then 1 else - 1)"

instance ..

end

subsection \<open>Equivalence relation over positive reals\<close>

lemma realrel_iff [simp]: "(((x1,y1),(x2,y2)) \<in> realrel) = (x1 + y2 = x2 + y1)"
  by (simp add: realrel_def)

lemma preal_trans_lemma:
  assumes "x + y1 = x1 + y" and "x + y2 = x2 + y"
  shows "x1 + y2 = x2 + (y1::preal)"
  by (metis add.left_commute assms preal_add_left_cancel)

lemma equiv_realrel: "equiv UNIV realrel"
  by (auto simp: equiv_def refl_on_def sym_def trans_def realrel_def intro: dest: preal_trans_lemma)

text\<open>Reduces equality of equivalence classes to the \<^term>\<open>realrel\<close> relation:
  \<^term>\<open>(realrel `` {x} = realrel `` {y}) = ((x,y) \<in> realrel)\<close>\<close>
lemmas equiv_realrel_iff [simp] = 
       eq_equiv_class_iff [OF equiv_realrel UNIV_I UNIV_I]

lemma realrel_in_real [simp]: "realrel``{(x,y)} \<in> Real"
  by (simp add: Real_def realrel_def quotient_def, blast)

declare Abs_Real_inject [simp] Abs_Real_inverse [simp]


text\<open>Case analysis on the representation of a real number as an equivalence
      class of pairs of positive reals.\<close>
lemma eq_Abs_Real [case_names Abs_Real, cases type: real]: 
     "(\<And>x y. z = Abs_Real(realrel``{(x,y)}) \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis Rep_Real_inverse prod.exhaust  Rep_Real [of z, unfolded Real_def, THEN quotientE])

subsection \<open>Addition and Subtraction\<close>

lemma real_add:
     "Abs_Real (realrel``{(x,y)}) + Abs_Real (realrel``{(u,v)}) =
      Abs_Real (realrel``{(x+u, y+v)})"
proof -
  have "(\<lambda>z w. (\<lambda>(x,y). (\<lambda>(u,v). {Abs_Real (realrel `` {(x+u, y+v)})}) w) z)
        respects2 realrel"
  by (clarsimp simp: congruent2_def) (metis add.left_commute preal_add_assoc)
  thus ?thesis
    by (simp add: real_add_def UN_UN_split_split_eq UN_equiv_class2 [OF equiv_realrel equiv_realrel])
qed

lemma real_minus: "- Abs_Real(realrel``{(x,y)}) = Abs_Real(realrel `` {(y,x)})"
proof -
  have "(\<lambda>(x,y). {Abs_Real (realrel``{(y,x)})}) respects realrel"
    by (auto simp: congruent_def add.commute) 
  thus ?thesis
    by (simp add: real_minus_def UN_equiv_class [OF equiv_realrel])
qed

instance real :: ab_group_add
proof
  fix x y z :: real
  show "(x + y) + z = x + (y + z)"
    by (cases x, cases y, cases z, simp add: real_add add.assoc)
  show "x + y = y + x"
    by (cases x, cases y, simp add: real_add add.commute)
  show "0 + x = x"
    by (cases x, simp add: real_add real_zero_def ac_simps)
  show "- x + x = 0"
    by (cases x, simp add: real_minus real_add real_zero_def add.commute)
  show "x - y = x + - y"
    by (simp add: real_diff_def)
qed


subsection \<open>Multiplication\<close>

lemma real_mult_congruent2_lemma:
     "!!(x1::preal). \<lbrakk>x1 + y2 = x2 + y1\<rbrakk> \<Longrightarrow>
          x * x1 + y * y1 + (x * y2 + y * x2) =
          x * x2 + y * y2 + (x * y1 + y * x1)"
  by (metis (no_types, opaque_lifting) add.left_commute preal_add_commute preal_add_mult_distrib2)

lemma real_mult_congruent2:
  "(\<lambda>p1 p2.
        (\<lambda>(x1,y1). (\<lambda>(x2,y2). 
          { Abs_Real (realrel``{(x1*x2 + y1*y2, x1*y2+y1*x2)}) }) p2) p1)
     respects2 realrel"
  apply (rule congruent2_commuteI [OF equiv_realrel])
  by (auto simp: mult.commute add.commute combine_common_factor preal_add_assoc preal_add_commute)

lemma real_mult:
  "Abs_Real((realrel``{(x1,y1)})) * Abs_Real((realrel``{(x2,y2)})) =
   Abs_Real(realrel `` {(x1*x2+y1*y2,x1*y2+y1*x2)})"
  by (simp add: real_mult_def UN_UN_split_split_eq
      UN_equiv_class2 [OF equiv_realrel equiv_realrel real_mult_congruent2])

lemma real_mult_commute: "(z::real) * w = w * z"
by (cases z, cases w, simp add: real_mult ac_simps)

lemma real_mult_assoc: "((z1::real) * z2) * z3 = z1 * (z2 * z3)"
  by (cases z1, cases z2, cases z3) (simp add: real_mult algebra_simps)

lemma real_mult_1: "(1::real) * z = z"
  by (cases z) (simp add: real_mult real_one_def algebra_simps)

lemma real_add_mult_distrib: "((z1::real) + z2) * w = (z1 * w) + (z2 * w)"
  by (cases z1, cases z2, cases w) (simp add: real_add real_mult algebra_simps)

text\<open>one and zero are distinct\<close>
lemma real_zero_not_eq_one: "0 \<noteq> (1::real)"
proof -
  have "(1::preal) < 1 + 1"
    by (simp add: preal_self_less_add_left)
  then show ?thesis
    by (simp add: real_zero_def real_one_def neq_iff)
qed

instance real :: comm_ring_1
proof
  fix x y z :: real
  show "(x * y) * z = x * (y * z)" by (rule real_mult_assoc)
  show "x * y = y * x" by (rule real_mult_commute)
  show "1 * x = x" by (rule real_mult_1)
  show "(x + y) * z = x * z + y * z" by (rule real_add_mult_distrib)
  show "0 \<noteq> (1::real)" by (rule real_zero_not_eq_one)
qed

subsection \<open>Inverse and Division\<close>

lemma real_zero_iff: "Abs_Real (realrel `` {(x, x)}) = 0"
  by (simp add: real_zero_def add.commute)

lemma real_mult_inverse_left_ex:
  assumes "x \<noteq> 0" obtains y::real where "y*x = 1"
proof (cases x)
  case (Abs_Real u v)
  show ?thesis
  proof (cases u v rule: linorder_cases)
    case less
    then have "v * inverse (v - u) = 1 + u * inverse (v - u)"
      using less_add_left [of u v]
      by (metis preal_add_commute preal_add_mult_distrib preal_mult_inverse_right)
    then have "Abs_Real (realrel``{(1, inverse (v-u) + 1)}) * x - 1 = 0"
      by (simp add: Abs_Real real_mult preal_mult_inverse_right real_one_def) (simp add: algebra_simps)
    with that show thesis by auto
  next
    case equal
    then show ?thesis
      using Abs_Real assms real_zero_iff by blast
  next
    case greater
    then have "u * inverse (u - v) = 1 + v * inverse (u - v)"
      using less_add_left [of v u] by (metis add.commute distrib_right preal_mult_inverse_right)
    then have "Abs_Real (realrel``{(inverse (u-v) + 1, 1)}) * x - 1 = 0"
      by (simp add: Abs_Real real_mult preal_mult_inverse_right real_one_def) (simp add: algebra_simps)
    with that show thesis by auto
  qed
qed


lemma real_mult_inverse_left:
  fixes x :: real
  assumes "x \<noteq> 0" shows "inverse x * x = 1"
proof -
  obtain y where "y*x = 1"
    using assms real_mult_inverse_left_ex by blast
  then have "(THE s. s * x = 1) * x = 1"
  proof (rule theI)
    show "y' = y" if "y' * x = 1" for y'
      by (metis \<open>y * x = 1\<close> mult.left_commute mult.right_neutral that) 
  qed
  then show ?thesis
    using assms real_inverse_def by auto
qed


subsection\<open>The Real Numbers form a Field\<close>

instance real :: field
proof
  fix x y z :: real
  show "x \<noteq> 0 \<Longrightarrow> inverse x * x = 1" by (rule real_mult_inverse_left)
  show "x / y = x * inverse y" by (simp add: real_divide_def)
  show "inverse 0 = (0::real)" by (simp add: real_inverse_def)
qed


subsection\<open>The \<open>\<le>\<close> Ordering\<close>

lemma real_le_refl: "w \<le> (w::real)"
  by (cases w, force simp: real_le_def)

text\<open>The arithmetic decision procedure is not set up for type preal.
  This lemma is currently unused, but it could simplify the proofs of the
  following two lemmas.\<close>
lemma preal_eq_le_imp_le:
  assumes eq: "a+b = c+d" and le: "c \<le> a"
  shows "b \<le> (d::preal)"
proof -
  from le have "c+d \<le> a+d" by simp
  hence "a+b \<le> a+d" by (simp add: eq)
  thus "b \<le> d" by simp
qed

lemma real_le_lemma:
  assumes l: "u1 + v2 \<le> u2 + v1"
    and "x1 + v1 = u1 + y1"
    and "x2 + v2 = u2 + y2"
  shows "x1 + y2 \<le> x2 + (y1::preal)"
proof -
  have "(x1+v1) + (u2+y2) = (u1+y1) + (x2+v2)" by (simp add: assms)
  hence "(x1+y2) + (u2+v1) = (x2+y1) + (u1+v2)" by (simp add: ac_simps)
  also have "\<dots> \<le> (x2+y1) + (u2+v1)" by (simp add: assms)
  finally show ?thesis by simp
qed

lemma real_le: 
  "Abs_Real(realrel``{(x1,y1)}) \<le> Abs_Real(realrel``{(x2,y2)})  \<longleftrightarrow>  x1 + y2 \<le> x2 + y1"
  unfolding real_le_def by (auto intro: real_le_lemma)

lemma real_le_antisym: "\<lbrakk>z \<le> w; w \<le> z\<rbrakk> \<Longrightarrow> z = (w::real)"
  by (cases z, cases w, simp add: real_le)

lemma real_trans_lemma:
  assumes "x + v \<le> u + y"
    and "u + v' \<le> u' + v"
    and "x2 + v2 = u2 + y2"
  shows "x + v' \<le> u' + (y::preal)"
proof -
  have "(x+v') + (u+v) = (x+v) + (u+v')" by (simp add: ac_simps)
  also have "\<dots> \<le> (u+y) + (u+v')" by (simp add: assms)
  also have "\<dots> \<le> (u+y) + (u'+v)" by (simp add: assms)
  also have "\<dots> = (u'+y) + (u+v)"  by (simp add: ac_simps)
  finally show ?thesis by simp
qed

lemma real_le_trans: "\<lbrakk>i \<le> j; j \<le> k\<rbrakk> \<Longrightarrow> i \<le> (k::real)"
  by (cases i, cases j, cases k) (auto simp: real_le intro: real_trans_lemma)

instance real :: order
proof
  show "u < v \<longleftrightarrow> u \<le> v \<and> \<not> v \<le> u" for u v::real
    by (auto simp: real_less_def intro: real_le_antisym)
qed (auto intro: real_le_refl real_le_trans real_le_antisym)

instance real :: linorder
proof
  show "x \<le> y \<or> y \<le> x" for x y :: real
    by (meson eq_refl le_cases real_le_def)
qed

instantiation real :: distrib_lattice
begin

definition
  "(inf :: real \<Rightarrow> real \<Rightarrow> real) = min"

definition
  "(sup :: real \<Rightarrow> real \<Rightarrow> real) = max"

instance
  by standard (auto simp: inf_real_def sup_real_def max_min_distrib2)

end

subsection\<open>The Reals Form an Ordered Field\<close>

lemma real_le_eq_diff: "(x \<le> y) \<longleftrightarrow> (x-y \<le> (0::real))"
  by (cases x, cases y) (simp add: real_le real_zero_def real_diff_def real_add real_minus preal_add_commute)

lemma real_add_left_mono: 
  assumes le: "x \<le> y" shows "z + x \<le> z + (y::real)"
proof -
  have "z + x - (z + y) = (z + -z) + (x - y)" 
    by (simp add: algebra_simps) 
  with le show ?thesis 
    by (simp add: real_le_eq_diff[of x] real_le_eq_diff[of "z+x"])
qed

lemma real_sum_gt_zero_less: "(0 < s + (-w::real)) \<Longrightarrow> (w < s)"
  by (simp add: linorder_not_le [symmetric] real_le_eq_diff [of s])

lemma real_less_sum_gt_zero: "(w < s) \<Longrightarrow> (0 < s + (-w::real))"
  by (simp add: linorder_not_le [symmetric] real_le_eq_diff [of s])

lemma real_mult_order: 
  fixes x y::real
  assumes "0 < x" "0 < y"
  shows "0 < x * y"
  proof (cases x, cases y)
  show "0 < x * y"
    if x: "x = Abs_Real (Dedekind_Real.realrel `` {(x1, x2)})"
      and y: "y = Abs_Real (Dedekind_Real.realrel `` {(y1, y2)})"
    for x1 x2 y1 y2
  proof -
    have "x2 < x1" "y2 < y1"
      using assms not_le real_zero_def real_le x y
      by (metis preal_add_le_cancel_left real_zero_iff)+
    then obtain xd yd where "x1 = x2 + xd" "y1 = y2 + yd"
      using less_add_left by metis
    then have "\<not> (x * y \<le> 0)"
      apply (simp add: x y real_mult real_zero_def real_le)
      apply (simp add: not_le algebra_simps preal_self_less_add_left)
      done
    then show ?thesis
      by auto
  qed
qed

lemma real_mult_less_mono2: "\<lbrakk>(0::real) < z; x < y\<rbrakk> \<Longrightarrow> z * x < z * y"
  by (metis add_uminus_conv_diff real_less_sum_gt_zero real_mult_order real_sum_gt_zero_less right_diff_distrib')


instance real :: linordered_field
proof
  fix x y z :: real
  show "x \<le> y \<Longrightarrow> z + x \<le> z + y" by (rule real_add_left_mono)
  show "\<bar>x\<bar> = (if x < 0 then -x else x)" by (simp only: real_abs_def)
  show "sgn x = (if x=0 then 0 else if 0<x then 1 else - 1)"
    by (simp only: real_sgn_def)
  show "z * x < z * y" if "x < y" "0 < z"
    by (simp add: real_mult_less_mono2 that)
qed


subsection \<open>Completeness of the reals\<close>

text\<open>The function \<^term>\<open>real_of_preal\<close> requires many proofs, but it seems
to be essential for proving completeness of the reals from that of the
positive reals.\<close>

lemma real_of_preal_add:
  "real_of_preal ((x::preal) + y) = real_of_preal x + real_of_preal y"
  by (simp add: real_of_preal_def real_add algebra_simps)

lemma real_of_preal_mult:
  "real_of_preal ((x::preal) * y) = real_of_preal x * real_of_preal y"
  by (simp add: real_of_preal_def real_mult algebra_simps)

text\<open>Gleason prop 9-4.4 p 127\<close>
lemma real_of_preal_trichotomy:
  "\<exists>m. (x::real) = real_of_preal m \<or> x = 0 \<or> x = -(real_of_preal m)"
proof (cases x)
  case (Abs_Real u v)
  show ?thesis
  proof (cases u v rule: linorder_cases)
    case less
    then show ?thesis
      using less_add_left
      apply (simp add: Abs_Real real_of_preal_def real_minus real_zero_def)
      by (metis preal_add_assoc preal_add_commute)      
  next
    case equal
    then show ?thesis
      using Abs_Real real_zero_iff by blast
  next
    case greater
    then show ?thesis
      using less_add_left
      apply (simp add: Abs_Real real_of_preal_def real_minus real_zero_def)
      by (metis preal_add_assoc preal_add_commute)      
  qed
qed

lemma real_of_preal_less_iff [simp]:
  "(real_of_preal m1 < real_of_preal m2) = (m1 < m2)"
  by (metis not_less preal_add_less_cancel_right real_le real_of_preal_def)

lemma real_of_preal_le_iff [simp]:
  "(real_of_preal m1 \<le> real_of_preal m2) = (m1 \<le> m2)"
  by (simp add: linorder_not_less [symmetric])

lemma real_of_preal_zero_less [simp]: "0 < real_of_preal m"
  by (metis less_add_same_cancel2 preal_self_less_add_left real_of_preal_add real_of_preal_less_iff)


subsection\<open>Theorems About the Ordering\<close>

lemma real_gt_zero_preal_Ex: "(0 < x) \<longleftrightarrow> (\<exists>y. x = real_of_preal y)"
  using order.asym real_of_preal_trichotomy by fastforce

subsection \<open>Completeness of Positive Reals\<close>

text \<open>
  Supremum property for the set of positive reals

  Let \<open>P\<close> be a non-empty set of positive reals, with an upper
  bound \<open>y\<close>.  Then \<open>P\<close> has a least upper bound
  (written \<open>S\<close>).

  FIXME: Can the premise be weakened to \<open>\<forall>x \<in> P. x\<le> y\<close>?
\<close>

lemma posreal_complete:
  assumes positive_P: "\<forall>x \<in> P. (0::real) < x"
    and not_empty_P: "\<exists>x. x \<in> P"
    and upper_bound_Ex: "\<exists>y. \<forall>x \<in> P. x<y"
  shows "\<exists>s. \<forall>y. (\<exists>x \<in> P. y < x) = (y < s)"
proof (rule exI, rule allI)
  fix y
  let ?pP = "{w. real_of_preal w \<in> P}"

  show "(\<exists>x\<in>P. y < x) = (y < real_of_preal (psup ?pP))"
  proof (cases "0 < y")
    assume neg_y: "\<not> 0 < y"
    show ?thesis
    proof
      assume "\<exists>x\<in>P. y < x"
      thus "y < real_of_preal (psup ?pP)"
        by (metis dual_order.strict_trans neg_y not_less_iff_gr_or_eq real_of_preal_zero_less) 
    next
      assume "y < real_of_preal (psup ?pP)"
      obtain "x" where x_in_P: "x \<in> P" using not_empty_P ..
      thus "\<exists>x \<in> P. y < x" using x_in_P
        using neg_y not_less_iff_gr_or_eq positive_P by fastforce 
    qed
  next
    assume pos_y: "0 < y"
    then obtain py where y_is_py: "y = real_of_preal py"
      by (auto simp: real_gt_zero_preal_Ex)

    obtain a where "a \<in> P" using not_empty_P ..
    with positive_P have a_pos: "0 < a" ..
    then obtain pa where "a = real_of_preal pa"
      by (auto simp: real_gt_zero_preal_Ex)
    hence "pa \<in> ?pP" using \<open>a \<in> P\<close> by auto
    hence pP_not_empty: "?pP \<noteq> {}" by auto

    obtain sup where sup: "\<forall>x \<in> P. x < sup"
      using upper_bound_Ex ..
    from this and \<open>a \<in> P\<close> have "a < sup" ..
    hence "0 < sup" using a_pos by arith
    then obtain possup where "sup = real_of_preal possup"
      by (auto simp: real_gt_zero_preal_Ex)
    hence "\<forall>X \<in> ?pP. X \<le> possup"
      using sup by auto
    with pP_not_empty have psup: "\<And>Z. (\<exists>X \<in> ?pP. Z < X) = (Z < psup ?pP)"
      by (meson preal_complete)
    show ?thesis
    proof
      assume "\<exists>x \<in> P. y < x"
      then obtain x where x_in_P: "x \<in> P" and y_less_x: "y < x" ..
      hence "0 < x" using pos_y by arith
      then obtain px where x_is_px: "x = real_of_preal px"
        by (auto simp: real_gt_zero_preal_Ex)

      have py_less_X: "\<exists>X \<in> ?pP. py < X"
      proof
        show "py < px" using y_is_py and x_is_px and y_less_x
          by simp
        show "px \<in> ?pP" using x_in_P and x_is_px by simp
      qed

      have "(\<exists>X \<in> ?pP. py < X) \<Longrightarrow> (py < psup ?pP)"
        using psup by simp
      hence "py < psup ?pP" using py_less_X by simp
      thus "y < real_of_preal (psup {w. real_of_preal w \<in> P})"
        using y_is_py and pos_y by simp
    next
      assume y_less_psup: "y < real_of_preal (psup ?pP)"

      hence "py < psup ?pP" using y_is_py
        by simp
      then obtain "X" where py_less_X: "py < X" and X_in_pP: "X \<in> ?pP"
        using psup by auto
      then obtain x where x_is_X: "x = real_of_preal X"
        by (simp add: real_gt_zero_preal_Ex)
      hence "y < x" using py_less_X and y_is_py
        by simp
      moreover have "x \<in> P" 
        using x_is_X and X_in_pP by simp
      ultimately show "\<exists> x \<in> P. y < x" ..
    qed
  qed
qed


subsection \<open>Completeness\<close>

lemma reals_complete:
  fixes S :: "real set"
  assumes notempty_S: "\<exists>X. X \<in> S"
    and exists_Ub: "bdd_above S"
  shows "\<exists>x. (\<forall>s\<in>S. s \<le> x) \<and> (\<forall>y. (\<forall>s\<in>S. s \<le> y) \<longrightarrow> x \<le> y)"
proof -
  obtain X where X_in_S: "X \<in> S" using notempty_S ..
  obtain Y where Y_isUb: "\<forall>s\<in>S. s \<le> Y"
    using exists_Ub by (auto simp: bdd_above_def)
  let ?SHIFT = "{z. \<exists>x \<in>S. z = x + (-X) + 1} \<inter> {x. 0 < x}"

  {
    fix x
    assume S_le_x: "\<forall>s\<in>S. s \<le> x"
    {
      fix s
      assume "s \<in> {z. \<exists>x\<in>S. z = x + - X + 1}"
      hence "\<exists> x \<in> S. s = x + -X + 1" ..
      then obtain x1 where x1: "x1 \<in> S" "s = x1 + (-X) + 1" ..
      then have "x1 \<le> x" using S_le_x by simp
      with x1 have "s \<le> x + - X + 1" by arith
    }
    then have "\<forall>s\<in>?SHIFT. s \<le> x + (-X) + 1"
      by auto
  } note S_Ub_is_SHIFT_Ub = this

  have *: "\<forall>s\<in>?SHIFT. s \<le> Y + (-X) + 1" using Y_isUb by (rule S_Ub_is_SHIFT_Ub)
  have "\<forall>s\<in>?SHIFT. s < Y + (-X) + 2"
  proof
    fix s assume "s\<in>?SHIFT"
    with * have "s \<le> Y + (-X) + 1" by simp
    also have "\<dots> < Y + (-X) + 2" by simp
    finally show "s < Y + (-X) + 2" .
  qed
  moreover have "\<forall>y \<in> ?SHIFT. 0 < y" by auto
  moreover have shifted_not_empty: "\<exists>u. u \<in> ?SHIFT"
    using X_in_S and Y_isUb by auto
  ultimately obtain t where t_is_Lub: "\<forall>y. (\<exists>x\<in>?SHIFT. y < x) = (y < t)"
    using posreal_complete [of ?SHIFT] unfolding bdd_above_def by blast

  show ?thesis
  proof
    show "(\<forall>s\<in>S. s \<le> (t + X + (-1))) \<and> (\<forall>y. (\<forall>s\<in>S. s \<le> y) \<longrightarrow> (t + X + (-1)) \<le> y)"
    proof safe
      fix x
      assume "\<forall>s\<in>S. s \<le> x"
      hence "\<forall>s\<in>?SHIFT. s \<le> x + (-X) + 1"
        using S_Ub_is_SHIFT_Ub by simp
      then have "\<not> x + (-X) + 1 < t"
        by (subst t_is_Lub[rule_format, symmetric]) (simp add: not_less)
      thus "t + X + -1 \<le> x" by arith
    next
      fix y
      assume y_in_S: "y \<in> S"
      obtain "u" where u_in_shift: "u \<in> ?SHIFT" using shifted_not_empty ..
      hence "\<exists> x \<in> S. u = x + - X + 1" by simp
      then obtain "x" where x_and_u: "u = x + - X + 1" ..
      have u_le_t: "u \<le> t"
      proof (rule dense_le)
        fix x assume "x < u" then have "x < t"
          using u_in_shift t_is_Lub by auto
        then show "x \<le> t"  by simp
      qed

      show "y \<le> t + X + -1"
      proof cases
        assume "y \<le> x"
        moreover have "x = u + X + - 1" using x_and_u by arith
        moreover have "u + X + - 1  \<le> t + X + -1" using u_le_t by arith
        ultimately show "y  \<le> t + X + -1" by arith
      next
        assume "~(y \<le> x)"
        hence x_less_y: "x < y" by arith

        have "x + (-X) + 1 \<in> ?SHIFT" using x_and_u and u_in_shift by simp
        hence "0 < x + (-X) + 1" by simp
        hence "0 < y + (-X) + 1" using x_less_y by arith
        hence *: "y + (-X) + 1 \<in> ?SHIFT" using y_in_S by simp
        have "y + (-X) + 1 \<le> t"
        proof (rule dense_le)
          fix x assume "x < y + (-X) + 1" then have "x < t"
            using * t_is_Lub by auto
          then show "x \<le> t"  by simp
        qed
        thus ?thesis by simp
      qed
    qed
  qed
qed

subsection \<open>The Archimedean Property of the Reals\<close>

theorem reals_Archimedean:
  fixes x :: real
  assumes x_pos: "0 < x"
  shows "\<exists>n. inverse (of_nat (Suc n)) < x"
proof (rule ccontr)
  assume contr: "\<not> ?thesis"
  have "\<forall>n. x * of_nat (Suc n) \<le> 1"
  proof
    fix n
    from contr have "x \<le> inverse (of_nat (Suc n))"
      by (simp add: linorder_not_less)
    hence "x \<le> (1 / (of_nat (Suc n)))"
      by (simp add: inverse_eq_divide)
    moreover have "(0::real) \<le> of_nat (Suc n)"
      by (rule of_nat_0_le_iff)
    ultimately have "x * of_nat (Suc n) \<le> (1 / of_nat (Suc n)) * of_nat (Suc n)"
      by (rule mult_right_mono)
    thus "x * of_nat (Suc n) \<le> 1" by (simp del: of_nat_Suc)
  qed
  hence 2: "bdd_above {z. \<exists>n. z = x * (of_nat (Suc n))}"
    by (auto intro!: bdd_aboveI[of _ 1])
  have 1: "\<exists>X. X \<in> {z. \<exists>n. z = x* (of_nat (Suc n))}" by auto
  obtain t where
    upper: "\<And>z. z \<in> {z. \<exists>n. z = x * of_nat (Suc n)} \<Longrightarrow> z \<le> t" and
    least: "\<And>y. (\<And>a. a \<in> {z. \<exists>n. z = x * of_nat (Suc n)} \<Longrightarrow> a \<le> y) \<Longrightarrow> t \<le> y"
    using reals_complete[OF 1 2] by auto

  have "t \<le> t + - x"
  proof (rule least)
    fix a assume a: "a \<in> {z. \<exists>n. z = x * (of_nat (Suc n))}"
    have "\<forall>n::nat. x * of_nat n \<le> t + - x"
    proof
      fix n
      have "x * of_nat (Suc n) \<le> t"
        by (simp add: upper)
      hence  "x * (of_nat n) + x \<le> t"
        by (simp add: distrib_left)
      thus  "x * (of_nat n) \<le> t + - x" by arith
    qed    hence "\<forall>m. x * of_nat (Suc m) \<le> t + - x" by (simp del: of_nat_Suc)
    with a show "a \<le> t + - x"
      by auto
  qed
  thus False using x_pos by arith
qed

text \<open>
  There must be other proofs, e.g. \<open>Suc\<close> of the largest
  integer in the cut representing \<open>x\<close>.
\<close>

lemma reals_Archimedean2: "\<exists>n. (x::real) < of_nat (n::nat)"
proof cases
  assume "x \<le> 0"
  hence "x < of_nat (1::nat)" by simp
  thus ?thesis ..
next
  assume "\<not> x \<le> 0"
  hence x_greater_zero: "0 < x" by simp
  hence "0 < inverse x" by simp
  then obtain n where "inverse (of_nat (Suc n)) < inverse x"
    using reals_Archimedean by blast
  hence "inverse (of_nat (Suc n)) * x < inverse x * x"
    using x_greater_zero by (rule mult_strict_right_mono)
  hence "inverse (of_nat (Suc n)) * x < 1"
    using x_greater_zero by simp
  hence "of_nat (Suc n) * (inverse (of_nat (Suc n)) * x) < of_nat (Suc n) * 1"
    by (rule mult_strict_left_mono) (simp del: of_nat_Suc)
  hence "x < of_nat (Suc n)"
    by (simp add: algebra_simps del: of_nat_Suc)
  thus "\<exists>(n::nat). x < of_nat n" ..
qed

instance real :: archimedean_field
proof
  fix r :: real
  obtain n :: nat where "r < of_nat n"
    using reals_Archimedean2 ..
  then have "r \<le> of_int (int n)"
    by simp
  then show "\<exists>z. r \<le> of_int z" ..
qed

end
