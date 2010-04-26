(*  Title:      Multivariate_Analysis/Vec1.thy
    Author:     Amine Chaieb, University of Cambridge
    Author:     Robert Himmelmann, TU Muenchen
*)

header {* Vectors of size 1, 2, or 3 *}

theory Vec1
imports Topology_Euclidean_Space
begin

text{* Some common special cases.*}

lemma forall_1[simp]: "(\<forall>i::1. P i) \<longleftrightarrow> P 1"
  by (metis num1_eq_iff)

lemma ex_1[simp]: "(\<exists>x::1. P x) \<longleftrightarrow> P 1"
  by auto (metis num1_eq_iff)

lemma exhaust_2:
  fixes x :: 2 shows "x = 1 \<or> x = 2"
proof (induct x)
  case (of_int z)
  then have "0 <= z" and "z < 2" by simp_all
  then have "z = 0 | z = 1" by arith
  then show ?case by auto
qed

lemma forall_2: "(\<forall>i::2. P i) \<longleftrightarrow> P 1 \<and> P 2"
  by (metis exhaust_2)

lemma exhaust_3:
  fixes x :: 3 shows "x = 1 \<or> x = 2 \<or> x = 3"
proof (induct x)
  case (of_int z)
  then have "0 <= z" and "z < 3" by simp_all
  then have "z = 0 \<or> z = 1 \<or> z = 2" by arith
  then show ?case by auto
qed

lemma forall_3: "(\<forall>i::3. P i) \<longleftrightarrow> P 1 \<and> P 2 \<and> P 3"
  by (metis exhaust_3)

lemma UNIV_1 [simp]: "UNIV = {1::1}"
  by (auto simp add: num1_eq_iff)

lemma UNIV_2: "UNIV = {1::2, 2::2}"
  using exhaust_2 by auto

lemma UNIV_3: "UNIV = {1::3, 2::3, 3::3}"
  using exhaust_3 by auto

lemma setsum_1: "setsum f (UNIV::1 set) = f 1"
  unfolding UNIV_1 by simp

lemma setsum_2: "setsum f (UNIV::2 set) = f 1 + f 2"
  unfolding UNIV_2 by simp

lemma setsum_3: "setsum f (UNIV::3 set) = f 1 + f 2 + f 3"
  unfolding UNIV_3 by (simp add: add_ac)

instantiation num1 :: cart_one begin
instance proof
  show "CARD(1) = Suc 0" by auto
qed end

(* "lift" from 'a to 'a^1 and "drop" from 'a^1 to 'a -- FIXME: potential use of transfer *)

abbreviation vec1:: "'a \<Rightarrow> 'a ^ 1" where "vec1 x \<equiv> vec x"

abbreviation dest_vec1:: "'a ^1 \<Rightarrow> 'a"
  where "dest_vec1 x \<equiv> (x$1)"

lemma vec1_component[simp]: "(vec1 x)$1 = x"
  by simp

lemma vec1_dest_vec1: "vec1(dest_vec1 x) = x" "dest_vec1(vec1 y) = y"
  by (simp_all add:  Cart_eq)

declare vec1_dest_vec1(1) [simp]

lemma forall_vec1: "(\<forall>x. P x) \<longleftrightarrow> (\<forall>x. P (vec1 x))"
  by (metis vec1_dest_vec1(1))

lemma exists_vec1: "(\<exists>x. P x) \<longleftrightarrow> (\<exists>x. P(vec1 x))"
  by (metis vec1_dest_vec1(1))

lemma vec1_eq[simp]:  "vec1 x = vec1 y \<longleftrightarrow> x = y"
  by (metis vec1_dest_vec1(2))

lemma dest_vec1_eq[simp]: "dest_vec1 x = dest_vec1 y \<longleftrightarrow> x = y"
  by (metis vec1_dest_vec1(1))

subsection{* The collapse of the general concepts to dimension one. *}

lemma vector_one: "(x::'a ^1) = (\<chi> i. (x$1))"
  by (simp add: Cart_eq)

lemma forall_one: "(\<forall>(x::'a ^1). P x) \<longleftrightarrow> (\<forall>x. P(\<chi> i. x))"
  apply auto
  apply (erule_tac x= "x$1" in allE)
  apply (simp only: vector_one[symmetric])
  done

lemma norm_vector_1: "norm (x :: _^1) = norm (x$1)"
  by (simp add: norm_vector_def)

lemma norm_real: "norm(x::real ^ 1) = abs(x$1)"
  by (simp add: norm_vector_1)

lemma dist_real: "dist(x::real ^ 1) y = abs((x$1) - (y$1))"
  by (auto simp add: norm_real dist_norm)

subsection{* Explicit vector construction from lists. *}

primrec from_nat :: "nat \<Rightarrow> 'a::{monoid_add,one}"
where "from_nat 0 = 0" | "from_nat (Suc n) = 1 + from_nat n"

lemma from_nat [simp]: "from_nat = of_nat"
by (rule ext, induct_tac x, simp_all)

primrec
  list_fun :: "nat \<Rightarrow> _ list \<Rightarrow> _ \<Rightarrow> _"
where
  "list_fun n [] = (\<lambda>x. 0)"
| "list_fun n (x # xs) = fun_upd (list_fun (Suc n) xs) (from_nat n) x"

definition "vector l = (\<chi> i. list_fun 1 l i)"
(*definition "vector l = (\<chi> i. if i <= length l then l ! (i - 1) else 0)"*)

lemma vector_1: "(vector[x]) $1 = x"
  unfolding vector_def by simp

lemma vector_2:
 "(vector[x,y]) $1 = x"
 "(vector[x,y] :: 'a^2)$2 = (y::'a::zero)"
  unfolding vector_def by simp_all

lemma vector_3:
 "(vector [x,y,z] ::('a::zero)^3)$1 = x"
 "(vector [x,y,z] ::('a::zero)^3)$2 = y"
 "(vector [x,y,z] ::('a::zero)^3)$3 = z"
  unfolding vector_def by simp_all

lemma forall_vector_1: "(\<forall>v::'a::zero^1. P v) \<longleftrightarrow> (\<forall>x. P(vector[x]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (subgoal_tac "vector [v$1] = v")
  apply simp
  apply (vector vector_def)
  apply simp
  done

lemma forall_vector_2: "(\<forall>v::'a::zero^2. P v) \<longleftrightarrow> (\<forall>x y. P(vector[x, y]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (subgoal_tac "vector [v$1, v$2] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_2)
  done

lemma forall_vector_3: "(\<forall>v::'a::zero^3. P v) \<longleftrightarrow> (\<forall>x y z. P(vector[x, y, z]))"
  apply auto
  apply (erule_tac x="v$1" in allE)
  apply (erule_tac x="v$2" in allE)
  apply (erule_tac x="v$3" in allE)
  apply (subgoal_tac "vector [v$1, v$2, v$3] = v")
  apply simp
  apply (vector vector_def)
  apply (simp add: forall_3)
  done

lemma range_vec1[simp]:"range vec1 = UNIV" apply(rule set_ext,rule) unfolding image_iff defer
  apply(rule_tac x="dest_vec1 x" in bexI) by auto

lemma dest_vec1_lambda: "dest_vec1(\<chi> i. x i) = x 1"
  by (simp)

lemma dest_vec1_vec: "dest_vec1(vec x) = x"
  by (simp)

lemma dest_vec1_sum: assumes fS: "finite S"
  shows "dest_vec1(setsum f S) = setsum (dest_vec1 o f) S"
  apply (induct rule: finite_induct[OF fS])
  apply simp
  apply auto
  done

lemma norm_vec1: "norm(vec1 x) = abs(x)"
  by (simp add: vec_def norm_real)

lemma dist_vec1: "dist(vec1 x) (vec1 y) = abs(x - y)"
  by (simp only: dist_real vec1_component)
lemma abs_dest_vec1: "norm x = \<bar>dest_vec1 x\<bar>"
  by (metis vec1_dest_vec1(1) norm_vec1)

lemmas vec1_dest_vec1_simps = forall_vec1 vec_add[THEN sym] dist_vec1 vec_sub[THEN sym] vec1_dest_vec1 norm_vec1 vector_smult_component
   vec1_eq vec_cmul[THEN sym] smult_conv_scaleR[THEN sym] o_def dist_real_def norm_vec1 real_norm_def

lemma bounded_linear_vec1:"bounded_linear (vec1::real\<Rightarrow>real^1)"
  unfolding bounded_linear_def additive_def bounded_linear_axioms_def 
  unfolding smult_conv_scaleR[THEN sym] unfolding vec1_dest_vec1_simps
  apply(rule conjI) defer apply(rule conjI) defer apply(rule_tac x=1 in exI) by auto

lemma linear_vmul_dest_vec1:
  fixes f:: "'a::semiring_1^_ \<Rightarrow> 'a^1"
  shows "linear f \<Longrightarrow> linear (\<lambda>x. dest_vec1(f x) *s v)"
  apply (rule linear_vmul_component)
  by auto

lemma linear_from_scalars:
  assumes lf: "linear (f::'a::comm_ring_1 ^1 \<Rightarrow> 'a^_)"
  shows "f = (\<lambda>x. dest_vec1 x *s column 1 (matrix f))"
  apply (rule ext)
  apply (subst matrix_works[OF lf, symmetric])
  apply (auto simp add: Cart_eq matrix_vector_mult_def column_def mult_commute)
  done

lemma linear_to_scalars: assumes lf: "linear (f::real ^'n \<Rightarrow> real^1)"
  shows "f = (\<lambda>x. vec1(row 1 (matrix f) \<bullet> x))"
  apply (rule ext)
  apply (subst matrix_works[OF lf, symmetric])
  apply (simp add: Cart_eq matrix_vector_mult_def row_def inner_vector_def mult_commute)
  done

lemma dest_vec1_eq_0: "dest_vec1 x = 0 \<longleftrightarrow> x = 0"
  by (simp add: dest_vec1_eq[symmetric])

lemma setsum_scalars: assumes fS: "finite S"
  shows "setsum f S = vec1 (setsum (dest_vec1 o f) S)"
  unfolding vec_setsum[OF fS] by simp

lemma dest_vec1_wlog_le: "(\<And>(x::'a::linorder ^ 1) y. P x y \<longleftrightarrow> P y x)  \<Longrightarrow> (\<And>x y. dest_vec1 x <= dest_vec1 y ==> P x y) \<Longrightarrow> P x y"
  apply (cases "dest_vec1 x \<le> dest_vec1 y")
  apply simp
  apply (subgoal_tac "dest_vec1 y \<le> dest_vec1 x")
  apply (auto)
  done

text{* Lifting and dropping *}

lemma continuous_on_o_dest_vec1: fixes f::"real \<Rightarrow> 'a::real_normed_vector"
  assumes "continuous_on {a..b::real} f" shows "continuous_on {vec1 a..vec1 b} (f o dest_vec1)"
  using assms unfolding continuous_on_iff apply safe
  apply(erule_tac x="x$1" in ballE,erule_tac x=e in allE) apply safe
  apply(rule_tac x=d in exI) apply safe unfolding o_def dist_real_def dist_real 
  apply(erule_tac x="dest_vec1 x'" in ballE) by(auto simp add:vector_le_def)

lemma continuous_on_o_vec1: fixes f::"real^1 \<Rightarrow> 'a::real_normed_vector"
  assumes "continuous_on {a..b} f" shows "continuous_on {dest_vec1 a..dest_vec1 b} (f o vec1)"
  using assms unfolding continuous_on_iff apply safe
  apply(erule_tac x="vec x" in ballE,erule_tac x=e in allE) apply safe
  apply(rule_tac x=d in exI) apply safe unfolding o_def dist_real_def dist_real 
  apply(erule_tac x="vec1 x'" in ballE) by(auto simp add:vector_le_def)

lemma continuous_on_vec1:"continuous_on A (vec1::real\<Rightarrow>real^1)"
  by(rule linear_continuous_on[OF bounded_linear_vec1])

lemma mem_interval_1: fixes x :: "real^1" shows
 "(x \<in> {a .. b} \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 x \<and> dest_vec1 x \<le> dest_vec1 b)"
 "(x \<in> {a<..<b} \<longleftrightarrow> dest_vec1 a < dest_vec1 x \<and> dest_vec1 x < dest_vec1 b)"
by(simp_all add: Cart_eq vector_less_def vector_le_def)

lemma vec1_interval:fixes a::"real" shows
  "vec1 ` {a .. b} = {vec1 a .. vec1 b}"
  "vec1 ` {a<..<b} = {vec1 a<..<vec1 b}"
  apply(rule_tac[!] set_ext) unfolding image_iff vector_less_def unfolding mem_interval
  unfolding forall_1 unfolding vec1_dest_vec1_simps
  apply rule defer apply(rule_tac x="dest_vec1 x" in bexI) prefer 3 apply rule defer
  apply(rule_tac x="dest_vec1 x" in bexI) by auto

(* Some special cases for intervals in R^1.                                  *)

lemma interval_cases_1: fixes x :: "real^1" shows
 "x \<in> {a .. b} ==> x \<in> {a<..<b} \<or> (x = a) \<or> (x = b)"
  unfolding Cart_eq vector_less_def vector_le_def mem_interval by(auto simp del:dest_vec1_eq)

lemma in_interval_1: fixes x :: "real^1" shows
 "(x \<in> {a .. b} \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 x \<and> dest_vec1 x \<le> dest_vec1 b) \<and>
  (x \<in> {a<..<b} \<longleftrightarrow> dest_vec1 a < dest_vec1 x \<and> dest_vec1 x < dest_vec1 b)"
  unfolding Cart_eq vector_less_def vector_le_def mem_interval by(auto simp del:dest_vec1_eq)

lemma interval_eq_empty_1: fixes a :: "real^1" shows
  "{a .. b} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a"
  "{a<..<b} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a"
  unfolding interval_eq_empty and ex_1 by auto

lemma subset_interval_1: fixes a :: "real^1" shows
 "({a .. b} \<subseteq> {c .. d} \<longleftrightarrow>  dest_vec1 b < dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a \<le> dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
 "({a .. b} \<subseteq> {c<..<d} \<longleftrightarrow>  dest_vec1 b < dest_vec1 a \<or>
                dest_vec1 c < dest_vec1 a \<and> dest_vec1 a \<le> dest_vec1 b \<and> dest_vec1 b < dest_vec1 d)"
 "({a<..<b} \<subseteq> {c .. d} \<longleftrightarrow>  dest_vec1 b \<le> dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a < dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
 "({a<..<b} \<subseteq> {c<..<d} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or>
                dest_vec1 c \<le> dest_vec1 a \<and> dest_vec1 a < dest_vec1 b \<and> dest_vec1 b \<le> dest_vec1 d)"
  unfolding subset_interval[of a b c d] unfolding forall_1 by auto

lemma eq_interval_1: fixes a :: "real^1" shows
 "{a .. b} = {c .. d} \<longleftrightarrow>
          dest_vec1 b < dest_vec1 a \<and> dest_vec1 d < dest_vec1 c \<or>
          dest_vec1 a = dest_vec1 c \<and> dest_vec1 b = dest_vec1 d"
unfolding set_eq_subset[of "{a .. b}" "{c .. d}"]
unfolding subset_interval_1(1)[of a b c d]
unfolding subset_interval_1(1)[of c d a b]
by auto

lemma disjoint_interval_1: fixes a :: "real^1" shows
  "{a .. b} \<inter> {c .. d} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a \<or> dest_vec1 d < dest_vec1 c  \<or>  dest_vec1 b < dest_vec1 c \<or> dest_vec1 d < dest_vec1 a"
  "{a .. b} \<inter> {c<..<d} = {} \<longleftrightarrow> dest_vec1 b < dest_vec1 a \<or> dest_vec1 d \<le> dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  "{a<..<b} \<inter> {c .. d} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or> dest_vec1 d < dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  "{a<..<b} \<inter> {c<..<d} = {} \<longleftrightarrow> dest_vec1 b \<le> dest_vec1 a \<or> dest_vec1 d \<le> dest_vec1 c  \<or>  dest_vec1 b \<le> dest_vec1 c \<or> dest_vec1 d \<le> dest_vec1 a"
  unfolding disjoint_interval and ex_1 by auto

lemma open_closed_interval_1: fixes a :: "real^1" shows
 "{a<..<b} = {a .. b} - {a, b}"
  unfolding expand_set_eq apply simp unfolding vector_less_def and vector_le_def and forall_1 and dest_vec1_eq[THEN sym] by(auto simp del:dest_vec1_eq)

lemma closed_open_interval_1: "dest_vec1 (a::real^1) \<le> dest_vec1 b ==> {a .. b} = {a<..<b} \<union> {a,b}"
  unfolding expand_set_eq apply simp unfolding vector_less_def and vector_le_def and forall_1 and dest_vec1_eq[THEN sym] by(auto simp del:dest_vec1_eq)

lemma Lim_drop_le: fixes f :: "'a \<Rightarrow> real^1" shows
  "(f ---> l) net \<Longrightarrow> ~(trivial_limit net) \<Longrightarrow> eventually (\<lambda>x. dest_vec1 (f x) \<le> b) net ==> dest_vec1 l \<le> b"
  using Lim_component_le[of f l net 1 b] by auto

lemma Lim_drop_ge: fixes f :: "'a \<Rightarrow> real^1" shows
 "(f ---> l) net \<Longrightarrow> ~(trivial_limit net) \<Longrightarrow> eventually (\<lambda>x. b \<le> dest_vec1 (f x)) net ==> b \<le> dest_vec1 l"
  using Lim_component_ge[of f l net b 1] by auto

text{* Also more convenient formulations of monotone convergence.                *}

lemma bounded_increasing_convergent: fixes s::"nat \<Rightarrow> real^1"
  assumes "bounded {s n| n::nat. True}"  "\<forall>n. dest_vec1(s n) \<le> dest_vec1(s(Suc n))"
  shows "\<exists>l. (s ---> l) sequentially"
proof-
  obtain a where a:"\<forall>n. \<bar>dest_vec1 (s n)\<bar> \<le>  a" using assms(1)[unfolded bounded_iff abs_dest_vec1] by auto
  { fix m::nat
    have "\<And> n. n\<ge>m \<longrightarrow> dest_vec1 (s m) \<le> dest_vec1 (s n)"
      apply(induct_tac n) apply simp using assms(2) apply(erule_tac x="na" in allE) by(auto simp add: not_less_eq_eq)  }
  hence "\<forall>m n. m \<le> n \<longrightarrow> dest_vec1 (s m) \<le> dest_vec1 (s n)" by auto
  then obtain l where "\<forall>e>0. \<exists>N. \<forall>n\<ge>N. \<bar>dest_vec1 (s n) - l\<bar> < e" using convergent_bounded_monotone[OF a] unfolding monoseq_def by auto
  thus ?thesis unfolding Lim_sequentially apply(rule_tac x="vec1 l" in exI)
    unfolding dist_norm unfolding abs_dest_vec1  by auto
qed

lemma dest_vec1_simps[simp]: fixes a::"real^1"
  shows "a$1 = 0 \<longleftrightarrow> a = 0" (*"a \<le> 1 \<longleftrightarrow> dest_vec1 a \<le> 1" "0 \<le> a \<longleftrightarrow> 0 \<le> dest_vec1 a"*)
  "a \<le> b \<longleftrightarrow> dest_vec1 a \<le> dest_vec1 b" "dest_vec1 (1::real^1) = 1"
  by(auto simp add: vector_le_def Cart_eq)

lemma dest_vec1_inverval:
  "dest_vec1 ` {a .. b} = {dest_vec1 a .. dest_vec1 b}"
  "dest_vec1 ` {a<.. b} = {dest_vec1 a<.. dest_vec1 b}"
  "dest_vec1 ` {a ..<b} = {dest_vec1 a ..<dest_vec1 b}"
  "dest_vec1 ` {a<..<b} = {dest_vec1 a<..<dest_vec1 b}"
  apply(rule_tac [!] equalityI)
  unfolding subset_eq Ball_def Bex_def mem_interval_1 image_iff
  apply(rule_tac [!] allI)apply(rule_tac [!] impI)
  apply(rule_tac[2] x="vec1 x" in exI)apply(rule_tac[4] x="vec1 x" in exI)
  apply(rule_tac[6] x="vec1 x" in exI)apply(rule_tac[8] x="vec1 x" in exI)
  by (auto simp add: vector_less_def vector_le_def)

lemma dest_vec1_setsum: assumes "finite S"
  shows " dest_vec1 (setsum f S) = setsum (\<lambda>x. dest_vec1 (f x)) S"
  using dest_vec1_sum[OF assms] by auto

lemma open_dest_vec1_vimage: "open S \<Longrightarrow> open (dest_vec1 -` S)"
unfolding open_vector_def forall_1 by auto

lemma tendsto_dest_vec1 [tendsto_intros]:
  "(f ---> l) net \<Longrightarrow> ((\<lambda>x. dest_vec1 (f x)) ---> dest_vec1 l) net"
by(rule tendsto_Cart_nth)

lemma continuous_dest_vec1: "continuous net f \<Longrightarrow> continuous net (\<lambda>x. dest_vec1 (f x))"
  unfolding continuous_def by (rule tendsto_dest_vec1)

lemma forall_dest_vec1: "(\<forall>x. P x) \<longleftrightarrow> (\<forall>x. P(dest_vec1 x))" 
  apply safe defer apply(erule_tac x="vec1 x" in allE) by auto

lemma forall_of_dest_vec1: "(\<forall>v. P (\<lambda>x. dest_vec1 (v x))) \<longleftrightarrow> (\<forall>x. P x)"
  apply rule apply rule apply(erule_tac x="(vec1 \<circ> x)" in allE) unfolding o_def vec1_dest_vec1 by auto 

lemma forall_of_dest_vec1': "(\<forall>v. P (dest_vec1 v)) \<longleftrightarrow> (\<forall>x. P x)"
  apply rule apply rule apply(erule_tac x="(vec1 x)" in allE) defer apply rule 
  apply(erule_tac x="dest_vec1 v" in allE) unfolding o_def vec1_dest_vec1 by auto

end
