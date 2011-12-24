(*  Author: Amine Chaieb and L C Paulson, University of Cambridge *)

header {*Sup and Inf Operators on Sets of Reals.*}

theory SupInf
imports RComplete
begin

instantiation real :: Sup 
begin
definition
  Sup_real_def: "Sup X == (LEAST z::real. \<forall>x\<in>X. x\<le>z)"

instance ..
end

instantiation real :: Inf 
begin
definition
  Inf_real_def: "Inf (X::real set) == - (Sup (uminus ` X))"

instance ..
end

subsection{*Supremum of a set of reals*}

lemma Sup_upper [intro]: (*REAL_SUP_UBOUND in HOL4*)
  fixes x :: real
  assumes x: "x \<in> X"
      and z: "!!x. x \<in> X \<Longrightarrow> x \<le> z"
  shows "x \<le> Sup X"
proof (auto simp add: Sup_real_def) 
  from complete_real
  obtain s where s: "(\<forall>y\<in>X. y \<le> s) & (\<forall>z. ((\<forall>y\<in>X. y \<le> z) --> s \<le> z))"
    by (blast intro: x z)
  hence "x \<le> s"
    by (blast intro: x z)
  also with s have "... = (LEAST z. \<forall>x\<in>X. x \<le> z)"
    by (fast intro: Least_equality [symmetric])  
  finally show "x \<le> (LEAST z. \<forall>x\<in>X. x \<le> z)" .
qed

lemma Sup_least [intro]: (*REAL_IMP_SUP_LE in HOL4*)
  fixes z :: real
  assumes x: "X \<noteq> {}"
      and z: "\<And>x. x \<in> X \<Longrightarrow> x \<le> z"
  shows "Sup X \<le> z"
proof (auto simp add: Sup_real_def) 
  from complete_real x
  obtain s where s: "(\<forall>y\<in>X. y \<le> s) & (\<forall>z. ((\<forall>y\<in>X. y \<le> z) --> s \<le> z))"
    by (blast intro: z)
  hence "(LEAST z. \<forall>x\<in>X. x \<le> z) = s"
    by (best intro: Least_equality)  
  also with s z have "... \<le> z"
    by blast
  finally show "(LEAST z. \<forall>x\<in>X. x \<le> z) \<le> z" .
qed

lemma less_SupE:
  fixes y :: real
  assumes "y < Sup X" "X \<noteq> {}"
  obtains x where "x\<in>X" "y < x"
by (metis SupInf.Sup_least assms linorder_not_less that)

lemma Sup_singleton [simp]: "Sup {x::real} = x"
  by (force intro: Least_equality simp add: Sup_real_def)
 
lemma Sup_eq_maximum: (*REAL_SUP_MAX in HOL4*)
  fixes z :: real
  assumes X: "z \<in> X" and z: "!!x. x \<in> X \<Longrightarrow> x \<le> z"
  shows  "Sup X = z"
  by (force intro: Least_equality X z simp add: Sup_real_def)
 
lemma Sup_upper2: (*REAL_IMP_LE_SUP in HOL4*)
  fixes x :: real
  shows "x \<in> X \<Longrightarrow> y \<le> x \<Longrightarrow> (!!x. x \<in> X \<Longrightarrow> x \<le> z) \<Longrightarrow> y \<le> Sup X"
  by (metis Sup_upper order_trans)

lemma Sup_real_iff : (*REAL_SUP_LE in HOL4*)
  fixes z :: real
  shows "X ~= {} ==> (!!x. x \<in> X ==> x \<le> z) ==> (\<exists>x\<in>X. y<x) <-> y < Sup X"
  by (rule iffI, metis less_le_trans Sup_upper, metis Sup_least not_less)

lemma Sup_eq:
  fixes a :: real
  shows "(!!x. x \<in> X \<Longrightarrow> x \<le> a) 
        \<Longrightarrow> (!!y. (!!x. x \<in> X \<Longrightarrow> x \<le> y) \<Longrightarrow> a \<le> y) \<Longrightarrow> Sup X = a"
  by (metis Sup_least Sup_upper add_le_cancel_left diff_add_cancel insert_absorb
        insert_not_empty order_antisym)

lemma Sup_le:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> S *<= b \<Longrightarrow> Sup S \<le> b"
by (metis SupInf.Sup_least setle_def)

lemma Sup_upper_EX: 
  fixes x :: real
  shows "x \<in> X \<Longrightarrow> \<exists>z. \<forall>x. x \<in> X \<longrightarrow> x \<le> z \<Longrightarrow>  x \<le> Sup X"
  by blast

lemma Sup_insert_nonempty: 
  fixes x :: real
  assumes x: "x \<in> X"
      and z: "!!x. x \<in> X \<Longrightarrow> x \<le> z"
  shows "Sup (insert a X) = max a (Sup X)"
proof (cases "Sup X \<le> a")
  case True
  thus ?thesis
    apply (simp add: max_def)
    apply (rule Sup_eq_maximum)
    apply (rule insertI1)
    apply (metis Sup_upper [OF _ z] insertE linear order_trans)
    done
next
  case False
  hence 1:"a < Sup X" by simp
  have "Sup X \<le> Sup (insert a X)"
    apply (rule Sup_least)
    apply (metis ex_in_conv x)
    apply (rule Sup_upper_EX) 
    apply blast
    apply (metis insert_iff linear order_trans z)
    done
  moreover 
  have "Sup (insert a X) \<le> Sup X"
    apply (rule Sup_least)
    apply blast
    apply (metis False Sup_upper insertE linear z)
    done
  ultimately have "Sup (insert a X) = Sup X"
    by (blast intro:  antisym )
  thus ?thesis
    by (metis 1 min_max.le_iff_sup less_le)
qed

lemma Sup_insert_if: 
  fixes X :: "real set"
  assumes z: "!!x. x \<in> X \<Longrightarrow> x \<le> z"
  shows "Sup (insert a X) = (if X={} then a else max a (Sup X))"
by auto (metis Sup_insert_nonempty z) 

lemma Sup: 
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> (\<exists>b. S *<= b) \<Longrightarrow> isLub UNIV S (Sup S)"
by  (auto simp add: isLub_def setle_def leastP_def isUb_def intro!: setgeI) 

lemma Sup_finite_Max: 
  fixes S :: "real set"
  assumes fS: "finite S" and Se: "S \<noteq> {}"
  shows "Sup S = Max S"
using fS Se
proof-
  let ?m = "Max S"
  from Max_ge[OF fS] have Sm: "\<forall> x\<in> S. x \<le> ?m" by metis
  with Sup[OF Se] have lub: "isLub UNIV S (Sup S)" by (metis setle_def)
  from Max_in[OF fS Se] lub have mrS: "?m \<le> Sup S"
    by (auto simp add: isLub_def leastP_def setle_def setge_def isUb_def)
  moreover
  have "Sup S \<le> ?m" using Sm lub
    by (auto simp add: isLub_def leastP_def isUb_def setle_def setge_def)
  ultimately  show ?thesis by arith
qed

lemma Sup_finite_in:
  fixes S :: "real set"
  assumes fS: "finite S" and Se: "S \<noteq> {}"
  shows "Sup S \<in> S"
  using Sup_finite_Max[OF fS Se] Max_in[OF fS Se] by metis

lemma Sup_finite_ge_iff: 
  fixes S :: "real set"
  assumes fS: "finite S" and Se: "S \<noteq> {}"
  shows "a \<le> Sup S \<longleftrightarrow> (\<exists> x \<in> S. a \<le> x)"
by (metis Max_ge Se Sup_finite_Max Sup_finite_in fS linorder_not_le less_le_trans)

lemma Sup_finite_le_iff: 
  fixes S :: "real set"
  assumes fS: "finite S" and Se: "S \<noteq> {}"
  shows "a \<ge> Sup S \<longleftrightarrow> (\<forall> x \<in> S. a \<ge> x)"
by (metis Max_ge Se Sup_finite_Max Sup_finite_in fS order_trans)

lemma Sup_finite_gt_iff: 
  fixes S :: "real set"
  assumes fS: "finite S" and Se: "S \<noteq> {}"
  shows "a < Sup S \<longleftrightarrow> (\<exists> x \<in> S. a < x)"
by (metis Se Sup_finite_le_iff fS linorder_not_less)

lemma Sup_finite_lt_iff: 
  fixes S :: "real set"
  assumes fS: "finite S" and Se: "S \<noteq> {}"
  shows "a > Sup S \<longleftrightarrow> (\<forall> x \<in> S. a > x)"
by (metis Se Sup_finite_ge_iff fS linorder_not_less)

lemma Sup_unique:
  fixes S :: "real set"
  shows "S *<= b \<Longrightarrow> (\<forall>b' < b. \<exists>x \<in> S. b' < x) \<Longrightarrow> Sup S = b"
unfolding setle_def
apply (rule Sup_eq, auto) 
apply (metis linorder_not_less) 
done

lemma Sup_abs_le:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> (\<forall>x\<in>S. \<bar>x\<bar> \<le> a) \<Longrightarrow> \<bar>Sup S\<bar> \<le> a"
by (auto simp add: abs_le_interval_iff) (metis Sup_upper2) 

lemma Sup_bounds:
  fixes S :: "real set"
  assumes Se: "S \<noteq> {}" and l: "a <=* S" and u: "S *<= b"
  shows "a \<le> Sup S \<and> Sup S \<le> b"
proof-
  from Sup[OF Se] u have lub: "isLub UNIV S (Sup S)" by blast
  hence b: "Sup S \<le> b" using u 
    by (auto simp add: isLub_def leastP_def setle_def setge_def isUb_def) 
  from Se obtain y where y: "y \<in> S" by blast
  from lub l have "a \<le> Sup S"
    by (auto simp add: isLub_def leastP_def setle_def setge_def isUb_def)
       (metis le_iff_sup le_sup_iff y)
  with b show ?thesis by blast
qed

lemma Sup_asclose: 
  fixes S :: "real set"
  assumes S:"S \<noteq> {}" and b: "\<forall>x\<in>S. \<bar>x - l\<bar> \<le> e" shows "\<bar>Sup S - l\<bar> \<le> e"
proof-
  have th: "\<And>(x::real) l e. \<bar>x - l\<bar> \<le> e \<longleftrightarrow> l - e \<le> x \<and> x \<le> l + e" by arith
  thus ?thesis using S b Sup_bounds[of S "l - e" "l+e"] unfolding th
    by  (auto simp add: setge_def setle_def)
qed

lemma Sup_lessThan[simp]: "Sup {..<x} = (x::real)"
  by (auto intro!: Sup_eq intro: dense_le)

lemma Sup_greaterThanLessThan[simp]: "y < x \<Longrightarrow> Sup {y<..<x} = (x::real)"
  by (auto intro!: Sup_eq intro: dense_le_bounded)

lemma Sup_atLeastLessThan[simp]: "y < x \<Longrightarrow> Sup {y..<x} = (x::real)"
  by (auto intro!: Sup_eq intro: dense_le_bounded)

lemma Sup_atMost[simp]: "Sup {..x} = (x::real)"
  by (auto intro!: Sup_eq_maximum)

lemma Sup_greaterThanAtMost[simp]: "y < x \<Longrightarrow> Sup {y<..x} = (x::real)"
  by (auto intro!: Sup_eq_maximum)

lemma Sup_atLeastAtMost[simp]: "y \<le> x \<Longrightarrow> Sup {y..x} = (x::real)"
  by (auto intro!: Sup_eq_maximum)


subsection{*Infimum of a set of reals*}

lemma Inf_lower [intro]: 
  fixes z :: real
  assumes x: "x \<in> X"
      and z: "!!x. x \<in> X \<Longrightarrow> z \<le> x"
  shows "Inf X \<le> x"
proof -
  have "-x \<le> Sup (uminus ` X)"
    by (rule Sup_upper [where z = "-z"]) (auto simp add: image_iff x z)
  thus ?thesis 
    by (auto simp add: Inf_real_def)
qed

lemma Inf_greatest [intro]: 
  fixes z :: real
  assumes x: "X \<noteq> {}"
      and z: "\<And>x. x \<in> X \<Longrightarrow> z \<le> x"
  shows "z \<le> Inf X"
proof -
  have "Sup (uminus ` X) \<le> -z" using x z by force
  hence "z \<le> - Sup (uminus ` X)"
    by simp
  thus ?thesis 
    by (auto simp add: Inf_real_def)
qed

lemma Inf_singleton [simp]: "Inf {x::real} = x"
  by (simp add: Inf_real_def) 
 
lemma Inf_eq_minimum: (*REAL_INF_MIN in HOL4*)
  fixes z :: real
  assumes x: "z \<in> X" and z: "!!x. x \<in> X \<Longrightarrow> z \<le> x"
  shows  "Inf X = z"
proof -
  have "Sup (uminus ` X) = -z" using x z
    by (force intro: Sup_eq_maximum x z)
  thus ?thesis
    by (simp add: Inf_real_def) 
qed
 
lemma Inf_lower2:
  fixes x :: real
  shows "x \<in> X \<Longrightarrow> x \<le> y \<Longrightarrow> (!!x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> Inf X \<le> y"
  by (metis Inf_lower order_trans)

lemma Inf_real_iff:
  fixes z :: real
  shows "X \<noteq> {} \<Longrightarrow> (!!x. x \<in> X \<Longrightarrow> z \<le> x) \<Longrightarrow> (\<exists>x\<in>X. x<y) \<longleftrightarrow> Inf X < y"
  by (metis Inf_greatest Inf_lower less_le_not_le linear
            order_less_le_trans)

lemma Inf_eq:
  fixes a :: real
  shows "(!!x. x \<in> X \<Longrightarrow> a \<le> x) \<Longrightarrow> (!!y. (!!x. x \<in> X \<Longrightarrow> y \<le> x) \<Longrightarrow> y \<le> a) \<Longrightarrow> Inf X = a"
  by (metis Inf_greatest Inf_lower add_le_cancel_left diff_add_cancel
        insert_absorb insert_not_empty order_antisym)

lemma Inf_ge: 
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> b <=* S \<Longrightarrow> Inf S \<ge> b"
by (metis SupInf.Inf_greatest setge_def)

lemma Inf_lower_EX: 
  fixes x :: real
  shows "x \<in> X \<Longrightarrow> \<exists>z. \<forall>x. x \<in> X \<longrightarrow> z \<le> x \<Longrightarrow> Inf X \<le> x"
  by blast

lemma Inf_insert_nonempty: 
  fixes x :: real
  assumes x: "x \<in> X"
      and z: "!!x. x \<in> X \<Longrightarrow> z \<le> x"
  shows "Inf (insert a X) = min a (Inf X)"
proof (cases "a \<le> Inf X")
  case True
  thus ?thesis
    by (simp add: min_def)
       (blast intro: Inf_eq_minimum order_trans z)
next
  case False
  hence 1:"Inf X < a" by simp
  have "Inf (insert a X) \<le> Inf X"
    apply (rule Inf_greatest)
    apply (metis ex_in_conv x)
    apply (rule Inf_lower_EX)
    apply (erule insertI2)
    apply (metis insert_iff linear order_trans z)
    done
  moreover 
  have "Inf X \<le> Inf (insert a X)"
    apply (rule Inf_greatest)
    apply blast
    apply (metis False Inf_lower insertE linear z) 
    done
  ultimately have "Inf (insert a X) = Inf X"
    by (blast intro:  antisym )
  thus ?thesis
    by (metis False min_max.inf_absorb2 linear)
qed

lemma Inf_insert_if: 
  fixes X :: "real set"
  assumes z:  "!!x. x \<in> X \<Longrightarrow> z \<le> x"
  shows "Inf (insert a X) = (if X={} then a else min a (Inf X))"
by auto (metis Inf_insert_nonempty z) 

lemma Inf_greater:
  fixes z :: real
  shows "X \<noteq> {} \<Longrightarrow> Inf X < z \<Longrightarrow> \<exists>x \<in> X. x < z"
  by (metis Inf_real_iff not_leE)

lemma Inf_close:
  fixes e :: real
  shows "X \<noteq> {} \<Longrightarrow> 0 < e \<Longrightarrow> \<exists>x \<in> X. x < Inf X + e"
  by (metis add_strict_increasing add_commute Inf_greater linorder_not_le pos_add_strict)

lemma Inf_finite_Min:
  fixes S :: "real set"
  shows "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> Inf S = Min S"
by (simp add: Inf_real_def Sup_finite_Max image_image) 

lemma Inf_finite_in: 
  fixes S :: "real set"
  assumes fS: "finite S" and Se: "S \<noteq> {}"
  shows "Inf S \<in> S"
  using Inf_finite_Min[OF fS Se] Min_in[OF fS Se] by metis

lemma Inf_finite_ge_iff: 
  fixes S :: "real set"
  shows "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> a \<le> Inf S \<longleftrightarrow> (\<forall> x \<in> S. a \<le> x)"
by (metis Inf_finite_Min Inf_finite_in Min_le order_trans)

lemma Inf_finite_le_iff:
  fixes S :: "real set"
  shows "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> a \<ge> Inf S \<longleftrightarrow> (\<exists> x \<in> S. a \<ge> x)"
by (metis Inf_finite_Min Inf_finite_ge_iff Inf_finite_in Min_le
          order_antisym linear)

lemma Inf_finite_gt_iff: 
  fixes S :: "real set"
  shows "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> a < Inf S \<longleftrightarrow> (\<forall> x \<in> S. a < x)"
by (metis Inf_finite_le_iff linorder_not_less)

lemma Inf_finite_lt_iff: 
  fixes S :: "real set"
  shows "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> a > Inf S \<longleftrightarrow> (\<exists> x \<in> S. a > x)"
by (metis Inf_finite_ge_iff linorder_not_less)

lemma Inf_unique:
  fixes S :: "real set"
  shows "b <=* S \<Longrightarrow> (\<forall>b' > b. \<exists>x \<in> S. b' > x) \<Longrightarrow> Inf S = b"
unfolding setge_def
apply (rule Inf_eq, auto) 
apply (metis less_le_not_le linorder_not_less) 
done

lemma Inf_abs_ge:
  fixes S :: "real set"
  shows "S \<noteq> {} \<Longrightarrow> (\<forall>x\<in>S. \<bar>x\<bar> \<le> a) \<Longrightarrow> \<bar>Inf S\<bar> \<le> a"
by (simp add: Inf_real_def) (rule Sup_abs_le, auto) 

lemma Inf_asclose:
  fixes S :: "real set"
  assumes S:"S \<noteq> {}" and b: "\<forall>x\<in>S. \<bar>x - l\<bar> \<le> e" shows "\<bar>Inf S - l\<bar> \<le> e"
proof -
  have "\<bar>- Sup (uminus ` S) - l\<bar> =  \<bar>Sup (uminus ` S) - (-l)\<bar>"
    by auto
  also have "... \<le> e" 
    apply (rule Sup_asclose) 
    apply (auto simp add: S)
    apply (metis abs_minus_add_cancel b add_commute diff_minus)
    done
  finally have "\<bar>- Sup (uminus ` S) - l\<bar> \<le> e" .
  thus ?thesis
    by (simp add: Inf_real_def)
qed

lemma Inf_greaterThanLessThan[simp]: "y < x \<Longrightarrow> Inf {y<..<x} = (y::real)"
  by (simp add: Inf_real_def)

lemma Inf_atLeastLessThan[simp]: "y < x \<Longrightarrow> Inf {y..<x} = (y::real)"
  by (simp add: Inf_real_def)

lemma Inf_atLeast[simp]: "Inf {x..} = (x::real)"
  by (simp add: Inf_real_def)

lemma Inf_greaterThanAtMost[simp]: "y < x \<Longrightarrow> Inf {y<..x} = (y::real)"
  by (simp add: Inf_real_def)

lemma Inf_atLeastAtMost[simp]: "y \<le> x \<Longrightarrow> Inf {y..x} = (y::real)"
  by (simp add: Inf_real_def)

subsection{*Relate max and min to Sup and Inf.*}

lemma real_max_Sup:
  fixes x :: real
  shows "max x y = Sup {x,y}"
proof-
  have f: "finite {x, y}" "{x,y} \<noteq> {}"  by simp_all
  from Sup_finite_le_iff[OF f, of "max x y"] have "Sup {x,y} \<le> max x y" by simp
  moreover
  have "max x y \<le> Sup {x,y}" using Sup_finite_ge_iff[OF f, of "max x y"]
    by (simp add: linorder_linear)
  ultimately show ?thesis by arith
qed

lemma real_min_Inf: 
  fixes x :: real
  shows "min x y = Inf {x,y}"
proof-
  have f: "finite {x, y}" "{x,y} \<noteq> {}"  by simp_all
  from Inf_finite_le_iff[OF f, of "min x y"] have "Inf {x,y} \<le> min x y"
    by (simp add: linorder_linear)
  moreover
  have "min x y \<le> Inf {x,y}" using Inf_finite_ge_iff[OF f, of "min x y"]
    by simp
  ultimately show ?thesis by arith
qed

lemma reals_complete_interval:
  fixes a::real and b::real
  assumes "a < b" and "P a" and "~P b"
  shows "\<exists>c. a \<le> c & c \<le> b & (\<forall>x. a \<le> x & x < c --> P x) &
             (\<forall>d. (\<forall>x. a \<le> x & x < d --> P x) --> d \<le> c)"
proof (rule exI [where x = "Sup {d. \<forall>x. a \<le> x & x < d --> P x}"], auto)
  show "a \<le> Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c}"
    by (rule SupInf.Sup_upper [where z=b], auto)
       (metis `a < b` `\<not> P b` linear less_le)
next
  show "Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c} \<le> b"
    apply (rule SupInf.Sup_least) 
    apply (auto simp add: )
    apply (metis less_le_not_le)
    apply (metis `a<b` `~ P b` linear less_le)
    done
next
  fix x
  assume x: "a \<le> x" and lt: "x < Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c}"
  show "P x"
    apply (rule less_SupE [OF lt], auto)
    apply (metis less_le_not_le)
    apply (metis x) 
    done
next
  fix d
    assume 0: "\<forall>x. a \<le> x \<and> x < d \<longrightarrow> P x"
    thus "d \<le> Sup {d. \<forall>c. a \<le> c \<and> c < d \<longrightarrow> P c}"
      by (rule_tac z="b" in SupInf.Sup_upper, auto) 
         (metis `a<b` `~ P b` linear less_le)
qed

end
