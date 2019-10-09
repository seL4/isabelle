section \<open>Asymptotic real interval arithmetic\<close>
(*
  File:     Multiseries_Expansion_Bounds.thy
  Author:   Manuel Eberl, TU München

  Automatic computation of upper and lower expansions for real-valued functions.
  Allows limited handling of functions involving oscillating functions like sin, cos, floor, etc.
*)
theory Multiseries_Expansion_Bounds
imports
  Multiseries_Expansion
begin

lemma expands_to_cong_reverse:
  "eventually (\<lambda>x. f x = g x) at_top \<Longrightarrow> (g expands_to F) bs \<Longrightarrow> (f expands_to F) bs"
  using expands_to_cong[of g F bs f] by (simp add: eq_commute)

lemma expands_to_trivial_bounds: "(f expands_to F) bs \<Longrightarrow> eventually (\<lambda>x. f x \<in> {f x..f x}) at_top"
  by simp

lemma eventually_in_atLeastAtMostI:
  assumes "eventually (\<lambda>x. f x \<ge> l x) at_top" "eventually (\<lambda>x. f x \<le> u x) at_top"
  shows   "eventually (\<lambda>x. f x \<in> {l x..u x}) at_top"
  using assms by eventually_elim simp_all

lemma tendsto_sandwich':
  fixes l f u :: "'a \<Rightarrow> 'b :: order_topology"
  shows "eventually (\<lambda>x. l x \<le> f x) F \<Longrightarrow> eventually (\<lambda>x. f x \<le> u x) F \<Longrightarrow>
           (l \<longlongrightarrow> L1) F \<Longrightarrow> (u \<longlongrightarrow> L2) F \<Longrightarrow> L1 = L2 \<Longrightarrow> (f \<longlongrightarrow> L1) F"
  using tendsto_sandwich[of l f F u L1] by simp

(* TODO: Move? *)
lemma filterlim_at_bot_mono:
  fixes l f u :: "'a \<Rightarrow> 'b :: linorder_topology"
  assumes "filterlim u at_bot F" and "eventually (\<lambda>x. f x \<le> u x) F"
  shows   "filterlim f at_bot F"
  unfolding filterlim_at_bot
proof
  fix Z :: 'b
  from assms(1) have "eventually (\<lambda>x. u x \<le> Z) F" by (auto simp: filterlim_at_bot)
  with assms(2) show "eventually (\<lambda>x. f x \<le> Z) F" by eventually_elim simp
qed

context
begin

qualified lemma eq_zero_imp_nonneg: "x = (0::real) \<Longrightarrow> x \<ge> 0"
  by simp

qualified lemma exact_to_bound: "(f expands_to F) bs \<Longrightarrow> eventually (\<lambda>x. f x \<le> f x) at_top"
  by simp

qualified lemma expands_to_abs_nonneg: "(f expands_to F) bs \<Longrightarrow> eventually (\<lambda>x. abs (f x) \<ge> 0) at_top"
  by simp

qualified lemma eventually_nonpos_flip: "eventually (\<lambda>x. f x \<le> (0::real)) F \<Longrightarrow> eventually (\<lambda>x. -f x \<ge> 0) F"
  by simp

qualified lemma bounds_uminus:
  fixes a b :: "real \<Rightarrow> real"
  assumes "eventually (\<lambda>x. a x \<le> b x) at_top"
  shows   "eventually (\<lambda>x. -b x \<le> -a x) at_top"
  using assms by eventually_elim simp

qualified lemma
  fixes a b c d :: "real \<Rightarrow> real"
  assumes "eventually (\<lambda>x. a x \<le> b x) at_top" "eventually (\<lambda>x. c x \<le> d x) at_top"
  shows   combine_bounds_add:  "eventually (\<lambda>x. a x + c x \<le> b x + d x) at_top"
    and   combine_bounds_diff: "eventually (\<lambda>x. a x - d x \<le> b x - c x) at_top"
  by (use assms in eventually_elim; simp add: add_mono diff_mono)+

qualified lemma
  fixes a b c d :: "real \<Rightarrow> real"
  assumes "eventually (\<lambda>x. a x \<le> b x) at_top" "eventually (\<lambda>x. c x \<le> d x) at_top"
  shows   combine_bounds_min: "eventually (\<lambda>x. min (a x) (c x) \<le> min (b x) (d x)) at_top"
    and   combine_bounds_max: "eventually (\<lambda>x. max (a x) (c x) \<le> max (b x) (d x)) at_top"
  by (blast intro: eventually_elim2[OF assms] min.mono max.mono)+


qualified lemma trivial_bounds_sin:  "\<forall>x::real. sin x \<in> {-1..1}"
  and trivial_bounds_cos:  "\<forall>x::real. cos x \<in> {-1..1}"
  and trivial_bounds_frac: "\<forall>x::real. frac x \<in> {0..1}"
  by (auto simp: less_imp_le[OF frac_lt_1])

qualified lemma trivial_boundsI:
  fixes f g:: "real \<Rightarrow> real"
  assumes "\<forall>x. f x \<in> {l..u}" and "g \<equiv> g"
  shows   "eventually (\<lambda>x. f (g x) \<ge> l) at_top" "eventually (\<lambda>x. f (g x) \<le> u) at_top"
  using assms by auto

qualified lemma
  fixes f f' :: "real \<Rightarrow> real"
  shows transfer_lower_bound:
          "eventually (\<lambda>x. g x \<ge> l x) at_top \<Longrightarrow> f \<equiv> g \<Longrightarrow> eventually (\<lambda>x. f x \<ge> l x) at_top"
  and   transfer_upper_bound:
          "eventually (\<lambda>x. g x \<le> u x) at_top \<Longrightarrow> f \<equiv> g \<Longrightarrow> eventually (\<lambda>x. f x \<le> u x) at_top"
  by simp_all  

qualified lemma mono_bound:
  fixes f g h :: "real \<Rightarrow> real"
  assumes "mono h" "eventually (\<lambda>x. f x \<le> g x) at_top"
  shows   "eventually (\<lambda>x. h (f x) \<le> h (g x)) at_top"
  by (intro eventually_mono[OF assms(2)] monoD[OF assms(1)])

qualified lemma
  fixes f l :: "real \<Rightarrow> real"
  assumes "(l expands_to L) bs" "trimmed_pos L" "basis_wf bs" "eventually (\<lambda>x. l x \<le> f x) at_top"
  shows   expands_to_lb_ln: "eventually (\<lambda>x. ln (l x) \<le> ln (f x)) at_top"
    and   expands_to_ub_ln: 
            "eventually (\<lambda>x. f x \<le> u x) at_top \<Longrightarrow> eventually (\<lambda>x. ln (f x) \<le> ln (u x)) at_top"
proof -
  from assms(3,1,2) have pos: "eventually (\<lambda>x. l x > 0) at_top"
    by (rule expands_to_imp_eventually_pos)  
  from pos and assms(4)
    show "eventually (\<lambda>x. ln (l x) \<le> ln (f x)) at_top" by eventually_elim simp
  assume "eventually (\<lambda>x. f x \<le> u x) at_top"
  with pos and assms(4) show "eventually (\<lambda>x. ln (f x) \<le> ln (u x)) at_top"
    by eventually_elim simp
qed

qualified lemma eventually_sgn_ge_1D:
  assumes "eventually (\<lambda>x::real. sgn (f x) \<ge> l x) at_top"
          "(l expands_to (const_expansion 1 :: 'a :: multiseries)) bs"
  shows   "((\<lambda>x. sgn (f x)) expands_to (const_expansion 1 :: 'a)) bs"
proof (rule expands_to_cong)
  from assms(2) have "eventually (\<lambda>x. l x = 1) at_top"
    by (simp add: expands_to.simps)
  with assms(1) show "eventually (\<lambda>x. 1 = sgn (f x)) at_top"
    by eventually_elim (auto simp: sgn_if split: if_splits)
qed (insert assms, auto simp: expands_to.simps)

qualified lemma eventually_sgn_le_neg1D:
  assumes "eventually (\<lambda>x::real. sgn (f x) \<le> u x) at_top"
          "(u expands_to (const_expansion (-1) :: 'a :: multiseries)) bs"
  shows   "((\<lambda>x. sgn (f x)) expands_to (const_expansion (-1) :: 'a)) bs"
proof (rule expands_to_cong)
  from assms(2) have "eventually (\<lambda>x. u x = -1) at_top"
    by (simp add: expands_to.simps eq_commute)
  with assms(1) show "eventually (\<lambda>x. -1 = sgn (f x)) at_top"
    by eventually_elim (auto simp: sgn_if split: if_splits)
qed (insert assms, auto simp: expands_to.simps)


qualified lemma expands_to_squeeze:
  assumes "eventually (\<lambda>x. l x \<le> f x) at_top" "eventually (\<lambda>x. f x \<le> g x) at_top"
          "(l expands_to L) bs" "(g expands_to L) bs"
  shows   "(f expands_to L) bs"
proof (rule expands_to_cong[OF assms(3)])
  from assms have "eventually (\<lambda>x. eval L x = l x) at_top" "eventually (\<lambda>x. eval L x = g x) at_top"
    by (simp_all add: expands_to.simps)
  with assms(1,2) show "eventually (\<lambda>x. l x = f x) at_top"
    by eventually_elim simp
qed 


qualified lemma mono_exp_real: "mono (exp :: real \<Rightarrow> real)"
  by (auto intro!: monoI)

qualified lemma mono_sgn_real: "mono (sgn :: real \<Rightarrow> real)"
  by (auto intro!: monoI simp: sgn_if)

qualified lemma mono_arctan_real: "mono (arctan :: real \<Rightarrow> real)"
  by (auto intro!: monoI arctan_monotone')

qualified lemma mono_root_real: "n \<equiv> n \<Longrightarrow> mono (root n :: real \<Rightarrow> real)"
  by (cases n) (auto simp: mono_def)

qualified lemma mono_rfloor: "mono rfloor" and mono_rceil: "mono rceil"
  by (auto intro!: monoI simp: rfloor_def floor_mono rceil_def ceiling_mono)

qualified lemma lower_bound_cong:
  "eventually (\<lambda>x. f x = g x) at_top \<Longrightarrow> eventually (\<lambda>x. l x \<le> g x) at_top \<Longrightarrow>
     eventually (\<lambda>x. l x \<le> f x) at_top"
  by (erule (1) eventually_elim2) simp

qualified lemma upper_bound_cong:
  "eventually (\<lambda>x. f x = g x) at_top \<Longrightarrow> eventually (\<lambda>x. g x \<le> u x) at_top \<Longrightarrow>
     eventually (\<lambda>x. f x \<le> u x) at_top"
  by (erule (1) eventually_elim2) simp

qualified lemma
  assumes "eventually (\<lambda>x. f x = (g x :: real)) at_top"
  shows   eventually_eq_min: "eventually (\<lambda>x. min (f x) (g x) = f x) at_top"
    and   eventually_eq_max: "eventually (\<lambda>x. max (f x) (g x) = f x) at_top"
  by (rule eventually_mono[OF assms]; simp)+

qualified lemma rfloor_bound:
    "eventually (\<lambda>x. l x \<le> f x) at_top \<Longrightarrow> eventually (\<lambda>x. l x - 1 \<le> rfloor (f x)) at_top"
    "eventually (\<lambda>x. f x \<le> u x) at_top \<Longrightarrow> eventually (\<lambda>x. rfloor (f x) \<le> u x) at_top"
  and rceil_bound:
    "eventually (\<lambda>x. l x \<le> f x) at_top \<Longrightarrow> eventually (\<lambda>x. l x \<le> rceil (f x)) at_top"
    "eventually (\<lambda>x. f x \<le> u x) at_top \<Longrightarrow> eventually (\<lambda>x. rceil (f x) \<le> u x + 1) at_top"
  unfolding rfloor_def rceil_def by (erule eventually_mono, linarith)+

qualified lemma natmod_trivial_lower_bound:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f \<equiv> f" "g \<equiv> g"
  shows "eventually (\<lambda>x. rnatmod (f x) (g x) \<ge> 0) at_top"
  by (simp add: rnatmod_def)

qualified lemma natmod_upper_bound:
  fixes f g :: "real \<Rightarrow> real"
  assumes "f \<equiv> f" and "eventually (\<lambda>x. l2 x \<le> g x) at_top" and "eventually (\<lambda>x. g x \<le> u2 x) at_top"
  assumes "eventually (\<lambda>x. l2 x - 1 \<ge> 0) at_top"
  shows "eventually (\<lambda>x. rnatmod (f x) (g x) \<le> u2 x - 1) at_top"
  using assms(2-)
proof eventually_elim
  case (elim x)
  have "rnatmod (f x) (g x) = real (nat \<lfloor>f x\<rfloor> mod nat \<lfloor>g x\<rfloor>)"
    by (simp add: rnatmod_def)
  also have "nat \<lfloor>f x\<rfloor> mod nat \<lfloor>g x\<rfloor> < nat \<lfloor>g x\<rfloor>"
    using elim by (intro mod_less_divisor) auto
  hence "real (nat \<lfloor>f x\<rfloor> mod nat \<lfloor>g x\<rfloor>) \<le> u2 x - 1"
    using elim by linarith
  finally show ?case .
qed

qualified lemma natmod_upper_bound':
  fixes f g :: "real \<Rightarrow> real"
  assumes "g \<equiv> g" "eventually (\<lambda>x. u1 x \<ge> 0) at_top" and "eventually (\<lambda>x. f x \<le> u1 x) at_top"
  shows "eventually (\<lambda>x. rnatmod (f x) (g x) \<le> u1 x) at_top"
  using assms(2-)
proof eventually_elim
  case (elim x)
  have "rnatmod (f x) (g x) = real (nat \<lfloor>f x\<rfloor> mod nat \<lfloor>g x\<rfloor>)"
    by (simp add: rnatmod_def)
  also have "nat \<lfloor>f x\<rfloor> mod nat \<lfloor>g x\<rfloor> \<le> nat \<lfloor>f x\<rfloor>"
    by auto
  hence "real (nat \<lfloor>f x\<rfloor> mod nat \<lfloor>g x\<rfloor>) \<le> real (nat \<lfloor>f x\<rfloor>)"
    by simp
  also have "\<dots> \<le> u1 x" using elim by linarith
  finally show "rnatmod (f x) (g x) \<le> \<dots>" .
qed

qualified lemma expands_to_natmod_nonpos:
  fixes f g :: "real \<Rightarrow> real"
  assumes "g \<equiv> g" "eventually (\<lambda>x. u1 x \<le> 0) at_top" "eventually (\<lambda>x. f x \<le> u1 x) at_top"
          "((\<lambda>_. 0) expands_to C) bs"
  shows "((\<lambda>x. rnatmod (f x) (g x)) expands_to C) bs"
  by (rule expands_to_cong[OF assms(4)])
     (insert assms, auto elim: eventually_elim2 simp: rnatmod_def)
  

qualified lemma eventually_atLeastAtMostI:
  fixes f l r :: "real \<Rightarrow> real"
  assumes "eventually (\<lambda>x. l x \<le> f x) at_top" "eventually (\<lambda>x. f x \<le> u x) at_top"
  shows   "eventually (\<lambda>x. f x \<in> {l x..u x}) at_top"
  using assms by eventually_elim simp

qualified lemma eventually_atLeastAtMostD:
  fixes f l r :: "real \<Rightarrow> real"
  assumes "eventually (\<lambda>x. f x \<in> {l x..u x}) at_top"
  shows   "eventually (\<lambda>x. l x \<le> f x) at_top" "eventually (\<lambda>x. f x \<le> u x) at_top" 
  using assms by (simp_all add: eventually_conj_iff)

qualified lemma eventually_0_imp_prod_zero:
  fixes f g :: "real \<Rightarrow> real"
  assumes "eventually (\<lambda>x. f x = 0) at_top"
  shows   "eventually (\<lambda>x. f x * g x = 0) at_top" "eventually (\<lambda>x. g x * f x = 0) at_top"
  by (use assms in eventually_elim; simp)+

qualified lemma mult_right_bounds:
  fixes f g :: "real \<Rightarrow> real"
  shows "\<forall>x. f x \<in> {l x..u x} \<longrightarrow> g x \<ge> 0 \<longrightarrow> f x * g x \<in> {l x * g x..u x * g x}"
    and "\<forall>x. f x \<in> {l x..u x} \<longrightarrow> g x \<le> 0 \<longrightarrow> f x * g x \<in> {u x * g x..l x * g x}"
  by (auto intro: mult_right_mono mult_right_mono_neg)

qualified lemma mult_left_bounds:
  fixes f g :: "real \<Rightarrow> real"
  shows "\<forall>x. g x \<in> {l x..u x} \<longrightarrow> f x \<ge> 0 \<longrightarrow> f x * g x \<in> {f x * l x..f x * u x}"
    and "\<forall>x. g x \<in> {l x..u x} \<longrightarrow> f x \<le> 0 \<longrightarrow> f x * g x \<in> {f x * u x..f x * l x}"
  by (auto intro: mult_left_mono mult_left_mono_neg)

qualified lemma mult_mono_nonpos_nonneg:
  "a \<le> c \<Longrightarrow> d \<le> b \<Longrightarrow> a \<le> 0 \<Longrightarrow> d \<ge> 0 \<Longrightarrow> a * b \<le> c * (d :: 'a :: linordered_ring)"
  using mult_mono[of "-c" "-a" d b] by simp

qualified lemma mult_mono_nonneg_nonpos:
  "c \<le> a \<Longrightarrow> b \<le> d \<Longrightarrow> a \<ge> 0 \<Longrightarrow> d \<le> 0 \<Longrightarrow> a * b \<le> c * (d :: 'a :: {comm_ring, linordered_ring})"
  using mult_mono[of c a "-d" "-b"] by (simp add: mult.commute)

qualified lemma mult_mono_nonpos_nonpos:
  "c \<le> a \<Longrightarrow> d \<le> b \<Longrightarrow> c \<le> 0 \<Longrightarrow> b \<le> 0 \<Longrightarrow> a * b \<le> c * (d :: 'a :: linordered_ring)"
  using mult_mono[of "-a" "-c" "-b" "-d"] by simp

qualified lemmas mult_monos =
  mult_mono mult_mono_nonpos_nonneg mult_mono_nonneg_nonpos mult_mono_nonpos_nonpos


qualified lemma mult_bounds_real:
  fixes f g l1 u1 l2 u2 l u :: "real \<Rightarrow> real"
  defines "P \<equiv> \<lambda>l u x. f x \<in> {l1 x..u1 x} \<longrightarrow> g x \<in> {l2 x..u2 x} \<longrightarrow> f x * g x \<in> {l..u}"
  shows   "\<forall>x. l1 x \<ge> 0 \<longrightarrow> l2 x \<ge> 0 \<longrightarrow> P (l1 x * l2 x) (u1 x * u2 x) x"
    and   "\<forall>x. u1 x \<le> 0 \<longrightarrow> l2 x \<ge> 0 \<longrightarrow> P (l1 x * u2 x) (u1 x * l2 x) x"
    and   "\<forall>x. l1 x \<ge> 0 \<longrightarrow> u2 x \<le> 0 \<longrightarrow> P (u1 x * l2 x) (l1 x * u2 x) x"
    and   "\<forall>x. u1 x \<le> 0 \<longrightarrow> u2 x \<le> 0 \<longrightarrow> P (u1 x * u2 x) (l1 x * l2 x) x"

    and   "\<forall>x. l1 x \<le> 0 \<longrightarrow> u1 x \<ge> 0 \<longrightarrow> l2 x \<ge> 0 \<longrightarrow> P (l1 x * u2 x) (u1 x * u2 x) x"
    and   "\<forall>x. l1 x \<le> 0 \<longrightarrow> u1 x \<ge> 0 \<longrightarrow> u2 x \<le> 0 \<longrightarrow> P (u1 x * l2 x) (l1 x * l2 x) x"
    and   "\<forall>x. l1 x \<ge> 0 \<longrightarrow> l2 x \<le> 0 \<longrightarrow> u2 x \<ge> 0 \<longrightarrow> P (u1 x * l2 x) (u1 x * u2 x) x"
    and   "\<forall>x. u1 x \<le> 0 \<longrightarrow> l2 x \<le> 0 \<longrightarrow> u2 x \<ge> 0 \<longrightarrow> P (l1 x * u2 x) (l1 x * l2 x) x"

    and   "\<forall>x. l1 x \<le> 0 \<longrightarrow> u1 x \<ge> 0 \<longrightarrow> l2 x \<le> 0 \<longrightarrow> u2 x \<ge> 0 \<longrightarrow> l x \<le> l1 x * u2 x \<longrightarrow>
             l x \<le> u1 x * l2 x \<longrightarrow> u x \<ge> l1 x* l2 x \<longrightarrow> u x \<ge> u1 x * u2 x \<longrightarrow> P (l x) (u x) x"
proof goal_cases
  case 1
  show ?case by (auto intro: mult_mono simp: P_def)
next
  case 2
  show ?case by (auto intro: mult_monos(2) simp: P_def)
next
  case 3
  show ?case unfolding P_def
    by (subst (1 2 3) mult.commute) (auto intro: mult_monos(2) simp: P_def)
next
  case 4
  show ?case by (auto intro: mult_monos(4) simp: P_def)
next
  case 5
  show ?case by (auto intro: mult_monos(1,2) simp: P_def)
next
  case 6
  show ?case by (auto intro: mult_monos(3,4) simp: P_def)
next
  case 7
  show ?case unfolding P_def
    by (subst (1 2 3) mult.commute) (auto intro: mult_monos(1,2))
next
  case 8
  show ?case unfolding P_def
    by (subst (1 2 3) mult.commute) (auto intro: mult_monos(3,4))
next
  case 9
  show ?case
  proof (safe, goal_cases)
    case (1 x)
    from 1(1-4) show ?case unfolding P_def
      by (cases "f x \<ge> 0"; cases "g x \<ge> 0";
          fastforce intro: mult_monos 1(5,6)[THEN order.trans] 1(7,8)[THEN order.trans[rotated]])
  qed
qed


qualified lemma powr_bounds_real:
  fixes f g l1 u1 l2 u2 l u :: "real \<Rightarrow> real"
  defines "P \<equiv> \<lambda>l u x. f x \<in> {l1 x..u1 x} \<longrightarrow> g x \<in> {l2 x..u2 x} \<longrightarrow> f x powr g x \<in> {l..u}"
  shows   "\<forall>x. l1 x \<ge> 0 \<longrightarrow> l1 x \<ge> 1 \<longrightarrow> l2 x \<ge> 0 \<longrightarrow> P (l1 x powr l2 x) (u1 x powr u2 x) x"
    and   "\<forall>x. l1 x \<ge> 0 \<longrightarrow> u1 x \<le> 1 \<longrightarrow> l2 x \<ge> 0 \<longrightarrow> P (l1 x powr u2 x) (u1 x powr l2 x) x"
    and   "\<forall>x. l1 x \<ge> 0 \<longrightarrow> l1 x \<ge> 1 \<longrightarrow> u2 x \<le> 0 \<longrightarrow> P (u1 x powr l2 x) (l1 x powr u2 x) x"
    and   "\<forall>x. l1 x > 0 \<longrightarrow> u1 x \<le> 1 \<longrightarrow> u2 x \<le> 0 \<longrightarrow> P (u1 x powr u2 x) (l1 x powr l2 x) x"

    and   "\<forall>x. l1 x \<ge> 0 \<longrightarrow> l1 x \<le> 1 \<longrightarrow> u1 x \<ge> 1 \<longrightarrow> l2 x \<ge> 0 \<longrightarrow> P (l1 x powr u2 x) (u1 x powr u2 x) x"
    and   "\<forall>x. l1 x > 0 \<longrightarrow> l1 x \<le> 1 \<longrightarrow> u1 x \<ge> 1 \<longrightarrow> u2 x \<le> 0 \<longrightarrow> P (u1 x powr l2 x) (l1 x powr l2 x) x"
    and   "\<forall>x. l1 x \<ge> 0 \<longrightarrow> l1 x \<ge> 1 \<longrightarrow> l2 x \<le> 0 \<longrightarrow> u2 x \<ge> 0 \<longrightarrow> P (u1 x powr l2 x) (u1 x powr u2 x) x"
    and   "\<forall>x. l1 x > 0 \<longrightarrow> u1 x \<le> 1 \<longrightarrow> l2 x \<le> 0 \<longrightarrow> u2 x \<ge> 0 \<longrightarrow> P (l1 x powr u2 x) (l1 x powr l2 x) x"

    and   "\<forall>x. l1 x > 0 \<longrightarrow> l1 x \<le> 1 \<longrightarrow> u1 x \<ge> 1 \<longrightarrow> l2 x \<le> 0 \<longrightarrow> u2 x \<ge> 0 \<longrightarrow> l x \<le> l1 x powr u2 x \<longrightarrow>
             l x \<le> u1 x powr l2 x \<longrightarrow> u x \<ge> l1 x powr l2 x \<longrightarrow> u x \<ge> u1 x powr u2 x \<longrightarrow> P (l x) (u x) x"
proof goal_cases
  case 1
  show ?case by (auto simp: P_def powr_def intro: mult_monos)
next
  case 2
  show ?case by (auto simp: P_def powr_def intro: mult_monos)
next
  case 3
  show ?case by (auto simp: P_def powr_def intro: mult_monos)
next
  case 4
  show ?case by (auto simp: P_def powr_def intro: mult_monos)
next
  case 5
  note comm = mult.commute[of _ "ln x" for x :: real]
  show ?case by (auto simp: P_def powr_def comm intro: mult_monos)
next
  case 6
  note comm = mult.commute[of _ "ln x" for x :: real]
  show ?case by (auto simp: P_def powr_def comm intro: mult_monos)
next
  case 7
  show ?case by (auto simp: P_def powr_def intro: mult_monos)
next
  case 8  
  show ?case 
    by (auto simp: P_def powr_def intro: mult_monos)
next
  case 9
  show ?case unfolding P_def
  proof (safe, goal_cases)
    case (1 x)
    define l' where "l' = (\<lambda>x. min (ln (l1 x) * u2 x) (ln (u1 x) * l2 x))"
    define u' where "u' = (\<lambda>x. max (ln (l1 x) * l2 x) (ln (u1 x) * u2 x))"
    from 1 spec[OF mult_bounds_real(9)[of "\<lambda>x. ln (l1 x)" "\<lambda>x. ln (u1 x)" l2 u2 l' u' 
                                          "\<lambda>x. ln (f x)" g], of x]
      have "ln (f x) * g x \<in> {l' x..u' x}" by (auto simp: powr_def mult.commute l'_def u'_def)
    with 1 have "f x powr g x \<in> {exp (l' x)..exp (u' x)}"
      by (auto simp: powr_def mult.commute)
    also from 1 have "exp (l' x) = min (l1 x powr u2 x) (u1 x powr l2 x)"
      by (auto simp add: l'_def powr_def min_def mult.commute)
    also from 1 have "exp (u' x) = max (l1 x powr l2 x) (u1 x powr u2 x)"
      by (auto simp add: u'_def powr_def max_def mult.commute)
    finally show ?case using 1(5-9) by auto
  qed
qed

qualified lemma powr_right_bounds:
  fixes f g :: "real \<Rightarrow> real"
  shows "\<forall>x. l x \<ge> 0 \<longrightarrow> f x \<in> {l x..u x} \<longrightarrow> g x \<ge> 0 \<longrightarrow> f x powr g x \<in> {l x powr g x..u x powr g x}"
    and "\<forall>x. l x > 0 \<longrightarrow> f x \<in> {l x..u x} \<longrightarrow> g x \<le> 0 \<longrightarrow> f x powr g x \<in> {u x powr g x..l x powr g x}"
  by (auto intro: powr_mono2 powr_mono2')

(* TODO Move *)
lemma powr_mono': "a \<le> (b::real) \<Longrightarrow> x \<ge> 0 \<Longrightarrow> x \<le> 1 \<Longrightarrow> x powr b \<le> x powr a"
  using powr_mono[of "-b" "-a" "inverse x"] by (auto simp: powr_def ln_inverse ln_div field_split_simps)

qualified lemma powr_left_bounds:
  fixes f g :: "real \<Rightarrow> real"
  shows "\<forall>x. f x > 0 \<longrightarrow> g x \<in> {l x..u x} \<longrightarrow> f x \<ge> 1 \<longrightarrow> f x powr g x \<in> {f x powr l x..f x powr u x}"
    and "\<forall>x. f x > 0 \<longrightarrow> g x \<in> {l x..u x} \<longrightarrow> f x \<le> 1 \<longrightarrow> f x powr g x \<in> {f x powr u x..f x powr l x}"
  by (auto intro: powr_mono powr_mono')

qualified lemma powr_nat_bounds_transfer_ge:
  "\<forall>x. l1 x \<ge> 0 \<longrightarrow> f x \<ge> l1 x \<longrightarrow> f x powr g x \<ge> l x \<longrightarrow> powr_nat (f x) (g x) \<ge> l x"
  by (auto simp: powr_nat_def)

qualified lemma powr_nat_bounds_transfer_le:
  "\<forall>x. l1 x > 0 \<longrightarrow> f x \<ge> l1 x \<longrightarrow> f x powr g x \<le> u x \<longrightarrow> powr_nat (f x) (g x) \<le> u x"
  "\<forall>x. l1 x \<ge> 0 \<longrightarrow> l2 x > 0 \<longrightarrow> f x \<ge> l1 x \<longrightarrow> g x \<ge> l2 x \<longrightarrow> 
      f x powr g x \<le> u x \<longrightarrow> powr_nat (f x) (g x) \<le> u x"
  "\<forall>x. l1 x \<ge> 0 \<longrightarrow> u2 x < 0 \<longrightarrow> f x \<ge> l1 x \<longrightarrow> g x \<le> u2 x \<longrightarrow>
      f x powr g x \<le> u x \<longrightarrow> powr_nat (f x) (g x) \<le> u x"
  "\<forall>x. l1 x \<ge> 0 \<longrightarrow> f x \<ge> l1 x \<longrightarrow>  f x powr g x \<le> u x \<longrightarrow> u x \<le> u' x \<longrightarrow> 1 \<le> u' x \<longrightarrow> 
     powr_nat (f x) (g x) \<le> u' x"
  by (auto simp: powr_nat_def)

lemma abs_powr_nat_le: "abs (powr_nat x y) \<le> powr_nat (abs x) y"
  by (simp add: powr_nat_def abs_mult)

qualified lemma powr_nat_bounds_ge_neg:
  assumes "powr_nat (abs x) y \<le> u"
  shows   "powr_nat x y \<ge> -u" "powr_nat x y \<le> u"
proof -
  have "abs (powr_nat x y) \<le> powr_nat (abs x) y"
    by (rule abs_powr_nat_le)
  also have "\<dots> \<le> u" using assms by auto
  finally show "powr_nat x y \<ge> -u" "powr_nat x y \<le> u" by auto
qed

qualified lemma powr_nat_bounds_transfer_abs [eventuallized]:
  "\<forall>x. powr_nat (abs (f x)) (g x) \<le> u x \<longrightarrow> powr_nat (f x) (g x) \<ge> -u x"
  "\<forall>x. powr_nat (abs (f x)) (g x) \<le> u x \<longrightarrow> powr_nat (f x) (g x) \<le> u x"
  using powr_nat_bounds_ge_neg by blast+

qualified lemma eventually_powr_const_nonneg:
  "f \<equiv> f \<Longrightarrow> p \<equiv> p \<Longrightarrow> eventually (\<lambda>x. f x powr p \<ge> (0::real)) at_top"
  by simp

qualified lemma eventually_powr_const_mono_nonneg:
  assumes "p \<ge> (0 :: real)" "eventually (\<lambda>x. l x \<ge> 0) at_top" "eventually (\<lambda>x. l x \<le> f x) at_top"
          "eventually (\<lambda>x. f x \<le> g x) at_top"
  shows   "eventually (\<lambda>x. f x powr p \<le> g x powr p) at_top"
  using assms(2-4) by eventually_elim (auto simp: assms(1) intro!: powr_mono2)

qualified lemma eventually_powr_const_mono_nonpos:
  assumes "p \<le> (0 :: real)" "eventually (\<lambda>x. l x > 0) at_top" "eventually (\<lambda>x. l x \<le> f x) at_top"
          "eventually (\<lambda>x. f x \<le> g x) at_top"
  shows   "eventually (\<lambda>x. f x powr p \<ge> g x powr p) at_top"
  using assms(2-4) by eventually_elim (auto simp: assms(1) intro!: powr_mono2')


qualified lemma eventually_power_mono:
  assumes "eventually (\<lambda>x. 0 \<le> l x) at_top" "eventually (\<lambda>x. l x \<le> f x) at_top"
          "eventually (\<lambda>x. f x \<le> g x) at_top" "n \<equiv> n"
  shows   "eventually (\<lambda>x. f x ^ n \<le> (g x :: real) ^ n) at_top"
  using assms(1-3) by eventually_elim (auto intro: power_mono)

qualified lemma eventually_mono_power_odd:
  assumes "odd n" "eventually (\<lambda>x. f x \<le> (g x :: real)) at_top"
  shows   "eventually (\<lambda>x. f x ^ n \<le> g x ^ n) at_top"
  using assms(2) by eventually_elim (insert assms(1), auto intro: power_mono_odd)


qualified lemma eventually_lower_bound_power_even_nonpos:
  assumes "even n" "eventually (\<lambda>x. u x \<le> (0::real)) at_top"
          "eventually (\<lambda>x. f x \<le> u x) at_top"
  shows   "eventually (\<lambda>x. u x ^ n \<le> f x ^ n) at_top"
  using assms(2-) by eventually_elim (rule power_mono_even, auto simp: assms(1))

qualified lemma eventually_upper_bound_power_even_nonpos:
  assumes "even n" "eventually (\<lambda>x. u x \<le> (0::real)) at_top"
          "eventually (\<lambda>x. l x \<le> f x) at_top" "eventually (\<lambda>x. f x \<le> u x) at_top"
  shows   "eventually (\<lambda>x. f x ^ n \<le> l x ^ n) at_top"
  using assms(2-) by eventually_elim (rule power_mono_even, auto simp: assms(1))

qualified lemma eventually_lower_bound_power_even_indet:
  assumes "even n" "f \<equiv> f"
  shows   "eventually (\<lambda>x. (0::real) \<le> f x ^ n) at_top"
  using assms by (simp add: zero_le_even_power)


qualified lemma eventually_lower_bound_power_indet:
  assumes "eventually (\<lambda>x. l x \<le> f x) at_top"
  assumes "eventually (\<lambda>x. l' x \<le> l x ^ n) at_top" "eventually (\<lambda>x. l' x \<le> 0) at_top"
  shows   "eventually (\<lambda>x. l' x \<le> (f x ^ n :: real)) at_top"
  using assms
proof eventually_elim
  case (elim x)
  thus ?case
    using power_mono_odd[of n "l x" "f x"] zero_le_even_power[of n "f x"]
    by (cases "even n") auto
qed

qualified lemma eventually_upper_bound_power_indet:
  assumes "eventually (\<lambda>x. l x \<le> f x) at_top" "eventually (\<lambda>x. f x \<le> u x) at_top"
          "eventually (\<lambda>x. u' x \<ge> -l x) at_top" "eventually (\<lambda>x. u' x \<ge> u x) at_top" "n \<equiv> n"
  shows   "eventually (\<lambda>x. f x ^ n \<le> (u' x ^ n :: real)) at_top"
  using assms(1-4)
proof eventually_elim
  case (elim x)
  have "f x ^ n \<le> \<bar>f x ^ n\<bar>" by simp
  also have "\<dots> = \<bar>f x\<bar> ^ n" by (simp add: power_abs)
  also from elim have "\<dots> \<le> u' x ^ n" by (intro power_mono) auto
  finally show ?case .
qed

qualified lemma expands_to_imp_exp_ln_eq:
  assumes "(l expands_to L) bs" "eventually (\<lambda>x. l x \<le> f x) at_top"
          "trimmed_pos L" "basis_wf bs"
  shows   "eventually (\<lambda>x. exp (ln (f x)) = f x) at_top"
proof -
  from expands_to_imp_eventually_pos[of bs l L] assms
    have "eventually (\<lambda>x. l x > 0) at_top" by simp
  with assms(2) show ?thesis by eventually_elim simp
qed

qualified lemma expands_to_imp_ln_powr_eq:
  assumes "(l expands_to L) bs" "eventually (\<lambda>x. l x \<le> f x) at_top"
          "trimmed_pos L" "basis_wf bs"
  shows   "eventually (\<lambda>x. ln (f x powr g x) = ln (f x) * g x) at_top"
proof -
  from expands_to_imp_eventually_pos[of bs l L] assms
    have "eventually (\<lambda>x. l x > 0) at_top" by simp
  with assms(2) show ?thesis by eventually_elim (simp add: powr_def)
qed

qualified lemma inverse_bounds_real:
  fixes f l u :: "real \<Rightarrow> real"
  shows "\<forall>x. l x > 0 \<longrightarrow> l x \<le> f x \<longrightarrow> f x \<le> u x \<longrightarrow> inverse (f x) \<in> {inverse (u x)..inverse (l x)}"
    and "\<forall>x. u x < 0 \<longrightarrow> l x \<le> f x \<longrightarrow> f x \<le> u x \<longrightarrow> inverse (f x) \<in> {inverse (u x)..inverse (l x)}"
  by (auto simp: field_simps)

qualified lemma pos_imp_inverse_pos: "\<forall>x::real. f x > 0 \<longrightarrow> inverse (f x) > (0::real)"
  and neg_imp_inverse_neg: "\<forall>x::real. f x < 0 \<longrightarrow> inverse (f x) < (0::real)"
  by auto

qualified lemma transfer_divide_bounds:
  fixes f g :: "real \<Rightarrow> real"
  shows "Trueprop (eventually (\<lambda>x. f x \<in> {h x * inverse (i x)..j x}) at_top) \<equiv>
         Trueprop (eventually (\<lambda>x. f x \<in> {h x / i x..j x}) at_top)"
    and "Trueprop (eventually (\<lambda>x. f x \<in> {j x..h x * inverse (i x)}) at_top) \<equiv>
         Trueprop (eventually (\<lambda>x. f x \<in> {j x..h x / i x}) at_top)"
    and "Trueprop (eventually (\<lambda>x. f x * inverse (g x) \<in> A x) at_top) \<equiv>
         Trueprop (eventually (\<lambda>x. f x / g x \<in> A x) at_top)"
    and "Trueprop (((\<lambda>x. f x * inverse (g x)) expands_to F) bs) \<equiv>
         Trueprop (((\<lambda>x. f x / g x) expands_to F) bs)"
  by (simp_all add: field_simps)

qualified lemma eventually_le_self: "eventually (\<lambda>x::real. f x \<le> (f x :: real)) at_top"
  by simp

qualified lemma max_eventually_eq:
  "eventually (\<lambda>x. f x = (g x :: real)) at_top \<Longrightarrow> eventually (\<lambda>x. max (f x) (g x) = f x) at_top"
  by (erule eventually_mono) simp

qualified lemma min_eventually_eq:
  "eventually (\<lambda>x. f x = (g x :: real)) at_top \<Longrightarrow> eventually (\<lambda>x. min (f x) (g x) = f x) at_top"
  by (erule eventually_mono) simp

qualified lemma
  assumes "eventually (\<lambda>x. f x = (g x :: 'a :: preorder)) F"
  shows   eventually_eq_imp_ge: "eventually (\<lambda>x. f x \<ge> g x) F"
    and   eventually_eq_imp_le: "eventually (\<lambda>x. f x \<le> g x) F"
  by (use assms in eventually_elim; simp)+

qualified lemma eventually_less_imp_le:
  assumes "eventually (\<lambda>x. f x < (g x :: 'a :: order)) F"
  shows   "eventually (\<lambda>x. f x \<le> g x) F"
  using assms by eventually_elim auto

qualified lemma
  fixes f :: "real \<Rightarrow> real"
  shows eventually_abs_ge_0: "eventually (\<lambda>x. abs (f x) \<ge> 0) at_top"
    and nonneg_abs_bounds: "\<forall>x. l x \<ge> 0 \<longrightarrow> f x \<in> {l x..u x} \<longrightarrow> abs (f x) \<in> {l x..u x}" 
    and nonpos_abs_bounds: "\<forall>x. u x \<le> 0 \<longrightarrow> f x \<in> {l x..u x} \<longrightarrow> abs (f x) \<in> {-u x..-l x}" 
    and indet_abs_bounds:
          "\<forall>x. l x \<le> 0 \<longrightarrow> u x \<ge> 0 \<longrightarrow> f x \<in> {l x..u x} \<longrightarrow> -l x \<le> h x \<longrightarrow> u x \<le> h x \<longrightarrow> 
             abs (f x) \<in> {0..h x}"
  by auto

qualified lemma eventually_le_abs_nonneg:
  "eventually (\<lambda>x. l x \<ge> 0) at_top \<Longrightarrow> eventually (\<lambda>x. f x \<ge> l x) at_top \<Longrightarrow>
     eventually (\<lambda>x::real. l x \<le> (\<bar>f x\<bar> :: real)) at_top"
  by (auto elim: eventually_elim2)

qualified lemma eventually_le_abs_nonpos:
  "eventually (\<lambda>x. u x \<le> 0) at_top \<Longrightarrow> eventually (\<lambda>x. f x \<le> u x) at_top \<Longrightarrow>
     eventually (\<lambda>x::real. -u x \<le> (\<bar>f x\<bar> :: real)) at_top"
  by (auto elim: eventually_elim2)

qualified lemma
  fixes f g h :: "'a \<Rightarrow> 'b :: order"
  shows eventually_le_less:"eventually (\<lambda>x. f x \<le> g x) F \<Longrightarrow> eventually (\<lambda>x. g x < h x) F \<Longrightarrow> 
           eventually (\<lambda>x. f x < h x) F"
  and   eventually_less_le:"eventually (\<lambda>x. f x < g x) F \<Longrightarrow> eventually (\<lambda>x. g x \<le> h x) F \<Longrightarrow>
           eventually (\<lambda>x. f x < h x) F"
  by (erule (1) eventually_elim2; erule (1) order.trans le_less_trans less_le_trans)+

qualified lemma eventually_pos_imp_nz [eventuallized]: "\<forall>x. f x > 0 \<longrightarrow> f x \<noteq> (0 :: 'a :: linordered_semiring)"
  and eventually_neg_imp_nz [eventuallized]: "\<forall>x. f x < 0 \<longrightarrow> f x \<noteq> 0"
  by auto

qualified lemma
  fixes f g l1 l2 u1 :: "'a \<Rightarrow> real"
  assumes "eventually (\<lambda>x. l1 x \<le> f x) F"
  assumes "eventually (\<lambda>x. f x \<le> u1 x) F"
  assumes "eventually (\<lambda>x. abs (g x) \<ge> l2 x) F"
  assumes "eventually (\<lambda>x. l2 x \<ge> 0) F"
  shows   bounds_smallo_imp_smallo: "l1 \<in> o[F](l2) \<Longrightarrow> u1 \<in> o[F](l2) \<Longrightarrow> f \<in> o[F](g)"
    and   bounds_bigo_imp_bigo:     "l1 \<in> O[F](l2) \<Longrightarrow> u1 \<in> O[F](l2) \<Longrightarrow> f \<in> O[F](g)"
proof -
  assume *: "l1 \<in> o[F](l2)" "u1 \<in> o[F](l2)"
  show "f \<in> o[F](g)"
  proof (rule landau_o.smallI, goal_cases)
    case (1 c)
    from *[THEN landau_o.smallD[OF _ 1]] and assms show ?case
    proof eventually_elim
      case (elim x)
      from elim have "norm (f x) \<le> c * l2 x" by simp
      also have "\<dots> \<le> c * norm (g x)" using 1 elim by (intro mult_left_mono) auto
      finally show ?case .
    qed
  qed
next
  assume *: "l1 \<in> O[F](l2)" "u1 \<in> O[F](l2)"
  then obtain C1 C2 where **: "C1 > 0" "C2 > 0" "eventually (\<lambda>x. norm (l1 x) \<le> C1 * norm (l2 x)) F"
    "eventually (\<lambda>x. norm (u1 x) \<le> C2 * norm (l2 x)) F" by (auto elim!: landau_o.bigE)
  from this(3,4) and assms have "eventually (\<lambda>x. norm (f x) \<le> max C1 C2 * norm (g x)) F"
  proof eventually_elim
    case (elim x)
    from elim have "norm (f x) \<le> max C1 C2 * l2 x" by (subst max_mult_distrib_right) auto
    also have "\<dots> \<le> max C1 C2 * norm (g x)" using elim ** by (intro mult_left_mono) auto
    finally show ?case .
  qed
  thus "f \<in> O[F](g)" by (rule bigoI)
qed

qualified lemma real_root_mono: "mono (root n)"
  by (cases n) (auto simp: mono_def)

(* TODO: support for rintmod *)

ML_file \<open>multiseries_expansion_bounds.ML\<close>

method_setup real_asymp = \<open>
let
  type flags = {verbose : bool, fallback : bool}
  fun join_flags
        {verbose = verbose1, fallback = fallback1}
        {verbose = verbose2, fallback = fallback2} =
    {verbose = verbose1 orelse verbose2, fallback = fallback1 orelse fallback2}
  val parse_flag =
    (Args.$$$ "verbose" >> K {verbose = true, fallback = false}) ||
    (Args.$$$ "fallback" >> K {verbose = false, fallback = true})
  val default_flags = {verbose = false, fallback = false}
  val parse_flags =
    Scan.optional (Args.parens (Parse.list1 parse_flag)) [] >>
      (fn xs => fold join_flags xs default_flags)
in
  Scan.lift parse_flags --| Method.sections Simplifier.simp_modifiers >>
    (fn flags => SIMPLE_METHOD' o
      (if #fallback flags then Real_Asymp_Basic.tac else Real_Asymp_Bounds.tac) (#verbose flags))
end
\<close> "Semi-automatic decision procedure for asymptotics of exp-log functions"

end

lemma "filterlim (\<lambda>x::real. sin x / x) (nhds 0) at_top"
  by real_asymp

lemma "(\<lambda>x::real. exp (sin x)) \<in> O(\<lambda>_. 1)"
  by real_asymp

lemma "(\<lambda>x::real. exp (real_of_int (floor x))) \<in> \<Theta>(\<lambda>x. exp x)"
  by real_asymp

lemma "(\<lambda>n::nat. n div 2 * ln (n div 2)) \<in> \<Theta>(\<lambda>n::nat. n * ln n)"
  by real_asymp

end
