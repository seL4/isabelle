(* Author:     Johannes Hoelzl, TU Muenchen
   Coercions removed by Dmitriy Traytel *)

theory Approximation
imports
  Complex_Main
  Approximation_Bounds
  "HOL-Library.Code_Target_Numeral_Float"
keywords "approximate" :: diag
begin

section "Implement floatarith"

subsection "Define syntax and semantics"

datatype floatarith
  = Add floatarith floatarith
  | Minus floatarith
  | Mult floatarith floatarith
  | Inverse floatarith
  | Cos floatarith
  | Arctan floatarith
  | Abs floatarith
  | Max floatarith floatarith
  | Min floatarith floatarith
  | Pi
  | Sqrt floatarith
  | Exp floatarith
  | Powr floatarith floatarith
  | Ln floatarith
  | Power floatarith nat
  | Floor floatarith
  | Var nat
  | Num float

fun interpret_floatarith :: "floatarith \<Rightarrow> real list \<Rightarrow> real" where
"interpret_floatarith (Add a b) vs   = (interpret_floatarith a vs) + (interpret_floatarith b vs)" |
"interpret_floatarith (Minus a) vs    = - (interpret_floatarith a vs)" |
"interpret_floatarith (Mult a b) vs   = (interpret_floatarith a vs) * (interpret_floatarith b vs)" |
"interpret_floatarith (Inverse a) vs  = inverse (interpret_floatarith a vs)" |
"interpret_floatarith (Cos a) vs      = cos (interpret_floatarith a vs)" |
"interpret_floatarith (Arctan a) vs   = arctan (interpret_floatarith a vs)" |
"interpret_floatarith (Min a b) vs    = min (interpret_floatarith a vs) (interpret_floatarith b vs)" |
"interpret_floatarith (Max a b) vs    = max (interpret_floatarith a vs) (interpret_floatarith b vs)" |
"interpret_floatarith (Abs a) vs      = \<bar>interpret_floatarith a vs\<bar>" |
"interpret_floatarith Pi vs           = pi" |
"interpret_floatarith (Sqrt a) vs     = sqrt (interpret_floatarith a vs)" |
"interpret_floatarith (Exp a) vs      = exp (interpret_floatarith a vs)" |
"interpret_floatarith (Powr a b) vs   = interpret_floatarith a vs powr interpret_floatarith b vs" |
"interpret_floatarith (Ln a) vs       = ln (interpret_floatarith a vs)" |
"interpret_floatarith (Power a n) vs  = (interpret_floatarith a vs)^n" |
"interpret_floatarith (Floor a) vs      = floor (interpret_floatarith a vs)" |
"interpret_floatarith (Num f) vs      = f" |
"interpret_floatarith (Var n) vs     = vs ! n"

lemma interpret_floatarith_divide:
  "interpret_floatarith (Mult a (Inverse b)) vs =
    (interpret_floatarith a vs) / (interpret_floatarith b vs)"
  unfolding divide_inverse interpret_floatarith.simps ..

lemma interpret_floatarith_diff:
  "interpret_floatarith (Add a (Minus b)) vs =
    (interpret_floatarith a vs) - (interpret_floatarith b vs)"
  unfolding interpret_floatarith.simps by simp

lemma interpret_floatarith_sin:
  "interpret_floatarith (Cos (Add (Mult Pi (Num (Float 1 (- 1)))) (Minus a))) vs =
    sin (interpret_floatarith a vs)"
  unfolding sin_cos_eq interpret_floatarith.simps
    interpret_floatarith_divide interpret_floatarith_diff
  by auto


subsection "Implement approximation function"

fun lift_bin :: "(float interval) option \<Rightarrow> (float interval) option \<Rightarrow> (float interval \<Rightarrow> float interval \<Rightarrow> (float interval) option) \<Rightarrow> (float interval) option" where
"lift_bin (Some ivl1) (Some ivl2) f = f ivl1 ivl2" |
"lift_bin a b f = None"

fun lift_bin' :: "(float interval) option \<Rightarrow> (float interval) option \<Rightarrow> (float interval \<Rightarrow> float interval \<Rightarrow> float interval) \<Rightarrow> (float interval) option" where
"lift_bin' (Some ivl1) (Some ivl2) f = Some (f ivl1 ivl2)" |
"lift_bin' a b f = None"

fun lift_un :: "float interval option \<Rightarrow> (float interval \<Rightarrow> float interval option) \<Rightarrow> float interval option" where
"lift_un (Some ivl) f = f ivl" |
"lift_un b f = None"

lemma lift_un_eq:\<comment> \<open>TODO\<close> "lift_un x f = Option.bind x f"
  by (cases x) auto

fun lift_un' :: "(float interval) option \<Rightarrow> (float interval \<Rightarrow> (float interval)) \<Rightarrow> (float interval) option" where
"lift_un' (Some ivl1) f = Some (f ivl1)" |
"lift_un' b f = None"

definition bounded_by :: "real list \<Rightarrow> (float interval) option list \<Rightarrow> bool" where
  "bounded_by xs vs \<longleftrightarrow> (\<forall> i < length vs. case vs ! i of None \<Rightarrow> True | Some ivl \<Rightarrow> xs ! i \<in>\<^sub>r ivl)"

lemma bounded_byE:
  assumes "bounded_by xs vs"
  shows "\<And> i. i < length vs \<Longrightarrow> case vs ! i of None \<Rightarrow> True
         | Some ivl \<Rightarrow> xs ! i \<in>\<^sub>r ivl"
  using assms
  by (auto simp: bounded_by_def)

lemma bounded_by_update:
  assumes "bounded_by xs vs"
    and bnd: "xs ! i \<in>\<^sub>r ivl"
  shows "bounded_by xs (vs[i := Some ivl])"
  using assms
  by (cases "i < length vs") (auto simp: bounded_by_def nth_list_update split: option.splits)

lemma bounded_by_None: "bounded_by xs (replicate (length xs) None)"
  unfolding bounded_by_def by auto

fun approx approx' :: "nat \<Rightarrow> floatarith \<Rightarrow> (float interval) option list \<Rightarrow> (float interval) option"
  where
    "approx' prec a bs          = (case (approx prec a bs) of Some ivl \<Rightarrow> Some (round_interval prec ivl) | None \<Rightarrow> None)" |
    "approx prec (Add a b) bs   = lift_bin' (approx' prec a bs) (approx' prec b bs) (plus_float_interval prec)" |
    "approx prec (Minus a) bs   = lift_un' (approx' prec a bs) uminus" |
    "approx prec (Mult a b) bs  = lift_bin' (approx' prec a bs) (approx' prec b bs) (mult_float_interval prec)" |
    "approx prec (Inverse a) bs = lift_un (approx' prec a bs) (inverse_float_interval prec)" |
    "approx prec (Cos a) bs     = lift_un' (approx' prec a bs) (cos_float_interval prec)" |
    "approx prec Pi bs          = Some (pi_float_interval prec)" |
    "approx prec (Min a b) bs   = lift_bin' (approx' prec a bs) (approx' prec b bs) (min_interval)" |
    "approx prec (Max a b) bs   = lift_bin' (approx' prec a bs) (approx' prec b bs) (max_interval)" |
    "approx prec (Abs a) bs     = lift_un' (approx' prec a bs) (abs_interval)" |
    "approx prec (Arctan a) bs  = lift_un' (approx' prec a bs) (arctan_float_interval prec)" |
    "approx prec (Sqrt a) bs    = lift_un' (approx' prec a bs) (sqrt_float_interval prec)" |
    "approx prec (Exp a) bs     = lift_un' (approx' prec a bs) (exp_float_interval prec)" |
    "approx prec (Powr a b) bs  = lift_bin (approx' prec a bs) (approx' prec b bs) (powr_float_interval prec)" |
    "approx prec (Ln a) bs      = lift_un (approx' prec a bs) (ln_float_interval prec)" |
    "approx prec (Power a n) bs = lift_un' (approx' prec a bs) (power_float_interval prec n)" |
    "approx prec (Floor a) bs = lift_un' (approx' prec a bs) (floor_float_interval)" |
    "approx prec (Num f) bs     = Some (interval_of f)" |
    "approx prec (Var i) bs    = (if i < length bs then bs ! i else None)"

lemma approx_approx':
  assumes Pa: "\<And>ivl. approx prec a vs = Some ivl \<Longrightarrow> interpret_floatarith a xs \<in>\<^sub>r ivl"
    and approx': "approx' prec a vs = Some ivl"
  shows "interpret_floatarith a xs \<in>\<^sub>r ivl"
proof -
  obtain ivl' where S: "approx prec a vs = Some ivl'" and ivl_def: "ivl = round_interval prec ivl'"
    using approx' unfolding approx'.simps by (cases "approx prec a vs") auto
  show ?thesis
    by (auto simp: ivl_def intro!: in_round_intervalI Pa[OF S])
qed

lemma approx:
  assumes "bounded_by xs vs"
    and "approx prec arith vs = Some ivl"
  shows "interpret_floatarith arith xs \<in>\<^sub>r ivl"
  using \<open>approx prec arith vs = Some ivl\<close>
  using  \<open>bounded_by xs vs\<close>[THEN bounded_byE]
  by (induct arith arbitrary: ivl)
    (force split: option.splits if_splits
      intro!: plus_float_intervalI mult_float_intervalI uminus_in_float_intervalI
      inverse_float_interval_eqI abs_in_float_intervalI
      min_intervalI max_intervalI
      cos_float_intervalI
      arctan_float_intervalI pi_float_interval sqrt_float_intervalI exp_float_intervalI
      powr_float_interval_eqI ln_float_interval_eqI power_float_intervalI floor_float_intervalI
      intro: in_round_intervalI)+

datatype form = Bound floatarith floatarith floatarith form
              | Assign floatarith floatarith form
              | Less floatarith floatarith
              | LessEqual floatarith floatarith
              | AtLeastAtMost floatarith floatarith floatarith
              | Conj form form
              | Disj form form

fun interpret_form :: "form \<Rightarrow> real list \<Rightarrow> bool" where
"interpret_form (Bound x a b f) vs = (interpret_floatarith x vs \<in> { interpret_floatarith a vs .. interpret_floatarith b vs } \<longrightarrow> interpret_form f vs)" |
"interpret_form (Assign x a f) vs  = (interpret_floatarith x vs = interpret_floatarith a vs \<longrightarrow> interpret_form f vs)" |
"interpret_form (Less a b) vs      = (interpret_floatarith a vs < interpret_floatarith b vs)" |
"interpret_form (LessEqual a b) vs = (interpret_floatarith a vs \<le> interpret_floatarith b vs)" |
"interpret_form (AtLeastAtMost x a b) vs = (interpret_floatarith x vs \<in> { interpret_floatarith a vs .. interpret_floatarith b vs })" |
"interpret_form (Conj f g) vs \<longleftrightarrow> interpret_form f vs \<and> interpret_form g vs" |
"interpret_form (Disj f g) vs \<longleftrightarrow> interpret_form f vs \<or> interpret_form g vs"

fun approx_form' and approx_form :: "nat \<Rightarrow> form \<Rightarrow> (float interval) option list \<Rightarrow> nat list \<Rightarrow> bool" where
"approx_form' prec f 0 n ivl bs ss = approx_form prec f (bs[n := Some ivl]) ss" |
"approx_form' prec f (Suc s) n ivl bs ss =
  (let (ivl1, ivl2) = split_float_interval ivl
   in (if approx_form' prec f s n ivl1 bs ss then approx_form' prec f s n ivl2 bs ss else False))" |
"approx_form prec (Bound (Var n) a b f) bs ss =
   (case (approx prec a bs, approx prec b bs)
   of (Some ivl1, Some ivl2) \<Rightarrow> approx_form' prec f (ss ! n) n (sup ivl1 ivl2) bs ss
    | _ \<Rightarrow> False)" |
"approx_form prec (Assign (Var n) a f) bs ss =
   (case (approx prec a bs)
   of (Some ivl) \<Rightarrow> approx_form' prec f (ss ! n) n ivl bs ss
    | _ \<Rightarrow> False)" |
"approx_form prec (Less a b) bs ss =
   (case (approx prec a bs, approx prec b bs)
   of (Some ivl, Some ivl') \<Rightarrow> float_plus_up prec (upper ivl) (-lower ivl') < 0
    | _ \<Rightarrow> False)" |
"approx_form prec (LessEqual a b) bs ss =
   (case (approx prec a bs, approx prec b bs)
   of (Some ivl, Some ivl') \<Rightarrow> float_plus_up prec (upper ivl) (-lower ivl') \<le> 0
    | _ \<Rightarrow> False)" |
"approx_form prec (AtLeastAtMost x a b) bs ss =
   (case (approx prec x bs, approx prec a bs, approx prec b bs)
   of (Some ivlx, Some ivl, Some ivl') \<Rightarrow>
      float_plus_up prec (upper ivl) (-lower ivlx) \<le> 0 \<and>
      float_plus_up prec (upper ivlx) (-lower ivl') \<le> 0
    | _ \<Rightarrow> False)" |
"approx_form prec (Conj a b) bs ss \<longleftrightarrow> approx_form prec a bs ss \<and> approx_form prec b bs ss" |
"approx_form prec (Disj a b) bs ss \<longleftrightarrow> approx_form prec a bs ss \<or> approx_form prec b bs ss" |
"approx_form _ _ _ _ = False"

lemma lazy_conj: "(if A then B else False) = (A \<and> B)" by simp

lemma approx_form_approx_form':
  assumes "approx_form' prec f s n ivl bs ss"
    and "(x::real) \<in>\<^sub>r ivl"
  obtains ivl' where "x \<in>\<^sub>r ivl'"
    and "approx_form prec f (bs[n := Some ivl']) ss"
using assms proof (induct s arbitrary: ivl)
  case 0
  from this(1)[of ivl] this(2,3)
  show thesis by auto
next
  case (Suc s)
  then obtain ivl1 ivl2 where ivl_split: "split_float_interval ivl = (ivl1, ivl2)"
    by (fastforce dest: split_float_intervalD)
  from split_float_interval_realD[OF this \<open>x \<in>\<^sub>r ivl\<close>]
  consider "x \<in>\<^sub>r ivl1" | "x \<in>\<^sub>r ivl2"
    by atomize_elim
  then show thesis
  proof cases
    case *: 1
    from Suc.hyps[OF _ _ *] Suc.prems
    show ?thesis
      by (simp add: lazy_conj ivl_split split: prod.splits)
  next
    case *: 2
    from Suc.hyps[OF _ _ *] Suc.prems
    show ?thesis
      by (simp add: lazy_conj ivl_split split: prod.splits)
  qed
qed

lemma approx_form_aux:
  assumes "approx_form prec f vs ss"
    and "bounded_by xs vs"
  shows "interpret_form f xs"
using assms proof (induct f arbitrary: vs)
  case (Bound x a b f)
  then obtain n
    where x_eq: "x = Var n" by (cases x) auto

  with Bound.prems obtain ivl1 ivl2
    where l_eq: "approx prec a vs = Some ivl1"
    and u_eq: "approx prec b vs = Some ivl2"
    and approx_form': "approx_form' prec f (ss ! n) n (sup ivl1 ivl2) vs ss"
    by (cases "approx prec a vs", simp) (cases "approx prec b vs", auto)

  have "interpret_form f xs"
    if "xs ! n \<in> { interpret_floatarith a xs .. interpret_floatarith b xs }"
  proof -
    from approx[OF Bound.prems(2) l_eq] and approx[OF Bound.prems(2) u_eq] that
    have "xs ! n \<in>\<^sub>r (sup ivl1 ivl2)"
      by (auto simp: set_of_eq sup_float_def max_def inf_float_def min_def)

    from approx_form_approx_form'[OF approx_form' this]
    obtain ivlx where bnds: "xs ! n \<in>\<^sub>r ivlx"
      and approx_form: "approx_form prec f (vs[n := Some ivlx]) ss" .

    from \<open>bounded_by xs vs\<close> bnds have "bounded_by xs (vs[n := Some ivlx])"
      by (rule bounded_by_update)
    with Bound.hyps[OF approx_form] show ?thesis
      by blast
  qed
  thus ?case
    using interpret_form.simps x_eq and interpret_floatarith.simps by simp
next
  case (Assign x a f)
  then obtain n where x_eq: "x = Var n"
    by (cases x) auto

  with Assign.prems obtain ivl
    where bnd_eq: "approx prec a vs = Some ivl"
    and x_eq: "x = Var n"
    and approx_form': "approx_form' prec f (ss ! n) n ivl vs ss"
    by (cases "approx prec a vs") auto

  have "interpret_form f xs"
    if bnds: "xs ! n = interpret_floatarith a xs"
  proof -
    from approx[OF Assign.prems(2) bnd_eq] bnds
    have "xs ! n \<in>\<^sub>r ivl" by auto
    from approx_form_approx_form'[OF approx_form' this]
    obtain ivlx where bnds: "xs ! n \<in>\<^sub>r ivlx"
      and approx_form: "approx_form prec f (vs[n := Some ivlx]) ss" .

    from \<open>bounded_by xs vs\<close> bnds have "bounded_by xs (vs[n := Some ivlx])"
      by (rule bounded_by_update)
    with Assign.hyps[OF approx_form] show ?thesis
      by blast
  qed
  thus ?case
    using interpret_form.simps x_eq and interpret_floatarith.simps by simp
next
  case (Less a b)
  then obtain ivl ivl'
    where l_eq: "approx prec a vs = Some ivl"
      and u_eq: "approx prec b vs = Some ivl'"
      and inequality: "real_of_float (float_plus_up prec (upper ivl) (-lower ivl')) < 0"
    by (cases "approx prec a vs", auto, cases "approx prec b vs", auto)
  from le_less_trans[OF float_plus_up inequality]
    approx[OF Less.prems(2) l_eq] approx[OF Less.prems(2) u_eq]
  show ?case by (auto simp: set_of_eq)
next
  case (LessEqual a b)
  then obtain ivl ivl'
    where l_eq: "approx prec a vs = Some ivl"
      and u_eq: "approx prec b vs = Some ivl'"
      and inequality: "real_of_float (float_plus_up prec (upper ivl) (-lower ivl')) \<le> 0"
    by (cases "approx prec a vs", auto, cases "approx prec b vs", auto)
  from order_trans[OF float_plus_up inequality]
    approx[OF LessEqual.prems(2) l_eq] approx[OF LessEqual.prems(2) u_eq]
  show ?case by (auto simp: set_of_eq)
next
  case (AtLeastAtMost x a b)
  then obtain ivlx ivl ivl'
    where x_eq: "approx prec x vs = Some ivlx"
      and l_eq: "approx prec a vs = Some ivl"
      and u_eq: "approx prec b vs = Some ivl'"
    and inequality: "real_of_float (float_plus_up prec (upper ivl) (-lower ivlx)) \<le> 0"
      "real_of_float (float_plus_up prec (upper ivlx) (-lower ivl')) \<le> 0"
    by (cases "approx prec x vs", auto,
      cases "approx prec a vs", auto,
      cases "approx prec b vs", auto)
  from order_trans[OF float_plus_up inequality(1)] order_trans[OF float_plus_up inequality(2)]
    approx[OF AtLeastAtMost.prems(2) l_eq] approx[OF AtLeastAtMost.prems(2) u_eq] approx[OF AtLeastAtMost.prems(2) x_eq]
  show ?case by (auto simp: set_of_eq)
qed auto

lemma approx_form:
  assumes "n = length xs"
    and "approx_form prec f (replicate n None) ss"
  shows "interpret_form f xs"
  using approx_form_aux[OF _ bounded_by_None] assms by auto


subsection \<open>Implementing Taylor series expansion\<close>

fun isDERIV :: "nat \<Rightarrow> floatarith \<Rightarrow> real list \<Rightarrow> bool" where
"isDERIV x (Add a b) vs         = (isDERIV x a vs \<and> isDERIV x b vs)" |
"isDERIV x (Mult a b) vs        = (isDERIV x a vs \<and> isDERIV x b vs)" |
"isDERIV x (Minus a) vs         = isDERIV x a vs" |
"isDERIV x (Inverse a) vs       = (isDERIV x a vs \<and> interpret_floatarith a vs \<noteq> 0)" |
"isDERIV x (Cos a) vs           = isDERIV x a vs" |
"isDERIV x (Arctan a) vs        = isDERIV x a vs" |
"isDERIV x (Min a b) vs         = False" |
"isDERIV x (Max a b) vs         = False" |
"isDERIV x (Abs a) vs           = False" |
"isDERIV x Pi vs                = True" |
"isDERIV x (Sqrt a) vs          = (isDERIV x a vs \<and> interpret_floatarith a vs > 0)" |
"isDERIV x (Exp a) vs           = isDERIV x a vs" |
"isDERIV x (Powr a b) vs        =
    (isDERIV x a vs \<and> isDERIV x b vs \<and> interpret_floatarith a vs > 0)" |
"isDERIV x (Ln a) vs            = (isDERIV x a vs \<and> interpret_floatarith a vs > 0)" |
"isDERIV x (Floor a) vs         = (isDERIV x a vs \<and> interpret_floatarith a vs \<notin> \<int>)" |
"isDERIV x (Power a 0) vs       = True" |
"isDERIV x (Power a (Suc n)) vs = isDERIV x a vs" |
"isDERIV x (Num f) vs           = True" |
"isDERIV x (Var n) vs          = True"

fun DERIV_floatarith :: "nat \<Rightarrow> floatarith \<Rightarrow> floatarith" where
"DERIV_floatarith x (Add a b)         = Add (DERIV_floatarith x a) (DERIV_floatarith x b)" |
"DERIV_floatarith x (Mult a b)        = Add (Mult a (DERIV_floatarith x b)) (Mult (DERIV_floatarith x a) b)" |
"DERIV_floatarith x (Minus a)         = Minus (DERIV_floatarith x a)" |
"DERIV_floatarith x (Inverse a)       = Minus (Mult (DERIV_floatarith x a) (Inverse (Power a 2)))" |
"DERIV_floatarith x (Cos a)           = Minus (Mult (Cos (Add (Mult Pi (Num (Float 1 (- 1)))) (Minus a))) (DERIV_floatarith x a))" |
"DERIV_floatarith x (Arctan a)        = Mult (Inverse (Add (Num 1) (Power a 2))) (DERIV_floatarith x a)" |
"DERIV_floatarith x (Min a b)         = Num 0" |
"DERIV_floatarith x (Max a b)         = Num 0" |
"DERIV_floatarith x (Abs a)           = Num 0" |
"DERIV_floatarith x Pi                = Num 0" |
"DERIV_floatarith x (Sqrt a)          = (Mult (Inverse (Mult (Sqrt a) (Num 2))) (DERIV_floatarith x a))" |
"DERIV_floatarith x (Exp a)           = Mult (Exp a) (DERIV_floatarith x a)" |
"DERIV_floatarith x (Powr a b)        =
   Mult (Powr a b) (Add (Mult (DERIV_floatarith x b) (Ln a)) (Mult (Mult (DERIV_floatarith x a) b) (Inverse a)))" |
"DERIV_floatarith x (Ln a)            = Mult (Inverse a) (DERIV_floatarith x a)" |
"DERIV_floatarith x (Power a 0)       = Num 0" |
"DERIV_floatarith x (Power a (Suc n)) = Mult (Num (Float (int (Suc n)) 0)) (Mult (Power a n) (DERIV_floatarith x a))" |
"DERIV_floatarith x (Floor a)         = Num 0" |
"DERIV_floatarith x (Num f)           = Num 0" |
"DERIV_floatarith x (Var n)          = (if x = n then Num 1 else Num 0)"

lemma has_real_derivative_powr':
  fixes f g :: "real \<Rightarrow> real"
  assumes "(f has_real_derivative f') (at x)"
  assumes "(g has_real_derivative g') (at x)"
  assumes "f x > 0"
  defines "h \<equiv> \<lambda>x. f x powr g x * (g' * ln (f x) + f' * g x / f x)"
  shows   "((\<lambda>x. f x powr g x) has_real_derivative h x) (at x)"
proof (subst DERIV_cong_ev[OF refl _ refl])
  from assms have "isCont f x"
    by (simp add: DERIV_continuous)
  hence "f \<midarrow>x\<rightarrow> f x" by (simp add: continuous_at)
  with \<open>f x > 0\<close> have "eventually (\<lambda>x. f x > 0) (nhds x)"
    by (auto simp: tendsto_at_iff_tendsto_nhds dest: order_tendstoD)
  thus "eventually (\<lambda>x. f x powr g x = exp (g x * ln (f x))) (nhds x)"
    by eventually_elim (simp add: powr_def)
next
  from assms show "((\<lambda>x. exp (g x * ln (f x))) has_real_derivative h x) (at x)"
    by (auto intro!: derivative_eq_intros simp: h_def powr_def)
qed

lemma DERIV_floatarith:
  assumes "n < length vs"
  assumes isDERIV: "isDERIV n f (vs[n := x])"
  shows "DERIV (\<lambda> x'. interpret_floatarith f (vs[n := x'])) x :>
               interpret_floatarith (DERIV_floatarith n f) (vs[n := x])"
   (is "DERIV (?i f) x :> _")
using isDERIV
proof (induct f arbitrary: x)
  case (Inverse a)
  thus ?case
    by (auto intro!: derivative_eq_intros simp add: algebra_simps power2_eq_square)
next
  case (Cos a)
  thus ?case
    by (auto intro!: derivative_eq_intros
           simp del: interpret_floatarith.simps(5)
           simp add: interpret_floatarith_sin interpret_floatarith.simps(5)[of a])
next
  case (Power a n)
  thus ?case
    by (cases n) (auto intro!: derivative_eq_intros simp del: power_Suc)
next
  case (Floor a)
  thus ?case
    by (auto intro!: derivative_eq_intros DERIV_isCont floor_has_real_derivative)
next
  case (Ln a)
  thus ?case by (auto intro!: derivative_eq_intros simp add: divide_inverse)
next
  case (Var i)
  thus ?case using \<open>n < length vs\<close> by auto
next
  case (Powr a b)
  note [derivative_intros] = has_real_derivative_powr'
  from Powr show ?case
    by (auto intro!: derivative_eq_intros simp: field_simps)
qed (auto intro!: derivative_eq_intros)

declare approx.simps[simp del]

fun isDERIV_approx :: "nat \<Rightarrow> nat \<Rightarrow> floatarith \<Rightarrow> (float interval) option list \<Rightarrow> bool" where
"isDERIV_approx prec x (Add a b) vs         = (isDERIV_approx prec x a vs \<and> isDERIV_approx prec x b vs)" |
"isDERIV_approx prec x (Mult a b) vs        = (isDERIV_approx prec x a vs \<and> isDERIV_approx prec x b vs)" |
"isDERIV_approx prec x (Minus a) vs         = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Inverse a) vs       =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some ivl \<Rightarrow> 0 < lower ivl \<or> upper ivl < 0 | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Cos a) vs           = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Arctan a) vs        = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Min a b) vs         = False" |
"isDERIV_approx prec x (Max a b) vs         = False" |
"isDERIV_approx prec x (Abs a) vs           = False" |
"isDERIV_approx prec x Pi vs                = True" |
"isDERIV_approx prec x (Sqrt a) vs          =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some ivl \<Rightarrow> 0 < lower ivl | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Exp a) vs           = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Powr a b) vs        =
  (isDERIV_approx prec x a vs \<and> isDERIV_approx prec x b vs \<and> (case approx prec a vs of Some ivl \<Rightarrow> 0 < lower ivl | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Ln a) vs            =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some ivl \<Rightarrow> 0 < lower ivl | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Power a 0) vs       = True" |
"isDERIV_approx prec x (Floor a) vs         =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some ivl \<Rightarrow> lower ivl > floor (upper ivl) \<and> upper ivl < ceiling (lower ivl) | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Power a (Suc n)) vs = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Num f) vs           = True" |
"isDERIV_approx prec x (Var n) vs           = True"

lemma isDERIV_approx:
  assumes "bounded_by xs vs"
    and isDERIV_approx: "isDERIV_approx prec x f vs"
  shows "isDERIV x f xs"
  using isDERIV_approx
proof (induct f)
  case (Inverse a)
  then obtain ivl where approx_Some: "approx prec a vs = Some ivl"
    and *: "0 < lower ivl \<or> upper ivl < 0"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some]
  have "interpret_floatarith a xs \<noteq> 0" by (auto simp: set_of_eq)
  thus ?case using Inverse by auto
next
  case (Ln a)
  then obtain ivl where approx_Some: "approx prec a vs = Some ivl"
    and *: "0 < lower ivl"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some]
  have "0 < interpret_floatarith a xs" by (auto simp: set_of_eq)
  thus ?case using Ln by auto
next
  case (Sqrt a)
  then obtain ivl where approx_Some: "approx prec a vs = Some ivl"
    and *: "0 < lower ivl"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some]
  have "0 < interpret_floatarith a xs" by (auto simp: set_of_eq)
  thus ?case using Sqrt by auto
next
  case (Power a n)
  thus ?case by (cases n) auto
next
  case (Powr a b)
  from Powr obtain ivl1 where a: "approx prec a vs = Some ivl1"
    and pos: "0 < lower ivl1"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> a]
  have "0 < interpret_floatarith a xs" by (auto simp: set_of_eq)
  with Powr show ?case by auto
next
  case (Floor a)
  then obtain ivl where approx_Some: "approx prec a vs = Some ivl"
    and "real_of_int \<lfloor>real_of_float (upper ivl)\<rfloor> < real_of_float (lower ivl)"
      "real_of_float (upper ivl) < real_of_int \<lceil>real_of_float (lower ivl)\<rceil>"
    and "isDERIV x a xs"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some] le_floor_iff
  show ?case
    by (force elim!: Ints_cases simp: set_of_eq)
qed auto

lemma bounded_by_update_var:
  assumes "bounded_by xs vs"
    and "vs ! i = Some ivl"
    and bnd: "x \<in>\<^sub>r ivl"
  shows "bounded_by (xs[i := x]) vs"
  using assms
  using nth_list_update
  by (cases "i < length xs")
    (force simp: bounded_by_def  split: option.splits)+

lemma isDERIV_approx':
  assumes "bounded_by xs vs"
    and vs_x: "vs ! x = Some ivl"
    and X_in: "X \<in>\<^sub>r ivl"
    and approx: "isDERIV_approx prec x f vs"
  shows "isDERIV x f (xs[x := X])"
proof -
  from bounded_by_update_var[OF \<open>bounded_by xs vs\<close> vs_x X_in] approx
  show ?thesis by (rule isDERIV_approx)
qed

lemma DERIV_approx:
  assumes "n < length xs"
    and bnd: "bounded_by xs vs"
    and isD: "isDERIV_approx prec n f vs"
    and app: "approx prec (DERIV_floatarith n f) vs = Some ivl" (is "approx _ ?D _ = _")
  shows "\<exists>(x::real). x \<in>\<^sub>r ivl \<and>
             DERIV (\<lambda> x. interpret_floatarith f (xs[n := x])) (xs!n) :> x"
         (is "\<exists> x. _ \<and> DERIV (?i f) _ :> _")
proof (rule exI[of _ "?i ?D (xs!n)"], rule conjI)
  let "?i f" = "\<lambda>x. interpret_floatarith f (xs[n := x])"
  from approx[OF bnd app]
  show "?i ?D (xs!n) \<in>\<^sub>r ivl"
    using \<open>n < length xs\<close> by auto
  from DERIV_floatarith[OF \<open>n < length xs\<close>, of f "xs!n"] isDERIV_approx[OF bnd isD]
  show "DERIV (?i f) (xs!n) :> (?i ?D (xs!n))"
    by simp
qed

lemma lift_bin_aux:
  assumes lift_bin_Some: "lift_bin a b f = Some ivl"
  obtains ivl1 ivl2
  where "a = Some ivl1"
    and "b = Some ivl2"
    and "f ivl1 ivl2 = Some ivl"
  using assms by (cases a, simp, cases b, simp, auto)


fun approx_tse where
"approx_tse prec n 0 c k f bs = approx prec f bs" |
"approx_tse prec n (Suc s) c k f bs =
  (if isDERIV_approx prec n f bs then
    lift_bin (approx prec f (bs[n := Some (interval_of c)]))
             (approx_tse prec n s c (Suc k) (DERIV_floatarith n f) bs)
             (\<lambda>ivl1 ivl2. approx prec
                 (Add (Var 0)
                      (Mult (Inverse (Num (Float (int k) 0)))
                                 (Mult (Add (Var (Suc (Suc 0))) (Minus (Num c)))
                                       (Var (Suc 0))))) [Some ivl1, Some ivl2, bs!n])
  else approx prec f bs)"

lemma bounded_by_Cons:
  assumes bnd: "bounded_by xs vs"
    and x: "x \<in>\<^sub>r ivl"
  shows "bounded_by (x#xs) ((Some ivl)#vs)"
proof -
  have "case ((Some ivl)#vs) ! i of Some ivl \<Rightarrow> (x#xs)!i \<in>\<^sub>r ivl | None \<Rightarrow> True"
    if *: "i < length ((Some ivl)#vs)" for i
  proof (cases i)
    case 0
    with x show ?thesis by auto
  next
    case (Suc i)
    with * have "i < length vs" by auto
    from bnd[THEN bounded_byE, OF this]
    show ?thesis unfolding Suc nth_Cons_Suc .
  qed
  thus ?thesis
    by (auto simp add: bounded_by_def)
qed

lemma approx_tse_generic:
  assumes "bounded_by xs vs"
    and bnd_c: "bounded_by (xs[x := c]) vs"
    and "x < length vs" and "x < length xs"
    and bnd_x: "vs ! x = Some ivlx"
    and ate: "approx_tse prec x s c k f vs = Some ivl"
  shows "\<exists> n. (\<forall> m < n. \<forall> (z::real) \<in> set_of (real_interval ivlx).
      DERIV (\<lambda> y. interpret_floatarith ((DERIV_floatarith x ^^ m) f) (xs[x := y])) z :>
            (interpret_floatarith ((DERIV_floatarith x ^^ (Suc m)) f) (xs[x := z])))
   \<and> (\<forall> (t::real) \<in> set_of (real_interval ivlx).  (\<Sum> i = 0..<n. inverse (real (\<Prod> j \<in> {k..<k+i}. j)) *
                  interpret_floatarith ((DERIV_floatarith x ^^ i) f) (xs[x := c]) *
                  (xs!x - c)^i) +
      inverse (real (\<Prod> j \<in> {k..<k+n}. j)) *
      interpret_floatarith ((DERIV_floatarith x ^^ n) f) (xs[x := t]) *
      (xs!x - c)^n \<in>\<^sub>r ivl)" (is "\<exists> n. ?taylor f k ivl n")
  using ate
proof (induct s arbitrary: k f ivl)
  case 0
  {
    fix t::real assume "t \<in>\<^sub>r ivlx"
    note bounded_by_update_var[OF \<open>bounded_by xs vs\<close> bnd_x this]
    from approx[OF this 0[unfolded approx_tse.simps]]
    have "(interpret_floatarith f (xs[x := t])) \<in>\<^sub>r ivl"
      by (auto simp add: algebra_simps)
  }
  thus ?case by (auto intro!: exI[of _ 0])
next
  case (Suc s)
  show ?case
  proof (cases "isDERIV_approx prec x f vs")
    case False
    note ap = Suc.prems[unfolded approx_tse.simps if_not_P[OF False]]
    {
      fix t::real assume "t \<in>\<^sub>r ivlx"
      note bounded_by_update_var[OF \<open>bounded_by xs vs\<close> bnd_x this]
      from approx[OF this ap]
      have "(interpret_floatarith f (xs[x := t])) \<in>\<^sub>r ivl"
        by (auto simp add: algebra_simps)
    }
    thus ?thesis by (auto intro!: exI[of _ 0])
  next
    case True
    with Suc.prems
    obtain ivl1 ivl2
      where a: "approx prec f (vs[x := Some (interval_of c)]) = Some ivl1"
        and ate: "approx_tse prec x s c (Suc k) (DERIV_floatarith x f) vs = Some ivl2"
        and final: "approx prec
          (Add (Var 0)
               (Mult (Inverse (Num (Float (int k) 0)))
                     (Mult (Add (Var (Suc (Suc 0))) (Minus (Num c)))
                           (Var (Suc 0))))) [Some ivl1, Some ivl2, vs!x] = Some ivl"
      by (auto elim!: lift_bin_aux)

    from bnd_c \<open>x < length xs\<close>
    have bnd: "bounded_by (xs[x:=c]) (vs[x:= Some (interval_of c)])"
      by (auto intro!: bounded_by_update)

    from approx[OF this a]
    have f_c: "interpret_floatarith ((DERIV_floatarith x ^^ 0) f) (xs[x := c]) \<in>\<^sub>r ivl1"
              (is "?f 0 (real_of_float c) \<in> _")
      by auto

    have funpow_Suc[symmetric]: "(f ^^ Suc n) x = (f ^^ n) (f x)"
      for f :: "'a \<Rightarrow> 'a" and n :: nat and x :: 'a
      by (induct n) auto
    from Suc.hyps[OF ate, unfolded this] obtain n
      where DERIV_hyp: "\<And>m z. \<lbrakk> m < n ; (z::real) \<in>\<^sub>r ivlx \<rbrakk> \<Longrightarrow>
        DERIV (?f (Suc m)) z :> ?f (Suc (Suc m)) z"
      and hyp: "\<forall>t \<in> set_of (real_interval ivlx).
        (\<Sum> i = 0..<n. inverse (real (\<Prod> j \<in> {Suc k..<Suc k + i}. j)) * ?f (Suc i) c * (xs!x - c)^i) +
          inverse (real (\<Prod> j \<in> {Suc k..<Suc k + n}. j)) * ?f (Suc n) t * (xs!x - c)^n \<in>\<^sub>r ivl2"
          (is "\<forall> t \<in> _. ?X (Suc k) f n t \<in> _")
      by blast

    have DERIV: "DERIV (?f m) z :> ?f (Suc m) z"
      if "m < Suc n" and bnd_z: "z \<in>\<^sub>r ivlx" for m and z::real
    proof (cases m)
      case 0
      with DERIV_floatarith[OF \<open>x < length xs\<close>
        isDERIV_approx'[OF \<open>bounded_by xs vs\<close> bnd_x bnd_z True]]
      show ?thesis by simp
    next
      case (Suc m')
      hence "m' < n"
        using \<open>m < Suc n\<close> by auto
      from DERIV_hyp[OF this bnd_z] show ?thesis
        using Suc by simp
    qed

    have "\<And>k i. k < i \<Longrightarrow> {k ..< i} = insert k {Suc k ..< i}" by auto
    hence prod_head_Suc: "\<And>k i. \<Prod>{k ..< k + Suc i} = k * \<Prod>{Suc k ..< Suc k + i}"
      by auto
    have sum_move0: "\<And>k F. sum F {0..<Suc k} = F 0 + sum (\<lambda> k. F (Suc k)) {0..<k}"
      unfolding sum.shift_bounds_Suc_ivl[symmetric]
      unfolding sum.atLeast_Suc_lessThan[OF zero_less_Suc] ..
    define C where "C = xs!x - c"

    {
      fix t::real assume t: "t \<in>\<^sub>r ivlx"
      hence "bounded_by [xs!x] [vs!x]"
        using \<open>bounded_by xs vs\<close>[THEN bounded_byE, OF \<open>x < length vs\<close>]
        by (cases "vs!x", auto simp add: bounded_by_def)

      with hyp[THEN bspec, OF t] f_c
      have "bounded_by [?f 0 c, ?X (Suc k) f n t, xs!x] [Some ivl1, Some ivl2, vs!x]"
        by (auto intro!: bounded_by_Cons)
      from approx[OF this final, unfolded atLeastAtMost_iff[symmetric]]
      have "?X (Suc k) f n t * (xs!x - real_of_float c) * inverse k + ?f 0 c \<in>\<^sub>r ivl"
        by (auto simp add: algebra_simps)
      also have "?X (Suc k) f n t * (xs!x - real_of_float c) * inverse (real k) + ?f 0 c =
               (\<Sum> i = 0..<Suc n. inverse (real (\<Prod> j \<in> {k..<k+i}. j)) * ?f i c * (xs!x - c)^i) +
               inverse (real (\<Prod> j \<in> {k..<k+Suc n}. j)) * ?f (Suc n) t * (xs!x - c)^Suc n" (is "_ = ?T")
        unfolding funpow_Suc C_def[symmetric] sum_move0 prod_head_Suc
        by (auto simp add: algebra_simps)
          (simp only: mult.left_commute [of _ "inverse (real k)"] sum_distrib_left [symmetric])
      finally have "?T \<in>\<^sub>r ivl" .
    }
    thus ?thesis using DERIV by blast
  qed
qed

lemma prod_fact: "real (\<Prod> {1..<1 + k}) = fact (k :: nat)"
  by (simp add: fact_prod atLeastLessThanSuc_atLeastAtMost)

lemma approx_tse:
  assumes "bounded_by xs vs"
    and bnd_x: "vs ! x = Some ivlx"
    and bnd_c: "real_of_float c \<in>\<^sub>r ivlx"
    and "x < length vs" and "x < length xs"
    and ate: "approx_tse prec x s c 1 f vs = Some ivl"
  shows "interpret_floatarith f xs \<in>\<^sub>r ivl"
proof -
  define F where [abs_def]: "F n z =
    interpret_floatarith ((DERIV_floatarith x ^^ n) f) (xs[x := z])" for n z
  hence F0: "F 0 = (\<lambda> z. interpret_floatarith f (xs[x := z]))" by auto

  hence "bounded_by (xs[x := c]) vs" and "x < length vs" "x < length xs"
    using \<open>bounded_by xs vs\<close> bnd_x bnd_c \<open>x < length vs\<close> \<open>x < length xs\<close>
    by (auto intro!: bounded_by_update_var)

  from approx_tse_generic[OF \<open>bounded_by xs vs\<close> this bnd_x ate]
  obtain n
    where DERIV: "\<forall> m z. m < n \<and> real_of_float (lower ivlx) \<le> z \<and> z \<le> real_of_float (upper ivlx) \<longrightarrow> DERIV (F m) z :> F (Suc m) z"
    and hyp: "\<And> (t::real). t \<in>\<^sub>r ivlx \<Longrightarrow>
           (\<Sum> j = 0..<n. inverse(fact j) * F j c * (xs!x - c)^j) +
             inverse ((fact n)) * F n t * (xs!x - c)^n
             \<in>\<^sub>r ivl" (is "\<And> t. _ \<Longrightarrow> ?taylor t \<in> _")
    unfolding F_def atLeastAtMost_iff[symmetric] prod_fact
    by (auto simp: set_of_eq Ball_def)

  have bnd_xs: "xs ! x \<in>\<^sub>r ivlx"
    using \<open>bounded_by xs vs\<close>[THEN bounded_byE, OF \<open>x < length vs\<close>] bnd_x by auto

  show ?thesis
  proof (cases n)
    case 0
    thus ?thesis
      using hyp[OF bnd_xs] unfolding F_def by auto
  next
    case (Suc n')
    show ?thesis
    proof (cases "xs ! x = c")
      case True
      from True[symmetric] hyp[OF bnd_xs] Suc show ?thesis
        unfolding F_def Suc sum.atLeast_Suc_lessThan[OF zero_less_Suc] sum.shift_bounds_Suc_ivl
        by auto
    next
      case False
      have "lower ivlx \<le> real_of_float c" "real_of_float c \<le> upper ivlx" "lower ivlx \<le> xs!x" "xs!x \<le> upper ivlx"
        using Suc bnd_c \<open>bounded_by xs vs\<close>[THEN bounded_byE, OF \<open>x < length vs\<close>] bnd_x
        by (auto simp: set_of_eq)
      from Taylor[OF zero_less_Suc, of F, OF F0 DERIV[unfolded Suc] this False]
      obtain t::real where t_bnd: "if xs ! x < c then xs ! x < t \<and> t < c else c < t \<and> t < xs ! x"
        and fl_eq: "interpret_floatarith f (xs[x := xs ! x]) =
           (\<Sum>m = 0..<Suc n'. F m c / (fact m) * (xs ! x - c) ^ m) +
           F (Suc n') t / (fact (Suc n')) * (xs ! x - c) ^ Suc n'"
        unfolding atLeast0LessThan by blast

      from t_bnd bnd_xs bnd_c have *: "t \<in>\<^sub>r ivlx"
        by (cases "xs ! x < c") (auto simp: set_of_eq)

      have "interpret_floatarith f (xs[x := xs ! x]) = ?taylor t"
        unfolding fl_eq Suc by (auto simp add: algebra_simps divide_inverse)
      also have "\<dots> \<in>\<^sub>r ivl"
        using * by (rule hyp)
      finally show ?thesis
        by simp
    qed
  qed
qed

fun approx_tse_form' where
"approx_tse_form' prec t f 0 ivl cmp =
  (case approx_tse prec 0 t (mid ivl) 1 f [Some ivl]
     of Some ivl \<Rightarrow> cmp ivl | None \<Rightarrow> False)" |
"approx_tse_form' prec t f (Suc s) ivl cmp =
  (let (ivl1, ivl2) = split_float_interval ivl
   in (if approx_tse_form' prec t f s ivl1 cmp then
      approx_tse_form' prec t f s ivl2 cmp else False))"

lemma approx_tse_form':
  fixes x :: real
  assumes "approx_tse_form' prec t f s ivl cmp"
    and "x \<in>\<^sub>r ivl"
  shows "\<exists>ivl' ivly. x \<in>\<^sub>r ivl' \<and> ivl' \<le> ivl \<and> cmp ivly \<and>
    approx_tse prec 0 t (mid ivl') 1 f [Some ivl'] = Some ivly"
  using assms
proof (induct s arbitrary: ivl)
  case 0
  then obtain ivly
    where *: "approx_tse prec 0 t (mid ivl) 1 f [Some ivl] = Some ivly"
    and **: "cmp ivly" by (auto elim!: case_optionE)
  with 0 show ?case by auto
next
  case (Suc s)
  let ?ivl1 = "fst (split_float_interval ivl)"
  let ?ivl2 = "snd (split_float_interval ivl)"
  from Suc.prems
  have l: "approx_tse_form' prec t f s ?ivl1 cmp"
    and u: "approx_tse_form' prec t f s ?ivl2 cmp"
    by (auto simp add: Let_def lazy_conj)

  have subintervals: "?ivl1 \<le> ivl" "?ivl2 \<le> ivl"
    using mid_le
    by (auto simp: less_eq_interval_def split_float_interval_bounds)

  from split_float_interval_realD[OF _ \<open>x \<in>\<^sub>r ivl\<close>] consider "x \<in>\<^sub>r ?ivl1" | "x \<in>\<^sub>r ?ivl2"
    by (auto simp: prod_eq_iff)
  then show ?case
  proof cases
    case 1
    from Suc.hyps[OF l this]
    obtain ivl' ivly where
      "x \<in>\<^sub>r ivl' \<and> ivl' \<le> fst (split_float_interval ivl) \<and> cmp ivly \<and>
        approx_tse prec 0 t (mid ivl') 1 f [Some ivl'] = Some ivly"
      by blast
    then show ?thesis
      using subintervals
      by (auto)
  next
    case 2
    from Suc.hyps[OF u this]
    obtain ivl' ivly where
      "x \<in>\<^sub>r ivl' \<and> ivl' \<le> snd (split_float_interval ivl) \<and> cmp ivly \<and>
        approx_tse prec 0 t (mid ivl') 1 f [Some ivl'] = Some ivly"
      by blast
    then show ?thesis
      using subintervals
      by (auto)
  qed
qed

lemma approx_tse_form'_less:
  fixes x :: real
  assumes tse: "approx_tse_form' prec t (Add a (Minus b)) s ivl (\<lambda> ivl. 0 < lower ivl)"
    and x: "x \<in>\<^sub>r ivl"
  shows "interpret_floatarith b [x] < interpret_floatarith a [x]"
proof -
  from approx_tse_form'[OF tse x]
  obtain ivl' ivly
    where x': "x \<in>\<^sub>r ivl'"
    and "ivl' \<le> ivl" and "0 < lower ivly"
    and tse: "approx_tse prec 0 t (mid ivl') 1 (Add a (Minus b)) [Some ivl'] = Some ivly"
    by blast

  hence "bounded_by [x] [Some ivl']"
    by (auto simp add: bounded_by_def)
  from approx_tse[OF this _ _ _ _ tse, of ivl'] x' mid_le
  have "lower ivly \<le> interpret_floatarith a [x] - interpret_floatarith b [x]"
    by (auto simp: set_of_eq)
  from order_less_le_trans[OF _ this, of 0] \<open>0 < lower ivly\<close> show ?thesis
    by auto
qed

lemma approx_tse_form'_le:
  fixes x :: real
  assumes tse: "approx_tse_form' prec t (Add a (Minus b)) s ivl (\<lambda> ivl. 0 \<le> lower ivl)"
    and x: "x \<in>\<^sub>r ivl"
  shows "interpret_floatarith b [x] \<le> interpret_floatarith a [x]"
proof -
  from approx_tse_form'[OF tse x]
  obtain ivl' ivly
    where x': "x \<in>\<^sub>r ivl'"
    and "ivl' \<le> ivl" and "0 \<le> lower ivly"
    and tse: "approx_tse prec 0 t (mid ivl') 1 (Add a (Minus b)) [Some (ivl')] = Some ivly"
    by blast

  hence "bounded_by [x] [Some ivl']" by (auto simp add: bounded_by_def)
  from approx_tse[OF this _ _ _ _ tse, of ivl'] x' mid_le
  have "lower ivly \<le> interpret_floatarith a [x] - interpret_floatarith b [x]"
    by (auto simp: set_of_eq)
  from order_trans[OF _ this, of 0] \<open>0 \<le> lower ivly\<close> show ?thesis
    by auto
qed

fun approx_tse_concl where
"approx_tse_concl prec t (Less lf rt) s ivl ivl' \<longleftrightarrow>
    approx_tse_form' prec t (Add rt (Minus lf)) s (sup ivl ivl') (\<lambda> ivl. 0 < lower ivl)" |
"approx_tse_concl prec t (LessEqual lf rt) s ivl ivl' \<longleftrightarrow>
    approx_tse_form' prec t (Add rt (Minus lf)) s (sup ivl ivl') (\<lambda> ivl. 0 \<le> lower ivl)" |
"approx_tse_concl prec t (AtLeastAtMost x lf rt) s ivl ivl' \<longleftrightarrow>
    (if approx_tse_form' prec t (Add x (Minus lf)) s (sup ivl ivl') (\<lambda> ivl. 0 \<le> lower ivl) then
      approx_tse_form' prec t (Add rt (Minus x)) s (sup ivl ivl') (\<lambda> ivl. 0 \<le> lower ivl) else False)" |
"approx_tse_concl prec t (Conj f g) s ivl ivl' \<longleftrightarrow>
    approx_tse_concl prec t f s ivl ivl' \<and> approx_tse_concl prec t g s ivl ivl'" |
"approx_tse_concl prec t (Disj f g) s ivl ivl' \<longleftrightarrow>
    approx_tse_concl prec t f s ivl ivl' \<or> approx_tse_concl prec t g s ivl ivl'" |
"approx_tse_concl _ _ _ _ _ _ \<longleftrightarrow> False"

definition
  "approx_tse_form prec t s f =
    (case f of
      Bound x a b f \<Rightarrow>
        x = Var 0 \<and>
        (case (approx prec a [None], approx prec b [None]) of
          (Some ivl, Some ivl') \<Rightarrow> approx_tse_concl prec t f s ivl ivl'
        | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"

lemma approx_tse_form:
  assumes "approx_tse_form prec t s f"
  shows "interpret_form f [x]"
proof (cases f)
  case f_def: (Bound i a b f')
  with assms obtain ivl ivl'
    where a: "approx prec a [None] = Some ivl"
    and b: "approx prec b [None] = Some ivl'"
    unfolding approx_tse_form_def by (auto elim!: case_optionE)

  from f_def assms have "i = Var 0"
    unfolding approx_tse_form_def by auto
  hence i: "interpret_floatarith i [x] = x" by auto

  {
    let ?f = "\<lambda>z. interpret_floatarith z [x]"
    assume "?f i \<in> { ?f a .. ?f b }"
    with approx[OF _ a, of "[x]"] approx[OF _ b, of "[x]"]
    have bnd: "x \<in>\<^sub>r sup ivl ivl'" unfolding bounded_by_def i
      by (auto simp: set_of_eq sup_float_def inf_float_def min_def max_def)

    have "interpret_form f' [x]"
      using assms[unfolded f_def]
    proof (induct f')
      case (Less lf rt)
      with a b
      have "approx_tse_form' prec t (Add rt (Minus lf)) s (sup ivl ivl') (\<lambda> ivl. 0 < lower ivl)"
        unfolding approx_tse_form_def by auto
      from approx_tse_form'_less[OF this bnd]
      show ?case using Less by auto
    next
      case (LessEqual lf rt)
      with f_def a b assms
      have "approx_tse_form' prec t (Add rt (Minus lf)) s (sup ivl ivl') (\<lambda> ivl. 0 \<le> lower ivl)"
        unfolding approx_tse_form_def by auto
      from approx_tse_form'_le[OF this bnd]
      show ?case using LessEqual by auto
    next
      case (AtLeastAtMost x lf rt)
      with f_def a b assms
      have "approx_tse_form' prec t (Add rt (Minus x)) s (sup ivl ivl') (\<lambda> ivl. 0 \<le> lower ivl)"
        and "approx_tse_form' prec t (Add x (Minus lf)) s (sup ivl ivl') (\<lambda> ivl. 0 \<le> lower ivl)"
        unfolding approx_tse_form_def lazy_conj by (auto split: if_split_asm)
      from approx_tse_form'_le[OF this(1) bnd] approx_tse_form'_le[OF this(2) bnd]
      show ?case using AtLeastAtMost by auto
    qed (auto simp: f_def approx_tse_form_def elim!: case_optionE)
  }
  thus ?thesis unfolding f_def by auto
qed (insert assms, auto simp add: approx_tse_form_def)

text \<open>\<^term>\<open>approx_form_eval\<close> is only used for the {\tt value}-command.\<close>

fun approx_form_eval :: "nat \<Rightarrow> form \<Rightarrow> (float interval) option list \<Rightarrow> (float interval) option list" where
"approx_form_eval prec (Bound (Var n) a b f) bs =
   (case (approx prec a bs, approx prec b bs)
   of (Some ivl1, Some ivl2) \<Rightarrow> approx_form_eval prec f (bs[n := Some (sup ivl1 ivl2)])
    | _ \<Rightarrow> bs)" |
"approx_form_eval prec (Assign (Var n) a f) bs =
   (case (approx prec a bs)
   of (Some ivl) \<Rightarrow> approx_form_eval prec f (bs[n := Some ivl])
    | _ \<Rightarrow> bs)" |
"approx_form_eval prec (Less a b) bs = bs @ [approx prec a bs, approx prec b bs]" |
"approx_form_eval prec (LessEqual a b) bs = bs @ [approx prec a bs, approx prec b bs]" |
"approx_form_eval prec (AtLeastAtMost x a b) bs =
   bs @ [approx prec x bs, approx prec a bs, approx prec b bs]" |
"approx_form_eval _ _ bs = bs"


subsection \<open>Implement proof method \texttt{approximation}\<close>

ML \<open>
val _ = \<comment> \<open>Trusting the oracle \<close>@{oracle_name "holds_by_evaluation"}
signature APPROXIMATION_COMPUTATION = sig
val approx_bool: Proof.context -> term -> term
val approx_arith: Proof.context -> term -> term
val approx_form_eval: Proof.context -> term -> term
val approx_conv: Proof.context -> conv
end

structure Approximation_Computation : APPROXIMATION_COMPUTATION = struct

  fun approx_conv ctxt ct =
    @{computation_check
      terms: Trueprop
        "0 :: nat" "1 :: nat" "2 :: nat" "3 :: nat" Suc
          "(+)::nat\<Rightarrow>nat\<Rightarrow>nat" "(-)::nat\<Rightarrow>nat\<Rightarrow>nat" "(*)::nat\<Rightarrow>nat\<Rightarrow>nat"
        "0 :: int" "1 :: int" "2 :: int" "3 :: int" "-1 :: int"
          "(+)::int\<Rightarrow>int\<Rightarrow>int" "(-)::int\<Rightarrow>int\<Rightarrow>int" "(*)::int\<Rightarrow>int\<Rightarrow>int" "uminus::int\<Rightarrow>int"
        "replicate :: _ \<Rightarrow> (float interval) option \<Rightarrow> _"
        "interval_of::float\<Rightarrow>float interval"
        approx'
        approx_form
        approx_tse_form
        approx_form_eval
      datatypes: bool
        int
        nat
        integer
        "nat list"
        float
        "(float interval) option list"
        floatarith
        form
    } ctxt ct

  fun term_of_bool true = \<^term>\<open>True\<close>
    | term_of_bool false = \<^term>\<open>False\<close>;

  val mk_int = HOLogic.mk_number \<^typ>\<open>int\<close> o @{code integer_of_int};

  fun term_of_float (@{code Float} (k, l)) =
    \<^term>\<open>Float\<close> $ mk_int k $ mk_int l;

  fun term_of_float_interval x = @{term "Interval::_\<Rightarrow>float interval"} $
    HOLogic.mk_prod
      (apply2 term_of_float (@{code lowerF} x, @{code upperF} x))

  fun term_of_float_interval_option NONE = \<^term>\<open>None :: (float interval) option\<close>
    | term_of_float_interval_option (SOME ff) = \<^term>\<open>Some :: float interval \<Rightarrow> _\<close>
        $ (term_of_float_interval ff);

  val term_of_float_interval_option_list =
    HOLogic.mk_list \<^typ>\<open>(float interval) option\<close> o map term_of_float_interval_option;

  val approx_bool = @{computation bool}
    (fn _ => fn x => case x of SOME b => term_of_bool b
      | NONE => error "Computation approx_bool failed.")
  val approx_arith = @{computation "float interval option"}
    (fn _ => fn x => case x of SOME ffo => term_of_float_interval_option ffo
      | NONE => error "Computation approx_arith failed.")
  val approx_form_eval = @{computation "float interval option list"}
    (fn _ => fn x => case x of SOME ffos => term_of_float_interval_option_list ffos
      | NONE => error "Computation approx_form_eval failed.")

end
\<close>

lemma intervalE: "a \<le> x \<and> x \<le> b \<Longrightarrow> \<lbrakk> x \<in> { a .. b } \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

lemma meta_eqE: "x \<equiv> a \<Longrightarrow> \<lbrakk> x = a \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

named_theorems approximation_preproc

lemma approximation_preproc_floatarith[approximation_preproc]:
  "0 = real_of_float 0"
  "1 = real_of_float 1"
  "0 = Float 0 0"
  "1 = Float 1 0"
  "numeral a = Float (numeral a) 0"
  "numeral a = real_of_float (numeral a)"
  "x - y = x + - y"
  "x / y = x * inverse y"
  "ceiling x = - floor (- x)"
  "log x y = ln y * inverse (ln x)"
  "sin x = cos (pi / 2 - x)"
  "tan x = sin x / cos x"
  by (simp_all add: inverse_eq_divide ceiling_def log_def sin_cos_eq tan_def real_of_float_eq)

lemma approximation_preproc_int[approximation_preproc]:
  "real_of_int 0 = real_of_float 0"
  "real_of_int 1 = real_of_float 1"
  "real_of_int (i + j) = real_of_int i + real_of_int j"
  "real_of_int (- i) = - real_of_int i"
  "real_of_int (i - j) = real_of_int i - real_of_int j"
  "real_of_int (i * j) = real_of_int i * real_of_int j"
  "real_of_int (i div j) = real_of_int (floor (real_of_int i / real_of_int j))"
  "real_of_int (min i j) = min (real_of_int i) (real_of_int j)"
  "real_of_int (max i j) = max (real_of_int i) (real_of_int j)"
  "real_of_int (abs i) = abs (real_of_int i)"
  "real_of_int (i ^ n) = (real_of_int i) ^ n"
  "real_of_int (numeral a) = real_of_float (numeral a)"
  "i mod j = i - i div j * j"
  "i = j \<longleftrightarrow> real_of_int i = real_of_int j"
  "i \<le> j \<longleftrightarrow> real_of_int i \<le> real_of_int j"
  "i < j \<longleftrightarrow> real_of_int i < real_of_int j"
  "i \<in> {j .. k} \<longleftrightarrow> real_of_int i \<in> {real_of_int j .. real_of_int k}"
  by (simp_all add: floor_divide_of_int_eq minus_div_mult_eq_mod [symmetric])

lemma approximation_preproc_nat[approximation_preproc]:
  "real 0 = real_of_float 0"
  "real 1 = real_of_float 1"
  "real (i + j) = real i + real j"
  "real (i - j) = max (real i - real j) 0"
  "real (i * j) = real i * real j"
  "real (i div j) = real_of_int (floor (real i / real j))"
  "real (min i j) = min (real i) (real j)"
  "real (max i j) = max (real i) (real j)"
  "real (i ^ n) = (real i) ^ n"
  "real (numeral a) = real_of_float (numeral a)"
  "i mod j = i - i div j * j"
  "n = m \<longleftrightarrow> real n = real m"
  "n \<le> m \<longleftrightarrow> real n \<le> real m"
  "n < m \<longleftrightarrow> real n < real m"
  "n \<in> {m .. l} \<longleftrightarrow> real n \<in> {real m .. real l}"
  by (simp_all add: real_div_nat_eq_floor_of_divide minus_div_mult_eq_mod [symmetric])

ML_file \<open>approximation.ML\<close>

method_setup approximation = \<open>
  let
    val free =
      Args.context -- Args.term >> (fn (_, Free (n, _)) => n | (ctxt, t) =>
        error ("Bad free variable: " ^ Syntax.string_of_term ctxt t));
  in
    Scan.lift Parse.nat --
    Scan.optional (Scan.lift (Args.$$$ "splitting" |-- Args.colon)
      |-- Parse.and_list' (free --| Scan.lift (Args.$$$ "=") -- Scan.lift Parse.nat)) [] --
    Scan.option (Scan.lift (Args.$$$ "taylor" |-- Args.colon) |--
    (free |-- Scan.lift (Args.$$$ "=") |-- Scan.lift Parse.nat)) >>
    (fn ((prec, splitting), taylor) => fn ctxt =>
      SIMPLE_METHOD' (Approximation.approximation_tac prec splitting taylor ctxt))
  end
\<close> "real number approximation"


section "Quickcheck Generator"

lemma approximation_preproc_push_neg[approximation_preproc]:
  fixes a b::real
  shows
    "\<not> (a < b) \<longleftrightarrow> b \<le> a"
    "\<not> (a \<le> b) \<longleftrightarrow> b < a"
    "\<not> (a = b) \<longleftrightarrow> b < a \<or> a < b"
    "\<not> (p \<and> q) \<longleftrightarrow> \<not> p \<or> \<not> q"
    "\<not> (p \<or> q) \<longleftrightarrow> \<not> p \<and> \<not> q"
    "\<not> \<not> q \<longleftrightarrow> q"
  by auto

ML_file \<open>approximation_generator.ML\<close>
setup "Approximation_Generator.setup"

section "Avoid pollution of name space"

bundle floatarith_notation begin

notation Add ("Add")
notation Minus ("Minus")
notation Mult ("Mult")
notation Inverse ("Inverse")
notation Cos ("Cos")
notation Arctan ("Arctan")
notation Abs ("Abs")
notation Max ("Max")
notation Min ("Min")
notation Pi ("Pi")
notation Sqrt ("Sqrt")
notation Exp ("Exp")
notation Powr ("Powr")
notation Ln ("Ln")
notation Power ("Power")
notation Floor ("Floor")
notation Var ("Var")
notation Num ("Num")

end

bundle no_floatarith_notation begin

no_notation Add ("Add")
no_notation Minus ("Minus")
no_notation Mult ("Mult")
no_notation Inverse ("Inverse")
no_notation Cos ("Cos")
no_notation Arctan ("Arctan")
no_notation Abs ("Abs")
no_notation Max ("Max")
no_notation Min ("Min")
no_notation Pi ("Pi")
no_notation Sqrt ("Sqrt")
no_notation Exp ("Exp")
no_notation Powr ("Powr")
no_notation Ln ("Ln")
no_notation Power ("Power")
no_notation Floor ("Floor")
no_notation Var ("Var")
no_notation Num ("Num")

end

hide_const (open)
  Add
  Minus
  Mult
  Inverse
  Cos
  Arctan
  Abs
  Max
  Min
  Pi
  Sqrt
  Exp
  Powr
  Ln
  Power
  Floor
  Var
  Num

end
