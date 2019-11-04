 (* Author:     Johannes Hoelzl, TU Muenchen
   Coercions removed by Dmitriy Traytel *)

theory Approximation
imports
  Complex_Main
  "HOL-Library.Code_Target_Numeral"
  Approximation_Bounds
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

fun lift_bin :: "(float * float) option \<Rightarrow> (float * float) option \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> (float * float) option) \<Rightarrow> (float * float) option" where
"lift_bin (Some (l1, u1)) (Some (l2, u2)) f = f l1 u1 l2 u2" |
"lift_bin a b f = None"

fun lift_bin' :: "(float * float) option \<Rightarrow> (float * float) option \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> float \<Rightarrow> (float * float)) \<Rightarrow> (float * float) option" where
"lift_bin' (Some (l1, u1)) (Some (l2, u2)) f = Some (f l1 u1 l2 u2)" |
"lift_bin' a b f = None"

fun lift_un :: "(float * float) option \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> ((float option) * (float option))) \<Rightarrow> (float * float) option" where
"lift_un (Some (l1, u1)) f = (case (f l1 u1) of (Some l, Some u) \<Rightarrow> Some (l, u)
                                             | t \<Rightarrow> None)" |
"lift_un b f = None"

fun lift_un' :: "(float * float) option \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> (float * float)) \<Rightarrow> (float * float) option" where
"lift_un' (Some (l1, u1)) f = Some (f l1 u1)" |
"lift_un' b f = None"

definition bounded_by :: "real list \<Rightarrow> (float \<times> float) option list \<Rightarrow> bool" where 
  "bounded_by xs vs \<longleftrightarrow>
  (\<forall> i < length vs. case vs ! i of None \<Rightarrow> True
         | Some (l, u) \<Rightarrow> xs ! i \<in> { real_of_float l .. real_of_float u })"
                                                                     
lemma bounded_byE:
  assumes "bounded_by xs vs"
  shows "\<And> i. i < length vs \<Longrightarrow> case vs ! i of None \<Rightarrow> True
         | Some (l, u) \<Rightarrow> xs ! i \<in> { real_of_float l .. real_of_float u }"
  using assms bounded_by_def by blast

lemma bounded_by_update:
  assumes "bounded_by xs vs"
    and bnd: "xs ! i \<in> { real_of_float l .. real_of_float u }"
  shows "bounded_by xs (vs[i := Some (l,u)])"
proof -
  {
    fix j
    let ?vs = "vs[i := Some (l,u)]"
    assume "j < length ?vs"
    hence [simp]: "j < length vs" by simp
    have "case ?vs ! j of None \<Rightarrow> True | Some (l, u) \<Rightarrow> xs ! j \<in> { real_of_float l .. real_of_float u }"
    proof (cases "?vs ! j")
      case (Some b)
      thus ?thesis
      proof (cases "i = j")
        case True
        thus ?thesis using \<open>?vs ! j = Some b\<close> and bnd by auto
      next
        case False
        thus ?thesis using \<open>bounded_by xs vs\<close> unfolding bounded_by_def by auto
      qed
    qed auto
  }
  thus ?thesis unfolding bounded_by_def by auto
qed

lemma bounded_by_None: "bounded_by xs (replicate (length xs) None)"
  unfolding bounded_by_def by auto

fun approx approx' :: "nat \<Rightarrow> floatarith \<Rightarrow> (float * float) option list \<Rightarrow> (float * float) option" where
"approx' prec a bs          = (case (approx prec a bs) of Some (l, u) \<Rightarrow> Some (float_round_down prec l, float_round_up prec u) | None \<Rightarrow> None)" |
"approx prec (Add a b) bs   =
  lift_bin' (approx' prec a bs) (approx' prec b bs)
    (\<lambda> l1 u1 l2 u2. (float_plus_down prec l1 l2, float_plus_up prec u1 u2))" |
"approx prec (Minus a) bs   = lift_un' (approx' prec a bs) (\<lambda> l u. (-u, -l))" |
"approx prec (Mult a b) bs  =
  lift_bin' (approx' prec a bs) (approx' prec b bs) (bnds_mult prec)" |
"approx prec (Inverse a) bs = lift_un (approx' prec a bs) (\<lambda> l u. if (0 < l \<or> u < 0) then (Some (float_divl prec 1 u), Some (float_divr prec 1 l)) else (None, None))" |
"approx prec (Cos a) bs     = lift_un' (approx' prec a bs) (bnds_cos prec)" |
"approx prec Pi bs          = Some (lb_pi prec, ub_pi prec)" |
"approx prec (Min a b) bs   = lift_bin' (approx' prec a bs) (approx' prec b bs) (\<lambda> l1 u1 l2 u2. (min l1 l2, min u1 u2))" |
"approx prec (Max a b) bs   = lift_bin' (approx' prec a bs) (approx' prec b bs) (\<lambda> l1 u1 l2 u2. (max l1 l2, max u1 u2))" |
"approx prec (Abs a) bs     = lift_un' (approx' prec a bs) (\<lambda>l u. (if l < 0 \<and> 0 < u then 0 else min \<bar>l\<bar> \<bar>u\<bar>, max \<bar>l\<bar> \<bar>u\<bar>))" |
"approx prec (Arctan a) bs  = lift_un' (approx' prec a bs) (\<lambda> l u. (lb_arctan prec l, ub_arctan prec u))" |
"approx prec (Sqrt a) bs    = lift_un' (approx' prec a bs) (\<lambda> l u. (lb_sqrt prec l, ub_sqrt prec u))" |
"approx prec (Exp a) bs     = lift_un' (approx' prec a bs) (\<lambda> l u. (lb_exp prec l, ub_exp prec u))" |
"approx prec (Powr a b) bs  = lift_bin (approx' prec a bs) (approx' prec b bs) (bnds_powr prec)" |
"approx prec (Ln a) bs      = lift_un (approx' prec a bs) (\<lambda> l u. (lb_ln prec l, ub_ln prec u))" |
"approx prec (Power a n) bs = lift_un' (approx' prec a bs) (float_power_bnds prec n)" |
"approx prec (Floor a) bs = lift_un' (approx' prec a bs) (\<lambda> l u. (floor_fl l, floor_fl u))" |
"approx prec (Num f) bs     = Some (f, f)" |
"approx prec (Var i) bs    = (if i < length bs then bs ! i else None)"

lemma approx_approx':
  assumes Pa: "\<And>l u. Some (l, u) = approx prec a vs \<Longrightarrow>
      l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
    and approx': "Some (l, u) = approx' prec a vs"
  shows "l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
proof -
  obtain l' u' where S: "Some (l', u') = approx prec a vs"
    using approx' unfolding approx'.simps by (cases "approx prec a vs") auto
  have l': "l = float_round_down prec l'" and u': "u = float_round_up prec u'"
    using approx' unfolding approx'.simps S[symmetric] by auto
  show ?thesis unfolding l' u'
    using order_trans[OF Pa[OF S, THEN conjunct2] float_round_up[of u']]
    using order_trans[OF float_round_down[of _ l'] Pa[OF S, THEN conjunct1]] by auto
qed

lemma lift_bin_ex:
  assumes lift_bin_Some: "Some (l, u) = lift_bin a b f"
  shows "\<exists> l1 u1 l2 u2. Some (l1, u1) = a \<and> Some (l2, u2) = b"
proof (cases a)
  case None
  hence "None = lift_bin a b f"
    unfolding None lift_bin.simps ..
  thus ?thesis
    using lift_bin_Some by auto
next
  case (Some a')
  show ?thesis
  proof (cases b)
    case None
    hence "None = lift_bin a b f"
      unfolding None lift_bin.simps ..
    thus ?thesis using lift_bin_Some by auto
  next
    case (Some b')
    obtain la ua where a': "a' = (la, ua)"
      by (cases a') auto
    obtain lb ub where b': "b' = (lb, ub)"
      by (cases b') auto
    thus ?thesis
      unfolding \<open>a = Some a'\<close> \<open>b = Some b'\<close> a' b' by auto
  qed
qed

lemma lift_bin_f:
  assumes lift_bin_Some: "Some (l, u) = lift_bin (g a) (g b) f"
    and Pa: "\<And>l u. Some (l, u) = g a \<Longrightarrow> P l u a"
    and Pb: "\<And>l u. Some (l, u) = g b \<Longrightarrow> P l u b"
  shows "\<exists> l1 u1 l2 u2. P l1 u1 a \<and> P l2 u2 b \<and> Some (l, u) = f l1 u1 l2 u2"
proof -
  obtain l1 u1 l2 u2
    where Sa: "Some (l1, u1) = g a"
      and Sb: "Some (l2, u2) = g b"
    using lift_bin_ex[OF assms(1)] by auto
  have lu: "Some (l, u) = f l1 u1 l2 u2"
    using lift_bin_Some[unfolded Sa[symmetric] Sb[symmetric] lift_bin.simps] by auto
  thus ?thesis
    using Pa[OF Sa] Pb[OF Sb] by auto
qed

lemma lift_bin:
  assumes lift_bin_Some: "Some (l, u) = lift_bin (approx' prec a bs) (approx' prec b bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
      real_of_float l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> real_of_float u" (is "\<And>l u. _ = ?g a \<Longrightarrow> ?P l u a")
    and Pb: "\<And>l u. Some (l, u) = approx prec b bs \<Longrightarrow>
      real_of_float l \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> real_of_float u"
  shows "\<exists>l1 u1 l2 u2. (real_of_float l1 \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> real_of_float u1) \<and>
                       (real_of_float l2 \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> real_of_float u2) \<and>
                       Some (l, u) = (f l1 u1 l2 u2)"
proof -
  { fix l u assume "Some (l, u) = approx' prec a bs"
    with approx_approx'[of prec a bs, OF _ this] Pa
    have "l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u" by auto } note Pa = this
  { fix l u assume "Some (l, u) = approx' prec b bs"
    with approx_approx'[of prec b bs, OF _ this] Pb
    have "l \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> u" by auto } note Pb = this

  from lift_bin_f[where g="\<lambda>a. approx' prec a bs" and P = ?P, OF lift_bin_Some, OF Pa Pb]
  show ?thesis by auto
qed

lemma lift_bin'_ex:
  assumes lift_bin'_Some: "Some (l, u) = lift_bin' a b f"
  shows "\<exists> l1 u1 l2 u2. Some (l1, u1) = a \<and> Some (l2, u2) = b"
proof (cases a)
  case None
  hence "None = lift_bin' a b f"
    unfolding None lift_bin'.simps ..
  thus ?thesis
    using lift_bin'_Some by auto
next
  case (Some a')
  show ?thesis
  proof (cases b)
    case None
    hence "None = lift_bin' a b f"
      unfolding None lift_bin'.simps ..
    thus ?thesis using lift_bin'_Some by auto
  next
    case (Some b')
    obtain la ua where a': "a' = (la, ua)"
      by (cases a') auto
    obtain lb ub where b': "b' = (lb, ub)"
      by (cases b') auto
    thus ?thesis
      unfolding \<open>a = Some a'\<close> \<open>b = Some b'\<close> a' b' by auto
  qed
qed

lemma lift_bin'_f:
  assumes lift_bin'_Some: "Some (l, u) = lift_bin' (g a) (g b) f"
    and Pa: "\<And>l u. Some (l, u) = g a \<Longrightarrow> P l u a"
    and Pb: "\<And>l u. Some (l, u) = g b \<Longrightarrow> P l u b"
  shows "\<exists> l1 u1 l2 u2. P l1 u1 a \<and> P l2 u2 b \<and> l = fst (f l1 u1 l2 u2) \<and> u = snd (f l1 u1 l2 u2)"
proof -
  obtain l1 u1 l2 u2
    where Sa: "Some (l1, u1) = g a"
      and Sb: "Some (l2, u2) = g b"
    using lift_bin'_ex[OF assms(1)] by auto
  have lu: "(l, u) = f l1 u1 l2 u2"
    using lift_bin'_Some[unfolded Sa[symmetric] Sb[symmetric] lift_bin'.simps] by auto
  have "l = fst (f l1 u1 l2 u2)" and "u = snd (f l1 u1 l2 u2)"
    unfolding lu[symmetric] by auto
  thus ?thesis
    using Pa[OF Sa] Pb[OF Sb] by auto
qed

lemma lift_bin':
  assumes lift_bin'_Some: "Some (l, u) = lift_bin' (approx' prec a bs) (approx' prec b bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
      l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u" (is "\<And>l u. _ = ?g a \<Longrightarrow> ?P l u a")
    and Pb: "\<And>l u. Some (l, u) = approx prec b bs \<Longrightarrow>
      l \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> u"
  shows "\<exists>l1 u1 l2 u2. (l1 \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u1) \<and>
                       (l2 \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> u2) \<and>
                       l = fst (f l1 u1 l2 u2) \<and> u = snd (f l1 u1 l2 u2)"
proof -
  { fix l u assume "Some (l, u) = approx' prec a bs"
    with approx_approx'[of prec a bs, OF _ this] Pa
    have "l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u" by auto } note Pa = this
  { fix l u assume "Some (l, u) = approx' prec b bs"
    with approx_approx'[of prec b bs, OF _ this] Pb
    have "l \<le> interpret_floatarith b xs \<and> interpret_floatarith b xs \<le> u" by auto } note Pb = this

  from lift_bin'_f[where g="\<lambda>a. approx' prec a bs" and P = ?P, OF lift_bin'_Some, OF Pa Pb]
  show ?thesis by auto
qed

lemma lift_un'_ex:
  assumes lift_un'_Some: "Some (l, u) = lift_un' a f"
  shows "\<exists> l u. Some (l, u) = a"
proof (cases a)
  case None
  hence "None = lift_un' a f"
    unfolding None lift_un'.simps ..
  thus ?thesis
    using lift_un'_Some by auto
next
  case (Some a')
  obtain la ua where a': "a' = (la, ua)"
    by (cases a') auto
  thus ?thesis
    unfolding \<open>a = Some a'\<close> a' by auto
qed

lemma lift_un'_f:
  assumes lift_un'_Some: "Some (l, u) = lift_un' (g a) f"
    and Pa: "\<And>l u. Some (l, u) = g a \<Longrightarrow> P l u a"
  shows "\<exists> l1 u1. P l1 u1 a \<and> l = fst (f l1 u1) \<and> u = snd (f l1 u1)"
proof -
  obtain l1 u1 where Sa: "Some (l1, u1) = g a"
    using lift_un'_ex[OF assms(1)] by auto
  have lu: "(l, u) = f l1 u1"
    using lift_un'_Some[unfolded Sa[symmetric] lift_un'.simps] by auto
  have "l = fst (f l1 u1)" and "u = snd (f l1 u1)"
    unfolding lu[symmetric] by auto
  thus ?thesis
    using Pa[OF Sa] by auto
qed

lemma lift_un':
  assumes lift_un'_Some: "Some (l, u) = lift_un' (approx' prec a bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
      l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
      (is "\<And>l u. _ = ?g a \<Longrightarrow> ?P l u a")
  shows "\<exists>l1 u1. (l1 \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u1) \<and>
    l = fst (f l1 u1) \<and> u = snd (f l1 u1)"
proof -
  have Pa: "l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
    if "Some (l, u) = approx' prec a bs" for l u
    using approx_approx'[of prec a bs, OF _ that] Pa
     by auto
  from lift_un'_f[where g="\<lambda>a. approx' prec a bs" and P = ?P, OF lift_un'_Some, OF Pa]
  show ?thesis by auto
qed

lemma lift_un'_bnds:
  assumes bnds: "\<forall> (x::real) lx ux. (l, u) = f lx ux \<and> x \<in> { lx .. ux } \<longrightarrow> l \<le> f' x \<and> f' x \<le> u"
    and lift_un'_Some: "Some (l, u) = lift_un' (approx' prec a bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
      l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
  shows "real_of_float l \<le> f' (interpret_floatarith a xs) \<and> f' (interpret_floatarith a xs) \<le> real_of_float u"
proof -
  from lift_un'[OF lift_un'_Some Pa]
  obtain l1 u1 where "l1 \<le> interpret_floatarith a xs"
    and "interpret_floatarith a xs \<le> u1"
    and "l = fst (f l1 u1)"
    and "u = snd (f l1 u1)"
    by blast
  hence "(l, u) = f l1 u1" and "interpret_floatarith a xs \<in> {l1 .. u1}"
    by auto
  thus ?thesis
    using bnds by auto
qed

lemma lift_un_ex:
  assumes lift_un_Some: "Some (l, u) = lift_un a f"
  shows "\<exists>l u. Some (l, u) = a"
proof (cases a)
  case None
  hence "None = lift_un a f"
    unfolding None lift_un.simps ..
  thus ?thesis
    using lift_un_Some by auto
next
  case (Some a')
  obtain la ua where a': "a' = (la, ua)"
    by (cases a') auto
  thus ?thesis
    unfolding \<open>a = Some a'\<close> a' by auto
qed

lemma lift_un_f:
  assumes lift_un_Some: "Some (l, u) = lift_un (g a) f"
    and Pa: "\<And>l u. Some (l, u) = g a \<Longrightarrow> P l u a"
  shows "\<exists> l1 u1. P l1 u1 a \<and> Some l = fst (f l1 u1) \<and> Some u = snd (f l1 u1)"
proof -
  obtain l1 u1 where Sa: "Some (l1, u1) = g a"
    using lift_un_ex[OF assms(1)] by auto
  have "fst (f l1 u1) \<noteq> None \<and> snd (f l1 u1) \<noteq> None"
  proof (rule ccontr)
    assume "\<not> (fst (f l1 u1) \<noteq> None \<and> snd (f l1 u1) \<noteq> None)"
    hence or: "fst (f l1 u1) = None \<or> snd (f l1 u1) = None" by auto
    hence "lift_un (g a) f = None"
    proof (cases "fst (f l1 u1) = None")
      case True
      then obtain b where b: "f l1 u1 = (None, b)"
        by (cases "f l1 u1") auto
      thus ?thesis
        unfolding Sa[symmetric] lift_un.simps b by auto
    next
      case False
      hence "snd (f l1 u1) = None"
        using or by auto
      with False obtain b where b: "f l1 u1 = (Some b, None)"
        by (cases "f l1 u1") auto
      thus ?thesis
        unfolding Sa[symmetric] lift_un.simps b by auto
    qed
    thus False
      using lift_un_Some by auto
  qed
  then obtain a' b' where f: "f l1 u1 = (Some a', Some b')"
    by (cases "f l1 u1") auto
  from lift_un_Some[unfolded Sa[symmetric] lift_un.simps f]
  have "Some l = fst (f l1 u1)" and "Some u = snd (f l1 u1)"
    unfolding f by auto
  thus ?thesis
    unfolding Sa[symmetric] lift_un.simps using Pa[OF Sa] by auto
qed

lemma lift_un:
  assumes lift_un_Some: "Some (l, u) = lift_un (approx' prec a bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
        l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
      (is "\<And>l u. _ = ?g a \<Longrightarrow> ?P l u a")
  shows "\<exists>l1 u1. (l1 \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u1) \<and>
                  Some l = fst (f l1 u1) \<and> Some u = snd (f l1 u1)"
proof -
  have Pa: "l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
    if "Some (l, u) = approx' prec a bs" for l u
    using approx_approx'[of prec a bs, OF _ that] Pa by auto
  from lift_un_f[where g="\<lambda>a. approx' prec a bs" and P = ?P, OF lift_un_Some, OF Pa]
  show ?thesis by auto
qed

lemma lift_un_bnds:
  assumes bnds: "\<forall>(x::real) lx ux. (Some l, Some u) = f lx ux \<and> x \<in> { lx .. ux } \<longrightarrow> l \<le> f' x \<and> f' x \<le> u"
    and lift_un_Some: "Some (l, u) = lift_un (approx' prec a bs) f"
    and Pa: "\<And>l u. Some (l, u) = approx prec a bs \<Longrightarrow>
      l \<le> interpret_floatarith a xs \<and> interpret_floatarith a xs \<le> u"
  shows "real_of_float l \<le> f' (interpret_floatarith a xs) \<and> f' (interpret_floatarith a xs) \<le> real_of_float u"
proof -
  from lift_un[OF lift_un_Some Pa]
  obtain l1 u1 where "l1 \<le> interpret_floatarith a xs"
    and "interpret_floatarith a xs \<le> u1"
    and "Some l = fst (f l1 u1)"
    and "Some u = snd (f l1 u1)"
    by blast
  hence "(Some l, Some u) = f l1 u1" and "interpret_floatarith a xs \<in> {l1 .. u1}"
    by auto
  thus ?thesis
    using bnds by auto
qed

lemma approx:
  assumes "bounded_by xs vs"
    and "Some (l, u) = approx prec arith vs" (is "_ = ?g arith")
  shows "l \<le> interpret_floatarith arith xs \<and> interpret_floatarith arith xs \<le> u" (is "?P l u arith")
  using \<open>Some (l, u) = approx prec arith vs\<close>
proof (induct arith arbitrary: l u)
  case (Add a b)
  from lift_bin'[OF Add.prems[unfolded approx.simps]] Add.hyps
  obtain l1 u1 l2 u2 where "l = float_plus_down prec l1 l2"
    and "u = float_plus_up prec u1 u2" "l1 \<le> interpret_floatarith a xs"
    and "interpret_floatarith a xs \<le> u1" "l2 \<le> interpret_floatarith b xs"
    and "interpret_floatarith b xs \<le> u2"
    unfolding fst_conv snd_conv by blast
  thus ?case
    unfolding interpret_floatarith.simps by (auto intro!: float_plus_up_le float_plus_down_le)
next
  case (Minus a)
  from lift_un'[OF Minus.prems[unfolded approx.simps]] Minus.hyps
  obtain l1 u1 where "l = -u1" "u = -l1"
    and "l1 \<le> interpret_floatarith a xs" "interpret_floatarith a xs \<le> u1"
    unfolding fst_conv snd_conv by blast
  thus ?case
    unfolding interpret_floatarith.simps using minus_float.rep_eq by auto
next
  case (Mult a b)
  from lift_bin'[OF Mult.prems[unfolded approx.simps]] Mult.hyps
  obtain l1 u1 l2 u2
    where l: "l = fst (bnds_mult prec l1 u1 l2 u2)"
    and u: "u = snd (bnds_mult prec l1 u1 l2 u2)"
    and a: "l1 \<le> interpret_floatarith a xs" "interpret_floatarith a xs \<le> u1"
    and b: "l2 \<le> interpret_floatarith b xs" "interpret_floatarith b xs \<le> u2" unfolding fst_conv snd_conv by blast
  from l u have lu: "(l, u) = bnds_mult prec l1 u1 l2 u2" by simp
  from bnds_mult[OF lu] a b show ?case by simp
next
  case (Inverse a)
  from lift_un[OF Inverse.prems[unfolded approx.simps], unfolded if_distrib[of fst] if_distrib[of snd] fst_conv snd_conv] Inverse.hyps
  obtain l1 u1 where l': "Some l = (if 0 < l1 \<or> u1 < 0 then Some (float_divl prec 1 u1) else None)"
    and u': "Some u = (if 0 < l1 \<or> u1 < 0 then Some (float_divr prec 1 l1) else None)"
    and l1: "l1 \<le> interpret_floatarith a xs"
    and u1: "interpret_floatarith a xs \<le> u1"
    by blast
  have either: "0 < l1 \<or> u1 < 0"
  proof (rule ccontr)
    assume P: "\<not> (0 < l1 \<or> u1 < 0)"
    show False
      using l' unfolding if_not_P[OF P] by auto
  qed
  moreover have l1_le_u1: "real_of_float l1 \<le> real_of_float u1"
    using l1 u1 by auto
  ultimately have "real_of_float l1 \<noteq> 0" and "real_of_float u1 \<noteq> 0"
    by auto

  have inv: "inverse u1 \<le> inverse (interpret_floatarith a xs)
           \<and> inverse (interpret_floatarith a xs) \<le> inverse l1"
  proof (cases "0 < l1")
    case True
    hence "0 < real_of_float u1" and "0 < real_of_float l1" "0 < interpret_floatarith a xs"
      using l1_le_u1 l1 by auto
    show ?thesis
      unfolding inverse_le_iff_le[OF \<open>0 < real_of_float u1\<close> \<open>0 < interpret_floatarith a xs\<close>]
        inverse_le_iff_le[OF \<open>0 < interpret_floatarith a xs\<close> \<open>0 < real_of_float l1\<close>]
      using l1 u1 by auto
  next
    case False
    hence "u1 < 0"
      using either by blast
    hence "real_of_float u1 < 0" and "real_of_float l1 < 0" "interpret_floatarith a xs < 0"
      using l1_le_u1 u1 by auto
    show ?thesis
      unfolding inverse_le_iff_le_neg[OF \<open>real_of_float u1 < 0\<close> \<open>interpret_floatarith a xs < 0\<close>]
        inverse_le_iff_le_neg[OF \<open>interpret_floatarith a xs < 0\<close> \<open>real_of_float l1 < 0\<close>]
      using l1 u1 by auto
  qed

  from l' have "l = float_divl prec 1 u1"
    by (cases "0 < l1 \<or> u1 < 0") auto
  hence "l \<le> inverse u1"
    unfolding nonzero_inverse_eq_divide[OF \<open>real_of_float u1 \<noteq> 0\<close>]
    using float_divl[of prec 1 u1] by auto
  also have "\<dots> \<le> inverse (interpret_floatarith a xs)"
    using inv by auto
  finally have "l \<le> inverse (interpret_floatarith a xs)" .
  moreover
  from u' have "u = float_divr prec 1 l1"
    by (cases "0 < l1 \<or> u1 < 0") auto
  hence "inverse l1 \<le> u"
    unfolding nonzero_inverse_eq_divide[OF \<open>real_of_float l1 \<noteq> 0\<close>]
    using float_divr[of 1 l1 prec] by auto
  hence "inverse (interpret_floatarith a xs) \<le> u"
    by (rule order_trans[OF inv[THEN conjunct2]])
  ultimately show ?case
    unfolding interpret_floatarith.simps using l1 u1 by auto
next
  case (Abs x)
  from lift_un'[OF Abs.prems[unfolded approx.simps], unfolded fst_conv snd_conv] Abs.hyps
  obtain l1 u1 where l': "l = (if l1 < 0 \<and> 0 < u1 then 0 else min \<bar>l1\<bar> \<bar>u1\<bar>)"
    and u': "u = max \<bar>l1\<bar> \<bar>u1\<bar>"
    and l1: "l1 \<le> interpret_floatarith x xs"
    and u1: "interpret_floatarith x xs \<le> u1"
    by blast
  thus ?case
    unfolding l' u'
    by (cases "l1 < 0 \<and> 0 < u1") (auto simp add: real_of_float_min real_of_float_max)
next
  case (Min a b)
  from lift_bin'[OF Min.prems[unfolded approx.simps], unfolded fst_conv snd_conv] Min.hyps
  obtain l1 u1 l2 u2 where l': "l = min l1 l2" and u': "u = min u1 u2"
    and l1: "l1 \<le> interpret_floatarith a xs" and u1: "interpret_floatarith a xs \<le> u1"
    and l1: "l2 \<le> interpret_floatarith b xs" and u1: "interpret_floatarith b xs \<le> u2"
    by blast
  thus ?case
    unfolding l' u' by (auto simp add: real_of_float_min)
next
  case (Max a b)
  from lift_bin'[OF Max.prems[unfolded approx.simps], unfolded fst_conv snd_conv] Max.hyps
  obtain l1 u1 l2 u2 where l': "l = max l1 l2" and u': "u = max u1 u2"
    and l1: "l1 \<le> interpret_floatarith a xs" and u1: "interpret_floatarith a xs \<le> u1"
    and l1: "l2 \<le> interpret_floatarith b xs" and u1: "interpret_floatarith b xs \<le> u2"
    by blast
  thus ?case
    unfolding l' u' by (auto simp add: real_of_float_max)
next
  case (Cos a)
  with lift_un'_bnds[OF bnds_cos] show ?case by auto
next
  case (Arctan a)
  with lift_un'_bnds[OF bnds_arctan] show ?case by auto
next
  case Pi
  with pi_boundaries show ?case by auto
next
  case (Sqrt a)
  with lift_un'_bnds[OF bnds_sqrt] show ?case by auto
next
  case (Exp a)
  with lift_un'_bnds[OF bnds_exp] show ?case by auto
next
  case (Powr a b)
  from lift_bin[OF Powr.prems[unfolded approx.simps]] Powr.hyps
    obtain l1 u1 l2 u2 where lu: "Some (l, u) = bnds_powr prec l1 u1 l2 u2"
      and l1: "l1 \<le> interpret_floatarith a xs" and u1: "interpret_floatarith a xs \<le> u1"
      and l2: "l2 \<le> interpret_floatarith b xs" and u2: "interpret_floatarith b xs \<le> u2"
      by blast
  from bnds_powr[OF lu] l1 u1 l2 u2
    show ?case by simp
next
  case (Ln a)
  with lift_un_bnds[OF bnds_ln] show ?case by auto
next
  case (Power a n)
  with lift_un'_bnds[OF bnds_power] show ?case by auto
next
  case (Floor a)
  from lift_un'[OF Floor.prems[unfolded approx.simps] Floor.hyps]
  show ?case by (auto simp: floor_fl.rep_eq floor_mono)
next
  case (Num f)
  thus ?case by auto
next
  case (Var n)
  from this[symmetric] \<open>bounded_by xs vs\<close>[THEN bounded_byE, of n]
  show ?case by (cases "n < length vs") auto
qed

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

fun approx_form' and approx_form :: "nat \<Rightarrow> form \<Rightarrow> (float * float) option list \<Rightarrow> nat list \<Rightarrow> bool" where
"approx_form' prec f 0 n l u bs ss = approx_form prec f (bs[n := Some (l, u)]) ss" |
"approx_form' prec f (Suc s) n l u bs ss =
  (let m = (l + u) * Float 1 (- 1)
   in (if approx_form' prec f s n l m bs ss then approx_form' prec f s n m u bs ss else False))" |
"approx_form prec (Bound (Var n) a b f) bs ss =
   (case (approx prec a bs, approx prec b bs)
   of (Some (l, _), Some (_, u)) \<Rightarrow> approx_form' prec f (ss ! n) n l u bs ss
    | _ \<Rightarrow> False)" |
"approx_form prec (Assign (Var n) a f) bs ss =
   (case (approx prec a bs)
   of (Some (l, u)) \<Rightarrow> approx_form' prec f (ss ! n) n l u bs ss
    | _ \<Rightarrow> False)" |
"approx_form prec (Less a b) bs ss =
   (case (approx prec a bs, approx prec b bs)
   of (Some (l, u), Some (l', u')) \<Rightarrow> float_plus_up prec u (-l') < 0
    | _ \<Rightarrow> False)" |
"approx_form prec (LessEqual a b) bs ss =
   (case (approx prec a bs, approx prec b bs)
   of (Some (l, u), Some (l', u')) \<Rightarrow> float_plus_up prec u (-l') \<le> 0
    | _ \<Rightarrow> False)" |
"approx_form prec (AtLeastAtMost x a b) bs ss =
   (case (approx prec x bs, approx prec a bs, approx prec b bs)
   of (Some (lx, ux), Some (l, u), Some (l', u')) \<Rightarrow> float_plus_up prec u (-lx) \<le> 0 \<and> float_plus_up prec ux (-l') \<le> 0
    | _ \<Rightarrow> False)" |
"approx_form prec (Conj a b) bs ss \<longleftrightarrow> approx_form prec a bs ss \<and> approx_form prec b bs ss" |
"approx_form prec (Disj a b) bs ss \<longleftrightarrow> approx_form prec a bs ss \<or> approx_form prec b bs ss" |
"approx_form _ _ _ _ = False"

lemma lazy_conj: "(if A then B else False) = (A \<and> B)" by simp

lemma approx_form_approx_form':
  assumes "approx_form' prec f s n l u bs ss"
    and "(x::real) \<in> { l .. u }"
  obtains l' u' where "x \<in> { l' .. u' }"
    and "approx_form prec f (bs[n := Some (l', u')]) ss"
using assms proof (induct s arbitrary: l u)
  case 0
  from this(1)[of l u] this(2,3)
  show thesis by auto
next
  case (Suc s)

  let ?m = "(l + u) * Float 1 (- 1)"
  have "real_of_float l \<le> ?m" and "?m \<le> real_of_float u"
    unfolding less_eq_float_def using Suc.prems by auto

  with \<open>x \<in> { l .. u }\<close>
  have "x \<in> { l .. ?m} \<or> x \<in> { ?m .. u }" by auto
  thus thesis
  proof (rule disjE)
    assume *: "x \<in> { l .. ?m }"
    with Suc.hyps[OF _ _ *] Suc.prems
    show thesis by (simp add: Let_def lazy_conj)
  next
    assume *: "x \<in> { ?m .. u }"
    with Suc.hyps[OF _ _ *] Suc.prems
    show thesis by (simp add: Let_def lazy_conj)
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

  with Bound.prems obtain l u' l' u
    where l_eq: "Some (l, u') = approx prec a vs"
    and u_eq: "Some (l', u) = approx prec b vs"
    and approx_form': "approx_form' prec f (ss ! n) n l u vs ss"
    by (cases "approx prec a vs", simp) (cases "approx prec b vs", auto)

  have "interpret_form f xs"
    if "xs ! n \<in> { interpret_floatarith a xs .. interpret_floatarith b xs }"
  proof -
    from approx[OF Bound.prems(2) l_eq] and approx[OF Bound.prems(2) u_eq] that
    have "xs ! n \<in> { l .. u}" by auto

    from approx_form_approx_form'[OF approx_form' this]
    obtain lx ux where bnds: "xs ! n \<in> { lx .. ux }"
      and approx_form: "approx_form prec f (vs[n := Some (lx, ux)]) ss" .

    from \<open>bounded_by xs vs\<close> bnds have "bounded_by xs (vs[n := Some (lx, ux)])"
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

  with Assign.prems obtain l u
    where bnd_eq: "Some (l, u) = approx prec a vs"
    and x_eq: "x = Var n"
    and approx_form': "approx_form' prec f (ss ! n) n l u vs ss"
    by (cases "approx prec a vs") auto

  have "interpret_form f xs"
    if bnds: "xs ! n = interpret_floatarith a xs"
  proof -
    from approx[OF Assign.prems(2) bnd_eq] bnds
    have "xs ! n \<in> { l .. u}" by auto
    from approx_form_approx_form'[OF approx_form' this]
    obtain lx ux where bnds: "xs ! n \<in> { lx .. ux }"
      and approx_form: "approx_form prec f (vs[n := Some (lx, ux)]) ss" .

    from \<open>bounded_by xs vs\<close> bnds have "bounded_by xs (vs[n := Some (lx, ux)])"
      by (rule bounded_by_update)
    with Assign.hyps[OF approx_form] show ?thesis
      by blast
  qed
  thus ?case
    using interpret_form.simps x_eq and interpret_floatarith.simps by simp
next
  case (Less a b)
  then obtain l u l' u'
    where l_eq: "Some (l, u) = approx prec a vs"
      and u_eq: "Some (l', u') = approx prec b vs"
      and inequality: "real_of_float (float_plus_up prec u (-l')) < 0"
    by (cases "approx prec a vs", auto, cases "approx prec b vs", auto)
  from le_less_trans[OF float_plus_up inequality]
    approx[OF Less.prems(2) l_eq] approx[OF Less.prems(2) u_eq]
  show ?case by auto
next
  case (LessEqual a b)
  then obtain l u l' u'
    where l_eq: "Some (l, u) = approx prec a vs"
      and u_eq: "Some (l', u') = approx prec b vs"
      and inequality: "real_of_float (float_plus_up prec u (-l')) \<le> 0"
    by (cases "approx prec a vs", auto, cases "approx prec b vs", auto)
  from order_trans[OF float_plus_up inequality]
    approx[OF LessEqual.prems(2) l_eq] approx[OF LessEqual.prems(2) u_eq]
  show ?case by auto
next
  case (AtLeastAtMost x a b)
  then obtain lx ux l u l' u'
    where x_eq: "Some (lx, ux) = approx prec x vs"
    and l_eq: "Some (l, u) = approx prec a vs"
    and u_eq: "Some (l', u') = approx prec b vs"
    and inequality: "real_of_float (float_plus_up prec u (-lx)) \<le> 0" "real_of_float (float_plus_up prec ux (-l')) \<le> 0"
    by (cases "approx prec x vs", auto,
      cases "approx prec a vs", auto,
      cases "approx prec b vs", auto)
  from order_trans[OF float_plus_up inequality(1)] order_trans[OF float_plus_up inequality(2)]
    approx[OF AtLeastAtMost.prems(2) l_eq] approx[OF AtLeastAtMost.prems(2) u_eq] approx[OF AtLeastAtMost.prems(2) x_eq]
  show ?case by auto
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

fun isDERIV_approx :: "nat \<Rightarrow> nat \<Rightarrow> floatarith \<Rightarrow> (float * float) option list \<Rightarrow> bool" where
"isDERIV_approx prec x (Add a b) vs         = (isDERIV_approx prec x a vs \<and> isDERIV_approx prec x b vs)" |
"isDERIV_approx prec x (Mult a b) vs        = (isDERIV_approx prec x a vs \<and> isDERIV_approx prec x b vs)" |
"isDERIV_approx prec x (Minus a) vs         = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Inverse a) vs       =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some (l, u) \<Rightarrow> 0 < l \<or> u < 0 | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Cos a) vs           = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Arctan a) vs        = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Min a b) vs         = False" |
"isDERIV_approx prec x (Max a b) vs         = False" |
"isDERIV_approx prec x (Abs a) vs           = False" |
"isDERIV_approx prec x Pi vs                = True" |
"isDERIV_approx prec x (Sqrt a) vs          =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some (l, u) \<Rightarrow> 0 < l | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Exp a) vs           = isDERIV_approx prec x a vs" |
"isDERIV_approx prec x (Powr a b) vs        =
  (isDERIV_approx prec x a vs \<and> isDERIV_approx prec x b vs \<and> (case approx prec a vs of Some (l, u) \<Rightarrow> 0 < l | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Ln a) vs            =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some (l, u) \<Rightarrow> 0 < l | None \<Rightarrow> False))" |
"isDERIV_approx prec x (Power a 0) vs       = True" |
"isDERIV_approx prec x (Floor a) vs         =
  (isDERIV_approx prec x a vs \<and> (case approx prec a vs of Some (l, u) \<Rightarrow> l > floor u \<and> u < ceiling l | None \<Rightarrow> False))" |
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
  then obtain l u where approx_Some: "Some (l, u) = approx prec a vs"
    and *: "0 < l \<or> u < 0"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some]
  have "interpret_floatarith a xs \<noteq> 0" by auto
  thus ?case using Inverse by auto
next
  case (Ln a)
  then obtain l u where approx_Some: "Some (l, u) = approx prec a vs"
    and *: "0 < l"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some]
  have "0 < interpret_floatarith a xs" by auto
  thus ?case using Ln by auto
next
  case (Sqrt a)
  then obtain l u where approx_Some: "Some (l, u) = approx prec a vs"
    and *: "0 < l"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some]
  have "0 < interpret_floatarith a xs" by auto
  thus ?case using Sqrt by auto
next
  case (Power a n)
  thus ?case by (cases n) auto
next
  case (Powr a b)
  from Powr obtain l1 u1 where a: "Some (l1, u1) = approx prec a vs" and pos: "0 < l1"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> a]
    have "0 < interpret_floatarith a xs" by auto
  with Powr show ?case by auto
next
  case (Floor a)
  then obtain l u where approx_Some: "Some (l, u) = approx prec a vs"
    and "real_of_int \<lfloor>real_of_float u\<rfloor> < real_of_float l" "real_of_float u < real_of_int \<lceil>real_of_float l\<rceil>"
    and "isDERIV x a xs"
    by (cases "approx prec a vs") auto
  with approx[OF \<open>bounded_by xs vs\<close> approx_Some] le_floor_iff
  show ?case
    by (force elim!: Ints_cases)
qed auto

lemma bounded_by_update_var:
  assumes "bounded_by xs vs"
    and "vs ! i = Some (l, u)"
    and bnd: "x \<in> { real_of_float l .. real_of_float u }"
  shows "bounded_by (xs[i := x]) vs"
proof (cases "i < length xs")
  case False
  thus ?thesis
    using \<open>bounded_by xs vs\<close> by auto
next
  case True
  let ?xs = "xs[i := x]"
  from True have "i < length ?xs" by auto
  have "case vs ! j of None \<Rightarrow> True | Some (l, u) \<Rightarrow> ?xs ! j \<in> {real_of_float l .. real_of_float u}"
    if "j < length vs" for j
  proof (cases "vs ! j")
    case None
    then show ?thesis by simp
  next
    case (Some b)
    thus ?thesis
    proof (cases "i = j")
      case True
      thus ?thesis using \<open>vs ! i = Some (l, u)\<close> Some and bnd \<open>i < length ?xs\<close>
        by auto
    next
      case False
      thus ?thesis
        using \<open>bounded_by xs vs\<close>[THEN bounded_byE, OF \<open>j < length vs\<close>] Some by auto
    qed
  qed
  thus ?thesis
    unfolding bounded_by_def by auto
qed

lemma isDERIV_approx':
  assumes "bounded_by xs vs"
    and vs_x: "vs ! x = Some (l, u)"
    and X_in: "X \<in> {real_of_float l .. real_of_float u}"
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
    and app: "Some (l, u) = approx prec (DERIV_floatarith n f) vs" (is "_ = approx _ ?D _")
  shows "\<exists>(x::real). l \<le> x \<and> x \<le> u \<and>
             DERIV (\<lambda> x. interpret_floatarith f (xs[n := x])) (xs!n) :> x"
         (is "\<exists> x. _ \<and> _ \<and> DERIV (?i f) _ :> _")
proof (rule exI[of _ "?i ?D (xs!n)"], rule conjI[OF _ conjI])
  let "?i f" = "\<lambda>x. interpret_floatarith f (xs[n := x])"
  from approx[OF bnd app]
  show "l \<le> ?i ?D (xs!n)" and "?i ?D (xs!n) \<le> u"
    using \<open>n < length xs\<close> by auto
  from DERIV_floatarith[OF \<open>n < length xs\<close>, of f "xs!n"] isDERIV_approx[OF bnd isD]
  show "DERIV (?i f) (xs!n) :> (?i ?D (xs!n))"
    by simp
qed

lemma lift_bin_aux:
  assumes lift_bin_Some: "Some (l, u) = lift_bin a b f"
  obtains l1 u1 l2 u2
  where "a = Some (l1, u1)"
    and "b = Some (l2, u2)"
    and "f l1 u1 l2 u2 = Some (l, u)"
  using assms by (cases a, simp, cases b, simp, auto)


fun approx_tse where
"approx_tse prec n 0 c k f bs = approx prec f bs" |
"approx_tse prec n (Suc s) c k f bs =
  (if isDERIV_approx prec n f bs then
    lift_bin (approx prec f (bs[n := Some (c,c)]))
             (approx_tse prec n s c (Suc k) (DERIV_floatarith n f) bs)
             (\<lambda> l1 u1 l2 u2. approx prec
                 (Add (Var 0)
                      (Mult (Inverse (Num (Float (int k) 0)))
                                 (Mult (Add (Var (Suc (Suc 0))) (Minus (Num c)))
                                       (Var (Suc 0))))) [Some (l1, u1), Some (l2, u2), bs!n])
  else approx prec f bs)"

lemma bounded_by_Cons:
  assumes bnd: "bounded_by xs vs"
    and x: "x \<in> { real_of_float l .. real_of_float u }"
  shows "bounded_by (x#xs) ((Some (l, u))#vs)"
proof -
  have "case ((Some (l,u))#vs) ! i of Some (l, u) \<Rightarrow> (x#xs)!i \<in> { real_of_float l .. real_of_float u } | None \<Rightarrow> True"
    if *: "i < length ((Some (l, u))#vs)" for i
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
    and bnd_x: "vs ! x = Some (lx, ux)"
    and ate: "Some (l, u) = approx_tse prec x s c k f vs"
  shows "\<exists> n. (\<forall> m < n. \<forall> (z::real) \<in> {lx .. ux}.
      DERIV (\<lambda> y. interpret_floatarith ((DERIV_floatarith x ^^ m) f) (xs[x := y])) z :>
            (interpret_floatarith ((DERIV_floatarith x ^^ (Suc m)) f) (xs[x := z])))
   \<and> (\<forall> (t::real) \<in> {lx .. ux}.  (\<Sum> i = 0..<n. inverse (real (\<Prod> j \<in> {k..<k+i}. j)) *
                  interpret_floatarith ((DERIV_floatarith x ^^ i) f) (xs[x := c]) *
                  (xs!x - c)^i) +
      inverse (real (\<Prod> j \<in> {k..<k+n}. j)) *
      interpret_floatarith ((DERIV_floatarith x ^^ n) f) (xs[x := t]) *
      (xs!x - c)^n \<in> {l .. u})" (is "\<exists> n. ?taylor f k l u n")
  using ate
proof (induct s arbitrary: k f l u)
  case 0
  {
    fix t::real assume "t \<in> {lx .. ux}"
    note bounded_by_update_var[OF \<open>bounded_by xs vs\<close> bnd_x this]
    from approx[OF this 0[unfolded approx_tse.simps]]
    have "(interpret_floatarith f (xs[x := t])) \<in> {l .. u}"
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
      fix t::real assume "t \<in> {lx .. ux}"
      note bounded_by_update_var[OF \<open>bounded_by xs vs\<close> bnd_x this]
      from approx[OF this ap]
      have "(interpret_floatarith f (xs[x := t])) \<in> {l .. u}"
        by (auto simp add: algebra_simps)
    }
    thus ?thesis by (auto intro!: exI[of _ 0])
  next
    case True
    with Suc.prems
    obtain l1 u1 l2 u2
      where a: "Some (l1, u1) = approx prec f (vs[x := Some (c,c)])"
        and ate: "Some (l2, u2) = approx_tse prec x s c (Suc k) (DERIV_floatarith x f) vs"
        and final: "Some (l, u) = approx prec
          (Add (Var 0)
               (Mult (Inverse (Num (Float (int k) 0)))
                     (Mult (Add (Var (Suc (Suc 0))) (Minus (Num c)))
                           (Var (Suc 0))))) [Some (l1, u1), Some (l2, u2), vs!x]"
      by (auto elim!: lift_bin_aux)

    from bnd_c \<open>x < length xs\<close>
    have bnd: "bounded_by (xs[x:=c]) (vs[x:= Some (c,c)])"
      by (auto intro!: bounded_by_update)

    from approx[OF this a]
    have f_c: "interpret_floatarith ((DERIV_floatarith x ^^ 0) f) (xs[x := c]) \<in> { l1 .. u1 }"
              (is "?f 0 (real_of_float c) \<in> _")
      by auto

    have funpow_Suc[symmetric]: "(f ^^ Suc n) x = (f ^^ n) (f x)"
      for f :: "'a \<Rightarrow> 'a" and n :: nat and x :: 'a
      by (induct n) auto
    from Suc.hyps[OF ate, unfolded this] obtain n
      where DERIV_hyp: "\<And>m z. \<lbrakk> m < n ; (z::real) \<in> { lx .. ux } \<rbrakk> \<Longrightarrow>
        DERIV (?f (Suc m)) z :> ?f (Suc (Suc m)) z"
      and hyp: "\<forall>t \<in> {real_of_float lx .. real_of_float ux}.
        (\<Sum> i = 0..<n. inverse (real (\<Prod> j \<in> {Suc k..<Suc k + i}. j)) * ?f (Suc i) c * (xs!x - c)^i) +
          inverse (real (\<Prod> j \<in> {Suc k..<Suc k + n}. j)) * ?f (Suc n) t * (xs!x - c)^n \<in> {l2 .. u2}"
          (is "\<forall> t \<in> _. ?X (Suc k) f n t \<in> _")
      by blast

    have DERIV: "DERIV (?f m) z :> ?f (Suc m) z"
      if "m < Suc n" and bnd_z: "z \<in> { lx .. ux }" for m and z::real
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
      fix t::real assume t: "t \<in> {lx .. ux}"
      hence "bounded_by [xs!x] [vs!x]"
        using \<open>bounded_by xs vs\<close>[THEN bounded_byE, OF \<open>x < length vs\<close>]
        by (cases "vs!x", auto simp add: bounded_by_def)

      with hyp[THEN bspec, OF t] f_c
      have "bounded_by [?f 0 c, ?X (Suc k) f n t, xs!x] [Some (l1, u1), Some (l2, u2), vs!x]"
        by (auto intro!: bounded_by_Cons)
      from approx[OF this final, unfolded atLeastAtMost_iff[symmetric]]
      have "?X (Suc k) f n t * (xs!x - real_of_float c) * inverse k + ?f 0 c \<in> {l .. u}"
        by (auto simp add: algebra_simps)
      also have "?X (Suc k) f n t * (xs!x - real_of_float c) * inverse (real k) + ?f 0 c =
               (\<Sum> i = 0..<Suc n. inverse (real (\<Prod> j \<in> {k..<k+i}. j)) * ?f i c * (xs!x - c)^i) +
               inverse (real (\<Prod> j \<in> {k..<k+Suc n}. j)) * ?f (Suc n) t * (xs!x - c)^Suc n" (is "_ = ?T")
        unfolding funpow_Suc C_def[symmetric] sum_move0 prod_head_Suc
        by (auto simp add: algebra_simps)
          (simp only: mult.left_commute [of _ "inverse (real k)"] sum_distrib_left [symmetric])
      finally have "?T \<in> {l .. u}" .
    }
    thus ?thesis using DERIV by blast
  qed
qed

lemma prod_fact: "real (\<Prod> {1..<1 + k}) = fact (k :: nat)"
  by (simp add: fact_prod atLeastLessThanSuc_atLeastAtMost)

lemma approx_tse:
  assumes "bounded_by xs vs"
    and bnd_x: "vs ! x = Some (lx, ux)"
    and bnd_c: "real_of_float c \<in> {lx .. ux}"
    and "x < length vs" and "x < length xs"
    and ate: "Some (l, u) = approx_tse prec x s c 1 f vs"
  shows "interpret_floatarith f xs \<in> {l .. u}"
proof -
  define F where [abs_def]: "F n z =
    interpret_floatarith ((DERIV_floatarith x ^^ n) f) (xs[x := z])" for n z
  hence F0: "F 0 = (\<lambda> z. interpret_floatarith f (xs[x := z]))" by auto

  hence "bounded_by (xs[x := c]) vs" and "x < length vs" "x < length xs"
    using \<open>bounded_by xs vs\<close> bnd_x bnd_c \<open>x < length vs\<close> \<open>x < length xs\<close>
    by (auto intro!: bounded_by_update_var)

  from approx_tse_generic[OF \<open>bounded_by xs vs\<close> this bnd_x ate]
  obtain n
    where DERIV: "\<forall> m z. m < n \<and> real_of_float lx \<le> z \<and> z \<le> real_of_float ux \<longrightarrow> DERIV (F m) z :> F (Suc m) z"
    and hyp: "\<And> (t::real). t \<in> {lx .. ux} \<Longrightarrow>
           (\<Sum> j = 0..<n. inverse(fact j) * F j c * (xs!x - c)^j) +
             inverse ((fact n)) * F n t * (xs!x - c)^n
             \<in> {l .. u}" (is "\<And> t. _ \<Longrightarrow> ?taylor t \<in> _")
    unfolding F_def atLeastAtMost_iff[symmetric] prod_fact
    by blast

  have bnd_xs: "xs ! x \<in> { lx .. ux }"
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
      have "lx \<le> real_of_float c" "real_of_float c \<le> ux" "lx \<le> xs!x" "xs!x \<le> ux"
        using Suc bnd_c \<open>bounded_by xs vs\<close>[THEN bounded_byE, OF \<open>x < length vs\<close>] bnd_x by auto
      from Taylor[OF zero_less_Suc, of F, OF F0 DERIV[unfolded Suc] this False]
      obtain t::real where t_bnd: "if xs ! x < c then xs ! x < t \<and> t < c else c < t \<and> t < xs ! x"
        and fl_eq: "interpret_floatarith f (xs[x := xs ! x]) =
           (\<Sum>m = 0..<Suc n'. F m c / (fact m) * (xs ! x - c) ^ m) +
           F (Suc n') t / (fact (Suc n')) * (xs ! x - c) ^ Suc n'"
        unfolding atLeast0LessThan by blast

      from t_bnd bnd_xs bnd_c have *: "t \<in> {lx .. ux}"
        by (cases "xs ! x < c") auto

      have "interpret_floatarith f (xs[x := xs ! x]) = ?taylor t"
        unfolding fl_eq Suc by (auto simp add: algebra_simps divide_inverse)
      also have "\<dots> \<in> {l .. u}"
        using * by (rule hyp)
      finally show ?thesis
        by simp
    qed
  qed
qed

fun approx_tse_form' where
"approx_tse_form' prec t f 0 l u cmp =
  (case approx_tse prec 0 t ((l + u) * Float 1 (- 1)) 1 f [Some (l, u)]
     of Some (l, u) \<Rightarrow> cmp l u | None \<Rightarrow> False)" |
"approx_tse_form' prec t f (Suc s) l u cmp =
  (let m = (l + u) * Float 1 (- 1)
   in (if approx_tse_form' prec t f s l m cmp then
      approx_tse_form' prec t f s m u cmp else False))"

lemma approx_tse_form':
  fixes x :: real
  assumes "approx_tse_form' prec t f s l u cmp"
    and "x \<in> {l .. u}"
  shows "\<exists>l' u' ly uy. x \<in> {l' .. u'} \<and> real_of_float l \<le> l' \<and> u' \<le> real_of_float u \<and> cmp ly uy \<and>
    approx_tse prec 0 t ((l' + u') * Float 1 (- 1)) 1 f [Some (l', u')] = Some (ly, uy)"
  using assms
proof (induct s arbitrary: l u)
  case 0
  then obtain ly uy
    where *: "approx_tse prec 0 t ((l + u) * Float 1 (- 1)) 1 f [Some (l, u)] = Some (ly, uy)"
    and **: "cmp ly uy" by (auto elim!: case_optionE)
  with 0 show ?case by auto
next
  case (Suc s)
  let ?m = "(l + u) * Float 1 (- 1)"
  from Suc.prems
  have l: "approx_tse_form' prec t f s l ?m cmp"
    and u: "approx_tse_form' prec t f s ?m u cmp"
    by (auto simp add: Let_def lazy_conj)

  have m_l: "real_of_float l \<le> ?m" and m_u: "?m \<le> real_of_float u"
    unfolding less_eq_float_def using Suc.prems by auto
  with \<open>x \<in> { l .. u }\<close> consider "x \<in> { l .. ?m}" | "x \<in> {?m .. u}"
    by atomize_elim auto
  thus ?case
  proof cases
    case 1
    from Suc.hyps[OF l this]
    obtain l' u' ly uy where
      "x \<in> {l' .. u'} \<and> real_of_float l \<le> l' \<and> real_of_float u' \<le> ?m \<and> cmp ly uy \<and>
        approx_tse prec 0 t ((l' + u') * Float 1 (- 1)) 1 f [Some (l', u')] = Some (ly, uy)"
      by blast
    with m_u show ?thesis
      by (auto intro!: exI)
  next
    case 2
    from Suc.hyps[OF u this]
    obtain l' u' ly uy where
      "x \<in> { l' .. u' } \<and> ?m \<le> real_of_float l' \<and> u' \<le> real_of_float u \<and> cmp ly uy \<and>
        approx_tse prec 0 t ((l' + u') * Float 1 (- 1)) 1 f [Some (l', u')] = Some (ly, uy)"
      by blast
    with m_u show ?thesis
      by (auto intro!: exI)
  qed
qed

lemma approx_tse_form'_less:
  fixes x :: real
  assumes tse: "approx_tse_form' prec t (Add a (Minus b)) s l u (\<lambda> l u. 0 < l)"
    and x: "x \<in> {l .. u}"
  shows "interpret_floatarith b [x] < interpret_floatarith a [x]"
proof -
  from approx_tse_form'[OF tse x]
  obtain l' u' ly uy
    where x': "x \<in> {l' .. u'}"
    and "real_of_float l \<le> real_of_float l'"
    and "real_of_float u' \<le> real_of_float u" and "0 < ly"
    and tse: "approx_tse prec 0 t ((l' + u') * Float 1 (- 1)) 1 (Add a (Minus b)) [Some (l', u')] = Some (ly, uy)"
    by blast

  hence "bounded_by [x] [Some (l', u')]"
    by (auto simp add: bounded_by_def)
  from approx_tse[OF this _ _ _ _ tse[symmetric], of l' u'] x'
  have "ly \<le> interpret_floatarith a [x] - interpret_floatarith b [x]"
    by auto
  from order_less_le_trans[OF _ this, of 0] \<open>0 < ly\<close> show ?thesis
    by auto
qed

lemma approx_tse_form'_le:
  fixes x :: real
  assumes tse: "approx_tse_form' prec t (Add a (Minus b)) s l u (\<lambda> l u. 0 \<le> l)"
    and x: "x \<in> {l .. u}"
  shows "interpret_floatarith b [x] \<le> interpret_floatarith a [x]"
proof -
  from approx_tse_form'[OF tse x]
  obtain l' u' ly uy
    where x': "x \<in> {l' .. u'}"
    and "l \<le> real_of_float l'"
    and "real_of_float u' \<le> u" and "0 \<le> ly"
    and tse: "approx_tse prec 0 t ((l' + u') * Float 1 (- 1)) 1 (Add a (Minus b)) [Some (l', u')] = Some (ly, uy)"
    by blast

  hence "bounded_by [x] [Some (l', u')]" by (auto simp add: bounded_by_def)
  from approx_tse[OF this _ _ _ _ tse[symmetric], of l' u'] x'
  have "ly \<le> interpret_floatarith a [x] - interpret_floatarith b [x]"
    by auto
  from order_trans[OF _ this, of 0] \<open>0 \<le> ly\<close> show ?thesis
    by auto
qed

fun approx_tse_concl where
"approx_tse_concl prec t (Less lf rt) s l u l' u' \<longleftrightarrow>
    approx_tse_form' prec t (Add rt (Minus lf)) s l u' (\<lambda> l u. 0 < l)" |
"approx_tse_concl prec t (LessEqual lf rt) s l u l' u' \<longleftrightarrow>
    approx_tse_form' prec t (Add rt (Minus lf)) s l u' (\<lambda> l u. 0 \<le> l)" |
"approx_tse_concl prec t (AtLeastAtMost x lf rt) s l u l' u' \<longleftrightarrow>
    (if approx_tse_form' prec t (Add x (Minus lf)) s l u' (\<lambda> l u. 0 \<le> l) then
      approx_tse_form' prec t (Add rt (Minus x)) s l u' (\<lambda> l u. 0 \<le> l) else False)" |
"approx_tse_concl prec t (Conj f g) s l u l' u' \<longleftrightarrow>
    approx_tse_concl prec t f s l u l' u' \<and> approx_tse_concl prec t g s l u l' u'" |
"approx_tse_concl prec t (Disj f g) s l u l' u' \<longleftrightarrow>
    approx_tse_concl prec t f s l u l' u' \<or> approx_tse_concl prec t g s l u l' u'" |
"approx_tse_concl _ _ _ _ _ _ _ _ \<longleftrightarrow> False"

definition
  "approx_tse_form prec t s f =
    (case f of
      Bound x a b f \<Rightarrow>
        x = Var 0 \<and>
        (case (approx prec a [None], approx prec b [None]) of
          (Some (l, u), Some (l', u')) \<Rightarrow> approx_tse_concl prec t f s l u l' u'
        | _ \<Rightarrow> False)
    | _ \<Rightarrow> False)"

lemma approx_tse_form:
  assumes "approx_tse_form prec t s f"
  shows "interpret_form f [x]"
proof (cases f)
  case f_def: (Bound i a b f')
  with assms obtain l u l' u'
    where a: "approx prec a [None] = Some (l, u)"
    and b: "approx prec b [None] = Some (l', u')"
    unfolding approx_tse_form_def by (auto elim!: case_optionE)

  from f_def assms have "i = Var 0"
    unfolding approx_tse_form_def by auto
  hence i: "interpret_floatarith i [x] = x" by auto

  {
    let ?f = "\<lambda>z. interpret_floatarith z [x]"
    assume "?f i \<in> { ?f a .. ?f b }"
    with approx[OF _ a[symmetric], of "[x]"] approx[OF _ b[symmetric], of "[x]"]
    have bnd: "x \<in> { l .. u'}" unfolding bounded_by_def i by auto

    have "interpret_form f' [x]"
      using assms[unfolded f_def]
    proof (induct f')
      case (Less lf rt)
      with a b
      have "approx_tse_form' prec t (Add rt (Minus lf)) s l u' (\<lambda> l u. 0 < l)"
        unfolding approx_tse_form_def by auto
      from approx_tse_form'_less[OF this bnd]
      show ?case using Less by auto
    next
      case (LessEqual lf rt)
      with f_def a b assms
      have "approx_tse_form' prec t (Add rt (Minus lf)) s l u' (\<lambda> l u. 0 \<le> l)"
        unfolding approx_tse_form_def by auto
      from approx_tse_form'_le[OF this bnd]
      show ?case using LessEqual by auto
    next
      case (AtLeastAtMost x lf rt)
      with f_def a b assms
      have "approx_tse_form' prec t (Add rt (Minus x)) s l u' (\<lambda> l u. 0 \<le> l)"
        and "approx_tse_form' prec t (Add x (Minus lf)) s l u' (\<lambda> l u. 0 \<le> l)"
        unfolding approx_tse_form_def lazy_conj by (auto split: if_split_asm)
      from approx_tse_form'_le[OF this(1) bnd] approx_tse_form'_le[OF this(2) bnd]
      show ?case using AtLeastAtMost by auto
    qed (auto simp: f_def approx_tse_form_def elim!: case_optionE)
  }
  thus ?thesis unfolding f_def by auto
qed (insert assms, auto simp add: approx_tse_form_def)

text \<open>\<^term>\<open>approx_form_eval\<close> is only used for the {\tt value}-command.\<close>

fun approx_form_eval :: "nat \<Rightarrow> form \<Rightarrow> (float * float) option list \<Rightarrow> (float * float) option list" where
"approx_form_eval prec (Bound (Var n) a b f) bs =
   (case (approx prec a bs, approx prec b bs)
   of (Some (l, _), Some (_, u)) \<Rightarrow> approx_form_eval prec f (bs[n := Some (l, u)])
    | _ \<Rightarrow> bs)" |
"approx_form_eval prec (Assign (Var n) a f) bs =
   (case (approx prec a bs)
   of (Some (l, u)) \<Rightarrow> approx_form_eval prec f (bs[n := Some (l, u)])
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
        "replicate :: _ \<Rightarrow> (float \<times> float) option \<Rightarrow> _"
        approx'
        approx_form
        approx_tse_form
        approx_form_eval
      datatypes: bool
        int
        nat
        integer
        "nat list"
        "(float \<times> float) option list"
        floatarith
        form
    } ctxt ct

  fun term_of_bool true = \<^term>\<open>True\<close>
    | term_of_bool false = \<^term>\<open>False\<close>;

  val mk_int = HOLogic.mk_number \<^typ>\<open>int\<close> o @{code integer_of_int};

  fun term_of_float (@{code Float} (k, l)) =
    \<^term>\<open>Float\<close> $ mk_int k $ mk_int l;

  fun term_of_float_float_option NONE = \<^term>\<open>None :: (float \<times> float) option\<close>
    | term_of_float_float_option (SOME ff) = \<^term>\<open>Some :: float \<times> float \<Rightarrow> _\<close>
        $ HOLogic.mk_prod (apply2 term_of_float ff);

  val term_of_float_float_option_list =
    HOLogic.mk_list \<^typ>\<open>(float \<times> float) option\<close> o map term_of_float_float_option;

  val approx_bool = @{computation bool}
    (fn _ => fn x => case x of SOME b => term_of_bool b
      | NONE => error "Computation approx_bool failed.")
  val approx_arith = @{computation "(float \<times> float) option"}
    (fn _ => fn x => case x of SOME ffo => term_of_float_float_option ffo
      | NONE => error "Computation approx_arith failed.")
  val approx_form_eval = @{computation "(float \<times> float) option list"}
    (fn _ => fn x => case x of SOME ffos => term_of_float_float_option_list ffos
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
