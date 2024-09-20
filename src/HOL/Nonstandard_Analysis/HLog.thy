(*  Title:      HOL/Nonstandard_Analysis/HLog.thy
    Author:     Jacques D. Fleuriot
    Copyright:  2000, 2001 University of Edinburgh
*)

section \<open>Logarithms: Non-Standard Version\<close>

theory HLog
  imports HTranscendental
begin

definition powhr :: "hypreal \<Rightarrow> hypreal \<Rightarrow> hypreal"  (infixr \<open>powhr\<close> 80)
  where [transfer_unfold]: "x powhr a = starfun2 (powr) x a"

definition hlog :: "hypreal \<Rightarrow> hypreal \<Rightarrow> hypreal"
  where [transfer_unfold]: "hlog a x = starfun2 log a x"

lemma powhr: "(star_n X) powhr (star_n Y) = star_n (\<lambda>n. (X n) powr (Y n))"
  by (simp add: powhr_def starfun2_star_n)

lemma powhr_one_eq_one [simp]: "\<And>a. 1 powhr a = 1"
  by transfer simp

lemma powhr_mult: "\<And>a x y. 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> (x * y) powhr a = (x powhr a) * (y powhr a)"
  by transfer (simp add: powr_mult)

lemma powhr_gt_zero [simp]: "\<And>a x. 0 < x powhr a \<longleftrightarrow> x \<noteq> 0"
  by transfer simp

lemma powhr_not_zero [simp]: "\<And>a x. x powhr a \<noteq> 0 \<longleftrightarrow> x \<noteq> 0"
  by transfer simp

lemma powhr_divide: "\<And>a x y. 0 \<le> x \<Longrightarrow> 0 \<le> y \<Longrightarrow> (x / y) powhr a = (x powhr a) / (y powhr a)"
  by transfer (rule powr_divide)

lemma powhr_add: "\<And>a b x. x powhr (a + b) = (x powhr a) * (x powhr b)"
  by transfer (rule powr_add)

lemma powhr_powhr: "\<And>a b x. (x powhr a) powhr b = x powhr (a * b)"
  by transfer (rule powr_powr)

lemma powhr_powhr_swap: "\<And>a b x. (x powhr a) powhr b = (x powhr b) powhr a"
  by transfer (rule powr_powr_swap)

lemma powhr_minus: "\<And>a x. x powhr (- a) = inverse (x powhr a)"
  by transfer (rule powr_minus)

lemma powhr_minus_divide: "x powhr (- a) = 1 / (x powhr a)"
  by (simp add: divide_inverse powhr_minus)

lemma powhr_less_mono: "\<And>a b x. a < b \<Longrightarrow> 1 < x \<Longrightarrow> x powhr a < x powhr b"
  by transfer simp

lemma powhr_less_cancel: "\<And>a b x. x powhr a < x powhr b \<Longrightarrow> 1 < x \<Longrightarrow> a < b"
  by transfer simp

lemma powhr_less_cancel_iff [simp]: "1 < x \<Longrightarrow> x powhr a < x powhr b \<longleftrightarrow> a < b"
  by (blast intro: powhr_less_cancel powhr_less_mono)

lemma powhr_le_cancel_iff [simp]: "1 < x \<Longrightarrow> x powhr a \<le> x powhr b \<longleftrightarrow> a \<le> b"
  by (simp add: linorder_not_less [symmetric])

lemma hlog: "hlog (star_n X) (star_n Y) = star_n (\<lambda>n. log (X n) (Y n))"
  by (simp add: hlog_def starfun2_star_n)

lemma hlog_starfun_ln: "\<And>x. ( *f* ln) x = hlog (( *f* exp) 1) x"
  by transfer (rule log_ln)

lemma powhr_hlog_cancel [simp]: "\<And>a x. 0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow> a powhr (hlog a x) = x"
  by transfer simp

lemma hlog_powhr_cancel [simp]: "\<And>a y. 0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> hlog a (a powhr y) = y"
  by transfer simp

lemma hlog_mult:
  "\<And>a x y. hlog a (x * y) = (if x\<noteq>0 \<and> y\<noteq>0 then hlog a x + hlog a y else 0)"
  by transfer (rule log_mult)

lemma hlog_as_starfun: "\<And>a x. 0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> hlog a x = ( *f* ln) x / ( *f* ln) a"
  by transfer (simp add: log_def)

lemma hlog_eq_div_starfun_ln_mult_hlog:
  "\<And>a b x. 0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> 0 < b \<Longrightarrow> b \<noteq> 1 \<Longrightarrow> 0 < x \<Longrightarrow>
    hlog a x = (( *f* ln) b / ( *f* ln) a) * hlog b x"
  by transfer (rule log_eq_div_ln_mult_log)

lemma powhr_as_starfun: "\<And>a x. x powhr a = (if x = 0 then 0 else ( *f* exp) (a * ( *f* real_ln) x))"
  by transfer (simp add: powr_def)

lemma HInfinite_powhr:
  "x \<in> HInfinite \<Longrightarrow> 0 < x \<Longrightarrow> a \<in> HFinite - Infinitesimal \<Longrightarrow> 0 < a \<Longrightarrow> x powhr a \<in> HInfinite"
  by (auto intro!: starfun_ln_ge_zero starfun_ln_HInfinite
        HInfinite_HFinite_not_Infinitesimal_mult2 starfun_exp_HInfinite
      simp add: order_less_imp_le HInfinite_gt_zero_gt_one powhr_as_starfun zero_le_mult_iff)

lemma hlog_hrabs_HInfinite_Infinitesimal:
  "x \<in> HFinite - Infinitesimal \<Longrightarrow> a \<in> HInfinite \<Longrightarrow> 0 < a \<Longrightarrow> hlog a \<bar>x\<bar> \<in> Infinitesimal"
  apply (frule HInfinite_gt_zero_gt_one)
   apply (auto intro!: starfun_ln_HFinite_not_Infinitesimal
      HInfinite_inverse_Infinitesimal Infinitesimal_HFinite_mult2
      simp add: starfun_ln_HInfinite not_Infinitesimal_not_zero
      hlog_as_starfun divide_inverse)
  done

lemma hlog_HInfinite_as_starfun: "a \<in> HInfinite \<Longrightarrow> 0 < a \<Longrightarrow> hlog a x = ( *f* ln) x / ( *f* ln) a"
  by (rule hlog_as_starfun) auto

lemma hlog_one [simp]: "\<And>a. hlog a 1 = 0"
  by transfer simp

lemma hlog_eq_one [simp]: "\<And>a. 0 < a \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> hlog a a = 1"
  by transfer (rule log_eq_one)

lemma hlog_inverse: "\<And>a x. hlog a (inverse x) = - hlog a x"
  by transfer (simp add: log_inverse)

lemma hlog_divide: "hlog a (x / y) = (if x\<noteq>0 \<and> y\<noteq>0 then hlog a x - hlog a y else 0)"
  by (simp add: hlog_mult hlog_inverse divide_inverse)

lemma hlog_less_cancel_iff [simp]:
  "\<And>a x y. 1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> hlog a x < hlog a y \<longleftrightarrow> x < y"
  by transfer simp

lemma hlog_le_cancel_iff [simp]: "1 < a \<Longrightarrow> 0 < x \<Longrightarrow> 0 < y \<Longrightarrow> hlog a x \<le> hlog a y \<longleftrightarrow> x \<le> y"
  by (simp add: linorder_not_less [symmetric])

end
