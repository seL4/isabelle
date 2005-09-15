(*  Title       : HLog.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2000,2001 University of Edinburgh
*)

header{*Logarithms: Non-Standard Version*}

theory HLog
imports Log HTranscendental
begin


(* should be in NSA.ML *)
lemma epsilon_ge_zero [simp]: "0 \<le> epsilon"
by (simp add: epsilon_def star_n_zero_num star_n_le)

lemma hpfinite_witness: "epsilon : {x. 0 \<le> x & x : HFinite}"
by auto


constdefs

    powhr  :: "[hypreal,hypreal] => hypreal"     (infixr "powhr" 80)
    "x powhr a == starfun2 (op powr) x a"
  
    hlog :: "[hypreal,hypreal] => hypreal"
    "hlog a x == starfun2 log a x"

declare powhr_def [transfer_unfold]
declare hlog_def [transfer_unfold]

lemma powhr: "(star_n X) powhr (star_n Y) = star_n (%n. (X n) powr (Y n))"
by (simp add: powhr_def starfun2_star_n)

lemma powhr_one_eq_one [simp]: "!!a. 1 powhr a = 1"
by (transfer, simp)

lemma powhr_mult:
  "!!a x y. [| 0 < x; 0 < y |] ==> (x * y) powhr a = (x powhr a) * (y powhr a)"
by (transfer, rule powr_mult)

lemma powhr_gt_zero [simp]: "!!a x. 0 < x powhr a"
by (transfer, simp)

lemma powhr_not_zero [simp]: "x powhr a \<noteq> 0"
by (rule powhr_gt_zero [THEN hypreal_not_refl2, THEN not_sym])

lemma powhr_divide:
  "!!a x y. [| 0 < x; 0 < y |] ==> (x / y) powhr a = (x powhr a)/(y powhr a)"
by (transfer, rule powr_divide)

lemma powhr_add: "!!a b x. x powhr (a + b) = (x powhr a) * (x powhr b)"
by (transfer, rule powr_add)

lemma powhr_powhr: "!!a b x. (x powhr a) powhr b = x powhr (a * b)"
by (transfer, rule powr_powr)

lemma powhr_powhr_swap: "!!a b x. (x powhr a) powhr b = (x powhr b) powhr a"
by (transfer, rule powr_powr_swap)

lemma powhr_minus: "!!a x. x powhr (-a) = inverse (x powhr a)"
by (transfer, rule powr_minus)

lemma powhr_minus_divide: "x powhr (-a) = 1/(x powhr a)"
by (simp add: divide_inverse powhr_minus)

lemma powhr_less_mono: "!!a b x. [| a < b; 1 < x |] ==> x powhr a < x powhr b"
by (transfer, simp)

lemma powhr_less_cancel: "!!a b x. [| x powhr a < x powhr b; 1 < x |] ==> a < b"
by (transfer, simp)

lemma powhr_less_cancel_iff [simp]:
     "1 < x ==> (x powhr a < x powhr b) = (a < b)"
by (blast intro: powhr_less_cancel powhr_less_mono)

lemma powhr_le_cancel_iff [simp]:
     "1 < x ==> (x powhr a \<le> x powhr b) = (a \<le> b)"
by (simp add: linorder_not_less [symmetric])

lemma hlog:
     "hlog (star_n X) (star_n Y) =  
      star_n (%n. log (X n) (Y n))"
by (simp add: hlog_def starfun2_star_n)

lemma hlog_starfun_ln: "!!x. ( *f* ln) x = hlog (( *f* exp) 1) x"
by (transfer, rule log_ln)

lemma powhr_hlog_cancel [simp]:
     "!!a x. [| 0 < a; a \<noteq> 1; 0 < x |] ==> a powhr (hlog a x) = x"
by (transfer, simp)

lemma hlog_powhr_cancel [simp]:
     "!!a y. [| 0 < a; a \<noteq> 1 |] ==> hlog a (a powhr y) = y"
by (transfer, simp)

lemma hlog_mult:
     "!!a x y. [| 0 < a; a \<noteq> 1; 0 < x; 0 < y  |]  
      ==> hlog a (x * y) = hlog a x + hlog a y"
by (transfer, rule log_mult)

lemma hlog_as_starfun:
     "!!a x. [| 0 < a; a \<noteq> 1 |] ==> hlog a x = ( *f* ln) x / ( *f* ln) a"
by (transfer, simp add: log_def)

lemma hlog_eq_div_starfun_ln_mult_hlog:
     "!!a b x. [| 0 < a; a \<noteq> 1; 0 < b; b \<noteq> 1; 0 < x |]  
      ==> hlog a x = (( *f* ln) b/( *f*ln) a) * hlog b x"
by (transfer, rule log_eq_div_ln_mult_log)

lemma powhr_as_starfun: "!!a x. x powhr a = ( *f* exp) (a * ( *f* ln) x)"
by (transfer, simp add: powr_def)

lemma HInfinite_powhr:
     "[| x : HInfinite; 0 < x; a : HFinite - Infinitesimal;  
         0 < a |] ==> x powhr a : HInfinite"
apply (auto intro!: starfun_ln_ge_zero starfun_ln_HInfinite HInfinite_HFinite_not_Infinitesimal_mult2 starfun_exp_HInfinite 
       simp add: order_less_imp_le HInfinite_gt_zero_gt_one powhr_as_starfun zero_le_mult_iff)
done

lemma hlog_hrabs_HInfinite_Infinitesimal:
     "[| x : HFinite - Infinitesimal; a : HInfinite; 0 < a |]  
      ==> hlog a (abs x) : Infinitesimal"
apply (frule HInfinite_gt_zero_gt_one)
apply (auto intro!: starfun_ln_HFinite_not_Infinitesimal
            HInfinite_inverse_Infinitesimal Infinitesimal_HFinite_mult2 
        simp add: starfun_ln_HInfinite not_Infinitesimal_not_zero 
          hlog_as_starfun hypreal_not_refl2 [THEN not_sym] divide_inverse)
done

lemma hlog_HInfinite_as_starfun:
     "[| a : HInfinite; 0 < a |] ==> hlog a x = ( *f* ln) x / ( *f* ln) a"
by (rule hlog_as_starfun, auto)

lemma hlog_one [simp]: "!!a. hlog a 1 = 0"
by (transfer, simp)

lemma hlog_eq_one [simp]: "!!a. [| 0 < a; a \<noteq> 1 |] ==> hlog a a = 1"
by (transfer, rule log_eq_one)

lemma hlog_inverse:
     "[| 0 < a; a \<noteq> 1; 0 < x |] ==> hlog a (inverse x) = - hlog a x"
apply (rule add_left_cancel [of "hlog a x", THEN iffD1])
apply (simp add: hlog_mult [symmetric])
done

lemma hlog_divide:
     "[| 0 < a; a \<noteq> 1; 0 < x; 0 < y|] ==> hlog a (x/y) = hlog a x - hlog a y"
by (simp add: hlog_mult hlog_inverse divide_inverse)

lemma hlog_less_cancel_iff [simp]:
     "!!a x y. [| 1 < a; 0 < x; 0 < y |] ==> (hlog a x < hlog a y) = (x < y)"
by (transfer, simp)

lemma hlog_le_cancel_iff [simp]:
     "[| 1 < a; 0 < x; 0 < y |] ==> (hlog a x \<le> hlog a y) = (x \<le> y)"
by (simp add: linorder_not_less [symmetric])


ML
{*
val powhr = thm "powhr";
val powhr_one_eq_one = thm "powhr_one_eq_one";
val powhr_mult = thm "powhr_mult";
val powhr_gt_zero = thm "powhr_gt_zero";
val powhr_not_zero = thm "powhr_not_zero";
val powhr_divide = thm "powhr_divide";
val powhr_add = thm "powhr_add";
val powhr_powhr = thm "powhr_powhr";
val powhr_powhr_swap = thm "powhr_powhr_swap";
val powhr_minus = thm "powhr_minus";
val powhr_minus_divide = thm "powhr_minus_divide";
val powhr_less_mono = thm "powhr_less_mono";
val powhr_less_cancel = thm "powhr_less_cancel";
val powhr_less_cancel_iff = thm "powhr_less_cancel_iff";
val powhr_le_cancel_iff = thm "powhr_le_cancel_iff";
val hlog = thm "hlog";
val hlog_starfun_ln = thm "hlog_starfun_ln";
val powhr_hlog_cancel = thm "powhr_hlog_cancel";
val hlog_powhr_cancel = thm "hlog_powhr_cancel";
val hlog_mult = thm "hlog_mult";
val hlog_as_starfun = thm "hlog_as_starfun";
val hlog_eq_div_starfun_ln_mult_hlog = thm "hlog_eq_div_starfun_ln_mult_hlog";
val powhr_as_starfun = thm "powhr_as_starfun";
val HInfinite_powhr = thm "HInfinite_powhr";
val hlog_hrabs_HInfinite_Infinitesimal = thm "hlog_hrabs_HInfinite_Infinitesimal";
val hlog_HInfinite_as_starfun = thm "hlog_HInfinite_as_starfun";
val hlog_one = thm "hlog_one";
val hlog_eq_one = thm "hlog_eq_one";
val hlog_inverse = thm "hlog_inverse";
val hlog_divide = thm "hlog_divide";
val hlog_less_cancel_iff = thm "hlog_less_cancel_iff";
val hlog_le_cancel_iff = thm "hlog_le_cancel_iff";
*}

end
