(*  Title       : HLog.thy
    Author      : Jacques D. Fleuriot
    Copyright   : 2000,2001 University of Edinburgh
*)

header{*Logarithms: Non-Standard Version*}

theory HLog = Log + HTranscendental: 


(* should be in NSA.ML *)
lemma epsilon_ge_zero [simp]: "0 \<le> epsilon"
by (simp add: epsilon_def hypreal_zero_num hypreal_le)

lemma hpfinite_witness: "epsilon : {x. 0 \<le> x & x : HFinite}"
by auto


constdefs

    powhr  :: "[hypreal,hypreal] => hypreal"     (infixr "powhr" 80)
    "x powhr a == ( *f* exp) (a * ( *f* ln) x)"
  
    hlog :: "[hypreal,hypreal] => hypreal"
    "hlog a x == Abs_hypreal(\<Union>A \<in> Rep_hypreal(a).\<Union>X \<in> Rep_hypreal(x).
			     hyprel `` {%n. log (A n) (X n)})"


lemma powhr: 
    "(Abs_hypreal(hyprel `` {X})) powhr (Abs_hypreal(hyprel `` {Y})) =  
     Abs_hypreal(hyprel `` {%n.  (X n) powr (Y n)})"
by (simp add: powhr_def starfun hypreal_mult powr_def)

lemma powhr_one_eq_one [simp]: "1 powhr a = 1"
apply (cases a)
apply (simp add: powhr hypreal_one_num)
done

lemma powhr_mult:
     "[| 0 < x; 0 < y |] ==> (x * y) powhr a = (x powhr a) * (y powhr a)"
apply (cases x, cases y, cases a)
apply (simp add: powhr hypreal_zero_num hypreal_mult hypreal_less, ultra)
apply (simp add: powr_mult) 
done

lemma powhr_gt_zero [simp]: "0 < x powhr a"
apply (cases a, cases x)
apply (simp add: hypreal_zero_def powhr hypreal_less hypreal_zero_num)
done

lemma powhr_not_zero [simp]: "x powhr a \<noteq> 0"
by (rule powhr_gt_zero [THEN hypreal_not_refl2, THEN not_sym])

lemma hypreal_divide: 
     "(Abs_hypreal(hyprel `` {X}))/(Abs_hypreal(hyprel `` {Y})) =  
      (Abs_hypreal(hyprel `` {%n. (X n)/(Y n)}))"
by (simp add: divide_inverse hypreal_zero_num hypreal_inverse hypreal_mult) 

lemma powhr_divide:
     "[| 0 < x; 0 < y |] ==> (x / y) powhr a = (x powhr a)/(y powhr a)"
apply (cases x, cases y, cases a)
apply (simp add: powhr hypreal_divide hypreal_zero_num hypreal_less, ultra)
apply (simp add: powr_divide)
done

lemma powhr_add: "x powhr (a + b) = (x powhr a) * (x powhr b)"
apply (cases x, cases b, cases a)
apply (simp add: powhr hypreal_add hypreal_mult powr_add)
done

lemma powhr_powhr: "(x powhr a) powhr b = x powhr (a * b)"
apply (cases x, cases b, cases a)
apply (simp add: powhr hypreal_mult powr_powr)
done

lemma powhr_powhr_swap: "(x powhr a) powhr b = (x powhr b) powhr a"
apply (cases x, cases b, cases a)
apply (simp add: powhr powr_powr_swap)
done

lemma powhr_minus: "x powhr (-a) = inverse (x powhr a)"
apply (cases x, cases a)
apply (simp add: powhr hypreal_minus hypreal_inverse hypreal_less powr_minus)
done

lemma powhr_minus_divide: "x powhr (-a) = 1/(x powhr a)"
by (simp add: divide_inverse powhr_minus)

lemma powhr_less_mono: "[| a < b; 1 < x |] ==> x powhr a < x powhr b"
apply (cases x, cases a, cases b)
apply (simp add: powhr hypreal_one_num hypreal_less, ultra)
done

lemma powhr_less_cancel: "[| x powhr a < x powhr b; 1 < x |] ==> a < b"
apply (cases x, cases a, cases b)
apply (simp add: powhr hypreal_one_num hypreal_less, ultra)
done

lemma powhr_less_cancel_iff [simp]:
     "1 < x ==> (x powhr a < x powhr b) = (a < b)"
by (blast intro: powhr_less_cancel powhr_less_mono)

lemma powhr_le_cancel_iff [simp]:
     "1 < x ==> (x powhr a \<le> x powhr b) = (a \<le> b)"
by (simp add: linorder_not_less [symmetric])

lemma hlog: 
     "hlog (Abs_hypreal(hyprel `` {X})) (Abs_hypreal(hyprel `` {Y})) =  
      Abs_hypreal(hyprel `` {%n. log (X n) (Y n)})"
apply (simp add: hlog_def)
apply (rule arg_cong [where f=Abs_hypreal], auto, ultra)
done

lemma hlog_starfun_ln: "( *f* ln) x = hlog (( *f* exp) 1) x"
apply (cases x)
apply (simp add: starfun hlog log_ln hypreal_one_num)
done

lemma powhr_hlog_cancel [simp]:
     "[| 0 < a; a \<noteq> 1; 0 < x |] ==> a powhr (hlog a x) = x"
apply (cases x, cases a)
apply (simp add: hlog powhr hypreal_zero_num hypreal_less hypreal_one_num, ultra)
done

lemma hlog_powhr_cancel [simp]:
     "[| 0 < a; a \<noteq> 1 |] ==> hlog a (a powhr y) = y"
apply (cases y, cases a)
apply (simp add: hlog powhr hypreal_zero_num hypreal_less hypreal_one_num, ultra)
apply (auto intro: log_powr_cancel) 
done

lemma hlog_mult:
     "[| 0 < a; a \<noteq> 1; 0 < x; 0 < y  |]  
      ==> hlog a (x * y) = hlog a x + hlog a y"
apply (cases x, cases y, cases a)
apply (simp add: hlog powhr hypreal_zero_num hypreal_one_num hypreal_less hypreal_add hypreal_mult, ultra)
apply (simp add: log_mult)
done

lemma hlog_as_starfun:
     "[| 0 < a; a \<noteq> 1 |] ==> hlog a x = ( *f* ln) x / ( *f* ln) a"
apply (cases x, cases a)
apply (simp add: hlog starfun hypreal_zero_num hypreal_one_num hypreal_divide log_def)
done

lemma hlog_eq_div_starfun_ln_mult_hlog:
     "[| 0 < a; a \<noteq> 1; 0 < b; b \<noteq> 1; 0 < x |]  
      ==> hlog a x = (( *f* ln) b/( *f*ln) a) * hlog b x"
apply (cases x, cases a, cases b)
apply (simp add: hlog starfun hypreal_zero_num hypreal_one_num hypreal_less hypreal_divide hypreal_mult, ultra)
apply (auto dest: log_eq_div_ln_mult_log) 
done

lemma powhr_as_starfun: "x powhr a = ( *f* exp) (a * ( *f* ln) x)"
apply (cases a, cases x)
apply (simp add: powhr starfun hypreal_mult powr_def)
done

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

lemma hlog_one [simp]: "hlog a 1 = 0"
apply (cases a)
apply (simp add: hypreal_one_num hypreal_zero_num hlog)
done

lemma hlog_eq_one [simp]: "[| 0 < a; a \<noteq> 1 |] ==> hlog a a = 1"
apply (cases a)
apply (simp add: hypreal_one_num hypreal_zero_num hlog hypreal_less, ultra)
apply (auto intro: log_eq_one) 
done

lemma hlog_inverse:
     "[| 0 < a; a \<noteq> 1; 0 < x |] ==> hlog a (inverse x) = - hlog a x"
apply (rule add_left_cancel [of "hlog a x", THEN iffD1])
apply (simp add: hlog_mult [symmetric])
done

lemma hlog_divide:
     "[| 0 < a; a \<noteq> 1; 0 < x; 0 < y|] ==> hlog a (x/y) = hlog a x - hlog a y"
by (simp add: hlog_mult hlog_inverse divide_inverse)

lemma hlog_less_cancel_iff [simp]:
     "[| 1 < a; 0 < x; 0 < y |] ==> (hlog a x < hlog a y) = (x < y)"
apply (cases a, cases x, cases y)
apply (auto simp add: hlog hypreal_less hypreal_zero_num hypreal_one_num, ultra+)
done

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
val hypreal_divide = thm "hypreal_divide";
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
