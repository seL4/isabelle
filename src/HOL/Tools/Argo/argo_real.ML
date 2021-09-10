(*  Title:      HOL/Tools/Argo/argo_real.ML
    Author:     Sascha Boehme

Extension of the Argo tactic for the reals.
*)

structure Argo_Real: sig end =
struct

(* translating input terms *)

fun trans_type _ \<^typ>\<open>Real.real\<close> tcx = SOME (Argo_Expr.Real, tcx)
  | trans_type _ _ _ = NONE

fun trans_term f (@{const Groups.uminus_class.uminus (real)} $ t) tcx =
      tcx |> f t |>> Argo_Expr.mk_neg |> SOME
  | trans_term f (@{const Groups.plus_class.plus (real)} $ t1 $ t2) tcx =
      tcx |> f t1 ||>> f t2 |>> uncurry Argo_Expr.mk_add2 |> SOME
  | trans_term f (@{const Groups.minus_class.minus (real)} $ t1 $ t2) tcx =
      tcx |> f t1 ||>> f t2 |>> uncurry Argo_Expr.mk_sub |> SOME
  | trans_term f (@{const Groups.times_class.times (real)} $ t1 $ t2) tcx =
      tcx |> f t1 ||>> f t2 |>> uncurry Argo_Expr.mk_mul |> SOME
  | trans_term f (@{const Rings.divide_class.divide (real)} $ t1 $ t2) tcx =
      tcx |> f t1 ||>> f t2 |>> uncurry Argo_Expr.mk_div |> SOME
  | trans_term f (@{const Orderings.ord_class.min (real)} $ t1 $ t2) tcx =
      tcx |> f t1 ||>> f t2 |>> uncurry Argo_Expr.mk_min |> SOME
  | trans_term f (@{const Orderings.ord_class.max (real)} $ t1 $ t2) tcx =
      tcx |> f t1 ||>> f t2 |>> uncurry Argo_Expr.mk_max |> SOME
  | trans_term f (@{const Groups.abs_class.abs (real)} $ t) tcx =
      tcx |> f t |>> Argo_Expr.mk_abs |> SOME
  | trans_term f (@{const Orderings.ord_class.less (real)} $ t1 $ t2) tcx =
      tcx |> f t1 ||>> f t2 |>> uncurry Argo_Expr.mk_lt |> SOME
  | trans_term f (@{const Orderings.ord_class.less_eq (real)} $ t1 $ t2) tcx =
      tcx |> f t1 ||>> f t2 |>> uncurry Argo_Expr.mk_le |> SOME
  | trans_term _ t tcx =
      (case try HOLogic.dest_number t of
        SOME (\<^typ>\<open>Real.real\<close>, n) => SOME (Argo_Expr.mk_num (Rat.of_int n), tcx)
      | _ => NONE)


(* reverse translation *)

fun mk_plus t1 t2 = @{const Groups.plus_class.plus (real)} $ t1 $ t2
fun mk_sum ts = uncurry (fold_rev mk_plus) (split_last ts)
fun mk_times t1 t2 = @{const Groups.times_class.times (real)} $ t1 $ t2
fun mk_divide t1 t2 = @{const Rings.divide_class.divide (real)} $ t1 $ t2
fun mk_le t1 t2 = @{const Orderings.ord_class.less_eq (real)} $ t1 $ t2
fun mk_lt t1 t2 = @{const Orderings.ord_class.less (real)} $ t1 $ t2

fun mk_real_num i = HOLogic.mk_number \<^typ>\<open>Real.real\<close> i

fun mk_number n =
  let val (p, q) = Rat.dest n
  in if q = 1 then mk_real_num p else mk_divide (mk_real_num p) (mk_real_num q) end

fun term_of _ (Argo_Expr.E (Argo_Expr.Num n, _)) = SOME (mk_number n)
  | term_of f (Argo_Expr.E (Argo_Expr.Neg, [e])) =
      SOME (@{const Groups.uminus_class.uminus (real)} $ f e)
  | term_of f (Argo_Expr.E (Argo_Expr.Add, es)) = SOME (mk_sum (map f es))
  | term_of f (Argo_Expr.E (Argo_Expr.Sub, [e1, e2])) =
      SOME (@{const Groups.minus_class.minus (real)} $ f e1 $ f e2)
  | term_of f (Argo_Expr.E (Argo_Expr.Mul, [e1, e2])) = SOME (mk_times (f e1) (f e2))
  | term_of f (Argo_Expr.E (Argo_Expr.Div, [e1, e2])) = SOME (mk_divide (f e1) (f e2))
  | term_of f (Argo_Expr.E (Argo_Expr.Min, [e1, e2])) =
      SOME (@{const Orderings.ord_class.min (real)} $ f e1 $ f e2)
  | term_of f (Argo_Expr.E (Argo_Expr.Max, [e1, e2])) =
      SOME (@{const Orderings.ord_class.max (real)} $ f e1 $ f e2)
  | term_of f (Argo_Expr.E (Argo_Expr.Abs, [e])) = SOME (@{const Groups.abs_class.abs (real)} $ f e)
  | term_of f (Argo_Expr.E (Argo_Expr.Le, [e1, e2])) = SOME (mk_le (f e1) (f e2))
  | term_of f (Argo_Expr.E (Argo_Expr.Lt, [e1, e2])) = SOME (mk_lt (f e1) (f e2))
  | term_of _ _ = NONE


(* proof replay for rewrite steps *)

fun mk_rewr thm = thm RS @{thm eq_reflection}

fun by_simp ctxt t = 
  let fun prove {context, ...} = HEADGOAL (Simplifier.simp_tac context)
  in Goal.prove ctxt [] [] (HOLogic.mk_Trueprop t) prove end

fun prove_num_pred ctxt n =
  by_simp ctxt (uncurry mk_lt (apply2 mk_number (if @0 < n then (@0, n) else (n, @0))))

fun simp_conv ctxt t = Conv.rewr_conv (mk_rewr (by_simp ctxt t))

fun nums_conv mk f ctxt n m =
  simp_conv ctxt (HOLogic.mk_eq (mk (mk_number n) (mk_number m), mk_number (f (n, m))))

val add_nums_conv = nums_conv mk_plus (op +)
val mul_nums_conv = nums_conv mk_times (op *)
val div_nums_conv = nums_conv mk_divide (op /)
fun inv_num_conv ctxt = nums_conv mk_divide (fn (_, n) => Rat.inv n) ctxt @1

fun cmp_nums_conv ctxt b ct =
  let val t = if b then \<^const>\<open>HOL.True\<close> else \<^const>\<open>HOL.False\<close>
  in simp_conv ctxt (HOLogic.mk_eq (Thm.term_of ct, t)) ct end

local

fun is_add2 (@{const Groups.plus_class.plus (real)} $ _ $ _) = true
  | is_add2 _ = false

fun is_add3 (@{const Groups.plus_class.plus (real)} $ _ $ t) = is_add2 t
  | is_add3 _ = false

val flatten_thm = mk_rewr @{lemma "(a::real) + b + c = a + (b + c)" by simp}
  
fun flatten_conv ct =
  if is_add2 (Thm.term_of ct) then Argo_Tactic.flatten_conv flatten_conv flatten_thm ct
  else Conv.all_conv ct

val swap_conv = Conv.rewrs_conv (map mk_rewr @{lemma 
  "(a::real) + (b + c) = b + (a + c)"
  "(a::real) + b = b + a"
  by simp_all})

val assoc_conv = Conv.rewr_conv (mk_rewr @{lemma "(a::real) + (b + c) = (a + b) + c" by simp})

val norm_monom_thm = mk_rewr @{lemma "1 * (a::real) = a" by simp}
fun norm_monom_conv n = if n = @1 then Conv.rewr_conv norm_monom_thm else Conv.all_conv

val add2_thms = map mk_rewr @{lemma
  "n * (a::real) + m * a = (n + m) * a"
  "n * (a::real) + a = (n + 1) * a"
  "(a::real) + m * a = (1 + m) * a"
  "(a::real) + a = (1 + 1) * a"
  by algebra+}

val add3_thms = map mk_rewr @{lemma
  "n * (a::real) + (m * a + b) = (n + m) * a + b"
  "n * (a::real) + (a + b) = (n + 1) * a + b"
  "(a::real) + (m * a + b) = (1 + m) * a + b"
  "(a::real) + (a + b) = (1 + 1) * a + b"
  by algebra+}

fun choose_conv cv2 cv3 ct = if is_add3 (Thm.term_of ct) then cv3 ct else cv2 ct

fun join_num_conv ctxt n m =
  let val conv = add_nums_conv ctxt n m
  in choose_conv conv (assoc_conv then_conv Conv.arg1_conv conv) end

fun join_monom_conv ctxt n m =
  let
    val conv = Conv.arg1_conv (add_nums_conv ctxt n m) then_conv norm_monom_conv (n + m)
    fun seq_conv thms cv = Conv.rewrs_conv thms then_conv cv
  in choose_conv (seq_conv add2_thms conv) (seq_conv add3_thms (Conv.arg1_conv conv)) end

fun join_conv NONE = join_num_conv
  | join_conv (SOME _) = join_monom_conv

fun bubble_down_conv _ _ [] ct = Conv.no_conv ct
  | bubble_down_conv _ _ [_] ct = Conv.all_conv ct
  | bubble_down_conv ctxt i ((m1 as (n1, i1)) :: (m2 as (n2, i2)) :: ms) ct =
      if i1 = i then
        if i2 = i then
          (join_conv i ctxt n1 n2 then_conv bubble_down_conv ctxt i ((n1 + n2, i) :: ms)) ct
        else (swap_conv then_conv Conv.arg_conv (bubble_down_conv ctxt i (m1 :: ms))) ct
      else Conv.arg_conv (bubble_down_conv ctxt i (m2 :: ms)) ct

fun drop_var i ms = filter_out (fn (_, i') => i' = i) ms

fun permute_conv _ [] [] ct = Conv.all_conv ct
  | permute_conv ctxt (ms as ((_, i) :: _)) [] ct =
      (bubble_down_conv ctxt i ms then_conv permute_conv ctxt (drop_var i ms) []) ct
  | permute_conv ctxt ms1 ms2 ct =
      let val (ms2', (_, i)) = split_last ms2
      in (bubble_down_conv ctxt i ms1 then_conv permute_conv ctxt (drop_var i ms1) ms2') ct end

val no_monom_conv = Conv.rewr_conv (mk_rewr @{lemma "0 * (a::real) = 0" by simp})

val norm_sum_conv = Conv.rewrs_conv (map mk_rewr @{lemma
  "0 * (a::real) + b = b"
  "(a::real) + 0 * b = a"
  "0 + (a::real) = a"
  "(a::real) + 0 = a"
  by simp_all})

fun drop0_conv ct =
  if is_add2 (Thm.term_of ct) then
    ((norm_sum_conv then_conv drop0_conv) else_conv Conv.arg_conv drop0_conv) ct
  else Conv.try_conv no_monom_conv ct

fun full_add_conv ctxt ms1 ms2 =
  if eq_list (op =) (ms1, ms2) then flatten_conv
  else flatten_conv then_conv permute_conv ctxt ms1 ms2 then_conv drop0_conv

in

fun add_conv ctxt (ms1, ms2 as [(n, NONE)]) =
      if n = @0 then full_add_conv ctxt ms1 [] else full_add_conv ctxt ms1 ms2
  | add_conv ctxt (ms1, ms2) = full_add_conv ctxt ms1 ms2

end

val mul_suml_thm = mk_rewr @{lemma "((x::real) + y) * z = x * z + y * z" by (rule ring_distribs)}
val mul_sumr_thm = mk_rewr @{lemma "(x::real) * (y + z) = x * y + x * z" by (rule ring_distribs)}
fun mul_sum_conv thm ct =
  Conv.try_conv (Conv.rewr_conv thm then_conv Conv.binop_conv (mul_sum_conv thm)) ct

val div_sum_thm = mk_rewr @{lemma "((x::real) + y) / z = x / z + y / z"
  by (rule add_divide_distrib)}
fun div_sum_conv ct =
  Conv.try_conv (Conv.rewr_conv div_sum_thm then_conv Conv.binop_conv div_sum_conv) ct

fun var_of_add_cmp (_ $ _ $ (_ $ _ $ (_ $ _ $ Var v))) = v
  | var_of_add_cmp t = raise TERM ("var_of_add_cmp", [t])

fun add_cmp_conv ctxt n thm =
  let val v = var_of_add_cmp (Thm.prop_of thm) in
    Conv.rewr_conv
      (Thm.instantiate (TVars.empty, Vars.make [(v, Thm.cterm_of ctxt (mk_number n))]) thm)
  end

fun mul_cmp_conv ctxt n pos_thm neg_thm =
  let val thm = if @0 < n then pos_thm else neg_thm
  in Conv.rewr_conv (prove_num_pred ctxt n RS thm) end

val neg_thm = mk_rewr @{lemma "-(x::real) = -1 * x" by simp}
val sub_thm = mk_rewr @{lemma "(x::real) - y = x + -1 * y" by simp}
val mul_zero_thm = mk_rewr @{lemma "0 * (x::real) = 0" by (rule mult_zero_left)}
val mul_one_thm = mk_rewr @{lemma "1 * (x::real) = x" by (rule mult_1)}
val mul_comm_thm = mk_rewr @{lemma "(x::real) * y = y * x" by simp}
val mul_assocl_thm = mk_rewr @{lemma "((x::real) * y) * z = x * (y * z)" by simp}
val mul_assocr_thm = mk_rewr @{lemma "(x::real) * (y * z) = (x * y) * z" by simp}
val mul_divl_thm = mk_rewr @{lemma "((x::real) / y) * z = (x * z) / y" by simp}
val mul_divr_thm = mk_rewr @{lemma "(x::real) * (y / z) = (x * y) / z" by simp}
val div_zero_thm = mk_rewr @{lemma "0 / (x::real) = 0" by (rule div_0)}
val div_one_thm = mk_rewr @{lemma "(x::real) / 1 = x" by (rule div_by_1)}
val div_numl_thm = mk_rewr @{lemma "(x::real) / y = x * (1 / y)" by simp}
val div_numr_thm = mk_rewr @{lemma "(x::real) / y = (1 / y) * x" by simp}
val div_mull_thm = mk_rewr @{lemma "((x::real) * y) / z = x * (y / z)" by simp}
val div_mulr_thm = mk_rewr @{lemma "(x::real) / (y * z) = (1 / y) * (x / z)" by simp}
val div_divl_thm = mk_rewr @{lemma "((x::real) / y) / z = x / (y * z)" by simp}
val div_divr_thm = mk_rewr @{lemma "(x::real) / (y / z) = (x * z) / y" by simp}
val min_eq_thm = mk_rewr @{lemma "min (x::real) x = x" by (simp add: min_def)}
val min_lt_thm = mk_rewr @{lemma "min (x::real) y = (if x <= y then x else y)" by (rule min_def)}
val min_gt_thm = mk_rewr @{lemma "min (x::real) y = (if y <= x then y else x)"
  by (simp add: min_def)}
val max_eq_thm = mk_rewr @{lemma "max (x::real) x = x" by (simp add: max_def)}
val max_lt_thm = mk_rewr @{lemma "max (x::real) y = (if x <= y then y else x)" by (rule max_def)}
val max_gt_thm = mk_rewr @{lemma "max (x::real) y = (if y <= x then x else y)"
  by (simp add: max_def)}
val abs_thm = mk_rewr @{lemma "abs (x::real) = (if 0 <= x then x else -x)" by simp}
val sub_eq_thm = mk_rewr @{lemma "((x::real) = y) = (x - y = 0)" by simp}
val eq_le_thm = mk_rewr @{lemma "((x::real) = y) = ((x \<le> y) \<and> (y \<le> x))" by (rule order_eq_iff)}
val add_le_thm = mk_rewr @{lemma "((x::real) \<le> y) = (x + n \<le> y + n)" by simp}
val add_lt_thm = mk_rewr @{lemma "((x::real) < y) = (x + n < y + n)" by simp}
val sub_le_thm = mk_rewr @{lemma "((x::real) <= y) = (x - y <= 0)" by simp}
val sub_lt_thm = mk_rewr @{lemma "((x::real) < y) = (x - y < 0)" by simp}
val pos_mul_le_thm = mk_rewr @{lemma "0 < n ==> ((x::real) <= y) = (n * x <= n * y)" by simp}
val neg_mul_le_thm = mk_rewr @{lemma "n < 0 ==> ((x::real) <= y) = (n * y <= n * x)" by simp}
val pos_mul_lt_thm = mk_rewr @{lemma "0 < n ==> ((x::real) < y) = (n * x < n * y)" by simp}
val neg_mul_lt_thm = mk_rewr @{lemma "n < 0 ==> ((x::real) < y) = (n * y < n * x)" by simp}
val not_le_thm = mk_rewr @{lemma "(\<not>((x::real) \<le> y)) = (y < x)" by auto}
val not_lt_thm = mk_rewr @{lemma "(\<not>((x::real) < y)) = (y \<le> x)" by auto}

fun replay_rewr _ Argo_Proof.Rewr_Neg = Conv.rewr_conv neg_thm
  | replay_rewr ctxt (Argo_Proof.Rewr_Add ps) = add_conv ctxt ps
  | replay_rewr _ Argo_Proof.Rewr_Sub = Conv.rewr_conv sub_thm
  | replay_rewr _ Argo_Proof.Rewr_Mul_Zero = Conv.rewr_conv mul_zero_thm
  | replay_rewr _ Argo_Proof.Rewr_Mul_One = Conv.rewr_conv mul_one_thm
  | replay_rewr ctxt (Argo_Proof.Rewr_Mul_Nums (n, m)) = mul_nums_conv ctxt n m
  | replay_rewr _ Argo_Proof.Rewr_Mul_Comm = Conv.rewr_conv mul_comm_thm
  | replay_rewr _ (Argo_Proof.Rewr_Mul_Assoc Argo_Proof.Left) = Conv.rewr_conv mul_assocl_thm
  | replay_rewr _ (Argo_Proof.Rewr_Mul_Assoc Argo_Proof.Right) = Conv.rewr_conv mul_assocr_thm
  | replay_rewr _ (Argo_Proof.Rewr_Mul_Sum Argo_Proof.Left) = mul_sum_conv mul_suml_thm
  | replay_rewr _ (Argo_Proof.Rewr_Mul_Sum Argo_Proof.Right) = mul_sum_conv mul_sumr_thm
  | replay_rewr _ (Argo_Proof.Rewr_Mul_Div Argo_Proof.Left) = Conv.rewr_conv mul_divl_thm
  | replay_rewr _ (Argo_Proof.Rewr_Mul_Div Argo_Proof.Right) = Conv.rewr_conv mul_divr_thm
  | replay_rewr _ Argo_Proof.Rewr_Div_Zero = Conv.rewr_conv div_zero_thm
  | replay_rewr _ Argo_Proof.Rewr_Div_One = Conv.rewr_conv div_one_thm
  | replay_rewr ctxt (Argo_Proof.Rewr_Div_Nums (n, m)) = div_nums_conv ctxt n m
  | replay_rewr _ (Argo_Proof.Rewr_Div_Num (Argo_Proof.Left, _)) = Conv.rewr_conv div_numl_thm
  | replay_rewr ctxt (Argo_Proof.Rewr_Div_Num (Argo_Proof.Right, n)) =
      Conv.rewr_conv div_numr_thm then_conv Conv.arg1_conv (inv_num_conv ctxt n)
  | replay_rewr _ (Argo_Proof.Rewr_Div_Mul (Argo_Proof.Left, _)) = Conv.rewr_conv div_mull_thm
  | replay_rewr ctxt (Argo_Proof.Rewr_Div_Mul (Argo_Proof.Right, n)) =
      Conv.rewr_conv div_mulr_thm then_conv Conv.arg1_conv (inv_num_conv ctxt n)
  | replay_rewr _ (Argo_Proof.Rewr_Div_Div Argo_Proof.Left) = Conv.rewr_conv div_divl_thm
  | replay_rewr _ (Argo_Proof.Rewr_Div_Div Argo_Proof.Right) = Conv.rewr_conv div_divr_thm
  | replay_rewr _ Argo_Proof.Rewr_Div_Sum = div_sum_conv
  | replay_rewr _ Argo_Proof.Rewr_Min_Eq = Conv.rewr_conv min_eq_thm
  | replay_rewr _ Argo_Proof.Rewr_Min_Lt = Conv.rewr_conv min_lt_thm
  | replay_rewr _ Argo_Proof.Rewr_Min_Gt = Conv.rewr_conv min_gt_thm
  | replay_rewr _ Argo_Proof.Rewr_Max_Eq = Conv.rewr_conv max_eq_thm
  | replay_rewr _ Argo_Proof.Rewr_Max_Lt = Conv.rewr_conv max_lt_thm
  | replay_rewr _ Argo_Proof.Rewr_Max_Gt = Conv.rewr_conv max_gt_thm
  | replay_rewr _ Argo_Proof.Rewr_Abs = Conv.rewr_conv abs_thm
  | replay_rewr ctxt (Argo_Proof.Rewr_Eq_Nums b) = cmp_nums_conv ctxt b
  | replay_rewr _ Argo_Proof.Rewr_Eq_Sub = Conv.rewr_conv sub_eq_thm
  | replay_rewr _ Argo_Proof.Rewr_Eq_Le = Conv.rewr_conv eq_le_thm
  | replay_rewr ctxt (Argo_Proof.Rewr_Ineq_Nums (_, b)) = cmp_nums_conv ctxt b
  | replay_rewr ctxt (Argo_Proof.Rewr_Ineq_Add (Argo_Proof.Le, n)) =
      add_cmp_conv ctxt n add_le_thm
  | replay_rewr ctxt (Argo_Proof.Rewr_Ineq_Add (Argo_Proof.Lt, n)) =
      add_cmp_conv ctxt n add_lt_thm
  | replay_rewr _ (Argo_Proof.Rewr_Ineq_Sub Argo_Proof.Le) = Conv.rewr_conv sub_le_thm
  | replay_rewr _ (Argo_Proof.Rewr_Ineq_Sub Argo_Proof.Lt) = Conv.rewr_conv sub_lt_thm
  | replay_rewr ctxt (Argo_Proof.Rewr_Ineq_Mul (Argo_Proof.Le, n)) =
      mul_cmp_conv ctxt n pos_mul_le_thm neg_mul_le_thm
  | replay_rewr ctxt (Argo_Proof.Rewr_Ineq_Mul (Argo_Proof.Lt, n)) =
      mul_cmp_conv ctxt n pos_mul_lt_thm neg_mul_lt_thm
  | replay_rewr _ (Argo_Proof.Rewr_Not_Ineq Argo_Proof.Le) = Conv.rewr_conv not_le_thm
  | replay_rewr _ (Argo_Proof.Rewr_Not_Ineq Argo_Proof.Lt) = Conv.rewr_conv not_lt_thm
  | replay_rewr _ _ = Conv.no_conv


(* proof replay *)

val combine_thms = @{lemma
  "(a::real) < b ==> c < d ==> a + c < b + d"
  "(a::real) < b ==> c <= d ==> a + c < b + d"
  "(a::real) <= b ==> c < d ==> a + c < b + d"
  "(a::real) <= b ==> c <= d ==> a + c <= b + d"
  by auto}

fun combine thm1 thm2 = hd (Argo_Tactic.discharges thm2 (Argo_Tactic.discharges thm1 combine_thms))

fun replay _ _ Argo_Proof.Linear_Comb prems = SOME (uncurry (fold_rev combine) (split_last prems))
  | replay _ _ _ _ = NONE


(* real extension of the Argo solver *)

val _ = Theory.setup (Argo_Tactic.add_extension {
  trans_type = trans_type,
  trans_term = trans_term,
  term_of = term_of,
  replay_rewr = replay_rewr,
  replay = replay})

end
