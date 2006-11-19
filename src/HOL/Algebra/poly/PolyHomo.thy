(*
    Universal property and evaluation homomorphism of univariate polynomials
    $Id$
    Author: Clemens Ballarin, started 15 April 1997
*)

theory PolyHomo imports UnivPoly2 begin

definition
  EVAL2 :: "['a::ring => 'b, 'b, 'a up] => 'b::ring" where
  "EVAL2 phi a p = setsum (%i. phi (coeff p i) * a ^ i) {..deg p}"

definition
  EVAL :: "['a::ring, 'a up] => 'a" where
  "EVAL = EVAL2 (%x. x)"

lemma SUM_shrink_lemma:
  "!! f::(nat=>'a::ring).
     m <= n & (ALL i. m < i & i <= n --> f i = 0) -->
     setsum f {..m} = setsum f {..n}"
  apply (induct_tac n)
  (* Base case *)
   apply (simp (no_asm))
  (* Induction step *)
  apply (case_tac "m <= n")
   apply auto
  apply (subgoal_tac "m = Suc n")
   apply (simp (no_asm_simp))
  apply arith
  done

lemma SUM_shrink:
  "!! f::(nat=>'a::ring).
     [| m <= n; !!i. [| m < i; i <= n |] ==> f i = 0; P (setsum f {..n}) |]
   ==> P (setsum f {..m})"
  apply (cut_tac m = m and n = n and f = f in SUM_shrink_lemma)
  apply simp
  done

lemma SUM_extend:
  "!! f::(nat=>'a::ring).
     [| m <= n; !!i. [| m < i; i <= n |] ==> f i = 0; P (setsum f {..m}) |]
     ==> P (setsum f {..n})"
  apply (cut_tac m = m and n = n and f = f in SUM_shrink_lemma)
  apply simp
  done

lemma DiagSum_lemma:
  "!!f::nat=>'a::ring. j <= n + m -->
     setsum (%k. setsum (%i. f i * g (k - i)) {..k}) {..j} =
     setsum (%k. setsum (%i. f k * g i) {..j - k}) {..j}"
  apply (induct_tac j)
  (* Base case *)
   apply (simp (no_asm))
  (* Induction step *)
  apply (simp (no_asm) add: Suc_diff_le natsum_add)
  apply (simp (no_asm_simp))
  done

lemma DiagSum:
  "!!f::nat=>'a::ring.
     setsum (%k. setsum (%i. f i * g (k - i)) {..k}) {..n + m} =
     setsum (%k. setsum (%i. f k * g i) {..n + m - k}) {..n + m}"
  apply (rule DiagSum_lemma [THEN mp])
  apply (rule le_refl)
  done

lemma CauchySum:
  "!! f::nat=>'a::ring. [| bound n f; bound m g|] ==>
     setsum (%k. setsum (%i. f i * g (k-i)) {..k}) {..n + m} =
     setsum f {..n} * setsum g {..m}"
  apply (simp (no_asm) add: natsum_ldistr DiagSum)
  (* SUM_rdistr must be applied after SUM_ldistr ! *)
  apply (simp (no_asm) add: natsum_rdistr)
  apply (rule_tac m = n and n = "n + m" in SUM_extend)
  apply (rule le_add1)
   apply force
  apply (rule natsum_cong)
   apply (rule refl)
  apply (rule_tac m = m and n = "n +m - i" in SUM_shrink)
    apply (simp (no_asm_simp) add: le_add_diff)
   apply auto
  done

(* Evaluation homomorphism *)

lemma EVAL2_homo:
    "!! phi::('a::ring=>'b::ring). homo phi ==> homo (EVAL2 phi a)"
  apply (rule homoI)
    apply (unfold EVAL2_def)
  (* + commutes *)
  (* degree estimations:
    bound of all sums can be extended to max (deg aa) (deg b) *)
    apply (rule_tac m = "deg (aa + b) " and n = "max (deg aa) (deg b)" in SUM_shrink)
      apply (rule deg_add)
     apply (simp (no_asm_simp) del: coeff_add add: deg_aboveD)
    apply (rule_tac m = "deg aa" and n = "max (deg aa) (deg b)" in SUM_shrink)
     apply (rule le_maxI1)
    apply (simp (no_asm_simp) add: deg_aboveD)
   apply (rule_tac m = "deg b" and n = "max (deg aa) (deg b) " in SUM_shrink)
     apply (rule le_maxI2)
    apply (simp (no_asm_simp) add: deg_aboveD)
  (* actual homom property + *)
    apply (simp (no_asm_simp) add: l_distr natsum_add)

  (* * commutes *)
   apply (rule_tac m = "deg (aa * b) " and n = "deg aa + deg b" in SUM_shrink)
    apply (rule deg_mult_ring)
    apply (simp (no_asm_simp) del: coeff_mult add: deg_aboveD)
   apply (rule trans)
    apply (rule_tac [2] CauchySum)
     prefer 2
     apply (simp add: boundI deg_aboveD)
    prefer 2
    apply (simp add: boundI deg_aboveD)
  (* getting a^i and a^(k-i) together is difficult, so we do it manually *)
  apply (rule_tac s = "setsum (%k. setsum (%i. phi (coeff aa i) * (phi (coeff b (k - i)) * (a ^ i * a ^ (k - i)))) {..k}) {..deg aa + deg b}" in trans)
    apply (simp (no_asm_simp) add: power_mult leD [THEN add_diff_inverse] natsum_ldistr)
   apply (simp (no_asm))
  (* 1 commutes *)
  apply (simp (no_asm_simp))
  done

lemma EVAL2_const:
    "!!phi::'a::ring=>'b::ring. EVAL2 phi a (monom b 0) = phi b"
  by (simp add: EVAL2_def)

lemma EVAL2_monom1:
    "!! phi::'a::domain=>'b::ring. homo phi ==> EVAL2 phi a (monom 1 1) = a"
  by (simp add: EVAL2_def)
  (* Must be able to distinguish 0 from 1, hence 'a::domain *)

lemma EVAL2_monom:
  "!! phi::'a::domain=>'b::ring. homo phi ==> EVAL2 phi a (monom 1 n) = a ^ n"
  apply (unfold EVAL2_def)
  apply (simp (no_asm))
  apply (case_tac n)
   apply auto
  done

lemma EVAL2_smult:
  "!!phi::'a::ring=>'b::ring.
     homo phi ==> EVAL2 phi a (b *s p) = phi b * EVAL2 phi a p"
  by (simp (no_asm_simp) add: monom_mult_is_smult [symmetric] EVAL2_homo EVAL2_const)

lemma monom_decomp: "monom (a::'a::ring) n = monom a 0 * monom 1 n"
  apply (simp (no_asm) add: monom_mult_is_smult)
  apply (rule up_eqI)
  apply (simp (no_asm))
  done

lemma EVAL2_monom_n:
  "!! phi::'a::domain=>'b::ring.
     homo phi ==> EVAL2 phi a (monom b n) = phi b * a ^ n"
  apply (subst monom_decomp)
  apply (simp (no_asm_simp) add: EVAL2_homo EVAL2_const EVAL2_monom)
  done

lemma EVAL_homo: "!!a::'a::ring. homo (EVAL a)"
  by (simp add: EVAL_def EVAL2_homo)

lemma EVAL_const: "!!a::'a::ring. EVAL a (monom b 0) = b"
  by (simp add: EVAL_def EVAL2_const)

lemma EVAL_monom: "!!a::'a::domain. EVAL a (monom 1 n) = a ^ n"
  by (simp add: EVAL_def EVAL2_monom)

lemma EVAL_smult: "!!a::'a::ring. EVAL a (b *s p) = b * EVAL a p"
  by (simp add: EVAL_def EVAL2_smult)

lemma EVAL_monom_n: "!!a::'a::domain. EVAL a (monom b n) = b * a ^ n"
  by (simp add: EVAL_def EVAL2_monom_n)


(* Examples *)

lemma "EVAL (x::'a::domain) (a*X^2 + b*X^1 + c*X^0) = a * x ^ 2 + b * x ^ 1 + c"
  by (simp del: power_Suc add: EVAL_homo EVAL_monom EVAL_monom_n)

lemma
  "EVAL (y::'a::domain)
    (EVAL (monom x 0) (monom 1 1 + monom (a*X^2 + b*X^1 + c*X^0) 0)) =
   x ^ 1 + (a * y ^ 2 + b * y ^ 1 + c)"
  by (simp del: power_Suc add: EVAL_homo EVAL_monom EVAL_monom_n EVAL_const)

end
