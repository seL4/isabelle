(*
    Universal property and evaluation homomorphism of univariate polynomials
    $Id$
    Author: Clemens Ballarin, started 16 April 1997
*)

(* Summation result for tactic-style proofs *)

val natsum_add = thm "natsum_add";
val natsum_ldistr = thm "natsum_ldistr";
val natsum_rdistr = thm "natsum_rdistr";

Goal
  "!! f::(nat=>'a::ring). \
\    m <= n & (ALL i. m < i & i <= n --> f i = 0) --> \
\    setsum f {..m} = setsum f {..n}";
by (induct_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (case_tac "m <= n" 1);
by Auto_tac;
by (subgoal_tac "m = Suc n" 1);
by (Asm_simp_tac 1);
by (fast_arith_tac 1);
val SUM_shrink_lemma = result();

Goal
  "!! f::(nat=>'a::ring). \
\    [| m <= n; !!i. [| m < i; i <= n |] ==> f i = 0; P (setsum f {..n}) |] \
\  ==> P (setsum f {..m})";
by (cut_inst_tac [("m", "m"), ("n", "n"), ("f", "f")] SUM_shrink_lemma 1);
by (Asm_full_simp_tac 1);
qed "SUM_shrink";

Goal
  "!! f::(nat=>'a::ring). \
\    [| m <= n; !!i. [| m < i; i <= n |] ==> f i = 0; P (setsum f {..m}) |] \
\    ==> P (setsum f {..n})";
by (cut_inst_tac [("m", "m"), ("n", "n"), ("f", "f")] SUM_shrink_lemma 1);
by (Asm_full_simp_tac 1);
qed "SUM_extend";

Goal
  "!!f::nat=>'a::ring. j <= n + m --> \
\    setsum (%k. setsum (%i. f i * g (k - i)) {..k}) {..j} = \
\    setsum (%k. setsum (%i. f k * g i) {..j - k}) {..j}";
by (induct_tac "j" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (simp_tac (simpset() addsimps [Suc_diff_le, natsum_add]) 1);
(*
by (asm_simp_tac (simpset() addsimps a_ac) 1);
*)
by (Asm_simp_tac 1);
val DiagSum_lemma = result();

Goal
  "!!f::nat=>'a::ring. \
\    setsum (%k. setsum (%i. f i * g (k - i)) {..k}) {..n + m} = \
\    setsum (%k. setsum (%i. f k * g i) {..n + m - k}) {..n + m}";
by (rtac (DiagSum_lemma RS mp) 1);
by (rtac le_refl 1);
qed "DiagSum";

Goal
  "!! f::nat=>'a::ring. [| bound n f; bound m g|] ==> \
\    setsum (%k. setsum (%i. f i * g (k-i)) {..k}) {..n + m} = \
\    setsum f {..n} * setsum g {..m}";
by (simp_tac (simpset() addsimps [natsum_ldistr, DiagSum]) 1);
(* SUM_rdistr must be applied after SUM_ldistr ! *)
by (simp_tac (simpset() addsimps [natsum_rdistr]) 1);
by (res_inst_tac [("m", "n"), ("n", "n+m")] SUM_extend 1);
by (rtac le_add1 1);
by (Force_tac 1);
by (rtac (thm "natsum_cong") 1);
by (rtac refl 1);
by (res_inst_tac [("m", "m"), ("n", "n+m-i")] SUM_shrink 1);
by (asm_simp_tac (simpset() addsimps [le_add_diff]) 1);
by Auto_tac;
qed "CauchySum";

(* Ring homomorphisms and polynomials *)
(*
Goal "homo (const::'a::ring=>'a up)";
by (auto_tac (claset() addSIs [homoI], simpset()));
qed "const_homo";

Delsimps [const_add, const_mult, const_one, const_zero];
Addsimps [const_homo];

Goal
  "!!f::'a::ring up=>'b::ring. homo f ==> f (a *s p) = f (const a) * f p";
by (asm_simp_tac (simpset() addsimps [const_mult_is_smult RS sym]) 1);
qed "homo_smult";

Addsimps [homo_smult];
*)

val deg_add = thm "deg_add";
val deg_mult_ring = thm "deg_mult_ring";
val deg_aboveD = thm "deg_aboveD";
val coeff_add = thm "coeff_add";
val coeff_mult = thm "coeff_mult";
val boundI = thm "boundI";
val monom_mult_is_smult = thm "monom_mult_is_smult";

(* Evaluation homomorphism *)

Goal
  "!! phi::('a::ring=>'b::ring). homo phi ==> homo (EVAL2 phi a)";
by (rtac homoI 1);
by (rewtac EVAL2_def);
(* + commutes *)
(* degree estimations:
  bound of all sums can be extended to max (deg aa) (deg b) *)
by (res_inst_tac [("m", "deg (aa + b)"), ("n", "max (deg aa) (deg b)")]
  SUM_shrink 1);
by (rtac deg_add 1);
by (asm_simp_tac (simpset() delsimps [coeff_add] addsimps [deg_aboveD]) 1);
by (res_inst_tac [("m", "deg aa"), ("n", "max (deg aa) (deg b)")]
  SUM_shrink 1);
by (rtac le_maxI1 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD]) 1);
by (res_inst_tac [("m", "deg b"), ("n", "max (deg aa) (deg b)")]
  SUM_shrink 1);
by (rtac le_maxI2 1);
by (asm_simp_tac (simpset() addsimps [deg_aboveD]) 1);
(* actual homom property + *)
by (asm_simp_tac (simpset() addsimps [l_distr, natsum_add]) 1);

(* * commutes *)
by (res_inst_tac [("m", "deg (aa * b)"), ("n", "deg aa + deg b")]
  SUM_shrink 1);
by (rtac deg_mult_ring 1);
by (asm_simp_tac (simpset() delsimps [coeff_mult] addsimps [deg_aboveD]) 1);
by (rtac trans 1);
by (rtac CauchySum 2);
by (asm_simp_tac (simpset() addsimps [boundI, deg_aboveD]) 2);
by (asm_simp_tac (simpset() addsimps [boundI, deg_aboveD]) 2);
(* getting a^i and a^(k-i) together is difficult, so we do it manually *)
by (res_inst_tac [("s", 
"        setsum  \
\           (%k. setsum \
\                 (%i. phi (coeff aa i) * (phi (coeff b (k - i)) * \
\                      (a ^ i * a ^ (k - i)))) {..k}) \
\           {..deg aa + deg b}")] trans 1);
by (asm_simp_tac (simpset()
    addsimps [power_mult, leD RS add_diff_inverse, natsum_ldistr]) 1);
by (Simp_tac 1);
(* 1 commutes *)
by (Asm_simp_tac 1);
qed "EVAL2_homo";

Goalw [EVAL2_def]
  "!! phi::'a::ring=>'b::ring. EVAL2 phi a (monom b 0) = phi b";
by (Simp_tac 1);
qed "EVAL2_const";

Goalw [EVAL2_def]
  "!! phi::'a::domain=>'b::ring. homo phi ==> EVAL2 phi a (monom 1 1) = a";
(* Must be able to distinguish 0 from 1, hence 'a::domain *)
by (Asm_simp_tac 1);
qed "EVAL2_monom1";

Goalw [EVAL2_def]
  "!! phi::'a::domain=>'b::ring. homo phi ==> EVAL2 phi a (monom 1 n) = a ^ n";
by (Simp_tac 1);
by (case_tac "n" 1); 
by Auto_tac;
qed "EVAL2_monom";

Goal
  "!! phi::'a::ring=>'b::ring. \
\    homo phi ==> EVAL2 phi a (b *s p) = phi b * EVAL2 phi a p";
by (asm_simp_tac (simpset() 
    addsimps [monom_mult_is_smult RS sym, EVAL2_homo, EVAL2_const]) 1);
qed "EVAL2_smult";

val up_eqI = thm "up_eqI";

Goal "monom (a::'a::ring) n = monom a 0 * monom 1 n";
by (simp_tac (simpset() addsimps [monom_mult_is_smult]) 1);
by (rtac up_eqI 1);
by (Simp_tac 1);
qed "monom_decomp";

Goal
  "!! phi::'a::domain=>'b::ring. \
\    homo phi ==> EVAL2 phi a (monom b n) = phi b * a ^ n";
by (stac monom_decomp 1);
by (asm_simp_tac (simpset() 
    addsimps [EVAL2_homo, EVAL2_const, EVAL2_monom]) 1);
qed "EVAL2_monom_n";

Goalw [EVAL_def] "!! a::'a::ring. homo (EVAL a)";
by (asm_simp_tac (simpset() addsimps [EVAL2_homo]) 1);
qed "EVAL_homo";

Goalw [EVAL_def] "!! a::'a::ring. EVAL a (monom b 0) = b";
by (asm_simp_tac (simpset() addsimps [EVAL2_const]) 1);
qed "EVAL_const";

Goalw [EVAL_def] "!! a::'a::domain. EVAL a (monom 1 n) = a ^ n";
by (asm_simp_tac (simpset() addsimps [EVAL2_monom]) 1);
qed "EVAL_monom";

Goalw [EVAL_def] "!! a::'a::ring. EVAL a (b *s p) = b * EVAL a p";
by (asm_simp_tac (simpset() addsimps [EVAL2_smult]) 1);
qed "EVAL_smult";

Goalw [EVAL_def] "!! a::'a::domain. EVAL a (monom b n) = b * a ^ n";
by (asm_simp_tac (simpset() addsimps [EVAL2_monom_n]) 1);
qed "EVAL_monom_n";

(* Examples *)

Goal
  "EVAL (x::'a::domain) (a*X^2 + b*X^1 + c*X^0) = a * x ^ 2 + b * x ^ 1 + c";
by (asm_simp_tac (simpset() delsimps [power_Suc]
    addsimps [EVAL_homo, EVAL_monom, EVAL_monom_n]) 1);
result();

Goal
  "EVAL (y::'a::domain) \
\    (EVAL (monom x 0) (monom 1 1 + monom (a*X^2 + b*X^1 + c*X^0) 0)) = \
\  x ^ 1 + (a * y ^ 2 + b * y ^ 1 + c)";
by (asm_simp_tac (simpset() delsimps [power_Suc]
    addsimps [EVAL_homo, EVAL_monom, EVAL_monom_n, EVAL_const]) 1);
result();

