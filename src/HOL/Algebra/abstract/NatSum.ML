(*
    Sums with naturals as index domain
    $Id$
    Author: Clemens Ballarin, started 12 December 1996
*)

section "Basic Properties";

Goalw [SUM_def] "SUM 0 f = (f 0::'a::ring)";
by (Asm_simp_tac 1);
qed "SUM_0";

Goalw [SUM_def]
  "SUM (Suc n) f = (f (Suc n) + SUM n f::'a::ring)";
by (Simp_tac 1);
qed "SUM_Suc";

Addsimps [SUM_0, SUM_Suc];

Goal
  "SUM (Suc n) f = (SUM n (%i. f (Suc i)) + f 0::'a::ring)";
by (nat_ind_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (asm_full_simp_tac (simpset() addsimps [a_assoc]) 1);
qed "SUM_Suc2";

(* Congruence rules *)

val [p_equal, p_context] = goal NatSum.thy
  "[| m = n; !!i. i <= n ==> f i = g i |] ==> SUM m f = (SUM n g::'a::ring)";
by (simp_tac (simpset() addsimps [p_equal]) 1);
by (cut_inst_tac [("n", "n")] le_refl 1);
by (etac rev_mp 1);
by (res_inst_tac [("P", "%k. k <= n --> SUM k f = SUM k g")] nat_induct 1);
(* Base case *)
by (simp_tac (simpset() addsimps [p_context]) 1);
(* Induction step *)
by (rtac impI 1);
by (etac impE 1);
by (rtac Suc_leD 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps [p_context]) 1);
qed "SUM_cong";

Addcongs [SUM_cong];

(* Results needed for the development of polynomials *)

section "Ring Properties";

Goal "SUM n (%i. <0>) = (<0>::'a::ring)";
by (nat_ind_tac "n" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "SUM_zero";

Addsimps [SUM_zero];

Goal
  "!!f::nat=>'a::ring. SUM n (%i. f i + g i) = SUM n f + SUM n g";
by (nat_ind_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (asm_simp_tac (simpset() addsimps a_ac) 1);
qed "SUM_add";

Goal
  "!!a::'a::ring. SUM n f * a = SUM n (%i. f i * a)";
by (nat_ind_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (asm_simp_tac (simpset() addsimps [l_distr]) 1);
qed "SUM_ldistr";

Goal
  "!!a::'a::ring. a * SUM n f = SUM n (%i. a * f i)";
by (nat_ind_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (asm_simp_tac (simpset() addsimps [r_distr]) 1);
qed "SUM_rdistr";

section "Results for the Construction of Polynomials";

goal Main.thy (* could go to Arith *)
  "!!j::nat. [| m <= j; Suc j <= n |] ==> (n - m) - Suc (j - m) = n - Suc j";
by (asm_simp_tac (simpset() addsimps [Suc_diff_le RS sym]) 1);
by (asm_simp_tac (simpset() addsimps [diff_right_cancel, less_imp_le]) 1);
qed "Suc_diff_lemma";

Goal
  "!!a::nat=>'a::ring. k <= n --> \
\  SUM k (%j. SUM j (%i. a i * b (j-i)) * c (n-j)) = \
\  SUM k (%j. a j * SUM (k-j) (%i. b i * c (n-j-i)))";
by (nat_ind_tac "k" 1);
(* Base case *)
by (simp_tac (simpset() addsimps [m_assoc]) 1);
(* Induction step *)
by (rtac impI 1);
by (etac impE 1);
by (rtac Suc_leD 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps a_ac@[Suc_diff_le, l_distr, r_distr, m_assoc, SUM_add]) 1);
by (asm_simp_tac (simpset() addsimps a_ac@[Suc_diff_lemma, SUM_ldistr, m_assoc]) 1);
qed "poly_assoc_lemma1";

Goal
  "!!a::nat=>'a::ring. \
\  SUM n (%j. SUM j (%i. a i * b (j-i)) * c (n-j)) = \
\  SUM n (%j. a j * SUM (n-j) (%i. b i * c (n-j-i)))";
by (rtac (poly_assoc_lemma1 RS mp) 1);
by (rtac le_refl 1);
qed "poly_assoc_lemma";

goal Main.thy (* could go to Arith *)
  "!! n. Suc i <= n ==> Suc (a + (n - Suc i)) = a + (n - i)";
by (asm_simp_tac (simpset() delsimps [add_Suc] addsimps [add_Suc_right RS sym, Suc_diff_Suc]) 1);
qed "Suc_add_diff_Suc";

goal Main.thy (* could go to Arith *)
  "!! n. [| Suc j <= n; i <= j |] ==> \
\    n - Suc i - (n - Suc j) = n - i - (n - j)";
by (res_inst_tac [("m1", "n - Suc i"), ("n1", "n - Suc j")]
  (diff_Suc_Suc RS subst) 1);
by (subgoal_tac "Suc i <= n" 1);
by (asm_simp_tac (simpset() delsimps [diff_Suc_Suc] addsimps [Suc_diff_Suc]) 1);
by (fast_arith_tac 1);
qed "diff_lemma2";

Goal
  "!! a::nat=>'a::ring. j <= n --> \
\    SUM j (%i. a i * b (n-i)) = SUM j (%i. a (n-i-(n-j)) * b (i+(n-j)))";
by (nat_ind_tac "j" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (rtac impI 1);
by (etac impE 1);
by (rtac Suc_leD 1);
by (assume_tac 1);
by (stac SUM_Suc2 1);
by (stac SUM_Suc 1);
by (asm_simp_tac (simpset()
    addsimps [a_comm, Suc_add_diff_Suc, diff_diff_cancel, diff_lemma2]) 1);
qed "poly_comm_lemma1";

Goal
 "!!a::nat=>'a::ring. SUM n (%i. a i * b (n-i)) = SUM n (%i. a (n-i) * b i)";
by (cut_inst_tac [("j", "n"), ("n", "n")] poly_comm_lemma1 1);
by (Asm_full_simp_tac 1);
qed "poly_comm_lemma";

section "Changing the Range of Summation";

Goal
  "!! f::(nat=>'a::ring). \
\    SUM n (%i. if i = x then f i else <0>) = (if x <= n then f x else <0>)";
by (nat_ind_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (Asm_simp_tac 1);
by (Clarify_tac 1);
by (res_inst_tac [("f", "f")] arg_cong 1);
by (arith_tac 1);
qed "SUM_if_singleton";

Goal
  "!! f::(nat=>'a::ring). \
\    m <= n & (ALL i. m < i & i <= n --> f i = <0>) --> \
\    SUM m f = SUM n f";
by (nat_ind_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (case_tac "m <= n" 1);
by (rtac impI 1);
by (etac impE 1);
by (SELECT_GOAL Auto_tac 1);
by (etac conjE 1);
by (dres_inst_tac [("x", "Suc n")] spec 1);
by (asm_simp_tac (simpset() addsimps [less_Suc_eq_le]) 1);
(* case n < m, in fact m = Suc n *)
by (rtac impI 1);
by (etac conjE 1);
by (subgoal_tac "m = Suc n" 1);
by (Asm_simp_tac 1);
by (fast_arith_tac 1);
val SUM_shrink_lemma = result();

Goal
  "!! f::(nat=>'a::ring). \
\    [| m <= n; !!i. [| m < i; i <= n |] ==> f i = <0>; P (SUM n f) |] ==> \
\      P (SUM m f)";
by (cut_inst_tac [("m", "m"), ("n", "n"), ("f", "f")] SUM_shrink_lemma 1);
by (Asm_full_simp_tac 1);
qed "SUM_shrink";

Goal
  "!! f::(nat=>'a::ring). \
\    [| m <= n; !!i. [| m < i; i <= n |] ==> f i = <0>; P (SUM m f) |] ==> \
\      P (SUM n f)";
by (cut_inst_tac [("m", "m"), ("n", "n"), ("f", "f")] SUM_shrink_lemma 1);
by (Asm_full_simp_tac 1);
qed "SUM_extend";

Goal
  "!! f::(nat=>'a::ring). \
\    (ALL i. i < m --> f i = <0>) --> SUM d (%i. f (i+m)) = SUM (m+d) f";
by (nat_ind_tac "d" 1);
(* Base case *)
by (nat_ind_tac "m" 1);
by (Simp_tac 1);
by (rtac impI 1);
by (etac impE 1);
by (Asm_simp_tac 1);
by (subgoal_tac "SUM m f = <0>" 1);
by (Asm_simp_tac 1);
by (Asm_full_simp_tac 1);
(* Induction step *)
by (asm_simp_tac (simpset() addsimps add_ac) 1);
val SUM_shrink_below_lemma = result();

Goal
  "!! f::(nat=>'a::ring). \
\    [| m <= n; !!i. i < m ==> f i = <0>; P (SUM (n-m) (%i. f (i+m))) |] ==> \
\    P (SUM n f)";
by (asm_full_simp_tac (simpset() addsimps
  [SUM_shrink_below_lemma, add_diff_inverse, leD]) 1);
qed "SUM_extend_below";

section "Result for the Univeral Property of Polynomials";

Goal
  "!!f::nat=>'a::ring. j <= n + m --> \
\    SUM j (%k. SUM k (%i. f i * g (k - i))) = \
\    SUM j (%k. SUM (j - k) (%i. f k * g i))";
by (nat_ind_tac "j" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (simp_tac (simpset() addsimps [Suc_diff_le]) 1);
by (simp_tac (simpset() addsimps [SUM_add]) 1);
by (rtac impI 1);
by (etac impE 1);
by (dtac Suc_leD 1);
by (assume_tac 1);
by (asm_simp_tac (simpset() addsimps a_ac) 1);
val DiagSum_lemma = result();

Goal
  "!!f::nat=>'a::ring. \
\    SUM (n + m) (%k. SUM k (%i. f i * g (k - i))) = \
\    SUM (n + m) (%k. SUM (n + m - k) (%i. f k * g i))";
by (rtac (DiagSum_lemma RS mp) 1);
by (rtac le_refl 1);
qed "DiagSum";




