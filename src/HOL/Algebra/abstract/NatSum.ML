(*
    Sums with naturals as index domain
    $Id$
    Author: Clemens Ballarin, started 12 December 1996
*)

section "Basic Properties";

Goal "setsum f {..0::nat} = (f 0::'a::ring)";
by (Asm_simp_tac 1);
qed "SUM_0";

Goal "setsum f {..Suc n} = (f (Suc n) + setsum f {..n}::'a::ring)";
by (simp_tac (simpset() addsimps [atMost_Suc]) 1);
qed "SUM_Suc";

Addsimps [SUM_0, SUM_Suc];

Goal
  "setsum f {..Suc n} = (setsum (%i. f (Suc i)) {..n} + f 0::'a::ring)";
by (induct_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (asm_full_simp_tac (simpset() addsimps [a_assoc]) 1);
qed "SUM_Suc2";

(* Congruence rules *)

Goal "ALL j'::nat. j=j' --> (ALL i. i<=j' --> f i = (f' i :: 'a :: ring)) \
\     --> setsum f {..j} = setsum f' {..j'}";
by (induct_tac "j" 1);
by Auto_tac;  
bind_thm ("SUM_cong", (impI RS allI) RSN (2, result() RS spec RS mp RS mp));
Addcongs [SUM_cong];

(* Results needed for the development of polynomials *)

section "Ring Properties";

Goal "setsum (%i. 0) {..n::nat} = (0::'a::ring)";
by (induct_tac "n" 1);
by (Simp_tac 1);
by (Asm_simp_tac 1);
qed "SUM_zero";

Addsimps [SUM_zero];

Goal
  "!!f::nat=>'a::ring. \
\  setsum (%i. f i + g i) {..n::nat} = setsum f {..n} + setsum g {..n}";
by (induct_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (asm_simp_tac (simpset() addsimps a_ac) 1);
qed "SUM_add";

Goal
  "!!a::'a::ring. setsum f {..n::nat} * a = setsum (%i. f i * a) {..n}";
by (induct_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (asm_simp_tac (simpset() addsimps [l_distr]) 1);
qed "SUM_ldistr";

Goal
  "!!a::'a::ring. a * setsum f {..n::nat} = setsum (%i. a * f i) {..n}";
by (induct_tac "n" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (asm_simp_tac (simpset() addsimps [r_distr]) 1);
qed "SUM_rdistr";

section "Results for the Construction of Polynomials";

Goal
  "!!a::nat=>'a::ring. k <= n --> \
\  setsum (%j. setsum (%i. a i * b (j-i)) {..j} * c (n-j)) {..k} = \
\  setsum (%j. a j * setsum  (%i. b i * c (n-j-i)) {..k-j}) {..k}";
by (induct_tac "k" 1);
(* Base case *)
by (simp_tac (simpset() addsimps [m_assoc]) 1);
(* Induction step *)
by (rtac impI 1);
by (etac impE 1);
by (arith_tac 1);
by (asm_simp_tac
    (simpset() addsimps a_ac@
                        [Suc_diff_le, l_distr, r_distr, m_assoc, SUM_add]) 1);
by (asm_simp_tac (simpset() addsimps a_ac@ [SUM_ldistr, m_assoc]) 1);
qed_spec_mp "poly_assoc_lemma1";

Goal
  "!!a::nat=>'a::ring. \
\  setsum (%j. setsum (%i. a i * b (j-i)) {..j} * c (n-j)) {..n} = \
\  setsum (%j. a j * setsum (%i. b i * c (n-(j+i))) {..n-j}) {..n}";
by (asm_simp_tac (simpset() addsimps [poly_assoc_lemma1]) 1);
qed "poly_assoc_lemma";

Goal
  "!! a::nat=>'a::ring. j <= n --> \
\    setsum (%i. a i * b (n-i)) {..j} = \
\    setsum (%i. a (n-i-(n-j)) * b (i+(n-j))) {..j}";
by (Simp_tac 1); 
by (induct_tac "j" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (stac SUM_Suc2 1);
by (asm_simp_tac (simpset() addsimps [a_comm]) 1);
qed "poly_comm_lemma1";

Goal
 "!!a::nat=>'a::ring. \
\   setsum (%i. a i * b (n-i)) {..n} = \
\   setsum (%i. a (n-i) * b i) {..n}";
by (cut_inst_tac [("j", "n"), ("n", "n")] poly_comm_lemma1 1);
by (Asm_full_simp_tac 1);
qed "poly_comm_lemma";

section "Changing the Range of Summation";

Goal
  "!! f::(nat=>'a::ring). \
\   setsum (%i. if i = x then f i else 0) {..n} = (if x <= n then f x else 0)";
by (induct_tac "n" 1);
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
  "!! f::(nat=>'a::ring). \
\    (ALL i. i < m --> f i = 0) --> \
\      setsum (%i. f (i+m)) {..d} = setsum f {..m+d}";
by (induct_tac "d" 1);
(* Base case *)
by (induct_tac "m" 1);
by (Simp_tac 1);
by (Force_tac 1);
(* Induction step *)
by (asm_simp_tac (simpset() addsimps add_ac) 1);
val SUM_shrink_below_lemma = result();

Goal
  "!! f::(nat=>'a::ring). \
\    [| m <= n; !!i. i < m ==> f i = 0; P (setsum (%i. f (i+m)) {..n-m}) |] \
\    ==> P (setsum f {..n})";
by (asm_full_simp_tac 
    (simpset() addsimps [SUM_shrink_below_lemma, add_diff_inverse, leD]) 1);
qed "SUM_extend_below";

section "Result for the Univeral Property of Polynomials";

Goal
  "!!f::nat=>'a::ring. j <= n + m --> \
\    setsum (%k. setsum (%i. f i * g (k - i)) {..k}) {..j} = \
\    setsum (%k. setsum (%i. f k * g i) {..j - k}) {..j}";
by (induct_tac "j" 1);
(* Base case *)
by (Simp_tac 1);
(* Induction step *)
by (simp_tac (simpset() addsimps [Suc_diff_le, SUM_add]) 1);
by (asm_simp_tac (simpset() addsimps a_ac) 1);
val DiagSum_lemma = result();

Goal
  "!!f::nat=>'a::ring. \
\    setsum (%k. setsum (%i. f i * g (k - i)) {..k}) {..n + m} = \
\    setsum (%k. setsum (%i. f k * g i) {..n + m - k}) {..n + m}";
by (rtac (DiagSum_lemma RS mp) 1);
by (rtac le_refl 1);
qed "DiagSum";




