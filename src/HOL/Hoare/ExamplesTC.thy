(* Title:      Examples using Hoare Logic for Total Correctness
   Author:     Walter Guttmann
*)

section \<open>Examples using Hoare Logic for Total Correctness\<close>

theory ExamplesTC
  imports Hoare_Logic
begin

text \<open>
This theory demonstrates a few simple partial- and total-correctness proofs.
The first example is taken from HOL/Hoare/Examples.thy written by N. Galm.
We have added the invariant \<open>m \<le> a\<close>.
\<close>

lemma multiply_by_add: "VARS m s a b
  {a=A \<and> b=B}
  m := 0; s := 0;
  WHILE m\<noteq>a
  INV {s=m*b \<and> a=A \<and> b=B \<and> m\<le>a}
  DO s := s+b; m := m+(1::nat) OD
  {s = A*B}"
  by vcg_simp

text \<open>
Here is the total-correctness proof for the same program.
It needs the additional invariant \<open>m \<le> a\<close>.
\<close>
ML \<open>\<^const_syntax>\<open>HOL.eq\<close>\<close>
lemma multiply_by_add_tc: "VARS m s a b
  [a=A \<and> b=B]
  m := 0; s := 0;
  WHILE m\<noteq>a
  INV {s=m*b \<and> a=A \<and> b=B \<and> m\<le>a}
  VAR {a-m}
  DO s := s+b; m := m+(1::nat) OD
  [s = A*B]"
  apply vcg_tc_simp
  by auto

text \<open>
Next, we prove partial correctness of a program that computes powers.
\<close>

lemma power: "VARS (p::int) i
  { True }
  p := 1;
  i := 0;
  WHILE i < n
    INV { p = x^i \<and> i \<le> n }
     DO p := p * x;
        i := i + 1
     OD
  { p = x^n }"
  apply vcg_simp
  by auto

text \<open>
Here is its total-correctness proof.
\<close>

lemma power_tc: "VARS (p::int) i
  [ True ]
  p := 1;
  i := 0;
  WHILE i < n
    INV { p = x^i \<and> i \<le> n }
    VAR { n - i }
     DO p := p * x;
        i := i + 1
     OD
  [ p = x^n ]"
  apply vcg_tc
  by auto

text \<open>
The last example is again taken from HOL/Hoare/Examples.thy.
We have modified it to integers so it requires precondition \<open>0 \<le> x\<close>.
\<close>

lemma sqrt_tc: "VARS r
  [0 \<le> (x::int)]
  r := 0;
  WHILE (r+1)*(r+1) <= x
  INV {r*r \<le> x}
  VAR { nat (x-r)}
  DO r := r+1 OD
  [r*r \<le> x \<and> x < (r+1)*(r+1)]"
  apply vcg_tc_simp
  by (smt (verit) div_pos_pos_trivial mult_less_0_iff nonzero_mult_div_cancel_left)

text \<open>
A total-correctness proof allows us to extract a function for further use.
For every input satisfying the precondition the function returns an output satisfying the postcondition.
\<close>

lemma sqrt_exists:
  "0 \<le> (x::int) \<Longrightarrow> \<exists>r' . r'*r' \<le> x \<and> x < (r'+1)*(r'+1)"
  using tc_extract_function sqrt_tc by blast

definition "sqrt (x::int) \<equiv> (SOME r' . r'*r' \<le> x \<and> x < (r'+1)*(r'+1))"

lemma sqrt_function:
  assumes "0 \<le> (x::int)"
    and "r' = sqrt x"
  shows "r'*r' \<le> x \<and> x < (r'+1)*(r'+1)"
proof -
  let ?P = "\<lambda>r' . r'*r' \<le> x \<and> x < (r'+1)*(r'+1)"
  have "?P (SOME z . ?P z)"
    by (metis (mono_tags, lifting) assms(1) sqrt_exists some_eq_imp)
  thus ?thesis
    using assms(2) sqrt_def by auto
qed

text \<open>Nested loops!\<close>

lemma "VARS (i::nat) j
  [ True ]
  WHILE 0 < i
    INV { True }
    VAR { z = i }
     DO i := i - 1; j := i;
        WHILE 0 < j
        INV { z = i+1 }
        VAR { j }
        DO j := j - 1 OD
     OD
  [ i \<le> 0 ]"
  apply vcg_tc
  by auto

end
