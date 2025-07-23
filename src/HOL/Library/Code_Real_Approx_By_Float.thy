(*  Title:      HOL/Library/Code_Real_Approx_By_Float.thy
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Florian Haftmann
    Author:     Johannes Hölzl
    Author:     Tobias Nipkow
*)

theory Code_Real_Approx_By_Float
imports Complex_Main Code_Target_Int
begin

text\<open>
  \<^bold>\<open>WARNING!\<close> This theory implements mathematical reals by machine reals
  (floats). This is inconsistent. See the proof of False at the end of the
  theory, where an equality on mathematical reals is (incorrectly) disproved
  by mapping it to machine reals.

  The \<^theory_text>\<open>value\<close> command cannot display real results yet.

  The only legitimate use of this theory is as a tool for code generation
  purposes.
\<close>

context
begin

qualified definition real_of_integer :: "integer \<Rightarrow> real"
  where [code_abbrev]: "real_of_integer = of_int \<circ> int_of_integer"

end

code_datatype Code_Real_Approx_By_Float.real_of_integer \<open>(/) :: real \<Rightarrow> real \<Rightarrow> real\<close>

lemma [code_unfold del]: "numeral k \<equiv> real_of_rat (numeral k)"
  by simp

lemma [code_unfold del]: "- numeral k \<equiv> real_of_rat (- numeral k)"
  by simp

context
begin

qualified definition real_of_int :: \<open>int \<Rightarrow> real\<close>
  where [code_abbrev]: \<open>real_of_int = of_int\<close>

lemma [code]: "real_of_int = Code_Real_Approx_By_Float.real_of_integer \<circ> integer_of_int"
  by (simp add: fun_eq_iff Code_Real_Approx_By_Float.real_of_integer_def real_of_int_def)

qualified definition exp_real :: \<open>real \<Rightarrow> real\<close>
  where [code_abbrev, code del]: \<open>exp_real = exp\<close>

qualified definition sin_real :: \<open>real \<Rightarrow> real\<close>
  where [code_abbrev, code del]: \<open>sin_real = sin\<close>

qualified definition cos_real :: \<open>real \<Rightarrow> real\<close>
  where [code_abbrev, code del]: \<open>cos_real = cos\<close>

qualified definition tan_real :: \<open>real \<Rightarrow> real\<close>
  where [code_abbrev, code del]: \<open>tan_real = tan\<close>

end

lemma [code]: \<open>r - s = r + (- s)\<close> for r s :: real
  by (fact diff_conv_add_uminus)

lemma [code]: \<open>inverse r = 1 / r\<close> for r :: real
  by (fact inverse_eq_divide)

lemma [code]: \<open>Ratreal r = (let (p, q) = quotient_of r in real_of_int p / real_of_int q)\<close>
  by (cases r) (simp add: quotient_of_Fract of_rat_rat)

declare [[code drop:
  \<open>HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool\<close>
  \<open>(\<le>) :: real \<Rightarrow> real \<Rightarrow> bool\<close>
  \<open>(<) :: real \<Rightarrow> real \<Rightarrow> bool\<close>
  \<open>(+) :: real \<Rightarrow> real \<Rightarrow> real\<close>
  \<open>uminus :: real \<Rightarrow> real\<close>
  \<open>(*) :: real \<Rightarrow> real \<Rightarrow> real\<close>
  sqrt
  \<open>ln :: real \<Rightarrow> real\<close>
  pi
  arcsin
  arccos
  arctan]]

code_reserved (SML) Real

code_printing
  type_constructor real \<rightharpoonup>
    (SML) "real"
    and (OCaml) "float"
    and (Haskell) "Prelude.Double" (*Double precision*)
| constant "0 :: real" \<rightharpoonup>
    (SML) "0.0"
    and (OCaml) "0.0"
    and (Haskell) "0.0"
| constant "1 :: real" \<rightharpoonup>
    (SML) "1.0"
    and (OCaml) "1.0"
    and (Haskell) "1.0"
| constant "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Real.== ((_), (_))"
    and (OCaml) "Pervasives.(=)"
    and (Haskell) infix 4 "=="
| class_instance real :: "HOL.equal" => (Haskell) - (*This is necessary. See the tutorial on code generation, page 29*)
| constant "(\<le>) :: real \<Rightarrow> real \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Real.<= ((_), (_))"
    and (OCaml) "Pervasives.(<=)"
    and (Haskell) infix 4 "<="
| constant "(<) :: real \<Rightarrow> real \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Real.< ((_), (_))"
    and (OCaml) "Pervasives.(<)"
    and (Haskell) infix 4 "<"
| constant "(+) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.+ ((_), (_))"
    and (OCaml) "Pervasives.( +. )"
    and (Haskell) infixl 6 "+"
| constant "(*) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.* ((_), (_))"
    and (Haskell) infixl 7 "*"
| constant "uminus :: real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.~"
    and (OCaml) "Pervasives.( ~-. )"
    and (Haskell) "negate"
| constant "(-) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.- ((_), (_))"
    and (OCaml) "Pervasives.( -. )"
    and (Haskell) infixl 6 "-"
| constant "(/) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.'/ ((_), (_))"
    and (OCaml) "Pervasives.( '/. )"
    and (Haskell) infixl 7 "/"
| constant "sqrt :: real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Math.sqrt"
    and (OCaml) "Pervasives.sqrt"
    and (Haskell) "Prelude.sqrt" 
| constant Code_Real_Approx_By_Float.exp_real \<rightharpoonup>
    (SML) "Math.exp"
    and (OCaml) "Pervasives.exp"
    and (Haskell) "Prelude.exp"
| constant ln \<rightharpoonup>
    (SML) "Math.ln"
    and (OCaml) "Pervasives.ln"
    and (Haskell) "Prelude.log"
| constant Code_Real_Approx_By_Float.sin_real \<rightharpoonup>
    (SML) "Math.sin"
    and (OCaml) "Pervasives.sin"
    and (Haskell) "Prelude.sin"
| constant Code_Real_Approx_By_Float.cos_real \<rightharpoonup>
    (SML) "Math.cos"
    and (OCaml) "Pervasives.cos"
    and (Haskell) "Prelude.cos"
| constant Code_Real_Approx_By_Float.tan_real \<rightharpoonup>
    (SML) "Math.tan"
    and (OCaml) "Pervasives.tan"
    and (Haskell) "Prelude.tan"
| constant pi \<rightharpoonup>
    (SML) "Math.pi"
    (*missing in OCaml*)
    and (Haskell) "Prelude.pi"
| constant arcsin \<rightharpoonup>
    (SML) "Math.asin"
    and (OCaml) "Pervasives.asin"
    and (Haskell) "Prelude.asin"
| constant arccos \<rightharpoonup>
    (SML) "Math.scos"
    and (OCaml) "Pervasives.acos"
    and (Haskell) "Prelude.acos"
| constant arctan \<rightharpoonup>
    (SML) "Math.atan"
    and (OCaml) "Pervasives.atan"
    and (Haskell) "Prelude.atan"
| constant Code_Real_Approx_By_Float.real_of_integer \<rightharpoonup>
    (SML) "Real.fromInt"
    and (OCaml) "Pervasives.float/ (Big'_int.to'_int (_))"
    and (Haskell) "Prelude.fromIntegral (_)"

notepad
begin
  have "cos (pi/2) = 0" by (rule cos_pi_half)
  moreover have "cos (pi/2) \<noteq> 0" by eval
  ultimately have False by blast
end

end
