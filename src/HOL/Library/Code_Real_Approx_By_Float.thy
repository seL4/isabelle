(*  Title:      HOL/Library/Code_Real_Approx_By_Float.thy
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

definition Realfract :: \<open>real \<Rightarrow> real \<Rightarrow> real\<close>
  where \<open>Realfract p q = p / q\<close>

code_datatype Realfract

context
begin

qualified definition real_of_int :: \<open>int \<Rightarrow> real\<close>
  where [code_abbrev]: \<open>real_of_int = of_int\<close>

qualified definition real_of_integer :: "integer \<Rightarrow> real"
  where [code_abbrev]: "real_of_integer = of_int \<circ> int_of_integer"

lemma [code]: "real_of_int = real_of_integer \<circ> integer_of_int"
  by (simp add: fun_eq_iff real_of_integer_def real_of_int_def)

qualified definition exp_real :: \<open>real \<Rightarrow> real\<close>
  where [code_abbrev, code del]: \<open>exp_real = exp\<close>

qualified definition sin_real :: \<open>real \<Rightarrow> real\<close>
  where [code_abbrev, code del]: \<open>sin_real = sin\<close>

qualified definition cos_real :: \<open>real \<Rightarrow> real\<close>
  where [code_abbrev, code del]: \<open>cos_real = cos\<close>

end

definition Quotreal :: \<open>int \<Rightarrow> int \<Rightarrow> real\<close>
  where \<open>Quotreal p q = Realfract (of_int p) (of_int q)\<close>

lemma [code]: "Ratreal r = case_prod Quotreal (quotient_of r)"
  by (cases r) (simp add: Realfract_def Quotreal_def quotient_of_Fract of_rat_rat)

lemma [code]: \<open>inverse r = 1 / r\<close> for r :: real
  by (fact inverse_eq_divide)

lemma [code_unfold del]: "numeral k \<equiv> real_of_rat (numeral k)"
  by simp

lemma [code_unfold del]: "- numeral k \<equiv> real_of_rat (- numeral k)"
  by simp

declare [[code drop: \<open>HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool\<close>
  \<open>plus :: real \<Rightarrow> real \<Rightarrow> real\<close>
  \<open>uminus :: real \<Rightarrow> real\<close>
  \<open>minus :: real \<Rightarrow> real \<Rightarrow> real\<close>
  \<open>times :: real \<Rightarrow> real \<Rightarrow> real\<close>
  \<open>divide :: real \<Rightarrow> real \<Rightarrow> real\<close>
  \<open>(<) :: real \<Rightarrow> real \<Rightarrow> bool\<close>
  \<open>(\<le>) :: real \<Rightarrow> real \<Rightarrow> bool\<close>
  sqrt \<open>ln :: real \<Rightarrow> real\<close> pi
  arcsin arccos arctan]]

code_reserved SML Real

code_printing
  type_constructor real \<rightharpoonup>
    (SML) "real"
    and (OCaml) "float"

code_printing
  constant Realfract \<rightharpoonup> (SML) "_/ '// _"

code_printing
  constant "0 :: real" \<rightharpoonup>
    (SML) "0.0"
    and (OCaml) "0.0"

code_printing
  constant "1 :: real" \<rightharpoonup>
    (SML) "1.0"
    and (OCaml) "1.0"

code_printing
  constant "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Real.== ((_), (_))"
    and (OCaml) "Pervasives.(=)"

code_printing
  constant "Orderings.less_eq :: real \<Rightarrow> real \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Real.<= ((_), (_))"
    and (OCaml) "Pervasives.(<=)"

code_printing
  constant "Orderings.less :: real \<Rightarrow> real \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Real.< ((_), (_))"
    and (OCaml) "Pervasives.(<)"

code_printing
  constant "(+) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.+ ((_), (_))"
    and (OCaml) "Pervasives.( +. )"

code_printing
  constant "(*) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.* ((_), (_))"
    and (OCaml) "Pervasives.( *. )"

code_printing
  constant "(-) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.- ((_), (_))"
    and (OCaml) "Pervasives.( -. )"

code_printing
  constant "uminus :: real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.~"
    and (OCaml) "Pervasives.( ~-. )"

code_printing
  constant "(/) :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.'/ ((_), (_))"
    and (OCaml) "Pervasives.( '/. )"

code_printing
  constant "sqrt :: real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Math.sqrt"
    and (OCaml) "Pervasives.sqrt"

code_printing
  constant Code_Real_Approx_By_Float.exp_real \<rightharpoonup>
    (SML) "Math.exp"
    and (OCaml) "Pervasives.exp"

code_printing
  constant ln \<rightharpoonup>
    (SML) "Math.ln"
    and (OCaml) "Pervasives.ln"

code_printing
  constant Code_Real_Approx_By_Float.cos_real \<rightharpoonup>
    (SML) "Math.cos"
    and (OCaml) "Pervasives.cos"

code_printing
  constant Code_Real_Approx_By_Float.sin_real \<rightharpoonup>
    (SML) "Math.sin"
    and (OCaml) "Pervasives.sin"

code_printing
  constant pi \<rightharpoonup>
    (SML) "Math.pi"
    and (OCaml) "Pervasives.pi"

code_printing
  constant arctan \<rightharpoonup>
    (SML) "Math.atan"
    and (OCaml) "Pervasives.atan"

code_printing
  constant arccos \<rightharpoonup>
    (SML) "Math.scos"
    and (OCaml) "Pervasives.acos"

code_printing
  constant arcsin \<rightharpoonup>
    (SML) "Math.asin"
    and (OCaml) "Pervasives.asin"

code_printing
  constant Code_Real_Approx_By_Float.real_of_integer \<rightharpoonup>
    (SML) "Real.fromInt"
    and (OCaml) "Pervasives.float/ (Big'_int.to'_int (_))"

notepad
begin
  have "cos (pi/2) = 0" by (rule cos_pi_half)
  moreover have "cos (pi/2) \<noteq> 0" by eval
  ultimately have False by blast
end

end
