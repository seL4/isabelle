(* Authors: Florian Haftmann, Johannes Hölzl, Tobias Nipkow *)

theory Code_Real_Approx_By_Float
imports Complex_Main Code_Target_Int
begin

text{* \textbf{WARNING} This theory implements mathematical reals by machine
reals (floats). This is inconsistent. See the proof of False at the end of
the theory, where an equality on mathematical reals is (incorrectly)
disproved by mapping it to machine reals.

The value command cannot display real results yet.

The only legitimate use of this theory is as a tool for code generation
purposes. *}

code_printing
  type_constructor real \<rightharpoonup>
    (SML) "real"
    and (OCaml) "float"

code_printing
  constant Ratreal \<rightharpoonup>
    (SML) "error/ \"Bad constant: Ratreal\""

code_printing
  constant "0 :: real" \<rightharpoonup>
    (SML) "0.0"
    and (OCaml) "0.0"
declare zero_real_code[code_unfold del]

code_printing
  constant "1 :: real" \<rightharpoonup>
    (SML) "1.0"
    and (OCaml) "1.0"
declare one_real_code[code_unfold del]

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
  constant "op + :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.+ ((_), (_))"
    and (OCaml) "Pervasives.( +. )"

code_printing
  constant "op * :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.* ((_), (_))"
    and (OCaml) "Pervasives.( *. )"

code_printing
  constant "op - :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.- ((_), (_))"
    and (OCaml) "Pervasives.( -. )"

code_printing
  constant "uminus :: real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.~"
    and (OCaml) "Pervasives.( ~-. )"

code_printing
  constant "op / :: real \<Rightarrow> real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Real.'/ ((_), (_))"
    and (OCaml) "Pervasives.( '/. )"

code_printing
  constant "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool" \<rightharpoonup>
    (SML) "Real.== ((_:real), (_))"

code_printing
  constant "sqrt :: real \<Rightarrow> real" \<rightharpoonup>
    (SML) "Math.sqrt"
    and (OCaml) "Pervasives.sqrt"
declare sqrt_def[code del]

definition real_exp :: "real \<Rightarrow> real" where "real_exp = exp"

lemma exp_eq_real_exp[code_unfold]: "exp = real_exp"
  unfolding real_exp_def ..

code_printing
  constant real_exp \<rightharpoonup>
    (SML) "Math.exp"
    and (OCaml) "Pervasives.exp"
declare real_exp_def[code del]
declare exp_def[code del]

hide_const (open) real_exp

code_printing
  constant ln \<rightharpoonup>
    (SML) "Math.ln"
    and (OCaml) "Pervasives.ln"
declare ln_def[code del]

code_printing
  constant cos \<rightharpoonup>
    (SML) "Math.cos"
    and (OCaml) "Pervasives.cos"
declare cos_def[code del]

code_printing
  constant sin \<rightharpoonup>
    (SML) "Math.sin"
    and (OCaml) "Pervasives.sin"
declare sin_def[code del]

code_printing
  constant pi \<rightharpoonup>
    (SML) "Math.pi"
    and (OCaml) "Pervasives.pi"
declare pi_def[code del]

code_printing
  constant arctan \<rightharpoonup>
    (SML) "Math.atan"
    and (OCaml) "Pervasives.atan"
declare arctan_def[code del]

code_printing
  constant arccos \<rightharpoonup>
    (SML) "Math.scos"
    and (OCaml) "Pervasives.acos"
declare arccos_def[code del]

code_printing
  constant arcsin \<rightharpoonup>
    (SML) "Math.asin"
    and (OCaml) "Pervasives.asin"
declare arcsin_def[code del]

definition real_of_integer :: "integer \<Rightarrow> real" where
  "real_of_integer = of_int \<circ> int_of_integer"

code_printing
  constant real_of_integer \<rightharpoonup>
    (SML) "Real.fromInt"
    and (OCaml) "Pervasives.float (Big'_int.int'_of'_big'_int (_))"

definition real_of_int :: "int \<Rightarrow> real" where
  [code_abbrev]: "real_of_int = of_int"

lemma [code]:
  "real_of_int = real_of_integer \<circ> integer_of_int"
  by (simp add: fun_eq_iff real_of_integer_def real_of_int_def)

lemma [code_unfold del]:
  "0 \<equiv> (of_rat 0 :: real)"
  by simp

lemma [code_unfold del]:
  "1 \<equiv> (of_rat 1 :: real)"
  by simp

lemma [code_unfold del]:
  "numeral k \<equiv> (of_rat (numeral k) :: real)"
  by simp

lemma [code_unfold del]:
  "- numeral k \<equiv> (of_rat (- numeral k) :: real)"
  by simp

hide_const (open) real_of_int

code_printing
  constant Ratreal \<rightharpoonup> (SML)

definition Realfract :: "int => int => real"
where
  "Realfract p q = of_int p / of_int q"

code_datatype Realfract

code_printing
  constant Realfract \<rightharpoonup> (SML) "Real.fromInt _/ '// Real.fromInt _"

lemma [code]:
  "Ratreal r = split Realfract (quotient_of r)"
  by (cases r) (simp add: Realfract_def quotient_of_Fract of_rat_rat)

lemma [code, code del]:
  "(HOL.equal :: real=>real=>bool) = (HOL.equal :: real => real => bool) "
  ..

lemma [code, code del]:
  "(plus :: real => real => real) = plus"
  ..

lemma [code, code del]:
  "(uminus :: real => real) = uminus"
  ..

lemma [code, code del]:
  "(minus :: real => real => real) = minus"
  ..

lemma [code, code del]:
  "(times :: real => real => real) = times"
  ..

lemma [code, code del]:
  "(divide :: real => real => real) = divide"
  ..

lemma [code]:
  fixes r :: real
  shows "inverse r = 1 / r"
  by (fact inverse_eq_divide)

notepad
begin
  have "cos (pi/2) = 0" by (rule cos_pi_half)
  moreover have "cos (pi/2) \<noteq> 0" by eval
  ultimately have "False" by blast
end

end

