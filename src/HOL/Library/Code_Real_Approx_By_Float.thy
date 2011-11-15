(* Authors: Florian Haftmann, Johannes Hölzl, Tobias Nipkow *)

theory Code_Real_Approx_By_Float
imports Complex_Main "~~/src/HOL/Library/Code_Integer"
begin

text{* \textbf{WARNING} This theory implements mathematical reals by machine
reals (floats). This is inconsistent. See the proof of False at the end of
the theory, where an equality on mathematical reals is (incorrectly)
disproved by mapping it to machine reals.

The value command cannot display real results yet.

The only legitimate use of this theory is as a tool for code generation
purposes. *}

code_type real
  (SML   "real")
  (OCaml "float")

code_const Ratreal
  (SML "error/ \"Bad constant: Ratreal\"")

code_const "0 :: real"
  (SML   "0.0")
  (OCaml "0.0")
declare zero_real_code[code_unfold del]

code_const "1 :: real"
  (SML   "1.0")
  (OCaml "1.0")
declare one_real_code[code_unfold del]

code_const "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool"
  (SML   "Real.== ((_), (_))")
  (OCaml "Pervasives.(=)")

code_const "Orderings.less_eq :: real \<Rightarrow> real \<Rightarrow> bool"
  (SML   "Real.<= ((_), (_))")
  (OCaml "Pervasives.(<=)")

code_const "Orderings.less :: real \<Rightarrow> real \<Rightarrow> bool"
  (SML   "Real.< ((_), (_))")
  (OCaml "Pervasives.(<)")

code_const "op + :: real \<Rightarrow> real \<Rightarrow> real"
  (SML   "Real.+ ((_), (_))")
  (OCaml "Pervasives.( +. )")

code_const "op * :: real \<Rightarrow> real \<Rightarrow> real"
  (SML   "Real.* ((_), (_))")
  (OCaml "Pervasives.( *. )")

code_const "op - :: real \<Rightarrow> real \<Rightarrow> real"
  (SML   "Real.- ((_), (_))")
  (OCaml "Pervasives.( -. )")

code_const "uminus :: real \<Rightarrow> real"
  (SML   "Real.~")
  (OCaml "Pervasives.( ~-. )")

code_const "op / :: real \<Rightarrow> real \<Rightarrow> real"
  (SML   "Real.'/ ((_), (_))")
  (OCaml "Pervasives.( '/. )")

code_const "HOL.equal :: real \<Rightarrow> real \<Rightarrow> bool"
  (SML   "Real.== ((_:real), (_))")

code_const "sqrt :: real \<Rightarrow> real"
  (SML   "Math.sqrt")
  (OCaml "Pervasives.sqrt")
declare sqrt_def[code del]

definition real_exp :: "real \<Rightarrow> real" where "real_exp = exp"

lemma exp_eq_real_exp[code_unfold]: "exp = real_exp"
  unfolding real_exp_def ..

code_const real_exp
  (SML   "Math.exp")
  (OCaml "Pervasives.exp")
declare real_exp_def[code del]
declare exp_def[code del]

hide_const (open) real_exp

code_const ln
  (SML   "Math.ln")
  (OCaml "Pervasives.ln")
declare ln_def[code del]

code_const cos
  (SML   "Math.cos")
  (OCaml "Pervasives.cos")
declare cos_def[code del]

code_const sin
  (SML   "Math.sin")
  (OCaml "Pervasives.sin")
declare sin_def[code del]

code_const pi
  (SML   "Math.pi")
  (OCaml "Pervasives.pi")
declare pi_def[code del]

code_const arctan
  (SML   "Math.atan")
  (OCaml "Pervasives.atan")
declare arctan_def[code del]

code_const arccos
  (SML   "Math.scos")
  (OCaml "Pervasives.acos")
declare arccos_def[code del]

code_const arcsin
  (SML   "Math.asin")
  (OCaml "Pervasives.asin")
declare arcsin_def[code del]

definition real_of_int :: "int \<Rightarrow> real" where
  "real_of_int \<equiv> of_int"

code_const real_of_int
  (SML "Real.fromInt")
  (OCaml "Pervasives.float (Big'_int.int'_of'_big'_int (_))")

lemma of_int_eq_real_of_int[code_unfold]: "of_int = real_of_int"
  unfolding real_of_int_def ..

hide_const (open) real_of_int

declare number_of_real_code [code_unfold del]

lemma "False"
proof-
  have "cos(pi/2) = 0" by(rule cos_pi_half)
  moreover have "cos(pi/2) \<noteq> 0" by eval
  ultimately show "False" by blast
qed

end
