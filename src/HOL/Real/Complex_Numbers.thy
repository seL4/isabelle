(*  Title:      HOL/Real/Complex_Numbers.thy
    ID:         $Id$
    Author:     Gertrud Bauer and Markus Wenzel, TU München
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Complex numbers *}

theory Complex_Numbers = RealPow + Ring_and_Field:

subsection {* Representation of complex numbers *}

datatype complex = Complex real real

consts Re :: "complex => real"
primrec "Re (Complex x y) = x"

consts Im :: "complex => real"
primrec "Im (Complex x y) = y"

lemma complex_surj [simp]: "Complex (Re z) (Im z) = z"
  by (induct z) simp

instance complex :: zero ..
instance complex :: one ..
instance complex :: number ..
instance complex :: plus ..
instance complex :: minus ..
instance complex :: times ..
instance complex :: inverse ..

defs (overloaded)
  zero_complex_def: "0 == Complex 0 0"
  one_complex_def: "1 == Complex 1 0"
  number_of_complex_def: "number_of b == Complex (number_of b) 0"
  add_complex_def: "z + w == Complex (Re z + Re w) (Im z + Im w)"
  minus_complex_def: "z - w == Complex (Re z - Re w) (Im z - Im w)"
  uminus_complex_def: "- z == Complex (- Re z) (- Im z)"
  mult_complex_def: "z * w ==
    Complex (Re z * Re w - Im z * Im w) (Re z * Im w + Im z * Re w)"
  inverse_complex_def: "(z::complex) \<noteq> 0 ==> inverse z ==
    Complex (Re z / ((Re z)\<twosuperior> + (Im z)\<twosuperior>)) (- Im z / ((Re z)\<twosuperior> + (Im z)\<twosuperior>))"
  divide_complex_def: "(w::complex) \<noteq> 0 ==> z / (w::complex) == z * inverse w"

lemma complex_equality [intro?]: "Re z = Re w ==> Im z = Im w ==> z = w"
  by (induct z, induct w) simp

lemma Re_zero [simp]: "Re 0 = 0"
  and Im_zero [simp]: "Im 0 = 0"
  by (simp_all add: zero_complex_def)

lemma Re_one [simp]: "Re 1 = 1"
  and Im_one [simp]: "Im 1 = 0"
  by (simp_all add: one_complex_def)

lemma Re_add [simp]: "Re (z + w) = Re z + Re w"
  by (simp add: add_complex_def)

lemma Im_add [simp]: "Im (z + w) = Im z + Im w"
  by (simp add: add_complex_def)

lemma Re_diff [simp]: "Re (z - w) = Re z - Re w"
  by (simp add: minus_complex_def)

lemma Im_diff [simp]: "Im (z - w) = Im z - Im w"
  by (simp add: minus_complex_def)

lemma Re_uminus [simp]: "Re (-z) = - Re z"
  by (simp add: uminus_complex_def)

lemma Im_uminus [simp]: "Im (-z) = - Im z"
  by (simp add: uminus_complex_def)

lemma Re_mult [simp]: "Re (z * w) = Re z * Re w - Im z * Im w"
  by (simp add: mult_complex_def)

lemma Im_mult [simp]: "Im (z * w) = Re z * Im w + Im z * Re w"
  by (simp add: mult_complex_def)

lemma zero_complex_iff: "(z = 0) = (Re z = 0 \<and> Im z = 0)"
  and one_complex_iff: "(z = 1) = (Re z = 1 \<and> Im z = 0)"
  by (auto simp add: complex_equality)


subsection {* The field of complex numbers *}

instance complex :: field
proof
  fix z u v w :: complex
  show "(u + v) + w = u + (v + w)"
    by (simp add: add_complex_def)
  show "z + w = w + z"
    by (simp add: add_complex_def)
  show "0 + z = z"
    by (simp add: add_complex_def zero_complex_def)
  show "-z + z = 0"
    by (simp add: complex_equality minus_complex_def)
  show "z - w = z + -w"
    by (simp add: add_complex_def minus_complex_def uminus_complex_def)
  show "(u * v) * w = u * (v * w)"
    by (simp add: mult_complex_def mult_ac ring_distrib real_diff_def)  (* FIXME *)
  show "z * w = w * z"
    by (simp add: mult_complex_def)
  show "1 * z = z"
    by (simp add: one_complex_def mult_complex_def)
  show "0 \<noteq> (1::complex)"  --{*for some reason it has to be early*}
    by (simp add: zero_complex_def one_complex_def) 
  show "(u + v) * w = u * w + v * w"
    by (simp add: add_complex_def mult_complex_def ring_distrib)
  show "z+u = z+v ==> u=v"
    proof -
      assume eq: "z+u = z+v" 
      hence "(-z + z) + u = (-z + z) + v" by (simp add: eq add_complex_def)
      thus "u = v" by (simp add: add_complex_def)
    qed
  assume neq: "w \<noteq> 0"
  thus "z / w = z * inverse w"
    by (simp add: divide_complex_def)
  show "inverse w * w = 1"
  proof
    have neq': "Re w * Re w + Im w * Im w \<noteq> 0"
    proof -
      have ge: "0 \<le> Re w * Re w"  "0 \<le> Im w * Im w" by simp_all
      from neq have "Re w \<noteq> 0 \<or> Im w \<noteq> 0" by (simp add: zero_complex_iff)
      hence "Re w * Re w \<noteq> 0 \<or> Im w * Im w \<noteq> 0" by simp
      thus ?thesis by rule (insert ge, arith+)
    qed
    with neq show "Re (inverse w * w) = Re 1"
      by (simp add: inverse_complex_def real_power_two add_divide_distrib [symmetric])
    from neq show "Im (inverse w * w) = Im 1"
      by (simp add: inverse_complex_def real_power_two
        mult_ac add_divide_distrib [symmetric])
  qed
qed


subsection {* Basic operations *}

instance complex :: power ..
primrec (power_complex)
  "z ^ 0 = 1"
  "z ^ Suc n = (z::complex) * (z ^ n)"

lemma complex_power_two: "z\<twosuperior> = z * (z::complex)"
  by (simp add: complex_equality numeral_2_eq_2)


constdefs
  im_unit :: complex    ("\<i>")
  "\<i> == Complex 0 1"

lemma im_unit_square: "\<i>\<twosuperior> = -1"
  by (simp add: im_unit_def complex_power_two mult_complex_def number_of_complex_def)


constdefs
  conjg :: "complex => complex"
  "conjg z == Complex (Re z) (- Im z)"

lemma Re_cong [simp]: "Re (conjg z) = Re z"
  by (simp add: conjg_def)

lemma Im_cong [simp]: "Im (conjg z) = - Im z"
  by (simp add: conjg_def)

lemma Re_conjg_self: "Re (z * conjg z) = (Re z)\<twosuperior> + (Im z)\<twosuperior>"
  by (simp add: real_power_two)

lemma Im_conjg_self: "Im (z * conjg z) = 0"
  by simp


subsection {* Embedding other number domains *}

constdefs
  complex :: "'a => complex"
  "complex x == Complex (real x) 0";

lemma Re_complex [simp]: "Re (complex x) = real x"
  by (simp add: complex_def)

end
