(*  Title:       Complex.ML
    Author:      Jacques D. Fleuriot
    Copyright:   2001  University of Edinburgh
    Description: Complex numbers
*)

Goal "inj Rep_complex";
by (rtac inj_inverseI 1);
by (rtac Rep_complex_inverse 1);
qed "inj_Rep_complex";

Goal "inj Abs_complex";
by (rtac inj_inverseI 1);
by (rtac Abs_complex_inverse 1);
by (simp_tac (simpset() addsimps [complex_def]) 1);
qed "inj_Abs_complex";
Addsimps [inj_Abs_complex RS injD];

Goal "(Abs_complex x = Abs_complex y) = (x = y)";
by (auto_tac (claset() addDs [inj_Abs_complex RS injD],simpset()));
qed "Abs_complex_cancel_iff";
Addsimps [Abs_complex_cancel_iff]; 

Goalw [complex_def] "(x,y) : complex";
by (Auto_tac);
qed "pair_mem_complex";
Addsimps [pair_mem_complex];

Goal "Rep_complex (Abs_complex (x,y)) = (x,y)";
by (simp_tac (simpset() addsimps [Abs_complex_inverse]) 1);
qed "Abs_complex_inverse2";
Addsimps [Abs_complex_inverse2];

val [prem] = goal Complex.thy
    "(!!x y. z = Abs_complex(x,y) ==> P) ==> P";
by (res_inst_tac [("p","Rep_complex z")] PairE 1);
by (dres_inst_tac [("f","Abs_complex")] arg_cong 1);
by (res_inst_tac [("x","x"),("y","y")] prem 1);
by (asm_full_simp_tac (simpset() addsimps [Rep_complex_inverse]) 1);
qed "eq_Abs_complex";

Goalw [Re_def] "Re(Abs_complex(x,y)) = x";
by (Simp_tac 1);
qed "Re";
Addsimps [Re];

Goalw [Im_def] "Im(Abs_complex(x,y)) = y";
by (Simp_tac 1);
qed "Im";
Addsimps [Im];

Goal "Abs_complex(Re(z),Im(z)) = z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (Asm_simp_tac 1);
qed "Abs_complex_cancel";
Addsimps [Abs_complex_cancel];

Goal "(w=z) = (Re(w) = Re(z) & Im(w) = Im(z))";
by (res_inst_tac [("z","w")] eq_Abs_complex 1);
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset() addDs [inj_Abs_complex RS injD],simpset()));
qed "complex_Re_Im_cancel_iff";

Goalw [complex_zero_def] "Re 0 = 0";
by (Simp_tac 1);
qed "complex_Re_zero";

Goalw [complex_zero_def] "Im 0 = 0";
by (Simp_tac 1);
qed "complex_Im_zero";
Addsimps [complex_Re_zero,complex_Im_zero];

Goalw [complex_one_def] "Re 1 = 1";
by (Simp_tac 1);
qed "complex_Re_one";
Addsimps [complex_Re_one];

Goalw [complex_one_def] "Im 1 = 0";
by (Simp_tac 1);
qed "complex_Im_one";
Addsimps [complex_Im_one];

Goalw [i_def] "Re(ii) = 0";
by Auto_tac;
qed "complex_Re_i";
Addsimps [complex_Re_i];

Goalw [i_def] "Im(ii) = 1";
by Auto_tac;
qed "complex_Im_i";
Addsimps [complex_Im_i];

Goalw [complex_of_real_def] "Re(complex_of_real 0) = 0";
by (Simp_tac 1);
qed "Re_complex_of_real_zero";
Addsimps [Re_complex_of_real_zero];

Goalw [complex_of_real_def] "Im(complex_of_real 0) = 0";
by (Simp_tac 1);
qed "Im_complex_of_real_zero";
Addsimps [Im_complex_of_real_zero];

Goalw [complex_of_real_def] "Re(complex_of_real 1) = 1";
by (Simp_tac 1);
qed "Re_complex_of_real_one";
Addsimps [Re_complex_of_real_one];

Goalw [complex_of_real_def] "Im(complex_of_real 1) = 0";
by (Simp_tac 1);
qed "Im_complex_of_real_one";
Addsimps [Im_complex_of_real_one];

Goalw [complex_of_real_def] "Re(complex_of_real z) = z";
by Auto_tac;
qed "Re_complex_of_real";
Addsimps [Re_complex_of_real];

Goalw [complex_of_real_def] "Im(complex_of_real z) = 0";
by Auto_tac;
qed "Im_complex_of_real";
Addsimps [Im_complex_of_real];

(*** negation ***)

Goalw [complex_minus_def] "- Abs_complex(x,y) = Abs_complex(-x,-y)";
by (Simp_tac 1);
qed "complex_minus";

Goalw [Re_def] "Re (-z) = - Re z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_minus]));
qed "complex_Re_minus";

Goalw [Im_def] "Im (-z) = - Im z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_minus]));
qed "complex_Im_minus";

Goalw [complex_minus_def] "- (- z) = (z::complex)";
by (Simp_tac 1);
qed "complex_minus_minus";
Addsimps [complex_minus_minus];

Goal "inj(%r::complex. -r)";
by (rtac injI 1);
by (dres_inst_tac [("f","uminus")] arg_cong 1);
by (Asm_full_simp_tac 1);
qed "inj_complex_minus";

Goalw [complex_zero_def] "-(0::complex) = 0";
by (simp_tac (simpset() addsimps [complex_minus]) 1);
qed "complex_minus_zero";
Addsimps [complex_minus_zero];

Goal "(-x = 0) = (x = (0::complex))"; 
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (auto_tac (claset() addDs [inj_Abs_complex RS injD],simpset() 
    addsimps [complex_zero_def,complex_minus]));
qed "complex_minus_zero_iff";
Addsimps [complex_minus_zero_iff];

Goal "(0 = -x) = (x = (0::real))"; 
by (auto_tac (claset() addDs [sym],simpset()));
qed "complex_minus_zero_iff2";
Addsimps [complex_minus_zero_iff2];

Goal "(-x ~= 0) = (x ~= (0::complex))"; 
by Auto_tac;
qed "complex_minus_not_zero_iff";

(*** addition ***)

Goalw [complex_add_def]
      "Abs_complex(x1,y1) + Abs_complex(x2,y2) = Abs_complex(x1+x2,y1+y2)";
by (Simp_tac 1);
qed "complex_add";

Goalw [Re_def] "Re(x + y) = Re(x) + Re(y)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (res_inst_tac [("z","y")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_add]));
qed "complex_Re_add";

Goalw [Im_def] "Im(x + y) = Im(x) + Im(y)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (res_inst_tac [("z","y")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_add]));
qed "complex_Im_add";

Goalw [complex_add_def] "(u::complex) + v = v + u";
by (simp_tac (simpset() addsimps [real_add_commute]) 1);
qed "complex_add_commute";

Goalw [complex_add_def] "((u::complex) + v) + w = u + (v + w)";
by (simp_tac (simpset() addsimps [real_add_assoc]) 1);
qed "complex_add_assoc";

Goalw [complex_add_def] "(x::complex) + (y + z) = y + (x + z)";
by (simp_tac (simpset() addsimps [real_add_left_commute]) 1);
qed "complex_add_left_commute";

val complex_add_ac = [complex_add_assoc,complex_add_commute,
                      complex_add_left_commute];

Goalw [complex_add_def,complex_zero_def] "(0::complex) + z = z";
by (Simp_tac 1);
qed "complex_add_zero_left";
Addsimps [complex_add_zero_left];

Goalw [complex_add_def,complex_zero_def] "z + (0::complex) = z";
by (Simp_tac 1);
qed "complex_add_zero_right";
Addsimps [complex_add_zero_right];

Goalw [complex_add_def,complex_minus_def,complex_zero_def] 
      "z + -z = (0::complex)";
by (Simp_tac 1);
qed "complex_add_minus_right_zero";
Addsimps [complex_add_minus_right_zero];

Goalw [complex_add_def,complex_minus_def,complex_zero_def] 
      "-z + z = (0::complex)";
by (Simp_tac 1);
qed "complex_add_minus_left_zero";
Addsimps [complex_add_minus_left_zero];

Goal "z + (- z + w) = (w::complex)";
by (simp_tac (simpset() addsimps [complex_add_assoc RS sym]) 1);
qed "complex_add_minus_cancel";

Goal "(-z) + (z + w) = (w::complex)";
by (simp_tac (simpset() addsimps [complex_add_assoc RS sym]) 1);
qed "complex_minus_add_cancel";

Addsimps [complex_add_minus_cancel, complex_minus_add_cancel];

Goal "x + y = (0::complex) ==> x = -y";
by (auto_tac (claset(),simpset() addsimps [complex_Re_Im_cancel_iff,
    complex_Re_add,complex_Im_add,complex_Re_minus,complex_Im_minus]));
qed "complex_add_minus_eq_minus";

Goal "-(x + y) = -x + -(y::complex)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (res_inst_tac [("z","y")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_minus,complex_add]));
qed "complex_minus_add_distrib";
Addsimps [complex_minus_add_distrib];

Goal "((x::complex) + y = x + z) = (y = z)";
by (Step_tac 1);
by (dres_inst_tac [("f","%t.-x + t")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [complex_add_assoc RS sym]) 1);
qed "complex_add_left_cancel";
AddIffs [complex_add_left_cancel];

Goal "(y + (x::complex)= z + x) = (y = z)";
by (simp_tac (simpset() addsimps [complex_add_commute]) 1);
qed "complex_add_right_cancel";
Addsimps [complex_add_right_cancel];

Goal "((x::complex) = y) = (0 = x + - y)";
by (Step_tac 1);
by (res_inst_tac [("x1","-y")] 
      (complex_add_right_cancel RS iffD1) 2);
by (Auto_tac);
qed "complex_eq_minus_iff"; 

Goal "((x::complex) = y) = (x + - y = 0)";
by (Step_tac 1);
by (res_inst_tac [("x1","-y")] 
      (complex_add_right_cancel RS iffD1) 2);
by (Auto_tac);
qed "complex_eq_minus_iff2"; 

Goal "(0::complex) - x = -x";
by (simp_tac (simpset() addsimps [complex_diff_def]) 1);
qed "complex_diff_0";

Goal "x - (0::complex) = x";
by (simp_tac (simpset() addsimps [complex_diff_def]) 1);
qed "complex_diff_0_right";

Goal "x - x = (0::complex)";
by (simp_tac (simpset() addsimps [complex_diff_def]) 1);
qed "complex_diff_self";

Addsimps [complex_diff_0, complex_diff_0_right, complex_diff_self];

Goalw [complex_diff_def]
      "Abs_complex(x1,y1) - Abs_complex(x2,y2) = Abs_complex(x1-x2,y1-y2)";
by (simp_tac (simpset() addsimps [complex_add,complex_minus]) 1);
qed "complex_diff";

Goal "((x::complex) - y = z) = (x = z + y)";
by (auto_tac (claset(),simpset() addsimps [complex_diff_def,complex_add_assoc]));
qed "complex_diff_eq_eq";

(*** complex multiplication ***)

Goalw [complex_mult_def]
      "Abs_complex(x1,y1) * Abs_complex(x2,y2) = \
\      Abs_complex(x1*x2 - y1*y2,x1*y2 + y1*x2)";
by (Simp_tac 1);
qed "complex_mult";

Goalw [complex_mult_def] "(w::complex) * z = z * w";
by (simp_tac (simpset() addsimps [real_mult_commute,real_add_commute]) 1);
qed "complex_mult_commute";

Goalw [complex_mult_def] "((u::complex) * v) * w = u * (v * w)";
by (simp_tac (simpset() addsimps [complex_Re_Im_cancel_iff,
    real_mult_assoc,real_diff_mult_distrib2,
    real_add_mult_distrib2,real_diff_mult_distrib,
    real_add_mult_distrib,real_mult_left_commute]) 1);
qed "complex_mult_assoc";

Goalw [complex_mult_def] "(x::complex) * (y * z) = y * (x * z)";
by (simp_tac (simpset() addsimps [complex_Re_Im_cancel_iff,
    real_mult_left_commute,real_diff_mult_distrib2,
    real_add_mult_distrib2]) 1);
qed "complex_mult_left_commute";

val complex_mult_ac = [complex_mult_assoc,complex_mult_commute,
                      complex_mult_left_commute];

Goalw [complex_one_def] "(1::complex) * z = z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_mult]) 1);
qed "complex_mult_one_left";
Addsimps [complex_mult_one_left];

Goal "z * (1::complex) = z";
by (simp_tac (simpset() addsimps [complex_mult_commute]) 1);
qed "complex_mult_one_right";
Addsimps [complex_mult_one_right];

Goalw [complex_zero_def] "(0::complex) * z = 0";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_mult]) 1);
qed "complex_mult_zero_left";
Addsimps [complex_mult_zero_left];

Goal "z * 0 = (0::complex)";
by (simp_tac (simpset() addsimps [complex_mult_commute]) 1);
qed "complex_mult_zero_right";
Addsimps [complex_mult_zero_right];

Goalw [complex_divide_def] "0 / z = (0::complex)";
by Auto_tac;
qed "complex_divide_zero";
Addsimps [complex_divide_zero];

Goal "-(x * y) = -x * (y::complex)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (res_inst_tac [("z","y")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_minus,
    real_diff_def]));
qed "complex_minus_mult_eq1";

Goal "-(x * y) = x * -(y::complex)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (res_inst_tac [("z","y")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_minus,
    real_diff_def]));
qed "complex_minus_mult_eq2";

Addsimps [ complex_minus_mult_eq1 RS sym, complex_minus_mult_eq2 RS sym];

Goal "-(1::complex) * z = -z";
by (Simp_tac 1);
qed "complex_mult_minus_one";
Addsimps [complex_mult_minus_one];

Goal "z * -(1::complex) = -z";
by (stac complex_mult_commute 1);
by (Simp_tac 1);
qed "complex_mult_minus_one_right";
Addsimps [complex_mult_minus_one_right];

Goal "-x * -y = x * (y::complex)";
by (Simp_tac 1);
qed "complex_minus_mult_cancel";
Addsimps [complex_minus_mult_cancel];

Goal "-x * y = x * -(y::complex)";
by (Simp_tac 1);
qed "complex_minus_mult_commute";

qed_goal "complex_add_assoc_cong" thy
    "!!z. (z::complex) + v = z' + v' ==> z + (v + w) = z' + (v' + w)"
 (fn _ => [(asm_simp_tac (simpset() addsimps [complex_add_assoc RS sym]) 1)]);

qed_goal "complex_add_assoc_swap" thy "(z::complex) + (v + w) = v + (z + w)"
 (fn _ => [(REPEAT (ares_tac [complex_add_commute RS complex_add_assoc_cong] 1))]);

Goal "((z1::complex) + z2) * w = (z1 * w) + (z2 * w)";
by (res_inst_tac [("z","z1")] eq_Abs_complex 1);
by (res_inst_tac [("z","z2")] eq_Abs_complex 1);
by (res_inst_tac [("z","w")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_add,
    real_add_mult_distrib,real_diff_def] @ real_add_ac));
qed "complex_add_mult_distrib";

Goal "(w::complex) * (z1 + z2) = (w * z1) + (w * z2)";
by (res_inst_tac [("z1","z1 + z2")] (complex_mult_commute RS ssubst) 1);
by (simp_tac (simpset() addsimps [complex_add_mult_distrib]) 1);
by (simp_tac (simpset() addsimps [complex_mult_commute]) 1);
qed "complex_add_mult_distrib2";

Goalw [complex_zero_def,complex_one_def] "(0::complex) ~= 1";
by (simp_tac (simpset() addsimps [complex_Re_Im_cancel_iff]) 1);
qed "complex_zero_not_eq_one";
Addsimps [complex_zero_not_eq_one];
Addsimps [complex_zero_not_eq_one RS not_sym];

(*** inverse ***)
Goalw [complex_inverse_def] "inverse (Abs_complex(x,y)) = \
\    Abs_complex(x/(x ^ 2 + y ^ 2),-y/(x ^ 2 + y ^ 2))";
by (Simp_tac 1);
qed "complex_inverse";

Goalw [complex_inverse_def,complex_zero_def] "inverse 0 = (0::complex)";
by Auto_tac;
qed "COMPLEX_INVERSE_ZERO";

Goal "a / (0::complex) = 0";
by (simp_tac (simpset() addsimps [complex_divide_def, COMPLEX_INVERSE_ZERO]) 1);
qed "COMPLEX_DIVISION_BY_ZERO";  (*NOT for adding to default simpset*)

fun complex_div_undefined_case_tac s i =
  case_tac s i THEN 
  asm_simp_tac (simpset() addsimps [COMPLEX_DIVISION_BY_ZERO, COMPLEX_INVERSE_ZERO]) i;

(*REMOVE?:
lemmas:replace previous versions to accommodate new behaviour of simplification
Goal "x ^ 2 + y ^ 2 = 0 ==> x = (0::real)";
by (auto_tac (claset() addIs [real_sum_squares_cancel],
    simpset() addsimps [CLAIM "2 = Suc(Suc 0)"]));
qed "real_sum_squares_cancel";

Goal "x ^ 2 + y ^ 2 = 0 ==> y = (0::real)";
by (auto_tac (claset() addIs [real_sum_squares_cancel2],
    simpset() addsimps [CLAIM "2 = Suc(Suc 0)"]));
qed "real_sum_squares_cancel2";
*)

Goal "z ~= (0::complex) ==> inverse(z) * z = 1";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_inverse,
    complex_one_def,complex_zero_def,real_add_divide_distrib RS sym,
    realpow_two_eq_mult] @ real_mult_ac));
by (dres_inst_tac [("y","y")] real_sum_squares_not_zero 1);
by (dres_inst_tac [("x","x")] real_sum_squares_not_zero2 2);
by Auto_tac;
qed "complex_mult_inv_left";
Addsimps [complex_mult_inv_left];

Goal "z ~= (0::complex) ==> z * inverse(z) = 1";
by (auto_tac (claset() addIs [complex_mult_commute RS subst],simpset()));
qed "complex_mult_inv_right";
Addsimps [complex_mult_inv_right];

Goal "(c::complex) ~= 0 ==> (c*a=c*b) = (a=b)";
by Auto_tac;
by (dres_inst_tac [("f","%x. x*inverse c")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps complex_mult_ac)  1);
qed "complex_mult_left_cancel";
    
Goal "(c::complex) ~= 0 ==> (a*c=b*c) = (a=b)";
by (Step_tac 1);
by (dres_inst_tac [("f","%x. x*inverse c")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps complex_mult_ac)  1);
qed "complex_mult_right_cancel";

Goal "z ~= 0 ==> inverse(z::complex) ~= 0";
by (Step_tac 1);
by (ftac (complex_mult_right_cancel RS iffD2) 1);
by (thin_tac "inverse z = 0" 2);
by (assume_tac 1 THEN Auto_tac);
qed "complex_inverse_not_zero";
Addsimps [complex_inverse_not_zero];

Goal "!!x. [| x ~= 0; y ~= (0::complex) |] ==> x * y ~= 0";
by (Step_tac 1);
by (dres_inst_tac [("f","%z. inverse x*z")] arg_cong 1);
by (asm_full_simp_tac (simpset() addsimps [complex_mult_assoc RS sym]) 1);
qed "complex_mult_not_zero";

bind_thm ("complex_mult_not_zeroE",complex_mult_not_zero RS notE);

Goal "inverse(inverse (x::complex)) = x";
by (complex_div_undefined_case_tac "x = 0" 1);
by (res_inst_tac [("c1","inverse x")] (complex_mult_right_cancel RS iffD1) 1);
by (etac complex_inverse_not_zero 1);
by (auto_tac (claset() addDs [complex_inverse_not_zero],simpset()));
qed "complex_inverse_inverse";
Addsimps [complex_inverse_inverse];

Goalw [complex_one_def] "inverse(1::complex) = 1";
by (simp_tac (simpset() addsimps [complex_inverse,realpow_num_two]) 1);
qed "complex_inverse_one";
Addsimps [complex_inverse_one];

Goal "inverse(-x) = -inverse(x::complex)";
by (complex_div_undefined_case_tac "x = 0" 1);
by (res_inst_tac [("c1","-x")] (complex_mult_right_cancel RS iffD1) 1);
by (stac complex_mult_inv_left 2);
by Auto_tac;
qed "complex_minus_inverse";

Goal "inverse(x*y) = inverse x * inverse (y::complex)";
by (complex_div_undefined_case_tac "x = 0" 1);
by (complex_div_undefined_case_tac "y = 0" 1);
by (res_inst_tac [("c1","x*y")] (complex_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult_not_zero]
    @ complex_mult_ac));
by (auto_tac (claset(),simpset() addsimps [complex_mult_not_zero,
    complex_mult_assoc RS sym]));
qed "complex_inverse_distrib";


(*** division ***)

(*adding some of these theorems to simpset as for reals: 
  not 100% convinced for some*)

Goal "(x::complex) * (y/z) = (x*y)/z";
by (simp_tac (simpset() addsimps [complex_divide_def, complex_mult_assoc]) 1); 
qed "complex_times_divide1_eq";

Goal "(y/z) * (x::complex) = (y*x)/z";
by (simp_tac (simpset() addsimps [complex_divide_def]@complex_mult_ac) 1); 
qed "complex_times_divide2_eq";

Addsimps [complex_times_divide1_eq, complex_times_divide2_eq];

Goal "(x::complex) / (y/z) = (x*z)/y";
by (simp_tac (simpset() addsimps [complex_divide_def, complex_inverse_distrib]@
                                  complex_mult_ac) 1); 
qed "complex_divide_divide1_eq";

Goal "((x::complex) / y) / z = x/(y*z)";
by (simp_tac (simpset() addsimps [complex_divide_def, complex_inverse_distrib, 
                                  complex_mult_assoc]) 1); 
qed "complex_divide_divide2_eq";

Addsimps [complex_divide_divide1_eq, complex_divide_divide2_eq];

(** As with multiplication, pull minus signs OUT of the / operator **)

Goal "(-x) / (y::complex) = - (x/y)";
by (simp_tac (simpset() addsimps [complex_divide_def]) 1); 
qed "complex_minus_divide_eq";
Addsimps [complex_minus_divide_eq];

Goal "(x / -(y::complex)) = - (x/y)";
by (simp_tac (simpset() addsimps [complex_divide_def, complex_minus_inverse]) 1); 
qed "complex_divide_minus_eq";
Addsimps [complex_divide_minus_eq];

Goal "(x+y)/(z::complex) = x/z + y/z";
by (simp_tac (simpset() addsimps [complex_divide_def, complex_add_mult_distrib]) 1); 
qed "complex_add_divide_distrib";

(*---------------------------------------------------------------------------*)
(*          Embedding properties for complex_of_real map                     *)
(*---------------------------------------------------------------------------*)

Goal "inj complex_of_real";
by (rtac injI 1);
by (auto_tac (claset() addDs [inj_Abs_complex RS injD],
    simpset() addsimps [complex_of_real_def]));
qed "inj_complex_of_real";

Goalw [complex_one_def,complex_of_real_def]
      "complex_of_real 1 = 1";
by (rtac refl 1);
qed "complex_of_real_one";
Addsimps [complex_of_real_one];

Goalw [complex_zero_def,complex_of_real_def]
      "complex_of_real 0 = 0";
by (rtac refl 1);
qed "complex_of_real_zero";
Addsimps [complex_of_real_zero];

Goal "(complex_of_real x = complex_of_real y) = (x = y)";
by (auto_tac (claset() addDs [inj_complex_of_real RS injD],simpset()));
qed "complex_of_real_eq_iff";
AddIffs [complex_of_real_eq_iff];

Goal "complex_of_real(-x) = - complex_of_real x";
by (simp_tac (simpset() addsimps [complex_of_real_def,complex_minus]) 1);
qed "complex_of_real_minus";

Goal "complex_of_real(inverse x) = inverse(complex_of_real x)";
by (real_div_undefined_case_tac "x=0" 1);
by (simp_tac (simpset() addsimps [DIVISION_BY_ZERO,COMPLEX_INVERSE_ZERO]) 1);
by (auto_tac (claset(),simpset() addsimps [complex_inverse,
    complex_of_real_def,realpow_num_two,real_divide_def,
    real_inverse_distrib]));
qed "complex_of_real_inverse";

Goal "complex_of_real x + complex_of_real y = complex_of_real (x + y)";
by (simp_tac (simpset() addsimps [complex_add,complex_of_real_def]) 1);
qed "complex_of_real_add";

Goal "complex_of_real x - complex_of_real y = complex_of_real (x - y)";
by (simp_tac (simpset() addsimps [complex_of_real_minus RS sym,
    complex_diff_def,complex_of_real_add]) 1);
qed "complex_of_real_diff";

Goal "complex_of_real x * complex_of_real y = complex_of_real (x * y)";
by (simp_tac (simpset() addsimps [complex_mult,complex_of_real_def]) 1);
qed "complex_of_real_mult";

Goalw [complex_divide_def] 
      "complex_of_real x / complex_of_real y = complex_of_real(x/y)";
by (real_div_undefined_case_tac "y=0" 1);
by (simp_tac (simpset() addsimps [rename_numerals DIVISION_BY_ZERO,
    COMPLEX_INVERSE_ZERO]) 1);
by (asm_simp_tac (simpset() addsimps [complex_of_real_mult RS sym,
    complex_of_real_inverse,real_divide_def]) 1);
qed "complex_of_real_divide";

Goal "complex_of_real (x ^ n) = (complex_of_real x) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [complex_of_real_mult RS sym]));
qed "complex_of_real_pow";

Goalw [cmod_def] "cmod (Abs_complex(x,y)) = sqrt(x ^ 2 + y ^ 2)";
by (Simp_tac 1);
qed "complex_mod";

Goalw [cmod_def] "cmod(0) = 0";
by (Simp_tac 1);
qed "complex_mod_zero";
Addsimps [complex_mod_zero];

Goalw [cmod_def] "cmod(1) = 1";
by (simp_tac (simpset() addsimps [realpow_num_two]) 1);
qed "complex_mod_one";
Addsimps [complex_mod_one];

Goalw [complex_of_real_def] "cmod(complex_of_real x) = abs x";
by (simp_tac (simpset() addsimps [complex_mod,realpow_num_two]) 1);
qed "complex_mod_complex_of_real";
Addsimps [complex_mod_complex_of_real];

Goal "complex_of_real (abs x) = complex_of_real(cmod(complex_of_real x))";
by (Simp_tac 1);
qed "complex_of_real_abs";

(*---------------------------------------------------------------------------*)
(*                   conjugation is an automorphism                          *)
(*---------------------------------------------------------------------------*)

Goalw [cnj_def] "cnj (Abs_complex(x,y)) = Abs_complex(x,-y)";
by (Simp_tac 1);
qed "complex_cnj";

Goal "inj cnj";
by (rtac injI 1);
by (auto_tac (claset(),simpset() addsimps [cnj_def,
    Abs_complex_cancel_iff,complex_Re_Im_cancel_iff]));
qed "inj_cnj";

Goal "(cnj x = cnj y) = (x = y)";
by (auto_tac (claset() addDs [inj_cnj RS injD],simpset()));
qed "complex_cnj_cancel_iff";
Addsimps [complex_cnj_cancel_iff];

Goalw [cnj_def] "cnj (cnj z) = z";
by (Simp_tac 1);
qed "complex_cnj_cnj";
Addsimps [complex_cnj_cnj];

Goalw [complex_of_real_def] "cnj (complex_of_real x) = complex_of_real x";
by (simp_tac (simpset() addsimps [complex_cnj]) 1);
qed "complex_cnj_complex_of_real";
Addsimps [complex_cnj_complex_of_real];

Goal "cmod (cnj z) = cmod z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_cnj,complex_mod,realpow_num_two]) 1);
qed "complex_mod_cnj";
Addsimps [complex_mod_cnj];

Goalw [cnj_def] "cnj (-z) = - cnj z";
by (simp_tac (simpset() addsimps [complex_minus,
    complex_Re_minus,complex_Im_minus]) 1);
qed "complex_cnj_minus";

Goal "cnj(inverse z) = inverse(cnj z)";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_cnj,complex_inverse,
    realpow_num_two]) 1);
qed "complex_cnj_inverse";

Goal "cnj(w + z) = cnj(w) + cnj(z)";
by (res_inst_tac [("z","w")] eq_Abs_complex 1);
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_cnj,complex_add]) 1);
qed "complex_cnj_add";

Goalw [complex_diff_def] "cnj(w - z) = cnj(w) - cnj(z)";
by (simp_tac (simpset() addsimps [complex_cnj_add,complex_cnj_minus]) 1);
qed "complex_cnj_diff";

Goal "cnj(w * z) = cnj(w) * cnj(z)";
by (res_inst_tac [("z","w")] eq_Abs_complex 1);
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_cnj,complex_mult]) 1);
qed "complex_cnj_mult";

Goalw [complex_divide_def] "cnj(w / z) = (cnj w)/(cnj z)";
by (simp_tac (simpset() addsimps [complex_cnj_mult,complex_cnj_inverse]) 1);
qed "complex_cnj_divide";

Goalw [cnj_def,complex_one_def] "cnj 1 = 1";
by (Simp_tac 1);
qed "complex_cnj_one";
Addsimps [complex_cnj_one];

Goal "cnj(z ^ n) = cnj(z) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [complex_cnj_mult]));
qed "complex_cnj_pow";

Goal "z + cnj z = complex_of_real (2 * Re(z))";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_add,complex_cnj,
    complex_of_real_def]) 1);
qed "complex_add_cnj";

Goal "z - cnj z = complex_of_real (2 * Im(z)) * ii";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_add,complex_cnj,
    complex_of_real_def,complex_diff_def,complex_minus,
    i_def,complex_mult]) 1);
qed "complex_diff_cnj";

goalw Complex.thy  [cnj_def,complex_zero_def] 
      "cnj 0 = 0";
by Auto_tac;
qed "complex_cnj_zero";
Addsimps [complex_cnj_zero];

goal Complex.thy "(cnj z = 0) = (z = 0)";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_zero_def,
    complex_cnj]));
qed "complex_cnj_zero_iff";
AddIffs [complex_cnj_zero_iff];

Goal "z * cnj z = complex_of_real (Re(z) ^ 2 + Im(z) ^ 2)";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_cnj,complex_mult,
    complex_of_real_def,realpow_num_two]));
qed "complex_mult_cnj";

(*---------------------------------------------------------------------------*)
(*                              algebra                                      *)
(*---------------------------------------------------------------------------*)

Goal "(x*y = (0::complex)) = (x = 0 | y = 0)";
by Auto_tac;
by (auto_tac (claset() addIs [ccontr] addDs 
    [complex_mult_not_zero],simpset()));
qed "complex_mult_zero_iff";
AddIffs [complex_mult_zero_iff];

Goalw [complex_zero_def] "(x + y = x) = (y = (0::complex))";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (res_inst_tac [("z","y")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_add]));
qed "complex_add_left_cancel_zero";
Addsimps [complex_add_left_cancel_zero];

Goalw [complex_diff_def] 
      "((z1::complex) - z2) * w = (z1 * w) - (z2 * w)";
by (simp_tac (simpset() addsimps [complex_add_mult_distrib]) 1);
qed "complex_diff_mult_distrib";

Goalw [complex_diff_def]
      "(w::complex) * (z1 - z2) = (w * z1) - (w * z2)";
by (simp_tac (simpset() addsimps [complex_add_mult_distrib2]) 1);
qed "complex_diff_mult_distrib2";

(*---------------------------------------------------------------------------*)
(*                               modulus                                     *)
(*---------------------------------------------------------------------------*)

(*
Goal "[| sqrt(x) = 0; 0 <= x |] ==> x = 0";
by (auto_tac (claset() addIs [real_sqrt_eq_zero_cancel],
    simpset()));
qed "real_sqrt_eq_zero_cancel2";
*)

Goal "(cmod x = 0) = (x = 0)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (auto_tac (claset() addIs
    [real_sum_squares_cancel,real_sum_squares_cancel2],
    simpset() addsimps [complex_mod,complex_zero_def,
    realpow_num_two]));
qed "complex_mod_eq_zero_cancel";
Addsimps [complex_mod_eq_zero_cancel];

Goal "cmod (complex_of_real(real (n::nat))) = real n";
by (Simp_tac 1);
qed "complex_mod_complex_of_real_of_nat";
Addsimps [complex_mod_complex_of_real_of_nat];

Goal "cmod (-x) = cmod(x)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_mod,complex_minus,
    realpow_num_two]) 1);
qed "complex_mod_minus";
Addsimps [complex_mod_minus];

Goal "cmod(z * cnj(z)) = cmod(z) ^ 2";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_mod,complex_cnj,
    complex_mult, CLAIM "0 ^ 2 = (0::real)"]) 1);
by (simp_tac (simpset() addsimps [realpow_two_eq_mult]) 1);
qed "complex_mod_mult_cnj";

Goalw [cmod_def] "cmod(Abs_complex(x,y)) ^ 2 = x ^ 2 + y ^ 2";
by Auto_tac;
qed "complex_mod_squared";

Goalw [cmod_def]  "0 <= cmod x";
by (auto_tac (claset() addIs [real_sqrt_ge_zero],simpset()));
qed "complex_mod_ge_zero";
Addsimps [complex_mod_ge_zero];

Goal "abs(cmod x) = cmod x";
by (auto_tac (claset() addIs [abs_eqI1],simpset()));
qed "abs_cmod_cancel";
Addsimps [abs_cmod_cancel];

Goal "cmod(x*y) = cmod(x) * cmod(y)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (res_inst_tac [("z","y")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult,
    complex_mod,real_sqrt_mult_distrib2 RS sym] delsimps [realpow_Suc]));
by (res_inst_tac [("n","1")] realpow_Suc_cancel_eq 1);
by (auto_tac (claset(),simpset() addsimps [realpow_num_two RS sym] 
    delsimps [realpow_Suc]));
by (auto_tac (claset(),simpset() addsimps [real_diff_def,realpow_num_two,
    real_add_mult_distrib2,real_add_mult_distrib] @ real_add_ac @ 
    real_mult_ac));
qed "complex_mod_mult";

Goal "cmod(x + y) ^ 2 = cmod(x) ^ 2 + cmod(y) ^ 2 + 2 * Re(x * cnj y)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (res_inst_tac [("z","y")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_add,
    complex_mod_squared,complex_mult,complex_cnj,real_diff_def] 
    delsimps [realpow_Suc]));
by (auto_tac (claset(),simpset() addsimps [real_add_mult_distrib2,
    real_add_mult_distrib,realpow_num_two] @ real_mult_ac @ real_add_ac));
qed "complex_mod_add_squared_eq";

Goal "Re(x * cnj y) <= cmod(x * cnj y)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (res_inst_tac [("z","y")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mod,
    complex_mult,complex_cnj,real_diff_def] delsimps [realpow_Suc]));
qed "complex_Re_mult_cnj_le_cmod";
Addsimps [complex_Re_mult_cnj_le_cmod];

Goal "Re(x * cnj y) <= cmod(x * y)";
by (cut_inst_tac [("x","x"),("y","y")] complex_Re_mult_cnj_le_cmod 1);
by (asm_full_simp_tac (simpset() addsimps [complex_mod_mult]) 1);
qed "complex_Re_mult_cnj_le_cmod2";
Addsimps [complex_Re_mult_cnj_le_cmod2];

Goal "((x::real) + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y";
by (simp_tac (simpset() addsimps [real_add_mult_distrib,
    real_add_mult_distrib2,realpow_num_two]) 1);
qed "real_sum_squared_expand";

Goal "cmod (x + y) ^ 2 <= (cmod(x) + cmod(y)) ^ 2";
by (simp_tac (simpset() addsimps [real_sum_squared_expand,
    complex_mod_add_squared_eq,real_mult_assoc,complex_mod_mult RS sym]) 1);
qed "complex_mod_triangle_squared";
Addsimps [complex_mod_triangle_squared];

Goal "- cmod x <= cmod x";
by (rtac (complex_mod_ge_zero RSN (2,real_le_trans)) 1);
by (Simp_tac 1);
qed "complex_mod_minus_le_complex_mod";
Addsimps [complex_mod_minus_le_complex_mod];

Goal "cmod (x + y) <= cmod(x) + cmod(y)";
by (res_inst_tac [("n","1")] realpow_increasing 1);
by (auto_tac (claset() addIs [(complex_mod_ge_zero RSN (2,real_le_trans))],
    simpset() addsimps [realpow_num_two RS sym]));
qed "complex_mod_triangle_ineq";
Addsimps [complex_mod_triangle_ineq];

Goal "cmod(b + a) - cmod b <= cmod a";
by (cut_inst_tac [("x1","b"),("y1","a"),("z","-cmod b")]
   (complex_mod_triangle_ineq RS real_add_le_mono1) 1);
by (Simp_tac 1);
qed "complex_mod_triangle_ineq2";
Addsimps [complex_mod_triangle_ineq2];

Goal "cmod (x - y) = cmod (y - x)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (res_inst_tac [("z","y")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_diff,
    complex_mod,real_diff_mult_distrib2,realpow_num_two,
    real_diff_mult_distrib] @ real_add_ac @ real_mult_ac));
qed "complex_mod_diff_commute";

Goal "[| cmod x < r; cmod y < s |] ==> cmod (x + y) < r + s";
by (auto_tac (claset() addIs [order_le_less_trans,
    complex_mod_triangle_ineq],simpset()));
qed "complex_mod_add_less";

Goal "[| cmod x < r; cmod y < s |] ==> cmod (x * y) < r * s";
by (auto_tac (claset() addIs [real_mult_less_mono'],simpset()     
    addsimps [complex_mod_mult]));
qed "complex_mod_mult_less";

goal Complex.thy "cmod(a) - cmod(b) <= cmod(a + b)";
by (res_inst_tac [("R1.0","cmod(a)"),("R2.0","cmod(b)")]
    real_linear_less2 1);
by Auto_tac;
by (dtac (ARITH_PROVE "a < b ==> a - (b::real) < 0") 1);
by (rtac real_le_trans 1 THEN rtac order_less_imp_le 1);
by Auto_tac;
by (dtac (ARITH_PROVE "a < b ==> 0 < (b::real) - a") 1);
by (rtac (ARITH_PROVE "a  <= b + c ==> a - c <= (b::real)") 1);
by (rtac (complex_mod_minus RS subst) 1);
by (rtac real_le_trans 1);
by (rtac complex_mod_triangle_ineq 2);
by (auto_tac (claset(),simpset() addsimps complex_add_ac));
qed "complex_mod_diff_ineq";
Addsimps [complex_mod_diff_ineq];

Goal "Re z <= cmod z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mod]
    delsimps [realpow_Suc]));
qed "complex_Re_le_cmod";
Addsimps [complex_Re_le_cmod];

Goal "z ~= 0 ==> 0 < cmod z";
by (cut_inst_tac [("x","z")] complex_mod_ge_zero 1);
by (dtac order_le_imp_less_or_eq 1);
by Auto_tac;
qed "complex_mod_gt_zero";


(*---------------------------------------------------------------------------*)
(*                       a few more theorems                                 *)
(*---------------------------------------------------------------------------*)

Goal "cmod(x ^ n) = cmod(x) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [complex_mod_mult]));
qed "complex_mod_complexpow";

Goal "(-x::complex) ^ n = (if even n then (x ^ n) else -(x ^ n))";
by (induct_tac "n" 1);
by Auto_tac;
qed "complexpow_minus";

Goal "inverse (-x) = - inverse (x::complex)";
by (res_inst_tac [("z","x")] eq_Abs_complex 1);
by (asm_simp_tac (simpset() addsimps [complex_inverse,complex_minus,
    realpow_num_two]) 1);
qed "complex_inverse_minus";

Goalw [complex_divide_def] "x / (1::complex) = x";
by (Simp_tac 1);
qed "complex_divide_one";
Addsimps [complex_divide_one];

Goal "cmod(inverse x) = inverse(cmod x)";
by (complex_div_undefined_case_tac "x=0" 1);
by (res_inst_tac [("c1","cmod x")] (real_mult_left_cancel RS iffD1) 1);
by (auto_tac (claset(),simpset() addsimps [complex_mod_mult RS sym]));
qed "complex_mod_inverse";

Goalw [complex_divide_def,real_divide_def]
      "cmod(x/y) = cmod(x)/(cmod y)";
by (auto_tac (claset(),simpset() addsimps [complex_mod_mult,
    complex_mod_inverse]));
qed "complex_mod_divide";

Goalw [complex_divide_def]  
      "inverse(x/y) = y/(x::complex)";
by (auto_tac (claset(),simpset() addsimps [complex_inverse_distrib,
    complex_mult_commute]));
qed "complex_inverse_divide";
Addsimps [complex_inverse_divide];

Goal "((r::complex) * s) ^ n = (r ^ n) * (s ^ n)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps complex_mult_ac));
qed "complexpow_mult";

(*---------------------------------------------------------------------------*)
(*                       More exponentiation                                 *)
(*---------------------------------------------------------------------------*)

Goal "(0::complex) ^ (Suc n) = 0";
by (Auto_tac);
qed "complexpow_zero";
Addsimps [complexpow_zero];

Goal "r ~= (0::complex) --> r ^ n ~= 0";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult_not_zero]));
qed_spec_mp "complexpow_not_zero";
Addsimps [complexpow_not_zero];
AddIs [complexpow_not_zero];

Goal "r ^ n = (0::complex) ==> r = 0";
by (blast_tac (claset() addIs [ccontr] 
    addDs [complexpow_not_zero]) 1);
qed "complexpow_zero_zero";

Goalw [i_def] "ii ^ 2 = -(1::complex)";
by (auto_tac (claset(),simpset() addsimps 
    [complex_mult,complex_one_def,complex_minus,realpow_num_two]));
qed "complexpow_i_squared";
Addsimps [complexpow_i_squared];

Goalw [i_def,complex_zero_def] "ii ~= 0";
by Auto_tac;
qed "complex_i_not_zero";
Addsimps [complex_i_not_zero];

Goal "x * y ~= (0::complex) ==> x ~= 0";
by Auto_tac;
qed "complex_mult_eq_zero_cancel1";

Goal "x * y ~= 0 ==> y ~= (0::complex)";
by Auto_tac;
qed "complex_mult_eq_zero_cancel2";

Goal "(x * y ~= 0) = (x ~= 0 & y ~= (0::complex))";
by Auto_tac;
qed "complex_mult_not_eq_zero_iff";
AddIffs [complex_mult_not_eq_zero_iff];

Goal "inverse ((r::complex) ^ n) = (inverse r) ^ n";
by (induct_tac "n" 1);
by (auto_tac (claset(), simpset() addsimps [complex_inverse_distrib]));
qed "complexpow_inverse";

(*---------------------------------------------------------------------------*)
(* sgn                                                                       *)
(*---------------------------------------------------------------------------*)

Goalw [sgn_def] "sgn 0 = 0";
by (Simp_tac 1);
qed "sgn_zero";
Addsimps[sgn_zero];

Goalw [sgn_def] "sgn 1 = 1";
by (Simp_tac 1);
qed "sgn_one";
Addsimps [sgn_one];

Goalw [sgn_def] "sgn (-z) = - sgn(z)";
by Auto_tac;
qed "sgn_minus";

Goalw [sgn_def] 
    "sgn z = z / complex_of_real (cmod z)";
by (Simp_tac 1);
qed "sgn_eq";

Goal "EX x y. z = complex_of_real(x) + ii * complex_of_real(y)";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_of_real_def,
    i_def,complex_mult,complex_add]));
qed "complex_split";

Goal "Re(complex_of_real(x) + ii * complex_of_real(y)) = x";
by (auto_tac (claset(),simpset() addsimps [complex_of_real_def,
    i_def,complex_mult,complex_add]));
qed "Re_complex_i";
Addsimps [Re_complex_i];

Goal "Im(complex_of_real(x) + ii * complex_of_real(y)) = y";
by (auto_tac (claset(),simpset() addsimps [complex_of_real_def,
    i_def,complex_mult,complex_add]));
qed "Im_complex_i";
Addsimps [Im_complex_i];

Goalw [i_def,complex_of_real_def] "ii * ii = complex_of_real (-1)";
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_add]));
qed "i_mult_eq";

Goalw [i_def,complex_one_def] "ii * ii = -(1::complex)";
by (simp_tac (simpset() addsimps [complex_mult,complex_minus]) 1);
qed "i_mult_eq2";
Addsimps [i_mult_eq2];

Goal "cmod (complex_of_real(x) + ii * complex_of_real(y)) = \
\     sqrt (x ^ 2 + y ^ 2)";
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_add,
    i_def,complex_of_real_def,cmod_def]));
qed "cmod_i";

Goalw [complex_of_real_def,i_def] 
     "complex_of_real xa + ii * complex_of_real ya = \
\     complex_of_real xb + ii * complex_of_real yb \
\      ==> xa = xb";
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_add]));
qed "complex_eq_Re_eq";

Goalw [complex_of_real_def,i_def] 
     "complex_of_real xa + ii * complex_of_real ya = \
\     complex_of_real xb + ii * complex_of_real yb \
\      ==> ya = yb";
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_add]));
qed "complex_eq_Im_eq";

Goal "(complex_of_real xa + ii * complex_of_real ya = \
\      complex_of_real xb + ii * complex_of_real yb) = ((xa = xb) & (ya = yb))";
by (auto_tac (claset() addIs [complex_eq_Im_eq,complex_eq_Re_eq],simpset()));
qed "complex_eq_cancel_iff";
AddIffs [complex_eq_cancel_iff];

Goal "(complex_of_real xa + complex_of_real ya * ii = \
\      complex_of_real xb + complex_of_real yb * ii ) = ((xa = xb) & (ya = yb))";
by (auto_tac (claset(),simpset() addsimps [complex_mult_commute]));
qed "complex_eq_cancel_iffA";
AddIffs [complex_eq_cancel_iffA];

Goal "(complex_of_real xa + complex_of_real ya * ii = \
\      complex_of_real xb + ii * complex_of_real yb) = ((xa = xb) & (ya = yb))";
by (auto_tac (claset(),simpset() addsimps [complex_mult_commute]));
qed "complex_eq_cancel_iffB";
AddIffs [complex_eq_cancel_iffB];

Goal "(complex_of_real xa + ii * complex_of_real ya  = \
\      complex_of_real xb + complex_of_real yb * ii) = ((xa = xb) & (ya = yb))";
by (auto_tac (claset(),simpset() addsimps [complex_mult_commute]));
qed "complex_eq_cancel_iffC";
AddIffs [complex_eq_cancel_iffC];

Goal"(complex_of_real x + ii * complex_of_real y = \
\     complex_of_real xa) = (x = xa & y = 0)";
by (cut_inst_tac [("xa","x"),("ya","y"),("xb","xa"),("yb","0")]  
    complex_eq_cancel_iff 1);
by (asm_full_simp_tac (simpset() delsimps [complex_eq_cancel_iff]) 1);
qed "complex_eq_cancel_iff2";
Addsimps [complex_eq_cancel_iff2];

Goal"(complex_of_real x + complex_of_real y * ii = \
\     complex_of_real xa) = (x = xa & y = 0)";
by (auto_tac (claset(),simpset() addsimps [complex_mult_commute]));
qed "complex_eq_cancel_iff2a";
Addsimps [complex_eq_cancel_iff2a];

Goal "(complex_of_real x + ii * complex_of_real y = \
\     ii * complex_of_real ya) = (x = 0 & y = ya)";
by (cut_inst_tac [("xa","x"),("ya","y"),("xb","0"),("yb","ya")]  
    complex_eq_cancel_iff 1);
by (asm_full_simp_tac (simpset() delsimps [complex_eq_cancel_iff]) 1);
qed "complex_eq_cancel_iff3";
Addsimps [complex_eq_cancel_iff3];

Goal "(complex_of_real x + complex_of_real y * ii = \
\     ii * complex_of_real ya) = (x = 0 & y = ya)";
by (auto_tac (claset(),simpset() addsimps [complex_mult_commute]));
qed "complex_eq_cancel_iff3a";
Addsimps [complex_eq_cancel_iff3a];

Goalw [complex_of_real_def,i_def,complex_zero_def] 
     "complex_of_real x + ii * complex_of_real y = 0 \
\     ==> x = 0";
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_add]));
qed "complex_split_Re_zero";

Goalw [complex_of_real_def,i_def,complex_zero_def] 
     "complex_of_real x + ii * complex_of_real y = 0 \
\     ==> y = 0";
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_add]));
qed "complex_split_Im_zero";

Goalw [sgn_def,complex_divide_def] 
      "Re(sgn z) = Re(z)/cmod z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_of_real_inverse RS sym]));
by (auto_tac (claset(),simpset() addsimps [complex_of_real_def,
    complex_mult,real_divide_def]));
qed "Re_sgn";
Addsimps [Re_sgn];

Goalw [sgn_def,complex_divide_def] 
      "Im(sgn z) = Im(z)/cmod z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_of_real_inverse RS sym]));
by (auto_tac (claset(),simpset() addsimps [complex_of_real_def,
    complex_mult,real_divide_def]));
qed "Im_sgn";
Addsimps [Im_sgn];

Goalw [complex_of_real_def,i_def] 
     "inverse(complex_of_real x + ii * complex_of_real y) = \
\     complex_of_real(x/(x ^ 2 + y ^ 2)) - \
\     ii * complex_of_real(y/(x ^ 2 + y ^ 2))";
by (auto_tac (claset(),simpset() addsimps [complex_mult,complex_add,
    complex_diff_def,complex_minus,complex_inverse,real_divide_def]));
qed "complex_inverse_complex_split";

(*----------------------------------------------------------------------------*)
(* Many of the theorems below need to be moved elsewhere e.g. Transc.ML. Also *)
(* many of the theorems are not used - so should they be kept?                *)
(*----------------------------------------------------------------------------*)

Goalw [i_def,complex_of_real_def]
    "Re (ii * complex_of_real y) = 0";
by (auto_tac (claset(),simpset() addsimps [complex_mult]));
qed "Re_mult_i_eq";
Addsimps [Re_mult_i_eq];

Goalw [i_def,complex_of_real_def]
    "Im (ii * complex_of_real y) = y";
by (auto_tac (claset(),simpset() addsimps [complex_mult]));
qed "Im_mult_i_eq";
Addsimps [Im_mult_i_eq];

Goalw [i_def,complex_of_real_def]
    "cmod (ii * complex_of_real y) = abs y";
by (auto_tac (claset(),simpset() addsimps [complex_mult,
    complex_mod,realpow_num_two]));
qed "complex_mod_mult_i";
Addsimps [complex_mod_mult_i];

Goalw [arg_def] 
   "0 < y ==> cos (arg(ii * complex_of_real y)) = 0";
by (auto_tac (claset(),simpset() addsimps [abs_eqI2]));
by (res_inst_tac [("a","pi/2")] someI2 1);
by Auto_tac;
by (res_inst_tac [("R2.0","0")] real_less_trans 1);
by Auto_tac;
qed "cos_arg_i_mult_zero";
Addsimps [cos_arg_i_mult_zero];

Goalw [arg_def] 
   "y < 0 ==> cos (arg(ii * complex_of_real y)) = 0";
by (auto_tac (claset(),simpset() addsimps [abs_minus_eqI2]));
by (res_inst_tac [("a","- pi/2")] someI2 1);
by Auto_tac;
by (res_inst_tac [("j","0")] real_le_trans 1);
by Auto_tac;
qed "cos_arg_i_mult_zero2";
Addsimps [cos_arg_i_mult_zero2];

Goalw [complex_zero_def,complex_of_real_def] 
      "(complex_of_real y ~= 0) = (y ~= 0)";
by Auto_tac;
qed "complex_of_real_not_zero_iff";
Addsimps [complex_of_real_not_zero_iff];

Goal "(complex_of_real y = 0) = (y = 0)";
by Auto_tac;
by (rtac ccontr 1 THEN dtac (complex_of_real_not_zero_iff RS iffD2) 1);
by (Asm_full_simp_tac 1);
qed "complex_of_real_zero_iff";
Addsimps [complex_of_real_zero_iff];

Goal "y ~= 0 ==> cos (arg(ii * complex_of_real y)) = 0";
by (cut_inst_tac [("R1.0","y"),("R2.0","0")] real_linear 1);
by Auto_tac;
qed "cos_arg_i_mult_zero3";
Addsimps [cos_arg_i_mult_zero3];

(*---------------------------------------------------------------------------*)
(* Finally! Polar form for complex numbers                                   *) 
(*---------------------------------------------------------------------------*)

Goal "EX r a. z = complex_of_real r * \
\     (complex_of_real(cos a) + ii * complex_of_real(sin a))";
by (cut_inst_tac [("z","z")] complex_split 1);
by (auto_tac (claset(),simpset() addsimps [polar_Ex,
    complex_add_mult_distrib2,complex_of_real_mult] @ complex_mult_ac));
qed "complex_split_polar";

Goalw [rcis_def,cis_def] "EX r a. z = rcis r a";
by (rtac complex_split_polar 1);
qed "rcis_Ex";

Goal "Re(complex_of_real r * \
\     (complex_of_real(cos a) + ii * complex_of_real(sin a))) = r * cos a";
by (auto_tac (claset(),simpset() addsimps [complex_add_mult_distrib2,
    complex_of_real_mult] @ complex_mult_ac));
qed "Re_complex_polar";
Addsimps [Re_complex_polar];

Goalw [rcis_def,cis_def] "Re(rcis r a) = r * cos a";
by Auto_tac;
qed "Re_rcis";
Addsimps [Re_rcis];

Goal "Im(complex_of_real r * \
\     (complex_of_real(cos a) + ii * complex_of_real(sin a))) = r * sin a";
by (auto_tac (claset(),simpset() addsimps [complex_add_mult_distrib2,
    complex_of_real_mult] @ complex_mult_ac));
qed "Im_complex_polar";
Addsimps [Im_complex_polar];

Goalw [rcis_def,cis_def] "Im(rcis r a) = r * sin a";
by Auto_tac;
qed "Im_rcis";
Addsimps [Im_rcis];

Goal "cmod (complex_of_real r * \
\     (complex_of_real(cos a) + ii * complex_of_real(sin a))) = abs r";
by (auto_tac (claset(),simpset() addsimps [complex_add_mult_distrib2,
    cmod_i,complex_of_real_mult,real_add_mult_distrib2
    RS sym,realpow_mult]  @ complex_mult_ac@ real_mult_ac 
    delsimps [realpow_Suc]));
qed "complex_mod_complex_polar";
Addsimps [complex_mod_complex_polar];

Goalw [rcis_def,cis_def] "cmod(rcis r a) = abs r";
by Auto_tac;
qed "complex_mod_rcis";
Addsimps [complex_mod_rcis];

Goalw [cmod_def] "cmod z = sqrt (Re (z * cnj z))";
by (rtac (real_sqrt_eq_iff RS iffD2) 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult_cnj]));
qed "complex_mod_sqrt_Re_mult_cnj";

Goal "Re(cnj z) = Re z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_cnj]));
qed "complex_Re_cnj";
Addsimps [complex_Re_cnj];

Goal "Im(cnj z) = - Im z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_cnj]));
qed "complex_Im_cnj";
Addsimps [complex_Im_cnj];

Goal "Im (z * cnj z) = 0";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_cnj,complex_mult]));
qed "complex_In_mult_cnj_zero";
Addsimps [complex_In_mult_cnj_zero];

Goal "[| Im w = 0; Im z = 0 |] ==> Re(w * z) = Re(w) * Re(z)";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (res_inst_tac [("z","w")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult]));
qed "complex_Re_mult";

Goalw [complex_of_real_def] "Re (z * complex_of_real c) = Re(z) * c";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult]));
qed "complex_Re_mult_complex_of_real";
Addsimps [complex_Re_mult_complex_of_real];

Goalw [complex_of_real_def] "Im (z * complex_of_real c) = Im(z) * c";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult]));
qed "complex_Im_mult_complex_of_real";
Addsimps [complex_Im_mult_complex_of_real];

Goalw [complex_of_real_def] "Re (complex_of_real c * z) = c * Re(z)";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult]));
qed "complex_Re_mult_complex_of_real2";
Addsimps [complex_Re_mult_complex_of_real2];

Goalw [complex_of_real_def] "Im (complex_of_real c * z) = c * Im(z)";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult]));
qed "complex_Im_mult_complex_of_real2";
Addsimps [complex_Im_mult_complex_of_real2];

(*---------------------------------------------------------------------------*)
(*  (r1 * cis a) * (r2 * cis b) = r1 * r2 * cis (a + b)                      *) 
(*---------------------------------------------------------------------------*)

Goalw [rcis_def] "cis a = rcis 1 a";
by (Simp_tac 1);
qed "cis_rcis_eq";

Goalw [rcis_def,cis_def] 
  "rcis r1 a * rcis r2 b = rcis (r1*r2) (a + b)";
by (auto_tac (claset(),simpset() addsimps [cos_add,sin_add,
    complex_add_mult_distrib2,complex_add_mult_distrib]
     @ complex_mult_ac @ complex_add_ac));
by (auto_tac (claset(),simpset() addsimps [complex_add_mult_distrib2 RS sym,
    complex_mult_assoc RS sym,complex_of_real_mult,complex_of_real_add,
    complex_add_assoc RS sym,i_mult_eq] delsimps [i_mult_eq2]));
by (auto_tac (claset(),simpset() addsimps complex_add_ac));
by (auto_tac (claset(),simpset() addsimps [complex_add_assoc RS sym,
    complex_of_real_add,real_add_mult_distrib2,
    real_diff_def] @ real_mult_ac @ real_add_ac));
qed "rcis_mult";

Goal "cis a * cis b = cis (a + b)";
by (simp_tac (simpset() addsimps [cis_rcis_eq,rcis_mult]) 1);
qed "cis_mult";

Goalw [cis_def] "cis 0 = 1";
by Auto_tac;
qed "cis_zero";
Addsimps [cis_zero];

Goalw [cis_def] "cis 0 = complex_of_real 1";
by Auto_tac;
qed "cis_zero2";
Addsimps [cis_zero2];

Goalw [rcis_def] "rcis 0 a = 0";
by (Simp_tac 1);
qed "rcis_zero_mod";
Addsimps [rcis_zero_mod];

Goalw [rcis_def] "rcis r 0 = complex_of_real r";
by (Simp_tac 1);
qed "rcis_zero_arg";
Addsimps [rcis_zero_arg];

Goalw [complex_of_real_def,complex_one_def] 
   "complex_of_real (-(1::real)) = -(1::complex)";
by (simp_tac (simpset() addsimps [complex_minus]) 1);
qed "complex_of_real_minus_one";

Goal "ii * (ii * x) = - x";
by (simp_tac (simpset() addsimps [complex_mult_assoc RS sym]) 1);
qed "complex_i_mult_minus";
Addsimps [complex_i_mult_minus];

Goal "ii * ii * x = - x";
by (Simp_tac 1);
qed "complex_i_mult_minus2";
Addsimps [complex_i_mult_minus2];

Goalw [cis_def] 
   "cis (real (Suc n) * a) = cis a * cis (real n * a)";
by (auto_tac (claset(),simpset() addsimps [real_of_nat_Suc,
    real_add_mult_distrib,cos_add,sin_add,complex_add_mult_distrib,
    complex_add_mult_distrib2,complex_of_real_add,complex_of_real_mult] 
    @ complex_mult_ac @ complex_add_ac));
by (auto_tac (claset(),simpset() addsimps [complex_add_mult_distrib2 RS sym,
    complex_mult_assoc RS sym,i_mult_eq,complex_of_real_mult,
    complex_of_real_add,complex_add_assoc RS sym,complex_of_real_minus
    RS sym,real_diff_def] @ real_mult_ac delsimps [i_mult_eq2]));
qed "cis_real_of_nat_Suc_mult";

Goal "(cis a) ^ n = cis (real n * a)";
by (induct_tac "n" 1);
by (auto_tac (claset(),simpset() addsimps [cis_real_of_nat_Suc_mult]));
qed "DeMoivre";

Goalw [rcis_def] 
   "(rcis r a) ^ n = rcis (r ^ n) (real n * a)";
by (auto_tac (claset(),simpset() addsimps [complexpow_mult,
    DeMoivre,complex_of_real_pow]));
qed "DeMoivre2";

Goalw [cis_def] "inverse(cis a) = cis (-a)";
by (auto_tac (claset(),simpset() addsimps [complex_inverse_complex_split,
    complex_of_real_minus,complex_diff_def]));
qed "cis_inverse";
Addsimps [cis_inverse];

Goal "inverse(rcis r a) = rcis (1/r) (-a)";
by (real_div_undefined_case_tac "r=0" 1);
by (simp_tac (simpset() addsimps [rename_numerals DIVISION_BY_ZERO,
    COMPLEX_INVERSE_ZERO]) 1);
by (auto_tac (claset(),simpset() addsimps [complex_inverse_complex_split,
    complex_add_mult_distrib2,complex_of_real_mult,rcis_def,cis_def,
    realpow_num_two] @ complex_mult_ac @ real_mult_ac));
by (auto_tac (claset(),simpset() addsimps [real_add_mult_distrib2 RS sym,
    complex_of_real_minus,complex_diff_def]));
qed "rcis_inverse";

Goalw [complex_divide_def] "cis a / cis b = cis (a - b)";
by (auto_tac (claset(),simpset() addsimps [cis_mult,real_diff_def]));
qed "cis_divide";

Goalw [complex_divide_def]
 "rcis r1 a / rcis r2 b = rcis (r1/r2) (a - b)";
by (real_div_undefined_case_tac "r2=0" 1);
by (simp_tac (simpset() addsimps [rename_numerals DIVISION_BY_ZERO,
    COMPLEX_INVERSE_ZERO]) 1);
by (auto_tac (claset(),simpset() addsimps [rcis_inverse,rcis_mult,
    real_diff_def]));
qed "rcis_divide";

Goalw [cis_def] "Re(cis a) = cos a";
by Auto_tac;
qed "Re_cis";
Addsimps [Re_cis];

Goalw [cis_def] "Im(cis a) = sin a";
by Auto_tac;
qed "Im_cis";
Addsimps [Im_cis];

Goal "cos (real n * a) = Re(cis a ^ n)";
by (auto_tac (claset(),simpset() addsimps [DeMoivre]));
qed "cos_n_Re_cis_pow_n";
 
Goal "sin (real n * a) = Im(cis a ^ n)";
by (auto_tac (claset(),simpset() addsimps [DeMoivre]));
qed "sin_n_Im_cis_pow_n";

Goalw [expi_def,cis_def]
    "expi (ii * complex_of_real y) = \
\    complex_of_real (cos y) + ii * complex_of_real (sin y)";
by Auto_tac;
qed "expi_Im_split";

Goalw [expi_def]
    "expi (ii * complex_of_real y) = cis y";
by Auto_tac;
qed "expi_Im_cis";

Goalw [expi_def] "expi(a + b) = expi(a) * expi(b)";
by (auto_tac (claset(),simpset() addsimps [complex_Re_add,exp_add,
    complex_Im_add,cis_mult RS sym,complex_of_real_mult] @
    complex_mult_ac));
qed "expi_add";

Goalw [expi_def] 
     "expi(complex_of_real x + ii * complex_of_real y) = \
\     complex_of_real (exp(x)) * cis y";
by Auto_tac;
qed "expi_complex_split";

Goalw [expi_def] "expi (0::complex) = 1";
by Auto_tac;
qed "expi_zero";
Addsimps [expi_zero];

goal Complex.thy 
     "Re (w * z) = Re w * Re z - Im w * Im z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (res_inst_tac [("z","w")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult]));
qed "complex_Re_mult_eq";

goal Complex.thy 
     "Im (w * z) = Re w * Im z + Im w * Re z";
by (res_inst_tac [("z","z")] eq_Abs_complex 1);
by (res_inst_tac [("z","w")] eq_Abs_complex 1);
by (auto_tac (claset(),simpset() addsimps [complex_mult]));
qed "complex_Im_mult_eq";

goal Complex.thy 
   "EX a r. z = complex_of_real r * expi a";
by (cut_inst_tac [("z","z")] rcis_Ex 1);
by (auto_tac (claset(),simpset() addsimps [expi_def,rcis_def,
    complex_mult_assoc RS sym,complex_of_real_mult]));
by (res_inst_tac [("x","ii * complex_of_real a")] exI 1);
by Auto_tac;
qed "complex_expi_Ex";


(****
Goal "[| - pi < a; a <= pi |] ==> (-pi < a & a <= 0) | (0 <= a & a <= pi)";
by Auto_tac;
qed "lemma_split_interval";

Goalw [arg_def] 
  "[| r ~= 0; - pi < a; a <= pi |] \
\  ==> arg(complex_of_real r * \
\      (complex_of_real(cos a) + ii * complex_of_real(sin a))) = a";
by Auto_tac;
by (cut_inst_tac [("R1.0","0"),("R2.0","r")] real_linear 1);
by (auto_tac (claset(),simpset() addsimps (map (full_rename_numerals thy)
    [rabs_eqI2,rabs_minus_eqI2,real_minus_rinv]) @ [real_divide_def,
    real_minus_mult_eq2 RS sym] @ real_mult_ac));
by (auto_tac (claset(),simpset() addsimps [real_mult_assoc RS sym]));
by (dtac lemma_split_interval 1 THEN Step_tac 1);
****)

