(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOL4Real imports HOL4Base begin

setup_theory "~~/src/HOL/Import/HOL" realax

lemma HREAL_RDISTRIB: "hreal_mul (hreal_add x y) z = hreal_add (hreal_mul x z) (hreal_mul y z)"
  by (import realax HREAL_RDISTRIB)

lemma HREAL_EQ_ADDL: "x ~= hreal_add x y"
  by (import realax HREAL_EQ_ADDL)

lemma HREAL_EQ_LADD: "(hreal_add x y = hreal_add x z) = (y = z)"
  by (import realax HREAL_EQ_LADD)

lemma HREAL_LT_REFL: "~ hreal_lt x x"
  by (import realax HREAL_LT_REFL)

lemma HREAL_LT_ADDL: "hreal_lt x (hreal_add x y)"
  by (import realax HREAL_LT_ADDL)

lemma HREAL_LT_NE: "hreal_lt x y ==> x ~= y"
  by (import realax HREAL_LT_NE)

lemma HREAL_LT_ADDR: "~ hreal_lt (hreal_add x y) x"
  by (import realax HREAL_LT_ADDR)

lemma HREAL_LT_GT: "hreal_lt x y ==> ~ hreal_lt y x"
  by (import realax HREAL_LT_GT)

lemma HREAL_LT_ADD2: "hreal_lt x1 y1 & hreal_lt x2 y2
==> hreal_lt (hreal_add x1 x2) (hreal_add y1 y2)"
  by (import realax HREAL_LT_ADD2)

lemma HREAL_LT_LADD: "hreal_lt (hreal_add x y) (hreal_add x z) = hreal_lt y z"
  by (import realax HREAL_LT_LADD)

definition
  treal_0 :: "hreal * hreal"  where
  "treal_0 == (hreal_1, hreal_1)"

lemma treal_0: "treal_0 = (hreal_1, hreal_1)"
  by (import realax treal_0)

definition
  treal_1 :: "hreal * hreal"  where
  "treal_1 == (hreal_add hreal_1 hreal_1, hreal_1)"

lemma treal_1: "treal_1 = (hreal_add hreal_1 hreal_1, hreal_1)"
  by (import realax treal_1)

definition
  treal_neg :: "hreal * hreal => hreal * hreal"  where
  "treal_neg == %(x, y). (y, x)"

lemma treal_neg: "treal_neg (x, y) = (y, x)"
  by (import realax treal_neg)

definition
  treal_add :: "hreal * hreal => hreal * hreal => hreal * hreal"  where
  "treal_add == %(x1, y1) (x2, y2). (hreal_add x1 x2, hreal_add y1 y2)"

lemma treal_add: "treal_add (x1, y1) (x2, y2) = (hreal_add x1 x2, hreal_add y1 y2)"
  by (import realax treal_add)

definition
  treal_mul :: "hreal * hreal => hreal * hreal => hreal * hreal"  where
  "treal_mul ==
%(x1, y1) (x2, y2).
   (hreal_add (hreal_mul x1 x2) (hreal_mul y1 y2),
    hreal_add (hreal_mul x1 y2) (hreal_mul y1 x2))"

lemma treal_mul: "treal_mul (x1, y1) (x2, y2) =
(hreal_add (hreal_mul x1 x2) (hreal_mul y1 y2),
 hreal_add (hreal_mul x1 y2) (hreal_mul y1 x2))"
  by (import realax treal_mul)

definition
  treal_lt :: "hreal * hreal => hreal * hreal => bool"  where
  "treal_lt == %(x1, y1) (x2, y2). hreal_lt (hreal_add x1 y2) (hreal_add x2 y1)"

lemma treal_lt: "treal_lt (x1, y1) (x2, y2) = hreal_lt (hreal_add x1 y2) (hreal_add x2 y1)"
  by (import realax treal_lt)

definition
  treal_inv :: "hreal * hreal => hreal * hreal"  where
  "treal_inv ==
%(x, y).
   if x = y then treal_0
   else if hreal_lt y x
        then (hreal_add (hreal_inv (hreal_sub x y)) hreal_1, hreal_1)
        else (hreal_1, hreal_add (hreal_inv (hreal_sub y x)) hreal_1)"

lemma treal_inv: "treal_inv (x, y) =
(if x = y then treal_0
 else if hreal_lt y x
      then (hreal_add (hreal_inv (hreal_sub x y)) hreal_1, hreal_1)
      else (hreal_1, hreal_add (hreal_inv (hreal_sub y x)) hreal_1))"
  by (import realax treal_inv)

definition
  treal_eq :: "hreal * hreal => hreal * hreal => bool"  where
  "treal_eq == %(x1, y1) (x2, y2). hreal_add x1 y2 = hreal_add x2 y1"

lemma treal_eq: "treal_eq (x1, y1) (x2, y2) = (hreal_add x1 y2 = hreal_add x2 y1)"
  by (import realax treal_eq)

lemma TREAL_EQ_REFL: "treal_eq x x"
  by (import realax TREAL_EQ_REFL)

lemma TREAL_EQ_SYM: "treal_eq x y = treal_eq y x"
  by (import realax TREAL_EQ_SYM)

lemma TREAL_EQ_TRANS: "treal_eq x y & treal_eq y z ==> treal_eq x z"
  by (import realax TREAL_EQ_TRANS)

lemma TREAL_EQ_EQUIV: "treal_eq p q = (treal_eq p = treal_eq q)"
  by (import realax TREAL_EQ_EQUIV)

lemma TREAL_EQ_AP: "p = q ==> treal_eq p q"
  by (import realax TREAL_EQ_AP)

lemma TREAL_10: "~ treal_eq treal_1 treal_0"
  by (import realax TREAL_10)

lemma TREAL_ADD_SYM: "treal_add x y = treal_add y x"
  by (import realax TREAL_ADD_SYM)

lemma TREAL_MUL_SYM: "treal_mul x y = treal_mul y x"
  by (import realax TREAL_MUL_SYM)

lemma TREAL_ADD_ASSOC: "treal_add x (treal_add y z) = treal_add (treal_add x y) z"
  by (import realax TREAL_ADD_ASSOC)

lemma TREAL_MUL_ASSOC: "treal_mul x (treal_mul y z) = treal_mul (treal_mul x y) z"
  by (import realax TREAL_MUL_ASSOC)

lemma TREAL_LDISTRIB: "treal_mul x (treal_add y z) = treal_add (treal_mul x y) (treal_mul x z)"
  by (import realax TREAL_LDISTRIB)

lemma TREAL_ADD_LID: "treal_eq (treal_add treal_0 x) x"
  by (import realax TREAL_ADD_LID)

lemma TREAL_MUL_LID: "treal_eq (treal_mul treal_1 x) x"
  by (import realax TREAL_MUL_LID)

lemma TREAL_ADD_LINV: "treal_eq (treal_add (treal_neg x) x) treal_0"
  by (import realax TREAL_ADD_LINV)

lemma TREAL_INV_0: "treal_eq (treal_inv treal_0) treal_0"
  by (import realax TREAL_INV_0)

lemma TREAL_MUL_LINV: "~ treal_eq x treal_0 ==> treal_eq (treal_mul (treal_inv x) x) treal_1"
  by (import realax TREAL_MUL_LINV)

lemma TREAL_LT_TOTAL: "treal_eq x y | treal_lt x y | treal_lt y x"
  by (import realax TREAL_LT_TOTAL)

lemma TREAL_LT_REFL: "~ treal_lt x x"
  by (import realax TREAL_LT_REFL)

lemma TREAL_LT_TRANS: "treal_lt x y & treal_lt y z ==> treal_lt x z"
  by (import realax TREAL_LT_TRANS)

lemma TREAL_LT_ADD: "treal_lt y z ==> treal_lt (treal_add x y) (treal_add x z)"
  by (import realax TREAL_LT_ADD)

lemma TREAL_LT_MUL: "treal_lt treal_0 x & treal_lt treal_0 y ==> treal_lt treal_0 (treal_mul x y)"
  by (import realax TREAL_LT_MUL)

definition
  treal_of_hreal :: "hreal => hreal * hreal"  where
  "treal_of_hreal == %x. (hreal_add x hreal_1, hreal_1)"

lemma treal_of_hreal: "treal_of_hreal x = (hreal_add x hreal_1, hreal_1)"
  by (import realax treal_of_hreal)

definition
  hreal_of_treal :: "hreal * hreal => hreal"  where
  "hreal_of_treal == %(x, y). SOME d. x = hreal_add y d"

lemma hreal_of_treal: "hreal_of_treal (x, y) = (SOME d. x = hreal_add y d)"
  by (import realax hreal_of_treal)

lemma TREAL_BIJ: "(ALL h. hreal_of_treal (treal_of_hreal h) = h) &
(ALL r. treal_lt treal_0 r = treal_eq (treal_of_hreal (hreal_of_treal r)) r)"
  by (import realax TREAL_BIJ)

lemma TREAL_ISO: "hreal_lt h i ==> treal_lt (treal_of_hreal h) (treal_of_hreal i)"
  by (import realax TREAL_ISO)

lemma TREAL_BIJ_WELLDEF: "treal_eq h i ==> hreal_of_treal h = hreal_of_treal i"
  by (import realax TREAL_BIJ_WELLDEF)

lemma TREAL_NEG_WELLDEF: "treal_eq x1 x2 ==> treal_eq (treal_neg x1) (treal_neg x2)"
  by (import realax TREAL_NEG_WELLDEF)

lemma TREAL_ADD_WELLDEFR: "treal_eq x1 x2 ==> treal_eq (treal_add x1 y) (treal_add x2 y)"
  by (import realax TREAL_ADD_WELLDEFR)

lemma TREAL_ADD_WELLDEF: "treal_eq x1 x2 & treal_eq y1 y2
==> treal_eq (treal_add x1 y1) (treal_add x2 y2)"
  by (import realax TREAL_ADD_WELLDEF)

lemma TREAL_MUL_WELLDEFR: "treal_eq x1 x2 ==> treal_eq (treal_mul x1 y) (treal_mul x2 y)"
  by (import realax TREAL_MUL_WELLDEFR)

lemma TREAL_MUL_WELLDEF: "treal_eq x1 x2 & treal_eq y1 y2
==> treal_eq (treal_mul x1 y1) (treal_mul x2 y2)"
  by (import realax TREAL_MUL_WELLDEF)

lemma TREAL_LT_WELLDEFR: "treal_eq x1 x2 ==> treal_lt x1 y = treal_lt x2 y"
  by (import realax TREAL_LT_WELLDEFR)

lemma TREAL_LT_WELLDEFL: "treal_eq y1 y2 ==> treal_lt x y1 = treal_lt x y2"
  by (import realax TREAL_LT_WELLDEFL)

lemma TREAL_LT_WELLDEF: "treal_eq x1 x2 & treal_eq y1 y2 ==> treal_lt x1 y1 = treal_lt x2 y2"
  by (import realax TREAL_LT_WELLDEF)

lemma TREAL_INV_WELLDEF: "treal_eq x1 x2 ==> treal_eq (treal_inv x1) (treal_inv x2)"
  by (import realax TREAL_INV_WELLDEF)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" real

lemma REAL_0: "(0::real) = (0::real)"
  by (import real REAL_0)

lemma REAL_1: "(1::real) = (1::real)"
  by (import real REAL_1)

lemma REAL_ADD_LID_UNIQ: "((x::real) + (y::real) = y) = (x = (0::real))"
  by (import real REAL_ADD_LID_UNIQ)

lemma REAL_ADD_RID_UNIQ: "((x::real) + (y::real) = x) = (y = (0::real))"
  by (import real REAL_ADD_RID_UNIQ)

lemma REAL_LT_ANTISYM: "~ ((x::real) < (y::real) & y < x)"
  by (import real REAL_LT_ANTISYM)

lemma REAL_LTE_TOTAL: "(x::real) < (y::real) | y <= x"
  by (import real REAL_LTE_TOTAL)

lemma REAL_LET_ANTISYM: "~ ((x::real) < (y::real) & y <= x)"
  by (import real REAL_LET_ANTISYM)

lemma REAL_LTE_ANTSYM: "~ ((x::real) <= (y::real) & y < x)"
  by (import real REAL_LTE_ANTSYM)

lemma REAL_LT_NEGTOTAL: "(x::real) = (0::real) | (0::real) < x | (0::real) < - x"
  by (import real REAL_LT_NEGTOTAL)

lemma REAL_LE_NEGTOTAL: "(0::real) <= (x::real) | (0::real) <= - x"
  by (import real REAL_LE_NEGTOTAL)

lemma REAL_LT_ADDNEG: "((y::real) < (x::real) + - (z::real)) = (y + z < x)"
  by (import real REAL_LT_ADDNEG)

lemma REAL_LT_ADDNEG2: "((x::real) + - (y::real) < (z::real)) = (x < z + y)"
  by (import real REAL_LT_ADDNEG2)

lemma REAL_LT_ADD1: "(x::real) <= (y::real) ==> x < y + (1::real)"
  by (import real REAL_LT_ADD1)

lemma REAL_SUB_ADD2: "(y::real) + ((x::real) - y) = x"
  by (import real REAL_SUB_ADD2)

lemma REAL_SUB_LT: "((0::real) < (x::real) - (y::real)) = (y < x)"
  by (import real REAL_SUB_LT)

lemma REAL_SUB_LE: "((0::real) <= (x::real) - (y::real)) = (y <= x)"
  by (import real REAL_SUB_LE)

lemma REAL_ADD_SUB: "(x::real) + (y::real) - x = y"
  by (import real REAL_ADD_SUB)

lemma REAL_NEG_EQ: "(- (x::real) = (y::real)) = (x = - y)"
  by (import real REAL_NEG_EQ)

lemma REAL_LT_LMUL_0: "(0::real) < (x::real) ==> ((0::real) < x * (y::real)) = ((0::real) < y)"
  by (import real REAL_LT_LMUL_0)

lemma REAL_LT_RMUL_0: "(0::real) < (y::real) ==> ((0::real) < (x::real) * y) = ((0::real) < x)"
  by (import real REAL_LT_RMUL_0)

lemma REAL_LINV_UNIQ: "(x::real) * (y::real) = (1::real) ==> x = inverse y"
  by (import real REAL_LINV_UNIQ)

lemma REAL_LE_INV: "(0::real) <= (x::real) ==> (0::real) <= inverse x"
  by (import real REAL_LE_INV)

lemma REAL_LE_ADDR: "((x::real) <= x + (y::real)) = ((0::real) <= y)"
  by (import real REAL_LE_ADDR)

lemma REAL_LE_ADDL: "((y::real) <= (x::real) + y) = ((0::real) <= x)"
  by (import real REAL_LE_ADDL)

lemma REAL_LT_ADDR: "((x::real) < x + (y::real)) = ((0::real) < y)"
  by (import real REAL_LT_ADDR)

lemma REAL_LT_ADDL: "((y::real) < (x::real) + y) = ((0::real) < x)"
  by (import real REAL_LT_ADDL)

lemma REAL_LT_NZ: "(real (n::nat) ~= (0::real)) = ((0::real) < real n)"
  by (import real REAL_LT_NZ)

lemma REAL_NZ_IMP_LT: "(n::nat) ~= (0::nat) ==> (0::real) < real n"
  by (import real REAL_NZ_IMP_LT)

lemma REAL_LT_RDIV_0: "(0::real) < (z::real) ==> ((0::real) < (y::real) / z) = ((0::real) < y)"
  by (import real REAL_LT_RDIV_0)

lemma REAL_LT_RDIV: "(0::real) < (z::real) ==> ((x::real) / z < (y::real) / z) = (x < y)"
  by (import real REAL_LT_RDIV)

lemma REAL_LT_FRACTION_0: "(n::nat) ~= (0::nat) ==> ((0::real) < (d::real) / real n) = ((0::real) < d)"
  by (import real REAL_LT_FRACTION_0)

lemma REAL_LT_MULTIPLE: "(1::nat) < (x::nat) ==> ((xa::real) < real x * xa) = ((0::real) < xa)"
  by (import real REAL_LT_MULTIPLE)

lemma REAL_LT_FRACTION: "(1::nat) < (n::nat) ==> ((d::real) / real n < d) = ((0::real) < d)"
  by (import real REAL_LT_FRACTION)

lemma REAL_LT_HALF2: "((d::real) / (2::real) < d) = ((0::real) < d)"
  by (import real REAL_LT_HALF2)

lemma REAL_DIV_LMUL: "(y::real) ~= (0::real) ==> y * ((x::real) / y) = x"
  by (import real REAL_DIV_LMUL)

lemma REAL_DIV_RMUL: "(y::real) ~= (0::real) ==> (x::real) / y * y = x"
  by (import real REAL_DIV_RMUL)

lemma REAL_DOWN: "(0::real) < (x::real) ==> EX xa>0::real. xa < x"
  by (import real REAL_DOWN)

lemma REAL_SUB_SUB: "(x::real) - (y::real) - x = - y"
  by (import real REAL_SUB_SUB)

lemma REAL_SUB_LNEG: "- (x::real) - (y::real) = - (x + y)"
  by (import real REAL_SUB_LNEG)

lemma REAL_SUB_NEG2: "- (x::real) - - (y::real) = y - x"
  by (import real REAL_SUB_NEG2)

lemma REAL_SUB_TRIANGLE: "(a::real) - (b::real) + (b - (c::real)) = a - c"
  by (import real REAL_SUB_TRIANGLE)

lemma REAL_INV_MUL: "(x::real) ~= (0::real) & (y::real) ~= (0::real)
==> inverse (x * y) = inverse x * inverse y"
  by (import real REAL_INV_MUL)

lemma REAL_SUB_INV2: "(x::real) ~= (0::real) & (y::real) ~= (0::real)
==> inverse x - inverse y = (y - x) / (x * y)"
  by (import real REAL_SUB_INV2)

lemma REAL_SUB_SUB2: "(x::real) - (x - (y::real)) = y"
  by (import real REAL_SUB_SUB2)

lemma REAL_ADD_SUB2: "(x::real) - (x + (y::real)) = - y"
  by (import real REAL_ADD_SUB2)

lemma REAL_LE_DIV: "(0::real) <= (x::real) & (0::real) <= (xa::real) ==> (0::real) <= x / xa"
  by (import real REAL_LE_DIV)

lemma REAL_LT_1: "(0::real) <= (x::real) & x < (y::real) ==> x / y < (1::real)"
  by (import real REAL_LT_1)

lemma REAL_POS_NZ: "(0::real) < (x::real) ==> x ~= (0::real)"
  by (import real REAL_POS_NZ)

lemma REAL_EQ_RMUL_IMP: "(z::real) ~= (0::real) & (x::real) * z = (y::real) * z ==> x = y"
  by (import real REAL_EQ_RMUL_IMP)

lemma REAL_EQ_LMUL_IMP: "(x::real) ~= (0::real) & x * (xa::real) = x * (xb::real) ==> xa = xb"
  by (import real REAL_EQ_LMUL_IMP)

lemma REAL_FACT_NZ: "real (FACT n) ~= 0"
  by (import real REAL_FACT_NZ)

lemma REAL_POASQ: "((0::real) < (x::real) * x) = (x ~= (0::real))"
  by (import real REAL_POASQ)

lemma REAL_DIV_MUL2: "(x::real) ~= (0::real) & (z::real) ~= (0::real)
==> (y::real) / z = x * y / (x * z)"
  by (import real REAL_DIV_MUL2)

lemma REAL_MIDDLE1: "(a::real) <= (b::real) ==> a <= (a + b) / (2::real)"
  by (import real REAL_MIDDLE1)

lemma REAL_MIDDLE2: "(a::real) <= (b::real) ==> (a + b) / (2::real) <= b"
  by (import real REAL_MIDDLE2)

lemma ABS_LT_MUL2: "abs (w::real) < (y::real) & abs (x::real) < (z::real)
==> abs (w * x) < y * z"
  by (import real ABS_LT_MUL2)

lemma ABS_REFL: "(abs (x::real) = x) = ((0::real) <= x)"
  by (import real ABS_REFL)

lemma ABS_BETWEEN: "((0::real) < (d::real) & (x::real) - d < (y::real) & y < x + d) =
(abs (y - x) < d)"
  by (import real ABS_BETWEEN)

lemma ABS_BOUND: "abs ((x::real) - (y::real)) < (d::real) ==> y < x + d"
  by (import real ABS_BOUND)

lemma ABS_STILLNZ: "abs ((x::real) - (y::real)) < abs y ==> x ~= (0::real)"
  by (import real ABS_STILLNZ)

lemma ABS_CASES: "(x::real) = (0::real) | (0::real) < abs x"
  by (import real ABS_CASES)

lemma ABS_BETWEEN1: "(x::real) < (z::real) & abs ((y::real) - x) < z - x ==> y < z"
  by (import real ABS_BETWEEN1)

lemma ABS_SIGN: "abs ((x::real) - (y::real)) < y ==> (0::real) < x"
  by (import real ABS_SIGN)

lemma ABS_SIGN2: "abs ((x::real) - (y::real)) < - y ==> x < (0::real)"
  by (import real ABS_SIGN2)

lemma ABS_CIRCLE: "abs (h::real) < abs (y::real) - abs (x::real) ==> abs (x + h) < abs y"
  by (import real ABS_CIRCLE)

lemma ABS_BETWEEN2: "(x0::real) < (y0::real) &
abs ((x::real) - x0) < (y0 - x0) / (2::real) &
abs ((y::real) - y0) < (y0 - x0) / (2::real)
==> x < y"
  by (import real ABS_BETWEEN2)

lemma POW_PLUS1: "0 < e ==> 1 + real n * e <= (1 + e) ^ n"
  by (import real POW_PLUS1)

lemma POW_M1: "abs ((- (1::real)) ^ (n::nat)) = (1::real)"
  by (import real POW_M1)

lemma REAL_LE1_POW2: "(1::real) <= (x::real) ==> (1::real) <= x ^ (2::nat)"
  by (import real REAL_LE1_POW2)

lemma REAL_LT1_POW2: "(1::real) < (x::real) ==> (1::real) < x ^ (2::nat)"
  by (import real REAL_LT1_POW2)

lemma POW_POS_LT: "(0::real) < (x::real) ==> (0::real) < x ^ Suc (n::nat)"
  by (import real POW_POS_LT)

lemma POW_LT: "(0::real) <= (x::real) & x < (y::real) ==> x ^ Suc (n::nat) < y ^ Suc n"
  by (import real POW_LT)

lemma POW_ZERO: "(x::real) ^ (n::nat) = (0::real) ==> x = (0::real)"
  by (import real POW_ZERO)

lemma POW_ZERO_EQ: "((x::real) ^ Suc (n::nat) = (0::real)) = (x = (0::real))"
  by (import real POW_ZERO_EQ)

lemma REAL_POW_LT2: "(n::nat) ~= (0::nat) & (0::real) <= (x::real) & x < (y::real)
==> x ^ n < y ^ n"
  by (import real REAL_POW_LT2)

lemma REAL_POW_MONO_LT: "(1::real) < (x::real) & (m::nat) < (n::nat) ==> x ^ m < x ^ n"
  by (import real REAL_POW_MONO_LT)

lemma REAL_SUP_SOMEPOS: "(EX x::real. (P::real => bool) x & (0::real) < x) &
(EX z::real. ALL x::real. P x --> x < z)
==> EX s::real. ALL y::real. (EX x::real. P x & y < x) = (y < s)"
  by (import real REAL_SUP_SOMEPOS)

lemma SUP_LEMMA1: "(!!y::real.
    (EX x::real. (P::real => bool) (x + (d::real)) & y < x) =
    (y < (s::real)))
==> (EX x::real. P x & (y::real) < x) = (y < s + d)"
  by (import real SUP_LEMMA1)

lemma SUP_LEMMA2: "Ex (P::real => bool) ==> EX (d::real) x::real. P (x + d) & (0::real) < x"
  by (import real SUP_LEMMA2)

lemma SUP_LEMMA3: "EX z::real. ALL x::real. (P::real => bool) x --> x < z
==> EX x::real. ALL xa::real. P (xa + (d::real)) --> xa < x"
  by (import real SUP_LEMMA3)

lemma REAL_SUP_EXISTS: "Ex (P::real => bool) & (EX z::real. ALL x::real. P x --> x < z)
==> EX x::real. ALL y::real. (EX x::real. P x & y < x) = (y < x)"
  by (import real REAL_SUP_EXISTS)

consts
  sup :: "(real => bool) => real" 

defs
  sup_def: "real.sup == %P. SOME s. ALL y. (EX x. P x & y < x) = (y < s)"

lemma sup: "real.sup P = (SOME s. ALL y. (EX x. P x & y < x) = (y < s))"
  by (import real sup)

lemma REAL_SUP: "Ex P & (EX z. ALL x. P x --> x < z)
==> (EX x. P x & y < x) = (y < real.sup P)"
  by (import real REAL_SUP)

lemma REAL_SUP_UBOUND: "[| Ex P & (EX z. ALL x. P x --> x < z); P y |] ==> y <= real.sup P"
  by (import real REAL_SUP_UBOUND)

lemma SETOK_LE_LT: "(Ex (P::real => bool) & (EX z::real. ALL x::real. P x --> x <= z)) =
(Ex P & (EX z::real. ALL x::real. P x --> x < z))"
  by (import real SETOK_LE_LT)

lemma REAL_SUP_LE: "Ex P & (EX z. ALL x. P x --> x <= z)
==> (EX x. P x & y < x) = (y < real.sup P)"
  by (import real REAL_SUP_LE)

lemma REAL_SUP_UBOUND_LE: "[| Ex P & (EX z. ALL x. P x --> x <= z); P y |] ==> y <= real.sup P"
  by (import real REAL_SUP_UBOUND_LE)

consts
  sumc :: "nat => nat => (nat => real) => real" 

specification (sumc) sumc: "(ALL n f. sumc n 0 f = 0) &
(ALL n m f. sumc n (Suc m) f = sumc n m f + f (n + m))"
  by (import real sumc)

consts
  sum :: "nat * nat => (nat => real) => real" 

defs
  sum_def: "real.sum == %(x, y). sumc x y"

lemma SUM_DEF: "real.sum (m, n) f = sumc m n f"
  by (import real SUM_DEF)

lemma sum: "real.sum (xa, 0) x = 0 &
real.sum (xa, Suc xb) x = real.sum (xa, xb) x + x (xa + xb)"
  by (import real sum)

lemma SUM_TWO: "real.sum (0, n) f + real.sum (n, p) f = real.sum (0, n + p) f"
  by (import real SUM_TWO)

lemma SUM_DIFF: "real.sum (m, n) f = real.sum (0, m + n) f - real.sum (0, m) f"
  by (import real SUM_DIFF)

lemma ABS_SUM: "abs (real.sum (m, n) f) <= real.sum (m, n) (%n. abs (f n))"
  by (import real ABS_SUM)

lemma SUM_LE: "(!!r. m <= r & r < n + m ==> f r <= g r)
==> real.sum (m, n) f <= real.sum (m, n) g"
  by (import real SUM_LE)

lemma SUM_EQ: "(!!r. m <= r & r < n + m ==> f r = g r)
==> real.sum (m, n) f = real.sum (m, n) g"
  by (import real SUM_EQ)

lemma SUM_POS: "(!!n. 0 <= f n) ==> 0 <= real.sum (m, n) f"
  by (import real SUM_POS)

lemma SUM_POS_GEN: "(!!n. m <= n ==> 0 <= f n) ==> 0 <= real.sum (m, n) f"
  by (import real SUM_POS_GEN)

lemma SUM_ABS: "abs (real.sum (m, x) (%m. abs (f m))) = real.sum (m, x) (%m. abs (f m))"
  by (import real SUM_ABS)

lemma SUM_ABS_LE: "abs (real.sum (m, n) f) <= real.sum (m, n) (%n. abs (f n))"
  by (import real SUM_ABS_LE)

lemma SUM_ZERO: "[| !!n. N <= n ==> f n = 0; N <= m |] ==> real.sum (m, n) f = 0"
  by (import real SUM_ZERO)

lemma SUM_ADD: "real.sum (m, n) (%n. f n + g n) = real.sum (m, n) f + real.sum (m, n) g"
  by (import real SUM_ADD)

lemma SUM_CMUL: "real.sum (m, n) (%n. c * f n) = c * real.sum (m, n) f"
  by (import real SUM_CMUL)

lemma SUM_NEG: "real.sum (n, d) (%n. - f n) = - real.sum (n, d) f"
  by (import real SUM_NEG)

lemma SUM_SUB: "real.sum (m, n) (%x. f x - g x) = real.sum (m, n) f - real.sum (m, n) g"
  by (import real SUM_SUB)

lemma SUM_SUBST: "(!!p. m <= p & p < m + n ==> f p = g p)
==> real.sum (m, n) f = real.sum (m, n) g"
  by (import real SUM_SUBST)

lemma SUM_NSUB: "real.sum (0, n) f - real n * c = real.sum (0, n) (%p. f p - c)"
  by (import real SUM_NSUB)

lemma SUM_BOUND: "(!!p. m <= p & p < m + n ==> f p <= k) ==> real.sum (m, n) f <= real n * k"
  by (import real SUM_BOUND)

lemma SUM_GROUP: "real.sum (0, n) (%m. real.sum (m * k, k) f) = real.sum (0, n * k) f"
  by (import real SUM_GROUP)

lemma SUM_1: "real.sum (n, 1) f = f n"
  by (import real SUM_1)

lemma SUM_2: "real.sum (n, 2) f = f n + f (n + 1)"
  by (import real SUM_2)

lemma SUM_OFFSET: "real.sum (0, n) (%m. f (m + k)) = real.sum (0, n + k) f - real.sum (0, k) f"
  by (import real SUM_OFFSET)

lemma SUM_REINDEX: "real.sum (m + k, n) f = real.sum (m, n) (%r. f (r + k))"
  by (import real SUM_REINDEX)

lemma SUM_0: "real.sum (m, n) (%r. 0) = 0"
  by (import real SUM_0)

lemma SUM_PERMUTE_0: "(!!y. y < n ==> EX! x. x < n & p x = y)
==> real.sum (0, n) (%n. f (p n)) = real.sum (0, n) f"
  by (import real SUM_PERMUTE_0)

lemma SUM_CANCEL: "real.sum (n, d) (%n. f (Suc n) - f n) = f (n + d) - f n"
  by (import real SUM_CANCEL)

lemma REAL_LE_RNEG: "((x::real) <= - (y::real)) = (x + y <= (0::real))"
  by (import real REAL_LE_RNEG)

lemma REAL_EQ_RDIV_EQ: "(0::real) < (xb::real) ==> ((x::real) = (xa::real) / xb) = (x * xb = xa)"
  by (import real REAL_EQ_RDIV_EQ)

lemma REAL_EQ_LDIV_EQ: "(0::real) < (xb::real) ==> ((x::real) / xb = (xa::real)) = (x = xa * xb)"
  by (import real REAL_EQ_LDIV_EQ)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" topology

definition
  re_Union :: "(('a => bool) => bool) => 'a => bool"  where
  "re_Union == %P x. EX s. P s & s x"

lemma re_Union: "re_Union P = (%x. EX s. P s & s x)"
  by (import topology re_Union)

definition
  re_union :: "('a => bool) => ('a => bool) => 'a => bool"  where
  "re_union == %P Q x. P x | Q x"

lemma re_union: "re_union P Q = (%x. P x | Q x)"
  by (import topology re_union)

definition
  re_intersect :: "('a => bool) => ('a => bool) => 'a => bool"  where
  "re_intersect == %P Q x. P x & Q x"

lemma re_intersect: "re_intersect P Q = (%x. P x & Q x)"
  by (import topology re_intersect)

definition
  re_null :: "'a => bool"  where
  "re_null == %x. False"

lemma re_null: "re_null = (%x. False)"
  by (import topology re_null)

definition
  re_universe :: "'a => bool"  where
  "re_universe == %x. True"

lemma re_universe: "re_universe = (%x. True)"
  by (import topology re_universe)

definition
  re_subset :: "('a => bool) => ('a => bool) => bool"  where
  "re_subset == %P Q. ALL x. P x --> Q x"

lemma re_subset: "re_subset P Q = (ALL x. P x --> Q x)"
  by (import topology re_subset)

definition
  re_compl :: "('a => bool) => 'a => bool"  where
  "re_compl == %P x. ~ P x"

lemma re_compl: "re_compl P = (%x. ~ P x)"
  by (import topology re_compl)

lemma SUBSET_REFL: "re_subset P P"
  by (import topology SUBSET_REFL)

lemma COMPL_MEM: "P x = (~ re_compl P x)"
  by (import topology COMPL_MEM)

lemma SUBSET_ANTISYM: "(re_subset P Q & re_subset Q P) = (P = Q)"
  by (import topology SUBSET_ANTISYM)

lemma SUBSET_TRANS: "re_subset P Q & re_subset Q R ==> re_subset P R"
  by (import topology SUBSET_TRANS)

definition
  istopology :: "(('a => bool) => bool) => bool"  where
  "istopology ==
%L. L re_null &
    L re_universe &
    (ALL a b. L a & L b --> L (re_intersect a b)) &
    (ALL P. re_subset P L --> L (re_Union P))"

lemma istopology: "istopology L =
(L re_null &
 L re_universe &
 (ALL a b. L a & L b --> L (re_intersect a b)) &
 (ALL P. re_subset P L --> L (re_Union P)))"
  by (import topology istopology)

typedef (open) ('a) topology = "Collect istopology::(('a::type => bool) => bool) set"
  by (rule typedef_helper,import topology topology_TY_DEF)

lemmas topology_TY_DEF = typedef_hol2hol4 [OF type_definition_topology]

consts
  topology :: "(('a => bool) => bool) => 'a topology" 
  "open" :: "'a topology => ('a => bool) => bool" 

specification ("open" topology) topology_tybij: "(ALL a::'a topology. topology (topology.open a) = a) &
(ALL r::('a => bool) => bool.
    istopology r = (topology.open (topology r) = r))"
  by (import topology topology_tybij)

lemma TOPOLOGY: "topology.open L re_null &
topology.open L re_universe &
(ALL a b.
    topology.open L a & topology.open L b -->
    topology.open L (re_intersect a b)) &
(ALL P. re_subset P (topology.open L) --> topology.open L (re_Union P))"
  by (import topology TOPOLOGY)

lemma TOPOLOGY_UNION: "re_subset xa (topology.open x) ==> topology.open x (re_Union xa)"
  by (import topology TOPOLOGY_UNION)

definition
  neigh :: "'a topology => ('a => bool) * 'a => bool"  where
  "neigh == %tp (N, x). EX P. topology.open tp P & re_subset P N & P x"

lemma neigh: "neigh (tp::'a::type topology) (N::'a::type => bool, x::'a::type) =
(EX P::'a::type => bool. topology.open tp P & re_subset P N & P x)"
  by (import topology neigh)

lemma OPEN_OWN_NEIGH: "topology.open (tp::'a::type topology) (S'::'a::type => bool) &
S' (x::'a::type)
==> neigh tp (S', x)"
  by (import topology OPEN_OWN_NEIGH)

lemma OPEN_UNOPEN: "topology.open (tp::'a::type topology) (S'::'a::type => bool) =
(re_Union (%P::'a::type => bool. topology.open tp P & re_subset P S') = S')"
  by (import topology OPEN_UNOPEN)

lemma OPEN_SUBOPEN: "topology.open (tp::'a::type topology) (S'::'a::type => bool) =
(ALL x::'a::type.
    S' x -->
    (EX P::'a::type => bool. P x & topology.open tp P & re_subset P S'))"
  by (import topology OPEN_SUBOPEN)

lemma OPEN_NEIGH: "topology.open (tp::'a::type topology) (S'::'a::type => bool) =
(ALL x::'a::type.
    S' x --> (EX N::'a::type => bool. neigh tp (N, x) & re_subset N S'))"
  by (import topology OPEN_NEIGH)

consts
  closed :: "'a topology => ('a => bool) => bool" 

defs
  closed_def: "topology.closed == %L S'. topology.open L (re_compl S')"

lemma closed: "topology.closed L S' = topology.open L (re_compl S')"
  by (import topology closed)

definition
  limpt :: "'a topology => 'a => ('a => bool) => bool"  where
  "limpt == %tp x S'. ALL N. neigh tp (N, x) --> (EX y. x ~= y & S' y & N y)"

lemma limpt: "limpt (tp::'a::type topology) (x::'a::type) (S'::'a::type => bool) =
(ALL N::'a::type => bool.
    neigh tp (N, x) --> (EX y::'a::type. x ~= y & S' y & N y))"
  by (import topology limpt)

lemma CLOSED_LIMPT: "topology.closed (tp::'a::type topology) (S'::'a::type => bool) =
(ALL x::'a::type. limpt tp x S' --> S' x)"
  by (import topology CLOSED_LIMPT)

definition
  ismet :: "('a * 'a => real) => bool"  where
  "ismet ==
%m. (ALL x y. (m (x, y) = 0) = (x = y)) &
    (ALL x y z. m (y, z) <= m (x, y) + m (x, z))"

lemma ismet: "ismet m =
((ALL x y. (m (x, y) = 0) = (x = y)) &
 (ALL x y z. m (y, z) <= m (x, y) + m (x, z)))"
  by (import topology ismet)

typedef (open) ('a) metric = "Collect ismet :: ('a::type * 'a::type => real) set"
  by (rule typedef_helper,import topology metric_TY_DEF)

lemmas metric_TY_DEF = typedef_hol2hol4 [OF type_definition_metric]

consts
  metric :: "('a * 'a => real) => 'a metric" 
  dist :: "'a metric => 'a * 'a => real" 

specification (dist metric) metric_tybij: "(ALL a::'a metric. metric (topology.dist a) = a) &
(ALL r::'a * 'a => real. ismet r = (topology.dist (metric r) = r))"
  by (import topology metric_tybij)

lemma METRIC_ISMET: "ismet (topology.dist m)"
  by (import topology METRIC_ISMET)

lemma METRIC_ZERO: "(topology.dist m (x, y) = 0) = (x = y)"
  by (import topology METRIC_ZERO)

lemma METRIC_SAME: "topology.dist m (x, x) = 0"
  by (import topology METRIC_SAME)

lemma METRIC_POS: "0 <= topology.dist m (x, y)"
  by (import topology METRIC_POS)

lemma METRIC_SYM: "topology.dist m (x, y) = topology.dist m (y, x)"
  by (import topology METRIC_SYM)

lemma METRIC_TRIANGLE: "topology.dist m (x, z) <= topology.dist m (x, y) + topology.dist m (y, z)"
  by (import topology METRIC_TRIANGLE)

lemma METRIC_NZ: "x ~= y ==> 0 < topology.dist m (x, y)"
  by (import topology METRIC_NZ)

definition
  mtop :: "'a metric => 'a topology"  where
  "mtop ==
%m. topology
     (%S'. ALL x.
              S' x --> (EX e>0. ALL y. topology.dist m (x, y) < e --> S' y))"

lemma mtop: "mtop m =
topology
 (%S'. ALL x. S' x --> (EX e>0. ALL y. topology.dist m (x, y) < e --> S' y))"
  by (import topology mtop)

lemma mtop_istopology: "istopology
 (%S'. ALL x. S' x --> (EX e>0. ALL y. topology.dist m (x, y) < e --> S' y))"
  by (import topology mtop_istopology)

lemma MTOP_OPEN: "topology.open (mtop x) S' =
(ALL xa. S' xa --> (EX e>0. ALL y. topology.dist x (xa, y) < e --> S' y))"
  by (import topology MTOP_OPEN)

definition
  B :: "'a metric => 'a * real => 'a => bool"  where
  "B == %m (x, e) y. topology.dist m (x, y) < e"

lemma ball: "B m (x, e) = (%y. topology.dist m (x, y) < e)"
  by (import topology ball)

lemma BALL_OPEN: "0 < e ==> topology.open (mtop m) (B m (x, e))"
  by (import topology BALL_OPEN)

lemma BALL_NEIGH: "0 < e ==> neigh (mtop m) (B m (x, e), x)"
  by (import topology BALL_NEIGH)

lemma MTOP_LIMPT: "limpt (mtop m) x S' =
(ALL e>0. EX y. x ~= y & S' y & topology.dist m (x, y) < e)"
  by (import topology MTOP_LIMPT)

lemma ISMET_R1: "ismet (%(x, y). abs (y - x))"
  by (import topology ISMET_R1)

definition
  mr1 :: "real metric"  where
  "mr1 == metric (%(x, y). abs (y - x))"

lemma mr1: "mr1 = metric (%(x, y). abs (y - x))"
  by (import topology mr1)

lemma MR1_DEF: "topology.dist mr1 (x, y) = abs (y - x)"
  by (import topology MR1_DEF)

lemma MR1_ADD: "topology.dist mr1 (x, x + d) = abs d"
  by (import topology MR1_ADD)

lemma MR1_SUB: "topology.dist mr1 (x, x - d) = abs d"
  by (import topology MR1_SUB)

lemma MR1_ADD_POS: "0 <= d ==> topology.dist mr1 (x, x + d) = d"
  by (import topology MR1_ADD_POS)

lemma MR1_SUB_LE: "0 <= d ==> topology.dist mr1 (x, x - d) = d"
  by (import topology MR1_SUB_LE)

lemma MR1_ADD_LT: "0 < d ==> topology.dist mr1 (x, x + d) = d"
  by (import topology MR1_ADD_LT)

lemma MR1_SUB_LT: "0 < d ==> topology.dist mr1 (x, x - d) = d"
  by (import topology MR1_SUB_LT)

lemma MR1_BETWEEN1: "x < z & topology.dist mr1 (x, y) < z - x ==> y < z"
  by (import topology MR1_BETWEEN1)

lemma MR1_LIMPT: "limpt (mtop mr1) x re_universe"
  by (import topology MR1_LIMPT)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" nets

definition
  dorder :: "('a => 'a => bool) => bool"  where
  "dorder ==
%g. ALL x y.
       g x x & g y y --> (EX z. g z z & (ALL w. g w z --> g w x & g w y))"

lemma dorder: "dorder g =
(ALL x y.
    g x x & g y y --> (EX z. g z z & (ALL w. g w z --> g w x & g w y)))"
  by (import nets dorder)

definition
  tends :: "('b => 'a) => 'a => 'a topology * ('b => 'b => bool) => bool"  where
  "tends ==
%(s::'b => 'a) (l::'a) (tp::'a topology, g::'b => 'b => bool).
   ALL N::'a => bool.
      neigh tp (N, l) -->
      (EX n::'b. g n n & (ALL m::'b. g m n --> N (s m)))"

lemma tends: "tends (s::'b::type => 'a::type) (l::'a::type)
 (tp::'a::type topology, g::'b::type => 'b::type => bool) =
(ALL N::'a::type => bool.
    neigh tp (N, l) -->
    (EX n::'b::type. g n n & (ALL m::'b::type. g m n --> N (s m))))"
  by (import nets tends)

definition
  bounded :: "'a metric * ('b => 'b => bool) => ('b => 'a) => bool"  where
  "bounded ==
%(m, g) f. EX k x N. g N N & (ALL n. g n N --> topology.dist m (f n, x) < k)"

lemma bounded: "bounded (m, g) f =
(EX k x N. g N N & (ALL n. g n N --> topology.dist m (f n, x) < k))"
  by (import nets bounded)

consts
  tendsto :: "'a metric * 'a => 'a => 'a => bool" 

defs
  tendsto_def: "nets.tendsto ==
%(m, x) y z.
   0 < topology.dist m (x, y) &
   topology.dist m (x, y) <= topology.dist m (x, z)"

lemma tendsto: "nets.tendsto (m, x) y z =
(0 < topology.dist m (x, y) &
 topology.dist m (x, y) <= topology.dist m (x, z))"
  by (import nets tendsto)

lemma DORDER_LEMMA: "[| dorder g;
   (EX n. g n n & (ALL m. g m n --> P m)) &
   (EX n. g n n & (ALL m. g m n --> Q m)) |]
==> EX n. g n n & (ALL m. g m n --> P m & Q m)"
  by (import nets DORDER_LEMMA)

lemma DORDER_NGE: "dorder nat_ge"
  by (import nets DORDER_NGE)

lemma DORDER_TENDSTO: "dorder (nets.tendsto (m, x))"
  by (import nets DORDER_TENDSTO)

lemma MTOP_TENDS: "tends (x::'b => 'a) (x0::'a) (mtop (d::'a metric), g::'b => 'b => bool) =
(ALL e>0::real.
    EX n::'b. g n n & (ALL m::'b. g m n --> topology.dist d (x m, x0) < e))"
  by (import nets MTOP_TENDS)

lemma MTOP_TENDS_UNIQ: "[| dorder (g::'b => 'b => bool);
   tends (x::'b => 'a) (x0::'a) (mtop (d::'a metric), g) &
   tends x (x1::'a) (mtop d, g) |]
==> x0 = x1"
  by (import nets MTOP_TENDS_UNIQ)

lemma SEQ_TENDS: "tends x x0 (mtop d, nat_ge) =
(ALL xa>0. EX xb. ALL xc>=xb. topology.dist d (x xc, x0) < xa)"
  by (import nets SEQ_TENDS)

lemma LIM_TENDS: "limpt (mtop m1) x0 re_universe
==> tends f y0 (mtop m2, nets.tendsto (m1, x0)) =
    (ALL e>0.
        EX d>0.
           ALL x.
              0 < topology.dist m1 (x, x0) &
              topology.dist m1 (x, x0) <= d -->
              topology.dist m2 (f x, y0) < e)"
  by (import nets LIM_TENDS)

lemma LIM_TENDS2: "limpt (mtop m1) x0 re_universe
==> tends f y0 (mtop m2, nets.tendsto (m1, x0)) =
    (ALL e>0.
        EX d>0.
           ALL x.
              0 < topology.dist m1 (x, x0) &
              topology.dist m1 (x, x0) < d -->
              topology.dist m2 (f x, y0) < e)"
  by (import nets LIM_TENDS2)

lemma MR1_BOUNDED: "bounded (mr1, g) f = (EX k N. g N N & (ALL n. g n N --> abs (f n) < k))"
  by (import nets MR1_BOUNDED)

lemma NET_NULL: "tends x x0 (mtop mr1, g) = tends (%n. x n - x0) 0 (mtop mr1, g)"
  by (import nets NET_NULL)

lemma NET_CONV_BOUNDED: "tends x x0 (mtop mr1, g) ==> bounded (mr1, g) x"
  by (import nets NET_CONV_BOUNDED)

lemma NET_CONV_NZ: "tends x x0 (mtop mr1, g) & x0 ~= 0
==> EX N. g N N & (ALL n. g n N --> x n ~= 0)"
  by (import nets NET_CONV_NZ)

lemma NET_CONV_IBOUNDED: "tends x x0 (mtop mr1, g) & x0 ~= 0 ==> bounded (mr1, g) (%n. inverse (x n))"
  by (import nets NET_CONV_IBOUNDED)

lemma NET_NULL_ADD: "[| dorder g; tends x 0 (mtop mr1, g) & tends y 0 (mtop mr1, g) |]
==> tends (%n. x n + y n) 0 (mtop mr1, g)"
  by (import nets NET_NULL_ADD)

lemma NET_NULL_MUL: "[| dorder g; bounded (mr1, g) x & tends y 0 (mtop mr1, g) |]
==> tends (%n. x n * y n) 0 (mtop mr1, g)"
  by (import nets NET_NULL_MUL)

lemma NET_NULL_CMUL: "tends x 0 (mtop mr1, g) ==> tends (%n. k * x n) 0 (mtop mr1, g)"
  by (import nets NET_NULL_CMUL)

lemma NET_ADD: "[| dorder g; tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) |]
==> tends (%n. x n + y n) (x0 + y0) (mtop mr1, g)"
  by (import nets NET_ADD)

lemma NET_NEG: "dorder g
==> tends x x0 (mtop mr1, g) = tends (%n. - x n) (- x0) (mtop mr1, g)"
  by (import nets NET_NEG)

lemma NET_SUB: "[| dorder g; tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) |]
==> tends (%xa. x xa - y xa) (x0 - y0) (mtop mr1, g)"
  by (import nets NET_SUB)

lemma NET_MUL: "[| dorder g; tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) |]
==> tends (%n. x n * y n) (x0 * y0) (mtop mr1, g)"
  by (import nets NET_MUL)

lemma NET_INV: "[| dorder g; tends x x0 (mtop mr1, g) & x0 ~= 0 |]
==> tends (%n. inverse (x n)) (inverse x0) (mtop mr1, g)"
  by (import nets NET_INV)

lemma NET_DIV: "[| dorder g;
   tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) & y0 ~= 0 |]
==> tends (%xa. x xa / y xa) (x0 / y0) (mtop mr1, g)"
  by (import nets NET_DIV)

lemma NET_ABS: "tends x x0 (mtop mr1, g) ==> tends (%n. abs (x n)) (abs x0) (mtop mr1, g)"
  by (import nets NET_ABS)

lemma NET_LE: "[| dorder g;
   tends x x0 (mtop mr1, g) &
   tends y y0 (mtop mr1, g) &
   (EX N. g N N & (ALL n. g n N --> x n <= y n)) |]
==> x0 <= y0"
  by (import nets NET_LE)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" seq

consts
  "hol4-->" :: "(nat => real) => real => bool" ("hol4-->")

defs
  "hol4-->_def": "hol4--> == %x x0. tends x x0 (mtop mr1, nat_ge)"

lemma tends_num_real: "hol4--> x x0 = tends x x0 (mtop mr1, nat_ge)"
  by (import seq tends_num_real)

lemma SEQ: "hol4--> x x0 = (ALL e>0. EX N. ALL n>=N. abs (x n - x0) < e)"
  by (import seq SEQ)

lemma SEQ_CONST: "hol4--> (%x. k) k"
  by (import seq SEQ_CONST)

lemma SEQ_ADD: "hol4--> x x0 & hol4--> y y0 ==> hol4--> (%n. x n + y n) (x0 + y0)"
  by (import seq SEQ_ADD)

lemma SEQ_MUL: "hol4--> x x0 & hol4--> y y0 ==> hol4--> (%n. x n * y n) (x0 * y0)"
  by (import seq SEQ_MUL)

lemma SEQ_NEG: "hol4--> x x0 = hol4--> (%n. - x n) (- x0)"
  by (import seq SEQ_NEG)

lemma SEQ_INV: "hol4--> x x0 & x0 ~= 0 ==> hol4--> (%n. inverse (x n)) (inverse x0)"
  by (import seq SEQ_INV)

lemma SEQ_SUB: "hol4--> x x0 & hol4--> y y0 ==> hol4--> (%n. x n - y n) (x0 - y0)"
  by (import seq SEQ_SUB)

lemma SEQ_DIV: "hol4--> x x0 & hol4--> y y0 & y0 ~= 0 ==> hol4--> (%n. x n / y n) (x0 / y0)"
  by (import seq SEQ_DIV)

lemma SEQ_UNIQ: "hol4--> x x1 & hol4--> x x2 ==> x1 = x2"
  by (import seq SEQ_UNIQ)

consts
  convergent :: "(nat => real) => bool" 

defs
  convergent_def: "seq.convergent == %f. Ex (hol4--> f)"

lemma convergent: "seq.convergent f = Ex (hol4--> f)"
  by (import seq convergent)

definition
  cauchy :: "(nat => real) => bool"  where
  "cauchy ==
%f. ALL e>0. EX N. ALL m n. N <= m & N <= n --> abs (f m - f n) < e"

lemma cauchy: "cauchy f = (ALL e>0. EX N. ALL m n. N <= m & N <= n --> abs (f m - f n) < e)"
  by (import seq cauchy)

consts
  lim :: "(nat => real) => real" 

defs
  lim_def: "seq.lim == %f. Eps (hol4--> f)"

lemma lim: "seq.lim f = Eps (hol4--> f)"
  by (import seq lim)

lemma SEQ_LIM: "seq.convergent f = hol4--> f (seq.lim f)"
  by (import seq SEQ_LIM)

consts
  subseq :: "(nat => nat) => bool" 

defs
  subseq_def: "seq.subseq == %f. ALL m n. m < n --> f m < f n"

lemma subseq: "seq.subseq f = (ALL m n. m < n --> f m < f n)"
  by (import seq subseq)

lemma SUBSEQ_SUC: "seq.subseq f = (ALL n. f n < f (Suc n))"
  by (import seq SUBSEQ_SUC)

consts
  mono :: "(nat => real) => bool" 

defs
  mono_def: "seq.mono ==
%f. (ALL m n. m <= n --> f m <= f n) | (ALL m n. m <= n --> f n <= f m)"

lemma mono: "seq.mono f =
((ALL m n. m <= n --> f m <= f n) | (ALL m n. m <= n --> f n <= f m))"
  by (import seq mono)

lemma MONO_SUC: "seq.mono f = ((ALL x. f x <= f (Suc x)) | (ALL n. f (Suc n) <= f n))"
  by (import seq MONO_SUC)

lemma MAX_LEMMA: "EX k::real. ALL n<N::nat. abs ((s::nat => real) n) < k"
  by (import seq MAX_LEMMA)

lemma SEQ_BOUNDED: "bounded (mr1, nat_ge) s = (EX k. ALL n. abs (s n) < k)"
  by (import seq SEQ_BOUNDED)

lemma SEQ_BOUNDED_2: "(!!n. k <= f n & f n <= k') ==> bounded (mr1, nat_ge) f"
  by (import seq SEQ_BOUNDED_2)

lemma SEQ_CBOUNDED: "cauchy f ==> bounded (mr1, nat_ge) f"
  by (import seq SEQ_CBOUNDED)

lemma SEQ_ICONV: "bounded (mr1, nat_ge) f & (ALL m n. n <= m --> f n <= f m)
==> seq.convergent f"
  by (import seq SEQ_ICONV)

lemma SEQ_NEG_CONV: "seq.convergent f = seq.convergent (%n. - f n)"
  by (import seq SEQ_NEG_CONV)

lemma SEQ_NEG_BOUNDED: "bounded (mr1, nat_ge) (%n. - f n) = bounded (mr1, nat_ge) f"
  by (import seq SEQ_NEG_BOUNDED)

lemma SEQ_BCONV: "bounded (mr1, nat_ge) f & seq.mono f ==> seq.convergent f"
  by (import seq SEQ_BCONV)

lemma SEQ_MONOSUB: "EX f. seq.subseq f & seq.mono (%n. s (f n))"
  by (import seq SEQ_MONOSUB)

lemma SEQ_SBOUNDED: "bounded (mr1, nat_ge) s ==> bounded (mr1, nat_ge) (%n. s (f n))"
  by (import seq SEQ_SBOUNDED)

lemma SEQ_SUBLE: "seq.subseq f ==> n <= f n"
  by (import seq SEQ_SUBLE)

lemma SEQ_DIRECT: "seq.subseq f ==> EX x>=N1. N2 <= f x"
  by (import seq SEQ_DIRECT)

lemma SEQ_CAUCHY: "cauchy f = seq.convergent f"
  by (import seq SEQ_CAUCHY)

lemma SEQ_LE: "hol4--> f l & hol4--> g m & (EX x. ALL xa>=x. f xa <= g xa) ==> l <= m"
  by (import seq SEQ_LE)

lemma SEQ_SUC: "hol4--> f l = hol4--> (%n. f (Suc n)) l"
  by (import seq SEQ_SUC)

lemma SEQ_ABS: "hol4--> (%n. abs (f n)) 0 = hol4--> f 0"
  by (import seq SEQ_ABS)

lemma SEQ_ABS_IMP: "hol4--> f l ==> hol4--> (%n. abs (f n)) (abs l)"
  by (import seq SEQ_ABS_IMP)

lemma SEQ_INV0: "(!!y. EX N. ALL n>=N. y < f n) ==> hol4--> (%n. inverse (f n)) 0"
  by (import seq SEQ_INV0)

lemma SEQ_POWER_ABS: "abs c < 1 ==> hol4--> (op ^ (abs c)) 0"
  by (import seq SEQ_POWER_ABS)

lemma SEQ_POWER: "abs c < 1 ==> hol4--> (op ^ c) 0"
  by (import seq SEQ_POWER)

lemma NEST_LEMMA: "(ALL n. f n <= f (Suc n)) & (ALL n. g (Suc n) <= g n) & (ALL n. f n <= g n)
==> EX l m.
       l <= m &
       ((ALL n. f n <= l) & hol4--> f l) & (ALL n. m <= g n) & hol4--> g m"
  by (import seq NEST_LEMMA)

lemma NEST_LEMMA_UNIQ: "(ALL n. f n <= f (Suc n)) &
(ALL n. g (Suc n) <= g n) & (ALL n. f n <= g n) & hol4--> (%n. f n - g n) 0
==> EX x. ((ALL n. f n <= x) & hol4--> f x) &
          (ALL n. x <= g n) & hol4--> g x"
  by (import seq NEST_LEMMA_UNIQ)

consts
  sums :: "(nat => real) => real => bool" 

defs
  sums_def: "seq.sums == %f. hol4--> (%n. real.sum (0, n) f)"

lemma sums: "seq.sums f s = hol4--> (%n. real.sum (0, n) f) s"
  by (import seq sums)

consts
  summable :: "(nat => real) => bool" 

defs
  summable_def: "seq.summable == %f. Ex (seq.sums f)"

lemma summable: "seq.summable f = Ex (seq.sums f)"
  by (import seq summable)

consts
  suminf :: "(nat => real) => real" 

defs
  suminf_def: "seq.suminf == %f. Eps (seq.sums f)"

lemma suminf: "seq.suminf f = Eps (seq.sums f)"
  by (import seq suminf)

lemma SUM_SUMMABLE: "seq.sums f l ==> seq.summable f"
  by (import seq SUM_SUMMABLE)

lemma SUMMABLE_SUM: "seq.summable f ==> seq.sums f (seq.suminf f)"
  by (import seq SUMMABLE_SUM)

lemma SUM_UNIQ: "seq.sums f x ==> x = seq.suminf f"
  by (import seq SUM_UNIQ)

lemma SER_0: "(!!m. n <= m ==> f m = 0) ==> seq.sums f (real.sum (0, n) f)"
  by (import seq SER_0)

lemma SER_POS_LE: "seq.summable f & (ALL m>=n. 0 <= f m) ==> real.sum (0, n) f <= seq.suminf f"
  by (import seq SER_POS_LE)

lemma SER_POS_LT: "seq.summable f & (ALL m>=n. 0 < f m) ==> real.sum (0, n) f < seq.suminf f"
  by (import seq SER_POS_LT)

lemma SER_GROUP: "seq.summable f & 0 < k
==> seq.sums (%n. real.sum (n * k, k) f) (seq.suminf f)"
  by (import seq SER_GROUP)

lemma SER_PAIR: "seq.summable f ==> seq.sums (%n. real.sum (2 * n, 2) f) (seq.suminf f)"
  by (import seq SER_PAIR)

lemma SER_OFFSET: "seq.summable f
==> seq.sums (%n. f (n + k)) (seq.suminf f - real.sum (0, k) f)"
  by (import seq SER_OFFSET)

lemma SER_POS_LT_PAIR: "seq.summable f & (ALL d. 0 < f (n + 2 * d) + f (n + (2 * d + 1)))
==> real.sum (0, n) f < seq.suminf f"
  by (import seq SER_POS_LT_PAIR)

lemma SER_ADD: "seq.sums x x0 & seq.sums y y0 ==> seq.sums (%n. x n + y n) (x0 + y0)"
  by (import seq SER_ADD)

lemma SER_CMUL: "seq.sums x x0 ==> seq.sums (%n. c * x n) (c * x0)"
  by (import seq SER_CMUL)

lemma SER_NEG: "seq.sums x x0 ==> seq.sums (%xa. - x xa) (- x0)"
  by (import seq SER_NEG)

lemma SER_SUB: "seq.sums x x0 & seq.sums y y0 ==> seq.sums (%xa. x xa - y xa) (x0 - y0)"
  by (import seq SER_SUB)

lemma SER_CDIV: "seq.sums x x0 ==> seq.sums (%xa. x xa / c) (x0 / c)"
  by (import seq SER_CDIV)

lemma SER_CAUCHY: "seq.summable f =
(ALL e>0. EX N. ALL m n. N <= m --> abs (real.sum (m, n) f) < e)"
  by (import seq SER_CAUCHY)

lemma SER_ZERO: "seq.summable f ==> hol4--> f 0"
  by (import seq SER_ZERO)

lemma SER_COMPAR: "(EX x. ALL xa>=x. abs (f xa) <= g xa) & seq.summable g ==> seq.summable f"
  by (import seq SER_COMPAR)

lemma SER_COMPARA: "(EX x. ALL xa>=x. abs (f xa) <= g xa) & seq.summable g
==> seq.summable (%k. abs (f k))"
  by (import seq SER_COMPARA)

lemma SER_LE: "(ALL n. f n <= g n) & seq.summable f & seq.summable g
==> seq.suminf f <= seq.suminf g"
  by (import seq SER_LE)

lemma SER_LE2: "(ALL n. abs (f n) <= g n) & seq.summable g
==> seq.summable f & seq.suminf f <= seq.suminf g"
  by (import seq SER_LE2)

lemma SER_ACONV: "seq.summable (%n. abs (f n)) ==> seq.summable f"
  by (import seq SER_ACONV)

lemma SER_ABS: "seq.summable (%n. abs (f n))
==> abs (seq.suminf f) <= seq.suminf (%n. abs (f n))"
  by (import seq SER_ABS)

lemma GP_FINITE: "x ~= 1 ==> real.sum (0, n) (op ^ x) = (x ^ n - 1) / (x - 1)"
  by (import seq GP_FINITE)

lemma GP: "abs x < 1 ==> seq.sums (op ^ x) (inverse (1 - x))"
  by (import seq GP)

lemma SER_RATIO: "c < 1 & (ALL n>=N. abs (f (Suc n)) <= c * abs (f n)) ==> seq.summable f"
  by (import seq SER_RATIO)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" lim

definition
  tends_real_real :: "(real => real) => real => real => bool"  where
  "tends_real_real == %f l x0. tends f l (mtop mr1, nets.tendsto (mr1, x0))"

lemma tends_real_real: "tends_real_real f l x0 = tends f l (mtop mr1, nets.tendsto (mr1, x0))"
  by (import lim tends_real_real)

lemma LIM: "tends_real_real f y0 x0 =
(ALL e>0.
    EX d>0.
       ALL x. 0 < abs (x - x0) & abs (x - x0) < d --> abs (f x - y0) < e)"
  by (import lim LIM)

lemma LIM_CONST: "tends_real_real (%x. k) k x"
  by (import lim LIM_CONST)

lemma LIM_ADD: "tends_real_real f l x & tends_real_real g m x
==> tends_real_real (%x. f x + g x) (l + m) x"
  by (import lim LIM_ADD)

lemma LIM_MUL: "tends_real_real f l x & tends_real_real g m x
==> tends_real_real (%x. f x * g x) (l * m) x"
  by (import lim LIM_MUL)

lemma LIM_NEG: "tends_real_real f l x = tends_real_real (%x. - f x) (- l) x"
  by (import lim LIM_NEG)

lemma LIM_INV: "tends_real_real f l x & l ~= 0
==> tends_real_real (%x. inverse (f x)) (inverse l) x"
  by (import lim LIM_INV)

lemma LIM_SUB: "tends_real_real f l x & tends_real_real g m x
==> tends_real_real (%x. f x - g x) (l - m) x"
  by (import lim LIM_SUB)

lemma LIM_DIV: "tends_real_real f l x & tends_real_real g m x & m ~= 0
==> tends_real_real (%x. f x / g x) (l / m) x"
  by (import lim LIM_DIV)

lemma LIM_NULL: "tends_real_real f l x = tends_real_real (%x. f x - l) 0 x"
  by (import lim LIM_NULL)

lemma LIM_X: "tends_real_real (%x. x) x0 x0"
  by (import lim LIM_X)

lemma LIM_UNIQ: "tends_real_real f l x & tends_real_real f m x ==> l = m"
  by (import lim LIM_UNIQ)

lemma LIM_EQUAL: "(!!x. x ~= x0 ==> f x = g x)
==> tends_real_real f l x0 = tends_real_real g l x0"
  by (import lim LIM_EQUAL)

lemma LIM_TRANSFORM: "tends_real_real (%x. f x - g x) 0 x0 & tends_real_real g l x0
==> tends_real_real f l x0"
  by (import lim LIM_TRANSFORM)

definition
  diffl :: "(real => real) => real => real => bool"  where
  "diffl == %f l x. tends_real_real (%h. (f (x + h) - f x) / h) l 0"

lemma diffl: "diffl f l x = tends_real_real (%h. (f (x + h) - f x) / h) l 0"
  by (import lim diffl)

definition
  contl :: "(real => real) => real => bool"  where
  "contl == %f x. tends_real_real (%h. f (x + h)) (f x) 0"

lemma contl: "contl f x = tends_real_real (%h. f (x + h)) (f x) 0"
  by (import lim contl)

consts
  differentiable :: "(real => real) => real => bool" 

defs
  differentiable_def: "lim.differentiable == %f x. EX l. diffl f l x"

lemma differentiable: "lim.differentiable f x = (EX l. diffl f l x)"
  by (import lim differentiable)

lemma DIFF_UNIQ: "diffl f l x & diffl f m x ==> l = m"
  by (import lim DIFF_UNIQ)

lemma DIFF_CONT: "diffl f l x ==> contl f x"
  by (import lim DIFF_CONT)

lemma CONTL_LIM: "contl f x = tends_real_real f (f x) x"
  by (import lim CONTL_LIM)

lemma DIFF_CARAT: "diffl f l x =
(EX g. (ALL z. f z - f x = g z * (z - x)) & contl g x & g x = l)"
  by (import lim DIFF_CARAT)

lemma CONT_CONST: "contl (%x. k) x"
  by (import lim CONT_CONST)

lemma CONT_ADD: "contl f x & contl g x ==> contl (%x. f x + g x) x"
  by (import lim CONT_ADD)

lemma CONT_MUL: "contl f x & contl g x ==> contl (%x. f x * g x) x"
  by (import lim CONT_MUL)

lemma CONT_NEG: "contl f x ==> contl (%x. - f x) x"
  by (import lim CONT_NEG)

lemma CONT_INV: "contl f x & f x ~= 0 ==> contl (%x. inverse (f x)) x"
  by (import lim CONT_INV)

lemma CONT_SUB: "contl f x & contl g x ==> contl (%x. f x - g x) x"
  by (import lim CONT_SUB)

lemma CONT_DIV: "contl f x & contl g x & g x ~= 0 ==> contl (%x. f x / g x) x"
  by (import lim CONT_DIV)

lemma CONT_COMPOSE: "contl f x & contl g (f x) ==> contl (%x. g (f x)) x"
  by (import lim CONT_COMPOSE)

lemma IVT: "a <= b & (f a <= y & y <= f b) & (ALL x. a <= x & x <= b --> contl f x)
==> EX x>=a. x <= b & f x = y"
  by (import lim IVT)

lemma IVT2: "a <= b & (f b <= y & y <= f a) & (ALL x. a <= x & x <= b --> contl f x)
==> EX x>=a. x <= b & f x = y"
  by (import lim IVT2)

lemma DIFF_CONST: "diffl (%x. k) 0 x"
  by (import lim DIFF_CONST)

lemma DIFF_ADD: "diffl f l x & diffl g m x ==> diffl (%x. f x + g x) (l + m) x"
  by (import lim DIFF_ADD)

lemma DIFF_MUL: "diffl f l x & diffl g m x ==> diffl (%x. f x * g x) (l * g x + m * f x) x"
  by (import lim DIFF_MUL)

lemma DIFF_CMUL: "diffl f l x ==> diffl (%x. c * f x) (c * l) x"
  by (import lim DIFF_CMUL)

lemma DIFF_NEG: "diffl f l x ==> diffl (%x. - f x) (- l) x"
  by (import lim DIFF_NEG)

lemma DIFF_SUB: "diffl f l x & diffl g m x ==> diffl (%x. f x - g x) (l - m) x"
  by (import lim DIFF_SUB)

lemma DIFF_CHAIN: "diffl f l (g x) & diffl g m x ==> diffl (%x. f (g x)) (l * m) x"
  by (import lim DIFF_CHAIN)

lemma DIFF_X: "diffl (%x. x) 1 x"
  by (import lim DIFF_X)

lemma DIFF_POW: "diffl (%x. x ^ n) (real n * x ^ (n - 1)) x"
  by (import lim DIFF_POW)

lemma DIFF_XM1: "x ~= 0 ==> diffl inverse (- (inverse x ^ 2)) x"
  by (import lim DIFF_XM1)

lemma DIFF_INV: "diffl f l x & f x ~= 0 ==> diffl (%x. inverse (f x)) (- (l / f x ^ 2)) x"
  by (import lim DIFF_INV)

lemma DIFF_DIV: "diffl f l x & diffl g m x & g x ~= 0
==> diffl (%x. f x / g x) ((l * g x - m * f x) / g x ^ 2) x"
  by (import lim DIFF_DIV)

lemma DIFF_SUM: "(!!r. m <= r & r < m + n ==> diffl (f r) (f' r x) x)
==> diffl (%x. real.sum (m, n) (%n. f n x)) (real.sum (m, n) (%r. f' r x)) x"
  by (import lim DIFF_SUM)

lemma CONT_BOUNDED: "a <= b & (ALL x. a <= x & x <= b --> contl f x)
==> EX M. ALL x. a <= x & x <= b --> f x <= M"
  by (import lim CONT_BOUNDED)

lemma CONT_HASSUP: "a <= b & (ALL x. a <= x & x <= b --> contl f x)
==> EX M. (ALL x. a <= x & x <= b --> f x <= M) &
          (ALL N<M. EX x>=a. x <= b & N < f x)"
  by (import lim CONT_HASSUP)

lemma CONT_ATTAINS: "a <= b & (ALL x. a <= x & x <= b --> contl f x)
==> EX x. (ALL xa. a <= xa & xa <= b --> f xa <= x) &
          (EX xa>=a. xa <= b & f xa = x)"
  by (import lim CONT_ATTAINS)

lemma CONT_ATTAINS2: "a <= b & (ALL x. a <= x & x <= b --> contl f x)
==> EX x. (ALL xa. a <= xa & xa <= b --> x <= f xa) &
          (EX xa>=a. xa <= b & f xa = x)"
  by (import lim CONT_ATTAINS2)

lemma CONT_ATTAINS_ALL: "a <= b & (ALL x. a <= x & x <= b --> contl f x)
==> EX x M.
       x <= M &
       (ALL y. x <= y & y <= M --> (EX x>=a. x <= b & f x = y)) &
       (ALL xa. a <= xa & xa <= b --> x <= f xa & f xa <= M)"
  by (import lim CONT_ATTAINS_ALL)

lemma DIFF_LINC: "diffl f l x & 0 < l ==> EX d>0. ALL h. 0 < h & h < d --> f x < f (x + h)"
  by (import lim DIFF_LINC)

lemma DIFF_LDEC: "diffl f l x & l < 0 ==> EX d>0. ALL h. 0 < h & h < d --> f x < f (x - h)"
  by (import lim DIFF_LDEC)

lemma DIFF_LMAX: "diffl f l x & (EX d>0. ALL y. abs (x - y) < d --> f y <= f x) ==> l = 0"
  by (import lim DIFF_LMAX)

lemma DIFF_LMIN: "diffl f l x & (EX d>0. ALL y. abs (x - y) < d --> f x <= f y) ==> l = 0"
  by (import lim DIFF_LMIN)

lemma DIFF_LCONST: "diffl f l x & (EX d>0. ALL y. abs (x - y) < d --> f y = f x) ==> l = 0"
  by (import lim DIFF_LCONST)

lemma ROLLE: "a < b &
f a = f b &
(ALL x. a <= x & x <= b --> contl f x) &
(ALL x. a < x & x < b --> lim.differentiable f x)
==> EX z>a. z < b & diffl f 0 z"
  by (import lim ROLLE)

lemma MVT: "a < b &
(ALL x. a <= x & x <= b --> contl f x) &
(ALL x. a < x & x < b --> lim.differentiable f x)
==> EX l z. a < z & z < b & diffl f l z & f b - f a = (b - a) * l"
  by (import lim MVT)

lemma DIFF_ISCONST_END: "a < b &
(ALL x. a <= x & x <= b --> contl f x) &
(ALL x. a < x & x < b --> diffl f 0 x)
==> f b = f a"
  by (import lim DIFF_ISCONST_END)

lemma DIFF_ISCONST: "[| a < b &
   (ALL x. a <= x & x <= b --> contl f x) &
   (ALL x. a < x & x < b --> diffl f 0 x);
   a <= x & x <= b |]
==> f x = f a"
  by (import lim DIFF_ISCONST)

lemma DIFF_ISCONST_ALL: "(!!x. diffl f 0 x) ==> f x = f y"
  by (import lim DIFF_ISCONST_ALL)

lemma INTERVAL_ABS: "((x::real) - (d::real) <= (z::real) & z <= x + d) = (abs (z - x) <= d)"
  by (import lim INTERVAL_ABS)

lemma CONT_INJ_LEMMA: "0 < d &
(ALL z. abs (z - x) <= d --> g (f z) = z) &
(ALL z. abs (z - x) <= d --> contl f z)
==> ~ (ALL z. abs (z - x) <= d --> f z <= f x)"
  by (import lim CONT_INJ_LEMMA)

lemma CONT_INJ_LEMMA2: "0 < d &
(ALL z. abs (z - x) <= d --> g (f z) = z) &
(ALL z. abs (z - x) <= d --> contl f z)
==> ~ (ALL z. abs (z - x) <= d --> f x <= f z)"
  by (import lim CONT_INJ_LEMMA2)

lemma CONT_INJ_RANGE: "0 < d &
(ALL z. abs (z - x) <= d --> g (f z) = z) &
(ALL z. abs (z - x) <= d --> contl f z)
==> EX e>0. ALL y. abs (y - f x) <= e --> (EX z. abs (z - x) <= d & f z = y)"
  by (import lim CONT_INJ_RANGE)

lemma CONT_INVERSE: "0 < d &
(ALL z. abs (z - x) <= d --> g (f z) = z) &
(ALL z. abs (z - x) <= d --> contl f z)
==> contl g (f x)"
  by (import lim CONT_INVERSE)

lemma DIFF_INVERSE: "0 < d &
(ALL z. abs (z - x) <= d --> g (f z) = z) &
(ALL z. abs (z - x) <= d --> contl f z) & diffl f l x & l ~= 0
==> diffl g (inverse l) (f x)"
  by (import lim DIFF_INVERSE)

lemma DIFF_INVERSE_LT: "0 < d &
(ALL z. abs (z - x) < d --> g (f z) = z) &
(ALL z. abs (z - x) < d --> contl f z) & diffl f l x & l ~= 0
==> diffl g (inverse l) (f x)"
  by (import lim DIFF_INVERSE_LT)

lemma INTERVAL_CLEMMA: "(a::real) < (x::real) & x < (b::real)
==> EX d>0::real. ALL y::real. abs (y - x) <= d --> a < y & y < b"
  by (import lim INTERVAL_CLEMMA)

lemma DIFF_INVERSE_OPEN: "a < x &
x < b &
(ALL z. a < z & z < b --> g (f z) = z & contl f z) & diffl f l x & l ~= 0
==> diffl g (inverse l) (f x)"
  by (import lim DIFF_INVERSE_OPEN)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" powser

lemma POWDIFF_LEMMA: "real.sum (0, Suc n) (%p. x ^ p * y ^ (Suc n - p)) =
y * real.sum (0, Suc n) (%p. x ^ p * y ^ (n - p))"
  by (import powser POWDIFF_LEMMA)

lemma POWDIFF: "x ^ Suc n - y ^ Suc n =
(x - y) * real.sum (0, Suc n) (%p. x ^ p * y ^ (n - p))"
  by (import powser POWDIFF)

lemma POWREV: "real.sum (0, Suc n) (%xa. x ^ xa * y ^ (n - xa)) =
real.sum (0, Suc n) (%xa. x ^ (n - xa) * y ^ xa)"
  by (import powser POWREV)

lemma POWSER_INSIDEA: "seq.summable (%n. f n * x ^ n) & abs z < abs x
==> seq.summable (%n. abs (f n) * z ^ n)"
  by (import powser POWSER_INSIDEA)

lemma POWSER_INSIDE: "seq.summable (%n. f n * x ^ n) & abs z < abs x
==> seq.summable (%n. f n * z ^ n)"
  by (import powser POWSER_INSIDE)

consts
  diffs :: "(nat => real) => nat => real" 

defs
  diffs_def: "powser.diffs == %c n. real (Suc n) * c (Suc n)"

lemma diffs: "powser.diffs c = (%n. real (Suc n) * c (Suc n))"
  by (import powser diffs)

lemma DIFFS_NEG: "powser.diffs (%n. - c n) = (%x. - powser.diffs c x)"
  by (import powser DIFFS_NEG)

lemma DIFFS_LEMMA: "real.sum (0, n) (%n. powser.diffs c n * x ^ n) =
real.sum (0, n) (%n. real n * (c n * x ^ (n - 1))) +
real n * (c n * x ^ (n - 1))"
  by (import powser DIFFS_LEMMA)

lemma DIFFS_LEMMA2: "real.sum (0, n) (%n. real n * (c n * x ^ (n - 1))) =
real.sum (0, n) (%n. powser.diffs c n * x ^ n) -
real n * (c n * x ^ (n - 1))"
  by (import powser DIFFS_LEMMA2)

lemma DIFFS_EQUIV: "seq.summable (%n. powser.diffs c n * x ^ n)
==> seq.sums (%n. real n * (c n * x ^ (n - 1)))
     (seq.suminf (%n. powser.diffs c n * x ^ n))"
  by (import powser DIFFS_EQUIV)

lemma TERMDIFF_LEMMA1: "real.sum (0, m) (%p. (z + h) ^ (m - p) * z ^ p - z ^ m) =
real.sum (0, m) (%p. z ^ p * ((z + h) ^ (m - p) - z ^ (m - p)))"
  by (import powser TERMDIFF_LEMMA1)

lemma TERMDIFF_LEMMA2: "h ~= 0
==> ((z + h) ^ n - z ^ n) / h - real n * z ^ (n - 1) =
    h *
    real.sum (0, n - 1)
     (%p. z ^ p *
          real.sum (0, n - 1 - p) (%q. (z + h) ^ q * z ^ (n - 2 - p - q)))"
  by (import powser TERMDIFF_LEMMA2)

lemma TERMDIFF_LEMMA3: "h ~= 0 & abs z <= k' & abs (z + h) <= k'
==> abs (((z + h) ^ n - z ^ n) / h - real n * z ^ (n - 1))
    <= real n * (real (n - 1) * (k' ^ (n - 2) * abs h))"
  by (import powser TERMDIFF_LEMMA3)

lemma TERMDIFF_LEMMA4: "0 < k & (ALL h. 0 < abs h & abs h < k --> abs (f h) <= k' * abs h)
==> tends_real_real f 0 0"
  by (import powser TERMDIFF_LEMMA4)

lemma TERMDIFF_LEMMA5: "0 < k &
seq.summable f &
(ALL h. 0 < abs h & abs h < k --> (ALL n. abs (g h n) <= f n * abs h))
==> tends_real_real (%h. seq.suminf (g h)) 0 0"
  by (import powser TERMDIFF_LEMMA5)

lemma TERMDIFF: "seq.summable (%n. c n * k' ^ n) &
seq.summable (%n. powser.diffs c n * k' ^ n) &
seq.summable (%n. powser.diffs (powser.diffs c) n * k' ^ n) & abs x < abs k'
==> diffl (%x. seq.suminf (%n. c n * x ^ n))
     (seq.suminf (%n. powser.diffs c n * x ^ n)) x"
  by (import powser TERMDIFF)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" transc

consts
  exp :: "real => real" 

defs
  exp_def: "transc.exp == %x. seq.suminf (%n. inverse (real (FACT n)) * x ^ n)"

lemma exp: "transc.exp x = seq.suminf (%n. inverse (real (FACT n)) * x ^ n)"
  by (import transc exp)

consts
  cos :: "real => real" 

defs
  cos_def: "transc.cos ==
%x. seq.suminf
     (%n. (if EVEN n then (- 1) ^ (n div 2) / real (FACT n) else 0) * x ^ n)"

lemma cos: "transc.cos x =
seq.suminf
 (%n. (if EVEN n then (- 1) ^ (n div 2) / real (FACT n) else 0) * x ^ n)"
  by (import transc cos)

consts
  sin :: "real => real" 

defs
  sin_def: "transc.sin ==
%x. seq.suminf
     (%n. (if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)) *
          x ^ n)"

lemma sin: "transc.sin x =
seq.suminf
 (%n. (if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)) *
      x ^ n)"
  by (import transc sin)

lemma EXP_CONVERGES: "seq.sums (%n. inverse (real (FACT n)) * x ^ n) (transc.exp x)"
  by (import transc EXP_CONVERGES)

lemma SIN_CONVERGES: "seq.sums
 (%n. (if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)) *
      x ^ n)
 (transc.sin x)"
  by (import transc SIN_CONVERGES)

lemma COS_CONVERGES: "seq.sums
 (%n. (if EVEN n then (- 1) ^ (n div 2) / real (FACT n) else 0) * x ^ n)
 (transc.cos x)"
  by (import transc COS_CONVERGES)

lemma EXP_FDIFF: "powser.diffs (%n. inverse (real (FACT n))) = (%n. inverse (real (FACT n)))"
  by (import transc EXP_FDIFF)

lemma SIN_FDIFF: "powser.diffs
 (%n. if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)) =
(%n. if EVEN n then (- 1) ^ (n div 2) / real (FACT n) else 0)"
  by (import transc SIN_FDIFF)

lemma COS_FDIFF: "powser.diffs (%n. if EVEN n then (- 1) ^ (n div 2) / real (FACT n) else 0) =
(%n. - (if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)))"
  by (import transc COS_FDIFF)

lemma SIN_NEGLEMMA: "- transc.sin x =
seq.suminf
 (%n. - ((if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)) *
         x ^ n))"
  by (import transc SIN_NEGLEMMA)

lemma DIFF_EXP: "diffl transc.exp (transc.exp x) x"
  by (import transc DIFF_EXP)

lemma DIFF_SIN: "diffl transc.sin (transc.cos x) x"
  by (import transc DIFF_SIN)

lemma DIFF_COS: "diffl transc.cos (- transc.sin x) x"
  by (import transc DIFF_COS)

lemma DIFF_COMPOSITE: "(diffl f l x & f x ~= 0 --> diffl (%x. inverse (f x)) (- (l / f x ^ 2)) x) &
(diffl f l x & diffl g m x & g x ~= 0 -->
 diffl (%x. f x / g x) ((l * g x - m * f x) / g x ^ 2) x) &
(diffl f l x & diffl g m x --> diffl (%x. f x + g x) (l + m) x) &
(diffl f l x & diffl g m x -->
 diffl (%x. f x * g x) (l * g x + m * f x) x) &
(diffl f l x & diffl g m x --> diffl (%x. f x - g x) (l - m) x) &
(diffl f l x --> diffl (%x. - f x) (- l) x) &
(diffl g m x --> diffl (%x. g x ^ n) (real n * g x ^ (n - 1) * m) x) &
(diffl g m x --> diffl (%x. transc.exp (g x)) (transc.exp (g x) * m) x) &
(diffl g m x --> diffl (%x. transc.sin (g x)) (transc.cos (g x) * m) x) &
(diffl g m x --> diffl (%x. transc.cos (g x)) (- transc.sin (g x) * m) x)"
  by (import transc DIFF_COMPOSITE)

lemma EXP_0: "transc.exp 0 = 1"
  by (import transc EXP_0)

lemma EXP_LE_X: "0 <= x ==> 1 + x <= transc.exp x"
  by (import transc EXP_LE_X)

lemma EXP_LT_1: "0 < x ==> 1 < transc.exp x"
  by (import transc EXP_LT_1)

lemma EXP_ADD_MUL: "transc.exp (x + y) * transc.exp (- x) = transc.exp y"
  by (import transc EXP_ADD_MUL)

lemma EXP_NEG_MUL: "transc.exp x * transc.exp (- x) = 1"
  by (import transc EXP_NEG_MUL)

lemma EXP_NEG_MUL2: "transc.exp (- x) * transc.exp x = 1"
  by (import transc EXP_NEG_MUL2)

lemma EXP_NEG: "transc.exp (- x) = inverse (transc.exp x)"
  by (import transc EXP_NEG)

lemma EXP_ADD: "transc.exp (x + y) = transc.exp x * transc.exp y"
  by (import transc EXP_ADD)

lemma EXP_POS_LE: "0 <= transc.exp x"
  by (import transc EXP_POS_LE)

lemma EXP_NZ: "transc.exp x ~= 0"
  by (import transc EXP_NZ)

lemma EXP_POS_LT: "0 < transc.exp x"
  by (import transc EXP_POS_LT)

lemma EXP_N: "transc.exp (real n * x) = transc.exp x ^ n"
  by (import transc EXP_N)

lemma EXP_SUB: "transc.exp (x - y) = transc.exp x / transc.exp y"
  by (import transc EXP_SUB)

lemma EXP_MONO_IMP: "x < y ==> transc.exp x < transc.exp y"
  by (import transc EXP_MONO_IMP)

lemma EXP_MONO_LT: "(transc.exp x < transc.exp y) = (x < y)"
  by (import transc EXP_MONO_LT)

lemma EXP_MONO_LE: "(transc.exp x <= transc.exp y) = (x <= y)"
  by (import transc EXP_MONO_LE)

lemma EXP_INJ: "(transc.exp x = transc.exp y) = (x = y)"
  by (import transc EXP_INJ)

lemma EXP_TOTAL_LEMMA: "1 <= y ==> EX x>=0. x <= y - 1 & transc.exp x = y"
  by (import transc EXP_TOTAL_LEMMA)

lemma EXP_TOTAL: "0 < y ==> EX x. transc.exp x = y"
  by (import transc EXP_TOTAL)

consts
  ln :: "real => real" 

defs
  ln_def: "transc.ln == %x. SOME u. transc.exp u = x"

lemma ln: "transc.ln x = (SOME u. transc.exp u = x)"
  by (import transc ln)

lemma LN_EXP: "transc.ln (transc.exp x) = x"
  by (import transc LN_EXP)

lemma EXP_LN: "(transc.exp (transc.ln x) = x) = (0 < x)"
  by (import transc EXP_LN)

lemma LN_MUL: "0 < x & 0 < y ==> transc.ln (x * y) = transc.ln x + transc.ln y"
  by (import transc LN_MUL)

lemma LN_INJ: "0 < x & 0 < y ==> (transc.ln x = transc.ln y) = (x = y)"
  by (import transc LN_INJ)

lemma LN_1: "transc.ln 1 = 0"
  by (import transc LN_1)

lemma LN_INV: "0 < x ==> transc.ln (inverse x) = - transc.ln x"
  by (import transc LN_INV)

lemma LN_DIV: "0 < x & 0 < y ==> transc.ln (x / y) = transc.ln x - transc.ln y"
  by (import transc LN_DIV)

lemma LN_MONO_LT: "0 < x & 0 < y ==> (transc.ln x < transc.ln y) = (x < y)"
  by (import transc LN_MONO_LT)

lemma LN_MONO_LE: "0 < x & 0 < y ==> (transc.ln x <= transc.ln y) = (x <= y)"
  by (import transc LN_MONO_LE)

lemma LN_POW: "0 < x ==> transc.ln (x ^ n) = real n * transc.ln x"
  by (import transc LN_POW)

lemma LN_LE: "0 <= x ==> transc.ln (1 + x) <= x"
  by (import transc LN_LE)

lemma LN_LT_X: "0 < x ==> transc.ln x < x"
  by (import transc LN_LT_X)

lemma LN_POS: "1 <= x ==> 0 <= transc.ln x"
  by (import transc LN_POS)

consts
  root :: "nat => real => real" 

defs
  root_def: "transc.root == %n x. SOME u. (0 < x --> 0 < u) & u ^ n = x"

lemma root: "transc.root n x = (SOME u. (0 < x --> 0 < u) & u ^ n = x)"
  by (import transc root)

consts
  sqrt :: "real => real" 

defs
  sqrt_def: "transc.sqrt == transc.root 2"

lemma sqrt: "transc.sqrt x = transc.root 2 x"
  by (import transc sqrt)

lemma ROOT_LT_LEMMA: "0 < x ==> transc.exp (transc.ln x / real (Suc n)) ^ Suc n = x"
  by (import transc ROOT_LT_LEMMA)

lemma ROOT_LN: "0 < x ==> transc.root (Suc n) x = transc.exp (transc.ln x / real (Suc n))"
  by (import transc ROOT_LN)

lemma ROOT_0: "transc.root (Suc n) 0 = 0"
  by (import transc ROOT_0)

lemma ROOT_1: "transc.root (Suc n) 1 = 1"
  by (import transc ROOT_1)

lemma ROOT_POS_LT: "0 < x ==> 0 < transc.root (Suc n) x"
  by (import transc ROOT_POS_LT)

lemma ROOT_POW_POS: "0 <= x ==> transc.root (Suc n) x ^ Suc n = x"
  by (import transc ROOT_POW_POS)

lemma POW_ROOT_POS: "0 <= x ==> transc.root (Suc n) (x ^ Suc n) = x"
  by (import transc POW_ROOT_POS)

lemma ROOT_POS: "0 <= x ==> 0 <= transc.root (Suc n) x"
  by (import transc ROOT_POS)

lemma ROOT_POS_UNIQ: "0 <= x & 0 <= y & y ^ Suc n = x ==> transc.root (Suc n) x = y"
  by (import transc ROOT_POS_UNIQ)

lemma ROOT_MUL: "0 <= x & 0 <= y
==> transc.root (Suc n) (x * y) =
    transc.root (Suc n) x * transc.root (Suc n) y"
  by (import transc ROOT_MUL)

lemma ROOT_INV: "0 <= x ==> transc.root (Suc n) (inverse x) = inverse (transc.root (Suc n) x)"
  by (import transc ROOT_INV)

lemma ROOT_DIV: "0 <= xa & 0 <= xb
==> transc.root (Suc x) (xa / xb) =
    transc.root (Suc x) xa / transc.root (Suc x) xb"
  by (import transc ROOT_DIV)

lemma ROOT_MONO_LE: "0 <= x & x <= y ==> transc.root (Suc n) x <= transc.root (Suc n) y"
  by (import transc ROOT_MONO_LE)

lemma SQRT_0: "transc.sqrt 0 = 0"
  by (import transc SQRT_0)

lemma SQRT_1: "transc.sqrt 1 = 1"
  by (import transc SQRT_1)

lemma SQRT_POS_LT: "0 < x ==> 0 < transc.sqrt x"
  by (import transc SQRT_POS_LT)

lemma SQRT_POS_LE: "0 <= x ==> 0 <= transc.sqrt x"
  by (import transc SQRT_POS_LE)

lemma SQRT_POW2: "(transc.sqrt x ^ 2 = x) = (0 <= x)"
  by (import transc SQRT_POW2)

lemma SQRT_POW_2: "0 <= x ==> transc.sqrt x ^ 2 = x"
  by (import transc SQRT_POW_2)

lemma POW_2_SQRT: "0 <= x ==> transc.sqrt (x ^ 2) = x"
  by (import transc POW_2_SQRT)

lemma SQRT_POS_UNIQ: "0 <= x & 0 <= xa & xa ^ 2 = x ==> transc.sqrt x = xa"
  by (import transc SQRT_POS_UNIQ)

lemma SQRT_MUL: "0 <= x & 0 <= xa ==> transc.sqrt (x * xa) = transc.sqrt x * transc.sqrt xa"
  by (import transc SQRT_MUL)

lemma SQRT_INV: "0 <= x ==> transc.sqrt (inverse x) = inverse (transc.sqrt x)"
  by (import transc SQRT_INV)

lemma SQRT_DIV: "0 <= x & 0 <= xa ==> transc.sqrt (x / xa) = transc.sqrt x / transc.sqrt xa"
  by (import transc SQRT_DIV)

lemma SQRT_MONO_LE: "0 <= x & x <= xa ==> transc.sqrt x <= transc.sqrt xa"
  by (import transc SQRT_MONO_LE)

lemma SQRT_EVEN_POW2: "EVEN n ==> transc.sqrt (2 ^ n) = 2 ^ (n div 2)"
  by (import transc SQRT_EVEN_POW2)

lemma REAL_DIV_SQRT: "0 <= x ==> x / transc.sqrt x = transc.sqrt x"
  by (import transc REAL_DIV_SQRT)

lemma SQRT_EQ: "x ^ 2 = y & 0 <= x ==> x = transc.sqrt y"
  by (import transc SQRT_EQ)

lemma SIN_0: "transc.sin 0 = 0"
  by (import transc SIN_0)

lemma COS_0: "transc.cos 0 = 1"
  by (import transc COS_0)

lemma SIN_CIRCLE: "transc.sin x ^ 2 + transc.cos x ^ 2 = 1"
  by (import transc SIN_CIRCLE)

lemma SIN_BOUND: "abs (transc.sin x) <= 1"
  by (import transc SIN_BOUND)

lemma SIN_BOUNDS: "- 1 <= transc.sin x & transc.sin x <= 1"
  by (import transc SIN_BOUNDS)

lemma COS_BOUND: "abs (transc.cos x) <= 1"
  by (import transc COS_BOUND)

lemma COS_BOUNDS: "- 1 <= transc.cos x & transc.cos x <= 1"
  by (import transc COS_BOUNDS)

lemma SIN_COS_ADD: "(transc.sin (x + y) -
 (transc.sin x * transc.cos y + transc.cos x * transc.sin y)) ^
2 +
(transc.cos (x + y) -
 (transc.cos x * transc.cos y - transc.sin x * transc.sin y)) ^
2 =
0"
  by (import transc SIN_COS_ADD)

lemma SIN_COS_NEG: "(transc.sin (- x) + transc.sin x) ^ 2 +
(transc.cos (- x) - transc.cos x) ^ 2 =
0"
  by (import transc SIN_COS_NEG)

lemma SIN_ADD: "transc.sin (x + y) =
transc.sin x * transc.cos y + transc.cos x * transc.sin y"
  by (import transc SIN_ADD)

lemma COS_ADD: "transc.cos (x + y) =
transc.cos x * transc.cos y - transc.sin x * transc.sin y"
  by (import transc COS_ADD)

lemma SIN_NEG: "transc.sin (- x) = - transc.sin x"
  by (import transc SIN_NEG)

lemma COS_NEG: "transc.cos (- x) = transc.cos x"
  by (import transc COS_NEG)

lemma SIN_DOUBLE: "transc.sin (2 * x) = 2 * (transc.sin x * transc.cos x)"
  by (import transc SIN_DOUBLE)

lemma COS_DOUBLE: "transc.cos (2 * x) = transc.cos x ^ 2 - transc.sin x ^ 2"
  by (import transc COS_DOUBLE)

lemma SIN_PAIRED: "seq.sums (%n. (- 1) ^ n / real (FACT (2 * n + 1)) * x ^ (2 * n + 1))
 (transc.sin x)"
  by (import transc SIN_PAIRED)

lemma SIN_POS: "0 < x & x < 2 ==> 0 < transc.sin x"
  by (import transc SIN_POS)

lemma COS_PAIRED: "seq.sums (%n. (- 1) ^ n / real (FACT (2 * n)) * x ^ (2 * n)) (transc.cos x)"
  by (import transc COS_PAIRED)

lemma COS_2: "transc.cos 2 < 0"
  by (import transc COS_2)

lemma COS_ISZERO: "EX! x. 0 <= x & x <= 2 & transc.cos x = 0"
  by (import transc COS_ISZERO)

consts
  pi :: "real" 

defs
  pi_def: "transc.pi == 2 * (SOME x. 0 <= x & x <= 2 & transc.cos x = 0)"

lemma pi: "transc.pi = 2 * (SOME x. 0 <= x & x <= 2 & transc.cos x = 0)"
  by (import transc pi)

lemma PI2: "transc.pi / 2 = (SOME x. 0 <= x & x <= 2 & transc.cos x = 0)"
  by (import transc PI2)

lemma COS_PI2: "transc.cos (transc.pi / 2) = 0"
  by (import transc COS_PI2)

lemma PI2_BOUNDS: "0 < transc.pi / 2 & transc.pi / 2 < 2"
  by (import transc PI2_BOUNDS)

lemma PI_POS: "0 < transc.pi"
  by (import transc PI_POS)

lemma SIN_PI2: "transc.sin (transc.pi / 2) = 1"
  by (import transc SIN_PI2)

lemma COS_PI: "transc.cos transc.pi = - 1"
  by (import transc COS_PI)

lemma SIN_PI: "transc.sin transc.pi = 0"
  by (import transc SIN_PI)

lemma SIN_COS: "transc.sin x = transc.cos (transc.pi / 2 - x)"
  by (import transc SIN_COS)

lemma COS_SIN: "transc.cos x = transc.sin (transc.pi / 2 - x)"
  by (import transc COS_SIN)

lemma SIN_PERIODIC_PI: "transc.sin (x + transc.pi) = - transc.sin x"
  by (import transc SIN_PERIODIC_PI)

lemma COS_PERIODIC_PI: "transc.cos (x + transc.pi) = - transc.cos x"
  by (import transc COS_PERIODIC_PI)

lemma SIN_PERIODIC: "transc.sin (x + 2 * transc.pi) = transc.sin x"
  by (import transc SIN_PERIODIC)

lemma COS_PERIODIC: "transc.cos (x + 2 * transc.pi) = transc.cos x"
  by (import transc COS_PERIODIC)

lemma COS_NPI: "transc.cos (real n * transc.pi) = (- 1) ^ n"
  by (import transc COS_NPI)

lemma SIN_NPI: "transc.sin (real (n::nat) * transc.pi) = (0::real)"
  by (import transc SIN_NPI)

lemma SIN_POS_PI2: "0 < x & x < transc.pi / 2 ==> 0 < transc.sin x"
  by (import transc SIN_POS_PI2)

lemma COS_POS_PI2: "0 < x & x < transc.pi / 2 ==> 0 < transc.cos x"
  by (import transc COS_POS_PI2)

lemma COS_POS_PI: "- (transc.pi / 2) < x & x < transc.pi / 2 ==> 0 < transc.cos x"
  by (import transc COS_POS_PI)

lemma SIN_POS_PI: "0 < x & x < transc.pi ==> 0 < transc.sin x"
  by (import transc SIN_POS_PI)

lemma COS_POS_PI2_LE: "0 <= x & x <= transc.pi / 2 ==> 0 <= transc.cos x"
  by (import transc COS_POS_PI2_LE)

lemma COS_POS_PI_LE: "- (transc.pi / 2) <= x & x <= transc.pi / 2 ==> 0 <= transc.cos x"
  by (import transc COS_POS_PI_LE)

lemma SIN_POS_PI2_LE: "0 <= x & x <= transc.pi / 2 ==> 0 <= transc.sin x"
  by (import transc SIN_POS_PI2_LE)

lemma SIN_POS_PI_LE: "0 <= x & x <= transc.pi ==> 0 <= transc.sin x"
  by (import transc SIN_POS_PI_LE)

lemma COS_TOTAL: "- 1 <= y & y <= 1 ==> EX! x. 0 <= x & x <= transc.pi & transc.cos x = y"
  by (import transc COS_TOTAL)

lemma SIN_TOTAL: "- 1 <= y & y <= 1
==> EX! x. - (transc.pi / 2) <= x & x <= transc.pi / 2 & transc.sin x = y"
  by (import transc SIN_TOTAL)

lemma COS_ZERO_LEMMA: "0 <= x & transc.cos x = 0 ==> EX n. ~ EVEN n & x = real n * (transc.pi / 2)"
  by (import transc COS_ZERO_LEMMA)

lemma SIN_ZERO_LEMMA: "0 <= x & transc.sin x = 0 ==> EX n. EVEN n & x = real n * (transc.pi / 2)"
  by (import transc SIN_ZERO_LEMMA)

lemma COS_ZERO: "(transc.cos x = 0) =
((EX n. ~ EVEN n & x = real n * (transc.pi / 2)) |
 (EX n. ~ EVEN n & x = - (real n * (transc.pi / 2))))"
  by (import transc COS_ZERO)

lemma SIN_ZERO: "(transc.sin x = 0) =
((EX n. EVEN n & x = real n * (transc.pi / 2)) |
 (EX n. EVEN n & x = - (real n * (transc.pi / 2))))"
  by (import transc SIN_ZERO)

consts
  tan :: "real => real" 

defs
  tan_def: "transc.tan == %x. transc.sin x / transc.cos x"

lemma tan: "transc.tan x = transc.sin x / transc.cos x"
  by (import transc tan)

lemma TAN_0: "transc.tan 0 = 0"
  by (import transc TAN_0)

lemma TAN_PI: "transc.tan transc.pi = 0"
  by (import transc TAN_PI)

lemma TAN_NPI: "transc.tan (real (n::nat) * transc.pi) = (0::real)"
  by (import transc TAN_NPI)

lemma TAN_NEG: "transc.tan (- x) = - transc.tan x"
  by (import transc TAN_NEG)

lemma TAN_PERIODIC: "transc.tan (x + 2 * transc.pi) = transc.tan x"
  by (import transc TAN_PERIODIC)

lemma TAN_ADD: "transc.cos x ~= 0 & transc.cos y ~= 0 & transc.cos (x + y) ~= 0
==> transc.tan (x + y) =
    (transc.tan x + transc.tan y) / (1 - transc.tan x * transc.tan y)"
  by (import transc TAN_ADD)

lemma TAN_DOUBLE: "transc.cos x ~= 0 & transc.cos (2 * x) ~= 0
==> transc.tan (2 * x) = 2 * transc.tan x / (1 - transc.tan x ^ 2)"
  by (import transc TAN_DOUBLE)

lemma TAN_POS_PI2: "0 < x & x < transc.pi / 2 ==> 0 < transc.tan x"
  by (import transc TAN_POS_PI2)

lemma DIFF_TAN: "transc.cos x ~= 0 ==> diffl transc.tan (inverse (transc.cos x ^ 2)) x"
  by (import transc DIFF_TAN)

lemma TAN_TOTAL_LEMMA: "0 < y ==> EX x>0. x < transc.pi / 2 & y < transc.tan x"
  by (import transc TAN_TOTAL_LEMMA)

lemma TAN_TOTAL_POS: "0 <= y ==> EX x>=0. x < transc.pi / 2 & transc.tan x = y"
  by (import transc TAN_TOTAL_POS)

lemma TAN_TOTAL: "EX! x. - (transc.pi / 2) < x & x < transc.pi / 2 & transc.tan x = y"
  by (import transc TAN_TOTAL)

definition
  asn :: "real => real"  where
  "asn ==
%y. SOME x. - (transc.pi / 2) <= x & x <= transc.pi / 2 & transc.sin x = y"

lemma asn: "asn y =
(SOME x. - (transc.pi / 2) <= x & x <= transc.pi / 2 & transc.sin x = y)"
  by (import transc asn)

definition
  acs :: "real => real"  where
  "acs == %y. SOME x. 0 <= x & x <= transc.pi & transc.cos x = y"

lemma acs: "acs y = (SOME x. 0 <= x & x <= transc.pi & transc.cos x = y)"
  by (import transc acs)

definition
  atn :: "real => real"  where
  "atn ==
%y. SOME x. - (transc.pi / 2) < x & x < transc.pi / 2 & transc.tan x = y"

lemma atn: "atn y =
(SOME x. - (transc.pi / 2) < x & x < transc.pi / 2 & transc.tan x = y)"
  by (import transc atn)

lemma ASN: "- 1 <= y & y <= 1
==> - (transc.pi / 2) <= asn y &
    asn y <= transc.pi / 2 & transc.sin (asn y) = y"
  by (import transc ASN)

lemma ASN_SIN: "- 1 <= y & y <= 1 ==> transc.sin (asn y) = y"
  by (import transc ASN_SIN)

lemma ASN_BOUNDS: "- 1 <= y & y <= 1 ==> - (transc.pi / 2) <= asn y & asn y <= transc.pi / 2"
  by (import transc ASN_BOUNDS)

lemma ASN_BOUNDS_LT: "- 1 < y & y < 1 ==> - (transc.pi / 2) < asn y & asn y < transc.pi / 2"
  by (import transc ASN_BOUNDS_LT)

lemma SIN_ASN: "- (transc.pi / 2) <= x & x <= transc.pi / 2 ==> asn (transc.sin x) = x"
  by (import transc SIN_ASN)

lemma ACS: "- 1 <= y & y <= 1
==> 0 <= acs y & acs y <= transc.pi & transc.cos (acs y) = y"
  by (import transc ACS)

lemma ACS_COS: "- 1 <= y & y <= 1 ==> transc.cos (acs y) = y"
  by (import transc ACS_COS)

lemma ACS_BOUNDS: "- 1 <= y & y <= 1 ==> 0 <= acs y & acs y <= transc.pi"
  by (import transc ACS_BOUNDS)

lemma ACS_BOUNDS_LT: "- 1 < y & y < 1 ==> 0 < acs y & acs y < transc.pi"
  by (import transc ACS_BOUNDS_LT)

lemma COS_ACS: "0 <= x & x <= transc.pi ==> acs (transc.cos x) = x"
  by (import transc COS_ACS)

lemma ATN: "- (transc.pi / 2) < atn y & atn y < transc.pi / 2 & transc.tan (atn y) = y"
  by (import transc ATN)

lemma ATN_TAN: "transc.tan (atn x) = x"
  by (import transc ATN_TAN)

lemma ATN_BOUNDS: "- (transc.pi / 2) < atn x & atn x < transc.pi / 2"
  by (import transc ATN_BOUNDS)

lemma TAN_ATN: "- (transc.pi / 2) < x & x < transc.pi / 2 ==> atn (transc.tan x) = x"
  by (import transc TAN_ATN)

lemma TAN_SEC: "transc.cos x ~= 0 ==> 1 + transc.tan x ^ 2 = inverse (transc.cos x) ^ 2"
  by (import transc TAN_SEC)

lemma SIN_COS_SQ: "0 <= x & x <= transc.pi
==> transc.sin x = transc.sqrt (1 - transc.cos x ^ 2)"
  by (import transc SIN_COS_SQ)

lemma COS_SIN_SQ: "- (transc.pi / 2) <= x & x <= transc.pi / 2
==> transc.cos x = transc.sqrt (1 - transc.sin x ^ 2)"
  by (import transc COS_SIN_SQ)

lemma COS_ATN_NZ: "transc.cos (atn x) ~= 0"
  by (import transc COS_ATN_NZ)

lemma COS_ASN_NZ: "- 1 < x & x < 1 ==> transc.cos (asn x) ~= 0"
  by (import transc COS_ASN_NZ)

lemma SIN_ACS_NZ: "- 1 < x & x < 1 ==> transc.sin (acs x) ~= 0"
  by (import transc SIN_ACS_NZ)

lemma COS_SIN_SQRT: "0 <= transc.cos x ==> transc.cos x = transc.sqrt (1 - transc.sin x ^ 2)"
  by (import transc COS_SIN_SQRT)

lemma SIN_COS_SQRT: "0 <= transc.sin x ==> transc.sin x = transc.sqrt (1 - transc.cos x ^ 2)"
  by (import transc SIN_COS_SQRT)

lemma DIFF_LN: "0 < x ==> diffl transc.ln (inverse x) x"
  by (import transc DIFF_LN)

lemma DIFF_ASN_LEMMA: "- 1 < x & x < 1 ==> diffl asn (inverse (transc.cos (asn x))) x"
  by (import transc DIFF_ASN_LEMMA)

lemma DIFF_ASN: "- 1 < x & x < 1 ==> diffl asn (inverse (transc.sqrt (1 - x ^ 2))) x"
  by (import transc DIFF_ASN)

lemma DIFF_ACS_LEMMA: "- 1 < x & x < 1 ==> diffl acs (inverse (- transc.sin (acs x))) x"
  by (import transc DIFF_ACS_LEMMA)

lemma DIFF_ACS: "- 1 < x & x < 1 ==> diffl acs (- inverse (transc.sqrt (1 - x ^ 2))) x"
  by (import transc DIFF_ACS)

lemma DIFF_ATN: "diffl atn (inverse (1 + x ^ 2)) x"
  by (import transc DIFF_ATN)

definition
  division :: "real * real => (nat => real) => bool"  where
  "division ==
%(a, b) D.
   D 0 = a & (EX N. (ALL n<N. D n < D (Suc n)) & (ALL n>=N. D n = b))"

lemma division: "division (a, b) D =
(D 0 = a & (EX N. (ALL n<N. D n < D (Suc n)) & (ALL n>=N. D n = b)))"
  by (import transc division)

definition
  dsize :: "(nat => real) => nat"  where
  "dsize == %D. SOME N. (ALL n<N. D n < D (Suc n)) & (ALL n>=N. D n = D N)"

lemma dsize: "dsize D = (SOME N. (ALL n<N. D n < D (Suc n)) & (ALL n>=N. D n = D N))"
  by (import transc dsize)

definition
  tdiv :: "real * real => (nat => real) * (nat => real) => bool"  where
  "tdiv ==
%(a, b) (D, p). division (a, b) D & (ALL n. D n <= p n & p n <= D (Suc n))"

lemma tdiv: "tdiv (a, b) (D, p) =
(division (a, b) D & (ALL n. D n <= p n & p n <= D (Suc n)))"
  by (import transc tdiv)

definition
  gauge :: "(real => bool) => (real => real) => bool"  where
  "gauge == %E g. ALL x. E x --> 0 < g x"

lemma gauge: "gauge E g = (ALL x. E x --> 0 < g x)"
  by (import transc gauge)

definition
  fine :: "(real => real) => (nat => real) * (nat => real) => bool"  where
  "fine == %g (D, p). ALL n<dsize D. D (Suc n) - D n < g (p n)"

lemma fine: "fine g (D, p) = (ALL n<dsize D. D (Suc n) - D n < g (p n))"
  by (import transc fine)

definition
  rsum :: "(nat => real) * (nat => real) => (real => real) => real"  where
  "rsum == %(D, p) f. real.sum (0, dsize D) (%n. f (p n) * (D (Suc n) - D n))"

lemma rsum: "rsum (D, p) f = real.sum (0, dsize D) (%n. f (p n) * (D (Suc n) - D n))"
  by (import transc rsum)

definition
  Dint :: "real * real => (real => real) => real => bool"  where
  "Dint ==
%(a, b) f k.
   ALL e>0.
      EX g. gauge (%x. a <= x & x <= b) g &
            (ALL D p.
                tdiv (a, b) (D, p) & fine g (D, p) -->
                abs (rsum (D, p) f - k) < e)"

lemma Dint: "Dint (a, b) f k =
(ALL e>0.
    EX g. gauge (%x. a <= x & x <= b) g &
          (ALL D p.
              tdiv (a, b) (D, p) & fine g (D, p) -->
              abs (rsum (D, p) f - k) < e))"
  by (import transc Dint)

lemma DIVISION_0: "a = b ==> dsize (%n. if n = 0 then a else b) = 0"
  by (import transc DIVISION_0)

lemma DIVISION_1: "a < b ==> dsize (%n. if n = 0 then a else b) = 1"
  by (import transc DIVISION_1)

lemma DIVISION_SINGLE: "a <= b ==> division (a, b) (%n. if n = 0 then a else b)"
  by (import transc DIVISION_SINGLE)

lemma DIVISION_LHS: "division (a, b) D ==> D 0 = a"
  by (import transc DIVISION_LHS)

lemma DIVISION_THM: "division (a, b) D =
(D 0 = a & (ALL n<dsize D. D n < D (Suc n)) & (ALL n>=dsize D. D n = b))"
  by (import transc DIVISION_THM)

lemma DIVISION_RHS: "division (a, b) D ==> D (dsize D) = b"
  by (import transc DIVISION_RHS)

lemma DIVISION_LT_GEN: "division (a, b) D & m < n & n <= dsize D ==> D m < D n"
  by (import transc DIVISION_LT_GEN)

lemma DIVISION_LT: "[| division (a, b) D; n < dsize D |] ==> D 0 < D (Suc n)"
  by (import transc DIVISION_LT)

lemma DIVISION_LE: "division (a, b) D ==> a <= b"
  by (import transc DIVISION_LE)

lemma DIVISION_GT: "[| division (a, b) D; n < dsize D |] ==> D n < D (dsize D)"
  by (import transc DIVISION_GT)

lemma DIVISION_EQ: "division (a, b) D ==> (a = b) = (dsize D = 0)"
  by (import transc DIVISION_EQ)

lemma DIVISION_LBOUND: "division (a, b) D ==> a <= D r"
  by (import transc DIVISION_LBOUND)

lemma DIVISION_LBOUND_LT: "division (a, b) D & dsize D ~= 0 ==> a < D (Suc n)"
  by (import transc DIVISION_LBOUND_LT)

lemma DIVISION_UBOUND: "division (a, b) D ==> D r <= b"
  by (import transc DIVISION_UBOUND)

lemma DIVISION_UBOUND_LT: "division (a, b) D & n < dsize D ==> D n < b"
  by (import transc DIVISION_UBOUND_LT)

lemma DIVISION_APPEND: "(EX D1 p1. tdiv (a, b) (D1, p1) & fine g (D1, p1)) &
(EX D2 p2. tdiv (b, c) (D2, p2) & fine g (D2, p2))
==> EX x p. tdiv (a, c) (x, p) & fine g (x, p)"
  by (import transc DIVISION_APPEND)

lemma DIVISION_EXISTS: "a <= b & gauge (%x. a <= x & x <= b) g
==> EX D p. tdiv (a, b) (D, p) & fine g (D, p)"
  by (import transc DIVISION_EXISTS)

lemma GAUGE_MIN: "gauge E g1 & gauge E g2 ==> gauge E (%x. if g1 x < g2 x then g1 x else g2 x)"
  by (import transc GAUGE_MIN)

lemma FINE_MIN: "fine (%x. if g1 x < g2 x then g1 x else g2 x) (D, p)
==> fine g1 (D, p) & fine g2 (D, p)"
  by (import transc FINE_MIN)

lemma DINT_UNIQ: "a <= b & Dint (a, b) f k1 & Dint (a, b) f k2 ==> k1 = k2"
  by (import transc DINT_UNIQ)

lemma INTEGRAL_NULL: "Dint (a, a) f 0"
  by (import transc INTEGRAL_NULL)

lemma FTC1: "a <= b & (ALL x. a <= x & x <= b --> diffl f (f' x) x)
==> Dint (a, b) f' (f b - f a)"
  by (import transc FTC1)

lemma MCLAURIN: "0 < h &
0 < n &
diff 0 = f &
(ALL m t. m < n & 0 <= t & t <= h --> diffl (diff m) (diff (Suc m) t) t)
==> EX t>0.
       t < h &
       f h =
       real.sum (0, n) (%m. diff m 0 / real (FACT m) * h ^ m) +
       diff n t / real (FACT n) * h ^ n"
  by (import transc MCLAURIN)

lemma MCLAURIN_NEG: "h < 0 &
0 < n &
diff 0 = f &
(ALL m t. m < n & h <= t & t <= 0 --> diffl (diff m) (diff (Suc m) t) t)
==> EX t>h.
       t < 0 &
       f h =
       real.sum (0, n) (%m. diff m 0 / real (FACT m) * h ^ m) +
       diff n t / real (FACT n) * h ^ n"
  by (import transc MCLAURIN_NEG)

lemma MCLAURIN_ALL_LT: "[| diff 0 = f & (ALL m x. diffl (diff m) (diff (Suc m) x) x);
   x ~= 0 & 0 < n |]
==> EX t. 0 < abs t &
          abs t < abs x &
          f x =
          real.sum (0, n) (%m. diff m 0 / real (FACT m) * x ^ m) +
          diff n t / real (FACT n) * x ^ n"
  by (import transc MCLAURIN_ALL_LT)

lemma MCLAURIN_ZERO: "(x::real) = (0::real) & (0::nat) < (n::nat)
==> real.sum (0::nat, n)
     (%m::nat.
         (diff::nat => real => real) m (0::real) / real (FACT m) * x ^ m) =
    diff (0::nat) (0::real)"
  by (import transc MCLAURIN_ZERO)

lemma MCLAURIN_ALL_LE: "diff 0 = f & (ALL m x. diffl (diff m) (diff (Suc m) x) x)
==> EX t. abs t <= abs x &
          f x =
          real.sum (0, n) (%m. diff m 0 / real (FACT m) * x ^ m) +
          diff n t / real (FACT n) * x ^ n"
  by (import transc MCLAURIN_ALL_LE)

lemma MCLAURIN_EXP_LT: "x ~= 0 & 0 < n
==> EX xa.
       0 < abs xa &
       abs xa < abs x &
       transc.exp x =
       real.sum (0, n) (%m. x ^ m / real (FACT m)) +
       transc.exp xa / real (FACT n) * x ^ n"
  by (import transc MCLAURIN_EXP_LT)

lemma MCLAURIN_EXP_LE: "EX xa.
   abs xa <= abs x &
   transc.exp x =
   real.sum (0, n) (%m. x ^ m / real (FACT m)) +
   transc.exp xa / real (FACT n) * x ^ n"
  by (import transc MCLAURIN_EXP_LE)

lemma DIFF_LN_COMPOSITE: "diffl g m x & 0 < g x ==> diffl (%x. transc.ln (g x)) (inverse (g x) * m) x"
  by (import transc DIFF_LN_COMPOSITE)

;end_setup

setup_theory "~~/src/HOL/Import/HOL" poly

consts
  poly :: "real list => real => real" 

specification (poly_primdef: poly) poly_def: "(ALL x. poly [] x = 0) & (ALL h t x. poly (h # t) x = h + x * poly t x)"
  by (import poly poly_def)

consts
  poly_add :: "real list => real list => real list" 

specification (poly_add_primdef: poly_add) poly_add_def: "(ALL l2. poly_add [] l2 = l2) &
(ALL h t l2.
    poly_add (h # t) l2 =
    (if l2 = [] then h # t else (h + hd l2) # poly_add t (tl l2)))"
  by (import poly poly_add_def)

consts
  "##" :: "real => real list => real list" ("##")

specification ("##") poly_cmul_def: "(ALL c. ## c [] = []) & (ALL c h t. ## c (h # t) = c * h # ## c t)"
  by (import poly poly_cmul_def)

consts
  poly_neg :: "real list => real list" 

defs
  poly_neg_primdef: "poly_neg == ## (- 1)"

lemma poly_neg_def: "poly_neg = ## (- 1)"
  by (import poly poly_neg_def)

consts
  poly_mul :: "real list => real list => real list" 

specification (poly_mul_primdef: poly_mul) poly_mul_def: "(ALL l2. poly_mul [] l2 = []) &
(ALL h t l2.
    poly_mul (h # t) l2 =
    (if t = [] then ## h l2 else poly_add (## h l2) (0 # poly_mul t l2)))"
  by (import poly poly_mul_def)

consts
  poly_exp :: "real list => nat => real list" 

specification (poly_exp_primdef: poly_exp) poly_exp_def: "(ALL p. poly_exp p 0 = [1]) &
(ALL p n. poly_exp p (Suc n) = poly_mul p (poly_exp p n))"
  by (import poly poly_exp_def)

consts
  poly_diff_aux :: "nat => real list => real list" 

specification (poly_diff_aux_primdef: poly_diff_aux) poly_diff_aux_def: "(ALL n. poly_diff_aux n [] = []) &
(ALL n h t. poly_diff_aux n (h # t) = real n * h # poly_diff_aux (Suc n) t)"
  by (import poly poly_diff_aux_def)

definition
  diff :: "real list => real list"  where
  "diff == %l. if l = [] then [] else poly_diff_aux 1 (tl l)"

lemma poly_diff_def: "diff l = (if l = [] then [] else poly_diff_aux 1 (tl l))"
  by (import poly poly_diff_def)

lemma POLY_ADD_CLAUSES: "poly_add [] p2 = p2 &
poly_add p1 [] = p1 &
poly_add (h1 # t1) (h2 # t2) = (h1 + h2) # poly_add t1 t2"
  by (import poly POLY_ADD_CLAUSES)

lemma POLY_CMUL_CLAUSES: "## c [] = [] & ## c (h # t) = c * h # ## c t"
  by (import poly POLY_CMUL_CLAUSES)

lemma POLY_NEG_CLAUSES: "poly_neg [] = [] & poly_neg (h # t) = - h # poly_neg t"
  by (import poly POLY_NEG_CLAUSES)

lemma POLY_MUL_CLAUSES: "poly_mul [] p2 = [] &
poly_mul [h1] p2 = ## h1 p2 &
poly_mul (h1 # k1 # t1) p2 = poly_add (## h1 p2) (0 # poly_mul (k1 # t1) p2)"
  by (import poly POLY_MUL_CLAUSES)

lemma POLY_DIFF_CLAUSES: "diff [] = [] & diff [c] = [] & diff (h # t) = poly_diff_aux 1 t"
  by (import poly POLY_DIFF_CLAUSES)

lemma POLY_ADD: "poly (poly_add t p2) x = poly t x + poly p2 x"
  by (import poly POLY_ADD)

lemma POLY_CMUL: "poly (## c t) x = c * poly t x"
  by (import poly POLY_CMUL)

lemma POLY_NEG: "poly (poly_neg x) xa = - poly x xa"
  by (import poly POLY_NEG)

lemma POLY_MUL: "poly (poly_mul t p2) x = poly t x * poly p2 x"
  by (import poly POLY_MUL)

lemma POLY_EXP: "poly (poly_exp p n) x = poly p x ^ n"
  by (import poly POLY_EXP)

lemma POLY_DIFF_LEMMA: "diffl (%x. x ^ Suc n * poly t x) (x ^ n * poly (poly_diff_aux (Suc n) t) x)
 x"
  by (import poly POLY_DIFF_LEMMA)

lemma POLY_DIFF: "diffl (poly t) (poly (diff t) x) x"
  by (import poly POLY_DIFF)

lemma POLY_DIFFERENTIABLE: "lim.differentiable (poly l) x"
  by (import poly POLY_DIFFERENTIABLE)

lemma POLY_CONT: "contl (poly l) x"
  by (import poly POLY_CONT)

lemma POLY_IVT_POS: "xa < xb & poly x xa < 0 & 0 < poly x xb
==> EX xc>xa. xc < xb & poly x xc = 0"
  by (import poly POLY_IVT_POS)

lemma POLY_IVT_NEG: "a < b & 0 < poly p a & poly p b < 0 ==> EX x>a. x < b & poly p x = 0"
  by (import poly POLY_IVT_NEG)

lemma POLY_MVT: "a < b ==> EX x>a. x < b & poly p b - poly p a = (b - a) * poly (diff p) x"
  by (import poly POLY_MVT)

lemma POLY_ADD_RZERO: "poly (poly_add x []) = poly x"
  by (import poly POLY_ADD_RZERO)

lemma POLY_MUL_ASSOC: "poly (poly_mul x (poly_mul xa xb)) = poly (poly_mul (poly_mul x xa) xb)"
  by (import poly POLY_MUL_ASSOC)

lemma POLY_EXP_ADD: "poly (poly_exp xb (xa + x)) =
poly (poly_mul (poly_exp xb xa) (poly_exp xb x))"
  by (import poly POLY_EXP_ADD)

lemma POLY_DIFF_AUX_ADD: "poly (poly_diff_aux n (poly_add t p2)) =
poly (poly_add (poly_diff_aux n t) (poly_diff_aux n p2))"
  by (import poly POLY_DIFF_AUX_ADD)

lemma POLY_DIFF_AUX_CMUL: "poly (poly_diff_aux n (## c t)) = poly (## c (poly_diff_aux n t))"
  by (import poly POLY_DIFF_AUX_CMUL)

lemma POLY_DIFF_AUX_NEG: "poly (poly_diff_aux xa (poly_neg x)) = poly (poly_neg (poly_diff_aux xa x))"
  by (import poly POLY_DIFF_AUX_NEG)

lemma POLY_DIFF_AUX_MUL_LEMMA: "poly (poly_diff_aux (Suc n) t) = poly (poly_add (poly_diff_aux n t) t)"
  by (import poly POLY_DIFF_AUX_MUL_LEMMA)

lemma POLY_DIFF_ADD: "poly (diff (poly_add t p2)) = poly (poly_add (diff t) (diff p2))"
  by (import poly POLY_DIFF_ADD)

lemma POLY_DIFF_CMUL: "poly (diff (## c t)) = poly (## c (diff t))"
  by (import poly POLY_DIFF_CMUL)

lemma POLY_DIFF_NEG: "poly (diff (poly_neg x)) = poly (poly_neg (diff x))"
  by (import poly POLY_DIFF_NEG)

lemma POLY_DIFF_MUL_LEMMA: "poly (diff (xa # x)) = poly (poly_add (0 # diff x) x)"
  by (import poly POLY_DIFF_MUL_LEMMA)

lemma POLY_DIFF_MUL: "poly (diff (poly_mul t p2)) =
poly (poly_add (poly_mul t (diff p2)) (poly_mul (diff t) p2))"
  by (import poly POLY_DIFF_MUL)

lemma POLY_DIFF_EXP: "poly (diff (poly_exp p (Suc n))) =
poly (poly_mul (## (real (Suc n)) (poly_exp p n)) (diff p))"
  by (import poly POLY_DIFF_EXP)

lemma POLY_DIFF_EXP_PRIME: "poly (diff (poly_exp [- a, 1] (Suc n))) =
poly (## (real (Suc n)) (poly_exp [- a, 1] n))"
  by (import poly POLY_DIFF_EXP_PRIME)

lemma POLY_LINEAR_REM: "EX q r. h # t = poly_add [r] (poly_mul [- a, 1] q)"
  by (import poly POLY_LINEAR_REM)

lemma POLY_LINEAR_DIVIDES: "(poly t a = 0) = (t = [] | (EX q. t = poly_mul [- a, 1] q))"
  by (import poly POLY_LINEAR_DIVIDES)

lemma POLY_LENGTH_MUL: "length (poly_mul [- a, 1] x) = Suc (length x)"
  by (import poly POLY_LENGTH_MUL)

lemma POLY_ROOTS_INDEX_LEMMA: "poly p ~= poly [] & length p = n
==> EX i. ALL x. poly p x = 0 --> (EX m<=n. x = i m)"
  by (import poly POLY_ROOTS_INDEX_LEMMA)

lemma POLY_ROOTS_INDEX_LENGTH: "poly p ~= poly []
==> EX i. ALL x. poly p x = 0 --> (EX n<=length p. x = i n)"
  by (import poly POLY_ROOTS_INDEX_LENGTH)

lemma POLY_ROOTS_FINITE_LEMMA: "poly (p::real list) ~= poly []
==> EX (N::nat) i::nat => real.
       ALL x::real. poly p x = (0::real) --> (EX n<N. x = i n)"
  by (import poly POLY_ROOTS_FINITE_LEMMA)

lemma FINITE_LEMMA: "(!!xb::real. (xa::real => bool) xb ==> EX n<x::nat. xb = (i::nat => real) n)
==> EX a::real. ALL x::real. xa x --> x < a"
  by (import poly FINITE_LEMMA)

lemma POLY_ROOTS_FINITE: "(poly (p::real list) ~= poly []) =
(EX (N::nat) i::nat => real.
    ALL x::real. poly p x = (0::real) --> (EX n<N. x = i n))"
  by (import poly POLY_ROOTS_FINITE)

lemma POLY_ENTIRE_LEMMA: "poly p ~= poly [] & poly q ~= poly [] ==> poly (poly_mul p q) ~= poly []"
  by (import poly POLY_ENTIRE_LEMMA)

lemma POLY_ENTIRE: "(poly (poly_mul p q) = poly []) = (poly p = poly [] | poly q = poly [])"
  by (import poly POLY_ENTIRE)

lemma POLY_MUL_LCANCEL: "(poly (poly_mul x xa) = poly (poly_mul x xb)) =
(poly x = poly [] | poly xa = poly xb)"
  by (import poly POLY_MUL_LCANCEL)

lemma POLY_EXP_EQ_0: "(poly (poly_exp p n) = poly []) = (poly p = poly [] & n ~= 0)"
  by (import poly POLY_EXP_EQ_0)

lemma POLY_PRIME_EQ_0: "poly [a, 1] ~= poly []"
  by (import poly POLY_PRIME_EQ_0)

lemma POLY_EXP_PRIME_EQ_0: "poly (poly_exp [a, 1] n) ~= poly []"
  by (import poly POLY_EXP_PRIME_EQ_0)

lemma POLY_ZERO_LEMMA: "poly (h # t) = poly [] ==> h = 0 & poly t = poly []"
  by (import poly POLY_ZERO_LEMMA)

lemma POLY_ZERO: "(poly t = poly []) = list_all (%c. c = 0) t"
  by (import poly POLY_ZERO)

lemma POLY_DIFF_AUX_ISZERO: "list_all (%c. c = 0) (poly_diff_aux (Suc n) t) = list_all (%c. c = 0) t"
  by (import poly POLY_DIFF_AUX_ISZERO)

lemma POLY_DIFF_ISZERO: "poly (diff x) = poly [] ==> EX h. poly x = poly [h]"
  by (import poly POLY_DIFF_ISZERO)

lemma POLY_DIFF_ZERO: "poly x = poly [] ==> poly (diff x) = poly []"
  by (import poly POLY_DIFF_ZERO)

lemma POLY_DIFF_WELLDEF: "poly p = poly q ==> poly (diff p) = poly (diff q)"
  by (import poly POLY_DIFF_WELLDEF)

definition
  poly_divides :: "real list => real list => bool"  where
  "poly_divides == %p1 p2. EX q. poly p2 = poly (poly_mul p1 q)"

lemma poly_divides: "poly_divides p1 p2 = (EX q. poly p2 = poly (poly_mul p1 q))"
  by (import poly poly_divides)

lemma POLY_PRIMES: "poly_divides [a, 1] (poly_mul p q) =
(poly_divides [a, 1] p | poly_divides [a, 1] q)"
  by (import poly POLY_PRIMES)

lemma POLY_DIVIDES_REFL: "poly_divides p p"
  by (import poly POLY_DIVIDES_REFL)

lemma POLY_DIVIDES_TRANS: "poly_divides p q & poly_divides q r ==> poly_divides p r"
  by (import poly POLY_DIVIDES_TRANS)

lemma POLY_DIVIDES_EXP: "m <= n ==> poly_divides (poly_exp p m) (poly_exp p n)"
  by (import poly POLY_DIVIDES_EXP)

lemma POLY_EXP_DIVIDES: "poly_divides (poly_exp p n) q & m <= n ==> poly_divides (poly_exp p m) q"
  by (import poly POLY_EXP_DIVIDES)

lemma POLY_DIVIDES_ADD: "poly_divides p q & poly_divides p r ==> poly_divides p (poly_add q r)"
  by (import poly POLY_DIVIDES_ADD)

lemma POLY_DIVIDES_SUB: "poly_divides p q & poly_divides p (poly_add q r) ==> poly_divides p r"
  by (import poly POLY_DIVIDES_SUB)

lemma POLY_DIVIDES_SUB2: "poly_divides p r & poly_divides p (poly_add q r) ==> poly_divides p q"
  by (import poly POLY_DIVIDES_SUB2)

lemma POLY_DIVIDES_ZERO: "poly p = poly [] ==> poly_divides q p"
  by (import poly POLY_DIVIDES_ZERO)

lemma POLY_ORDER_EXISTS: "length p = d & poly p ~= poly []
==> EX x. poly_divides (poly_exp [- a, 1] x) p &
          ~ poly_divides (poly_exp [- a, 1] (Suc x)) p"
  by (import poly POLY_ORDER_EXISTS)

lemma POLY_ORDER: "poly p ~= poly []
==> EX! n.
       poly_divides (poly_exp [- a, 1] n) p &
       ~ poly_divides (poly_exp [- a, 1] (Suc n)) p"
  by (import poly POLY_ORDER)

definition
  poly_order :: "real => real list => nat"  where
  "poly_order ==
%a p. SOME n.
         poly_divides (poly_exp [- a, 1] n) p &
         ~ poly_divides (poly_exp [- a, 1] (Suc n)) p"

lemma poly_order: "poly_order a p =
(SOME n.
    poly_divides (poly_exp [- a, 1] n) p &
    ~ poly_divides (poly_exp [- a, 1] (Suc n)) p)"
  by (import poly poly_order)

lemma ORDER: "(poly_divides (poly_exp [- a, 1] n) p &
 ~ poly_divides (poly_exp [- a, 1] (Suc n)) p) =
(n = poly_order a p & poly p ~= poly [])"
  by (import poly ORDER)

lemma ORDER_THM: "poly p ~= poly []
==> poly_divides (poly_exp [- a, 1] (poly_order a p)) p &
    ~ poly_divides (poly_exp [- a, 1] (Suc (poly_order a p))) p"
  by (import poly ORDER_THM)

lemma ORDER_UNIQUE: "poly p ~= poly [] &
poly_divides (poly_exp [- a, 1] n) p &
~ poly_divides (poly_exp [- a, 1] (Suc n)) p
==> n = poly_order a p"
  by (import poly ORDER_UNIQUE)

lemma ORDER_POLY: "poly p = poly q ==> poly_order a p = poly_order a q"
  by (import poly ORDER_POLY)

lemma ORDER_ROOT: "(poly p a = 0) = (poly p = poly [] | poly_order a p ~= 0)"
  by (import poly ORDER_ROOT)

lemma ORDER_DIVIDES: "poly_divides (poly_exp [- a, 1] n) p =
(poly p = poly [] | n <= poly_order a p)"
  by (import poly ORDER_DIVIDES)

lemma ORDER_DECOMP: "poly p ~= poly []
==> EX x. poly p = poly (poly_mul (poly_exp [- a, 1] (poly_order a p)) x) &
          ~ poly_divides [- a, 1] x"
  by (import poly ORDER_DECOMP)

lemma ORDER_MUL: "poly (poly_mul p q) ~= poly []
==> poly_order a (poly_mul p q) = poly_order a p + poly_order a q"
  by (import poly ORDER_MUL)

lemma ORDER_DIFF: "poly (diff p) ~= poly [] & poly_order a p ~= 0
==> poly_order a p = Suc (poly_order a (diff p))"
  by (import poly ORDER_DIFF)

lemma POLY_SQUAREFREE_DECOMP_ORDER: "poly (diff p) ~= poly [] &
poly p = poly (poly_mul q d) &
poly (diff p) = poly (poly_mul e d) &
poly d = poly (poly_add (poly_mul r p) (poly_mul s (diff p)))
==> poly_order a q = (if poly_order a p = 0 then 0 else 1)"
  by (import poly POLY_SQUAREFREE_DECOMP_ORDER)

definition
  rsquarefree :: "real list => bool"  where
  "rsquarefree ==
%p. poly p ~= poly [] & (ALL a. poly_order a p = 0 | poly_order a p = 1)"

lemma rsquarefree: "rsquarefree p =
(poly p ~= poly [] & (ALL a. poly_order a p = 0 | poly_order a p = 1))"
  by (import poly rsquarefree)

lemma RSQUAREFREE_ROOTS: "rsquarefree p = (ALL a. ~ (poly p a = 0 & poly (diff p) a = 0))"
  by (import poly RSQUAREFREE_ROOTS)

lemma RSQUAREFREE_DECOMP: "rsquarefree p & poly p a = 0
==> EX q. poly p = poly (poly_mul [- a, 1] q) & poly q a ~= 0"
  by (import poly RSQUAREFREE_DECOMP)

lemma POLY_SQUAREFREE_DECOMP: "poly (diff p) ~= poly [] &
poly p = poly (poly_mul q d) &
poly (diff p) = poly (poly_mul e d) &
poly d = poly (poly_add (poly_mul r p) (poly_mul s (diff p)))
==> rsquarefree q & (ALL x. (poly q x = 0) = (poly p x = 0))"
  by (import poly POLY_SQUAREFREE_DECOMP)

consts
  normalize :: "real list => real list" 

specification (normalize) normalize: "normalize [] = [] &
(ALL h t.
    normalize (h # t) =
    (if normalize t = [] then if h = 0 then [] else [h]
     else h # normalize t))"
  by (import poly normalize)

lemma POLY_NORMALIZE: "poly (normalize t) = poly t"
  by (import poly POLY_NORMALIZE)

definition
  degree :: "real list => nat"  where
  "degree == %p. PRE (length (normalize p))"

lemma degree: "degree p = PRE (length (normalize p))"
  by (import poly degree)

lemma DEGREE_ZERO: "poly p = poly [] ==> degree p = 0"
  by (import poly DEGREE_ZERO)

lemma POLY_ROOTS_FINITE_SET: "poly p ~= poly [] ==> FINITE (GSPEC (%x. (x, poly p x = 0)))"
  by (import poly POLY_ROOTS_FINITE_SET)

lemma POLY_MONO: "abs x <= k ==> abs (poly xa x) <= poly (map abs xa) k"
  by (import poly POLY_MONO)

;end_setup

end

