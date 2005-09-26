(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOL4Real imports HOL4Base begin

;setup_theory realax

lemma HREAL_RDISTRIB: "ALL (x::hreal) (y::hreal) z::hreal.
   hreal_mul (hreal_add x y) z = hreal_add (hreal_mul x z) (hreal_mul y z)"
  by (import realax HREAL_RDISTRIB)

lemma HREAL_EQ_ADDL: "ALL (x::hreal) y::hreal. x ~= hreal_add x y"
  by (import realax HREAL_EQ_ADDL)

lemma HREAL_EQ_LADD: "ALL (x::hreal) (y::hreal) z::hreal.
   (hreal_add x y = hreal_add x z) = (y = z)"
  by (import realax HREAL_EQ_LADD)

lemma HREAL_LT_REFL: "ALL x::hreal. ~ hreal_lt x x"
  by (import realax HREAL_LT_REFL)

lemma HREAL_LT_ADDL: "ALL (x::hreal) y::hreal. hreal_lt x (hreal_add x y)"
  by (import realax HREAL_LT_ADDL)

lemma HREAL_LT_NE: "ALL (x::hreal) y::hreal. hreal_lt x y --> x ~= y"
  by (import realax HREAL_LT_NE)

lemma HREAL_LT_ADDR: "ALL (x::hreal) y::hreal. ~ hreal_lt (hreal_add x y) x"
  by (import realax HREAL_LT_ADDR)

lemma HREAL_LT_GT: "ALL (x::hreal) y::hreal. hreal_lt x y --> ~ hreal_lt y x"
  by (import realax HREAL_LT_GT)

lemma HREAL_LT_ADD2: "ALL (x1::hreal) (x2::hreal) (y1::hreal) y2::hreal.
   hreal_lt x1 y1 & hreal_lt x2 y2 -->
   hreal_lt (hreal_add x1 x2) (hreal_add y1 y2)"
  by (import realax HREAL_LT_ADD2)

lemma HREAL_LT_LADD: "ALL (x::hreal) (y::hreal) z::hreal.
   hreal_lt (hreal_add x y) (hreal_add x z) = hreal_lt y z"
  by (import realax HREAL_LT_LADD)

constdefs
  treal_0 :: "hreal * hreal" 
  "treal_0 == (hreal_1, hreal_1)"

lemma treal_0: "treal_0 = (hreal_1, hreal_1)"
  by (import realax treal_0)

constdefs
  treal_1 :: "hreal * hreal" 
  "treal_1 == (hreal_add hreal_1 hreal_1, hreal_1)"

lemma treal_1: "treal_1 = (hreal_add hreal_1 hreal_1, hreal_1)"
  by (import realax treal_1)

constdefs
  treal_neg :: "hreal * hreal => hreal * hreal" 
  "treal_neg == %(x::hreal, y::hreal). (y, x)"

lemma treal_neg: "ALL (x::hreal) y::hreal. treal_neg (x, y) = (y, x)"
  by (import realax treal_neg)

constdefs
  treal_add :: "hreal * hreal => hreal * hreal => hreal * hreal" 
  "treal_add ==
%(x1::hreal, y1::hreal) (x2::hreal, y2::hreal).
   (hreal_add x1 x2, hreal_add y1 y2)"

lemma treal_add: "ALL (x1::hreal) (y1::hreal) (x2::hreal) y2::hreal.
   treal_add (x1, y1) (x2, y2) = (hreal_add x1 x2, hreal_add y1 y2)"
  by (import realax treal_add)

constdefs
  treal_mul :: "hreal * hreal => hreal * hreal => hreal * hreal" 
  "treal_mul ==
%(x1::hreal, y1::hreal) (x2::hreal, y2::hreal).
   (hreal_add (hreal_mul x1 x2) (hreal_mul y1 y2),
    hreal_add (hreal_mul x1 y2) (hreal_mul y1 x2))"

lemma treal_mul: "ALL (x1::hreal) (y1::hreal) (x2::hreal) y2::hreal.
   treal_mul (x1, y1) (x2, y2) =
   (hreal_add (hreal_mul x1 x2) (hreal_mul y1 y2),
    hreal_add (hreal_mul x1 y2) (hreal_mul y1 x2))"
  by (import realax treal_mul)

constdefs
  treal_lt :: "hreal * hreal => hreal * hreal => bool" 
  "treal_lt ==
%(x1::hreal, y1::hreal) (x2::hreal, y2::hreal).
   hreal_lt (hreal_add x1 y2) (hreal_add x2 y1)"

lemma treal_lt: "ALL (x1::hreal) (y1::hreal) (x2::hreal) y2::hreal.
   treal_lt (x1, y1) (x2, y2) = hreal_lt (hreal_add x1 y2) (hreal_add x2 y1)"
  by (import realax treal_lt)

constdefs
  treal_inv :: "hreal * hreal => hreal * hreal" 
  "treal_inv ==
%(x::hreal, y::hreal).
   if x = y then treal_0
   else if hreal_lt y x
        then (hreal_add (hreal_inv (hreal_sub x y)) hreal_1, hreal_1)
        else (hreal_1, hreal_add (hreal_inv (hreal_sub y x)) hreal_1)"

lemma treal_inv: "ALL (x::hreal) y::hreal.
   treal_inv (x, y) =
   (if x = y then treal_0
    else if hreal_lt y x
         then (hreal_add (hreal_inv (hreal_sub x y)) hreal_1, hreal_1)
         else (hreal_1, hreal_add (hreal_inv (hreal_sub y x)) hreal_1))"
  by (import realax treal_inv)

constdefs
  treal_eq :: "hreal * hreal => hreal * hreal => bool" 
  "treal_eq ==
%(x1::hreal, y1::hreal) (x2::hreal, y2::hreal).
   hreal_add x1 y2 = hreal_add x2 y1"

lemma treal_eq: "ALL (x1::hreal) (y1::hreal) (x2::hreal) y2::hreal.
   treal_eq (x1, y1) (x2, y2) = (hreal_add x1 y2 = hreal_add x2 y1)"
  by (import realax treal_eq)

lemma TREAL_EQ_REFL: "ALL x::hreal * hreal. treal_eq x x"
  by (import realax TREAL_EQ_REFL)

lemma TREAL_EQ_SYM: "ALL (x::hreal * hreal) y::hreal * hreal. treal_eq x y = treal_eq y x"
  by (import realax TREAL_EQ_SYM)

lemma TREAL_EQ_TRANS: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_eq x y & treal_eq y z --> treal_eq x z"
  by (import realax TREAL_EQ_TRANS)

lemma TREAL_EQ_EQUIV: "ALL (p::hreal * hreal) q::hreal * hreal.
   treal_eq p q = (treal_eq p = treal_eq q)"
  by (import realax TREAL_EQ_EQUIV)

lemma TREAL_EQ_AP: "ALL (p::hreal * hreal) q::hreal * hreal. p = q --> treal_eq p q"
  by (import realax TREAL_EQ_AP)

lemma TREAL_10: "~ treal_eq treal_1 treal_0"
  by (import realax TREAL_10)

lemma TREAL_ADD_SYM: "ALL (x::hreal * hreal) y::hreal * hreal. treal_add x y = treal_add y x"
  by (import realax TREAL_ADD_SYM)

lemma TREAL_MUL_SYM: "ALL (x::hreal * hreal) y::hreal * hreal. treal_mul x y = treal_mul y x"
  by (import realax TREAL_MUL_SYM)

lemma TREAL_ADD_ASSOC: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_add x (treal_add y z) = treal_add (treal_add x y) z"
  by (import realax TREAL_ADD_ASSOC)

lemma TREAL_MUL_ASSOC: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_mul x (treal_mul y z) = treal_mul (treal_mul x y) z"
  by (import realax TREAL_MUL_ASSOC)

lemma TREAL_LDISTRIB: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_mul x (treal_add y z) = treal_add (treal_mul x y) (treal_mul x z)"
  by (import realax TREAL_LDISTRIB)

lemma TREAL_ADD_LID: "ALL x::hreal * hreal. treal_eq (treal_add treal_0 x) x"
  by (import realax TREAL_ADD_LID)

lemma TREAL_MUL_LID: "ALL x::hreal * hreal. treal_eq (treal_mul treal_1 x) x"
  by (import realax TREAL_MUL_LID)

lemma TREAL_ADD_LINV: "ALL x::hreal * hreal. treal_eq (treal_add (treal_neg x) x) treal_0"
  by (import realax TREAL_ADD_LINV)

lemma TREAL_INV_0: "treal_eq (treal_inv treal_0) treal_0"
  by (import realax TREAL_INV_0)

lemma TREAL_MUL_LINV: "ALL x::hreal * hreal.
   ~ treal_eq x treal_0 --> treal_eq (treal_mul (treal_inv x) x) treal_1"
  by (import realax TREAL_MUL_LINV)

lemma TREAL_LT_TOTAL: "ALL (x::hreal * hreal) y::hreal * hreal.
   treal_eq x y | treal_lt x y | treal_lt y x"
  by (import realax TREAL_LT_TOTAL)

lemma TREAL_LT_REFL: "ALL x::hreal * hreal. ~ treal_lt x x"
  by (import realax TREAL_LT_REFL)

lemma TREAL_LT_TRANS: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_lt x y & treal_lt y z --> treal_lt x z"
  by (import realax TREAL_LT_TRANS)

lemma TREAL_LT_ADD: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_lt y z --> treal_lt (treal_add x y) (treal_add x z)"
  by (import realax TREAL_LT_ADD)

lemma TREAL_LT_MUL: "ALL (x::hreal * hreal) y::hreal * hreal.
   treal_lt treal_0 x & treal_lt treal_0 y -->
   treal_lt treal_0 (treal_mul x y)"
  by (import realax TREAL_LT_MUL)

constdefs
  treal_of_hreal :: "hreal => hreal * hreal" 
  "treal_of_hreal == %x::hreal. (hreal_add x hreal_1, hreal_1)"

lemma treal_of_hreal: "ALL x::hreal. treal_of_hreal x = (hreal_add x hreal_1, hreal_1)"
  by (import realax treal_of_hreal)

constdefs
  hreal_of_treal :: "hreal * hreal => hreal" 
  "hreal_of_treal == %(x::hreal, y::hreal). SOME d::hreal. x = hreal_add y d"

lemma hreal_of_treal: "ALL (x::hreal) y::hreal.
   hreal_of_treal (x, y) = (SOME d::hreal. x = hreal_add y d)"
  by (import realax hreal_of_treal)

lemma TREAL_BIJ: "(ALL h::hreal. hreal_of_treal (treal_of_hreal h) = h) &
(ALL r::hreal * hreal.
    treal_lt treal_0 r = treal_eq (treal_of_hreal (hreal_of_treal r)) r)"
  by (import realax TREAL_BIJ)

lemma TREAL_ISO: "ALL (h::hreal) i::hreal.
   hreal_lt h i --> treal_lt (treal_of_hreal h) (treal_of_hreal i)"
  by (import realax TREAL_ISO)

lemma TREAL_BIJ_WELLDEF: "ALL (h::hreal * hreal) i::hreal * hreal.
   treal_eq h i --> hreal_of_treal h = hreal_of_treal i"
  by (import realax TREAL_BIJ_WELLDEF)

lemma TREAL_NEG_WELLDEF: "ALL (x1::hreal * hreal) x2::hreal * hreal.
   treal_eq x1 x2 --> treal_eq (treal_neg x1) (treal_neg x2)"
  by (import realax TREAL_NEG_WELLDEF)

lemma TREAL_ADD_WELLDEFR: "ALL (x1::hreal * hreal) (x2::hreal * hreal) y::hreal * hreal.
   treal_eq x1 x2 --> treal_eq (treal_add x1 y) (treal_add x2 y)"
  by (import realax TREAL_ADD_WELLDEFR)

lemma TREAL_ADD_WELLDEF: "ALL (x1::hreal * hreal) (x2::hreal * hreal) (y1::hreal * hreal)
   y2::hreal * hreal.
   treal_eq x1 x2 & treal_eq y1 y2 -->
   treal_eq (treal_add x1 y1) (treal_add x2 y2)"
  by (import realax TREAL_ADD_WELLDEF)

lemma TREAL_MUL_WELLDEFR: "ALL (x1::hreal * hreal) (x2::hreal * hreal) y::hreal * hreal.
   treal_eq x1 x2 --> treal_eq (treal_mul x1 y) (treal_mul x2 y)"
  by (import realax TREAL_MUL_WELLDEFR)

lemma TREAL_MUL_WELLDEF: "ALL (x1::hreal * hreal) (x2::hreal * hreal) (y1::hreal * hreal)
   y2::hreal * hreal.
   treal_eq x1 x2 & treal_eq y1 y2 -->
   treal_eq (treal_mul x1 y1) (treal_mul x2 y2)"
  by (import realax TREAL_MUL_WELLDEF)

lemma TREAL_LT_WELLDEFR: "ALL (x1::hreal * hreal) (x2::hreal * hreal) y::hreal * hreal.
   treal_eq x1 x2 --> treal_lt x1 y = treal_lt x2 y"
  by (import realax TREAL_LT_WELLDEFR)

lemma TREAL_LT_WELLDEFL: "ALL (x::hreal * hreal) (y1::hreal * hreal) y2::hreal * hreal.
   treal_eq y1 y2 --> treal_lt x y1 = treal_lt x y2"
  by (import realax TREAL_LT_WELLDEFL)

lemma TREAL_LT_WELLDEF: "ALL (x1::hreal * hreal) (x2::hreal * hreal) (y1::hreal * hreal)
   y2::hreal * hreal.
   treal_eq x1 x2 & treal_eq y1 y2 --> treal_lt x1 y1 = treal_lt x2 y2"
  by (import realax TREAL_LT_WELLDEF)

lemma TREAL_INV_WELLDEF: "ALL (x1::hreal * hreal) x2::hreal * hreal.
   treal_eq x1 x2 --> treal_eq (treal_inv x1) (treal_inv x2)"
  by (import realax TREAL_INV_WELLDEF)

;end_setup

;setup_theory real

lemma REAL_0: "(0::real) = (0::real)"
  by (import real REAL_0)

lemma REAL_1: "(1::real) = (1::real)"
  by (import real REAL_1)

lemma REAL_ADD_LID_UNIQ: "ALL (x::real) y::real. (x + y = y) = (x = (0::real))"
  by (import real REAL_ADD_LID_UNIQ)

lemma REAL_ADD_RID_UNIQ: "ALL (x::real) y::real. (x + y = x) = (y = (0::real))"
  by (import real REAL_ADD_RID_UNIQ)

lemma REAL_LNEG_UNIQ: "ALL (x::real) y::real. (x + y = (0::real)) = (x = - y)"
  by (import real REAL_LNEG_UNIQ)

lemma REAL_LT_ANTISYM: "ALL (x::real) y::real. ~ (x < y & y < x)"
  by (import real REAL_LT_ANTISYM)

lemma REAL_LTE_TOTAL: "ALL (x::real) y::real. x < y | y <= x"
  by (import real REAL_LTE_TOTAL)

lemma REAL_LET_ANTISYM: "ALL (x::real) y::real. ~ (x < y & y <= x)"
  by (import real REAL_LET_ANTISYM)

lemma REAL_LTE_ANTSYM: "ALL (x::real) y::real. ~ (x <= y & y < x)"
  by (import real REAL_LTE_ANTSYM)

lemma REAL_LT_NEGTOTAL: "ALL x::real. x = (0::real) | (0::real) < x | (0::real) < - x"
  by (import real REAL_LT_NEGTOTAL)

lemma REAL_LE_NEGTOTAL: "ALL x::real. (0::real) <= x | (0::real) <= - x"
  by (import real REAL_LE_NEGTOTAL)

lemma REAL_LT_ADDNEG: "ALL (x::real) (y::real) z::real. (y < x + - z) = (y + z < x)"
  by (import real REAL_LT_ADDNEG)

lemma REAL_LT_ADDNEG2: "ALL (x::real) (y::real) z::real. (x + - y < z) = (x < z + y)"
  by (import real REAL_LT_ADDNEG2)

lemma REAL_LT_ADD1: "ALL (x::real) y::real. x <= y --> x < y + (1::real)"
  by (import real REAL_LT_ADD1)

lemma REAL_SUB_ADD2: "ALL (x::real) y::real. y + (x - y) = x"
  by (import real REAL_SUB_ADD2)

lemma REAL_SUB_LT: "ALL (x::real) y::real. ((0::real) < x - y) = (y < x)"
  by (import real REAL_SUB_LT)

lemma REAL_SUB_LE: "ALL (x::real) y::real. ((0::real) <= x - y) = (y <= x)"
  by (import real REAL_SUB_LE)

lemma REAL_ADD_SUB: "ALL (x::real) y::real. x + y - x = y"
  by (import real REAL_ADD_SUB)

lemma REAL_NEG_EQ: "ALL (x::real) y::real. (- x = y) = (x = - y)"
  by (import real REAL_NEG_EQ)

lemma REAL_NEG_MINUS1: "ALL x::real. - x = - (1::real) * x"
  by (import real REAL_NEG_MINUS1)

lemma REAL_LT_LMUL_0: "ALL (x::real) y::real.
   (0::real) < x --> ((0::real) < x * y) = ((0::real) < y)"
  by (import real REAL_LT_LMUL_0)

lemma REAL_LT_RMUL_0: "ALL (x::real) y::real.
   (0::real) < y --> ((0::real) < x * y) = ((0::real) < x)"
  by (import real REAL_LT_RMUL_0)

lemma REAL_LT_LMUL: "ALL (x::real) (y::real) z::real. (0::real) < x --> (x * y < x * z) = (y < z)"
  by (import real REAL_LT_LMUL)

lemma REAL_LINV_UNIQ: "ALL (x::real) y::real. x * y = (1::real) --> x = inverse y"
  by (import real REAL_LINV_UNIQ)

lemma REAL_LE_INV: "ALL x>=0::real. (0::real) <= inverse x"
  by (import real REAL_LE_INV)

lemma REAL_LE_ADDR: "ALL (x::real) y::real. (x <= x + y) = ((0::real) <= y)"
  by (import real REAL_LE_ADDR)

lemma REAL_LE_ADDL: "ALL (x::real) y::real. (y <= x + y) = ((0::real) <= x)"
  by (import real REAL_LE_ADDL)

lemma REAL_LT_ADDR: "ALL (x::real) y::real. (x < x + y) = ((0::real) < y)"
  by (import real REAL_LT_ADDR)

lemma REAL_LT_ADDL: "ALL (x::real) y::real. (y < x + y) = ((0::real) < x)"
  by (import real REAL_LT_ADDL)

lemma REAL_LT_NZ: "ALL n::nat. (real n ~= (0::real)) = ((0::real) < real n)"
  by (import real REAL_LT_NZ)

lemma REAL_NZ_IMP_LT: "ALL n::nat. n ~= (0::nat) --> (0::real) < real n"
  by (import real REAL_NZ_IMP_LT)

lemma REAL_LT_RDIV_0: "ALL (y::real) z::real.
   (0::real) < z --> ((0::real) < y / z) = ((0::real) < y)"
  by (import real REAL_LT_RDIV_0)

lemma REAL_LT_RDIV: "ALL (x::real) (y::real) z::real. (0::real) < z --> (x / z < y / z) = (x < y)"
  by (import real REAL_LT_RDIV)

lemma REAL_LT_FRACTION_0: "ALL (n::nat) d::real.
   n ~= (0::nat) --> ((0::real) < d / real n) = ((0::real) < d)"
  by (import real REAL_LT_FRACTION_0)

lemma REAL_LT_MULTIPLE: "ALL (x::nat) xa::real.
   (1::nat) < x --> (xa < real x * xa) = ((0::real) < xa)"
  by (import real REAL_LT_MULTIPLE)

lemma REAL_LT_FRACTION: "ALL (n::nat) d::real. (1::nat) < n --> (d / real n < d) = ((0::real) < d)"
  by (import real REAL_LT_FRACTION)

lemma REAL_LT_HALF2: "ALL d::real. (d / (2::real) < d) = ((0::real) < d)"
  by (import real REAL_LT_HALF2)

lemma REAL_DIV_LMUL: "ALL (x::real) y::real. y ~= (0::real) --> y * (x / y) = x"
  by (import real REAL_DIV_LMUL)

lemma REAL_DIV_RMUL: "ALL (x::real) y::real. y ~= (0::real) --> x / y * y = x"
  by (import real REAL_DIV_RMUL)

lemma REAL_DOWN: "ALL x>0::real. EX xa>0::real. xa < x"
  by (import real REAL_DOWN)

lemma REAL_SUB_SUB: "ALL (x::real) y::real. x - y - x = - y"
  by (import real REAL_SUB_SUB)

lemma REAL_ADD2_SUB2: "ALL (a::real) (b::real) (c::real) d::real. a + b - (c + d) = a - c + (b - d)"
  by (import real REAL_ADD2_SUB2)

lemma REAL_SUB_LNEG: "ALL (x::real) y::real. - x - y = - (x + y)"
  by (import real REAL_SUB_LNEG)

lemma REAL_SUB_NEG2: "ALL (x::real) y::real. - x - - y = y - x"
  by (import real REAL_SUB_NEG2)

lemma REAL_SUB_TRIANGLE: "ALL (a::real) (b::real) c::real. a - b + (b - c) = a - c"
  by (import real REAL_SUB_TRIANGLE)

lemma REAL_INV_MUL: "ALL (x::real) y::real.
   x ~= (0::real) & y ~= (0::real) -->
   inverse (x * y) = inverse x * inverse y"
  by (import real REAL_INV_MUL)

lemma REAL_SUB_INV2: "ALL (x::real) y::real.
   x ~= (0::real) & y ~= (0::real) -->
   inverse x - inverse y = (y - x) / (x * y)"
  by (import real REAL_SUB_INV2)

lemma REAL_SUB_SUB2: "ALL (x::real) y::real. x - (x - y) = y"
  by (import real REAL_SUB_SUB2)

lemma REAL_ADD_SUB2: "ALL (x::real) y::real. x - (x + y) = - y"
  by (import real REAL_ADD_SUB2)

lemma REAL_LE_MUL2: "ALL (x1::real) (x2::real) (y1::real) y2::real.
   (0::real) <= x1 & (0::real) <= y1 & x1 <= x2 & y1 <= y2 -->
   x1 * y1 <= x2 * y2"
  by (import real REAL_LE_MUL2)

lemma REAL_LE_DIV: "ALL (x::real) xa::real.
   (0::real) <= x & (0::real) <= xa --> (0::real) <= x / xa"
  by (import real REAL_LE_DIV)

lemma REAL_LT_1: "ALL (x::real) y::real. (0::real) <= x & x < y --> x / y < (1::real)"
  by (import real REAL_LT_1)

lemma REAL_POS_NZ: "ALL x>0::real. x ~= (0::real)"
  by (import real REAL_POS_NZ)

lemma REAL_EQ_LMUL_IMP: "ALL (x::real) (xa::real) xb::real.
   x ~= (0::real) & x * xa = x * xb --> xa = xb"
  by (import real REAL_EQ_LMUL_IMP)

lemma REAL_FACT_NZ: "ALL n::nat. real (FACT n) ~= (0::real)"
  by (import real REAL_FACT_NZ)

lemma REAL_DIFFSQ: "ALL (x::real) y::real. (x + y) * (x - y) = x * x - y * y"
  by (import real REAL_DIFFSQ)

lemma REAL_POASQ: "ALL x::real. ((0::real) < x * x) = (x ~= (0::real))"
  by (import real REAL_POASQ)

lemma REAL_SUMSQ: "ALL (x::real) y::real.
   (x * x + y * y = (0::real)) = (x = (0::real) & y = (0::real))"
  by (import real REAL_SUMSQ)

lemma REAL_DIV_MUL2: "ALL (x::real) z::real.
   x ~= (0::real) & z ~= (0::real) -->
   (ALL y::real. y / z = x * y / (x * z))"
  by (import real REAL_DIV_MUL2)

lemma REAL_MIDDLE1: "ALL (a::real) b::real. a <= b --> a <= (a + b) / (2::real)"
  by (import real REAL_MIDDLE1)

lemma REAL_MIDDLE2: "ALL (a::real) b::real. a <= b --> (a + b) / (2::real) <= b"
  by (import real REAL_MIDDLE2)

lemma ABS_LT_MUL2: "ALL (w::real) (x::real) (y::real) z::real.
   abs w < y & abs x < z --> abs (w * x) < y * z"
  by (import real ABS_LT_MUL2)

lemma ABS_REFL: "ALL x::real. (abs x = x) = ((0::real) <= x)"
  by (import real ABS_REFL)

lemma ABS_BETWEEN: "ALL (x::real) (y::real) d::real.
   ((0::real) < d & x - d < y & y < x + d) = (abs (y - x) < d)"
  by (import real ABS_BETWEEN)

lemma ABS_BOUND: "ALL (x::real) (y::real) d::real. abs (x - y) < d --> y < x + d"
  by (import real ABS_BOUND)

lemma ABS_STILLNZ: "ALL (x::real) y::real. abs (x - y) < abs y --> x ~= (0::real)"
  by (import real ABS_STILLNZ)

lemma ABS_CASES: "ALL x::real. x = (0::real) | (0::real) < abs x"
  by (import real ABS_CASES)

lemma ABS_BETWEEN1: "ALL (x::real) (y::real) z::real. x < z & abs (y - x) < z - x --> y < z"
  by (import real ABS_BETWEEN1)

lemma ABS_SIGN: "ALL (x::real) y::real. abs (x - y) < y --> (0::real) < x"
  by (import real ABS_SIGN)

lemma ABS_SIGN2: "ALL (x::real) y::real. abs (x - y) < - y --> x < (0::real)"
  by (import real ABS_SIGN2)

lemma ABS_CIRCLE: "ALL (x::real) (y::real) h::real.
   abs h < abs y - abs x --> abs (x + h) < abs y"
  by (import real ABS_CIRCLE)

lemma ABS_BETWEEN2: "ALL (x0::real) (x::real) (y0::real) y::real.
   x0 < y0 &
   abs (x - x0) < (y0 - x0) / (2::real) &
   abs (y - y0) < (y0 - x0) / (2::real) -->
   x < y"
  by (import real ABS_BETWEEN2)

lemma POW_PLUS1: "ALL e>0::real. ALL n::nat. (1::real) + real n * e <= ((1::real) + e) ^ n"
  by (import real POW_PLUS1)

lemma POW_M1: "ALL n::nat. abs ((- (1::real)) ^ n) = (1::real)"
  by (import real POW_M1)

lemma REAL_LE1_POW2: "ALL x>=1::real. (1::real) <= x ^ 2"
  by (import real REAL_LE1_POW2)

lemma REAL_LT1_POW2: "ALL x>1::real. (1::real) < x ^ 2"
  by (import real REAL_LT1_POW2)

lemma POW_POS_LT: "ALL (x::real) n::nat. (0::real) < x --> (0::real) < x ^ Suc n"
  by (import real POW_POS_LT)

lemma POW_LT: "ALL (n::nat) (x::real) y::real.
   (0::real) <= x & x < y --> x ^ Suc n < y ^ Suc n"
  by (import real POW_LT)

lemma POW_ZERO_EQ: "ALL (n::nat) x::real. (x ^ Suc n = (0::real)) = (x = (0::real))"
  by (import real POW_ZERO_EQ)

lemma REAL_POW_LT2: "ALL (n::nat) (x::real) y::real.
   n ~= (0::nat) & (0::real) <= x & x < y --> x ^ n < y ^ n"
  by (import real REAL_POW_LT2)

lemma REAL_POW_MONO_LT: "ALL (m::nat) (n::nat) x::real. (1::real) < x & m < n --> x ^ m < x ^ n"
  by (import real REAL_POW_MONO_LT)

lemma REAL_SUP_SOMEPOS: "ALL P::real => bool.
   (EX x::real. P x & (0::real) < x) &
   (EX z::real. ALL x::real. P x --> x < z) -->
   (EX s::real. ALL y::real. (EX x::real. P x & y < x) = (y < s))"
  by (import real REAL_SUP_SOMEPOS)

lemma SUP_LEMMA1: "ALL (P::real => bool) (s::real) d::real.
   (ALL y::real. (EX x::real. P (x + d) & y < x) = (y < s)) -->
   (ALL y::real. (EX x::real. P x & y < x) = (y < s + d))"
  by (import real SUP_LEMMA1)

lemma SUP_LEMMA2: "ALL P::real => bool.
   Ex P --> (EX (d::real) x::real. P (x + d) & (0::real) < x)"
  by (import real SUP_LEMMA2)

lemma SUP_LEMMA3: "ALL d::real.
   (EX z::real. ALL x::real. (P::real => bool) x --> x < z) -->
   (EX x::real. ALL xa::real. P (xa + d) --> xa < x)"
  by (import real SUP_LEMMA3)

lemma REAL_SUP_EXISTS: "ALL P::real => bool.
   Ex P & (EX z::real. ALL x::real. P x --> x < z) -->
   (EX x::real. ALL y::real. (EX x::real. P x & y < x) = (y < x))"
  by (import real REAL_SUP_EXISTS)

constdefs
  sup :: "(real => bool) => real" 
  "sup ==
%P::real => bool.
   SOME s::real. ALL y::real. (EX x::real. P x & y < x) = (y < s)"

lemma sup: "ALL P::real => bool.
   sup P = (SOME s::real. ALL y::real. (EX x::real. P x & y < x) = (y < s))"
  by (import real sup)

lemma REAL_SUP: "ALL P::real => bool.
   Ex P & (EX z::real. ALL x::real. P x --> x < z) -->
   (ALL y::real. (EX x::real. P x & y < x) = (y < sup P))"
  by (import real REAL_SUP)

lemma REAL_SUP_UBOUND: "ALL P::real => bool.
   Ex P & (EX z::real. ALL x::real. P x --> x < z) -->
   (ALL y::real. P y --> y <= sup P)"
  by (import real REAL_SUP_UBOUND)

lemma SETOK_LE_LT: "ALL P::real => bool.
   (Ex P & (EX z::real. ALL x::real. P x --> x <= z)) =
   (Ex P & (EX z::real. ALL x::real. P x --> x < z))"
  by (import real SETOK_LE_LT)

lemma REAL_SUP_LE: "ALL P::real => bool.
   Ex P & (EX z::real. ALL x::real. P x --> x <= z) -->
   (ALL y::real. (EX x::real. P x & y < x) = (y < sup P))"
  by (import real REAL_SUP_LE)

lemma REAL_SUP_UBOUND_LE: "ALL P::real => bool.
   Ex P & (EX z::real. ALL x::real. P x --> x <= z) -->
   (ALL y::real. P y --> y <= sup P)"
  by (import real REAL_SUP_UBOUND_LE)

lemma REAL_ARCH_LEAST: "ALL y>0::real.
   ALL x>=0::real. EX n::nat. real n * y <= x & x < real (Suc n) * y"
  by (import real REAL_ARCH_LEAST)

consts
  sumc :: "nat => nat => (nat => real) => real" 

specification (sumc) sumc: "(ALL (n::nat) f::nat => real. sumc n (0::nat) f = (0::real)) &
(ALL (n::nat) (m::nat) f::nat => real.
    sumc n (Suc m) f = sumc n m f + f (n + m))"
  by (import real sumc)

consts
  sum :: "nat * nat => (nat => real) => real" 

defs
  sum_def: "(op ==::(nat * nat => (nat => real) => real)
        => (nat * nat => (nat => real) => real) => prop)
 (real.sum::nat * nat => (nat => real) => real)
 ((split::(nat => nat => (nat => real) => real)
          => nat * nat => (nat => real) => real)
   (sumc::nat => nat => (nat => real) => real))"

lemma SUM_DEF: "ALL (m::nat) (n::nat) f::nat => real. real.sum (m, n) f = sumc m n f"
  by (import real SUM_DEF)

lemma sum: "ALL (x::nat => real) (xa::nat) xb::nat.
   real.sum (xa, 0::nat) x = (0::real) &
   real.sum (xa, Suc xb) x = real.sum (xa, xb) x + x (xa + xb)"
  by (import real sum)

lemma SUM_TWO: "ALL (f::nat => real) (n::nat) p::nat.
   real.sum (0::nat, n) f + real.sum (n, p) f = real.sum (0::nat, n + p) f"
  by (import real SUM_TWO)

lemma SUM_DIFF: "ALL (f::nat => real) (m::nat) n::nat.
   real.sum (m, n) f = real.sum (0::nat, m + n) f - real.sum (0::nat, m) f"
  by (import real SUM_DIFF)

lemma ABS_SUM: "ALL (f::nat => real) (m::nat) n::nat.
   abs (real.sum (m, n) f) <= real.sum (m, n) (%n::nat. abs (f n))"
  by (import real ABS_SUM)

lemma SUM_LE: "ALL (f::nat => real) (g::nat => real) (m::nat) n::nat.
   (ALL r::nat. m <= r & r < n + m --> f r <= g r) -->
   real.sum (m, n) f <= real.sum (m, n) g"
  by (import real SUM_LE)

lemma SUM_EQ: "ALL (f::nat => real) (g::nat => real) (m::nat) n::nat.
   (ALL r::nat. m <= r & r < n + m --> f r = g r) -->
   real.sum (m, n) f = real.sum (m, n) g"
  by (import real SUM_EQ)

lemma SUM_POS: "ALL f::nat => real.
   (ALL n::nat. (0::real) <= f n) -->
   (ALL (m::nat) n::nat. (0::real) <= real.sum (m, n) f)"
  by (import real SUM_POS)

lemma SUM_POS_GEN: "ALL (f::nat => real) m::nat.
   (ALL n::nat. m <= n --> (0::real) <= f n) -->
   (ALL n::nat. (0::real) <= real.sum (m, n) f)"
  by (import real SUM_POS_GEN)

lemma SUM_ABS: "ALL (f::nat => real) (m::nat) x::nat.
   abs (real.sum (m, x) (%m::nat. abs (f m))) =
   real.sum (m, x) (%m::nat. abs (f m))"
  by (import real SUM_ABS)

lemma SUM_ABS_LE: "ALL (f::nat => real) (m::nat) n::nat.
   abs (real.sum (m, n) f) <= real.sum (m, n) (%n::nat. abs (f n))"
  by (import real SUM_ABS_LE)

lemma SUM_ZERO: "ALL (f::nat => real) N::nat.
   (ALL n::nat. N <= n --> f n = (0::real)) -->
   (ALL (m::nat) n::nat. N <= m --> real.sum (m, n) f = (0::real))"
  by (import real SUM_ZERO)

lemma SUM_ADD: "ALL (f::nat => real) (g::nat => real) (m::nat) n::nat.
   real.sum (m, n) (%n::nat. f n + g n) =
   real.sum (m, n) f + real.sum (m, n) g"
  by (import real SUM_ADD)

lemma SUM_CMUL: "ALL (f::nat => real) (c::real) (m::nat) n::nat.
   real.sum (m, n) (%n::nat. c * f n) = c * real.sum (m, n) f"
  by (import real SUM_CMUL)

lemma SUM_NEG: "ALL (f::nat => real) (n::nat) d::nat.
   real.sum (n, d) (%n::nat. - f n) = - real.sum (n, d) f"
  by (import real SUM_NEG)

lemma SUM_SUB: "ALL (f::nat => real) (g::nat => real) (m::nat) n::nat.
   real.sum (m, n) (%x::nat. f x - g x) =
   real.sum (m, n) f - real.sum (m, n) g"
  by (import real SUM_SUB)

lemma SUM_SUBST: "ALL (f::nat => real) (g::nat => real) (m::nat) n::nat.
   (ALL p::nat. m <= p & p < m + n --> f p = g p) -->
   real.sum (m, n) f = real.sum (m, n) g"
  by (import real SUM_SUBST)

lemma SUM_NSUB: "ALL (n::nat) (f::nat => real) c::real.
   real.sum (0::nat, n) f - real n * c =
   real.sum (0::nat, n) (%p::nat. f p - c)"
  by (import real SUM_NSUB)

lemma SUM_BOUND: "ALL (f::nat => real) (k::real) (m::nat) n::nat.
   (ALL p::nat. m <= p & p < m + n --> f p <= k) -->
   real.sum (m, n) f <= real n * k"
  by (import real SUM_BOUND)

lemma SUM_GROUP: "ALL (n::nat) (k::nat) f::nat => real.
   real.sum (0::nat, n) (%m::nat. real.sum (m * k, k) f) =
   real.sum (0::nat, n * k) f"
  by (import real SUM_GROUP)

lemma SUM_1: "ALL (f::nat => real) n::nat. real.sum (n, 1::nat) f = f n"
  by (import real SUM_1)

lemma SUM_2: "ALL (f::nat => real) n::nat. real.sum (n, 2::nat) f = f n + f (n + (1::nat))"
  by (import real SUM_2)

lemma SUM_OFFSET: "ALL (f::nat => real) (n::nat) k::nat.
   real.sum (0::nat, n) (%m::nat. f (m + k)) =
   real.sum (0::nat, n + k) f - real.sum (0::nat, k) f"
  by (import real SUM_OFFSET)

lemma SUM_REINDEX: "ALL (f::nat => real) (m::nat) (k::nat) n::nat.
   real.sum (m + k, n) f = real.sum (m, n) (%r::nat. f (r + k))"
  by (import real SUM_REINDEX)

lemma SUM_0: "ALL (m::nat) n::nat. real.sum (m, n) (%r::nat. 0::real) = (0::real)"
  by (import real SUM_0)

lemma SUM_PERMUTE_0: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::((nat => nat) => bool) => bool)
      (%p::nat => nat.
          (op -->::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%y::nat.
                 (op -->::bool => bool => bool)
                  ((op <::nat => nat => bool) y n)
                  ((Ex1::(nat => bool) => bool)
                    (%x::nat.
                        (op &::bool => bool => bool)
                         ((op <::nat => nat => bool) x n)
                         ((op =::nat => nat => bool) (p x) y)))))
           ((All::((nat => real) => bool) => bool)
             (%f::nat => real.
                 (op =::real => real => bool)
                  ((real.sum::nat * nat => (nat => real) => real)
                    ((Pair::nat => nat => nat * nat) (0::nat) n)
                    (%n::nat. f (p n)))
                  ((real.sum::nat * nat => (nat => real) => real)
                    ((Pair::nat => nat => nat * nat) (0::nat) n) f)))))"
  by (import real SUM_PERMUTE_0)

lemma SUM_CANCEL: "ALL (f::nat => real) (n::nat) d::nat.
   real.sum (n, d) (%n::nat. f (Suc n) - f n) = f (n + d) - f n"
  by (import real SUM_CANCEL)

lemma REAL_EQ_RDIV_EQ: "ALL (x::real) (xa::real) xb::real.
   (0::real) < xb --> (x = xa / xb) = (x * xb = xa)"
  by (import real REAL_EQ_RDIV_EQ)

lemma REAL_EQ_LDIV_EQ: "ALL (x::real) (xa::real) xb::real.
   (0::real) < xb --> (x / xb = xa) = (x = xa * xb)"
  by (import real REAL_EQ_LDIV_EQ)

;end_setup

;setup_theory topology

constdefs
  re_Union :: "(('a::type => bool) => bool) => 'a::type => bool" 
  "re_Union ==
%(P::('a::type => bool) => bool) x::'a::type.
   EX s::'a::type => bool. P s & s x"

lemma re_Union: "ALL P::('a::type => bool) => bool.
   re_Union P = (%x::'a::type. EX s::'a::type => bool. P s & s x)"
  by (import topology re_Union)

constdefs
  re_union :: "('a::type => bool) => ('a::type => bool) => 'a::type => bool" 
  "re_union ==
%(P::'a::type => bool) (Q::'a::type => bool) x::'a::type. P x | Q x"

lemma re_union: "ALL (P::'a::type => bool) Q::'a::type => bool.
   re_union P Q = (%x::'a::type. P x | Q x)"
  by (import topology re_union)

constdefs
  re_intersect :: "('a::type => bool) => ('a::type => bool) => 'a::type => bool" 
  "re_intersect ==
%(P::'a::type => bool) (Q::'a::type => bool) x::'a::type. P x & Q x"

lemma re_intersect: "ALL (P::'a::type => bool) Q::'a::type => bool.
   re_intersect P Q = (%x::'a::type. P x & Q x)"
  by (import topology re_intersect)

constdefs
  re_null :: "'a::type => bool" 
  "re_null == %x::'a::type. False"

lemma re_null: "re_null = (%x::'a::type. False)"
  by (import topology re_null)

constdefs
  re_universe :: "'a::type => bool" 
  "re_universe == %x::'a::type. True"

lemma re_universe: "re_universe = (%x::'a::type. True)"
  by (import topology re_universe)

constdefs
  re_subset :: "('a::type => bool) => ('a::type => bool) => bool" 
  "re_subset ==
%(P::'a::type => bool) Q::'a::type => bool. ALL x::'a::type. P x --> Q x"

lemma re_subset: "ALL (P::'a::type => bool) Q::'a::type => bool.
   re_subset P Q = (ALL x::'a::type. P x --> Q x)"
  by (import topology re_subset)

constdefs
  re_compl :: "('a::type => bool) => 'a::type => bool" 
  "re_compl == %(P::'a::type => bool) x::'a::type. ~ P x"

lemma re_compl: "ALL P::'a::type => bool. re_compl P = (%x::'a::type. ~ P x)"
  by (import topology re_compl)

lemma SUBSET_REFL: "ALL P::'a::type => bool. re_subset P P"
  by (import topology SUBSET_REFL)

lemma COMPL_MEM: "ALL (P::'a::type => bool) x::'a::type. P x = (~ re_compl P x)"
  by (import topology COMPL_MEM)

lemma SUBSET_ANTISYM: "ALL (P::'a::type => bool) Q::'a::type => bool.
   (re_subset P Q & re_subset Q P) = (P = Q)"
  by (import topology SUBSET_ANTISYM)

lemma SUBSET_TRANS: "ALL (P::'a::type => bool) (Q::'a::type => bool) R::'a::type => bool.
   re_subset P Q & re_subset Q R --> re_subset P R"
  by (import topology SUBSET_TRANS)

constdefs
  istopology :: "(('a::type => bool) => bool) => bool" 
  "istopology ==
%L::('a::type => bool) => bool.
   L re_null &
   L re_universe &
   (ALL (a::'a::type => bool) b::'a::type => bool.
       L a & L b --> L (re_intersect a b)) &
   (ALL P::('a::type => bool) => bool. re_subset P L --> L (re_Union P))"

lemma istopology: "ALL L::('a::type => bool) => bool.
   istopology L =
   (L re_null &
    L re_universe &
    (ALL (a::'a::type => bool) b::'a::type => bool.
        L a & L b --> L (re_intersect a b)) &
    (ALL P::('a::type => bool) => bool. re_subset P L --> L (re_Union P)))"
  by (import topology istopology)

typedef (open) ('a) topology = "(Collect::((('a::type => bool) => bool) => bool)
          => (('a::type => bool) => bool) set)
 (istopology::(('a::type => bool) => bool) => bool)" 
  by (rule typedef_helper,import topology topology_TY_DEF)

lemmas topology_TY_DEF = typedef_hol2hol4 [OF type_definition_topology]

consts
  topology :: "(('a::type => bool) => bool) => 'a::type topology" 
  "open" :: "'a::type topology => ('a::type => bool) => bool" 

specification ("open" topology) topology_tybij: "(ALL a::'a::type topology. topology (open a) = a) &
(ALL r::('a::type => bool) => bool. istopology r = (open (topology r) = r))"
  by (import topology topology_tybij)

lemma TOPOLOGY: "ALL L::'a::type topology.
   open L re_null &
   open L re_universe &
   (ALL (a::'a::type => bool) b::'a::type => bool.
       open L a & open L b --> open L (re_intersect a b)) &
   (ALL P::('a::type => bool) => bool.
       re_subset P (open L) --> open L (re_Union P))"
  by (import topology TOPOLOGY)

lemma TOPOLOGY_UNION: "ALL (x::'a::type topology) xa::('a::type => bool) => bool.
   re_subset xa (open x) --> open x (re_Union xa)"
  by (import topology TOPOLOGY_UNION)

constdefs
  neigh :: "'a::type topology => ('a::type => bool) * 'a::type => bool" 
  "neigh ==
%(top::'a::type topology) (N::'a::type => bool, x::'a::type).
   EX P::'a::type => bool. open top P & re_subset P N & P x"

lemma neigh: "ALL (top::'a::type topology) (N::'a::type => bool) x::'a::type.
   neigh top (N, x) =
   (EX P::'a::type => bool. open top P & re_subset P N & P x)"
  by (import topology neigh)

lemma OPEN_OWN_NEIGH: "ALL (S'::'a::type => bool) (top::'a::type topology) x::'a::type.
   open top S' & S' x --> neigh top (S', x)"
  by (import topology OPEN_OWN_NEIGH)

lemma OPEN_UNOPEN: "ALL (S'::'a::type => bool) top::'a::type topology.
   open top S' =
   (re_Union (%P::'a::type => bool. open top P & re_subset P S') = S')"
  by (import topology OPEN_UNOPEN)

lemma OPEN_SUBOPEN: "ALL (S'::'a::type => bool) top::'a::type topology.
   open top S' =
   (ALL x::'a::type.
       S' x --> (EX P::'a::type => bool. P x & open top P & re_subset P S'))"
  by (import topology OPEN_SUBOPEN)

lemma OPEN_NEIGH: "ALL (S'::'a::type => bool) top::'a::type topology.
   open top S' =
   (ALL x::'a::type.
       S' x --> (EX N::'a::type => bool. neigh top (N, x) & re_subset N S'))"
  by (import topology OPEN_NEIGH)

constdefs
  closed :: "'a::type topology => ('a::type => bool) => bool" 
  "closed == %(L::'a::type topology) S'::'a::type => bool. open L (re_compl S')"

lemma closed: "ALL (L::'a::type topology) S'::'a::type => bool.
   closed L S' = open L (re_compl S')"
  by (import topology closed)

constdefs
  limpt :: "'a::type topology => 'a::type => ('a::type => bool) => bool" 
  "limpt ==
%(top::'a::type topology) (x::'a::type) S'::'a::type => bool.
   ALL N::'a::type => bool.
      neigh top (N, x) --> (EX y::'a::type. x ~= y & S' y & N y)"

lemma limpt: "ALL (top::'a::type topology) (x::'a::type) S'::'a::type => bool.
   limpt top x S' =
   (ALL N::'a::type => bool.
       neigh top (N, x) --> (EX y::'a::type. x ~= y & S' y & N y))"
  by (import topology limpt)

lemma CLOSED_LIMPT: "ALL (top::'a::type topology) S'::'a::type => bool.
   closed top S' = (ALL x::'a::type. limpt top x S' --> S' x)"
  by (import topology CLOSED_LIMPT)

constdefs
  ismet :: "('a::type * 'a::type => real) => bool" 
  "ismet ==
%m::'a::type * 'a::type => real.
   (ALL (x::'a::type) y::'a::type. (m (x, y) = (0::real)) = (x = y)) &
   (ALL (x::'a::type) (y::'a::type) z::'a::type.
       m (y, z) <= m (x, y) + m (x, z))"

lemma ismet: "ALL m::'a::type * 'a::type => real.
   ismet m =
   ((ALL (x::'a::type) y::'a::type. (m (x, y) = (0::real)) = (x = y)) &
    (ALL (x::'a::type) (y::'a::type) z::'a::type.
        m (y, z) <= m (x, y) + m (x, z)))"
  by (import topology ismet)

typedef (open) ('a) metric = "(Collect::(('a::type * 'a::type => real) => bool)
          => ('a::type * 'a::type => real) set)
 (ismet::('a::type * 'a::type => real) => bool)" 
  by (rule typedef_helper,import topology metric_TY_DEF)

lemmas metric_TY_DEF = typedef_hol2hol4 [OF type_definition_metric]

consts
  metric :: "('a::type * 'a::type => real) => 'a::type metric" 
  dist :: "'a::type metric => 'a::type * 'a::type => real" 

specification (dist metric) metric_tybij: "(ALL a::'a::type metric. metric (dist a) = a) &
(ALL r::'a::type * 'a::type => real. ismet r = (dist (metric r) = r))"
  by (import topology metric_tybij)

lemma METRIC_ISMET: "ALL m::'a::type metric. ismet (dist m)"
  by (import topology METRIC_ISMET)

lemma METRIC_ZERO: "ALL (m::'a::type metric) (x::'a::type) y::'a::type.
   (dist m (x, y) = (0::real)) = (x = y)"
  by (import topology METRIC_ZERO)

lemma METRIC_SAME: "ALL (m::'a::type metric) x::'a::type. dist m (x, x) = (0::real)"
  by (import topology METRIC_SAME)

lemma METRIC_POS: "ALL (m::'a::type metric) (x::'a::type) y::'a::type.
   (0::real) <= dist m (x, y)"
  by (import topology METRIC_POS)

lemma METRIC_SYM: "ALL (m::'a::type metric) (x::'a::type) y::'a::type.
   dist m (x, y) = dist m (y, x)"
  by (import topology METRIC_SYM)

lemma METRIC_TRIANGLE: "ALL (m::'a::type metric) (x::'a::type) (y::'a::type) z::'a::type.
   dist m (x, z) <= dist m (x, y) + dist m (y, z)"
  by (import topology METRIC_TRIANGLE)

lemma METRIC_NZ: "ALL (m::'a::type metric) (x::'a::type) y::'a::type.
   x ~= y --> (0::real) < dist m (x, y)"
  by (import topology METRIC_NZ)

constdefs
  mtop :: "'a::type metric => 'a::type topology" 
  "mtop ==
%m::'a::type metric.
   topology
    (%S'::'a::type => bool.
        ALL x::'a::type.
           S' x -->
           (EX e>0::real. ALL y::'a::type. dist m (x, y) < e --> S' y))"

lemma mtop: "ALL m::'a::type metric.
   mtop m =
   topology
    (%S'::'a::type => bool.
        ALL x::'a::type.
           S' x -->
           (EX e>0::real. ALL y::'a::type. dist m (x, y) < e --> S' y))"
  by (import topology mtop)

lemma mtop_istopology: "ALL m::'a::type metric.
   istopology
    (%S'::'a::type => bool.
        ALL x::'a::type.
           S' x -->
           (EX e>0::real. ALL y::'a::type. dist m (x, y) < e --> S' y))"
  by (import topology mtop_istopology)

lemma MTOP_OPEN: "ALL (S'::'a::type => bool) x::'a::type metric.
   open (mtop x) S' =
   (ALL xa::'a::type.
       S' xa -->
       (EX e>0::real. ALL y::'a::type. dist x (xa, y) < e --> S' y))"
  by (import topology MTOP_OPEN)

constdefs
  B :: "'a::type metric => 'a::type * real => 'a::type => bool" 
  "B ==
%(m::'a::type metric) (x::'a::type, e::real) y::'a::type. dist m (x, y) < e"

lemma ball: "ALL (m::'a::type metric) (x::'a::type) e::real.
   B m (x, e) = (%y::'a::type. dist m (x, y) < e)"
  by (import topology ball)

lemma BALL_OPEN: "ALL (m::'a::type metric) (x::'a::type) e::real.
   (0::real) < e --> open (mtop m) (B m (x, e))"
  by (import topology BALL_OPEN)

lemma BALL_NEIGH: "ALL (m::'a::type metric) (x::'a::type) e::real.
   (0::real) < e --> neigh (mtop m) (B m (x, e), x)"
  by (import topology BALL_NEIGH)

lemma MTOP_LIMPT: "ALL (m::'a::type metric) (x::'a::type) S'::'a::type => bool.
   limpt (mtop m) x S' =
   (ALL e>0::real. EX y::'a::type. x ~= y & S' y & dist m (x, y) < e)"
  by (import topology MTOP_LIMPT)

lemma ISMET_R1: "ismet (%(x::real, y::real). abs (y - x))"
  by (import topology ISMET_R1)

constdefs
  mr1 :: "real metric" 
  "mr1 == metric (%(x::real, y::real). abs (y - x))"

lemma mr1: "mr1 = metric (%(x::real, y::real). abs (y - x))"
  by (import topology mr1)

lemma MR1_DEF: "ALL (x::real) y::real. dist mr1 (x, y) = abs (y - x)"
  by (import topology MR1_DEF)

lemma MR1_ADD: "ALL (x::real) d::real. dist mr1 (x, x + d) = abs d"
  by (import topology MR1_ADD)

lemma MR1_SUB: "ALL (x::real) d::real. dist mr1 (x, x - d) = abs d"
  by (import topology MR1_SUB)

lemma MR1_ADD_POS: "ALL (x::real) d::real. (0::real) <= d --> dist mr1 (x, x + d) = d"
  by (import topology MR1_ADD_POS)

lemma MR1_SUB_LE: "ALL (x::real) d::real. (0::real) <= d --> dist mr1 (x, x - d) = d"
  by (import topology MR1_SUB_LE)

lemma MR1_ADD_LT: "ALL (x::real) d::real. (0::real) < d --> dist mr1 (x, x + d) = d"
  by (import topology MR1_ADD_LT)

lemma MR1_SUB_LT: "ALL (x::real) d::real. (0::real) < d --> dist mr1 (x, x - d) = d"
  by (import topology MR1_SUB_LT)

lemma MR1_BETWEEN1: "ALL (x::real) (y::real) z::real. x < z & dist mr1 (x, y) < z - x --> y < z"
  by (import topology MR1_BETWEEN1)

lemma MR1_LIMPT: "ALL x::real. limpt (mtop mr1) x re_universe"
  by (import topology MR1_LIMPT)

;end_setup

;setup_theory nets

constdefs
  dorder :: "('a::type => 'a::type => bool) => bool" 
  "dorder ==
%g::'a::type => 'a::type => bool.
   ALL (x::'a::type) y::'a::type.
      g x x & g y y -->
      (EX z::'a::type. g z z & (ALL w::'a::type. g w z --> g w x & g w y))"

lemma dorder: "ALL g::'a::type => 'a::type => bool.
   dorder g =
   (ALL (x::'a::type) y::'a::type.
       g x x & g y y -->
       (EX z::'a::type. g z z & (ALL w::'a::type. g w z --> g w x & g w y)))"
  by (import nets dorder)

constdefs
  tends :: "('b::type => 'a::type)
=> 'a::type => 'a::type topology * ('b::type => 'b::type => bool) => bool" 
  "tends ==
%(s::'b::type => 'a::type) (l::'a::type) (top::'a::type topology,
   g::'b::type => 'b::type => bool).
   ALL N::'a::type => bool.
      neigh top (N, l) -->
      (EX n::'b::type. g n n & (ALL m::'b::type. g m n --> N (s m)))"

lemma tends: "ALL (s::'b::type => 'a::type) (l::'a::type) (top::'a::type topology)
   g::'b::type => 'b::type => bool.
   tends s l (top, g) =
   (ALL N::'a::type => bool.
       neigh top (N, l) -->
       (EX n::'b::type. g n n & (ALL m::'b::type. g m n --> N (s m))))"
  by (import nets tends)

constdefs
  bounded :: "'a::type metric * ('b::type => 'b::type => bool)
=> ('b::type => 'a::type) => bool" 
  "bounded ==
%(m::'a::type metric, g::'b::type => 'b::type => bool)
   f::'b::type => 'a::type.
   EX (k::real) (x::'a::type) N::'b::type.
      g N N & (ALL n::'b::type. g n N --> dist m (f n, x) < k)"

lemma bounded: "ALL (m::'a::type metric) (g::'b::type => 'b::type => bool)
   f::'b::type => 'a::type.
   bounded (m, g) f =
   (EX (k::real) (x::'a::type) N::'b::type.
       g N N & (ALL n::'b::type. g n N --> dist m (f n, x) < k))"
  by (import nets bounded)

constdefs
  tendsto :: "'a::type metric * 'a::type => 'a::type => 'a::type => bool" 
  "tendsto ==
%(m::'a::type metric, x::'a::type) (y::'a::type) z::'a::type.
   (0::real) < dist m (x, y) & dist m (x, y) <= dist m (x, z)"

lemma tendsto: "ALL (m::'a::type metric) (x::'a::type) (y::'a::type) z::'a::type.
   tendsto (m, x) y z =
   ((0::real) < dist m (x, y) & dist m (x, y) <= dist m (x, z))"
  by (import nets tendsto)

lemma DORDER_LEMMA: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (P::'a::type => bool) Q::'a::type => bool.
       (EX n::'a::type. g n n & (ALL m::'a::type. g m n --> P m)) &
       (EX n::'a::type. g n n & (ALL m::'a::type. g m n --> Q m)) -->
       (EX n::'a::type. g n n & (ALL m::'a::type. g m n --> P m & Q m)))"
  by (import nets DORDER_LEMMA)

lemma DORDER_NGE: "dorder nat_ge"
  by (import nets DORDER_NGE)

lemma DORDER_TENDSTO: "ALL (m::'a::type metric) x::'a::type. dorder (tendsto (m, x))"
  by (import nets DORDER_TENDSTO)

lemma MTOP_TENDS: "ALL (d::'a::type metric) (g::'b::type => 'b::type => bool)
   (x::'b::type => 'a::type) x0::'a::type.
   tends x x0 (mtop d, g) =
   (ALL e>0::real.
       EX n::'b::type.
          g n n & (ALL m::'b::type. g m n --> dist d (x m, x0) < e))"
  by (import nets MTOP_TENDS)

lemma MTOP_TENDS_UNIQ: "ALL (g::'b::type => 'b::type => bool) d::'a::type metric.
   dorder g -->
   tends (x::'b::type => 'a::type) (x0::'a::type) (mtop d, g) &
   tends x (x1::'a::type) (mtop d, g) -->
   x0 = x1"
  by (import nets MTOP_TENDS_UNIQ)

lemma SEQ_TENDS: "ALL (d::'a::type metric) (x::nat => 'a::type) x0::'a::type.
   tends x x0 (mtop d, nat_ge) =
   (ALL xa>0::real.
       EX xb::nat. ALL xc::nat. xb <= xc --> dist d (x xc, x0) < xa)"
  by (import nets SEQ_TENDS)

lemma LIM_TENDS: "ALL (m1::'a::type metric) (m2::'b::type metric) (f::'a::type => 'b::type)
   (x0::'a::type) y0::'b::type.
   limpt (mtop m1) x0 re_universe -->
   tends f y0 (mtop m2, tendsto (m1, x0)) =
   (ALL e>0::real.
       EX d>0::real.
          ALL x::'a::type.
             (0::real) < dist m1 (x, x0) & dist m1 (x, x0) <= d -->
             dist m2 (f x, y0) < e)"
  by (import nets LIM_TENDS)

lemma LIM_TENDS2: "ALL (m1::'a::type metric) (m2::'b::type metric) (f::'a::type => 'b::type)
   (x0::'a::type) y0::'b::type.
   limpt (mtop m1) x0 re_universe -->
   tends f y0 (mtop m2, tendsto (m1, x0)) =
   (ALL e>0::real.
       EX d>0::real.
          ALL x::'a::type.
             (0::real) < dist m1 (x, x0) & dist m1 (x, x0) < d -->
             dist m2 (f x, y0) < e)"
  by (import nets LIM_TENDS2)

lemma MR1_BOUNDED: "ALL (g::'a::type => 'a::type => bool) f::'a::type => real.
   bounded (mr1, g) f =
   (EX (k::real) N::'a::type.
       g N N & (ALL n::'a::type. g n N --> abs (f n) < k))"
  by (import nets MR1_BOUNDED)

lemma NET_NULL: "ALL (g::'a::type => 'a::type => bool) (x::'a::type => real) x0::real.
   tends x x0 (mtop mr1, g) =
   tends (%n::'a::type. x n - x0) (0::real) (mtop mr1, g)"
  by (import nets NET_NULL)

lemma NET_CONV_BOUNDED: "ALL (g::'a::type => 'a::type => bool) (x::'a::type => real) x0::real.
   tends x x0 (mtop mr1, g) --> bounded (mr1, g) x"
  by (import nets NET_CONV_BOUNDED)

lemma NET_CONV_NZ: "ALL (g::'a::type => 'a::type => bool) (x::'a::type => real) x0::real.
   tends x x0 (mtop mr1, g) & x0 ~= (0::real) -->
   (EX N::'a::type. g N N & (ALL n::'a::type. g n N --> x n ~= (0::real)))"
  by (import nets NET_CONV_NZ)

lemma NET_CONV_IBOUNDED: "ALL (g::'a::type => 'a::type => bool) (x::'a::type => real) x0::real.
   tends x x0 (mtop mr1, g) & x0 ~= (0::real) -->
   bounded (mr1, g) (%n::'a::type. inverse (x n))"
  by (import nets NET_CONV_IBOUNDED)

lemma NET_NULL_ADD: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) y::'a::type => real.
       tends x (0::real) (mtop mr1, g) & tends y (0::real) (mtop mr1, g) -->
       tends (%n::'a::type. x n + y n) (0::real) (mtop mr1, g))"
  by (import nets NET_NULL_ADD)

lemma NET_NULL_MUL: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) y::'a::type => real.
       bounded (mr1, g) x & tends y (0::real) (mtop mr1, g) -->
       tends (%n::'a::type. x n * y n) (0::real) (mtop mr1, g))"
  by (import nets NET_NULL_MUL)

lemma NET_NULL_CMUL: "ALL (g::'a::type => 'a::type => bool) (k::real) x::'a::type => real.
   tends x (0::real) (mtop mr1, g) -->
   tends (%n::'a::type. k * x n) (0::real) (mtop mr1, g)"
  by (import nets NET_NULL_CMUL)

lemma NET_ADD: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) (x0::real) (y::'a::type => real) y0::real.
       tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) -->
       tends (%n::'a::type. x n + y n) (x0 + y0) (mtop mr1, g))"
  by (import nets NET_ADD)

lemma NET_NEG: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) x0::real.
       tends x x0 (mtop mr1, g) =
       tends (%n::'a::type. - x n) (- x0) (mtop mr1, g))"
  by (import nets NET_NEG)

lemma NET_SUB: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) (x0::real) (y::'a::type => real) y0::real.
       tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) -->
       tends (%xa::'a::type. x xa - y xa) (x0 - y0) (mtop mr1, g))"
  by (import nets NET_SUB)

lemma NET_MUL: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) (y::'a::type => real) (x0::real) y0::real.
       tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) -->
       tends (%n::'a::type. x n * y n) (x0 * y0) (mtop mr1, g))"
  by (import nets NET_MUL)

lemma NET_INV: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) x0::real.
       tends x x0 (mtop mr1, g) & x0 ~= (0::real) -->
       tends (%n::'a::type. inverse (x n)) (inverse x0) (mtop mr1, g))"
  by (import nets NET_INV)

lemma NET_DIV: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) (x0::real) (y::'a::type => real) y0::real.
       tends x x0 (mtop mr1, g) &
       tends y y0 (mtop mr1, g) & y0 ~= (0::real) -->
       tends (%xa::'a::type. x xa / y xa) (x0 / y0) (mtop mr1, g))"
  by (import nets NET_DIV)

lemma NET_ABS: "ALL (g::'a::type => 'a::type => bool) (x::'a::type => real) x0::real.
   tends x x0 (mtop mr1, g) -->
   tends (%n::'a::type. abs (x n)) (abs x0) (mtop mr1, g)"
  by (import nets NET_ABS)

lemma NET_LE: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) (x0::real) (y::'a::type => real) y0::real.
       tends x x0 (mtop mr1, g) &
       tends y y0 (mtop mr1, g) &
       (EX N::'a::type. g N N & (ALL n::'a::type. g n N --> x n <= y n)) -->
       x0 <= y0)"
  by (import nets NET_LE)

;end_setup

;setup_theory seq

consts
  "-->" :: "(nat => real) => real => bool" ("-->")

defs
  "-->_def": "--> == %(x::nat => real) x0::real. tends x x0 (mtop mr1, nat_ge)"

lemma tends_num_real: "ALL (x::nat => real) x0::real. --> x x0 = tends x x0 (mtop mr1, nat_ge)"
  by (import seq tends_num_real)

lemma SEQ: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (op =::bool => bool => bool)
           ((-->::(nat => real) => real => bool) x x0)
           ((All::(real => bool) => bool)
             (%e::real.
                 (op -->::bool => bool => bool)
                  ((op <::real => real => bool) (0::real) e)
                  ((Ex::(nat => bool) => bool)
                    (%N::nat.
                        (All::(nat => bool) => bool)
                         (%n::nat.
                             (op -->::bool => bool => bool)
                              ((op <=::nat => nat => bool) N n)
                              ((op <::real => real => bool)
                                ((abs::real => real)
                                  ((op -::real => real => real) (x n) x0))
                                e))))))))"
  by (import seq SEQ)

lemma SEQ_CONST: "ALL k::real. --> (%x::nat. k) k"
  by (import seq SEQ_CONST)

lemma SEQ_ADD: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (All::((nat => real) => bool) => bool)
           (%y::nat => real.
               (All::(real => bool) => bool)
                (%y0::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((-->::(nat => real) => real => bool) x x0)
                       ((-->::(nat => real) => real => bool) y y0))
                     ((-->::(nat => real) => real => bool)
                       (%n::nat. (op +::real => real => real) (x n) (y n))
                       ((op +::real => real => real) x0 y0))))))"
  by (import seq SEQ_ADD)

lemma SEQ_MUL: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (All::((nat => real) => bool) => bool)
           (%y::nat => real.
               (All::(real => bool) => bool)
                (%y0::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((-->::(nat => real) => real => bool) x x0)
                       ((-->::(nat => real) => real => bool) y y0))
                     ((-->::(nat => real) => real => bool)
                       (%n::nat. (op *::real => real => real) (x n) (y n))
                       ((op *::real => real => real) x0 y0))))))"
  by (import seq SEQ_MUL)

lemma SEQ_NEG: "ALL (x::nat => real) x0::real. --> x x0 = --> (%n::nat. - x n) (- x0)"
  by (import seq SEQ_NEG)

lemma SEQ_INV: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((-->::(nat => real) => real => bool) x x0)
             ((Not::bool => bool)
               ((op =::real => real => bool) x0 (0::real))))
           ((-->::(nat => real) => real => bool)
             (%n::nat. (inverse::real => real) (x n))
             ((inverse::real => real) x0))))"
  by (import seq SEQ_INV)

lemma SEQ_SUB: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (All::((nat => real) => bool) => bool)
           (%y::nat => real.
               (All::(real => bool) => bool)
                (%y0::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((-->::(nat => real) => real => bool) x x0)
                       ((-->::(nat => real) => real => bool) y y0))
                     ((-->::(nat => real) => real => bool)
                       (%n::nat. (op -::real => real => real) (x n) (y n))
                       ((op -::real => real => real) x0 y0))))))"
  by (import seq SEQ_SUB)

lemma SEQ_DIV: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (All::((nat => real) => bool) => bool)
           (%y::nat => real.
               (All::(real => bool) => bool)
                (%y0::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((-->::(nat => real) => real => bool) x x0)
                       ((op &::bool => bool => bool)
                         ((-->::(nat => real) => real => bool) y y0)
                         ((Not::bool => bool)
                           ((op =::real => real => bool) y0 (0::real)))))
                     ((-->::(nat => real) => real => bool)
                       (%n::nat. (op /::real => real => real) (x n) (y n))
                       ((op /::real => real => real) x0 y0))))))"
  by (import seq SEQ_DIV)

lemma SEQ_UNIQ: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x1::real.
          (All::(real => bool) => bool)
           (%x2::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((-->::(nat => real) => real => bool) x x1)
                  ((-->::(nat => real) => real => bool) x x2))
                ((op =::real => real => bool) x1 x2))))"
  by (import seq SEQ_UNIQ)

constdefs
  convergent :: "(nat => real) => bool" 
  "convergent == %f::nat => real. Ex (--> f)"

lemma convergent: "ALL f::nat => real. convergent f = Ex (--> f)"
  by (import seq convergent)

constdefs
  cauchy :: "(nat => real) => bool" 
  "(op ==::((nat => real) => bool) => ((nat => real) => bool) => prop)
 (cauchy::(nat => real) => bool)
 (%f::nat => real.
     (All::(real => bool) => bool)
      (%e::real.
          (op -->::bool => bool => bool)
           ((op <::real => real => bool) (0::real) e)
           ((Ex::(nat => bool) => bool)
             (%N::nat.
                 (All::(nat => bool) => bool)
                  (%m::nat.
                      (All::(nat => bool) => bool)
                       (%n::nat.
                           (op -->::bool => bool => bool)
                            ((op &::bool => bool => bool)
                              ((op <=::nat => nat => bool) N m)
                              ((op <=::nat => nat => bool) N n))
                            ((op <::real => real => bool)
                              ((abs::real => real)
                                ((op -::real => real => real) (f m) (f n)))
                              e)))))))"

lemma cauchy: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op =::bool => bool => bool) ((cauchy::(nat => real) => bool) f)
      ((All::(real => bool) => bool)
        (%e::real.
            (op -->::bool => bool => bool)
             ((op <::real => real => bool) (0::real) e)
             ((Ex::(nat => bool) => bool)
               (%N::nat.
                   (All::(nat => bool) => bool)
                    (%m::nat.
                        (All::(nat => bool) => bool)
                         (%n::nat.
                             (op -->::bool => bool => bool)
                              ((op &::bool => bool => bool)
                                ((op <=::nat => nat => bool) N m)
                                ((op <=::nat => nat => bool) N n))
                              ((op <::real => real => bool)
                                ((abs::real => real)
                                  ((op -::real => real => real) (f m)
                                    (f n)))
                                e))))))))"
  by (import seq cauchy)

constdefs
  lim :: "(nat => real) => real" 
  "lim == %f::nat => real. Eps (--> f)"

lemma lim: "ALL f::nat => real. lim f = Eps (--> f)"
  by (import seq lim)

lemma SEQ_LIM: "ALL f::nat => real. convergent f = --> f (lim f)"
  by (import seq SEQ_LIM)

constdefs
  subseq :: "(nat => nat) => bool" 
  "(op ==::((nat => nat) => bool) => ((nat => nat) => bool) => prop)
 (subseq::(nat => nat) => bool)
 (%f::nat => nat.
     (All::(nat => bool) => bool)
      (%m::nat.
          (All::(nat => bool) => bool)
           (%n::nat.
               (op -->::bool => bool => bool)
                ((op <::nat => nat => bool) m n)
                ((op <::nat => nat => bool) (f m) (f n)))))"

lemma subseq: "(All::((nat => nat) => bool) => bool)
 (%f::nat => nat.
     (op =::bool => bool => bool) ((subseq::(nat => nat) => bool) f)
      ((All::(nat => bool) => bool)
        (%m::nat.
            (All::(nat => bool) => bool)
             (%n::nat.
                 (op -->::bool => bool => bool)
                  ((op <::nat => nat => bool) m n)
                  ((op <::nat => nat => bool) (f m) (f n))))))"
  by (import seq subseq)

lemma SUBSEQ_SUC: "ALL f::nat => nat. subseq f = (ALL n::nat. f n < f (Suc n))"
  by (import seq SUBSEQ_SUC)

consts
  mono :: "(nat => real) => bool" 

defs
  mono_def: "(op ==::((nat => real) => bool) => ((nat => real) => bool) => prop)
 (seq.mono::(nat => real) => bool)
 (%f::nat => real.
     (op |::bool => bool => bool)
      ((All::(nat => bool) => bool)
        (%m::nat.
            (All::(nat => bool) => bool)
             (%n::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m n)
                  ((op <=::real => real => bool) (f m) (f n)))))
      ((All::(nat => bool) => bool)
        (%m::nat.
            (All::(nat => bool) => bool)
             (%n::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) m n)
                  ((op <=::real => real => bool) (f n) (f m))))))"

lemma mono: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op =::bool => bool => bool) ((seq.mono::(nat => real) => bool) f)
      ((op |::bool => bool => bool)
        ((All::(nat => bool) => bool)
          (%m::nat.
              (All::(nat => bool) => bool)
               (%n::nat.
                   (op -->::bool => bool => bool)
                    ((op <=::nat => nat => bool) m n)
                    ((op <=::real => real => bool) (f m) (f n)))))
        ((All::(nat => bool) => bool)
          (%m::nat.
              (All::(nat => bool) => bool)
               (%n::nat.
                   (op -->::bool => bool => bool)
                    ((op <=::nat => nat => bool) m n)
                    ((op <=::real => real => bool) (f n) (f m)))))))"
  by (import seq mono)

lemma MONO_SUC: "ALL f::nat => real.
   seq.mono f =
   ((ALL x::nat. f x <= f (Suc x)) | (ALL n::nat. f (Suc n) <= f n))"
  by (import seq MONO_SUC)

lemma MAX_LEMMA: "(All::((nat => real) => bool) => bool)
 (%s::nat => real.
     (All::(nat => bool) => bool)
      (%N::nat.
          (Ex::(real => bool) => bool)
           (%k::real.
               (All::(nat => bool) => bool)
                (%n::nat.
                    (op -->::bool => bool => bool)
                     ((op <::nat => nat => bool) n N)
                     ((op <::real => real => bool)
                       ((abs::real => real) (s n)) k)))))"
  by (import seq MAX_LEMMA)

lemma SEQ_BOUNDED: "ALL s::nat => real.
   bounded (mr1, nat_ge) s = (EX k::real. ALL n::nat. abs (s n) < k)"
  by (import seq SEQ_BOUNDED)

lemma SEQ_BOUNDED_2: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(real => bool) => bool)
      (%k::real.
          (All::(real => bool) => bool)
           (%k'::real.
               (op -->::bool => bool => bool)
                ((All::(nat => bool) => bool)
                  (%n::nat.
                      (op &::bool => bool => bool)
                       ((op <=::real => real => bool) k (f n))
                       ((op <=::real => real => bool) (f n) k')))
                ((bounded::real metric * (nat => nat => bool)
                           => (nat => real) => bool)
                  ((Pair::real metric
                          => (nat => nat => bool)
                             => real metric * (nat => nat => bool))
                    (mr1::real metric) (nat_ge::nat => nat => bool))
                  f))))"
  by (import seq SEQ_BOUNDED_2)

lemma SEQ_CBOUNDED: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op -->::bool => bool => bool) ((cauchy::(nat => real) => bool) f)
      ((bounded::real metric * (nat => nat => bool)
                 => (nat => real) => bool)
        ((Pair::real metric
                => (nat => nat => bool)
                   => real metric * (nat => nat => bool))
          (mr1::real metric) (nat_ge::nat => nat => bool))
        f))"
  by (import seq SEQ_CBOUNDED)

lemma SEQ_ICONV: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((bounded::real metric * (nat => nat => bool)
                   => (nat => real) => bool)
          ((Pair::real metric
                  => (nat => nat => bool)
                     => real metric * (nat => nat => bool))
            (mr1::real metric) (nat_ge::nat => nat => bool))
          f)
        ((All::(nat => bool) => bool)
          (%m::nat.
              (All::(nat => bool) => bool)
               (%n::nat.
                   (op -->::bool => bool => bool)
                    ((op <=::nat => nat => bool) n m)
                    ((op <=::real => real => bool) (f n) (f m))))))
      ((convergent::(nat => real) => bool) f))"
  by (import seq SEQ_ICONV)

lemma SEQ_NEG_CONV: "ALL f::nat => real. convergent f = convergent (%n::nat. - f n)"
  by (import seq SEQ_NEG_CONV)

lemma SEQ_NEG_BOUNDED: "ALL f::nat => real.
   bounded (mr1, nat_ge) (%n::nat. - f n) = bounded (mr1, nat_ge) f"
  by (import seq SEQ_NEG_BOUNDED)

lemma SEQ_BCONV: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((bounded::real metric * (nat => nat => bool)
                   => (nat => real) => bool)
          ((Pair::real metric
                  => (nat => nat => bool)
                     => real metric * (nat => nat => bool))
            (mr1::real metric) (nat_ge::nat => nat => bool))
          f)
        ((seq.mono::(nat => real) => bool) f))
      ((convergent::(nat => real) => bool) f))"
  by (import seq SEQ_BCONV)

lemma SEQ_MONOSUB: "ALL s::nat => real. EX f::nat => nat. subseq f & seq.mono (%n::nat. s (f n))"
  by (import seq SEQ_MONOSUB)

lemma SEQ_SBOUNDED: "(All::((nat => real) => bool) => bool)
 (%s::nat => real.
     (All::((nat => nat) => bool) => bool)
      (%f::nat => nat.
          (op -->::bool => bool => bool)
           ((bounded::real metric * (nat => nat => bool)
                      => (nat => real) => bool)
             ((Pair::real metric
                     => (nat => nat => bool)
                        => real metric * (nat => nat => bool))
               (mr1::real metric) (nat_ge::nat => nat => bool))
             s)
           ((bounded::real metric * (nat => nat => bool)
                      => (nat => real) => bool)
             ((Pair::real metric
                     => (nat => nat => bool)
                        => real metric * (nat => nat => bool))
               (mr1::real metric) (nat_ge::nat => nat => bool))
             (%n::nat. s (f n)))))"
  by (import seq SEQ_SBOUNDED)

lemma SEQ_SUBLE: "(All::((nat => nat) => bool) => bool)
 (%f::nat => nat.
     (op -->::bool => bool => bool) ((subseq::(nat => nat) => bool) f)
      ((All::(nat => bool) => bool)
        (%n::nat. (op <=::nat => nat => bool) n (f n))))"
  by (import seq SEQ_SUBLE)

lemma SEQ_DIRECT: "(All::((nat => nat) => bool) => bool)
 (%f::nat => nat.
     (op -->::bool => bool => bool) ((subseq::(nat => nat) => bool) f)
      ((All::(nat => bool) => bool)
        (%N1::nat.
            (All::(nat => bool) => bool)
             (%N2::nat.
                 (Ex::(nat => bool) => bool)
                  (%x::nat.
                      (op &::bool => bool => bool)
                       ((op <=::nat => nat => bool) N1 x)
                       ((op <=::nat => nat => bool) N2 (f x)))))))"
  by (import seq SEQ_DIRECT)

lemma SEQ_CAUCHY: "ALL f::nat => real. cauchy f = convergent f"
  by (import seq SEQ_CAUCHY)

lemma SEQ_LE: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::((nat => real) => bool) => bool)
      (%g::nat => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%m::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((-->::(nat => real) => real => bool) f l)
                       ((op &::bool => bool => bool)
                         ((-->::(nat => real) => real => bool) g m)
                         ((Ex::(nat => bool) => bool)
                           (%x::nat.
                               (All::(nat => bool) => bool)
                                (%xa::nat.
                                    (op -->::bool => bool => bool)
                                     ((op <=::nat => nat => bool) x xa)
                                     ((op <=::real => real => bool) (f xa)
 (g xa)))))))
                     ((op <=::real => real => bool) l m)))))"
  by (import seq SEQ_LE)

lemma SEQ_SUC: "ALL (f::nat => real) l::real. --> f l = --> (%n::nat. f (Suc n)) l"
  by (import seq SEQ_SUC)

lemma SEQ_ABS: "ALL f::nat => real. --> (%n::nat. abs (f n)) (0::real) = --> f (0::real)"
  by (import seq SEQ_ABS)

lemma SEQ_ABS_IMP: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(real => bool) => bool)
      (%l::real.
          (op -->::bool => bool => bool)
           ((-->::(nat => real) => real => bool) f l)
           ((-->::(nat => real) => real => bool)
             (%n::nat. (abs::real => real) (f n)) ((abs::real => real) l))))"
  by (import seq SEQ_ABS_IMP)

lemma SEQ_INV0: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op -->::bool => bool => bool)
      ((All::(real => bool) => bool)
        (%y::real.
            (Ex::(nat => bool) => bool)
             (%N::nat.
                 (All::(nat => bool) => bool)
                  (%n::nat.
                      (op -->::bool => bool => bool)
                       ((op <=::nat => nat => bool) N n)
                       ((op <::real => real => bool) y (f n))))))
      ((-->::(nat => real) => real => bool)
        (%n::nat. (inverse::real => real) (f n)) (0::real)))"
  by (import seq SEQ_INV0)

lemma SEQ_POWER_ABS: "(All::(real => bool) => bool)
 (%c::real.
     (op -->::bool => bool => bool)
      ((op <::real => real => bool) ((abs::real => real) c) (1::real))
      ((-->::(nat => real) => real => bool)
        ((op ^::real => nat => real) ((abs::real => real) c)) (0::real)))"
  by (import seq SEQ_POWER_ABS)

lemma SEQ_POWER: "(All::(real => bool) => bool)
 (%c::real.
     (op -->::bool => bool => bool)
      ((op <::real => real => bool) ((abs::real => real) c) (1::real))
      ((-->::(nat => real) => real => bool) ((op ^::real => nat => real) c)
        (0::real)))"
  by (import seq SEQ_POWER)

lemma NEST_LEMMA: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::((nat => real) => bool) => bool)
      (%g::nat => real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%n::nat.
                   (op <=::real => real => bool) (f n)
                    (f ((Suc::nat => nat) n))))
             ((op &::bool => bool => bool)
               ((All::(nat => bool) => bool)
                 (%n::nat.
                     (op <=::real => real => bool) (g ((Suc::nat => nat) n))
                      (g n)))
               ((All::(nat => bool) => bool)
                 (%n::nat. (op <=::real => real => bool) (f n) (g n)))))
           ((Ex::(real => bool) => bool)
             (%l::real.
                 (Ex::(real => bool) => bool)
                  (%m::real.
                      (op &::bool => bool => bool)
                       ((op <=::real => real => bool) l m)
                       ((op &::bool => bool => bool)
                         ((op &::bool => bool => bool)
                           ((All::(nat => bool) => bool)
                             (%n::nat.
                                 (op <=::real => real => bool) (f n) l))
                           ((-->::(nat => real) => real => bool) f l))
                         ((op &::bool => bool => bool)
                           ((All::(nat => bool) => bool)
                             (%n::nat.
                                 (op <=::real => real => bool) m (g n)))
                           ((-->::(nat => real) => real => bool) g m))))))))"
  by (import seq NEST_LEMMA)

lemma NEST_LEMMA_UNIQ: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::((nat => real) => bool) => bool)
      (%g::nat => real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%n::nat.
                   (op <=::real => real => bool) (f n)
                    (f ((Suc::nat => nat) n))))
             ((op &::bool => bool => bool)
               ((All::(nat => bool) => bool)
                 (%n::nat.
                     (op <=::real => real => bool) (g ((Suc::nat => nat) n))
                      (g n)))
               ((op &::bool => bool => bool)
                 ((All::(nat => bool) => bool)
                   (%n::nat. (op <=::real => real => bool) (f n) (g n)))
                 ((-->::(nat => real) => real => bool)
                   (%n::nat. (op -::real => real => real) (f n) (g n))
                   (0::real)))))
           ((Ex::(real => bool) => bool)
             (%x::real.
                 (op &::bool => bool => bool)
                  ((op &::bool => bool => bool)
                    ((All::(nat => bool) => bool)
                      (%n::nat. (op <=::real => real => bool) (f n) x))
                    ((-->::(nat => real) => real => bool) f x))
                  ((op &::bool => bool => bool)
                    ((All::(nat => bool) => bool)
                      (%n::nat. (op <=::real => real => bool) x (g n)))
                    ((-->::(nat => real) => real => bool) g x))))))"
  by (import seq NEST_LEMMA_UNIQ)

lemma BOLZANO_LEMMA: "(All::((real * real => bool) => bool) => bool)
 (%P::real * real => bool.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((All::(real => bool) => bool)
          (%a::real.
              (All::(real => bool) => bool)
               (%b::real.
                   (All::(real => bool) => bool)
                    (%c::real.
                        (op -->::bool => bool => bool)
                         ((op &::bool => bool => bool)
                           ((op <=::real => real => bool) a b)
                           ((op &::bool => bool => bool)
                             ((op <=::real => real => bool) b c)
                             ((op &::bool => bool => bool)
                               (P ((Pair::real => real => real * real) a b))
                               (P ((Pair::real => real => real * real) b
                                    c)))))
                         (P ((Pair::real => real => real * real) a c))))))
        ((All::(real => bool) => bool)
          (%x::real.
              (Ex::(real => bool) => bool)
               (%d::real.
                   (op &::bool => bool => bool)
                    ((op <::real => real => bool) (0::real) d)
                    ((All::(real => bool) => bool)
                      (%a::real.
                          (All::(real => bool) => bool)
                           (%b::real.
                               (op -->::bool => bool => bool)
                                ((op &::bool => bool => bool)
                                  ((op <=::real => real => bool) a x)
                                  ((op &::bool => bool => bool)
                                    ((op <=::real => real => bool) x b)
                                    ((op <::real => real => bool)
((op -::real => real => real) b a) d)))
                                (P ((Pair::real => real => real * real) a
                                     b)))))))))
      ((All::(real => bool) => bool)
        (%a::real.
            (All::(real => bool) => bool)
             (%b::real.
                 (op -->::bool => bool => bool)
                  ((op <=::real => real => bool) a b)
                  (P ((Pair::real => real => real * real) a b))))))"
  by (import seq BOLZANO_LEMMA)

constdefs
  sums :: "(nat => real) => real => bool" 
  "sums == %f::nat => real. --> (%n::nat. real.sum (0::nat, n) f)"

lemma sums: "ALL (f::nat => real) s::real.
   sums f s = --> (%n::nat. real.sum (0::nat, n) f) s"
  by (import seq sums)

constdefs
  summable :: "(nat => real) => bool" 
  "summable == %f::nat => real. Ex (sums f)"

lemma summable: "ALL f::nat => real. summable f = Ex (sums f)"
  by (import seq summable)

constdefs
  suminf :: "(nat => real) => real" 
  "suminf == %f::nat => real. Eps (sums f)"

lemma suminf: "ALL f::nat => real. suminf f = Eps (sums f)"
  by (import seq suminf)

lemma SUM_SUMMABLE: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(real => bool) => bool)
      (%l::real.
          (op -->::bool => bool => bool)
           ((sums::(nat => real) => real => bool) f l)
           ((summable::(nat => real) => bool) f)))"
  by (import seq SUM_SUMMABLE)

lemma SUMMABLE_SUM: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op -->::bool => bool => bool) ((summable::(nat => real) => bool) f)
      ((sums::(nat => real) => real => bool) f
        ((suminf::(nat => real) => real) f)))"
  by (import seq SUMMABLE_SUM)

lemma SUM_UNIQ: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((sums::(nat => real) => real => bool) f x)
           ((op =::real => real => bool) x
             ((suminf::(nat => real) => real) f))))"
  by (import seq SUM_UNIQ)

lemma SER_0: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(nat => bool) => bool)
      (%n::nat.
          (op -->::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%m::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) n m)
                  ((op =::real => real => bool) (f m) (0::real))))
           ((sums::(nat => real) => real => bool) f
             ((real.sum::nat * nat => (nat => real) => real)
               ((Pair::nat => nat => nat * nat) (0::nat) n) f))))"
  by (import seq SER_0)

lemma SER_POS_LE: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(nat => bool) => bool)
      (%n::nat.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((summable::(nat => real) => bool) f)
             ((All::(nat => bool) => bool)
               (%m::nat.
                   (op -->::bool => bool => bool)
                    ((op <=::nat => nat => bool) n m)
                    ((op <=::real => real => bool) (0::real) (f m)))))
           ((op <=::real => real => bool)
             ((real.sum::nat * nat => (nat => real) => real)
               ((Pair::nat => nat => nat * nat) (0::nat) n) f)
             ((suminf::(nat => real) => real) f))))"
  by (import seq SER_POS_LE)

lemma SER_POS_LT: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(nat => bool) => bool)
      (%n::nat.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((summable::(nat => real) => bool) f)
             ((All::(nat => bool) => bool)
               (%m::nat.
                   (op -->::bool => bool => bool)
                    ((op <=::nat => nat => bool) n m)
                    ((op <::real => real => bool) (0::real) (f m)))))
           ((op <::real => real => bool)
             ((real.sum::nat * nat => (nat => real) => real)
               ((Pair::nat => nat => nat * nat) (0::nat) n) f)
             ((suminf::(nat => real) => real) f))))"
  by (import seq SER_POS_LT)

lemma SER_GROUP: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(nat => bool) => bool)
      (%k::nat.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((summable::(nat => real) => bool) f)
             ((op <::nat => nat => bool) (0::nat) k))
           ((sums::(nat => real) => real => bool)
             (%n::nat.
                 (real.sum::nat * nat => (nat => real) => real)
                  ((Pair::nat => nat => nat * nat)
                    ((op *::nat => nat => nat) n k) k)
                  f)
             ((suminf::(nat => real) => real) f))))"
  by (import seq SER_GROUP)

lemma SER_PAIR: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op -->::bool => bool => bool) ((summable::(nat => real) => bool) f)
      ((sums::(nat => real) => real => bool)
        (%n::nat.
            (real.sum::nat * nat => (nat => real) => real)
             ((Pair::nat => nat => nat * nat)
               ((op *::nat => nat => nat)
                 ((number_of::bin => nat)
                   ((op BIT::bin => bit => bin)
                     ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                       (bit.B1::bit))
                     (bit.B0::bit)))
                 n)
               ((number_of::bin => nat)
                 ((op BIT::bin => bit => bin)
                   ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                     (bit.B1::bit))
                   (bit.B0::bit))))
             f)
        ((suminf::(nat => real) => real) f)))"
  by (import seq SER_PAIR)

lemma SER_OFFSET: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op -->::bool => bool => bool) ((summable::(nat => real) => bool) f)
      ((All::(nat => bool) => bool)
        (%k::nat.
            (sums::(nat => real) => real => bool)
             (%n::nat. f ((op +::nat => nat => nat) n k))
             ((op -::real => real => real)
               ((suminf::(nat => real) => real) f)
               ((real.sum::nat * nat => (nat => real) => real)
                 ((Pair::nat => nat => nat * nat) (0::nat) k) f)))))"
  by (import seq SER_OFFSET)

lemma SER_POS_LT_PAIR: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(nat => bool) => bool)
      (%n::nat.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((summable::(nat => real) => bool) f)
             ((All::(nat => bool) => bool)
               (%d::nat.
                   (op <::real => real => bool) (0::real)
                    ((op +::real => real => real)
                      (f ((op +::nat => nat => nat) n
                           ((op *::nat => nat => nat)
                             ((number_of::bin => nat)
                               ((op BIT::bin => bit => bin)
                                 ((op BIT::bin => bit => bin)
                                   (Numeral.Pls::bin) (bit.B1::bit))
                                 (bit.B0::bit)))
                             d)))
                      (f ((op +::nat => nat => nat) n
                           ((op +::nat => nat => nat)
                             ((op *::nat => nat => nat)
                               ((number_of::bin => nat)
                                 ((op BIT::bin => bit => bin)
                                   ((op BIT::bin => bit => bin)
                                     (Numeral.Pls::bin) (bit.B1::bit))
                                   (bit.B0::bit)))
                               d)
                             (1::nat))))))))
           ((op <::real => real => bool)
             ((real.sum::nat * nat => (nat => real) => real)
               ((Pair::nat => nat => nat * nat) (0::nat) n) f)
             ((suminf::(nat => real) => real) f))))"
  by (import seq SER_POS_LT_PAIR)

lemma SER_ADD: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (All::((nat => real) => bool) => bool)
           (%y::nat => real.
               (All::(real => bool) => bool)
                (%y0::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((sums::(nat => real) => real => bool) x x0)
                       ((sums::(nat => real) => real => bool) y y0))
                     ((sums::(nat => real) => real => bool)
                       (%n::nat. (op +::real => real => real) (x n) (y n))
                       ((op +::real => real => real) x0 y0))))))"
  by (import seq SER_ADD)

lemma SER_CMUL: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (All::(real => bool) => bool)
           (%c::real.
               (op -->::bool => bool => bool)
                ((sums::(nat => real) => real => bool) x x0)
                ((sums::(nat => real) => real => bool)
                  (%n::nat. (op *::real => real => real) c (x n))
                  ((op *::real => real => real) c x0)))))"
  by (import seq SER_CMUL)

lemma SER_NEG: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (op -->::bool => bool => bool)
           ((sums::(nat => real) => real => bool) x x0)
           ((sums::(nat => real) => real => bool)
             (%xa::nat. (uminus::real => real) (x xa))
             ((uminus::real => real) x0))))"
  by (import seq SER_NEG)

lemma SER_SUB: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (All::((nat => real) => bool) => bool)
           (%y::nat => real.
               (All::(real => bool) => bool)
                (%y0::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((sums::(nat => real) => real => bool) x x0)
                       ((sums::(nat => real) => real => bool) y y0))
                     ((sums::(nat => real) => real => bool)
                       (%xa::nat.
                           (op -::real => real => real) (x xa) (y xa))
                       ((op -::real => real => real) x0 y0))))))"
  by (import seq SER_SUB)

lemma SER_CDIV: "(All::((nat => real) => bool) => bool)
 (%x::nat => real.
     (All::(real => bool) => bool)
      (%x0::real.
          (All::(real => bool) => bool)
           (%c::real.
               (op -->::bool => bool => bool)
                ((sums::(nat => real) => real => bool) x x0)
                ((sums::(nat => real) => real => bool)
                  (%xa::nat. (op /::real => real => real) (x xa) c)
                  ((op /::real => real => real) x0 c)))))"
  by (import seq SER_CDIV)

lemma SER_CAUCHY: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op =::bool => bool => bool) ((summable::(nat => real) => bool) f)
      ((All::(real => bool) => bool)
        (%e::real.
            (op -->::bool => bool => bool)
             ((op <::real => real => bool) (0::real) e)
             ((Ex::(nat => bool) => bool)
               (%N::nat.
                   (All::(nat => bool) => bool)
                    (%m::nat.
                        (All::(nat => bool) => bool)
                         (%n::nat.
                             (op -->::bool => bool => bool)
                              ((op <=::nat => nat => bool) N m)
                              ((op <::real => real => bool)
                                ((abs::real => real)
                                  ((real.sum::nat * nat
        => (nat => real) => real)
                                    ((Pair::nat => nat => nat * nat) m n)
                                    f))
                                e))))))))"
  by (import seq SER_CAUCHY)

lemma SER_ZERO: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op -->::bool => bool => bool) ((summable::(nat => real) => bool) f)
      ((-->::(nat => real) => real => bool) f (0::real)))"
  by (import seq SER_ZERO)

lemma SER_COMPAR: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::((nat => real) => bool) => bool)
      (%g::nat => real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((Ex::(nat => bool) => bool)
               (%x::nat.
                   (All::(nat => bool) => bool)
                    (%xa::nat.
                        (op -->::bool => bool => bool)
                         ((op <=::nat => nat => bool) x xa)
                         ((op <=::real => real => bool)
                           ((abs::real => real) (f xa)) (g xa)))))
             ((summable::(nat => real) => bool) g))
           ((summable::(nat => real) => bool) f)))"
  by (import seq SER_COMPAR)

lemma SER_COMPARA: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::((nat => real) => bool) => bool)
      (%g::nat => real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((Ex::(nat => bool) => bool)
               (%x::nat.
                   (All::(nat => bool) => bool)
                    (%xa::nat.
                        (op -->::bool => bool => bool)
                         ((op <=::nat => nat => bool) x xa)
                         ((op <=::real => real => bool)
                           ((abs::real => real) (f xa)) (g xa)))))
             ((summable::(nat => real) => bool) g))
           ((summable::(nat => real) => bool)
             (%k::nat. (abs::real => real) (f k)))))"
  by (import seq SER_COMPARA)

lemma SER_LE: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::((nat => real) => bool) => bool)
      (%g::nat => real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%n::nat. (op <=::real => real => bool) (f n) (g n)))
             ((op &::bool => bool => bool)
               ((summable::(nat => real) => bool) f)
               ((summable::(nat => real) => bool) g)))
           ((op <=::real => real => bool)
             ((suminf::(nat => real) => real) f)
             ((suminf::(nat => real) => real) g))))"
  by (import seq SER_LE)

lemma SER_LE2: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::((nat => real) => bool) => bool)
      (%g::nat => real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%n::nat.
                   (op <=::real => real => bool) ((abs::real => real) (f n))
                    (g n)))
             ((summable::(nat => real) => bool) g))
           ((op &::bool => bool => bool)
             ((summable::(nat => real) => bool) f)
             ((op <=::real => real => bool)
               ((suminf::(nat => real) => real) f)
               ((suminf::(nat => real) => real) g)))))"
  by (import seq SER_LE2)

lemma SER_ACONV: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op -->::bool => bool => bool)
      ((summable::(nat => real) => bool)
        (%n::nat. (abs::real => real) (f n)))
      ((summable::(nat => real) => bool) f))"
  by (import seq SER_ACONV)

lemma SER_ABS: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (op -->::bool => bool => bool)
      ((summable::(nat => real) => bool)
        (%n::nat. (abs::real => real) (f n)))
      ((op <=::real => real => bool)
        ((abs::real => real) ((suminf::(nat => real) => real) f))
        ((suminf::(nat => real) => real)
          (%n::nat. (abs::real => real) (f n)))))"
  by (import seq SER_ABS)

lemma GP_FINITE: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((Not::bool => bool) ((op =::real => real => bool) x (1::real)))
      ((All::(nat => bool) => bool)
        (%n::nat.
            (op =::real => real => bool)
             ((real.sum::nat * nat => (nat => real) => real)
               ((Pair::nat => nat => nat * nat) (0::nat) n)
               ((op ^::real => nat => real) x))
             ((op /::real => real => real)
               ((op -::real => real => real)
                 ((op ^::real => nat => real) x n) (1::real))
               ((op -::real => real => real) x (1::real))))))"
  by (import seq GP_FINITE)

lemma GP: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op <::real => real => bool) ((abs::real => real) x) (1::real))
      ((sums::(nat => real) => real => bool) ((op ^::real => nat => real) x)
        ((inverse::real => real)
          ((op -::real => real => real) (1::real) x))))"
  by (import seq GP)

lemma ABS_NEG_LEMMA: "(All::(real => bool) => bool)
 (%c::real.
     (op -->::bool => bool => bool)
      ((op <=::real => real => bool) c (0::real))
      ((All::(real => bool) => bool)
        (%x::real.
            (All::(real => bool) => bool)
             (%y::real.
                 (op -->::bool => bool => bool)
                  ((op <=::real => real => bool) ((abs::real => real) x)
                    ((op *::real => real => real) c
                      ((abs::real => real) y)))
                  ((op =::real => real => bool) x (0::real))))))"
  by (import seq ABS_NEG_LEMMA)

lemma SER_RATIO: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(real => bool) => bool)
      (%c::real.
          (All::(nat => bool) => bool)
           (%N::nat.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) c (1::real))
                  ((All::(nat => bool) => bool)
                    (%n::nat.
                        (op -->::bool => bool => bool)
                         ((op <=::nat => nat => bool) N n)
                         ((op <=::real => real => bool)
                           ((abs::real => real) (f ((Suc::nat => nat) n)))
                           ((op *::real => real => real) c
                             ((abs::real => real) (f n)))))))
                ((summable::(nat => real) => bool) f))))"
  by (import seq SER_RATIO)

;end_setup

;setup_theory lim

constdefs
  tends_real_real :: "(real => real) => real => real => bool" 
  "tends_real_real ==
%(f::real => real) (l::real) x0::real.
   tends f l (mtop mr1, tendsto (mr1, x0))"

lemma tends_real_real: "ALL (f::real => real) (l::real) x0::real.
   tends_real_real f l x0 = tends f l (mtop mr1, tendsto (mr1, x0))"
  by (import lim tends_real_real)

lemma LIM: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%y0::real.
          (All::(real => bool) => bool)
           (%x0::real.
               (op =::bool => bool => bool)
                ((tends_real_real::(real => real) => real => real => bool) f
                  y0 x0)
                ((All::(real => bool) => bool)
                  (%e::real.
                      (op -->::bool => bool => bool)
                       ((op <::real => real => bool) (0::real) e)
                       ((Ex::(real => bool) => bool)
                         (%d::real.
                             (op &::bool => bool => bool)
                              ((op <::real => real => bool) (0::real) d)
                              ((All::(real => bool) => bool)
                                (%x::real.
                                    (op -->::bool => bool => bool)
                                     ((op &::bool => bool => bool)
 ((op <::real => real => bool) (0::real)
   ((abs::real => real) ((op -::real => real => real) x x0)))
 ((op <::real => real => bool)
   ((abs::real => real) ((op -::real => real => real) x x0)) d))
                                     ((op <::real => real => bool)
 ((abs::real => real) ((op -::real => real => real) (f x) y0)) e))))))))))"
  by (import lim LIM)

lemma LIM_CONST: "ALL k::real. All (tends_real_real (%x::real. k) k)"
  by (import lim LIM_CONST)

lemma LIM_ADD: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%m::real.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((tends_real_real::(real => real)
         => real => real => bool)
                              f l x)
                            ((tends_real_real::(real => real)
         => real => real => bool)
                              g m x))
                          ((tends_real_real::(real => real)
       => real => real => bool)
                            (%x::real.
                                (op +::real => real => real) (f x) (g x))
                            ((op +::real => real => real) l m) x))))))"
  by (import lim LIM_ADD)

lemma LIM_MUL: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%m::real.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((tends_real_real::(real => real)
         => real => real => bool)
                              f l x)
                            ((tends_real_real::(real => real)
         => real => real => bool)
                              g m x))
                          ((tends_real_real::(real => real)
       => real => real => bool)
                            (%x::real.
                                (op *::real => real => real) (f x) (g x))
                            ((op *::real => real => real) l m) x))))))"
  by (import lim LIM_MUL)

lemma LIM_NEG: "ALL (f::real => real) (l::real) x::real.
   tends_real_real f l x = tends_real_real (%x::real. - f x) (- l) x"
  by (import lim LIM_NEG)

lemma LIM_INV: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%l::real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((tends_real_real::(real => real) => real => real => bool)
                    f l x)
                  ((Not::bool => bool)
                    ((op =::real => real => bool) l (0::real))))
                ((tends_real_real::(real => real) => real => real => bool)
                  (%x::real. (inverse::real => real) (f x))
                  ((inverse::real => real) l) x))))"
  by (import lim LIM_INV)

lemma LIM_SUB: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%m::real.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((tends_real_real::(real => real)
         => real => real => bool)
                              f l x)
                            ((tends_real_real::(real => real)
         => real => real => bool)
                              g m x))
                          ((tends_real_real::(real => real)
       => real => real => bool)
                            (%x::real.
                                (op -::real => real => real) (f x) (g x))
                            ((op -::real => real => real) l m) x))))))"
  by (import lim LIM_SUB)

lemma LIM_DIV: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%m::real.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((tends_real_real::(real => real)
         => real => real => bool)
                              f l x)
                            ((op &::bool => bool => bool)
                              ((tends_real_real::(real => real)
           => real => real => bool)
                                g m x)
                              ((Not::bool => bool)
                                ((op =::real => real => bool) m
                                  (0::real)))))
                          ((tends_real_real::(real => real)
       => real => real => bool)
                            (%x::real.
                                (op /::real => real => real) (f x) (g x))
                            ((op /::real => real => real) l m) x))))))"
  by (import lim LIM_DIV)

lemma LIM_NULL: "ALL (f::real => real) (l::real) x::real.
   tends_real_real f l x = tends_real_real (%x::real. f x - l) (0::real) x"
  by (import lim LIM_NULL)

lemma LIM_X: "ALL x0::real. tends_real_real (%x::real. x) x0 x0"
  by (import lim LIM_X)

lemma LIM_UNIQ: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%l::real.
          (All::(real => bool) => bool)
           (%m::real.
               (All::(real => bool) => bool)
                (%x::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((tends_real_real::(real => real)
    => real => real => bool)
                         f l x)
                       ((tends_real_real::(real => real)
    => real => real => bool)
                         f m x))
                     ((op =::real => real => bool) l m)))))"
  by (import lim LIM_UNIQ)

lemma LIM_EQUAL: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%x0::real.
                    (op -->::bool => bool => bool)
                     ((All::(real => bool) => bool)
                       (%x::real.
                           (op -->::bool => bool => bool)
                            ((Not::bool => bool)
                              ((op =::real => real => bool) x x0))
                            ((op =::real => real => bool) (f x) (g x))))
                     ((op =::bool => bool => bool)
                       ((tends_real_real::(real => real)
    => real => real => bool)
                         f l x0)
                       ((tends_real_real::(real => real)
    => real => real => bool)
                         g l x0))))))"
  by (import lim LIM_EQUAL)

lemma LIM_TRANSFORM: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%x0::real.
               (All::(real => bool) => bool)
                (%l::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((tends_real_real::(real => real)
    => real => real => bool)
                         (%x::real.
                             (op -::real => real => real) (f x) (g x))
                         (0::real) x0)
                       ((tends_real_real::(real => real)
    => real => real => bool)
                         g l x0))
                     ((tends_real_real::(real => real)
  => real => real => bool)
                       f l x0)))))"
  by (import lim LIM_TRANSFORM)

constdefs
  diffl :: "(real => real) => real => real => bool" 
  "diffl ==
%(f::real => real) (l::real) x::real.
   tends_real_real (%h::real. (f (x + h) - f x) / h) l (0::real)"

lemma diffl: "ALL (f::real => real) (l::real) x::real.
   diffl f l x =
   tends_real_real (%h::real. (f (x + h) - f x) / h) l (0::real)"
  by (import lim diffl)

constdefs
  contl :: "(real => real) => real => bool" 
  "contl ==
%(f::real => real) x::real.
   tends_real_real (%h::real. f (x + h)) (f x) (0::real)"

lemma contl: "ALL (f::real => real) x::real.
   contl f x = tends_real_real (%h::real. f (x + h)) (f x) (0::real)"
  by (import lim contl)

constdefs
  differentiable :: "(real => real) => real => bool" 
  "differentiable == %(f::real => real) x::real. EX l::real. diffl f l x"

lemma differentiable: "ALL (f::real => real) x::real.
   differentiable f x = (EX l::real. diffl f l x)"
  by (import lim differentiable)

lemma DIFF_UNIQ: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%l::real.
          (All::(real => bool) => bool)
           (%m::real.
               (All::(real => bool) => bool)
                (%x::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((diffl::(real => real) => real => real => bool) f l
                         x)
                       ((diffl::(real => real) => real => real => bool) f m
                         x))
                     ((op =::real => real => bool) l m)))))"
  by (import lim DIFF_UNIQ)

lemma DIFF_CONT: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%l::real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((diffl::(real => real) => real => real => bool) f l x)
                ((contl::(real => real) => real => bool) f x))))"
  by (import lim DIFF_CONT)

lemma CONTL_LIM: "ALL (f::real => real) x::real. contl f x = tends_real_real f (f x) x"
  by (import lim CONTL_LIM)

lemma DIFF_CARAT: "ALL (f::real => real) (l::real) x::real.
   diffl f l x =
   (EX g::real => real.
       (ALL z::real. f z - f x = g z * (z - x)) & contl g x & g x = l)"
  by (import lim DIFF_CARAT)

lemma CONT_CONST: "ALL k::real. All (contl (%x::real. k))"
  by (import lim CONT_CONST)

lemma CONT_ADD: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((contl::(real => real) => real => bool) f x)
                  ((contl::(real => real) => real => bool) g x))
                ((contl::(real => real) => real => bool)
                  (%x::real. (op +::real => real => real) (f x) (g x)) x))))"
  by (import lim CONT_ADD)

lemma CONT_MUL: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((contl::(real => real) => real => bool) f x)
                  ((contl::(real => real) => real => bool) g x))
                ((contl::(real => real) => real => bool)
                  (%x::real. (op *::real => real => real) (f x) (g x)) x))))"
  by (import lim CONT_MUL)

lemma CONT_NEG: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((contl::(real => real) => real => bool) f x)
           ((contl::(real => real) => real => bool)
             (%x::real. (uminus::real => real) (f x)) x)))"
  by (import lim CONT_NEG)

lemma CONT_INV: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((contl::(real => real) => real => bool) f x)
             ((Not::bool => bool)
               ((op =::real => real => bool) (f x) (0::real))))
           ((contl::(real => real) => real => bool)
             (%x::real. (inverse::real => real) (f x)) x)))"
  by (import lim CONT_INV)

lemma CONT_SUB: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((contl::(real => real) => real => bool) f x)
                  ((contl::(real => real) => real => bool) g x))
                ((contl::(real => real) => real => bool)
                  (%x::real. (op -::real => real => real) (f x) (g x)) x))))"
  by (import lim CONT_SUB)

lemma CONT_DIV: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((contl::(real => real) => real => bool) f x)
                  ((op &::bool => bool => bool)
                    ((contl::(real => real) => real => bool) g x)
                    ((Not::bool => bool)
                      ((op =::real => real => bool) (g x) (0::real)))))
                ((contl::(real => real) => real => bool)
                  (%x::real. (op /::real => real => real) (f x) (g x)) x))))"
  by (import lim CONT_DIV)

lemma CONT_COMPOSE: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((contl::(real => real) => real => bool) f x)
                  ((contl::(real => real) => real => bool) g (f x)))
                ((contl::(real => real) => real => bool) (%x::real. g (f x))
                  x))))"
  by (import lim CONT_COMPOSE)

lemma IVT: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (All::(real => bool) => bool)
                (%y::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((op <=::real => real => bool) a b)
                       ((op &::bool => bool => bool)
                         ((op &::bool => bool => bool)
                           ((op <=::real => real => bool) (f a) y)
                           ((op <=::real => real => bool) y (f b)))
                         ((All::(real => bool) => bool)
                           (%x::real.
                               (op -->::bool => bool => bool)
                                ((op &::bool => bool => bool)
                                  ((op <=::real => real => bool) a x)
                                  ((op <=::real => real => bool) x b))
                                ((contl::(real => real) => real => bool) f
                                  x)))))
                     ((Ex::(real => bool) => bool)
                       (%x::real.
                           (op &::bool => bool => bool)
                            ((op <=::real => real => bool) a x)
                            ((op &::bool => bool => bool)
                              ((op <=::real => real => bool) x b)
                              ((op =::real => real => bool) (f x) y))))))))"
  by (import lim IVT)

lemma IVT2: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (All::(real => bool) => bool)
                (%y::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((op <=::real => real => bool) a b)
                       ((op &::bool => bool => bool)
                         ((op &::bool => bool => bool)
                           ((op <=::real => real => bool) (f b) y)
                           ((op <=::real => real => bool) y (f a)))
                         ((All::(real => bool) => bool)
                           (%x::real.
                               (op -->::bool => bool => bool)
                                ((op &::bool => bool => bool)
                                  ((op <=::real => real => bool) a x)
                                  ((op <=::real => real => bool) x b))
                                ((contl::(real => real) => real => bool) f
                                  x)))))
                     ((Ex::(real => bool) => bool)
                       (%x::real.
                           (op &::bool => bool => bool)
                            ((op <=::real => real => bool) a x)
                            ((op &::bool => bool => bool)
                              ((op <=::real => real => bool) x b)
                              ((op =::real => real => bool) (f x) y))))))))"
  by (import lim IVT2)

lemma DIFF_CONST: "ALL k::real. All (diffl (%x::real. k) (0::real))"
  by (import lim DIFF_CONST)

lemma DIFF_ADD: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%m::real.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((diffl::(real => real) => real => real => bool)
                              f l x)
                            ((diffl::(real => real) => real => real => bool)
                              g m x))
                          ((diffl::(real => real) => real => real => bool)
                            (%x::real.
                                (op +::real => real => real) (f x) (g x))
                            ((op +::real => real => real) l m) x))))))"
  by (import lim DIFF_ADD)

lemma DIFF_MUL: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%m::real.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((diffl::(real => real) => real => real => bool)
                              f l x)
                            ((diffl::(real => real) => real => real => bool)
                              g m x))
                          ((diffl::(real => real) => real => real => bool)
                            (%x::real.
                                (op *::real => real => real) (f x) (g x))
                            ((op +::real => real => real)
                              ((op *::real => real => real) l (g x))
                              ((op *::real => real => real) m (f x)))
                            x))))))"
  by (import lim DIFF_MUL)

lemma DIFF_CMUL: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%c::real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%x::real.
                    (op -->::bool => bool => bool)
                     ((diffl::(real => real) => real => real => bool) f l x)
                     ((diffl::(real => real) => real => real => bool)
                       (%x::real. (op *::real => real => real) c (f x))
                       ((op *::real => real => real) c l) x)))))"
  by (import lim DIFF_CMUL)

lemma DIFF_NEG: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%l::real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((diffl::(real => real) => real => real => bool) f l x)
                ((diffl::(real => real) => real => real => bool)
                  (%x::real. (uminus::real => real) (f x))
                  ((uminus::real => real) l) x))))"
  by (import lim DIFF_NEG)

lemma DIFF_SUB: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%m::real.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((diffl::(real => real) => real => real => bool)
                              f l x)
                            ((diffl::(real => real) => real => real => bool)
                              g m x))
                          ((diffl::(real => real) => real => real => bool)
                            (%x::real.
                                (op -::real => real => real) (f x) (g x))
                            ((op -::real => real => real) l m) x))))))"
  by (import lim DIFF_SUB)

lemma DIFF_CHAIN: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%m::real.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((diffl::(real => real) => real => real => bool)
                              f l (g x))
                            ((diffl::(real => real) => real => real => bool)
                              g m x))
                          ((diffl::(real => real) => real => real => bool)
                            (%x::real. f (g x))
                            ((op *::real => real => real) l m) x))))))"
  by (import lim DIFF_CHAIN)

lemma DIFF_X: "All (diffl (%x::real. x) (1::real))"
  by (import lim DIFF_X)

lemma DIFF_POW: "ALL (n::nat) x::real.
   diffl (%x::real. x ^ n) (real n * x ^ (n - (1::nat))) x"
  by (import lim DIFF_POW)

lemma DIFF_XM1: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((Not::bool => bool) ((op =::real => real => bool) x (0::real)))
      ((diffl::(real => real) => real => real => bool)
        (inverse::real => real)
        ((uminus::real => real)
          ((op ^::real => nat => real) ((inverse::real => real) x)
            ((number_of::bin => nat)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit)))))
        x))"
  by (import lim DIFF_XM1)

lemma DIFF_INV: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%l::real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((diffl::(real => real) => real => real => bool) f l x)
                  ((Not::bool => bool)
                    ((op =::real => real => bool) (f x) (0::real))))
                ((diffl::(real => real) => real => real => bool)
                  (%x::real. (inverse::real => real) (f x))
                  ((uminus::real => real)
                    ((op /::real => real => real) l
                      ((op ^::real => nat => real) (f x)
                        ((number_of::bin => nat)
                          ((op BIT::bin => bit => bin)
                            ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                              (bit.B1::bit))
                            (bit.B0::bit))))))
                  x))))"
  by (import lim DIFF_INV)

lemma DIFF_DIV: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%m::real.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((diffl::(real => real) => real => real => bool)
                              f l x)
                            ((op &::bool => bool => bool)
                              ((diffl::(real => real)
 => real => real => bool)
                                g m x)
                              ((Not::bool => bool)
                                ((op =::real => real => bool) (g x)
                                  (0::real)))))
                          ((diffl::(real => real) => real => real => bool)
                            (%x::real.
                                (op /::real => real => real) (f x) (g x))
                            ((op /::real => real => real)
                              ((op -::real => real => real)
                                ((op *::real => real => real) l (g x))
                                ((op *::real => real => real) m (f x)))
                              ((op ^::real => nat => real) (g x)
                                ((number_of::bin => nat)
                                  ((op BIT::bin => bit => bin)
                                    ((op BIT::bin => bit => bin)
(Numeral.Pls::bin) (bit.B1::bit))
                                    (bit.B0::bit)))))
                            x))))))"
  by (import lim DIFF_DIV)

lemma DIFF_SUM: "(All::((nat => real => real) => bool) => bool)
 (%f::nat => real => real.
     (All::((nat => real => real) => bool) => bool)
      (%f'::nat => real => real.
          (All::(nat => bool) => bool)
           (%m::nat.
               (All::(nat => bool) => bool)
                (%n::nat.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (op -->::bool => bool => bool)
                          ((All::(nat => bool) => bool)
                            (%r::nat.
                                (op -->::bool => bool => bool)
                                 ((op &::bool => bool => bool)
                                   ((op <=::nat => nat => bool) m r)
                                   ((op <::nat => nat => bool) r
                                     ((op +::nat => nat => nat) m n)))
                                 ((diffl::(real => real)
    => real => real => bool)
                                   (f r) (f' r x) x)))
                          ((diffl::(real => real) => real => real => bool)
                            (%x::real.
                                (real.sum::nat * nat
     => (nat => real) => real)
                                 ((Pair::nat => nat => nat * nat) m n)
                                 (%n::nat. f n x))
                            ((real.sum::nat * nat => (nat => real) => real)
                              ((Pair::nat => nat => nat * nat) m n)
                              (%r::nat. f' r x))
                            x))))))"
  by (import lim DIFF_SUM)

lemma CONT_BOUNDED: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::real => real => bool) a b)
                  ((All::(real => bool) => bool)
                    (%x::real.
                        (op -->::bool => bool => bool)
                         ((op &::bool => bool => bool)
                           ((op <=::real => real => bool) a x)
                           ((op <=::real => real => bool) x b))
                         ((contl::(real => real) => real => bool) f x))))
                ((Ex::(real => bool) => bool)
                  (%M::real.
                      (All::(real => bool) => bool)
                       (%x::real.
                           (op -->::bool => bool => bool)
                            ((op &::bool => bool => bool)
                              ((op <=::real => real => bool) a x)
                              ((op <=::real => real => bool) x b))
                            ((op <=::real => real => bool) (f x) M)))))))"
  by (import lim CONT_BOUNDED)

lemma CONT_HASSUP: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::real => real => bool) a b)
                  ((All::(real => bool) => bool)
                    (%x::real.
                        (op -->::bool => bool => bool)
                         ((op &::bool => bool => bool)
                           ((op <=::real => real => bool) a x)
                           ((op <=::real => real => bool) x b))
                         ((contl::(real => real) => real => bool) f x))))
                ((Ex::(real => bool) => bool)
                  (%M::real.
                      (op &::bool => bool => bool)
                       ((All::(real => bool) => bool)
                         (%x::real.
                             (op -->::bool => bool => bool)
                              ((op &::bool => bool => bool)
                                ((op <=::real => real => bool) a x)
                                ((op <=::real => real => bool) x b))
                              ((op <=::real => real => bool) (f x) M)))
                       ((All::(real => bool) => bool)
                         (%N::real.
                             (op -->::bool => bool => bool)
                              ((op <::real => real => bool) N M)
                              ((Ex::(real => bool) => bool)
                                (%x::real.
                                    (op &::bool => bool => bool)
                                     ((op <=::real => real => bool) a x)
                                     ((op &::bool => bool => bool)
 ((op <=::real => real => bool) x b)
 ((op <::real => real => bool) N (f x))))))))))))"
  by (import lim CONT_HASSUP)

lemma CONT_ATTAINS: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::real => real => bool) a b)
                  ((All::(real => bool) => bool)
                    (%x::real.
                        (op -->::bool => bool => bool)
                         ((op &::bool => bool => bool)
                           ((op <=::real => real => bool) a x)
                           ((op <=::real => real => bool) x b))
                         ((contl::(real => real) => real => bool) f x))))
                ((Ex::(real => bool) => bool)
                  (%x::real.
                      (op &::bool => bool => bool)
                       ((All::(real => bool) => bool)
                         (%xa::real.
                             (op -->::bool => bool => bool)
                              ((op &::bool => bool => bool)
                                ((op <=::real => real => bool) a xa)
                                ((op <=::real => real => bool) xa b))
                              ((op <=::real => real => bool) (f xa) x)))
                       ((Ex::(real => bool) => bool)
                         (%xa::real.
                             (op &::bool => bool => bool)
                              ((op <=::real => real => bool) a xa)
                              ((op &::bool => bool => bool)
                                ((op <=::real => real => bool) xa b)
                                ((op =::real => real => bool) (f xa)
                                  x)))))))))"
  by (import lim CONT_ATTAINS)

lemma CONT_ATTAINS2: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::real => real => bool) a b)
                  ((All::(real => bool) => bool)
                    (%x::real.
                        (op -->::bool => bool => bool)
                         ((op &::bool => bool => bool)
                           ((op <=::real => real => bool) a x)
                           ((op <=::real => real => bool) x b))
                         ((contl::(real => real) => real => bool) f x))))
                ((Ex::(real => bool) => bool)
                  (%x::real.
                      (op &::bool => bool => bool)
                       ((All::(real => bool) => bool)
                         (%xa::real.
                             (op -->::bool => bool => bool)
                              ((op &::bool => bool => bool)
                                ((op <=::real => real => bool) a xa)
                                ((op <=::real => real => bool) xa b))
                              ((op <=::real => real => bool) x (f xa))))
                       ((Ex::(real => bool) => bool)
                         (%xa::real.
                             (op &::bool => bool => bool)
                              ((op <=::real => real => bool) a xa)
                              ((op &::bool => bool => bool)
                                ((op <=::real => real => bool) xa b)
                                ((op =::real => real => bool) (f xa)
                                  x)))))))))"
  by (import lim CONT_ATTAINS2)

lemma CONT_ATTAINS_ALL: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::real => real => bool) a b)
                  ((All::(real => bool) => bool)
                    (%x::real.
                        (op -->::bool => bool => bool)
                         ((op &::bool => bool => bool)
                           ((op <=::real => real => bool) a x)
                           ((op <=::real => real => bool) x b))
                         ((contl::(real => real) => real => bool) f x))))
                ((Ex::(real => bool) => bool)
                  (%x::real.
                      (Ex::(real => bool) => bool)
                       (%M::real.
                           (op &::bool => bool => bool)
                            ((op <=::real => real => bool) x M)
                            ((op &::bool => bool => bool)
                              ((All::(real => bool) => bool)
                                (%y::real.
                                    (op -->::bool => bool => bool)
                                     ((op &::bool => bool => bool)
 ((op <=::real => real => bool) x y) ((op <=::real => real => bool) y M))
                                     ((Ex::(real => bool) => bool)
 (%x::real.
     (op &::bool => bool => bool) ((op <=::real => real => bool) a x)
      ((op &::bool => bool => bool) ((op <=::real => real => bool) x b)
        ((op =::real => real => bool) (f x) y))))))
                              ((All::(real => bool) => bool)
                                (%xa::real.
                                    (op -->::bool => bool => bool)
                                     ((op &::bool => bool => bool)
 ((op <=::real => real => bool) a xa) ((op <=::real => real => bool) xa b))
                                     ((op &::bool => bool => bool)
 ((op <=::real => real => bool) x (f xa))
 ((op <=::real => real => bool) (f xa) M)))))))))))"
  by (import lim CONT_ATTAINS_ALL)

lemma DIFF_LINC: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%x::real.
          (All::(real => bool) => bool)
           (%l::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((diffl::(real => real) => real => real => bool) f l x)
                  ((op <::real => real => bool) (0::real) l))
                ((Ex::(real => bool) => bool)
                  (%d::real.
                      (op &::bool => bool => bool)
                       ((op <::real => real => bool) (0::real) d)
                       ((All::(real => bool) => bool)
                         (%h::real.
                             (op -->::bool => bool => bool)
                              ((op &::bool => bool => bool)
                                ((op <::real => real => bool) (0::real) h)
                                ((op <::real => real => bool) h d))
                              ((op <::real => real => bool) (f x)
                                (f ((op +::real => real => real) x
                                     h))))))))))"
  by (import lim DIFF_LINC)

lemma DIFF_LDEC: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%x::real.
          (All::(real => bool) => bool)
           (%l::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((diffl::(real => real) => real => real => bool) f l x)
                  ((op <::real => real => bool) l (0::real)))
                ((Ex::(real => bool) => bool)
                  (%d::real.
                      (op &::bool => bool => bool)
                       ((op <::real => real => bool) (0::real) d)
                       ((All::(real => bool) => bool)
                         (%h::real.
                             (op -->::bool => bool => bool)
                              ((op &::bool => bool => bool)
                                ((op <::real => real => bool) (0::real) h)
                                ((op <::real => real => bool) h d))
                              ((op <::real => real => bool) (f x)
                                (f ((op -::real => real => real) x
                                     h))))))))))"
  by (import lim DIFF_LDEC)

lemma DIFF_LMAX: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%x::real.
          (All::(real => bool) => bool)
           (%l::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((diffl::(real => real) => real => real => bool) f l x)
                  ((Ex::(real => bool) => bool)
                    (%d::real.
                        (op &::bool => bool => bool)
                         ((op <::real => real => bool) (0::real) d)
                         ((All::(real => bool) => bool)
                           (%y::real.
                               (op -->::bool => bool => bool)
                                ((op <::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) x y))
                                  d)
                                ((op <=::real => real => bool) (f y)
                                  (f x)))))))
                ((op =::real => real => bool) l (0::real)))))"
  by (import lim DIFF_LMAX)

lemma DIFF_LMIN: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%x::real.
          (All::(real => bool) => bool)
           (%l::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((diffl::(real => real) => real => real => bool) f l x)
                  ((Ex::(real => bool) => bool)
                    (%d::real.
                        (op &::bool => bool => bool)
                         ((op <::real => real => bool) (0::real) d)
                         ((All::(real => bool) => bool)
                           (%y::real.
                               (op -->::bool => bool => bool)
                                ((op <::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) x y))
                                  d)
                                ((op <=::real => real => bool) (f x)
                                  (f y)))))))
                ((op =::real => real => bool) l (0::real)))))"
  by (import lim DIFF_LMIN)

lemma DIFF_LCONST: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%x::real.
          (All::(real => bool) => bool)
           (%l::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((diffl::(real => real) => real => real => bool) f l x)
                  ((Ex::(real => bool) => bool)
                    (%d::real.
                        (op &::bool => bool => bool)
                         ((op <::real => real => bool) (0::real) d)
                         ((All::(real => bool) => bool)
                           (%y::real.
                               (op -->::bool => bool => bool)
                                ((op <::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) x y))
                                  d)
                                ((op =::real => real => bool) (f y)
                                  (f x)))))))
                ((op =::real => real => bool) l (0::real)))))"
  by (import lim DIFF_LCONST)

lemma INTERVAL_LEMMA: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real => bool) => bool)
      (%b::real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) a x)
                  ((op <::real => real => bool) x b))
                ((Ex::(real => bool) => bool)
                  (%d::real.
                      (op &::bool => bool => bool)
                       ((op <::real => real => bool) (0::real) d)
                       ((All::(real => bool) => bool)
                         (%y::real.
                             (op -->::bool => bool => bool)
                              ((op <::real => real => bool)
                                ((abs::real => real)
                                  ((op -::real => real => real) x y))
                                d)
                              ((op &::bool => bool => bool)
                                ((op <=::real => real => bool) a y)
                                ((op <=::real => real => bool) y b)))))))))"
  by (import lim INTERVAL_LEMMA)

lemma ROLLE: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) a b)
                  ((op &::bool => bool => bool)
                    ((op =::real => real => bool) (f a) (f b))
                    ((op &::bool => bool => bool)
                      ((All::(real => bool) => bool)
                        (%x::real.
                            (op -->::bool => bool => bool)
                             ((op &::bool => bool => bool)
                               ((op <=::real => real => bool) a x)
                               ((op <=::real => real => bool) x b))
                             ((contl::(real => real) => real => bool) f x)))
                      ((All::(real => bool) => bool)
                        (%x::real.
                            (op -->::bool => bool => bool)
                             ((op &::bool => bool => bool)
                               ((op <::real => real => bool) a x)
                               ((op <::real => real => bool) x b))
                             ((differentiable::(real => real)
         => real => bool)
                               f x))))))
                ((Ex::(real => bool) => bool)
                  (%z::real.
                      (op &::bool => bool => bool)
                       ((op <::real => real => bool) a z)
                       ((op &::bool => bool => bool)
                         ((op <::real => real => bool) z b)
                         ((diffl::(real => real) => real => real => bool) f
                           (0::real) z)))))))"
  by (import lim ROLLE)

lemma MVT_LEMMA: "ALL (f::real => real) (a::real) b::real.
   f a - (f b - f a) / (b - a) * a = f b - (f b - f a) / (b - a) * b"
  by (import lim MVT_LEMMA)

lemma MVT: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) a b)
                  ((op &::bool => bool => bool)
                    ((All::(real => bool) => bool)
                      (%x::real.
                          (op -->::bool => bool => bool)
                           ((op &::bool => bool => bool)
                             ((op <=::real => real => bool) a x)
                             ((op <=::real => real => bool) x b))
                           ((contl::(real => real) => real => bool) f x)))
                    ((All::(real => bool) => bool)
                      (%x::real.
                          (op -->::bool => bool => bool)
                           ((op &::bool => bool => bool)
                             ((op <::real => real => bool) a x)
                             ((op <::real => real => bool) x b))
                           ((differentiable::(real => real) => real => bool)
                             f x)))))
                ((Ex::(real => bool) => bool)
                  (%l::real.
                      (Ex::(real => bool) => bool)
                       (%z::real.
                           (op &::bool => bool => bool)
                            ((op <::real => real => bool) a z)
                            ((op &::bool => bool => bool)
                              ((op <::real => real => bool) z b)
                              ((op &::bool => bool => bool)
                                ((diffl::(real => real)
   => real => real => bool)
                                  f l z)
                                ((op =::real => real => bool)
                                  ((op -::real => real => real) (f b) (f a))
                                  ((op *::real => real => real)
                                    ((op -::real => real => real) b a)
                                    l))))))))))"
  by (import lim MVT)

lemma DIFF_ISCONST_END: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) a b)
                  ((op &::bool => bool => bool)
                    ((All::(real => bool) => bool)
                      (%x::real.
                          (op -->::bool => bool => bool)
                           ((op &::bool => bool => bool)
                             ((op <=::real => real => bool) a x)
                             ((op <=::real => real => bool) x b))
                           ((contl::(real => real) => real => bool) f x)))
                    ((All::(real => bool) => bool)
                      (%x::real.
                          (op -->::bool => bool => bool)
                           ((op &::bool => bool => bool)
                             ((op <::real => real => bool) a x)
                             ((op <::real => real => bool) x b))
                           ((diffl::(real => real) => real => real => bool)
                             f (0::real) x)))))
                ((op =::real => real => bool) (f b) (f a)))))"
  by (import lim DIFF_ISCONST_END)

lemma DIFF_ISCONST: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) a b)
                  ((op &::bool => bool => bool)
                    ((All::(real => bool) => bool)
                      (%x::real.
                          (op -->::bool => bool => bool)
                           ((op &::bool => bool => bool)
                             ((op <=::real => real => bool) a x)
                             ((op <=::real => real => bool) x b))
                           ((contl::(real => real) => real => bool) f x)))
                    ((All::(real => bool) => bool)
                      (%x::real.
                          (op -->::bool => bool => bool)
                           ((op &::bool => bool => bool)
                             ((op <::real => real => bool) a x)
                             ((op <::real => real => bool) x b))
                           ((diffl::(real => real) => real => real => bool)
                             f (0::real) x)))))
                ((All::(real => bool) => bool)
                  (%x::real.
                      (op -->::bool => bool => bool)
                       ((op &::bool => bool => bool)
                         ((op <=::real => real => bool) a x)
                         ((op <=::real => real => bool) x b))
                       ((op =::real => real => bool) (f x) (f a)))))))"
  by (import lim DIFF_ISCONST)

lemma DIFF_ISCONST_ALL: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (op -->::bool => bool => bool)
      ((All::(real => bool) => bool)
        ((diffl::(real => real) => real => real => bool) f (0::real)))
      ((All::(real => bool) => bool)
        (%x::real.
            (All::(real => bool) => bool)
             (%y::real. (op =::real => real => bool) (f x) (f y)))))"
  by (import lim DIFF_ISCONST_ALL)

lemma INTERVAL_ABS: "ALL (x::real) (z::real) d::real.
   (x - d <= z & z <= x + d) = (abs (z - x) <= d)"
  by (import lim INTERVAL_ABS)

lemma CONT_INJ_LEMMA: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%x::real.
               (All::(real => bool) => bool)
                (%d::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((op <::real => real => bool) (0::real) d)
                       ((op &::bool => bool => bool)
                         ((All::(real => bool) => bool)
                           (%z::real.
                               (op -->::bool => bool => bool)
                                ((op <=::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) z x))
                                  d)
                                ((op =::real => real => bool) (g (f z)) z)))
                         ((All::(real => bool) => bool)
                           (%z::real.
                               (op -->::bool => bool => bool)
                                ((op <=::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) z x))
                                  d)
                                ((contl::(real => real) => real => bool) f
                                  z)))))
                     ((Not::bool => bool)
                       ((All::(real => bool) => bool)
                         (%z::real.
                             (op -->::bool => bool => bool)
                              ((op <=::real => real => bool)
                                ((abs::real => real)
                                  ((op -::real => real => real) z x))
                                d)
                              ((op <=::real => real => bool) (f z)
                                (f x)))))))))"
  by (import lim CONT_INJ_LEMMA)

lemma CONT_INJ_LEMMA2: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%x::real.
               (All::(real => bool) => bool)
                (%d::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((op <::real => real => bool) (0::real) d)
                       ((op &::bool => bool => bool)
                         ((All::(real => bool) => bool)
                           (%z::real.
                               (op -->::bool => bool => bool)
                                ((op <=::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) z x))
                                  d)
                                ((op =::real => real => bool) (g (f z)) z)))
                         ((All::(real => bool) => bool)
                           (%z::real.
                               (op -->::bool => bool => bool)
                                ((op <=::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) z x))
                                  d)
                                ((contl::(real => real) => real => bool) f
                                  z)))))
                     ((Not::bool => bool)
                       ((All::(real => bool) => bool)
                         (%z::real.
                             (op -->::bool => bool => bool)
                              ((op <=::real => real => bool)
                                ((abs::real => real)
                                  ((op -::real => real => real) z x))
                                d)
                              ((op <=::real => real => bool) (f x)
                                (f z)))))))))"
  by (import lim CONT_INJ_LEMMA2)

lemma CONT_INJ_RANGE: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%x::real.
               (All::(real => bool) => bool)
                (%d::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((op <::real => real => bool) (0::real) d)
                       ((op &::bool => bool => bool)
                         ((All::(real => bool) => bool)
                           (%z::real.
                               (op -->::bool => bool => bool)
                                ((op <=::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) z x))
                                  d)
                                ((op =::real => real => bool) (g (f z)) z)))
                         ((All::(real => bool) => bool)
                           (%z::real.
                               (op -->::bool => bool => bool)
                                ((op <=::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) z x))
                                  d)
                                ((contl::(real => real) => real => bool) f
                                  z)))))
                     ((Ex::(real => bool) => bool)
                       (%e::real.
                           (op &::bool => bool => bool)
                            ((op <::real => real => bool) (0::real) e)
                            ((All::(real => bool) => bool)
                              (%y::real.
                                  (op -->::bool => bool => bool)
                                   ((op <=::real => real => bool)
                                     ((abs::real => real)
 ((op -::real => real => real) y (f x)))
                                     e)
                                   ((Ex::(real => bool) => bool)
                                     (%z::real.
   (op &::bool => bool => bool)
    ((op <=::real => real => bool)
      ((abs::real => real) ((op -::real => real => real) z x)) d)
    ((op =::real => real => bool) (f z) y)))))))))))"
  by (import lim CONT_INJ_RANGE)

lemma CONT_INVERSE: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%x::real.
               (All::(real => bool) => bool)
                (%d::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((op <::real => real => bool) (0::real) d)
                       ((op &::bool => bool => bool)
                         ((All::(real => bool) => bool)
                           (%z::real.
                               (op -->::bool => bool => bool)
                                ((op <=::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) z x))
                                  d)
                                ((op =::real => real => bool) (g (f z)) z)))
                         ((All::(real => bool) => bool)
                           (%z::real.
                               (op -->::bool => bool => bool)
                                ((op <=::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real) z x))
                                  d)
                                ((contl::(real => real) => real => bool) f
                                  z)))))
                     ((contl::(real => real) => real => bool) g (f x))))))"
  by (import lim CONT_INVERSE)

lemma DIFF_INVERSE: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%x::real.
                    (All::(real => bool) => bool)
                     (%d::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((op <::real => real => bool) (0::real) d)
                            ((op &::bool => bool => bool)
                              ((All::(real => bool) => bool)
                                (%z::real.
                                    (op -->::bool => bool => bool)
                                     ((op <=::real => real => bool)
 ((abs::real => real) ((op -::real => real => real) z x)) d)
                                     ((op =::real => real => bool) (g (f z))
 z)))
                              ((op &::bool => bool => bool)
                                ((All::(real => bool) => bool)
                                  (%z::real.
(op -->::bool => bool => bool)
 ((op <=::real => real => bool)
   ((abs::real => real) ((op -::real => real => real) z x)) d)
 ((contl::(real => real) => real => bool) f z)))
                                ((op &::bool => bool => bool)
                                  ((diffl::(real => real)
     => real => real => bool)
                                    f l x)
                                  ((Not::bool => bool)
                                    ((op =::real => real => bool) l
(0::real)))))))
                          ((diffl::(real => real) => real => real => bool) g
                            ((inverse::real => real) l) (f x)))))))"
  by (import lim DIFF_INVERSE)

lemma DIFF_INVERSE_LT: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%x::real.
                    (All::(real => bool) => bool)
                     (%d::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((op <::real => real => bool) (0::real) d)
                            ((op &::bool => bool => bool)
                              ((All::(real => bool) => bool)
                                (%z::real.
                                    (op -->::bool => bool => bool)
                                     ((op <::real => real => bool)
 ((abs::real => real) ((op -::real => real => real) z x)) d)
                                     ((op =::real => real => bool) (g (f z))
 z)))
                              ((op &::bool => bool => bool)
                                ((All::(real => bool) => bool)
                                  (%z::real.
(op -->::bool => bool => bool)
 ((op <::real => real => bool)
   ((abs::real => real) ((op -::real => real => real) z x)) d)
 ((contl::(real => real) => real => bool) f z)))
                                ((op &::bool => bool => bool)
                                  ((diffl::(real => real)
     => real => real => bool)
                                    f l x)
                                  ((Not::bool => bool)
                                    ((op =::real => real => bool) l
(0::real)))))))
                          ((diffl::(real => real) => real => real => bool) g
                            ((inverse::real => real) l) (f x)))))))"
  by (import lim DIFF_INVERSE_LT)

lemma INTERVAL_CLEMMA: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real => bool) => bool)
      (%b::real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) a x)
                  ((op <::real => real => bool) x b))
                ((Ex::(real => bool) => bool)
                  (%d::real.
                      (op &::bool => bool => bool)
                       ((op <::real => real => bool) (0::real) d)
                       ((All::(real => bool) => bool)
                         (%y::real.
                             (op -->::bool => bool => bool)
                              ((op <=::real => real => bool)
                                ((abs::real => real)
                                  ((op -::real => real => real) y x))
                                d)
                              ((op &::bool => bool => bool)
                                ((op <::real => real => bool) a y)
                                ((op <::real => real => bool) y b)))))))))"
  by (import lim INTERVAL_CLEMMA)

lemma DIFF_INVERSE_OPEN: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (All::(real => bool) => bool)
           (%l::real.
               (All::(real => bool) => bool)
                (%a::real.
                    (All::(real => bool) => bool)
                     (%x::real.
                         (All::(real => bool) => bool)
                          (%b::real.
                              (op -->::bool => bool => bool)
                               ((op &::bool => bool => bool)
                                 ((op <::real => real => bool) a x)
                                 ((op &::bool => bool => bool)
                                   ((op <::real => real => bool) x b)
                                   ((op &::bool => bool => bool)
                                     ((All::(real => bool) => bool)
 (%z::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool) ((op <::real => real => bool) a z)
        ((op <::real => real => bool) z b))
      ((op &::bool => bool => bool)
        ((op =::real => real => bool) (g (f z)) z)
        ((contl::(real => real) => real => bool) f z))))
                                     ((op &::bool => bool => bool)
 ((diffl::(real => real) => real => real => bool) f l x)
 ((Not::bool => bool) ((op =::real => real => bool) l (0::real)))))))
                               ((diffl::(real => real)
  => real => real => bool)
                                 g ((inverse::real => real) l) (f x))))))))"
  by (import lim DIFF_INVERSE_OPEN)

;end_setup

;setup_theory powser

lemma POWDIFF_LEMMA: "ALL (n::nat) (x::real) y::real.
   real.sum (0::nat, Suc n) (%p::nat. x ^ p * y ^ (Suc n - p)) =
   y * real.sum (0::nat, Suc n) (%p::nat. x ^ p * y ^ (n - p))"
  by (import powser POWDIFF_LEMMA)

lemma POWDIFF: "ALL (n::nat) (x::real) y::real.
   x ^ Suc n - y ^ Suc n =
   (x - y) * real.sum (0::nat, Suc n) (%p::nat. x ^ p * y ^ (n - p))"
  by (import powser POWDIFF)

lemma POWREV: "ALL (n::nat) (x::real) y::real.
   real.sum (0::nat, Suc n) (%xa::nat. x ^ xa * y ^ (n - xa)) =
   real.sum (0::nat, Suc n) (%xa::nat. x ^ (n - xa) * y ^ xa)"
  by (import powser POWREV)

lemma POWSER_INSIDEA: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(real => bool) => bool)
      (%x::real.
          (All::(real => bool) => bool)
           (%z::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((summable::(nat => real) => bool)
                    (%n::nat.
                        (op *::real => real => real) (f n)
                         ((op ^::real => nat => real) x n)))
                  ((op <::real => real => bool) ((abs::real => real) z)
                    ((abs::real => real) x)))
                ((summable::(nat => real) => bool)
                  (%n::nat.
                      (op *::real => real => real)
                       ((abs::real => real) (f n))
                       ((op ^::real => nat => real) z n))))))"
  by (import powser POWSER_INSIDEA)

lemma POWSER_INSIDE: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::(real => bool) => bool)
      (%x::real.
          (All::(real => bool) => bool)
           (%z::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((summable::(nat => real) => bool)
                    (%n::nat.
                        (op *::real => real => real) (f n)
                         ((op ^::real => nat => real) x n)))
                  ((op <::real => real => bool) ((abs::real => real) z)
                    ((abs::real => real) x)))
                ((summable::(nat => real) => bool)
                  (%n::nat.
                      (op *::real => real => real) (f n)
                       ((op ^::real => nat => real) z n))))))"
  by (import powser POWSER_INSIDE)

constdefs
  diffs :: "(nat => real) => nat => real" 
  "diffs == %(c::nat => real) n::nat. real (Suc n) * c (Suc n)"

lemma diffs: "ALL c::nat => real. diffs c = (%n::nat. real (Suc n) * c (Suc n))"
  by (import powser diffs)

lemma DIFFS_NEG: "ALL c::nat => real. diffs (%n::nat. - c n) = (%x::nat. - diffs c x)"
  by (import powser DIFFS_NEG)

lemma DIFFS_LEMMA: "ALL (n::nat) (c::nat => real) x::real.
   real.sum (0::nat, n) (%n::nat. diffs c n * x ^ n) =
   real.sum (0::nat, n) (%n::nat. real n * (c n * x ^ (n - (1::nat)))) +
   real n * (c n * x ^ (n - (1::nat)))"
  by (import powser DIFFS_LEMMA)

lemma DIFFS_LEMMA2: "ALL (n::nat) (c::nat => real) x::real.
   real.sum (0::nat, n) (%n::nat. real n * (c n * x ^ (n - (1::nat)))) =
   real.sum (0::nat, n) (%n::nat. diffs c n * x ^ n) -
   real n * (c n * x ^ (n - (1::nat)))"
  by (import powser DIFFS_LEMMA2)

lemma DIFFS_EQUIV: "(All::((nat => real) => bool) => bool)
 (%c::nat => real.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((summable::(nat => real) => bool)
             (%n::nat.
                 (op *::real => real => real)
                  ((diffs::(nat => real) => nat => real) c n)
                  ((op ^::real => nat => real) x n)))
           ((sums::(nat => real) => real => bool)
             (%n::nat.
                 (op *::real => real => real) ((real::nat => real) n)
                  ((op *::real => real => real) (c n)
                    ((op ^::real => nat => real) x
                      ((op -::nat => nat => nat) n (1::nat)))))
             ((suminf::(nat => real) => real)
               (%n::nat.
                   (op *::real => real => real)
                    ((diffs::(nat => real) => nat => real) c n)
                    ((op ^::real => nat => real) x n))))))"
  by (import powser DIFFS_EQUIV)

lemma TERMDIFF_LEMMA1: "ALL (m::nat) (z::real) h::real.
   real.sum (0::nat, m) (%p::nat. (z + h) ^ (m - p) * z ^ p - z ^ m) =
   real.sum (0::nat, m) (%p::nat. z ^ p * ((z + h) ^ (m - p) - z ^ (m - p)))"
  by (import powser TERMDIFF_LEMMA1)

lemma TERMDIFF_LEMMA2: "(All::(real => bool) => bool)
 (%z::real.
     (All::(real => bool) => bool)
      (%h::real.
          (All::(nat => bool) => bool)
           (%n::nat.
               (op -->::bool => bool => bool)
                ((Not::bool => bool)
                  ((op =::real => real => bool) h (0::real)))
                ((op =::real => real => bool)
                  ((op -::real => real => real)
                    ((op /::real => real => real)
                      ((op -::real => real => real)
                        ((op ^::real => nat => real)
                          ((op +::real => real => real) z h) n)
                        ((op ^::real => nat => real) z n))
                      h)
                    ((op *::real => real => real) ((real::nat => real) n)
                      ((op ^::real => nat => real) z
                        ((op -::nat => nat => nat) n (1::nat)))))
                  ((op *::real => real => real) h
                    ((real.sum::nat * nat => (nat => real) => real)
                      ((Pair::nat => nat => nat * nat) (0::nat)
                        ((op -::nat => nat => nat) n (1::nat)))
                      (%p::nat.
                          (op *::real => real => real)
                           ((op ^::real => nat => real) z p)
                           ((real.sum::nat * nat => (nat => real) => real)
                             ((Pair::nat => nat => nat * nat) (0::nat)
                               ((op -::nat => nat => nat)
                                 ((op -::nat => nat => nat) n (1::nat)) p))
                             (%q::nat.
                                 (op *::real => real => real)
                                  ((op ^::real => nat => real)
                                    ((op +::real => real => real) z h) q)
                                  ((op ^::real => nat => real) z
                                    ((op -::nat => nat => nat)
((op -::nat => nat => nat)
  ((op -::nat => nat => nat) n
    ((number_of::bin => nat)
      ((op BIT::bin => bit => bin)
        ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
        (bit.B0::bit))))
  p)
q)))))))))))"
  by (import powser TERMDIFF_LEMMA2)

lemma TERMDIFF_LEMMA3: "(All::(real => bool) => bool)
 (%z::real.
     (All::(real => bool) => bool)
      (%h::real.
          (All::(nat => bool) => bool)
           (%n::nat.
               (All::(real => bool) => bool)
                (%k'::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((Not::bool => bool)
                         ((op =::real => real => bool) h (0::real)))
                       ((op &::bool => bool => bool)
                         ((op <=::real => real => bool)
                           ((abs::real => real) z) k')
                         ((op <=::real => real => bool)
                           ((abs::real => real)
                             ((op +::real => real => real) z h))
                           k')))
                     ((op <=::real => real => bool)
                       ((abs::real => real)
                         ((op -::real => real => real)
                           ((op /::real => real => real)
                             ((op -::real => real => real)
                               ((op ^::real => nat => real)
                                 ((op +::real => real => real) z h) n)
                               ((op ^::real => nat => real) z n))
                             h)
                           ((op *::real => real => real)
                             ((real::nat => real) n)
                             ((op ^::real => nat => real) z
                               ((op -::nat => nat => nat) n (1::nat))))))
                       ((op *::real => real => real) ((real::nat => real) n)
                         ((op *::real => real => real)
                           ((real::nat => real)
                             ((op -::nat => nat => nat) n (1::nat)))
                           ((op *::real => real => real)
                             ((op ^::real => nat => real) k'
                               ((op -::nat => nat => nat) n
                                 ((number_of::bin => nat)
                                   ((op BIT::bin => bit => bin)
                                     ((op BIT::bin => bit => bin)
 (Numeral.Pls::bin) (bit.B1::bit))
                                     (bit.B0::bit)))))
                             ((abs::real => real) h)))))))))"
  by (import powser TERMDIFF_LEMMA3)

lemma TERMDIFF_LEMMA4: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::(real => bool) => bool)
      (%k'::real.
          (All::(real => bool) => bool)
           (%k::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) (0::real) k)
                  ((All::(real => bool) => bool)
                    (%h::real.
                        (op -->::bool => bool => bool)
                         ((op &::bool => bool => bool)
                           ((op <::real => real => bool) (0::real)
                             ((abs::real => real) h))
                           ((op <::real => real => bool)
                             ((abs::real => real) h) k))
                         ((op <=::real => real => bool)
                           ((abs::real => real) (f h))
                           ((op *::real => real => real) k'
                             ((abs::real => real) h))))))
                ((tends_real_real::(real => real) => real => real => bool) f
                  (0::real) (0::real)))))"
  by (import powser TERMDIFF_LEMMA4)

lemma TERMDIFF_LEMMA5: "(All::((nat => real) => bool) => bool)
 (%f::nat => real.
     (All::((real => nat => real) => bool) => bool)
      (%g::real => nat => real.
          (All::(real => bool) => bool)
           (%k::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) (0::real) k)
                  ((op &::bool => bool => bool)
                    ((summable::(nat => real) => bool) f)
                    ((All::(real => bool) => bool)
                      (%h::real.
                          (op -->::bool => bool => bool)
                           ((op &::bool => bool => bool)
                             ((op <::real => real => bool) (0::real)
                               ((abs::real => real) h))
                             ((op <::real => real => bool)
                               ((abs::real => real) h) k))
                           ((All::(nat => bool) => bool)
                             (%n::nat.
                                 (op <=::real => real => bool)
                                  ((abs::real => real) (g h n))
                                  ((op *::real => real => real) (f n)
                                    ((abs::real => real) h))))))))
                ((tends_real_real::(real => real) => real => real => bool)
                  (%h::real. (suminf::(nat => real) => real) (g h))
                  (0::real) (0::real)))))"
  by (import powser TERMDIFF_LEMMA5)

lemma TERMDIFF: "(All::((nat => real) => bool) => bool)
 (%c::nat => real.
     (All::(real => bool) => bool)
      (%k'::real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((summable::(nat => real) => bool)
                    (%n::nat.
                        (op *::real => real => real) (c n)
                         ((op ^::real => nat => real) k' n)))
                  ((op &::bool => bool => bool)
                    ((summable::(nat => real) => bool)
                      (%n::nat.
                          (op *::real => real => real)
                           ((diffs::(nat => real) => nat => real) c n)
                           ((op ^::real => nat => real) k' n)))
                    ((op &::bool => bool => bool)
                      ((summable::(nat => real) => bool)
                        (%n::nat.
                            (op *::real => real => real)
                             ((diffs::(nat => real) => nat => real)
                               ((diffs::(nat => real) => nat => real) c) n)
                             ((op ^::real => nat => real) k' n)))
                      ((op <::real => real => bool) ((abs::real => real) x)
                        ((abs::real => real) k')))))
                ((diffl::(real => real) => real => real => bool)
                  (%x::real.
                      (suminf::(nat => real) => real)
                       (%n::nat.
                           (op *::real => real => real) (c n)
                            ((op ^::real => nat => real) x n)))
                  ((suminf::(nat => real) => real)
                    (%n::nat.
                        (op *::real => real => real)
                         ((diffs::(nat => real) => nat => real) c n)
                         ((op ^::real => nat => real) x n)))
                  x))))"
  by (import powser TERMDIFF)

;end_setup

;setup_theory transc

constdefs
  exp :: "real => real" 
  "exp == %x::real. suminf (%n::nat. inverse (real (FACT n)) * x ^ n)"

lemma exp: "ALL x::real. exp x = suminf (%n::nat. inverse (real (FACT n)) * x ^ n)"
  by (import transc exp)

constdefs
  cos :: "real => real" 
  "(cos ==
 (%(x::real).
     (suminf
       (%(n::nat).
           ((if (EVEN n)
             then (((- (1::real)) ^ (n div (2::nat))) / (real (FACT n)))
             else (0::real)) *
            (x ^ n))))))"

lemma cos: "(ALL (x::real).
    ((cos x) =
     (suminf
       (%(n::nat).
           ((if (EVEN n)
             then (((- (1::real)) ^ (n div (2::nat))) / (real (FACT n)))
             else (0::real)) *
            (x ^ n))))))"
  by (import transc cos)

constdefs
  sin :: "real => real" 
  "sin ==
%x::real.
   suminf
    (%n::nat.
        (if EVEN n then 0::real
         else (- (1::real)) ^ ((n - (1::nat)) div (2::nat)) /
              real (FACT n)) *
        x ^ n)"

lemma sin: "ALL x::real.
   sin x =
   suminf
    (%n::nat.
        (if EVEN n then 0::real
         else (- (1::real)) ^ ((n - (1::nat)) div (2::nat)) /
              real (FACT n)) *
        x ^ n)"
  by (import transc sin)

lemma EXP_CONVERGES: "ALL x::real. sums (%n::nat. inverse (real (FACT n)) * x ^ n) (exp x)"
  by (import transc EXP_CONVERGES)

lemma SIN_CONVERGES: "ALL x::real.
   sums
    (%n::nat.
        (if EVEN n then 0::real
         else (- (1::real)) ^ ((n - (1::nat)) div (2::nat)) /
              real (FACT n)) *
        x ^ n)
    (sin x)"
  by (import transc SIN_CONVERGES)

lemma COS_CONVERGES: "(ALL (x::real).
    (sums
      (%(n::nat).
          ((if (EVEN n)
            then (((- (1::real)) ^ (n div (2::nat))) / (real (FACT n)))
            else (0::real)) *
           (x ^ n)))
      (cos x)))"
  by (import transc COS_CONVERGES)

lemma EXP_FDIFF: "diffs (%n::nat. inverse (real (FACT n))) =
(%n::nat. inverse (real (FACT n)))"
  by (import transc EXP_FDIFF)

lemma SIN_FDIFF: "((diffs
   (%(n::nat).
       (if (EVEN n) then (0::real)
        else (((- (1::real)) ^ ((n - (1::nat)) div (2::nat))) /
              (real (FACT n)))))) =
 (%(n::nat).
     (if (EVEN n)
      then (((- (1::real)) ^ (n div (2::nat))) / (real (FACT n)))
      else (0::real))))"
  by (import transc SIN_FDIFF)

lemma COS_FDIFF: "((diffs
   (%(n::nat).
       (if (EVEN n)
        then (((- (1::real)) ^ (n div (2::nat))) / (real (FACT n)))
        else (0::real)))) =
 (%(n::nat).
     (- (if (EVEN n) then (0::real)
         else (((- (1::real)) ^ ((n - (1::nat)) div (2::nat))) /
               (real (FACT n)))))))"
  by (import transc COS_FDIFF)

lemma SIN_NEGLEMMA: "ALL x::real.
   - sin x =
   suminf
    (%n::nat.
        - ((if EVEN n then 0::real
            else (- (1::real)) ^ ((n - (1::nat)) div (2::nat)) /
                 real (FACT n)) *
           x ^ n))"
  by (import transc SIN_NEGLEMMA)

lemma DIFF_EXP: "ALL x::real. diffl exp (exp x) x"
  by (import transc DIFF_EXP)

lemma DIFF_SIN: "ALL x::real. diffl sin (cos x) x"
  by (import transc DIFF_SIN)

lemma DIFF_COS: "ALL x::real. diffl cos (- sin x) x"
  by (import transc DIFF_COS)

lemma DIFF_COMPOSITE: "(op &::bool => bool => bool)
 ((op -->::bool => bool => bool)
   ((op &::bool => bool => bool)
     ((diffl::(real => real) => real => real => bool) (f::real => real)
       (l::real) (x::real))
     ((Not::bool => bool) ((op =::real => real => bool) (f x) (0::real))))
   ((diffl::(real => real) => real => real => bool)
     (%x::real. (inverse::real => real) (f x))
     ((uminus::real => real)
       ((op /::real => real => real) l
         ((op ^::real => nat => real) (f x)
           ((number_of::bin => nat)
             ((op BIT::bin => bit => bin)
               ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                 (bit.B1::bit))
               (bit.B0::bit))))))
     x))
 ((op &::bool => bool => bool)
   ((op -->::bool => bool => bool)
     ((op &::bool => bool => bool)
       ((diffl::(real => real) => real => real => bool) f l x)
       ((op &::bool => bool => bool)
         ((diffl::(real => real) => real => real => bool) (g::real => real)
           (m::real) x)
         ((Not::bool => bool)
           ((op =::real => real => bool) (g x) (0::real)))))
     ((diffl::(real => real) => real => real => bool)
       (%x::real. (op /::real => real => real) (f x) (g x))
       ((op /::real => real => real)
         ((op -::real => real => real)
           ((op *::real => real => real) l (g x))
           ((op *::real => real => real) m (f x)))
         ((op ^::real => nat => real) (g x)
           ((number_of::bin => nat)
             ((op BIT::bin => bit => bin)
               ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                 (bit.B1::bit))
               (bit.B0::bit)))))
       x))
   ((op &::bool => bool => bool)
     ((op -->::bool => bool => bool)
       ((op &::bool => bool => bool)
         ((diffl::(real => real) => real => real => bool) f l x)
         ((diffl::(real => real) => real => real => bool) g m x))
       ((diffl::(real => real) => real => real => bool)
         (%x::real. (op +::real => real => real) (f x) (g x))
         ((op +::real => real => real) l m) x))
     ((op &::bool => bool => bool)
       ((op -->::bool => bool => bool)
         ((op &::bool => bool => bool)
           ((diffl::(real => real) => real => real => bool) f l x)
           ((diffl::(real => real) => real => real => bool) g m x))
         ((diffl::(real => real) => real => real => bool)
           (%x::real. (op *::real => real => real) (f x) (g x))
           ((op +::real => real => real)
             ((op *::real => real => real) l (g x))
             ((op *::real => real => real) m (f x)))
           x))
       ((op &::bool => bool => bool)
         ((op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((diffl::(real => real) => real => real => bool) f l x)
             ((diffl::(real => real) => real => real => bool) g m x))
           ((diffl::(real => real) => real => real => bool)
             (%x::real. (op -::real => real => real) (f x) (g x))
             ((op -::real => real => real) l m) x))
         ((op &::bool => bool => bool)
           ((op -->::bool => bool => bool)
             ((diffl::(real => real) => real => real => bool) f l x)
             ((diffl::(real => real) => real => real => bool)
               (%x::real. (uminus::real => real) (f x))
               ((uminus::real => real) l) x))
           ((op &::bool => bool => bool)
             ((op -->::bool => bool => bool)
               ((diffl::(real => real) => real => real => bool) g m x)
               ((diffl::(real => real) => real => real => bool)
                 (%x::real. (op ^::real => nat => real) (g x) (n::nat))
                 ((op *::real => real => real)
                   ((op *::real => real => real) ((real::nat => real) n)
                     ((op ^::real => nat => real) (g x)
                       ((op -::nat => nat => nat) n (1::nat))))
                   m)
                 x))
             ((op &::bool => bool => bool)
               ((op -->::bool => bool => bool)
                 ((diffl::(real => real) => real => real => bool) g m x)
                 ((diffl::(real => real) => real => real => bool)
                   (%x::real. (exp::real => real) (g x))
                   ((op *::real => real => real) ((exp::real => real) (g x))
                     m)
                   x))
               ((op &::bool => bool => bool)
                 ((op -->::bool => bool => bool)
                   ((diffl::(real => real) => real => real => bool) g m x)
                   ((diffl::(real => real) => real => real => bool)
                     (%x::real. (sin::real => real) (g x))
                     ((op *::real => real => real)
                       ((cos::real => real) (g x)) m)
                     x))
                 ((op -->::bool => bool => bool)
                   ((diffl::(real => real) => real => real => bool) g m x)
                   ((diffl::(real => real) => real => real => bool)
                     (%x::real. (cos::real => real) (g x))
                     ((op *::real => real => real)
                       ((uminus::real => real) ((sin::real => real) (g x)))
                       m)
                     x))))))))))"
  by (import transc DIFF_COMPOSITE)

lemma EXP_0: "exp (0::real) = (1::real)"
  by (import transc EXP_0)

lemma EXP_LE_X: "ALL x>=0::real. (1::real) + x <= exp x"
  by (import transc EXP_LE_X)

lemma EXP_LT_1: "ALL x>0::real. (1::real) < exp x"
  by (import transc EXP_LT_1)

lemma EXP_ADD_MUL: "ALL (x::real) y::real. exp (x + y) * exp (- x) = exp y"
  by (import transc EXP_ADD_MUL)

lemma EXP_NEG_MUL: "ALL x::real. exp x * exp (- x) = (1::real)"
  by (import transc EXP_NEG_MUL)

lemma EXP_NEG_MUL2: "ALL x::real. exp (- x) * exp x = (1::real)"
  by (import transc EXP_NEG_MUL2)

lemma EXP_NEG: "ALL x::real. exp (- x) = inverse (exp x)"
  by (import transc EXP_NEG)

lemma EXP_ADD: "ALL (x::real) y::real. exp (x + y) = exp x * exp y"
  by (import transc EXP_ADD)

lemma EXP_POS_LE: "ALL x::real. (0::real) <= exp x"
  by (import transc EXP_POS_LE)

lemma EXP_NZ: "ALL x::real. exp x ~= (0::real)"
  by (import transc EXP_NZ)

lemma EXP_POS_LT: "ALL x::real. (0::real) < exp x"
  by (import transc EXP_POS_LT)

lemma EXP_N: "ALL (n::nat) x::real. exp (real n * x) = exp x ^ n"
  by (import transc EXP_N)

lemma EXP_SUB: "ALL (x::real) y::real. exp (x - y) = exp x / exp y"
  by (import transc EXP_SUB)

lemma EXP_MONO_IMP: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%y::real.
          (op -->::bool => bool => bool) ((op <::real => real => bool) x y)
           ((op <::real => real => bool) ((exp::real => real) x)
             ((exp::real => real) y))))"
  by (import transc EXP_MONO_IMP)

lemma EXP_MONO_LT: "ALL (x::real) y::real. (exp x < exp y) = (x < y)"
  by (import transc EXP_MONO_LT)

lemma EXP_MONO_LE: "ALL (x::real) y::real. (exp x <= exp y) = (x <= y)"
  by (import transc EXP_MONO_LE)

lemma EXP_INJ: "ALL (x::real) y::real. (exp x = exp y) = (x = y)"
  by (import transc EXP_INJ)

lemma EXP_TOTAL_LEMMA: "ALL y>=1::real. EX x>=0::real. x <= y - (1::real) & exp x = y"
  by (import transc EXP_TOTAL_LEMMA)

lemma EXP_TOTAL: "ALL y>0::real. EX x::real. exp x = y"
  by (import transc EXP_TOTAL)

constdefs
  ln :: "real => real" 
  "ln == %x::real. SOME u::real. exp u = x"

lemma ln: "ALL x::real. ln x = (SOME u::real. exp u = x)"
  by (import transc ln)

lemma LN_EXP: "ALL x::real. ln (exp x) = x"
  by (import transc LN_EXP)

lemma EXP_LN: "ALL x::real. (exp (ln x) = x) = ((0::real) < x)"
  by (import transc EXP_LN)

lemma LN_MUL: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%y::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <::real => real => bool) (0::real) x)
             ((op <::real => real => bool) (0::real) y))
           ((op =::real => real => bool)
             ((ln::real => real) ((op *::real => real => real) x y))
             ((op +::real => real => real) ((ln::real => real) x)
               ((ln::real => real) y)))))"
  by (import transc LN_MUL)

lemma LN_INJ: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%y::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <::real => real => bool) (0::real) x)
             ((op <::real => real => bool) (0::real) y))
           ((op =::bool => bool => bool)
             ((op =::real => real => bool) ((ln::real => real) x)
               ((ln::real => real) y))
             ((op =::real => real => bool) x y))))"
  by (import transc LN_INJ)

lemma LN_1: "ln (1::real) = (0::real)"
  by (import transc LN_1)

lemma LN_INV: "ALL x>0::real. ln (inverse x) = - ln x"
  by (import transc LN_INV)

lemma LN_DIV: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%y::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <::real => real => bool) (0::real) x)
             ((op <::real => real => bool) (0::real) y))
           ((op =::real => real => bool)
             ((ln::real => real) ((op /::real => real => real) x y))
             ((op -::real => real => real) ((ln::real => real) x)
               ((ln::real => real) y)))))"
  by (import transc LN_DIV)

lemma LN_MONO_LT: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%y::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <::real => real => bool) (0::real) x)
             ((op <::real => real => bool) (0::real) y))
           ((op =::bool => bool => bool)
             ((op <::real => real => bool) ((ln::real => real) x)
               ((ln::real => real) y))
             ((op <::real => real => bool) x y))))"
  by (import transc LN_MONO_LT)

lemma LN_MONO_LE: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%y::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <::real => real => bool) (0::real) x)
             ((op <::real => real => bool) (0::real) y))
           ((op =::bool => bool => bool)
             ((op <=::real => real => bool) ((ln::real => real) x)
               ((ln::real => real) y))
             ((op <=::real => real => bool) x y))))"
  by (import transc LN_MONO_LE)

lemma LN_POW: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op <::real => real => bool) (0::real) x)
           ((op =::real => real => bool)
             ((ln::real => real) ((op ^::real => nat => real) x n))
             ((op *::real => real => real) ((real::nat => real) n)
               ((ln::real => real) x)))))"
  by (import transc LN_POW)

lemma LN_LE: "ALL x>=0::real. ln ((1::real) + x) <= x"
  by (import transc LN_LE)

lemma LN_LT_X: "ALL x>0::real. ln x < x"
  by (import transc LN_LT_X)

lemma LN_POS: "ALL x>=1::real. (0::real) <= ln x"
  by (import transc LN_POS)

constdefs
  root :: "nat => real => real" 
  "(op ==::(nat => real => real) => (nat => real => real) => prop)
 (root::nat => real => real)
 (%(n::nat) x::real.
     (Eps::(real => bool) => real)
      (%u::real.
          (op &::bool => bool => bool)
           ((op -->::bool => bool => bool)
             ((op <::real => real => bool) (0::real) x)
             ((op <::real => real => bool) (0::real) u))
           ((op =::real => real => bool) ((op ^::real => nat => real) u n)
             x)))"

lemma root: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (op =::real => real => bool) ((root::nat => real => real) n x)
           ((Eps::(real => bool) => real)
             (%u::real.
                 (op &::bool => bool => bool)
                  ((op -->::bool => bool => bool)
                    ((op <::real => real => bool) (0::real) x)
                    ((op <::real => real => bool) (0::real) u))
                  ((op =::real => real => bool)
                    ((op ^::real => nat => real) u n) x)))))"
  by (import transc root)

constdefs
  sqrt :: "real => real" 
  "sqrt == root (2::nat)"

lemma sqrt: "ALL x::real. sqrt x = root (2::nat) x"
  by (import transc sqrt)

lemma ROOT_LT_LEMMA: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op <::real => real => bool) (0::real) x)
           ((op =::real => real => bool)
             ((op ^::real => nat => real)
               ((exp::real => real)
                 ((op /::real => real => real) ((ln::real => real) x)
                   ((real::nat => real) ((Suc::nat => nat) n))))
               ((Suc::nat => nat) n))
             x)))"
  by (import transc ROOT_LT_LEMMA)

lemma ROOT_LN: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op <::real => real => bool) (0::real) x)
           ((op =::real => real => bool)
             ((root::nat => real => real) ((Suc::nat => nat) n) x)
             ((exp::real => real)
               ((op /::real => real => real) ((ln::real => real) x)
                 ((real::nat => real) ((Suc::nat => nat) n)))))))"
  by (import transc ROOT_LN)

lemma ROOT_0: "ALL n::nat. root (Suc n) (0::real) = (0::real)"
  by (import transc ROOT_0)

lemma ROOT_1: "ALL n::nat. root (Suc n) (1::real) = (1::real)"
  by (import transc ROOT_1)

lemma ROOT_POS_LT: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op <::real => real => bool) (0::real) x)
           ((op <::real => real => bool) (0::real)
             ((root::nat => real => real) ((Suc::nat => nat) n) x))))"
  by (import transc ROOT_POS_LT)

lemma ROOT_POW_POS: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op <=::real => real => bool) (0::real) x)
           ((op =::real => real => bool)
             ((op ^::real => nat => real)
               ((root::nat => real => real) ((Suc::nat => nat) n) x)
               ((Suc::nat => nat) n))
             x)))"
  by (import transc ROOT_POW_POS)

lemma POW_ROOT_POS: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op <=::real => real => bool) (0::real) x)
           ((op =::real => real => bool)
             ((root::nat => real => real) ((Suc::nat => nat) n)
               ((op ^::real => nat => real) x ((Suc::nat => nat) n)))
             x)))"
  by (import transc POW_ROOT_POS)

lemma ROOT_POS: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op <=::real => real => bool) (0::real) x)
           ((op <=::real => real => bool) (0::real)
             ((root::nat => real => real) ((Suc::nat => nat) n) x))))"
  by (import transc ROOT_POS)

lemma ROOT_POS_UNIQ: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (All::(real => bool) => bool)
           (%y::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::real => real => bool) (0::real) x)
                  ((op &::bool => bool => bool)
                    ((op <=::real => real => bool) (0::real) y)
                    ((op =::real => real => bool)
                      ((op ^::real => nat => real) y ((Suc::nat => nat) n))
                      x)))
                ((op =::real => real => bool)
                  ((root::nat => real => real) ((Suc::nat => nat) n) x)
                  y))))"
  by (import transc ROOT_POS_UNIQ)

lemma ROOT_MUL: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (All::(real => bool) => bool)
           (%y::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::real => real => bool) (0::real) x)
                  ((op <=::real => real => bool) (0::real) y))
                ((op =::real => real => bool)
                  ((root::nat => real => real) ((Suc::nat => nat) n)
                    ((op *::real => real => real) x y))
                  ((op *::real => real => real)
                    ((root::nat => real => real) ((Suc::nat => nat) n) x)
                    ((root::nat => real => real) ((Suc::nat => nat) n)
                      y))))))"
  by (import transc ROOT_MUL)

lemma ROOT_INV: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool)
           ((op <=::real => real => bool) (0::real) x)
           ((op =::real => real => bool)
             ((root::nat => real => real) ((Suc::nat => nat) n)
               ((inverse::real => real) x))
             ((inverse::real => real)
               ((root::nat => real => real) ((Suc::nat => nat) n) x)))))"
  by (import transc ROOT_INV)

lemma ROOT_DIV: "(All::(nat => bool) => bool)
 (%x::nat.
     (All::(real => bool) => bool)
      (%xa::real.
          (All::(real => bool) => bool)
           (%xb::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::real => real => bool) (0::real) xa)
                  ((op <=::real => real => bool) (0::real) xb))
                ((op =::real => real => bool)
                  ((root::nat => real => real) ((Suc::nat => nat) x)
                    ((op /::real => real => real) xa xb))
                  ((op /::real => real => real)
                    ((root::nat => real => real) ((Suc::nat => nat) x) xa)
                    ((root::nat => real => real) ((Suc::nat => nat) x)
                      xb))))))"
  by (import transc ROOT_DIV)

lemma ROOT_MONO_LE: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%y::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <=::real => real => bool) (0::real) x)
             ((op <=::real => real => bool) x y))
           ((op <=::real => real => bool)
             ((root::nat => real => real) ((Suc::nat => nat) (n::nat)) x)
             ((root::nat => real => real) ((Suc::nat => nat) n) y))))"
  by (import transc ROOT_MONO_LE)

lemma SQRT_0: "sqrt (0::real) = (0::real)"
  by (import transc SQRT_0)

lemma SQRT_1: "sqrt (1::real) = (1::real)"
  by (import transc SQRT_1)

lemma SQRT_POS_LT: "ALL x>0::real. (0::real) < sqrt x"
  by (import transc SQRT_POS_LT)

lemma SQRT_POS_LE: "ALL x>=0::real. (0::real) <= sqrt x"
  by (import transc SQRT_POS_LE)

lemma SQRT_POW2: "ALL x::real. (sqrt x ^ 2 = x) = ((0::real) <= x)"
  by (import transc SQRT_POW2)

lemma SQRT_POW_2: "ALL x>=0::real. sqrt x ^ 2 = x"
  by (import transc SQRT_POW_2)

lemma POW_2_SQRT: "(op -->::bool => bool => bool)
 ((op <=::real => real => bool) (0::real) (x::real))
 ((op =::real => real => bool)
   ((sqrt::real => real)
     ((op ^::real => nat => real) x
       ((number_of::bin => nat)
         ((op BIT::bin => bit => bin)
           ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
           (bit.B0::bit)))))
   x)"
  by (import transc POW_2_SQRT)

lemma SQRT_POS_UNIQ: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%xa::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <=::real => real => bool) (0::real) x)
             ((op &::bool => bool => bool)
               ((op <=::real => real => bool) (0::real) xa)
               ((op =::real => real => bool)
                 ((op ^::real => nat => real) xa
                   ((number_of::bin => nat)
                     ((op BIT::bin => bit => bin)
                       ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                         (bit.B1::bit))
                       (bit.B0::bit))))
                 x)))
           ((op =::real => real => bool) ((sqrt::real => real) x) xa)))"
  by (import transc SQRT_POS_UNIQ)

lemma SQRT_MUL: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%xa::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <=::real => real => bool) (0::real) x)
             ((op <=::real => real => bool) (0::real) xa))
           ((op =::real => real => bool)
             ((sqrt::real => real) ((op *::real => real => real) x xa))
             ((op *::real => real => real) ((sqrt::real => real) x)
               ((sqrt::real => real) xa)))))"
  by (import transc SQRT_MUL)

lemma SQRT_INV: "ALL x>=0::real. sqrt (inverse x) = inverse (sqrt x)"
  by (import transc SQRT_INV)

lemma SQRT_DIV: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%xa::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <=::real => real => bool) (0::real) x)
             ((op <=::real => real => bool) (0::real) xa))
           ((op =::real => real => bool)
             ((sqrt::real => real) ((op /::real => real => real) x xa))
             ((op /::real => real => real) ((sqrt::real => real) x)
               ((sqrt::real => real) xa)))))"
  by (import transc SQRT_DIV)

lemma SQRT_MONO_LE: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%xa::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op <=::real => real => bool) (0::real) x)
             ((op <=::real => real => bool) x xa))
           ((op <=::real => real => bool) ((sqrt::real => real) x)
             ((sqrt::real => real) xa))))"
  by (import transc SQRT_MONO_LE)

lemma SQRT_EVEN_POW2: "(All::(nat => bool) => bool)
 (%n::nat.
     (op -->::bool => bool => bool) ((EVEN::nat => bool) n)
      ((op =::real => real => bool)
        ((sqrt::real => real)
          ((op ^::real => nat => real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit)))
            n))
        ((op ^::real => nat => real)
          ((number_of::bin => real)
            ((op BIT::bin => bit => bin)
              ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
              (bit.B0::bit)))
          ((op div::nat => nat => nat) n
            ((number_of::bin => nat)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit)))))))"
  by (import transc SQRT_EVEN_POW2)

lemma REAL_DIV_SQRT: "ALL x>=0::real. x / sqrt x = sqrt x"
  by (import transc REAL_DIV_SQRT)

lemma SQRT_EQ: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%y::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op =::real => real => bool)
               ((op ^::real => nat => real) x
                 ((number_of::bin => nat)
                   ((op BIT::bin => bit => bin)
                     ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                       (bit.B1::bit))
                     (bit.B0::bit))))
               y)
             ((op <=::real => real => bool) (0::real) x))
           ((op =::real => real => bool) x ((sqrt::real => real) y))))"
  by (import transc SQRT_EQ)

lemma SIN_0: "sin (0::real) = (0::real)"
  by (import transc SIN_0)

lemma COS_0: "cos (0::real) = (1::real)"
  by (import transc COS_0)

lemma SIN_CIRCLE: "ALL x::real. sin x ^ 2 + cos x ^ 2 = (1::real)"
  by (import transc SIN_CIRCLE)

lemma SIN_BOUND: "ALL x::real. abs (sin x) <= (1::real)"
  by (import transc SIN_BOUND)

lemma SIN_BOUNDS: "ALL x::real. - (1::real) <= sin x & sin x <= (1::real)"
  by (import transc SIN_BOUNDS)

lemma COS_BOUND: "ALL x::real. abs (cos x) <= (1::real)"
  by (import transc COS_BOUND)

lemma COS_BOUNDS: "ALL x::real. - (1::real) <= cos x & cos x <= (1::real)"
  by (import transc COS_BOUNDS)

lemma SIN_COS_ADD: "ALL (x::real) y::real.
   (sin (x + y) - (sin x * cos y + cos x * sin y)) ^ 2 +
   (cos (x + y) - (cos x * cos y - sin x * sin y)) ^ 2 =
   (0::real)"
  by (import transc SIN_COS_ADD)

lemma SIN_COS_NEG: "ALL x::real. (sin (- x) + sin x) ^ 2 + (cos (- x) - cos x) ^ 2 = (0::real)"
  by (import transc SIN_COS_NEG)

lemma SIN_ADD: "ALL (x::real) y::real. sin (x + y) = sin x * cos y + cos x * sin y"
  by (import transc SIN_ADD)

lemma COS_ADD: "ALL (x::real) y::real. cos (x + y) = cos x * cos y - sin x * sin y"
  by (import transc COS_ADD)

lemma SIN_NEG: "ALL x::real. sin (- x) = - sin x"
  by (import transc SIN_NEG)

lemma COS_NEG: "ALL x::real. cos (- x) = cos x"
  by (import transc COS_NEG)

lemma SIN_DOUBLE: "ALL x::real. sin ((2::real) * x) = (2::real) * (sin x * cos x)"
  by (import transc SIN_DOUBLE)

lemma COS_DOUBLE: "ALL x::real. cos ((2::real) * x) = cos x ^ 2 - sin x ^ 2"
  by (import transc COS_DOUBLE)

lemma SIN_PAIRED: "ALL x::real.
   sums
    (%n::nat.
        (- (1::real)) ^ n / real (FACT ((2::nat) * n + (1::nat))) *
        x ^ ((2::nat) * n + (1::nat)))
    (sin x)"
  by (import transc SIN_PAIRED)

lemma SIN_POS: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) (0::real) x)
        ((op <::real => real => bool) x
          ((number_of::bin => real)
            ((op BIT::bin => bit => bin)
              ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
              (bit.B0::bit)))))
      ((op <::real => real => bool) (0::real) ((sin::real => real) x)))"
  by (import transc SIN_POS)

lemma COS_PAIRED: "ALL x::real.
   sums
    (%n::nat.
        (- (1::real)) ^ n / real (FACT ((2::nat) * n)) * x ^ ((2::nat) * n))
    (cos x)"
  by (import transc COS_PAIRED)

lemma COS_2: "cos (2::real) < (0::real)"
  by (import transc COS_2)

lemma COS_ISZERO: "EX! x::real. (0::real) <= x & x <= (2::real) & cos x = (0::real)"
  by (import transc COS_ISZERO)

constdefs
  pi :: "real" 
  "pi ==
(2::real) *
(SOME x::real. (0::real) <= x & x <= (2::real) & cos x = (0::real))"

lemma pi: "pi =
(2::real) *
(SOME x::real. (0::real) <= x & x <= (2::real) & cos x = (0::real))"
  by (import transc pi)

lemma PI2: "pi / (2::real) =
(SOME x::real. (0::real) <= x & x <= (2::real) & cos x = (0::real))"
  by (import transc PI2)

lemma COS_PI2: "cos (pi / (2::real)) = (0::real)"
  by (import transc COS_PI2)

lemma PI2_BOUNDS: "(0::real) < pi / (2::real) & pi / (2::real) < (2::real)"
  by (import transc PI2_BOUNDS)

lemma PI_POS: "(0::real) < pi"
  by (import transc PI_POS)

lemma SIN_PI2: "sin (pi / (2::real)) = (1::real)"
  by (import transc SIN_PI2)

lemma COS_PI: "cos pi = - (1::real)"
  by (import transc COS_PI)

lemma SIN_PI: "sin pi = (0::real)"
  by (import transc SIN_PI)

lemma SIN_COS: "ALL x::real. sin x = cos (pi / (2::real) - x)"
  by (import transc SIN_COS)

lemma COS_SIN: "ALL x::real. cos x = sin (pi / (2::real) - x)"
  by (import transc COS_SIN)

lemma SIN_PERIODIC_PI: "ALL x::real. sin (x + pi) = - sin x"
  by (import transc SIN_PERIODIC_PI)

lemma COS_PERIODIC_PI: "ALL x::real. cos (x + pi) = - cos x"
  by (import transc COS_PERIODIC_PI)

lemma SIN_PERIODIC: "ALL x::real. sin (x + (2::real) * pi) = sin x"
  by (import transc SIN_PERIODIC)

lemma COS_PERIODIC: "ALL x::real. cos (x + (2::real) * pi) = cos x"
  by (import transc COS_PERIODIC)

lemma COS_NPI: "ALL n::nat. cos (real n * pi) = (- (1::real)) ^ n"
  by (import transc COS_NPI)

lemma SIN_NPI: "ALL n::nat. sin (real n * pi) = (0::real)"
  by (import transc SIN_NPI)

lemma SIN_POS_PI2: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) (0::real) x)
        ((op <::real => real => bool) x
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))))
      ((op <::real => real => bool) (0::real) ((sin::real => real) x)))"
  by (import transc SIN_POS_PI2)

lemma COS_POS_PI2: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) (0::real) x)
        ((op <::real => real => bool) x
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))))
      ((op <::real => real => bool) (0::real) ((cos::real => real) x)))"
  by (import transc COS_POS_PI2)

lemma COS_POS_PI: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool)
          ((uminus::real => real)
            ((op /::real => real => real) (pi::real)
              ((number_of::bin => real)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit)))))
          x)
        ((op <::real => real => bool) x
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))))
      ((op <::real => real => bool) (0::real) ((cos::real => real) x)))"
  by (import transc COS_POS_PI)

lemma SIN_POS_PI: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) (0::real) x)
        ((op <::real => real => bool) x (pi::real)))
      ((op <::real => real => bool) (0::real) ((sin::real => real) x)))"
  by (import transc SIN_POS_PI)

lemma COS_POS_PI2_LE: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) (0::real) x)
        ((op <=::real => real => bool) x
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))))
      ((op <=::real => real => bool) (0::real) ((cos::real => real) x)))"
  by (import transc COS_POS_PI2_LE)

lemma COS_POS_PI_LE: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool)
          ((uminus::real => real)
            ((op /::real => real => real) (pi::real)
              ((number_of::bin => real)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit)))))
          x)
        ((op <=::real => real => bool) x
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))))
      ((op <=::real => real => bool) (0::real) ((cos::real => real) x)))"
  by (import transc COS_POS_PI_LE)

lemma SIN_POS_PI2_LE: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) (0::real) x)
        ((op <=::real => real => bool) x
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))))
      ((op <=::real => real => bool) (0::real) ((sin::real => real) x)))"
  by (import transc SIN_POS_PI2_LE)

lemma SIN_POS_PI_LE: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) (0::real) x)
        ((op <=::real => real => bool) x (pi::real)))
      ((op <=::real => real => bool) (0::real) ((sin::real => real) x)))"
  by (import transc SIN_POS_PI_LE)

lemma COS_TOTAL: "(All::(real => bool) => bool)
 (%y::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) ((uminus::real => real) (1::real)) y)
        ((op <=::real => real => bool) y (1::real)))
      ((Ex1::(real => bool) => bool)
        (%x::real.
            (op &::bool => bool => bool)
             ((op <=::real => real => bool) (0::real) x)
             ((op &::bool => bool => bool)
               ((op <=::real => real => bool) x (pi::real))
               ((op =::real => real => bool) ((cos::real => real) x) y)))))"
  by (import transc COS_TOTAL)

lemma SIN_TOTAL: "(All::(real => bool) => bool)
 (%y::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) ((uminus::real => real) (1::real)) y)
        ((op <=::real => real => bool) y (1::real)))
      ((Ex1::(real => bool) => bool)
        (%x::real.
            (op &::bool => bool => bool)
             ((op <=::real => real => bool)
               ((uminus::real => real)
                 ((op /::real => real => real) (pi::real)
                   ((number_of::bin => real)
                     ((op BIT::bin => bit => bin)
                       ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                         (bit.B1::bit))
                       (bit.B0::bit)))))
               x)
             ((op &::bool => bool => bool)
               ((op <=::real => real => bool) x
                 ((op /::real => real => real) (pi::real)
                   ((number_of::bin => real)
                     ((op BIT::bin => bit => bin)
                       ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                         (bit.B1::bit))
                       (bit.B0::bit)))))
               ((op =::real => real => bool) ((sin::real => real) x) y)))))"
  by (import transc SIN_TOTAL)

lemma COS_ZERO_LEMMA: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) (0::real) x)
        ((op =::real => real => bool) ((cos::real => real) x) (0::real)))
      ((Ex::(nat => bool) => bool)
        (%n::nat.
            (op &::bool => bool => bool)
             ((Not::bool => bool) ((EVEN::nat => bool) n))
             ((op =::real => real => bool) x
               ((op *::real => real => real) ((real::nat => real) n)
                 ((op /::real => real => real) (pi::real)
                   ((number_of::bin => real)
                     ((op BIT::bin => bit => bin)
                       ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                         (bit.B1::bit))
                       (bit.B0::bit)))))))))"
  by (import transc COS_ZERO_LEMMA)

lemma SIN_ZERO_LEMMA: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) (0::real) x)
        ((op =::real => real => bool) ((sin::real => real) x) (0::real)))
      ((Ex::(nat => bool) => bool)
        (%n::nat.
            (op &::bool => bool => bool) ((EVEN::nat => bool) n)
             ((op =::real => real => bool) x
               ((op *::real => real => real) ((real::nat => real) n)
                 ((op /::real => real => real) (pi::real)
                   ((number_of::bin => real)
                     ((op BIT::bin => bit => bin)
                       ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                         (bit.B1::bit))
                       (bit.B0::bit)))))))))"
  by (import transc SIN_ZERO_LEMMA)

lemma COS_ZERO: "ALL x::real.
   (cos x = (0::real)) =
   ((EX n::nat. ~ EVEN n & x = real n * (pi / (2::real))) |
    (EX n::nat. ~ EVEN n & x = - (real n * (pi / (2::real)))))"
  by (import transc COS_ZERO)

lemma SIN_ZERO: "ALL x::real.
   (sin x = (0::real)) =
   ((EX n::nat. EVEN n & x = real n * (pi / (2::real))) |
    (EX n::nat. EVEN n & x = - (real n * (pi / (2::real)))))"
  by (import transc SIN_ZERO)

constdefs
  tan :: "real => real" 
  "tan == %x::real. sin x / cos x"

lemma tan: "ALL x::real. tan x = sin x / cos x"
  by (import transc tan)

lemma TAN_0: "tan (0::real) = (0::real)"
  by (import transc TAN_0)

lemma TAN_PI: "tan pi = (0::real)"
  by (import transc TAN_PI)

lemma TAN_NPI: "ALL n::nat. tan (real n * pi) = (0::real)"
  by (import transc TAN_NPI)

lemma TAN_NEG: "ALL x::real. tan (- x) = - tan x"
  by (import transc TAN_NEG)

lemma TAN_PERIODIC: "ALL x::real. tan (x + (2::real) * pi) = tan x"
  by (import transc TAN_PERIODIC)

lemma TAN_ADD: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%y::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((Not::bool => bool)
               ((op =::real => real => bool) ((cos::real => real) x)
                 (0::real)))
             ((op &::bool => bool => bool)
               ((Not::bool => bool)
                 ((op =::real => real => bool) ((cos::real => real) y)
                   (0::real)))
               ((Not::bool => bool)
                 ((op =::real => real => bool)
                   ((cos::real => real) ((op +::real => real => real) x y))
                   (0::real)))))
           ((op =::real => real => bool)
             ((tan::real => real) ((op +::real => real => real) x y))
             ((op /::real => real => real)
               ((op +::real => real => real) ((tan::real => real) x)
                 ((tan::real => real) y))
               ((op -::real => real => real) (1::real)
                 ((op *::real => real => real) ((tan::real => real) x)
                   ((tan::real => real) y)))))))"
  by (import transc TAN_ADD)

lemma TAN_DOUBLE: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((Not::bool => bool)
          ((op =::real => real => bool) ((cos::real => real) x) (0::real)))
        ((Not::bool => bool)
          ((op =::real => real => bool)
            ((cos::real => real)
              ((op *::real => real => real)
                ((number_of::bin => real)
                  ((op BIT::bin => bit => bin)
                    ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                      (bit.B1::bit))
                    (bit.B0::bit)))
                x))
            (0::real))))
      ((op =::real => real => bool)
        ((tan::real => real)
          ((op *::real => real => real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit)))
            x))
        ((op /::real => real => real)
          ((op *::real => real => real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit)))
            ((tan::real => real) x))
          ((op -::real => real => real) (1::real)
            ((op ^::real => nat => real) ((tan::real => real) x)
              ((number_of::bin => nat)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit))))))))"
  by (import transc TAN_DOUBLE)

lemma TAN_POS_PI2: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) (0::real) x)
        ((op <::real => real => bool) x
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))))
      ((op <::real => real => bool) (0::real) ((tan::real => real) x)))"
  by (import transc TAN_POS_PI2)

lemma DIFF_TAN: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((Not::bool => bool)
        ((op =::real => real => bool) ((cos::real => real) x) (0::real)))
      ((diffl::(real => real) => real => real => bool) (tan::real => real)
        ((inverse::real => real)
          ((op ^::real => nat => real) ((cos::real => real) x)
            ((number_of::bin => nat)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit)))))
        x))"
  by (import transc DIFF_TAN)

lemma TAN_TOTAL_LEMMA: "ALL y>0::real. EX x>0::real. x < pi / (2::real) & y < tan x"
  by (import transc TAN_TOTAL_LEMMA)

lemma TAN_TOTAL_POS: "ALL y>=0::real. EX x>=0::real. x < pi / (2::real) & tan x = y"
  by (import transc TAN_TOTAL_POS)

lemma TAN_TOTAL: "ALL y::real.
   EX! x::real. - (pi / (2::real)) < x & x < pi / (2::real) & tan x = y"
  by (import transc TAN_TOTAL)

constdefs
  asn :: "real => real" 
  "asn ==
%y::real.
   SOME x::real. - (pi / (2::real)) <= x & x <= pi / (2::real) & sin x = y"

lemma asn: "ALL y::real.
   asn y =
   (SOME x::real. - (pi / (2::real)) <= x & x <= pi / (2::real) & sin x = y)"
  by (import transc asn)

constdefs
  acs :: "real => real" 
  "acs == %y::real. SOME x::real. (0::real) <= x & x <= pi & cos x = y"

lemma acs: "ALL y::real. acs y = (SOME x::real. (0::real) <= x & x <= pi & cos x = y)"
  by (import transc acs)

constdefs
  atn :: "real => real" 
  "atn ==
%y::real.
   SOME x::real. - (pi / (2::real)) < x & x < pi / (2::real) & tan x = y"

lemma atn: "ALL y::real.
   atn y =
   (SOME x::real. - (pi / (2::real)) < x & x < pi / (2::real) & tan x = y)"
  by (import transc atn)

lemma ASN: "(All::(real => bool) => bool)
 (%y::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) ((uminus::real => real) (1::real)) y)
        ((op <=::real => real => bool) y (1::real)))
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool)
          ((uminus::real => real)
            ((op /::real => real => real) (pi::real)
              ((number_of::bin => real)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit)))))
          ((asn::real => real) y))
        ((op &::bool => bool => bool)
          ((op <=::real => real => bool) ((asn::real => real) y)
            ((op /::real => real => real) (pi::real)
              ((number_of::bin => real)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit)))))
          ((op =::real => real => bool)
            ((sin::real => real) ((asn::real => real) y)) y))))"
  by (import transc ASN)

lemma ASN_SIN: "(All::(real => bool) => bool)
 (%y::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) ((uminus::real => real) (1::real)) y)
        ((op <=::real => real => bool) y (1::real)))
      ((op =::real => real => bool)
        ((sin::real => real) ((asn::real => real) y)) y))"
  by (import transc ASN_SIN)

lemma ASN_BOUNDS: "(All::(real => bool) => bool)
 (%y::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) ((uminus::real => real) (1::real)) y)
        ((op <=::real => real => bool) y (1::real)))
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool)
          ((uminus::real => real)
            ((op /::real => real => real) (pi::real)
              ((number_of::bin => real)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit)))))
          ((asn::real => real) y))
        ((op <=::real => real => bool) ((asn::real => real) y)
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit)))))))"
  by (import transc ASN_BOUNDS)

lemma ASN_BOUNDS_LT: "(All::(real => bool) => bool)
 (%y::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) ((uminus::real => real) (1::real)) y)
        ((op <::real => real => bool) y (1::real)))
      ((op &::bool => bool => bool)
        ((op <::real => real => bool)
          ((uminus::real => real)
            ((op /::real => real => real) (pi::real)
              ((number_of::bin => real)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit)))))
          ((asn::real => real) y))
        ((op <::real => real => bool) ((asn::real => real) y)
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit)))))))"
  by (import transc ASN_BOUNDS_LT)

lemma SIN_ASN: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool)
          ((uminus::real => real)
            ((op /::real => real => real) (pi::real)
              ((number_of::bin => real)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit)))))
          x)
        ((op <=::real => real => bool) x
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))))
      ((op =::real => real => bool)
        ((asn::real => real) ((sin::real => real) x)) x))"
  by (import transc SIN_ASN)

lemma ACS: "(All::(real => bool) => bool)
 (%y::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) ((uminus::real => real) (1::real)) y)
        ((op <=::real => real => bool) y (1::real)))
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) (0::real) ((acs::real => real) y))
        ((op &::bool => bool => bool)
          ((op <=::real => real => bool) ((acs::real => real) y) (pi::real))
          ((op =::real => real => bool)
            ((cos::real => real) ((acs::real => real) y)) y))))"
  by (import transc ACS)

lemma ACS_COS: "(All::(real => bool) => bool)
 (%y::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) ((uminus::real => real) (1::real)) y)
        ((op <=::real => real => bool) y (1::real)))
      ((op =::real => real => bool)
        ((cos::real => real) ((acs::real => real) y)) y))"
  by (import transc ACS_COS)

lemma ACS_BOUNDS: "(All::(real => bool) => bool)
 (%y::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) ((uminus::real => real) (1::real)) y)
        ((op <=::real => real => bool) y (1::real)))
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) (0::real) ((acs::real => real) y))
        ((op <=::real => real => bool) ((acs::real => real) y) (pi::real))))"
  by (import transc ACS_BOUNDS)

lemma ACS_BOUNDS_LT: "(All::(real => bool) => bool)
 (%y::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) ((uminus::real => real) (1::real)) y)
        ((op <::real => real => bool) y (1::real)))
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) (0::real) ((acs::real => real) y))
        ((op <::real => real => bool) ((acs::real => real) y) (pi::real))))"
  by (import transc ACS_BOUNDS_LT)

lemma COS_ACS: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) (0::real) x)
        ((op <=::real => real => bool) x (pi::real)))
      ((op =::real => real => bool)
        ((acs::real => real) ((cos::real => real) x)) x))"
  by (import transc COS_ACS)

lemma ATN: "ALL y::real.
   - (pi / (2::real)) < atn y & atn y < pi / (2::real) & tan (atn y) = y"
  by (import transc ATN)

lemma ATN_TAN: "ALL x::real. tan (atn x) = x"
  by (import transc ATN_TAN)

lemma ATN_BOUNDS: "ALL x::real. - (pi / (2::real)) < atn x & atn x < pi / (2::real)"
  by (import transc ATN_BOUNDS)

lemma TAN_ATN: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool)
          ((uminus::real => real)
            ((op /::real => real => real) (pi::real)
              ((number_of::bin => real)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit)))))
          x)
        ((op <::real => real => bool) x
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))))
      ((op =::real => real => bool)
        ((atn::real => real) ((tan::real => real) x)) x))"
  by (import transc TAN_ATN)

lemma TAN_SEC: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((Not::bool => bool)
        ((op =::real => real => bool) ((cos::real => real) x) (0::real)))
      ((op =::real => real => bool)
        ((op +::real => real => real) (1::real)
          ((op ^::real => nat => real) ((tan::real => real) x)
            ((number_of::bin => nat)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit)))))
        ((op ^::real => nat => real)
          ((inverse::real => real) ((cos::real => real) x))
          ((number_of::bin => nat)
            ((op BIT::bin => bit => bin)
              ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
              (bit.B0::bit))))))"
  by (import transc TAN_SEC)

lemma SIN_COS_SQ: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool) (0::real) x)
        ((op <=::real => real => bool) x (pi::real)))
      ((op =::real => real => bool) ((sin::real => real) x)
        ((sqrt::real => real)
          ((op -::real => real => real) (1::real)
            ((op ^::real => nat => real) ((cos::real => real) x)
              ((number_of::bin => nat)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit))))))))"
  by (import transc SIN_COS_SQ)

lemma COS_SIN_SQ: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <=::real => real => bool)
          ((uminus::real => real)
            ((op /::real => real => real) (pi::real)
              ((number_of::bin => real)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit)))))
          x)
        ((op <=::real => real => bool) x
          ((op /::real => real => real) (pi::real)
            ((number_of::bin => real)
              ((op BIT::bin => bit => bin)
                ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                  (bit.B1::bit))
                (bit.B0::bit))))))
      ((op =::real => real => bool) ((cos::real => real) x)
        ((sqrt::real => real)
          ((op -::real => real => real) (1::real)
            ((op ^::real => nat => real) ((sin::real => real) x)
              ((number_of::bin => nat)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit))))))))"
  by (import transc COS_SIN_SQ)

lemma COS_ATN_NZ: "ALL x::real. cos (atn x) ~= (0::real)"
  by (import transc COS_ATN_NZ)

lemma COS_ASN_NZ: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) ((uminus::real => real) (1::real)) x)
        ((op <::real => real => bool) x (1::real)))
      ((Not::bool => bool)
        ((op =::real => real => bool)
          ((cos::real => real) ((asn::real => real) x)) (0::real))))"
  by (import transc COS_ASN_NZ)

lemma SIN_ACS_NZ: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) ((uminus::real => real) (1::real)) x)
        ((op <::real => real => bool) x (1::real)))
      ((Not::bool => bool)
        ((op =::real => real => bool)
          ((sin::real => real) ((acs::real => real) x)) (0::real))))"
  by (import transc SIN_ACS_NZ)

lemma COS_SIN_SQRT: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op <=::real => real => bool) (0::real) ((cos::real => real) x))
      ((op =::real => real => bool) ((cos::real => real) x)
        ((sqrt::real => real)
          ((op -::real => real => real) (1::real)
            ((op ^::real => nat => real) ((sin::real => real) x)
              ((number_of::bin => nat)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit))))))))"
  by (import transc COS_SIN_SQRT)

lemma SIN_COS_SQRT: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op <=::real => real => bool) (0::real) ((sin::real => real) x))
      ((op =::real => real => bool) ((sin::real => real) x)
        ((sqrt::real => real)
          ((op -::real => real => real) (1::real)
            ((op ^::real => nat => real) ((cos::real => real) x)
              ((number_of::bin => nat)
                ((op BIT::bin => bit => bin)
                  ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                    (bit.B1::bit))
                  (bit.B0::bit))))))))"
  by (import transc SIN_COS_SQRT)

lemma DIFF_LN: "ALL x>0::real. diffl ln (inverse x) x"
  by (import transc DIFF_LN)

lemma DIFF_ASN_LEMMA: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) ((uminus::real => real) (1::real)) x)
        ((op <::real => real => bool) x (1::real)))
      ((diffl::(real => real) => real => real => bool) (asn::real => real)
        ((inverse::real => real)
          ((cos::real => real) ((asn::real => real) x)))
        x))"
  by (import transc DIFF_ASN_LEMMA)

lemma DIFF_ASN: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) ((uminus::real => real) (1::real)) x)
        ((op <::real => real => bool) x (1::real)))
      ((diffl::(real => real) => real => real => bool) (asn::real => real)
        ((inverse::real => real)
          ((sqrt::real => real)
            ((op -::real => real => real) (1::real)
              ((op ^::real => nat => real) x
                ((number_of::bin => nat)
                  ((op BIT::bin => bit => bin)
                    ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                      (bit.B1::bit))
                    (bit.B0::bit)))))))
        x))"
  by (import transc DIFF_ASN)

lemma DIFF_ACS_LEMMA: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) ((uminus::real => real) (1::real)) x)
        ((op <::real => real => bool) x (1::real)))
      ((diffl::(real => real) => real => real => bool) (acs::real => real)
        ((inverse::real => real)
          ((uminus::real => real)
            ((sin::real => real) ((acs::real => real) x))))
        x))"
  by (import transc DIFF_ACS_LEMMA)

lemma DIFF_ACS: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((op <::real => real => bool) ((uminus::real => real) (1::real)) x)
        ((op <::real => real => bool) x (1::real)))
      ((diffl::(real => real) => real => real => bool) (acs::real => real)
        ((uminus::real => real)
          ((inverse::real => real)
            ((sqrt::real => real)
              ((op -::real => real => real) (1::real)
                ((op ^::real => nat => real) x
                  ((number_of::bin => nat)
                    ((op BIT::bin => bit => bin)
                      ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                        (bit.B1::bit))
                      (bit.B0::bit))))))))
        x))"
  by (import transc DIFF_ACS)

lemma DIFF_ATN: "ALL x::real. diffl atn (inverse ((1::real) + x ^ 2)) x"
  by (import transc DIFF_ATN)

constdefs
  division :: "real * real => (nat => real) => bool" 
  "(op ==::(real * real => (nat => real) => bool)
        => (real * real => (nat => real) => bool) => prop)
 (division::real * real => (nat => real) => bool)
 ((split::(real => real => (nat => real) => bool)
          => real * real => (nat => real) => bool)
   (%(a::real) (b::real) D::nat => real.
       (op &::bool => bool => bool)
        ((op =::real => real => bool) (D (0::nat)) a)
        ((Ex::(nat => bool) => bool)
          (%N::nat.
              (op &::bool => bool => bool)
               ((All::(nat => bool) => bool)
                 (%n::nat.
                     (op -->::bool => bool => bool)
                      ((op <::nat => nat => bool) n N)
                      ((op <::real => real => bool) (D n)
                        (D ((Suc::nat => nat) n)))))
               ((All::(nat => bool) => bool)
                 (%n::nat.
                     (op -->::bool => bool => bool)
                      ((op <=::nat => nat => bool) N n)
                      ((op =::real => real => bool) (D n) b)))))))"

lemma division: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real => bool) => bool)
      (%b::real.
          (All::((nat => real) => bool) => bool)
           (%D::nat => real.
               (op =::bool => bool => bool)
                ((division::real * real => (nat => real) => bool)
                  ((Pair::real => real => real * real) a b) D)
                ((op &::bool => bool => bool)
                  ((op =::real => real => bool) (D (0::nat)) a)
                  ((Ex::(nat => bool) => bool)
                    (%N::nat.
                        (op &::bool => bool => bool)
                         ((All::(nat => bool) => bool)
                           (%n::nat.
                               (op -->::bool => bool => bool)
                                ((op <::nat => nat => bool) n N)
                                ((op <::real => real => bool) (D n)
                                  (D ((Suc::nat => nat) n)))))
                         ((All::(nat => bool) => bool)
                           (%n::nat.
                               (op -->::bool => bool => bool)
                                ((op <=::nat => nat => bool) N n)
                                ((op =::real => real => bool) (D n)
                                  b)))))))))"
  by (import transc division)

constdefs
  dsize :: "(nat => real) => nat" 
  "(op ==::((nat => real) => nat) => ((nat => real) => nat) => prop)
 (dsize::(nat => real) => nat)
 (%D::nat => real.
     (Eps::(nat => bool) => nat)
      (%N::nat.
          (op &::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%n::nat.
                 (op -->::bool => bool => bool)
                  ((op <::nat => nat => bool) n N)
                  ((op <::real => real => bool) (D n)
                    (D ((Suc::nat => nat) n)))))
           ((All::(nat => bool) => bool)
             (%n::nat.
                 (op -->::bool => bool => bool)
                  ((op <=::nat => nat => bool) N n)
                  ((op =::real => real => bool) (D n) (D N))))))"

lemma dsize: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (op =::nat => nat => bool) ((dsize::(nat => real) => nat) D)
      ((Eps::(nat => bool) => nat)
        (%N::nat.
            (op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%n::nat.
                   (op -->::bool => bool => bool)
                    ((op <::nat => nat => bool) n N)
                    ((op <::real => real => bool) (D n)
                      (D ((Suc::nat => nat) n)))))
             ((All::(nat => bool) => bool)
               (%n::nat.
                   (op -->::bool => bool => bool)
                    ((op <=::nat => nat => bool) N n)
                    ((op =::real => real => bool) (D n) (D N)))))))"
  by (import transc dsize)

constdefs
  tdiv :: "real * real => (nat => real) * (nat => real) => bool" 
  "tdiv ==
%(a::real, b::real) (D::nat => real, p::nat => real).
   division (a, b) D & (ALL n::nat. D n <= p n & p n <= D (Suc n))"

lemma tdiv: "ALL (a::real) (b::real) (D::nat => real) p::nat => real.
   tdiv (a, b) (D, p) =
   (division (a, b) D & (ALL n::nat. D n <= p n & p n <= D (Suc n)))"
  by (import transc tdiv)

constdefs
  gauge :: "(real => bool) => (real => real) => bool" 
  "(op ==::((real => bool) => (real => real) => bool)
        => ((real => bool) => (real => real) => bool) => prop)
 (gauge::(real => bool) => (real => real) => bool)
 (%(E::real => bool) g::real => real.
     (All::(real => bool) => bool)
      (%x::real.
          (op -->::bool => bool => bool) (E x)
           ((op <::real => real => bool) (0::real) (g x))))"

lemma gauge: "(All::((real => bool) => bool) => bool)
 (%E::real => bool.
     (All::((real => real) => bool) => bool)
      (%g::real => real.
          (op =::bool => bool => bool)
           ((gauge::(real => bool) => (real => real) => bool) E g)
           ((All::(real => bool) => bool)
             (%x::real.
                 (op -->::bool => bool => bool) (E x)
                  ((op <::real => real => bool) (0::real) (g x))))))"
  by (import transc gauge)

constdefs
  fine :: "(real => real) => (nat => real) * (nat => real) => bool" 
  "(op ==::((real => real) => (nat => real) * (nat => real) => bool)
        => ((real => real) => (nat => real) * (nat => real) => bool)
           => prop)
 (fine::(real => real) => (nat => real) * (nat => real) => bool)
 (%g::real => real.
     (split::((nat => real) => (nat => real) => bool)
             => (nat => real) * (nat => real) => bool)
      (%(D::nat => real) p::nat => real.
          (All::(nat => bool) => bool)
           (%n::nat.
               (op -->::bool => bool => bool)
                ((op <::nat => nat => bool) n
                  ((dsize::(nat => real) => nat) D))
                ((op <::real => real => bool)
                  ((op -::real => real => real) (D ((Suc::nat => nat) n))
                    (D n))
                  (g (p n))))))"

lemma fine: "(All::((real => real) => bool) => bool)
 (%g::real => real.
     (All::((nat => real) => bool) => bool)
      (%D::nat => real.
          (All::((nat => real) => bool) => bool)
           (%p::nat => real.
               (op =::bool => bool => bool)
                ((fine::(real => real)
                        => (nat => real) * (nat => real) => bool)
                  g ((Pair::(nat => real)
                            => (nat => real)
                               => (nat => real) * (nat => real))
                      D p))
                ((All::(nat => bool) => bool)
                  (%n::nat.
                      (op -->::bool => bool => bool)
                       ((op <::nat => nat => bool) n
                         ((dsize::(nat => real) => nat) D))
                       ((op <::real => real => bool)
                         ((op -::real => real => real)
                           (D ((Suc::nat => nat) n)) (D n))
                         (g (p n))))))))"
  by (import transc fine)

constdefs
  rsum :: "(nat => real) * (nat => real) => (real => real) => real" 
  "rsum ==
%(D::nat => real, p::nat => real) f::real => real.
   real.sum (0::nat, dsize D) (%n::nat. f (p n) * (D (Suc n) - D n))"

lemma rsum: "ALL (D::nat => real) (p::nat => real) f::real => real.
   rsum (D, p) f =
   real.sum (0::nat, dsize D) (%n::nat. f (p n) * (D (Suc n) - D n))"
  by (import transc rsum)

constdefs
  Dint :: "real * real => (real => real) => real => bool" 
  "(op ==::(real * real => (real => real) => real => bool)
        => (real * real => (real => real) => real => bool) => prop)
 (Dint::real * real => (real => real) => real => bool)
 ((split::(real => real => (real => real) => real => bool)
          => real * real => (real => real) => real => bool)
   (%(a::real) (b::real) (f::real => real) k::real.
       (All::(real => bool) => bool)
        (%e::real.
            (op -->::bool => bool => bool)
             ((op <::real => real => bool) (0::real) e)
             ((Ex::((real => real) => bool) => bool)
               (%g::real => real.
                   (op &::bool => bool => bool)
                    ((gauge::(real => bool) => (real => real) => bool)
                      (%x::real.
                          (op &::bool => bool => bool)
                           ((op <=::real => real => bool) a x)
                           ((op <=::real => real => bool) x b))
                      g)
                    ((All::((nat => real) => bool) => bool)
                      (%D::nat => real.
                          (All::((nat => real) => bool) => bool)
                           (%p::nat => real.
                               (op -->::bool => bool => bool)
                                ((op &::bool => bool => bool)
                                  ((tdiv::real * real
    => (nat => real) * (nat => real) => bool)
                                    ((Pair::real => real => real * real) a
b)
                                    ((Pair::(nat => real)
      => (nat => real) => (nat => real) * (nat => real))
D p))
                                  ((fine::(real => real)
    => (nat => real) * (nat => real) => bool)
                                    g ((Pair::(nat => real)
        => (nat => real) => (nat => real) * (nat => real))
  D p)))
                                ((op <::real => real => bool)
                                  ((abs::real => real)
                                    ((op -::real => real => real)
((rsum::(nat => real) * (nat => real) => (real => real) => real)
  ((Pair::(nat => real) => (nat => real) => (nat => real) * (nat => real)) D
    p)
  f)
k))
                                  e)))))))))"

lemma Dint: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real => bool) => bool)
      (%b::real.
          (All::((real => real) => bool) => bool)
           (%f::real => real.
               (All::(real => bool) => bool)
                (%k::real.
                    (op =::bool => bool => bool)
                     ((Dint::real * real => (real => real) => real => bool)
                       ((Pair::real => real => real * real) a b) f k)
                     ((All::(real => bool) => bool)
                       (%e::real.
                           (op -->::bool => bool => bool)
                            ((op <::real => real => bool) (0::real) e)
                            ((Ex::((real => real) => bool) => bool)
                              (%g::real => real.
                                  (op &::bool => bool => bool)
                                   ((gauge::(real => bool)
      => (real => real) => bool)
                                     (%x::real.
   (op &::bool => bool => bool) ((op <=::real => real => bool) a x)
    ((op <=::real => real => bool) x b))
                                     g)
                                   ((All::((nat => real) => bool) => bool)
                                     (%D::nat => real.
   (All::((nat => real) => bool) => bool)
    (%p::nat => real.
        (op -->::bool => bool => bool)
         ((op &::bool => bool => bool)
           ((tdiv::real * real => (nat => real) * (nat => real) => bool)
             ((Pair::real => real => real * real) a b)
             ((Pair::(nat => real)
                     => (nat => real) => (nat => real) * (nat => real))
               D p))
           ((fine::(real => real) => (nat => real) * (nat => real) => bool)
             g ((Pair::(nat => real)
                       => (nat => real) => (nat => real) * (nat => real))
                 D p)))
         ((op <::real => real => bool)
           ((abs::real => real)
             ((op -::real => real => real)
               ((rsum::(nat => real) * (nat => real)
                       => (real => real) => real)
                 ((Pair::(nat => real)
                         => (nat => real) => (nat => real) * (nat => real))
                   D p)
                 f)
               k))
           e))))))))))))"
  by (import transc Dint)

lemma DIVISION_0: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real => bool) => bool)
      (%b::real.
          (op -->::bool => bool => bool) ((op =::real => real => bool) a b)
           ((op =::nat => nat => bool)
             ((dsize::(nat => real) => nat)
               (%n::nat.
                   (If::bool => real => real => real)
                    ((op =::nat => nat => bool) n (0::nat)) a b))
             (0::nat))))"
  by (import transc DIVISION_0)

lemma DIVISION_1: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real => bool) => bool)
      (%b::real.
          (op -->::bool => bool => bool) ((op <::real => real => bool) a b)
           ((op =::nat => nat => bool)
             ((dsize::(nat => real) => nat)
               (%n::nat.
                   (If::bool => real => real => real)
                    ((op =::nat => nat => bool) n (0::nat)) a b))
             (1::nat))))"
  by (import transc DIVISION_1)

lemma DIVISION_SINGLE: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real => bool) => bool)
      (%b::real.
          (op -->::bool => bool => bool) ((op <=::real => real => bool) a b)
           ((division::real * real => (nat => real) => bool)
             ((Pair::real => real => real * real) a b)
             (%n::nat.
                 (If::bool => real => real => real)
                  ((op =::nat => nat => bool) n (0::nat)) a b))))"
  by (import transc DIVISION_SINGLE)

lemma DIVISION_LHS: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((division::real * real => (nat => real) => bool)
                  ((Pair::real => real => real * real) a b) D)
                ((op =::real => real => bool) (D (0::nat)) a))))"
  by (import transc DIVISION_LHS)

lemma DIVISION_THM: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op =::bool => bool => bool)
                ((division::real * real => (nat => real) => bool)
                  ((Pair::real => real => real * real) a b) D)
                ((op &::bool => bool => bool)
                  ((op =::real => real => bool) (D (0::nat)) a)
                  ((op &::bool => bool => bool)
                    ((All::(nat => bool) => bool)
                      (%n::nat.
                          (op -->::bool => bool => bool)
                           ((op <::nat => nat => bool) n
                             ((dsize::(nat => real) => nat) D))
                           ((op <::real => real => bool) (D n)
                             (D ((Suc::nat => nat) n)))))
                    ((All::(nat => bool) => bool)
                      (%n::nat.
                          (op -->::bool => bool => bool)
                           ((op <=::nat => nat => bool)
                             ((dsize::(nat => real) => nat) D) n)
                           ((op =::real => real => bool) (D n) b))))))))"
  by (import transc DIVISION_THM)

lemma DIVISION_RHS: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((division::real * real => (nat => real) => bool)
                  ((Pair::real => real => real * real) a b) D)
                ((op =::real => real => bool)
                  (D ((dsize::(nat => real) => nat) D)) b))))"
  by (import transc DIVISION_RHS)

lemma DIVISION_LT_GEN: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (All::(nat => bool) => bool)
                (%m::nat.
                    (All::(nat => bool) => bool)
                     (%n::nat.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((division::real * real
  => (nat => real) => bool)
                              ((Pair::real => real => real * real) a b) D)
                            ((op &::bool => bool => bool)
                              ((op <::nat => nat => bool) m n)
                              ((op <=::nat => nat => bool) n
                                ((dsize::(nat => real) => nat) D))))
                          ((op <::real => real => bool) (D m) (D n)))))))"
  by (import transc DIVISION_LT_GEN)

lemma DIVISION_LT: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((division::real * real => (nat => real) => bool)
                  ((Pair::real => real => real * real) a b) D)
                ((All::(nat => bool) => bool)
                  (%n::nat.
                      (op -->::bool => bool => bool)
                       ((op <::nat => nat => bool) n
                         ((dsize::(nat => real) => nat) D))
                       ((op <::real => real => bool) (D (0::nat))
                         (D ((Suc::nat => nat) n))))))))"
  by (import transc DIVISION_LT)

lemma DIVISION_LE: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((division::real * real => (nat => real) => bool)
                  ((Pair::real => real => real * real) a b) D)
                ((op <=::real => real => bool) a b))))"
  by (import transc DIVISION_LE)

lemma DIVISION_GT: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((division::real * real => (nat => real) => bool)
                  ((Pair::real => real => real * real) a b) D)
                ((All::(nat => bool) => bool)
                  (%n::nat.
                      (op -->::bool => bool => bool)
                       ((op <::nat => nat => bool) n
                         ((dsize::(nat => real) => nat) D))
                       ((op <::real => real => bool) (D n)
                         (D ((dsize::(nat => real) => nat) D))))))))"
  by (import transc DIVISION_GT)

lemma DIVISION_EQ: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((division::real * real => (nat => real) => bool)
                  ((Pair::real => real => real * real) a b) D)
                ((op =::bool => bool => bool)
                  ((op =::real => real => bool) a b)
                  ((op =::nat => nat => bool)
                    ((dsize::(nat => real) => nat) D) (0::nat))))))"
  by (import transc DIVISION_EQ)

lemma DIVISION_LBOUND: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((division::real * real => (nat => real) => bool)
                  ((Pair::real => real => real * real) a b) D)
                ((All::(nat => bool) => bool)
                  (%r::nat. (op <=::real => real => bool) a (D r))))))"
  by (import transc DIVISION_LBOUND)

lemma DIVISION_LBOUND_LT: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((division::real * real => (nat => real) => bool)
                    ((Pair::real => real => real * real) a b) D)
                  ((Not::bool => bool)
                    ((op =::nat => nat => bool)
                      ((dsize::(nat => real) => nat) D) (0::nat))))
                ((All::(nat => bool) => bool)
                  (%n::nat.
                      (op <::real => real => bool) a
                       (D ((Suc::nat => nat) n)))))))"
  by (import transc DIVISION_LBOUND_LT)

lemma DIVISION_UBOUND: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((division::real * real => (nat => real) => bool)
                  ((Pair::real => real => real * real) a b) D)
                ((All::(nat => bool) => bool)
                  (%r::nat. (op <=::real => real => bool) (D r) b)))))"
  by (import transc DIVISION_UBOUND)

lemma DIVISION_UBOUND_LT: "(All::((nat => real) => bool) => bool)
 (%D::nat => real.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (All::(nat => bool) => bool)
                (%n::nat.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((division::real * real => (nat => real) => bool)
                         ((Pair::real => real => real * real) a b) D)
                       ((op <::nat => nat => bool) n
                         ((dsize::(nat => real) => nat) D)))
                     ((op <::real => real => bool) (D n) b)))))"
  by (import transc DIVISION_UBOUND_LT)

lemma DIVISION_APPEND: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real => bool) => bool)
      (%b::real.
          (All::(real => bool) => bool)
           (%c::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((Ex::((nat => real) => bool) => bool)
                    (%D1::nat => real.
                        (Ex::((nat => real) => bool) => bool)
                         (%p1::nat => real.
                             (op &::bool => bool => bool)
                              ((tdiv::real * real
=> (nat => real) * (nat => real) => bool)
                                ((Pair::real => real => real * real) a b)
                                ((Pair::(nat => real)
  => (nat => real) => (nat => real) * (nat => real))
                                  D1 p1))
                              ((fine::(real => real)
=> (nat => real) * (nat => real) => bool)
                                (g::real => real)
                                ((Pair::(nat => real)
  => (nat => real) => (nat => real) * (nat => real))
                                  D1 p1)))))
                  ((Ex::((nat => real) => bool) => bool)
                    (%D2::nat => real.
                        (Ex::((nat => real) => bool) => bool)
                         (%p2::nat => real.
                             (op &::bool => bool => bool)
                              ((tdiv::real * real
=> (nat => real) * (nat => real) => bool)
                                ((Pair::real => real => real * real) b c)
                                ((Pair::(nat => real)
  => (nat => real) => (nat => real) * (nat => real))
                                  D2 p2))
                              ((fine::(real => real)
=> (nat => real) * (nat => real) => bool)
                                g ((Pair::(nat => real)
    => (nat => real) => (nat => real) * (nat => real))
                                    D2 p2))))))
                ((Ex::((nat => real) => bool) => bool)
                  (%x::nat => real.
                      (Ex::((nat => real) => bool) => bool)
                       (%p::nat => real.
                           (op &::bool => bool => bool)
                            ((tdiv::real * real
                                    => (nat => real) * (nat => real)
 => bool)
                              ((Pair::real => real => real * real) a c)
                              ((Pair::(nat => real)
=> (nat => real) => (nat => real) * (nat => real))
                                x p))
                            ((fine::(real => real)
                                    => (nat => real) * (nat => real)
 => bool)
                              g ((Pair::(nat => real)
  => (nat => real) => (nat => real) * (nat => real))
                                  x p))))))))"
  by (import transc DIVISION_APPEND)

lemma DIVISION_EXISTS: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real => bool) => bool)
      (%b::real.
          (All::((real => real) => bool) => bool)
           (%g::real => real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::real => real => bool) a b)
                  ((gauge::(real => bool) => (real => real) => bool)
                    (%x::real.
                        (op &::bool => bool => bool)
                         ((op <=::real => real => bool) a x)
                         ((op <=::real => real => bool) x b))
                    g))
                ((Ex::((nat => real) => bool) => bool)
                  (%D::nat => real.
                      (Ex::((nat => real) => bool) => bool)
                       (%p::nat => real.
                           (op &::bool => bool => bool)
                            ((tdiv::real * real
                                    => (nat => real) * (nat => real)
 => bool)
                              ((Pair::real => real => real * real) a b)
                              ((Pair::(nat => real)
=> (nat => real) => (nat => real) * (nat => real))
                                D p))
                            ((fine::(real => real)
                                    => (nat => real) * (nat => real)
 => bool)
                              g ((Pair::(nat => real)
  => (nat => real) => (nat => real) * (nat => real))
                                  D p))))))))"
  by (import transc DIVISION_EXISTS)

lemma GAUGE_MIN: "(All::((real => bool) => bool) => bool)
 (%E::real => bool.
     (All::((real => real) => bool) => bool)
      (%g1::real => real.
          (All::((real => real) => bool) => bool)
           (%g2::real => real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((gauge::(real => bool) => (real => real) => bool) E g1)
                  ((gauge::(real => bool) => (real => real) => bool) E g2))
                ((gauge::(real => bool) => (real => real) => bool) E
                  (%x::real.
                      (If::bool => real => real => real)
                       ((op <::real => real => bool) (g1 x) (g2 x)) (g1 x)
                       (g2 x))))))"
  by (import transc GAUGE_MIN)

lemma FINE_MIN: "(All::((real => real) => bool) => bool)
 (%g1::real => real.
     (All::((real => real) => bool) => bool)
      (%g2::real => real.
          (All::((nat => real) => bool) => bool)
           (%D::nat => real.
               (All::((nat => real) => bool) => bool)
                (%p::nat => real.
                    (op -->::bool => bool => bool)
                     ((fine::(real => real)
                             => (nat => real) * (nat => real) => bool)
                       (%x::real.
                           (If::bool => real => real => real)
                            ((op <::real => real => bool) (g1 x) (g2 x))
                            (g1 x) (g2 x))
                       ((Pair::(nat => real)
                               => (nat => real)
                                  => (nat => real) * (nat => real))
                         D p))
                     ((op &::bool => bool => bool)
                       ((fine::(real => real)
                               => (nat => real) * (nat => real) => bool)
                         g1 ((Pair::(nat => real)
                                    => (nat => real)
 => (nat => real) * (nat => real))
                              D p))
                       ((fine::(real => real)
                               => (nat => real) * (nat => real) => bool)
                         g2 ((Pair::(nat => real)
                                    => (nat => real)
 => (nat => real) * (nat => real))
                              D p)))))))"
  by (import transc FINE_MIN)

lemma DINT_UNIQ: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real => bool) => bool)
      (%b::real.
          (All::((real => real) => bool) => bool)
           (%f::real => real.
               (All::(real => bool) => bool)
                (%k1::real.
                    (All::(real => bool) => bool)
                     (%k2::real.
                         (op -->::bool => bool => bool)
                          ((op &::bool => bool => bool)
                            ((op <=::real => real => bool) a b)
                            ((op &::bool => bool => bool)
                              ((Dint::real * real
=> (real => real) => real => bool)
                                ((Pair::real => real => real * real) a b) f
                                k1)
                              ((Dint::real * real
=> (real => real) => real => bool)
                                ((Pair::real => real => real * real) a b) f
                                k2)))
                          ((op =::real => real => bool) k1 k2))))))"
  by (import transc DINT_UNIQ)

lemma INTEGRAL_NULL: "ALL (f::real => real) a::real. Dint (a, a) f (0::real)"
  by (import transc INTEGRAL_NULL)

lemma FTC1: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((real => real) => bool) => bool)
      (%f'::real => real.
          (All::(real => bool) => bool)
           (%a::real.
               (All::(real => bool) => bool)
                (%b::real.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((op <=::real => real => bool) a b)
                       ((All::(real => bool) => bool)
                         (%x::real.
                             (op -->::bool => bool => bool)
                              ((op &::bool => bool => bool)
                                ((op <=::real => real => bool) a x)
                                ((op <=::real => real => bool) x b))
                              ((diffl::(real => real)
 => real => real => bool)
                                f (f' x) x))))
                     ((Dint::real * real => (real => real) => real => bool)
                       ((Pair::real => real => real * real) a b) f'
                       ((op -::real => real => real) (f b) (f a)))))))"
  by (import transc FTC1)

lemma MCLAURIN: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((nat => real => real) => bool) => bool)
      (%diff::nat => real => real.
          (All::(real => bool) => bool)
           (%h::real.
               (All::(nat => bool) => bool)
                (%n::nat.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((op <::real => real => bool) (0::real) h)
                       ((op &::bool => bool => bool)
                         ((op <::nat => nat => bool) (0::nat) n)
                         ((op &::bool => bool => bool)
                           ((op =::(real => real) => (real => real) => bool)
                             (diff (0::nat)) f)
                           ((All::(nat => bool) => bool)
                             (%m::nat.
                                 (All::(real => bool) => bool)
                                  (%t::real.
(op -->::bool => bool => bool)
 ((op &::bool => bool => bool) ((op <::nat => nat => bool) m n)
   ((op &::bool => bool => bool) ((op <=::real => real => bool) (0::real) t)
     ((op <=::real => real => bool) t h)))
 ((diffl::(real => real) => real => real => bool) (diff m)
   (diff ((Suc::nat => nat) m) t) t)))))))
                     ((Ex::(real => bool) => bool)
                       (%t::real.
                           (op &::bool => bool => bool)
                            ((op <::real => real => bool) (0::real) t)
                            ((op &::bool => bool => bool)
                              ((op <::real => real => bool) t h)
                              ((op =::real => real => bool) (f h)
                                ((op +::real => real => real)
                                  ((real.sum::nat * nat
        => (nat => real) => real)
                                    ((Pair::nat => nat => nat * nat)
(0::nat) n)
                                    (%m::nat.
  (op *::real => real => real)
   ((op /::real => real => real) (diff m (0::real))
     ((real::nat => real) ((FACT::nat => nat) m)))
   ((op ^::real => nat => real) h m)))
                                  ((op *::real => real => real)
                                    ((op /::real => real => real) (diff n t)
((real::nat => real) ((FACT::nat => nat) n)))
                                    ((op ^::real => nat => real) h
n)))))))))))"
  by (import transc MCLAURIN)

lemma MCLAURIN_NEG: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((nat => real => real) => bool) => bool)
      (%diff::nat => real => real.
          (All::(real => bool) => bool)
           (%h::real.
               (All::(nat => bool) => bool)
                (%n::nat.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((op <::real => real => bool) h (0::real))
                       ((op &::bool => bool => bool)
                         ((op <::nat => nat => bool) (0::nat) n)
                         ((op &::bool => bool => bool)
                           ((op =::(real => real) => (real => real) => bool)
                             (diff (0::nat)) f)
                           ((All::(nat => bool) => bool)
                             (%m::nat.
                                 (All::(real => bool) => bool)
                                  (%t::real.
(op -->::bool => bool => bool)
 ((op &::bool => bool => bool) ((op <::nat => nat => bool) m n)
   ((op &::bool => bool => bool) ((op <=::real => real => bool) h t)
     ((op <=::real => real => bool) t (0::real))))
 ((diffl::(real => real) => real => real => bool) (diff m)
   (diff ((Suc::nat => nat) m) t) t)))))))
                     ((Ex::(real => bool) => bool)
                       (%t::real.
                           (op &::bool => bool => bool)
                            ((op <::real => real => bool) h t)
                            ((op &::bool => bool => bool)
                              ((op <::real => real => bool) t (0::real))
                              ((op =::real => real => bool) (f h)
                                ((op +::real => real => real)
                                  ((real.sum::nat * nat
        => (nat => real) => real)
                                    ((Pair::nat => nat => nat * nat)
(0::nat) n)
                                    (%m::nat.
  (op *::real => real => real)
   ((op /::real => real => real) (diff m (0::real))
     ((real::nat => real) ((FACT::nat => nat) m)))
   ((op ^::real => nat => real) h m)))
                                  ((op *::real => real => real)
                                    ((op /::real => real => real) (diff n t)
((real::nat => real) ((FACT::nat => nat) n)))
                                    ((op ^::real => nat => real) h
n)))))))))))"
  by (import transc MCLAURIN_NEG)

lemma MCLAURIN_ALL_LT: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((nat => real => real) => bool) => bool)
      (%diff::nat => real => real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op =::(real => real) => (real => real) => bool)
               (diff (0::nat)) f)
             ((All::(nat => bool) => bool)
               (%m::nat.
                   (All::(real => bool) => bool)
                    (%x::real.
                        (diffl::(real => real) => real => real => bool)
                         (diff m) (diff ((Suc::nat => nat) m) x) x))))
           ((All::(real => bool) => bool)
             (%x::real.
                 (All::(nat => bool) => bool)
                  (%n::nat.
                      (op -->::bool => bool => bool)
                       ((op &::bool => bool => bool)
                         ((Not::bool => bool)
                           ((op =::real => real => bool) x (0::real)))
                         ((op <::nat => nat => bool) (0::nat) n))
                       ((Ex::(real => bool) => bool)
                         (%t::real.
                             (op &::bool => bool => bool)
                              ((op <::real => real => bool) (0::real)
                                ((abs::real => real) t))
                              ((op &::bool => bool => bool)
                                ((op <::real => real => bool)
                                  ((abs::real => real) t)
                                  ((abs::real => real) x))
                                ((op =::real => real => bool) (f x)
                                  ((op +::real => real => real)
                                    ((real.sum::nat * nat
          => (nat => real) => real)
((Pair::nat => nat => nat * nat) (0::nat) n)
(%m::nat.
    (op *::real => real => real)
     ((op /::real => real => real) (diff m (0::real))
       ((real::nat => real) ((FACT::nat => nat) m)))
     ((op ^::real => nat => real) x m)))
                                    ((op *::real => real => real)
((op /::real => real => real) (diff n t)
  ((real::nat => real) ((FACT::nat => nat) n)))
((op ^::real => nat => real) x n))))))))))))"
  by (import transc MCLAURIN_ALL_LT)

lemma MCLAURIN_ZERO: "(All::((nat => real => real) => bool) => bool)
 (%diff::nat => real => real.
     (All::(nat => bool) => bool)
      (%n::nat.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op =::real => real => bool) x (0::real))
                  ((op <::nat => nat => bool) (0::nat) n))
                ((op =::real => real => bool)
                  ((real.sum::nat * nat => (nat => real) => real)
                    ((Pair::nat => nat => nat * nat) (0::nat) n)
                    (%m::nat.
                        (op *::real => real => real)
                         ((op /::real => real => real) (diff m (0::real))
                           ((real::nat => real) ((FACT::nat => nat) m)))
                         ((op ^::real => nat => real) x m)))
                  (diff (0::nat) (0::real))))))"
  by (import transc MCLAURIN_ZERO)

lemma MCLAURIN_ALL_LE: "(All::((real => real) => bool) => bool)
 (%f::real => real.
     (All::((nat => real => real) => bool) => bool)
      (%diff::nat => real => real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((op =::(real => real) => (real => real) => bool)
               (diff (0::nat)) f)
             ((All::(nat => bool) => bool)
               (%m::nat.
                   (All::(real => bool) => bool)
                    (%x::real.
                        (diffl::(real => real) => real => real => bool)
                         (diff m) (diff ((Suc::nat => nat) m) x) x))))
           ((All::(real => bool) => bool)
             (%x::real.
                 (All::(nat => bool) => bool)
                  (%n::nat.
                      (Ex::(real => bool) => bool)
                       (%t::real.
                           (op &::bool => bool => bool)
                            ((op <=::real => real => bool)
                              ((abs::real => real) t)
                              ((abs::real => real) x))
                            ((op =::real => real => bool) (f x)
                              ((op +::real => real => real)
                                ((real.sum::nat * nat
      => (nat => real) => real)
                                  ((Pair::nat => nat => nat * nat) (0::nat)
                                    n)
                                  (%m::nat.
(op *::real => real => real)
 ((op /::real => real => real) (diff m (0::real))
   ((real::nat => real) ((FACT::nat => nat) m)))
 ((op ^::real => nat => real) x m)))
                                ((op *::real => real => real)
                                  ((op /::real => real => real) (diff n t)
                                    ((real::nat => real)
((FACT::nat => nat) n)))
                                  ((op ^::real => nat => real) x n))))))))))"
  by (import transc MCLAURIN_ALL_LE)

lemma MCLAURIN_EXP_LT: "(All::(real => bool) => bool)
 (%x::real.
     (All::(nat => bool) => bool)
      (%n::nat.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((Not::bool => bool)
               ((op =::real => real => bool) x (0::real)))
             ((op <::nat => nat => bool) (0::nat) n))
           ((Ex::(real => bool) => bool)
             (%xa::real.
                 (op &::bool => bool => bool)
                  ((op <::real => real => bool) (0::real)
                    ((abs::real => real) xa))
                  ((op &::bool => bool => bool)
                    ((op <::real => real => bool) ((abs::real => real) xa)
                      ((abs::real => real) x))
                    ((op =::real => real => bool) ((exp::real => real) x)
                      ((op +::real => real => real)
                        ((real.sum::nat * nat => (nat => real) => real)
                          ((Pair::nat => nat => nat * nat) (0::nat) n)
                          (%m::nat.
                              (op /::real => real => real)
                               ((op ^::real => nat => real) x m)
                               ((real::nat => real)
                                 ((FACT::nat => nat) m))))
                        ((op *::real => real => real)
                          ((op /::real => real => real)
                            ((exp::real => real) xa)
                            ((real::nat => real) ((FACT::nat => nat) n)))
                          ((op ^::real => nat => real) x n)))))))))"
  by (import transc MCLAURIN_EXP_LT)

lemma MCLAURIN_EXP_LE: "ALL (x::real) n::nat.
   EX xa::real.
      abs xa <= abs x &
      exp x =
      real.sum (0::nat, n) (%m::nat. x ^ m / real (FACT m)) +
      exp xa / real (FACT n) * x ^ n"
  by (import transc MCLAURIN_EXP_LE)

lemma DIFF_LN_COMPOSITE: "(All::((real => real) => bool) => bool)
 (%g::real => real.
     (All::(real => bool) => bool)
      (%m::real.
          (All::(real => bool) => bool)
           (%x::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((diffl::(real => real) => real => real => bool) g m x)
                  ((op <::real => real => bool) (0::real) (g x)))
                ((diffl::(real => real) => real => real => bool)
                  (%x::real. (ln::real => real) (g x))
                  ((op *::real => real => real)
                    ((inverse::real => real) (g x)) m)
                  x))))"
  by (import transc DIFF_LN_COMPOSITE)

;end_setup

;setup_theory poly

consts
  poly :: "real list => real => real" 

specification (poly_primdef: poly) poly_def: "(ALL x::real. poly [] x = (0::real)) &
(ALL (h::real) (t::real list) x::real. poly (h # t) x = h + x * poly t x)"
  by (import poly poly_def)

consts
  poly_add :: "real list => real list => real list" 

specification (poly_add_primdef: poly_add) poly_add_def: "(ALL l2::real list. poly_add [] l2 = l2) &
(ALL (h::real) (t::real list) l2::real list.
    poly_add (h # t) l2 =
    (if l2 = [] then h # t else (h + hd l2) # poly_add t (tl l2)))"
  by (import poly poly_add_def)

consts
  "##" :: "real => real list => real list" ("##")

specification ("##") poly_cmul_def: "(ALL c::real. ## c [] = []) &
(ALL (c::real) (h::real) t::real list. ## c (h # t) = c * h # ## c t)"
  by (import poly poly_cmul_def)

consts
  poly_neg :: "real list => real list" 

defs
  poly_neg_primdef: "poly_neg == ## (- (1::real))"

lemma poly_neg_def: "poly_neg = ## (- (1::real))"
  by (import poly poly_neg_def)

consts
  poly_mul :: "real list => real list => real list" 

specification (poly_mul_primdef: poly_mul) poly_mul_def: "(ALL l2::real list. poly_mul [] l2 = []) &
(ALL (h::real) (t::real list) l2::real list.
    poly_mul (h # t) l2 =
    (if t = [] then ## h l2
     else poly_add (## h l2) ((0::real) # poly_mul t l2)))"
  by (import poly poly_mul_def)

consts
  poly_exp :: "real list => nat => real list" 

specification (poly_exp_primdef: poly_exp) poly_exp_def: "(ALL p::real list. poly_exp p (0::nat) = [1::real]) &
(ALL (p::real list) n::nat. poly_exp p (Suc n) = poly_mul p (poly_exp p n))"
  by (import poly poly_exp_def)

consts
  poly_diff_aux :: "nat => real list => real list" 

specification (poly_diff_aux_primdef: poly_diff_aux) poly_diff_aux_def: "(ALL n::nat. poly_diff_aux n [] = []) &
(ALL (n::nat) (h::real) t::real list.
    poly_diff_aux n (h # t) = real n * h # poly_diff_aux (Suc n) t)"
  by (import poly poly_diff_aux_def)

constdefs
  diff :: "real list => real list" 
  "diff == %l::real list. if l = [] then [] else poly_diff_aux (1::nat) (tl l)"

lemma poly_diff_def: "ALL l::real list.
   diff l = (if l = [] then [] else poly_diff_aux (1::nat) (tl l))"
  by (import poly poly_diff_def)

lemma POLY_ADD_CLAUSES: "poly_add [] (p2::real list) = p2 &
poly_add (p1::real list) [] = p1 &
poly_add ((h1::real) # (t1::real list)) ((h2::real) # (t2::real list)) =
(h1 + h2) # poly_add t1 t2"
  by (import poly POLY_ADD_CLAUSES)

lemma POLY_CMUL_CLAUSES: "## (c::real) [] = [] & ## c ((h::real) # (t::real list)) = c * h # ## c t"
  by (import poly POLY_CMUL_CLAUSES)

lemma POLY_NEG_CLAUSES: "poly_neg [] = [] & poly_neg ((h::real) # (t::real list)) = - h # poly_neg t"
  by (import poly POLY_NEG_CLAUSES)

lemma POLY_MUL_CLAUSES: "poly_mul [] (p2::real list) = [] &
poly_mul [h1::real] p2 = ## h1 p2 &
poly_mul (h1 # (k1::real) # (t1::real list)) p2 =
poly_add (## h1 p2) ((0::real) # poly_mul (k1 # t1) p2)"
  by (import poly POLY_MUL_CLAUSES)

lemma POLY_DIFF_CLAUSES: "diff [] = [] &
diff [c::real] = [] &
diff ((h::real) # (t::real list)) = poly_diff_aux (1::nat) t"
  by (import poly POLY_DIFF_CLAUSES)

lemma POLY_ADD: "ALL (t::real list) (p2::real list) x::real.
   poly (poly_add t p2) x = poly t x + poly p2 x"
  by (import poly POLY_ADD)

lemma POLY_CMUL: "ALL (t::real list) (c::real) x::real. poly (## c t) x = c * poly t x"
  by (import poly POLY_CMUL)

lemma POLY_NEG: "ALL (x::real list) xa::real. poly (poly_neg x) xa = - poly x xa"
  by (import poly POLY_NEG)

lemma POLY_MUL: "ALL (x::real) (t::real list) p2::real list.
   poly (poly_mul t p2) x = poly t x * poly p2 x"
  by (import poly POLY_MUL)

lemma POLY_EXP: "ALL (p::real list) (n::nat) x::real. poly (poly_exp p n) x = poly p x ^ n"
  by (import poly POLY_EXP)

lemma POLY_DIFF_LEMMA: "ALL (t::real list) (n::nat) x::real.
   diffl (%x::real. x ^ Suc n * poly t x)
    (x ^ n * poly (poly_diff_aux (Suc n) t) x) x"
  by (import poly POLY_DIFF_LEMMA)

lemma POLY_DIFF: "ALL (t::real list) x::real. diffl (poly t) (poly (diff t) x) x"
  by (import poly POLY_DIFF)

lemma POLY_DIFFERENTIABLE: "ALL l::real list. All (differentiable (poly l))"
  by (import poly POLY_DIFFERENTIABLE)

lemma POLY_CONT: "ALL l::real list. All (contl (poly l))"
  by (import poly POLY_CONT)

lemma POLY_IVT_POS: "(All::(real list => bool) => bool)
 (%x::real list.
     (All::(real => bool) => bool)
      (%xa::real.
          (All::(real => bool) => bool)
           (%xb::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) xa xb)
                  ((op &::bool => bool => bool)
                    ((op <::real => real => bool)
                      ((poly::real list => real => real) x xa) (0::real))
                    ((op <::real => real => bool) (0::real)
                      ((poly::real list => real => real) x xb))))
                ((Ex::(real => bool) => bool)
                  (%xc::real.
                      (op &::bool => bool => bool)
                       ((op <::real => real => bool) xa xc)
                       ((op &::bool => bool => bool)
                         ((op <::real => real => bool) xc xb)
                         ((op =::real => real => bool)
                           ((poly::real list => real => real) x xc)
                           (0::real))))))))"
  by (import poly POLY_IVT_POS)

lemma POLY_IVT_NEG: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <::real => real => bool) a b)
                  ((op &::bool => bool => bool)
                    ((op <::real => real => bool) (0::real)
                      ((poly::real list => real => real) p a))
                    ((op <::real => real => bool)
                      ((poly::real list => real => real) p b) (0::real))))
                ((Ex::(real => bool) => bool)
                  (%x::real.
                      (op &::bool => bool => bool)
                       ((op <::real => real => bool) a x)
                       ((op &::bool => bool => bool)
                         ((op <::real => real => bool) x b)
                         ((op =::real => real => bool)
                           ((poly::real list => real => real) p x)
                           (0::real))))))))"
  by (import poly POLY_IVT_NEG)

lemma POLY_MVT: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(real => bool) => bool)
           (%b::real.
               (op -->::bool => bool => bool)
                ((op <::real => real => bool) a b)
                ((Ex::(real => bool) => bool)
                  (%x::real.
                      (op &::bool => bool => bool)
                       ((op <::real => real => bool) a x)
                       ((op &::bool => bool => bool)
                         ((op <::real => real => bool) x b)
                         ((op =::real => real => bool)
                           ((op -::real => real => real)
                             ((poly::real list => real => real) p b)
                             ((poly::real list => real => real) p a))
                           ((op *::real => real => real)
                             ((op -::real => real => real) b a)
                             ((poly::real list => real => real)
                               ((diff::real list => real list) p) x)))))))))"
  by (import poly POLY_MVT)

lemma POLY_ADD_RZERO: "ALL x::real list. poly (poly_add x []) = poly x"
  by (import poly POLY_ADD_RZERO)

lemma POLY_MUL_ASSOC: "ALL (x::real list) (xa::real list) xb::real list.
   poly (poly_mul x (poly_mul xa xb)) = poly (poly_mul (poly_mul x xa) xb)"
  by (import poly POLY_MUL_ASSOC)

lemma POLY_EXP_ADD: "ALL (x::nat) (xa::nat) xb::real list.
   poly (poly_exp xb (xa + x)) =
   poly (poly_mul (poly_exp xb xa) (poly_exp xb x))"
  by (import poly POLY_EXP_ADD)

lemma POLY_DIFF_AUX_ADD: "ALL (t::real list) (p2::real list) n::nat.
   poly (poly_diff_aux n (poly_add t p2)) =
   poly (poly_add (poly_diff_aux n t) (poly_diff_aux n p2))"
  by (import poly POLY_DIFF_AUX_ADD)

lemma POLY_DIFF_AUX_CMUL: "ALL (t::real list) (c::real) n::nat.
   poly (poly_diff_aux n (## c t)) = poly (## c (poly_diff_aux n t))"
  by (import poly POLY_DIFF_AUX_CMUL)

lemma POLY_DIFF_AUX_NEG: "ALL (x::real list) xa::nat.
   poly (poly_diff_aux xa (poly_neg x)) =
   poly (poly_neg (poly_diff_aux xa x))"
  by (import poly POLY_DIFF_AUX_NEG)

lemma POLY_DIFF_AUX_MUL_LEMMA: "ALL (t::real list) n::nat.
   poly (poly_diff_aux (Suc n) t) = poly (poly_add (poly_diff_aux n t) t)"
  by (import poly POLY_DIFF_AUX_MUL_LEMMA)

lemma POLY_DIFF_ADD: "ALL (t::real list) p2::real list.
   poly (diff (poly_add t p2)) = poly (poly_add (diff t) (diff p2))"
  by (import poly POLY_DIFF_ADD)

lemma POLY_DIFF_CMUL: "ALL (t::real list) c::real. poly (diff (## c t)) = poly (## c (diff t))"
  by (import poly POLY_DIFF_CMUL)

lemma POLY_DIFF_NEG: "ALL x::real list. poly (diff (poly_neg x)) = poly (poly_neg (diff x))"
  by (import poly POLY_DIFF_NEG)

lemma POLY_DIFF_MUL_LEMMA: "ALL (x::real list) xa::real.
   poly (diff (xa # x)) = poly (poly_add ((0::real) # diff x) x)"
  by (import poly POLY_DIFF_MUL_LEMMA)

lemma POLY_DIFF_MUL: "ALL (t::real list) p2::real list.
   poly (diff (poly_mul t p2)) =
   poly (poly_add (poly_mul t (diff p2)) (poly_mul (diff t) p2))"
  by (import poly POLY_DIFF_MUL)

lemma POLY_DIFF_EXP: "ALL (p::real list) n::nat.
   poly (diff (poly_exp p (Suc n))) =
   poly (poly_mul (## (real (Suc n)) (poly_exp p n)) (diff p))"
  by (import poly POLY_DIFF_EXP)

lemma POLY_DIFF_EXP_PRIME: "ALL (n::nat) a::real.
   poly (diff (poly_exp [- a, 1::real] (Suc n))) =
   poly (## (real (Suc n)) (poly_exp [- a, 1::real] n))"
  by (import poly POLY_DIFF_EXP_PRIME)

lemma POLY_LINEAR_REM: "ALL (t::real list) h::real.
   EX (q::real list) r::real.
      h # t = poly_add [r] (poly_mul [- (a::real), 1::real] q)"
  by (import poly POLY_LINEAR_REM)

lemma POLY_LINEAR_DIVIDES: "ALL (a::real) t::real list.
   (poly t a = (0::real)) =
   (t = [] | (EX q::real list. t = poly_mul [- a, 1::real] q))"
  by (import poly POLY_LINEAR_DIVIDES)

lemma POLY_LENGTH_MUL: "ALL x::real list.
   length (poly_mul [- (a::real), 1::real] x) = Suc (length x)"
  by (import poly POLY_LENGTH_MUL)

lemma POLY_ROOTS_INDEX_LEMMA: "(All::(nat => bool) => bool)
 (%n::nat.
     (All::(real list => bool) => bool)
      (%p::real list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((Not::bool => bool)
               ((op =::(real => real) => (real => real) => bool)
                 ((poly::real list => real => real) p)
                 ((poly::real list => real => real) ([]::real list))))
             ((op =::nat => nat => bool) ((size::real list => nat) p) n))
           ((Ex::((nat => real) => bool) => bool)
             (%i::nat => real.
                 (All::(real => bool) => bool)
                  (%x::real.
                      (op -->::bool => bool => bool)
                       ((op =::real => real => bool)
                         ((poly::real list => real => real) p x) (0::real))
                       ((Ex::(nat => bool) => bool)
                         (%m::nat.
                             (op &::bool => bool => bool)
                              ((op <=::nat => nat => bool) m n)
                              ((op =::real => real => bool) x (i m)))))))))"
  by (import poly POLY_ROOTS_INDEX_LEMMA)

lemma POLY_ROOTS_INDEX_LENGTH: "(All::(real list => bool) => bool)
 (%p::real list.
     (op -->::bool => bool => bool)
      ((Not::bool => bool)
        ((op =::(real => real) => (real => real) => bool)
          ((poly::real list => real => real) p)
          ((poly::real list => real => real) ([]::real list))))
      ((Ex::((nat => real) => bool) => bool)
        (%i::nat => real.
            (All::(real => bool) => bool)
             (%x::real.
                 (op -->::bool => bool => bool)
                  ((op =::real => real => bool)
                    ((poly::real list => real => real) p x) (0::real))
                  ((Ex::(nat => bool) => bool)
                    (%n::nat.
                        (op &::bool => bool => bool)
                         ((op <=::nat => nat => bool) n
                           ((size::real list => nat) p))
                         ((op =::real => real => bool) x (i n))))))))"
  by (import poly POLY_ROOTS_INDEX_LENGTH)

lemma POLY_ROOTS_FINITE_LEMMA: "(All::(real list => bool) => bool)
 (%p::real list.
     (op -->::bool => bool => bool)
      ((Not::bool => bool)
        ((op =::(real => real) => (real => real) => bool)
          ((poly::real list => real => real) p)
          ((poly::real list => real => real) ([]::real list))))
      ((Ex::(nat => bool) => bool)
        (%N::nat.
            (Ex::((nat => real) => bool) => bool)
             (%i::nat => real.
                 (All::(real => bool) => bool)
                  (%x::real.
                      (op -->::bool => bool => bool)
                       ((op =::real => real => bool)
                         ((poly::real list => real => real) p x) (0::real))
                       ((Ex::(nat => bool) => bool)
                         (%n::nat.
                             (op &::bool => bool => bool)
                              ((op <::nat => nat => bool) n N)
                              ((op =::real => real => bool) x (i n)))))))))"
  by (import poly POLY_ROOTS_FINITE_LEMMA)

lemma FINITE_LEMMA: "(All::((nat => real) => bool) => bool)
 (%i::nat => real.
     (All::(nat => bool) => bool)
      (%x::nat.
          (All::((real => bool) => bool) => bool)
           (%xa::real => bool.
               (op -->::bool => bool => bool)
                ((All::(real => bool) => bool)
                  (%xb::real.
                      (op -->::bool => bool => bool) (xa xb)
                       ((Ex::(nat => bool) => bool)
                         (%n::nat.
                             (op &::bool => bool => bool)
                              ((op <::nat => nat => bool) n x)
                              ((op =::real => real => bool) xb (i n))))))
                ((Ex::(real => bool) => bool)
                  (%a::real.
                      (All::(real => bool) => bool)
                       (%x::real.
                           (op -->::bool => bool => bool) (xa x)
                            ((op <::real => real => bool) x a)))))))"
  by (import poly FINITE_LEMMA)

lemma POLY_ROOTS_FINITE: "(All::(real list => bool) => bool)
 (%p::real list.
     (op =::bool => bool => bool)
      ((Not::bool => bool)
        ((op =::(real => real) => (real => real) => bool)
          ((poly::real list => real => real) p)
          ((poly::real list => real => real) ([]::real list))))
      ((Ex::(nat => bool) => bool)
        (%N::nat.
            (Ex::((nat => real) => bool) => bool)
             (%i::nat => real.
                 (All::(real => bool) => bool)
                  (%x::real.
                      (op -->::bool => bool => bool)
                       ((op =::real => real => bool)
                         ((poly::real list => real => real) p x) (0::real))
                       ((Ex::(nat => bool) => bool)
                         (%n::nat.
                             (op &::bool => bool => bool)
                              ((op <::nat => nat => bool) n N)
                              ((op =::real => real => bool) x (i n)))))))))"
  by (import poly POLY_ROOTS_FINITE)

lemma POLY_ENTIRE_LEMMA: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((Not::bool => bool)
               ((op =::(real => real) => (real => real) => bool)
                 ((poly::real list => real => real) p)
                 ((poly::real list => real => real) ([]::real list))))
             ((Not::bool => bool)
               ((op =::(real => real) => (real => real) => bool)
                 ((poly::real list => real => real) q)
                 ((poly::real list => real => real) ([]::real list)))))
           ((Not::bool => bool)
             ((op =::(real => real) => (real => real) => bool)
               ((poly::real list => real => real)
                 ((poly_mul::real list => real list => real list) p q))
               ((poly::real list => real => real) ([]::real list))))))"
  by (import poly POLY_ENTIRE_LEMMA)

lemma POLY_ENTIRE: "ALL (p::real list) q::real list.
   (poly (poly_mul p q) = poly []) = (poly p = poly [] | poly q = poly [])"
  by (import poly POLY_ENTIRE)

lemma POLY_MUL_LCANCEL: "ALL (x::real list) (xa::real list) xb::real list.
   (poly (poly_mul x xa) = poly (poly_mul x xb)) =
   (poly x = poly [] | poly xa = poly xb)"
  by (import poly POLY_MUL_LCANCEL)

lemma POLY_EXP_EQ_0: "ALL (p::real list) n::nat.
   (poly (poly_exp p n) = poly []) = (poly p = poly [] & n ~= (0::nat))"
  by (import poly POLY_EXP_EQ_0)

lemma POLY_PRIME_EQ_0: "ALL a::real. poly [a, 1::real] ~= poly []"
  by (import poly POLY_PRIME_EQ_0)

lemma POLY_EXP_PRIME_EQ_0: "ALL (a::real) n::nat. poly (poly_exp [a, 1::real] n) ~= poly []"
  by (import poly POLY_EXP_PRIME_EQ_0)

lemma POLY_ZERO_LEMMA: "(All::(real => bool) => bool)
 (%h::real.
     (All::(real list => bool) => bool)
      (%t::real list.
          (op -->::bool => bool => bool)
           ((op =::(real => real) => (real => real) => bool)
             ((poly::real list => real => real)
               ((op #::real => real list => real list) h t))
             ((poly::real list => real => real) ([]::real list)))
           ((op &::bool => bool => bool)
             ((op =::real => real => bool) h (0::real))
             ((op =::(real => real) => (real => real) => bool)
               ((poly::real list => real => real) t)
               ((poly::real list => real => real) ([]::real list))))))"
  by (import poly POLY_ZERO_LEMMA)

lemma POLY_ZERO: "ALL t::real list. (poly t = poly []) = list_all (%c::real. c = (0::real)) t"
  by (import poly POLY_ZERO)

lemma POLY_DIFF_AUX_ISZERO: "ALL (t::real list) n::nat.
   list_all (%c::real. c = (0::real)) (poly_diff_aux (Suc n) t) =
   list_all (%c::real. c = (0::real)) t"
  by (import poly POLY_DIFF_AUX_ISZERO)

lemma POLY_DIFF_ISZERO: "(All::(real list => bool) => bool)
 (%x::real list.
     (op -->::bool => bool => bool)
      ((op =::(real => real) => (real => real) => bool)
        ((poly::real list => real => real)
          ((diff::real list => real list) x))
        ((poly::real list => real => real) ([]::real list)))
      ((Ex::(real => bool) => bool)
        (%h::real.
            (op =::(real => real) => (real => real) => bool)
             ((poly::real list => real => real) x)
             ((poly::real list => real => real)
               ((op #::real => real list => real list) h
                 ([]::real list))))))"
  by (import poly POLY_DIFF_ISZERO)

lemma POLY_DIFF_ZERO: "(All::(real list => bool) => bool)
 (%x::real list.
     (op -->::bool => bool => bool)
      ((op =::(real => real) => (real => real) => bool)
        ((poly::real list => real => real) x)
        ((poly::real list => real => real) ([]::real list)))
      ((op =::(real => real) => (real => real) => bool)
        ((poly::real list => real => real)
          ((diff::real list => real list) x))
        ((poly::real list => real => real) ([]::real list))))"
  by (import poly POLY_DIFF_ZERO)

lemma POLY_DIFF_WELLDEF: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (op -->::bool => bool => bool)
           ((op =::(real => real) => (real => real) => bool)
             ((poly::real list => real => real) p)
             ((poly::real list => real => real) q))
           ((op =::(real => real) => (real => real) => bool)
             ((poly::real list => real => real)
               ((diff::real list => real list) p))
             ((poly::real list => real => real)
               ((diff::real list => real list) q)))))"
  by (import poly POLY_DIFF_WELLDEF)

constdefs
  poly_divides :: "real list => real list => bool" 
  "poly_divides ==
%(p1::real list) p2::real list.
   EX q::real list. poly p2 = poly (poly_mul p1 q)"

lemma poly_divides: "ALL (p1::real list) p2::real list.
   poly_divides p1 p2 = (EX q::real list. poly p2 = poly (poly_mul p1 q))"
  by (import poly poly_divides)

lemma POLY_PRIMES: "ALL (a::real) (p::real list) q::real list.
   poly_divides [a, 1::real] (poly_mul p q) =
   (poly_divides [a, 1::real] p | poly_divides [a, 1::real] q)"
  by (import poly POLY_PRIMES)

lemma POLY_DIVIDES_REFL: "ALL p::real list. poly_divides p p"
  by (import poly POLY_DIVIDES_REFL)

lemma POLY_DIVIDES_TRANS: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (All::(real list => bool) => bool)
           (%r::real list.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((poly_divides::real list => real list => bool) p q)
                  ((poly_divides::real list => real list => bool) q r))
                ((poly_divides::real list => real list => bool) p r))))"
  by (import poly POLY_DIVIDES_TRANS)

lemma POLY_DIVIDES_EXP: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(nat => bool) => bool)
      (%m::nat.
          (All::(nat => bool) => bool)
           (%n::nat.
               (op -->::bool => bool => bool)
                ((op <=::nat => nat => bool) m n)
                ((poly_divides::real list => real list => bool)
                  ((poly_exp::real list => nat => real list) p m)
                  ((poly_exp::real list => nat => real list) p n)))))"
  by (import poly POLY_DIVIDES_EXP)

lemma POLY_EXP_DIVIDES: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (All::(nat => bool) => bool)
           (%m::nat.
               (All::(nat => bool) => bool)
                (%n::nat.
                    (op -->::bool => bool => bool)
                     ((op &::bool => bool => bool)
                       ((poly_divides::real list => real list => bool)
                         ((poly_exp::real list => nat => real list) p n) q)
                       ((op <=::nat => nat => bool) m n))
                     ((poly_divides::real list => real list => bool)
                       ((poly_exp::real list => nat => real list) p m)
                       q)))))"
  by (import poly POLY_EXP_DIVIDES)

lemma POLY_DIVIDES_ADD: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (All::(real list => bool) => bool)
           (%r::real list.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((poly_divides::real list => real list => bool) p q)
                  ((poly_divides::real list => real list => bool) p r))
                ((poly_divides::real list => real list => bool) p
                  ((poly_add::real list => real list => real list) q r)))))"
  by (import poly POLY_DIVIDES_ADD)

lemma POLY_DIVIDES_SUB: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (All::(real list => bool) => bool)
           (%r::real list.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((poly_divides::real list => real list => bool) p q)
                  ((poly_divides::real list => real list => bool) p
                    ((poly_add::real list => real list => real list) q r)))
                ((poly_divides::real list => real list => bool) p r))))"
  by (import poly POLY_DIVIDES_SUB)

lemma POLY_DIVIDES_SUB2: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (All::(real list => bool) => bool)
           (%r::real list.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((poly_divides::real list => real list => bool) p r)
                  ((poly_divides::real list => real list => bool) p
                    ((poly_add::real list => real list => real list) q r)))
                ((poly_divides::real list => real list => bool) p q))))"
  by (import poly POLY_DIVIDES_SUB2)

lemma POLY_DIVIDES_ZERO: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (op -->::bool => bool => bool)
           ((op =::(real => real) => (real => real) => bool)
             ((poly::real list => real => real) p)
             ((poly::real list => real => real) ([]::real list)))
           ((poly_divides::real list => real list => bool) q p)))"
  by (import poly POLY_DIVIDES_ZERO)

lemma POLY_ORDER_EXISTS: "(All::(real => bool) => bool)
 (%a::real.
     (All::(nat => bool) => bool)
      (%d::nat.
          (All::(real list => bool) => bool)
           (%p::real list.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op =::nat => nat => bool) ((size::real list => nat) p)
                    d)
                  ((Not::bool => bool)
                    ((op =::(real => real) => (real => real) => bool)
                      ((poly::real list => real => real) p)
                      ((poly::real list => real => real) ([]::real list)))))
                ((Ex::(nat => bool) => bool)
                  (%x::nat.
                      (op &::bool => bool => bool)
                       ((poly_divides::real list => real list => bool)
                         ((poly_exp::real list => nat => real list)
                           ((op #::real => real list => real list)
                             ((uminus::real => real) a)
                             ((op #::real => real list => real list)
                               (1::real) ([]::real list)))
                           x)
                         p)
                       ((Not::bool => bool)
                         ((poly_divides::real list => real list => bool)
                           ((poly_exp::real list => nat => real list)
                             ((op #::real => real list => real list)
                               ((uminus::real => real) a)
                               ((op #::real => real list => real list)
                                 (1::real) ([]::real list)))
                             ((Suc::nat => nat) x))
                           p)))))))"
  by (import poly POLY_ORDER_EXISTS)

lemma POLY_ORDER: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real => bool) => bool)
      (%a::real.
          (op -->::bool => bool => bool)
           ((Not::bool => bool)
             ((op =::(real => real) => (real => real) => bool)
               ((poly::real list => real => real) p)
               ((poly::real list => real => real) ([]::real list))))
           ((Ex1::(nat => bool) => bool)
             (%n::nat.
                 (op &::bool => bool => bool)
                  ((poly_divides::real list => real list => bool)
                    ((poly_exp::real list => nat => real list)
                      ((op #::real => real list => real list)
                        ((uminus::real => real) a)
                        ((op #::real => real list => real list) (1::real)
                          ([]::real list)))
                      n)
                    p)
                  ((Not::bool => bool)
                    ((poly_divides::real list => real list => bool)
                      ((poly_exp::real list => nat => real list)
                        ((op #::real => real list => real list)
                          ((uminus::real => real) a)
                          ((op #::real => real list => real list) (1::real)
                            ([]::real list)))
                        ((Suc::nat => nat) n))
                      p))))))"
  by (import poly POLY_ORDER)

constdefs
  poly_order :: "real => real list => nat" 
  "poly_order ==
%(a::real) p::real list.
   SOME n::nat.
      poly_divides (poly_exp [- a, 1::real] n) p &
      ~ poly_divides (poly_exp [- a, 1::real] (Suc n)) p"

lemma poly_order: "ALL (a::real) p::real list.
   poly_order a p =
   (SOME n::nat.
       poly_divides (poly_exp [- a, 1::real] n) p &
       ~ poly_divides (poly_exp [- a, 1::real] (Suc n)) p)"
  by (import poly poly_order)

lemma ORDER: "ALL (p::real list) (a::real) n::nat.
   (poly_divides (poly_exp [- a, 1::real] n) p &
    ~ poly_divides (poly_exp [- a, 1::real] (Suc n)) p) =
   (n = poly_order a p & poly p ~= poly [])"
  by (import poly ORDER)

lemma ORDER_THM: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real => bool) => bool)
      (%a::real.
          (op -->::bool => bool => bool)
           ((Not::bool => bool)
             ((op =::(real => real) => (real => real) => bool)
               ((poly::real list => real => real) p)
               ((poly::real list => real => real) ([]::real list))))
           ((op &::bool => bool => bool)
             ((poly_divides::real list => real list => bool)
               ((poly_exp::real list => nat => real list)
                 ((op #::real => real list => real list)
                   ((uminus::real => real) a)
                   ((op #::real => real list => real list) (1::real)
                     ([]::real list)))
                 ((poly_order::real => real list => nat) a p))
               p)
             ((Not::bool => bool)
               ((poly_divides::real list => real list => bool)
                 ((poly_exp::real list => nat => real list)
                   ((op #::real => real list => real list)
                     ((uminus::real => real) a)
                     ((op #::real => real list => real list) (1::real)
                       ([]::real list)))
                   ((Suc::nat => nat)
                     ((poly_order::real => real list => nat) a p)))
                 p)))))"
  by (import poly ORDER_THM)

lemma ORDER_UNIQUE: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real => bool) => bool)
      (%a::real.
          (All::(nat => bool) => bool)
           (%n::nat.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((Not::bool => bool)
                    ((op =::(real => real) => (real => real) => bool)
                      ((poly::real list => real => real) p)
                      ((poly::real list => real => real) ([]::real list))))
                  ((op &::bool => bool => bool)
                    ((poly_divides::real list => real list => bool)
                      ((poly_exp::real list => nat => real list)
                        ((op #::real => real list => real list)
                          ((uminus::real => real) a)
                          ((op #::real => real list => real list) (1::real)
                            ([]::real list)))
                        n)
                      p)
                    ((Not::bool => bool)
                      ((poly_divides::real list => real list => bool)
                        ((poly_exp::real list => nat => real list)
                          ((op #::real => real list => real list)
                            ((uminus::real => real) a)
                            ((op #::real => real list => real list)
                              (1::real) ([]::real list)))
                          ((Suc::nat => nat) n))
                        p))))
                ((op =::nat => nat => bool) n
                  ((poly_order::real => real list => nat) a p)))))"
  by (import poly ORDER_UNIQUE)

lemma ORDER_POLY: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (All::(real => bool) => bool)
           (%a::real.
               (op -->::bool => bool => bool)
                ((op =::(real => real) => (real => real) => bool)
                  ((poly::real list => real => real) p)
                  ((poly::real list => real => real) q))
                ((op =::nat => nat => bool)
                  ((poly_order::real => real list => nat) a p)
                  ((poly_order::real => real list => nat) a q)))))"
  by (import poly ORDER_POLY)

lemma ORDER_ROOT: "ALL (p::real list) a::real.
   (poly p a = (0::real)) = (poly p = poly [] | poly_order a p ~= (0::nat))"
  by (import poly ORDER_ROOT)

lemma ORDER_DIVIDES: "ALL (p::real list) (a::real) n::nat.
   poly_divides (poly_exp [- a, 1::real] n) p =
   (poly p = poly [] | n <= poly_order a p)"
  by (import poly ORDER_DIVIDES)

lemma ORDER_DECOMP: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real => bool) => bool)
      (%a::real.
          (op -->::bool => bool => bool)
           ((Not::bool => bool)
             ((op =::(real => real) => (real => real) => bool)
               ((poly::real list => real => real) p)
               ((poly::real list => real => real) ([]::real list))))
           ((Ex::(real list => bool) => bool)
             (%x::real list.
                 (op &::bool => bool => bool)
                  ((op =::(real => real) => (real => real) => bool)
                    ((poly::real list => real => real) p)
                    ((poly::real list => real => real)
                      ((poly_mul::real list => real list => real list)
                        ((poly_exp::real list => nat => real list)
                          ((op #::real => real list => real list)
                            ((uminus::real => real) a)
                            ((op #::real => real list => real list)
                              (1::real) ([]::real list)))
                          ((poly_order::real => real list => nat) a p))
                        x)))
                  ((Not::bool => bool)
                    ((poly_divides::real list => real list => bool)
                      ((op #::real => real list => real list)
                        ((uminus::real => real) a)
                        ((op #::real => real list => real list) (1::real)
                          ([]::real list)))
                      x))))))"
  by (import poly ORDER_DECOMP)

lemma ORDER_MUL: "(All::(real => bool) => bool)
 (%a::real.
     (All::(real list => bool) => bool)
      (%p::real list.
          (All::(real list => bool) => bool)
           (%q::real list.
               (op -->::bool => bool => bool)
                ((Not::bool => bool)
                  ((op =::(real => real) => (real => real) => bool)
                    ((poly::real list => real => real)
                      ((poly_mul::real list => real list => real list) p q))
                    ((poly::real list => real => real) ([]::real list))))
                ((op =::nat => nat => bool)
                  ((poly_order::real => real list => nat) a
                    ((poly_mul::real list => real list => real list) p q))
                  ((op +::nat => nat => nat)
                    ((poly_order::real => real list => nat) a p)
                    ((poly_order::real => real list => nat) a q))))))"
  by (import poly ORDER_MUL)

lemma ORDER_DIFF: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real => bool) => bool)
      (%a::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((Not::bool => bool)
               ((op =::(real => real) => (real => real) => bool)
                 ((poly::real list => real => real)
                   ((diff::real list => real list) p))
                 ((poly::real list => real => real) ([]::real list))))
             ((Not::bool => bool)
               ((op =::nat => nat => bool)
                 ((poly_order::real => real list => nat) a p) (0::nat))))
           ((op =::nat => nat => bool)
             ((poly_order::real => real list => nat) a p)
             ((Suc::nat => nat)
               ((poly_order::real => real list => nat) a
                 ((diff::real list => real list) p))))))"
  by (import poly ORDER_DIFF)

lemma POLY_SQUAREFREE_DECOMP_ORDER: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (All::(real list => bool) => bool)
           (%d::real list.
               (All::(real list => bool) => bool)
                (%e::real list.
                    (All::(real list => bool) => bool)
                     (%r::real list.
                         (All::(real list => bool) => bool)
                          (%s::real list.
                              (op -->::bool => bool => bool)
                               ((op &::bool => bool => bool)
                                 ((Not::bool => bool)
                                   ((op =::(real => real)
     => (real => real) => bool)
                                     ((poly::real list => real => real)
 ((diff::real list => real list) p))
                                     ((poly::real list => real => real)
 ([]::real list))))
                                 ((op &::bool => bool => bool)
                                   ((op =::(real => real)
     => (real => real) => bool)
                                     ((poly::real list => real => real) p)
                                     ((poly::real list => real => real)
 ((poly_mul::real list => real list => real list) q d)))
                                   ((op &::bool => bool => bool)
                                     ((op =::(real => real)
       => (real => real) => bool)
 ((poly::real list => real => real) ((diff::real list => real list) p))
 ((poly::real list => real => real)
   ((poly_mul::real list => real list => real list) e d)))
                                     ((op =::(real => real)
       => (real => real) => bool)
 ((poly::real list => real => real) d)
 ((poly::real list => real => real)
   ((poly_add::real list => real list => real list)
     ((poly_mul::real list => real list => real list) r p)
     ((poly_mul::real list => real list => real list) s
       ((diff::real list => real list) p))))))))
                               ((All::(real => bool) => bool)
                                 (%a::real.
                                     (op =::nat => nat => bool)
((poly_order::real => real list => nat) a q)
((If::bool => nat => nat => nat)
  ((op =::nat => nat => bool) ((poly_order::real => real list => nat) a p)
    (0::nat))
  (0::nat) (1::nat))))))))))"
  by (import poly POLY_SQUAREFREE_DECOMP_ORDER)

constdefs
  rsquarefree :: "real list => bool" 
  "rsquarefree ==
%p::real list.
   poly p ~= poly [] &
   (ALL a::real. poly_order a p = (0::nat) | poly_order a p = (1::nat))"

lemma rsquarefree: "ALL p::real list.
   rsquarefree p =
   (poly p ~= poly [] &
    (ALL a::real. poly_order a p = (0::nat) | poly_order a p = (1::nat)))"
  by (import poly rsquarefree)

lemma RSQUAREFREE_ROOTS: "ALL p::real list.
   rsquarefree p =
   (ALL a::real. ~ (poly p a = (0::real) & poly (diff p) a = (0::real)))"
  by (import poly RSQUAREFREE_ROOTS)

lemma RSQUAREFREE_DECOMP: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real => bool) => bool)
      (%a::real.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((rsquarefree::real list => bool) p)
             ((op =::real => real => bool)
               ((poly::real list => real => real) p a) (0::real)))
           ((Ex::(real list => bool) => bool)
             (%q::real list.
                 (op &::bool => bool => bool)
                  ((op =::(real => real) => (real => real) => bool)
                    ((poly::real list => real => real) p)
                    ((poly::real list => real => real)
                      ((poly_mul::real list => real list => real list)
                        ((op #::real => real list => real list)
                          ((uminus::real => real) a)
                          ((op #::real => real list => real list) (1::real)
                            ([]::real list)))
                        q)))
                  ((Not::bool => bool)
                    ((op =::real => real => bool)
                      ((poly::real list => real => real) q a)
                      (0::real)))))))"
  by (import poly RSQUAREFREE_DECOMP)

lemma POLY_SQUAREFREE_DECOMP: "(All::(real list => bool) => bool)
 (%p::real list.
     (All::(real list => bool) => bool)
      (%q::real list.
          (All::(real list => bool) => bool)
           (%d::real list.
               (All::(real list => bool) => bool)
                (%e::real list.
                    (All::(real list => bool) => bool)
                     (%r::real list.
                         (All::(real list => bool) => bool)
                          (%s::real list.
                              (op -->::bool => bool => bool)
                               ((op &::bool => bool => bool)
                                 ((Not::bool => bool)
                                   ((op =::(real => real)
     => (real => real) => bool)
                                     ((poly::real list => real => real)
 ((diff::real list => real list) p))
                                     ((poly::real list => real => real)
 ([]::real list))))
                                 ((op &::bool => bool => bool)
                                   ((op =::(real => real)
     => (real => real) => bool)
                                     ((poly::real list => real => real) p)
                                     ((poly::real list => real => real)
 ((poly_mul::real list => real list => real list) q d)))
                                   ((op &::bool => bool => bool)
                                     ((op =::(real => real)
       => (real => real) => bool)
 ((poly::real list => real => real) ((diff::real list => real list) p))
 ((poly::real list => real => real)
   ((poly_mul::real list => real list => real list) e d)))
                                     ((op =::(real => real)
       => (real => real) => bool)
 ((poly::real list => real => real) d)
 ((poly::real list => real => real)
   ((poly_add::real list => real list => real list)
     ((poly_mul::real list => real list => real list) r p)
     ((poly_mul::real list => real list => real list) s
       ((diff::real list => real list) p))))))))
                               ((op &::bool => bool => bool)
                                 ((rsquarefree::real list => bool) q)
                                 ((All::(real => bool) => bool)
                                   (%x::real.
 (op =::bool => bool => bool)
  ((op =::real => real => bool) ((poly::real list => real => real) q x)
    (0::real))
  ((op =::real => real => bool) ((poly::real list => real => real) p x)
    (0::real)))))))))))"
  by (import poly POLY_SQUAREFREE_DECOMP)

consts
  normalize :: "real list => real list" 

specification (normalize) normalize: "normalize [] = [] &
(ALL (h::real) t::real list.
    normalize (h # t) =
    (if normalize t = [] then if h = (0::real) then [] else [h]
     else h # normalize t))"
  by (import poly normalize)

lemma POLY_NORMALIZE: "ALL t::real list. poly (normalize t) = poly t"
  by (import poly POLY_NORMALIZE)

constdefs
  degree :: "real list => nat" 
  "degree == %p::real list. PRE (length (normalize p))"

lemma degree: "ALL p::real list. degree p = PRE (length (normalize p))"
  by (import poly degree)

lemma DEGREE_ZERO: "(All::(real list => bool) => bool)
 (%p::real list.
     (op -->::bool => bool => bool)
      ((op =::(real => real) => (real => real) => bool)
        ((poly::real list => real => real) p)
        ((poly::real list => real => real) ([]::real list)))
      ((op =::nat => nat => bool) ((degree::real list => nat) p) (0::nat)))"
  by (import poly DEGREE_ZERO)

lemma POLY_ROOTS_FINITE_SET: "(All::(real list => bool) => bool)
 (%p::real list.
     (op -->::bool => bool => bool)
      ((Not::bool => bool)
        ((op =::(real => real) => (real => real) => bool)
          ((poly::real list => real => real) p)
          ((poly::real list => real => real) ([]::real list))))
      ((FINITE::(real => bool) => bool)
        ((GSPEC::(real => real * bool) => real => bool)
          (%x::real.
              (Pair::real => bool => real * bool) x
               ((op =::real => real => bool)
                 ((poly::real list => real => real) p x) (0::real))))))"
  by (import poly POLY_ROOTS_FINITE_SET)

lemma POLY_MONO: "(All::(real => bool) => bool)
 (%x::real.
     (All::(real => bool) => bool)
      (%k::real.
          (All::(real list => bool) => bool)
           (%xa::real list.
               (op -->::bool => bool => bool)
                ((op <=::real => real => bool) ((abs::real => real) x) k)
                ((op <=::real => real => bool)
                  ((abs::real => real)
                    ((poly::real list => real => real) xa x))
                  ((poly::real list => real => real)
                    ((map::(real => real) => real list => real list)
                      (abs::real => real) xa)
                    k)))))"
  by (import poly POLY_MONO)

;end_setup

end

