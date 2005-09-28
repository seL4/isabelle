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

lemma REAL_0: "(op =::real => real => bool) (0::real) (0::real)"
  by (import real REAL_0)

lemma REAL_1: "(op =::real => real => bool) (1::real) (1::real)"
  by (import real REAL_1)

lemma REAL_ADD_LID_UNIQ: "ALL (x::real) y::real. (x + y = y) = (x = 0)"
  by (import real REAL_ADD_LID_UNIQ)

lemma REAL_ADD_RID_UNIQ: "ALL (x::real) y::real. (x + y = x) = (y = 0)"
  by (import real REAL_ADD_RID_UNIQ)

lemma REAL_LNEG_UNIQ: "ALL (x::real) y::real. (x + y = 0) = (x = - y)"
  by (import real REAL_LNEG_UNIQ)

lemma REAL_LT_ANTISYM: "ALL (x::real) y::real. ~ (x < y & y < x)"
  by (import real REAL_LT_ANTISYM)

lemma REAL_LTE_TOTAL: "ALL (x::real) y::real. x < y | y <= x"
  by (import real REAL_LTE_TOTAL)

lemma REAL_LET_ANTISYM: "ALL (x::real) y::real. ~ (x < y & y <= x)"
  by (import real REAL_LET_ANTISYM)

lemma REAL_LTE_ANTSYM: "ALL (x::real) y::real. ~ (x <= y & y < x)"
  by (import real REAL_LTE_ANTSYM)

lemma REAL_LT_NEGTOTAL: "ALL x::real. x = 0 | 0 < x | 0 < - x"
  by (import real REAL_LT_NEGTOTAL)

lemma REAL_LE_NEGTOTAL: "ALL x::real. 0 <= x | 0 <= - x"
  by (import real REAL_LE_NEGTOTAL)

lemma REAL_LT_ADDNEG: "ALL (x::real) (y::real) z::real. (y < x + - z) = (y + z < x)"
  by (import real REAL_LT_ADDNEG)

lemma REAL_LT_ADDNEG2: "ALL (x::real) (y::real) z::real. (x + - y < z) = (x < z + y)"
  by (import real REAL_LT_ADDNEG2)

lemma REAL_LT_ADD1: "ALL (x::real) y::real. x <= y --> x < y + 1"
  by (import real REAL_LT_ADD1)

lemma REAL_SUB_ADD2: "ALL (x::real) y::real. y + (x - y) = x"
  by (import real REAL_SUB_ADD2)

lemma REAL_SUB_LT: "ALL (x::real) y::real. (0 < x - y) = (y < x)"
  by (import real REAL_SUB_LT)

lemma REAL_SUB_LE: "ALL (x::real) y::real. (0 <= x - y) = (y <= x)"
  by (import real REAL_SUB_LE)

lemma REAL_ADD_SUB: "ALL (x::real) y::real. x + y - x = y"
  by (import real REAL_ADD_SUB)

lemma REAL_NEG_EQ: "ALL (x::real) y::real. (- x = y) = (x = - y)"
  by (import real REAL_NEG_EQ)

lemma REAL_NEG_MINUS1: "ALL x::real. - x = - 1 * x"
  by (import real REAL_NEG_MINUS1)

lemma REAL_LT_LMUL_0: "ALL (x::real) y::real. 0 < x --> (0 < x * y) = (0 < y)"
  by (import real REAL_LT_LMUL_0)

lemma REAL_LT_RMUL_0: "ALL (x::real) y::real. 0 < y --> (0 < x * y) = (0 < x)"
  by (import real REAL_LT_RMUL_0)

lemma REAL_LT_LMUL: "ALL (x::real) (y::real) z::real. 0 < x --> (x * y < x * z) = (y < z)"
  by (import real REAL_LT_LMUL)

lemma REAL_LINV_UNIQ: "ALL (x::real) y::real. x * y = 1 --> x = inverse y"
  by (import real REAL_LINV_UNIQ)

lemma REAL_LE_INV: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op <=::real => real => bool) (0::real) x)
      ((op <=::real => real => bool) (0::real) ((inverse::real => real) x)))"
  by (import real REAL_LE_INV)

lemma REAL_LE_ADDR: "ALL (x::real) y::real. (x <= x + y) = (0 <= y)"
  by (import real REAL_LE_ADDR)

lemma REAL_LE_ADDL: "ALL (x::real) y::real. (y <= x + y) = (0 <= x)"
  by (import real REAL_LE_ADDL)

lemma REAL_LT_ADDR: "ALL (x::real) y::real. (x < x + y) = (0 < y)"
  by (import real REAL_LT_ADDR)

lemma REAL_LT_ADDL: "ALL (x::real) y::real. (y < x + y) = (0 < x)"
  by (import real REAL_LT_ADDL)

lemma REAL_LT_NZ: "ALL n::nat. (real n ~= 0) = (0 < real n)"
  by (import real REAL_LT_NZ)

lemma REAL_NZ_IMP_LT: "ALL n::nat. n ~= 0 --> 0 < real n"
  by (import real REAL_NZ_IMP_LT)

lemma REAL_LT_RDIV_0: "ALL (y::real) z::real. 0 < z --> (0 < y / z) = (0 < y)"
  by (import real REAL_LT_RDIV_0)

lemma REAL_LT_RDIV: "ALL (x::real) (y::real) z::real. 0 < z --> (x / z < y / z) = (x < y)"
  by (import real REAL_LT_RDIV)

lemma REAL_LT_FRACTION_0: "ALL (n::nat) d::real. n ~= 0 --> (0 < d / real n) = (0 < d)"
  by (import real REAL_LT_FRACTION_0)

lemma REAL_LT_MULTIPLE: "ALL (x::nat) xa::real. 1 < x --> (xa < real x * xa) = (0 < xa)"
  by (import real REAL_LT_MULTIPLE)

lemma REAL_LT_FRACTION: "ALL (n::nat) d::real. 1 < n --> (d / real n < d) = (0 < d)"
  by (import real REAL_LT_FRACTION)

lemma REAL_LT_HALF2: "ALL d::real. (d / 2 < d) = (0 < d)"
  by (import real REAL_LT_HALF2)

lemma REAL_DIV_LMUL: "ALL (x::real) y::real. y ~= 0 --> y * (x / y) = x"
  by (import real REAL_DIV_LMUL)

lemma REAL_DIV_RMUL: "ALL (x::real) y::real. y ~= 0 --> x / y * y = x"
  by (import real REAL_DIV_RMUL)

lemma REAL_DOWN: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op <::real => real => bool) (0::real) x)
      ((Ex::(real => bool) => bool)
        (%xa::real.
            (op &::bool => bool => bool)
             ((op <::real => real => bool) (0::real) xa)
             ((op <::real => real => bool) xa x))))"
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
   x ~= 0 & y ~= 0 --> inverse (x * y) = inverse x * inverse y"
  by (import real REAL_INV_MUL)

lemma REAL_SUB_INV2: "ALL (x::real) y::real.
   x ~= 0 & y ~= 0 --> inverse x - inverse y = (y - x) / (x * y)"
  by (import real REAL_SUB_INV2)

lemma REAL_SUB_SUB2: "ALL (x::real) y::real. x - (x - y) = y"
  by (import real REAL_SUB_SUB2)

lemma REAL_ADD_SUB2: "ALL (x::real) y::real. x - (x + y) = - y"
  by (import real REAL_ADD_SUB2)

lemma REAL_LE_MUL2: "ALL (x1::real) (x2::real) (y1::real) y2::real.
   0 <= x1 & 0 <= y1 & x1 <= x2 & y1 <= y2 --> x1 * y1 <= x2 * y2"
  by (import real REAL_LE_MUL2)

lemma REAL_LE_DIV: "ALL (x::real) xa::real. 0 <= x & 0 <= xa --> 0 <= x / xa"
  by (import real REAL_LE_DIV)

lemma REAL_LT_1: "ALL (x::real) y::real. 0 <= x & x < y --> x / y < 1"
  by (import real REAL_LT_1)

lemma REAL_POS_NZ: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op <::real => real => bool) (0::real) x)
      ((Not::bool => bool) ((op =::real => real => bool) x (0::real))))"
  by (import real REAL_POS_NZ)

lemma REAL_EQ_LMUL_IMP: "ALL (x::real) (xa::real) xb::real. x ~= 0 & x * xa = x * xb --> xa = xb"
  by (import real REAL_EQ_LMUL_IMP)

lemma REAL_FACT_NZ: "ALL n::nat. real (FACT n) ~= 0"
  by (import real REAL_FACT_NZ)

lemma REAL_DIFFSQ: "ALL (x::real) y::real. (x + y) * (x - y) = x * x - y * y"
  by (import real REAL_DIFFSQ)

lemma REAL_POASQ: "ALL x::real. (0 < x * x) = (x ~= 0)"
  by (import real REAL_POASQ)

lemma REAL_SUMSQ: "ALL (x::real) y::real. (x * x + y * y = 0) = (x = 0 & y = 0)"
  by (import real REAL_SUMSQ)

lemma REAL_DIV_MUL2: "ALL (x::real) z::real.
   x ~= 0 & z ~= 0 --> (ALL y::real. y / z = x * y / (x * z))"
  by (import real REAL_DIV_MUL2)

lemma REAL_MIDDLE1: "ALL (a::real) b::real. a <= b --> a <= (a + b) / 2"
  by (import real REAL_MIDDLE1)

lemma REAL_MIDDLE2: "ALL (a::real) b::real. a <= b --> (a + b) / 2 <= b"
  by (import real REAL_MIDDLE2)

lemma ABS_LT_MUL2: "ALL (w::real) (x::real) (y::real) z::real.
   abs w < y & abs x < z --> abs (w * x) < y * z"
  by (import real ABS_LT_MUL2)

lemma ABS_REFL: "ALL x::real. (abs x = x) = (0 <= x)"
  by (import real ABS_REFL)

lemma ABS_BETWEEN: "ALL (x::real) (y::real) d::real.
   (0 < d & x - d < y & y < x + d) = (abs (y - x) < d)"
  by (import real ABS_BETWEEN)

lemma ABS_BOUND: "ALL (x::real) (y::real) d::real. abs (x - y) < d --> y < x + d"
  by (import real ABS_BOUND)

lemma ABS_STILLNZ: "ALL (x::real) y::real. abs (x - y) < abs y --> x ~= 0"
  by (import real ABS_STILLNZ)

lemma ABS_CASES: "ALL x::real. x = 0 | 0 < abs x"
  by (import real ABS_CASES)

lemma ABS_BETWEEN1: "ALL (x::real) (y::real) z::real. x < z & abs (y - x) < z - x --> y < z"
  by (import real ABS_BETWEEN1)

lemma ABS_SIGN: "ALL (x::real) y::real. abs (x - y) < y --> 0 < x"
  by (import real ABS_SIGN)

lemma ABS_SIGN2: "ALL (x::real) y::real. abs (x - y) < - y --> x < 0"
  by (import real ABS_SIGN2)

lemma ABS_CIRCLE: "ALL (x::real) (y::real) h::real.
   abs h < abs y - abs x --> abs (x + h) < abs y"
  by (import real ABS_CIRCLE)

lemma ABS_BETWEEN2: "ALL (x0::real) (x::real) (y0::real) y::real.
   x0 < y0 & abs (x - x0) < (y0 - x0) / 2 & abs (y - y0) < (y0 - x0) / 2 -->
   x < y"
  by (import real ABS_BETWEEN2)

lemma POW_PLUS1: "ALL e>0. ALL n::nat. 1 + real n * e <= (1 + e) ^ n"
  by (import real POW_PLUS1)

lemma POW_M1: "(All::(nat => bool) => bool)
 (%n::nat.
     (op =::real => real => bool)
      ((abs::real => real)
        ((op ^::real => nat => real) ((uminus::real => real) (1::real)) n))
      (1::real))"
  by (import real POW_M1)

lemma REAL_LE1_POW2: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op <=::real => real => bool) (1::real) x)
      ((op <=::real => real => bool) (1::real)
        ((op ^::real => nat => real) x
          ((number_of::bin => nat)
            ((op BIT::bin => bit => bin)
              ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
              (bit.B0::bit))))))"
  by (import real REAL_LE1_POW2)

lemma REAL_LT1_POW2: "(All::(real => bool) => bool)
 (%x::real.
     (op -->::bool => bool => bool)
      ((op <::real => real => bool) (1::real) x)
      ((op <::real => real => bool) (1::real)
        ((op ^::real => nat => real) x
          ((number_of::bin => nat)
            ((op BIT::bin => bit => bin)
              ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
              (bit.B0::bit))))))"
  by (import real REAL_LT1_POW2)

lemma POW_POS_LT: "ALL (x::real) n::nat. 0 < x --> 0 < x ^ Suc n"
  by (import real POW_POS_LT)

lemma POW_LT: "ALL (n::nat) (x::real) y::real. 0 <= x & x < y --> x ^ Suc n < y ^ Suc n"
  by (import real POW_LT)

lemma POW_ZERO_EQ: "ALL (n::nat) x::real. (x ^ Suc n = 0) = (x = 0)"
  by (import real POW_ZERO_EQ)

lemma REAL_POW_LT2: "ALL (n::nat) (x::real) y::real. n ~= 0 & 0 <= x & x < y --> x ^ n < y ^ n"
  by (import real REAL_POW_LT2)

lemma REAL_POW_MONO_LT: "ALL (m::nat) (n::nat) x::real. 1 < x & m < n --> x ^ m < x ^ n"
  by (import real REAL_POW_MONO_LT)

lemma REAL_SUP_SOMEPOS: "ALL P::real => bool.
   (EX x::real. P x & 0 < x) & (EX z::real. ALL x::real. P x --> x < z) -->
   (EX s::real. ALL y::real. (EX x::real. P x & y < x) = (y < s))"
  by (import real REAL_SUP_SOMEPOS)

lemma SUP_LEMMA1: "ALL (P::real => bool) (s::real) d::real.
   (ALL y::real. (EX x::real. P (x + d) & y < x) = (y < s)) -->
   (ALL y::real. (EX x::real. P x & y < x) = (y < s + d))"
  by (import real SUP_LEMMA1)

lemma SUP_LEMMA2: "ALL P::real => bool. Ex P --> (EX (d::real) x::real. P (x + d) & 0 < x)"
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

lemma REAL_ARCH_LEAST: "ALL y>0. ALL x>=0. EX n::nat. real n * y <= x & x < real (Suc n) * y"
  by (import real REAL_ARCH_LEAST)

consts
  sumc :: "nat => nat => (nat => real) => real" 

specification (sumc) sumc: "(ALL (n::nat) f::nat => real. sumc n 0 f = 0) &
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
   real.sum (xa, 0) x = 0 &
   real.sum (xa, Suc xb) x = real.sum (xa, xb) x + x (xa + xb)"
  by (import real sum)

lemma SUM_TWO: "ALL (f::nat => real) (n::nat) p::nat.
   real.sum (0, n) f + real.sum (n, p) f = real.sum (0, n + p) f"
  by (import real SUM_TWO)

lemma SUM_DIFF: "ALL (f::nat => real) (m::nat) n::nat.
   real.sum (m, n) f = real.sum (0, m + n) f - real.sum (0, m) f"
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
   (ALL n::nat. 0 <= f n) --> (ALL (m::nat) n::nat. 0 <= real.sum (m, n) f)"
  by (import real SUM_POS)

lemma SUM_POS_GEN: "ALL (f::nat => real) m::nat.
   (ALL n::nat. m <= n --> 0 <= f n) -->
   (ALL n::nat. 0 <= real.sum (m, n) f)"
  by (import real SUM_POS_GEN)

lemma SUM_ABS: "ALL (f::nat => real) (m::nat) x::nat.
   abs (real.sum (m, x) (%m::nat. abs (f m))) =
   real.sum (m, x) (%m::nat. abs (f m))"
  by (import real SUM_ABS)

lemma SUM_ABS_LE: "ALL (f::nat => real) (m::nat) n::nat.
   abs (real.sum (m, n) f) <= real.sum (m, n) (%n::nat. abs (f n))"
  by (import real SUM_ABS_LE)

lemma SUM_ZERO: "ALL (f::nat => real) N::nat.
   (ALL n::nat. N <= n --> f n = 0) -->
   (ALL (m::nat) n::nat. N <= m --> real.sum (m, n) f = 0)"
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
   real.sum (0, n) f - real n * c = real.sum (0, n) (%p::nat. f p - c)"
  by (import real SUM_NSUB)

lemma SUM_BOUND: "ALL (f::nat => real) (k::real) (m::nat) n::nat.
   (ALL p::nat. m <= p & p < m + n --> f p <= k) -->
   real.sum (m, n) f <= real n * k"
  by (import real SUM_BOUND)

lemma SUM_GROUP: "ALL (n::nat) (k::nat) f::nat => real.
   real.sum (0, n) (%m::nat. real.sum (m * k, k) f) = real.sum (0, n * k) f"
  by (import real SUM_GROUP)

lemma SUM_1: "ALL (f::nat => real) n::nat. real.sum (n, 1) f = f n"
  by (import real SUM_1)

lemma SUM_2: "ALL (f::nat => real) n::nat. real.sum (n, 2) f = f n + f (n + 1)"
  by (import real SUM_2)

lemma SUM_OFFSET: "ALL (f::nat => real) (n::nat) k::nat.
   real.sum (0, n) (%m::nat. f (m + k)) =
   real.sum (0, n + k) f - real.sum (0, k) f"
  by (import real SUM_OFFSET)

lemma SUM_REINDEX: "ALL (f::nat => real) (m::nat) (k::nat) n::nat.
   real.sum (m + k, n) f = real.sum (m, n) (%r::nat. f (r + k))"
  by (import real SUM_REINDEX)

lemma SUM_0: "ALL (m::nat) n::nat. real.sum (m, n) (%r::nat. 0) = 0"
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

lemma REAL_EQ_RDIV_EQ: "ALL (x::real) (xa::real) xb::real. 0 < xb --> (x = xa / xb) = (x * xb = xa)"
  by (import real REAL_EQ_RDIV_EQ)

lemma REAL_EQ_LDIV_EQ: "ALL (x::real) (xa::real) xb::real. 0 < xb --> (x / xb = xa) = (x = xa * xb)"
  by (import real REAL_EQ_LDIV_EQ)

;end_setup

;setup_theory topology

constdefs
  re_Union :: "(('a => bool) => bool) => 'a => bool" 
  "re_Union ==
%(P::('a::type => bool) => bool) x::'a::type.
   EX s::'a::type => bool. P s & s x"

lemma re_Union: "ALL P::('a::type => bool) => bool.
   re_Union P = (%x::'a::type. EX s::'a::type => bool. P s & s x)"
  by (import topology re_Union)

constdefs
  re_union :: "('a => bool) => ('a => bool) => 'a => bool" 
  "re_union ==
%(P::'a::type => bool) (Q::'a::type => bool) x::'a::type. P x | Q x"

lemma re_union: "ALL (P::'a::type => bool) Q::'a::type => bool.
   re_union P Q = (%x::'a::type. P x | Q x)"
  by (import topology re_union)

constdefs
  re_intersect :: "('a => bool) => ('a => bool) => 'a => bool" 
  "re_intersect ==
%(P::'a::type => bool) (Q::'a::type => bool) x::'a::type. P x & Q x"

lemma re_intersect: "ALL (P::'a::type => bool) Q::'a::type => bool.
   re_intersect P Q = (%x::'a::type. P x & Q x)"
  by (import topology re_intersect)

constdefs
  re_null :: "'a => bool" 
  "re_null == %x::'a::type. False"

lemma re_null: "re_null = (%x::'a::type. False)"
  by (import topology re_null)

constdefs
  re_universe :: "'a => bool" 
  "re_universe == %x::'a::type. True"

lemma re_universe: "re_universe = (%x::'a::type. True)"
  by (import topology re_universe)

constdefs
  re_subset :: "('a => bool) => ('a => bool) => bool" 
  "re_subset ==
%(P::'a::type => bool) Q::'a::type => bool. ALL x::'a::type. P x --> Q x"

lemma re_subset: "ALL (P::'a::type => bool) Q::'a::type => bool.
   re_subset P Q = (ALL x::'a::type. P x --> Q x)"
  by (import topology re_subset)

constdefs
  re_compl :: "('a => bool) => 'a => bool" 
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
  istopology :: "(('a => bool) => bool) => bool" 
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
  topology :: "(('a => bool) => bool) => 'a topology" 
  "open" :: "'a topology => ('a => bool) => bool" 

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
  neigh :: "'a topology => ('a => bool) * 'a => bool" 
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
  closed :: "'a topology => ('a => bool) => bool" 
  "closed == %(L::'a::type topology) S'::'a::type => bool. open L (re_compl S')"

lemma closed: "ALL (L::'a::type topology) S'::'a::type => bool.
   closed L S' = open L (re_compl S')"
  by (import topology closed)

constdefs
  limpt :: "'a topology => 'a => ('a => bool) => bool" 
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
  ismet :: "('a * 'a => real) => bool" 
  "ismet ==
%m::'a::type * 'a::type => real.
   (ALL (x::'a::type) y::'a::type. (m (x, y) = 0) = (x = y)) &
   (ALL (x::'a::type) (y::'a::type) z::'a::type.
       m (y, z) <= m (x, y) + m (x, z))"

lemma ismet: "ALL m::'a::type * 'a::type => real.
   ismet m =
   ((ALL (x::'a::type) y::'a::type. (m (x, y) = 0) = (x = y)) &
    (ALL (x::'a::type) (y::'a::type) z::'a::type.
        m (y, z) <= m (x, y) + m (x, z)))"
  by (import topology ismet)

typedef (open) ('a) metric = "(Collect::(('a::type * 'a::type => real) => bool)
          => ('a::type * 'a::type => real) set)
 (ismet::('a::type * 'a::type => real) => bool)" 
  by (rule typedef_helper,import topology metric_TY_DEF)

lemmas metric_TY_DEF = typedef_hol2hol4 [OF type_definition_metric]

consts
  metric :: "('a * 'a => real) => 'a metric" 
  dist :: "'a metric => 'a * 'a => real" 

specification (dist metric) metric_tybij: "(ALL a::'a::type metric. metric (dist a) = a) &
(ALL r::'a::type * 'a::type => real. ismet r = (dist (metric r) = r))"
  by (import topology metric_tybij)

lemma METRIC_ISMET: "ALL m::'a::type metric. ismet (dist m)"
  by (import topology METRIC_ISMET)

lemma METRIC_ZERO: "ALL (m::'a::type metric) (x::'a::type) y::'a::type.
   (dist m (x, y) = 0) = (x = y)"
  by (import topology METRIC_ZERO)

lemma METRIC_SAME: "ALL (m::'a::type metric) x::'a::type. dist m (x, x) = 0"
  by (import topology METRIC_SAME)

lemma METRIC_POS: "ALL (m::'a::type metric) (x::'a::type) y::'a::type. 0 <= dist m (x, y)"
  by (import topology METRIC_POS)

lemma METRIC_SYM: "ALL (m::'a::type metric) (x::'a::type) y::'a::type.
   dist m (x, y) = dist m (y, x)"
  by (import topology METRIC_SYM)

lemma METRIC_TRIANGLE: "ALL (m::'a::type metric) (x::'a::type) (y::'a::type) z::'a::type.
   dist m (x, z) <= dist m (x, y) + dist m (y, z)"
  by (import topology METRIC_TRIANGLE)

lemma METRIC_NZ: "ALL (m::'a::type metric) (x::'a::type) y::'a::type.
   x ~= y --> 0 < dist m (x, y)"
  by (import topology METRIC_NZ)

constdefs
  mtop :: "'a metric => 'a topology" 
  "mtop ==
%m::'a::type metric.
   topology
    (%S'::'a::type => bool.
        ALL x::'a::type.
           S' x --> (EX e>0. ALL y::'a::type. dist m (x, y) < e --> S' y))"

lemma mtop: "ALL m::'a::type metric.
   mtop m =
   topology
    (%S'::'a::type => bool.
        ALL x::'a::type.
           S' x --> (EX e>0. ALL y::'a::type. dist m (x, y) < e --> S' y))"
  by (import topology mtop)

lemma mtop_istopology: "ALL m::'a::type metric.
   istopology
    (%S'::'a::type => bool.
        ALL x::'a::type.
           S' x --> (EX e>0. ALL y::'a::type. dist m (x, y) < e --> S' y))"
  by (import topology mtop_istopology)

lemma MTOP_OPEN: "ALL (S'::'a::type => bool) x::'a::type metric.
   open (mtop x) S' =
   (ALL xa::'a::type.
       S' xa --> (EX e>0. ALL y::'a::type. dist x (xa, y) < e --> S' y))"
  by (import topology MTOP_OPEN)

constdefs
  B :: "'a metric => 'a * real => 'a => bool" 
  "B ==
%(m::'a::type metric) (x::'a::type, e::real) y::'a::type. dist m (x, y) < e"

lemma ball: "ALL (m::'a::type metric) (x::'a::type) e::real.
   B m (x, e) = (%y::'a::type. dist m (x, y) < e)"
  by (import topology ball)

lemma BALL_OPEN: "ALL (m::'a::type metric) (x::'a::type) e::real.
   0 < e --> open (mtop m) (B m (x, e))"
  by (import topology BALL_OPEN)

lemma BALL_NEIGH: "ALL (m::'a::type metric) (x::'a::type) e::real.
   0 < e --> neigh (mtop m) (B m (x, e), x)"
  by (import topology BALL_NEIGH)

lemma MTOP_LIMPT: "ALL (m::'a::type metric) (x::'a::type) S'::'a::type => bool.
   limpt (mtop m) x S' =
   (ALL e>0. EX y::'a::type. x ~= y & S' y & dist m (x, y) < e)"
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

lemma MR1_ADD_POS: "ALL (x::real) d::real. 0 <= d --> dist mr1 (x, x + d) = d"
  by (import topology MR1_ADD_POS)

lemma MR1_SUB_LE: "ALL (x::real) d::real. 0 <= d --> dist mr1 (x, x - d) = d"
  by (import topology MR1_SUB_LE)

lemma MR1_ADD_LT: "ALL (x::real) d::real. 0 < d --> dist mr1 (x, x + d) = d"
  by (import topology MR1_ADD_LT)

lemma MR1_SUB_LT: "ALL (x::real) d::real. 0 < d --> dist mr1 (x, x - d) = d"
  by (import topology MR1_SUB_LT)

lemma MR1_BETWEEN1: "ALL (x::real) (y::real) z::real. x < z & dist mr1 (x, y) < z - x --> y < z"
  by (import topology MR1_BETWEEN1)

lemma MR1_LIMPT: "ALL x::real. limpt (mtop mr1) x re_universe"
  by (import topology MR1_LIMPT)

;end_setup

;setup_theory nets

constdefs
  dorder :: "('a => 'a => bool) => bool" 
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
  tends :: "('b => 'a) => 'a => 'a topology * ('b => 'b => bool) => bool" 
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
  bounded :: "'a metric * ('b => 'b => bool) => ('b => 'a) => bool" 
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
  tendsto :: "'a metric * 'a => 'a => 'a => bool" 
  "tendsto ==
%(m::'a::type metric, x::'a::type) (y::'a::type) z::'a::type.
   0 < dist m (x, y) & dist m (x, y) <= dist m (x, z)"

lemma tendsto: "ALL (m::'a::type metric) (x::'a::type) (y::'a::type) z::'a::type.
   tendsto (m, x) y z = (0 < dist m (x, y) & dist m (x, y) <= dist m (x, z))"
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
   (ALL e>0.
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
   (ALL xa>0. EX xb::nat. ALL xc::nat. xb <= xc --> dist d (x xc, x0) < xa)"
  by (import nets SEQ_TENDS)

lemma LIM_TENDS: "ALL (m1::'a::type metric) (m2::'b::type metric) (f::'a::type => 'b::type)
   (x0::'a::type) y0::'b::type.
   limpt (mtop m1) x0 re_universe -->
   tends f y0 (mtop m2, tendsto (m1, x0)) =
   (ALL e>0.
       EX d>0.
          ALL x::'a::type.
             0 < dist m1 (x, x0) & dist m1 (x, x0) <= d -->
             dist m2 (f x, y0) < e)"
  by (import nets LIM_TENDS)

lemma LIM_TENDS2: "ALL (m1::'a::type metric) (m2::'b::type metric) (f::'a::type => 'b::type)
   (x0::'a::type) y0::'b::type.
   limpt (mtop m1) x0 re_universe -->
   tends f y0 (mtop m2, tendsto (m1, x0)) =
   (ALL e>0.
       EX d>0.
          ALL x::'a::type.
             0 < dist m1 (x, x0) & dist m1 (x, x0) < d -->
             dist m2 (f x, y0) < e)"
  by (import nets LIM_TENDS2)

lemma MR1_BOUNDED: "ALL (g::'a::type => 'a::type => bool) f::'a::type => real.
   bounded (mr1, g) f =
   (EX (k::real) N::'a::type.
       g N N & (ALL n::'a::type. g n N --> abs (f n) < k))"
  by (import nets MR1_BOUNDED)

lemma NET_NULL: "ALL (g::'a::type => 'a::type => bool) (x::'a::type => real) x0::real.
   tends x x0 (mtop mr1, g) = tends (%n::'a::type. x n - x0) 0 (mtop mr1, g)"
  by (import nets NET_NULL)

lemma NET_CONV_BOUNDED: "ALL (g::'a::type => 'a::type => bool) (x::'a::type => real) x0::real.
   tends x x0 (mtop mr1, g) --> bounded (mr1, g) x"
  by (import nets NET_CONV_BOUNDED)

lemma NET_CONV_NZ: "ALL (g::'a::type => 'a::type => bool) (x::'a::type => real) x0::real.
   tends x x0 (mtop mr1, g) & x0 ~= 0 -->
   (EX N::'a::type. g N N & (ALL n::'a::type. g n N --> x n ~= 0))"
  by (import nets NET_CONV_NZ)

lemma NET_CONV_IBOUNDED: "ALL (g::'a::type => 'a::type => bool) (x::'a::type => real) x0::real.
   tends x x0 (mtop mr1, g) & x0 ~= 0 -->
   bounded (mr1, g) (%n::'a::type. inverse (x n))"
  by (import nets NET_CONV_IBOUNDED)

lemma NET_NULL_ADD: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) y::'a::type => real.
       tends x 0 (mtop mr1, g) & tends y 0 (mtop mr1, g) -->
       tends (%n::'a::type. x n + y n) 0 (mtop mr1, g))"
  by (import nets NET_NULL_ADD)

lemma NET_NULL_MUL: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) y::'a::type => real.
       bounded (mr1, g) x & tends y 0 (mtop mr1, g) -->
       tends (%n::'a::type. x n * y n) 0 (mtop mr1, g))"
  by (import nets NET_NULL_MUL)

lemma NET_NULL_CMUL: "ALL (g::'a::type => 'a::type => bool) (k::real) x::'a::type => real.
   tends x 0 (mtop mr1, g) --> tends (%n::'a::type. k * x n) 0 (mtop mr1, g)"
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
       tends x x0 (mtop mr1, g) & x0 ~= 0 -->
       tends (%n::'a::type. inverse (x n)) (inverse x0) (mtop mr1, g))"
  by (import nets NET_INV)

lemma NET_DIV: "ALL g::'a::type => 'a::type => bool.
   dorder g -->
   (ALL (x::'a::type => real) (x0::real) (y::'a::type => real) y0::real.
       tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) & y0 ~= 0 -->
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
  "hol4-->" :: "(nat => real) => real => bool" ("hol4-->")

defs
  "hol4-->_def": "hol4--> == %(x::nat => real) x0::real. tends x x0 (mtop mr1, nat_ge)"

lemma tends_num_real: "ALL (x::nat => real) x0::real. hol4--> x x0 = tends x x0 (mtop mr1, nat_ge)"
  by (import seq tends_num_real)

lemma SEQ: "ALL (x::nat => real) x0::real.
   hol4--> x x0 =
   (ALL e>0. EX N::nat. ALL n::nat. N <= n --> abs (x n - x0) < e)"
  by (import seq SEQ)

lemma SEQ_CONST: "ALL k::real. hol4--> (%x::nat. k) k"
  by (import seq SEQ_CONST)

lemma SEQ_ADD: "ALL (x::nat => real) (x0::real) (y::nat => real) y0::real.
   hol4--> x x0 & hol4--> y y0 --> hol4--> (%n::nat. x n + y n) (x0 + y0)"
  by (import seq SEQ_ADD)

lemma SEQ_MUL: "ALL (x::nat => real) (x0::real) (y::nat => real) y0::real.
   hol4--> x x0 & hol4--> y y0 --> hol4--> (%n::nat. x n * y n) (x0 * y0)"
  by (import seq SEQ_MUL)

lemma SEQ_NEG: "ALL (x::nat => real) x0::real.
   hol4--> x x0 = hol4--> (%n::nat. - x n) (- x0)"
  by (import seq SEQ_NEG)

lemma SEQ_INV: "ALL (x::nat => real) x0::real.
   hol4--> x x0 & x0 ~= 0 --> hol4--> (%n::nat. inverse (x n)) (inverse x0)"
  by (import seq SEQ_INV)

lemma SEQ_SUB: "ALL (x::nat => real) (x0::real) (y::nat => real) y0::real.
   hol4--> x x0 & hol4--> y y0 --> hol4--> (%n::nat. x n - y n) (x0 - y0)"
  by (import seq SEQ_SUB)

lemma SEQ_DIV: "ALL (x::nat => real) (x0::real) (y::nat => real) y0::real.
   hol4--> x x0 & hol4--> y y0 & y0 ~= 0 -->
   hol4--> (%n::nat. x n / y n) (x0 / y0)"
  by (import seq SEQ_DIV)

lemma SEQ_UNIQ: "ALL (x::nat => real) (x1::real) x2::real.
   hol4--> x x1 & hol4--> x x2 --> x1 = x2"
  by (import seq SEQ_UNIQ)

constdefs
  convergent :: "(nat => real) => bool" 
  "convergent == %f::nat => real. Ex (hol4--> f)"

lemma convergent: "ALL f::nat => real. convergent f = Ex (hol4--> f)"
  by (import seq convergent)

constdefs
  cauchy :: "(nat => real) => bool" 
  "cauchy ==
%f::nat => real.
   ALL e>0.
      EX N::nat.
         ALL (m::nat) n::nat. N <= m & N <= n --> abs (f m - f n) < e"

lemma cauchy: "ALL f::nat => real.
   cauchy f =
   (ALL e>0.
       EX N::nat.
          ALL (m::nat) n::nat. N <= m & N <= n --> abs (f m - f n) < e)"
  by (import seq cauchy)

constdefs
  lim :: "(nat => real) => real" 
  "lim == %f::nat => real. Eps (hol4--> f)"

lemma lim: "ALL f::nat => real. lim f = Eps (hol4--> f)"
  by (import seq lim)

lemma SEQ_LIM: "ALL f::nat => real. convergent f = hol4--> f (lim f)"
  by (import seq SEQ_LIM)

constdefs
  subseq :: "(nat => nat) => bool" 
  "subseq == %f::nat => nat. ALL (m::nat) n::nat. m < n --> f m < f n"

lemma subseq: "ALL f::nat => nat. subseq f = (ALL (m::nat) n::nat. m < n --> f m < f n)"
  by (import seq subseq)

lemma SUBSEQ_SUC: "ALL f::nat => nat. subseq f = (ALL n::nat. f n < f (Suc n))"
  by (import seq SUBSEQ_SUC)

consts
  mono :: "(nat => real) => bool" 

defs
  mono_def: "seq.mono ==
%f::nat => real.
   (ALL (m::nat) n::nat. m <= n --> f m <= f n) |
   (ALL (m::nat) n::nat. m <= n --> f n <= f m)"

lemma mono: "ALL f::nat => real.
   seq.mono f =
   ((ALL (m::nat) n::nat. m <= n --> f m <= f n) |
    (ALL (m::nat) n::nat. m <= n --> f n <= f m))"
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

lemma SEQ_BOUNDED_2: "ALL (f::nat => real) (k::real) k'::real.
   (ALL n::nat. k <= f n & f n <= k') --> bounded (mr1, nat_ge) f"
  by (import seq SEQ_BOUNDED_2)

lemma SEQ_CBOUNDED: "ALL f::nat => real. cauchy f --> bounded (mr1, nat_ge) f"
  by (import seq SEQ_CBOUNDED)

lemma SEQ_ICONV: "ALL f::nat => real.
   bounded (mr1, nat_ge) f &
   (ALL (m::nat) n::nat. n <= m --> f n <= f m) -->
   convergent f"
  by (import seq SEQ_ICONV)

lemma SEQ_NEG_CONV: "ALL f::nat => real. convergent f = convergent (%n::nat. - f n)"
  by (import seq SEQ_NEG_CONV)

lemma SEQ_NEG_BOUNDED: "ALL f::nat => real.
   bounded (mr1, nat_ge) (%n::nat. - f n) = bounded (mr1, nat_ge) f"
  by (import seq SEQ_NEG_BOUNDED)

lemma SEQ_BCONV: "ALL f::nat => real. bounded (mr1, nat_ge) f & seq.mono f --> convergent f"
  by (import seq SEQ_BCONV)

lemma SEQ_MONOSUB: "ALL s::nat => real. EX f::nat => nat. subseq f & seq.mono (%n::nat. s (f n))"
  by (import seq SEQ_MONOSUB)

lemma SEQ_SBOUNDED: "ALL (s::nat => real) f::nat => nat.
   bounded (mr1, nat_ge) s --> bounded (mr1, nat_ge) (%n::nat. s (f n))"
  by (import seq SEQ_SBOUNDED)

lemma SEQ_SUBLE: "ALL f::nat => nat. subseq f --> (ALL n::nat. n <= f n)"
  by (import seq SEQ_SUBLE)

lemma SEQ_DIRECT: "ALL f::nat => nat.
   subseq f --> (ALL (N1::nat) N2::nat. EX x::nat. N1 <= x & N2 <= f x)"
  by (import seq SEQ_DIRECT)

lemma SEQ_CAUCHY: "ALL f::nat => real. cauchy f = convergent f"
  by (import seq SEQ_CAUCHY)

lemma SEQ_LE: "ALL (f::nat => real) (g::nat => real) (l::real) m::real.
   hol4--> f l &
   hol4--> g m & (EX x::nat. ALL xa::nat. x <= xa --> f xa <= g xa) -->
   l <= m"
  by (import seq SEQ_LE)

lemma SEQ_SUC: "ALL (f::nat => real) l::real. hol4--> f l = hol4--> (%n::nat. f (Suc n)) l"
  by (import seq SEQ_SUC)

lemma SEQ_ABS: "ALL f::nat => real. hol4--> (%n::nat. abs (f n)) 0 = hol4--> f 0"
  by (import seq SEQ_ABS)

lemma SEQ_ABS_IMP: "ALL (f::nat => real) l::real.
   hol4--> f l --> hol4--> (%n::nat. abs (f n)) (abs l)"
  by (import seq SEQ_ABS_IMP)

lemma SEQ_INV0: "ALL f::nat => real.
   (ALL y::real. EX N::nat. ALL n::nat. N <= n --> y < f n) -->
   hol4--> (%n::nat. inverse (f n)) 0"
  by (import seq SEQ_INV0)

lemma SEQ_POWER_ABS: "ALL c::real. abs c < 1 --> hol4--> (op ^ (abs c)) 0"
  by (import seq SEQ_POWER_ABS)

lemma SEQ_POWER: "ALL c::real. abs c < 1 --> hol4--> (op ^ c) 0"
  by (import seq SEQ_POWER)

lemma NEST_LEMMA: "ALL (f::nat => real) g::nat => real.
   (ALL n::nat. f n <= f (Suc n)) &
   (ALL n::nat. g (Suc n) <= g n) & (ALL n::nat. f n <= g n) -->
   (EX (l::real) m::real.
       l <= m &
       ((ALL n::nat. f n <= l) & hol4--> f l) &
       (ALL n::nat. m <= g n) & hol4--> g m)"
  by (import seq NEST_LEMMA)

lemma NEST_LEMMA_UNIQ: "ALL (f::nat => real) g::nat => real.
   (ALL n::nat. f n <= f (Suc n)) &
   (ALL n::nat. g (Suc n) <= g n) &
   (ALL n::nat. f n <= g n) & hol4--> (%n::nat. f n - g n) 0 -->
   (EX x::real.
       ((ALL n::nat. f n <= x) & hol4--> f x) &
       (ALL n::nat. x <= g n) & hol4--> g x)"
  by (import seq NEST_LEMMA_UNIQ)

lemma BOLZANO_LEMMA: "ALL P::real * real => bool.
   (ALL (a::real) (b::real) c::real.
       a <= b & b <= c & P (a, b) & P (b, c) --> P (a, c)) &
   (ALL x::real.
       EX d>0.
          ALL (a::real) b::real.
             a <= x & x <= b & b - a < d --> P (a, b)) -->
   (ALL (a::real) b::real. a <= b --> P (a, b))"
  by (import seq BOLZANO_LEMMA)

constdefs
  sums :: "(nat => real) => real => bool" 
  "sums == %f::nat => real. hol4--> (%n::nat. real.sum (0, n) f)"

lemma sums: "ALL (f::nat => real) s::real.
   sums f s = hol4--> (%n::nat. real.sum (0, n) f) s"
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

lemma SUM_SUMMABLE: "ALL (f::nat => real) l::real. sums f l --> summable f"
  by (import seq SUM_SUMMABLE)

lemma SUMMABLE_SUM: "ALL f::nat => real. summable f --> sums f (suminf f)"
  by (import seq SUMMABLE_SUM)

lemma SUM_UNIQ: "ALL (f::nat => real) x::real. sums f x --> x = suminf f"
  by (import seq SUM_UNIQ)

lemma SER_0: "ALL (f::nat => real) n::nat.
   (ALL m::nat. n <= m --> f m = 0) --> sums f (real.sum (0, n) f)"
  by (import seq SER_0)

lemma SER_POS_LE: "ALL (f::nat => real) n::nat.
   summable f & (ALL m::nat. n <= m --> 0 <= f m) -->
   real.sum (0, n) f <= suminf f"
  by (import seq SER_POS_LE)

lemma SER_POS_LT: "ALL (f::nat => real) n::nat.
   summable f & (ALL m::nat. n <= m --> 0 < f m) -->
   real.sum (0, n) f < suminf f"
  by (import seq SER_POS_LT)

lemma SER_GROUP: "ALL (f::nat => real) k::nat.
   summable f & 0 < k --> sums (%n::nat. real.sum (n * k, k) f) (suminf f)"
  by (import seq SER_GROUP)

lemma SER_PAIR: "ALL f::nat => real.
   summable f --> sums (%n::nat. real.sum (2 * n, 2) f) (suminf f)"
  by (import seq SER_PAIR)

lemma SER_OFFSET: "ALL f::nat => real.
   summable f -->
   (ALL k::nat. sums (%n::nat. f (n + k)) (suminf f - real.sum (0, k) f))"
  by (import seq SER_OFFSET)

lemma SER_POS_LT_PAIR: "ALL (f::nat => real) n::nat.
   summable f & (ALL d::nat. 0 < f (n + 2 * d) + f (n + (2 * d + 1))) -->
   real.sum (0, n) f < suminf f"
  by (import seq SER_POS_LT_PAIR)

lemma SER_ADD: "ALL (x::nat => real) (x0::real) (y::nat => real) y0::real.
   sums x x0 & sums y y0 --> sums (%n::nat. x n + y n) (x0 + y0)"
  by (import seq SER_ADD)

lemma SER_CMUL: "ALL (x::nat => real) (x0::real) c::real.
   sums x x0 --> sums (%n::nat. c * x n) (c * x0)"
  by (import seq SER_CMUL)

lemma SER_NEG: "ALL (x::nat => real) x0::real. sums x x0 --> sums (%xa::nat. - x xa) (- x0)"
  by (import seq SER_NEG)

lemma SER_SUB: "ALL (x::nat => real) (x0::real) (y::nat => real) y0::real.
   sums x x0 & sums y y0 --> sums (%xa::nat. x xa - y xa) (x0 - y0)"
  by (import seq SER_SUB)

lemma SER_CDIV: "ALL (x::nat => real) (x0::real) c::real.
   sums x x0 --> sums (%xa::nat. x xa / c) (x0 / c)"
  by (import seq SER_CDIV)

lemma SER_CAUCHY: "ALL f::nat => real.
   summable f =
   (ALL e>0.
       EX N::nat.
          ALL (m::nat) n::nat. N <= m --> abs (real.sum (m, n) f) < e)"
  by (import seq SER_CAUCHY)

lemma SER_ZERO: "ALL f::nat => real. summable f --> hol4--> f 0"
  by (import seq SER_ZERO)

lemma SER_COMPAR: "ALL (f::nat => real) g::nat => real.
   (EX x::nat. ALL xa::nat. x <= xa --> abs (f xa) <= g xa) & summable g -->
   summable f"
  by (import seq SER_COMPAR)

lemma SER_COMPARA: "ALL (f::nat => real) g::nat => real.
   (EX x::nat. ALL xa::nat. x <= xa --> abs (f xa) <= g xa) & summable g -->
   summable (%k::nat. abs (f k))"
  by (import seq SER_COMPARA)

lemma SER_LE: "ALL (f::nat => real) g::nat => real.
   (ALL n::nat. f n <= g n) & summable f & summable g -->
   suminf f <= suminf g"
  by (import seq SER_LE)

lemma SER_LE2: "ALL (f::nat => real) g::nat => real.
   (ALL n::nat. abs (f n) <= g n) & summable g -->
   summable f & suminf f <= suminf g"
  by (import seq SER_LE2)

lemma SER_ACONV: "ALL f::nat => real. summable (%n::nat. abs (f n)) --> summable f"
  by (import seq SER_ACONV)

lemma SER_ABS: "ALL f::nat => real.
   summable (%n::nat. abs (f n)) -->
   abs (suminf f) <= suminf (%n::nat. abs (f n))"
  by (import seq SER_ABS)

lemma GP_FINITE: "ALL x::real.
   x ~= 1 --> (ALL n::nat. real.sum (0, n) (op ^ x) = (x ^ n - 1) / (x - 1))"
  by (import seq GP_FINITE)

lemma GP: "ALL x::real. abs x < 1 --> sums (op ^ x) (inverse (1 - x))"
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

lemma SER_RATIO: "ALL (f::nat => real) (c::real) N::nat.
   c < 1 & (ALL n::nat. N <= n --> abs (f (Suc n)) <= c * abs (f n)) -->
   summable f"
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

lemma LIM: "ALL (f::real => real) (y0::real) x0::real.
   tends_real_real f y0 x0 =
   (ALL e>0.
       EX d>0.
          ALL x::real.
             0 < abs (x - x0) & abs (x - x0) < d --> abs (f x - y0) < e)"
  by (import lim LIM)

lemma LIM_CONST: "ALL k::real. All (tends_real_real (%x::real. k) k)"
  by (import lim LIM_CONST)

lemma LIM_ADD: "ALL (f::real => real) (g::real => real) (l::real) (m::real) x::real.
   tends_real_real f l x & tends_real_real g m x -->
   tends_real_real (%x::real. f x + g x) (l + m) x"
  by (import lim LIM_ADD)

lemma LIM_MUL: "ALL (f::real => real) (g::real => real) (l::real) (m::real) x::real.
   tends_real_real f l x & tends_real_real g m x -->
   tends_real_real (%x::real. f x * g x) (l * m) x"
  by (import lim LIM_MUL)

lemma LIM_NEG: "ALL (f::real => real) (l::real) x::real.
   tends_real_real f l x = tends_real_real (%x::real. - f x) (- l) x"
  by (import lim LIM_NEG)

lemma LIM_INV: "ALL (f::real => real) (l::real) x::real.
   tends_real_real f l x & l ~= 0 -->
   tends_real_real (%x::real. inverse (f x)) (inverse l) x"
  by (import lim LIM_INV)

lemma LIM_SUB: "ALL (f::real => real) (g::real => real) (l::real) (m::real) x::real.
   tends_real_real f l x & tends_real_real g m x -->
   tends_real_real (%x::real. f x - g x) (l - m) x"
  by (import lim LIM_SUB)

lemma LIM_DIV: "ALL (f::real => real) (g::real => real) (l::real) (m::real) x::real.
   tends_real_real f l x & tends_real_real g m x & m ~= 0 -->
   tends_real_real (%x::real. f x / g x) (l / m) x"
  by (import lim LIM_DIV)

lemma LIM_NULL: "ALL (f::real => real) (l::real) x::real.
   tends_real_real f l x = tends_real_real (%x::real. f x - l) 0 x"
  by (import lim LIM_NULL)

lemma LIM_X: "ALL x0::real. tends_real_real (%x::real. x) x0 x0"
  by (import lim LIM_X)

lemma LIM_UNIQ: "ALL (f::real => real) (l::real) (m::real) x::real.
   tends_real_real f l x & tends_real_real f m x --> l = m"
  by (import lim LIM_UNIQ)

lemma LIM_EQUAL: "ALL (f::real => real) (g::real => real) (l::real) x0::real.
   (ALL x::real. x ~= x0 --> f x = g x) -->
   tends_real_real f l x0 = tends_real_real g l x0"
  by (import lim LIM_EQUAL)

lemma LIM_TRANSFORM: "ALL (f::real => real) (g::real => real) (x0::real) l::real.
   tends_real_real (%x::real. f x - g x) 0 x0 & tends_real_real g l x0 -->
   tends_real_real f l x0"
  by (import lim LIM_TRANSFORM)

constdefs
  diffl :: "(real => real) => real => real => bool" 
  "diffl ==
%(f::real => real) (l::real) x::real.
   tends_real_real (%h::real. (f (x + h) - f x) / h) l 0"

lemma diffl: "ALL (f::real => real) (l::real) x::real.
   diffl f l x = tends_real_real (%h::real. (f (x + h) - f x) / h) l 0"
  by (import lim diffl)

constdefs
  contl :: "(real => real) => real => bool" 
  "contl ==
%(f::real => real) x::real. tends_real_real (%h::real. f (x + h)) (f x) 0"

lemma contl: "ALL (f::real => real) x::real.
   contl f x = tends_real_real (%h::real. f (x + h)) (f x) 0"
  by (import lim contl)

constdefs
  differentiable :: "(real => real) => real => bool" 
  "differentiable == %(f::real => real) x::real. EX l::real. diffl f l x"

lemma differentiable: "ALL (f::real => real) x::real.
   differentiable f x = (EX l::real. diffl f l x)"
  by (import lim differentiable)

lemma DIFF_UNIQ: "ALL (f::real => real) (l::real) (m::real) x::real.
   diffl f l x & diffl f m x --> l = m"
  by (import lim DIFF_UNIQ)

lemma DIFF_CONT: "ALL (f::real => real) (l::real) x::real. diffl f l x --> contl f x"
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

lemma CONT_ADD: "ALL (f::real => real) (g::real => real) x::real.
   contl f x & contl g x --> contl (%x::real. f x + g x) x"
  by (import lim CONT_ADD)

lemma CONT_MUL: "ALL (f::real => real) (g::real => real) x::real.
   contl f x & contl g x --> contl (%x::real. f x * g x) x"
  by (import lim CONT_MUL)

lemma CONT_NEG: "ALL (f::real => real) x::real. contl f x --> contl (%x::real. - f x) x"
  by (import lim CONT_NEG)

lemma CONT_INV: "ALL (f::real => real) x::real.
   contl f x & f x ~= 0 --> contl (%x::real. inverse (f x)) x"
  by (import lim CONT_INV)

lemma CONT_SUB: "ALL (f::real => real) (g::real => real) x::real.
   contl f x & contl g x --> contl (%x::real. f x - g x) x"
  by (import lim CONT_SUB)

lemma CONT_DIV: "ALL (f::real => real) (g::real => real) x::real.
   contl f x & contl g x & g x ~= 0 --> contl (%x::real. f x / g x) x"
  by (import lim CONT_DIV)

lemma CONT_COMPOSE: "ALL (f::real => real) (g::real => real) x::real.
   contl f x & contl g (f x) --> contl (%x::real. g (f x)) x"
  by (import lim CONT_COMPOSE)

lemma IVT: "ALL (f::real => real) (a::real) (b::real) y::real.
   a <= b &
   (f a <= y & y <= f b) & (ALL x::real. a <= x & x <= b --> contl f x) -->
   (EX x::real. a <= x & x <= b & f x = y)"
  by (import lim IVT)

lemma IVT2: "ALL (f::real => real) (a::real) (b::real) y::real.
   a <= b &
   (f b <= y & y <= f a) & (ALL x::real. a <= x & x <= b --> contl f x) -->
   (EX x::real. a <= x & x <= b & f x = y)"
  by (import lim IVT2)

lemma DIFF_CONST: "ALL k::real. All (diffl (%x::real. k) 0)"
  by (import lim DIFF_CONST)

lemma DIFF_ADD: "ALL (f::real => real) (g::real => real) (l::real) (m::real) x::real.
   diffl f l x & diffl g m x --> diffl (%x::real. f x + g x) (l + m) x"
  by (import lim DIFF_ADD)

lemma DIFF_MUL: "ALL (f::real => real) (g::real => real) (l::real) (m::real) x::real.
   diffl f l x & diffl g m x -->
   diffl (%x::real. f x * g x) (l * g x + m * f x) x"
  by (import lim DIFF_MUL)

lemma DIFF_CMUL: "ALL (f::real => real) (c::real) (l::real) x::real.
   diffl f l x --> diffl (%x::real. c * f x) (c * l) x"
  by (import lim DIFF_CMUL)

lemma DIFF_NEG: "ALL (f::real => real) (l::real) x::real.
   diffl f l x --> diffl (%x::real. - f x) (- l) x"
  by (import lim DIFF_NEG)

lemma DIFF_SUB: "ALL (f::real => real) (g::real => real) (l::real) (m::real) x::real.
   diffl f l x & diffl g m x --> diffl (%x::real. f x - g x) (l - m) x"
  by (import lim DIFF_SUB)

lemma DIFF_CHAIN: "ALL (f::real => real) (g::real => real) (l::real) (m::real) x::real.
   diffl f l (g x) & diffl g m x --> diffl (%x::real. f (g x)) (l * m) x"
  by (import lim DIFF_CHAIN)

lemma DIFF_X: "All (diffl (%x::real. x) 1)"
  by (import lim DIFF_X)

lemma DIFF_POW: "ALL (n::nat) x::real. diffl (%x::real. x ^ n) (real n * x ^ (n - 1)) x"
  by (import lim DIFF_POW)

lemma DIFF_XM1: "ALL x::real. x ~= 0 --> diffl inverse (- (inverse x ^ 2)) x"
  by (import lim DIFF_XM1)

lemma DIFF_INV: "ALL (f::real => real) (l::real) x::real.
   diffl f l x & f x ~= 0 -->
   diffl (%x::real. inverse (f x)) (- (l / f x ^ 2)) x"
  by (import lim DIFF_INV)

lemma DIFF_DIV: "ALL (f::real => real) (g::real => real) (l::real) (m::real) x::real.
   diffl f l x & diffl g m x & g x ~= 0 -->
   diffl (%x::real. f x / g x) ((l * g x - m * f x) / g x ^ 2) x"
  by (import lim DIFF_DIV)

lemma DIFF_SUM: "ALL (f::nat => real => real) (f'::nat => real => real) (m::nat) (n::nat)
   x::real.
   (ALL r::nat. m <= r & r < m + n --> diffl (f r) (f' r x) x) -->
   diffl (%x::real. real.sum (m, n) (%n::nat. f n x))
    (real.sum (m, n) (%r::nat. f' r x)) x"
  by (import lim DIFF_SUM)

lemma CONT_BOUNDED: "ALL (f::real => real) (a::real) b::real.
   a <= b & (ALL x::real. a <= x & x <= b --> contl f x) -->
   (EX M::real. ALL x::real. a <= x & x <= b --> f x <= M)"
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

lemma CONT_ATTAINS: "ALL (f::real => real) (a::real) b::real.
   a <= b & (ALL x::real. a <= x & x <= b --> contl f x) -->
   (EX x::real.
       (ALL xa::real. a <= xa & xa <= b --> f xa <= x) &
       (EX xa::real. a <= xa & xa <= b & f xa = x))"
  by (import lim CONT_ATTAINS)

lemma CONT_ATTAINS2: "ALL (f::real => real) (a::real) b::real.
   a <= b & (ALL x::real. a <= x & x <= b --> contl f x) -->
   (EX x::real.
       (ALL xa::real. a <= xa & xa <= b --> x <= f xa) &
       (EX xa::real. a <= xa & xa <= b & f xa = x))"
  by (import lim CONT_ATTAINS2)

lemma CONT_ATTAINS_ALL: "ALL (f::real => real) (a::real) b::real.
   a <= b & (ALL x::real. a <= x & x <= b --> contl f x) -->
   (EX (x::real) M::real.
       x <= M &
       (ALL y::real.
           x <= y & y <= M --> (EX x::real. a <= x & x <= b & f x = y)) &
       (ALL xa::real. a <= xa & xa <= b --> x <= f xa & f xa <= M))"
  by (import lim CONT_ATTAINS_ALL)

lemma DIFF_LINC: "ALL (f::real => real) (x::real) l::real.
   diffl f l x & 0 < l -->
   (EX d>0. ALL h::real. 0 < h & h < d --> f x < f (x + h))"
  by (import lim DIFF_LINC)

lemma DIFF_LDEC: "ALL (f::real => real) (x::real) l::real.
   diffl f l x & l < 0 -->
   (EX d>0. ALL h::real. 0 < h & h < d --> f x < f (x - h))"
  by (import lim DIFF_LDEC)

lemma DIFF_LMAX: "ALL (f::real => real) (x::real) l::real.
   diffl f l x & (EX d>0. ALL y::real. abs (x - y) < d --> f y <= f x) -->
   l = 0"
  by (import lim DIFF_LMAX)

lemma DIFF_LMIN: "ALL (f::real => real) (x::real) l::real.
   diffl f l x & (EX d>0. ALL y::real. abs (x - y) < d --> f x <= f y) -->
   l = 0"
  by (import lim DIFF_LMIN)

lemma DIFF_LCONST: "ALL (f::real => real) (x::real) l::real.
   diffl f l x & (EX d>0. ALL y::real. abs (x - y) < d --> f y = f x) -->
   l = 0"
  by (import lim DIFF_LCONST)

lemma INTERVAL_LEMMA: "ALL (a::real) (b::real) x::real.
   a < x & x < b -->
   (EX d>0. ALL y::real. abs (x - y) < d --> a <= y & y <= b)"
  by (import lim INTERVAL_LEMMA)

lemma ROLLE: "ALL (f::real => real) (a::real) b::real.
   a < b &
   f a = f b &
   (ALL x::real. a <= x & x <= b --> contl f x) &
   (ALL x::real. a < x & x < b --> differentiable f x) -->
   (EX z::real. a < z & z < b & diffl f 0 z)"
  by (import lim ROLLE)

lemma MVT_LEMMA: "ALL (f::real => real) (a::real) b::real.
   f a - (f b - f a) / (b - a) * a = f b - (f b - f a) / (b - a) * b"
  by (import lim MVT_LEMMA)

lemma MVT: "ALL (f::real => real) (a::real) b::real.
   a < b &
   (ALL x::real. a <= x & x <= b --> contl f x) &
   (ALL x::real. a < x & x < b --> differentiable f x) -->
   (EX (l::real) z::real.
       a < z & z < b & diffl f l z & f b - f a = (b - a) * l)"
  by (import lim MVT)

lemma DIFF_ISCONST_END: "ALL (f::real => real) (a::real) b::real.
   a < b &
   (ALL x::real. a <= x & x <= b --> contl f x) &
   (ALL x::real. a < x & x < b --> diffl f 0 x) -->
   f b = f a"
  by (import lim DIFF_ISCONST_END)

lemma DIFF_ISCONST: "ALL (f::real => real) (a::real) b::real.
   a < b &
   (ALL x::real. a <= x & x <= b --> contl f x) &
   (ALL x::real. a < x & x < b --> diffl f 0 x) -->
   (ALL x::real. a <= x & x <= b --> f x = f a)"
  by (import lim DIFF_ISCONST)

lemma DIFF_ISCONST_ALL: "ALL f::real => real. All (diffl f 0) --> (ALL (x::real) y::real. f x = f y)"
  by (import lim DIFF_ISCONST_ALL)

lemma INTERVAL_ABS: "ALL (x::real) (z::real) d::real.
   (x - d <= z & z <= x + d) = (abs (z - x) <= d)"
  by (import lim INTERVAL_ABS)

lemma CONT_INJ_LEMMA: "ALL (f::real => real) (g::real => real) (x::real) d::real.
   0 < d &
   (ALL z::real. abs (z - x) <= d --> g (f z) = z) &
   (ALL z::real. abs (z - x) <= d --> contl f z) -->
   ~ (ALL z::real. abs (z - x) <= d --> f z <= f x)"
  by (import lim CONT_INJ_LEMMA)

lemma CONT_INJ_LEMMA2: "ALL (f::real => real) (g::real => real) (x::real) d::real.
   0 < d &
   (ALL z::real. abs (z - x) <= d --> g (f z) = z) &
   (ALL z::real. abs (z - x) <= d --> contl f z) -->
   ~ (ALL z::real. abs (z - x) <= d --> f x <= f z)"
  by (import lim CONT_INJ_LEMMA2)

lemma CONT_INJ_RANGE: "ALL (f::real => real) (g::real => real) (x::real) d::real.
   0 < d &
   (ALL z::real. abs (z - x) <= d --> g (f z) = z) &
   (ALL z::real. abs (z - x) <= d --> contl f z) -->
   (EX e>0.
       ALL y::real.
          abs (y - f x) <= e --> (EX z::real. abs (z - x) <= d & f z = y))"
  by (import lim CONT_INJ_RANGE)

lemma CONT_INVERSE: "ALL (f::real => real) (g::real => real) (x::real) d::real.
   0 < d &
   (ALL z::real. abs (z - x) <= d --> g (f z) = z) &
   (ALL z::real. abs (z - x) <= d --> contl f z) -->
   contl g (f x)"
  by (import lim CONT_INVERSE)

lemma DIFF_INVERSE: "ALL (f::real => real) (g::real => real) (l::real) (x::real) d::real.
   0 < d &
   (ALL z::real. abs (z - x) <= d --> g (f z) = z) &
   (ALL z::real. abs (z - x) <= d --> contl f z) & diffl f l x & l ~= 0 -->
   diffl g (inverse l) (f x)"
  by (import lim DIFF_INVERSE)

lemma DIFF_INVERSE_LT: "ALL (f::real => real) (g::real => real) (l::real) (x::real) d::real.
   0 < d &
   (ALL z::real. abs (z - x) < d --> g (f z) = z) &
   (ALL z::real. abs (z - x) < d --> contl f z) & diffl f l x & l ~= 0 -->
   diffl g (inverse l) (f x)"
  by (import lim DIFF_INVERSE_LT)

lemma INTERVAL_CLEMMA: "ALL (a::real) (b::real) x::real.
   a < x & x < b -->
   (EX d>0. ALL y::real. abs (y - x) <= d --> a < y & y < b)"
  by (import lim INTERVAL_CLEMMA)

lemma DIFF_INVERSE_OPEN: "ALL (f::real => real) (g::real => real) (l::real) (a::real) (x::real)
   b::real.
   a < x &
   x < b &
   (ALL z::real. a < z & z < b --> g (f z) = z & contl f z) &
   diffl f l x & l ~= 0 -->
   diffl g (inverse l) (f x)"
  by (import lim DIFF_INVERSE_OPEN)

;end_setup

;setup_theory powser

lemma POWDIFF_LEMMA: "ALL (n::nat) (x::real) y::real.
   real.sum (0, Suc n) (%p::nat. x ^ p * y ^ (Suc n - p)) =
   y * real.sum (0, Suc n) (%p::nat. x ^ p * y ^ (n - p))"
  by (import powser POWDIFF_LEMMA)

lemma POWDIFF: "ALL (n::nat) (x::real) y::real.
   x ^ Suc n - y ^ Suc n =
   (x - y) * real.sum (0, Suc n) (%p::nat. x ^ p * y ^ (n - p))"
  by (import powser POWDIFF)

lemma POWREV: "ALL (n::nat) (x::real) y::real.
   real.sum (0, Suc n) (%xa::nat. x ^ xa * y ^ (n - xa)) =
   real.sum (0, Suc n) (%xa::nat. x ^ (n - xa) * y ^ xa)"
  by (import powser POWREV)

lemma POWSER_INSIDEA: "ALL (f::nat => real) (x::real) z::real.
   summable (%n::nat. f n * x ^ n) & abs z < abs x -->
   summable (%n::nat. abs (f n) * z ^ n)"
  by (import powser POWSER_INSIDEA)

lemma POWSER_INSIDE: "ALL (f::nat => real) (x::real) z::real.
   summable (%n::nat. f n * x ^ n) & abs z < abs x -->
   summable (%n::nat. f n * z ^ n)"
  by (import powser POWSER_INSIDE)

constdefs
  diffs :: "(nat => real) => nat => real" 
  "diffs == %(c::nat => real) n::nat. real (Suc n) * c (Suc n)"

lemma diffs: "ALL c::nat => real. diffs c = (%n::nat. real (Suc n) * c (Suc n))"
  by (import powser diffs)

lemma DIFFS_NEG: "ALL c::nat => real. diffs (%n::nat. - c n) = (%x::nat. - diffs c x)"
  by (import powser DIFFS_NEG)

lemma DIFFS_LEMMA: "ALL (n::nat) (c::nat => real) x::real.
   real.sum (0, n) (%n::nat. diffs c n * x ^ n) =
   real.sum (0, n) (%n::nat. real n * (c n * x ^ (n - 1))) +
   real n * (c n * x ^ (n - 1))"
  by (import powser DIFFS_LEMMA)

lemma DIFFS_LEMMA2: "ALL (n::nat) (c::nat => real) x::real.
   real.sum (0, n) (%n::nat. real n * (c n * x ^ (n - 1))) =
   real.sum (0, n) (%n::nat. diffs c n * x ^ n) -
   real n * (c n * x ^ (n - 1))"
  by (import powser DIFFS_LEMMA2)

lemma DIFFS_EQUIV: "ALL (c::nat => real) x::real.
   summable (%n::nat. diffs c n * x ^ n) -->
   sums (%n::nat. real n * (c n * x ^ (n - 1)))
    (suminf (%n::nat. diffs c n * x ^ n))"
  by (import powser DIFFS_EQUIV)

lemma TERMDIFF_LEMMA1: "ALL (m::nat) (z::real) h::real.
   real.sum (0, m) (%p::nat. (z + h) ^ (m - p) * z ^ p - z ^ m) =
   real.sum (0, m) (%p::nat. z ^ p * ((z + h) ^ (m - p) - z ^ (m - p)))"
  by (import powser TERMDIFF_LEMMA1)

lemma TERMDIFF_LEMMA2: "ALL (z::real) (h::real) n::nat.
   h ~= 0 -->
   ((z + h) ^ n - z ^ n) / h - real n * z ^ (n - 1) =
   h *
   real.sum (0, n - 1)
    (%p::nat.
        z ^ p *
        real.sum (0, n - 1 - p)
         (%q::nat. (z + h) ^ q * z ^ (n - 2 - p - q)))"
  by (import powser TERMDIFF_LEMMA2)

lemma TERMDIFF_LEMMA3: "ALL (z::real) (h::real) (n::nat) k'::real.
   h ~= 0 & abs z <= k' & abs (z + h) <= k' -->
   abs (((z + h) ^ n - z ^ n) / h - real n * z ^ (n - 1))
   <= real n * (real (n - 1) * (k' ^ (n - 2) * abs h))"
  by (import powser TERMDIFF_LEMMA3)

lemma TERMDIFF_LEMMA4: "ALL (f::real => real) (k'::real) k::real.
   0 < k &
   (ALL h::real. 0 < abs h & abs h < k --> abs (f h) <= k' * abs h) -->
   tends_real_real f 0 0"
  by (import powser TERMDIFF_LEMMA4)

lemma TERMDIFF_LEMMA5: "ALL (f::nat => real) (g::real => nat => real) k::real.
   0 < k &
   summable f &
   (ALL h::real.
       0 < abs h & abs h < k -->
       (ALL n::nat. abs (g h n) <= f n * abs h)) -->
   tends_real_real (%h::real. suminf (g h)) 0 0"
  by (import powser TERMDIFF_LEMMA5)

lemma TERMDIFF: "ALL (c::nat => real) (k'::real) x::real.
   summable (%n::nat. c n * k' ^ n) &
   summable (%n::nat. diffs c n * k' ^ n) &
   summable (%n::nat. diffs (diffs c) n * k' ^ n) & abs x < abs k' -->
   diffl (%x::real. suminf (%n::nat. c n * x ^ n))
    (suminf (%n::nat. diffs c n * x ^ n)) x"
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
  "cos ==
%x::real.
   suminf
    (%n::nat.
        (if EVEN n then (- 1) ^ (n div 2) / real (FACT n) else 0) * x ^ n)"

lemma cos: "ALL x::real.
   cos x =
   suminf
    (%n::nat.
        (if EVEN n then (- 1) ^ (n div 2) / real (FACT n) else 0) * x ^ n)"
  by (import transc cos)

constdefs
  sin :: "real => real" 
  "sin ==
%x::real.
   suminf
    (%n::nat.
        (if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)) *
        x ^ n)"

lemma sin: "ALL x::real.
   sin x =
   suminf
    (%n::nat.
        (if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)) *
        x ^ n)"
  by (import transc sin)

lemma EXP_CONVERGES: "ALL x::real. sums (%n::nat. inverse (real (FACT n)) * x ^ n) (exp x)"
  by (import transc EXP_CONVERGES)

lemma SIN_CONVERGES: "ALL x::real.
   sums
    (%n::nat.
        (if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)) *
        x ^ n)
    (sin x)"
  by (import transc SIN_CONVERGES)

lemma COS_CONVERGES: "ALL x::real.
   sums
    (%n::nat.
        (if EVEN n then (- 1) ^ (n div 2) / real (FACT n) else 0) * x ^ n)
    (cos x)"
  by (import transc COS_CONVERGES)

lemma EXP_FDIFF: "diffs (%n::nat. inverse (real (FACT n))) =
(%n::nat. inverse (real (FACT n)))"
  by (import transc EXP_FDIFF)

lemma SIN_FDIFF: "diffs
 (%n::nat. if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)) =
(%n::nat. if EVEN n then (- 1) ^ (n div 2) / real (FACT n) else 0)"
  by (import transc SIN_FDIFF)

lemma COS_FDIFF: "diffs (%n::nat. if EVEN n then (- 1) ^ (n div 2) / real (FACT n) else 0) =
(%n::nat. - (if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)))"
  by (import transc COS_FDIFF)

lemma SIN_NEGLEMMA: "ALL x::real.
   - sin x =
   suminf
    (%n::nat.
        - ((if EVEN n then 0 else (- 1) ^ ((n - 1) div 2) / real (FACT n)) *
           x ^ n))"
  by (import transc SIN_NEGLEMMA)

lemma DIFF_EXP: "ALL x::real. diffl exp (exp x) x"
  by (import transc DIFF_EXP)

lemma DIFF_SIN: "ALL x::real. diffl sin (cos x) x"
  by (import transc DIFF_SIN)

lemma DIFF_COS: "ALL x::real. diffl cos (- sin x) x"
  by (import transc DIFF_COS)

lemma DIFF_COMPOSITE: "(diffl (f::real => real) (l::real) (x::real) & f x ~= 0 -->
 diffl (%x::real. inverse (f x)) (- (l / f x ^ 2)) x) &
(diffl f l x & diffl (g::real => real) (m::real) x & g x ~= 0 -->
 diffl (%x::real. f x / g x) ((l * g x - m * f x) / g x ^ 2) x) &
(diffl f l x & diffl g m x --> diffl (%x::real. f x + g x) (l + m) x) &
(diffl f l x & diffl g m x -->
 diffl (%x::real. f x * g x) (l * g x + m * f x) x) &
(diffl f l x & diffl g m x --> diffl (%x::real. f x - g x) (l - m) x) &
(diffl f l x --> diffl (%x::real. - f x) (- l) x) &
(diffl g m x -->
 diffl (%x::real. g x ^ (n::nat)) (real n * g x ^ (n - 1) * m) x) &
(diffl g m x --> diffl (%x::real. exp (g x)) (exp (g x) * m) x) &
(diffl g m x --> diffl (%x::real. sin (g x)) (cos (g x) * m) x) &
(diffl g m x --> diffl (%x::real. cos (g x)) (- sin (g x) * m) x)"
  by (import transc DIFF_COMPOSITE)

lemma EXP_0: "exp 0 = 1"
  by (import transc EXP_0)

lemma EXP_LE_X: "ALL x>=0. 1 + x <= exp x"
  by (import transc EXP_LE_X)

lemma EXP_LT_1: "ALL x>0. 1 < exp x"
  by (import transc EXP_LT_1)

lemma EXP_ADD_MUL: "ALL (x::real) y::real. exp (x + y) * exp (- x) = exp y"
  by (import transc EXP_ADD_MUL)

lemma EXP_NEG_MUL: "ALL x::real. exp x * exp (- x) = 1"
  by (import transc EXP_NEG_MUL)

lemma EXP_NEG_MUL2: "ALL x::real. exp (- x) * exp x = 1"
  by (import transc EXP_NEG_MUL2)

lemma EXP_NEG: "ALL x::real. exp (- x) = inverse (exp x)"
  by (import transc EXP_NEG)

lemma EXP_ADD: "ALL (x::real) y::real. exp (x + y) = exp x * exp y"
  by (import transc EXP_ADD)

lemma EXP_POS_LE: "ALL x::real. 0 <= exp x"
  by (import transc EXP_POS_LE)

lemma EXP_NZ: "ALL x::real. exp x ~= 0"
  by (import transc EXP_NZ)

lemma EXP_POS_LT: "ALL x::real. 0 < exp x"
  by (import transc EXP_POS_LT)

lemma EXP_N: "ALL (n::nat) x::real. exp (real n * x) = exp x ^ n"
  by (import transc EXP_N)

lemma EXP_SUB: "ALL (x::real) y::real. exp (x - y) = exp x / exp y"
  by (import transc EXP_SUB)

lemma EXP_MONO_IMP: "ALL (x::real) y::real. x < y --> exp x < exp y"
  by (import transc EXP_MONO_IMP)

lemma EXP_MONO_LT: "ALL (x::real) y::real. (exp x < exp y) = (x < y)"
  by (import transc EXP_MONO_LT)

lemma EXP_MONO_LE: "ALL (x::real) y::real. (exp x <= exp y) = (x <= y)"
  by (import transc EXP_MONO_LE)

lemma EXP_INJ: "ALL (x::real) y::real. (exp x = exp y) = (x = y)"
  by (import transc EXP_INJ)

lemma EXP_TOTAL_LEMMA: "ALL y>=1. EX x>=0. x <= y - 1 & exp x = y"
  by (import transc EXP_TOTAL_LEMMA)

lemma EXP_TOTAL: "ALL y>0. EX x::real. exp x = y"
  by (import transc EXP_TOTAL)

constdefs
  ln :: "real => real" 
  "ln == %x::real. SOME u::real. exp u = x"

lemma ln: "ALL x::real. ln x = (SOME u::real. exp u = x)"
  by (import transc ln)

lemma LN_EXP: "ALL x::real. ln (exp x) = x"
  by (import transc LN_EXP)

lemma EXP_LN: "ALL x::real. (exp (ln x) = x) = (0 < x)"
  by (import transc EXP_LN)

lemma LN_MUL: "ALL (x::real) y::real. 0 < x & 0 < y --> ln (x * y) = ln x + ln y"
  by (import transc LN_MUL)

lemma LN_INJ: "ALL (x::real) y::real. 0 < x & 0 < y --> (ln x = ln y) = (x = y)"
  by (import transc LN_INJ)

lemma LN_1: "ln 1 = 0"
  by (import transc LN_1)

lemma LN_INV: "ALL x>0. ln (inverse x) = - ln x"
  by (import transc LN_INV)

lemma LN_DIV: "ALL (x::real) y::real. 0 < x & 0 < y --> ln (x / y) = ln x - ln y"
  by (import transc LN_DIV)

lemma LN_MONO_LT: "ALL (x::real) y::real. 0 < x & 0 < y --> (ln x < ln y) = (x < y)"
  by (import transc LN_MONO_LT)

lemma LN_MONO_LE: "ALL (x::real) y::real. 0 < x & 0 < y --> (ln x <= ln y) = (x <= y)"
  by (import transc LN_MONO_LE)

lemma LN_POW: "ALL (n::nat) x::real. 0 < x --> ln (x ^ n) = real n * ln x"
  by (import transc LN_POW)

lemma LN_LE: "ALL x>=0. ln (1 + x) <= x"
  by (import transc LN_LE)

lemma LN_LT_X: "ALL x>0. ln x < x"
  by (import transc LN_LT_X)

lemma LN_POS: "ALL x>=1. 0 <= ln x"
  by (import transc LN_POS)

constdefs
  root :: "nat => real => real" 
  "root == %(n::nat) x::real. SOME u::real. (0 < x --> 0 < u) & u ^ n = x"

lemma root: "ALL (n::nat) x::real.
   root n x = (SOME u::real. (0 < x --> 0 < u) & u ^ n = x)"
  by (import transc root)

constdefs
  sqrt :: "real => real" 
  "sqrt == root 2"

lemma sqrt: "ALL x::real. sqrt x = root 2 x"
  by (import transc sqrt)

lemma ROOT_LT_LEMMA: "ALL (n::nat) x::real. 0 < x --> exp (ln x / real (Suc n)) ^ Suc n = x"
  by (import transc ROOT_LT_LEMMA)

lemma ROOT_LN: "ALL (n::nat) x::real. 0 < x --> root (Suc n) x = exp (ln x / real (Suc n))"
  by (import transc ROOT_LN)

lemma ROOT_0: "ALL n::nat. root (Suc n) 0 = 0"
  by (import transc ROOT_0)

lemma ROOT_1: "ALL n::nat. root (Suc n) 1 = 1"
  by (import transc ROOT_1)

lemma ROOT_POS_LT: "ALL (n::nat) x::real. 0 < x --> 0 < root (Suc n) x"
  by (import transc ROOT_POS_LT)

lemma ROOT_POW_POS: "ALL (n::nat) x::real. 0 <= x --> root (Suc n) x ^ Suc n = x"
  by (import transc ROOT_POW_POS)

lemma POW_ROOT_POS: "ALL (n::nat) x::real. 0 <= x --> root (Suc n) (x ^ Suc n) = x"
  by (import transc POW_ROOT_POS)

lemma ROOT_POS: "ALL (n::nat) x::real. 0 <= x --> 0 <= root (Suc n) x"
  by (import transc ROOT_POS)

lemma ROOT_POS_UNIQ: "ALL (n::nat) (x::real) y::real.
   0 <= x & 0 <= y & y ^ Suc n = x --> root (Suc n) x = y"
  by (import transc ROOT_POS_UNIQ)

lemma ROOT_MUL: "ALL (n::nat) (x::real) y::real.
   0 <= x & 0 <= y -->
   root (Suc n) (x * y) = root (Suc n) x * root (Suc n) y"
  by (import transc ROOT_MUL)

lemma ROOT_INV: "ALL (n::nat) x::real.
   0 <= x --> root (Suc n) (inverse x) = inverse (root (Suc n) x)"
  by (import transc ROOT_INV)

lemma ROOT_DIV: "ALL (x::nat) (xa::real) xb::real.
   0 <= xa & 0 <= xb -->
   root (Suc x) (xa / xb) = root (Suc x) xa / root (Suc x) xb"
  by (import transc ROOT_DIV)

lemma ROOT_MONO_LE: "ALL (x::real) y::real.
   0 <= x & x <= y --> root (Suc (n::nat)) x <= root (Suc n) y"
  by (import transc ROOT_MONO_LE)

lemma SQRT_0: "sqrt 0 = 0"
  by (import transc SQRT_0)

lemma SQRT_1: "sqrt 1 = 1"
  by (import transc SQRT_1)

lemma SQRT_POS_LT: "ALL x>0. 0 < sqrt x"
  by (import transc SQRT_POS_LT)

lemma SQRT_POS_LE: "ALL x>=0. 0 <= sqrt x"
  by (import transc SQRT_POS_LE)

lemma SQRT_POW2: "ALL x::real. (sqrt x ^ 2 = x) = (0 <= x)"
  by (import transc SQRT_POW2)

lemma SQRT_POW_2: "ALL x>=0. sqrt x ^ 2 = x"
  by (import transc SQRT_POW_2)

lemma POW_2_SQRT: "0 <= (x::real) --> sqrt (x ^ 2) = x"
  by (import transc POW_2_SQRT)

lemma SQRT_POS_UNIQ: "ALL (x::real) xa::real. 0 <= x & 0 <= xa & xa ^ 2 = x --> sqrt x = xa"
  by (import transc SQRT_POS_UNIQ)

lemma SQRT_MUL: "ALL (x::real) xa::real.
   0 <= x & 0 <= xa --> sqrt (x * xa) = sqrt x * sqrt xa"
  by (import transc SQRT_MUL)

lemma SQRT_INV: "ALL x>=0. sqrt (inverse x) = inverse (sqrt x)"
  by (import transc SQRT_INV)

lemma SQRT_DIV: "ALL (x::real) xa::real.
   0 <= x & 0 <= xa --> sqrt (x / xa) = sqrt x / sqrt xa"
  by (import transc SQRT_DIV)

lemma SQRT_MONO_LE: "ALL (x::real) xa::real. 0 <= x & x <= xa --> sqrt x <= sqrt xa"
  by (import transc SQRT_MONO_LE)

lemma SQRT_EVEN_POW2: "ALL n::nat. EVEN n --> sqrt (2 ^ n) = 2 ^ (n div 2)"
  by (import transc SQRT_EVEN_POW2)

lemma REAL_DIV_SQRT: "ALL x>=0. x / sqrt x = sqrt x"
  by (import transc REAL_DIV_SQRT)

lemma SQRT_EQ: "ALL (x::real) y::real. x ^ 2 = y & 0 <= x --> x = sqrt y"
  by (import transc SQRT_EQ)

lemma SIN_0: "sin 0 = 0"
  by (import transc SIN_0)

lemma COS_0: "cos 0 = 1"
  by (import transc COS_0)

lemma SIN_CIRCLE: "ALL x::real. sin x ^ 2 + cos x ^ 2 = 1"
  by (import transc SIN_CIRCLE)

lemma SIN_BOUND: "ALL x::real. abs (sin x) <= 1"
  by (import transc SIN_BOUND)

lemma SIN_BOUNDS: "ALL x::real. - 1 <= sin x & sin x <= 1"
  by (import transc SIN_BOUNDS)

lemma COS_BOUND: "ALL x::real. abs (cos x) <= 1"
  by (import transc COS_BOUND)

lemma COS_BOUNDS: "ALL x::real. - 1 <= cos x & cos x <= 1"
  by (import transc COS_BOUNDS)

lemma SIN_COS_ADD: "ALL (x::real) y::real.
   (sin (x + y) - (sin x * cos y + cos x * sin y)) ^ 2 +
   (cos (x + y) - (cos x * cos y - sin x * sin y)) ^ 2 =
   0"
  by (import transc SIN_COS_ADD)

lemma SIN_COS_NEG: "ALL x::real. (sin (- x) + sin x) ^ 2 + (cos (- x) - cos x) ^ 2 = 0"
  by (import transc SIN_COS_NEG)

lemma SIN_ADD: "ALL (x::real) y::real. sin (x + y) = sin x * cos y + cos x * sin y"
  by (import transc SIN_ADD)

lemma COS_ADD: "ALL (x::real) y::real. cos (x + y) = cos x * cos y - sin x * sin y"
  by (import transc COS_ADD)

lemma SIN_NEG: "ALL x::real. sin (- x) = - sin x"
  by (import transc SIN_NEG)

lemma COS_NEG: "ALL x::real. cos (- x) = cos x"
  by (import transc COS_NEG)

lemma SIN_DOUBLE: "ALL x::real. sin (2 * x) = 2 * (sin x * cos x)"
  by (import transc SIN_DOUBLE)

lemma COS_DOUBLE: "ALL x::real. cos (2 * x) = cos x ^ 2 - sin x ^ 2"
  by (import transc COS_DOUBLE)

lemma SIN_PAIRED: "ALL x::real.
   sums (%n::nat. (- 1) ^ n / real (FACT (2 * n + 1)) * x ^ (2 * n + 1))
    (sin x)"
  by (import transc SIN_PAIRED)

lemma SIN_POS: "ALL x::real. 0 < x & x < 2 --> 0 < sin x"
  by (import transc SIN_POS)

lemma COS_PAIRED: "ALL x::real.
   sums (%n::nat. (- 1) ^ n / real (FACT (2 * n)) * x ^ (2 * n)) (cos x)"
  by (import transc COS_PAIRED)

lemma COS_2: "cos 2 < 0"
  by (import transc COS_2)

lemma COS_ISZERO: "EX! x::real. 0 <= x & x <= 2 & cos x = 0"
  by (import transc COS_ISZERO)

constdefs
  pi :: "real" 
  "pi == 2 * (SOME x::real. 0 <= x & x <= 2 & cos x = 0)"

lemma pi: "pi = 2 * (SOME x::real. 0 <= x & x <= 2 & cos x = 0)"
  by (import transc pi)

lemma PI2: "pi / 2 = (SOME x::real. 0 <= x & x <= 2 & cos x = 0)"
  by (import transc PI2)

lemma COS_PI2: "cos (pi / 2) = 0"
  by (import transc COS_PI2)

lemma PI2_BOUNDS: "0 < pi / 2 & pi / 2 < 2"
  by (import transc PI2_BOUNDS)

lemma PI_POS: "0 < pi"
  by (import transc PI_POS)

lemma SIN_PI2: "sin (pi / 2) = 1"
  by (import transc SIN_PI2)

lemma COS_PI: "cos pi = - 1"
  by (import transc COS_PI)

lemma SIN_PI: "sin pi = 0"
  by (import transc SIN_PI)

lemma SIN_COS: "ALL x::real. sin x = cos (pi / 2 - x)"
  by (import transc SIN_COS)

lemma COS_SIN: "ALL x::real. cos x = sin (pi / 2 - x)"
  by (import transc COS_SIN)

lemma SIN_PERIODIC_PI: "ALL x::real. sin (x + pi) = - sin x"
  by (import transc SIN_PERIODIC_PI)

lemma COS_PERIODIC_PI: "ALL x::real. cos (x + pi) = - cos x"
  by (import transc COS_PERIODIC_PI)

lemma SIN_PERIODIC: "ALL x::real. sin (x + 2 * pi) = sin x"
  by (import transc SIN_PERIODIC)

lemma COS_PERIODIC: "ALL x::real. cos (x + 2 * pi) = cos x"
  by (import transc COS_PERIODIC)

lemma COS_NPI: "ALL n::nat. cos (real n * pi) = (- 1) ^ n"
  by (import transc COS_NPI)

lemma SIN_NPI: "ALL n::nat. sin (real n * pi) = 0"
  by (import transc SIN_NPI)

lemma SIN_POS_PI2: "ALL x::real. 0 < x & x < pi / 2 --> 0 < sin x"
  by (import transc SIN_POS_PI2)

lemma COS_POS_PI2: "ALL x::real. 0 < x & x < pi / 2 --> 0 < cos x"
  by (import transc COS_POS_PI2)

lemma COS_POS_PI: "ALL x::real. - (pi / 2) < x & x < pi / 2 --> 0 < cos x"
  by (import transc COS_POS_PI)

lemma SIN_POS_PI: "ALL x::real. 0 < x & x < pi --> 0 < sin x"
  by (import transc SIN_POS_PI)

lemma COS_POS_PI2_LE: "ALL x::real. 0 <= x & x <= pi / 2 --> 0 <= cos x"
  by (import transc COS_POS_PI2_LE)

lemma COS_POS_PI_LE: "ALL x::real. - (pi / 2) <= x & x <= pi / 2 --> 0 <= cos x"
  by (import transc COS_POS_PI_LE)

lemma SIN_POS_PI2_LE: "ALL x::real. 0 <= x & x <= pi / 2 --> 0 <= sin x"
  by (import transc SIN_POS_PI2_LE)

lemma SIN_POS_PI_LE: "ALL x::real. 0 <= x & x <= pi --> 0 <= sin x"
  by (import transc SIN_POS_PI_LE)

lemma COS_TOTAL: "ALL y::real.
   - 1 <= y & y <= 1 --> (EX! x::real. 0 <= x & x <= pi & cos x = y)"
  by (import transc COS_TOTAL)

lemma SIN_TOTAL: "ALL y::real.
   - 1 <= y & y <= 1 -->
   (EX! x::real. - (pi / 2) <= x & x <= pi / 2 & sin x = y)"
  by (import transc SIN_TOTAL)

lemma COS_ZERO_LEMMA: "ALL x::real.
   0 <= x & cos x = 0 --> (EX n::nat. ~ EVEN n & x = real n * (pi / 2))"
  by (import transc COS_ZERO_LEMMA)

lemma SIN_ZERO_LEMMA: "ALL x::real.
   0 <= x & sin x = 0 --> (EX n::nat. EVEN n & x = real n * (pi / 2))"
  by (import transc SIN_ZERO_LEMMA)

lemma COS_ZERO: "ALL x::real.
   (cos x = 0) =
   ((EX n::nat. ~ EVEN n & x = real n * (pi / 2)) |
    (EX n::nat. ~ EVEN n & x = - (real n * (pi / 2))))"
  by (import transc COS_ZERO)

lemma SIN_ZERO: "ALL x::real.
   (sin x = 0) =
   ((EX n::nat. EVEN n & x = real n * (pi / 2)) |
    (EX n::nat. EVEN n & x = - (real n * (pi / 2))))"
  by (import transc SIN_ZERO)

constdefs
  tan :: "real => real" 
  "tan == %x::real. sin x / cos x"

lemma tan: "ALL x::real. tan x = sin x / cos x"
  by (import transc tan)

lemma TAN_0: "tan 0 = 0"
  by (import transc TAN_0)

lemma TAN_PI: "tan pi = 0"
  by (import transc TAN_PI)

lemma TAN_NPI: "ALL n::nat. tan (real n * pi) = 0"
  by (import transc TAN_NPI)

lemma TAN_NEG: "ALL x::real. tan (- x) = - tan x"
  by (import transc TAN_NEG)

lemma TAN_PERIODIC: "ALL x::real. tan (x + 2 * pi) = tan x"
  by (import transc TAN_PERIODIC)

lemma TAN_ADD: "ALL (x::real) y::real.
   cos x ~= 0 & cos y ~= 0 & cos (x + y) ~= 0 -->
   tan (x + y) = (tan x + tan y) / (1 - tan x * tan y)"
  by (import transc TAN_ADD)

lemma TAN_DOUBLE: "ALL x::real.
   cos x ~= 0 & cos (2 * x) ~= 0 -->
   tan (2 * x) = 2 * tan x / (1 - tan x ^ 2)"
  by (import transc TAN_DOUBLE)

lemma TAN_POS_PI2: "ALL x::real. 0 < x & x < pi / 2 --> 0 < tan x"
  by (import transc TAN_POS_PI2)

lemma DIFF_TAN: "ALL x::real. cos x ~= 0 --> diffl tan (inverse (cos x ^ 2)) x"
  by (import transc DIFF_TAN)

lemma TAN_TOTAL_LEMMA: "ALL y>0. EX x>0. x < pi / 2 & y < tan x"
  by (import transc TAN_TOTAL_LEMMA)

lemma TAN_TOTAL_POS: "ALL y>=0. EX x>=0. x < pi / 2 & tan x = y"
  by (import transc TAN_TOTAL_POS)

lemma TAN_TOTAL: "ALL y::real. EX! x::real. - (pi / 2) < x & x < pi / 2 & tan x = y"
  by (import transc TAN_TOTAL)

constdefs
  asn :: "real => real" 
  "asn == %y::real. SOME x::real. - (pi / 2) <= x & x <= pi / 2 & sin x = y"

lemma asn: "ALL y::real.
   asn y = (SOME x::real. - (pi / 2) <= x & x <= pi / 2 & sin x = y)"
  by (import transc asn)

constdefs
  acs :: "real => real" 
  "acs == %y::real. SOME x::real. 0 <= x & x <= pi & cos x = y"

lemma acs: "ALL y::real. acs y = (SOME x::real. 0 <= x & x <= pi & cos x = y)"
  by (import transc acs)

constdefs
  atn :: "real => real" 
  "atn == %y::real. SOME x::real. - (pi / 2) < x & x < pi / 2 & tan x = y"

lemma atn: "ALL y::real. atn y = (SOME x::real. - (pi / 2) < x & x < pi / 2 & tan x = y)"
  by (import transc atn)

lemma ASN: "ALL y::real.
   - 1 <= y & y <= 1 -->
   - (pi / 2) <= asn y & asn y <= pi / 2 & sin (asn y) = y"
  by (import transc ASN)

lemma ASN_SIN: "ALL y::real. - 1 <= y & y <= 1 --> sin (asn y) = y"
  by (import transc ASN_SIN)

lemma ASN_BOUNDS: "ALL y::real. - 1 <= y & y <= 1 --> - (pi / 2) <= asn y & asn y <= pi / 2"
  by (import transc ASN_BOUNDS)

lemma ASN_BOUNDS_LT: "ALL y::real. - 1 < y & y < 1 --> - (pi / 2) < asn y & asn y < pi / 2"
  by (import transc ASN_BOUNDS_LT)

lemma SIN_ASN: "ALL x::real. - (pi / 2) <= x & x <= pi / 2 --> asn (sin x) = x"
  by (import transc SIN_ASN)

lemma ACS: "ALL y::real.
   - 1 <= y & y <= 1 --> 0 <= acs y & acs y <= pi & cos (acs y) = y"
  by (import transc ACS)

lemma ACS_COS: "ALL y::real. - 1 <= y & y <= 1 --> cos (acs y) = y"
  by (import transc ACS_COS)

lemma ACS_BOUNDS: "ALL y::real. - 1 <= y & y <= 1 --> 0 <= acs y & acs y <= pi"
  by (import transc ACS_BOUNDS)

lemma ACS_BOUNDS_LT: "ALL y::real. - 1 < y & y < 1 --> 0 < acs y & acs y < pi"
  by (import transc ACS_BOUNDS_LT)

lemma COS_ACS: "ALL x::real. 0 <= x & x <= pi --> acs (cos x) = x"
  by (import transc COS_ACS)

lemma ATN: "ALL y::real. - (pi / 2) < atn y & atn y < pi / 2 & tan (atn y) = y"
  by (import transc ATN)

lemma ATN_TAN: "ALL x::real. tan (atn x) = x"
  by (import transc ATN_TAN)

lemma ATN_BOUNDS: "ALL x::real. - (pi / 2) < atn x & atn x < pi / 2"
  by (import transc ATN_BOUNDS)

lemma TAN_ATN: "ALL x::real. - (pi / 2) < x & x < pi / 2 --> atn (tan x) = x"
  by (import transc TAN_ATN)

lemma TAN_SEC: "ALL x::real. cos x ~= 0 --> 1 + tan x ^ 2 = inverse (cos x) ^ 2"
  by (import transc TAN_SEC)

lemma SIN_COS_SQ: "ALL x::real. 0 <= x & x <= pi --> sin x = sqrt (1 - cos x ^ 2)"
  by (import transc SIN_COS_SQ)

lemma COS_SIN_SQ: "ALL x::real. - (pi / 2) <= x & x <= pi / 2 --> cos x = sqrt (1 - sin x ^ 2)"
  by (import transc COS_SIN_SQ)

lemma COS_ATN_NZ: "ALL x::real. cos (atn x) ~= 0"
  by (import transc COS_ATN_NZ)

lemma COS_ASN_NZ: "ALL x::real. - 1 < x & x < 1 --> cos (asn x) ~= 0"
  by (import transc COS_ASN_NZ)

lemma SIN_ACS_NZ: "ALL x::real. - 1 < x & x < 1 --> sin (acs x) ~= 0"
  by (import transc SIN_ACS_NZ)

lemma COS_SIN_SQRT: "ALL x::real. 0 <= cos x --> cos x = sqrt (1 - sin x ^ 2)"
  by (import transc COS_SIN_SQRT)

lemma SIN_COS_SQRT: "ALL x::real. 0 <= sin x --> sin x = sqrt (1 - cos x ^ 2)"
  by (import transc SIN_COS_SQRT)

lemma DIFF_LN: "ALL x>0. diffl ln (inverse x) x"
  by (import transc DIFF_LN)

lemma DIFF_ASN_LEMMA: "ALL x::real. - 1 < x & x < 1 --> diffl asn (inverse (cos (asn x))) x"
  by (import transc DIFF_ASN_LEMMA)

lemma DIFF_ASN: "ALL x::real. - 1 < x & x < 1 --> diffl asn (inverse (sqrt (1 - x ^ 2))) x"
  by (import transc DIFF_ASN)

lemma DIFF_ACS_LEMMA: "ALL x::real. - 1 < x & x < 1 --> diffl acs (inverse (- sin (acs x))) x"
  by (import transc DIFF_ACS_LEMMA)

lemma DIFF_ACS: "ALL x::real. - 1 < x & x < 1 --> diffl acs (- inverse (sqrt (1 - x ^ 2))) x"
  by (import transc DIFF_ACS)

lemma DIFF_ATN: "ALL x::real. diffl atn (inverse (1 + x ^ 2)) x"
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
  "gauge == %(E::real => bool) g::real => real. ALL x::real. E x --> 0 < g x"

lemma gauge: "ALL (E::real => bool) g::real => real.
   gauge E g = (ALL x::real. E x --> 0 < g x)"
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
   real.sum (0, dsize D) (%n::nat. f (p n) * (D (Suc n) - D n))"

lemma rsum: "ALL (D::nat => real) (p::nat => real) f::real => real.
   rsum (D, p) f =
   real.sum (0, dsize D) (%n::nat. f (p n) * (D (Suc n) - D n))"
  by (import transc rsum)

constdefs
  Dint :: "real * real => (real => real) => real => bool" 
  "Dint ==
%(a::real, b::real) (f::real => real) k::real.
   ALL e>0.
      EX g::real => real.
         gauge (%x::real. a <= x & x <= b) g &
         (ALL (D::nat => real) p::nat => real.
             tdiv (a, b) (D, p) & fine g (D, p) -->
             abs (rsum (D, p) f - k) < e)"

lemma Dint: "ALL (a::real) (b::real) (f::real => real) k::real.
   Dint (a, b) f k =
   (ALL e>0.
       EX g::real => real.
          gauge (%x::real. a <= x & x <= b) g &
          (ALL (D::nat => real) p::nat => real.
              tdiv (a, b) (D, p) & fine g (D, p) -->
              abs (rsum (D, p) f - k) < e))"
  by (import transc Dint)

lemma DIVISION_0: "ALL (a::real) b::real. a = b --> dsize (%n::nat. if n = 0 then a else b) = 0"
  by (import transc DIVISION_0)

lemma DIVISION_1: "ALL (a::real) b::real. a < b --> dsize (%n::nat. if n = 0 then a else b) = 1"
  by (import transc DIVISION_1)

lemma DIVISION_SINGLE: "ALL (a::real) b::real.
   a <= b --> division (a, b) (%n::nat. if n = 0 then a else b)"
  by (import transc DIVISION_SINGLE)

lemma DIVISION_LHS: "ALL (D::nat => real) (a::real) b::real. division (a, b) D --> D 0 = a"
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

lemma DIVISION_RHS: "ALL (D::nat => real) (a::real) b::real.
   division (a, b) D --> D (dsize D) = b"
  by (import transc DIVISION_RHS)

lemma DIVISION_LT_GEN: "ALL (D::nat => real) (a::real) (b::real) (m::nat) n::nat.
   division (a, b) D & m < n & n <= dsize D --> D m < D n"
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

lemma DIVISION_LE: "ALL (D::nat => real) (a::real) b::real. division (a, b) D --> a <= b"
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

lemma DIVISION_EQ: "ALL (D::nat => real) (a::real) b::real.
   division (a, b) D --> (a = b) = (dsize D = 0)"
  by (import transc DIVISION_EQ)

lemma DIVISION_LBOUND: "ALL (D::nat => real) (a::real) b::real.
   division (a, b) D --> (ALL r::nat. a <= D r)"
  by (import transc DIVISION_LBOUND)

lemma DIVISION_LBOUND_LT: "ALL (D::nat => real) (a::real) b::real.
   division (a, b) D & dsize D ~= 0 --> (ALL n::nat. a < D (Suc n))"
  by (import transc DIVISION_LBOUND_LT)

lemma DIVISION_UBOUND: "ALL (D::nat => real) (a::real) b::real.
   division (a, b) D --> (ALL r::nat. D r <= b)"
  by (import transc DIVISION_UBOUND)

lemma DIVISION_UBOUND_LT: "ALL (D::nat => real) (a::real) (b::real) n::nat.
   division (a, b) D & n < dsize D --> D n < b"
  by (import transc DIVISION_UBOUND_LT)

lemma DIVISION_APPEND: "ALL (a::real) (b::real) c::real.
   (EX (D1::nat => real) p1::nat => real.
       tdiv (a, b) (D1, p1) & fine (g::real => real) (D1, p1)) &
   (EX (D2::nat => real) p2::nat => real.
       tdiv (b, c) (D2, p2) & fine g (D2, p2)) -->
   (EX (x::nat => real) p::nat => real. tdiv (a, c) (x, p) & fine g (x, p))"
  by (import transc DIVISION_APPEND)

lemma DIVISION_EXISTS: "ALL (a::real) (b::real) g::real => real.
   a <= b & gauge (%x::real. a <= x & x <= b) g -->
   (EX (D::nat => real) p::nat => real. tdiv (a, b) (D, p) & fine g (D, p))"
  by (import transc DIVISION_EXISTS)

lemma GAUGE_MIN: "ALL (E::real => bool) (g1::real => real) g2::real => real.
   gauge E g1 & gauge E g2 -->
   gauge E (%x::real. if g1 x < g2 x then g1 x else g2 x)"
  by (import transc GAUGE_MIN)

lemma FINE_MIN: "ALL (g1::real => real) (g2::real => real) (D::nat => real) p::nat => real.
   fine (%x::real. if g1 x < g2 x then g1 x else g2 x) (D, p) -->
   fine g1 (D, p) & fine g2 (D, p)"
  by (import transc FINE_MIN)

lemma DINT_UNIQ: "ALL (a::real) (b::real) (f::real => real) (k1::real) k2::real.
   a <= b & Dint (a, b) f k1 & Dint (a, b) f k2 --> k1 = k2"
  by (import transc DINT_UNIQ)

lemma INTEGRAL_NULL: "ALL (f::real => real) a::real. Dint (a, a) f 0"
  by (import transc INTEGRAL_NULL)

lemma FTC1: "ALL (f::real => real) (f'::real => real) (a::real) b::real.
   a <= b & (ALL x::real. a <= x & x <= b --> diffl f (f' x) x) -->
   Dint (a, b) f' (f b - f a)"
  by (import transc FTC1)

lemma MCLAURIN: "ALL (f::real => real) (diff::nat => real => real) (h::real) n::nat.
   0 < h &
   0 < n &
   diff 0 = f &
   (ALL (m::nat) t::real.
       m < n & 0 <= t & t <= h --> diffl (diff m) (diff (Suc m) t) t) -->
   (EX t>0.
       t < h &
       f h =
       real.sum (0, n) (%m::nat. diff m 0 / real (FACT m) * h ^ m) +
       diff n t / real (FACT n) * h ^ n)"
  by (import transc MCLAURIN)

lemma MCLAURIN_NEG: "ALL (f::real => real) (diff::nat => real => real) (h::real) n::nat.
   h < 0 &
   0 < n &
   diff 0 = f &
   (ALL (m::nat) t::real.
       m < n & h <= t & t <= 0 --> diffl (diff m) (diff (Suc m) t) t) -->
   (EX t::real.
       h < t &
       t < 0 &
       f h =
       real.sum (0, n) (%m::nat. diff m 0 / real (FACT m) * h ^ m) +
       diff n t / real (FACT n) * h ^ n)"
  by (import transc MCLAURIN_NEG)

lemma MCLAURIN_ALL_LT: "ALL (f::real => real) diff::nat => real => real.
   diff 0 = f &
   (ALL (m::nat) x::real. diffl (diff m) (diff (Suc m) x) x) -->
   (ALL (x::real) n::nat.
       x ~= 0 & 0 < n -->
       (EX t::real.
           0 < abs t &
           abs t < abs x &
           f x =
           real.sum (0, n) (%m::nat. diff m 0 / real (FACT m) * x ^ m) +
           diff n t / real (FACT n) * x ^ n))"
  by (import transc MCLAURIN_ALL_LT)

lemma MCLAURIN_ZERO: "ALL (diff::nat => real => real) (n::nat) x::real.
   x = 0 & 0 < n -->
   real.sum (0, n) (%m::nat. diff m 0 / real (FACT m) * x ^ m) = diff 0 0"
  by (import transc MCLAURIN_ZERO)

lemma MCLAURIN_ALL_LE: "ALL (f::real => real) diff::nat => real => real.
   diff 0 = f &
   (ALL (m::nat) x::real. diffl (diff m) (diff (Suc m) x) x) -->
   (ALL (x::real) n::nat.
       EX t::real.
          abs t <= abs x &
          f x =
          real.sum (0, n) (%m::nat. diff m 0 / real (FACT m) * x ^ m) +
          diff n t / real (FACT n) * x ^ n)"
  by (import transc MCLAURIN_ALL_LE)

lemma MCLAURIN_EXP_LT: "ALL (x::real) n::nat.
   x ~= 0 & 0 < n -->
   (EX xa::real.
       0 < abs xa &
       abs xa < abs x &
       exp x =
       real.sum (0, n) (%m::nat. x ^ m / real (FACT m)) +
       exp xa / real (FACT n) * x ^ n)"
  by (import transc MCLAURIN_EXP_LT)

lemma MCLAURIN_EXP_LE: "ALL (x::real) n::nat.
   EX xa::real.
      abs xa <= abs x &
      exp x =
      real.sum (0, n) (%m::nat. x ^ m / real (FACT m)) +
      exp xa / real (FACT n) * x ^ n"
  by (import transc MCLAURIN_EXP_LE)

lemma DIFF_LN_COMPOSITE: "ALL (g::real => real) (m::real) x::real.
   diffl g m x & 0 < g x -->
   diffl (%x::real. ln (g x)) (inverse (g x) * m) x"
  by (import transc DIFF_LN_COMPOSITE)

;end_setup

;setup_theory poly

consts
  poly :: "real list => real => real" 

specification (poly_primdef: poly) poly_def: "(ALL x::real. poly [] x = 0) &
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
  poly_neg_primdef: "poly_neg == ## (- 1)"

lemma poly_neg_def: "poly_neg = ## (- 1)"
  by (import poly poly_neg_def)

consts
  poly_mul :: "real list => real list => real list" 

specification (poly_mul_primdef: poly_mul) poly_mul_def: "(ALL l2::real list. poly_mul [] l2 = []) &
(ALL (h::real) (t::real list) l2::real list.
    poly_mul (h # t) l2 =
    (if t = [] then ## h l2 else poly_add (## h l2) (0 # poly_mul t l2)))"
  by (import poly poly_mul_def)

consts
  poly_exp :: "real list => nat => real list" 

specification (poly_exp_primdef: poly_exp) poly_exp_def: "(ALL p::real list. poly_exp p 0 = [1]) &
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
  "diff == %l::real list. if l = [] then [] else poly_diff_aux 1 (tl l)"

lemma poly_diff_def: "ALL l::real list. diff l = (if l = [] then [] else poly_diff_aux 1 (tl l))"
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
poly_add (## h1 p2) (0 # poly_mul (k1 # t1) p2)"
  by (import poly POLY_MUL_CLAUSES)

lemma POLY_DIFF_CLAUSES: "diff [] = [] &
diff [c::real] = [] & diff ((h::real) # (t::real list)) = poly_diff_aux 1 t"
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

lemma POLY_IVT_POS: "ALL (x::real list) (xa::real) xb::real.
   xa < xb & poly x xa < 0 & 0 < poly x xb -->
   (EX xc::real. xa < xc & xc < xb & poly x xc = 0)"
  by (import poly POLY_IVT_POS)

lemma POLY_IVT_NEG: "ALL (p::real list) (a::real) b::real.
   a < b & 0 < poly p a & poly p b < 0 -->
   (EX x::real. a < x & x < b & poly p x = 0)"
  by (import poly POLY_IVT_NEG)

lemma POLY_MVT: "ALL (p::real list) (a::real) b::real.
   a < b -->
   (EX x::real.
       a < x & x < b & poly p b - poly p a = (b - a) * poly (diff p) x)"
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
   poly (diff (xa # x)) = poly (poly_add (0 # diff x) x)"
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
   poly (diff (poly_exp [- a, 1] (Suc n))) =
   poly (## (real (Suc n)) (poly_exp [- a, 1] n))"
  by (import poly POLY_DIFF_EXP_PRIME)

lemma POLY_LINEAR_REM: "ALL (t::real list) h::real.
   EX (q::real list) r::real.
      h # t = poly_add [r] (poly_mul [- (a::real), 1] q)"
  by (import poly POLY_LINEAR_REM)

lemma POLY_LINEAR_DIVIDES: "ALL (a::real) t::real list.
   (poly t a = 0) = (t = [] | (EX q::real list. t = poly_mul [- a, 1] q))"
  by (import poly POLY_LINEAR_DIVIDES)

lemma POLY_LENGTH_MUL: "ALL x::real list. length (poly_mul [- (a::real), 1] x) = Suc (length x)"
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

lemma POLY_ENTIRE_LEMMA: "ALL (p::real list) q::real list.
   poly p ~= poly [] & poly q ~= poly [] --> poly (poly_mul p q) ~= poly []"
  by (import poly POLY_ENTIRE_LEMMA)

lemma POLY_ENTIRE: "ALL (p::real list) q::real list.
   (poly (poly_mul p q) = poly []) = (poly p = poly [] | poly q = poly [])"
  by (import poly POLY_ENTIRE)

lemma POLY_MUL_LCANCEL: "ALL (x::real list) (xa::real list) xb::real list.
   (poly (poly_mul x xa) = poly (poly_mul x xb)) =
   (poly x = poly [] | poly xa = poly xb)"
  by (import poly POLY_MUL_LCANCEL)

lemma POLY_EXP_EQ_0: "ALL (p::real list) n::nat.
   (poly (poly_exp p n) = poly []) = (poly p = poly [] & n ~= 0)"
  by (import poly POLY_EXP_EQ_0)

lemma POLY_PRIME_EQ_0: "ALL a::real. poly [a, 1] ~= poly []"
  by (import poly POLY_PRIME_EQ_0)

lemma POLY_EXP_PRIME_EQ_0: "ALL (a::real) n::nat. poly (poly_exp [a, 1] n) ~= poly []"
  by (import poly POLY_EXP_PRIME_EQ_0)

lemma POLY_ZERO_LEMMA: "ALL (h::real) t::real list.
   poly (h # t) = poly [] --> h = 0 & poly t = poly []"
  by (import poly POLY_ZERO_LEMMA)

lemma POLY_ZERO: "ALL t::real list. (poly t = poly []) = list_all (%c::real. c = 0) t"
  by (import poly POLY_ZERO)

lemma POLY_DIFF_AUX_ISZERO: "ALL (t::real list) n::nat.
   list_all (%c::real. c = 0) (poly_diff_aux (Suc n) t) =
   list_all (%c::real. c = 0) t"
  by (import poly POLY_DIFF_AUX_ISZERO)

lemma POLY_DIFF_ISZERO: "ALL x::real list.
   poly (diff x) = poly [] --> (EX h::real. poly x = poly [h])"
  by (import poly POLY_DIFF_ISZERO)

lemma POLY_DIFF_ZERO: "ALL x::real list. poly x = poly [] --> poly (diff x) = poly []"
  by (import poly POLY_DIFF_ZERO)

lemma POLY_DIFF_WELLDEF: "ALL (p::real list) q::real list.
   poly p = poly q --> poly (diff p) = poly (diff q)"
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
   poly_divides [a, 1] (poly_mul p q) =
   (poly_divides [a, 1] p | poly_divides [a, 1] q)"
  by (import poly POLY_PRIMES)

lemma POLY_DIVIDES_REFL: "ALL p::real list. poly_divides p p"
  by (import poly POLY_DIVIDES_REFL)

lemma POLY_DIVIDES_TRANS: "ALL (p::real list) (q::real list) r::real list.
   poly_divides p q & poly_divides q r --> poly_divides p r"
  by (import poly POLY_DIVIDES_TRANS)

lemma POLY_DIVIDES_EXP: "ALL (p::real list) (m::nat) n::nat.
   m <= n --> poly_divides (poly_exp p m) (poly_exp p n)"
  by (import poly POLY_DIVIDES_EXP)

lemma POLY_EXP_DIVIDES: "ALL (p::real list) (q::real list) (m::nat) n::nat.
   poly_divides (poly_exp p n) q & m <= n --> poly_divides (poly_exp p m) q"
  by (import poly POLY_EXP_DIVIDES)

lemma POLY_DIVIDES_ADD: "ALL (p::real list) (q::real list) r::real list.
   poly_divides p q & poly_divides p r --> poly_divides p (poly_add q r)"
  by (import poly POLY_DIVIDES_ADD)

lemma POLY_DIVIDES_SUB: "ALL (p::real list) (q::real list) r::real list.
   poly_divides p q & poly_divides p (poly_add q r) --> poly_divides p r"
  by (import poly POLY_DIVIDES_SUB)

lemma POLY_DIVIDES_SUB2: "ALL (p::real list) (q::real list) r::real list.
   poly_divides p r & poly_divides p (poly_add q r) --> poly_divides p q"
  by (import poly POLY_DIVIDES_SUB2)

lemma POLY_DIVIDES_ZERO: "ALL (p::real list) q::real list. poly p = poly [] --> poly_divides q p"
  by (import poly POLY_DIVIDES_ZERO)

lemma POLY_ORDER_EXISTS: "ALL (a::real) (d::nat) p::real list.
   length p = d & poly p ~= poly [] -->
   (EX x::nat.
       poly_divides (poly_exp [- a, 1] x) p &
       ~ poly_divides (poly_exp [- a, 1] (Suc x)) p)"
  by (import poly POLY_ORDER_EXISTS)

lemma POLY_ORDER: "ALL (p::real list) a::real.
   poly p ~= poly [] -->
   (EX! n::nat.
       poly_divides (poly_exp [- a, 1] n) p &
       ~ poly_divides (poly_exp [- a, 1] (Suc n)) p)"
  by (import poly POLY_ORDER)

constdefs
  poly_order :: "real => real list => nat" 
  "poly_order ==
%(a::real) p::real list.
   SOME n::nat.
      poly_divides (poly_exp [- a, 1] n) p &
      ~ poly_divides (poly_exp [- a, 1] (Suc n)) p"

lemma poly_order: "ALL (a::real) p::real list.
   poly_order a p =
   (SOME n::nat.
       poly_divides (poly_exp [- a, 1] n) p &
       ~ poly_divides (poly_exp [- a, 1] (Suc n)) p)"
  by (import poly poly_order)

lemma ORDER: "ALL (p::real list) (a::real) n::nat.
   (poly_divides (poly_exp [- a, 1] n) p &
    ~ poly_divides (poly_exp [- a, 1] (Suc n)) p) =
   (n = poly_order a p & poly p ~= poly [])"
  by (import poly ORDER)

lemma ORDER_THM: "ALL (p::real list) a::real.
   poly p ~= poly [] -->
   poly_divides (poly_exp [- a, 1] (poly_order a p)) p &
   ~ poly_divides (poly_exp [- a, 1] (Suc (poly_order a p))) p"
  by (import poly ORDER_THM)

lemma ORDER_UNIQUE: "ALL (p::real list) (a::real) n::nat.
   poly p ~= poly [] &
   poly_divides (poly_exp [- a, 1] n) p &
   ~ poly_divides (poly_exp [- a, 1] (Suc n)) p -->
   n = poly_order a p"
  by (import poly ORDER_UNIQUE)

lemma ORDER_POLY: "ALL (p::real list) (q::real list) a::real.
   poly p = poly q --> poly_order a p = poly_order a q"
  by (import poly ORDER_POLY)

lemma ORDER_ROOT: "ALL (p::real list) a::real.
   (poly p a = 0) = (poly p = poly [] | poly_order a p ~= 0)"
  by (import poly ORDER_ROOT)

lemma ORDER_DIVIDES: "ALL (p::real list) (a::real) n::nat.
   poly_divides (poly_exp [- a, 1] n) p =
   (poly p = poly [] | n <= poly_order a p)"
  by (import poly ORDER_DIVIDES)

lemma ORDER_DECOMP: "ALL (p::real list) a::real.
   poly p ~= poly [] -->
   (EX x::real list.
       poly p = poly (poly_mul (poly_exp [- a, 1] (poly_order a p)) x) &
       ~ poly_divides [- a, 1] x)"
  by (import poly ORDER_DECOMP)

lemma ORDER_MUL: "ALL (a::real) (p::real list) q::real list.
   poly (poly_mul p q) ~= poly [] -->
   poly_order a (poly_mul p q) = poly_order a p + poly_order a q"
  by (import poly ORDER_MUL)

lemma ORDER_DIFF: "ALL (p::real list) a::real.
   poly (diff p) ~= poly [] & poly_order a p ~= 0 -->
   poly_order a p = Suc (poly_order a (diff p))"
  by (import poly ORDER_DIFF)

lemma POLY_SQUAREFREE_DECOMP_ORDER: "ALL (p::real list) (q::real list) (d::real list) (e::real list)
   (r::real list) s::real list.
   poly (diff p) ~= poly [] &
   poly p = poly (poly_mul q d) &
   poly (diff p) = poly (poly_mul e d) &
   poly d = poly (poly_add (poly_mul r p) (poly_mul s (diff p))) -->
   (ALL a::real. poly_order a q = (if poly_order a p = 0 then 0 else 1))"
  by (import poly POLY_SQUAREFREE_DECOMP_ORDER)

constdefs
  rsquarefree :: "real list => bool" 
  "rsquarefree ==
%p::real list.
   poly p ~= poly [] &
   (ALL a::real. poly_order a p = 0 | poly_order a p = 1)"

lemma rsquarefree: "ALL p::real list.
   rsquarefree p =
   (poly p ~= poly [] &
    (ALL a::real. poly_order a p = 0 | poly_order a p = 1))"
  by (import poly rsquarefree)

lemma RSQUAREFREE_ROOTS: "ALL p::real list.
   rsquarefree p = (ALL a::real. ~ (poly p a = 0 & poly (diff p) a = 0))"
  by (import poly RSQUAREFREE_ROOTS)

lemma RSQUAREFREE_DECOMP: "ALL (p::real list) a::real.
   rsquarefree p & poly p a = 0 -->
   (EX q::real list. poly p = poly (poly_mul [- a, 1] q) & poly q a ~= 0)"
  by (import poly RSQUAREFREE_DECOMP)

lemma POLY_SQUAREFREE_DECOMP: "ALL (p::real list) (q::real list) (d::real list) (e::real list)
   (r::real list) s::real list.
   poly (diff p) ~= poly [] &
   poly p = poly (poly_mul q d) &
   poly (diff p) = poly (poly_mul e d) &
   poly d = poly (poly_add (poly_mul r p) (poly_mul s (diff p))) -->
   rsquarefree q & (ALL x::real. (poly q x = 0) = (poly p x = 0))"
  by (import poly POLY_SQUAREFREE_DECOMP)

consts
  normalize :: "real list => real list" 

specification (normalize) normalize: "normalize [] = [] &
(ALL (h::real) t::real list.
    normalize (h # t) =
    (if normalize t = [] then if h = 0 then [] else [h]
     else h # normalize t))"
  by (import poly normalize)

lemma POLY_NORMALIZE: "ALL t::real list. poly (normalize t) = poly t"
  by (import poly POLY_NORMALIZE)

constdefs
  degree :: "real list => nat" 
  "degree == %p::real list. PRE (length (normalize p))"

lemma degree: "ALL p::real list. degree p = PRE (length (normalize p))"
  by (import poly degree)

lemma DEGREE_ZERO: "ALL p::real list. poly p = poly [] --> degree p = 0"
  by (import poly DEGREE_ZERO)

lemma POLY_ROOTS_FINITE_SET: "ALL p::real list.
   poly p ~= poly [] --> FINITE (GSPEC (%x::real. (x, poly p x = 0)))"
  by (import poly POLY_ROOTS_FINITE_SET)

lemma POLY_MONO: "ALL (x::real) (k::real) xa::real list.
   abs x <= k --> abs (poly xa x) <= poly (map abs xa) k"
  by (import poly POLY_MONO)

;end_setup

end

