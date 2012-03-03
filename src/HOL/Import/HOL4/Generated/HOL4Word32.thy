(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOL4Word32 imports HOL4Base begin

setup_theory "~~/src/HOL/Import/HOL4/Generated" bits

consts
  DIV2 :: "nat => nat" 

defs
  DIV2_primdef: "DIV2 == %n. n div 2"

lemma DIV2_def: "DIV2 n = n div 2"
  by (import bits DIV2_def)

consts
  TIMES_2EXP :: "nat => nat => nat" 

defs
  TIMES_2EXP_primdef: "TIMES_2EXP == %x n. n * 2 ^ x"

lemma TIMES_2EXP_def: "TIMES_2EXP x n = n * 2 ^ x"
  by (import bits TIMES_2EXP_def)

consts
  DIV_2EXP :: "nat => nat => nat" 

defs
  DIV_2EXP_primdef: "DIV_2EXP == %x n. n div 2 ^ x"

lemma DIV_2EXP_def: "DIV_2EXP x n = n div 2 ^ x"
  by (import bits DIV_2EXP_def)

consts
  MOD_2EXP :: "nat => nat => nat" 

defs
  MOD_2EXP_primdef: "MOD_2EXP == %x n. n mod 2 ^ x"

lemma MOD_2EXP_def: "MOD_2EXP x n = n mod 2 ^ x"
  by (import bits MOD_2EXP_def)

consts
  DIVMOD_2EXP :: "nat => nat => nat * nat" 

defs
  DIVMOD_2EXP_primdef: "DIVMOD_2EXP == %x n. (n div 2 ^ x, n mod 2 ^ x)"

lemma DIVMOD_2EXP_def: "DIVMOD_2EXP x n = (n div 2 ^ x, n mod 2 ^ x)"
  by (import bits DIVMOD_2EXP_def)

consts
  SBIT :: "bool => nat => nat" 

defs
  SBIT_primdef: "SBIT == %b n. if b then 2 ^ n else 0"

lemma SBIT_def: "SBIT b n = (if b then 2 ^ n else 0)"
  by (import bits SBIT_def)

consts
  BITS :: "nat => nat => nat => nat" 

defs
  BITS_primdef: "BITS == %h l n. MOD_2EXP (Suc h - l) (DIV_2EXP l n)"

lemma BITS_def: "BITS h l n = MOD_2EXP (Suc h - l) (DIV_2EXP l n)"
  by (import bits BITS_def)

definition
  bit :: "nat => nat => bool"  where
  "bit == %b n. BITS b b n = 1"

lemma BIT_def: "bit b n = (BITS b b n = 1)"
  by (import bits BIT_def)

consts
  SLICE :: "nat => nat => nat => nat" 

defs
  SLICE_primdef: "SLICE == %h l n. MOD_2EXP (Suc h) n - MOD_2EXP l n"

lemma SLICE_def: "SLICE h l n = MOD_2EXP (Suc h) n - MOD_2EXP l n"
  by (import bits SLICE_def)

consts
  LSBn :: "nat => bool" 

defs
  LSBn_primdef: "LSBn == bit 0"

lemma LSBn_def: "LSBn = bit 0"
  by (import bits LSBn_def)

consts
  BITWISE :: "nat => (bool => bool => bool) => nat => nat => nat" 

specification (BITWISE_primdef: BITWISE) BITWISE_def: "(ALL oper x y. BITWISE 0 oper x y = 0) &
(ALL n oper x y.
    BITWISE (Suc n) oper x y =
    BITWISE n oper x y + SBIT (oper (bit n x) (bit n y)) n)"
  by (import bits BITWISE_def)

lemma SUC_SUB: "Suc a - a = 1"
  by (import bits SUC_SUB)

lemma DIV_MULT_1: "(r::nat) < (n::nat) ==> (n + r) div n = (1::nat)"
  by (import bits DIV_MULT_1)

lemma ZERO_LT_TWOEXP: "(0::nat) < (2::nat) ^ (n::nat)"
  by (import bits ZERO_LT_TWOEXP)

lemma MOD_2EXP_LT: "(k::nat) mod (2::nat) ^ (n::nat) < (2::nat) ^ n"
  by (import bits MOD_2EXP_LT)

lemma TWOEXP_DIVISION: "(k::nat) = k div (2::nat) ^ (n::nat) * (2::nat) ^ n + k mod (2::nat) ^ n"
  by (import bits TWOEXP_DIVISION)

lemma TWOEXP_MONO: "(a::nat) < (b::nat) ==> (2::nat) ^ a < (2::nat) ^ b"
  by (import bits TWOEXP_MONO)

lemma TWOEXP_MONO2: "(a::nat) <= (b::nat) ==> (2::nat) ^ a <= (2::nat) ^ b"
  by (import bits TWOEXP_MONO2)

lemma EXP_SUB_LESS_EQ: "(2::nat) ^ ((a::nat) - (b::nat)) <= (2::nat) ^ a"
  by (import bits EXP_SUB_LESS_EQ)

lemma BITS_THM: "BITS x xa xb = xb div 2 ^ xa mod 2 ^ (Suc x - xa)"
  by (import bits BITS_THM)

lemma BITSLT_THM: "BITS h l n < 2 ^ (Suc h - l)"
  by (import bits BITSLT_THM)

lemma DIV_MULT_LEM: "(0::nat) < (n::nat) ==> (m::nat) div n * n <= m"
  by (import bits DIV_MULT_LEM)

lemma MOD_2EXP_LEM: "(n::nat) mod (2::nat) ^ (x::nat) = n - n div (2::nat) ^ x * (2::nat) ^ x"
  by (import bits MOD_2EXP_LEM)

lemma BITS2_THM: "BITS h l n = n mod 2 ^ Suc h div 2 ^ l"
  by (import bits BITS2_THM)

lemma BITS_COMP_THM: "h2 + l1 <= h1 ==> BITS h2 l2 (BITS h1 l1 n) = BITS (h2 + l1) (l2 + l1) n"
  by (import bits BITS_COMP_THM)

lemma BITS_DIV_THM: "BITS h l x div 2 ^ n = BITS h (l + n) x"
  by (import bits BITS_DIV_THM)

lemma BITS_LT_HIGH: "n < 2 ^ Suc h ==> BITS h l n = n div 2 ^ l"
  by (import bits BITS_LT_HIGH)

lemma BITS_ZERO: "h < l ==> BITS h l n = 0"
  by (import bits BITS_ZERO)

lemma BITS_ZERO2: "BITS h l 0 = 0"
  by (import bits BITS_ZERO2)

lemma BITS_ZERO3: "BITS h 0 x = x mod 2 ^ Suc h"
  by (import bits BITS_ZERO3)

lemma BITS_COMP_THM2: "BITS h2 l2 (BITS h1 l1 n) = BITS (min h1 (h2 + l1)) (l2 + l1) n"
  by (import bits BITS_COMP_THM2)

lemma NOT_MOD2_LEM: "((n::nat) mod (2::nat) ~= (0::nat)) = (n mod (2::nat) = (1::nat))"
  by (import bits NOT_MOD2_LEM)

lemma NOT_MOD2_LEM2: "((n::nat) mod (2::nat) ~= (1::nat)) = (n mod (2::nat) = (0::nat))"
  by (import bits NOT_MOD2_LEM2)

lemma EVEN_MOD2_LEM: "EVEN n = (n mod 2 = 0)"
  by (import bits EVEN_MOD2_LEM)

lemma ODD_MOD2_LEM: "ODD n = (n mod 2 = 1)"
  by (import bits ODD_MOD2_LEM)

lemma LSB_ODD: "LSBn = ODD"
  by (import bits LSB_ODD)

lemma DIV_MULT_THM: "(n::nat) div (2::nat) ^ (x::nat) * (2::nat) ^ x = n - n mod (2::nat) ^ x"
  by (import bits DIV_MULT_THM)

lemma DIV_MULT_THM2: "(2::nat) * ((x::nat) div (2::nat)) = x - x mod (2::nat)"
  by (import bits DIV_MULT_THM2)

lemma LESS_EQ_EXP_MULT: "(a::nat) <= (b::nat) ==> EX x::nat. (2::nat) ^ b = x * (2::nat) ^ a"
  by (import bits LESS_EQ_EXP_MULT)

lemma SLICE_LEM1: "(a::nat) div (2::nat) ^ ((x::nat) + (y::nat)) * (2::nat) ^ (x + y) =
a div (2::nat) ^ x * (2::nat) ^ x -
a div (2::nat) ^ x mod (2::nat) ^ y * (2::nat) ^ x"
  by (import bits SLICE_LEM1)

lemma SLICE_LEM2: "(n::nat) mod (2::nat) ^ ((x::nat) + (y::nat)) =
n mod (2::nat) ^ x + n div (2::nat) ^ x mod (2::nat) ^ y * (2::nat) ^ x"
  by (import bits SLICE_LEM2)

lemma SLICE_LEM3: "(l::nat) < (h::nat) ==> (n::nat) mod (2::nat) ^ Suc l <= n mod (2::nat) ^ h"
  by (import bits SLICE_LEM3)

lemma SLICE_THM: "SLICE h l n = BITS h l n * 2 ^ l"
  by (import bits SLICE_THM)

lemma SLICELT_THM: "SLICE h l n < 2 ^ Suc h"
  by (import bits SLICELT_THM)

lemma BITS_SLICE_THM: "BITS h l (SLICE h l n) = BITS h l n"
  by (import bits BITS_SLICE_THM)

lemma BITS_SLICE_THM2: "h <= h2 ==> BITS h2 l (SLICE h l n) = BITS h l n"
  by (import bits BITS_SLICE_THM2)

lemma MOD_2EXP_MONO: "(l::nat) <= (h::nat) ==> (n::nat) mod (2::nat) ^ l <= n mod (2::nat) ^ Suc h"
  by (import bits MOD_2EXP_MONO)

lemma SLICE_COMP_THM: "Suc m <= h & l <= m ==> SLICE h (Suc m) n + SLICE m l n = SLICE h l n"
  by (import bits SLICE_COMP_THM)

lemma SLICE_ZERO: "h < l ==> SLICE h l n = 0"
  by (import bits SLICE_ZERO)

lemma BIT_COMP_THM3: "Suc m <= h & l <= m
==> BITS h (Suc m) n * 2 ^ (Suc m - l) + BITS m l n = BITS h l n"
  by (import bits BIT_COMP_THM3)

lemma NOT_BIT: "(~ bit n a) = (BITS n n a = 0)"
  by (import bits NOT_BIT)

lemma NOT_BITS: "(BITS n n a ~= 0) = (BITS n n a = 1)"
  by (import bits NOT_BITS)

lemma NOT_BITS2: "(BITS n n a ~= 1) = (BITS n n a = 0)"
  by (import bits NOT_BITS2)

lemma BIT_SLICE: "(bit n a = bit n b) = (SLICE n n a = SLICE n n b)"
  by (import bits BIT_SLICE)

lemma BIT_SLICE_LEM: "SBIT (bit x n) (x + y) = SLICE x x n * 2 ^ y"
  by (import bits BIT_SLICE_LEM)

lemma BIT_SLICE_THM: "SBIT (bit x xa) x = SLICE x x xa"
  by (import bits BIT_SLICE_THM)

lemma SBIT_DIV: "n < m ==> SBIT b (m - n) = SBIT b m div 2 ^ n"
  by (import bits SBIT_DIV)

lemma BITS_SUC: "l <= Suc h
==> SBIT (bit (Suc h) n) (Suc h - l) + BITS h l n = BITS (Suc h) l n"
  by (import bits BITS_SUC)

lemma BITS_SUC_THM: "BITS (Suc h) l n =
(if Suc h < l then 0 else SBIT (bit (Suc h) n) (Suc h - l) + BITS h l n)"
  by (import bits BITS_SUC_THM)

lemma BIT_BITS_THM: "(ALL x. l <= x & x <= h --> bit x a = bit x b) = (BITS h l a = BITS h l b)"
  by (import bits BIT_BITS_THM)

lemma BITWISE_LT_2EXP: "BITWISE n oper a b < 2 ^ n"
  by (import bits BITWISE_LT_2EXP)

lemma LESS_EXP_MULT2: "(a::nat) < (b::nat)
==> EX x::nat. (2::nat) ^ b = (2::nat) ^ (x + (1::nat)) * (2::nat) ^ a"
  by (import bits LESS_EXP_MULT2)

lemma BITWISE_THM: "x < n ==> bit x (BITWISE n oper a b) = oper (bit x a) (bit x b)"
  by (import bits BITWISE_THM)

lemma BITWISE_COR: "[| x < n; oper (bit x a) (bit x b) |]
==> BITWISE n oper a b div 2 ^ x mod 2 = 1"
  by (import bits BITWISE_COR)

lemma BITWISE_NOT_COR: "[| x < n; ~ oper (bit x a) (bit x b) |]
==> BITWISE n oper a b div 2 ^ x mod 2 = 0"
  by (import bits BITWISE_NOT_COR)

lemma MOD_PLUS_RIGHT: "(0::nat) < (n::nat) ==> ((j::nat) + (k::nat) mod n) mod n = (j + k) mod n"
  by (import bits MOD_PLUS_RIGHT)

lemma MOD_PLUS_1: "(0::nat) < (n::nat)
==> (((x::nat) + (1::nat)) mod n = (0::nat)) = (x mod n + (1::nat) = n)"
  by (import bits MOD_PLUS_1)

lemma MOD_ADD_1: "[| (0::nat) < (n::nat); ((x::nat) + (1::nat)) mod n ~= (0::nat) |]
==> (x + (1::nat)) mod n = x mod n + (1::nat)"
  by (import bits MOD_ADD_1)

;end_setup

setup_theory "~~/src/HOL/Import/HOL4/Generated" word32

consts
  HB :: "nat" 

defs
  HB_primdef: "HB ==
NUMERAL
 (NUMERAL_BIT1
   (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO)))))"

lemma HB_def: "HB =
NUMERAL
 (NUMERAL_BIT1
   (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO)))))"
  by (import word32 HB_def)

consts
  WL :: "nat" 

defs
  WL_primdef: "WL == Suc HB"

lemma WL_def: "WL = Suc HB"
  by (import word32 WL_def)

consts
  MODw :: "nat => nat" 

defs
  MODw_primdef: "MODw == %n. n mod 2 ^ WL"

lemma MODw_def: "MODw n = n mod 2 ^ WL"
  by (import word32 MODw_def)

consts
  INw :: "nat => bool" 

defs
  INw_primdef: "INw == %n. n < 2 ^ WL"

lemma INw_def: "INw n = (n < 2 ^ WL)"
  by (import word32 INw_def)

consts
  EQUIV :: "nat => nat => bool" 

defs
  EQUIV_primdef: "EQUIV == %x y. MODw x = MODw y"

lemma EQUIV_def: "EQUIV x y = (MODw x = MODw y)"
  by (import word32 EQUIV_def)

lemma EQUIV_QT: "EQUIV x y = (EQUIV x = EQUIV y)"
  by (import word32 EQUIV_QT)

lemma FUNPOW_THM2: "(f ^^ Suc n) x = f ((f ^^ n) x)"
  by (import word32 FUNPOW_THM2)

lemma FUNPOW_COMP: "(f ^^ m) ((f ^^ n) a) = (f ^^ (m + n)) a"
  by (import word32 FUNPOW_COMP)

lemma INw_MODw: "INw (MODw n)"
  by (import word32 INw_MODw)

lemma TOw_IDEM: "INw a ==> MODw a = a"
  by (import word32 TOw_IDEM)

lemma MODw_IDEM2: "MODw (MODw a) = MODw a"
  by (import word32 MODw_IDEM2)

lemma TOw_QT: "EQUIV (MODw a) a"
  by (import word32 TOw_QT)

lemma MODw_THM: "MODw = BITS HB 0"
  by (import word32 MODw_THM)

lemma MOD_ADD: "MODw (a + b) = MODw (MODw a + MODw b)"
  by (import word32 MOD_ADD)

lemma MODw_MULT: "MODw (a * b) = MODw (MODw a * MODw b)"
  by (import word32 MODw_MULT)

consts
  AONE :: "nat" 

defs
  AONE_primdef: "AONE == 1"

lemma AONE_def: "AONE = 1"
  by (import word32 AONE_def)

lemma ADD_QT: "(ALL n. EQUIV (0 + n) n) & (ALL m n. EQUIV (Suc m + n) (Suc (m + n)))"
  by (import word32 ADD_QT)

lemma ADD_0_QT: "EQUIV (a + 0) a"
  by (import word32 ADD_0_QT)

lemma ADD_COMM_QT: "EQUIV (a + b) (b + a)"
  by (import word32 ADD_COMM_QT)

lemma ADD_ASSOC_QT: "EQUIV (a + (b + c)) (a + b + c)"
  by (import word32 ADD_ASSOC_QT)

lemma MULT_QT: "(ALL n. EQUIV (0 * n) 0) & (ALL m n. EQUIV (Suc m * n) (m * n + n))"
  by (import word32 MULT_QT)

lemma ADD1_QT: "EQUIV (Suc m) (m + AONE)"
  by (import word32 ADD1_QT)

lemma ADD_CLAUSES_QT: "(ALL m. EQUIV (0 + m) m) &
(ALL m. EQUIV (m + 0) m) &
(ALL m n. EQUIV (Suc m + n) (Suc (m + n))) &
(ALL m n. EQUIV (m + Suc n) (Suc (m + n)))"
  by (import word32 ADD_CLAUSES_QT)

lemma SUC_EQUIV_COMP: "EQUIV (Suc a) b ==> EQUIV a (b + (2 ^ WL - 1))"
  by (import word32 SUC_EQUIV_COMP)

lemma INV_SUC_EQ_QT: "EQUIV (Suc m) (Suc n) = EQUIV m n"
  by (import word32 INV_SUC_EQ_QT)

lemma ADD_INV_0_QT: "EQUIV (m + n) m ==> EQUIV n 0"
  by (import word32 ADD_INV_0_QT)

lemma ADD_INV_0_EQ_QT: "EQUIV (m + n) m = EQUIV n 0"
  by (import word32 ADD_INV_0_EQ_QT)

lemma EQ_ADD_LCANCEL_QT: "EQUIV (m + n) (m + p) = EQUIV n p"
  by (import word32 EQ_ADD_LCANCEL_QT)

lemma EQ_ADD_RCANCEL_QT: "EQUIV (x + xb) (xa + xb) = EQUIV x xa"
  by (import word32 EQ_ADD_RCANCEL_QT)

lemma LEFT_ADD_DISTRIB_QT: "EQUIV (p * (m + n)) (p * m + p * n)"
  by (import word32 LEFT_ADD_DISTRIB_QT)

lemma MULT_ASSOC_QT: "EQUIV (m * (n * p)) (m * n * p)"
  by (import word32 MULT_ASSOC_QT)

lemma MULT_COMM_QT: "EQUIV (m * n) (n * m)"
  by (import word32 MULT_COMM_QT)

lemma MULT_CLAUSES_QT: "EQUIV (0 * m) 0 &
EQUIV (m * 0) 0 &
EQUIV (AONE * m) m &
EQUIV (m * AONE) m &
EQUIV (Suc m * n) (m * n + n) & EQUIV (m * Suc n) (m + m * n)"
  by (import word32 MULT_CLAUSES_QT)

consts
  MSBn :: "nat => bool" 

defs
  MSBn_primdef: "MSBn == bit HB"

lemma MSBn_def: "MSBn = bit HB"
  by (import word32 MSBn_def)

consts
  ONE_COMP :: "nat => nat" 

defs
  ONE_COMP_primdef: "ONE_COMP == %x. 2 ^ WL - 1 - MODw x"

lemma ONE_COMP_def: "ONE_COMP x = 2 ^ WL - 1 - MODw x"
  by (import word32 ONE_COMP_def)

consts
  TWO_COMP :: "nat => nat" 

defs
  TWO_COMP_primdef: "TWO_COMP == %x. 2 ^ WL - MODw x"

lemma TWO_COMP_def: "TWO_COMP x = 2 ^ WL - MODw x"
  by (import word32 TWO_COMP_def)

lemma ADD_TWO_COMP_QT: "EQUIV (MODw a + TWO_COMP a) 0"
  by (import word32 ADD_TWO_COMP_QT)

lemma TWO_COMP_ONE_COMP_QT: "EQUIV (TWO_COMP a) (ONE_COMP a + AONE)"
  by (import word32 TWO_COMP_ONE_COMP_QT)

lemma BIT_EQUIV_THM: "(ALL xb<WL. bit xb x = bit xb xa) = EQUIV x xa"
  by (import word32 BIT_EQUIV_THM)

lemma BITS_SUC2: "BITS (Suc n) 0 a = SLICE (Suc n) (Suc n) a + BITS n 0 a"
  by (import word32 BITS_SUC2)

lemma BITWISE_ONE_COMP_THM: "BITWISE WL (%x y. ~ x) a b = ONE_COMP a"
  by (import word32 BITWISE_ONE_COMP_THM)

lemma ONE_COMP_THM: "xa < WL ==> bit xa (ONE_COMP x) = (~ bit xa x)"
  by (import word32 ONE_COMP_THM)

consts
  OR :: "nat => nat => nat" 

defs
  OR_primdef: "OR == BITWISE WL op |"

lemma OR_def: "OR = BITWISE WL op |"
  by (import word32 OR_def)

consts
  AND :: "nat => nat => nat" 

defs
  AND_primdef: "AND == BITWISE WL op &"

lemma AND_def: "AND = BITWISE WL op &"
  by (import word32 AND_def)

consts
  EOR :: "nat => nat => nat" 

defs
  EOR_primdef: "EOR == BITWISE WL op ~="

lemma EOR_def: "EOR = BITWISE WL op ~="
  by (import word32 EOR_def)

consts
  COMP0 :: "nat" 

defs
  COMP0_primdef: "COMP0 == ONE_COMP 0"

lemma COMP0_def: "COMP0 = ONE_COMP 0"
  by (import word32 COMP0_def)

lemma BITWISE_THM2: "(ALL x<WL. oper (bit x a) (bit x b) = bit x y) =
EQUIV (BITWISE WL oper a b) y"
  by (import word32 BITWISE_THM2)

lemma OR_ASSOC_QT: "EQUIV (OR a (OR b c)) (OR (OR a b) c)"
  by (import word32 OR_ASSOC_QT)

lemma OR_COMM_QT: "EQUIV (OR a b) (OR b a)"
  by (import word32 OR_COMM_QT)

lemma OR_ABSORB_QT: "EQUIV (AND a (OR a b)) a"
  by (import word32 OR_ABSORB_QT)

lemma OR_IDEM_QT: "EQUIV (OR a a) a"
  by (import word32 OR_IDEM_QT)

lemma AND_ASSOC_QT: "EQUIV (AND a (AND b c)) (AND (AND a b) c)"
  by (import word32 AND_ASSOC_QT)

lemma AND_COMM_QT: "EQUIV (AND a b) (AND b a)"
  by (import word32 AND_COMM_QT)

lemma AND_ABSORB_QT: "EQUIV (OR a (AND a b)) a"
  by (import word32 AND_ABSORB_QT)

lemma AND_IDEM_QT: "EQUIV (AND a a) a"
  by (import word32 AND_IDEM_QT)

lemma OR_COMP_QT: "EQUIV (OR a (ONE_COMP a)) COMP0"
  by (import word32 OR_COMP_QT)

lemma AND_COMP_QT: "EQUIV (AND a (ONE_COMP a)) 0"
  by (import word32 AND_COMP_QT)

lemma ONE_COMP_QT: "EQUIV (ONE_COMP (ONE_COMP a)) a"
  by (import word32 ONE_COMP_QT)

lemma RIGHT_AND_OVER_OR_QT: "EQUIV (AND (OR a b) c) (OR (AND a c) (AND b c))"
  by (import word32 RIGHT_AND_OVER_OR_QT)

lemma RIGHT_OR_OVER_AND_QT: "EQUIV (OR (AND a b) c) (AND (OR a c) (OR b c))"
  by (import word32 RIGHT_OR_OVER_AND_QT)

lemma DE_MORGAN_THM_QT: "EQUIV (ONE_COMP (AND a b)) (OR (ONE_COMP a) (ONE_COMP b)) &
EQUIV (ONE_COMP (OR a b)) (AND (ONE_COMP a) (ONE_COMP b))"
  by (import word32 DE_MORGAN_THM_QT)

lemma BIT_EQUIV: "[| n < WL; EQUIV a b |] ==> bit n a = bit n b"
  by (import word32 BIT_EQUIV)

lemma LSB_WELLDEF: "EQUIV a b ==> LSBn a = LSBn b"
  by (import word32 LSB_WELLDEF)

lemma MSB_WELLDEF: "EQUIV a b ==> MSBn a = MSBn b"
  by (import word32 MSB_WELLDEF)

lemma BITWISE_ISTEP: "0 < n
==> BITWISE n oper (a div 2) (b div 2) =
    BITWISE n oper a b div 2 + SBIT (oper (bit n a) (bit n b)) (n - 1)"
  by (import word32 BITWISE_ISTEP)

lemma BITWISE_EVAL: "BITWISE (Suc n) oper a b =
2 * BITWISE n oper (a div 2) (b div 2) + SBIT (oper (LSBn a) (LSBn b)) 0"
  by (import word32 BITWISE_EVAL)

lemma BITWISE_WELLDEF: "EQUIV a b & EQUIV c d ==> EQUIV (BITWISE n oper a c) (BITWISE n oper b d)"
  by (import word32 BITWISE_WELLDEF)

lemma BITWISEw_WELLDEF: "EQUIV a b & EQUIV c d ==> EQUIV (BITWISE WL oper a c) (BITWISE WL oper b d)"
  by (import word32 BITWISEw_WELLDEF)

lemma SUC_WELLDEF: "EQUIV a b ==> EQUIV (Suc a) (Suc b)"
  by (import word32 SUC_WELLDEF)

lemma ADD_WELLDEF: "EQUIV a b & EQUIV c d ==> EQUIV (a + c) (b + d)"
  by (import word32 ADD_WELLDEF)

lemma MUL_WELLDEF: "EQUIV a b & EQUIV c d ==> EQUIV (a * c) (b * d)"
  by (import word32 MUL_WELLDEF)

lemma ONE_COMP_WELLDEF: "EQUIV a b ==> EQUIV (ONE_COMP a) (ONE_COMP b)"
  by (import word32 ONE_COMP_WELLDEF)

lemma TWO_COMP_WELLDEF: "EQUIV a b ==> EQUIV (TWO_COMP a) (TWO_COMP b)"
  by (import word32 TWO_COMP_WELLDEF)

lemma TOw_WELLDEF: "EQUIV a b ==> EQUIV (MODw a) (MODw b)"
  by (import word32 TOw_WELLDEF)

consts
  LSR_ONE :: "nat => nat" 

defs
  LSR_ONE_primdef: "LSR_ONE == %a. MODw a div 2"

lemma LSR_ONE_def: "LSR_ONE a = MODw a div 2"
  by (import word32 LSR_ONE_def)

consts
  ASR_ONE :: "nat => nat" 

defs
  ASR_ONE_primdef: "ASR_ONE == %a. LSR_ONE a + SBIT (MSBn a) HB"

lemma ASR_ONE_def: "ASR_ONE a = LSR_ONE a + SBIT (MSBn a) HB"
  by (import word32 ASR_ONE_def)

consts
  ROR_ONE :: "nat => nat" 

defs
  ROR_ONE_primdef: "ROR_ONE == %a. LSR_ONE a + SBIT (LSBn a) HB"

lemma ROR_ONE_def: "ROR_ONE a = LSR_ONE a + SBIT (LSBn a) HB"
  by (import word32 ROR_ONE_def)

consts
  RRXn :: "bool => nat => nat" 

defs
  RRXn_primdef: "RRXn == %c a. LSR_ONE a + SBIT c HB"

lemma RRXn_def: "RRXn c a = LSR_ONE a + SBIT c HB"
  by (import word32 RRXn_def)

lemma LSR_ONE_WELLDEF: "EQUIV a b ==> EQUIV (LSR_ONE a) (LSR_ONE b)"
  by (import word32 LSR_ONE_WELLDEF)

lemma ASR_ONE_WELLDEF: "EQUIV a b ==> EQUIV (ASR_ONE a) (ASR_ONE b)"
  by (import word32 ASR_ONE_WELLDEF)

lemma ROR_ONE_WELLDEF: "EQUIV a b ==> EQUIV (ROR_ONE a) (ROR_ONE b)"
  by (import word32 ROR_ONE_WELLDEF)

lemma RRX_WELLDEF: "EQUIV a b ==> EQUIV (RRXn c a) (RRXn c b)"
  by (import word32 RRX_WELLDEF)

lemma LSR_ONE: "LSR_ONE = BITS HB 1"
  by (import word32 LSR_ONE)

typedef (open) word32 = "{x::nat => bool. EX xa. x = EQUIV xa}" 
  by (rule typedef_helper,import word32 word32_TY_DEF)

lemmas word32_TY_DEF = typedef_hol2hol4 [OF type_definition_word32]

consts
  mk_word32 :: "(nat => bool) => word32" 
  dest_word32 :: "word32 => nat => bool" 

specification (dest_word32 mk_word32) word32_tybij: "(ALL a. mk_word32 (dest_word32 a) = a) &
(ALL r. (EX x. r = EQUIV x) = (dest_word32 (mk_word32 r) = r))"
  by (import word32 word32_tybij)

consts
  w_0 :: "word32" 

defs
  w_0_primdef: "w_0 == mk_word32 (EQUIV 0)"

lemma w_0_def: "w_0 = mk_word32 (EQUIV 0)"
  by (import word32 w_0_def)

consts
  w_1 :: "word32" 

defs
  w_1_primdef: "w_1 == mk_word32 (EQUIV AONE)"

lemma w_1_def: "w_1 = mk_word32 (EQUIV AONE)"
  by (import word32 w_1_def)

consts
  w_T :: "word32" 

defs
  w_T_primdef: "w_T == mk_word32 (EQUIV COMP0)"

lemma w_T_def: "w_T = mk_word32 (EQUIV COMP0)"
  by (import word32 w_T_def)

definition
  word_suc :: "word32 => word32"  where
  "word_suc == %T1. mk_word32 (EQUIV (Suc (Eps (dest_word32 T1))))"

lemma word_suc: "word_suc T1 = mk_word32 (EQUIV (Suc (Eps (dest_word32 T1))))"
  by (import word32 word_suc)

definition
  word_add :: "word32 => word32 => word32"  where
  "word_add ==
%T1 T2. mk_word32 (EQUIV (Eps (dest_word32 T1) + Eps (dest_word32 T2)))"

lemma word_add: "word_add T1 T2 =
mk_word32 (EQUIV (Eps (dest_word32 T1) + Eps (dest_word32 T2)))"
  by (import word32 word_add)

definition
  word_mul :: "word32 => word32 => word32"  where
  "word_mul ==
%T1 T2. mk_word32 (EQUIV (Eps (dest_word32 T1) * Eps (dest_word32 T2)))"

lemma word_mul: "word_mul T1 T2 =
mk_word32 (EQUIV (Eps (dest_word32 T1) * Eps (dest_word32 T2)))"
  by (import word32 word_mul)

definition
  word_1comp :: "word32 => word32"  where
  "word_1comp == %T1. mk_word32 (EQUIV (ONE_COMP (Eps (dest_word32 T1))))"

lemma word_1comp: "word_1comp T1 = mk_word32 (EQUIV (ONE_COMP (Eps (dest_word32 T1))))"
  by (import word32 word_1comp)

definition
  word_2comp :: "word32 => word32"  where
  "word_2comp == %T1. mk_word32 (EQUIV (TWO_COMP (Eps (dest_word32 T1))))"

lemma word_2comp: "word_2comp T1 = mk_word32 (EQUIV (TWO_COMP (Eps (dest_word32 T1))))"
  by (import word32 word_2comp)

definition
  word_lsr1 :: "word32 => word32"  where
  "word_lsr1 == %T1. mk_word32 (EQUIV (LSR_ONE (Eps (dest_word32 T1))))"

lemma word_lsr1: "word_lsr1 T1 = mk_word32 (EQUIV (LSR_ONE (Eps (dest_word32 T1))))"
  by (import word32 word_lsr1)

definition
  word_asr1 :: "word32 => word32"  where
  "word_asr1 == %T1. mk_word32 (EQUIV (ASR_ONE (Eps (dest_word32 T1))))"

lemma word_asr1: "word_asr1 T1 = mk_word32 (EQUIV (ASR_ONE (Eps (dest_word32 T1))))"
  by (import word32 word_asr1)

definition
  word_ror1 :: "word32 => word32"  where
  "word_ror1 == %T1. mk_word32 (EQUIV (ROR_ONE (Eps (dest_word32 T1))))"

lemma word_ror1: "word_ror1 T1 = mk_word32 (EQUIV (ROR_ONE (Eps (dest_word32 T1))))"
  by (import word32 word_ror1)

consts
  RRX :: "bool => word32 => word32" 

defs
  RRX_primdef: "RRX == %T1 T2. mk_word32 (EQUIV (RRXn T1 (Eps (dest_word32 T2))))"

lemma RRX_def: "RRX T1 T2 = mk_word32 (EQUIV (RRXn T1 (Eps (dest_word32 T2))))"
  by (import word32 RRX_def)

consts
  LSB :: "word32 => bool" 

defs
  LSB_primdef: "LSB == %T1. LSBn (Eps (dest_word32 T1))"

lemma LSB_def: "LSB T1 = LSBn (Eps (dest_word32 T1))"
  by (import word32 LSB_def)

consts
  MSB :: "word32 => bool" 

defs
  MSB_primdef: "MSB == %T1. MSBn (Eps (dest_word32 T1))"

lemma MSB_def: "MSB T1 = MSBn (Eps (dest_word32 T1))"
  by (import word32 MSB_def)

definition
  bitwise_or :: "word32 => word32 => word32"  where
  "bitwise_or ==
%T1 T2. mk_word32 (EQUIV (OR (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"

lemma bitwise_or: "bitwise_or T1 T2 =
mk_word32 (EQUIV (OR (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"
  by (import word32 bitwise_or)

definition
  bitwise_eor :: "word32 => word32 => word32"  where
  "bitwise_eor ==
%T1 T2.
   mk_word32 (EQUIV (EOR (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"

lemma bitwise_eor: "bitwise_eor T1 T2 =
mk_word32 (EQUIV (EOR (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"
  by (import word32 bitwise_eor)

definition
  bitwise_and :: "word32 => word32 => word32"  where
  "bitwise_and ==
%T1 T2.
   mk_word32 (EQUIV (AND (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"

lemma bitwise_and: "bitwise_and T1 T2 =
mk_word32 (EQUIV (AND (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"
  by (import word32 bitwise_and)

consts
  TOw :: "word32 => word32" 

defs
  TOw_primdef: "TOw == %T1. mk_word32 (EQUIV (MODw (Eps (dest_word32 T1))))"

lemma TOw_def: "TOw T1 = mk_word32 (EQUIV (MODw (Eps (dest_word32 T1))))"
  by (import word32 TOw_def)

consts
  n2w :: "nat => word32" 

defs
  n2w_primdef: "n2w == %n. mk_word32 (EQUIV n)"

lemma n2w_def: "n2w n = mk_word32 (EQUIV n)"
  by (import word32 n2w_def)

consts
  w2n :: "word32 => nat" 

defs
  w2n_primdef: "w2n == %w. MODw (Eps (dest_word32 w))"

lemma w2n_def: "w2n w = MODw (Eps (dest_word32 w))"
  by (import word32 w2n_def)

lemma ADDw: "(ALL x. word_add w_0 x = x) &
(ALL x xa. word_add (word_suc x) xa = word_suc (word_add x xa))"
  by (import word32 ADDw)

lemma ADD_0w: "word_add x w_0 = x"
  by (import word32 ADD_0w)

lemma ADD1w: "word_suc x = word_add x w_1"
  by (import word32 ADD1w)

lemma ADD_ASSOCw: "word_add x (word_add xa xb) = word_add (word_add x xa) xb"
  by (import word32 ADD_ASSOCw)

lemma ADD_CLAUSESw: "(ALL x. word_add w_0 x = x) &
(ALL x. word_add x w_0 = x) &
(ALL x xa. word_add (word_suc x) xa = word_suc (word_add x xa)) &
(ALL x xa. word_add x (word_suc xa) = word_suc (word_add x xa))"
  by (import word32 ADD_CLAUSESw)

lemma ADD_COMMw: "word_add x xa = word_add xa x"
  by (import word32 ADD_COMMw)

lemma ADD_INV_0_EQw: "(word_add x xa = x) = (xa = w_0)"
  by (import word32 ADD_INV_0_EQw)

lemma EQ_ADD_LCANCELw: "(word_add x xa = word_add x xb) = (xa = xb)"
  by (import word32 EQ_ADD_LCANCELw)

lemma EQ_ADD_RCANCELw: "(word_add x xb = word_add xa xb) = (x = xa)"
  by (import word32 EQ_ADD_RCANCELw)

lemma LEFT_ADD_DISTRIBw: "word_mul xb (word_add x xa) = word_add (word_mul xb x) (word_mul xb xa)"
  by (import word32 LEFT_ADD_DISTRIBw)

lemma MULT_ASSOCw: "word_mul x (word_mul xa xb) = word_mul (word_mul x xa) xb"
  by (import word32 MULT_ASSOCw)

lemma MULT_COMMw: "word_mul x xa = word_mul xa x"
  by (import word32 MULT_COMMw)

lemma MULT_CLAUSESw: "word_mul w_0 x = w_0 &
word_mul x w_0 = w_0 &
word_mul w_1 x = x &
word_mul x w_1 = x &
word_mul (word_suc x) xa = word_add (word_mul x xa) xa &
word_mul x (word_suc xa) = word_add x (word_mul x xa)"
  by (import word32 MULT_CLAUSESw)

lemma TWO_COMP_ONE_COMP: "word_2comp x = word_add (word_1comp x) w_1"
  by (import word32 TWO_COMP_ONE_COMP)

lemma OR_ASSOCw: "bitwise_or x (bitwise_or xa xb) = bitwise_or (bitwise_or x xa) xb"
  by (import word32 OR_ASSOCw)

lemma OR_COMMw: "bitwise_or x xa = bitwise_or xa x"
  by (import word32 OR_COMMw)

lemma OR_IDEMw: "bitwise_or x x = x"
  by (import word32 OR_IDEMw)

lemma OR_ABSORBw: "bitwise_and x (bitwise_or x xa) = x"
  by (import word32 OR_ABSORBw)

lemma AND_ASSOCw: "bitwise_and x (bitwise_and xa xb) = bitwise_and (bitwise_and x xa) xb"
  by (import word32 AND_ASSOCw)

lemma AND_COMMw: "bitwise_and x xa = bitwise_and xa x"
  by (import word32 AND_COMMw)

lemma AND_IDEMw: "bitwise_and x x = x"
  by (import word32 AND_IDEMw)

lemma AND_ABSORBw: "bitwise_or x (bitwise_and x xa) = x"
  by (import word32 AND_ABSORBw)

lemma ONE_COMPw: "word_1comp (word_1comp x) = x"
  by (import word32 ONE_COMPw)

lemma RIGHT_AND_OVER_ORw: "bitwise_and (bitwise_or x xa) xb =
bitwise_or (bitwise_and x xb) (bitwise_and xa xb)"
  by (import word32 RIGHT_AND_OVER_ORw)

lemma RIGHT_OR_OVER_ANDw: "bitwise_or (bitwise_and x xa) xb =
bitwise_and (bitwise_or x xb) (bitwise_or xa xb)"
  by (import word32 RIGHT_OR_OVER_ANDw)

lemma DE_MORGAN_THMw: "word_1comp (bitwise_and x xa) = bitwise_or (word_1comp x) (word_1comp xa) &
word_1comp (bitwise_or x xa) = bitwise_and (word_1comp x) (word_1comp xa)"
  by (import word32 DE_MORGAN_THMw)

lemma w_0: "w_0 = n2w 0"
  by (import word32 w_0)

lemma w_1: "w_1 = n2w 1"
  by (import word32 w_1)

lemma w_T: "w_T =
n2w (NUMERAL
      (NUMERAL_BIT1
        (NUMERAL_BIT1
          (NUMERAL_BIT1
            (NUMERAL_BIT1
              (NUMERAL_BIT1
                (NUMERAL_BIT1
                  (NUMERAL_BIT1
                    (NUMERAL_BIT1
                      (NUMERAL_BIT1
                        (NUMERAL_BIT1
                          (NUMERAL_BIT1
                            (NUMERAL_BIT1
                              (NUMERAL_BIT1
                                (NUMERAL_BIT1
                                  (NUMERAL_BIT1
                                    (NUMERAL_BIT1
(NUMERAL_BIT1
  (NUMERAL_BIT1
    (NUMERAL_BIT1
      (NUMERAL_BIT1
        (NUMERAL_BIT1
          (NUMERAL_BIT1
            (NUMERAL_BIT1
              (NUMERAL_BIT1
                (NUMERAL_BIT1
                  (NUMERAL_BIT1
                    (NUMERAL_BIT1
                      (NUMERAL_BIT1
                        (NUMERAL_BIT1
                          (NUMERAL_BIT1
                            (NUMERAL_BIT1
                              (NUMERAL_BIT1
                                ALT_ZERO)))))))))))))))))))))))))))))))))"
  by (import word32 w_T)

lemma ADD_TWO_COMP: "word_add x (word_2comp x) = w_0"
  by (import word32 ADD_TWO_COMP)

lemma ADD_TWO_COMP2: "word_add (word_2comp x) x = w_0"
  by (import word32 ADD_TWO_COMP2)

definition
  word_sub :: "word32 => word32 => word32"  where
  "word_sub == %a b. word_add a (word_2comp b)"

lemma word_sub: "word_sub a b = word_add a (word_2comp b)"
  by (import word32 word_sub)

definition
  word_lsl :: "word32 => nat => word32"  where
  "word_lsl == %a n. word_mul a (n2w (2 ^ n))"

lemma word_lsl: "word_lsl a n = word_mul a (n2w (2 ^ n))"
  by (import word32 word_lsl)

definition
  word_lsr :: "word32 => nat => word32"  where
  "word_lsr == %a n. (word_lsr1 ^^ n) a"

lemma word_lsr: "word_lsr a n = (word_lsr1 ^^ n) a"
  by (import word32 word_lsr)

definition
  word_asr :: "word32 => nat => word32"  where
  "word_asr == %a n. (word_asr1 ^^ n) a"

lemma word_asr: "word_asr a n = (word_asr1 ^^ n) a"
  by (import word32 word_asr)

definition
  word_ror :: "word32 => nat => word32"  where
  "word_ror == %a n. (word_ror1 ^^ n) a"

lemma word_ror: "word_ror a n = (word_ror1 ^^ n) a"
  by (import word32 word_ror)

consts
  BITw :: "nat => word32 => bool" 

defs
  BITw_primdef: "BITw == %b n. bit b (w2n n)"

lemma BITw_def: "BITw b n = bit b (w2n n)"
  by (import word32 BITw_def)

consts
  BITSw :: "nat => nat => word32 => nat" 

defs
  BITSw_primdef: "BITSw == %h l n. BITS h l (w2n n)"

lemma BITSw_def: "BITSw h l n = BITS h l (w2n n)"
  by (import word32 BITSw_def)

consts
  SLICEw :: "nat => nat => word32 => nat" 

defs
  SLICEw_primdef: "SLICEw == %h l n. SLICE h l (w2n n)"

lemma SLICEw_def: "SLICEw h l n = SLICE h l (w2n n)"
  by (import word32 SLICEw_def)

lemma TWO_COMP_ADD: "word_2comp (word_add a b) = word_add (word_2comp a) (word_2comp b)"
  by (import word32 TWO_COMP_ADD)

lemma TWO_COMP_ELIM: "word_2comp (word_2comp a) = a"
  by (import word32 TWO_COMP_ELIM)

lemma ADD_SUB_ASSOC: "word_sub (word_add a b) c = word_add a (word_sub b c)"
  by (import word32 ADD_SUB_ASSOC)

lemma ADD_SUB_SYM: "word_sub (word_add a b) c = word_add (word_sub a c) b"
  by (import word32 ADD_SUB_SYM)

lemma SUB_EQUALw: "word_sub a a = w_0"
  by (import word32 SUB_EQUALw)

lemma ADD_SUBw: "word_sub (word_add a b) b = a"
  by (import word32 ADD_SUBw)

lemma SUB_SUBw: "word_sub a (word_sub b c) = word_sub (word_add a c) b"
  by (import word32 SUB_SUBw)

lemma ONE_COMP_TWO_COMP: "word_1comp a = word_sub (word_2comp a) w_1"
  by (import word32 ONE_COMP_TWO_COMP)

lemma SUBw: "word_sub (word_suc m) n = word_suc (word_sub m n)"
  by (import word32 SUBw)

lemma ADD_EQ_SUBw: "(word_add m n = p) = (m = word_sub p n)"
  by (import word32 ADD_EQ_SUBw)

lemma CANCEL_SUBw: "(word_sub n p = word_sub m p) = (n = m)"
  by (import word32 CANCEL_SUBw)

lemma SUB_PLUSw: "word_sub a (word_add b c) = word_sub (word_sub a b) c"
  by (import word32 SUB_PLUSw)

lemma word_nchotomy: "EX n. w = n2w n"
  by (import word32 word_nchotomy)

lemma dest_word_mk_word_eq3: "dest_word32 (mk_word32 (EQUIV a)) = EQUIV a"
  by (import word32 dest_word_mk_word_eq3)

lemma MODw_ELIM: "n2w (MODw n) = n2w n"
  by (import word32 MODw_ELIM)

lemma w2n_EVAL: "w2n (n2w n) = MODw n"
  by (import word32 w2n_EVAL)

lemma w2n_ELIM: "n2w (w2n a) = a"
  by (import word32 w2n_ELIM)

lemma n2w_11: "(n2w a = n2w b) = (MODw a = MODw b)"
  by (import word32 n2w_11)

lemma ADD_EVAL: "word_add (n2w a) (n2w b) = n2w (a + b)"
  by (import word32 ADD_EVAL)

lemma MUL_EVAL: "word_mul (n2w a) (n2w b) = n2w (a * b)"
  by (import word32 MUL_EVAL)

lemma ONE_COMP_EVAL: "word_1comp (n2w a) = n2w (ONE_COMP a)"
  by (import word32 ONE_COMP_EVAL)

lemma TWO_COMP_EVAL: "word_2comp (n2w a) = n2w (TWO_COMP a)"
  by (import word32 TWO_COMP_EVAL)

lemma LSR_ONE_EVAL: "word_lsr1 (n2w a) = n2w (LSR_ONE a)"
  by (import word32 LSR_ONE_EVAL)

lemma ASR_ONE_EVAL: "word_asr1 (n2w a) = n2w (ASR_ONE a)"
  by (import word32 ASR_ONE_EVAL)

lemma ROR_ONE_EVAL: "word_ror1 (n2w a) = n2w (ROR_ONE a)"
  by (import word32 ROR_ONE_EVAL)

lemma RRX_EVAL: "RRX c (n2w a) = n2w (RRXn c a)"
  by (import word32 RRX_EVAL)

lemma LSB_EVAL: "LSB (n2w a) = LSBn a"
  by (import word32 LSB_EVAL)

lemma MSB_EVAL: "MSB (n2w a) = MSBn a"
  by (import word32 MSB_EVAL)

lemma OR_EVAL: "bitwise_or (n2w a) (n2w b) = n2w (OR a b)"
  by (import word32 OR_EVAL)

lemma EOR_EVAL: "bitwise_eor (n2w a) (n2w b) = n2w (EOR a b)"
  by (import word32 EOR_EVAL)

lemma AND_EVAL: "bitwise_and (n2w a) (n2w b) = n2w (AND a b)"
  by (import word32 AND_EVAL)

lemma BITS_EVAL: "BITSw h l (n2w a) = BITS h l (MODw a)"
  by (import word32 BITS_EVAL)

lemma BIT_EVAL: "BITw b (n2w a) = bit b (MODw a)"
  by (import word32 BIT_EVAL)

lemma SLICE_EVAL: "SLICEw h l (n2w a) = SLICE h l (MODw a)"
  by (import word32 SLICE_EVAL)

lemma LSL_ADD: "word_lsl (word_lsl a m) n = word_lsl a (m + n)"
  by (import word32 LSL_ADD)

lemma LSR_ADD: "word_lsr (word_lsr x xa) xb = word_lsr x (xa + xb)"
  by (import word32 LSR_ADD)

lemma ASR_ADD: "word_asr (word_asr x xa) xb = word_asr x (xa + xb)"
  by (import word32 ASR_ADD)

lemma ROR_ADD: "word_ror (word_ror x xa) xb = word_ror x (xa + xb)"
  by (import word32 ROR_ADD)

lemma LSL_LIMIT: "HB < n ==> word_lsl w n = w_0"
  by (import word32 LSL_LIMIT)

lemma MOD_MOD_DIV: "INw (MODw a div 2 ^ b)"
  by (import word32 MOD_MOD_DIV)

lemma MOD_MOD_DIV_2EXP: "MODw (MODw a div 2 ^ n) div 2 = MODw a div 2 ^ Suc n"
  by (import word32 MOD_MOD_DIV_2EXP)

lemma LSR_EVAL: "word_lsr (n2w a) n = n2w (MODw a div 2 ^ n)"
  by (import word32 LSR_EVAL)

lemma LSR_THM: "word_lsr (n2w n) x = n2w (BITS HB (min WL x) n)"
  by (import word32 LSR_THM)

lemma LSR_LIMIT: "HB < x ==> word_lsr w x = w_0"
  by (import word32 LSR_LIMIT)

lemma LEFT_SHIFT_LESS: "(a::nat) < (2::nat) ^ (m::nat)
==> (2::nat) ^ (n::nat) + a * (2::nat) ^ n <= (2::nat) ^ (m + n)"
  by (import word32 LEFT_SHIFT_LESS)

lemma ROR_THM: "word_ror (n2w n) x =
(let x' = x mod WL
 in n2w (BITS HB x' n + BITS (x' - 1) 0 n * 2 ^ (WL - x')))"
  by (import word32 ROR_THM)

lemma ROR_CYCLE: "word_ror w (x * WL) = w"
  by (import word32 ROR_CYCLE)

lemma ASR_THM: "word_asr (n2w n) x =
(let x' = min HB x; s = BITS HB x' n
 in n2w (if MSBn n then 2 ^ WL - 2 ^ (WL - x') + s else s))"
  by (import word32 ASR_THM)

lemma ASR_LIMIT: "HB <= x ==> word_asr w x = (if MSB w then w_T else w_0)"
  by (import word32 ASR_LIMIT)

lemma ZERO_SHIFT: "(ALL n. word_lsl w_0 n = w_0) &
(ALL n. word_asr w_0 n = w_0) &
(ALL n. word_lsr w_0 n = w_0) & (ALL n. word_ror w_0 n = w_0)"
  by (import word32 ZERO_SHIFT)

lemma ZERO_SHIFT2: "(ALL a. word_lsl a 0 = a) &
(ALL a. word_asr a 0 = a) &
(ALL a. word_lsr a 0 = a) & (ALL a. word_ror a 0 = a)"
  by (import word32 ZERO_SHIFT2)

lemma ASR_w_T: "word_asr w_T n = w_T"
  by (import word32 ASR_w_T)

lemma ROR_w_T: "word_ror w_T n = w_T"
  by (import word32 ROR_w_T)

lemma MODw_EVAL: "MODw x =
x mod
NUMERAL
 (NUMERAL_BIT2
   (NUMERAL_BIT1
     (NUMERAL_BIT1
       (NUMERAL_BIT1
         (NUMERAL_BIT1
           (NUMERAL_BIT1
             (NUMERAL_BIT1
               (NUMERAL_BIT1
                 (NUMERAL_BIT1
                   (NUMERAL_BIT1
                     (NUMERAL_BIT1
                       (NUMERAL_BIT1
                         (NUMERAL_BIT1
                           (NUMERAL_BIT1
                             (NUMERAL_BIT1
                               (NUMERAL_BIT1
                                 (NUMERAL_BIT1
                                   (NUMERAL_BIT1
                                     (NUMERAL_BIT1
 (NUMERAL_BIT1
   (NUMERAL_BIT1
     (NUMERAL_BIT1
       (NUMERAL_BIT1
         (NUMERAL_BIT1
           (NUMERAL_BIT1
             (NUMERAL_BIT1
               (NUMERAL_BIT1
                 (NUMERAL_BIT1
                   (NUMERAL_BIT1
                     (NUMERAL_BIT1
                       (NUMERAL_BIT1
                         (NUMERAL_BIT1
                           ALT_ZERO))))))))))))))))))))))))))))))))"
  by (import word32 MODw_EVAL)

lemma ADD_EVAL2: "word_add (n2w a) (n2w b) = n2w (MODw (a + b))"
  by (import word32 ADD_EVAL2)

lemma MUL_EVAL2: "word_mul (n2w a) (n2w b) = n2w (MODw (a * b))"
  by (import word32 MUL_EVAL2)

lemma ONE_COMP_EVAL2: "word_1comp (n2w a) =
n2w (2 ^
     NUMERAL
      (NUMERAL_BIT2
        (NUMERAL_BIT1
          (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))) -
     1 -
     MODw a)"
  by (import word32 ONE_COMP_EVAL2)

lemma TWO_COMP_EVAL2: "word_2comp (n2w a) =
n2w (MODw
      (2 ^
       NUMERAL
        (NUMERAL_BIT2
          (NUMERAL_BIT1
            (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))) -
       MODw a))"
  by (import word32 TWO_COMP_EVAL2)

lemma LSR_ONE_EVAL2: "word_lsr1 (n2w a) = n2w (MODw a div 2)"
  by (import word32 LSR_ONE_EVAL2)

lemma ASR_ONE_EVAL2: "word_asr1 (n2w a) =
n2w (MODw a div 2 +
     SBIT (MSBn a)
      (NUMERAL
        (NUMERAL_BIT1
          (NUMERAL_BIT1
            (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO)))))))"
  by (import word32 ASR_ONE_EVAL2)

lemma ROR_ONE_EVAL2: "word_ror1 (n2w a) =
n2w (MODw a div 2 +
     SBIT (LSBn a)
      (NUMERAL
        (NUMERAL_BIT1
          (NUMERAL_BIT1
            (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO)))))))"
  by (import word32 ROR_ONE_EVAL2)

lemma RRX_EVAL2: "RRX c (n2w a) =
n2w (MODw a div 2 +
     SBIT c
      (NUMERAL
        (NUMERAL_BIT1
          (NUMERAL_BIT1
            (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO)))))))"
  by (import word32 RRX_EVAL2)

lemma LSB_EVAL2: "LSB (n2w a) = ODD a"
  by (import word32 LSB_EVAL2)

lemma MSB_EVAL2: "MSB (n2w a) =
bit (NUMERAL
      (NUMERAL_BIT1
        (NUMERAL_BIT1
          (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))))
 a"
  by (import word32 MSB_EVAL2)

lemma OR_EVAL2: "bitwise_or (n2w a) (n2w b) =
n2w (BITWISE
      (NUMERAL
        (NUMERAL_BIT2
          (NUMERAL_BIT1
            (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))))
      op | a b)"
  by (import word32 OR_EVAL2)

lemma AND_EVAL2: "bitwise_and (n2w a) (n2w b) =
n2w (BITWISE
      (NUMERAL
        (NUMERAL_BIT2
          (NUMERAL_BIT1
            (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))))
      op & a b)"
  by (import word32 AND_EVAL2)

lemma EOR_EVAL2: "bitwise_eor (n2w a) (n2w b) =
n2w (BITWISE
      (NUMERAL
        (NUMERAL_BIT2
          (NUMERAL_BIT1
            (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))))
      op ~= a b)"
  by (import word32 EOR_EVAL2)

lemma BITWISE_EVAL2: "BITWISE n oper x y =
(if n = 0 then 0
 else 2 * BITWISE (n - 1) oper (x div 2) (y div 2) +
      (if oper (ODD x) (ODD y) then 1 else 0))"
  by (import word32 BITWISE_EVAL2)

lemma BITSwLT_THM: "BITSw h l n < 2 ^ (Suc h - l)"
  by (import word32 BITSwLT_THM)

lemma BITSw_COMP_THM: "h2 + l1 <= h1 ==> BITS h2 l2 (BITSw h1 l1 n) = BITSw (h2 + l1) (l2 + l1) n"
  by (import word32 BITSw_COMP_THM)

lemma BITSw_DIV_THM: "BITSw h l x div 2 ^ n = BITSw h (l + n) x"
  by (import word32 BITSw_DIV_THM)

lemma BITw_THM: "BITw b n = (BITSw b b n = 1)"
  by (import word32 BITw_THM)

lemma SLICEw_THM: "SLICEw h l n = BITSw h l n * 2 ^ l"
  by (import word32 SLICEw_THM)

lemma BITS_SLICEw_THM: "BITS h l (SLICEw h l n) = BITSw h l n"
  by (import word32 BITS_SLICEw_THM)

lemma SLICEw_ZERO_THM: "SLICEw h 0 n = BITSw h 0 n"
  by (import word32 SLICEw_ZERO_THM)

lemma SLICEw_COMP_THM: "Suc m <= h & l <= m ==> SLICEw h (Suc m) a + SLICEw m l a = SLICEw h l a"
  by (import word32 SLICEw_COMP_THM)

lemma BITSw_ZERO: "h < l ==> BITSw h l n = 0"
  by (import word32 BITSw_ZERO)

lemma SLICEw_ZERO: "h < l ==> SLICEw h l n = 0"
  by (import word32 SLICEw_ZERO)

;end_setup

end

