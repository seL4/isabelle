(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOL4Word32 imports HOL4Base begin

;setup_theory bits

consts
  DIV2 :: "nat => nat" 

defs
  DIV2_primdef: "DIV2 == %n::nat. n div 2"

lemma DIV2_def: "ALL n::nat. DIV2 n = n div 2"
  by (import bits DIV2_def)

consts
  TIMES_2EXP :: "nat => nat => nat" 

defs
  TIMES_2EXP_primdef: "TIMES_2EXP == %(x::nat) n::nat. n * 2 ^ x"

lemma TIMES_2EXP_def: "ALL (x::nat) n::nat. TIMES_2EXP x n = n * 2 ^ x"
  by (import bits TIMES_2EXP_def)

consts
  DIV_2EXP :: "nat => nat => nat" 

defs
  DIV_2EXP_primdef: "DIV_2EXP == %(x::nat) n::nat. n div 2 ^ x"

lemma DIV_2EXP_def: "ALL (x::nat) n::nat. DIV_2EXP x n = n div 2 ^ x"
  by (import bits DIV_2EXP_def)

consts
  MOD_2EXP :: "nat => nat => nat" 

defs
  MOD_2EXP_primdef: "MOD_2EXP == %(x::nat) n::nat. n mod 2 ^ x"

lemma MOD_2EXP_def: "ALL (x::nat) n::nat. MOD_2EXP x n = n mod 2 ^ x"
  by (import bits MOD_2EXP_def)

consts
  DIVMOD_2EXP :: "nat => nat => nat * nat" 

defs
  DIVMOD_2EXP_primdef: "DIVMOD_2EXP == %(x::nat) n::nat. (n div 2 ^ x, n mod 2 ^ x)"

lemma DIVMOD_2EXP_def: "ALL (x::nat) n::nat. DIVMOD_2EXP x n = (n div 2 ^ x, n mod 2 ^ x)"
  by (import bits DIVMOD_2EXP_def)

consts
  SBIT :: "bool => nat => nat" 

defs
  SBIT_primdef: "SBIT == %(b::bool) n::nat. if b then 2 ^ n else 0"

lemma SBIT_def: "ALL (b::bool) n::nat. SBIT b n = (if b then 2 ^ n else 0)"
  by (import bits SBIT_def)

consts
  BITS :: "nat => nat => nat => nat" 

defs
  BITS_primdef: "BITS == %(h::nat) (l::nat) n::nat. MOD_2EXP (Suc h - l) (DIV_2EXP l n)"

lemma BITS_def: "ALL (h::nat) (l::nat) n::nat.
   BITS h l n = MOD_2EXP (Suc h - l) (DIV_2EXP l n)"
  by (import bits BITS_def)

constdefs
  bit :: "nat => nat => bool" 
  "bit == %(b::nat) n::nat. BITS b b n = 1"

lemma BIT_def: "ALL (b::nat) n::nat. bit b n = (BITS b b n = 1)"
  by (import bits BIT_def)

consts
  SLICE :: "nat => nat => nat => nat" 

defs
  SLICE_primdef: "SLICE == %(h::nat) (l::nat) n::nat. MOD_2EXP (Suc h) n - MOD_2EXP l n"

lemma SLICE_def: "ALL (h::nat) (l::nat) n::nat.
   SLICE h l n = MOD_2EXP (Suc h) n - MOD_2EXP l n"
  by (import bits SLICE_def)

consts
  LSBn :: "nat => bool" 

defs
  LSBn_primdef: "LSBn == bit 0"

lemma LSBn_def: "LSBn = bit 0"
  by (import bits LSBn_def)

consts
  BITWISE :: "nat => (bool => bool => bool) => nat => nat => nat" 

specification (BITWISE_primdef: BITWISE) BITWISE_def: "(ALL (oper::bool => bool => bool) (x::nat) y::nat. BITWISE 0 oper x y = 0) &
(ALL (n::nat) (oper::bool => bool => bool) (x::nat) y::nat.
    BITWISE (Suc n) oper x y =
    BITWISE n oper x y + SBIT (oper (bit n x) (bit n y)) n)"
  by (import bits BITWISE_def)

lemma DIV1: "ALL x::nat. x div 1 = x"
  by (import bits DIV1)

lemma SUC_SUB: "Suc (a::nat) - a = 1"
  by (import bits SUC_SUB)

lemma DIV_MULT_1: "ALL (r::nat) n::nat. r < n --> (n + r) div n = 1"
  by (import bits DIV_MULT_1)

lemma ZERO_LT_TWOEXP: "(All::(nat => bool) => bool)
 (%n::nat.
     (op <::nat => nat => bool) (0::nat)
      ((op ^::nat => nat => nat)
        ((number_of::bin => nat)
          ((op BIT::bin => bit => bin)
            ((op BIT::bin => bit => bin) (Numeral.Pls::bin) (bit.B1::bit))
            (bit.B0::bit)))
        n))"
  by (import bits ZERO_LT_TWOEXP)

lemma MOD_2EXP_LT: "ALL (n::nat) k::nat. k mod 2 ^ n < 2 ^ n"
  by (import bits MOD_2EXP_LT)

lemma TWOEXP_DIVISION: "ALL (n::nat) k::nat. k = k div 2 ^ n * 2 ^ n + k mod 2 ^ n"
  by (import bits TWOEXP_DIVISION)

lemma TWOEXP_MONO: "(All::(nat => bool) => bool)
 (%a::nat.
     (All::(nat => bool) => bool)
      (%b::nat.
          (op -->::bool => bool => bool) ((op <::nat => nat => bool) a b)
           ((op <::nat => nat => bool)
             ((op ^::nat => nat => nat)
               ((number_of::bin => nat)
                 ((op BIT::bin => bit => bin)
                   ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                     (bit.B1::bit))
                   (bit.B0::bit)))
               a)
             ((op ^::nat => nat => nat)
               ((number_of::bin => nat)
                 ((op BIT::bin => bit => bin)
                   ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                     (bit.B1::bit))
                   (bit.B0::bit)))
               b))))"
  by (import bits TWOEXP_MONO)

lemma TWOEXP_MONO2: "(All::(nat => bool) => bool)
 (%a::nat.
     (All::(nat => bool) => bool)
      (%b::nat.
          (op -->::bool => bool => bool) ((op <=::nat => nat => bool) a b)
           ((op <=::nat => nat => bool)
             ((op ^::nat => nat => nat)
               ((number_of::bin => nat)
                 ((op BIT::bin => bit => bin)
                   ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                     (bit.B1::bit))
                   (bit.B0::bit)))
               a)
             ((op ^::nat => nat => nat)
               ((number_of::bin => nat)
                 ((op BIT::bin => bit => bin)
                   ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                     (bit.B1::bit))
                   (bit.B0::bit)))
               b))))"
  by (import bits TWOEXP_MONO2)

lemma EXP_SUB_LESS_EQ: "(All::(nat => bool) => bool)
 (%a::nat.
     (All::(nat => bool) => bool)
      (%b::nat.
          (op <=::nat => nat => bool)
           ((op ^::nat => nat => nat)
             ((number_of::bin => nat)
               ((op BIT::bin => bit => bin)
                 ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                   (bit.B1::bit))
                 (bit.B0::bit)))
             ((op -::nat => nat => nat) a b))
           ((op ^::nat => nat => nat)
             ((number_of::bin => nat)
               ((op BIT::bin => bit => bin)
                 ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                   (bit.B1::bit))
                 (bit.B0::bit)))
             a)))"
  by (import bits EXP_SUB_LESS_EQ)

lemma BITS_THM: "ALL (x::nat) (xa::nat) xb::nat.
   BITS x xa xb = xb div 2 ^ xa mod 2 ^ (Suc x - xa)"
  by (import bits BITS_THM)

lemma BITSLT_THM: "ALL (h::nat) (l::nat) n::nat. BITS h l n < 2 ^ (Suc h - l)"
  by (import bits BITSLT_THM)

lemma DIV_MULT_LEM: "ALL (m::nat) n::nat. 0 < n --> m div n * n <= m"
  by (import bits DIV_MULT_LEM)

lemma MOD_2EXP_LEM: "ALL (n::nat) x::nat. n mod 2 ^ x = n - n div 2 ^ x * 2 ^ x"
  by (import bits MOD_2EXP_LEM)

lemma BITS2_THM: "ALL (h::nat) (l::nat) n::nat. BITS h l n = n mod 2 ^ Suc h div 2 ^ l"
  by (import bits BITS2_THM)

lemma BITS_COMP_THM: "ALL (h1::nat) (l1::nat) (h2::nat) (l2::nat) n::nat.
   h2 + l1 <= h1 --> BITS h2 l2 (BITS h1 l1 n) = BITS (h2 + l1) (l2 + l1) n"
  by (import bits BITS_COMP_THM)

lemma BITS_DIV_THM: "ALL (h::nat) (l::nat) (x::nat) n::nat.
   BITS h l x div 2 ^ n = BITS h (l + n) x"
  by (import bits BITS_DIV_THM)

lemma BITS_LT_HIGH: "ALL (h::nat) (l::nat) n::nat. n < 2 ^ Suc h --> BITS h l n = n div 2 ^ l"
  by (import bits BITS_LT_HIGH)

lemma BITS_ZERO: "ALL (h::nat) (l::nat) n::nat. h < l --> BITS h l n = 0"
  by (import bits BITS_ZERO)

lemma BITS_ZERO2: "ALL (h::nat) l::nat. BITS h l 0 = 0"
  by (import bits BITS_ZERO2)

lemma BITS_ZERO3: "ALL (h::nat) x::nat. BITS h 0 x = x mod 2 ^ Suc h"
  by (import bits BITS_ZERO3)

lemma BITS_COMP_THM2: "ALL (h1::nat) (l1::nat) (h2::nat) (l2::nat) n::nat.
   BITS h2 l2 (BITS h1 l1 n) = BITS (min h1 (h2 + l1)) (l2 + l1) n"
  by (import bits BITS_COMP_THM2)

lemma NOT_MOD2_LEM: "ALL n::nat. (n mod 2 ~= 0) = (n mod 2 = 1)"
  by (import bits NOT_MOD2_LEM)

lemma NOT_MOD2_LEM2: "ALL (n::nat) a::'a::type. (n mod 2 ~= 1) = (n mod 2 = 0)"
  by (import bits NOT_MOD2_LEM2)

lemma EVEN_MOD2_LEM: "ALL n::nat. EVEN n = (n mod 2 = 0)"
  by (import bits EVEN_MOD2_LEM)

lemma ODD_MOD2_LEM: "ALL n::nat. ODD n = (n mod 2 = 1)"
  by (import bits ODD_MOD2_LEM)

lemma LSB_ODD: "LSBn = ODD"
  by (import bits LSB_ODD)

lemma DIV_MULT_THM: "ALL (x::nat) n::nat. n div 2 ^ x * 2 ^ x = n - n mod 2 ^ x"
  by (import bits DIV_MULT_THM)

lemma DIV_MULT_THM2: "ALL x::nat. 2 * (x div 2) = x - x mod 2"
  by (import bits DIV_MULT_THM2)

lemma LESS_EQ_EXP_MULT: "ALL (a::nat) b::nat. a <= b --> (EX x::nat. 2 ^ b = x * 2 ^ a)"
  by (import bits LESS_EQ_EXP_MULT)

lemma SLICE_LEM1: "ALL (a::nat) (x::nat) y::nat.
   a div 2 ^ (x + y) * 2 ^ (x + y) =
   a div 2 ^ x * 2 ^ x - a div 2 ^ x mod 2 ^ y * 2 ^ x"
  by (import bits SLICE_LEM1)

lemma SLICE_LEM2: "ALL (a::'a::type) (x::nat) y::nat.
   (n::nat) mod 2 ^ (x + y) = n mod 2 ^ x + n div 2 ^ x mod 2 ^ y * 2 ^ x"
  by (import bits SLICE_LEM2)

lemma SLICE_LEM3: "ALL (n::nat) (h::nat) l::nat. l < h --> n mod 2 ^ Suc l <= n mod 2 ^ h"
  by (import bits SLICE_LEM3)

lemma SLICE_THM: "ALL (n::nat) (h::nat) l::nat. SLICE h l n = BITS h l n * 2 ^ l"
  by (import bits SLICE_THM)

lemma SLICELT_THM: "ALL (h::nat) (l::nat) n::nat. SLICE h l n < 2 ^ Suc h"
  by (import bits SLICELT_THM)

lemma BITS_SLICE_THM: "ALL (h::nat) (l::nat) n::nat. BITS h l (SLICE h l n) = BITS h l n"
  by (import bits BITS_SLICE_THM)

lemma BITS_SLICE_THM2: "ALL (h::nat) (l::nat) n::nat.
   h <= (h2::nat) --> BITS h2 l (SLICE h l n) = BITS h l n"
  by (import bits BITS_SLICE_THM2)

lemma MOD_2EXP_MONO: "ALL (n::nat) (h::nat) l::nat. l <= h --> n mod 2 ^ l <= n mod 2 ^ Suc h"
  by (import bits MOD_2EXP_MONO)

lemma SLICE_COMP_THM: "ALL (h::nat) (m::nat) (l::nat) n::nat.
   Suc m <= h & l <= m --> SLICE h (Suc m) n + SLICE m l n = SLICE h l n"
  by (import bits SLICE_COMP_THM)

lemma SLICE_ZERO: "ALL (h::nat) (l::nat) n::nat. h < l --> SLICE h l n = 0"
  by (import bits SLICE_ZERO)

lemma BIT_COMP_THM3: "ALL (h::nat) (m::nat) (l::nat) n::nat.
   Suc m <= h & l <= m -->
   BITS h (Suc m) n * 2 ^ (Suc m - l) + BITS m l n = BITS h l n"
  by (import bits BIT_COMP_THM3)

lemma NOT_BIT: "ALL (n::nat) a::nat. (~ bit n a) = (BITS n n a = 0)"
  by (import bits NOT_BIT)

lemma NOT_BITS: "ALL (n::nat) a::nat. (BITS n n a ~= 0) = (BITS n n a = 1)"
  by (import bits NOT_BITS)

lemma NOT_BITS2: "ALL (n::nat) a::nat. (BITS n n a ~= 1) = (BITS n n a = 0)"
  by (import bits NOT_BITS2)

lemma BIT_SLICE: "ALL (n::nat) (a::nat) b::nat.
   (bit n a = bit n b) = (SLICE n n a = SLICE n n b)"
  by (import bits BIT_SLICE)

lemma BIT_SLICE_LEM: "ALL (y::nat) (x::nat) n::nat. SBIT (bit x n) (x + y) = SLICE x x n * 2 ^ y"
  by (import bits BIT_SLICE_LEM)

lemma BIT_SLICE_THM: "ALL (x::nat) xa::nat. SBIT (bit x xa) x = SLICE x x xa"
  by (import bits BIT_SLICE_THM)

lemma SBIT_DIV: "ALL (b::bool) (m::nat) n::nat. n < m --> SBIT b (m - n) = SBIT b m div 2 ^ n"
  by (import bits SBIT_DIV)

lemma BITS_SUC: "ALL (h::nat) (l::nat) n::nat.
   l <= Suc h -->
   SBIT (bit (Suc h) n) (Suc h - l) + BITS h l n = BITS (Suc h) l n"
  by (import bits BITS_SUC)

lemma BITS_SUC_THM: "ALL (h::nat) (l::nat) n::nat.
   BITS (Suc h) l n =
   (if Suc h < l then 0 else SBIT (bit (Suc h) n) (Suc h - l) + BITS h l n)"
  by (import bits BITS_SUC_THM)

lemma BIT_BITS_THM: "ALL (h::nat) (l::nat) (a::nat) b::nat.
   (ALL x::nat. l <= x & x <= h --> bit x a = bit x b) =
   (BITS h l a = BITS h l b)"
  by (import bits BIT_BITS_THM)

lemma BITWISE_LT_2EXP: "ALL (n::nat) (oper::bool => bool => bool) (a::nat) b::nat.
   BITWISE n oper a b < 2 ^ n"
  by (import bits BITWISE_LT_2EXP)

lemma LESS_EXP_MULT2: "(All::(nat => bool) => bool)
 (%a::nat.
     (All::(nat => bool) => bool)
      (%b::nat.
          (op -->::bool => bool => bool) ((op <::nat => nat => bool) a b)
           ((Ex::(nat => bool) => bool)
             (%x::nat.
                 (op =::nat => nat => bool)
                  ((op ^::nat => nat => nat)
                    ((number_of::bin => nat)
                      ((op BIT::bin => bit => bin)
                        ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                          (bit.B1::bit))
                        (bit.B0::bit)))
                    b)
                  ((op *::nat => nat => nat)
                    ((op ^::nat => nat => nat)
                      ((number_of::bin => nat)
                        ((op BIT::bin => bit => bin)
                          ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                            (bit.B1::bit))
                          (bit.B0::bit)))
                      ((op +::nat => nat => nat) x (1::nat)))
                    ((op ^::nat => nat => nat)
                      ((number_of::bin => nat)
                        ((op BIT::bin => bit => bin)
                          ((op BIT::bin => bit => bin) (Numeral.Pls::bin)
                            (bit.B1::bit))
                          (bit.B0::bit)))
                      a))))))"
  by (import bits LESS_EXP_MULT2)

lemma BITWISE_THM: "ALL (x::nat) (n::nat) (oper::bool => bool => bool) (a::nat) b::nat.
   x < n --> bit x (BITWISE n oper a b) = oper (bit x a) (bit x b)"
  by (import bits BITWISE_THM)

lemma BITWISE_COR: "ALL (x::nat) (n::nat) (oper::bool => bool => bool) (a::nat) b::nat.
   x < n -->
   oper (bit x a) (bit x b) --> BITWISE n oper a b div 2 ^ x mod 2 = 1"
  by (import bits BITWISE_COR)

lemma BITWISE_NOT_COR: "ALL (x::nat) (n::nat) (oper::bool => bool => bool) (a::nat) b::nat.
   x < n -->
   ~ oper (bit x a) (bit x b) --> BITWISE n oper a b div 2 ^ x mod 2 = 0"
  by (import bits BITWISE_NOT_COR)

lemma MOD_PLUS_RIGHT: "ALL n>0. ALL (j::nat) k::nat. (j + k mod n) mod n = (j + k) mod n"
  by (import bits MOD_PLUS_RIGHT)

lemma MOD_PLUS_1: "ALL n>0. ALL x::nat. ((x + 1) mod n = 0) = (x mod n + 1 = n)"
  by (import bits MOD_PLUS_1)

lemma MOD_ADD_1: "ALL n>0. ALL x::nat. (x + 1) mod n ~= 0 --> (x + 1) mod n = x mod n + 1"
  by (import bits MOD_ADD_1)

;end_setup

;setup_theory word32

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
  MODw_primdef: "MODw == %n::nat. n mod 2 ^ WL"

lemma MODw_def: "ALL n::nat. MODw n = n mod 2 ^ WL"
  by (import word32 MODw_def)

consts
  INw :: "nat => bool" 

defs
  INw_primdef: "INw == %n::nat. n < 2 ^ WL"

lemma INw_def: "ALL n::nat. INw n = (n < 2 ^ WL)"
  by (import word32 INw_def)

consts
  EQUIV :: "nat => nat => bool" 

defs
  EQUIV_primdef: "EQUIV == %(x::nat) y::nat. MODw x = MODw y"

lemma EQUIV_def: "ALL (x::nat) y::nat. EQUIV x y = (MODw x = MODw y)"
  by (import word32 EQUIV_def)

lemma EQUIV_QT: "ALL (x::nat) y::nat. EQUIV x y = (EQUIV x = EQUIV y)"
  by (import word32 EQUIV_QT)

lemma FUNPOW_THM: "ALL (f::'a::type => 'a::type) (n::nat) x::'a::type.
   (f ^ n) (f x) = f ((f ^ n) x)"
  by (import word32 FUNPOW_THM)

lemma FUNPOW_THM2: "ALL (f::'a::type => 'a::type) (n::nat) x::'a::type.
   (f ^ Suc n) x = f ((f ^ n) x)"
  by (import word32 FUNPOW_THM2)

lemma FUNPOW_COMP: "ALL (f::'a::type => 'a::type) (m::nat) (n::nat) a::'a::type.
   (f ^ m) ((f ^ n) a) = (f ^ (m + n)) a"
  by (import word32 FUNPOW_COMP)

lemma INw_MODw: "ALL n::nat. INw (MODw n)"
  by (import word32 INw_MODw)

lemma TOw_IDEM: "ALL a::nat. INw a --> MODw a = a"
  by (import word32 TOw_IDEM)

lemma MODw_IDEM2: "ALL a::nat. MODw (MODw a) = MODw a"
  by (import word32 MODw_IDEM2)

lemma TOw_QT: "ALL a::nat. EQUIV (MODw a) a"
  by (import word32 TOw_QT)

lemma MODw_THM: "MODw = BITS HB 0"
  by (import word32 MODw_THM)

lemma MOD_ADD: "ALL (a::nat) b::nat. MODw (a + b) = MODw (MODw a + MODw b)"
  by (import word32 MOD_ADD)

lemma MODw_MULT: "ALL (a::nat) b::nat. MODw (a * b) = MODw (MODw a * MODw b)"
  by (import word32 MODw_MULT)

consts
  AONE :: "nat" 

defs
  AONE_primdef: "AONE == 1"

lemma AONE_def: "AONE = 1"
  by (import word32 AONE_def)

lemma ADD_QT: "(ALL n::nat. EQUIV (0 + n) n) &
(ALL (m::nat) n::nat. EQUIV (Suc m + n) (Suc (m + n)))"
  by (import word32 ADD_QT)

lemma ADD_0_QT: "ALL a::nat. EQUIV (a + 0) a"
  by (import word32 ADD_0_QT)

lemma ADD_COMM_QT: "ALL (a::nat) b::nat. EQUIV (a + b) (b + a)"
  by (import word32 ADD_COMM_QT)

lemma ADD_ASSOC_QT: "ALL (a::nat) (b::nat) c::nat. EQUIV (a + (b + c)) (a + b + c)"
  by (import word32 ADD_ASSOC_QT)

lemma MULT_QT: "(ALL n::nat. EQUIV (0 * n) 0) &
(ALL (m::nat) n::nat. EQUIV (Suc m * n) (m * n + n))"
  by (import word32 MULT_QT)

lemma ADD1_QT: "ALL m::nat. EQUIV (Suc m) (m + AONE)"
  by (import word32 ADD1_QT)

lemma ADD_CLAUSES_QT: "(ALL m::nat. EQUIV (0 + m) m) &
(ALL m::nat. EQUIV (m + 0) m) &
(ALL (m::nat) n::nat. EQUIV (Suc m + n) (Suc (m + n))) &
(ALL (m::nat) n::nat. EQUIV (m + Suc n) (Suc (m + n)))"
  by (import word32 ADD_CLAUSES_QT)

lemma SUC_EQUIV_COMP: "ALL (a::nat) b::nat. EQUIV (Suc a) b --> EQUIV a (b + (2 ^ WL - 1))"
  by (import word32 SUC_EQUIV_COMP)

lemma INV_SUC_EQ_QT: "ALL (m::nat) n::nat. EQUIV (Suc m) (Suc n) = EQUIV m n"
  by (import word32 INV_SUC_EQ_QT)

lemma ADD_INV_0_QT: "ALL (m::nat) n::nat. EQUIV (m + n) m --> EQUIV n 0"
  by (import word32 ADD_INV_0_QT)

lemma ADD_INV_0_EQ_QT: "ALL (m::nat) n::nat. EQUIV (m + n) m = EQUIV n 0"
  by (import word32 ADD_INV_0_EQ_QT)

lemma EQ_ADD_LCANCEL_QT: "ALL (m::nat) (n::nat) p::nat. EQUIV (m + n) (m + p) = EQUIV n p"
  by (import word32 EQ_ADD_LCANCEL_QT)

lemma EQ_ADD_RCANCEL_QT: "ALL (x::nat) (xa::nat) xb::nat. EQUIV (x + xb) (xa + xb) = EQUIV x xa"
  by (import word32 EQ_ADD_RCANCEL_QT)

lemma LEFT_ADD_DISTRIB_QT: "ALL (m::nat) (n::nat) p::nat. EQUIV (p * (m + n)) (p * m + p * n)"
  by (import word32 LEFT_ADD_DISTRIB_QT)

lemma MULT_ASSOC_QT: "ALL (m::nat) (n::nat) p::nat. EQUIV (m * (n * p)) (m * n * p)"
  by (import word32 MULT_ASSOC_QT)

lemma MULT_COMM_QT: "ALL (m::nat) n::nat. EQUIV (m * n) (n * m)"
  by (import word32 MULT_COMM_QT)

lemma MULT_CLAUSES_QT: "ALL (m::nat) n::nat.
   EQUIV (0 * m) 0 &
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
  ONE_COMP_primdef: "ONE_COMP == %x::nat. 2 ^ WL - 1 - MODw x"

lemma ONE_COMP_def: "ALL x::nat. ONE_COMP x = 2 ^ WL - 1 - MODw x"
  by (import word32 ONE_COMP_def)

consts
  TWO_COMP :: "nat => nat" 

defs
  TWO_COMP_primdef: "TWO_COMP == %x::nat. 2 ^ WL - MODw x"

lemma TWO_COMP_def: "ALL x::nat. TWO_COMP x = 2 ^ WL - MODw x"
  by (import word32 TWO_COMP_def)

lemma ADD_TWO_COMP_QT: "ALL a::nat. EQUIV (MODw a + TWO_COMP a) 0"
  by (import word32 ADD_TWO_COMP_QT)

lemma TWO_COMP_ONE_COMP_QT: "ALL a::nat. EQUIV (TWO_COMP a) (ONE_COMP a + AONE)"
  by (import word32 TWO_COMP_ONE_COMP_QT)

lemma BIT_EQUIV_THM: "(All::(nat => bool) => bool)
 (%x::nat.
     (All::(nat => bool) => bool)
      (%xa::nat.
          (op =::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%xb::nat.
                 (op -->::bool => bool => bool)
                  ((op <::nat => nat => bool) xb (WL::nat))
                  ((op =::bool => bool => bool)
                    ((bit::nat => nat => bool) xb x)
                    ((bit::nat => nat => bool) xb xa))))
           ((EQUIV::nat => nat => bool) x xa)))"
  by (import word32 BIT_EQUIV_THM)

lemma BITS_SUC2: "ALL (n::nat) a::nat. BITS (Suc n) 0 a = SLICE (Suc n) (Suc n) a + BITS n 0 a"
  by (import word32 BITS_SUC2)

lemma BITWISE_ONE_COMP_THM: "ALL (a::nat) b::nat. BITWISE WL (%(x::bool) y::bool. ~ x) a b = ONE_COMP a"
  by (import word32 BITWISE_ONE_COMP_THM)

lemma ONE_COMP_THM: "ALL (x::nat) xa::nat. xa < WL --> bit xa (ONE_COMP x) = (~ bit xa x)"
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
  EOR_primdef: "EOR == BITWISE WL (%(x::bool) y::bool. x ~= y)"

lemma EOR_def: "EOR = BITWISE WL (%(x::bool) y::bool. x ~= y)"
  by (import word32 EOR_def)

consts
  COMP0 :: "nat" 

defs
  COMP0_primdef: "COMP0 == ONE_COMP 0"

lemma COMP0_def: "COMP0 = ONE_COMP 0"
  by (import word32 COMP0_def)

lemma BITWISE_THM2: "(All::(nat => bool) => bool)
 (%y::nat.
     (All::((bool => bool => bool) => bool) => bool)
      (%oper::bool => bool => bool.
          (All::(nat => bool) => bool)
           (%a::nat.
               (All::(nat => bool) => bool)
                (%b::nat.
                    (op =::bool => bool => bool)
                     ((All::(nat => bool) => bool)
                       (%x::nat.
                           (op -->::bool => bool => bool)
                            ((op <::nat => nat => bool) x (WL::nat))
                            ((op =::bool => bool => bool)
                              (oper ((bit::nat => nat => bool) x a)
                                ((bit::nat => nat => bool) x b))
                              ((bit::nat => nat => bool) x y))))
                     ((EQUIV::nat => nat => bool)
                       ((BITWISE::nat
                                  => (bool => bool => bool)
                                     => nat => nat => nat)
                         (WL::nat) oper a b)
                       y)))))"
  by (import word32 BITWISE_THM2)

lemma OR_ASSOC_QT: "ALL (a::nat) (b::nat) c::nat. EQUIV (OR a (OR b c)) (OR (OR a b) c)"
  by (import word32 OR_ASSOC_QT)

lemma OR_COMM_QT: "ALL (a::nat) b::nat. EQUIV (OR a b) (OR b a)"
  by (import word32 OR_COMM_QT)

lemma OR_ABSORB_QT: "ALL (a::nat) b::nat. EQUIV (AND a (OR a b)) a"
  by (import word32 OR_ABSORB_QT)

lemma OR_IDEM_QT: "ALL a::nat. EQUIV (OR a a) a"
  by (import word32 OR_IDEM_QT)

lemma AND_ASSOC_QT: "ALL (a::nat) (b::nat) c::nat. EQUIV (AND a (AND b c)) (AND (AND a b) c)"
  by (import word32 AND_ASSOC_QT)

lemma AND_COMM_QT: "ALL (a::nat) b::nat. EQUIV (AND a b) (AND b a)"
  by (import word32 AND_COMM_QT)

lemma AND_ABSORB_QT: "ALL (a::nat) b::nat. EQUIV (OR a (AND a b)) a"
  by (import word32 AND_ABSORB_QT)

lemma AND_IDEM_QT: "ALL a::nat. EQUIV (AND a a) a"
  by (import word32 AND_IDEM_QT)

lemma OR_COMP_QT: "ALL a::nat. EQUIV (OR a (ONE_COMP a)) COMP0"
  by (import word32 OR_COMP_QT)

lemma AND_COMP_QT: "ALL a::nat. EQUIV (AND a (ONE_COMP a)) 0"
  by (import word32 AND_COMP_QT)

lemma ONE_COMP_QT: "ALL a::nat. EQUIV (ONE_COMP (ONE_COMP a)) a"
  by (import word32 ONE_COMP_QT)

lemma RIGHT_AND_OVER_OR_QT: "ALL (a::nat) (b::nat) c::nat.
   EQUIV (AND (OR a b) c) (OR (AND a c) (AND b c))"
  by (import word32 RIGHT_AND_OVER_OR_QT)

lemma RIGHT_OR_OVER_AND_QT: "ALL (a::nat) (b::nat) c::nat. EQUIV (OR (AND a b) c) (AND (OR a c) (OR b c))"
  by (import word32 RIGHT_OR_OVER_AND_QT)

lemma DE_MORGAN_THM_QT: "ALL (a::nat) b::nat.
   EQUIV (ONE_COMP (AND a b)) (OR (ONE_COMP a) (ONE_COMP b)) &
   EQUIV (ONE_COMP (OR a b)) (AND (ONE_COMP a) (ONE_COMP b))"
  by (import word32 DE_MORGAN_THM_QT)

lemma BIT_EQUIV: "ALL (n::nat) (a::nat) b::nat. n < WL --> EQUIV a b --> bit n a = bit n b"
  by (import word32 BIT_EQUIV)

lemma LSB_WELLDEF: "ALL (a::nat) b::nat. EQUIV a b --> LSBn a = LSBn b"
  by (import word32 LSB_WELLDEF)

lemma MSB_WELLDEF: "ALL (a::nat) b::nat. EQUIV a b --> MSBn a = MSBn b"
  by (import word32 MSB_WELLDEF)

lemma BITWISE_ISTEP: "ALL (n::nat) (oper::bool => bool => bool) (a::nat) b::nat.
   0 < n -->
   BITWISE n oper (a div 2) (b div 2) =
   BITWISE n oper a b div 2 + SBIT (oper (bit n a) (bit n b)) (n - 1)"
  by (import word32 BITWISE_ISTEP)

lemma BITWISE_EVAL: "ALL (n::nat) (oper::bool => bool => bool) (a::nat) b::nat.
   BITWISE (Suc n) oper a b =
   2 * BITWISE n oper (a div 2) (b div 2) + SBIT (oper (LSBn a) (LSBn b)) 0"
  by (import word32 BITWISE_EVAL)

lemma BITWISE_WELLDEF: "ALL (n::nat) (oper::bool => bool => bool) (a::nat) (b::nat) (c::nat) d::nat.
   EQUIV a b & EQUIV c d --> EQUIV (BITWISE n oper a c) (BITWISE n oper b d)"
  by (import word32 BITWISE_WELLDEF)

lemma BITWISEw_WELLDEF: "ALL (oper::bool => bool => bool) (a::nat) (b::nat) (c::nat) d::nat.
   EQUIV a b & EQUIV c d -->
   EQUIV (BITWISE WL oper a c) (BITWISE WL oper b d)"
  by (import word32 BITWISEw_WELLDEF)

lemma SUC_WELLDEF: "ALL (a::nat) b::nat. EQUIV a b --> EQUIV (Suc a) (Suc b)"
  by (import word32 SUC_WELLDEF)

lemma ADD_WELLDEF: "ALL (a::nat) (b::nat) (c::nat) d::nat.
   EQUIV a b & EQUIV c d --> EQUIV (a + c) (b + d)"
  by (import word32 ADD_WELLDEF)

lemma MUL_WELLDEF: "ALL (a::nat) (b::nat) (c::nat) d::nat.
   EQUIV a b & EQUIV c d --> EQUIV (a * c) (b * d)"
  by (import word32 MUL_WELLDEF)

lemma ONE_COMP_WELLDEF: "ALL (a::nat) b::nat. EQUIV a b --> EQUIV (ONE_COMP a) (ONE_COMP b)"
  by (import word32 ONE_COMP_WELLDEF)

lemma TWO_COMP_WELLDEF: "ALL (a::nat) b::nat. EQUIV a b --> EQUIV (TWO_COMP a) (TWO_COMP b)"
  by (import word32 TWO_COMP_WELLDEF)

lemma TOw_WELLDEF: "ALL (a::nat) b::nat. EQUIV a b --> EQUIV (MODw a) (MODw b)"
  by (import word32 TOw_WELLDEF)

consts
  LSR_ONE :: "nat => nat" 

defs
  LSR_ONE_primdef: "LSR_ONE == %a::nat. MODw a div 2"

lemma LSR_ONE_def: "ALL a::nat. LSR_ONE a = MODw a div 2"
  by (import word32 LSR_ONE_def)

consts
  ASR_ONE :: "nat => nat" 

defs
  ASR_ONE_primdef: "ASR_ONE == %a::nat. LSR_ONE a + SBIT (MSBn a) HB"

lemma ASR_ONE_def: "ALL a::nat. ASR_ONE a = LSR_ONE a + SBIT (MSBn a) HB"
  by (import word32 ASR_ONE_def)

consts
  ROR_ONE :: "nat => nat" 

defs
  ROR_ONE_primdef: "ROR_ONE == %a::nat. LSR_ONE a + SBIT (LSBn a) HB"

lemma ROR_ONE_def: "ALL a::nat. ROR_ONE a = LSR_ONE a + SBIT (LSBn a) HB"
  by (import word32 ROR_ONE_def)

consts
  RRXn :: "bool => nat => nat" 

defs
  RRXn_primdef: "RRXn == %(c::bool) a::nat. LSR_ONE a + SBIT c HB"

lemma RRXn_def: "ALL (c::bool) a::nat. RRXn c a = LSR_ONE a + SBIT c HB"
  by (import word32 RRXn_def)

lemma LSR_ONE_WELLDEF: "ALL (a::nat) b::nat. EQUIV a b --> EQUIV (LSR_ONE a) (LSR_ONE b)"
  by (import word32 LSR_ONE_WELLDEF)

lemma ASR_ONE_WELLDEF: "ALL (a::nat) b::nat. EQUIV a b --> EQUIV (ASR_ONE a) (ASR_ONE b)"
  by (import word32 ASR_ONE_WELLDEF)

lemma ROR_ONE_WELLDEF: "ALL (a::nat) b::nat. EQUIV a b --> EQUIV (ROR_ONE a) (ROR_ONE b)"
  by (import word32 ROR_ONE_WELLDEF)

lemma RRX_WELLDEF: "ALL (a::nat) (b::nat) c::bool. EQUIV a b --> EQUIV (RRXn c a) (RRXn c b)"
  by (import word32 RRX_WELLDEF)

lemma LSR_ONE: "LSR_ONE = BITS HB 1"
  by (import word32 LSR_ONE)

typedef (open) word32 = "{x::nat => bool. EX xa::nat. x = EQUIV xa}" 
  by (rule typedef_helper,import word32 word32_TY_DEF)

lemmas word32_TY_DEF = typedef_hol2hol4 [OF type_definition_word32]

consts
  mk_word32 :: "(nat => bool) => word32" 
  dest_word32 :: "word32 => nat => bool" 

specification (dest_word32 mk_word32) word32_tybij: "(ALL a::word32. mk_word32 (dest_word32 a) = a) &
(ALL r::nat => bool.
    (EX x::nat. r = EQUIV x) = (dest_word32 (mk_word32 r) = r))"
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

constdefs
  word_suc :: "word32 => word32" 
  "word_suc == %T1::word32. mk_word32 (EQUIV (Suc (Eps (dest_word32 T1))))"

lemma word_suc: "ALL T1::word32. word_suc T1 = mk_word32 (EQUIV (Suc (Eps (dest_word32 T1))))"
  by (import word32 word_suc)

constdefs
  word_add :: "word32 => word32 => word32" 
  "word_add ==
%(T1::word32) T2::word32.
   mk_word32 (EQUIV (Eps (dest_word32 T1) + Eps (dest_word32 T2)))"

lemma word_add: "ALL (T1::word32) T2::word32.
   word_add T1 T2 =
   mk_word32 (EQUIV (Eps (dest_word32 T1) + Eps (dest_word32 T2)))"
  by (import word32 word_add)

constdefs
  word_mul :: "word32 => word32 => word32" 
  "word_mul ==
%(T1::word32) T2::word32.
   mk_word32 (EQUIV (Eps (dest_word32 T1) * Eps (dest_word32 T2)))"

lemma word_mul: "ALL (T1::word32) T2::word32.
   word_mul T1 T2 =
   mk_word32 (EQUIV (Eps (dest_word32 T1) * Eps (dest_word32 T2)))"
  by (import word32 word_mul)

constdefs
  word_1comp :: "word32 => word32" 
  "word_1comp ==
%T1::word32. mk_word32 (EQUIV (ONE_COMP (Eps (dest_word32 T1))))"

lemma word_1comp: "ALL T1::word32.
   word_1comp T1 = mk_word32 (EQUIV (ONE_COMP (Eps (dest_word32 T1))))"
  by (import word32 word_1comp)

constdefs
  word_2comp :: "word32 => word32" 
  "word_2comp ==
%T1::word32. mk_word32 (EQUIV (TWO_COMP (Eps (dest_word32 T1))))"

lemma word_2comp: "ALL T1::word32.
   word_2comp T1 = mk_word32 (EQUIV (TWO_COMP (Eps (dest_word32 T1))))"
  by (import word32 word_2comp)

constdefs
  word_lsr1 :: "word32 => word32" 
  "word_lsr1 == %T1::word32. mk_word32 (EQUIV (LSR_ONE (Eps (dest_word32 T1))))"

lemma word_lsr1: "ALL T1::word32.
   word_lsr1 T1 = mk_word32 (EQUIV (LSR_ONE (Eps (dest_word32 T1))))"
  by (import word32 word_lsr1)

constdefs
  word_asr1 :: "word32 => word32" 
  "word_asr1 == %T1::word32. mk_word32 (EQUIV (ASR_ONE (Eps (dest_word32 T1))))"

lemma word_asr1: "ALL T1::word32.
   word_asr1 T1 = mk_word32 (EQUIV (ASR_ONE (Eps (dest_word32 T1))))"
  by (import word32 word_asr1)

constdefs
  word_ror1 :: "word32 => word32" 
  "word_ror1 == %T1::word32. mk_word32 (EQUIV (ROR_ONE (Eps (dest_word32 T1))))"

lemma word_ror1: "ALL T1::word32.
   word_ror1 T1 = mk_word32 (EQUIV (ROR_ONE (Eps (dest_word32 T1))))"
  by (import word32 word_ror1)

consts
  RRX :: "bool => word32 => word32" 

defs
  RRX_primdef: "RRX ==
%(T1::bool) T2::word32. mk_word32 (EQUIV (RRXn T1 (Eps (dest_word32 T2))))"

lemma RRX_def: "ALL (T1::bool) T2::word32.
   RRX T1 T2 = mk_word32 (EQUIV (RRXn T1 (Eps (dest_word32 T2))))"
  by (import word32 RRX_def)

consts
  LSB :: "word32 => bool" 

defs
  LSB_primdef: "LSB == %T1::word32. LSBn (Eps (dest_word32 T1))"

lemma LSB_def: "ALL T1::word32. LSB T1 = LSBn (Eps (dest_word32 T1))"
  by (import word32 LSB_def)

consts
  MSB :: "word32 => bool" 

defs
  MSB_primdef: "MSB == %T1::word32. MSBn (Eps (dest_word32 T1))"

lemma MSB_def: "ALL T1::word32. MSB T1 = MSBn (Eps (dest_word32 T1))"
  by (import word32 MSB_def)

constdefs
  bitwise_or :: "word32 => word32 => word32" 
  "bitwise_or ==
%(T1::word32) T2::word32.
   mk_word32 (EQUIV (OR (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"

lemma bitwise_or: "ALL (T1::word32) T2::word32.
   bitwise_or T1 T2 =
   mk_word32 (EQUIV (OR (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"
  by (import word32 bitwise_or)

constdefs
  bitwise_eor :: "word32 => word32 => word32" 
  "bitwise_eor ==
%(T1::word32) T2::word32.
   mk_word32 (EQUIV (EOR (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"

lemma bitwise_eor: "ALL (T1::word32) T2::word32.
   bitwise_eor T1 T2 =
   mk_word32 (EQUIV (EOR (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"
  by (import word32 bitwise_eor)

constdefs
  bitwise_and :: "word32 => word32 => word32" 
  "bitwise_and ==
%(T1::word32) T2::word32.
   mk_word32 (EQUIV (AND (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"

lemma bitwise_and: "ALL (T1::word32) T2::word32.
   bitwise_and T1 T2 =
   mk_word32 (EQUIV (AND (Eps (dest_word32 T1)) (Eps (dest_word32 T2))))"
  by (import word32 bitwise_and)

consts
  TOw :: "word32 => word32" 

defs
  TOw_primdef: "TOw == %T1::word32. mk_word32 (EQUIV (MODw (Eps (dest_word32 T1))))"

lemma TOw_def: "ALL T1::word32. TOw T1 = mk_word32 (EQUIV (MODw (Eps (dest_word32 T1))))"
  by (import word32 TOw_def)

consts
  n2w :: "nat => word32" 

defs
  n2w_primdef: "n2w == %n::nat. mk_word32 (EQUIV n)"

lemma n2w_def: "ALL n::nat. n2w n = mk_word32 (EQUIV n)"
  by (import word32 n2w_def)

consts
  w2n :: "word32 => nat" 

defs
  w2n_primdef: "w2n == %w::word32. MODw (Eps (dest_word32 w))"

lemma w2n_def: "ALL w::word32. w2n w = MODw (Eps (dest_word32 w))"
  by (import word32 w2n_def)

lemma ADDw: "(ALL x::word32. word_add w_0 x = x) &
(ALL (x::word32) xa::word32.
    word_add (word_suc x) xa = word_suc (word_add x xa))"
  by (import word32 ADDw)

lemma ADD_0w: "ALL x::word32. word_add x w_0 = x"
  by (import word32 ADD_0w)

lemma ADD1w: "ALL x::word32. word_suc x = word_add x w_1"
  by (import word32 ADD1w)

lemma ADD_ASSOCw: "ALL (x::word32) (xa::word32) xb::word32.
   word_add x (word_add xa xb) = word_add (word_add x xa) xb"
  by (import word32 ADD_ASSOCw)

lemma ADD_CLAUSESw: "(ALL x::word32. word_add w_0 x = x) &
(ALL x::word32. word_add x w_0 = x) &
(ALL (x::word32) xa::word32.
    word_add (word_suc x) xa = word_suc (word_add x xa)) &
(ALL (x::word32) xa::word32.
    word_add x (word_suc xa) = word_suc (word_add x xa))"
  by (import word32 ADD_CLAUSESw)

lemma ADD_COMMw: "ALL (x::word32) xa::word32. word_add x xa = word_add xa x"
  by (import word32 ADD_COMMw)

lemma ADD_INV_0_EQw: "ALL (x::word32) xa::word32. (word_add x xa = x) = (xa = w_0)"
  by (import word32 ADD_INV_0_EQw)

lemma EQ_ADD_LCANCELw: "ALL (x::word32) (xa::word32) xb::word32.
   (word_add x xa = word_add x xb) = (xa = xb)"
  by (import word32 EQ_ADD_LCANCELw)

lemma EQ_ADD_RCANCELw: "ALL (x::word32) (xa::word32) xb::word32.
   (word_add x xb = word_add xa xb) = (x = xa)"
  by (import word32 EQ_ADD_RCANCELw)

lemma LEFT_ADD_DISTRIBw: "ALL (x::word32) (xa::word32) xb::word32.
   word_mul xb (word_add x xa) = word_add (word_mul xb x) (word_mul xb xa)"
  by (import word32 LEFT_ADD_DISTRIBw)

lemma MULT_ASSOCw: "ALL (x::word32) (xa::word32) xb::word32.
   word_mul x (word_mul xa xb) = word_mul (word_mul x xa) xb"
  by (import word32 MULT_ASSOCw)

lemma MULT_COMMw: "ALL (x::word32) xa::word32. word_mul x xa = word_mul xa x"
  by (import word32 MULT_COMMw)

lemma MULT_CLAUSESw: "ALL (x::word32) xa::word32.
   word_mul w_0 x = w_0 &
   word_mul x w_0 = w_0 &
   word_mul w_1 x = x &
   word_mul x w_1 = x &
   word_mul (word_suc x) xa = word_add (word_mul x xa) xa &
   word_mul x (word_suc xa) = word_add x (word_mul x xa)"
  by (import word32 MULT_CLAUSESw)

lemma TWO_COMP_ONE_COMP: "ALL x::word32. word_2comp x = word_add (word_1comp x) w_1"
  by (import word32 TWO_COMP_ONE_COMP)

lemma OR_ASSOCw: "ALL (x::word32) (xa::word32) xb::word32.
   bitwise_or x (bitwise_or xa xb) = bitwise_or (bitwise_or x xa) xb"
  by (import word32 OR_ASSOCw)

lemma OR_COMMw: "ALL (x::word32) xa::word32. bitwise_or x xa = bitwise_or xa x"
  by (import word32 OR_COMMw)

lemma OR_IDEMw: "ALL x::word32. bitwise_or x x = x"
  by (import word32 OR_IDEMw)

lemma OR_ABSORBw: "ALL (x::word32) xa::word32. bitwise_and x (bitwise_or x xa) = x"
  by (import word32 OR_ABSORBw)

lemma AND_ASSOCw: "ALL (x::word32) (xa::word32) xb::word32.
   bitwise_and x (bitwise_and xa xb) = bitwise_and (bitwise_and x xa) xb"
  by (import word32 AND_ASSOCw)

lemma AND_COMMw: "ALL (x::word32) xa::word32. bitwise_and x xa = bitwise_and xa x"
  by (import word32 AND_COMMw)

lemma AND_IDEMw: "ALL x::word32. bitwise_and x x = x"
  by (import word32 AND_IDEMw)

lemma AND_ABSORBw: "ALL (x::word32) xa::word32. bitwise_or x (bitwise_and x xa) = x"
  by (import word32 AND_ABSORBw)

lemma ONE_COMPw: "ALL x::word32. word_1comp (word_1comp x) = x"
  by (import word32 ONE_COMPw)

lemma RIGHT_AND_OVER_ORw: "ALL (x::word32) (xa::word32) xb::word32.
   bitwise_and (bitwise_or x xa) xb =
   bitwise_or (bitwise_and x xb) (bitwise_and xa xb)"
  by (import word32 RIGHT_AND_OVER_ORw)

lemma RIGHT_OR_OVER_ANDw: "ALL (x::word32) (xa::word32) xb::word32.
   bitwise_or (bitwise_and x xa) xb =
   bitwise_and (bitwise_or x xb) (bitwise_or xa xb)"
  by (import word32 RIGHT_OR_OVER_ANDw)

lemma DE_MORGAN_THMw: "ALL (x::word32) xa::word32.
   word_1comp (bitwise_and x xa) =
   bitwise_or (word_1comp x) (word_1comp xa) &
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

lemma ADD_TWO_COMP: "ALL x::word32. word_add x (word_2comp x) = w_0"
  by (import word32 ADD_TWO_COMP)

lemma ADD_TWO_COMP2: "ALL x::word32. word_add (word_2comp x) x = w_0"
  by (import word32 ADD_TWO_COMP2)

constdefs
  word_sub :: "word32 => word32 => word32" 
  "word_sub == %(a::word32) b::word32. word_add a (word_2comp b)"

lemma word_sub: "ALL (a::word32) b::word32. word_sub a b = word_add a (word_2comp b)"
  by (import word32 word_sub)

constdefs
  word_lsl :: "word32 => nat => word32" 
  "word_lsl == %(a::word32) n::nat. word_mul a (n2w (2 ^ n))"

lemma word_lsl: "ALL (a::word32) n::nat. word_lsl a n = word_mul a (n2w (2 ^ n))"
  by (import word32 word_lsl)

constdefs
  word_lsr :: "word32 => nat => word32" 
  "word_lsr == %(a::word32) n::nat. (word_lsr1 ^ n) a"

lemma word_lsr: "ALL (a::word32) n::nat. word_lsr a n = (word_lsr1 ^ n) a"
  by (import word32 word_lsr)

constdefs
  word_asr :: "word32 => nat => word32" 
  "word_asr == %(a::word32) n::nat. (word_asr1 ^ n) a"

lemma word_asr: "ALL (a::word32) n::nat. word_asr a n = (word_asr1 ^ n) a"
  by (import word32 word_asr)

constdefs
  word_ror :: "word32 => nat => word32" 
  "word_ror == %(a::word32) n::nat. (word_ror1 ^ n) a"

lemma word_ror: "ALL (a::word32) n::nat. word_ror a n = (word_ror1 ^ n) a"
  by (import word32 word_ror)

consts
  BITw :: "nat => word32 => bool" 

defs
  BITw_primdef: "BITw == %(b::nat) n::word32. bit b (w2n n)"

lemma BITw_def: "ALL (b::nat) n::word32. BITw b n = bit b (w2n n)"
  by (import word32 BITw_def)

consts
  BITSw :: "nat => nat => word32 => nat" 

defs
  BITSw_primdef: "BITSw == %(h::nat) (l::nat) n::word32. BITS h l (w2n n)"

lemma BITSw_def: "ALL (h::nat) (l::nat) n::word32. BITSw h l n = BITS h l (w2n n)"
  by (import word32 BITSw_def)

consts
  SLICEw :: "nat => nat => word32 => nat" 

defs
  SLICEw_primdef: "SLICEw == %(h::nat) (l::nat) n::word32. SLICE h l (w2n n)"

lemma SLICEw_def: "ALL (h::nat) (l::nat) n::word32. SLICEw h l n = SLICE h l (w2n n)"
  by (import word32 SLICEw_def)

lemma TWO_COMP_ADD: "ALL (a::word32) b::word32.
   word_2comp (word_add a b) = word_add (word_2comp a) (word_2comp b)"
  by (import word32 TWO_COMP_ADD)

lemma TWO_COMP_ELIM: "ALL a::word32. word_2comp (word_2comp a) = a"
  by (import word32 TWO_COMP_ELIM)

lemma ADD_SUB_ASSOC: "ALL (a::word32) (b::word32) c::word32.
   word_sub (word_add a b) c = word_add a (word_sub b c)"
  by (import word32 ADD_SUB_ASSOC)

lemma ADD_SUB_SYM: "ALL (a::word32) (b::word32) c::word32.
   word_sub (word_add a b) c = word_add (word_sub a c) b"
  by (import word32 ADD_SUB_SYM)

lemma SUB_EQUALw: "ALL a::word32. word_sub a a = w_0"
  by (import word32 SUB_EQUALw)

lemma ADD_SUBw: "ALL (a::word32) b::word32. word_sub (word_add a b) b = a"
  by (import word32 ADD_SUBw)

lemma SUB_SUBw: "ALL (a::word32) (b::word32) c::word32.
   word_sub a (word_sub b c) = word_sub (word_add a c) b"
  by (import word32 SUB_SUBw)

lemma ONE_COMP_TWO_COMP: "ALL a::word32. word_1comp a = word_sub (word_2comp a) w_1"
  by (import word32 ONE_COMP_TWO_COMP)

lemma SUBw: "ALL (m::word32) n::word32. word_sub (word_suc m) n = word_suc (word_sub m n)"
  by (import word32 SUBw)

lemma ADD_EQ_SUBw: "ALL (m::word32) (n::word32) p::word32.
   (word_add m n = p) = (m = word_sub p n)"
  by (import word32 ADD_EQ_SUBw)

lemma CANCEL_SUBw: "ALL (m::word32) (n::word32) p::word32.
   (word_sub n p = word_sub m p) = (n = m)"
  by (import word32 CANCEL_SUBw)

lemma SUB_PLUSw: "ALL (a::word32) (b::word32) c::word32.
   word_sub a (word_add b c) = word_sub (word_sub a b) c"
  by (import word32 SUB_PLUSw)

lemma word_nchotomy: "ALL w::word32. EX n::nat. w = n2w n"
  by (import word32 word_nchotomy)

lemma dest_word_mk_word_eq3: "ALL a::nat. dest_word32 (mk_word32 (EQUIV a)) = EQUIV a"
  by (import word32 dest_word_mk_word_eq3)

lemma MODw_ELIM: "ALL n::nat. n2w (MODw n) = n2w n"
  by (import word32 MODw_ELIM)

lemma w2n_EVAL: "ALL n::nat. w2n (n2w n) = MODw n"
  by (import word32 w2n_EVAL)

lemma w2n_ELIM: "ALL a::word32. n2w (w2n a) = a"
  by (import word32 w2n_ELIM)

lemma n2w_11: "ALL (a::nat) b::nat. (n2w a = n2w b) = (MODw a = MODw b)"
  by (import word32 n2w_11)

lemma ADD_EVAL: "word_add (n2w (a::nat)) (n2w (b::nat)) = n2w (a + b)"
  by (import word32 ADD_EVAL)

lemma MUL_EVAL: "word_mul (n2w (a::nat)) (n2w (b::nat)) = n2w (a * b)"
  by (import word32 MUL_EVAL)

lemma ONE_COMP_EVAL: "word_1comp (n2w (a::nat)) = n2w (ONE_COMP a)"
  by (import word32 ONE_COMP_EVAL)

lemma TWO_COMP_EVAL: "word_2comp (n2w (a::nat)) = n2w (TWO_COMP a)"
  by (import word32 TWO_COMP_EVAL)

lemma LSR_ONE_EVAL: "word_lsr1 (n2w (a::nat)) = n2w (LSR_ONE a)"
  by (import word32 LSR_ONE_EVAL)

lemma ASR_ONE_EVAL: "word_asr1 (n2w (a::nat)) = n2w (ASR_ONE a)"
  by (import word32 ASR_ONE_EVAL)

lemma ROR_ONE_EVAL: "word_ror1 (n2w (a::nat)) = n2w (ROR_ONE a)"
  by (import word32 ROR_ONE_EVAL)

lemma RRX_EVAL: "RRX (c::bool) (n2w (a::nat)) = n2w (RRXn c a)"
  by (import word32 RRX_EVAL)

lemma LSB_EVAL: "LSB (n2w (a::nat)) = LSBn a"
  by (import word32 LSB_EVAL)

lemma MSB_EVAL: "MSB (n2w (a::nat)) = MSBn a"
  by (import word32 MSB_EVAL)

lemma OR_EVAL: "bitwise_or (n2w (a::nat)) (n2w (b::nat)) = n2w (OR a b)"
  by (import word32 OR_EVAL)

lemma EOR_EVAL: "bitwise_eor (n2w (a::nat)) (n2w (b::nat)) = n2w (EOR a b)"
  by (import word32 EOR_EVAL)

lemma AND_EVAL: "bitwise_and (n2w (a::nat)) (n2w (b::nat)) = n2w (AND a b)"
  by (import word32 AND_EVAL)

lemma BITS_EVAL: "ALL (h::nat) (l::nat) a::nat. BITSw h l (n2w a) = BITS h l (MODw a)"
  by (import word32 BITS_EVAL)

lemma BIT_EVAL: "ALL (b::nat) a::nat. BITw b (n2w a) = bit b (MODw a)"
  by (import word32 BIT_EVAL)

lemma SLICE_EVAL: "ALL (h::nat) (l::nat) a::nat. SLICEw h l (n2w a) = SLICE h l (MODw a)"
  by (import word32 SLICE_EVAL)

lemma LSL_ADD: "ALL (a::word32) (m::nat) n::nat.
   word_lsl (word_lsl a m) n = word_lsl a (m + n)"
  by (import word32 LSL_ADD)

lemma LSR_ADD: "ALL (x::word32) (xa::nat) xb::nat.
   word_lsr (word_lsr x xa) xb = word_lsr x (xa + xb)"
  by (import word32 LSR_ADD)

lemma ASR_ADD: "ALL (x::word32) (xa::nat) xb::nat.
   word_asr (word_asr x xa) xb = word_asr x (xa + xb)"
  by (import word32 ASR_ADD)

lemma ROR_ADD: "ALL (x::word32) (xa::nat) xb::nat.
   word_ror (word_ror x xa) xb = word_ror x (xa + xb)"
  by (import word32 ROR_ADD)

lemma LSL_LIMIT: "ALL (w::word32) n::nat. HB < n --> word_lsl w n = w_0"
  by (import word32 LSL_LIMIT)

lemma MOD_MOD_DIV: "ALL (a::nat) b::nat. INw (MODw a div 2 ^ b)"
  by (import word32 MOD_MOD_DIV)

lemma MOD_MOD_DIV_2EXP: "ALL (a::nat) n::nat. MODw (MODw a div 2 ^ n) div 2 = MODw a div 2 ^ Suc n"
  by (import word32 MOD_MOD_DIV_2EXP)

lemma LSR_EVAL: "ALL n::nat. word_lsr (n2w (a::nat)) n = n2w (MODw a div 2 ^ n)"
  by (import word32 LSR_EVAL)

lemma LSR_THM: "ALL (x::nat) n::nat. word_lsr (n2w n) x = n2w (BITS HB (min WL x) n)"
  by (import word32 LSR_THM)

lemma LSR_LIMIT: "ALL (x::nat) w::word32. HB < x --> word_lsr w x = w_0"
  by (import word32 LSR_LIMIT)

lemma LEFT_SHIFT_LESS: "ALL (n::nat) (m::nat) a::nat. a < 2 ^ m --> 2 ^ n + a * 2 ^ n <= 2 ^ (m + n)"
  by (import word32 LEFT_SHIFT_LESS)

lemma ROR_THM: "ALL (x::nat) n::nat.
   word_ror (n2w n) x =
   (let x'::nat = x mod WL
    in n2w (BITS HB x' n + BITS (x' - 1) 0 n * 2 ^ (WL - x')))"
  by (import word32 ROR_THM)

lemma ROR_CYCLE: "ALL (x::nat) w::word32. word_ror w (x * WL) = w"
  by (import word32 ROR_CYCLE)

lemma ASR_THM: "ALL (x::nat) n::nat.
   word_asr (n2w n) x =
   (let x'::nat = min HB x; s::nat = BITS HB x' n
    in n2w (if MSBn n then 2 ^ WL - 2 ^ (WL - x') + s else s))"
  by (import word32 ASR_THM)

lemma ASR_LIMIT: "ALL (x::nat) w::word32.
   HB <= x --> word_asr w x = (if MSB w then w_T else w_0)"
  by (import word32 ASR_LIMIT)

lemma ZERO_SHIFT: "(ALL n::nat. word_lsl w_0 n = w_0) &
(ALL n::nat. word_asr w_0 n = w_0) &
(ALL n::nat. word_lsr w_0 n = w_0) & (ALL n::nat. word_ror w_0 n = w_0)"
  by (import word32 ZERO_SHIFT)

lemma ZERO_SHIFT2: "(ALL a::word32. word_lsl a 0 = a) &
(ALL a::word32. word_asr a 0 = a) &
(ALL a::word32. word_lsr a 0 = a) & (ALL a::word32. word_ror a 0 = a)"
  by (import word32 ZERO_SHIFT2)

lemma ASR_w_T: "ALL n::nat. word_asr w_T n = w_T"
  by (import word32 ASR_w_T)

lemma ROR_w_T: "ALL n::nat. word_ror w_T n = w_T"
  by (import word32 ROR_w_T)

lemma MODw_EVAL: "ALL x::nat.
   MODw x =
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

lemma ADD_EVAL2: "ALL (b::nat) a::nat. word_add (n2w a) (n2w b) = n2w (MODw (a + b))"
  by (import word32 ADD_EVAL2)

lemma MUL_EVAL2: "ALL (b::nat) a::nat. word_mul (n2w a) (n2w b) = n2w (MODw (a * b))"
  by (import word32 MUL_EVAL2)

lemma ONE_COMP_EVAL2: "ALL a::nat.
   word_1comp (n2w a) =
   n2w (2 ^
        NUMERAL
         (NUMERAL_BIT2
           (NUMERAL_BIT1
             (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))) -
        1 -
        MODw a)"
  by (import word32 ONE_COMP_EVAL2)

lemma TWO_COMP_EVAL2: "ALL a::nat.
   word_2comp (n2w a) =
   n2w (MODw
         (2 ^
          NUMERAL
           (NUMERAL_BIT2
             (NUMERAL_BIT1
               (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))) -
          MODw a))"
  by (import word32 TWO_COMP_EVAL2)

lemma LSR_ONE_EVAL2: "ALL a::nat. word_lsr1 (n2w a) = n2w (MODw a div 2)"
  by (import word32 LSR_ONE_EVAL2)

lemma ASR_ONE_EVAL2: "ALL a::nat.
   word_asr1 (n2w a) =
   n2w (MODw a div 2 +
        SBIT (MSBn a)
         (NUMERAL
           (NUMERAL_BIT1
             (NUMERAL_BIT1
               (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO)))))))"
  by (import word32 ASR_ONE_EVAL2)

lemma ROR_ONE_EVAL2: "ALL a::nat.
   word_ror1 (n2w a) =
   n2w (MODw a div 2 +
        SBIT (LSBn a)
         (NUMERAL
           (NUMERAL_BIT1
             (NUMERAL_BIT1
               (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO)))))))"
  by (import word32 ROR_ONE_EVAL2)

lemma RRX_EVAL2: "ALL (c::bool) a::nat.
   RRX c (n2w a) =
   n2w (MODw a div 2 +
        SBIT c
         (NUMERAL
           (NUMERAL_BIT1
             (NUMERAL_BIT1
               (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO)))))))"
  by (import word32 RRX_EVAL2)

lemma LSB_EVAL2: "ALL a::nat. LSB (n2w a) = ODD a"
  by (import word32 LSB_EVAL2)

lemma MSB_EVAL2: "ALL a::nat.
   MSB (n2w a) =
   bit (NUMERAL
         (NUMERAL_BIT1
           (NUMERAL_BIT1
             (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))))
    a"
  by (import word32 MSB_EVAL2)

lemma OR_EVAL2: "ALL (b::nat) a::nat.
   bitwise_or (n2w a) (n2w b) =
   n2w (BITWISE
         (NUMERAL
           (NUMERAL_BIT2
             (NUMERAL_BIT1
               (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))))
         op | a b)"
  by (import word32 OR_EVAL2)

lemma AND_EVAL2: "ALL (b::nat) a::nat.
   bitwise_and (n2w a) (n2w b) =
   n2w (BITWISE
         (NUMERAL
           (NUMERAL_BIT2
             (NUMERAL_BIT1
               (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))))
         op & a b)"
  by (import word32 AND_EVAL2)

lemma EOR_EVAL2: "ALL (b::nat) a::nat.
   bitwise_eor (n2w a) (n2w b) =
   n2w (BITWISE
         (NUMERAL
           (NUMERAL_BIT2
             (NUMERAL_BIT1
               (NUMERAL_BIT1 (NUMERAL_BIT1 (NUMERAL_BIT1 ALT_ZERO))))))
         (%(x::bool) y::bool. x ~= y) a b)"
  by (import word32 EOR_EVAL2)

lemma BITWISE_EVAL2: "ALL (n::nat) (oper::bool => bool => bool) (x::nat) y::nat.
   BITWISE n oper x y =
   (if n = 0 then 0
    else 2 * BITWISE (n - 1) oper (x div 2) (y div 2) +
         (if oper (ODD x) (ODD y) then 1 else 0))"
  by (import word32 BITWISE_EVAL2)

lemma BITSwLT_THM: "ALL (h::nat) (l::nat) n::word32. BITSw h l n < 2 ^ (Suc h - l)"
  by (import word32 BITSwLT_THM)

lemma BITSw_COMP_THM: "ALL (h1::nat) (l1::nat) (h2::nat) (l2::nat) n::word32.
   h2 + l1 <= h1 -->
   BITS h2 l2 (BITSw h1 l1 n) = BITSw (h2 + l1) (l2 + l1) n"
  by (import word32 BITSw_COMP_THM)

lemma BITSw_DIV_THM: "ALL (h::nat) (l::nat) (n::nat) x::word32.
   BITSw h l x div 2 ^ n = BITSw h (l + n) x"
  by (import word32 BITSw_DIV_THM)

lemma BITw_THM: "ALL (b::nat) n::word32. BITw b n = (BITSw b b n = 1)"
  by (import word32 BITw_THM)

lemma SLICEw_THM: "ALL (n::word32) (h::nat) l::nat. SLICEw h l n = BITSw h l n * 2 ^ l"
  by (import word32 SLICEw_THM)

lemma BITS_SLICEw_THM: "ALL (h::nat) (l::nat) n::word32. BITS h l (SLICEw h l n) = BITSw h l n"
  by (import word32 BITS_SLICEw_THM)

lemma SLICEw_ZERO_THM: "ALL (n::word32) h::nat. SLICEw h 0 n = BITSw h 0 n"
  by (import word32 SLICEw_ZERO_THM)

lemma SLICEw_COMP_THM: "ALL (h::nat) (m::nat) (l::nat) a::word32.
   Suc m <= h & l <= m --> SLICEw h (Suc m) a + SLICEw m l a = SLICEw h l a"
  by (import word32 SLICEw_COMP_THM)

lemma BITSw_ZERO: "ALL (h::nat) (l::nat) n::word32. h < l --> BITSw h l n = 0"
  by (import word32 BITSw_ZERO)

lemma SLICEw_ZERO: "ALL (h::nat) (l::nat) n::word32. h < l --> SLICEw h l n = 0"
  by (import word32 SLICEw_ZERO)

;end_setup

end

