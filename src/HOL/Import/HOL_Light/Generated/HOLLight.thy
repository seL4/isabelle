(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOLLight
imports "../../HOL4Syntax" "../Compatibility"
begin 

setup_theory "~~/src/HOL/Import/HOL_Light/Generated" hollight

consts
  "_FALSITY_" :: "bool" ("'_FALSITY'_")

defs
  "_FALSITY__def": "_FALSITY_ == False"

lemma DEF__FALSITY_: "_FALSITY_ = False"
  by (import hollight DEF__FALSITY_)

lemma CONJ_ACI: "(p & q) = (q & p) &
((p & q) & r) = (p & q & r) &
(p & q & r) = (q & p & r) & (p & p) = p & (p & p & q) = (p & q)"
  by (import hollight CONJ_ACI)

lemma DISJ_ACI: "(p | q) = (q | p) &
((p | q) | r) = (p | q | r) &
(p | q | r) = (q | p | r) & (p | p) = p & (p | p | q) = (p | q)"
  by (import hollight DISJ_ACI)

lemma IMP_CONJ_ALT: "(p & q --> r) = (q --> p --> r)"
  by (import hollight IMP_CONJ_ALT)

lemma EQ_CLAUSES: "(True = t) = t & (t = True) = t & (False = t) = (~ t) & (t = False) = (~ t)"
  by (import hollight EQ_CLAUSES)

lemma NOT_CLAUSES_WEAK: "(~ True) = False & (~ False) = True"
  by (import hollight NOT_CLAUSES_WEAK)

lemma AND_CLAUSES: "(True & t) = t &
(t & True) = t & (False & t) = False & (t & False) = False & (t & t) = t"
  by (import hollight AND_CLAUSES)

lemma OR_CLAUSES: "(True | t) = True &
(t | True) = True & (False | t) = t & (t | False) = t & (t | t) = t"
  by (import hollight OR_CLAUSES)

lemma IMP_CLAUSES: "(True --> t) = t &
(t --> True) = True &
(False --> t) = True & (t --> t) = True & (t --> False) = (~ t)"
  by (import hollight IMP_CLAUSES)

lemma IMP_EQ_CLAUSE: "((x::'q_851) = x --> (p::bool)) = p"
  by (import hollight IMP_EQ_CLAUSE)

lemma TRIV_EXISTS_AND_THM: "(EX x::'A. (P::bool) & (Q::bool)) = ((EX x::'A. P) & (EX x::'A. Q))"
  by (import hollight TRIV_EXISTS_AND_THM)

lemma TRIV_AND_EXISTS_THM: "((EX x::'A. (P::bool)) & (EX x::'A. (Q::bool))) = (EX x::'A. P & Q)"
  by (import hollight TRIV_AND_EXISTS_THM)

lemma TRIV_FORALL_OR_THM: "(ALL x::'A. (P::bool) | (Q::bool)) = ((ALL x::'A. P) | (ALL x::'A. Q))"
  by (import hollight TRIV_FORALL_OR_THM)

lemma TRIV_OR_FORALL_THM: "((ALL x::'A. (P::bool)) | (ALL x::'A. (Q::bool))) = (ALL x::'A. P | Q)"
  by (import hollight TRIV_OR_FORALL_THM)

lemma TRIV_FORALL_IMP_THM: "(ALL x::'A. (P::bool) --> (Q::bool)) = ((EX x::'A. P) --> (ALL x::'A. Q))"
  by (import hollight TRIV_FORALL_IMP_THM)

lemma TRIV_EXISTS_IMP_THM: "(EX x::'A. (P::bool) --> (Q::bool)) = ((ALL x::'A. P) --> (EX x::'A. Q))"
  by (import hollight TRIV_EXISTS_IMP_THM)

lemma EXISTS_UNIQUE_ALT: "Ex1 (P::'A => bool) = (EX x::'A. ALL y::'A. P y = (x = y))"
  by (import hollight EXISTS_UNIQUE_ALT)

lemma SELECT_UNIQUE: "(!!y::'A. (P::'A => bool) y = (y = (x::'A))) ==> Eps P = x"
  by (import hollight SELECT_UNIQUE)

lemma EXCLUDED_MIDDLE: "t | ~ t"
  by (import hollight EXCLUDED_MIDDLE)

lemma COND_CLAUSES: "(if True then x::'A else (xa::'A)) = x & (if False then x else xa) = xa"
  by (import hollight COND_CLAUSES)

lemma COND_EXPAND: "(if b then t1 else t2) = ((~ b | t1) & (b | t2))"
  by (import hollight COND_EXPAND)

lemma COND_RATOR: "(if b::bool then f::'A => 'B else (g::'A => 'B)) (x::'A) =
(if b then f x else g x)"
  by (import hollight COND_RATOR)

lemma COND_ABS: "(%x::'A. if b::bool then (f::'A => 'B) x else (g::'A => 'B) x) =
(if b then f else g)"
  by (import hollight COND_ABS)

lemma MONO_COND: "[| (A --> B) & (C --> D); if b then A else C |] ==> if b then B else D"
  by (import hollight MONO_COND)

lemma SKOLEM_THM: "(ALL x::'A. Ex ((P::'A => 'B => bool) x)) =
(EX x::'A => 'B. ALL xa::'A. P xa (x xa))"
  by (import hollight SKOLEM_THM)

lemma UNIQUE_SKOLEM_ALT: "(ALL x::'A. Ex1 ((P::'A => 'B => bool) x)) =
(EX f::'A => 'B. ALL (x::'A) y::'B. P x y = (f x = y))"
  by (import hollight UNIQUE_SKOLEM_ALT)

lemma COND_EQ_CLAUSE: "(if (x::'q_2963) = x then y::'q_2956 else (z::'q_2956)) = y"
  by (import hollight COND_EQ_CLAUSE)

lemma bool_RECURSION: "EX x::bool => 'A. x False = (a::'A) & x True = (b::'A)"
  by (import hollight bool_RECURSION)

lemma o_ASSOC: "(f::'C => 'D) o ((g::'B => 'C) o (h::'A => 'B)) = f o g o h"
  by (import hollight o_ASSOC)

lemma I_O_ID: "id o (f::'A => 'B) = f & f o id = f"
  by (import hollight I_O_ID)

lemma EXISTS_ONE_REP: "EX x. x"
  by (import hollight EXISTS_ONE_REP)

lemma one_axiom: "(f::'A => unit) = (x::'A => unit)"
  by (import hollight one_axiom)

lemma one_RECURSION: "EX x::unit => 'A. x () = (e::'A)"
  by (import hollight one_RECURSION)

lemma one_Axiom: "EX! fn::unit => 'A. fn () = (e::'A)"
  by (import hollight one_Axiom)

lemma th_cond: "(b = False --> x = x0) & (b = True --> x = x1) ==> x = (b & x1 | ~ b & x0)"
  by (import hollight th_cond)

definition
  LET_END :: "'A => 'A"  where
  "LET_END == %t::'A. t"

lemma DEF_LET_END: "LET_END = (%t::'A. t)"
  by (import hollight DEF_LET_END)

consts
  "_SEQPATTERN" :: "('q_4007 => 'q_4004 => bool)
=> ('q_4007 => 'q_4004 => bool) => 'q_4007 => 'q_4004 => bool" ("'_SEQPATTERN")

defs
  "_SEQPATTERN_def": "_SEQPATTERN ==
%(r::'q_4007 => 'q_4004 => bool) (s::'q_4007 => 'q_4004 => bool) x::'q_4007.
   if Ex (r x) then r x else s x"

lemma DEF__SEQPATTERN: "_SEQPATTERN =
(%(r::'q_4007 => 'q_4004 => bool) (s::'q_4007 => 'q_4004 => bool)
    x::'q_4007. if Ex (r x) then r x else s x)"
  by (import hollight DEF__SEQPATTERN)

consts
  "_UNGUARDED_PATTERN" :: "bool => bool => bool" ("'_UNGUARDED'_PATTERN")

defs
  "_UNGUARDED_PATTERN_def": "_UNGUARDED_PATTERN == op &"

lemma DEF__UNGUARDED_PATTERN: "_UNGUARDED_PATTERN = op &"
  by (import hollight DEF__UNGUARDED_PATTERN)

consts
  "_GUARDED_PATTERN" :: "bool => bool => bool => bool" ("'_GUARDED'_PATTERN")

defs
  "_GUARDED_PATTERN_def": "_GUARDED_PATTERN == %p g r. p & g & r"

lemma DEF__GUARDED_PATTERN: "_GUARDED_PATTERN = (%p g r. p & g & r)"
  by (import hollight DEF__GUARDED_PATTERN)

consts
  "_MATCH" :: "'q_4049 => ('q_4049 => 'q_4053 => bool) => 'q_4053" ("'_MATCH")

defs
  "_MATCH_def": "_MATCH ==
%(e::'q_4049) r::'q_4049 => 'q_4053 => bool.
   if Ex1 (r e) then Eps (r e) else SOME z::'q_4053. False"

lemma DEF__MATCH: "_MATCH =
(%(e::'q_4049) r::'q_4049 => 'q_4053 => bool.
    if Ex1 (r e) then Eps (r e) else SOME z::'q_4053. False)"
  by (import hollight DEF__MATCH)

consts
  "_FUNCTION" :: "('q_4071 => 'q_4075 => bool) => 'q_4071 => 'q_4075" ("'_FUNCTION")

defs
  "_FUNCTION_def": "_FUNCTION ==
%(r::'q_4071 => 'q_4075 => bool) x::'q_4071.
   if Ex1 (r x) then Eps (r x) else SOME z::'q_4075. False"

lemma DEF__FUNCTION: "_FUNCTION =
(%(r::'q_4071 => 'q_4075 => bool) x::'q_4071.
    if Ex1 (r x) then Eps (r x) else SOME z::'q_4075. False)"
  by (import hollight DEF__FUNCTION)

lemma PAIR_EXISTS_THM: "EX (x::'A => 'B => bool) (a::'A) b::'B. x = Pair_Rep a b"
  by (import hollight PAIR_EXISTS_THM)

lemma pair_RECURSION: "EX x::'A * 'B => 'C.
   ALL (a0::'A) a1::'B. x (a0, a1) = (PAIR'::'A => 'B => 'C) a0 a1"
  by (import hollight pair_RECURSION)

definition
  UNCURRY :: "('A => 'B => 'C) => 'A * 'B => 'C"  where
  "UNCURRY == %(u::'A => 'B => 'C) ua::'A * 'B. u (fst ua) (snd ua)"

lemma DEF_UNCURRY: "UNCURRY = (%(u::'A => 'B => 'C) ua::'A * 'B. u (fst ua) (snd ua))"
  by (import hollight DEF_UNCURRY)

definition
  PASSOC :: "(('A * 'B) * 'C => 'D) => 'A * 'B * 'C => 'D"  where
  "PASSOC ==
%(u::('A * 'B) * 'C => 'D) ua::'A * 'B * 'C.
   u ((fst ua, fst (snd ua)), snd (snd ua))"

lemma DEF_PASSOC: "PASSOC =
(%(u::('A * 'B) * 'C => 'D) ua::'A * 'B * 'C.
    u ((fst ua, fst (snd ua)), snd (snd ua)))"
  by (import hollight DEF_PASSOC)

lemma LAMBDA_PAIR_THM: "(x::'q_4547 * 'q_4546 => 'q_4539) =
(SOME f::'q_4547 * 'q_4546 => 'q_4539.
    ALL (xa::'q_4547) y::'q_4546. f (xa, y) = x (xa, y))"
  by (import hollight LAMBDA_PAIR_THM)

lemma FORALL_PAIRED_THM: "All (SOME f::'q_4576 * 'q_4575 => bool.
        ALL (x::'q_4576) y::'q_4575.
           f (x, y) = (P::'q_4576 => 'q_4575 => bool) x y) =
(ALL x::'q_4576. All (P x))"
  by (import hollight FORALL_PAIRED_THM)

lemma EXISTS_PAIRED_THM: "Ex (SOME f::'q_4612 * 'q_4611 => bool.
       ALL (x::'q_4612) y::'q_4611.
          f (x, y) = (P::'q_4612 => 'q_4611 => bool) x y) =
(EX x::'q_4612. Ex (P x))"
  by (import hollight EXISTS_PAIRED_THM)

lemma FORALL_TRIPLED_THM: "All (SOME f::'q_4649 * 'q_4648 * 'q_4647 => bool.
        ALL (x::'q_4649) (y::'q_4648) z::'q_4647.
           f (x, y, z) = (P::'q_4649 => 'q_4648 => 'q_4647 => bool) x y z) =
(ALL (x::'q_4649) y::'q_4648. All (P x y))"
  by (import hollight FORALL_TRIPLED_THM)

lemma EXISTS_TRIPLED_THM: "Ex (SOME f::'q_4695 * 'q_4694 * 'q_4693 => bool.
       ALL (x::'q_4695) (y::'q_4694) z::'q_4693.
          f (x, y, z) = (P::'q_4695 => 'q_4694 => 'q_4693 => bool) x y z) =
(EX (x::'q_4695) y::'q_4694. Ex (P x y))"
  by (import hollight EXISTS_TRIPLED_THM)

lemma IND_SUC_0_EXISTS: "EX (x::ind => ind) z::ind.
   (ALL (x1::ind) x2::ind. (x x1 = x x2) = (x1 = x2)) &
   (ALL xa::ind. x xa ~= z)"
  by (import hollight IND_SUC_0_EXISTS)

definition
  IND_SUC :: "ind => ind"  where
  "IND_SUC ==
SOME f. EX z. (ALL x1 x2. (f x1 = f x2) = (x1 = x2)) & (ALL x. f x ~= z)"

lemma DEF_IND_SUC: "IND_SUC =
(SOME f. EX z. (ALL x1 x2. (f x1 = f x2) = (x1 = x2)) & (ALL x. f x ~= z))"
  by (import hollight DEF_IND_SUC)

definition
  IND_0 :: "ind"  where
  "IND_0 ==
SOME z.
   (ALL x1 x2. (IND_SUC x1 = IND_SUC x2) = (x1 = x2)) &
   (ALL x. IND_SUC x ~= z)"

lemma DEF_IND_0: "IND_0 =
(SOME z.
    (ALL x1 x2. (IND_SUC x1 = IND_SUC x2) = (x1 = x2)) &
    (ALL x. IND_SUC x ~= z))"
  by (import hollight DEF_IND_0)

definition
  NUM_REP :: "ind => bool"  where
  "NUM_REP ==
%a. ALL NUM_REP'.
       (ALL a.
           a = IND_0 | (EX i. a = IND_SUC i & NUM_REP' i) -->
           NUM_REP' a) -->
       NUM_REP' a"

lemma DEF_NUM_REP: "NUM_REP =
(%a. ALL NUM_REP'.
        (ALL a.
            a = IND_0 | (EX i. a = IND_SUC i & NUM_REP' i) -->
            NUM_REP' a) -->
        NUM_REP' a)"
  by (import hollight DEF_NUM_REP)

lemma num_RECURSION_STD: "EX fn::nat => 'Z.
   fn (0::nat) = (e::'Z) &
   (ALL n::nat. fn (Suc n) = (f::nat => 'Z => 'Z) n (fn n))"
  by (import hollight num_RECURSION_STD)

lemma ADD_CLAUSES: "(ALL x::nat. (0::nat) + x = x) &
(ALL x::nat. x + (0::nat) = x) &
(ALL (x::nat) xa::nat. Suc x + xa = Suc (x + xa)) &
(ALL (x::nat) xa::nat. x + Suc xa = Suc (x + xa))"
  by (import hollight ADD_CLAUSES)

lemma ADD_AC: "(m::nat) + (n::nat) = n + m &
m + n + (p::nat) = m + (n + p) & m + (n + p) = n + (m + p)"
  by (import hollight ADD_AC)

lemma EQ_ADD_LCANCEL_0: "((m::nat) + (n::nat) = m) = (n = (0::nat))"
  by (import hollight EQ_ADD_LCANCEL_0)

lemma EQ_ADD_RCANCEL_0: "((x::nat) + (xa::nat) = xa) = (x = (0::nat))"
  by (import hollight EQ_ADD_RCANCEL_0)

lemma BIT1: "2 * x + 1 = Suc (x + x)"
  by (import hollight BIT1)

lemma BIT1_THM: "2 * x + 1 = Suc (x + x)"
  by (import hollight BIT1_THM)

lemma TWO: "2 = Suc 1"
  by (import hollight TWO)

lemma MULT_CLAUSES: "(ALL x::nat. (0::nat) * x = (0::nat)) &
(ALL x::nat. x * (0::nat) = (0::nat)) &
(ALL x::nat. (1::nat) * x = x) &
(ALL x::nat. x * (1::nat) = x) &
(ALL (x::nat) xa::nat. Suc x * xa = x * xa + xa) &
(ALL (x::nat) xa::nat. x * Suc xa = x + x * xa)"
  by (import hollight MULT_CLAUSES)

lemma MULT_AC: "(m::nat) * (n::nat) = n * m &
m * n * (p::nat) = m * (n * p) & m * (n * p) = n * (m * p)"
  by (import hollight MULT_AC)

lemma EXP_EQ_1: "((x::nat) ^ (n::nat) = (1::nat)) = (x = (1::nat) | n = (0::nat))"
  by (import hollight EXP_EQ_1)

lemma LT_ANTISYM: "~ ((m::nat) < (n::nat) & n < m)"
  by (import hollight LT_ANTISYM)

lemma LET_ANTISYM: "~ ((m::nat) <= (n::nat) & n < m)"
  by (import hollight LET_ANTISYM)

lemma LTE_ANTISYM: "~ ((x::nat) < (xa::nat) & xa <= x)"
  by (import hollight LTE_ANTISYM)

lemma LT_CASES: "(m::nat) < (n::nat) | n < m | m = n"
  by (import hollight LT_CASES)

lemma LTE_CASES: "(x::nat) < (xa::nat) | xa <= x"
  by (import hollight LTE_CASES)

lemma LE_1: "(ALL x::nat. x ~= (0::nat) --> (0::nat) < x) &
(ALL x::nat. x ~= (0::nat) --> (1::nat) <= x) &
(ALL x>0::nat. x ~= (0::nat)) &
(ALL x>0::nat. (1::nat) <= x) &
(ALL x>=1::nat. (0::nat) < x) & (ALL x>=1::nat. x ~= (0::nat))"
  by (import hollight LE_1)

lemma LT_EXISTS: "(m < n) = (EX d. n = m + Suc d)"
  by (import hollight LT_EXISTS)

lemma LT_ADD: "((m::nat) < m + (n::nat)) = ((0::nat) < n)"
  by (import hollight LT_ADD)

lemma LT_ADDR: "((xa::nat) < (x::nat) + xa) = ((0::nat) < x)"
  by (import hollight LT_ADDR)

lemma LT_LMULT: "(m::nat) ~= (0::nat) & (n::nat) < (p::nat) ==> m * n < m * p"
  by (import hollight LT_LMULT)

lemma LE_MULT_LCANCEL: "((m::nat) * (n::nat) <= m * (p::nat)) = (m = (0::nat) | n <= p)"
  by (import hollight LE_MULT_LCANCEL)

lemma LE_MULT_RCANCEL: "((x::nat) * (xb::nat) <= (xa::nat) * xb) = (x <= xa | xb = (0::nat))"
  by (import hollight LE_MULT_RCANCEL)

lemma LT_MULT_LCANCEL: "((m::nat) * (n::nat) < m * (p::nat)) = (m ~= (0::nat) & n < p)"
  by (import hollight LT_MULT_LCANCEL)

lemma LT_MULT_RCANCEL: "((x::nat) * (xb::nat) < (xa::nat) * xb) = (x < xa & xb ~= (0::nat))"
  by (import hollight LT_MULT_RCANCEL)

lemma LT_MULT2: "(m::nat) < (n::nat) & (p::nat) < (q::nat) ==> m * p < n * q"
  by (import hollight LT_MULT2)

lemma WLOG_LE: "(ALL (m::nat) n::nat. (P::nat => nat => bool) m n = P n m) &
(ALL (m::nat) n::nat. m <= n --> P m n)
==> P (m::nat) (x::nat)"
  by (import hollight WLOG_LE)

lemma WLOG_LT: "(ALL m::nat. (P::nat => nat => bool) m m) &
(ALL (m::nat) n::nat. P m n = P n m) &
(ALL (m::nat) n::nat. m < n --> P m n)
==> P (m::nat) (x::nat)"
  by (import hollight WLOG_LT)

lemma num_WOP: "Ex (P::nat => bool) = (EX n::nat. P n & (ALL m<n. ~ P m))"
  by (import hollight num_WOP)

lemma num_MAX: "(Ex (P::nat => bool) & (EX M::nat. ALL x::nat. P x --> x <= M)) =
(EX m::nat. P m & (ALL x::nat. P x --> x <= m))"
  by (import hollight num_MAX)

lemma NOT_EVEN: "odd (n::nat) = odd n"
  by (import hollight NOT_EVEN)

lemma NOT_ODD: "(~ odd (n::nat)) = even n"
  by (import hollight NOT_ODD)

lemma EVEN_OR_ODD: "even (n::nat) | odd n"
  by (import hollight EVEN_OR_ODD)

lemma EVEN_AND_ODD: "~ (even (x::nat) & odd x)"
  by (import hollight EVEN_AND_ODD)

lemma EVEN_EXP: "even ((m::nat) ^ (n::nat)) = (even m & n ~= (0::nat))"
  by (import hollight EVEN_EXP)

lemma ODD_MULT: "odd ((m::nat) * (n::nat)) = (odd m & odd n)"
  by (import hollight ODD_MULT)

lemma ODD_EXP: "odd ((m::nat) ^ (n::nat)) = (odd m | n = (0::nat))"
  by (import hollight ODD_EXP)

lemma EVEN_DOUBLE: "even ((2::nat) * (n::nat))"
  by (import hollight EVEN_DOUBLE)

lemma ODD_DOUBLE: "odd (Suc (2 * x))"
  by (import hollight ODD_DOUBLE)

lemma EVEN_EXISTS_LEMMA: "(even n --> (EX m. n = 2 * m)) & (odd n --> (EX m. n = Suc (2 * m)))"
  by (import hollight EVEN_EXISTS_LEMMA)

lemma EVEN_ODD_DECOMPOSITION: "(EX (k::nat) m::nat. odd m & (n::nat) = (2::nat) ^ k * m) = (n ~= (0::nat))"
  by (import hollight EVEN_ODD_DECOMPOSITION)

lemma SUB_0: "(0::nat) - (x::nat) = (0::nat) & x - (0::nat) = x"
  by (import hollight SUB_0)

lemma SUB_PRESUC: "Suc m - n - Suc 0 = m - n"
  by (import hollight SUB_PRESUC)

lemma ADD_SUBR: "(xa::nat) - ((x::nat) + xa) = (0::nat)"
  by (import hollight ADD_SUBR)

lemma EVEN_SUB: "even ((m::nat) - (n::nat)) = (m <= n | even m = even n)"
  by (import hollight EVEN_SUB)

lemma ODD_SUB: "odd ((x::nat) - (xa::nat)) = (xa < x & odd x ~= odd xa)"
  by (import hollight ODD_SUB)

lemma EXP_LT_0: "((0::nat) < (xa::nat) ^ (x::nat)) = (xa ~= (0::nat) | x = (0::nat))"
  by (import hollight EXP_LT_0)

lemma LT_EXP: "((x::nat) ^ (m::nat) < x ^ (n::nat)) =
((2::nat) <= x & m < n | x = (0::nat) & m ~= (0::nat) & n = (0::nat))"
  by (import hollight LT_EXP)

lemma LE_EXP: "((x::nat) ^ (m::nat) <= x ^ (n::nat)) =
(if x = (0::nat) then m = (0::nat) --> n = (0::nat)
 else x = (1::nat) | m <= n)"
  by (import hollight LE_EXP)

lemma EQ_EXP: "((x::nat) ^ (m::nat) = x ^ (n::nat)) =
(if x = (0::nat) then (m = (0::nat)) = (n = (0::nat))
 else x = (1::nat) | m = n)"
  by (import hollight EQ_EXP)

lemma EXP_MONO_LE_IMP: "(x::nat) <= (xa::nat) ==> x ^ (xb::nat) <= xa ^ xb"
  by (import hollight EXP_MONO_LE_IMP)

lemma EXP_MONO_LT_IMP: "(x::nat) < (y::nat) & (n::nat) ~= (0::nat) ==> x ^ n < y ^ n"
  by (import hollight EXP_MONO_LT_IMP)

lemma EXP_MONO_LE: "((x::nat) ^ (n::nat) <= (y::nat) ^ n) = (x <= y | n = (0::nat))"
  by (import hollight EXP_MONO_LE)

lemma EXP_MONO_LT: "((x::nat) ^ (xb::nat) < (xa::nat) ^ xb) = (x < xa & xb ~= (0::nat))"
  by (import hollight EXP_MONO_LT)

lemma EXP_MONO_EQ: "((x::nat) ^ (xb::nat) = (xa::nat) ^ xb) = (x = xa | xb = (0::nat))"
  by (import hollight EXP_MONO_EQ)

lemma DIVMOD_EXIST: "(n::nat) ~= (0::nat) ==> EX (q::nat) r::nat. (m::nat) = q * n + r & r < n"
  by (import hollight DIVMOD_EXIST)

lemma DIVMOD_EXIST_0: "EX (x::nat) xa::nat.
   if (n::nat) = (0::nat) then x = (0::nat) & xa = (m::nat)
   else m = x * n + xa & xa < n"
  by (import hollight DIVMOD_EXIST_0)

lemma DIVISION: "(n::nat) ~= (0::nat) ==> (m::nat) = m div n * n + m mod n & m mod n < n"
  by (import hollight DIVISION)

lemma DIVMOD_UNIQ_LEMMA: "((m::nat) = (q1::nat) * (n::nat) + (r1::nat) & r1 < n) &
m = (q2::nat) * n + (r2::nat) & r2 < n
==> q1 = q2 & r1 = r2"
  by (import hollight DIVMOD_UNIQ_LEMMA)

lemma DIVMOD_UNIQ: "(m::nat) = (q::nat) * (n::nat) + (r::nat) & r < n
==> m div n = q & m mod n = r"
  by (import hollight DIVMOD_UNIQ)

lemma MOD_UNIQ: "(m::nat) = (q::nat) * (n::nat) + (r::nat) & r < n ==> m mod n = r"
  by (import hollight MOD_UNIQ)

lemma DIV_UNIQ: "(m::nat) = (q::nat) * (n::nat) + (r::nat) & r < n ==> m div n = q"
  by (import hollight DIV_UNIQ)

lemma MOD_EQ: "(m::nat) = (n::nat) + (q::nat) * (p::nat) ==> m mod p = n mod p"
  by (import hollight MOD_EQ)

lemma DIV_LE: "(n::nat) ~= (0::nat) ==> (m::nat) div n <= m"
  by (import hollight DIV_LE)

lemma DIV_MUL_LE: "(n::nat) * ((m::nat) div n) <= m"
  by (import hollight DIV_MUL_LE)

lemma MOD_MOD: "(n::nat) * (p::nat) ~= (0::nat) ==> (m::nat) mod (n * p) mod n = m mod n"
  by (import hollight MOD_MOD)

lemma MOD_MOD_REFL: "(n::nat) ~= (0::nat) ==> (m::nat) mod n mod n = m mod n"
  by (import hollight MOD_MOD_REFL)

lemma DIV_MULT2: "(x::nat) * (xb::nat) ~= (0::nat) ==> x * (xa::nat) div (x * xb) = xa div xb"
  by (import hollight DIV_MULT2)

lemma MOD_MULT2: "(x::nat) * (xb::nat) ~= (0::nat)
==> x * (xa::nat) mod (x * xb) = x * (xa mod xb)"
  by (import hollight MOD_MULT2)

lemma MOD_EXISTS: "(EX q::nat. (m::nat) = (n::nat) * q) =
(if n = (0::nat) then m = (0::nat) else m mod n = (0::nat))"
  by (import hollight MOD_EXISTS)

lemma LE_RDIV_EQ: "(a::nat) ~= (0::nat) ==> ((n::nat) <= (b::nat) div a) = (a * n <= b)"
  by (import hollight LE_RDIV_EQ)

lemma LE_LDIV_EQ: "(a::nat) ~= (0::nat)
==> ((b::nat) div a <= (n::nat)) = (b < a * (n + (1::nat)))"
  by (import hollight LE_LDIV_EQ)

lemma LE_LDIV: "(x::nat) ~= (0::nat) & (xa::nat) <= x * (xb::nat) ==> xa div x <= xb"
  by (import hollight LE_LDIV)

lemma DIV_MONO: "(p::nat) ~= (0::nat) & (m::nat) <= (n::nat) ==> m div p <= n div p"
  by (import hollight DIV_MONO)

lemma DIV_MONO_LT: "(p::nat) ~= (0::nat) & (m::nat) + p <= (n::nat) ==> m div p < n div p"
  by (import hollight DIV_MONO_LT)

lemma DIV_EQ_0: "(n::nat) ~= (0::nat) ==> ((m::nat) div n = (0::nat)) = (m < n)"
  by (import hollight DIV_EQ_0)

lemma MOD_EQ_0: "(n::nat) ~= (0::nat)
==> ((m::nat) mod n = (0::nat)) = (EX q::nat. m = q * n)"
  by (import hollight MOD_EQ_0)

lemma EVEN_MOD: "even (n::nat) = (n mod (2::nat) = (0::nat))"
  by (import hollight EVEN_MOD)

lemma ODD_MOD: "odd (n::nat) = (n mod (2::nat) = (1::nat))"
  by (import hollight ODD_MOD)

lemma MOD_MULT_RMOD: "(n::nat) ~= (0::nat) ==> (m::nat) * ((p::nat) mod n) mod n = m * p mod n"
  by (import hollight MOD_MULT_RMOD)

lemma MOD_MULT_LMOD: "(xa::nat) ~= (0::nat) ==> (x::nat) mod xa * (xb::nat) mod xa = x * xb mod xa"
  by (import hollight MOD_MULT_LMOD)

lemma MOD_MULT_MOD2: "(xa::nat) ~= (0::nat)
==> (x::nat) mod xa * ((xb::nat) mod xa) mod xa = x * xb mod xa"
  by (import hollight MOD_MULT_MOD2)

lemma MOD_EXP_MOD: "(n::nat) ~= (0::nat) ==> ((m::nat) mod n) ^ (p::nat) mod n = m ^ p mod n"
  by (import hollight MOD_EXP_MOD)

lemma MOD_ADD_MOD: "(n::nat) ~= (0::nat)
==> ((a::nat) mod n + (b::nat) mod n) mod n = (a + b) mod n"
  by (import hollight MOD_ADD_MOD)

lemma DIV_ADD_MOD: "(n::nat) ~= (0::nat)
==> (((a::nat) + (b::nat)) mod n = a mod n + b mod n) =
    ((a + b) div n = a div n + b div n)"
  by (import hollight DIV_ADD_MOD)

lemma MOD_LE: "(n::nat) ~= (0::nat) ==> (m::nat) mod n <= m"
  by (import hollight MOD_LE)

lemma DIV_MONO2: "(p::nat) ~= (0::nat) & p <= (m::nat) ==> (n::nat) div m <= n div p"
  by (import hollight DIV_MONO2)

lemma DIV_LE_EXCLUSION: "(b::nat) ~= (0::nat) & b * (c::nat) < ((a::nat) + (1::nat)) * (d::nat)
==> c div d <= a div b"
  by (import hollight DIV_LE_EXCLUSION)

lemma DIV_EQ_EXCLUSION: "(b::nat) * (c::nat) < ((a::nat) + (1::nat)) * (d::nat) &
a * d < (c + (1::nat)) * b
==> a div b = c div d"
  by (import hollight DIV_EQ_EXCLUSION)

lemma MULT_DIV_LE: "(p::nat) ~= (0::nat) ==> (m::nat) * ((n::nat) div p) <= m * n div p"
  by (import hollight MULT_DIV_LE)

lemma DIV_DIV: "(xa::nat) * (xb::nat) ~= (0::nat)
==> (x::nat) div xa div xb = x div (xa * xb)"
  by (import hollight DIV_DIV)

lemma DIV_MOD: "(xa::nat) * (xb::nat) ~= (0::nat)
==> (x::nat) div xa mod xb = x mod (xa * xb) div xa"
  by (import hollight DIV_MOD)

lemma PRE_ELIM_THM: "P (n - Suc 0) = (ALL m. n = Suc m | m = 0 & n = 0 --> P m)"
  by (import hollight PRE_ELIM_THM)

lemma SUB_ELIM_THM: "(P::nat => bool) ((a::nat) - (b::nat)) =
(ALL d::nat. a = b + d | a < b & d = (0::nat) --> P d)"
  by (import hollight SUB_ELIM_THM)

lemma DIVMOD_ELIM_THM: "(P::nat => nat => bool) ((m::nat) div (n::nat)) (m mod n) =
(ALL (x::nat) xa::nat.
    n = (0::nat) & x = (0::nat) & xa = m | m = x * n + xa & xa < n -->
    P x xa)"
  by (import hollight DIVMOD_ELIM_THM)

definition
  minimal :: "(nat => bool) => nat"  where
  "minimal == %u. SOME n. u n & (ALL m<n. ~ u m)"

lemma DEF_minimal: "minimal = (%u. SOME n. u n & (ALL m<n. ~ u m))"
  by (import hollight DEF_minimal)

lemma MINIMAL: "Ex P = (P (minimal P) & (ALL x<minimal P. ~ P x))"
  by (import hollight MINIMAL)

lemma TRANSITIVE_STEPWISE_LT_EQ: "(!!x y z. R x y & R y z ==> R x z)
==> (ALL m n. m < n --> R m n) = (ALL n. R n (Suc n))"
  by (import hollight TRANSITIVE_STEPWISE_LT_EQ)

lemma TRANSITIVE_STEPWISE_LT: "[| (ALL x y z. R x y & R y z --> R x z) & (ALL n. R n (Suc n)); m < n |]
==> R m n"
  by (import hollight TRANSITIVE_STEPWISE_LT)

lemma TRANSITIVE_STEPWISE_LE_EQ: "(ALL x. R x x) & (ALL x y z. R x y & R y z --> R x z)
==> (ALL m n. m <= n --> R m n) = (ALL n. R n (Suc n))"
  by (import hollight TRANSITIVE_STEPWISE_LE_EQ)

lemma TRANSITIVE_STEPWISE_LE: "[| (ALL x. R x x) &
   (ALL x y z. R x y & R y z --> R x z) & (ALL n. R n (Suc n));
   m <= n |]
==> R m n"
  by (import hollight TRANSITIVE_STEPWISE_LE)

lemma WF_EQ: "wfP (u_556::'A => 'A => bool) =
(ALL P::'A => bool.
    Ex P = (EX x::'A. P x & (ALL y::'A. u_556 y x --> ~ P y)))"
  by (import hollight WF_EQ)

lemma WF_IND: "wfP (u_556::'A => 'A => bool) =
(ALL P::'A => bool.
    (ALL x::'A. (ALL y::'A. u_556 y x --> P y) --> P x) --> All P)"
  by (import hollight WF_IND)

lemma WF_DCHAIN: "wfP (u_556::'A => 'A => bool) =
(~ (EX s::nat => 'A. ALL n::nat. u_556 (s (Suc n)) (s n)))"
  by (import hollight WF_DCHAIN)

lemma WF_UREC: "[| wfP (u_556::'A => 'A => bool);
   !!(f::'A => 'B) (g::'A => 'B) x::'A.
      (!!z::'A. u_556 z x ==> f z = g z)
      ==> (H::('A => 'B) => 'A => 'B) f x = H g x;
   (ALL x::'A. (f::'A => 'B) x = H f x) &
   (ALL x::'A. (g::'A => 'B) x = H g x) |]
==> f = g"
  by (import hollight WF_UREC)

lemma WF_UREC_WF: "(!!(H::('A => bool) => 'A => bool) (f::'A => bool) g::'A => bool.
    [| !!(f::'A => bool) (g::'A => bool) x::'A.
          (!!z::'A. (u_556::'A => 'A => bool) z x ==> f z = g z)
          ==> H f x = H g x;
       (ALL x::'A. f x = H f x) & (ALL x::'A. g x = H g x) |]
    ==> f = g)
==> wfP u_556"
  by (import hollight WF_UREC_WF)

lemma WF_REC_INVARIANT: "[| wfP (u_556::'A => 'A => bool);
   !!(f::'A => 'B) (g::'A => 'B) x::'A.
      (!!z::'A. u_556 z x ==> f z = g z & (S::'A => 'B => bool) z (f z))
      ==> (H::('A => 'B) => 'A => 'B) f x = H g x & S x (H f x) |]
==> EX f::'A => 'B. ALL x::'A. f x = H f x"
  by (import hollight WF_REC_INVARIANT)

lemma WF_REC: "[| wfP (u_556::'A => 'A => bool);
   !!(f::'A => 'B) (g::'A => 'B) x::'A.
      (!!z::'A. u_556 z x ==> f z = g z)
      ==> (H::('A => 'B) => 'A => 'B) f x = H g x |]
==> EX f::'A => 'B. ALL x::'A. f x = H f x"
  by (import hollight WF_REC)

lemma WF_REC_WF: "(!!H::('A => nat) => 'A => nat.
    (!!(f::'A => nat) (g::'A => nat) x::'A.
        (!!z::'A. (u_556::'A => 'A => bool) z x ==> f z = g z)
        ==> H f x = H g x)
    ==> EX f::'A => nat. ALL x::'A. f x = H f x)
==> wfP u_556"
  by (import hollight WF_REC_WF)

lemma WF_EREC: "[| wfP (u_556::'A => 'A => bool);
   !!(f::'A => 'B) (g::'A => 'B) x::'A.
      (!!z::'A. u_556 z x ==> f z = g z)
      ==> (H::('A => 'B) => 'A => 'B) f x = H g x |]
==> EX! f::'A => 'B. ALL x::'A. f x = H f x"
  by (import hollight WF_EREC)

lemma WF_SUBSET: "(ALL (x::'A) y::'A.
    (u_556::'A => 'A => bool) x y --> (u_670::'A => 'A => bool) x y) &
wfP u_670
==> wfP u_556"
  by (import hollight WF_SUBSET)

lemma WF_MEASURE_GEN: "wfP (u_556::'B => 'B => bool)
==> wfP (%(x::'A) x'::'A. u_556 ((m::'A => 'B) x) (m x'))"
  by (import hollight WF_MEASURE_GEN)

lemma WF_LEX_DEPENDENT: "wfP (R::'A => 'A => bool) & (ALL x::'A. wfP ((S::'A => 'B => 'B => bool) x))
==> wfP (SOME f::'A * 'B => 'A * 'B => bool.
            ALL (r1::'A) s1::'B.
               f (r1, s1) =
               (SOME f::'A * 'B => bool.
                   ALL (r2::'A) s2::'B.
                      f (r2, s2) = (R r1 r2 | r1 = r2 & S r1 s1 s2)))"
  by (import hollight WF_LEX_DEPENDENT)

lemma WF_LEX: "wfP (x::'A => 'A => bool) & wfP (xa::'B => 'B => bool)
==> wfP (SOME f::'A * 'B => 'A * 'B => bool.
            ALL (r1::'A) s1::'B.
               f (r1, s1) =
               (SOME f::'A * 'B => bool.
                   ALL (r2::'A) s2::'B.
                      f (r2, s2) = (x r1 r2 | r1 = r2 & xa s1 s2)))"
  by (import hollight WF_LEX)

lemma WF_POINTWISE: "wfP (u_556::'A => 'A => bool) & wfP (u_670::'B => 'B => bool)
==> wfP (SOME f::'A * 'B => 'A * 'B => bool.
            ALL (x1::'A) y1::'B.
               f (x1, y1) =
               (SOME f::'A * 'B => bool.
                   ALL (x2::'A) y2::'B.
                      f (x2, y2) = (u_556 x1 x2 & u_670 y1 y2)))"
  by (import hollight WF_POINTWISE)

lemma WF_num: "(wfP::(nat => nat => bool) => bool) (op <::nat => nat => bool)"
  by (import hollight WF_num)

lemma WF_REC_num: "(!!(f::nat => 'A) (g::nat => 'A) x::nat.
    (!!z::nat. z < x ==> f z = g z)
    ==> (H::(nat => 'A) => nat => 'A) f x = H g x)
==> EX f::nat => 'A. ALL x::nat. f x = H f x"
  by (import hollight WF_REC_num)

lemma WF_MEASURE: "wfP (%(a::'A) b::'A. (a, b) : measure (m::'A => nat))"
  by (import hollight WF_MEASURE)

lemma MEASURE_LE: "(ALL x::'q_12099.
    (x, a::'q_12099) : measure (m::'q_12099 => nat) -->
    (x, b::'q_12099) : measure m) =
(m a <= m b)"
  by (import hollight MEASURE_LE)

lemma WF_REFL: "wfP (u_556::'A => 'A => bool) ==> ~ u_556 (x::'A) x"
  by (import hollight WF_REFL)

lemma WF_REC_TAIL: "EX f::'A => 'B.
   ALL x::'A.
      f x =
      (if (P::'A => bool) x then f ((g::'A => 'A) x) else (h::'A => 'B) x)"
  by (import hollight WF_REC_TAIL)

lemma WF_REC_TAIL_GENERAL: "wfP (u_556::'A => 'A => bool) &
(ALL (f::'A => 'B) (g::'A => 'B) x::'A.
    (ALL z::'A. u_556 z x --> f z = g z) -->
    (P::('A => 'B) => 'A => bool) f x = P g x &
    (G::('A => 'B) => 'A => 'A) f x = G g x &
    (H::('A => 'B) => 'A => 'B) f x = H g x) &
(ALL (f::'A => 'B) (g::'A => 'B) x::'A.
    (ALL z::'A. u_556 z x --> f z = g z) --> H f x = H g x) &
(ALL (f::'A => 'B) (x::'A) y::'A. P f x & u_556 y (G f x) --> u_556 y x)
==> EX f::'A => 'B. ALL x::'A. f x = (if P f x then f (G f x) else H f x)"
  by (import hollight WF_REC_TAIL_GENERAL)

lemma ARITH_ZERO: "(0::nat) = (0::nat) & (0::nat) = (0::nat)"
  by (import hollight ARITH_ZERO)

lemma ARITH_SUC: "(ALL x. Suc x = Suc x) &
Suc 0 = 1 &
(ALL x. Suc (2 * x) = 2 * x + 1) & (ALL x. Suc (2 * x + 1) = 2 * Suc x)"
  by (import hollight ARITH_SUC)

lemma ARITH_PRE: "(ALL x. x - Suc 0 = x - Suc 0) &
0 - Suc 0 = 0 &
(ALL x. 2 * x - Suc 0 = (if x = 0 then 0 else 2 * (x - Suc 0) + 1)) &
(ALL x. 2 * x + 1 - Suc 0 = 2 * x)"
  by (import hollight ARITH_PRE)

lemma ARITH_ADD: "(ALL (x::nat) xa::nat. x + xa = x + xa) &
(0::nat) + (0::nat) = (0::nat) &
(ALL x::nat. (0::nat) + (2::nat) * x = (2::nat) * x) &
(ALL x::nat.
    (0::nat) + ((2::nat) * x + (1::nat)) = (2::nat) * x + (1::nat)) &
(ALL x::nat. (2::nat) * x + (0::nat) = (2::nat) * x) &
(ALL x::nat. (2::nat) * x + (1::nat) + (0::nat) = (2::nat) * x + (1::nat)) &
(ALL (x::nat) xa::nat. (2::nat) * x + (2::nat) * xa = (2::nat) * (x + xa)) &
(ALL (x::nat) xa::nat.
    (2::nat) * x + ((2::nat) * xa + (1::nat)) =
    (2::nat) * (x + xa) + (1::nat)) &
(ALL (x::nat) xa::nat.
    (2::nat) * x + (1::nat) + (2::nat) * xa =
    (2::nat) * (x + xa) + (1::nat)) &
(ALL (x::nat) xa::nat.
    (2::nat) * x + (1::nat) + ((2::nat) * xa + (1::nat)) =
    (2::nat) * Suc (x + xa))"
  by (import hollight ARITH_ADD)

lemma ARITH_MULT: "(ALL (x::nat) xa::nat. x * xa = x * xa) &
(0::nat) * (0::nat) = (0::nat) &
(ALL x::nat. (0::nat) * ((2::nat) * x) = (0::nat)) &
(ALL x::nat. (0::nat) * ((2::nat) * x + (1::nat)) = (0::nat)) &
(ALL x::nat. (2::nat) * x * (0::nat) = (0::nat)) &
(ALL x::nat. ((2::nat) * x + (1::nat)) * (0::nat) = (0::nat)) &
(ALL (x::nat) xa::nat.
    (2::nat) * x * ((2::nat) * xa) = (2::nat) * ((2::nat) * (x * xa))) &
(ALL (x::nat) xa::nat.
    (2::nat) * x * ((2::nat) * xa + (1::nat)) =
    (2::nat) * x + (2::nat) * ((2::nat) * (x * xa))) &
(ALL (x::nat) xa::nat.
    ((2::nat) * x + (1::nat)) * ((2::nat) * xa) =
    (2::nat) * xa + (2::nat) * ((2::nat) * (x * xa))) &
(ALL (x::nat) xa::nat.
    ((2::nat) * x + (1::nat)) * ((2::nat) * xa + (1::nat)) =
    (2::nat) * x + (1::nat) +
    ((2::nat) * xa + (2::nat) * ((2::nat) * (x * xa))))"
  by (import hollight ARITH_MULT)

lemma ARITH_EXP: "(ALL (x::nat) xa::nat. x ^ xa = x ^ xa) &
(0::nat) ^ (0::nat) = (1::nat) &
(ALL m::nat. ((2::nat) * m) ^ (0::nat) = (1::nat)) &
(ALL m::nat. ((2::nat) * m + (1::nat)) ^ (0::nat) = (1::nat)) &
(ALL n::nat. (0::nat) ^ ((2::nat) * n) = (0::nat) ^ n * (0::nat) ^ n) &
(ALL (m::nat) n::nat.
    ((2::nat) * m) ^ ((2::nat) * n) =
    ((2::nat) * m) ^ n * ((2::nat) * m) ^ n) &
(ALL (m::nat) n::nat.
    ((2::nat) * m + (1::nat)) ^ ((2::nat) * n) =
    ((2::nat) * m + (1::nat)) ^ n * ((2::nat) * m + (1::nat)) ^ n) &
(ALL n::nat. (0::nat) ^ ((2::nat) * n + (1::nat)) = (0::nat)) &
(ALL (m::nat) n::nat.
    ((2::nat) * m) ^ ((2::nat) * n + (1::nat)) =
    (2::nat) * m * (((2::nat) * m) ^ n * ((2::nat) * m) ^ n)) &
(ALL (m::nat) n::nat.
    ((2::nat) * m + (1::nat)) ^ ((2::nat) * n + (1::nat)) =
    ((2::nat) * m + (1::nat)) *
    (((2::nat) * m + (1::nat)) ^ n * ((2::nat) * m + (1::nat)) ^ n))"
  by (import hollight ARITH_EXP)

lemma ARITH_EVEN: "(ALL x::nat. even x = even x) &
even (0::nat) = True &
(ALL x::nat. even ((2::nat) * x) = True) &
(ALL x::nat. even ((2::nat) * x + (1::nat)) = False)"
  by (import hollight ARITH_EVEN)

lemma ARITH_ODD: "(ALL x::nat. odd x = odd x) &
odd (0::nat) = False &
(ALL x::nat. odd ((2::nat) * x) = False) &
(ALL x::nat. odd ((2::nat) * x + (1::nat)) = True)"
  by (import hollight ARITH_ODD)

lemma ARITH_LE: "(ALL (x::nat) xa::nat. (x <= xa) = (x <= xa)) &
((0::nat) <= (0::nat)) = True &
(ALL x::nat. ((2::nat) * x <= (0::nat)) = (x <= (0::nat))) &
(ALL x::nat. ((2::nat) * x + (1::nat) <= (0::nat)) = False) &
(ALL x::nat. ((0::nat) <= (2::nat) * x) = True) &
(ALL x::nat. ((0::nat) <= (2::nat) * x + (1::nat)) = True) &
(ALL (x::nat) xa::nat. ((2::nat) * x <= (2::nat) * xa) = (x <= xa)) &
(ALL (x::nat) xa::nat.
    ((2::nat) * x <= (2::nat) * xa + (1::nat)) = (x <= xa)) &
(ALL (x::nat) xa::nat.
    ((2::nat) * x + (1::nat) <= (2::nat) * xa) = (x < xa)) &
(ALL (x::nat) xa::nat.
    ((2::nat) * x + (1::nat) <= (2::nat) * xa + (1::nat)) = (x <= xa))"
  by (import hollight ARITH_LE)

lemma ARITH_LT: "(ALL (x::nat) xa::nat. (x < xa) = (x < xa)) &
((0::nat) < (0::nat)) = False &
(ALL x::nat. ((2::nat) * x < (0::nat)) = False) &
(ALL x::nat. ((2::nat) * x + (1::nat) < (0::nat)) = False) &
(ALL x::nat. ((0::nat) < (2::nat) * x) = ((0::nat) < x)) &
(ALL x::nat. ((0::nat) < (2::nat) * x + (1::nat)) = True) &
(ALL (x::nat) xa::nat. ((2::nat) * x < (2::nat) * xa) = (x < xa)) &
(ALL (x::nat) xa::nat.
    ((2::nat) * x < (2::nat) * xa + (1::nat)) = (x <= xa)) &
(ALL (x::nat) xa::nat.
    ((2::nat) * x + (1::nat) < (2::nat) * xa) = (x < xa)) &
(ALL (x::nat) xa::nat.
    ((2::nat) * x + (1::nat) < (2::nat) * xa + (1::nat)) = (x < xa))"
  by (import hollight ARITH_LT)

lemma ARITH_EQ: "(ALL (x::nat) xa::nat. (x = xa) = (x = xa)) &
((0::nat) = (0::nat)) = True &
(ALL x::nat. ((2::nat) * x = (0::nat)) = (x = (0::nat))) &
(ALL x::nat. ((2::nat) * x + (1::nat) = (0::nat)) = False) &
(ALL x::nat. ((0::nat) = (2::nat) * x) = ((0::nat) = x)) &
(ALL x::nat. ((0::nat) = (2::nat) * x + (1::nat)) = False) &
(ALL (x::nat) xa::nat. ((2::nat) * x = (2::nat) * xa) = (x = xa)) &
(ALL (x::nat) xa::nat. ((2::nat) * x = (2::nat) * xa + (1::nat)) = False) &
(ALL (x::nat) xa::nat. ((2::nat) * x + (1::nat) = (2::nat) * xa) = False) &
(ALL (x::nat) xa::nat.
    ((2::nat) * x + (1::nat) = (2::nat) * xa + (1::nat)) = (x = xa))"
  by (import hollight ARITH_EQ)

lemma ARITH_SUB: "(ALL (x::nat) xa::nat. x - xa = x - xa) &
(0::nat) - (0::nat) = (0::nat) &
(ALL x::nat. (0::nat) - (2::nat) * x = (0::nat)) &
(ALL x::nat. (0::nat) - ((2::nat) * x + (1::nat)) = (0::nat)) &
(ALL x::nat. (2::nat) * x - (0::nat) = (2::nat) * x) &
(ALL x::nat. (2::nat) * x + (1::nat) - (0::nat) = (2::nat) * x + (1::nat)) &
(ALL (m::nat) n::nat. (2::nat) * m - (2::nat) * n = (2::nat) * (m - n)) &
(ALL (m::nat) n::nat.
    (2::nat) * m - ((2::nat) * n + (1::nat)) =
    (2::nat) * (m - n) - Suc (0::nat)) &
(ALL (m::nat) n::nat.
    (2::nat) * m + (1::nat) - (2::nat) * n =
    (if n <= m then (2::nat) * (m - n) + (1::nat) else (0::nat))) &
(ALL (m::nat) n::nat.
    (2::nat) * m + (1::nat) - ((2::nat) * n + (1::nat)) =
    (2::nat) * (m - n))"
  by (import hollight ARITH_SUB)

lemma right_th: "(s::nat) * ((2::nat) * (x::nat) + (1::nat)) = s + (2::nat) * (s * x)"
  by (import hollight right_th)

lemma SEMIRING_PTHS: "(ALL (x::'A) (y::'A) z::'A.
    (add::'A => 'A => 'A) x (add y z) = add (add x y) z) &
(ALL (x::'A) y::'A. add x y = add y x) &
(ALL x::'A. add (r0::'A) x = x) &
(ALL (x::'A) (y::'A) z::'A.
    (mul::'A => 'A => 'A) x (mul y z) = mul (mul x y) z) &
(ALL (x::'A) y::'A. mul x y = mul y x) &
(ALL x::'A. mul (r1::'A) x = x) &
(ALL x::'A. mul r0 x = r0) &
(ALL (x::'A) (y::'A) z::'A. mul x (add y z) = add (mul x y) (mul x z)) &
(ALL x::'A. (pwr::'A => nat => 'A) x (0::nat) = r1) &
(ALL (x::'A) n::nat. pwr x (Suc n) = mul x (pwr x n))
==> mul r1 (x::'A) = x &
    add (mul (a::'A) (m::'A)) (mul (b::'A) m) = mul (add a b) m &
    add (mul a m) m = mul (add a r1) m &
    add m (mul a m) = mul (add a r1) m &
    add m m = mul (add r1 r1) m &
    mul r0 m = r0 &
    add r0 a = a &
    add a r0 = a &
    mul a b = mul b a &
    mul (add a b) (c::'A) = add (mul a c) (mul b c) &
    mul r0 a = r0 &
    mul a r0 = r0 &
    mul r1 a = a &
    mul a r1 = a &
    mul (mul (lx::'A) (ly::'A)) (mul (rx::'A) (ry::'A)) =
    mul (mul lx rx) (mul ly ry) &
    mul (mul lx ly) (mul rx ry) = mul lx (mul ly (mul rx ry)) &
    mul (mul lx ly) (mul rx ry) = mul rx (mul (mul lx ly) ry) &
    mul (mul lx ly) rx = mul (mul lx rx) ly &
    mul (mul lx ly) rx = mul lx (mul ly rx) &
    mul lx rx = mul rx lx &
    mul lx (mul rx ry) = mul (mul lx rx) ry &
    mul lx (mul rx ry) = mul rx (mul lx ry) &
    add (add a b) (add c (d::'A)) = add (add a c) (add b d) &
    add (add a b) c = add a (add b c) &
    add a (add c d) = add c (add a d) &
    add (add a b) c = add (add a c) b &
    add a c = add c a &
    add a (add c d) = add (add a c) d &
    mul (pwr x (p::nat)) (pwr x (q::nat)) = pwr x (p + q) &
    mul x (pwr x q) = pwr x (Suc q) &
    mul (pwr x q) x = pwr x (Suc q) &
    mul x x = pwr x (2::nat) &
    pwr (mul x (y::'A)) q = mul (pwr x q) (pwr y q) &
    pwr (pwr x p) q = pwr x (p * q) &
    pwr x (0::nat) = r1 &
    pwr x (1::nat) = x &
    mul x (add y (z::'A)) = add (mul x y) (mul x z) &
    pwr x (Suc q) = mul x (pwr x q)"
  by (import hollight SEMIRING_PTHS)

lemma NUM_INTEGRAL_LEMMA: "(w::nat) = (x::nat) + (d::nat) & (y::nat) = (z::nat) + (e::nat)
==> (w * y + x * z = w * z + x * y) = (w = x | y = z)"
  by (import hollight NUM_INTEGRAL_LEMMA)

lemma NUM_INTEGRAL: "(ALL x::nat. (0::nat) * x = (0::nat)) &
(ALL (x::nat) (xa::nat) xb::nat. (x + xa = x + xb) = (xa = xb)) &
(ALL (w::nat) (x::nat) (y::nat) z::nat.
    (w * y + x * z = w * z + x * y) = (w = x | y = z))"
  by (import hollight NUM_INTEGRAL)

lemma INJ_INVERSE2: "(!!(x1::'A) (y1::'B) (x2::'A) y2::'B.
    ((P::'A => 'B => 'C) x1 y1 = P x2 y2) = (x1 = x2 & y1 = y2))
==> EX (x::'C => 'A) Y::'C => 'B.
       ALL (xa::'A) y::'B. x (P xa y) = xa & Y (P xa y) = y"
  by (import hollight INJ_INVERSE2)

definition
  NUMPAIR :: "nat => nat => nat"  where
  "NUMPAIR == %u ua. 2 ^ u * (2 * ua + 1)"

lemma DEF_NUMPAIR: "NUMPAIR = (%u ua. 2 ^ u * (2 * ua + 1))"
  by (import hollight DEF_NUMPAIR)

lemma NUMPAIR_INJ_LEMMA: "NUMPAIR x xa = NUMPAIR xb xc ==> x = xb"
  by (import hollight NUMPAIR_INJ_LEMMA)

lemma NUMPAIR_INJ: "(NUMPAIR x1 y1 = NUMPAIR x2 y2) = (x1 = x2 & y1 = y2)"
  by (import hollight NUMPAIR_INJ)

definition
  NUMFST :: "nat => nat"  where
  "NUMFST == SOME X. EX Y. ALL x y. X (NUMPAIR x y) = x & Y (NUMPAIR x y) = y"

lemma DEF_NUMFST: "NUMFST = (SOME X. EX Y. ALL x y. X (NUMPAIR x y) = x & Y (NUMPAIR x y) = y)"
  by (import hollight DEF_NUMFST)

definition
  NUMSND :: "nat => nat"  where
  "NUMSND == SOME Y. ALL x y. NUMFST (NUMPAIR x y) = x & Y (NUMPAIR x y) = y"

lemma DEF_NUMSND: "NUMSND = (SOME Y. ALL x y. NUMFST (NUMPAIR x y) = x & Y (NUMPAIR x y) = y)"
  by (import hollight DEF_NUMSND)

definition
  NUMSUM :: "bool => nat => nat"  where
  "NUMSUM == %u ua. if u then Suc (2 * ua) else 2 * ua"

lemma DEF_NUMSUM: "NUMSUM = (%u ua. if u then Suc (2 * ua) else 2 * ua)"
  by (import hollight DEF_NUMSUM)

lemma NUMSUM_INJ: "(NUMSUM b1 x1 = NUMSUM b2 x2) = (b1 = b2 & x1 = x2)"
  by (import hollight NUMSUM_INJ)

definition
  NUMLEFT :: "nat => bool"  where
  "NUMLEFT == SOME X. EX Y. ALL x y. X (NUMSUM x y) = x & Y (NUMSUM x y) = y"

lemma DEF_NUMLEFT: "NUMLEFT = (SOME X. EX Y. ALL x y. X (NUMSUM x y) = x & Y (NUMSUM x y) = y)"
  by (import hollight DEF_NUMLEFT)

definition
  NUMRIGHT :: "nat => nat"  where
  "NUMRIGHT == SOME Y. ALL x y. NUMLEFT (NUMSUM x y) = x & Y (NUMSUM x y) = y"

lemma DEF_NUMRIGHT: "NUMRIGHT = (SOME Y. ALL x y. NUMLEFT (NUMSUM x y) = x & Y (NUMSUM x y) = y)"
  by (import hollight DEF_NUMRIGHT)

definition
  INJN :: "nat => nat => 'A => bool"  where
  "INJN == %(u::nat) (n::nat) a::'A. n = u"

lemma DEF_INJN: "INJN = (%(u::nat) (n::nat) a::'A. n = u)"
  by (import hollight DEF_INJN)

lemma INJN_INJ: "(op =::bool => bool => bool)
 ((op =::(nat => 'A::type => bool) => (nat => 'A::type => bool) => bool)
   ((INJN::nat => nat => 'A::type => bool) (n1::nat))
   ((INJN::nat => nat => 'A::type => bool) (n2::nat)))
 ((op =::nat => nat => bool) n1 n2)"
  by (import hollight INJN_INJ)

definition
  INJA :: "'A => nat => 'A => bool"  where
  "INJA == %(u::'A) (n::nat) b::'A. b = u"

lemma DEF_INJA: "INJA = (%(u::'A) (n::nat) b::'A. b = u)"
  by (import hollight DEF_INJA)

lemma INJA_INJ: "(INJA (a1::'A) = INJA (a2::'A)) = (a1 = a2)"
  by (import hollight INJA_INJ)

definition
  INJF :: "(nat => nat => 'A => bool) => nat => 'A => bool"  where
  "INJF == %(u::nat => nat => 'A => bool) n::nat. u (NUMFST n) (NUMSND n)"

lemma DEF_INJF: "INJF = (%(u::nat => nat => 'A => bool) n::nat. u (NUMFST n) (NUMSND n))"
  by (import hollight DEF_INJF)

lemma INJF_INJ: "(INJF (f1::nat => nat => 'A => bool) =
 INJF (f2::nat => nat => 'A => bool)) =
(f1 = f2)"
  by (import hollight INJF_INJ)

definition
  INJP :: "(nat => 'A => bool) => (nat => 'A => bool) => nat => 'A => bool"  where
  "INJP ==
%(u::nat => 'A => bool) (ua::nat => 'A => bool) (n::nat) a::'A.
   if NUMLEFT n then u (NUMRIGHT n) a else ua (NUMRIGHT n) a"

lemma DEF_INJP: "INJP =
(%(u::nat => 'A => bool) (ua::nat => 'A => bool) (n::nat) a::'A.
    if NUMLEFT n then u (NUMRIGHT n) a else ua (NUMRIGHT n) a)"
  by (import hollight DEF_INJP)

lemma INJP_INJ: "(INJP (f1::nat => 'A => bool) (f2::nat => 'A => bool) =
 INJP (f1'::nat => 'A => bool) (f2'::nat => 'A => bool)) =
(f1 = f1' & f2 = f2')"
  by (import hollight INJP_INJ)

definition
  ZCONSTR :: "nat => 'A => (nat => nat => 'A => bool) => nat => 'A => bool"  where
  "ZCONSTR ==
%(u::nat) (ua::'A) ub::nat => nat => 'A => bool.
   INJP (INJN (Suc u)) (INJP (INJA ua) (INJF ub))"

lemma DEF_ZCONSTR: "ZCONSTR =
(%(u::nat) (ua::'A) ub::nat => nat => 'A => bool.
    INJP (INJN (Suc u)) (INJP (INJA ua) (INJF ub)))"
  by (import hollight DEF_ZCONSTR)

definition
  ZBOT :: "nat => 'A => bool"  where
  "ZBOT == INJP (INJN (0::nat)) (SOME z::nat => 'A => bool. True)"

lemma DEF_ZBOT: "ZBOT = INJP (INJN (0::nat)) (SOME z::nat => 'A => bool. True)"
  by (import hollight DEF_ZBOT)

lemma ZCONSTR_ZBOT: "ZCONSTR (x::nat) (xa::'A) (xb::nat => nat => 'A => bool) ~= ZBOT"
  by (import hollight ZCONSTR_ZBOT)

definition
  ZRECSPACE :: "(nat => 'A => bool) => bool"  where
  "ZRECSPACE ==
%a::nat => 'A => bool.
   ALL ZRECSPACE'::(nat => 'A => bool) => bool.
      (ALL a::nat => 'A => bool.
          a = ZBOT |
          (EX (c::nat) (i::'A) r::nat => nat => 'A => bool.
              a = ZCONSTR c i r & (ALL n::nat. ZRECSPACE' (r n))) -->
          ZRECSPACE' a) -->
      ZRECSPACE' a"

lemma DEF_ZRECSPACE: "ZRECSPACE =
(%a::nat => 'A => bool.
    ALL ZRECSPACE'::(nat => 'A => bool) => bool.
       (ALL a::nat => 'A => bool.
           a = ZBOT |
           (EX (c::nat) (i::'A) r::nat => nat => 'A => bool.
               a = ZCONSTR c i r & (ALL n::nat. ZRECSPACE' (r n))) -->
           ZRECSPACE' a) -->
       ZRECSPACE' a)"
  by (import hollight DEF_ZRECSPACE)

typedef (open) 'a recspace = "Collect ZRECSPACE :: (nat \<Rightarrow> 'a \<Rightarrow> bool) set" 
  morphisms "_dest_rec" "_mk_rec"
  apply (rule light_ex_imp_nonempty [where t="ZBOT"])
  by (import hollight TYDEF_recspace)

syntax
  "_dest_rec" :: _ ("'_dest'_rec")

syntax
  "_mk_rec" :: _ ("'_mk'_rec")

lemmas "TYDEF_recspace_@intern" = typedef_hol2hollight 
  [where a="a :: 'A recspace" and r=r ,
   OF type_definition_recspace]

definition
  BOTTOM :: "'A recspace"  where
  "BOTTOM == _mk_rec ZBOT"

lemma DEF_BOTTOM: "BOTTOM = _mk_rec ZBOT"
  by (import hollight DEF_BOTTOM)

definition
  CONSTR :: "nat => 'A => (nat => 'A recspace) => 'A recspace"  where
  "CONSTR ==
%(u::nat) (ua::'A::type) ub::nat => 'A::type recspace.
   _mk_rec (ZCONSTR u ua (%n::nat. _dest_rec (ub n)))"

lemma DEF_CONSTR: "CONSTR =
(%(u::nat) (ua::'A::type) ub::nat => 'A::type recspace.
    _mk_rec (ZCONSTR u ua (%n::nat. _dest_rec (ub n))))"
  by (import hollight DEF_CONSTR)

lemma MK_REC_INJ: "[| _mk_rec (x::nat => 'A::type => bool) =
   _mk_rec (y::nat => 'A::type => bool);
   ZRECSPACE x & ZRECSPACE y |]
==> x = y"
  by (import hollight MK_REC_INJ)

lemma CONSTR_BOT: "CONSTR (c::nat) (i::'A) (r::nat => 'A recspace) ~= BOTTOM"
  by (import hollight CONSTR_BOT)

lemma CONSTR_INJ: "(CONSTR (c1::nat) (i1::'A) (r1::nat => 'A recspace) =
 CONSTR (c2::nat) (i2::'A) (r2::nat => 'A recspace)) =
(c1 = c2 & i1 = i2 & r1 = r2)"
  by (import hollight CONSTR_INJ)

lemma CONSTR_IND: "(P::'A recspace => bool) BOTTOM &
(ALL (c::nat) (i::'A) r::nat => 'A recspace.
    (ALL n::nat. P (r n)) --> P (CONSTR c i r))
==> P (x::'A recspace)"
  by (import hollight CONSTR_IND)

lemma CONSTR_REC: "EX f::'A recspace => 'B.
   ALL (c::nat) (i::'A) r::nat => 'A recspace.
      f (CONSTR c i r) =
      (Fn::nat => 'A => (nat => 'A recspace) => (nat => 'B) => 'B) c i r
       (%n::nat. f (r n))"
  by (import hollight CONSTR_REC)

definition
  FCONS :: "'A => (nat => 'A) => nat => 'A"  where
  "FCONS ==
SOME FCONS::'A => (nat => 'A) => nat => 'A.
   (ALL (a::'A) f::nat => 'A. FCONS a f (0::nat) = a) &
   (ALL (a::'A) (f::nat => 'A) n::nat. FCONS a f (Suc n) = f n)"

lemma DEF_FCONS: "FCONS =
(SOME FCONS::'A => (nat => 'A) => nat => 'A.
    (ALL (a::'A) f::nat => 'A. FCONS a f (0::nat) = a) &
    (ALL (a::'A) (f::nat => 'A) n::nat. FCONS a f (Suc n) = f n))"
  by (import hollight DEF_FCONS)

lemma FCONS_UNDO: "(f::nat => 'A) = FCONS (f (0::nat)) (f o Suc)"
  by (import hollight FCONS_UNDO)

definition
  FNIL :: "nat => 'A"  where
  "FNIL == %u::nat. SOME x::'A. True"

lemma DEF_FNIL: "FNIL = (%u::nat. SOME x::'A. True)"
  by (import hollight DEF_FNIL)

definition
  ISO :: "('A => 'B) => ('B => 'A) => bool"  where
  "ISO ==
%(u::'A => 'B) ua::'B => 'A.
   (ALL x::'B. u (ua x) = x) & (ALL y::'A. ua (u y) = y)"

lemma DEF_ISO: "ISO =
(%(u::'A => 'B) ua::'B => 'A.
    (ALL x::'B. u (ua x) = x) & (ALL y::'A. ua (u y) = y))"
  by (import hollight DEF_ISO)

lemma ISO_REFL: "ISO (%x::'A. x) (%x::'A. x)"
  by (import hollight ISO_REFL)

lemma ISO_FUN: "ISO (f::'A => 'A') (f'::'A' => 'A) & ISO (g::'B => 'B') (g'::'B' => 'B)
==> ISO (%(h::'A => 'B) a'::'A'. g (h (f' a')))
     (%(h::'A' => 'B') a::'A. g' (h (f a)))"
  by (import hollight ISO_FUN)

lemma ISO_USAGE: "ISO (f::'q_17485 => 'q_17482) (g::'q_17482 => 'q_17485)
==> (ALL P::'q_17485 => bool. All P = (ALL x::'q_17482. P (g x))) &
    (ALL P::'q_17485 => bool. Ex P = (EX x::'q_17482. P (g x))) &
    (ALL (a::'q_17485) b::'q_17482. (a = g b) = (f a = b))"
  by (import hollight ISO_USAGE)

typedef (open) char = "{a. ALL char'.
       (ALL a.
           (EX a0 a1 a2 a3 a4 a5 a6 a7.
               a =
               CONSTR (NUMERAL 0) (a0 :: bool, a1 :: bool, a2 :: bool, a3 :: bool, a4 :: bool, a5 :: bool, a6 :: bool, a7:: bool)
                (%n. BOTTOM)) -->
           char' a) -->
       char' a}"
  morphisms "_dest_char" "_mk_char"
  apply (rule light_ex_imp_nonempty [where t="CONSTR (NUMERAL 0) (a0, a1, a2, a3, a4, a5, a6, a7) (%n. BOTTOM)"])
  by (import hollight TYDEF_char)

syntax
  "_dest_char" :: _ ("'_dest'_char")

syntax
  "_mk_char" :: _ ("'_mk'_char")

lemmas "TYDEF_char_@intern" = typedef_hol2hollight 
  [where a="a :: hollight.char" and r=r ,
   OF type_definition_char]

consts
  "_11937" :: "bool
=> bool => bool => bool => bool => bool => bool => bool => hollight.char" ("'_11937")

defs
  "_11937_def": "_11937 ==
%(a0::bool) (a1::bool) (a2::bool) (a3::bool) (a4::bool) (a5::bool)
   (a6::bool) a7::bool.
   _mk_char
    (CONSTR (0::nat) (a0, a1, a2, a3, a4, a5, a6, a7) (%n::nat. BOTTOM))"

lemma DEF__11937: "_11937 =
(%(a0::bool) (a1::bool) (a2::bool) (a3::bool) (a4::bool) (a5::bool)
    (a6::bool) a7::bool.
    _mk_char
     (CONSTR (0::nat) (a0, a1, a2, a3, a4, a5, a6, a7) (%n::nat. BOTTOM)))"
  by (import hollight DEF__11937)

definition
  ASCII :: "bool
=> bool => bool => bool => bool => bool => bool => bool => hollight.char"  where
  "ASCII == _11937"

lemma DEF_ASCII: "ASCII = _11937"
  by (import hollight DEF_ASCII)

consts
  dist :: "nat * nat => nat" 

defs
  dist_def: "hollight.dist == %u. fst u - snd u + (snd u - fst u)"

lemma DEF_dist: "hollight.dist = (%u. fst u - snd u + (snd u - fst u))"
  by (import hollight DEF_dist)

lemma DIST_REFL: "hollight.dist (x, x) = 0"
  by (import hollight DIST_REFL)

lemma DIST_LZERO: "hollight.dist (0, x) = x"
  by (import hollight DIST_LZERO)

lemma DIST_RZERO: "hollight.dist (x, 0) = x"
  by (import hollight DIST_RZERO)

lemma DIST_SYM: "hollight.dist (x, xa) = hollight.dist (xa, x)"
  by (import hollight DIST_SYM)

lemma DIST_LADD: "hollight.dist (x + xb, x + xa) = hollight.dist (xb, xa)"
  by (import hollight DIST_LADD)

lemma DIST_RADD: "hollight.dist (x + xa, xb + xa) = hollight.dist (x, xb)"
  by (import hollight DIST_RADD)

lemma DIST_LADD_0: "hollight.dist (x + xa, x) = xa"
  by (import hollight DIST_LADD_0)

lemma DIST_RADD_0: "hollight.dist (x, x + xa) = xa"
  by (import hollight DIST_RADD_0)

lemma DIST_LMUL: "x * hollight.dist (xa, xb) = hollight.dist (x * xa, x * xb)"
  by (import hollight DIST_LMUL)

lemma DIST_RMUL: "hollight.dist (x, xa) * xb = hollight.dist (x * xb, xa * xb)"
  by (import hollight DIST_RMUL)

lemma DIST_EQ_0: "(hollight.dist (x, xa) = 0) = (x = xa)"
  by (import hollight DIST_EQ_0)

lemma DIST_ELIM_THM: "P (hollight.dist (x, y)) =
(ALL d. (x = y + d --> P d) & (y = x + d --> P d))"
  by (import hollight DIST_ELIM_THM)

lemma DIST_LE_CASES: "(hollight.dist (m, n) <= p) = (m <= n + p & n <= m + p)"
  by (import hollight DIST_LE_CASES)

lemma DIST_TRIANGLE_LE: "hollight.dist (m, n) + hollight.dist (n, p) <= q
==> hollight.dist (m, p) <= q"
  by (import hollight DIST_TRIANGLE_LE)

lemma DIST_TRIANGLES_LE: "hollight.dist (m, n) <= r & hollight.dist (p, q) <= s
==> hollight.dist (m, p) <= hollight.dist (n, q) + (r + s)"
  by (import hollight DIST_TRIANGLES_LE)

lemma BOUNDS_LINEAR: "(ALL n::nat. (A::nat) * n <= (B::nat) * n + (C::nat)) = (A <= B)"
  by (import hollight BOUNDS_LINEAR)

lemma BOUNDS_LINEAR_0: "(ALL n::nat. (A::nat) * n <= (B::nat)) = (A = (0::nat))"
  by (import hollight BOUNDS_LINEAR_0)

lemma BOUNDS_DIVIDED: "(EX B::nat. ALL n::nat. (P::nat => nat) n <= B) =
(EX (x::nat) B::nat. ALL n::nat. n * P n <= x * n + B)"
  by (import hollight BOUNDS_DIVIDED)

lemma BOUNDS_NOTZERO: "(P::nat => nat => nat) (0::nat) (0::nat) = (0::nat) &
(ALL (m::nat) n::nat. P m n <= (A::nat) * (m + n) + (B::nat))
==> EX x::nat. ALL (m::nat) n::nat. P m n <= x * (m + n)"
  by (import hollight BOUNDS_NOTZERO)

lemma BOUNDS_IGNORE: "(EX B::nat. ALL i::nat. (P::nat => nat) i <= (Q::nat => nat) i + B) =
(EX (x::nat) N::nat. ALL i>=N. P i <= Q i + x)"
  by (import hollight BOUNDS_IGNORE)

definition
  is_nadd :: "(nat => nat) => bool"  where
  "is_nadd ==
%u. EX B. ALL m n. hollight.dist (m * u n, n * u m) <= B * (m + n)"

lemma DEF_is_nadd: "is_nadd =
(%u. EX B. ALL m n. hollight.dist (m * u n, n * u m) <= B * (m + n))"
  by (import hollight DEF_is_nadd)

lemma is_nadd_0: "is_nadd (%n. 0)"
  by (import hollight is_nadd_0)

typedef (open) nadd = "Collect is_nadd"  morphisms "dest_nadd" "mk_nadd"
  apply (rule light_ex_imp_nonempty[where t="%n. NUMERAL 0"])
  by (import hollight TYDEF_nadd)

syntax
  dest_nadd :: _ 

syntax
  mk_nadd :: _ 

lemmas "TYDEF_nadd_@intern" = typedef_hol2hollight 
  [where a="a :: nadd" and r=r ,
   OF type_definition_nadd]

lemma NADD_CAUCHY: "EX xa.
   ALL xb xc.
      hollight.dist (xb * dest_nadd x xc, xc * dest_nadd x xb)
      <= xa * (xb + xc)"
  by (import hollight NADD_CAUCHY)

lemma NADD_BOUND: "EX xa B. ALL n. dest_nadd x n <= xa * n + B"
  by (import hollight NADD_BOUND)

lemma NADD_MULTIPLICATIVE: "EX xa.
   ALL m n.
      hollight.dist (dest_nadd x (m * n), m * dest_nadd x n) <= xa * m + xa"
  by (import hollight NADD_MULTIPLICATIVE)

lemma NADD_ADDITIVE: "EX xa.
   ALL m n.
      hollight.dist (dest_nadd x (m + n), dest_nadd x m + dest_nadd x n)
      <= xa"
  by (import hollight NADD_ADDITIVE)

lemma NADD_SUC: "EX xa. ALL n. hollight.dist (dest_nadd x (Suc n), dest_nadd x n) <= xa"
  by (import hollight NADD_SUC)

lemma NADD_DIST_LEMMA: "EX xa. ALL m n. hollight.dist (dest_nadd x (m + n), dest_nadd x m) <= xa * n"
  by (import hollight NADD_DIST_LEMMA)

lemma NADD_DIST: "EX xa.
   ALL m n.
      hollight.dist (dest_nadd x m, dest_nadd x n)
      <= xa * hollight.dist (m, n)"
  by (import hollight NADD_DIST)

lemma NADD_ALTMUL: "EX A B.
   ALL n.
      hollight.dist
       (n * dest_nadd x (dest_nadd y n), dest_nadd x n * dest_nadd y n)
      <= A * n + B"
  by (import hollight NADD_ALTMUL)

definition
  nadd_eq :: "nadd => nadd => bool"  where
  "nadd_eq ==
%u ua. EX B. ALL n. hollight.dist (dest_nadd u n, dest_nadd ua n) <= B"

lemma DEF_nadd_eq: "nadd_eq =
(%u ua. EX B. ALL n. hollight.dist (dest_nadd u n, dest_nadd ua n) <= B)"
  by (import hollight DEF_nadd_eq)

lemma NADD_EQ_REFL: "nadd_eq x x"
  by (import hollight NADD_EQ_REFL)

lemma NADD_EQ_SYM: "nadd_eq x y = nadd_eq y x"
  by (import hollight NADD_EQ_SYM)

lemma NADD_EQ_TRANS: "nadd_eq x y & nadd_eq y z ==> nadd_eq x z"
  by (import hollight NADD_EQ_TRANS)

definition
  nadd_of_num :: "nat => nadd"  where
  "nadd_of_num == %u. mk_nadd (op * u)"

lemma DEF_nadd_of_num: "nadd_of_num = (%u. mk_nadd (op * u))"
  by (import hollight DEF_nadd_of_num)

lemma NADD_OF_NUM: "dest_nadd (nadd_of_num x) = op * x"
  by (import hollight NADD_OF_NUM)

lemma NADD_OF_NUM_WELLDEF: "m = n ==> nadd_eq (nadd_of_num m) (nadd_of_num n)"
  by (import hollight NADD_OF_NUM_WELLDEF)

lemma NADD_OF_NUM_EQ: "nadd_eq (nadd_of_num m) (nadd_of_num n) = (m = n)"
  by (import hollight NADD_OF_NUM_EQ)

definition
  nadd_le :: "nadd => nadd => bool"  where
  "nadd_le == %u ua. EX B. ALL n. dest_nadd u n <= dest_nadd ua n + B"

lemma DEF_nadd_le: "nadd_le = (%u ua. EX B. ALL n. dest_nadd u n <= dest_nadd ua n + B)"
  by (import hollight DEF_nadd_le)

lemma NADD_LE_WELLDEF_LEMMA: "nadd_eq x x' & nadd_eq y y' & nadd_le x y ==> nadd_le x' y'"
  by (import hollight NADD_LE_WELLDEF_LEMMA)

lemma NADD_LE_WELLDEF: "nadd_eq x x' & nadd_eq y y' ==> nadd_le x y = nadd_le x' y'"
  by (import hollight NADD_LE_WELLDEF)

lemma NADD_LE_REFL: "nadd_le x x"
  by (import hollight NADD_LE_REFL)

lemma NADD_LE_TRANS: "nadd_le x y & nadd_le y z ==> nadd_le x z"
  by (import hollight NADD_LE_TRANS)

lemma NADD_LE_ANTISYM: "(nadd_le x y & nadd_le y x) = nadd_eq x y"
  by (import hollight NADD_LE_ANTISYM)

lemma NADD_LE_TOTAL_LEMMA: "~ nadd_le x y ==> EX n. n ~= 0 & dest_nadd y n + B < dest_nadd x n"
  by (import hollight NADD_LE_TOTAL_LEMMA)

lemma NADD_LE_TOTAL: "nadd_le x y | nadd_le y x"
  by (import hollight NADD_LE_TOTAL)

lemma NADD_ARCH: "EX xa. nadd_le x (nadd_of_num xa)"
  by (import hollight NADD_ARCH)

lemma NADD_OF_NUM_LE: "nadd_le (nadd_of_num m) (nadd_of_num n) = (m <= n)"
  by (import hollight NADD_OF_NUM_LE)

definition
  nadd_add :: "nadd => nadd => nadd"  where
  "nadd_add == %u ua. mk_nadd (%n. dest_nadd u n + dest_nadd ua n)"

lemma DEF_nadd_add: "nadd_add = (%u ua. mk_nadd (%n. dest_nadd u n + dest_nadd ua n))"
  by (import hollight DEF_nadd_add)

lemma NADD_ADD: "dest_nadd (nadd_add x y) = (%n. dest_nadd x n + dest_nadd y n)"
  by (import hollight NADD_ADD)

lemma NADD_ADD_WELLDEF: "nadd_eq x x' & nadd_eq y y' ==> nadd_eq (nadd_add x y) (nadd_add x' y')"
  by (import hollight NADD_ADD_WELLDEF)

lemma NADD_ADD_SYM: "nadd_eq (nadd_add x y) (nadd_add y x)"
  by (import hollight NADD_ADD_SYM)

lemma NADD_ADD_ASSOC: "nadd_eq (nadd_add x (nadd_add y z)) (nadd_add (nadd_add x y) z)"
  by (import hollight NADD_ADD_ASSOC)

lemma NADD_ADD_LID: "nadd_eq (nadd_add (nadd_of_num 0) x) x"
  by (import hollight NADD_ADD_LID)

lemma NADD_ADD_LCANCEL: "nadd_eq (nadd_add x y) (nadd_add x z) ==> nadd_eq y z"
  by (import hollight NADD_ADD_LCANCEL)

lemma NADD_LE_ADD: "nadd_le x (nadd_add x y)"
  by (import hollight NADD_LE_ADD)

lemma NADD_LE_EXISTS: "nadd_le x y ==> EX d. nadd_eq y (nadd_add x d)"
  by (import hollight NADD_LE_EXISTS)

lemma NADD_OF_NUM_ADD: "nadd_eq (nadd_add (nadd_of_num x) (nadd_of_num xa)) (nadd_of_num (x + xa))"
  by (import hollight NADD_OF_NUM_ADD)

definition
  nadd_mul :: "nadd => nadd => nadd"  where
  "nadd_mul == %u ua. mk_nadd (%n. dest_nadd u (dest_nadd ua n))"

lemma DEF_nadd_mul: "nadd_mul = (%u ua. mk_nadd (%n. dest_nadd u (dest_nadd ua n)))"
  by (import hollight DEF_nadd_mul)

lemma NADD_MUL: "dest_nadd (nadd_mul x y) = (%n. dest_nadd x (dest_nadd y n))"
  by (import hollight NADD_MUL)

lemma NADD_MUL_SYM: "nadd_eq (nadd_mul x y) (nadd_mul y x)"
  by (import hollight NADD_MUL_SYM)

lemma NADD_MUL_ASSOC: "nadd_eq (nadd_mul x (nadd_mul y z)) (nadd_mul (nadd_mul x y) z)"
  by (import hollight NADD_MUL_ASSOC)

lemma NADD_MUL_LID: "nadd_eq (nadd_mul (nadd_of_num 1) x) x"
  by (import hollight NADD_MUL_LID)

lemma NADD_LDISTRIB: "nadd_eq (nadd_mul x (nadd_add y z)) (nadd_add (nadd_mul x y) (nadd_mul x z))"
  by (import hollight NADD_LDISTRIB)

lemma NADD_MUL_WELLDEF_LEMMA: "nadd_eq y y' ==> nadd_eq (nadd_mul x y) (nadd_mul x y')"
  by (import hollight NADD_MUL_WELLDEF_LEMMA)

lemma NADD_MUL_WELLDEF: "nadd_eq x x' & nadd_eq y y' ==> nadd_eq (nadd_mul x y) (nadd_mul x' y')"
  by (import hollight NADD_MUL_WELLDEF)

lemma NADD_OF_NUM_MUL: "nadd_eq (nadd_mul (nadd_of_num x) (nadd_of_num xa)) (nadd_of_num (x * xa))"
  by (import hollight NADD_OF_NUM_MUL)

lemma NADD_LE_0: "nadd_le (nadd_of_num 0) x"
  by (import hollight NADD_LE_0)

lemma NADD_EQ_IMP_LE: "nadd_eq x y ==> nadd_le x y"
  by (import hollight NADD_EQ_IMP_LE)

lemma NADD_LE_LMUL: "nadd_le y z ==> nadd_le (nadd_mul x y) (nadd_mul x z)"
  by (import hollight NADD_LE_LMUL)

lemma NADD_LE_RMUL: "nadd_le x y ==> nadd_le (nadd_mul x z) (nadd_mul y z)"
  by (import hollight NADD_LE_RMUL)

lemma NADD_LE_RADD: "nadd_le (nadd_add x z) (nadd_add y z) = nadd_le x y"
  by (import hollight NADD_LE_RADD)

lemma NADD_LE_LADD: "nadd_le (nadd_add x y) (nadd_add x z) = nadd_le y z"
  by (import hollight NADD_LE_LADD)

lemma NADD_RDISTRIB: "nadd_eq (nadd_mul (nadd_add x y) z) (nadd_add (nadd_mul x z) (nadd_mul y z))"
  by (import hollight NADD_RDISTRIB)

lemma NADD_ARCH_MULT: "~ nadd_eq x (nadd_of_num 0)
==> EX xa. nadd_le (nadd_of_num k) (nadd_mul (nadd_of_num xa) x)"
  by (import hollight NADD_ARCH_MULT)

lemma NADD_ARCH_ZERO: "(!!n. nadd_le (nadd_mul (nadd_of_num n) x) k) ==> nadd_eq x (nadd_of_num 0)"
  by (import hollight NADD_ARCH_ZERO)

lemma NADD_ARCH_LEMMA: "(!!n. nadd_le (nadd_mul (nadd_of_num n) x)
       (nadd_add (nadd_mul (nadd_of_num n) y) z))
==> nadd_le x y"
  by (import hollight NADD_ARCH_LEMMA)

lemma NADD_COMPLETE: "Ex P & (EX M. ALL x. P x --> nadd_le x M)
==> EX M. (ALL x. P x --> nadd_le x M) &
          (ALL M'. (ALL x. P x --> nadd_le x M') --> nadd_le M M')"
  by (import hollight NADD_COMPLETE)

lemma NADD_UBOUND: "EX xa N. ALL n>=N. dest_nadd x n <= xa * n"
  by (import hollight NADD_UBOUND)

lemma NADD_NONZERO: "~ nadd_eq x (nadd_of_num 0) ==> EX N. ALL n>=N. dest_nadd x n ~= 0"
  by (import hollight NADD_NONZERO)

lemma NADD_LBOUND: "~ nadd_eq x (nadd_of_num 0) ==> EX A N. ALL n>=N. n <= A * dest_nadd x n"
  by (import hollight NADD_LBOUND)

definition
  nadd_rinv :: "nadd => nat => nat"  where
  "nadd_rinv == %u n. n * n div dest_nadd u n"

lemma DEF_nadd_rinv: "nadd_rinv = (%u n. n * n div dest_nadd u n)"
  by (import hollight DEF_nadd_rinv)

lemma NADD_MUL_LINV_LEMMA0: "~ nadd_eq x (nadd_of_num 0) ==> EX xa B. ALL i. nadd_rinv x i <= xa * i + B"
  by (import hollight NADD_MUL_LINV_LEMMA0)

lemma NADD_MUL_LINV_LEMMA1: "dest_nadd x n ~= 0
==> hollight.dist (dest_nadd x n * nadd_rinv x n, n * n) <= dest_nadd x n"
  by (import hollight NADD_MUL_LINV_LEMMA1)

lemma NADD_MUL_LINV_LEMMA2: "~ nadd_eq x (nadd_of_num 0)
==> EX N. ALL n>=N.
             hollight.dist (dest_nadd x n * nadd_rinv x n, n * n)
             <= dest_nadd x n"
  by (import hollight NADD_MUL_LINV_LEMMA2)

lemma NADD_MUL_LINV_LEMMA3: "~ nadd_eq x (nadd_of_num 0)
==> EX N. ALL m n.
             N <= n -->
             hollight.dist
              (m * (dest_nadd x m * (dest_nadd x n * nadd_rinv x n)),
               m * (dest_nadd x m * (n * n)))
             <= m * (dest_nadd x m * dest_nadd x n)"
  by (import hollight NADD_MUL_LINV_LEMMA3)

lemma NADD_MUL_LINV_LEMMA4: "~ nadd_eq x (nadd_of_num 0)
==> EX N. ALL m n.
             N <= m & N <= n -->
             dest_nadd x m * dest_nadd x n *
             hollight.dist (m * nadd_rinv x n, n * nadd_rinv x m)
             <= m * n *
                hollight.dist (m * dest_nadd x n, n * dest_nadd x m) +
                dest_nadd x m * dest_nadd x n * (m + n)"
  by (import hollight NADD_MUL_LINV_LEMMA4)

lemma NADD_MUL_LINV_LEMMA5: "~ nadd_eq x (nadd_of_num 0)
==> EX B N.
       ALL m n.
          N <= m & N <= n -->
          dest_nadd x m * dest_nadd x n *
          hollight.dist (m * nadd_rinv x n, n * nadd_rinv x m)
          <= B * (m * n * (m + n))"
  by (import hollight NADD_MUL_LINV_LEMMA5)

lemma NADD_MUL_LINV_LEMMA6: "~ nadd_eq x (nadd_of_num 0)
==> EX B N.
       ALL m n.
          N <= m & N <= n -->
          m * n * hollight.dist (m * nadd_rinv x n, n * nadd_rinv x m)
          <= B * (m * n * (m + n))"
  by (import hollight NADD_MUL_LINV_LEMMA6)

lemma NADD_MUL_LINV_LEMMA7: "~ nadd_eq x (nadd_of_num 0)
==> EX B N.
       ALL m n.
          N <= m & N <= n -->
          hollight.dist (m * nadd_rinv x n, n * nadd_rinv x m)
          <= B * (m + n)"
  by (import hollight NADD_MUL_LINV_LEMMA7)

lemma NADD_MUL_LINV_LEMMA7a: "~ nadd_eq x (nadd_of_num 0)
==> EX A B.
       ALL m n.
          m <= N -->
          hollight.dist (m * nadd_rinv x n, n * nadd_rinv x m) <= A * n + B"
  by (import hollight NADD_MUL_LINV_LEMMA7a)

lemma NADD_MUL_LINV_LEMMA8: "~ nadd_eq x (nadd_of_num 0)
==> EX B. ALL m n.
             hollight.dist (m * nadd_rinv x n, n * nadd_rinv x m)
             <= B * (m + n)"
  by (import hollight NADD_MUL_LINV_LEMMA8)

definition
  nadd_inv :: "nadd => nadd"  where
  "nadd_inv ==
%u. if nadd_eq u (nadd_of_num 0) then nadd_of_num 0
    else mk_nadd (nadd_rinv u)"

lemma DEF_nadd_inv: "nadd_inv =
(%u. if nadd_eq u (nadd_of_num 0) then nadd_of_num 0
     else mk_nadd (nadd_rinv u))"
  by (import hollight DEF_nadd_inv)

lemma NADD_INV: "dest_nadd (nadd_inv x) =
(if nadd_eq x (nadd_of_num 0) then %n. 0 else nadd_rinv x)"
  by (import hollight NADD_INV)

lemma NADD_MUL_LINV: "~ nadd_eq x (nadd_of_num 0)
==> nadd_eq (nadd_mul (nadd_inv x) x) (nadd_of_num 1)"
  by (import hollight NADD_MUL_LINV)

lemma NADD_INV_0: "nadd_eq (nadd_inv (nadd_of_num 0)) (nadd_of_num 0)"
  by (import hollight NADD_INV_0)

lemma NADD_INV_WELLDEF: "nadd_eq x y ==> nadd_eq (nadd_inv x) (nadd_inv y)"
  by (import hollight NADD_INV_WELLDEF)

typedef (open) hreal = "{s. EX x. s = nadd_eq x}"  morphisms "dest_hreal" "mk_hreal"
  apply (rule light_ex_imp_nonempty[where t="nadd_eq x"])
  by (import hollight TYDEF_hreal)

syntax
  dest_hreal :: _ 

syntax
  mk_hreal :: _ 

lemmas "TYDEF_hreal_@intern" = typedef_hol2hollight 
  [where a="a :: hreal" and r=r ,
   OF type_definition_hreal]

definition
  hreal_of_num :: "nat => hreal"  where
  "hreal_of_num == %m. mk_hreal (nadd_eq (nadd_of_num m))"

lemma DEF_hreal_of_num: "hreal_of_num = (%m. mk_hreal (nadd_eq (nadd_of_num m)))"
  by (import hollight DEF_hreal_of_num)

definition
  hreal_add :: "hreal => hreal => hreal"  where
  "hreal_add ==
%x y. mk_hreal
       (%u. EX xa ya.
               nadd_eq (nadd_add xa ya) u &
               dest_hreal x xa & dest_hreal y ya)"

lemma DEF_hreal_add: "hreal_add =
(%x y. mk_hreal
        (%u. EX xa ya.
                nadd_eq (nadd_add xa ya) u &
                dest_hreal x xa & dest_hreal y ya))"
  by (import hollight DEF_hreal_add)

definition
  hreal_mul :: "hreal => hreal => hreal"  where
  "hreal_mul ==
%x y. mk_hreal
       (%u. EX xa ya.
               nadd_eq (nadd_mul xa ya) u &
               dest_hreal x xa & dest_hreal y ya)"

lemma DEF_hreal_mul: "hreal_mul =
(%x y. mk_hreal
        (%u. EX xa ya.
                nadd_eq (nadd_mul xa ya) u &
                dest_hreal x xa & dest_hreal y ya))"
  by (import hollight DEF_hreal_mul)

definition
  hreal_le :: "hreal => hreal => bool"  where
  "hreal_le ==
%x y. SOME u.
         EX xa ya. nadd_le xa ya = u & dest_hreal x xa & dest_hreal y ya"

lemma DEF_hreal_le: "hreal_le =
(%x y. SOME u.
          EX xa ya. nadd_le xa ya = u & dest_hreal x xa & dest_hreal y ya)"
  by (import hollight DEF_hreal_le)

definition
  hreal_inv :: "hreal => hreal"  where
  "hreal_inv ==
%x. mk_hreal (%u. EX xa. nadd_eq (nadd_inv xa) u & dest_hreal x xa)"

lemma DEF_hreal_inv: "hreal_inv =
(%x. mk_hreal (%u. EX xa. nadd_eq (nadd_inv xa) u & dest_hreal x xa))"
  by (import hollight DEF_hreal_inv)

lemma HREAL_LE_EXISTS_DEF: "hreal_le m n = (EX d. n = hreal_add m d)"
  by (import hollight HREAL_LE_EXISTS_DEF)

lemma HREAL_EQ_ADD_LCANCEL: "(hreal_add m n = hreal_add m p) = (n = p)"
  by (import hollight HREAL_EQ_ADD_LCANCEL)

lemma HREAL_EQ_ADD_RCANCEL: "(hreal_add x xb = hreal_add xa xb) = (x = xa)"
  by (import hollight HREAL_EQ_ADD_RCANCEL)

lemma HREAL_LE_ADD_LCANCEL: "hreal_le (hreal_add x xa) (hreal_add x xb) = hreal_le xa xb"
  by (import hollight HREAL_LE_ADD_LCANCEL)

lemma HREAL_LE_ADD_RCANCEL: "hreal_le (hreal_add x xb) (hreal_add xa xb) = hreal_le x xa"
  by (import hollight HREAL_LE_ADD_RCANCEL)

lemma HREAL_ADD_RID: "hreal_add x (hreal_of_num 0) = x"
  by (import hollight HREAL_ADD_RID)

lemma HREAL_ADD_RDISTRIB: "hreal_mul (hreal_add x xa) xb = hreal_add (hreal_mul x xb) (hreal_mul xa xb)"
  by (import hollight HREAL_ADD_RDISTRIB)

lemma HREAL_MUL_LZERO: "hreal_mul (hreal_of_num 0) m = hreal_of_num 0"
  by (import hollight HREAL_MUL_LZERO)

lemma HREAL_MUL_RZERO: "hreal_mul x (hreal_of_num 0) = hreal_of_num 0"
  by (import hollight HREAL_MUL_RZERO)

lemma HREAL_ADD_AC: "hreal_add m n = hreal_add n m &
hreal_add (hreal_add m n) p = hreal_add m (hreal_add n p) &
hreal_add m (hreal_add n p) = hreal_add n (hreal_add m p)"
  by (import hollight HREAL_ADD_AC)

lemma HREAL_LE_ADD2: "hreal_le a b & hreal_le c d ==> hreal_le (hreal_add a c) (hreal_add b d)"
  by (import hollight HREAL_LE_ADD2)

lemma HREAL_LE_MUL_RCANCEL_IMP: "hreal_le a b ==> hreal_le (hreal_mul a c) (hreal_mul b c)"
  by (import hollight HREAL_LE_MUL_RCANCEL_IMP)

definition
  treal_of_num :: "nat => hreal * hreal"  where
  "treal_of_num == %u. (hreal_of_num u, hreal_of_num 0)"

lemma DEF_treal_of_num: "treal_of_num = (%u. (hreal_of_num u, hreal_of_num 0))"
  by (import hollight DEF_treal_of_num)

definition
  treal_neg :: "hreal * hreal => hreal * hreal"  where
  "treal_neg == %u. (snd u, fst u)"

lemma DEF_treal_neg: "treal_neg = (%u. (snd u, fst u))"
  by (import hollight DEF_treal_neg)

definition
  treal_add :: "hreal * hreal => hreal * hreal => hreal * hreal"  where
  "treal_add == %u ua. (hreal_add (fst u) (fst ua), hreal_add (snd u) (snd ua))"

lemma DEF_treal_add: "treal_add =
(%u ua. (hreal_add (fst u) (fst ua), hreal_add (snd u) (snd ua)))"
  by (import hollight DEF_treal_add)

definition
  treal_mul :: "hreal * hreal => hreal * hreal => hreal * hreal"  where
  "treal_mul ==
%u ua.
   (hreal_add (hreal_mul (fst u) (fst ua)) (hreal_mul (snd u) (snd ua)),
    hreal_add (hreal_mul (fst u) (snd ua)) (hreal_mul (snd u) (fst ua)))"

lemma DEF_treal_mul: "treal_mul =
(%u ua.
    (hreal_add (hreal_mul (fst u) (fst ua)) (hreal_mul (snd u) (snd ua)),
     hreal_add (hreal_mul (fst u) (snd ua)) (hreal_mul (snd u) (fst ua))))"
  by (import hollight DEF_treal_mul)

definition
  treal_le :: "hreal * hreal => hreal * hreal => bool"  where
  "treal_le ==
%u ua. hreal_le (hreal_add (fst u) (snd ua)) (hreal_add (fst ua) (snd u))"

lemma DEF_treal_le: "treal_le =
(%u ua. hreal_le (hreal_add (fst u) (snd ua)) (hreal_add (fst ua) (snd u)))"
  by (import hollight DEF_treal_le)

definition
  treal_inv :: "hreal * hreal => hreal * hreal"  where
  "treal_inv ==
%u. if fst u = snd u then (hreal_of_num 0, hreal_of_num 0)
    else if hreal_le (snd u) (fst u)
         then (hreal_inv (SOME d. fst u = hreal_add (snd u) d),
               hreal_of_num 0)
         else (hreal_of_num 0,
               hreal_inv (SOME d. snd u = hreal_add (fst u) d))"

lemma DEF_treal_inv: "treal_inv =
(%u. if fst u = snd u then (hreal_of_num 0, hreal_of_num 0)
     else if hreal_le (snd u) (fst u)
          then (hreal_inv (SOME d. fst u = hreal_add (snd u) d),
                hreal_of_num 0)
          else (hreal_of_num 0,
                hreal_inv (SOME d. snd u = hreal_add (fst u) d)))"
  by (import hollight DEF_treal_inv)

definition
  treal_eq :: "hreal * hreal => hreal * hreal => bool"  where
  "treal_eq == %u ua. hreal_add (fst u) (snd ua) = hreal_add (fst ua) (snd u)"

lemma DEF_treal_eq: "treal_eq = (%u ua. hreal_add (fst u) (snd ua) = hreal_add (fst ua) (snd u))"
  by (import hollight DEF_treal_eq)

lemma TREAL_EQ_REFL: "treal_eq x x"
  by (import hollight TREAL_EQ_REFL)

lemma TREAL_EQ_SYM: "treal_eq x y = treal_eq y x"
  by (import hollight TREAL_EQ_SYM)

lemma TREAL_EQ_TRANS: "treal_eq x y & treal_eq y z ==> treal_eq x z"
  by (import hollight TREAL_EQ_TRANS)

lemma TREAL_EQ_AP: "x = xa ==> treal_eq x xa"
  by (import hollight TREAL_EQ_AP)

lemma TREAL_OF_NUM_EQ: "treal_eq (treal_of_num x) (treal_of_num xa) = (x = xa)"
  by (import hollight TREAL_OF_NUM_EQ)

lemma TREAL_OF_NUM_LE: "treal_le (treal_of_num x) (treal_of_num xa) = (x <= xa)"
  by (import hollight TREAL_OF_NUM_LE)

lemma TREAL_OF_NUM_ADD: "treal_eq (treal_add (treal_of_num x) (treal_of_num xa))
 (treal_of_num (x + xa))"
  by (import hollight TREAL_OF_NUM_ADD)

lemma TREAL_OF_NUM_MUL: "treal_eq (treal_mul (treal_of_num x) (treal_of_num xa))
 (treal_of_num (x * xa))"
  by (import hollight TREAL_OF_NUM_MUL)

lemma TREAL_ADD_SYM_EQ: "treal_add x y = treal_add y x"
  by (import hollight TREAL_ADD_SYM_EQ)

lemma TREAL_MUL_SYM_EQ: "treal_mul x y = treal_mul y x"
  by (import hollight TREAL_MUL_SYM_EQ)

lemma TREAL_ADD_SYM: "treal_eq (treal_add x y) (treal_add y x)"
  by (import hollight TREAL_ADD_SYM)

lemma TREAL_ADD_ASSOC: "treal_eq (treal_add x (treal_add y z)) (treal_add (treal_add x y) z)"
  by (import hollight TREAL_ADD_ASSOC)

lemma TREAL_ADD_LID: "treal_eq (treal_add (treal_of_num 0) x) x"
  by (import hollight TREAL_ADD_LID)

lemma TREAL_ADD_LINV: "treal_eq (treal_add (treal_neg x) x) (treal_of_num 0)"
  by (import hollight TREAL_ADD_LINV)

lemma TREAL_MUL_SYM: "treal_eq (treal_mul x xa) (treal_mul xa x)"
  by (import hollight TREAL_MUL_SYM)

lemma TREAL_MUL_ASSOC: "treal_eq (treal_mul x (treal_mul y z)) (treal_mul (treal_mul x y) z)"
  by (import hollight TREAL_MUL_ASSOC)

lemma TREAL_MUL_LID: "treal_eq (treal_mul (treal_of_num 1) x) x"
  by (import hollight TREAL_MUL_LID)

lemma TREAL_ADD_LDISTRIB: "treal_eq (treal_mul x (treal_add y z))
 (treal_add (treal_mul x y) (treal_mul x z))"
  by (import hollight TREAL_ADD_LDISTRIB)

lemma TREAL_LE_REFL: "treal_le x x"
  by (import hollight TREAL_LE_REFL)

lemma TREAL_LE_ANTISYM: "(treal_le x y & treal_le y x) = treal_eq x y"
  by (import hollight TREAL_LE_ANTISYM)

lemma TREAL_LE_TRANS: "treal_le x y & treal_le y z ==> treal_le x z"
  by (import hollight TREAL_LE_TRANS)

lemma TREAL_LE_TOTAL: "treal_le x y | treal_le y x"
  by (import hollight TREAL_LE_TOTAL)

lemma TREAL_LE_LADD_IMP: "treal_le y z ==> treal_le (treal_add x y) (treal_add x z)"
  by (import hollight TREAL_LE_LADD_IMP)

lemma TREAL_LE_MUL: "treal_le (treal_of_num 0) x & treal_le (treal_of_num 0) y
==> treal_le (treal_of_num 0) (treal_mul x y)"
  by (import hollight TREAL_LE_MUL)

lemma TREAL_INV_0: "treal_eq (treal_inv (treal_of_num 0)) (treal_of_num 0)"
  by (import hollight TREAL_INV_0)

lemma TREAL_MUL_LINV: "~ treal_eq x (treal_of_num 0)
==> treal_eq (treal_mul (treal_inv x) x) (treal_of_num 1)"
  by (import hollight TREAL_MUL_LINV)

lemma TREAL_OF_NUM_WELLDEF: "m = n ==> treal_eq (treal_of_num m) (treal_of_num n)"
  by (import hollight TREAL_OF_NUM_WELLDEF)

lemma TREAL_NEG_WELLDEF: "treal_eq x1 x2 ==> treal_eq (treal_neg x1) (treal_neg x2)"
  by (import hollight TREAL_NEG_WELLDEF)

lemma TREAL_ADD_WELLDEFR: "treal_eq x1 x2 ==> treal_eq (treal_add x1 y) (treal_add x2 y)"
  by (import hollight TREAL_ADD_WELLDEFR)

lemma TREAL_ADD_WELLDEF: "treal_eq x1 x2 & treal_eq y1 y2
==> treal_eq (treal_add x1 y1) (treal_add x2 y2)"
  by (import hollight TREAL_ADD_WELLDEF)

lemma TREAL_MUL_WELLDEFR: "treal_eq x1 x2 ==> treal_eq (treal_mul x1 y) (treal_mul x2 y)"
  by (import hollight TREAL_MUL_WELLDEFR)

lemma TREAL_MUL_WELLDEF: "treal_eq x1 x2 & treal_eq y1 y2
==> treal_eq (treal_mul x1 y1) (treal_mul x2 y2)"
  by (import hollight TREAL_MUL_WELLDEF)

lemma TREAL_EQ_IMP_LE: "treal_eq x y ==> treal_le x y"
  by (import hollight TREAL_EQ_IMP_LE)

lemma TREAL_LE_WELLDEF: "treal_eq x1 x2 & treal_eq y1 y2 ==> treal_le x1 y1 = treal_le x2 y2"
  by (import hollight TREAL_LE_WELLDEF)

lemma TREAL_INV_WELLDEF: "treal_eq x y ==> treal_eq (treal_inv x) (treal_inv y)"
  by (import hollight TREAL_INV_WELLDEF)

typedef (open) real = "{s. EX x. s = treal_eq x}"  morphisms "dest_real" "mk_real"
  apply (rule light_ex_imp_nonempty[where t="treal_eq x"])
  by (import hollight TYDEF_real)

syntax
  dest_real :: _ 

syntax
  mk_real :: _ 

lemmas "TYDEF_real_@intern" = typedef_hol2hollight 
  [where a="a :: hollight.real" and r=r ,
   OF type_definition_real]

definition
  real_of_num :: "nat => hollight.real"  where
  "real_of_num == %m. mk_real (treal_eq (treal_of_num m))"

lemma DEF_real_of_num: "real_of_num = (%m. mk_real (treal_eq (treal_of_num m)))"
  by (import hollight DEF_real_of_num)

definition
  real_neg :: "hollight.real => hollight.real"  where
  "real_neg ==
%x1. mk_real (%u. EX x1a. treal_eq (treal_neg x1a) u & dest_real x1 x1a)"

lemma DEF_real_neg: "real_neg =
(%x1. mk_real (%u. EX x1a. treal_eq (treal_neg x1a) u & dest_real x1 x1a))"
  by (import hollight DEF_real_neg)

definition
  real_add :: "hollight.real => hollight.real => hollight.real"  where
  "real_add ==
%x1 y1.
   mk_real
    (%u. EX x1a y1a.
            treal_eq (treal_add x1a y1a) u &
            dest_real x1 x1a & dest_real y1 y1a)"

lemma DEF_real_add: "real_add =
(%x1 y1.
    mk_real
     (%u. EX x1a y1a.
             treal_eq (treal_add x1a y1a) u &
             dest_real x1 x1a & dest_real y1 y1a))"
  by (import hollight DEF_real_add)

definition
  real_mul :: "hollight.real => hollight.real => hollight.real"  where
  "real_mul ==
%x1 y1.
   mk_real
    (%u. EX x1a y1a.
            treal_eq (treal_mul x1a y1a) u &
            dest_real x1 x1a & dest_real y1 y1a)"

lemma DEF_real_mul: "real_mul =
(%x1 y1.
    mk_real
     (%u. EX x1a y1a.
             treal_eq (treal_mul x1a y1a) u &
             dest_real x1 x1a & dest_real y1 y1a))"
  by (import hollight DEF_real_mul)

definition
  real_le :: "hollight.real => hollight.real => bool"  where
  "real_le ==
%x1 y1.
   SOME u.
      EX x1a y1a. treal_le x1a y1a = u & dest_real x1 x1a & dest_real y1 y1a"

lemma DEF_real_le: "real_le =
(%x1 y1.
    SOME u.
       EX x1a y1a.
          treal_le x1a y1a = u & dest_real x1 x1a & dest_real y1 y1a)"
  by (import hollight DEF_real_le)

definition
  real_inv :: "hollight.real => hollight.real"  where
  "real_inv ==
%x. mk_real (%u. EX xa. treal_eq (treal_inv xa) u & dest_real x xa)"

lemma DEF_real_inv: "real_inv =
(%x. mk_real (%u. EX xa. treal_eq (treal_inv xa) u & dest_real x xa))"
  by (import hollight DEF_real_inv)

definition
  real_sub :: "hollight.real => hollight.real => hollight.real"  where
  "real_sub == %u ua. real_add u (real_neg ua)"

lemma DEF_real_sub: "real_sub = (%u ua. real_add u (real_neg ua))"
  by (import hollight DEF_real_sub)

definition
  real_lt :: "hollight.real => hollight.real => bool"  where
  "real_lt == %u ua. ~ real_le ua u"

lemma DEF_real_lt: "real_lt = (%u ua. ~ real_le ua u)"
  by (import hollight DEF_real_lt)

definition
  real_ge :: "hollight.real => hollight.real => bool"  where
  "real_ge == %u ua. real_le ua u"

lemma DEF_real_ge: "real_ge = (%u ua. real_le ua u)"
  by (import hollight DEF_real_ge)

definition
  real_gt :: "hollight.real => hollight.real => bool"  where
  "real_gt == %u ua. real_lt ua u"

lemma DEF_real_gt: "real_gt = (%u ua. real_lt ua u)"
  by (import hollight DEF_real_gt)

definition
  real_abs :: "hollight.real => hollight.real"  where
  "real_abs == %u. if real_le (real_of_num 0) u then u else real_neg u"

lemma DEF_real_abs: "real_abs = (%u. if real_le (real_of_num 0) u then u else real_neg u)"
  by (import hollight DEF_real_abs)

definition
  real_pow :: "hollight.real => nat => hollight.real"  where
  "real_pow ==
SOME real_pow.
   (ALL x. real_pow x 0 = real_of_num 1) &
   (ALL x n. real_pow x (Suc n) = real_mul x (real_pow x n))"

lemma DEF_real_pow: "real_pow =
(SOME real_pow.
    (ALL x. real_pow x 0 = real_of_num 1) &
    (ALL x n. real_pow x (Suc n) = real_mul x (real_pow x n)))"
  by (import hollight DEF_real_pow)

definition
  real_div :: "hollight.real => hollight.real => hollight.real"  where
  "real_div == %u ua. real_mul u (real_inv ua)"

lemma DEF_real_div: "real_div = (%u ua. real_mul u (real_inv ua))"
  by (import hollight DEF_real_div)

definition
  real_max :: "hollight.real => hollight.real => hollight.real"  where
  "real_max == %u ua. if real_le u ua then ua else u"

lemma DEF_real_max: "real_max = (%u ua. if real_le u ua then ua else u)"
  by (import hollight DEF_real_max)

definition
  real_min :: "hollight.real => hollight.real => hollight.real"  where
  "real_min == %u ua. if real_le u ua then u else ua"

lemma DEF_real_min: "real_min = (%u ua. if real_le u ua then u else ua)"
  by (import hollight DEF_real_min)

lemma REAL_HREAL_LEMMA1: "EX x. (ALL xa. real_le (real_of_num 0) xa = (EX y. xa = x y)) &
      (ALL y z. hreal_le y z = real_le (x y) (x z))"
  by (import hollight REAL_HREAL_LEMMA1)

lemma REAL_HREAL_LEMMA2: "EX x r.
   (ALL xa. x (r xa) = xa) &
   (ALL xa. real_le (real_of_num 0) xa --> r (x xa) = xa) &
   (ALL x. real_le (real_of_num 0) (r x)) &
   (ALL x y. hreal_le x y = real_le (r x) (r y))"
  by (import hollight REAL_HREAL_LEMMA2)

lemma REAL_COMPLETE_SOMEPOS: "(EX x. P x & real_le (real_of_num 0) x) & (EX M. ALL x. P x --> real_le x M)
==> EX M. (ALL x. P x --> real_le x M) &
          (ALL M'. (ALL x. P x --> real_le x M') --> real_le M M')"
  by (import hollight REAL_COMPLETE_SOMEPOS)

lemma REAL_COMPLETE: "Ex P & (EX M. ALL x. P x --> real_le x M)
==> EX M. (ALL x. P x --> real_le x M) &
          (ALL M'. (ALL x. P x --> real_le x M') --> real_le M M')"
  by (import hollight REAL_COMPLETE)

lemma REAL_ADD_AC: "real_add m n = real_add n m &
real_add (real_add m n) p = real_add m (real_add n p) &
real_add m (real_add n p) = real_add n (real_add m p)"
  by (import hollight REAL_ADD_AC)

lemma REAL_ADD_RINV: "real_add x (real_neg x) = real_of_num 0"
  by (import hollight REAL_ADD_RINV)

lemma REAL_EQ_ADD_LCANCEL: "(real_add x y = real_add x z) = (y = z)"
  by (import hollight REAL_EQ_ADD_LCANCEL)

lemma REAL_EQ_ADD_RCANCEL: "(real_add x z = real_add y z) = (x = y)"
  by (import hollight REAL_EQ_ADD_RCANCEL)

lemma REAL_MUL_RZERO: "real_mul x (real_of_num 0) = real_of_num 0"
  by (import hollight REAL_MUL_RZERO)

lemma REAL_MUL_LZERO: "real_mul (real_of_num 0) x = real_of_num 0"
  by (import hollight REAL_MUL_LZERO)

lemma REAL_NEG_NEG: "real_neg (real_neg x) = x"
  by (import hollight REAL_NEG_NEG)

lemma REAL_MUL_RNEG: "real_mul x (real_neg y) = real_neg (real_mul x y)"
  by (import hollight REAL_MUL_RNEG)

lemma REAL_MUL_LNEG: "real_mul (real_neg x) y = real_neg (real_mul x y)"
  by (import hollight REAL_MUL_LNEG)

lemma REAL_NEG_ADD: "real_neg (real_add x y) = real_add (real_neg x) (real_neg y)"
  by (import hollight REAL_NEG_ADD)

lemma REAL_ADD_RID: "real_add x (real_of_num 0) = x"
  by (import hollight REAL_ADD_RID)

lemma REAL_NEG_0: "real_neg (real_of_num 0) = real_of_num 0"
  by (import hollight REAL_NEG_0)

lemma REAL_LE_LNEG: "real_le (real_neg x) y = real_le (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LE_LNEG)

lemma REAL_LE_NEG2: "real_le (real_neg x) (real_neg y) = real_le y x"
  by (import hollight REAL_LE_NEG2)

lemma REAL_LE_RNEG: "real_le x (real_neg y) = real_le (real_add x y) (real_of_num 0)"
  by (import hollight REAL_LE_RNEG)

lemma REAL_OF_NUM_POW: "real_pow (real_of_num x) n = real_of_num (x ^ n)"
  by (import hollight REAL_OF_NUM_POW)

lemma REAL_POW_NEG: "real_pow (real_neg x) n =
(if even n then real_pow x n else real_neg (real_pow x n))"
  by (import hollight REAL_POW_NEG)

lemma REAL_ABS_NUM: "real_abs (real_of_num x) = real_of_num x"
  by (import hollight REAL_ABS_NUM)

lemma REAL_ABS_NEG: "real_abs (real_neg x) = real_abs x"
  by (import hollight REAL_ABS_NEG)

lemma REAL_LTE_TOTAL: "real_lt x xa | real_le xa x"
  by (import hollight REAL_LTE_TOTAL)

lemma REAL_LET_TOTAL: "real_le x xa | real_lt xa x"
  by (import hollight REAL_LET_TOTAL)

lemma REAL_LT_IMP_LE: "real_lt x y ==> real_le x y"
  by (import hollight REAL_LT_IMP_LE)

lemma REAL_LTE_TRANS: "real_lt x y & real_le y z ==> real_lt x z"
  by (import hollight REAL_LTE_TRANS)

lemma REAL_LET_TRANS: "real_le x y & real_lt y z ==> real_lt x z"
  by (import hollight REAL_LET_TRANS)

lemma REAL_LT_TRANS: "real_lt x y & real_lt y z ==> real_lt x z"
  by (import hollight REAL_LT_TRANS)

lemma REAL_LE_ADD: "real_le (real_of_num 0) x & real_le (real_of_num 0) y
==> real_le (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LE_ADD)

lemma REAL_LTE_ANTISYM: "~ (real_lt x y & real_le y x)"
  by (import hollight REAL_LTE_ANTISYM)

lemma REAL_SUB_LE: "real_le (real_of_num 0) (real_sub x xa) = real_le xa x"
  by (import hollight REAL_SUB_LE)

lemma REAL_NEG_SUB: "real_neg (real_sub x xa) = real_sub xa x"
  by (import hollight REAL_NEG_SUB)

lemma REAL_LE_LT: "real_le x xa = (real_lt x xa | x = xa)"
  by (import hollight REAL_LE_LT)

lemma REAL_SUB_LT: "real_lt (real_of_num 0) (real_sub x xa) = real_lt xa x"
  by (import hollight REAL_SUB_LT)

lemma REAL_NOT_LT: "(~ real_lt x xa) = real_le xa x"
  by (import hollight REAL_NOT_LT)

lemma REAL_SUB_0: "(real_sub x y = real_of_num 0) = (x = y)"
  by (import hollight REAL_SUB_0)

lemma REAL_LT_LE: "real_lt x y = (real_le x y & x ~= y)"
  by (import hollight REAL_LT_LE)

lemma REAL_LT_REFL: "~ real_lt x x"
  by (import hollight REAL_LT_REFL)

lemma REAL_LTE_ADD: "real_lt (real_of_num 0) x & real_le (real_of_num 0) y
==> real_lt (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LTE_ADD)

lemma REAL_LET_ADD: "real_le (real_of_num 0) x & real_lt (real_of_num 0) y
==> real_lt (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LET_ADD)

lemma REAL_LT_ADD: "real_lt (real_of_num 0) x & real_lt (real_of_num 0) y
==> real_lt (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LT_ADD)

lemma REAL_ENTIRE: "(real_mul x y = real_of_num 0) = (x = real_of_num 0 | y = real_of_num 0)"
  by (import hollight REAL_ENTIRE)

lemma REAL_LE_NEGTOTAL: "real_le (real_of_num 0) x | real_le (real_of_num 0) (real_neg x)"
  by (import hollight REAL_LE_NEGTOTAL)

lemma REAL_LE_SQUARE: "real_le (real_of_num 0) (real_mul x x)"
  by (import hollight REAL_LE_SQUARE)

lemma REAL_MUL_RID: "real_mul x (real_of_num 1) = x"
  by (import hollight REAL_MUL_RID)

lemma REAL_POW_2: "real_pow x 2 = real_mul x x"
  by (import hollight REAL_POW_2)

lemma REAL_POLY_CLAUSES: "(ALL x y z. real_add x (real_add y z) = real_add (real_add x y) z) &
(ALL x y. real_add x y = real_add y x) &
(ALL x. real_add (real_of_num 0) x = x) &
(ALL x y z. real_mul x (real_mul y z) = real_mul (real_mul x y) z) &
(ALL x y. real_mul x y = real_mul y x) &
(ALL x. real_mul (real_of_num 1) x = x) &
(ALL x. real_mul (real_of_num 0) x = real_of_num 0) &
(ALL x xa xb.
    real_mul x (real_add xa xb) =
    real_add (real_mul x xa) (real_mul x xb)) &
(ALL x. real_pow x 0 = real_of_num 1) &
(ALL x xa. real_pow x (Suc xa) = real_mul x (real_pow x xa))"
  by (import hollight REAL_POLY_CLAUSES)

lemma REAL_POLY_NEG_CLAUSES: "(ALL x. real_neg x = real_mul (real_neg (real_of_num 1)) x) &
(ALL x xa.
    real_sub x xa = real_add x (real_mul (real_neg (real_of_num 1)) xa))"
  by (import hollight REAL_POLY_NEG_CLAUSES)

lemma REAL_POS: "real_le (real_of_num 0) (real_of_num x)"
  by (import hollight REAL_POS)

lemma REAL_OF_NUM_LT: "real_lt (real_of_num x) (real_of_num xa) = (x < xa)"
  by (import hollight REAL_OF_NUM_LT)

lemma REAL_OF_NUM_GE: "real_ge (real_of_num x) (real_of_num xa) = (xa <= x)"
  by (import hollight REAL_OF_NUM_GE)

lemma REAL_OF_NUM_GT: "real_gt (real_of_num x) (real_of_num xa) = (xa < x)"
  by (import hollight REAL_OF_NUM_GT)

lemma REAL_OF_NUM_MAX: "real_max (real_of_num x) (real_of_num xa) = real_of_num (max x xa)"
  by (import hollight REAL_OF_NUM_MAX)

lemma REAL_OF_NUM_MIN: "real_min (real_of_num x) (real_of_num xa) = real_of_num (min x xa)"
  by (import hollight REAL_OF_NUM_MIN)

lemma REAL_OF_NUM_SUC: "real_add (real_of_num x) (real_of_num 1) = real_of_num (Suc x)"
  by (import hollight REAL_OF_NUM_SUC)

lemma REAL_OF_NUM_SUB: "m <= n ==> real_sub (real_of_num n) (real_of_num m) = real_of_num (n - m)"
  by (import hollight REAL_OF_NUM_SUB)

lemma REAL_MUL_AC: "real_mul m n = real_mul n m &
real_mul (real_mul m n) p = real_mul m (real_mul n p) &
real_mul m (real_mul n p) = real_mul n (real_mul m p)"
  by (import hollight REAL_MUL_AC)

lemma REAL_ADD_RDISTRIB: "real_mul (real_add x y) z = real_add (real_mul x z) (real_mul y z)"
  by (import hollight REAL_ADD_RDISTRIB)

lemma REAL_LT_LADD_IMP: "real_lt y z ==> real_lt (real_add x y) (real_add x z)"
  by (import hollight REAL_LT_LADD_IMP)

lemma REAL_LT_MUL: "real_lt (real_of_num 0) x & real_lt (real_of_num 0) y
==> real_lt (real_of_num 0) (real_mul x y)"
  by (import hollight REAL_LT_MUL)

lemma REAL_EQ_ADD_LCANCEL_0: "(real_add x y = x) = (y = real_of_num 0)"
  by (import hollight REAL_EQ_ADD_LCANCEL_0)

lemma REAL_EQ_ADD_RCANCEL_0: "(real_add x y = y) = (x = real_of_num 0)"
  by (import hollight REAL_EQ_ADD_RCANCEL_0)

lemma REAL_LNEG_UNIQ: "(real_add x y = real_of_num 0) = (x = real_neg y)"
  by (import hollight REAL_LNEG_UNIQ)

lemma REAL_RNEG_UNIQ: "(real_add x y = real_of_num 0) = (y = real_neg x)"
  by (import hollight REAL_RNEG_UNIQ)

lemma REAL_NEG_LMUL: "real_neg (real_mul x y) = real_mul (real_neg x) y"
  by (import hollight REAL_NEG_LMUL)

lemma REAL_NEG_RMUL: "real_neg (real_mul x y) = real_mul x (real_neg y)"
  by (import hollight REAL_NEG_RMUL)

lemma REAL_NEGNEG: "real_neg (real_neg x) = x"
  by (import hollight REAL_NEGNEG)

lemma REAL_NEG_MUL2: "real_mul (real_neg x) (real_neg y) = real_mul x y"
  by (import hollight REAL_NEG_MUL2)

lemma REAL_LT_LADD: "real_lt (real_add x y) (real_add x z) = real_lt y z"
  by (import hollight REAL_LT_LADD)

lemma REAL_LT_RADD: "real_lt (real_add x z) (real_add y z) = real_lt x y"
  by (import hollight REAL_LT_RADD)

lemma REAL_LT_ANTISYM: "~ (real_lt x y & real_lt y x)"
  by (import hollight REAL_LT_ANTISYM)

lemma REAL_LT_GT: "real_lt x y ==> ~ real_lt y x"
  by (import hollight REAL_LT_GT)

lemma REAL_NOT_EQ: "(x ~= y) = (real_lt x y | real_lt y x)"
  by (import hollight REAL_NOT_EQ)

lemma REAL_LET_ANTISYM: "~ (real_le x y & real_lt y x)"
  by (import hollight REAL_LET_ANTISYM)

lemma REAL_NEG_LT0: "real_lt (real_neg x) (real_of_num 0) = real_lt (real_of_num 0) x"
  by (import hollight REAL_NEG_LT0)

lemma REAL_NEG_GT0: "real_lt (real_of_num 0) (real_neg x) = real_lt x (real_of_num 0)"
  by (import hollight REAL_NEG_GT0)

lemma REAL_NEG_LE0: "real_le (real_neg x) (real_of_num 0) = real_le (real_of_num 0) x"
  by (import hollight REAL_NEG_LE0)

lemma REAL_NEG_GE0: "real_le (real_of_num 0) (real_neg x) = real_le x (real_of_num 0)"
  by (import hollight REAL_NEG_GE0)

lemma REAL_LT_TOTAL: "x = y | real_lt x y | real_lt y x"
  by (import hollight REAL_LT_TOTAL)

lemma REAL_LT_NEGTOTAL: "x = real_of_num 0 |
real_lt (real_of_num 0) x | real_lt (real_of_num 0) (real_neg x)"
  by (import hollight REAL_LT_NEGTOTAL)

lemma REAL_LE_01: "real_le (real_of_num 0) (real_of_num 1)"
  by (import hollight REAL_LE_01)

lemma REAL_LT_01: "real_lt (real_of_num 0) (real_of_num 1)"
  by (import hollight REAL_LT_01)

lemma REAL_LE_LADD: "real_le (real_add x y) (real_add x z) = real_le y z"
  by (import hollight REAL_LE_LADD)

lemma REAL_LE_RADD: "real_le (real_add x z) (real_add y z) = real_le x y"
  by (import hollight REAL_LE_RADD)

lemma REAL_LT_ADD2: "real_lt w x & real_lt y z ==> real_lt (real_add w y) (real_add x z)"
  by (import hollight REAL_LT_ADD2)

lemma REAL_LE_ADD2: "real_le w x & real_le y z ==> real_le (real_add w y) (real_add x z)"
  by (import hollight REAL_LE_ADD2)

lemma REAL_LT_LNEG: "real_lt (real_neg x) xa = real_lt (real_of_num 0) (real_add x xa)"
  by (import hollight REAL_LT_LNEG)

lemma REAL_LT_RNEG: "real_lt x (real_neg xa) = real_lt (real_add x xa) (real_of_num 0)"
  by (import hollight REAL_LT_RNEG)

lemma REAL_LT_ADDNEG: "real_lt y (real_add x (real_neg z)) = real_lt (real_add y z) x"
  by (import hollight REAL_LT_ADDNEG)

lemma REAL_LT_ADDNEG2: "real_lt (real_add x (real_neg y)) z = real_lt x (real_add z y)"
  by (import hollight REAL_LT_ADDNEG2)

lemma REAL_LT_ADD1: "real_le x y ==> real_lt x (real_add y (real_of_num 1))"
  by (import hollight REAL_LT_ADD1)

lemma REAL_SUB_ADD: "real_add (real_sub x y) y = x"
  by (import hollight REAL_SUB_ADD)

lemma REAL_SUB_ADD2: "real_add y (real_sub x y) = x"
  by (import hollight REAL_SUB_ADD2)

lemma REAL_SUB_REFL: "real_sub x x = real_of_num 0"
  by (import hollight REAL_SUB_REFL)

lemma REAL_LE_DOUBLE: "real_le (real_of_num 0) (real_add x x) = real_le (real_of_num 0) x"
  by (import hollight REAL_LE_DOUBLE)

lemma REAL_LE_NEGL: "real_le (real_neg x) x = real_le (real_of_num 0) x"
  by (import hollight REAL_LE_NEGL)

lemma REAL_LE_NEGR: "real_le x (real_neg x) = real_le x (real_of_num 0)"
  by (import hollight REAL_LE_NEGR)

lemma REAL_NEG_EQ_0: "(real_neg x = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight REAL_NEG_EQ_0)

lemma REAL_ADD_SUB: "real_sub (real_add x y) x = y"
  by (import hollight REAL_ADD_SUB)

lemma REAL_NEG_EQ: "(real_neg x = y) = (x = real_neg y)"
  by (import hollight REAL_NEG_EQ)

lemma REAL_NEG_MINUS1: "real_neg x = real_mul (real_neg (real_of_num 1)) x"
  by (import hollight REAL_NEG_MINUS1)

lemma REAL_LT_IMP_NE: "real_lt x y ==> x ~= y"
  by (import hollight REAL_LT_IMP_NE)

lemma REAL_LE_ADDR: "real_le x (real_add x y) = real_le (real_of_num 0) y"
  by (import hollight REAL_LE_ADDR)

lemma REAL_LE_ADDL: "real_le y (real_add x y) = real_le (real_of_num 0) x"
  by (import hollight REAL_LE_ADDL)

lemma REAL_LT_ADDR: "real_lt x (real_add x y) = real_lt (real_of_num 0) y"
  by (import hollight REAL_LT_ADDR)

lemma REAL_LT_ADDL: "real_lt y (real_add x y) = real_lt (real_of_num 0) x"
  by (import hollight REAL_LT_ADDL)

lemma REAL_SUB_SUB: "real_sub (real_sub x y) x = real_neg y"
  by (import hollight REAL_SUB_SUB)

lemma REAL_LT_ADD_SUB: "real_lt (real_add x y) z = real_lt x (real_sub z y)"
  by (import hollight REAL_LT_ADD_SUB)

lemma REAL_LT_SUB_RADD: "real_lt (real_sub x y) z = real_lt x (real_add z y)"
  by (import hollight REAL_LT_SUB_RADD)

lemma REAL_LT_SUB_LADD: "real_lt x (real_sub y z) = real_lt (real_add x z) y"
  by (import hollight REAL_LT_SUB_LADD)

lemma REAL_LE_SUB_LADD: "real_le x (real_sub y z) = real_le (real_add x z) y"
  by (import hollight REAL_LE_SUB_LADD)

lemma REAL_LE_SUB_RADD: "real_le (real_sub x y) z = real_le x (real_add z y)"
  by (import hollight REAL_LE_SUB_RADD)

lemma REAL_LT_NEG: "real_lt (real_neg x) (real_neg y) = real_lt y x"
  by (import hollight REAL_LT_NEG)

lemma REAL_LE_NEG: "real_le (real_neg x) (real_neg y) = real_le y x"
  by (import hollight REAL_LE_NEG)

lemma REAL_ADD2_SUB2: "real_sub (real_add a b) (real_add c d) =
real_add (real_sub a c) (real_sub b d)"
  by (import hollight REAL_ADD2_SUB2)

lemma REAL_SUB_LZERO: "real_sub (real_of_num 0) x = real_neg x"
  by (import hollight REAL_SUB_LZERO)

lemma REAL_SUB_RZERO: "real_sub x (real_of_num 0) = x"
  by (import hollight REAL_SUB_RZERO)

lemma REAL_LET_ADD2: "real_le w x & real_lt y z ==> real_lt (real_add w y) (real_add x z)"
  by (import hollight REAL_LET_ADD2)

lemma REAL_LTE_ADD2: "real_lt w x & real_le y z ==> real_lt (real_add w y) (real_add x z)"
  by (import hollight REAL_LTE_ADD2)

lemma REAL_SUB_LNEG: "real_sub (real_neg x) y = real_neg (real_add x y)"
  by (import hollight REAL_SUB_LNEG)

lemma REAL_SUB_RNEG: "real_sub x (real_neg y) = real_add x y"
  by (import hollight REAL_SUB_RNEG)

lemma REAL_SUB_NEG2: "real_sub (real_neg x) (real_neg y) = real_sub y x"
  by (import hollight REAL_SUB_NEG2)

lemma REAL_SUB_TRIANGLE: "real_add (real_sub a b) (real_sub b c) = real_sub a c"
  by (import hollight REAL_SUB_TRIANGLE)

lemma REAL_EQ_SUB_LADD: "(x = real_sub y z) = (real_add x z = y)"
  by (import hollight REAL_EQ_SUB_LADD)

lemma REAL_EQ_SUB_RADD: "(real_sub x y = z) = (x = real_add z y)"
  by (import hollight REAL_EQ_SUB_RADD)

lemma REAL_SUB_SUB2: "real_sub x (real_sub x y) = y"
  by (import hollight REAL_SUB_SUB2)

lemma REAL_ADD_SUB2: "real_sub x (real_add x y) = real_neg y"
  by (import hollight REAL_ADD_SUB2)

lemma REAL_EQ_IMP_LE: "x = y ==> real_le x y"
  by (import hollight REAL_EQ_IMP_LE)

lemma REAL_POS_NZ: "real_lt (real_of_num 0) x ==> x ~= real_of_num 0"
  by (import hollight REAL_POS_NZ)

lemma REAL_DIFFSQ: "real_mul (real_add x y) (real_sub x y) =
real_sub (real_mul x x) (real_mul y y)"
  by (import hollight REAL_DIFFSQ)

lemma REAL_EQ_NEG2: "(real_neg x = real_neg y) = (x = y)"
  by (import hollight REAL_EQ_NEG2)

lemma REAL_LT_NEG2: "real_lt (real_neg x) (real_neg y) = real_lt y x"
  by (import hollight REAL_LT_NEG2)

lemma REAL_SUB_LDISTRIB: "real_mul x (real_sub y z) = real_sub (real_mul x y) (real_mul x z)"
  by (import hollight REAL_SUB_LDISTRIB)

lemma REAL_SUB_RDISTRIB: "real_mul (real_sub x y) z = real_sub (real_mul x z) (real_mul y z)"
  by (import hollight REAL_SUB_RDISTRIB)

lemma REAL_ABS_ZERO: "(real_abs x = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight REAL_ABS_ZERO)

lemma REAL_ABS_0: "real_abs (real_of_num 0) = real_of_num 0"
  by (import hollight REAL_ABS_0)

lemma REAL_ABS_1: "real_abs (real_of_num 1) = real_of_num 1"
  by (import hollight REAL_ABS_1)

lemma REAL_ABS_TRIANGLE: "real_le (real_abs (real_add x y)) (real_add (real_abs x) (real_abs y))"
  by (import hollight REAL_ABS_TRIANGLE)

lemma REAL_ABS_TRIANGLE_LE: "real_le (real_add (real_abs x) (real_abs (real_sub y x))) z
==> real_le (real_abs y) z"
  by (import hollight REAL_ABS_TRIANGLE_LE)

lemma REAL_ABS_TRIANGLE_LT: "real_lt (real_add (real_abs x) (real_abs (real_sub y x))) z
==> real_lt (real_abs y) z"
  by (import hollight REAL_ABS_TRIANGLE_LT)

lemma REAL_ABS_POS: "real_le (real_of_num 0) (real_abs x)"
  by (import hollight REAL_ABS_POS)

lemma REAL_ABS_SUB: "real_abs (real_sub x y) = real_abs (real_sub y x)"
  by (import hollight REAL_ABS_SUB)

lemma REAL_ABS_NZ: "(x ~= real_of_num 0) = real_lt (real_of_num 0) (real_abs x)"
  by (import hollight REAL_ABS_NZ)

lemma REAL_ABS_ABS: "real_abs (real_abs x) = real_abs x"
  by (import hollight REAL_ABS_ABS)

lemma REAL_ABS_LE: "real_le x (real_abs x)"
  by (import hollight REAL_ABS_LE)

lemma REAL_ABS_REFL: "(real_abs x = x) = real_le (real_of_num 0) x"
  by (import hollight REAL_ABS_REFL)

lemma REAL_ABS_BETWEEN: "(real_lt (real_of_num 0) d &
 real_lt (real_sub x d) y & real_lt y (real_add x d)) =
real_lt (real_abs (real_sub y x)) d"
  by (import hollight REAL_ABS_BETWEEN)

lemma REAL_ABS_BOUND: "real_lt (real_abs (real_sub x y)) d ==> real_lt y (real_add x d)"
  by (import hollight REAL_ABS_BOUND)

lemma REAL_ABS_STILLNZ: "real_lt (real_abs (real_sub x y)) (real_abs y) ==> x ~= real_of_num 0"
  by (import hollight REAL_ABS_STILLNZ)

lemma REAL_ABS_CASES: "x = real_of_num 0 | real_lt (real_of_num 0) (real_abs x)"
  by (import hollight REAL_ABS_CASES)

lemma REAL_ABS_BETWEEN1: "real_lt x z & real_lt (real_abs (real_sub y x)) (real_sub z x)
==> real_lt y z"
  by (import hollight REAL_ABS_BETWEEN1)

lemma REAL_ABS_SIGN: "real_lt (real_abs (real_sub x y)) y ==> real_lt (real_of_num 0) x"
  by (import hollight REAL_ABS_SIGN)

lemma REAL_ABS_SIGN2: "real_lt (real_abs (real_sub x y)) (real_neg y) ==> real_lt x (real_of_num 0)"
  by (import hollight REAL_ABS_SIGN2)

lemma REAL_ABS_CIRCLE: "real_lt (real_abs h) (real_sub (real_abs y) (real_abs x))
==> real_lt (real_abs (real_add x h)) (real_abs y)"
  by (import hollight REAL_ABS_CIRCLE)

lemma REAL_SUB_ABS: "real_le (real_sub (real_abs x) (real_abs y)) (real_abs (real_sub x y))"
  by (import hollight REAL_SUB_ABS)

lemma REAL_ABS_SUB_ABS: "real_le (real_abs (real_sub (real_abs x) (real_abs y)))
 (real_abs (real_sub x y))"
  by (import hollight REAL_ABS_SUB_ABS)

lemma REAL_ABS_BETWEEN2: "real_lt x0 y0 &
real_lt (real_mul (real_of_num 2) (real_abs (real_sub x x0)))
 (real_sub y0 x0) &
real_lt (real_mul (real_of_num 2) (real_abs (real_sub y y0)))
 (real_sub y0 x0)
==> real_lt x y"
  by (import hollight REAL_ABS_BETWEEN2)

lemma REAL_ABS_BOUNDS: "real_le (real_abs x) k = (real_le (real_neg k) x & real_le x k)"
  by (import hollight REAL_ABS_BOUNDS)

lemma REAL_BOUNDS_LE: "(real_le (real_neg k) x & real_le x k) = real_le (real_abs x) k"
  by (import hollight REAL_BOUNDS_LE)

lemma REAL_BOUNDS_LT: "(real_lt (real_neg k) x & real_lt x k) = real_lt (real_abs x) k"
  by (import hollight REAL_BOUNDS_LT)

lemma REAL_MIN_MAX: "real_min x y = real_neg (real_max (real_neg x) (real_neg y))"
  by (import hollight REAL_MIN_MAX)

lemma REAL_MAX_MIN: "real_max x y = real_neg (real_min (real_neg x) (real_neg y))"
  by (import hollight REAL_MAX_MIN)

lemma REAL_MAX_MAX: "real_le x (real_max x y) & real_le y (real_max x y)"
  by (import hollight REAL_MAX_MAX)

lemma REAL_MIN_MIN: "real_le (real_min x y) x & real_le (real_min x y) y"
  by (import hollight REAL_MIN_MIN)

lemma REAL_MAX_SYM: "real_max x y = real_max y x"
  by (import hollight REAL_MAX_SYM)

lemma REAL_MIN_SYM: "real_min x y = real_min y x"
  by (import hollight REAL_MIN_SYM)

lemma REAL_LE_MAX: "real_le z (real_max x y) = (real_le z x | real_le z y)"
  by (import hollight REAL_LE_MAX)

lemma REAL_LE_MIN: "real_le z (real_min x y) = (real_le z x & real_le z y)"
  by (import hollight REAL_LE_MIN)

lemma REAL_LT_MAX: "real_lt z (real_max x y) = (real_lt z x | real_lt z y)"
  by (import hollight REAL_LT_MAX)

lemma REAL_LT_MIN: "real_lt z (real_min x y) = (real_lt z x & real_lt z y)"
  by (import hollight REAL_LT_MIN)

lemma REAL_MAX_LE: "real_le (real_max x y) z = (real_le x z & real_le y z)"
  by (import hollight REAL_MAX_LE)

lemma REAL_MIN_LE: "real_le (real_min x y) z = (real_le x z | real_le y z)"
  by (import hollight REAL_MIN_LE)

lemma REAL_MAX_LT: "real_lt (real_max x y) z = (real_lt x z & real_lt y z)"
  by (import hollight REAL_MAX_LT)

lemma REAL_MIN_LT: "real_lt (real_min x y) z = (real_lt x z | real_lt y z)"
  by (import hollight REAL_MIN_LT)

lemma REAL_MAX_ASSOC: "real_max x (real_max y z) = real_max (real_max x y) z"
  by (import hollight REAL_MAX_ASSOC)

lemma REAL_MIN_ASSOC: "real_min x (real_min y z) = real_min (real_min x y) z"
  by (import hollight REAL_MIN_ASSOC)

lemma REAL_MAX_ACI: "real_max x y = real_max y x &
real_max (real_max x y) z = real_max x (real_max y z) &
real_max x (real_max y z) = real_max y (real_max x z) &
real_max x x = x & real_max x (real_max x y) = real_max x y"
  by (import hollight REAL_MAX_ACI)

lemma REAL_MIN_ACI: "real_min x y = real_min y x &
real_min (real_min x y) z = real_min x (real_min y z) &
real_min x (real_min y z) = real_min y (real_min x z) &
real_min x x = x & real_min x (real_min x y) = real_min x y"
  by (import hollight REAL_MIN_ACI)

lemma REAL_ABS_MUL: "real_abs (real_mul x y) = real_mul (real_abs x) (real_abs y)"
  by (import hollight REAL_ABS_MUL)

lemma REAL_POW_LE: "real_le (real_of_num 0) x ==> real_le (real_of_num 0) (real_pow x n)"
  by (import hollight REAL_POW_LE)

lemma REAL_POW_LT: "real_lt (real_of_num 0) x ==> real_lt (real_of_num 0) (real_pow x n)"
  by (import hollight REAL_POW_LT)

lemma REAL_ABS_POW: "real_abs (real_pow x n) = real_pow (real_abs x) n"
  by (import hollight REAL_ABS_POW)

lemma REAL_LE_LMUL: "real_le (real_of_num 0) x & real_le xa xb
==> real_le (real_mul x xa) (real_mul x xb)"
  by (import hollight REAL_LE_LMUL)

lemma REAL_LE_RMUL: "real_le x y & real_le (real_of_num 0) z
==> real_le (real_mul x z) (real_mul y z)"
  by (import hollight REAL_LE_RMUL)

lemma REAL_LT_LMUL: "real_lt (real_of_num 0) x & real_lt xa xb
==> real_lt (real_mul x xa) (real_mul x xb)"
  by (import hollight REAL_LT_LMUL)

lemma REAL_LT_RMUL: "real_lt x y & real_lt (real_of_num 0) z
==> real_lt (real_mul x z) (real_mul y z)"
  by (import hollight REAL_LT_RMUL)

lemma REAL_EQ_MUL_LCANCEL: "(real_mul x y = real_mul x z) = (x = real_of_num 0 | y = z)"
  by (import hollight REAL_EQ_MUL_LCANCEL)

lemma REAL_EQ_MUL_RCANCEL: "(real_mul x xb = real_mul xa xb) = (x = xa | xb = real_of_num 0)"
  by (import hollight REAL_EQ_MUL_RCANCEL)

lemma REAL_MUL_LINV_UNIQ: "real_mul x y = real_of_num 1 ==> real_inv y = x"
  by (import hollight REAL_MUL_LINV_UNIQ)

lemma REAL_MUL_RINV_UNIQ: "real_mul x xa = real_of_num 1 ==> real_inv x = xa"
  by (import hollight REAL_MUL_RINV_UNIQ)

lemma REAL_INV_INV: "real_inv (real_inv x) = x"
  by (import hollight REAL_INV_INV)

lemma REAL_EQ_INV2: "(real_inv x = real_inv y) = (x = y)"
  by (import hollight REAL_EQ_INV2)

lemma REAL_INV_EQ_0: "(real_inv x = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight REAL_INV_EQ_0)

lemma REAL_LT_INV: "real_lt (real_of_num 0) x ==> real_lt (real_of_num 0) (real_inv x)"
  by (import hollight REAL_LT_INV)

lemma REAL_LT_INV_EQ: "real_lt (real_of_num 0) (real_inv x) = real_lt (real_of_num 0) x"
  by (import hollight REAL_LT_INV_EQ)

lemma REAL_INV_NEG: "real_inv (real_neg x) = real_neg (real_inv x)"
  by (import hollight REAL_INV_NEG)

lemma REAL_LE_INV_EQ: "real_le (real_of_num 0) (real_inv x) = real_le (real_of_num 0) x"
  by (import hollight REAL_LE_INV_EQ)

lemma REAL_LE_INV: "real_le (real_of_num 0) x ==> real_le (real_of_num 0) (real_inv x)"
  by (import hollight REAL_LE_INV)

lemma REAL_MUL_RINV: "x ~= real_of_num 0 ==> real_mul x (real_inv x) = real_of_num 1"
  by (import hollight REAL_MUL_RINV)

lemma REAL_INV_1: "real_inv (real_of_num 1) = real_of_num 1"
  by (import hollight REAL_INV_1)

lemma REAL_INV_EQ_1: "(real_inv x = real_of_num 1) = (x = real_of_num 1)"
  by (import hollight REAL_INV_EQ_1)

lemma REAL_DIV_1: "real_div x (real_of_num 1) = x"
  by (import hollight REAL_DIV_1)

lemma REAL_DIV_REFL: "x ~= real_of_num 0 ==> real_div x x = real_of_num 1"
  by (import hollight REAL_DIV_REFL)

lemma REAL_DIV_RMUL: "xa ~= real_of_num 0 ==> real_mul (real_div x xa) xa = x"
  by (import hollight REAL_DIV_RMUL)

lemma REAL_DIV_LMUL: "xa ~= real_of_num 0 ==> real_mul xa (real_div x xa) = x"
  by (import hollight REAL_DIV_LMUL)

lemma REAL_ABS_INV: "real_abs (real_inv x) = real_inv (real_abs x)"
  by (import hollight REAL_ABS_INV)

lemma REAL_ABS_DIV: "real_abs (real_div x xa) = real_div (real_abs x) (real_abs xa)"
  by (import hollight REAL_ABS_DIV)

lemma REAL_INV_MUL: "real_inv (real_mul x y) = real_mul (real_inv x) (real_inv y)"
  by (import hollight REAL_INV_MUL)

lemma REAL_INV_DIV: "real_inv (real_div x xa) = real_div xa x"
  by (import hollight REAL_INV_DIV)

lemma REAL_POW_MUL: "real_pow (real_mul x y) n = real_mul (real_pow x n) (real_pow y n)"
  by (import hollight REAL_POW_MUL)

lemma REAL_POW_INV: "real_pow (real_inv x) n = real_inv (real_pow x n)"
  by (import hollight REAL_POW_INV)

lemma REAL_INV_POW: "real_inv (real_pow x xa) = real_pow (real_inv x) xa"
  by (import hollight REAL_INV_POW)

lemma REAL_POW_DIV: "real_pow (real_div x xa) xb = real_div (real_pow x xb) (real_pow xa xb)"
  by (import hollight REAL_POW_DIV)

lemma REAL_POW_ADD: "real_pow x (m + n) = real_mul (real_pow x m) (real_pow x n)"
  by (import hollight REAL_POW_ADD)

lemma REAL_POW_NZ: "x ~= real_of_num 0 ==> real_pow x n ~= real_of_num 0"
  by (import hollight REAL_POW_NZ)

lemma REAL_POW_SUB: "x ~= real_of_num 0 & m <= n
==> real_pow x (n - m) = real_div (real_pow x n) (real_pow x m)"
  by (import hollight REAL_POW_SUB)

lemma REAL_LT_IMP_NZ: "real_lt (real_of_num 0) x ==> x ~= real_of_num 0"
  by (import hollight REAL_LT_IMP_NZ)

lemma REAL_LT_LCANCEL_IMP: "real_lt (real_of_num 0) x & real_lt (real_mul x y) (real_mul x z)
==> real_lt y z"
  by (import hollight REAL_LT_LCANCEL_IMP)

lemma REAL_LT_RCANCEL_IMP: "real_lt (real_of_num 0) xb & real_lt (real_mul x xb) (real_mul xa xb)
==> real_lt x xa"
  by (import hollight REAL_LT_RCANCEL_IMP)

lemma REAL_LE_LCANCEL_IMP: "real_lt (real_of_num 0) x & real_le (real_mul x y) (real_mul x z)
==> real_le y z"
  by (import hollight REAL_LE_LCANCEL_IMP)

lemma REAL_LE_RCANCEL_IMP: "real_lt (real_of_num 0) xb & real_le (real_mul x xb) (real_mul xa xb)
==> real_le x xa"
  by (import hollight REAL_LE_RCANCEL_IMP)

lemma REAL_LE_RMUL_EQ: "real_lt (real_of_num 0) z
==> real_le (real_mul x z) (real_mul y z) = real_le x y"
  by (import hollight REAL_LE_RMUL_EQ)

lemma REAL_LE_LMUL_EQ: "real_lt (real_of_num 0) z
==> real_le (real_mul z x) (real_mul z y) = real_le x y"
  by (import hollight REAL_LE_LMUL_EQ)

lemma REAL_LT_RMUL_EQ: "real_lt (real_of_num 0) xb
==> real_lt (real_mul x xb) (real_mul xa xb) = real_lt x xa"
  by (import hollight REAL_LT_RMUL_EQ)

lemma REAL_LT_LMUL_EQ: "real_lt (real_of_num 0) xb
==> real_lt (real_mul xb x) (real_mul xb xa) = real_lt x xa"
  by (import hollight REAL_LT_LMUL_EQ)

lemma REAL_LE_MUL_EQ: "(ALL x y.
    real_lt (real_of_num 0) x -->
    real_le (real_of_num 0) (real_mul x y) = real_le (real_of_num 0) y) &
(ALL x y.
    real_lt (real_of_num 0) y -->
    real_le (real_of_num 0) (real_mul x y) = real_le (real_of_num 0) x)"
  by (import hollight REAL_LE_MUL_EQ)

lemma REAL_LT_MUL_EQ: "(ALL x y.
    real_lt (real_of_num 0) x -->
    real_lt (real_of_num 0) (real_mul x y) = real_lt (real_of_num 0) y) &
(ALL x y.
    real_lt (real_of_num 0) y -->
    real_lt (real_of_num 0) (real_mul x y) = real_lt (real_of_num 0) x)"
  by (import hollight REAL_LT_MUL_EQ)

lemma REAL_MUL_POS_LT: "real_lt (real_of_num 0) (real_mul x y) =
(real_lt (real_of_num 0) x & real_lt (real_of_num 0) y |
 real_lt x (real_of_num 0) & real_lt y (real_of_num 0))"
  by (import hollight REAL_MUL_POS_LT)

lemma REAL_MUL_POS_LE: "real_le (real_of_num 0) (real_mul x xa) =
(x = real_of_num 0 |
 xa = real_of_num 0 |
 real_lt (real_of_num 0) x & real_lt (real_of_num 0) xa |
 real_lt x (real_of_num 0) & real_lt xa (real_of_num 0))"
  by (import hollight REAL_MUL_POS_LE)

lemma REAL_LE_RDIV_EQ: "real_lt (real_of_num 0) z
==> real_le x (real_div y z) = real_le (real_mul x z) y"
  by (import hollight REAL_LE_RDIV_EQ)

lemma REAL_LE_LDIV_EQ: "real_lt (real_of_num 0) z
==> real_le (real_div x z) y = real_le x (real_mul y z)"
  by (import hollight REAL_LE_LDIV_EQ)

lemma REAL_LT_RDIV_EQ: "real_lt (real_of_num 0) xb
==> real_lt x (real_div xa xb) = real_lt (real_mul x xb) xa"
  by (import hollight REAL_LT_RDIV_EQ)

lemma REAL_LT_LDIV_EQ: "real_lt (real_of_num 0) xb
==> real_lt (real_div x xb) xa = real_lt x (real_mul xa xb)"
  by (import hollight REAL_LT_LDIV_EQ)

lemma REAL_EQ_RDIV_EQ: "real_lt (real_of_num 0) xb ==> (x = real_div xa xb) = (real_mul x xb = xa)"
  by (import hollight REAL_EQ_RDIV_EQ)

lemma REAL_EQ_LDIV_EQ: "real_lt (real_of_num 0) xb ==> (real_div x xb = xa) = (x = real_mul xa xb)"
  by (import hollight REAL_EQ_LDIV_EQ)

lemma REAL_LT_DIV2_EQ: "real_lt (real_of_num 0) xb
==> real_lt (real_div x xb) (real_div xa xb) = real_lt x xa"
  by (import hollight REAL_LT_DIV2_EQ)

lemma REAL_LE_DIV2_EQ: "real_lt (real_of_num 0) xb
==> real_le (real_div x xb) (real_div xa xb) = real_le x xa"
  by (import hollight REAL_LE_DIV2_EQ)

lemma REAL_MUL_2: "real_mul (real_of_num 2) x = real_add x x"
  by (import hollight REAL_MUL_2)

lemma REAL_POW_EQ_0: "(real_pow x n = real_of_num 0) = (x = real_of_num 0 & n ~= 0)"
  by (import hollight REAL_POW_EQ_0)

lemma REAL_LE_MUL2: "real_le (real_of_num 0) w &
real_le w x & real_le (real_of_num 0) y & real_le y z
==> real_le (real_mul w y) (real_mul x z)"
  by (import hollight REAL_LE_MUL2)

lemma REAL_LT_MUL2: "real_le (real_of_num 0) w &
real_lt w x & real_le (real_of_num 0) y & real_lt y z
==> real_lt (real_mul w y) (real_mul x z)"
  by (import hollight REAL_LT_MUL2)

lemma REAL_LT_SQUARE: "real_lt (real_of_num 0) (real_mul x x) = (x ~= real_of_num 0)"
  by (import hollight REAL_LT_SQUARE)

lemma REAL_POW_1: "real_pow x 1 = x"
  by (import hollight REAL_POW_1)

lemma REAL_POW_ONE: "real_pow (real_of_num 1) n = real_of_num 1"
  by (import hollight REAL_POW_ONE)

lemma REAL_LT_INV2: "real_lt (real_of_num 0) x & real_lt x y
==> real_lt (real_inv y) (real_inv x)"
  by (import hollight REAL_LT_INV2)

lemma REAL_LE_INV2: "real_lt (real_of_num 0) x & real_le x y
==> real_le (real_inv y) (real_inv x)"
  by (import hollight REAL_LE_INV2)

lemma REAL_LT_LINV: "real_lt (real_of_num 0) y & real_lt (real_inv y) x
==> real_lt (real_inv x) y"
  by (import hollight REAL_LT_LINV)

lemma REAL_LT_RINV: "real_lt (real_of_num 0) x & real_lt x (real_inv y)
==> real_lt y (real_inv x)"
  by (import hollight REAL_LT_RINV)

lemma REAL_LE_LINV: "real_lt (real_of_num 0) y & real_le (real_inv y) x
==> real_le (real_inv x) y"
  by (import hollight REAL_LE_LINV)

lemma REAL_LE_RINV: "real_lt (real_of_num 0) x & real_le x (real_inv y)
==> real_le y (real_inv x)"
  by (import hollight REAL_LE_RINV)

lemma REAL_INV_LE_1: "real_le (real_of_num 1) x ==> real_le (real_inv x) (real_of_num 1)"
  by (import hollight REAL_INV_LE_1)

lemma REAL_INV_1_LE: "real_lt (real_of_num 0) x & real_le x (real_of_num 1)
==> real_le (real_of_num 1) (real_inv x)"
  by (import hollight REAL_INV_1_LE)

lemma REAL_INV_LT_1: "real_lt (real_of_num 1) x ==> real_lt (real_inv x) (real_of_num 1)"
  by (import hollight REAL_INV_LT_1)

lemma REAL_INV_1_LT: "real_lt (real_of_num 0) x & real_lt x (real_of_num 1)
==> real_lt (real_of_num 1) (real_inv x)"
  by (import hollight REAL_INV_1_LT)

lemma REAL_SUB_INV: "x ~= real_of_num 0 & xa ~= real_of_num 0
==> real_sub (real_inv x) (real_inv xa) =
    real_div (real_sub xa x) (real_mul x xa)"
  by (import hollight REAL_SUB_INV)

lemma REAL_DOWN: "real_lt (real_of_num 0) d ==> EX x. real_lt (real_of_num 0) x & real_lt x d"
  by (import hollight REAL_DOWN)

lemma REAL_DOWN2: "real_lt (real_of_num 0) d1 & real_lt (real_of_num 0) d2
==> EX e. real_lt (real_of_num 0) e & real_lt e d1 & real_lt e d2"
  by (import hollight REAL_DOWN2)

lemma REAL_POW_LE2: "real_le (real_of_num 0) x & real_le x y
==> real_le (real_pow x n) (real_pow y n)"
  by (import hollight REAL_POW_LE2)

lemma REAL_POW_LE_1: "real_le (real_of_num 1) x ==> real_le (real_of_num 1) (real_pow x n)"
  by (import hollight REAL_POW_LE_1)

lemma REAL_POW_1_LE: "real_le (real_of_num 0) x & real_le x (real_of_num 1)
==> real_le (real_pow x n) (real_of_num 1)"
  by (import hollight REAL_POW_1_LE)

lemma REAL_POW_MONO: "real_le (real_of_num 1) x & m <= n ==> real_le (real_pow x m) (real_pow x n)"
  by (import hollight REAL_POW_MONO)

lemma REAL_POW_LT2: "n ~= 0 & real_le (real_of_num 0) x & real_lt x y
==> real_lt (real_pow x n) (real_pow y n)"
  by (import hollight REAL_POW_LT2)

lemma REAL_POW_LT_1: "n ~= 0 & real_lt (real_of_num 1) x
==> real_lt (real_of_num 1) (real_pow x n)"
  by (import hollight REAL_POW_LT_1)

lemma REAL_POW_1_LT: "n ~= 0 & real_le (real_of_num 0) x & real_lt x (real_of_num 1)
==> real_lt (real_pow x n) (real_of_num 1)"
  by (import hollight REAL_POW_1_LT)

lemma REAL_POW_MONO_LT: "real_lt (real_of_num 1) x & m < n ==> real_lt (real_pow x m) (real_pow x n)"
  by (import hollight REAL_POW_MONO_LT)

lemma REAL_POW_POW: "real_pow (real_pow x m) n = real_pow x (m * n)"
  by (import hollight REAL_POW_POW)

lemma REAL_EQ_RCANCEL_IMP: "z ~= real_of_num 0 & real_mul x z = real_mul y z ==> x = y"
  by (import hollight REAL_EQ_RCANCEL_IMP)

lemma REAL_EQ_LCANCEL_IMP: "xb ~= real_of_num 0 & real_mul xb x = real_mul xb xa ==> x = xa"
  by (import hollight REAL_EQ_LCANCEL_IMP)

lemma REAL_LT_DIV: "real_lt (real_of_num 0) x & real_lt (real_of_num 0) xa
==> real_lt (real_of_num 0) (real_div x xa)"
  by (import hollight REAL_LT_DIV)

lemma REAL_LE_DIV: "real_le (real_of_num 0) x & real_le (real_of_num 0) xa
==> real_le (real_of_num 0) (real_div x xa)"
  by (import hollight REAL_LE_DIV)

lemma REAL_DIV_POW2: "x ~= real_of_num 0
==> real_div (real_pow x m) (real_pow x n) =
    (if n <= m then real_pow x (m - n) else real_inv (real_pow x (n - m)))"
  by (import hollight REAL_DIV_POW2)

lemma REAL_DIV_POW2_ALT: "x ~= real_of_num 0
==> real_div (real_pow x m) (real_pow x n) =
    (if n < m then real_pow x (m - n) else real_inv (real_pow x (n - m)))"
  by (import hollight REAL_DIV_POW2_ALT)

lemma REAL_LT_POW2: "real_lt (real_of_num 0) (real_pow (real_of_num 2) x)"
  by (import hollight REAL_LT_POW2)

lemma REAL_LE_POW2: "real_le (real_of_num 1) (real_pow (real_of_num 2) n)"
  by (import hollight REAL_LE_POW2)

lemma REAL_POW2_ABS: "real_pow (real_abs x) 2 = real_pow x 2"
  by (import hollight REAL_POW2_ABS)

lemma REAL_LE_SQUARE_ABS: "real_le (real_abs x) (real_abs y) = real_le (real_pow x 2) (real_pow y 2)"
  by (import hollight REAL_LE_SQUARE_ABS)

lemma REAL_LT_SQUARE_ABS: "real_lt (real_abs x) (real_abs xa) = real_lt (real_pow x 2) (real_pow xa 2)"
  by (import hollight REAL_LT_SQUARE_ABS)

lemma REAL_EQ_SQUARE_ABS: "(real_abs x = real_abs xa) = (real_pow x 2 = real_pow xa 2)"
  by (import hollight REAL_EQ_SQUARE_ABS)

lemma REAL_LE_POW_2: "real_le (real_of_num 0) (real_pow x 2)"
  by (import hollight REAL_LE_POW_2)

lemma REAL_SOS_EQ_0: "(real_add (real_pow x 2) (real_pow y 2) = real_of_num 0) =
(x = real_of_num 0 & y = real_of_num 0)"
  by (import hollight REAL_SOS_EQ_0)

lemma REAL_POW_ZERO: "real_pow (real_of_num 0) n =
(if n = 0 then real_of_num 1 else real_of_num 0)"
  by (import hollight REAL_POW_ZERO)

lemma REAL_POW_MONO_INV: "real_le (real_of_num 0) x & real_le x (real_of_num 1) & n <= m
==> real_le (real_pow x m) (real_pow x n)"
  by (import hollight REAL_POW_MONO_INV)

lemma REAL_POW_LE2_REV: "n ~= 0 & real_le (real_of_num 0) y & real_le (real_pow x n) (real_pow y n)
==> real_le x y"
  by (import hollight REAL_POW_LE2_REV)

lemma REAL_POW_LT2_REV: "real_le (real_of_num 0) y & real_lt (real_pow x n) (real_pow y n)
==> real_lt x y"
  by (import hollight REAL_POW_LT2_REV)

lemma REAL_POW_EQ: "x ~= 0 &
real_le (real_of_num 0) xa &
real_le (real_of_num 0) xb & real_pow xa x = real_pow xb x
==> xa = xb"
  by (import hollight REAL_POW_EQ)

lemma REAL_POW_EQ_ABS: "n ~= 0 & real_pow x n = real_pow y n ==> real_abs x = real_abs y"
  by (import hollight REAL_POW_EQ_ABS)

lemma REAL_POW_EQ_1_IMP: "n ~= 0 & real_pow x n = real_of_num 1 ==> real_abs x = real_of_num 1"
  by (import hollight REAL_POW_EQ_1_IMP)

lemma REAL_POW_EQ_1: "(real_pow x n = real_of_num 1) =
(real_abs x = real_of_num 1 & (real_lt x (real_of_num 0) --> even n) |
 n = 0)"
  by (import hollight REAL_POW_EQ_1)

lemma REAL_POW_LT2_ODD: "real_lt x y & odd n ==> real_lt (real_pow x n) (real_pow y n)"
  by (import hollight REAL_POW_LT2_ODD)

lemma REAL_POW_LE2_ODD: "real_le xa xb & odd x ==> real_le (real_pow xa x) (real_pow xb x)"
  by (import hollight REAL_POW_LE2_ODD)

lemma REAL_POW_LT2_ODD_EQ: "odd n ==> real_lt (real_pow x n) (real_pow y n) = real_lt x y"
  by (import hollight REAL_POW_LT2_ODD_EQ)

lemma REAL_POW_LE2_ODD_EQ: "odd n ==> real_le (real_pow x n) (real_pow y n) = real_le x y"
  by (import hollight REAL_POW_LE2_ODD_EQ)

lemma REAL_POW_EQ_ODD_EQ: "odd x ==> (real_pow xa x = real_pow xb x) = (xa = xb)"
  by (import hollight REAL_POW_EQ_ODD_EQ)

lemma REAL_POW_EQ_ODD: "odd n & real_pow x n = real_pow y n ==> x = y"
  by (import hollight REAL_POW_EQ_ODD)

lemma REAL_POW_EQ_EQ: "(real_pow x n = real_pow y n) =
(if even n then n = 0 | real_abs x = real_abs y else x = y)"
  by (import hollight REAL_POW_EQ_EQ)

definition
  real_sgn :: "hollight.real => hollight.real"  where
  "real_sgn ==
%u. if real_lt (real_of_num 0) u then real_of_num 1
    else if real_lt u (real_of_num 0) then real_neg (real_of_num 1)
         else real_of_num 0"

lemma DEF_real_sgn: "real_sgn =
(%u. if real_lt (real_of_num 0) u then real_of_num 1
     else if real_lt u (real_of_num 0) then real_neg (real_of_num 1)
          else real_of_num 0)"
  by (import hollight DEF_real_sgn)

lemma REAL_SGN_0: "real_sgn (real_of_num 0) = real_of_num 0"
  by (import hollight REAL_SGN_0)

lemma REAL_SGN_NEG: "real_sgn (real_neg x) = real_neg (real_sgn x)"
  by (import hollight REAL_SGN_NEG)

lemma REAL_SGN_ABS: "real_mul (real_sgn x) (real_abs x) = x"
  by (import hollight REAL_SGN_ABS)

lemma REAL_ABS_SGN: "real_abs (real_sgn x) = real_sgn (real_abs x)"
  by (import hollight REAL_ABS_SGN)

lemma REAL_SGN: "real_sgn x = real_div x (real_abs x)"
  by (import hollight REAL_SGN)

lemma REAL_SGN_MUL: "real_sgn (real_mul x xa) = real_mul (real_sgn x) (real_sgn xa)"
  by (import hollight REAL_SGN_MUL)

lemma REAL_SGN_INV: "real_sgn (real_inv x) = real_sgn x"
  by (import hollight REAL_SGN_INV)

lemma REAL_SGN_DIV: "real_sgn (real_div x xa) = real_div (real_sgn x) (real_sgn xa)"
  by (import hollight REAL_SGN_DIV)

lemma REAL_WLOG_LE: "(ALL x y. P x y = P y x) & (ALL x y. real_le x y --> P x y) ==> P x xa"
  by (import hollight REAL_WLOG_LE)

lemma REAL_WLOG_LT: "(ALL x. P x x) & (ALL x y. P x y = P y x) & (ALL x y. real_lt x y --> P x y)
==> P x xa"
  by (import hollight REAL_WLOG_LT)

definition
  DECIMAL :: "nat => nat => hollight.real"  where
  "DECIMAL == %u ua. real_div (real_of_num u) (real_of_num ua)"

lemma DEF_DECIMAL: "DECIMAL = (%u ua. real_div (real_of_num u) (real_of_num ua))"
  by (import hollight DEF_DECIMAL)

lemma RAT_LEMMA1: "y1 ~= real_of_num 0 & y2 ~= real_of_num 0
==> real_add (real_div x1 y1) (real_div x2 y2) =
    real_mul (real_add (real_mul x1 y2) (real_mul x2 y1))
     (real_mul (real_inv y1) (real_inv y2))"
  by (import hollight RAT_LEMMA1)

lemma RAT_LEMMA2: "real_lt (real_of_num 0) y1 & real_lt (real_of_num 0) y2
==> real_add (real_div x1 y1) (real_div x2 y2) =
    real_mul (real_add (real_mul x1 y2) (real_mul x2 y1))
     (real_mul (real_inv y1) (real_inv y2))"
  by (import hollight RAT_LEMMA2)

lemma RAT_LEMMA3: "real_lt (real_of_num 0) y1 & real_lt (real_of_num 0) y2
==> real_sub (real_div x1 y1) (real_div x2 y2) =
    real_mul (real_sub (real_mul x1 y2) (real_mul x2 y1))
     (real_mul (real_inv y1) (real_inv y2))"
  by (import hollight RAT_LEMMA3)

lemma RAT_LEMMA4: "real_lt (real_of_num 0) y1 & real_lt (real_of_num 0) y2
==> real_le (real_div x1 y1) (real_div x2 y2) =
    real_le (real_mul x1 y2) (real_mul x2 y1)"
  by (import hollight RAT_LEMMA4)

lemma RAT_LEMMA5: "real_lt (real_of_num 0) y1 & real_lt (real_of_num 0) y2
==> (real_div x1 y1 = real_div x2 y2) = (real_mul x1 y2 = real_mul x2 y1)"
  by (import hollight RAT_LEMMA5)

lemma REAL_INTEGRAL: "(ALL x. real_mul (real_of_num 0) x = real_of_num 0) &
(ALL x y z. (real_add x y = real_add x z) = (y = z)) &
(ALL w x y z.
    (real_add (real_mul w y) (real_mul x z) =
     real_add (real_mul w z) (real_mul x y)) =
    (w = x | y = z))"
  by (import hollight REAL_INTEGRAL)

definition
  integer :: "hollight.real => bool"  where
  "integer == %u. EX n. real_abs u = real_of_num n"

lemma DEF_integer: "integer = (%u. EX n. real_abs u = real_of_num n)"
  by (import hollight DEF_integer)

lemma is_int: "integer x = (EX n. x = real_of_num n | x = real_neg (real_of_num n))"
  by (import hollight is_int)

typedef (open) int = "Collect integer"  morphisms "real_of_int" "int_of_real"
  apply (rule light_ex_imp_nonempty[where t="Eps integer"])
  by (import hollight TYDEF_int)

syntax
  real_of_int :: _ 

syntax
  int_of_real :: _ 

lemmas "TYDEF_int_@intern" = typedef_hol2hollight 
  [where a="a :: hollight.int" and r=r ,
   OF type_definition_int]

lemma dest_int_rep: "EX n. hollight.real_of_int x = real_of_num n |
      hollight.real_of_int x = real_neg (real_of_num n)"
  by (import hollight dest_int_rep)

definition
  int_le :: "hollight.int => hollight.int => bool"  where
  "int_le == %u ua. real_le (hollight.real_of_int u) (hollight.real_of_int ua)"

lemma DEF_int_le: "int_le = (%u ua. real_le (hollight.real_of_int u) (hollight.real_of_int ua))"
  by (import hollight DEF_int_le)

definition
  int_lt :: "hollight.int => hollight.int => bool"  where
  "int_lt == %u ua. real_lt (hollight.real_of_int u) (hollight.real_of_int ua)"

lemma DEF_int_lt: "int_lt = (%u ua. real_lt (hollight.real_of_int u) (hollight.real_of_int ua))"
  by (import hollight DEF_int_lt)

definition
  int_ge :: "hollight.int => hollight.int => bool"  where
  "int_ge == %u ua. real_ge (hollight.real_of_int u) (hollight.real_of_int ua)"

lemma DEF_int_ge: "int_ge = (%u ua. real_ge (hollight.real_of_int u) (hollight.real_of_int ua))"
  by (import hollight DEF_int_ge)

definition
  int_gt :: "hollight.int => hollight.int => bool"  where
  "int_gt == %u ua. real_gt (hollight.real_of_int u) (hollight.real_of_int ua)"

lemma DEF_int_gt: "int_gt = (%u ua. real_gt (hollight.real_of_int u) (hollight.real_of_int ua))"
  by (import hollight DEF_int_gt)

definition
  int_of_num :: "nat => hollight.int"  where
  "int_of_num == %u. int_of_real (real_of_num u)"

lemma DEF_int_of_num: "int_of_num = (%u. int_of_real (real_of_num u))"
  by (import hollight DEF_int_of_num)

lemma int_of_num_th: "hollight.real_of_int (int_of_num x) = real_of_num x"
  by (import hollight int_of_num_th)

definition
  int_neg :: "hollight.int => hollight.int"  where
  "int_neg == %u. int_of_real (real_neg (hollight.real_of_int u))"

lemma DEF_int_neg: "int_neg = (%u. int_of_real (real_neg (hollight.real_of_int u)))"
  by (import hollight DEF_int_neg)

lemma int_neg_th: "hollight.real_of_int (int_neg x) = real_neg (hollight.real_of_int x)"
  by (import hollight int_neg_th)

definition
  int_add :: "hollight.int => hollight.int => hollight.int"  where
  "int_add ==
%u ua.
   int_of_real (real_add (hollight.real_of_int u) (hollight.real_of_int ua))"

lemma DEF_int_add: "int_add =
(%u ua.
    int_of_real
     (real_add (hollight.real_of_int u) (hollight.real_of_int ua)))"
  by (import hollight DEF_int_add)

lemma int_add_th: "hollight.real_of_int (int_add x xa) =
real_add (hollight.real_of_int x) (hollight.real_of_int xa)"
  by (import hollight int_add_th)

definition
  int_sub :: "hollight.int => hollight.int => hollight.int"  where
  "int_sub ==
%u ua.
   int_of_real (real_sub (hollight.real_of_int u) (hollight.real_of_int ua))"

lemma DEF_int_sub: "int_sub =
(%u ua.
    int_of_real
     (real_sub (hollight.real_of_int u) (hollight.real_of_int ua)))"
  by (import hollight DEF_int_sub)

lemma int_sub_th: "hollight.real_of_int (int_sub x xa) =
real_sub (hollight.real_of_int x) (hollight.real_of_int xa)"
  by (import hollight int_sub_th)

definition
  int_mul :: "hollight.int => hollight.int => hollight.int"  where
  "int_mul ==
%u ua.
   int_of_real (real_mul (hollight.real_of_int u) (hollight.real_of_int ua))"

lemma DEF_int_mul: "int_mul =
(%u ua.
    int_of_real
     (real_mul (hollight.real_of_int u) (hollight.real_of_int ua)))"
  by (import hollight DEF_int_mul)

lemma int_mul_th: "hollight.real_of_int (int_mul x y) =
real_mul (hollight.real_of_int x) (hollight.real_of_int y)"
  by (import hollight int_mul_th)

definition
  int_abs :: "hollight.int => hollight.int"  where
  "int_abs == %u. int_of_real (real_abs (hollight.real_of_int u))"

lemma DEF_int_abs: "int_abs = (%u. int_of_real (real_abs (hollight.real_of_int u)))"
  by (import hollight DEF_int_abs)

lemma int_abs_th: "hollight.real_of_int (int_abs x) = real_abs (hollight.real_of_int x)"
  by (import hollight int_abs_th)

definition
  int_sgn :: "hollight.int => hollight.int"  where
  "int_sgn == %u. int_of_real (real_sgn (hollight.real_of_int u))"

lemma DEF_int_sgn: "int_sgn = (%u. int_of_real (real_sgn (hollight.real_of_int u)))"
  by (import hollight DEF_int_sgn)

lemma int_sgn_th: "hollight.real_of_int (int_sgn x) = real_sgn (hollight.real_of_int x)"
  by (import hollight int_sgn_th)

definition
  int_max :: "hollight.int => hollight.int => hollight.int"  where
  "int_max ==
%u ua.
   int_of_real (real_max (hollight.real_of_int u) (hollight.real_of_int ua))"

lemma DEF_int_max: "int_max =
(%u ua.
    int_of_real
     (real_max (hollight.real_of_int u) (hollight.real_of_int ua)))"
  by (import hollight DEF_int_max)

lemma int_max_th: "hollight.real_of_int (int_max x y) =
real_max (hollight.real_of_int x) (hollight.real_of_int y)"
  by (import hollight int_max_th)

definition
  int_min :: "hollight.int => hollight.int => hollight.int"  where
  "int_min ==
%u ua.
   int_of_real (real_min (hollight.real_of_int u) (hollight.real_of_int ua))"

lemma DEF_int_min: "int_min =
(%u ua.
    int_of_real
     (real_min (hollight.real_of_int u) (hollight.real_of_int ua)))"
  by (import hollight DEF_int_min)

lemma int_min_th: "hollight.real_of_int (int_min x y) =
real_min (hollight.real_of_int x) (hollight.real_of_int y)"
  by (import hollight int_min_th)

definition
  int_pow :: "hollight.int => nat => hollight.int"  where
  "int_pow == %u ua. int_of_real (real_pow (hollight.real_of_int u) ua)"

lemma DEF_int_pow: "int_pow = (%u ua. int_of_real (real_pow (hollight.real_of_int u) ua))"
  by (import hollight DEF_int_pow)

lemma int_pow_th: "hollight.real_of_int (int_pow x xa) = real_pow (hollight.real_of_int x) xa"
  by (import hollight int_pow_th)

lemma INT_IMAGE: "(EX n. x = int_of_num n) | (EX n. x = int_neg (int_of_num n))"
  by (import hollight INT_IMAGE)

lemma INT_LT_DISCRETE: "int_lt x y = int_le (int_add x (int_of_num 1)) y"
  by (import hollight INT_LT_DISCRETE)

lemma INT_GT_DISCRETE: "int_gt x xa = int_ge x (int_add xa (int_of_num 1))"
  by (import hollight INT_GT_DISCRETE)

lemma INT_FORALL_POS: "(ALL n. P (int_of_num n)) = (ALL i. int_le (int_of_num 0) i --> P i)"
  by (import hollight INT_FORALL_POS)

lemma INT_EXISTS_POS: "(EX n. P (int_of_num n)) = (EX i. int_le (int_of_num 0) i & P i)"
  by (import hollight INT_EXISTS_POS)

lemma INT_FORALL_ABS: "(ALL n. x (int_of_num n)) = (ALL xa. x (int_abs xa))"
  by (import hollight INT_FORALL_ABS)

lemma INT_EXISTS_ABS: "(EX n. P (int_of_num n)) = (EX x. P (int_abs x))"
  by (import hollight INT_EXISTS_ABS)

lemma INT_ABS_MUL_1: "(int_abs (int_mul x y) = int_of_num 1) =
(int_abs x = int_of_num 1 & int_abs y = int_of_num 1)"
  by (import hollight INT_ABS_MUL_1)

lemma INT_WOP: "(EX x. int_le (int_of_num 0) x & P x) =
(EX x. int_le (int_of_num 0) x &
       P x & (ALL y. int_le (int_of_num 0) y & P y --> int_le x y))"
  by (import hollight INT_WOP)

lemma INT_POW: "int_pow x 0 = int_of_num 1 &
(ALL xa. int_pow x (Suc xa) = int_mul x (int_pow x xa))"
  by (import hollight INT_POW)

lemma INT_ABS: "int_abs x = (if int_le (int_of_num 0) x then x else int_neg x)"
  by (import hollight INT_ABS)

lemma INT_GE: "int_ge x xa = int_le xa x"
  by (import hollight INT_GE)

lemma INT_GT: "int_gt x xa = int_lt xa x"
  by (import hollight INT_GT)

lemma INT_LT: "int_lt x xa = (~ int_le xa x)"
  by (import hollight INT_LT)

lemma INT_ARCH: "d ~= int_of_num 0 ==> EX c. int_lt x (int_mul c d)"
  by (import hollight INT_ARCH)

lemma INT_DIVMOD_EXIST_0: "EX x xa.
   if n = int_of_num 0 then x = int_of_num 0 & xa = m
   else int_le (int_of_num 0) xa &
        int_lt xa (int_abs n) & m = int_add (int_mul x n) xa"
  by (import hollight INT_DIVMOD_EXIST_0)

consts
  div :: "hollight.int => hollight.int => hollight.int" ("div")

defs
  div_def: "div ==
SOME q.
   EX r. ALL m n.
            if n = int_of_num 0 then q m n = int_of_num 0 & r m n = m
            else int_le (int_of_num 0) (r m n) &
                 int_lt (r m n) (int_abs n) &
                 m = int_add (int_mul (q m n) n) (r m n)"

lemma DEF_div: "div =
(SOME q.
    EX r. ALL m n.
             if n = int_of_num 0 then q m n = int_of_num 0 & r m n = m
             else int_le (int_of_num 0) (r m n) &
                  int_lt (r m n) (int_abs n) &
                  m = int_add (int_mul (q m n) n) (r m n))"
  by (import hollight DEF_div)

definition
  rem :: "hollight.int => hollight.int => hollight.int"  where
  "rem ==
SOME r.
   ALL m n.
      if n = int_of_num 0 then div m n = int_of_num 0 & r m n = m
      else int_le (int_of_num 0) (r m n) &
           int_lt (r m n) (int_abs n) &
           m = int_add (int_mul (div m n) n) (r m n)"

lemma DEF_rem: "rem =
(SOME r.
    ALL m n.
       if n = int_of_num 0 then div m n = int_of_num 0 & r m n = m
       else int_le (int_of_num 0) (r m n) &
            int_lt (r m n) (int_abs n) &
            m = int_add (int_mul (div m n) n) (r m n))"
  by (import hollight DEF_rem)

lemma INT_DIVISION: "n ~= int_of_num 0
==> m = int_add (int_mul (div m n) n) (rem m n) &
    int_le (int_of_num 0) (rem m n) & int_lt (rem m n) (int_abs n)"
  by (import hollight INT_DIVISION)

lemma sth: "(ALL x y z. int_add x (int_add y z) = int_add (int_add x y) z) &
(ALL x y. int_add x y = int_add y x) &
(ALL x. int_add (int_of_num 0) x = x) &
(ALL x y z. int_mul x (int_mul y z) = int_mul (int_mul x y) z) &
(ALL x y. int_mul x y = int_mul y x) &
(ALL x. int_mul (int_of_num 1) x = x) &
(ALL x. int_mul (int_of_num 0) x = int_of_num 0) &
(ALL x y z. int_mul x (int_add y z) = int_add (int_mul x y) (int_mul x z)) &
(ALL x. int_pow x 0 = int_of_num 1) &
(ALL x xa. int_pow x (Suc xa) = int_mul x (int_pow x xa))"
  by (import hollight sth)

lemma INT_INTEGRAL: "(ALL x. int_mul (int_of_num 0) x = int_of_num 0) &
(ALL x y z. (int_add x y = int_add x z) = (y = z)) &
(ALL w x y z.
    (int_add (int_mul w y) (int_mul x z) =
     int_add (int_mul w z) (int_mul x y)) =
    (w = x | y = z))"
  by (import hollight INT_INTEGRAL)

lemma INT_DIVMOD_UNIQ: "m = int_add (int_mul q n) r & int_le (int_of_num 0) r & int_lt r (int_abs n)
==> div m n = q & rem m n = r"
  by (import hollight INT_DIVMOD_UNIQ)

consts
  eqeq :: "'A => 'A => ('A => 'A => bool) => bool" 

defs
  eqeq_def: "hollight.eqeq == %(u::'A) (ua::'A) ub::'A => 'A => bool. ub u ua"

lemma DEF__equal__equal_: "hollight.eqeq = (%(u::'A) (ua::'A) ub::'A => 'A => bool. ub u ua)"
  by (import hollight DEF__equal__equal_)

definition
  real_mod :: "hollight.real => hollight.real => hollight.real => bool"  where
  "real_mod == %u ua ub. EX q. integer q & real_sub ua ub = real_mul q u"

lemma DEF_real_mod: "real_mod = (%u ua ub. EX q. integer q & real_sub ua ub = real_mul q u)"
  by (import hollight DEF_real_mod)

definition
  int_divides :: "hollight.int => hollight.int => bool"  where
  "int_divides == %u ua. EX x. ua = int_mul u x"

lemma DEF_int_divides: "int_divides = (%u ua. EX x. ua = int_mul u x)"
  by (import hollight DEF_int_divides)

consts
  int_mod :: "hollight.int => hollight.int => hollight.int => bool" 

defs
  int_mod_def: "hollight.int_mod == %u ua ub. int_divides u (int_sub ua ub)"

lemma DEF_int_mod: "hollight.int_mod = (%u ua ub. int_divides u (int_sub ua ub))"
  by (import hollight DEF_int_mod)

lemma int_congruent: "hollight.eqeq x xa (hollight.int_mod xb) =
(EX d. int_sub x xa = int_mul xb d)"
  by (import hollight int_congruent)

consts
  int_coprime :: "hollight.int * hollight.int => bool" 

defs
  int_coprime_def: "hollight.int_coprime ==
%u. EX x y. int_add (int_mul (fst u) x) (int_mul (snd u) y) = int_of_num 1"

lemma DEF_int_coprime: "hollight.int_coprime =
(%u. EX x y. int_add (int_mul (fst u) x) (int_mul (snd u) y) = int_of_num 1)"
  by (import hollight DEF_int_coprime)

lemma FORALL_UNCURRY: "All (P::('A => 'B => 'C) => bool) =
(ALL f::'A * 'B => 'C. P (%(a::'A) b::'B. f (a, b)))"
  by (import hollight FORALL_UNCURRY)

lemma EXISTS_UNCURRY: "Ex (x::('A => 'B => 'C) => bool) =
(EX f::'A * 'B => 'C. x (%(a::'A) b::'B. f (a, b)))"
  by (import hollight EXISTS_UNCURRY)

lemma WF_INT_MEASURE: "(ALL x::'A. int_le (int_of_num (0::nat)) ((m::'A => hollight.int) x)) &
(ALL x::'A. (ALL y::'A. int_lt (m y) (m x) --> (P::'A => bool) y) --> P x)
==> P (x::'A)"
  by (import hollight WF_INT_MEASURE)

lemma WF_INT_MEASURE_2: "(ALL (x::'A) y::'B.
    int_le (int_of_num (0::nat)) ((m::'A => 'B => hollight.int) x y)) &
(ALL (x::'A) y::'B.
    (ALL (x'::'A) y'::'B.
        int_lt (m x' y') (m x y) --> (P::'A => 'B => bool) x' y') -->
    P x y)
==> P (x::'A) (xa::'B)"
  by (import hollight WF_INT_MEASURE_2)

lemma INT_GCD_EXISTS: "EX d. int_divides d a &
      int_divides d b & (EX x y. d = int_add (int_mul a x) (int_mul b y))"
  by (import hollight INT_GCD_EXISTS)

lemma INT_GCD_EXISTS_POS: "EX d. int_le (int_of_num 0) d &
      int_divides d a &
      int_divides d b & (EX x y. d = int_add (int_mul a x) (int_mul b y))"
  by (import hollight INT_GCD_EXISTS_POS)

consts
  int_gcd :: "hollight.int * hollight.int => hollight.int" 

defs
  int_gcd_def: "hollight.int_gcd ==
SOME d.
   ALL a b.
      int_le (int_of_num 0) (d (a, b)) &
      int_divides (d (a, b)) a &
      int_divides (d (a, b)) b &
      (EX x y. d (a, b) = int_add (int_mul a x) (int_mul b y))"

lemma DEF_int_gcd: "hollight.int_gcd =
(SOME d.
    ALL a b.
       int_le (int_of_num 0) (d (a, b)) &
       int_divides (d (a, b)) a &
       int_divides (d (a, b)) b &
       (EX x y. d (a, b) = int_add (int_mul a x) (int_mul b y)))"
  by (import hollight DEF_int_gcd)

definition
  num_of_int :: "hollight.int => nat"  where
  "num_of_int == %u. SOME n. int_of_num n = u"

lemma DEF_num_of_int: "num_of_int = (%u. SOME n. int_of_num n = u)"
  by (import hollight DEF_num_of_int)

lemma NUM_OF_INT_OF_NUM: "num_of_int (int_of_num x) = x"
  by (import hollight NUM_OF_INT_OF_NUM)

lemma INT_OF_NUM_OF_INT: "int_le (int_of_num 0) x ==> int_of_num (num_of_int x) = x"
  by (import hollight INT_OF_NUM_OF_INT)

lemma NUM_OF_INT: "int_le (int_of_num 0) x = (int_of_num (num_of_int x) = x)"
  by (import hollight NUM_OF_INT)

definition
  num_divides :: "nat => nat => bool"  where
  "num_divides == %u ua. int_divides (int_of_num u) (int_of_num ua)"

lemma DEF_num_divides: "num_divides = (%u ua. int_divides (int_of_num u) (int_of_num ua))"
  by (import hollight DEF_num_divides)

definition
  num_mod :: "nat => nat => nat => bool"  where
  "num_mod ==
%u ua ub. hollight.int_mod (int_of_num u) (int_of_num ua) (int_of_num ub)"

lemma DEF_num_mod: "num_mod =
(%u ua ub. hollight.int_mod (int_of_num u) (int_of_num ua) (int_of_num ub))"
  by (import hollight DEF_num_mod)

lemma num_congruent: "hollight.eqeq x xa (num_mod xb) =
hollight.eqeq (int_of_num x) (int_of_num xa)
 (hollight.int_mod (int_of_num xb))"
  by (import hollight num_congruent)

definition
  num_coprime :: "nat * nat => bool"  where
  "num_coprime ==
%u. hollight.int_coprime (int_of_num (fst u), int_of_num (snd u))"

lemma DEF_num_coprime: "num_coprime =
(%u. hollight.int_coprime (int_of_num (fst u), int_of_num (snd u)))"
  by (import hollight DEF_num_coprime)

definition
  num_gcd :: "nat * nat => nat"  where
  "num_gcd ==
%u. num_of_int (hollight.int_gcd (int_of_num (fst u), int_of_num (snd u)))"

lemma DEF_num_gcd: "num_gcd =
(%u. num_of_int (hollight.int_gcd (int_of_num (fst u), int_of_num (snd u))))"
  by (import hollight DEF_num_gcd)

lemma NUM_GCD: "int_of_num (num_gcd (x, xa)) =
hollight.int_gcd (int_of_num x, int_of_num xa)"
  by (import hollight NUM_GCD)

lemma IN_ELIM_THM: "(ALL (P::(bool => 'q_43295 => bool) => bool) x::'q_43295.
    (x : {v::'q_43295. P (SETSPEC v)}) =
    P (%(p::bool) t::'q_43295. p & x = t)) &
(ALL (p::'q_43326 => bool) x::'q_43326.
    (x : {v::'q_43326. EX y::'q_43326. p y & v = y}) = p x) &
(ALL (P::(bool => 'q_43354 => bool) => bool) x::'q_43354.
    x \<in> {v::'q_43354. P (SETSPEC v)} =
    P (%(p::bool) t::'q_43354. p & x = t)) &
(ALL (p::'q_43383 => bool) x::'q_43383.
    x \<in> {v::'q_43383. EX y::'q_43383. p y & v = y} = p x) &
(ALL (p::'q_43400 => bool) x::'q_43400. p x \<longleftrightarrow> p x)"
  by (import hollight IN_ELIM_THM)

lemma INSERT: "insert (x::'A) (s::'A set) = {u::'A. EX y::'A. (y : s | y = x) & u = y}"
  by (import hollight INSERT)

definition
  SING :: "('A set) => bool"  where
  "SING == %u::'A set. EX x::'A. u = {x}"

lemma DEF_SING: "SING = (%u::'A set. EX x::'A. u = {x})"
  by (import hollight DEF_SING)

definition
  INJ :: "('A => 'B) => ('A => bool) => ('B => bool) => bool"  where
  "INJ ==
%(u::'A => 'B) (ua::'A => bool) ub::'B => bool.
   (ALL x::'A. x : ua --> u x : ub) &
   (ALL (x::'A) y::'A. x : ua & y : ua & u x = u y --> x = y)"

lemma DEF_INJ: "INJ =
(%(u::'A => 'B) (ua::'A => bool) ub::'B => bool.
    (ALL x::'A. x : ua --> u x : ub) &
    (ALL (x::'A) y::'A. x : ua & y : ua & u x = u y --> x = y))"
  by (import hollight DEF_INJ)

definition
  SURJ :: "('A => 'B) => ('A => bool) => ('B => bool) => bool"  where
  "SURJ ==
%(u::'A => 'B) (ua::'A => bool) ub::'B => bool.
   (ALL x::'A. x : ua --> u x : ub) &
   (ALL x::'B. x : ub --> (EX y::'A. y : ua & u y = x))"

lemma DEF_SURJ: "SURJ =
(%(u::'A => 'B) (ua::'A => bool) ub::'B => bool.
    (ALL x::'A. x : ua --> u x : ub) &
    (ALL x::'B. x : ub --> (EX y::'A. y : ua & u y = x)))"
  by (import hollight DEF_SURJ)

definition
  BIJ :: "('A => 'B) => ('A => bool) => ('B => bool) => bool"  where
  "BIJ ==
%(u::'A => 'B) (ua::'A => bool) ub::'B => bool. INJ u ua ub & SURJ u ua ub"

lemma DEF_BIJ: "BIJ =
(%(u::'A => 'B) (ua::'A => bool) ub::'B => bool. INJ u ua ub & SURJ u ua ub)"
  by (import hollight DEF_BIJ)

definition
  REST :: "('A => bool) => 'A => bool"  where
  "REST == %u::'A => bool. u - {Eps u}"

lemma DEF_REST: "REST = (%u::'A => bool. u - {Eps u})"
  by (import hollight DEF_REST)

lemma NOT_IN_EMPTY: "(x::'A) ~: {}"
  by (import hollight NOT_IN_EMPTY)

lemma IN_UNIONS: "((xa::'A) : Union (x::('A => bool) => bool)) =
(EX t::'A => bool. t : x & xa : t)"
  by (import hollight IN_UNIONS)

lemma IN_INTERS: "((xa::'A) : Inter (x::('A => bool) => bool)) =
(ALL t::'A => bool. t : x --> xa : t)"
  by (import hollight IN_INTERS)

lemma IN_DELETE: "((xa::'A) : (x::'A => bool) - {xb::'A}) = (xa : x & xa ~= xb)"
  by (import hollight IN_DELETE)

lemma IN_IMAGE: "((x::'B) : (xb::'A => 'B) ` (xa::'A => bool)) =
(EX xc::'A. x = xb xc & xc : xa)"
  by (import hollight IN_IMAGE)

lemma IN_REST: "((x::'A) : REST (xa::'A => bool)) = (x : xa & x ~= Eps xa)"
  by (import hollight IN_REST)

lemma FORALL_IN_INSERT: "(ALL xc::'q_44214.
    xc : insert (xa::'q_44214) (xb::'q_44214 => bool) -->
    (x::'q_44214 => bool) xc) =
(x xa & (ALL xa::'q_44214. xa : xb --> x xa))"
  by (import hollight FORALL_IN_INSERT)

lemma EXISTS_IN_INSERT: "(EX xc::'q_44255.
    xc : insert (xa::'q_44255) (xb::'q_44255 => bool) &
    (x::'q_44255 => bool) xc) =
(x xa | (EX xa::'q_44255. xa : xb & x xa))"
  by (import hollight EXISTS_IN_INSERT)

lemma CHOICE_DEF: "(x::'A => bool) ~= {} ==> Eps x : x"
  by (import hollight CHOICE_DEF)

lemma NOT_EQUAL_SETS: "((x::'A => bool) ~= (xa::'A => bool)) = (EX xb::'A. (xb : xa) = (xb ~: x))"
  by (import hollight NOT_EQUAL_SETS)

lemma EMPTY_NOT_UNIV: "(op ~=::('A::type => bool) => ('A::type => bool) => bool)
 ({}::'A::type => bool) (UNIV::'A::type => bool)"
  by (import hollight EMPTY_NOT_UNIV)

lemma EQ_UNIV: "(ALL x::'A. x : (s::'A => bool)) = (s = UNIV)"
  by (import hollight EQ_UNIV)

lemma SING_SUBSET: "({xa::'q_44493} <= (x::'q_44493 => bool)) = (xa : x)"
  by (import hollight SING_SUBSET)

lemma PSUBSET_UNIV: "((x::'A => bool) < UNIV) = (EX xa::'A. xa ~: x)"
  by (import hollight PSUBSET_UNIV)

lemma PSUBSET_ALT: "((x::'A => bool) < (xa::'A => bool)) =
(x <= xa & (EX a::'A. a : xa & a ~: x))"
  by (import hollight PSUBSET_ALT)

lemma SUBSET_UNION: "(ALL (x::'A => bool) xa::'A => bool. x <= x Un xa) &
(ALL (x::'A => bool) xa::'A => bool. x <= xa Un x)"
  by (import hollight SUBSET_UNION)

lemma UNION_EMPTY: "(ALL x::'A => bool. {} Un x = x) & (ALL x::'A => bool. x Un {} = x)"
  by (import hollight UNION_EMPTY)

lemma UNION_UNIV: "(ALL x::'A => bool. UNIV Un x = UNIV) &
(ALL x::'A => bool. x Un UNIV = UNIV)"
  by (import hollight UNION_UNIV)

lemma INTER_SUBSET: "(ALL (x::'A => bool) xa::'A => bool. x Int xa <= x) &
(ALL (x::'A => bool) xa::'A => bool. xa Int x <= x)"
  by (import hollight INTER_SUBSET)

lemma INTER_EMPTY: "(ALL x::'A => bool. {} Int x = {}) & (ALL x::'A => bool. x Int {} = {})"
  by (import hollight INTER_EMPTY)

lemma INTER_UNIV: "(ALL x::'A => bool. UNIV Int x = x) & (ALL x::'A => bool. x Int UNIV = x)"
  by (import hollight INTER_UNIV)

lemma IN_DISJOINT: "((x::'A => bool) Int (xa::'A => bool) = {}) =
(~ (EX xb::'A. xb : x & xb : xa))"
  by (import hollight IN_DISJOINT)

lemma DISJOINT_SYM: "((x::'A => bool) Int (xa::'A => bool) = {}) = (xa Int x = {})"
  by (import hollight DISJOINT_SYM)

lemma DISJOINT_EMPTY: "{} Int (x::'A => bool) = {} & x Int {} = {}"
  by (import hollight DISJOINT_EMPTY)

lemma DISJOINT_EMPTY_REFL: "((x::'A => bool) = {}) = (x Int x = {})"
  by (import hollight DISJOINT_EMPTY_REFL)

lemma DISJOINT_UNION: "(((x::'A => bool) Un (xa::'A => bool)) Int (xb::'A => bool) = {}) =
(x Int xb = {} & xa Int xb = {})"
  by (import hollight DISJOINT_UNION)

lemma DECOMPOSITION: "((x::'A) : (s::'A => bool)) = (EX t::'A => bool. s = insert x t & x ~: t)"
  by (import hollight DECOMPOSITION)

lemma SET_CASES: "(s::'A => bool) = {} | (EX (x::'A) t::'A => bool. s = insert x t & x ~: t)"
  by (import hollight SET_CASES)

lemma ABSORPTION: "((x::'A) : (xa::'A => bool)) = (insert x xa = xa)"
  by (import hollight ABSORPTION)

lemma INSERT_UNIV: "insert (x::'A) UNIV = UNIV"
  by (import hollight INSERT_UNIV)

lemma INSERT_UNION: "insert (x::'A) (s::'A => bool) Un (t::'A => bool) =
(if x : t then s Un t else insert x (s Un t))"
  by (import hollight INSERT_UNION)

lemma DISJOINT_INSERT: "(insert (x::'A) (xa::'A => bool) Int (xb::'A => bool) = {}) =
(xa Int xb = {} & x ~: xb)"
  by (import hollight DISJOINT_INSERT)

lemma INSERT_AC: "insert (x::'q_45764) (insert (y::'q_45764) (s::'q_45764 => bool)) =
insert y (insert x s) &
insert x (insert x s) = insert x s"
  by (import hollight INSERT_AC)

lemma INTER_ACI: "(p::'q_45831 => bool) Int (q::'q_45831 => bool) = q Int p &
p Int q Int (r::'q_45831 => bool) = p Int (q Int r) &
p Int (q Int r) = q Int (p Int r) & p Int p = p & p Int (p Int q) = p Int q"
  by (import hollight INTER_ACI)

lemma UNION_ACI: "(p::'q_45897 => bool) Un (q::'q_45897 => bool) = q Un p &
p Un q Un (r::'q_45897 => bool) = p Un (q Un r) &
p Un (q Un r) = q Un (p Un r) & p Un p = p & p Un (p Un q) = p Un q"
  by (import hollight UNION_ACI)

lemma DELETE_NON_ELEMENT: "((x::'A) ~: (xa::'A => bool)) = (xa - {x} = xa)"
  by (import hollight DELETE_NON_ELEMENT)

lemma IN_DELETE_EQ: "(((x::'A) : (s::'A => bool)) = ((x'::'A) : s)) =
((x : s - {x'}) = (x' : s - {x}))"
  by (import hollight IN_DELETE_EQ)

lemma EMPTY_DELETE: "{} - {x::'A} = {}"
  by (import hollight EMPTY_DELETE)

lemma DELETE_DELETE: "(xa::'A => bool) - {x::'A} - {x} = xa - {x}"
  by (import hollight DELETE_DELETE)

lemma DELETE_COMM: "(xb::'A => bool) - {x::'A} - {xa::'A} = xb - {xa} - {x}"
  by (import hollight DELETE_COMM)

lemma DELETE_SUBSET: "(xa::'A => bool) - {x::'A} <= xa"
  by (import hollight DELETE_SUBSET)

lemma SUBSET_DELETE: "((xa::'A => bool) <= (xb::'A => bool) - {x::'A}) = (x ~: xa & xa <= xb)"
  by (import hollight SUBSET_DELETE)

lemma SUBSET_INSERT_DELETE: "((xa::'A => bool) <= insert (x::'A) (xb::'A => bool)) = (xa - {x} <= xb)"
  by (import hollight SUBSET_INSERT_DELETE)

lemma PSUBSET_INSERT_SUBSET: "((x::'A => bool) < (xa::'A => bool)) =
(EX xb::'A. xb ~: x & insert xb x <= xa)"
  by (import hollight PSUBSET_INSERT_SUBSET)

lemma PSUBSET_MEMBER: "((x::'A => bool) < (xa::'A => bool)) =
(x <= xa & (EX y::'A. y : xa & y ~: x))"
  by (import hollight PSUBSET_MEMBER)

lemma DELETE_INSERT: "insert (x::'A) (s::'A => bool) - {y::'A} =
(if x = y then s - {y} else insert x (s - {y}))"
  by (import hollight DELETE_INSERT)

lemma DELETE_INTER: "((x::'A => bool) - {xb::'A}) Int (xa::'A => bool) = x Int xa - {xb}"
  by (import hollight DELETE_INTER)

lemma DISJOINT_DELETE_SYM: "(((x::'A => bool) - {xb::'A}) Int (xa::'A => bool) = {}) =
((xa - {xb}) Int x = {})"
  by (import hollight DISJOINT_DELETE_SYM)

lemma FORALL_IN_UNIONS: "(ALL x::'q_46386.
    x : Union (s::('q_46386 => bool) => bool) --> (P::'q_46386 => bool) x) =
(ALL (t::'q_46386 => bool) x::'q_46386. t : s & x : t --> P x)"
  by (import hollight FORALL_IN_UNIONS)

lemma EXISTS_IN_UNIONS: "(EX x::'q_46428.
    x : Union (s::('q_46428 => bool) => bool) & (P::'q_46428 => bool) x) =
(EX (t::'q_46428 => bool) x::'q_46428. t : s & x : t & P x)"
  by (import hollight EXISTS_IN_UNIONS)

lemma EMPTY_UNIONS: "(Union (x::('q_46454 => bool) => bool) = {}) =
(ALL xa::'q_46454 => bool. xa : x --> xa = {})"
  by (import hollight EMPTY_UNIONS)

lemma INTER_UNIONS: "(ALL (x::('q_46493 => bool) => bool) xa::'q_46493 => bool.
    Union x Int xa =
    Union
     {u::'q_46493 => bool.
      EX xb::'q_46493 => bool. xb : x & u = xb Int xa}) &
(ALL (x::('q_46529 => bool) => bool) xa::'q_46529 => bool.
    xa Int Union x =
    Union
     {u::'q_46529 => bool. EX xb::'q_46529 => bool. xb : x & u = xa Int xb})"
  by (import hollight INTER_UNIONS)

lemma UNIONS_SUBSET: "(Union (x::('q_46545 => bool) => bool) <= (xa::'q_46545 => bool)) =
(ALL xb::'q_46545 => bool. xb : x --> xb <= xa)"
  by (import hollight UNIONS_SUBSET)

lemma IMAGE_CLAUSES: "(f::'q_46676 => 'q_46680) ` {} = {} &
f ` insert (x::'q_46676) (s::'q_46676 => bool) = insert (f x) (f ` s)"
  by (import hollight IMAGE_CLAUSES)

lemma IMAGE_INTER_INJ: "(!!(xa::'q_46846) y::'q_46846.
    (x::'q_46846 => 'q_46857) xa = x y ==> xa = y)
==> x ` ((xa::'q_46846 => bool) Int (xb::'q_46846 => bool)) =
    x ` xa Int x ` xb"
  by (import hollight IMAGE_INTER_INJ)

lemma IMAGE_DIFF_INJ: "(!!(xa::'q_46900) y::'q_46900.
    (x::'q_46900 => 'q_46911) xa = x y ==> xa = y)
==> x ` ((xa::'q_46900 => bool) - (xb::'q_46900 => bool)) = x ` xa - x ` xb"
  by (import hollight IMAGE_DIFF_INJ)

lemma IMAGE_DELETE_INJ: "(!!xa::'q_46958.
    (x::'q_46958 => 'q_46957) xa = x (xb::'q_46958) ==> xa = xb)
==> x ` ((xa::'q_46958 => bool) - {xb}) = x ` xa - {x xb}"
  by (import hollight IMAGE_DELETE_INJ)

lemma FORALL_IN_IMAGE: "(ALL xb::'q_47016.
    xb : (x::'q_47017 => 'q_47016) ` (xa::'q_47017 => bool) -->
    (P::'q_47016 => bool) xb) =
(ALL xb::'q_47017. xb : xa --> P (x xb))"
  by (import hollight FORALL_IN_IMAGE)

lemma EXISTS_IN_IMAGE: "(EX xb::'q_47052.
    xb : (x::'q_47053 => 'q_47052) ` (xa::'q_47053 => bool) &
    (P::'q_47052 => bool) xb) =
(EX xb::'q_47053. xb : xa & P (x xb))"
  by (import hollight EXISTS_IN_IMAGE)

lemma FORALL_SUBSET_IMAGE: "(ALL xc<=(xa::'q_47140 => 'q_47156) ` (xb::'q_47140 => bool).
    (x::('q_47156 => bool) => bool) xc) =
(ALL t<=xb. x (xa ` t))"
  by (import hollight FORALL_SUBSET_IMAGE)

lemma EXISTS_SUBSET_IMAGE: "(EX xc<=(xa::'q_47183 => 'q_47199) ` (xb::'q_47183 => bool).
    (x::('q_47199 => bool) => bool) xc) =
(EX t<=xb. x (xa ` t))"
  by (import hollight EXISTS_SUBSET_IMAGE)

lemma SIMPLE_IMAGE: "{u::'q_47262.
 EX xb::'q_47258.
    xb : (xa::'q_47258 => bool) & u = (x::'q_47258 => 'q_47262) xb} =
x ` xa"
  by (import hollight SIMPLE_IMAGE)

lemma SIMPLE_IMAGE_GEN: "{u::'q_47292.
 EX xa::'q_47305.
    (P::'q_47305 => bool) xa & u = (x::'q_47305 => 'q_47292) xa} =
x ` {u::'q_47305. EX x::'q_47305. P x & u = x}"
  by (import hollight SIMPLE_IMAGE_GEN)

lemma IMAGE_UNIONS: "(x::'q_47323 => 'q_47332) ` Union (xa::('q_47323 => bool) => bool) =
Union (op ` x ` xa)"
  by (import hollight IMAGE_UNIONS)

lemma SURJECTIVE_IMAGE_EQ: "(ALL y::'q_47396.
    y : (xa::'q_47396 => bool) -->
    (EX x::'q_47400. (f::'q_47400 => 'q_47396) x = y)) &
(ALL xb::'q_47400. (f xb : xa) = (xb : (x::'q_47400 => bool)))
==> f ` x = xa"
  by (import hollight SURJECTIVE_IMAGE_EQ)

lemma EMPTY_GSPEC: "{u::'q_47425. Ex (SETSPEC u False)} = {}"
  by (import hollight EMPTY_GSPEC)

lemma SING_GSPEC: "(ALL x::'q_47454. {u::'q_47454. EX xa::'q_47454. xa = x & u = xa} = {x}) &
(ALL x::'q_47480. {u::'q_47480. EX xa::'q_47480. x = xa & u = xa} = {x})"
  by (import hollight SING_GSPEC)

lemma IN_ELIM_PAIR_THM: "((xa::'q_47526, xb::'q_47525)
 : {xa::'q_47526 * 'q_47525.
    EX (xb::'q_47526) y::'q_47525.
       (x::'q_47526 => 'q_47525 => bool) xb y & xa = (xb, y)}) =
x xa xb"
  by (import hollight IN_ELIM_PAIR_THM)

lemma SET_PAIR_THM: "{u::'q_47570 * 'q_47569.
 EX p::'q_47570 * 'q_47569. (x::'q_47570 * 'q_47569 => bool) p & u = p} =
{u::'q_47570 * 'q_47569.
 EX (a::'q_47570) b::'q_47569. x (a, b) & u = (a, b)}"
  by (import hollight SET_PAIR_THM)

lemma FORALL_IN_GSPEC: "(ALL (P::'q_47618 => bool) f::'q_47618 => 'q_47739.
    (ALL z::'q_47739.
        z : {u::'q_47739. EX x::'q_47618. P x & u = f x} -->
        (Q::'q_47739 => bool) z) =
    (ALL x::'q_47618. P x --> Q (f x))) &
(ALL (P::'q_47675 => 'q_47674 => bool) f::'q_47675 => 'q_47674 => 'q_47739.
    (ALL z::'q_47739.
        z : {u::'q_47739.
             EX (x::'q_47675) y::'q_47674. P x y & u = f x y} -->
        Q z) =
    (ALL (x::'q_47675) y::'q_47674. P x y --> Q (f x y))) &
(ALL (P::'q_47742 => 'q_47741 => 'q_47740 => bool)
    f::'q_47742 => 'q_47741 => 'q_47740 => 'q_47739.
    (ALL z::'q_47739.
        z : {u::'q_47739.
             EX (w::'q_47742) (x::'q_47741) y::'q_47740.
                P w x y & u = f w x y} -->
        Q z) =
    (ALL (w::'q_47742) (x::'q_47741) y::'q_47740. P w x y --> Q (f w x y)))"
  by (import hollight FORALL_IN_GSPEC)

lemma EXISTS_IN_GSPEC: "(ALL (P::'q_47788 => bool) f::'q_47788 => 'q_47909.
    (EX z::'q_47909.
        z : {u::'q_47909. EX x::'q_47788. P x & u = f x} &
        (Q::'q_47909 => bool) z) =
    (EX x::'q_47788. P x & Q (f x))) &
(ALL (P::'q_47845 => 'q_47844 => bool) f::'q_47845 => 'q_47844 => 'q_47909.
    (EX z::'q_47909.
        z : {u::'q_47909. EX (x::'q_47845) y::'q_47844. P x y & u = f x y} &
        Q z) =
    (EX (x::'q_47845) y::'q_47844. P x y & Q (f x y))) &
(ALL (P::'q_47912 => 'q_47911 => 'q_47910 => bool)
    f::'q_47912 => 'q_47911 => 'q_47910 => 'q_47909.
    (EX z::'q_47909.
        z : {u::'q_47909.
             EX (w::'q_47912) (x::'q_47911) y::'q_47910.
                P w x y & u = f w x y} &
        Q z) =
    (EX (w::'q_47912) (x::'q_47911) y::'q_47910. P w x y & Q (f w x y)))"
  by (import hollight EXISTS_IN_GSPEC)

lemma SET_PROVE_CASES: "(P::('A => bool) => bool) {} &
(ALL (a::'A) s::'A => bool. a ~: s --> P (insert a s))
==> P (x::'A => bool)"
  by (import hollight SET_PROVE_CASES)

lemma UNIONS_IMAGE: "Union ((f::'q_47989 => 'q_47973 => bool) ` (s::'q_47989 => bool)) =
{u::'q_47973. EX y::'q_47973. (EX x::'q_47989. x : s & y : f x) & u = y}"
  by (import hollight UNIONS_IMAGE)

lemma INTERS_IMAGE: "Inter ((f::'q_48032 => 'q_48016 => bool) ` (s::'q_48032 => bool)) =
{u::'q_48016. EX y::'q_48016. (ALL x::'q_48032. x : s --> y : f x) & u = y}"
  by (import hollight INTERS_IMAGE)

lemma UNIONS_GSPEC: "(ALL (P::'q_48085 => bool) f::'q_48085 => 'q_48071 => bool.
    Union {u::'q_48071 => bool. EX x::'q_48085. P x & u = f x} =
    {u::'q_48071.
     EX a::'q_48071. (EX x::'q_48085. P x & a : f x) & u = a}) &
(ALL (P::'q_48149 => 'q_48148 => bool)
    f::'q_48149 => 'q_48148 => 'q_48129 => bool.
    Union
     {u::'q_48129 => bool.
      EX (x::'q_48149) y::'q_48148. P x y & u = f x y} =
    {u::'q_48129.
     EX a::'q_48129.
        (EX (x::'q_48149) y::'q_48148. P x y & a : f x y) & u = a}) &
(ALL (P::'q_48223 => 'q_48222 => 'q_48221 => bool)
    f::'q_48223 => 'q_48222 => 'q_48221 => 'q_48197 => bool.
    Union
     {u::'q_48197 => bool.
      EX (x::'q_48223) (y::'q_48222) z::'q_48221. P x y z & u = f x y z} =
    {u::'q_48197.
     EX a::'q_48197.
        (EX (x::'q_48223) (y::'q_48222) z::'q_48221.
            P x y z & a : f x y z) &
        u = a})"
  by (import hollight UNIONS_GSPEC)

lemma INTERS_GSPEC: "(ALL (P::'q_48276 => bool) f::'q_48276 => 'q_48262 => bool.
    Inter {u::'q_48262 => bool. EX x::'q_48276. P x & u = f x} =
    {u::'q_48262.
     EX a::'q_48262. (ALL x::'q_48276. P x --> a : f x) & u = a}) &
(ALL (P::'q_48340 => 'q_48339 => bool)
    f::'q_48340 => 'q_48339 => 'q_48320 => bool.
    Inter
     {u::'q_48320 => bool.
      EX (x::'q_48340) y::'q_48339. P x y & u = f x y} =
    {u::'q_48320.
     EX a::'q_48320.
        (ALL (x::'q_48340) y::'q_48339. P x y --> a : f x y) & u = a}) &
(ALL (P::'q_48414 => 'q_48413 => 'q_48412 => bool)
    f::'q_48414 => 'q_48413 => 'q_48412 => 'q_48388 => bool.
    Inter
     {u::'q_48388 => bool.
      EX (x::'q_48414) (y::'q_48413) z::'q_48412. P x y z & u = f x y z} =
    {u::'q_48388.
     EX a::'q_48388.
        (ALL (x::'q_48414) (y::'q_48413) z::'q_48412.
            P x y z --> a : f x y z) &
        u = a})"
  by (import hollight INTERS_GSPEC)

lemma DIFF_INTERS: "(x::'q_48451 => bool) - Inter (xa::('q_48451 => bool) => bool) =
Union {u::'q_48451 => bool. EX xb::'q_48451 => bool. xb : xa & u = x - xb}"
  by (import hollight DIFF_INTERS)

lemma INTERS_UNIONS: "Inter (x::('q_48486 => bool) => bool) =
UNIV -
Union {u::'q_48486 => bool. EX t::'q_48486 => bool. t : x & u = UNIV - t}"
  by (import hollight INTERS_UNIONS)

lemma UNIONS_INTERS: "Union (s::('q_48521 => bool) => bool) =
UNIV -
Inter {u::'q_48521 => bool. EX t::'q_48521 => bool. t : s & u = UNIV - t}"
  by (import hollight UNIONS_INTERS)

lemma FINITE_SING: "finite {x::'q_48799}"
  by (import hollight FINITE_SING)

lemma FINITE_DELETE_IMP: "finite (s::'A => bool) ==> finite (s - {x::'A})"
  by (import hollight FINITE_DELETE_IMP)

lemma FINITE_DELETE: "finite ((s::'A => bool) - {x::'A}) = finite s"
  by (import hollight FINITE_DELETE)

lemma FINITE_FINITE_UNIONS: "finite (s::('q_48871 => bool) => bool)
==> finite (Union s) = (ALL t::'q_48871 => bool. t : s --> finite t)"
  by (import hollight FINITE_FINITE_UNIONS)

lemma FINITE_IMAGE_EXPAND: "finite (s::'A => bool)
==> finite
     {u::'B. EX y::'B. (EX x::'A. x : s & y = (f::'A => 'B) x) & u = y}"
  by (import hollight FINITE_IMAGE_EXPAND)

lemma FINITE_IMAGE_INJ_GENERAL: "(ALL (x::'A) y::'A.
    x : (s::'A => bool) & y : s & (f::'A => 'B) x = f y --> x = y) &
finite (x::'B => bool)
==> finite {u::'A. EX xa::'A. (xa : s & f xa : x) & u = xa}"
  by (import hollight FINITE_IMAGE_INJ_GENERAL)

lemma FINITE_FINITE_PREIMAGE_GENERAL: "finite (t::'B => bool) &
(ALL y::'B.
    y : t -->
    finite
     {u::'A. EX x::'A. (x : (s::'A => bool) & (f::'A => 'B) x = y) & u = x})
==> finite {u::'A. EX x::'A. (x : s & f x : t) & u = x}"
  by (import hollight FINITE_FINITE_PREIMAGE_GENERAL)

lemma FINITE_FINITE_PREIMAGE: "finite (t::'B => bool) &
(ALL y::'B. y : t --> finite {u::'A. EX x::'A. (f::'A => 'B) x = y & u = x})
==> finite {u::'A. EX x::'A. f x : t & u = x}"
  by (import hollight FINITE_FINITE_PREIMAGE)

lemma FINITE_IMAGE_INJ_EQ: "(!!(x::'A) y::'A.
    x : (s::'A => bool) & y : s & (f::'A => 'B) x = f y ==> x = y)
==> finite (f ` s) = finite s"
  by (import hollight FINITE_IMAGE_INJ_EQ)

lemma FINITE_IMAGE_INJ: "(ALL (x::'A) y::'A. (f::'A => 'B) x = f y --> x = y) &
finite (A::'B => bool)
==> finite {u::'A. EX x::'A. f x : A & u = x}"
  by (import hollight FINITE_IMAGE_INJ)

lemma INFINITE_IMAGE_INJ: "[| !!(x::'A) y::'A. (f::'A => 'B) x = f y ==> x = y;
   infinite (s::'A => bool) |]
==> infinite (f ` s)"
  by (import hollight INFINITE_IMAGE_INJ)

lemma FINITE_SUBSET_IMAGE: "(finite (t::'B => bool) & t <= (f::'A => 'B) ` (s::'A => bool)) =
(EX x::'A => bool. finite x & x <= s & t = f ` x)"
  by (import hollight FINITE_SUBSET_IMAGE)

lemma EXISTS_FINITE_SUBSET_IMAGE: "(EX xc::'q_49755 => bool.
    finite xc &
    xc <= (xa::'q_49735 => 'q_49755) ` (xb::'q_49735 => bool) &
    (x::('q_49755 => bool) => bool) xc) =
(EX xc::'q_49735 => bool. finite xc & xc <= xb & x (xa ` xc))"
  by (import hollight EXISTS_FINITE_SUBSET_IMAGE)

lemma FINITE_SUBSET_IMAGE_IMP: "finite (t::'B => bool) & t <= (f::'A => 'B) ` (s::'A => bool)
==> EX s'::'A => bool. finite s' & s' <= s & t <= f ` s'"
  by (import hollight FINITE_SUBSET_IMAGE_IMP)

definition
  FINREC :: "('A => 'B => 'B) => 'B => ('A => bool) => 'B => nat => bool"  where
  "FINREC ==
SOME FINREC::('A => 'B => 'B) => 'B => ('A => bool) => 'B => nat => bool.
   (ALL (f::'A => 'B => 'B) (s::'A => bool) (a::'B) b::'B.
       FINREC f b s a (0::nat) = (s = {} & a = b)) &
   (ALL (b::'B) (s::'A => bool) (n::nat) (a::'B) f::'A => 'B => 'B.
       FINREC f b s a (Suc n) =
       (EX (x::'A) c::'B. x : s & FINREC f b (s - {x}) c n & a = f x c))"

lemma DEF_FINREC: "FINREC =
(SOME FINREC::('A => 'B => 'B) => 'B => ('A => bool) => 'B => nat => bool.
    (ALL (f::'A => 'B => 'B) (s::'A => bool) (a::'B) b::'B.
        FINREC f b s a (0::nat) = (s = {} & a = b)) &
    (ALL (b::'B) (s::'A => bool) (n::nat) (a::'B) f::'A => 'B => 'B.
        FINREC f b s a (Suc n) =
        (EX (x::'A) c::'B. x : s & FINREC f b (s - {x}) c n & a = f x c)))"
  by (import hollight DEF_FINREC)

lemma FINREC_1_LEMMA: "FINREC (x::'q_49919 => 'q_49918 => 'q_49918) (xa::'q_49918)
 (xb::'q_49919 => bool) (xc::'q_49918) (Suc (0::nat)) =
(EX xd::'q_49919. xb = {xd} & xc = x xd xa)"
  by (import hollight FINREC_1_LEMMA)

lemma FINREC_SUC_LEMMA: "[| !!(x::'A) (y::'A) s::'B.
      x ~= y ==> (f::'A => 'B => 'B) x (f y s) = f y (f x s);
   FINREC f (b::'B) (s::'A => bool) (z::'B) (Suc (n::nat)); (x::'A) : s |]
==> EX w::'B. FINREC f b (s - {x}) w n & z = f x w"
  by (import hollight FINREC_SUC_LEMMA)

lemma FINREC_UNIQUE_LEMMA: "[| !!(x::'A) (y::'A) s::'B.
      x ~= y ==> (f::'A => 'B => 'B) x (f y s) = f y (f x s);
   FINREC f (b::'B) (s::'A => bool) (a1::'B) (n1::nat) &
   FINREC f b s (a2::'B) (n2::nat) |]
==> a1 = a2 & n1 = n2"
  by (import hollight FINREC_UNIQUE_LEMMA)

lemma FINREC_EXISTS_LEMMA: "finite (s::'A => bool)
==> EX a::'B. Ex (FINREC (f::'A => 'B => 'B) (b::'B) s a)"
  by (import hollight FINREC_EXISTS_LEMMA)

lemma FINREC_FUN_LEMMA: "(ALL s::'A.
    (P::'A => bool) s -->
    (EX a::'B. Ex ((R::'A => 'B => 'C => bool) s a))) &
(ALL (n1::'C) (n2::'C) (s::'A) (a1::'B) a2::'B.
    R s a1 n1 & R s a2 n2 --> a1 = a2 & n1 = n2)
==> EX x::'A => 'B. ALL (s::'A) a::'B. P s --> Ex (R s a) = (x s = a)"
  by (import hollight FINREC_FUN_LEMMA)

lemma FINREC_FUN: "(!!(x::'A) (y::'A) s::'B.
    x ~= y ==> (f::'A => 'B => 'B) x (f y s) = f y (f x s))
==> EX g::('A => bool) => 'B.
       g {} = (b::'B) &
       (ALL (s::'A => bool) x::'A.
           finite s & x : s --> g s = f x (g (s - {x})))"
  by (import hollight FINREC_FUN)

lemma SET_RECURSION_LEMMA: "(!!(x::'A) (y::'A) s::'B.
    x ~= y ==> (f::'A => 'B => 'B) x (f y s) = f y (f x s))
==> EX g::('A => bool) => 'B.
       g {} = (b::'B) &
       (ALL (x::'A) s::'A => bool.
           finite s --> g (insert x s) = (if x : s then g s else f x (g s)))"
  by (import hollight SET_RECURSION_LEMMA)

definition
  ITSET :: "('q_50575 => 'q_50574 => 'q_50574)
=> ('q_50575 => bool) => 'q_50574 => 'q_50574"  where
  "ITSET ==
%(u::'q_50575 => 'q_50574 => 'q_50574) (ua::'q_50575 => bool) ub::'q_50574.
   (SOME g::('q_50575 => bool) => 'q_50574.
       g {} = ub &
       (ALL (x::'q_50575) s::'q_50575 => bool.
           finite s -->
           g (insert x s) = (if x : s then g s else u x (g s))))
    ua"

lemma DEF_ITSET: "ITSET =
(%(u::'q_50575 => 'q_50574 => 'q_50574) (ua::'q_50575 => bool) ub::'q_50574.
    (SOME g::('q_50575 => bool) => 'q_50574.
        g {} = ub &
        (ALL (x::'q_50575) s::'q_50575 => bool.
            finite s -->
            g (insert x s) = (if x : s then g s else u x (g s))))
     ua)"
  by (import hollight DEF_ITSET)

lemma FINITE_RECURSION: "(!!(x::'A) (y::'A) s::'B.
    x ~= y ==> (f::'A => 'B => 'B) x (f y s) = f y (f x s))
==> ITSET f {} (b::'B) = b &
    (ALL (x::'A) xa::'A => bool.
        finite xa -->
        ITSET f (insert x xa) b =
        (if x : xa then ITSET f xa b else f x (ITSET f xa b)))"
  by (import hollight FINITE_RECURSION)

lemma FINITE_RECURSION_DELETE: "(!!(x::'A) (y::'A) s::'B.
    x ~= y ==> (f::'A => 'B => 'B) x (f y s) = f y (f x s))
==> ITSET f {} (b::'B) = b &
    (ALL (x::'A) s::'A => bool.
        finite s -->
        ITSET f s b =
        (if x : s then f x (ITSET f (s - {x}) b) else ITSET f (s - {x}) b))"
  by (import hollight FINITE_RECURSION_DELETE)

lemma ITSET_EQ: "finite (x::'q_50880 => bool) &
(ALL xc::'q_50880.
    xc : x -->
    (xa::'q_50880 => 'q_50881 => 'q_50881) xc =
    (xb::'q_50880 => 'q_50881 => 'q_50881) xc) &
(ALL (x::'q_50880) (y::'q_50880) s::'q_50881.
    x ~= y --> xa x (xa y s) = xa y (xa x s)) &
(ALL (x::'q_50880) (y::'q_50880) s::'q_50881.
    x ~= y --> xb x (xb y s) = xb y (xb x s))
==> ITSET xa x (xc::'q_50881) = ITSET xb x xc"
  by (import hollight ITSET_EQ)

lemma SUBSET_RESTRICT: "{u::'q_50914.
 EX xb::'q_50914.
    (xb : (x::'q_50914 => bool) & (xa::'q_50914 => bool) xb) & u = xb}
<= x"
  by (import hollight SUBSET_RESTRICT)

lemma FINITE_RESTRICT: "finite (s::'A => bool)
==> finite {u::'A. EX x::'A. (x : s & (P::'A => bool) x) & u = x}"
  by (import hollight FINITE_RESTRICT)

definition
  CARD :: "('q_50968 => bool) => nat"  where
  "CARD == %u::'q_50968 => bool. ITSET (%x::'q_50968. Suc) u (0::nat)"

lemma DEF_CARD: "CARD = (%u::'q_50968 => bool. ITSET (%x::'q_50968. Suc) u (0::nat))"
  by (import hollight DEF_CARD)

lemma CARD_CLAUSES: "CARD {} = (0::nat) &
(ALL (x::'A::type) s::'A::type => bool.
    finite s -->
    CARD (insert x s) = (if x : s then CARD s else Suc (CARD s)))"
  by (import hollight CARD_CLAUSES)

lemma CARD_UNION: "finite (x::'A => bool) & finite (xa::'A => bool) & x Int xa = {}
==> CARD (x Un xa) = CARD x + CARD xa"
  by (import hollight CARD_UNION)

lemma CARD_DELETE: "finite (s::'A => bool)
==> CARD (s - {x::'A}) = (if x : s then CARD s - (1::nat) else CARD s)"
  by (import hollight CARD_DELETE)

lemma CARD_UNION_EQ: "finite (u::'q_51213 => bool) &
(s::'q_51213 => bool) Int (t::'q_51213 => bool) = {} & s Un t = u
==> CARD s + CARD t = CARD u"
  by (import hollight CARD_UNION_EQ)

lemma CARD_DIFF: "finite (s::'q_51270 => bool) & (t::'q_51270 => bool) <= s
==> CARD (s - t) = CARD s - CARD t"
  by (import hollight CARD_DIFF)

lemma CARD_EQ_0: "finite (s::'q_51308 => bool) ==> (CARD s = (0::nat)) = (s = {})"
  by (import hollight CARD_EQ_0)

lemma FINITE_INDUCT_DELETE: "[| (P::('A => bool) => bool) {} &
   (ALL s::'A => bool.
       finite s & s ~= {} --> (EX x::'A. x : s & (P (s - {x}) --> P s)));
   finite (s::'A => bool) |]
==> P s"
  by (import hollight FINITE_INDUCT_DELETE)

definition
  HAS_SIZE :: "('q_51427 => bool) => nat => bool"  where
  "HAS_SIZE == %(u::'q_51427 => bool) ua::nat. finite u & CARD u = ua"

lemma DEF_HAS_SIZE: "HAS_SIZE = (%(u::'q_51427 => bool) ua::nat. finite u & CARD u = ua)"
  by (import hollight DEF_HAS_SIZE)

lemma HAS_SIZE_CARD: "HAS_SIZE (x::'q_51446 => bool) (xa::nat) ==> CARD x = xa"
  by (import hollight HAS_SIZE_CARD)

lemma HAS_SIZE_0: "HAS_SIZE (s::'A => bool) (0::nat) = (s = {})"
  by (import hollight HAS_SIZE_0)

lemma HAS_SIZE_SUC: "HAS_SIZE (s::'A => bool) (Suc (n::nat)) =
(s ~= {} & (ALL x::'A. x : s --> HAS_SIZE (s - {x}) n))"
  by (import hollight HAS_SIZE_SUC)

lemma HAS_SIZE_UNION: "HAS_SIZE (x::'q_51584 => bool) (xb::nat) &
HAS_SIZE (xa::'q_51584 => bool) (xc::nat) & x Int xa = {}
==> HAS_SIZE (x Un xa) (xb + xc)"
  by (import hollight HAS_SIZE_UNION)

lemma HAS_SIZE_DIFF: "HAS_SIZE (x::'q_51620 => bool) (xb::nat) &
HAS_SIZE (xa::'q_51620 => bool) (xc::nat) & xa <= x
==> HAS_SIZE (x - xa) (xb - xc)"
  by (import hollight HAS_SIZE_DIFF)

lemma HAS_SIZE_UNIONS: "HAS_SIZE (x::'A => bool) (xb::nat) &
(ALL xb::'A. xb : x --> HAS_SIZE ((xa::'A => 'B => bool) xb) (xc::nat)) &
(ALL (xb::'A) y::'A. xb : x & y : x & xb ~= y --> xa xb Int xa y = {})
==> HAS_SIZE (Union {u::'B => bool. EX xb::'A. xb : x & u = xa xb})
     (xb * xc)"
  by (import hollight HAS_SIZE_UNIONS)

lemma FINITE_HAS_SIZE: "finite (x::'q_51824 => bool) = HAS_SIZE x (CARD x)"
  by (import hollight FINITE_HAS_SIZE)

lemma HAS_SIZE_CLAUSES: "HAS_SIZE (s::'q_51886 => bool) (0::nat) = (s = {}) &
HAS_SIZE s (Suc (n::nat)) =
(EX (a::'q_51886) t::'q_51886 => bool.
    HAS_SIZE t n & a ~: t & s = insert a t)"
  by (import hollight HAS_SIZE_CLAUSES)

lemma CARD_SUBSET_EQ: "finite (b::'A => bool) & (a::'A => bool) <= b & CARD a = CARD b ==> a = b"
  by (import hollight CARD_SUBSET_EQ)

lemma CARD_SUBSET: "(a::'A => bool) <= (b::'A => bool) & finite b ==> CARD a <= CARD b"
  by (import hollight CARD_SUBSET)

lemma CARD_SUBSET_LE: "finite (b::'A => bool) & (a::'A => bool) <= b & CARD b <= CARD a ==> a = b"
  by (import hollight CARD_SUBSET_LE)

lemma SUBSET_CARD_EQ: "finite (t::'q_52197 => bool) & (s::'q_52197 => bool) <= t
==> (CARD s = CARD t) = (s = t)"
  by (import hollight SUBSET_CARD_EQ)

lemma CARD_PSUBSET: "(a::'A => bool) < (b::'A => bool) & finite b ==> CARD a < CARD b"
  by (import hollight CARD_PSUBSET)

lemma CARD_UNION_LE: "finite (s::'A => bool) & finite (t::'A => bool)
==> CARD (s Un t) <= CARD s + CARD t"
  by (import hollight CARD_UNION_LE)

lemma CARD_UNIONS_LE: "HAS_SIZE (x::'A => bool) (xb::nat) &
(ALL xb::'A.
    xb : x -->
    finite ((xa::'A => 'B => bool) xb) & CARD (xa xb) <= (xc::nat))
==> CARD (Union {u::'B => bool. EX xb::'A. xb : x & u = xa xb}) <= xb * xc"
  by (import hollight CARD_UNIONS_LE)

lemma CARD_UNION_GEN: "finite (s::'q_52620 => bool) & finite (t::'q_52620 => bool)
==> CARD (s Un t) = CARD s + CARD t - CARD (s Int t)"
  by (import hollight CARD_UNION_GEN)

lemma CARD_UNION_OVERLAP_EQ: "finite (s::'q_52701 => bool) & finite (t::'q_52701 => bool)
==> (CARD (s Un t) = CARD s + CARD t) = (s Int t = {})"
  by (import hollight CARD_UNION_OVERLAP_EQ)

lemma CARD_UNION_OVERLAP: "finite (x::'q_52743 => bool) &
finite (xa::'q_52743 => bool) & CARD (x Un xa) < CARD x + CARD xa
==> x Int xa ~= {}"
  by (import hollight CARD_UNION_OVERLAP)

lemma CARD_IMAGE_INJ: "(ALL (xa::'A) y::'A.
    xa : (x::'A => bool) & y : x & (f::'A => 'B) xa = f y --> xa = y) &
finite x
==> CARD (f ` x) = CARD x"
  by (import hollight CARD_IMAGE_INJ)

lemma HAS_SIZE_IMAGE_INJ: "(ALL (xb::'A) y::'A.
    xb : (xa::'A => bool) & y : xa & (x::'A => 'B) xb = x y --> xb = y) &
HAS_SIZE xa (xb::nat)
==> HAS_SIZE (x ` xa) xb"
  by (import hollight HAS_SIZE_IMAGE_INJ)

lemma CARD_IMAGE_LE: "finite (s::'A => bool) ==> CARD ((f::'A => 'B) ` s) <= CARD s"
  by (import hollight CARD_IMAGE_LE)

lemma CARD_IMAGE_INJ_EQ: "finite (s::'A => bool) &
(ALL x::'A. x : s --> (f::'A => 'B) x : (t::'B => bool)) &
(ALL y::'B. y : t --> (EX! x::'A. x : s & f x = y))
==> CARD t = CARD s"
  by (import hollight CARD_IMAGE_INJ_EQ)

lemma CARD_SUBSET_IMAGE: "finite (t::'q_52977 => bool) &
(s::'q_52984 => bool) <= (f::'q_52977 => 'q_52984) ` t
==> CARD s <= CARD t"
  by (import hollight CARD_SUBSET_IMAGE)

lemma HAS_SIZE_IMAGE_INJ_EQ: "(!!(x::'q_53049) y::'q_53049.
    x : (s::'q_53049 => bool) & y : s & (f::'q_53049 => 'q_53044) x = f y
    ==> x = y)
==> HAS_SIZE (f ` s) (n::nat) = HAS_SIZE s n"
  by (import hollight HAS_SIZE_IMAGE_INJ_EQ)

lemma CHOOSE_SUBSET_STRONG: "(finite (s::'A => bool) ==> (n::nat) <= CARD s) ==> EX t<=s. HAS_SIZE t n"
  by (import hollight CHOOSE_SUBSET_STRONG)

lemma CHOOSE_SUBSET: "[| finite (s::'A => bool); (n::nat) <= CARD s |] ==> EX t<=s. HAS_SIZE t n"
  by (import hollight CHOOSE_SUBSET)

lemma HAS_SIZE_PRODUCT_DEPENDENT: "HAS_SIZE (x::'A => bool) (xa::nat) &
(ALL xa::'A. xa : x --> HAS_SIZE ((xb::'A => 'B => bool) xa) (xc::nat))
==> HAS_SIZE
     {u::'A * 'B. EX (xa::'A) y::'B. (xa : x & y : xb xa) & u = (xa, y)}
     (xa * xc)"
  by (import hollight HAS_SIZE_PRODUCT_DEPENDENT)

lemma FINITE_PRODUCT_DEPENDENT: "finite (s::'A => bool) &
(ALL x::'A. x : s --> finite ((t::'A => 'B => bool) x))
==> finite
     {u::'C.
      EX (x::'A) y::'B. (x : s & y : t x) & u = (f::'A => 'B => 'C) x y}"
  by (import hollight FINITE_PRODUCT_DEPENDENT)

lemma FINITE_PRODUCT: "finite (x::'A => bool) & finite (xa::'B => bool)
==> finite {u::'A * 'B. EX (xb::'A) y::'B. (xb : x & y : xa) & u = (xb, y)}"
  by (import hollight FINITE_PRODUCT)

lemma CARD_PRODUCT: "finite (s::'A => bool) & finite (t::'B => bool)
==> CARD {u::'A * 'B. EX (x::'A) y::'B. (x : s & y : t) & u = (x, y)} =
    CARD s * CARD t"
  by (import hollight CARD_PRODUCT)

lemma HAS_SIZE_PRODUCT: "HAS_SIZE (x::'A => bool) (xa::nat) & HAS_SIZE (xb::'B => bool) (xc::nat)
==> HAS_SIZE
     {u::'A * 'B. EX (xa::'A) y::'B. (xa : x & y : xb) & u = (xa, y)}
     (xa * xc)"
  by (import hollight HAS_SIZE_PRODUCT)

definition
  CROSS :: "('q_53759 => bool) => ('q_53758 => bool) => 'q_53759 * 'q_53758 => bool"  where
  "CROSS ==
%(u::'q_53759 => bool) ua::'q_53758 => bool.
   {ub::'q_53759 * 'q_53758.
    EX (x::'q_53759) y::'q_53758. (x : u & y : ua) & ub = (x, y)}"

lemma DEF_CROSS: "CROSS =
(%(u::'q_53759 => bool) ua::'q_53758 => bool.
    {ub::'q_53759 * 'q_53758.
     EX (x::'q_53759) y::'q_53758. (x : u & y : ua) & ub = (x, y)})"
  by (import hollight DEF_CROSS)

lemma IN_CROSS: "((x::'q_53795, xa::'q_53798)
 : CROSS (xb::'q_53795 => bool) (xc::'q_53798 => bool)) =
(x : xb & xa : xc)"
  by (import hollight IN_CROSS)

lemma HAS_SIZE_CROSS: "HAS_SIZE (x::'q_53823 => bool) (xb::nat) &
HAS_SIZE (xa::'q_53826 => bool) (xc::nat)
==> HAS_SIZE (CROSS x xa) (xb * xc)"
  by (import hollight HAS_SIZE_CROSS)

lemma FINITE_CROSS: "finite (x::'q_53851 => bool) & finite (xa::'q_53853 => bool)
==> finite (CROSS x xa)"
  by (import hollight FINITE_CROSS)

lemma CARD_CROSS: "finite (x::'q_53874 => bool) & finite (xa::'q_53876 => bool)
==> CARD (CROSS x xa) = CARD x * CARD xa"
  by (import hollight CARD_CROSS)

lemma CROSS_EQ_EMPTY: "(CROSS (x::'q_53917 => bool) (xa::'q_53921 => bool) = {}) =
(x = {} | xa = {})"
  by (import hollight CROSS_EQ_EMPTY)

lemma HAS_SIZE_FUNSPACE: "HAS_SIZE (s::'A => bool) (m::nat) & HAS_SIZE (t::'B => bool) (n::nat)
==> HAS_SIZE
     {u::'A => 'B.
      EX f::'A => 'B.
         ((ALL x::'A. x : s --> f x : t) &
          (ALL x::'A. x ~: s --> f x = (d::'B))) &
         u = f}
     (n ^ m)"
  by (import hollight HAS_SIZE_FUNSPACE)

lemma CARD_FUNSPACE: "finite (s::'q_54227 => bool) & finite (t::'q_54224 => bool)
==> CARD
     {u::'q_54227 => 'q_54224.
      EX f::'q_54227 => 'q_54224.
         ((ALL x::'q_54227. x : s --> f x : t) &
          (ALL x::'q_54227. x ~: s --> f x = (d::'q_54224))) &
         u = f} =
    CARD t ^ CARD s"
  by (import hollight CARD_FUNSPACE)

lemma FINITE_FUNSPACE: "finite (s::'q_54293 => bool) & finite (t::'q_54290 => bool)
==> finite
     {u::'q_54293 => 'q_54290.
      EX f::'q_54293 => 'q_54290.
         ((ALL x::'q_54293. x : s --> f x : t) &
          (ALL x::'q_54293. x ~: s --> f x = (d::'q_54290))) &
         u = f}"
  by (import hollight FINITE_FUNSPACE)

lemma HAS_SIZE_POWERSET: "HAS_SIZE (s::'A => bool) (n::nat)
==> HAS_SIZE {u::'A => bool. EX t<=s. u = t} ((2::nat) ^ n)"
  by (import hollight HAS_SIZE_POWERSET)

lemma CARD_POWERSET: "finite (s::'A => bool)
==> CARD {u::'A => bool. EX t<=s. u = t} = (2::nat) ^ CARD s"
  by (import hollight CARD_POWERSET)

lemma FINITE_POWERSET: "finite (s::'A => bool) ==> finite {u::'A => bool. EX t<=s. u = t}"
  by (import hollight FINITE_POWERSET)

lemma FINITE_UNIONS: "finite (Union (s::('A => bool) => bool)) =
(finite s & (ALL t::'A => bool. t : s --> finite t))"
  by (import hollight FINITE_UNIONS)

lemma POWERSET_CLAUSES: "{x::'q_54515 => bool. EX xa<={}. x = xa} = {{}} &
(ALL (x::'A) xa::'A => bool.
    {xb::'A => bool. EX xc<=insert x xa. xb = xc} =
    {u::'A => bool. EX s<=xa. u = s} Un
    insert x ` {u::'A => bool. EX s<=xa. u = s})"
  by (import hollight POWERSET_CLAUSES)

lemma HAS_SIZE_NUMSEG_LT: "HAS_SIZE {u. EX m<n. u = m} n"
  by (import hollight HAS_SIZE_NUMSEG_LT)

lemma CARD_NUMSEG_LT: "CARD {u. EX m<x. u = m} = x"
  by (import hollight CARD_NUMSEG_LT)

lemma FINITE_NUMSEG_LT: "finite {u::nat. EX m<x::nat. u = m}"
  by (import hollight FINITE_NUMSEG_LT)

lemma HAS_SIZE_NUMSEG_LE: "HAS_SIZE {xa. EX xb<=x. xa = xb} (x + 1)"
  by (import hollight HAS_SIZE_NUMSEG_LE)

lemma FINITE_NUMSEG_LE: "finite {u::nat. EX m<=x::nat. u = m}"
  by (import hollight FINITE_NUMSEG_LE)

lemma CARD_NUMSEG_LE: "CARD {u. EX m<=x. u = m} = x + 1"
  by (import hollight CARD_NUMSEG_LE)

lemma num_FINITE: "finite (s::nat => bool) = (EX a::nat. ALL x::nat. x : s --> x <= a)"
  by (import hollight num_FINITE)

lemma num_FINITE_AVOID: "finite (s::nat => bool) ==> EX a::nat. a ~: s"
  by (import hollight num_FINITE_AVOID)

lemma FINITE_REAL_INTERVAL: "(ALL a. infinite {u. EX x. real_lt a x & u = x}) &
(ALL a. infinite {u. EX x. real_le a x & u = x}) &
(ALL b. infinite {u. EX x. real_lt x b & u = x}) &
(ALL b. infinite {u. EX x. real_le x b & u = x}) &
(ALL x xa.
    finite {u. EX xb. (real_lt x xb & real_lt xb xa) & u = xb} =
    real_le xa x) &
(ALL a b.
    finite {u. EX x. (real_le a x & real_lt x b) & u = x} = real_le b a) &
(ALL a b.
    finite {u. EX x. (real_lt a x & real_le x b) & u = x} = real_le b a) &
(ALL a b.
    finite {u. EX x. (real_le a x & real_le x b) & u = x} = real_le b a)"
  by (import hollight FINITE_REAL_INTERVAL)

lemma real_INFINITE: "(infinite::(hollight.real => bool) => bool) (UNIV::hollight.real => bool)"
  by (import hollight real_INFINITE)

lemma HAS_SIZE_INDEX: "HAS_SIZE (x::'A => bool) (n::nat)
==> EX f::nat => 'A.
       (ALL m<n. f m : x) &
       (ALL xa::'A. xa : x --> (EX! m::nat. m < n & f m = xa))"
  by (import hollight HAS_SIZE_INDEX)

definition
  pairwise :: "('q_55938 => 'q_55938 => bool) => ('q_55938 => bool) => bool"  where
  "pairwise ==
%(u::'q_55938 => 'q_55938 => bool) ua::'q_55938 => bool.
   ALL (x::'q_55938) y::'q_55938. x : ua & y : ua & x ~= y --> u x y"

lemma DEF_pairwise: "pairwise =
(%(u::'q_55938 => 'q_55938 => bool) ua::'q_55938 => bool.
    ALL (x::'q_55938) y::'q_55938. x : ua & y : ua & x ~= y --> u x y)"
  by (import hollight DEF_pairwise)

definition
  PAIRWISE :: "('A => 'A => bool) => 'A list => bool"  where
  "PAIRWISE ==
SOME PAIRWISE::('A => 'A => bool) => 'A list => bool.
   (ALL r::'A => 'A => bool. PAIRWISE r [] = True) &
   (ALL (h::'A) (r::'A => 'A => bool) t::'A list.
       PAIRWISE r (h # t) = (list_all (r h) t & PAIRWISE r t))"

lemma DEF_PAIRWISE: "PAIRWISE =
(SOME PAIRWISE::('A => 'A => bool) => 'A list => bool.
    (ALL r::'A => 'A => bool. PAIRWISE r [] = True) &
    (ALL (h::'A) (r::'A => 'A => bool) t::'A list.
        PAIRWISE r (h # t) = (list_all (r h) t & PAIRWISE r t)))"
  by (import hollight DEF_PAIRWISE)

lemma PAIRWISE_EMPTY: "pairwise (x::'q_55973 => 'q_55973 => bool) {} = True"
  by (import hollight PAIRWISE_EMPTY)

lemma PAIRWISE_SING: "pairwise (x::'q_55991 => 'q_55991 => bool) {xa::'q_55991} = True"
  by (import hollight PAIRWISE_SING)

lemma PAIRWISE_MONO: "pairwise (x::'q_56011 => 'q_56011 => bool) (xa::'q_56011 => bool) &
(xb::'q_56011 => bool) <= xa
==> pairwise x xb"
  by (import hollight PAIRWISE_MONO)

lemma SURJECTIVE_IFF_INJECTIVE_GEN: "finite (s::'A => bool) &
finite (t::'B => bool) & CARD s = CARD t & (f::'A => 'B) ` s <= t
==> (ALL y::'B. y : t --> (EX x::'A. x : s & f x = y)) =
    (ALL (x::'A) y::'A. x : s & y : s & f x = f y --> x = y)"
  by (import hollight SURJECTIVE_IFF_INJECTIVE_GEN)

lemma SURJECTIVE_IFF_INJECTIVE: "finite (x::'A => bool) & (xa::'A => 'A) ` x <= x
==> (ALL y::'A. y : x --> (EX xb::'A. xb : x & xa xb = y)) =
    (ALL (xb::'A) y::'A. xb : x & y : x & xa xb = xa y --> xb = y)"
  by (import hollight SURJECTIVE_IFF_INJECTIVE)

lemma IMAGE_IMP_INJECTIVE_GEN: "[| finite (s::'A => bool) &
   CARD s = CARD (t::'B => bool) & (f::'A => 'B) ` s = t;
   (x::'A) : s & (y::'A) : s & f x = f y |]
==> x = y"
  by (import hollight IMAGE_IMP_INJECTIVE_GEN)

lemma IMAGE_IMP_INJECTIVE: "[| finite (s::'q_56387 => bool) & (f::'q_56387 => 'q_56387) ` s = s;
   (x::'q_56387) : s & (y::'q_56387) : s & f x = f y |]
==> x = y"
  by (import hollight IMAGE_IMP_INJECTIVE)

lemma CARD_LE_INJ: "finite (x::'A => bool) & finite (xa::'B => bool) & CARD x <= CARD xa
==> EX f::'A => 'B.
       f ` x <= xa &
       (ALL (xa::'A) y::'A. xa : x & y : x & f xa = f y --> xa = y)"
  by (import hollight CARD_LE_INJ)

lemma FORALL_IN_CLAUSES: "(ALL x::'q_56493 => bool. (ALL xa::'q_56493. xa : {} --> x xa) = True) &
(ALL (x::'q_56533 => bool) (xa::'q_56533) xb::'q_56533 => bool.
    (ALL xc::'q_56533. xc : insert xa xb --> x xc) =
    (x xa & (ALL xa::'q_56533. xa : xb --> x xa)))"
  by (import hollight FORALL_IN_CLAUSES)

lemma EXISTS_IN_CLAUSES: "(ALL x::'q_56553 => bool. (EX xa::'q_56553. xa : {} & x xa) = False) &
(ALL (x::'q_56593 => bool) (xa::'q_56593) xb::'q_56593 => bool.
    (EX xc::'q_56593. xc : insert xa xb & x xc) =
    (x xa | (EX xa::'q_56593. xa : xb & x xa)))"
  by (import hollight EXISTS_IN_CLAUSES)

lemma SURJECTIVE_ON_RIGHT_INVERSE: "(ALL xb::'q_56650.
    xb : (xa::'q_56650 => bool) -->
    (EX xa::'q_56649.
        xa : (s::'q_56649 => bool) & (x::'q_56649 => 'q_56650) xa = xb)) =
(EX g::'q_56650 => 'q_56649.
    ALL y::'q_56650. y : xa --> g y : s & x (g y) = y)"
  by (import hollight SURJECTIVE_ON_RIGHT_INVERSE)

lemma INJECTIVE_ON_LEFT_INVERSE: "(ALL (xb::'q_56743) y::'q_56743.
    xb : (xa::'q_56743 => bool) &
    y : xa & (x::'q_56743 => 'q_56746) xb = x y -->
    xb = y) =
(EX xb::'q_56746 => 'q_56743. ALL xc::'q_56743. xc : xa --> xb (x xc) = xc)"
  by (import hollight INJECTIVE_ON_LEFT_INVERSE)

lemma BIJECTIVE_ON_LEFT_RIGHT_INVERSE: "(!!x::'q_56878.
    x : (s::'q_56878 => bool)
    ==> (f::'q_56878 => 'q_56877) x : (t::'q_56877 => bool))
==> ((ALL (x::'q_56878) y::'q_56878. x : s & y : s & f x = f y --> x = y) &
     (ALL x::'q_56877. x : t --> (EX xa::'q_56878. xa : s & f xa = x))) =
    (EX g::'q_56877 => 'q_56878.
        (ALL y::'q_56877. y : t --> g y : s) &
        (ALL y::'q_56877. y : t --> f (g y) = y) &
        (ALL x::'q_56878. x : s --> g (f x) = x))"
  by (import hollight BIJECTIVE_ON_LEFT_RIGHT_INVERSE)

lemma SURJECTIVE_RIGHT_INVERSE: "(ALL y::'q_56902. EX x::'q_56905. (f::'q_56905 => 'q_56902) x = y) =
(EX g::'q_56902 => 'q_56905. ALL y::'q_56902. f (g y) = y)"
  by (import hollight SURJECTIVE_RIGHT_INVERSE)

lemma INJECTIVE_LEFT_INVERSE: "(ALL (x::'q_56939) xa::'q_56939.
    (f::'q_56939 => 'q_56942) x = f xa --> x = xa) =
(EX g::'q_56942 => 'q_56939. ALL x::'q_56939. g (f x) = x)"
  by (import hollight INJECTIVE_LEFT_INVERSE)

lemma BIJECTIVE_LEFT_RIGHT_INVERSE: "((ALL (x::'A) y::'A. (f::'A => 'B) x = f y --> x = y) &
 (ALL y::'B. EX x::'A. f x = y)) =
(EX g::'B => 'A. (ALL y::'B. f (g y) = y) & (ALL x::'A. g (f x) = x))"
  by (import hollight BIJECTIVE_LEFT_RIGHT_INVERSE)

lemma FUNCTION_FACTORS_RIGHT: "(ALL xb::'q_57046.
    EX y::'q_57034.
       (xa::'q_57034 => 'q_57047) y = (x::'q_57046 => 'q_57047) xb) =
(EX xb::'q_57046 => 'q_57034. x = xa o xb)"
  by (import hollight FUNCTION_FACTORS_RIGHT)

lemma FUNCTION_FACTORS_LEFT: "(ALL (xb::'q_57119) y::'q_57119.
    (xa::'q_57119 => 'q_57099) xb = xa y -->
    (x::'q_57119 => 'q_57120) xb = x y) =
(EX xb::'q_57099 => 'q_57120. x = xb o xa)"
  by (import hollight FUNCTION_FACTORS_LEFT)

lemma SURJECTIVE_FORALL_THM: "(ALL y::'B. EX x::'A. (f::'A => 'B) x = y) =
(ALL P::'B => bool. (ALL x::'A. P (f x)) = All P)"
  by (import hollight SURJECTIVE_FORALL_THM)

lemma SURJECTIVE_EXISTS_THM: "(ALL y::'B. EX x::'A. (f::'A => 'B) x = y) =
(ALL P::'B => bool. (EX x::'A. P (f x)) = Ex P)"
  by (import hollight SURJECTIVE_EXISTS_THM)

lemma SURJECTIVE_IMAGE_THM: "(ALL y::'B. EX x::'A. (f::'A => 'B) x = y) =
(ALL x::'B => bool.
    f ` {u::'A. EX xa::'A. x (f xa) & u = xa} =
    {u::'B. EX xa::'B. x xa & u = xa})"
  by (import hollight SURJECTIVE_IMAGE_THM)

lemma IMAGE_INJECTIVE_IMAGE_OF_SUBSET: "EX x<=s::'A => bool.
   (f::'A => 'B) ` s = f ` x &
   (ALL (xa::'A) y::'A. xa : x & y : x & f xa = f y --> xa = y)"
  by (import hollight IMAGE_INJECTIVE_IMAGE_OF_SUBSET)

lemma INJECTIVE_ON_IMAGE: "(ALL (s::'A => bool) t::'A => bool.
    s <= (u::'A => bool) & t <= u & (f::'A => 'B) ` s = f ` t --> s = t) =
(ALL (x::'A) y::'A. x : u & y : u & f x = f y --> x = y)"
  by (import hollight INJECTIVE_ON_IMAGE)

lemma INJECTIVE_IMAGE: "(ALL (s::'A => bool) t::'A => bool. (f::'A => 'B) ` s = f ` t --> s = t) =
(ALL (x::'A) y::'A. f x = f y --> x = y)"
  by (import hollight INJECTIVE_IMAGE)

lemma SURJECTIVE_ON_IMAGE: "(ALL t<=v::'B => bool. EX s<=u::'A => bool. (f::'A => 'B) ` s = t) =
(ALL y::'B. y : v --> (EX x::'A. x : u & f x = y))"
  by (import hollight SURJECTIVE_ON_IMAGE)

lemma SURJECTIVE_IMAGE: "(ALL t::'B => bool. EX s::'A => bool. (f::'A => 'B) ` s = t) =
(ALL y::'B. EX x::'A. f x = y)"
  by (import hollight SURJECTIVE_IMAGE)

lemma CARD_EQ_BIJECTION: "finite (s::'A => bool) & finite (t::'B => bool) & CARD s = CARD t
==> EX f::'A => 'B.
       (ALL x::'A. x : s --> f x : t) &
       (ALL y::'B. y : t --> (EX x::'A. x : s & f x = y)) &
       (ALL (x::'A) y::'A. x : s & y : s & f x = f y --> x = y)"
  by (import hollight CARD_EQ_BIJECTION)

lemma CARD_EQ_BIJECTIONS: "finite (s::'A => bool) & finite (t::'B => bool) & CARD s = CARD t
==> EX (f::'A => 'B) g::'B => 'A.
       (ALL x::'A. x : s --> f x : t & g (f x) = x) &
       (ALL y::'B. y : t --> g y : s & f (g y) = y)"
  by (import hollight CARD_EQ_BIJECTIONS)

lemma BIJECTIONS_HAS_SIZE: "(ALL x::'A.
    x : (s::'A => bool) -->
    (f::'A => 'B) x : (t::'B => bool) & (g::'B => 'A) (f x) = x) &
(ALL y::'B. y : t --> g y : s & f (g y) = y) & HAS_SIZE s (n::nat)
==> HAS_SIZE t n"
  by (import hollight BIJECTIONS_HAS_SIZE)

lemma BIJECTIONS_HAS_SIZE_EQ: "(ALL x::'A.
    x : (s::'A => bool) -->
    (f::'A => 'B) x : (t::'B => bool) & (g::'B => 'A) (f x) = x) &
(ALL y::'B. y : t --> g y : s & f (g y) = y)
==> HAS_SIZE s (n::nat) = HAS_SIZE t n"
  by (import hollight BIJECTIONS_HAS_SIZE_EQ)

lemma BIJECTIONS_CARD_EQ: "(finite (s::'A => bool) | finite (t::'B => bool)) &
(ALL x::'A. x : s --> (f::'A => 'B) x : t & (g::'B => 'A) (f x) = x) &
(ALL y::'B. y : t --> g y : s & f (g y) = y)
==> CARD s = CARD t"
  by (import hollight BIJECTIONS_CARD_EQ)

lemma WF_FINITE: "(ALL x::'A. ~ (u_556::'A => 'A => bool) x x) &
(ALL (x::'A) (y::'A) z::'A. u_556 x y & u_556 y z --> u_556 x z) &
(ALL x::'A. finite {u::'A. EX y::'A. u_556 y x & u = y})
==> wfP u_556"
  by (import hollight WF_FINITE)

consts
  "<=_c" :: "('q_58200 => bool) => ('q_58195 => bool) => bool" ("<='_c")

defs
  "<=_c_def": "<=_c ==
%(u::'q_58200 => bool) ua::'q_58195 => bool.
   EX f::'q_58200 => 'q_58195.
      (ALL x::'q_58200. x : u --> f x : ua) &
      (ALL (x::'q_58200) y::'q_58200. x : u & y : u & f x = f y --> x = y)"

lemma DEF__lessthan__equal__c: "<=_c =
(%(u::'q_58200 => bool) ua::'q_58195 => bool.
    EX f::'q_58200 => 'q_58195.
       (ALL x::'q_58200. x : u --> f x : ua) &
       (ALL (x::'q_58200) y::'q_58200. x : u & y : u & f x = f y --> x = y))"
  by (import hollight DEF__lessthan__equal__c)

consts
  "<_c" :: "('q_58212 => bool) => ('q_58213 => bool) => bool" ("<'_c")

defs
  "<_c_def": "<_c == %(u::'q_58212 => bool) ua::'q_58213 => bool. <=_c u ua & ~ <=_c ua u"

lemma DEF__lessthan__c: "<_c = (%(u::'q_58212 => bool) ua::'q_58213 => bool. <=_c u ua & ~ <=_c ua u)"
  by (import hollight DEF__lessthan__c)

consts
  "=_c" :: "('q_58264 => bool) => ('q_58261 => bool) => bool" ("='_c")

defs
  "=_c_def": "=_c ==
%(u::'q_58264 => bool) ua::'q_58261 => bool.
   EX f::'q_58264 => 'q_58261.
      (ALL x::'q_58264. x : u --> f x : ua) &
      (ALL y::'q_58261. y : ua --> (EX! x::'q_58264. x : u & f x = y))"

lemma DEF__equal__c: "=_c =
(%(u::'q_58264 => bool) ua::'q_58261 => bool.
    EX f::'q_58264 => 'q_58261.
       (ALL x::'q_58264. x : u --> f x : ua) &
       (ALL y::'q_58261. y : ua --> (EX! x::'q_58264. x : u & f x = y)))"
  by (import hollight DEF__equal__c)

consts
  ">=_c" :: "('q_58273 => bool) => ('q_58272 => bool) => bool" (">='_c")

defs
  ">=_c_def": ">=_c == %(u::'q_58273 => bool) ua::'q_58272 => bool. <=_c ua u"

lemma DEF__greaterthan__equal__c: ">=_c = (%(u::'q_58273 => bool) ua::'q_58272 => bool. <=_c ua u)"
  by (import hollight DEF__greaterthan__equal__c)

consts
  ">_c" :: "('q_58282 => bool) => ('q_58281 => bool) => bool" (">'_c")

defs
  ">_c_def": ">_c == %(u::'q_58282 => bool) ua::'q_58281 => bool. <_c ua u"

lemma DEF__greaterthan__c: ">_c = (%(u::'q_58282 => bool) ua::'q_58281 => bool. <_c ua u)"
  by (import hollight DEF__greaterthan__c)

lemma LE_C: "<=_c (x::'q_58320 => bool) (xa::'q_58323 => bool) =
(EX xb::'q_58323 => 'q_58320.
    ALL xc::'q_58320. xc : x --> (EX x::'q_58323. x : xa & xb x = xc))"
  by (import hollight LE_C)

lemma GE_C: ">=_c (x::'q_58364 => bool) (xa::'q_58361 => bool) =
(EX f::'q_58364 => 'q_58361.
    ALL y::'q_58361. y : xa --> (EX xa::'q_58364. xa : x & y = f xa))"
  by (import hollight GE_C)

definition
  COUNTABLE :: "('q_58372 => bool) => bool"  where
  "(op ==::(('q_58372::type => bool) => bool)
        => (('q_58372::type => bool) => bool) => prop)
 (COUNTABLE::('q_58372::type => bool) => bool)
 ((>=_c::(nat => bool) => ('q_58372::type => bool) => bool)
   (UNIV::nat => bool))"

lemma DEF_COUNTABLE: "(op =::(('q_58372::type => bool) => bool)
       => (('q_58372::type => bool) => bool) => bool)
 (COUNTABLE::('q_58372::type => bool) => bool)
 ((>=_c::(nat => bool) => ('q_58372::type => bool) => bool)
   (UNIV::nat => bool))"
  by (import hollight DEF_COUNTABLE)

lemma NUMSEG_COMBINE_R: "(x::nat) <= (xa::nat) + (1::nat) & xa <= (xb::nat)
==> {x..xa} Un {xa + (1::nat)..xb} = {x..xb}"
  by (import hollight NUMSEG_COMBINE_R)

lemma NUMSEG_COMBINE_L: "(x::nat) <= (xa::nat) & xa <= (xb::nat) + (1::nat)
==> {x..xa - (1::nat)} Un {xa..xb} = {x..xb}"
  by (import hollight NUMSEG_COMBINE_L)

lemma NUMSEG_LREC: "(x::nat) <= (xa::nat) ==> insert x {x + (1::nat)..xa} = {x..xa}"
  by (import hollight NUMSEG_LREC)

lemma NUMSEG_RREC: "(x::nat) <= (xa::nat) ==> insert xa {x..xa - (1::nat)} = {x..xa}"
  by (import hollight NUMSEG_RREC)

lemma IN_NUMSEG_0: "((x::nat) : {0::nat..xa::nat}) = (x <= xa)"
  by (import hollight IN_NUMSEG_0)

lemma NUMSEG_EMPTY: "({x::nat..xa::nat} = {}) = (xa < x)"
  by (import hollight NUMSEG_EMPTY)

lemma CARD_NUMSEG_LEMMA: "CARD {m..m + d} = d + 1"
  by (import hollight CARD_NUMSEG_LEMMA)

lemma CARD_NUMSEG: "CARD {m..n} = n + 1 - m"
  by (import hollight CARD_NUMSEG)

lemma HAS_SIZE_NUMSEG: "HAS_SIZE {x..xa} (xa + 1 - x)"
  by (import hollight HAS_SIZE_NUMSEG)

lemma CARD_NUMSEG_1: "CARD {1..x} = x"
  by (import hollight CARD_NUMSEG_1)

lemma HAS_SIZE_NUMSEG_1: "HAS_SIZE {1..x} x"
  by (import hollight HAS_SIZE_NUMSEG_1)

lemma NUMSEG_CLAUSES: "(ALL m::nat. {m..0::nat} = (if m = (0::nat) then {0::nat} else {})) &
(ALL (m::nat) n::nat.
    {m..Suc n} = (if m <= Suc n then insert (Suc n) {m..n} else {m..n}))"
  by (import hollight NUMSEG_CLAUSES)

lemma FINITE_INDEX_NUMSEG: "finite (s::'A => bool) =
(EX f::nat => 'A.
    (ALL (i::nat) j::nat.
        i : {1::nat..CARD s} & j : {1::nat..CARD s} & f i = f j --> i = j) &
    s = f ` {1::nat..CARD s})"
  by (import hollight FINITE_INDEX_NUMSEG)

lemma FINITE_INDEX_NUMBERS: "finite (s::'A => bool) =
(EX (k::nat => bool) f::nat => 'A.
    (ALL (i::nat) j::nat. i : k & j : k & f i = f j --> i = j) &
    finite k & s = f ` k)"
  by (import hollight FINITE_INDEX_NUMBERS)

lemma DISJOINT_NUMSEG: "({x::nat..xa::nat} Int {xb::nat..xc::nat} = {}) =
(xa < xb | xc < x | xa < x | xc < xb)"
  by (import hollight DISJOINT_NUMSEG)

lemma NUMSEG_ADD_SPLIT: "(x::nat) <= (xa::nat) + (1::nat)
==> {x..xa + (xb::nat)} = {x..xa} Un {xa + (1::nat)..xa + xb}"
  by (import hollight NUMSEG_ADD_SPLIT)

lemma SUBSET_NUMSEG: "({m::nat..n::nat} <= {p::nat..q::nat}) = (n < m | p <= m & n <= q)"
  by (import hollight SUBSET_NUMSEG)

lemma NUMSEG_LE: "{u::nat. EX xa<=x::nat. u = xa} = {0::nat..x}"
  by (import hollight NUMSEG_LE)

lemma NUMSEG_LT: "{u::nat. EX x<n::nat. u = x} =
(if n = (0::nat) then {} else {0::nat..n - (1::nat)})"
  by (import hollight NUMSEG_LT)

lemma TOPOLOGICAL_SORT: "[| (ALL (x::'A) y::'A.
       (u_556::'A => 'A => bool) x y & u_556 y x --> x = y) &
   (ALL (x::'A) (y::'A) z::'A. u_556 x y & u_556 y z --> u_556 x z);
   HAS_SIZE (s::'A => bool) (n::nat) |]
==> EX f::nat => 'A.
       s = f ` {1::nat..n} &
       (ALL (j::nat) k::nat.
           j : {1::nat..n} & k : {1::nat..n} & j < k -->
           ~ u_556 (f k) (f j))"
  by (import hollight TOPOLOGICAL_SORT)

lemma FINITE_INTSEG: "(ALL l r. finite {u. EX x. (int_le l x & int_le x r) & u = x}) &
(ALL l r. finite {u. EX x. (int_le l x & int_lt x r) & u = x}) &
(ALL l r. finite {u. EX x. (int_lt l x & int_le x r) & u = x}) &
(ALL l r. finite {u. EX x. (int_lt l x & int_lt x r) & u = x})"
  by (import hollight FINITE_INTSEG)

definition
  neutral :: "('q_59899 => 'q_59899 => 'q_59899) => 'q_59899"  where
  "neutral ==
%u::'q_59899 => 'q_59899 => 'q_59899.
   SOME x::'q_59899. ALL y::'q_59899. u x y = y & u y x = y"

lemma DEF_neutral: "neutral =
(%u::'q_59899 => 'q_59899 => 'q_59899.
    SOME x::'q_59899. ALL y::'q_59899. u x y = y & u y x = y)"
  by (import hollight DEF_neutral)

definition
  monoidal :: "('A => 'A => 'A) => bool"  where
  "monoidal ==
%u::'A => 'A => 'A.
   (ALL (x::'A) y::'A. u x y = u y x) &
   (ALL (x::'A) (y::'A) z::'A. u x (u y z) = u (u x y) z) &
   (ALL x::'A. u (neutral u) x = x)"

lemma DEF_monoidal: "monoidal =
(%u::'A => 'A => 'A.
    (ALL (x::'A) y::'A. u x y = u y x) &
    (ALL (x::'A) (y::'A) z::'A. u x (u y z) = u (u x y) z) &
    (ALL x::'A. u (neutral u) x = x))"
  by (import hollight DEF_monoidal)

lemma MONOIDAL_AC: "monoidal (x::'q_60055 => 'q_60055 => 'q_60055)
==> (ALL a::'q_60055. x (neutral x) a = a) &
    (ALL a::'q_60055. x a (neutral x) = a) &
    (ALL (a::'q_60055) b::'q_60055. x a b = x b a) &
    (ALL (a::'q_60055) (b::'q_60055) c::'q_60055.
        x (x a b) c = x a (x b c)) &
    (ALL (a::'q_60055) (b::'q_60055) c::'q_60055. x a (x b c) = x b (x a c))"
  by (import hollight MONOIDAL_AC)

definition
  support :: "('B => 'B => 'B) => ('A => 'B) => ('A => bool) => 'A => bool"  where
  "support ==
%(u::'B => 'B => 'B) (ua::'A => 'B) ub::'A => bool.
   {uc::'A. EX x::'A. (x : ub & ua x ~= neutral u) & uc = x}"

lemma DEF_support: "support =
(%(u::'B => 'B => 'B) (ua::'A => 'B) ub::'A => bool.
    {uc::'A. EX x::'A. (x : ub & ua x ~= neutral u) & uc = x})"
  by (import hollight DEF_support)

definition
  iterate :: "('q_60113 => 'q_60113 => 'q_60113)
=> ('A => bool) => ('A => 'q_60113) => 'q_60113"  where
  "iterate ==
%(u::'q_60113 => 'q_60113 => 'q_60113) (ua::'A => bool) ub::'A => 'q_60113.
   if finite (support u ub ua)
   then ITSET (%x::'A. u (ub x)) (support u ub ua) (neutral u)
   else neutral u"

lemma DEF_iterate: "iterate =
(%(u::'q_60113 => 'q_60113 => 'q_60113) (ua::'A => bool) ub::'A => 'q_60113.
    if finite (support u ub ua)
    then ITSET (%x::'A. u (ub x)) (support u ub ua) (neutral u)
    else neutral u)"
  by (import hollight DEF_iterate)

lemma IN_SUPPORT: "((xb::'q_60163)
 : support (x::'q_60160 => 'q_60160 => 'q_60160) (xa::'q_60163 => 'q_60160)
    (xc::'q_60163 => bool)) =
(xb : xc & xa xb ~= neutral x)"
  by (import hollight IN_SUPPORT)

lemma SUPPORT_SUPPORT: "support (x::'q_60185 => 'q_60185 => 'q_60185) (xa::'q_60196 => 'q_60185)
 (support x xa (xb::'q_60196 => bool)) =
support x xa xb"
  by (import hollight SUPPORT_SUPPORT)

lemma SUPPORT_EMPTY: "(ALL xc::'q_60235.
    xc : (xb::'q_60235 => bool) -->
    (xa::'q_60235 => 'q_60221) xc =
    neutral (x::'q_60221 => 'q_60221 => 'q_60221)) =
(support x xa xb = {})"
  by (import hollight SUPPORT_EMPTY)

lemma SUPPORT_SUBSET: "support (x::'q_60255 => 'q_60255 => 'q_60255) (xa::'q_60256 => 'q_60255)
 (xb::'q_60256 => bool)
<= xb"
  by (import hollight SUPPORT_SUBSET)

lemma FINITE_SUPPORT: "finite (s::'q_60273 => bool)
==> finite
     (support (u::'q_60279 => 'q_60279 => 'q_60279)
       (f::'q_60273 => 'q_60279) s)"
  by (import hollight FINITE_SUPPORT)

lemma SUPPORT_CLAUSES: "(ALL x::'q_60297 => 'q_60530.
    support (u_4371::'q_60530 => 'q_60530 => 'q_60530) x {} = {}) &
(ALL (x::'q_60345 => 'q_60530) (xa::'q_60345) xb::'q_60345 => bool.
    support u_4371 x (insert xa xb) =
    (if x xa = neutral u_4371 then support u_4371 x xb
     else insert xa (support u_4371 x xb))) &
(ALL (x::'q_60378 => 'q_60530) (xa::'q_60378) xb::'q_60378 => bool.
    support u_4371 x (xb - {xa}) = support u_4371 x xb - {xa}) &
(ALL (x::'q_60416 => 'q_60530) (xa::'q_60416 => bool) xb::'q_60416 => bool.
    support u_4371 x (xa Un xb) =
    support u_4371 x xa Un support u_4371 x xb) &
(ALL (x::'q_60454 => 'q_60530) (xa::'q_60454 => bool) xb::'q_60454 => bool.
    support u_4371 x (xa Int xb) =
    support u_4371 x xa Int support u_4371 x xb) &
(ALL (x::'q_60492 => 'q_60530) (xa::'q_60492 => bool) xb::'q_60492 => bool.
    support u_4371 x (xa - xb) =
    support u_4371 x xa - support u_4371 x xb) &
(ALL (x::'q_60529 => 'q_60520) (xa::'q_60520 => 'q_60530)
    xb::'q_60529 => bool.
    support u_4371 xa (x ` xb) = x ` support u_4371 (xa o x) xb)"
  by (import hollight SUPPORT_CLAUSES)

lemma SUPPORT_DELTA: "support (x::'q_60556 => 'q_60556 => 'q_60556)
 (%xa::'q_60584.
     if xa = (xc::'q_60584) then (xb::'q_60584 => 'q_60556) xa
     else neutral x)
 (xa::'q_60584 => bool) =
(if xc : xa then support x xb {xc} else {})"
  by (import hollight SUPPORT_DELTA)

lemma FINITE_SUPPORT_DELTA: "finite
 (support (x::'q_60605 => 'q_60605 => 'q_60605)
   (%xc::'q_60614.
       if xc = (xb::'q_60614) then (xa::'q_60614 => 'q_60605) xc
       else neutral x)
   (s::'q_60614 => bool))"
  by (import hollight FINITE_SUPPORT_DELTA)

lemma ITERATE_SUPPORT: "iterate (x::'q_60630 => 'q_60630 => 'q_60630)
 (support x (xa::'q_60642 => 'q_60630) (xb::'q_60642 => bool)) xa =
iterate x xb xa"
  by (import hollight ITERATE_SUPPORT)

lemma ITERATE_EXPAND_CASES: "iterate (x::'q_60661 => 'q_60661 => 'q_60661) (xb::'q_60667 => bool)
 (xa::'q_60667 => 'q_60661) =
(if finite (support x xa xb) then iterate x (support x xa xb) xa
 else neutral x)"
  by (import hollight ITERATE_EXPAND_CASES)

lemma ITERATE_CLAUSES_GEN: "monoidal (u_4371::'B => 'B => 'B)
==> (ALL f::'A => 'B. iterate u_4371 {} f = neutral u_4371) &
    (ALL (f::'A => 'B) (x::'A) s::'A => bool.
        monoidal u_4371 & finite (support u_4371 f s) -->
        iterate u_4371 (insert x s) f =
        (if x : s then iterate u_4371 s f
         else u_4371 (f x) (iterate u_4371 s f)))"
  by (import hollight ITERATE_CLAUSES_GEN)

lemma ITERATE_CLAUSES: "monoidal (x::'q_60857 => 'q_60857 => 'q_60857)
==> (ALL f::'q_60815 => 'q_60857. iterate x {} f = neutral x) &
    (ALL (f::'q_60859 => 'q_60857) (xa::'q_60859) s::'q_60859 => bool.
        finite s -->
        iterate x (insert xa s) f =
        (if xa : s then iterate x s f else x (f xa) (iterate x s f)))"
  by (import hollight ITERATE_CLAUSES)

lemma ITERATE_UNION: "[| monoidal (u_4371::'q_60945 => 'q_60945 => 'q_60945);
   finite (s::'q_60930 => bool) &
   finite (x::'q_60930 => bool) & s Int x = {} |]
==> iterate u_4371 (s Un x) (f::'q_60930 => 'q_60945) =
    u_4371 (iterate u_4371 s f) (iterate u_4371 x f)"
  by (import hollight ITERATE_UNION)

lemma ITERATE_UNION_GEN: "[| monoidal (x::'B => 'B => 'B);
   finite (support x (xa::'A => 'B) (xb::'A => bool)) &
   finite (support x xa (xc::'A => bool)) &
   support x xa xb Int support x xa xc = {} |]
==> iterate x (xb Un xc) xa = x (iterate x xb xa) (iterate x xc xa)"
  by (import hollight ITERATE_UNION_GEN)

lemma ITERATE_DIFF: "[| monoidal (u::'q_61087 => 'q_61087 => 'q_61087);
   finite (s::'q_61083 => bool) & (t::'q_61083 => bool) <= s |]
==> u (iterate u (s - t) (f::'q_61083 => 'q_61087)) (iterate u t f) =
    iterate u s f"
  by (import hollight ITERATE_DIFF)

lemma ITERATE_DIFF_GEN: "[| monoidal (x::'B => 'B => 'B);
   finite (support x (xa::'A => 'B) (xb::'A => bool)) &
   support x xa (xc::'A => bool) <= support x xa xb |]
==> x (iterate x (xb - xc) xa) (iterate x xc xa) = iterate x xb xa"
  by (import hollight ITERATE_DIFF_GEN)

lemma ITERATE_INCL_EXCL: "[| monoidal (u_4371::'q_61316 => 'q_61316 => 'q_61316);
   finite (s::'q_61298 => bool) & finite (t::'q_61298 => bool) |]
==> u_4371 (iterate u_4371 s (f::'q_61298 => 'q_61316))
     (iterate u_4371 t f) =
    u_4371 (iterate u_4371 (s Un t) f) (iterate u_4371 (s Int t) f)"
  by (import hollight ITERATE_INCL_EXCL)

lemma ITERATE_CLOSED: "[| monoidal (u_4371::'B => 'B => 'B);
   (P::'B => bool) (neutral u_4371) &
   (ALL (x::'B) y::'B. P x & P y --> P (u_4371 x y));
   !!x::'A.
      x : (s::'A => bool) & (f::'A => 'B) x ~= neutral u_4371 ==> P (f x) |]
==> P (iterate u_4371 s f)"
  by (import hollight ITERATE_CLOSED)

lemma ITERATE_RELATED: "[| monoidal (u_4371::'B => 'B => 'B);
   (R::'B => 'B => bool) (neutral u_4371) (neutral u_4371) &
   (ALL (x1::'B) (y1::'B) (x2::'B) y2::'B.
       R x1 x2 & R y1 y2 --> R (u_4371 x1 y1) (u_4371 x2 y2));
   finite (x::'A => bool) &
   (ALL xa::'A. xa : x --> R ((f::'A => 'B) xa) ((g::'A => 'B) xa)) |]
==> R (iterate u_4371 x f) (iterate u_4371 x g)"
  by (import hollight ITERATE_RELATED)

lemma ITERATE_EQ_NEUTRAL: "[| monoidal (u_4371::'B => 'B => 'B);
   !!x::'A. x : (s::'A => bool) ==> (f::'A => 'B) x = neutral u_4371 |]
==> iterate u_4371 s f = neutral u_4371"
  by (import hollight ITERATE_EQ_NEUTRAL)

lemma ITERATE_SING: "monoidal (x::'B => 'B => 'B) ==> iterate x {xa::'A} (f::'A => 'B) = f xa"
  by (import hollight ITERATE_SING)

lemma ITERATE_DELETE: "[| monoidal (u::'B => 'B => 'B); finite (s::'A => bool) & (a::'A) : s |]
==> u ((f::'A => 'B) a) (iterate u (s - {a}) f) = iterate u s f"
  by (import hollight ITERATE_DELETE)

lemma ITERATE_DELTA: "monoidal (u_4371::'q_61672 => 'q_61672 => 'q_61672)
==> iterate u_4371 (xb::'q_61691 => bool)
     (%xb::'q_61691.
         if xb = (xa::'q_61691) then (x::'q_61691 => 'q_61672) xb
         else neutral u_4371) =
    (if xa : xb then x xa else neutral u_4371)"
  by (import hollight ITERATE_DELTA)

lemma ITERATE_IMAGE: "[| monoidal (u_4371::'C => 'C => 'C);
   !!(x::'A) y::'A.
      x : (s::'A => bool) & y : s & (f::'A => 'B) x = f y ==> x = y |]
==> iterate u_4371 (f ` s) (g::'B => 'C) = iterate u_4371 s (g o f)"
  by (import hollight ITERATE_IMAGE)

lemma ITERATE_BIJECTION: "[| monoidal (u_4371::'B => 'B => 'B);
   (ALL x::'A. x : (s::'A => bool) --> (p::'A => 'A) x : s) &
   (ALL y::'A. y : s --> (EX! x::'A. x : s & p x = y)) |]
==> iterate u_4371 s (f::'A => 'B) = iterate u_4371 s (f o p)"
  by (import hollight ITERATE_BIJECTION)

lemma ITERATE_ITERATE_PRODUCT: "[| monoidal (u_4371::'C => 'C => 'C);
   finite (x::'A => bool) &
   (ALL i::'A. i : x --> finite ((xa::'A => 'B => bool) i)) |]
==> iterate u_4371 x
     (%i::'A. iterate u_4371 (xa i) ((xb::'A => 'B => 'C) i)) =
    iterate u_4371
     {u::'A * 'B. EX (i::'A) j::'B. (i : x & j : xa i) & u = (i, j)}
     (SOME f::'A * 'B => 'C. ALL (i::'A) j::'B. f (i, j) = xb i j)"
  by (import hollight ITERATE_ITERATE_PRODUCT)

lemma ITERATE_EQ: "[| monoidal (u_4371::'B => 'B => 'B);
   !!x::'A. x : (s::'A => bool) ==> (f::'A => 'B) x = (g::'A => 'B) x |]
==> iterate u_4371 s f = iterate u_4371 s g"
  by (import hollight ITERATE_EQ)

lemma ITERATE_EQ_GENERAL: "[| monoidal (u_4371::'C => 'C => 'C);
   (ALL y::'B.
       y : (t::'B => bool) -->
       (EX! x::'A. x : (s::'A => bool) & (h::'A => 'B) x = y)) &
   (ALL x::'A. x : s --> h x : t & (g::'B => 'C) (h x) = (f::'A => 'C) x) |]
==> iterate u_4371 s f = iterate u_4371 t g"
  by (import hollight ITERATE_EQ_GENERAL)

lemma ITERATE_EQ_GENERAL_INVERSES: "[| monoidal (u_4371::'C => 'C => 'C);
   (ALL y::'B.
       y : (t::'B => bool) -->
       (k::'B => 'A) y : (s::'A => bool) & (h::'A => 'B) (k y) = y) &
   (ALL x::'A.
       x : s -->
       h x : t & k (h x) = x & (g::'B => 'C) (h x) = (f::'A => 'C) x) |]
==> iterate u_4371 s f = iterate u_4371 t g"
  by (import hollight ITERATE_EQ_GENERAL_INVERSES)

lemma ITERATE_INJECTION: "[| monoidal (u_4371::'B => 'B => 'B);
   finite (s::'A => bool) &
   (ALL x::'A. x : s --> (p::'A => 'A) x : s) &
   (ALL (x::'A) y::'A. x : s & y : s & p x = p y --> x = y) |]
==> iterate u_4371 s ((f::'A => 'B) o p) = iterate u_4371 s f"
  by (import hollight ITERATE_INJECTION)

lemma ITERATE_UNION_NONZERO: "[| monoidal (u_4371::'B => 'B => 'B);
   finite (s::'A => bool) &
   finite (t::'A => bool) &
   (ALL x::'A. x : s Int t --> (f::'A => 'B) x = neutral u_4371) |]
==> iterate u_4371 (s Un t) f =
    u_4371 (iterate u_4371 s f) (iterate u_4371 t f)"
  by (import hollight ITERATE_UNION_NONZERO)

lemma ITERATE_OP: "[| monoidal (u_4371::'q_62649 => 'q_62649 => 'q_62649);
   finite (s::'q_62648 => bool) |]
==> iterate u_4371 s
     (%x::'q_62648.
         u_4371 ((f::'q_62648 => 'q_62649) x)
          ((g::'q_62648 => 'q_62649) x)) =
    u_4371 (iterate u_4371 s f) (iterate u_4371 s g)"
  by (import hollight ITERATE_OP)

lemma ITERATE_SUPERSET: "[| monoidal (u_4371::'B => 'B => 'B);
   (u::'A => bool) <= (v::'A => bool) &
   (ALL x::'A. x : v & x ~: u --> (f::'A => 'B) x = neutral u_4371) |]
==> iterate u_4371 v f = iterate u_4371 u f"
  by (import hollight ITERATE_SUPERSET)

lemma ITERATE_IMAGE_NONZERO: "[| monoidal (u_4371::'C => 'C => 'C);
   finite (x::'A => bool) &
   (ALL (xa::'A) y::'A.
       xa : x & y : x & xa ~= y & (f::'A => 'B) xa = f y -->
       (g::'B => 'C) (f xa) = neutral u_4371) |]
==> iterate u_4371 (f ` x) g = iterate u_4371 x (g o f)"
  by (import hollight ITERATE_IMAGE_NONZERO)

lemma ITERATE_CASES: "[| monoidal (u_4371::'B => 'B => 'B); finite (s::'A => bool) |]
==> iterate u_4371 s
     (%x::'A.
         if (P::'A => bool) x then (f::'A => 'B) x else (g::'A => 'B) x) =
    u_4371 (iterate u_4371 {u::'A. EX x::'A. (x : s & P x) & u = x} f)
     (iterate u_4371 {u::'A. EX x::'A. (x : s & ~ P x) & u = x} g)"
  by (import hollight ITERATE_CASES)

lemma ITERATE_OP_GEN: "[| monoidal (u_4371::'B => 'B => 'B);
   finite (support u_4371 (f::'A => 'B) (s::'A => bool)) &
   finite (support u_4371 (g::'A => 'B) s) |]
==> iterate u_4371 s (%x::'A. u_4371 (f x) (g x)) =
    u_4371 (iterate u_4371 s f) (iterate u_4371 s g)"
  by (import hollight ITERATE_OP_GEN)

lemma ITERATE_CLAUSES_NUMSEG: "monoidal (x::'q_63246 => 'q_63246 => 'q_63246)
==> (ALL xa::nat.
        iterate x {xa..0::nat} (f::nat => 'q_63246) =
        (if xa = (0::nat) then f (0::nat) else neutral x)) &
    (ALL (xa::nat) xb::nat.
        iterate x {xa..Suc xb} f =
        (if xa <= Suc xb then x (iterate x {xa..xb} f) (f (Suc xb))
         else iterate x {xa..xb} f))"
  by (import hollight ITERATE_CLAUSES_NUMSEG)

lemma ITERATE_PAIR: "monoidal (u_4371::'q_63421 => 'q_63421 => 'q_63421)
==> iterate u_4371 {(2::nat) * (m::nat)..(2::nat) * (n::nat) + (1::nat)}
     (f::nat => 'q_63421) =
    iterate u_4371 {m..n}
     (%i::nat. u_4371 (f ((2::nat) * i)) (f ((2::nat) * i + (1::nat))))"
  by (import hollight ITERATE_PAIR)

definition
  nsum :: "('q_63439 => bool) => ('q_63439 => nat) => nat"  where
  "(op ==::(('q_63439::type => bool) => ('q_63439::type => nat) => nat)
        => (('q_63439::type => bool) => ('q_63439::type => nat) => nat)
           => prop)
 (nsum::('q_63439::type => bool) => ('q_63439::type => nat) => nat)
 ((iterate::(nat => nat => nat)
            => ('q_63439::type => bool) => ('q_63439::type => nat) => nat)
   (op +::nat => nat => nat))"

lemma DEF_nsum: "(op =::(('q_63439::type => bool) => ('q_63439::type => nat) => nat)
       => (('q_63439::type => bool) => ('q_63439::type => nat) => nat)
          => bool)
 (nsum::('q_63439::type => bool) => ('q_63439::type => nat) => nat)
 ((iterate::(nat => nat => nat)
            => ('q_63439::type => bool) => ('q_63439::type => nat) => nat)
   (op +::nat => nat => nat))"
  by (import hollight DEF_nsum)

lemma NEUTRAL_ADD: "neutral op + = (0::nat)"
  by (import hollight NEUTRAL_ADD)

lemma NEUTRAL_MUL: "neutral op * = (1::nat)"
  by (import hollight NEUTRAL_MUL)

lemma MONOIDAL_ADD: "(monoidal::(nat => nat => nat) => bool) (op +::nat => nat => nat)"
  by (import hollight MONOIDAL_ADD)

lemma MONOIDAL_MUL: "(monoidal::(nat => nat => nat) => bool) (op *::nat => nat => nat)"
  by (import hollight MONOIDAL_MUL)

lemma NSUM_CLAUSES: "(ALL x::'q_63477 => nat. nsum {} x = (0::nat)) &
(ALL (x::'q_63516) (xa::'q_63516 => nat) xb::'q_63516 => bool.
    finite xb -->
    nsum (insert x xb) xa =
    (if x : xb then nsum xb xa else xa x + nsum xb xa))"
  by (import hollight NSUM_CLAUSES)

lemma NSUM_UNION: "finite (xa::'q_63542 => bool) &
finite (xb::'q_63542 => bool) & xa Int xb = {}
==> nsum (xa Un xb) (x::'q_63542 => nat) = nsum xa x + nsum xb x"
  by (import hollight NSUM_UNION)

lemma NSUM_DIFF: "finite (s::'q_63597 => bool) & (t::'q_63597 => bool) <= s
==> nsum (s - t) (f::'q_63597 => nat) = nsum s f - nsum t f"
  by (import hollight NSUM_DIFF)

lemma NSUM_INCL_EXCL: "finite (x::'A => bool) & finite (xa::'A => bool)
==> nsum x (xb::'A => nat) + nsum xa xb =
    nsum (x Un xa) xb + nsum (x Int xa) xb"
  by (import hollight NSUM_INCL_EXCL)

lemma NSUM_SUPPORT: "nsum (support op + (x::'q_63686 => nat) (xa::'q_63686 => bool)) x =
nsum xa x"
  by (import hollight NSUM_SUPPORT)

lemma NSUM_ADD: "finite (xb::'q_63720 => bool)
==> nsum xb
     (%xb::'q_63720. (x::'q_63720 => nat) xb + (xa::'q_63720 => nat) xb) =
    nsum xb x + nsum xb xa"
  by (import hollight NSUM_ADD)

lemma NSUM_ADD_GEN: "finite
 {xa::'q_63807.
  EX xc::'q_63807.
     (xc : (xb::'q_63807 => bool) & (x::'q_63807 => nat) xc ~= (0::nat)) &
     xa = xc} &
finite
 {x::'q_63807.
  EX xc::'q_63807.
     (xc : xb & (xa::'q_63807 => nat) xc ~= (0::nat)) & x = xc}
==> nsum xb (%xb::'q_63807. x xb + xa xb) = nsum xb x + nsum xb xa"
  by (import hollight NSUM_ADD_GEN)

lemma NSUM_EQ_0: "(!!xb::'A. xb : (xa::'A => bool) ==> (x::'A => nat) xb = (0::nat))
==> nsum xa x = (0::nat)"
  by (import hollight NSUM_EQ_0)

lemma NSUM_0: "nsum (x::'A => bool) (%n::'A. 0::nat) = (0::nat)"
  by (import hollight NSUM_0)

lemma NSUM_LMUL: "nsum (s::'A => bool) (%x::'A. (c::nat) * (f::'A => nat) x) = c * nsum s f"
  by (import hollight NSUM_LMUL)

lemma NSUM_RMUL: "nsum (xb::'A => bool) (%xb::'A. (x::'A => nat) xb * (xa::nat)) =
nsum xb x * xa"
  by (import hollight NSUM_RMUL)

lemma NSUM_LE: "finite (xb::'q_63997 => bool) &
(ALL xc::'q_63997.
    xc : xb --> (x::'q_63997 => nat) xc <= (xa::'q_63997 => nat) xc)
==> nsum xb x <= nsum xb xa"
  by (import hollight NSUM_LE)

lemma NSUM_LT: "finite (s::'A => bool) &
(ALL x::'A. x : s --> (f::'A => nat) x <= (g::'A => nat) x) &
(EX x::'A. x : s & f x < g x)
==> nsum s f < nsum s g"
  by (import hollight NSUM_LT)

lemma NSUM_LT_ALL: "finite (s::'q_64119 => bool) &
s ~= {} &
(ALL x::'q_64119. x : s --> (f::'q_64119 => nat) x < (g::'q_64119 => nat) x)
==> nsum s f < nsum s g"
  by (import hollight NSUM_LT_ALL)

lemma NSUM_EQ: "(!!xc::'q_64157.
    xc : (xb::'q_64157 => bool)
    ==> (x::'q_64157 => nat) xc = (xa::'q_64157 => nat) xc)
==> nsum xb x = nsum xb xa"
  by (import hollight NSUM_EQ)

lemma NSUM_CONST: "finite (s::'q_64187 => bool) ==> nsum s (%n::'q_64187. c::nat) = CARD s * c"
  by (import hollight NSUM_CONST)

lemma NSUM_POS_BOUND: "[| finite (x::'A => bool) & nsum x (f::'A => nat) <= (b::nat);
   (xa::'A) : x |]
==> f xa <= b"
  by (import hollight NSUM_POS_BOUND)

lemma NSUM_EQ_0_IFF: "finite (s::'q_64296 => bool)
==> (nsum s (f::'q_64296 => nat) = (0::nat)) =
    (ALL x::'q_64296. x : s --> f x = (0::nat))"
  by (import hollight NSUM_EQ_0_IFF)

lemma NSUM_DELETE: "finite (xa::'q_64325 => bool) & (xb::'q_64325) : xa
==> (x::'q_64325 => nat) xb + nsum (xa - {xb}) x = nsum xa x"
  by (import hollight NSUM_DELETE)

lemma NSUM_SING: "nsum {xa::'q_64354} (x::'q_64354 => nat) = x xa"
  by (import hollight NSUM_SING)

lemma NSUM_DELTA: "nsum (x::'A => bool) (%x::'A. if x = (xa::'A) then b::nat else (0::nat)) =
(if xa : x then b else (0::nat))"
  by (import hollight NSUM_DELTA)

lemma NSUM_SWAP: "finite (x::'A => bool) & finite (xa::'B => bool)
==> nsum x (%i::'A. nsum xa ((f::'A => 'B => nat) i)) =
    nsum xa (%j::'B. nsum x (%i::'A. f i j))"
  by (import hollight NSUM_SWAP)

lemma NSUM_IMAGE: "(!!(xa::'q_64490) y::'q_64490.
    xa : (xb::'q_64490 => bool) &
    y : xb & (x::'q_64490 => 'q_64466) xa = x y
    ==> xa = y)
==> nsum (x ` xb) (xa::'q_64466 => nat) = nsum xb (xa o x)"
  by (import hollight NSUM_IMAGE)

lemma NSUM_SUPERSET: "(xa::'A => bool) <= (xb::'A => bool) &
(ALL xc::'A. xc : xb & xc ~: xa --> (x::'A => nat) xc = (0::nat))
==> nsum xb x = nsum xa x"
  by (import hollight NSUM_SUPERSET)

lemma NSUM_UNION_RZERO: "finite (u::'A => bool) &
(ALL x::'A. x : (v::'A => bool) & x ~: u --> (f::'A => nat) x = (0::nat))
==> nsum (u Un v) f = nsum u f"
  by (import hollight NSUM_UNION_RZERO)

lemma NSUM_UNION_LZERO: "finite (v::'A => bool) &
(ALL x::'A. x : (u::'A => bool) & x ~: v --> (f::'A => nat) x = (0::nat))
==> nsum (u Un v) f = nsum v f"
  by (import hollight NSUM_UNION_LZERO)

lemma NSUM_RESTRICT: "finite (s::'q_64681 => bool)
==> nsum s
     (%x::'q_64681. if x : s then (f::'q_64681 => nat) x else (0::nat)) =
    nsum s f"
  by (import hollight NSUM_RESTRICT)

lemma NSUM_BOUND: "finite (x::'A => bool) &
(ALL xc::'A. xc : x --> (xa::'A => nat) xc <= (xb::nat))
==> nsum x xa <= CARD x * xb"
  by (import hollight NSUM_BOUND)

lemma NSUM_BOUND_GEN: "finite (x::'A => bool) &
x ~= {} & (ALL xa::'A. xa : x --> (f::'A => nat) xa <= (b::nat) div CARD x)
==> nsum x f <= b"
  by (import hollight NSUM_BOUND_GEN)

lemma NSUM_BOUND_LT: "finite (s::'A => bool) &
(ALL x::'A. x : s --> (f::'A => nat) x <= (b::nat)) &
(EX x::'A. x : s & f x < b)
==> nsum s f < CARD s * b"
  by (import hollight NSUM_BOUND_LT)

lemma NSUM_BOUND_LT_ALL: "finite (s::'q_64899 => bool) &
s ~= {} & (ALL x::'q_64899. x : s --> (f::'q_64899 => nat) x < (b::nat))
==> nsum s f < CARD s * b"
  by (import hollight NSUM_BOUND_LT_ALL)

lemma NSUM_BOUND_LT_GEN: "finite (s::'A => bool) &
s ~= {} & (ALL x::'A. x : s --> (f::'A => nat) x < (b::nat) div CARD s)
==> nsum s f < b"
  by (import hollight NSUM_BOUND_LT_GEN)

lemma NSUM_UNION_EQ: "finite (u::'q_65000 => bool) &
(s::'q_65000 => bool) Int (t::'q_65000 => bool) = {} & s Un t = u
==> nsum s (f::'q_65000 => nat) + nsum t f = nsum u f"
  by (import hollight NSUM_UNION_EQ)

lemma NSUM_EQ_SUPERSET: "finite (t::'A => bool) &
t <= (s::'A => bool) &
(ALL x::'A. x : t --> (f::'A => nat) x = (g::'A => nat) x) &
(ALL x::'A. x : s & x ~: t --> f x = (0::nat))
==> nsum s f = nsum t g"
  by (import hollight NSUM_EQ_SUPERSET)

lemma NSUM_RESTRICT_SET: "nsum
 {u::'A. EX xb::'A. (xb : (xa::'A => bool) & (x::'A => bool) xb) & u = xb}
 (xb::'A => nat) =
nsum xa (%xa::'A. if x xa then xb xa else (0::nat))"
  by (import hollight NSUM_RESTRICT_SET)

lemma NSUM_NSUM_RESTRICT: "finite (s::'q_65257 => bool) & finite (t::'q_65256 => bool)
==> nsum s
     (%x::'q_65257.
         nsum
          {u::'q_65256.
           EX y::'q_65256.
              (y : t & (R::'q_65257 => 'q_65256 => bool) x y) & u = y}
          ((f::'q_65257 => 'q_65256 => nat) x)) =
    nsum t
     (%y::'q_65256.
         nsum {u::'q_65257. EX x::'q_65257. (x : s & R x y) & u = x}
          (%x::'q_65257. f x y))"
  by (import hollight NSUM_NSUM_RESTRICT)

lemma CARD_EQ_NSUM: "finite (x::'q_65276 => bool) ==> CARD x = nsum x (%x::'q_65276. 1::nat)"
  by (import hollight CARD_EQ_NSUM)

lemma NSUM_MULTICOUNT_GEN: "finite (s::'A => bool) &
finite (t::'B => bool) &
(ALL j::'B.
    j : t -->
    CARD {u::'A. EX i::'A. (i : s & (R::'A => 'B => bool) i j) & u = i} =
    (k::'B => nat) j)
==> nsum s (%i::'A. CARD {u::'B. EX j::'B. (j : t & R i j) & u = j}) =
    nsum t k"
  by (import hollight NSUM_MULTICOUNT_GEN)

lemma NSUM_MULTICOUNT: "finite (s::'A => bool) &
finite (t::'B => bool) &
(ALL j::'B.
    j : t -->
    CARD {u::'A. EX i::'A. (i : s & (R::'A => 'B => bool) i j) & u = i} =
    (k::nat))
==> nsum s (%i::'A. CARD {u::'B. EX j::'B. (j : t & R i j) & u = j}) =
    k * CARD t"
  by (import hollight NSUM_MULTICOUNT)

lemma NSUM_IMAGE_GEN: "finite (s::'A => bool)
==> nsum s (g::'A => nat) =
    nsum ((f::'A => 'B) ` s)
     (%y::'B. nsum {u::'A. EX x::'A. (x : s & f x = y) & u = x} g)"
  by (import hollight NSUM_IMAGE_GEN)

lemma NSUM_GROUP: "finite (s::'A => bool) & (f::'A => 'B) ` s <= (t::'B => bool)
==> nsum t
     (%y::'B.
         nsum {u::'A. EX x::'A. (x : s & f x = y) & u = x} (g::'A => nat)) =
    nsum s g"
  by (import hollight NSUM_GROUP)

lemma NSUM_SUBSET: "finite (u::'A => bool) &
finite (v::'A => bool) &
(ALL x::'A. x : u - v --> (f::'A => nat) x = (0::nat))
==> nsum u f <= nsum v f"
  by (import hollight NSUM_SUBSET)

lemma NSUM_SUBSET_SIMPLE: "finite (v::'q_65804 => bool) & (u::'q_65804 => bool) <= v
==> nsum u (f::'q_65804 => nat) <= nsum v f"
  by (import hollight NSUM_SUBSET_SIMPLE)

lemma NSUM_IMAGE_NONZERO: "finite (xb::'A => bool) &
(ALL (xc::'A) xd::'A.
    xc : xb & xd : xb & xc ~= xd & (xa::'A => 'B) xc = xa xd -->
    (x::'B => nat) (xa xc) = (0::nat))
==> nsum (xa ` xb) x = nsum xb (x o xa)"
  by (import hollight NSUM_IMAGE_NONZERO)

lemma NSUM_BIJECTION: "(ALL x::'A. x : (xb::'A => bool) --> (xa::'A => 'A) x : xb) &
(ALL y::'A. y : xb --> (EX! x::'A. x : xb & xa x = y))
==> nsum xb (x::'A => nat) = nsum xb (x o xa)"
  by (import hollight NSUM_BIJECTION)

lemma NSUM_NSUM_PRODUCT: "finite (x::'A => bool) &
(ALL i::'A. i : x --> finite ((xa::'A => 'B => bool) i))
==> nsum x (%x::'A. nsum (xa x) ((xb::'A => 'B => nat) x)) =
    nsum {u::'A * 'B. EX (i::'A) j::'B. (i : x & j : xa i) & u = (i, j)}
     (SOME f::'A * 'B => nat. ALL (i::'A) j::'B. f (i, j) = xb i j)"
  by (import hollight NSUM_NSUM_PRODUCT)

lemma NSUM_EQ_GENERAL: "(ALL y::'B.
    y : (xa::'B => bool) -->
    (EX! xa::'A. xa : (x::'A => bool) & (xd::'A => 'B) xa = y)) &
(ALL xe::'A.
    xe : x --> xd xe : xa & (xc::'B => nat) (xd xe) = (xb::'A => nat) xe)
==> nsum x xb = nsum xa xc"
  by (import hollight NSUM_EQ_GENERAL)

lemma NSUM_EQ_GENERAL_INVERSES: "(ALL y::'B.
    y : (xa::'B => bool) -->
    (xe::'B => 'A) y : (x::'A => bool) & (xd::'A => 'B) (xe y) = y) &
(ALL xf::'A.
    xf : x -->
    xd xf : xa &
    xe (xd xf) = xf & (xc::'B => nat) (xd xf) = (xb::'A => nat) xf)
==> nsum x xb = nsum xa xc"
  by (import hollight NSUM_EQ_GENERAL_INVERSES)

lemma NSUM_INJECTION: "finite (xb::'q_66274 => bool) &
(ALL x::'q_66274. x : xb --> (xa::'q_66274 => 'q_66274) x : xb) &
(ALL (x::'q_66274) y::'q_66274. x : xb & y : xb & xa x = xa y --> x = y)
==> nsum xb ((x::'q_66274 => nat) o xa) = nsum xb x"
  by (import hollight NSUM_INJECTION)

lemma NSUM_UNION_NONZERO: "finite (xa::'q_66317 => bool) &
finite (xb::'q_66317 => bool) &
(ALL xc::'q_66317. xc : xa Int xb --> (x::'q_66317 => nat) xc = (0::nat))
==> nsum (xa Un xb) x = nsum xa x + nsum xb x"
  by (import hollight NSUM_UNION_NONZERO)

lemma NSUM_UNIONS_NONZERO: "finite (x::('A => bool) => bool) &
(ALL t::'A => bool. t : x --> finite t) &
(ALL (t1::'A => bool) (t2::'A => bool) xa::'A.
    t1 : x & t2 : x & t1 ~= t2 & xa : t1 & xa : t2 -->
    (f::'A => nat) xa = (0::nat))
==> nsum (Union x) f = nsum x (%t::'A => bool. nsum t f)"
  by (import hollight NSUM_UNIONS_NONZERO)

lemma NSUM_CASES: "finite (x::'A => bool)
==> nsum x
     (%x::'A.
         if (xa::'A => bool) x then (xb::'A => nat) x
         else (xc::'A => nat) x) =
    nsum {u::'A. EX xb::'A. (xb : x & xa xb) & u = xb} xb +
    nsum {u::'A. EX xb::'A. (xb : x & ~ xa xb) & u = xb} xc"
  by (import hollight NSUM_CASES)

lemma NSUM_CLOSED: "(P::nat => bool) (0::nat) &
(ALL (x::nat) y::nat. P x & P y --> P (x + y)) &
(ALL a::'A. a : (s::'A => bool) --> P ((f::'A => nat) a))
==> P (nsum s f)"
  by (import hollight NSUM_CLOSED)

lemma NSUM_ADD_NUMSEG: "nsum {xb::nat..xc::nat} (%i::nat. (x::nat => nat) i + (xa::nat => nat) i) =
nsum {xb..xc} x + nsum {xb..xc} xa"
  by (import hollight NSUM_ADD_NUMSEG)

lemma NSUM_LE_NUMSEG: "(!!i::nat.
    (xb::nat) <= i & i <= (xc::nat)
    ==> (x::nat => nat) i <= (xa::nat => nat) i)
==> nsum {xb..xc} x <= nsum {xb..xc} xa"
  by (import hollight NSUM_LE_NUMSEG)

lemma NSUM_EQ_NUMSEG: "(!!i::nat.
    (m::nat) <= i & i <= (n::nat) ==> (f::nat => nat) i = (g::nat => nat) i)
==> nsum {m..n} f = nsum {m..n} g"
  by (import hollight NSUM_EQ_NUMSEG)

lemma NSUM_CONST_NUMSEG: "nsum {xa..xb} (%n. x) = (xb + 1 - xa) * x"
  by (import hollight NSUM_CONST_NUMSEG)

lemma NSUM_EQ_0_NUMSEG: "(!!i::nat. (m::nat) <= i & i <= (n::nat) ==> (x::nat => nat) i = (0::nat))
==> nsum {m..n} x = (0::nat)"
  by (import hollight NSUM_EQ_0_NUMSEG)

lemma NSUM_EQ_0_IFF_NUMSEG: "(nsum {xa::nat..xb::nat} (x::nat => nat) = (0::nat)) =
(ALL i::nat. xa <= i & i <= xb --> x i = (0::nat))"
  by (import hollight NSUM_EQ_0_IFF_NUMSEG)

lemma NSUM_TRIV_NUMSEG: "(n::nat) < (m::nat) ==> nsum {m..n} (f::nat => nat) = (0::nat)"
  by (import hollight NSUM_TRIV_NUMSEG)

lemma NSUM_SING_NUMSEG: "nsum {xa::nat..xa} (x::nat => nat) = x xa"
  by (import hollight NSUM_SING_NUMSEG)

lemma NSUM_CLAUSES_NUMSEG: "(ALL m. nsum {m..0} f = (if m = 0 then f 0 else 0)) &
(ALL m n.
    nsum {m..Suc n} f =
    (if m <= Suc n then nsum {m..n} f + f (Suc n) else nsum {m..n} f))"
  by (import hollight NSUM_CLAUSES_NUMSEG)

lemma NSUM_SWAP_NUMSEG: "nsum {a::nat..b::nat}
 (%i::nat. nsum {c::nat..d::nat} ((f::nat => nat => nat) i)) =
nsum {c..d} (%j::nat. nsum {a..b} (%i::nat. f i j))"
  by (import hollight NSUM_SWAP_NUMSEG)

lemma NSUM_ADD_SPLIT: "(xa::nat) <= (xb::nat) + (1::nat)
==> nsum {xa..xb + (xc::nat)} (x::nat => nat) =
    nsum {xa..xb} x + nsum {xb + (1::nat)..xb + xc} x"
  by (import hollight NSUM_ADD_SPLIT)

lemma NSUM_OFFSET: "nsum {(xb::nat) + (x::nat)..(xc::nat) + x} (xa::nat => nat) =
nsum {xb..xc} (%i::nat. xa (i + x))"
  by (import hollight NSUM_OFFSET)

lemma NSUM_OFFSET_0: "(xa::nat) <= (xb::nat)
==> nsum {xa..xb} (x::nat => nat) =
    nsum {0::nat..xb - xa} (%i::nat. x (i + xa))"
  by (import hollight NSUM_OFFSET_0)

lemma NSUM_CLAUSES_LEFT: "(xa::nat) <= (xb::nat)
==> nsum {xa..xb} (x::nat => nat) = x xa + nsum {xa + (1::nat)..xb} x"
  by (import hollight NSUM_CLAUSES_LEFT)

lemma NSUM_CLAUSES_RIGHT: "(0::nat) < (n::nat) & (m::nat) <= n
==> nsum {m..n} (f::nat => nat) = nsum {m..n - (1::nat)} f + f n"
  by (import hollight NSUM_CLAUSES_RIGHT)

lemma NSUM_PAIR: "nsum {(2::nat) * (m::nat)..(2::nat) * (n::nat) + (1::nat)} (f::nat => nat) =
nsum {m..n} (%i::nat. f ((2::nat) * i) + f ((2::nat) * i + (1::nat)))"
  by (import hollight NSUM_PAIR)

lemma CARD_UNIONS: "finite (x::('A => bool) => bool) &
(ALL t::'A => bool. t : x --> finite t) &
(ALL (t::'A => bool) u::'A => bool. t : x & u : x & t ~= u --> t Int u = {})
==> CARD (Union x) = nsum x CARD"
  by (import hollight CARD_UNIONS)

consts
  sum :: "('q_67488 => bool) => ('q_67488 => hollight.real) => hollight.real" 

defs
  sum_def: "(op ==::(('q_67488::type => bool)
         => ('q_67488::type => hollight.real) => hollight.real)
        => (('q_67488::type => bool)
            => ('q_67488::type => hollight.real) => hollight.real)
           => prop)
 (hollight.sum::('q_67488::type => bool)
                => ('q_67488::type => hollight.real) => hollight.real)
 ((iterate::(hollight.real => hollight.real => hollight.real)
            => ('q_67488::type => bool)
               => ('q_67488::type => hollight.real) => hollight.real)
   (real_add::hollight.real => hollight.real => hollight.real))"

lemma DEF_sum: "(op =::(('q_67488::type => bool)
        => ('q_67488::type => hollight.real) => hollight.real)
       => (('q_67488::type => bool)
           => ('q_67488::type => hollight.real) => hollight.real)
          => bool)
 (hollight.sum::('q_67488::type => bool)
                => ('q_67488::type => hollight.real) => hollight.real)
 ((iterate::(hollight.real => hollight.real => hollight.real)
            => ('q_67488::type => bool)
               => ('q_67488::type => hollight.real) => hollight.real)
   (real_add::hollight.real => hollight.real => hollight.real))"
  by (import hollight DEF_sum)

lemma NEUTRAL_REAL_ADD: "neutral real_add = real_of_num 0"
  by (import hollight NEUTRAL_REAL_ADD)

lemma NEUTRAL_REAL_MUL: "neutral real_mul = real_of_num 1"
  by (import hollight NEUTRAL_REAL_MUL)

lemma MONOIDAL_REAL_ADD: "monoidal real_add"
  by (import hollight MONOIDAL_REAL_ADD)

lemma MONOIDAL_REAL_MUL: "monoidal real_mul"
  by (import hollight MONOIDAL_REAL_MUL)

lemma SUM_CLAUSES: "(ALL x::'q_67530 => hollight.real.
    hollight.sum {} x = real_of_num (0::nat)) &
(ALL (x::'q_67571) (xa::'q_67571 => hollight.real) xb::'q_67571 => bool.
    finite xb -->
    hollight.sum (insert x xb) xa =
    (if x : xb then hollight.sum xb xa
     else real_add (xa x) (hollight.sum xb xa)))"
  by (import hollight SUM_CLAUSES)

lemma SUM_UNION: "finite (xa::'q_67597 => bool) &
finite (xb::'q_67597 => bool) & xa Int xb = {}
==> hollight.sum (xa Un xb) (x::'q_67597 => hollight.real) =
    real_add (hollight.sum xa x) (hollight.sum xb x)"
  by (import hollight SUM_UNION)

lemma SUM_DIFF: "finite (xa::'q_67637 => bool) & (xb::'q_67637 => bool) <= xa
==> hollight.sum (xa - xb) (x::'q_67637 => hollight.real) =
    real_sub (hollight.sum xa x) (hollight.sum xb x)"
  by (import hollight SUM_DIFF)

lemma SUM_INCL_EXCL: "finite (x::'A => bool) & finite (xa::'A => bool)
==> real_add (hollight.sum x (xb::'A => hollight.real))
     (hollight.sum xa xb) =
    real_add (hollight.sum (x Un xa) xb) (hollight.sum (x Int xa) xb)"
  by (import hollight SUM_INCL_EXCL)

lemma SUM_SUPPORT: "hollight.sum
 (support real_add (x::'q_67726 => hollight.real) (xa::'q_67726 => bool))
 x =
hollight.sum xa x"
  by (import hollight SUM_SUPPORT)

lemma SUM_ADD: "finite (xb::'q_67760 => bool)
==> hollight.sum xb
     (%xb::'q_67760.
         real_add ((x::'q_67760 => hollight.real) xb)
          ((xa::'q_67760 => hollight.real) xb)) =
    real_add (hollight.sum xb x) (hollight.sum xb xa)"
  by (import hollight SUM_ADD)

lemma SUM_ADD_GEN: "finite
 {xa::'q_67851.
  EX xc::'q_67851.
     (xc : (xb::'q_67851 => bool) &
      (x::'q_67851 => hollight.real) xc ~= real_of_num (0::nat)) &
     xa = xc} &
finite
 {x::'q_67851.
  EX xc::'q_67851.
     (xc : xb &
      (xa::'q_67851 => hollight.real) xc ~= real_of_num (0::nat)) &
     x = xc}
==> hollight.sum xb (%xb::'q_67851. real_add (x xb) (xa xb)) =
    real_add (hollight.sum xb x) (hollight.sum xb xa)"
  by (import hollight SUM_ADD_GEN)

lemma SUM_EQ_0: "(!!xb::'A.
    xb : (xa::'A => bool)
    ==> (x::'A => hollight.real) xb = real_of_num (0::nat))
==> hollight.sum xa x = real_of_num (0::nat)"
  by (import hollight SUM_EQ_0)

lemma SUM_0: "hollight.sum (x::'A => bool) (%n::'A. real_of_num (0::nat)) =
real_of_num (0::nat)"
  by (import hollight SUM_0)

lemma SUM_LMUL: "hollight.sum (s::'A => bool)
 (%x::'A. real_mul (c::hollight.real) ((f::'A => hollight.real) x)) =
real_mul c (hollight.sum s f)"
  by (import hollight SUM_LMUL)

lemma SUM_RMUL: "hollight.sum (xb::'A => bool)
 (%xb::'A. real_mul ((x::'A => hollight.real) xb) (xa::hollight.real)) =
real_mul (hollight.sum xb x) xa"
  by (import hollight SUM_RMUL)

lemma SUM_NEG: "hollight.sum (xa::'q_68051 => bool)
 (%xa::'q_68051. real_neg ((x::'q_68051 => hollight.real) xa)) =
real_neg (hollight.sum xa x)"
  by (import hollight SUM_NEG)

lemma SUM_SUB: "finite (xb::'q_68086 => bool)
==> hollight.sum xb
     (%xb::'q_68086.
         real_sub ((x::'q_68086 => hollight.real) xb)
          ((xa::'q_68086 => hollight.real) xb)) =
    real_sub (hollight.sum xb x) (hollight.sum xb xa)"
  by (import hollight SUM_SUB)

lemma SUM_LE: "finite (xb::'q_68128 => bool) &
(ALL xc::'q_68128.
    xc : xb -->
    real_le ((x::'q_68128 => hollight.real) xc)
     ((xa::'q_68128 => hollight.real) xc))
==> real_le (hollight.sum xb x) (hollight.sum xb xa)"
  by (import hollight SUM_LE)

lemma SUM_LT: "finite (s::'A => bool) &
(ALL x::'A.
    x : s -->
    real_le ((f::'A => hollight.real) x) ((g::'A => hollight.real) x)) &
(EX x::'A. x : s & real_lt (f x) (g x))
==> real_lt (hollight.sum s f) (hollight.sum s g)"
  by (import hollight SUM_LT)

lemma SUM_LT_ALL: "finite (s::'q_68250 => bool) &
s ~= {} &
(ALL x::'q_68250.
    x : s -->
    real_lt ((f::'q_68250 => hollight.real) x)
     ((g::'q_68250 => hollight.real) x))
==> real_lt (hollight.sum s f) (hollight.sum s g)"
  by (import hollight SUM_LT_ALL)

lemma SUM_EQ: "(!!xc::'q_68288.
    xc : (xb::'q_68288 => bool)
    ==> (x::'q_68288 => hollight.real) xc =
        (xa::'q_68288 => hollight.real) xc)
==> hollight.sum xb x = hollight.sum xb xa"
  by (import hollight SUM_EQ)

lemma SUM_ABS: "finite (s::'q_68347 => bool)
==> real_le (real_abs (hollight.sum s (f::'q_68347 => hollight.real)))
     (hollight.sum s (%x::'q_68347. real_abs (f x)))"
  by (import hollight SUM_ABS)

lemma SUM_ABS_LE: "finite (s::'A => bool) &
(ALL x::'A.
    x : s -->
    real_le (real_abs ((f::'A => hollight.real) x))
     ((g::'A => hollight.real) x))
==> real_le (real_abs (hollight.sum s f)) (hollight.sum s g)"
  by (import hollight SUM_ABS_LE)

lemma SUM_CONST: "finite (s::'q_68423 => bool)
==> hollight.sum s (%n::'q_68423. c::hollight.real) =
    real_mul (real_of_num (CARD s)) c"
  by (import hollight SUM_CONST)

lemma SUM_POS_LE: "finite (xa::'q_68465 => bool) &
(ALL xb::'q_68465.
    xb : xa -->
    real_le (real_of_num (0::nat)) ((x::'q_68465 => hollight.real) xb))
==> real_le (real_of_num (0::nat)) (hollight.sum xa x)"
  by (import hollight SUM_POS_LE)

lemma SUM_POS_BOUND: "[| finite (x::'A => bool) &
   (ALL xa::'A.
       xa : x -->
       real_le (real_of_num (0::nat)) ((f::'A => hollight.real) xa)) &
   real_le (hollight.sum x f) (b::hollight.real);
   (xa::'A) : x |]
==> real_le (f xa) b"
  by (import hollight SUM_POS_BOUND)

lemma SUM_POS_EQ_0: "[| finite (xa::'q_68612 => bool) &
   (ALL xb::'q_68612.
       xb : xa -->
       real_le (real_of_num (0::nat)) ((x::'q_68612 => hollight.real) xb)) &
   hollight.sum xa x = real_of_num (0::nat);
   (xb::'q_68612) : xa |]
==> x xb = real_of_num (0::nat)"
  by (import hollight SUM_POS_EQ_0)

lemma SUM_ZERO_EXISTS: "finite (s::'A => bool) &
hollight.sum s (u::'A => hollight.real) = real_of_num (0::nat)
==> (ALL i::'A. i : s --> u i = real_of_num (0::nat)) |
    (EX (j::'A) k::'A.
        j : s &
        real_lt (u j) (real_of_num (0::nat)) &
        k : s & real_gt (u k) (real_of_num (0::nat)))"
  by (import hollight SUM_ZERO_EXISTS)

lemma SUM_DELETE: "finite (xa::'q_68854 => bool) & (xb::'q_68854) : xa
==> hollight.sum (xa - {xb}) (x::'q_68854 => hollight.real) =
    real_sub (hollight.sum xa x) (x xb)"
  by (import hollight SUM_DELETE)

lemma SUM_DELETE_CASES: "finite (s::'q_68907 => bool)
==> hollight.sum (s - {a::'q_68907}) (f::'q_68907 => hollight.real) =
    (if a : s then real_sub (hollight.sum s f) (f a) else hollight.sum s f)"
  by (import hollight SUM_DELETE_CASES)

lemma SUM_SING: "hollight.sum {xa::'q_68930} (x::'q_68930 => hollight.real) = x xa"
  by (import hollight SUM_SING)

lemma SUM_DELTA: "hollight.sum (x::'A => bool)
 (%x::'A. if x = (xa::'A) then b::hollight.real else real_of_num (0::nat)) =
(if xa : x then b else real_of_num (0::nat))"
  by (import hollight SUM_DELTA)

lemma SUM_SWAP: "finite (x::'A => bool) & finite (xa::'B => bool)
==> hollight.sum x
     (%i::'A. hollight.sum xa ((f::'A => 'B => hollight.real) i)) =
    hollight.sum xa (%j::'B. hollight.sum x (%i::'A. f i j))"
  by (import hollight SUM_SWAP)

lemma SUM_IMAGE: "(!!(xa::'q_69070) y::'q_69070.
    xa : (xb::'q_69070 => bool) &
    y : xb & (x::'q_69070 => 'q_69046) xa = x y
    ==> xa = y)
==> hollight.sum (x ` xb) (xa::'q_69046 => hollight.real) =
    hollight.sum xb (xa o x)"
  by (import hollight SUM_IMAGE)

lemma SUM_SUPERSET: "(xa::'A => bool) <= (xb::'A => bool) &
(ALL xc::'A.
    xc : xb & xc ~: xa -->
    (x::'A => hollight.real) xc = real_of_num (0::nat))
==> hollight.sum xb x = hollight.sum xa x"
  by (import hollight SUM_SUPERSET)

lemma SUM_UNION_RZERO: "finite (u::'A => bool) &
(ALL x::'A.
    x : (v::'A => bool) & x ~: u -->
    (f::'A => hollight.real) x = real_of_num (0::nat))
==> hollight.sum (u Un v) f = hollight.sum u f"
  by (import hollight SUM_UNION_RZERO)

lemma SUM_UNION_LZERO: "finite (v::'A => bool) &
(ALL x::'A.
    x : (u::'A => bool) & x ~: v -->
    (f::'A => hollight.real) x = real_of_num (0::nat))
==> hollight.sum (u Un v) f = hollight.sum v f"
  by (import hollight SUM_UNION_LZERO)

lemma SUM_RESTRICT: "finite (s::'q_69267 => bool)
==> hollight.sum s
     (%x::'q_69267.
         if x : s then (f::'q_69267 => hollight.real) x
         else real_of_num (0::nat)) =
    hollight.sum s f"
  by (import hollight SUM_RESTRICT)

lemma SUM_BOUND: "finite (x::'A => bool) &
(ALL xc::'A.
    xc : x --> real_le ((xa::'A => hollight.real) xc) (xb::hollight.real))
==> real_le (hollight.sum x xa) (real_mul (real_of_num (CARD x)) xb)"
  by (import hollight SUM_BOUND)

lemma SUM_BOUND_GEN: "finite (s::'A => bool) &
s ~= {} &
(ALL x::'A.
    x : s -->
    real_le ((f::'A => hollight.real) x)
     (real_div (b::hollight.real) (real_of_num (CARD s))))
==> real_le (hollight.sum s f) b"
  by (import hollight SUM_BOUND_GEN)

lemma SUM_ABS_BOUND: "finite (s::'A => bool) &
(ALL x::'A.
    x : s -->
    real_le (real_abs ((f::'A => hollight.real) x)) (b::hollight.real))
==> real_le (real_abs (hollight.sum s f))
     (real_mul (real_of_num (CARD s)) b)"
  by (import hollight SUM_ABS_BOUND)

lemma SUM_BOUND_LT: "finite (s::'A => bool) &
(ALL x::'A.
    x : s --> real_le ((f::'A => hollight.real) x) (b::hollight.real)) &
(EX x::'A. x : s & real_lt (f x) b)
==> real_lt (hollight.sum s f) (real_mul (real_of_num (CARD s)) b)"
  by (import hollight SUM_BOUND_LT)

lemma SUM_BOUND_LT_ALL: "finite (s::'q_69531 => bool) &
s ~= {} &
(ALL x::'q_69531.
    x : s --> real_lt ((f::'q_69531 => hollight.real) x) (b::hollight.real))
==> real_lt (hollight.sum s f) (real_mul (real_of_num (CARD s)) b)"
  by (import hollight SUM_BOUND_LT_ALL)

lemma SUM_BOUND_LT_GEN: "finite (s::'A => bool) &
s ~= {} &
(ALL x::'A.
    x : s -->
    real_lt ((f::'A => hollight.real) x)
     (real_div (b::hollight.real) (real_of_num (CARD s))))
==> real_lt (hollight.sum s f) b"
  by (import hollight SUM_BOUND_LT_GEN)

lemma SUM_UNION_EQ: "finite (u::'q_69614 => bool) &
(s::'q_69614 => bool) Int (t::'q_69614 => bool) = {} & s Un t = u
==> real_add (hollight.sum s (f::'q_69614 => hollight.real))
     (hollight.sum t f) =
    hollight.sum u f"
  by (import hollight SUM_UNION_EQ)

lemma SUM_EQ_SUPERSET: "finite (t::'A => bool) &
t <= (s::'A => bool) &
(ALL x::'A.
    x : t --> (f::'A => hollight.real) x = (g::'A => hollight.real) x) &
(ALL x::'A. x : s & x ~: t --> f x = real_of_num (0::nat))
==> hollight.sum s f = hollight.sum t g"
  by (import hollight SUM_EQ_SUPERSET)

lemma SUM_RESTRICT_SET: "hollight.sum
 {u::'q_69783.
  EX xb::'q_69783.
     (xb : (xa::'q_69783 => bool) & (x::'q_69783 => bool) xb) & u = xb}
 (xb::'q_69783 => hollight.real) =
hollight.sum xa
 (%xa::'q_69783. if x xa then xb xa else real_of_num (0::nat))"
  by (import hollight SUM_RESTRICT_SET)

lemma SUM_SUM_RESTRICT: "finite (s::'q_69875 => bool) & finite (t::'q_69874 => bool)
==> hollight.sum s
     (%x::'q_69875.
         hollight.sum
          {u::'q_69874.
           EX y::'q_69874.
              (y : t & (R::'q_69875 => 'q_69874 => bool) x y) & u = y}
          ((f::'q_69875 => 'q_69874 => hollight.real) x)) =
    hollight.sum t
     (%y::'q_69874.
         hollight.sum {u::'q_69875. EX x::'q_69875. (x : s & R x y) & u = x}
          (%x::'q_69875. f x y))"
  by (import hollight SUM_SUM_RESTRICT)

lemma CARD_EQ_SUM: "finite (x::'q_69896 => bool)
==> real_of_num (CARD x) =
    hollight.sum x (%x::'q_69896. real_of_num (1::nat))"
  by (import hollight CARD_EQ_SUM)

lemma SUM_MULTICOUNT_GEN: "finite (s::'A => bool) &
finite (t::'B => bool) &
(ALL j::'B.
    j : t -->
    CARD {u::'A. EX i::'A. (i : s & (R::'A => 'B => bool) i j) & u = i} =
    (k::'B => nat) j)
==> hollight.sum s
     (%i::'A.
         real_of_num (CARD {u::'B. EX j::'B. (j : t & R i j) & u = j})) =
    hollight.sum t (%i::'B. real_of_num (k i))"
  by (import hollight SUM_MULTICOUNT_GEN)

lemma SUM_MULTICOUNT: "finite (s::'A => bool) &
finite (t::'B => bool) &
(ALL j::'B.
    j : t -->
    CARD {u::'A. EX i::'A. (i : s & (R::'A => 'B => bool) i j) & u = i} =
    (k::nat))
==> hollight.sum s
     (%i::'A.
         real_of_num (CARD {u::'B. EX j::'B. (j : t & R i j) & u = j})) =
    real_of_num (k * CARD t)"
  by (import hollight SUM_MULTICOUNT)

lemma SUM_IMAGE_GEN: "finite (s::'A => bool)
==> hollight.sum s (g::'A => hollight.real) =
    hollight.sum ((f::'A => 'B) ` s)
     (%y::'B. hollight.sum {u::'A. EX x::'A. (x : s & f x = y) & u = x} g)"
  by (import hollight SUM_IMAGE_GEN)

lemma SUM_GROUP: "finite (s::'A => bool) & (f::'A => 'B) ` s <= (t::'B => bool)
==> hollight.sum t
     (%y::'B.
         hollight.sum {u::'A. EX x::'A. (x : s & f x = y) & u = x}
          (g::'A => hollight.real)) =
    hollight.sum s g"
  by (import hollight SUM_GROUP)

lemma REAL_OF_NUM_SUM: "finite (s::'q_70361 => bool)
==> real_of_num (nsum s (f::'q_70361 => nat)) =
    hollight.sum s (%x::'q_70361. real_of_num (f x))"
  by (import hollight REAL_OF_NUM_SUM)

lemma SUM_SUBSET: "finite (u::'A => bool) &
finite (v::'A => bool) &
(ALL x::'A.
    x : u - v -->
    real_le ((f::'A => hollight.real) x) (real_of_num (0::nat))) &
(ALL x::'A. x : v - u --> real_le (real_of_num (0::nat)) (f x))
==> real_le (hollight.sum u f) (hollight.sum v f)"
  by (import hollight SUM_SUBSET)

lemma SUM_SUBSET_SIMPLE: "finite (v::'A => bool) &
(u::'A => bool) <= v &
(ALL x::'A.
    x : v - u -->
    real_le (real_of_num (0::nat)) ((f::'A => hollight.real) x))
==> real_le (hollight.sum u f) (hollight.sum v f)"
  by (import hollight SUM_SUBSET_SIMPLE)

lemma SUM_IMAGE_NONZERO: "finite (xb::'A => bool) &
(ALL (xc::'A) xd::'A.
    xc : xb & xd : xb & xc ~= xd & (xa::'A => 'B) xc = xa xd -->
    (x::'B => hollight.real) (xa xc) = real_of_num (0::nat))
==> hollight.sum (xa ` xb) x = hollight.sum xb (x o xa)"
  by (import hollight SUM_IMAGE_NONZERO)

lemma SUM_BIJECTION: "(ALL x::'A. x : (xb::'A => bool) --> (xa::'A => 'A) x : xb) &
(ALL y::'A. y : xb --> (EX! x::'A. x : xb & xa x = y))
==> hollight.sum xb (x::'A => hollight.real) = hollight.sum xb (x o xa)"
  by (import hollight SUM_BIJECTION)

lemma SUM_SUM_PRODUCT: "finite (x::'A => bool) &
(ALL i::'A. i : x --> finite ((xa::'A => 'B => bool) i))
==> hollight.sum x
     (%x::'A. hollight.sum (xa x) ((xb::'A => 'B => hollight.real) x)) =
    hollight.sum
     {u::'A * 'B. EX (i::'A) j::'B. (i : x & j : xa i) & u = (i, j)}
     (SOME f::'A * 'B => hollight.real.
         ALL (i::'A) j::'B. f (i, j) = xb i j)"
  by (import hollight SUM_SUM_PRODUCT)

lemma SUM_EQ_GENERAL: "(ALL y::'B.
    y : (xa::'B => bool) -->
    (EX! xa::'A. xa : (x::'A => bool) & (xd::'A => 'B) xa = y)) &
(ALL xe::'A.
    xe : x -->
    xd xe : xa &
    (xc::'B => hollight.real) (xd xe) = (xb::'A => hollight.real) xe)
==> hollight.sum x xb = hollight.sum xa xc"
  by (import hollight SUM_EQ_GENERAL)

lemma SUM_EQ_GENERAL_INVERSES: "(ALL y::'B.
    y : (xa::'B => bool) -->
    (xe::'B => 'A) y : (x::'A => bool) & (xd::'A => 'B) (xe y) = y) &
(ALL xf::'A.
    xf : x -->
    xd xf : xa &
    xe (xd xf) = xf &
    (xc::'B => hollight.real) (xd xf) = (xb::'A => hollight.real) xf)
==> hollight.sum x xb = hollight.sum xa xc"
  by (import hollight SUM_EQ_GENERAL_INVERSES)

lemma SUM_INJECTION: "finite (xb::'q_71007 => bool) &
(ALL x::'q_71007. x : xb --> (xa::'q_71007 => 'q_71007) x : xb) &
(ALL (x::'q_71007) y::'q_71007. x : xb & y : xb & xa x = xa y --> x = y)
==> hollight.sum xb ((x::'q_71007 => hollight.real) o xa) =
    hollight.sum xb x"
  by (import hollight SUM_INJECTION)

lemma SUM_UNION_NONZERO: "finite (xa::'q_71050 => bool) &
finite (xb::'q_71050 => bool) &
(ALL xc::'q_71050.
    xc : xa Int xb -->
    (x::'q_71050 => hollight.real) xc = real_of_num (0::nat))
==> hollight.sum (xa Un xb) x =
    real_add (hollight.sum xa x) (hollight.sum xb x)"
  by (import hollight SUM_UNION_NONZERO)

lemma SUM_UNIONS_NONZERO: "finite (x::('A => bool) => bool) &
(ALL t::'A => bool. t : x --> finite t) &
(ALL (t1::'A => bool) (t2::'A => bool) xa::'A.
    t1 : x & t2 : x & t1 ~= t2 & xa : t1 & xa : t2 -->
    (f::'A => hollight.real) xa = real_of_num (0::nat))
==> hollight.sum (Union x) f =
    hollight.sum x (%t::'A => bool. hollight.sum t f)"
  by (import hollight SUM_UNIONS_NONZERO)

lemma SUM_CASES: "finite (x::'A => bool)
==> hollight.sum x
     (%x::'A.
         if (xa::'A => bool) x then (xb::'A => hollight.real) x
         else (xc::'A => hollight.real) x) =
    real_add (hollight.sum {u::'A. EX xb::'A. (xb : x & xa xb) & u = xb} xb)
     (hollight.sum {u::'A. EX xb::'A. (xb : x & ~ xa xb) & u = xb} xc)"
  by (import hollight SUM_CASES)

lemma SUM_CASES_1: "finite (s::'q_71319 => bool) & (a::'q_71319) : s
==> hollight.sum s
     (%x::'q_71319.
         if x = a then y::hollight.real
         else (f::'q_71319 => hollight.real) x) =
    real_add (hollight.sum s f) (real_sub y (f a))"
  by (import hollight SUM_CASES_1)

lemma SUM_LE_INCLUDED: "finite (s::'A => bool) &
finite (t::'B => bool) &
(ALL y::'B.
    y : t --> real_le (real_of_num (0::nat)) ((g::'B => hollight.real) y)) &
(ALL x::'A.
    x : s -->
    (EX y::'B.
        y : t &
        (i::'B => 'A) y = x & real_le ((f::'A => hollight.real) x) (g y)))
==> real_le (hollight.sum s f) (hollight.sum t g)"
  by (import hollight SUM_LE_INCLUDED)

lemma SUM_IMAGE_LE: "finite (s::'A => bool) &
(ALL x::'A.
    x : s -->
    real_le (real_of_num (0::nat))
     ((g::'B => hollight.real) ((f::'A => 'B) x)))
==> real_le (hollight.sum (f ` s) g) (hollight.sum s (g o f))"
  by (import hollight SUM_IMAGE_LE)

lemma SUM_CLOSED: "(P::hollight.real => bool) (real_of_num (0::nat)) &
(ALL (x::hollight.real) y::hollight.real. P x & P y --> P (real_add x y)) &
(ALL a::'A. a : (s::'A => bool) --> P ((f::'A => hollight.real) a))
==> P (hollight.sum s f)"
  by (import hollight SUM_CLOSED)

lemma SUM_ADD_NUMSEG: "hollight.sum {xb::nat..xc::nat}
 (%i::nat.
     real_add ((x::nat => hollight.real) i)
      ((xa::nat => hollight.real) i)) =
real_add (hollight.sum {xb..xc} x) (hollight.sum {xb..xc} xa)"
  by (import hollight SUM_ADD_NUMSEG)

lemma SUM_SUB_NUMSEG: "hollight.sum {xb::nat..xc::nat}
 (%i::nat.
     real_sub ((x::nat => hollight.real) i)
      ((xa::nat => hollight.real) i)) =
real_sub (hollight.sum {xb..xc} x) (hollight.sum {xb..xc} xa)"
  by (import hollight SUM_SUB_NUMSEG)

lemma SUM_LE_NUMSEG: "(!!i::nat.
    (xb::nat) <= i & i <= (xc::nat)
    ==> real_le ((x::nat => hollight.real) i)
         ((xa::nat => hollight.real) i))
==> real_le (hollight.sum {xb..xc} x) (hollight.sum {xb..xc} xa)"
  by (import hollight SUM_LE_NUMSEG)

lemma SUM_EQ_NUMSEG: "(!!i::nat.
    (m::nat) <= i & i <= (n::nat)
    ==> (f::nat => hollight.real) i = (g::nat => hollight.real) i)
==> hollight.sum {m..n} f = hollight.sum {m..n} g"
  by (import hollight SUM_EQ_NUMSEG)

lemma SUM_ABS_NUMSEG: "real_le
 (real_abs (hollight.sum {xa::nat..xb::nat} (x::nat => hollight.real)))
 (hollight.sum {xa..xb} (%i::nat. real_abs (x i)))"
  by (import hollight SUM_ABS_NUMSEG)

lemma SUM_CONST_NUMSEG: "hollight.sum {xa..xb} (%n. x) = real_mul (real_of_num (xb + 1 - xa)) x"
  by (import hollight SUM_CONST_NUMSEG)

lemma SUM_EQ_0_NUMSEG: "(!!i::nat.
    (m::nat) <= i & i <= (n::nat)
    ==> (x::nat => hollight.real) i = real_of_num (0::nat))
==> hollight.sum {m..n} x = real_of_num (0::nat)"
  by (import hollight SUM_EQ_0_NUMSEG)

lemma SUM_TRIV_NUMSEG: "(n::nat) < (m::nat)
==> hollight.sum {m..n} (f::nat => hollight.real) = real_of_num (0::nat)"
  by (import hollight SUM_TRIV_NUMSEG)

lemma SUM_POS_LE_NUMSEG: "(!!p::nat.
    (x::nat) <= p & p <= (xa::nat)
    ==> real_le (real_of_num (0::nat)) ((xb::nat => hollight.real) p))
==> real_le (real_of_num (0::nat)) (hollight.sum {x..xa} xb)"
  by (import hollight SUM_POS_LE_NUMSEG)

lemma SUM_POS_EQ_0_NUMSEG: "[| (ALL p::nat.
       (m::nat) <= p & p <= (n::nat) -->
       real_le (real_of_num (0::nat)) ((f::nat => hollight.real) p)) &
   hollight.sum {m..n} f = real_of_num (0::nat);
   m <= (p::nat) & p <= n |]
==> f p = real_of_num (0::nat)"
  by (import hollight SUM_POS_EQ_0_NUMSEG)

lemma SUM_SING_NUMSEG: "hollight.sum {xa::nat..xa} (x::nat => hollight.real) = x xa"
  by (import hollight SUM_SING_NUMSEG)

lemma SUM_CLAUSES_NUMSEG: "(ALL m. hollight.sum {m..0} f = (if m = 0 then f 0 else real_of_num 0)) &
(ALL m n.
    hollight.sum {m..Suc n} f =
    (if m <= Suc n then real_add (hollight.sum {m..n} f) (f (Suc n))
     else hollight.sum {m..n} f))"
  by (import hollight SUM_CLAUSES_NUMSEG)

lemma SUM_SWAP_NUMSEG: "hollight.sum {a::nat..b::nat}
 (%i::nat.
     hollight.sum {c::nat..d::nat} ((f::nat => nat => hollight.real) i)) =
hollight.sum {c..d} (%j::nat. hollight.sum {a..b} (%i::nat. f i j))"
  by (import hollight SUM_SWAP_NUMSEG)

lemma SUM_ADD_SPLIT: "(xa::nat) <= (xb::nat) + (1::nat)
==> hollight.sum {xa..xb + (xc::nat)} (x::nat => hollight.real) =
    real_add (hollight.sum {xa..xb} x)
     (hollight.sum {xb + (1::nat)..xb + xc} x)"
  by (import hollight SUM_ADD_SPLIT)

lemma SUM_OFFSET: "hollight.sum {(xb::nat) + (x::nat)..(xc::nat) + x}
 (xa::nat => hollight.real) =
hollight.sum {xb..xc} (%i::nat. xa (i + x))"
  by (import hollight SUM_OFFSET)

lemma SUM_OFFSET_0: "(xa::nat) <= (xb::nat)
==> hollight.sum {xa..xb} (x::nat => hollight.real) =
    hollight.sum {0::nat..xb - xa} (%i::nat. x (i + xa))"
  by (import hollight SUM_OFFSET_0)

lemma SUM_CLAUSES_LEFT: "(xa::nat) <= (xb::nat)
==> hollight.sum {xa..xb} (x::nat => hollight.real) =
    real_add (x xa) (hollight.sum {xa + (1::nat)..xb} x)"
  by (import hollight SUM_CLAUSES_LEFT)

lemma SUM_CLAUSES_RIGHT: "(0::nat) < (n::nat) & (m::nat) <= n
==> hollight.sum {m..n} (f::nat => hollight.real) =
    real_add (hollight.sum {m..n - (1::nat)} f) (f n)"
  by (import hollight SUM_CLAUSES_RIGHT)

lemma SUM_PAIR: "hollight.sum {(2::nat) * (m::nat)..(2::nat) * (n::nat) + (1::nat)}
 (f::nat => hollight.real) =
hollight.sum {m..n}
 (%i::nat. real_add (f ((2::nat) * i)) (f ((2::nat) * i + (1::nat))))"
  by (import hollight SUM_PAIR)

lemma REAL_OF_NUM_SUM_NUMSEG: "real_of_num (nsum {xa::nat..xb::nat} (x::nat => nat)) =
hollight.sum {xa..xb} (%i::nat. real_of_num (x i))"
  by (import hollight REAL_OF_NUM_SUM_NUMSEG)

lemma SUM_PARTIAL_SUC: "hollight.sum {m::nat..n::nat}
 (%k::nat.
     real_mul ((f::nat => hollight.real) k)
      (real_sub ((g::nat => hollight.real) (k + (1::nat))) (g k))) =
(if m <= n
 then real_sub
       (real_sub (real_mul (f (n + (1::nat))) (g (n + (1::nat))))
         (real_mul (f m) (g m)))
       (hollight.sum {m..n}
         (%k::nat.
             real_mul (g (k + (1::nat)))
              (real_sub (f (k + (1::nat))) (f k))))
 else real_of_num (0::nat))"
  by (import hollight SUM_PARTIAL_SUC)

lemma SUM_PARTIAL_PRE: "hollight.sum {m::nat..n::nat}
 (%k::nat.
     real_mul ((f::nat => hollight.real) k)
      (real_sub ((g::nat => hollight.real) k) (g (k - (1::nat))))) =
(if m <= n
 then real_sub
       (real_sub (real_mul (f (n + (1::nat))) (g n))
         (real_mul (f m) (g (m - (1::nat)))))
       (hollight.sum {m..n}
         (%k::nat. real_mul (g k) (real_sub (f (k + (1::nat))) (f k))))
 else real_of_num (0::nat))"
  by (import hollight SUM_PARTIAL_PRE)

lemma SUM_DIFFS: "hollight.sum {x::nat..xa::nat}
 (%x::nat. real_sub ((f::nat => hollight.real) x) (f (x + (1::nat)))) =
(if x <= xa then real_sub (f x) (f (xa + (1::nat)))
 else real_of_num (0::nat))"
  by (import hollight SUM_DIFFS)

lemma SUM_DIFFS_ALT: "hollight.sum {m::nat..n::nat}
 (%x::nat. real_sub ((f::nat => hollight.real) (x + (1::nat))) (f x)) =
(if m <= n then real_sub (f (n + (1::nat))) (f m) else real_of_num (0::nat))"
  by (import hollight SUM_DIFFS_ALT)

lemma SUM_COMBINE_R: "(m::nat) <= (n::nat) + (1::nat) & n <= (p::nat)
==> real_add (hollight.sum {m..n} (f::nat => hollight.real))
     (hollight.sum {n + (1::nat)..p} f) =
    hollight.sum {m..p} f"
  by (import hollight SUM_COMBINE_R)

lemma SUM_COMBINE_L: "(0::nat) < (n::nat) & (m::nat) <= n & n <= (p::nat) + (1::nat)
==> real_add (hollight.sum {m..n - (1::nat)} (f::nat => hollight.real))
     (hollight.sum {n..p} f) =
    hollight.sum {m..p} f"
  by (import hollight SUM_COMBINE_L)

lemma REAL_SUB_POW: "1 <= xb
==> real_sub (real_pow x xb) (real_pow xa xb) =
    real_mul (real_sub x xa)
     (hollight.sum {0..xb - 1}
       (%i. real_mul (real_pow x i) (real_pow xa (xb - 1 - i))))"
  by (import hollight REAL_SUB_POW)

lemma REAL_SUB_POW_R1: "1 <= n
==> real_sub (real_pow x n) (real_of_num 1) =
    real_mul (real_sub x (real_of_num 1))
     (hollight.sum {0..n - 1} (real_pow x))"
  by (import hollight REAL_SUB_POW_R1)

lemma REAL_SUB_POW_L1: "1 <= xa
==> real_sub (real_of_num 1) (real_pow x xa) =
    real_mul (real_sub (real_of_num 1) x)
     (hollight.sum {0..xa - 1} (real_pow x))"
  by (import hollight REAL_SUB_POW_L1)

definition
  dimindex :: "('A => bool) => nat"  where
  "(op ==::(('A::type => bool) => nat) => (('A::type => bool) => nat) => prop)
 (dimindex::('A::type => bool) => nat)
 (%u::'A::type => bool.
     (If::bool => nat => nat => nat)
      ((finite::('A::type => bool) => bool) (UNIV::'A::type => bool))
      ((CARD::('A::type => bool) => nat) (UNIV::'A::type => bool)) (1::nat))"

lemma DEF_dimindex: "(op =::(('A::type => bool) => nat) => (('A::type => bool) => nat) => bool)
 (dimindex::('A::type => bool) => nat)
 (%u::'A::type => bool.
     (If::bool => nat => nat => nat)
      ((finite::('A::type => bool) => bool) (UNIV::'A::type => bool))
      ((CARD::('A::type => bool) => nat) (UNIV::'A::type => bool)) (1::nat))"
  by (import hollight DEF_dimindex)

lemma DIMINDEX_NONZERO: "dimindex (s::'A => bool) ~= (0::nat)"
  by (import hollight DIMINDEX_NONZERO)

lemma DIMINDEX_GE_1: "(1::nat) <= dimindex (x::'A => bool)"
  by (import hollight DIMINDEX_GE_1)

lemma DIMINDEX_UNIV: "(op =::nat => nat => bool)
 ((dimindex::('A::type => bool) => nat) (x::'A::type => bool))
 ((dimindex::('A::type => bool) => nat) (UNIV::'A::type => bool))"
  by (import hollight DIMINDEX_UNIV)

lemma DIMINDEX_UNIQUE: "(op ==>::prop => prop => prop)
 ((Trueprop::bool => prop)
   ((HAS_SIZE::('A::type => bool) => nat => bool) (UNIV::'A::type => bool)
     (n::nat)))
 ((Trueprop::bool => prop)
   ((op =::nat => nat => bool)
     ((dimindex::('A::type => bool) => nat) (UNIV::'A::type => bool)) n))"
  by (import hollight DIMINDEX_UNIQUE)

typedef (open) ('A) finite_image = "{x::nat. x : dotdot (NUMERAL (NUMERAL_BIT1 (0::nat))) (dimindex UNIV)}"  morphisms "dest_finite_image" "finite_index"
  apply (rule light_ex_imp_nonempty[where t="SOME x::nat. x : dotdot (NUMERAL (NUMERAL_BIT1 (0::nat))) (dimindex UNIV)"])
  by (import hollight TYDEF_finite_image)

syntax
  dest_finite_image :: _ 

syntax
  finite_index :: _ 

lemmas "TYDEF_finite_image_@intern" = typedef_hol2hollight 
  [where a="a :: 'A finite_image" and r=r ,
   OF type_definition_finite_image]

lemma FINITE_IMAGE_IMAGE: "(op =::('A::type finite_image => bool)
       => ('A::type finite_image => bool) => bool)
 (UNIV::'A::type finite_image => bool)
 ((op `::(nat => 'A::type finite_image)
         => (nat => bool) => 'A::type finite_image => bool)
   (finite_index::nat => 'A::type finite_image)
   ((atLeastAtMost::nat => nat => nat => bool) (1::nat)
     ((dimindex::('A::type => bool) => nat) (UNIV::'A::type => bool))))"
  by (import hollight FINITE_IMAGE_IMAGE)

lemma HAS_SIZE_FINITE_IMAGE: "(HAS_SIZE::('A::type finite_image => bool) => nat => bool)
 (UNIV::'A::type finite_image => bool)
 ((dimindex::('A::type => bool) => nat) (s::'A::type => bool))"
  by (import hollight HAS_SIZE_FINITE_IMAGE)

lemma CARD_FINITE_IMAGE: "(op =::nat => nat => bool)
 ((CARD::('A::type finite_image => bool) => nat)
   (UNIV::'A::type finite_image => bool))
 ((dimindex::('A::type => bool) => nat) (s::'A::type => bool))"
  by (import hollight CARD_FINITE_IMAGE)

lemma FINITE_FINITE_IMAGE: "(finite::('A::type finite_image => bool) => bool)
 (UNIV::'A::type finite_image => bool)"
  by (import hollight FINITE_FINITE_IMAGE)

lemma DIMINDEX_FINITE_IMAGE: "dimindex (s::'A finite_image => bool) = dimindex (t::'A => bool)"
  by (import hollight DIMINDEX_FINITE_IMAGE)

lemma FINITE_INDEX_WORKS: "(Ex1::(nat => bool) => bool)
 (%xa::nat.
     (op &::bool => bool => bool) ((op <=::nat => nat => bool) (1::nat) xa)
      ((op &::bool => bool => bool)
        ((op <=::nat => nat => bool) xa
          ((dimindex::('A::type => bool) => nat) (UNIV::'A::type => bool)))
        ((op =::'A::type finite_image => 'A::type finite_image => bool)
          ((finite_index::nat => 'A::type finite_image) xa)
          (x::'A::type finite_image))))"
  by (import hollight FINITE_INDEX_WORKS)

lemma FINITE_INDEX_INJ: "(op ==>::prop => prop => prop)
 ((Trueprop::bool => prop)
   ((op &::bool => bool => bool)
     ((op <=::nat => nat => bool) (1::nat) (i::nat))
     ((op &::bool => bool => bool)
       ((op <=::nat => nat => bool) i
         ((dimindex::('A::type => bool) => nat) (UNIV::'A::type => bool)))
       ((op &::bool => bool => bool)
         ((op <=::nat => nat => bool) (1::nat) (j::nat))
         ((op <=::nat => nat => bool) j
           ((dimindex::('A::type => bool) => nat)
             (UNIV::'A::type => bool)))))))
 ((Trueprop::bool => prop)
   ((op =::bool => bool => bool)
     ((op =::'A::type finite_image => 'A::type finite_image => bool)
       ((finite_index::nat => 'A::type finite_image) i)
       ((finite_index::nat => 'A::type finite_image) j))
     ((op =::nat => nat => bool) i j)))"
  by (import hollight FINITE_INDEX_INJ)

lemma FORALL_FINITE_INDEX: "(op =::bool => bool => bool)
 ((All::('N::type finite_image => bool) => bool)
   (P::'N::type finite_image => bool))
 ((All::(nat => bool) => bool)
   (%i::nat.
       (op -->::bool => bool => bool)
        ((op &::bool => bool => bool)
          ((op <=::nat => nat => bool) (1::nat) i)
          ((op <=::nat => nat => bool) i
            ((dimindex::('N::type => bool) => nat)
              (UNIV::'N::type => bool))))
        (P ((finite_index::nat => 'N::type finite_image) i))))"
  by (import hollight FORALL_FINITE_INDEX)

typedef (open) ('A, 'B) cart = "{f. True}"  morphisms "dest_cart" "mk_cart"
  apply (rule light_ex_imp_nonempty[where t="SOME f. True"])
  by (import hollight TYDEF_cart)

syntax
  dest_cart :: _ 

syntax
  mk_cart :: _ 

lemmas "TYDEF_cart_@intern" = typedef_hol2hollight 
  [where a="a :: ('A, 'B) cart" and r=r ,
   OF type_definition_cart]

consts
  "$" :: "('q_73536, 'q_73546) cart => nat => 'q_73536" ("$")

defs
  "$_def": "$ == %(u::('q_73536, 'q_73546) cart) ua::nat. dest_cart u (finite_index ua)"

lemma "DEF_$": "$ = (%(u::('q_73536, 'q_73546) cart) ua::nat. dest_cart u (finite_index ua))"
  by (import hollight "DEF_$")

lemma CART_EQ: "(op =::bool => bool => bool)
 ((op =::('A::type, 'B::type) cart => ('A::type, 'B::type) cart => bool)
   (x::('A::type, 'B::type) cart) (y::('A::type, 'B::type) cart))
 ((All::(nat => bool) => bool)
   (%xa::nat.
       (op -->::bool => bool => bool)
        ((op &::bool => bool => bool)
          ((op <=::nat => nat => bool) (1::nat) xa)
          ((op <=::nat => nat => bool) xa
            ((dimindex::('B::type => bool) => nat)
              (UNIV::'B::type => bool))))
        ((op =::'A::type => 'A::type => bool)
          (($::('A::type, 'B::type) cart => nat => 'A::type) x xa)
          (($::('A::type, 'B::type) cart => nat => 'A::type) y xa))))"
  by (import hollight CART_EQ)

definition
  lambda :: "(nat => 'A) => ('A, 'B) cart"  where
  "(op ==::((nat => 'A::type) => ('A::type, 'B::type) cart)
        => ((nat => 'A::type) => ('A::type, 'B::type) cart) => prop)
 (lambda::(nat => 'A::type) => ('A::type, 'B::type) cart)
 (%u::nat => 'A::type.
     (Eps::(('A::type, 'B::type) cart => bool) => ('A::type, 'B::type) cart)
      (%f::('A::type, 'B::type) cart.
          (All::(nat => bool) => bool)
           (%i::nat.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::nat => nat => bool) (1::nat) i)
                  ((op <=::nat => nat => bool) i
                    ((dimindex::('B::type => bool) => nat)
                      (UNIV::'B::type => bool))))
                ((op =::'A::type => 'A::type => bool)
                  (($::('A::type, 'B::type) cart => nat => 'A::type) f i)
                  (u i)))))"

lemma DEF_lambda: "(op =::((nat => 'A::type) => ('A::type, 'B::type) cart)
       => ((nat => 'A::type) => ('A::type, 'B::type) cart) => bool)
 (lambda::(nat => 'A::type) => ('A::type, 'B::type) cart)
 (%u::nat => 'A::type.
     (Eps::(('A::type, 'B::type) cart => bool) => ('A::type, 'B::type) cart)
      (%f::('A::type, 'B::type) cart.
          (All::(nat => bool) => bool)
           (%i::nat.
               (op -->::bool => bool => bool)
                ((op &::bool => bool => bool)
                  ((op <=::nat => nat => bool) (1::nat) i)
                  ((op <=::nat => nat => bool) i
                    ((dimindex::('B::type => bool) => nat)
                      (UNIV::'B::type => bool))))
                ((op =::'A::type => 'A::type => bool)
                  (($::('A::type, 'B::type) cart => nat => 'A::type) f i)
                  (u i)))))"
  by (import hollight DEF_lambda)

lemma LAMBDA_BETA: "(op ==>::prop => prop => prop)
 ((Trueprop::bool => prop)
   ((op &::bool => bool => bool)
     ((op <=::nat => nat => bool) (1::nat) (x::nat))
     ((op <=::nat => nat => bool) x
       ((dimindex::('B::type => bool) => nat) (UNIV::'B::type => bool)))))
 ((Trueprop::bool => prop)
   ((op =::'A::type => 'A::type => bool)
     (($::('A::type, 'B::type) cart => nat => 'A::type)
       ((lambda::(nat => 'A::type) => ('A::type, 'B::type) cart)
         (g::nat => 'A::type))
       x)
     (g x)))"
  by (import hollight LAMBDA_BETA)

lemma LAMBDA_UNIQUE: "(op =::bool => bool => bool)
 ((All::(nat => bool) => bool)
   (%i::nat.
       (op -->::bool => bool => bool)
        ((op &::bool => bool => bool)
          ((op <=::nat => nat => bool) (1::nat) i)
          ((op <=::nat => nat => bool) i
            ((dimindex::('B::type => bool) => nat)
              (UNIV::'B::type => bool))))
        ((op =::'A::type => 'A::type => bool)
          (($::('A::type, 'B::type) cart => nat => 'A::type)
            (x::('A::type, 'B::type) cart) i)
          ((xa::nat => 'A::type) i))))
 ((op =::('A::type, 'B::type) cart => ('A::type, 'B::type) cart => bool)
   ((lambda::(nat => 'A::type) => ('A::type, 'B::type) cart) xa) x)"
  by (import hollight LAMBDA_UNIQUE)

lemma LAMBDA_ETA: "lambda ($ (x::('q_73734, 'q_73738) cart)) = x"
  by (import hollight LAMBDA_ETA)

lemma FINITE_INDEX_INRANGE: "(Ex::(nat => bool) => bool)
 (%xa::nat.
     (op &::bool => bool => bool) ((op <=::nat => nat => bool) (1::nat) xa)
      ((op &::bool => bool => bool)
        ((op <=::nat => nat => bool) xa
          ((dimindex::('N::type => bool) => nat) (UNIV::'N::type => bool)))
        ((All::(('A::type, 'N::type) cart => bool) => bool)
          (%xb::('A::type, 'N::type) cart.
              (op =::'A::type => 'A::type => bool)
               (($::('A::type, 'N::type) cart => nat => 'A::type) xb
                 (x::nat))
               (($::('A::type, 'N::type) cart => nat => 'A::type) xb xa)))))"
  by (import hollight FINITE_INDEX_INRANGE)

lemma CART_EQ_FULL: "((x::('A, 'N) cart) = (y::('A, 'N) cart)) = (ALL i::nat. $ x i = $ y i)"
  by (import hollight CART_EQ_FULL)

typedef (open) ('A, 'B) finite_sum = "{x::nat.
 x : dotdot (NUMERAL (NUMERAL_BIT1 (0::nat)))
      (dimindex UNIV + dimindex UNIV)}"  morphisms "dest_finite_sum" "mk_finite_sum"
  apply (rule light_ex_imp_nonempty[where t="SOME x::nat.
   x : dotdot (NUMERAL (NUMERAL_BIT1 (0::nat)))
        (dimindex UNIV + dimindex UNIV)"])
  by (import hollight TYDEF_finite_sum)

syntax
  dest_finite_sum :: _ 

syntax
  mk_finite_sum :: _ 

lemmas "TYDEF_finite_sum_@intern" = typedef_hol2hollight 
  [where a="a :: ('A, 'B) finite_sum" and r=r ,
   OF type_definition_finite_sum]

definition
  pastecart :: "('A, 'M) cart => ('A, 'N) cart => ('A, ('M, 'N) finite_sum) cart"  where
  "(op ==::(('A::type, 'M::type) cart
         => ('A::type, 'N::type) cart
            => ('A::type, ('M::type, 'N::type) finite_sum) cart)
        => (('A::type, 'M::type) cart
            => ('A::type, 'N::type) cart
               => ('A::type, ('M::type, 'N::type) finite_sum) cart)
           => prop)
 (pastecart::('A::type, 'M::type) cart
             => ('A::type, 'N::type) cart
                => ('A::type, ('M::type, 'N::type) finite_sum) cart)
 (%(u::('A::type, 'M::type) cart) ua::('A::type, 'N::type) cart.
     (lambda::(nat => 'A::type)
              => ('A::type, ('M::type, 'N::type) finite_sum) cart)
      (%i::nat.
          (If::bool => 'A::type => 'A::type => 'A::type)
           ((op <=::nat => nat => bool) i
             ((dimindex::('M::type => bool) => nat)
               (UNIV::'M::type => bool)))
           (($::('A::type, 'M::type) cart => nat => 'A::type) u i)
           (($::('A::type, 'N::type) cart => nat => 'A::type) ua
             ((op -::nat => nat => nat) i
               ((dimindex::('M::type => bool) => nat)
                 (UNIV::'M::type => bool))))))"

lemma DEF_pastecart: "(op =::(('A::type, 'M::type) cart
        => ('A::type, 'N::type) cart
           => ('A::type, ('M::type, 'N::type) finite_sum) cart)
       => (('A::type, 'M::type) cart
           => ('A::type, 'N::type) cart
              => ('A::type, ('M::type, 'N::type) finite_sum) cart)
          => bool)
 (pastecart::('A::type, 'M::type) cart
             => ('A::type, 'N::type) cart
                => ('A::type, ('M::type, 'N::type) finite_sum) cart)
 (%(u::('A::type, 'M::type) cart) ua::('A::type, 'N::type) cart.
     (lambda::(nat => 'A::type)
              => ('A::type, ('M::type, 'N::type) finite_sum) cart)
      (%i::nat.
          (If::bool => 'A::type => 'A::type => 'A::type)
           ((op <=::nat => nat => bool) i
             ((dimindex::('M::type => bool) => nat)
               (UNIV::'M::type => bool)))
           (($::('A::type, 'M::type) cart => nat => 'A::type) u i)
           (($::('A::type, 'N::type) cart => nat => 'A::type) ua
             ((op -::nat => nat => nat) i
               ((dimindex::('M::type => bool) => nat)
                 (UNIV::'M::type => bool))))))"
  by (import hollight DEF_pastecart)

definition
  fstcart :: "('A, ('M, 'N) finite_sum) cart => ('A, 'M) cart"  where
  "fstcart == %u::('A, ('M, 'N) finite_sum) cart. lambda ($ u)"

lemma DEF_fstcart: "fstcart = (%u::('A, ('M, 'N) finite_sum) cart. lambda ($ u))"
  by (import hollight DEF_fstcart)

definition
  sndcart :: "('A, ('M, 'N) finite_sum) cart => ('A, 'N) cart"  where
  "(op ==::(('A::type, ('M::type, 'N::type) finite_sum) cart
         => ('A::type, 'N::type) cart)
        => (('A::type, ('M::type, 'N::type) finite_sum) cart
            => ('A::type, 'N::type) cart)
           => prop)
 (sndcart::('A::type, ('M::type, 'N::type) finite_sum) cart
           => ('A::type, 'N::type) cart)
 (%u::('A::type, ('M::type, 'N::type) finite_sum) cart.
     (lambda::(nat => 'A::type) => ('A::type, 'N::type) cart)
      (%i::nat.
          ($::('A::type, ('M::type, 'N::type) finite_sum) cart
              => nat => 'A::type)
           u ((op +::nat => nat => nat) i
               ((dimindex::('M::type => bool) => nat)
                 (UNIV::'M::type => bool)))))"

lemma DEF_sndcart: "(op =::(('A::type, ('M::type, 'N::type) finite_sum) cart
        => ('A::type, 'N::type) cart)
       => (('A::type, ('M::type, 'N::type) finite_sum) cart
           => ('A::type, 'N::type) cart)
          => bool)
 (sndcart::('A::type, ('M::type, 'N::type) finite_sum) cart
           => ('A::type, 'N::type) cart)
 (%u::('A::type, ('M::type, 'N::type) finite_sum) cart.
     (lambda::(nat => 'A::type) => ('A::type, 'N::type) cart)
      (%i::nat.
          ($::('A::type, ('M::type, 'N::type) finite_sum) cart
              => nat => 'A::type)
           u ((op +::nat => nat => nat) i
               ((dimindex::('M::type => bool) => nat)
                 (UNIV::'M::type => bool)))))"
  by (import hollight DEF_sndcart)

lemma FINITE_SUM_IMAGE: "(op =::(('A::type, 'B::type) finite_sum => bool)
       => (('A::type, 'B::type) finite_sum => bool) => bool)
 (UNIV::('A::type, 'B::type) finite_sum => bool)
 ((op `::(nat => ('A::type, 'B::type) finite_sum)
         => (nat => bool) => ('A::type, 'B::type) finite_sum => bool)
   (mk_finite_sum::nat => ('A::type, 'B::type) finite_sum)
   ((atLeastAtMost::nat => nat => nat => bool) (1::nat)
     ((op +::nat => nat => nat)
       ((dimindex::('A::type => bool) => nat) (UNIV::'A::type => bool))
       ((dimindex::('B::type => bool) => nat) (UNIV::'B::type => bool)))))"
  by (import hollight FINITE_SUM_IMAGE)

lemma HAS_SIZE_1: "(HAS_SIZE::(unit => bool) => nat => bool) (UNIV::unit => bool) (1::nat)"
  by (import hollight HAS_SIZE_1)

typedef (open) N_2 = "{x. x : dotdot (NUMERAL (NUMERAL_BIT1 0))
         (NUMERAL (NUMERAL_BIT0 (NUMERAL_BIT1 0)))}"  morphisms "dest_auto_define_finite_type_2" "mk_auto_define_finite_type_2"
  apply (rule light_ex_imp_nonempty[where t="SOME x.
   x : dotdot (NUMERAL (NUMERAL_BIT1 0))
        (NUMERAL (NUMERAL_BIT0 (NUMERAL_BIT1 0)))"])
  by (import hollight TYDEF_2)

syntax
  dest_auto_define_finite_type_2 :: _ 

syntax
  mk_auto_define_finite_type_2 :: _ 

lemmas "TYDEF_2_@intern" = typedef_hol2hollight 
  [where a="a :: N_2" and r=r ,
   OF type_definition_N_2]

typedef (open) N_3 = "{x. x : dotdot (NUMERAL (NUMERAL_BIT1 0))
         (NUMERAL (NUMERAL_BIT1 (NUMERAL_BIT1 0)))}"  morphisms "dest_auto_define_finite_type_3" "mk_auto_define_finite_type_3"
  apply (rule light_ex_imp_nonempty[where t="SOME x.
   x : dotdot (NUMERAL (NUMERAL_BIT1 0))
        (NUMERAL (NUMERAL_BIT1 (NUMERAL_BIT1 0)))"])
  by (import hollight TYDEF_3)

syntax
  dest_auto_define_finite_type_3 :: _ 

syntax
  mk_auto_define_finite_type_3 :: _ 

lemmas "TYDEF_3_@intern" = typedef_hol2hollight 
  [where a="a :: N_3" and r=r ,
   OF type_definition_N_3]

lemma FINITE_CART: "(op ==>::prop => prop => prop)
 ((all::(nat => prop) => prop)
   (%i::nat.
       (op ==>::prop => prop => prop)
        ((Trueprop::bool => prop)
          ((op &::bool => bool => bool)
            ((op <=::nat => nat => bool) (1::nat) i)
            ((op <=::nat => nat => bool) i
              ((dimindex::('N::type => bool) => nat)
                (UNIV::'N::type => bool)))))
        ((Trueprop::bool => prop)
          ((finite::('A::type => bool) => bool)
            ((Collect::('A::type => bool) => 'A::type => bool)
              (%u::'A::type.
                  (Ex::('A::type => bool) => bool)
                   (%x::'A::type.
                       (op &::bool => bool => bool)
                        ((P::nat => 'A::type => bool) i x)
                        ((op =::'A::type => 'A::type => bool) u x))))))))
 ((Trueprop::bool => prop)
   ((finite::(('A::type, 'N::type) cart => bool) => bool)
     ((Collect::(('A::type, 'N::type) cart => bool)
                => ('A::type, 'N::type) cart => bool)
       (%u::('A::type, 'N::type) cart.
           (Ex::(('A::type, 'N::type) cart => bool) => bool)
            (%v::('A::type, 'N::type) cart.
                (op &::bool => bool => bool)
                 ((All::(nat => bool) => bool)
                   (%i::nat.
                       (op -->::bool => bool => bool)
                        ((op &::bool => bool => bool)
                          ((op <=::nat => nat => bool) (1::nat) i)
                          ((op <=::nat => nat => bool) i
                            ((dimindex::('N::type => bool) => nat)
                              (UNIV::'N::type => bool))))
                        (P i (($::('A::type, 'N::type) cart
                                  => nat => 'A::type)
                               v i))))
                 ((op =::('A::type, 'N::type) cart
                         => ('A::type, 'N::type) cart => bool)
                   u v))))))"
  by (import hollight FINITE_CART)

definition
  vector :: "'A list => ('A, 'N) cart"  where
  "(op ==::('A::type list => ('A::type, 'N::type) cart)
        => ('A::type list => ('A::type, 'N::type) cart) => prop)
 (vector::'A::type list => ('A::type, 'N::type) cart)
 (%u::'A::type list.
     (lambda::(nat => 'A::type) => ('A::type, 'N::type) cart)
      (%i::nat.
          (op !::'A::type list => nat => 'A::type) u
           ((op -::nat => nat => nat) i (1::nat))))"

lemma DEF_vector: "(op =::('A::type list => ('A::type, 'N::type) cart)
       => ('A::type list => ('A::type, 'N::type) cart) => bool)
 (vector::'A::type list => ('A::type, 'N::type) cart)
 (%u::'A::type list.
     (lambda::(nat => 'A::type) => ('A::type, 'N::type) cart)
      (%i::nat.
          (op !::'A::type list => nat => 'A::type) u
           ((op -::nat => nat => nat) i (1::nat))))"
  by (import hollight DEF_vector)

definition
  CASEWISE :: "(('q_74835 => 'q_74839) * ('q_74840 => 'q_74835 => 'q_74799)) list
=> 'q_74840 => 'q_74839 => 'q_74799"  where
  "CASEWISE ==
SOME CASEWISE::(('q_74835 => 'q_74839) *
                ('q_74840 => 'q_74835 => 'q_74799)) list
               => 'q_74840 => 'q_74839 => 'q_74799.
   (ALL (f::'q_74840) x::'q_74839.
       CASEWISE [] f x = (SOME y::'q_74799. True)) &
   (ALL (h::('q_74835 => 'q_74839) * ('q_74840 => 'q_74835 => 'q_74799))
       (t::(('q_74835 => 'q_74839) *
            ('q_74840 => 'q_74835 => 'q_74799)) list)
       (f::'q_74840) x::'q_74839.
       CASEWISE (h # t) f x =
       (if EX y::'q_74835. fst h y = x
        then snd h f (SOME y::'q_74835. fst h y = x) else CASEWISE t f x))"

lemma DEF_CASEWISE: "CASEWISE =
(SOME CASEWISE::(('q_74835 => 'q_74839) *
                 ('q_74840 => 'q_74835 => 'q_74799)) list
                => 'q_74840 => 'q_74839 => 'q_74799.
    (ALL (f::'q_74840) x::'q_74839.
        CASEWISE [] f x = (SOME y::'q_74799. True)) &
    (ALL (h::('q_74835 => 'q_74839) * ('q_74840 => 'q_74835 => 'q_74799))
        (t::(('q_74835 => 'q_74839) *
             ('q_74840 => 'q_74835 => 'q_74799)) list)
        (f::'q_74840) x::'q_74839.
        CASEWISE (h # t) f x =
        (if EX y::'q_74835. fst h y = x
         then snd h f (SOME y::'q_74835. fst h y = x) else CASEWISE t f x)))"
  by (import hollight DEF_CASEWISE)

definition
  admissible :: "('q_75137 => 'q_75130 => bool)
=> (('q_75137 => 'q_75133) => 'q_75143 => bool)
   => ('q_75143 => 'q_75130)
      => (('q_75137 => 'q_75133) => 'q_75143 => 'q_75138) => bool"  where
  "admissible ==
%(u::'q_75137 => 'q_75130 => bool)
   (ua::('q_75137 => 'q_75133) => 'q_75143 => bool)
   (ub::'q_75143 => 'q_75130)
   uc::('q_75137 => 'q_75133) => 'q_75143 => 'q_75138.
   ALL (f::'q_75137 => 'q_75133) (g::'q_75137 => 'q_75133) a::'q_75143.
      ua f a & ua g a & (ALL z::'q_75137. u z (ub a) --> f z = g z) -->
      uc f a = uc g a"

lemma DEF_admissible: "admissible =
(%(u::'q_75137 => 'q_75130 => bool)
    (ua::('q_75137 => 'q_75133) => 'q_75143 => bool)
    (ub::'q_75143 => 'q_75130)
    uc::('q_75137 => 'q_75133) => 'q_75143 => 'q_75138.
    ALL (f::'q_75137 => 'q_75133) (g::'q_75137 => 'q_75133) a::'q_75143.
       ua f a & ua g a & (ALL z::'q_75137. u z (ub a) --> f z = g z) -->
       uc f a = uc g a)"
  by (import hollight DEF_admissible)

definition
  tailadmissible :: "('A => 'A => bool)
=> (('A => 'B) => 'P => bool)
   => ('P => 'A) => (('A => 'B) => 'P => 'B) => bool"  where
  "tailadmissible ==
%(u::'A => 'A => bool) (ua::('A => 'B) => 'P => bool) (ub::'P => 'A)
   uc::('A => 'B) => 'P => 'B.
   EX (P::('A => 'B) => 'P => bool) (G::('A => 'B) => 'P => 'A)
      H::('A => 'B) => 'P => 'B.
      (ALL (f::'A => 'B) (a::'P) y::'A.
          P f a & u y (G f a) --> u y (ub a)) &
      (ALL (f::'A => 'B) (g::'A => 'B) a::'P.
          (ALL z::'A. u z (ub a) --> f z = g z) -->
          P f a = P g a & G f a = G g a & H f a = H g a) &
      (ALL (f::'A => 'B) a::'P.
          ua f a --> uc f a = (if P f a then f (G f a) else H f a))"

lemma DEF_tailadmissible: "tailadmissible =
(%(u::'A => 'A => bool) (ua::('A => 'B) => 'P => bool) (ub::'P => 'A)
    uc::('A => 'B) => 'P => 'B.
    EX (P::('A => 'B) => 'P => bool) (G::('A => 'B) => 'P => 'A)
       H::('A => 'B) => 'P => 'B.
       (ALL (f::'A => 'B) (a::'P) y::'A.
           P f a & u y (G f a) --> u y (ub a)) &
       (ALL (f::'A => 'B) (g::'A => 'B) a::'P.
           (ALL z::'A. u z (ub a) --> f z = g z) -->
           P f a = P g a & G f a = G g a & H f a = H g a) &
       (ALL (f::'A => 'B) a::'P.
           ua f a --> uc f a = (if P f a then f (G f a) else H f a)))"
  by (import hollight DEF_tailadmissible)

definition
  superadmissible :: "('q_75287 => 'q_75287 => bool)
=> (('q_75287 => 'q_75289) => 'q_75295 => bool)
   => ('q_75295 => 'q_75287)
      => (('q_75287 => 'q_75289) => 'q_75295 => 'q_75289) => bool"  where
  "superadmissible ==
%(u::'q_75287 => 'q_75287 => bool)
   (ua::('q_75287 => 'q_75289) => 'q_75295 => bool)
   (ub::'q_75295 => 'q_75287)
   uc::('q_75287 => 'q_75289) => 'q_75295 => 'q_75289.
   admissible u (%(f::'q_75287 => 'q_75289) a::'q_75295. True) ub ua -->
   tailadmissible u ua ub uc"

lemma DEF_superadmissible: "superadmissible =
(%(u::'q_75287 => 'q_75287 => bool)
    (ua::('q_75287 => 'q_75289) => 'q_75295 => bool)
    (ub::'q_75295 => 'q_75287)
    uc::('q_75287 => 'q_75289) => 'q_75295 => 'q_75289.
    admissible u (%(f::'q_75287 => 'q_75289) a::'q_75295. True) ub ua -->
    tailadmissible u ua ub uc)"
  by (import hollight DEF_superadmissible)

lemma MATCH_SEQPATTERN: "_MATCH (x::'q_75330)
 (_SEQPATTERN (r::'q_75330 => 'q_75323 => bool)
   (s::'q_75330 => 'q_75323 => bool)) =
(if Ex (r x) then _MATCH x r else _MATCH x s)"
  by (import hollight MATCH_SEQPATTERN)

lemma ADMISSIBLE_CONST: "admissible (u_556::'q_75351 => 'q_75350 => bool)
 (x::('q_75351 => 'q_75352) => 'q_75353 => bool) (xa::'q_75353 => 'q_75350)
 (%f::'q_75351 => 'q_75352. xb::'q_75353 => 'q_75354)"
  by (import hollight ADMISSIBLE_CONST)

lemma ADMISSIBLE_BASE: "(!!(f::'A => 'B) a::'P.
    (xa::('A => 'B) => 'P => bool) f a
    ==> (x::'A => 'A => bool) ((xc::'P => 'A) a) ((xb::'P => 'A) a))
==> admissible x xa xb (%(f::'A => 'B) x::'P. f (xc x))"
  by (import hollight ADMISSIBLE_BASE)

lemma ADMISSIBLE_COMB: "admissible (x::'A => 'A => bool) (xa::('A => 'B) => 'P => bool)
 (xb::'P => 'A) (xc::('A => 'B) => 'P => 'C => 'D) &
admissible x xa xb (xd::('A => 'B) => 'P => 'C)
==> admissible x xa xb (%(f::'A => 'B) x::'P. xc f x (xd f x))"
  by (import hollight ADMISSIBLE_COMB)

lemma ADMISSIBLE_RAND: "admissible (x::'A => 'A => bool) (xa::('A => 'B) => 'P => bool)
 (xb::'P => 'A) (xd::('A => 'B) => 'P => 'C)
==> admissible x xa xb
     (%(f::'A => 'B) x::'P. (xc::'P => 'C => 'D) x (xd f x))"
  by (import hollight ADMISSIBLE_RAND)

lemma ADMISSIBLE_LAMBDA: "admissible (x::'A => 'A => bool)
 (%f::'A => 'B.
     SOME fa::'C * 'P => bool.
        ALL (u::'C) x::'P. fa (u, x) = (xa::('A => 'B) => 'P => bool) f x)
 (SOME f::'C * 'P => 'A. ALL (u::'C) x::'P. f (u, x) = (xb::'P => 'A) x)
 (%f::'A => 'B.
     SOME fa::'C * 'P => bool.
        ALL (u::'C) x::'P.
           fa (u, x) = (xc::('A => 'B) => 'C => 'P => bool) f u x)
==> admissible x xa xb (%(f::'A => 'B) (x::'P) u::'C. xc f u x)"
  by (import hollight ADMISSIBLE_LAMBDA)

lemma ADMISSIBLE_NEST: "admissible (x::'A => 'A => bool) (xa::('A => 'B) => 'P => bool)
 (xb::'P => 'A) (xc::('A => 'B) => 'P => 'A) &
(ALL (f::'A => 'B) a::'P. xa f a --> x (xc f a) (xb a))
==> admissible x xa xb (%(f::'A => 'B) x::'P. f (xc f x))"
  by (import hollight ADMISSIBLE_NEST)

lemma ADMISSIBLE_COND: "admissible (u_556::'q_75688 => 'q_75687 => bool)
 (p::('q_75688 => 'q_75719) => 'P => bool) (s::'P => 'q_75687)
 (P::('q_75688 => 'q_75719) => 'P => bool) &
admissible u_556 (%(f::'q_75688 => 'q_75719) x::'P. p f x & P f x) s
 (h::('q_75688 => 'q_75719) => 'P => 'q_75744) &
admissible u_556 (%(f::'q_75688 => 'q_75719) x::'P. p f x & ~ P f x) s
 (k::('q_75688 => 'q_75719) => 'P => 'q_75744)
==> admissible u_556 p s
     (%(f::'q_75688 => 'q_75719) x::'P. if P f x then h f x else k f x)"
  by (import hollight ADMISSIBLE_COND)

lemma ADMISSIBLE_MATCH: "admissible (x::'q_75790 => 'q_75789 => bool)
 (xa::('q_75790 => 'q_75791) => 'P => bool) (xb::'P => 'q_75789)
 (xc::('q_75790 => 'q_75791) => 'P => 'q_75826) &
admissible x xa xb
 (%(f::'q_75790 => 'q_75791) x::'P.
     (c::('q_75790 => 'q_75791) => 'P => 'q_75826 => 'q_75823 => bool) f x
      (xc f x))
==> admissible x xa xb
     (%(f::'q_75790 => 'q_75791) x::'P. _MATCH (xc f x) (c f x))"
  by (import hollight ADMISSIBLE_MATCH)

lemma ADMISSIBLE_SEQPATTERN: "admissible (x::'q_75867 => 'q_75866 => bool)
 (xa::('q_75867 => 'q_75929) => 'P => bool) (xb::'P => 'q_75866)
 (%(f::'q_75867 => 'q_75929) x::'P.
     Ex ((xc::('q_75867 => 'q_75929) => 'P => 'q_75955 => 'q_75945 => bool)
          f x ((xe::('q_75867 => 'q_75929) => 'P => 'q_75955) f x))) &
admissible x
 (%(f::'q_75867 => 'q_75929) x::'P. xa f x & Ex (xc f x (xe f x))) xb
 (%(f::'q_75867 => 'q_75929) x::'P. xc f x (xe f x)) &
admissible x
 (%(f::'q_75867 => 'q_75929) x::'P. xa f x & ~ Ex (xc f x (xe f x))) xb
 (%(f::'q_75867 => 'q_75929) x::'P.
     (xd::('q_75867 => 'q_75929) => 'P => 'q_75955 => 'q_75945 => bool) f x
      (xe f x))
==> admissible x xa xb
     (%(f::'q_75867 => 'q_75929) x::'P.
         _SEQPATTERN (xc f x) (xd f x) (xe f x))"
  by (import hollight ADMISSIBLE_SEQPATTERN)

lemma ADMISSIBLE_UNGUARDED_PATTERN: "admissible (u_556::'q_76041 => 'q_76040 => bool)
 (p::('q_76041 => 'q_76088) => 'P => bool) (s::'P => 'q_76040)
 (pat::('q_76041 => 'q_76088) => 'P => 'q_76121) &
admissible u_556 p s (e::('q_76041 => 'q_76088) => 'P => 'q_76121) &
admissible u_556 (%(f::'q_76041 => 'q_76088) x::'P. p f x & pat f x = e f x)
 s (t::('q_76041 => 'q_76088) => 'P => 'q_76128) &
admissible u_556 (%(f::'q_76041 => 'q_76088) x::'P. p f x & pat f x = e f x)
 s (y::('q_76041 => 'q_76088) => 'P => 'q_76128)
==> admissible u_556 p s
     (%(f::'q_76041 => 'q_76088) x::'P.
         _UNGUARDED_PATTERN (pat f x = e f x) (t f x = y f x))"
  by (import hollight ADMISSIBLE_UNGUARDED_PATTERN)

lemma ADMISSIBLE_GUARDED_PATTERN: "admissible (u_556::'q_76215 => 'q_76214 => bool)
 (p::('q_76215 => 'q_76292) => 'P => bool) (s::'P => 'q_76214)
 (pat::('q_76215 => 'q_76292) => 'P => 'q_76330) &
admissible u_556 p s (e::('q_76215 => 'q_76292) => 'P => 'q_76330) &
admissible u_556
 (%(f::'q_76215 => 'q_76292) x::'P.
     p f x &
     pat f x = e f x & (q::('q_76215 => 'q_76292) => 'P => bool) f x)
 s (t::('q_76215 => 'q_76292) => 'P => 'q_76339) &
admissible u_556 (%(f::'q_76215 => 'q_76292) x::'P. p f x & pat f x = e f x)
 s q &
admissible u_556
 (%(f::'q_76215 => 'q_76292) x::'P. p f x & pat f x = e f x & q f x) s
 (y::('q_76215 => 'q_76292) => 'P => 'q_76339)
==> admissible u_556 p s
     (%(f::'q_76215 => 'q_76292) x::'P.
         _GUARDED_PATTERN (pat f x = e f x) (q f x) (t f x = y f x))"
  by (import hollight ADMISSIBLE_GUARDED_PATTERN)

lemma ADMISSIBLE_NSUM: "admissible (x::'B => 'A => bool)
 (%f::'B => 'C.
     SOME fa::nat * 'P => bool.
        ALL (k::nat) x::'P.
           fa (k, x) =
           ((xd::'P => nat) x <= k &
            k <= (xe::'P => nat) x & (xa::('B => 'C) => 'P => bool) f x))
 (SOME f::nat * 'P => 'A. ALL (k::nat) x::'P. f (k, x) = (xb::'P => 'A) x)
 (%f::'B => 'C.
     SOME fa::nat * 'P => nat.
        ALL (k::nat) x::'P.
           fa (k, x) = (xc::('B => 'C) => 'P => nat => nat) f x k)
==> admissible x xa xb (%(f::'B => 'C) x::'P. nsum {xd x..xe x} (xc f x))"
  by (import hollight ADMISSIBLE_NSUM)

lemma ADMISSIBLE_SUM: "admissible (x::'B => 'A => bool)
 (%f::'B => 'C.
     SOME fa::nat * 'P => bool.
        ALL (k::nat) x::'P.
           fa (k, x) =
           ((xd::'P => nat) x <= k &
            k <= (xe::'P => nat) x & (xa::('B => 'C) => 'P => bool) f x))
 (SOME f::nat * 'P => 'A. ALL (k::nat) x::'P. f (k, x) = (xb::'P => 'A) x)
 (%f::'B => 'C.
     SOME fa::nat * 'P => hollight.real.
        ALL (k::nat) x::'P.
           fa (k, x) = (xc::('B => 'C) => 'P => nat => hollight.real) f x k)
==> admissible x xa xb
     (%(f::'B => 'C) x::'P. hollight.sum {xd x..xe x} (xc f x))"
  by (import hollight ADMISSIBLE_SUM)

lemma ADMISSIBLE_MAP: "admissible (x::'A => 'q_76632 => bool) (xa::('A => 'B) => 'P => bool)
 (xb::'P => 'q_76632) (xd::('A => 'B) => 'P => 'q_76647 list) &
admissible x
 (%f::'A => 'B.
     SOME fa::'q_76647 * 'P => bool.
        ALL (y::'q_76647) x::'P. fa (y, x) = (xa f x & y : set (xd f x)))
 (SOME f::'q_76647 * 'P => 'q_76632.
     ALL (y::'q_76647) x::'P. f (y, x) = xb x)
 (%f::'A => 'B.
     SOME fa::'q_76647 * 'P => 'q_76641.
        ALL (y::'q_76647) x::'P.
           fa (y, x) = (xc::('A => 'B) => 'P => 'q_76647 => 'q_76641) f x y)
==> admissible x xa xb (%(f::'A => 'B) x::'P. map (xc f x) (xd f x))"
  by (import hollight ADMISSIBLE_MAP)

lemma ADMISSIBLE_MATCH_SEQPATTERN: "admissible (x::'q_76705 => 'q_76704 => bool)
 (xa::('q_76705 => 'q_76770) => 'P => bool) (xb::'P => 'q_76704)
 (%(f::'q_76705 => 'q_76770) x::'P.
     Ex ((xc::('q_76705 => 'q_76770) => 'P => 'q_76825 => 'q_76794 => bool)
          f x ((xe::('q_76705 => 'q_76770) => 'P => 'q_76825) f x))) &
admissible x
 (%(f::'q_76705 => 'q_76770) x::'P. xa f x & Ex (xc f x (xe f x))) xb
 (%(f::'q_76705 => 'q_76770) x::'P. _MATCH (xe f x) (xc f x)) &
admissible x
 (%(f::'q_76705 => 'q_76770) x::'P. xa f x & ~ Ex (xc f x (xe f x))) xb
 (%(f::'q_76705 => 'q_76770) x::'P.
     _MATCH (xe f x)
      ((xd::('q_76705 => 'q_76770) => 'P => 'q_76825 => 'q_76794 => bool) f
        x))
==> admissible x xa xb
     (%(x::'q_76705 => 'q_76770) xa::'P.
         _MATCH (xe x xa) (_SEQPATTERN (xc x xa) (xd x xa)))"
  by (import hollight ADMISSIBLE_MATCH_SEQPATTERN)

lemma ADMISSIBLE_IMP_SUPERADMISSIBLE: "admissible (x::'A => 'A => bool) (xa::('A => 'B) => 'P => bool)
 (xb::'P => 'A) (xc::('A => 'B) => 'P => 'B)
==> superadmissible x xa xb xc"
  by (import hollight ADMISSIBLE_IMP_SUPERADMISSIBLE)

lemma SUPERADMISSIBLE_CONST: "superadmissible (u_556::'q_76904 => 'q_76904 => bool)
 (p::('q_76904 => 'q_76906) => 'q_76905 => bool) (s::'q_76905 => 'q_76904)
 (%f::'q_76904 => 'q_76906. c::'q_76905 => 'q_76906)"
  by (import hollight SUPERADMISSIBLE_CONST)

lemma SUPERADMISSIBLE_TAIL: "admissible (x::'A => 'A => bool) (xa::('A => 'B) => 'P => bool)
 (xb::'P => 'A) (xc::('A => 'B) => 'P => 'A) &
(ALL (f::'A => 'B) a::'P.
    xa f a --> (ALL y::'A. x y (xc f a) --> x y (xb a)))
==> superadmissible x xa xb (%(f::'A => 'B) x::'P. f (xc f x))"
  by (import hollight SUPERADMISSIBLE_TAIL)

lemma SUPERADMISSIBLE_COND: "admissible (x::'A => 'A => bool) (xa::('A => 'B) => 'P => bool)
 (xc::'P => 'A) (xb::('A => 'B) => 'P => bool) &
superadmissible x (%(f::'A => 'B) x::'P. xa f x & xb f x) xc
 (xd::('A => 'B) => 'P => 'B) &
superadmissible x (%(f::'A => 'B) x::'P. xa f x & ~ xb f x) xc
 (xe::('A => 'B) => 'P => 'B)
==> superadmissible x xa xc
     (%(f::'A => 'B) x::'P. if xb f x then xd f x else xe f x)"
  by (import hollight SUPERADMISSIBLE_COND)

lemma SUPERADMISSIBLE_MATCH_SEQPATTERN: "admissible (x::'q_77225 => 'q_77225 => bool)
 (xa::('q_77225 => 'q_77341) => 'P => bool) (xb::'P => 'q_77225)
 (%(f::'q_77225 => 'q_77341) x::'P.
     Ex ((xc::('q_77225 => 'q_77341) => 'P => 'q_77340 => 'q_77341 => bool)
          f x ((xe::('q_77225 => 'q_77341) => 'P => 'q_77340) f x))) &
superadmissible x
 (%(f::'q_77225 => 'q_77341) x::'P. xa f x & Ex (xc f x (xe f x))) xb
 (%(f::'q_77225 => 'q_77341) x::'P. _MATCH (xe f x) (xc f x)) &
superadmissible x
 (%(f::'q_77225 => 'q_77341) x::'P. xa f x & ~ Ex (xc f x (xe f x))) xb
 (%(f::'q_77225 => 'q_77341) x::'P.
     _MATCH (xe f x)
      ((xd::('q_77225 => 'q_77341) => 'P => 'q_77340 => 'q_77341 => bool) f
        x))
==> superadmissible x xa xb
     (%(x::'q_77225 => 'q_77341) xa::'P.
         _MATCH (xe x xa) (_SEQPATTERN (xc x xa) (xd x xa)))"
  by (import hollight SUPERADMISSIBLE_MATCH_SEQPATTERN)

lemma SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN: "(ALL (f::'A => 'B) (a::'P) (t::'Q) u::'Q.
    (p::('A => 'B) => 'P => bool) f a &
    (pat::'Q => 'D) t = (e::'P => 'D) a & pat u = e a -->
    (arg::'P => 'Q => 'A) a t = arg a u) &
(ALL (f::'A => 'B) (a::'P) t::'Q.
    p f a & pat t = e a -->
    (ALL y::'A.
        (u_556::'A => 'A => bool) y (arg a t) -->
        u_556 y ((s::'P => 'A) a)))
==> superadmissible u_556 p s
     (%(f::'A => 'B) x::'P.
         _MATCH (e x)
          (%(u::'D) v::'B.
              EX t::'Q. _UNGUARDED_PATTERN (pat t = u) (f (arg x t) = v)))"
  by (import hollight SUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN)

lemma SUPERADMISSIBLE_MATCH_GUARDED_PATTERN: "(ALL (f::'A => 'B) (a::'P) (t::'Q) u::'Q.
    (p::('A => 'B) => 'P => bool) f a &
    (pat::'Q => 'D) t = (e::'P => 'D) a &
    (q::'P => 'Q => bool) a t & pat u = e a & q a u -->
    (arg::'P => 'Q => 'A) a t = arg a u) &
(ALL (f::'A => 'B) (a::'P) t::'Q.
    p f a & q a t & pat t = e a -->
    (ALL y::'A.
        (u_556::'A => 'A => bool) y (arg a t) -->
        u_556 y ((s::'P => 'A) a)))
==> superadmissible u_556 p s
     (%(f::'A => 'B) x::'P.
         _MATCH (e x)
          (%(u::'D) v::'B.
              EX t::'Q.
                 _GUARDED_PATTERN (pat t = u) (q x t) (f (arg x t) = v)))"
  by (import hollight SUPERADMISSIBLE_MATCH_GUARDED_PATTERN)

lemma cth: "[| !!(c::'q_78547) (x::'A) y::'A.
      (p1::'A => 'q_78536) x = (p1'::'A => 'q_78536) y
      ==> (p2::'q_78547 => 'A => 'q_78541) c x =
          (p2'::'q_78547 => 'A => 'q_78541) c y;
   p1' (x::'A) = p1 (y::'A) |]
==> p2' (c::'q_78547) x = p2 c y"
  by (import hollight cth)

lemma SUPERADMISSIBLE_T: "superadmissible (u_556::'q_78694 => 'q_78694 => bool)
 (%(f::'q_78694 => 'q_78696) x::'q_78700. True) (s::'q_78700 => 'q_78694)
 (t::('q_78694 => 'q_78696) => 'q_78700 => 'q_78696) =
tailadmissible u_556 (%(f::'q_78694 => 'q_78696) x::'q_78700. True) s t"
  by (import hollight SUPERADMISSIBLE_T)

lemma elemma0: "(ALL z::'q_78985 * 'q_78984.
    (f::'q_78985 * 'q_78984 => 'q_78975) z =
    (g::'q_78985 * 'q_78984 => 'q_78975) z) =
(ALL (x::'q_78985) y::'q_78984. f (x, y) = g (x, y)) &
(P::'q_79002 * 'q_79001 => 'q_78994) =
(SOME f::'q_79002 * 'q_79001 => 'q_78994.
    ALL (x::'q_79002) y::'q_79001. f (x, y) = P (x, y))"
  by (import hollight elemma0)

;end_setup

end

