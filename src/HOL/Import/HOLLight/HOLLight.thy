(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOLLight imports "../HOLLightCompat" "../HOL4Syntax" begin

;setup_theory hollight

consts
  "_FALSITY_" :: "bool" ("'_FALSITY'_")

defs
  "_FALSITY__def": "_FALSITY_ == False"

lemma DEF__FALSITY_: "_FALSITY_ = False"
  by (import hollight DEF__FALSITY_)

lemma CONJ_ACI: "((p::bool) & (q::bool)) = (q & p) &
((p & q) & (r::bool)) = (p & q & r) &
(p & q & r) = (q & p & r) & (p & p) = p & (p & p & q) = (p & q)"
  by (import hollight CONJ_ACI)

lemma DISJ_ACI: "((p::bool) | (q::bool)) = (q | p) &
((p | q) | (r::bool)) = (p | q | r) &
(p | q | r) = (q | p | r) & (p | p) = p & (p | p | q) = (p | q)"
  by (import hollight DISJ_ACI)

lemma EQ_CLAUSES: "ALL t::bool.
   (True = t) = t &
   (t = True) = t & (False = t) = (~ t) & (t = False) = (~ t)"
  by (import hollight EQ_CLAUSES)

lemma NOT_CLAUSES_WEAK: "(~ True) = False & (~ False) = True"
  by (import hollight NOT_CLAUSES_WEAK)

lemma AND_CLAUSES: "ALL t::bool.
   (True & t) = t &
   (t & True) = t & (False & t) = False & (t & False) = False & (t & t) = t"
  by (import hollight AND_CLAUSES)

lemma OR_CLAUSES: "ALL t::bool.
   (True | t) = True &
   (t | True) = True & (False | t) = t & (t | False) = t & (t | t) = t"
  by (import hollight OR_CLAUSES)

lemma IMP_CLAUSES: "ALL t::bool.
   (True --> t) = t &
   (t --> True) = True &
   (False --> t) = True & (t --> t) = True & (t --> False) = (~ t)"
  by (import hollight IMP_CLAUSES)

lemma IMP_EQ_CLAUSE: "((x::'q_864::type) = x --> (p::bool)) = p"
  by (import hollight IMP_EQ_CLAUSE)

lemma SWAP_FORALL_THM: "ALL P::'A::type => 'B::type => bool.
   (ALL x::'A::type. All (P x)) = (ALL (y::'B::type) x::'A::type. P x y)"
  by (import hollight SWAP_FORALL_THM)

lemma SWAP_EXISTS_THM: "ALL P::'A::type => 'B::type => bool.
   (EX x::'A::type. Ex (P x)) = (EX (x::'B::type) xa::'A::type. P xa x)"
  by (import hollight SWAP_EXISTS_THM)

lemma TRIV_EXISTS_AND_THM: "ALL (P::bool) Q::bool.
   (EX x::'A::type. P & Q) = ((EX x::'A::type. P) & (EX x::'A::type. Q))"
  by (import hollight TRIV_EXISTS_AND_THM)

lemma TRIV_AND_EXISTS_THM: "ALL (P::bool) Q::bool.
   ((EX x::'A::type. P) & (EX x::'A::type. Q)) = (EX x::'A::type. P & Q)"
  by (import hollight TRIV_AND_EXISTS_THM)

lemma TRIV_FORALL_OR_THM: "ALL (P::bool) Q::bool.
   (ALL x::'A::type. P | Q) = ((ALL x::'A::type. P) | (ALL x::'A::type. Q))"
  by (import hollight TRIV_FORALL_OR_THM)

lemma TRIV_OR_FORALL_THM: "ALL (P::bool) Q::bool.
   ((ALL x::'A::type. P) | (ALL x::'A::type. Q)) = (ALL x::'A::type. P | Q)"
  by (import hollight TRIV_OR_FORALL_THM)

lemma TRIV_FORALL_IMP_THM: "ALL (P::bool) Q::bool.
   (ALL x::'A::type. P --> Q) =
   ((EX x::'A::type. P) --> (ALL x::'A::type. Q))"
  by (import hollight TRIV_FORALL_IMP_THM)

lemma TRIV_EXISTS_IMP_THM: "ALL (P::bool) Q::bool.
   (EX x::'A::type. P --> Q) =
   ((ALL x::'A::type. P) --> (EX x::'A::type. Q))"
  by (import hollight TRIV_EXISTS_IMP_THM)

lemma EXISTS_UNIQUE_ALT: "ALL P::'A::type => bool.
   Ex1 P = (EX x::'A::type. ALL y::'A::type. P y = (x = y))"
  by (import hollight EXISTS_UNIQUE_ALT)

lemma SELECT_UNIQUE: "ALL (P::'A::type => bool) x::'A::type.
   (ALL y::'A::type. P y = (y = x)) --> Eps P = x"
  by (import hollight SELECT_UNIQUE)

lemma EXCLUDED_MIDDLE: "ALL t::bool. t | ~ t"
  by (import hollight EXCLUDED_MIDDLE)

constdefs
  COND :: "bool => 'A => 'A => 'A" 
  "COND ==
%(t::bool) (t1::'A::type) t2::'A::type.
   SOME x::'A::type. (t = True --> x = t1) & (t = False --> x = t2)"

lemma DEF_COND: "COND =
(%(t::bool) (t1::'A::type) t2::'A::type.
    SOME x::'A::type. (t = True --> x = t1) & (t = False --> x = t2))"
  by (import hollight DEF_COND)

lemma COND_CLAUSES: "ALL (x::'A::type) xa::'A::type. COND True x xa = x & COND False x xa = xa"
  by (import hollight COND_CLAUSES)

lemma COND_EXPAND: "ALL (b::bool) (t1::bool) t2::bool. COND b t1 t2 = ((~ b | t1) & (b | t2))"
  by (import hollight COND_EXPAND)

lemma COND_ID: "ALL (b::bool) t::'A::type. COND b t t = t"
  by (import hollight COND_ID)

lemma COND_RAND: "ALL (b::bool) (f::'A::type => 'B::type) (x::'A::type) y::'A::type.
   f (COND b x y) = COND b (f x) (f y)"
  by (import hollight COND_RAND)

lemma COND_RATOR: "ALL (b::bool) (f::'A::type => 'B::type) (g::'A::type => 'B::type)
   x::'A::type. COND b f g x = COND b (f x) (g x)"
  by (import hollight COND_RATOR)

lemma COND_ABS: "ALL (b::bool) (f::'A::type => 'B::type) g::'A::type => 'B::type.
   (%x::'A::type. COND b (f x) (g x)) = COND b f g"
  by (import hollight COND_ABS)

lemma MONO_COND: "((A::bool) --> (B::bool)) & ((C::bool) --> (D::bool)) -->
COND (b::bool) A C --> COND b B D"
  by (import hollight MONO_COND)

lemma COND_ELIM_THM: "(P::'A::type => bool) (COND (c::bool) (x::'A::type) (y::'A::type)) =
((c --> P x) & (~ c --> P y))"
  by (import hollight COND_ELIM_THM)

lemma SKOLEM_THM: "ALL P::'A::type => 'B::type => bool.
   (ALL x::'A::type. Ex (P x)) =
   (EX x::'A::type => 'B::type. ALL xa::'A::type. P xa (x xa))"
  by (import hollight SKOLEM_THM)

lemma UNIQUE_SKOLEM_ALT: "ALL P::'A::type => 'B::type => bool.
   (ALL x::'A::type. Ex1 (P x)) =
   (EX f::'A::type => 'B::type.
       ALL (x::'A::type) y::'B::type. P x y = (f x = y))"
  by (import hollight UNIQUE_SKOLEM_ALT)

lemma COND_EQ_CLAUSE: "COND ((x::'q_3000::type) = x) (y::'q_2993::type) (z::'q_2993::type) = y"
  by (import hollight COND_EQ_CLAUSE)

lemma o_ASSOC: "ALL (f::'C::type => 'D::type) (g::'B::type => 'C::type)
   h::'A::type => 'B::type. f o (g o h) = f o g o h"
  by (import hollight o_ASSOC)

lemma I_O_ID: "ALL f::'A::type => 'B::type. id o f = f & f o id = f"
  by (import hollight I_O_ID)

lemma EXISTS_ONE_REP: "EX x::bool. x"
  by (import hollight EXISTS_ONE_REP)

lemma one_axiom: "ALL f::'A::type => unit. All (op = f)"
  by (import hollight one_axiom)

lemma one_RECURSION: "ALL e::'A::type. EX x::unit => 'A::type. x () = e"
  by (import hollight one_RECURSION)

lemma one_Axiom: "ALL e::'A::type. EX! fn::unit => 'A::type. fn () = e"
  by (import hollight one_Axiom)

lemma th_cond: "(P::'A::type => bool => bool) (COND (b::bool) (x::'A::type) (y::'A::type))
 b =
(b & P x True | ~ b & P y False)"
  by (import hollight th_cond)

constdefs
  LET_END :: "'A => 'A" 
  "LET_END == %t::'A::type. t"

lemma DEF_LET_END: "LET_END = (%t::'A::type. t)"
  by (import hollight DEF_LET_END)

constdefs
  GABS :: "('A => bool) => 'A" 
  "(op ==::(('A::type => bool) => 'A::type)
        => (('A::type => bool) => 'A::type) => prop)
 (GABS::('A::type => bool) => 'A::type)
 (Eps::('A::type => bool) => 'A::type)"

lemma DEF_GABS: "(op =::(('A::type => bool) => 'A::type)
       => (('A::type => bool) => 'A::type) => bool)
 (GABS::('A::type => bool) => 'A::type)
 (Eps::('A::type => bool) => 'A::type)"
  by (import hollight DEF_GABS)

constdefs
  GEQ :: "'A => 'A => bool" 
  "(op ==::('A::type => 'A::type => bool)
        => ('A::type => 'A::type => bool) => prop)
 (GEQ::'A::type => 'A::type => bool) (op =::'A::type => 'A::type => bool)"

lemma DEF_GEQ: "(op =::('A::type => 'A::type => bool)
       => ('A::type => 'A::type => bool) => bool)
 (GEQ::'A::type => 'A::type => bool) (op =::'A::type => 'A::type => bool)"
  by (import hollight DEF_GEQ)

lemma PAIR_EXISTS_THM: "EX (x::'A::type => 'B::type => bool) (a::'A::type) b::'B::type.
   x = Pair_Rep a b"
  by (import hollight PAIR_EXISTS_THM)

constdefs
  CURRY :: "('A * 'B => 'C) => 'A => 'B => 'C" 
  "CURRY ==
%(u::'A::type * 'B::type => 'C::type) (ua::'A::type) ub::'B::type.
   u (ua, ub)"

lemma DEF_CURRY: "CURRY =
(%(u::'A::type * 'B::type => 'C::type) (ua::'A::type) ub::'B::type.
    u (ua, ub))"
  by (import hollight DEF_CURRY)

constdefs
  UNCURRY :: "('A => 'B => 'C) => 'A * 'B => 'C" 
  "UNCURRY ==
%(u::'A::type => 'B::type => 'C::type) ua::'A::type * 'B::type.
   u (fst ua) (snd ua)"

lemma DEF_UNCURRY: "UNCURRY =
(%(u::'A::type => 'B::type => 'C::type) ua::'A::type * 'B::type.
    u (fst ua) (snd ua))"
  by (import hollight DEF_UNCURRY)

constdefs
  PASSOC :: "(('A * 'B) * 'C => 'D) => 'A * 'B * 'C => 'D" 
  "PASSOC ==
%(u::('A::type * 'B::type) * 'C::type => 'D::type)
   ua::'A::type * 'B::type * 'C::type.
   u ((fst ua, fst (snd ua)), snd (snd ua))"

lemma DEF_PASSOC: "PASSOC =
(%(u::('A::type * 'B::type) * 'C::type => 'D::type)
    ua::'A::type * 'B::type * 'C::type.
    u ((fst ua, fst (snd ua)), snd (snd ua)))"
  by (import hollight DEF_PASSOC)

lemma num_Axiom: "ALL (e::'A::type) f::'A::type => nat => 'A::type.
   EX! fn::nat => 'A::type. fn 0 = e & (ALL n::nat. fn (Suc n) = f (fn n) n)"
  by (import hollight num_Axiom)

lemma ADD_CLAUSES: "(ALL x::nat. 0 + x = x) &
(ALL x::nat. x + 0 = x) &
(ALL (x::nat) xa::nat. Suc x + xa = Suc (x + xa)) &
(ALL (x::nat) xa::nat. x + Suc xa = Suc (x + xa))"
  by (import hollight ADD_CLAUSES)

lemma ADD_AC: "(m::nat) + (n::nat) = n + m &
m + n + (p::nat) = m + (n + p) & m + (n + p) = n + (m + p)"
  by (import hollight ADD_AC)

lemma EQ_ADD_LCANCEL_0: "ALL (m::nat) n::nat. (m + n = m) = (n = 0)"
  by (import hollight EQ_ADD_LCANCEL_0)

lemma EQ_ADD_RCANCEL_0: "ALL (x::nat) xa::nat. (x + xa = xa) = (x = 0)"
  by (import hollight EQ_ADD_RCANCEL_0)

lemma ONE: "NUMERAL_BIT1 0 = Suc 0"
  by (import hollight ONE)

lemma TWO: "NUMERAL_BIT0 (NUMERAL_BIT1 0) = Suc (NUMERAL_BIT1 0)"
  by (import hollight TWO)

lemma ADD1: "ALL x::nat. Suc x = x + NUMERAL_BIT1 0"
  by (import hollight ADD1)

lemma MULT_CLAUSES: "(ALL x::nat. 0 * x = 0) &
(ALL x::nat. x * 0 = 0) &
(ALL x::nat. NUMERAL_BIT1 0 * x = x) &
(ALL x::nat. x * NUMERAL_BIT1 0 = x) &
(ALL (x::nat) xa::nat. Suc x * xa = x * xa + xa) &
(ALL (x::nat) xa::nat. x * Suc xa = x + x * xa)"
  by (import hollight MULT_CLAUSES)

lemma MULT_AC: "(m::nat) * (n::nat) = n * m &
m * n * (p::nat) = m * (n * p) & m * (n * p) = n * (m * p)"
  by (import hollight MULT_AC)

lemma MULT_2: "ALL n::nat. NUMERAL_BIT0 (NUMERAL_BIT1 0) * n = n + n"
  by (import hollight MULT_2)

lemma MULT_EQ_1: "ALL (m::nat) n::nat.
   (m * n = NUMERAL_BIT1 0) = (m = NUMERAL_BIT1 0 & n = NUMERAL_BIT1 0)"
  by (import hollight MULT_EQ_1)

constdefs
  EXP :: "nat => nat => nat" 
  "EXP ==
SOME EXP::nat => nat => nat.
   (ALL m::nat. EXP m 0 = NUMERAL_BIT1 0) &
   (ALL (m::nat) n::nat. EXP m (Suc n) = m * EXP m n)"

lemma DEF_EXP: "EXP =
(SOME EXP::nat => nat => nat.
    (ALL m::nat. EXP m 0 = NUMERAL_BIT1 0) &
    (ALL (m::nat) n::nat. EXP m (Suc n) = m * EXP m n))"
  by (import hollight DEF_EXP)

lemma EXP_EQ_0: "ALL (m::nat) n::nat. (EXP m n = 0) = (m = 0 & n ~= 0)"
  by (import hollight EXP_EQ_0)

lemma EXP_ADD: "ALL (m::nat) (n::nat) p::nat. EXP m (n + p) = EXP m n * EXP m p"
  by (import hollight EXP_ADD)

lemma EXP_ONE: "ALL n::nat. EXP (NUMERAL_BIT1 0) n = NUMERAL_BIT1 0"
  by (import hollight EXP_ONE)

lemma EXP_1: "ALL x::nat. EXP x (NUMERAL_BIT1 0) = x"
  by (import hollight EXP_1)

lemma EXP_2: "ALL x::nat. EXP x (NUMERAL_BIT0 (NUMERAL_BIT1 0)) = x * x"
  by (import hollight EXP_2)

lemma MULT_EXP: "ALL (p::nat) (m::nat) n::nat. EXP (m * n) p = EXP m p * EXP n p"
  by (import hollight MULT_EXP)

lemma EXP_MULT: "ALL (m::nat) (n::nat) p::nat. EXP m (n * p) = EXP (EXP m n) p"
  by (import hollight EXP_MULT)

consts
  "<=" :: "nat => nat => bool" ("<=")

defs
  "<=_def": "<= ==
SOME u::nat => nat => bool.
   (ALL m::nat. u m 0 = (m = 0)) &
   (ALL (m::nat) n::nat. u m (Suc n) = (m = Suc n | u m n))"

lemma DEF__lessthan__equal_: "<= =
(SOME u::nat => nat => bool.
    (ALL m::nat. u m 0 = (m = 0)) &
    (ALL (m::nat) n::nat. u m (Suc n) = (m = Suc n | u m n)))"
  by (import hollight DEF__lessthan__equal_)

consts
  "<" :: "nat => nat => bool" ("<")

defs
  "<_def": "< ==
SOME u::nat => nat => bool.
   (ALL m::nat. u m 0 = False) &
   (ALL (m::nat) n::nat. u m (Suc n) = (m = n | u m n))"

lemma DEF__lessthan_: "< =
(SOME u::nat => nat => bool.
    (ALL m::nat. u m 0 = False) &
    (ALL (m::nat) n::nat. u m (Suc n) = (m = n | u m n)))"
  by (import hollight DEF__lessthan_)

consts
  ">=" :: "nat => nat => bool" (">=")

defs
  ">=_def": ">= == %(u::nat) ua::nat. <= ua u"

lemma DEF__greaterthan__equal_: ">= = (%(u::nat) ua::nat. <= ua u)"
  by (import hollight DEF__greaterthan__equal_)

consts
  ">" :: "nat => nat => bool" (">")

defs
  ">_def": "> == %(u::nat) ua::nat. < ua u"

lemma DEF__greaterthan_: "> = (%(u::nat) ua::nat. < ua u)"
  by (import hollight DEF__greaterthan_)

lemma LE_SUC_LT: "ALL (m::nat) n::nat. <= (Suc m) n = < m n"
  by (import hollight LE_SUC_LT)

lemma LT_SUC_LE: "ALL (m::nat) n::nat. < m (Suc n) = <= m n"
  by (import hollight LT_SUC_LE)

lemma LE_SUC: "ALL (x::nat) xa::nat. <= (Suc x) (Suc xa) = <= x xa"
  by (import hollight LE_SUC)

lemma LT_SUC: "ALL (x::nat) xa::nat. < (Suc x) (Suc xa) = < x xa"
  by (import hollight LT_SUC)

lemma LE_0: "All (<= 0)"
  by (import hollight LE_0)

lemma LT_0: "ALL x::nat. < 0 (Suc x)"
  by (import hollight LT_0)

lemma LE_REFL: "ALL n::nat. <= n n"
  by (import hollight LE_REFL)

lemma LT_REFL: "ALL n::nat. ~ < n n"
  by (import hollight LT_REFL)

lemma LE_ANTISYM: "ALL (m::nat) n::nat. (<= m n & <= n m) = (m = n)"
  by (import hollight LE_ANTISYM)

lemma LT_ANTISYM: "ALL (m::nat) n::nat. ~ (< m n & < n m)"
  by (import hollight LT_ANTISYM)

lemma LET_ANTISYM: "ALL (m::nat) n::nat. ~ (<= m n & < n m)"
  by (import hollight LET_ANTISYM)

lemma LTE_ANTISYM: "ALL (x::nat) xa::nat. ~ (< x xa & <= xa x)"
  by (import hollight LTE_ANTISYM)

lemma LE_TRANS: "ALL (m::nat) (n::nat) p::nat. <= m n & <= n p --> <= m p"
  by (import hollight LE_TRANS)

lemma LT_TRANS: "ALL (m::nat) (n::nat) p::nat. < m n & < n p --> < m p"
  by (import hollight LT_TRANS)

lemma LET_TRANS: "ALL (m::nat) (n::nat) p::nat. <= m n & < n p --> < m p"
  by (import hollight LET_TRANS)

lemma LTE_TRANS: "ALL (m::nat) (n::nat) p::nat. < m n & <= n p --> < m p"
  by (import hollight LTE_TRANS)

lemma LE_CASES: "ALL (m::nat) n::nat. <= m n | <= n m"
  by (import hollight LE_CASES)

lemma LT_CASES: "ALL (m::nat) n::nat. < m n | < n m | m = n"
  by (import hollight LT_CASES)

lemma LET_CASES: "ALL (m::nat) n::nat. <= m n | < n m"
  by (import hollight LET_CASES)

lemma LTE_CASES: "ALL (x::nat) xa::nat. < x xa | <= xa x"
  by (import hollight LTE_CASES)

lemma LT_NZ: "ALL n::nat. < 0 n = (n ~= 0)"
  by (import hollight LT_NZ)

lemma LE_LT: "ALL (m::nat) n::nat. <= m n = (< m n | m = n)"
  by (import hollight LE_LT)

lemma LT_LE: "ALL (x::nat) xa::nat. < x xa = (<= x xa & x ~= xa)"
  by (import hollight LT_LE)

lemma NOT_LE: "ALL (m::nat) n::nat. (~ <= m n) = < n m"
  by (import hollight NOT_LE)

lemma NOT_LT: "ALL (m::nat) n::nat. (~ < m n) = <= n m"
  by (import hollight NOT_LT)

lemma LT_IMP_LE: "ALL (x::nat) xa::nat. < x xa --> <= x xa"
  by (import hollight LT_IMP_LE)

lemma EQ_IMP_LE: "ALL (m::nat) n::nat. m = n --> <= m n"
  by (import hollight EQ_IMP_LE)

lemma LE_EXISTS: "ALL (m::nat) n::nat. <= m n = (EX d::nat. n = m + d)"
  by (import hollight LE_EXISTS)

lemma LT_EXISTS: "ALL (m::nat) n::nat. < m n = (EX d::nat. n = m + Suc d)"
  by (import hollight LT_EXISTS)

lemma LE_ADD: "ALL (m::nat) n::nat. <= m (m + n)"
  by (import hollight LE_ADD)

lemma LE_ADDR: "ALL (x::nat) xa::nat. <= xa (x + xa)"
  by (import hollight LE_ADDR)

lemma LT_ADD: "ALL (m::nat) n::nat. < m (m + n) = < 0 n"
  by (import hollight LT_ADD)

lemma LT_ADDR: "ALL (x::nat) xa::nat. < xa (x + xa) = < 0 x"
  by (import hollight LT_ADDR)

lemma LE_ADD_LCANCEL: "ALL (x::nat) (xa::nat) xb::nat. <= (x + xa) (x + xb) = <= xa xb"
  by (import hollight LE_ADD_LCANCEL)

lemma LE_ADD_RCANCEL: "ALL (x::nat) (xa::nat) xb::nat. <= (x + xb) (xa + xb) = <= x xa"
  by (import hollight LE_ADD_RCANCEL)

lemma LT_ADD_LCANCEL: "ALL (x::nat) (xa::nat) xb::nat. < (x + xa) (x + xb) = < xa xb"
  by (import hollight LT_ADD_LCANCEL)

lemma LT_ADD_RCANCEL: "ALL (x::nat) (xa::nat) xb::nat. < (x + xb) (xa + xb) = < x xa"
  by (import hollight LT_ADD_RCANCEL)

lemma LE_ADD2: "ALL (m::nat) (n::nat) (p::nat) q::nat.
   <= m p & <= n q --> <= (m + n) (p + q)"
  by (import hollight LE_ADD2)

lemma LET_ADD2: "ALL (m::nat) (n::nat) (p::nat) q::nat. <= m p & < n q --> < (m + n) (p + q)"
  by (import hollight LET_ADD2)

lemma LTE_ADD2: "ALL (x::nat) (xa::nat) (xb::nat) xc::nat.
   < x xb & <= xa xc --> < (x + xa) (xb + xc)"
  by (import hollight LTE_ADD2)

lemma LT_ADD2: "ALL (m::nat) (n::nat) (p::nat) q::nat. < m p & < n q --> < (m + n) (p + q)"
  by (import hollight LT_ADD2)

lemma LT_MULT: "ALL (m::nat) n::nat. < 0 (m * n) = (< 0 m & < 0 n)"
  by (import hollight LT_MULT)

lemma LE_MULT2: "ALL (m::nat) (n::nat) (p::nat) q::nat.
   <= m n & <= p q --> <= (m * p) (n * q)"
  by (import hollight LE_MULT2)

lemma LT_LMULT: "ALL (m::nat) (n::nat) p::nat. m ~= 0 & < n p --> < (m * n) (m * p)"
  by (import hollight LT_LMULT)

lemma LE_MULT_LCANCEL: "ALL (m::nat) (n::nat) p::nat. <= (m * n) (m * p) = (m = 0 | <= n p)"
  by (import hollight LE_MULT_LCANCEL)

lemma LE_MULT_RCANCEL: "ALL (x::nat) (xa::nat) xb::nat. <= (x * xb) (xa * xb) = (<= x xa | xb = 0)"
  by (import hollight LE_MULT_RCANCEL)

lemma LT_MULT_LCANCEL: "ALL (m::nat) (n::nat) p::nat. < (m * n) (m * p) = (m ~= 0 & < n p)"
  by (import hollight LT_MULT_LCANCEL)

lemma LT_MULT_RCANCEL: "ALL (x::nat) (xa::nat) xb::nat. < (x * xb) (xa * xb) = (< x xa & xb ~= 0)"
  by (import hollight LT_MULT_RCANCEL)

lemma LT_MULT2: "ALL (m::nat) (n::nat) (p::nat) q::nat. < m n & < p q --> < (m * p) (n * q)"
  by (import hollight LT_MULT2)

lemma LE_SQUARE_REFL: "ALL n::nat. <= n (n * n)"
  by (import hollight LE_SQUARE_REFL)

lemma WLOG_LE: "(ALL (m::nat) n::nat. (P::nat => nat => bool) m n = P n m) &
(ALL (m::nat) n::nat. <= m n --> P m n) -->
(ALL m::nat. All (P m))"
  by (import hollight WLOG_LE)

lemma WLOG_LT: "(ALL m::nat. (P::nat => nat => bool) m m) &
(ALL (m::nat) n::nat. P m n = P n m) &
(ALL (m::nat) n::nat. < m n --> P m n) -->
(ALL m::nat. All (P m))"
  by (import hollight WLOG_LT)

lemma num_WF: "ALL P::nat => bool.
   (ALL n::nat. (ALL m::nat. < m n --> P m) --> P n) --> All P"
  by (import hollight num_WF)

lemma num_WOP: "ALL P::nat => bool. Ex P = (EX n::nat. P n & (ALL m::nat. < m n --> ~ P m))"
  by (import hollight num_WOP)

lemma num_MAX: "ALL P::nat => bool.
   (Ex P & (EX M::nat. ALL x::nat. P x --> <= x M)) =
   (EX m::nat. P m & (ALL x::nat. P x --> <= x m))"
  by (import hollight num_MAX)

constdefs
  EVEN :: "nat => bool" 
  "EVEN ==
SOME EVEN::nat => bool.
   EVEN 0 = True & (ALL n::nat. EVEN (Suc n) = (~ EVEN n))"

lemma DEF_EVEN: "EVEN =
(SOME EVEN::nat => bool.
    EVEN 0 = True & (ALL n::nat. EVEN (Suc n) = (~ EVEN n)))"
  by (import hollight DEF_EVEN)

constdefs
  ODD :: "nat => bool" 
  "ODD ==
SOME ODD::nat => bool. ODD 0 = False & (ALL n::nat. ODD (Suc n) = (~ ODD n))"

lemma DEF_ODD: "ODD =
(SOME ODD::nat => bool.
    ODD 0 = False & (ALL n::nat. ODD (Suc n) = (~ ODD n)))"
  by (import hollight DEF_ODD)

lemma NOT_EVEN: "ALL n::nat. (~ EVEN n) = ODD n"
  by (import hollight NOT_EVEN)

lemma NOT_ODD: "ALL n::nat. (~ ODD n) = EVEN n"
  by (import hollight NOT_ODD)

lemma EVEN_OR_ODD: "ALL n::nat. EVEN n | ODD n"
  by (import hollight EVEN_OR_ODD)

lemma EVEN_AND_ODD: "ALL x::nat. ~ (EVEN x & ODD x)"
  by (import hollight EVEN_AND_ODD)

lemma EVEN_ADD: "ALL (m::nat) n::nat. EVEN (m + n) = (EVEN m = EVEN n)"
  by (import hollight EVEN_ADD)

lemma EVEN_MULT: "ALL (m::nat) n::nat. EVEN (m * n) = (EVEN m | EVEN n)"
  by (import hollight EVEN_MULT)

lemma EVEN_EXP: "ALL (m::nat) n::nat. EVEN (EXP m n) = (EVEN m & n ~= 0)"
  by (import hollight EVEN_EXP)

lemma ODD_ADD: "ALL (m::nat) n::nat. ODD (m + n) = (ODD m ~= ODD n)"
  by (import hollight ODD_ADD)

lemma ODD_MULT: "ALL (m::nat) n::nat. ODD (m * n) = (ODD m & ODD n)"
  by (import hollight ODD_MULT)

lemma ODD_EXP: "ALL (m::nat) n::nat. ODD (EXP m n) = (ODD m | n = 0)"
  by (import hollight ODD_EXP)

lemma EVEN_DOUBLE: "ALL n::nat. EVEN (NUMERAL_BIT0 (NUMERAL_BIT1 0) * n)"
  by (import hollight EVEN_DOUBLE)

lemma ODD_DOUBLE: "ALL x::nat. ODD (Suc (NUMERAL_BIT0 (NUMERAL_BIT1 0) * x))"
  by (import hollight ODD_DOUBLE)

lemma EVEN_EXISTS_LEMMA: "ALL n::nat.
   (EVEN n --> (EX m::nat. n = NUMERAL_BIT0 (NUMERAL_BIT1 0) * m)) &
   (~ EVEN n --> (EX m::nat. n = Suc (NUMERAL_BIT0 (NUMERAL_BIT1 0) * m)))"
  by (import hollight EVEN_EXISTS_LEMMA)

lemma EVEN_EXISTS: "ALL n::nat. EVEN n = (EX m::nat. n = NUMERAL_BIT0 (NUMERAL_BIT1 0) * m)"
  by (import hollight EVEN_EXISTS)

lemma ODD_EXISTS: "ALL n::nat. ODD n = (EX m::nat. n = Suc (NUMERAL_BIT0 (NUMERAL_BIT1 0) * m))"
  by (import hollight ODD_EXISTS)

lemma EVEN_ODD_DECOMPOSITION: "ALL n::nat.
   (EX (k::nat) m::nat.
       ODD m & n = EXP (NUMERAL_BIT0 (NUMERAL_BIT1 0)) k * m) =
   (n ~= 0)"
  by (import hollight EVEN_ODD_DECOMPOSITION)

lemma SUB_0: "ALL x::nat. 0 - x = 0 & x - 0 = x"
  by (import hollight SUB_0)

lemma SUB_PRESUC: "ALL (m::nat) n::nat. Pred (Suc m - n) = m - n"
  by (import hollight SUB_PRESUC)

lemma SUB_EQ_0: "ALL (m::nat) n::nat. (m - n = 0) = <= m n"
  by (import hollight SUB_EQ_0)

lemma ADD_SUBR: "ALL (x::nat) xa::nat. xa - (x + xa) = 0"
  by (import hollight ADD_SUBR)

lemma SUB_ADD: "ALL (x::nat) xa::nat. <= xa x --> x - xa + xa = x"
  by (import hollight SUB_ADD)

lemma SUC_SUB1: "ALL x::nat. Suc x - NUMERAL_BIT1 0 = x"
  by (import hollight SUC_SUB1)

constdefs
  FACT :: "nat => nat" 
  "FACT ==
SOME FACT::nat => nat.
   FACT 0 = NUMERAL_BIT1 0 & (ALL n::nat. FACT (Suc n) = Suc n * FACT n)"

lemma DEF_FACT: "FACT =
(SOME FACT::nat => nat.
    FACT 0 = NUMERAL_BIT1 0 & (ALL n::nat. FACT (Suc n) = Suc n * FACT n))"
  by (import hollight DEF_FACT)

lemma FACT_LT: "ALL n::nat. < 0 (FACT n)"
  by (import hollight FACT_LT)

lemma FACT_LE: "ALL x::nat. <= (NUMERAL_BIT1 0) (FACT x)"
  by (import hollight FACT_LE)

lemma FACT_MONO: "ALL (m::nat) n::nat. <= m n --> <= (FACT m) (FACT n)"
  by (import hollight FACT_MONO)

lemma DIVMOD_EXIST: "ALL (m::nat) n::nat. n ~= 0 --> (EX (q::nat) r::nat. m = q * n + r & < r n)"
  by (import hollight DIVMOD_EXIST)

lemma DIVMOD_EXIST_0: "ALL (m::nat) n::nat.
   EX (x::nat) xa::nat.
      COND (n = 0) (x = 0 & xa = 0) (m = x * n + xa & < xa n)"
  by (import hollight DIVMOD_EXIST_0)

constdefs
  DIV :: "nat => nat => nat" 
  "DIV ==
SOME q::nat => nat => nat.
   EX r::nat => nat => nat.
      ALL (m::nat) n::nat.
         COND (n = 0) (q m n = 0 & r m n = 0)
          (m = q m n * n + r m n & < (r m n) n)"

lemma DEF_DIV: "DIV =
(SOME q::nat => nat => nat.
    EX r::nat => nat => nat.
       ALL (m::nat) n::nat.
          COND (n = 0) (q m n = 0 & r m n = 0)
           (m = q m n * n + r m n & < (r m n) n))"
  by (import hollight DEF_DIV)

constdefs
  MOD :: "nat => nat => nat" 
  "MOD ==
SOME r::nat => nat => nat.
   ALL (m::nat) n::nat.
      COND (n = 0) (DIV m n = 0 & r m n = 0)
       (m = DIV m n * n + r m n & < (r m n) n)"

lemma DEF_MOD: "MOD =
(SOME r::nat => nat => nat.
    ALL (m::nat) n::nat.
       COND (n = 0) (DIV m n = 0 & r m n = 0)
        (m = DIV m n * n + r m n & < (r m n) n))"
  by (import hollight DEF_MOD)

lemma DIVISION: "ALL (m::nat) n::nat. n ~= 0 --> m = DIV m n * n + MOD m n & < (MOD m n) n"
  by (import hollight DIVISION)

lemma DIVMOD_UNIQ_LEMMA: "ALL (m::nat) (n::nat) (q1::nat) (r1::nat) (q2::nat) r2::nat.
   (m = q1 * n + r1 & < r1 n) & m = q2 * n + r2 & < r2 n -->
   q1 = q2 & r1 = r2"
  by (import hollight DIVMOD_UNIQ_LEMMA)

lemma DIVMOD_UNIQ: "ALL (m::nat) (n::nat) (q::nat) r::nat.
   m = q * n + r & < r n --> DIV m n = q & MOD m n = r"
  by (import hollight DIVMOD_UNIQ)

lemma MOD_UNIQ: "ALL (m::nat) (n::nat) (q::nat) r::nat. m = q * n + r & < r n --> MOD m n = r"
  by (import hollight MOD_UNIQ)

lemma DIV_UNIQ: "ALL (m::nat) (n::nat) (q::nat) r::nat. m = q * n + r & < r n --> DIV m n = q"
  by (import hollight DIV_UNIQ)

lemma MOD_MULT: "ALL (x::nat) xa::nat. x ~= 0 --> MOD (x * xa) x = 0"
  by (import hollight MOD_MULT)

lemma DIV_MULT: "ALL (x::nat) xa::nat. x ~= 0 --> DIV (x * xa) x = xa"
  by (import hollight DIV_MULT)

lemma DIV_DIV: "ALL (m::nat) (n::nat) p::nat. n * p ~= 0 --> DIV (DIV m n) p = DIV m (n * p)"
  by (import hollight DIV_DIV)

lemma MOD_LT: "ALL (m::nat) n::nat. < m n --> MOD m n = m"
  by (import hollight MOD_LT)

lemma MOD_EQ: "ALL (m::nat) (n::nat) (p::nat) q::nat. m = n + q * p --> MOD m p = MOD n p"
  by (import hollight MOD_EQ)

lemma DIV_MOD: "ALL (m::nat) (n::nat) p::nat.
   n * p ~= 0 --> MOD (DIV m n) p = DIV (MOD m (n * p)) n"
  by (import hollight DIV_MOD)

lemma DIV_1: "ALL n::nat. DIV n (NUMERAL_BIT1 0) = n"
  by (import hollight DIV_1)

lemma EXP_LT_0: "ALL (x::nat) xa::nat. < 0 (EXP xa x) = (xa ~= 0 | x = 0)"
  by (import hollight EXP_LT_0)

lemma DIV_LE: "ALL (m::nat) n::nat. n ~= 0 --> <= (DIV m n) m"
  by (import hollight DIV_LE)

lemma DIV_MUL_LE: "ALL (m::nat) n::nat. <= (n * DIV m n) m"
  by (import hollight DIV_MUL_LE)

lemma DIV_0: "ALL n::nat. n ~= 0 --> DIV 0 n = 0"
  by (import hollight DIV_0)

lemma MOD_0: "ALL n::nat. n ~= 0 --> MOD 0 n = 0"
  by (import hollight MOD_0)

lemma DIV_LT: "ALL (m::nat) n::nat. < m n --> DIV m n = 0"
  by (import hollight DIV_LT)

lemma MOD_MOD: "ALL (m::nat) (n::nat) p::nat. n * p ~= 0 --> MOD (MOD m (n * p)) n = MOD m n"
  by (import hollight MOD_MOD)

lemma MOD_MOD_REFL: "ALL (m::nat) n::nat. n ~= 0 --> MOD (MOD m n) n = MOD m n"
  by (import hollight MOD_MOD_REFL)

lemma DIV_MULT2: "ALL (x::nat) (xa::nat) xb::nat.
   x * xb ~= 0 --> DIV (x * xa) (x * xb) = DIV xa xb"
  by (import hollight DIV_MULT2)

lemma MOD_MULT2: "ALL (x::nat) (xa::nat) xb::nat.
   x * xb ~= 0 --> MOD (x * xa) (x * xb) = x * MOD xa xb"
  by (import hollight MOD_MULT2)

lemma MOD_1: "ALL n::nat. MOD n (NUMERAL_BIT1 0) = 0"
  by (import hollight MOD_1)

lemma MOD_EXISTS: "ALL (m::nat) n::nat.
   (EX q::nat. m = n * q) = COND (n = 0) (m = 0) (MOD m n = 0)"
  by (import hollight MOD_EXISTS)

lemma LT_EXP: "ALL (x::nat) (m::nat) n::nat.
   < (EXP x m) (EXP x n) =
   (<= (NUMERAL_BIT0 (NUMERAL_BIT1 0)) x & < m n | x = 0 & m ~= 0 & n = 0)"
  by (import hollight LT_EXP)

lemma LE_EXP: "ALL (x::nat) (m::nat) n::nat.
   <= (EXP x m) (EXP x n) =
   COND (x = 0) (m = 0 --> n = 0) (x = NUMERAL_BIT1 0 | <= m n)"
  by (import hollight LE_EXP)

lemma DIV_MONO: "ALL (m::nat) (n::nat) p::nat. p ~= 0 & <= m n --> <= (DIV m p) (DIV n p)"
  by (import hollight DIV_MONO)

lemma DIV_MONO_LT: "ALL (m::nat) (n::nat) p::nat.
   p ~= 0 & <= (m + p) n --> < (DIV m p) (DIV n p)"
  by (import hollight DIV_MONO_LT)

lemma LE_LDIV: "ALL (a::nat) (b::nat) n::nat. a ~= 0 & <= b (a * n) --> <= (DIV b a) n"
  by (import hollight LE_LDIV)

lemma LE_RDIV_EQ: "ALL (a::nat) (b::nat) n::nat. a ~= 0 --> <= n (DIV b a) = <= (a * n) b"
  by (import hollight LE_RDIV_EQ)

lemma LE_LDIV_EQ: "ALL (a::nat) (b::nat) n::nat.
   a ~= 0 --> <= (DIV b a) n = < b (a * (n + NUMERAL_BIT1 0))"
  by (import hollight LE_LDIV_EQ)

lemma DIV_EQ_0: "ALL (m::nat) n::nat. n ~= 0 --> (DIV m n = 0) = < m n"
  by (import hollight DIV_EQ_0)

lemma MOD_EQ_0: "ALL (m::nat) n::nat. n ~= 0 --> (MOD m n = 0) = (EX q::nat. m = q * n)"
  by (import hollight MOD_EQ_0)

lemma EVEN_MOD: "ALL n::nat. EVEN n = (MOD n (NUMERAL_BIT0 (NUMERAL_BIT1 0)) = 0)"
  by (import hollight EVEN_MOD)

lemma ODD_MOD: "ALL n::nat. ODD n = (MOD n (NUMERAL_BIT0 (NUMERAL_BIT1 0)) = NUMERAL_BIT1 0)"
  by (import hollight ODD_MOD)

lemma MOD_MULT_RMOD: "ALL (m::nat) (n::nat) p::nat. n ~= 0 --> MOD (m * MOD p n) n = MOD (m * p) n"
  by (import hollight MOD_MULT_RMOD)

lemma MOD_MULT_LMOD: "ALL (x::nat) (xa::nat) xb::nat.
   xa ~= 0 --> MOD (MOD x xa * xb) xa = MOD (x * xb) xa"
  by (import hollight MOD_MULT_LMOD)

lemma MOD_MULT_MOD2: "ALL (x::nat) (xa::nat) xb::nat.
   xa ~= 0 --> MOD (MOD x xa * MOD xb xa) xa = MOD (x * xb) xa"
  by (import hollight MOD_MULT_MOD2)

lemma MOD_EXP_MOD: "ALL (m::nat) (n::nat) p::nat.
   n ~= 0 --> MOD (EXP (MOD m n) p) n = MOD (EXP m p) n"
  by (import hollight MOD_EXP_MOD)

lemma MOD_MULT_ADD: "ALL (m::nat) (n::nat) p::nat. MOD (m * n + p) n = MOD p n"
  by (import hollight MOD_MULT_ADD)

lemma MOD_ADD_MOD: "ALL (a::nat) (b::nat) n::nat.
   n ~= 0 --> MOD (MOD a n + MOD b n) n = MOD (a + b) n"
  by (import hollight MOD_ADD_MOD)

lemma DIV_ADD_MOD: "ALL (a::nat) (b::nat) n::nat.
   n ~= 0 -->
   (MOD (a + b) n = MOD a n + MOD b n) = (DIV (a + b) n = DIV a n + DIV b n)"
  by (import hollight DIV_ADD_MOD)

lemma DIV_REFL: "ALL n::nat. n ~= 0 --> DIV n n = NUMERAL_BIT1 0"
  by (import hollight DIV_REFL)

lemma MOD_LE: "ALL (m::nat) n::nat. n ~= 0 --> <= (MOD m n) m"
  by (import hollight MOD_LE)

lemma DIV_MONO2: "ALL (m::nat) (n::nat) p::nat. p ~= 0 & <= p m --> <= (DIV n m) (DIV n p)"
  by (import hollight DIV_MONO2)

lemma DIV_LE_EXCLUSION: "ALL (a::nat) (b::nat) (c::nat) d::nat.
   b ~= 0 & < (b * c) ((a + NUMERAL_BIT1 0) * d) --> <= (DIV c d) (DIV a b)"
  by (import hollight DIV_LE_EXCLUSION)

lemma DIV_EQ_EXCLUSION: "< ((b::nat) * (c::nat)) (((a::nat) + NUMERAL_BIT1 0) * (d::nat)) &
< (a * d) ((c + NUMERAL_BIT1 0) * b) -->
DIV a b = DIV c d"
  by (import hollight DIV_EQ_EXCLUSION)

lemma SUB_ELIM_THM: "(P::nat => bool) ((a::nat) - (b::nat)) =
(ALL x::nat. (b = a + x --> P 0) & (a = b + x --> P x))"
  by (import hollight SUB_ELIM_THM)

lemma PRE_ELIM_THM: "(P::nat => bool) (Pred (n::nat)) =
(ALL m::nat. (n = 0 --> P 0) & (n = Suc m --> P m))"
  by (import hollight PRE_ELIM_THM)

lemma DIVMOD_ELIM_THM: "(P::nat => nat => bool) (DIV (m::nat) (n::nat)) (MOD m n) =
(n = 0 & P 0 0 |
 n ~= 0 & (ALL (q::nat) r::nat. m = q * n + r & < r n --> P q r))"
  by (import hollight DIVMOD_ELIM_THM)

constdefs
  eqeq :: "'q_9910 => 'q_9909 => ('q_9910 => 'q_9909 => bool) => bool" 
  "eqeq ==
%(u::'q_9910::type) (ua::'q_9909::type)
   ub::'q_9910::type => 'q_9909::type => bool. ub u ua"

lemma DEF__equal__equal_: "eqeq =
(%(u::'q_9910::type) (ua::'q_9909::type)
    ub::'q_9910::type => 'q_9909::type => bool. ub u ua)"
  by (import hollight DEF__equal__equal_)

constdefs
  mod_nat :: "nat => nat => nat => bool" 
  "mod_nat ==
%(u::nat) (ua::nat) ub::nat. EX (q1::nat) q2::nat. ua + u * q1 = ub + u * q2"

lemma DEF_mod_nat: "mod_nat =
(%(u::nat) (ua::nat) ub::nat.
    EX (q1::nat) q2::nat. ua + u * q1 = ub + u * q2)"
  by (import hollight DEF_mod_nat)

constdefs
  minimal :: "(nat => bool) => nat" 
  "minimal == %u::nat => bool. SOME n::nat. u n & (ALL m::nat. < m n --> ~ u m)"

lemma DEF_minimal: "minimal =
(%u::nat => bool. SOME n::nat. u n & (ALL m::nat. < m n --> ~ u m))"
  by (import hollight DEF_minimal)

lemma MINIMAL: "ALL P::nat => bool.
   Ex P = (P (minimal P) & (ALL x::nat. < x (minimal P) --> ~ P x))"
  by (import hollight MINIMAL)

constdefs
  WF :: "('A => 'A => bool) => bool" 
  "WF ==
%u::'A::type => 'A::type => bool.
   ALL P::'A::type => bool.
      Ex P --> (EX x::'A::type. P x & (ALL y::'A::type. u y x --> ~ P y))"

lemma DEF_WF: "WF =
(%u::'A::type => 'A::type => bool.
    ALL P::'A::type => bool.
       Ex P --> (EX x::'A::type. P x & (ALL y::'A::type. u y x --> ~ P y)))"
  by (import hollight DEF_WF)

lemma WF_EQ: "WF (u_354::'A::type => 'A::type => bool) =
(ALL P::'A::type => bool.
    Ex P = (EX x::'A::type. P x & (ALL y::'A::type. u_354 y x --> ~ P y)))"
  by (import hollight WF_EQ)

lemma WF_IND: "WF (u_354::'A::type => 'A::type => bool) =
(ALL P::'A::type => bool.
    (ALL x::'A::type. (ALL y::'A::type. u_354 y x --> P y) --> P x) -->
    All P)"
  by (import hollight WF_IND)

lemma WF_DCHAIN: "WF (u_354::'A::type => 'A::type => bool) =
(~ (EX s::nat => 'A::type. ALL n::nat. u_354 (s (Suc n)) (s n)))"
  by (import hollight WF_DCHAIN)

lemma WF_UREC: "WF (u_354::'A::type => 'A::type => bool) -->
(ALL H::('A::type => 'B::type) => 'A::type => 'B::type.
    (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
        (ALL z::'A::type. u_354 z x --> f z = g z) --> H f x = H g x) -->
    (ALL (f::'A::type => 'B::type) g::'A::type => 'B::type.
        (ALL x::'A::type. f x = H f x) & (ALL x::'A::type. g x = H g x) -->
        f = g))"
  by (import hollight WF_UREC)

lemma WF_UREC_WF: "(ALL H::('A::type => bool) => 'A::type => bool.
    (ALL (f::'A::type => bool) (g::'A::type => bool) x::'A::type.
        (ALL z::'A::type.
            (u_354::'A::type => 'A::type => bool) z x --> f z = g z) -->
        H f x = H g x) -->
    (ALL (f::'A::type => bool) g::'A::type => bool.
        (ALL x::'A::type. f x = H f x) & (ALL x::'A::type. g x = H g x) -->
        f = g)) -->
WF u_354"
  by (import hollight WF_UREC_WF)

lemma WF_REC_INVARIANT: "WF (u_354::'A::type => 'A::type => bool) -->
(ALL (H::('A::type => 'B::type) => 'A::type => 'B::type)
    S::'A::type => 'B::type => bool.
    (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
        (ALL z::'A::type. u_354 z x --> f z = g z & S z (f z)) -->
        H f x = H g x & S x (H f x)) -->
    (EX f::'A::type => 'B::type. ALL x::'A::type. f x = H f x))"
  by (import hollight WF_REC_INVARIANT)

lemma WF_REC: "WF (u_354::'A::type => 'A::type => bool) -->
(ALL H::('A::type => 'B::type) => 'A::type => 'B::type.
    (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
        (ALL z::'A::type. u_354 z x --> f z = g z) --> H f x = H g x) -->
    (EX f::'A::type => 'B::type. ALL x::'A::type. f x = H f x))"
  by (import hollight WF_REC)

lemma WF_REC_WF: "(ALL H::('A::type => nat) => 'A::type => nat.
    (ALL (f::'A::type => nat) (g::'A::type => nat) x::'A::type.
        (ALL z::'A::type.
            (u_354::'A::type => 'A::type => bool) z x --> f z = g z) -->
        H f x = H g x) -->
    (EX f::'A::type => nat. ALL x::'A::type. f x = H f x)) -->
WF u_354"
  by (import hollight WF_REC_WF)

lemma WF_EREC: "WF (u_354::'A::type => 'A::type => bool) -->
(ALL H::('A::type => 'B::type) => 'A::type => 'B::type.
    (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
        (ALL z::'A::type. u_354 z x --> f z = g z) --> H f x = H g x) -->
    (EX! f::'A::type => 'B::type. ALL x::'A::type. f x = H f x))"
  by (import hollight WF_EREC)

lemma WF_SUBSET: "(ALL (x::'A::type) y::'A::type.
    (u_354::'A::type => 'A::type => bool) x y -->
    (u_473::'A::type => 'A::type => bool) x y) &
WF u_473 -->
WF u_354"
  by (import hollight WF_SUBSET)

lemma WF_MEASURE_GEN: "ALL m::'A::type => 'B::type.
   WF (u_354::'B::type => 'B::type => bool) -->
   WF (%(x::'A::type) x'::'A::type. u_354 (m x) (m x'))"
  by (import hollight WF_MEASURE_GEN)

lemma WF_LEX_DEPENDENT: "ALL (R::'A::type => 'A::type => bool)
   S::'A::type => 'B::type => 'B::type => bool.
   WF R & (ALL x::'A::type. WF (S x)) -->
   WF (GABS
        (%f::'A::type * 'B::type => 'A::type * 'B::type => bool.
            ALL (r1::'A::type) s1::'B::type.
               GEQ (f (r1, s1))
                (GABS
                  (%f::'A::type * 'B::type => bool.
                      ALL (r2::'A::type) s2::'B::type.
                         GEQ (f (r2, s2))
                          (R r1 r2 | r1 = r2 & S r1 s1 s2)))))"
  by (import hollight WF_LEX_DEPENDENT)

lemma WF_LEX: "ALL (x::'A::type => 'A::type => bool) xa::'B::type => 'B::type => bool.
   WF x & WF xa -->
   WF (GABS
        (%f::'A::type * 'B::type => 'A::type * 'B::type => bool.
            ALL (r1::'A::type) s1::'B::type.
               GEQ (f (r1, s1))
                (GABS
                  (%f::'A::type * 'B::type => bool.
                      ALL (r2::'A::type) s2::'B::type.
                         GEQ (f (r2, s2)) (x r1 r2 | r1 = r2 & xa s1 s2)))))"
  by (import hollight WF_LEX)

lemma WF_POINTWISE: "WF (u_354::'A::type => 'A::type => bool) &
WF (u_473::'B::type => 'B::type => bool) -->
WF (GABS
     (%f::'A::type * 'B::type => 'A::type * 'B::type => bool.
         ALL (x1::'A::type) y1::'B::type.
            GEQ (f (x1, y1))
             (GABS
               (%f::'A::type * 'B::type => bool.
                   ALL (x2::'A::type) y2::'B::type.
                      GEQ (f (x2, y2)) (u_354 x1 x2 & u_473 y1 y2)))))"
  by (import hollight WF_POINTWISE)

lemma WF_num: "WF <"
  by (import hollight WF_num)

lemma WF_REC_num: "ALL H::(nat => 'A::type) => nat => 'A::type.
   (ALL (f::nat => 'A::type) (g::nat => 'A::type) x::nat.
       (ALL z::nat. < z x --> f z = g z) --> H f x = H g x) -->
   (EX f::nat => 'A::type. ALL x::nat. f x = H f x)"
  by (import hollight WF_REC_num)

consts
  measure :: "('q_11107 => nat) => 'q_11107 => 'q_11107 => bool" 

defs
  measure_def: "hollight.measure ==
%(u::'q_11107::type => nat) (x::'q_11107::type) y::'q_11107::type.
   < (u x) (u y)"

lemma DEF_measure: "hollight.measure =
(%(u::'q_11107::type => nat) (x::'q_11107::type) y::'q_11107::type.
    < (u x) (u y))"
  by (import hollight DEF_measure)

lemma WF_MEASURE: "ALL m::'A::type => nat. WF (hollight.measure m)"
  by (import hollight WF_MEASURE)

lemma MEASURE_LE: "(ALL x::'q_11137::type.
    hollight.measure (m::'q_11137::type => nat) x (a::'q_11137::type) -->
    hollight.measure m x (b::'q_11137::type)) =
<= (m a) (m b)"
  by (import hollight MEASURE_LE)

lemma WF_REFL: "ALL x::'A::type. WF (u_354::'A::type => 'A::type => bool) --> ~ u_354 x x"
  by (import hollight WF_REFL)

lemma WF_FALSE: "WF (%(x::'A::type) y::'A::type. False)"
  by (import hollight WF_FALSE)

lemma WF_REC_TAIL: "ALL (P::'A::type => bool) (g::'A::type => 'A::type) h::'A::type => 'B::type.
   EX f::'A::type => 'B::type.
      ALL x::'A::type. f x = COND (P x) (f (g x)) (h x)"
  by (import hollight WF_REC_TAIL)

lemma WF_REC_TAIL_GENERAL: "ALL (P::('A::type => 'B::type) => 'A::type => bool)
   (G::('A::type => 'B::type) => 'A::type => 'A::type)
   H::('A::type => 'B::type) => 'A::type => 'B::type.
   WF (u_354::'A::type => 'A::type => bool) &
   (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
       (ALL z::'A::type. u_354 z x --> f z = g z) -->
       P f x = P g x & G f x = G g x & H f x = H g x) &
   (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
       (ALL z::'A::type. u_354 z x --> f z = g z) --> H f x = H g x) &
   (ALL (f::'A::type => 'B::type) (x::'A::type) y::'A::type.
       P f x & u_354 y (G f x) --> u_354 y x) -->
   (EX f::'A::type => 'B::type.
       ALL x::'A::type. f x = COND (P f x) (f (G f x)) (H f x))"
  by (import hollight WF_REC_TAIL_GENERAL)

lemma ARITH_ZERO: "(op &::bool => bool => bool) ((op =::nat => nat => bool) (0::nat) (0::nat))
 ((op =::nat => nat => bool) ((NUMERAL_BIT0::nat => nat) (0::nat)) (0::nat))"
  by (import hollight ARITH_ZERO)

lemma ARITH_SUC: "(ALL x::nat. Suc x = Suc x) &
Suc 0 = NUMERAL_BIT1 0 &
(ALL x::nat. Suc (NUMERAL_BIT0 x) = NUMERAL_BIT1 x) &
(ALL x::nat. Suc (NUMERAL_BIT1 x) = NUMERAL_BIT0 (Suc x))"
  by (import hollight ARITH_SUC)

lemma ARITH_PRE: "(ALL x::nat. Pred x = Pred x) &
Pred 0 = 0 &
(ALL x::nat.
    Pred (NUMERAL_BIT0 x) = COND (x = 0) 0 (NUMERAL_BIT1 (Pred x))) &
(ALL x::nat. Pred (NUMERAL_BIT1 x) = NUMERAL_BIT0 x)"
  by (import hollight ARITH_PRE)

lemma ARITH_ADD: "(op &::bool => bool => bool)
 ((All::(nat => bool) => bool)
   (%x::nat.
       (All::(nat => bool) => bool)
        (%xa::nat.
            (op =::nat => nat => bool) ((op +::nat => nat => nat) x xa)
             ((op +::nat => nat => nat) x xa))))
 ((op &::bool => bool => bool)
   ((op =::nat => nat => bool) ((op +::nat => nat => nat) (0::nat) (0::nat))
     (0::nat))
   ((op &::bool => bool => bool)
     ((All::(nat => bool) => bool)
       (%x::nat.
           (op =::nat => nat => bool)
            ((op +::nat => nat => nat) (0::nat)
              ((NUMERAL_BIT0::nat => nat) x))
            ((NUMERAL_BIT0::nat => nat) x)))
     ((op &::bool => bool => bool)
       ((All::(nat => bool) => bool)
         (%x::nat.
             (op =::nat => nat => bool)
              ((op +::nat => nat => nat) (0::nat)
                ((NUMERAL_BIT1::nat => nat) x))
              ((NUMERAL_BIT1::nat => nat) x)))
       ((op &::bool => bool => bool)
         ((All::(nat => bool) => bool)
           (%x::nat.
               (op =::nat => nat => bool)
                ((op +::nat => nat => nat) ((NUMERAL_BIT0::nat => nat) x)
                  (0::nat))
                ((NUMERAL_BIT0::nat => nat) x)))
         ((op &::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%x::nat.
                 (op =::nat => nat => bool)
                  ((op +::nat => nat => nat) ((NUMERAL_BIT1::nat => nat) x)
                    (0::nat))
                  ((NUMERAL_BIT1::nat => nat) x)))
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%x::nat.
                   (All::(nat => bool) => bool)
                    (%xa::nat.
                        (op =::nat => nat => bool)
                         ((op +::nat => nat => nat)
                           ((NUMERAL_BIT0::nat => nat) x)
                           ((NUMERAL_BIT0::nat => nat) xa))
                         ((NUMERAL_BIT0::nat => nat)
                           ((op +::nat => nat => nat) x xa)))))
             ((op &::bool => bool => bool)
               ((All::(nat => bool) => bool)
                 (%x::nat.
                     (All::(nat => bool) => bool)
                      (%xa::nat.
                          (op =::nat => nat => bool)
                           ((op +::nat => nat => nat)
                             ((NUMERAL_BIT0::nat => nat) x)
                             ((NUMERAL_BIT1::nat => nat) xa))
                           ((NUMERAL_BIT1::nat => nat)
                             ((op +::nat => nat => nat) x xa)))))
               ((op &::bool => bool => bool)
                 ((All::(nat => bool) => bool)
                   (%x::nat.
                       (All::(nat => bool) => bool)
                        (%xa::nat.
                            (op =::nat => nat => bool)
                             ((op +::nat => nat => nat)
                               ((NUMERAL_BIT1::nat => nat) x)
                               ((NUMERAL_BIT0::nat => nat) xa))
                             ((NUMERAL_BIT1::nat => nat)
                               ((op +::nat => nat => nat) x xa)))))
                 ((All::(nat => bool) => bool)
                   (%x::nat.
                       (All::(nat => bool) => bool)
                        (%xa::nat.
                            (op =::nat => nat => bool)
                             ((op +::nat => nat => nat)
                               ((NUMERAL_BIT1::nat => nat) x)
                               ((NUMERAL_BIT1::nat => nat) xa))
                             ((NUMERAL_BIT0::nat => nat)
                               ((Suc::nat => nat)
                                 ((op +::nat => nat => nat) x
                                   xa))))))))))))))"
  by (import hollight ARITH_ADD)

lemma ARITH_MULT: "(op &::bool => bool => bool)
 ((All::(nat => bool) => bool)
   (%x::nat.
       (All::(nat => bool) => bool)
        (%xa::nat.
            (op =::nat => nat => bool) ((op *::nat => nat => nat) x xa)
             ((op *::nat => nat => nat) x xa))))
 ((op &::bool => bool => bool)
   ((op =::nat => nat => bool) ((op *::nat => nat => nat) (0::nat) (0::nat))
     (0::nat))
   ((op &::bool => bool => bool)
     ((All::(nat => bool) => bool)
       (%x::nat.
           (op =::nat => nat => bool)
            ((op *::nat => nat => nat) (0::nat)
              ((NUMERAL_BIT0::nat => nat) x))
            (0::nat)))
     ((op &::bool => bool => bool)
       ((All::(nat => bool) => bool)
         (%x::nat.
             (op =::nat => nat => bool)
              ((op *::nat => nat => nat) (0::nat)
                ((NUMERAL_BIT1::nat => nat) x))
              (0::nat)))
       ((op &::bool => bool => bool)
         ((All::(nat => bool) => bool)
           (%x::nat.
               (op =::nat => nat => bool)
                ((op *::nat => nat => nat) ((NUMERAL_BIT0::nat => nat) x)
                  (0::nat))
                (0::nat)))
         ((op &::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%x::nat.
                 (op =::nat => nat => bool)
                  ((op *::nat => nat => nat) ((NUMERAL_BIT1::nat => nat) x)
                    (0::nat))
                  (0::nat)))
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%x::nat.
                   (All::(nat => bool) => bool)
                    (%xa::nat.
                        (op =::nat => nat => bool)
                         ((op *::nat => nat => nat)
                           ((NUMERAL_BIT0::nat => nat) x)
                           ((NUMERAL_BIT0::nat => nat) xa))
                         ((NUMERAL_BIT0::nat => nat)
                           ((NUMERAL_BIT0::nat => nat)
                             ((op *::nat => nat => nat) x xa))))))
             ((op &::bool => bool => bool)
               ((All::(nat => bool) => bool)
                 (%x::nat.
                     (All::(nat => bool) => bool)
                      (%xa::nat.
                          (op =::nat => nat => bool)
                           ((op *::nat => nat => nat)
                             ((NUMERAL_BIT0::nat => nat) x)
                             ((NUMERAL_BIT1::nat => nat) xa))
                           ((op +::nat => nat => nat)
                             ((NUMERAL_BIT0::nat => nat) x)
                             ((NUMERAL_BIT0::nat => nat)
                               ((NUMERAL_BIT0::nat => nat)
                                 ((op *::nat => nat => nat) x xa)))))))
               ((op &::bool => bool => bool)
                 ((All::(nat => bool) => bool)
                   (%x::nat.
                       (All::(nat => bool) => bool)
                        (%xa::nat.
                            (op =::nat => nat => bool)
                             ((op *::nat => nat => nat)
                               ((NUMERAL_BIT1::nat => nat) x)
                               ((NUMERAL_BIT0::nat => nat) xa))
                             ((op +::nat => nat => nat)
                               ((NUMERAL_BIT0::nat => nat) xa)
                               ((NUMERAL_BIT0::nat => nat)
                                 ((NUMERAL_BIT0::nat => nat)
                                   ((op *::nat => nat => nat) x xa)))))))
                 ((All::(nat => bool) => bool)
                   (%x::nat.
                       (All::(nat => bool) => bool)
                        (%xa::nat.
                            (op =::nat => nat => bool)
                             ((op *::nat => nat => nat)
                               ((NUMERAL_BIT1::nat => nat) x)
                               ((NUMERAL_BIT1::nat => nat) xa))
                             ((op +::nat => nat => nat)
                               ((NUMERAL_BIT1::nat => nat) x)
                               ((op +::nat => nat => nat)
                                 ((NUMERAL_BIT0::nat => nat) xa)
                                 ((NUMERAL_BIT0::nat => nat)
                                   ((NUMERAL_BIT0::nat => nat)
                                     ((op *::nat => nat => nat) x
 xa))))))))))))))))"
  by (import hollight ARITH_MULT)

lemma ARITH_EXP: "(ALL (x::nat) xa::nat. EXP x xa = EXP x xa) &
EXP 0 0 = NUMERAL_BIT1 0 &
(ALL m::nat. EXP (NUMERAL_BIT0 m) 0 = NUMERAL_BIT1 0) &
(ALL m::nat. EXP (NUMERAL_BIT1 m) 0 = NUMERAL_BIT1 0) &
(ALL n::nat. EXP 0 (NUMERAL_BIT0 n) = EXP 0 n * EXP 0 n) &
(ALL (m::nat) n::nat.
    EXP (NUMERAL_BIT0 m) (NUMERAL_BIT0 n) =
    EXP (NUMERAL_BIT0 m) n * EXP (NUMERAL_BIT0 m) n) &
(ALL (m::nat) n::nat.
    EXP (NUMERAL_BIT1 m) (NUMERAL_BIT0 n) =
    EXP (NUMERAL_BIT1 m) n * EXP (NUMERAL_BIT1 m) n) &
(ALL n::nat. EXP 0 (NUMERAL_BIT1 n) = 0) &
(ALL (m::nat) n::nat.
    EXP (NUMERAL_BIT0 m) (NUMERAL_BIT1 n) =
    NUMERAL_BIT0 m * (EXP (NUMERAL_BIT0 m) n * EXP (NUMERAL_BIT0 m) n)) &
(ALL (m::nat) n::nat.
    EXP (NUMERAL_BIT1 m) (NUMERAL_BIT1 n) =
    NUMERAL_BIT1 m * (EXP (NUMERAL_BIT1 m) n * EXP (NUMERAL_BIT1 m) n))"
  by (import hollight ARITH_EXP)

lemma ARITH_EVEN: "(ALL x::nat. EVEN x = EVEN x) &
EVEN 0 = True &
(ALL x::nat. EVEN (NUMERAL_BIT0 x) = True) &
(ALL x::nat. EVEN (NUMERAL_BIT1 x) = False)"
  by (import hollight ARITH_EVEN)

lemma ARITH_ODD: "(ALL x::nat. ODD x = ODD x) &
ODD 0 = False &
(ALL x::nat. ODD (NUMERAL_BIT0 x) = False) &
(ALL x::nat. ODD (NUMERAL_BIT1 x) = True)"
  by (import hollight ARITH_ODD)

lemma ARITH_LE: "(ALL (x::nat) xa::nat. <= x xa = <= x xa) &
<= 0 0 = True &
(ALL x::nat. <= (NUMERAL_BIT0 x) 0 = (x = 0)) &
(ALL x::nat. <= (NUMERAL_BIT1 x) 0 = False) &
(ALL x::nat. <= 0 (NUMERAL_BIT0 x) = True) &
(ALL x::nat. <= 0 (NUMERAL_BIT1 x) = True) &
(ALL (x::nat) xa::nat. <= (NUMERAL_BIT0 x) (NUMERAL_BIT0 xa) = <= x xa) &
(ALL (x::nat) xa::nat. <= (NUMERAL_BIT0 x) (NUMERAL_BIT1 xa) = <= x xa) &
(ALL (x::nat) xa::nat. <= (NUMERAL_BIT1 x) (NUMERAL_BIT0 xa) = < x xa) &
(ALL (x::nat) xa::nat. <= (NUMERAL_BIT1 x) (NUMERAL_BIT1 xa) = <= x xa)"
  by (import hollight ARITH_LE)

lemma ARITH_LT: "(ALL (x::nat) xa::nat. < x xa = < x xa) &
< 0 0 = False &
(ALL x::nat. < (NUMERAL_BIT0 x) 0 = False) &
(ALL x::nat. < (NUMERAL_BIT1 x) 0 = False) &
(ALL x::nat. < 0 (NUMERAL_BIT0 x) = < 0 x) &
(ALL x::nat. < 0 (NUMERAL_BIT1 x) = True) &
(ALL (x::nat) xa::nat. < (NUMERAL_BIT0 x) (NUMERAL_BIT0 xa) = < x xa) &
(ALL (x::nat) xa::nat. < (NUMERAL_BIT0 x) (NUMERAL_BIT1 xa) = <= x xa) &
(ALL (x::nat) xa::nat. < (NUMERAL_BIT1 x) (NUMERAL_BIT0 xa) = < x xa) &
(ALL (x::nat) xa::nat. < (NUMERAL_BIT1 x) (NUMERAL_BIT1 xa) = < x xa)"
  by (import hollight ARITH_LT)

lemma ARITH_EQ: "(op &::bool => bool => bool)
 ((All::(nat => bool) => bool)
   (%x::nat.
       (All::(nat => bool) => bool)
        (%xa::nat.
            (op =::bool => bool => bool) ((op =::nat => nat => bool) x xa)
             ((op =::nat => nat => bool) x xa))))
 ((op &::bool => bool => bool)
   ((op =::bool => bool => bool)
     ((op =::nat => nat => bool) (0::nat) (0::nat)) (True::bool))
   ((op &::bool => bool => bool)
     ((All::(nat => bool) => bool)
       (%x::nat.
           (op =::bool => bool => bool)
            ((op =::nat => nat => bool) ((NUMERAL_BIT0::nat => nat) x)
              (0::nat))
            ((op =::nat => nat => bool) x (0::nat))))
     ((op &::bool => bool => bool)
       ((All::(nat => bool) => bool)
         (%x::nat.
             (op =::bool => bool => bool)
              ((op =::nat => nat => bool) ((NUMERAL_BIT1::nat => nat) x)
                (0::nat))
              (False::bool)))
       ((op &::bool => bool => bool)
         ((All::(nat => bool) => bool)
           (%x::nat.
               (op =::bool => bool => bool)
                ((op =::nat => nat => bool) (0::nat)
                  ((NUMERAL_BIT0::nat => nat) x))
                ((op =::nat => nat => bool) (0::nat) x)))
         ((op &::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%x::nat.
                 (op =::bool => bool => bool)
                  ((op =::nat => nat => bool) (0::nat)
                    ((NUMERAL_BIT1::nat => nat) x))
                  (False::bool)))
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%x::nat.
                   (All::(nat => bool) => bool)
                    (%xa::nat.
                        (op =::bool => bool => bool)
                         ((op =::nat => nat => bool)
                           ((NUMERAL_BIT0::nat => nat) x)
                           ((NUMERAL_BIT0::nat => nat) xa))
                         ((op =::nat => nat => bool) x xa))))
             ((op &::bool => bool => bool)
               ((All::(nat => bool) => bool)
                 (%x::nat.
                     (All::(nat => bool) => bool)
                      (%xa::nat.
                          (op =::bool => bool => bool)
                           ((op =::nat => nat => bool)
                             ((NUMERAL_BIT0::nat => nat) x)
                             ((NUMERAL_BIT1::nat => nat) xa))
                           (False::bool))))
               ((op &::bool => bool => bool)
                 ((All::(nat => bool) => bool)
                   (%x::nat.
                       (All::(nat => bool) => bool)
                        (%xa::nat.
                            (op =::bool => bool => bool)
                             ((op =::nat => nat => bool)
                               ((NUMERAL_BIT1::nat => nat) x)
                               ((NUMERAL_BIT0::nat => nat) xa))
                             (False::bool))))
                 ((All::(nat => bool) => bool)
                   (%x::nat.
                       (All::(nat => bool) => bool)
                        (%xa::nat.
                            (op =::bool => bool => bool)
                             ((op =::nat => nat => bool)
                               ((NUMERAL_BIT1::nat => nat) x)
                               ((NUMERAL_BIT1::nat => nat) xa))
                             ((op =::nat => nat => bool) x xa))))))))))))"
  by (import hollight ARITH_EQ)

lemma ARITH_SUB: "(op &::bool => bool => bool)
 ((All::(nat => bool) => bool)
   (%x::nat.
       (All::(nat => bool) => bool)
        (%xa::nat.
            (op =::nat => nat => bool) ((op -::nat => nat => nat) x xa)
             ((op -::nat => nat => nat) x xa))))
 ((op &::bool => bool => bool)
   ((op =::nat => nat => bool) ((op -::nat => nat => nat) (0::nat) (0::nat))
     (0::nat))
   ((op &::bool => bool => bool)
     ((All::(nat => bool) => bool)
       (%x::nat.
           (op =::nat => nat => bool)
            ((op -::nat => nat => nat) (0::nat)
              ((NUMERAL_BIT0::nat => nat) x))
            (0::nat)))
     ((op &::bool => bool => bool)
       ((All::(nat => bool) => bool)
         (%x::nat.
             (op =::nat => nat => bool)
              ((op -::nat => nat => nat) (0::nat)
                ((NUMERAL_BIT1::nat => nat) x))
              (0::nat)))
       ((op &::bool => bool => bool)
         ((All::(nat => bool) => bool)
           (%x::nat.
               (op =::nat => nat => bool)
                ((op -::nat => nat => nat) ((NUMERAL_BIT0::nat => nat) x)
                  (0::nat))
                ((NUMERAL_BIT0::nat => nat) x)))
         ((op &::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%x::nat.
                 (op =::nat => nat => bool)
                  ((op -::nat => nat => nat) ((NUMERAL_BIT1::nat => nat) x)
                    (0::nat))
                  ((NUMERAL_BIT1::nat => nat) x)))
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%m::nat.
                   (All::(nat => bool) => bool)
                    (%n::nat.
                        (op =::nat => nat => bool)
                         ((op -::nat => nat => nat)
                           ((NUMERAL_BIT0::nat => nat) m)
                           ((NUMERAL_BIT0::nat => nat) n))
                         ((NUMERAL_BIT0::nat => nat)
                           ((op -::nat => nat => nat) m n)))))
             ((op &::bool => bool => bool)
               ((All::(nat => bool) => bool)
                 (%m::nat.
                     (All::(nat => bool) => bool)
                      (%n::nat.
                          (op =::nat => nat => bool)
                           ((op -::nat => nat => nat)
                             ((NUMERAL_BIT0::nat => nat) m)
                             ((NUMERAL_BIT1::nat => nat) n))
                           ((Pred::nat => nat)
                             ((NUMERAL_BIT0::nat => nat)
                               ((op -::nat => nat => nat) m n))))))
               ((op &::bool => bool => bool)
                 ((All::(nat => bool) => bool)
                   (%m::nat.
                       (All::(nat => bool) => bool)
                        (%n::nat.
                            (op =::nat => nat => bool)
                             ((op -::nat => nat => nat)
                               ((NUMERAL_BIT1::nat => nat) m)
                               ((NUMERAL_BIT0::nat => nat) n))
                             ((COND::bool => nat => nat => nat)
                               ((<=::nat => nat => bool) n m)
                               ((NUMERAL_BIT1::nat => nat)
                                 ((op -::nat => nat => nat) m n))
                               (0::nat)))))
                 ((All::(nat => bool) => bool)
                   (%m::nat.
                       (All::(nat => bool) => bool)
                        (%n::nat.
                            (op =::nat => nat => bool)
                             ((op -::nat => nat => nat)
                               ((NUMERAL_BIT1::nat => nat) m)
                               ((NUMERAL_BIT1::nat => nat) n))
                             ((NUMERAL_BIT0::nat => nat)
                               ((op -::nat => nat => nat) m n)))))))))))))"
  by (import hollight ARITH_SUB)

lemma right_th: "(s::nat) * NUMERAL_BIT1 (x::nat) = s + NUMERAL_BIT0 (s * x)"
  by (import hollight right_th)

lemma SEMIRING_PTHS: "(ALL (x::'A::type) (y::'A::type) z::'A::type.
    (add::'A::type => 'A::type => 'A::type) x (add y z) = add (add x y) z) &
(ALL (x::'A::type) y::'A::type. add x y = add y x) &
(ALL x::'A::type. add (r0::'A::type) x = x) &
(ALL (x::'A::type) (y::'A::type) z::'A::type.
    (mul::'A::type => 'A::type => 'A::type) x (mul y z) = mul (mul x y) z) &
(ALL (x::'A::type) y::'A::type. mul x y = mul y x) &
(ALL x::'A::type. mul (r1::'A::type) x = x) &
(ALL x::'A::type. mul r0 x = r0) &
(ALL (x::'A::type) (y::'A::type) z::'A::type.
    mul x (add y z) = add (mul x y) (mul x z)) &
(ALL x::'A::type. (pwr::'A::type => nat => 'A::type) x 0 = r1) &
(ALL (x::'A::type) n::nat. pwr x (Suc n) = mul x (pwr x n)) -->
mul r1 (x::'A::type) = x &
add (mul (a::'A::type) (m::'A::type)) (mul (b::'A::type) m) =
mul (add a b) m &
add (mul a m) m = mul (add a r1) m &
add m (mul a m) = mul (add a r1) m &
add m m = mul (add r1 r1) m &
mul r0 m = r0 &
add r0 a = a &
add a r0 = a &
mul a b = mul b a &
mul (add a b) (c::'A::type) = add (mul a c) (mul b c) &
mul r0 a = r0 &
mul a r0 = r0 &
mul r1 a = a &
mul a r1 = a &
mul (mul (lx::'A::type) (ly::'A::type))
 (mul (rx::'A::type) (ry::'A::type)) =
mul (mul lx rx) (mul ly ry) &
mul (mul lx ly) (mul rx ry) = mul lx (mul ly (mul rx ry)) &
mul (mul lx ly) (mul rx ry) = mul rx (mul (mul lx ly) ry) &
mul (mul lx ly) rx = mul (mul lx rx) ly &
mul (mul lx ly) rx = mul lx (mul ly rx) &
mul lx rx = mul rx lx &
mul lx (mul rx ry) = mul (mul lx rx) ry &
mul lx (mul rx ry) = mul rx (mul lx ry) &
add (add a b) (add c (d::'A::type)) = add (add a c) (add b d) &
add (add a b) c = add a (add b c) &
add a (add c d) = add c (add a d) &
add (add a b) c = add (add a c) b &
add a c = add c a &
add a (add c d) = add (add a c) d &
mul (pwr x (p::nat)) (pwr x (q::nat)) = pwr x (p + q) &
mul x (pwr x q) = pwr x (Suc q) &
mul (pwr x q) x = pwr x (Suc q) &
mul x x = pwr x (NUMERAL_BIT0 (NUMERAL_BIT1 0)) &
pwr (mul x (y::'A::type)) q = mul (pwr x q) (pwr y q) &
pwr (pwr x p) q = pwr x (p * q) &
pwr x 0 = r1 &
pwr x (NUMERAL_BIT1 0) = x &
mul x (add y (z::'A::type)) = add (mul x y) (mul x z) &
pwr x (Suc q) = mul x (pwr x q)"
  by (import hollight SEMIRING_PTHS)

lemma sth: "(ALL (x::nat) (y::nat) z::nat. x + (y + z) = x + y + z) &
(ALL (x::nat) y::nat. x + y = y + x) &
(ALL x::nat. 0 + x = x) &
(ALL (x::nat) (y::nat) z::nat. x * (y * z) = x * y * z) &
(ALL (x::nat) y::nat. x * y = y * x) &
(ALL x::nat. NUMERAL_BIT1 0 * x = x) &
(ALL x::nat. 0 * x = 0) &
(ALL (x::nat) (xa::nat) xb::nat. x * (xa + xb) = x * xa + x * xb) &
(ALL x::nat. EXP x 0 = NUMERAL_BIT1 0) &
(ALL (x::nat) xa::nat. EXP x (Suc xa) = x * EXP x xa)"
  by (import hollight sth)

lemma NUM_INTEGRAL_LEMMA: "(w::nat) = (x::nat) + (d::nat) & (y::nat) = (z::nat) + (e::nat) -->
(w * y + x * z = w * z + x * y) = (w = x | y = z)"
  by (import hollight NUM_INTEGRAL_LEMMA)

lemma NUM_INTEGRAL: "(ALL x::nat. 0 * x = 0) &
(ALL (x::nat) (xa::nat) xb::nat. (x + xa = x + xb) = (xa = xb)) &
(ALL (w::nat) (x::nat) (y::nat) z::nat.
    (w * y + x * z = w * z + x * y) = (w = x | y = z))"
  by (import hollight NUM_INTEGRAL)

lemma INJ_INVERSE2: "ALL P::'A::type => 'B::type => 'C::type.
   (ALL (x1::'A::type) (y1::'B::type) (x2::'A::type) y2::'B::type.
       (P x1 y1 = P x2 y2) = (x1 = x2 & y1 = y2)) -->
   (EX (x::'C::type => 'A::type) Y::'C::type => 'B::type.
       ALL (xa::'A::type) y::'B::type. x (P xa y) = xa & Y (P xa y) = y)"
  by (import hollight INJ_INVERSE2)

constdefs
  NUMPAIR :: "nat => nat => nat" 
  "NUMPAIR ==
%(u::nat) ua::nat.
   EXP (NUMERAL_BIT0 (NUMERAL_BIT1 0)) u *
   (NUMERAL_BIT0 (NUMERAL_BIT1 0) * ua + NUMERAL_BIT1 0)"

lemma DEF_NUMPAIR: "NUMPAIR =
(%(u::nat) ua::nat.
    EXP (NUMERAL_BIT0 (NUMERAL_BIT1 0)) u *
    (NUMERAL_BIT0 (NUMERAL_BIT1 0) * ua + NUMERAL_BIT1 0))"
  by (import hollight DEF_NUMPAIR)

lemma NUMPAIR_INJ_LEMMA: "ALL (x::nat) (xa::nat) (xb::nat) xc::nat.
   NUMPAIR x xa = NUMPAIR xb xc --> x = xb"
  by (import hollight NUMPAIR_INJ_LEMMA)

lemma NUMPAIR_INJ: "ALL (x1::nat) (y1::nat) (x2::nat) y2::nat.
   (NUMPAIR x1 y1 = NUMPAIR x2 y2) = (x1 = x2 & y1 = y2)"
  by (import hollight NUMPAIR_INJ)

constdefs
  NUMFST :: "nat => nat" 
  "NUMFST ==
SOME X::nat => nat.
   EX Y::nat => nat.
      ALL (x::nat) y::nat. X (NUMPAIR x y) = x & Y (NUMPAIR x y) = y"

lemma DEF_NUMFST: "NUMFST =
(SOME X::nat => nat.
    EX Y::nat => nat.
       ALL (x::nat) y::nat. X (NUMPAIR x y) = x & Y (NUMPAIR x y) = y)"
  by (import hollight DEF_NUMFST)

constdefs
  NUMSND :: "nat => nat" 
  "NUMSND ==
SOME Y::nat => nat.
   ALL (x::nat) y::nat. NUMFST (NUMPAIR x y) = x & Y (NUMPAIR x y) = y"

lemma DEF_NUMSND: "NUMSND =
(SOME Y::nat => nat.
    ALL (x::nat) y::nat. NUMFST (NUMPAIR x y) = x & Y (NUMPAIR x y) = y)"
  by (import hollight DEF_NUMSND)

constdefs
  NUMSUM :: "bool => nat => nat" 
  "NUMSUM ==
%(u::bool) ua::nat.
   COND u (Suc (NUMERAL_BIT0 (NUMERAL_BIT1 0) * ua))
    (NUMERAL_BIT0 (NUMERAL_BIT1 0) * ua)"

lemma DEF_NUMSUM: "NUMSUM =
(%(u::bool) ua::nat.
    COND u (Suc (NUMERAL_BIT0 (NUMERAL_BIT1 0) * ua))
     (NUMERAL_BIT0 (NUMERAL_BIT1 0) * ua))"
  by (import hollight DEF_NUMSUM)

lemma NUMSUM_INJ: "ALL (b1::bool) (x1::nat) (b2::bool) x2::nat.
   (NUMSUM b1 x1 = NUMSUM b2 x2) = (b1 = b2 & x1 = x2)"
  by (import hollight NUMSUM_INJ)

constdefs
  NUMLEFT :: "nat => bool" 
  "NUMLEFT ==
SOME X::nat => bool.
   EX Y::nat => nat.
      ALL (x::bool) y::nat. X (NUMSUM x y) = x & Y (NUMSUM x y) = y"

lemma DEF_NUMLEFT: "NUMLEFT =
(SOME X::nat => bool.
    EX Y::nat => nat.
       ALL (x::bool) y::nat. X (NUMSUM x y) = x & Y (NUMSUM x y) = y)"
  by (import hollight DEF_NUMLEFT)

constdefs
  NUMRIGHT :: "nat => nat" 
  "NUMRIGHT ==
SOME Y::nat => nat.
   ALL (x::bool) y::nat. NUMLEFT (NUMSUM x y) = x & Y (NUMSUM x y) = y"

lemma DEF_NUMRIGHT: "NUMRIGHT =
(SOME Y::nat => nat.
    ALL (x::bool) y::nat. NUMLEFT (NUMSUM x y) = x & Y (NUMSUM x y) = y)"
  by (import hollight DEF_NUMRIGHT)

constdefs
  INJN :: "nat => nat => 'A => bool" 
  "INJN == %(u::nat) (n::nat) a::'A::type. n = u"

lemma DEF_INJN: "INJN = (%(u::nat) (n::nat) a::'A::type. n = u)"
  by (import hollight DEF_INJN)

lemma INJN_INJ: "(All::(nat => bool) => bool)
 (%n1::nat.
     (All::(nat => bool) => bool)
      (%n2::nat.
          (op =::bool => bool => bool)
           ((op =::(nat => 'A::type => bool)
                   => (nat => 'A::type => bool) => bool)
             ((INJN::nat => nat => 'A::type => bool) n1)
             ((INJN::nat => nat => 'A::type => bool) n2))
           ((op =::nat => nat => bool) n1 n2)))"
  by (import hollight INJN_INJ)

constdefs
  INJA :: "'A => nat => 'A => bool" 
  "INJA == %(u::'A::type) (n::nat) b::'A::type. b = u"

lemma DEF_INJA: "INJA = (%(u::'A::type) (n::nat) b::'A::type. b = u)"
  by (import hollight DEF_INJA)

lemma INJA_INJ: "ALL (a1::'A::type) a2::'A::type. (INJA a1 = INJA a2) = (a1 = a2)"
  by (import hollight INJA_INJ)

constdefs
  INJF :: "(nat => nat => 'A => bool) => nat => 'A => bool" 
  "INJF == %(u::nat => nat => 'A::type => bool) n::nat. u (NUMFST n) (NUMSND n)"

lemma DEF_INJF: "INJF =
(%(u::nat => nat => 'A::type => bool) n::nat. u (NUMFST n) (NUMSND n))"
  by (import hollight DEF_INJF)

lemma INJF_INJ: "ALL (f1::nat => nat => 'A::type => bool) f2::nat => nat => 'A::type => bool.
   (INJF f1 = INJF f2) = (f1 = f2)"
  by (import hollight INJF_INJ)

constdefs
  INJP :: "(nat => 'A => bool) => (nat => 'A => bool) => nat => 'A => bool" 
  "INJP ==
%(u::nat => 'A::type => bool) (ua::nat => 'A::type => bool) (n::nat)
   a::'A::type. COND (NUMLEFT n) (u (NUMRIGHT n) a) (ua (NUMRIGHT n) a)"

lemma DEF_INJP: "INJP =
(%(u::nat => 'A::type => bool) (ua::nat => 'A::type => bool) (n::nat)
    a::'A::type. COND (NUMLEFT n) (u (NUMRIGHT n) a) (ua (NUMRIGHT n) a))"
  by (import hollight DEF_INJP)

lemma INJP_INJ: "ALL (f1::nat => 'A::type => bool) (f1'::nat => 'A::type => bool)
   (f2::nat => 'A::type => bool) f2'::nat => 'A::type => bool.
   (INJP f1 f2 = INJP f1' f2') = (f1 = f1' & f2 = f2')"
  by (import hollight INJP_INJ)

constdefs
  ZCONSTR :: "nat => 'A => (nat => nat => 'A => bool) => nat => 'A => bool" 
  "ZCONSTR ==
%(u::nat) (ua::'A::type) ub::nat => nat => 'A::type => bool.
   INJP (INJN (Suc u)) (INJP (INJA ua) (INJF ub))"

lemma DEF_ZCONSTR: "ZCONSTR =
(%(u::nat) (ua::'A::type) ub::nat => nat => 'A::type => bool.
    INJP (INJN (Suc u)) (INJP (INJA ua) (INJF ub)))"
  by (import hollight DEF_ZCONSTR)

constdefs
  ZBOT :: "nat => 'A => bool" 
  "ZBOT == INJP (INJN 0) (SOME z::nat => 'A::type => bool. True)"

lemma DEF_ZBOT: "ZBOT = INJP (INJN 0) (SOME z::nat => 'A::type => bool. True)"
  by (import hollight DEF_ZBOT)

lemma ZCONSTR_ZBOT: "ALL (x::nat) (xa::'A::type) xb::nat => nat => 'A::type => bool.
   ZCONSTR x xa xb ~= ZBOT"
  by (import hollight ZCONSTR_ZBOT)

constdefs
  ZRECSPACE :: "(nat => 'A => bool) => bool" 
  "ZRECSPACE ==
%a::nat => 'A::type => bool.
   ALL ZRECSPACE'::(nat => 'A::type => bool) => bool.
      (ALL a::nat => 'A::type => bool.
          a = ZBOT |
          (EX (c::nat) (i::'A::type) r::nat => nat => 'A::type => bool.
              a = ZCONSTR c i r & (ALL n::nat. ZRECSPACE' (r n))) -->
          ZRECSPACE' a) -->
      ZRECSPACE' a"

lemma DEF_ZRECSPACE: "ZRECSPACE =
(%a::nat => 'A::type => bool.
    ALL ZRECSPACE'::(nat => 'A::type => bool) => bool.
       (ALL a::nat => 'A::type => bool.
           a = ZBOT |
           (EX (c::nat) (i::'A::type) r::nat => nat => 'A::type => bool.
               a = ZCONSTR c i r & (ALL n::nat. ZRECSPACE' (r n))) -->
           ZRECSPACE' a) -->
       ZRECSPACE' a)"
  by (import hollight DEF_ZRECSPACE)

typedef (open) ('A) recspace = "(Collect::((nat => 'A::type => bool) => bool)
          => (nat => 'A::type => bool) set)
 (ZRECSPACE::(nat => 'A::type => bool) => bool)"  morphisms "_dest_rec" "_mk_rec"
  apply (rule light_ex_imp_nonempty[where t="ZBOT::nat => 'A::type => bool"])
  by (import hollight TYDEF_recspace)

syntax
  "_dest_rec" :: _ ("'_dest'_rec")

syntax
  "_mk_rec" :: _ ("'_mk'_rec")

lemmas "TYDEF_recspace_@intern" = typedef_hol2hollight 
  [where a="a :: 'A recspace" and r=r ,
   OF type_definition_recspace]

constdefs
  BOTTOM :: "'A recspace" 
  "(op ==::'A::type recspace => 'A::type recspace => prop)
 (BOTTOM::'A::type recspace)
 ((_mk_rec::(nat => 'A::type => bool) => 'A::type recspace)
   (ZBOT::nat => 'A::type => bool))"

lemma DEF_BOTTOM: "(op =::'A::type recspace => 'A::type recspace => bool)
 (BOTTOM::'A::type recspace)
 ((_mk_rec::(nat => 'A::type => bool) => 'A::type recspace)
   (ZBOT::nat => 'A::type => bool))"
  by (import hollight DEF_BOTTOM)

constdefs
  CONSTR :: "nat => 'A => (nat => 'A recspace) => 'A recspace" 
  "(op ==::(nat => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
        => (nat
            => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
           => prop)
 (CONSTR::nat
          => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
 (%(u::nat) (ua::'A::type) ub::nat => 'A::type recspace.
     (_mk_rec::(nat => 'A::type => bool) => 'A::type recspace)
      ((ZCONSTR::nat
                 => 'A::type
                    => (nat => nat => 'A::type => bool)
                       => nat => 'A::type => bool)
        u ua
        (%n::nat.
            (_dest_rec::'A::type recspace => nat => 'A::type => bool)
             (ub n))))"

lemma DEF_CONSTR: "(op =::(nat => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
       => (nat
           => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
          => bool)
 (CONSTR::nat
          => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
 (%(u::nat) (ua::'A::type) ub::nat => 'A::type recspace.
     (_mk_rec::(nat => 'A::type => bool) => 'A::type recspace)
      ((ZCONSTR::nat
                 => 'A::type
                    => (nat => nat => 'A::type => bool)
                       => nat => 'A::type => bool)
        u ua
        (%n::nat.
            (_dest_rec::'A::type recspace => nat => 'A::type => bool)
             (ub n))))"
  by (import hollight DEF_CONSTR)

lemma MK_REC_INJ: "(All::((nat => 'A::type => bool) => bool) => bool)
 (%x::nat => 'A::type => bool.
     (All::((nat => 'A::type => bool) => bool) => bool)
      (%y::nat => 'A::type => bool.
          (op -->::bool => bool => bool)
           ((op =::'A::type recspace => 'A::type recspace => bool)
             ((_mk_rec::(nat => 'A::type => bool) => 'A::type recspace) x)
             ((_mk_rec::(nat => 'A::type => bool) => 'A::type recspace) y))
           ((op -->::bool => bool => bool)
             ((op &::bool => bool => bool)
               ((ZRECSPACE::(nat => 'A::type => bool) => bool) x)
               ((ZRECSPACE::(nat => 'A::type => bool) => bool) y))
             ((op =::(nat => 'A::type => bool)
                     => (nat => 'A::type => bool) => bool)
               x y))))"
  by (import hollight MK_REC_INJ)

lemma CONSTR_BOT: "ALL (c::nat) (i::'A::type) r::nat => 'A::type recspace.
   CONSTR c i r ~= BOTTOM"
  by (import hollight CONSTR_BOT)

lemma CONSTR_INJ: "ALL (c1::nat) (i1::'A::type) (r1::nat => 'A::type recspace) (c2::nat)
   (i2::'A::type) r2::nat => 'A::type recspace.
   (CONSTR c1 i1 r1 = CONSTR c2 i2 r2) = (c1 = c2 & i1 = i2 & r1 = r2)"
  by (import hollight CONSTR_INJ)

lemma CONSTR_IND: "ALL P::'A::type recspace => bool.
   P BOTTOM &
   (ALL (c::nat) (i::'A::type) r::nat => 'A::type recspace.
       (ALL n::nat. P (r n)) --> P (CONSTR c i r)) -->
   All P"
  by (import hollight CONSTR_IND)

lemma CONSTR_REC: "ALL Fn::nat
        => 'A::type
           => (nat => 'A::type recspace) => (nat => 'B::type) => 'B::type.
   EX f::'A::type recspace => 'B::type.
      ALL (c::nat) (i::'A::type) r::nat => 'A::type recspace.
         f (CONSTR c i r) = Fn c i r (%n::nat. f (r n))"
  by (import hollight CONSTR_REC)

constdefs
  FCONS :: "'A => (nat => 'A) => nat => 'A" 
  "FCONS ==
SOME FCONS::'A::type => (nat => 'A::type) => nat => 'A::type.
   (ALL (a::'A::type) f::nat => 'A::type. FCONS a f 0 = a) &
   (ALL (a::'A::type) (f::nat => 'A::type) n::nat. FCONS a f (Suc n) = f n)"

lemma DEF_FCONS: "FCONS =
(SOME FCONS::'A::type => (nat => 'A::type) => nat => 'A::type.
    (ALL (a::'A::type) f::nat => 'A::type. FCONS a f 0 = a) &
    (ALL (a::'A::type) (f::nat => 'A::type) n::nat.
        FCONS a f (Suc n) = f n))"
  by (import hollight DEF_FCONS)

lemma FCONS_UNDO: "ALL f::nat => 'A::type. f = FCONS (f 0) (f o Suc)"
  by (import hollight FCONS_UNDO)

constdefs
  FNIL :: "nat => 'A" 
  "FNIL == %u::nat. SOME x::'A::type. True"

lemma DEF_FNIL: "FNIL = (%u::nat. SOME x::'A::type. True)"
  by (import hollight DEF_FNIL)

typedef (open) ('A, 'B) sum = "(Collect::(('A::type * 'B::type) recspace => bool)
          => ('A::type * 'B::type) recspace set)
 (%a::('A::type * 'B::type) recspace.
     (All::((('A::type * 'B::type) recspace => bool) => bool) => bool)
      (%sum'::('A::type * 'B::type) recspace => bool.
          (op -->::bool => bool => bool)
           ((All::(('A::type * 'B::type) recspace => bool) => bool)
             (%a::('A::type * 'B::type) recspace.
                 (op -->::bool => bool => bool)
                  ((op |::bool => bool => bool)
                    ((Ex::('A::type => bool) => bool)
                      (%aa::'A::type.
                          (op =::('A::type * 'B::type) recspace
                                 => ('A::type * 'B::type) recspace => bool)
                           a ((CONSTR::nat
 => 'A::type * 'B::type
    => (nat => ('A::type * 'B::type) recspace)
       => ('A::type * 'B::type) recspace)
                               ((NUMERAL::nat => nat) (0::nat))
                               ((Pair::'A::type
 => 'B::type => 'A::type * 'B::type)
                                 aa ((Eps::('B::type => bool) => 'B::type)
(%v::'B::type. True::bool)))
                               (%n::nat.
                                   BOTTOM::('A::type *
      'B::type) recspace))))
                    ((Ex::('B::type => bool) => bool)
                      (%aa::'B::type.
                          (op =::('A::type * 'B::type) recspace
                                 => ('A::type * 'B::type) recspace => bool)
                           a ((CONSTR::nat
 => 'A::type * 'B::type
    => (nat => ('A::type * 'B::type) recspace)
       => ('A::type * 'B::type) recspace)
                               ((Suc::nat => nat)
                                 ((NUMERAL::nat => nat) (0::nat)))
                               ((Pair::'A::type
 => 'B::type => 'A::type * 'B::type)
                                 ((Eps::('A::type => bool) => 'A::type)
                                   (%v::'A::type. True::bool))
                                 aa)
                               (%n::nat.
                                   BOTTOM::('A::type *
      'B::type) recspace)))))
                  (sum' a)))
           (sum' a)))"  morphisms "_dest_sum" "_mk_sum"
  apply (rule light_ex_imp_nonempty[where t="(CONSTR::nat
         => 'A::type * 'B::type
            => (nat => ('A::type * 'B::type) recspace)
               => ('A::type * 'B::type) recspace)
 ((NUMERAL::nat => nat) (0::nat))
 ((Pair::'A::type => 'B::type => 'A::type * 'B::type) (a::'A::type)
   ((Eps::('B::type => bool) => 'B::type) (%v::'B::type. True::bool)))
 (%n::nat. BOTTOM::('A::type * 'B::type) recspace)"])
  by (import hollight TYDEF_sum)

syntax
  "_dest_sum" :: _ ("'_dest'_sum")

syntax
  "_mk_sum" :: _ ("'_mk'_sum")

lemmas "TYDEF_sum_@intern" = typedef_hol2hollight 
  [where a="a :: ('A, 'B) sum" and r=r ,
   OF type_definition_sum]

constdefs
  INL :: "'A => ('A, 'B) sum" 
  "(op ==::('A::type => ('A::type, 'B::type) sum)
        => ('A::type => ('A::type, 'B::type) sum) => prop)
 (INL::'A::type => ('A::type, 'B::type) sum)
 (%a::'A::type.
     (_mk_sum::('A::type * 'B::type) recspace => ('A::type, 'B::type) sum)
      ((CONSTR::nat
                => 'A::type * 'B::type
                   => (nat => ('A::type * 'B::type) recspace)
                      => ('A::type * 'B::type) recspace)
        (0::nat)
        ((Pair::'A::type => 'B::type => 'A::type * 'B::type) a
          ((Eps::('B::type => bool) => 'B::type)
            (%v::'B::type. True::bool)))
        (%n::nat. BOTTOM::('A::type * 'B::type) recspace)))"

lemma DEF_INL: "(op =::('A::type => ('A::type, 'B::type) sum)
       => ('A::type => ('A::type, 'B::type) sum) => bool)
 (INL::'A::type => ('A::type, 'B::type) sum)
 (%a::'A::type.
     (_mk_sum::('A::type * 'B::type) recspace => ('A::type, 'B::type) sum)
      ((CONSTR::nat
                => 'A::type * 'B::type
                   => (nat => ('A::type * 'B::type) recspace)
                      => ('A::type * 'B::type) recspace)
        (0::nat)
        ((Pair::'A::type => 'B::type => 'A::type * 'B::type) a
          ((Eps::('B::type => bool) => 'B::type)
            (%v::'B::type. True::bool)))
        (%n::nat. BOTTOM::('A::type * 'B::type) recspace)))"
  by (import hollight DEF_INL)

constdefs
  INR :: "'B => ('A, 'B) sum" 
  "(op ==::('B::type => ('A::type, 'B::type) sum)
        => ('B::type => ('A::type, 'B::type) sum) => prop)
 (INR::'B::type => ('A::type, 'B::type) sum)
 (%a::'B::type.
     (_mk_sum::('A::type * 'B::type) recspace => ('A::type, 'B::type) sum)
      ((CONSTR::nat
                => 'A::type * 'B::type
                   => (nat => ('A::type * 'B::type) recspace)
                      => ('A::type * 'B::type) recspace)
        ((Suc::nat => nat) (0::nat))
        ((Pair::'A::type => 'B::type => 'A::type * 'B::type)
          ((Eps::('A::type => bool) => 'A::type) (%v::'A::type. True::bool))
          a)
        (%n::nat. BOTTOM::('A::type * 'B::type) recspace)))"

lemma DEF_INR: "(op =::('B::type => ('A::type, 'B::type) sum)
       => ('B::type => ('A::type, 'B::type) sum) => bool)
 (INR::'B::type => ('A::type, 'B::type) sum)
 (%a::'B::type.
     (_mk_sum::('A::type * 'B::type) recspace => ('A::type, 'B::type) sum)
      ((CONSTR::nat
                => 'A::type * 'B::type
                   => (nat => ('A::type * 'B::type) recspace)
                      => ('A::type * 'B::type) recspace)
        ((Suc::nat => nat) (0::nat))
        ((Pair::'A::type => 'B::type => 'A::type * 'B::type)
          ((Eps::('A::type => bool) => 'A::type) (%v::'A::type. True::bool))
          a)
        (%n::nat. BOTTOM::('A::type * 'B::type) recspace)))"
  by (import hollight DEF_INR)

consts
  OUTL :: "('A, 'B) sum => 'A" 

defs
  OUTL_def: "hollight.OUTL ==
SOME OUTL::('A::type, 'B::type) sum => 'A::type.
   ALL x::'A::type. OUTL (INL x) = x"

lemma DEF_OUTL: "hollight.OUTL =
(SOME OUTL::('A::type, 'B::type) sum => 'A::type.
    ALL x::'A::type. OUTL (INL x) = x)"
  by (import hollight DEF_OUTL)

consts
  OUTR :: "('A, 'B) sum => 'B" 

defs
  OUTR_def: "hollight.OUTR ==
SOME OUTR::('A::type, 'B::type) sum => 'B::type.
   ALL y::'B::type. OUTR (INR y) = y"

lemma DEF_OUTR: "hollight.OUTR =
(SOME OUTR::('A::type, 'B::type) sum => 'B::type.
    ALL y::'B::type. OUTR (INR y) = y)"
  by (import hollight DEF_OUTR)

typedef (open) ('A) option = "(Collect::('A::type recspace => bool) => 'A::type recspace set)
 (%a::'A::type recspace.
     (All::(('A::type recspace => bool) => bool) => bool)
      (%option'::'A::type recspace => bool.
          (op -->::bool => bool => bool)
           ((All::('A::type recspace => bool) => bool)
             (%a::'A::type recspace.
                 (op -->::bool => bool => bool)
                  ((op |::bool => bool => bool)
                    ((op =::'A::type recspace => 'A::type recspace => bool)
                      a ((CONSTR::nat
                                  => 'A::type
                                     => (nat => 'A::type recspace)
  => 'A::type recspace)
                          ((NUMERAL::nat => nat) (0::nat))
                          ((Eps::('A::type => bool) => 'A::type)
                            (%v::'A::type. True::bool))
                          (%n::nat. BOTTOM::'A::type recspace)))
                    ((Ex::('A::type => bool) => bool)
                      (%aa::'A::type.
                          (op =::'A::type recspace
                                 => 'A::type recspace => bool)
                           a ((CONSTR::nat
 => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
                               ((Suc::nat => nat)
                                 ((NUMERAL::nat => nat) (0::nat)))
                               aa (%n::nat. BOTTOM::'A::type recspace)))))
                  (option' a)))
           (option' a)))"  morphisms "_dest_option" "_mk_option"
  apply (rule light_ex_imp_nonempty[where t="(CONSTR::nat => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
 ((NUMERAL::nat => nat) (0::nat))
 ((Eps::('A::type => bool) => 'A::type) (%v::'A::type. True::bool))
 (%n::nat. BOTTOM::'A::type recspace)"])
  by (import hollight TYDEF_option)

syntax
  "_dest_option" :: _ ("'_dest'_option")

syntax
  "_mk_option" :: _ ("'_mk'_option")

lemmas "TYDEF_option_@intern" = typedef_hol2hollight 
  [where a="a :: 'A hollight.option" and r=r ,
   OF type_definition_option]

constdefs
  NONE :: "'A hollight.option" 
  "(op ==::'A::type hollight.option => 'A::type hollight.option => prop)
 (NONE::'A::type hollight.option)
 ((_mk_option::'A::type recspace => 'A::type hollight.option)
   ((CONSTR::nat
             => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
     (0::nat)
     ((Eps::('A::type => bool) => 'A::type) (%v::'A::type. True::bool))
     (%n::nat. BOTTOM::'A::type recspace)))"

lemma DEF_NONE: "(op =::'A::type hollight.option => 'A::type hollight.option => bool)
 (NONE::'A::type hollight.option)
 ((_mk_option::'A::type recspace => 'A::type hollight.option)
   ((CONSTR::nat
             => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
     (0::nat)
     ((Eps::('A::type => bool) => 'A::type) (%v::'A::type. True::bool))
     (%n::nat. BOTTOM::'A::type recspace)))"
  by (import hollight DEF_NONE)

consts
  SOME :: "'A => 'A hollight.option" ("SOME")

defs
  SOME_def: "(op ==::('A::type => 'A::type hollight.option)
        => ('A::type => 'A::type hollight.option) => prop)
 (SOME::'A::type => 'A::type hollight.option)
 (%a::'A::type.
     (_mk_option::'A::type recspace => 'A::type hollight.option)
      ((CONSTR::nat
                => 'A::type
                   => (nat => 'A::type recspace) => 'A::type recspace)
        ((Suc::nat => nat) (0::nat)) a
        (%n::nat. BOTTOM::'A::type recspace)))"

lemma DEF_SOME: "(op =::('A::type => 'A::type hollight.option)
       => ('A::type => 'A::type hollight.option) => bool)
 (SOME::'A::type => 'A::type hollight.option)
 (%a::'A::type.
     (_mk_option::'A::type recspace => 'A::type hollight.option)
      ((CONSTR::nat
                => 'A::type
                   => (nat => 'A::type recspace) => 'A::type recspace)
        ((Suc::nat => nat) (0::nat)) a
        (%n::nat. BOTTOM::'A::type recspace)))"
  by (import hollight DEF_SOME)

typedef (open) ('A) list = "(Collect::('A::type recspace => bool) => 'A::type recspace set)
 (%a::'A::type recspace.
     (All::(('A::type recspace => bool) => bool) => bool)
      (%list'::'A::type recspace => bool.
          (op -->::bool => bool => bool)
           ((All::('A::type recspace => bool) => bool)
             (%a::'A::type recspace.
                 (op -->::bool => bool => bool)
                  ((op |::bool => bool => bool)
                    ((op =::'A::type recspace => 'A::type recspace => bool)
                      a ((CONSTR::nat
                                  => 'A::type
                                     => (nat => 'A::type recspace)
  => 'A::type recspace)
                          ((NUMERAL::nat => nat) (0::nat))
                          ((Eps::('A::type => bool) => 'A::type)
                            (%v::'A::type. True::bool))
                          (%n::nat. BOTTOM::'A::type recspace)))
                    ((Ex::('A::type => bool) => bool)
                      (%a0::'A::type.
                          (Ex::('A::type recspace => bool) => bool)
                           (%a1::'A::type recspace.
                               (op &::bool => bool => bool)
                                ((op =::'A::type recspace
  => 'A::type recspace => bool)
                                  a ((CONSTR::nat
        => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
((Suc::nat => nat) ((NUMERAL::nat => nat) (0::nat))) a0
((FCONS::'A::type recspace
         => (nat => 'A::type recspace) => nat => 'A::type recspace)
  a1 (%n::nat. BOTTOM::'A::type recspace))))
                                (list' a1)))))
                  (list' a)))
           (list' a)))"  morphisms "_dest_list" "_mk_list"
  apply (rule light_ex_imp_nonempty[where t="(CONSTR::nat => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
 ((NUMERAL::nat => nat) (0::nat))
 ((Eps::('A::type => bool) => 'A::type) (%v::'A::type. True::bool))
 (%n::nat. BOTTOM::'A::type recspace)"])
  by (import hollight TYDEF_list)

syntax
  "_dest_list" :: _ ("'_dest'_list")

syntax
  "_mk_list" :: _ ("'_mk'_list")

lemmas "TYDEF_list_@intern" = typedef_hol2hollight 
  [where a="a :: 'A hollight.list" and r=r ,
   OF type_definition_list]

constdefs
  NIL :: "'A hollight.list" 
  "(op ==::'A::type hollight.list => 'A::type hollight.list => prop)
 (NIL::'A::type hollight.list)
 ((_mk_list::'A::type recspace => 'A::type hollight.list)
   ((CONSTR::nat
             => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
     (0::nat)
     ((Eps::('A::type => bool) => 'A::type) (%v::'A::type. True::bool))
     (%n::nat. BOTTOM::'A::type recspace)))"

lemma DEF_NIL: "(op =::'A::type hollight.list => 'A::type hollight.list => bool)
 (NIL::'A::type hollight.list)
 ((_mk_list::'A::type recspace => 'A::type hollight.list)
   ((CONSTR::nat
             => 'A::type => (nat => 'A::type recspace) => 'A::type recspace)
     (0::nat)
     ((Eps::('A::type => bool) => 'A::type) (%v::'A::type. True::bool))
     (%n::nat. BOTTOM::'A::type recspace)))"
  by (import hollight DEF_NIL)

constdefs
  CONS :: "'A => 'A hollight.list => 'A hollight.list" 
  "(op ==::('A::type => 'A::type hollight.list => 'A::type hollight.list)
        => ('A::type => 'A::type hollight.list => 'A::type hollight.list)
           => prop)
 (CONS::'A::type => 'A::type hollight.list => 'A::type hollight.list)
 (%(a0::'A::type) a1::'A::type hollight.list.
     (_mk_list::'A::type recspace => 'A::type hollight.list)
      ((CONSTR::nat
                => 'A::type
                   => (nat => 'A::type recspace) => 'A::type recspace)
        ((Suc::nat => nat) (0::nat)) a0
        ((FCONS::'A::type recspace
                 => (nat => 'A::type recspace) => nat => 'A::type recspace)
          ((_dest_list::'A::type hollight.list => 'A::type recspace) a1)
          (%n::nat. BOTTOM::'A::type recspace))))"

lemma DEF_CONS: "(op =::('A::type => 'A::type hollight.list => 'A::type hollight.list)
       => ('A::type => 'A::type hollight.list => 'A::type hollight.list)
          => bool)
 (CONS::'A::type => 'A::type hollight.list => 'A::type hollight.list)
 (%(a0::'A::type) a1::'A::type hollight.list.
     (_mk_list::'A::type recspace => 'A::type hollight.list)
      ((CONSTR::nat
                => 'A::type
                   => (nat => 'A::type recspace) => 'A::type recspace)
        ((Suc::nat => nat) (0::nat)) a0
        ((FCONS::'A::type recspace
                 => (nat => 'A::type recspace) => nat => 'A::type recspace)
          ((_dest_list::'A::type hollight.list => 'A::type recspace) a1)
          (%n::nat. BOTTOM::'A::type recspace))))"
  by (import hollight DEF_CONS)

lemma pair_RECURSION: "ALL PAIR'::'A::type => 'B::type => 'C::type.
   EX x::'A::type * 'B::type => 'C::type.
      ALL (a0::'A::type) a1::'B::type. x (a0, a1) = PAIR' a0 a1"
  by (import hollight pair_RECURSION)

lemma num_RECURSION_STD: "ALL (e::'Z::type) f::nat => 'Z::type => 'Z::type.
   EX fn::nat => 'Z::type. fn 0 = e & (ALL n::nat. fn (Suc n) = f n (fn n))"
  by (import hollight num_RECURSION_STD)

constdefs
  ISO :: "('A => 'B) => ('B => 'A) => bool" 
  "ISO ==
%(u::'A::type => 'B::type) ua::'B::type => 'A::type.
   (ALL x::'B::type. u (ua x) = x) & (ALL y::'A::type. ua (u y) = y)"

lemma DEF_ISO: "ISO =
(%(u::'A::type => 'B::type) ua::'B::type => 'A::type.
    (ALL x::'B::type. u (ua x) = x) & (ALL y::'A::type. ua (u y) = y))"
  by (import hollight DEF_ISO)

lemma ISO_REFL: "ISO (%x::'A::type. x) (%x::'A::type. x)"
  by (import hollight ISO_REFL)

lemma ISO_FUN: "ISO (f::'A::type => 'A'::type) (f'::'A'::type => 'A::type) &
ISO (g::'B::type => 'B'::type) (g'::'B'::type => 'B::type) -->
ISO (%(h::'A::type => 'B::type) a'::'A'::type. g (h (f' a')))
 (%(h::'A'::type => 'B'::type) a::'A::type. g' (h (f a)))"
  by (import hollight ISO_FUN)

lemma ISO_USAGE: "ISO (f::'q_16585::type => 'q_16582::type)
 (g::'q_16582::type => 'q_16585::type) -->
(ALL P::'q_16585::type => bool. All P = (ALL x::'q_16582::type. P (g x))) &
(ALL P::'q_16585::type => bool. Ex P = (EX x::'q_16582::type. P (g x))) &
(ALL (a::'q_16585::type) b::'q_16582::type. (a = g b) = (f a = b))"
  by (import hollight ISO_USAGE)

typedef (open) N_2 = "{a::bool recspace.
 ALL u::bool recspace => bool.
    (ALL a::bool recspace.
        a = CONSTR (NUMERAL 0) (SOME x::bool. True) (%n::nat. BOTTOM) |
        a =
        CONSTR (Suc (NUMERAL 0)) (SOME x::bool. True) (%n::nat. BOTTOM) -->
        u a) -->
    u a}"  morphisms "_dest_2" "_mk_2"
  apply (rule light_ex_imp_nonempty[where t="CONSTR (NUMERAL 0) (SOME x::bool. True) (%n::nat. BOTTOM)"])
  by (import hollight TYDEF_2)

syntax
  "_dest_2" :: _ ("'_dest'_2")

syntax
  "_mk_2" :: _ ("'_mk'_2")

lemmas "TYDEF_2_@intern" = typedef_hol2hollight 
  [where a="a :: N_2" and r=r ,
   OF type_definition_N_2]

consts
  "_10288" :: "N_2" ("'_10288")

defs
  "_10288_def": "(op ==::N_2 => N_2 => prop) (_10288::N_2)
 ((_mk_2::bool recspace => N_2)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     (0::nat) ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"

lemma DEF__10288: "(op =::N_2 => N_2 => bool) (_10288::N_2)
 ((_mk_2::bool recspace => N_2)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     (0::nat) ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"
  by (import hollight DEF__10288)

consts
  "_10289" :: "N_2" ("'_10289")

defs
  "_10289_def": "(op ==::N_2 => N_2 => prop) (_10289::N_2)
 ((_mk_2::bool recspace => N_2)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) (0::nat))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"

lemma DEF__10289: "(op =::N_2 => N_2 => bool) (_10289::N_2)
 ((_mk_2::bool recspace => N_2)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) (0::nat))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"
  by (import hollight DEF__10289)

constdefs
  two_1 :: "N_2" 
  "two_1 == _10288"

lemma DEF_two_1: "two_1 = _10288"
  by (import hollight DEF_two_1)

constdefs
  two_2 :: "N_2" 
  "two_2 == _10289"

lemma DEF_two_2: "two_2 = _10289"
  by (import hollight DEF_two_2)

typedef (open) N_3 = "{a::bool recspace.
 ALL u::bool recspace => bool.
    (ALL a::bool recspace.
        a = CONSTR (NUMERAL 0) (SOME x::bool. True) (%n::nat. BOTTOM) |
        a =
        CONSTR (Suc (NUMERAL 0)) (SOME x::bool. True) (%n::nat. BOTTOM) |
        a =
        CONSTR (Suc (Suc (NUMERAL 0))) (SOME x::bool. True)
         (%n::nat. BOTTOM) -->
        u a) -->
    u a}"  morphisms "_dest_3" "_mk_3"
  apply (rule light_ex_imp_nonempty[where t="CONSTR (NUMERAL 0) (SOME x::bool. True) (%n::nat. BOTTOM)"])
  by (import hollight TYDEF_3)

syntax
  "_dest_3" :: _ ("'_dest'_3")

syntax
  "_mk_3" :: _ ("'_mk'_3")

lemmas "TYDEF_3_@intern" = typedef_hol2hollight 
  [where a="a :: N_3" and r=r ,
   OF type_definition_N_3]

consts
  "_10312" :: "N_3" ("'_10312")

defs
  "_10312_def": "(op ==::N_3 => N_3 => prop) (_10312::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     (0::nat) ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"

lemma DEF__10312: "(op =::N_3 => N_3 => bool) (_10312::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     (0::nat) ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"
  by (import hollight DEF__10312)

consts
  "_10313" :: "N_3" ("'_10313")

defs
  "_10313_def": "(op ==::N_3 => N_3 => prop) (_10313::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) (0::nat))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"

lemma DEF__10313: "(op =::N_3 => N_3 => bool) (_10313::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) (0::nat))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"
  by (import hollight DEF__10313)

consts
  "_10314" :: "N_3" ("'_10314")

defs
  "_10314_def": "(op ==::N_3 => N_3 => prop) (_10314::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) ((Suc::nat => nat) (0::nat)))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"

lemma DEF__10314: "(op =::N_3 => N_3 => bool) (_10314::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) ((Suc::nat => nat) (0::nat)))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"
  by (import hollight DEF__10314)

constdefs
  three_1 :: "N_3" 
  "three_1 == _10312"

lemma DEF_three_1: "three_1 = _10312"
  by (import hollight DEF_three_1)

constdefs
  three_2 :: "N_3" 
  "three_2 == _10313"

lemma DEF_three_2: "three_2 = _10313"
  by (import hollight DEF_three_2)

constdefs
  three_3 :: "N_3" 
  "three_3 == _10314"

lemma DEF_three_3: "three_3 = _10314"
  by (import hollight DEF_three_3)

lemma list_INDUCT: "ALL P::'A::type hollight.list => bool.
   P NIL &
   (ALL (a0::'A::type) a1::'A::type hollight.list.
       P a1 --> P (CONS a0 a1)) -->
   All P"
  by (import hollight list_INDUCT)

constdefs
  HD :: "'A hollight.list => 'A" 
  "HD ==
SOME HD::'A::type hollight.list => 'A::type.
   ALL (t::'A::type hollight.list) h::'A::type. HD (CONS h t) = h"

lemma DEF_HD: "HD =
(SOME HD::'A::type hollight.list => 'A::type.
    ALL (t::'A::type hollight.list) h::'A::type. HD (CONS h t) = h)"
  by (import hollight DEF_HD)

constdefs
  TL :: "'A hollight.list => 'A hollight.list" 
  "TL ==
SOME TL::'A::type hollight.list => 'A::type hollight.list.
   ALL (h::'A::type) t::'A::type hollight.list. TL (CONS h t) = t"

lemma DEF_TL: "TL =
(SOME TL::'A::type hollight.list => 'A::type hollight.list.
    ALL (h::'A::type) t::'A::type hollight.list. TL (CONS h t) = t)"
  by (import hollight DEF_TL)

constdefs
  APPEND :: "'A hollight.list => 'A hollight.list => 'A hollight.list" 
  "APPEND ==
SOME APPEND::'A::type hollight.list
             => 'A::type hollight.list => 'A::type hollight.list.
   (ALL l::'A::type hollight.list. APPEND NIL l = l) &
   (ALL (h::'A::type) (t::'A::type hollight.list) l::'A::type hollight.list.
       APPEND (CONS h t) l = CONS h (APPEND t l))"

lemma DEF_APPEND: "APPEND =
(SOME APPEND::'A::type hollight.list
              => 'A::type hollight.list => 'A::type hollight.list.
    (ALL l::'A::type hollight.list. APPEND NIL l = l) &
    (ALL (h::'A::type) (t::'A::type hollight.list)
        l::'A::type hollight.list.
        APPEND (CONS h t) l = CONS h (APPEND t l)))"
  by (import hollight DEF_APPEND)

constdefs
  REVERSE :: "'A hollight.list => 'A hollight.list" 
  "REVERSE ==
SOME REVERSE::'A::type hollight.list => 'A::type hollight.list.
   REVERSE NIL = NIL &
   (ALL (l::'A::type hollight.list) x::'A::type.
       REVERSE (CONS x l) = APPEND (REVERSE l) (CONS x NIL))"

lemma DEF_REVERSE: "REVERSE =
(SOME REVERSE::'A::type hollight.list => 'A::type hollight.list.
    REVERSE NIL = NIL &
    (ALL (l::'A::type hollight.list) x::'A::type.
        REVERSE (CONS x l) = APPEND (REVERSE l) (CONS x NIL)))"
  by (import hollight DEF_REVERSE)

constdefs
  LENGTH :: "'A hollight.list => nat" 
  "LENGTH ==
SOME LENGTH::'A::type hollight.list => nat.
   LENGTH NIL = 0 &
   (ALL (h::'A::type) t::'A::type hollight.list.
       LENGTH (CONS h t) = Suc (LENGTH t))"

lemma DEF_LENGTH: "LENGTH =
(SOME LENGTH::'A::type hollight.list => nat.
    LENGTH NIL = 0 &
    (ALL (h::'A::type) t::'A::type hollight.list.
        LENGTH (CONS h t) = Suc (LENGTH t)))"
  by (import hollight DEF_LENGTH)

constdefs
  MAP :: "('A => 'B) => 'A hollight.list => 'B hollight.list" 
  "MAP ==
SOME MAP::('A::type => 'B::type)
          => 'A::type hollight.list => 'B::type hollight.list.
   (ALL f::'A::type => 'B::type. MAP f NIL = NIL) &
   (ALL (f::'A::type => 'B::type) (h::'A::type) t::'A::type hollight.list.
       MAP f (CONS h t) = CONS (f h) (MAP f t))"

lemma DEF_MAP: "MAP =
(SOME MAP::('A::type => 'B::type)
           => 'A::type hollight.list => 'B::type hollight.list.
    (ALL f::'A::type => 'B::type. MAP f NIL = NIL) &
    (ALL (f::'A::type => 'B::type) (h::'A::type) t::'A::type hollight.list.
        MAP f (CONS h t) = CONS (f h) (MAP f t)))"
  by (import hollight DEF_MAP)

constdefs
  LAST :: "'A hollight.list => 'A" 
  "LAST ==
SOME LAST::'A::type hollight.list => 'A::type.
   ALL (h::'A::type) t::'A::type hollight.list.
      LAST (CONS h t) = COND (t = NIL) h (LAST t)"

lemma DEF_LAST: "LAST =
(SOME LAST::'A::type hollight.list => 'A::type.
    ALL (h::'A::type) t::'A::type hollight.list.
       LAST (CONS h t) = COND (t = NIL) h (LAST t))"
  by (import hollight DEF_LAST)

constdefs
  REPLICATE :: "nat => 'q_16809 => 'q_16809 hollight.list" 
  "REPLICATE ==
SOME REPLICATE::nat => 'q_16809::type => 'q_16809::type hollight.list.
   (ALL x::'q_16809::type. REPLICATE 0 x = NIL) &
   (ALL (n::nat) x::'q_16809::type.
       REPLICATE (Suc n) x = CONS x (REPLICATE n x))"

lemma DEF_REPLICATE: "REPLICATE =
(SOME REPLICATE::nat => 'q_16809::type => 'q_16809::type hollight.list.
    (ALL x::'q_16809::type. REPLICATE 0 x = NIL) &
    (ALL (n::nat) x::'q_16809::type.
        REPLICATE (Suc n) x = CONS x (REPLICATE n x)))"
  by (import hollight DEF_REPLICATE)

constdefs
  NULL :: "'q_16824 hollight.list => bool" 
  "NULL ==
SOME NULL::'q_16824::type hollight.list => bool.
   NULL NIL = True &
   (ALL (h::'q_16824::type) t::'q_16824::type hollight.list.
       NULL (CONS h t) = False)"

lemma DEF_NULL: "NULL =
(SOME NULL::'q_16824::type hollight.list => bool.
    NULL NIL = True &
    (ALL (h::'q_16824::type) t::'q_16824::type hollight.list.
        NULL (CONS h t) = False))"
  by (import hollight DEF_NULL)

constdefs
  ALL_list :: "('q_16844 => bool) => 'q_16844 hollight.list => bool" 
  "ALL_list ==
SOME u::('q_16844::type => bool) => 'q_16844::type hollight.list => bool.
   (ALL P::'q_16844::type => bool. u P NIL = True) &
   (ALL (h::'q_16844::type) (P::'q_16844::type => bool)
       t::'q_16844::type hollight.list. u P (CONS h t) = (P h & u P t))"

lemma DEF_ALL: "ALL_list =
(SOME u::('q_16844::type => bool) => 'q_16844::type hollight.list => bool.
    (ALL P::'q_16844::type => bool. u P NIL = True) &
    (ALL (h::'q_16844::type) (P::'q_16844::type => bool)
        t::'q_16844::type hollight.list. u P (CONS h t) = (P h & u P t)))"
  by (import hollight DEF_ALL)

consts
  EX :: "('q_16865 => bool) => 'q_16865 hollight.list => bool" ("EX")

defs
  EX_def: "EX ==
SOME u::('q_16865::type => bool) => 'q_16865::type hollight.list => bool.
   (ALL P::'q_16865::type => bool. u P NIL = False) &
   (ALL (h::'q_16865::type) (P::'q_16865::type => bool)
       t::'q_16865::type hollight.list. u P (CONS h t) = (P h | u P t))"

lemma DEF_EX: "EX =
(SOME u::('q_16865::type => bool) => 'q_16865::type hollight.list => bool.
    (ALL P::'q_16865::type => bool. u P NIL = False) &
    (ALL (h::'q_16865::type) (P::'q_16865::type => bool)
        t::'q_16865::type hollight.list. u P (CONS h t) = (P h | u P t)))"
  by (import hollight DEF_EX)

constdefs
  ITLIST :: "('q_16888 => 'q_16887 => 'q_16887)
=> 'q_16888 hollight.list => 'q_16887 => 'q_16887" 
  "ITLIST ==
SOME ITLIST::('q_16888::type => 'q_16887::type => 'q_16887::type)
             => 'q_16888::type hollight.list
                => 'q_16887::type => 'q_16887::type.
   (ALL (f::'q_16888::type => 'q_16887::type => 'q_16887::type)
       b::'q_16887::type. ITLIST f NIL b = b) &
   (ALL (h::'q_16888::type)
       (f::'q_16888::type => 'q_16887::type => 'q_16887::type)
       (t::'q_16888::type hollight.list) b::'q_16887::type.
       ITLIST f (CONS h t) b = f h (ITLIST f t b))"

lemma DEF_ITLIST: "ITLIST =
(SOME ITLIST::('q_16888::type => 'q_16887::type => 'q_16887::type)
              => 'q_16888::type hollight.list
                 => 'q_16887::type => 'q_16887::type.
    (ALL (f::'q_16888::type => 'q_16887::type => 'q_16887::type)
        b::'q_16887::type. ITLIST f NIL b = b) &
    (ALL (h::'q_16888::type)
        (f::'q_16888::type => 'q_16887::type => 'q_16887::type)
        (t::'q_16888::type hollight.list) b::'q_16887::type.
        ITLIST f (CONS h t) b = f h (ITLIST f t b)))"
  by (import hollight DEF_ITLIST)

constdefs
  MEM :: "'q_16913 => 'q_16913 hollight.list => bool" 
  "MEM ==
SOME MEM::'q_16913::type => 'q_16913::type hollight.list => bool.
   (ALL x::'q_16913::type. MEM x NIL = False) &
   (ALL (h::'q_16913::type) (x::'q_16913::type)
       t::'q_16913::type hollight.list.
       MEM x (CONS h t) = (x = h | MEM x t))"

lemma DEF_MEM: "MEM =
(SOME MEM::'q_16913::type => 'q_16913::type hollight.list => bool.
    (ALL x::'q_16913::type. MEM x NIL = False) &
    (ALL (h::'q_16913::type) (x::'q_16913::type)
        t::'q_16913::type hollight.list.
        MEM x (CONS h t) = (x = h | MEM x t)))"
  by (import hollight DEF_MEM)

constdefs
  ALL2 :: "('q_16946 => 'q_16953 => bool)
=> 'q_16946 hollight.list => 'q_16953 hollight.list => bool" 
  "ALL2 ==
SOME ALL2::('q_16946::type => 'q_16953::type => bool)
           => 'q_16946::type hollight.list
              => 'q_16953::type hollight.list => bool.
   (ALL (P::'q_16946::type => 'q_16953::type => bool)
       l2::'q_16953::type hollight.list. ALL2 P NIL l2 = (l2 = NIL)) &
   (ALL (h1::'q_16946::type) (P::'q_16946::type => 'q_16953::type => bool)
       (t1::'q_16946::type hollight.list) l2::'q_16953::type hollight.list.
       ALL2 P (CONS h1 t1) l2 =
       COND (l2 = NIL) False (P h1 (HD l2) & ALL2 P t1 (TL l2)))"

lemma DEF_ALL2: "ALL2 =
(SOME ALL2::('q_16946::type => 'q_16953::type => bool)
            => 'q_16946::type hollight.list
               => 'q_16953::type hollight.list => bool.
    (ALL (P::'q_16946::type => 'q_16953::type => bool)
        l2::'q_16953::type hollight.list. ALL2 P NIL l2 = (l2 = NIL)) &
    (ALL (h1::'q_16946::type) (P::'q_16946::type => 'q_16953::type => bool)
        (t1::'q_16946::type hollight.list) l2::'q_16953::type hollight.list.
        ALL2 P (CONS h1 t1) l2 =
        COND (l2 = NIL) False (P h1 (HD l2) & ALL2 P t1 (TL l2))))"
  by (import hollight DEF_ALL2)

lemma ALL2: "ALL2 (P::'q_17008::type => 'q_17007::type => bool) NIL NIL = True &
ALL2 P (CONS (h1::'q_17008::type) (t1::'q_17008::type hollight.list)) NIL =
False &
ALL2 P NIL (CONS (h2::'q_17007::type) (t2::'q_17007::type hollight.list)) =
False &
ALL2 P (CONS h1 t1) (CONS h2 t2) = (P h1 h2 & ALL2 P t1 t2)"
  by (import hollight ALL2)

constdefs
  MAP2 :: "('q_17038 => 'q_17045 => 'q_17035)
=> 'q_17038 hollight.list
   => 'q_17045 hollight.list => 'q_17035 hollight.list" 
  "MAP2 ==
SOME MAP2::('q_17038::type => 'q_17045::type => 'q_17035::type)
           => 'q_17038::type hollight.list
              => 'q_17045::type hollight.list
                 => 'q_17035::type hollight.list.
   (ALL (f::'q_17038::type => 'q_17045::type => 'q_17035::type)
       l::'q_17045::type hollight.list. MAP2 f NIL l = NIL) &
   (ALL (h1::'q_17038::type)
       (f::'q_17038::type => 'q_17045::type => 'q_17035::type)
       (t1::'q_17038::type hollight.list) l::'q_17045::type hollight.list.
       MAP2 f (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l)))"

lemma DEF_MAP2: "MAP2 =
(SOME MAP2::('q_17038::type => 'q_17045::type => 'q_17035::type)
            => 'q_17038::type hollight.list
               => 'q_17045::type hollight.list
                  => 'q_17035::type hollight.list.
    (ALL (f::'q_17038::type => 'q_17045::type => 'q_17035::type)
        l::'q_17045::type hollight.list. MAP2 f NIL l = NIL) &
    (ALL (h1::'q_17038::type)
        (f::'q_17038::type => 'q_17045::type => 'q_17035::type)
        (t1::'q_17038::type hollight.list) l::'q_17045::type hollight.list.
        MAP2 f (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l))))"
  by (import hollight DEF_MAP2)

lemma MAP2: "MAP2 (f::'q_17080::type => 'q_17079::type => 'q_17086::type) NIL NIL = NIL &
MAP2 f (CONS (h1::'q_17080::type) (t1::'q_17080::type hollight.list))
 (CONS (h2::'q_17079::type) (t2::'q_17079::type hollight.list)) =
CONS (f h1 h2) (MAP2 f t1 t2)"
  by (import hollight MAP2)

constdefs
  EL :: "nat => 'q_17106 hollight.list => 'q_17106" 
  "EL ==
SOME EL::nat => 'q_17106::type hollight.list => 'q_17106::type.
   (ALL l::'q_17106::type hollight.list. EL 0 l = HD l) &
   (ALL (n::nat) l::'q_17106::type hollight.list.
       EL (Suc n) l = EL n (TL l))"

lemma DEF_EL: "EL =
(SOME EL::nat => 'q_17106::type hollight.list => 'q_17106::type.
    (ALL l::'q_17106::type hollight.list. EL 0 l = HD l) &
    (ALL (n::nat) l::'q_17106::type hollight.list.
        EL (Suc n) l = EL n (TL l)))"
  by (import hollight DEF_EL)

constdefs
  FILTER :: "('q_17131 => bool) => 'q_17131 hollight.list => 'q_17131 hollight.list" 
  "FILTER ==
SOME FILTER::('q_17131::type => bool)
             => 'q_17131::type hollight.list
                => 'q_17131::type hollight.list.
   (ALL P::'q_17131::type => bool. FILTER P NIL = NIL) &
   (ALL (h::'q_17131::type) (P::'q_17131::type => bool)
       t::'q_17131::type hollight.list.
       FILTER P (CONS h t) = COND (P h) (CONS h (FILTER P t)) (FILTER P t))"

lemma DEF_FILTER: "FILTER =
(SOME FILTER::('q_17131::type => bool)
              => 'q_17131::type hollight.list
                 => 'q_17131::type hollight.list.
    (ALL P::'q_17131::type => bool. FILTER P NIL = NIL) &
    (ALL (h::'q_17131::type) (P::'q_17131::type => bool)
        t::'q_17131::type hollight.list.
        FILTER P (CONS h t) =
        COND (P h) (CONS h (FILTER P t)) (FILTER P t)))"
  by (import hollight DEF_FILTER)

constdefs
  ASSOC :: "'q_17160 => ('q_17160 * 'q_17154) hollight.list => 'q_17154" 
  "ASSOC ==
SOME ASSOC::'q_17160::type
            => ('q_17160::type * 'q_17154::type) hollight.list
               => 'q_17154::type.
   ALL (h::'q_17160::type * 'q_17154::type) (a::'q_17160::type)
      t::('q_17160::type * 'q_17154::type) hollight.list.
      ASSOC a (CONS h t) = COND (fst h = a) (snd h) (ASSOC a t)"

lemma DEF_ASSOC: "ASSOC =
(SOME ASSOC::'q_17160::type
             => ('q_17160::type * 'q_17154::type) hollight.list
                => 'q_17154::type.
    ALL (h::'q_17160::type * 'q_17154::type) (a::'q_17160::type)
       t::('q_17160::type * 'q_17154::type) hollight.list.
       ASSOC a (CONS h t) = COND (fst h = a) (snd h) (ASSOC a t))"
  by (import hollight DEF_ASSOC)

constdefs
  ITLIST2 :: "('q_17184 => 'q_17192 => 'q_17182 => 'q_17182)
=> 'q_17184 hollight.list => 'q_17192 hollight.list => 'q_17182 => 'q_17182" 
  "ITLIST2 ==
SOME ITLIST2::('q_17184::type
               => 'q_17192::type => 'q_17182::type => 'q_17182::type)
              => 'q_17184::type hollight.list
                 => 'q_17192::type hollight.list
                    => 'q_17182::type => 'q_17182::type.
   (ALL (f::'q_17184::type
            => 'q_17192::type => 'q_17182::type => 'q_17182::type)
       (l2::'q_17192::type hollight.list) b::'q_17182::type.
       ITLIST2 f NIL l2 b = b) &
   (ALL (h1::'q_17184::type)
       (f::'q_17184::type
           => 'q_17192::type => 'q_17182::type => 'q_17182::type)
       (t1::'q_17184::type hollight.list) (l2::'q_17192::type hollight.list)
       b::'q_17182::type.
       ITLIST2 f (CONS h1 t1) l2 b = f h1 (HD l2) (ITLIST2 f t1 (TL l2) b))"

lemma DEF_ITLIST2: "ITLIST2 =
(SOME ITLIST2::('q_17184::type
                => 'q_17192::type => 'q_17182::type => 'q_17182::type)
               => 'q_17184::type hollight.list
                  => 'q_17192::type hollight.list
                     => 'q_17182::type => 'q_17182::type.
    (ALL (f::'q_17184::type
             => 'q_17192::type => 'q_17182::type => 'q_17182::type)
        (l2::'q_17192::type hollight.list) b::'q_17182::type.
        ITLIST2 f NIL l2 b = b) &
    (ALL (h1::'q_17184::type)
        (f::'q_17184::type
            => 'q_17192::type => 'q_17182::type => 'q_17182::type)
        (t1::'q_17184::type hollight.list)
        (l2::'q_17192::type hollight.list) b::'q_17182::type.
        ITLIST2 f (CONS h1 t1) l2 b =
        f h1 (HD l2) (ITLIST2 f t1 (TL l2) b)))"
  by (import hollight DEF_ITLIST2)

lemma ITLIST2: "ITLIST2
 (f::'q_17226::type => 'q_17225::type => 'q_17224::type => 'q_17224::type)
 NIL NIL (b::'q_17224::type) =
b &
ITLIST2 f (CONS (h1::'q_17226::type) (t1::'q_17226::type hollight.list))
 (CONS (h2::'q_17225::type) (t2::'q_17225::type hollight.list)) b =
f h1 h2 (ITLIST2 f t1 t2 b)"
  by (import hollight ITLIST2)

consts
  ZIP :: "'q_17256 hollight.list
=> 'q_17264 hollight.list => ('q_17256 * 'q_17264) hollight.list" 

defs
  ZIP_def: "hollight.ZIP ==
SOME ZIP::'q_17256::type hollight.list
          => 'q_17264::type hollight.list
             => ('q_17256::type * 'q_17264::type) hollight.list.
   (ALL l2::'q_17264::type hollight.list. ZIP NIL l2 = NIL) &
   (ALL (h1::'q_17256::type) (t1::'q_17256::type hollight.list)
       l2::'q_17264::type hollight.list.
       ZIP (CONS h1 t1) l2 = CONS (h1, HD l2) (ZIP t1 (TL l2)))"

lemma DEF_ZIP: "hollight.ZIP =
(SOME ZIP::'q_17256::type hollight.list
           => 'q_17264::type hollight.list
              => ('q_17256::type * 'q_17264::type) hollight.list.
    (ALL l2::'q_17264::type hollight.list. ZIP NIL l2 = NIL) &
    (ALL (h1::'q_17256::type) (t1::'q_17256::type hollight.list)
        l2::'q_17264::type hollight.list.
        ZIP (CONS h1 t1) l2 = CONS (h1, HD l2) (ZIP t1 (TL l2))))"
  by (import hollight DEF_ZIP)

lemma ZIP: "(op &::bool => bool => bool)
 ((op =::('q_17275::type * 'q_17276::type) hollight.list
         => ('q_17275::type * 'q_17276::type) hollight.list => bool)
   ((hollight.ZIP::'q_17275::type hollight.list
                   => 'q_17276::type hollight.list
                      => ('q_17275::type * 'q_17276::type) hollight.list)
     (NIL::'q_17275::type hollight.list)
     (NIL::'q_17276::type hollight.list))
   (NIL::('q_17275::type * 'q_17276::type) hollight.list))
 ((op =::('q_17300::type * 'q_17301::type) hollight.list
         => ('q_17300::type * 'q_17301::type) hollight.list => bool)
   ((hollight.ZIP::'q_17300::type hollight.list
                   => 'q_17301::type hollight.list
                      => ('q_17300::type * 'q_17301::type) hollight.list)
     ((CONS::'q_17300::type
             => 'q_17300::type hollight.list
                => 'q_17300::type hollight.list)
       (h1::'q_17300::type) (t1::'q_17300::type hollight.list))
     ((CONS::'q_17301::type
             => 'q_17301::type hollight.list
                => 'q_17301::type hollight.list)
       (h2::'q_17301::type) (t2::'q_17301::type hollight.list)))
   ((CONS::'q_17300::type * 'q_17301::type
           => ('q_17300::type * 'q_17301::type) hollight.list
              => ('q_17300::type * 'q_17301::type) hollight.list)
     ((Pair::'q_17300::type
             => 'q_17301::type => 'q_17300::type * 'q_17301::type)
       h1 h2)
     ((hollight.ZIP::'q_17300::type hollight.list
                     => 'q_17301::type hollight.list
                        => ('q_17300::type * 'q_17301::type) hollight.list)
       t1 t2)))"
  by (import hollight ZIP)

lemma NOT_CONS_NIL: "ALL (x::'A::type) xa::'A::type hollight.list. CONS x xa ~= NIL"
  by (import hollight NOT_CONS_NIL)

lemma LAST_CLAUSES: "LAST (CONS (h::'A::type) NIL) = h &
LAST (CONS h (CONS (k::'A::type) (t::'A::type hollight.list))) =
LAST (CONS k t)"
  by (import hollight LAST_CLAUSES)

lemma APPEND_NIL: "ALL l::'A::type hollight.list. APPEND l NIL = l"
  by (import hollight APPEND_NIL)

lemma APPEND_ASSOC: "ALL (l::'A::type hollight.list) (m::'A::type hollight.list)
   n::'A::type hollight.list. APPEND l (APPEND m n) = APPEND (APPEND l m) n"
  by (import hollight APPEND_ASSOC)

lemma REVERSE_APPEND: "ALL (l::'A::type hollight.list) m::'A::type hollight.list.
   REVERSE (APPEND l m) = APPEND (REVERSE m) (REVERSE l)"
  by (import hollight REVERSE_APPEND)

lemma REVERSE_REVERSE: "ALL l::'A::type hollight.list. REVERSE (REVERSE l) = l"
  by (import hollight REVERSE_REVERSE)

lemma CONS_11: "ALL (x::'A::type) (xa::'A::type) (xb::'A::type hollight.list)
   xc::'A::type hollight.list. (CONS x xb = CONS xa xc) = (x = xa & xb = xc)"
  by (import hollight CONS_11)

lemma list_CASES: "ALL l::'A::type hollight.list.
   l = NIL | (EX (h::'A::type) t::'A::type hollight.list. l = CONS h t)"
  by (import hollight list_CASES)

lemma LENGTH_APPEND: "ALL (l::'A::type hollight.list) m::'A::type hollight.list.
   LENGTH (APPEND l m) = LENGTH l + LENGTH m"
  by (import hollight LENGTH_APPEND)

lemma MAP_APPEND: "ALL (f::'A::type => 'B::type) (l1::'A::type hollight.list)
   l2::'A::type hollight.list.
   MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)"
  by (import hollight MAP_APPEND)

lemma LENGTH_MAP: "ALL (l::'A::type hollight.list) f::'A::type => 'B::type.
   LENGTH (MAP f l) = LENGTH l"
  by (import hollight LENGTH_MAP)

lemma LENGTH_EQ_NIL: "ALL l::'A::type hollight.list. (LENGTH l = 0) = (l = NIL)"
  by (import hollight LENGTH_EQ_NIL)

lemma LENGTH_EQ_CONS: "ALL (l::'q_17608::type hollight.list) n::nat.
   (LENGTH l = Suc n) =
   (EX (h::'q_17608::type) t::'q_17608::type hollight.list.
       l = CONS h t & LENGTH t = n)"
  by (import hollight LENGTH_EQ_CONS)

lemma MAP_o: "ALL (f::'A::type => 'B::type) (g::'B::type => 'C::type)
   l::'A::type hollight.list. MAP (g o f) l = MAP g (MAP f l)"
  by (import hollight MAP_o)

lemma MAP_EQ: "ALL (f::'q_17672::type => 'q_17683::type)
   (g::'q_17672::type => 'q_17683::type) l::'q_17672::type hollight.list.
   ALL_list (%x::'q_17672::type. f x = g x) l --> MAP f l = MAP g l"
  by (import hollight MAP_EQ)

lemma ALL_IMP: "ALL (P::'q_17713::type => bool) (Q::'q_17713::type => bool)
   l::'q_17713::type hollight.list.
   (ALL x::'q_17713::type. MEM x l & P x --> Q x) & ALL_list P l -->
   ALL_list Q l"
  by (import hollight ALL_IMP)

lemma NOT_EX: "ALL (P::'q_17741::type => bool) l::'q_17741::type hollight.list.
   (~ EX P l) = ALL_list (%x::'q_17741::type. ~ P x) l"
  by (import hollight NOT_EX)

lemma NOT_ALL: "ALL (P::'q_17763::type => bool) l::'q_17763::type hollight.list.
   (~ ALL_list P l) = EX (%x::'q_17763::type. ~ P x) l"
  by (import hollight NOT_ALL)

lemma ALL_MAP: "ALL (P::'q_17785::type => bool) (f::'q_17784::type => 'q_17785::type)
   l::'q_17784::type hollight.list.
   ALL_list P (MAP f l) = ALL_list (P o f) l"
  by (import hollight ALL_MAP)

lemma ALL_T: "All (ALL_list (%x::'q_17803::type. True))"
  by (import hollight ALL_T)

lemma MAP_EQ_ALL2: "ALL (l::'q_17828::type hollight.list) m::'q_17828::type hollight.list.
   ALL2
    (%(x::'q_17828::type) y::'q_17828::type.
        (f::'q_17828::type => 'q_17839::type) x = f y)
    l m -->
   MAP f l = MAP f m"
  by (import hollight MAP_EQ_ALL2)

lemma ALL2_MAP: "ALL (P::'q_17870::type => 'q_17871::type => bool)
   (f::'q_17871::type => 'q_17870::type) l::'q_17871::type hollight.list.
   ALL2 P (MAP f l) l = ALL_list (%a::'q_17871::type. P (f a) a) l"
  by (import hollight ALL2_MAP)

lemma MAP_EQ_DEGEN: "ALL (l::'q_17888::type hollight.list) f::'q_17888::type => 'q_17888::type.
   ALL_list (%x::'q_17888::type. f x = x) l --> MAP f l = l"
  by (import hollight MAP_EQ_DEGEN)

lemma ALL2_AND_RIGHT: "ALL (l::'q_17931::type hollight.list) (m::'q_17930::type hollight.list)
   (P::'q_17931::type => bool) Q::'q_17931::type => 'q_17930::type => bool.
   ALL2 (%(x::'q_17931::type) y::'q_17930::type. P x & Q x y) l m =
   (ALL_list P l & ALL2 Q l m)"
  by (import hollight ALL2_AND_RIGHT)

lemma ITLIST_EXTRA: "ALL l::'q_17968::type hollight.list.
   ITLIST (f::'q_17968::type => 'q_17967::type => 'q_17967::type)
    (APPEND l (CONS (a::'q_17968::type) NIL)) (b::'q_17967::type) =
   ITLIST f l (f a b)"
  by (import hollight ITLIST_EXTRA)

lemma ALL_MP: "ALL (P::'q_17994::type => bool) (Q::'q_17994::type => bool)
   l::'q_17994::type hollight.list.
   ALL_list (%x::'q_17994::type. P x --> Q x) l & ALL_list P l -->
   ALL_list Q l"
  by (import hollight ALL_MP)

lemma AND_ALL: "ALL x::'q_18024::type hollight.list.
   (ALL_list (P::'q_18024::type => bool) x &
    ALL_list (Q::'q_18024::type => bool) x) =
   ALL_list (%x::'q_18024::type. P x & Q x) x"
  by (import hollight AND_ALL)

lemma EX_IMP: "ALL (P::'q_18054::type => bool) (Q::'q_18054::type => bool)
   l::'q_18054::type hollight.list.
   (ALL x::'q_18054::type. MEM x l & P x --> Q x) & EX P l --> EX Q l"
  by (import hollight EX_IMP)

lemma ALL_MEM: "ALL (P::'q_18081::type => bool) l::'q_18081::type hollight.list.
   (ALL x::'q_18081::type. MEM x l --> P x) = ALL_list P l"
  by (import hollight ALL_MEM)

lemma LENGTH_REPLICATE: "ALL (n::nat) x::'q_18099::type. LENGTH (REPLICATE n x) = n"
  by (import hollight LENGTH_REPLICATE)

lemma EX_MAP: "ALL (P::'q_18123::type => bool) (f::'q_18122::type => 'q_18123::type)
   l::'q_18122::type hollight.list. EX P (MAP f l) = EX (P o f) l"
  by (import hollight EX_MAP)

lemma EXISTS_EX: "ALL (P::'q_18161::type => 'q_18160::type => bool)
   l::'q_18160::type hollight.list.
   (EX x::'q_18161::type. EX (P x) l) =
   EX (%s::'q_18160::type. EX x::'q_18161::type. P x s) l"
  by (import hollight EXISTS_EX)

lemma FORALL_ALL: "ALL (P::'q_18191::type => 'q_18190::type => bool)
   l::'q_18190::type hollight.list.
   (ALL x::'q_18191::type. ALL_list (P x) l) =
   ALL_list (%s::'q_18190::type. ALL x::'q_18191::type. P x s) l"
  by (import hollight FORALL_ALL)

lemma MEM_APPEND: "ALL (x::'q_18219::type) (l1::'q_18219::type hollight.list)
   l2::'q_18219::type hollight.list.
   MEM x (APPEND l1 l2) = (MEM x l1 | MEM x l2)"
  by (import hollight MEM_APPEND)

lemma MEM_MAP: "ALL (f::'q_18255::type => 'q_18252::type) (y::'q_18252::type)
   l::'q_18255::type hollight.list.
   MEM y (MAP f l) = (EX x::'q_18255::type. MEM x l & y = f x)"
  by (import hollight MEM_MAP)

lemma FILTER_APPEND: "ALL (P::'q_18286::type => bool) (l1::'q_18286::type hollight.list)
   l2::'q_18286::type hollight.list.
   FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)"
  by (import hollight FILTER_APPEND)

lemma FILTER_MAP: "ALL (P::'q_18313::type => bool) (f::'q_18320::type => 'q_18313::type)
   l::'q_18320::type hollight.list.
   FILTER P (MAP f l) = MAP f (FILTER (P o f) l)"
  by (import hollight FILTER_MAP)

lemma MEM_FILTER: "ALL (P::'q_18347::type => bool) (l::'q_18347::type hollight.list)
   x::'q_18347::type. MEM x (FILTER P l) = (P x & MEM x l)"
  by (import hollight MEM_FILTER)

lemma EX_MEM: "ALL (P::'q_18368::type => bool) l::'q_18368::type hollight.list.
   (EX x::'q_18368::type. P x & MEM x l) = EX P l"
  by (import hollight EX_MEM)

lemma MAP_FST_ZIP: "ALL (l1::'q_18388::type hollight.list) l2::'q_18390::type hollight.list.
   LENGTH l1 = LENGTH l2 --> MAP fst (hollight.ZIP l1 l2) = l1"
  by (import hollight MAP_FST_ZIP)

lemma MAP_SND_ZIP: "ALL (l1::'q_18419::type hollight.list) l2::'q_18421::type hollight.list.
   LENGTH l1 = LENGTH l2 --> MAP snd (hollight.ZIP l1 l2) = l2"
  by (import hollight MAP_SND_ZIP)

lemma MEM_ASSOC: "ALL (l::('q_18465::type * 'q_18449::type) hollight.list) x::'q_18465::type.
   MEM (x, ASSOC x l) l = MEM x (MAP fst l)"
  by (import hollight MEM_ASSOC)

lemma ALL_APPEND: "ALL (P::'q_18486::type => bool) (l1::'q_18486::type hollight.list)
   l2::'q_18486::type hollight.list.
   ALL_list P (APPEND l1 l2) = (ALL_list P l1 & ALL_list P l2)"
  by (import hollight ALL_APPEND)

lemma MEM_EL: "ALL (l::'q_18509::type hollight.list) n::nat.
   < n (LENGTH l) --> MEM (EL n l) l"
  by (import hollight MEM_EL)

lemma ALL2_MAP2: "ALL (l::'q_18552::type hollight.list) m::'q_18553::type hollight.list.
   ALL2 (P::'q_18551::type => 'q_18550::type => bool)
    (MAP (f::'q_18552::type => 'q_18551::type) l)
    (MAP (g::'q_18553::type => 'q_18550::type) m) =
   ALL2 (%(x::'q_18552::type) y::'q_18553::type. P (f x) (g y)) l m"
  by (import hollight ALL2_MAP2)

lemma AND_ALL2: "ALL (P::'q_18599::type => 'q_18598::type => bool)
   (Q::'q_18599::type => 'q_18598::type => bool)
   (x::'q_18599::type hollight.list) xa::'q_18598::type hollight.list.
   (ALL2 P x xa & ALL2 Q x xa) =
   ALL2 (%(x::'q_18599::type) y::'q_18598::type. P x y & Q x y) x xa"
  by (import hollight AND_ALL2)

lemma ALL2_ALL: "ALL (P::'q_18621::type => 'q_18621::type => bool)
   l::'q_18621::type hollight.list.
   ALL2 P l l = ALL_list (%x::'q_18621::type. P x x) l"
  by (import hollight ALL2_ALL)

lemma APPEND_EQ_NIL: "ALL (x::'q_18650::type hollight.list) xa::'q_18650::type hollight.list.
   (APPEND x xa = NIL) = (x = NIL & xa = NIL)"
  by (import hollight APPEND_EQ_NIL)

lemma LENGTH_MAP2: "ALL (f::'q_18670::type => 'q_18672::type => 'q_18683::type)
   (l::'q_18670::type hollight.list) m::'q_18672::type hollight.list.
   LENGTH l = LENGTH m --> LENGTH (MAP2 f l m) = LENGTH m"
  by (import hollight LENGTH_MAP2)

lemma MONO_ALL: "(ALL x::'A::type. (P::'A::type => bool) x --> (Q::'A::type => bool) x) -->
ALL_list P (l::'A::type hollight.list) --> ALL_list Q l"
  by (import hollight MONO_ALL)

lemma MONO_ALL2: "(ALL (x::'A::type) y::'B::type.
    (P::'A::type => 'B::type => bool) x y -->
    (Q::'A::type => 'B::type => bool) x y) -->
ALL2 P (l::'A::type hollight.list) (l'::'B::type hollight.list) -->
ALL2 Q l l'"
  by (import hollight MONO_ALL2)

constdefs
  dist :: "nat * nat => nat" 
  "dist == %u::nat * nat. fst u - snd u + (snd u - fst u)"

lemma DEF_dist: "dist = (%u::nat * nat. fst u - snd u + (snd u - fst u))"
  by (import hollight DEF_dist)

lemma DIST_REFL: "ALL x::nat. dist (x, x) = 0"
  by (import hollight DIST_REFL)

lemma DIST_LZERO: "ALL x::nat. dist (0, x) = x"
  by (import hollight DIST_LZERO)

lemma DIST_RZERO: "ALL x::nat. dist (x, 0) = x"
  by (import hollight DIST_RZERO)

lemma DIST_SYM: "ALL (x::nat) xa::nat. dist (x, xa) = dist (xa, x)"
  by (import hollight DIST_SYM)

lemma DIST_LADD: "ALL (x::nat) (xa::nat) xb::nat. dist (x + xb, x + xa) = dist (xb, xa)"
  by (import hollight DIST_LADD)

lemma DIST_RADD: "ALL (x::nat) (xa::nat) xb::nat. dist (x + xa, xb + xa) = dist (x, xb)"
  by (import hollight DIST_RADD)

lemma DIST_LADD_0: "ALL (x::nat) xa::nat. dist (x + xa, x) = xa"
  by (import hollight DIST_LADD_0)

lemma DIST_RADD_0: "ALL (x::nat) xa::nat. dist (x, x + xa) = xa"
  by (import hollight DIST_RADD_0)

lemma DIST_LMUL: "ALL (x::nat) (xa::nat) xb::nat. x * dist (xa, xb) = dist (x * xa, x * xb)"
  by (import hollight DIST_LMUL)

lemma DIST_RMUL: "ALL (x::nat) (xa::nat) xb::nat. dist (x, xa) * xb = dist (x * xb, xa * xb)"
  by (import hollight DIST_RMUL)

lemma DIST_EQ_0: "ALL (x::nat) xa::nat. (dist (x, xa) = 0) = (x = xa)"
  by (import hollight DIST_EQ_0)

lemma DIST_ELIM_THM: "(P::nat => bool) (dist (x::nat, y::nat)) =
(ALL d::nat. (x = y + d --> P d) & (y = x + d --> P d))"
  by (import hollight DIST_ELIM_THM)

lemma DIST_LE_CASES: "ALL (m::nat) (n::nat) p::nat.
   <= (dist (m, n)) p = (<= m (n + p) & <= n (m + p))"
  by (import hollight DIST_LE_CASES)

lemma DIST_ADDBOUND: "ALL (m::nat) n::nat. <= (dist (m, n)) (m + n)"
  by (import hollight DIST_ADDBOUND)

lemma DIST_TRIANGLE: "ALL (m::nat) (n::nat) p::nat. <= (dist (m, p)) (dist (m, n) + dist (n, p))"
  by (import hollight DIST_TRIANGLE)

lemma DIST_ADD2: "ALL (m::nat) (n::nat) (p::nat) q::nat.
   <= (dist (m + n, p + q)) (dist (m, p) + dist (n, q))"
  by (import hollight DIST_ADD2)

lemma DIST_ADD2_REV: "ALL (m::nat) (n::nat) (p::nat) q::nat.
   <= (dist (m, p)) (dist (m + n, p + q) + dist (n, q))"
  by (import hollight DIST_ADD2_REV)

lemma DIST_TRIANGLE_LE: "ALL (m::nat) (n::nat) (p::nat) q::nat.
   <= (dist (m, n) + dist (n, p)) q --> <= (dist (m, p)) q"
  by (import hollight DIST_TRIANGLE_LE)

lemma DIST_TRIANGLES_LE: "ALL (m::nat) (n::nat) (p::nat) (q::nat) (r::nat) s::nat.
   <= (dist (m, n)) r & <= (dist (p, q)) s -->
   <= (dist (m, p)) (dist (n, q) + (r + s))"
  by (import hollight DIST_TRIANGLES_LE)

lemma BOUNDS_LINEAR: "ALL (A::nat) (B::nat) C::nat. (ALL n::nat. <= (A * n) (B * n + C)) = <= A B"
  by (import hollight BOUNDS_LINEAR)

lemma BOUNDS_LINEAR_0: "ALL (A::nat) B::nat. (ALL n::nat. <= (A * n) B) = (A = 0)"
  by (import hollight BOUNDS_LINEAR_0)

lemma BOUNDS_DIVIDED: "ALL P::nat => nat.
   (EX B::nat. ALL n::nat. <= (P n) B) =
   (EX (x::nat) B::nat. ALL n::nat. <= (n * P n) (x * n + B))"
  by (import hollight BOUNDS_DIVIDED)

lemma BOUNDS_NOTZERO: "ALL (P::nat => nat => nat) (A::nat) B::nat.
   P 0 0 = 0 & (ALL (m::nat) n::nat. <= (P m n) (A * (m + n) + B)) -->
   (EX x::nat. ALL (m::nat) n::nat. <= (P m n) (x * (m + n)))"
  by (import hollight BOUNDS_NOTZERO)

lemma BOUNDS_IGNORE: "ALL (P::nat => nat) Q::nat => nat.
   (EX B::nat. ALL i::nat. <= (P i) (Q i + B)) =
   (EX (x::nat) N::nat. ALL i::nat. <= N i --> <= (P i) (Q i + x))"
  by (import hollight BOUNDS_IGNORE)

constdefs
  is_nadd :: "(nat => nat) => bool" 
  "is_nadd ==
%u::nat => nat.
   EX B::nat.
      ALL (m::nat) n::nat. <= (dist (m * u n, n * u m)) (B * (m + n))"

lemma DEF_is_nadd: "is_nadd =
(%u::nat => nat.
    EX B::nat.
       ALL (m::nat) n::nat. <= (dist (m * u n, n * u m)) (B * (m + n)))"
  by (import hollight DEF_is_nadd)

lemma is_nadd_0: "is_nadd (%n::nat. 0)"
  by (import hollight is_nadd_0)

typedef (open) nadd = "Collect is_nadd"  morphisms "dest_nadd" "mk_nadd"
  apply (rule light_ex_imp_nonempty[where t="%n::nat. NUMERAL 0"])
  by (import hollight TYDEF_nadd)

syntax
  dest_nadd :: _ 

syntax
  mk_nadd :: _ 

lemmas "TYDEF_nadd_@intern" = typedef_hol2hollight 
  [where a="a :: nadd" and r=r ,
   OF type_definition_nadd]

lemma NADD_CAUCHY: "ALL x::nadd.
   EX xa::nat.
      ALL (xb::nat) xc::nat.
         <= (dist (xb * dest_nadd x xc, xc * dest_nadd x xb))
          (xa * (xb + xc))"
  by (import hollight NADD_CAUCHY)

lemma NADD_BOUND: "ALL x::nadd.
   EX (xa::nat) B::nat. ALL n::nat. <= (dest_nadd x n) (xa * n + B)"
  by (import hollight NADD_BOUND)

lemma NADD_MULTIPLICATIVE: "ALL x::nadd.
   EX xa::nat.
      ALL (m::nat) n::nat.
         <= (dist (dest_nadd x (m * n), m * dest_nadd x n)) (xa * m + xa)"
  by (import hollight NADD_MULTIPLICATIVE)

lemma NADD_ADDITIVE: "ALL x::nadd.
   EX xa::nat.
      ALL (m::nat) n::nat.
         <= (dist (dest_nadd x (m + n), dest_nadd x m + dest_nadd x n)) xa"
  by (import hollight NADD_ADDITIVE)

lemma NADD_SUC: "ALL x::nadd.
   EX xa::nat. ALL n::nat. <= (dist (dest_nadd x (Suc n), dest_nadd x n)) xa"
  by (import hollight NADD_SUC)

lemma NADD_DIST_LEMMA: "ALL x::nadd.
   EX xa::nat.
      ALL (m::nat) n::nat.
         <= (dist (dest_nadd x (m + n), dest_nadd x m)) (xa * n)"
  by (import hollight NADD_DIST_LEMMA)

lemma NADD_DIST: "ALL x::nadd.
   EX xa::nat.
      ALL (m::nat) n::nat.
         <= (dist (dest_nadd x m, dest_nadd x n)) (xa * dist (m, n))"
  by (import hollight NADD_DIST)

lemma NADD_ALTMUL: "ALL (x::nadd) y::nadd.
   EX (A::nat) B::nat.
      ALL n::nat.
         <= (dist
              (n * dest_nadd x (dest_nadd y n),
               dest_nadd x n * dest_nadd y n))
          (A * n + B)"
  by (import hollight NADD_ALTMUL)

constdefs
  nadd_eq :: "nadd => nadd => bool" 
  "nadd_eq ==
%(u::nadd) ua::nadd.
   EX B::nat. ALL n::nat. <= (dist (dest_nadd u n, dest_nadd ua n)) B"

lemma DEF_nadd_eq: "nadd_eq =
(%(u::nadd) ua::nadd.
    EX B::nat. ALL n::nat. <= (dist (dest_nadd u n, dest_nadd ua n)) B)"
  by (import hollight DEF_nadd_eq)

lemma NADD_EQ_REFL: "ALL x::nadd. nadd_eq x x"
  by (import hollight NADD_EQ_REFL)

lemma NADD_EQ_SYM: "ALL (x::nadd) y::nadd. nadd_eq x y = nadd_eq y x"
  by (import hollight NADD_EQ_SYM)

lemma NADD_EQ_TRANS: "ALL (x::nadd) (y::nadd) z::nadd. nadd_eq x y & nadd_eq y z --> nadd_eq x z"
  by (import hollight NADD_EQ_TRANS)

constdefs
  nadd_of_num :: "nat => nadd" 
  "nadd_of_num == %u::nat. mk_nadd (op * u)"

lemma DEF_nadd_of_num: "nadd_of_num = (%u::nat. mk_nadd (op * u))"
  by (import hollight DEF_nadd_of_num)

lemma NADD_OF_NUM: "ALL x::nat. dest_nadd (nadd_of_num x) = op * x"
  by (import hollight NADD_OF_NUM)

lemma NADD_OF_NUM_WELLDEF: "ALL (m::nat) n::nat. m = n --> nadd_eq (nadd_of_num m) (nadd_of_num n)"
  by (import hollight NADD_OF_NUM_WELLDEF)

lemma NADD_OF_NUM_EQ: "ALL (m::nat) n::nat. nadd_eq (nadd_of_num m) (nadd_of_num n) = (m = n)"
  by (import hollight NADD_OF_NUM_EQ)

constdefs
  nadd_le :: "nadd => nadd => bool" 
  "nadd_le ==
%(u::nadd) ua::nadd.
   EX B::nat. ALL n::nat. <= (dest_nadd u n) (dest_nadd ua n + B)"

lemma DEF_nadd_le: "nadd_le =
(%(u::nadd) ua::nadd.
    EX B::nat. ALL n::nat. <= (dest_nadd u n) (dest_nadd ua n + B))"
  by (import hollight DEF_nadd_le)

lemma NADD_LE_WELLDEF_LEMMA: "ALL (x::nadd) (x'::nadd) (y::nadd) y'::nadd.
   nadd_eq x x' & nadd_eq y y' & nadd_le x y --> nadd_le x' y'"
  by (import hollight NADD_LE_WELLDEF_LEMMA)

lemma NADD_LE_WELLDEF: "ALL (x::nadd) (x'::nadd) (y::nadd) y'::nadd.
   nadd_eq x x' & nadd_eq y y' --> nadd_le x y = nadd_le x' y'"
  by (import hollight NADD_LE_WELLDEF)

lemma NADD_LE_REFL: "ALL x::nadd. nadd_le x x"
  by (import hollight NADD_LE_REFL)

lemma NADD_LE_TRANS: "ALL (x::nadd) (y::nadd) z::nadd. nadd_le x y & nadd_le y z --> nadd_le x z"
  by (import hollight NADD_LE_TRANS)

lemma NADD_LE_ANTISYM: "ALL (x::nadd) y::nadd. (nadd_le x y & nadd_le y x) = nadd_eq x y"
  by (import hollight NADD_LE_ANTISYM)

lemma NADD_LE_TOTAL_LEMMA: "ALL (x::nadd) y::nadd.
   ~ nadd_le x y -->
   (ALL B::nat. EX n::nat. n ~= 0 & < (dest_nadd y n + B) (dest_nadd x n))"
  by (import hollight NADD_LE_TOTAL_LEMMA)

lemma NADD_LE_TOTAL: "ALL (x::nadd) y::nadd. nadd_le x y | nadd_le y x"
  by (import hollight NADD_LE_TOTAL)

lemma NADD_ARCH: "ALL x::nadd. EX xa::nat. nadd_le x (nadd_of_num xa)"
  by (import hollight NADD_ARCH)

lemma NADD_OF_NUM_LE: "ALL (m::nat) n::nat. nadd_le (nadd_of_num m) (nadd_of_num n) = <= m n"
  by (import hollight NADD_OF_NUM_LE)

constdefs
  nadd_add :: "nadd => nadd => nadd" 
  "nadd_add ==
%(u::nadd) ua::nadd. mk_nadd (%n::nat. dest_nadd u n + dest_nadd ua n)"

lemma DEF_nadd_add: "nadd_add =
(%(u::nadd) ua::nadd. mk_nadd (%n::nat. dest_nadd u n + dest_nadd ua n))"
  by (import hollight DEF_nadd_add)

lemma NADD_ADD: "ALL (x::nadd) y::nadd.
   dest_nadd (nadd_add x y) = (%n::nat. dest_nadd x n + dest_nadd y n)"
  by (import hollight NADD_ADD)

lemma NADD_ADD_WELLDEF: "ALL (x::nadd) (x'::nadd) (y::nadd) y'::nadd.
   nadd_eq x x' & nadd_eq y y' --> nadd_eq (nadd_add x y) (nadd_add x' y')"
  by (import hollight NADD_ADD_WELLDEF)

lemma NADD_ADD_SYM: "ALL (x::nadd) y::nadd. nadd_eq (nadd_add x y) (nadd_add y x)"
  by (import hollight NADD_ADD_SYM)

lemma NADD_ADD_ASSOC: "ALL (x::nadd) (y::nadd) z::nadd.
   nadd_eq (nadd_add x (nadd_add y z)) (nadd_add (nadd_add x y) z)"
  by (import hollight NADD_ADD_ASSOC)

lemma NADD_ADD_LID: "ALL x::nadd. nadd_eq (nadd_add (nadd_of_num 0) x) x"
  by (import hollight NADD_ADD_LID)

lemma NADD_ADD_LCANCEL: "ALL (x::nadd) (y::nadd) z::nadd.
   nadd_eq (nadd_add x y) (nadd_add x z) --> nadd_eq y z"
  by (import hollight NADD_ADD_LCANCEL)

lemma NADD_LE_ADD: "ALL (x::nadd) y::nadd. nadd_le x (nadd_add x y)"
  by (import hollight NADD_LE_ADD)

lemma NADD_LE_EXISTS: "ALL (x::nadd) y::nadd.
   nadd_le x y --> (EX d::nadd. nadd_eq y (nadd_add x d))"
  by (import hollight NADD_LE_EXISTS)

lemma NADD_OF_NUM_ADD: "ALL (x::nat) xa::nat.
   nadd_eq (nadd_add (nadd_of_num x) (nadd_of_num xa))
    (nadd_of_num (x + xa))"
  by (import hollight NADD_OF_NUM_ADD)

constdefs
  nadd_mul :: "nadd => nadd => nadd" 
  "nadd_mul ==
%(u::nadd) ua::nadd. mk_nadd (%n::nat. dest_nadd u (dest_nadd ua n))"

lemma DEF_nadd_mul: "nadd_mul =
(%(u::nadd) ua::nadd. mk_nadd (%n::nat. dest_nadd u (dest_nadd ua n)))"
  by (import hollight DEF_nadd_mul)

lemma NADD_MUL: "ALL (x::nadd) y::nadd.
   dest_nadd (nadd_mul x y) = (%n::nat. dest_nadd x (dest_nadd y n))"
  by (import hollight NADD_MUL)

lemma NADD_MUL_SYM: "ALL (x::nadd) y::nadd. nadd_eq (nadd_mul x y) (nadd_mul y x)"
  by (import hollight NADD_MUL_SYM)

lemma NADD_MUL_ASSOC: "ALL (x::nadd) (y::nadd) z::nadd.
   nadd_eq (nadd_mul x (nadd_mul y z)) (nadd_mul (nadd_mul x y) z)"
  by (import hollight NADD_MUL_ASSOC)

lemma NADD_MUL_LID: "ALL x::nadd. nadd_eq (nadd_mul (nadd_of_num (NUMERAL_BIT1 0)) x) x"
  by (import hollight NADD_MUL_LID)

lemma NADD_LDISTRIB: "ALL (x::nadd) (y::nadd) z::nadd.
   nadd_eq (nadd_mul x (nadd_add y z))
    (nadd_add (nadd_mul x y) (nadd_mul x z))"
  by (import hollight NADD_LDISTRIB)

lemma NADD_MUL_WELLDEF_LEMMA: "ALL (x::nadd) (y::nadd) y'::nadd.
   nadd_eq y y' --> nadd_eq (nadd_mul x y) (nadd_mul x y')"
  by (import hollight NADD_MUL_WELLDEF_LEMMA)

lemma NADD_MUL_WELLDEF: "ALL (x::nadd) (x'::nadd) (y::nadd) y'::nadd.
   nadd_eq x x' & nadd_eq y y' --> nadd_eq (nadd_mul x y) (nadd_mul x' y')"
  by (import hollight NADD_MUL_WELLDEF)

lemma NADD_OF_NUM_MUL: "ALL (x::nat) xa::nat.
   nadd_eq (nadd_mul (nadd_of_num x) (nadd_of_num xa))
    (nadd_of_num (x * xa))"
  by (import hollight NADD_OF_NUM_MUL)

lemma NADD_LE_0: "All (nadd_le (nadd_of_num 0))"
  by (import hollight NADD_LE_0)

lemma NADD_EQ_IMP_LE: "ALL (x::nadd) y::nadd. nadd_eq x y --> nadd_le x y"
  by (import hollight NADD_EQ_IMP_LE)

lemma NADD_LE_LMUL: "ALL (x::nadd) (y::nadd) z::nadd.
   nadd_le y z --> nadd_le (nadd_mul x y) (nadd_mul x z)"
  by (import hollight NADD_LE_LMUL)

lemma NADD_LE_RMUL: "ALL (x::nadd) (y::nadd) z::nadd.
   nadd_le x y --> nadd_le (nadd_mul x z) (nadd_mul y z)"
  by (import hollight NADD_LE_RMUL)

lemma NADD_LE_RADD: "ALL (x::nadd) (y::nadd) z::nadd.
   nadd_le (nadd_add x z) (nadd_add y z) = nadd_le x y"
  by (import hollight NADD_LE_RADD)

lemma NADD_LE_LADD: "ALL (x::nadd) (y::nadd) z::nadd.
   nadd_le (nadd_add x y) (nadd_add x z) = nadd_le y z"
  by (import hollight NADD_LE_LADD)

lemma NADD_RDISTRIB: "ALL (x::nadd) (y::nadd) z::nadd.
   nadd_eq (nadd_mul (nadd_add x y) z)
    (nadd_add (nadd_mul x z) (nadd_mul y z))"
  by (import hollight NADD_RDISTRIB)

lemma NADD_ARCH_MULT: "ALL (x::nadd) k::nat.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX xa::nat. nadd_le (nadd_of_num k) (nadd_mul (nadd_of_num xa) x))"
  by (import hollight NADD_ARCH_MULT)

lemma NADD_ARCH_ZERO: "ALL (x::nadd) k::nadd.
   (ALL n::nat. nadd_le (nadd_mul (nadd_of_num n) x) k) -->
   nadd_eq x (nadd_of_num 0)"
  by (import hollight NADD_ARCH_ZERO)

lemma NADD_ARCH_LEMMA: "ALL (x::nadd) (y::nadd) z::nadd.
   (ALL n::nat.
       nadd_le (nadd_mul (nadd_of_num n) x)
        (nadd_add (nadd_mul (nadd_of_num n) y) z)) -->
   nadd_le x y"
  by (import hollight NADD_ARCH_LEMMA)

lemma NADD_COMPLETE: "ALL P::nadd => bool.
   Ex P & (EX M::nadd. ALL x::nadd. P x --> nadd_le x M) -->
   (EX M::nadd.
       (ALL x::nadd. P x --> nadd_le x M) &
       (ALL M'::nadd. (ALL x::nadd. P x --> nadd_le x M') --> nadd_le M M'))"
  by (import hollight NADD_COMPLETE)

lemma NADD_UBOUND: "ALL x::nadd.
   EX (xa::nat) N::nat. ALL n::nat. <= N n --> <= (dest_nadd x n) (xa * n)"
  by (import hollight NADD_UBOUND)

lemma NADD_NONZERO: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX N::nat. ALL n::nat. <= N n --> dest_nadd x n ~= 0)"
  by (import hollight NADD_NONZERO)

lemma NADD_LBOUND: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX (A::nat) N::nat. ALL n::nat. <= N n --> <= n (A * dest_nadd x n))"
  by (import hollight NADD_LBOUND)

constdefs
  nadd_rinv :: "nadd => nat => nat" 
  "nadd_rinv == %(u::nadd) n::nat. DIV (n * n) (dest_nadd u n)"

lemma DEF_nadd_rinv: "nadd_rinv = (%(u::nadd) n::nat. DIV (n * n) (dest_nadd u n))"
  by (import hollight DEF_nadd_rinv)

lemma NADD_MUL_LINV_LEMMA0: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX (xa::nat) B::nat. ALL i::nat. <= (nadd_rinv x i) (xa * i + B))"
  by (import hollight NADD_MUL_LINV_LEMMA0)

lemma NADD_MUL_LINV_LEMMA1: "ALL (x::nadd) n::nat.
   dest_nadd x n ~= 0 -->
   <= (dist (dest_nadd x n * nadd_rinv x n, n * n)) (dest_nadd x n)"
  by (import hollight NADD_MUL_LINV_LEMMA1)

lemma NADD_MUL_LINV_LEMMA2: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX N::nat.
       ALL n::nat.
          <= N n -->
          <= (dist (dest_nadd x n * nadd_rinv x n, n * n)) (dest_nadd x n))"
  by (import hollight NADD_MUL_LINV_LEMMA2)

lemma NADD_MUL_LINV_LEMMA3: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX N::nat.
       ALL (m::nat) n::nat.
          <= N n -->
          <= (dist
               (m * (dest_nadd x m * (dest_nadd x n * nadd_rinv x n)),
                m * (dest_nadd x m * (n * n))))
           (m * (dest_nadd x m * dest_nadd x n)))"
  by (import hollight NADD_MUL_LINV_LEMMA3)

lemma NADD_MUL_LINV_LEMMA4: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX N::nat.
       ALL (m::nat) n::nat.
          <= N m & <= N n -->
          <= (dest_nadd x m * dest_nadd x n *
              dist (m * nadd_rinv x n, n * nadd_rinv x m))
           (m * n * dist (m * dest_nadd x n, n * dest_nadd x m) +
            dest_nadd x m * dest_nadd x n * (m + n)))"
  by (import hollight NADD_MUL_LINV_LEMMA4)

lemma NADD_MUL_LINV_LEMMA5: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX (B::nat) N::nat.
       ALL (m::nat) n::nat.
          <= N m & <= N n -->
          <= (dest_nadd x m * dest_nadd x n *
              dist (m * nadd_rinv x n, n * nadd_rinv x m))
           (B * (m * n * (m + n))))"
  by (import hollight NADD_MUL_LINV_LEMMA5)

lemma NADD_MUL_LINV_LEMMA6: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX (B::nat) N::nat.
       ALL (m::nat) n::nat.
          <= N m & <= N n -->
          <= (m * n * dist (m * nadd_rinv x n, n * nadd_rinv x m))
           (B * (m * n * (m + n))))"
  by (import hollight NADD_MUL_LINV_LEMMA6)

lemma NADD_MUL_LINV_LEMMA7: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX (B::nat) N::nat.
       ALL (m::nat) n::nat.
          <= N m & <= N n -->
          <= (dist (m * nadd_rinv x n, n * nadd_rinv x m)) (B * (m + n)))"
  by (import hollight NADD_MUL_LINV_LEMMA7)

lemma NADD_MUL_LINV_LEMMA7a: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (ALL N::nat.
       EX (A::nat) B::nat.
          ALL (m::nat) n::nat.
             <= m N -->
             <= (dist (m * nadd_rinv x n, n * nadd_rinv x m)) (A * n + B))"
  by (import hollight NADD_MUL_LINV_LEMMA7a)

lemma NADD_MUL_LINV_LEMMA8: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   (EX B::nat.
       ALL (m::nat) n::nat.
          <= (dist (m * nadd_rinv x n, n * nadd_rinv x m)) (B * (m + n)))"
  by (import hollight NADD_MUL_LINV_LEMMA8)

constdefs
  nadd_inv :: "nadd => nadd" 
  "nadd_inv ==
%u::nadd.
   COND (nadd_eq u (nadd_of_num 0)) (nadd_of_num 0) (mk_nadd (nadd_rinv u))"

lemma DEF_nadd_inv: "nadd_inv =
(%u::nadd.
    COND (nadd_eq u (nadd_of_num 0)) (nadd_of_num 0)
     (mk_nadd (nadd_rinv u)))"
  by (import hollight DEF_nadd_inv)

lemma NADD_INV: "ALL x::nadd.
   dest_nadd (nadd_inv x) =
   COND (nadd_eq x (nadd_of_num 0)) (%n::nat. 0) (nadd_rinv x)"
  by (import hollight NADD_INV)

lemma NADD_MUL_LINV: "ALL x::nadd.
   ~ nadd_eq x (nadd_of_num 0) -->
   nadd_eq (nadd_mul (nadd_inv x) x) (nadd_of_num (NUMERAL_BIT1 0))"
  by (import hollight NADD_MUL_LINV)

lemma NADD_INV_0: "nadd_eq (nadd_inv (nadd_of_num 0)) (nadd_of_num 0)"
  by (import hollight NADD_INV_0)

lemma NADD_INV_WELLDEF: "ALL (x::nadd) y::nadd. nadd_eq x y --> nadd_eq (nadd_inv x) (nadd_inv y)"
  by (import hollight NADD_INV_WELLDEF)

typedef (open) hreal = "{s::nadd => bool. EX x::nadd. s = nadd_eq x}"  morphisms "dest_hreal" "mk_hreal"
  apply (rule light_ex_imp_nonempty[where t="nadd_eq (x::nadd)"])
  by (import hollight TYDEF_hreal)

syntax
  dest_hreal :: _ 

syntax
  mk_hreal :: _ 

lemmas "TYDEF_hreal_@intern" = typedef_hol2hollight 
  [where a="a :: hreal" and r=r ,
   OF type_definition_hreal]

constdefs
  hreal_of_num :: "nat => hreal" 
  "hreal_of_num == %m::nat. mk_hreal (nadd_eq (nadd_of_num m))"

lemma DEF_hreal_of_num: "hreal_of_num = (%m::nat. mk_hreal (nadd_eq (nadd_of_num m)))"
  by (import hollight DEF_hreal_of_num)

constdefs
  hreal_add :: "hreal => hreal => hreal" 
  "hreal_add ==
%(x::hreal) y::hreal.
   mk_hreal
    (%u::nadd.
        EX (xa::nadd) ya::nadd.
           nadd_eq (nadd_add xa ya) u & dest_hreal x xa & dest_hreal y ya)"

lemma DEF_hreal_add: "hreal_add =
(%(x::hreal) y::hreal.
    mk_hreal
     (%u::nadd.
         EX (xa::nadd) ya::nadd.
            nadd_eq (nadd_add xa ya) u & dest_hreal x xa & dest_hreal y ya))"
  by (import hollight DEF_hreal_add)

constdefs
  hreal_mul :: "hreal => hreal => hreal" 
  "hreal_mul ==
%(x::hreal) y::hreal.
   mk_hreal
    (%u::nadd.
        EX (xa::nadd) ya::nadd.
           nadd_eq (nadd_mul xa ya) u & dest_hreal x xa & dest_hreal y ya)"

lemma DEF_hreal_mul: "hreal_mul =
(%(x::hreal) y::hreal.
    mk_hreal
     (%u::nadd.
         EX (xa::nadd) ya::nadd.
            nadd_eq (nadd_mul xa ya) u & dest_hreal x xa & dest_hreal y ya))"
  by (import hollight DEF_hreal_mul)

constdefs
  hreal_le :: "hreal => hreal => bool" 
  "hreal_le ==
%(x::hreal) y::hreal.
   SOME u::bool.
      EX (xa::nadd) ya::nadd.
         nadd_le xa ya = u & dest_hreal x xa & dest_hreal y ya"

lemma DEF_hreal_le: "hreal_le =
(%(x::hreal) y::hreal.
    SOME u::bool.
       EX (xa::nadd) ya::nadd.
          nadd_le xa ya = u & dest_hreal x xa & dest_hreal y ya)"
  by (import hollight DEF_hreal_le)

constdefs
  hreal_inv :: "hreal => hreal" 
  "hreal_inv ==
%x::hreal.
   mk_hreal
    (%u::nadd. EX xa::nadd. nadd_eq (nadd_inv xa) u & dest_hreal x xa)"

lemma DEF_hreal_inv: "hreal_inv =
(%x::hreal.
    mk_hreal
     (%u::nadd. EX xa::nadd. nadd_eq (nadd_inv xa) u & dest_hreal x xa))"
  by (import hollight DEF_hreal_inv)

lemma HREAL_LE_EXISTS_DEF: "ALL (m::hreal) n::hreal. hreal_le m n = (EX d::hreal. n = hreal_add m d)"
  by (import hollight HREAL_LE_EXISTS_DEF)

lemma HREAL_EQ_ADD_LCANCEL: "ALL (m::hreal) (n::hreal) p::hreal.
   (hreal_add m n = hreal_add m p) = (n = p)"
  by (import hollight HREAL_EQ_ADD_LCANCEL)

lemma HREAL_EQ_ADD_RCANCEL: "ALL (x::hreal) (xa::hreal) xb::hreal.
   (hreal_add x xb = hreal_add xa xb) = (x = xa)"
  by (import hollight HREAL_EQ_ADD_RCANCEL)

lemma HREAL_LE_ADD_LCANCEL: "ALL (x::hreal) (xa::hreal) xb::hreal.
   hreal_le (hreal_add x xa) (hreal_add x xb) = hreal_le xa xb"
  by (import hollight HREAL_LE_ADD_LCANCEL)

lemma HREAL_LE_ADD_RCANCEL: "ALL (x::hreal) (xa::hreal) xb::hreal.
   hreal_le (hreal_add x xb) (hreal_add xa xb) = hreal_le x xa"
  by (import hollight HREAL_LE_ADD_RCANCEL)

lemma HREAL_ADD_RID: "ALL x::hreal. hreal_add x (hreal_of_num 0) = x"
  by (import hollight HREAL_ADD_RID)

lemma HREAL_ADD_RDISTRIB: "ALL (x::hreal) (xa::hreal) xb::hreal.
   hreal_mul (hreal_add x xa) xb =
   hreal_add (hreal_mul x xb) (hreal_mul xa xb)"
  by (import hollight HREAL_ADD_RDISTRIB)

lemma HREAL_MUL_LZERO: "ALL m::hreal. hreal_mul (hreal_of_num 0) m = hreal_of_num 0"
  by (import hollight HREAL_MUL_LZERO)

lemma HREAL_MUL_RZERO: "ALL x::hreal. hreal_mul x (hreal_of_num 0) = hreal_of_num 0"
  by (import hollight HREAL_MUL_RZERO)

lemma HREAL_ADD_AC: "hreal_add (m::hreal) (n::hreal) = hreal_add n m &
hreal_add (hreal_add m n) (p::hreal) = hreal_add m (hreal_add n p) &
hreal_add m (hreal_add n p) = hreal_add n (hreal_add m p)"
  by (import hollight HREAL_ADD_AC)

lemma HREAL_LE_ADD2: "ALL (a::hreal) (b::hreal) (c::hreal) d::hreal.
   hreal_le a b & hreal_le c d --> hreal_le (hreal_add a c) (hreal_add b d)"
  by (import hollight HREAL_LE_ADD2)

lemma HREAL_LE_MUL_RCANCEL_IMP: "ALL (a::hreal) (b::hreal) c::hreal.
   hreal_le a b --> hreal_le (hreal_mul a c) (hreal_mul b c)"
  by (import hollight HREAL_LE_MUL_RCANCEL_IMP)

constdefs
  treal_of_num :: "nat => hreal * hreal" 
  "treal_of_num == %u::nat. (hreal_of_num u, hreal_of_num 0)"

lemma DEF_treal_of_num: "treal_of_num = (%u::nat. (hreal_of_num u, hreal_of_num 0))"
  by (import hollight DEF_treal_of_num)

constdefs
  treal_neg :: "hreal * hreal => hreal * hreal" 
  "treal_neg == %u::hreal * hreal. (snd u, fst u)"

lemma DEF_treal_neg: "treal_neg = (%u::hreal * hreal. (snd u, fst u))"
  by (import hollight DEF_treal_neg)

constdefs
  treal_add :: "hreal * hreal => hreal * hreal => hreal * hreal" 
  "treal_add ==
%(u::hreal * hreal) ua::hreal * hreal.
   (hreal_add (fst u) (fst ua), hreal_add (snd u) (snd ua))"

lemma DEF_treal_add: "treal_add =
(%(u::hreal * hreal) ua::hreal * hreal.
    (hreal_add (fst u) (fst ua), hreal_add (snd u) (snd ua)))"
  by (import hollight DEF_treal_add)

constdefs
  treal_mul :: "hreal * hreal => hreal * hreal => hreal * hreal" 
  "treal_mul ==
%(u::hreal * hreal) ua::hreal * hreal.
   (hreal_add (hreal_mul (fst u) (fst ua)) (hreal_mul (snd u) (snd ua)),
    hreal_add (hreal_mul (fst u) (snd ua)) (hreal_mul (snd u) (fst ua)))"

lemma DEF_treal_mul: "treal_mul =
(%(u::hreal * hreal) ua::hreal * hreal.
    (hreal_add (hreal_mul (fst u) (fst ua)) (hreal_mul (snd u) (snd ua)),
     hreal_add (hreal_mul (fst u) (snd ua)) (hreal_mul (snd u) (fst ua))))"
  by (import hollight DEF_treal_mul)

constdefs
  treal_le :: "hreal * hreal => hreal * hreal => bool" 
  "treal_le ==
%(u::hreal * hreal) ua::hreal * hreal.
   hreal_le (hreal_add (fst u) (snd ua)) (hreal_add (fst ua) (snd u))"

lemma DEF_treal_le: "treal_le =
(%(u::hreal * hreal) ua::hreal * hreal.
    hreal_le (hreal_add (fst u) (snd ua)) (hreal_add (fst ua) (snd u)))"
  by (import hollight DEF_treal_le)

constdefs
  treal_inv :: "hreal * hreal => hreal * hreal" 
  "treal_inv ==
%u::hreal * hreal.
   COND (fst u = snd u) (hreal_of_num 0, hreal_of_num 0)
    (COND (hreal_le (snd u) (fst u))
      (hreal_inv (SOME d::hreal. fst u = hreal_add (snd u) d),
       hreal_of_num 0)
      (hreal_of_num 0,
       hreal_inv (SOME d::hreal. snd u = hreal_add (fst u) d)))"

lemma DEF_treal_inv: "treal_inv =
(%u::hreal * hreal.
    COND (fst u = snd u) (hreal_of_num 0, hreal_of_num 0)
     (COND (hreal_le (snd u) (fst u))
       (hreal_inv (SOME d::hreal. fst u = hreal_add (snd u) d),
        hreal_of_num 0)
       (hreal_of_num 0,
        hreal_inv (SOME d::hreal. snd u = hreal_add (fst u) d))))"
  by (import hollight DEF_treal_inv)

constdefs
  treal_eq :: "hreal * hreal => hreal * hreal => bool" 
  "treal_eq ==
%(u::hreal * hreal) ua::hreal * hreal.
   hreal_add (fst u) (snd ua) = hreal_add (fst ua) (snd u)"

lemma DEF_treal_eq: "treal_eq =
(%(u::hreal * hreal) ua::hreal * hreal.
    hreal_add (fst u) (snd ua) = hreal_add (fst ua) (snd u))"
  by (import hollight DEF_treal_eq)

lemma TREAL_EQ_REFL: "ALL x::hreal * hreal. treal_eq x x"
  by (import hollight TREAL_EQ_REFL)

lemma TREAL_EQ_SYM: "ALL (x::hreal * hreal) y::hreal * hreal. treal_eq x y = treal_eq y x"
  by (import hollight TREAL_EQ_SYM)

lemma TREAL_EQ_TRANS: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_eq x y & treal_eq y z --> treal_eq x z"
  by (import hollight TREAL_EQ_TRANS)

lemma TREAL_EQ_AP: "ALL (x::hreal * hreal) y::hreal * hreal. x = y --> treal_eq x y"
  by (import hollight TREAL_EQ_AP)

lemma TREAL_OF_NUM_EQ: "ALL (x::nat) xa::nat. treal_eq (treal_of_num x) (treal_of_num xa) = (x = xa)"
  by (import hollight TREAL_OF_NUM_EQ)

lemma TREAL_OF_NUM_LE: "ALL (x::nat) xa::nat. treal_le (treal_of_num x) (treal_of_num xa) = <= x xa"
  by (import hollight TREAL_OF_NUM_LE)

lemma TREAL_OF_NUM_ADD: "ALL (x::nat) xa::nat.
   treal_eq (treal_add (treal_of_num x) (treal_of_num xa))
    (treal_of_num (x + xa))"
  by (import hollight TREAL_OF_NUM_ADD)

lemma TREAL_OF_NUM_MUL: "ALL (x::nat) xa::nat.
   treal_eq (treal_mul (treal_of_num x) (treal_of_num xa))
    (treal_of_num (x * xa))"
  by (import hollight TREAL_OF_NUM_MUL)

lemma TREAL_ADD_SYM_EQ: "ALL (x::hreal * hreal) y::hreal * hreal. treal_add x y = treal_add y x"
  by (import hollight TREAL_ADD_SYM_EQ)

lemma TREAL_MUL_SYM_EQ: "ALL (x::hreal * hreal) y::hreal * hreal. treal_mul x y = treal_mul y x"
  by (import hollight TREAL_MUL_SYM_EQ)

lemma TREAL_ADD_SYM: "ALL (x::hreal * hreal) y::hreal * hreal.
   treal_eq (treal_add x y) (treal_add y x)"
  by (import hollight TREAL_ADD_SYM)

lemma TREAL_ADD_ASSOC: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_eq (treal_add x (treal_add y z)) (treal_add (treal_add x y) z)"
  by (import hollight TREAL_ADD_ASSOC)

lemma TREAL_ADD_LID: "ALL x::hreal * hreal. treal_eq (treal_add (treal_of_num 0) x) x"
  by (import hollight TREAL_ADD_LID)

lemma TREAL_ADD_LINV: "ALL x::hreal * hreal. treal_eq (treal_add (treal_neg x) x) (treal_of_num 0)"
  by (import hollight TREAL_ADD_LINV)

lemma TREAL_MUL_SYM: "ALL (x::hreal * hreal) y::hreal * hreal.
   treal_eq (treal_mul x y) (treal_mul y x)"
  by (import hollight TREAL_MUL_SYM)

lemma TREAL_MUL_ASSOC: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_eq (treal_mul x (treal_mul y z)) (treal_mul (treal_mul x y) z)"
  by (import hollight TREAL_MUL_ASSOC)

lemma TREAL_MUL_LID: "ALL x::hreal * hreal.
   treal_eq (treal_mul (treal_of_num (NUMERAL_BIT1 0)) x) x"
  by (import hollight TREAL_MUL_LID)

lemma TREAL_ADD_LDISTRIB: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_eq (treal_mul x (treal_add y z))
    (treal_add (treal_mul x y) (treal_mul x z))"
  by (import hollight TREAL_ADD_LDISTRIB)

lemma TREAL_LE_REFL: "ALL x::hreal * hreal. treal_le x x"
  by (import hollight TREAL_LE_REFL)

lemma TREAL_LE_ANTISYM: "ALL (x::hreal * hreal) y::hreal * hreal.
   (treal_le x y & treal_le y x) = treal_eq x y"
  by (import hollight TREAL_LE_ANTISYM)

lemma TREAL_LE_TRANS: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_le x y & treal_le y z --> treal_le x z"
  by (import hollight TREAL_LE_TRANS)

lemma TREAL_LE_TOTAL: "ALL (x::hreal * hreal) y::hreal * hreal. treal_le x y | treal_le y x"
  by (import hollight TREAL_LE_TOTAL)

lemma TREAL_LE_LADD_IMP: "ALL (x::hreal * hreal) (y::hreal * hreal) z::hreal * hreal.
   treal_le y z --> treal_le (treal_add x y) (treal_add x z)"
  by (import hollight TREAL_LE_LADD_IMP)

lemma TREAL_LE_MUL: "ALL (x::hreal * hreal) y::hreal * hreal.
   treal_le (treal_of_num 0) x & treal_le (treal_of_num 0) y -->
   treal_le (treal_of_num 0) (treal_mul x y)"
  by (import hollight TREAL_LE_MUL)

lemma TREAL_INV_0: "treal_eq (treal_inv (treal_of_num 0)) (treal_of_num 0)"
  by (import hollight TREAL_INV_0)

lemma TREAL_MUL_LINV: "ALL x::hreal * hreal.
   ~ treal_eq x (treal_of_num 0) -->
   treal_eq (treal_mul (treal_inv x) x) (treal_of_num (NUMERAL_BIT1 0))"
  by (import hollight TREAL_MUL_LINV)

lemma TREAL_OF_NUM_WELLDEF: "ALL (m::nat) n::nat. m = n --> treal_eq (treal_of_num m) (treal_of_num n)"
  by (import hollight TREAL_OF_NUM_WELLDEF)

lemma TREAL_NEG_WELLDEF: "ALL (x1::hreal * hreal) x2::hreal * hreal.
   treal_eq x1 x2 --> treal_eq (treal_neg x1) (treal_neg x2)"
  by (import hollight TREAL_NEG_WELLDEF)

lemma TREAL_ADD_WELLDEFR: "ALL (x1::hreal * hreal) (x2::hreal * hreal) y::hreal * hreal.
   treal_eq x1 x2 --> treal_eq (treal_add x1 y) (treal_add x2 y)"
  by (import hollight TREAL_ADD_WELLDEFR)

lemma TREAL_ADD_WELLDEF: "ALL (x1::hreal * hreal) (x2::hreal * hreal) (y1::hreal * hreal)
   y2::hreal * hreal.
   treal_eq x1 x2 & treal_eq y1 y2 -->
   treal_eq (treal_add x1 y1) (treal_add x2 y2)"
  by (import hollight TREAL_ADD_WELLDEF)

lemma TREAL_MUL_WELLDEFR: "ALL (x1::hreal * hreal) (x2::hreal * hreal) y::hreal * hreal.
   treal_eq x1 x2 --> treal_eq (treal_mul x1 y) (treal_mul x2 y)"
  by (import hollight TREAL_MUL_WELLDEFR)

lemma TREAL_MUL_WELLDEF: "ALL (x1::hreal * hreal) (x2::hreal * hreal) (y1::hreal * hreal)
   y2::hreal * hreal.
   treal_eq x1 x2 & treal_eq y1 y2 -->
   treal_eq (treal_mul x1 y1) (treal_mul x2 y2)"
  by (import hollight TREAL_MUL_WELLDEF)

lemma TREAL_EQ_IMP_LE: "ALL (x::hreal * hreal) y::hreal * hreal. treal_eq x y --> treal_le x y"
  by (import hollight TREAL_EQ_IMP_LE)

lemma TREAL_LE_WELLDEF: "ALL (x1::hreal * hreal) (x2::hreal * hreal) (y1::hreal * hreal)
   y2::hreal * hreal.
   treal_eq x1 x2 & treal_eq y1 y2 --> treal_le x1 y1 = treal_le x2 y2"
  by (import hollight TREAL_LE_WELLDEF)

lemma TREAL_INV_WELLDEF: "ALL (x::hreal * hreal) y::hreal * hreal.
   treal_eq x y --> treal_eq (treal_inv x) (treal_inv y)"
  by (import hollight TREAL_INV_WELLDEF)

typedef (open) real = "{s::hreal * hreal => bool. EX x::hreal * hreal. s = treal_eq x}"  morphisms "dest_real" "mk_real"
  apply (rule light_ex_imp_nonempty[where t="treal_eq (x::hreal * hreal)"])
  by (import hollight TYDEF_real)

syntax
  dest_real :: _ 

syntax
  mk_real :: _ 

lemmas "TYDEF_real_@intern" = typedef_hol2hollight 
  [where a="a :: hollight.real" and r=r ,
   OF type_definition_real]

constdefs
  real_of_num :: "nat => hollight.real" 
  "real_of_num == %m::nat. mk_real (treal_eq (treal_of_num m))"

lemma DEF_real_of_num: "real_of_num = (%m::nat. mk_real (treal_eq (treal_of_num m)))"
  by (import hollight DEF_real_of_num)

constdefs
  real_neg :: "hollight.real => hollight.real" 
  "real_neg ==
%x1::hollight.real.
   mk_real
    (%u::hreal * hreal.
        EX x1a::hreal * hreal.
           treal_eq (treal_neg x1a) u & dest_real x1 x1a)"

lemma DEF_real_neg: "real_neg =
(%x1::hollight.real.
    mk_real
     (%u::hreal * hreal.
         EX x1a::hreal * hreal.
            treal_eq (treal_neg x1a) u & dest_real x1 x1a))"
  by (import hollight DEF_real_neg)

constdefs
  real_add :: "hollight.real => hollight.real => hollight.real" 
  "real_add ==
%(x1::hollight.real) y1::hollight.real.
   mk_real
    (%u::hreal * hreal.
        EX (x1a::hreal * hreal) y1a::hreal * hreal.
           treal_eq (treal_add x1a y1a) u &
           dest_real x1 x1a & dest_real y1 y1a)"

lemma DEF_real_add: "real_add =
(%(x1::hollight.real) y1::hollight.real.
    mk_real
     (%u::hreal * hreal.
         EX (x1a::hreal * hreal) y1a::hreal * hreal.
            treal_eq (treal_add x1a y1a) u &
            dest_real x1 x1a & dest_real y1 y1a))"
  by (import hollight DEF_real_add)

constdefs
  real_mul :: "hollight.real => hollight.real => hollight.real" 
  "real_mul ==
%(x1::hollight.real) y1::hollight.real.
   mk_real
    (%u::hreal * hreal.
        EX (x1a::hreal * hreal) y1a::hreal * hreal.
           treal_eq (treal_mul x1a y1a) u &
           dest_real x1 x1a & dest_real y1 y1a)"

lemma DEF_real_mul: "real_mul =
(%(x1::hollight.real) y1::hollight.real.
    mk_real
     (%u::hreal * hreal.
         EX (x1a::hreal * hreal) y1a::hreal * hreal.
            treal_eq (treal_mul x1a y1a) u &
            dest_real x1 x1a & dest_real y1 y1a))"
  by (import hollight DEF_real_mul)

constdefs
  real_le :: "hollight.real => hollight.real => bool" 
  "real_le ==
%(x1::hollight.real) y1::hollight.real.
   SOME u::bool.
      EX (x1a::hreal * hreal) y1a::hreal * hreal.
         treal_le x1a y1a = u & dest_real x1 x1a & dest_real y1 y1a"

lemma DEF_real_le: "real_le =
(%(x1::hollight.real) y1::hollight.real.
    SOME u::bool.
       EX (x1a::hreal * hreal) y1a::hreal * hreal.
          treal_le x1a y1a = u & dest_real x1 x1a & dest_real y1 y1a)"
  by (import hollight DEF_real_le)

constdefs
  real_inv :: "hollight.real => hollight.real" 
  "real_inv ==
%x::hollight.real.
   mk_real
    (%u::hreal * hreal.
        EX xa::hreal * hreal. treal_eq (treal_inv xa) u & dest_real x xa)"

lemma DEF_real_inv: "real_inv =
(%x::hollight.real.
    mk_real
     (%u::hreal * hreal.
         EX xa::hreal * hreal. treal_eq (treal_inv xa) u & dest_real x xa))"
  by (import hollight DEF_real_inv)

constdefs
  real_sub :: "hollight.real => hollight.real => hollight.real" 
  "real_sub == %(u::hollight.real) ua::hollight.real. real_add u (real_neg ua)"

lemma DEF_real_sub: "real_sub = (%(u::hollight.real) ua::hollight.real. real_add u (real_neg ua))"
  by (import hollight DEF_real_sub)

constdefs
  real_lt :: "hollight.real => hollight.real => bool" 
  "real_lt == %(u::hollight.real) ua::hollight.real. ~ real_le ua u"

lemma DEF_real_lt: "real_lt = (%(u::hollight.real) ua::hollight.real. ~ real_le ua u)"
  by (import hollight DEF_real_lt)

consts
  real_ge :: "hollight.real => hollight.real => bool" 

defs
  real_ge_def: "hollight.real_ge == %(u::hollight.real) ua::hollight.real. real_le ua u"

lemma DEF_real_ge: "hollight.real_ge = (%(u::hollight.real) ua::hollight.real. real_le ua u)"
  by (import hollight DEF_real_ge)

consts
  real_gt :: "hollight.real => hollight.real => bool" 

defs
  real_gt_def: "hollight.real_gt == %(u::hollight.real) ua::hollight.real. real_lt ua u"

lemma DEF_real_gt: "hollight.real_gt = (%(u::hollight.real) ua::hollight.real. real_lt ua u)"
  by (import hollight DEF_real_gt)

constdefs
  real_abs :: "hollight.real => hollight.real" 
  "real_abs ==
%u::hollight.real. COND (real_le (real_of_num 0) u) u (real_neg u)"

lemma DEF_real_abs: "real_abs =
(%u::hollight.real. COND (real_le (real_of_num 0) u) u (real_neg u))"
  by (import hollight DEF_real_abs)

constdefs
  real_pow :: "hollight.real => nat => hollight.real" 
  "real_pow ==
SOME real_pow::hollight.real => nat => hollight.real.
   (ALL x::hollight.real. real_pow x 0 = real_of_num (NUMERAL_BIT1 0)) &
   (ALL (x::hollight.real) n::nat.
       real_pow x (Suc n) = real_mul x (real_pow x n))"

lemma DEF_real_pow: "real_pow =
(SOME real_pow::hollight.real => nat => hollight.real.
    (ALL x::hollight.real. real_pow x 0 = real_of_num (NUMERAL_BIT1 0)) &
    (ALL (x::hollight.real) n::nat.
        real_pow x (Suc n) = real_mul x (real_pow x n)))"
  by (import hollight DEF_real_pow)

constdefs
  real_div :: "hollight.real => hollight.real => hollight.real" 
  "real_div == %(u::hollight.real) ua::hollight.real. real_mul u (real_inv ua)"

lemma DEF_real_div: "real_div = (%(u::hollight.real) ua::hollight.real. real_mul u (real_inv ua))"
  by (import hollight DEF_real_div)

constdefs
  real_max :: "hollight.real => hollight.real => hollight.real" 
  "real_max == %(u::hollight.real) ua::hollight.real. COND (real_le u ua) ua u"

lemma DEF_real_max: "real_max = (%(u::hollight.real) ua::hollight.real. COND (real_le u ua) ua u)"
  by (import hollight DEF_real_max)

constdefs
  real_min :: "hollight.real => hollight.real => hollight.real" 
  "real_min == %(u::hollight.real) ua::hollight.real. COND (real_le u ua) u ua"

lemma DEF_real_min: "real_min = (%(u::hollight.real) ua::hollight.real. COND (real_le u ua) u ua)"
  by (import hollight DEF_real_min)

lemma REAL_HREAL_LEMMA1: "EX x::hreal => hollight.real.
   (ALL xa::hollight.real.
       real_le (real_of_num 0) xa = (EX y::hreal. xa = x y)) &
   (ALL (y::hreal) z::hreal. hreal_le y z = real_le (x y) (x z))"
  by (import hollight REAL_HREAL_LEMMA1)

lemma REAL_HREAL_LEMMA2: "EX (x::hollight.real => hreal) r::hreal => hollight.real.
   (ALL xa::hreal. x (r xa) = xa) &
   (ALL xa::hollight.real. real_le (real_of_num 0) xa --> r (x xa) = xa) &
   (ALL x::hreal. real_le (real_of_num 0) (r x)) &
   (ALL (x::hreal) y::hreal. hreal_le x y = real_le (r x) (r y))"
  by (import hollight REAL_HREAL_LEMMA2)

lemma REAL_COMPLETE_SOMEPOS: "ALL P::hollight.real => bool.
   (EX x::hollight.real. P x & real_le (real_of_num 0) x) &
   (EX M::hollight.real. ALL x::hollight.real. P x --> real_le x M) -->
   (EX M::hollight.real.
       (ALL x::hollight.real. P x --> real_le x M) &
       (ALL M'::hollight.real.
           (ALL x::hollight.real. P x --> real_le x M') --> real_le M M'))"
  by (import hollight REAL_COMPLETE_SOMEPOS)

lemma REAL_COMPLETE: "ALL P::hollight.real => bool.
   Ex P &
   (EX M::hollight.real. ALL x::hollight.real. P x --> real_le x M) -->
   (EX M::hollight.real.
       (ALL x::hollight.real. P x --> real_le x M) &
       (ALL M'::hollight.real.
           (ALL x::hollight.real. P x --> real_le x M') --> real_le M M'))"
  by (import hollight REAL_COMPLETE)

lemma REAL_ADD_AC: "real_add (m::hollight.real) (n::hollight.real) = real_add n m &
real_add (real_add m n) (p::hollight.real) = real_add m (real_add n p) &
real_add m (real_add n p) = real_add n (real_add m p)"
  by (import hollight REAL_ADD_AC)

lemma REAL_ADD_RINV: "ALL x::hollight.real. real_add x (real_neg x) = real_of_num 0"
  by (import hollight REAL_ADD_RINV)

lemma REAL_EQ_ADD_LCANCEL: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (real_add x y = real_add x z) = (y = z)"
  by (import hollight REAL_EQ_ADD_LCANCEL)

lemma REAL_EQ_ADD_RCANCEL: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (real_add x z = real_add y z) = (x = y)"
  by (import hollight REAL_EQ_ADD_RCANCEL)

lemma REAL_NEG_NEG: "ALL x::hollight.real. real_neg (real_neg x) = x"
  by (import hollight REAL_NEG_NEG)

lemma REAL_MUL_RNEG: "ALL (x::hollight.real) y::hollight.real.
   real_mul x (real_neg y) = real_neg (real_mul x y)"
  by (import hollight REAL_MUL_RNEG)

lemma REAL_MUL_LNEG: "ALL (x::hollight.real) y::hollight.real.
   real_mul (real_neg x) y = real_neg (real_mul x y)"
  by (import hollight REAL_MUL_LNEG)

lemma REAL_ADD_RID: "ALL x::hollight.real. real_add x (real_of_num 0) = x"
  by (import hollight REAL_ADD_RID)

lemma REAL_LE_LNEG: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_neg x) y = real_le (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LE_LNEG)

lemma REAL_LE_NEG2: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_neg x) (real_neg y) = real_le y x"
  by (import hollight REAL_LE_NEG2)

lemma REAL_LE_RNEG: "ALL (x::hollight.real) y::hollight.real.
   real_le x (real_neg y) = real_le (real_add x y) (real_of_num 0)"
  by (import hollight REAL_LE_RNEG)

lemma REAL_OF_NUM_POW: "ALL (x::nat) n::nat. real_pow (real_of_num x) n = real_of_num (EXP x n)"
  by (import hollight REAL_OF_NUM_POW)

lemma REAL_POW_NEG: "ALL (x::hollight.real) n::nat.
   real_pow (real_neg x) n =
   COND (EVEN n) (real_pow x n) (real_neg (real_pow x n))"
  by (import hollight REAL_POW_NEG)

lemma REAL_ABS_NUM: "ALL x::nat. real_abs (real_of_num x) = real_of_num x"
  by (import hollight REAL_ABS_NUM)

lemma REAL_ABS_NEG: "ALL x::hollight.real. real_abs (real_neg x) = real_abs x"
  by (import hollight REAL_ABS_NEG)

lemma REAL_LTE_TOTAL: "ALL (x::hollight.real) xa::hollight.real. real_lt x xa | real_le xa x"
  by (import hollight REAL_LTE_TOTAL)

lemma REAL_LET_TOTAL: "ALL (x::hollight.real) xa::hollight.real. real_le x xa | real_lt xa x"
  by (import hollight REAL_LET_TOTAL)

lemma REAL_LET_TRANS: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le x y & real_lt y z --> real_lt x z"
  by (import hollight REAL_LET_TRANS)

lemma REAL_LT_TRANS: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt x y & real_lt y z --> real_lt x z"
  by (import hollight REAL_LT_TRANS)

lemma REAL_LE_ADD: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) y -->
   real_le (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LE_ADD)

lemma REAL_LTE_ANTISYM: "ALL (x::hollight.real) y::hollight.real. ~ (real_lt x y & real_le y x)"
  by (import hollight REAL_LTE_ANTISYM)

lemma REAL_LT_REFL: "ALL x::hollight.real. ~ real_lt x x"
  by (import hollight REAL_LT_REFL)

lemma REAL_LET_ADD: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_lt (real_of_num 0) y -->
   real_lt (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LET_ADD)

lemma REAL_ENTIRE: "ALL (x::hollight.real) y::hollight.real.
   (real_mul x y = real_of_num 0) = (x = real_of_num 0 | y = real_of_num 0)"
  by (import hollight REAL_ENTIRE)

lemma REAL_POW_2: "ALL x::hollight.real.
   real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)) = real_mul x x"
  by (import hollight REAL_POW_2)

lemma REAL_POLY_CLAUSES: "(ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
    real_add x (real_add y z) = real_add (real_add x y) z) &
(ALL (x::hollight.real) y::hollight.real. real_add x y = real_add y x) &
(ALL x::hollight.real. real_add (real_of_num 0) x = x) &
(ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
    real_mul x (real_mul y z) = real_mul (real_mul x y) z) &
(ALL (x::hollight.real) y::hollight.real. real_mul x y = real_mul y x) &
(ALL x::hollight.real. real_mul (real_of_num (NUMERAL_BIT1 0)) x = x) &
(ALL x::hollight.real. real_mul (real_of_num 0) x = real_of_num 0) &
(ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
    real_mul x (real_add xa xb) =
    real_add (real_mul x xa) (real_mul x xb)) &
(ALL x::hollight.real. real_pow x 0 = real_of_num (NUMERAL_BIT1 0)) &
(ALL (x::hollight.real) xa::nat.
    real_pow x (Suc xa) = real_mul x (real_pow x xa))"
  by (import hollight REAL_POLY_CLAUSES)

lemma REAL_POLY_NEG_CLAUSES: "(ALL x::hollight.real.
    real_neg x = real_mul (real_neg (real_of_num (NUMERAL_BIT1 0))) x) &
(ALL (x::hollight.real) xa::hollight.real.
    real_sub x xa =
    real_add x (real_mul (real_neg (real_of_num (NUMERAL_BIT1 0))) xa))"
  by (import hollight REAL_POLY_NEG_CLAUSES)

lemma REAL_OF_NUM_LT: "ALL (x::nat) xa::nat. real_lt (real_of_num x) (real_of_num xa) = < x xa"
  by (import hollight REAL_OF_NUM_LT)

lemma REAL_OF_NUM_GE: "ALL (x::nat) xa::nat.
   hollight.real_ge (real_of_num x) (real_of_num xa) = >= x xa"
  by (import hollight REAL_OF_NUM_GE)

lemma REAL_OF_NUM_GT: "ALL (x::nat) xa::nat.
   hollight.real_gt (real_of_num x) (real_of_num xa) = > x xa"
  by (import hollight REAL_OF_NUM_GT)

lemma REAL_OF_NUM_SUC: "ALL x::nat.
   real_add (real_of_num x) (real_of_num (NUMERAL_BIT1 0)) =
   real_of_num (Suc x)"
  by (import hollight REAL_OF_NUM_SUC)

lemma REAL_OF_NUM_SUB: "ALL (m::nat) n::nat.
   <= m n --> real_sub (real_of_num n) (real_of_num m) = real_of_num (n - m)"
  by (import hollight REAL_OF_NUM_SUB)

lemma REAL_MUL_AC: "real_mul (m::hollight.real) (n::hollight.real) = real_mul n m &
real_mul (real_mul m n) (p::hollight.real) = real_mul m (real_mul n p) &
real_mul m (real_mul n p) = real_mul n (real_mul m p)"
  by (import hollight REAL_MUL_AC)

lemma REAL_ADD_RDISTRIB: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_mul (real_add x y) z = real_add (real_mul x z) (real_mul y z)"
  by (import hollight REAL_ADD_RDISTRIB)

lemma REAL_LT_LADD_IMP: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt y z --> real_lt (real_add x y) (real_add x z)"
  by (import hollight REAL_LT_LADD_IMP)

lemma REAL_LT_MUL: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_lt (real_of_num 0) y -->
   real_lt (real_of_num 0) (real_mul x y)"
  by (import hollight REAL_LT_MUL)

lemma REAL_EQ_ADD_LCANCEL_0: "ALL (x::hollight.real) y::hollight.real.
   (real_add x y = x) = (y = real_of_num 0)"
  by (import hollight REAL_EQ_ADD_LCANCEL_0)

lemma REAL_EQ_ADD_RCANCEL_0: "ALL (x::hollight.real) y::hollight.real.
   (real_add x y = y) = (x = real_of_num 0)"
  by (import hollight REAL_EQ_ADD_RCANCEL_0)

lemma REAL_NOT_EQ: "ALL (x::hollight.real) y::hollight.real.
   (x ~= y) = (real_lt x y | real_lt y x)"
  by (import hollight REAL_NOT_EQ)

lemma REAL_LE_ANTISYM: "ALL (x::hollight.real) y::hollight.real.
   (real_le x y & real_le y x) = (x = y)"
  by (import hollight REAL_LE_ANTISYM)

lemma REAL_LET_ANTISYM: "ALL (x::hollight.real) y::hollight.real. ~ (real_le x y & real_lt y x)"
  by (import hollight REAL_LET_ANTISYM)

lemma REAL_LT_TOTAL: "ALL (x::hollight.real) y::hollight.real. x = y | real_lt x y | real_lt y x"
  by (import hollight REAL_LT_TOTAL)

lemma REAL_LE_01: "real_le (real_of_num 0) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight REAL_LE_01)

lemma REAL_LE_ADD2: "ALL (w::hollight.real) (x::hollight.real) (y::hollight.real)
   z::hollight.real.
   real_le w x & real_le y z --> real_le (real_add w y) (real_add x z)"
  by (import hollight REAL_LE_ADD2)

lemma REAL_LT_LNEG: "ALL (x::hollight.real) xa::hollight.real.
   real_lt (real_neg x) xa = real_lt (real_of_num 0) (real_add x xa)"
  by (import hollight REAL_LT_LNEG)

lemma REAL_LT_RNEG: "ALL (x::hollight.real) xa::hollight.real.
   real_lt x (real_neg xa) = real_lt (real_add x xa) (real_of_num 0)"
  by (import hollight REAL_LT_RNEG)

lemma REAL_NEG_EQ_0: "ALL x::hollight.real. (real_neg x = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight REAL_NEG_EQ_0)

lemma REAL_ADD_SUB: "ALL (x::hollight.real) y::hollight.real. real_sub (real_add x y) x = y"
  by (import hollight REAL_ADD_SUB)

lemma REAL_LE_ADDR: "ALL (x::hollight.real) y::hollight.real.
   real_le x (real_add x y) = real_le (real_of_num 0) y"
  by (import hollight REAL_LE_ADDR)

lemma REAL_LE_ADDL: "ALL (x::hollight.real) y::hollight.real.
   real_le y (real_add x y) = real_le (real_of_num 0) x"
  by (import hollight REAL_LE_ADDL)

lemma REAL_LT_ADDR: "ALL (x::hollight.real) y::hollight.real.
   real_lt x (real_add x y) = real_lt (real_of_num 0) y"
  by (import hollight REAL_LT_ADDR)

lemma REAL_LT_ADDL: "ALL (x::hollight.real) y::hollight.real.
   real_lt y (real_add x y) = real_lt (real_of_num 0) x"
  by (import hollight REAL_LT_ADDL)

lemma REAL_ADD2_SUB2: "ALL (a::hollight.real) (b::hollight.real) (c::hollight.real)
   d::hollight.real.
   real_sub (real_add a b) (real_add c d) =
   real_add (real_sub a c) (real_sub b d)"
  by (import hollight REAL_ADD2_SUB2)

lemma REAL_LET_ADD2: "ALL (w::hollight.real) (x::hollight.real) (y::hollight.real)
   z::hollight.real.
   real_le w x & real_lt y z --> real_lt (real_add w y) (real_add x z)"
  by (import hollight REAL_LET_ADD2)

lemma REAL_EQ_SUB_LADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (x = real_sub y z) = (real_add x z = y)"
  by (import hollight REAL_EQ_SUB_LADD)

lemma REAL_EQ_SUB_RADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (real_sub x y = z) = (x = real_add z y)"
  by (import hollight REAL_EQ_SUB_RADD)

lemma REAL_ADD_SUB2: "ALL (x::hollight.real) y::hollight.real.
   real_sub x (real_add x y) = real_neg y"
  by (import hollight REAL_ADD_SUB2)

lemma REAL_EQ_IMP_LE: "ALL (x::hollight.real) y::hollight.real. x = y --> real_le x y"
  by (import hollight REAL_EQ_IMP_LE)

lemma REAL_DIFFSQ: "ALL (x::hollight.real) y::hollight.real.
   real_mul (real_add x y) (real_sub x y) =
   real_sub (real_mul x x) (real_mul y y)"
  by (import hollight REAL_DIFFSQ)

lemma REAL_EQ_NEG2: "ALL (x::hollight.real) y::hollight.real. (real_neg x = real_neg y) = (x = y)"
  by (import hollight REAL_EQ_NEG2)

lemma REAL_LT_NEG2: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_neg x) (real_neg y) = real_lt y x"
  by (import hollight REAL_LT_NEG2)

lemma REAL_ABS_ZERO: "ALL x::hollight.real. (real_abs x = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight REAL_ABS_ZERO)

lemma REAL_ABS_0: "real_abs (real_of_num 0) = real_of_num 0"
  by (import hollight REAL_ABS_0)

lemma REAL_ABS_1: "real_abs (real_of_num (NUMERAL_BIT1 0)) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight REAL_ABS_1)

lemma REAL_ABS_TRIANGLE: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_abs (real_add x y)) (real_add (real_abs x) (real_abs y))"
  by (import hollight REAL_ABS_TRIANGLE)

lemma REAL_ABS_TRIANGLE_LE: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le (real_add (real_abs x) (real_abs (real_sub y x))) z -->
   real_le (real_abs y) z"
  by (import hollight REAL_ABS_TRIANGLE_LE)

lemma REAL_ABS_TRIANGLE_LT: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_add (real_abs x) (real_abs (real_sub y x))) z -->
   real_lt (real_abs y) z"
  by (import hollight REAL_ABS_TRIANGLE_LT)

lemma REAL_ABS_POS: "ALL x::hollight.real. real_le (real_of_num 0) (real_abs x)"
  by (import hollight REAL_ABS_POS)

lemma REAL_ABS_SUB: "ALL (x::hollight.real) y::hollight.real.
   real_abs (real_sub x y) = real_abs (real_sub y x)"
  by (import hollight REAL_ABS_SUB)

lemma REAL_ABS_NZ: "ALL x::hollight.real.
   (x ~= real_of_num 0) = real_lt (real_of_num 0) (real_abs x)"
  by (import hollight REAL_ABS_NZ)

lemma REAL_ABS_ABS: "ALL x::hollight.real. real_abs (real_abs x) = real_abs x"
  by (import hollight REAL_ABS_ABS)

lemma REAL_ABS_LE: "ALL x::hollight.real. real_le x (real_abs x)"
  by (import hollight REAL_ABS_LE)

lemma REAL_ABS_REFL: "ALL x::hollight.real. (real_abs x = x) = real_le (real_of_num 0) x"
  by (import hollight REAL_ABS_REFL)

lemma REAL_ABS_BETWEEN: "ALL (x::hollight.real) (y::hollight.real) d::hollight.real.
   (real_lt (real_of_num 0) d &
    real_lt (real_sub x d) y & real_lt y (real_add x d)) =
   real_lt (real_abs (real_sub y x)) d"
  by (import hollight REAL_ABS_BETWEEN)

lemma REAL_ABS_BOUND: "ALL (x::hollight.real) (y::hollight.real) d::hollight.real.
   real_lt (real_abs (real_sub x y)) d --> real_lt y (real_add x d)"
  by (import hollight REAL_ABS_BOUND)

lemma REAL_ABS_STILLNZ: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_abs (real_sub x y)) (real_abs y) --> x ~= real_of_num 0"
  by (import hollight REAL_ABS_STILLNZ)

lemma REAL_ABS_CASES: "ALL x::hollight.real.
   x = real_of_num 0 | real_lt (real_of_num 0) (real_abs x)"
  by (import hollight REAL_ABS_CASES)

lemma REAL_ABS_BETWEEN1: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt x z & real_lt (real_abs (real_sub y x)) (real_sub z x) -->
   real_lt y z"
  by (import hollight REAL_ABS_BETWEEN1)

lemma REAL_ABS_SIGN: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_abs (real_sub x y)) y --> real_lt (real_of_num 0) x"
  by (import hollight REAL_ABS_SIGN)

lemma REAL_ABS_SIGN2: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_abs (real_sub x y)) (real_neg y) -->
   real_lt x (real_of_num 0)"
  by (import hollight REAL_ABS_SIGN2)

lemma REAL_ABS_CIRCLE: "ALL (x::hollight.real) (y::hollight.real) h::hollight.real.
   real_lt (real_abs h) (real_sub (real_abs y) (real_abs x)) -->
   real_lt (real_abs (real_add x h)) (real_abs y)"
  by (import hollight REAL_ABS_CIRCLE)

lemma REAL_ABS_SUB_ABS: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_abs (real_sub (real_abs x) (real_abs y)))
    (real_abs (real_sub x y))"
  by (import hollight REAL_ABS_SUB_ABS)

lemma REAL_ABS_BETWEEN2: "ALL (x0::hollight.real) (x::hollight.real) (y0::hollight.real)
   y::hollight.real.
   real_lt x0 y0 &
   real_lt
    (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
      (real_abs (real_sub x x0)))
    (real_sub y0 x0) &
   real_lt
    (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
      (real_abs (real_sub y y0)))
    (real_sub y0 x0) -->
   real_lt x y"
  by (import hollight REAL_ABS_BETWEEN2)

lemma REAL_ABS_BOUNDS: "ALL (x::hollight.real) k::hollight.real.
   real_le (real_abs x) k = (real_le (real_neg k) x & real_le x k)"
  by (import hollight REAL_ABS_BOUNDS)

lemma REAL_MIN_MAX: "ALL (x::hollight.real) y::hollight.real.
   real_min x y = real_neg (real_max (real_neg x) (real_neg y))"
  by (import hollight REAL_MIN_MAX)

lemma REAL_MAX_MIN: "ALL (x::hollight.real) y::hollight.real.
   real_max x y = real_neg (real_min (real_neg x) (real_neg y))"
  by (import hollight REAL_MAX_MIN)

lemma REAL_MAX_MAX: "ALL (x::hollight.real) y::hollight.real.
   real_le x (real_max x y) & real_le y (real_max x y)"
  by (import hollight REAL_MAX_MAX)

lemma REAL_MIN_MIN: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_min x y) x & real_le (real_min x y) y"
  by (import hollight REAL_MIN_MIN)

lemma REAL_MAX_SYM: "ALL (x::hollight.real) y::hollight.real. real_max x y = real_max y x"
  by (import hollight REAL_MAX_SYM)

lemma REAL_MIN_SYM: "ALL (x::hollight.real) y::hollight.real. real_min x y = real_min y x"
  by (import hollight REAL_MIN_SYM)

lemma REAL_LE_MAX: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le z (real_max x y) = (real_le z x | real_le z y)"
  by (import hollight REAL_LE_MAX)

lemma REAL_LE_MIN: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le z (real_min x y) = (real_le z x & real_le z y)"
  by (import hollight REAL_LE_MIN)

lemma REAL_LT_MAX: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt z (real_max x y) = (real_lt z x | real_lt z y)"
  by (import hollight REAL_LT_MAX)

lemma REAL_LT_MIN: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt z (real_min x y) = (real_lt z x & real_lt z y)"
  by (import hollight REAL_LT_MIN)

lemma REAL_MAX_LE: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le (real_max x y) z = (real_le x z & real_le y z)"
  by (import hollight REAL_MAX_LE)

lemma REAL_MIN_LE: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le (real_min x y) z = (real_le x z | real_le y z)"
  by (import hollight REAL_MIN_LE)

lemma REAL_MAX_LT: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_max x y) z = (real_lt x z & real_lt y z)"
  by (import hollight REAL_MAX_LT)

lemma REAL_MIN_LT: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_min x y) z = (real_lt x z | real_lt y z)"
  by (import hollight REAL_MIN_LT)

lemma REAL_MAX_ASSOC: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_max x (real_max y z) = real_max (real_max x y) z"
  by (import hollight REAL_MAX_ASSOC)

lemma REAL_MIN_ASSOC: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_min x (real_min y z) = real_min (real_min x y) z"
  by (import hollight REAL_MIN_ASSOC)

lemma REAL_MAX_ACI: "real_max (x::hollight.real) (y::hollight.real) = real_max y x &
real_max (real_max x y) (z::hollight.real) = real_max x (real_max y z) &
real_max x (real_max y z) = real_max y (real_max x z) &
real_max x x = x & real_max x (real_max x y) = real_max x y"
  by (import hollight REAL_MAX_ACI)

lemma REAL_MIN_ACI: "real_min (x::hollight.real) (y::hollight.real) = real_min y x &
real_min (real_min x y) (z::hollight.real) = real_min x (real_min y z) &
real_min x (real_min y z) = real_min y (real_min x z) &
real_min x x = x & real_min x (real_min x y) = real_min x y"
  by (import hollight REAL_MIN_ACI)

lemma REAL_ABS_MUL: "ALL (x::hollight.real) y::hollight.real.
   real_abs (real_mul x y) = real_mul (real_abs x) (real_abs y)"
  by (import hollight REAL_ABS_MUL)

lemma REAL_POW_LE: "ALL (x::hollight.real) n::nat.
   real_le (real_of_num 0) x --> real_le (real_of_num 0) (real_pow x n)"
  by (import hollight REAL_POW_LE)

lemma REAL_POW_LT: "ALL (x::hollight.real) n::nat.
   real_lt (real_of_num 0) x --> real_lt (real_of_num 0) (real_pow x n)"
  by (import hollight REAL_POW_LT)

lemma REAL_ABS_POW: "ALL (x::hollight.real) n::nat.
   real_abs (real_pow x n) = real_pow (real_abs x) n"
  by (import hollight REAL_ABS_POW)

lemma REAL_LE_LMUL: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_le (real_of_num 0) x & real_le xa xb -->
   real_le (real_mul x xa) (real_mul x xb)"
  by (import hollight REAL_LE_LMUL)

lemma REAL_LE_RMUL: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le x y & real_le (real_of_num 0) z -->
   real_le (real_mul x z) (real_mul y z)"
  by (import hollight REAL_LE_RMUL)

lemma REAL_LT_LMUL: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) x & real_lt xa xb -->
   real_lt (real_mul x xa) (real_mul x xb)"
  by (import hollight REAL_LT_LMUL)

lemma REAL_LT_RMUL: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt x y & real_lt (real_of_num 0) z -->
   real_lt (real_mul x z) (real_mul y z)"
  by (import hollight REAL_LT_RMUL)

lemma REAL_EQ_MUL_LCANCEL: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (real_mul x y = real_mul x z) = (x = real_of_num 0 | y = z)"
  by (import hollight REAL_EQ_MUL_LCANCEL)

lemma REAL_EQ_MUL_RCANCEL: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   (real_mul x xb = real_mul xa xb) = (x = xa | xb = real_of_num 0)"
  by (import hollight REAL_EQ_MUL_RCANCEL)

lemma REAL_MUL_LINV_UNIQ: "ALL (x::hollight.real) y::hollight.real.
   real_mul x y = real_of_num (NUMERAL_BIT1 0) --> real_inv y = x"
  by (import hollight REAL_MUL_LINV_UNIQ)

lemma REAL_MUL_RINV_UNIQ: "ALL (x::hollight.real) xa::hollight.real.
   real_mul x xa = real_of_num (NUMERAL_BIT1 0) --> real_inv x = xa"
  by (import hollight REAL_MUL_RINV_UNIQ)

lemma REAL_INV_INV: "ALL x::hollight.real. real_inv (real_inv x) = x"
  by (import hollight REAL_INV_INV)

lemma REAL_INV_EQ_0: "ALL x::hollight.real. (real_inv x = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight REAL_INV_EQ_0)

lemma REAL_LT_INV: "ALL x::hollight.real.
   real_lt (real_of_num 0) x --> real_lt (real_of_num 0) (real_inv x)"
  by (import hollight REAL_LT_INV)

lemma REAL_LT_INV_EQ: "ALL x::hollight.real.
   real_lt (real_of_num 0) (real_inv x) = real_lt (real_of_num 0) x"
  by (import hollight REAL_LT_INV_EQ)

lemma REAL_INV_NEG: "ALL x::hollight.real. real_inv (real_neg x) = real_neg (real_inv x)"
  by (import hollight REAL_INV_NEG)

lemma REAL_LE_INV_EQ: "ALL x::hollight.real.
   real_le (real_of_num 0) (real_inv x) = real_le (real_of_num 0) x"
  by (import hollight REAL_LE_INV_EQ)

lemma REAL_LE_INV: "ALL x::hollight.real.
   real_le (real_of_num 0) x --> real_le (real_of_num 0) (real_inv x)"
  by (import hollight REAL_LE_INV)

lemma REAL_INV_1: "real_inv (real_of_num (NUMERAL_BIT1 0)) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight REAL_INV_1)

lemma REAL_DIV_1: "ALL x::hollight.real. real_div x (real_of_num (NUMERAL_BIT1 0)) = x"
  by (import hollight REAL_DIV_1)

lemma REAL_DIV_REFL: "ALL x::hollight.real.
   x ~= real_of_num 0 --> real_div x x = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight REAL_DIV_REFL)

lemma REAL_DIV_RMUL: "ALL (x::hollight.real) xa::hollight.real.
   xa ~= real_of_num 0 --> real_mul (real_div x xa) xa = x"
  by (import hollight REAL_DIV_RMUL)

lemma REAL_DIV_LMUL: "ALL (x::hollight.real) xa::hollight.real.
   xa ~= real_of_num 0 --> real_mul xa (real_div x xa) = x"
  by (import hollight REAL_DIV_LMUL)

lemma REAL_ABS_INV: "ALL x::hollight.real. real_abs (real_inv x) = real_inv (real_abs x)"
  by (import hollight REAL_ABS_INV)

lemma REAL_ABS_DIV: "ALL (x::hollight.real) xa::hollight.real.
   real_abs (real_div x xa) = real_div (real_abs x) (real_abs xa)"
  by (import hollight REAL_ABS_DIV)

lemma REAL_INV_MUL: "ALL (x::hollight.real) y::hollight.real.
   real_inv (real_mul x y) = real_mul (real_inv x) (real_inv y)"
  by (import hollight REAL_INV_MUL)

lemma REAL_INV_DIV: "ALL (x::hollight.real) xa::hollight.real.
   real_inv (real_div x xa) = real_div xa x"
  by (import hollight REAL_INV_DIV)

lemma REAL_POW_MUL: "ALL (x::hollight.real) (y::hollight.real) n::nat.
   real_pow (real_mul x y) n = real_mul (real_pow x n) (real_pow y n)"
  by (import hollight REAL_POW_MUL)

lemma REAL_POW_INV: "ALL (x::hollight.real) n::nat.
   real_pow (real_inv x) n = real_inv (real_pow x n)"
  by (import hollight REAL_POW_INV)

lemma REAL_POW_DIV: "ALL (x::hollight.real) (xa::hollight.real) xb::nat.
   real_pow (real_div x xa) xb = real_div (real_pow x xb) (real_pow xa xb)"
  by (import hollight REAL_POW_DIV)

lemma REAL_POW_ADD: "ALL (x::hollight.real) (m::nat) n::nat.
   real_pow x (m + n) = real_mul (real_pow x m) (real_pow x n)"
  by (import hollight REAL_POW_ADD)

lemma REAL_POW_NZ: "ALL (x::hollight.real) n::nat.
   x ~= real_of_num 0 --> real_pow x n ~= real_of_num 0"
  by (import hollight REAL_POW_NZ)

lemma REAL_POW_SUB: "ALL (x::hollight.real) (m::nat) n::nat.
   x ~= real_of_num 0 & <= m n -->
   real_pow x (n - m) = real_div (real_pow x n) (real_pow x m)"
  by (import hollight REAL_POW_SUB)

lemma REAL_LT_IMP_NZ: "ALL x::hollight.real. real_lt (real_of_num 0) x --> x ~= real_of_num 0"
  by (import hollight REAL_LT_IMP_NZ)

lemma REAL_LT_LCANCEL_IMP: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) x & real_lt (real_mul x y) (real_mul x z) -->
   real_lt y z"
  by (import hollight REAL_LT_LCANCEL_IMP)

lemma REAL_LT_RCANCEL_IMP: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) xb & real_lt (real_mul x xb) (real_mul xa xb) -->
   real_lt x xa"
  by (import hollight REAL_LT_RCANCEL_IMP)

lemma REAL_LE_LCANCEL_IMP: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) x & real_le (real_mul x y) (real_mul x z) -->
   real_le y z"
  by (import hollight REAL_LE_LCANCEL_IMP)

lemma REAL_LE_RCANCEL_IMP: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) xb & real_le (real_mul x xb) (real_mul xa xb) -->
   real_le x xa"
  by (import hollight REAL_LE_RCANCEL_IMP)

lemma REAL_LE_LMUL_EQ: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) z -->
   real_le (real_mul z x) (real_mul z y) = real_le x y"
  by (import hollight REAL_LE_LMUL_EQ)

lemma REAL_LE_RDIV_EQ: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) z -->
   real_le x (real_div y z) = real_le (real_mul x z) y"
  by (import hollight REAL_LE_RDIV_EQ)

lemma REAL_LE_LDIV_EQ: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) z -->
   real_le (real_div x z) y = real_le x (real_mul y z)"
  by (import hollight REAL_LE_LDIV_EQ)

lemma REAL_LT_RDIV_EQ: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) xb -->
   real_lt x (real_div xa xb) = real_lt (real_mul x xb) xa"
  by (import hollight REAL_LT_RDIV_EQ)

lemma REAL_LT_LDIV_EQ: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) xb -->
   real_lt (real_div x xb) xa = real_lt x (real_mul xa xb)"
  by (import hollight REAL_LT_LDIV_EQ)

lemma REAL_EQ_RDIV_EQ: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) xb -->
   (x = real_div xa xb) = (real_mul x xb = xa)"
  by (import hollight REAL_EQ_RDIV_EQ)

lemma REAL_EQ_LDIV_EQ: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) xb -->
   (real_div x xb = xa) = (x = real_mul xa xb)"
  by (import hollight REAL_EQ_LDIV_EQ)

lemma REAL_LT_DIV2_EQ: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) xb -->
   real_lt (real_div x xb) (real_div xa xb) = real_lt x xa"
  by (import hollight REAL_LT_DIV2_EQ)

lemma REAL_LE_DIV2_EQ: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) xb -->
   real_le (real_div x xb) (real_div xa xb) = real_le x xa"
  by (import hollight REAL_LE_DIV2_EQ)

lemma REAL_MUL_2: "ALL x::hollight.real.
   real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) x = real_add x x"
  by (import hollight REAL_MUL_2)

lemma REAL_POW_EQ_0: "ALL (x::hollight.real) n::nat.
   (real_pow x n = real_of_num 0) = (x = real_of_num 0 & n ~= 0)"
  by (import hollight REAL_POW_EQ_0)

lemma REAL_LE_MUL2: "ALL (w::hollight.real) (x::hollight.real) (y::hollight.real)
   z::hollight.real.
   real_le (real_of_num 0) w &
   real_le w x & real_le (real_of_num 0) y & real_le y z -->
   real_le (real_mul w y) (real_mul x z)"
  by (import hollight REAL_LE_MUL2)

lemma REAL_LT_MUL2: "ALL (w::hollight.real) (x::hollight.real) (y::hollight.real)
   z::hollight.real.
   real_le (real_of_num 0) w &
   real_lt w x & real_le (real_of_num 0) y & real_lt y z -->
   real_lt (real_mul w y) (real_mul x z)"
  by (import hollight REAL_LT_MUL2)

lemma REAL_LT_SQUARE: "ALL x::hollight.real.
   real_lt (real_of_num 0) (real_mul x x) = (x ~= real_of_num 0)"
  by (import hollight REAL_LT_SQUARE)

lemma REAL_INV_LE_1: "ALL x::hollight.real.
   real_le (real_of_num (NUMERAL_BIT1 0)) x -->
   real_le (real_inv x) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight REAL_INV_LE_1)

lemma REAL_POW_LE_1: "ALL (n::nat) x::hollight.real.
   real_le (real_of_num (NUMERAL_BIT1 0)) x -->
   real_le (real_of_num (NUMERAL_BIT1 0)) (real_pow x n)"
  by (import hollight REAL_POW_LE_1)

lemma REAL_POW_1_LE: "ALL (n::nat) x::hollight.real.
   real_le (real_of_num 0) x & real_le x (real_of_num (NUMERAL_BIT1 0)) -->
   real_le (real_pow x n) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight REAL_POW_1_LE)

lemma REAL_POW_1: "ALL x::hollight.real. real_pow x (NUMERAL_BIT1 0) = x"
  by (import hollight REAL_POW_1)

lemma REAL_POW_ONE: "ALL n::nat.
   real_pow (real_of_num (NUMERAL_BIT1 0)) n = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight REAL_POW_ONE)

lemma REAL_LT_INV2: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_lt x y -->
   real_lt (real_inv y) (real_inv x)"
  by (import hollight REAL_LT_INV2)

lemma REAL_LE_INV2: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_le x y -->
   real_le (real_inv y) (real_inv x)"
  by (import hollight REAL_LE_INV2)

lemma REAL_INV_1_LE: "ALL x::hollight.real.
   real_lt (real_of_num 0) x & real_le x (real_of_num (NUMERAL_BIT1 0)) -->
   real_le (real_of_num (NUMERAL_BIT1 0)) (real_inv x)"
  by (import hollight REAL_INV_1_LE)

lemma REAL_SUB_INV: "ALL (x::hollight.real) xa::hollight.real.
   x ~= real_of_num 0 & xa ~= real_of_num 0 -->
   real_sub (real_inv x) (real_inv xa) =
   real_div (real_sub xa x) (real_mul x xa)"
  by (import hollight REAL_SUB_INV)

lemma REAL_DOWN: "ALL d::hollight.real.
   real_lt (real_of_num 0) d -->
   (EX x::hollight.real. real_lt (real_of_num 0) x & real_lt x d)"
  by (import hollight REAL_DOWN)

lemma REAL_DOWN2: "ALL (d1::hollight.real) d2::hollight.real.
   real_lt (real_of_num 0) d1 & real_lt (real_of_num 0) d2 -->
   (EX e::hollight.real.
       real_lt (real_of_num 0) e & real_lt e d1 & real_lt e d2)"
  by (import hollight REAL_DOWN2)

lemma REAL_POW_LE2: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_le x y -->
   real_le (real_pow x n) (real_pow y n)"
  by (import hollight REAL_POW_LE2)

lemma REAL_POW_MONO: "ALL (m::nat) (n::nat) x::hollight.real.
   real_le (real_of_num (NUMERAL_BIT1 0)) x & <= m n -->
   real_le (real_pow x m) (real_pow x n)"
  by (import hollight REAL_POW_MONO)

lemma REAL_POW_LT2: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   n ~= 0 & real_le (real_of_num 0) x & real_lt x y -->
   real_lt (real_pow x n) (real_pow y n)"
  by (import hollight REAL_POW_LT2)

lemma REAL_POW_MONO_LT: "ALL (m::nat) (n::nat) x::hollight.real.
   real_lt (real_of_num (NUMERAL_BIT1 0)) x & < m n -->
   real_lt (real_pow x m) (real_pow x n)"
  by (import hollight REAL_POW_MONO_LT)

lemma REAL_POW_POW: "ALL (x::hollight.real) (m::nat) n::nat.
   real_pow (real_pow x m) n = real_pow x (m * n)"
  by (import hollight REAL_POW_POW)

lemma REAL_EQ_RCANCEL_IMP: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   z ~= real_of_num 0 & real_mul x z = real_mul y z --> x = y"
  by (import hollight REAL_EQ_RCANCEL_IMP)

lemma REAL_EQ_LCANCEL_IMP: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   xb ~= real_of_num 0 & real_mul xb x = real_mul xb xa --> x = xa"
  by (import hollight REAL_EQ_LCANCEL_IMP)

lemma REAL_LT_DIV: "ALL (x::hollight.real) xa::hollight.real.
   real_lt (real_of_num 0) x & real_lt (real_of_num 0) xa -->
   real_lt (real_of_num 0) (real_div x xa)"
  by (import hollight REAL_LT_DIV)

lemma REAL_LE_DIV: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) xa -->
   real_le (real_of_num 0) (real_div x xa)"
  by (import hollight REAL_LE_DIV)

lemma REAL_DIV_POW2: "ALL (x::hollight.real) (m::nat) n::nat.
   x ~= real_of_num 0 -->
   real_div (real_pow x m) (real_pow x n) =
   COND (<= n m) (real_pow x (m - n)) (real_inv (real_pow x (n - m)))"
  by (import hollight REAL_DIV_POW2)

lemma REAL_DIV_POW2_ALT: "ALL (x::hollight.real) (m::nat) n::nat.
   x ~= real_of_num 0 -->
   real_div (real_pow x m) (real_pow x n) =
   COND (< n m) (real_pow x (m - n)) (real_inv (real_pow x (n - m)))"
  by (import hollight REAL_DIV_POW2_ALT)

lemma REAL_LT_POW2: "ALL x::nat.
   real_lt (real_of_num 0)
    (real_pow (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) x)"
  by (import hollight REAL_LT_POW2)

lemma REAL_LE_POW2: "ALL n::nat.
   real_le (real_of_num (NUMERAL_BIT1 0))
    (real_pow (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) n)"
  by (import hollight REAL_LE_POW2)

lemma REAL_POW2_ABS: "ALL x::hollight.real.
   real_pow (real_abs x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)) =
   real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0))"
  by (import hollight REAL_POW2_ABS)

lemma REAL_LE_SQUARE_ABS: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_abs x) (real_abs y) =
   real_le (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
    (real_pow y (NUMERAL_BIT0 (NUMERAL_BIT1 0)))"
  by (import hollight REAL_LE_SQUARE_ABS)

lemma REAL_WLOG_LE: "(ALL (x::hollight.real) y::hollight.real.
    (P::hollight.real => hollight.real => bool) x y = P y x) &
(ALL (x::hollight.real) y::hollight.real. real_le x y --> P x y) -->
(ALL x::hollight.real. All (P x))"
  by (import hollight REAL_WLOG_LE)

lemma REAL_WLOG_LT: "(ALL x::hollight.real. (P::hollight.real => hollight.real => bool) x x) &
(ALL (x::hollight.real) y::hollight.real. P x y = P y x) &
(ALL (x::hollight.real) y::hollight.real. real_lt x y --> P x y) -->
(ALL x::hollight.real. All (P x))"
  by (import hollight REAL_WLOG_LT)

constdefs
  mod_real :: "hollight.real => hollight.real => hollight.real => bool" 
  "mod_real ==
%(u::hollight.real) (ua::hollight.real) ub::hollight.real.
   EX q::hollight.real. real_sub ua ub = real_mul q u"

lemma DEF_mod_real: "mod_real =
(%(u::hollight.real) (ua::hollight.real) ub::hollight.real.
    EX q::hollight.real. real_sub ua ub = real_mul q u)"
  by (import hollight DEF_mod_real)

constdefs
  DECIMAL :: "nat => nat => hollight.real" 
  "DECIMAL == %(u::nat) ua::nat. real_div (real_of_num u) (real_of_num ua)"

lemma DEF_DECIMAL: "DECIMAL = (%(u::nat) ua::nat. real_div (real_of_num u) (real_of_num ua))"
  by (import hollight DEF_DECIMAL)

lemma RAT_LEMMA1: "(y1::hollight.real) ~= real_of_num 0 &
(y2::hollight.real) ~= real_of_num 0 -->
real_add (real_div (x1::hollight.real) y1)
 (real_div (x2::hollight.real) y2) =
real_mul (real_add (real_mul x1 y2) (real_mul x2 y1))
 (real_mul (real_inv y1) (real_inv y2))"
  by (import hollight RAT_LEMMA1)

lemma RAT_LEMMA2: "real_lt (real_of_num 0) (y1::hollight.real) &
real_lt (real_of_num 0) (y2::hollight.real) -->
real_add (real_div (x1::hollight.real) y1)
 (real_div (x2::hollight.real) y2) =
real_mul (real_add (real_mul x1 y2) (real_mul x2 y1))
 (real_mul (real_inv y1) (real_inv y2))"
  by (import hollight RAT_LEMMA2)

lemma RAT_LEMMA3: "real_lt (real_of_num 0) (y1::hollight.real) &
real_lt (real_of_num 0) (y2::hollight.real) -->
real_sub (real_div (x1::hollight.real) y1)
 (real_div (x2::hollight.real) y2) =
real_mul (real_sub (real_mul x1 y2) (real_mul x2 y1))
 (real_mul (real_inv y1) (real_inv y2))"
  by (import hollight RAT_LEMMA3)

lemma RAT_LEMMA4: "real_lt (real_of_num 0) (y1::hollight.real) &
real_lt (real_of_num 0) (y2::hollight.real) -->
real_le (real_div (x1::hollight.real) y1)
 (real_div (x2::hollight.real) y2) =
real_le (real_mul x1 y2) (real_mul x2 y1)"
  by (import hollight RAT_LEMMA4)

lemma RAT_LEMMA5: "real_lt (real_of_num 0) (y1::hollight.real) &
real_lt (real_of_num 0) (y2::hollight.real) -->
(real_div (x1::hollight.real) y1 = real_div (x2::hollight.real) y2) =
(real_mul x1 y2 = real_mul x2 y1)"
  by (import hollight RAT_LEMMA5)

constdefs
  is_int :: "hollight.real => bool" 
  "is_int ==
%u::hollight.real.
   EX n::nat. u = real_of_num n | u = real_neg (real_of_num n)"

lemma DEF_is_int: "is_int =
(%u::hollight.real.
    EX n::nat. u = real_of_num n | u = real_neg (real_of_num n))"
  by (import hollight DEF_is_int)

typedef (open) int = "Collect is_int"  morphisms "dest_int" "mk_int"
  apply (rule light_ex_imp_nonempty[where t="real_of_num (NUMERAL 0)"])
  by (import hollight TYDEF_int)

syntax
  dest_int :: _ 

syntax
  mk_int :: _ 

lemmas "TYDEF_int_@intern" = typedef_hol2hollight 
  [where a="a :: hollight.int" and r=r ,
   OF type_definition_int]

lemma dest_int_rep: "ALL x::hollight.int.
   EX n::nat.
      dest_int x = real_of_num n | dest_int x = real_neg (real_of_num n)"
  by (import hollight dest_int_rep)

constdefs
  int_le :: "hollight.int => hollight.int => bool" 
  "int_le ==
%(u::hollight.int) ua::hollight.int. real_le (dest_int u) (dest_int ua)"

lemma DEF_int_le: "int_le =
(%(u::hollight.int) ua::hollight.int. real_le (dest_int u) (dest_int ua))"
  by (import hollight DEF_int_le)

constdefs
  int_lt :: "hollight.int => hollight.int => bool" 
  "int_lt ==
%(u::hollight.int) ua::hollight.int. real_lt (dest_int u) (dest_int ua)"

lemma DEF_int_lt: "int_lt =
(%(u::hollight.int) ua::hollight.int. real_lt (dest_int u) (dest_int ua))"
  by (import hollight DEF_int_lt)

constdefs
  int_ge :: "hollight.int => hollight.int => bool" 
  "int_ge ==
%(u::hollight.int) ua::hollight.int.
   hollight.real_ge (dest_int u) (dest_int ua)"

lemma DEF_int_ge: "int_ge =
(%(u::hollight.int) ua::hollight.int.
    hollight.real_ge (dest_int u) (dest_int ua))"
  by (import hollight DEF_int_ge)

constdefs
  int_gt :: "hollight.int => hollight.int => bool" 
  "int_gt ==
%(u::hollight.int) ua::hollight.int.
   hollight.real_gt (dest_int u) (dest_int ua)"

lemma DEF_int_gt: "int_gt =
(%(u::hollight.int) ua::hollight.int.
    hollight.real_gt (dest_int u) (dest_int ua))"
  by (import hollight DEF_int_gt)

constdefs
  int_of_num :: "nat => hollight.int" 
  "int_of_num == %u::nat. mk_int (real_of_num u)"

lemma DEF_int_of_num: "int_of_num = (%u::nat. mk_int (real_of_num u))"
  by (import hollight DEF_int_of_num)

lemma int_of_num_th: "ALL x::nat. dest_int (int_of_num x) = real_of_num x"
  by (import hollight int_of_num_th)

constdefs
  int_neg :: "hollight.int => hollight.int" 
  "int_neg == %u::hollight.int. mk_int (real_neg (dest_int u))"

lemma DEF_int_neg: "int_neg = (%u::hollight.int. mk_int (real_neg (dest_int u)))"
  by (import hollight DEF_int_neg)

lemma int_neg_th: "ALL x::hollight.int. dest_int (int_neg x) = real_neg (dest_int x)"
  by (import hollight int_neg_th)

constdefs
  int_add :: "hollight.int => hollight.int => hollight.int" 
  "int_add ==
%(u::hollight.int) ua::hollight.int.
   mk_int (real_add (dest_int u) (dest_int ua))"

lemma DEF_int_add: "int_add =
(%(u::hollight.int) ua::hollight.int.
    mk_int (real_add (dest_int u) (dest_int ua)))"
  by (import hollight DEF_int_add)

lemma int_add_th: "ALL (x::hollight.int) xa::hollight.int.
   dest_int (int_add x xa) = real_add (dest_int x) (dest_int xa)"
  by (import hollight int_add_th)

constdefs
  int_sub :: "hollight.int => hollight.int => hollight.int" 
  "int_sub ==
%(u::hollight.int) ua::hollight.int.
   mk_int (real_sub (dest_int u) (dest_int ua))"

lemma DEF_int_sub: "int_sub =
(%(u::hollight.int) ua::hollight.int.
    mk_int (real_sub (dest_int u) (dest_int ua)))"
  by (import hollight DEF_int_sub)

lemma int_sub_th: "ALL (x::hollight.int) xa::hollight.int.
   dest_int (int_sub x xa) = real_sub (dest_int x) (dest_int xa)"
  by (import hollight int_sub_th)

constdefs
  int_mul :: "hollight.int => hollight.int => hollight.int" 
  "int_mul ==
%(u::hollight.int) ua::hollight.int.
   mk_int (real_mul (dest_int u) (dest_int ua))"

lemma DEF_int_mul: "int_mul =
(%(u::hollight.int) ua::hollight.int.
    mk_int (real_mul (dest_int u) (dest_int ua)))"
  by (import hollight DEF_int_mul)

lemma int_mul_th: "ALL (x::hollight.int) y::hollight.int.
   dest_int (int_mul x y) = real_mul (dest_int x) (dest_int y)"
  by (import hollight int_mul_th)

constdefs
  int_abs :: "hollight.int => hollight.int" 
  "int_abs == %u::hollight.int. mk_int (real_abs (dest_int u))"

lemma DEF_int_abs: "int_abs = (%u::hollight.int. mk_int (real_abs (dest_int u)))"
  by (import hollight DEF_int_abs)

lemma int_abs_th: "ALL x::hollight.int. dest_int (int_abs x) = real_abs (dest_int x)"
  by (import hollight int_abs_th)

constdefs
  int_max :: "hollight.int => hollight.int => hollight.int" 
  "int_max ==
%(u::hollight.int) ua::hollight.int.
   mk_int (real_max (dest_int u) (dest_int ua))"

lemma DEF_int_max: "int_max =
(%(u::hollight.int) ua::hollight.int.
    mk_int (real_max (dest_int u) (dest_int ua)))"
  by (import hollight DEF_int_max)

lemma int_max_th: "ALL (x::hollight.int) y::hollight.int.
   dest_int (int_max x y) = real_max (dest_int x) (dest_int y)"
  by (import hollight int_max_th)

constdefs
  int_min :: "hollight.int => hollight.int => hollight.int" 
  "int_min ==
%(u::hollight.int) ua::hollight.int.
   mk_int (real_min (dest_int u) (dest_int ua))"

lemma DEF_int_min: "int_min =
(%(u::hollight.int) ua::hollight.int.
    mk_int (real_min (dest_int u) (dest_int ua)))"
  by (import hollight DEF_int_min)

lemma int_min_th: "ALL (x::hollight.int) y::hollight.int.
   dest_int (int_min x y) = real_min (dest_int x) (dest_int y)"
  by (import hollight int_min_th)

constdefs
  int_pow :: "hollight.int => nat => hollight.int" 
  "int_pow == %(u::hollight.int) ua::nat. mk_int (real_pow (dest_int u) ua)"

lemma DEF_int_pow: "int_pow = (%(u::hollight.int) ua::nat. mk_int (real_pow (dest_int u) ua))"
  by (import hollight DEF_int_pow)

lemma int_pow_th: "ALL (x::hollight.int) xa::nat.
   dest_int (int_pow x xa) = real_pow (dest_int x) xa"
  by (import hollight int_pow_th)

lemma INT_IMAGE: "ALL x::hollight.int.
   (EX n::nat. x = int_of_num n) | (EX n::nat. x = int_neg (int_of_num n))"
  by (import hollight INT_IMAGE)

lemma INT_LT_DISCRETE: "ALL (x::hollight.int) y::hollight.int.
   int_lt x y = int_le (int_add x (int_of_num (NUMERAL_BIT1 0))) y"
  by (import hollight INT_LT_DISCRETE)

lemma INT_GT_DISCRETE: "ALL (x::hollight.int) xa::hollight.int.
   int_gt x xa = int_ge x (int_add xa (int_of_num (NUMERAL_BIT1 0)))"
  by (import hollight INT_GT_DISCRETE)

lemma INT_FORALL_POS: "(ALL n::nat. (P::hollight.int => bool) (int_of_num n)) =
(ALL i::hollight.int. int_le (int_of_num 0) i --> P i)"
  by (import hollight INT_FORALL_POS)

lemma INT_ABS_MUL_1: "ALL (x::hollight.int) y::hollight.int.
   (int_abs (int_mul x y) = int_of_num (NUMERAL_BIT1 0)) =
   (int_abs x = int_of_num (NUMERAL_BIT1 0) &
    int_abs y = int_of_num (NUMERAL_BIT1 0))"
  by (import hollight INT_ABS_MUL_1)

lemma INT_POW: "int_pow (x::hollight.int) 0 = int_of_num (NUMERAL_BIT1 0) &
(ALL xa::nat. int_pow x (Suc xa) = int_mul x (int_pow x xa))"
  by (import hollight INT_POW)

lemma INT_ABS: "ALL x::hollight.int.
   int_abs x = COND (int_le (int_of_num 0) x) x (int_neg x)"
  by (import hollight INT_ABS)

lemma INT_GE: "ALL (x::hollight.int) xa::hollight.int. int_ge x xa = int_le xa x"
  by (import hollight INT_GE)

lemma INT_GT: "ALL (x::hollight.int) xa::hollight.int. int_gt x xa = int_lt xa x"
  by (import hollight INT_GT)

lemma INT_LT: "ALL (x::hollight.int) xa::hollight.int. int_lt x xa = (~ int_le xa x)"
  by (import hollight INT_LT)

lemma INT_ARCH: "ALL (x::hollight.int) d::hollight.int.
   d ~= int_of_num 0 --> (EX c::hollight.int. int_lt x (int_mul c d))"
  by (import hollight INT_ARCH)

constdefs
  mod_int :: "hollight.int => hollight.int => hollight.int => bool" 
  "mod_int ==
%(u::hollight.int) (ua::hollight.int) ub::hollight.int.
   EX q::hollight.int. int_sub ua ub = int_mul q u"

lemma DEF_mod_int: "mod_int =
(%(u::hollight.int) (ua::hollight.int) ub::hollight.int.
    EX q::hollight.int. int_sub ua ub = int_mul q u)"
  by (import hollight DEF_mod_int)

constdefs
  IN :: "'A => ('A => bool) => bool" 
  "IN == %(u::'A::type) ua::'A::type => bool. ua u"

lemma DEF_IN: "IN = (%(u::'A::type) ua::'A::type => bool. ua u)"
  by (import hollight DEF_IN)

lemma EXTENSION: "ALL (x::'A::type => bool) xa::'A::type => bool.
   (x = xa) = (ALL xb::'A::type. IN xb x = IN xb xa)"
  by (import hollight EXTENSION)

constdefs
  GSPEC :: "('A => bool) => 'A => bool" 
  "GSPEC == %u::'A::type => bool. u"

lemma DEF_GSPEC: "GSPEC = (%u::'A::type => bool. u)"
  by (import hollight DEF_GSPEC)

constdefs
  SETSPEC :: "'q_36941 => bool => 'q_36941 => bool" 
  "SETSPEC == %(u::'q_36941::type) (ua::bool) ub::'q_36941::type. ua & u = ub"

lemma DEF_SETSPEC: "SETSPEC = (%(u::'q_36941::type) (ua::bool) ub::'q_36941::type. ua & u = ub)"
  by (import hollight DEF_SETSPEC)

lemma IN_ELIM_THM: "(ALL (P::(bool => 'q_36974::type => bool) => bool) x::'q_36974::type.
    IN x (GSPEC (%v::'q_36974::type. P (SETSPEC v))) =
    P (%(p::bool) t::'q_36974::type. p & x = t)) &
(ALL (p::'q_37005::type => bool) x::'q_37005::type.
    IN x
     (GSPEC (%v::'q_37005::type. EX y::'q_37005::type. SETSPEC v (p y) y)) =
    p x) &
(ALL (P::(bool => 'q_37033::type => bool) => bool) x::'q_37033::type.
    GSPEC (%v::'q_37033::type. P (SETSPEC v)) x =
    P (%(p::bool) t::'q_37033::type. p & x = t)) &
(ALL (p::'q_37062::type => bool) x::'q_37062::type.
    GSPEC (%v::'q_37062::type. EX y::'q_37062::type. SETSPEC v (p y) y) x =
    p x) &
(ALL (p::'q_37079::type => bool) x::'q_37079::type. IN x p = p x)"
  by (import hollight IN_ELIM_THM)

constdefs
  EMPTY :: "'A => bool" 
  "EMPTY == %x::'A::type. False"

lemma DEF_EMPTY: "EMPTY = (%x::'A::type. False)"
  by (import hollight DEF_EMPTY)

constdefs
  INSERT :: "'A => ('A => bool) => 'A => bool" 
  "INSERT == %(u::'A::type) (ua::'A::type => bool) y::'A::type. IN y ua | y = u"

lemma DEF_INSERT: "INSERT =
(%(u::'A::type) (ua::'A::type => bool) y::'A::type. IN y ua | y = u)"
  by (import hollight DEF_INSERT)

consts
  UNIV :: "'A => bool" 

defs
  UNIV_def: "hollight.UNIV == %x::'A::type. True"

lemma DEF_UNIV: "hollight.UNIV = (%x::'A::type. True)"
  by (import hollight DEF_UNIV)

consts
  UNION :: "('A => bool) => ('A => bool) => 'A => bool" 

defs
  UNION_def: "hollight.UNION ==
%(u::'A::type => bool) ua::'A::type => bool.
   GSPEC (%ub::'A::type. EX x::'A::type. SETSPEC ub (IN x u | IN x ua) x)"

lemma DEF_UNION: "hollight.UNION =
(%(u::'A::type => bool) ua::'A::type => bool.
    GSPEC (%ub::'A::type. EX x::'A::type. SETSPEC ub (IN x u | IN x ua) x))"
  by (import hollight DEF_UNION)

constdefs
  UNIONS :: "(('A => bool) => bool) => 'A => bool" 
  "UNIONS ==
%u::('A::type => bool) => bool.
   GSPEC
    (%ua::'A::type.
        EX x::'A::type.
           SETSPEC ua (EX ua::'A::type => bool. IN ua u & IN x ua) x)"

lemma DEF_UNIONS: "UNIONS =
(%u::('A::type => bool) => bool.
    GSPEC
     (%ua::'A::type.
         EX x::'A::type.
            SETSPEC ua (EX ua::'A::type => bool. IN ua u & IN x ua) x))"
  by (import hollight DEF_UNIONS)

consts
  INTER :: "('A => bool) => ('A => bool) => 'A => bool" 

defs
  INTER_def: "hollight.INTER ==
%(u::'A::type => bool) ua::'A::type => bool.
   GSPEC (%ub::'A::type. EX x::'A::type. SETSPEC ub (IN x u & IN x ua) x)"

lemma DEF_INTER: "hollight.INTER =
(%(u::'A::type => bool) ua::'A::type => bool.
    GSPEC (%ub::'A::type. EX x::'A::type. SETSPEC ub (IN x u & IN x ua) x))"
  by (import hollight DEF_INTER)

constdefs
  INTERS :: "(('A => bool) => bool) => 'A => bool" 
  "INTERS ==
%u::('A::type => bool) => bool.
   GSPEC
    (%ua::'A::type.
        EX x::'A::type.
           SETSPEC ua (ALL ua::'A::type => bool. IN ua u --> IN x ua) x)"

lemma DEF_INTERS: "INTERS =
(%u::('A::type => bool) => bool.
    GSPEC
     (%ua::'A::type.
         EX x::'A::type.
            SETSPEC ua (ALL ua::'A::type => bool. IN ua u --> IN x ua) x))"
  by (import hollight DEF_INTERS)

constdefs
  DIFF :: "('A => bool) => ('A => bool) => 'A => bool" 
  "DIFF ==
%(u::'A::type => bool) ua::'A::type => bool.
   GSPEC (%ub::'A::type. EX x::'A::type. SETSPEC ub (IN x u & ~ IN x ua) x)"

lemma DEF_DIFF: "DIFF =
(%(u::'A::type => bool) ua::'A::type => bool.
    GSPEC
     (%ub::'A::type. EX x::'A::type. SETSPEC ub (IN x u & ~ IN x ua) x))"
  by (import hollight DEF_DIFF)

lemma INSERT: "INSERT (x::'A::type) (s::'A::type => bool) =
GSPEC (%u::'A::type. EX y::'A::type. SETSPEC u (IN y s | y = x) y)"
  by (import hollight INSERT)

constdefs
  DELETE :: "('A => bool) => 'A => 'A => bool" 
  "DELETE ==
%(u::'A::type => bool) ua::'A::type.
   GSPEC (%ub::'A::type. EX y::'A::type. SETSPEC ub (IN y u & y ~= ua) y)"

lemma DEF_DELETE: "DELETE =
(%(u::'A::type => bool) ua::'A::type.
    GSPEC (%ub::'A::type. EX y::'A::type. SETSPEC ub (IN y u & y ~= ua) y))"
  by (import hollight DEF_DELETE)

constdefs
  SUBSET :: "('A => bool) => ('A => bool) => bool" 
  "SUBSET ==
%(u::'A::type => bool) ua::'A::type => bool.
   ALL x::'A::type. IN x u --> IN x ua"

lemma DEF_SUBSET: "SUBSET =
(%(u::'A::type => bool) ua::'A::type => bool.
    ALL x::'A::type. IN x u --> IN x ua)"
  by (import hollight DEF_SUBSET)

constdefs
  PSUBSET :: "('A => bool) => ('A => bool) => bool" 
  "PSUBSET ==
%(u::'A::type => bool) ua::'A::type => bool. SUBSET u ua & u ~= ua"

lemma DEF_PSUBSET: "PSUBSET =
(%(u::'A::type => bool) ua::'A::type => bool. SUBSET u ua & u ~= ua)"
  by (import hollight DEF_PSUBSET)

constdefs
  DISJOINT :: "('A => bool) => ('A => bool) => bool" 
  "DISJOINT ==
%(u::'A::type => bool) ua::'A::type => bool. hollight.INTER u ua = EMPTY"

lemma DEF_DISJOINT: "DISJOINT =
(%(u::'A::type => bool) ua::'A::type => bool. hollight.INTER u ua = EMPTY)"
  by (import hollight DEF_DISJOINT)

constdefs
  SING :: "('A => bool) => bool" 
  "SING == %u::'A::type => bool. EX x::'A::type. u = INSERT x EMPTY"

lemma DEF_SING: "SING = (%u::'A::type => bool. EX x::'A::type. u = INSERT x EMPTY)"
  by (import hollight DEF_SING)

constdefs
  FINITE :: "('A => bool) => bool" 
  "FINITE ==
%a::'A::type => bool.
   ALL FINITE'::('A::type => bool) => bool.
      (ALL a::'A::type => bool.
          a = EMPTY |
          (EX (x::'A::type) s::'A::type => bool.
              a = INSERT x s & FINITE' s) -->
          FINITE' a) -->
      FINITE' a"

lemma DEF_FINITE: "FINITE =
(%a::'A::type => bool.
    ALL FINITE'::('A::type => bool) => bool.
       (ALL a::'A::type => bool.
           a = EMPTY |
           (EX (x::'A::type) s::'A::type => bool.
               a = INSERT x s & FINITE' s) -->
           FINITE' a) -->
       FINITE' a)"
  by (import hollight DEF_FINITE)

constdefs
  INFINITE :: "('A => bool) => bool" 
  "INFINITE == %u::'A::type => bool. ~ FINITE u"

lemma DEF_INFINITE: "INFINITE = (%u::'A::type => bool. ~ FINITE u)"
  by (import hollight DEF_INFINITE)

constdefs
  IMAGE :: "('A => 'B) => ('A => bool) => 'B => bool" 
  "IMAGE ==
%(u::'A::type => 'B::type) ua::'A::type => bool.
   GSPEC
    (%ub::'B::type.
        EX y::'B::type. SETSPEC ub (EX x::'A::type. IN x ua & y = u x) y)"

lemma DEF_IMAGE: "IMAGE =
(%(u::'A::type => 'B::type) ua::'A::type => bool.
    GSPEC
     (%ub::'B::type.
         EX y::'B::type. SETSPEC ub (EX x::'A::type. IN x ua & y = u x) y))"
  by (import hollight DEF_IMAGE)

constdefs
  INJ :: "('A => 'B) => ('A => bool) => ('B => bool) => bool" 
  "INJ ==
%(u::'A::type => 'B::type) (ua::'A::type => bool) ub::'B::type => bool.
   (ALL x::'A::type. IN x ua --> IN (u x) ub) &
   (ALL (x::'A::type) y::'A::type. IN x ua & IN y ua & u x = u y --> x = y)"

lemma DEF_INJ: "INJ =
(%(u::'A::type => 'B::type) (ua::'A::type => bool) ub::'B::type => bool.
    (ALL x::'A::type. IN x ua --> IN (u x) ub) &
    (ALL (x::'A::type) y::'A::type.
        IN x ua & IN y ua & u x = u y --> x = y))"
  by (import hollight DEF_INJ)

constdefs
  SURJ :: "('A => 'B) => ('A => bool) => ('B => bool) => bool" 
  "SURJ ==
%(u::'A::type => 'B::type) (ua::'A::type => bool) ub::'B::type => bool.
   (ALL x::'A::type. IN x ua --> IN (u x) ub) &
   (ALL x::'B::type. IN x ub --> (EX y::'A::type. IN y ua & u y = x))"

lemma DEF_SURJ: "SURJ =
(%(u::'A::type => 'B::type) (ua::'A::type => bool) ub::'B::type => bool.
    (ALL x::'A::type. IN x ua --> IN (u x) ub) &
    (ALL x::'B::type. IN x ub --> (EX y::'A::type. IN y ua & u y = x)))"
  by (import hollight DEF_SURJ)

constdefs
  BIJ :: "('A => 'B) => ('A => bool) => ('B => bool) => bool" 
  "BIJ ==
%(u::'A::type => 'B::type) (ua::'A::type => bool) ub::'B::type => bool.
   INJ u ua ub & SURJ u ua ub"

lemma DEF_BIJ: "BIJ =
(%(u::'A::type => 'B::type) (ua::'A::type => bool) ub::'B::type => bool.
    INJ u ua ub & SURJ u ua ub)"
  by (import hollight DEF_BIJ)

constdefs
  CHOICE :: "('A => bool) => 'A" 
  "CHOICE == %u::'A::type => bool. SOME x::'A::type. IN x u"

lemma DEF_CHOICE: "CHOICE = (%u::'A::type => bool. SOME x::'A::type. IN x u)"
  by (import hollight DEF_CHOICE)

constdefs
  REST :: "('A => bool) => 'A => bool" 
  "REST == %u::'A::type => bool. DELETE u (CHOICE u)"

lemma DEF_REST: "REST = (%u::'A::type => bool. DELETE u (CHOICE u))"
  by (import hollight DEF_REST)

constdefs
  CARD_GE :: "('q_37578 => bool) => ('q_37575 => bool) => bool" 
  "CARD_GE ==
%(u::'q_37578::type => bool) ua::'q_37575::type => bool.
   EX f::'q_37578::type => 'q_37575::type.
      ALL y::'q_37575::type.
         IN y ua --> (EX x::'q_37578::type. IN x u & y = f x)"

lemma DEF_CARD_GE: "CARD_GE =
(%(u::'q_37578::type => bool) ua::'q_37575::type => bool.
    EX f::'q_37578::type => 'q_37575::type.
       ALL y::'q_37575::type.
          IN y ua --> (EX x::'q_37578::type. IN x u & y = f x))"
  by (import hollight DEF_CARD_GE)

constdefs
  CARD_LE :: "('q_37587 => bool) => ('q_37586 => bool) => bool" 
  "CARD_LE ==
%(u::'q_37587::type => bool) ua::'q_37586::type => bool. CARD_GE ua u"

lemma DEF_CARD_LE: "CARD_LE =
(%(u::'q_37587::type => bool) ua::'q_37586::type => bool. CARD_GE ua u)"
  by (import hollight DEF_CARD_LE)

constdefs
  CARD_EQ :: "('q_37597 => bool) => ('q_37598 => bool) => bool" 
  "CARD_EQ ==
%(u::'q_37597::type => bool) ua::'q_37598::type => bool.
   CARD_LE u ua & CARD_LE ua u"

lemma DEF_CARD_EQ: "CARD_EQ =
(%(u::'q_37597::type => bool) ua::'q_37598::type => bool.
    CARD_LE u ua & CARD_LE ua u)"
  by (import hollight DEF_CARD_EQ)

constdefs
  CARD_GT :: "('q_37612 => bool) => ('q_37613 => bool) => bool" 
  "CARD_GT ==
%(u::'q_37612::type => bool) ua::'q_37613::type => bool.
   CARD_GE u ua & ~ CARD_GE ua u"

lemma DEF_CARD_GT: "CARD_GT =
(%(u::'q_37612::type => bool) ua::'q_37613::type => bool.
    CARD_GE u ua & ~ CARD_GE ua u)"
  by (import hollight DEF_CARD_GT)

constdefs
  CARD_LT :: "('q_37628 => bool) => ('q_37629 => bool) => bool" 
  "CARD_LT ==
%(u::'q_37628::type => bool) ua::'q_37629::type => bool.
   CARD_LE u ua & ~ CARD_LE ua u"

lemma DEF_CARD_LT: "CARD_LT =
(%(u::'q_37628::type => bool) ua::'q_37629::type => bool.
    CARD_LE u ua & ~ CARD_LE ua u)"
  by (import hollight DEF_CARD_LT)

constdefs
  COUNTABLE :: "('q_37642 => bool) => bool" 
  "(op ==::(('q_37642::type => bool) => bool)
        => (('q_37642::type => bool) => bool) => prop)
 (COUNTABLE::('q_37642::type => bool) => bool)
 ((CARD_GE::(nat => bool) => ('q_37642::type => bool) => bool)
   (hollight.UNIV::nat => bool))"

lemma DEF_COUNTABLE: "(op =::(('q_37642::type => bool) => bool)
       => (('q_37642::type => bool) => bool) => bool)
 (COUNTABLE::('q_37642::type => bool) => bool)
 ((CARD_GE::(nat => bool) => ('q_37642::type => bool) => bool)
   (hollight.UNIV::nat => bool))"
  by (import hollight DEF_COUNTABLE)

lemma NOT_IN_EMPTY: "ALL x::'A::type. ~ IN x EMPTY"
  by (import hollight NOT_IN_EMPTY)

lemma IN_UNIV: "ALL x::'A::type. IN x hollight.UNIV"
  by (import hollight IN_UNIV)

lemma IN_UNION: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type.
   IN xb (hollight.UNION x xa) = (IN xb x | IN xb xa)"
  by (import hollight IN_UNION)

lemma IN_UNIONS: "ALL (x::('A::type => bool) => bool) xa::'A::type.
   IN xa (UNIONS x) = (EX t::'A::type => bool. IN t x & IN xa t)"
  by (import hollight IN_UNIONS)

lemma IN_INTER: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type.
   IN xb (hollight.INTER x xa) = (IN xb x & IN xb xa)"
  by (import hollight IN_INTER)

lemma IN_INTERS: "ALL (x::('A::type => bool) => bool) xa::'A::type.
   IN xa (INTERS x) = (ALL t::'A::type => bool. IN t x --> IN xa t)"
  by (import hollight IN_INTERS)

lemma IN_DIFF: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type.
   IN xb (DIFF x xa) = (IN xb x & ~ IN xb xa)"
  by (import hollight IN_DIFF)

lemma IN_INSERT: "ALL (x::'A::type) (xa::'A::type) xb::'A::type => bool.
   IN x (INSERT xa xb) = (x = xa | IN x xb)"
  by (import hollight IN_INSERT)

lemma IN_DELETE: "ALL (x::'A::type => bool) (xa::'A::type) xb::'A::type.
   IN xa (DELETE x xb) = (IN xa x & xa ~= xb)"
  by (import hollight IN_DELETE)

lemma IN_SING: "ALL (x::'A::type) xa::'A::type. IN x (INSERT xa EMPTY) = (x = xa)"
  by (import hollight IN_SING)

lemma IN_IMAGE: "ALL (x::'B::type) (xa::'A::type => bool) xb::'A::type => 'B::type.
   IN x (IMAGE xb xa) = (EX xc::'A::type. x = xb xc & IN xc xa)"
  by (import hollight IN_IMAGE)

lemma IN_REST: "ALL (x::'A::type) xa::'A::type => bool.
   IN x (REST xa) = (IN x xa & x ~= CHOICE xa)"
  by (import hollight IN_REST)

lemma CHOICE_DEF: "ALL x::'A::type => bool. x ~= EMPTY --> IN (CHOICE x) x"
  by (import hollight CHOICE_DEF)

lemma NOT_EQUAL_SETS: "ALL (x::'A::type => bool) xa::'A::type => bool.
   (x ~= xa) = (EX xb::'A::type. IN xb xa = (~ IN xb x))"
  by (import hollight NOT_EQUAL_SETS)

lemma MEMBER_NOT_EMPTY: "ALL x::'A::type => bool. (EX xa::'A::type. IN xa x) = (x ~= EMPTY)"
  by (import hollight MEMBER_NOT_EMPTY)

lemma UNIV_NOT_EMPTY: "(Not::bool => bool)
 ((op =::('A::type => bool) => ('A::type => bool) => bool)
   (hollight.UNIV::'A::type => bool) (EMPTY::'A::type => bool))"
  by (import hollight UNIV_NOT_EMPTY)

lemma EMPTY_NOT_UNIV: "(Not::bool => bool)
 ((op =::('A::type => bool) => ('A::type => bool) => bool)
   (EMPTY::'A::type => bool) (hollight.UNIV::'A::type => bool))"
  by (import hollight EMPTY_NOT_UNIV)

lemma EQ_UNIV: "(ALL x::'A::type. IN x (s::'A::type => bool)) = (s = hollight.UNIV)"
  by (import hollight EQ_UNIV)

lemma SUBSET_TRANS: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type => bool.
   SUBSET x xa & SUBSET xa xb --> SUBSET x xb"
  by (import hollight SUBSET_TRANS)

lemma SUBSET_REFL: "ALL x::'A::type => bool. SUBSET x x"
  by (import hollight SUBSET_REFL)

lemma SUBSET_ANTISYM: "ALL (x::'A::type => bool) xa::'A::type => bool.
   SUBSET x xa & SUBSET xa x --> x = xa"
  by (import hollight SUBSET_ANTISYM)

lemma EMPTY_SUBSET: "(All::(('A::type => bool) => bool) => bool)
 ((SUBSET::('A::type => bool) => ('A::type => bool) => bool)
   (EMPTY::'A::type => bool))"
  by (import hollight EMPTY_SUBSET)

lemma SUBSET_EMPTY: "ALL x::'A::type => bool. SUBSET x EMPTY = (x = EMPTY)"
  by (import hollight SUBSET_EMPTY)

lemma SUBSET_UNIV: "ALL x::'A::type => bool. SUBSET x hollight.UNIV"
  by (import hollight SUBSET_UNIV)

lemma UNIV_SUBSET: "ALL x::'A::type => bool. SUBSET hollight.UNIV x = (x = hollight.UNIV)"
  by (import hollight UNIV_SUBSET)

lemma PSUBSET_TRANS: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type => bool.
   PSUBSET x xa & PSUBSET xa xb --> PSUBSET x xb"
  by (import hollight PSUBSET_TRANS)

lemma PSUBSET_SUBSET_TRANS: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type => bool.
   PSUBSET x xa & SUBSET xa xb --> PSUBSET x xb"
  by (import hollight PSUBSET_SUBSET_TRANS)

lemma SUBSET_PSUBSET_TRANS: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type => bool.
   SUBSET x xa & PSUBSET xa xb --> PSUBSET x xb"
  by (import hollight SUBSET_PSUBSET_TRANS)

lemma PSUBSET_IRREFL: "ALL x::'A::type => bool. ~ PSUBSET x x"
  by (import hollight PSUBSET_IRREFL)

lemma NOT_PSUBSET_EMPTY: "ALL x::'A::type => bool. ~ PSUBSET x EMPTY"
  by (import hollight NOT_PSUBSET_EMPTY)

lemma NOT_UNIV_PSUBSET: "ALL x::'A::type => bool. ~ PSUBSET hollight.UNIV x"
  by (import hollight NOT_UNIV_PSUBSET)

lemma PSUBSET_UNIV: "ALL x::'A::type => bool.
   PSUBSET x hollight.UNIV = (EX xa::'A::type. ~ IN xa x)"
  by (import hollight PSUBSET_UNIV)

lemma UNION_ASSOC: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type => bool.
   hollight.UNION (hollight.UNION x xa) xb =
   hollight.UNION x (hollight.UNION xa xb)"
  by (import hollight UNION_ASSOC)

lemma UNION_IDEMPOT: "ALL x::'A::type => bool. hollight.UNION x x = x"
  by (import hollight UNION_IDEMPOT)

lemma UNION_COMM: "ALL (x::'A::type => bool) xa::'A::type => bool.
   hollight.UNION x xa = hollight.UNION xa x"
  by (import hollight UNION_COMM)

lemma SUBSET_UNION: "(ALL (x::'A::type => bool) xa::'A::type => bool.
    SUBSET x (hollight.UNION x xa)) &
(ALL (x::'A::type => bool) xa::'A::type => bool.
    SUBSET x (hollight.UNION xa x))"
  by (import hollight SUBSET_UNION)

lemma SUBSET_UNION_ABSORPTION: "ALL (x::'A::type => bool) xa::'A::type => bool.
   SUBSET x xa = (hollight.UNION x xa = xa)"
  by (import hollight SUBSET_UNION_ABSORPTION)

lemma UNION_EMPTY: "(ALL x::'A::type => bool. hollight.UNION EMPTY x = x) &
(ALL x::'A::type => bool. hollight.UNION x EMPTY = x)"
  by (import hollight UNION_EMPTY)

lemma UNION_UNIV: "(ALL x::'A::type => bool. hollight.UNION hollight.UNIV x = hollight.UNIV) &
(ALL x::'A::type => bool. hollight.UNION x hollight.UNIV = hollight.UNIV)"
  by (import hollight UNION_UNIV)

lemma EMPTY_UNION: "ALL (x::'A::type => bool) xa::'A::type => bool.
   (hollight.UNION x xa = EMPTY) = (x = EMPTY & xa = EMPTY)"
  by (import hollight EMPTY_UNION)

lemma UNION_SUBSET: "ALL (x::'q_38479::type => bool) (xa::'q_38479::type => bool)
   xb::'q_38479::type => bool.
   SUBSET (hollight.UNION x xa) xb = (SUBSET x xb & SUBSET xa xb)"
  by (import hollight UNION_SUBSET)

lemma INTER_ASSOC: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type => bool.
   hollight.INTER (hollight.INTER x xa) xb =
   hollight.INTER x (hollight.INTER xa xb)"
  by (import hollight INTER_ASSOC)

lemma INTER_IDEMPOT: "ALL x::'A::type => bool. hollight.INTER x x = x"
  by (import hollight INTER_IDEMPOT)

lemma INTER_COMM: "ALL (x::'A::type => bool) xa::'A::type => bool.
   hollight.INTER x xa = hollight.INTER xa x"
  by (import hollight INTER_COMM)

lemma INTER_SUBSET: "(ALL (x::'A::type => bool) xa::'A::type => bool.
    SUBSET (hollight.INTER x xa) x) &
(ALL (x::'A::type => bool) xa::'A::type => bool.
    SUBSET (hollight.INTER xa x) x)"
  by (import hollight INTER_SUBSET)

lemma SUBSET_INTER_ABSORPTION: "ALL (x::'A::type => bool) xa::'A::type => bool.
   SUBSET x xa = (hollight.INTER x xa = x)"
  by (import hollight SUBSET_INTER_ABSORPTION)

lemma INTER_EMPTY: "(ALL x::'A::type => bool. hollight.INTER EMPTY x = EMPTY) &
(ALL x::'A::type => bool. hollight.INTER x EMPTY = EMPTY)"
  by (import hollight INTER_EMPTY)

lemma INTER_UNIV: "(ALL x::'A::type => bool. hollight.INTER hollight.UNIV x = x) &
(ALL x::'A::type => bool. hollight.INTER x hollight.UNIV = x)"
  by (import hollight INTER_UNIV)

lemma UNION_OVER_INTER: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type => bool.
   hollight.INTER x (hollight.UNION xa xb) =
   hollight.UNION (hollight.INTER x xa) (hollight.INTER x xb)"
  by (import hollight UNION_OVER_INTER)

lemma INTER_OVER_UNION: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type => bool.
   hollight.UNION x (hollight.INTER xa xb) =
   hollight.INTER (hollight.UNION x xa) (hollight.UNION x xb)"
  by (import hollight INTER_OVER_UNION)

lemma IN_DISJOINT: "ALL (x::'A::type => bool) xa::'A::type => bool.
   DISJOINT x xa = (~ (EX xb::'A::type. IN xb x & IN xb xa))"
  by (import hollight IN_DISJOINT)

lemma DISJOINT_SYM: "ALL (x::'A::type => bool) xa::'A::type => bool.
   DISJOINT x xa = DISJOINT xa x"
  by (import hollight DISJOINT_SYM)

lemma DISJOINT_EMPTY: "ALL x::'A::type => bool. DISJOINT EMPTY x & DISJOINT x EMPTY"
  by (import hollight DISJOINT_EMPTY)

lemma DISJOINT_EMPTY_REFL: "ALL x::'A::type => bool. (x = EMPTY) = DISJOINT x x"
  by (import hollight DISJOINT_EMPTY_REFL)

lemma DISJOINT_UNION: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type => bool.
   DISJOINT (hollight.UNION x xa) xb = (DISJOINT x xb & DISJOINT xa xb)"
  by (import hollight DISJOINT_UNION)

lemma DIFF_EMPTY: "ALL x::'A::type => bool. DIFF x EMPTY = x"
  by (import hollight DIFF_EMPTY)

lemma EMPTY_DIFF: "ALL x::'A::type => bool. DIFF EMPTY x = EMPTY"
  by (import hollight EMPTY_DIFF)

lemma DIFF_UNIV: "ALL x::'A::type => bool. DIFF x hollight.UNIV = EMPTY"
  by (import hollight DIFF_UNIV)

lemma DIFF_DIFF: "ALL (x::'A::type => bool) xa::'A::type => bool.
   DIFF (DIFF x xa) xa = DIFF x xa"
  by (import hollight DIFF_DIFF)

lemma DIFF_EQ_EMPTY: "ALL x::'A::type => bool. DIFF x x = EMPTY"
  by (import hollight DIFF_EQ_EMPTY)

lemma SUBSET_DIFF: "ALL (x::'q_38897::type => bool) xa::'q_38897::type => bool.
   SUBSET (DIFF x xa) x"
  by (import hollight SUBSET_DIFF)

lemma COMPONENT: "ALL (x::'A::type) s::'A::type => bool. IN x (INSERT x s)"
  by (import hollight COMPONENT)

lemma DECOMPOSITION: "ALL (s::'A::type => bool) x::'A::type.
   IN x s = (EX t::'A::type => bool. s = INSERT x t & ~ IN x t)"
  by (import hollight DECOMPOSITION)

lemma SET_CASES: "ALL s::'A::type => bool.
   s = EMPTY |
   (EX (x::'A::type) t::'A::type => bool. s = INSERT x t & ~ IN x t)"
  by (import hollight SET_CASES)

lemma ABSORPTION: "ALL (x::'A::type) xa::'A::type => bool. IN x xa = (INSERT x xa = xa)"
  by (import hollight ABSORPTION)

lemma INSERT_INSERT: "ALL (x::'A::type) xa::'A::type => bool. INSERT x (INSERT x xa) = INSERT x xa"
  by (import hollight INSERT_INSERT)

lemma INSERT_COMM: "ALL (x::'A::type) (xa::'A::type) xb::'A::type => bool.
   INSERT x (INSERT xa xb) = INSERT xa (INSERT x xb)"
  by (import hollight INSERT_COMM)

lemma INSERT_UNIV: "ALL x::'A::type. INSERT x hollight.UNIV = hollight.UNIV"
  by (import hollight INSERT_UNIV)

lemma NOT_INSERT_EMPTY: "ALL (x::'A::type) xa::'A::type => bool. INSERT x xa ~= EMPTY"
  by (import hollight NOT_INSERT_EMPTY)

lemma NOT_EMPTY_INSERT: "ALL (x::'A::type) xa::'A::type => bool. EMPTY ~= INSERT x xa"
  by (import hollight NOT_EMPTY_INSERT)

lemma INSERT_UNION: "ALL (x::'A::type) (s::'A::type => bool) t::'A::type => bool.
   hollight.UNION (INSERT x s) t =
   COND (IN x t) (hollight.UNION s t) (INSERT x (hollight.UNION s t))"
  by (import hollight INSERT_UNION)

lemma INSERT_UNION_EQ: "ALL (x::'A::type) (xa::'A::type => bool) xb::'A::type => bool.
   hollight.UNION (INSERT x xa) xb = INSERT x (hollight.UNION xa xb)"
  by (import hollight INSERT_UNION_EQ)

lemma INSERT_INTER: "ALL (x::'A::type) (s::'A::type => bool) t::'A::type => bool.
   hollight.INTER (INSERT x s) t =
   COND (IN x t) (INSERT x (hollight.INTER s t)) (hollight.INTER s t)"
  by (import hollight INSERT_INTER)

lemma DISJOINT_INSERT: "ALL (x::'A::type) (xa::'A::type => bool) xb::'A::type => bool.
   DISJOINT (INSERT x xa) xb = (DISJOINT xa xb & ~ IN x xb)"
  by (import hollight DISJOINT_INSERT)

lemma INSERT_SUBSET: "ALL (x::'A::type) (xa::'A::type => bool) xb::'A::type => bool.
   SUBSET (INSERT x xa) xb = (IN x xb & SUBSET xa xb)"
  by (import hollight INSERT_SUBSET)

lemma SUBSET_INSERT: "ALL (x::'A::type) xa::'A::type => bool.
   ~ IN x xa -->
   (ALL xb::'A::type => bool. SUBSET xa (INSERT x xb) = SUBSET xa xb)"
  by (import hollight SUBSET_INSERT)

lemma INSERT_DIFF: "ALL (s::'A::type => bool) (t::'A::type => bool) x::'A::type.
   DIFF (INSERT x s) t = COND (IN x t) (DIFF s t) (INSERT x (DIFF s t))"
  by (import hollight INSERT_DIFF)

lemma INSERT_AC: "INSERT (x::'q_39353::type)
 (INSERT (y::'q_39353::type) (s::'q_39353::type => bool)) =
INSERT y (INSERT x s) &
INSERT x (INSERT x s) = INSERT x s"
  by (import hollight INSERT_AC)

lemma INTER_ACI: "hollight.INTER (p::'q_39420::type => bool) (q::'q_39420::type => bool) =
hollight.INTER q p &
hollight.INTER (hollight.INTER p q) (r::'q_39420::type => bool) =
hollight.INTER p (hollight.INTER q r) &
hollight.INTER p (hollight.INTER q r) =
hollight.INTER q (hollight.INTER p r) &
hollight.INTER p p = p &
hollight.INTER p (hollight.INTER p q) = hollight.INTER p q"
  by (import hollight INTER_ACI)

lemma UNION_ACI: "hollight.UNION (p::'q_39486::type => bool) (q::'q_39486::type => bool) =
hollight.UNION q p &
hollight.UNION (hollight.UNION p q) (r::'q_39486::type => bool) =
hollight.UNION p (hollight.UNION q r) &
hollight.UNION p (hollight.UNION q r) =
hollight.UNION q (hollight.UNION p r) &
hollight.UNION p p = p &
hollight.UNION p (hollight.UNION p q) = hollight.UNION p q"
  by (import hollight UNION_ACI)

lemma DELETE_NON_ELEMENT: "ALL (x::'A::type) xa::'A::type => bool. (~ IN x xa) = (DELETE xa x = xa)"
  by (import hollight DELETE_NON_ELEMENT)

lemma IN_DELETE_EQ: "ALL (s::'A::type => bool) (x::'A::type) x'::'A::type.
   (IN x s = IN x' s) = (IN x (DELETE s x') = IN x' (DELETE s x))"
  by (import hollight IN_DELETE_EQ)

lemma EMPTY_DELETE: "ALL x::'A::type. DELETE EMPTY x = EMPTY"
  by (import hollight EMPTY_DELETE)

lemma DELETE_DELETE: "ALL (x::'A::type) xa::'A::type => bool. DELETE (DELETE xa x) x = DELETE xa x"
  by (import hollight DELETE_DELETE)

lemma DELETE_COMM: "ALL (x::'A::type) (xa::'A::type) xb::'A::type => bool.
   DELETE (DELETE xb x) xa = DELETE (DELETE xb xa) x"
  by (import hollight DELETE_COMM)

lemma DELETE_SUBSET: "ALL (x::'A::type) xa::'A::type => bool. SUBSET (DELETE xa x) xa"
  by (import hollight DELETE_SUBSET)

lemma SUBSET_DELETE: "ALL (x::'A::type) (xa::'A::type => bool) xb::'A::type => bool.
   SUBSET xa (DELETE xb x) = (~ IN x xa & SUBSET xa xb)"
  by (import hollight SUBSET_DELETE)

lemma SUBSET_INSERT_DELETE: "ALL (x::'A::type) (xa::'A::type => bool) xb::'A::type => bool.
   SUBSET xa (INSERT x xb) = SUBSET (DELETE xa x) xb"
  by (import hollight SUBSET_INSERT_DELETE)

lemma DIFF_INSERT: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type.
   DIFF x (INSERT xb xa) = DIFF (DELETE x xb) xa"
  by (import hollight DIFF_INSERT)

lemma PSUBSET_INSERT_SUBSET: "ALL (x::'A::type => bool) xa::'A::type => bool.
   PSUBSET x xa = (EX xb::'A::type. ~ IN xb x & SUBSET (INSERT xb x) xa)"
  by (import hollight PSUBSET_INSERT_SUBSET)

lemma PSUBSET_MEMBER: "ALL (x::'A::type => bool) xa::'A::type => bool.
   PSUBSET x xa = (SUBSET x xa & (EX y::'A::type. IN y xa & ~ IN y x))"
  by (import hollight PSUBSET_MEMBER)

lemma DELETE_INSERT: "ALL (x::'A::type) (y::'A::type) s::'A::type => bool.
   DELETE (INSERT x s) y = COND (x = y) (DELETE s y) (INSERT x (DELETE s y))"
  by (import hollight DELETE_INSERT)

lemma INSERT_DELETE: "ALL (x::'A::type) xa::'A::type => bool.
   IN x xa --> INSERT x (DELETE xa x) = xa"
  by (import hollight INSERT_DELETE)

lemma DELETE_INTER: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type.
   hollight.INTER (DELETE x xb) xa = DELETE (hollight.INTER x xa) xb"
  by (import hollight DELETE_INTER)

lemma DISJOINT_DELETE_SYM: "ALL (x::'A::type => bool) (xa::'A::type => bool) xb::'A::type.
   DISJOINT (DELETE x xb) xa = DISJOINT (DELETE xa xb) x"
  by (import hollight DISJOINT_DELETE_SYM)

lemma UNIONS_0: "(op =::('q_39893::type => bool) => ('q_39893::type => bool) => bool)
 ((UNIONS::(('q_39893::type => bool) => bool) => 'q_39893::type => bool)
   (EMPTY::('q_39893::type => bool) => bool))
 (EMPTY::'q_39893::type => bool)"
  by (import hollight UNIONS_0)

lemma UNIONS_1: "UNIONS (INSERT (s::'q_39899::type => bool) EMPTY) = s"
  by (import hollight UNIONS_1)

lemma UNIONS_2: "UNIONS
 (INSERT (s::'q_39919::type => bool)
   (INSERT (t::'q_39919::type => bool) EMPTY)) =
hollight.UNION s t"
  by (import hollight UNIONS_2)

lemma UNIONS_INSERT: "UNIONS
 (INSERT (s::'q_39933::type => bool)
   (u::('q_39933::type => bool) => bool)) =
hollight.UNION s (UNIONS u)"
  by (import hollight UNIONS_INSERT)

lemma FORALL_IN_UNIONS: "ALL (x::'q_39975::type => bool) xa::('q_39975::type => bool) => bool.
   (ALL xb::'q_39975::type. IN xb (UNIONS xa) --> x xb) =
   (ALL (t::'q_39975::type => bool) xb::'q_39975::type.
       IN t xa & IN xb t --> x xb)"
  by (import hollight FORALL_IN_UNIONS)

lemma EMPTY_UNIONS: "ALL x::('q_40001::type => bool) => bool.
   (UNIONS x = EMPTY) =
   (ALL xa::'q_40001::type => bool. IN xa x --> xa = EMPTY)"
  by (import hollight EMPTY_UNIONS)

lemma IMAGE_CLAUSES: "IMAGE (f::'q_40027::type => 'q_40031::type) EMPTY = EMPTY &
IMAGE f (INSERT (x::'q_40027::type) (s::'q_40027::type => bool)) =
INSERT (f x) (IMAGE f s)"
  by (import hollight IMAGE_CLAUSES)

lemma IMAGE_UNION: "ALL (x::'q_40054::type => 'q_40065::type) (xa::'q_40054::type => bool)
   xb::'q_40054::type => bool.
   IMAGE x (hollight.UNION xa xb) = hollight.UNION (IMAGE x xa) (IMAGE x xb)"
  by (import hollight IMAGE_UNION)

lemma IMAGE_o: "ALL (x::'q_40098::type => 'q_40094::type)
   (xa::'q_40089::type => 'q_40098::type) xb::'q_40089::type => bool.
   IMAGE (x o xa) xb = IMAGE x (IMAGE xa xb)"
  by (import hollight IMAGE_o)

lemma IMAGE_SUBSET: "ALL (x::'q_40116::type => 'q_40127::type) (xa::'q_40116::type => bool)
   xb::'q_40116::type => bool.
   SUBSET xa xb --> SUBSET (IMAGE x xa) (IMAGE x xb)"
  by (import hollight IMAGE_SUBSET)

lemma IMAGE_DIFF_INJ: "(ALL (x::'q_40158::type) y::'q_40158::type.
    (f::'q_40158::type => 'q_40169::type) x = f y --> x = y) -->
IMAGE f (DIFF (s::'q_40158::type => bool) (t::'q_40158::type => bool)) =
DIFF (IMAGE f s) (IMAGE f t)"
  by (import hollight IMAGE_DIFF_INJ)

lemma IMAGE_DELETE_INJ: "(ALL x::'q_40204::type.
    (f::'q_40204::type => 'q_40203::type) x = f (a::'q_40204::type) -->
    x = a) -->
IMAGE f (DELETE (s::'q_40204::type => bool) a) = DELETE (IMAGE f s) (f a)"
  by (import hollight IMAGE_DELETE_INJ)

lemma IMAGE_EQ_EMPTY: "ALL (x::'q_40227::type => 'q_40223::type) xa::'q_40227::type => bool.
   (IMAGE x xa = EMPTY) = (xa = EMPTY)"
  by (import hollight IMAGE_EQ_EMPTY)

lemma FORALL_IN_IMAGE: "ALL (x::'q_40263::type => 'q_40262::type) xa::'q_40263::type => bool.
   (ALL xb::'q_40262::type.
       IN xb (IMAGE x xa) --> (P::'q_40262::type => bool) xb) =
   (ALL xb::'q_40263::type. IN xb xa --> P (x xb))"
  by (import hollight FORALL_IN_IMAGE)

lemma EXISTS_IN_IMAGE: "ALL (x::'q_40299::type => 'q_40298::type) xa::'q_40299::type => bool.
   (EX xb::'q_40298::type.
       IN xb (IMAGE x xa) & (P::'q_40298::type => bool) xb) =
   (EX xb::'q_40299::type. IN xb xa & P (x xb))"
  by (import hollight EXISTS_IN_IMAGE)

lemma SUBSET_IMAGE: "ALL (f::'A::type => 'B::type) (s::'B::type => bool) t::'A::type => bool.
   SUBSET s (IMAGE f t) =
   (EX x::'A::type => bool. SUBSET x t & s = IMAGE f x)"
  by (import hollight SUBSET_IMAGE)

lemma IMAGE_CONST: "ALL (s::'q_40385::type => bool) c::'q_40390::type.
   IMAGE (%x::'q_40385::type. c) s = COND (s = EMPTY) EMPTY (INSERT c EMPTY)"
  by (import hollight IMAGE_CONST)

lemma SIMPLE_IMAGE: "ALL (x::'q_40418::type => 'q_40422::type) xa::'q_40418::type => bool.
   GSPEC
    (%u::'q_40422::type.
        EX xb::'q_40418::type. SETSPEC u (IN xb xa) (x xb)) =
   IMAGE x xa"
  by (import hollight SIMPLE_IMAGE)

lemma EMPTY_GSPEC: "GSPEC (%u::'q_40439::type. Ex (SETSPEC u False)) = EMPTY"
  by (import hollight EMPTY_GSPEC)

lemma FINITE_INDUCT_STRONG: "ALL P::('A::type => bool) => bool.
   P EMPTY &
   (ALL (x::'A::type) s::'A::type => bool.
       P s & ~ IN x s & FINITE s --> P (INSERT x s)) -->
   (ALL s::'A::type => bool. FINITE s --> P s)"
  by (import hollight FINITE_INDUCT_STRONG)

lemma FINITE_SUBSET: "ALL (x::'A::type => bool) t::'A::type => bool.
   FINITE t & SUBSET x t --> FINITE x"
  by (import hollight FINITE_SUBSET)

lemma FINITE_UNION_IMP: "ALL (x::'A::type => bool) xa::'A::type => bool.
   FINITE x & FINITE xa --> FINITE (hollight.UNION x xa)"
  by (import hollight FINITE_UNION_IMP)

lemma FINITE_UNION: "ALL (s::'A::type => bool) t::'A::type => bool.
   FINITE (hollight.UNION s t) = (FINITE s & FINITE t)"
  by (import hollight FINITE_UNION)

lemma FINITE_INTER: "ALL (s::'A::type => bool) t::'A::type => bool.
   FINITE s | FINITE t --> FINITE (hollight.INTER s t)"
  by (import hollight FINITE_INTER)

lemma FINITE_INSERT: "ALL (s::'A::type => bool) x::'A::type. FINITE (INSERT x s) = FINITE s"
  by (import hollight FINITE_INSERT)

lemma FINITE_DELETE_IMP: "ALL (s::'A::type => bool) x::'A::type. FINITE s --> FINITE (DELETE s x)"
  by (import hollight FINITE_DELETE_IMP)

lemma FINITE_DELETE: "ALL (s::'A::type => bool) x::'A::type. FINITE (DELETE s x) = FINITE s"
  by (import hollight FINITE_DELETE)

lemma FINITE_UNIONS: "ALL s::('q_40774::type => bool) => bool.
   FINITE s -->
   FINITE (UNIONS s) = (ALL t::'q_40774::type => bool. IN t s --> FINITE t)"
  by (import hollight FINITE_UNIONS)

lemma FINITE_IMAGE_EXPAND: "ALL (f::'A::type => 'B::type) s::'A::type => bool.
   FINITE s -->
   FINITE
    (GSPEC
      (%u::'B::type.
          EX y::'B::type. SETSPEC u (EX x::'A::type. IN x s & y = f x) y))"
  by (import hollight FINITE_IMAGE_EXPAND)

lemma FINITE_IMAGE: "ALL (x::'A::type => 'B::type) xa::'A::type => bool.
   FINITE xa --> FINITE (IMAGE x xa)"
  by (import hollight FINITE_IMAGE)

lemma FINITE_IMAGE_INJ_GENERAL: "ALL (f::'A::type => 'B::type) (x::'B::type => bool) s::'A::type => bool.
   (ALL (x::'A::type) y::'A::type. IN x s & IN y s & f x = f y --> x = y) &
   FINITE x -->
   FINITE
    (GSPEC
      (%u::'A::type. EX xa::'A::type. SETSPEC u (IN xa s & IN (f xa) x) xa))"
  by (import hollight FINITE_IMAGE_INJ_GENERAL)

lemma FINITE_IMAGE_INJ: "ALL (f::'A::type => 'B::type) A::'B::type => bool.
   (ALL (x::'A::type) y::'A::type. f x = f y --> x = y) & FINITE A -->
   FINITE (GSPEC (%u::'A::type. EX x::'A::type. SETSPEC u (IN (f x) A) x))"
  by (import hollight FINITE_IMAGE_INJ)

lemma INFINITE_IMAGE_INJ: "ALL f::'A::type => 'B::type.
   (ALL (x::'A::type) y::'A::type. f x = f y --> x = y) -->
   (ALL s::'A::type => bool. INFINITE s --> INFINITE (IMAGE f s))"
  by (import hollight INFINITE_IMAGE_INJ)

lemma INFINITE_NONEMPTY: "ALL s::'q_41257::type => bool. INFINITE s --> s ~= EMPTY"
  by (import hollight INFINITE_NONEMPTY)

lemma INFINITE_DIFF_FINITE: "ALL (s::'A::type => bool) t::'A::type => bool.
   INFINITE s & FINITE t --> INFINITE (DIFF s t)"
  by (import hollight INFINITE_DIFF_FINITE)

lemma FINITE_SUBSET_IMAGE: "ALL (f::'A::type => 'B::type) (s::'A::type => bool) t::'B::type => bool.
   (FINITE t & SUBSET t (IMAGE f s)) =
   (EX x::'A::type => bool. FINITE x & SUBSET x s & t = IMAGE f x)"
  by (import hollight FINITE_SUBSET_IMAGE)

lemma FINITE_SUBSET_IMAGE_IMP: "ALL (f::'A::type => 'B::type) (s::'A::type => bool) t::'B::type => bool.
   FINITE t & SUBSET t (IMAGE f s) -->
   (EX s'::'A::type => bool.
       FINITE s' & SUBSET s' s & SUBSET t (IMAGE f s'))"
  by (import hollight FINITE_SUBSET_IMAGE_IMP)

lemma FINITE_SUBSETS: "ALL s::'A::type => bool.
   FINITE s -->
   FINITE
    (GSPEC
      (%u::'A::type => bool.
          EX t::'A::type => bool. SETSPEC u (SUBSET t s) t))"
  by (import hollight FINITE_SUBSETS)

lemma FINITE_DIFF: "ALL (s::'q_41555::type => bool) t::'q_41555::type => bool.
   FINITE s --> FINITE (DIFF s t)"
  by (import hollight FINITE_DIFF)

constdefs
  FINREC :: "('q_41615 => 'q_41614 => 'q_41614)
=> 'q_41614 => ('q_41615 => bool) => 'q_41614 => nat => bool" 
  "FINREC ==
SOME FINREC::('q_41615::type => 'q_41614::type => 'q_41614::type)
             => 'q_41614::type
                => ('q_41615::type => bool)
                   => 'q_41614::type => nat => bool.
   (ALL (f::'q_41615::type => 'q_41614::type => 'q_41614::type)
       (s::'q_41615::type => bool) (a::'q_41614::type) b::'q_41614::type.
       FINREC f b s a 0 = (s = EMPTY & a = b)) &
   (ALL (b::'q_41614::type) (s::'q_41615::type => bool) (n::nat)
       (a::'q_41614::type)
       f::'q_41615::type => 'q_41614::type => 'q_41614::type.
       FINREC f b s a (Suc n) =
       (EX (x::'q_41615::type) c::'q_41614::type.
           IN x s & FINREC f b (DELETE s x) c n & a = f x c))"

lemma DEF_FINREC: "FINREC =
(SOME FINREC::('q_41615::type => 'q_41614::type => 'q_41614::type)
              => 'q_41614::type
                 => ('q_41615::type => bool)
                    => 'q_41614::type => nat => bool.
    (ALL (f::'q_41615::type => 'q_41614::type => 'q_41614::type)
        (s::'q_41615::type => bool) (a::'q_41614::type) b::'q_41614::type.
        FINREC f b s a 0 = (s = EMPTY & a = b)) &
    (ALL (b::'q_41614::type) (s::'q_41615::type => bool) (n::nat)
        (a::'q_41614::type)
        f::'q_41615::type => 'q_41614::type => 'q_41614::type.
        FINREC f b s a (Suc n) =
        (EX (x::'q_41615::type) c::'q_41614::type.
            IN x s & FINREC f b (DELETE s x) c n & a = f x c)))"
  by (import hollight DEF_FINREC)

lemma FINREC_1_LEMMA: "ALL (x::'q_41660::type => 'q_41659::type => 'q_41659::type)
   (xa::'q_41659::type) (xb::'q_41660::type => bool) xc::'q_41659::type.
   FINREC x xa xb xc (Suc 0) =
   (EX xd::'q_41660::type. xb = INSERT xd EMPTY & xc = x xd xa)"
  by (import hollight FINREC_1_LEMMA)

lemma FINREC_SUC_LEMMA: "ALL (f::'A::type => 'B::type => 'B::type) b::'B::type.
   (ALL (x::'A::type) (y::'A::type) s::'B::type.
       x ~= y --> f x (f y s) = f y (f x s)) -->
   (ALL (n::nat) (s::'A::type => bool) z::'B::type.
       FINREC f b s z (Suc n) -->
       (ALL x::'A::type.
           IN x s -->
           (EX w::'B::type. FINREC f b (DELETE s x) w n & z = f x w)))"
  by (import hollight FINREC_SUC_LEMMA)

lemma FINREC_UNIQUE_LEMMA: "ALL (f::'A::type => 'B::type => 'B::type) b::'B::type.
   (ALL (x::'A::type) (y::'A::type) s::'B::type.
       x ~= y --> f x (f y s) = f y (f x s)) -->
   (ALL (n1::nat) (n2::nat) (s::'A::type => bool) (a1::'B::type)
       a2::'B::type.
       FINREC f b s a1 n1 & FINREC f b s a2 n2 --> a1 = a2 & n1 = n2)"
  by (import hollight FINREC_UNIQUE_LEMMA)

lemma FINREC_EXISTS_LEMMA: "ALL (f::'A::type => 'B::type => 'B::type) (b::'B::type) s::'A::type => bool.
   FINITE s --> (EX a::'B::type. Ex (FINREC f b s a))"
  by (import hollight FINREC_EXISTS_LEMMA)

lemma FINREC_FUN_LEMMA: "ALL (P::'A::type => bool) R::'A::type => 'B::type => 'C::type => bool.
   (ALL s::'A::type. P s --> (EX a::'B::type. Ex (R s a))) &
   (ALL (n1::'C::type) (n2::'C::type) (s::'A::type) (a1::'B::type)
       a2::'B::type. R s a1 n1 & R s a2 n2 --> a1 = a2 & n1 = n2) -->
   (EX x::'A::type => 'B::type.
       ALL (s::'A::type) a::'B::type. P s --> Ex (R s a) = (x s = a))"
  by (import hollight FINREC_FUN_LEMMA)

lemma FINREC_FUN: "ALL (f::'A::type => 'B::type => 'B::type) b::'B::type.
   (ALL (x::'A::type) (y::'A::type) s::'B::type.
       x ~= y --> f x (f y s) = f y (f x s)) -->
   (EX g::('A::type => bool) => 'B::type.
       g EMPTY = b &
       (ALL (s::'A::type => bool) x::'A::type.
           FINITE s & IN x s --> g s = f x (g (DELETE s x))))"
  by (import hollight FINREC_FUN)

lemma SET_RECURSION_LEMMA: "ALL (f::'A::type => 'B::type => 'B::type) b::'B::type.
   (ALL (x::'A::type) (y::'A::type) s::'B::type.
       x ~= y --> f x (f y s) = f y (f x s)) -->
   (EX g::('A::type => bool) => 'B::type.
       g EMPTY = b &
       (ALL (x::'A::type) s::'A::type => bool.
           FINITE s --> g (INSERT x s) = COND (IN x s) (g s) (f x (g s))))"
  by (import hollight SET_RECURSION_LEMMA)

constdefs
  ITSET :: "('q_42316 => 'q_42315 => 'q_42315)
=> ('q_42316 => bool) => 'q_42315 => 'q_42315" 
  "ITSET ==
%(u::'q_42316::type => 'q_42315::type => 'q_42315::type)
   (ua::'q_42316::type => bool) ub::'q_42315::type.
   (SOME g::('q_42316::type => bool) => 'q_42315::type.
       g EMPTY = ub &
       (ALL (x::'q_42316::type) s::'q_42316::type => bool.
           FINITE s --> g (INSERT x s) = COND (IN x s) (g s) (u x (g s))))
    ua"

lemma DEF_ITSET: "ITSET =
(%(u::'q_42316::type => 'q_42315::type => 'q_42315::type)
    (ua::'q_42316::type => bool) ub::'q_42315::type.
    (SOME g::('q_42316::type => bool) => 'q_42315::type.
        g EMPTY = ub &
        (ALL (x::'q_42316::type) s::'q_42316::type => bool.
            FINITE s --> g (INSERT x s) = COND (IN x s) (g s) (u x (g s))))
     ua)"
  by (import hollight DEF_ITSET)

lemma FINITE_RECURSION: "ALL (f::'A::type => 'B::type => 'B::type) b::'B::type.
   (ALL (x::'A::type) (y::'A::type) s::'B::type.
       x ~= y --> f x (f y s) = f y (f x s)) -->
   ITSET f EMPTY b = b &
   (ALL (x::'A::type) xa::'A::type => bool.
       FINITE xa -->
       ITSET f (INSERT x xa) b =
       COND (IN x xa) (ITSET f xa b) (f x (ITSET f xa b)))"
  by (import hollight FINITE_RECURSION)

lemma FINITE_RECURSION_DELETE: "ALL (f::'A::type => 'B::type => 'B::type) b::'B::type.
   (ALL (x::'A::type) (y::'A::type) s::'B::type.
       x ~= y --> f x (f y s) = f y (f x s)) -->
   ITSET f EMPTY b = b &
   (ALL (x::'A::type) s::'A::type => bool.
       FINITE s -->
       ITSET f s b =
       COND (IN x s) (f x (ITSET f (DELETE s x) b))
        (ITSET f (DELETE s x) b))"
  by (import hollight FINITE_RECURSION_DELETE)

lemma ITSET_EQ: "ALL (x::'q_42621::type => bool)
   (xa::'q_42621::type => 'q_42622::type => 'q_42622::type)
   (xb::'q_42621::type => 'q_42622::type => 'q_42622::type)
   xc::'q_42622::type.
   FINITE x &
   (ALL xc::'q_42621::type. IN xc x --> xa xc = xb xc) &
   (ALL (x::'q_42621::type) (y::'q_42621::type) s::'q_42622::type.
       x ~= y --> xa x (xa y s) = xa y (xa x s)) &
   (ALL (x::'q_42621::type) (y::'q_42621::type) s::'q_42622::type.
       x ~= y --> xb x (xb y s) = xb y (xb x s)) -->
   ITSET xa x xc = ITSET xb x xc"
  by (import hollight ITSET_EQ)

lemma SUBSET_RESTRICT: "ALL (x::'q_42655::type => bool) xa::'q_42655::type => bool.
   SUBSET
    (GSPEC
      (%u::'q_42655::type.
          EX xb::'q_42655::type. SETSPEC u (IN xb x & xa xb) xb))
    x"
  by (import hollight SUBSET_RESTRICT)

lemma FINITE_RESTRICT: "ALL (s::'A::type => bool) p::'q_42673::type.
   FINITE s -->
   FINITE
    (GSPEC
      (%u::'A::type.
          EX x::'A::type. SETSPEC u (IN x s & (P::'A::type => bool) x) x))"
  by (import hollight FINITE_RESTRICT)

constdefs
  CARD :: "('q_42709 => bool) => nat" 
  "CARD == %u::'q_42709::type => bool. ITSET (%x::'q_42709::type. Suc) u 0"

lemma DEF_CARD: "CARD = (%u::'q_42709::type => bool. ITSET (%x::'q_42709::type. Suc) u 0)"
  by (import hollight DEF_CARD)

lemma CARD_CLAUSES: "(op &::bool => bool => bool)
 ((op =::nat => nat => bool)
   ((CARD::('A::type => bool) => nat) (EMPTY::'A::type => bool)) (0::nat))
 ((All::('A::type => bool) => bool)
   (%x::'A::type.
       (All::(('A::type => bool) => bool) => bool)
        (%s::'A::type => bool.
            (op -->::bool => bool => bool)
             ((FINITE::('A::type => bool) => bool) s)
             ((op =::nat => nat => bool)
               ((CARD::('A::type => bool) => nat)
                 ((INSERT::'A::type
                           => ('A::type => bool) => 'A::type => bool)
                   x s))
               ((COND::bool => nat => nat => nat)
                 ((IN::'A::type => ('A::type => bool) => bool) x s)
                 ((CARD::('A::type => bool) => nat) s)
                 ((Suc::nat => nat)
                   ((CARD::('A::type => bool) => nat) s)))))))"
  by (import hollight CARD_CLAUSES)

lemma CARD_UNION: "ALL (x::'A::type => bool) xa::'A::type => bool.
   FINITE x & FINITE xa & hollight.INTER x xa = EMPTY -->
   CARD (hollight.UNION x xa) = CARD x + CARD xa"
  by (import hollight CARD_UNION)

lemma CARD_DELETE: "ALL (x::'A::type) s::'A::type => bool.
   FINITE s -->
   CARD (DELETE s x) = COND (IN x s) (CARD s - NUMERAL_BIT1 0) (CARD s)"
  by (import hollight CARD_DELETE)

lemma CARD_UNION_EQ: "ALL (s::'q_42954::type => bool) (t::'q_42954::type => bool)
   u::'q_42954::type => bool.
   FINITE u & hollight.INTER s t = EMPTY & hollight.UNION s t = u -->
   CARD s + CARD t = CARD u"
  by (import hollight CARD_UNION_EQ)

constdefs
  HAS_SIZE :: "('q_42990 => bool) => nat => bool" 
  "HAS_SIZE == %(u::'q_42990::type => bool) ua::nat. FINITE u & CARD u = ua"

lemma DEF_HAS_SIZE: "HAS_SIZE = (%(u::'q_42990::type => bool) ua::nat. FINITE u & CARD u = ua)"
  by (import hollight DEF_HAS_SIZE)

lemma HAS_SIZE_CARD: "ALL (x::'q_43009::type => bool) xa::nat. HAS_SIZE x xa --> CARD x = xa"
  by (import hollight HAS_SIZE_CARD)

lemma HAS_SIZE_0: "ALL (s::'A::type => bool) n::'q_43025::type. HAS_SIZE s 0 = (s = EMPTY)"
  by (import hollight HAS_SIZE_0)

lemma HAS_SIZE_SUC: "ALL (s::'A::type => bool) n::nat.
   HAS_SIZE s (Suc n) =
   (s ~= EMPTY & (ALL x::'A::type. IN x s --> HAS_SIZE (DELETE s x) n))"
  by (import hollight HAS_SIZE_SUC)

lemma HAS_SIZE_UNION: "ALL (x::'q_43147::type => bool) (xa::'q_43147::type => bool) (xb::nat)
   xc::nat.
   HAS_SIZE x xb & HAS_SIZE xa xc & DISJOINT x xa -->
   HAS_SIZE (hollight.UNION x xa) (xb + xc)"
  by (import hollight HAS_SIZE_UNION)

lemma HAS_SIZE_UNIONS: "ALL (x::'A::type => bool) (xa::'A::type => 'B::type => bool) (xb::nat)
   xc::nat.
   HAS_SIZE x xb &
   (ALL xb::'A::type. IN xb x --> HAS_SIZE (xa xb) xc) &
   (ALL (xb::'A::type) y::'A::type.
       IN xb x & IN y x & xb ~= y --> DISJOINT (xa xb) (xa y)) -->
   HAS_SIZE
    (UNIONS
      (GSPEC
        (%u::'B::type => bool.
            EX xb::'A::type. SETSPEC u (IN xb x) (xa xb))))
    (xb * xc)"
  by (import hollight HAS_SIZE_UNIONS)

lemma HAS_SIZE_CLAUSES: "HAS_SIZE (s::'q_43395::type => bool) 0 = (s = EMPTY) &
HAS_SIZE s (Suc (n::nat)) =
(EX (a::'q_43395::type) t::'q_43395::type => bool.
    HAS_SIZE t n & ~ IN a t & s = INSERT a t)"
  by (import hollight HAS_SIZE_CLAUSES)

lemma CARD_SUBSET_EQ: "ALL (a::'A::type => bool) b::'A::type => bool.
   FINITE b & SUBSET a b & CARD a = CARD b --> a = b"
  by (import hollight CARD_SUBSET_EQ)

lemma CARD_SUBSET: "ALL (a::'A::type => bool) b::'A::type => bool.
   SUBSET a b & FINITE b --> <= (CARD a) (CARD b)"
  by (import hollight CARD_SUBSET)

lemma CARD_SUBSET_LE: "ALL (a::'A::type => bool) b::'A::type => bool.
   FINITE b & SUBSET a b & <= (CARD b) (CARD a) --> a = b"
  by (import hollight CARD_SUBSET_LE)

lemma CARD_EQ_0: "ALL s::'q_43711::type => bool. FINITE s --> (CARD s = 0) = (s = EMPTY)"
  by (import hollight CARD_EQ_0)

lemma CARD_PSUBSET: "ALL (a::'A::type => bool) b::'A::type => bool.
   PSUBSET a b & FINITE b --> < (CARD a) (CARD b)"
  by (import hollight CARD_PSUBSET)

lemma CARD_UNION_LE: "ALL (s::'A::type => bool) t::'A::type => bool.
   FINITE s & FINITE t --> <= (CARD (hollight.UNION s t)) (CARD s + CARD t)"
  by (import hollight CARD_UNION_LE)

lemma CARD_UNIONS_LE: "ALL (x::'A::type => bool) (xa::'A::type => 'B::type => bool) (xb::nat)
   xc::nat.
   HAS_SIZE x xb &
   (ALL xb::'A::type. IN xb x --> FINITE (xa xb) & <= (CARD (xa xb)) xc) -->
   <= (CARD
        (UNIONS
          (GSPEC
            (%u::'B::type => bool.
                EX xb::'A::type. SETSPEC u (IN xb x) (xa xb)))))
    (xb * xc)"
  by (import hollight CARD_UNIONS_LE)

lemma CARD_IMAGE_INJ: "ALL (f::'A::type => 'B::type) x::'A::type => bool.
   (ALL (xa::'A::type) y::'A::type.
       IN xa x & IN y x & f xa = f y --> xa = y) &
   FINITE x -->
   CARD (IMAGE f x) = CARD x"
  by (import hollight CARD_IMAGE_INJ)

lemma HAS_SIZE_IMAGE_INJ: "ALL (x::'A::type => 'B::type) (xa::'A::type => bool) xb::nat.
   (ALL (xb::'A::type) y::'A::type.
       IN xb xa & IN y xa & x xb = x y --> xb = y) &
   HAS_SIZE xa xb -->
   HAS_SIZE (IMAGE x xa) xb"
  by (import hollight HAS_SIZE_IMAGE_INJ)

lemma CARD_IMAGE_LE: "ALL (f::'A::type => 'B::type) s::'A::type => bool.
   FINITE s --> <= (CARD (IMAGE f s)) (CARD s)"
  by (import hollight CARD_IMAGE_LE)

lemma CHOOSE_SUBSET: "ALL s::'A::type => bool.
   FINITE s -->
   (ALL n::nat.
       <= n (CARD s) -->
       (EX t::'A::type => bool. SUBSET t s & HAS_SIZE t n))"
  by (import hollight CHOOSE_SUBSET)

lemma HAS_SIZE_PRODUCT_DEPENDENT: "ALL (x::'A::type => bool) (xa::nat) (xb::'A::type => 'B::type => bool)
   xc::nat.
   HAS_SIZE x xa & (ALL xa::'A::type. IN xa x --> HAS_SIZE (xb xa) xc) -->
   HAS_SIZE
    (GSPEC
      (%u::'A::type * 'B::type.
          EX (xa::'A::type) y::'B::type.
             SETSPEC u (IN xa x & IN y (xb xa)) (xa, y)))
    (xa * xc)"
  by (import hollight HAS_SIZE_PRODUCT_DEPENDENT)

lemma FINITE_PRODUCT_DEPENDENT: "ALL (x::'A::type => bool) xa::'A::type => 'B::type => bool.
   FINITE x & (ALL xb::'A::type. IN xb x --> FINITE (xa xb)) -->
   FINITE
    (GSPEC
      (%u::'A::type * 'B::type.
          EX (xb::'A::type) y::'B::type.
             SETSPEC u (IN xb x & IN y (xa xb)) (xb, y)))"
  by (import hollight FINITE_PRODUCT_DEPENDENT)

lemma FINITE_PRODUCT: "ALL (x::'A::type => bool) xa::'B::type => bool.
   FINITE x & FINITE xa -->
   FINITE
    (GSPEC
      (%u::'A::type * 'B::type.
          EX (xb::'A::type) y::'B::type.
             SETSPEC u (IN xb x & IN y xa) (xb, y)))"
  by (import hollight FINITE_PRODUCT)

lemma CARD_PRODUCT: "ALL (s::'A::type => bool) t::'B::type => bool.
   FINITE s & FINITE t -->
   CARD
    (GSPEC
      (%u::'A::type * 'B::type.
          EX (x::'A::type) y::'B::type.
             SETSPEC u (IN x s & IN y t) (x, y))) =
   CARD s * CARD t"
  by (import hollight CARD_PRODUCT)

lemma HAS_SIZE_PRODUCT: "ALL (x::'A::type => bool) (xa::nat) (xb::'B::type => bool) xc::nat.
   HAS_SIZE x xa & HAS_SIZE xb xc -->
   HAS_SIZE
    (GSPEC
      (%u::'A::type * 'B::type.
          EX (xa::'A::type) y::'B::type.
             SETSPEC u (IN xa x & IN y xb) (xa, y)))
    (xa * xc)"
  by (import hollight HAS_SIZE_PRODUCT)

lemma HAS_SIZE_FUNSPACE: "ALL (d::'B::type) (n::nat) (t::'B::type => bool) (m::nat)
   s::'A::type => bool.
   HAS_SIZE s m & HAS_SIZE t n -->
   HAS_SIZE
    (GSPEC
      (%u::'A::type => 'B::type.
          EX f::'A::type => 'B::type.
             SETSPEC u
              ((ALL x::'A::type. IN x s --> IN (f x) t) &
               (ALL x::'A::type. ~ IN x s --> f x = d))
              f))
    (EXP n m)"
  by (import hollight HAS_SIZE_FUNSPACE)

lemma CARD_FUNSPACE: "ALL (s::'q_45066::type => bool) t::'q_45063::type => bool.
   FINITE s & FINITE t -->
   CARD
    (GSPEC
      (%u::'q_45066::type => 'q_45063::type.
          EX f::'q_45066::type => 'q_45063::type.
             SETSPEC u
              ((ALL x::'q_45066::type. IN x s --> IN (f x) t) &
               (ALL x::'q_45066::type.
                   ~ IN x s --> f x = (d::'q_45063::type)))
              f)) =
   EXP (CARD t) (CARD s)"
  by (import hollight CARD_FUNSPACE)

lemma FINITE_FUNSPACE: "ALL (s::'q_45132::type => bool) t::'q_45129::type => bool.
   FINITE s & FINITE t -->
   FINITE
    (GSPEC
      (%u::'q_45132::type => 'q_45129::type.
          EX f::'q_45132::type => 'q_45129::type.
             SETSPEC u
              ((ALL x::'q_45132::type. IN x s --> IN (f x) t) &
               (ALL x::'q_45132::type.
                   ~ IN x s --> f x = (d::'q_45129::type)))
              f))"
  by (import hollight FINITE_FUNSPACE)

lemma HAS_SIZE_POWERSET: "ALL (s::'A::type => bool) n::nat.
   HAS_SIZE s n -->
   HAS_SIZE
    (GSPEC
      (%u::'A::type => bool.
          EX t::'A::type => bool. SETSPEC u (SUBSET t s) t))
    (EXP (NUMERAL_BIT0 (NUMERAL_BIT1 0)) n)"
  by (import hollight HAS_SIZE_POWERSET)

lemma CARD_POWERSET: "ALL s::'A::type => bool.
   FINITE s -->
   CARD
    (GSPEC
      (%u::'A::type => bool.
          EX t::'A::type => bool. SETSPEC u (SUBSET t s) t)) =
   EXP (NUMERAL_BIT0 (NUMERAL_BIT1 0)) (CARD s)"
  by (import hollight CARD_POWERSET)

lemma FINITE_POWERSET: "ALL s::'A::type => bool.
   FINITE s -->
   FINITE
    (GSPEC
      (%u::'A::type => bool.
          EX t::'A::type => bool. SETSPEC u (SUBSET t s) t))"
  by (import hollight FINITE_POWERSET)

lemma CARD_GE_REFL: "ALL s::'A::type => bool. CARD_GE s s"
  by (import hollight CARD_GE_REFL)

lemma CARD_GE_TRANS: "ALL (s::'A::type => bool) (t::'B::type => bool) u::'C::type => bool.
   CARD_GE s t & CARD_GE t u --> CARD_GE s u"
  by (import hollight CARD_GE_TRANS)

lemma FINITE_HAS_SIZE_LEMMA: "ALL s::'A::type => bool.
   FINITE s -->
   (EX n::nat. CARD_GE (GSPEC (%u::nat. EX x::nat. SETSPEC u (< x n) x)) s)"
  by (import hollight FINITE_HAS_SIZE_LEMMA)

lemma HAS_SIZE_NUMSEG_LT: "ALL n::nat. HAS_SIZE (GSPEC (%u::nat. EX m::nat. SETSPEC u (< m n) m)) n"
  by (import hollight HAS_SIZE_NUMSEG_LT)

lemma CARD_NUMSEG_LT: "ALL x::nat. CARD (GSPEC (%u::nat. EX m::nat. SETSPEC u (< m x) m)) = x"
  by (import hollight CARD_NUMSEG_LT)

lemma FINITE_NUMSEG_LT: "ALL x::nat. FINITE (GSPEC (%u::nat. EX m::nat. SETSPEC u (< m x) m))"
  by (import hollight FINITE_NUMSEG_LT)

lemma HAS_SIZE_NUMSEG_LE: "ALL x::nat.
   HAS_SIZE (GSPEC (%xa::nat. EX xb::nat. SETSPEC xa (<= xb x) xb))
    (x + NUMERAL_BIT1 0)"
  by (import hollight HAS_SIZE_NUMSEG_LE)

lemma FINITE_NUMSEG_LE: "ALL x::nat. FINITE (GSPEC (%u::nat. EX m::nat. SETSPEC u (<= m x) m))"
  by (import hollight FINITE_NUMSEG_LE)

lemma CARD_NUMSEG_LE: "ALL x::nat.
   CARD (GSPEC (%u::nat. EX m::nat. SETSPEC u (<= m x) m)) =
   x + NUMERAL_BIT1 0"
  by (import hollight CARD_NUMSEG_LE)

lemma num_FINITE: "ALL s::nat => bool. FINITE s = (EX a::nat. ALL x::nat. IN x s --> <= x a)"
  by (import hollight num_FINITE)

lemma num_FINITE_AVOID: "ALL s::nat => bool. FINITE s --> (EX a::nat. ~ IN a s)"
  by (import hollight num_FINITE_AVOID)

lemma num_INFINITE: "(INFINITE::(nat => bool) => bool) (hollight.UNIV::nat => bool)"
  by (import hollight num_INFINITE)

lemma HAS_SIZE_INDEX: "ALL (x::'A::type => bool) n::nat.
   HAS_SIZE x n -->
   (EX f::nat => 'A::type.
       (ALL m::nat. < m n --> IN (f m) x) &
       (ALL xa::'A::type. IN xa x --> (EX! m::nat. < m n & f m = xa)))"
  by (import hollight HAS_SIZE_INDEX)

constdefs
  set_of_list :: "'q_45759 hollight.list => 'q_45759 => bool" 
  "set_of_list ==
SOME set_of_list::'q_45759::type hollight.list => 'q_45759::type => bool.
   set_of_list NIL = EMPTY &
   (ALL (h::'q_45759::type) t::'q_45759::type hollight.list.
       set_of_list (CONS h t) = INSERT h (set_of_list t))"

lemma DEF_set_of_list: "set_of_list =
(SOME set_of_list::'q_45759::type hollight.list => 'q_45759::type => bool.
    set_of_list NIL = EMPTY &
    (ALL (h::'q_45759::type) t::'q_45759::type hollight.list.
        set_of_list (CONS h t) = INSERT h (set_of_list t)))"
  by (import hollight DEF_set_of_list)

constdefs
  list_of_set :: "('q_45777 => bool) => 'q_45777 hollight.list" 
  "list_of_set ==
%u::'q_45777::type => bool.
   SOME l::'q_45777::type hollight.list.
      set_of_list l = u & LENGTH l = CARD u"

lemma DEF_list_of_set: "list_of_set =
(%u::'q_45777::type => bool.
    SOME l::'q_45777::type hollight.list.
       set_of_list l = u & LENGTH l = CARD u)"
  by (import hollight DEF_list_of_set)

lemma LIST_OF_SET_PROPERTIES: "ALL x::'A::type => bool.
   FINITE x -->
   set_of_list (list_of_set x) = x & LENGTH (list_of_set x) = CARD x"
  by (import hollight LIST_OF_SET_PROPERTIES)

lemma SET_OF_LIST_OF_SET: "ALL s::'q_45826::type => bool. FINITE s --> set_of_list (list_of_set s) = s"
  by (import hollight SET_OF_LIST_OF_SET)

lemma LENGTH_LIST_OF_SET: "ALL s::'q_45842::type => bool. FINITE s --> LENGTH (list_of_set s) = CARD s"
  by (import hollight LENGTH_LIST_OF_SET)

lemma MEM_LIST_OF_SET: "ALL s::'A::type => bool.
   FINITE s --> (ALL x::'A::type. MEM x (list_of_set s) = IN x s)"
  by (import hollight MEM_LIST_OF_SET)

lemma FINITE_SET_OF_LIST: "ALL l::'q_45887::type hollight.list. FINITE (set_of_list l)"
  by (import hollight FINITE_SET_OF_LIST)

lemma IN_SET_OF_LIST: "ALL (x::'q_45905::type) l::'q_45905::type hollight.list.
   IN x (set_of_list l) = MEM x l"
  by (import hollight IN_SET_OF_LIST)

lemma SET_OF_LIST_APPEND: "ALL (x::'q_45930::type hollight.list) xa::'q_45930::type hollight.list.
   set_of_list (APPEND x xa) =
   hollight.UNION (set_of_list x) (set_of_list xa)"
  by (import hollight SET_OF_LIST_APPEND)

constdefs
  pairwise :: "('q_45989 => 'q_45989 => bool) => ('q_45989 => bool) => bool" 
  "pairwise ==
%(u::'q_45989::type => 'q_45989::type => bool) ua::'q_45989::type => bool.
   ALL (x::'q_45989::type) y::'q_45989::type.
      IN x ua & IN y ua & x ~= y --> u x y"

lemma DEF_pairwise: "pairwise =
(%(u::'q_45989::type => 'q_45989::type => bool) ua::'q_45989::type => bool.
    ALL (x::'q_45989::type) y::'q_45989::type.
       IN x ua & IN y ua & x ~= y --> u x y)"
  by (import hollight DEF_pairwise)

constdefs
  PAIRWISE :: "('q_46011 => 'q_46011 => bool) => 'q_46011 hollight.list => bool" 
  "PAIRWISE ==
SOME PAIRWISE::('q_46011::type => 'q_46011::type => bool)
               => 'q_46011::type hollight.list => bool.
   (ALL r::'q_46011::type => 'q_46011::type => bool.
       PAIRWISE r NIL = True) &
   (ALL (h::'q_46011::type) (r::'q_46011::type => 'q_46011::type => bool)
       t::'q_46011::type hollight.list.
       PAIRWISE r (CONS h t) = (ALL_list (r h) t & PAIRWISE r t))"

lemma DEF_PAIRWISE: "PAIRWISE =
(SOME PAIRWISE::('q_46011::type => 'q_46011::type => bool)
                => 'q_46011::type hollight.list => bool.
    (ALL r::'q_46011::type => 'q_46011::type => bool.
        PAIRWISE r NIL = True) &
    (ALL (h::'q_46011::type) (r::'q_46011::type => 'q_46011::type => bool)
        t::'q_46011::type hollight.list.
        PAIRWISE r (CONS h t) = (ALL_list (r h) t & PAIRWISE r t)))"
  by (import hollight DEF_PAIRWISE)

typedef (open) ('A) finite_image = "(Collect::('A::type => bool) => 'A::type set)
 (%x::'A::type.
     (op |::bool => bool => bool)
      ((op =::'A::type => 'A::type => bool) x
        ((Eps::('A::type => bool) => 'A::type) (%z::'A::type. True::bool)))
      ((FINITE::('A::type => bool) => bool)
        (hollight.UNIV::'A::type => bool)))"  morphisms "dest_finite_image" "mk_finite_image"
  apply (rule light_ex_imp_nonempty[where t="(Eps::('A::type => bool) => 'A::type)
 (%x::'A::type.
     (op |::bool => bool => bool)
      ((op =::'A::type => 'A::type => bool) x
        ((Eps::('A::type => bool) => 'A::type) (%z::'A::type. True::bool)))
      ((FINITE::('A::type => bool) => bool)
        (hollight.UNIV::'A::type => bool)))"])
  by (import hollight TYDEF_finite_image)

syntax
  dest_finite_image :: _ 

syntax
  mk_finite_image :: _ 

lemmas "TYDEF_finite_image_@intern" = typedef_hol2hollight 
  [where a="a :: 'A finite_image" and r=r ,
   OF type_definition_finite_image]

lemma FINITE_IMAGE_IMAGE: "(op =::('A::type finite_image => bool)
       => ('A::type finite_image => bool) => bool)
 (hollight.UNIV::'A::type finite_image => bool)
 ((IMAGE::('A::type => 'A::type finite_image)
          => ('A::type => bool) => 'A::type finite_image => bool)
   (mk_finite_image::'A::type => 'A::type finite_image)
   ((COND::bool
           => ('A::type => bool) => ('A::type => bool) => 'A::type => bool)
     ((FINITE::('A::type => bool) => bool)
       (hollight.UNIV::'A::type => bool))
     (hollight.UNIV::'A::type => bool)
     ((INSERT::'A::type => ('A::type => bool) => 'A::type => bool)
       ((Eps::('A::type => bool) => 'A::type) (%z::'A::type. True::bool))
       (EMPTY::'A::type => bool))))"
  by (import hollight FINITE_IMAGE_IMAGE)

constdefs
  dimindex :: "('A => bool) => nat" 
  "(op ==::(('A::type => bool) => nat) => (('A::type => bool) => nat) => prop)
 (dimindex::('A::type => bool) => nat)
 (%u::'A::type => bool.
     (COND::bool => nat => nat => nat)
      ((FINITE::('A::type => bool) => bool)
        (hollight.UNIV::'A::type => bool))
      ((CARD::('A::type => bool) => nat) (hollight.UNIV::'A::type => bool))
      ((NUMERAL_BIT1::nat => nat) (0::nat)))"

lemma DEF_dimindex: "(op =::(('A::type => bool) => nat) => (('A::type => bool) => nat) => bool)
 (dimindex::('A::type => bool) => nat)
 (%u::'A::type => bool.
     (COND::bool => nat => nat => nat)
      ((FINITE::('A::type => bool) => bool)
        (hollight.UNIV::'A::type => bool))
      ((CARD::('A::type => bool) => nat) (hollight.UNIV::'A::type => bool))
      ((NUMERAL_BIT1::nat => nat) (0::nat)))"
  by (import hollight DEF_dimindex)

lemma HAS_SIZE_FINITE_IMAGE: "(All::(('A::type => bool) => bool) => bool)
 (%s::'A::type => bool.
     (HAS_SIZE::('A::type finite_image => bool) => nat => bool)
      (hollight.UNIV::'A::type finite_image => bool)
      ((dimindex::('A::type => bool) => nat) s))"
  by (import hollight HAS_SIZE_FINITE_IMAGE)

lemma CARD_FINITE_IMAGE: "(All::(('A::type => bool) => bool) => bool)
 (%s::'A::type => bool.
     (op =::nat => nat => bool)
      ((CARD::('A::type finite_image => bool) => nat)
        (hollight.UNIV::'A::type finite_image => bool))
      ((dimindex::('A::type => bool) => nat) s))"
  by (import hollight CARD_FINITE_IMAGE)

lemma FINITE_FINITE_IMAGE: "(FINITE::('A::type finite_image => bool) => bool)
 (hollight.UNIV::'A::type finite_image => bool)"
  by (import hollight FINITE_FINITE_IMAGE)

lemma DIMINDEX_NONZERO: "ALL s::'A::type => bool. dimindex s ~= 0"
  by (import hollight DIMINDEX_NONZERO)

lemma DIMINDEX_GE_1: "ALL x::'A::type => bool. <= (NUMERAL_BIT1 0) (dimindex x)"
  by (import hollight DIMINDEX_GE_1)

lemma DIMINDEX_FINITE_IMAGE: "ALL (s::'A::type finite_image => bool) t::'A::type => bool.
   dimindex s = dimindex t"
  by (import hollight DIMINDEX_FINITE_IMAGE)

constdefs
  finite_index :: "nat => 'A" 
  "(op ==::(nat => 'A::type) => (nat => 'A::type) => prop)
 (finite_index::nat => 'A::type)
 ((Eps::((nat => 'A::type) => bool) => nat => 'A::type)
   (%f::nat => 'A::type.
       (All::('A::type => bool) => bool)
        (%x::'A::type.
            (Ex1::(nat => bool) => bool)
             (%n::nat.
                 (op &::bool => bool => bool)
                  ((<=::nat => nat => bool)
                    ((NUMERAL_BIT1::nat => nat) (0::nat)) n)
                  ((op &::bool => bool => bool)
                    ((<=::nat => nat => bool) n
                      ((dimindex::('A::type => bool) => nat)
                        (hollight.UNIV::'A::type => bool)))
                    ((op =::'A::type => 'A::type => bool) (f n) x))))))"

lemma DEF_finite_index: "(op =::(nat => 'A::type) => (nat => 'A::type) => bool)
 (finite_index::nat => 'A::type)
 ((Eps::((nat => 'A::type) => bool) => nat => 'A::type)
   (%f::nat => 'A::type.
       (All::('A::type => bool) => bool)
        (%x::'A::type.
            (Ex1::(nat => bool) => bool)
             (%n::nat.
                 (op &::bool => bool => bool)
                  ((<=::nat => nat => bool)
                    ((NUMERAL_BIT1::nat => nat) (0::nat)) n)
                  ((op &::bool => bool => bool)
                    ((<=::nat => nat => bool) n
                      ((dimindex::('A::type => bool) => nat)
                        (hollight.UNIV::'A::type => bool)))
                    ((op =::'A::type => 'A::type => bool) (f n) x))))))"
  by (import hollight DEF_finite_index)

lemma FINITE_INDEX_WORKS_FINITE: "(op -->::bool => bool => bool)
 ((FINITE::('N::type => bool) => bool) (hollight.UNIV::'N::type => bool))
 ((All::('N::type => bool) => bool)
   (%x::'N::type.
       (Ex1::(nat => bool) => bool)
        (%xa::nat.
            (op &::bool => bool => bool)
             ((<=::nat => nat => bool) ((NUMERAL_BIT1::nat => nat) (0::nat))
               xa)
             ((op &::bool => bool => bool)
               ((<=::nat => nat => bool) xa
                 ((dimindex::('N::type => bool) => nat)
                   (hollight.UNIV::'N::type => bool)))
               ((op =::'N::type => 'N::type => bool)
                 ((finite_index::nat => 'N::type) xa) x)))))"
  by (import hollight FINITE_INDEX_WORKS_FINITE)

lemma FINITE_INDEX_WORKS: "(All::('A::type finite_image => bool) => bool)
 (%i::'A::type finite_image.
     (Ex1::(nat => bool) => bool)
      (%n::nat.
          (op &::bool => bool => bool)
           ((<=::nat => nat => bool) ((NUMERAL_BIT1::nat => nat) (0::nat))
             n)
           ((op &::bool => bool => bool)
             ((<=::nat => nat => bool) n
               ((dimindex::('A::type => bool) => nat)
                 (hollight.UNIV::'A::type => bool)))
             ((op =::'A::type finite_image => 'A::type finite_image => bool)
               ((finite_index::nat => 'A::type finite_image) n) i))))"
  by (import hollight FINITE_INDEX_WORKS)

lemma FINITE_INDEX_INJ: "(All::(nat => bool) => bool)
 (%x::nat.
     (All::(nat => bool) => bool)
      (%xa::nat.
          (op -->::bool => bool => bool)
           ((op &::bool => bool => bool)
             ((<=::nat => nat => bool) ((NUMERAL_BIT1::nat => nat) (0::nat))
               x)
             ((op &::bool => bool => bool)
               ((<=::nat => nat => bool) x
                 ((dimindex::('A::type => bool) => nat)
                   (hollight.UNIV::'A::type => bool)))
               ((op &::bool => bool => bool)
                 ((<=::nat => nat => bool)
                   ((NUMERAL_BIT1::nat => nat) (0::nat)) xa)
                 ((<=::nat => nat => bool) xa
                   ((dimindex::('A::type => bool) => nat)
                     (hollight.UNIV::'A::type => bool))))))
           ((op =::bool => bool => bool)
             ((op =::'A::type => 'A::type => bool)
               ((finite_index::nat => 'A::type) x)
               ((finite_index::nat => 'A::type) xa))
             ((op =::nat => nat => bool) x xa))))"
  by (import hollight FINITE_INDEX_INJ)

lemma FORALL_FINITE_INDEX: "(op =::bool => bool => bool)
 ((All::('N::type finite_image => bool) => bool)
   (P::'N::type finite_image => bool))
 ((All::(nat => bool) => bool)
   (%i::nat.
       (op -->::bool => bool => bool)
        ((op &::bool => bool => bool)
          ((<=::nat => nat => bool) ((NUMERAL_BIT1::nat => nat) (0::nat)) i)
          ((<=::nat => nat => bool) i
            ((dimindex::('N::type => bool) => nat)
              (hollight.UNIV::'N::type => bool))))
        (P ((finite_index::nat => 'N::type finite_image) i))))"
  by (import hollight FORALL_FINITE_INDEX)

typedef (open) ('A, 'B) cart = "(Collect::(('B::type finite_image => 'A::type) => bool)
          => ('B::type finite_image => 'A::type) set)
 (%f::'B::type finite_image => 'A::type. True::bool)"  morphisms "dest_cart" "mk_cart"
  apply (rule light_ex_imp_nonempty[where t="(Eps::(('B::type finite_image => 'A::type) => bool)
      => 'B::type finite_image => 'A::type)
 (%f::'B::type finite_image => 'A::type. True::bool)"])
  by (import hollight TYDEF_cart)

syntax
  dest_cart :: _ 

syntax
  mk_cart :: _ 

lemmas "TYDEF_cart_@intern" = typedef_hol2hollight 
  [where a="a :: ('A, 'B) cart" and r=r ,
   OF type_definition_cart]

consts
  "$" :: "('q_46418, 'q_46425) cart => nat => 'q_46418" ("$")

defs
  "$_def": "$ ==
%(u::('q_46418::type, 'q_46425::type) cart) ua::nat.
   dest_cart u (finite_index ua)"

lemma "DEF_$": "$ =
(%(u::('q_46418::type, 'q_46425::type) cart) ua::nat.
    dest_cart u (finite_index ua))"
  by (import hollight "DEF_$")

lemma CART_EQ: "(All::(('A::type, 'B::type) cart => bool) => bool)
 (%x::('A::type, 'B::type) cart.
     (All::(('A::type, 'B::type) cart => bool) => bool)
      (%y::('A::type, 'B::type) cart.
          (op =::bool => bool => bool)
           ((op =::('A::type, 'B::type) cart
                   => ('A::type, 'B::type) cart => bool)
             x y)
           ((All::(nat => bool) => bool)
             (%xa::nat.
                 (op -->::bool => bool => bool)
                  ((op &::bool => bool => bool)
                    ((<=::nat => nat => bool)
                      ((NUMERAL_BIT1::nat => nat) (0::nat)) xa)
                    ((<=::nat => nat => bool) xa
                      ((dimindex::('B::type => bool) => nat)
                        (hollight.UNIV::'B::type => bool))))
                  ((op =::'A::type => 'A::type => bool)
                    (($::('A::type, 'B::type) cart => nat => 'A::type) x xa)
                    (($::('A::type, 'B::type) cart => nat => 'A::type) y
                      xa))))))"
  by (import hollight CART_EQ)

constdefs
  lambda :: "(nat => 'A) => ('A, 'B) cart" 
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
                  ((<=::nat => nat => bool)
                    ((NUMERAL_BIT1::nat => nat) (0::nat)) i)
                  ((<=::nat => nat => bool) i
                    ((dimindex::('B::type => bool) => nat)
                      (hollight.UNIV::'B::type => bool))))
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
                  ((<=::nat => nat => bool)
                    ((NUMERAL_BIT1::nat => nat) (0::nat)) i)
                  ((<=::nat => nat => bool) i
                    ((dimindex::('B::type => bool) => nat)
                      (hollight.UNIV::'B::type => bool))))
                ((op =::'A::type => 'A::type => bool)
                  (($::('A::type, 'B::type) cart => nat => 'A::type) f i)
                  (u i)))))"
  by (import hollight DEF_lambda)

lemma LAMBDA_BETA: "(All::(nat => bool) => bool)
 (%x::nat.
     (op -->::bool => bool => bool)
      ((op &::bool => bool => bool)
        ((<=::nat => nat => bool) ((NUMERAL_BIT1::nat => nat) (0::nat)) x)
        ((<=::nat => nat => bool) x
          ((dimindex::('B::type => bool) => nat)
            (hollight.UNIV::'B::type => bool))))
      ((op =::'A::type => 'A::type => bool)
        (($::('A::type, 'B::type) cart => nat => 'A::type)
          ((lambda::(nat => 'A::type) => ('A::type, 'B::type) cart)
            (g::nat => 'A::type))
          x)
        (g x)))"
  by (import hollight LAMBDA_BETA)

lemma LAMBDA_UNIQUE: "(All::(('A::type, 'B::type) cart => bool) => bool)
 (%x::('A::type, 'B::type) cart.
     (All::((nat => 'A::type) => bool) => bool)
      (%xa::nat => 'A::type.
          (op =::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%i::nat.
                 (op -->::bool => bool => bool)
                  ((op &::bool => bool => bool)
                    ((<=::nat => nat => bool)
                      ((NUMERAL_BIT1::nat => nat) (0::nat)) i)
                    ((<=::nat => nat => bool) i
                      ((dimindex::('B::type => bool) => nat)
                        (hollight.UNIV::'B::type => bool))))
                  ((op =::'A::type => 'A::type => bool)
                    (($::('A::type, 'B::type) cart => nat => 'A::type) x i)
                    (xa i))))
           ((op =::('A::type, 'B::type) cart
                   => ('A::type, 'B::type) cart => bool)
             ((lambda::(nat => 'A::type) => ('A::type, 'B::type) cart) xa)
             x)))"
  by (import hollight LAMBDA_UNIQUE)

lemma LAMBDA_ETA: "ALL x::('q_46616::type, 'q_46620::type) cart. lambda ($ x) = x"
  by (import hollight LAMBDA_ETA)

typedef (open) ('A, 'B) finite_sum = "(Collect::(('A::type finite_image, 'B::type finite_image) sum => bool)
          => ('A::type finite_image, 'B::type finite_image) sum set)
 (%x::('A::type finite_image, 'B::type finite_image) sum. True::bool)"  morphisms "dest_finite_sum" "mk_finite_sum"
  apply (rule light_ex_imp_nonempty[where t="(Eps::(('A::type finite_image, 'B::type finite_image) sum => bool)
      => ('A::type finite_image, 'B::type finite_image) sum)
 (%x::('A::type finite_image, 'B::type finite_image) sum. True::bool)"])
  by (import hollight TYDEF_finite_sum)

syntax
  dest_finite_sum :: _ 

syntax
  mk_finite_sum :: _ 

lemmas "TYDEF_finite_sum_@intern" = typedef_hol2hollight 
  [where a="a :: ('A, 'B) finite_sum" and r=r ,
   OF type_definition_finite_sum]

constdefs
  pastecart :: "('A, 'M) cart => ('A, 'N) cart => ('A, ('M, 'N) finite_sum) cart" 
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
          (COND::bool => 'A::type => 'A::type => 'A::type)
           ((<=::nat => nat => bool) i
             ((dimindex::('M::type => bool) => nat)
               (hollight.UNIV::'M::type => bool)))
           (($::('A::type, 'M::type) cart => nat => 'A::type) u i)
           (($::('A::type, 'N::type) cart => nat => 'A::type) ua
             ((op -::nat => nat => nat) i
               ((dimindex::('M::type => bool) => nat)
                 (hollight.UNIV::'M::type => bool))))))"

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
          (COND::bool => 'A::type => 'A::type => 'A::type)
           ((<=::nat => nat => bool) i
             ((dimindex::('M::type => bool) => nat)
               (hollight.UNIV::'M::type => bool)))
           (($::('A::type, 'M::type) cart => nat => 'A::type) u i)
           (($::('A::type, 'N::type) cart => nat => 'A::type) ua
             ((op -::nat => nat => nat) i
               ((dimindex::('M::type => bool) => nat)
                 (hollight.UNIV::'M::type => bool))))))"
  by (import hollight DEF_pastecart)

constdefs
  fstcart :: "('A, ('M, 'N) finite_sum) cart => ('A, 'M) cart" 
  "fstcart ==
%u::('A::type, ('M::type, 'N::type) finite_sum) cart. lambda ($ u)"

lemma DEF_fstcart: "fstcart =
(%u::('A::type, ('M::type, 'N::type) finite_sum) cart. lambda ($ u))"
  by (import hollight DEF_fstcart)

constdefs
  sndcart :: "('A, ('M, 'N) finite_sum) cart => ('A, 'N) cart" 
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
                 (hollight.UNIV::'M::type => bool)))))"

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
                 (hollight.UNIV::'M::type => bool)))))"
  by (import hollight DEF_sndcart)

lemma DIMINDEX_HAS_SIZE_FINITE_SUM: "(HAS_SIZE::(('M::type, 'N::type) finite_sum => bool) => nat => bool)
 (hollight.UNIV::('M::type, 'N::type) finite_sum => bool)
 ((op +::nat => nat => nat)
   ((dimindex::('M::type => bool) => nat) (hollight.UNIV::'M::type => bool))
   ((dimindex::('N::type => bool) => nat)
     (hollight.UNIV::'N::type => bool)))"
  by (import hollight DIMINDEX_HAS_SIZE_FINITE_SUM)

lemma DIMINDEX_FINITE_SUM: "(op =::nat => nat => bool)
 ((dimindex::(('M::type, 'N::type) finite_sum => bool) => nat)
   (hollight.UNIV::('M::type, 'N::type) finite_sum => bool))
 ((op +::nat => nat => nat)
   ((dimindex::('M::type => bool) => nat) (hollight.UNIV::'M::type => bool))
   ((dimindex::('N::type => bool) => nat)
     (hollight.UNIV::'N::type => bool)))"
  by (import hollight DIMINDEX_FINITE_SUM)

lemma FSTCART_PASTECART: "ALL (x::('A::type, 'M::type) cart) xa::('A::type, 'N::type) cart.
   fstcart (pastecart x xa) = x"
  by (import hollight FSTCART_PASTECART)

lemma SNDCART_PASTECART: "ALL (x::('A::type, 'M::type) cart) xa::('A::type, 'N::type) cart.
   sndcart (pastecart x xa) = xa"
  by (import hollight SNDCART_PASTECART)

lemma PASTECART_FST_SND: "ALL x::('q_46940::type, ('q_46937::type, 'q_46935::type) finite_sum) cart.
   pastecart (fstcart x) (sndcart x) = x"
  by (import hollight PASTECART_FST_SND)

lemma PASTECART_EQ: "ALL (x::('q_46978::type, ('q_46968::type, 'q_46979::type) finite_sum) cart)
   y::('q_46978::type, ('q_46968::type, 'q_46979::type) finite_sum) cart.
   (x = y) = (fstcart x = fstcart y & sndcart x = sndcart y)"
  by (import hollight PASTECART_EQ)

lemma FORALL_PASTECART: "All (P::('q_46999::type, ('q_47000::type, 'q_47001::type) finite_sum) cart
        => bool) =
(ALL (x::('q_46999::type, 'q_47000::type) cart)
    y::('q_46999::type, 'q_47001::type) cart. P (pastecart x y))"
  by (import hollight FORALL_PASTECART)

lemma EXISTS_PASTECART: "Ex (P::('q_47021::type, ('q_47022::type, 'q_47023::type) finite_sum) cart
       => bool) =
(EX (x::('q_47021::type, 'q_47022::type) cart)
    y::('q_47021::type, 'q_47023::type) cart. P (pastecart x y))"
  by (import hollight EXISTS_PASTECART)

lemma SURJECTIVE_IFF_INJECTIVE_GEN: "ALL (s::'A::type => bool) (t::'B::type => bool) f::'A::type => 'B::type.
   FINITE s & FINITE t & CARD s = CARD t & SUBSET (IMAGE f s) t -->
   (ALL y::'B::type. IN y t --> (EX x::'A::type. IN x s & f x = y)) =
   (ALL (x::'A::type) y::'A::type. IN x s & IN y s & f x = f y --> x = y)"
  by (import hollight SURJECTIVE_IFF_INJECTIVE_GEN)

lemma SURJECTIVE_IFF_INJECTIVE: "ALL (x::'A::type => bool) xa::'A::type => 'A::type.
   FINITE x & SUBSET (IMAGE xa x) x -->
   (ALL y::'A::type. IN y x --> (EX xb::'A::type. IN xb x & xa xb = y)) =
   (ALL (xb::'A::type) y::'A::type.
       IN xb x & IN y x & xa xb = xa y --> xb = y)"
  by (import hollight SURJECTIVE_IFF_INJECTIVE)

lemma IMAGE_IMP_INJECTIVE_GEN: "ALL (s::'A::type => bool) (t::'B::type => bool) f::'A::type => 'B::type.
   FINITE s & CARD s = CARD t & IMAGE f s = t -->
   (ALL (x::'A::type) y::'A::type. IN x s & IN y s & f x = f y --> x = y)"
  by (import hollight IMAGE_IMP_INJECTIVE_GEN)

lemma IMAGE_IMP_INJECTIVE: "ALL (s::'q_47348::type => bool) f::'q_47348::type => 'q_47348::type.
   FINITE s & IMAGE f s = s -->
   (ALL (x::'q_47348::type) y::'q_47348::type.
       IN x s & IN y s & f x = f y --> x = y)"
  by (import hollight IMAGE_IMP_INJECTIVE)

lemma CARD_LE_INJ: "ALL (x::'A::type => bool) xa::'B::type => bool.
   FINITE x & FINITE xa & <= (CARD x) (CARD xa) -->
   (EX f::'A::type => 'B::type.
       SUBSET (IMAGE f x) xa &
       (ALL (xa::'A::type) y::'A::type.
           IN xa x & IN y x & f xa = f y --> xa = y))"
  by (import hollight CARD_LE_INJ)

lemma FORALL_IN_CLAUSES: "(ALL x::'q_47454::type => bool.
    (ALL xa::'q_47454::type. IN xa EMPTY --> x xa) = True) &
(ALL (x::'q_47494::type => bool) (xa::'q_47494::type)
    xb::'q_47494::type => bool.
    (ALL xc::'q_47494::type. IN xc (INSERT xa xb) --> x xc) =
    (x xa & (ALL xa::'q_47494::type. IN xa xb --> x xa)))"
  by (import hollight FORALL_IN_CLAUSES)

lemma EXISTS_IN_CLAUSES: "(ALL x::'q_47514::type => bool.
    (EX xa::'q_47514::type. IN xa EMPTY & x xa) = False) &
(ALL (x::'q_47554::type => bool) (xa::'q_47554::type)
    xb::'q_47554::type => bool.
    (EX xc::'q_47554::type. IN xc (INSERT xa xb) & x xc) =
    (x xa | (EX xa::'q_47554::type. IN xa xb & x xa)))"
  by (import hollight EXISTS_IN_CLAUSES)

lemma SURJECTIVE_ON_RIGHT_INVERSE: "ALL (x::'q_47610::type => 'q_47611::type) xa::'q_47611::type => bool.
   (ALL xb::'q_47611::type.
       IN xb xa -->
       (EX xa::'q_47610::type.
           IN xa (s::'q_47610::type => bool) & x xa = xb)) =
   (EX g::'q_47611::type => 'q_47610::type.
       ALL y::'q_47611::type. IN y xa --> IN (g y) s & x (g y) = y)"
  by (import hollight SURJECTIVE_ON_RIGHT_INVERSE)

lemma INJECTIVE_ON_LEFT_INVERSE: "ALL (x::'q_47704::type => 'q_47707::type) xa::'q_47704::type => bool.
   (ALL (xb::'q_47704::type) y::'q_47704::type.
       IN xb xa & IN y xa & x xb = x y --> xb = y) =
   (EX xb::'q_47707::type => 'q_47704::type.
       ALL xc::'q_47704::type. IN xc xa --> xb (x xc) = xc)"
  by (import hollight INJECTIVE_ON_LEFT_INVERSE)

lemma SURJECTIVE_RIGHT_INVERSE: "(ALL y::'q_47732::type.
    EX x::'q_47735::type. (f::'q_47735::type => 'q_47732::type) x = y) =
(EX g::'q_47732::type => 'q_47735::type. ALL y::'q_47732::type. f (g y) = y)"
  by (import hollight SURJECTIVE_RIGHT_INVERSE)

lemma INJECTIVE_LEFT_INVERSE: "(ALL (x::'q_47769::type) xa::'q_47769::type.
    (f::'q_47769::type => 'q_47772::type) x = f xa --> x = xa) =
(EX g::'q_47772::type => 'q_47769::type. ALL x::'q_47769::type. g (f x) = x)"
  by (import hollight INJECTIVE_LEFT_INVERSE)

lemma FUNCTION_FACTORS_RIGHT: "ALL (x::'q_47808::type => 'q_47809::type)
   xa::'q_47796::type => 'q_47809::type.
   (ALL xb::'q_47808::type. EX y::'q_47796::type. xa y = x xb) =
   (EX xb::'q_47808::type => 'q_47796::type. x = xa o xb)"
  by (import hollight FUNCTION_FACTORS_RIGHT)

lemma FUNCTION_FACTORS_LEFT: "ALL (x::'q_47881::type => 'q_47882::type)
   xa::'q_47881::type => 'q_47861::type.
   (ALL (xb::'q_47881::type) y::'q_47881::type.
       xa xb = xa y --> x xb = x y) =
   (EX xb::'q_47861::type => 'q_47882::type. x = xb o xa)"
  by (import hollight FUNCTION_FACTORS_LEFT)

constdefs
  dotdot :: "nat => nat => nat => bool" 
  "dotdot ==
%(u::nat) ua::nat.
   GSPEC (%ub::nat. EX x::nat. SETSPEC ub (<= u x & <= x ua) x)"

lemma DEF__dot__dot_: "dotdot =
(%(u::nat) ua::nat.
    GSPEC (%ub::nat. EX x::nat. SETSPEC ub (<= u x & <= x ua) x))"
  by (import hollight DEF__dot__dot_)

lemma FINITE_NUMSEG: "ALL (m::nat) n::nat. FINITE (dotdot m n)"
  by (import hollight FINITE_NUMSEG)

lemma NUMSEG_COMBINE_R: "ALL (x::'q_47957::type) (p::nat) m::nat.
   <= m p & <= p (n::nat) -->
   hollight.UNION (dotdot m p) (dotdot (p + NUMERAL_BIT1 0) n) = dotdot m n"
  by (import hollight NUMSEG_COMBINE_R)

lemma NUMSEG_COMBINE_L: "ALL (x::'q_47995::type) (p::nat) m::nat.
   <= m p & <= p (n::nat) -->
   hollight.UNION (dotdot m (p - NUMERAL_BIT1 0)) (dotdot p n) = dotdot m n"
  by (import hollight NUMSEG_COMBINE_L)

lemma NUMSEG_LREC: "ALL (x::nat) xa::nat.
   <= x xa --> INSERT x (dotdot (x + NUMERAL_BIT1 0) xa) = dotdot x xa"
  by (import hollight NUMSEG_LREC)

lemma NUMSEG_RREC: "ALL (x::nat) xa::nat.
   <= x xa --> INSERT xa (dotdot x (xa - NUMERAL_BIT1 0)) = dotdot x xa"
  by (import hollight NUMSEG_RREC)

lemma NUMSEG_REC: "ALL (x::nat) xa::nat.
   <= x (Suc xa) --> dotdot x (Suc xa) = INSERT (Suc xa) (dotdot x xa)"
  by (import hollight NUMSEG_REC)

lemma IN_NUMSEG: "ALL (x::nat) (xa::nat) xb::nat. IN xb (dotdot x xa) = (<= x xb & <= xb xa)"
  by (import hollight IN_NUMSEG)

lemma NUMSEG_SING: "ALL x::nat. dotdot x x = INSERT x EMPTY"
  by (import hollight NUMSEG_SING)

lemma NUMSEG_EMPTY: "ALL (x::nat) xa::nat. (dotdot x xa = EMPTY) = < xa x"
  by (import hollight NUMSEG_EMPTY)

lemma CARD_NUMSEG_LEMMA: "ALL (m::nat) d::nat. CARD (dotdot m (m + d)) = d + NUMERAL_BIT1 0"
  by (import hollight CARD_NUMSEG_LEMMA)

lemma CARD_NUMSEG: "ALL (m::nat) n::nat. CARD (dotdot m n) = n + NUMERAL_BIT1 0 - m"
  by (import hollight CARD_NUMSEG)

lemma HAS_SIZE_NUMSEG: "ALL (x::nat) xa::nat. HAS_SIZE (dotdot x xa) (xa + NUMERAL_BIT1 0 - x)"
  by (import hollight HAS_SIZE_NUMSEG)

lemma CARD_NUMSEG_1: "ALL x::nat. CARD (dotdot (NUMERAL_BIT1 0) x) = x"
  by (import hollight CARD_NUMSEG_1)

lemma HAS_SIZE_NUMSEG_1: "ALL x::nat. HAS_SIZE (dotdot (NUMERAL_BIT1 0) x) x"
  by (import hollight HAS_SIZE_NUMSEG_1)

lemma NUMSEG_CLAUSES: "(ALL m::nat. dotdot m 0 = COND (m = 0) (INSERT 0 EMPTY) EMPTY) &
(ALL (m::nat) n::nat.
    dotdot m (Suc n) =
    COND (<= m (Suc n)) (INSERT (Suc n) (dotdot m n)) (dotdot m n))"
  by (import hollight NUMSEG_CLAUSES)

lemma FINITE_INDEX_NUMSEG: "ALL s::'A::type => bool.
   FINITE s =
   (EX f::nat => 'A::type.
       (ALL (i::nat) j::nat.
           IN i (dotdot (NUMERAL_BIT1 0) (CARD s)) &
           IN j (dotdot (NUMERAL_BIT1 0) (CARD s)) & f i = f j -->
           i = j) &
       s = IMAGE f (dotdot (NUMERAL_BIT1 0) (CARD s)))"
  by (import hollight FINITE_INDEX_NUMSEG)

lemma FINITE_INDEX_NUMBERS: "ALL s::'A::type => bool.
   FINITE s =
   (EX (k::nat => bool) f::nat => 'A::type.
       (ALL (i::nat) j::nat. IN i k & IN j k & f i = f j --> i = j) &
       FINITE k & s = IMAGE f k)"
  by (import hollight FINITE_INDEX_NUMBERS)

lemma DISJOINT_NUMSEG: "ALL (x::nat) (xa::nat) (xb::nat) xc::nat.
   DISJOINT (dotdot x xa) (dotdot xb xc) =
   (< xa xb | < xc x | < xa x | < xc xb)"
  by (import hollight DISJOINT_NUMSEG)

lemma NUMSEG_ADD_SPLIT: "ALL (x::nat) (xa::nat) xb::nat.
   <= x (xa + NUMERAL_BIT1 0) -->
   dotdot x (xa + xb) =
   hollight.UNION (dotdot x xa) (dotdot (xa + NUMERAL_BIT1 0) (xa + xb))"
  by (import hollight NUMSEG_ADD_SPLIT)

lemma NUMSEG_OFFSET_IMAGE: "ALL (x::nat) (xa::nat) xb::nat.
   dotdot (x + xb) (xa + xb) = IMAGE (%i::nat. i + xb) (dotdot x xa)"
  by (import hollight NUMSEG_OFFSET_IMAGE)

lemma SUBSET_NUMSEG: "ALL (m::nat) (n::nat) (p::nat) q::nat.
   SUBSET (dotdot m n) (dotdot p q) = (< n m | <= p m & <= n q)"
  by (import hollight SUBSET_NUMSEG)

constdefs
  neutral :: "('q_48776 => 'q_48776 => 'q_48776) => 'q_48776" 
  "neutral ==
%u::'q_48776::type => 'q_48776::type => 'q_48776::type.
   SOME x::'q_48776::type. ALL y::'q_48776::type. u x y = y & u y x = y"

lemma DEF_neutral: "neutral =
(%u::'q_48776::type => 'q_48776::type => 'q_48776::type.
    SOME x::'q_48776::type. ALL y::'q_48776::type. u x y = y & u y x = y)"
  by (import hollight DEF_neutral)

constdefs
  monoidal :: "('A => 'A => 'A) => bool" 
  "monoidal ==
%u::'A::type => 'A::type => 'A::type.
   (ALL (x::'A::type) y::'A::type. u x y = u y x) &
   (ALL (x::'A::type) (y::'A::type) z::'A::type.
       u x (u y z) = u (u x y) z) &
   (ALL x::'A::type. u (neutral u) x = x)"

lemma DEF_monoidal: "monoidal =
(%u::'A::type => 'A::type => 'A::type.
    (ALL (x::'A::type) y::'A::type. u x y = u y x) &
    (ALL (x::'A::type) (y::'A::type) z::'A::type.
        u x (u y z) = u (u x y) z) &
    (ALL x::'A::type. u (neutral u) x = x))"
  by (import hollight DEF_monoidal)

constdefs
  support :: "('B => 'B => 'B) => ('A => 'B) => ('A => bool) => 'A => bool" 
  "support ==
%(u::'B::type => 'B::type => 'B::type) (ua::'A::type => 'B::type)
   ub::'A::type => bool.
   GSPEC
    (%uc::'A::type.
        EX x::'A::type. SETSPEC uc (IN x ub & ua x ~= neutral u) x)"

lemma DEF_support: "support =
(%(u::'B::type => 'B::type => 'B::type) (ua::'A::type => 'B::type)
    ub::'A::type => bool.
    GSPEC
     (%uc::'A::type.
         EX x::'A::type. SETSPEC uc (IN x ub & ua x ~= neutral u) x))"
  by (import hollight DEF_support)

constdefs
  iterate :: "('q_48881 => 'q_48881 => 'q_48881)
=> ('A => bool) => ('A => 'q_48881) => 'q_48881" 
  "iterate ==
%(u::'q_48881::type => 'q_48881::type => 'q_48881::type)
   (ua::'A::type => bool) ub::'A::type => 'q_48881::type.
   ITSET (%x::'A::type. u (ub x)) (support u ub ua) (neutral u)"

lemma DEF_iterate: "iterate =
(%(u::'q_48881::type => 'q_48881::type => 'q_48881::type)
    (ua::'A::type => bool) ub::'A::type => 'q_48881::type.
    ITSET (%x::'A::type. u (ub x)) (support u ub ua) (neutral u))"
  by (import hollight DEF_iterate)

lemma IN_SUPPORT: "ALL (x::'q_48924::type => 'q_48924::type => 'q_48924::type)
   (xa::'q_48927::type => 'q_48924::type) (xb::'q_48927::type)
   xc::'q_48927::type => bool.
   IN xb (support x xa xc) = (IN xb xc & xa xb ~= neutral x)"
  by (import hollight IN_SUPPORT)

lemma SUPPORT_SUPPORT: "ALL (x::'q_48949::type => 'q_48949::type => 'q_48949::type)
   (xa::'q_48960::type => 'q_48949::type) xb::'q_48960::type => bool.
   support x xa (support x xa xb) = support x xa xb"
  by (import hollight SUPPORT_SUPPORT)

lemma SUPPORT_EMPTY: "ALL (x::'q_48985::type => 'q_48985::type => 'q_48985::type)
   (xa::'q_48999::type => 'q_48985::type) xb::'q_48999::type => bool.
   (ALL xc::'q_48999::type. IN xc xb --> xa xc = neutral x) =
   (support x xa xb = EMPTY)"
  by (import hollight SUPPORT_EMPTY)

lemma SUPPORT_SUBSET: "ALL (x::'q_49019::type => 'q_49019::type => 'q_49019::type)
   (xa::'q_49020::type => 'q_49019::type) xb::'q_49020::type => bool.
   SUBSET (support x xa xb) xb"
  by (import hollight SUPPORT_SUBSET)

lemma FINITE_SUPPORT: "ALL (u::'q_49043::type => 'q_49043::type => 'q_49043::type)
   (f::'q_49037::type => 'q_49043::type) s::'q_49037::type => bool.
   FINITE s --> FINITE (support u f s)"
  by (import hollight FINITE_SUPPORT)

lemma SUPPORT_CLAUSES: "(ALL x::'q_49061::type => 'q_49091::type.
    support (u_4215::'q_49091::type => 'q_49091::type => 'q_49091::type) x
     EMPTY =
    EMPTY) &
(ALL (x::'q_49109::type => 'q_49091::type) (xa::'q_49109::type)
    xb::'q_49109::type => bool.
    support u_4215 x (INSERT xa xb) =
    COND (x xa = neutral u_4215) (support u_4215 x xb)
     (INSERT xa (support u_4215 x xb))) &
(ALL (x::'q_49142::type => 'q_49091::type) (xa::'q_49142::type)
    xb::'q_49142::type => bool.
    support u_4215 x (DELETE xb xa) = DELETE (support u_4215 x xb) xa) &
(ALL (x::'q_49180::type => 'q_49091::type) (xa::'q_49180::type => bool)
    xb::'q_49180::type => bool.
    support u_4215 x (hollight.UNION xa xb) =
    hollight.UNION (support u_4215 x xa) (support u_4215 x xb)) &
(ALL (x::'q_49218::type => 'q_49091::type) (xa::'q_49218::type => bool)
    xb::'q_49218::type => bool.
    support u_4215 x (hollight.INTER xa xb) =
    hollight.INTER (support u_4215 x xa) (support u_4215 x xb)) &
(ALL (x::'q_49254::type => 'q_49091::type) (xa::'q_49254::type => bool)
    xb::'q_49254::type => bool.
    support u_4215 x (DIFF xa xb) =
    DIFF (support u_4215 x xa) (support u_4215 x xb))"
  by (import hollight SUPPORT_CLAUSES)

lemma ITERATE_SUPPORT: "ALL (x::'q_49275::type => 'q_49275::type => 'q_49275::type)
   (xa::'q_49276::type => 'q_49275::type) xb::'q_49276::type => bool.
   FINITE (support x xa xb) -->
   iterate x (support x xa xb) xa = iterate x xb xa"
  by (import hollight ITERATE_SUPPORT)

lemma SUPPORT_DELTA: "ALL (x::'q_49320::type => 'q_49320::type => 'q_49320::type)
   (xa::'q_49348::type => bool) (xb::'q_49348::type => 'q_49320::type)
   xc::'q_49348::type.
   support x (%xa::'q_49348::type. COND (xa = xc) (xb xa) (neutral x)) xa =
   COND (IN xc xa) (support x xb (INSERT xc EMPTY)) EMPTY"
  by (import hollight SUPPORT_DELTA)

lemma FINITE_SUPPORT_DELTA: "ALL (x::'q_49369::type => 'q_49369::type => 'q_49369::type)
   (xa::'q_49378::type => 'q_49369::type) xb::'q_49378::type.
   FINITE
    (support x (%xc::'q_49378::type. COND (xc = xb) (xa xc) (neutral x))
      (s::'q_49378::type => bool))"
  by (import hollight FINITE_SUPPORT_DELTA)

lemma ITERATE_CLAUSES_GEN: "ALL u_4215::'B::type => 'B::type => 'B::type.
   monoidal u_4215 -->
   (ALL f::'A::type => 'B::type. iterate u_4215 EMPTY f = neutral u_4215) &
   (ALL (f::'A::type => 'B::type) (x::'A::type) s::'A::type => bool.
       monoidal u_4215 & FINITE (support u_4215 f s) -->
       iterate u_4215 (INSERT x s) f =
       COND (IN x s) (iterate u_4215 s f)
        (u_4215 (f x) (iterate u_4215 s f)))"
  by (import hollight ITERATE_CLAUSES_GEN)

lemma ITERATE_CLAUSES: "ALL x::'q_49546::type => 'q_49546::type => 'q_49546::type.
   monoidal x -->
   (ALL f::'q_49504::type => 'q_49546::type.
       iterate x EMPTY f = neutral x) &
   (ALL (f::'q_49548::type => 'q_49546::type) (xa::'q_49548::type)
       s::'q_49548::type => bool.
       FINITE s -->
       iterate x (INSERT xa s) f =
       COND (IN xa s) (iterate x s f) (x (f xa) (iterate x s f)))"
  by (import hollight ITERATE_CLAUSES)

lemma ITERATE_UNION: "ALL u_4215::'q_49634::type => 'q_49634::type => 'q_49634::type.
   monoidal u_4215 -->
   (ALL (f::'q_49619::type => 'q_49634::type) (s::'q_49619::type => bool)
       x::'q_49619::type => bool.
       FINITE s & FINITE x & DISJOINT s x -->
       iterate u_4215 (hollight.UNION s x) f =
       u_4215 (iterate u_4215 s f) (iterate u_4215 x f))"
  by (import hollight ITERATE_UNION)

lemma ITERATE_UNION_GEN: "ALL u_4215::'B::type => 'B::type => 'B::type.
   monoidal u_4215 -->
   (ALL (f::'A::type => 'B::type) (s::'A::type => bool) t::'A::type => bool.
       FINITE (support u_4215 f s) &
       FINITE (support u_4215 f t) &
       DISJOINT (support u_4215 f s) (support u_4215 f t) -->
       iterate u_4215 (hollight.UNION s t) f =
       u_4215 (iterate u_4215 s f) (iterate u_4215 t f))"
  by (import hollight ITERATE_UNION_GEN)

lemma ITERATE_DIFF: "ALL u::'q_49777::type => 'q_49777::type => 'q_49777::type.
   monoidal u -->
   (ALL (f::'q_49773::type => 'q_49777::type) (s::'q_49773::type => bool)
       t::'q_49773::type => bool.
       FINITE s & SUBSET t s -->
       u (iterate u (DIFF s t) f) (iterate u t f) = iterate u s f)"
  by (import hollight ITERATE_DIFF)

lemma ITERATE_DIFF_GEN: "ALL u_4215::'B::type => 'B::type => 'B::type.
   monoidal u_4215 -->
   (ALL (f::'A::type => 'B::type) (s::'A::type => bool) t::'A::type => bool.
       FINITE (support u_4215 f s) &
       SUBSET (support u_4215 f t) (support u_4215 f s) -->
       u_4215 (iterate u_4215 (DIFF s t) f) (iterate u_4215 t f) =
       iterate u_4215 s f)"
  by (import hollight ITERATE_DIFF_GEN)

lemma ITERATE_CLOSED: "ALL u_4215::'B::type => 'B::type => 'B::type.
   monoidal u_4215 -->
   (ALL P::'B::type => bool.
       P (neutral u_4215) &
       (ALL (x::'B::type) y::'B::type. P x & P y --> P (u_4215 x y)) -->
       (ALL (f::'A::type => 'B::type) x::'A::type => bool.
           FINITE x & (ALL xa::'A::type. IN xa x --> P (f xa)) -->
           P (iterate u_4215 x f)))"
  by (import hollight ITERATE_CLOSED)

lemma ITERATE_CLOSED_GEN: "ALL u_4215::'B::type => 'B::type => 'B::type.
   monoidal u_4215 -->
   (ALL P::'B::type => bool.
       P (neutral u_4215) &
       (ALL (x::'B::type) y::'B::type. P x & P y --> P (u_4215 x y)) -->
       (ALL (f::'A::type => 'B::type) s::'A::type => bool.
           FINITE (support u_4215 f s) &
           (ALL x::'A::type. IN x s & f x ~= neutral u_4215 --> P (f x)) -->
           P (iterate u_4215 s f)))"
  by (import hollight ITERATE_CLOSED_GEN)

lemma ITERATE_RELATED: "ALL u_4215::'B::type => 'B::type => 'B::type.
   monoidal u_4215 -->
   (ALL R::'B::type => 'B::type => bool.
       R (neutral u_4215) (neutral u_4215) &
       (ALL (x1::'B::type) (y1::'B::type) (x2::'B::type) y2::'B::type.
           R x1 x2 & R y1 y2 --> R (u_4215 x1 y1) (u_4215 x2 y2)) -->
       (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type)
           x::'A::type => bool.
           FINITE x & (ALL xa::'A::type. IN xa x --> R (f xa) (g xa)) -->
           R (iterate u_4215 x f) (iterate u_4215 x g)))"
  by (import hollight ITERATE_RELATED)

lemma ITERATE_EQ_NEUTRAL: "ALL u_4215::'B::type => 'B::type => 'B::type.
   monoidal u_4215 -->
   (ALL (f::'A::type => 'B::type) s::'A::type => bool.
       (ALL x::'A::type. IN x s --> f x = neutral u_4215) -->
       iterate u_4215 s f = neutral u_4215)"
  by (import hollight ITERATE_EQ_NEUTRAL)

lemma ITERATE_SING: "ALL x::'B::type => 'B::type => 'B::type.
   monoidal x -->
   (ALL (f::'A::type => 'B::type) xa::'A::type.
       iterate x (INSERT xa EMPTY) f = f xa)"
  by (import hollight ITERATE_SING)

lemma ITERATE_DELTA: "ALL u_4215::'q_50229::type => 'q_50229::type => 'q_50229::type.
   monoidal u_4215 -->
   (ALL (x::'q_50248::type => 'q_50229::type) (xa::'q_50248::type)
       xb::'q_50248::type => bool.
       iterate u_4215 xb
        (%xb::'q_50248::type. COND (xb = xa) (x xb) (neutral u_4215)) =
       COND (IN xa xb) (x xa) (neutral u_4215))"
  by (import hollight ITERATE_DELTA)

lemma ITERATE_IMAGE: "ALL u_4215::'q_50327::type => 'q_50327::type => 'q_50327::type.
   monoidal u_4215 -->
   (ALL (f::'q_50326::type => 'q_50298::type)
       (g::'q_50298::type => 'q_50327::type) x::'q_50326::type => bool.
       FINITE x &
       (ALL (xa::'q_50326::type) y::'q_50326::type.
           IN xa x & IN y x & f xa = f y --> xa = y) -->
       iterate u_4215 (IMAGE f x) g = iterate u_4215 x (g o f))"
  by (import hollight ITERATE_IMAGE)

constdefs
  nsum :: "('q_50348 => bool) => ('q_50348 => nat) => nat" 
  "(op ==::(('q_50348::type => bool) => ('q_50348::type => nat) => nat)
        => (('q_50348::type => bool) => ('q_50348::type => nat) => nat)
           => prop)
 (nsum::('q_50348::type => bool) => ('q_50348::type => nat) => nat)
 ((iterate::(nat => nat => nat)
            => ('q_50348::type => bool) => ('q_50348::type => nat) => nat)
   (op +::nat => nat => nat))"

lemma DEF_nsum: "(op =::(('q_50348::type => bool) => ('q_50348::type => nat) => nat)
       => (('q_50348::type => bool) => ('q_50348::type => nat) => nat)
          => bool)
 (nsum::('q_50348::type => bool) => ('q_50348::type => nat) => nat)
 ((iterate::(nat => nat => nat)
            => ('q_50348::type => bool) => ('q_50348::type => nat) => nat)
   (op +::nat => nat => nat))"
  by (import hollight DEF_nsum)

lemma NEUTRAL_ADD: "(op =::nat => nat => bool)
 ((neutral::(nat => nat => nat) => nat) (op +::nat => nat => nat)) (0::nat)"
  by (import hollight NEUTRAL_ADD)

lemma NEUTRAL_MUL: "neutral op * = NUMERAL_BIT1 0"
  by (import hollight NEUTRAL_MUL)

lemma MONOIDAL_ADD: "(monoidal::(nat => nat => nat) => bool) (op +::nat => nat => nat)"
  by (import hollight MONOIDAL_ADD)

lemma MONOIDAL_MUL: "(monoidal::(nat => nat => nat) => bool) (op *::nat => nat => nat)"
  by (import hollight MONOIDAL_MUL)

lemma NSUM_CLAUSES: "(ALL x::'q_50386::type => nat. nsum EMPTY x = 0) &
(ALL (x::'q_50425::type) (xa::'q_50425::type => nat)
    xb::'q_50425::type => bool.
    FINITE xb -->
    nsum (INSERT x xb) xa = COND (IN x xb) (nsum xb xa) (xa x + nsum xb xa))"
  by (import hollight NSUM_CLAUSES)

lemma NSUM_UNION: "ALL (x::'q_50451::type => nat) (xa::'q_50451::type => bool)
   xb::'q_50451::type => bool.
   FINITE xa & FINITE xb & DISJOINT xa xb -->
   nsum (hollight.UNION xa xb) x = nsum xa x + nsum xb x"
  by (import hollight NSUM_UNION)

lemma NSUM_DIFF: "ALL (f::'q_50506::type => nat) (s::'q_50506::type => bool)
   t::'q_50506::type => bool.
   FINITE s & SUBSET t s --> nsum (DIFF s t) f = nsum s f - nsum t f"
  by (import hollight NSUM_DIFF)

lemma NSUM_SUPPORT: "ALL (x::'q_50545::type => nat) xa::'q_50545::type => bool.
   FINITE (support op + x xa) --> nsum (support op + x xa) x = nsum xa x"
  by (import hollight NSUM_SUPPORT)

lemma NSUM_ADD: "ALL (f::'q_50591::type => nat) (g::'q_50591::type => nat)
   s::'q_50591::type => bool.
   FINITE s --> nsum s (%x::'q_50591::type. f x + g x) = nsum s f + nsum s g"
  by (import hollight NSUM_ADD)

lemma NSUM_CMUL: "ALL (f::'q_50629::type => nat) (c::nat) s::'q_50629::type => bool.
   FINITE s --> nsum s (%x::'q_50629::type. c * f x) = c * nsum s f"
  by (import hollight NSUM_CMUL)

lemma NSUM_LE: "ALL (x::'q_50668::type => nat) (xa::'q_50668::type => nat)
   xb::'q_50668::type => bool.
   FINITE xb & (ALL xc::'q_50668::type. IN xc xb --> <= (x xc) (xa xc)) -->
   <= (nsum xb x) (nsum xb xa)"
  by (import hollight NSUM_LE)

lemma NSUM_LT: "ALL (f::'A::type => nat) (g::'A::type => nat) s::'A::type => bool.
   FINITE s &
   (ALL x::'A::type. IN x s --> <= (f x) (g x)) &
   (EX x::'A::type. IN x s & < (f x) (g x)) -->
   < (nsum s f) (nsum s g)"
  by (import hollight NSUM_LT)

lemma NSUM_LT_ALL: "ALL (f::'q_50790::type => nat) (g::'q_50790::type => nat)
   s::'q_50790::type => bool.
   FINITE s &
   s ~= EMPTY & (ALL x::'q_50790::type. IN x s --> < (f x) (g x)) -->
   < (nsum s f) (nsum s g)"
  by (import hollight NSUM_LT_ALL)

lemma NSUM_EQ: "ALL (x::'q_50832::type => nat) (xa::'q_50832::type => nat)
   xb::'q_50832::type => bool.
   FINITE xb & (ALL xc::'q_50832::type. IN xc xb --> x xc = xa xc) -->
   nsum xb x = nsum xb xa"
  by (import hollight NSUM_EQ)

lemma NSUM_CONST: "ALL (c::nat) s::'q_50862::type => bool.
   FINITE s --> nsum s (%n::'q_50862::type. c) = CARD s * c"
  by (import hollight NSUM_CONST)

lemma NSUM_EQ_0: "ALL (x::'A::type => nat) xa::'A::type => bool.
   (ALL xb::'A::type. IN xb xa --> x xb = 0) --> nsum xa x = 0"
  by (import hollight NSUM_EQ_0)

lemma NSUM_0: "ALL x::'A::type => bool. nsum x (%n::'A::type. 0) = 0"
  by (import hollight NSUM_0)

lemma NSUM_POS_LE: "ALL (x::'q_50941::type => nat) xa::'q_50941::type => bool.
   FINITE xa & (ALL xb::'q_50941::type. IN xb xa --> <= 0 (x xb)) -->
   <= 0 (nsum xa x)"
  by (import hollight NSUM_POS_LE)

lemma NSUM_POS_BOUND: "ALL (f::'A::type => nat) (b::nat) x::'A::type => bool.
   FINITE x &
   (ALL xa::'A::type. IN xa x --> <= 0 (f xa)) & <= (nsum x f) b -->
   (ALL xa::'A::type. IN xa x --> <= (f xa) b)"
  by (import hollight NSUM_POS_BOUND)

lemma NSUM_POS_EQ_0: "ALL (x::'q_51076::type => nat) xa::'q_51076::type => bool.
   FINITE xa &
   (ALL xb::'q_51076::type. IN xb xa --> <= 0 (x xb)) & nsum xa x = 0 -->
   (ALL xb::'q_51076::type. IN xb xa --> x xb = 0)"
  by (import hollight NSUM_POS_EQ_0)

lemma NSUM_SING: "ALL (x::'q_51096::type => nat) xa::'q_51096::type.
   nsum (INSERT xa EMPTY) x = x xa"
  by (import hollight NSUM_SING)

lemma NSUM_DELTA: "ALL (x::'A::type => bool) xa::'A::type.
   nsum x (%x::'A::type. COND (x = xa) (b::nat) 0) = COND (IN xa x) b 0"
  by (import hollight NSUM_DELTA)

lemma NSUM_SWAP: "ALL (f::'A::type => 'B::type => nat) (x::'A::type => bool)
   xa::'B::type => bool.
   FINITE x & FINITE xa -->
   nsum x (%i::'A::type. nsum xa (f i)) =
   nsum xa (%j::'B::type. nsum x (%i::'A::type. f i j))"
  by (import hollight NSUM_SWAP)

lemma NSUM_IMAGE: "ALL (x::'q_51236::type => 'q_51212::type) (xa::'q_51212::type => nat)
   xb::'q_51236::type => bool.
   FINITE xb &
   (ALL (xa::'q_51236::type) y::'q_51236::type.
       IN xa xb & IN y xb & x xa = x y --> xa = y) -->
   nsum (IMAGE x xb) xa = nsum xb (xa o x)"
  by (import hollight NSUM_IMAGE)

lemma NSUM_SUPERSET: "ALL (f::'A::type => nat) (u::'A::type => bool) v::'A::type => bool.
   FINITE u &
   SUBSET u v & (ALL x::'A::type. IN x v & ~ IN x u --> f x = 0) -->
   nsum v f = nsum u f"
  by (import hollight NSUM_SUPERSET)

lemma NSUM_UNION_RZERO: "ALL (f::'A::type => nat) (u::'A::type => bool) v::'A::type => bool.
   FINITE u & (ALL x::'A::type. IN x v & ~ IN x u --> f x = 0) -->
   nsum (hollight.UNION u v) f = nsum u f"
  by (import hollight NSUM_UNION_RZERO)

lemma NSUM_UNION_LZERO: "ALL (f::'A::type => nat) (u::'A::type => bool) v::'A::type => bool.
   FINITE v & (ALL x::'A::type. IN x u & ~ IN x v --> f x = 0) -->
   nsum (hollight.UNION u v) f = nsum v f"
  by (import hollight NSUM_UNION_LZERO)

lemma NSUM_RESTRICT: "ALL (f::'q_51457::type => nat) s::'q_51457::type => bool.
   FINITE s -->
   nsum s (%x::'q_51457::type. COND (IN x s) (f x) 0) = nsum s f"
  by (import hollight NSUM_RESTRICT)

lemma NSUM_BOUND: "ALL (x::'A::type => bool) (xa::'A::type => nat) xb::nat.
   FINITE x & (ALL xc::'A::type. IN xc x --> <= (xa xc) xb) -->
   <= (nsum x xa) (CARD x * xb)"
  by (import hollight NSUM_BOUND)

lemma NSUM_BOUND_GEN: "ALL (x::'A::type => bool) (xa::'q_51532::type) b::nat.
   FINITE x &
   x ~= EMPTY &
   (ALL xa::'A::type.
       IN xa x --> <= ((f::'A::type => nat) xa) (DIV b (CARD x))) -->
   <= (nsum x f) b"
  by (import hollight NSUM_BOUND_GEN)

lemma NSUM_BOUND_LT: "ALL (s::'A::type => bool) (f::'A::type => nat) b::nat.
   FINITE s &
   (ALL x::'A::type. IN x s --> <= (f x) b) &
   (EX x::'A::type. IN x s & < (f x) b) -->
   < (nsum s f) (CARD s * b)"
  by (import hollight NSUM_BOUND_LT)

lemma NSUM_BOUND_LT_ALL: "ALL (s::'q_51675::type => bool) (f::'q_51675::type => nat) b::nat.
   FINITE s & s ~= EMPTY & (ALL x::'q_51675::type. IN x s --> < (f x) b) -->
   < (nsum s f) (CARD s * b)"
  by (import hollight NSUM_BOUND_LT_ALL)

lemma NSUM_BOUND_LT_GEN: "ALL (s::'A::type => bool) (t::'q_51717::type) b::nat.
   FINITE s &
   s ~= EMPTY &
   (ALL x::'A::type.
       IN x s --> < ((f::'A::type => nat) x) (DIV b (CARD s))) -->
   < (nsum s f) b"
  by (import hollight NSUM_BOUND_LT_GEN)

lemma NSUM_UNION_EQ: "ALL (s::'q_51776::type => bool) (t::'q_51776::type => bool)
   u::'q_51776::type => bool.
   FINITE u & hollight.INTER s t = EMPTY & hollight.UNION s t = u -->
   nsum s (f::'q_51776::type => nat) + nsum t f = nsum u f"
  by (import hollight NSUM_UNION_EQ)

lemma NSUM_EQ_SUPERSET: "ALL (f::'A::type => nat) (s::'A::type => bool) t::'A::type => bool.
   FINITE t &
   SUBSET t s &
   (ALL x::'A::type. IN x t --> f x = (g::'A::type => nat) x) &
   (ALL x::'A::type. IN x s & ~ IN x t --> f x = 0) -->
   nsum s f = nsum t g"
  by (import hollight NSUM_EQ_SUPERSET)

lemma NSUM_RESTRICT_SET: "ALL (s::'A::type => bool) (f::'A::type => nat) r::'q_51887::type.
   FINITE s -->
   nsum
    (GSPEC
      (%u::'A::type.
          EX x::'A::type. SETSPEC u (IN x s & (P::'A::type => bool) x) x))
    f =
   nsum s (%x::'A::type. COND (P x) (f x) 0)"
  by (import hollight NSUM_RESTRICT_SET)

lemma NSUM_NSUM_RESTRICT: "ALL (R::'q_52016::type => 'q_52015::type => bool)
   (f::'q_52016::type => 'q_52015::type => nat) (s::'q_52016::type => bool)
   t::'q_52015::type => bool.
   FINITE s & FINITE t -->
   nsum s
    (%x::'q_52016::type.
        nsum
         (GSPEC
           (%u::'q_52015::type.
               EX y::'q_52015::type. SETSPEC u (IN y t & R x y) y))
         (f x)) =
   nsum t
    (%y::'q_52015::type.
        nsum
         (GSPEC
           (%u::'q_52016::type.
               EX x::'q_52016::type. SETSPEC u (IN x s & R x y) x))
         (%x::'q_52016::type. f x y))"
  by (import hollight NSUM_NSUM_RESTRICT)

lemma CARD_EQ_NSUM: "ALL x::'q_52035::type => bool.
   FINITE x --> CARD x = nsum x (%x::'q_52035::type. NUMERAL_BIT1 0)"
  by (import hollight CARD_EQ_NSUM)

lemma NSUM_MULTICOUNT_GEN: "ALL (R::'A::type => 'B::type => bool) (s::'A::type => bool)
   (t::'B::type => bool) k::'B::type => nat.
   FINITE s &
   FINITE t &
   (ALL j::'B::type.
       IN j t -->
       CARD
        (GSPEC
          (%u::'A::type. EX i::'A::type. SETSPEC u (IN i s & R i j) i)) =
       k j) -->
   nsum s
    (%i::'A::type.
        CARD
         (GSPEC
           (%u::'B::type. EX j::'B::type. SETSPEC u (IN j t & R i j) j))) =
   nsum t k"
  by (import hollight NSUM_MULTICOUNT_GEN)

lemma NSUM_MULTICOUNT: "ALL (R::'A::type => 'B::type => bool) (s::'A::type => bool)
   (t::'B::type => bool) k::nat.
   FINITE s &
   FINITE t &
   (ALL j::'B::type.
       IN j t -->
       CARD
        (GSPEC
          (%u::'A::type. EX i::'A::type. SETSPEC u (IN i s & R i j) i)) =
       k) -->
   nsum s
    (%i::'A::type.
        CARD
         (GSPEC
           (%u::'B::type. EX j::'B::type. SETSPEC u (IN j t & R i j) j))) =
   k * CARD t"
  by (import hollight NSUM_MULTICOUNT)

lemma NSUM_IMAGE_GEN: "ALL (f::'A::type => 'B::type) (g::'A::type => nat) s::'A::type => bool.
   FINITE s -->
   nsum s g =
   nsum (IMAGE f s)
    (%y::'B::type.
        nsum
         (GSPEC
           (%u::'A::type. EX x::'A::type. SETSPEC u (IN x s & f x = y) x))
         g)"
  by (import hollight NSUM_IMAGE_GEN)

lemma NSUM_SUBSET: "ALL (u::'A::type => bool) (v::'A::type => bool) f::'A::type => nat.
   FINITE u & FINITE v & (ALL x::'A::type. IN x (DIFF u v) --> f x = 0) -->
   <= (nsum u f) (nsum v f)"
  by (import hollight NSUM_SUBSET)

lemma NSUM_SUBSET_SIMPLE: "ALL (u::'q_52495::type => bool) (v::'q_52495::type => bool)
   f::'q_52495::type => nat.
   FINITE v & SUBSET u v --> <= (nsum u f) (nsum v f)"
  by (import hollight NSUM_SUBSET_SIMPLE)

lemma NSUM_ADD_NUMSEG: "ALL (x::nat => nat) (xa::nat => nat) (xb::nat) xc::nat.
   nsum (dotdot xb xc) (%i::nat. x i + xa i) =
   nsum (dotdot xb xc) x + nsum (dotdot xb xc) xa"
  by (import hollight NSUM_ADD_NUMSEG)

lemma NSUM_CMUL_NUMSEG: "ALL (x::nat => nat) (xa::nat) (xb::nat) xc::nat.
   nsum (dotdot xb xc) (%i::nat. xa * x i) = xa * nsum (dotdot xb xc) x"
  by (import hollight NSUM_CMUL_NUMSEG)

lemma NSUM_LE_NUMSEG: "ALL (x::nat => nat) (xa::nat => nat) (xb::nat) xc::nat.
   (ALL i::nat. <= xb i & <= i xc --> <= (x i) (xa i)) -->
   <= (nsum (dotdot xb xc) x) (nsum (dotdot xb xc) xa)"
  by (import hollight NSUM_LE_NUMSEG)

lemma NSUM_EQ_NUMSEG: "ALL (f::nat => nat) (g::nat => nat) (m::nat) n::nat.
   (ALL i::nat. <= m i & <= i n --> f i = g i) -->
   nsum (dotdot m n) f = nsum (dotdot m n) g"
  by (import hollight NSUM_EQ_NUMSEG)

lemma NSUM_CONST_NUMSEG: "ALL (x::nat) (xa::nat) xb::nat.
   nsum (dotdot xa xb) (%n::nat. x) = (xb + NUMERAL_BIT1 0 - xa) * x"
  by (import hollight NSUM_CONST_NUMSEG)

lemma NSUM_EQ_0_NUMSEG: "ALL (x::nat => nat) xa::'q_52734::type.
   (ALL i::nat. <= (m::nat) i & <= i (n::nat) --> x i = 0) -->
   nsum (dotdot m n) x = 0"
  by (import hollight NSUM_EQ_0_NUMSEG)

lemma NSUM_TRIV_NUMSEG: "ALL (f::nat => nat) (m::nat) n::nat. < n m --> nsum (dotdot m n) f = 0"
  by (import hollight NSUM_TRIV_NUMSEG)

lemma NSUM_POS_LE_NUMSEG: "ALL (x::nat) (xa::nat) xb::nat => nat.
   (ALL p::nat. <= x p & <= p xa --> <= 0 (xb p)) -->
   <= 0 (nsum (dotdot x xa) xb)"
  by (import hollight NSUM_POS_LE_NUMSEG)

lemma NSUM_POS_EQ_0_NUMSEG: "ALL (f::nat => nat) (m::nat) n::nat.
   (ALL p::nat. <= m p & <= p n --> <= 0 (f p)) &
   nsum (dotdot m n) f = 0 -->
   (ALL p::nat. <= m p & <= p n --> f p = 0)"
  by (import hollight NSUM_POS_EQ_0_NUMSEG)

lemma NSUM_SING_NUMSEG: "ALL (x::nat => nat) xa::nat. nsum (dotdot xa xa) x = x xa"
  by (import hollight NSUM_SING_NUMSEG)

lemma NSUM_CLAUSES_NUMSEG: "(ALL x::nat. nsum (dotdot x 0) (f::nat => nat) = COND (x = 0) (f 0) 0) &
(ALL (x::nat) xa::nat.
    nsum (dotdot x (Suc xa)) f =
    COND (<= x (Suc xa)) (nsum (dotdot x xa) f + f (Suc xa))
     (nsum (dotdot x xa) f))"
  by (import hollight NSUM_CLAUSES_NUMSEG)

lemma NSUM_SWAP_NUMSEG: "ALL (a::nat) (b::nat) (c::nat) (d::nat) f::nat => nat => nat.
   nsum (dotdot a b) (%i::nat. nsum (dotdot c d) (f i)) =
   nsum (dotdot c d) (%j::nat. nsum (dotdot a b) (%i::nat. f i j))"
  by (import hollight NSUM_SWAP_NUMSEG)

lemma NSUM_ADD_SPLIT: "ALL (x::nat => nat) (xa::nat) (xb::nat) xc::nat.
   <= xa (xb + NUMERAL_BIT1 0) -->
   nsum (dotdot xa (xb + xc)) x =
   nsum (dotdot xa xb) x + nsum (dotdot (xb + NUMERAL_BIT1 0) (xb + xc)) x"
  by (import hollight NSUM_ADD_SPLIT)

lemma NSUM_OFFSET: "ALL (x::nat => nat) (xa::nat) xb::nat.
   nsum (dotdot (xa + xb) ((n::nat) + xb)) x =
   nsum (dotdot xa n) (%i::nat. x (i + xb))"
  by (import hollight NSUM_OFFSET)

lemma NSUM_OFFSET_0: "ALL (x::nat => nat) (xa::nat) xb::nat.
   <= xa xb -->
   nsum (dotdot xa xb) x = nsum (dotdot 0 (xb - xa)) (%i::nat. x (i + xa))"
  by (import hollight NSUM_OFFSET_0)

lemma NSUM_CLAUSES_LEFT: "ALL (x::nat => nat) (xa::nat) xb::nat.
   <= xa xb -->
   nsum (dotdot xa xb) x = x xa + nsum (dotdot (xa + NUMERAL_BIT1 0) xb) x"
  by (import hollight NSUM_CLAUSES_LEFT)

lemma NSUM_CLAUSES_RIGHT: "ALL (f::nat => nat) (m::nat) n::nat.
   < 0 n & <= m n -->
   nsum (dotdot m n) f = nsum (dotdot m (n - NUMERAL_BIT1 0)) f + f n"
  by (import hollight NSUM_CLAUSES_RIGHT)

consts
  sum :: "('q_53311 => bool) => ('q_53311 => hollight.real) => hollight.real" 

defs
  sum_def: "(op ==::(('q_53311::type => bool)
         => ('q_53311::type => hollight.real) => hollight.real)
        => (('q_53311::type => bool)
            => ('q_53311::type => hollight.real) => hollight.real)
           => prop)
 (hollight.sum::('q_53311::type => bool)
                => ('q_53311::type => hollight.real) => hollight.real)
 ((iterate::(hollight.real => hollight.real => hollight.real)
            => ('q_53311::type => bool)
               => ('q_53311::type => hollight.real) => hollight.real)
   (real_add::hollight.real => hollight.real => hollight.real))"

lemma DEF_sum: "(op =::(('q_53311::type => bool)
        => ('q_53311::type => hollight.real) => hollight.real)
       => (('q_53311::type => bool)
           => ('q_53311::type => hollight.real) => hollight.real)
          => bool)
 (hollight.sum::('q_53311::type => bool)
                => ('q_53311::type => hollight.real) => hollight.real)
 ((iterate::(hollight.real => hollight.real => hollight.real)
            => ('q_53311::type => bool)
               => ('q_53311::type => hollight.real) => hollight.real)
   (real_add::hollight.real => hollight.real => hollight.real))"
  by (import hollight DEF_sum)

lemma NEUTRAL_REAL_ADD: "neutral real_add = real_of_num 0"
  by (import hollight NEUTRAL_REAL_ADD)

lemma NEUTRAL_REAL_MUL: "neutral real_mul = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight NEUTRAL_REAL_MUL)

lemma MONOIDAL_REAL_ADD: "monoidal real_add"
  by (import hollight MONOIDAL_REAL_ADD)

lemma MONOIDAL_REAL_MUL: "monoidal real_mul"
  by (import hollight MONOIDAL_REAL_MUL)

lemma SUM_CLAUSES: "(ALL x::'q_53353::type => hollight.real.
    hollight.sum EMPTY x = real_of_num 0) &
(ALL (x::'q_53394::type) (xa::'q_53394::type => hollight.real)
    xb::'q_53394::type => bool.
    FINITE xb -->
    hollight.sum (INSERT x xb) xa =
    COND (IN x xb) (hollight.sum xb xa)
     (real_add (xa x) (hollight.sum xb xa)))"
  by (import hollight SUM_CLAUSES)

lemma SUM_UNION: "ALL (x::'q_53420::type => hollight.real) (xa::'q_53420::type => bool)
   xb::'q_53420::type => bool.
   FINITE xa & FINITE xb & DISJOINT xa xb -->
   hollight.sum (hollight.UNION xa xb) x =
   real_add (hollight.sum xa x) (hollight.sum xb x)"
  by (import hollight SUM_UNION)

lemma SUM_SUPPORT: "ALL (x::'q_53499::type => hollight.real) xa::'q_53499::type => bool.
   FINITE (support real_add x xa) -->
   hollight.sum (support real_add x xa) x = hollight.sum xa x"
  by (import hollight SUM_SUPPORT)

lemma SUM_LT: "ALL (f::'A::type => hollight.real) (g::'A::type => hollight.real)
   s::'A::type => bool.
   FINITE s &
   (ALL x::'A::type. IN x s --> real_le (f x) (g x)) &
   (EX x::'A::type. IN x s & real_lt (f x) (g x)) -->
   real_lt (hollight.sum s f) (hollight.sum s g)"
  by (import hollight SUM_LT)

lemma SUM_LT_ALL: "ALL (f::'q_53825::type => hollight.real)
   (g::'q_53825::type => hollight.real) s::'q_53825::type => bool.
   FINITE s &
   s ~= EMPTY & (ALL x::'q_53825::type. IN x s --> real_lt (f x) (g x)) -->
   real_lt (hollight.sum s f) (hollight.sum s g)"
  by (import hollight SUM_LT_ALL)

lemma SUM_POS_LE: "ALL (x::'q_54040::type => hollight.real) xa::'q_54040::type => bool.
   FINITE xa &
   (ALL xb::'q_54040::type. IN xb xa --> real_le (real_of_num 0) (x xb)) -->
   real_le (real_of_num 0) (hollight.sum xa x)"
  by (import hollight SUM_POS_LE)

lemma SUM_POS_BOUND: "ALL (f::'A::type => hollight.real) (b::hollight.real) x::'A::type => bool.
   FINITE x &
   (ALL xa::'A::type. IN xa x --> real_le (real_of_num 0) (f xa)) &
   real_le (hollight.sum x f) b -->
   (ALL xa::'A::type. IN xa x --> real_le (f xa) b)"
  by (import hollight SUM_POS_BOUND)

lemma SUM_POS_EQ_0: "ALL (x::'q_54187::type => hollight.real) xa::'q_54187::type => bool.
   FINITE xa &
   (ALL xb::'q_54187::type. IN xb xa --> real_le (real_of_num 0) (x xb)) &
   hollight.sum xa x = real_of_num 0 -->
   (ALL xb::'q_54187::type. IN xb xa --> x xb = real_of_num 0)"
  by (import hollight SUM_POS_EQ_0)

lemma SUM_SING: "ALL (x::'q_54209::type => hollight.real) xa::'q_54209::type.
   hollight.sum (INSERT xa EMPTY) x = x xa"
  by (import hollight SUM_SING)

lemma SUM_DELTA: "ALL (x::'A::type => bool) xa::'A::type.
   hollight.sum x
    (%x::'A::type. COND (x = xa) (b::hollight.real) (real_of_num 0)) =
   COND (IN xa x) b (real_of_num 0)"
  by (import hollight SUM_DELTA)

lemma SUM_IMAGE: "ALL (x::'q_54353::type => 'q_54329::type)
   (xa::'q_54329::type => hollight.real) xb::'q_54353::type => bool.
   FINITE xb &
   (ALL (xa::'q_54353::type) y::'q_54353::type.
       IN xa xb & IN y xb & x xa = x y --> xa = y) -->
   hollight.sum (IMAGE x xb) xa = hollight.sum xb (xa o x)"
  by (import hollight SUM_IMAGE)

lemma SUM_SUPERSET: "ALL (f::'A::type => hollight.real) (u::'A::type => bool)
   v::'A::type => bool.
   FINITE u &
   SUBSET u v &
   (ALL x::'A::type. IN x v & ~ IN x u --> f x = real_of_num 0) -->
   hollight.sum v f = hollight.sum u f"
  by (import hollight SUM_SUPERSET)

lemma SUM_UNION_RZERO: "ALL (f::'A::type => hollight.real) (u::'A::type => bool)
   v::'A::type => bool.
   FINITE u &
   (ALL x::'A::type. IN x v & ~ IN x u --> f x = real_of_num 0) -->
   hollight.sum (hollight.UNION u v) f = hollight.sum u f"
  by (import hollight SUM_UNION_RZERO)

lemma SUM_UNION_LZERO: "ALL (f::'A::type => hollight.real) (u::'A::type => bool)
   v::'A::type => bool.
   FINITE v &
   (ALL x::'A::type. IN x u & ~ IN x v --> f x = real_of_num 0) -->
   hollight.sum (hollight.UNION u v) f = hollight.sum v f"
  by (import hollight SUM_UNION_LZERO)

lemma SUM_RESTRICT: "ALL (f::'q_54580::type => hollight.real) s::'q_54580::type => bool.
   FINITE s -->
   hollight.sum s
    (%x::'q_54580::type. COND (IN x s) (f x) (real_of_num 0)) =
   hollight.sum s f"
  by (import hollight SUM_RESTRICT)

lemma SUM_BOUND_GEN: "ALL (s::'A::type => bool) (t::'q_54639::type) b::hollight.real.
   FINITE s &
   s ~= EMPTY &
   (ALL x::'A::type.
       IN x s -->
       real_le ((f::'A::type => hollight.real) x)
        (real_div b (real_of_num (CARD s)))) -->
   real_le (hollight.sum s f) b"
  by (import hollight SUM_BOUND_GEN)

lemma SUM_ABS_BOUND: "ALL (s::'A::type => bool) (f::'A::type => hollight.real) b::hollight.real.
   FINITE s & (ALL x::'A::type. IN x s --> real_le (real_abs (f x)) b) -->
   real_le (real_abs (hollight.sum s f)) (real_mul (real_of_num (CARD s)) b)"
  by (import hollight SUM_ABS_BOUND)

lemma SUM_BOUND_LT: "ALL (s::'A::type => bool) (f::'A::type => hollight.real) b::hollight.real.
   FINITE s &
   (ALL x::'A::type. IN x s --> real_le (f x) b) &
   (EX x::'A::type. IN x s & real_lt (f x) b) -->
   real_lt (hollight.sum s f) (real_mul (real_of_num (CARD s)) b)"
  by (import hollight SUM_BOUND_LT)

lemma SUM_BOUND_LT_ALL: "ALL (s::'q_54844::type => bool) (f::'q_54844::type => hollight.real)
   b::hollight.real.
   FINITE s &
   s ~= EMPTY & (ALL x::'q_54844::type. IN x s --> real_lt (f x) b) -->
   real_lt (hollight.sum s f) (real_mul (real_of_num (CARD s)) b)"
  by (import hollight SUM_BOUND_LT_ALL)

lemma SUM_BOUND_LT_GEN: "ALL (s::'A::type => bool) (t::'q_54866::type) b::hollight.real.
   FINITE s &
   s ~= EMPTY &
   (ALL x::'A::type.
       IN x s -->
       real_lt ((f::'A::type => hollight.real) x)
        (real_div b (real_of_num (CARD s)))) -->
   real_lt (hollight.sum s f) b"
  by (import hollight SUM_BOUND_LT_GEN)

lemma SUM_UNION_EQ: "ALL (s::'q_54927::type => bool) (t::'q_54927::type => bool)
   u::'q_54927::type => bool.
   FINITE u & hollight.INTER s t = EMPTY & hollight.UNION s t = u -->
   real_add (hollight.sum s (f::'q_54927::type => hollight.real))
    (hollight.sum t f) =
   hollight.sum u f"
  by (import hollight SUM_UNION_EQ)

lemma SUM_EQ_SUPERSET: "ALL (f::'A::type => hollight.real) (s::'A::type => bool)
   t::'A::type => bool.
   FINITE t &
   SUBSET t s &
   (ALL x::'A::type. IN x t --> f x = (g::'A::type => hollight.real) x) &
   (ALL x::'A::type. IN x s & ~ IN x t --> f x = real_of_num 0) -->
   hollight.sum s f = hollight.sum t g"
  by (import hollight SUM_EQ_SUPERSET)

lemma SUM_RESTRICT_SET: "ALL (s::'A::type => bool) (f::'A::type => hollight.real) r::'q_55040::type.
   FINITE s -->
   hollight.sum
    (GSPEC
      (%u::'A::type.
          EX x::'A::type. SETSPEC u (IN x s & (P::'A::type => bool) x) x))
    f =
   hollight.sum s (%x::'A::type. COND (P x) (f x) (real_of_num 0))"
  by (import hollight SUM_RESTRICT_SET)

lemma SUM_SUM_RESTRICT: "ALL (R::'q_55171::type => 'q_55170::type => bool)
   (f::'q_55171::type => 'q_55170::type => hollight.real)
   (s::'q_55171::type => bool) t::'q_55170::type => bool.
   FINITE s & FINITE t -->
   hollight.sum s
    (%x::'q_55171::type.
        hollight.sum
         (GSPEC
           (%u::'q_55170::type.
               EX y::'q_55170::type. SETSPEC u (IN y t & R x y) y))
         (f x)) =
   hollight.sum t
    (%y::'q_55170::type.
        hollight.sum
         (GSPEC
           (%u::'q_55171::type.
               EX x::'q_55171::type. SETSPEC u (IN x s & R x y) x))
         (%x::'q_55171::type. f x y))"
  by (import hollight SUM_SUM_RESTRICT)

lemma CARD_EQ_SUM: "ALL x::'q_55192::type => bool.
   FINITE x -->
   real_of_num (CARD x) =
   hollight.sum x (%x::'q_55192::type. real_of_num (NUMERAL_BIT1 0))"
  by (import hollight CARD_EQ_SUM)

lemma SUM_MULTICOUNT_GEN: "ALL (R::'A::type => 'B::type => bool) (s::'A::type => bool)
   (t::'B::type => bool) k::'B::type => nat.
   FINITE s &
   FINITE t &
   (ALL j::'B::type.
       IN j t -->
       CARD
        (GSPEC
          (%u::'A::type. EX i::'A::type. SETSPEC u (IN i s & R i j) i)) =
       k j) -->
   hollight.sum s
    (%i::'A::type.
        real_of_num
         (CARD
           (GSPEC
             (%u::'B::type.
                 EX j::'B::type. SETSPEC u (IN j t & R i j) j)))) =
   hollight.sum t (%i::'B::type. real_of_num (k i))"
  by (import hollight SUM_MULTICOUNT_GEN)

lemma SUM_MULTICOUNT: "ALL (R::'A::type => 'B::type => bool) (s::'A::type => bool)
   (t::'B::type => bool) k::nat.
   FINITE s &
   FINITE t &
   (ALL j::'B::type.
       IN j t -->
       CARD
        (GSPEC
          (%u::'A::type. EX i::'A::type. SETSPEC u (IN i s & R i j) i)) =
       k) -->
   hollight.sum s
    (%i::'A::type.
        real_of_num
         (CARD
           (GSPEC
             (%u::'B::type.
                 EX j::'B::type. SETSPEC u (IN j t & R i j) j)))) =
   real_of_num (k * CARD t)"
  by (import hollight SUM_MULTICOUNT)

lemma SUM_IMAGE_GEN: "ALL (f::'A::type => 'B::type) (g::'A::type => hollight.real)
   s::'A::type => bool.
   FINITE s -->
   hollight.sum s g =
   hollight.sum (IMAGE f s)
    (%y::'B::type.
        hollight.sum
         (GSPEC
           (%u::'A::type. EX x::'A::type. SETSPEC u (IN x s & f x = y) x))
         g)"
  by (import hollight SUM_IMAGE_GEN)

lemma REAL_OF_NUM_SUM: "ALL (f::'q_55589::type => nat) s::'q_55589::type => bool.
   FINITE s -->
   real_of_num (nsum s f) =
   hollight.sum s (%x::'q_55589::type. real_of_num (f x))"
  by (import hollight REAL_OF_NUM_SUM)

lemma SUM_SUBSET: "ALL (u::'A::type => bool) (v::'A::type => bool)
   f::'A::type => hollight.real.
   FINITE u &
   FINITE v &
   (ALL x::'A::type. IN x (DIFF u v) --> real_le (f x) (real_of_num 0)) &
   (ALL x::'A::type. IN x (DIFF v u) --> real_le (real_of_num 0) (f x)) -->
   real_le (hollight.sum u f) (hollight.sum v f)"
  by (import hollight SUM_SUBSET)

lemma SUM_SUBSET_SIMPLE: "ALL (u::'A::type => bool) (v::'A::type => bool)
   f::'A::type => hollight.real.
   FINITE v &
   SUBSET u v &
   (ALL x::'A::type. IN x (DIFF v u) --> real_le (real_of_num 0) (f x)) -->
   real_le (hollight.sum u f) (hollight.sum v f)"
  by (import hollight SUM_SUBSET_SIMPLE)

lemma SUM_ADD_NUMSEG: "ALL (x::nat => hollight.real) (xa::nat => hollight.real) (xb::nat) xc::nat.
   hollight.sum (dotdot xb xc) (%i::nat. real_add (x i) (xa i)) =
   real_add (hollight.sum (dotdot xb xc) x) (hollight.sum (dotdot xb xc) xa)"
  by (import hollight SUM_ADD_NUMSEG)

lemma SUM_CMUL_NUMSEG: "ALL (x::nat => hollight.real) (xa::hollight.real) (xb::nat) xc::nat.
   hollight.sum (dotdot xb xc) (%i::nat. real_mul xa (x i)) =
   real_mul xa (hollight.sum (dotdot xb xc) x)"
  by (import hollight SUM_CMUL_NUMSEG)

lemma SUM_NEG_NUMSEG: "ALL (x::nat => hollight.real) (xa::nat) xb::nat.
   hollight.sum (dotdot xa xb) (%i::nat. real_neg (x i)) =
   real_neg (hollight.sum (dotdot xa xb) x)"
  by (import hollight SUM_NEG_NUMSEG)

lemma SUM_SUB_NUMSEG: "ALL (x::nat => hollight.real) (xa::nat => hollight.real) (xb::nat) xc::nat.
   hollight.sum (dotdot xb xc) (%i::nat. real_sub (x i) (xa i)) =
   real_sub (hollight.sum (dotdot xb xc) x) (hollight.sum (dotdot xb xc) xa)"
  by (import hollight SUM_SUB_NUMSEG)

lemma SUM_LE_NUMSEG: "ALL (x::nat => hollight.real) (xa::nat => hollight.real) (xb::nat) xc::nat.
   (ALL i::nat. <= xb i & <= i xc --> real_le (x i) (xa i)) -->
   real_le (hollight.sum (dotdot xb xc) x) (hollight.sum (dotdot xb xc) xa)"
  by (import hollight SUM_LE_NUMSEG)

lemma SUM_EQ_NUMSEG: "ALL (f::nat => hollight.real) (g::nat => hollight.real) (m::nat) n::nat.
   (ALL i::nat. <= m i & <= i n --> f i = g i) -->
   hollight.sum (dotdot m n) f = hollight.sum (dotdot m n) g"
  by (import hollight SUM_EQ_NUMSEG)

lemma SUM_ABS_NUMSEG: "ALL (x::nat => hollight.real) (xa::nat) xb::nat.
   real_le (real_abs (hollight.sum (dotdot xa xb) x))
    (hollight.sum (dotdot xa xb) (%i::nat. real_abs (x i)))"
  by (import hollight SUM_ABS_NUMSEG)

lemma SUM_CONST_NUMSEG: "ALL (x::hollight.real) (xa::nat) xb::nat.
   hollight.sum (dotdot xa xb) (%n::nat. x) =
   real_mul (real_of_num (xb + NUMERAL_BIT1 0 - xa)) x"
  by (import hollight SUM_CONST_NUMSEG)

lemma SUM_EQ_0_NUMSEG: "ALL (x::nat => hollight.real) xa::'q_56115::type.
   (ALL i::nat. <= (m::nat) i & <= i (n::nat) --> x i = real_of_num 0) -->
   hollight.sum (dotdot m n) x = real_of_num 0"
  by (import hollight SUM_EQ_0_NUMSEG)

lemma SUM_TRIV_NUMSEG: "ALL (f::nat => hollight.real) (m::nat) n::nat.
   < n m --> hollight.sum (dotdot m n) f = real_of_num 0"
  by (import hollight SUM_TRIV_NUMSEG)

lemma SUM_POS_LE_NUMSEG: "ALL (x::nat) (xa::nat) xb::nat => hollight.real.
   (ALL p::nat. <= x p & <= p xa --> real_le (real_of_num 0) (xb p)) -->
   real_le (real_of_num 0) (hollight.sum (dotdot x xa) xb)"
  by (import hollight SUM_POS_LE_NUMSEG)

lemma SUM_POS_EQ_0_NUMSEG: "ALL (f::nat => hollight.real) (m::nat) n::nat.
   (ALL p::nat. <= m p & <= p n --> real_le (real_of_num 0) (f p)) &
   hollight.sum (dotdot m n) f = real_of_num 0 -->
   (ALL p::nat. <= m p & <= p n --> f p = real_of_num 0)"
  by (import hollight SUM_POS_EQ_0_NUMSEG)

lemma SUM_SING_NUMSEG: "ALL (x::nat => hollight.real) xa::nat. hollight.sum (dotdot xa xa) x = x xa"
  by (import hollight SUM_SING_NUMSEG)

lemma SUM_CLAUSES_NUMSEG: "(ALL x::nat.
    hollight.sum (dotdot x 0) (f::nat => hollight.real) =
    COND (x = 0) (f 0) (real_of_num 0)) &
(ALL (x::nat) xa::nat.
    hollight.sum (dotdot x (Suc xa)) f =
    COND (<= x (Suc xa))
     (real_add (hollight.sum (dotdot x xa) f) (f (Suc xa)))
     (hollight.sum (dotdot x xa) f))"
  by (import hollight SUM_CLAUSES_NUMSEG)

lemma SUM_SWAP_NUMSEG: "ALL (a::nat) (b::nat) (c::nat) (d::nat) f::nat => nat => hollight.real.
   hollight.sum (dotdot a b) (%i::nat. hollight.sum (dotdot c d) (f i)) =
   hollight.sum (dotdot c d)
    (%j::nat. hollight.sum (dotdot a b) (%i::nat. f i j))"
  by (import hollight SUM_SWAP_NUMSEG)

lemma SUM_ADD_SPLIT: "ALL (x::nat => hollight.real) (xa::nat) (xb::nat) xc::nat.
   <= xa (xb + NUMERAL_BIT1 0) -->
   hollight.sum (dotdot xa (xb + xc)) x =
   real_add (hollight.sum (dotdot xa xb) x)
    (hollight.sum (dotdot (xb + NUMERAL_BIT1 0) (xb + xc)) x)"
  by (import hollight SUM_ADD_SPLIT)

lemma SUM_OFFSET_0: "ALL (x::nat => hollight.real) (xa::nat) xb::nat.
   <= xa xb -->
   hollight.sum (dotdot xa xb) x =
   hollight.sum (dotdot 0 (xb - xa)) (%i::nat. x (i + xa))"
  by (import hollight SUM_OFFSET_0)

lemma SUM_CLAUSES_LEFT: "ALL (x::nat => hollight.real) (xa::nat) xb::nat.
   <= xa xb -->
   hollight.sum (dotdot xa xb) x =
   real_add (x xa) (hollight.sum (dotdot (xa + NUMERAL_BIT1 0) xb) x)"
  by (import hollight SUM_CLAUSES_LEFT)

lemma SUM_CLAUSES_RIGHT: "ALL (f::nat => hollight.real) (m::nat) n::nat.
   < 0 n & <= m n -->
   hollight.sum (dotdot m n) f =
   real_add (hollight.sum (dotdot m (n - NUMERAL_BIT1 0)) f) (f n)"
  by (import hollight SUM_CLAUSES_RIGHT)

lemma REAL_OF_NUM_SUM_NUMSEG: "ALL (x::nat => nat) (xa::nat) xb::nat.
   real_of_num (nsum (dotdot xa xb) x) =
   hollight.sum (dotdot xa xb) (%i::nat. real_of_num (x i))"
  by (import hollight REAL_OF_NUM_SUM_NUMSEG)

constdefs
  CASEWISE :: "(('q_56787 => 'q_56791) * ('q_56792 => 'q_56787 => 'q_56751)) hollight.list
=> 'q_56792 => 'q_56791 => 'q_56751" 
  "CASEWISE ==
SOME CASEWISE::(('q_56787::type => 'q_56791::type) *
                ('q_56792::type
                 => 'q_56787::type => 'q_56751::type)) hollight.list
               => 'q_56792::type => 'q_56791::type => 'q_56751::type.
   (ALL (f::'q_56792::type) x::'q_56791::type.
       CASEWISE NIL f x = (SOME y::'q_56751::type. True)) &
   (ALL (h::('q_56787::type => 'q_56791::type) *
            ('q_56792::type => 'q_56787::type => 'q_56751::type))
       (t::(('q_56787::type => 'q_56791::type) *
            ('q_56792::type
             => 'q_56787::type => 'q_56751::type)) hollight.list)
       (f::'q_56792::type) x::'q_56791::type.
       CASEWISE (CONS h t) f x =
       COND (EX y::'q_56787::type. fst h y = x)
        (snd h f (SOME y::'q_56787::type. fst h y = x)) (CASEWISE t f x))"

lemma DEF_CASEWISE: "CASEWISE =
(SOME CASEWISE::(('q_56787::type => 'q_56791::type) *
                 ('q_56792::type
                  => 'q_56787::type => 'q_56751::type)) hollight.list
                => 'q_56792::type => 'q_56791::type => 'q_56751::type.
    (ALL (f::'q_56792::type) x::'q_56791::type.
        CASEWISE NIL f x = (SOME y::'q_56751::type. True)) &
    (ALL (h::('q_56787::type => 'q_56791::type) *
             ('q_56792::type => 'q_56787::type => 'q_56751::type))
        (t::(('q_56787::type => 'q_56791::type) *
             ('q_56792::type
              => 'q_56787::type => 'q_56751::type)) hollight.list)
        (f::'q_56792::type) x::'q_56791::type.
        CASEWISE (CONS h t) f x =
        COND (EX y::'q_56787::type. fst h y = x)
         (snd h f (SOME y::'q_56787::type. fst h y = x)) (CASEWISE t f x)))"
  by (import hollight DEF_CASEWISE)

lemma CASEWISE: "(op &::bool => bool => bool)
 ((op =::'q_56811::type => 'q_56811::type => bool)
   ((CASEWISE::(('q_56803::type => 'q_56851::type) *
                ('q_56852::type
                 => 'q_56803::type => 'q_56811::type)) hollight.list
               => 'q_56852::type => 'q_56851::type => 'q_56811::type)
     (NIL::(('q_56803::type => 'q_56851::type) *
            ('q_56852::type
             => 'q_56803::type => 'q_56811::type)) hollight.list)
     (f::'q_56852::type) (x::'q_56851::type))
   ((Eps::('q_56811::type => bool) => 'q_56811::type)
     (%y::'q_56811::type. True::bool)))
 ((op =::'q_56812::type => 'q_56812::type => bool)
   ((CASEWISE::(('q_56854::type => 'q_56851::type) *
                ('q_56852::type
                 => 'q_56854::type => 'q_56812::type)) hollight.list
               => 'q_56852::type => 'q_56851::type => 'q_56812::type)
     ((CONS::('q_56854::type => 'q_56851::type) *
             ('q_56852::type => 'q_56854::type => 'q_56812::type)
             => (('q_56854::type => 'q_56851::type) *
                 ('q_56852::type
                  => 'q_56854::type => 'q_56812::type)) hollight.list
                => (('q_56854::type => 'q_56851::type) *
                    ('q_56852::type
                     => 'q_56854::type => 'q_56812::type)) hollight.list)
       ((Pair::('q_56854::type => 'q_56851::type)
               => ('q_56852::type => 'q_56854::type => 'q_56812::type)
                  => ('q_56854::type => 'q_56851::type) *
                     ('q_56852::type => 'q_56854::type => 'q_56812::type))
         (s::'q_56854::type => 'q_56851::type)
         (t::'q_56852::type => 'q_56854::type => 'q_56812::type))
       (clauses::(('q_56854::type => 'q_56851::type) *
                  ('q_56852::type
                   => 'q_56854::type => 'q_56812::type)) hollight.list))
     f x)
   ((COND::bool => 'q_56812::type => 'q_56812::type => 'q_56812::type)
     ((Ex::('q_56854::type => bool) => bool)
       (%y::'q_56854::type.
           (op =::'q_56851::type => 'q_56851::type => bool) (s y) x))
     (t f ((Eps::('q_56854::type => bool) => 'q_56854::type)
            (%y::'q_56854::type.
                (op =::'q_56851::type => 'q_56851::type => bool) (s y) x)))
     ((CASEWISE::(('q_56854::type => 'q_56851::type) *
                  ('q_56852::type
                   => 'q_56854::type => 'q_56812::type)) hollight.list
                 => 'q_56852::type => 'q_56851::type => 'q_56812::type)
       clauses f x)))"
  by (import hollight CASEWISE)

lemma CASEWISE_CASES: "ALL (clauses::(('q_56946::type => 'q_56943::type) *
               ('q_56944::type
                => 'q_56946::type => 'q_56953::type)) hollight.list)
   (c::'q_56944::type) x::'q_56943::type.
   (EX (s::'q_56946::type => 'q_56943::type)
       (t::'q_56944::type => 'q_56946::type => 'q_56953::type)
       a::'q_56946::type.
       MEM (s, t) clauses & s a = x & CASEWISE clauses c x = t c a) |
   ~ (EX (s::'q_56946::type => 'q_56943::type)
         (t::'q_56944::type => 'q_56946::type => 'q_56953::type)
         a::'q_56946::type. MEM (s, t) clauses & s a = x) &
   CASEWISE clauses c x = (SOME y::'q_56953::type. True)"
  by (import hollight CASEWISE_CASES)

lemma CASEWISE_WORKS: "ALL (x::(('P::type => 'A::type) *
         ('C::type => 'P::type => 'B::type)) hollight.list)
   xa::'C::type.
   (ALL (s::'P::type => 'A::type) (t::'C::type => 'P::type => 'B::type)
       (s'::'P::type => 'A::type) (t'::'C::type => 'P::type => 'B::type)
       (xb::'P::type) y::'P::type.
       MEM (s, t) x & MEM (s', t') x & s xb = s' y -->
       t xa xb = t' xa y) -->
   ALL_list
    (GABS
      (%f::('P::type => 'A::type) * ('C::type => 'P::type => 'B::type)
           => bool.
          ALL (s::'P::type => 'A::type) t::'C::type => 'P::type => 'B::type.
             GEQ (f (s, t))
              (ALL xb::'P::type. CASEWISE x xa (s xb) = t xa xb)))
    x"
  by (import hollight CASEWISE_WORKS)

constdefs
  admissible :: "('q_57089 => 'q_57082 => bool)
=> (('q_57089 => 'q_57085) => 'q_57095 => bool)
   => ('q_57095 => 'q_57082)
      => (('q_57089 => 'q_57085) => 'q_57095 => 'q_57090) => bool" 
  "admissible ==
%(u::'q_57089::type => 'q_57082::type => bool)
   (ua::('q_57089::type => 'q_57085::type) => 'q_57095::type => bool)
   (ub::'q_57095::type => 'q_57082::type)
   uc::('q_57089::type => 'q_57085::type)
       => 'q_57095::type => 'q_57090::type.
   ALL (f::'q_57089::type => 'q_57085::type)
      (g::'q_57089::type => 'q_57085::type) a::'q_57095::type.
      ua f a &
      ua g a & (ALL z::'q_57089::type. u z (ub a) --> f z = g z) -->
      uc f a = uc g a"

lemma DEF_admissible: "admissible =
(%(u::'q_57089::type => 'q_57082::type => bool)
    (ua::('q_57089::type => 'q_57085::type) => 'q_57095::type => bool)
    (ub::'q_57095::type => 'q_57082::type)
    uc::('q_57089::type => 'q_57085::type)
        => 'q_57095::type => 'q_57090::type.
    ALL (f::'q_57089::type => 'q_57085::type)
       (g::'q_57089::type => 'q_57085::type) a::'q_57095::type.
       ua f a &
       ua g a & (ALL z::'q_57089::type. u z (ub a) --> f z = g z) -->
       uc f a = uc g a)"
  by (import hollight DEF_admissible)

constdefs
  tailadmissible :: "('A => 'A => bool)
=> (('A => 'B) => 'P => bool)
   => ('P => 'A) => (('A => 'B) => 'P => 'B) => bool" 
  "tailadmissible ==
%(u::'A::type => 'A::type => bool)
   (ua::('A::type => 'B::type) => 'P::type => bool)
   (ub::'P::type => 'A::type)
   uc::('A::type => 'B::type) => 'P::type => 'B::type.
   EX (P::('A::type => 'B::type) => 'P::type => bool)
      (G::('A::type => 'B::type) => 'P::type => 'A::type)
      H::('A::type => 'B::type) => 'P::type => 'B::type.
      (ALL (f::'A::type => 'B::type) (a::'P::type) y::'A::type.
          P f a & u y (G f a) --> u y (ub a)) &
      (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) a::'P::type.
          (ALL z::'A::type. u z (ub a) --> f z = g z) -->
          P f a = P g a & G f a = G g a & H f a = H g a) &
      (ALL (f::'A::type => 'B::type) a::'P::type.
          ua f a --> uc f a = COND (P f a) (f (G f a)) (H f a))"

lemma DEF_tailadmissible: "tailadmissible =
(%(u::'A::type => 'A::type => bool)
    (ua::('A::type => 'B::type) => 'P::type => bool)
    (ub::'P::type => 'A::type)
    uc::('A::type => 'B::type) => 'P::type => 'B::type.
    EX (P::('A::type => 'B::type) => 'P::type => bool)
       (G::('A::type => 'B::type) => 'P::type => 'A::type)
       H::('A::type => 'B::type) => 'P::type => 'B::type.
       (ALL (f::'A::type => 'B::type) (a::'P::type) y::'A::type.
           P f a & u y (G f a) --> u y (ub a)) &
       (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) a::'P::type.
           (ALL z::'A::type. u z (ub a) --> f z = g z) -->
           P f a = P g a & G f a = G g a & H f a = H g a) &
       (ALL (f::'A::type => 'B::type) a::'P::type.
           ua f a --> uc f a = COND (P f a) (f (G f a)) (H f a)))"
  by (import hollight DEF_tailadmissible)

constdefs
  superadmissible :: "('q_57239 => 'q_57239 => bool)
=> (('q_57239 => 'q_57241) => 'q_57247 => bool)
   => ('q_57247 => 'q_57239)
      => (('q_57239 => 'q_57241) => 'q_57247 => 'q_57241) => bool" 
  "superadmissible ==
%(u::'q_57239::type => 'q_57239::type => bool)
   (ua::('q_57239::type => 'q_57241::type) => 'q_57247::type => bool)
   (ub::'q_57247::type => 'q_57239::type)
   uc::('q_57239::type => 'q_57241::type)
       => 'q_57247::type => 'q_57241::type.
   admissible u
    (%(f::'q_57239::type => 'q_57241::type) a::'q_57247::type. True) ub
    ua -->
   tailadmissible u ua ub uc"

lemma DEF_superadmissible: "superadmissible =
(%(u::'q_57239::type => 'q_57239::type => bool)
    (ua::('q_57239::type => 'q_57241::type) => 'q_57247::type => bool)
    (ub::'q_57247::type => 'q_57239::type)
    uc::('q_57239::type => 'q_57241::type)
        => 'q_57247::type => 'q_57241::type.
    admissible u
     (%(f::'q_57239::type => 'q_57241::type) a::'q_57247::type. True) ub
     ua -->
    tailadmissible u ua ub uc)"
  by (import hollight DEF_superadmissible)

lemma SUPERADMISSIBLE_COND: "ALL (x::'A::type => 'A::type => bool)
   (xa::('A::type => 'B::type) => 'P::type => bool)
   (xb::('A::type => 'B::type) => 'P::type => bool)
   (xc::'P::type => 'A::type)
   (xd::('A::type => 'B::type) => 'P::type => 'B::type)
   xe::('A::type => 'B::type) => 'P::type => 'B::type.
   admissible x xa xc xb &
   superadmissible x
    (%(f::'A::type => 'B::type) x::'P::type. xa f x & xb f x) xc xd &
   superadmissible x
    (%(f::'A::type => 'B::type) x::'P::type. xa f x & ~ xb f x) xc xe -->
   superadmissible x xa xc
    (%(f::'A::type => 'B::type) x::'P::type.
        COND (xb f x) (xd f x) (xe f x))"
  by (import hollight SUPERADMISSIBLE_COND)

lemma ADMISSIBLE_IMP_SUPERADMISSIBLE: "ALL (x::'A::type => 'A::type => bool)
   (xa::('A::type => 'B::type) => 'P::type => bool)
   (xb::'P::type => 'A::type)
   xc::('A::type => 'B::type) => 'P::type => 'B::type.
   admissible x xa xb xc --> superadmissible x xa xb xc"
  by (import hollight ADMISSIBLE_IMP_SUPERADMISSIBLE)

lemma TAIL_IMP_SUPERADMISSIBLE: "ALL (x::'A::type => 'A::type => bool)
   (xa::('A::type => 'B::type) => 'P::type => bool)
   (xb::'P::type => 'A::type)
   xc::('A::type => 'B::type) => 'P::type => 'A::type.
   admissible x xa xb xc &
   (ALL (f::'A::type => 'B::type) a::'P::type.
       xa f a --> (ALL y::'A::type. x y (xc f a) --> x y (xb a))) -->
   superadmissible x xa xb
    (%(f::'A::type => 'B::type) x::'P::type. f (xc f x))"
  by (import hollight TAIL_IMP_SUPERADMISSIBLE)

lemma ADMISSIBLE_COND: "ALL (u_354::'A::type => 'q_57627::type => bool)
   (p::('A::type => 'B::type) => 'P::type => bool)
   (P::('A::type => 'B::type) => 'P::type => bool)
   (s::'P::type => 'q_57627::type)
   (h::('A::type => 'B::type) => 'P::type => 'B::type)
   k::('A::type => 'B::type) => 'P::type => 'B::type.
   admissible u_354 p s P &
   admissible u_354 (%(f::'A::type => 'B::type) x::'P::type. p f x & P f x)
    s h &
   admissible u_354
    (%(f::'A::type => 'B::type) x::'P::type. p f x & ~ P f x) s k -->
   admissible u_354 p s
    (%(f::'A::type => 'B::type) x::'P::type. COND (P f x) (h f x) (k f x))"
  by (import hollight ADMISSIBLE_COND)

lemma ADMISSIBLE_CONST: "admissible (u_354::'q_57702::type => 'q_57701::type => bool)
 (p::('q_57702::type => 'q_57703::type) => 'q_57704::type => bool)
 (s::'q_57704::type => 'q_57701::type)
 (%f::'q_57702::type => 'q_57703::type. c::'q_57704::type => 'q_57705::type)"
  by (import hollight ADMISSIBLE_CONST)

lemma ADMISSIBLE_COMB: "ALL (x::'A::type => 'A::type => bool)
   (xa::('A::type => 'B::type) => 'P::type => bool)
   (xb::'P::type => 'A::type)
   (xc::('A::type => 'B::type) => 'P::type => 'C::type => 'D::type)
   xd::('A::type => 'B::type) => 'P::type => 'C::type.
   admissible x xa xb xc & admissible x xa xb xd -->
   admissible x xa xb
    (%(f::'A::type => 'B::type) x::'P::type. xc f x (xd f x))"
  by (import hollight ADMISSIBLE_COMB)

lemma ADMISSIBLE_BASE: "ALL (x::'A::type => 'A::type => bool)
   (xa::('A::type => 'B::type) => 'P::type => bool)
   (xb::'P::type => 'A::type) xc::'P::type => 'A::type.
   (ALL (f::'A::type => 'B::type) a::'P::type.
       xa f a --> x (xc a) (xb a)) -->
   admissible x xa xb (%(f::'A::type => 'B::type) x::'P::type. f (xc x))"
  by (import hollight ADMISSIBLE_BASE)

lemma ADMISSIBLE_NEST: "ALL (x::'A::type => 'A::type => bool)
   (xa::('A::type => 'B::type) => 'P::type => bool)
   (xb::'P::type => 'A::type)
   xc::('A::type => 'B::type) => 'P::type => 'A::type.
   admissible x xa xb xc &
   (ALL (f::'A::type => 'B::type) a::'P::type.
       xa f a --> x (xc f a) (xb a)) -->
   admissible x xa xb (%(f::'A::type => 'B::type) x::'P::type. f (xc f x))"
  by (import hollight ADMISSIBLE_NEST)

lemma ADMISSIBLE_LAMBDA: "ALL (x::'A::type => 'A::type => bool)
   (xa::('A::type => 'B::type) => 'P::type => bool)
   (xb::'P::type => 'A::type)
   xc::'C::type => ('A::type => 'B::type) => 'P::type => 'D::type.
   (ALL xd::'C::type. admissible x xa xb (xc xd)) -->
   admissible x xa xb
    (%(f::'A::type => 'B::type) (x::'P::type) u::'C::type. xc u f x)"
  by (import hollight ADMISSIBLE_LAMBDA)

lemma WF_REC_CASES: "ALL (u_354::'A::type => 'A::type => bool)
   clauses::(('P::type => 'A::type) *
             (('A::type => 'B::type)
              => 'P::type => 'B::type)) hollight.list.
   WF u_354 &
   ALL_list
    (GABS
      (%f::('P::type => 'A::type) *
           (('A::type => 'B::type) => 'P::type => 'B::type)
           => bool.
          ALL (s::'P::type => 'A::type)
             t::('A::type => 'B::type) => 'P::type => 'B::type.
             GEQ (f (s, t))
              (EX (P::('A::type => 'B::type) => 'P::type => bool)
                  (G::('A::type => 'B::type) => 'P::type => 'A::type)
                  H::('A::type => 'B::type) => 'P::type => 'B::type.
                  (ALL (f::'A::type => 'B::type) (a::'P::type) y::'A::type.
                      P f a & u_354 y (G f a) --> u_354 y (s a)) &
                  (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type)
                      a::'P::type.
                      (ALL z::'A::type. u_354 z (s a) --> f z = g z) -->
                      P f a = P g a & G f a = G g a & H f a = H g a) &
                  (ALL (f::'A::type => 'B::type) a::'P::type.
                      t f a = COND (P f a) (f (G f a)) (H f a)))))
    clauses -->
   (EX f::'A::type => 'B::type. ALL x::'A::type. f x = CASEWISE clauses f x)"
  by (import hollight WF_REC_CASES)

lemma RECURSION_CASEWISE: "ALL clauses::(('P::type => 'A::type) *
              (('A::type => 'B::type)
               => 'P::type => 'B::type)) hollight.list.
   (EX u::'A::type => 'A::type => bool.
       WF u &
       ALL_list
        (GABS
          (%f::('P::type => 'A::type) *
               (('A::type => 'B::type) => 'P::type => 'B::type)
               => bool.
              ALL (s::'P::type => 'A::type)
                 t::('A::type => 'B::type) => 'P::type => 'B::type.
                 GEQ (f (s, t))
                  (tailadmissible u
                    (%(f::'A::type => 'B::type) a::'P::type. True) s t)))
        clauses) &
   (ALL (x::'P::type => 'A::type)
       (xa::('A::type => 'B::type) => 'P::type => 'B::type)
       (xb::'P::type => 'A::type)
       (xc::('A::type => 'B::type) => 'P::type => 'B::type)
       (xd::'A::type => 'B::type) (xe::'P::type) xf::'P::type.
       MEM (x, xa) clauses & MEM (xb, xc) clauses -->
       x xe = xb xf --> xa xd xe = xc xd xf) -->
   (EX f::'A::type => 'B::type.
       ALL_list
        (GABS
          (%fa::('P::type => 'A::type) *
                (('A::type => 'B::type) => 'P::type => 'B::type)
                => bool.
              ALL (s::'P::type => 'A::type)
                 t::('A::type => 'B::type) => 'P::type => 'B::type.
                 GEQ (fa (s, t)) (ALL x::'P::type. f (s x) = t f x)))
        clauses)"
  by (import hollight RECURSION_CASEWISE)

lemma cth: "ALL (p1::'A::type => 'q_58634::type)
   (p2::'q_58645::type => 'A::type => 'q_58639::type)
   (p1'::'A::type => 'q_58634::type)
   p2'::'q_58645::type => 'A::type => 'q_58639::type.
   (ALL (c::'q_58645::type) (x::'A::type) y::'A::type.
       p1 x = p1' y --> p2 c x = p2' c y) -->
   (ALL (c::'q_58645::type) (x::'A::type) y::'A::type.
       p1' x = p1 y --> p2' c x = p2 c y)"
  by (import hollight cth)

lemma RECURSION_CASEWISE_PAIRWISE: "ALL x::(('q_58682::type => 'q_58662::type) *
        (('q_58662::type => 'q_58678::type)
         => 'q_58682::type => 'q_58678::type)) hollight.list.
   (EX u::'q_58662::type => 'q_58662::type => bool.
       WF u &
       ALL_list
        (GABS
          (%f::('q_58682::type => 'q_58662::type) *
               (('q_58662::type => 'q_58678::type)
                => 'q_58682::type => 'q_58678::type)
               => bool.
              ALL (s::'q_58682::type => 'q_58662::type)
                 t::('q_58662::type => 'q_58678::type)
                    => 'q_58682::type => 'q_58678::type.
                 GEQ (f (s, t))
                  (tailadmissible u
                    (%(f::'q_58662::type => 'q_58678::type)
                        a::'q_58682::type. True)
                    s t)))
        x) &
   ALL_list
    (GABS
      (%f::('q_58682::type => 'q_58662::type) *
           (('q_58662::type => 'q_58678::type)
            => 'q_58682::type => 'q_58678::type)
           => bool.
          ALL (a::'q_58682::type => 'q_58662::type)
             b::('q_58662::type => 'q_58678::type)
                => 'q_58682::type => 'q_58678::type.
             GEQ (f (a, b))
              (ALL (c::'q_58662::type => 'q_58678::type) (x::'q_58682::type)
                  y::'q_58682::type. a x = a y --> b c x = b c y)))
    x &
   PAIRWISE
    (GABS
      (%f::('q_58682::type => 'q_58662::type) *
           (('q_58662::type => 'q_58678::type)
            => 'q_58682::type => 'q_58678::type)
           => ('q_58682::type => 'q_58662::type) *
              (('q_58662::type => 'q_58678::type)
               => 'q_58682::type => 'q_58678::type)
              => bool.
          ALL (s::'q_58682::type => 'q_58662::type)
             t::('q_58662::type => 'q_58678::type)
                => 'q_58682::type => 'q_58678::type.
             GEQ (f (s, t))
              (GABS
                (%f::('q_58682::type => 'q_58662::type) *
                     (('q_58662::type => 'q_58678::type)
                      => 'q_58682::type => 'q_58678::type)
                     => bool.
                    ALL (s'::'q_58682::type => 'q_58662::type)
                       t'::('q_58662::type => 'q_58678::type)
                           => 'q_58682::type => 'q_58678::type.
                       GEQ (f (s', t'))
                        (ALL (c::'q_58662::type => 'q_58678::type)
                            (x::'q_58682::type) y::'q_58682::type.
                            s x = s' y --> t c x = t' c y)))))
    x -->
   (EX f::'q_58662::type => 'q_58678::type.
       ALL_list
        (GABS
          (%fa::('q_58682::type => 'q_58662::type) *
                (('q_58662::type => 'q_58678::type)
                 => 'q_58682::type => 'q_58678::type)
                => bool.
              ALL (s::'q_58682::type => 'q_58662::type)
                 t::('q_58662::type => 'q_58678::type)
                    => 'q_58682::type => 'q_58678::type.
                 GEQ (fa (s, t)) (ALL x::'q_58682::type. f (s x) = t f x)))
        x)"
  by (import hollight RECURSION_CASEWISE_PAIRWISE)

lemma SUPERADMISSIBLE_T: "superadmissible (u_354::'q_58792::type => 'q_58792::type => bool)
 (%(f::'q_58792::type => 'q_58794::type) x::'q_58798::type. True)
 (s::'q_58798::type => 'q_58792::type)
 (t::('q_58792::type => 'q_58794::type)
     => 'q_58798::type => 'q_58794::type) =
tailadmissible u_354
 (%(f::'q_58792::type => 'q_58794::type) x::'q_58798::type. True) s t"
  by (import hollight SUPERADMISSIBLE_T)

lemma SUB_SUB: "ALL (x::nat) xa::nat. <= xa x --> (ALL a::nat. a - (x - xa) = a + xa - x)"
  by (import hollight SUB_SUB)

lemma SUB_OLD: "(ALL m::nat. 0 - m = 0) &
(ALL (m::nat) n::nat. Suc m - n = COND (< m n) 0 (Suc (m - n)))"
  by (import hollight SUB_OLD)

lemma real_le: "ALL (x::hollight.real) xa::hollight.real. real_le x xa = (~ real_lt xa x)"
  by (import hollight real_le)

lemma REAL_MUL_RID: "ALL x::hollight.real. real_mul x (real_of_num (NUMERAL_BIT1 0)) = x"
  by (import hollight REAL_MUL_RID)

lemma REAL_MUL_RINV: "ALL x::hollight.real.
   x ~= real_of_num 0 -->
   real_mul x (real_inv x) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight REAL_MUL_RINV)

lemma REAL_RDISTRIB: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_mul (real_add x y) z = real_add (real_mul x z) (real_mul y z)"
  by (import hollight REAL_RDISTRIB)

lemma REAL_EQ_LADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (real_add x y = real_add x z) = (y = z)"
  by (import hollight REAL_EQ_LADD)

lemma REAL_EQ_RADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (real_add x z = real_add y z) = (x = y)"
  by (import hollight REAL_EQ_RADD)

lemma REAL_ADD_LID_UNIQ: "ALL (x::hollight.real) y::hollight.real.
   (real_add x y = y) = (x = real_of_num 0)"
  by (import hollight REAL_ADD_LID_UNIQ)

lemma REAL_ADD_RID_UNIQ: "ALL (x::hollight.real) y::hollight.real.
   (real_add x y = x) = (y = real_of_num 0)"
  by (import hollight REAL_ADD_RID_UNIQ)

lemma REAL_LNEG_UNIQ: "ALL (x::hollight.real) y::hollight.real.
   (real_add x y = real_of_num 0) = (x = real_neg y)"
  by (import hollight REAL_LNEG_UNIQ)

lemma REAL_RNEG_UNIQ: "ALL (x::hollight.real) y::hollight.real.
   (real_add x y = real_of_num 0) = (y = real_neg x)"
  by (import hollight REAL_RNEG_UNIQ)

lemma REAL_NEG_ADD: "ALL (x::hollight.real) y::hollight.real.
   real_neg (real_add x y) = real_add (real_neg x) (real_neg y)"
  by (import hollight REAL_NEG_ADD)

lemma REAL_MUL_LZERO: "ALL x::hollight.real. real_mul (real_of_num 0) x = real_of_num 0"
  by (import hollight REAL_MUL_LZERO)

lemma REAL_MUL_RZERO: "ALL x::hollight.real. real_mul x (real_of_num 0) = real_of_num 0"
  by (import hollight REAL_MUL_RZERO)

lemma REAL_NEG_LMUL: "ALL (x::hollight.real) y::hollight.real.
   real_neg (real_mul x y) = real_mul (real_neg x) y"
  by (import hollight REAL_NEG_LMUL)

lemma REAL_NEG_RMUL: "ALL (x::hollight.real) y::hollight.real.
   real_neg (real_mul x y) = real_mul x (real_neg y)"
  by (import hollight REAL_NEG_RMUL)

lemma REAL_NEGNEG: "ALL x::hollight.real. real_neg (real_neg x) = x"
  by (import hollight REAL_NEGNEG)

lemma REAL_NEG_MUL2: "ALL (x::hollight.real) xa::hollight.real.
   real_mul (real_neg x) (real_neg xa) = real_mul x xa"
  by (import hollight REAL_NEG_MUL2)

lemma REAL_LT_LADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_add x y) (real_add x z) = real_lt y z"
  by (import hollight REAL_LT_LADD)

lemma REAL_LT_RADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_add x z) (real_add y z) = real_lt x y"
  by (import hollight REAL_LT_RADD)

lemma REAL_NOT_LT: "ALL (x::hollight.real) y::hollight.real. (~ real_lt x y) = real_le y x"
  by (import hollight REAL_NOT_LT)

lemma REAL_LT_ANTISYM: "ALL (x::hollight.real) y::hollight.real. ~ (real_lt x y & real_lt y x)"
  by (import hollight REAL_LT_ANTISYM)

lemma REAL_LT_GT: "ALL (x::hollight.real) y::hollight.real. real_lt x y --> ~ real_lt y x"
  by (import hollight REAL_LT_GT)

lemma REAL_LE_TOTAL: "ALL (x::hollight.real) y::hollight.real. real_le x y | real_le y x"
  by (import hollight REAL_LE_TOTAL)

lemma REAL_LE_REFL: "ALL x::hollight.real. real_le x x"
  by (import hollight REAL_LE_REFL)

lemma REAL_LE_LT: "ALL (x::hollight.real) y::hollight.real. real_le x y = (real_lt x y | x = y)"
  by (import hollight REAL_LE_LT)

lemma REAL_LT_LE: "ALL (x::hollight.real) y::hollight.real.
   real_lt x y = (real_le x y & x ~= y)"
  by (import hollight REAL_LT_LE)

lemma REAL_LT_IMP_LE: "ALL (x::hollight.real) y::hollight.real. real_lt x y --> real_le x y"
  by (import hollight REAL_LT_IMP_LE)

lemma REAL_LTE_TRANS: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt x y & real_le y z --> real_lt x z"
  by (import hollight REAL_LTE_TRANS)

lemma REAL_LE_TRANS: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le x y & real_le y z --> real_le x z"
  by (import hollight REAL_LE_TRANS)

lemma REAL_NEG_LT0: "ALL x::hollight.real.
   real_lt (real_neg x) (real_of_num 0) = real_lt (real_of_num 0) x"
  by (import hollight REAL_NEG_LT0)

lemma REAL_NEG_GT0: "ALL x::hollight.real.
   real_lt (real_of_num 0) (real_neg x) = real_lt x (real_of_num 0)"
  by (import hollight REAL_NEG_GT0)

lemma REAL_NEG_LE0: "ALL x::hollight.real.
   real_le (real_neg x) (real_of_num 0) = real_le (real_of_num 0) x"
  by (import hollight REAL_NEG_LE0)

lemma REAL_NEG_GE0: "ALL x::hollight.real.
   real_le (real_of_num 0) (real_neg x) = real_le x (real_of_num 0)"
  by (import hollight REAL_NEG_GE0)

lemma REAL_LT_NEGTOTAL: "ALL x::hollight.real.
   x = real_of_num 0 |
   real_lt (real_of_num 0) x | real_lt (real_of_num 0) (real_neg x)"
  by (import hollight REAL_LT_NEGTOTAL)

lemma REAL_LE_NEGTOTAL: "ALL x::hollight.real.
   real_le (real_of_num 0) x | real_le (real_of_num 0) (real_neg x)"
  by (import hollight REAL_LE_NEGTOTAL)

lemma REAL_LE_MUL: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) y -->
   real_le (real_of_num 0) (real_mul x y)"
  by (import hollight REAL_LE_MUL)

lemma REAL_LE_SQUARE: "ALL x::hollight.real. real_le (real_of_num 0) (real_mul x x)"
  by (import hollight REAL_LE_SQUARE)

lemma REAL_LT_01: "real_lt (real_of_num 0) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight REAL_LT_01)

lemma REAL_LE_LADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le (real_add x y) (real_add x z) = real_le y z"
  by (import hollight REAL_LE_LADD)

lemma REAL_LE_RADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le (real_add x z) (real_add y z) = real_le x y"
  by (import hollight REAL_LE_RADD)

lemma REAL_LT_ADD2: "ALL (w::hollight.real) (x::hollight.real) (y::hollight.real)
   z::hollight.real.
   real_lt w x & real_lt y z --> real_lt (real_add w y) (real_add x z)"
  by (import hollight REAL_LT_ADD2)

lemma REAL_LT_ADD: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_lt (real_of_num 0) y -->
   real_lt (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LT_ADD)

lemma REAL_LT_ADDNEG: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt y (real_add x (real_neg z)) = real_lt (real_add y z) x"
  by (import hollight REAL_LT_ADDNEG)

lemma REAL_LT_ADDNEG2: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_add x (real_neg y)) z = real_lt x (real_add z y)"
  by (import hollight REAL_LT_ADDNEG2)

lemma REAL_LT_ADD1: "ALL (x::hollight.real) y::hollight.real.
   real_le x y --> real_lt x (real_add y (real_of_num (NUMERAL_BIT1 0)))"
  by (import hollight REAL_LT_ADD1)

lemma REAL_SUB_ADD: "ALL (x::hollight.real) y::hollight.real. real_add (real_sub x y) y = x"
  by (import hollight REAL_SUB_ADD)

lemma REAL_SUB_ADD2: "ALL (x::hollight.real) y::hollight.real. real_add y (real_sub x y) = x"
  by (import hollight REAL_SUB_ADD2)

lemma REAL_SUB_REFL: "ALL x::hollight.real. real_sub x x = real_of_num 0"
  by (import hollight REAL_SUB_REFL)

lemma REAL_SUB_0: "ALL (x::hollight.real) y::hollight.real.
   (real_sub x y = real_of_num 0) = (x = y)"
  by (import hollight REAL_SUB_0)

lemma REAL_LE_DOUBLE: "ALL x::hollight.real.
   real_le (real_of_num 0) (real_add x x) = real_le (real_of_num 0) x"
  by (import hollight REAL_LE_DOUBLE)

lemma REAL_LE_NEGL: "ALL x::hollight.real. real_le (real_neg x) x = real_le (real_of_num 0) x"
  by (import hollight REAL_LE_NEGL)

lemma REAL_LE_NEGR: "ALL x::hollight.real. real_le x (real_neg x) = real_le x (real_of_num 0)"
  by (import hollight REAL_LE_NEGR)

lemma REAL_NEG_EQ0: "ALL x::hollight.real. (real_neg x = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight REAL_NEG_EQ0)

lemma REAL_NEG_0: "real_neg (real_of_num 0) = real_of_num 0"
  by (import hollight REAL_NEG_0)

lemma REAL_NEG_SUB: "ALL (x::hollight.real) y::hollight.real.
   real_neg (real_sub x y) = real_sub y x"
  by (import hollight REAL_NEG_SUB)

lemma REAL_SUB_LT: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) (real_sub x y) = real_lt y x"
  by (import hollight REAL_SUB_LT)

lemma REAL_SUB_LE: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) (real_sub x y) = real_le y x"
  by (import hollight REAL_SUB_LE)

lemma REAL_EQ_LMUL: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (real_mul x y = real_mul x z) = (x = real_of_num 0 | y = z)"
  by (import hollight REAL_EQ_LMUL)

lemma REAL_EQ_RMUL: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (real_mul x z = real_mul y z) = (z = real_of_num 0 | x = y)"
  by (import hollight REAL_EQ_RMUL)

lemma REAL_SUB_LDISTRIB: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_mul x (real_sub y z) = real_sub (real_mul x y) (real_mul x z)"
  by (import hollight REAL_SUB_LDISTRIB)

lemma REAL_SUB_RDISTRIB: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_mul (real_sub x y) z = real_sub (real_mul x z) (real_mul y z)"
  by (import hollight REAL_SUB_RDISTRIB)

lemma REAL_NEG_EQ: "ALL (x::hollight.real) y::hollight.real. (real_neg x = y) = (x = real_neg y)"
  by (import hollight REAL_NEG_EQ)

lemma REAL_NEG_MINUS1: "ALL x::hollight.real.
   real_neg x = real_mul (real_neg (real_of_num (NUMERAL_BIT1 0))) x"
  by (import hollight REAL_NEG_MINUS1)

lemma REAL_INV_NZ: "ALL x::hollight.real. x ~= real_of_num 0 --> real_inv x ~= real_of_num 0"
  by (import hollight REAL_INV_NZ)

lemma REAL_INVINV: "ALL x::hollight.real. x ~= real_of_num 0 --> real_inv (real_inv x) = x"
  by (import hollight REAL_INVINV)

lemma REAL_LT_IMP_NE: "ALL (x::hollight.real) y::hollight.real. real_lt x y --> x ~= y"
  by (import hollight REAL_LT_IMP_NE)

lemma REAL_INV_POS: "ALL x::hollight.real.
   real_lt (real_of_num 0) x --> real_lt (real_of_num 0) (real_inv x)"
  by (import hollight REAL_INV_POS)

lemma REAL_LT_LMUL_0: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x -->
   real_lt (real_of_num 0) (real_mul x y) = real_lt (real_of_num 0) y"
  by (import hollight REAL_LT_LMUL_0)

lemma REAL_LT_RMUL_0: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) y -->
   real_lt (real_of_num 0) (real_mul x y) = real_lt (real_of_num 0) x"
  by (import hollight REAL_LT_RMUL_0)

lemma REAL_LT_LMUL_EQ: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) x -->
   real_lt (real_mul x y) (real_mul x z) = real_lt y z"
  by (import hollight REAL_LT_LMUL_EQ)

lemma REAL_LT_RMUL_EQ: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) z -->
   real_lt (real_mul x z) (real_mul y z) = real_lt x y"
  by (import hollight REAL_LT_RMUL_EQ)

lemma REAL_LT_RMUL_IMP: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt x y & real_lt (real_of_num 0) z -->
   real_lt (real_mul x z) (real_mul y z)"
  by (import hollight REAL_LT_RMUL_IMP)

lemma REAL_LT_LMUL_IMP: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt y z & real_lt (real_of_num 0) x -->
   real_lt (real_mul x y) (real_mul x z)"
  by (import hollight REAL_LT_LMUL_IMP)

lemma REAL_LINV_UNIQ: "ALL (x::hollight.real) y::hollight.real.
   real_mul x y = real_of_num (NUMERAL_BIT1 0) --> x = real_inv y"
  by (import hollight REAL_LINV_UNIQ)

lemma REAL_RINV_UNIQ: "ALL (x::hollight.real) y::hollight.real.
   real_mul x y = real_of_num (NUMERAL_BIT1 0) --> y = real_inv x"
  by (import hollight REAL_RINV_UNIQ)

lemma REAL_NEG_INV: "ALL x::hollight.real.
   x ~= real_of_num 0 --> real_neg (real_inv x) = real_inv (real_neg x)"
  by (import hollight REAL_NEG_INV)

lemma REAL_INV_1OVER: "ALL x::hollight.real. real_inv x = real_div (real_of_num (NUMERAL_BIT1 0)) x"
  by (import hollight REAL_INV_1OVER)

lemma REAL: "ALL x::nat.
   real_of_num (Suc x) =
   real_add (real_of_num x) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight REAL)

lemma REAL_POS: "ALL n::nat. real_le (real_of_num 0) (real_of_num n)"
  by (import hollight REAL_POS)

lemma REAL_LE: "ALL (m::nat) n::nat. real_le (real_of_num m) (real_of_num n) = <= m n"
  by (import hollight REAL_LE)

lemma REAL_LT: "ALL (m::nat) n::nat. real_lt (real_of_num m) (real_of_num n) = < m n"
  by (import hollight REAL_LT)

lemma th: "((m::nat) = (n::nat)) = (<= m n & <= n m)"
  by (import hollight th)

lemma REAL_INJ: "ALL (m::nat) n::nat. (real_of_num m = real_of_num n) = (m = n)"
  by (import hollight REAL_INJ)

lemma REAL_ADD: "ALL (m::nat) n::nat.
   real_add (real_of_num m) (real_of_num n) = real_of_num (m + n)"
  by (import hollight REAL_ADD)

lemma REAL_MUL: "ALL (m::nat) n::nat.
   real_mul (real_of_num m) (real_of_num n) = real_of_num (m * n)"
  by (import hollight REAL_MUL)

lemma REAL_INV1: "real_inv (real_of_num (NUMERAL_BIT1 0)) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight REAL_INV1)

lemma REAL_DIV_LZERO: "ALL x::hollight.real. real_div (real_of_num 0) x = real_of_num 0"
  by (import hollight REAL_DIV_LZERO)

lemma REAL_LT_NZ: "ALL n::nat.
   (real_of_num n ~= real_of_num 0) =
   real_lt (real_of_num 0) (real_of_num n)"
  by (import hollight REAL_LT_NZ)

lemma REAL_NZ_IMP_LT: "ALL n::nat. n ~= 0 --> real_lt (real_of_num 0) (real_of_num n)"
  by (import hollight REAL_NZ_IMP_LT)

lemma REAL_LT_RDIV_0: "ALL (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) z -->
   real_lt (real_of_num 0) (real_div y z) = real_lt (real_of_num 0) y"
  by (import hollight REAL_LT_RDIV_0)

lemma REAL_LT_RDIV: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) z -->
   real_lt (real_div x z) (real_div y z) = real_lt x y"
  by (import hollight REAL_LT_RDIV)

lemma REAL_LT_FRACTION_0: "ALL (n::nat) d::hollight.real.
   n ~= 0 -->
   real_lt (real_of_num 0) (real_div d (real_of_num n)) =
   real_lt (real_of_num 0) d"
  by (import hollight REAL_LT_FRACTION_0)

lemma REAL_LT_MULTIPLE: "ALL (x::nat) xa::hollight.real.
   < (NUMERAL_BIT1 0) x -->
   real_lt xa (real_mul (real_of_num x) xa) = real_lt (real_of_num 0) xa"
  by (import hollight REAL_LT_MULTIPLE)

lemma REAL_LT_FRACTION: "ALL (n::nat) d::hollight.real.
   < (NUMERAL_BIT1 0) n -->
   real_lt (real_div d (real_of_num n)) d = real_lt (real_of_num 0) d"
  by (import hollight REAL_LT_FRACTION)

lemma REAL_LT_HALF1: "ALL d::hollight.real.
   real_lt (real_of_num 0)
    (real_div d (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) =
   real_lt (real_of_num 0) d"
  by (import hollight REAL_LT_HALF1)

lemma REAL_LT_HALF2: "ALL d::hollight.real.
   real_lt (real_div d (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) d =
   real_lt (real_of_num 0) d"
  by (import hollight REAL_LT_HALF2)

lemma REAL_DOUBLE: "ALL x::hollight.real.
   real_add x x = real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) x"
  by (import hollight REAL_DOUBLE)

lemma REAL_HALF_DOUBLE: "ALL x::hollight.real.
   real_add (real_div x (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
    (real_div x (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) =
   x"
  by (import hollight REAL_HALF_DOUBLE)

lemma REAL_SUB_SUB: "ALL (x::hollight.real) y::hollight.real.
   real_sub (real_sub x y) x = real_neg y"
  by (import hollight REAL_SUB_SUB)

lemma REAL_LT_ADD_SUB: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_add x y) z = real_lt x (real_sub z y)"
  by (import hollight REAL_LT_ADD_SUB)

lemma REAL_LT_SUB_RADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_sub x y) z = real_lt x (real_add z y)"
  by (import hollight REAL_LT_SUB_RADD)

lemma REAL_LT_SUB_LADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt x (real_sub y z) = real_lt (real_add x z) y"
  by (import hollight REAL_LT_SUB_LADD)

lemma REAL_LE_SUB_LADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le x (real_sub y z) = real_le (real_add x z) y"
  by (import hollight REAL_LE_SUB_LADD)

lemma REAL_LE_SUB_RADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le (real_sub x y) z = real_le x (real_add z y)"
  by (import hollight REAL_LE_SUB_RADD)

lemma REAL_LT_NEG: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_neg x) (real_neg y) = real_lt y x"
  by (import hollight REAL_LT_NEG)

lemma REAL_LE_NEG: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_neg x) (real_neg y) = real_le y x"
  by (import hollight REAL_LE_NEG)

lemma REAL_SUB_LZERO: "ALL x::hollight.real. real_sub (real_of_num 0) x = real_neg x"
  by (import hollight REAL_SUB_LZERO)

lemma REAL_SUB_RZERO: "ALL x::hollight.real. real_sub x (real_of_num 0) = x"
  by (import hollight REAL_SUB_RZERO)

lemma REAL_LTE_ADD2: "ALL (w::hollight.real) (x::hollight.real) (y::hollight.real)
   z::hollight.real.
   real_lt w x & real_le y z --> real_lt (real_add w y) (real_add x z)"
  by (import hollight REAL_LTE_ADD2)

lemma REAL_LTE_ADD: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_le (real_of_num 0) y -->
   real_lt (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LTE_ADD)

lemma REAL_LT_MUL2_ALT: "ALL (x1::hollight.real) (x2::hollight.real) (y1::hollight.real)
   y2::hollight.real.
   real_le (real_of_num 0) x1 &
   real_le (real_of_num 0) y1 & real_lt x1 x2 & real_lt y1 y2 -->
   real_lt (real_mul x1 y1) (real_mul x2 y2)"
  by (import hollight REAL_LT_MUL2_ALT)

lemma REAL_SUB_LNEG: "ALL (x::hollight.real) y::hollight.real.
   real_sub (real_neg x) y = real_neg (real_add x y)"
  by (import hollight REAL_SUB_LNEG)

lemma REAL_SUB_RNEG: "ALL (x::hollight.real) y::hollight.real.
   real_sub x (real_neg y) = real_add x y"
  by (import hollight REAL_SUB_RNEG)

lemma REAL_SUB_NEG2: "ALL (x::hollight.real) y::hollight.real.
   real_sub (real_neg x) (real_neg y) = real_sub y x"
  by (import hollight REAL_SUB_NEG2)

lemma REAL_SUB_TRIANGLE: "ALL (a::hollight.real) (b::hollight.real) c::hollight.real.
   real_add (real_sub a b) (real_sub b c) = real_sub a c"
  by (import hollight REAL_SUB_TRIANGLE)

lemma REAL_INV_MUL_WEAK: "ALL (x::hollight.real) xa::hollight.real.
   x ~= real_of_num 0 & xa ~= real_of_num 0 -->
   real_inv (real_mul x xa) = real_mul (real_inv x) (real_inv xa)"
  by (import hollight REAL_INV_MUL_WEAK)

lemma REAL_LE_LMUL_LOCAL: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) x -->
   real_le (real_mul x y) (real_mul x z) = real_le y z"
  by (import hollight REAL_LE_LMUL_LOCAL)

lemma REAL_LE_RMUL_EQ: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) z -->
   real_le (real_mul x z) (real_mul y z) = real_le x y"
  by (import hollight REAL_LE_RMUL_EQ)

lemma REAL_SUB_INV2: "ALL (x::hollight.real) y::hollight.real.
   x ~= real_of_num 0 & y ~= real_of_num 0 -->
   real_sub (real_inv x) (real_inv y) =
   real_div (real_sub y x) (real_mul x y)"
  by (import hollight REAL_SUB_INV2)

lemma REAL_SUB_SUB2: "ALL (x::hollight.real) y::hollight.real. real_sub x (real_sub x y) = y"
  by (import hollight REAL_SUB_SUB2)

lemma REAL_MEAN: "ALL (x::hollight.real) y::hollight.real.
   real_lt x y --> (EX z::hollight.real. real_lt x z & real_lt z y)"
  by (import hollight REAL_MEAN)

lemma REAL_EQ_LMUL2: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   x ~= real_of_num 0 --> (y = z) = (real_mul x y = real_mul x z)"
  by (import hollight REAL_EQ_LMUL2)

lemma REAL_LE_MUL2V: "ALL (x1::hollight.real) (x2::hollight.real) (y1::hollight.real)
   y2::hollight.real.
   real_le (real_of_num 0) x1 &
   real_le (real_of_num 0) y1 & real_le x1 x2 & real_le y1 y2 -->
   real_le (real_mul x1 y1) (real_mul x2 y2)"
  by (import hollight REAL_LE_MUL2V)

lemma REAL_LE_LDIV: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) x & real_le y (real_mul z x) -->
   real_le (real_div y x) z"
  by (import hollight REAL_LE_LDIV)

lemma REAL_LE_RDIV: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) x & real_le (real_mul y x) z -->
   real_le y (real_div z x)"
  by (import hollight REAL_LE_RDIV)

lemma REAL_LT_1: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_lt x y -->
   real_lt (real_div x y) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight REAL_LT_1)

lemma REAL_LE_LMUL_IMP: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_le (real_of_num 0) x & real_le y z -->
   real_le (real_mul x y) (real_mul x z)"
  by (import hollight REAL_LE_LMUL_IMP)

lemma REAL_LE_RMUL_IMP: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_le (real_of_num 0) x & real_le xa xb -->
   real_le (real_mul xa x) (real_mul xb x)"
  by (import hollight REAL_LE_RMUL_IMP)

lemma REAL_INV_LT1: "ALL x::hollight.real.
   real_lt (real_of_num 0) x & real_lt x (real_of_num (NUMERAL_BIT1 0)) -->
   real_lt (real_of_num (NUMERAL_BIT1 0)) (real_inv x)"
  by (import hollight REAL_INV_LT1)

lemma REAL_POS_NZ: "ALL x::hollight.real. real_lt (real_of_num 0) x --> x ~= real_of_num 0"
  by (import hollight REAL_POS_NZ)

lemma REAL_EQ_RMUL_IMP: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   z ~= real_of_num 0 & real_mul x z = real_mul y z --> x = y"
  by (import hollight REAL_EQ_RMUL_IMP)

lemma REAL_EQ_LMUL_IMP: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   x ~= real_of_num 0 & real_mul x xa = real_mul x xb --> xa = xb"
  by (import hollight REAL_EQ_LMUL_IMP)

lemma REAL_FACT_NZ: "ALL n::nat. real_of_num (FACT n) ~= real_of_num 0"
  by (import hollight REAL_FACT_NZ)

lemma REAL_POSSQ: "ALL x::hollight.real.
   real_lt (real_of_num 0) (real_mul x x) = (x ~= real_of_num 0)"
  by (import hollight REAL_POSSQ)

lemma REAL_SUMSQ: "ALL (x::hollight.real) y::hollight.real.
   (real_add (real_mul x x) (real_mul y y) = real_of_num 0) =
   (x = real_of_num 0 & y = real_of_num 0)"
  by (import hollight REAL_SUMSQ)

lemma REAL_EQ_NEG: "ALL (x::hollight.real) y::hollight.real. (real_neg x = real_neg y) = (x = y)"
  by (import hollight REAL_EQ_NEG)

lemma REAL_DIV_MUL2: "ALL (x::hollight.real) z::hollight.real.
   x ~= real_of_num 0 & z ~= real_of_num 0 -->
   (ALL y::hollight.real.
       real_div y z = real_div (real_mul x y) (real_mul x z))"
  by (import hollight REAL_DIV_MUL2)

lemma REAL_MIDDLE1: "ALL (a::hollight.real) b::hollight.real.
   real_le a b -->
   real_le a
    (real_div (real_add a b) (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))"
  by (import hollight REAL_MIDDLE1)

lemma REAL_MIDDLE2: "ALL (a::hollight.real) b::hollight.real.
   real_le a b -->
   real_le
    (real_div (real_add a b) (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
    b"
  by (import hollight REAL_MIDDLE2)

lemma ABS_ZERO: "ALL x::hollight.real. (real_abs x = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight ABS_ZERO)

lemma ABS_0: "real_abs (real_of_num 0) = real_of_num 0"
  by (import hollight ABS_0)

lemma ABS_1: "real_abs (real_of_num (NUMERAL_BIT1 0)) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight ABS_1)

lemma ABS_NEG: "ALL x::hollight.real. real_abs (real_neg x) = real_abs x"
  by (import hollight ABS_NEG)

lemma ABS_TRIANGLE: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_abs (real_add x y)) (real_add (real_abs x) (real_abs y))"
  by (import hollight ABS_TRIANGLE)

lemma ABS_POS: "ALL x::hollight.real. real_le (real_of_num 0) (real_abs x)"
  by (import hollight ABS_POS)

lemma ABS_MUL: "ALL (x::hollight.real) y::hollight.real.
   real_abs (real_mul x y) = real_mul (real_abs x) (real_abs y)"
  by (import hollight ABS_MUL)

lemma ABS_LT_MUL2: "ALL (w::hollight.real) (x::hollight.real) (y::hollight.real)
   z::hollight.real.
   real_lt (real_abs w) y & real_lt (real_abs x) z -->
   real_lt (real_abs (real_mul w x)) (real_mul y z)"
  by (import hollight ABS_LT_MUL2)

lemma ABS_SUB: "ALL (x::hollight.real) y::hollight.real.
   real_abs (real_sub x y) = real_abs (real_sub y x)"
  by (import hollight ABS_SUB)

lemma ABS_NZ: "ALL x::hollight.real.
   (x ~= real_of_num 0) = real_lt (real_of_num 0) (real_abs x)"
  by (import hollight ABS_NZ)

lemma ABS_INV: "ALL x::hollight.real.
   x ~= real_of_num 0 --> real_abs (real_inv x) = real_inv (real_abs x)"
  by (import hollight ABS_INV)

lemma ABS_ABS: "ALL x::hollight.real. real_abs (real_abs x) = real_abs x"
  by (import hollight ABS_ABS)

lemma ABS_LE: "ALL x::hollight.real. real_le x (real_abs x)"
  by (import hollight ABS_LE)

lemma ABS_REFL: "ALL x::hollight.real. (real_abs x = x) = real_le (real_of_num 0) x"
  by (import hollight ABS_REFL)

lemma ABS_N: "ALL n::nat. real_abs (real_of_num n) = real_of_num n"
  by (import hollight ABS_N)

lemma ABS_BETWEEN: "ALL (x::hollight.real) (y::hollight.real) d::hollight.real.
   (real_lt (real_of_num 0) d &
    real_lt (real_sub x d) y & real_lt y (real_add x d)) =
   real_lt (real_abs (real_sub y x)) d"
  by (import hollight ABS_BETWEEN)

lemma ABS_BOUND: "ALL (x::hollight.real) (y::hollight.real) d::hollight.real.
   real_lt (real_abs (real_sub x y)) d --> real_lt y (real_add x d)"
  by (import hollight ABS_BOUND)

lemma ABS_STILLNZ: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_abs (real_sub x y)) (real_abs y) --> x ~= real_of_num 0"
  by (import hollight ABS_STILLNZ)

lemma ABS_CASES: "ALL x::hollight.real.
   x = real_of_num 0 | real_lt (real_of_num 0) (real_abs x)"
  by (import hollight ABS_CASES)

lemma ABS_BETWEEN1: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt x z & real_lt (real_abs (real_sub y x)) (real_sub z x) -->
   real_lt y z"
  by (import hollight ABS_BETWEEN1)

lemma ABS_SIGN: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_abs (real_sub x y)) y --> real_lt (real_of_num 0) x"
  by (import hollight ABS_SIGN)

lemma ABS_SIGN2: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_abs (real_sub x y)) (real_neg y) -->
   real_lt x (real_of_num 0)"
  by (import hollight ABS_SIGN2)

lemma ABS_DIV: "ALL y::hollight.real.
   y ~= real_of_num 0 -->
   (ALL x::hollight.real.
       real_abs (real_div x y) = real_div (real_abs x) (real_abs y))"
  by (import hollight ABS_DIV)

lemma ABS_CIRCLE: "ALL (x::hollight.real) (y::hollight.real) h::hollight.real.
   real_lt (real_abs h) (real_sub (real_abs y) (real_abs x)) -->
   real_lt (real_abs (real_add x h)) (real_abs y)"
  by (import hollight ABS_CIRCLE)

lemma REAL_SUB_ABS: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_sub (real_abs x) (real_abs y)) (real_abs (real_sub x y))"
  by (import hollight REAL_SUB_ABS)

lemma ABS_SUB_ABS: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_abs (real_sub (real_abs x) (real_abs y)))
    (real_abs (real_sub x y))"
  by (import hollight ABS_SUB_ABS)

lemma ABS_BETWEEN2: "ALL (x0::hollight.real) (x::hollight.real) (y0::hollight.real)
   y::hollight.real.
   real_lt x0 y0 &
   real_lt (real_abs (real_sub x x0))
    (real_div (real_sub y0 x0)
      (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
   real_lt (real_abs (real_sub y y0))
    (real_div (real_sub y0 x0)
      (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) -->
   real_lt x y"
  by (import hollight ABS_BETWEEN2)

lemma ABS_BOUNDS: "ALL (x::hollight.real) k::hollight.real.
   real_le (real_abs x) k = (real_le (real_neg k) x & real_le x k)"
  by (import hollight ABS_BOUNDS)

lemma POW_0: "ALL n::nat. real_pow (real_of_num 0) (Suc n) = real_of_num 0"
  by (import hollight POW_0)

lemma POW_NZ: "ALL (c::hollight.real) n::nat.
   c ~= real_of_num 0 --> real_pow c n ~= real_of_num 0"
  by (import hollight POW_NZ)

lemma POW_INV: "ALL (c::hollight.real) x::nat.
   c ~= real_of_num 0 --> real_inv (real_pow c x) = real_pow (real_inv c) x"
  by (import hollight POW_INV)

lemma POW_ABS: "ALL (c::hollight.real) n::nat.
   real_pow (real_abs c) n = real_abs (real_pow c n)"
  by (import hollight POW_ABS)

lemma POW_PLUS1: "ALL (e::hollight.real) x::nat.
   real_lt (real_of_num 0) e -->
   real_le
    (real_add (real_of_num (NUMERAL_BIT1 0)) (real_mul (real_of_num x) e))
    (real_pow (real_add (real_of_num (NUMERAL_BIT1 0)) e) x)"
  by (import hollight POW_PLUS1)

lemma POW_ADD: "ALL (c::hollight.real) (m::nat) n::nat.
   real_pow c (m + n) = real_mul (real_pow c m) (real_pow c n)"
  by (import hollight POW_ADD)

lemma POW_1: "ALL x::hollight.real. real_pow x (NUMERAL_BIT1 0) = x"
  by (import hollight POW_1)

lemma POW_2: "ALL x::hollight.real.
   real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)) = real_mul x x"
  by (import hollight POW_2)

lemma POW_POS: "ALL (x::hollight.real) xa::nat.
   real_le (real_of_num 0) x --> real_le (real_of_num 0) (real_pow x xa)"
  by (import hollight POW_POS)

lemma POW_LE: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_le x y -->
   real_le (real_pow x n) (real_pow y n)"
  by (import hollight POW_LE)

lemma POW_M1: "ALL n::nat.
   real_abs (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0))) n) =
   real_of_num (NUMERAL_BIT1 0)"
  by (import hollight POW_M1)

lemma POW_MUL: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   real_pow (real_mul x y) n = real_mul (real_pow x n) (real_pow y n)"
  by (import hollight POW_MUL)

lemma REAL_LE_SQUARE_POW: "ALL x::hollight.real.
   real_le (real_of_num 0) (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))"
  by (import hollight REAL_LE_SQUARE_POW)

lemma ABS_POW2: "ALL x::hollight.real.
   real_abs (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0))) =
   real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0))"
  by (import hollight ABS_POW2)

lemma REAL_LE1_POW2: "ALL x::hollight.real.
   real_le (real_of_num (NUMERAL_BIT1 0)) x -->
   real_le (real_of_num (NUMERAL_BIT1 0))
    (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))"
  by (import hollight REAL_LE1_POW2)

lemma REAL_LT1_POW2: "ALL x::hollight.real.
   real_lt (real_of_num (NUMERAL_BIT1 0)) x -->
   real_lt (real_of_num (NUMERAL_BIT1 0))
    (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))"
  by (import hollight REAL_LT1_POW2)

lemma POW_POS_LT: "ALL (x::hollight.real) n::nat.
   real_lt (real_of_num 0) x -->
   real_lt (real_of_num 0) (real_pow x (Suc n))"
  by (import hollight POW_POS_LT)

lemma POW_2_LE1: "ALL n::nat.
   real_le (real_of_num (NUMERAL_BIT1 0))
    (real_pow (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) n)"
  by (import hollight POW_2_LE1)

lemma POW_2_LT: "ALL n::nat.
   real_lt (real_of_num n)
    (real_pow (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) n)"
  by (import hollight POW_2_LT)

lemma POW_MINUS1: "ALL n::nat.
   real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
    (NUMERAL_BIT0 (NUMERAL_BIT1 0) * n) =
   real_of_num (NUMERAL_BIT1 0)"
  by (import hollight POW_MINUS1)

lemma REAL_SUP_EXISTS: "ALL P::hollight.real => bool.
   Ex P &
   (EX z::hollight.real. ALL x::hollight.real. P x --> real_lt x z) -->
   (EX s::hollight.real.
       ALL y::hollight.real.
          (EX x::hollight.real. P x & real_lt y x) = real_lt y s)"
  by (import hollight REAL_SUP_EXISTS)

constdefs
  sup :: "(hollight.real => bool) => hollight.real" 
  "sup ==
%u::hollight.real => bool.
   SOME a::hollight.real.
      (ALL x::hollight.real. IN x u --> real_le x a) &
      (ALL b::hollight.real.
          (ALL x::hollight.real. IN x u --> real_le x b) --> real_le a b)"

lemma DEF_sup: "sup =
(%u::hollight.real => bool.
    SOME a::hollight.real.
       (ALL x::hollight.real. IN x u --> real_le x a) &
       (ALL b::hollight.real.
           (ALL x::hollight.real. IN x u --> real_le x b) --> real_le a b))"
  by (import hollight DEF_sup)

lemma sup: "sup (P::hollight.real => bool) =
(SOME s::hollight.real.
    ALL y::hollight.real.
       (EX x::hollight.real. P x & real_lt y x) = real_lt y s)"
  by (import hollight sup)

lemma REAL_SUP: "ALL P::hollight.real => bool.
   Ex P &
   (EX z::hollight.real. ALL x::hollight.real. P x --> real_lt x z) -->
   (ALL y::hollight.real.
       (EX x::hollight.real. P x & real_lt y x) = real_lt y (sup P))"
  by (import hollight REAL_SUP)

lemma REAL_SUP_UBOUND: "ALL P::hollight.real => bool.
   Ex P &
   (EX z::hollight.real. ALL x::hollight.real. P x --> real_lt x z) -->
   (ALL y::hollight.real. P y --> real_le y (sup P))"
  by (import hollight REAL_SUP_UBOUND)

lemma SETOK_LE_LT: "ALL P::hollight.real => bool.
   (Ex P &
    (EX z::hollight.real. ALL x::hollight.real. P x --> real_le x z)) =
   (Ex P &
    (EX x::hollight.real. ALL xa::hollight.real. P xa --> real_lt xa x))"
  by (import hollight SETOK_LE_LT)

lemma REAL_SUP_LE: "ALL P::hollight.real => bool.
   Ex P &
   (EX z::hollight.real. ALL x::hollight.real. P x --> real_le x z) -->
   (ALL y::hollight.real.
       (EX x::hollight.real. P x & real_lt y x) = real_lt y (sup P))"
  by (import hollight REAL_SUP_LE)

lemma REAL_SUP_UBOUND_LE: "ALL P::hollight.real => bool.
   Ex P &
   (EX z::hollight.real. ALL x::hollight.real. P x --> real_le x z) -->
   (ALL y::hollight.real. P y --> real_le y (sup P))"
  by (import hollight REAL_SUP_UBOUND_LE)

lemma REAL_ARCH_SIMPLE: "ALL x::hollight.real. EX n::nat. real_le x (real_of_num n)"
  by (import hollight REAL_ARCH_SIMPLE)

lemma REAL_ARCH: "ALL x::hollight.real.
   real_lt (real_of_num 0) x -->
   (ALL y::hollight.real. EX n::nat. real_lt y (real_mul (real_of_num n) x))"
  by (import hollight REAL_ARCH)

lemma REAL_ARCH_LEAST: "ALL y::hollight.real.
   real_lt (real_of_num 0) y -->
   (ALL x::hollight.real.
       real_le (real_of_num 0) x -->
       (EX n::nat.
           real_le (real_mul (real_of_num n) y) x &
           real_lt x (real_mul (real_of_num (Suc n)) y)))"
  by (import hollight REAL_ARCH_LEAST)

lemma sum_EXISTS: "EX x::nat * nat => (nat => hollight.real) => hollight.real.
   (ALL (f::nat => hollight.real) n::nat. x (n, 0) f = real_of_num 0) &
   (ALL (f::nat => hollight.real) (m::nat) n::nat.
       x (n, Suc m) f = real_add (x (n, m) f) (f (n + m)))"
  by (import hollight sum_EXISTS)

constdefs
  psum :: "nat * nat => (nat => hollight.real) => hollight.real" 
  "psum ==
SOME sum::nat * nat => (nat => hollight.real) => hollight.real.
   (ALL (f::nat => hollight.real) n::nat. sum (n, 0) f = real_of_num 0) &
   (ALL (f::nat => hollight.real) (m::nat) n::nat.
       sum (n, Suc m) f = real_add (sum (n, m) f) (f (n + m)))"

lemma DEF_psum: "psum =
(SOME sum::nat * nat => (nat => hollight.real) => hollight.real.
    (ALL (f::nat => hollight.real) n::nat. sum (n, 0) f = real_of_num 0) &
    (ALL (f::nat => hollight.real) (m::nat) n::nat.
        sum (n, Suc m) f = real_add (sum (n, m) f) (f (n + m))))"
  by (import hollight DEF_psum)

lemma sum: "psum (n::nat, 0) (f::nat => hollight.real) = real_of_num 0 &
psum (n, Suc (m::nat)) f = real_add (psum (n, m) f) (f (n + m))"
  by (import hollight sum)

lemma PSUM_SUM: "ALL (f::nat => hollight.real) (m::nat) n::nat.
   psum (m, n) f =
   hollight.sum
    (GSPEC (%u::nat. EX i::nat. SETSPEC u (<= m i & < i (m + n)) i)) f"
  by (import hollight PSUM_SUM)

lemma PSUM_SUM_NUMSEG: "ALL (f::nat => hollight.real) (m::nat) n::nat.
   ~ (m = 0 & n = 0) -->
   psum (m, n) f = hollight.sum (dotdot m (m + n - NUMERAL_BIT1 0)) f"
  by (import hollight PSUM_SUM_NUMSEG)

lemma SUM_TWO: "ALL (f::nat => hollight.real) (n::nat) p::nat.
   real_add (psum (0, n) f) (psum (n, p) f) = psum (0, n + p) f"
  by (import hollight SUM_TWO)

lemma SUM_DIFF: "ALL (f::nat => hollight.real) (m::nat) n::nat.
   psum (m, n) f = real_sub (psum (0, m + n) f) (psum (0, m) f)"
  by (import hollight SUM_DIFF)

lemma ABS_SUM: "ALL (f::nat => hollight.real) (m::nat) n::nat.
   real_le (real_abs (psum (m, n) f))
    (psum (m, n) (%n::nat. real_abs (f n)))"
  by (import hollight ABS_SUM)

lemma SUM_LE: "ALL (f::nat => hollight.real) (g::nat => hollight.real) (m::nat) n::nat.
   (ALL r::nat. <= m r & < r (n + m) --> real_le (f r) (g r)) -->
   real_le (psum (m, n) f) (psum (m, n) g)"
  by (import hollight SUM_LE)

lemma SUM_EQ: "ALL (f::nat => hollight.real) (g::nat => hollight.real) (m::nat) n::nat.
   (ALL r::nat. <= m r & < r (n + m) --> f r = g r) -->
   psum (m, n) f = psum (m, n) g"
  by (import hollight SUM_EQ)

lemma SUM_POS: "ALL f::nat => hollight.real.
   (ALL n::nat. real_le (real_of_num 0) (f n)) -->
   (ALL (m::nat) n::nat. real_le (real_of_num 0) (psum (m, n) f))"
  by (import hollight SUM_POS)

lemma SUM_POS_GEN: "ALL (f::nat => hollight.real) (m::nat) n::nat.
   (ALL n::nat. <= m n --> real_le (real_of_num 0) (f n)) -->
   real_le (real_of_num 0) (psum (m, n) f)"
  by (import hollight SUM_POS_GEN)

lemma SUM_ABS: "ALL (f::nat => hollight.real) (m::nat) x::nat.
   real_abs (psum (m, x) (%m::nat. real_abs (f m))) =
   psum (m, x) (%m::nat. real_abs (f m))"
  by (import hollight SUM_ABS)

lemma SUM_ABS_LE: "ALL (f::nat => hollight.real) (m::nat) n::nat.
   real_le (real_abs (psum (m, n) f))
    (psum (m, n) (%n::nat. real_abs (f n)))"
  by (import hollight SUM_ABS_LE)

lemma SUM_ZERO: "ALL (f::nat => hollight.real) N::nat.
   (ALL n::nat. >= n N --> f n = real_of_num 0) -->
   (ALL (m::nat) n::nat. >= m N --> psum (m, n) f = real_of_num 0)"
  by (import hollight SUM_ZERO)

lemma SUM_ADD: "ALL (f::nat => hollight.real) (g::nat => hollight.real) (m::nat) n::nat.
   psum (m, n) (%n::nat. real_add (f n) (g n)) =
   real_add (psum (m, n) f) (psum (m, n) g)"
  by (import hollight SUM_ADD)

lemma SUM_CMUL: "ALL (f::nat => hollight.real) (c::hollight.real) (m::nat) n::nat.
   psum (m, n) (%n::nat. real_mul c (f n)) = real_mul c (psum (m, n) f)"
  by (import hollight SUM_CMUL)

lemma SUM_NEG: "ALL (f::nat => hollight.real) (n::nat) d::nat.
   psum (n, d) (%n::nat. real_neg (f n)) = real_neg (psum (n, d) f)"
  by (import hollight SUM_NEG)

lemma SUM_SUB: "ALL (f::nat => hollight.real) (g::nat => hollight.real) (m::nat) n::nat.
   psum (m, n) (%x::nat. real_sub (f x) (g x)) =
   real_sub (psum (m, n) f) (psum (m, n) g)"
  by (import hollight SUM_SUB)

lemma SUM_SUBST: "ALL (f::nat => hollight.real) (g::nat => hollight.real) (m::nat) n::nat.
   (ALL p::nat. <= m p & < p (m + n) --> f p = g p) -->
   psum (m, n) f = psum (m, n) g"
  by (import hollight SUM_SUBST)

lemma SUM_NSUB: "ALL (n::nat) (f::nat => hollight.real) c::hollight.real.
   real_sub (psum (0, n) f) (real_mul (real_of_num n) c) =
   psum (0, n) (%p::nat. real_sub (f p) c)"
  by (import hollight SUM_NSUB)

lemma SUM_BOUND: "ALL (f::nat => hollight.real) (K::hollight.real) (m::nat) n::nat.
   (ALL p::nat. <= m p & < p (m + n) --> real_le (f p) K) -->
   real_le (psum (m, n) f) (real_mul (real_of_num n) K)"
  by (import hollight SUM_BOUND)

lemma SUM_GROUP: "ALL (n::nat) (k::nat) f::nat => hollight.real.
   psum (0, n) (%m::nat. psum (m * k, k) f) = psum (0, n * k) f"
  by (import hollight SUM_GROUP)

lemma SUM_1: "ALL (f::nat => hollight.real) n::nat. psum (n, NUMERAL_BIT1 0) f = f n"
  by (import hollight SUM_1)

lemma SUM_2: "ALL (f::nat => hollight.real) n::nat.
   psum (n, NUMERAL_BIT0 (NUMERAL_BIT1 0)) f =
   real_add (f n) (f (n + NUMERAL_BIT1 0))"
  by (import hollight SUM_2)

lemma SUM_OFFSET: "ALL (f::nat => hollight.real) (n::nat) k::nat.
   psum (0, n) (%m::nat. f (m + k)) =
   real_sub (psum (0, n + k) f) (psum (0, k) f)"
  by (import hollight SUM_OFFSET)

lemma SUM_REINDEX: "ALL (f::nat => hollight.real) (m::nat) (k::nat) n::nat.
   psum (m + k, n) f = psum (m, n) (%r::nat. f (r + k))"
  by (import hollight SUM_REINDEX)

lemma SUM_0: "ALL (m::nat) n::nat. psum (m, n) (%r::nat. real_of_num 0) = real_of_num 0"
  by (import hollight SUM_0)

lemma SUM_CANCEL: "ALL (f::nat => hollight.real) (n::nat) d::nat.
   psum (n, d) (%n::nat. real_sub (f (Suc n)) (f n)) =
   real_sub (f (n + d)) (f n)"
  by (import hollight SUM_CANCEL)

lemma SUM_HORNER: "ALL (f::nat => hollight.real) (n::nat) x::hollight.real.
   psum (0, Suc n) (%i::nat. real_mul (f i) (real_pow x i)) =
   real_add (f 0)
    (real_mul x
      (psum (0, n) (%i::nat. real_mul (f (Suc i)) (real_pow x i))))"
  by (import hollight SUM_HORNER)

lemma SUM_CONST: "ALL (c::hollight.real) n::nat.
   psum (0, n) (%m::nat. c) = real_mul (real_of_num n) c"
  by (import hollight SUM_CONST)

lemma SUM_SPLIT: "ALL (f::nat => hollight.real) (n::nat) p::nat.
   real_add (psum (m::nat, n) f) (psum (m + n, p) f) = psum (m, n + p) f"
  by (import hollight SUM_SPLIT)

lemma SUM_SWAP: "ALL (f::nat => nat => hollight.real) (m1::nat) (n1::nat) (m2::nat) n2::nat.
   psum (m1, n1) (%a::nat. psum (m2, n2) (f a)) =
   psum (m2, n2) (%b::nat. psum (m1, n1) (%a::nat. f a b))"
  by (import hollight SUM_SWAP)

lemma SUM_EQ_0: "(ALL r::nat.
    <= (m::nat) r & < r (m + (n::nat)) -->
    (f::nat => hollight.real) r = real_of_num 0) -->
psum (m, n) f = real_of_num 0"
  by (import hollight SUM_EQ_0)

lemma SUM_MORETERMS_EQ: "ALL (m::nat) (n::nat) p::nat.
   <= n p &
   (ALL r::nat.
       <= (m + n) r & < r (m + p) -->
       (f::nat => hollight.real) r = real_of_num 0) -->
   psum (m, p) f = psum (m, n) f"
  by (import hollight SUM_MORETERMS_EQ)

lemma SUM_DIFFERENCES_EQ: "ALL (x::nat) (xa::nat) xb::nat.
   <= xa xb &
   (ALL r::nat.
       <= (x + xa) r & < r (x + xb) -->
       (f::nat => hollight.real) r = (g::nat => hollight.real) r) -->
   real_sub (psum (x, xb) f) (psum (x, xa) f) =
   real_sub (psum (x, xb) g) (psum (x, xa) g)"
  by (import hollight SUM_DIFFERENCES_EQ)

constdefs
  re_Union :: "(('A => bool) => bool) => 'A => bool" 
  "re_Union ==
%(u::('A::type => bool) => bool) x::'A::type.
   EX s::'A::type => bool. u s & s x"

lemma DEF_re_Union: "re_Union =
(%(u::('A::type => bool) => bool) x::'A::type.
    EX s::'A::type => bool. u s & s x)"
  by (import hollight DEF_re_Union)

constdefs
  re_union :: "('A => bool) => ('A => bool) => 'A => bool" 
  "re_union ==
%(u::'A::type => bool) (ua::'A::type => bool) x::'A::type. u x | ua x"

lemma DEF_re_union: "re_union =
(%(u::'A::type => bool) (ua::'A::type => bool) x::'A::type. u x | ua x)"
  by (import hollight DEF_re_union)

constdefs
  re_intersect :: "('A => bool) => ('A => bool) => 'A => bool" 
  "re_intersect ==
%(u::'A::type => bool) (ua::'A::type => bool) x::'A::type. u x & ua x"

lemma DEF_re_intersect: "re_intersect =
(%(u::'A::type => bool) (ua::'A::type => bool) x::'A::type. u x & ua x)"
  by (import hollight DEF_re_intersect)

constdefs
  re_null :: "'A => bool" 
  "re_null == %x::'A::type. False"

lemma DEF_re_null: "re_null = (%x::'A::type. False)"
  by (import hollight DEF_re_null)

constdefs
  re_universe :: "'A => bool" 
  "re_universe == %x::'A::type. True"

lemma DEF_re_universe: "re_universe = (%x::'A::type. True)"
  by (import hollight DEF_re_universe)

constdefs
  re_subset :: "('A => bool) => ('A => bool) => bool" 
  "re_subset ==
%(u::'A::type => bool) ua::'A::type => bool. ALL x::'A::type. u x --> ua x"

lemma DEF_re_subset: "re_subset =
(%(u::'A::type => bool) ua::'A::type => bool. ALL x::'A::type. u x --> ua x)"
  by (import hollight DEF_re_subset)

constdefs
  re_compl :: "('A => bool) => 'A => bool" 
  "re_compl == %(u::'A::type => bool) x::'A::type. ~ u x"

lemma DEF_re_compl: "re_compl = (%(u::'A::type => bool) x::'A::type. ~ u x)"
  by (import hollight DEF_re_compl)

lemma SUBSETA_REFL: "ALL S::'A::type => bool. re_subset S S"
  by (import hollight SUBSETA_REFL)

lemma COMPL_MEM: "ALL (S::'A::type => bool) x::'A::type. S x = (~ re_compl S x)"
  by (import hollight COMPL_MEM)

lemma SUBSETA_ANTISYM: "ALL (P::'A::type => bool) Q::'A::type => bool.
   (re_subset P Q & re_subset Q P) = (P = Q)"
  by (import hollight SUBSETA_ANTISYM)

lemma SUBSETA_TRANS: "ALL (P::'A::type => bool) (Q::'A::type => bool) R::'A::type => bool.
   re_subset P Q & re_subset Q R --> re_subset P R"
  by (import hollight SUBSETA_TRANS)

constdefs
  istopology :: "(('A => bool) => bool) => bool" 
  "istopology ==
%u::('A::type => bool) => bool.
   u re_null &
   u re_universe &
   (ALL (a::'A::type => bool) b::'A::type => bool.
       u a & u b --> u (re_intersect a b)) &
   (ALL P::('A::type => bool) => bool. re_subset P u --> u (re_Union P))"

lemma DEF_istopology: "istopology =
(%u::('A::type => bool) => bool.
    u re_null &
    u re_universe &
    (ALL (a::'A::type => bool) b::'A::type => bool.
        u a & u b --> u (re_intersect a b)) &
    (ALL P::('A::type => bool) => bool. re_subset P u --> u (re_Union P)))"
  by (import hollight DEF_istopology)

typedef (open) ('A) topology = "(Collect::((('A::type => bool) => bool) => bool)
          => (('A::type => bool) => bool) set)
 (istopology::(('A::type => bool) => bool) => bool)"  morphisms "open" "topology"
  apply (rule light_ex_imp_nonempty[where t="(Eps::((('A::type => bool) => bool) => bool) => ('A::type => bool) => bool)
 (istopology::(('A::type => bool) => bool) => bool)"])
  by (import hollight TYDEF_topology)

syntax
  "open" :: _ 

syntax
  topology :: _ 

lemmas "TYDEF_topology_@intern" = typedef_hol2hollight 
  [where a="a :: 'A topology" and r=r ,
   OF type_definition_topology]

lemma TOPOLOGY: "ALL L::'A::type topology.
   open L re_null &
   open L re_universe &
   (ALL (a::'A::type => bool) b::'A::type => bool.
       open L a & open L b --> open L (re_intersect a b)) &
   (ALL P::('A::type => bool) => bool.
       re_subset P (open L) --> open L (re_Union P))"
  by (import hollight TOPOLOGY)

lemma TOPOLOGY_UNION: "ALL (x::'A::type topology) xa::('A::type => bool) => bool.
   re_subset xa (open x) --> open x (re_Union xa)"
  by (import hollight TOPOLOGY_UNION)

constdefs
  neigh :: "'A topology => ('A => bool) * 'A => bool" 
  "neigh ==
%(u::'A::type topology) ua::('A::type => bool) * 'A::type.
   EX P::'A::type => bool. open u P & re_subset P (fst ua) & P (snd ua)"

lemma DEF_neigh: "neigh =
(%(u::'A::type topology) ua::('A::type => bool) * 'A::type.
    EX P::'A::type => bool. open u P & re_subset P (fst ua) & P (snd ua))"
  by (import hollight DEF_neigh)

lemma OPEN_OWN_NEIGH: "ALL (S::'A::type => bool) (top::'A::type topology) x::'A::type.
   open top S & S x --> neigh top (S, x)"
  by (import hollight OPEN_OWN_NEIGH)

lemma OPEN_UNOPEN: "ALL (S::'A::type => bool) top::'A::type topology.
   open top S =
   (re_Union (%P::'A::type => bool. open top P & re_subset P S) = S)"
  by (import hollight OPEN_UNOPEN)

lemma OPEN_SUBOPEN: "ALL (S::'A::type => bool) top::'A::type topology.
   open top S =
   (ALL x::'A::type.
       S x -->
       (EX xa::'A::type => bool. xa x & open top xa & re_subset xa S))"
  by (import hollight OPEN_SUBOPEN)

lemma OPEN_NEIGH: "ALL (S::'A::type => bool) top::'A::type topology.
   open top S =
   (ALL x::'A::type.
       S x -->
       (EX xa::'A::type => bool. neigh top (xa, x) & re_subset xa S))"
  by (import hollight OPEN_NEIGH)

constdefs
  closed :: "'A topology => ('A => bool) => bool" 
  "closed == %(u::'A::type topology) ua::'A::type => bool. open u (re_compl ua)"

lemma DEF_closed: "closed =
(%(u::'A::type topology) ua::'A::type => bool. open u (re_compl ua))"
  by (import hollight DEF_closed)

constdefs
  limpt :: "'A topology => 'A => ('A => bool) => bool" 
  "limpt ==
%(u::'A::type topology) (ua::'A::type) ub::'A::type => bool.
   ALL N::'A::type => bool.
      neigh u (N, ua) --> (EX y::'A::type. ua ~= y & ub y & N y)"

lemma DEF_limpt: "limpt =
(%(u::'A::type topology) (ua::'A::type) ub::'A::type => bool.
    ALL N::'A::type => bool.
       neigh u (N, ua) --> (EX y::'A::type. ua ~= y & ub y & N y))"
  by (import hollight DEF_limpt)

lemma CLOSED_LIMPT: "ALL (top::'A::type topology) S::'A::type => bool.
   closed top S = (ALL x::'A::type. limpt top x S --> S x)"
  by (import hollight CLOSED_LIMPT)

constdefs
  ismet :: "('A * 'A => hollight.real) => bool" 
  "ismet ==
%u::'A::type * 'A::type => hollight.real.
   (ALL (x::'A::type) y::'A::type. (u (x, y) = real_of_num 0) = (x = y)) &
   (ALL (x::'A::type) (y::'A::type) z::'A::type.
       real_le (u (y, z)) (real_add (u (x, y)) (u (x, z))))"

lemma DEF_ismet: "ismet =
(%u::'A::type * 'A::type => hollight.real.
    (ALL (x::'A::type) y::'A::type. (u (x, y) = real_of_num 0) = (x = y)) &
    (ALL (x::'A::type) (y::'A::type) z::'A::type.
        real_le (u (y, z)) (real_add (u (x, y)) (u (x, z)))))"
  by (import hollight DEF_ismet)

typedef (open) ('A) metric = "(Collect::(('A::type * 'A::type => hollight.real) => bool)
          => ('A::type * 'A::type => hollight.real) set)
 (ismet::('A::type * 'A::type => hollight.real) => bool)"  morphisms "mdist" "metric"
  apply (rule light_ex_imp_nonempty[where t="(Eps::(('A::type * 'A::type => hollight.real) => bool)
      => 'A::type * 'A::type => hollight.real)
 (ismet::('A::type * 'A::type => hollight.real) => bool)"])
  by (import hollight TYDEF_metric)

syntax
  mdist :: _ 

syntax
  metric :: _ 

lemmas "TYDEF_metric_@intern" = typedef_hol2hollight 
  [where a="a :: 'A metric" and r=r ,
   OF type_definition_metric]

lemma METRIC_ISMET: "ALL m::'A::type metric. ismet (mdist m)"
  by (import hollight METRIC_ISMET)

lemma METRIC_ZERO: "ALL (m::'A::type metric) (x::'A::type) y::'A::type.
   (mdist m (x, y) = real_of_num 0) = (x = y)"
  by (import hollight METRIC_ZERO)

lemma METRIC_SAME: "ALL (m::'A::type metric) x::'A::type. mdist m (x, x) = real_of_num 0"
  by (import hollight METRIC_SAME)

lemma METRIC_POS: "ALL (m::'A::type metric) (x::'A::type) y::'A::type.
   real_le (real_of_num 0) (mdist m (x, y))"
  by (import hollight METRIC_POS)

lemma METRIC_SYM: "ALL (m::'A::type metric) (x::'A::type) y::'A::type.
   mdist m (x, y) = mdist m (y, x)"
  by (import hollight METRIC_SYM)

lemma METRIC_TRIANGLE: "ALL (m::'A::type metric) (x::'A::type) (y::'A::type) z::'A::type.
   real_le (mdist m (x, z)) (real_add (mdist m (x, y)) (mdist m (y, z)))"
  by (import hollight METRIC_TRIANGLE)

lemma METRIC_NZ: "ALL (m::'A::type metric) (x::'A::type) y::'A::type.
   x ~= y --> real_lt (real_of_num 0) (mdist m (x, y))"
  by (import hollight METRIC_NZ)

constdefs
  mtop :: "'A metric => 'A topology" 
  "mtop ==
%u::'A::type metric.
   topology
    (%S::'A::type => bool.
        ALL x::'A::type.
           S x -->
           (EX e::hollight.real.
               real_lt (real_of_num 0) e &
               (ALL y::'A::type. real_lt (mdist u (x, y)) e --> S y)))"

lemma DEF_mtop: "mtop =
(%u::'A::type metric.
    topology
     (%S::'A::type => bool.
         ALL x::'A::type.
            S x -->
            (EX e::hollight.real.
                real_lt (real_of_num 0) e &
                (ALL y::'A::type. real_lt (mdist u (x, y)) e --> S y))))"
  by (import hollight DEF_mtop)

lemma mtop_istopology: "ALL m::'A::type metric.
   istopology
    (%S::'A::type => bool.
        ALL x::'A::type.
           S x -->
           (EX e::hollight.real.
               real_lt (real_of_num 0) e &
               (ALL y::'A::type. real_lt (mdist m (x, y)) e --> S y)))"
  by (import hollight mtop_istopology)

lemma MTOP_OPEN: "ALL m::'A::type metric.
   open (mtop m) (S::'A::type => bool) =
   (ALL x::'A::type.
       S x -->
       (EX e::hollight.real.
           real_lt (real_of_num 0) e &
           (ALL y::'A::type. real_lt (mdist m (x, y)) e --> S y)))"
  by (import hollight MTOP_OPEN)

constdefs
  ball :: "'A metric => 'A * hollight.real => 'A => bool" 
  "ball ==
%(u::'A::type metric) (ua::'A::type * hollight.real) y::'A::type.
   real_lt (mdist u (fst ua, y)) (snd ua)"

lemma DEF_ball: "ball =
(%(u::'A::type metric) (ua::'A::type * hollight.real) y::'A::type.
    real_lt (mdist u (fst ua, y)) (snd ua))"
  by (import hollight DEF_ball)

lemma BALL_OPEN: "ALL (m::'A::type metric) (x::'A::type) e::hollight.real.
   real_lt (real_of_num 0) e --> open (mtop m) (ball m (x, e))"
  by (import hollight BALL_OPEN)

lemma BALL_NEIGH: "ALL (m::'A::type metric) (x::'A::type) e::hollight.real.
   real_lt (real_of_num 0) e --> neigh (mtop m) (ball m (x, e), x)"
  by (import hollight BALL_NEIGH)

lemma MTOP_LIMPT: "ALL (m::'A::type metric) (x::'A::type) S::'A::type => bool.
   limpt (mtop m) x S =
   (ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX y::'A::type. x ~= y & S y & real_lt (mdist m (x, y)) e))"
  by (import hollight MTOP_LIMPT)

lemma ISMET_R1: "ismet
 (GABS
   (%f::hollight.real * hollight.real => hollight.real.
       ALL (x::hollight.real) y::hollight.real.
          GEQ (f (x, y)) (real_abs (real_sub y x))))"
  by (import hollight ISMET_R1)

constdefs
  mr1 :: "hollight.real metric" 
  "mr1 ==
metric
 (GABS
   (%f::hollight.real * hollight.real => hollight.real.
       ALL (x::hollight.real) y::hollight.real.
          GEQ (f (x, y)) (real_abs (real_sub y x))))"

lemma DEF_mr1: "mr1 =
metric
 (GABS
   (%f::hollight.real * hollight.real => hollight.real.
       ALL (x::hollight.real) y::hollight.real.
          GEQ (f (x, y)) (real_abs (real_sub y x))))"
  by (import hollight DEF_mr1)

lemma MR1_DEF: "ALL (x::hollight.real) y::hollight.real.
   mdist mr1 (x, y) = real_abs (real_sub y x)"
  by (import hollight MR1_DEF)

lemma MR1_ADD: "ALL (x::hollight.real) d::hollight.real.
   mdist mr1 (x, real_add x d) = real_abs d"
  by (import hollight MR1_ADD)

lemma MR1_SUB: "ALL (x::hollight.real) d::hollight.real.
   mdist mr1 (x, real_sub x d) = real_abs d"
  by (import hollight MR1_SUB)

lemma MR1_ADD_LE: "ALL (x::hollight.real) d::hollight.real.
   real_le (real_of_num 0) d --> mdist mr1 (x, real_add x d) = d"
  by (import hollight MR1_ADD_LE)

lemma MR1_SUB_LE: "ALL (x::hollight.real) d::hollight.real.
   real_le (real_of_num 0) d --> mdist mr1 (x, real_sub x d) = d"
  by (import hollight MR1_SUB_LE)

lemma MR1_ADD_LT: "ALL (x::hollight.real) d::hollight.real.
   real_lt (real_of_num 0) d --> mdist mr1 (x, real_add x d) = d"
  by (import hollight MR1_ADD_LT)

lemma MR1_SUB_LT: "ALL (x::hollight.real) d::hollight.real.
   real_lt (real_of_num 0) d --> mdist mr1 (x, real_sub x d) = d"
  by (import hollight MR1_SUB_LT)

lemma MR1_BETWEEN1: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt x z & real_lt (mdist mr1 (x, y)) (real_sub z x) --> real_lt y z"
  by (import hollight MR1_BETWEEN1)

lemma MR1_LIMPT: "ALL x::hollight.real. limpt (mtop mr1) x re_universe"
  by (import hollight MR1_LIMPT)

constdefs
  dorder :: "('A => 'A => bool) => bool" 
  "dorder ==
%u::'A::type => 'A::type => bool.
   ALL (x::'A::type) y::'A::type.
      u x x & u y y -->
      (EX z::'A::type. u z z & (ALL w::'A::type. u w z --> u w x & u w y))"

lemma DEF_dorder: "dorder =
(%u::'A::type => 'A::type => bool.
    ALL (x::'A::type) y::'A::type.
       u x x & u y y -->
       (EX z::'A::type. u z z & (ALL w::'A::type. u w z --> u w x & u w y)))"
  by (import hollight DEF_dorder)

constdefs
  tends :: "('B => 'A) => 'A => 'A topology * ('B => 'B => bool) => bool" 
  "tends ==
%(u::'B::type => 'A::type) (ua::'A::type)
   ub::'A::type topology * ('B::type => 'B::type => bool).
   ALL N::'A::type => bool.
      neigh (fst ub) (N, ua) -->
      (EX n::'B::type.
          snd ub n n & (ALL m::'B::type. snd ub m n --> N (u m)))"

lemma DEF_tends: "tends =
(%(u::'B::type => 'A::type) (ua::'A::type)
    ub::'A::type topology * ('B::type => 'B::type => bool).
    ALL N::'A::type => bool.
       neigh (fst ub) (N, ua) -->
       (EX n::'B::type.
           snd ub n n & (ALL m::'B::type. snd ub m n --> N (u m))))"
  by (import hollight DEF_tends)

constdefs
  bounded :: "'A metric * ('B => 'B => bool) => ('B => 'A) => bool" 
  "bounded ==
%(u::'A::type metric * ('B::type => 'B::type => bool))
   ua::'B::type => 'A::type.
   EX (k::hollight.real) (x::'A::type) N::'B::type.
      snd u N N &
      (ALL n::'B::type. snd u n N --> real_lt (mdist (fst u) (ua n, x)) k)"

lemma DEF_bounded: "bounded =
(%(u::'A::type metric * ('B::type => 'B::type => bool))
    ua::'B::type => 'A::type.
    EX (k::hollight.real) (x::'A::type) N::'B::type.
       snd u N N &
       (ALL n::'B::type. snd u n N --> real_lt (mdist (fst u) (ua n, x)) k))"
  by (import hollight DEF_bounded)

constdefs
  tendsto :: "'A metric * 'A => 'A => 'A => bool" 
  "tendsto ==
%(u::'A::type metric * 'A::type) (ua::'A::type) ub::'A::type.
   real_lt (real_of_num 0) (mdist (fst u) (snd u, ua)) &
   real_le (mdist (fst u) (snd u, ua)) (mdist (fst u) (snd u, ub))"

lemma DEF_tendsto: "tendsto =
(%(u::'A::type metric * 'A::type) (ua::'A::type) ub::'A::type.
    real_lt (real_of_num 0) (mdist (fst u) (snd u, ua)) &
    real_le (mdist (fst u) (snd u, ua)) (mdist (fst u) (snd u, ub)))"
  by (import hollight DEF_tendsto)

lemma DORDER_LEMMA: "ALL g::'A::type => 'A::type => bool.
   dorder g -->
   (ALL (P::'A::type => bool) Q::'A::type => bool.
       (EX n::'A::type. g n n & (ALL m::'A::type. g m n --> P m)) &
       (EX n::'A::type. g n n & (ALL m::'A::type. g m n --> Q m)) -->
       (EX n::'A::type. g n n & (ALL m::'A::type. g m n --> P m & Q m)))"
  by (import hollight DORDER_LEMMA)

lemma DORDER_NGE: "dorder >="
  by (import hollight DORDER_NGE)

lemma DORDER_TENDSTO: "ALL (m::'A::type metric) x::'A::type. dorder (tendsto (m, x))"
  by (import hollight DORDER_TENDSTO)

lemma MTOP_TENDS: "ALL (d::'A::type metric) (g::'B::type => 'B::type => bool)
   (x::'B::type => 'A::type) x0::'A::type.
   tends x x0 (mtop d, g) =
   (ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX n::'B::type.
           g n n &
           (ALL m::'B::type. g m n --> real_lt (mdist d (x m, x0)) e)))"
  by (import hollight MTOP_TENDS)

lemma MTOP_TENDS_UNIQ: "ALL (g::'B::type => 'B::type => bool) d::'A::type metric.
   dorder g -->
   tends (x::'B::type => 'A::type) (x0::'A::type) (mtop d, g) &
   tends x (x1::'A::type) (mtop d, g) -->
   x0 = x1"
  by (import hollight MTOP_TENDS_UNIQ)

lemma SEQ_TENDS: "ALL (d::'A::type metric) (x::nat => 'A::type) x0::'A::type.
   tends x x0 (mtop d, >=) =
   (ALL xa::hollight.real.
       real_lt (real_of_num 0) xa -->
       (EX xb::nat.
           ALL xc::nat. >= xc xb --> real_lt (mdist d (x xc, x0)) xa))"
  by (import hollight SEQ_TENDS)

lemma LIM_TENDS: "ALL (m1::'A::type metric) (m2::'B::type metric) (f::'A::type => 'B::type)
   (x0::'A::type) y0::'B::type.
   limpt (mtop m1) x0 re_universe -->
   tends f y0 (mtop m2, tendsto (m1, x0)) =
   (ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX d::hollight.real.
           real_lt (real_of_num 0) d &
           (ALL x::'A::type.
               real_lt (real_of_num 0) (mdist m1 (x, x0)) &
               real_le (mdist m1 (x, x0)) d -->
               real_lt (mdist m2 (f x, y0)) e)))"
  by (import hollight LIM_TENDS)

lemma LIM_TENDS2: "ALL (m1::'A::type metric) (m2::'B::type metric) (f::'A::type => 'B::type)
   (x0::'A::type) y0::'B::type.
   limpt (mtop m1) x0 re_universe -->
   tends f y0 (mtop m2, tendsto (m1, x0)) =
   (ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX d::hollight.real.
           real_lt (real_of_num 0) d &
           (ALL x::'A::type.
               real_lt (real_of_num 0) (mdist m1 (x, x0)) &
               real_lt (mdist m1 (x, x0)) d -->
               real_lt (mdist m2 (f x, y0)) e)))"
  by (import hollight LIM_TENDS2)

lemma MR1_BOUNDED: "ALL (g::'A::type => 'A::type => bool) f::'A::type => hollight.real.
   bounded (mr1, g) f =
   (EX (k::hollight.real) N::'A::type.
       g N N & (ALL n::'A::type. g n N --> real_lt (real_abs (f n)) k))"
  by (import hollight MR1_BOUNDED)

lemma NET_NULL: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   x0::hollight.real.
   tends x x0 (mtop mr1, g) =
   tends (%n::'A::type. real_sub (x n) x0) (real_of_num 0) (mtop mr1, g)"
  by (import hollight NET_NULL)

lemma NET_CONV_BOUNDED: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   x0::hollight.real. tends x x0 (mtop mr1, g) --> bounded (mr1, g) x"
  by (import hollight NET_CONV_BOUNDED)

lemma NET_CONV_NZ: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   x0::hollight.real.
   tends x x0 (mtop mr1, g) & x0 ~= real_of_num 0 -->
   (EX N::'A::type.
       g N N & (ALL n::'A::type. g n N --> x n ~= real_of_num 0))"
  by (import hollight NET_CONV_NZ)

lemma NET_CONV_IBOUNDED: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   x0::hollight.real.
   tends x x0 (mtop mr1, g) & x0 ~= real_of_num 0 -->
   bounded (mr1, g) (%n::'A::type. real_inv (x n))"
  by (import hollight NET_CONV_IBOUNDED)

lemma NET_NULL_ADD: "ALL g::'A::type => 'A::type => bool.
   dorder g -->
   (ALL (x::'A::type => hollight.real) y::'A::type => hollight.real.
       tends x (real_of_num 0) (mtop mr1, g) &
       tends y (real_of_num 0) (mtop mr1, g) -->
       tends (%n::'A::type. real_add (x n) (y n)) (real_of_num 0)
        (mtop mr1, g))"
  by (import hollight NET_NULL_ADD)

lemma NET_NULL_MUL: "ALL g::'A::type => 'A::type => bool.
   dorder g -->
   (ALL (x::'A::type => hollight.real) y::'A::type => hollight.real.
       bounded (mr1, g) x & tends y (real_of_num 0) (mtop mr1, g) -->
       tends (%n::'A::type. real_mul (x n) (y n)) (real_of_num 0)
        (mtop mr1, g))"
  by (import hollight NET_NULL_MUL)

lemma NET_NULL_CMUL: "ALL (g::'A::type => 'A::type => bool) (k::hollight.real)
   x::'A::type => hollight.real.
   tends x (real_of_num 0) (mtop mr1, g) -->
   tends (%n::'A::type. real_mul k (x n)) (real_of_num 0) (mtop mr1, g)"
  by (import hollight NET_NULL_CMUL)

lemma NET_ADD: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   (x0::hollight.real) (y::'A::type => hollight.real) y0::hollight.real.
   dorder g -->
   tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) -->
   tends (%n::'A::type. real_add (x n) (y n)) (real_add x0 y0) (mtop mr1, g)"
  by (import hollight NET_ADD)

lemma NET_NEG: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   x0::hollight.real.
   dorder g -->
   tends x x0 (mtop mr1, g) =
   tends (%n::'A::type. real_neg (x n)) (real_neg x0) (mtop mr1, g)"
  by (import hollight NET_NEG)

lemma NET_SUB: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   (x0::hollight.real) (y::'A::type => hollight.real) y0::hollight.real.
   dorder g -->
   tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) -->
   tends (%xa::'A::type. real_sub (x xa) (y xa)) (real_sub x0 y0)
    (mtop mr1, g)"
  by (import hollight NET_SUB)

lemma NET_MUL: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   (y::'A::type => hollight.real) (x0::hollight.real) y0::hollight.real.
   dorder g -->
   tends x x0 (mtop mr1, g) & tends y y0 (mtop mr1, g) -->
   tends (%n::'A::type. real_mul (x n) (y n)) (real_mul x0 y0) (mtop mr1, g)"
  by (import hollight NET_MUL)

lemma NET_INV: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   x0::hollight.real.
   dorder g -->
   tends x x0 (mtop mr1, g) & x0 ~= real_of_num 0 -->
   tends (%n::'A::type. real_inv (x n)) (real_inv x0) (mtop mr1, g)"
  by (import hollight NET_INV)

lemma NET_DIV: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   (x0::hollight.real) (y::'A::type => hollight.real) y0::hollight.real.
   dorder g -->
   tends x x0 (mtop mr1, g) &
   tends y y0 (mtop mr1, g) & y0 ~= real_of_num 0 -->
   tends (%xa::'A::type. real_div (x xa) (y xa)) (real_div x0 y0)
    (mtop mr1, g)"
  by (import hollight NET_DIV)

lemma NET_ABS: "ALL (x::'A::type => hollight.real) x0::hollight.real.
   tends x x0 (mtop mr1, g::'A::type => 'A::type => bool) -->
   tends (%n::'A::type. real_abs (x n)) (real_abs x0) (mtop mr1, g)"
  by (import hollight NET_ABS)

lemma NET_SUM: "ALL g::'q_71813::type => 'q_71813::type => bool.
   dorder g &
   tends (%x::'q_71813::type. real_of_num 0) (real_of_num 0)
    (mtop mr1, g) -->
   (ALL (x::nat) n::nat.
       (ALL r::nat.
           <= x r & < r (x + n) -->
           tends ((f::nat => 'q_71813::type => hollight.real) r)
            ((l::nat => hollight.real) r) (mtop mr1, g)) -->
       tends (%xa::'q_71813::type. psum (x, n) (%r::nat. f r xa))
        (psum (x, n) l) (mtop mr1, g))"
  by (import hollight NET_SUM)

lemma NET_LE: "ALL (g::'A::type => 'A::type => bool) (x::'A::type => hollight.real)
   (x0::hollight.real) (y::'A::type => hollight.real) y0::hollight.real.
   dorder g -->
   tends x x0 (mtop mr1, g) &
   tends y y0 (mtop mr1, g) &
   (EX N::'A::type.
       g N N & (ALL n::'A::type. g n N --> real_le (x n) (y n))) -->
   real_le x0 y0"
  by (import hollight NET_LE)

constdefs
  tends_num_real :: "(nat => hollight.real) => hollight.real => bool" 
  "tends_num_real ==
%(u::nat => hollight.real) ua::hollight.real. tends u ua (mtop mr1, >=)"

lemma DEF_tends_num_real: "tends_num_real =
(%(u::nat => hollight.real) ua::hollight.real. tends u ua (mtop mr1, >=))"
  by (import hollight DEF_tends_num_real)

lemma SEQ: "ALL (x::nat => hollight.real) x0::hollight.real.
   tends_num_real x x0 =
   (ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX N::nat.
           ALL n::nat. >= n N --> real_lt (real_abs (real_sub (x n) x0)) e))"
  by (import hollight SEQ)

lemma SEQ_CONST: "ALL k::hollight.real. tends_num_real (%x::nat. k) k"
  by (import hollight SEQ_CONST)

lemma SEQ_ADD: "ALL (x::nat => hollight.real) (x0::hollight.real) (y::nat => hollight.real)
   y0::hollight.real.
   tends_num_real x x0 & tends_num_real y y0 -->
   tends_num_real (%n::nat. real_add (x n) (y n)) (real_add x0 y0)"
  by (import hollight SEQ_ADD)

lemma SEQ_MUL: "ALL (x::nat => hollight.real) (x0::hollight.real) (y::nat => hollight.real)
   y0::hollight.real.
   tends_num_real x x0 & tends_num_real y y0 -->
   tends_num_real (%n::nat. real_mul (x n) (y n)) (real_mul x0 y0)"
  by (import hollight SEQ_MUL)

lemma SEQ_NEG: "ALL (x::nat => hollight.real) x0::hollight.real.
   tends_num_real x x0 =
   tends_num_real (%n::nat. real_neg (x n)) (real_neg x0)"
  by (import hollight SEQ_NEG)

lemma SEQ_INV: "ALL (x::nat => hollight.real) x0::hollight.real.
   tends_num_real x x0 & x0 ~= real_of_num 0 -->
   tends_num_real (%n::nat. real_inv (x n)) (real_inv x0)"
  by (import hollight SEQ_INV)

lemma SEQ_SUB: "ALL (x::nat => hollight.real) (x0::hollight.real) (y::nat => hollight.real)
   y0::hollight.real.
   tends_num_real x x0 & tends_num_real y y0 -->
   tends_num_real (%n::nat. real_sub (x n) (y n)) (real_sub x0 y0)"
  by (import hollight SEQ_SUB)

lemma SEQ_DIV: "ALL (x::nat => hollight.real) (x0::hollight.real) (y::nat => hollight.real)
   y0::hollight.real.
   tends_num_real x x0 & tends_num_real y y0 & y0 ~= real_of_num 0 -->
   tends_num_real (%n::nat. real_div (x n) (y n)) (real_div x0 y0)"
  by (import hollight SEQ_DIV)

lemma SEQ_UNIQ: "ALL (x::nat => hollight.real) (x1::hollight.real) x2::hollight.real.
   tends_num_real x x1 & tends_num_real x x2 --> x1 = x2"
  by (import hollight SEQ_UNIQ)

lemma SEQ_NULL: "ALL (s::nat => hollight.real) l::hollight.real.
   tends_num_real s l =
   tends_num_real (%n::nat. real_sub (s n) l) (real_of_num 0)"
  by (import hollight SEQ_NULL)

lemma SEQ_SUM: "ALL (f::nat => nat => hollight.real) (l::nat => hollight.real) (m::nat)
   n::nat.
   (ALL x::nat. <= m x & < x (m + n) --> tends_num_real (f x) (l x)) -->
   tends_num_real (%k::nat. psum (m, n) (%r::nat. f r k)) (psum (m, n) l)"
  by (import hollight SEQ_SUM)

lemma SEQ_TRANSFORM: "ALL (x::nat => hollight.real) (xa::nat => hollight.real) (xb::hollight.real)
   xc::nat.
   (ALL n::nat. <= xc n --> x n = xa n) & tends_num_real x xb -->
   tends_num_real xa xb"
  by (import hollight SEQ_TRANSFORM)

constdefs
  convergent :: "(nat => hollight.real) => bool" 
  "convergent == %u::nat => hollight.real. Ex (tends_num_real u)"

lemma DEF_convergent: "convergent = (%u::nat => hollight.real. Ex (tends_num_real u))"
  by (import hollight DEF_convergent)

constdefs
  cauchy :: "(nat => hollight.real) => bool" 
  "cauchy ==
%u::nat => hollight.real.
   ALL e::hollight.real.
      real_lt (real_of_num 0) e -->
      (EX N::nat.
          ALL (m::nat) n::nat.
             >= m N & >= n N -->
             real_lt (real_abs (real_sub (u m) (u n))) e)"

lemma DEF_cauchy: "cauchy =
(%u::nat => hollight.real.
    ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX N::nat.
           ALL (m::nat) n::nat.
              >= m N & >= n N -->
              real_lt (real_abs (real_sub (u m) (u n))) e))"
  by (import hollight DEF_cauchy)

constdefs
  lim :: "(nat => hollight.real) => hollight.real" 
  "lim == %u::nat => hollight.real. Eps (tends_num_real u)"

lemma DEF_lim: "lim = (%u::nat => hollight.real. Eps (tends_num_real u))"
  by (import hollight DEF_lim)

lemma SEQ_LIM: "ALL f::nat => hollight.real. convergent f = tends_num_real f (lim f)"
  by (import hollight SEQ_LIM)

constdefs
  subseq :: "(nat => nat) => bool" 
  "subseq == %u::nat => nat. ALL (m::nat) n::nat. < m n --> < (u m) (u n)"

lemma DEF_subseq: "subseq = (%u::nat => nat. ALL (m::nat) n::nat. < m n --> < (u m) (u n))"
  by (import hollight DEF_subseq)

lemma SUBSEQ_SUC: "ALL f::nat => nat. subseq f = (ALL n::nat. < (f n) (f (Suc n)))"
  by (import hollight SUBSEQ_SUC)

consts
  mono :: "(nat => hollight.real) => bool" 

defs
  mono_def: "hollight.mono ==
%u::nat => hollight.real.
   (ALL (m::nat) n::nat. <= m n --> real_le (u m) (u n)) |
   (ALL (m::nat) n::nat. <= m n --> hollight.real_ge (u m) (u n))"

lemma DEF_mono: "hollight.mono =
(%u::nat => hollight.real.
    (ALL (m::nat) n::nat. <= m n --> real_le (u m) (u n)) |
    (ALL (m::nat) n::nat. <= m n --> hollight.real_ge (u m) (u n)))"
  by (import hollight DEF_mono)

lemma MONO_SUC: "ALL f::nat => hollight.real.
   hollight.mono f =
   ((ALL x::nat. hollight.real_ge (f (Suc x)) (f x)) |
    (ALL n::nat. real_le (f (Suc n)) (f n)))"
  by (import hollight MONO_SUC)

lemma MAX_LEMMA: "ALL (s::nat => hollight.real) N::nat.
   EX k::hollight.real. ALL n::nat. < n N --> real_lt (real_abs (s n)) k"
  by (import hollight MAX_LEMMA)

lemma SEQ_BOUNDED: "ALL s::nat => hollight.real.
   bounded (mr1, >=) s =
   (EX k::hollight.real. ALL n::nat. real_lt (real_abs (s n)) k)"
  by (import hollight SEQ_BOUNDED)

lemma SEQ_BOUNDED_2: "ALL (f::nat => hollight.real) (k::hollight.real) K::hollight.real.
   (ALL n::nat. real_le k (f n) & real_le (f n) K) --> bounded (mr1, >=) f"
  by (import hollight SEQ_BOUNDED_2)

lemma SEQ_CBOUNDED: "ALL f::nat => hollight.real. cauchy f --> bounded (mr1, >=) f"
  by (import hollight SEQ_CBOUNDED)

lemma SEQ_ICONV: "ALL f::nat => hollight.real.
   bounded (mr1, >=) f &
   (ALL (m::nat) n::nat. >= m n --> hollight.real_ge (f m) (f n)) -->
   convergent f"
  by (import hollight SEQ_ICONV)

lemma SEQ_NEG_CONV: "ALL f::nat => hollight.real.
   convergent f = convergent (%n::nat. real_neg (f n))"
  by (import hollight SEQ_NEG_CONV)

lemma SEQ_NEG_BOUNDED: "ALL f::nat => hollight.real.
   bounded (mr1, >=) (%n::nat. real_neg (f n)) = bounded (mr1, >=) f"
  by (import hollight SEQ_NEG_BOUNDED)

lemma SEQ_BCONV: "ALL f::nat => hollight.real.
   bounded (mr1, >=) f & hollight.mono f --> convergent f"
  by (import hollight SEQ_BCONV)

lemma SEQ_MONOSUB: "ALL s::nat => hollight.real.
   EX f::nat => nat. subseq f & hollight.mono (%n::nat. s (f n))"
  by (import hollight SEQ_MONOSUB)

lemma SEQ_SBOUNDED: "ALL (s::nat => hollight.real) f::nat => nat.
   bounded (mr1, >=) s --> bounded (mr1, >=) (%n::nat. s (f n))"
  by (import hollight SEQ_SBOUNDED)

lemma SEQ_SUBLE: "ALL (f::nat => nat) x::nat. subseq f --> <= x (f x)"
  by (import hollight SEQ_SUBLE)

lemma SEQ_DIRECT: "ALL f::nat => nat.
   subseq f --> (ALL (N1::nat) N2::nat. EX x::nat. >= x N1 & >= (f x) N2)"
  by (import hollight SEQ_DIRECT)

lemma SEQ_CAUCHY: "ALL f::nat => hollight.real. cauchy f = convergent f"
  by (import hollight SEQ_CAUCHY)

lemma SEQ_LE: "ALL (f::nat => hollight.real) (g::nat => hollight.real) (l::hollight.real)
   m::hollight.real.
   tends_num_real f l &
   tends_num_real g m &
   (EX N::nat. ALL n::nat. >= n N --> real_le (f n) (g n)) -->
   real_le l m"
  by (import hollight SEQ_LE)

lemma SEQ_LE_0: "ALL (x::nat => hollight.real) xa::nat => hollight.real.
   tends_num_real x (real_of_num 0) &
   (EX xb::nat.
       ALL xc::nat.
          >= xc xb --> real_le (real_abs (xa xc)) (real_abs (x xc))) -->
   tends_num_real xa (real_of_num 0)"
  by (import hollight SEQ_LE_0)

lemma SEQ_SUC: "ALL (f::nat => hollight.real) l::hollight.real.
   tends_num_real f l = tends_num_real (%n::nat. f (Suc n)) l"
  by (import hollight SEQ_SUC)

lemma SEQ_ABS: "ALL f::nat => hollight.real.
   tends_num_real (%n::nat. real_abs (f n)) (real_of_num 0) =
   tends_num_real f (real_of_num 0)"
  by (import hollight SEQ_ABS)

lemma SEQ_ABS_IMP: "ALL (f::nat => hollight.real) l::hollight.real.
   tends_num_real f l -->
   tends_num_real (%n::nat. real_abs (f n)) (real_abs l)"
  by (import hollight SEQ_ABS_IMP)

lemma SEQ_INV0: "ALL f::nat => hollight.real.
   (ALL y::hollight.real.
       EX N::nat. ALL n::nat. >= n N --> hollight.real_gt (f n) y) -->
   tends_num_real (%n::nat. real_inv (f n)) (real_of_num 0)"
  by (import hollight SEQ_INV0)

lemma SEQ_POWER_ABS: "ALL c::hollight.real.
   real_lt (real_abs c) (real_of_num (NUMERAL_BIT1 0)) -->
   tends_num_real (real_pow (real_abs c)) (real_of_num 0)"
  by (import hollight SEQ_POWER_ABS)

lemma SEQ_POWER: "ALL c::hollight.real.
   real_lt (real_abs c) (real_of_num (NUMERAL_BIT1 0)) -->
   tends_num_real (real_pow c) (real_of_num 0)"
  by (import hollight SEQ_POWER)

lemma NEST_LEMMA: "ALL (f::nat => hollight.real) g::nat => hollight.real.
   (ALL n::nat. hollight.real_ge (f (Suc n)) (f n)) &
   (ALL n::nat. real_le (g (Suc n)) (g n)) &
   (ALL n::nat. real_le (f n) (g n)) -->
   (EX (l::hollight.real) m::hollight.real.
       real_le l m &
       ((ALL n::nat. real_le (f n) l) & tends_num_real f l) &
       (ALL n::nat. real_le m (g n)) & tends_num_real g m)"
  by (import hollight NEST_LEMMA)

lemma NEST_LEMMA_UNIQ: "ALL (f::nat => hollight.real) g::nat => hollight.real.
   (ALL n::nat. hollight.real_ge (f (Suc n)) (f n)) &
   (ALL n::nat. real_le (g (Suc n)) (g n)) &
   (ALL n::nat. real_le (f n) (g n)) &
   tends_num_real (%n::nat. real_sub (f n) (g n)) (real_of_num 0) -->
   (EX l::hollight.real.
       ((ALL n::nat. real_le (f n) l) & tends_num_real f l) &
       (ALL n::nat. real_le l (g n)) & tends_num_real g l)"
  by (import hollight NEST_LEMMA_UNIQ)

lemma BOLZANO_LEMMA: "ALL P::hollight.real * hollight.real => bool.
   (ALL (a::hollight.real) (b::hollight.real) c::hollight.real.
       real_le a b & real_le b c & P (a, b) & P (b, c) --> P (a, c)) &
   (ALL x::hollight.real.
       EX d::hollight.real.
          real_lt (real_of_num 0) d &
          (ALL (a::hollight.real) b::hollight.real.
              real_le a x & real_le x b & real_lt (real_sub b a) d -->
              P (a, b))) -->
   (ALL (a::hollight.real) b::hollight.real. real_le a b --> P (a, b))"
  by (import hollight BOLZANO_LEMMA)

constdefs
  sums :: "(nat => hollight.real) => hollight.real => bool" 
  "sums == %u::nat => hollight.real. tends_num_real (%n::nat. psum (0, n) u)"

lemma DEF_sums: "sums = (%u::nat => hollight.real. tends_num_real (%n::nat. psum (0, n) u))"
  by (import hollight DEF_sums)

constdefs
  summable :: "(nat => hollight.real) => bool" 
  "summable == %u::nat => hollight.real. Ex (sums u)"

lemma DEF_summable: "summable = (%u::nat => hollight.real. Ex (sums u))"
  by (import hollight DEF_summable)

constdefs
  suminf :: "(nat => hollight.real) => hollight.real" 
  "suminf == %u::nat => hollight.real. Eps (sums u)"

lemma DEF_suminf: "suminf = (%u::nat => hollight.real. Eps (sums u))"
  by (import hollight DEF_suminf)

lemma SUM_SUMMABLE: "ALL (f::nat => hollight.real) l::hollight.real. sums f l --> summable f"
  by (import hollight SUM_SUMMABLE)

lemma SUMMABLE_SUM: "ALL f::nat => hollight.real. summable f --> sums f (suminf f)"
  by (import hollight SUMMABLE_SUM)

lemma SUM_UNIQ: "ALL (f::nat => hollight.real) x::hollight.real. sums f x --> x = suminf f"
  by (import hollight SUM_UNIQ)

lemma SER_UNIQ: "ALL (f::nat => hollight.real) (x::hollight.real) y::hollight.real.
   sums f x & sums f y --> x = y"
  by (import hollight SER_UNIQ)

lemma SER_0: "ALL (f::nat => hollight.real) n::nat.
   (ALL m::nat. <= n m --> f m = real_of_num 0) --> sums f (psum (0, n) f)"
  by (import hollight SER_0)

lemma SER_POS_LE: "ALL (f::nat => hollight.real) n::nat.
   summable f & (ALL m::nat. <= n m --> real_le (real_of_num 0) (f m)) -->
   real_le (psum (0, n) f) (suminf f)"
  by (import hollight SER_POS_LE)

lemma SER_POS_LT: "ALL (f::nat => hollight.real) n::nat.
   summable f & (ALL m::nat. <= n m --> real_lt (real_of_num 0) (f m)) -->
   real_lt (psum (0, n) f) (suminf f)"
  by (import hollight SER_POS_LT)

lemma SER_GROUP: "ALL (f::nat => hollight.real) k::nat.
   summable f & < 0 k --> sums (%n::nat. psum (n * k, k) f) (suminf f)"
  by (import hollight SER_GROUP)

lemma SER_PAIR: "ALL f::nat => hollight.real.
   summable f -->
   sums
    (%n::nat.
        psum
         (NUMERAL_BIT0 (NUMERAL_BIT1 0) * n, NUMERAL_BIT0 (NUMERAL_BIT1 0))
         f)
    (suminf f)"
  by (import hollight SER_PAIR)

lemma SER_OFFSET: "ALL f::nat => hollight.real.
   summable f -->
   (ALL k::nat.
       sums (%n::nat. f (n + k)) (real_sub (suminf f) (psum (0, k) f)))"
  by (import hollight SER_OFFSET)

lemma SER_OFFSET_REV: "ALL (f::nat => hollight.real) k::nat.
   summable (%n::nat. f (n + k)) -->
   sums f (real_add (psum (0, k) f) (suminf (%n::nat. f (n + k))))"
  by (import hollight SER_OFFSET_REV)

lemma SER_POS_LT_PAIR: "ALL (f::nat => hollight.real) n::nat.
   summable f &
   (ALL d::nat.
       real_lt (real_of_num 0)
        (real_add (f (n + NUMERAL_BIT0 (NUMERAL_BIT1 0) * d))
          (f (n +
              (NUMERAL_BIT0 (NUMERAL_BIT1 0) * d + NUMERAL_BIT1 0))))) -->
   real_lt (psum (0, n) f) (suminf f)"
  by (import hollight SER_POS_LT_PAIR)

lemma SER_ADD: "ALL (x::nat => hollight.real) (x0::hollight.real) (y::nat => hollight.real)
   y0::hollight.real.
   sums x x0 & sums y y0 -->
   sums (%n::nat. real_add (x n) (y n)) (real_add x0 y0)"
  by (import hollight SER_ADD)

lemma SER_CMUL: "ALL (x::nat => hollight.real) (x0::hollight.real) c::hollight.real.
   sums x x0 --> sums (%n::nat. real_mul c (x n)) (real_mul c x0)"
  by (import hollight SER_CMUL)

lemma SER_NEG: "ALL (x::nat => hollight.real) x0::hollight.real.
   sums x x0 --> sums (%xa::nat. real_neg (x xa)) (real_neg x0)"
  by (import hollight SER_NEG)

lemma SER_SUB: "ALL (x::nat => hollight.real) (x0::hollight.real) (y::nat => hollight.real)
   y0::hollight.real.
   sums x x0 & sums y y0 -->
   sums (%n::nat. real_sub (x n) (y n)) (real_sub x0 y0)"
  by (import hollight SER_SUB)

lemma SER_CDIV: "ALL (x::nat => hollight.real) (x0::hollight.real) c::hollight.real.
   sums x x0 --> sums (%xa::nat. real_div (x xa) c) (real_div x0 c)"
  by (import hollight SER_CDIV)

lemma SER_CAUCHY: "ALL f::nat => hollight.real.
   summable f =
   (ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX N::nat.
           ALL (m::nat) n::nat.
              >= m N --> real_lt (real_abs (psum (m, n) f)) e))"
  by (import hollight SER_CAUCHY)

lemma SER_ZERO: "ALL f::nat => hollight.real. summable f --> tends_num_real f (real_of_num 0)"
  by (import hollight SER_ZERO)

lemma SER_COMPAR: "ALL (f::nat => hollight.real) g::nat => hollight.real.
   (EX x::nat. ALL xa::nat. >= xa x --> real_le (real_abs (f xa)) (g xa)) &
   summable g -->
   summable f"
  by (import hollight SER_COMPAR)

lemma SER_COMPARA: "ALL (f::nat => hollight.real) g::nat => hollight.real.
   (EX x::nat. ALL xa::nat. >= xa x --> real_le (real_abs (f xa)) (g xa)) &
   summable g -->
   summable (%k::nat. real_abs (f k))"
  by (import hollight SER_COMPARA)

lemma SER_LE: "ALL (f::nat => hollight.real) g::nat => hollight.real.
   (ALL n::nat. real_le (f n) (g n)) & summable f & summable g -->
   real_le (suminf f) (suminf g)"
  by (import hollight SER_LE)

lemma SER_LE2: "ALL (f::nat => hollight.real) g::nat => hollight.real.
   (ALL n::nat. real_le (real_abs (f n)) (g n)) & summable g -->
   summable f & real_le (suminf f) (suminf g)"
  by (import hollight SER_LE2)

lemma SER_ACONV: "ALL f::nat => hollight.real.
   summable (%n::nat. real_abs (f n)) --> summable f"
  by (import hollight SER_ACONV)

lemma SER_ABS: "ALL f::nat => hollight.real.
   summable (%n::nat. real_abs (f n)) -->
   real_le (real_abs (suminf f)) (suminf (%n::nat. real_abs (f n)))"
  by (import hollight SER_ABS)

lemma GP_FINITE: "ALL x::hollight.real.
   x ~= real_of_num (NUMERAL_BIT1 0) -->
   (ALL n::nat.
       psum (0, n) (real_pow x) =
       real_div (real_sub (real_pow x n) (real_of_num (NUMERAL_BIT1 0)))
        (real_sub x (real_of_num (NUMERAL_BIT1 0))))"
  by (import hollight GP_FINITE)

lemma GP: "ALL x::hollight.real.
   real_lt (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   sums (real_pow x) (real_inv (real_sub (real_of_num (NUMERAL_BIT1 0)) x))"
  by (import hollight GP)

lemma ABS_NEG_LEMMA: "ALL (c::hollight.real) (x::hollight.real) y::hollight.real.
   real_le c (real_of_num 0) -->
   real_le (real_abs x) (real_mul c (real_abs y)) --> x = real_of_num 0"
  by (import hollight ABS_NEG_LEMMA)

lemma SER_RATIO: "ALL (f::nat => hollight.real) (c::hollight.real) N::nat.
   real_lt c (real_of_num (NUMERAL_BIT1 0)) &
   (ALL n::nat.
       >= n N -->
       real_le (real_abs (f (Suc n))) (real_mul c (real_abs (f n)))) -->
   summable f"
  by (import hollight SER_RATIO)

lemma SEQ_TRUNCATION: "ALL (f::nat => hollight.real) (l::hollight.real) (n::nat) b::hollight.real.
   sums f l & (ALL m::nat. real_le (real_abs (psum (n, m) f)) b) -->
   real_le (real_abs (real_sub l (psum (0, n) f))) b"
  by (import hollight SEQ_TRUNCATION)

constdefs
  tends_real_real :: "(hollight.real => hollight.real) => hollight.real => hollight.real => bool" 
  "tends_real_real ==
%(u::hollight.real => hollight.real) (ua::hollight.real) ub::hollight.real.
   tends u ua (mtop mr1, tendsto (mr1, ub))"

lemma DEF_tends_real_real: "tends_real_real =
(%(u::hollight.real => hollight.real) (ua::hollight.real) ub::hollight.real.
    tends u ua (mtop mr1, tendsto (mr1, ub)))"
  by (import hollight DEF_tends_real_real)

lemma LIM: "ALL (f::hollight.real => hollight.real) (y0::hollight.real)
   x0::hollight.real.
   tends_real_real f y0 x0 =
   (ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX d::hollight.real.
           real_lt (real_of_num 0) d &
           (ALL x::hollight.real.
               real_lt (real_of_num 0) (real_abs (real_sub x x0)) &
               real_lt (real_abs (real_sub x x0)) d -->
               real_lt (real_abs (real_sub (f x) y0)) e)))"
  by (import hollight LIM)

lemma LIM_CONST: "ALL k::hollight.real. All (tends_real_real (%x::hollight.real. k) k)"
  by (import hollight LIM_CONST)

lemma LIM_ADD: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) m::hollight.real.
   tends_real_real f l (x::hollight.real) & tends_real_real g m x -->
   tends_real_real (%x::hollight.real. real_add (f x) (g x)) (real_add l m)
    x"
  by (import hollight LIM_ADD)

lemma LIM_MUL: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) m::hollight.real.
   tends_real_real f l (x::hollight.real) & tends_real_real g m x -->
   tends_real_real (%x::hollight.real. real_mul (f x) (g x)) (real_mul l m)
    x"
  by (import hollight LIM_MUL)

lemma LIM_NEG: "ALL (f::hollight.real => hollight.real) l::hollight.real.
   tends_real_real f l (x::hollight.real) =
   tends_real_real (%x::hollight.real. real_neg (f x)) (real_neg l) x"
  by (import hollight LIM_NEG)

lemma LIM_INV: "ALL (f::hollight.real => hollight.real) l::hollight.real.
   tends_real_real f l (x::hollight.real) & l ~= real_of_num 0 -->
   tends_real_real (%x::hollight.real. real_inv (f x)) (real_inv l) x"
  by (import hollight LIM_INV)

lemma LIM_SUB: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) m::hollight.real.
   tends_real_real f l (x::hollight.real) & tends_real_real g m x -->
   tends_real_real (%x::hollight.real. real_sub (f x) (g x)) (real_sub l m)
    x"
  by (import hollight LIM_SUB)

lemma LIM_DIV: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) m::hollight.real.
   tends_real_real f l (x::hollight.real) &
   tends_real_real g m x & m ~= real_of_num 0 -->
   tends_real_real (%x::hollight.real. real_div (f x) (g x)) (real_div l m)
    x"
  by (import hollight LIM_DIV)

lemma LIM_NULL: "ALL (f::hollight.real => hollight.real) (l::hollight.real) x::hollight.real.
   tends_real_real f l x =
   tends_real_real (%x::hollight.real. real_sub (f x) l) (real_of_num 0) x"
  by (import hollight LIM_NULL)

lemma LIM_SUM: "ALL (f::nat => hollight.real => hollight.real) (l::nat => hollight.real)
   (m::nat) (n::nat) x::hollight.real.
   (ALL xa::nat.
       <= m xa & < xa (m + n) --> tends_real_real (f xa) (l xa) x) -->
   tends_real_real (%x::hollight.real. psum (m, n) (%r::nat. f r x))
    (psum (m, n) l) x"
  by (import hollight LIM_SUM)

lemma LIM_X: "ALL x0::hollight.real. tends_real_real (%x::hollight.real. x) x0 x0"
  by (import hollight LIM_X)

lemma LIM_UNIQ: "ALL (f::hollight.real => hollight.real) (l::hollight.real)
   (m::hollight.real) x::hollight.real.
   tends_real_real f l x & tends_real_real f m x --> l = m"
  by (import hollight LIM_UNIQ)

lemma LIM_EQUAL: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) x0::hollight.real.
   (ALL x::hollight.real. x ~= x0 --> f x = g x) -->
   tends_real_real f l x0 = tends_real_real g l x0"
  by (import hollight LIM_EQUAL)

lemma LIM_TRANSFORM: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (x0::hollight.real) l::hollight.real.
   tends_real_real (%x::hollight.real. real_sub (f x) (g x)) (real_of_num 0)
    x0 &
   tends_real_real g l x0 -->
   tends_real_real f l x0"
  by (import hollight LIM_TRANSFORM)

constdefs
  diffl :: "(hollight.real => hollight.real) => hollight.real => hollight.real => bool" 
  "diffl ==
%(u::hollight.real => hollight.real) (ua::hollight.real) ub::hollight.real.
   tends_real_real
    (%h::hollight.real. real_div (real_sub (u (real_add ub h)) (u ub)) h) ua
    (real_of_num 0)"

lemma DEF_diffl: "diffl =
(%(u::hollight.real => hollight.real) (ua::hollight.real) ub::hollight.real.
    tends_real_real
     (%h::hollight.real. real_div (real_sub (u (real_add ub h)) (u ub)) h)
     ua (real_of_num 0))"
  by (import hollight DEF_diffl)

constdefs
  contl :: "(hollight.real => hollight.real) => hollight.real => bool" 
  "contl ==
%(u::hollight.real => hollight.real) ua::hollight.real.
   tends_real_real (%h::hollight.real. u (real_add ua h)) (u ua)
    (real_of_num 0)"

lemma DEF_contl: "contl =
(%(u::hollight.real => hollight.real) ua::hollight.real.
    tends_real_real (%h::hollight.real. u (real_add ua h)) (u ua)
     (real_of_num 0))"
  by (import hollight DEF_contl)

constdefs
  differentiable :: "(hollight.real => hollight.real) => hollight.real => bool" 
  "differentiable ==
%(u::hollight.real => hollight.real) ua::hollight.real.
   EX l::hollight.real. diffl u l ua"

lemma DEF_differentiable: "differentiable =
(%(u::hollight.real => hollight.real) ua::hollight.real.
    EX l::hollight.real. diffl u l ua)"
  by (import hollight DEF_differentiable)

lemma DIFF_UNIQ: "ALL (f::hollight.real => hollight.real) (l::hollight.real)
   (m::hollight.real) x::hollight.real. diffl f l x & diffl f m x --> l = m"
  by (import hollight DIFF_UNIQ)

lemma DIFF_CONT: "ALL (f::hollight.real => hollight.real) (l::hollight.real) x::hollight.real.
   diffl f l x --> contl f x"
  by (import hollight DIFF_CONT)

lemma CONTL_LIM: "ALL (f::hollight.real => hollight.real) x::hollight.real.
   contl f x = tends_real_real f (f x) x"
  by (import hollight CONTL_LIM)

lemma CONT_X: "All (contl (%x::hollight.real. x))"
  by (import hollight CONT_X)

lemma CONT_CONST: "All (contl (%x::hollight.real. k::hollight.real))"
  by (import hollight CONT_CONST)

lemma CONT_ADD: "ALL x::hollight.real.
   contl (f::hollight.real => hollight.real) x &
   contl (g::hollight.real => hollight.real) x -->
   contl (%x::hollight.real. real_add (f x) (g x)) x"
  by (import hollight CONT_ADD)

lemma CONT_MUL: "ALL x::hollight.real.
   contl (f::hollight.real => hollight.real) x &
   contl (g::hollight.real => hollight.real) x -->
   contl (%x::hollight.real. real_mul (f x) (g x)) x"
  by (import hollight CONT_MUL)

lemma CONT_NEG: "ALL x::hollight.real.
   contl (f::hollight.real => hollight.real) x -->
   contl (%x::hollight.real. real_neg (f x)) x"
  by (import hollight CONT_NEG)

lemma CONT_INV: "ALL x::hollight.real.
   contl (f::hollight.real => hollight.real) x & f x ~= real_of_num 0 -->
   contl (%x::hollight.real. real_inv (f x)) x"
  by (import hollight CONT_INV)

lemma CONT_SUB: "ALL x::hollight.real.
   contl (f::hollight.real => hollight.real) x &
   contl (g::hollight.real => hollight.real) x -->
   contl (%x::hollight.real. real_sub (f x) (g x)) x"
  by (import hollight CONT_SUB)

lemma CONT_DIV: "ALL x::hollight.real.
   contl (f::hollight.real => hollight.real) x &
   contl (g::hollight.real => hollight.real) x & g x ~= real_of_num 0 -->
   contl (%x::hollight.real. real_div (f x) (g x)) x"
  by (import hollight CONT_DIV)

lemma CONT_COMPOSE: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   x::hollight.real.
   contl f x & contl g (f x) --> contl (%x::hollight.real. g (f x)) x"
  by (import hollight CONT_COMPOSE)

lemma IVT: "ALL (f::hollight.real => hollight.real) (a::hollight.real)
   (b::hollight.real) y::hollight.real.
   real_le a b &
   (real_le (f a) y & real_le y (f b)) &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) -->
   (EX x::hollight.real. real_le a x & real_le x b & f x = y)"
  by (import hollight IVT)

lemma IVT2: "ALL (f::hollight.real => hollight.real) (a::hollight.real)
   (b::hollight.real) y::hollight.real.
   real_le a b &
   (real_le (f b) y & real_le y (f a)) &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) -->
   (EX x::hollight.real. real_le a x & real_le x b & f x = y)"
  by (import hollight IVT2)

lemma DIFF_CONST: "ALL k::hollight.real. All (diffl (%x::hollight.real. k) (real_of_num 0))"
  by (import hollight DIFF_CONST)

lemma DIFF_ADD: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) (m::hollight.real) x::hollight.real.
   diffl f l x & diffl g m x -->
   diffl (%x::hollight.real. real_add (f x) (g x)) (real_add l m) x"
  by (import hollight DIFF_ADD)

lemma DIFF_MUL: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) (m::hollight.real) x::hollight.real.
   diffl f l x & diffl g m x -->
   diffl (%x::hollight.real. real_mul (f x) (g x))
    (real_add (real_mul l (g x)) (real_mul m (f x))) x"
  by (import hollight DIFF_MUL)

lemma DIFF_CMUL: "ALL (f::hollight.real => hollight.real) (c::hollight.real)
   (l::hollight.real) x::hollight.real.
   diffl f l x -->
   diffl (%x::hollight.real. real_mul c (f x)) (real_mul c l) x"
  by (import hollight DIFF_CMUL)

lemma DIFF_NEG: "ALL (f::hollight.real => hollight.real) (l::hollight.real) x::hollight.real.
   diffl f l x --> diffl (%x::hollight.real. real_neg (f x)) (real_neg l) x"
  by (import hollight DIFF_NEG)

lemma DIFF_SUB: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) (m::hollight.real) x::hollight.real.
   diffl f l x & diffl g m x -->
   diffl (%x::hollight.real. real_sub (f x) (g x)) (real_sub l m) x"
  by (import hollight DIFF_SUB)

lemma DIFF_CARAT: "ALL (f::hollight.real => hollight.real) (l::hollight.real) x::hollight.real.
   diffl f l x =
   (EX xa::hollight.real => hollight.real.
       (ALL z::hollight.real.
           real_sub (f z) (f x) = real_mul (xa z) (real_sub z x)) &
       contl xa x & xa x = l)"
  by (import hollight DIFF_CARAT)

lemma DIFF_CHAIN: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) (m::hollight.real) x::hollight.real.
   diffl f l (g x) & diffl g m x -->
   diffl (%x::hollight.real. f (g x)) (real_mul l m) x"
  by (import hollight DIFF_CHAIN)

lemma DIFF_X: "All (diffl (%x::hollight.real. x) (real_of_num (NUMERAL_BIT1 0)))"
  by (import hollight DIFF_X)

lemma DIFF_POW: "ALL (n::nat) x::hollight.real.
   diffl (%x::hollight.real. real_pow x n)
    (real_mul (real_of_num n) (real_pow x (n - NUMERAL_BIT1 0))) x"
  by (import hollight DIFF_POW)

lemma DIFF_XM1: "ALL x::hollight.real.
   x ~= real_of_num 0 -->
   diffl real_inv
    (real_neg (real_pow (real_inv x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) x"
  by (import hollight DIFF_XM1)

lemma DIFF_INV: "ALL (f::hollight.real => hollight.real) (l::hollight.real) x::hollight.real.
   diffl f l x & f x ~= real_of_num 0 -->
   diffl (%x::hollight.real. real_inv (f x))
    (real_neg (real_div l (real_pow (f x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    x"
  by (import hollight DIFF_INV)

lemma DIFF_DIV: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) m::hollight.real.
   diffl f l (x::hollight.real) & diffl g m x & g x ~= real_of_num 0 -->
   diffl (%x::hollight.real. real_div (f x) (g x))
    (real_div (real_sub (real_mul l (g x)) (real_mul m (f x)))
      (real_pow (g x) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
    x"
  by (import hollight DIFF_DIV)

lemma DIFF_SUM: "ALL (f::nat => hollight.real => hollight.real)
   (f'::nat => hollight.real => hollight.real) (m::nat) (n::nat)
   x::hollight.real.
   (ALL r::nat. <= m r & < r (m + n) --> diffl (f r) (f' r x) x) -->
   diffl (%x::hollight.real. psum (m, n) (%n::nat. f n x))
    (psum (m, n) (%r::nat. f' r x)) x"
  by (import hollight DIFF_SUM)

lemma CONT_BOUNDED: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_le a b &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) -->
   (EX M::hollight.real.
       ALL x::hollight.real. real_le a x & real_le x b --> real_le (f x) M)"
  by (import hollight CONT_BOUNDED)

lemma CONT_BOUNDED_ABS: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) -->
   (EX M::hollight.real.
       ALL x::hollight.real.
          real_le a x & real_le x b --> real_le (real_abs (f x)) M)"
  by (import hollight CONT_BOUNDED_ABS)

lemma CONT_HASSUP: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_le a b &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) -->
   (EX M::hollight.real.
       (ALL x::hollight.real.
           real_le a x & real_le x b --> real_le (f x) M) &
       (ALL N::hollight.real.
           real_lt N M -->
           (EX x::hollight.real.
               real_le a x & real_le x b & real_lt N (f x))))"
  by (import hollight CONT_HASSUP)

lemma CONT_ATTAINS: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_le a b &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) -->
   (EX x::hollight.real.
       (ALL xa::hollight.real.
           real_le a xa & real_le xa b --> real_le (f xa) x) &
       (EX xa::hollight.real. real_le a xa & real_le xa b & f xa = x))"
  by (import hollight CONT_ATTAINS)

lemma CONT_ATTAINS2: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_le a b &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) -->
   (EX M::hollight.real.
       (ALL x::hollight.real.
           real_le a x & real_le x b --> real_le M (f x)) &
       (EX x::hollight.real. real_le a x & real_le x b & f x = M))"
  by (import hollight CONT_ATTAINS2)

lemma CONT_ATTAINS_ALL: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_le a b &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) -->
   (EX (L::hollight.real) M::hollight.real.
       (ALL x::hollight.real.
           real_le a x & real_le x b -->
           real_le L (f x) & real_le (f x) M) &
       (ALL y::hollight.real.
           real_le L y & real_le y M -->
           (EX x::hollight.real. real_le a x & real_le x b & f x = y)))"
  by (import hollight CONT_ATTAINS_ALL)

lemma DIFF_LINC: "ALL (f::hollight.real => hollight.real) (x::hollight.real) l::hollight.real.
   diffl f l x & real_lt (real_of_num 0) l -->
   (EX d::hollight.real.
       real_lt (real_of_num 0) d &
       (ALL h::hollight.real.
           real_lt (real_of_num 0) h & real_lt h d -->
           real_lt (f x) (f (real_add x h))))"
  by (import hollight DIFF_LINC)

lemma DIFF_LDEC: "ALL (f::hollight.real => hollight.real) (x::hollight.real) l::hollight.real.
   diffl f l x & real_lt l (real_of_num 0) -->
   (EX d::hollight.real.
       real_lt (real_of_num 0) d &
       (ALL h::hollight.real.
           real_lt (real_of_num 0) h & real_lt h d -->
           real_lt (f x) (f (real_sub x h))))"
  by (import hollight DIFF_LDEC)

lemma DIFF_LMAX: "ALL (f::hollight.real => hollight.real) (x::hollight.real) l::hollight.real.
   diffl f l x &
   (EX d::hollight.real.
       real_lt (real_of_num 0) d &
       (ALL y::hollight.real.
           real_lt (real_abs (real_sub x y)) d --> real_le (f y) (f x))) -->
   l = real_of_num 0"
  by (import hollight DIFF_LMAX)

lemma DIFF_LMIN: "ALL (f::hollight.real => hollight.real) (x::hollight.real) l::hollight.real.
   diffl f l x &
   (EX d::hollight.real.
       real_lt (real_of_num 0) d &
       (ALL y::hollight.real.
           real_lt (real_abs (real_sub x y)) d --> real_le (f x) (f y))) -->
   l = real_of_num 0"
  by (import hollight DIFF_LMIN)

lemma DIFF_LCONST: "ALL (f::hollight.real => hollight.real) (x::hollight.real) l::hollight.real.
   diffl f l x &
   (EX d::hollight.real.
       real_lt (real_of_num 0) d &
       (ALL y::hollight.real.
           real_lt (real_abs (real_sub x y)) d --> f y = f x)) -->
   l = real_of_num 0"
  by (import hollight DIFF_LCONST)

lemma INTERVAL_LEMMA_LT: "ALL (a::hollight.real) (b::hollight.real) x::hollight.real.
   real_lt a x & real_lt x b -->
   (EX xa::hollight.real.
       real_lt (real_of_num 0) xa &
       (ALL xb::hollight.real.
           real_lt (real_abs (real_sub x xb)) xa -->
           real_lt a xb & real_lt xb b))"
  by (import hollight INTERVAL_LEMMA_LT)

lemma INTERVAL_LEMMA: "ALL (a::hollight.real) (b::hollight.real) x::hollight.real.
   real_lt a x & real_lt x b -->
   (EX xa::hollight.real.
       real_lt (real_of_num 0) xa &
       (ALL y::hollight.real.
           real_lt (real_abs (real_sub x y)) xa -->
           real_le a y & real_le y b))"
  by (import hollight INTERVAL_LEMMA)

lemma ROLLE: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_lt a b &
   f a = f b &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) &
   (ALL x::hollight.real.
       real_lt a x & real_lt x b --> differentiable f x) -->
   (EX z::hollight.real.
       real_lt a z & real_lt z b & diffl f (real_of_num 0) z)"
  by (import hollight ROLLE)

lemma MVT_LEMMA: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_sub (f a)
    (real_mul (real_div (real_sub (f b) (f a)) (real_sub b a)) a) =
   real_sub (f b)
    (real_mul (real_div (real_sub (f b) (f a)) (real_sub b a)) b)"
  by (import hollight MVT_LEMMA)

lemma MVT: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_lt a b &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) &
   (ALL x::hollight.real.
       real_lt a x & real_lt x b --> differentiable f x) -->
   (EX (l::hollight.real) z::hollight.real.
       real_lt a z &
       real_lt z b &
       diffl f l z & real_sub (f b) (f a) = real_mul (real_sub b a) l)"
  by (import hollight MVT)

lemma MVT_ALT: "ALL (f::hollight.real => hollight.real) (f'::hollight.real => hollight.real)
   (a::hollight.real) b::hollight.real.
   real_lt a b &
   (ALL x::hollight.real.
       real_le a x & real_le x b --> diffl f (f' x) x) -->
   (EX z::hollight.real.
       real_lt a z &
       real_lt z b & real_sub (f b) (f a) = real_mul (real_sub b a) (f' z))"
  by (import hollight MVT_ALT)

lemma DIFF_ISCONST_END: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_lt a b &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) &
   (ALL x::hollight.real.
       real_lt a x & real_lt x b --> diffl f (real_of_num 0) x) -->
   f b = f a"
  by (import hollight DIFF_ISCONST_END)

lemma DIFF_ISCONST: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_lt a b &
   (ALL x::hollight.real. real_le a x & real_le x b --> contl f x) &
   (ALL x::hollight.real.
       real_lt a x & real_lt x b --> diffl f (real_of_num 0) x) -->
   (ALL x::hollight.real. real_le a x & real_le x b --> f x = f a)"
  by (import hollight DIFF_ISCONST)

lemma DIFF_ISCONST_END_SIMPLE: "ALL (f::hollight.real => hollight.real) (a::hollight.real) b::hollight.real.
   real_lt a b &
   (ALL x::hollight.real.
       real_le a x & real_le x b --> diffl f (real_of_num 0) x) -->
   f b = f a"
  by (import hollight DIFF_ISCONST_END_SIMPLE)

lemma DIFF_ISCONST_ALL: "ALL (x::hollight.real => hollight.real) (xa::hollight.real)
   xb::hollight.real. All (diffl x (real_of_num 0)) --> x xa = x xb"
  by (import hollight DIFF_ISCONST_ALL)

lemma INTERVAL_ABS: "ALL (x::hollight.real) (z::hollight.real) d::hollight.real.
   (real_le (real_sub x d) z & real_le z (real_add x d)) =
   real_le (real_abs (real_sub z x)) d"
  by (import hollight INTERVAL_ABS)

lemma CONT_INJ_LEMMA: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (x::hollight.real) d::hollight.real.
   real_lt (real_of_num 0) d &
   (ALL z::hollight.real.
       real_le (real_abs (real_sub z x)) d --> g (f z) = z) &
   (ALL z::hollight.real.
       real_le (real_abs (real_sub z x)) d --> contl f z) -->
   ~ (ALL z::hollight.real.
         real_le (real_abs (real_sub z x)) d --> real_le (f z) (f x))"
  by (import hollight CONT_INJ_LEMMA)

lemma CONT_INJ_LEMMA2: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (x::hollight.real) d::hollight.real.
   real_lt (real_of_num 0) d &
   (ALL z::hollight.real.
       real_le (real_abs (real_sub z x)) d --> g (f z) = z) &
   (ALL z::hollight.real.
       real_le (real_abs (real_sub z x)) d --> contl f z) -->
   ~ (ALL z::hollight.real.
         real_le (real_abs (real_sub z x)) d --> real_le (f x) (f z))"
  by (import hollight CONT_INJ_LEMMA2)

lemma CONT_INJ_RANGE: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (x::hollight.real) d::hollight.real.
   real_lt (real_of_num 0) d &
   (ALL z::hollight.real.
       real_le (real_abs (real_sub z x)) d --> g (f z) = z) &
   (ALL z::hollight.real.
       real_le (real_abs (real_sub z x)) d --> contl f z) -->
   (EX e::hollight.real.
       real_lt (real_of_num 0) e &
       (ALL y::hollight.real.
           real_le (real_abs (real_sub y (f x))) e -->
           (EX z::hollight.real.
               real_le (real_abs (real_sub z x)) d & f z = y)))"
  by (import hollight CONT_INJ_RANGE)

lemma CONT_INVERSE: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (x::hollight.real) d::hollight.real.
   real_lt (real_of_num 0) d &
   (ALL z::hollight.real.
       real_le (real_abs (real_sub z x)) d --> g (f z) = z) &
   (ALL z::hollight.real.
       real_le (real_abs (real_sub z x)) d --> contl f z) -->
   contl g (f x)"
  by (import hollight CONT_INVERSE)

lemma DIFF_INVERSE: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) (x::hollight.real) d::hollight.real.
   real_lt (real_of_num 0) d &
   (ALL z::hollight.real.
       real_le (real_abs (real_sub z x)) d --> g (f z) = z) &
   (ALL z::hollight.real.
       real_le (real_abs (real_sub z x)) d --> contl f z) &
   diffl f l x & l ~= real_of_num 0 -->
   diffl g (real_inv l) (f x)"
  by (import hollight DIFF_INVERSE)

lemma DIFF_INVERSE_LT: "ALL (f::hollight.real => hollight.real) (g::hollight.real => hollight.real)
   (l::hollight.real) (x::hollight.real) d::hollight.real.
   real_lt (real_of_num 0) d &
   (ALL z::hollight.real.
       real_lt (real_abs (real_sub z x)) d --> g (f z) = z) &
   (ALL z::hollight.real.
       real_lt (real_abs (real_sub z x)) d --> contl f z) &
   diffl f l x & l ~= real_of_num 0 -->
   diffl g (real_inv l) (f x)"
  by (import hollight DIFF_INVERSE_LT)

lemma IVT_DERIVATIVE_0: "ALL (f::hollight.real => hollight.real) (f'::hollight.real => hollight.real)
   (a::hollight.real) b::hollight.real.
   real_le a b &
   (ALL x::hollight.real. real_le a x & real_le x b --> diffl f (f' x) x) &
   hollight.real_gt (f' a) (real_of_num 0) &
   real_lt (f' b) (real_of_num 0) -->
   (EX z::hollight.real. real_lt a z & real_lt z b & f' z = real_of_num 0)"
  by (import hollight IVT_DERIVATIVE_0)

lemma IVT_DERIVATIVE_POS: "ALL (x::hollight.real => hollight.real) (xa::hollight.real => hollight.real)
   (xb::hollight.real) (xc::hollight.real) xd::hollight.real.
   real_le xb xc &
   (ALL xd::hollight.real.
       real_le xb xd & real_le xd xc --> diffl x (xa xd) xd) &
   hollight.real_gt (xa xb) xd & real_lt (xa xc) xd -->
   (EX z::hollight.real. real_lt xb z & real_lt z xc & xa z = xd)"
  by (import hollight IVT_DERIVATIVE_POS)

lemma IVT_DERIVATIVE_NEG: "ALL (x::hollight.real => hollight.real) (xa::hollight.real => hollight.real)
   (xb::hollight.real) (xc::hollight.real) xd::hollight.real.
   real_le xb xc &
   (ALL xd::hollight.real.
       real_le xb xd & real_le xd xc --> diffl x (xa xd) xd) &
   real_lt (xa xb) xd & hollight.real_gt (xa xc) xd -->
   (EX z::hollight.real. real_lt xb z & real_lt z xc & xa z = xd)"
  by (import hollight IVT_DERIVATIVE_NEG)

lemma SEQ_CONT_UNIFORM: "ALL (s::nat => hollight.real => hollight.real)
   (f::hollight.real => hollight.real) x0::hollight.real.
   (ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX (N::nat) d::hollight.real.
           real_lt (real_of_num 0) d &
           (ALL (x::hollight.real) n::nat.
               real_lt (real_abs (real_sub x x0)) d & >= n N -->
               real_lt (real_abs (real_sub (s n x) (f x))) e))) &
   (EX N::nat. ALL n::nat. >= n N --> contl (s n) x0) -->
   contl f x0"
  by (import hollight SEQ_CONT_UNIFORM)

lemma SER_COMPARA_UNIFORM: "ALL (s::hollight.real => nat => hollight.real) (x0::hollight.real)
   g::nat => hollight.real.
   (EX (N::nat) d::hollight.real.
       real_lt (real_of_num 0) d &
       (ALL (n::nat) x::hollight.real.
           real_lt (real_abs (real_sub x x0)) d & >= n N -->
           real_le (real_abs (s x n)) (g n))) &
   summable g -->
   (EX (f::hollight.real => hollight.real) d::hollight.real.
       real_lt (real_of_num 0) d &
       (ALL e::hollight.real.
           real_lt (real_of_num 0) e -->
           (EX N::nat.
               ALL (x::hollight.real) n::nat.
                  real_lt (real_abs (real_sub x x0)) d & >= n N -->
                  real_lt (real_abs (real_sub (psum (0, n) (s x)) (f x)))
                   e)))"
  by (import hollight SER_COMPARA_UNIFORM)

lemma SER_COMPARA_UNIFORM_WEAK: "ALL (s::hollight.real => nat => hollight.real) (x0::hollight.real)
   g::nat => hollight.real.
   (EX (N::nat) d::hollight.real.
       real_lt (real_of_num 0) d &
       (ALL (n::nat) x::hollight.real.
           real_lt (real_abs (real_sub x x0)) d & >= n N -->
           real_le (real_abs (s x n)) (g n))) &
   summable g -->
   (EX f::hollight.real => hollight.real.
       ALL e::hollight.real.
          real_lt (real_of_num 0) e -->
          (EX (N::nat) d::hollight.real.
              real_lt (real_of_num 0) d &
              (ALL (x::hollight.real) n::nat.
                  real_lt (real_abs (real_sub x x0)) d & >= n N -->
                  real_lt (real_abs (real_sub (psum (0, n) (s x)) (f x)))
                   e)))"
  by (import hollight SER_COMPARA_UNIFORM_WEAK)

lemma POWDIFF_LEMMA: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   psum (0, Suc n)
    (%p::nat. real_mul (real_pow x p) (real_pow y (Suc n - p))) =
   real_mul y
    (psum (0, Suc n)
      (%p::nat. real_mul (real_pow x p) (real_pow y (n - p))))"
  by (import hollight POWDIFF_LEMMA)

lemma POWDIFF: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   real_sub (real_pow x (Suc n)) (real_pow y (Suc n)) =
   real_mul (real_sub x y)
    (psum (0, Suc n)
      (%p::nat. real_mul (real_pow x p) (real_pow y (n - p))))"
  by (import hollight POWDIFF)

lemma POWREV: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   psum (0, Suc n)
    (%xa::nat. real_mul (real_pow x xa) (real_pow y (n - xa))) =
   psum (0, Suc n)
    (%xa::nat. real_mul (real_pow x (n - xa)) (real_pow y xa))"
  by (import hollight POWREV)

lemma POWSER_INSIDEA: "ALL (f::nat => hollight.real) (x::hollight.real) z::hollight.real.
   summable (%n::nat. real_mul (f n) (real_pow x n)) &
   real_lt (real_abs z) (real_abs x) -->
   summable (%n::nat. real_mul (real_abs (f n)) (real_pow z n))"
  by (import hollight POWSER_INSIDEA)

lemma POWSER_INSIDE: "ALL (f::nat => hollight.real) (x::hollight.real) z::hollight.real.
   summable (%n::nat. real_mul (f n) (real_pow x n)) &
   real_lt (real_abs z) (real_abs x) -->
   summable (%n::nat. real_mul (f n) (real_pow z n))"
  by (import hollight POWSER_INSIDE)

constdefs
  diffs :: "(nat => hollight.real) => nat => hollight.real" 
  "diffs ==
%(u::nat => hollight.real) n::nat.
   real_mul (real_of_num (Suc n)) (u (Suc n))"

lemma DEF_diffs: "diffs =
(%(u::nat => hollight.real) n::nat.
    real_mul (real_of_num (Suc n)) (u (Suc n)))"
  by (import hollight DEF_diffs)

lemma DIFFS_NEG: "ALL c::nat => hollight.real.
   diffs (%n::nat. real_neg (c n)) = (%x::nat. real_neg (diffs c x))"
  by (import hollight DIFFS_NEG)

lemma DIFFS_LEMMA: "ALL (n::nat) (c::nat => hollight.real) x::hollight.real.
   psum (0, n) (%n::nat. real_mul (diffs c n) (real_pow x n)) =
   real_add
    (psum (0, n)
      (%n::nat.
          real_mul (real_of_num n)
           (real_mul (c n) (real_pow x (n - NUMERAL_BIT1 0)))))
    (real_mul (real_of_num n)
      (real_mul (c n) (real_pow x (n - NUMERAL_BIT1 0))))"
  by (import hollight DIFFS_LEMMA)

lemma DIFFS_LEMMA2: "ALL (n::nat) (c::nat => hollight.real) x::hollight.real.
   psum (0, n)
    (%n::nat.
        real_mul (real_of_num n)
         (real_mul (c n) (real_pow x (n - NUMERAL_BIT1 0)))) =
   real_sub (psum (0, n) (%n::nat. real_mul (diffs c n) (real_pow x n)))
    (real_mul (real_of_num n)
      (real_mul (c n) (real_pow x (n - NUMERAL_BIT1 0))))"
  by (import hollight DIFFS_LEMMA2)

lemma DIFFS_EQUIV: "ALL (c::nat => hollight.real) x::hollight.real.
   summable (%n::nat. real_mul (diffs c n) (real_pow x n)) -->
   sums
    (%n::nat.
        real_mul (real_of_num n)
         (real_mul (c n) (real_pow x (n - NUMERAL_BIT1 0))))
    (suminf (%n::nat. real_mul (diffs c n) (real_pow x n)))"
  by (import hollight DIFFS_EQUIV)

lemma TERMDIFF_LEMMA1: "ALL (m::nat) (z::hollight.real) h::hollight.real.
   psum (0, m)
    (%p::nat.
        real_sub (real_mul (real_pow (real_add z h) (m - p)) (real_pow z p))
         (real_pow z m)) =
   psum (0, m)
    (%p::nat.
        real_mul (real_pow z p)
         (real_sub (real_pow (real_add z h) (m - p)) (real_pow z (m - p))))"
  by (import hollight TERMDIFF_LEMMA1)

lemma TERMDIFF_LEMMA2: "ALL (z::hollight.real) h::hollight.real.
   h ~= real_of_num 0 -->
   real_sub
    (real_div (real_sub (real_pow (real_add z h) (n::nat)) (real_pow z n))
      h)
    (real_mul (real_of_num n) (real_pow z (n - NUMERAL_BIT1 0))) =
   real_mul h
    (psum (0, n - NUMERAL_BIT1 0)
      (%p::nat.
          real_mul (real_pow z p)
           (psum (0, n - NUMERAL_BIT1 0 - p)
             (%q::nat.
                 real_mul (real_pow (real_add z h) q)
                  (real_pow z
                    (n - NUMERAL_BIT0 (NUMERAL_BIT1 0) - p - q))))))"
  by (import hollight TERMDIFF_LEMMA2)

lemma TERMDIFF_LEMMA3: "ALL (z::hollight.real) (h::hollight.real) (n::nat) K::hollight.real.
   h ~= real_of_num 0 &
   real_le (real_abs z) K & real_le (real_abs (real_add z h)) K -->
   real_le
    (real_abs
      (real_sub
        (real_div (real_sub (real_pow (real_add z h) n) (real_pow z n)) h)
        (real_mul (real_of_num n) (real_pow z (n - NUMERAL_BIT1 0)))))
    (real_mul (real_of_num n)
      (real_mul (real_of_num (n - NUMERAL_BIT1 0))
        (real_mul (real_pow K (n - NUMERAL_BIT0 (NUMERAL_BIT1 0)))
          (real_abs h))))"
  by (import hollight TERMDIFF_LEMMA3)

lemma TERMDIFF_LEMMA4: "ALL (f::hollight.real => hollight.real) (K::hollight.real) k::hollight.real.
   real_lt (real_of_num 0) k &
   (ALL h::hollight.real.
       real_lt (real_of_num 0) (real_abs h) & real_lt (real_abs h) k -->
       real_le (real_abs (f h)) (real_mul K (real_abs h))) -->
   tends_real_real f (real_of_num 0) (real_of_num 0)"
  by (import hollight TERMDIFF_LEMMA4)

lemma TERMDIFF_LEMMA5: "ALL (f::nat => hollight.real) (g::hollight.real => nat => hollight.real)
   k::hollight.real.
   real_lt (real_of_num 0) k &
   summable f &
   (ALL h::hollight.real.
       real_lt (real_of_num 0) (real_abs h) & real_lt (real_abs h) k -->
       (ALL n::nat.
           real_le (real_abs (g h n)) (real_mul (f n) (real_abs h)))) -->
   tends_real_real (%h::hollight.real. suminf (g h)) (real_of_num 0)
    (real_of_num 0)"
  by (import hollight TERMDIFF_LEMMA5)

lemma TERMDIFF: "ALL (c::nat => hollight.real) K::hollight.real.
   summable (%n::nat. real_mul (c n) (real_pow K n)) &
   summable (%n::nat. real_mul (diffs c n) (real_pow K n)) &
   summable (%n::nat. real_mul (diffs (diffs c) n) (real_pow K n)) &
   real_lt (real_abs (x::hollight.real)) (real_abs K) -->
   diffl
    (%x::hollight.real. suminf (%n::nat. real_mul (c n) (real_pow x n)))
    (suminf (%n::nat. real_mul (diffs c n) (real_pow x n))) x"
  by (import hollight TERMDIFF)

lemma SEQ_NPOW: "ALL x::hollight.real.
   real_lt (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   tends_num_real (%n::nat. real_mul (real_of_num n) (real_pow x n))
    (real_of_num 0)"
  by (import hollight SEQ_NPOW)

lemma TERMDIFF_CONVERGES: "ALL K::hollight.real.
   (ALL x::hollight.real.
       real_lt (real_abs x) K -->
       summable
        (%n::nat.
            real_mul ((c::nat => hollight.real) n) (real_pow x n))) -->
   (ALL x::hollight.real.
       real_lt (real_abs x) K -->
       summable (%n::nat. real_mul (diffs c n) (real_pow x n)))"
  by (import hollight TERMDIFF_CONVERGES)

lemma TERMDIFF_STRONG: "ALL (c::nat => hollight.real) (K::hollight.real) x::hollight.real.
   summable (%n::nat. real_mul (c n) (real_pow K n)) &
   real_lt (real_abs x) (real_abs K) -->
   diffl
    (%x::hollight.real. suminf (%n::nat. real_mul (c n) (real_pow x n)))
    (suminf (%n::nat. real_mul (diffs c n) (real_pow x n))) x"
  by (import hollight TERMDIFF_STRONG)

lemma POWSER_0: "ALL a::nat => hollight.real.
   sums (%n::nat. real_mul (a n) (real_pow (real_of_num 0) n)) (a 0)"
  by (import hollight POWSER_0)

lemma POWSER_LIMIT_0: "ALL (f::hollight.real => hollight.real) (a::nat => hollight.real)
   s::hollight.real.
   real_lt (real_of_num 0) s &
   (ALL x::hollight.real.
       real_lt (real_abs x) s -->
       sums (%n::nat. real_mul (a n) (real_pow x n)) (f x)) -->
   tends_real_real f (a 0) (real_of_num 0)"
  by (import hollight POWSER_LIMIT_0)

lemma POWSER_LIMIT_0_STRONG: "ALL (f::hollight.real => hollight.real) (a::nat => hollight.real)
   s::hollight.real.
   real_lt (real_of_num 0) s &
   (ALL x::hollight.real.
       real_lt (real_of_num 0) (real_abs x) & real_lt (real_abs x) s -->
       sums (%n::nat. real_mul (a n) (real_pow x n)) (f x)) -->
   tends_real_real f (a 0) (real_of_num 0)"
  by (import hollight POWSER_LIMIT_0_STRONG)

lemma POWSER_EQUAL_0: "ALL (f::hollight.real => hollight.real) (a::nat => hollight.real)
   (b::nat => hollight.real) P::hollight.real => bool.
   (ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX x::hollight.real.
           P x &
           real_lt (real_of_num 0) (real_abs x) & real_lt (real_abs x) e)) &
   (ALL x::hollight.real.
       real_lt (real_of_num 0) (real_abs x) & P x -->
       sums (%n::nat. real_mul (a n) (real_pow x n)) (f x) &
       sums (%n::nat. real_mul (b n) (real_pow x n)) (f x)) -->
   a 0 = b 0"
  by (import hollight POWSER_EQUAL_0)

lemma POWSER_EQUAL: "ALL (f::hollight.real => hollight.real) (a::nat => hollight.real)
   (b::nat => hollight.real) P::hollight.real => bool.
   (ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX x::hollight.real.
           P x &
           real_lt (real_of_num 0) (real_abs x) & real_lt (real_abs x) e)) &
   (ALL x::hollight.real.
       P x -->
       sums (%n::nat. real_mul (a n) (real_pow x n)) (f x) &
       sums (%n::nat. real_mul (b n) (real_pow x n)) (f x)) -->
   a = b"
  by (import hollight POWSER_EQUAL)

lemma MULT_DIV_2: "ALL n::nat.
   DIV (NUMERAL_BIT0 (NUMERAL_BIT1 0) * n) (NUMERAL_BIT0 (NUMERAL_BIT1 0)) =
   n"
  by (import hollight MULT_DIV_2)

lemma EVEN_DIV2: "ALL n::nat.
   ~ EVEN n -->
   DIV (Suc n) (NUMERAL_BIT0 (NUMERAL_BIT1 0)) =
   Suc (DIV (n - NUMERAL_BIT1 0) (NUMERAL_BIT0 (NUMERAL_BIT1 0)))"
  by (import hollight EVEN_DIV2)

lemma POW_ZERO: "ALL (n::nat) x::hollight.real.
   real_pow x n = real_of_num 0 --> x = real_of_num 0"
  by (import hollight POW_ZERO)

lemma POW_ZERO_EQ: "ALL (n::nat) x::hollight.real.
   (real_pow x (Suc n) = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight POW_ZERO_EQ)

lemma POW_LT: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_lt x y -->
   real_lt (real_pow x (Suc n)) (real_pow y (Suc n))"
  by (import hollight POW_LT)

lemma POW_EQ: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x &
   real_le (real_of_num 0) y & real_pow x (Suc n) = real_pow y (Suc n) -->
   x = y"
  by (import hollight POW_EQ)

constdefs
  exp :: "hollight.real => hollight.real" 
  "exp ==
%u::hollight.real.
   suminf
    (%n::nat. real_mul (real_inv (real_of_num (FACT n))) (real_pow u n))"

lemma DEF_exp: "exp =
(%u::hollight.real.
    suminf
     (%n::nat. real_mul (real_inv (real_of_num (FACT n))) (real_pow u n)))"
  by (import hollight DEF_exp)

constdefs
  sin :: "hollight.real => hollight.real" 
  "sin ==
%u::hollight.real.
   suminf
    (%n::nat.
        real_mul
         (COND (EVEN n) (real_of_num 0)
           (real_div
             (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
               (DIV (n - NUMERAL_BIT1 0) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
             (real_of_num (FACT n))))
         (real_pow u n))"

lemma DEF_sin: "sin =
(%u::hollight.real.
    suminf
     (%n::nat.
         real_mul
          (COND (EVEN n) (real_of_num 0)
            (real_div
              (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
                (DIV (n - NUMERAL_BIT1 0) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
              (real_of_num (FACT n))))
          (real_pow u n)))"
  by (import hollight DEF_sin)

constdefs
  cos :: "hollight.real => hollight.real" 
  "cos ==
%u::hollight.real.
   suminf
    (%n::nat.
        real_mul
         (COND (EVEN n)
           (real_div
             (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
               (DIV n (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
             (real_of_num (FACT n)))
           (real_of_num 0))
         (real_pow u n))"

lemma DEF_cos: "cos =
(%u::hollight.real.
    suminf
     (%n::nat.
         real_mul
          (COND (EVEN n)
            (real_div
              (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
                (DIV n (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
              (real_of_num (FACT n)))
            (real_of_num 0))
          (real_pow u n)))"
  by (import hollight DEF_cos)

lemma REAL_EXP_CONVERGES: "ALL x::hollight.real.
   sums (%n::nat. real_mul (real_inv (real_of_num (FACT n))) (real_pow x n))
    (exp x)"
  by (import hollight REAL_EXP_CONVERGES)

lemma SIN_CONVERGES: "ALL x::hollight.real.
   sums
    (%n::nat.
        real_mul
         (COND (EVEN n) (real_of_num 0)
           (real_div
             (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
               (DIV (n - NUMERAL_BIT1 0) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
             (real_of_num (FACT n))))
         (real_pow x n))
    (sin x)"
  by (import hollight SIN_CONVERGES)

lemma COS_CONVERGES: "ALL x::hollight.real.
   sums
    (%n::nat.
        real_mul
         (COND (EVEN n)
           (real_div
             (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
               (DIV n (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
             (real_of_num (FACT n)))
           (real_of_num 0))
         (real_pow x n))
    (cos x)"
  by (import hollight COS_CONVERGES)

lemma REAL_EXP_FDIFF: "diffs (%n::nat. real_inv (real_of_num (FACT n))) =
(%n::nat. real_inv (real_of_num (FACT n)))"
  by (import hollight REAL_EXP_FDIFF)

lemma SIN_FDIFF: "diffs
 (%n::nat.
     COND (EVEN n) (real_of_num 0)
      (real_div
        (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
          (DIV (n - NUMERAL_BIT1 0) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
        (real_of_num (FACT n)))) =
(%n::nat.
    COND (EVEN n)
     (real_div
       (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
         (DIV n (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
       (real_of_num (FACT n)))
     (real_of_num 0))"
  by (import hollight SIN_FDIFF)

lemma COS_FDIFF: "diffs
 (%n::nat.
     COND (EVEN n)
      (real_div
        (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
          (DIV n (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
        (real_of_num (FACT n)))
      (real_of_num 0)) =
(%n::nat.
    real_neg
     (COND (EVEN n) (real_of_num 0)
       (real_div
         (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
           (DIV (n - NUMERAL_BIT1 0) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
         (real_of_num (FACT n)))))"
  by (import hollight COS_FDIFF)

lemma SIN_NEGLEMMA: "ALL x::hollight.real.
   real_neg (sin x) =
   suminf
    (%n::nat.
        real_neg
         (real_mul
           (COND (EVEN n) (real_of_num 0)
             (real_div
               (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
                 (DIV (n - NUMERAL_BIT1 0) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
               (real_of_num (FACT n))))
           (real_pow x n)))"
  by (import hollight SIN_NEGLEMMA)

lemma DIFF_EXP: "ALL x::hollight.real. diffl exp (exp x) x"
  by (import hollight DIFF_EXP)

lemma DIFF_SIN: "ALL x::hollight.real. diffl sin (cos x) x"
  by (import hollight DIFF_SIN)

lemma DIFF_COS: "ALL x::hollight.real. diffl cos (real_neg (sin x)) x"
  by (import hollight DIFF_COS)

lemma DIFF_COMPOSITE: "(diffl (f::hollight.real => hollight.real) (l::hollight.real)
  (x::hollight.real) &
 f x ~= real_of_num 0 -->
 diffl (%x::hollight.real. real_inv (f x))
  (real_neg (real_div l (real_pow (f x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
  x) &
(diffl f l x &
 diffl (g::hollight.real => hollight.real) (m::hollight.real) x &
 g x ~= real_of_num 0 -->
 diffl (%x::hollight.real. real_div (f x) (g x))
  (real_div (real_sub (real_mul l (g x)) (real_mul m (f x)))
    (real_pow (g x) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
  x) &
(diffl f l x & diffl g m x -->
 diffl (%x::hollight.real. real_add (f x) (g x)) (real_add l m) x) &
(diffl f l x & diffl g m x -->
 diffl (%x::hollight.real. real_mul (f x) (g x))
  (real_add (real_mul l (g x)) (real_mul m (f x))) x) &
(diffl f l x & diffl g m x -->
 diffl (%x::hollight.real. real_sub (f x) (g x)) (real_sub l m) x) &
(diffl f l x --> diffl (%x::hollight.real. real_neg (f x)) (real_neg l) x) &
(diffl g m x -->
 diffl (%x::hollight.real. real_pow (g x) (n::nat))
  (real_mul (real_mul (real_of_num n) (real_pow (g x) (n - NUMERAL_BIT1 0)))
    m)
  x) &
(diffl g m x -->
 diffl (%x::hollight.real. exp (g x)) (real_mul (exp (g x)) m) x) &
(diffl g m x -->
 diffl (%x::hollight.real. sin (g x)) (real_mul (cos (g x)) m) x) &
(diffl g m x -->
 diffl (%x::hollight.real. cos (g x)) (real_mul (real_neg (sin (g x))) m) x)"
  by (import hollight DIFF_COMPOSITE)

lemma REAL_EXP_0: "exp (real_of_num 0) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight REAL_EXP_0)

lemma REAL_EXP_LE_X: "ALL x::hollight.real.
   real_le (real_of_num 0) x -->
   real_le (real_add (real_of_num (NUMERAL_BIT1 0)) x) (exp x)"
  by (import hollight REAL_EXP_LE_X)

lemma REAL_EXP_LT_1: "ALL x::hollight.real.
   real_lt (real_of_num 0) x -->
   real_lt (real_of_num (NUMERAL_BIT1 0)) (exp x)"
  by (import hollight REAL_EXP_LT_1)

lemma REAL_EXP_ADD_MUL: "ALL (x::hollight.real) y::hollight.real.
   real_mul (exp (real_add x y)) (exp (real_neg x)) = exp y"
  by (import hollight REAL_EXP_ADD_MUL)

lemma REAL_EXP_NEG_MUL: "ALL x::hollight.real.
   real_mul (exp x) (exp (real_neg x)) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight REAL_EXP_NEG_MUL)

lemma REAL_EXP_NEG_MUL2: "ALL x::hollight.real.
   real_mul (exp (real_neg x)) (exp x) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight REAL_EXP_NEG_MUL2)

lemma REAL_EXP_NEG: "ALL x::hollight.real. exp (real_neg x) = real_inv (exp x)"
  by (import hollight REAL_EXP_NEG)

lemma REAL_EXP_ADD: "ALL (x::hollight.real) y::hollight.real.
   exp (real_add x y) = real_mul (exp x) (exp y)"
  by (import hollight REAL_EXP_ADD)

lemma REAL_EXP_POS_LE: "ALL x::hollight.real. real_le (real_of_num 0) (exp x)"
  by (import hollight REAL_EXP_POS_LE)

lemma REAL_EXP_NZ: "ALL x::hollight.real. exp x ~= real_of_num 0"
  by (import hollight REAL_EXP_NZ)

lemma REAL_EXP_POS_LT: "ALL x::hollight.real. real_lt (real_of_num 0) (exp x)"
  by (import hollight REAL_EXP_POS_LT)

lemma REAL_EXP_N: "ALL (n::nat) x::hollight.real.
   exp (real_mul (real_of_num n) x) = real_pow (exp x) n"
  by (import hollight REAL_EXP_N)

lemma REAL_EXP_SUB: "ALL (x::hollight.real) y::hollight.real.
   exp (real_sub x y) = real_div (exp x) (exp y)"
  by (import hollight REAL_EXP_SUB)

lemma REAL_EXP_MONO_IMP: "ALL (x::hollight.real) y::hollight.real.
   real_lt x y --> real_lt (exp x) (exp y)"
  by (import hollight REAL_EXP_MONO_IMP)

lemma REAL_EXP_MONO_LT: "ALL (x::hollight.real) y::hollight.real.
   real_lt (exp x) (exp y) = real_lt x y"
  by (import hollight REAL_EXP_MONO_LT)

lemma REAL_EXP_MONO_LE: "ALL (x::hollight.real) y::hollight.real.
   real_le (exp x) (exp y) = real_le x y"
  by (import hollight REAL_EXP_MONO_LE)

lemma REAL_EXP_INJ: "ALL (x::hollight.real) y::hollight.real. (exp x = exp y) = (x = y)"
  by (import hollight REAL_EXP_INJ)

lemma REAL_EXP_TOTAL_LEMMA: "ALL y::hollight.real.
   real_le (real_of_num (NUMERAL_BIT1 0)) y -->
   (EX x::hollight.real.
       real_le (real_of_num 0) x &
       real_le x (real_sub y (real_of_num (NUMERAL_BIT1 0))) & exp x = y)"
  by (import hollight REAL_EXP_TOTAL_LEMMA)

lemma REAL_EXP_TOTAL: "ALL y::hollight.real.
   real_lt (real_of_num 0) y --> (EX x::hollight.real. exp x = y)"
  by (import hollight REAL_EXP_TOTAL)

lemma REAL_EXP_BOUND_LEMMA: "ALL x::hollight.real.
   real_le (real_of_num 0) x &
   real_le x (real_inv (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) -->
   real_le (exp x)
    (real_add (real_of_num (NUMERAL_BIT1 0))
      (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) x))"
  by (import hollight REAL_EXP_BOUND_LEMMA)

constdefs
  ln :: "hollight.real => hollight.real" 
  "ln == %u::hollight.real. SOME ua::hollight.real. exp ua = u"

lemma DEF_ln: "ln = (%u::hollight.real. SOME ua::hollight.real. exp ua = u)"
  by (import hollight DEF_ln)

lemma LN_EXP: "ALL x::hollight.real. ln (exp x) = x"
  by (import hollight LN_EXP)

lemma REAL_EXP_LN: "ALL x::hollight.real. (exp (ln x) = x) = real_lt (real_of_num 0) x"
  by (import hollight REAL_EXP_LN)

lemma LN_MUL: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_lt (real_of_num 0) y -->
   ln (real_mul x y) = real_add (ln x) (ln y)"
  by (import hollight LN_MUL)

lemma LN_INJ: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_lt (real_of_num 0) y -->
   (ln x = ln y) = (x = y)"
  by (import hollight LN_INJ)

lemma LN_1: "ln (real_of_num (NUMERAL_BIT1 0)) = real_of_num 0"
  by (import hollight LN_1)

lemma LN_INV: "ALL x::hollight.real.
   real_lt (real_of_num 0) x --> ln (real_inv x) = real_neg (ln x)"
  by (import hollight LN_INV)

lemma LN_DIV: "ALL x::hollight.real.
   real_lt (real_of_num 0) x &
   real_lt (real_of_num 0) (y::hollight.real) -->
   ln (real_div x y) = real_sub (ln x) (ln y)"
  by (import hollight LN_DIV)

lemma LN_MONO_LT: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_lt (real_of_num 0) y -->
   real_lt (ln x) (ln y) = real_lt x y"
  by (import hollight LN_MONO_LT)

lemma LN_MONO_LE: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_lt (real_of_num 0) y -->
   real_le (ln x) (ln y) = real_le x y"
  by (import hollight LN_MONO_LE)

lemma LN_POW: "ALL (n::nat) x::hollight.real.
   real_lt (real_of_num 0) x -->
   ln (real_pow x n) = real_mul (real_of_num n) (ln x)"
  by (import hollight LN_POW)

lemma LN_LE: "ALL x::hollight.real.
   real_le (real_of_num 0) x -->
   real_le (ln (real_add (real_of_num (NUMERAL_BIT1 0)) x)) x"
  by (import hollight LN_LE)

lemma LN_LT_X: "ALL x::hollight.real. real_lt (real_of_num 0) x --> real_lt (ln x) x"
  by (import hollight LN_LT_X)

lemma LN_POS: "ALL x::hollight.real.
   real_le (real_of_num (NUMERAL_BIT1 0)) x -->
   real_le (real_of_num 0) (ln x)"
  by (import hollight LN_POS)

lemma LN_POS_LT: "ALL x::hollight.real.
   real_lt (real_of_num (NUMERAL_BIT1 0)) x -->
   real_lt (real_of_num 0) (ln x)"
  by (import hollight LN_POS_LT)

lemma DIFF_LN: "ALL x::hollight.real. real_lt (real_of_num 0) x --> diffl ln (real_inv x) x"
  by (import hollight DIFF_LN)

constdefs
  root :: "nat => hollight.real => hollight.real" 
  "root ==
%(u::nat) ua::hollight.real.
   SOME ub::hollight.real.
      (real_lt (real_of_num 0) ua --> real_lt (real_of_num 0) ub) &
      real_pow ub u = ua"

lemma DEF_root: "root =
(%(u::nat) ua::hollight.real.
    SOME ub::hollight.real.
       (real_lt (real_of_num 0) ua --> real_lt (real_of_num 0) ub) &
       real_pow ub u = ua)"
  by (import hollight DEF_root)

constdefs
  sqrt :: "hollight.real => hollight.real" 
  "sqrt ==
%u::hollight.real.
   SOME y::hollight.real.
      real_le (real_of_num 0) y &
      real_pow y (NUMERAL_BIT0 (NUMERAL_BIT1 0)) = u"

lemma DEF_sqrt: "sqrt =
(%u::hollight.real.
    SOME y::hollight.real.
       real_le (real_of_num 0) y &
       real_pow y (NUMERAL_BIT0 (NUMERAL_BIT1 0)) = u)"
  by (import hollight DEF_sqrt)

lemma sqrt: "sqrt (x::hollight.real) = root (NUMERAL_BIT0 (NUMERAL_BIT1 0)) x"
  by (import hollight sqrt)

lemma ROOT_LT_LEMMA: "ALL (n::nat) x::hollight.real.
   real_lt (real_of_num 0) x -->
   real_pow (exp (real_div (ln x) (real_of_num (Suc n)))) (Suc n) = x"
  by (import hollight ROOT_LT_LEMMA)

lemma ROOT_LN: "ALL x::hollight.real.
   real_lt (real_of_num 0) x -->
   (ALL n::nat.
       root (Suc n) x = exp (real_div (ln x) (real_of_num (Suc n))))"
  by (import hollight ROOT_LN)

lemma ROOT_0: "ALL n::nat. root (Suc n) (real_of_num 0) = real_of_num 0"
  by (import hollight ROOT_0)

lemma ROOT_1: "ALL n::nat.
   root (Suc n) (real_of_num (NUMERAL_BIT1 0)) =
   real_of_num (NUMERAL_BIT1 0)"
  by (import hollight ROOT_1)

lemma ROOT_POW_POS: "ALL (n::nat) x::hollight.real.
   real_le (real_of_num 0) x --> real_pow (root (Suc n) x) (Suc n) = x"
  by (import hollight ROOT_POW_POS)

lemma POW_ROOT_POS: "ALL (n::nat) x::hollight.real.
   real_le (real_of_num 0) x --> root (Suc n) (real_pow x (Suc n)) = x"
  by (import hollight POW_ROOT_POS)

lemma ROOT_POS_POSITIVE: "ALL (x::hollight.real) n::nat.
   real_le (real_of_num 0) x --> real_le (real_of_num 0) (root (Suc n) x)"
  by (import hollight ROOT_POS_POSITIVE)

lemma ROOT_POS_UNIQ: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x &
   real_le (real_of_num 0) y & real_pow y (Suc n) = x -->
   root (Suc n) x = y"
  by (import hollight ROOT_POS_UNIQ)

lemma ROOT_MUL: "ALL (n::nat) (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) y -->
   root (Suc n) (real_mul x y) = real_mul (root (Suc n) x) (root (Suc n) y)"
  by (import hollight ROOT_MUL)

lemma ROOT_INV: "ALL (n::nat) x::hollight.real.
   real_le (real_of_num 0) x -->
   root (Suc n) (real_inv x) = real_inv (root (Suc n) x)"
  by (import hollight ROOT_INV)

lemma ROOT_DIV: "ALL (x::nat) (xa::hollight.real) xb::hollight.real.
   real_le (real_of_num 0) xa & real_le (real_of_num 0) xb -->
   root (Suc x) (real_div xa xb) =
   real_div (root (Suc x) xa) (root (Suc x) xb)"
  by (import hollight ROOT_DIV)

lemma ROOT_MONO_LT: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_lt x y -->
   real_lt (root (Suc (n::nat)) x) (root (Suc n) y)"
  by (import hollight ROOT_MONO_LT)

lemma ROOT_MONO_LE: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_le x y -->
   real_le (root (Suc (n::nat)) x) (root (Suc n) y)"
  by (import hollight ROOT_MONO_LE)

lemma ROOT_MONO_LT_EQ: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) y -->
   real_lt (root (Suc (n::nat)) x) (root (Suc n) y) = real_lt x y"
  by (import hollight ROOT_MONO_LT_EQ)

lemma ROOT_MONO_LE_EQ: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) y -->
   real_le (root (Suc (n::nat)) x) (root (Suc n) y) = real_le x y"
  by (import hollight ROOT_MONO_LE_EQ)

lemma ROOT_INJ: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) xa -->
   (root (Suc (n::nat)) x = root (Suc n) xa) = (x = xa)"
  by (import hollight ROOT_INJ)

lemma SQRT_0: "sqrt (real_of_num 0) = real_of_num 0"
  by (import hollight SQRT_0)

lemma SQRT_1: "sqrt (real_of_num (NUMERAL_BIT1 0)) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight SQRT_1)

lemma SQRT_POS_LT: "ALL x::hollight.real.
   real_lt (real_of_num 0) x --> real_lt (real_of_num 0) (sqrt x)"
  by (import hollight SQRT_POS_LT)

lemma SQRT_POS_LE: "ALL x::hollight.real.
   real_le (real_of_num 0) x --> real_le (real_of_num 0) (sqrt x)"
  by (import hollight SQRT_POS_LE)

lemma SQRT_POW2: "ALL x::hollight.real.
   (real_pow (sqrt x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)) = x) =
   real_le (real_of_num 0) x"
  by (import hollight SQRT_POW2)

lemma SQRT_POW_2: "ALL x::hollight.real.
   real_le (real_of_num 0) x -->
   real_pow (sqrt x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)) = x"
  by (import hollight SQRT_POW_2)

lemma POW_2_SQRT: "real_le (real_of_num 0) (x::hollight.real) -->
sqrt (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0))) = x"
  by (import hollight POW_2_SQRT)

lemma SQRT_POS_UNIQ: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) x &
   real_le (real_of_num 0) xa &
   real_pow xa (NUMERAL_BIT0 (NUMERAL_BIT1 0)) = x -->
   sqrt x = xa"
  by (import hollight SQRT_POS_UNIQ)

lemma SQRT_MUL: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) xa -->
   sqrt (real_mul x xa) = real_mul (sqrt x) (sqrt xa)"
  by (import hollight SQRT_MUL)

lemma SQRT_INV: "ALL x::hollight.real.
   real_le (real_of_num 0) x --> sqrt (real_inv x) = real_inv (sqrt x)"
  by (import hollight SQRT_INV)

lemma SQRT_DIV: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) xa -->
   sqrt (real_div x xa) = real_div (sqrt x) (sqrt xa)"
  by (import hollight SQRT_DIV)

lemma SQRT_MONO_LT: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) x & real_lt x xa --> real_lt (sqrt x) (sqrt xa)"
  by (import hollight SQRT_MONO_LT)

lemma SQRT_MONO_LE: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) x & real_le x xa --> real_le (sqrt x) (sqrt xa)"
  by (import hollight SQRT_MONO_LE)

lemma SQRT_MONO_LT_EQ: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) xa -->
   real_lt (sqrt x) (sqrt xa) = real_lt x xa"
  by (import hollight SQRT_MONO_LT_EQ)

lemma SQRT_MONO_LE_EQ: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) xa -->
   real_le (sqrt x) (sqrt xa) = real_le x xa"
  by (import hollight SQRT_MONO_LE_EQ)

lemma SQRT_INJ: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) x & real_le (real_of_num 0) xa -->
   (sqrt x = sqrt xa) = (x = xa)"
  by (import hollight SQRT_INJ)

lemma SQRT_EVEN_POW2: "ALL n::nat.
   EVEN n -->
   sqrt (real_pow (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) n) =
   real_pow (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
    (DIV n (NUMERAL_BIT0 (NUMERAL_BIT1 0)))"
  by (import hollight SQRT_EVEN_POW2)

lemma REAL_DIV_SQRT: "ALL x::hollight.real.
   real_le (real_of_num 0) x --> real_div x (sqrt x) = sqrt x"
  by (import hollight REAL_DIV_SQRT)

lemma POW_2_SQRT_ABS: "ALL x::hollight.real.
   sqrt (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0))) = real_abs x"
  by (import hollight POW_2_SQRT_ABS)

lemma SQRT_EQ_0: "ALL x::hollight.real.
   real_le (real_of_num 0) x -->
   (sqrt x = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight SQRT_EQ_0)

lemma REAL_LE_LSQRT: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x &
   real_le (real_of_num 0) y &
   real_le x (real_pow y (NUMERAL_BIT0 (NUMERAL_BIT1 0))) -->
   real_le (sqrt x) y"
  by (import hollight REAL_LE_LSQRT)

lemma REAL_LE_POW_2: "ALL x::hollight.real.
   real_le (real_of_num 0) (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))"
  by (import hollight REAL_LE_POW_2)

lemma REAL_LE_RSQRT: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0))) y -->
   real_le x (sqrt y)"
  by (import hollight REAL_LE_RSQRT)

lemma SIN_0: "sin (real_of_num 0) = real_of_num 0"
  by (import hollight SIN_0)

lemma COS_0: "cos (real_of_num 0) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight COS_0)

lemma SIN_CIRCLE: "ALL x::hollight.real.
   real_add (real_pow (sin x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
    (real_pow (cos x) (NUMERAL_BIT0 (NUMERAL_BIT1 0))) =
   real_of_num (NUMERAL_BIT1 0)"
  by (import hollight SIN_CIRCLE)

lemma SIN_BOUND: "ALL x::hollight.real.
   real_le (real_abs (sin x)) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight SIN_BOUND)

lemma SIN_BOUNDS: "ALL x::hollight.real.
   real_le (real_neg (real_of_num (NUMERAL_BIT1 0))) (sin x) &
   real_le (sin x) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight SIN_BOUNDS)

lemma COS_BOUND: "ALL x::hollight.real.
   real_le (real_abs (cos x)) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight COS_BOUND)

lemma COS_BOUNDS: "ALL x::hollight.real.
   real_le (real_neg (real_of_num (NUMERAL_BIT1 0))) (cos x) &
   real_le (cos x) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight COS_BOUNDS)

lemma SIN_COS_ADD: "ALL (x::hollight.real) y::hollight.real.
   real_add
    (real_pow
      (real_sub (sin (real_add x y))
        (real_add (real_mul (sin x) (cos y)) (real_mul (cos x) (sin y))))
      (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
    (real_pow
      (real_sub (cos (real_add x y))
        (real_sub (real_mul (cos x) (cos y)) (real_mul (sin x) (sin y))))
      (NUMERAL_BIT0 (NUMERAL_BIT1 0))) =
   real_of_num 0"
  by (import hollight SIN_COS_ADD)

lemma SIN_COS_NEG: "ALL x::hollight.real.
   real_add
    (real_pow (real_add (sin (real_neg x)) (sin x))
      (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
    (real_pow (real_sub (cos (real_neg x)) (cos x))
      (NUMERAL_BIT0 (NUMERAL_BIT1 0))) =
   real_of_num 0"
  by (import hollight SIN_COS_NEG)

lemma SIN_ADD: "ALL (x::hollight.real) y::hollight.real.
   sin (real_add x y) =
   real_add (real_mul (sin x) (cos y)) (real_mul (cos x) (sin y))"
  by (import hollight SIN_ADD)

lemma COS_ADD: "ALL (x::hollight.real) y::hollight.real.
   cos (real_add x y) =
   real_sub (real_mul (cos x) (cos y)) (real_mul (sin x) (sin y))"
  by (import hollight COS_ADD)

lemma SIN_NEG: "ALL x::hollight.real. sin (real_neg x) = real_neg (sin x)"
  by (import hollight SIN_NEG)

lemma COS_NEG: "ALL x::hollight.real. cos (real_neg x) = cos x"
  by (import hollight COS_NEG)

lemma SIN_DOUBLE: "ALL x::hollight.real.
   sin (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) x) =
   real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
    (real_mul (sin x) (cos x))"
  by (import hollight SIN_DOUBLE)

lemma COS_DOUBLE: "ALL x::hollight.real.
   cos (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) x) =
   real_sub (real_pow (cos x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
    (real_pow (sin x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)))"
  by (import hollight COS_DOUBLE)

lemma COS_ABS: "ALL x::hollight.real. cos (real_abs x) = cos x"
  by (import hollight COS_ABS)

lemma SIN_PAIRED: "ALL x::hollight.real.
   sums
    (%n::nat.
        real_mul
         (real_div (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0))) n)
           (real_of_num
             (FACT (NUMERAL_BIT0 (NUMERAL_BIT1 0) * n + NUMERAL_BIT1 0))))
         (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0) * n + NUMERAL_BIT1 0)))
    (sin x)"
  by (import hollight SIN_PAIRED)

lemma SIN_POS: "ALL x::hollight.real.
   real_lt (real_of_num 0) x &
   real_lt x (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) -->
   real_lt (real_of_num 0) (sin x)"
  by (import hollight SIN_POS)

lemma COS_PAIRED: "ALL x::hollight.real.
   sums
    (%n::nat.
        real_mul
         (real_div (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0))) n)
           (real_of_num (FACT (NUMERAL_BIT0 (NUMERAL_BIT1 0) * n))))
         (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0) * n)))
    (cos x)"
  by (import hollight COS_PAIRED)

lemma COS_2: "real_lt (cos (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) (real_of_num 0)"
  by (import hollight COS_2)

lemma COS_ISZERO: "EX! x::hollight.real.
   real_le (real_of_num 0) x &
   real_le x (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) &
   cos x = real_of_num 0"
  by (import hollight COS_ISZERO)

constdefs
  pi :: "hollight.real" 
  "pi ==
real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
 (SOME x::hollight.real.
     real_le (real_of_num 0) x &
     real_le x (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) &
     cos x = real_of_num 0)"

lemma DEF_pi: "pi =
real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
 (SOME x::hollight.real.
     real_le (real_of_num 0) x &
     real_le x (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) &
     cos x = real_of_num 0)"
  by (import hollight DEF_pi)

lemma PI2: "real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) =
(SOME x::hollight.real.
    real_le (real_of_num 0) x &
    real_le x (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) &
    cos x = real_of_num 0)"
  by (import hollight PI2)

lemma COS_PI2: "cos (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) =
real_of_num 0"
  by (import hollight COS_PI2)

lemma PI2_BOUNDS: "real_lt (real_of_num 0)
 (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
real_lt (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
 (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))"
  by (import hollight PI2_BOUNDS)

lemma PI_POS: "real_lt (real_of_num 0) pi"
  by (import hollight PI_POS)

lemma SIN_PI2: "sin (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) =
real_of_num (NUMERAL_BIT1 0)"
  by (import hollight SIN_PI2)

lemma COS_PI: "cos pi = real_neg (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight COS_PI)

lemma SIN_PI: "sin pi = real_of_num 0"
  by (import hollight SIN_PI)

lemma SIN_COS: "ALL x::hollight.real.
   sin x =
   cos (real_sub (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
         x)"
  by (import hollight SIN_COS)

lemma COS_SIN: "ALL x::hollight.real.
   cos x =
   sin (real_sub (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
         x)"
  by (import hollight COS_SIN)

lemma SIN_PERIODIC_PI: "ALL x::hollight.real. sin (real_add x pi) = real_neg (sin x)"
  by (import hollight SIN_PERIODIC_PI)

lemma COS_PERIODIC_PI: "ALL x::hollight.real. cos (real_add x pi) = real_neg (cos x)"
  by (import hollight COS_PERIODIC_PI)

lemma SIN_PERIODIC: "ALL x::hollight.real.
   sin (real_add x
         (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) pi)) =
   sin x"
  by (import hollight SIN_PERIODIC)

lemma COS_PERIODIC: "ALL x::hollight.real.
   cos (real_add x
         (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) pi)) =
   cos x"
  by (import hollight COS_PERIODIC)

lemma COS_NPI: "ALL n::nat.
   cos (real_mul (real_of_num n) pi) =
   real_pow (real_neg (real_of_num (NUMERAL_BIT1 0))) n"
  by (import hollight COS_NPI)

lemma SIN_NPI: "ALL n::nat. sin (real_mul (real_of_num n) pi) = real_of_num 0"
  by (import hollight SIN_NPI)

lemma SIN_POS_PI2: "ALL x::hollight.real.
   real_lt (real_of_num 0) x &
   real_lt x (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) -->
   real_lt (real_of_num 0) (sin x)"
  by (import hollight SIN_POS_PI2)

lemma COS_POS_PI2: "ALL x::hollight.real.
   real_lt (real_of_num 0) x &
   real_lt x (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) -->
   real_lt (real_of_num 0) (cos x)"
  by (import hollight COS_POS_PI2)

lemma COS_POS_PI: "ALL x::hollight.real.
   real_lt
    (real_neg (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    x &
   real_lt x (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) -->
   real_lt (real_of_num 0) (cos x)"
  by (import hollight COS_POS_PI)

lemma SIN_POS_PI: "ALL x::hollight.real.
   real_lt (real_of_num 0) x & real_lt x pi -->
   real_lt (real_of_num 0) (sin x)"
  by (import hollight SIN_POS_PI)

lemma SIN_POS_PI_LE: "ALL x::hollight.real.
   real_le (real_of_num 0) x & real_le x pi -->
   real_le (real_of_num 0) (sin x)"
  by (import hollight SIN_POS_PI_LE)

lemma COS_TOTAL: "ALL y::hollight.real.
   real_le (real_neg (real_of_num (NUMERAL_BIT1 0))) y &
   real_le y (real_of_num (NUMERAL_BIT1 0)) -->
   (EX! x::hollight.real.
       real_le (real_of_num 0) x & real_le x pi & cos x = y)"
  by (import hollight COS_TOTAL)

lemma SIN_TOTAL: "ALL y::hollight.real.
   real_le (real_neg (real_of_num (NUMERAL_BIT1 0))) y &
   real_le y (real_of_num (NUMERAL_BIT1 0)) -->
   (EX! x::hollight.real.
       real_le
        (real_neg
          (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
        x &
       real_le x
        (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
       sin x = y)"
  by (import hollight SIN_TOTAL)

lemma COS_ZERO_LEMMA: "ALL x::hollight.real.
   real_le (real_of_num 0) x & cos x = real_of_num 0 -->
   (EX n::nat.
       ~ EVEN n &
       x =
       real_mul (real_of_num n)
        (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))"
  by (import hollight COS_ZERO_LEMMA)

lemma SIN_ZERO_LEMMA: "ALL x::hollight.real.
   real_le (real_of_num 0) x & sin x = real_of_num 0 -->
   (EX n::nat.
       EVEN n &
       x =
       real_mul (real_of_num n)
        (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))"
  by (import hollight SIN_ZERO_LEMMA)

lemma COS_ZERO: "ALL x::hollight.real.
   (cos x = real_of_num 0) =
   ((EX n::nat.
        ~ EVEN n &
        x =
        real_mul (real_of_num n)
         (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))) |
    (EX n::nat.
        ~ EVEN n &
        x =
        real_neg
         (real_mul (real_of_num n)
           (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))))"
  by (import hollight COS_ZERO)

lemma SIN_ZERO: "ALL x::hollight.real.
   (sin x = real_of_num 0) =
   ((EX n::nat.
        EVEN n &
        x =
        real_mul (real_of_num n)
         (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))) |
    (EX n::nat.
        EVEN n &
        x =
        real_neg
         (real_mul (real_of_num n)
           (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))))"
  by (import hollight SIN_ZERO)

lemma SIN_ZERO_PI: "ALL x::hollight.real.
   (sin x = real_of_num 0) =
   ((EX n::nat. x = real_mul (real_of_num n) pi) |
    (EX n::nat. x = real_neg (real_mul (real_of_num n) pi)))"
  by (import hollight SIN_ZERO_PI)

lemma COS_ONE_2PI: "ALL x::hollight.real.
   (cos x = real_of_num (NUMERAL_BIT1 0)) =
   ((EX n::nat.
        x =
        real_mul (real_of_num n)
         (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) pi)) |
    (EX n::nat.
        x =
        real_neg
         (real_mul (real_of_num n)
           (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) pi))))"
  by (import hollight COS_ONE_2PI)

constdefs
  tan :: "hollight.real => hollight.real" 
  "tan == %u::hollight.real. real_div (sin u) (cos u)"

lemma DEF_tan: "tan = (%u::hollight.real. real_div (sin u) (cos u))"
  by (import hollight DEF_tan)

lemma TAN_0: "tan (real_of_num 0) = real_of_num 0"
  by (import hollight TAN_0)

lemma TAN_PI: "tan pi = real_of_num 0"
  by (import hollight TAN_PI)

lemma TAN_NPI: "ALL n::nat. tan (real_mul (real_of_num n) pi) = real_of_num 0"
  by (import hollight TAN_NPI)

lemma TAN_NEG: "ALL x::hollight.real. tan (real_neg x) = real_neg (tan x)"
  by (import hollight TAN_NEG)

lemma TAN_PERIODIC: "ALL x::hollight.real.
   tan (real_add x
         (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) pi)) =
   tan x"
  by (import hollight TAN_PERIODIC)

lemma TAN_PERIODIC_PI: "ALL x::hollight.real. tan (real_add x pi) = tan x"
  by (import hollight TAN_PERIODIC_PI)

lemma TAN_PERIODIC_NPI: "ALL (x::hollight.real) n::nat.
   tan (real_add x (real_mul (real_of_num n) pi)) = tan x"
  by (import hollight TAN_PERIODIC_NPI)

lemma TAN_ADD: "ALL (x::hollight.real) y::hollight.real.
   cos x ~= real_of_num 0 &
   cos y ~= real_of_num 0 & cos (real_add x y) ~= real_of_num 0 -->
   tan (real_add x y) =
   real_div (real_add (tan x) (tan y))
    (real_sub (real_of_num (NUMERAL_BIT1 0)) (real_mul (tan x) (tan y)))"
  by (import hollight TAN_ADD)

lemma TAN_DOUBLE: "ALL x::hollight.real.
   cos x ~= real_of_num 0 &
   cos (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) x) ~=
   real_of_num 0 -->
   tan (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) x) =
   real_div (real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) (tan x))
    (real_sub (real_of_num (NUMERAL_BIT1 0))
      (real_pow (tan x) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))"
  by (import hollight TAN_DOUBLE)

lemma TAN_POS_PI2: "ALL x::hollight.real.
   real_lt (real_of_num 0) x &
   real_lt x (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) -->
   real_lt (real_of_num 0) (tan x)"
  by (import hollight TAN_POS_PI2)

lemma DIFF_TAN: "ALL x::hollight.real.
   cos x ~= real_of_num 0 -->
   diffl tan (real_inv (real_pow (cos x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) x"
  by (import hollight DIFF_TAN)

lemma DIFF_TAN_COMPOSITE: "diffl (g::hollight.real => hollight.real) (m::hollight.real)
 (x::hollight.real) &
cos (g x) ~= real_of_num 0 -->
diffl (%x::hollight.real. tan (g x))
 (real_mul (real_inv (real_pow (cos (g x)) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
   m)
 x"
  by (import hollight DIFF_TAN_COMPOSITE)

lemma TAN_TOTAL_LEMMA: "ALL y::hollight.real.
   real_lt (real_of_num 0) y -->
   (EX x::hollight.real.
       real_lt (real_of_num 0) x &
       real_lt x
        (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
       real_lt y (tan x))"
  by (import hollight TAN_TOTAL_LEMMA)

lemma TAN_TOTAL_POS: "ALL y::hollight.real.
   real_le (real_of_num 0) y -->
   (EX x::hollight.real.
       real_le (real_of_num 0) x &
       real_lt x
        (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
       tan x = y)"
  by (import hollight TAN_TOTAL_POS)

lemma TAN_TOTAL: "ALL y::hollight.real.
   EX! x::hollight.real.
      real_lt
       (real_neg
         (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
       x &
      real_lt x
       (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
      tan x = y"
  by (import hollight TAN_TOTAL)

lemma PI2_PI4: "real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))) =
real_mul (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
 (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))"
  by (import hollight PI2_PI4)

lemma TAN_PI4: "tan (real_div pi
      (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT0 (NUMERAL_BIT1 0))))) =
real_of_num (NUMERAL_BIT1 0)"
  by (import hollight TAN_PI4)

lemma TAN_COT: "ALL x::hollight.real.
   tan (real_sub (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
         x) =
   real_inv (tan x)"
  by (import hollight TAN_COT)

lemma TAN_BOUND_PI2: "ALL x::hollight.real.
   real_lt (real_abs x)
    (real_div pi
      (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT0 (NUMERAL_BIT1 0))))) -->
   real_lt (real_abs (tan x)) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight TAN_BOUND_PI2)

lemma TAN_ABS_GE_X: "ALL x::hollight.real.
   real_lt (real_abs x)
    (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) -->
   real_le (real_abs x) (real_abs (tan x))"
  by (import hollight TAN_ABS_GE_X)

constdefs
  asn :: "hollight.real => hollight.real" 
  "asn ==
%u::hollight.real.
   SOME x::hollight.real.
      real_le
       (real_neg
         (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
       x &
      real_le x
       (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
      sin x = u"

lemma DEF_asn: "asn =
(%u::hollight.real.
    SOME x::hollight.real.
       real_le
        (real_neg
          (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
        x &
       real_le x
        (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
       sin x = u)"
  by (import hollight DEF_asn)

constdefs
  acs :: "hollight.real => hollight.real" 
  "acs ==
%u::hollight.real.
   SOME x::hollight.real.
      real_le (real_of_num 0) x & real_le x pi & cos x = u"

lemma DEF_acs: "acs =
(%u::hollight.real.
    SOME x::hollight.real.
       real_le (real_of_num 0) x & real_le x pi & cos x = u)"
  by (import hollight DEF_acs)

constdefs
  atn :: "hollight.real => hollight.real" 
  "atn ==
%u::hollight.real.
   SOME x::hollight.real.
      real_lt
       (real_neg
         (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
       x &
      real_lt x
       (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
      tan x = u"

lemma DEF_atn: "atn =
(%u::hollight.real.
    SOME x::hollight.real.
       real_lt
        (real_neg
          (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
        x &
       real_lt x
        (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
       tan x = u)"
  by (import hollight DEF_atn)

lemma ASN: "ALL y::hollight.real.
   real_le (real_neg (real_of_num (NUMERAL_BIT1 0))) y &
   real_le y (real_of_num (NUMERAL_BIT1 0)) -->
   real_le
    (real_neg (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    (asn y) &
   real_le (asn y)
    (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
   sin (asn y) = y"
  by (import hollight ASN)

lemma ASN_SIN: "ALL y::hollight.real.
   real_le (real_neg (real_of_num (NUMERAL_BIT1 0))) y &
   real_le y (real_of_num (NUMERAL_BIT1 0)) -->
   sin (asn y) = y"
  by (import hollight ASN_SIN)

lemma ASN_BOUNDS: "ALL y::hollight.real.
   real_le (real_neg (real_of_num (NUMERAL_BIT1 0))) y &
   real_le y (real_of_num (NUMERAL_BIT1 0)) -->
   real_le
    (real_neg (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    (asn y) &
   real_le (asn y)
    (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))"
  by (import hollight ASN_BOUNDS)

lemma ASN_BOUNDS_LT: "ALL y::hollight.real.
   real_lt (real_neg (real_of_num (NUMERAL_BIT1 0))) y &
   real_lt y (real_of_num (NUMERAL_BIT1 0)) -->
   real_lt
    (real_neg (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    (asn y) &
   real_lt (asn y)
    (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))"
  by (import hollight ASN_BOUNDS_LT)

lemma SIN_ASN: "ALL x::hollight.real.
   real_le
    (real_neg (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    x &
   real_le x (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) -->
   asn (sin x) = x"
  by (import hollight SIN_ASN)

lemma ACS: "ALL y::hollight.real.
   real_le (real_neg (real_of_num (NUMERAL_BIT1 0))) y &
   real_le y (real_of_num (NUMERAL_BIT1 0)) -->
   real_le (real_of_num 0) (acs y) & real_le (acs y) pi & cos (acs y) = y"
  by (import hollight ACS)

lemma ACS_COS: "ALL y::hollight.real.
   real_le (real_neg (real_of_num (NUMERAL_BIT1 0))) y &
   real_le y (real_of_num (NUMERAL_BIT1 0)) -->
   cos (acs y) = y"
  by (import hollight ACS_COS)

lemma ACS_BOUNDS: "ALL y::hollight.real.
   real_le (real_neg (real_of_num (NUMERAL_BIT1 0))) y &
   real_le y (real_of_num (NUMERAL_BIT1 0)) -->
   real_le (real_of_num 0) (acs y) & real_le (acs y) pi"
  by (import hollight ACS_BOUNDS)

lemma ACS_BOUNDS_LT: "ALL y::hollight.real.
   real_lt (real_neg (real_of_num (NUMERAL_BIT1 0))) y &
   real_lt y (real_of_num (NUMERAL_BIT1 0)) -->
   real_lt (real_of_num 0) (acs y) & real_lt (acs y) pi"
  by (import hollight ACS_BOUNDS_LT)

lemma COS_ACS: "ALL x::hollight.real.
   real_le (real_of_num 0) x & real_le x pi --> acs (cos x) = x"
  by (import hollight COS_ACS)

lemma ATN: "ALL y::hollight.real.
   real_lt
    (real_neg (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    (atn y) &
   real_lt (atn y)
    (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) &
   tan (atn y) = y"
  by (import hollight ATN)

lemma ATN_TAN: "ALL x::hollight.real. tan (atn x) = x"
  by (import hollight ATN_TAN)

lemma ATN_BOUNDS: "ALL x::hollight.real.
   real_lt
    (real_neg (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    (atn x) &
   real_lt (atn x)
    (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0))))"
  by (import hollight ATN_BOUNDS)

lemma TAN_ATN: "ALL x::hollight.real.
   real_lt
    (real_neg (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    x &
   real_lt x (real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT1 0)))) -->
   atn (tan x) = x"
  by (import hollight TAN_ATN)

lemma ATN_0: "atn (real_of_num 0) = real_of_num 0"
  by (import hollight ATN_0)

lemma ATN_1: "atn (real_of_num (NUMERAL_BIT1 0)) =
real_div pi (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT0 (NUMERAL_BIT1 0))))"
  by (import hollight ATN_1)

lemma ATN_NEG: "ALL x::hollight.real. atn (real_neg x) = real_neg (atn x)"
  by (import hollight ATN_NEG)

lemma COS_ATN_NZ: "ALL x::hollight.real. cos (atn x) ~= real_of_num 0"
  by (import hollight COS_ATN_NZ)

lemma TAN_SEC: "ALL x::hollight.real.
   cos x ~= real_of_num 0 -->
   real_add (real_of_num (NUMERAL_BIT1 0))
    (real_pow (tan x) (NUMERAL_BIT0 (NUMERAL_BIT1 0))) =
   real_pow (real_inv (cos x)) (NUMERAL_BIT0 (NUMERAL_BIT1 0))"
  by (import hollight TAN_SEC)

lemma DIFF_ATN: "ALL x::hollight.real.
   diffl atn
    (real_inv
      (real_add (real_of_num (NUMERAL_BIT1 0))
        (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    x"
  by (import hollight DIFF_ATN)

lemma DIFF_ATN_COMPOSITE: "diffl (g::hollight.real => hollight.real) (m::hollight.real)
 (x::hollight.real) -->
diffl (%x::hollight.real. atn (g x))
 (real_mul
   (real_inv
     (real_add (real_of_num (NUMERAL_BIT1 0))
       (real_pow (g x) (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
   m)
 x"
  by (import hollight DIFF_ATN_COMPOSITE)

lemma ATN_MONO_LT: "ALL (x::hollight.real) y::hollight.real.
   real_lt x y --> real_lt (atn x) (atn y)"
  by (import hollight ATN_MONO_LT)

lemma ATN_MONO_LT_EQ: "ALL (x::hollight.real) y::hollight.real.
   real_lt (atn x) (atn y) = real_lt x y"
  by (import hollight ATN_MONO_LT_EQ)

lemma ATN_MONO_LE_EQ: "ALL (x::hollight.real) xa::hollight.real.
   real_le (atn x) (atn xa) = real_le x xa"
  by (import hollight ATN_MONO_LE_EQ)

lemma ATN_INJ: "ALL (x::hollight.real) xa::hollight.real. (atn x = atn xa) = (x = xa)"
  by (import hollight ATN_INJ)

lemma ATN_POS_LT: "real_lt (real_of_num 0) (atn (x::hollight.real)) = real_lt (real_of_num 0) x"
  by (import hollight ATN_POS_LT)

lemma ATN_POS_LE: "real_le (real_of_num 0) (atn (x::hollight.real)) = real_le (real_of_num 0) x"
  by (import hollight ATN_POS_LE)

lemma ATN_LT_PI4_POS: "ALL x::hollight.real.
   real_lt x (real_of_num (NUMERAL_BIT1 0)) -->
   real_lt (atn x)
    (real_div pi
      (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))"
  by (import hollight ATN_LT_PI4_POS)

lemma ATN_LT_PI4_NEG: "ALL x::hollight.real.
   real_lt (real_neg (real_of_num (NUMERAL_BIT1 0))) x -->
   real_lt
    (real_neg
      (real_div pi
        (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT0 (NUMERAL_BIT1 0))))))
    (atn x)"
  by (import hollight ATN_LT_PI4_NEG)

lemma ATN_LT_PI4: "ALL x::hollight.real.
   real_lt (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   real_lt (real_abs (atn x))
    (real_div pi
      (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))"
  by (import hollight ATN_LT_PI4)

lemma ATN_LE_PI4: "ALL x::hollight.real.
   real_le (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   real_le (real_abs (atn x))
    (real_div pi
      (real_of_num (NUMERAL_BIT0 (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))"
  by (import hollight ATN_LE_PI4)

lemma COS_SIN_SQRT: "ALL x::hollight.real.
   real_le (real_of_num 0) (cos x) -->
   cos x =
   sqrt
    (real_sub (real_of_num (NUMERAL_BIT1 0))
      (real_pow (sin x) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))"
  by (import hollight COS_SIN_SQRT)

lemma COS_ASN_NZ: "ALL x::hollight.real.
   real_lt (real_neg (real_of_num (NUMERAL_BIT1 0))) x &
   real_lt x (real_of_num (NUMERAL_BIT1 0)) -->
   cos (asn x) ~= real_of_num 0"
  by (import hollight COS_ASN_NZ)

lemma DIFF_ASN_COS: "ALL x::hollight.real.
   real_lt (real_neg (real_of_num (NUMERAL_BIT1 0))) x &
   real_lt x (real_of_num (NUMERAL_BIT1 0)) -->
   diffl asn (real_inv (cos (asn x))) x"
  by (import hollight DIFF_ASN_COS)

lemma DIFF_ASN: "ALL x::hollight.real.
   real_lt (real_neg (real_of_num (NUMERAL_BIT1 0))) x &
   real_lt x (real_of_num (NUMERAL_BIT1 0)) -->
   diffl asn
    (real_inv
      (sqrt
        (real_sub (real_of_num (NUMERAL_BIT1 0))
          (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0))))))
    x"
  by (import hollight DIFF_ASN)

lemma SIN_COS_SQRT: "ALL x::hollight.real.
   real_le (real_of_num 0) (sin x) -->
   sin x =
   sqrt
    (real_sub (real_of_num (NUMERAL_BIT1 0))
      (real_pow (cos x) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))"
  by (import hollight SIN_COS_SQRT)

lemma SIN_ACS_NZ: "ALL x::hollight.real.
   real_lt (real_neg (real_of_num (NUMERAL_BIT1 0))) x &
   real_lt x (real_of_num (NUMERAL_BIT1 0)) -->
   sin (acs x) ~= real_of_num 0"
  by (import hollight SIN_ACS_NZ)

lemma DIFF_ACS_SIN: "ALL x::hollight.real.
   real_lt (real_neg (real_of_num (NUMERAL_BIT1 0))) x &
   real_lt x (real_of_num (NUMERAL_BIT1 0)) -->
   diffl acs (real_inv (real_neg (sin (acs x)))) x"
  by (import hollight DIFF_ACS_SIN)

lemma DIFF_ACS: "ALL x::hollight.real.
   real_lt (real_neg (real_of_num (NUMERAL_BIT1 0))) x &
   real_lt x (real_of_num (NUMERAL_BIT1 0)) -->
   diffl acs
    (real_neg
      (real_inv
        (sqrt
          (real_sub (real_of_num (NUMERAL_BIT1 0))
            (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))))
    x"
  by (import hollight DIFF_ACS)

lemma CIRCLE_SINCOS: "ALL (x::hollight.real) y::hollight.real.
   real_add (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
    (real_pow y (NUMERAL_BIT0 (NUMERAL_BIT1 0))) =
   real_of_num (NUMERAL_BIT1 0) -->
   (EX t::hollight.real. x = cos t & y = sin t)"
  by (import hollight CIRCLE_SINCOS)

lemma ACS_MONO_LT: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_neg (real_of_num (NUMERAL_BIT1 0))) x &
   real_lt x y & real_lt y (real_of_num (NUMERAL_BIT1 0)) -->
   real_lt (acs y) (acs x)"
  by (import hollight ACS_MONO_LT)

lemma LESS_SUC_EQ: "ALL (m::nat) n::nat. < m (Suc n) = <= m n"
  by (import hollight LESS_SUC_EQ)

lemma LESS_1: "ALL x::nat. < x (NUMERAL_BIT1 0) = (x = 0)"
  by (import hollight LESS_1)

constdefs
  division :: "hollight.real * hollight.real => (nat => hollight.real) => bool" 
  "division ==
%(u::hollight.real * hollight.real) ua::nat => hollight.real.
   ua 0 = fst u &
   (EX N::nat.
       (ALL n::nat. < n N --> real_lt (ua n) (ua (Suc n))) &
       (ALL n::nat. >= n N --> ua n = snd u))"

lemma DEF_division: "division =
(%(u::hollight.real * hollight.real) ua::nat => hollight.real.
    ua 0 = fst u &
    (EX N::nat.
        (ALL n::nat. < n N --> real_lt (ua n) (ua (Suc n))) &
        (ALL n::nat. >= n N --> ua n = snd u)))"
  by (import hollight DEF_division)

constdefs
  dsize :: "(nat => hollight.real) => nat" 
  "dsize ==
%u::nat => hollight.real.
   SOME N::nat.
      (ALL n::nat. < n N --> real_lt (u n) (u (Suc n))) &
      (ALL n::nat. >= n N --> u n = u N)"

lemma DEF_dsize: "dsize =
(%u::nat => hollight.real.
    SOME N::nat.
       (ALL n::nat. < n N --> real_lt (u n) (u (Suc n))) &
       (ALL n::nat. >= n N --> u n = u N))"
  by (import hollight DEF_dsize)

constdefs
  tdiv :: "hollight.real * hollight.real
=> (nat => hollight.real) * (nat => hollight.real) => bool" 
  "tdiv ==
%(u::hollight.real * hollight.real)
   ua::(nat => hollight.real) * (nat => hollight.real).
   division (fst u, snd u) (fst ua) &
   (ALL n::nat.
       real_le (fst ua n) (snd ua n) & real_le (snd ua n) (fst ua (Suc n)))"

lemma DEF_tdiv: "tdiv =
(%(u::hollight.real * hollight.real)
    ua::(nat => hollight.real) * (nat => hollight.real).
    division (fst u, snd u) (fst ua) &
    (ALL n::nat.
        real_le (fst ua n) (snd ua n) &
        real_le (snd ua n) (fst ua (Suc n))))"
  by (import hollight DEF_tdiv)

constdefs
  gauge :: "(hollight.real => bool) => (hollight.real => hollight.real) => bool" 
  "gauge ==
%(u::hollight.real => bool) ua::hollight.real => hollight.real.
   ALL x::hollight.real. u x --> real_lt (real_of_num 0) (ua x)"

lemma DEF_gauge: "gauge =
(%(u::hollight.real => bool) ua::hollight.real => hollight.real.
    ALL x::hollight.real. u x --> real_lt (real_of_num 0) (ua x))"
  by (import hollight DEF_gauge)

constdefs
  fine :: "(hollight.real => hollight.real)
=> (nat => hollight.real) * (nat => hollight.real) => bool" 
  "fine ==
%(u::hollight.real => hollight.real)
   ua::(nat => hollight.real) * (nat => hollight.real).
   ALL n::nat.
      < n (dsize (fst ua)) -->
      real_lt (real_sub (fst ua (Suc n)) (fst ua n)) (u (snd ua n))"

lemma DEF_fine: "fine =
(%(u::hollight.real => hollight.real)
    ua::(nat => hollight.real) * (nat => hollight.real).
    ALL n::nat.
       < n (dsize (fst ua)) -->
       real_lt (real_sub (fst ua (Suc n)) (fst ua n)) (u (snd ua n)))"
  by (import hollight DEF_fine)

constdefs
  rsum :: "(nat => hollight.real) * (nat => hollight.real)
=> (hollight.real => hollight.real) => hollight.real" 
  "rsum ==
%(u::(nat => hollight.real) * (nat => hollight.real))
   ua::hollight.real => hollight.real.
   psum (0, dsize (fst u))
    (%n::nat. real_mul (ua (snd u n)) (real_sub (fst u (Suc n)) (fst u n)))"

lemma DEF_rsum: "rsum =
(%(u::(nat => hollight.real) * (nat => hollight.real))
    ua::hollight.real => hollight.real.
    psum (0, dsize (fst u))
     (%n::nat.
         real_mul (ua (snd u n)) (real_sub (fst u (Suc n)) (fst u n))))"
  by (import hollight DEF_rsum)

constdefs
  defint :: "hollight.real * hollight.real
=> (hollight.real => hollight.real) => hollight.real => bool" 
  "defint ==
%(u::hollight.real * hollight.real) (ua::hollight.real => hollight.real)
   ub::hollight.real.
   ALL e::hollight.real.
      real_lt (real_of_num 0) e -->
      (EX g::hollight.real => hollight.real.
          gauge (%x::hollight.real. real_le (fst u) x & real_le x (snd u))
           g &
          (ALL (D::nat => hollight.real) p::nat => hollight.real.
              tdiv (fst u, snd u) (D, p) & fine g (D, p) -->
              real_lt (real_abs (real_sub (rsum (D, p) ua) ub)) e))"

lemma DEF_defint: "defint =
(%(u::hollight.real * hollight.real) (ua::hollight.real => hollight.real)
    ub::hollight.real.
    ALL e::hollight.real.
       real_lt (real_of_num 0) e -->
       (EX g::hollight.real => hollight.real.
           gauge (%x::hollight.real. real_le (fst u) x & real_le x (snd u))
            g &
           (ALL (D::nat => hollight.real) p::nat => hollight.real.
               tdiv (fst u, snd u) (D, p) & fine g (D, p) -->
               real_lt (real_abs (real_sub (rsum (D, p) ua) ub)) e)))"
  by (import hollight DEF_defint)

lemma DIVISION_0: "ALL (a::hollight.real) b::hollight.real.
   a = b --> dsize (%n::nat. COND (n = 0) a b) = 0"
  by (import hollight DIVISION_0)

lemma DIVISION_1: "ALL (a::hollight.real) b::hollight.real.
   real_lt a b --> dsize (%n::nat. COND (n = 0) a b) = NUMERAL_BIT1 0"
  by (import hollight DIVISION_1)

lemma DIVISION_SINGLE: "ALL (a::hollight.real) b::hollight.real.
   real_le a b --> division (a, b) (%n::nat. COND (n = 0) a b)"
  by (import hollight DIVISION_SINGLE)

lemma DIVISION_LHS: "ALL (D::nat => hollight.real) (a::hollight.real) b::hollight.real.
   division (a, b) D --> D 0 = a"
  by (import hollight DIVISION_LHS)

lemma DIVISION_THM: "ALL (D::nat => hollight.real) (a::hollight.real) b::hollight.real.
   division (a, b) D =
   (D 0 = a &
    (ALL n::nat. < n (dsize D) --> real_lt (D n) (D (Suc n))) &
    (ALL n::nat. >= n (dsize D) --> D n = b))"
  by (import hollight DIVISION_THM)

lemma DIVISION_RHS: "ALL (D::nat => hollight.real) (a::hollight.real) b::hollight.real.
   division (a, b) D --> D (dsize D) = b"
  by (import hollight DIVISION_RHS)

lemma DIVISION_LT_GEN: "ALL (D::nat => hollight.real) (a::hollight.real) (b::hollight.real) (m::nat)
   n::nat.
   division (a, b) D & < m n & <= n (dsize D) --> real_lt (D m) (D n)"
  by (import hollight DIVISION_LT_GEN)

lemma DIVISION_LT: "ALL (D::nat => hollight.real) (a::hollight.real) b::hollight.real.
   division (a, b) D -->
   (ALL n::nat. < n (dsize D) --> real_lt (D 0) (D (Suc n)))"
  by (import hollight DIVISION_LT)

lemma DIVISION_LE: "ALL (D::nat => hollight.real) (a::hollight.real) b::hollight.real.
   division (a, b) D --> real_le a b"
  by (import hollight DIVISION_LE)

lemma DIVISION_GT: "ALL (D::nat => hollight.real) (a::hollight.real) b::hollight.real.
   division (a, b) D -->
   (ALL n::nat. < n (dsize D) --> real_lt (D n) (D (dsize D)))"
  by (import hollight DIVISION_GT)

lemma DIVISION_EQ: "ALL (D::nat => hollight.real) (a::hollight.real) b::hollight.real.
   division (a, b) D --> (a = b) = (dsize D = 0)"
  by (import hollight DIVISION_EQ)

lemma DIVISION_LBOUND: "ALL (x::nat => hollight.real) (xa::hollight.real) (xb::hollight.real)
   xc::nat. division (xa, xb) x --> real_le xa (x xc)"
  by (import hollight DIVISION_LBOUND)

lemma DIVISION_LBOUND_LT: "ALL (x::nat => hollight.real) (xa::hollight.real) (xb::hollight.real)
   xc::nat. division (xa, xb) x & dsize x ~= 0 --> real_lt xa (x (Suc xc))"
  by (import hollight DIVISION_LBOUND_LT)

lemma DIVISION_UBOUND: "ALL (x::nat => hollight.real) (xa::hollight.real) (xb::hollight.real)
   xc::nat. division (xa, xb) x --> real_le (x xc) xb"
  by (import hollight DIVISION_UBOUND)

lemma DIVISION_UBOUND_LT: "ALL (D::nat => hollight.real) (a::hollight.real) (b::hollight.real) n::nat.
   division (a, b) D & < n (dsize D) --> real_lt (D n) b"
  by (import hollight DIVISION_UBOUND_LT)

lemma DIVISION_APPEND_LEMMA1: "ALL (a::hollight.real) (b::hollight.real) (c::hollight.real)
   (D1::nat => hollight.real) D2::nat => hollight.real.
   division (a, b) D1 & division (b, c) D2 -->
   (ALL n::nat.
       < n (dsize D1 + dsize D2) -->
       real_lt (COND (< n (dsize D1)) (D1 n) (D2 (n - dsize D1)))
        (COND (< (Suc n) (dsize D1)) (D1 (Suc n))
          (D2 (Suc n - dsize D1)))) &
   (ALL n::nat.
       >= n (dsize D1 + dsize D2) -->
       COND (< n (dsize D1)) (D1 n) (D2 (n - dsize D1)) =
       COND (< (dsize D1 + dsize D2) (dsize D1)) (D1 (dsize D1 + dsize D2))
        (D2 (dsize D1 + dsize D2 - dsize D1)))"
  by (import hollight DIVISION_APPEND_LEMMA1)

lemma DIVISION_APPEND_LEMMA2: "ALL (a::hollight.real) (b::hollight.real) (c::hollight.real)
   (D1::nat => hollight.real) D2::nat => hollight.real.
   division (a, b) D1 & division (b, c) D2 -->
   dsize (%n::nat. COND (< n (dsize D1)) (D1 n) (D2 (n - dsize D1))) =
   dsize D1 + dsize D2"
  by (import hollight DIVISION_APPEND_LEMMA2)

lemma DIVISION_APPEND: "ALL (a::hollight.real) (b::hollight.real) c::hollight.real.
   (EX (D1::nat => hollight.real) p1::nat => hollight.real.
       tdiv (a, b) (D1, p1) &
       fine (g::hollight.real => hollight.real) (D1, p1)) &
   (EX (D2::nat => hollight.real) p2::nat => hollight.real.
       tdiv (b, c) (D2, p2) & fine g (D2, p2)) -->
   (EX (x::nat => hollight.real) p::nat => hollight.real.
       tdiv (a, c) (x, p) & fine g (x, p))"
  by (import hollight DIVISION_APPEND)

lemma DIVISION_EXISTS: "ALL (a::hollight.real) (b::hollight.real) g::hollight.real => hollight.real.
   real_le a b & gauge (%x::hollight.real. real_le a x & real_le x b) g -->
   (EX (D::nat => hollight.real) p::nat => hollight.real.
       tdiv (a, b) (D, p) & fine g (D, p))"
  by (import hollight DIVISION_EXISTS)

lemma GAUGE_MIN: "ALL (E::hollight.real => bool) (g1::hollight.real => hollight.real)
   g2::hollight.real => hollight.real.
   gauge E g1 & gauge E g2 -->
   gauge E (%x::hollight.real. COND (real_lt (g1 x) (g2 x)) (g1 x) (g2 x))"
  by (import hollight GAUGE_MIN)

lemma FINE_MIN: "ALL (g1::hollight.real => hollight.real)
   (g2::hollight.real => hollight.real) (D::nat => hollight.real)
   p::nat => hollight.real.
   fine (%x::hollight.real. COND (real_lt (g1 x) (g2 x)) (g1 x) (g2 x))
    (D, p) -->
   fine g1 (D, p) & fine g2 (D, p)"
  by (import hollight FINE_MIN)

lemma DINT_UNIQ: "ALL (a::hollight.real) (b::hollight.real)
   (f::hollight.real => hollight.real) (k1::hollight.real)
   k2::hollight.real.
   real_le a b & defint (a, b) f k1 & defint (a, b) f k2 --> k1 = k2"
  by (import hollight DINT_UNIQ)

lemma INTEGRAL_NULL: "ALL (f::hollight.real => hollight.real) a::hollight.real.
   defint (a, a) f (real_of_num 0)"
  by (import hollight INTEGRAL_NULL)

lemma STRADDLE_LEMMA: "ALL (f::hollight.real => hollight.real) (f'::hollight.real => hollight.real)
   (a::hollight.real) (b::hollight.real) e::hollight.real.
   (ALL x::hollight.real. real_le a x & real_le x b --> diffl f (f' x) x) &
   real_lt (real_of_num 0) e -->
   (EX x::hollight.real => hollight.real.
       gauge (%x::hollight.real. real_le a x & real_le x b) x &
       (ALL (xa::hollight.real) (u::hollight.real) v::hollight.real.
           real_le a u &
           real_le u xa &
           real_le xa v & real_le v b & real_lt (real_sub v u) (x xa) -->
           real_le
            (real_abs
              (real_sub (real_sub (f v) (f u))
                (real_mul (f' xa) (real_sub v u))))
            (real_mul e (real_sub v u))))"
  by (import hollight STRADDLE_LEMMA)

lemma FTC1: "ALL (f::hollight.real => hollight.real) (f'::hollight.real => hollight.real)
   (a::hollight.real) b::hollight.real.
   real_le a b &
   (ALL x::hollight.real.
       real_le a x & real_le x b --> diffl f (f' x) x) -->
   defint (a, b) f' (real_sub (f b) (f a))"
  by (import hollight FTC1)

lemma MCLAURIN: "ALL (f::hollight.real => hollight.real)
   (diff::nat => hollight.real => hollight.real) (h::hollight.real) n::nat.
   real_lt (real_of_num 0) h &
   < 0 n &
   diff 0 = f &
   (ALL (m::nat) t::hollight.real.
       < m n & real_le (real_of_num 0) t & real_le t h -->
       diffl (diff m) (diff (Suc m) t) t) -->
   (EX t::hollight.real.
       real_lt (real_of_num 0) t &
       real_lt t h &
       f h =
       real_add
        (psum (0, n)
          (%m::nat.
              real_mul
               (real_div (diff m (real_of_num 0)) (real_of_num (FACT m)))
               (real_pow h m)))
        (real_mul (real_div (diff n t) (real_of_num (FACT n)))
          (real_pow h n)))"
  by (import hollight MCLAURIN)

lemma MCLAURIN_NEG: "ALL (f::hollight.real => hollight.real)
   (diff::nat => hollight.real => hollight.real) (h::hollight.real) n::nat.
   real_lt h (real_of_num 0) &
   < 0 n &
   diff 0 = f &
   (ALL (m::nat) t::hollight.real.
       < m n & real_le h t & real_le t (real_of_num 0) -->
       diffl (diff m) (diff (Suc m) t) t) -->
   (EX t::hollight.real.
       real_lt h t &
       real_lt t (real_of_num 0) &
       f h =
       real_add
        (psum (0, n)
          (%m::nat.
              real_mul
               (real_div (diff m (real_of_num 0)) (real_of_num (FACT m)))
               (real_pow h m)))
        (real_mul (real_div (diff n t) (real_of_num (FACT n)))
          (real_pow h n)))"
  by (import hollight MCLAURIN_NEG)

lemma MCLAURIN_BI_LE: "ALL (f::hollight.real => hollight.real)
   (diff::nat => hollight.real => hollight.real) (x::hollight.real) n::nat.
   diff 0 = f &
   (ALL (m::nat) t::hollight.real.
       < m n & real_le (real_abs t) (real_abs x) -->
       diffl (diff m) (diff (Suc m) t) t) -->
   (EX xa::hollight.real.
       real_le (real_abs xa) (real_abs x) &
       f x =
       real_add
        (psum (0, n)
          (%m::nat.
              real_mul
               (real_div (diff m (real_of_num 0)) (real_of_num (FACT m)))
               (real_pow x m)))
        (real_mul (real_div (diff n xa) (real_of_num (FACT n)))
          (real_pow x n)))"
  by (import hollight MCLAURIN_BI_LE)

lemma MCLAURIN_ALL_LT: "ALL (f::hollight.real => hollight.real)
   diff::nat => hollight.real => hollight.real.
   diff 0 = f &
   (ALL (m::nat) x::hollight.real. diffl (diff m) (diff (Suc m) x) x) -->
   (ALL (x::hollight.real) n::nat.
       x ~= real_of_num 0 & < 0 n -->
       (EX t::hollight.real.
           real_lt (real_of_num 0) (real_abs t) &
           real_lt (real_abs t) (real_abs x) &
           f x =
           real_add
            (psum (0, n)
              (%m::nat.
                  real_mul
                   (real_div (diff m (real_of_num 0))
                     (real_of_num (FACT m)))
                   (real_pow x m)))
            (real_mul (real_div (diff n t) (real_of_num (FACT n)))
              (real_pow x n))))"
  by (import hollight MCLAURIN_ALL_LT)

lemma MCLAURIN_ZERO: "ALL (diff::nat => hollight.real => hollight.real) (n::nat) x::hollight.real.
   x = real_of_num 0 & < 0 n -->
   psum (0, n)
    (%m::nat.
        real_mul (real_div (diff m (real_of_num 0)) (real_of_num (FACT m)))
         (real_pow x m)) =
   diff 0 (real_of_num 0)"
  by (import hollight MCLAURIN_ZERO)

lemma MCLAURIN_ALL_LE: "ALL (f::hollight.real => hollight.real)
   diff::nat => hollight.real => hollight.real.
   diff 0 = f &
   (ALL (m::nat) x::hollight.real. diffl (diff m) (diff (Suc m) x) x) -->
   (ALL (x::hollight.real) n::nat.
       EX t::hollight.real.
          real_le (real_abs t) (real_abs x) &
          f x =
          real_add
           (psum (0, n)
             (%m::nat.
                 real_mul
                  (real_div (diff m (real_of_num 0)) (real_of_num (FACT m)))
                  (real_pow x m)))
           (real_mul (real_div (diff n t) (real_of_num (FACT n)))
             (real_pow x n)))"
  by (import hollight MCLAURIN_ALL_LE)

lemma MCLAURIN_EXP_LEMMA: "exp = exp & (ALL (x::nat) xa::hollight.real. diffl exp (exp xa) xa)"
  by (import hollight MCLAURIN_EXP_LEMMA)

lemma MCLAURIN_EXP_LT: "ALL (x::hollight.real) n::nat.
   x ~= real_of_num 0 & < 0 n -->
   (EX t::hollight.real.
       real_lt (real_of_num 0) (real_abs t) &
       real_lt (real_abs t) (real_abs x) &
       exp x =
       real_add
        (psum (0, n)
          (%m::nat. real_div (real_pow x m) (real_of_num (FACT m))))
        (real_mul (real_div (exp t) (real_of_num (FACT n))) (real_pow x n)))"
  by (import hollight MCLAURIN_EXP_LT)

lemma MCLAURIN_EXP_LE: "ALL (x::hollight.real) n::nat.
   EX t::hollight.real.
      real_le (real_abs t) (real_abs x) &
      exp x =
      real_add
       (psum (0, n)
         (%m::nat. real_div (real_pow x m) (real_of_num (FACT m))))
       (real_mul (real_div (exp t) (real_of_num (FACT n))) (real_pow x n))"
  by (import hollight MCLAURIN_EXP_LE)

lemma DIFF_LN_COMPOSITE: "ALL (g::hollight.real => hollight.real) (m::hollight.real) x::hollight.real.
   diffl g m x & real_lt (real_of_num 0) (g x) -->
   diffl (%x::hollight.real. ln (g x)) (real_mul (real_inv (g x)) m) x"
  by (import hollight DIFF_LN_COMPOSITE)

lemma MCLAURIN_LN_POS: "ALL (x::hollight.real) n::nat.
   real_lt (real_of_num 0) x & < 0 n -->
   (EX t::hollight.real.
       real_lt (real_of_num 0) t &
       real_lt t x &
       ln (real_add (real_of_num (NUMERAL_BIT1 0)) x) =
       real_add
        (psum (0, n)
          (%m::nat.
              real_mul
               (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0))) (Suc m))
               (real_div (real_pow x m) (real_of_num m))))
        (real_mul
          (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0))) (Suc n))
          (real_div (real_pow x n)
            (real_mul (real_of_num n)
              (real_pow (real_add (real_of_num (NUMERAL_BIT1 0)) t) n)))))"
  by (import hollight MCLAURIN_LN_POS)

lemma MCLAURIN_LN_NEG: "ALL (x::hollight.real) n::nat.
   real_lt (real_of_num 0) x &
   real_lt x (real_of_num (NUMERAL_BIT1 0)) & < 0 n -->
   (EX t::hollight.real.
       real_lt (real_of_num 0) t &
       real_lt t x &
       real_neg (ln (real_sub (real_of_num (NUMERAL_BIT1 0)) x)) =
       real_add
        (psum (0, n) (%m::nat. real_div (real_pow x m) (real_of_num m)))
        (real_div (real_pow x n)
          (real_mul (real_of_num n)
            (real_pow (real_sub (real_of_num (NUMERAL_BIT1 0)) t) n))))"
  by (import hollight MCLAURIN_LN_NEG)

lemma MCLAURIN_SIN: "ALL (x::hollight.real) n::nat.
   real_le
    (real_abs
      (real_sub (sin x)
        (psum (0, n)
          (%m::nat.
              real_mul
               (COND (EVEN m) (real_of_num 0)
                 (real_div
                   (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
                     (DIV (m - NUMERAL_BIT1 0)
                       (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
                   (real_of_num (FACT m))))
               (real_pow x m)))))
    (real_mul (real_inv (real_of_num (FACT n))) (real_pow (real_abs x) n))"
  by (import hollight MCLAURIN_SIN)

lemma MCLAURIN_COS: "ALL (x::hollight.real) n::nat.
   real_le
    (real_abs
      (real_sub (cos x)
        (psum (0, n)
          (%m::nat.
              real_mul
               (COND (EVEN m)
                 (real_div
                   (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
                     (DIV m (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
                   (real_of_num (FACT m)))
                 (real_of_num 0))
               (real_pow x m)))))
    (real_mul (real_inv (real_of_num (FACT n))) (real_pow (real_abs x) n))"
  by (import hollight MCLAURIN_COS)

lemma REAL_ATN_POWSER_SUMMABLE: "ALL x::hollight.real.
   real_lt (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   summable
    (%n::nat.
        real_mul
         (COND (EVEN n) (real_of_num 0)
           (real_div
             (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
               (DIV (n - NUMERAL_BIT1 0) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
             (real_of_num n)))
         (real_pow x n))"
  by (import hollight REAL_ATN_POWSER_SUMMABLE)

lemma REAL_ATN_POWSER_DIFFS_SUMMABLE: "ALL x::hollight.real.
   real_lt (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   summable
    (%xa::nat.
        real_mul
         (diffs
           (%n::nat.
               COND (EVEN n) (real_of_num 0)
                (real_div
                  (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
                    (DIV (n - NUMERAL_BIT1 0)
                      (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
                  (real_of_num n)))
           xa)
         (real_pow x xa))"
  by (import hollight REAL_ATN_POWSER_DIFFS_SUMMABLE)

lemma REAL_ATN_POWSER_DIFFS_SUM: "ALL x::hollight.real.
   real_lt (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   sums
    (%n::nat.
        real_mul
         (diffs
           (%n::nat.
               COND (EVEN n) (real_of_num 0)
                (real_div
                  (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
                    (DIV (n - NUMERAL_BIT1 0)
                      (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
                  (real_of_num n)))
           n)
         (real_pow x n))
    (real_inv
      (real_add (real_of_num (NUMERAL_BIT1 0))
        (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))"
  by (import hollight REAL_ATN_POWSER_DIFFS_SUM)

lemma REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE: "ALL x::hollight.real.
   real_lt (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   summable
    (%xa::nat.
        real_mul
         (diffs
           (diffs
             (%n::nat.
                 COND (EVEN n) (real_of_num 0)
                  (real_div
                    (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
                      (DIV (n - NUMERAL_BIT1 0)
                        (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
                    (real_of_num n))))
           xa)
         (real_pow x xa))"
  by (import hollight REAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE)

lemma REAL_ATN_POWSER_DIFFL: "ALL x::hollight.real.
   real_lt (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   diffl
    (%x::hollight.real.
        suminf
         (%n::nat.
             real_mul
              (COND (EVEN n) (real_of_num 0)
                (real_div
                  (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
                    (DIV (n - NUMERAL_BIT1 0)
                      (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
                  (real_of_num n)))
              (real_pow x n)))
    (real_inv
      (real_add (real_of_num (NUMERAL_BIT1 0))
        (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))))
    x"
  by (import hollight REAL_ATN_POWSER_DIFFL)

lemma REAL_ATN_POWSER: "ALL x::hollight.real.
   real_lt (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   sums
    (%n::nat.
        real_mul
         (COND (EVEN n) (real_of_num 0)
           (real_div
             (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
               (DIV (n - NUMERAL_BIT1 0) (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
             (real_of_num n)))
         (real_pow x n))
    (atn x)"
  by (import hollight REAL_ATN_POWSER)

lemma MCLAURIN_ATN: "ALL (x::hollight.real) n::nat.
   real_lt (real_abs x) (real_of_num (NUMERAL_BIT1 0)) -->
   real_le
    (real_abs
      (real_sub (atn x)
        (psum (0, n)
          (%m::nat.
              real_mul
               (COND (EVEN m) (real_of_num 0)
                 (real_div
                   (real_pow (real_neg (real_of_num (NUMERAL_BIT1 0)))
                     (DIV (m - NUMERAL_BIT1 0)
                       (NUMERAL_BIT0 (NUMERAL_BIT1 0))))
                   (real_of_num m)))
               (real_pow x m)))))
    (real_div (real_pow (real_abs x) n)
      (real_sub (real_of_num (NUMERAL_BIT1 0)) (real_abs x)))"
  by (import hollight MCLAURIN_ATN)

;end_setup

end

