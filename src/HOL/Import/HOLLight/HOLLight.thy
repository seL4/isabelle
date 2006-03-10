(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOLLight = "../HOLLightCompat" + "../HOL4Syntax":

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

lemma WF_EQ: "WF (u_353::'A::type => 'A::type => bool) =
(ALL P::'A::type => bool.
    Ex P = (EX x::'A::type. P x & (ALL y::'A::type. u_353 y x --> ~ P y)))"
  by (import hollight WF_EQ)

lemma WF_IND: "WF (u_353::'A::type => 'A::type => bool) =
(ALL P::'A::type => bool.
    (ALL x::'A::type. (ALL y::'A::type. u_353 y x --> P y) --> P x) -->
    All P)"
  by (import hollight WF_IND)

lemma WF_DCHAIN: "WF (u_353::'A::type => 'A::type => bool) =
(~ (EX s::nat => 'A::type. ALL n::nat. u_353 (s (Suc n)) (s n)))"
  by (import hollight WF_DCHAIN)

lemma WF_UREC: "WF (u_353::'A::type => 'A::type => bool) -->
(ALL H::('A::type => 'B::type) => 'A::type => 'B::type.
    (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
        (ALL z::'A::type. u_353 z x --> f z = g z) --> H f x = H g x) -->
    (ALL (f::'A::type => 'B::type) g::'A::type => 'B::type.
        (ALL x::'A::type. f x = H f x) & (ALL x::'A::type. g x = H g x) -->
        f = g))"
  by (import hollight WF_UREC)

lemma WF_UREC_WF: "(ALL H::('A::type => bool) => 'A::type => bool.
    (ALL (f::'A::type => bool) (g::'A::type => bool) x::'A::type.
        (ALL z::'A::type.
            (u_353::'A::type => 'A::type => bool) z x --> f z = g z) -->
        H f x = H g x) -->
    (ALL (f::'A::type => bool) g::'A::type => bool.
        (ALL x::'A::type. f x = H f x) & (ALL x::'A::type. g x = H g x) -->
        f = g)) -->
WF u_353"
  by (import hollight WF_UREC_WF)

lemma WF_REC_INVARIANT: "WF (u_353::'A::type => 'A::type => bool) -->
(ALL (H::('A::type => 'B::type) => 'A::type => 'B::type)
    S::'A::type => 'B::type => bool.
    (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
        (ALL z::'A::type. u_353 z x --> f z = g z & S z (f z)) -->
        H f x = H g x & S x (H f x)) -->
    (EX f::'A::type => 'B::type. ALL x::'A::type. f x = H f x))"
  by (import hollight WF_REC_INVARIANT)

lemma WF_REC: "WF (u_353::'A::type => 'A::type => bool) -->
(ALL H::('A::type => 'B::type) => 'A::type => 'B::type.
    (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
        (ALL z::'A::type. u_353 z x --> f z = g z) --> H f x = H g x) -->
    (EX f::'A::type => 'B::type. ALL x::'A::type. f x = H f x))"
  by (import hollight WF_REC)

lemma WF_REC_WF: "(ALL H::('A::type => nat) => 'A::type => nat.
    (ALL (f::'A::type => nat) (g::'A::type => nat) x::'A::type.
        (ALL z::'A::type.
            (u_353::'A::type => 'A::type => bool) z x --> f z = g z) -->
        H f x = H g x) -->
    (EX f::'A::type => nat. ALL x::'A::type. f x = H f x)) -->
WF u_353"
  by (import hollight WF_REC_WF)

lemma WF_EREC: "WF (u_353::'A::type => 'A::type => bool) -->
(ALL H::('A::type => 'B::type) => 'A::type => 'B::type.
    (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
        (ALL z::'A::type. u_353 z x --> f z = g z) --> H f x = H g x) -->
    (EX! f::'A::type => 'B::type. ALL x::'A::type. f x = H f x))"
  by (import hollight WF_EREC)

lemma WF_SUBSET: "(ALL (x::'A::type) y::'A::type.
    (u_353::'A::type => 'A::type => bool) x y -->
    (u_472::'A::type => 'A::type => bool) x y) &
WF u_472 -->
WF u_353"
  by (import hollight WF_SUBSET)

lemma WF_MEASURE_GEN: "ALL m::'A::type => 'B::type.
   WF (u_353::'B::type => 'B::type => bool) -->
   WF (%(x::'A::type) x'::'A::type. u_353 (m x) (m x'))"
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

lemma WF_POINTWISE: "WF (u_353::'A::type => 'A::type => bool) &
WF (u_472::'B::type => 'B::type => bool) -->
WF (GABS
     (%f::'A::type * 'B::type => 'A::type * 'B::type => bool.
         ALL (x1::'A::type) y1::'B::type.
            GEQ (f (x1, y1))
             (GABS
               (%f::'A::type * 'B::type => bool.
                   ALL (x2::'A::type) y2::'B::type.
                      GEQ (f (x2, y2)) (u_353 x1 x2 & u_472 y1 y2)))))"
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

lemma WF_REFL: "ALL x::'A::type. WF (u_353::'A::type => 'A::type => bool) --> ~ u_353 x x"
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
   WF (u_353::'A::type => 'A::type => bool) &
   (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
       (ALL z::'A::type. u_353 z x --> f z = g z) -->
       P f x = P g x & G f x = G g x & H f x = H g x) &
   (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type) x::'A::type.
       (ALL z::'A::type. u_353 z x --> f z = g z) --> H f x = H g x) &
   (ALL (f::'A::type => 'B::type) (x::'A::type) y::'A::type.
       P f x & u_353 y (G f x) --> u_353 y x) -->
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
            (op =::nat => nat => bool) ((HOL.plus::nat => nat => nat) x xa)
             ((HOL.plus::nat => nat => nat) x xa))))
 ((op &::bool => bool => bool)
   ((op =::nat => nat => bool) ((HOL.plus::nat => nat => nat) (0::nat) (0::nat))
     (0::nat))
   ((op &::bool => bool => bool)
     ((All::(nat => bool) => bool)
       (%x::nat.
           (op =::nat => nat => bool)
            ((HOL.plus::nat => nat => nat) (0::nat)
              ((NUMERAL_BIT0::nat => nat) x))
            ((NUMERAL_BIT0::nat => nat) x)))
     ((op &::bool => bool => bool)
       ((All::(nat => bool) => bool)
         (%x::nat.
             (op =::nat => nat => bool)
              ((HOL.plus::nat => nat => nat) (0::nat)
                ((NUMERAL_BIT1::nat => nat) x))
              ((NUMERAL_BIT1::nat => nat) x)))
       ((op &::bool => bool => bool)
         ((All::(nat => bool) => bool)
           (%x::nat.
               (op =::nat => nat => bool)
                ((HOL.plus::nat => nat => nat) ((NUMERAL_BIT0::nat => nat) x)
                  (0::nat))
                ((NUMERAL_BIT0::nat => nat) x)))
         ((op &::bool => bool => bool)
           ((All::(nat => bool) => bool)
             (%x::nat.
                 (op =::nat => nat => bool)
                  ((HOL.plus::nat => nat => nat) ((NUMERAL_BIT1::nat => nat) x)
                    (0::nat))
                  ((NUMERAL_BIT1::nat => nat) x)))
           ((op &::bool => bool => bool)
             ((All::(nat => bool) => bool)
               (%x::nat.
                   (All::(nat => bool) => bool)
                    (%xa::nat.
                        (op =::nat => nat => bool)
                         ((HOL.plus::nat => nat => nat)
                           ((NUMERAL_BIT0::nat => nat) x)
                           ((NUMERAL_BIT0::nat => nat) xa))
                         ((NUMERAL_BIT0::nat => nat)
                           ((HOL.plus::nat => nat => nat) x xa)))))
             ((op &::bool => bool => bool)
               ((All::(nat => bool) => bool)
                 (%x::nat.
                     (All::(nat => bool) => bool)
                      (%xa::nat.
                          (op =::nat => nat => bool)
                           ((HOL.plus::nat => nat => nat)
                             ((NUMERAL_BIT0::nat => nat) x)
                             ((NUMERAL_BIT1::nat => nat) xa))
                           ((NUMERAL_BIT1::nat => nat)
                             ((HOL.plus::nat => nat => nat) x xa)))))
               ((op &::bool => bool => bool)
                 ((All::(nat => bool) => bool)
                   (%x::nat.
                       (All::(nat => bool) => bool)
                        (%xa::nat.
                            (op =::nat => nat => bool)
                             ((HOL.plus::nat => nat => nat)
                               ((NUMERAL_BIT1::nat => nat) x)
                               ((NUMERAL_BIT0::nat => nat) xa))
                             ((NUMERAL_BIT1::nat => nat)
                               ((HOL.plus::nat => nat => nat) x xa)))))
                 ((All::(nat => bool) => bool)
                   (%x::nat.
                       (All::(nat => bool) => bool)
                        (%xa::nat.
                            (op =::nat => nat => bool)
                             ((HOL.plus::nat => nat => nat)
                               ((NUMERAL_BIT1::nat => nat) x)
                               ((NUMERAL_BIT1::nat => nat) xa))
                             ((NUMERAL_BIT0::nat => nat)
                               ((Suc::nat => nat)
                                 ((HOL.plus::nat => nat => nat) x
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
                           ((HOL.plus::nat => nat => nat)
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
                             ((HOL.plus::nat => nat => nat)
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
                             ((HOL.plus::nat => nat => nat)
                               ((NUMERAL_BIT1::nat => nat) x)
                               ((HOL.plus::nat => nat => nat)
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

consts
  OUTL :: "'A + 'B => 'A" 

defs
  OUTL_def: "hollight.OUTL ==
SOME OUTL::'A::type + 'B::type => 'A::type.
   ALL x::'A::type. OUTL (Inl x) = x"

lemma DEF_OUTL: "hollight.OUTL =
(SOME OUTL::'A::type + 'B::type => 'A::type.
    ALL x::'A::type. OUTL (Inl x) = x)"
  by (import hollight DEF_OUTL)

consts
  OUTR :: "'A + 'B => 'B" 

defs
  OUTR_def: "hollight.OUTR ==
SOME OUTR::'A::type + 'B::type => 'B::type.
   ALL y::'B::type. OUTR (Inr y) = y"

lemma DEF_OUTR: "hollight.OUTR =
(SOME OUTR::'A::type + 'B::type => 'B::type.
    ALL y::'B::type. OUTR (Inr y) = y)"
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

lemma bool_RECURSION: "ALL (a::'A::type) b::'A::type.
   EX x::bool => 'A::type. x False = a & x True = b"
  by (import hollight bool_RECURSION)

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

lemma ISO_USAGE: "ISO (f::'q_16636::type => 'q_16633::type)
 (g::'q_16633::type => 'q_16636::type) -->
(ALL P::'q_16636::type => bool. All P = (ALL x::'q_16633::type. P (g x))) &
(ALL P::'q_16636::type => bool. Ex P = (EX x::'q_16633::type. P (g x))) &
(ALL (a::'q_16636::type) b::'q_16633::type. (a = g b) = (f a = b))"
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
  "_10302" :: "N_2" ("'_10302")

defs
  "_10302_def": "(op ==::N_2 => N_2 => prop) (_10302::N_2)
 ((_mk_2::bool recspace => N_2)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     (0::nat) ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"

lemma DEF__10302: "(op =::N_2 => N_2 => bool) (_10302::N_2)
 ((_mk_2::bool recspace => N_2)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     (0::nat) ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"
  by (import hollight DEF__10302)

consts
  "_10303" :: "N_2" ("'_10303")

defs
  "_10303_def": "(op ==::N_2 => N_2 => prop) (_10303::N_2)
 ((_mk_2::bool recspace => N_2)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) (0::nat))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"

lemma DEF__10303: "(op =::N_2 => N_2 => bool) (_10303::N_2)
 ((_mk_2::bool recspace => N_2)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) (0::nat))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"
  by (import hollight DEF__10303)

constdefs
  two_1 :: "N_2" 
  "two_1 == _10302"

lemma DEF_two_1: "two_1 = _10302"
  by (import hollight DEF_two_1)

constdefs
  two_2 :: "N_2" 
  "two_2 == _10303"

lemma DEF_two_2: "two_2 = _10303"
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
  "_10326" :: "N_3" ("'_10326")

defs
  "_10326_def": "(op ==::N_3 => N_3 => prop) (_10326::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     (0::nat) ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"

lemma DEF__10326: "(op =::N_3 => N_3 => bool) (_10326::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     (0::nat) ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"
  by (import hollight DEF__10326)

consts
  "_10327" :: "N_3" ("'_10327")

defs
  "_10327_def": "(op ==::N_3 => N_3 => prop) (_10327::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) (0::nat))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"

lemma DEF__10327: "(op =::N_3 => N_3 => bool) (_10327::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) (0::nat))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"
  by (import hollight DEF__10327)

consts
  "_10328" :: "N_3" ("'_10328")

defs
  "_10328_def": "(op ==::N_3 => N_3 => prop) (_10328::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) ((Suc::nat => nat) (0::nat)))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"

lemma DEF__10328: "(op =::N_3 => N_3 => bool) (_10328::N_3)
 ((_mk_3::bool recspace => N_3)
   ((CONSTR::nat => bool => (nat => bool recspace) => bool recspace)
     ((Suc::nat => nat) ((Suc::nat => nat) (0::nat)))
     ((Eps::(bool => bool) => bool) (%x::bool. True::bool))
     (%n::nat. BOTTOM::bool recspace)))"
  by (import hollight DEF__10328)

constdefs
  three_1 :: "N_3" 
  "three_1 == _10326"

lemma DEF_three_1: "three_1 = _10326"
  by (import hollight DEF_three_1)

constdefs
  three_2 :: "N_3" 
  "three_2 == _10327"

lemma DEF_three_2: "three_2 = _10327"
  by (import hollight DEF_three_2)

constdefs
  three_3 :: "N_3" 
  "three_3 == _10328"

lemma DEF_three_3: "three_3 = _10328"
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
  REPLICATE :: "nat => 'q_16860 => 'q_16860 hollight.list" 
  "REPLICATE ==
SOME REPLICATE::nat => 'q_16860::type => 'q_16860::type hollight.list.
   (ALL x::'q_16860::type. REPLICATE 0 x = NIL) &
   (ALL (n::nat) x::'q_16860::type.
       REPLICATE (Suc n) x = CONS x (REPLICATE n x))"

lemma DEF_REPLICATE: "REPLICATE =
(SOME REPLICATE::nat => 'q_16860::type => 'q_16860::type hollight.list.
    (ALL x::'q_16860::type. REPLICATE 0 x = NIL) &
    (ALL (n::nat) x::'q_16860::type.
        REPLICATE (Suc n) x = CONS x (REPLICATE n x)))"
  by (import hollight DEF_REPLICATE)

constdefs
  NULL :: "'q_16875 hollight.list => bool" 
  "NULL ==
SOME NULL::'q_16875::type hollight.list => bool.
   NULL NIL = True &
   (ALL (h::'q_16875::type) t::'q_16875::type hollight.list.
       NULL (CONS h t) = False)"

lemma DEF_NULL: "NULL =
(SOME NULL::'q_16875::type hollight.list => bool.
    NULL NIL = True &
    (ALL (h::'q_16875::type) t::'q_16875::type hollight.list.
        NULL (CONS h t) = False))"
  by (import hollight DEF_NULL)

constdefs
  ALL_list :: "('q_16895 => bool) => 'q_16895 hollight.list => bool" 
  "ALL_list ==
SOME u::('q_16895::type => bool) => 'q_16895::type hollight.list => bool.
   (ALL P::'q_16895::type => bool. u P NIL = True) &
   (ALL (h::'q_16895::type) (P::'q_16895::type => bool)
       t::'q_16895::type hollight.list. u P (CONS h t) = (P h & u P t))"

lemma DEF_ALL: "ALL_list =
(SOME u::('q_16895::type => bool) => 'q_16895::type hollight.list => bool.
    (ALL P::'q_16895::type => bool. u P NIL = True) &
    (ALL (h::'q_16895::type) (P::'q_16895::type => bool)
        t::'q_16895::type hollight.list. u P (CONS h t) = (P h & u P t)))"
  by (import hollight DEF_ALL)

consts
  EX :: "('q_16916 => bool) => 'q_16916 hollight.list => bool" ("EX")

defs
  EX_def: "EX ==
SOME u::('q_16916::type => bool) => 'q_16916::type hollight.list => bool.
   (ALL P::'q_16916::type => bool. u P NIL = False) &
   (ALL (h::'q_16916::type) (P::'q_16916::type => bool)
       t::'q_16916::type hollight.list. u P (CONS h t) = (P h | u P t))"

lemma DEF_EX: "EX =
(SOME u::('q_16916::type => bool) => 'q_16916::type hollight.list => bool.
    (ALL P::'q_16916::type => bool. u P NIL = False) &
    (ALL (h::'q_16916::type) (P::'q_16916::type => bool)
        t::'q_16916::type hollight.list. u P (CONS h t) = (P h | u P t)))"
  by (import hollight DEF_EX)

constdefs
  ITLIST :: "('q_16939 => 'q_16938 => 'q_16938)
=> 'q_16939 hollight.list => 'q_16938 => 'q_16938" 
  "ITLIST ==
SOME ITLIST::('q_16939::type => 'q_16938::type => 'q_16938::type)
             => 'q_16939::type hollight.list
                => 'q_16938::type => 'q_16938::type.
   (ALL (f::'q_16939::type => 'q_16938::type => 'q_16938::type)
       b::'q_16938::type. ITLIST f NIL b = b) &
   (ALL (h::'q_16939::type)
       (f::'q_16939::type => 'q_16938::type => 'q_16938::type)
       (t::'q_16939::type hollight.list) b::'q_16938::type.
       ITLIST f (CONS h t) b = f h (ITLIST f t b))"

lemma DEF_ITLIST: "ITLIST =
(SOME ITLIST::('q_16939::type => 'q_16938::type => 'q_16938::type)
              => 'q_16939::type hollight.list
                 => 'q_16938::type => 'q_16938::type.
    (ALL (f::'q_16939::type => 'q_16938::type => 'q_16938::type)
        b::'q_16938::type. ITLIST f NIL b = b) &
    (ALL (h::'q_16939::type)
        (f::'q_16939::type => 'q_16938::type => 'q_16938::type)
        (t::'q_16939::type hollight.list) b::'q_16938::type.
        ITLIST f (CONS h t) b = f h (ITLIST f t b)))"
  by (import hollight DEF_ITLIST)

constdefs
  MEM :: "'q_16964 => 'q_16964 hollight.list => bool" 
  "MEM ==
SOME MEM::'q_16964::type => 'q_16964::type hollight.list => bool.
   (ALL x::'q_16964::type. MEM x NIL = False) &
   (ALL (h::'q_16964::type) (x::'q_16964::type)
       t::'q_16964::type hollight.list.
       MEM x (CONS h t) = (x = h | MEM x t))"

lemma DEF_MEM: "MEM =
(SOME MEM::'q_16964::type => 'q_16964::type hollight.list => bool.
    (ALL x::'q_16964::type. MEM x NIL = False) &
    (ALL (h::'q_16964::type) (x::'q_16964::type)
        t::'q_16964::type hollight.list.
        MEM x (CONS h t) = (x = h | MEM x t)))"
  by (import hollight DEF_MEM)

constdefs
  ALL2 :: "('q_16997 => 'q_17004 => bool)
=> 'q_16997 hollight.list => 'q_17004 hollight.list => bool" 
  "ALL2 ==
SOME ALL2::('q_16997::type => 'q_17004::type => bool)
           => 'q_16997::type hollight.list
              => 'q_17004::type hollight.list => bool.
   (ALL (P::'q_16997::type => 'q_17004::type => bool)
       l2::'q_17004::type hollight.list. ALL2 P NIL l2 = (l2 = NIL)) &
   (ALL (h1::'q_16997::type) (P::'q_16997::type => 'q_17004::type => bool)
       (t1::'q_16997::type hollight.list) l2::'q_17004::type hollight.list.
       ALL2 P (CONS h1 t1) l2 =
       COND (l2 = NIL) False (P h1 (HD l2) & ALL2 P t1 (TL l2)))"

lemma DEF_ALL2: "ALL2 =
(SOME ALL2::('q_16997::type => 'q_17004::type => bool)
            => 'q_16997::type hollight.list
               => 'q_17004::type hollight.list => bool.
    (ALL (P::'q_16997::type => 'q_17004::type => bool)
        l2::'q_17004::type hollight.list. ALL2 P NIL l2 = (l2 = NIL)) &
    (ALL (h1::'q_16997::type) (P::'q_16997::type => 'q_17004::type => bool)
        (t1::'q_16997::type hollight.list) l2::'q_17004::type hollight.list.
        ALL2 P (CONS h1 t1) l2 =
        COND (l2 = NIL) False (P h1 (HD l2) & ALL2 P t1 (TL l2))))"
  by (import hollight DEF_ALL2)

lemma ALL2: "ALL2 (P::'q_17059::type => 'q_17058::type => bool) NIL NIL = True &
ALL2 P (CONS (h1::'q_17059::type) (t1::'q_17059::type hollight.list)) NIL =
False &
ALL2 P NIL (CONS (h2::'q_17058::type) (t2::'q_17058::type hollight.list)) =
False &
ALL2 P (CONS h1 t1) (CONS h2 t2) = (P h1 h2 & ALL2 P t1 t2)"
  by (import hollight ALL2)

constdefs
  MAP2 :: "('q_17089 => 'q_17096 => 'q_17086)
=> 'q_17089 hollight.list
   => 'q_17096 hollight.list => 'q_17086 hollight.list" 
  "MAP2 ==
SOME MAP2::('q_17089::type => 'q_17096::type => 'q_17086::type)
           => 'q_17089::type hollight.list
              => 'q_17096::type hollight.list
                 => 'q_17086::type hollight.list.
   (ALL (f::'q_17089::type => 'q_17096::type => 'q_17086::type)
       l::'q_17096::type hollight.list. MAP2 f NIL l = NIL) &
   (ALL (h1::'q_17089::type)
       (f::'q_17089::type => 'q_17096::type => 'q_17086::type)
       (t1::'q_17089::type hollight.list) l::'q_17096::type hollight.list.
       MAP2 f (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l)))"

lemma DEF_MAP2: "MAP2 =
(SOME MAP2::('q_17089::type => 'q_17096::type => 'q_17086::type)
            => 'q_17089::type hollight.list
               => 'q_17096::type hollight.list
                  => 'q_17086::type hollight.list.
    (ALL (f::'q_17089::type => 'q_17096::type => 'q_17086::type)
        l::'q_17096::type hollight.list. MAP2 f NIL l = NIL) &
    (ALL (h1::'q_17089::type)
        (f::'q_17089::type => 'q_17096::type => 'q_17086::type)
        (t1::'q_17089::type hollight.list) l::'q_17096::type hollight.list.
        MAP2 f (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l))))"
  by (import hollight DEF_MAP2)

lemma MAP2: "MAP2 (f::'q_17131::type => 'q_17130::type => 'q_17137::type) NIL NIL = NIL &
MAP2 f (CONS (h1::'q_17131::type) (t1::'q_17131::type hollight.list))
 (CONS (h2::'q_17130::type) (t2::'q_17130::type hollight.list)) =
CONS (f h1 h2) (MAP2 f t1 t2)"
  by (import hollight MAP2)

constdefs
  EL :: "nat => 'q_17157 hollight.list => 'q_17157" 
  "EL ==
SOME EL::nat => 'q_17157::type hollight.list => 'q_17157::type.
   (ALL l::'q_17157::type hollight.list. EL 0 l = HD l) &
   (ALL (n::nat) l::'q_17157::type hollight.list.
       EL (Suc n) l = EL n (TL l))"

lemma DEF_EL: "EL =
(SOME EL::nat => 'q_17157::type hollight.list => 'q_17157::type.
    (ALL l::'q_17157::type hollight.list. EL 0 l = HD l) &
    (ALL (n::nat) l::'q_17157::type hollight.list.
        EL (Suc n) l = EL n (TL l)))"
  by (import hollight DEF_EL)

constdefs
  FILTER :: "('q_17182 => bool) => 'q_17182 hollight.list => 'q_17182 hollight.list" 
  "FILTER ==
SOME FILTER::('q_17182::type => bool)
             => 'q_17182::type hollight.list
                => 'q_17182::type hollight.list.
   (ALL P::'q_17182::type => bool. FILTER P NIL = NIL) &
   (ALL (h::'q_17182::type) (P::'q_17182::type => bool)
       t::'q_17182::type hollight.list.
       FILTER P (CONS h t) = COND (P h) (CONS h (FILTER P t)) (FILTER P t))"

lemma DEF_FILTER: "FILTER =
(SOME FILTER::('q_17182::type => bool)
              => 'q_17182::type hollight.list
                 => 'q_17182::type hollight.list.
    (ALL P::'q_17182::type => bool. FILTER P NIL = NIL) &
    (ALL (h::'q_17182::type) (P::'q_17182::type => bool)
        t::'q_17182::type hollight.list.
        FILTER P (CONS h t) =
        COND (P h) (CONS h (FILTER P t)) (FILTER P t)))"
  by (import hollight DEF_FILTER)

constdefs
  ASSOC :: "'q_17211 => ('q_17211 * 'q_17205) hollight.list => 'q_17205" 
  "ASSOC ==
SOME ASSOC::'q_17211::type
            => ('q_17211::type * 'q_17205::type) hollight.list
               => 'q_17205::type.
   ALL (h::'q_17211::type * 'q_17205::type) (a::'q_17211::type)
      t::('q_17211::type * 'q_17205::type) hollight.list.
      ASSOC a (CONS h t) = COND (fst h = a) (snd h) (ASSOC a t)"

lemma DEF_ASSOC: "ASSOC =
(SOME ASSOC::'q_17211::type
             => ('q_17211::type * 'q_17205::type) hollight.list
                => 'q_17205::type.
    ALL (h::'q_17211::type * 'q_17205::type) (a::'q_17211::type)
       t::('q_17211::type * 'q_17205::type) hollight.list.
       ASSOC a (CONS h t) = COND (fst h = a) (snd h) (ASSOC a t))"
  by (import hollight DEF_ASSOC)

constdefs
  ITLIST2 :: "('q_17235 => 'q_17243 => 'q_17233 => 'q_17233)
=> 'q_17235 hollight.list => 'q_17243 hollight.list => 'q_17233 => 'q_17233" 
  "ITLIST2 ==
SOME ITLIST2::('q_17235::type
               => 'q_17243::type => 'q_17233::type => 'q_17233::type)
              => 'q_17235::type hollight.list
                 => 'q_17243::type hollight.list
                    => 'q_17233::type => 'q_17233::type.
   (ALL (f::'q_17235::type
            => 'q_17243::type => 'q_17233::type => 'q_17233::type)
       (l2::'q_17243::type hollight.list) b::'q_17233::type.
       ITLIST2 f NIL l2 b = b) &
   (ALL (h1::'q_17235::type)
       (f::'q_17235::type
           => 'q_17243::type => 'q_17233::type => 'q_17233::type)
       (t1::'q_17235::type hollight.list) (l2::'q_17243::type hollight.list)
       b::'q_17233::type.
       ITLIST2 f (CONS h1 t1) l2 b = f h1 (HD l2) (ITLIST2 f t1 (TL l2) b))"

lemma DEF_ITLIST2: "ITLIST2 =
(SOME ITLIST2::('q_17235::type
                => 'q_17243::type => 'q_17233::type => 'q_17233::type)
               => 'q_17235::type hollight.list
                  => 'q_17243::type hollight.list
                     => 'q_17233::type => 'q_17233::type.
    (ALL (f::'q_17235::type
             => 'q_17243::type => 'q_17233::type => 'q_17233::type)
        (l2::'q_17243::type hollight.list) b::'q_17233::type.
        ITLIST2 f NIL l2 b = b) &
    (ALL (h1::'q_17235::type)
        (f::'q_17235::type
            => 'q_17243::type => 'q_17233::type => 'q_17233::type)
        (t1::'q_17235::type hollight.list)
        (l2::'q_17243::type hollight.list) b::'q_17233::type.
        ITLIST2 f (CONS h1 t1) l2 b =
        f h1 (HD l2) (ITLIST2 f t1 (TL l2) b)))"
  by (import hollight DEF_ITLIST2)

lemma ITLIST2: "ITLIST2
 (f::'q_17277::type => 'q_17276::type => 'q_17275::type => 'q_17275::type)
 NIL NIL (b::'q_17275::type) =
b &
ITLIST2 f (CONS (h1::'q_17277::type) (t1::'q_17277::type hollight.list))
 (CONS (h2::'q_17276::type) (t2::'q_17276::type hollight.list)) b =
f h1 h2 (ITLIST2 f t1 t2 b)"
  by (import hollight ITLIST2)

consts
  ZIP :: "'q_17307 hollight.list
=> 'q_17315 hollight.list => ('q_17307 * 'q_17315) hollight.list" 

defs
  ZIP_def: "hollight.ZIP ==
SOME ZIP::'q_17307::type hollight.list
          => 'q_17315::type hollight.list
             => ('q_17307::type * 'q_17315::type) hollight.list.
   (ALL l2::'q_17315::type hollight.list. ZIP NIL l2 = NIL) &
   (ALL (h1::'q_17307::type) (t1::'q_17307::type hollight.list)
       l2::'q_17315::type hollight.list.
       ZIP (CONS h1 t1) l2 = CONS (h1, HD l2) (ZIP t1 (TL l2)))"

lemma DEF_ZIP: "hollight.ZIP =
(SOME ZIP::'q_17307::type hollight.list
           => 'q_17315::type hollight.list
              => ('q_17307::type * 'q_17315::type) hollight.list.
    (ALL l2::'q_17315::type hollight.list. ZIP NIL l2 = NIL) &
    (ALL (h1::'q_17307::type) (t1::'q_17307::type hollight.list)
        l2::'q_17315::type hollight.list.
        ZIP (CONS h1 t1) l2 = CONS (h1, HD l2) (ZIP t1 (TL l2))))"
  by (import hollight DEF_ZIP)

lemma ZIP: "(op &::bool => bool => bool)
 ((op =::('q_17326::type * 'q_17327::type) hollight.list
         => ('q_17326::type * 'q_17327::type) hollight.list => bool)
   ((hollight.ZIP::'q_17326::type hollight.list
                   => 'q_17327::type hollight.list
                      => ('q_17326::type * 'q_17327::type) hollight.list)
     (NIL::'q_17326::type hollight.list)
     (NIL::'q_17327::type hollight.list))
   (NIL::('q_17326::type * 'q_17327::type) hollight.list))
 ((op =::('q_17351::type * 'q_17352::type) hollight.list
         => ('q_17351::type * 'q_17352::type) hollight.list => bool)
   ((hollight.ZIP::'q_17351::type hollight.list
                   => 'q_17352::type hollight.list
                      => ('q_17351::type * 'q_17352::type) hollight.list)
     ((CONS::'q_17351::type
             => 'q_17351::type hollight.list
                => 'q_17351::type hollight.list)
       (h1::'q_17351::type) (t1::'q_17351::type hollight.list))
     ((CONS::'q_17352::type
             => 'q_17352::type hollight.list
                => 'q_17352::type hollight.list)
       (h2::'q_17352::type) (t2::'q_17352::type hollight.list)))
   ((CONS::'q_17351::type * 'q_17352::type
           => ('q_17351::type * 'q_17352::type) hollight.list
              => ('q_17351::type * 'q_17352::type) hollight.list)
     ((Pair::'q_17351::type
             => 'q_17352::type => 'q_17351::type * 'q_17352::type)
       h1 h2)
     ((hollight.ZIP::'q_17351::type hollight.list
                     => 'q_17352::type hollight.list
                        => ('q_17351::type * 'q_17352::type) hollight.list)
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

lemma LENGTH_EQ_CONS: "ALL (l::'q_17659::type hollight.list) n::nat.
   (LENGTH l = Suc n) =
   (EX (h::'q_17659::type) t::'q_17659::type hollight.list.
       l = CONS h t & LENGTH t = n)"
  by (import hollight LENGTH_EQ_CONS)

lemma MAP_o: "ALL (f::'A::type => 'B::type) (g::'B::type => 'C::type)
   l::'A::type hollight.list. MAP (g o f) l = MAP g (MAP f l)"
  by (import hollight MAP_o)

lemma MAP_EQ: "ALL (f::'q_17723::type => 'q_17734::type)
   (g::'q_17723::type => 'q_17734::type) l::'q_17723::type hollight.list.
   ALL_list (%x::'q_17723::type. f x = g x) l --> MAP f l = MAP g l"
  by (import hollight MAP_EQ)

lemma ALL_IMP: "ALL (P::'q_17764::type => bool) (Q::'q_17764::type => bool)
   l::'q_17764::type hollight.list.
   (ALL x::'q_17764::type. MEM x l & P x --> Q x) & ALL_list P l -->
   ALL_list Q l"
  by (import hollight ALL_IMP)

lemma NOT_EX: "ALL (P::'q_17792::type => bool) l::'q_17792::type hollight.list.
   (~ EX P l) = ALL_list (%x::'q_17792::type. ~ P x) l"
  by (import hollight NOT_EX)

lemma NOT_ALL: "ALL (P::'q_17814::type => bool) l::'q_17814::type hollight.list.
   (~ ALL_list P l) = EX (%x::'q_17814::type. ~ P x) l"
  by (import hollight NOT_ALL)

lemma ALL_MAP: "ALL (P::'q_17836::type => bool) (f::'q_17835::type => 'q_17836::type)
   l::'q_17835::type hollight.list.
   ALL_list P (MAP f l) = ALL_list (P o f) l"
  by (import hollight ALL_MAP)

lemma ALL_T: "All (ALL_list (%x::'q_17854::type. True))"
  by (import hollight ALL_T)

lemma MAP_EQ_ALL2: "ALL (l::'q_17879::type hollight.list) m::'q_17879::type hollight.list.
   ALL2
    (%(x::'q_17879::type) y::'q_17879::type.
        (f::'q_17879::type => 'q_17890::type) x = f y)
    l m -->
   MAP f l = MAP f m"
  by (import hollight MAP_EQ_ALL2)

lemma ALL2_MAP: "ALL (P::'q_17921::type => 'q_17922::type => bool)
   (f::'q_17922::type => 'q_17921::type) l::'q_17922::type hollight.list.
   ALL2 P (MAP f l) l = ALL_list (%a::'q_17922::type. P (f a) a) l"
  by (import hollight ALL2_MAP)

lemma MAP_EQ_DEGEN: "ALL (l::'q_17939::type hollight.list) f::'q_17939::type => 'q_17939::type.
   ALL_list (%x::'q_17939::type. f x = x) l --> MAP f l = l"
  by (import hollight MAP_EQ_DEGEN)

lemma ALL2_AND_RIGHT: "ALL (l::'q_17982::type hollight.list) (m::'q_17981::type hollight.list)
   (P::'q_17982::type => bool) Q::'q_17982::type => 'q_17981::type => bool.
   ALL2 (%(x::'q_17982::type) y::'q_17981::type. P x & Q x y) l m =
   (ALL_list P l & ALL2 Q l m)"
  by (import hollight ALL2_AND_RIGHT)

lemma ITLIST_EXTRA: "ALL l::'q_18019::type hollight.list.
   ITLIST (f::'q_18019::type => 'q_18018::type => 'q_18018::type)
    (APPEND l (CONS (a::'q_18019::type) NIL)) (b::'q_18018::type) =
   ITLIST f l (f a b)"
  by (import hollight ITLIST_EXTRA)

lemma ALL_MP: "ALL (P::'q_18045::type => bool) (Q::'q_18045::type => bool)
   l::'q_18045::type hollight.list.
   ALL_list (%x::'q_18045::type. P x --> Q x) l & ALL_list P l -->
   ALL_list Q l"
  by (import hollight ALL_MP)

lemma AND_ALL: "ALL x::'q_18075::type hollight.list.
   (ALL_list (P::'q_18075::type => bool) x &
    ALL_list (Q::'q_18075::type => bool) x) =
   ALL_list (%x::'q_18075::type. P x & Q x) x"
  by (import hollight AND_ALL)

lemma EX_IMP: "ALL (P::'q_18105::type => bool) (Q::'q_18105::type => bool)
   l::'q_18105::type hollight.list.
   (ALL x::'q_18105::type. MEM x l & P x --> Q x) & EX P l --> EX Q l"
  by (import hollight EX_IMP)

lemma ALL_MEM: "ALL (P::'q_18132::type => bool) l::'q_18132::type hollight.list.
   (ALL x::'q_18132::type. MEM x l --> P x) = ALL_list P l"
  by (import hollight ALL_MEM)

lemma LENGTH_REPLICATE: "ALL (n::nat) x::'q_18150::type. LENGTH (REPLICATE n x) = n"
  by (import hollight LENGTH_REPLICATE)

lemma EX_MAP: "ALL (P::'q_18174::type => bool) (f::'q_18173::type => 'q_18174::type)
   l::'q_18173::type hollight.list. EX P (MAP f l) = EX (P o f) l"
  by (import hollight EX_MAP)

lemma EXISTS_EX: "ALL (P::'q_18212::type => 'q_18211::type => bool)
   l::'q_18211::type hollight.list.
   (EX x::'q_18212::type. EX (P x) l) =
   EX (%s::'q_18211::type. EX x::'q_18212::type. P x s) l"
  by (import hollight EXISTS_EX)

lemma FORALL_ALL: "ALL (P::'q_18242::type => 'q_18241::type => bool)
   l::'q_18241::type hollight.list.
   (ALL x::'q_18242::type. ALL_list (P x) l) =
   ALL_list (%s::'q_18241::type. ALL x::'q_18242::type. P x s) l"
  by (import hollight FORALL_ALL)

lemma MEM_APPEND: "ALL (x::'q_18270::type) (l1::'q_18270::type hollight.list)
   l2::'q_18270::type hollight.list.
   MEM x (APPEND l1 l2) = (MEM x l1 | MEM x l2)"
  by (import hollight MEM_APPEND)

lemma MEM_MAP: "ALL (f::'q_18306::type => 'q_18303::type) (y::'q_18303::type)
   l::'q_18306::type hollight.list.
   MEM y (MAP f l) = (EX x::'q_18306::type. MEM x l & y = f x)"
  by (import hollight MEM_MAP)

lemma FILTER_APPEND: "ALL (P::'q_18337::type => bool) (l1::'q_18337::type hollight.list)
   l2::'q_18337::type hollight.list.
   FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)"
  by (import hollight FILTER_APPEND)

lemma FILTER_MAP: "ALL (P::'q_18364::type => bool) (f::'q_18371::type => 'q_18364::type)
   l::'q_18371::type hollight.list.
   FILTER P (MAP f l) = MAP f (FILTER (P o f) l)"
  by (import hollight FILTER_MAP)

lemma MEM_FILTER: "ALL (P::'q_18398::type => bool) (l::'q_18398::type hollight.list)
   x::'q_18398::type. MEM x (FILTER P l) = (P x & MEM x l)"
  by (import hollight MEM_FILTER)

lemma EX_MEM: "ALL (P::'q_18419::type => bool) l::'q_18419::type hollight.list.
   (EX x::'q_18419::type. P x & MEM x l) = EX P l"
  by (import hollight EX_MEM)

lemma MAP_FST_ZIP: "ALL (l1::'q_18439::type hollight.list) l2::'q_18441::type hollight.list.
   LENGTH l1 = LENGTH l2 --> MAP fst (hollight.ZIP l1 l2) = l1"
  by (import hollight MAP_FST_ZIP)

lemma MAP_SND_ZIP: "ALL (l1::'q_18470::type hollight.list) l2::'q_18472::type hollight.list.
   LENGTH l1 = LENGTH l2 --> MAP snd (hollight.ZIP l1 l2) = l2"
  by (import hollight MAP_SND_ZIP)

lemma MEM_ASSOC: "ALL (l::('q_18516::type * 'q_18500::type) hollight.list) x::'q_18516::type.
   MEM (x, ASSOC x l) l = MEM x (MAP fst l)"
  by (import hollight MEM_ASSOC)

lemma ALL_APPEND: "ALL (P::'q_18537::type => bool) (l1::'q_18537::type hollight.list)
   l2::'q_18537::type hollight.list.
   ALL_list P (APPEND l1 l2) = (ALL_list P l1 & ALL_list P l2)"
  by (import hollight ALL_APPEND)

lemma MEM_EL: "ALL (l::'q_18560::type hollight.list) n::nat.
   < n (LENGTH l) --> MEM (EL n l) l"
  by (import hollight MEM_EL)

lemma ALL2_MAP2: "ALL (l::'q_18603::type hollight.list) m::'q_18604::type hollight.list.
   ALL2 (P::'q_18602::type => 'q_18601::type => bool)
    (MAP (f::'q_18603::type => 'q_18602::type) l)
    (MAP (g::'q_18604::type => 'q_18601::type) m) =
   ALL2 (%(x::'q_18603::type) y::'q_18604::type. P (f x) (g y)) l m"
  by (import hollight ALL2_MAP2)

lemma AND_ALL2: "ALL (P::'q_18650::type => 'q_18649::type => bool)
   (Q::'q_18650::type => 'q_18649::type => bool)
   (x::'q_18650::type hollight.list) xa::'q_18649::type hollight.list.
   (ALL2 P x xa & ALL2 Q x xa) =
   ALL2 (%(x::'q_18650::type) y::'q_18649::type. P x y & Q x y) x xa"
  by (import hollight AND_ALL2)

lemma ALL2_ALL: "ALL (P::'q_18672::type => 'q_18672::type => bool)
   l::'q_18672::type hollight.list.
   ALL2 P l l = ALL_list (%x::'q_18672::type. P x x) l"
  by (import hollight ALL2_ALL)

lemma APPEND_EQ_NIL: "ALL (x::'q_18701::type hollight.list) xa::'q_18701::type hollight.list.
   (APPEND x xa = NIL) = (x = NIL & xa = NIL)"
  by (import hollight APPEND_EQ_NIL)

lemma LENGTH_MAP2: "ALL (f::'q_18721::type => 'q_18723::type => 'q_18734::type)
   (l::'q_18721::type hollight.list) m::'q_18723::type hollight.list.
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

lemma REAL_MUL_RZERO: "ALL x::hollight.real. real_mul x (real_of_num 0) = real_of_num 0"
  by (import hollight REAL_MUL_RZERO)

lemma REAL_MUL_LZERO: "ALL x::hollight.real. real_mul (real_of_num 0) x = real_of_num 0"
  by (import hollight REAL_MUL_LZERO)

lemma REAL_NEG_NEG: "ALL x::hollight.real. real_neg (real_neg x) = x"
  by (import hollight REAL_NEG_NEG)

lemma REAL_MUL_RNEG: "ALL (x::hollight.real) y::hollight.real.
   real_mul x (real_neg y) = real_neg (real_mul x y)"
  by (import hollight REAL_MUL_RNEG)

lemma REAL_MUL_LNEG: "ALL (x::hollight.real) y::hollight.real.
   real_mul (real_neg x) y = real_neg (real_mul x y)"
  by (import hollight REAL_MUL_LNEG)

lemma REAL_NEG_ADD: "ALL (x::hollight.real) y::hollight.real.
   real_neg (real_add x y) = real_add (real_neg x) (real_neg y)"
  by (import hollight REAL_NEG_ADD)

lemma REAL_ADD_RID: "ALL x::hollight.real. real_add x (real_of_num 0) = x"
  by (import hollight REAL_ADD_RID)

lemma REAL_NEG_0: "real_neg (real_of_num 0) = real_of_num 0"
  by (import hollight REAL_NEG_0)

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

lemma REAL_LT_IMP_LE: "ALL (x::hollight.real) y::hollight.real. real_lt x y --> real_le x y"
  by (import hollight REAL_LT_IMP_LE)

lemma REAL_LTE_TRANS: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt x y & real_le y z --> real_lt x z"
  by (import hollight REAL_LTE_TRANS)

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

lemma REAL_SUB_LE: "ALL (x::hollight.real) xa::hollight.real.
   real_le (real_of_num 0) (real_sub x xa) = real_le xa x"
  by (import hollight REAL_SUB_LE)

lemma REAL_NEG_SUB: "ALL (x::hollight.real) xa::hollight.real.
   real_neg (real_sub x xa) = real_sub xa x"
  by (import hollight REAL_NEG_SUB)

lemma REAL_LE_LT: "ALL (x::hollight.real) xa::hollight.real.
   real_le x xa = (real_lt x xa | x = xa)"
  by (import hollight REAL_LE_LT)

lemma REAL_SUB_LT: "ALL (x::hollight.real) xa::hollight.real.
   real_lt (real_of_num 0) (real_sub x xa) = real_lt xa x"
  by (import hollight REAL_SUB_LT)

lemma REAL_NOT_LT: "ALL (x::hollight.real) xa::hollight.real. (~ real_lt x xa) = real_le xa x"
  by (import hollight REAL_NOT_LT)

lemma REAL_SUB_0: "ALL (x::hollight.real) y::hollight.real.
   (real_sub x y = real_of_num 0) = (x = y)"
  by (import hollight REAL_SUB_0)

lemma REAL_LT_LE: "ALL (x::hollight.real) y::hollight.real.
   real_lt x y = (real_le x y & x ~= y)"
  by (import hollight REAL_LT_LE)

lemma REAL_LT_REFL: "ALL x::hollight.real. ~ real_lt x x"
  by (import hollight REAL_LT_REFL)

lemma REAL_LTE_ADD: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_le (real_of_num 0) y -->
   real_lt (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LTE_ADD)

lemma REAL_LET_ADD: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_of_num 0) x & real_lt (real_of_num 0) y -->
   real_lt (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LET_ADD)

lemma REAL_LT_ADD: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_of_num 0) x & real_lt (real_of_num 0) y -->
   real_lt (real_of_num 0) (real_add x y)"
  by (import hollight REAL_LT_ADD)

lemma REAL_ENTIRE: "ALL (x::hollight.real) y::hollight.real.
   (real_mul x y = real_of_num 0) = (x = real_of_num 0 | y = real_of_num 0)"
  by (import hollight REAL_ENTIRE)

lemma REAL_LE_NEGTOTAL: "ALL x::hollight.real.
   real_le (real_of_num 0) x | real_le (real_of_num 0) (real_neg x)"
  by (import hollight REAL_LE_NEGTOTAL)

lemma REAL_LE_SQUARE: "ALL x::hollight.real. real_le (real_of_num 0) (real_mul x x)"
  by (import hollight REAL_LE_SQUARE)

lemma REAL_MUL_RID: "ALL x::hollight.real. real_mul x (real_of_num (NUMERAL_BIT1 0)) = x"
  by (import hollight REAL_MUL_RID)

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

lemma REAL_POS: "ALL x::nat. real_le (real_of_num 0) (real_of_num x)"
  by (import hollight REAL_POS)

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

lemma REAL_LNEG_UNIQ: "ALL (x::hollight.real) y::hollight.real.
   (real_add x y = real_of_num 0) = (x = real_neg y)"
  by (import hollight REAL_LNEG_UNIQ)

lemma REAL_RNEG_UNIQ: "ALL (x::hollight.real) y::hollight.real.
   (real_add x y = real_of_num 0) = (y = real_neg x)"
  by (import hollight REAL_RNEG_UNIQ)

lemma REAL_NEG_LMUL: "ALL (x::hollight.real) y::hollight.real.
   real_neg (real_mul x y) = real_mul (real_neg x) y"
  by (import hollight REAL_NEG_LMUL)

lemma REAL_NEG_RMUL: "ALL (x::hollight.real) y::hollight.real.
   real_neg (real_mul x y) = real_mul x (real_neg y)"
  by (import hollight REAL_NEG_RMUL)

lemma REAL_NEGNEG: "ALL x::hollight.real. real_neg (real_neg x) = x"
  by (import hollight REAL_NEGNEG)

lemma REAL_NEG_MUL2: "ALL (x::hollight.real) y::hollight.real.
   real_mul (real_neg x) (real_neg y) = real_mul x y"
  by (import hollight REAL_NEG_MUL2)

lemma REAL_LT_LADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_add x y) (real_add x z) = real_lt y z"
  by (import hollight REAL_LT_LADD)

lemma REAL_LT_RADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_add x z) (real_add y z) = real_lt x y"
  by (import hollight REAL_LT_RADD)

lemma REAL_LT_ANTISYM: "ALL (x::hollight.real) y::hollight.real. ~ (real_lt x y & real_lt y x)"
  by (import hollight REAL_LT_ANTISYM)

lemma REAL_LT_GT: "ALL (x::hollight.real) y::hollight.real. real_lt x y --> ~ real_lt y x"
  by (import hollight REAL_LT_GT)

lemma REAL_NOT_EQ: "ALL (x::hollight.real) y::hollight.real.
   (x ~= y) = (real_lt x y | real_lt y x)"
  by (import hollight REAL_NOT_EQ)

lemma REAL_LE_TOTAL: "ALL (x::hollight.real) y::hollight.real. real_le x y | real_le y x"
  by (import hollight REAL_LE_TOTAL)

lemma REAL_LE_REFL: "ALL x::hollight.real. real_le x x"
  by (import hollight REAL_LE_REFL)

lemma REAL_LE_ANTISYM: "ALL (x::hollight.real) y::hollight.real.
   (real_le x y & real_le y x) = (x = y)"
  by (import hollight REAL_LE_ANTISYM)

lemma REAL_LET_ANTISYM: "ALL (x::hollight.real) y::hollight.real. ~ (real_le x y & real_lt y x)"
  by (import hollight REAL_LET_ANTISYM)

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

lemma REAL_LT_TOTAL: "ALL (x::hollight.real) y::hollight.real. x = y | real_lt x y | real_lt y x"
  by (import hollight REAL_LT_TOTAL)

lemma REAL_LT_NEGTOTAL: "ALL x::hollight.real.
   x = real_of_num 0 |
   real_lt (real_of_num 0) x | real_lt (real_of_num 0) (real_neg x)"
  by (import hollight REAL_LT_NEGTOTAL)

lemma REAL_LE_01: "real_le (real_of_num 0) (real_of_num (NUMERAL_BIT1 0))"
  by (import hollight REAL_LE_01)

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

lemma REAL_LE_DOUBLE: "ALL x::hollight.real.
   real_le (real_of_num 0) (real_add x x) = real_le (real_of_num 0) x"
  by (import hollight REAL_LE_DOUBLE)

lemma REAL_LE_NEGL: "ALL x::hollight.real. real_le (real_neg x) x = real_le (real_of_num 0) x"
  by (import hollight REAL_LE_NEGL)

lemma REAL_LE_NEGR: "ALL x::hollight.real. real_le x (real_neg x) = real_le x (real_of_num 0)"
  by (import hollight REAL_LE_NEGR)

lemma REAL_NEG_EQ_0: "ALL x::hollight.real. (real_neg x = real_of_num 0) = (x = real_of_num 0)"
  by (import hollight REAL_NEG_EQ_0)

lemma REAL_ADD_SUB: "ALL (x::hollight.real) y::hollight.real. real_sub (real_add x y) x = y"
  by (import hollight REAL_ADD_SUB)

lemma REAL_NEG_EQ: "ALL (x::hollight.real) y::hollight.real. (real_neg x = y) = (x = real_neg y)"
  by (import hollight REAL_NEG_EQ)

lemma REAL_NEG_MINUS1: "ALL x::hollight.real.
   real_neg x = real_mul (real_neg (real_of_num (NUMERAL_BIT1 0))) x"
  by (import hollight REAL_NEG_MINUS1)

lemma REAL_LT_IMP_NE: "ALL (x::hollight.real) y::hollight.real. real_lt x y --> x ~= y"
  by (import hollight REAL_LT_IMP_NE)

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

lemma REAL_ADD2_SUB2: "ALL (a::hollight.real) (b::hollight.real) (c::hollight.real)
   d::hollight.real.
   real_sub (real_add a b) (real_add c d) =
   real_add (real_sub a c) (real_sub b d)"
  by (import hollight REAL_ADD2_SUB2)

lemma REAL_SUB_LZERO: "ALL x::hollight.real. real_sub (real_of_num 0) x = real_neg x"
  by (import hollight REAL_SUB_LZERO)

lemma REAL_SUB_RZERO: "ALL x::hollight.real. real_sub x (real_of_num 0) = x"
  by (import hollight REAL_SUB_RZERO)

lemma REAL_LET_ADD2: "ALL (w::hollight.real) (x::hollight.real) (y::hollight.real)
   z::hollight.real.
   real_le w x & real_lt y z --> real_lt (real_add w y) (real_add x z)"
  by (import hollight REAL_LET_ADD2)

lemma REAL_LTE_ADD2: "ALL (w::hollight.real) (x::hollight.real) (y::hollight.real)
   z::hollight.real.
   real_lt w x & real_le y z --> real_lt (real_add w y) (real_add x z)"
  by (import hollight REAL_LTE_ADD2)

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

lemma REAL_EQ_SUB_LADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (x = real_sub y z) = (real_add x z = y)"
  by (import hollight REAL_EQ_SUB_LADD)

lemma REAL_EQ_SUB_RADD: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   (real_sub x y = z) = (x = real_add z y)"
  by (import hollight REAL_EQ_SUB_RADD)

lemma REAL_SUB_SUB2: "ALL (x::hollight.real) y::hollight.real. real_sub x (real_sub x y) = y"
  by (import hollight REAL_SUB_SUB2)

lemma REAL_ADD_SUB2: "ALL (x::hollight.real) y::hollight.real.
   real_sub x (real_add x y) = real_neg y"
  by (import hollight REAL_ADD_SUB2)

lemma REAL_EQ_IMP_LE: "ALL (x::hollight.real) y::hollight.real. x = y --> real_le x y"
  by (import hollight REAL_EQ_IMP_LE)

lemma REAL_POS_NZ: "ALL x::hollight.real. real_lt (real_of_num 0) x --> x ~= real_of_num 0"
  by (import hollight REAL_POS_NZ)

lemma REAL_DIFFSQ: "ALL (x::hollight.real) y::hollight.real.
   real_mul (real_add x y) (real_sub x y) =
   real_sub (real_mul x x) (real_mul y y)"
  by (import hollight REAL_DIFFSQ)

lemma REAL_EQ_NEG2: "ALL (x::hollight.real) y::hollight.real. (real_neg x = real_neg y) = (x = y)"
  by (import hollight REAL_EQ_NEG2)

lemma REAL_LT_NEG2: "ALL (x::hollight.real) y::hollight.real.
   real_lt (real_neg x) (real_neg y) = real_lt y x"
  by (import hollight REAL_LT_NEG2)

lemma REAL_SUB_LDISTRIB: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_mul x (real_sub y z) = real_sub (real_mul x y) (real_mul x z)"
  by (import hollight REAL_SUB_LDISTRIB)

lemma REAL_SUB_RDISTRIB: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_mul (real_sub x y) z = real_sub (real_mul x z) (real_mul y z)"
  by (import hollight REAL_SUB_RDISTRIB)

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

lemma REAL_SUB_ABS: "ALL (x::hollight.real) y::hollight.real.
   real_le (real_sub (real_abs x) (real_abs y)) (real_abs (real_sub x y))"
  by (import hollight REAL_SUB_ABS)

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

lemma REAL_MUL_RINV: "ALL x::hollight.real.
   x ~= real_of_num 0 -->
   real_mul x (real_inv x) = real_of_num (NUMERAL_BIT1 0)"
  by (import hollight REAL_MUL_RINV)

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

lemma REAL_LE_RMUL_EQ: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) z -->
   real_le (real_mul x z) (real_mul y z) = real_le x y"
  by (import hollight REAL_LE_RMUL_EQ)

lemma REAL_LE_LMUL_EQ: "ALL (x::hollight.real) (y::hollight.real) z::hollight.real.
   real_lt (real_of_num 0) z -->
   real_le (real_mul z x) (real_mul z y) = real_le x y"
  by (import hollight REAL_LE_LMUL_EQ)

lemma REAL_LT_RMUL_EQ: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) xb -->
   real_lt (real_mul x xb) (real_mul xa xb) = real_lt x xa"
  by (import hollight REAL_LT_RMUL_EQ)

lemma REAL_LT_LMUL_EQ: "ALL (x::hollight.real) (xa::hollight.real) xb::hollight.real.
   real_lt (real_of_num 0) xb -->
   real_lt (real_mul xb x) (real_mul xb xa) = real_lt x xa"
  by (import hollight REAL_LT_LMUL_EQ)

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

lemma REAL_SOS_EQ_0: "ALL (x::hollight.real) y::hollight.real.
   (real_add (real_pow x (NUMERAL_BIT0 (NUMERAL_BIT1 0)))
     (real_pow y (NUMERAL_BIT0 (NUMERAL_BIT1 0))) =
    real_of_num 0) =
   (x = real_of_num 0 & y = real_of_num 0)"
  by (import hollight REAL_SOS_EQ_0)

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
  SETSPEC :: "'q_37056 => bool => 'q_37056 => bool" 
  "SETSPEC == %(u::'q_37056::type) (ua::bool) ub::'q_37056::type. ua & u = ub"

lemma DEF_SETSPEC: "SETSPEC = (%(u::'q_37056::type) (ua::bool) ub::'q_37056::type. ua & u = ub)"
  by (import hollight DEF_SETSPEC)

lemma IN_ELIM_THM: "(ALL (P::(bool => 'q_37089::type => bool) => bool) x::'q_37089::type.
    IN x (GSPEC (%v::'q_37089::type. P (SETSPEC v))) =
    P (%(p::bool) t::'q_37089::type. p & x = t)) &
(ALL (p::'q_37120::type => bool) x::'q_37120::type.
    IN x
     (GSPEC (%v::'q_37120::type. EX y::'q_37120::type. SETSPEC v (p y) y)) =
    p x) &
(ALL (P::(bool => 'q_37148::type => bool) => bool) x::'q_37148::type.
    GSPEC (%v::'q_37148::type. P (SETSPEC v)) x =
    P (%(p::bool) t::'q_37148::type. p & x = t)) &
(ALL (p::'q_37177::type => bool) x::'q_37177::type.
    GSPEC (%v::'q_37177::type. EX y::'q_37177::type. SETSPEC v (p y) y) x =
    p x) &
(ALL (p::'q_37194::type => bool) x::'q_37194::type. IN x p = p x)"
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
  CARD_GE :: "('q_37693 => bool) => ('q_37690 => bool) => bool" 
  "CARD_GE ==
%(u::'q_37693::type => bool) ua::'q_37690::type => bool.
   EX f::'q_37693::type => 'q_37690::type.
      ALL y::'q_37690::type.
         IN y ua --> (EX x::'q_37693::type. IN x u & y = f x)"

lemma DEF_CARD_GE: "CARD_GE =
(%(u::'q_37693::type => bool) ua::'q_37690::type => bool.
    EX f::'q_37693::type => 'q_37690::type.
       ALL y::'q_37690::type.
          IN y ua --> (EX x::'q_37693::type. IN x u & y = f x))"
  by (import hollight DEF_CARD_GE)

constdefs
  CARD_LE :: "('q_37702 => bool) => ('q_37701 => bool) => bool" 
  "CARD_LE ==
%(u::'q_37702::type => bool) ua::'q_37701::type => bool. CARD_GE ua u"

lemma DEF_CARD_LE: "CARD_LE =
(%(u::'q_37702::type => bool) ua::'q_37701::type => bool. CARD_GE ua u)"
  by (import hollight DEF_CARD_LE)

constdefs
  CARD_EQ :: "('q_37712 => bool) => ('q_37713 => bool) => bool" 
  "CARD_EQ ==
%(u::'q_37712::type => bool) ua::'q_37713::type => bool.
   CARD_LE u ua & CARD_LE ua u"

lemma DEF_CARD_EQ: "CARD_EQ =
(%(u::'q_37712::type => bool) ua::'q_37713::type => bool.
    CARD_LE u ua & CARD_LE ua u)"
  by (import hollight DEF_CARD_EQ)

constdefs
  CARD_GT :: "('q_37727 => bool) => ('q_37728 => bool) => bool" 
  "CARD_GT ==
%(u::'q_37727::type => bool) ua::'q_37728::type => bool.
   CARD_GE u ua & ~ CARD_GE ua u"

lemma DEF_CARD_GT: "CARD_GT =
(%(u::'q_37727::type => bool) ua::'q_37728::type => bool.
    CARD_GE u ua & ~ CARD_GE ua u)"
  by (import hollight DEF_CARD_GT)

constdefs
  CARD_LT :: "('q_37743 => bool) => ('q_37744 => bool) => bool" 
  "CARD_LT ==
%(u::'q_37743::type => bool) ua::'q_37744::type => bool.
   CARD_LE u ua & ~ CARD_LE ua u"

lemma DEF_CARD_LT: "CARD_LT =
(%(u::'q_37743::type => bool) ua::'q_37744::type => bool.
    CARD_LE u ua & ~ CARD_LE ua u)"
  by (import hollight DEF_CARD_LT)

constdefs
  COUNTABLE :: "('q_37757 => bool) => bool" 
  "(op ==::(('q_37757::type => bool) => bool)
        => (('q_37757::type => bool) => bool) => prop)
 (COUNTABLE::('q_37757::type => bool) => bool)
 ((CARD_GE::(nat => bool) => ('q_37757::type => bool) => bool)
   (hollight.UNIV::nat => bool))"

lemma DEF_COUNTABLE: "(op =::(('q_37757::type => bool) => bool)
       => (('q_37757::type => bool) => bool) => bool)
 (COUNTABLE::('q_37757::type => bool) => bool)
 ((CARD_GE::(nat => bool) => ('q_37757::type => bool) => bool)
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

lemma UNION_SUBSET: "ALL (x::'q_38594::type => bool) (xa::'q_38594::type => bool)
   xb::'q_38594::type => bool.
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

lemma SUBSET_DIFF: "ALL (x::'q_39012::type => bool) xa::'q_39012::type => bool.
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

lemma INSERT_AC: "INSERT (x::'q_39468::type)
 (INSERT (y::'q_39468::type) (s::'q_39468::type => bool)) =
INSERT y (INSERT x s) &
INSERT x (INSERT x s) = INSERT x s"
  by (import hollight INSERT_AC)

lemma INTER_ACI: "hollight.INTER (p::'q_39535::type => bool) (q::'q_39535::type => bool) =
hollight.INTER q p &
hollight.INTER (hollight.INTER p q) (r::'q_39535::type => bool) =
hollight.INTER p (hollight.INTER q r) &
hollight.INTER p (hollight.INTER q r) =
hollight.INTER q (hollight.INTER p r) &
hollight.INTER p p = p &
hollight.INTER p (hollight.INTER p q) = hollight.INTER p q"
  by (import hollight INTER_ACI)

lemma UNION_ACI: "hollight.UNION (p::'q_39601::type => bool) (q::'q_39601::type => bool) =
hollight.UNION q p &
hollight.UNION (hollight.UNION p q) (r::'q_39601::type => bool) =
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

lemma UNIONS_0: "(op =::('q_40008::type => bool) => ('q_40008::type => bool) => bool)
 ((UNIONS::(('q_40008::type => bool) => bool) => 'q_40008::type => bool)
   (EMPTY::('q_40008::type => bool) => bool))
 (EMPTY::'q_40008::type => bool)"
  by (import hollight UNIONS_0)

lemma UNIONS_1: "UNIONS (INSERT (s::'q_40014::type => bool) EMPTY) = s"
  by (import hollight UNIONS_1)

lemma UNIONS_2: "UNIONS
 (INSERT (s::'q_40034::type => bool)
   (INSERT (t::'q_40034::type => bool) EMPTY)) =
hollight.UNION s t"
  by (import hollight UNIONS_2)

lemma UNIONS_INSERT: "UNIONS
 (INSERT (s::'q_40048::type => bool)
   (u::('q_40048::type => bool) => bool)) =
hollight.UNION s (UNIONS u)"
  by (import hollight UNIONS_INSERT)

lemma FORALL_IN_UNIONS: "ALL (x::'q_40090::type => bool) xa::('q_40090::type => bool) => bool.
   (ALL xb::'q_40090::type. IN xb (UNIONS xa) --> x xb) =
   (ALL (t::'q_40090::type => bool) xb::'q_40090::type.
       IN t xa & IN xb t --> x xb)"
  by (import hollight FORALL_IN_UNIONS)

lemma EMPTY_UNIONS: "ALL x::('q_40116::type => bool) => bool.
   (UNIONS x = EMPTY) =
   (ALL xa::'q_40116::type => bool. IN xa x --> xa = EMPTY)"
  by (import hollight EMPTY_UNIONS)

lemma INTERS_0: "(op =::('q_40124::type => bool) => ('q_40124::type => bool) => bool)
 ((INTERS::(('q_40124::type => bool) => bool) => 'q_40124::type => bool)
   (EMPTY::('q_40124::type => bool) => bool))
 (hollight.UNIV::'q_40124::type => bool)"
  by (import hollight INTERS_0)

lemma INTERS_1: "INTERS (INSERT (s::'q_40130::type => bool) EMPTY) = s"
  by (import hollight INTERS_1)

lemma INTERS_2: "INTERS
 (INSERT (s::'q_40150::type => bool)
   (INSERT (t::'q_40150::type => bool) EMPTY)) =
hollight.INTER s t"
  by (import hollight INTERS_2)

lemma INTERS_INSERT: "INTERS
 (INSERT (s::'q_40164::type => bool)
   (u::('q_40164::type => bool) => bool)) =
hollight.INTER s (INTERS u)"
  by (import hollight INTERS_INSERT)

lemma IMAGE_CLAUSES: "IMAGE (f::'q_40190::type => 'q_40194::type) EMPTY = EMPTY &
IMAGE f (INSERT (x::'q_40190::type) (s::'q_40190::type => bool)) =
INSERT (f x) (IMAGE f s)"
  by (import hollight IMAGE_CLAUSES)

lemma IMAGE_UNION: "ALL (x::'q_40217::type => 'q_40228::type) (xa::'q_40217::type => bool)
   xb::'q_40217::type => bool.
   IMAGE x (hollight.UNION xa xb) = hollight.UNION (IMAGE x xa) (IMAGE x xb)"
  by (import hollight IMAGE_UNION)

lemma IMAGE_o: "ALL (x::'q_40261::type => 'q_40257::type)
   (xa::'q_40252::type => 'q_40261::type) xb::'q_40252::type => bool.
   IMAGE (x o xa) xb = IMAGE x (IMAGE xa xb)"
  by (import hollight IMAGE_o)

lemma IMAGE_SUBSET: "ALL (x::'q_40279::type => 'q_40290::type) (xa::'q_40279::type => bool)
   xb::'q_40279::type => bool.
   SUBSET xa xb --> SUBSET (IMAGE x xa) (IMAGE x xb)"
  by (import hollight IMAGE_SUBSET)

lemma IMAGE_DIFF_INJ: "(ALL (x::'q_40321::type) y::'q_40321::type.
    (f::'q_40321::type => 'q_40332::type) x = f y --> x = y) -->
IMAGE f (DIFF (s::'q_40321::type => bool) (t::'q_40321::type => bool)) =
DIFF (IMAGE f s) (IMAGE f t)"
  by (import hollight IMAGE_DIFF_INJ)

lemma IMAGE_DELETE_INJ: "(ALL x::'q_40367::type.
    (f::'q_40367::type => 'q_40366::type) x = f (a::'q_40367::type) -->
    x = a) -->
IMAGE f (DELETE (s::'q_40367::type => bool) a) = DELETE (IMAGE f s) (f a)"
  by (import hollight IMAGE_DELETE_INJ)

lemma IMAGE_EQ_EMPTY: "ALL (x::'q_40390::type => 'q_40386::type) xa::'q_40390::type => bool.
   (IMAGE x xa = EMPTY) = (xa = EMPTY)"
  by (import hollight IMAGE_EQ_EMPTY)

lemma FORALL_IN_IMAGE: "ALL (x::'q_40426::type => 'q_40425::type) xa::'q_40426::type => bool.
   (ALL xb::'q_40425::type.
       IN xb (IMAGE x xa) --> (P::'q_40425::type => bool) xb) =
   (ALL xb::'q_40426::type. IN xb xa --> P (x xb))"
  by (import hollight FORALL_IN_IMAGE)

lemma EXISTS_IN_IMAGE: "ALL (x::'q_40462::type => 'q_40461::type) xa::'q_40462::type => bool.
   (EX xb::'q_40461::type.
       IN xb (IMAGE x xa) & (P::'q_40461::type => bool) xb) =
   (EX xb::'q_40462::type. IN xb xa & P (x xb))"
  by (import hollight EXISTS_IN_IMAGE)

lemma SUBSET_IMAGE: "ALL (f::'A::type => 'B::type) (s::'B::type => bool) t::'A::type => bool.
   SUBSET s (IMAGE f t) =
   (EX x::'A::type => bool. SUBSET x t & s = IMAGE f x)"
  by (import hollight SUBSET_IMAGE)

lemma IMAGE_CONST: "ALL (s::'q_40548::type => bool) c::'q_40553::type.
   IMAGE (%x::'q_40548::type. c) s = COND (s = EMPTY) EMPTY (INSERT c EMPTY)"
  by (import hollight IMAGE_CONST)

lemma SIMPLE_IMAGE: "ALL (x::'q_40581::type => 'q_40585::type) xa::'q_40581::type => bool.
   GSPEC
    (%u::'q_40585::type.
        EX xb::'q_40581::type. SETSPEC u (IN xb xa) (x xb)) =
   IMAGE x xa"
  by (import hollight SIMPLE_IMAGE)

lemma EMPTY_GSPEC: "GSPEC (%u::'q_40602::type. Ex (SETSPEC u False)) = EMPTY"
  by (import hollight EMPTY_GSPEC)

lemma IN_ELIM_PAIR_THM: "ALL (x::'q_40648::type => 'q_40647::type => bool) (xa::'q_40648::type)
   xb::'q_40647::type.
   IN (xa, xb)
    (GSPEC
      (%xa::'q_40648::type * 'q_40647::type.
          EX (xb::'q_40648::type) y::'q_40647::type.
             SETSPEC xa (x xb y) (xb, y))) =
   x xa xb"
  by (import hollight IN_ELIM_PAIR_THM)

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

lemma FINITE_UNIONS: "ALL s::('q_40983::type => bool) => bool.
   FINITE s -->
   FINITE (UNIONS s) = (ALL t::'q_40983::type => bool. IN t s --> FINITE t)"
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

lemma INFINITE_NONEMPTY: "ALL s::'q_41466::type => bool. INFINITE s --> s ~= EMPTY"
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

lemma FINITE_DIFF: "ALL (s::'q_41764::type => bool) t::'q_41764::type => bool.
   FINITE s --> FINITE (DIFF s t)"
  by (import hollight FINITE_DIFF)

constdefs
  FINREC :: "('q_41824 => 'q_41823 => 'q_41823)
=> 'q_41823 => ('q_41824 => bool) => 'q_41823 => nat => bool" 
  "FINREC ==
SOME FINREC::('q_41824::type => 'q_41823::type => 'q_41823::type)
             => 'q_41823::type
                => ('q_41824::type => bool)
                   => 'q_41823::type => nat => bool.
   (ALL (f::'q_41824::type => 'q_41823::type => 'q_41823::type)
       (s::'q_41824::type => bool) (a::'q_41823::type) b::'q_41823::type.
       FINREC f b s a 0 = (s = EMPTY & a = b)) &
   (ALL (b::'q_41823::type) (s::'q_41824::type => bool) (n::nat)
       (a::'q_41823::type)
       f::'q_41824::type => 'q_41823::type => 'q_41823::type.
       FINREC f b s a (Suc n) =
       (EX (x::'q_41824::type) c::'q_41823::type.
           IN x s & FINREC f b (DELETE s x) c n & a = f x c))"

lemma DEF_FINREC: "FINREC =
(SOME FINREC::('q_41824::type => 'q_41823::type => 'q_41823::type)
              => 'q_41823::type
                 => ('q_41824::type => bool)
                    => 'q_41823::type => nat => bool.
    (ALL (f::'q_41824::type => 'q_41823::type => 'q_41823::type)
        (s::'q_41824::type => bool) (a::'q_41823::type) b::'q_41823::type.
        FINREC f b s a 0 = (s = EMPTY & a = b)) &
    (ALL (b::'q_41823::type) (s::'q_41824::type => bool) (n::nat)
        (a::'q_41823::type)
        f::'q_41824::type => 'q_41823::type => 'q_41823::type.
        FINREC f b s a (Suc n) =
        (EX (x::'q_41824::type) c::'q_41823::type.
            IN x s & FINREC f b (DELETE s x) c n & a = f x c)))"
  by (import hollight DEF_FINREC)

lemma FINREC_1_LEMMA: "ALL (x::'q_41869::type => 'q_41868::type => 'q_41868::type)
   (xa::'q_41868::type) (xb::'q_41869::type => bool) xc::'q_41868::type.
   FINREC x xa xb xc (Suc 0) =
   (EX xd::'q_41869::type. xb = INSERT xd EMPTY & xc = x xd xa)"
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
  ITSET :: "('q_42525 => 'q_42524 => 'q_42524)
=> ('q_42525 => bool) => 'q_42524 => 'q_42524" 
  "ITSET ==
%(u::'q_42525::type => 'q_42524::type => 'q_42524::type)
   (ua::'q_42525::type => bool) ub::'q_42524::type.
   (SOME g::('q_42525::type => bool) => 'q_42524::type.
       g EMPTY = ub &
       (ALL (x::'q_42525::type) s::'q_42525::type => bool.
           FINITE s --> g (INSERT x s) = COND (IN x s) (g s) (u x (g s))))
    ua"

lemma DEF_ITSET: "ITSET =
(%(u::'q_42525::type => 'q_42524::type => 'q_42524::type)
    (ua::'q_42525::type => bool) ub::'q_42524::type.
    (SOME g::('q_42525::type => bool) => 'q_42524::type.
        g EMPTY = ub &
        (ALL (x::'q_42525::type) s::'q_42525::type => bool.
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

lemma ITSET_EQ: "ALL (x::'q_42830::type => bool)
   (xa::'q_42830::type => 'q_42831::type => 'q_42831::type)
   (xb::'q_42830::type => 'q_42831::type => 'q_42831::type)
   xc::'q_42831::type.
   FINITE x &
   (ALL xc::'q_42830::type. IN xc x --> xa xc = xb xc) &
   (ALL (x::'q_42830::type) (y::'q_42830::type) s::'q_42831::type.
       x ~= y --> xa x (xa y s) = xa y (xa x s)) &
   (ALL (x::'q_42830::type) (y::'q_42830::type) s::'q_42831::type.
       x ~= y --> xb x (xb y s) = xb y (xb x s)) -->
   ITSET xa x xc = ITSET xb x xc"
  by (import hollight ITSET_EQ)

lemma SUBSET_RESTRICT: "ALL (x::'q_42864::type => bool) xa::'q_42864::type => bool.
   SUBSET
    (GSPEC
      (%u::'q_42864::type.
          EX xb::'q_42864::type. SETSPEC u (IN xb x & xa xb) xb))
    x"
  by (import hollight SUBSET_RESTRICT)

lemma FINITE_RESTRICT: "ALL (s::'A::type => bool) p::'q_42882::type.
   FINITE s -->
   FINITE
    (GSPEC
      (%u::'A::type.
          EX x::'A::type. SETSPEC u (IN x s & (P::'A::type => bool) x) x))"
  by (import hollight FINITE_RESTRICT)

constdefs
  CARD :: "('q_42918 => bool) => nat" 
  "CARD == %u::'q_42918::type => bool. ITSET (%x::'q_42918::type. Suc) u 0"

lemma DEF_CARD: "CARD = (%u::'q_42918::type => bool. ITSET (%x::'q_42918::type. Suc) u 0)"
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

lemma CARD_UNION_EQ: "ALL (s::'q_43163::type => bool) (t::'q_43163::type => bool)
   u::'q_43163::type => bool.
   FINITE u & hollight.INTER s t = EMPTY & hollight.UNION s t = u -->
   CARD s + CARD t = CARD u"
  by (import hollight CARD_UNION_EQ)

constdefs
  HAS_SIZE :: "('q_43199 => bool) => nat => bool" 
  "HAS_SIZE == %(u::'q_43199::type => bool) ua::nat. FINITE u & CARD u = ua"

lemma DEF_HAS_SIZE: "HAS_SIZE = (%(u::'q_43199::type => bool) ua::nat. FINITE u & CARD u = ua)"
  by (import hollight DEF_HAS_SIZE)

lemma HAS_SIZE_CARD: "ALL (x::'q_43218::type => bool) xa::nat. HAS_SIZE x xa --> CARD x = xa"
  by (import hollight HAS_SIZE_CARD)

lemma HAS_SIZE_0: "ALL (s::'A::type => bool) n::'q_43234::type. HAS_SIZE s 0 = (s = EMPTY)"
  by (import hollight HAS_SIZE_0)

lemma HAS_SIZE_SUC: "ALL (s::'A::type => bool) n::nat.
   HAS_SIZE s (Suc n) =
   (s ~= EMPTY & (ALL x::'A::type. IN x s --> HAS_SIZE (DELETE s x) n))"
  by (import hollight HAS_SIZE_SUC)

lemma HAS_SIZE_UNION: "ALL (x::'q_43356::type => bool) (xa::'q_43356::type => bool) (xb::nat)
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

lemma HAS_SIZE_CLAUSES: "HAS_SIZE (s::'q_43604::type => bool) 0 = (s = EMPTY) &
HAS_SIZE s (Suc (n::nat)) =
(EX (a::'q_43604::type) t::'q_43604::type => bool.
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

lemma CARD_EQ_0: "ALL s::'q_43920::type => bool. FINITE s --> (CARD s = 0) = (s = EMPTY)"
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

lemma CARD_FUNSPACE: "ALL (s::'q_45275::type => bool) t::'q_45272::type => bool.
   FINITE s & FINITE t -->
   CARD
    (GSPEC
      (%u::'q_45275::type => 'q_45272::type.
          EX f::'q_45275::type => 'q_45272::type.
             SETSPEC u
              ((ALL x::'q_45275::type. IN x s --> IN (f x) t) &
               (ALL x::'q_45275::type.
                   ~ IN x s --> f x = (d::'q_45272::type)))
              f)) =
   EXP (CARD t) (CARD s)"
  by (import hollight CARD_FUNSPACE)

lemma FINITE_FUNSPACE: "ALL (s::'q_45341::type => bool) t::'q_45338::type => bool.
   FINITE s & FINITE t -->
   FINITE
    (GSPEC
      (%u::'q_45341::type => 'q_45338::type.
          EX f::'q_45341::type => 'q_45338::type.
             SETSPEC u
              ((ALL x::'q_45341::type. IN x s --> IN (f x) t) &
               (ALL x::'q_45341::type.
                   ~ IN x s --> f x = (d::'q_45338::type)))
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
  set_of_list :: "'q_45968 hollight.list => 'q_45968 => bool" 
  "set_of_list ==
SOME set_of_list::'q_45968::type hollight.list => 'q_45968::type => bool.
   set_of_list NIL = EMPTY &
   (ALL (h::'q_45968::type) t::'q_45968::type hollight.list.
       set_of_list (CONS h t) = INSERT h (set_of_list t))"

lemma DEF_set_of_list: "set_of_list =
(SOME set_of_list::'q_45968::type hollight.list => 'q_45968::type => bool.
    set_of_list NIL = EMPTY &
    (ALL (h::'q_45968::type) t::'q_45968::type hollight.list.
        set_of_list (CONS h t) = INSERT h (set_of_list t)))"
  by (import hollight DEF_set_of_list)

constdefs
  list_of_set :: "('q_45986 => bool) => 'q_45986 hollight.list" 
  "list_of_set ==
%u::'q_45986::type => bool.
   SOME l::'q_45986::type hollight.list.
      set_of_list l = u & LENGTH l = CARD u"

lemma DEF_list_of_set: "list_of_set =
(%u::'q_45986::type => bool.
    SOME l::'q_45986::type hollight.list.
       set_of_list l = u & LENGTH l = CARD u)"
  by (import hollight DEF_list_of_set)

lemma LIST_OF_SET_PROPERTIES: "ALL x::'A::type => bool.
   FINITE x -->
   set_of_list (list_of_set x) = x & LENGTH (list_of_set x) = CARD x"
  by (import hollight LIST_OF_SET_PROPERTIES)

lemma SET_OF_LIST_OF_SET: "ALL s::'q_46035::type => bool. FINITE s --> set_of_list (list_of_set s) = s"
  by (import hollight SET_OF_LIST_OF_SET)

lemma LENGTH_LIST_OF_SET: "ALL s::'q_46051::type => bool. FINITE s --> LENGTH (list_of_set s) = CARD s"
  by (import hollight LENGTH_LIST_OF_SET)

lemma MEM_LIST_OF_SET: "ALL s::'A::type => bool.
   FINITE s --> (ALL x::'A::type. MEM x (list_of_set s) = IN x s)"
  by (import hollight MEM_LIST_OF_SET)

lemma FINITE_SET_OF_LIST: "ALL l::'q_46096::type hollight.list. FINITE (set_of_list l)"
  by (import hollight FINITE_SET_OF_LIST)

lemma IN_SET_OF_LIST: "ALL (x::'q_46114::type) l::'q_46114::type hollight.list.
   IN x (set_of_list l) = MEM x l"
  by (import hollight IN_SET_OF_LIST)

lemma SET_OF_LIST_APPEND: "ALL (x::'q_46139::type hollight.list) xa::'q_46139::type hollight.list.
   set_of_list (APPEND x xa) =
   hollight.UNION (set_of_list x) (set_of_list xa)"
  by (import hollight SET_OF_LIST_APPEND)

constdefs
  pairwise :: "('q_46198 => 'q_46198 => bool) => ('q_46198 => bool) => bool" 
  "pairwise ==
%(u::'q_46198::type => 'q_46198::type => bool) ua::'q_46198::type => bool.
   ALL (x::'q_46198::type) y::'q_46198::type.
      IN x ua & IN y ua & x ~= y --> u x y"

lemma DEF_pairwise: "pairwise =
(%(u::'q_46198::type => 'q_46198::type => bool) ua::'q_46198::type => bool.
    ALL (x::'q_46198::type) y::'q_46198::type.
       IN x ua & IN y ua & x ~= y --> u x y)"
  by (import hollight DEF_pairwise)

constdefs
  PAIRWISE :: "('q_46220 => 'q_46220 => bool) => 'q_46220 hollight.list => bool" 
  "PAIRWISE ==
SOME PAIRWISE::('q_46220::type => 'q_46220::type => bool)
               => 'q_46220::type hollight.list => bool.
   (ALL r::'q_46220::type => 'q_46220::type => bool.
       PAIRWISE r NIL = True) &
   (ALL (h::'q_46220::type) (r::'q_46220::type => 'q_46220::type => bool)
       t::'q_46220::type hollight.list.
       PAIRWISE r (CONS h t) = (ALL_list (r h) t & PAIRWISE r t))"

lemma DEF_PAIRWISE: "PAIRWISE =
(SOME PAIRWISE::('q_46220::type => 'q_46220::type => bool)
                => 'q_46220::type hollight.list => bool.
    (ALL r::'q_46220::type => 'q_46220::type => bool.
        PAIRWISE r NIL = True) &
    (ALL (h::'q_46220::type) (r::'q_46220::type => 'q_46220::type => bool)
        t::'q_46220::type hollight.list.
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
  "$" :: "('q_46627, 'q_46634) cart => nat => 'q_46627" ("$")

defs
  "$_def": "$ ==
%(u::('q_46627::type, 'q_46634::type) cart) ua::nat.
   dest_cart u (finite_index ua)"

lemma "DEF_$": "$ =
(%(u::('q_46627::type, 'q_46634::type) cart) ua::nat.
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

lemma LAMBDA_ETA: "ALL x::('q_46825::type, 'q_46829::type) cart. lambda ($ x) = x"
  by (import hollight LAMBDA_ETA)

typedef (open) ('A, 'B) finite_sum = "(Collect::('A::type finite_image + 'B::type finite_image => bool)
          => ('A::type finite_image + 'B::type finite_image) set)
 (%x::'A::type finite_image + 'B::type finite_image. True::bool)"  morphisms "dest_finite_sum" "mk_finite_sum"
  apply (rule light_ex_imp_nonempty[where t="(Eps::('A::type finite_image + 'B::type finite_image => bool)
      => 'A::type finite_image + 'B::type finite_image)
 (%x::'A::type finite_image + 'B::type finite_image. True::bool)"])
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
           u ((HOL.plus::nat => nat => nat) i
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
           u ((HOL.plus::nat => nat => nat) i
               ((dimindex::('M::type => bool) => nat)
                 (hollight.UNIV::'M::type => bool)))))"
  by (import hollight DEF_sndcart)

lemma DIMINDEX_HAS_SIZE_FINITE_SUM: "(HAS_SIZE::(('M::type, 'N::type) finite_sum => bool) => nat => bool)
 (hollight.UNIV::('M::type, 'N::type) finite_sum => bool)
 ((HOL.plus::nat => nat => nat)
   ((dimindex::('M::type => bool) => nat) (hollight.UNIV::'M::type => bool))
   ((dimindex::('N::type => bool) => nat)
     (hollight.UNIV::'N::type => bool)))"
  by (import hollight DIMINDEX_HAS_SIZE_FINITE_SUM)

lemma DIMINDEX_FINITE_SUM: "(op =::nat => nat => bool)
 ((dimindex::(('M::type, 'N::type) finite_sum => bool) => nat)
   (hollight.UNIV::('M::type, 'N::type) finite_sum => bool))
 ((HOL.plus::nat => nat => nat)
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

lemma PASTECART_FST_SND: "ALL x::('q_47149::type, ('q_47146::type, 'q_47144::type) finite_sum) cart.
   pastecart (fstcart x) (sndcart x) = x"
  by (import hollight PASTECART_FST_SND)

lemma PASTECART_EQ: "ALL (x::('q_47187::type, ('q_47177::type, 'q_47188::type) finite_sum) cart)
   y::('q_47187::type, ('q_47177::type, 'q_47188::type) finite_sum) cart.
   (x = y) = (fstcart x = fstcart y & sndcart x = sndcart y)"
  by (import hollight PASTECART_EQ)

lemma FORALL_PASTECART: "All (P::('q_47208::type, ('q_47209::type, 'q_47210::type) finite_sum) cart
        => bool) =
(ALL (x::('q_47208::type, 'q_47209::type) cart)
    y::('q_47208::type, 'q_47210::type) cart. P (pastecart x y))"
  by (import hollight FORALL_PASTECART)

lemma EXISTS_PASTECART: "Ex (P::('q_47230::type, ('q_47231::type, 'q_47232::type) finite_sum) cart
       => bool) =
(EX (x::('q_47230::type, 'q_47231::type) cart)
    y::('q_47230::type, 'q_47232::type) cart. P (pastecart x y))"
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

lemma IMAGE_IMP_INJECTIVE: "ALL (s::'q_47557::type => bool) f::'q_47557::type => 'q_47557::type.
   FINITE s & IMAGE f s = s -->
   (ALL (x::'q_47557::type) y::'q_47557::type.
       IN x s & IN y s & f x = f y --> x = y)"
  by (import hollight IMAGE_IMP_INJECTIVE)

lemma CARD_LE_INJ: "ALL (x::'A::type => bool) xa::'B::type => bool.
   FINITE x & FINITE xa & <= (CARD x) (CARD xa) -->
   (EX f::'A::type => 'B::type.
       SUBSET (IMAGE f x) xa &
       (ALL (xa::'A::type) y::'A::type.
           IN xa x & IN y x & f xa = f y --> xa = y))"
  by (import hollight CARD_LE_INJ)

lemma FORALL_IN_CLAUSES: "(ALL x::'q_47663::type => bool.
    (ALL xa::'q_47663::type. IN xa EMPTY --> x xa) = True) &
(ALL (x::'q_47703::type => bool) (xa::'q_47703::type)
    xb::'q_47703::type => bool.
    (ALL xc::'q_47703::type. IN xc (INSERT xa xb) --> x xc) =
    (x xa & (ALL xa::'q_47703::type. IN xa xb --> x xa)))"
  by (import hollight FORALL_IN_CLAUSES)

lemma EXISTS_IN_CLAUSES: "(ALL x::'q_47723::type => bool.
    (EX xa::'q_47723::type. IN xa EMPTY & x xa) = False) &
(ALL (x::'q_47763::type => bool) (xa::'q_47763::type)
    xb::'q_47763::type => bool.
    (EX xc::'q_47763::type. IN xc (INSERT xa xb) & x xc) =
    (x xa | (EX xa::'q_47763::type. IN xa xb & x xa)))"
  by (import hollight EXISTS_IN_CLAUSES)

lemma SURJECTIVE_ON_RIGHT_INVERSE: "ALL (x::'q_47819::type => 'q_47820::type) xa::'q_47820::type => bool.
   (ALL xb::'q_47820::type.
       IN xb xa -->
       (EX xa::'q_47819::type.
           IN xa (s::'q_47819::type => bool) & x xa = xb)) =
   (EX g::'q_47820::type => 'q_47819::type.
       ALL y::'q_47820::type. IN y xa --> IN (g y) s & x (g y) = y)"
  by (import hollight SURJECTIVE_ON_RIGHT_INVERSE)

lemma INJECTIVE_ON_LEFT_INVERSE: "ALL (x::'q_47913::type => 'q_47916::type) xa::'q_47913::type => bool.
   (ALL (xb::'q_47913::type) y::'q_47913::type.
       IN xb xa & IN y xa & x xb = x y --> xb = y) =
   (EX xb::'q_47916::type => 'q_47913::type.
       ALL xc::'q_47913::type. IN xc xa --> xb (x xc) = xc)"
  by (import hollight INJECTIVE_ON_LEFT_INVERSE)

lemma SURJECTIVE_RIGHT_INVERSE: "(ALL y::'q_47941::type.
    EX x::'q_47944::type. (f::'q_47944::type => 'q_47941::type) x = y) =
(EX g::'q_47941::type => 'q_47944::type. ALL y::'q_47941::type. f (g y) = y)"
  by (import hollight SURJECTIVE_RIGHT_INVERSE)

lemma INJECTIVE_LEFT_INVERSE: "(ALL (x::'q_47978::type) xa::'q_47978::type.
    (f::'q_47978::type => 'q_47981::type) x = f xa --> x = xa) =
(EX g::'q_47981::type => 'q_47978::type. ALL x::'q_47978::type. g (f x) = x)"
  by (import hollight INJECTIVE_LEFT_INVERSE)

lemma FUNCTION_FACTORS_RIGHT: "ALL (x::'q_48017::type => 'q_48018::type)
   xa::'q_48005::type => 'q_48018::type.
   (ALL xb::'q_48017::type. EX y::'q_48005::type. xa y = x xb) =
   (EX xb::'q_48017::type => 'q_48005::type. x = xa o xb)"
  by (import hollight FUNCTION_FACTORS_RIGHT)

lemma FUNCTION_FACTORS_LEFT: "ALL (x::'q_48090::type => 'q_48091::type)
   xa::'q_48090::type => 'q_48070::type.
   (ALL (xb::'q_48090::type) y::'q_48090::type.
       xa xb = xa y --> x xb = x y) =
   (EX xb::'q_48070::type => 'q_48091::type. x = xb o xa)"
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

lemma NUMSEG_COMBINE_R: "ALL (x::'q_48166::type) (p::nat) m::nat.
   <= m p & <= p (n::nat) -->
   hollight.UNION (dotdot m p) (dotdot (p + NUMERAL_BIT1 0) n) = dotdot m n"
  by (import hollight NUMSEG_COMBINE_R)

lemma NUMSEG_COMBINE_L: "ALL (x::'q_48204::type) (p::nat) m::nat.
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
  neutral :: "('q_48985 => 'q_48985 => 'q_48985) => 'q_48985" 
  "neutral ==
%u::'q_48985::type => 'q_48985::type => 'q_48985::type.
   SOME x::'q_48985::type. ALL y::'q_48985::type. u x y = y & u y x = y"

lemma DEF_neutral: "neutral =
(%u::'q_48985::type => 'q_48985::type => 'q_48985::type.
    SOME x::'q_48985::type. ALL y::'q_48985::type. u x y = y & u y x = y)"
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
  iterate :: "('q_49090 => 'q_49090 => 'q_49090)
=> ('A => bool) => ('A => 'q_49090) => 'q_49090" 
  "iterate ==
%(u::'q_49090::type => 'q_49090::type => 'q_49090::type)
   (ua::'A::type => bool) ub::'A::type => 'q_49090::type.
   ITSET (%x::'A::type. u (ub x)) (support u ub ua) (neutral u)"

lemma DEF_iterate: "iterate =
(%(u::'q_49090::type => 'q_49090::type => 'q_49090::type)
    (ua::'A::type => bool) ub::'A::type => 'q_49090::type.
    ITSET (%x::'A::type. u (ub x)) (support u ub ua) (neutral u))"
  by (import hollight DEF_iterate)

lemma IN_SUPPORT: "ALL (x::'q_49133::type => 'q_49133::type => 'q_49133::type)
   (xa::'q_49136::type => 'q_49133::type) (xb::'q_49136::type)
   xc::'q_49136::type => bool.
   IN xb (support x xa xc) = (IN xb xc & xa xb ~= neutral x)"
  by (import hollight IN_SUPPORT)

lemma SUPPORT_SUPPORT: "ALL (x::'q_49158::type => 'q_49158::type => 'q_49158::type)
   (xa::'q_49169::type => 'q_49158::type) xb::'q_49169::type => bool.
   support x xa (support x xa xb) = support x xa xb"
  by (import hollight SUPPORT_SUPPORT)

lemma SUPPORT_EMPTY: "ALL (x::'q_49194::type => 'q_49194::type => 'q_49194::type)
   (xa::'q_49208::type => 'q_49194::type) xb::'q_49208::type => bool.
   (ALL xc::'q_49208::type. IN xc xb --> xa xc = neutral x) =
   (support x xa xb = EMPTY)"
  by (import hollight SUPPORT_EMPTY)

lemma SUPPORT_SUBSET: "ALL (x::'q_49228::type => 'q_49228::type => 'q_49228::type)
   (xa::'q_49229::type => 'q_49228::type) xb::'q_49229::type => bool.
   SUBSET (support x xa xb) xb"
  by (import hollight SUPPORT_SUBSET)

lemma FINITE_SUPPORT: "ALL (u::'q_49252::type => 'q_49252::type => 'q_49252::type)
   (f::'q_49246::type => 'q_49252::type) s::'q_49246::type => bool.
   FINITE s --> FINITE (support u f s)"
  by (import hollight FINITE_SUPPORT)

lemma SUPPORT_CLAUSES: "(ALL x::'q_49270::type => 'q_49300::type.
    support (u_4247::'q_49300::type => 'q_49300::type => 'q_49300::type) x
     EMPTY =
    EMPTY) &
(ALL (x::'q_49318::type => 'q_49300::type) (xa::'q_49318::type)
    xb::'q_49318::type => bool.
    support u_4247 x (INSERT xa xb) =
    COND (x xa = neutral u_4247) (support u_4247 x xb)
     (INSERT xa (support u_4247 x xb))) &
(ALL (x::'q_49351::type => 'q_49300::type) (xa::'q_49351::type)
    xb::'q_49351::type => bool.
    support u_4247 x (DELETE xb xa) = DELETE (support u_4247 x xb) xa) &
(ALL (x::'q_49389::type => 'q_49300::type) (xa::'q_49389::type => bool)
    xb::'q_49389::type => bool.
    support u_4247 x (hollight.UNION xa xb) =
    hollight.UNION (support u_4247 x xa) (support u_4247 x xb)) &
(ALL (x::'q_49427::type => 'q_49300::type) (xa::'q_49427::type => bool)
    xb::'q_49427::type => bool.
    support u_4247 x (hollight.INTER xa xb) =
    hollight.INTER (support u_4247 x xa) (support u_4247 x xb)) &
(ALL (x::'q_49463::type => 'q_49300::type) (xa::'q_49463::type => bool)
    xb::'q_49463::type => bool.
    support u_4247 x (DIFF xa xb) =
    DIFF (support u_4247 x xa) (support u_4247 x xb))"
  by (import hollight SUPPORT_CLAUSES)

lemma ITERATE_SUPPORT: "ALL (x::'q_49484::type => 'q_49484::type => 'q_49484::type)
   (xa::'q_49485::type => 'q_49484::type) xb::'q_49485::type => bool.
   FINITE (support x xa xb) -->
   iterate x (support x xa xb) xa = iterate x xb xa"
  by (import hollight ITERATE_SUPPORT)

lemma SUPPORT_DELTA: "ALL (x::'q_49529::type => 'q_49529::type => 'q_49529::type)
   (xa::'q_49557::type => bool) (xb::'q_49557::type => 'q_49529::type)
   xc::'q_49557::type.
   support x (%xa::'q_49557::type. COND (xa = xc) (xb xa) (neutral x)) xa =
   COND (IN xc xa) (support x xb (INSERT xc EMPTY)) EMPTY"
  by (import hollight SUPPORT_DELTA)

lemma FINITE_SUPPORT_DELTA: "ALL (x::'q_49578::type => 'q_49578::type => 'q_49578::type)
   (xa::'q_49587::type => 'q_49578::type) xb::'q_49587::type.
   FINITE
    (support x (%xc::'q_49587::type. COND (xc = xb) (xa xc) (neutral x))
      (s::'q_49587::type => bool))"
  by (import hollight FINITE_SUPPORT_DELTA)

lemma ITERATE_CLAUSES_GEN: "ALL u_4247::'B::type => 'B::type => 'B::type.
   monoidal u_4247 -->
   (ALL f::'A::type => 'B::type. iterate u_4247 EMPTY f = neutral u_4247) &
   (ALL (f::'A::type => 'B::type) (x::'A::type) s::'A::type => bool.
       monoidal u_4247 & FINITE (support u_4247 f s) -->
       iterate u_4247 (INSERT x s) f =
       COND (IN x s) (iterate u_4247 s f)
        (u_4247 (f x) (iterate u_4247 s f)))"
  by (import hollight ITERATE_CLAUSES_GEN)

lemma ITERATE_CLAUSES: "ALL x::'q_49755::type => 'q_49755::type => 'q_49755::type.
   monoidal x -->
   (ALL f::'q_49713::type => 'q_49755::type.
       iterate x EMPTY f = neutral x) &
   (ALL (f::'q_49757::type => 'q_49755::type) (xa::'q_49757::type)
       s::'q_49757::type => bool.
       FINITE s -->
       iterate x (INSERT xa s) f =
       COND (IN xa s) (iterate x s f) (x (f xa) (iterate x s f)))"
  by (import hollight ITERATE_CLAUSES)

lemma ITERATE_UNION: "ALL u_4247::'q_49843::type => 'q_49843::type => 'q_49843::type.
   monoidal u_4247 -->
   (ALL (f::'q_49828::type => 'q_49843::type) (s::'q_49828::type => bool)
       x::'q_49828::type => bool.
       FINITE s & FINITE x & DISJOINT s x -->
       iterate u_4247 (hollight.UNION s x) f =
       u_4247 (iterate u_4247 s f) (iterate u_4247 x f))"
  by (import hollight ITERATE_UNION)

lemma ITERATE_UNION_GEN: "ALL u_4247::'B::type => 'B::type => 'B::type.
   monoidal u_4247 -->
   (ALL (f::'A::type => 'B::type) (s::'A::type => bool) t::'A::type => bool.
       FINITE (support u_4247 f s) &
       FINITE (support u_4247 f t) &
       DISJOINT (support u_4247 f s) (support u_4247 f t) -->
       iterate u_4247 (hollight.UNION s t) f =
       u_4247 (iterate u_4247 s f) (iterate u_4247 t f))"
  by (import hollight ITERATE_UNION_GEN)

lemma ITERATE_DIFF: "ALL u::'q_49986::type => 'q_49986::type => 'q_49986::type.
   monoidal u -->
   (ALL (f::'q_49982::type => 'q_49986::type) (s::'q_49982::type => bool)
       t::'q_49982::type => bool.
       FINITE s & SUBSET t s -->
       u (iterate u (DIFF s t) f) (iterate u t f) = iterate u s f)"
  by (import hollight ITERATE_DIFF)

lemma ITERATE_DIFF_GEN: "ALL u_4247::'B::type => 'B::type => 'B::type.
   monoidal u_4247 -->
   (ALL (f::'A::type => 'B::type) (s::'A::type => bool) t::'A::type => bool.
       FINITE (support u_4247 f s) &
       SUBSET (support u_4247 f t) (support u_4247 f s) -->
       u_4247 (iterate u_4247 (DIFF s t) f) (iterate u_4247 t f) =
       iterate u_4247 s f)"
  by (import hollight ITERATE_DIFF_GEN)

lemma ITERATE_CLOSED: "ALL u_4247::'B::type => 'B::type => 'B::type.
   monoidal u_4247 -->
   (ALL P::'B::type => bool.
       P (neutral u_4247) &
       (ALL (x::'B::type) y::'B::type. P x & P y --> P (u_4247 x y)) -->
       (ALL (f::'A::type => 'B::type) x::'A::type => bool.
           FINITE x & (ALL xa::'A::type. IN xa x --> P (f xa)) -->
           P (iterate u_4247 x f)))"
  by (import hollight ITERATE_CLOSED)

lemma ITERATE_CLOSED_GEN: "ALL u_4247::'B::type => 'B::type => 'B::type.
   monoidal u_4247 -->
   (ALL P::'B::type => bool.
       P (neutral u_4247) &
       (ALL (x::'B::type) y::'B::type. P x & P y --> P (u_4247 x y)) -->
       (ALL (f::'A::type => 'B::type) s::'A::type => bool.
           FINITE (support u_4247 f s) &
           (ALL x::'A::type. IN x s & f x ~= neutral u_4247 --> P (f x)) -->
           P (iterate u_4247 s f)))"
  by (import hollight ITERATE_CLOSED_GEN)

lemma ITERATE_RELATED: "ALL u_4247::'B::type => 'B::type => 'B::type.
   monoidal u_4247 -->
   (ALL R::'B::type => 'B::type => bool.
       R (neutral u_4247) (neutral u_4247) &
       (ALL (x1::'B::type) (y1::'B::type) (x2::'B::type) y2::'B::type.
           R x1 x2 & R y1 y2 --> R (u_4247 x1 y1) (u_4247 x2 y2)) -->
       (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type)
           x::'A::type => bool.
           FINITE x & (ALL xa::'A::type. IN xa x --> R (f xa) (g xa)) -->
           R (iterate u_4247 x f) (iterate u_4247 x g)))"
  by (import hollight ITERATE_RELATED)

lemma ITERATE_EQ_NEUTRAL: "ALL u_4247::'B::type => 'B::type => 'B::type.
   monoidal u_4247 -->
   (ALL (f::'A::type => 'B::type) s::'A::type => bool.
       (ALL x::'A::type. IN x s --> f x = neutral u_4247) -->
       iterate u_4247 s f = neutral u_4247)"
  by (import hollight ITERATE_EQ_NEUTRAL)

lemma ITERATE_SING: "ALL x::'B::type => 'B::type => 'B::type.
   monoidal x -->
   (ALL (f::'A::type => 'B::type) xa::'A::type.
       iterate x (INSERT xa EMPTY) f = f xa)"
  by (import hollight ITERATE_SING)

lemma ITERATE_DELTA: "ALL u_4247::'q_50438::type => 'q_50438::type => 'q_50438::type.
   monoidal u_4247 -->
   (ALL (x::'q_50457::type => 'q_50438::type) (xa::'q_50457::type)
       xb::'q_50457::type => bool.
       iterate u_4247 xb
        (%xb::'q_50457::type. COND (xb = xa) (x xb) (neutral u_4247)) =
       COND (IN xa xb) (x xa) (neutral u_4247))"
  by (import hollight ITERATE_DELTA)

lemma ITERATE_IMAGE: "ALL u_4247::'q_50536::type => 'q_50536::type => 'q_50536::type.
   monoidal u_4247 -->
   (ALL (f::'q_50535::type => 'q_50507::type)
       (g::'q_50507::type => 'q_50536::type) x::'q_50535::type => bool.
       FINITE x &
       (ALL (xa::'q_50535::type) y::'q_50535::type.
           IN xa x & IN y x & f xa = f y --> xa = y) -->
       iterate u_4247 (IMAGE f x) g = iterate u_4247 x (g o f))"
  by (import hollight ITERATE_IMAGE)

lemma ITERATE_BIJECTION: "ALL u_4247::'B::type => 'B::type => 'B::type.
   monoidal u_4247 -->
   (ALL (f::'A::type => 'B::type) (p::'A::type => 'A::type)
       s::'A::type => bool.
       FINITE s &
       (ALL x::'A::type. IN x s --> IN (p x) s) &
       (ALL y::'A::type. IN y s --> (EX! x::'A::type. IN x s & p x = y)) -->
       iterate u_4247 s f = iterate u_4247 s (f o p))"
  by (import hollight ITERATE_BIJECTION)

lemma ITERATE_ITERATE_PRODUCT: "ALL u_4247::'C::type => 'C::type => 'C::type.
   monoidal u_4247 -->
   (ALL (x::'A::type => bool) (xa::'A::type => 'B::type => bool)
       xb::'A::type => 'B::type => 'C::type.
       FINITE x & (ALL i::'A::type. IN i x --> FINITE (xa i)) -->
       iterate u_4247 x (%i::'A::type. iterate u_4247 (xa i) (xb i)) =
       iterate u_4247
        (GSPEC
          (%u::'A::type * 'B::type.
              EX (i::'A::type) j::'B::type.
                 SETSPEC u (IN i x & IN j (xa i)) (i, j)))
        (GABS
          (%f::'A::type * 'B::type => 'C::type.
              ALL (i::'A::type) j::'B::type. GEQ (f (i, j)) (xb i j))))"
  by (import hollight ITERATE_ITERATE_PRODUCT)

lemma ITERATE_EQ: "ALL u_4247::'q_50867::type => 'q_50867::type => 'q_50867::type.
   monoidal u_4247 -->
   (ALL (f::'q_50871::type => 'q_50867::type)
       (g::'q_50871::type => 'q_50867::type) x::'q_50871::type => bool.
       FINITE x & (ALL xa::'q_50871::type. IN xa x --> f xa = g xa) -->
       iterate u_4247 x f = iterate u_4247 x g)"
  by (import hollight ITERATE_EQ)

lemma ITERATE_EQ_GENERAL: "ALL u_4247::'C::type => 'C::type => 'C::type.
   monoidal u_4247 -->
   (ALL (s::'A::type => bool) (t::'B::type => bool)
       (f::'A::type => 'C::type) (g::'B::type => 'C::type)
       h::'A::type => 'B::type.
       FINITE s &
       (ALL y::'B::type. IN y t --> (EX! x::'A::type. IN x s & h x = y)) &
       (ALL x::'A::type. IN x s --> IN (h x) t & g (h x) = f x) -->
       iterate u_4247 s f = iterate u_4247 t g)"
  by (import hollight ITERATE_EQ_GENERAL)

constdefs
  nsum :: "('q_51017 => bool) => ('q_51017 => nat) => nat" 
  "(op ==::(('q_51017::type => bool) => ('q_51017::type => nat) => nat)
        => (('q_51017::type => bool) => ('q_51017::type => nat) => nat)
           => prop)
 (nsum::('q_51017::type => bool) => ('q_51017::type => nat) => nat)
 ((iterate::(nat => nat => nat)
            => ('q_51017::type => bool) => ('q_51017::type => nat) => nat)
   (HOL.plus::nat => nat => nat))"

lemma DEF_nsum: "(op =::(('q_51017::type => bool) => ('q_51017::type => nat) => nat)
       => (('q_51017::type => bool) => ('q_51017::type => nat) => nat)
          => bool)
 (nsum::('q_51017::type => bool) => ('q_51017::type => nat) => nat)
 ((iterate::(nat => nat => nat)
            => ('q_51017::type => bool) => ('q_51017::type => nat) => nat)
   (HOL.plus::nat => nat => nat))"
  by (import hollight DEF_nsum)

lemma NEUTRAL_ADD: "(op =::nat => nat => bool)
 ((neutral::(nat => nat => nat) => nat) (HOL.plus::nat => nat => nat)) (0::nat)"
  by (import hollight NEUTRAL_ADD)

lemma NEUTRAL_MUL: "neutral op * = NUMERAL_BIT1 0"
  by (import hollight NEUTRAL_MUL)

lemma MONOIDAL_ADD: "(monoidal::(nat => nat => nat) => bool) (HOL.plus::nat => nat => nat)"
  by (import hollight MONOIDAL_ADD)

lemma MONOIDAL_MUL: "(monoidal::(nat => nat => nat) => bool) (op *::nat => nat => nat)"
  by (import hollight MONOIDAL_MUL)

lemma NSUM_CLAUSES: "(ALL x::'q_51055::type => nat. nsum EMPTY x = 0) &
(ALL (x::'q_51094::type) (xa::'q_51094::type => nat)
    xb::'q_51094::type => bool.
    FINITE xb -->
    nsum (INSERT x xb) xa = COND (IN x xb) (nsum xb xa) (xa x + nsum xb xa))"
  by (import hollight NSUM_CLAUSES)

lemma NSUM_UNION: "ALL (x::'q_51120::type => nat) (xa::'q_51120::type => bool)
   xb::'q_51120::type => bool.
   FINITE xa & FINITE xb & DISJOINT xa xb -->
   nsum (hollight.UNION xa xb) x = nsum xa x + nsum xb x"
  by (import hollight NSUM_UNION)

lemma NSUM_DIFF: "ALL (f::'q_51175::type => nat) (s::'q_51175::type => bool)
   t::'q_51175::type => bool.
   FINITE s & SUBSET t s --> nsum (DIFF s t) f = nsum s f - nsum t f"
  by (import hollight NSUM_DIFF)

lemma NSUM_SUPPORT: "ALL (x::'q_51214::type => nat) xa::'q_51214::type => bool.
   FINITE (support HOL.plus x xa) --> nsum (support HOL.plus x xa) x = nsum xa x"
  by (import hollight NSUM_SUPPORT)

lemma NSUM_ADD: "ALL (f::'q_51260::type => nat) (g::'q_51260::type => nat)
   s::'q_51260::type => bool.
   FINITE s --> nsum s (%x::'q_51260::type. f x + g x) = nsum s f + nsum s g"
  by (import hollight NSUM_ADD)

lemma NSUM_CMUL: "ALL (f::'q_51298::type => nat) (c::nat) s::'q_51298::type => bool.
   FINITE s --> nsum s (%x::'q_51298::type. c * f x) = c * nsum s f"
  by (import hollight NSUM_CMUL)

lemma NSUM_LE: "ALL (x::'q_51337::type => nat) (xa::'q_51337::type => nat)
   xb::'q_51337::type => bool.
   FINITE xb & (ALL xc::'q_51337::type. IN xc xb --> <= (x xc) (xa xc)) -->
   <= (nsum xb x) (nsum xb xa)"
  by (import hollight NSUM_LE)

lemma NSUM_LT: "ALL (f::'A::type => nat) (g::'A::type => nat) s::'A::type => bool.
   FINITE s &
   (ALL x::'A::type. IN x s --> <= (f x) (g x)) &
   (EX x::'A::type. IN x s & < (f x) (g x)) -->
   < (nsum s f) (nsum s g)"
  by (import hollight NSUM_LT)

lemma NSUM_LT_ALL: "ALL (f::'q_51459::type => nat) (g::'q_51459::type => nat)
   s::'q_51459::type => bool.
   FINITE s &
   s ~= EMPTY & (ALL x::'q_51459::type. IN x s --> < (f x) (g x)) -->
   < (nsum s f) (nsum s g)"
  by (import hollight NSUM_LT_ALL)

lemma NSUM_EQ: "ALL (x::'q_51501::type => nat) (xa::'q_51501::type => nat)
   xb::'q_51501::type => bool.
   FINITE xb & (ALL xc::'q_51501::type. IN xc xb --> x xc = xa xc) -->
   nsum xb x = nsum xb xa"
  by (import hollight NSUM_EQ)

lemma NSUM_CONST: "ALL (c::nat) s::'q_51531::type => bool.
   FINITE s --> nsum s (%n::'q_51531::type. c) = CARD s * c"
  by (import hollight NSUM_CONST)

lemma NSUM_EQ_0: "ALL (x::'A::type => nat) xa::'A::type => bool.
   (ALL xb::'A::type. IN xb xa --> x xb = 0) --> nsum xa x = 0"
  by (import hollight NSUM_EQ_0)

lemma NSUM_0: "ALL x::'A::type => bool. nsum x (%n::'A::type. 0) = 0"
  by (import hollight NSUM_0)

lemma NSUM_POS_LE: "ALL (x::'q_51610::type => nat) xa::'q_51610::type => bool.
   FINITE xa & (ALL xb::'q_51610::type. IN xb xa --> <= 0 (x xb)) -->
   <= 0 (nsum xa x)"
  by (import hollight NSUM_POS_LE)

lemma NSUM_POS_BOUND: "ALL (f::'A::type => nat) (b::nat) x::'A::type => bool.
   FINITE x &
   (ALL xa::'A::type. IN xa x --> <= 0 (f xa)) & <= (nsum x f) b -->
   (ALL xa::'A::type. IN xa x --> <= (f xa) b)"
  by (import hollight NSUM_POS_BOUND)

lemma NSUM_POS_EQ_0: "ALL (x::'q_51745::type => nat) xa::'q_51745::type => bool.
   FINITE xa &
   (ALL xb::'q_51745::type. IN xb xa --> <= 0 (x xb)) & nsum xa x = 0 -->
   (ALL xb::'q_51745::type. IN xb xa --> x xb = 0)"
  by (import hollight NSUM_POS_EQ_0)

lemma NSUM_SING: "ALL (x::'q_51765::type => nat) xa::'q_51765::type.
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

lemma NSUM_IMAGE: "ALL (x::'q_51905::type => 'q_51881::type) (xa::'q_51881::type => nat)
   xb::'q_51905::type => bool.
   FINITE xb &
   (ALL (xa::'q_51905::type) y::'q_51905::type.
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

lemma NSUM_RESTRICT: "ALL (f::'q_52126::type => nat) s::'q_52126::type => bool.
   FINITE s -->
   nsum s (%x::'q_52126::type. COND (IN x s) (f x) 0) = nsum s f"
  by (import hollight NSUM_RESTRICT)

lemma NSUM_BOUND: "ALL (x::'A::type => bool) (xa::'A::type => nat) xb::nat.
   FINITE x & (ALL xc::'A::type. IN xc x --> <= (xa xc) xb) -->
   <= (nsum x xa) (CARD x * xb)"
  by (import hollight NSUM_BOUND)

lemma NSUM_BOUND_GEN: "ALL (x::'A::type => bool) (xa::'q_52201::type) b::nat.
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

lemma NSUM_BOUND_LT_ALL: "ALL (s::'q_52344::type => bool) (f::'q_52344::type => nat) b::nat.
   FINITE s & s ~= EMPTY & (ALL x::'q_52344::type. IN x s --> < (f x) b) -->
   < (nsum s f) (CARD s * b)"
  by (import hollight NSUM_BOUND_LT_ALL)

lemma NSUM_BOUND_LT_GEN: "ALL (s::'A::type => bool) (t::'q_52386::type) b::nat.
   FINITE s &
   s ~= EMPTY &
   (ALL x::'A::type.
       IN x s --> < ((f::'A::type => nat) x) (DIV b (CARD s))) -->
   < (nsum s f) b"
  by (import hollight NSUM_BOUND_LT_GEN)

lemma NSUM_UNION_EQ: "ALL (s::'q_52445::type => bool) (t::'q_52445::type => bool)
   u::'q_52445::type => bool.
   FINITE u & hollight.INTER s t = EMPTY & hollight.UNION s t = u -->
   nsum s (f::'q_52445::type => nat) + nsum t f = nsum u f"
  by (import hollight NSUM_UNION_EQ)

lemma NSUM_EQ_SUPERSET: "ALL (f::'A::type => nat) (s::'A::type => bool) t::'A::type => bool.
   FINITE t &
   SUBSET t s &
   (ALL x::'A::type. IN x t --> f x = (g::'A::type => nat) x) &
   (ALL x::'A::type. IN x s & ~ IN x t --> f x = 0) -->
   nsum s f = nsum t g"
  by (import hollight NSUM_EQ_SUPERSET)

lemma NSUM_RESTRICT_SET: "ALL (s::'A::type => bool) (f::'A::type => nat) r::'q_52556::type.
   FINITE s -->
   nsum
    (GSPEC
      (%u::'A::type.
          EX x::'A::type. SETSPEC u (IN x s & (P::'A::type => bool) x) x))
    f =
   nsum s (%x::'A::type. COND (P x) (f x) 0)"
  by (import hollight NSUM_RESTRICT_SET)

lemma NSUM_NSUM_RESTRICT: "ALL (R::'q_52685::type => 'q_52684::type => bool)
   (f::'q_52685::type => 'q_52684::type => nat) (s::'q_52685::type => bool)
   t::'q_52684::type => bool.
   FINITE s & FINITE t -->
   nsum s
    (%x::'q_52685::type.
        nsum
         (GSPEC
           (%u::'q_52684::type.
               EX y::'q_52684::type. SETSPEC u (IN y t & R x y) y))
         (f x)) =
   nsum t
    (%y::'q_52684::type.
        nsum
         (GSPEC
           (%u::'q_52685::type.
               EX x::'q_52685::type. SETSPEC u (IN x s & R x y) x))
         (%x::'q_52685::type. f x y))"
  by (import hollight NSUM_NSUM_RESTRICT)

lemma CARD_EQ_NSUM: "ALL x::'q_52704::type => bool.
   FINITE x --> CARD x = nsum x (%x::'q_52704::type. NUMERAL_BIT1 0)"
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

lemma NSUM_SUBSET_SIMPLE: "ALL (u::'q_53164::type => bool) (v::'q_53164::type => bool)
   f::'q_53164::type => nat.
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

lemma NSUM_EQ_0_NUMSEG: "ALL (x::nat => nat) xa::'q_53403::type.
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

lemma NSUM_BIJECTION: "ALL (x::'A::type => nat) (xa::'A::type => 'A::type) xb::'A::type => bool.
   FINITE xb &
   (ALL x::'A::type. IN x xb --> IN (xa x) xb) &
   (ALL y::'A::type. IN y xb --> (EX! x::'A::type. IN x xb & xa x = y)) -->
   nsum xb x = nsum xb (x o xa)"
  by (import hollight NSUM_BIJECTION)

lemma NSUM_NSUM_PRODUCT: "ALL (x::'A::type => bool) (xa::'A::type => 'B::type => bool)
   xb::'A::type => 'B::type => nat.
   FINITE x & (ALL i::'A::type. IN i x --> FINITE (xa i)) -->
   nsum x (%x::'A::type. nsum (xa x) (xb x)) =
   nsum
    (GSPEC
      (%u::'A::type * 'B::type.
          EX (i::'A::type) j::'B::type.
             SETSPEC u (IN i x & IN j (xa i)) (i, j)))
    (GABS
      (%f::'A::type * 'B::type => nat.
          ALL (i::'A::type) j::'B::type. GEQ (f (i, j)) (xb i j)))"
  by (import hollight NSUM_NSUM_PRODUCT)

lemma NSUM_EQ_GENERAL: "ALL (x::'A::type => bool) (xa::'B::type => bool) (xb::'A::type => nat)
   (xc::'B::type => nat) xd::'A::type => 'B::type.
   FINITE x &
   (ALL y::'B::type. IN y xa --> (EX! xa::'A::type. IN xa x & xd xa = y)) &
   (ALL xe::'A::type. IN xe x --> IN (xd xe) xa & xc (xd xe) = xb xe) -->
   nsum x xb = nsum xa xc"
  by (import hollight NSUM_EQ_GENERAL)

consts
  sum :: "('q_54215 => bool) => ('q_54215 => hollight.real) => hollight.real" 

defs
  sum_def: "(op ==::(('q_54215::type => bool)
         => ('q_54215::type => hollight.real) => hollight.real)
        => (('q_54215::type => bool)
            => ('q_54215::type => hollight.real) => hollight.real)
           => prop)
 (hollight.sum::('q_54215::type => bool)
                => ('q_54215::type => hollight.real) => hollight.real)
 ((iterate::(hollight.real => hollight.real => hollight.real)
            => ('q_54215::type => bool)
               => ('q_54215::type => hollight.real) => hollight.real)
   (real_add::hollight.real => hollight.real => hollight.real))"

lemma DEF_sum: "(op =::(('q_54215::type => bool)
        => ('q_54215::type => hollight.real) => hollight.real)
       => (('q_54215::type => bool)
           => ('q_54215::type => hollight.real) => hollight.real)
          => bool)
 (hollight.sum::('q_54215::type => bool)
                => ('q_54215::type => hollight.real) => hollight.real)
 ((iterate::(hollight.real => hollight.real => hollight.real)
            => ('q_54215::type => bool)
               => ('q_54215::type => hollight.real) => hollight.real)
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

lemma SUM_CLAUSES: "(ALL x::'q_54257::type => hollight.real.
    hollight.sum EMPTY x = real_of_num 0) &
(ALL (x::'q_54298::type) (xa::'q_54298::type => hollight.real)
    xb::'q_54298::type => bool.
    FINITE xb -->
    hollight.sum (INSERT x xb) xa =
    COND (IN x xb) (hollight.sum xb xa)
     (real_add (xa x) (hollight.sum xb xa)))"
  by (import hollight SUM_CLAUSES)

lemma SUM_UNION: "ALL (x::'q_54324::type => hollight.real) (xa::'q_54324::type => bool)
   xb::'q_54324::type => bool.
   FINITE xa & FINITE xb & DISJOINT xa xb -->
   hollight.sum (hollight.UNION xa xb) x =
   real_add (hollight.sum xa x) (hollight.sum xb x)"
  by (import hollight SUM_UNION)

lemma SUM_DIFF: "ALL (x::'q_54364::type => hollight.real) (xa::'q_54364::type => bool)
   xb::'q_54364::type => bool.
   FINITE xa & SUBSET xb xa -->
   hollight.sum (DIFF xa xb) x =
   real_sub (hollight.sum xa x) (hollight.sum xb x)"
  by (import hollight SUM_DIFF)

lemma SUM_SUPPORT: "ALL (x::'q_54403::type => hollight.real) xa::'q_54403::type => bool.
   FINITE (support real_add x xa) -->
   hollight.sum (support real_add x xa) x = hollight.sum xa x"
  by (import hollight SUM_SUPPORT)

lemma SUM_ADD: "ALL (f::'q_54449::type => hollight.real)
   (g::'q_54449::type => hollight.real) s::'q_54449::type => bool.
   FINITE s -->
   hollight.sum s (%x::'q_54449::type. real_add (f x) (g x)) =
   real_add (hollight.sum s f) (hollight.sum s g)"
  by (import hollight SUM_ADD)

lemma SUM_CMUL: "ALL (f::'q_54487::type => hollight.real) (c::hollight.real)
   s::'q_54487::type => bool.
   FINITE s -->
   hollight.sum s (%x::'q_54487::type. real_mul c (f x)) =
   real_mul c (hollight.sum s f)"
  by (import hollight SUM_CMUL)

lemma SUM_NEG: "ALL (x::'q_54530::type => hollight.real) xa::'q_54530::type => bool.
   FINITE xa -->
   hollight.sum xa (%xa::'q_54530::type. real_neg (x xa)) =
   real_neg (hollight.sum xa x)"
  by (import hollight SUM_NEG)

lemma SUM_SUB: "ALL (x::'q_54565::type => hollight.real)
   (xa::'q_54565::type => hollight.real) xb::'q_54565::type => bool.
   FINITE xb -->
   hollight.sum xb (%xb::'q_54565::type. real_sub (x xb) (xa xb)) =
   real_sub (hollight.sum xb x) (hollight.sum xb xa)"
  by (import hollight SUM_SUB)

lemma SUM_LE: "ALL (x::'q_54607::type => hollight.real)
   (xa::'q_54607::type => hollight.real) xb::'q_54607::type => bool.
   FINITE xb &
   (ALL xc::'q_54607::type. IN xc xb --> real_le (x xc) (xa xc)) -->
   real_le (hollight.sum xb x) (hollight.sum xb xa)"
  by (import hollight SUM_LE)

lemma SUM_LT: "ALL (f::'A::type => hollight.real) (g::'A::type => hollight.real)
   s::'A::type => bool.
   FINITE s &
   (ALL x::'A::type. IN x s --> real_le (f x) (g x)) &
   (EX x::'A::type. IN x s & real_lt (f x) (g x)) -->
   real_lt (hollight.sum s f) (hollight.sum s g)"
  by (import hollight SUM_LT)

lemma SUM_LT_ALL: "ALL (f::'q_54729::type => hollight.real)
   (g::'q_54729::type => hollight.real) s::'q_54729::type => bool.
   FINITE s &
   s ~= EMPTY & (ALL x::'q_54729::type. IN x s --> real_lt (f x) (g x)) -->
   real_lt (hollight.sum s f) (hollight.sum s g)"
  by (import hollight SUM_LT_ALL)

lemma SUM_EQ: "ALL (x::'q_54771::type => hollight.real)
   (xa::'q_54771::type => hollight.real) xb::'q_54771::type => bool.
   FINITE xb & (ALL xc::'q_54771::type. IN xc xb --> x xc = xa xc) -->
   hollight.sum xb x = hollight.sum xb xa"
  by (import hollight SUM_EQ)

lemma SUM_ABS: "ALL (f::'q_54830::type => hollight.real) s::'q_54830::type => bool.
   FINITE s -->
   real_le (real_abs (hollight.sum s f))
    (hollight.sum s (%x::'q_54830::type. real_abs (f x)))"
  by (import hollight SUM_ABS)

lemma SUM_CONST: "ALL (c::hollight.real) s::'q_54851::type => bool.
   FINITE s -->
   hollight.sum s (%n::'q_54851::type. c) =
   real_mul (real_of_num (CARD s)) c"
  by (import hollight SUM_CONST)

lemma SUM_EQ_0: "ALL (x::'A::type => hollight.real) xa::'A::type => bool.
   (ALL xb::'A::type. IN xb xa --> x xb = real_of_num 0) -->
   hollight.sum xa x = real_of_num 0"
  by (import hollight SUM_EQ_0)

lemma SUM_0: "ALL x::'A::type => bool.
   hollight.sum x (%n::'A::type. real_of_num 0) = real_of_num 0"
  by (import hollight SUM_0)

lemma SUM_POS_LE: "ALL (x::'q_54944::type => hollight.real) xa::'q_54944::type => bool.
   FINITE xa &
   (ALL xb::'q_54944::type. IN xb xa --> real_le (real_of_num 0) (x xb)) -->
   real_le (real_of_num 0) (hollight.sum xa x)"
  by (import hollight SUM_POS_LE)

lemma SUM_POS_BOUND: "ALL (f::'A::type => hollight.real) (b::hollight.real) x::'A::type => bool.
   FINITE x &
   (ALL xa::'A::type. IN xa x --> real_le (real_of_num 0) (f xa)) &
   real_le (hollight.sum x f) b -->
   (ALL xa::'A::type. IN xa x --> real_le (f xa) b)"
  by (import hollight SUM_POS_BOUND)

lemma SUM_POS_EQ_0: "ALL (x::'q_55091::type => hollight.real) xa::'q_55091::type => bool.
   FINITE xa &
   (ALL xb::'q_55091::type. IN xb xa --> real_le (real_of_num 0) (x xb)) &
   hollight.sum xa x = real_of_num 0 -->
   (ALL xb::'q_55091::type. IN xb xa --> x xb = real_of_num 0)"
  by (import hollight SUM_POS_EQ_0)

lemma SUM_SING: "ALL (x::'q_55113::type => hollight.real) xa::'q_55113::type.
   hollight.sum (INSERT xa EMPTY) x = x xa"
  by (import hollight SUM_SING)

lemma SUM_DELTA: "ALL (x::'A::type => bool) xa::'A::type.
   hollight.sum x
    (%x::'A::type. COND (x = xa) (b::hollight.real) (real_of_num 0)) =
   COND (IN xa x) b (real_of_num 0)"
  by (import hollight SUM_DELTA)

lemma SUM_SWAP: "ALL (f::'A::type => 'B::type => hollight.real) (x::'A::type => bool)
   xa::'B::type => bool.
   FINITE x & FINITE xa -->
   hollight.sum x (%i::'A::type. hollight.sum xa (f i)) =
   hollight.sum xa (%j::'B::type. hollight.sum x (%i::'A::type. f i j))"
  by (import hollight SUM_SWAP)

lemma SUM_IMAGE: "ALL (x::'q_55257::type => 'q_55233::type)
   (xa::'q_55233::type => hollight.real) xb::'q_55257::type => bool.
   FINITE xb &
   (ALL (xa::'q_55257::type) y::'q_55257::type.
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

lemma SUM_RESTRICT: "ALL (f::'q_55484::type => hollight.real) s::'q_55484::type => bool.
   FINITE s -->
   hollight.sum s
    (%x::'q_55484::type. COND (IN x s) (f x) (real_of_num 0)) =
   hollight.sum s f"
  by (import hollight SUM_RESTRICT)

lemma SUM_BOUND: "ALL (x::'A::type => bool) (xa::'A::type => hollight.real) xb::hollight.real.
   FINITE x & (ALL xc::'A::type. IN xc x --> real_le (xa xc) xb) -->
   real_le (hollight.sum x xa) (real_mul (real_of_num (CARD x)) xb)"
  by (import hollight SUM_BOUND)

lemma SUM_BOUND_GEN: "ALL (s::'A::type => bool) (t::'q_55543::type) b::hollight.real.
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

lemma SUM_BOUND_LT_ALL: "ALL (s::'q_55748::type => bool) (f::'q_55748::type => hollight.real)
   b::hollight.real.
   FINITE s &
   s ~= EMPTY & (ALL x::'q_55748::type. IN x s --> real_lt (f x) b) -->
   real_lt (hollight.sum s f) (real_mul (real_of_num (CARD s)) b)"
  by (import hollight SUM_BOUND_LT_ALL)

lemma SUM_BOUND_LT_GEN: "ALL (s::'A::type => bool) (t::'q_55770::type) b::hollight.real.
   FINITE s &
   s ~= EMPTY &
   (ALL x::'A::type.
       IN x s -->
       real_lt ((f::'A::type => hollight.real) x)
        (real_div b (real_of_num (CARD s)))) -->
   real_lt (hollight.sum s f) b"
  by (import hollight SUM_BOUND_LT_GEN)

lemma SUM_UNION_EQ: "ALL (s::'q_55831::type => bool) (t::'q_55831::type => bool)
   u::'q_55831::type => bool.
   FINITE u & hollight.INTER s t = EMPTY & hollight.UNION s t = u -->
   real_add (hollight.sum s (f::'q_55831::type => hollight.real))
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

lemma SUM_RESTRICT_SET: "ALL (s::'A::type => bool) (f::'A::type => hollight.real) r::'q_55944::type.
   FINITE s -->
   hollight.sum
    (GSPEC
      (%u::'A::type.
          EX x::'A::type. SETSPEC u (IN x s & (P::'A::type => bool) x) x))
    f =
   hollight.sum s (%x::'A::type. COND (P x) (f x) (real_of_num 0))"
  by (import hollight SUM_RESTRICT_SET)

lemma SUM_SUM_RESTRICT: "ALL (R::'q_56075::type => 'q_56074::type => bool)
   (f::'q_56075::type => 'q_56074::type => hollight.real)
   (s::'q_56075::type => bool) t::'q_56074::type => bool.
   FINITE s & FINITE t -->
   hollight.sum s
    (%x::'q_56075::type.
        hollight.sum
         (GSPEC
           (%u::'q_56074::type.
               EX y::'q_56074::type. SETSPEC u (IN y t & R x y) y))
         (f x)) =
   hollight.sum t
    (%y::'q_56074::type.
        hollight.sum
         (GSPEC
           (%u::'q_56075::type.
               EX x::'q_56075::type. SETSPEC u (IN x s & R x y) x))
         (%x::'q_56075::type. f x y))"
  by (import hollight SUM_SUM_RESTRICT)

lemma CARD_EQ_SUM: "ALL x::'q_56096::type => bool.
   FINITE x -->
   real_of_num (CARD x) =
   hollight.sum x (%x::'q_56096::type. real_of_num (NUMERAL_BIT1 0))"
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

lemma REAL_OF_NUM_SUM: "ALL (f::'q_56493::type => nat) s::'q_56493::type => bool.
   FINITE s -->
   real_of_num (nsum s f) =
   hollight.sum s (%x::'q_56493::type. real_of_num (f x))"
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

lemma SUM_EQ_0_NUMSEG: "ALL (x::nat => hollight.real) xa::'q_57019::type.
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

lemma SUM_OFFSET: "ALL (x::nat => hollight.real) (xa::nat) xb::nat.
   hollight.sum (dotdot (xa + xb) ((n::nat) + xb)) x =
   hollight.sum (dotdot xa n) (%i::nat. x (i + xb))"
  by (import hollight SUM_OFFSET)

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

lemma SUM_BIJECTION: "ALL (x::'A::type => hollight.real) (xa::'A::type => 'A::type)
   xb::'A::type => bool.
   FINITE xb &
   (ALL x::'A::type. IN x xb --> IN (xa x) xb) &
   (ALL y::'A::type. IN y xb --> (EX! x::'A::type. IN x xb & xa x = y)) -->
   hollight.sum xb x = hollight.sum xb (x o xa)"
  by (import hollight SUM_BIJECTION)

lemma SUM_SUM_PRODUCT: "ALL (x::'A::type => bool) (xa::'A::type => 'B::type => bool)
   xb::'A::type => 'B::type => hollight.real.
   FINITE x & (ALL i::'A::type. IN i x --> FINITE (xa i)) -->
   hollight.sum x (%x::'A::type. hollight.sum (xa x) (xb x)) =
   hollight.sum
    (GSPEC
      (%u::'A::type * 'B::type.
          EX (i::'A::type) j::'B::type.
             SETSPEC u (IN i x & IN j (xa i)) (i, j)))
    (GABS
      (%f::'A::type * 'B::type => hollight.real.
          ALL (i::'A::type) j::'B::type. GEQ (f (i, j)) (xb i j)))"
  by (import hollight SUM_SUM_PRODUCT)

lemma SUM_EQ_GENERAL: "ALL (x::'A::type => bool) (xa::'B::type => bool)
   (xb::'A::type => hollight.real) (xc::'B::type => hollight.real)
   xd::'A::type => 'B::type.
   FINITE x &
   (ALL y::'B::type. IN y xa --> (EX! xa::'A::type. IN xa x & xd xa = y)) &
   (ALL xe::'A::type. IN xe x --> IN (xd xe) xa & xc (xd xe) = xb xe) -->
   hollight.sum x xb = hollight.sum xa xc"
  by (import hollight SUM_EQ_GENERAL)

constdefs
  CASEWISE :: "(('q_57926 => 'q_57930) * ('q_57931 => 'q_57926 => 'q_57890)) hollight.list
=> 'q_57931 => 'q_57930 => 'q_57890" 
  "CASEWISE ==
SOME CASEWISE::(('q_57926::type => 'q_57930::type) *
                ('q_57931::type
                 => 'q_57926::type => 'q_57890::type)) hollight.list
               => 'q_57931::type => 'q_57930::type => 'q_57890::type.
   (ALL (f::'q_57931::type) x::'q_57930::type.
       CASEWISE NIL f x = (SOME y::'q_57890::type. True)) &
   (ALL (h::('q_57926::type => 'q_57930::type) *
            ('q_57931::type => 'q_57926::type => 'q_57890::type))
       (t::(('q_57926::type => 'q_57930::type) *
            ('q_57931::type
             => 'q_57926::type => 'q_57890::type)) hollight.list)
       (f::'q_57931::type) x::'q_57930::type.
       CASEWISE (CONS h t) f x =
       COND (EX y::'q_57926::type. fst h y = x)
        (snd h f (SOME y::'q_57926::type. fst h y = x)) (CASEWISE t f x))"

lemma DEF_CASEWISE: "CASEWISE =
(SOME CASEWISE::(('q_57926::type => 'q_57930::type) *
                 ('q_57931::type
                  => 'q_57926::type => 'q_57890::type)) hollight.list
                => 'q_57931::type => 'q_57930::type => 'q_57890::type.
    (ALL (f::'q_57931::type) x::'q_57930::type.
        CASEWISE NIL f x = (SOME y::'q_57890::type. True)) &
    (ALL (h::('q_57926::type => 'q_57930::type) *
             ('q_57931::type => 'q_57926::type => 'q_57890::type))
        (t::(('q_57926::type => 'q_57930::type) *
             ('q_57931::type
              => 'q_57926::type => 'q_57890::type)) hollight.list)
        (f::'q_57931::type) x::'q_57930::type.
        CASEWISE (CONS h t) f x =
        COND (EX y::'q_57926::type. fst h y = x)
         (snd h f (SOME y::'q_57926::type. fst h y = x)) (CASEWISE t f x)))"
  by (import hollight DEF_CASEWISE)

lemma CASEWISE: "(op &::bool => bool => bool)
 ((op =::'q_57950::type => 'q_57950::type => bool)
   ((CASEWISE::(('q_57942::type => 'q_57990::type) *
                ('q_57991::type
                 => 'q_57942::type => 'q_57950::type)) hollight.list
               => 'q_57991::type => 'q_57990::type => 'q_57950::type)
     (NIL::(('q_57942::type => 'q_57990::type) *
            ('q_57991::type
             => 'q_57942::type => 'q_57950::type)) hollight.list)
     (f::'q_57991::type) (x::'q_57990::type))
   ((Eps::('q_57950::type => bool) => 'q_57950::type)
     (%y::'q_57950::type. True::bool)))
 ((op =::'q_57951::type => 'q_57951::type => bool)
   ((CASEWISE::(('q_57993::type => 'q_57990::type) *
                ('q_57991::type
                 => 'q_57993::type => 'q_57951::type)) hollight.list
               => 'q_57991::type => 'q_57990::type => 'q_57951::type)
     ((CONS::('q_57993::type => 'q_57990::type) *
             ('q_57991::type => 'q_57993::type => 'q_57951::type)
             => (('q_57993::type => 'q_57990::type) *
                 ('q_57991::type
                  => 'q_57993::type => 'q_57951::type)) hollight.list
                => (('q_57993::type => 'q_57990::type) *
                    ('q_57991::type
                     => 'q_57993::type => 'q_57951::type)) hollight.list)
       ((Pair::('q_57993::type => 'q_57990::type)
               => ('q_57991::type => 'q_57993::type => 'q_57951::type)
                  => ('q_57993::type => 'q_57990::type) *
                     ('q_57991::type => 'q_57993::type => 'q_57951::type))
         (s::'q_57993::type => 'q_57990::type)
         (t::'q_57991::type => 'q_57993::type => 'q_57951::type))
       (clauses::(('q_57993::type => 'q_57990::type) *
                  ('q_57991::type
                   => 'q_57993::type => 'q_57951::type)) hollight.list))
     f x)
   ((COND::bool => 'q_57951::type => 'q_57951::type => 'q_57951::type)
     ((Ex::('q_57993::type => bool) => bool)
       (%y::'q_57993::type.
           (op =::'q_57990::type => 'q_57990::type => bool) (s y) x))
     (t f ((Eps::('q_57993::type => bool) => 'q_57993::type)
            (%y::'q_57993::type.
                (op =::'q_57990::type => 'q_57990::type => bool) (s y) x)))
     ((CASEWISE::(('q_57993::type => 'q_57990::type) *
                  ('q_57991::type
                   => 'q_57993::type => 'q_57951::type)) hollight.list
                 => 'q_57991::type => 'q_57990::type => 'q_57951::type)
       clauses f x)))"
  by (import hollight CASEWISE)

lemma CASEWISE_CASES: "ALL (clauses::(('q_58085::type => 'q_58082::type) *
               ('q_58083::type
                => 'q_58085::type => 'q_58092::type)) hollight.list)
   (c::'q_58083::type) x::'q_58082::type.
   (EX (s::'q_58085::type => 'q_58082::type)
       (t::'q_58083::type => 'q_58085::type => 'q_58092::type)
       a::'q_58085::type.
       MEM (s, t) clauses & s a = x & CASEWISE clauses c x = t c a) |
   ~ (EX (s::'q_58085::type => 'q_58082::type)
         (t::'q_58083::type => 'q_58085::type => 'q_58092::type)
         a::'q_58085::type. MEM (s, t) clauses & s a = x) &
   CASEWISE clauses c x = (SOME y::'q_58092::type. True)"
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
  admissible :: "('q_58228 => 'q_58221 => bool)
=> (('q_58228 => 'q_58224) => 'q_58234 => bool)
   => ('q_58234 => 'q_58221)
      => (('q_58228 => 'q_58224) => 'q_58234 => 'q_58229) => bool" 
  "admissible ==
%(u::'q_58228::type => 'q_58221::type => bool)
   (ua::('q_58228::type => 'q_58224::type) => 'q_58234::type => bool)
   (ub::'q_58234::type => 'q_58221::type)
   uc::('q_58228::type => 'q_58224::type)
       => 'q_58234::type => 'q_58229::type.
   ALL (f::'q_58228::type => 'q_58224::type)
      (g::'q_58228::type => 'q_58224::type) a::'q_58234::type.
      ua f a &
      ua g a & (ALL z::'q_58228::type. u z (ub a) --> f z = g z) -->
      uc f a = uc g a"

lemma DEF_admissible: "admissible =
(%(u::'q_58228::type => 'q_58221::type => bool)
    (ua::('q_58228::type => 'q_58224::type) => 'q_58234::type => bool)
    (ub::'q_58234::type => 'q_58221::type)
    uc::('q_58228::type => 'q_58224::type)
        => 'q_58234::type => 'q_58229::type.
    ALL (f::'q_58228::type => 'q_58224::type)
       (g::'q_58228::type => 'q_58224::type) a::'q_58234::type.
       ua f a &
       ua g a & (ALL z::'q_58228::type. u z (ub a) --> f z = g z) -->
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
  superadmissible :: "('q_58378 => 'q_58378 => bool)
=> (('q_58378 => 'q_58380) => 'q_58386 => bool)
   => ('q_58386 => 'q_58378)
      => (('q_58378 => 'q_58380) => 'q_58386 => 'q_58380) => bool" 
  "superadmissible ==
%(u::'q_58378::type => 'q_58378::type => bool)
   (ua::('q_58378::type => 'q_58380::type) => 'q_58386::type => bool)
   (ub::'q_58386::type => 'q_58378::type)
   uc::('q_58378::type => 'q_58380::type)
       => 'q_58386::type => 'q_58380::type.
   admissible u
    (%(f::'q_58378::type => 'q_58380::type) a::'q_58386::type. True) ub
    ua -->
   tailadmissible u ua ub uc"

lemma DEF_superadmissible: "superadmissible =
(%(u::'q_58378::type => 'q_58378::type => bool)
    (ua::('q_58378::type => 'q_58380::type) => 'q_58386::type => bool)
    (ub::'q_58386::type => 'q_58378::type)
    uc::('q_58378::type => 'q_58380::type)
        => 'q_58386::type => 'q_58380::type.
    admissible u
     (%(f::'q_58378::type => 'q_58380::type) a::'q_58386::type. True) ub
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

lemma ADMISSIBLE_COND: "ALL (u_353::'A::type => 'q_58766::type => bool)
   (p::('A::type => 'B::type) => 'P::type => bool)
   (P::('A::type => 'B::type) => 'P::type => bool)
   (s::'P::type => 'q_58766::type)
   (h::('A::type => 'B::type) => 'P::type => 'B::type)
   k::('A::type => 'B::type) => 'P::type => 'B::type.
   admissible u_353 p s P &
   admissible u_353 (%(f::'A::type => 'B::type) x::'P::type. p f x & P f x)
    s h &
   admissible u_353
    (%(f::'A::type => 'B::type) x::'P::type. p f x & ~ P f x) s k -->
   admissible u_353 p s
    (%(f::'A::type => 'B::type) x::'P::type. COND (P f x) (h f x) (k f x))"
  by (import hollight ADMISSIBLE_COND)

lemma ADMISSIBLE_CONST: "admissible (u_353::'q_58841::type => 'q_58840::type => bool)
 (p::('q_58841::type => 'q_58842::type) => 'q_58843::type => bool)
 (s::'q_58843::type => 'q_58840::type)
 (%f::'q_58841::type => 'q_58842::type. c::'q_58843::type => 'q_58844::type)"
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

lemma ADMISSIBLE_NSUM: "ALL (x::'B::type => 'A::type => bool)
   (xa::('B::type => 'C::type) => 'P::type => bool)
   (xb::'P::type => 'A::type)
   (xc::('B::type => 'C::type) => 'P::type => nat => nat)
   (xd::'P::type => nat) xe::'P::type => nat.
   (ALL xf::nat.
       admissible x
        (%(f::'B::type => 'C::type) x::'P::type.
            <= (xd x) xf & <= xf (xe x) & xa f x)
        xb (%(f::'B::type => 'C::type) x::'P::type. xc f x xf)) -->
   admissible x xa xb
    (%(f::'B::type => 'C::type) x::'P::type.
        nsum (dotdot (xd x) (xe x)) (xc f x))"
  by (import hollight ADMISSIBLE_NSUM)

lemma ADMISSIBLE_SUM: "ALL (x::'B::type => 'A::type => bool)
   (xa::('B::type => 'C::type) => 'P::type => bool)
   (xb::'P::type => 'A::type)
   (xc::('B::type => 'C::type) => 'P::type => nat => hollight.real)
   (xd::'P::type => nat) xe::'P::type => nat.
   (ALL xf::nat.
       admissible x
        (%(f::'B::type => 'C::type) x::'P::type.
            <= (xd x) xf & <= xf (xe x) & xa f x)
        xb (%(f::'B::type => 'C::type) x::'P::type. xc f x xf)) -->
   admissible x xa xb
    (%(f::'B::type => 'C::type) x::'P::type.
        hollight.sum (dotdot (xd x) (xe x)) (xc f x))"
  by (import hollight ADMISSIBLE_SUM)

lemma WF_REC_CASES: "ALL (u_353::'A::type => 'A::type => bool)
   clauses::(('P::type => 'A::type) *
             (('A::type => 'B::type)
              => 'P::type => 'B::type)) hollight.list.
   WF u_353 &
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
                      P f a & u_353 y (G f a) --> u_353 y (s a)) &
                  (ALL (f::'A::type => 'B::type) (g::'A::type => 'B::type)
                      a::'P::type.
                      (ALL z::'A::type. u_353 z (s a) --> f z = g z) -->
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

lemma cth: "ALL (p1::'A::type => 'q_59947::type)
   (p2::'q_59958::type => 'A::type => 'q_59952::type)
   (p1'::'A::type => 'q_59947::type)
   p2'::'q_59958::type => 'A::type => 'q_59952::type.
   (ALL (c::'q_59958::type) (x::'A::type) y::'A::type.
       p1 x = p1' y --> p2 c x = p2' c y) -->
   (ALL (c::'q_59958::type) (x::'A::type) y::'A::type.
       p1' x = p1 y --> p2' c x = p2 c y)"
  by (import hollight cth)

lemma RECURSION_CASEWISE_PAIRWISE: "ALL x::(('q_59995::type => 'q_59975::type) *
        (('q_59975::type => 'q_59991::type)
         => 'q_59995::type => 'q_59991::type)) hollight.list.
   (EX u::'q_59975::type => 'q_59975::type => bool.
       WF u &
       ALL_list
        (GABS
          (%f::('q_59995::type => 'q_59975::type) *
               (('q_59975::type => 'q_59991::type)
                => 'q_59995::type => 'q_59991::type)
               => bool.
              ALL (s::'q_59995::type => 'q_59975::type)
                 t::('q_59975::type => 'q_59991::type)
                    => 'q_59995::type => 'q_59991::type.
                 GEQ (f (s, t))
                  (tailadmissible u
                    (%(f::'q_59975::type => 'q_59991::type)
                        a::'q_59995::type. True)
                    s t)))
        x) &
   ALL_list
    (GABS
      (%f::('q_59995::type => 'q_59975::type) *
           (('q_59975::type => 'q_59991::type)
            => 'q_59995::type => 'q_59991::type)
           => bool.
          ALL (a::'q_59995::type => 'q_59975::type)
             b::('q_59975::type => 'q_59991::type)
                => 'q_59995::type => 'q_59991::type.
             GEQ (f (a, b))
              (ALL (c::'q_59975::type => 'q_59991::type) (x::'q_59995::type)
                  y::'q_59995::type. a x = a y --> b c x = b c y)))
    x &
   PAIRWISE
    (GABS
      (%f::('q_59995::type => 'q_59975::type) *
           (('q_59975::type => 'q_59991::type)
            => 'q_59995::type => 'q_59991::type)
           => ('q_59995::type => 'q_59975::type) *
              (('q_59975::type => 'q_59991::type)
               => 'q_59995::type => 'q_59991::type)
              => bool.
          ALL (s::'q_59995::type => 'q_59975::type)
             t::('q_59975::type => 'q_59991::type)
                => 'q_59995::type => 'q_59991::type.
             GEQ (f (s, t))
              (GABS
                (%f::('q_59995::type => 'q_59975::type) *
                     (('q_59975::type => 'q_59991::type)
                      => 'q_59995::type => 'q_59991::type)
                     => bool.
                    ALL (s'::'q_59995::type => 'q_59975::type)
                       t'::('q_59975::type => 'q_59991::type)
                           => 'q_59995::type => 'q_59991::type.
                       GEQ (f (s', t'))
                        (ALL (c::'q_59975::type => 'q_59991::type)
                            (x::'q_59995::type) y::'q_59995::type.
                            s x = s' y --> t c x = t' c y)))))
    x -->
   (EX f::'q_59975::type => 'q_59991::type.
       ALL_list
        (GABS
          (%fa::('q_59995::type => 'q_59975::type) *
                (('q_59975::type => 'q_59991::type)
                 => 'q_59995::type => 'q_59991::type)
                => bool.
              ALL (s::'q_59995::type => 'q_59975::type)
                 t::('q_59975::type => 'q_59991::type)
                    => 'q_59995::type => 'q_59991::type.
                 GEQ (fa (s, t)) (ALL x::'q_59995::type. f (s x) = t f x)))
        x)"
  by (import hollight RECURSION_CASEWISE_PAIRWISE)

lemma SUPERADMISSIBLE_T: "superadmissible (u_353::'q_60105::type => 'q_60105::type => bool)
 (%(f::'q_60105::type => 'q_60107::type) x::'q_60111::type. True)
 (s::'q_60111::type => 'q_60105::type)
 (t::('q_60105::type => 'q_60107::type)
     => 'q_60111::type => 'q_60107::type) =
tailadmissible u_353
 (%(f::'q_60105::type => 'q_60107::type) x::'q_60111::type. True) s t"
  by (import hollight SUPERADMISSIBLE_T)

;end_setup

end

