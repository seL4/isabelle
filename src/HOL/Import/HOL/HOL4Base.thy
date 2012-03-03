(* AUTOMATICALLY GENERATED, DO NOT EDIT! *)

theory HOL4Base imports "../HOL4Compat" "../HOL4Syntax" begin

setup_theory "~~/src/HOL/Import/HOL" bool

definition
  ARB :: "'a"  where
  "ARB == SOME x. True"

lemma ARB_DEF: "ARB = (SOME x. True)"
  sorry

definition
  IN :: "'a => ('a => bool) => bool"  where
  "IN == %x f. f x"

lemma IN_DEF: "IN = (%x f. f x)"
  sorry

definition
  RES_FORALL :: "('a => bool) => ('a => bool) => bool"  where
  "RES_FORALL == %p m. ALL x. IN x p --> m x"

lemma RES_FORALL_DEF: "RES_FORALL = (%p m. ALL x. IN x p --> m x)"
  sorry

definition
  RES_EXISTS :: "('a => bool) => ('a => bool) => bool"  where
  "RES_EXISTS == %p m. EX x. IN x p & m x"

lemma RES_EXISTS_DEF: "RES_EXISTS = (%p m. EX x. IN x p & m x)"
  sorry

definition
  RES_EXISTS_UNIQUE :: "('a => bool) => ('a => bool) => bool"  where
  "RES_EXISTS_UNIQUE ==
%p m. RES_EXISTS p m &
      RES_FORALL p (%x. RES_FORALL p (%y. m x & m y --> x = y))"

lemma RES_EXISTS_UNIQUE_DEF: "RES_EXISTS_UNIQUE =
(%p m. RES_EXISTS p m &
       RES_FORALL p (%x. RES_FORALL p (%y. m x & m y --> x = y)))"
  sorry

definition
  RES_SELECT :: "('a => bool) => ('a => bool) => 'a"  where
  "RES_SELECT == %p m. SOME x. IN x p & m x"

lemma RES_SELECT_DEF: "RES_SELECT = (%p m. SOME x. IN x p & m x)"
  sorry

lemma EXCLUDED_MIDDLE: "t | ~ t"
  sorry

lemma FORALL_THM: "All f = All f"
  sorry

lemma EXISTS_THM: "Ex f = Ex f"
  sorry

lemma F_IMP: "[| ~ t; t |] ==> False"
  sorry

lemma NOT_AND: "~ (t & ~ t)"
  sorry

lemma AND_CLAUSES: "(True & t) = t &
(t & True) = t & (False & t) = False & (t & False) = False & (t & t) = t"
  sorry

lemma OR_CLAUSES: "(True | t) = True &
(t | True) = True & (False | t) = t & (t | False) = t & (t | t) = t"
  sorry

lemma IMP_CLAUSES: "(True --> t) = t &
(t --> True) = True &
(False --> t) = True & (t --> t) = True & (t --> False) = (~ t)"
  sorry

lemma NOT_CLAUSES: "(ALL t. (~ ~ t) = t) & (~ True) = False & (~ False) = True"
  sorry

lemma BOOL_EQ_DISTINCT: "True ~= False & False ~= True"
  sorry

lemma EQ_CLAUSES: "(True = t) = t & (t = True) = t & (False = t) = (~ t) & (t = False) = (~ t)"
  sorry

lemma COND_CLAUSES: "(if True then t1 else t2) = t1 & (if False then t1 else t2) = t2"
  sorry

lemma SELECT_UNIQUE: "(!!y. P y = (y = x)) ==> Eps P = x"
  sorry

lemma BOTH_EXISTS_AND_THM: "(EX x::'a. (P::bool) & (Q::bool)) = ((EX x::'a. P) & (EX x::'a. Q))"
  sorry

lemma BOTH_FORALL_OR_THM: "(ALL x::'a. (P::bool) | (Q::bool)) = ((ALL x::'a. P) | (ALL x::'a. Q))"
  sorry

lemma BOTH_FORALL_IMP_THM: "(ALL x::'a. (P::bool) --> (Q::bool)) = ((EX x::'a. P) --> (ALL x::'a. Q))"
  sorry

lemma BOTH_EXISTS_IMP_THM: "(EX x::'a. (P::bool) --> (Q::bool)) = ((ALL x::'a. P) --> (EX x::'a. Q))"
  sorry

lemma OR_IMP_THM: "(A = (B | A)) = (B --> A)"
  sorry

lemma DE_MORGAN_THM: "(~ (A & B)) = (~ A | ~ B) & (~ (A | B)) = (~ A & ~ B)"
  sorry

lemma IMP_F_EQ_F: "(t --> False) = (t = False)"
  sorry

lemma COND_RATOR: "(if b::bool then f::'a => 'b else (g::'a => 'b)) (x::'a) =
(if b then f x else g x)"
  sorry

lemma COND_ABS: "(%x. if b then f x else g x) = (if b then f else g)"
  sorry

lemma COND_EXPAND: "(if b then t1 else t2) = ((~ b | t1) & (b | t2))"
  sorry

lemma ONE_ONE_THM: "inj f = (ALL x1 x2. f x1 = f x2 --> x1 = x2)"
  sorry

lemma ABS_REP_THM: "(op ==>::prop => prop => prop)
 ((Trueprop::bool => prop)
   ((Ex::(('b::type => 'a::type) => bool) => bool)
     ((TYPE_DEFINITION::('a::type => bool)
                        => ('b::type => 'a::type) => bool)
       (P::'a::type => bool))))
 ((Trueprop::bool => prop)
   ((Ex::(('b::type => 'a::type) => bool) => bool)
     (%x::'b::type => 'a::type.
         (Ex::(('a::type => 'b::type) => bool) => bool)
          (%abs::'a::type => 'b::type.
              (op &::bool => bool => bool)
               ((All::('b::type => bool) => bool)
                 (%a::'b::type.
                     (op =::'b::type => 'b::type => bool) (abs (x a)) a))
               ((All::('a::type => bool) => bool)
                 (%r::'a::type.
                     (op =::bool => bool => bool) (P r)
                      ((op =::'a::type => 'a::type => bool) (x (abs r))
                        r)))))))"
  sorry

lemma LET_RAND: "(P::'b => bool) (Let (M::'a) (N::'a => 'b)) = (let x::'a = M in P (N x))"
  sorry

lemma LET_RATOR: "Let (M::'a) (N::'a => 'b => 'c) (b::'b) = (let x::'a = M in N x b)"
  sorry

lemma AND_CONG: "(Q --> P = P') & (P' --> Q = Q') ==> (P & Q) = (P' & Q')"
  sorry

lemma OR_CONG: "(~ Q --> P = P') & (~ P' --> Q = Q') ==> (P | Q) = (P' | Q')"
  sorry

lemma COND_CONG: "P = Q & (Q --> x = x') & (~ Q --> y = y')
==> (if P then x else y) = (if Q then x' else y')"
  sorry

lemma MONO_COND: "[| x ==> y; z ==> w; if b then x else z |] ==> if b then y else w"
  sorry

lemma SKOLEM_THM: "(ALL x. Ex (P x)) = (EX f. ALL x. P x (f x))"
  sorry

lemma bool_case_thm: "(ALL (e0::'a) e1::'a. (case True of True => e0 | False => e1) = e0) &
(ALL (e0::'a) e1::'a. (case False of True => e0 | False => e1) = e1)"
  sorry

lemma bool_case_ID: "(case b of True => x | _ => x) = x"
  sorry

lemma boolAxiom: "EX x. x True = e0 & x False = e1"
  sorry

lemma UEXISTS_OR_THM: "EX! x. P x | Q x ==> Ex1 P | Ex1 Q"
  sorry

lemma UEXISTS_SIMP: "(EX! x::'a. (t::bool)) = (t & (ALL x::'a. All (op = x)))"
  sorry

consts
  RES_ABSTRACT :: "('a => bool) => ('a => 'b) => 'a => 'b" 

specification (RES_ABSTRACT) RES_ABSTRACT_DEF: "(ALL (p::'a => bool) (m::'a => 'b) x::'a.
    IN x p --> RES_ABSTRACT p m x = m x) &
(ALL (p::'a => bool) (m1::'a => 'b) m2::'a => 'b.
    (ALL x::'a. IN x p --> m1 x = m2 x) -->
    RES_ABSTRACT p m1 = RES_ABSTRACT p m2)"
  sorry

lemma BOOL_FUN_CASES_THM: "f = (%b. True) | f = (%b. False) | f = (%b. b) | f = Not"
  sorry

lemma BOOL_FUN_INDUCT: "P (%b. True) & P (%b. False) & P (%b. b) & P Not ==> P x"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" combin

definition
  K :: "'a => 'b => 'a"  where
  "K == %x y. x"

lemma K_DEF: "K = (%x y. x)"
  sorry

definition
  S :: "('a => 'b => 'c) => ('a => 'b) => 'a => 'c"  where
  "S == %f g x. f x (g x)"

lemma S_DEF: "S = (%f g x. f x (g x))"
  sorry

definition
  I :: "'a => 'a"  where
  "(op ==::('a::type => 'a::type) => ('a::type => 'a::type) => prop)
 (I::'a::type => 'a::type)
 ((S::('a::type => ('a::type => 'a::type) => 'a::type)
      => ('a::type => 'a::type => 'a::type) => 'a::type => 'a::type)
   (K::'a::type => ('a::type => 'a::type) => 'a::type)
   (K::'a::type => 'a::type => 'a::type))"

lemma I_DEF: "(op =::('a::type => 'a::type) => ('a::type => 'a::type) => bool)
 (I::'a::type => 'a::type)
 ((S::('a::type => ('a::type => 'a::type) => 'a::type)
      => ('a::type => 'a::type => 'a::type) => 'a::type => 'a::type)
   (K::'a::type => ('a::type => 'a::type) => 'a::type)
   (K::'a::type => 'a::type => 'a::type))"
  sorry

definition
  C :: "('a => 'b => 'c) => 'b => 'a => 'c"  where
  "C == %f x y. f y x"

lemma C_DEF: "C = (%f x y. f y x)"
  sorry

definition
  W :: "('a => 'a => 'b) => 'a => 'b"  where
  "W == %f x. f x x"

lemma W_DEF: "W = (%f x. f x x)"
  sorry

lemma I_THM: "I x = x"
  sorry

lemma I_o_ID: "I o f = f & f o I = f"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" sum

lemma ISL_OR_ISR: "ISL x | ISR x"
  sorry

lemma INL: "ISL x ==> Inl (OUTL x) = x"
  sorry

lemma INR: "ISR x ==> Inr (OUTR x) = x"
  sorry

lemma sum_case_cong: "(M::'b + 'c) = (M'::'b + 'c) &
(ALL x::'b. M' = Inl x --> (f::'b => 'a) x = (f'::'b => 'a) x) &
(ALL y::'c. M' = Inr y --> (g::'c => 'a) y = (g'::'c => 'a) y)
==> sum_case f g M = sum_case f' g' M'"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" one

;end_setup

setup_theory "~~/src/HOL/Import/HOL" option

lemma option_CLAUSES: "(op &::bool => bool => bool)
 ((All::('a::type => bool) => bool)
   (%x::'a::type.
       (All::('a::type => bool) => bool)
        (%y::'a::type.
            (op =::bool => bool => bool)
             ((op =::'a::type option => 'a::type option => bool)
               ((Some::'a::type => 'a::type option) x)
               ((Some::'a::type => 'a::type option) y))
             ((op =::'a::type => 'a::type => bool) x y))))
 ((op &::bool => bool => bool)
   ((All::('a::type => bool) => bool)
     (%x::'a::type.
         (op =::'a::type => 'a::type => bool)
          ((the::'a::type option => 'a::type)
            ((Some::'a::type => 'a::type option) x))
          x))
   ((op &::bool => bool => bool)
     ((All::('a::type => bool) => bool)
       (%x::'a::type.
           (op ~=::'a::type option => 'a::type option => bool)
            (None::'a::type option)
            ((Some::'a::type => 'a::type option) x)))
     ((op &::bool => bool => bool)
       ((All::('a::type => bool) => bool)
         (%x::'a::type.
             (op ~=::'a::type option => 'a::type option => bool)
              ((Some::'a::type => 'a::type option) x)
              (None::'a::type option)))
       ((op &::bool => bool => bool)
         ((All::('a::type => bool) => bool)
           (%x::'a::type.
               (op =::bool => bool => bool)
                ((IS_SOME::'a::type option => bool)
                  ((Some::'a::type => 'a::type option) x))
                (True::bool)))
         ((op &::bool => bool => bool)
           ((op =::bool => bool => bool)
             ((IS_SOME::'a::type option => bool) (None::'a::type option))
             (False::bool))
           ((op &::bool => bool => bool)
             ((All::('a::type option => bool) => bool)
               (%x::'a::type option.
                   (op =::bool => bool => bool)
                    ((IS_NONE::'a::type option => bool) x)
                    ((op =::'a::type option => 'a::type option => bool) x
                      (None::'a::type option))))
             ((op &::bool => bool => bool)
               ((All::('a::type option => bool) => bool)
                 (%x::'a::type option.
                     (op =::bool => bool => bool)
                      ((Not::bool => bool)
                        ((IS_SOME::'a::type option => bool) x))
                      ((op =::'a::type option => 'a::type option => bool) x
                        (None::'a::type option))))
               ((op &::bool => bool => bool)
                 ((All::('a::type option => bool) => bool)
                   (%x::'a::type option.
                       (op -->::bool => bool => bool)
                        ((IS_SOME::'a::type option => bool) x)
                        ((op =::'a::type option => 'a::type option => bool)
                          ((Some::'a::type => 'a::type option)
                            ((the::'a::type option => 'a::type) x))
                          x)))
                 ((op &::bool => bool => bool)
                   ((All::('a::type option => bool) => bool)
                     (%x::'a::type option.
                         (op =::'a::type option => 'a::type option => bool)
                          ((option_case::'a::type option
   => ('a::type => 'a::type option) => 'a::type option => 'a::type option)
                            (None::'a::type option)
                            (Some::'a::type => 'a::type option) x)
                          x))
                   ((op &::bool => bool => bool)
                     ((All::('a::type option => bool) => bool)
                       (%x::'a::type option.
                           (op =::'a::type option
                                  => 'a::type option => bool)
                            ((option_case::'a::type option
     => ('a::type => 'a::type option) => 'a::type option => 'a::type option)
                              x (Some::'a::type => 'a::type option) x)
                            x))
                     ((op &::bool => bool => bool)
                       ((All::('a::type option => bool) => bool)
                         (%x::'a::type option.
                             (op -->::bool => bool => bool)
                              ((IS_NONE::'a::type option => bool) x)
                              ((op =::'b::type => 'b::type => bool)
                                ((option_case::'b::type
         => ('a::type => 'b::type) => 'a::type option => 'b::type)
                                  (e::'b::type) (f::'a::type => 'b::type) x)
                                e)))
                       ((op &::bool => bool => bool)
                         ((All::('a::type option => bool) => bool)
                           (%x::'a::type option.
                               (op -->::bool => bool => bool)
                                ((IS_SOME::'a::type option => bool) x)
                                ((op =::'b::type => 'b::type => bool)
                                  ((option_case::'b::type
           => ('a::type => 'b::type) => 'a::type option => 'b::type)
                                    e f x)
                                  (f ((the::'a::type option => 'a::type)
 x)))))
                         ((op &::bool => bool => bool)
                           ((All::('a::type option => bool) => bool)
                             (%x::'a::type option.
                                 (op -->::bool => bool => bool)
                                  ((IS_SOME::'a::type option => bool) x)
                                  ((op =::'a::type option
    => 'a::type option => bool)
                                    ((option_case::'a::type option
             => ('a::type => 'a::type option)
                => 'a::type option => 'a::type option)
(ea::'a::type option) (Some::'a::type => 'a::type option) x)
                                    x)))
                           ((op &::bool => bool => bool)
                             ((All::('b::type => bool) => bool)
                               (%u::'b::type.
                                   (All::(('a::type => 'b::type) => bool)
   => bool)
                                    (%f::'a::type => 'b::type.
  (op =::'b::type => 'b::type => bool)
   ((option_case::'b::type
                  => ('a::type => 'b::type) => 'a::type option => 'b::type)
     u f (None::'a::type option))
   u)))
                             ((op &::bool => bool => bool)
                               ((All::('b::type => bool) => bool)
                                 (%u::'b::type.
                                     (All::(('a::type => 'b::type) => bool)
     => bool)
(%f::'a::type => 'b::type.
    (All::('a::type => bool) => bool)
     (%x::'a::type.
         (op =::'b::type => 'b::type => bool)
          ((option_case::'b::type
                         => ('a::type => 'b::type)
                            => 'a::type option => 'b::type)
            u f ((Some::'a::type => 'a::type option) x))
          (f x)))))
                               ((op &::bool => bool => bool)
                                 ((All::(('a::type => 'b::type) => bool)
  => bool)
                                   (%f::'a::type => 'b::type.
 (All::('a::type => bool) => bool)
  (%x::'a::type.
      (op =::'b::type option => 'b::type option => bool)
       ((Option.map::('a::type => 'b::type)
                     => 'a::type option => 'b::type option)
         f ((Some::'a::type => 'a::type option) x))
       ((Some::'b::type => 'b::type option) (f x)))))
                                 ((op &::bool => bool => bool)
                                   ((All::(('a::type => 'b::type) => bool)
    => bool)
                                     (%f::'a::type => 'b::type.
   (op =::'b::type option => 'b::type option => bool)
    ((Option.map::('a::type => 'b::type)
                  => 'a::type option => 'b::type option)
      f (None::'a::type option))
    (None::'b::type option)))
                                   ((op &::bool => bool => bool)
                                     ((op =::'a::type option
       => 'a::type option => bool)
 ((OPTION_JOIN::'a::type option option => 'a::type option)
   (None::'a::type option option))
 (None::'a::type option))
                                     ((All::('a::type option => bool)
      => bool)
 (%x::'a::type option.
     (op =::'a::type option => 'a::type option => bool)
      ((OPTION_JOIN::'a::type option option => 'a::type option)
        ((Some::'a::type option => 'a::type option option) x))
      x))))))))))))))))))))"
  sorry

lemma option_case_compute: "option_case (e::'b) (f::'a => 'b) (x::'a option) =
(if IS_SOME x then f (the x) else e)"
  sorry

lemma OPTION_MAP_EQ_SOME: "(Option.map (f::'a => 'b) (x::'a option) = Some (y::'b)) =
(EX z::'a. x = Some z & y = f z)"
  sorry

lemma OPTION_JOIN_EQ_SOME: "(OPTION_JOIN x = Some xa) = (x = Some (Some xa))"
  sorry

lemma option_case_cong: "M = M' & (M' = None --> u = u') & (ALL x. M' = Some x --> f x = f' x)
==> option_case u f M = option_case u' f' M'"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" marker

consts
  stmarker :: "'a => 'a" 

defs
  stmarker_primdef: "stmarker == %x. x"

lemma stmarker_def: "stmarker x = x"
  sorry

lemma move_left_conj: "(x & stmarker xb) = (stmarker xb & x) &
((stmarker xb & x) & xa) = (stmarker xb & x & xa) &
(x & stmarker xb & xa) = (stmarker xb & x & xa)"
  sorry

lemma move_right_conj: "(stmarker xb & x) = (x & stmarker xb) &
(x & xa & stmarker xb) = ((x & xa) & stmarker xb) &
((x & stmarker xb) & xa) = ((x & xa) & stmarker xb)"
  sorry

lemma move_left_disj: "(x | stmarker xb) = (stmarker xb | x) &
((stmarker xb | x) | xa) = (stmarker xb | x | xa) &
(x | stmarker xb | xa) = (stmarker xb | x | xa)"
  sorry

lemma move_right_disj: "(stmarker xb | x) = (x | stmarker xb) &
(x | xa | stmarker xb) = ((x | xa) | stmarker xb) &
((x | stmarker xb) | xa) = ((x | xa) | stmarker xb)"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" relation

definition
  TC :: "('a => 'a => bool) => 'a => 'a => bool"  where
  "TC ==
%R a b.
   ALL P.
      (ALL x y. R x y --> P x y) & (ALL x y z. P x y & P y z --> P x z) -->
      P a b"

lemma TC_DEF: "TC R a b =
(ALL P.
    (ALL x y. R x y --> P x y) & (ALL x y z. P x y & P y z --> P x z) -->
    P a b)"
  sorry

definition
  RTC :: "('a => 'a => bool) => 'a => 'a => bool"  where
  "RTC ==
%R a b.
   ALL P. (ALL x. P x x) & (ALL x y z. R x y & P y z --> P x z) --> P a b"

lemma RTC_DEF: "RTC R a b =
(ALL P. (ALL x. P x x) & (ALL x y z. R x y & P y z --> P x z) --> P a b)"
  sorry

consts
  RC :: "('a => 'a => bool) => 'a => 'a => bool" 

defs
  RC_primdef: "RC == %R x y. x = y | R x y"

lemma RC_def: "RC R x y = (x = y | R x y)"
  sorry

consts
  transitive :: "('a => 'a => bool) => bool" 

defs
  transitive_primdef: "transitive == %R. ALL x y z. R x y & R y z --> R x z"

lemma transitive_def: "transitive R = (ALL x y z. R x y & R y z --> R x z)"
  sorry

definition
  pred_reflexive :: "('a => 'a => bool) => bool"  where
  "pred_reflexive == %R. ALL x. R x x"

lemma reflexive_def: "pred_reflexive R = (ALL x. R x x)"
  sorry

lemma TC_TRANSITIVE: "transitive (TC x)"
  sorry

lemma RTC_INDUCT: "[| (ALL x. xa x x) & (ALL xb y z. x xb y & xa y z --> xa xb z);
   RTC x xb xc |]
==> xa xb xc"
  sorry

lemma TC_RULES: "(ALL xa xb. x xa xb --> TC x xa xb) &
(ALL xa xb xc. TC x xa xb & TC x xb xc --> TC x xa xc)"
  sorry

lemma RTC_RULES: "(ALL xa. RTC x xa xa) &
(ALL xa xb xc. x xa xb & RTC x xb xc --> RTC x xa xc)"
  sorry

lemma RTC_STRONG_INDUCT: "[| (ALL x. P x x) & (ALL x y z. R x y & RTC R y z & P y z --> P x z);
   RTC R x y |]
==> P x y"
  sorry

lemma RTC_RTC: "[| RTC R x y; RTC R y z |] ==> RTC R x z"
  sorry

lemma RTC_TRANSITIVE: "transitive (RTC x)"
  sorry

lemma RTC_REFLEXIVE: "pred_reflexive (RTC R)"
  sorry

lemma RC_REFLEXIVE: "pred_reflexive (RC R)"
  sorry

lemma TC_SUBSET: "x xa xb ==> TC x xa xb"
  sorry

lemma RTC_SUBSET: "R x y ==> RTC R x y"
  sorry

lemma RC_SUBSET: "R x y ==> RC R x y"
  sorry

lemma RC_RTC: "RC R x y ==> RTC R x y"
  sorry

lemma TC_INDUCT: "[| (ALL xb y. x xb y --> xa xb y) & (ALL x y z. xa x y & xa y z --> xa x z);
   TC x xb xc |]
==> xa xb xc"
  sorry

lemma TC_INDUCT_LEFT1: "[| (ALL xb y. x xb y --> xa xb y) &
   (ALL xb y z. x xb y & xa y z --> xa xb z);
   TC x xb xc |]
==> xa xb xc"
  sorry

lemma TC_STRONG_INDUCT: "[| (ALL x y. R x y --> P x y) &
   (ALL x y z. P x y & P y z & TC R x y & TC R y z --> P x z);
   TC R u v |]
==> P u v"
  sorry

lemma TC_STRONG_INDUCT_LEFT1: "[| (ALL x y. R x y --> P x y) &
   (ALL x y z. R x y & P y z & TC R y z --> P x z);
   TC R u v |]
==> P u v"
  sorry

lemma TC_RTC: "TC R x y ==> RTC R x y"
  sorry

lemma RTC_TC_RC: "RTC R x y ==> RC R x y | TC R x y"
  sorry

lemma TC_RC_EQNS: "RC (TC R) = RTC R & TC (RC R) = RTC R"
  sorry

lemma RC_IDEM: "RC (RC R) = RC R"
  sorry

lemma TC_IDEM: "TC (TC R) = TC R"
  sorry

lemma RTC_IDEM: "RTC (RTC R) = RTC R"
  sorry

lemma RTC_CASES1: "RTC x xa xb = (xa = xb | (EX u. x xa u & RTC x u xb))"
  sorry

lemma RTC_CASES2: "RTC x xa xb = (xa = xb | (EX u. RTC x xa u & x u xb))"
  sorry

lemma RTC_CASES_RTC_TWICE: "RTC x xa xb = (EX u. RTC x xa u & RTC x u xb)"
  sorry

lemma TC_CASES1: "TC R x z ==> R x z | (EX y. R x y & TC R y z)"
  sorry

lemma TC_CASES2: "TC R x z ==> R x z | (EX y. TC R x y & R y z)"
  sorry

lemma TC_MONOTONE: "[| !!x y. R x y ==> Q x y; TC R x y |] ==> TC Q x y"
  sorry

lemma RTC_MONOTONE: "[| !!x y. R x y ==> Q x y; RTC R x y |] ==> RTC Q x y"
  sorry

definition
  WF :: "('a => 'a => bool) => bool"  where
  "WF == %R. ALL B. Ex B --> (EX min. B min & (ALL b. R b min --> ~ B b))"

lemma WF_DEF: "WF R = (ALL B. Ex B --> (EX min. B min & (ALL b. R b min --> ~ B b)))"
  sorry

lemma WF_INDUCTION_THM: "[| WF R; !!x. (!!y. R y x ==> P y) ==> P x |] ==> P x"
  sorry

lemma WF_NOT_REFL: "[| WF x; x xa xb |] ==> xa ~= xb"
  sorry

definition
  EMPTY_REL :: "'a => 'a => bool"  where
  "EMPTY_REL == %x y. False"

lemma EMPTY_REL_DEF: "EMPTY_REL x y = False"
  sorry

lemma WF_EMPTY_REL: "WF EMPTY_REL"
  sorry

lemma WF_SUBSET: "WF x & (ALL xb y. xa xb y --> x xb y) ==> WF xa"
  sorry

lemma WF_TC: "WF R ==> WF (TC R)"
  sorry

consts
  inv_image :: "('b => 'b => bool) => ('a => 'b) => 'a => 'a => bool" 

defs
  inv_image_primdef: "relation.inv_image ==
%(R::'b => 'b => bool) (f::'a => 'b) (x::'a) y::'a. R (f x) (f y)"

lemma inv_image_def: "relation.inv_image R f = (%x y. R (f x) (f y))"
  sorry

lemma WF_inv_image: "WF (R::'b => 'b => bool) ==> WF (relation.inv_image R (f::'a => 'b))"
  sorry

definition
  RESTRICT :: "('a => 'b) => ('a => 'a => bool) => 'a => 'a => 'b"  where
  "RESTRICT == %f R x y. if R y x then f y else ARB"

lemma RESTRICT_DEF: "RESTRICT f R x = (%y. if R y x then f y else ARB)"
  sorry

lemma RESTRICT_LEMMA: "xa xb xc ==> RESTRICT x xa xc xb = x xb"
  sorry

consts
  approx :: "('a => 'a => bool) => (('a => 'b) => 'a => 'b) => 'a => ('a => 'b) => bool" 

defs
  approx_primdef: "approx == %R M x f. f = RESTRICT (%y. M (RESTRICT f R y) y) R x"

lemma approx_def: "approx R M x f = (f = RESTRICT (%y. M (RESTRICT f R y) y) R x)"
  sorry

consts
  the_fun :: "('a => 'a => bool) => (('a => 'b) => 'a => 'b) => 'a => 'a => 'b" 

defs
  the_fun_primdef: "the_fun == %R M x. Eps (approx R M x)"

lemma the_fun_def: "the_fun R M x = Eps (approx R M x)"
  sorry

definition
  WFREC :: "('a => 'a => bool) => (('a => 'b) => 'a => 'b) => 'a => 'b"  where
  "WFREC ==
%R M x. M (RESTRICT (the_fun (TC R) (%f v. M (RESTRICT f R v) v) x) R x) x"

lemma WFREC_DEF: "WFREC R M =
(%x. M (RESTRICT (the_fun (TC R) (%f v. M (RESTRICT f R v) v) x) R x) x)"
  sorry

lemma WFREC_THM: "WF R ==> WFREC R M x = M (RESTRICT (WFREC R M) R x) x"
  sorry

lemma WFREC_COROLLARY: "[| f = WFREC R M; WF R |] ==> f x = M (RESTRICT f R x) x"
  sorry

lemma WF_RECURSION_THM: "WF R ==> EX! f. ALL x. f x = M (RESTRICT f R x) x"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" pair

lemma CURRY_ONE_ONE_THM: "(curry f = curry g) = (f = g)"
  sorry

lemma UNCURRY_ONE_ONE_THM: "((%(x, y). f x y) = (%(x, y). g x y)) = (f = g)"
  sorry

lemma pair_Axiom: "EX x. ALL xa y. x (xa, y) = f xa y"
  sorry

lemma UNCURRY_CONG: "M = M' & (ALL x y. M' = (x, y) --> f x y = f' x y)
==> prod_case f M = prod_case f' M'"
  sorry

lemma ELIM_PEXISTS: "(EX p. P (fst p) (snd p)) = (EX p1. Ex (P p1))"
  sorry

lemma ELIM_PFORALL: "(ALL p. P (fst p) (snd p)) = (ALL p1. All (P p1))"
  sorry

lemma PFORALL_THM: "(ALL xa. All (x xa)) = All (%(xa, y). x xa y)"
  sorry

lemma PEXISTS_THM: "(EX xa. Ex (x xa)) = Ex (%(xa, y). x xa y)"
  sorry

lemma LET2_RAND: "(x::'c => 'd)
 (let (x::'a, y::'b) = xa::'a * 'b in (xb::'a => 'b => 'c) x y) =
(let (xa::'a, y::'b) = xa in x (xb xa y))"
  sorry

lemma LET2_RATOR: "(let (x::'a1, y::'a2) = x::'a1 * 'a2 in (xa::'a1 => 'a2 => 'b => 'c) x y)
 (xb::'b) =
(let (x::'a1, y::'a2) = x in xa x y xb)"
  sorry

lemma pair_case_cong: "x = xa & (ALL x y. xa = (x, y) --> xb x y = f' x y)
==> prod_case xb x = prod_case f' xa"
  sorry

definition
  LEX :: "('a => 'a => bool) => ('b => 'b => bool) => 'a * 'b => 'a * 'b => bool"  where
  "LEX == %R1 R2 (s, t) (u, v). R1 s u | s = u & R2 t v"

lemma LEX_DEF: "LEX R1 R2 = (%(s, t) (u, v). R1 s u | s = u & R2 t v)"
  sorry

lemma WF_LEX: "WF x & WF xa ==> WF (LEX x xa)"
  sorry

definition
  RPROD :: "('a => 'a => bool) => ('b => 'b => bool) => 'a * 'b => 'a * 'b => bool"  where
  "RPROD == %R1 R2 (s, t) (u, v). R1 s u & R2 t v"

lemma RPROD_DEF: "RPROD R1 R2 = (%(s, t) (u, v). R1 s u & R2 t v)"
  sorry

lemma WF_RPROD: "WF R & WF Q ==> WF (RPROD R Q)"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" num

;end_setup

setup_theory "~~/src/HOL/Import/HOL" prim_rec

lemma LESS_0_0: "0 < Suc 0"
  sorry

lemma LESS_LEMMA1: "x < Suc xa ==> x = xa | x < xa"
  sorry

lemma LESS_LEMMA2: "m = n | m < n ==> m < Suc n"
  sorry

lemma LESS_THM: "(m < Suc n) = (m = n | m < n)"
  sorry

lemma LESS_SUC_IMP: "[| x < Suc xa; x ~= xa |] ==> x < xa"
  sorry

lemma EQ_LESS: "Suc m = n ==> m < n"
  sorry

lemma NOT_LESS_EQ: "(m::nat) = (n::nat) ==> ~ m < n"
  sorry

definition
  SIMP_REC_REL :: "(nat => 'a) => 'a => ('a => 'a) => nat => bool"  where
  "SIMP_REC_REL == %fun x f n. fun 0 = x & (ALL m<n. fun (Suc m) = f (fun m))"

lemma SIMP_REC_REL: "SIMP_REC_REL fun x f n = (fun 0 = x & (ALL m<n. fun (Suc m) = f (fun m)))"
  sorry

lemma SIMP_REC_EXISTS: "EX fun. SIMP_REC_REL fun x f n"
  sorry

lemma SIMP_REC_REL_UNIQUE: "[| SIMP_REC_REL xb x xa xd & SIMP_REC_REL xc x xa xe; n < xd & n < xe |]
==> xb n = xc n"
  sorry

lemma SIMP_REC_REL_UNIQUE_RESULT: "EX! y. EX g. SIMP_REC_REL g x f (Suc n) & y = g n"
  sorry

consts
  SIMP_REC :: "'a => ('a => 'a) => nat => 'a" 

specification (SIMP_REC) SIMP_REC: "ALL x f' n. EX g. SIMP_REC_REL g x f' (Suc n) & SIMP_REC x f' n = g n"
  sorry

lemma LESS_SUC_SUC: "m < Suc m & m < Suc (Suc m)"
  sorry

lemma SIMP_REC_THM: "SIMP_REC x f 0 = x & (ALL m. SIMP_REC x f (Suc m) = f (SIMP_REC x f m))"
  sorry

definition
  PRE :: "nat => nat"  where
  "PRE == %m. if m = 0 then 0 else SOME n. m = Suc n"

lemma PRE_DEF: "PRE m = (if m = 0 then 0 else SOME n. m = Suc n)"
  sorry

lemma PRE: "PRE 0 = 0 & (ALL m. PRE (Suc m) = m)"
  sorry

definition
  PRIM_REC_FUN :: "'a => ('a => nat => 'a) => nat => nat => 'a"  where
  "PRIM_REC_FUN == %x f. SIMP_REC (%n. x) (%fun n. f (fun (PRE n)) n)"

lemma PRIM_REC_FUN: "PRIM_REC_FUN x f = SIMP_REC (%n. x) (%fun n. f (fun (PRE n)) n)"
  sorry

lemma PRIM_REC_EQN: "(ALL n. PRIM_REC_FUN x f 0 n = x) &
(ALL m n. PRIM_REC_FUN x f (Suc m) n = f (PRIM_REC_FUN x f m (PRE n)) n)"
  sorry

definition
  PRIM_REC :: "'a => ('a => nat => 'a) => nat => 'a"  where
  "PRIM_REC == %x f m. PRIM_REC_FUN x f m (PRE m)"

lemma PRIM_REC: "PRIM_REC x f m = PRIM_REC_FUN x f m (PRE m)"
  sorry

lemma PRIM_REC_THM: "PRIM_REC x f 0 = x & (ALL m. PRIM_REC x f (Suc m) = f (PRIM_REC x f m) m)"
  sorry

lemma DC: "P a & (ALL x. P x --> (EX y. P y & R x y))
==> EX x. x 0 = a & (ALL n. P (x n) & R (x n) (x (Suc n)))"
  sorry

lemma num_Axiom_old: "EX! fn1. fn1 0 = e & (ALL n. fn1 (Suc n) = f (fn1 n) n)"
  sorry

lemma num_Axiom: "EX x. x 0 = e & (ALL n. x (Suc n) = f n (x n))"
  sorry

consts
  wellfounded :: "('a => 'a => bool) => bool" 

defs
  wellfounded_primdef: "wellfounded == %R. ~ (EX f. ALL n. R (f (Suc n)) (f n))"

lemma wellfounded_def: "wellfounded R = (~ (EX f. ALL n. R (f (Suc n)) (f n)))"
  sorry

lemma WF_IFF_WELLFOUNDED: "WF R = wellfounded R"
  sorry

lemma WF_PRED: "WF (%x y. y = Suc x)"
  sorry

lemma WF_LESS: "(WF::(nat => nat => bool) => bool) (op <::nat => nat => bool)"
  sorry

consts
  measure :: "('a => nat) => 'a => 'a => bool" 

defs
  measure_primdef: "prim_rec.measure == relation.inv_image op <"

lemma measure_def: "prim_rec.measure = relation.inv_image op <"
  sorry

lemma WF_measure: "WF (prim_rec.measure x)"
  sorry

lemma measure_thm: "prim_rec.measure x xa xb = (x xa < x xb)"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" arithmetic

definition
  nat_elim__magic :: "nat => nat"  where
  "nat_elim__magic == %n. n"

lemma nat_elim__magic: "nat_elim__magic n = n"
  sorry

consts
  EVEN :: "nat => bool" 

specification (EVEN) EVEN: "EVEN 0 = True & (ALL n. EVEN (Suc n) = (~ EVEN n))"
  sorry

consts
  ODD :: "nat => bool" 

specification (ODD) ODD: "ODD 0 = False & (ALL n. ODD (Suc n) = (~ ODD n))"
  sorry

lemma TWO: "2 = Suc 1"
  sorry

lemma NORM_0: "(0::nat) = (0::nat)"
  sorry

lemma num_case_compute: "nat_case f g n = (if n = 0 then f else g (PRE n))"
  sorry

lemma ADD_CLAUSES: "0 + m = m & m + 0 = m & Suc m + n = Suc (m + n) & m + Suc n = Suc (m + n)"
  sorry

lemma LESS_ADD: "(n::nat) < (m::nat) ==> EX p::nat. p + n = m"
  sorry

lemma LESS_ANTISYM: "~ ((m::nat) < (n::nat) & n < m)"
  sorry

lemma LESS_LESS_SUC: "~ (x < xa & xa < Suc x)"
  sorry

lemma FUN_EQ_LEMMA: "f x1 & ~ f x2 ==> x1 ~= x2"
  sorry

lemma LESS_NOT_SUC: "m < n & n ~= Suc m ==> Suc m < n"
  sorry

lemma LESS_0_CASES: "(0::nat) = (m::nat) | (0::nat) < m"
  sorry

lemma LESS_CASES_IMP: "~ (m::nat) < (n::nat) & m ~= n ==> n < m"
  sorry

lemma LESS_CASES: "(m::nat) < (n::nat) | n <= m"
  sorry

lemma LESS_EQ_SUC_REFL: "m <= Suc m"
  sorry

lemma LESS_ADD_NONZERO: "(n::nat) ~= (0::nat) ==> (m::nat) < m + n"
  sorry

lemma LESS_EQ_ANTISYM: "~ ((x::nat) < (xa::nat) & xa <= x)"
  sorry

lemma SUB_0: "(0::nat) - (m::nat) = (0::nat) & m - (0::nat) = m"
  sorry

lemma PRE_SUB1: "PRE m = m - 1"
  sorry

lemma MULT_CLAUSES: "0 * x = 0 &
x * 0 = 0 &
1 * x = x & x * 1 = x & Suc x * xa = x * xa + xa & x * Suc xa = x + x * xa"
  sorry

lemma PRE_SUB: "PRE (m - n) = PRE m - n"
  sorry

lemma ADD_EQ_1: "((m::nat) + (n::nat) = (1::nat)) =
(m = (1::nat) & n = (0::nat) | m = (0::nat) & n = (1::nat))"
  sorry

lemma ADD_INV_0_EQ: "((m::nat) + (n::nat) = m) = (n = (0::nat))"
  sorry

lemma PRE_SUC_EQ: "0 < n ==> (m = PRE n) = (Suc m = n)"
  sorry

lemma INV_PRE_EQ: "0 < m & 0 < n ==> (PRE m = PRE n) = (m = n)"
  sorry

lemma LESS_SUC_NOT: "m < n ==> ~ n < Suc m"
  sorry

lemma ADD_EQ_SUB: "(n::nat) <= (p::nat) ==> ((m::nat) + n = p) = (m = p - n)"
  sorry

lemma LESS_ADD_1: "(xa::nat) < (x::nat) ==> EX xb::nat. x = xa + (xb + (1::nat))"
  sorry

lemma NOT_ODD_EQ_EVEN: "Suc (n + n) ~= m + m"
  sorry

lemma MULT_SUC_EQ: "(n * Suc p = m * Suc p) = (n = m)"
  sorry

lemma MULT_EXP_MONO: "(n * Suc q ^ p = m * Suc q ^ p) = (n = m)"
  sorry

lemma LESS_ADD_SUC: "m < m + Suc n"
  sorry

lemma LESS_OR_EQ_ADD: "(n::nat) < (m::nat) | (EX p::nat. n = p + m)"
  sorry

lemma WOP: "Ex (P::nat => bool) ==> EX n::nat. P n & (ALL m<n. ~ P m)"
  sorry

lemma INV_PRE_LESS: "0 < m ==> (PRE m < PRE n) = (m < n)"
  sorry

lemma INV_PRE_LESS_EQ: "0 < n ==> (PRE m <= PRE n) = (m <= n)"
  sorry

lemma SUB_EQ_EQ_0: "((m::nat) - (n::nat) = m) = (m = (0::nat) | n = (0::nat))"
  sorry

lemma SUB_LESS_OR: "(n::nat) < (m::nat) ==> n <= m - (1::nat)"
  sorry

lemma LESS_SUB_ADD_LESS: "(i::nat) < (n::nat) - (m::nat) ==> i + m < n"
  sorry

lemma LESS_EQ_SUB_LESS: "(xa::nat) <= (x::nat) ==> (x - xa < (c::nat)) = (x < xa + c)"
  sorry

lemma NOT_SUC_LESS_EQ: "(~ Suc x <= xa) = (xa <= x)"
  sorry

lemma SUB_LESS_EQ_ADD: "(m::nat) <= (p::nat) ==> (p - m <= (n::nat)) = (p <= m + n)"
  sorry

lemma SUB_CANCEL: "(xa::nat) <= (x::nat) & (xb::nat) <= x ==> (x - xa = x - xb) = (xa = xb)"
  sorry

lemma NOT_EXP_0: "Suc n ^ m ~= 0"
  sorry

lemma ZERO_LESS_EXP: "0 < Suc n ^ m"
  sorry

lemma ODD_OR_EVEN: "EX xa. x = Suc (Suc 0) * xa | x = Suc (Suc 0) * xa + 1"
  sorry

lemma LESS_EXP_SUC_MONO: "Suc (Suc m) ^ n < Suc (Suc m) ^ Suc n"
  sorry

lemma LESS_LESS_CASES: "(m::nat) = (n::nat) | m < n | n < m"
  sorry

consts
  FACT :: "nat => nat" 

specification (FACT) FACT: "FACT 0 = 1 & (ALL n. FACT (Suc n) = Suc n * FACT n)"
  sorry

lemma FACT_LESS: "0 < FACT n"
  sorry

lemma EVEN_ODD: "EVEN n = (~ ODD n)"
  sorry

lemma ODD_EVEN: "ODD x = (~ EVEN x)"
  sorry

lemma EVEN_OR_ODD: "EVEN x | ODD x"
  sorry

lemma EVEN_AND_ODD: "~ (EVEN x & ODD x)"
  sorry

lemma EVEN_ADD: "EVEN (m + n) = (EVEN m = EVEN n)"
  sorry

lemma EVEN_MULT: "EVEN (m * n) = (EVEN m | EVEN n)"
  sorry

lemma ODD_ADD: "ODD (m + n) = (ODD m ~= ODD n)"
  sorry

lemma ODD_MULT: "ODD (m * n) = (ODD m & ODD n)"
  sorry

lemma EVEN_DOUBLE: "EVEN (2 * n)"
  sorry

lemma ODD_DOUBLE: "ODD (Suc (2 * x))"
  sorry

lemma EVEN_ODD_EXISTS: "(EVEN x --> (EX m. x = 2 * m)) & (ODD x --> (EX m. x = Suc (2 * m)))"
  sorry

lemma EVEN_EXISTS: "EVEN n = (EX m. n = 2 * m)"
  sorry

lemma ODD_EXISTS: "ODD n = (EX m. n = Suc (2 * m))"
  sorry

lemma NOT_SUC_LESS_EQ_0: "~ Suc x <= 0"
  sorry

lemma NOT_NUM_EQ: "(x ~= xa) = (Suc x <= xa | Suc xa <= x)"
  sorry

lemma SUC_ADD_SYM: "Suc (m + n) = Suc n + m"
  sorry

lemma NOT_SUC_ADD_LESS_EQ: "~ Suc (m + n) <= m"
  sorry

lemma SUB_LEFT_ADD: "(m::nat) + ((n::nat) - (p::nat)) = (if n <= p then m else m + n - p)"
  sorry

lemma SUB_RIGHT_ADD: "(m::nat) - (n::nat) + (p::nat) = (if m <= n then p else m + p - n)"
  sorry

lemma SUB_LEFT_SUB: "(m::nat) - ((n::nat) - (p::nat)) = (if n <= p then m else m + p - n)"
  sorry

lemma SUB_LEFT_SUC: "Suc (m - n) = (if m <= n then Suc 0 else Suc m - n)"
  sorry

lemma SUB_LEFT_LESS_EQ: "((m::nat) <= (n::nat) - (p::nat)) = (m + p <= n | m <= (0::nat))"
  sorry

lemma SUB_RIGHT_LESS_EQ: "((m::nat) - (n::nat) <= (p::nat)) = (m <= n + p)"
  sorry

lemma SUB_RIGHT_LESS: "((m::nat) - (n::nat) < (p::nat)) = (m < n + p & (0::nat) < p)"
  sorry

lemma SUB_RIGHT_GREATER_EQ: "((p::nat) <= (m::nat) - (n::nat)) = (n + p <= m | p <= (0::nat))"
  sorry

lemma SUB_LEFT_GREATER: "((n::nat) - (p::nat) < (m::nat)) = (n < m + p & (0::nat) < m)"
  sorry

lemma SUB_RIGHT_GREATER: "((p::nat) < (m::nat) - (n::nat)) = (n + p < m)"
  sorry

lemma SUB_LEFT_EQ: "((m::nat) = (n::nat) - (p::nat)) = (m + p = n | m <= (0::nat) & n <= p)"
  sorry

lemma SUB_RIGHT_EQ: "((m::nat) - (n::nat) = (p::nat)) = (m = n + p | m <= n & p <= (0::nat))"
  sorry

lemma LE: "(ALL n::nat. (n <= (0::nat)) = (n = (0::nat))) &
(ALL (m::nat) n::nat. (m <= Suc n) = (m = Suc n | m <= n))"
  sorry

lemma DA: "(0::nat) < (n::nat) ==> EX (x::nat) q::nat. (k::nat) = q * n + x & x < n"
  sorry

lemma DIV_LESS_EQ: "(0::nat) < (n::nat) ==> (k::nat) div n <= k"
  sorry

lemma DIV_UNIQUE: "EX r::nat. (k::nat) = (q::nat) * (n::nat) + r & r < n ==> k div n = q"
  sorry

lemma MOD_UNIQUE: "EX q::nat. (k::nat) = q * (n::nat) + (r::nat) & r < n ==> k mod n = r"
  sorry

lemma DIV_MULT: "(r::nat) < (n::nat) ==> ((q::nat) * n + r) div n = q"
  sorry

lemma MOD_EQ_0: "(0::nat) < (n::nat) ==> (k::nat) * n mod n = (0::nat)"
  sorry

lemma ZERO_MOD: "(0::nat) < (n::nat) ==> (0::nat) mod n = (0::nat)"
  sorry

lemma ZERO_DIV: "(0::nat) < (n::nat) ==> (0::nat) div n = (0::nat)"
  sorry

lemma MOD_MULT: "(r::nat) < (n::nat) ==> ((q::nat) * n + r) mod n = r"
  sorry

lemma MOD_TIMES: "(0::nat) < (n::nat) ==> ((q::nat) * n + (r::nat)) mod n = r mod n"
  sorry

lemma MOD_PLUS: "(0::nat) < (n::nat)
==> ((j::nat) mod n + (k::nat) mod n) mod n = (j + k) mod n"
  sorry

lemma MOD_MOD: "(0::nat) < (n::nat) ==> (k::nat) mod n mod n = k mod n"
  sorry

lemma ADD_DIV_ADD_DIV: "(0::nat) < (x::nat) ==> ((xa::nat) * x + (r::nat)) div x = xa + r div x"
  sorry

lemma MOD_MULT_MOD: "(0::nat) < (n::nat) & (0::nat) < (m::nat)
==> (x::nat) mod (n * m) mod n = x mod n"
  sorry

lemma DIVMOD_ID: "(0::nat) < (n::nat) ==> n div n = (1::nat) & n mod n = (0::nat)"
  sorry

lemma DIV_DIV_DIV_MULT: "(0::nat) < (x::nat) & (0::nat) < (xa::nat)
==> (xb::nat) div x div xa = xb div (x * xa)"
  sorry

lemma DIV_P: "(0::nat) < (q::nat)
==> (P::nat => bool) ((p::nat) div q) =
    (EX (k::nat) r::nat. p = k * q + r & r < q & P k)"
  sorry

lemma MOD_P: "(0::nat) < (q::nat)
==> (P::nat => bool) ((p::nat) mod q) =
    (EX (k::nat) r::nat. p = k * q + r & r < q & P r)"
  sorry

lemma MOD_TIMES2: "(0::nat) < (n::nat)
==> (j::nat) mod n * ((k::nat) mod n) mod n = j * k mod n"
  sorry

lemma MOD_COMMON_FACTOR: "(0::nat) < (n::nat) & (0::nat) < (q::nat)
==> n * ((p::nat) mod q) = n * p mod (n * q)"
  sorry

lemma num_case_cong: "M = M' & (M' = 0 --> b = b') & (ALL n. M' = Suc n --> f n = f' n)
==> nat_case b f M = nat_case b' f' M'"
  sorry

lemma SUC_ELIM_THM: "(ALL n. P (Suc n) n) = (ALL n>0. P n (n - 1))"
  sorry

lemma SUB_ELIM_THM: "(P::nat => bool) ((a::nat) - (b::nat)) =
(ALL x::nat. (b = a + x --> P (0::nat)) & (a = b + x --> P x))"
  sorry

lemma PRE_ELIM_THM: "P (PRE n) = (ALL m. (n = 0 --> P 0) & (n = Suc m --> P m))"
  sorry

lemma MULT_INCREASES: "1 < m & 0 < n ==> Suc n <= m * n"
  sorry

lemma EXP_ALWAYS_BIG_ENOUGH: "(1::nat) < (b::nat) ==> EX m::nat. (n::nat) <= b ^ m"
  sorry

lemma EXP_EQ_0: "((n::nat) ^ (m::nat) = (0::nat)) = (n = (0::nat) & (0::nat) < m)"
  sorry

lemma EXP_1: "(1::nat) ^ (x::nat) = (1::nat) & x ^ (1::nat) = x"
  sorry

lemma MIN_MAX_EQ: "(min (x::nat) (xa::nat) = max x xa) = (x = xa)"
  sorry

lemma MIN_MAX_LT: "(min (x::nat) (xa::nat) < max x xa) = (x ~= xa)"
  sorry

lemma MIN_MAX_PRED: "(P::nat => bool) (m::nat) & P (n::nat) ==> P (min m n) & P (max m n)"
  sorry

lemma MIN_LT: "(min (xa::nat) (x::nat) < xa) = (xa ~= x & min xa x = x) &
(min xa x < x) = (xa ~= x & min xa x = xa) &
(xa < min xa x) = False & (x < min xa x) = False"
  sorry

lemma MAX_LT: "((xa::nat) < max xa (x::nat)) = (xa ~= x & max xa x = x) &
(x < max xa x) = (xa ~= x & max xa x = xa) &
(max xa x < xa) = False & (max xa x < x) = False"
  sorry

lemma MIN_LE: "min (xa::nat) (x::nat) <= xa & min xa x <= x"
  sorry

lemma MAX_LE: "(xa::nat) <= max xa (x::nat) & x <= max xa x"
  sorry

lemma MIN_0: "min (x::nat) (0::nat) = (0::nat) & min (0::nat) x = (0::nat)"
  sorry

lemma MAX_0: "max (x::nat) (0::nat) = x & max (0::nat) x = x"
  sorry

lemma EXISTS_GREATEST: "(Ex (P::nat => bool) & (EX x::nat. ALL y>x. ~ P y)) =
(EX x::nat. P x & (ALL y>x. ~ P y))"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" hrat

definition
  trat_1 :: "nat * nat"  where
  "trat_1 == (0, 0)"

lemma trat_1: "trat_1 = (0, 0)"
  sorry

definition
  trat_inv :: "nat * nat => nat * nat"  where
  "trat_inv == %(x, y). (y, x)"

lemma trat_inv: "trat_inv (x, y) = (y, x)"
  sorry

definition
  trat_add :: "nat * nat => nat * nat => nat * nat"  where
  "trat_add ==
%(x, y) (x', y').
   (PRE (Suc x * Suc y' + Suc x' * Suc y), PRE (Suc y * Suc y'))"

lemma trat_add: "trat_add (x, y) (x', y') =
(PRE (Suc x * Suc y' + Suc x' * Suc y), PRE (Suc y * Suc y'))"
  sorry

definition
  trat_mul :: "nat * nat => nat * nat => nat * nat"  where
  "trat_mul == %(x, y) (x', y'). (PRE (Suc x * Suc x'), PRE (Suc y * Suc y'))"

lemma trat_mul: "trat_mul (x, y) (x', y') = (PRE (Suc x * Suc x'), PRE (Suc y * Suc y'))"
  sorry

consts
  trat_sucint :: "nat => nat * nat" 

specification (trat_sucint) trat_sucint: "trat_sucint 0 = trat_1 &
(ALL n. trat_sucint (Suc n) = trat_add (trat_sucint n) trat_1)"
  sorry

definition
  trat_eq :: "nat * nat => nat * nat => bool"  where
  "trat_eq == %(x, y) (x', y'). Suc x * Suc y' = Suc x' * Suc y"

lemma trat_eq: "trat_eq (x, y) (x', y') = (Suc x * Suc y' = Suc x' * Suc y)"
  sorry

lemma TRAT_EQ_REFL: "trat_eq p p"
  sorry

lemma TRAT_EQ_SYM: "trat_eq p q = trat_eq q p"
  sorry

lemma TRAT_EQ_TRANS: "trat_eq p q & trat_eq q r ==> trat_eq p r"
  sorry

lemma TRAT_EQ_AP: "p = q ==> trat_eq p q"
  sorry

lemma TRAT_ADD_SYM_EQ: "trat_add h i = trat_add i h"
  sorry

lemma TRAT_MUL_SYM_EQ: "trat_mul h i = trat_mul i h"
  sorry

lemma TRAT_INV_WELLDEFINED: "trat_eq p q ==> trat_eq (trat_inv p) (trat_inv q)"
  sorry

lemma TRAT_ADD_WELLDEFINED: "trat_eq p q ==> trat_eq (trat_add p r) (trat_add q r)"
  sorry

lemma TRAT_ADD_WELLDEFINED2: "trat_eq p1 p2 & trat_eq q1 q2 ==> trat_eq (trat_add p1 q1) (trat_add p2 q2)"
  sorry

lemma TRAT_MUL_WELLDEFINED: "trat_eq p q ==> trat_eq (trat_mul p r) (trat_mul q r)"
  sorry

lemma TRAT_MUL_WELLDEFINED2: "trat_eq p1 p2 & trat_eq q1 q2 ==> trat_eq (trat_mul p1 q1) (trat_mul p2 q2)"
  sorry

lemma TRAT_ADD_SYM: "trat_eq (trat_add h i) (trat_add i h)"
  sorry

lemma TRAT_ADD_ASSOC: "trat_eq (trat_add h (trat_add i j)) (trat_add (trat_add h i) j)"
  sorry

lemma TRAT_MUL_SYM: "trat_eq (trat_mul h i) (trat_mul i h)"
  sorry

lemma TRAT_MUL_ASSOC: "trat_eq (trat_mul h (trat_mul i j)) (trat_mul (trat_mul h i) j)"
  sorry

lemma TRAT_LDISTRIB: "trat_eq (trat_mul h (trat_add i j)) (trat_add (trat_mul h i) (trat_mul h j))"
  sorry

lemma TRAT_MUL_LID: "trat_eq (trat_mul trat_1 h) h"
  sorry

lemma TRAT_MUL_LINV: "trat_eq (trat_mul (trat_inv h) h) trat_1"
  sorry

lemma TRAT_NOZERO: "~ trat_eq (trat_add h i) h"
  sorry

lemma TRAT_ADD_TOTAL: "trat_eq h i |
(EX d. trat_eq h (trat_add i d)) | (EX d. trat_eq i (trat_add h d))"
  sorry

lemma TRAT_SUCINT_0: "trat_eq (trat_sucint n) (n, 0)"
  sorry

lemma TRAT_ARCH: "EX n d. trat_eq (trat_sucint n) (trat_add h d)"
  sorry

lemma TRAT_SUCINT: "trat_eq (trat_sucint 0) trat_1 &
(ALL n. trat_eq (trat_sucint (Suc n)) (trat_add (trat_sucint n) trat_1))"
  sorry

lemma TRAT_EQ_EQUIV: "trat_eq p q = (trat_eq p = trat_eq q)"
  sorry

typedef (open) hrat = "{x. EX xa. x = trat_eq xa}" 
  sorry

lemmas hrat_TY_DEF = typedef_hol2hol4 [OF type_definition_hrat]

consts
  mk_hrat :: "(nat * nat => bool) => hrat" 
  dest_hrat :: "hrat => nat * nat => bool" 

specification (dest_hrat mk_hrat) hrat_tybij: "(ALL a. mk_hrat (dest_hrat a) = a) &
(ALL r. (EX x. r = trat_eq x) = (dest_hrat (mk_hrat r) = r))"
  sorry

definition
  hrat_1 :: "hrat"  where
  "hrat_1 == mk_hrat (trat_eq trat_1)"

lemma hrat_1: "hrat_1 = mk_hrat (trat_eq trat_1)"
  sorry

definition
  hrat_inv :: "hrat => hrat"  where
  "hrat_inv == %T1. mk_hrat (trat_eq (trat_inv (Eps (dest_hrat T1))))"

lemma hrat_inv: "hrat_inv T1 = mk_hrat (trat_eq (trat_inv (Eps (dest_hrat T1))))"
  sorry

definition
  hrat_add :: "hrat => hrat => hrat"  where
  "hrat_add ==
%T1 T2.
   mk_hrat (trat_eq (trat_add (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"

lemma hrat_add: "hrat_add T1 T2 =
mk_hrat (trat_eq (trat_add (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"
  sorry

definition
  hrat_mul :: "hrat => hrat => hrat"  where
  "hrat_mul ==
%T1 T2.
   mk_hrat (trat_eq (trat_mul (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"

lemma hrat_mul: "hrat_mul T1 T2 =
mk_hrat (trat_eq (trat_mul (Eps (dest_hrat T1)) (Eps (dest_hrat T2))))"
  sorry

definition
  hrat_sucint :: "nat => hrat"  where
  "hrat_sucint == %T1. mk_hrat (trat_eq (trat_sucint T1))"

lemma hrat_sucint: "hrat_sucint T1 = mk_hrat (trat_eq (trat_sucint T1))"
  sorry

lemma HRAT_ADD_SYM: "hrat_add h i = hrat_add i h"
  sorry

lemma HRAT_ADD_ASSOC: "hrat_add h (hrat_add i j) = hrat_add (hrat_add h i) j"
  sorry

lemma HRAT_MUL_SYM: "hrat_mul h i = hrat_mul i h"
  sorry

lemma HRAT_MUL_ASSOC: "hrat_mul h (hrat_mul i j) = hrat_mul (hrat_mul h i) j"
  sorry

lemma HRAT_LDISTRIB: "hrat_mul h (hrat_add i j) = hrat_add (hrat_mul h i) (hrat_mul h j)"
  sorry

lemma HRAT_MUL_LID: "hrat_mul hrat_1 h = h"
  sorry

lemma HRAT_MUL_LINV: "hrat_mul (hrat_inv h) h = hrat_1"
  sorry

lemma HRAT_NOZERO: "hrat_add h i ~= h"
  sorry

lemma HRAT_ADD_TOTAL: "h = i | (EX x. h = hrat_add i x) | (EX x. i = hrat_add h x)"
  sorry

lemma HRAT_ARCH: "EX x xa. hrat_sucint x = hrat_add h xa"
  sorry

lemma HRAT_SUCINT: "hrat_sucint 0 = hrat_1 &
(ALL x. hrat_sucint (Suc x) = hrat_add (hrat_sucint x) hrat_1)"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" hreal

definition
  hrat_lt :: "hrat => hrat => bool"  where
  "hrat_lt == %x y. EX d. y = hrat_add x d"

lemma hrat_lt: "hrat_lt x y = (EX d. y = hrat_add x d)"
  sorry

lemma HRAT_LT_REFL: "~ hrat_lt x x"
  sorry

lemma HRAT_LT_TRANS: "hrat_lt x y & hrat_lt y z ==> hrat_lt x z"
  sorry

lemma HRAT_LT_ANTISYM: "~ (hrat_lt x y & hrat_lt y x)"
  sorry

lemma HRAT_LT_TOTAL: "x = y | hrat_lt x y | hrat_lt y x"
  sorry

lemma HRAT_MUL_RID: "hrat_mul x hrat_1 = x"
  sorry

lemma HRAT_MUL_RINV: "hrat_mul x (hrat_inv x) = hrat_1"
  sorry

lemma HRAT_RDISTRIB: "hrat_mul (hrat_add x y) z = hrat_add (hrat_mul x z) (hrat_mul y z)"
  sorry

lemma HRAT_LT_ADDL: "hrat_lt x (hrat_add x y)"
  sorry

lemma HRAT_LT_ADDR: "hrat_lt xa (hrat_add x xa)"
  sorry

lemma HRAT_LT_GT: "hrat_lt x y ==> ~ hrat_lt y x"
  sorry

lemma HRAT_LT_NE: "hrat_lt x y ==> x ~= y"
  sorry

lemma HRAT_EQ_LADD: "(hrat_add x y = hrat_add x z) = (y = z)"
  sorry

lemma HRAT_EQ_LMUL: "(hrat_mul x y = hrat_mul x z) = (y = z)"
  sorry

lemma HRAT_LT_ADD2: "hrat_lt u x & hrat_lt v y ==> hrat_lt (hrat_add u v) (hrat_add x y)"
  sorry

lemma HRAT_LT_LADD: "hrat_lt (hrat_add z x) (hrat_add z y) = hrat_lt x y"
  sorry

lemma HRAT_LT_RADD: "hrat_lt (hrat_add x z) (hrat_add y z) = hrat_lt x y"
  sorry

lemma HRAT_LT_MUL2: "hrat_lt u x & hrat_lt v y ==> hrat_lt (hrat_mul u v) (hrat_mul x y)"
  sorry

lemma HRAT_LT_LMUL: "hrat_lt (hrat_mul z x) (hrat_mul z y) = hrat_lt x y"
  sorry

lemma HRAT_LT_RMUL: "hrat_lt (hrat_mul x z) (hrat_mul y z) = hrat_lt x y"
  sorry

lemma HRAT_LT_LMUL1: "hrat_lt (hrat_mul x y) y = hrat_lt x hrat_1"
  sorry

lemma HRAT_LT_RMUL1: "hrat_lt (hrat_mul x y) x = hrat_lt y hrat_1"
  sorry

lemma HRAT_GT_LMUL1: "hrat_lt y (hrat_mul x y) = hrat_lt hrat_1 x"
  sorry

lemma HRAT_LT_L1: "hrat_lt (hrat_mul (hrat_inv x) y) hrat_1 = hrat_lt y x"
  sorry

lemma HRAT_LT_R1: "hrat_lt (hrat_mul x (hrat_inv y)) hrat_1 = hrat_lt x y"
  sorry

lemma HRAT_GT_L1: "hrat_lt hrat_1 (hrat_mul (hrat_inv x) y) = hrat_lt x y"
  sorry

lemma HRAT_INV_MUL: "hrat_inv (hrat_mul x y) = hrat_mul (hrat_inv x) (hrat_inv y)"
  sorry

lemma HRAT_UP: "Ex (hrat_lt x)"
  sorry

lemma HRAT_DOWN: "EX xa. hrat_lt xa x"
  sorry

lemma HRAT_DOWN2: "EX xa. hrat_lt xa x & hrat_lt xa y"
  sorry

lemma HRAT_MEAN: "hrat_lt x y ==> EX xa. hrat_lt x xa & hrat_lt xa y"
  sorry

definition
  isacut :: "(hrat => bool) => bool"  where
  "isacut ==
%C. Ex C &
    (EX x. ~ C x) &
    (ALL x y. C x & hrat_lt y x --> C y) &
    (ALL x. C x --> (EX y. C y & hrat_lt x y))"

lemma isacut: "isacut (CC::hrat => bool) =
(Ex CC &
 (EX x::hrat. ~ CC x) &
 (ALL (x::hrat) y::hrat. CC x & hrat_lt y x --> CC y) &
 (ALL x::hrat. CC x --> (EX y::hrat. CC y & hrat_lt x y)))"
  sorry

definition
  cut_of_hrat :: "hrat => hrat => bool"  where
  "cut_of_hrat == %x y. hrat_lt y x"

lemma cut_of_hrat: "cut_of_hrat x = (%y. hrat_lt y x)"
  sorry

lemma ISACUT_HRAT: "isacut (cut_of_hrat h)"
  sorry

typedef (open) hreal = "Collect isacut" 
  sorry

lemmas hreal_TY_DEF = typedef_hol2hol4 [OF type_definition_hreal]

consts
  hreal :: "(hrat => bool) => hreal" 
  cut :: "hreal => hrat => bool" 

specification (cut hreal) hreal_tybij: "(ALL a. hreal (cut a) = a) & (ALL r. isacut r = (cut (hreal r) = r))"
  sorry

lemma EQUAL_CUTS: "cut X = cut Y ==> X = Y"
  sorry

lemma CUT_ISACUT: "isacut (cut x)"
  sorry

lemma CUT_NONEMPTY: "Ex (cut x)"
  sorry

lemma CUT_BOUNDED: "EX xa. ~ cut x xa"
  sorry

lemma CUT_DOWN: "cut x xa & hrat_lt xb xa ==> cut x xb"
  sorry

lemma CUT_UP: "cut x xa ==> EX y. cut x y & hrat_lt xa y"
  sorry

lemma CUT_UBOUND: "~ cut x xa & hrat_lt xa xb ==> ~ cut x xb"
  sorry

lemma CUT_STRADDLE: "cut X x & ~ cut X y ==> hrat_lt x y"
  sorry

lemma CUT_NEARTOP_ADD: "EX x. cut X x & ~ cut X (hrat_add x e)"
  sorry

lemma CUT_NEARTOP_MUL: "hrat_lt hrat_1 u ==> EX x. cut X x & ~ cut X (hrat_mul u x)"
  sorry

definition
  hreal_1 :: "hreal"  where
  "hreal_1 == hreal (cut_of_hrat hrat_1)"

lemma hreal_1: "hreal_1 = hreal (cut_of_hrat hrat_1)"
  sorry

definition
  hreal_add :: "hreal => hreal => hreal"  where
  "hreal_add == %X Y. hreal (%w. EX x y. w = hrat_add x y & cut X x & cut Y y)"

lemma hreal_add: "hreal_add X Y = hreal (%w. EX x y. w = hrat_add x y & cut X x & cut Y y)"
  sorry

definition
  hreal_mul :: "hreal => hreal => hreal"  where
  "hreal_mul == %X Y. hreal (%w. EX x y. w = hrat_mul x y & cut X x & cut Y y)"

lemma hreal_mul: "hreal_mul X Y = hreal (%w. EX x y. w = hrat_mul x y & cut X x & cut Y y)"
  sorry

definition
  hreal_inv :: "hreal => hreal"  where
  "hreal_inv ==
%X. hreal
     (%w. EX d. hrat_lt d hrat_1 &
                (ALL x. cut X x --> hrat_lt (hrat_mul w x) d))"

lemma hreal_inv: "hreal_inv X =
hreal
 (%w. EX d. hrat_lt d hrat_1 &
            (ALL x. cut X x --> hrat_lt (hrat_mul w x) d))"
  sorry

definition
  hreal_sup :: "(hreal => bool) => hreal"  where
  "hreal_sup == %P. hreal (%w. EX X. P X & cut X w)"

lemma hreal_sup: "hreal_sup P = hreal (%w. EX X. P X & cut X w)"
  sorry

definition
  hreal_lt :: "hreal => hreal => bool"  where
  "hreal_lt == %X Y. X ~= Y & (ALL x. cut X x --> cut Y x)"

lemma hreal_lt: "hreal_lt X Y = (X ~= Y & (ALL x. cut X x --> cut Y x))"
  sorry

lemma HREAL_INV_ISACUT: "isacut
 (%w. EX d. hrat_lt d hrat_1 &
            (ALL x. cut X x --> hrat_lt (hrat_mul w x) d))"
  sorry

lemma HREAL_ADD_ISACUT: "isacut (%w. EX x y. w = hrat_add x y & cut X x & cut Y y)"
  sorry

lemma HREAL_MUL_ISACUT: "isacut (%w. EX x y. w = hrat_mul x y & cut X x & cut Y y)"
  sorry

lemma HREAL_ADD_SYM: "hreal_add X Y = hreal_add Y X"
  sorry

lemma HREAL_MUL_SYM: "hreal_mul X Y = hreal_mul Y X"
  sorry

lemma HREAL_ADD_ASSOC: "hreal_add X (hreal_add Y Z) = hreal_add (hreal_add X Y) Z"
  sorry

lemma HREAL_MUL_ASSOC: "hreal_mul X (hreal_mul Y Z) = hreal_mul (hreal_mul X Y) Z"
  sorry

lemma HREAL_LDISTRIB: "hreal_mul X (hreal_add Y Z) = hreal_add (hreal_mul X Y) (hreal_mul X Z)"
  sorry

lemma HREAL_MUL_LID: "hreal_mul hreal_1 X = X"
  sorry

lemma HREAL_MUL_LINV: "hreal_mul (hreal_inv X) X = hreal_1"
  sorry

lemma HREAL_NOZERO: "hreal_add X Y ~= X"
  sorry

definition
  hreal_sub :: "hreal => hreal => hreal"  where
  "hreal_sub == %Y X. hreal (%w. EX x. ~ cut X x & cut Y (hrat_add x w))"

lemma hreal_sub: "hreal_sub Y X = hreal (%w. EX x. ~ cut X x & cut Y (hrat_add x w))"
  sorry

lemma HREAL_LT_LEMMA: "hreal_lt X Y ==> EX x. ~ cut X x & cut Y x"
  sorry

lemma HREAL_SUB_ISACUT: "hreal_lt X Y ==> isacut (%w. EX x. ~ cut X x & cut Y (hrat_add x w))"
  sorry

lemma HREAL_SUB_ADD: "hreal_lt X Y ==> hreal_add (hreal_sub Y X) X = Y"
  sorry

lemma HREAL_LT_TOTAL: "X = Y | hreal_lt X Y | hreal_lt Y X"
  sorry

lemma HREAL_LT: "hreal_lt X Y = (EX D. Y = hreal_add X D)"
  sorry

lemma HREAL_ADD_TOTAL: "X = Y | (EX D. Y = hreal_add X D) | (EX D. X = hreal_add Y D)"
  sorry

lemma HREAL_SUP_ISACUT: "Ex P & (EX Y. ALL X. P X --> hreal_lt X Y)
==> isacut (%w. EX X. P X & cut X w)"
  sorry

lemma HREAL_SUP: "Ex P & (EX Y. ALL X. P X --> hreal_lt X Y)
==> (EX X. P X & hreal_lt Y X) = hreal_lt Y (hreal_sup P)"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" numeral

lemma numeral_suc: "Suc ALT_ZERO = NUMERAL_BIT1 ALT_ZERO &
(ALL x. Suc (NUMERAL_BIT1 x) = NUMERAL_BIT2 x) &
(ALL x. Suc (NUMERAL_BIT2 x) = NUMERAL_BIT1 (Suc x))"
  sorry

definition
  iZ :: "nat => nat"  where
  "iZ == %x. x"

lemma iZ: "iZ x = x"
  sorry

definition
  iiSUC :: "nat => nat"  where
  "iiSUC == %n. Suc (Suc n)"

lemma iiSUC: "iiSUC n = Suc (Suc n)"
  sorry

lemma numeral_distrib: "(ALL x::nat. (0::nat) + x = x) &
(ALL x::nat. x + (0::nat) = x) &
(ALL (x::nat) xa::nat. NUMERAL x + NUMERAL xa = NUMERAL (iZ (x + xa))) &
(ALL x::nat. (0::nat) * x = (0::nat)) &
(ALL x::nat. x * (0::nat) = (0::nat)) &
(ALL (x::nat) xa::nat. NUMERAL x * NUMERAL xa = NUMERAL (x * xa)) &
(ALL x::nat. (0::nat) - x = (0::nat)) &
(ALL x::nat. x - (0::nat) = x) &
(ALL (x::nat) xa::nat. NUMERAL x - NUMERAL xa = NUMERAL (x - xa)) &
(ALL x::nat. (0::nat) ^ NUMERAL (NUMERAL_BIT1 x) = (0::nat)) &
(ALL x::nat. (0::nat) ^ NUMERAL (NUMERAL_BIT2 x) = (0::nat)) &
(ALL x::nat. x ^ (0::nat) = (1::nat)) &
(ALL (x::nat) xa::nat. NUMERAL x ^ NUMERAL xa = NUMERAL (x ^ xa)) &
Suc (0::nat) = (1::nat) &
(ALL x::nat. Suc (NUMERAL x) = NUMERAL (Suc x)) &
PRE (0::nat) = (0::nat) &
(ALL x::nat. PRE (NUMERAL x) = NUMERAL (PRE x)) &
(ALL x::nat. (NUMERAL x = (0::nat)) = (x = ALT_ZERO)) &
(ALL x::nat. ((0::nat) = NUMERAL x) = (x = ALT_ZERO)) &
(ALL (x::nat) xa::nat. (NUMERAL x = NUMERAL xa) = (x = xa)) &
(ALL x::nat. (x < (0::nat)) = False) &
(ALL x::nat. ((0::nat) < NUMERAL x) = (ALT_ZERO < x)) &
(ALL (x::nat) xa::nat. (NUMERAL x < NUMERAL xa) = (x < xa)) &
(ALL x::nat. (x < (0::nat)) = False) &
(ALL x::nat. ((0::nat) < NUMERAL x) = (ALT_ZERO < x)) &
(ALL (x::nat) xa::nat. (NUMERAL xa < NUMERAL x) = (xa < x)) &
(ALL x::nat. ((0::nat) <= x) = True) &
(ALL x::nat. (NUMERAL x <= (0::nat)) = (x <= ALT_ZERO)) &
(ALL (x::nat) xa::nat. (NUMERAL x <= NUMERAL xa) = (x <= xa)) &
(ALL x::nat. ((0::nat) <= x) = True) &
(ALL x::nat. (x <= (0::nat)) = (x = (0::nat))) &
(ALL (x::nat) xa::nat. (NUMERAL xa <= NUMERAL x) = (xa <= x)) &
(ALL x::nat. ODD (NUMERAL x) = ODD x) &
(ALL x::nat. EVEN (NUMERAL x) = EVEN x) & ~ ODD (0::nat) & EVEN (0::nat)"
  sorry

lemma numeral_iisuc: "iiSUC ALT_ZERO = NUMERAL_BIT2 ALT_ZERO &
iiSUC (NUMERAL_BIT1 n) = NUMERAL_BIT1 (Suc n) &
iiSUC (NUMERAL_BIT2 n) = NUMERAL_BIT2 (Suc n)"
  sorry

lemma numeral_add: "iZ (ALT_ZERO + x) = x &
iZ (x + ALT_ZERO) = x &
iZ (NUMERAL_BIT1 x + NUMERAL_BIT1 xa) = NUMERAL_BIT2 (iZ (x + xa)) &
iZ (NUMERAL_BIT1 x + NUMERAL_BIT2 xa) = NUMERAL_BIT1 (Suc (x + xa)) &
iZ (NUMERAL_BIT2 x + NUMERAL_BIT1 xa) = NUMERAL_BIT1 (Suc (x + xa)) &
iZ (NUMERAL_BIT2 x + NUMERAL_BIT2 xa) = NUMERAL_BIT2 (Suc (x + xa)) &
Suc (ALT_ZERO + x) = Suc x &
Suc (x + ALT_ZERO) = Suc x &
Suc (NUMERAL_BIT1 x + NUMERAL_BIT1 xa) = NUMERAL_BIT1 (Suc (x + xa)) &
Suc (NUMERAL_BIT1 x + NUMERAL_BIT2 xa) = NUMERAL_BIT2 (Suc (x + xa)) &
Suc (NUMERAL_BIT2 x + NUMERAL_BIT1 xa) = NUMERAL_BIT2 (Suc (x + xa)) &
Suc (NUMERAL_BIT2 x + NUMERAL_BIT2 xa) = NUMERAL_BIT1 (iiSUC (x + xa)) &
iiSUC (ALT_ZERO + x) = iiSUC x &
iiSUC (x + ALT_ZERO) = iiSUC x &
iiSUC (NUMERAL_BIT1 x + NUMERAL_BIT1 xa) = NUMERAL_BIT2 (Suc (x + xa)) &
iiSUC (NUMERAL_BIT1 x + NUMERAL_BIT2 xa) = NUMERAL_BIT1 (iiSUC (x + xa)) &
iiSUC (NUMERAL_BIT2 x + NUMERAL_BIT1 xa) = NUMERAL_BIT1 (iiSUC (x + xa)) &
iiSUC (NUMERAL_BIT2 x + NUMERAL_BIT2 xa) = NUMERAL_BIT2 (iiSUC (x + xa))"
  sorry

lemma numeral_eq: "(ALT_ZERO = NUMERAL_BIT1 x) = False &
(NUMERAL_BIT1 x = ALT_ZERO) = False &
(ALT_ZERO = NUMERAL_BIT2 x) = False &
(NUMERAL_BIT2 x = ALT_ZERO) = False &
(NUMERAL_BIT1 x = NUMERAL_BIT2 xa) = False &
(NUMERAL_BIT2 x = NUMERAL_BIT1 xa) = False &
(NUMERAL_BIT1 x = NUMERAL_BIT1 xa) = (x = xa) &
(NUMERAL_BIT2 x = NUMERAL_BIT2 xa) = (x = xa)"
  sorry

lemma numeral_lt: "(ALT_ZERO < NUMERAL_BIT1 x) = True &
(ALT_ZERO < NUMERAL_BIT2 x) = True &
(x < ALT_ZERO) = False &
(NUMERAL_BIT1 x < NUMERAL_BIT1 xa) = (x < xa) &
(NUMERAL_BIT2 x < NUMERAL_BIT2 xa) = (x < xa) &
(NUMERAL_BIT1 x < NUMERAL_BIT2 xa) = (~ xa < x) &
(NUMERAL_BIT2 x < NUMERAL_BIT1 xa) = (x < xa)"
  sorry

lemma numeral_lte: "(ALT_ZERO <= x) = True &
(NUMERAL_BIT1 x <= ALT_ZERO) = False &
(NUMERAL_BIT2 x <= ALT_ZERO) = False &
(NUMERAL_BIT1 x <= NUMERAL_BIT1 xa) = (x <= xa) &
(NUMERAL_BIT1 x <= NUMERAL_BIT2 xa) = (x <= xa) &
(NUMERAL_BIT2 x <= NUMERAL_BIT1 xa) = (~ xa <= x) &
(NUMERAL_BIT2 x <= NUMERAL_BIT2 xa) = (x <= xa)"
  sorry

lemma numeral_pre: "PRE ALT_ZERO = ALT_ZERO &
PRE (NUMERAL_BIT1 ALT_ZERO) = ALT_ZERO &
(ALL x.
    PRE (NUMERAL_BIT1 (NUMERAL_BIT1 x)) =
    NUMERAL_BIT2 (PRE (NUMERAL_BIT1 x))) &
(ALL x.
    PRE (NUMERAL_BIT1 (NUMERAL_BIT2 x)) = NUMERAL_BIT2 (NUMERAL_BIT1 x)) &
(ALL x. PRE (NUMERAL_BIT2 x) = NUMERAL_BIT1 x)"
  sorry

lemma bit_initiality: "EX x. x ALT_ZERO = zf &
      (ALL n. x (NUMERAL_BIT1 n) = b1f n (x n)) &
      (ALL n. x (NUMERAL_BIT2 n) = b2f n (x n))"
  sorry

consts
  iBIT_cases :: "nat => 'a => (nat => 'a) => (nat => 'a) => 'a" 

specification (iBIT_cases) iBIT_cases: "(ALL (zf::'a) (bf1::nat => 'a) bf2::nat => 'a.
    iBIT_cases ALT_ZERO zf bf1 bf2 = zf) &
(ALL (n::nat) (zf::'a) (bf1::nat => 'a) bf2::nat => 'a.
    iBIT_cases (NUMERAL_BIT1 n) zf bf1 bf2 = bf1 n) &
(ALL (n::nat) (zf::'a) (bf1::nat => 'a) bf2::nat => 'a.
    iBIT_cases (NUMERAL_BIT2 n) zf bf1 bf2 = bf2 n)"
  sorry

definition
  iDUB :: "nat => nat"  where
  "iDUB == %x. x + x"

lemma iDUB: "iDUB x = x + x"
  sorry

consts
  iSUB :: "bool => nat => nat => nat" 

specification (iSUB) iSUB_DEF: "(ALL b x. iSUB b ALT_ZERO x = ALT_ZERO) &
(ALL b n x.
    iSUB b (NUMERAL_BIT1 n) x =
    (if b
     then iBIT_cases x (NUMERAL_BIT1 n) (%m. iDUB (iSUB True n m))
           (%m. NUMERAL_BIT1 (iSUB False n m))
     else iBIT_cases x (iDUB n) (%m. NUMERAL_BIT1 (iSUB False n m))
           (%m. iDUB (iSUB False n m)))) &
(ALL b n x.
    iSUB b (NUMERAL_BIT2 n) x =
    (if b
     then iBIT_cases x (NUMERAL_BIT2 n) (%m. NUMERAL_BIT1 (iSUB True n m))
           (%m. iDUB (iSUB True n m))
     else iBIT_cases x (NUMERAL_BIT1 n) (%m. iDUB (iSUB True n m))
           (%m. NUMERAL_BIT1 (iSUB False n m))))"
  sorry

lemma bit_induction: "P ALT_ZERO &
(ALL n. P n --> P (NUMERAL_BIT1 n)) & (ALL n. P n --> P (NUMERAL_BIT2 n))
==> P x"
  sorry

lemma iSUB_THM: "iSUB (x::bool) ALT_ZERO (xn::nat) = ALT_ZERO &
iSUB True (xa::nat) ALT_ZERO = xa &
iSUB False (NUMERAL_BIT1 xa) ALT_ZERO = iDUB xa &
iSUB True (NUMERAL_BIT1 xa) (NUMERAL_BIT1 (xb::nat)) =
iDUB (iSUB True xa xb) &
iSUB False (NUMERAL_BIT1 xa) (NUMERAL_BIT1 xb) =
NUMERAL_BIT1 (iSUB False xa xb) &
iSUB True (NUMERAL_BIT1 xa) (NUMERAL_BIT2 xb) =
NUMERAL_BIT1 (iSUB False xa xb) &
iSUB False (NUMERAL_BIT1 xa) (NUMERAL_BIT2 xb) = iDUB (iSUB False xa xb) &
iSUB False (NUMERAL_BIT2 xa) ALT_ZERO = NUMERAL_BIT1 xa &
iSUB True (NUMERAL_BIT2 xa) (NUMERAL_BIT1 xb) =
NUMERAL_BIT1 (iSUB True xa xb) &
iSUB False (NUMERAL_BIT2 xa) (NUMERAL_BIT1 xb) = iDUB (iSUB True xa xb) &
iSUB True (NUMERAL_BIT2 xa) (NUMERAL_BIT2 xb) = iDUB (iSUB True xa xb) &
iSUB False (NUMERAL_BIT2 xa) (NUMERAL_BIT2 xb) =
NUMERAL_BIT1 (iSUB False xa xb)"
  sorry

lemma numeral_sub: "NUMERAL (x - xa) = (if xa < x then NUMERAL (iSUB True x xa) else 0)"
  sorry

lemma iDUB_removal: "iDUB (NUMERAL_BIT1 x) = NUMERAL_BIT2 (iDUB x) &
iDUB (NUMERAL_BIT2 x) = NUMERAL_BIT2 (NUMERAL_BIT1 x) &
iDUB ALT_ZERO = ALT_ZERO"
  sorry

lemma numeral_mult: "ALT_ZERO * x = ALT_ZERO &
x * ALT_ZERO = ALT_ZERO &
NUMERAL_BIT1 x * xa = iZ (iDUB (x * xa) + xa) &
NUMERAL_BIT2 x * xa = iDUB (iZ (x * xa + xa))"
  sorry

definition
  iSQR :: "nat => nat"  where
  "iSQR == %x. x * x"

lemma iSQR: "iSQR x = x * x"
  sorry

lemma numeral_exp: "(ALL x. x ^ ALT_ZERO = NUMERAL_BIT1 ALT_ZERO) &
(ALL x xa. x ^ NUMERAL_BIT1 xa = x * iSQR (x ^ xa)) &
(ALL x xa. x ^ NUMERAL_BIT2 xa = iSQR x * iSQR (x ^ xa))"
  sorry

lemma numeral_evenodd: "EVEN ALT_ZERO &
EVEN (NUMERAL_BIT2 x) &
~ EVEN (NUMERAL_BIT1 x) &
~ ODD ALT_ZERO & ~ ODD (NUMERAL_BIT2 x) & ODD (NUMERAL_BIT1 x)"
  sorry

lemma numeral_fact: "FACT n = (if n = 0 then 1 else n * FACT (PRE n))"
  sorry

lemma numeral_funpow: "(f ^^ n) x = (if n = 0 then x else (f ^^ (n - 1)) (f x))"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" ind_type

lemma INJ_INVERSE2: "(!!(x1::'A) (y1::'B) (x2::'A) y2::'B.
    ((P::'A => 'B => 'C) x1 y1 = P x2 y2) = (x1 = x2 & y1 = y2))
==> EX (x::'C => 'A) Y::'C => 'B.
       ALL (xa::'A) y::'B. x (P xa y) = xa & Y (P xa y) = y"
  sorry

definition
  NUMPAIR :: "nat => nat => nat"  where
  "NUMPAIR == %x y. 2 ^ x * (2 * y + 1)"

lemma NUMPAIR: "NUMPAIR x y = 2 ^ x * (2 * y + 1)"
  sorry

lemma NUMPAIR_INJ_LEMMA: "NUMPAIR x xa = NUMPAIR xb xc ==> x = xb"
  sorry

lemma NUMPAIR_INJ: "(NUMPAIR x1 y1 = NUMPAIR x2 y2) = (x1 = x2 & y1 = y2)"
  sorry

consts
  NUMSND :: "nat => nat" 
  NUMFST :: "nat => nat" 

specification (NUMFST NUMSND) NUMPAIR_DEST: "ALL x y. NUMFST (NUMPAIR x y) = x & NUMSND (NUMPAIR x y) = y"
  sorry

definition
  NUMSUM :: "bool => nat => nat"  where
  "NUMSUM == %b x. if b then Suc (2 * x) else 2 * x"

lemma NUMSUM: "NUMSUM b x = (if b then Suc (2 * x) else 2 * x)"
  sorry

lemma NUMSUM_INJ: "(NUMSUM b1 x1 = NUMSUM b2 x2) = (b1 = b2 & x1 = x2)"
  sorry

consts
  NUMRIGHT :: "nat => nat" 
  NUMLEFT :: "nat => bool" 

specification (NUMLEFT NUMRIGHT) NUMSUM_DEST: "ALL x y. NUMLEFT (NUMSUM x y) = x & NUMRIGHT (NUMSUM x y) = y"
  sorry

definition
  INJN :: "nat => nat => 'a => bool"  where
  "INJN == %m n a. n = m"

lemma INJN: "INJN m = (%n a. n = m)"
  sorry

lemma INJN_INJ: "(INJN n1 = INJN n2) = (n1 = n2)"
  sorry

definition
  INJA :: "'a => nat => 'a => bool"  where
  "INJA == %a n b. b = a"

lemma INJA: "INJA a = (%n b. b = a)"
  sorry

lemma INJA_INJ: "(INJA a1 = INJA a2) = (a1 = a2)"
  sorry

definition
  INJF :: "(nat => nat => 'a => bool) => nat => 'a => bool"  where
  "INJF == %f n. f (NUMFST n) (NUMSND n)"

lemma INJF: "INJF f = (%n. f (NUMFST n) (NUMSND n))"
  sorry

lemma INJF_INJ: "(INJF f1 = INJF f2) = (f1 = f2)"
  sorry

definition
  INJP :: "(nat => 'a => bool) => (nat => 'a => bool) => nat => 'a => bool"  where
  "INJP ==
%f1 f2 n a. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a"

lemma INJP: "INJP f1 f2 =
(%n a. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a)"
  sorry

lemma INJP_INJ: "(INJP f1 f2 = INJP f1' f2') = (f1 = f1' & f2 = f2')"
  sorry

definition
  ZCONSTR :: "nat => 'a => (nat => nat => 'a => bool) => nat => 'a => bool"  where
  "ZCONSTR == %c i r. INJP (INJN (Suc c)) (INJP (INJA i) (INJF r))"

lemma ZCONSTR: "ZCONSTR c i r = INJP (INJN (Suc c)) (INJP (INJA i) (INJF r))"
  sorry

definition
  ZBOT :: "nat => 'a => bool"  where
  "ZBOT == INJP (INJN 0) (SOME z. True)"

lemma ZBOT: "ZBOT = INJP (INJN 0) (SOME z. True)"
  sorry

lemma ZCONSTR_ZBOT: "ZCONSTR x xa xb ~= ZBOT"
  sorry

definition
  ZRECSPACE :: "(nat => 'a => bool) => bool"  where
  "ZRECSPACE ==
%a0. ALL ZRECSPACE'.
        (ALL a0.
            a0 = ZBOT |
            (EX c i r. a0 = ZCONSTR c i r & (ALL n. ZRECSPACE' (r n))) -->
            ZRECSPACE' a0) -->
        ZRECSPACE' a0"

lemma ZRECSPACE: "ZRECSPACE =
(%a0. ALL ZRECSPACE'.
         (ALL a0.
             a0 = ZBOT |
             (EX c i r. a0 = ZCONSTR c i r & (ALL n. ZRECSPACE' (r n))) -->
             ZRECSPACE' a0) -->
         ZRECSPACE' a0)"
  sorry

lemma ZRECSPACE_rules: "(op &::bool => bool => bool)
 ((ZRECSPACE::(nat => 'a::type => bool) => bool)
   (ZBOT::nat => 'a::type => bool))
 ((All::(nat => bool) => bool)
   (%c::nat.
       (All::('a::type => bool) => bool)
        (%i::'a::type.
            (All::((nat => nat => 'a::type => bool) => bool) => bool)
             (%r::nat => nat => 'a::type => bool.
                 (op -->::bool => bool => bool)
                  ((All::(nat => bool) => bool)
                    (%n::nat.
                        (ZRECSPACE::(nat => 'a::type => bool) => bool)
                         (r n)))
                  ((ZRECSPACE::(nat => 'a::type => bool) => bool)
                    ((ZCONSTR::nat
                               => 'a::type
                                  => (nat => nat => 'a::type => bool)
                                     => nat => 'a::type => bool)
                      c i r))))))"
  sorry

lemma ZRECSPACE_ind: "[| x ZBOT & (ALL c i r. (ALL n. x (r n)) --> x (ZCONSTR c i r));
   ZRECSPACE a0 |]
==> x a0"
  sorry

lemma ZRECSPACE_cases: "ZRECSPACE a0 =
(a0 = ZBOT | (EX c i r. a0 = ZCONSTR c i r & (ALL n. ZRECSPACE (r n))))"
  sorry

typedef (open) ('a) recspace = "Collect ZRECSPACE :: (nat \<Rightarrow> 'a\<Colon>type \<Rightarrow> bool) set"
  sorry

lemmas recspace_TY_DEF = typedef_hol2hol4 [OF type_definition_recspace]

consts
  mk_rec :: "(nat => 'a => bool) => 'a recspace" 
  dest_rec :: "'a recspace => nat => 'a => bool" 

specification (dest_rec mk_rec) recspace_repfns: "(ALL a::'a recspace. mk_rec (dest_rec a) = a) &
(ALL r::nat => 'a => bool. ZRECSPACE r = (dest_rec (mk_rec r) = r))"
  sorry

definition
  BOTTOM :: "'a recspace"  where
  "BOTTOM == mk_rec ZBOT"

lemma BOTTOM: "BOTTOM = mk_rec ZBOT"
  sorry

definition
  CONSTR :: "nat => 'a => (nat => 'a recspace) => 'a recspace"  where
  "CONSTR == %c i r. mk_rec (ZCONSTR c i (%n. dest_rec (r n)))"

lemma CONSTR: "CONSTR c i r = mk_rec (ZCONSTR c i (%n. dest_rec (r n)))"
  sorry

lemma MK_REC_INJ: "[| mk_rec x = mk_rec y; ZRECSPACE x & ZRECSPACE y |] ==> x = y"
  sorry

lemma DEST_REC_INJ: "(dest_rec x = dest_rec y) = (x = y)"
  sorry

lemma CONSTR_BOT: "CONSTR c i r ~= BOTTOM"
  sorry

lemma CONSTR_INJ: "(CONSTR c1 i1 r1 = CONSTR c2 i2 r2) = (c1 = c2 & i1 = i2 & r1 = r2)"
  sorry

lemma CONSTR_IND: "P BOTTOM & (ALL c i r. (ALL n. P (r n)) --> P (CONSTR c i r)) ==> P x"
  sorry

lemma CONSTR_REC: "EX f. ALL c i r. f (CONSTR c i r) = Fn c i r (%n. f (r n))"
  sorry

consts
  FCONS :: "'a => (nat => 'a) => nat => 'a" 

specification (FCONS) FCONS: "(ALL (a::'a) f::nat => 'a. FCONS a f (0::nat) = a) &
(ALL (a::'a) (f::nat => 'a) n::nat. FCONS a f (Suc n) = f n)"
  sorry

definition
  FNIL :: "nat => 'a"  where
  "FNIL == %n. SOME x. True"

lemma FNIL: "FNIL n = (SOME x. True)"
  sorry

definition
  ISO :: "('a => 'b) => ('b => 'a) => bool"  where
  "ISO == %f g. (ALL x. f (g x) = x) & (ALL y. g (f y) = y)"

lemma ISO: "ISO f g = ((ALL x. f (g x) = x) & (ALL y. g (f y) = y))"
  sorry

lemma ISO_REFL: "ISO (%x. x) (%x. x)"
  sorry

lemma ISO_FUN: "ISO (f::'a => 'c) (f'::'c => 'a) & ISO (g::'b => 'd) (g'::'d => 'b)
==> ISO (%(h::'a => 'b) a'::'c. g (h (f' a')))
     (%(h::'c => 'd) a::'a. g' (h (f a)))"
  sorry

lemma ISO_USAGE: "ISO f g
==> (ALL P. All P = (ALL x. P (g x))) &
    (ALL P. Ex P = (EX x. P (g x))) & (ALL a b. (a = g b) = (f a = b))"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" divides

lemma DIVIDES_FACT: "0 < b ==> b dvd FACT b"
  sorry

lemma DIVIDES_MULT_LEFT: "((x::nat) * (xa::nat) dvd xa) = (xa = (0::nat) | x = (1::nat))"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" prime

consts
  prime :: "nat => bool" 

defs
  prime_primdef: "prime.prime == %a. a ~= 1 & (ALL b. b dvd a --> b = a | b = 1)"

lemma prime_def: "prime.prime a = (a ~= 1 & (ALL b. b dvd a --> b = a | b = 1))"
  sorry

lemma NOT_PRIME_0: "~ prime.prime 0"
  sorry

lemma NOT_PRIME_1: "~ prime.prime 1"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" list

consts
  EL :: "nat => 'a list => 'a" 

specification (EL) EL: "(ALL l::'a list. EL (0::nat) l = hd l) &
(ALL (l::'a list) n::nat. EL (Suc n) l = EL n (tl l))"
  sorry

lemma NULL: "(op &::bool => bool => bool)
 ((List.null::'a::type list => bool) ([]::'a::type list))
 ((All::('a::type => bool) => bool)
   (%x::'a::type.
       (All::('a::type list => bool) => bool)
        (%xa::'a::type list.
            (Not::bool => bool)
             ((List.null::'a::type list => bool)
               ((op #::'a::type => 'a::type list => 'a::type list) x xa)))))"
  sorry

lemma list_case_compute: "list_case (b::'b) (f::'a => 'a list => 'b) (l::'a list) =
(if List.null l then b else f (hd l) (tl l))"
  sorry

lemma LIST_NOT_EQ: "l1 ~= l2 ==> x # l1 ~= xa # l2"
  sorry

lemma NOT_EQ_LIST: "h1 ~= h2 ==> h1 # x ~= h2 # xa"
  sorry

lemma EQ_LIST: "[| h1 = h2; l1 = l2 |] ==> h1 # l1 = h2 # l2"
  sorry

lemma CONS: "~ List.null l ==> hd l # tl l = l"
  sorry

lemma MAP_EQ_NIL: "(map (f::'a => 'b) (l::'a list) = []) = (l = []) & ([] = map f l) = (l = [])"
  sorry

lemma EVERY_EL: "list_all P l = (ALL n<length l. P (EL n l))"
  sorry

lemma EVERY_CONJ: "list_all (%x. P x & Q x) l = (list_all P l & list_all Q l)"
  sorry

lemma EVERY_MEM: "list_all P l = (ALL e. List.member l e --> P e)"
  sorry

lemma EXISTS_MEM: "list_ex P l = (EX e. List.member l e & P e)"
  sorry

lemma MEM_APPEND: "List.member (l1 @ l2) e = (List.member l1 e | List.member l2 e)"
  sorry

lemma NOT_EVERY: "(~ list_all P l) = list_ex (Not o P) l"
  sorry

lemma NOT_EXISTS: "(~ list_ex P l) = list_all (Not o P) l"
  sorry

lemma MEM_MAP: "List.member (map (f::'a => 'b) (l::'a list)) (x::'b) =
(EX y::'a. x = f y & List.member l y)"
  sorry

lemma LENGTH_CONS: "(length l = Suc n) = (EX h l'. length l' = n & l = h # l')"
  sorry

lemma LENGTH_EQ_CONS: "(ALL l. length l = Suc n --> P l) =
(ALL l. length l = n --> (ALL x. P (x # l)))"
  sorry

lemma LENGTH_EQ_NIL: "(ALL l. length l = 0 --> P l) = P []"
  sorry

lemma CONS_ACYCLIC: "l ~= x # l & x # l ~= l"
  sorry

lemma APPEND_eq_NIL: "(ALL (l1::'a list) l2::'a list. ([] = l1 @ l2) = (l1 = [] & l2 = [])) &
(ALL (l1::'a list) l2::'a list. (l1 @ l2 = []) = (l1 = [] & l2 = []))"
  sorry

lemma APPEND_11: "(ALL (l1::'a list) (l2::'a list) l3::'a list.
    (l1 @ l2 = l1 @ l3) = (l2 = l3)) &
(ALL (l1::'a list) (l2::'a list) l3::'a list.
    (l2 @ l1 = l3 @ l1) = (l2 = l3))"
  sorry

lemma EL_compute: "EL n l = (if n = 0 then hd l else EL (PRE n) (tl l))"
  sorry

lemma WF_LIST_PRED: "WF (%L1 L2. EX h. L2 = h # L1)"
  sorry

lemma list_size_cong: "M = N & (ALL x. List.member N x --> f x = f' x)
==> HOL4Compat.list_size f M = HOL4Compat.list_size f' N"
  sorry

lemma FOLDR_CONG: "l = l' & b = b' & (ALL x a. List.member l' x --> f x a = f' x a)
==> foldr f l b = foldr f' l' b'"
  sorry

lemma FOLDL_CONG: "l = l' & b = b' & (ALL x a. List.member l' x --> f a x = f' a x)
==> foldl f b l = foldl f' b' l'"
  sorry

lemma MAP_CONG: "l1 = l2 & (ALL x. List.member l2 x --> f x = f' x) ==> map f l1 = map f' l2"
  sorry

lemma EXISTS_CONG: "l1 = l2 & (ALL x. List.member l2 x --> P x = P' x)
==> list_ex P l1 = list_ex P' l2"
  sorry

lemma EVERY_CONG: "l1 = l2 & (ALL x. List.member l2 x --> P x = P' x)
==> list_all P l1 = list_all P' l2"
  sorry

lemma EVERY_MONOTONIC: "[| !!x. P x ==> Q x; list_all P l |] ==> list_all Q l"
  sorry

lemma LENGTH_ZIP: "length l1 = length l2
==> length (zip l1 l2) = length l1 & length (zip l1 l2) = length l2"
  sorry

lemma LENGTH_UNZIP: "length (fst (unzip pl)) = length pl & length (snd (unzip pl)) = length pl"
  sorry

lemma ZIP_UNZIP: "ZIP (unzip l) = l"
  sorry

lemma UNZIP_ZIP: "length l1 = length l2 ==> unzip (zip l1 l2) = (l1, l2)"
  sorry

lemma ZIP_MAP: "length l1 = length l2
==> zip (map f1 l1) l2 = map (%p. (f1 (fst p), snd p)) (zip l1 l2) &
    zip l1 (map f2 l2) = map (%p. (fst p, f2 (snd p))) (zip l1 l2)"
  sorry

lemma MEM_ZIP: "length l1 = length l2
==> List.member (zip l1 l2) p = (EX n<length l1. p = (EL n l1, EL n l2))"
  sorry

lemma EL_ZIP: "length l1 = length l2 & n < length l1
==> EL n (zip l1 l2) = (EL n l1, EL n l2)"
  sorry

lemma MAP2_ZIP: "length l1 = length l2 ==> map2 f l1 l2 = map (%(x, y). f x y) (zip l1 l2)"
  sorry

lemma MEM_EL: "List.member l x = (EX n<length l. x = EL n l)"
  sorry

lemma LAST_CONS: "(ALL x::'a. last [x] = x) &
(ALL (x::'a) (xa::'a) xb::'a list. last (x # xa # xb) = last (xa # xb))"
  sorry

lemma FRONT_CONS: "(ALL x::'a. butlast [x] = []) &
(ALL (x::'a) (xa::'a) xb::'a list.
    butlast (x # xa # xb) = x # butlast (xa # xb))"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" pred_set

lemma EXTENSION: "(s = t) = (ALL x. IN x s = IN x t)"
  sorry

lemma NOT_EQUAL_SETS: "(x ~= xa) = (EX xb. IN xb xa = (~ IN xb x))"
  sorry

lemma NUM_SET_WOP: "(EX n::nat. IN n (s::nat => bool)) =
(EX n::nat. IN n s & (ALL m::nat. IN m s --> n <= m))"
  sorry

consts
  GSPEC :: "('b => 'a * bool) => 'a => bool" 

specification (GSPEC) GSPECIFICATION: "ALL (f::'b => 'a * bool) v::'a. IN v (GSPEC f) = (EX x::'b. (v, True) = f x)"
  sorry

lemma SET_MINIMUM: "(EX x::'a. IN x (s::'a => bool)) =
(EX x::'a. IN x s & (ALL y::'a. IN y s --> (M::'a => nat) x <= M y))"
  sorry

definition
  EMPTY :: "'a => bool"  where
  "EMPTY == %x. False"

lemma EMPTY_DEF: "EMPTY = (%x. False)"
  sorry

lemma NOT_IN_EMPTY: "~ IN x EMPTY"
  sorry

lemma MEMBER_NOT_EMPTY: "(EX xa. IN xa x) = (x ~= EMPTY)"
  sorry

definition
  UNIV :: "'a => bool"  where
  "UNIV == %x. True"

lemma UNIV_DEF: "pred_set.UNIV = (%x. True)"
  sorry

lemma IN_UNIV: "IN x pred_set.UNIV"
  sorry

lemma UNIV_NOT_EMPTY: "pred_set.UNIV ~= EMPTY"
  sorry

lemma EMPTY_NOT_UNIV: "EMPTY ~= pred_set.UNIV"
  sorry

lemma EQ_UNIV: "(ALL x. IN x s) = (s = pred_set.UNIV)"
  sorry

definition
  SUBSET :: "('a => bool) => ('a => bool) => bool"  where
  "SUBSET == %s t. ALL x. IN x s --> IN x t"

lemma SUBSET_DEF: "SUBSET s t = (ALL x. IN x s --> IN x t)"
  sorry

lemma SUBSET_TRANS: "SUBSET x xa & SUBSET xa xb ==> SUBSET x xb"
  sorry

lemma SUBSET_REFL: "SUBSET x x"
  sorry

lemma SUBSET_ANTISYM: "SUBSET x xa & SUBSET xa x ==> x = xa"
  sorry

lemma EMPTY_SUBSET: "SUBSET EMPTY x"
  sorry

lemma SUBSET_EMPTY: "SUBSET x EMPTY = (x = EMPTY)"
  sorry

lemma SUBSET_UNIV: "SUBSET x pred_set.UNIV"
  sorry

lemma UNIV_SUBSET: "SUBSET pred_set.UNIV x = (x = pred_set.UNIV)"
  sorry

definition
  PSUBSET :: "('a => bool) => ('a => bool) => bool"  where
  "PSUBSET == %s t. SUBSET s t & s ~= t"

lemma PSUBSET_DEF: "PSUBSET s t = (SUBSET s t & s ~= t)"
  sorry

lemma PSUBSET_TRANS: "PSUBSET x xa & PSUBSET xa xb ==> PSUBSET x xb"
  sorry

lemma PSUBSET_IRREFL: "~ PSUBSET x x"
  sorry

lemma NOT_PSUBSET_EMPTY: "~ PSUBSET x EMPTY"
  sorry

lemma NOT_UNIV_PSUBSET: "~ PSUBSET pred_set.UNIV x"
  sorry

lemma PSUBSET_UNIV: "PSUBSET x pred_set.UNIV = (EX xa. ~ IN xa x)"
  sorry

definition
  UNION :: "('a => bool) => ('a => bool) => 'a => bool"  where
  "UNION == %s t. GSPEC (%x. (x, IN x s | IN x t))"

lemma UNION_DEF: "pred_set.UNION s t = GSPEC (%x. (x, IN x s | IN x t))"
  sorry

lemma IN_UNION: "IN xb (pred_set.UNION x xa) = (IN xb x | IN xb xa)"
  sorry

lemma UNION_ASSOC: "pred_set.UNION x (pred_set.UNION xa xb) =
pred_set.UNION (pred_set.UNION x xa) xb"
  sorry

lemma UNION_IDEMPOT: "pred_set.UNION x x = x"
  sorry

lemma UNION_COMM: "pred_set.UNION x xa = pred_set.UNION xa x"
  sorry

lemma SUBSET_UNION: "(ALL (x::'a => bool) xa::'a => bool. SUBSET x (pred_set.UNION x xa)) &
(ALL (x::'a => bool) xa::'a => bool. SUBSET x (pred_set.UNION xa x))"
  sorry

lemma UNION_SUBSET: "SUBSET (pred_set.UNION s t) u = (SUBSET s u & SUBSET t u)"
  sorry

lemma SUBSET_UNION_ABSORPTION: "SUBSET x xa = (pred_set.UNION x xa = xa)"
  sorry

lemma UNION_EMPTY: "(ALL x::'a => bool. pred_set.UNION EMPTY x = x) &
(ALL x::'a => bool. pred_set.UNION x EMPTY = x)"
  sorry

lemma UNION_UNIV: "(ALL x::'a => bool. pred_set.UNION pred_set.UNIV x = pred_set.UNIV) &
(ALL x::'a => bool. pred_set.UNION x pred_set.UNIV = pred_set.UNIV)"
  sorry

lemma EMPTY_UNION: "(pred_set.UNION x xa = EMPTY) = (x = EMPTY & xa = EMPTY)"
  sorry

definition
  INTER :: "('a => bool) => ('a => bool) => 'a => bool"  where
  "INTER == %s t. GSPEC (%x. (x, IN x s & IN x t))"

lemma INTER_DEF: "pred_set.INTER s t = GSPEC (%x. (x, IN x s & IN x t))"
  sorry

lemma IN_INTER: "IN xb (pred_set.INTER x xa) = (IN xb x & IN xb xa)"
  sorry

lemma INTER_ASSOC: "pred_set.INTER x (pred_set.INTER xa xb) =
pred_set.INTER (pred_set.INTER x xa) xb"
  sorry

lemma INTER_IDEMPOT: "pred_set.INTER x x = x"
  sorry

lemma INTER_COMM: "pred_set.INTER x xa = pred_set.INTER xa x"
  sorry

lemma INTER_SUBSET: "(ALL (x::'a => bool) xa::'a => bool. SUBSET (pred_set.INTER x xa) x) &
(ALL (x::'a => bool) xa::'a => bool. SUBSET (pred_set.INTER xa x) x)"
  sorry

lemma SUBSET_INTER: "SUBSET s (pred_set.INTER t u) = (SUBSET s t & SUBSET s u)"
  sorry

lemma SUBSET_INTER_ABSORPTION: "SUBSET x xa = (pred_set.INTER x xa = x)"
  sorry

lemma INTER_EMPTY: "(ALL x::'a => bool. pred_set.INTER EMPTY x = EMPTY) &
(ALL x::'a => bool. pred_set.INTER x EMPTY = EMPTY)"
  sorry

lemma INTER_UNIV: "(ALL x::'a => bool. pred_set.INTER pred_set.UNIV x = x) &
(ALL x::'a => bool. pred_set.INTER x pred_set.UNIV = x)"
  sorry

lemma UNION_OVER_INTER: "pred_set.INTER x (pred_set.UNION xa xb) =
pred_set.UNION (pred_set.INTER x xa) (pred_set.INTER x xb)"
  sorry

lemma INTER_OVER_UNION: "pred_set.UNION x (pred_set.INTER xa xb) =
pred_set.INTER (pred_set.UNION x xa) (pred_set.UNION x xb)"
  sorry

definition
  DISJOINT :: "('a => bool) => ('a => bool) => bool"  where
  "DISJOINT == %s t. pred_set.INTER s t = EMPTY"

lemma DISJOINT_DEF: "DISJOINT s t = (pred_set.INTER s t = EMPTY)"
  sorry

lemma IN_DISJOINT: "DISJOINT x xa = (~ (EX xb. IN xb x & IN xb xa))"
  sorry

lemma DISJOINT_SYM: "DISJOINT x xa = DISJOINT xa x"
  sorry

lemma DISJOINT_EMPTY: "DISJOINT EMPTY x & DISJOINT x EMPTY"
  sorry

lemma DISJOINT_EMPTY_REFL: "(x = EMPTY) = DISJOINT x x"
  sorry

lemma DISJOINT_UNION: "DISJOINT (pred_set.UNION x xa) xb = (DISJOINT x xb & DISJOINT xa xb)"
  sorry

lemma DISJOINT_UNION_BOTH: "DISJOINT (pred_set.UNION s t) u = (DISJOINT s u & DISJOINT t u) &
DISJOINT u (pred_set.UNION s t) = (DISJOINT s u & DISJOINT t u)"
  sorry

definition
  DIFF :: "('a => bool) => ('a => bool) => 'a => bool"  where
  "DIFF == %s t. GSPEC (%x. (x, IN x s & ~ IN x t))"

lemma DIFF_DEF: "DIFF s t = GSPEC (%x. (x, IN x s & ~ IN x t))"
  sorry

lemma IN_DIFF: "IN x (DIFF s t) = (IN x s & ~ IN x t)"
  sorry

lemma DIFF_EMPTY: "DIFF s EMPTY = s"
  sorry

lemma EMPTY_DIFF: "DIFF EMPTY s = EMPTY"
  sorry

lemma DIFF_UNIV: "DIFF s pred_set.UNIV = EMPTY"
  sorry

lemma DIFF_DIFF: "DIFF (DIFF x xa) xa = DIFF x xa"
  sorry

lemma DIFF_EQ_EMPTY: "DIFF x x = EMPTY"
  sorry

definition
  INSERT :: "'a => ('a => bool) => 'a => bool"  where
  "INSERT == %x s. GSPEC (%y. (y, y = x | IN y s))"

lemma INSERT_DEF: "INSERT x s = GSPEC (%y. (y, y = x | IN y s))"
  sorry

lemma IN_INSERT: "IN x (INSERT xa xb) = (x = xa | IN x xb)"
  sorry

lemma COMPONENT: "IN x (INSERT x xa)"
  sorry

lemma SET_CASES: "x = EMPTY | (EX xa xb. x = INSERT xa xb & ~ IN xa xb)"
  sorry

lemma DECOMPOSITION: "IN x s = (EX t. s = INSERT x t & ~ IN x t)"
  sorry

lemma ABSORPTION: "IN x xa = (INSERT x xa = xa)"
  sorry

lemma INSERT_INSERT: "INSERT x (INSERT x xa) = INSERT x xa"
  sorry

lemma INSERT_COMM: "INSERT x (INSERT xa xb) = INSERT xa (INSERT x xb)"
  sorry

lemma INSERT_UNIV: "INSERT x pred_set.UNIV = pred_set.UNIV"
  sorry

lemma NOT_INSERT_EMPTY: "INSERT x xa ~= EMPTY"
  sorry

lemma NOT_EMPTY_INSERT: "EMPTY ~= INSERT x xa"
  sorry

lemma INSERT_UNION: "pred_set.UNION (INSERT x s) t =
(if IN x t then pred_set.UNION s t else INSERT x (pred_set.UNION s t))"
  sorry

lemma INSERT_UNION_EQ: "pred_set.UNION (INSERT x s) t = INSERT x (pred_set.UNION s t)"
  sorry

lemma INSERT_INTER: "pred_set.INTER (INSERT x s) t =
(if IN x t then INSERT x (pred_set.INTER s t) else pred_set.INTER s t)"
  sorry

lemma DISJOINT_INSERT: "DISJOINT (INSERT x xa) xb = (DISJOINT xa xb & ~ IN x xb)"
  sorry

lemma INSERT_SUBSET: "SUBSET (INSERT x xa) xb = (IN x xb & SUBSET xa xb)"
  sorry

lemma SUBSET_INSERT: "~ IN x xa ==> SUBSET xa (INSERT x xb) = SUBSET xa xb"
  sorry

lemma INSERT_DIFF: "DIFF (INSERT x s) t = (if IN x t then DIFF s t else INSERT x (DIFF s t))"
  sorry

definition
  DELETE :: "('a => bool) => 'a => 'a => bool"  where
  "DELETE == %s x. DIFF s (INSERT x EMPTY)"

lemma DELETE_DEF: "DELETE s x = DIFF s (INSERT x EMPTY)"
  sorry

lemma IN_DELETE: "IN xa (DELETE x xb) = (IN xa x & xa ~= xb)"
  sorry

lemma DELETE_NON_ELEMENT: "(~ IN x xa) = (DELETE xa x = xa)"
  sorry

lemma IN_DELETE_EQ: "(IN x s = IN x' s) = (IN x (DELETE s x') = IN x' (DELETE s x))"
  sorry

lemma EMPTY_DELETE: "DELETE EMPTY x = EMPTY"
  sorry

lemma DELETE_DELETE: "DELETE (DELETE xa x) x = DELETE xa x"
  sorry

lemma DELETE_COMM: "DELETE (DELETE xb x) xa = DELETE (DELETE xb xa) x"
  sorry

lemma DELETE_SUBSET: "SUBSET (DELETE xa x) xa"
  sorry

lemma SUBSET_DELETE: "SUBSET xa (DELETE xb x) = (~ IN x xa & SUBSET xa xb)"
  sorry

lemma SUBSET_INSERT_DELETE: "SUBSET s (INSERT x t) = SUBSET (DELETE s x) t"
  sorry

lemma DIFF_INSERT: "DIFF x (INSERT xb xa) = DIFF (DELETE x xb) xa"
  sorry

lemma PSUBSET_INSERT_SUBSET: "PSUBSET x xa = (EX xb. ~ IN xb x & SUBSET (INSERT xb x) xa)"
  sorry

lemma PSUBSET_MEMBER: "PSUBSET s t = (SUBSET s t & (EX y. IN y t & ~ IN y s))"
  sorry

lemma DELETE_INSERT: "DELETE (INSERT x xb) xa =
(if x = xa then DELETE xb xa else INSERT x (DELETE xb xa))"
  sorry

lemma INSERT_DELETE: "IN x xa ==> INSERT x (DELETE xa x) = xa"
  sorry

lemma DELETE_INTER: "pred_set.INTER (DELETE x xb) xa = DELETE (pred_set.INTER x xa) xb"
  sorry

lemma DISJOINT_DELETE_SYM: "DISJOINT (DELETE x xb) xa = DISJOINT (DELETE xa xb) x"
  sorry

consts
  CHOICE :: "('a => bool) => 'a" 

specification (CHOICE) CHOICE_DEF: "ALL x. x ~= EMPTY --> IN (CHOICE x) x"
  sorry

definition
  REST :: "('a => bool) => 'a => bool"  where
  "REST == %s. DELETE s (CHOICE s)"

lemma REST_DEF: "REST s = DELETE s (CHOICE s)"
  sorry

lemma CHOICE_NOT_IN_REST: "~ IN (CHOICE x) (REST x)"
  sorry

lemma CHOICE_INSERT_REST: "s ~= EMPTY ==> INSERT (CHOICE s) (REST s) = s"
  sorry

lemma REST_SUBSET: "SUBSET (REST x) x"
  sorry

lemma REST_PSUBSET: "x ~= EMPTY ==> PSUBSET (REST x) x"
  sorry

definition
  SING :: "('a => bool) => bool"  where
  "SING == %s. EX x. s = INSERT x EMPTY"

lemma SING_DEF: "SING s = (EX x. s = INSERT x EMPTY)"
  sorry

lemma SING: "SING (INSERT x EMPTY)"
  sorry

lemma IN_SING: "IN x (INSERT xa EMPTY) = (x = xa)"
  sorry

lemma NOT_SING_EMPTY: "INSERT x EMPTY ~= EMPTY"
  sorry

lemma NOT_EMPTY_SING: "EMPTY ~= INSERT x EMPTY"
  sorry

lemma EQUAL_SING: "(INSERT x EMPTY = INSERT xa EMPTY) = (x = xa)"
  sorry

lemma DISJOINT_SING_EMPTY: "DISJOINT (INSERT x EMPTY) EMPTY"
  sorry

lemma INSERT_SING_UNION: "INSERT xa x = pred_set.UNION (INSERT xa EMPTY) x"
  sorry

lemma SING_DELETE: "DELETE (INSERT x EMPTY) x = EMPTY"
  sorry

lemma DELETE_EQ_SING: "IN xa x ==> (DELETE x xa = EMPTY) = (x = INSERT xa EMPTY)"
  sorry

lemma CHOICE_SING: "CHOICE (INSERT x EMPTY) = x"
  sorry

lemma REST_SING: "REST (INSERT x EMPTY) = EMPTY"
  sorry

lemma SING_IFF_EMPTY_REST: "SING x = (x ~= EMPTY & REST x = EMPTY)"
  sorry

definition
  IMAGE :: "('a => 'b) => ('a => bool) => 'b => bool"  where
  "IMAGE == %f s. GSPEC (%x. (f x, IN x s))"

lemma IMAGE_DEF: "IMAGE (f::'a => 'b) (s::'a => bool) = GSPEC (%x::'a. (f x, IN x s))"
  sorry

lemma IN_IMAGE: "IN (x::'b) (IMAGE (xb::'a => 'b) (xa::'a => bool)) =
(EX xc::'a. x = xb xc & IN xc xa)"
  sorry

lemma IMAGE_IN: "IN x xa ==> IN (xb x) (IMAGE xb xa)"
  sorry

lemma IMAGE_EMPTY: "IMAGE (x::'a => 'b) EMPTY = EMPTY"
  sorry

lemma IMAGE_ID: "IMAGE (%x. x) x = x"
  sorry

lemma IMAGE_COMPOSE: "IMAGE ((x::'b => 'c) o (xa::'a => 'b)) (xb::'a => bool) =
IMAGE x (IMAGE xa xb)"
  sorry

lemma IMAGE_INSERT: "IMAGE (x::'a => 'b) (INSERT (xa::'a) (xb::'a => bool)) =
INSERT (x xa) (IMAGE x xb)"
  sorry

lemma IMAGE_EQ_EMPTY: "(IMAGE (x::'a => 'b) (s::'a => bool) = EMPTY) = (s = EMPTY)"
  sorry

lemma IMAGE_DELETE: "~ IN x s ==> IMAGE f (DELETE s x) = IMAGE f s"
  sorry

lemma IMAGE_UNION: "IMAGE (x::'a => 'b) (pred_set.UNION (xa::'a => bool) (xb::'a => bool)) =
pred_set.UNION (IMAGE x xa) (IMAGE x xb)"
  sorry

lemma IMAGE_SUBSET: "SUBSET x xa ==> SUBSET (IMAGE xb x) (IMAGE xb xa)"
  sorry

lemma IMAGE_INTER: "SUBSET
 (IMAGE (f::'a => 'b) (pred_set.INTER (s::'a => bool) (t::'a => bool)))
 (pred_set.INTER (IMAGE f s) (IMAGE f t))"
  sorry

definition
  INJ :: "('a => 'b) => ('a => bool) => ('b => bool) => bool"  where
  "INJ ==
%f s t.
   (ALL x. IN x s --> IN (f x) t) &
   (ALL x y. IN x s & IN y s --> f x = f y --> x = y)"

lemma INJ_DEF: "INJ f s t =
((ALL x. IN x s --> IN (f x) t) &
 (ALL x y. IN x s & IN y s --> f x = f y --> x = y))"
  sorry

lemma INJ_ID: "INJ (%x. x) x x"
  sorry

lemma INJ_COMPOSE: "INJ x xb xc & INJ xa xc xd ==> INJ (xa o x) xb xd"
  sorry

lemma INJ_EMPTY: "All (INJ (x::'a => 'b) EMPTY) &
(ALL xa::'a => bool. INJ x xa EMPTY = (xa = EMPTY))"
  sorry

definition
  SURJ :: "('a => 'b) => ('a => bool) => ('b => bool) => bool"  where
  "SURJ ==
%f s t.
   (ALL x. IN x s --> IN (f x) t) &
   (ALL x. IN x t --> (EX y. IN y s & f y = x))"

lemma SURJ_DEF: "SURJ f s t =
((ALL x. IN x s --> IN (f x) t) &
 (ALL x. IN x t --> (EX y. IN y s & f y = x)))"
  sorry

lemma SURJ_ID: "SURJ (%x. x) x x"
  sorry

lemma SURJ_COMPOSE: "SURJ x xb xc & SURJ xa xc xd ==> SURJ (xa o x) xb xd"
  sorry

lemma SURJ_EMPTY: "(ALL xa::'b => bool. SURJ (x::'a => 'b) EMPTY xa = (xa = EMPTY)) &
(ALL xa::'a => bool. SURJ x xa EMPTY = (xa = EMPTY))"
  sorry

lemma IMAGE_SURJ: "SURJ x xa xb = (IMAGE x xa = xb)"
  sorry

definition
  BIJ :: "('a => 'b) => ('a => bool) => ('b => bool) => bool"  where
  "BIJ == %f s t. INJ f s t & SURJ f s t"

lemma BIJ_DEF: "BIJ f s t = (INJ f s t & SURJ f s t)"
  sorry

lemma BIJ_ID: "BIJ (%x. x) x x"
  sorry

lemma BIJ_EMPTY: "(ALL xa::'b => bool. BIJ (x::'a => 'b) EMPTY xa = (xa = EMPTY)) &
(ALL xa::'a => bool. BIJ x xa EMPTY = (xa = EMPTY))"
  sorry

lemma BIJ_COMPOSE: "BIJ x xb xc & BIJ xa xc xd ==> BIJ (xa o x) xb xd"
  sorry

consts
  LINV :: "('a => 'b) => ('a => bool) => 'b => 'a" 

specification (LINV) LINV_DEF: "ALL f s t. INJ f s t --> (ALL x. IN x s --> LINV f s (f x) = x)"
  sorry

consts
  RINV :: "('a => 'b) => ('a => bool) => 'b => 'a" 

specification (RINV) RINV_DEF: "ALL f s t. SURJ f s t --> (ALL x. IN x t --> f (RINV f s x) = x)"
  sorry

definition
  FINITE :: "('a => bool) => bool"  where
  "FINITE ==
%s. ALL P. P EMPTY & (ALL s. P s --> (ALL e. P (INSERT e s))) --> P s"

lemma FINITE_DEF: "FINITE s =
(ALL P. P EMPTY & (ALL s. P s --> (ALL e. P (INSERT e s))) --> P s)"
  sorry

lemma FINITE_EMPTY: "FINITE EMPTY"
  sorry

lemma FINITE_INDUCT: "[| P EMPTY &
   (ALL s. FINITE s & P s --> (ALL e. ~ IN e s --> P (INSERT e s)));
   FINITE s |]
==> P s"
  sorry

lemma FINITE_INSERT: "FINITE (INSERT x s) = FINITE s"
  sorry

lemma FINITE_DELETE: "FINITE (DELETE s x) = FINITE s"
  sorry

lemma FINITE_UNION: "FINITE (pred_set.UNION s t) = (FINITE s & FINITE t)"
  sorry

lemma INTER_FINITE: "FINITE s ==> FINITE (pred_set.INTER s t)"
  sorry

lemma SUBSET_FINITE: "[| FINITE s; SUBSET t s |] ==> FINITE t"
  sorry

lemma PSUBSET_FINITE: "[| FINITE x; PSUBSET xa x |] ==> FINITE xa"
  sorry

lemma FINITE_DIFF: "FINITE s ==> FINITE (DIFF s t)"
  sorry

lemma FINITE_SING: "FINITE (INSERT x EMPTY)"
  sorry

lemma SING_FINITE: "SING x ==> FINITE x"
  sorry

lemma IMAGE_FINITE: "FINITE s ==> FINITE (IMAGE f s)"
  sorry

consts
  CARD :: "('a => bool) => nat" 

specification (CARD) CARD_DEF: "(op &::bool => bool => bool)
 ((op =::nat => nat => bool)
   ((CARD::('a::type => bool) => nat) (EMPTY::'a::type => bool)) (0::nat))
 ((All::(('a::type => bool) => bool) => bool)
   (%s::'a::type => bool.
       (op -->::bool => bool => bool)
        ((FINITE::('a::type => bool) => bool) s)
        ((All::('a::type => bool) => bool)
          (%x::'a::type.
              (op =::nat => nat => bool)
               ((CARD::('a::type => bool) => nat)
                 ((INSERT::'a::type
                           => ('a::type => bool) => 'a::type => bool)
                   x s))
               ((If::bool => nat => nat => nat)
                 ((IN::'a::type => ('a::type => bool) => bool) x s)
                 ((CARD::('a::type => bool) => nat) s)
                 ((Suc::nat => nat)
                   ((CARD::('a::type => bool) => nat) s)))))))"
  sorry

lemma CARD_EMPTY: "CARD EMPTY = 0"
  sorry

lemma CARD_INSERT: "FINITE s ==> CARD (INSERT x s) = (if IN x s then CARD s else Suc (CARD s))"
  sorry

lemma CARD_EQ_0: "FINITE s ==> (CARD s = 0) = (s = EMPTY)"
  sorry

lemma CARD_DELETE: "FINITE s ==> CARD (DELETE s x) = (if IN x s then CARD s - 1 else CARD s)"
  sorry

lemma CARD_INTER_LESS_EQ: "FINITE s ==> CARD (pred_set.INTER s t) <= CARD s"
  sorry

lemma CARD_UNION: "[| FINITE s; FINITE t |]
==> CARD (pred_set.UNION s t) + CARD (pred_set.INTER s t) = CARD s + CARD t"
  sorry

lemma CARD_SUBSET: "[| FINITE s; SUBSET t s |] ==> CARD t <= CARD s"
  sorry

lemma CARD_PSUBSET: "[| FINITE s; PSUBSET t s |] ==> CARD t < CARD s"
  sorry

lemma CARD_SING: "CARD (INSERT x EMPTY) = 1"
  sorry

lemma SING_IFF_CARD1: "SING x = (CARD x = 1 & FINITE x)"
  sorry

lemma CARD_DIFF: "[| FINITE t; FINITE s |]
==> CARD (DIFF s t) = CARD s - CARD (pred_set.INTER s t)"
  sorry

lemma LESS_CARD_DIFF: "[| FINITE t; FINITE s; CARD t < CARD s |] ==> 0 < CARD (DIFF s t)"
  sorry

lemma FINITE_COMPLETE_INDUCTION: "[| !!x. [| !!y. PSUBSET y x ==> P y; FINITE x |] ==> P x; FINITE x |]
==> P x"
  sorry

definition
  INFINITE :: "('a => bool) => bool"  where
  "INFINITE == %s. ~ FINITE s"

lemma INFINITE_DEF: "INFINITE s = (~ FINITE s)"
  sorry

lemma NOT_IN_FINITE: "(op =::bool => bool => bool)
 ((INFINITE::('a::type => bool) => bool) (pred_set.UNIV::'a::type => bool))
 ((All::(('a::type => bool) => bool) => bool)
   (%s::'a::type => bool.
       (op -->::bool => bool => bool)
        ((FINITE::('a::type => bool) => bool) s)
        ((Ex::('a::type => bool) => bool)
          (%x::'a::type.
              (Not::bool => bool)
               ((IN::'a::type => ('a::type => bool) => bool) x s)))))"
  sorry

lemma INFINITE_INHAB: "INFINITE x ==> EX xa. IN xa x"
  sorry

lemma IMAGE_11_INFINITE: "[| !!x y. f x = f y ==> x = y; INFINITE s |] ==> INFINITE (IMAGE f s)"
  sorry

lemma INFINITE_SUBSET: "[| INFINITE x; SUBSET x xa |] ==> INFINITE xa"
  sorry

lemma IN_INFINITE_NOT_FINITE: "INFINITE x & FINITE xa ==> EX xb. IN xb x & ~ IN xb xa"
  sorry

lemma INFINITE_UNIV: "(op =::bool => bool => bool)
 ((INFINITE::('a::type => bool) => bool) (pred_set.UNIV::'a::type => bool))
 ((Ex::(('a::type => 'a::type) => bool) => bool)
   (%f::'a::type => 'a::type.
       (op &::bool => bool => bool)
        ((All::('a::type => bool) => bool)
          (%x::'a::type.
              (All::('a::type => bool) => bool)
               (%y::'a::type.
                   (op -->::bool => bool => bool)
                    ((op =::'a::type => 'a::type => bool) (f x) (f y))
                    ((op =::'a::type => 'a::type => bool) x y))))
        ((Ex::('a::type => bool) => bool)
          (%y::'a::type.
              (All::('a::type => bool) => bool)
               (%x::'a::type.
                   (op ~=::'a::type => 'a::type => bool) (f x) y)))))"
  sorry

lemma FINITE_PSUBSET_INFINITE: "INFINITE x = (ALL xa. FINITE xa --> SUBSET xa x --> PSUBSET xa x)"
  sorry

lemma FINITE_PSUBSET_UNIV: "(op =::bool => bool => bool)
 ((INFINITE::('a::type => bool) => bool) (pred_set.UNIV::'a::type => bool))
 ((All::(('a::type => bool) => bool) => bool)
   (%s::'a::type => bool.
       (op -->::bool => bool => bool)
        ((FINITE::('a::type => bool) => bool) s)
        ((PSUBSET::('a::type => bool) => ('a::type => bool) => bool) s
          (pred_set.UNIV::'a::type => bool))))"
  sorry

lemma INFINITE_DIFF_FINITE: "INFINITE s & FINITE t ==> DIFF s t ~= EMPTY"
  sorry

lemma FINITE_ISO_NUM: "FINITE s
==> EX f. (ALL n m. n < CARD s & m < CARD s --> f n = f m --> n = m) &
          s = GSPEC (%n. (f n, n < CARD s))"
  sorry

lemma FINITE_WEAK_ENUMERATE: "FINITE (x::'a => bool) =
(EX (f::nat => 'a) b::nat. ALL e::'a. IN e x = (EX n<b. e = f n))"
  sorry

definition
  BIGUNION :: "(('a => bool) => bool) => 'a => bool"  where
  "BIGUNION == %P. GSPEC (%x. (x, EX p. IN p P & IN x p))"

lemma BIGUNION: "BIGUNION P = GSPEC (%x. (x, EX p. IN p P & IN x p))"
  sorry

lemma IN_BIGUNION: "IN x (BIGUNION xa) = (EX s. IN x s & IN s xa)"
  sorry

lemma BIGUNION_EMPTY: "BIGUNION EMPTY = EMPTY"
  sorry

lemma BIGUNION_SING: "BIGUNION (INSERT x EMPTY) = x"
  sorry

lemma BIGUNION_UNION: "BIGUNION (pred_set.UNION x xa) = pred_set.UNION (BIGUNION x) (BIGUNION xa)"
  sorry

lemma DISJOINT_BIGUNION: "(ALL (s::('a => bool) => bool) t::'a => bool.
    DISJOINT (BIGUNION s) t =
    (ALL s'::'a => bool. IN s' s --> DISJOINT s' t)) &
(ALL (x::('a => bool) => bool) xa::'a => bool.
    DISJOINT xa (BIGUNION x) =
    (ALL xb::'a => bool. IN xb x --> DISJOINT xa xb))"
  sorry

lemma BIGUNION_INSERT: "BIGUNION (INSERT x xa) = pred_set.UNION x (BIGUNION xa)"
  sorry

lemma BIGUNION_SUBSET: "SUBSET (BIGUNION P) X = (ALL Y. IN Y P --> SUBSET Y X)"
  sorry

lemma FINITE_BIGUNION: "FINITE x & (ALL s. IN s x --> FINITE s) ==> FINITE (BIGUNION x)"
  sorry

definition
  BIGINTER :: "(('a => bool) => bool) => 'a => bool"  where
  "BIGINTER == %B. GSPEC (%x. (x, ALL P. IN P B --> IN x P))"

lemma BIGINTER: "BIGINTER B = GSPEC (%x. (x, ALL P. IN P B --> IN x P))"
  sorry

lemma IN_BIGINTER: "IN x (BIGINTER B) = (ALL P. IN P B --> IN x P)"
  sorry

lemma BIGINTER_INSERT: "BIGINTER (INSERT P B) = pred_set.INTER P (BIGINTER B)"
  sorry

lemma BIGINTER_EMPTY: "BIGINTER EMPTY = pred_set.UNIV"
  sorry

lemma BIGINTER_INTER: "BIGINTER (INSERT x (INSERT xa EMPTY)) = pred_set.INTER x xa"
  sorry

lemma BIGINTER_SING: "BIGINTER (INSERT x EMPTY) = x"
  sorry

lemma SUBSET_BIGINTER: "SUBSET X (BIGINTER P) = (ALL x. IN x P --> SUBSET X x)"
  sorry

lemma DISJOINT_BIGINTER: "IN xa xb & DISJOINT xa x
==> DISJOINT x (BIGINTER xb) & DISJOINT (BIGINTER xb) x"
  sorry

definition
  CROSS :: "('a => bool) => ('b => bool) => 'a * 'b => bool"  where
  "CROSS == %P Q. GSPEC (%p. (p, IN (fst p) P & IN (snd p) Q))"

lemma CROSS_DEF: "CROSS P Q = GSPEC (%p. (p, IN (fst p) P & IN (snd p) Q))"
  sorry

lemma IN_CROSS: "IN xb (CROSS x xa) = (IN (fst xb) x & IN (snd xb) xa)"
  sorry

lemma CROSS_EMPTY: "CROSS x EMPTY = EMPTY & CROSS EMPTY x = EMPTY"
  sorry

lemma CROSS_INSERT_LEFT: "CROSS (INSERT xb x) xa =
pred_set.UNION (CROSS (INSERT xb EMPTY) xa) (CROSS x xa)"
  sorry

lemma CROSS_INSERT_RIGHT: "CROSS x (INSERT xb xa) =
pred_set.UNION (CROSS x (INSERT xb EMPTY)) (CROSS x xa)"
  sorry

lemma FINITE_CROSS: "FINITE x & FINITE xa ==> FINITE (CROSS x xa)"
  sorry

lemma CROSS_SINGS: "CROSS (INSERT x EMPTY) (INSERT xa EMPTY) = INSERT (x, xa) EMPTY"
  sorry

lemma CARD_SING_CROSS: "FINITE (s::'b => bool) ==> CARD (CROSS (INSERT (x::'a) EMPTY) s) = CARD s"
  sorry

lemma CARD_CROSS: "FINITE x & FINITE xa ==> CARD (CROSS x xa) = CARD x * CARD xa"
  sorry

lemma CROSS_SUBSET: "SUBSET (CROSS xb xc) (CROSS x xa) =
(xb = EMPTY | xc = EMPTY | SUBSET xb x & SUBSET xc xa)"
  sorry

lemma FINITE_CROSS_EQ: "FINITE (CROSS P Q) = (P = EMPTY | Q = EMPTY | FINITE P & FINITE Q)"
  sorry

definition
  COMPL :: "('a => bool) => 'a => bool"  where
  "COMPL == DIFF pred_set.UNIV"

lemma COMPL_DEF: "COMPL P = DIFF pred_set.UNIV P"
  sorry

lemma IN_COMPL: "IN x (COMPL xa) = (~ IN x xa)"
  sorry

lemma COMPL_COMPL: "COMPL (COMPL x) = x"
  sorry

lemma COMPL_CLAUSES: "pred_set.INTER (COMPL x) x = EMPTY &
pred_set.UNION (COMPL x) x = pred_set.UNIV"
  sorry

lemma COMPL_SPLITS: "pred_set.UNION (pred_set.INTER x xa) (pred_set.INTER (COMPL x) xa) = xa"
  sorry

lemma INTER_UNION_COMPL: "pred_set.INTER x xa = COMPL (pred_set.UNION (COMPL x) (COMPL xa))"
  sorry

lemma COMPL_EMPTY: "COMPL EMPTY = pred_set.UNIV"
  sorry

consts
  count :: "nat => nat => bool" 

defs
  count_primdef: "count == %n. GSPEC (%m. (m, m < n))"

lemma count_def: "count n = GSPEC (%m. (m, m < n))"
  sorry

lemma IN_COUNT: "IN m (count n) = (m < n)"
  sorry

lemma COUNT_ZERO: "count 0 = EMPTY"
  sorry

lemma COUNT_SUC: "count (Suc n) = INSERT n (count n)"
  sorry

lemma FINITE_COUNT: "FINITE (count n)"
  sorry

lemma CARD_COUNT: "CARD (count n) = n"
  sorry

definition
  ITSET_tupled :: "('a => 'b => 'b) => ('a => bool) * 'b => 'b"  where
  "ITSET_tupled ==
%f. WFREC
     (SOME R.
         WF R &
         (ALL b s.
             FINITE s & s ~= EMPTY --> R (REST s, f (CHOICE s) b) (s, b)))
     (%ITSET_tupled (v, v1).
         if FINITE v
         then if v = EMPTY then v1
              else ITSET_tupled (REST v, f (CHOICE v) v1)
         else ARB)"

lemma ITSET_tupled_primitive_def: "ITSET_tupled f =
WFREC
 (SOME R.
     WF R &
     (ALL b s. FINITE s & s ~= EMPTY --> R (REST s, f (CHOICE s) b) (s, b)))
 (%ITSET_tupled (v, v1).
     if FINITE v
     then if v = EMPTY then v1 else ITSET_tupled (REST v, f (CHOICE v) v1)
     else ARB)"
  sorry

definition
  ITSET :: "('a => 'b => 'b) => ('a => bool) => 'b => 'b"  where
  "ITSET == %f x x1. ITSET_tupled f (x, x1)"

lemma ITSET_curried_def: "ITSET (f::'a => 'b => 'b) (x::'a => bool) (x1::'b) = ITSET_tupled f (x, x1)"
  sorry

lemma ITSET_IND: "(!!(s::'a => bool) b::'b.
    (FINITE s & s ~= EMPTY
     ==> (P::('a => bool) => 'b => bool) (REST s)
          ((f::'a => 'b => 'b) (CHOICE s) b))
    ==> P s b)
==> P (v::'a => bool) (x::'b)"
  sorry

lemma ITSET_THM: "FINITE s
==> ITSET f s b =
    (if s = EMPTY then b else ITSET f (REST s) (f (CHOICE s) b))"
  sorry

lemma ITSET_EMPTY: "ITSET (x::'a => 'b => 'b) EMPTY (xa::'b) = xa"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" operator

definition
  ASSOC :: "('a => 'a => 'a) => bool"  where
  "ASSOC == %f. ALL x y z. f x (f y z) = f (f x y) z"

lemma ASSOC_DEF: "ASSOC f = (ALL x y z. f x (f y z) = f (f x y) z)"
  sorry

definition
  COMM :: "('a => 'a => 'b) => bool"  where
  "COMM == %f. ALL x y. f x y = f y x"

lemma COMM_DEF: "COMM f = (ALL x y. f x y = f y x)"
  sorry

definition
  FCOMM :: "('a => 'b => 'a) => ('c => 'a => 'a) => bool"  where
  "FCOMM == %f g. ALL x y z. g x (f y z) = f (g x y) z"

lemma FCOMM_DEF: "FCOMM f g = (ALL x y z. g x (f y z) = f (g x y) z)"
  sorry

definition
  RIGHT_ID :: "('a => 'b => 'a) => 'b => bool"  where
  "RIGHT_ID == %f e. ALL x. f x e = x"

lemma RIGHT_ID_DEF: "RIGHT_ID f e = (ALL x. f x e = x)"
  sorry

definition
  LEFT_ID :: "('a => 'b => 'b) => 'a => bool"  where
  "LEFT_ID == %f e. ALL x. f e x = x"

lemma LEFT_ID_DEF: "LEFT_ID f e = (ALL x. f e x = x)"
  sorry

definition
  MONOID :: "('a => 'a => 'a) => 'a => bool"  where
  "MONOID == %f e. ASSOC f & RIGHT_ID f e & LEFT_ID f e"

lemma MONOID_DEF: "MONOID f e = (ASSOC f & RIGHT_ID f e & LEFT_ID f e)"
  sorry

lemma ASSOC_CONJ: "ASSOC op &"
  sorry

lemma ASSOC_DISJ: "ASSOC op |"
  sorry

lemma FCOMM_ASSOC: "FCOMM x x = ASSOC x"
  sorry

lemma MONOID_CONJ_T: "MONOID op & True"
  sorry

lemma MONOID_DISJ_F: "MONOID op | False"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" rich_list

consts
  SNOC :: "'a => 'a list => 'a list" 

specification (SNOC) SNOC: "(ALL x::'a. SNOC x [] = [x]) &
(ALL (x::'a) (x'::'a) l::'a list. SNOC x (x' # l) = x' # SNOC x l)"
  sorry

consts
  SCANL :: "('b => 'a => 'b) => 'b => 'a list => 'b list" 

specification (SCANL) SCANL: "(ALL (f::'b => 'a => 'b) e::'b. SCANL f e [] = [e]) &
(ALL (f::'b => 'a => 'b) (e::'b) (x::'a) l::'a list.
    SCANL f e (x # l) = e # SCANL f (f e x) l)"
  sorry

consts
  SCANR :: "('a => 'b => 'b) => 'b => 'a list => 'b list" 

specification (SCANR) SCANR: "(ALL (f::'a => 'b => 'b) e::'b. SCANR f e [] = [e]) &
(ALL (f::'a => 'b => 'b) (e::'b) (x::'a) l::'a list.
    SCANR f e (x # l) = f x (hd (SCANR f e l)) # SCANR f e l)"
  sorry

lemma IS_EL_DEF: "List.member l x = list_ex (op = x) l"
  sorry

definition
  AND_EL :: "bool list => bool"  where
  "AND_EL == list_all I"

lemma AND_EL_DEF: "AND_EL = list_all I"
  sorry

definition
  OR_EL :: "bool list => bool"  where
  "OR_EL == list_ex I"

lemma OR_EL_DEF: "OR_EL = list_ex I"
  sorry

consts
  FIRSTN :: "nat => 'a list => 'a list" 

specification (FIRSTN) FIRSTN: "(ALL l::'a list. FIRSTN (0::nat) l = []) &
(ALL (n::nat) (x::'a) l::'a list. FIRSTN (Suc n) (x # l) = x # FIRSTN n l)"
  sorry

consts
  BUTFIRSTN :: "nat => 'a list => 'a list" 

specification (BUTFIRSTN) BUTFIRSTN: "(ALL l::'a list. BUTFIRSTN (0::nat) l = l) &
(ALL (n::nat) (x::'a) l::'a list. BUTFIRSTN (Suc n) (x # l) = BUTFIRSTN n l)"
  sorry

consts
  SEG :: "nat => nat => 'a list => 'a list" 

specification (SEG) SEG: "(ALL (k::nat) l::'a list. SEG (0::nat) k l = []) &
(ALL (m::nat) (x::'a) l::'a list.
    SEG (Suc m) (0::nat) (x # l) = x # SEG m (0::nat) l) &
(ALL (m::nat) (k::nat) (x::'a) l::'a list.
    SEG (Suc m) (Suc k) (x # l) = SEG (Suc m) k l)"
  sorry

lemma LAST: "last (SNOC x l) = x"
  sorry

lemma BUTLAST: "butlast (SNOC x l) = l"
  sorry

consts
  LASTN :: "nat => 'a list => 'a list" 

specification (LASTN) LASTN: "(ALL l::'a list. LASTN (0::nat) l = []) &
(ALL (n::nat) (x::'a) l::'a list.
    LASTN (Suc n) (SNOC x l) = SNOC x (LASTN n l))"
  sorry

consts
  BUTLASTN :: "nat => 'a list => 'a list" 

specification (BUTLASTN) BUTLASTN: "(ALL l::'a list. BUTLASTN (0::nat) l = l) &
(ALL (n::nat) (x::'a) l::'a list.
    BUTLASTN (Suc n) (SNOC x l) = BUTLASTN n l)"
  sorry

lemma EL: "(ALL x::'a list. EL (0::nat) x = hd x) &
(ALL (x::nat) xa::'a list. EL (Suc x) xa = EL x (tl xa))"
  sorry

consts
  ELL :: "nat => 'a list => 'a" 

specification (ELL) ELL: "(ALL l::'a list. ELL (0::nat) l = last l) &
(ALL (n::nat) l::'a list. ELL (Suc n) l = ELL n (butlast l))"
  sorry

consts
  IS_PREFIX :: "'a list => 'a list => bool" 

specification (IS_PREFIX) IS_PREFIX: "(ALL l::'a list. IS_PREFIX l [] = True) &
(ALL (x::'a) l::'a list. IS_PREFIX [] (x # l) = False) &
(ALL (x1::'a) (l1::'a list) (x2::'a) l2::'a list.
    IS_PREFIX (x1 # l1) (x2 # l2) = (x1 = x2 & IS_PREFIX l1 l2))"
  sorry

lemma SNOC_APPEND: "SNOC x l = l @ [x]"
  sorry

lemma REVERSE: "rev [] = [] & (ALL (x::'a) xa::'a list. rev (x # xa) = SNOC x (rev xa))"
  sorry

lemma REVERSE_SNOC: "rev (SNOC x l) = x # rev l"
  sorry

lemma SNOC_Axiom: "EX x. x [] = e & (ALL xa l. x (SNOC xa l) = f xa l (x l))"
  sorry

consts
  IS_SUFFIX :: "'a list => 'a list => bool" 

specification (IS_SUFFIX) IS_SUFFIX: "(ALL l::'a list. IS_SUFFIX l [] = True) &
(ALL (x::'a) l::'a list. IS_SUFFIX [] (SNOC x l) = False) &
(ALL (x1::'a) (l1::'a list) (x2::'a) l2::'a list.
    IS_SUFFIX (SNOC x1 l1) (SNOC x2 l2) = (x1 = x2 & IS_SUFFIX l1 l2))"
  sorry

consts
  IS_SUBLIST :: "'a list => 'a list => bool" 

specification (IS_SUBLIST) IS_SUBLIST: "(ALL l::'a list. IS_SUBLIST l [] = True) &
(ALL (x::'a) l::'a list. IS_SUBLIST [] (x # l) = False) &
(ALL (x1::'a) (l1::'a list) (x2::'a) l2::'a list.
    IS_SUBLIST (x1 # l1) (x2 # l2) =
    (x1 = x2 & IS_PREFIX l1 l2 | IS_SUBLIST l1 (x2 # l2)))"
  sorry

consts
  SPLITP :: "('a => bool) => 'a list => 'a list * 'a list" 

specification (SPLITP) SPLITP: "(ALL P::'a => bool. SPLITP P [] = ([], [])) &
(ALL (P::'a => bool) (x::'a) l::'a list.
    SPLITP P (x # l) =
    (if P x then ([], x # l) else (x # fst (SPLITP P l), snd (SPLITP P l))))"
  sorry

definition
  PREFIX :: "('a => bool) => 'a list => 'a list"  where
  "PREFIX == %P l. fst (SPLITP (Not o P) l)"

lemma PREFIX_DEF: "PREFIX P l = fst (SPLITP (Not o P) l)"
  sorry

definition
  SUFFIX :: "('a => bool) => 'a list => 'a list"  where
  "SUFFIX == %P. foldl (%l' x. if P x then SNOC x l' else []) []"

lemma SUFFIX_DEF: "SUFFIX P l = foldl (%l' x. if P x then SNOC x l' else []) [] l"
  sorry

definition
  UNZIP_FST :: "('a * 'b) list => 'a list"  where
  "UNZIP_FST == %l. fst (unzip l)"

lemma UNZIP_FST_DEF: "UNZIP_FST l = fst (unzip l)"
  sorry

definition
  UNZIP_SND :: "('a * 'b) list => 'b list"  where
  "UNZIP_SND == %l. snd (unzip l)"

lemma UNZIP_SND_DEF: "UNZIP_SND (l::('a * 'b) list) = snd (unzip l)"
  sorry

consts
  GENLIST :: "(nat => 'a) => nat => 'a list" 

specification (GENLIST) GENLIST: "(ALL f::nat => 'a. GENLIST f (0::nat) = []) &
(ALL (f::nat => 'a) n::nat. GENLIST f (Suc n) = SNOC (f n) (GENLIST f n))"
  sorry

consts
  REPLICATE :: "nat => 'a => 'a list" 

specification (REPLICATE) REPLICATE: "(ALL x::'a. REPLICATE (0::nat) x = []) &
(ALL (n::nat) x::'a. REPLICATE (Suc n) x = x # REPLICATE n x)"
  sorry

lemma LENGTH_MAP2: "length l1 = length l2
==> length (map2 f l1 l2) = length l1 & length (map2 f l1 l2) = length l2"
  sorry

lemma LENGTH_EQ: "x = y ==> length x = length y"
  sorry

lemma LENGTH_NOT_NULL: "(0 < length l) = (~ List.null l)"
  sorry

lemma SNOC_INDUCT: "P [] & (ALL l. P l --> (ALL x. P (SNOC x l))) ==> P x"
  sorry

lemma SNOC_CASES: "x' = [] | (EX x l. x' = SNOC x l)"
  sorry

lemma LENGTH_SNOC: "length (SNOC x l) = Suc (length l)"
  sorry

lemma NOT_NIL_SNOC: "[] ~= SNOC x xa"
  sorry

lemma NOT_SNOC_NIL: "SNOC x xa ~= []"
  sorry

lemma SNOC_11: "(SNOC x l = SNOC x' l') = (x = x' & l = l')"
  sorry

lemma SNOC_EQ_LENGTH_EQ: "SNOC x1 l1 = SNOC x2 l2 ==> length l1 = length l2"
  sorry

lemma SNOC_REVERSE_CONS: "SNOC x xa = rev (x # rev xa)"
  sorry

lemma MAP_SNOC: "map (x::'a => 'b) (SNOC (xa::'a) (xb::'a list)) = SNOC (x xa) (map x xb)"
  sorry

lemma FOLDR_SNOC: "foldr (f::'a => 'b => 'b) (SNOC (x::'a) (l::'a list)) (e::'b) =
foldr f l (f x e)"
  sorry

lemma FOLDL_SNOC: "foldl (f::'b => 'a => 'b) (e::'b) (SNOC (x::'a) (l::'a list)) =
f (foldl f e l) x"
  sorry

lemma FOLDR_FOLDL: "MONOID f e ==> foldr f l e = foldl f e l"
  sorry

lemma LENGTH_FOLDR: "length l = foldr (%x. Suc) l 0"
  sorry

lemma LENGTH_FOLDL: "length l = foldl (%l' x. Suc l') 0 l"
  sorry

lemma MAP_FOLDR: "map (f::'a => 'b) (l::'a list) = foldr (%x::'a. op # (f x)) l []"
  sorry

lemma MAP_FOLDL: "map (f::'a => 'b) (l::'a list) =
foldl (%(l'::'b list) x::'a. SNOC (f x) l') [] l"
  sorry

lemma FILTER_FOLDR: "filter P l = foldr (%x l'. if P x then x # l' else l') l []"
  sorry

lemma FILTER_SNOC: "filter P (SNOC x l) = (if P x then SNOC x (filter P l) else filter P l)"
  sorry

lemma FILTER_FOLDL: "filter P l = foldl (%l' x. if P x then SNOC x l' else l') [] l"
  sorry

lemma FILTER_COMM: "filter f1 (filter f2 l) = filter f2 (filter f1 l)"
  sorry

lemma FILTER_IDEM: "filter f (filter f l) = filter f l"
  sorry

lemma LENGTH_SEG: "n + k <= length l ==> length (SEG n k l) = n"
  sorry

lemma APPEND_NIL: "(ALL l::'a list. l @ [] = l) & (ALL x::'a list. [] @ x = x)"
  sorry

lemma APPEND_SNOC: "l1 @ SNOC x l2 = SNOC x (l1 @ l2)"
  sorry

lemma APPEND_FOLDR: "l1 @ l2 = foldr op # l1 l2"
  sorry

lemma APPEND_FOLDL: "l1 @ l2 = foldl (%l' x. SNOC x l') l1 l2"
  sorry

lemma CONS_APPEND: "x # l = [x] @ l"
  sorry

lemma ASSOC_APPEND: "ASSOC op @"
  sorry

lemma MONOID_APPEND_NIL: "MONOID op @ []"
  sorry

lemma APPEND_LENGTH_EQ: "[| length l1 = length l1'; length l2 = length l2' |]
==> (l1 @ l2 = l1' @ l2') = (l1 = l1' & l2 = l2')"
  sorry

lemma FLAT_SNOC: "concat (SNOC x l) = concat l @ x"
  sorry

lemma FLAT_FOLDR: "concat l = foldr op @ l []"
  sorry

lemma LENGTH_FLAT: "length (concat l) = HOL4Compat.sum (map length l)"
  sorry

lemma REVERSE_FOLDR: "rev l = foldr SNOC l []"
  sorry

lemma ALL_EL_SNOC: "list_all P (SNOC x l) = (list_all P l & P x)"
  sorry

lemma ALL_EL_MAP: "list_all (P::'b => bool) (map (f::'a => 'b) (l::'a list)) =
list_all (P o f) l"
  sorry

lemma SOME_EL_SNOC: "list_ex P (SNOC x l) = (P x | list_ex P l)"
  sorry

lemma IS_EL_SNOC: "List.member (SNOC x l) y = (y = x | List.member l y)"
  sorry

lemma SUM_SNOC: "HOL4Compat.sum (SNOC x l) = HOL4Compat.sum l + x"
  sorry

lemma SUM_FOLDL: "HOL4Compat.sum l = foldl op + 0 l"
  sorry

lemma IS_PREFIX_APPEND: "IS_PREFIX l1 l2 = (EX l. l1 = l2 @ l)"
  sorry

lemma IS_SUFFIX_APPEND: "IS_SUFFIX l1 l2 = (EX l. l1 = l @ l2)"
  sorry

lemma IS_SUBLIST_APPEND: "IS_SUBLIST l1 l2 = (EX l l'. l1 = l @ l2 @ l')"
  sorry

lemma IS_PREFIX_IS_SUBLIST: "IS_PREFIX l1 l2 ==> IS_SUBLIST l1 l2"
  sorry

lemma IS_SUFFIX_IS_SUBLIST: "IS_SUFFIX l1 l2 ==> IS_SUBLIST l1 l2"
  sorry

lemma IS_PREFIX_REVERSE: "IS_PREFIX (rev l1) (rev l2) = IS_SUFFIX l1 l2"
  sorry

lemma IS_SUFFIX_REVERSE: "IS_SUFFIX (rev l1) (rev l2) = IS_PREFIX l1 l2"
  sorry

lemma IS_SUBLIST_REVERSE: "IS_SUBLIST (rev l1) (rev l2) = IS_SUBLIST l1 l2"
  sorry

lemma PREFIX_FOLDR: "PREFIX P x = foldr (%x l'. if P x then x # l' else []) x []"
  sorry

lemma PREFIX: "(ALL x::'a => bool. PREFIX x [] = []) &
(ALL (x::'a => bool) (xa::'a) xb::'a list.
    PREFIX x (xa # xb) = (if x xa then xa # PREFIX x xb else []))"
  sorry

lemma IS_PREFIX_PREFIX: "IS_PREFIX l (PREFIX P l)"
  sorry

lemma LENGTH_SCANL: "length (SCANL (f::'b => 'a => 'b) (e::'b) (l::'a list)) = Suc (length l)"
  sorry

lemma LENGTH_SCANR: "length (SCANR (f::'a => 'b => 'b) (e::'b) (l::'a list)) = Suc (length l)"
  sorry

lemma COMM_MONOID_FOLDL: "[| COMM x; MONOID x xa |] ==> foldl x e l = x e (foldl x xa l)"
  sorry

lemma COMM_MONOID_FOLDR: "[| COMM x; MONOID x xa |] ==> foldr x l e = x e (foldr x l xa)"
  sorry

lemma FCOMM_FOLDR_APPEND: "[| FCOMM x xa; LEFT_ID x xb |]
==> foldr xa (l1 @ l2) xb = x (foldr xa l1 xb) (foldr xa l2 xb)"
  sorry

lemma FCOMM_FOLDL_APPEND: "[| FCOMM x xa; RIGHT_ID xa xb |]
==> foldl x xb (l1 @ l2) = xa (foldl x xb l1) (foldl x xb l2)"
  sorry

lemma FOLDL_SINGLE: "foldl x xa [xb] = x xa xb"
  sorry

lemma FOLDR_SINGLE: "foldr (x::'a => 'b => 'b) [xb::'a] (xa::'b) = x xb xa"
  sorry

lemma FOLDR_CONS_NIL: "foldr op # l [] = l"
  sorry

lemma FOLDL_SNOC_NIL: "foldl (%xs x. SNOC x xs) [] l = l"
  sorry

lemma FOLDR_REVERSE: "foldr (x::'a => 'b => 'b) (rev (xb::'a list)) (xa::'b) =
foldl (%(xa::'b) y::'a. x y xa) xa xb"
  sorry

lemma FOLDL_REVERSE: "foldl x xa (rev xb) = foldr (%xa y. x y xa) xb xa"
  sorry

lemma FOLDR_MAP: "foldr (f::'a => 'a => 'a) (map (g::'b => 'a) (l::'b list)) (e::'a) =
foldr (%x::'b. f (g x)) l e"
  sorry

lemma ALL_EL_FOLDR: "list_all P l = foldr (%x. op & (P x)) l True"
  sorry

lemma ALL_EL_FOLDL: "list_all P l = foldl (%l' x. l' & P x) True l"
  sorry

lemma SOME_EL_FOLDR: "list_ex P l = foldr (%x. op | (P x)) l False"
  sorry

lemma SOME_EL_FOLDL: "list_ex P l = foldl (%l' x. l' | P x) False l"
  sorry

lemma ALL_EL_FOLDR_MAP: "list_all x xa = foldr op & (map x xa) True"
  sorry

lemma ALL_EL_FOLDL_MAP: "list_all x xa = foldl op & True (map x xa)"
  sorry

lemma SOME_EL_FOLDR_MAP: "list_ex x xa = foldr op | (map x xa) False"
  sorry

lemma SOME_EL_FOLDL_MAP: "list_ex x xa = foldl op | False (map x xa)"
  sorry

lemma FOLDR_FILTER: "foldr (f::'a => 'a => 'a) (filter (P::'a => bool) (l::'a list)) (e::'a) =
foldr (%(x::'a) y::'a. if P x then f x y else y) l e"
  sorry

lemma FOLDL_FILTER: "foldl (f::'a => 'a => 'a) (e::'a) (filter (P::'a => bool) (l::'a list)) =
foldl (%(x::'a) y::'a. if P y then f x y else x) e l"
  sorry

lemma ASSOC_FOLDR_FLAT: "[| ASSOC f; LEFT_ID f e |]
==> foldr f (concat l) e = foldr f (map (FOLDR f e) l) e"
  sorry

lemma ASSOC_FOLDL_FLAT: "[| ASSOC f; RIGHT_ID f e |]
==> foldl f e (concat l) = foldl f e (map (foldl f e) l)"
  sorry

lemma SOME_EL_MAP: "list_ex (P::'b => bool) (map (f::'a => 'b) (l::'a list)) = list_ex (P o f) l"
  sorry

lemma SOME_EL_DISJ: "list_ex (%x. P x | Q x) l = (list_ex P l | list_ex Q l)"
  sorry

lemma IS_EL_FOLDR: "List.member xa x = foldr (%xa. op | (x = xa)) xa False"
  sorry

lemma IS_EL_FOLDL: "List.member xa x = foldl (%l' xa. l' | x = xa) False xa"
  sorry

lemma NULL_FOLDR: "List.null l = foldr (%x l'. False) l True"
  sorry

lemma NULL_FOLDL: "List.null l = foldl (%x l'. False) True l"
  sorry

lemma SEG_LENGTH_ID: "SEG (length l) 0 l = l"
  sorry

lemma SEG_SUC_CONS: "SEG m (Suc n) (x # l) = SEG m n l"
  sorry

lemma SEG_0_SNOC: "m <= length l ==> SEG m 0 (SNOC x l) = SEG m 0 l"
  sorry

lemma BUTLASTN_SEG: "n <= length l ==> BUTLASTN n l = SEG (length l - n) 0 l"
  sorry

lemma LASTN_CONS: "n <= length l ==> LASTN n (x # l) = LASTN n l"
  sorry

lemma LENGTH_LASTN: "n <= length l ==> length (LASTN n l) = n"
  sorry

lemma LASTN_LENGTH_ID: "LASTN (length l) l = l"
  sorry

lemma LASTN_LASTN: "[| m <= length l; n <= m |] ==> LASTN n (LASTN m l) = LASTN n l"
  sorry

lemma FIRSTN_LENGTH_ID: "FIRSTN (length l) l = l"
  sorry

lemma FIRSTN_SNOC: "n <= length l ==> FIRSTN n (SNOC x l) = FIRSTN n l"
  sorry

lemma BUTLASTN_LENGTH_NIL: "BUTLASTN (length l) l = []"
  sorry

lemma BUTLASTN_SUC_BUTLAST: "n < length l ==> BUTLASTN (Suc n) l = BUTLASTN n (butlast l)"
  sorry

lemma BUTLASTN_BUTLAST: "n < length l ==> BUTLASTN n (butlast l) = butlast (BUTLASTN n l)"
  sorry

lemma LENGTH_BUTLASTN: "n <= length l ==> length (BUTLASTN n l) = length l - n"
  sorry

lemma BUTLASTN_BUTLASTN: "n + m <= length l ==> BUTLASTN n (BUTLASTN m l) = BUTLASTN (n + m) l"
  sorry

lemma APPEND_BUTLASTN_LASTN: "n <= length l ==> BUTLASTN n l @ LASTN n l = l"
  sorry

lemma APPEND_FIRSTN_LASTN: "m + n = length l ==> FIRSTN n l @ LASTN m l = l"
  sorry

lemma BUTLASTN_APPEND2: "n <= length l2 ==> BUTLASTN n (l1 @ l2) = l1 @ BUTLASTN n l2"
  sorry

lemma BUTLASTN_LENGTH_APPEND: "BUTLASTN (length l2) (l1 @ l2) = l1"
  sorry

lemma LASTN_LENGTH_APPEND: "LASTN (length l2) (l1 @ l2) = l2"
  sorry

lemma BUTLASTN_CONS: "n <= length l ==> BUTLASTN n (x # l) = x # BUTLASTN n l"
  sorry

lemma BUTLASTN_LENGTH_CONS: "BUTLASTN (length l) (x # l) = [x]"
  sorry

lemma LAST_LASTN_LAST: "[| n <= length l; 0 < n |] ==> last (LASTN n l) = last l"
  sorry

lemma BUTLASTN_LASTN_NIL: "n <= length l ==> BUTLASTN n (LASTN n l) = []"
  sorry

lemma LASTN_BUTLASTN: "n + m <= length l ==> LASTN n (BUTLASTN m l) = BUTLASTN m (LASTN (n + m) l)"
  sorry

lemma BUTLASTN_LASTN: "m <= n & n <= length l
==> BUTLASTN m (LASTN n l) = LASTN (n - m) (BUTLASTN m l)"
  sorry

lemma LASTN_1: "l ~= [] ==> LASTN 1 l = [last l]"
  sorry

lemma BUTLASTN_1: "l ~= [] ==> BUTLASTN 1 l = butlast l"
  sorry

lemma BUTLASTN_APPEND1: "length l2 <= n ==> BUTLASTN n (l1 @ l2) = BUTLASTN (n - length l2) l1"
  sorry

lemma LASTN_APPEND2: "n <= length l2 ==> LASTN n (l1 @ l2) = LASTN n l2"
  sorry

lemma LASTN_APPEND1: "length l2 <= n ==> LASTN n (l1 @ l2) = LASTN (n - length l2) l1 @ l2"
  sorry

lemma LASTN_MAP: "n <= length l ==> LASTN n (map f l) = map f (LASTN n l)"
  sorry

lemma BUTLASTN_MAP: "n <= length l ==> BUTLASTN n (map f l) = map f (BUTLASTN n l)"
  sorry

lemma ALL_EL_LASTN: "[| list_all P l; m <= length l |] ==> list_all P (LASTN m l)"
  sorry

lemma ALL_EL_BUTLASTN: "[| list_all P l; m <= length l |] ==> list_all P (BUTLASTN m l)"
  sorry

lemma LENGTH_FIRSTN: "n <= length l ==> length (FIRSTN n l) = n"
  sorry

lemma FIRSTN_FIRSTN: "[| m <= length l; n <= m |] ==> FIRSTN n (FIRSTN m l) = FIRSTN n l"
  sorry

lemma LENGTH_BUTFIRSTN: "n <= length l ==> length (BUTFIRSTN n l) = length l - n"
  sorry

lemma BUTFIRSTN_LENGTH_NIL: "BUTFIRSTN (length l) l = []"
  sorry

lemma BUTFIRSTN_APPEND1: "n <= length l1 ==> BUTFIRSTN n (l1 @ l2) = BUTFIRSTN n l1 @ l2"
  sorry

lemma BUTFIRSTN_APPEND2: "length l1 <= n ==> BUTFIRSTN n (l1 @ l2) = BUTFIRSTN (n - length l1) l2"
  sorry

lemma BUTFIRSTN_BUTFIRSTN: "n + m <= length l ==> BUTFIRSTN n (BUTFIRSTN m l) = BUTFIRSTN (n + m) l"
  sorry

lemma APPEND_FIRSTN_BUTFIRSTN: "n <= length l ==> FIRSTN n l @ BUTFIRSTN n l = l"
  sorry

lemma LASTN_SEG: "n <= length l ==> LASTN n l = SEG n (length l - n) l"
  sorry

lemma FIRSTN_SEG: "n <= length l ==> FIRSTN n l = SEG n 0 l"
  sorry

lemma BUTFIRSTN_SEG: "n <= length l ==> BUTFIRSTN n l = SEG (length l - n) n l"
  sorry

lemma BUTFIRSTN_SNOC: "n <= length l ==> BUTFIRSTN n (SNOC x l) = SNOC x (BUTFIRSTN n l)"
  sorry

lemma APPEND_BUTLASTN_BUTFIRSTN: "m + n = length l ==> BUTLASTN m l @ BUTFIRSTN n l = l"
  sorry

lemma SEG_SEG: "n1 + m1 <= length l & n2 + m2 <= n1
==> SEG n2 m2 (SEG n1 m1 l) = SEG n2 (m1 + m2) l"
  sorry

lemma SEG_APPEND1: "n + m <= length l1 ==> SEG n m (l1 @ l2) = SEG n m l1"
  sorry

lemma SEG_APPEND2: "length l1 <= m & n <= length l2
==> SEG n m (l1 @ l2) = SEG n (m - length l1) l2"
  sorry

lemma SEG_FIRSTN_BUTFISTN: "n + m <= length l ==> SEG n m l = FIRSTN n (BUTFIRSTN m l)"
  sorry

lemma SEG_APPEND: "m < length l1 & length l1 <= n + m & n + m <= length l1 + length l2
==> SEG n m (l1 @ l2) =
    SEG (length l1 - m) m l1 @ SEG (n + m - length l1) 0 l2"
  sorry

lemma SEG_LENGTH_SNOC: "SEG 1 (length x) (SNOC xa x) = [xa]"
  sorry

lemma SEG_SNOC: "n + m <= length l ==> SEG n m (SNOC x l) = SEG n m l"
  sorry

lemma ELL_SEG: "n < length l ==> ELL n l = hd (SEG 1 (PRE (length l - n)) l)"
  sorry

lemma SNOC_FOLDR: "SNOC x l = foldr op # l [x]"
  sorry

lemma IS_EL_FOLDR_MAP: "List.member xa x = foldr op | (map (op = x) xa) False"
  sorry

lemma IS_EL_FOLDL_MAP: "List.member xa x = foldl op | False (map (op = x) xa)"
  sorry

lemma FILTER_FILTER: "filter P (filter Q l) = [x<-l. P x & Q x]"
  sorry

lemma FCOMM_FOLDR_FLAT: "[| FCOMM g f; LEFT_ID g e |]
==> foldr f (concat l) e = foldr g (map (FOLDR f e) l) e"
  sorry

lemma FCOMM_FOLDL_FLAT: "[| FCOMM f g; RIGHT_ID g e |]
==> foldl f e (concat l) = foldl g e (map (foldl f e) l)"
  sorry

lemma FOLDR_MAP_REVERSE: "(!!(a::'a) (b::'a) c::'a. (f::'a => 'a => 'a) a (f b c) = f b (f a c))
==> foldr f (map (g::'b => 'a) (rev (l::'b list))) (e::'a) =
    foldr f (map g l) e"
  sorry

lemma FOLDR_FILTER_REVERSE: "(!!(a::'a) (b::'a) c::'a. (f::'a => 'a => 'a) a (f b c) = f b (f a c))
==> foldr f (filter (P::'a => bool) (rev (l::'a list))) (e::'a) =
    foldr f (filter P l) e"
  sorry

lemma COMM_ASSOC_FOLDR_REVERSE: "[| COMM f; ASSOC f |] ==> foldr f (rev l) e = foldr f l e"
  sorry

lemma COMM_ASSOC_FOLDL_REVERSE: "[| COMM f; ASSOC f |] ==> foldl f e (rev l) = foldl f e l"
  sorry

lemma ELL_LAST: "~ List.null l ==> ELL 0 l = last l"
  sorry

lemma ELL_0_SNOC: "ELL 0 (SNOC x l) = x"
  sorry

lemma ELL_SNOC: "0 < n ==> ELL n (SNOC x l) = ELL (PRE n) l"
  sorry

lemma ELL_SUC_SNOC: "ELL (Suc n) (SNOC x xa) = ELL n xa"
  sorry

lemma ELL_CONS: "n < length l ==> ELL n (x # l) = ELL n l"
  sorry

lemma ELL_LENGTH_CONS: "ELL (length l) (x # l) = x"
  sorry

lemma ELL_LENGTH_SNOC: "ELL (length l) (SNOC x l) = (if List.null l then x else hd l)"
  sorry

lemma ELL_APPEND2: "n < length l2 ==> ELL n (l1 @ l2) = ELL n l2"
  sorry

lemma ELL_APPEND1: "length l2 <= n ==> ELL n (l1 @ l2) = ELL (n - length l2) l1"
  sorry

lemma ELL_PRE_LENGTH: "l ~= [] ==> ELL (PRE (length l)) l = hd l"
  sorry

lemma EL_LENGTH_SNOC: "EL (length l) (SNOC x l) = x"
  sorry

lemma EL_PRE_LENGTH: "l ~= [] ==> EL (PRE (length l)) l = last l"
  sorry

lemma EL_SNOC: "n < length l ==> EL n (SNOC x l) = EL n l"
  sorry

lemma EL_ELL: "n < length l ==> EL n l = ELL (PRE (length l - n)) l"
  sorry

lemma EL_LENGTH_APPEND: "~ List.null l2 ==> EL (length l1) (l1 @ l2) = hd l2"
  sorry

lemma ELL_EL: "n < length l ==> ELL n l = EL (PRE (length l - n)) l"
  sorry

lemma ELL_MAP: "n < length l ==> ELL n (map f l) = f (ELL n l)"
  sorry

lemma LENGTH_BUTLAST: "l ~= [] ==> length (butlast l) = PRE (length l)"
  sorry

lemma BUTFIRSTN_LENGTH_APPEND: "BUTFIRSTN (length l1) (l1 @ l2) = l2"
  sorry

lemma FIRSTN_APPEND1: "n <= length l1 ==> FIRSTN n (l1 @ l2) = FIRSTN n l1"
  sorry

lemma FIRSTN_APPEND2: "length l1 <= n ==> FIRSTN n (l1 @ l2) = l1 @ FIRSTN (n - length l1) l2"
  sorry

lemma FIRSTN_LENGTH_APPEND: "FIRSTN (length l1) (l1 @ l2) = l1"
  sorry

lemma REVERSE_FLAT: "rev (concat l) = concat (rev (map rev l))"
  sorry

lemma MAP_FILTER: "(!!x. P (f x) = P x) ==> map f (filter P l) = filter P (map f l)"
  sorry

lemma FLAT_REVERSE: "concat (rev l) = rev (concat (map rev l))"
  sorry

lemma FLAT_FLAT: "concat (concat l) = concat (map concat l)"
  sorry

lemma ALL_EL_SEG: "[| list_all P l; m + k <= length l |] ==> list_all P (SEG m k l)"
  sorry

lemma ALL_EL_FIRSTN: "[| list_all P l; m <= length l |] ==> list_all P (FIRSTN m l)"
  sorry

lemma ALL_EL_BUTFIRSTN: "[| list_all P l; m <= length l |] ==> list_all P (BUTFIRSTN m l)"
  sorry

lemma SOME_EL_SEG: "[| m + k <= length l; list_ex P (SEG m k l) |] ==> list_ex P l"
  sorry

lemma SOME_EL_FIRSTN: "[| m <= length l; list_ex P (FIRSTN m l) |] ==> list_ex P l"
  sorry

lemma SOME_EL_BUTFIRSTN: "[| m <= length l; list_ex P (BUTFIRSTN m l) |] ==> list_ex P l"
  sorry

lemma SOME_EL_LASTN: "[| m <= length l; list_ex P (LASTN m l) |] ==> list_ex P l"
  sorry

lemma SOME_EL_BUTLASTN: "[| m <= length l; list_ex P (BUTLASTN m l) |] ==> list_ex P l"
  sorry

lemma IS_EL_REVERSE: "List.member (rev l) x = List.member l x"
  sorry

lemma IS_EL_FILTER: "P x ==> List.member (filter P l) x = List.member l x"
  sorry

lemma IS_EL_SEG: "[| n + m <= length l; List.member (SEG n m l) x |] ==> List.member l x"
  sorry

lemma IS_EL_SOME_EL: "List.member l x = list_ex (op = x) l"
  sorry

lemma IS_EL_FIRSTN: "[| x <= length xa; List.member (FIRSTN x xa) xb |] ==> List.member xa xb"
  sorry

lemma IS_EL_BUTFIRSTN: "[| x <= length xa; List.member (BUTFIRSTN x xa) xb |] ==> List.member xa xb"
  sorry

lemma IS_EL_BUTLASTN: "[| x <= length xa; List.member (BUTLASTN x xa) xb |] ==> List.member xa xb"
  sorry

lemma IS_EL_LASTN: "[| x <= length xa; List.member (LASTN x xa) xb |] ==> List.member xa xb"
  sorry

lemma ZIP_SNOC: "length l1 = length l2
==> zip (SNOC x1 l1) (SNOC x2 l2) = SNOC (x1, x2) (zip l1 l2)"
  sorry

lemma UNZIP_SNOC: "unzip (SNOC x l) =
(SNOC (fst x) (fst (unzip l)), SNOC (snd x) (snd (unzip l)))"
  sorry

lemma LENGTH_UNZIP_FST: "length (UNZIP_FST x) = length x"
  sorry

lemma LENGTH_UNZIP_SND: "length (UNZIP_SND (x::('a * 'b) list)) = length x"
  sorry

lemma SUM_APPEND: "HOL4Compat.sum (l1 @ l2) = HOL4Compat.sum l1 + HOL4Compat.sum l2"
  sorry

lemma SUM_REVERSE: "HOL4Compat.sum (rev l) = HOL4Compat.sum l"
  sorry

lemma SUM_FLAT: "HOL4Compat.sum (concat l) = HOL4Compat.sum (map HOL4Compat.sum l)"
  sorry

lemma EL_APPEND1: "n < length l1 ==> EL n (l1 @ l2) = EL n l1"
  sorry

lemma EL_APPEND2: "length l1 <= n ==> EL n (l1 @ l2) = EL (n - length l1) l2"
  sorry

lemma EL_MAP: "n < length l ==> EL n (map f l) = f (EL n l)"
  sorry

lemma EL_CONS: "0 < n ==> EL n (x # l) = EL (PRE n) l"
  sorry

lemma EL_SEG: "n < length l ==> EL n l = hd (SEG 1 n l)"
  sorry

lemma EL_IS_EL: "n < length l ==> List.member l (EL n l)"
  sorry

lemma TL_SNOC: "tl (SNOC x l) = (if List.null l then [] else SNOC x (tl l))"
  sorry

lemma EL_REVERSE: "n < length l ==> EL n (rev l) = EL (PRE (length l - n)) l"
  sorry

lemma EL_REVERSE_ELL: "n < length l ==> EL n (rev l) = ELL n l"
  sorry

lemma ELL_LENGTH_APPEND: "~ List.null l1 ==> ELL (length l2) (l1 @ l2) = last l1"
  sorry

lemma ELL_IS_EL: "n < length l ==> List.member l (ELL n l)"
  sorry

lemma ELL_REVERSE: "n < length l ==> ELL n (rev l) = ELL (PRE (length l - n)) l"
  sorry

lemma ELL_REVERSE_EL: "n < length l ==> ELL n (rev l) = EL n l"
  sorry

lemma FIRSTN_BUTLASTN: "n <= length l ==> FIRSTN n l = BUTLASTN (length l - n) l"
  sorry

lemma BUTLASTN_FIRSTN: "n <= length l ==> BUTLASTN n l = FIRSTN (length l - n) l"
  sorry

lemma LASTN_BUTFIRSTN: "n <= length l ==> LASTN n l = BUTFIRSTN (length l - n) l"
  sorry

lemma BUTFIRSTN_LASTN: "n <= length l ==> BUTFIRSTN n l = LASTN (length l - n) l"
  sorry

lemma SEG_LASTN_BUTLASTN: "n + m <= length l ==> SEG n m l = LASTN n (BUTLASTN (length l - (n + m)) l)"
  sorry

lemma BUTFIRSTN_REVERSE: "n <= length l ==> BUTFIRSTN n (rev l) = rev (BUTLASTN n l)"
  sorry

lemma BUTLASTN_REVERSE: "n <= length l ==> BUTLASTN n (rev l) = rev (BUTFIRSTN n l)"
  sorry

lemma LASTN_REVERSE: "n <= length l ==> LASTN n (rev l) = rev (FIRSTN n l)"
  sorry

lemma FIRSTN_REVERSE: "n <= length l ==> FIRSTN n (rev l) = rev (LASTN n l)"
  sorry

lemma SEG_REVERSE: "n + m <= length l ==> SEG n m (rev l) = rev (SEG n (length l - (n + m)) l)"
  sorry

lemma LENGTH_GENLIST: "length (GENLIST f n) = n"
  sorry

lemma LENGTH_REPLICATE: "length (REPLICATE n x) = n"
  sorry

lemma IS_EL_REPLICATE: "0 < n ==> List.member (REPLICATE n x) x"
  sorry

lemma ALL_EL_REPLICATE: "list_all (op = x) (REPLICATE n x)"
  sorry

lemma AND_EL_FOLDL: "AND_EL l = foldl op & True l"
  sorry

lemma AND_EL_FOLDR: "AND_EL l = foldr op & l True"
  sorry

lemma OR_EL_FOLDL: "OR_EL l = foldl op | False l"
  sorry

lemma OR_EL_FOLDR: "OR_EL l = foldr op | l False"
  sorry

;end_setup

setup_theory "~~/src/HOL/Import/HOL" state_transformer

definition
  UNIT :: "'b => 'a => 'b * 'a"  where
  "(op ==::('b::type => 'a::type => 'b::type * 'a::type)
        => ('b::type => 'a::type => 'b::type * 'a::type) => prop)
 (UNIT::'b::type => 'a::type => 'b::type * 'a::type)
 (Pair::'b::type => 'a::type => 'b::type * 'a::type)"

lemma UNIT_DEF: "UNIT x = Pair x"
  sorry

definition
  BIND :: "('a => 'b * 'a) => ('b => 'a => 'c * 'a) => 'a => 'c * 'a"  where
  "BIND == %g f. (%(x, y). f x y) o g"

lemma BIND_DEF: "BIND (g::'a => 'b * 'a) (f::'b => 'a => 'c * 'a) =
(%(x::'b, y::'a). f x y) o g"
  sorry

definition
  MMAP :: "('c => 'b) => ('a => 'c * 'a) => 'a => 'b * 'a"  where
  "MMAP == %(f::'c => 'b) m::'a => 'c * 'a. BIND m (UNIT o f)"

lemma MMAP_DEF: "MMAP f m = BIND m (UNIT o f)"
  sorry

definition
  JOIN :: "('a => ('a => 'b * 'a) * 'a) => 'a => 'b * 'a"  where
  "JOIN == %z. BIND z I"

lemma JOIN_DEF: "JOIN z = BIND z I"
  sorry

lemma BIND_LEFT_UNIT: "BIND (UNIT (x::'a)) (k::'a => 'b => 'c * 'b) = k x"
  sorry

lemma UNIT_UNCURRY: "prod_case UNIT x = x"
  sorry

lemma BIND_RIGHT_UNIT: "BIND k UNIT = k"
  sorry

lemma BIND_ASSOC: "BIND (x::'a => 'b * 'a)
 (%a::'b. BIND ((xa::'b => 'a => 'c * 'a) a) (xb::'c => 'a => 'd * 'a)) =
BIND (BIND x xa) xb"
  sorry

lemma MMAP_ID: "MMAP I = I"
  sorry

lemma MMAP_COMP: "MMAP ((f::'c => 'd) o (g::'b => 'c)) = MMAP f o MMAP g"
  sorry

lemma MMAP_UNIT: "MMAP (f::'b => 'c) o UNIT = UNIT o f"
  sorry

lemma MMAP_JOIN: "MMAP f o JOIN = JOIN o MMAP (MMAP f)"
  sorry

lemma JOIN_UNIT: "JOIN o UNIT = I"
  sorry

lemma JOIN_MMAP_UNIT: "JOIN o MMAP UNIT = I"
  sorry

lemma JOIN_MAP_JOIN: "JOIN o MMAP JOIN = JOIN o JOIN"
  sorry

lemma JOIN_MAP: "BIND (x::'a => 'b * 'a) (xa::'b => 'a => 'c * 'a) = JOIN (MMAP xa x)"
  sorry

lemma FST_o_UNIT: "fst o UNIT (x::'a) = K x"
  sorry

lemma SND_o_UNIT: "snd o UNIT (x::'a) = I"
  sorry

lemma FST_o_MMAP: "fst o MMAP (x::'a => 'b) (xa::'c => 'a * 'c) = x o (fst o xa)"
  sorry

;end_setup

end

